use c2rustc_mir::borrow_check::mir_borrowck;
use rustc::hir::def_id::DefId;
use rustc::mir::BindingForm::Var;
use rustc::mir::ClearCrossCrate::Set;
use rustc::mir::{Local, Mir, Mutability, Operand};
use rustc::mir::traversal;
use rustc::mir::BasicBlockData;
use rustc::mir::{TerminatorKind};
use rustc::ty::TyKind;
use rustc_data_structures::fx::{FxHashMap};
use std::collections::{BTreeMap, HashSet};
use std::collections::hash_map::HashMap;
use std::iter::FromIterator;
use syntax::ast::StmtKind::Local as StmtLocal;
use syntax::ast::{BindingMode, Crate, Pat, PatKind, Stmt};
use syntax::ptr::P;
use syntax::source_map::SpanData;

use std::fmt::{self, Display, Formatter};

use crate::ast_manip::fn_edit::{mut_visit_fns, FnKind};
use crate::ast_manip::FlatMapNodes;
use crate::command::{CommandState, Registry};
use crate::driver::Phase;
use crate::transform::Transform;
use crate::RefactorCtxt;

pub fn register_commands(reg: &mut Registry) {
    use super::mk;

    reg.register("remove_mut", |_args| mk(RemoveMutability));
}

pub struct RemoveMutability;

impl Transform for RemoveMutability {
    fn transform(&self, krate: &mut Crate, _st: &CommandState, cx: &RefactorCtxt) {
        let tcx = cx.ty_ctxt();
        let mut call_ctxt_collection = Vec::new();

        mut_visit_fns(krate, |fl| {
            if fl.kind == FnKind::Foreign {
                let def_id = cx.node_def_id(fl.id);
                call_ctxt_collection.push(CallCtxt { def_id, calls: Vec::new() });

                // TODO : Specific handling required for foreign functions so that they appear in call 
                // graph but dont throw an error by trying to walk them.
                return;
            }

            let def_id = cx.node_def_id(fl.id);
            let input_mir = tcx.mir_validated(def_id);
            let mir: &Mir<'_> = &input_mir.borrow();

            // println!("def_id: {:?}", def_id);

            let mut call_vec = Vec::new();

            for (bb, _) in traversal::reverse_postorder(&mir) {
                let BasicBlockData { statements: _, ref terminator, is_cleanup: _ } = mir[bb];

                if let Some(term) = terminator {
                    if let TerminatorKind::Call {
                        ref func,
                        ref args,
                        destination: _,
                        cleanup: _,
                        from_hir_call: _,
                    } = term.kind {
                        // println!("func: {:?} | args: {:?}", func, args);

                        // This is literally all I needed.
                        if let Operand::Constant(con) = func {
                            if let TyKind::FnDef(callee_id, _) = con.ty.sty {
                                // println!("called def_id: {:?}", callee_id);

                                let mut hash_map = HashMap::default();

                                for (arg_id, arg_op) in args.iter().enumerate() {
                                    let param_id = Local::from_usize(arg_id + 1);
                                    match arg_op {
                                        Operand::Move(place) | Operand::Copy(place) => {
                                            if let Some(local) = place.base_local() {
                                                hash_map.insert(param_id, local);
                                            }
                                        },
                                        Operand::Constant(_con) => { /* Do Nothing */ },
                                    }
                                }

                                call_vec.push(Call { def_id: callee_id, affected_locals: hash_map });
                            }
                        }
                    }
                }
            }

            call_ctxt_collection.push(CallCtxt { def_id, calls: call_vec });
        });

        // println!("call_ctxt_collection: {:?}", call_ctxt_collection);
        let mut call_graph = CallGraph::build_graph(call_ctxt_collection);
        

        mut_visit_fns(krate, |fl| {
            // println!("Checking FL.Ident: {:?}", fl.ident.name);

            if fl.kind == FnKind::Foreign {
                return;
            }

            let def_id = cx.node_def_id(fl.id);
            let mir = tcx.mir_validated(def_id).borrow();

            let borrow_check_result = mir_borrowck(tcx, def_id);

            call_graph.mark_analyzed(def_id);

            let used_mut_user_locals: HashSet<Local> =
                HashSet::from_iter(borrow_check_result.used_mut.iter().cloned());

            let sorted_user_locals = sort_user_locals(&mir);

            for arg in fl.decl.inputs.iter_mut() {
                let arg_span = arg.pat.span.data();
                // We won't find all definitions, like function generated through `#[derive(Copy)]`.
                if !sorted_user_locals.contains_key(&arg_span) {
                    continue;
                }

                let mir_local = sorted_user_locals
                    .get(&arg_span)
                    .expect("Can't match arg node to local.");
                let mir_decl = mir.local_decls.get(*mir_local).unwrap();

                if mir_decl.mutability == Mutability::Not {
                    continue;
                }

                if used_mut_user_locals.contains(mir_local) {
                    continue;
                }

                arg.pat.node = match &arg.pat.node {
                    PatKind::Ident(BindingMode::ByValue(_), ident, span) => PatKind::Ident(
                        BindingMode::ByValue(syntax::ast::Mutability::Immutable),
                        *ident,
                        span.clone(),
                    ),
                    x => x.clone(),
                };
            }

            FlatMapNodes::visit(&mut fl.block, |s: Stmt| {
                let new_stmt = match &s.node {
                    StmtLocal(ast_local) => {
                        match &ast_local.pat.node {
                            PatKind::Ident(BindingMode::ByValue(_), ident, span) => {
                                let local_span = ast_local.pat.span.data();

                                let mir_local = sorted_user_locals
                                    .get(&local_span)
                                    .expect("Can't match Ident to local.");
                                let mir_decl = mir.local_decls.get(*mir_local).unwrap();

                                if mir_decl.mutability == Mutability::Mut
                                    && !used_mut_user_locals.contains(mir_local)
                                {
                                    // Is this struct construction really idiomatic? But the borrow checker accepts it at least...
                                    let new_pat = P(Pat {
                                        node: PatKind::Ident(
                                            BindingMode::ByValue(
                                                syntax::ast::Mutability::Immutable,
                                            ),
                                            *ident,
                                            span.clone(),
                                        ),
                                        ..*ast_local.pat
                                    });
                                    let mut new_ast_local = ast_local.clone();
                                    new_ast_local.pat = new_pat;
                                    Stmt {
                                        node: StmtLocal(new_ast_local),
                                        ..s
                                    }
                                } else {
                                    s
                                }
                            }
                            _ => s,
                        }
                    }
                    _ => s,
                };
                smallvec![new_stmt]
            })
        });

        // println!("{}", call_graph);
        // println!("# of roots: {}", call_graph.roots.len());
    }

    fn min_phase(&self) -> Phase {
        Phase::Phase3
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct CallGraph {
    graph_nodes: FxHashMap<NodeTag, Node>,
    graph_edges: Vec<Edge>,
    roots: Vec<NodeTag>,
}

impl CallGraph {
    fn build_graph(call_ctxt_coll: Vec<CallCtxt>) -> Self {
        let mut graph_nodes : FxHashMap<NodeTag, Node> = 
            call_ctxt_coll.iter().map(|call_ctxt| {(
                NodeTag(call_ctxt.def_id),
                Node {
                    tag: NodeTag(call_ctxt.def_id),
                    data: call_ctxt.clone(),
                    analyzed: false,
                    pred: Vec::new(),
                    succ: call_ctxt.successors(),
                }
            )
        }).collect();

        let mut graph_edges = Vec::new();

        // Adds all predecessors to each node
        let clone_nodes : FxHashMap<NodeTag, Node> = graph_nodes.clone();
        clone_nodes.iter().for_each(|(_node_tag, node)| {
            // For each node in clone_nodes, add pred info to each successor.
            // Also construct the graph edges.
            for succ in node.succ.iter() {
                graph_edges.push(Edge{ src: node.tag, dst: *succ });

                if let Some(succ_node) = graph_nodes.get_mut(succ) {
                    succ_node.add_pred(node.tag);
                }
            }
        });

        // After all preds and succs are added, prune list of any node that has neither (as they are unimportant for following mutability)
        graph_nodes = graph_nodes.iter().filter_map(|(node_tag, node)| {
            if node.pred.is_empty() && node.succ.is_empty() {
                None
            } else {
                Some((*node_tag,node.clone()))
            }
        }).collect();

        let roots = graph_nodes.iter().filter_map(|(node_tag, node)| {
            if node.pred.is_empty() && !node.succ.is_empty() {
                Some(*node_tag)
            } else {
                None
            }
        }).collect();


        CallGraph {
            graph_nodes,
            graph_edges,
            roots,
        }
    }

    fn mark_analyzed(&mut self, def_id: DefId) {
        if let Some(node) = self.graph_nodes.get_mut(&NodeTag(def_id)) {
            node.mark_analyzed();
        }
    }
}

impl Display for CallGraph {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        write!(fmt, "digraph G {{\n")?;
        for (_node_tag, node) in self.graph_nodes.iter() {
            write!(fmt, "\t{}\n", node)?;
        }

        for edge in self.graph_edges.iter() {
            write!(fmt, "\t{}\n", edge)?;
        }

        write!(fmt, "}}")
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Edge {
    src: NodeTag,
    dst: NodeTag,
}

impl Display for Edge {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        write!(fmt, "{} -> {}", self.src, self.dst)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
struct NodeTag(DefId);

impl Display for NodeTag {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        write!(fmt, "\"{}_{}\"", self.0.krate, self.0.index.as_raw_u32())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Node {
    tag: NodeTag,
    data: CallCtxt,
    analyzed: bool,
    pred: Vec<NodeTag>,
    succ: Vec<NodeTag>,
}

impl Node {
    fn add_pred(&mut self, pred: NodeTag) {
        self.pred.push(pred);
    }

    fn mark_analyzed(&mut self) {
        self.analyzed = true;
    }
}

impl Display for Node {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        if self.analyzed {
            write!(fmt, "{} [shape=record color={} label= \"{}\"]", self.tag, "green", self.data)
        } else {
            write!(fmt, "{} [shape=record color={} label= \"{}\"]", self.tag, "red", self.data)
        }
        
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct CallCtxt {
    def_id: DefId,
    calls: Vec<Call>,
}

impl Display for CallCtxt {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        write!(fmt, "{:?}", self.def_id)
    }
}

impl CallCtxt {
    fn def_id(&self) -> DefId {
        self.def_id.clone()
    }

    fn successors(&self) -> Vec<NodeTag> {
        self.calls.iter().map(|call| {
            NodeTag(call.def_id.clone())
        }).collect()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Call {
    def_id: DefId,
    affected_locals: HashMap<Local, Local>,
}

fn sort_user_locals(mir: &Mir) -> BTreeMap<SpanData, Local> {
    let mut result = BTreeMap::new();

    for (local, local_decl) in mir.local_decls.iter_enumerated() {
        match &local_decl.is_user_variable {
            Some(Set(Var(binding))) => {
                let span = binding.pat_span.data();
                result.insert(span, local);
            }
            _ => {}
        }
    }

    result
}
