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

// TODO : Temp includes for linting
use rustc::lint::builtin::UNUSED_MUT;
use rustc::mir::ClearCrossCrate;
use rustc_errors::{Applicability};
// TODO : End previous TODO


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
        let mut fl_collection = HashMap::new();

        mut_visit_fns(krate, |fl| {
            if fl.kind == FnKind::Foreign {
                let def_id = cx.node_def_id(fl.id);
                call_ctxt_collection.push(CallCtxt { def_id, calls: Vec::new(), passed_locals: HashMap::new() });

                // TODO : Specific handling required for foreign functions so that they appear in call 
                // graph but dont throw an error by trying to walk them.
                return;
            }

            let def_id = cx.node_def_id(fl.id);
            let input_mir = tcx.mir_validated(def_id);
            let mir: &Mir<'_> = &input_mir.borrow();

            // println!("def_id: {:?}", def_id);
            fl_collection.insert(def_id, fl.clone());

            let mut call_vec = Vec::new();
            let mut locals_called : HashMap<Local, (DefId, Local)> = HashMap::new();

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
                                                locals_called.insert(local, (callee_id,param_id));
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

            call_ctxt_collection.push(CallCtxt { def_id, calls: call_vec, passed_locals: locals_called });
        });

        // println!("call_ctxt_collection: {:?}", call_ctxt_collection);
        let mut call_graph = CallGraph::build_graph(call_ctxt_collection);
        let mut func_results = HashMap::new();

        mut_visit_fns(krate, |fl| {
            // println!("Checking FL.Ident: {:?}", fl.ident.name);

            if fl.kind == FnKind::Foreign {
                return;
            }

            let def_id = cx.node_def_id(fl.id);
            let mir = tcx.mir_validated(def_id).borrow();

            let borrow_check_result = mir_borrowck(tcx, def_id);

            call_graph.mark_analyzed(def_id);
            func_results.insert(def_id, borrow_check_result.clone());

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
        for root in call_graph.get_roots() {
            let analysis_path = call_graph.into_iter(root, TraversalType::PostOrder);
            // println!("{:?}", call_graph.into_iter(root, TraversalType::PostOrder));

            for node_tag in analysis_path {
                if let Some(node) = call_graph.get_node(node_tag) {
                    if !node.analyzed() {
                        continue;
                    }

                    if let Some(current_node_analysis) = func_results.get(&node_tag.0) {
                        if current_node_analysis.may_use_refs.is_empty() {
                            // No need for further analysis if the current function is
                            // determined to not have any cases of may_mut
                            continue;
                        }
                        
                        // Make local copy of cna that can be mutated and eventually replace/update old cna
                        let mut cna = current_node_analysis.clone();
                        
                        for caller_may_mut in cna.may_use_refs.clone().iter() {
                            if let Some((callee_id, callee_param_pos)) = node.get_call_id(*caller_may_mut) {
                                // Check to make sure called function has been analyzed
                                if let Some(callee_node) = call_graph.get_node(NodeTag(*callee_id)) {
                                    if !callee_node.analyzed() {
                                        // Callee function has not been analyzed, thus we must assume pointer is used mutably.
                                        if let Some(caller_alias_set) = cna.aa.get_alias_set(caller_may_mut) {
                                            // may_mut has alias' that need to be added to used_mut_refs
                                            for caller_alias_local in caller_alias_set.iter() {
                                                cna.may_use_refs.remove(caller_alias_local);
                                                cna.used_mut_refs.insert(*caller_alias_local);
                                            }
                                        }

                                        cna.may_use_refs.remove(caller_may_mut);
                                        cna.used_mut_refs.insert(*caller_may_mut);
                                        continue;
                                    }

                                    // Callee function has been analyzed, get function analysis results.
                                    if let Some(callee_results) = func_results.get(callee_id) {
                                        if callee_results.may_use_refs.contains(callee_param_pos) {
                                            // TODO : This is likely a cyclic case.
                                            println!("Found caller: {:?} in callee's may_use_refs set: {:?}.", caller_may_mut, callee_param_pos);
                                            continue;
                                        }

                                        if !callee_results.used_mut_refs.contains(callee_param_pos) {
                                            // caller_may_mut not contained in callee may_use_refs or used_mut_refs
                                            // Check to see if may_use_ref has alias' and add any not used mutably to alias set
                                            if let Some(caller_alias_set) = cna.aa.get_alias_set(caller_may_mut) {
                                                for caller_alias_local in caller_alias_set.iter() {
                                                    if !cna.used_mut_refs.contains(caller_alias_local) {
                                                        cna.may_use_refs.insert(*caller_alias_local);
                                                    }
                                                }
                                            }

                                            continue;
                                        }
                                    }
                                }
                            }

                            // If no continue branch is hit, it means may_mut is either used mutably or could not be 
                            // analyzed, and in either case should be removed from may_use_refs and added to used_mut_refs
                            if let Some(caller_alias_set) = cna.aa.get_alias_set(caller_may_mut) {
                                // may_mut has alias' that need to be added to used_mut_refs
                                for caller_alias_local in caller_alias_set.iter() {
                                    cna.may_use_refs.remove(caller_alias_local);
                                    cna.used_mut_refs.insert(*caller_alias_local);
                                }
                            }

                            cna.may_use_refs.remove(caller_may_mut);
                            cna.used_mut_refs.insert(*caller_may_mut);
                        }

                        // With altered state of cna, print out still present may_use_refs
                        let mir = tcx.mir_validated(node_tag.0).borrow();

                        for local in cna.may_use_refs.iter() {
                            if let ClearCrossCrate::Set(ref vsi) = mir.source_scope_local_data {
                                let local_decl = &mir.local_decls[*local];
                                let span = local_decl.source_info.span;

                                let mut_span = tcx.sess.source_map().span_until_non_whitespace(span);
                                tcx.struct_span_lint_hir(
                                    UNUSED_MUT,
                                    vsi[local_decl.source_info.scope].lint_root,
                                    span,
                                    "not used mutably!",
                                )
                                    .span_suggestion_short(
                                        mut_span,
                                        "passed type does not need to be mutable.",
                                        String::new(),
                                        Applicability::MachineApplicable,
                                    )
                                    .emit();
                            }
                        }

                        // Update old func results with new func results.
                        func_results.insert(node_tag.0, cna);

                        // TODO : One thing that might increase the number of items found would be to remove the 
                        // set of passed variables that are passed to non-mut parameter positions.
                    }
                }
            }
        }
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
                    passed_locals: call_ctxt.passed_locals.clone(),
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

    fn get_node(&self, node_tag: NodeTag) -> Option<&Node> {
        self.graph_nodes.get(&node_tag)
    }

    fn get_roots(&self) -> Vec<NodeTag> {
        self.roots.clone()
    }

    fn mark_analyzed(&mut self, def_id: DefId) {
        if let Some(node) = self.graph_nodes.get_mut(&NodeTag(def_id)) {
            node.mark_analyzed();
        }
    }

    fn into_iter(&self, root: NodeTag, traversal_type: TraversalType) -> std::vec::IntoIter<NodeTag> {
        let mut traversal_path = Vec::new();
        let mut visited = Vec::new();
        let mut has_cycle = false;

        self.recurse_graph(
            root, 
            Vec::new(), 
            &mut visited,
            &mut traversal_path, 
            traversal_type,
            &mut has_cycle);

        // if has_cycle {
        //     println!("Root: {:?} has cycle!", root);
        // }

        traversal_path.into_iter()
    }

    fn recurse_graph(
        &self, 
        current_node: NodeTag, 
        mut call_stack: Vec<NodeTag>, 
        visited: &mut Vec<NodeTag>,
        tp: &mut Vec<NodeTag>, 
        travesal_type: TraversalType, 
        has_cycle: &mut bool
    ) {
        if !visited.contains(&current_node) {
            visited.push(current_node);
        }

        if !call_stack.contains(&current_node) {
            call_stack.push(current_node);
        }
    
        match travesal_type {
            TraversalType::DFS => {
                if !tp.contains(&current_node) {
                    tp.push(current_node);
                }

                if let Some(node) = self.graph_nodes.get(&current_node) {
                    for child_tag in node.children() {
                        if call_stack.contains(&child_tag) {
                            *has_cycle = true;
                        }
         
                        if !visited.contains(&child_tag) {
                            self.recurse_graph(
                                *child_tag,
                                call_stack.clone(),
                                visited,
                                tp,
                                travesal_type,
                                has_cycle,
                            );
                        }
                    }
                }
            },
            TraversalType::PostOrder => {
                if let Some(node) = self.graph_nodes.get(&current_node) {
                    for child_tag in node.children() {
                        if call_stack.contains(&child_tag) {
                            *has_cycle = true;
                        }
                        
                        if !visited.contains(&child_tag) {
                            self.recurse_graph(
                                *child_tag,
                                call_stack.clone(),
                                visited,
                                tp,
                                travesal_type,
                                has_cycle,
                            );
                        }
                    }
                }

                if !tp.contains(&current_node) {
                    tp.push(current_node);
                }
            },
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
    passed_locals: HashMap<Local, (DefId,Local)>,
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

    fn analyzed(&self) -> bool {
        self.analyzed
    }

    fn children(&self) -> &Vec<NodeTag> {
        &self.succ
    }

    fn parents(&self) -> &Vec<NodeTag> {
        &self.pred
    }

    fn get_call_id(&self, local: Local) -> Option<&(DefId,Local)> {
        self.passed_locals.get(&local)
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
    passed_locals: HashMap<Local,(DefId,Local)>,
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

#[derive(Clone, Copy)]
enum TraversalType {
    DFS,
    PostOrder,
}
