use c2rustc_mir::borrow_check::mir_borrowck;
use rustc::mir::BindingForm::Var;
use rustc::mir::ClearCrossCrate::Set;
use rustc::mir::{Local, Mir, Mutability};
use std::collections::{BTreeMap, HashSet};
use std::iter::FromIterator;
use syntax::ast::StmtKind::Local as StmtLocal;
use syntax::ast::{BindingMode, Crate, Pat, PatKind, Stmt};
use syntax::ptr::P;
use syntax::source_map::SpanData;

use crate::ast_manip::fn_edit::mut_visit_fns;
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

        mut_visit_fns(krate, |fl| {
            let def_id = cx.node_def_id(fl.id);
            let mir = tcx.mir_validated(def_id).borrow();

            let borrow_check_result = mir_borrowck(tcx, def_id);
            let used_mut_user_locals: HashSet<Local> =
                HashSet::from_iter(borrow_check_result.used_mut.iter().cloned());

            let sorted_user_locals = sort_user_locals(&mir);

            for arg in fl.decl.inputs.iter_mut() {
                let arg_span = arg.pat.span.data();
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

            FlatMapNodes::visit(&mut fl.decl, |s: Stmt| {
                let new_stmt = match &s.node {
                    StmtLocal(ast_local) => {
                        match &ast_local.pat.node {
                            PatKind::Ident(BindingMode::ByValue(_), ident, span) => {
                                let mir_local = sorted_user_locals
                                    .get(&s.span.data())
                                    .expect("Can't match Ident to local.");
                                let mir_decl = mir.local_decls.get(*mir_local).unwrap();

                                if mir_decl.mutability == Mutability::Mut
                                    && used_mut_user_locals.contains(mir_local)
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
    }

    fn min_phase(&self) -> Phase {
        Phase::Phase3
    }
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
