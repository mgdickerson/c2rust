use std::collections::HashSet;
use std::ops::Deref;

use rustc::hir::def::{DefKind, Namespace, Res};
use rustc::hir::def_id::DefId;
use rustc::hir::map as hir_map;
use rustc::hir::{self, Node, HirId};
use rustc::session::Session;
use rustc::session::config::CrateType;
use rustc::ty::subst::InternalSubsts;
use rustc::ty::{FnSig, ParamEnv, PolyFnSig, Ty, TyCtxt, TyKind};
use rustc_metadata::cstore::CStore;
use syntax::ast::{
    self, Expr, ExprKind, ForeignItem, ForeignItemKind, FnDecl, FunctionRetTy, Item, ItemKind, NodeId, Path, QSelf, UseTreeKind, DUMMY_NODE_ID,
};
use syntax::ptr::P;

use crate::ast_manip::AstEquiv;
use crate::command::{GenerationalTyCtxt, TyCtxtGeneration};
use crate::ast_manip::util::namespace;
use crate::reflect;
use c2rust_ast_builder::mk;

/// Driver context.  Contains all available analysis results as of the current compiler phase.
///
/// Accessor methods will panic if the requested results are not available.
#[derive(Clone)]
pub struct RefactorCtxt<'a, 'tcx: 'a> {
    sess: &'a Session,
    cstore: &'a CStore,

    map: Option<HirMap<'a, 'tcx>>,
    tcx: Option<GenerationalTyCtxt<'tcx>>,
}

impl<'a, 'tcx> RefactorCtxt<'a, 'tcx> {
    pub fn new(
        sess: &'a Session,
        cstore: &'a CStore,
        map: Option<&'a hir_map::Map<'tcx>>,
        tcx: Option<GenerationalTyCtxt<'tcx>>,
    ) -> Self {
        let map = map.map(|map| HirMap::new(sess, map));
        Self {
            sess,
            cstore,
            map,
            tcx,
        }
    }
}

#[derive(Copy, Clone)]
pub struct HirMap<'a, 'hir: 'a> {
    map: &'a hir_map::Map<'hir>,

    /// Next NodeId after the crate. Needed to validate NodeIds used with the
    /// map.
    max_node_id: NodeId,
}

impl<'a, 'hir> HirMap<'a, 'hir> {
    fn new(sess: &'a Session, map: &'a hir_map::Map<'hir>) -> Self {
        let max_node_id = sess.next_node_id();
        Self { map, max_node_id }
    }
}

// Core RefactorCtxt accessors
impl<'a, 'tcx> RefactorCtxt<'a, 'tcx> {
    #[inline]
    pub fn session(&self) -> &'a Session {
        self.sess
    }

    #[inline]
    pub fn cstore(&self) -> &'a CStore {
        self.cstore
    }

    #[inline]
    pub fn hir_map(&self) -> HirMap<'a, 'tcx> {
        self.map
            .expect("hir map is not available in this context (requires phase 2)")
    }

    #[inline]
    pub fn ty_ctxt(&self) -> TyCtxt<'tcx> {
        self.tcx
            .as_ref()
            .expect("ty ctxt is not available in this context (requires phase 3)")
            .ty_ctxt()
    }

    #[inline]
    pub fn tcx_gen(&self) -> TyCtxtGeneration {
        self.tcx
            .as_ref()
            .expect("ty ctxt is not available in this context (requires phase 3)")
            .tcx_gen()
    }

    #[inline]
    pub fn has_ty_ctxt(&self) -> bool {
        self.tcx.is_some()
    }
}

// Other context API methods
impl<'a, 'tcx> RefactorCtxt<'a, 'tcx> {
    /// Get the `ty::Ty` computed for a node.
    pub fn node_type(&self, id: NodeId) -> Ty<'tcx> {
        let hir_id = self.hir_map().node_to_hir_id(id);
        if let Some(def_id) = self.hir_map().opt_local_def_id(hir_id) {
            return self.def_type(def_id);
        }
        let parent = self.hir_map().get_parent_did(hir_id);
        let tables = self.ty_ctxt().typeck_tables_of(parent);
        tables.node_type(hir_id)
    }

    pub fn opt_node_type(&self, id: NodeId) -> Option<Ty<'tcx>> {
        let hir_id = self.hir_map().opt_node_to_hir_id(id)?;
        if let Some(def_id) = self.hir_map().opt_local_def_id(hir_id) {
            return Some(self.def_type(def_id));
        }
        let parent_node = self.hir_map().get_parent_item(hir_id);
        let parent = self.hir_map().opt_local_def_id(parent_node)?;
        if !self.ty_ctxt().has_typeck_tables(parent) {
            return None;
        }
        let tables = self.ty_ctxt().typeck_tables_of(parent);
        let hir_id = self.hir_map().node_to_hir_id(id);
        tables.node_type_opt(hir_id)
    }

    /// Get the `ty::Ty` computed for a node, taking into account any
    /// adjustments that were applied.
    pub fn adjusted_node_type(&self, id: NodeId) -> Ty<'tcx> {
        self.opt_adjusted_node_type(id)
            .unwrap_or_else(|| panic!("adjusted node type unavailable for {:?}", id))
    }

    pub fn opt_adjusted_node_type(&self, id: NodeId) -> Option<Ty<'tcx>> {
        let hir_id = self.hir_map().node_to_hir_id(id);
        if let Some(def_id) = self.hir_map().opt_local_def_id(hir_id) {
            return Some(self.def_type(def_id));
        }
        let parent_node = self.hir_map().get_parent_item(hir_id);
        let parent = self.hir_map().opt_local_def_id(parent_node)?;
        if !self.ty_ctxt().has_typeck_tables(parent) {
            return None;
        }
        let tables = self.ty_ctxt().typeck_tables_of(parent);
        if let Some(adj) = tables
            .adjustments()
            .get(hir_id)
            .and_then(|adjs| adjs.last())
        {
            Some(adj.target)
        } else {
            tables.node_type_opt(hir_id)
        }
    }

    pub fn def_type(&self, id: DefId) -> Ty<'tcx> {
        self.ty_ctxt().type_of(id)
    }

    /// Build a `Path` referring to a particular def.  This method returns an
    /// absolute path when possible.
    pub fn def_path(&self, id: DefId) -> Path {
        reflect::reflect_def_path(self.ty_ctxt(), id).1
    }

    pub fn def_qpath(&self, id: DefId) -> (Option<QSelf>, Path) {
        reflect::reflect_def_path(self.ty_ctxt(), id)
    }

    /// Obtain the `DefId` of a definition node, such as a `fn` item.
    pub fn node_def_id(&self, id: NodeId) -> DefId {
        match self.hir_map().find(id) {
            Some(Node::Binding(_)) => {
                let hir_id = self.hir_map().node_to_hir_id(id);
                self.node_def_id(self.hir_map().hir_to_node_id(
                    self.hir_map().get_parent_node(hir_id)
                ))
            }
            Some(Node::Item(item)) => self.hir_map().local_def_id(item.hir_id),
            _ => self.hir_map().local_def_id_from_node_id(id),
        }
    }

    pub fn res_to_hir_id(&self, res: &hir::def::Res) -> Option<hir::HirId> {
        match res {
            Res::Def(_, did) | Res::SelfCtor(did) => {
                if did.is_local() {
                    Some(self.hir_map().local_def_id_to_hir_id(did.to_local()))
                } else {
                    None
                }
            }
            Res::Local(id) => Some(*id),

            Res::PrimTy(_) | Res::SelfTy(..) | Res::ToolMod | Res::NonMacroAttr(_) | Res::Err => {
                None
            }
        }
    }

    pub fn try_resolve_expr_to_hid(&self, e: &Expr) -> Option<hir::HirId> {
        self.try_resolve_expr_hir(e)
            .or_else(|| {
                if self.has_ty_ctxt() {
                    self.try_resolve_node_type_dep(e.id)
                } else {
                    None
                }
            })
            .and_then(|def| {
                if let Some(def_id) = def.opt_def_id() {
                    self.hir_map().as_local_hir_id(def_id)
                } else if let Res::Local(hir_id) = def {
                    Some(hir_id)
                } else {
                    None
                }
            })
    }

    pub fn try_resolve_expr(&self, e: &Expr) -> Option<DefId> {
        if let Some(def) = self.try_resolve_expr_hir(e) {
            return def.opt_def_id();
        }

        if self.has_ty_ctxt() {
            // Only try the type_dependent_defs fallback on Path exprs.  Other expr kinds,
            // particularly MethodCall, can show up in type_dependent_defs, and we don't want to
            // wrongly treat those as path-like.
            if let ExprKind::Path(..) = e.kind {
                if let Some(def) = self.try_resolve_node_type_dep(e.id) {
                    return def.opt_def_id();
                }
            }
        }

        None
    }

    /// Get the target `DefId` of a path expr.
    pub fn resolve_expr(&self, e: &Expr) -> DefId {
        self.try_resolve_expr(e)
            .unwrap_or_else(|| panic!("expr does not resolve to a def: {:?}", e))
    }

    pub fn try_resolve_ty(&self, t: &ast::Ty) -> Option<DefId> {
        if let Some(def) = self.try_resolve_ty_hir(t) {
            return def.opt_def_id();
        }

        if self.has_ty_ctxt() {
            if let ast::TyKind::Path(..) = t.kind {
                if let Some(def) = self.try_resolve_node_type_dep(t.id) {
                    return def.opt_def_id();
                }
            }
        }

        None
    }

    /// Get the target `DefId` of a path ty.
    pub fn resolve_ty(&self, t: &ast::Ty) -> DefId {
        self.try_resolve_ty(t)
            .unwrap_or_else(|| panic!("ty does not resolve to a def: {:?}", t))
    }

    pub fn opt_callee(&self, e: &Expr) -> Option<DefId> {
        self.opt_callee_info(e).and_then(|info| info.def_id)
    }

    /// Get the `DefId` of the function or method being called by a `Call` or `MethodCall` expr.
    pub fn callee(&self, e: &Expr) -> DefId {
        self.opt_callee(e).expect("callee: expr is not a call")
    }

    pub fn opt_callee_info(&self, e: &Expr) -> Option<CalleeInfo<'tcx>> {
        if e.id == DUMMY_NODE_ID {
            return None;
        }
        let tcx = self.ty_ctxt();
        let hir_map = self.hir_map();

        let hir_id = hir_map.node_to_hir_id(e.id);
        let parent = hir_map.get_parent_item(hir_id);
        let parent_body = match_or!([hir_map.maybe_body_owned_by(parent)]
                                    Some(x) => x; return None);
        let tables = tcx.body_tables(parent_body);

        let mut def_id = None;
        let poly_sig;
        let mut substs = None;

        // Note this method gets used inside `fold_illtyped_exprs`, which means the tcx may be in a
        // more-or-less bad state due type errors.  We try really hard here to return `None`
        // instead of panicking when weird stuff happens.

        match e.kind {
            ExprKind::Call(ref func, _) => {
                let call_hir_id = hir_map.node_to_hir_id(e.id);
                let func_hir_id = hir_map.node_to_hir_id(func.id);

                // (1) Overloaded calls (FnOnce, etc).  These are special in two ways.  First, all
                // the information about the callee is attached to the Call expr itself, not the
                // func.  And second, it uses the special "rust-call" ABI where arguments are
                // gathered up and passed in a single tuple.
                //
                // We detect this case by the presence of a type-dependent def on the Call.
                if let Some(Ok((kind, func_def_id))) = tables.type_dependent_defs().get(call_hir_id) {
                    if !matches!([kind] DefKind::Fn, DefKind::Method) {
                        warn!(
                            "overloaded call dispatches to non-fnlike def {:?}",
                            kind
                        );
                        return None;
                    }
                    def_id = Some(*func_def_id);
                    poly_sig = tcx.fn_sig(*func_def_id);
                    substs = tables.node_substs_opt(call_hir_id);
                // TODO: adjust for rust-call ABI
                } else {
                    let func_hir = expect!([hir_map.find(func.id)] Some(hir::Node::Expr(e)) => e);

                    // (2) Function pointers.  We have to check for this first because it's
                    // possible that `func` might be a normal or type-dependent path to a
                    // fnptr-typed static or const item.
                    //
                    // We use the adjusted type here in case an `&fn()` got auto-derefed in order
                    // to make the call.
                    if let Some(&TyKind::FnPtr(sig)) =
                        tables.expr_ty_adjusted_opt(func_hir).map(|ty| &ty.kind)
                    {
                        poly_sig = sig;
                    // No substs.  fn ptrs can't be generic over anything but late-bound
                    // regions, and late-bound regions don't show up in the substs.

                    // (3) Type-dependent function (`S::f()`).  Unlike the next case, these don't
                    // get fully resolved until typeck, so the results are recorded differently.
                    } else if let Some(Ok((kind, func_def_id))) = tables.type_dependent_defs().get(func_hir_id) {
                        if !matches!([kind] DefKind::Fn, DefKind::Method) {
                            warn!("type-dep call dispatches to non-fnlike def {:?}", kind);
                            return None;
                        }
                        def_id = Some(*func_def_id);
                        poly_sig = tcx.fn_sig(*func_def_id);
                        substs = tables.node_substs_opt(func_hir_id);

                    // (4) Ordinary function call (`f()`).
                    } else if let Some(func_def_id) = self.try_resolve_expr(func) {
                        def_id = Some(func_def_id);
                        poly_sig = tcx.fn_sig(func_def_id);
                        substs = tables.node_substs_opt(func_hir_id);
                    } else {
                        // Failed to resolve.  Probably a really bad type error somewhere.
                        warn!("failed to resolve call expr {:?}", e);
                        return None;
                    }
                }
            }

            ExprKind::MethodCall(..) => {
                // These cases are much simpler - just get the method definition from
                // type_dependent_defs.
                let hir_id = hir_map.node_to_hir_id(e.id);
                if let Some(Ok((kind, func_def_id))) = tables.type_dependent_defs().get(hir_id) {
                    if !matches!([kind] DefKind::Fn, DefKind::Method) {
                        warn!("type-dep call dispatches to non-fnlike def {:?}", kind);
                        return None;
                    }
                    def_id = Some(*func_def_id);
                    poly_sig = tcx.fn_sig(*func_def_id);
                    substs = tables.node_substs_opt(hir_id);
                } else {
                    return None;
                }
            }

            _ => return None,
        }

        let unsubst_fn_sig = tcx.erase_late_bound_regions(&poly_sig);
        let fn_sig = if let Some(substs) = substs {
            tcx.subst_and_normalize_erasing_regions(substs, ParamEnv::empty(), &unsubst_fn_sig)
        } else {
            tcx.normalize_erasing_regions(ParamEnv::empty(), unsubst_fn_sig)
        };

        Some(CalleeInfo {
            fn_sig,
            poly_sig,
            def_id,
            substs,
        })
    }

    pub fn opt_callee_fn_sig(&self, e: &Expr) -> Option<FnSig<'tcx>> {
        self.opt_callee_info(e).map(|info| info.fn_sig)
    }

    pub fn try_resolve_expr_hir(&self, e: &Expr) -> Option<Res> {
        let node = match_or!([self.hir_map().find(e.id)] Some(x) => x;
                             return None);
        let e = match_or!([node] hir::Node::Expr(e) => e;
                          return None);
        let qpath = match_or!([e.kind] hir::ExprKind::Path(ref q) => q;
                              return None);
        let path = match_or!([*qpath] hir::QPath::Resolved(_, ref path) => path;
                             return None);
        Some(path.res)
    }

    pub fn try_resolve_ty_hir(&self, t: &ast::Ty) -> Option<Res> {
        let node = match_or!([self.hir_map().find(t.id)] Some(x) => x;
                             return None);
        let t = match_or!([node] hir::Node::Ty(t) => t;
                          return None);
        let qpath = match_or!([t.kind] hir::TyKind::Path(ref q) => q;
                              return None);
        let path = match_or!([*qpath] hir::QPath::Resolved(_, ref path) => path;
                             return None);
        Some(path.res)
    }

    /// Try to resolve a node as a reference to a type-dependent definition, like `Vec::new` (a.k.a.
    /// `<Vec>::new`) or `<Vec as IntoIterator>::into_iter`.
    ///
    /// Note that this method doesn't look up the node itself, so it can return results even for
    /// non-path nodes (unlike `try_resolve_expr/ty_hir`).
    pub fn try_resolve_node_type_dep(&self, id: NodeId) -> Option<Res> {
        let hir_map = self.hir_map();
        let tcx = self.ty_ctxt();

        let hir_id = hir_map.opt_node_to_hir_id(id)?;
        let parent = hir_map.get_parent_item(hir_id);
        let parent_body = match_or!([hir_map.maybe_body_owned_by(parent)]
                                    Some(x) => x; return None);
        let tables = tcx.body_tables(parent_body);

        let tdd = tables.type_dependent_defs();
        let def = match_or!([tdd.get(hir_id)] Some(x) => x; return None);
        def.ok().map(|(kind, id)| Res::Def(kind, id))
    }

    /// Attempt to resolve a `Use` item id to the `hir::Path` of the imported
    /// item. The given item _must_ be a `Use`.
    pub fn resolve_use_id(&self, id: NodeId) -> &hir::ptr::P<hir::Path> {
        let hir_node = self
            .hir_map()
            .find(id)
            .unwrap_or_else(|| panic!("Couldn't find HIR node for {:?}", id));
        let hir_item = expect!([hir_node] hir::Node::Item(i) => i);
        let path = expect!([&hir_item.kind] hir::ItemKind::Use(path, _) => path);
        path
    }

    /// Attempt to resolve a `Use` item id to the `hir::Path` of the imported
    /// item. The given item _must_ be a `Use`.
    pub fn try_resolve_use_id(&self, id: NodeId) -> Option<&hir::ptr::P<hir::Path>> {
        let hir_node = self
            .hir_map()
            .find(id)?;
        let hir_item = expect!([hir_node] hir::Node::Item(i) => i);
        let path = expect!([&hir_item.kind] hir::ItemKind::Use(path, _) => path);
        Some(path)
    }

    /// Compare two items for internal structural equivalence, ignoring field names.
    pub fn structural_eq(&self, item1: &Item, item2: &Item) -> bool {
        use syntax::ast::ItemKind::*;
        match (&item1.kind, &item2.kind) {
            // * Assure that these two items are in fact of the same type, just to be safe.
            (TyAlias(ty1, g1), TyAlias(ty2, g2)) => {
                match (self.opt_node_type(item1.id), self.opt_node_type(item2.id)) {
                    (Some(ty1), Some(ty2)) => self.structural_eq_tys(ty1, ty2),
                    _ => {
                        if g1.params.is_empty() && g2.params.is_empty() {
                            self.structural_eq_ast_tys(ty1, ty2)
                        } else {
                            // FIXME: handle generics (we don't need to for now)
                            false
                        }
                    }
                }
            }

            (Const(ty1, expr1), Const(ty2, expr2)) => {
                match (self.opt_node_type(item1.id), self.opt_node_type(item2.id)) {
                    (Some(ty1), Some(ty2)) => {
                        self.structural_eq_tys(ty1, ty2) && expr1.unnamed_equiv(expr2)
                    }
                    _ => self.structural_eq_ast_tys(ty1, ty2) && expr1.unnamed_equiv(expr2),
                }
            }

            (Use(_), Use(_)) => panic!("We should have already handled the use statement case"),

            (Struct(variant1, _), Struct(variant2, _))
            | (Union(variant1, _), Union(variant2, _)) => {
                match (self.opt_node_type(item1.id), self.opt_node_type(item2.id)) {
                    (Some(ty1), Some(ty2)) => self.structural_eq_tys(ty1, ty2),
                    _ => {
                        let mut fields = variant1.fields().iter().zip(variant2.fields().iter());
                        fields.all(|(field1, field2)| self.structural_eq_ast_tys(&field1.ty, &field2.ty))
                    }
                }
            }

            (Enum(enum1, _), Enum(enum2, _)) => {
                let variants = enum1.variants.iter().zip(enum2.variants.iter());
                let mut fields = variants.flat_map(|(variant1, variant2)| {
                    variant1
                        .data
                        .fields()
                        .iter()
                        .zip(variant2.data.fields().iter())
                });
                fields.all(|(field1, field2)| {
                    match (self.opt_node_type(field1.id), self.opt_node_type(field2.id)) {
                        (Some(ty1), Some(ty2)) => ty1 == ty2,
                        _ => false,
                    }
                })
            }

            _ => {
                if self.item_namespace(item1) == Some(Namespace::TypeNS) &&
                    self.item_namespace(item2) == Some(Namespace::TypeNS)
                {
                    match (self.opt_node_type(item1.id), self.opt_node_type(item2.id)) {
                        (Some(ty1), Some(ty2)) => return self.structural_eq_tys(ty1, ty2),
                        _ => {}
                    }
                }

                // Fall back on AST equivalence for other items
                item1.unnamed_equiv(item2)
            }
        }
    }

    /// Compare two function declarations for equivalent argument and return types,
    /// ignoring argument names.
    pub fn compatible_fn_prototypes(&self, decl1: &FnDecl, decl2: &FnDecl) -> bool {
        let mut args = decl1.inputs.iter().zip(decl2.inputs.iter());
        if !args.all(|(arg1, arg2)| self.structural_eq_ast_tys(&arg1.ty, &arg2.ty)) {
            return false;
        }

        // We assume we're dealing with function declaration prototypes, not
        // closures, so the default return type is ()
        let unit_ty = mk().tuple_ty::<P<ast::Ty>>(vec![]);
        let ty1 = match &decl1.output {
            FunctionRetTy::Default(..) => &unit_ty,
            FunctionRetTy::Ty(ty) => &ty,
        };
        let ty2 = match &decl2.output {
            FunctionRetTy::Default(..) => &unit_ty,
            FunctionRetTy::Ty(ty) => &ty,
        };

        self.structural_eq_ast_tys(ty1, ty2)
    }

    /// Compare two AST types for structural equivalence, ignoring names.
    fn structural_eq_ast_tys(&self, ty1: &ast::Ty, ty2: &ast::Ty) -> bool {
        match (self.opt_node_type(ty1.id), self.opt_node_type(ty2.id)) {
            (Some(ty1), Some(ty2)) => return self.structural_eq_tys(ty1, ty2),
            _ => {}
        }
        match (self.try_resolve_ty(ty1), self.try_resolve_ty(ty1)) {
            (Some(did1), Some(did2)) => self.structural_eq_defs(did1, did2),
            _ => ty1.unnamed_equiv(ty2),
        }
    }

    /// Compare two Ty types for structural equivalence, ignoring names.
    fn structural_eq_tys_impl(
        &self,
        ty1: Ty<'tcx>,
        ty2: Ty<'tcx>,
        seen: &mut HashSet<DefId>,
    ) -> bool {
        // TODO: Make this follow the C rules for structural equivalence rather
        // than strict equivalence
        if ty1 == ty2 {
            return true;
        }

        let tcx = self.ty_ctxt();

        match (&ty1.kind, &ty2.kind) {
            (TyKind::Adt(def1, substs1), TyKind::Adt(def2, substs2)) => {
                if substs1.types().count() != substs2.types().count() || 
                    !substs1.types().zip(substs2.types())
                         .all(|(ty1, ty2)| self.structural_eq_tys_impl(ty1, ty2, seen))
                {
                    trace!("Substituted types don't match between {:?} and {:?}", ty1, ty2);
                    return false;
                }
                // warning: we're ignore lifetime and const generic params

                if seen.contains(&def1.did) && seen.contains(&def2.did) {
                    return true;
                }

                def1.all_fields().count() == def2.all_fields().count() &&
                    def1.all_fields()
                        .zip(def2.all_fields())
                        .all(|(field1, field2)| {
                            self.structural_eq_defs_impl(field1.did, field2.did, seen)
                        })
            }

            (TyKind::Array(ty1, n1), TyKind::Array(ty2, n2)) => {
                let len1 = n1.try_eval_usize(tcx, ParamEnv::empty());
                let len2 = n2.try_eval_usize(tcx, ParamEnv::empty());
                // We allow 0 length arrays to match any length arrays. This
                // isn't exactly the C definition of compatible extern global
                // array types with global array definitions, but it should be
                // apply in practice as we translate empty extern array lengths
                // into 0 length extern arrays.
                if len1 != len2 && len1 != Some(0) && len2 != Some(0) {
                    trace!("Array lengths don't match: {:?} and {:?}", n1, n2);
                    return false;
                }
                self.structural_eq_tys_impl(ty1, ty2, seen)
            }

            (TyKind::Slice(ty1), TyKind::Slice(ty2)) => self.structural_eq_tys_impl(ty1, ty2, seen),

            (TyKind::RawPtr(ty1), TyKind::RawPtr(ty2)) => {
                if ty1.mutbl != ty2.mutbl { trace!("Mutability doesn't match: {:?} and {:?}", ty1, ty2); }
                ty1.mutbl == ty2.mutbl && self.structural_eq_tys_impl(ty1.ty, ty2.ty, seen)
            }

            (TyKind::Ref(region1, ty1, mutbl1), TyKind::Ref(region2, ty2, mutbl2)) => {
                if region1 != region2 { trace!("Regions don't match: {:?} and {:?}", ty1, ty2); }
                if mutbl1 != mutbl2 { trace!("Mutability doesn't match: {:?} and {:?}", ty1, ty2); }
                region1 == region2 && mutbl1 == mutbl2 && self.structural_eq_tys_impl(ty1, ty2, seen)
            }

            (TyKind::FnDef(fn1, substs1), TyKind::FnDef(fn2, substs2)) => {
                if substs1.types().count() != substs2.types().count() || 
                    !substs1.types().zip(substs2.types())
                         .all(|(ty1, ty2)| self.structural_eq_tys_impl(ty1, ty2, seen))
                {
                    trace!("Substituted types don't match between {:?} and {:?}", ty1, ty2);
                    return false;
                }
                // warning: we're ignore lifetime and const generic params

                self.structural_eq_defs_impl(*fn1, *fn2, seen)
            }

            (TyKind::FnPtr(fn1), TyKind::FnPtr(fn2)) => {
                let (fn1, fn2) = match (fn1.no_bound_vars(), fn2.no_bound_vars()) {
                    (Some(x), Some(y)) => (x, y),
                    _ => {
                        trace!("Function pointers have bound vars: {:?} and {:?}", fn1, fn2);
                        return false;
                    }
                };

                if fn1.inputs().len() != fn2.inputs().len() ||
                    fn1.c_variadic != fn2.c_variadic ||
                    fn1.abi != fn2.abi
                {
                    trace!("Function pointers attributes don't match: {:?} and {:?}", fn1, fn2);
                    return false;
                }

                if !self.structural_eq_tys_impl(fn1.output(), fn2.output(), seen) {
                    trace!("Function pointer output types don't match: {:?} and {:?}", fn1, fn2);
                    return false;
                }

                fn1.inputs().iter().zip(fn2.inputs().iter())
                    .all(|(ty1, ty2)| self.structural_eq_tys_impl(ty1, ty2, seen))
            }

            (TyKind::Tuple(_), TyKind::Tuple(_)) => {
                ty1.tuple_fields().count() == ty2.tuple_fields().count() &&
                    ty1.tuple_fields().zip(ty2.tuple_fields())
                       .all(|(ty1, ty2)| self.structural_eq_tys_impl(ty1, ty2, seen))
            }

            (TyKind::Foreign(did1), TyKind::Foreign(did2)) => {
                // Foreign types are matched by symbol name
                let matching = tcx.item_name(*did1) == tcx.item_name(*did2);
                if !matching { trace!("Foreign types did not match: {:?} and {:?}", ty1, ty2); }
                matching
            }

            // Allow foreign opaque types to match against any ADT with the same
            // name
            (TyKind::Foreign(foreign_did), TyKind::Adt(adt, _substs))
            | (TyKind::Adt(adt, _substs), TyKind::Foreign(foreign_did)) => {
                let matching = tcx.item_name(*foreign_did) == tcx.item_name(adt.did);
                if !matching { trace!("Foreign type did not match ADT: {:?} and {:?}", ty1, ty2); }
                matching
            }

            // We don't handle anything else here, and hopefully won't need
            // to...
            _ => {
                trace!("Unhandled types {:?} and {:?}", ty1.kind, ty2.kind);
                false
            }
        }
    }

    fn structural_eq_defs_impl(&self, did1: DefId, did2: DefId, seen: &mut HashSet<DefId>) -> bool {
        // Convert to TyCtxt types and compare
        if seen.contains(&did1) && seen.contains(&did2) {
            return true;
        }
        seen.insert(did1);
        seen.insert(did2);
        self.structural_eq_tys_impl(self.def_type(did1), self.def_type(did2), seen)
    }

    /// Compare two Defs for structural equivalence, ignoring names.
    pub fn structural_eq_defs(&self, did1: DefId, did2: DefId) -> bool {
        // We have to track which def ids we've seen so we don't recurse
        // infinitely
        let mut seen = HashSet::new();
        // Convert to TyCtxt types and compare
        self.structural_eq_defs_impl(did1, did2, &mut seen)
    }

    /// Compare two Tys for structural equivalence, ignoring names.
    pub fn structural_eq_tys(&self, ty1: Ty<'tcx>, ty2: Ty<'tcx>) -> bool {
        // We have to track which def ids we've seen so we don't recurse
        // infinitely
        let mut seen = HashSet::new();
        // Convert to TyCtxt types and compare
        self.structural_eq_tys_impl(ty1, ty2, &mut seen)
    }

    /// Are we refactoring an executable crate?
    pub fn is_executable(&self) -> bool {
        self.sess.crate_types.borrow().contains(&CrateType::Executable)
    }

    pub fn item_namespace(&self, item: &Item) -> Option<Namespace> {
        match &item.kind {
            ItemKind::Use(tree) => {
                // Nested uses should be already split apart
                if let UseTreeKind::Nested(..) = &tree.kind {
                    None
                } else {
                    let path = self.try_resolve_use_id(item.id)?;
                    namespace(&path.res)
                }
            }

            // Extern headers cannot contain impls
            ItemKind::Impl(..) => None,

            ItemKind::ForeignMod(_) => None,

            ItemKind::Static(..) | ItemKind::Const(..) | ItemKind::Fn(..) => Some(Namespace::ValueNS),

            _ => Some(Namespace::TypeNS),
        }
    }

    pub fn foreign_item_namespace(&self, item: &ForeignItem) -> Option<Namespace> {
        match &item.kind {
            ForeignItemKind::Fn(..) | ForeignItemKind::Static(..) => Some(Namespace::ValueNS),
            ForeignItemKind::Ty => Some(Namespace::TypeNS),
            ForeignItemKind::Macro(..) => None,
        }
    }
}

// Forwarding of HIR map queries so that we make sure to validate the NodeId, if
// applicable, first. We only validate the NodeId if the method returns an
// Option. If it can panic, it will just panic on an invalid NodeId.
impl<'a, 'hir> HirMap<'a, 'hir> {
    /// Map a crate NodeId to HirId, if possible. Only accepts NodeIds that were
    /// in the originally parsed crate.
    #[inline]
    pub fn opt_node_to_hir_id(&self, id: NodeId) -> Option<HirId> {
        if id > self.max_node_id {
            None
        } else {
            Some(self.map.node_to_hir_id(id))
        }
    }

    #[inline]
    pub fn node_to_hir_id(&self, id: NodeId) -> HirId {
        self.opt_node_to_hir_id(id)
            .unwrap_or_else(|| panic!("Could not find an HIR id for NodeId: {:?}", id))
    }

    /// Retrieves the `Node` corresponding to `id`, returning `None` if cannot be found.
    pub fn find(&self, id: NodeId) -> Option<Node<'hir>> {
        self.opt_node_to_hir_id(id)
            .and_then(|hir_id| self.map.find(hir_id))
    }

    /// Check if the node is an argument. An argument is a local variable whose
    /// immediate parent is an item or a closure.
    pub fn is_argument(&self, id: NodeId) -> bool {
        match self.opt_node_to_hir_id(id) {
            Some(id) => self.map.is_argument(id),
            None => false,
        }
    }
}

impl<'a, 'hir> Deref for HirMap<'a, 'hir> {
    type Target = hir_map::Map<'hir>;
    fn deref(&self) -> &Self::Target {
        self.map
    }
}

#[derive(Clone, Debug)]
pub struct CalleeInfo<'tcx> {
    /// The final signature used at the call site, after substituting in type and region arguments.
    pub fn_sig: FnSig<'tcx>,

    /// The un-substituted signature of the callee.
    pub poly_sig: PolyFnSig<'tcx>,

    /// The DefId of the function or method being called.  If the callee is a fn pointer, this is
    /// `None`.
    pub def_id: Option<DefId>,

    /// The type and region arguments that were substituted in at the call site.
    pub substs: Option<&'tcx InternalSubsts<'tcx>>,
}
