//! `Splice` and `Rewrite` impls, to support the `rewrite` module.
//!
//! This code interacts closely with the impls generated by `gen/rewrite.py`.
use std::ops::Deref;
use std::rc::Rc;
use diff;
use rustc::session::Session;
use syntax::ast::*;
// use syntax::abi::Abi;
use rustc_target::spec::abi::Abi;
use syntax::codemap::{Span, Spanned, DUMMY_SP};
use syntax::ext::hygiene::SyntaxContext;
use syntax::print::pprust;
use syntax::ptr::P;
use syntax::tokenstream::{TokenStream, ThinTokenStream};
use syntax::util::parser::{self, AssocOp, Fixity};
use syntax_pos::FileName;

use driver;
use ast_manip::{GetNodeId, GetSpan};
use ast_manip::util::extended_span;
use rewrite::{Rewrite, RewriteCtxt, RewriteCtxtRef, ExprPrec, NodeTable, TextAdjust};
use util::Lone;


fn describe(sess: &Session, span: Span) -> String {
    let cm = sess.codemap();
    let lo = cm.lookup_byte_offset(span.lo());
    let hi = cm.lookup_byte_offset(span.hi());
    let src = &lo.fm.src.as_ref().unwrap()[lo.pos.0 as usize .. hi.pos.0 as usize];

    if Rc::ptr_eq(&lo.fm, &hi.fm) {
        format!("{}: {} .. {} = {}", lo.fm.name, lo.pos.0, hi.pos.0, src)
    } else {
        format!("{}: {} .. {}: {} = {}", lo.fm.name, lo.pos.0, hi.fm.name, hi.pos.0, src)
    }
}


/// Trait for types that are "splice points", where the output mode can switch from recycled to
/// fresh or back.
trait Splice: Rewrite+'static {
    fn span(&self) -> Span;
    fn id(&self) -> NodeId;

    /// Pretty print this node.
    fn to_string(&self) -> String;

    /// The result type of `Self::parse`.  Usually `P<T>`, but some types use the `SelfDeref<T>`
    /// helper.
    type Parsed: Deref<Target=Self>;
    /// Parse a string to a node of this type.  Panics if parsing fails.
    fn parse(sess: &Session, src: &str) -> Self::Parsed;

    /// Obtain from the `RewriteCtxt` the table of old nodes of this type.
    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self>;

    /// Get the text adjustment (such as parenthesization) to apply at this node, if any.
    fn get_adjustment(&self, _rcx: &RewriteCtxt) -> TextAdjust {
        TextAdjust::None
    }


    /// Try to look up a node in `rcx`'s old nodes table for this type.
    fn get_node<'a, 's>(mut rcx: RewriteCtxtRef<'s, 'a>, id: NodeId) -> Option<&'s Self> {
        Self::node_table(&mut rcx).get(id)
    }

    /// Perform a switch from recycled mode to fresh mode.  The text at `old_span` will be replaced
    /// with pretty-printed code for `new`.
    fn splice_recycled_span(new: &Self, old_span: Span, mut rcx: RewriteCtxtRef) {
        let printed = new.to_string();
        let reparsed = Self::parse(rcx.session(), &printed);

        if old_span.lo() != old_span.hi() {
            info!("REWRITE {}", describe(rcx.session(), old_span));
            info!("   INTO {}", describe(rcx.session(), reparsed.span()));
        } else {
            info!("INSERT AT {}", describe(rcx.session(), old_span));
            info!("     TEXT {}", describe(rcx.session(), reparsed.span()));
        }

        let mut rewrites = Vec::new();
        let old_fs = rcx.replace_fresh_start(new.span());
        Rewrite::rewrite_fresh(new, &reparsed, rcx.with_rewrites(&mut rewrites));
        rcx.replace_fresh_start(old_fs);

        let adj = new.get_adjustment(&rcx);
        rcx.record(old_span, reparsed.span(), rewrites, adj);
    }

    /// Perform a switch from recycled mode to fresh mode.  The source text for `old` will be
    /// replaced with pretty-printed code for `new`.
    fn splice_recycled(new: &Self, old: &Self, rcx: RewriteCtxtRef) {
        Splice::splice_recycled_span(new, old.span(), rcx);
    }

    /// Perform a switch from fresh mode to recycled mode.  `new` must have been copied directly
    /// from the old AST.  The source text for `reparsed`, which was previously spliced into the
    /// output buffer by a `splice_recycled_span` call, will be replaced with the original source
    /// text for `new`.
    ///
    /// Returns `true` if the rewrite was successful.
    fn splice_fresh(new: &Self, reparsed: &Self, mut rcx: RewriteCtxtRef) -> bool {
        // Don't try to replace the entire fresh subtree with old text.   This breaks an infinite
        // recursion when a non-splice-point child differs between the old and new ASTs.  In such a
        // situation, `splice_recycled` wants to replace the old text with newly printed text
        // (because `old != new`), but `splice_fresh` wants to replace the printed text with the
        // old text (because `new` still has a source span covering the old text).  It's always
        // safe to use printed text instead of old text, so we bail out here if we detect this.
        if new.span() == rcx.fresh_start() {
            return false;
        }

        let old = match Self::get_node(rcx.borrow(), new.id()) {
            Some(x) => x,
            None => {
                return false;
            },
        };


        if old.span() == DUMMY_SP {
            return false;
        }

        let fm = rcx.session().codemap().lookup_byte_offset(old.span().lo()).fm;
        if let FileName::Macros(..) = fm.name {
            return false;
        }

        info!("REVERT {}", describe(rcx.session(), reparsed.span()));
        info!("    TO {}", describe(rcx.session(), old.span()));

        let mut rewrites = Vec::new();
        let mark = rcx.mark();
        let failed = Rewrite::rewrite_recycled(new, old, rcx.with_rewrites(&mut rewrites));
        if failed {
            rcx.rewind(mark);
            return false;
        }

        let adj = new.get_adjustment(&rcx);
        rcx.record(reparsed.span(), old.span(), rewrites, adj);
        true
    }
}


/// Helper type to provide a `Deref<Target = T>` impl for any `T`.  This is used in a few places to
/// satisfy the `Splice::Parsed` associated type.
struct SelfDeref<T>(pub T);
impl<T> Deref for SelfDeref<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl Splice for Expr {
    fn span(&self) -> Span {
        extended_span(self.span, &self.attrs)
    }

    fn id(&self) -> NodeId {
        self.id
    }

    fn to_string(&self) -> String {
        pprust::expr_to_string(self)
    }

    type Parsed = P<Expr>;
    fn parse(sess: &Session, src: &str) -> Self::Parsed {
        driver::parse_expr(sess, src)
    }

    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self> {
        rcx.old_exprs()
    }

    fn get_adjustment(&self, rcx: &RewriteCtxt) -> TextAdjust {
        // Check for cases where we can safely omit parentheses.
        let prec = self.precedence();
        let need_parens = match rcx.expr_prec() {
            ExprPrec::Normal(min_prec) => prec.order() < min_prec,
            ExprPrec::Cond(min_prec) =>
                prec.order() < min_prec || parser::contains_exterior_struct_lit(self),
            ExprPrec::Callee(min_prec) => match self.node {
                ExprKind::Field(..) => true,
                _ => prec.order() < min_prec,
            },
        };

        if need_parens {
            TextAdjust::Parenthesize
        } else {
            TextAdjust::None
        }
    }
}

impl Splice for Pat {
    fn span(&self) -> Span {
        self.span
    }

    fn id(&self) -> NodeId {
        self.id
    }

    fn to_string(&self) -> String {
        pprust::pat_to_string(self)
    }

    type Parsed = P<Pat>;
    fn parse(sess: &Session, src: &str) -> Self::Parsed {
        driver::parse_pat(sess, src)
    }

    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self> {
        rcx.old_pats()
    }
}

impl Splice for Ty {
    fn span(&self) -> Span {
        self.span
    }

    fn id(&self) -> NodeId {
        self.id
    }

    fn to_string(&self) -> String {
        pprust::ty_to_string(self)
    }

    type Parsed = P<Ty>;
    fn parse(sess: &Session, src: &str) -> Self::Parsed {
        driver::parse_ty(sess, src)
    }

    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self> {
        rcx.old_tys()
    }
}

impl Splice for Stmt {
    fn span(&self) -> Span {
        self.span
    }

    fn id(&self) -> NodeId {
        self.id
    }

    fn to_string(&self) -> String {
        pprust::stmt_to_string(self)
    }

    type Parsed = SelfDeref<Stmt>;
    fn parse(sess: &Session, src: &str) -> Self::Parsed {
        let stmt = driver::parse_stmts(sess, src).lone();
        SelfDeref(stmt)
    }

    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self> {
        rcx.old_stmts()
    }
}

impl Splice for Item {
    fn span(&self) -> Span {
        extended_span(self.span, &self.attrs)
    }

    fn id(&self) -> NodeId {
        self.id
    }

    fn to_string(&self) -> String {
        pprust::item_to_string(self)
    }

    type Parsed = P<Item>;
    fn parse(sess: &Session, src: &str) -> Self::Parsed {
        driver::parse_items(sess, src).lone()
    }

    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self> {
        rcx.old_items()
    }
}

impl Splice for ForeignItem {
    fn span(&self) -> Span {
        extended_span(self.span, &self.attrs)
    }

    fn id(&self) -> NodeId {
        self.id
    }

    fn to_string(&self) -> String {
        pprust::to_string(|s| s.print_foreign_item(self))
    }

    type Parsed = SelfDeref<ForeignItem>;
    fn parse(sess: &Session, src: &str) -> Self::Parsed {
        let fi = driver::parse_foreign_items(sess, src).lone();
        SelfDeref(fi)
    }

    fn node_table<'a, 's>(rcx: &'a mut RewriteCtxt<'s>) -> &'a mut NodeTable<'s, Self> {
        rcx.old_foreign_items()
    }
}


/// AST node types where sequence rewriting can apply.  Some of these impls are generated by
/// `gen/rewrite.py`.
pub trait SeqItem {
    #[inline]
    fn supported() -> bool { false }

    fn get_span(&self) -> Span { unimplemented!() }
    fn get_id(&self) -> NodeId { unimplemented!() }

    fn splice_recycled_span(_new: &Self, _old_span: Span, _rcx: RewriteCtxtRef) {
        unimplemented!()
    }
}

impl<T: SeqItem> SeqItem for P<T> {
    #[inline]
    fn supported() -> bool { <T as SeqItem>::supported() }

    fn get_span(&self) -> Span {
        <T as SeqItem>::get_span(self)
    }

    fn get_id(&self) -> NodeId {
        <T as SeqItem>::get_id(self)
    }

    fn splice_recycled_span(new: &Self, old_span: Span, rcx: RewriteCtxtRef) {
        <T as SeqItem>::splice_recycled_span(new, old_span, rcx);
    }
}

impl<T: SeqItem> SeqItem for Rc<T> {
    #[inline]
    fn supported() -> bool { <T as SeqItem>::supported() }

    fn get_span(&self) -> Span {
        <T as SeqItem>::get_span(self)
    }

    fn get_id(&self) -> NodeId {
        <T as SeqItem>::get_id(self)
    }

    fn splice_recycled_span(new: &Self, old_span: Span, rcx: RewriteCtxtRef) {
        <T as SeqItem>::splice_recycled_span(new, old_span, rcx);
    }
}

// Stub impls
impl<T: SeqItem> SeqItem for Spanned<T> {}
impl<T: SeqItem> SeqItem for Option<T> {}
impl<A: SeqItem, B: SeqItem> SeqItem for (A, B) {}
impl<A: SeqItem, B: SeqItem, C: SeqItem> SeqItem for (A, B, C) {}


// Generic Rewrite impls

impl<T: Rewrite> Rewrite for P<T> {
    fn rewrite_recycled(&self, old: &Self, rcx: RewriteCtxtRef) -> bool {
        <T as Rewrite>::rewrite_recycled(self, old, rcx)
    }

    fn rewrite_fresh(&self, reparsed: &Self, rcx: RewriteCtxtRef) {
        <T as Rewrite>::rewrite_fresh(self, reparsed, rcx);
    }
}

impl<T: Rewrite> Rewrite for Rc<T> {
    fn rewrite_recycled(&self, old: &Self, rcx: RewriteCtxtRef) -> bool {
        <T as Rewrite>::rewrite_recycled(self, old, rcx)
    }

    fn rewrite_fresh(&self, reparsed: &Self, rcx: RewriteCtxtRef) {
        <T as Rewrite>::rewrite_fresh(self, reparsed, rcx);
    }
}

impl<T: Rewrite> Rewrite for Spanned<T> {
    fn rewrite_recycled(&self, old: &Self, rcx: RewriteCtxtRef) -> bool {
        <T as Rewrite>::rewrite_recycled(&self.node, &old.node, rcx)
    }

    fn rewrite_fresh(&self, reparsed: &Self, rcx: RewriteCtxtRef) {
        <T as Rewrite>::rewrite_fresh(&self.node, &reparsed.node, rcx);
    }
}

impl<T: Rewrite> Rewrite for Option<T> {
    fn rewrite_recycled(&self, old: &Self, rcx: RewriteCtxtRef) -> bool {
        match (self, old) {
            (&Some(ref x1),
             &Some(ref x2)) => {
                Rewrite::rewrite_recycled(x1, x2, rcx)
            }
            (&None, &None) => false,
            (_, _) => true,
        }
    }

    fn rewrite_fresh(&self, reparsed: &Self, rcx: RewriteCtxtRef) {
        match (self, reparsed) {
            (&Some(ref x1),
             &Some(ref x2)) => {
                Rewrite::rewrite_fresh(x1, x2, rcx);
            },
            (&None, &None) => {},
            (_, _) => panic!("new and reparsed ASTs differ"),
        }
    }
}

impl<A: Rewrite, B: Rewrite> Rewrite for (A, B) {
    fn rewrite_recycled(&self, old: &Self, mut rcx: RewriteCtxtRef) -> bool {
        <A as Rewrite>::rewrite_recycled(&self.0, &old.0, rcx.borrow()) ||
        <B as Rewrite>::rewrite_recycled(&self.1, &old.1, rcx.borrow()) ||
        false
    }

    fn rewrite_fresh(&self, reparsed: &Self, mut rcx: RewriteCtxtRef) {
        <A as Rewrite>::rewrite_fresh(&self.0, &reparsed.0, rcx.borrow());
        <B as Rewrite>::rewrite_fresh(&self.1, &reparsed.1, rcx.borrow());
    }
}

impl<A: Rewrite, B: Rewrite, C: Rewrite> Rewrite for (A, B, C) {
    fn rewrite_recycled(&self, old: &Self, mut rcx: RewriteCtxtRef) -> bool {
        <A as Rewrite>::rewrite_recycled(&self.0, &old.0, rcx.borrow()) ||
        <B as Rewrite>::rewrite_recycled(&self.1, &old.1, rcx.borrow()) ||
        <C as Rewrite>::rewrite_recycled(&self.2, &old.2, rcx.borrow()) ||
        false
    }

    fn rewrite_fresh(&self, reparsed: &Self, mut rcx: RewriteCtxtRef) {
        <A as Rewrite>::rewrite_fresh(&self.0, &reparsed.0, rcx.borrow());
        <B as Rewrite>::rewrite_fresh(&self.1, &reparsed.1, rcx.borrow());
        <C as Rewrite>::rewrite_fresh(&self.2, &reparsed.2, rcx.borrow());
    }
}


// Sequence rewriting implementation.  The goal is to allow insertion and deletion of items without
// triggering reprinting of the entire sequnece.
impl<T: Rewrite+SeqItem> Rewrite for [T] {
    fn rewrite_recycled(&self, old: &Self, mut rcx: RewriteCtxtRef) -> bool {
        if !<T as SeqItem>::supported() {
            if self.len() != old.len() {
                // Length changed, and sequence rewriting is unsupported for this node type, so
                // there's nothing we can do.
                return true;
            }

            // Replace each item with the corresponding item from the new sequence.
            for i in 0 .. self.len() {
                if Rewrite::rewrite_recycled(&self[i], &old[i], rcx.borrow()) {
                    return true;
                }
            }
            false
        } else {
            if old.len() == 0 && self.len() != 0 {
                // We can't handle this case because it provides us with no span information about
                // the `old` side.  We need the spans so we know where to splice in any new items.
                return true;
            }

            // We diff the sequences of `NodeId`s to match up nodes on the left and the right.
            // This works because the old AST has `NodeId`s assigned properly.  (The new AST might
            // not, but in that case we will properly detect a change.)
            let new_ids = self.iter().map(|x| x.get_id()).collect::<Vec<_>>();
            let old_ids = old.iter().map(|x| x.get_id()).collect::<Vec<_>>();

            let mut i = 0;
            let mut j = 0;

            for step in diff::slice(&old_ids, &new_ids) {
                match step {
                    diff::Result::Left(_) => {
                        // There's an item on the left corresponding to nothing on the right.
                        // Delete the item from the left.
                        info!("DELETE {}", describe(rcx.session(), old[i].get_span()));
                        rcx.record(old[i].get_span(), DUMMY_SP, vec![], TextAdjust::None);
                        i += 1;
                    },
                    diff::Result::Right(_) => {
                        // There's an item on the right corresponding to nothing on the left.
                        // Insert the item before the current item on the left, rewriting
                        // recursively.
                        let old_span =
                            if i > 0 {
                                let s = old[i - 1].get_span();
                                s.with_lo(s.hi())
                            } else {
                                let s = old[0].get_span();
                                s.with_hi(s.lo())
                            };
                        SeqItem::splice_recycled_span(&self[j], old_span, rcx.borrow());
                        j += 1;
                    },
                    diff::Result::Both(_, _) => {
                        if Rewrite::rewrite_recycled(&self[j], &old[i], rcx.borrow()) {
                            // Rewriting failed inside the item.
                            return true;
                        }
                        i += 1;
                        j += 1;
                    },
                }
            }

            false
        }
    }

    fn rewrite_fresh(&self, reparsed: &Self, mut rcx: RewriteCtxtRef) {
        // Lengths should be the same, since `reparsed` should be structurally identical to `self`.
        assert!(self.len() == reparsed.len());

        for i in 0 .. self.len() {
            Rewrite::rewrite_fresh(&self[i], &reparsed[i], rcx.borrow());
        }
    }
}

impl<T: Rewrite+SeqItem> Rewrite for Vec<T> {
    fn rewrite_recycled(&self, old: &Self, rcx: RewriteCtxtRef) -> bool {
        <[T] as Rewrite>::rewrite_recycled(&self, &old, rcx)
    }

    fn rewrite_fresh(&self, reparsed: &Self, rcx: RewriteCtxtRef) {
        <[T] as Rewrite>::rewrite_fresh(&self, &reparsed, rcx);
    }
}

impl<T: Rewrite+SeqItem> Rewrite for ThinVec<T> {
    fn rewrite_recycled(&self, old: &Self, rcx: RewriteCtxtRef) -> bool {
        <[T] as Rewrite>::rewrite_recycled(&self, &old, rcx)
    }

    fn rewrite_fresh(&self, reparsed: &Self, rcx: RewriteCtxtRef) {
        <[T] as Rewrite>::rewrite_fresh(&self, &reparsed, rcx);
    }
}


include!(concat!(env!("OUT_DIR"), "/rewrite_impls_gen.inc.rs"));

fn binop_left_prec(op: &BinOp) -> i8 {
    let assoc_op = AssocOp::from_ast_binop(op.node);
    let prec = assoc_op.precedence() as i8;
    let fixity = assoc_op.fixity();

    match fixity {
        Fixity::Left => prec,
        Fixity::Right => prec + 1,
        Fixity::None => prec + 1,
    }
}

fn binop_right_prec(op: &BinOp) -> i8 {
    let assoc_op = AssocOp::from_ast_binop(op.node);
    let prec = assoc_op.precedence() as i8;
    let fixity = assoc_op.fixity();

    match fixity {
        Fixity::Left => prec + 1,
        Fixity::Right => prec,
        Fixity::None => prec + 1,
    }
}
