From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.list__iso Interface.cons__iso Interface.nat__iso Interface.nil__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.list__iso Interface.cons__iso Interface.nat__iso Interface.nil__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.cons__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.nil__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.list__iso.Interface <+ Interface.cons__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.nil__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1 : forall x x0 x1 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_cons x (imported_cons x0 (imported_nil imported_nat))) (imported_cons x (imported_cons x1 (imported_nil imported_nat))) ->
  imported_Corelib_Init_Logic_eq x0 x1.
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : (x1 :: x3 :: nil)%list = (x1 :: x5 :: nil)%list)
    (x8 : imported_Corelib_Init_Logic_eq (imported_cons x2 (imported_cons x4 (imported_nil imported_nat))) (imported_cons x2 (imported_cons x6 (imported_nil imported_nat)))),
  rel_iso (Corelib_Init_Logic_eq_iso (cons_iso hx (cons_iso hx0 (nil_iso nat_iso))) (cons_iso hx (cons_iso hx1 (nil_iso nat_iso)))) x7 x8 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx0 hx1) (Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1 x7) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1 x8).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1) ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1) imported_Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso; constructor : typeclass_instances.


End Interface.