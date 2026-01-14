From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso Interface.U_s__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Induction_LF_Induction_double__incr : forall x : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Induction_LF_Induction_double (imported_S x)) (imported_S (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double x))).
Parameter Original_LF__DOT__Induction_LF_Induction_double__incr_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Induction_LF_Induction_double_iso (S_iso hx)) (S_iso (S_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx))))
    (Original.LF_DOT_Induction.LF.Induction.double_incr x1) (imported_Original_LF__DOT__Induction_LF_Induction_double__incr x2).
Existing Instance Original_LF__DOT__Induction_LF_Induction_double__incr_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double_incr ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double__incr_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double_incr imported_Original_LF__DOT__Induction_LF_Induction_double__incr ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double__incr_iso; constructor : typeclass_instances.


End Interface.