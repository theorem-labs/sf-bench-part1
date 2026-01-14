From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Induction_LF_Induction_double__plus : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Induction_LF_Induction_double x) (imported_Nat_add x x).
Parameter Original_LF__DOT__Induction_LF_Induction_double__plus_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx) (Nat_add_iso hx hx)) (Original.LF_DOT_Induction.LF.Induction.double_plus x1)
    (imported_Original_LF__DOT__Induction_LF_Induction_double__plus x2).
Existing Instance Original_LF__DOT__Induction_LF_Induction_double__plus_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double_plus ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double__plus_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double_plus imported_Original_LF__DOT__Induction_LF_Induction_double__plus ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double__plus_iso; constructor : typeclass_instances.


End Interface.