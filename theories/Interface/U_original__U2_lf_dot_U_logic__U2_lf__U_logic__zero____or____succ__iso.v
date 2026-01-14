From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__pred__iso Interface.U_s__iso Interface.__0__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__pred__iso Interface.U_s__iso Interface.__0__iso Interface.or__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__pred__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__pred__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_zero__or__succ : forall x : imported_nat, imported_or (imported_Corelib_Init_Logic_eq x imported_0) (imported_Corelib_Init_Logic_eq x (imported_S (imported_Nat_pred x))).
Parameter Original_LF__DOT__Logic_LF_Logic_zero__or__succ_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := or_iso (Corelib_Init_Logic_eq_iso hx _0_iso) (Corelib_Init_Logic_eq_iso hx (S_iso (Nat_pred_iso hx)));
      from := from (or_iso (Corelib_Init_Logic_eq_iso hx _0_iso) (Corelib_Init_Logic_eq_iso hx (S_iso (Nat_pred_iso hx))));
      to_from :=
        fun x : imported_or (imported_Corelib_Init_Logic_eq x2 imported_0) (imported_Corelib_Init_Logic_eq x2 (imported_S (imported_Nat_pred x2))) =>
        to_from (or_iso (Corelib_Init_Logic_eq_iso hx _0_iso) (Corelib_Init_Logic_eq_iso hx (S_iso (Nat_pred_iso hx)))) x;
      from_to := fun x : x1 = 0 \/ x1 = S (Nat.pred x1) => seq_p_of_t (from_to (or_iso (Corelib_Init_Logic_eq_iso hx _0_iso) (Corelib_Init_Logic_eq_iso hx (S_iso (Nat_pred_iso hx)))) x)
    |} (Original.LF_DOT_Logic.LF.Logic.zero_or_succ x1) (imported_Original_LF__DOT__Logic_LF_Logic_zero__or__succ x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_zero__or__succ_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.zero_or_succ ?x) => unify x Original_LF__DOT__Logic_LF_Logic_zero__or__succ_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.zero_or_succ imported_Original_LF__DOT__Logic_LF_Logic_zero__or__succ ?x) => unify x Original_LF__DOT__Logic_LF_Logic_zero__or__succ_iso; constructor : typeclass_instances.


End Interface.