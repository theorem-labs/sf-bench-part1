From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__square__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__square__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__square__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__square__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_square__mult : forall x x0 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Tactics_LF_Tactics_square (imported_Nat_mul x x0))
    (imported_Nat_mul (imported_Original_LF__DOT__Tactics_LF_Tactics_square x) (imported_Original_LF__DOT__Tactics_LF_Tactics_square x0)).
Parameter Original_LF__DOT__Tactics_LF_Tactics_square__mult_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Tactics_LF_Tactics_square_iso (Nat_mul_iso hx hx0))
       (Nat_mul_iso (Original_LF__DOT__Tactics_LF_Tactics_square_iso hx) (Original_LF__DOT__Tactics_LF_Tactics_square_iso hx0)))
    (Original.LF_DOT_Tactics.LF.Tactics.square_mult x1 x3) (imported_Original_LF__DOT__Tactics_LF_Tactics_square__mult x2 x4).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_square__mult_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.square_mult ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_square__mult_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.square_mult imported_Original_LF__DOT__Tactics_LF_Tactics_square__mult ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_square__mult_iso; constructor : typeclass_instances.


End Interface.