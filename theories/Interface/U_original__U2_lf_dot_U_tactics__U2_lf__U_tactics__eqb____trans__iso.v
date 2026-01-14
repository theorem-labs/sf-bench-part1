From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_eqb__trans : forall x x0 x1 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x x0) imported_Original_LF__DOT__Basics_LF_Basics_true ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x0 x1) imported_Original_LF__DOT__Basics_LF_Basics_true ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x x1) imported_Original_LF__DOT__Basics_LF_Basics_true.
Parameter Original_LF__DOT__Tactics_LF_Tactics_eqb__trans_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Original.LF_DOT_Basics.LF.Basics.eqb x1 x3 = Original.LF_DOT_Basics.LF.Basics.true)
    (x8 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x4) imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx0) Original_LF__DOT__Basics_LF_Basics_true_iso) x7 x8 ->
  forall (x9 : Original.LF_DOT_Basics.LF.Basics.eqb x3 x5 = Original.LF_DOT_Basics.LF.Basics.true)
    (x10 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x4 x6) imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx0 hx1) Original_LF__DOT__Basics_LF_Basics_true_iso) x9 x10 ->
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx1) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original.LF_DOT_Tactics.LF.Tactics.eqb_trans x1 x3 x5 x7 x9)
    (imported_Original_LF__DOT__Tactics_LF_Tactics_eqb__trans x8 x10).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_eqb__trans_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.eqb_trans ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_eqb__trans_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.eqb_trans imported_Original_LF__DOT__Tactics_LF_Tactics_eqb__trans ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_eqb__trans_iso; constructor : typeclass_instances.


End Interface.