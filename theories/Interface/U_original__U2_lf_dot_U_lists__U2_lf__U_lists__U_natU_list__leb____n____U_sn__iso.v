From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso Interface.U_s__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb x (imported_S x)) imported_Original_LF__DOT__Basics_LF_Basics_true.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso hx (S_iso hx)) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original.LF_DOT_Lists.LF.Lists.NatList.leb_n_Sn x1)
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn x2).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.leb_n_Sn ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.leb_n_Sn imported_Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn_iso; constructor : typeclass_instances.


End Interface.