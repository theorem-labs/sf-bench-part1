From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__fst__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__pair__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__snd__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__fst__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__pair__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__snd__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__fst__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__pair__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__snd__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__fst__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__pair__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__snd__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing' : forall x x0 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_pair x x0)
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_pair (imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst (imported_Original_LF__DOT__Lists_LF_Lists_NatList_pair x x0))
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd (imported_Original_LF__DOT__Lists_LF_Lists_NatList_pair x x0))).
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_pair_iso hx hx0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_pair_iso (Original_LF__DOT__Lists_LF_Lists_NatList_fst_iso (Original_LF__DOT__Lists_LF_Lists_NatList_pair_iso hx hx0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_snd_iso (Original_LF__DOT__Lists_LF_Lists_NatList_pair_iso hx hx0))))
    (Original.LF_DOT_Lists.LF.Lists.NatList.surjective_pairing' x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing' x2 x4).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.surjective_pairing' ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.surjective_pairing' imported_Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing' ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing'_iso; constructor : typeclass_instances.


End Interface.