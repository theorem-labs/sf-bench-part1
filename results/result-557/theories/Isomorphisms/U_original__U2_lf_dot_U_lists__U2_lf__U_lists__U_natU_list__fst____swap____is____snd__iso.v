From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__fst__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__snd__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__swap____pair__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd : forall x : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst (imported_Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair x))
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd x) := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod)
    (hx : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso x1 x2),
  rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_fst_iso (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso hx)) (Original_LF__DOT__Lists_LF_Lists_NatList_snd_iso hx);
      from :=
        from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_fst_iso (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso hx))
             (Original_LF__DOT__Lists_LF_Lists_NatList_snd_iso hx));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst (imported_Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair x2))
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd x2) =>
        to_from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_fst_iso (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso hx))
             (Original_LF__DOT__Lists_LF_Lists_NatList_snd_iso hx))
          x;
      from_to :=
        fun x : Original.LF_DOT_Lists.LF.Lists.NatList.fst (Original.LF_DOT_Lists.LF.Lists.NatList.swap_pair x1) = Original.LF_DOT_Lists.LF.Lists.NatList.snd x1 =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_fst_iso (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso hx))
                (Original_LF__DOT__Lists_LF_Lists_NatList_snd_iso hx))
             x)
    |} (Original.LF_DOT_Lists.LF.Lists.NatList.fst_swap_is_snd x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  reflexivity.
Qed.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.fst_swap_is_snd := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.fst_swap_is_snd Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.fst_swap_is_snd Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd_iso := {}.