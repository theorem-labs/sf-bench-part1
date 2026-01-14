From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__app__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil__app : forall x : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil x) x := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nil__app.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_nil__app_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist)
    (hx : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso hx) hx;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso hx) hx);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil x2) x2 =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso hx) hx) x;
      from_to :=
        fun x : Original.LF_DOT_Lists.LF.Lists.NatList.app Original.LF_DOT_Lists.LF.Lists.NatList.nil x1 = x1 =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso hx) hx) x)
    |} (Original.LF_DOT_Lists.LF.Lists.NatList.nil_app x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil__app x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  (* The goal is to show the `to` of the Iso maps (nil_app x1) to (imported_nil_app x2) *)
  (* Both sides are in SProp, so they're equal by proof irrelevance in SProp *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.nil_app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nil__app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.nil_app Original_LF__DOT__Lists_LF_Lists_NatList_nil__app_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.nil_app Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nil__app Original_LF__DOT__Lists_LF_Lists_NatList_nil__app_iso := {}.