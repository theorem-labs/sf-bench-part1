From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_option__elim : imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_option__elim_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Lists.LF.Lists.NatList.natoption) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso x3 x4 ->
  rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.option_elim x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_option__elim x2 x4).
Proof.
  intros x1 x2 Hx x3 x4 Ho.
  unfold rel_iso in *. simpl in *.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_option__elim.
  destruct x3 as [n | ]; simpl.
  - (* Some case *)
    unfold natoption_to_imported in Ho. simpl in Ho.
    destruct Ho.
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* None case *)
    unfold natoption_to_imported in Ho. simpl in Ho.
    destruct Ho. destruct Hx.
    simpl. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.option_elim := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.option_elim Original_LF__DOT__Lists_LF_Lists_NatList_option__elim_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.option_elim Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim Original_LF__DOT__Lists_LF_Lists_NatList_option__elim_iso := {}.