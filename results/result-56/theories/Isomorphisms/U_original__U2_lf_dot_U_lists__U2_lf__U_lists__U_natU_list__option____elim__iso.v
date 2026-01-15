From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_option__elim : imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim.

Lemma option_elim_compat : forall d o,
  nat_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.option_elim d o) =
  Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim (nat_to_imported d) (natoption_to_imported o).
Proof.
  intros d o.
  destruct o; reflexivity.
Defined.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_option__elim_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Lists.LF.Lists.NatList.natoption) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso x3 x4 ->
  rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.option_elim x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_option__elim x2 x4).
Proof.
  intros x1 x2 Hx x3 x4 Ho.
  constructor. simpl.
  eapply eq_trans.
  { apply seq_of_eq. apply option_elim_compat. }
  apply f_equal2.
  - exact (proj_rel_iso Hx).
  - exact (proj_rel_iso Ho).
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.option_elim := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.option_elim Original_LF__DOT__Lists_LF_Lists_NatList_option__elim_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.option_elim Imported.Original_LF__DOT__Lists_LF_Lists_NatList_option__elim Original_LF__DOT__Lists_LF_Lists_NatList_option__elim_iso := {}.