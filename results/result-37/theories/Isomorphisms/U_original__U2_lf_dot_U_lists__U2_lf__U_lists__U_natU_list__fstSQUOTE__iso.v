From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst' : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst'.

Lemma fst'_iso_helper : forall (p : Original.LF_DOT_Lists.LF.Lists.NatList.natprod),
  IsomorphismDefinitions.eq
    (nat_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.fst' p))
    (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst' (natprod_to_imported p)).
Proof.
  intros p. destruct p as [n1 n2]. simpl.
  native_compute. apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_fst'_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.fst' x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst' x2).
Proof.
  intros x1 x2 Hrel.
  constructor. simpl.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_fst'.
  pose proof (fst'_iso_helper x1) as Hfst.
  eapply IsoEq.eq_trans.
  - exact Hfst.
  - apply IsoEq.f_equal. exact (proj_rel_iso Hrel).
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.fst' := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst' := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.fst' Original_LF__DOT__Lists_LF_Lists_NatList_fst'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.fst' Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst' Original_LF__DOT__Lists_LF_Lists_NatList_fst'_iso := {}.
