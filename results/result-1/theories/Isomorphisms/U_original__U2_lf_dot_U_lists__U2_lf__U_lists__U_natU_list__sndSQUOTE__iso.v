From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd' : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd'.

Lemma snd'_eq : forall m n, Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd' (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_pair m n) = n.
Proof. intros. reflexivity. Qed.

Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_snd'_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.snd' x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd' x2).
Proof.
  intros x1 x2 Hx.
  destruct x1 as [n1 n2].
  constructor.
  simpl.
  assert (H := proj_rel_iso Hx). simpl in H.
  rewrite <- (snd'_eq (nat_to_imported n1) (nat_to_imported n2)).
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd'.
  apply f_equal. exact H.
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.snd' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.snd' Original_LF__DOT__Lists_LF_Lists_NatList_snd'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.snd' Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd' Original_LF__DOT__Lists_LF_Lists_NatList_snd'_iso := {}.