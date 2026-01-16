From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_nat -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad.
Lemma nth_bad_iso_core : forall l1 n1,
  IsomorphismDefinitions.eq (to nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad l1 n1))
                            (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad (to Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso l1) (to nat_iso n1)).
Proof.
  fix IH 1.
  intro l1. destruct l1; intro n1; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - destruct n1; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply IH.
Qed.

Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad x2 x4).
Proof.
  intros l1 l2 Hl n1 n2 Hn.
  destruct Hl as [Hl]. destruct Hn as [Hn].
  constructor. simpl.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad.
  apply (eq_trans (nth_bad_iso_core l1 n1)).
  apply (f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad Hl Hn).
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad_iso := {}.