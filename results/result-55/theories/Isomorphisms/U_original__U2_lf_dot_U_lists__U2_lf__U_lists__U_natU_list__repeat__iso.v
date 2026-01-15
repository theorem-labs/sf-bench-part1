From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso.

Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat : imported_nat -> imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat.

Lemma imported_repeat_unfold_O : forall n,
  imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat n Imported.nat_O = 
  Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_nil.
Proof. intros. reflexivity. Qed.

Lemma imported_repeat_unfold_S : forall n c,
  imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat n (Imported.nat_S c) = 
  Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons n 
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat n c).
Proof. intros. reflexivity. Qed.

Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso (Original.LF_DOT_Lists.LF.Lists.NatList.repeat x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat x2 x4).
Proof.
  intros x1 x2 hx1 x3 x4 hx3.
  destruct hx1 as [Hn]. simpl in Hn. destruct Hn.
  destruct hx3 as [Hc]. simpl in Hc. destruct Hc.
  induction x3 as [|x3' IH].
  - simpl. rewrite imported_repeat_unfold_O.
    apply Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso.
  - simpl. rewrite imported_repeat_unfold_S.
    apply Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso.
    + constructor. apply IsomorphismDefinitions.eq_refl.
    + exact IH.
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.repeat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.repeat Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.repeat Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso := {}.