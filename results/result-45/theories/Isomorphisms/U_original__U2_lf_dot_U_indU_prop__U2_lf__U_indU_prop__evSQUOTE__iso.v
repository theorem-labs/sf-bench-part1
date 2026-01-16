From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

(* Convert Lean Eq to Logic.eq *)
#[local] Unset Universe Polymorphism.
Lemma Eq_to_eq : forall A (x y : A), Imported.LeanEq A x y -> x = y.
Proof.
  intros A x y H. destruct H. reflexivity.
Qed.

(* Helper lemma for nat_add O case *)
Lemma nat_add_O_eq : forall m : imported_nat, Imported.nat_add Imported.nat_O m = m.
Proof.
  intro m. apply Eq_to_eq. exact (Imported.nat_add_O m).
Qed.

(* Helper lemma for nat_add S case *)
Lemma nat_add_S_eq : forall n m : imported_nat, 
  Imported.nat_add (Imported.nat_S n) m = Imported.nat_S (Imported.nat_add n m).
Proof.
  intros n m. apply Eq_to_eq. exact (Imported.nat_add_S n m).
Qed.

(* Helper: show that nat_iso preserves addition *)
Lemma nat_add_iso : forall (n m : nat),
  Imported.nat_add (to nat_iso n) (to nat_iso m) = to nat_iso (n + m).
Proof.
  induction n; intro m.
  - apply nat_add_O_eq.
  - specialize (IHn m). simpl.
    etransitivity.
    + apply nat_add_S_eq.
    + f_equal. exact IHn.
Qed.
#[local] Set Universe Polymorphism.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev' : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'.

(* Forward: ev' n -> imported_ev' (nat_iso n) *)
Lemma ev'_to_imported : forall (n : nat), 
  Original.LF_DOT_IndProp.LF.IndProp.ev' n -> 
  Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' (to nat_iso n).
Proof.
  intros n H.
  induction H.
  - (* ev'_0 *) exact Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_0.
  - (* ev'_2 *) exact Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_2.
  - (* ev'_sum *) 
    rewrite <- nat_add_iso.
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_sum _ _ IHev'1 IHev'2).
Qed.

(* Helper lemmas for from side *)
Lemma nat_from_add_O_eq : forall m : imported_nat, 
  from nat_iso (Imported.nat_add Imported.nat_O m) = from nat_iso m.
Proof.
  intro m. 
  pose proof (nat_add_O_eq m) as H.
  unfold from; simpl.
  destruct H. reflexivity.
Qed.

Lemma nat_from_add_S_eq : forall n m : imported_nat, 
  from nat_iso (Imported.nat_add (Imported.nat_S n) m) = S (from nat_iso (Imported.nat_add n m)).
Proof.
  intros n m. 
  pose proof (nat_add_S_eq n m) as H.
  unfold from at 1. simpl.
  destruct H. reflexivity.
Qed.

(* Helper: from nat_iso preserves addition *)
Lemma nat_from_add_iso : forall (n m : imported_nat),
  from nat_iso (Imported.nat_add n m) = from nat_iso n + from nat_iso m.
Proof.
  induction n; intro m; simpl.
  - apply nat_from_add_O_eq.
  - etransitivity.
    + apply nat_from_add_S_eq.
    + simpl. f_equal. apply IHn.
Qed.

(* Backward: imported_ev' m -> SInhabited (ev' (from nat_iso m)) *)
Lemma ev'_from_imported_SInhabited : forall (m : imported_nat),
  Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' m ->
  SInhabited (Original.LF_DOT_IndProp.LF.IndProp.ev' (from nat_iso m)).
Proof.
  intros m H.
  induction H.
  - (* ev'_0 *) exact (sinhabits Original.LF_DOT_IndProp.LF.IndProp.ev'_0).
  - (* ev'_2 *) exact (sinhabits Original.LF_DOT_IndProp.LF.IndProp.ev'_2).
  - (* ev'_sum *)
    apply sinhabits.
    apply sinhabitant in IHOriginal_LF__DOT__IndProp_LF_IndProp_ev'1.
    apply sinhabitant in IHOriginal_LF__DOT__IndProp_LF_IndProp_ev'2.
    pose proof (nat_from_add_iso n m) as Heq.
    pose proof (Original.LF_DOT_IndProp.LF.IndProp.ev'_sum _ _ 
             IHOriginal_LF__DOT__IndProp_LF_IndProp_ev'1
             IHOriginal_LF__DOT__IndProp_LF_IndProp_ev'2) as Hsum.
    exact (@Logic.eq_ind_r _ _ (fun x => Original.LF_DOT_IndProp.LF.IndProp.ev' x) Hsum _ Heq).
Qed.

(* Helper to use from_to of nat_iso *)
Lemma ev'_from_to_transport (x1 : nat) 
  (H : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' (to nat_iso x1)) :
  Original.LF_DOT_IndProp.LF.IndProp.ev' x1.
Proof.
  pose proof (sinhabitant (@ev'_from_imported_SInhabited (to nat_iso x1) H)) as H'.
  pose proof (from_to nat_iso x1) as Heq.
  destruct Heq. exact H'.
Qed.

(* Now the main isomorphism *)
#[local] Unset Universe Polymorphism.
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_ev'_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.ev' x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev' x2).
Proof.
  intros x1 x2 Hrel.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_ev'.
  destruct Hrel as [Heq].
  destruct Heq.
  apply Build_Iso with (to := ev'_to_imported (n := x1)) (from := ev'_from_to_transport x1).
  - intro x. exact IsomorphismDefinitions.eq_refl.
  - intro x. 
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ (ev'_from_to_transport x1 (ev'_to_imported x)) x) as Heq.
    destruct Heq. constructor.
Defined.
#[local] Set Universe Polymorphism.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev' Original_LF__DOT__IndProp_LF_IndProp_ev'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev' Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' Original_LF__DOT__IndProp_LF_IndProp_ev'_iso := {}.