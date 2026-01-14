From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_gt : imported_nat -> imported_nat -> SProp := Imported.gt.

(* Helper: SProp True *)
Variant STrue : SProp := sI : STrue.

(* Helper: Imported.le (nat_S n) nat_O is absurd *)
Lemma imported_le_S_O_absurd : forall n' : imported_nat,
  Imported.le (Imported.nat_S n') Imported.nat_O -> False.
Proof.
  intros n' H.
  pose (P := fun (m : imported_nat) (_ : Imported.le (Imported.nat_S n') m) =>
               match m with
               | Imported.nat_O => SInhabited False
               | Imported.nat_S _ => STrue
               end : SProp).
  assert (Habs : P Imported.nat_O H).
  { apply (Imported.le_sind (Imported.nat_S n') P); [exact sI | intros m H' IH; exact sI]. }
  exact (sinhabitant Habs).
Qed.

(* Helper: Inversion for Imported.le *)
Lemma imported_le_S_S_inv : forall n m : imported_nat,
  Imported.le (Imported.nat_S n) (Imported.nat_S m) -> Imported.le n m.
Proof.
  intros n m H.
  pose (P := fun (m' : imported_nat) (_ : Imported.le (Imported.nat_S n) m') =>
               match m' with
               | Imported.nat_O => SInhabited False
               | Imported.nat_S m'' => Imported.le n m''
               end).
  assert (HP : P (Imported.nat_S m) H).
  { apply (Imported.le_sind (Imported.nat_S n) P).
    { apply Imported.le_le_n. }
    { intros m' H' IH.
      destruct m' as [|m''].
      { exfalso. exact (sinhabitant IH). }
      { simpl. apply Imported.le_le_S. exact IH. } } }
  exact HP.
Qed.

(* Forward: Peano.le -> Imported.le *)
Lemma le_forward : forall n m : nat,
  Peano.le n m -> Imported.le (nat_iso n) (nat_iso m).
Proof.
  intros n m H.
  induction H; [apply Imported.le_le_n | apply Imported.le_le_S; exact IHle].
Qed.

(* Backward: Imported.le -> Peano.le *)
Lemma le_back : forall n m : nat,
  Imported.le (nat_iso n) (nat_iso m) -> Peano.le n m.
Proof.
  induction n as [|n' IHn].
  { intros m _. apply Peano.le_0_n. }
  induction m as [|m' IHm].
  { intro H. exfalso. simpl in H. exact (imported_le_S_O_absurd H). }
  { intro H.
    apply le_n_S.
    apply IHn.
    simpl in H.
    exact (imported_le_S_S_inv H). }
Qed.

(* Now build the Iso for le *)
Lemma le_iso : forall (n1 : nat) (n2 : imported_nat), rel_iso nat_iso n1 n2 ->
               forall (m1 : nat) (m2 : imported_nat), rel_iso nat_iso m1 m2 ->
               Iso (Peano.le n1 m1) (Imported.le n2 m2).
Proof.
  intros n1 n2 Hn m1 m2 Hm.
  unfold rel_iso in *.
  destruct Hn. destruct Hm.
  (* Goal: Iso (n1 <= m1)%nat (Imported.le (nat_iso n1) (nat_iso m1)) *)
  refine (Build_Iso (@le_forward n1 m1) (@le_back n1 m1) _ _).
  - (* to_from *) intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *) intro x. 
    (* Both sides are proofs of (n1 <= m1) : Prop, need SProp eq *)
    (* Use proof irrelevance: any two proofs of Prop are equal *)
    exact (IsoEq.seq_of_peq_t (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ _ _)).
Defined.

(* Now prove lt_iso *)
Lemma lt_iso : forall (n1 : nat) (n2 : imported_nat), rel_iso nat_iso n1 n2 ->
               forall (m1 : nat) (m2 : imported_nat), rel_iso nat_iso m1 m2 ->
               Iso (Peano.lt n1 m1) (Imported.lt n2 m2).
Proof.
  intros n1 n2 Hn m1 m2 Hm.
  unfold Peano.lt, Imported.lt.
  unfold rel_iso in *.
  destruct Hn. destruct Hm.
  (* Now n2 = nat_iso n1 and m2 = nat_iso m1 *)
  (* Goal: Iso (S n1 <= m1) (Imported.le (nat_S (nat_iso n1)) (nat_iso m1)) *)
  (* Which is: Iso (S n1 <= m1) (Imported.le (nat_iso (S n1)) (nat_iso m1)) *)
  apply le_iso; constructor; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance gt_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Peano.gt x1 x3) (imported_gt x2 x4).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unfold Peano.gt, imported_gt, Imported.gt.
  apply lt_iso; assumption.
Defined.
Instance: KnownConstant gt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.gt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor gt gt_iso := {}.
Instance: IsoStatementProofBetween gt Imported.gt gt_iso := {}.