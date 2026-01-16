From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From Stdlib Require Import Logic.ProofIrrelevance.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_nat__add__iso.

Monomorphic Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' : imported_nat -> SProp := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'.

(* Helper: Nat_add commutes with conversion *)
Lemma Nat_add_conv : forall n m : nat,
  Logic.eq (nat_to_imported (n + m)) (Imported.Nat_add (nat_to_imported n) (nat_to_imported m)).
Proof.
  induction n as [| n' IH]; intro m; simpl.
  { reflexivity. }
  { change (Imported.Nat_add (Imported.nat_S (nat_to_imported n')) (nat_to_imported m))
      with (Imported.nat_S (Imported.Nat_add (nat_to_imported n') (nat_to_imported m))).
    apply Logic.f_equal. apply IH. }
Qed.

Lemma Nat_add_conv_inv : forall n m : imported_nat,
  Logic.eq (nat_from_imported n + nat_from_imported m) (nat_from_imported (Imported.Nat_add n m)).
Proof.
  fix IH 1.
  intros n m. destruct n as [| n']; simpl.
  { reflexivity. }
  { apply Logic.f_equal. apply IH. }
Qed.

(* Forward direction: Original ev' -> Imported ev' *)
Lemma ev'_forward : forall (n : nat),
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' n ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' (nat_to_imported n).
Proof.
  intros n Hev.
  induction Hev.
  - exact Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'_ev'_0.
  - exact Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'_ev'_2.
  - unfold imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' in *.
    rewrite Nat_add_conv.
    exact (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'_ev'_sum _ _ IHHev1 IHHev2).
Qed.

(* Backward direction: Imported ev' -> SInhabited (Original ev') *)
Lemma ev'_backward_sinhabited : forall (n : Imported.nat),
  Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' n ->
  SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' (nat_from_imported n)).
Proof.
  fix rec 2.
  intros n Hev.
  destruct Hev as [| | n0 m0 hn hm].
  { apply sinhabits. exact Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev'_0. }
  { apply sinhabits. exact Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev'_2. }
  { pose proof (sinhabitant (rec n0 hn)) as H1.
    pose proof (sinhabitant (rec m0 hm)) as H2.
    apply sinhabits.
    rewrite <- Nat_add_conv_inv.
    exact (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev'_sum _ _ H1 H2). }
Defined.

Lemma ev'_backward : forall (n : Imported.nat),
  Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' n ->
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' (nat_from_imported n).
Proof.
  intros n Hev.
  apply sinhabitant. apply ev'_backward_sinhabited. exact Hev.
Qed.

Lemma ev'_iso_to : forall (x1 : nat) (x2 : imported_nat),
  nat_to_imported x1 = x2 ->
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' x1 ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' x2.
Proof.
  intros x1 x2 Hx H.
  subst x2.
  exact (@ev'_forward x1 H).
Defined.

Lemma ev'_iso_from : forall (x1 : nat) (x2 : imported_nat),
  nat_to_imported x1 = x2 ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' x2 ->
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' x1.
Proof.
  intros x1 x2 Hx H.
  subst x2.
  rewrite <- (nat_from_to x1).
  apply ev'_backward. exact H.
Defined.

Monomorphic Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' x2).
Proof.
  intros x1 x2 Hx.
  destruct Hx as [Hx]. simpl in Hx.
  pose proof (eq_of_seq Hx) as Hx'.
  refine {|
    to := @ev'_iso_to x1 x2 Hx';
    from := @ev'_iso_from x1 x2 Hx';
    to_from := _;  (* forall x : SProp, to (from x) = x *)
    from_to := _   (* forall x : Prop, from (to x) = x *)
  |}.
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply seq_of_peq_t. apply proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ev' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev'_iso := {}.