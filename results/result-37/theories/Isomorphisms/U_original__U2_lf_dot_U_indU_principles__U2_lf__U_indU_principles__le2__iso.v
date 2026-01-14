From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2.

(* Convert Original.le2 (Prop) to Imported.le2 (SProp) *)
Definition le2_to_imported : forall (n m : nat), 
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 n m -> 
  Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso n) (nat_iso m).
Proof.
  intros n m H.
  induction H as [| m' IH IHrec].
  - apply Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_le2_n.
  - apply Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_le2_S.
    exact IHrec.
Defined.

Arguments le2_to_imported : clear implicits.

(* Lemma: from nat_iso (nat_iso n) = n *)
Lemma from_to_nat : forall n : nat, @Logic.eq nat (from nat_iso (nat_iso n)) n.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply (@Logic.f_equal nat nat S). exact IHn.
Defined.

(* Convert Imported.le2 (SProp) to Original.le2 (Prop) - need to eliminate to SProp first *)
(* Helper to convert through SInhabited *)  
Definition le2_from_imported_sprop : forall (n m : Imported.nat),
  Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n m ->
  SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 (from nat_iso n) (from nat_iso m)).
Proof.
  intros n m H.
  induction H as [| m' IH IHrec].
  - apply sinhabits. apply Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2_n.
  - destruct IHrec as [pf].
    apply sinhabits. apply Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2_S.
    exact pf.
Defined.

Arguments le2_from_imported_sprop : clear implicits.

(* We need a version that works with nat arguments directly *)
Definition le2_from_imported_nat (x1 x3 : nat) :
  Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso x1) (nat_iso x3) ->
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3.
Proof.
  intro H.
  apply sinhabitant.
  pose (le2_from_imported_sprop (nat_iso x1) (nat_iso x3) H) as pf.
  (* Need to transport pf using from_to_nat *)
  rewrite from_to_nat in pf.
  rewrite from_to_nat in pf.
  exact pf.
Defined.

Arguments le2_from_imported_nat : clear implicits.

(* A version of le2_from_imported_sprop that returns the correct type directly *)
(* We use the from_to_nat lemma to transport *)
Definition le2_from_imported_sprop_nat (x1 x3 : nat) 
  (H : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso x1) (nat_iso x3)) :
  SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3).
Proof.
  pose (le2_from_imported_sprop (nat_iso x1) (nat_iso x3) H) as pf.
  (* pf : SInhabited (le2 (from nat_iso (nat_iso x1)) (from nat_iso (nat_iso x3))) *)
  (* We need: SInhabited (le2 x1 x3) *)
  rewrite from_to_nat in pf.
  rewrite from_to_nat in pf.
  exact pf.
Defined.

(* Step 1: Iso from le2 (Prop) to SInhabited (le2) (SProp) using iso_SInhabited *)
Definition le2_to_sinhabited (x1 x3 : nat) : 
  Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3)
      (SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3)) :=
  iso_SInhabited.

(* Step 2: Iso from SInhabited (le2) (SProp) to Imported.le2 (SProp) *)
(* Both are SProp so eq_refl works for the round-trip proofs *)
Definition sinhabited_to_imported (x1 x3 : nat) :
  Iso (SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3))
      (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso x1) (nat_iso x3)).
Proof.
  apply Build_Iso with 
    (to := fun H => match H with sinhabits pf => le2_to_imported x1 x3 pf end)
    (from := le2_from_imported_sprop_nat x1 x3).
  - intro y. apply IsomorphismDefinitions.eq_refl.
  - intro y. apply IsomorphismDefinitions.eq_refl.
Defined.

(* Step 3: Compose the isomorphisms *)
Definition le2_iso_base (x1 x3 : nat) : 
  Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3)
      (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso x1) (nat_iso x3)) :=
  iso_trans (le2_to_sinhabited x1 x3) (sinhabited_to_imported x1 x3).

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 x2 x4).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unfold imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2.
  unfold rel_iso in Hx1, Hx3. simpl in Hx1, Hx3.
  destruct Hx1, Hx3.
  apply relax_Iso_Ps_Ts.
  exact (le2_iso_base x1 x3).
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_iso := {}.