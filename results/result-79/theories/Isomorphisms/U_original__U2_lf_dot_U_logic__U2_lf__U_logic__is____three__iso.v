From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From Stdlib.Logic Require Import ProofIrrelevance.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_is__three : imported_nat -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_is__three.

(* Forward direction: Original.is_three x1 -> imported_is_three x2 *)
Definition is_three_to (x1 : nat) (x2 : imported_nat) (rel : rel_iso nat_iso x1 x2) 
  (h : Original.LF_DOT_Logic.LF.Logic.is_three x1) : imported_Original_LF__DOT__Logic_LF_Logic_is__three x2.
Proof.
  unfold Original.LF_DOT_Logic.LF.Logic.is_three in h.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_is__three.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_is__three.
  destruct rel.
  simpl.
  subst x1.
  change (Imported.Eq Imported.nat Imported.three Imported.three).
  exact (Imported.Eq_refl Imported.nat Imported.three).
Defined.

(* Backward direction: imported_is_three x2 -> Original.is_three x1 *)
Definition is_three_from (x1 : nat) (x2 : imported_nat) (rel : rel_iso nat_iso x1 x2) 
  (h : imported_Original_LF__DOT__Logic_LF_Logic_is__three x2) : Original.LF_DOT_Logic.LF.Logic.is_three x1.
Proof.
  unfold Original.LF_DOT_Logic.LF.Logic.is_three.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_is__three in h.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_is__three in h.
  destruct rel.
  simpl in h.
  (* h : Imported.Eq Imported.nat (nat_to_imported x1) Imported.three *)
  (* Use Eq_recl to extract the equality in Prop *)
  pose proof (Imported.Eq_recl Imported.nat (nat_to_imported x1) 
           (fun y _ => Logic.eq (imported_to_nat (nat_to_imported x1)) (imported_to_nat y))
           Logic.eq_refl Imported.three h) as Heq.
  simpl in Heq.
  rewrite nat_round_trip in Heq.
  exact Heq.
Defined.

(* Build the full isomorphism *)
Instance Original_LF__DOT__Logic_LF_Logic_is__three_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_Logic.LF.Logic.is_three x1) (imported_Original_LF__DOT__Logic_LF_Logic_is__three x2).
Proof.
  intros x1 x2 rel.
  apply Build_Iso with (to := is_three_to rel) (from := is_three_from rel).
  (* to_from: for all h in imported_is_three, eq (to (from h)) h *)
  intro h.
  destruct rel.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
  (* from_to: for all h in Original.is_three, eq (from (to h)) h *)
  intro h.
  destruct rel.
  simpl.
  apply seq_of_eq.
  apply proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.is_three := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_is__three := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.is_three Original_LF__DOT__Logic_LF_Logic_is__three_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.is_three Imported.Original_LF__DOT__Logic_LF_Logic_is__three Original_LF__DOT__Logic_LF_Logic_is__three_iso := {}.