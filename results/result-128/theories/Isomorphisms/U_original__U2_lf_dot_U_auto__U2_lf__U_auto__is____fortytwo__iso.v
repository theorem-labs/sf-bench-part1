From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo : imported_nat -> SProp := Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo.

(* Helper: convert between Imported.RocqEq and standard eq *)
Lemma Imported_RocqEq_to_eq : forall (x y : Imported.nat), Imported.RocqEq Imported.nat x y -> x = y.
Proof.
  intros x y H.
  destruct H.
  reflexivity.
Qed.

(* Helper: to direction *)
Definition iso_to_helper (x1 : nat) : (x1 = 42%nat) -> Imported.RocqEq Imported.nat (nat_to_imported x1) Imported.nat_42 :=
  fun H => match H in (_ = n) return Imported.RocqEq Imported.nat (nat_to_imported x1) (nat_to_imported n) with
           | Logic.eq_refl => Imported.RocqEq_refl Imported.nat (nat_to_imported x1)
           end.

(* Helper: from direction *)
Definition iso_from_helper (x1 : nat) : Imported.RocqEq Imported.nat (nat_to_imported x1) Imported.nat_42 -> (x1 = 42%nat).
Proof.
  intro H.
  apply Imported_RocqEq_to_eq in H.
  transitivity (imported_to_nat (nat_to_imported x1)).
  - symmetry. apply nat_roundtrip.
  - apply (@Coq.Init.Logic.f_equal _ _ imported_to_nat) in H.
    exact H.
Defined.

(* Prove the isomorphism *)
Instance Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_Auto.LF.Auto.is_fortytwo x1) (imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo x2).
Proof.
  intros x1 x2 Hrel.
  pose proof (eq_of_seq Hrel) as Hstd.
  unfold Original.LF_DOT_Auto.LF.Auto.is_fortytwo.
  unfold imported_Original_LF__DOT__Auto_LF_Auto_is__fortytwo.
  unfold Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo.
  subst x2.
  change (nat_iso x1) with (nat_to_imported x1).
  apply (@Build_Iso (x1 = 42%nat) (Imported.RocqEq Imported.nat (nat_to_imported x1) Imported.nat_42) (@iso_to_helper x1) (@iso_from_helper x1)).
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro. apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Auto.LF.Auto.is_fortytwo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.is_fortytwo Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.is_fortytwo Imported.Original_LF__DOT__Auto_LF_Auto_is__fortytwo Original_LF__DOT__Auto_LF_Auto_is__fortytwo_iso := {}.