From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_false__iso.

Definition imported_ex : forall x : Type, (x -> SProp) -> SProp := Imported.ex.

(* Helper to convert from exists to Imported.ex *)
Definition ex_to {A B : Type} (hAB : Iso A B) (P : A -> Prop) (Q : B -> SProp)
  (hPQ : forall (a : A) (b : B), rel_iso hAB a b -> Iso (P a) (Q b))
  (e : exists y : A, P y) : imported_ex Q :=
  match e with
  | ex_intro _ a pa => Imported.ex_intro B Q (to hAB a) (to (hPQ a (to hAB a) (rel_iso_refl hAB a)) pa)
  end.

(* Helper to convert from Imported.ex to exists *)
Definition ex_from {A B : Type} (hAB : Iso A B) (P : A -> Prop) (Q : B -> SProp)
  (hPQ : forall (a : A) (b : B), rel_iso hAB a b -> Iso (P a) (Q b))
  (e : imported_ex Q) : exists y : A, P y :=
  sinhabitant (match e with
    | Imported.ex_intro _ _ b qb => 
        sinhabits (ex_intro _ (from hAB b) 
          (from (hPQ (from hAB b) b (rel_iso_unsym (rel_iso_refl (iso_sym hAB) b))) qb))
  end).

(* Round-trip proofs *)
Lemma from_to_helper : forall (A B : Type) (hAB : Iso A B) (P : A -> Prop) (Q : B -> SProp)
  (hPQ : forall (a : A) (b : B), rel_iso hAB a b -> Iso (P a) (Q b))
  (e : exists y : A, P y),
  IsomorphismDefinitions.eq (@ex_from A B hAB P Q hPQ (@ex_to A B hAB P Q hPQ e)) e.
Proof.
  intros.
  apply seq_of_eq.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

Lemma to_from_helper : forall (A B : Type) (hAB : Iso A B) (P : A -> Prop) (Q : B -> SProp)
  (hPQ : forall (a : A) (b : B), rel_iso hAB a b -> Iso (P a) (Q b))
  (e : imported_ex Q),
  IsomorphismDefinitions.eq (@ex_to A B hAB P Q hPQ (@ex_from A B hAB P Q hPQ e)) e.
Proof.
  intros.
  (* imported_ex Q is in SProp, so all values are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance ex_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp), 
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) -> 
  Iso (exists y, x3 y) (imported_ex x4).
Proof.
  intros A B hAB P Q hPQ.
  exact (@Build_Iso (exists y : A, P y) (imported_ex Q) 
    (@ex_to A B hAB P Q hPQ)
    (@ex_from A B hAB P Q hPQ)
    (@to_from_helper A B hAB P Q hPQ)
    (@from_to_helper A B hAB P Q hPQ)).
Defined.

Instance: KnownConstant ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor ex ex_iso := {}.
Instance: IsoStatementProofBetween ex Imported.ex ex_iso := {}.
