From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Local Open Scope nat_scope.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Local aliases for convenience *)
Definition nat_to_imported := to nat_iso.
Definition imported_to_nat := from nat_iso.

(* Helper to get Prop equality from SProp equality *)
Lemma nat_from_to_prop : forall x : nat, imported_to_nat (nat_to_imported x) = x.
Proof.
  intros x.
  apply eq_of_seq.
  apply from_to.
Defined.

(* IMPORTANT: Define this BEFORE le_to_imported to avoid type inference issues *)
(* Use explicit term to define conversion from Imported.le to SInhabited (Peano.le) *)
Definition imported_to_le_sinhabited (n m : Imported.nat) (H : Imported.le n m) : 
  SInhabited (Peano.le (imported_to_nat n) (imported_to_nat m)) :=
  Imported.le_sind n 
    (fun k _ => SInhabited (Peano.le (imported_to_nat n) (imported_to_nat k)))
    (sinhabits (Peano.le_n (imported_to_nat n)))
    (fun k _ IH => match IH with sinhabits pf => sinhabits (Peano.le_S _ _ pf) end)
    m H.

Definition imported_to_le (n m : Imported.nat) (H : Imported.le n m) : 
  Peano.le (imported_to_nat n) (imported_to_nat m) :=
  @sinhabitant _ (@imported_to_le_sinhabited n m H).

(* Convert Peano.le to Imported.le *)
Definition le_to_imported : forall (n m : nat), Peano.le n m -> 
  Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  intros n m H.
  induction H.
  - apply Imported.le_le_n.
  - apply Imported.le_le_S. exact IHle.
Defined.

(* The isomorphism *)
Instance le_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4), Iso (Peano.le x1 x3) (imported_le x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in H12, H34. simpl in H12, H34.
  unfold imported_le.
  
  apply IsoEq.eq_of_seq in H12.
  apply IsoEq.eq_of_seq in H34.
  subst x2 x4.
  
  unshelve refine {|
    to := @le_to_imported x1 x3;
    from := fun H => _ 
  |}.
  - pose (@imported_to_le (nat_to_imported x1) (nat_to_imported x3) H) as H'.
    rewrite nat_from_to_prop in H'.
    rewrite nat_from_to_prop in H'.
    exact H'.
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant le := {}. 
Instance: KnownConstant Imported.le := {}. 
Instance: IsoStatementProofFor le le_iso := {}.
Instance: IsoStatementProofBetween le Imported.le le_iso := {}.
