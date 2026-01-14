From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

(* Use qualified nat to avoid shadowing from Imported *)
Local Notation Nat := Corelib.Init.Datatypes.nat.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Helper lemmas *)
Lemma le_0_l : forall n : Nat, Peano.le O n.
Proof. induction n; constructor; auto. Qed.

(* le_to_imported: convert Rocq le to Imported.le *)
(* We prove this by showing le n m implies nat_le (nat_to_imported n) (nat_to_imported m) = true *)

(* Helper: nat_le O m = true for all m *)
Lemma nat_le_O (m : Imported.nat) : 
  Imported.nat_le Imported.nat_O m = Imported.Bool_true.
Proof. destruct m; reflexivity. Qed.

(* Helper for discrimination *)
Definition bool_discr (H : Imported.Bool_false = Imported.Bool_true) : False :=
  match H in (Corelib.Init.Logic.eq _ b) return (match b with Imported.Bool_true => False | Imported.Bool_false => True end) with
  | Corelib.Init.Logic.eq_refl => I
  end.

(* Helper: if nat_le n m = true then nat_le n (S m) = true *)
Fixpoint nat_le_step (n : Imported.nat) : forall (m : Imported.nat),
  Imported.nat_le n m = Imported.Bool_true -> 
  Imported.nat_le n (Imported.nat_S m) = Imported.Bool_true :=
  match n return forall m, Imported.nat_le n m = Imported.Bool_true -> 
                           Imported.nat_le n (Imported.nat_S m) = Imported.Bool_true with
  | Imported.nat_O => fun m _ => nat_le_O (Imported.nat_S m)
  | Imported.nat_S n' => fun m =>
      match m return Imported.nat_le (Imported.nat_S n') m = Imported.Bool_true ->
                      Imported.nat_le (Imported.nat_S n') (Imported.nat_S m) = Imported.Bool_true with
      | Imported.nat_O => fun H => False_rect _ (bool_discr H)
      | Imported.nat_S m' => fun H => nat_le_step n' m' H
      end
  end.

Definition le_implies_nat_le : forall (n m : Nat) (H : Peano.le n m),
  Imported.nat_le (nat_to_imported n) (nat_to_imported m) = Imported.Bool_true.
Proof.
  fix IH 3.
  intros n m H.
  destruct H as [|m' H'].
  - induction n; simpl; [reflexivity | exact IHn].
  - apply nat_le_step. exact (IH n m' H').
Defined.

Definition le_to_imported (n m : Nat) (H : Peano.le n m) : 
  Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  unfold Imported.le.
  rewrite le_implies_nat_le; [apply Imported.Eq_refl | exact H].
Defined.

(* imported_to_le: convert Imported.le to Rocq le *)
(* Key insight: match on (nat_le n m). In the Bool_false case, H is uninhabited. *)

Fixpoint nat_le_implies_le (n m : Imported.nat) {struct n} :
  Imported.nat_le n m = Imported.Bool_true -> Peano.le (imported_to_nat n) (imported_to_nat m).
Proof.
  destruct n, m; intro E; simpl in *.
  - exact (le_n 0).
  - apply le_0_l.
  - discriminate E.
  - apply le_n_S. apply nat_le_implies_le. exact E.
Defined.

Definition imported_to_le (n' m' : Imported.nat) (H : Imported.le n' m') : 
  Peano.le (imported_to_nat n') (imported_to_nat m').
Proof.
  unfold Imported.le in H.
  (* H : Eq Bool (nat_le n' m') Bool_true *)
  (* Match on the boolean (nat_le n' m') *)
  destruct (Imported.nat_le n' m') eqn:E.
  - (* nat_le n' m' = Bool_false - this is the first constructor! *)
    (* H : Eq Bool Bool_false Bool_true, which is empty! *)
    exact (False_rect _ (match H with end)).
  - (* nat_le n' m' = Bool_true *)
    apply nat_le_implies_le. exact E.
Defined.

(* Helper to get Prop equality from SProp equality *)
Lemma nat_from_to_prop : forall x : Nat, imported_to_nat (nat_to_imported x) = x.
Proof.
  fix IH 1.
  intros x. destruct x.
  - reflexivity.
  - simpl. f_equal. apply IH.
Defined.

(* The isomorphism *)
Instance le_iso : (forall (x1 : Nat) (x2 : imported_nat) (_ : @rel_iso Nat imported_nat nat_iso x1 x2) (x3 : Nat) (x4 : imported_nat) (_ : @rel_iso Nat imported_nat nat_iso x3 x4), Iso (Peano.le x1 x3) (imported_le x2 x4)).
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

Instance: KnownConstant Peano.le := {}. 
Instance: KnownConstant Imported.le := {}. 
Instance: IsoStatementProofFor Peano.le le_iso := {}.
Instance: IsoStatementProofBetween Peano.le Imported.le le_iso := {}.