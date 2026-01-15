From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.le__iso.

Definition imported_lt : imported_nat -> imported_nat -> SProp := Imported.lt.

(* lt n m is defined as le (S n) m in Rocq *)
(* Imported.lt is defined as Imported.le (Imported.nat_S n) m *)

Instance lt_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4), Iso (lt x1 x3) (imported_lt x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  destruct H12 as [H12]. destruct H34 as [H34].
  simpl in H12, H34.
  unfold imported_lt.
  
  apply IsoEq.eq_of_seq in H12.
  apply IsoEq.eq_of_seq in H34.
  subst x2 x4.
  
  (* lt x1 x3 = le (S x1) x3 *)
  (* Imported.lt (nat_to_imported x1) (nat_to_imported x3) 
       = Imported.le (Imported.nat_S (nat_to_imported x1)) (nat_to_imported x3) *)
  
  unfold lt, Imported.lt.
  
  (* Now we need: Iso (le (S x1) x3) (Imported.le (Imported.nat_S (nat_to_imported x1)) (nat_to_imported x3)) *)
  (* Which is the same as Iso (le (S x1) x3) (Imported.le (nat_to_imported (S x1)) (nat_to_imported x3)) *)
  
  (* The rel_iso for le_iso with (S x1) needs a proof that nat_to_imported (S x1) = Imported.nat_S (nat_to_imported x1) *)
  (* But by definition this is just eq_refl via simpl *)
  
  pose proof (@le_iso (S x1) (nat_to_imported (S x1)) IsomorphismDefinitions.eq_refl x3 (nat_to_imported x3) IsomorphismDefinitions.eq_refl) as Hle.
  simpl in Hle.
  exact Hle.
Defined.

Instance: KnownConstant lt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.lt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor lt lt_iso := {}.
Instance: IsoStatementProofBetween lt Imported.lt lt_iso := {}.