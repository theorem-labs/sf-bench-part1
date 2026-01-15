From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.le__iso.

Monomorphic Definition imported_gt : imported_nat -> imported_nat -> SProp := Imported.gt.

(* gt m n := le (S n) m in Rocq 
   Imported.gt m n := Imported.le (nat_S n) m *)
(* So we need to use le_iso with (S n, nat_S x4) and (m, x2) *)

Monomorphic Instance gt_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 > x3) (imported_gt x2 x4).
Proof.
  intros x1 x2 Hx1x2 x3 x4 Hx3x4.
  unfold Peano.gt.
  unfold imported_gt.
  unfold Imported.gt.
  simpl in *.
  (* Use le_iso with arguments swapped: (S x3, nat_S x4) and (x1, x2) *)
  destruct Hx1x2 as [Hx1x2]. destruct Hx3x4 as [Hx3x4].
  apply le_iso.
  - constructor. simpl. exact (f_equal Imported.nat_S Hx3x4).
  - constructor. exact Hx1x2.
Defined.

Instance: KnownConstant gt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.gt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor gt gt_iso := {}.
Instance: IsoStatementProofBetween gt Imported.gt gt_iso := {}.
