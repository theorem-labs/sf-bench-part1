From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Monomorphic Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof : forall x : imported_nat -> SProp, x imported_0 -> (forall x0 : imported_nat, x x0 -> x (imported_S x0)) -> forall x2 : imported_nat, x x2 := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof.

(* Helper lemma for simplified case where x8 = nat_iso x7 *)
Lemma build_proof_iso_simple : forall (x1 : Datatypes.nat -> Prop) (x2 : imported_nat -> SProp)
  (hx : forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 x3) (x2 x4))
  (x3 : x1 O) (x4 : x2 imported_0),
  rel_iso (hx O imported_0 _0_iso) x3 x4 ->
  forall (x5 : forall n : Datatypes.nat, x1 n -> x1 (Datatypes.S n))
    (x6 : forall x : imported_nat, x2 x -> x2 (imported_S x)),
  (forall (x7 : Datatypes.nat) (x8 : imported_nat) (hx1 : rel_iso nat_iso x7 x8) (x9 : x1 x7) (x10 : x2 x8),
   rel_iso (hx x7 x8 hx1) x9 x10 -> rel_iso (hx (Datatypes.S x7) (imported_S x8) (S_iso hx1)) (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Datatypes.nat),
  rel_iso (hx x7 (nat_iso x7) (Build_rel_iso IsomorphismDefinitions.eq_refl))
    (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof x2 x4 x6 (nat_iso x7)).
Proof.
  intros x1 x2 hx x3 x4 Hbase x5 x6 Hstep.
  induction x7 as [|n IHn].
  - simpl. exact Hbase.
  - simpl.
    change (nat_iso (S n)) with (imported_S (nat_iso n)).
    specialize (Hstep n (nat_iso n) (Build_rel_iso IsomorphismDefinitions.eq_refl)).
    specialize (Hstep _ _ IHn).
    exact Hstep.
Defined.

Monomorphic Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof_iso : forall (x1 : Datatypes.nat -> Prop) (x2 : imported_nat -> SProp) (hx : forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 x3) (x2 x4)) (x3 : x1 O) (x4 : x2 imported_0),
  rel_iso (hx O imported_0 _0_iso) x3 x4 ->
  forall (x5 : forall n : Datatypes.nat, x1 n -> x1 (Datatypes.S n)) (x6 : forall x : imported_nat, x2 x -> x2 (imported_S x)),
  (forall (x7 : Datatypes.nat) (x8 : imported_nat) (hx1 : rel_iso nat_iso x7 x8) (x9 : x1 x7) (x10 : x2 x8),
   rel_iso (hx x7 x8 hx1) x9 x10 -> rel_iso (hx (Datatypes.S x7) (imported_S x8) (S_iso hx1)) (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Datatypes.nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8),
  rel_iso (hx x7 x8 hx2) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof x1 x3 x5 x7) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof x2 x4 x6 x8).
Proof.
  intros x1 x2 hx x3 x4 Hbase x5 x6 Hstep.
  intros x7 x8 hx2.
  destruct hx2 as [e].
  destruct e.
  apply build_proof_iso_simple; auto.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof_iso := {}.