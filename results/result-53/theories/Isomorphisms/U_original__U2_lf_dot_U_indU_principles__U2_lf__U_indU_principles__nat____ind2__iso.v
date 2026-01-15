From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso.

(* Use O instead of 0 to avoid Lean.Nat numeral ambiguity *)
Local Notation "'Zero'" := (O : Datatypes.nat).
Local Notation "'One'" := (Datatypes.S O : Datatypes.nat).

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2 : forall x : imported_nat -> SProp, x imported_0 -> x (imported_S imported_0) -> (forall x0 : imported_nat, x x0 -> x (imported_S (imported_S x0))) -> forall x3 : imported_nat, x x3 := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2.
Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2_iso : forall (x1 : Datatypes.nat -> Prop) (x2 : imported_nat -> SProp) (hx : forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 x3) (x2 x4)) (x3 : x1 Zero) (x4 : x2 imported_0),
  rel_iso (hx Zero imported_0 _0_iso) x3 x4 ->
  forall (x5 : x1 One) (x6 : x2 (imported_S imported_0)),
  rel_iso (hx One (imported_S imported_0) (S_iso _0_iso)) x5 x6 ->
  forall (x7 : forall n : Datatypes.nat, x1 n -> x1 (Datatypes.S (Datatypes.S n))) (x8 : forall x : imported_nat, x2 x -> x2 (imported_S (imported_S x))),
  (forall (x9 : Datatypes.nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) (x11 : x1 x9) (x12 : x2 x10),
   rel_iso (hx x9 x10 hx2) x11 x12 -> rel_iso (hx (Datatypes.S (Datatypes.S x9)) (imported_S (imported_S x10)) (S_iso (S_iso hx2))) (x7 x9 x11) (x8 x10 x12)) ->
  forall (x9 : Datatypes.nat) (x10 : imported_nat) (hx3 : rel_iso nat_iso x9 x10),
  rel_iso (hx x9 x10 hx3) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nat_ind2 x1 x3 x5 x7 x9) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2 x2 x4 x6 x8 x10).
Proof.
  intros x1 x2 hx x3 x4 H0 x5 x6 H1 x7 x8 HSS.
  (* Use fix for structural recursion on x9 *)
  fix IH 1.
  intros x9 x10 hx3.
  destruct x9 as [|x9'].
  - (* Case x9 = 0 *)
    simpl Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nat_ind2.
    destruct hx3 as [hx3].
    destruct hx3.
    simpl nat_iso.
    constructor.
    (* Both sides are in SProp (x2 Imported._0 : SProp), so any two elements are equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* Case x9 = S x9' *)
    simpl Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nat_ind2.
    destruct hx3 as [hx3].
    destruct hx3.
    simpl nat_iso.
    constructor.
    (* Both sides are in SProp, so any two elements are equal *)
    apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nat_ind2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nat_ind2 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nat_ind2 Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind2_iso := {}.
