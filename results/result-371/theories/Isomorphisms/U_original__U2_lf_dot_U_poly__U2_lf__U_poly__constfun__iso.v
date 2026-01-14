From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_constfun : forall x : Type, x -> imported_nat -> x := (@Imported.Original_LF__DOT__Poly_LF_Poly_constfun).
Instance Original_LF__DOT__Poly_LF_Poly_constfun_iso : forall (x1 x2 : Type) (hx : IsoOrSortRelaxed x1 x2) (x3 : x1) (x4 : x2),
  rel_iso_sort hx x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> rel_iso_sort hx (Original.LF_DOT_Poly.LF.Poly.constfun x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_constfun x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold Original.LF_DOT_Poly.LF.Poly.constfun.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_constfun.
  unfold Imported.Original_LF__DOT__Poly_LF_Poly_constfun.
  simpl.
  exact H34.
Qed.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.constfun) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_constfun) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.constfun) Original_LF__DOT__Poly_LF_Poly_constfun_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.constfun) (@Imported.Original_LF__DOT__Poly_LF_Poly_constfun) Original_LF__DOT__Poly_LF_Poly_constfun_iso := {}.