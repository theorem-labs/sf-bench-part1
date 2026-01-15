From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_prod : Type -> Type -> Type := Imported.Original_LF__DOT__Poly_LF_Poly_prod.
Monomorphic Instance Original_LF__DOT__Poly_LF_Poly_prod_iso : forall x1 x2 : Type, Iso x1 x2 -> forall x3 x4 : Type, Iso x3 x4 -> Iso (Original.LF_DOT_Poly.LF.Poly.prod x1 x3) (imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4).
Proof.
  intros x1 x2 iso12 x3 x4 iso34.
  unshelve eapply Build_Iso.
  - (* to *) intro p. destruct p as [a b].
    exact (Imported.Original_LF__DOT__Poly_LF_Poly_prod_pair x2 x4 (to iso12 a) (to iso34 b)).
  - (* from *) intro p.
    exact (Original.LF_DOT_Poly.LF.Poly.pair (from iso12 (Imported.a____at___Solution__hyg4412 _ _ p)) (from iso34 (Imported.a____at___Solution__hyg4414 _ _ p))).
  - (* to_from *) intro p. simpl.
    apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_prod_pair x2 x4) (to_from iso12 _) (to_from iso34 _)).
  - (* from_to *) intro p. destruct p as [a b]. simpl.
    apply (IsoEq.f_equal2 Original.LF_DOT_Poly.LF.Poly.pair (from_to iso12 a) (from_to iso34 b)).
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.prod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_prod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.prod Original_LF__DOT__Poly_LF_Poly_prod_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.prod Imported.Original_LF__DOT__Poly_LF_Poly_prod Original_LF__DOT__Poly_LF_Poly_prod_iso := {}.