From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Poly_LF_Poly_prod : Type -> Type -> Type := Imported.Original_LF__DOT__Poly_LF_Poly_prod.

(* Define the isomorphism between the original prod and imported prod *)
Definition prod_to {X1 X2 Y1 Y2 : Type} (hx : Iso X1 X2) (hy : Iso Y1 Y2)
  (p : Original.LF_DOT_Poly.LF.Poly.prod X1 Y1) : imported_Original_LF__DOT__Poly_LF_Poly_prod X2 Y2 :=
  match p with
  | Original.LF_DOT_Poly.LF.Poly.pair x y => Imported.Original_LF__DOT__Poly_LF_Poly_pair X2 Y2 (hx.(to) x) (hy.(to) y)
  end.

Definition prod_from {X1 X2 Y1 Y2 : Type} (hx : Iso X1 X2) (hy : Iso Y1 Y2)
  (p : imported_Original_LF__DOT__Poly_LF_Poly_prod X2 Y2) : Original.LF_DOT_Poly.LF.Poly.prod X1 Y1 :=
  match p with
  | Imported.Original_LF__DOT__Poly_LF_Poly_prod_pair _ _ x y => Original.LF_DOT_Poly.LF.Poly.pair (hx.(from) x) (hy.(from) y)
  end.

Instance Original_LF__DOT__Poly_LF_Poly_prod_iso : forall x1 x2 : Type, Iso x1 x2 -> forall x3 x4 : Type, Iso x3 x4 -> Iso (Original.LF_DOT_Poly.LF.Poly.prod x1 x3) (imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4).
Proof.
  intros X1 X2 hx Y1 Y2 hy.
  refine {| to := prod_to hx hy; from := prod_from hx hy |}.
  - (* to_from *)
    intros p. unfold prod_to, prod_from. simpl.
    apply (f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_pair X2 Y2)); apply to_from.
  - (* from_to *)
    intros p. unfold prod_to, prod_from.
    destruct p as [x y]. simpl.
    apply (f_equal2 Original.LF_DOT_Poly.LF.Poly.pair); apply from_to.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.prod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_prod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.prod Original_LF__DOT__Poly_LF_Poly_prod_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.prod Imported.Original_LF__DOT__Poly_LF_Poly_prod Original_LF__DOT__Poly_LF_Poly_prod_iso := {}.