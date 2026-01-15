From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_fold : forall x x0 : Type, (x -> x0 -> x0) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> x0 -> x0 := (@Imported.Original_LF__DOT__Poly_LF_Poly_fold).

(* Helper: fold on canonical list produces the same result as imported fold *)
Fixpoint fold_canonical (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : IsoOrSortRelaxed x3 x4) 
    (f1 : x1 -> x3 -> x3) (f2 : x2 -> x4 -> x4)
    (Hf : forall (a : x1) (b : x2), rel_iso hx a b -> forall (c : x3) (d : x4), rel_iso_sort hx0 c d -> rel_iso_sort hx0 (f1 a c) (f2 b d))
    (l : Original.LF_DOT_Poly.LF.Poly.list x1) 
    (b1 : x3) (b2 : x4) (Hb : rel_iso_sort hx0 b1 b2)
    {struct l}
  : rel_iso_sort hx0 
      (Original.LF_DOT_Poly.LF.Poly.fold f1 l b1)
      (Imported.Original_LF__DOT__Poly_LF_Poly_fold x2 x4 f2 (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l) b2).
Proof.
  destruct l as [|h t].
  - (* nil case *)
    simpl. exact Hb.
  - (* cons case *)
    simpl.
    apply Hf.
    + apply Build_rel_iso. apply IsomorphismDefinitions.eq_refl.
    + apply fold_canonical; assumption.
Defined.

Monomorphic Instance Original_LF__DOT__Poly_LF_Poly_fold_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : IsoOrSortRelaxed x3 x4) (x5 : x1 -> x3 -> x3) (x6 : x2 -> x4 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (Original.LF_DOT_Poly.LF.Poly.fold x5 x7 x9) (imported_Original_LF__DOT__Poly_LF_Poly_fold x6 x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hf x7 x8 Hx78 x9 x10 Hx910.
  pose proof (proj_rel_iso Hx78) as Heq.
  pose proof (@fold_canonical x1 x2 hx x3 x4 hx0 x5 x6 Hf x7 x9 x10 Hx910) as H.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_fold.
  destruct Heq. exact H.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.fold) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.fold) (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.