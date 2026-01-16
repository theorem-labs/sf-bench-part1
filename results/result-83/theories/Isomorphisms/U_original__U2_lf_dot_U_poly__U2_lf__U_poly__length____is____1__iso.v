From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso Isomorphisms.nat__iso Isomorphisms.U_s__iso Isomorphisms.__0__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_length__is__1 : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Basics_LF_Basics_bool := (@Imported.Original_LF__DOT__Poly_LF_Poly_length__is__1).

Instance Original_LF__DOT__Poly_LF_Poly_length__is__1_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Poly.LF.Poly.length_is_1 x3) (imported_Original_LF__DOT__Poly_LF_Poly_length__is__1 x4).
Proof.
  intros x1 x2 hx l1 l2 Hl.
  unfold Original.LF_DOT_Poly.LF.Poly.length_is_1.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_length__is__1.
  unfold Imported.Original_LF__DOT__Poly_LF_Poly_length__is__1.
  apply Original_LF__DOT__Basics_LF_Basics_eqb_iso.
  - apply (@Original_LF__DOT__Poly_LF_Poly_length_iso x1 x2 hx). exact Hl.
  - apply S_iso. apply _0_iso.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.length_is_1) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_length__is__1) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.length_is_1) Original_LF__DOT__Poly_LF_Poly_length__is__1_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.length_is_1) (@Imported.Original_LF__DOT__Poly_LF_Poly_length__is__1) Original_LF__DOT__Poly_LF_Poly_length__is__1_iso := {}.