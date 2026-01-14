From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_merge : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_merge).
Instance Original_LF__DOT__IndProp_LF_IndProp_merge_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.merge x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_merge x4 x6 x8).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56 x7 x8 h78.
  (* Both merge types are uninhabited (no constructors) *)
  (* Original.merge is in Prop, Imported.merge is in SProp *)
  unshelve eapply Build_Iso.
  { intro m; destruct m. }
  { intro m; destruct m. }
  { intro m; destruct m. }
  { intro m; destruct m. }
Defined.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.merge) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_merge) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.merge) Original_LF__DOT__IndProp_LF_IndProp_merge_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.merge) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_merge) Original_LF__DOT__IndProp_LF_IndProp_merge_iso := {}.