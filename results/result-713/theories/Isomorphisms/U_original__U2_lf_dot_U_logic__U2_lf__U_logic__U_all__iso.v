From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_All : forall x : Type, (x -> SProp) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__Logic_LF_Logic_All).
Instance Original_LF__DOT__Logic_LF_Logic_All_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : forall _ : x1, Prop) (x4 : forall _ : x2, SProp) (_ : forall (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6), Iso (x3 x5) (x4 x6))
     (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
     (_ : @rel_iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) x5 x6),
   Iso (@Original.LF_DOT_Logic.LF.Logic.All x1 x3 x5) (@imported_Original_LF__DOT__Logic_LF_Logic_All x2 x4 x6)).
Admitted.
Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.All) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_All) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.All) Original_LF__DOT__Logic_LF_Logic_All_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.All) (@Imported.Original_LF__DOT__Logic_LF_Logic_All) Original_LF__DOT__Logic_LF_Logic_All_iso := {}.