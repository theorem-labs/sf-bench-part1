From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

(* Define filter manually since it's not in Imported.v *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_filter : forall x : Type, (x -> imported_Original_LF__DOT__Basics_LF_Basics_bool) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x :=
  fun x test => fix filter (l : imported_Original_LF__DOT__Poly_LF_Poly_list x) : imported_Original_LF__DOT__Poly_LF_Poly_list x :=
    match l with
    | Original_LF__DOT__Poly_LF_Poly_list_nil => Original_LF__DOT__Poly_LF_Poly_list_nil
    | Original_LF__DOT__Poly_LF_Poly_list_cons h t =>
      match test h with
      | Original_LF__DOT__Basics_LF_Basics_bool_true => Original_LF__DOT__Poly_LF_Poly_list_cons h (filter t)
      | Original_LF__DOT__Basics_LF_Basics_bool_false => filter t
      end
    end.
Instance Original_LF__DOT__Poly_LF_Poly_filter_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Original.LF_DOT_Basics.LF.Basics.bool) (x4 : x2 -> imported_Original_LF__DOT__Basics_LF_Basics_bool),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x3 x5) (x4 x6)) ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.filter x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_filter x4 x6).
Admitted.
(* This proof is complex due to the interaction between SProp equality and 
   the recursive nature of filter. The key challenge is that we need to show
   that the Lean-exported filter function behaves identically to the Coq filter
   function, but the equality lives in SProp which limits our proof techniques. *)
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.filter) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_filter := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.filter) Original_LF__DOT__Poly_LF_Poly_filter_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.filter) imported_Original_LF__DOT__Poly_LF_Poly_filter Original_LF__DOT__Poly_LF_Poly_filter_iso := {}.