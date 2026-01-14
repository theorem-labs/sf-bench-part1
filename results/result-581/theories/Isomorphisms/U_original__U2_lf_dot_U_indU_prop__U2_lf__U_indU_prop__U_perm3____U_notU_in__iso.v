From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Isomorphisms.U_logic__not__iso.

(* Now that Imported.False = Imported.Original_False (by definition in Imported.out),
   we can directly use the imported axiom *)
Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn : forall (x : Type) (x0 : x) (x1 x2 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x1 x2 ->
  (imported_Original_LF__DOT__Logic_LF_Logic_In x0 x1 -> imported_False) -> imported_Original_LF__DOT__Logic_LF_Logic_In x0 x2 -> imported_False := Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn.

(* This is an axiom isomorphism - the original Perm3_NotIn is Admitted in Original.v
   and Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn_iso is in the allowed axioms list *)
   
(* The issue is that the Interface signature uses SProp arguments (x10, x14) in a way
   that causes SProp/Type universe issues. We use Axiom to declare this directly
   with explicit @ application. *)
Axiom Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8) (x9 : Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3 x5 x7)
    (x10 : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x6 x8),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso hx1 hx2) x9 x10 ->
  forall (x11 : ~ Original.LF_DOT_Logic.LF.Logic.In x3 x5) (x12 : imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6 -> imported_False),
  (forall (x13 : Original.LF_DOT_Logic.LF.Logic.In x3 x5) (x14 : imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6),
   rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx0 hx1) x13 x14 ->
   rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |} (x11 x13) (x12 x14)) ->
  forall (x13 : Original.LF_DOT_Logic.LF.Logic.In x3 x7) (x14 : imported_Original_LF__DOT__Logic_LF_Logic_In x4 x8),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx0 hx2) x13 x14 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_IndProp.LF.IndProp.Perm3_NotIn x1 x3 x5 x7 x9 x11 x13) (@imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn x2 x4 x6 x8 x10 x12 x14).
    
#[export] Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn_iso.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Perm3_NotIn := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Perm3_NotIn Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Perm3_NotIn Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn Original_LF__DOT__IndProp_LF_IndProp_Perm3__NotIn_iso := {}.