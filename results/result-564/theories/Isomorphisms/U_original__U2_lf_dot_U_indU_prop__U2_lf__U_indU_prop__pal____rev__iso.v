From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__pal__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_pal__rev : forall (x : Type) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_pal x0 -> imported_Corelib_Init_Logic_eq x0 (imported_Original_LF__DOT__Poly_LF_Poly_rev x0) := Imported.Original_LF__DOT__IndProp_LF_IndProp_pal__rev.
Instance Original_LF__DOT__IndProp_LF_IndProp_pal__rev_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.pal x3) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_pal x4),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_pal_iso hx0) x5 x6 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0);
      from := from (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0));
      to_from := fun x : imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_rev x4) => to_from (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0)) x;
      from_to := fun x : x3 = Original.LF_DOT_Poly.LF.Poly.rev x3 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.pal_rev x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_pal__rev x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hpal.
  (* rel_iso on the custom Iso means: to iso (pal_rev x5) = imported_pal_rev x6 *)
  (* The to function is Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0) *)
  unfold rel_iso. simpl.
  (* Goal is in SProp, so all proofs are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.pal_rev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_pal__rev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.pal_rev Original_LF__DOT__IndProp_LF_IndProp_pal__rev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.pal_rev Imported.Original_LF__DOT__IndProp_LF_IndProp_pal__rev Original_LF__DOT__IndProp_LF_IndProp_pal__rev_iso := {}.