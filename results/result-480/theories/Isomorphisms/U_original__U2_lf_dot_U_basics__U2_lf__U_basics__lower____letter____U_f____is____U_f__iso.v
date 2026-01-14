From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_f__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____letter__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_lower__letter imported_Original_LF__DOT__Basics_LF_Basics_F) imported_Original_LF__DOT__Basics_LF_Basics_F := Imported.Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F.
Instance Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_lower__letter_iso Original_LF__DOT__Basics_LF_Basics_F_iso) Original_LF__DOT__Basics_LF_Basics_F_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_lower__letter_iso Original_LF__DOT__Basics_LF_Basics_F_iso) Original_LF__DOT__Basics_LF_Basics_F_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_lower__letter imported_Original_LF__DOT__Basics_LF_Basics_F) imported_Original_LF__DOT__Basics_LF_Basics_F =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_lower__letter_iso Original_LF__DOT__Basics_LF_Basics_F_iso) Original_LF__DOT__Basics_LF_Basics_F_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.lower_letter Original.LF_DOT_Basics.LF.Basics.F = Original.LF_DOT_Basics.LF.Basics.F =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_lower__letter_iso Original_LF__DOT__Basics_LF_Basics_F_iso) Original_LF__DOT__Basics_LF_Basics_F_iso) x)
    |} Original.LF_DOT_Basics.LF.Basics.lower_letter_F_is_F imported_Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F.
Proof.
  (* rel_iso iso x y := eq (to iso x) y 
     The target type is in SProp, so all values are equal by SProp proof irrelevance *)
  unfold rel_iso. simpl.
  (* The goal should be in SProp, so we can use eq_refl *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.lower_letter_F_is_F := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.lower_letter_F_is_F Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.lower_letter_F_is_F Imported.Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F_iso := {}.