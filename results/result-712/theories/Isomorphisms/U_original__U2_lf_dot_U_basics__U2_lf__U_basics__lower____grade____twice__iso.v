From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_c__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_grade__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_minus__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natural__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_lower__grade__twice : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Basics_LF_Basics_lower__grade
       (imported_Original_LF__DOT__Basics_LF_Basics_lower__grade
          (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_B imported_Original_LF__DOT__Basics_LF_Basics_Minus)))
    (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_C imported_Original_LF__DOT__Basics_LF_Basics_Natural) := Imported.Original_LF__DOT__Basics_LF_Basics_lower__grade__twice.

(* lower_grade_twice is an axiom (Admitted) in the original, so we use an axiom for this isomorphism as permitted *)
Axiom Original_LF__DOT__Basics_LF_Basics_lower__grade__twice_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
             (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)))
          (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Natural_iso);
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
                (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
                   (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)))
             (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Natural_iso));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Basics_LF_Basics_lower__grade
                   (imported_Original_LF__DOT__Basics_LF_Basics_lower__grade
                      (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_B imported_Original_LF__DOT__Basics_LF_Basics_Minus)))
                (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_C imported_Original_LF__DOT__Basics_LF_Basics_Natural) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
                (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
                   (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)))
             (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Natural_iso))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Basics.LF.Basics.lower_grade
                (Original.LF_DOT_Basics.LF.Basics.lower_grade (Original.LF_DOT_Basics.LF.Basics.Grade Original.LF_DOT_Basics.LF.Basics.B Original.LF_DOT_Basics.LF.Basics.Minus)) =
              Original.LF_DOT_Basics.LF.Basics.Grade Original.LF_DOT_Basics.LF.Basics.C Original.LF_DOT_Basics.LF.Basics.Natural =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
                   (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso
                      (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)))
                (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Natural_iso))
             x)
    |} Original.LF_DOT_Basics.LF.Basics.lower_grade_twice imported_Original_LF__DOT__Basics_LF_Basics_lower__grade__twice.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.lower_grade_twice := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_lower__grade__twice := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.lower_grade_twice Original_LF__DOT__Basics_LF_Basics_lower__grade__twice_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.lower_grade_twice Imported.Original_LF__DOT__Basics_LF_Basics_lower__grade__twice Original_LF__DOT__Basics_LF_Basics_lower__grade__twice_iso := {}.