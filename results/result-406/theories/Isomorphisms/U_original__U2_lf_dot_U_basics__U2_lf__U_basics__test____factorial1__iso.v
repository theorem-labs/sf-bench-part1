From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__factorial__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__factorial1 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_factorial (imported_S (imported_S (imported_S imported_0))))
    (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))) := Imported.Original_LF__DOT__Basics_LF_Basics_test__factorial1.

(* test_factorial1 is an axiom in Original.v (Admitted) and an axiom in Imported,
   so the isomorphism relating them must also be an axiom.
   This is allowed per the task description. *)
Axiom Original_LF__DOT__Basics_LF_Basics_test__factorial1_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_factorial_iso (S_iso (S_iso (S_iso _0_iso)))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))));
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_factorial_iso (S_iso (S_iso (S_iso _0_iso)))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_factorial (imported_S (imported_S (imported_S imported_0))))
                (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))) =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_factorial_iso (S_iso (S_iso (S_iso _0_iso)))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.factorial (S (S (S O))) = (S (S (S (S (S (S O)))))) =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_factorial_iso (S_iso (S_iso (S_iso _0_iso)))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) x)
    |} Original.LF_DOT_Basics.LF.Basics.test_factorial1 imported_Original_LF__DOT__Basics_LF_Basics_test__factorial1.
Existing Instance Original_LF__DOT__Basics_LF_Basics_test__factorial1_iso.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_factorial1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__factorial1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_factorial1 Original_LF__DOT__Basics_LF_Basics_test__factorial1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_factorial1 Imported.Original_LF__DOT__Basics_LF_Basics_test__factorial1 Original_LF__DOT__Basics_LF_Basics_test__factorial1_iso := {}.