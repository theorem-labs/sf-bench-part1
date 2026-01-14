From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__orb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__orb4 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_orb imported_Original_LF__DOT__Basics_LF_Basics_true imported_Original_LF__DOT__Basics_LF_Basics_true)
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Basics_LF_Basics_test__orb4.
Instance Original_LF__DOT__Basics_LF_Basics_test__orb4_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_orb_iso Original_LF__DOT__Basics_LF_Basics_true_iso Original_LF__DOT__Basics_LF_Basics_true_iso)
          Original_LF__DOT__Basics_LF_Basics_true_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_orb_iso Original_LF__DOT__Basics_LF_Basics_true_iso Original_LF__DOT__Basics_LF_Basics_true_iso)
             Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_orb imported_Original_LF__DOT__Basics_LF_Basics_true imported_Original_LF__DOT__Basics_LF_Basics_true)
                imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_orb_iso Original_LF__DOT__Basics_LF_Basics_true_iso Original_LF__DOT__Basics_LF_Basics_true_iso)
             Original_LF__DOT__Basics_LF_Basics_true_iso)
          x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.orb Original.LF_DOT_Basics.LF.Basics.true Original.LF_DOT_Basics.LF.Basics.true = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_orb_iso Original_LF__DOT__Basics_LF_Basics_true_iso Original_LF__DOT__Basics_LF_Basics_true_iso)
                Original_LF__DOT__Basics_LF_Basics_true_iso)
             x)
    |} Original.LF_DOT_Basics.LF.Basics.test_orb4 imported_Original_LF__DOT__Basics_LF_Basics_test__orb4.
Proof.
  (* rel_iso for terms whose type is an SProp (equality in SProp) *)
  (* Both sides are proofs of equality, which live in SProp. *)
  (* By SProp proof irrelevance, any two terms of an SProp are equal. *)
  unfold rel_iso. simpl.
  (* Goal is: eq (to (Corelib_Init_Logic_eq_iso ...) test_orb4) imported_test_orb4 *)
  (* Both are SProp values, so they are definitionally equal *)
  exact (IsomorphismDefinitions.eq_refl _).
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_orb4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__orb4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_orb4 Original_LF__DOT__Basics_LF_Basics_test__orb4_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_orb4 Imported.Original_LF__DOT__Basics_LF_Basics_test__orb4 Original_LF__DOT__Basics_LF_Basics_test__orb4_iso := {}.