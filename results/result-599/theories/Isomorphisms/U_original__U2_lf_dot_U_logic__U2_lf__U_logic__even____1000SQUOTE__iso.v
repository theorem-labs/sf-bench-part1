From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_s__iso.

(* Key lemma: n1000 is definitionally equal to the expected form *)
Lemma n1000_eq : Imported.n1000 = imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0))).
Proof. vm_compute. reflexivity. Qed.

(* The imported axiom uses n1000, we need to show it matches the expected form *)
Definition imported_Original_LF__DOT__Logic_LF_Logic_even__1000' : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_even (imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0)))))
    imported_Original_LF__DOT__Basics_LF_Basics_true.
Proof.
  unfold imported_Corelib_Init_Logic_eq, imported_Original_LF__DOT__Basics_LF_Basics_even, imported_Original_LF__DOT__Basics_LF_Basics_true.
  rewrite <- n1000_eq.
  exact Imported.Original_LF__DOT__Logic_LF_Logic_even__1000'.
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_even__1000'_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 997 Datatypes.O imported_0 _0_iso)))))
          Original_LF__DOT__Basics_LF_Basics_true_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 997 Datatypes.O imported_0 _0_iso)))))
             Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_even (imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0)))))
                imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 997 Datatypes.O imported_0 _0_iso)))))
             Original_LF__DOT__Basics_LF_Basics_true_iso)
          x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.even 1000 = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 997 Datatypes.O imported_0 _0_iso)))))
                Original_LF__DOT__Basics_LF_Basics_true_iso)
             x)
    |} Original.LF_DOT_Logic.LF.Logic.even_1000' imported_Original_LF__DOT__Logic_LF_Logic_even__1000'.
Proof.
  (* This is an isomorphism between two axioms/Admitted statements *)
  (* Both sides are Prop/SProp statements about equality *)
  (* Since both are inhabited (by the axioms), we can use proof irrelevance *)
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.even_1000' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_even__1000' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_1000' Original_LF__DOT__Logic_LF_Logic_even__1000'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_1000' Imported.Original_LF__DOT__Logic_LF_Logic_even__1000' Original_LF__DOT__Logic_LF_Logic_even__1000'_iso := {}.