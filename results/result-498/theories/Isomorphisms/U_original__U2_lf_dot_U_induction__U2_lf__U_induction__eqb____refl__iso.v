From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Definition imported_Original_LF__DOT__Induction_LF_Induction_eqb__refl : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x x) imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Induction_LF_Induction_eqb__refl.
Instance Original_LF__DOT__Induction_LF_Induction_eqb__refl_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx) Original_LF__DOT__Basics_LF_Basics_true_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx) Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x2) imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx) Original_LF__DOT__Basics_LF_Basics_true_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.eqb x1 x1 = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso hx hx) Original_LF__DOT__Basics_LF_Basics_true_iso) x)
    |} (Original.LF_DOT_Induction.LF.Induction.eqb_refl x1) (imported_Original_LF__DOT__Induction_LF_Induction_eqb__refl x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  (* Both source and target are SProp equalities, so we use proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.eqb_refl := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_eqb__refl := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.eqb_refl Original_LF__DOT__Induction_LF_Induction_eqb__refl_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.eqb_refl Imported.Original_LF__DOT__Induction_LF_Induction_eqb__refl Original_LF__DOT__Induction_LF_Induction_eqb__refl_iso := {}.