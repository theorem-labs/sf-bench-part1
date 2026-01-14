From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__minus__iso.

Definition imported_Original_LF__DOT__Induction_LF_Induction_minus__n__n : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_minus x x) imported_0 := Imported.Original_LF__DOT__Induction_LF_Induction_minus__n__n.

(* The original minus_n_n is an Admitted theorem, and our imported version is an axiom.
   Both claim that minus n n = 0.
   The isomorphism between the statements is in SProp, so we can use proof irrelevance. *)
Instance Original_LF__DOT__Induction_LF_Induction_minus__n__n_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_minus_iso hx hx) _0_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_minus_iso hx hx) _0_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_minus x2 x2) imported_0 =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_minus_iso hx hx) _0_iso) x;
      from_to := fun x : Original.LF_DOT_Basics.LF.Basics.minus x1 x1 = O => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_minus_iso hx hx) _0_iso) x)
    |} (Original.LF_DOT_Induction.LF.Induction.minus_n_n x1) (imported_Original_LF__DOT__Induction_LF_Induction_minus__n__n x2).
Proof.
  intros x1 x2 hx.
  (* The goal is to show that the original minus_n_n and imported minus_n_n are related.
     Both are proofs (in Prop/SProp) of equations about minus n n = 0.
     The isomorphism between them just uses the Corelib_Init_Logic_eq_iso. *)
  unfold rel_iso.
  simpl.
  (* Both sides are SProp, so they are proof-irrelevant and trivially equal. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.minus_n_n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_minus__n__n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.minus_n_n Original_LF__DOT__Induction_LF_Induction_minus__n__n_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.minus_n_n Imported.Original_LF__DOT__Induction_LF_Induction_minus__n__n Original_LF__DOT__Induction_LF_Induction_minus__n__n_iso := {}.