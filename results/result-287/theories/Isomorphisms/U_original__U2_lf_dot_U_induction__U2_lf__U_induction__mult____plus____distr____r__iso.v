From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r : forall x x0 x1 : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_mul (imported_Nat_add x x0) x1) (imported_Nat_add (imported_Nat_mul x x1) (imported_Nat_mul x0 x1)) := Imported.Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r.
Instance Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_mul_iso (Nat_add_iso hx hx0) hx1) (Nat_add_iso (Nat_mul_iso hx hx1) (Nat_mul_iso hx0 hx1));
      from := from (Corelib_Init_Logic_eq_iso (Nat_mul_iso (Nat_add_iso hx hx0) hx1) (Nat_add_iso (Nat_mul_iso hx hx1) (Nat_mul_iso hx0 hx1)));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Nat_mul (imported_Nat_add x2 x4) x6) (imported_Nat_add (imported_Nat_mul x2 x6) (imported_Nat_mul x4 x6)) =>
        to_from (Corelib_Init_Logic_eq_iso (Nat_mul_iso (Nat_add_iso hx hx0) hx1) (Nat_add_iso (Nat_mul_iso hx hx1) (Nat_mul_iso hx0 hx1))) x;
      from_to :=
        fun x : (x1 + x3) * x5 = x1 * x5 + x3 * x5 =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_mul_iso (Nat_add_iso hx hx0) hx1) (Nat_add_iso (Nat_mul_iso hx hx1) (Nat_mul_iso hx0 hx1))) x)
    |} (Original.LF_DOT_Induction.LF.Induction.mult_plus_distr_r x1 x3 x5) (imported_Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1.
  unfold rel_iso. simpl.
  (* The goal is to show that applying 'to' to the LHS gives the RHS *)
  (* Both sides are equalities (proofs), and the isomorphism on equalities works by transport *)
  (* Since both sides are proofs of equality propositions, they are equal by proof irrelevance in SProp *)
  reflexivity.
Defined.
Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.mult_plus_distr_r := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.mult_plus_distr_r Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.mult_plus_distr_r Imported.Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r_iso := {}.