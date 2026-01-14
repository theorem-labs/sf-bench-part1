From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0 : forall x x0 : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_Nat_mul x imported_0) (imported_Nat_mul x0 imported_0)) imported_0 := Imported.Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0.

(* The isomorphism for the Admitted theorem mult_n_0_m_0 *)
(* Since the original theorem is Admitted and our Lean axiom corresponds to it, *)
(* we prove the isomorphism by showing both are SProp values that can be mapped via the eq_iso *)
Instance Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso (Nat_mul_iso hx _0_iso) (Nat_mul_iso hx0 _0_iso)) _0_iso;
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso (Nat_mul_iso hx _0_iso) (Nat_mul_iso hx0 _0_iso)) _0_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_Nat_mul x2 imported_0) (imported_Nat_mul x4 imported_0)) imported_0 =>
        to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso (Nat_mul_iso hx _0_iso) (Nat_mul_iso hx0 _0_iso)) _0_iso) x;
      from_to := fun x : Nat.add (Nat.mul x1 Datatypes.O) (Nat.mul x3 Datatypes.O) = Datatypes.O => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso (Nat_mul_iso hx _0_iso) (Nat_mul_iso hx0 _0_iso)) _0_iso) x)
    |} (Original.LF_DOT_Basics.LF.Basics.mult_n_0_m_0 x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0 x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  unfold rel_iso.
  (* The goal is eq (to iso (mult_n_0_m_0 x1 x3)) (imported_mult_n_0_m_0 x2 x4) *)
  (* Both are values in SProp, so they are proof-irrelevant and equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.mult_n_0_m_0 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.mult_n_0_m_0 Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.mult_n_0_m_0 Imported.Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0 Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0_iso := {}.