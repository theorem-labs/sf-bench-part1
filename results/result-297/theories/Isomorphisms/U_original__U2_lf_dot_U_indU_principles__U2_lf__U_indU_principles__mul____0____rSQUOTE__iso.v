From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r' : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_mul x imported_0) imported_0 := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'.
Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_mul_iso hx _0_iso) _0_iso;
      from := from (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx _0_iso) _0_iso);
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_mul x2 imported_0) imported_0 => to_from (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx _0_iso) _0_iso) x;
      from_to := fun x : x1 * O = O => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx _0_iso) _0_iso) x)
    |} (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r' x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r' x2).
Proof.
  intros x1 x2 hx.
  (* rel_iso for an Iso on Props/SProps is trivial since both sides are inhabited proofs *)
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'_iso := {}.