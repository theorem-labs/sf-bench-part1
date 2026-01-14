From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add x (imported_S imported_0)) (imported_S x) := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'.

(* The isomorphism proof for axioms: since both are axioms stating the same thing,
   and the result type is in SProp, any two proofs are definitionally equal. *)
Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso hx (S_iso _0_iso)) (S_iso hx);
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso hx (S_iso _0_iso)) (S_iso hx));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add x2 (imported_S imported_0)) (imported_S x2) => to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso hx (S_iso _0_iso)) (S_iso hx)) x;
      from_to := fun x : x1 + 1 = S x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso hx (S_iso _0_iso)) (S_iso hx)) x)
    |} (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  (* Both sides are SProp values, so they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.plus_one_r' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r'_iso := {}.