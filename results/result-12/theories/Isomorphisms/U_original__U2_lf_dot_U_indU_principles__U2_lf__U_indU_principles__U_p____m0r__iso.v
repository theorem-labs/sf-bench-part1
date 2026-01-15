From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Typeclasses Opaque rel_iso. *) (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r : imported_nat -> SProp := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r.

(* Standard lemma for Coq's nat *)
Lemma mul_0_r_standard : forall n : Datatypes.nat, PeanoNat.Nat.mul n Datatypes.O = Datatypes.O.
Proof.
  intro n. induction n; simpl; auto.
Qed.

(* Helper to convert standard equality to SProp Corelib_Init_Logic_eq *)
Lemma eq_to_Corelib_eq : forall (A : Type) (x y : A), Logic.eq x y -> Imported.Corelib_Init_Logic_eq A x y.
Proof.
  intros A x y H.
  destruct H.
  exact (Imported.Corelib_Init_Logic_eq_refl A x).
Qed.

(* Now we can build the isomorphism *)
Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r x2).
Proof.
  intros x1 x2 Hrel.
  unfold Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r.
  unfold imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r.
  unfold Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r.
  (* Goal is: Iso (x1 * 0 = 0) (Imported.Corelib_Init_Logic_eq Imported.nat (Imported.nat_mul x2 Imported.nat_O) Imported.nat_O) *)
  apply (Corelib_Init_Logic_eq_iso (Nat_mul_iso Hrel _0_iso) _0_iso).
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r := {}.
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r := {}.
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r_iso := {}.
