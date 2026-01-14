From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_peanoU_nat__U_nat__leb__iso Isomorphisms.true__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_foo' : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_PeanoNat_Nat_leb imported_0 x) imported_true := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_foo'.

Instance Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (relax_Iso_Ts_Ps (Corelib_Init_Logic_eq_iso (PeanoNat_Nat_leb_iso _0_iso hx) true_iso)) (Original.LF_DOT_Imp.LF.Imp.AExp.foo' x1) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_foo' x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso at 1.
  unfold relax_Iso_Ts_Ps. simpl.
  (* Both sides are proofs in SProp - we can use proof irrelevance *)
  reflexivity.
Qed.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.foo' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_foo' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.foo' Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.foo' Imported.Original_LF__DOT__Imp_LF_Imp_AExp_foo' Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso := {}.
