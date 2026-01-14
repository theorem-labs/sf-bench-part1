From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm : forall x x0 : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_mul x x0) (imported_Nat_mul x0 x) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm.
Instance Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_mul_iso hx hx0) (Nat_mul_iso hx0 hx);
      from := from (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx hx0) (Nat_mul_iso hx0 hx));
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_mul x2 x4) (imported_Nat_mul x4 x2) => to_from (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx hx0) (Nat_mul_iso hx0 hx)) x;
      from_to := fun x : x1 * x3 = x3 * x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx hx0) (Nat_mul_iso hx0 hx)) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.mult_comm x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  unfold rel_iso. simpl.
  (* Both sides are inhabitants of the same SProp type, so they are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.mult_comm := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.mult_comm Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.mult_comm Imported.Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm Original_LF__DOT__AltAuto_LF_AltAuto_mult__comm_iso := {}.