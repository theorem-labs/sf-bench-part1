From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_peanoU_nat__U_nat__add__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop : forall x x0 : imported_nat, imported_Corelib_Init_Logic_eq (imported_PeanoNat_Nat_add x x0) (imported_PeanoNat_Nat_add x0 x) := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop.
Instance Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (PeanoNat_Nat_add_iso hx hx0) (PeanoNat_Nat_add_iso hx0 hx);
      from := from (Corelib_Init_Logic_eq_iso (PeanoNat_Nat_add_iso hx hx0) (PeanoNat_Nat_add_iso hx0 hx));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_PeanoNat_Nat_add x2 x4) (imported_PeanoNat_Nat_add x4 x2) =>
        to_from (Corelib_Init_Logic_eq_iso (PeanoNat_Nat_add_iso hx hx0) (PeanoNat_Nat_add_iso hx0 hx)) x;
      from_to := fun x : x1 + x3 = x3 + x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (PeanoNat_Nat_add_iso hx hx0) (PeanoNat_Nat_add_iso hx0 hx)) x)
    |} (Original.LF_DOT_Imp.LF.Imp.AExp.repeat_loop x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  unfold rel_iso. simpl.
  destruct hx. destruct hx0.
  (* Now we need to show that to (Original.LF_DOT_Imp.LF.Imp.AExp.repeat_loop x1 x3) = imported_Original... *)
  (* Both the LHS and RHS are in SProp - they are proofs of equality *)
  (* The 'to' function maps an equality proof in Prop to one in SProp *)
  (* Since both sides produce elements of SProp, all proofs in SProp are equal by definitional UIP *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.repeat_loop := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.repeat_loop Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.repeat_loop Imported.Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop_iso := {}.