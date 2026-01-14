From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__mul__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_mult__n__1 : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_mul x (imported_S imported_0)) x := Imported.Original_LF__DOT__Basics_LF_Basics_mult__n__1.
Instance Original_LF__DOT__Basics_LF_Basics_mult__n__1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_mul_iso hx (S_iso _0_iso)) hx;
      from := from (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx (S_iso _0_iso)) hx);
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_mul x2 (imported_S imported_0)) x2 => to_from (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx (S_iso _0_iso)) hx) x;
      from_to := fun x : x1 * 1 = x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx (S_iso _0_iso)) hx) x)
    |} (Original.LF_DOT_Basics.LF.Basics.mult_n_1 x1) (imported_Original_LF__DOT__Basics_LF_Basics_mult__n__1 x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  (* The goal is an SProp equality between two elements of an SProp type *)
  (* Both sides are proof-irrelevant (they're in SProp), so they're equal by reflexivity *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.mult_n_1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_mult__n__1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.mult_n_1 Original_LF__DOT__Basics_LF_Basics_mult__n__1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.mult_n_1 Imported.Original_LF__DOT__Basics_LF_Basics_mult__n__1 Original_LF__DOT__Basics_LF_Basics_mult__n__1_iso := {}.