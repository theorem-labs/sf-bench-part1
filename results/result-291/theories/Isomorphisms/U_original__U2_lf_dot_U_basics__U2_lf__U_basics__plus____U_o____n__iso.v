From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus__O__n : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add imported_0 x) x := Imported.Original_LF__DOT__Basics_LF_Basics_plus__O__n.
Instance Original_LF__DOT__Basics_LF_Basics_plus__O__n_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso _0_iso hx) hx;
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso _0_iso hx) hx);
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add imported_0 x2) x2 => to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso _0_iso hx) hx) x;
      from_to := fun x : 0 + x1 = x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso _0_iso hx) hx) x)
    |} (Original.LF_DOT_Basics.LF.Basics.plus_O_n x1) (imported_Original_LF__DOT__Basics_LF_Basics_plus__O__n x2).
Proof.
  intros x1 x2 hx.
  (* The result type is an SProp (imported_Corelib_Init_Logic_eq ...) 
     Both sides are proofs in SProp, so rel_iso holds trivially *)
  unfold rel_iso. simpl.
  (* The goal is: eq (to (Corelib_Init_Logic_eq_iso ...) (plus_O_n x1)) (imported_plus_O_n x2) *)
  (* Both sides live in SProp, so they are definitionally equal *)
  exact (IsomorphismDefinitions.eq_refl _).
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.plus_O_n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_plus__O__n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.plus_O_n Original_LF__DOT__Basics_LF_Basics_plus__O__n_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.plus_O_n Imported.Original_LF__DOT__Basics_LF_Basics_plus__O__n Original_LF__DOT__Basics_LF_Basics_plus__O__n_iso := {}.