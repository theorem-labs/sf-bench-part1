From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__add__iso.

Definition imported_Original_LF__DOT__Induction_LF_Induction_add__comm : forall x x0 : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add x x0) (imported_Nat_add x0 x) := Imported.Original_LF__DOT__Induction_LF_Induction_add__comm.

(* The isomorphism between axioms: both are in SProp, so the relation is trivial *)
Instance Original_LF__DOT__Induction_LF_Induction_add__comm_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx);
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx));
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add x2 x4) (imported_Nat_add x4 x2) => to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx)) x;
      from_to := fun x : x1 + x3 = x3 + x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx)) x)
    |} (Original.LF_DOT_Induction.LF.Induction.add_comm x1 x3) (imported_Original_LF__DOT__Induction_LF_Induction_add__comm x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  (* The rel_iso unfolds to an SProp equality. Since SProp is proof irrelevant,
     we just need to show that both sides have the same type *)
  unfold rel_iso. simpl.
  (* The goal is an SProp equality between proofs in SProp - use eq_refl *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.add_comm := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_add__comm := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.add_comm Original_LF__DOT__Induction_LF_Induction_add__comm_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.add_comm Imported.Original_LF__DOT__Induction_LF_Induction_add__comm Original_LF__DOT__Induction_LF_Induction_add__comm_iso := {}.