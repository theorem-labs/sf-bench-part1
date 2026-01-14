From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__add__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus__id__exercise : forall x x0 x1 : imported_nat, imported_Corelib_Init_Logic_eq x x0 -> imported_Corelib_Init_Logic_eq x0 x1 -> imported_Corelib_Init_Logic_eq (imported_Nat_add x x0) (imported_Nat_add x0 x1) := Imported.Original_LF__DOT__Basics_LF_Basics_plus__id__exercise.
Instance Original_LF__DOT__Basics_LF_Basics_plus__id__exercise_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : x1 = x3) (x8 : imported_Corelib_Init_Logic_eq x2 x4),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso hx hx0;
      from := from (Corelib_Init_Logic_eq_iso hx hx0);
      to_from := fun x : imported_Corelib_Init_Logic_eq x2 x4 => to_from (Corelib_Init_Logic_eq_iso hx hx0) x;
      from_to := fun x : x1 = x3 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso hx hx0) x)
    |} x7 x8 ->
  forall (x9 : x3 = x5) (x10 : imported_Corelib_Init_Logic_eq x4 x6),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso hx0 hx1;
      from := from (Corelib_Init_Logic_eq_iso hx0 hx1);
      to_from := fun x : imported_Corelib_Init_Logic_eq x4 x6 => to_from (Corelib_Init_Logic_eq_iso hx0 hx1) x;
      from_to := fun x : x3 = x5 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso hx0 hx1) x)
    |} x9 x10 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx1);
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx1));
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add x2 x4) (imported_Nat_add x4 x6) => to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx1)) x;
      from_to := fun x : x1 + x3 = x3 + x5 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx0) (Nat_add_iso hx0 hx1)) x)
    |} (Original.LF_DOT_Basics.LF.Basics.plus_id_exercise x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Basics_LF_Basics_plus__id__exercise x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1 x7 x8 Hrel1 x9 x10 Hrel2.
  (* The goal is to show that the results are related via the isomorphism *)
  (* Since both Original and Imported versions are axioms representing the same theorem, *)
  (* and all the inputs are properly related, the outputs should be related too *)
  (* For SProp equality, this is trivial by proof irrelevance *)
  unfold rel_iso. simpl.
  (* The goal is now an SProp equality, which is trivially true *)
  exact (IsomorphismDefinitions.eq_refl _).
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.plus_id_exercise := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_plus__id__exercise := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.plus_id_exercise Original_LF__DOT__Basics_LF_Basics_plus__id__exercise_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.plus_id_exercise Imported.Original_LF__DOT__Basics_LF_Basics_plus__id__exercise Original_LF__DOT__Basics_LF_Basics_plus__id__exercise_iso := {}.