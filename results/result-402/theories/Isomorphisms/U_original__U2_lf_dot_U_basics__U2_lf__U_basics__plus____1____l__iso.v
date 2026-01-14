From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus__1__l : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S imported_0) x) (imported_S x) := Imported.Original_LF__DOT__Basics_LF_Basics_plus__1__l.
Instance Original_LF__DOT__Basics_LF_Basics_plus__1__l_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx);
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S imported_0) x2) (imported_S x2) => to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx)) x;
      from_to := fun x : 1 + x1 = S x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx)) x)
    |} (Original.LF_DOT_Basics.LF.Basics.plus_1_l x1) (imported_Original_LF__DOT__Basics_LF_Basics_plus__1__l x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  destruct hx. simpl.
  (* Both sides are in SProp, so they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.plus_1_l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_plus__1__l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.plus_1_l Original_LF__DOT__Basics_LF_Basics_plus__1__l_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.plus_1_l Imported.Original_LF__DOT__Basics_LF_Basics_plus__1__l Original_LF__DOT__Basics_LF_Basics_plus__1__l_iso := {}.