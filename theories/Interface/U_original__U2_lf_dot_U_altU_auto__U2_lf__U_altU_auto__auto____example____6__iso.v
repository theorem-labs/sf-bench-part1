From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso Interface.le__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6 : forall x x0 x1 : imported_nat, (imported_le x x1 -> imported_and (imported_le x x0) (imported_le x0 x)) -> imported_le x x1 -> imported_Corelib_Init_Logic_eq x x0.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : x1 <= x5 -> x1 <= x3 <= x1) (x8 : imported_le x2 x6 -> imported_and (imported_le x2 x4) (imported_le x4 x2)),
  (forall (x9 : x1 <= x5) (x10 : imported_le x2 x6),
   rel_iso
     {| to := le_iso hx hx1; from := from (le_iso hx hx1); to_from := fun x : imported_le x2 x6 => to_from (le_iso hx hx1) x; from_to := fun x : x1 <= x5 => seq_p_of_t (from_to (le_iso hx hx1) x) |}
     x9 x10 ->
   rel_iso
     {|
       to := and_iso (le_iso hx hx0) (le_iso hx0 hx);
       from := from (and_iso (le_iso hx hx0) (le_iso hx0 hx));
       to_from := fun x : imported_and (imported_le x2 x4) (imported_le x4 x2) => to_from (and_iso (le_iso hx hx0) (le_iso hx0 hx)) x;
       from_to := fun x : x1 <= x3 <= x1 => seq_p_of_t (from_to (and_iso (le_iso hx hx0) (le_iso hx0 hx)) x)
     |} (x7 x9) (x8 x10)) ->
  forall (x9 : x1 <= x5) (x10 : imported_le x2 x6),
  rel_iso
    {| to := le_iso hx hx1; from := from (le_iso hx hx1); to_from := fun x : imported_le x2 x6 => to_from (le_iso hx hx1) x; from_to := fun x : x1 <= x5 => seq_p_of_t (from_to (le_iso hx hx1) x) |}
    x9 x10 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso hx hx0;
      from := from (Corelib_Init_Logic_eq_iso hx hx0);
      to_from := fun x : imported_Corelib_Init_Logic_eq x2 x4 => to_from (Corelib_Init_Logic_eq_iso hx hx0) x;
      from_to := fun x : x1 = x3 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso hx hx0) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_6 x1 x3 x5 x7 x9) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6 x8 x10).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_6 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_6 imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6_iso; constructor : typeclass_instances.


End Interface.