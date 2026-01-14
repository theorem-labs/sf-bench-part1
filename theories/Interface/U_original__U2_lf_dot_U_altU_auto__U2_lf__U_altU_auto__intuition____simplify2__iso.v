From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2 : forall (x x0 : imported_nat) (x1 x2 : imported_nat -> SProp), imported_and (imported_Corelib_Init_Logic_eq x x0) (imported_and (x1 x -> x2 x) (x1 x)) -> x2 x0.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat -> Prop) (x6 : imported_nat -> SProp)
    (hx1 : forall (x7 : nat) (x8 : imported_nat), rel_iso nat_iso x7 x8 -> Iso (x5 x7) (x6 x8)) (x7 : nat -> Prop) (x8 : imported_nat -> SProp)
    (hx2 : forall (x9 : nat) (x10 : imported_nat), rel_iso nat_iso x9 x10 -> Iso (x7 x9) (x8 x10)) (x9 : x1 = x3 /\ (x5 x1 -> x7 x1) /\ x5 x1)
    (x10 : imported_and (imported_Corelib_Init_Logic_eq x2 x4) (imported_and (x6 x2 -> x8 x2) (x6 x2))),
  rel_iso
    {|
      to := and_iso (Corelib_Init_Logic_eq_iso hx hx0) (and_iso (IsoArrow (hx1 x1 x2 hx) (hx2 x1 x2 hx)) (hx1 x1 x2 hx));
      from := from (and_iso (Corelib_Init_Logic_eq_iso hx hx0) (and_iso (IsoArrow (hx1 x1 x2 hx) (hx2 x1 x2 hx)) (hx1 x1 x2 hx)));
      to_from :=
        fun x : imported_and (imported_Corelib_Init_Logic_eq x2 x4) (imported_and (x6 x2 -> x8 x2) (x6 x2)) =>
        to_from (and_iso (Corelib_Init_Logic_eq_iso hx hx0) (and_iso (IsoArrow (hx1 x1 x2 hx) (hx2 x1 x2 hx)) (hx1 x1 x2 hx))) x;
      from_to := fun x : x1 = x3 /\ (x5 x1 -> x7 x1) /\ x5 x1 => seq_p_of_t (from_to (and_iso (Corelib_Init_Logic_eq_iso hx hx0) (and_iso (IsoArrow (hx1 x1 x2 hx) (hx2 x1 x2 hx)) (hx1 x1 x2 hx))) x)
    |} x9 x10 ->
  rel_iso (hx2 x3 x4 hx0) (Original.LF_DOT_AltAuto.LF.AltAuto.intuition_simplify2 x1 x3 x5 x7 x9) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2 x6 x8 x10).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.intuition_simplify2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.intuition_simplify2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2_iso; constructor : typeclass_instances.


End Interface.