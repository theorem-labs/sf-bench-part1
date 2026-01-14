From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso Interface.nat__iso Interface.U_nat__add__iso Interface.lt__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso Interface.nat__iso Interface.U_nat__add__iso Interface.lt__iso.

  Export Interface.and__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.lt__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.lt__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt : forall x x0 x1 : imported_nat, imported_lt (imported_Nat_add x x0) x1 -> imported_and (imported_lt x x1) (imported_lt x0 x1).
Parameter Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : x1 + x3 < x5) (x8 : imported_lt (imported_Nat_add x2 x4) x6),
  rel_iso
    {|
      to := lt_iso (Nat_add_iso hx hx0) hx1;
      from := from (lt_iso (Nat_add_iso hx hx0) hx1);
      to_from := fun x : imported_lt (imported_Nat_add x2 x4) x6 => to_from (lt_iso (Nat_add_iso hx hx0) hx1) x;
      from_to := fun x : x1 + x3 < x5 => seq_p_of_t (from_to (lt_iso (Nat_add_iso hx hx0) hx1) x)
    |} x7 x8 ->
  rel_iso
    {|
      to := and_iso (lt_iso hx hx1) (lt_iso hx0 hx1);
      from := from (and_iso (lt_iso hx hx1) (lt_iso hx0 hx1));
      to_from := fun x : imported_and (imported_lt x2 x6) (imported_lt x4 x6) => to_from (and_iso (lt_iso hx hx1) (lt_iso hx0 hx1)) x;
      from_to := fun x : x1 < x5 /\ x3 < x5 => seq_p_of_t (from_to (and_iso (lt_iso hx hx1) (lt_iso hx0 hx1)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.plus_lt x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_lt ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_lt imported_Original_LF__DOT__IndProp_LF_IndProp_plus__lt ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__lt_iso; constructor : typeclass_instances.


End Interface.