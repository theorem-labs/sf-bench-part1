From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.ge__iso Interface.lt__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.ge__iso Interface.lt__iso Interface.or__iso.

  Export Interface.nat__iso.CodeBlocks Interface.ge__iso.CodeBlocks Interface.lt__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.ge__iso.Interface <+ Interface.lt__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases : forall x x0 : imported_nat, imported_or (imported_lt x x0) (imported_ge x x0).
Parameter Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := or_iso (lt_iso hx hx0) (ge_iso hx hx0);
      from := from (or_iso (lt_iso hx hx0) (ge_iso hx hx0));
      to_from := fun x : imported_or (imported_lt x2 x4) (imported_ge x2 x4) => to_from (or_iso (lt_iso hx hx0) (ge_iso hx hx0)) x;
      from_to := fun x : x1 < x3 \/ x1 >= x3 => seq_p_of_t (from_to (or_iso (lt_iso hx hx0) (ge_iso hx hx0)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases imported_Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso; constructor : typeclass_instances.


End Interface.