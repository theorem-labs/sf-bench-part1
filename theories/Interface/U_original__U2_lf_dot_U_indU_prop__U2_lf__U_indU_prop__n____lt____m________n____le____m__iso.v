From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.le__iso Interface.lt__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.le__iso Interface.lt__iso.

  Export Interface.nat__iso.CodeBlocks Interface.le__iso.CodeBlocks Interface.lt__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.le__iso.Interface <+ Interface.lt__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m : forall x x0 : imported_nat, imported_lt x x0 -> imported_le x x0.
Parameter Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : x1 < x3) (x6 : imported_lt x2 x4),
  rel_iso (lt_iso hx hx0) x5 x6 -> rel_iso (le_iso hx hx0) (Original.LF_DOT_IndProp.LF.IndProp.n_lt_m__n_le_m x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.n_lt_m__n_le_m ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.n_lt_m__n_le_m imported_Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m_iso; constructor : typeclass_instances.


End Interface.