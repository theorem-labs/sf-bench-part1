From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.iff__iso.

  Export Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.iff__iso.Args <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_iff__sym : forall x x0 : SProp, imported_iff x x0 -> imported_iff x0 x.
Parameter Original_LF__DOT__Logic_LF_Logic_iff__sym_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 <-> x3) (x6 : imported_iff x2 x4),
  rel_iso (iff_iso hx hx0) x5 x6 -> rel_iso (iff_iso hx0 hx) (Original.LF_DOT_Logic.LF.Logic.iff_sym x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_iff__sym x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_iff__sym_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.iff_sym ?x) => unify x Original_LF__DOT__Logic_LF_Logic_iff__sym_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.iff_sym imported_Original_LF__DOT__Logic_LF_Logic_iff__sym ?x) => unify x Original_LF__DOT__Logic_LF_Logic_iff__sym_iso; constructor : typeclass_instances.


End Interface.