From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.iff__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.iff__iso Interface.or__iso.

  Export Interface.iff__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.iff__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_or__assoc : forall x x0 x1 : SProp, imported_iff (imported_or x (imported_or x0 x1)) (imported_or (imported_or x x0) x1).
Parameter Original_LF__DOT__Logic_LF_Logic_or__assoc_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6),
  rel_iso
    {|
      to := iff_iso (or_iso hx (or_iso hx0 hx1)) (or_iso (or_iso hx hx0) hx1);
      from := from (iff_iso (or_iso hx (or_iso hx0 hx1)) (or_iso (or_iso hx hx0) hx1));
      to_from := fun x : imported_iff (imported_or x2 (imported_or x4 x6)) (imported_or (imported_or x2 x4) x6) => to_from (iff_iso (or_iso hx (or_iso hx0 hx1)) (or_iso (or_iso hx hx0) hx1)) x;
      from_to := fun x : x1 \/ x3 \/ x5 <-> (x1 \/ x3) \/ x5 => seq_p_of_t (from_to (iff_iso (or_iso hx (or_iso hx0 hx1)) (or_iso (or_iso hx hx0) hx1)) x)
    |} (Original.LF_DOT_Logic.LF.Logic.or_assoc x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_or__assoc x2 x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_or__assoc_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.or_assoc ?x) => unify x Original_LF__DOT__Logic_LF_Logic_or__assoc_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.or_assoc imported_Original_LF__DOT__Logic_LF_Logic_or__assoc ?x) => unify x Original_LF__DOT__Logic_LF_Logic_or__assoc_iso; constructor : typeclass_instances.


End Interface.