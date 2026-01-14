From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso Interface.iff__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso Interface.iff__iso Interface.or__iso.

  Export Interface.and__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and : forall x x0 x1 : SProp, imported_iff (imported_or x (imported_and x0 x1)) (imported_and (imported_or x x0) (imported_or x x1)).
Parameter Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6),
  rel_iso
    {|
      to := iff_iso (or_iso hx (and_iso hx0 hx1)) (and_iso (or_iso hx hx0) (or_iso hx hx1));
      from := from (iff_iso (or_iso hx (and_iso hx0 hx1)) (and_iso (or_iso hx hx0) (or_iso hx hx1)));
      to_from :=
        fun x : imported_iff (imported_or x2 (imported_and x4 x6)) (imported_and (imported_or x2 x4) (imported_or x2 x6)) =>
        to_from (iff_iso (or_iso hx (and_iso hx0 hx1)) (and_iso (or_iso hx hx0) (or_iso hx hx1))) x;
      from_to := fun x : x1 \/ x3 /\ x5 <-> (x1 \/ x3) /\ (x1 \/ x5) => seq_p_of_t (from_to (iff_iso (or_iso hx (and_iso hx0 hx1)) (and_iso (or_iso hx hx0) (or_iso hx hx1))) x)
    |} (Original.LF_DOT_Logic.LF.Logic.or_distributes_over_and x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and x2 x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.or_distributes_over_and ?x) => unify x Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.or_distributes_over_and imported_Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and ?x) => unify x Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and_iso; constructor : typeclass_instances.


End Interface.