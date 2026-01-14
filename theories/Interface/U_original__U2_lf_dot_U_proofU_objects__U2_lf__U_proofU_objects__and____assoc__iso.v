From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso.

  Export Interface.and__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Args <+ Interface.and__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc : forall x x0 x1 : SProp, imported_and x (imported_and x0 x1) -> imported_and (imported_and x x0) x1.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : x1 /\ x3 /\ x5)
    (x8 : imported_and x2 (imported_and x4 x6)),
  rel_iso
    {|
      to := and_iso hx (and_iso hx0 hx1);
      from := from (and_iso hx (and_iso hx0 hx1));
      to_from := fun x : imported_and x2 (imported_and x4 x6) => to_from (and_iso hx (and_iso hx0 hx1)) x;
      from_to := fun x : x1 /\ x3 /\ x5 => seq_p_of_t (from_to (and_iso hx (and_iso hx0 hx1)) x)
    |} x7 x8 ->
  rel_iso
    {|
      to := and_iso (and_iso hx hx0) hx1;
      from := from (and_iso (and_iso hx hx0) hx1);
      to_from := fun x : imported_and (imported_and x2 x4) x6 => to_from (and_iso (and_iso hx hx0) hx1) x;
      from_to := fun x : (x1 /\ x3) /\ x5 => seq_p_of_t (from_to (and_iso (and_iso hx hx0) hx1) x)
    |} (Original.LF_DOT_ProofObjects.LF.ProofObjects.and_assoc x1 x3 x5 x7) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc x8).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.and_assoc ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.and_assoc imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_and__assoc_iso; constructor : typeclass_instances.


End Interface.