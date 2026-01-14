From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.and__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.and__iso Interface.or__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.and__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or : forall x x0 : SProp, (imported_or x x0 -> imported_False) -> imported_and (x -> imported_False) (x0 -> imported_False).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : ~ (x1 \/ x3)) (x6 : imported_or x2 x4 -> imported_False),
  (forall (x7 : x1 \/ x3) (x8 : imported_or x2 x4),
   rel_iso
     {| to := or_iso hx hx0; from := from (or_iso hx hx0); to_from := fun x : imported_or x2 x4 => to_from (or_iso hx hx0) x; from_to := fun x : x1 \/ x3 => seq_p_of_t (from_to (or_iso hx hx0) x) |}
     x7 x8 ->
   rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |} (x5 x7) (x6 x8)) ->
  rel_iso
    {|
      to := and_iso (IsoArrow hx False_iso) (IsoArrow hx0 False_iso);
      from := from (and_iso (IsoArrow hx False_iso) (IsoArrow hx0 False_iso));
      to_from := fun x : imported_and (x2 -> imported_False) (x4 -> imported_False) => to_from (and_iso (IsoArrow hx False_iso) (IsoArrow hx0 False_iso)) x;
      from_to := fun x : ~ x1 /\ ~ x3 => seq_p_of_t (from_to (and_iso (IsoArrow hx False_iso) (IsoArrow hx0 False_iso)) x)
    |} (Original.LF_DOT_ProofObjects.LF.ProofObjects.de_morgan_not_or x1 x3 x5) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or x6).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.de_morgan_not_or ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.de_morgan_not_or imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or_iso; constructor : typeclass_instances.


End Interface.