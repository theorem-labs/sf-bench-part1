From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso.

  Export Interface.U_false__iso.CodeBlocks.

#[export] Instance: MustUnfold Logic.not := {}.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Args <+ Interface.U_false__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Logic_not : SProp -> SProp
  := fun x : SProp => x -> imported_False.
Definition Logic_not_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> Iso (~ x1) (imported_Logic_not x2)
  := fun (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) => IsoArrow hx False_iso.
Existing Instance Logic_not_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Logic.not ?x) => unify x Logic_not_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Logic.not imported_Logic_not ?x) => unify x Logic_not_iso; constructor : typeclass_instances.


End Interface.