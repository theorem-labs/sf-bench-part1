From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

#[export] Instance: MustUnfold Original.LF.Rel.relation := {}.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Definition imported_Original_LF_Rel_relation : Type -> Type
  := fun x : Type => x -> x -> SProp.
Definition Original_LF_Rel_relation_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF.Rel.relation x1) (imported_Original_LF_Rel_relation x2)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) => IsoArrow hx (IsoArrow hx iso_Prop_SProp).
Existing Instance Original_LF_Rel_relation_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.relation ?x) => unify x Original_LF_Rel_relation_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.relation imported_Original_LF_Rel_relation ?x) => unify x Original_LF_Rel_relation_iso; constructor : typeclass_instances.


End Interface.