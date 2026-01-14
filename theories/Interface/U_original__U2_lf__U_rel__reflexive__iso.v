From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks.

#[export] Instance: MustUnfold (@Original.LF.Rel.reflexive) := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Args <+ Interface.U_original__U2_lf__U_rel__relation__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF_Rel_reflexive : forall x : Type, (x -> x -> SProp) -> SProp
  := fun (x : Type) (x0 : x -> x -> SProp) => forall a' : x, x0 a' a'.
Definition Original_LF_Rel_reflexive_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  Iso (Original.LF.Rel.reflexive x3) (imported_Original_LF_Rel_reflexive x4)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp)
    (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) =>
  IsoForall (fun a : x1 => x3 a a) (fun x6 : x2 => x4 x6 x6) (fun (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) => hx0 x5 x6 hx1 x5 x6 hx1).
Existing Instance Original_LF_Rel_reflexive_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF.Rel.reflexive) ?x) => unify x Original_LF_Rel_reflexive_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF.Rel.reflexive) imported_Original_LF_Rel_reflexive ?x) => unify x Original_LF_Rel_reflexive_iso; constructor : typeclass_instances.


End Interface.