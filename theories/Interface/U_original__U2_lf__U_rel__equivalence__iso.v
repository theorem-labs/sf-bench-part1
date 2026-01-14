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

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Args <+ Interface.U_original__U2_lf__U_rel__relation__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_equivalence : forall x : Type, (x -> x -> SProp) -> SProp.
Parameter Original_LF_Rel_equivalence_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  Iso (Original.LF.Rel.equivalence x3) (imported_Original_LF_Rel_equivalence x4).
Existing Instance Original_LF_Rel_equivalence_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF.Rel.equivalence) ?x) => unify x Original_LF_Rel_equivalence_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF.Rel.equivalence) imported_Original_LF_Rel_equivalence ?x) => unify x Original_LF_Rel_equivalence_iso; constructor : typeclass_instances.


End Interface.