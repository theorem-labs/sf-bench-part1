From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U_false__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U_false__iso.

  Export Interface.U_original__U_false__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_Logic.LF.Logic.not := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U_false__iso.Args <+ Interface.U_original__U_false__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__Logic_LF_Logic_not : SProp -> SProp
  := fun x : SProp => x -> imported_Original_False.
Definition Original_LF__DOT__Logic_LF_Logic_not_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> Iso (Original.LF_DOT_Logic.LF.Logic.not x1) (imported_Original_LF__DOT__Logic_LF_Logic_not x2)
  := fun (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) => IsoArrow hx Original_False_iso.
Existing Instance Original_LF__DOT__Logic_LF_Logic_not_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not imported_Original_LF__DOT__Logic_LF_Logic_not ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not_iso; constructor : typeclass_instances.


End Interface.