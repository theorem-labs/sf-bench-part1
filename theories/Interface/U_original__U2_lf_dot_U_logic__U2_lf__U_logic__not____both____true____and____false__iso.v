From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.and__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.and__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.and__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.and__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false : forall x : SProp, imported_and x (x -> imported_False) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1 /\ (x1 -> False)) (x4 : imported_and x2 (x2 -> imported_False)),
  rel_iso
    {|
      to := and_iso hx (IsoArrow hx False_iso);
      from := from (and_iso hx (IsoArrow hx False_iso));
      to_from := fun x : imported_and x2 (x2 -> imported_False) => to_from (and_iso hx (IsoArrow hx False_iso)) x;
      from_to := fun x : x1 /\ (x1 -> False) => seq_p_of_t (from_to (and_iso hx (IsoArrow hx False_iso)) x)
    |} x3 x4 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.not_both_true_and_false x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_both_true_and_false ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_both_true_and_false imported_Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false_iso; constructor : typeclass_instances.


End Interface.