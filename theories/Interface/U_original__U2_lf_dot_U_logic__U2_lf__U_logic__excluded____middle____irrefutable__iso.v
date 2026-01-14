From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.or__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable : forall x : SProp, (imported_or x (x -> imported_False) -> imported_False) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1 \/ (x1 -> False) -> False) (x4 : imported_or x2 (x2 -> imported_False) -> imported_False),
  (forall (x5 : x1 \/ (x1 -> False)) (x6 : imported_or x2 (x2 -> imported_False)),
   rel_iso
     {|
       to := or_iso hx (IsoArrow hx False_iso);
       from := from (or_iso hx (IsoArrow hx False_iso));
       to_from := fun x : imported_or x2 (x2 -> imported_False) => to_from (or_iso hx (IsoArrow hx False_iso)) x;
       from_to := fun x : x1 \/ (x1 -> False) => seq_p_of_t (from_to (or_iso hx (IsoArrow hx False_iso)) x)
     |} x5 x6 ->
   rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |} (x3 x5) (x4 x6)) ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.excluded_middle_irrefutable x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.excluded_middle_irrefutable ?x) => unify x Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.excluded_middle_irrefutable imported_Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable ?x) => unify x Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable_iso; constructor : typeclass_instances.


End Interface.