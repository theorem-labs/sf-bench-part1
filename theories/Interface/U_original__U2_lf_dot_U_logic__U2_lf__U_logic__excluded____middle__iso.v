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

#[export] Instance: MustUnfold Original.LF_DOT_Logic.LF.Logic.excluded_middle := {}.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__Logic_LF_Logic_excluded__middle : SProp
  := forall a' : SProp, imported_or a' (a' -> imported_False).
Definition Original_LF__DOT__Logic_LF_Logic_excluded__middle_iso : Iso Original.LF_DOT_Logic.LF.Logic.excluded_middle imported_Original_LF__DOT__Logic_LF_Logic_excluded__middle
  := IsoForall (fun a : Prop => a \/ ~ a) (fun x2 : SProp => imported_or x2 (x2 -> imported_False))
    (fun (x1 : Prop) (x2 : SProp) (hx : rel_iso iso_Prop_SProp x1 x2) =>
     relax_Iso_Ts_Ps (or_iso (iso_of_rel_iso_iso_sort_PropSProp_T hx) (IsoArrow (iso_of_rel_iso_iso_sort_PropSProp_T hx) False_iso))).
Existing Instance Original_LF__DOT__Logic_LF_Logic_excluded__middle_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.excluded_middle ?x) => unify x Original_LF__DOT__Logic_LF_Logic_excluded__middle_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.excluded_middle imported_Original_LF__DOT__Logic_LF_Logic_excluded__middle ?x) => unify x Original_LF__DOT__Logic_LF_Logic_excluded__middle_iso; constructor : typeclass_instances.


End Interface.