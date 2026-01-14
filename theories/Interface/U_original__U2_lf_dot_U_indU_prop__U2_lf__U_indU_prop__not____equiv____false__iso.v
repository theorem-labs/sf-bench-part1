From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U_false__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U_false__iso Interface.iff__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U_false__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U_false__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false : forall x : SProp, (x -> imported_False) -> imported_iff x imported_Original_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : ~ x1) (x4 : x2 -> imported_False),
  (forall (x5 : x1) (x6 : x2),
   rel_iso hx x5 x6 ->
   rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |} (x3 x5) (x4 x6)) ->
  rel_iso
    {|
      to := iff_iso hx Original_False_iso;
      from := from (iff_iso hx Original_False_iso);
      to_from := fun x : imported_iff x2 imported_Original_False => to_from (iff_iso hx Original_False_iso) x;
      from_to := fun x : x1 <-> Original.False => seq_p_of_t (from_to (iff_iso hx Original_False_iso) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.not_equiv_false x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.not_equiv_false ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.not_equiv_false imported_Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false_iso; constructor : typeclass_instances.


End Interface.