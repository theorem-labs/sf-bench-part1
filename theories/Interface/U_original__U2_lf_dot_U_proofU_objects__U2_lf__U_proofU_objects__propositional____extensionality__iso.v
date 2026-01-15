From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_ProofObjects.LF.ProofObjects.propositional_extensionality := {}.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality : SProp
  := forall a' a'0 : SProp, imported_iff a' a'0 -> imported_Corelib_Init_Logic_eq a' a'0.
Definition Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.propositional_extensionality imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality
  := IsoForall (fun a : Prop => forall Q : Prop, a <-> Q -> a = Q) (fun x2 : SProp => forall a' : SProp, imported_iff x2 a' -> imported_Corelib_Init_Logic_eq x2 a')
    (fun (x1 : Prop) (x2 : SProp) (hx : rel_iso iso_Prop_SProp x1 x2) =>
     IsoForall (fun a : Prop => x1 <-> a -> x1 = a) (fun x4 : SProp => imported_iff x2 x4 -> imported_Corelib_Init_Logic_eq x2 x4)
       (fun (x3 : Prop) (x4 : SProp) (hx0 : rel_iso iso_Prop_SProp x3 x4) =>
        IsoArrow (iff_iso (iso_of_rel_iso_iso_sort_PropSProp_T hx) (iso_of_rel_iso_iso_sort_PropSProp_T hx0)) (relax_Iso_Ts_Ps (Corelib_Init_Logic_eq_iso hx hx0)))).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.propositional_extensionality ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.propositional_extensionality imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality_iso; constructor : typeclass_instances.


End Interface.