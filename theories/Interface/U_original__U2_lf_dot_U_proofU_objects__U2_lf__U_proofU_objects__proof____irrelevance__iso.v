From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_ProofObjects.LF.ProofObjects.proof_irrelevance := {}.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance : SProp
  := forall (a' : SProp) (a'0 a'1 : a'), imported_Corelib_Init_Logic_eq_Prop a'0 a'1.
Definition Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.proof_irrelevance imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance
  := IsoForall (fun a : Prop => forall pf1 pf2 : a, pf1 = pf2) (fun x2 : SProp => forall a' a'0 : x2, imported_Corelib_Init_Logic_eq_Prop a' a'0)
    (fun (x1 : Prop) (x2 : SProp) (hx : rel_iso iso_Prop_SProp x1 x2) =>
     IsoForall (fun a : x1 => forall pf2 : x1, a = pf2) (fun x4 : x2 => forall a' : x2, imported_Corelib_Init_Logic_eq_Prop x4 a')
       (fun (x3 : x1) (x4 : x2) (hx0 : rel_iso (iso_of_rel_iso_iso_sort_PropSProp_T hx) x3 x4) =>
        IsoForall (Corelib.Init.Logic.eq x3) (fun x6 : x2 => imported_Corelib_Init_Logic_eq_Prop x4 x6)
          (fun (x5 : x1) (x6 : x2) (hx1 : rel_iso (iso_of_rel_iso_iso_sort_PropSProp_T hx) x5 x6) => Corelib_Init_Logic_eq_iso_Prop hx0 hx1))).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.proof_irrelevance ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.proof_irrelevance imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance_iso; constructor : typeclass_instances.


End Interface.