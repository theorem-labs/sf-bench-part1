From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso Interface.gt__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso Interface.gt__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.gt__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.gt__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1 : forall x : imported_nat, imported_gt x imported_0 -> imported_gt (imported_Nat_mul x (imported_S (imported_S imported_0))) x.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : x1 > 0) (x4 : imported_gt x2 imported_0),
  rel_iso (gt_iso hx _0_iso) x3 x4 ->
  rel_iso (gt_iso (Nat_mul_iso hx (S_iso (S_iso _0_iso))) hx) (Original.LF_DOT_AltAuto.LF.AltAuto.lia_succeed1 x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1 x4).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.lia_succeed1 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.lia_succeed1 imported_Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1_iso; constructor : typeclass_instances.


End Interface.