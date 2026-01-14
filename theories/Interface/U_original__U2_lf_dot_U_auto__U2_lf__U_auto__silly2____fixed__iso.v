From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.ex__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.ex__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_silly2__fixed : forall (x : imported_nat -> imported_nat -> SProp) (x0 : imported_nat -> SProp),
  imported_ex (fun x1 : imported_nat => x (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) x1) ->
  (forall x1 x2 : imported_nat, x x1 x2 -> x0 x1) -> x0 (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))).
Parameter Original_LF__DOT__Auto_LF_Auto_silly2__fixed_iso : forall (x1 : nat -> nat -> Prop) (x2 : imported_nat -> imported_nat -> SProp)
    (hx : forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (x1 x3 x5) (x2 x4 x6)) (x3 : nat -> Prop)
    (x4 : imported_nat -> SProp) (hx0 : forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (x3 x5) (x4 x6)) (x5 : exists y : nat, x1 42 y)
    (x6 : imported_ex (fun x : imported_nat => x2 (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) x)),
  rel_iso
    (ex_iso (fun y : nat => x1 42 y) (fun x : imported_nat => x2 (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) x)
       (fun (x7 : nat) (x8 : imported_nat) (hx1 : rel_iso nat_iso x7 x8) =>
        hx 42 (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 39 0 imported_0 _0_iso)))) x7 x8 hx1))
    x5 x6 ->
  forall (x7 : forall x y : nat, x1 x y -> x3 x) (x8 : forall x x0 : imported_nat, x2 x x0 -> x4 x),
  (forall (x9 : nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) (x11 : nat) (x12 : imported_nat) (hx3 : rel_iso nat_iso x11 x12) (x13 : x1 x9 x11) (x14 : x2 x10 x12),
   rel_iso (hx x9 x10 hx2 x11 x12 hx3) x13 x14 -> rel_iso (hx0 x9 x10 hx2) (x7 x9 x11 x13) (x8 x10 x12 x14)) ->
  rel_iso (hx0 42 (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 39 0 imported_0 _0_iso)))))
    (Original.LF_DOT_Auto.LF.Auto.silly2_fixed x1 x3 x5 x7) (imported_Original_LF__DOT__Auto_LF_Auto_silly2__fixed x2 x4 x6 x8).
Existing Instance Original_LF__DOT__Auto_LF_Auto_silly2__fixed_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.silly2_fixed ?x) => unify x Original_LF__DOT__Auto_LF_Auto_silly2__fixed_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.silly2_fixed imported_Original_LF__DOT__Auto_LF_Auto_silly2__fixed ?x) => unify x Original_LF__DOT__Auto_LF_Auto_silly2__fixed_iso; constructor : typeclass_instances.


End Interface.