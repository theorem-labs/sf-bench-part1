From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_leU_playground__le__iso Interface.U_s__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_leU_playground__le__iso Interface.U_s__iso Interface.or__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_leU_playground__le__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_leU_playground__le__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_le__inversion : forall x x0 : imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x x0 ->
  imported_or (imported_Corelib_Init_Logic_eq x x0)
    (imported_ex (fun H : imported_nat => imported_and (imported_Corelib_Init_Logic_eq x0 (imported_S H)) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x H))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso : forall (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : @rel_iso nat imported_nat nat_iso x3 x4)
    (x5 : Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 x3) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 x4),
  @rel_iso (Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 x4)
    (@relax_Iso_Ts_Ps (Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 x4)
       (@Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le_iso x1 x2 hx x3 x4 hx0))
    x5 x6 ->
  @rel_iso (x1 = x3 \/ (exists m' : nat, x3 = S m' /\ Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 m'))
    (imported_or (@imported_Corelib_Init_Logic_eq imported_nat x2 x4)
       (@imported_ex imported_nat
          (fun H : imported_nat => imported_and (@imported_Corelib_Init_Logic_eq imported_nat x4 (imported_S H)) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 H))))
    (@relax_Iso_Ts_Ps (x1 = x3 \/ (exists m' : nat, x3 = S m' /\ Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 m'))
       (imported_or (@imported_Corelib_Init_Logic_eq imported_nat x2 x4)
          (@imported_ex imported_nat
             (fun H : imported_nat => imported_and (@imported_Corelib_Init_Logic_eq imported_nat x4 (imported_S H)) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 H))))
       (@or_iso (x1 = x3) (@imported_Corelib_Init_Logic_eq imported_nat x2 x4) (@Corelib_Init_Logic_eq_iso nat imported_nat nat_iso x1 x2 hx x3 x4 hx0)
          (exists m' : nat, x3 = S m' /\ Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 m')
          (@imported_ex imported_nat
             (fun H : imported_nat => imported_and (@imported_Corelib_Init_Logic_eq imported_nat x4 (imported_S H)) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 H)))
          (@ex_iso nat imported_nat nat_iso (fun m' : nat => x3 = S m' /\ Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 m')
             (fun H : imported_nat => imported_and (@imported_Corelib_Init_Logic_eq imported_nat x4 (imported_S H)) (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 H))
             (fun (x7 : nat) (x8 : imported_nat) (hx2 : @rel_iso nat imported_nat nat_iso x7 x8) =>
              @and_iso (x3 = S x7) (@imported_Corelib_Init_Logic_eq imported_nat x4 (imported_S x8))
                (@Corelib_Init_Logic_eq_iso nat imported_nat nat_iso x3 x4 hx0 (S x7) (imported_S x8) (@S_iso x7 x8 hx2)) (Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le x1 x7)
                (imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le x2 x8) (@Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le_iso x1 x2 hx x7 x8 hx2)))))
    (Original.LF_DOT_IndProp.LF.IndProp.le_inversion x1 x3 x5) (@imported_Original_LF__DOT__IndProp_LF_IndProp_le__inversion x2 x4 x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.le_inversion ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.le_inversion imported_Original_LF__DOT__IndProp_LF_IndProp_le__inversion ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_le__inversion_iso; constructor : typeclass_instances.


End Interface.