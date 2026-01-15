From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_s__iso Interface.__0__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_s__iso Interface.__0__iso Interface.or__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_ev__inversion : forall x : imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x ->
  imported_or (imported_Corelib_Init_Logic_eq x imported_0)
    (imported_ex (fun H : imported_nat => imported_and (imported_Corelib_Init_Logic_eq x (imported_S (imported_S H))) (imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev H))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_ev__inversion_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x1)
    (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x2),
  rel_iso (relax_Iso_Ts_Ps (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx)) x3 x4 ->
  rel_iso
    (relax_Iso_Ts_Ps
       (or_iso (Corelib_Init_Logic_eq_iso hx _0_iso)
          (ex_iso (fun n' : nat => x1 = S (S n') /\ Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev n')
             (fun H : imported_nat => imported_and (imported_Corelib_Init_Logic_eq x2 (imported_S (imported_S H))) (imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev H))
             (fun (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) =>
              and_iso (Corelib_Init_Logic_eq_iso hx (S_iso (S_iso hx1))) (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx1)))))
    (Original.LF_DOT_IndProp.LF.IndProp.ev_inversion x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev__inversion x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_ev__inversion_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev_inversion ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev__inversion_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev_inversion imported_Original_LF__DOT__IndProp_LF_IndProp_ev__inversion ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev__inversion_iso; constructor : typeclass_instances.


End Interface.