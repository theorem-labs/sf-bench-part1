From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__apply____late____policy__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__ltb__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__apply____late____policy__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__ltb__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__apply____late____policy__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__ltb__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__apply____late____policy__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__ltb__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_grade__lowered__once : forall (x : imported_nat) (x0 : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_ltb x (imported_S (imported_S (imported_S (iterate1 imported_S 6 imported_0)))))
    imported_Original_LF__DOT__Basics_LF_Basics_false ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_ltb x (imported_S (imported_S (imported_S (iterate1 imported_S 14 imported_0)))))
    imported_Original_LF__DOT__Basics_LF_Basics_true ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy x x0) (imported_Original_LF__DOT__Basics_LF_Basics_lower__grade x0).
Parameter Original_LF__DOT__Basics_LF_Basics_grade__lowered__once_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_Basics.LF.Basics.grade) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_grade)
    (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso x3 x4) (x5 : Original.LF_DOT_Basics.LF.Basics.ltb x1 9 = Original.LF_DOT_Basics.LF.Basics.false)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_ltb x2 (imported_S (imported_S (imported_S (iterate1 imported_S 6 imported_0)))))
            imported_Original_LF__DOT__Basics_LF_Basics_false),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_ltb_iso hx (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 6 0 imported_0 _0_iso)))))
       Original_LF__DOT__Basics_LF_Basics_false_iso)
    x5 x6 ->
  forall (x7 : Original.LF_DOT_Basics.LF.Basics.ltb x1 17 = Original.LF_DOT_Basics.LF.Basics.true)
    (x8 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_ltb x2 (imported_S (imported_S (imported_S (iterate1 imported_S 14 imported_0)))))
            imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_ltb_iso hx (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 14 0 imported_0 _0_iso)))))
       Original_LF__DOT__Basics_LF_Basics_true_iso)
    x7 x8 ->
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_lower__grade_iso hx0))
    (Original.LF_DOT_Basics.LF.Basics.grade_lowered_once x1 x3 x5 x7) (imported_Original_LF__DOT__Basics_LF_Basics_grade__lowered__once x4 x6 x8).
Existing Instance Original_LF__DOT__Basics_LF_Basics_grade__lowered__once_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.grade_lowered_once ?x) => unify x Original_LF__DOT__Basics_LF_Basics_grade__lowered__once_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.grade_lowered_once imported_Original_LF__DOT__Basics_LF_Basics_grade__lowered__once ?x) => unify x Original_LF__DOT__Basics_LF_Basics_grade__lowered__once_iso; constructor : typeclass_instances.


End Interface.