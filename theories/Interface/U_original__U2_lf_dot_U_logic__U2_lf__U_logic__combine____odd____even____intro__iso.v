From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__combine____odd____even__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__combine____odd____even__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__combine____odd____even__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__combine____odd____even__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro : forall (x x0 : imported_nat -> SProp) (x1 : imported_nat),
  (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd x1) imported_Original_LF__DOT__Basics_LF_Basics_true -> x x1) ->
  (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd x1) imported_Original_LF__DOT__Basics_LF_Basics_false -> x0 x1) ->
  imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even (fun x2 : imported_nat => x x2) (fun x2 : imported_nat => x0 x2) x1.
Parameter Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro_iso : forall (x1 : nat -> Prop) (x2 : imported_nat -> SProp) (hx : forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 x3) (x2 x4)) (x3 : nat -> Prop) (x4 : imported_nat -> SProp)
    (hx0 : forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (x3 x5) (x4 x6)) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Original.LF_DOT_Basics.LF.Basics.odd x5 = Original.LF_DOT_Basics.LF.Basics.true -> x1 x5)
    (x8 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd x6) imported_Original_LF__DOT__Basics_LF_Basics_true -> x2 x6),
  (forall (x9 : Original.LF_DOT_Basics.LF.Basics.odd x5 = Original.LF_DOT_Basics.LF.Basics.true)
     (x10 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd x6) imported_Original_LF__DOT__Basics_LF_Basics_true),
   rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso hx1) Original_LF__DOT__Basics_LF_Basics_true_iso) x9 x10 -> rel_iso (hx x5 x6 hx1) (x7 x9) (x8 x10)) ->
  forall (x9 : Original.LF_DOT_Basics.LF.Basics.odd x5 = Original.LF_DOT_Basics.LF.Basics.false -> x3 x5)
    (x10 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd x6) imported_Original_LF__DOT__Basics_LF_Basics_false -> x4 x6),
  (forall (x11 : Original.LF_DOT_Basics.LF.Basics.odd x5 = Original.LF_DOT_Basics.LF.Basics.false)
     (x12 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd x6) imported_Original_LF__DOT__Basics_LF_Basics_false),
   rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso hx1) Original_LF__DOT__Basics_LF_Basics_false_iso) x11 x12 -> rel_iso (hx0 x5 x6 hx1) (x9 x11) (x10 x12)) ->
  rel_iso
    (Original_LF__DOT__Logic_LF_Logic_combine__odd__even_iso x1 (fun x : imported_nat => x2 x) (fun (x11 : nat) (x12 : imported_nat) (hx4 : rel_iso nat_iso x11 x12) => hx x11 x12 hx4) x3
       (fun x : imported_nat => x4 x) (fun (x11 : nat) (x12 : imported_nat) (hx4 : rel_iso nat_iso x11 x12) => hx0 x11 x12 hx4) hx1)
    (Original.LF_DOT_Logic.LF.Logic.combine_odd_even_intro x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro x2 x4 x8 x10).
Existing Instance Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.combine_odd_even_intro ?x) => unify x Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.combine_odd_even_intro imported_Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro ?x) => unify x Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro_iso; constructor : typeclass_instances.


End Interface.