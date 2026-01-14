From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool____rec__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool____rec__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso Interface.U_s__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool____rec__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool____rec__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.Interface <+ Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_even__double__conv : forall x : imported_nat,
  imported_ex
    (fun H : imported_nat =>
     imported_Corelib_Init_Logic_eq x
       (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat) (imported_Original_LF__DOT__Induction_LF_Induction_double H)
          (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double H)) (imported_Original_LF__DOT__Basics_LF_Basics_even x))).
Parameter Original_LF__DOT__Logic_LF_Logic_even__double__conv_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to :=
        ex_iso (fun k : nat => x1 = (if Original.LF_DOT_Basics.LF.Basics.even x1 then Original.LF_DOT_Induction.LF.Induction.double k else S (Original.LF_DOT_Induction.LF.Induction.double k)))
          (fun H : imported_nat =>
           imported_Corelib_Init_Logic_eq x2
             (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                (imported_Original_LF__DOT__Induction_LF_Induction_double H) (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double H))
                (imported_Original_LF__DOT__Basics_LF_Basics_even x2)))
          (fun (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) =>
           Corelib_Init_Logic_eq_iso hx
             (unwrap_sprop
                (Original_LF__DOT__Basics_LF_Basics_bool__rec_iso (fun _ : Original.LF_DOT_Basics.LF.Basics.bool => nat) (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                   (fun (x5 : Original.LF_DOT_Basics.LF.Basics.bool) (x6 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (_ : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x5 x6) => nat_iso)
                   (Original.LF_DOT_Induction.LF.Induction.double x3) (imported_Original_LF__DOT__Induction_LF_Induction_double x4)
                   {| unwrap_sprop := Original_LF__DOT__Induction_LF_Induction_double_iso hx0 |} (S (Original.LF_DOT_Induction.LF.Induction.double x3))
                   (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double x4)) {| unwrap_sprop := S_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx0) |}
                   (Original_LF__DOT__Basics_LF_Basics_even_iso hx))));
      from :=
        from
          (ex_iso (fun k : nat => x1 = (if Original.LF_DOT_Basics.LF.Basics.even x1 then Original.LF_DOT_Induction.LF.Induction.double k else S (Original.LF_DOT_Induction.LF.Induction.double k)))
             (fun H : imported_nat =>
              imported_Corelib_Init_Logic_eq x2
                (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                   (imported_Original_LF__DOT__Induction_LF_Induction_double H) (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double H))
                   (imported_Original_LF__DOT__Basics_LF_Basics_even x2)))
             (fun (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) =>
              Corelib_Init_Logic_eq_iso hx
                (unwrap_sprop
                   (Original_LF__DOT__Basics_LF_Basics_bool__rec_iso (fun _ : Original.LF_DOT_Basics.LF.Basics.bool => nat) (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                      (fun (x5 : Original.LF_DOT_Basics.LF.Basics.bool) (x6 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (_ : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x5 x6) =>
                       nat_iso)
                      (Original.LF_DOT_Induction.LF.Induction.double x3) (imported_Original_LF__DOT__Induction_LF_Induction_double x4)
                      {| unwrap_sprop := Original_LF__DOT__Induction_LF_Induction_double_iso hx0 |} (S (Original.LF_DOT_Induction.LF.Induction.double x3))
                      (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double x4)) {| unwrap_sprop := S_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx0) |}
                      (Original_LF__DOT__Basics_LF_Basics_even_iso hx)))));
      to_from :=
        fun
          x : imported_ex
                (fun H : imported_nat =>
                 imported_Corelib_Init_Logic_eq x2
                   (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                      (imported_Original_LF__DOT__Induction_LF_Induction_double H) (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double H))
                      (imported_Original_LF__DOT__Basics_LF_Basics_even x2))) =>
        to_from
          (ex_iso (fun k : nat => x1 = (if Original.LF_DOT_Basics.LF.Basics.even x1 then Original.LF_DOT_Induction.LF.Induction.double k else S (Original.LF_DOT_Induction.LF.Induction.double k)))
             (fun H : imported_nat =>
              imported_Corelib_Init_Logic_eq x2
                (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                   (imported_Original_LF__DOT__Induction_LF_Induction_double H) (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double H))
                   (imported_Original_LF__DOT__Basics_LF_Basics_even x2)))
             (fun (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) =>
              Corelib_Init_Logic_eq_iso hx
                (unwrap_sprop
                   (Original_LF__DOT__Basics_LF_Basics_bool__rec_iso (fun _ : Original.LF_DOT_Basics.LF.Basics.bool => nat) (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                      (fun (x5 : Original.LF_DOT_Basics.LF.Basics.bool) (x6 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (_ : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x5 x6) =>
                       nat_iso)
                      (Original.LF_DOT_Induction.LF.Induction.double x3) (imported_Original_LF__DOT__Induction_LF_Induction_double x4)
                      {| unwrap_sprop := Original_LF__DOT__Induction_LF_Induction_double_iso hx0 |} (S (Original.LF_DOT_Induction.LF.Induction.double x3))
                      (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double x4)) {| unwrap_sprop := S_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx0) |}
                      (Original_LF__DOT__Basics_LF_Basics_even_iso hx)))))
          x;
      from_to :=
        fun x : exists y : nat, x1 = (if Original.LF_DOT_Basics.LF.Basics.even x1 then Original.LF_DOT_Induction.LF.Induction.double y else S (Original.LF_DOT_Induction.LF.Induction.double y)) =>
        seq_p_of_t
          (from_to
             (ex_iso (fun k : nat => x1 = (if Original.LF_DOT_Basics.LF.Basics.even x1 then Original.LF_DOT_Induction.LF.Induction.double k else S (Original.LF_DOT_Induction.LF.Induction.double k)))
                (fun H : imported_nat =>
                 imported_Corelib_Init_Logic_eq x2
                   (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                      (imported_Original_LF__DOT__Induction_LF_Induction_double H) (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double H))
                      (imported_Original_LF__DOT__Basics_LF_Basics_even x2)))
                (fun (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) =>
                 Corelib_Init_Logic_eq_iso hx
                   (unwrap_sprop
                      (Original_LF__DOT__Basics_LF_Basics_bool__rec_iso (fun _ : Original.LF_DOT_Basics.LF.Basics.bool => nat)
                         (fun _ : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_nat)
                         (fun (x5 : Original.LF_DOT_Basics.LF.Basics.bool) (x6 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (_ : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x5 x6) =>
                          nat_iso)
                         (Original.LF_DOT_Induction.LF.Induction.double x3) (imported_Original_LF__DOT__Induction_LF_Induction_double x4)
                         {| unwrap_sprop := Original_LF__DOT__Induction_LF_Induction_double_iso hx0 |} (S (Original.LF_DOT_Induction.LF.Induction.double x3))
                         (imported_S (imported_Original_LF__DOT__Induction_LF_Induction_double x4)) {| unwrap_sprop := S_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx0) |}
                         (Original_LF__DOT__Basics_LF_Basics_even_iso hx)))))
             x)
    |} (Original.LF_DOT_Logic.LF.Logic.even_double_conv x1) (imported_Original_LF__DOT__Logic_LF_Logic_even__double__conv x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_even__double__conv_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_double_conv ?x) => unify x Original_LF__DOT__Logic_LF_Logic_even__double__conv_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_double_conv imported_Original_LF__DOT__Logic_LF_Logic_even__double__conv ?x) => unify x Original_LF__DOT__Logic_LF_Logic_even__double__conv_iso; constructor : typeclass_instances.


End Interface.