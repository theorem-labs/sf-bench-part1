From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__forallb__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__forallb__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__forallb__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__forallb__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_forallb__true__iff : forall (x : Type) (x0 : x -> imported_Original_LF__DOT__Basics_LF_Basics_bool) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Logic_LF_Logic_forallb (fun H : x => x0 H) x1) imported_Original_LF__DOT__Basics_LF_Basics_true)
    (imported_Original_LF__DOT__Logic_LF_Logic_All (fun H : x => imported_Corelib_Init_Logic_eq (x0 H) imported_Original_LF__DOT__Basics_LF_Basics_true) x1).
Parameter Original_LF__DOT__Logic_LF_Logic_forallb__true__iff_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Original.LF_DOT_Basics.LF.Basics.bool) (x4 : x2 -> imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x3 x5) (x4 x6)) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1)
    (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6),
  rel_iso
    {|
      to :=
        iff_iso
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Logic_LF_Logic_forallb_iso x3 (fun H : x2 => x4 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1)
             Original_LF__DOT__Basics_LF_Basics_true_iso)
          (Original_LF__DOT__Logic_LF_Logic_All_iso (fun x : x1 => x3 x = Original.LF_DOT_Basics.LF.Basics.true)
             (fun H : x2 => imported_Corelib_Init_Logic_eq (x4 H) imported_Original_LF__DOT__Basics_LF_Basics_true)
             (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => Corelib_Init_Logic_eq_iso (hx0 x7 x8 hx2) Original_LF__DOT__Basics_LF_Basics_true_iso) hx1);
      from :=
        from
          (iff_iso
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Logic_LF_Logic_forallb_iso x3 (fun H : x2 => x4 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1)
                Original_LF__DOT__Basics_LF_Basics_true_iso)
             (Original_LF__DOT__Logic_LF_Logic_All_iso (fun x : x1 => x3 x = Original.LF_DOT_Basics.LF.Basics.true)
                (fun H : x2 => imported_Corelib_Init_Logic_eq (x4 H) imported_Original_LF__DOT__Basics_LF_Basics_true)
                (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => Corelib_Init_Logic_eq_iso (hx0 x7 x8 hx2) Original_LF__DOT__Basics_LF_Basics_true_iso) hx1));
      to_from :=
        fun
          x : imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Logic_LF_Logic_forallb (fun H : x2 => x4 H) x6) imported_Original_LF__DOT__Basics_LF_Basics_true)
                (imported_Original_LF__DOT__Logic_LF_Logic_All (fun H : x2 => imported_Corelib_Init_Logic_eq (x4 H) imported_Original_LF__DOT__Basics_LF_Basics_true) x6) =>
        to_from
          (iff_iso
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Logic_LF_Logic_forallb_iso x3 (fun H : x2 => x4 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1)
                Original_LF__DOT__Basics_LF_Basics_true_iso)
             (Original_LF__DOT__Logic_LF_Logic_All_iso (fun x0 : x1 => x3 x0 = Original.LF_DOT_Basics.LF.Basics.true)
                (fun H : x2 => imported_Corelib_Init_Logic_eq (x4 H) imported_Original_LF__DOT__Basics_LF_Basics_true)
                (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => Corelib_Init_Logic_eq_iso (hx0 x7 x8 hx2) Original_LF__DOT__Basics_LF_Basics_true_iso) hx1))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Logic.LF.Logic.forallb x3 x5 = Original.LF_DOT_Basics.LF.Basics.true <->
              Original.LF_DOT_Logic.LF.Logic.All (fun x : x1 => x3 x = Original.LF_DOT_Basics.LF.Basics.true) x5 =>
        seq_p_of_t
          (from_to
             (iff_iso
                (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Logic_LF_Logic_forallb_iso x3 (fun H : x2 => x4 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1)
                   Original_LF__DOT__Basics_LF_Basics_true_iso)
                (Original_LF__DOT__Logic_LF_Logic_All_iso (fun x0 : x1 => x3 x0 = Original.LF_DOT_Basics.LF.Basics.true)
                   (fun H : x2 => imported_Corelib_Init_Logic_eq (x4 H) imported_Original_LF__DOT__Basics_LF_Basics_true)
                   (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => Corelib_Init_Logic_eq_iso (hx0 x7 x8 hx2) Original_LF__DOT__Basics_LF_Basics_true_iso) hx1))
             x)
    |} (Original.LF_DOT_Logic.LF.Logic.forallb_true_iff x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_forallb__true__iff x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_forallb__true__iff_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.forallb_true_iff ?x) => unify x Original_LF__DOT__Logic_LF_Logic_forallb__true__iff_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.forallb_true_iff imported_Original_LF__DOT__Logic_LF_Logic_forallb__true__iff ?x) => unify x Original_LF__DOT__Logic_LF_Logic_forallb__true__iff_iso; constructor : typeclass_instances.


End Interface.