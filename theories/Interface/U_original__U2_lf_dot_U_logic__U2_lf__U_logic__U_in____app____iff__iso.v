From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.iff__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.iff__iso Interface.or__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_In__app__iff : forall (x : Type) (x0 x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x) (x2 : x),
  imported_iff (imported_Original_LF__DOT__Logic_LF_Logic_In x2 (imported_Original_LF__DOT__Poly_LF_Poly_app x0 x1))
    (imported_or (imported_Original_LF__DOT__Logic_LF_Logic_In x2 x0) (imported_Original_LF__DOT__Logic_LF_Logic_In x2 x1)).
Parameter Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8),
  rel_iso
    {|
      to :=
        iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
          (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1));
      from :=
        from
          (iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
             (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1)));
      to_from :=
        fun
          x : imported_iff (imported_Original_LF__DOT__Logic_LF_Logic_In x8 (imported_Original_LF__DOT__Poly_LF_Poly_app x4 x6))
                (imported_or (imported_Original_LF__DOT__Logic_LF_Logic_In x8 x4) (imported_Original_LF__DOT__Logic_LF_Logic_In x8 x6)) =>
        to_from
          (iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
             (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1)))
          x;
      from_to :=
        fun x : Original.LF_DOT_Logic.LF.Logic.In x7 (Original.LF_DOT_Poly.LF.Poly.app x3 x5) <-> Original.LF_DOT_Logic.LF.Logic.In x7 x3 \/ Original.LF_DOT_Logic.LF.Logic.In x7 x5 =>
        seq_p_of_t
          (from_to
             (iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
                (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1)))
             x)
    |} (Original.LF_DOT_Logic.LF.Logic.In_app_iff x1 x3 x5 x7) (imported_Original_LF__DOT__Logic_LF_Logic_In__app__iff x4 x6 x8).
Existing Instance Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.In_app_iff ?x) => unify x Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.In_app_iff imported_Original_LF__DOT__Logic_LF_Logic_In__app__iff ?x) => unify x Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso; constructor : typeclass_instances.


End Interface.