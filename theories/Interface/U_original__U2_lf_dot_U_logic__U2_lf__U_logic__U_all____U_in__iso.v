From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.iff__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_all__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_All__In : forall (x : Type) (x0 : x -> SProp) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_iff (forall a' : x, imported_Original_LF__DOT__Logic_LF_Logic_In a' x1 -> x0 a') (imported_Original_LF__DOT__Logic_LF_Logic_All (fun H : x => x0 H) x1).
Parameter Original_LF__DOT__Logic_LF_Logic_All__In_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp) (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1)
    (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6),
  rel_iso
    (relax_Iso_Ts_Ps
       (iff_iso
          (IsoForall (fun a : x1 => Original.LF_DOT_Logic.LF.Logic.In a x5 -> x3 a) (fun a' : x2 => imported_Original_LF__DOT__Logic_LF_Logic_In a' x6 -> x4 a')
             (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => IsoArrow (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1) (hx0 x7 x8 hx2)))
          (Original_LF__DOT__Logic_LF_Logic_All_iso x3 (fun H : x2 => x4 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1)))
    (Original.LF_DOT_Logic.LF.Logic.All_In x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_All__In x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_All__In_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.All_In ?x) => unify x Original_LF__DOT__Logic_LF_Logic_All__In_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.All_In imported_Original_LF__DOT__Logic_LF_Logic_All__In ?x) => unify x Original_LF__DOT__Logic_LF_Logic_All__In_iso; constructor : typeclass_instances.


End Interface.