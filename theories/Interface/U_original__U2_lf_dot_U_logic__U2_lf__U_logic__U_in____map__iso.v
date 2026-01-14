From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_In__map : forall (x x0 : Type) (x1 : x -> x0) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list x) (x3 : x),
  imported_Original_LF__DOT__Logic_LF_Logic_In x3 x2 -> imported_Original_LF__DOT__Logic_LF_Logic_In (x1 x3) (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x4 : x => x1 x4) x2).
Parameter Original_LF__DOT__Logic_LF_Logic_In__map_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x1 -> x3) (x6 : x2 -> x4) (hx1 : forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8))
    (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8) (x9 : x1) 
    (x10 : x2) (hx3 : rel_iso hx x9 x10) (x11 : Original.LF_DOT_Logic.LF.Logic.In x9 x7) (x12 : imported_Original_LF__DOT__Logic_LF_Logic_In x10 x8),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx3 hx2) x11 x12 ->
  rel_iso
    (Original_LF__DOT__Logic_LF_Logic_In_iso (hx1 x9 x10 hx3)
       (Original_LF__DOT__Poly_LF_Poly_map_iso x5 (fun x : x2 => x6 x) (fun (x13 : x1) (x14 : x2) (hx5 : rel_iso hx x13 x14) => hx1 x13 x14 hx5) hx2))
    (Original.LF_DOT_Logic.LF.Logic.In_map x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__Logic_LF_Logic_In__map x6 x12).
Existing Instance Original_LF__DOT__Logic_LF_Logic_In__map_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.In_map ?x) => unify x Original_LF__DOT__Logic_LF_Logic_In__map_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.In_map imported_Original_LF__DOT__Logic_LF_Logic_In__map ?x) => unify x Original_LF__DOT__Logic_LF_Logic_In__map_iso; constructor : typeclass_instances.


End Interface.