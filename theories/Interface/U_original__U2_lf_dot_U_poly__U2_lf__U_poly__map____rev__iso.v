From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_map__rev : forall (x x0 : Type) (x1 : x -> x0) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x3 : x => x1 x3) (imported_Original_LF__DOT__Poly_LF_Poly_rev x2))
    (imported_Original_LF__DOT__Poly_LF_Poly_rev (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x3 : x => x1 x3) x2)).
Parameter Original_LF__DOT__Poly_LF_Poly_map__rev_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x1 -> x3) (x6 : x2 -> x4) (hx1 : forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8))
    (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_map_iso x5 (fun x : x2 => x6 x) (fun (x9 : x1) (x10 : x2) (hx3 : rel_iso hx x9 x10) => hx1 x9 x10 hx3) (Original_LF__DOT__Poly_LF_Poly_rev_iso hx2))
       (Original_LF__DOT__Poly_LF_Poly_rev_iso (Original_LF__DOT__Poly_LF_Poly_map_iso x5 (fun x : x2 => x6 x) (fun (x9 : x1) (x10 : x2) (hx3 : rel_iso hx x9 x10) => hx1 x9 x10 hx3) hx2)))
    (Original.LF_DOT_Poly.LF.Poly.map_rev x1 x3 x5 x7) (imported_Original_LF__DOT__Poly_LF_Poly_map__rev x6 x8).
Existing Instance Original_LF__DOT__Poly_LF_Poly_map__rev_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.map_rev ?x) => unify x Original_LF__DOT__Poly_LF_Poly_map__rev_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.map_rev imported_Original_LF__DOT__Poly_LF_Poly_map__rev ?x) => unify x Original_LF__DOT__Poly_LF_Poly_map__rev_iso; constructor : typeclass_instances.


End Interface.