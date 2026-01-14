From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____curry__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____uncurry__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____curry__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____uncurry__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____curry__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____uncurry__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____curry__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__prod____uncurry__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry : forall (x x0 x1 : Type) (x2 : x -> x0 -> x1) (x3 : x) (x4 : x0),
  imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry
       (fun x5 : imported_Original_LF__DOT__Poly_LF_Poly_prod x x0 => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_prod__uncurry (fun (x6 : x) (x7 : x0) => x2 x6 x7) x5) x3 x4)
    (x2 x3 x4).
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 x6 : Type) (hx1 : Iso x5 x6) (x7 : x1 -> x3 -> x5) (x8 : x2 -> x4 -> x6)
    (hx2 : forall (x9 : x1) (x10 : x2), rel_iso hx x9 x10 -> forall (x11 : x3) (x12 : x4), rel_iso hx0 x11 x12 -> rel_iso hx1 (x7 x9 x11) (x8 x10 x12)) (x9 : x1) (x10 : x2) 
    (hx3 : rel_iso hx x9 x10) (x11 : x3) (x12 : x4) (hx4 : rel_iso hx0 x11 x12),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (unwrap_sprop
          (Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry_iso hx1 (Original.LF_DOT_Poly.LF.Poly.Exercises.prod_uncurry x7)
             (fun x : imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4 => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_prod__uncurry (fun (x0 : x2) (x13 : x4) => x8 x0 x13) x)
             (fun (x13 : Original.LF_DOT_Poly.LF.Poly.prod x1 x3) (x14 : imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4) (hx5 : rel_iso (Original_LF__DOT__Poly_LF_Poly_prod_iso hx hx0) x13 x14) =>
              {|
                unwrap_sprop :=
                  unwrap_sprop
                    (Original_LF__DOT__Poly_LF_Poly_Exercises_prod__uncurry_iso hx1 x7 (fun (x : x2) (x0 : x4) => x8 x x0)
                       (fun (x15 : x1) (x16 : x2) (hx6 : rel_iso hx x15 x16) (x17 : x3) (x18 : x4) (hx7 : rel_iso hx0 x17 x18) => {| unwrap_sprop := hx2 x15 x16 hx6 x17 x18 hx7 |}) hx5)
              |})
             hx3 hx4))
       (hx2 x9 x10 hx3 x11 x12 hx4))
    (Original.LF_DOT_Poly.LF.Poly.Exercises.uncurry_curry x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry x8 x10 x12).
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.uncurry_curry ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.uncurry_curry imported_Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_uncurry__curry_iso; constructor : typeclass_instances.


End Interface.