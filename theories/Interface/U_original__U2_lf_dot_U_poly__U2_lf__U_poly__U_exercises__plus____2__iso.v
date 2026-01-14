From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__plus__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__three__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__two__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__plus__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__three__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__two__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__plus__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__three__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__two__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__plus__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__three__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__two__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2 : imported_Corelib_Init_Logic_eq
    (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
     imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x3 : x => x0 x3) x1)
       (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x1 : x => x0 x1) x3) (fun x : x2 => x4 x) x6)
    (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
     imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x3 : x => x0 x3) x1)
       (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x1 : x => x0 x1) x3) (fun x : x2 => x4 x) x6).
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (IsoFun
          (fun (x1 x2 : Type) (hx : rel_iso iso_Sort x1 x2) =>
           IsoArrow (IsoArrow (iso_of_rel_iso_iso_sort hx) (iso_of_rel_iso_iso_sort hx)) (IsoArrow (iso_of_rel_iso_iso_sort hx) (iso_of_rel_iso_iso_sort hx)))
          (Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.two Original.LF_DOT_Poly.LF.Poly.Exercises.three)
          (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
           imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x3 : x => x0 x3) x1)
             (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x1 : x => x0 x1) x3) (fun x : x2 => x4 x) x6)
          (fun (x1 x2 : Type) (hx : rel_iso iso_Sort x1 x2) =>
           IsoFunND (Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.two Original.LF_DOT_Poly.LF.Poly.Exercises.three x1)
             (fun (x4 : x2 -> x2) (x6 : x2) =>
              imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x5 : x => x0 x5) x3)
                (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x5 : x => x0 x5) x3) (fun x : x2 => x4 x) x6)
             (fun (x3 : x1 -> x1) (x4 : x2 -> x2) (hx0 : rel_iso (IsoArrow (iso_of_rel_iso_iso_sort hx) (iso_of_rel_iso_iso_sort hx)) x3 x4) =>
              IsoFunND (Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.two Original.LF_DOT_Poly.LF.Poly.Exercises.three x1 x3)
                (fun x6 : x2 =>
                 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x5 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x7 : x => x0 x7) x5)
                   (fun (x : Type) (x0 : x -> x) (x5 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x7 : x => x0 x7) x5) (fun x : x2 => x4 x) x6)
                (fun (x5 : x1) (x6 : x2) (hx1 : rel_iso (iso_of_rel_iso_iso_sort hx) x5 x6) =>
                 Original_LF__DOT__Poly_LF_Poly_Exercises_plus_iso Original.LF_DOT_Poly.LF.Poly.Exercises.two
                   (fun (x : Type) (x0 : x -> x) (x7 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x8 : x => x0 x8) x7)
                   (fun (x7 x8 : Type) (hx2 : Iso x7 x8) (x9 : x7 -> x7) (x10 : x8 -> x8) (hx3 : forall (x11 : x7) (x12 : x8), rel_iso hx2 x11 x12 -> rel_iso hx2 (x9 x11) (x10 x12)) 
                      (x11 : x7) (x12 : x8) (hx4 : rel_iso hx2 x11 x12) =>
                    Original_LF__DOT__Poly_LF_Poly_Exercises_two_iso x9 (fun x : x8 => x10 x) (fun (x13 : x7) (x14 : x8) (hx5 : rel_iso hx2 x13 x14) => hx3 x13 x14 hx5) hx4)
                   Original.LF_DOT_Poly.LF.Poly.Exercises.three (fun (x : Type) (x0 : x -> x) (x7 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x8 : x => x0 x8) x7)
                   (fun (x7 x8 : Type) (hx2 : Iso x7 x8) (x9 : x7 -> x7) (x10 : x8 -> x8) (hx3 : forall (x11 : x7) (x12 : x8), rel_iso hx2 x11 x12 -> rel_iso hx2 (x9 x11) (x10 x12)) 
                      (x11 : x7) (x12 : x8) (hx4 : rel_iso hx2 x11 x12) =>
                    Original_LF__DOT__Poly_LF_Poly_Exercises_three_iso x9 (fun x : x8 => x10 x) (fun (x13 : x7) (x14 : x8) (hx5 : rel_iso hx2 x13 x14) => hx3 x13 x14 hx5) hx4)
                   x3 (fun x : x2 => x4 x) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso (iso_of_rel_iso_iso_sort hx) x7 x8) => IsoUnFunND hx0 hx2) hx1))))
       (IsoFun
          (fun (x1 x2 : Type) (hx : rel_iso iso_Sort x1 x2) =>
           IsoArrow (IsoArrow (iso_of_rel_iso_iso_sort hx) (iso_of_rel_iso_iso_sort hx)) (IsoArrow (iso_of_rel_iso_iso_sort hx) (iso_of_rel_iso_iso_sort hx)))
          (Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.three Original.LF_DOT_Poly.LF.Poly.Exercises.two)
          (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
           imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x3 : x => x0 x3) x1)
             (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x1 : x => x0 x1) x3) (fun x : x2 => x4 x) x6)
          (fun (x1 x2 : Type) (hx : rel_iso iso_Sort x1 x2) =>
           IsoFunND (Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.three Original.LF_DOT_Poly.LF.Poly.Exercises.two x1)
             (fun (x4 : x2 -> x2) (x6 : x2) =>
              imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x5 : x => x0 x5) x3)
                (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x5 : x => x0 x5) x3) (fun x : x2 => x4 x) x6)
             (fun (x3 : x1 -> x1) (x4 : x2 -> x2) (hx0 : rel_iso (IsoArrow (iso_of_rel_iso_iso_sort hx) (iso_of_rel_iso_iso_sort hx)) x3 x4) =>
              IsoFunND (Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.three Original.LF_DOT_Poly.LF.Poly.Exercises.two x1 x3)
                (fun x6 : x2 =>
                 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x5 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x7 : x => x0 x7) x5)
                   (fun (x : Type) (x0 : x -> x) (x5 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x7 : x => x0 x7) x5) (fun x : x2 => x4 x) x6)
                (fun (x5 : x1) (x6 : x2) (hx1 : rel_iso (iso_of_rel_iso_iso_sort hx) x5 x6) =>
                 Original_LF__DOT__Poly_LF_Poly_Exercises_plus_iso Original.LF_DOT_Poly.LF.Poly.Exercises.three
                   (fun (x : Type) (x0 : x -> x) (x7 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three (fun x8 : x => x0 x8) x7)
                   (fun (x7 x8 : Type) (hx2 : Iso x7 x8) (x9 : x7 -> x7) (x10 : x8 -> x8) (hx3 : forall (x11 : x7) (x12 : x8), rel_iso hx2 x11 x12 -> rel_iso hx2 (x9 x11) (x10 x12)) 
                      (x11 : x7) (x12 : x8) (hx4 : rel_iso hx2 x11 x12) =>
                    Original_LF__DOT__Poly_LF_Poly_Exercises_three_iso x9 (fun x : x8 => x10 x) (fun (x13 : x7) (x14 : x8) (hx5 : rel_iso hx2 x13 x14) => hx3 x13 x14 hx5) hx4)
                   Original.LF_DOT_Poly.LF.Poly.Exercises.two (fun (x : Type) (x0 : x -> x) (x7 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x8 : x => x0 x8) x7)
                   (fun (x7 x8 : Type) (hx2 : Iso x7 x8) (x9 : x7 -> x7) (x10 : x8 -> x8) (hx3 : forall (x11 : x7) (x12 : x8), rel_iso hx2 x11 x12 -> rel_iso hx2 (x9 x11) (x10 x12)) 
                      (x11 : x7) (x12 : x8) (hx4 : rel_iso hx2 x11 x12) =>
                    Original_LF__DOT__Poly_LF_Poly_Exercises_two_iso x9 (fun x : x8 => x10 x) (fun (x13 : x7) (x14 : x8) (hx5 : rel_iso hx2 x13 x14) => hx3 x13 x14 hx5) hx4)
                   x3 (fun x : x2 => x4 x) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso (iso_of_rel_iso_iso_sort hx) x7 x8) => IsoUnFunND hx0 hx2) hx1)))))
    Original.LF_DOT_Poly.LF.Poly.Exercises.plus_2 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2.
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.plus_2 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.plus_2 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2_iso; constructor : typeclass_instances.


End Interface.