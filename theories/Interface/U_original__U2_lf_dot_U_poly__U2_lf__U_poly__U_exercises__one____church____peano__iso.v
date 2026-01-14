From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one (fun x : imported_nat => imported_S x) imported_0) (imported_S imported_0).
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_Exercises_one_iso S (fun x : imported_nat => imported_S x) (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => S_iso hx) _0_iso) 
       (S_iso _0_iso))
    Original.LF_DOT_Poly.LF.Poly.Exercises.one_church_peano imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano.
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.one_church_peano ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.one_church_peano imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano_iso; constructor : typeclass_instances.


End Interface.