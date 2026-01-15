From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_In__example__2 : forall x : imported_nat,
  imported_Original_LF__DOT__Logic_LF_Logic_In x
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))) ->
  imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x (imported_Nat_mul (imported_S (imported_S imported_0)) H)).
Parameter Original_LF__DOT__Logic_LF_Logic_In__example__2_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2)
    (x3 : Original.LF_DOT_Logic.LF.Logic.In x1 (Original.LF_DOT_Poly.LF.Poly.cons 2 (Original.LF_DOT_Poly.LF.Poly.cons 4 Original.LF_DOT_Poly.LF.Poly.nil)))
    (x4 : imported_Original_LF__DOT__Logic_LF_Logic_In x2
            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))),
  rel_iso
    (relax_Iso_Ts_Ps
       (Original_LF__DOT__Logic_LF_Logic_In_iso hx
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
    x3 x4 ->
  rel_iso
    (relax_Iso_Ts_Ps
       (ex_iso (fun n' : nat => x1 = 2 * n') (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_mul (imported_S (imported_S imported_0)) H))
          (fun (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) => Corelib_Init_Logic_eq_iso hx (Nat_mul_iso (S_iso (S_iso _0_iso)) hx1))))
    (Original.LF_DOT_Logic.LF.Logic.In_example_2 x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_In__example__2 x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_In__example__2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.In_example_2 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_In__example__2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.In_example_2 imported_Original_LF__DOT__Logic_LF_Logic_In__example__2 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_In__example__2_iso; constructor : typeclass_instances.


End Interface.