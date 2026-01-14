From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_lemma__application__ex : forall (x : imported_nat) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat),
  imported_Original_LF__DOT__Logic_LF_Logic_In x (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x1 : imported_nat => imported_Nat_mul x1 imported_0) x0) ->
  imported_Corelib_Init_Logic_eq x imported_0.
Parameter Original_LF__DOT__Logic_LF_Logic_lemma__application__ex_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4) (x5 : Original.LF_DOT_Logic.LF.Logic.In x1 (Original.LF_DOT_Poly.LF.Poly.map (fun m : nat => m * 0) x3))
    (x6 : imported_Original_LF__DOT__Logic_LF_Logic_In x2 (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x : imported_nat => imported_Nat_mul x imported_0) x4)),
  rel_iso
    (Original_LF__DOT__Logic_LF_Logic_In_iso hx
       (Original_LF__DOT__Poly_LF_Poly_map_iso (fun m : nat => m * 0) (fun x : imported_nat => imported_Nat_mul x imported_0)
          (fun (x7 : nat) (x8 : imported_nat) (hx1 : rel_iso nat_iso x7 x8) => Nat_mul_iso hx1 _0_iso) hx0))
    x5 x6 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx _0_iso) (Original.LF_DOT_Logic.LF.Logic.lemma_application_ex x5) (imported_Original_LF__DOT__Logic_LF_Logic_lemma__application__ex x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_lemma__application__ex_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.lemma_application_ex) ?x) => unify x Original_LF__DOT__Logic_LF_Logic_lemma__application__ex_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.lemma_application_ex) imported_Original_LF__DOT__Logic_LF_Logic_lemma__application__ex ?x) => unify x Original_LF__DOT__Logic_LF_Logic_lemma__application__ex_iso; constructor : typeclass_instances.


End Interface.