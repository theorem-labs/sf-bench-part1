From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_leb__plus__exists : forall x x0 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb x x0) imported_Original_LF__DOT__Basics_LF_Basics_true ->
  imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x0 (imported_Nat_add x H)).
Parameter Original_LF__DOT__Logic_LF_Logic_leb__plus__exists_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4)
    (x5 : Original.LF_DOT_Basics.LF.Basics.leb x1 x3 = Original.LF_DOT_Basics.LF.Basics.true)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb x2 x4) imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso (relax_Iso_Ts_Ps (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso hx hx0) Original_LF__DOT__Basics_LF_Basics_true_iso)) x5 x6 ->
  rel_iso
    (relax_Iso_Ts_Ps
       (ex_iso (fun x : nat => x3 = x1 + x) (fun H : imported_nat => imported_Corelib_Init_Logic_eq x4 (imported_Nat_add x2 H))
          (fun (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) => Corelib_Init_Logic_eq_iso hx0 (Nat_add_iso hx hx2))))
    (Original.LF_DOT_Logic.LF.Logic.leb_plus_exists x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_leb__plus__exists x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_leb__plus__exists_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.leb_plus_exists ?x) => unify x Original_LF__DOT__Logic_LF_Logic_leb__plus__exists_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.leb_plus_exists imported_Original_LF__DOT__Logic_LF_Logic_leb__plus__exists ?x) => unify x Original_LF__DOT__Logic_LF_Logic_leb__plus__exists_iso; constructor : typeclass_instances.


End Interface.