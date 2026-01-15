From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_nat__mul__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_and__example : imported_and
    (imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))))
       (imported_S (imported_S (imported_S (iterate1 imported_S 4 imported_0)))))
    (imported_Corelib_Init_Logic_eq (imported_Nat_mul (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
       (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))).
Parameter Original_LF__DOT__Logic_LF_Logic_and__example_iso : rel_iso
    (relax_Iso_Ts_Ps
       (and_iso
          (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))))
             (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 4 0 imported_0 _0_iso)))))
          (Corelib_Init_Logic_eq_iso (Nat_mul_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))))))
    Original.LF_DOT_Logic.LF.Logic.and_example imported_Original_LF__DOT__Logic_LF_Logic_and__example.
Existing Instance Original_LF__DOT__Logic_LF_Logic_and__example_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.and_example ?x) => unify x Original_LF__DOT__Logic_LF_Logic_and__example_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.and_example imported_Original_LF__DOT__Logic_LF_Logic_and__example ?x) => unify x Original_LF__DOT__Logic_LF_Logic_and__example_iso; constructor : typeclass_instances.


End Interface.