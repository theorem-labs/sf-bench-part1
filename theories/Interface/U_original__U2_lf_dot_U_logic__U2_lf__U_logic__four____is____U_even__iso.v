From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))).
Parameter Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso : rel_iso (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))) Original.LF_DOT_Logic.LF.Logic.four_is_Even
    imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even.
Existing Instance Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.four_is_Even ?x) => unify x Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.four_is_Even imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even ?x) => unify x Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso; constructor : typeclass_instances.


End Interface.