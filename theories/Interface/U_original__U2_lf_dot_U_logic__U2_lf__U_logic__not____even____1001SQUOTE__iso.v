From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 998 imported_0)))) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso : forall (x1 : Original.LF_DOT_Logic.LF.Logic.Even 1001) (x2 : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 998 imported_0))))),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 998 0 imported_0 _0_iso))))) x1 x2 ->
  rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.not_even_1001' x1) (imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_even_1001' ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_even_1001' imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso; constructor : typeclass_instances.


End Interface.