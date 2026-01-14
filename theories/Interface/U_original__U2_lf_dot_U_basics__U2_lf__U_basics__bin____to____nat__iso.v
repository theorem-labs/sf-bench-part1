From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_bin__to__nat : imported_Original_LF__DOT__Basics_LF_Basics_bin -> imported_nat.
Parameter Original_LF__DOT__Basics_LF_Basics_bin__to__nat_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bin) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bin),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bin_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.bin_to_nat x1) (imported_Original_LF__DOT__Basics_LF_Basics_bin__to__nat x2).
Existing Instance Original_LF__DOT__Basics_LF_Basics_bin__to__nat_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bin_to_nat ?x) => unify x Original_LF__DOT__Basics_LF_Basics_bin__to__nat_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bin_to_nat imported_Original_LF__DOT__Basics_LF_Basics_bin__to__nat ?x) => unify x Original_LF__DOT__Basics_LF_Basics_bin__to__nat_iso; constructor : typeclass_instances.


End Interface.