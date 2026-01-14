From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U_false__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U_false__iso.

  Export Interface.U_original__U_false__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U_false__iso.Args <+ Interface.U_original__U_false__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet : forall x : SProp, imported_Original_False -> x.
Parameter Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Original.False) (x4 : imported_Original_False),
  rel_iso Original_False_iso x3 x4 -> rel_iso hx (Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet x2 x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet ?x) => unify x Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet imported_Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet ?x) => unify x Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso; constructor : typeclass_instances.


End Interface.