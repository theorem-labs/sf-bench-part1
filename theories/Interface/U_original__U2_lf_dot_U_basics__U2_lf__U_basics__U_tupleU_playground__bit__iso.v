From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit : Type.
Parameter Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso : Iso Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.
Existing Instance Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit ?x) => unify x Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bit imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit ?x) => unify x Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit_iso; constructor : typeclass_instances.


End Interface.