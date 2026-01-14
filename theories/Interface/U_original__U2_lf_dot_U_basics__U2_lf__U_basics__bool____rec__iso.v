From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_bool__rec : forall x : imported_Original_LF__DOT__Basics_LF_Basics_bool -> Type,
  x imported_Original_LF__DOT__Basics_LF_Basics_true -> x imported_Original_LF__DOT__Basics_LF_Basics_false -> forall x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool, x x2.
Parameter Original_LF__DOT__Basics_LF_Basics_bool__rec_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool -> Set) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool -> Type)
    (hx : forall (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
          rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4 -> IsoOrSortRelaxed (x1 x3) (x2 x4))
    (x3 : x1 Original.LF_DOT_Basics.LF.Basics.true) (x4 : x2 imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso_sort (hx Original.LF_DOT_Basics.LF.Basics.true imported_Original_LF__DOT__Basics_LF_Basics_true Original_LF__DOT__Basics_LF_Basics_true_iso) x3 x4 ->
  forall (x5 : x1 Original.LF_DOT_Basics.LF.Basics.false) (x6 : x2 imported_Original_LF__DOT__Basics_LF_Basics_false),
  rel_iso_sort (hx Original.LF_DOT_Basics.LF.Basics.false imported_Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_false_iso) x5 x6 ->
  forall (x7 : Original.LF_DOT_Basics.LF.Basics.bool) (x8 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx2 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x7 x8),
  rel_iso_sort (hx x7 x8 hx2) (Original.LF_DOT_Basics.LF.Basics.bool_rec x1 x3 x5 x7) (imported_Original_LF__DOT__Basics_LF_Basics_bool__rec x2 x4 x6 x8).
Existing Instance Original_LF__DOT__Basics_LF_Basics_bool__rec_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bool_rec ?x) => unify x Original_LF__DOT__Basics_LF_Basics_bool__rec_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bool_rec imported_Original_LF__DOT__Basics_LF_Basics_bool__rec ?x) => unify x Original_LF__DOT__Basics_LF_Basics_bool__rec_iso; constructor : typeclass_instances.


End Interface.