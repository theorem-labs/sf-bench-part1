From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice : forall x : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool,
  (forall x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, imported_Corelib_Init_Logic_eq (x x0) x0) ->
  forall x1 : imported_Original_LF__DOT__Basics_LF_Basics_bool, imported_Corelib_Init_Logic_eq (x (x x1)) x1.
Parameter Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_Basics.LF.Basics.bool)
    (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx : forall (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
          rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x1 x3) (x2 x4))
    (x3 : forall x : Original.LF_DOT_Basics.LF.Basics.bool, x1 x = x) (x4 : forall x : imported_Original_LF__DOT__Basics_LF_Basics_bool, imported_Corelib_Init_Logic_eq (x2 x) x),
  (forall (x5 : Original.LF_DOT_Basics.LF.Basics.bool) (x6 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x5 x6),
   rel_iso (Corelib_Init_Logic_eq_iso (hx x5 x6 hx0) hx0) (x3 x5) (x4 x6)) ->
  forall (x5 : Original.LF_DOT_Basics.LF.Basics.bool) (x6 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx1 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x5 x6),
  rel_iso (Corelib_Init_Logic_eq_iso (hx (x1 x5) (x2 x6) (hx x5 x6 hx1)) hx1) (Original.LF_DOT_Basics.LF.Basics.identity_fn_applied_twice x1 x3 x5)
    (imported_Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice x2 x4 x6).
Existing Instance Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.identity_fn_applied_twice ?x) => unify x Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.identity_fn_applied_twice imported_Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice ?x) => unify x Original_LF__DOT__Basics_LF_Basics_identity__fn__applied__twice_iso; constructor : typeclass_instances.


End Interface.