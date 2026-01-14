From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsbSQUOTE__iso Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsb__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsbSQUOTE__iso Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsb__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsbSQUOTE__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsb__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsbSQUOTE__iso.Interface <+ Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__existsb__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb' : forall (x : Type) (x0 : x -> imported_Original_LF__DOT__Basics_LF_Basics_bool) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Tactics_LF_Tactics_existsb (fun x2 : x => x0 x2) x1) (imported_Original_LF__DOT__Tactics_LF_Tactics_existsb' (fun x2 : x => x0 x2) x1).
Parameter Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb'_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Original.LF_DOT_Basics.LF.Basics.bool) (x4 : x2 -> imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x3 x5) (x4 x6)) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1)
    (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Tactics_LF_Tactics_existsb_iso x3 (fun x : x2 => x4 x) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1)
       (Original_LF__DOT__Tactics_LF_Tactics_existsb'_iso x3 (fun x : x2 => x4 x) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2) hx1))
    (Original.LF_DOT_Tactics.LF.Tactics.existsb_existsb' x1 x3 x5) (imported_Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb' x4 x6).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.existsb_existsb' ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.existsb_existsb' imported_Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb' ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_existsb__existsb'_iso; constructor : typeclass_instances.


End Interface.