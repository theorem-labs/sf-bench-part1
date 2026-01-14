From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__orb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__orb__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__orb__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__orb__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Induction_LF_Induction_all3__spec : forall x x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool,
  imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Basics_LF_Basics_orb (imported_Original_LF__DOT__Basics_LF_Basics_andb x x0)
       (imported_Original_LF__DOT__Basics_LF_Basics_orb (imported_Original_LF__DOT__Basics_LF_Basics_negb x) (imported_Original_LF__DOT__Basics_LF_Basics_negb x0)))
    imported_Original_LF__DOT__Basics_LF_Basics_true.
Parameter Original_LF__DOT__Induction_LF_Induction_all3__spec_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2)
    (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Basics_LF_Basics_orb_iso (Original_LF__DOT__Basics_LF_Basics_andb_iso hx hx0)
          (Original_LF__DOT__Basics_LF_Basics_orb_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso hx) (Original_LF__DOT__Basics_LF_Basics_negb_iso hx0)))
       Original_LF__DOT__Basics_LF_Basics_true_iso)
    (Original.LF_DOT_Induction.LF.Induction.all3_spec x1 x3) (imported_Original_LF__DOT__Induction_LF_Induction_all3__spec x2 x4).
Existing Instance Original_LF__DOT__Induction_LF_Induction_all3__spec_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.all3_spec ?x) => unify x Original_LF__DOT__Induction_LF_Induction_all3__spec_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.all3_spec imported_Original_LF__DOT__Induction_LF_Induction_all3__spec ?x) => unify x Original_LF__DOT__Induction_LF_Induction_all3__spec_iso; constructor : typeclass_instances.


End Interface.