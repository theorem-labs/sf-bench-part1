From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_negb__involutive : forall x : imported_Original_LF__DOT__Basics_LF_Basics_bool, imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_negb (imported_Original_LF__DOT__Basics_LF_Basics_negb x)) x := Imported.Original_LF__DOT__Basics_LF_Basics_negb__involutive.
Instance Original_LF__DOT__Basics_LF_Basics_negb__involutive_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso hx)) hx;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso hx)) hx);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_negb (imported_Original_LF__DOT__Basics_LF_Basics_negb x2)) x2 =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso hx)) hx) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.negb (Original.LF_DOT_Basics.LF.Basics.negb x1) = x1 =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso (Original_LF__DOT__Basics_LF_Basics_negb_iso hx)) hx) x)
    |} (Original.LF_DOT_Basics.LF.Basics.negb_involutive x1) (imported_Original_LF__DOT__Basics_LF_Basics_negb__involutive x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  (* Both sides are SProp terms (proofs), so they are equal by proof irrelevance in SProp *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.negb_involutive := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_negb__involutive := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.negb_involutive Original_LF__DOT__Basics_LF_Basics_negb__involutive_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.negb_involutive Imported.Original_LF__DOT__Basics_LF_Basics_negb__involutive Original_LF__DOT__Basics_LF_Basics_negb__involutive_iso := {}.