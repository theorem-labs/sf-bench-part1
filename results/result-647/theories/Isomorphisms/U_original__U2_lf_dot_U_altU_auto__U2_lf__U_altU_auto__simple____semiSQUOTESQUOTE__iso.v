From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi'' : forall x : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Nat_add x (imported_S imported_0)) imported_0) imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi''.
Instance Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi''_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso (Nat_add_iso hx (S_iso _0_iso)) _0_iso) Original_LF__DOT__Basics_LF_Basics_false_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso (Nat_add_iso hx (S_iso _0_iso)) _0_iso) Original_LF__DOT__Basics_LF_Basics_false_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Nat_add x2 (imported_S imported_0)) imported_0)
                imported_Original_LF__DOT__Basics_LF_Basics_false =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso (Nat_add_iso hx (S_iso _0_iso)) _0_iso) Original_LF__DOT__Basics_LF_Basics_false_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.eqb (x1 + 1) 0 = Original.LF_DOT_Basics.LF.Basics.false =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_eqb_iso (Nat_add_iso hx (S_iso _0_iso)) _0_iso) Original_LF__DOT__Basics_LF_Basics_false_iso) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.simple_semi'' x1) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi'' x2).
Proof.
  intros.
  unfold rel_iso; simpl.
  (* Both sides are SProp values, so they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.simple_semi'' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi'' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.simple_semi'' Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi''_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.simple_semi'' Imported.Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi'' Original_LF__DOT__AltAuto_LF_AltAuto_simple__semi''_iso := {}.