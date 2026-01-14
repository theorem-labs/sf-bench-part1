From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1 : forall x x0 : imported_nat, imported_Corelib_Init_Logic_eq imported_Original_LF__DOT__Basics_LF_Basics_false imported_Original_LF__DOT__Basics_LF_Basics_true -> imported_Corelib_Init_Logic_eq x x0 := Imported.Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1.
Instance Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4)
    (x5 : Original.LF_DOT_Basics.LF.Basics.false = Original.LF_DOT_Basics.LF.Basics.true)
    (x6 : imported_Corelib_Init_Logic_eq imported_Original_LF__DOT__Basics_LF_Basics_false imported_Original_LF__DOT__Basics_LF_Basics_true),
  rel_iso (Corelib_Init_Logic_eq_iso Original_LF__DOT__Basics_LF_Basics_false_iso Original_LF__DOT__Basics_LF_Basics_true_iso) x5 x6 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original.LF_DOT_Tactics.LF.Tactics.discriminate_ex1 x1 x3 x5) (imported_Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1 x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hiso.
  (* The goal is to show that the results of the two discriminate_ex1 functions are related.
     Both functions produce equalities (x1 = x3) and (x2 = x4) respectively.
     The relation rel_iso on equalities lives in SProp.
     Since SProp values are proof-irrelevant, any two inhabitants are equal. *)
  unfold rel_iso.
  simpl.
  (* The isomorphism between equalities maps to SProp, so we need to show
     that the 'to' direction of the isomorphism applied to the original result
     equals the imported result. Both are in SProp, hence equal. *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Tactics.LF.Tactics.discriminate_ex1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.discriminate_ex1 Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.discriminate_ex1 Imported.Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1 Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1_iso := {}.