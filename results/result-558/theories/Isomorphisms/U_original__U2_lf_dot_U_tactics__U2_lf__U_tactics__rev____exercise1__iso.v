From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1 : forall x x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat,
  imported_Corelib_Init_Logic_eq x (imported_Original_LF__DOT__Poly_LF_Poly_rev x0) -> imported_Corelib_Init_Logic_eq x0 (imported_Original_LF__DOT__Poly_LF_Poly_rev x) := Imported.Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1.

Instance Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2)
    (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4)
    (x5 : x1 = Original.LF_DOT_Poly.LF.Poly.rev x3) (x6 : @imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) x2 (imported_Original_LF__DOT__Poly_LF_Poly_rev x4)),
  rel_iso (Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0)) x5 x6 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx)) (Original.LF_DOT_Tactics.LF.Tactics.rev_exercise1 x1 x3 x5)
    (@imported_Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1 x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 H56.
  (* Both sides are proofs of equality propositions. 
     Since they are in SProp, any two inhabitants are equal. *)
  unfold rel_iso.
  unfold imported_Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1.
  unfold imported_Corelib_Init_Logic_eq.
  (* The goal is to show that two SProp equality proofs are equal *)
  (* All SProp inhabitants are equal, so we just need reflexivity *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Tactics.LF.Tactics.rev_exercise1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.rev_exercise1 Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.rev_exercise1 Imported.Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1 Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1_iso := {}.