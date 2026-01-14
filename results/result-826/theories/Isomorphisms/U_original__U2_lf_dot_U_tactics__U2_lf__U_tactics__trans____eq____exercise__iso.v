From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__minustwo__iso.

(* The imported function takes: x x0 x1 x2 : nat, then proof1, then proof2 
   where x=n, x0=m, x1=o, x2=p *)
Definition imported_Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise : forall x x0 x1 x2 : imported_nat,
  @imported_Corelib_Init_Logic_eq imported_nat x0 (imported_Original_LF__DOT__Basics_LF_Basics_minustwo x1) ->
  @imported_Corelib_Init_Logic_eq imported_nat (imported_Nat_add x x2) x0 -> 
  @imported_Corelib_Init_Logic_eq imported_nat (imported_Nat_add x x2) (imported_Original_LF__DOT__Basics_LF_Basics_minustwo x1) := Imported.Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise.

(* The isomorphism maps:
   Original: trans_eq_exercise x1 x3 x5 x7 x9 x11  (n m o p proof1 proof2)
   to
   Imported: trans_eq_exercise x2 x4 x6 x8 x10 x12 (n' m' o' p' proof1' proof2')
   
   But the interface shows the call as: imported_... x10 x12
   This means imported_... should be partially applied with x2 x4 x6 x8 already!
*)
Instance Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) (x9 : x3 = Original.LF_DOT_Basics.LF.Basics.minustwo x5)
    (x10 : imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Basics_LF_Basics_minustwo x6)),
  rel_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Basics_LF_Basics_minustwo_iso hx1)) x9 x10 ->
  forall (x11 : x1 + x7 = x3) (x12 : imported_Corelib_Init_Logic_eq (imported_Nat_add x2 x8) x4),
  rel_iso (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx2) hx0) x11 x12 ->
  rel_iso (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx2) (Original_LF__DOT__Basics_LF_Basics_minustwo_iso hx1)) (Original.LF_DOT_Tactics.LF.Tactics.trans_eq_exercise x1 x3 x5 x7 x9 x11)
    (@imported_Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise x2 x4 x6 x8 x10 x12).
Proof.
  intros.
  (* Both source and target are propositions/SProp, so we can use eq_refl *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Tactics.LF.Tactics.trans_eq_exercise := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.trans_eq_exercise Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.trans_eq_exercise Imported.Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise_iso := {}.