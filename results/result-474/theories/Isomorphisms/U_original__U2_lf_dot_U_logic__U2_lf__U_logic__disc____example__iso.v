From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_disc__example : forall x : imported_nat, imported_Corelib_Init_Logic_eq imported_0 (imported_S x) -> imported_False := Imported.Original_LF__DOT__Logic_LF_Logic_disc__example.
Instance Original_LF__DOT__Logic_LF_Logic_disc__example_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : @Logic.eq nat 0%nat (S x1)) (x4 : imported_Corelib_Init_Logic_eq imported_0 (imported_S x2)),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso _0_iso (S_iso hx);
      from := from (Corelib_Init_Logic_eq_iso _0_iso (S_iso hx));
      to_from := fun x : imported_Corelib_Init_Logic_eq imported_0 (imported_S x2) => to_from (Corelib_Init_Logic_eq_iso _0_iso (S_iso hx)) x;
      from_to := fun x : @Logic.eq nat 0%nat (S x1) => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso _0_iso (S_iso hx)) x)
    |} x3 x4 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : Logic.False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.disc_example x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_disc__example x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  (* x3 : 0 = S x1 is a proof of a false statement (0 ≠ S x1).
     We can derive False from x3 using discriminate. *)
  exfalso. discriminate x3.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.disc_example := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_disc__example := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.disc_example Original_LF__DOT__Logic_LF_Logic_disc__example_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.disc_example Imported.Original_LF__DOT__Logic_LF_Logic_disc__example Original_LF__DOT__Logic_LF_Logic_disc__example_iso := {}.