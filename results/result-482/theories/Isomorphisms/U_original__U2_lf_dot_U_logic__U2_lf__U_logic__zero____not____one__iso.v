From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_zero__not__one : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) -> imported_False := Imported.Original_LF__DOT__Logic_LF_Logic_zero__not__one.

(* Use explicit Datatypes.nat numerals *)
Local Notation "0" := Datatypes.O.
Local Notation "1" := (Datatypes.S Datatypes.O).

Instance Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso : forall (x1 : 0 = 1) (x2 : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0)),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso);
      from := from (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso));
      to_from := fun x : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) => to_from (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) x;
      from_to := fun x : 0 = 1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) x)
    |} x1 x2 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.zero_not_one x1) (imported_Original_LF__DOT__Logic_LF_Logic_zero__not__one x2).
Proof.
  intros x1 x2 Hrel.
  (* The goal is to show rel_iso for False values - we use that x1 : 0 = 1 is absurd *)
  unfold rel_iso. simpl.
  (* Both sides compute to False values, which are related by eq_refl in SProp *)
  destruct (Original.LF_DOT_Logic.LF.Logic.zero_not_one x1).
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.zero_not_one := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_zero__not__one := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.zero_not_one Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.zero_not_one Imported.Original_LF__DOT__Logic_LF_Logic_zero__not__one Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso := {}.