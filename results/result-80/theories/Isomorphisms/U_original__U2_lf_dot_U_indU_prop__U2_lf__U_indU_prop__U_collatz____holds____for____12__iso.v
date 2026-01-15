From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_collatz____holds____for__iso Isomorphisms.U_s__iso.

(* 12 = S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) *)
Definition twelve_nat : nat := S (S (S (S (S (S (S (S (S (S (S (S O))))))))))).
Definition twelve_imported : imported_nat := imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))))).

Lemma twelve_iso : rel_iso nat_iso twelve_nat twelve_imported.
Proof.
  unfold twelve_nat, twelve_imported.
  repeat apply S_iso.
  exact _0_iso.
Qed.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 : imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for twelve_imported := Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12.
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12_iso : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso twelve_iso)
    Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12.
Proof.
  (* Both sides are axioms, but we can derive the rel_iso using the Iso we proved *)
  constructor.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12_iso := {}.