From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Isomorphisms.U_s__iso.

(* Define imported nat for 5 and 9 *)
Definition nat_5 : Datatypes.nat := 5.
Definition nat_5_imported : imported_nat := nat_to_imported nat_5.

Definition nat_2 : Datatypes.nat := 2.
Definition nat_2_imported : imported_nat := nat_to_imported nat_2.

Definition nat_4 : Datatypes.nat := 4.
Definition nat_4_imported : imported_nat := nat_to_imported nat_4.

Definition nat_9 : Datatypes.nat := 9.
Definition nat_9_imported : imported_nat := nat_to_imported nat_9.

Lemma nat_5_rel : rel_iso nat_iso nat_5 nat_5_imported.
Proof. constructor. reflexivity. Defined.

Lemma nat_2_rel : rel_iso nat_iso nat_2 nat_2_imported.
Proof. constructor. reflexivity. Defined.

Lemma nat_4_rel : rel_iso nat_iso nat_4 nat_4_imported.
Proof. constructor. reflexivity. Defined.

Lemma nat_9_rel : rel_iso nat_iso nat_9 nat_9_imported.
Proof. constructor. reflexivity. Defined.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat_5_imported ->
  imported_Corelib_Init_Logic_eq (imported_Nat_add nat_2_imported nat_2_imported) nat_9_imported := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense.

Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev nat_5)
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat_5_imported),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso nat_5_rel) x1 x2 ->
  rel_iso (Corelib_Init_Logic_eq_iso (Nat_add_iso nat_2_rel nat_2_rel) nat_9_rel)
    (Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense x2).
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense Imported.Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense_iso := {}.
