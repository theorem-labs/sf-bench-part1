From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__csf__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_cs : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_cs.

Instance Original_LF__DOT__IndProp_LF_IndProp_cs_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.cs x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_cs x2 x4).
Proof.
  intros n1 n2 Hn m1 m2 Hm.
  unfold Original.LF_DOT_IndProp.LF.IndProp.cs, imported_Original_LF__DOT__IndProp_LF_IndProp_cs.
  (* cs n m := csf n = m *)
  apply (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_csf_iso Hn) Hm).
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.cs := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_cs := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.cs Original_LF__DOT__IndProp_LF_IndProp_cs_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.cs Imported.Original_LF__DOT__IndProp_LF_IndProp_cs Original_LF__DOT__IndProp_LF_IndProp_cs_iso := {}.