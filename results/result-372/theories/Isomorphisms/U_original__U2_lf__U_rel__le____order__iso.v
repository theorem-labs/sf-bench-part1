From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__order__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Definition imported_Original_LF_Rel_le__order : imported_Original_LF_Rel_order (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0) := Imported.Original_LF_Rel_le__order.

(* The main theorem is admitted in Original.v, so the isomorphism uses SProp proof irrelevance *)
Instance Original_LF_Rel_le__order_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Original_LF_Rel_order_iso Original.LF_DOT_IndProp.LF.IndProp.le (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0)
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) => Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx0)))
    Original.LF.Rel.le_order imported_Original_LF_Rel_le__order.
Proof.
  unfold rel_iso.
  (* Both values are in SProp, so they are definitionally equal by proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF.Rel.le_order := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF_Rel_le__order := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF.Rel.le_order Original_LF_Rel_le__order_iso := {}.
Instance: IsoStatementProofBetween Original.LF.Rel.le_order Imported.Original_LF_Rel_le__order Original_LF_Rel_le__order_iso := {}.