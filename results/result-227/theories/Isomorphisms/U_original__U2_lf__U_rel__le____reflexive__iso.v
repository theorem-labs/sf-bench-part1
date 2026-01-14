From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__reflexive__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Definition imported_Original_LF_Rel_le__reflexive : forall x : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_le x x := Imported.Original_LF_Rel_le__reflexive.

(* The isomorphism between admitted le_reflexive and the Lean axiom.
   Since both are axioms for the same statement (forall x, le x x),
   we need to show that applying the isomorphism maps one to the other.
   
   Original.LF.Rel.le_reflexive : forall x : nat, Original.LF_DOT_IndProp.LF.IndProp.le x x
   imported_Original_LF_Rel_le__reflexive : forall x : Imported.nat, Imported.Original_LF__DOT__IndProp_LF_IndProp_le x x
   
   The isomorphism (Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx) gives:
   Iso (Original.LF_DOT_IndProp.LF.IndProp.le x1 x1) (Imported.Original_LF__DOT__IndProp_LF_IndProp_le x2 x2)
   
   rel_iso means: to applied_to_lhs = rhs (in SProp eq)
*)

Instance Original_LF_Rel_le__reflexive_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx) (Original.LF.Rel.le_reflexive x1) (imported_Original_LF_Rel_le__reflexive x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso.
  (* Need to show: eq (to (Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx) (Original.LF.Rel.le_reflexive x1)) 
                      (imported_Original_LF_Rel_le__reflexive x2) *)
  (* Since both sides are in SProp (Imported.Original_LF__DOT__IndProp_LF_IndProp_le x2 x2),
     and SProp is proof-irrelevant, they are definitionally equal *)
  exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF.Rel.le_reflexive := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF_Rel_le__reflexive := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF.Rel.le_reflexive Original_LF_Rel_le__reflexive_iso := {}.
Instance: IsoStatementProofBetween Original.LF.Rel.le_reflexive Imported.Original_LF_Rel_le__reflexive Original_LF_Rel_le__reflexive_iso := {}.