From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev__plus4 : forall x : imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x ->
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add (imported_S (imported_S (imported_S (imported_S imported_0)))) x) := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__plus4.

(* Since ev_plus4 is Admitted in Original.v, we use iso_SInhabited to establish the isomorphism.
   Both Original.LF_DOT_IndProp.LF.IndProp.ev_plus4 and Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__plus4
   are axioms, so we can't prove they map corresponding inputs to corresponding outputs directly.
   Instead, we use proof irrelevance: since the target type is an SProp, 
   any two inhabitants are definitionally equal. *)

Instance Original_LF__DOT__IndProp_LF_IndProp_ev__plus4_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x1)
    (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (Nat_add_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) hx)) (Original.LF_DOT_IndProp.LF.IndProp.ev_plus4 x1 x3)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_ev__plus4 x4).
Proof.
  intros x1 x2 hx x3 x4 hev.
  unfold rel_iso. simpl.
  (* The goal is: eq (to (ev_iso ...) (ev_plus4 x1 x3)) (imported_ev_plus4 x4) *)
  (* Both sides are inhabitants of the SProp 
     imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add ... x2)
     Since SProp has proof irrelevance, any two inhabitants are equal. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev_plus4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__plus4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev_plus4 Original_LF__DOT__IndProp_LF_IndProp_ev__plus4_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev_plus4 Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__plus4 Original_LF__DOT__IndProp_LF_IndProp_ev__plus4_iso := {}.