From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_evSS__ev : forall x : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S (imported_S x)) -> imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x := Imported.Original_LF__DOT__IndProp_LF_IndProp_evSS__ev.

(* The isomorphism for evSS_ev: the goal is an SProp equality, and SProp is proof-irrelevant *)
Instance Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev (S (S x1)))
    (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S (imported_S x2))),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (S_iso (S_iso hx))) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.evSS_ev x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_evSS__ev x4).
Proof.
  intros x1 x2 hx x3 x4 Hx34.
  unfold rel_iso in *.
  simpl in *.
  (* The goal is an SProp equality between two elements of an SProp type *)
  (* In SProp, all proofs are equal, so we can just use eq_refl *)
  exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.evSS_ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_evSS__ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.evSS_ev Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.evSS_ev Imported.Original_LF__DOT__IndProp_LF_IndProp_evSS__ev Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso := {}.