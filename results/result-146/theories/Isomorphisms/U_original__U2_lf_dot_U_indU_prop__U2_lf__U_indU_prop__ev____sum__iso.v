From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev__sum : forall x x0 : imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x ->
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x0 -> imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add x x0) := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__sum.

(* The isomorphism for ev types is an iso between SProp types.
   Since both sides are SProp, any two inhabitants are equal by eq_refl in SProp. *)

Instance Original_LF__DOT__IndProp_LF_IndProp_ev__sum_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x1)
    (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx) x5 x6 ->
  forall (x7 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x3) (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x4),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx0) x7 x8 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (Nat_add_iso hx hx0)) (Original.LF_DOT_IndProp.LF.IndProp.ev_sum x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_ev__sum x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 H56 x7 x8 H78.
  (* The goal is to prove that the ev (x1 + x3) and ev (x2 + x4) elements are related.
     The relation is an Iso between SProp types.
     Since both are SProp predicates, the proof is just eq_refl (definitional equality in SProp). *)
  unfold rel_iso. simpl.
  (* We need to show that to (ev_sum ... x5 x7) = imported_ev_sum x6 x8 *)
  (* Both ev types are SProp, so we can use the definitional UIP *)
  exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev_sum := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__sum := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev_sum Original_LF__DOT__IndProp_LF_IndProp_ev__sum_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev_sum Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__sum Original_LF__DOT__IndProp_LF_IndProp_ev__sum_iso := {}.