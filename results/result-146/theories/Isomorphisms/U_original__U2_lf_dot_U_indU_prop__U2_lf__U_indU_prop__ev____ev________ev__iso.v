From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.

(* Define with explicit arguments to match the interface *)
Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev : forall x x0 : imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add x x0) ->
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x -> imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x0 
  := @Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev.

(* Clear implicit arguments so both x and x0 are explicit *)
Arguments imported_Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev x x0 _ _ : clear implicits.

(* The isomorphism between the two axioms.
   Since both ev_ev__ev (in Original) and its imported version are axioms,
   and since the result type is an SProp (ev m), we can use that SProp 
   inhabitants are all equal by definition via eq_refl. *)

Instance Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev (x1 + x3))
    (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add x2 x4)),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (Nat_add_iso hx hx0)) x5 x6 ->
  forall (x7 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x1) (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx) x7 x8 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx0) (Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev x2 x4 x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hev_sum x7 x8 Hev_n.
  unfold rel_iso. simpl.
  (* Since both result types are SProp, eq_refl works *)
  exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev Imported.Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso := {}.
