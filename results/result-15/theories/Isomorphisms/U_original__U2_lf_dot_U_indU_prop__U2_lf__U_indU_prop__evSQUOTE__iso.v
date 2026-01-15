From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev' : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'.

(* Short names for convenience *)
Definition ev'_orig := Original.LF_DOT_IndProp.LF.IndProp.ev'.
Definition ev'_imp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'.
Definition ev_orig := Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev.
Definition ev_imp := Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.

(* Helper: ev_orig addition *)
Lemma ev_add : forall n m, Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev n -> Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev m -> Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn.
  - simpl. exact Hm.
  - simpl.
    exact (Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev_SS _ IHHn).
Qed.

(* Helper: ev'_orig -> ev_orig (using fix tactic) *)
Definition ev'_to_ev_orig : forall n : nat, Original.LF_DOT_IndProp.LF.IndProp.ev' n -> Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev n.
Proof.
  fix IH 2.
  intros n H.
  destruct H as [| | n' m' Hn Hm].
  - exact Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev_0.
  - exact (Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev_SS 0 Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev_0).
  - exact (@ev_add n' m' (IH n' Hn) (IH m' Hm)).
Defined.

(* Helper: ev_orig -> ev'_orig *)
Definition ev_to_ev'_orig : forall n : nat, Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev n -> Original.LF_DOT_IndProp.LF.IndProp.ev' n.
Proof.
  fix IH 2.
  intros n H.
  destruct H as [| n' H'].
  - exact Original.LF_DOT_IndProp.LF.IndProp.ev'_0.
  - exact (Original.LF_DOT_IndProp.LF.IndProp.ev'_sum 2 n' Original.LF_DOT_IndProp.LF.IndProp.ev'_2 (IH n' H')).
Defined.

(* Helper: construct ev'_imp from nat *)
Definition ev'_to_imported (n : Datatypes.nat) (H : Original.LF_DOT_IndProp.LF.IndProp.ev' n) : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' (nat_to_imported n).
Proof.
  pose (@ev'_to_ev_orig n H) as Hev.
  pose (@ev_to_imported_aux n Hev) as Hev_imp.
  pose (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'__ev (nat_to_imported n)) as Hiff.
  destruct Hiff as [_ Hback].
  exact (Hback Hev_imp).
Defined.

(* Helper: construct ev'_orig from ev'_imp *)
Definition ev'_from_imported (n : Imported.nat) (H : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' n) : Original.LF_DOT_IndProp.LF.IndProp.ev' (imported_to_nat n).
Proof.
  pose (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'__ev n) as Hiff.
  destruct Hiff as [Hfwd _].
  pose (Hfwd H) as Hev_imp.
  pose (@ev_from_imported n Hev_imp) as Hev_orig.
  exact (@ev_to_ev'_orig (imported_to_nat n) Hev_orig).
Defined.

(* Build the iso to/from functions *)
Definition ev'_iso_to (x1 : Datatypes.nat) (x2 : Imported.nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : ev'_orig x1) : ev'_imp x2 :=
  match Hx in (IsomorphismDefinitions.eq _ y) return ev'_imp y with
  | IsomorphismDefinitions.eq_refl => @ev'_to_imported x1 H
  end.

Definition ev'_iso_from (x1 : Datatypes.nat) (x2 : Imported.nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : ev'_imp x2) : ev'_orig x1 :=
  let H' := match Hx in (IsomorphismDefinitions.eq _ y) return ev'_imp y -> ev'_imp (nat_to_imported x1) with
            | IsomorphismDefinitions.eq_refl => fun h => h
            end H in
  let H'' := @ev'_from_imported (nat_to_imported x1) H' in
  match nat_roundtrip x1 in (_ = m) return ev'_orig m with
  | Logic.eq_refl => H''
  end.

Require Import Stdlib.Logic.ProofIrrelevance.

(* Convert proof irrelevance to SProp equality for Prop types *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_ev'_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2),
   Iso (Original.LF_DOT_IndProp.LF.IndProp.ev' x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev' x2)).
Proof.
  intros x1 x2 Hx.
  destruct Hx as [Hx]. simpl in Hx.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_ev'.
  refine {|
    to := @ev'_iso_to x1 x2 Hx;
    from := @ev'_iso_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev' := {}.
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' := {}.
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev' Original_LF__DOT__IndProp_LF_IndProp_ev'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev' Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' Original_LF__DOT__IndProp_LF_IndProp_ev'_iso := {}.
