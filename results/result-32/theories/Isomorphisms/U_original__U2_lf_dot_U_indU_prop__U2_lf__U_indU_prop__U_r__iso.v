From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_R : imported_nat -> imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_R.

Definition nat_to_imp := to nat_iso.
Definition imp_to_nat := from nat_iso.

(* Convert from Original R to Imported R - Prop to SProp works *)
Definition R_to_imported : forall (m n o : nat) (H : Original.LF_DOT_IndProp.LF.IndProp.R m n o), imported_Original_LF__DOT__IndProp_LF_IndProp_R (nat_to_imp m) (nat_to_imp n) (nat_to_imp o).
Proof.
  fix IH 4.
  intros m n o H.
  destruct H as [ | m' n' o' H' | m' n' o' H' | m' n' o' H' | m' n' o' H'].
  - exact Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c1.
  - exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c2 _ _ _ (IH _ _ _ H')).
  - exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c3 _ _ _ (IH _ _ _ H')).
  - exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c4 _ _ _ (IH _ _ _ H')).
  - exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c5 _ _ _ (IH _ _ _ H')).
Defined.

(* This isomorphism requires converting between Prop and SProp for an inductive type *)
(* The SProp -> Prop direction uses sinhabitant *)
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_R_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.R x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_R x2 x4 x6).
Proof.
  intros x1 x2 hx1 x3 x4 hx3 x5 x6 hx5.
  destruct hx1 as [hx1]. destruct hx3 as [hx3]. destruct hx5 as [hx5].
  simpl in *.
  (* hx1 : nat_to_imp x1 = x2, etc. *)
  destruct hx1. destruct hx3. destruct hx5.
  (* Now x2 = nat_to_imp x1, etc. *)
  unshelve eapply Build_Iso.
  - (* to: R in Prop -> imported R in SProp *)
    intro H.
    exact (@R_to_imported x1 x3 x5 H).
  - (* from: imported R in SProp -> R in Prop *)
    intro H.
    pose (converted := Imported.Original_LF__DOT__IndProp_LF_IndProp_R_indl
            (fun m n o _ => SInhabited (Original.LF_DOT_IndProp.LF.IndProp.R (imp_to_nat m) (imp_to_nat n) (imp_to_nat o)))
            (sinhabits Original.LF_DOT_IndProp.LF.IndProp.c1)
            (fun m' n' o' _ rec => sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c2 _ _ _ (sinhabitant rec)))
            (fun m' n' o' _ rec => sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c3 _ _ _ (sinhabitant rec)))
            (fun m' n' o' _ rec => sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c4 _ _ _ (sinhabitant rec)))
            (fun m' n' o' _ rec => sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c5 _ _ _ (sinhabitant rec)))
            (nat_to_imp x1) (nat_to_imp x3) (nat_to_imp x5) H).
    pose (result := sinhabitant converted).
    (* result has type R (imp_to_nat (nat_to_imp x1)) ... *)
    (* We need R x1 x3 x5, use from_to of nat_iso *)
    unfold imp_to_nat, nat_to_imp in result.
    pose (ft1 := from_to nat_iso x1).
    pose (ft3 := from_to nat_iso x3).
    pose (ft5 := from_to nat_iso x5).
    (* ft1 : from (to x1) = x1 in SProp, use eq_of_seq to convert to Prop *)
    rewrite (eq_of_seq ft1) in result.
    rewrite (eq_of_seq ft3) in result.
    rewrite (eq_of_seq ft5) in result.
    exact result.
  - (* to_from: SProp goal - SProp values are proof irrelevant *)
    intro H.
    constructor.
  - (* from_to: Prop goal - use proof irrelevance *)
    intro H.
    apply seq_of_peq_t.
    apply proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.R := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_R := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.R Original_LF__DOT__IndProp_LF_IndProp_R_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.R Imported.Original_LF__DOT__IndProp_LF_IndProp_R Original_LF__DOT__IndProp_LF_IndProp_R_iso := {}.
