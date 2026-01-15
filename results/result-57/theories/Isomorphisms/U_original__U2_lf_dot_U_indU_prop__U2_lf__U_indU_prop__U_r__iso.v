From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import Logic.ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_R : imported_nat -> imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_R.

(* Conversion functions between nat and Imported.nat - recursive to compute definitionally *)
Fixpoint nat_to_imp (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to_imp m)
  end.

Fixpoint imp_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (imp_to_nat m)
  end.

(* Forward direction: Original R -> Imported R *)
(* Using fix instead of Fixpoint to handle dependent types better *)
#[local] Unset Implicit Arguments.
Definition R_fwd : forall (m n o : nat), Original.LF_DOT_IndProp.LF.IndProp.R m n o -> 
  Imported.Original_LF__DOT__IndProp_LF_IndProp_R (nat_to_imp m) (nat_to_imp n) (nat_to_imp o).
Proof.
  fix IH 4.
  intros m n o H.
  destruct H as [ | m' n' o' H' | m' n' o' H' | m' n' o' H' | m' n' o' H'].
  - (* c1: R 0 0 0 *)
    exact Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c1.
  - (* c2: R (S m') n' (S o') from R m' n' o' *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c2 (nat_to_imp m') (nat_to_imp n') (nat_to_imp o') (IH m' n' o' H')).
  - (* c3: R m' (S n') (S o') from R m' n' o' *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c3 (nat_to_imp m') (nat_to_imp n') (nat_to_imp o') (IH m' n' o' H')).
  - (* c4: R m' n' o' from R (S m') (S n') (S (S o')) *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c4 (nat_to_imp m') (nat_to_imp n') (nat_to_imp o') (IH (S m') (S n') (S (S o')) H')).
  - (* c5: R n' m' o' from R m' n' o' *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_c5 (nat_to_imp m') (nat_to_imp n') (nat_to_imp o') (IH m' n' o' H')).
Defined.
#[local] Set Implicit Arguments.

(* For the backward direction, we need to convert Imported.R (in SProp) to Original.R (in Prop) *)
(* The key insight: both R relations have identical structure, so if one is inhabited, so is the other *)

(* We use the imported induction principle which eliminates to SProp *)
(* Since Original.R is in Prop and Prop embeds in SProp via SInhabited, we can use sinhabitant *)

(* Backward direction: first we show Imported.R m n o -> SInhabited (Original.R ...) *)
(* Then use sinhabitant to get the Prop *)

#[local] Unset Implicit Arguments.
Definition R_imp_to_SInh : forall (im in_ io : Imported.nat),
  Imported.Original_LF__DOT__IndProp_LF_IndProp_R im in_ io ->
  SInhabited (Original.LF_DOT_IndProp.LF.IndProp.R (imp_to_nat im) (imp_to_nat in_) (imp_to_nat io)).
Proof.
  intros im in_ io HR.
  refine (Imported.Original_LF__DOT__IndProp_LF_IndProp_R_sind
    (fun im in_ io _ => SInhabited (Original.LF_DOT_IndProp.LF.IndProp.R (imp_to_nat im) (imp_to_nat in_) (imp_to_nat io)))
    _ _ _ _ _ im in_ io HR).
  - (* c1: R 0 0 0 *)
    exact (sinhabits Original.LF_DOT_IndProp.LF.IndProp.c1).
  - (* c2: R (S m') n' (S o') from R m' n' o' *)
    intros m' n' o' _ IH.
    destruct IH as [H].
    exact (sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c2 (imp_to_nat m') (imp_to_nat n') (imp_to_nat o') H)).
  - (* c3: R m' (S n') (S o') from R m' n' o' *)
    intros m' n' o' _ IH.
    destruct IH as [H].
    exact (sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c3 (imp_to_nat m') (imp_to_nat n') (imp_to_nat o') H)).
  - (* c4: R m' n' o' from R (S m') (S n') (S (S o')) *)
    intros m' n' o' _ IH.
    destruct IH as [H].
    exact (sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c4 (imp_to_nat m') (imp_to_nat n') (imp_to_nat o') H)).
  - (* c5: R n' m' o' from R m' n' o' *)
    intros m' n' o' _ IH.
    destruct IH as [H].
    exact (sinhabits (Original.LF_DOT_IndProp.LF.IndProp.c5 (imp_to_nat m') (imp_to_nat n') (imp_to_nat o') H)).
Defined.
#[local] Set Implicit Arguments.

(* Now we need to show that nat_to_imp and imp_to_nat are inverses *)
Fixpoint nat_to_imp_inv (n : nat) : Logic.eq (imp_to_nat (nat_to_imp n)) n :=
  match n with
  | O => Logic.eq_refl
  | S m => match nat_to_imp_inv m in Logic.eq _ m' return Logic.eq (S (imp_to_nat (nat_to_imp m))) (S m') with
           | Logic.eq_refl => Logic.eq_refl
           end
  end.

(* The backward function: transport the proof using the inverse lemmas *)
#[local] Unset Implicit Arguments.
Definition R_bwd (m n o : nat)
  (HR : Imported.Original_LF__DOT__IndProp_LF_IndProp_R (nat_to_imp m) (nat_to_imp n) (nat_to_imp o)) :
  Original.LF_DOT_IndProp.LF.IndProp.R m n o.
Proof.
  apply sinhabitant.
  pose proof (R_imp_to_SInh (nat_to_imp m) (nat_to_imp n) (nat_to_imp o) HR) as H.
  rewrite !nat_to_imp_inv in H.
  exact H.
Defined.
#[local] Set Implicit Arguments.

(* Now we can build the isomorphism. Note that the to_from and from_to need to use SProp equality *)
(* The iso relates x1 to x2 when x2 = to nat_iso x1 *)
Instance Original_LF__DOT__IndProp_LF_IndProp_R_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4) (x5 : nat) 
     (x6 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x5 x6),
   Iso (Original.LF_DOT_IndProp.LF.IndProp.R x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_R x2 x4 x6)).
Proof.
  intros x1 x2 H12 x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_R.
  destruct H12, H34, H56.
  (* Now we need Iso (Original.R x1 x3 x5) (Imported.R (to nat_iso x1) (to nat_iso x3) (to nat_iso x5)) *)
  (* But nat_iso converts nat to Imported.nat, so (to nat_iso x1) = nat_to_imp x1 definitionally? *)
  (* Check that to nat_iso = nat_to_imp *)
  change (to nat_iso x1) with (nat_to_imp x1).
  change (to nat_iso x3) with (nat_to_imp x3).
  change (to nat_iso x5) with (nat_to_imp x5).
  (* Now build the Iso *)
  apply (@Build_Iso (Original.LF_DOT_IndProp.LF.IndProp.R x1 x3 x5) 
                    (Imported.Original_LF__DOT__IndProp_LF_IndProp_R (nat_to_imp x1) (nat_to_imp x3) (nat_to_imp x5))
                    (@R_fwd x1 x3 x5)
                    (@R_bwd x1 x3 x5)).
  - (* to_from: for all y, R_fwd (R_bwd y) = y *)
    (* This is in SProp, so it's trivially true by proof irrelevance *)
    intro y. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: for all x, R_bwd (R_fwd x) = x *)
    (* This is in Prop, so we need proof irrelevance *)
    intro x.
    pose proof (proof_irrelevance (Original.LF_DOT_IndProp.LF.IndProp.R x1 x3 x5) (R_bwd x1 x3 x5 (R_fwd x1 x3 x5 x)) x) as H.
    destruct H.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.R := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_R := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.R Original_LF__DOT__IndProp_LF_IndProp_R_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.R Imported.Original_LF__DOT__IndProp_LF_IndProp_R Original_LF__DOT__IndProp_LF_IndProp_R_iso := {}.