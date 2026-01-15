From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev.

(* Short names for convenience *)
Definition ev_orig := Original.LF_DOT_IndProp.LF.IndProp.ev.
Definition ev_imp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev.

(* Forward direction: construct ev_imp from ev_orig *)
Definition ev_to_imported : forall n : nat, ev_orig n -> ev_imp (nat_to_imported n).
Proof.
  refine (fix F n H {struct H} := _).
  destruct H as [|n' H'].
  - exact Imported.Original_LF__DOT__IndProp_LF_IndProp_ev_ev_0.
  - exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev_ev_SS (nat_to_imported n') (F n' H')).
Defined.

(* Backward direction using SInhabited *)
Fixpoint ev_from_imported_SInhabited (n : imported_nat)
  (H : ev_imp n)
  {struct H} : SInhabited (ev_orig (imported_to_nat n)).
Proof.
  destruct H.
  - apply sinhabits. exact Original.LF_DOT_IndProp.LF.IndProp.ev_0.
  - apply sinhabits.
    exact (Original.LF_DOT_IndProp.LF.IndProp.ev_SS _ 
             (sinhabitant (ev_from_imported_SInhabited n H))).
Defined.

Definition ev_from_imported (n : imported_nat) (H : ev_imp n) : ev_orig (imported_to_nat n) :=
  sinhabitant (@ev_from_imported_SInhabited n H).

(* Transport using the IsomorphismDefinitions.eq *)
Definition ev_iso_to (x1 : nat) (x2 : imported_nat) 
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2) 
  (Hev : ev_orig x1) : ev_imp x2 :=
  match Hx in (IsomorphismDefinitions.eq _ y) return ev_imp y with
  | IsomorphismDefinitions.eq_refl => @ev_to_imported x1 Hev
  end.

Definition ev_iso_from (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : ev_imp x2) : ev_orig x1 :=
  let H' := match Hx in (IsomorphismDefinitions.eq _ y) return ev_imp y -> ev_imp (nat_to_imported x1) with
            | IsomorphismDefinitions.eq_refl => fun h => h
            end H in
  let H'' := @ev_from_imported (nat_to_imported x1) H' in
  match nat_roundtrip x1 in (_ = m) return ev_orig m with
  | Logic.eq_refl => H''
  end.

Require Import Stdlib.Logic.ProofIrrelevance.

(* Convert proof irrelevance to SProp equality for Prop types *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_ev_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.ev x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev x2).
Proof.
  intros x1 x2 Hx.
  simpl in Hx.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_ev.
  refine {|
    to := @ev_iso_to x1 x2 Hx;
    from := @ev_iso_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev Original_LF__DOT__IndProp_LF_IndProp_ev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev Imported.Original_LF__DOT__IndProp_LF_IndProp_ev Original_LF__DOT__IndProp_LF_IndProp_ev_iso := {}.