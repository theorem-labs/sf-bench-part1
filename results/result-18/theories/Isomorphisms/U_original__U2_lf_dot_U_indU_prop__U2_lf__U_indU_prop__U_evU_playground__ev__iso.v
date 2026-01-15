From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

(* Define SProp unit type for trivial cases *)
Inductive sUnit : SProp := sI.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.

(* Short names for convenience *)
Definition ev_orig := Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev.
Definition ev_imp := Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.

(* Helper: construct ev_imp from nat, using same structure as ev *)
Fixpoint ev_to_imported (n : Datatypes.nat) (H : ev_orig n) {struct H} : ev_imp (nat_to_imported n).
Proof.
  destruct H as [|n' H'].
  - exact Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_ev_0.
  - exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_ev_SS 
             (nat_to_imported n') (ev_to_imported n' H')).
Defined.

(* For the reverse direction: we use structural recursion on the imported nat *)
(* Build SInhabited (ev_orig n) from ev_imp (nat_to_imported n) *)
(* We use _indl to eliminate ev_imp to SProp (SInhabited) *)
Fixpoint ev_from_imported_sinhabited (n : Datatypes.nat) (H : ev_imp (nat_to_imported n)) {struct n} : 
  SInhabited (ev_orig n).
Proof.
  destruct n as [|n'].
  - (* ev_imp 0 -> ev_orig 0 *)
    exact (sinhabits Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev_0).
  - destruct n' as [|n''].
    + (* ev_imp (S 0) - impossible, but we need to return something in SProp *)
      simpl in H.
      (* Use indl to extract - for odd numbers ev is uninhabited, so we can return anything *)
      exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_indl
               (fun m _ => match m with 
                           | Imported.nat_S Imported.nat_O => SInhabited (ev_orig 1)
                           | _ => sUnit
                           end)
               sI
               (fun m _ _ => sI)
               (Imported.nat_S Imported.nat_O) H).
    + (* ev_imp (S (S n'')) -> ev_orig (S (S n'')) *)
      simpl in H.
      (* Extract ev_imp n'' from H using indl *)
      pose proof (Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_indl
                    (fun m _ => match m with 
                                | Imported.nat_S (Imported.nat_S k) => ev_imp k
                                | _ => sUnit
                                end)
                    sI
                    (fun m Hm _ => Hm)
                    (Imported.nat_S (Imported.nat_S (nat_to_imported n''))) H) as H'.
      simpl in H'.
      apply sinhabits.
      apply Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev_SS.
      exact (sinhabitant (ev_from_imported_sinhabited n'' H')).
Defined.

Definition ev_from_imported (n : Datatypes.nat) (H : ev_imp (nat_to_imported n)) : ev_orig n :=
  sinhabitant (ev_from_imported_sinhabited n H).

(* Now we can define the isomorphism *)
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
  @ev_from_imported x1 H'.

Require Import Stdlib.Logic.ProofIrrelevance.

(* Convert proof irrelevance to SProp equality for Prop types *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

Instance Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2),
   Iso (Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x2)).
Proof.
  intros x1 x2 Hx.
  simpl in Hx.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.
  refine {|
    to := @ev_iso_to x1 x2 Hx;
    from := @ev_iso_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev Imported.Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso := {}.
