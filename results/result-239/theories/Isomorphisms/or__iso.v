From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* Convert Rocq or to Imported.or - this works because we're going from Prop to SProp *)
Definition or_to_imported (P : Prop) (P' : SProp) (isoP : Iso P P') 
  (Q : Prop) (Q' : SProp) (isoQ : Iso Q Q') 
  (H : or P Q) : Imported.or P' Q' :=
  match H with
  | or_introl p => Imported.or_inl P' Q' (to isoP p)
  | or_intror q => Imported.or_inr P' Q' (to isoQ q)
  end.

(* Convert Imported.or to SInhabited (or P Q) - elimination from SProp to SProp is allowed *)
Definition imported_or_to_sinhabited (P : Prop) (P' : SProp) (isoP : Iso P P') 
  (Q : Prop) (Q' : SProp) (isoQ : Iso Q Q') 
  (H : Imported.or P' Q') : SInhabited (or P Q) :=
  match H with
  | Imported.or_inl _ _ p' => sinhabits (or_introl (from isoP p'))
  | Imported.or_inr _ _ q' => sinhabits (or_intror (from isoQ q'))
  end.

Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)).
Proof.
  intros P1 P2 isoP Q1 Q2 isoQ.
  unfold imported_or.
  unshelve refine {|
    to := fun H => @or_to_imported P1 P2 isoP Q1 Q2 isoQ H;
    from := fun H => sinhabitant (@imported_or_to_sinhabited P1 P2 isoP Q1 Q2 isoQ H)
  |}.
  - (* to_from *)
    intro H. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro H. apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant or := {}.
Instance: KnownConstant Imported.or := {}.
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.