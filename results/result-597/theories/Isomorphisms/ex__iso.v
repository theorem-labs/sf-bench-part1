From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_ex : forall x : Type, (x -> SProp) -> SProp := Imported.ex.

Instance ex_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : forall _ : x1, Prop) (x4 : forall _ : x2, SProp) (_ : forall (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6), Iso (x3 x5) (x4 x6)),
   Iso (@ex x1 x3) (@imported_ex x2 x4)).
Proof.
  intros x1 x2 hx P1 P2 HP.
  unshelve eapply Build_Iso.
  - (* to: ex x1 P1 -> imported_ex x2 P2 *)
    intro He.
    destruct He as [w1 Hw1].
    pose (w2 := to hx w1).
    assert (Hrel' : rel_iso hx w1 w2).
    { unfold rel_iso. simpl. unfold w2. apply IsomorphismDefinitions.eq_refl. }
    pose (iso_P := HP w1 w2 Hrel').
    exact (Imported.ex_intro x2 P2 w2 (to iso_P Hw1)).
  - (* from: imported_ex x2 P2 -> ex x1 P1 *)
    intro Hi.
    (* We cannot destruct SProp directly into Prop. Use ex_indl instead. *)
    (* ex_indl eliminates to SProp, we use SInhabited as a bridge *)
    refine (sinhabitant _).
    revert Hi.
    apply (Imported.ex_indl x2 P2 (fun _ => SInhabited (@Logic.ex x1 P1))).
    intros w2 Hw2.
    pose (w1 := from hx w2).
    assert (Hrel' : rel_iso hx w1 (to hx w1)).
    { unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl. }
    pose (iso_P := HP w1 (to hx w1) Hrel').
    (* We need to transport Hw2 : P2 w2 to P2 (to hx w1) *)
    (* to hx w1 = to hx (from hx w2) = w2 by to_from *)
    pose (tf := to_from hx w2).
    (* tf : IsomorphismDefinitions.eq (to hx (from hx w2)) w2 *)
    (* = IsomorphismDefinitions.eq (to hx w1) w2 *)
    (* We need to transport along this eq *)
    pose (Hw2' := match tf in (IsomorphismDefinitions.eq _ y) return P2 y -> P2 (to hx w1) with
                  | IsomorphismDefinitions.eq_refl => fun x => x
                  end Hw2).
    apply sinhabits.
    exact (Logic.ex_intro P1 w1 (from iso_P Hw2')).
  - (* to_from *)
    intro Hi.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro He.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor ex ex_iso := {}.
Instance: IsoStatementProofBetween ex Imported.ex ex_iso := {}.