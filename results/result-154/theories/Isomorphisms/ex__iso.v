From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Lemma leibniz_to_iso_eq_ex : forall (A : Type) (a b : A), a = b -> IsomorphismDefinitions.eq a b.
Proof.
  intros A a b H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma prop_to_iso_eq_ex : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2.
Proof.
  intros P p1 p2.
  apply leibniz_to_iso_eq_ex.
  apply proof_irrelevance.
Qed.

Definition imported_ex : forall x : Type, (x -> SProp) -> SProp := Imported.ex.

Instance ex_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp), (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) -> Iso (exists y, x3 y) (imported_ex x4).
Proof.
  intros x1 x2 hx P Q HP.
  unshelve eapply Build_Iso.
  - (* to: (exists y, P y) -> imported_ex Q *)
    intro H. destruct H as [w Hw].
    unfold imported_ex.
    apply (Imported.ex_intro x2 Q (to hx w)).
    (* rel_iso hx w (to hx w) is eq (to hx w) (to hx w) which is eq_refl *)
    apply (to (HP w (to hx w) IsomorphismDefinitions.eq_refl)).
    exact Hw.
  - (* from: imported_ex Q -> (exists y, P y) *)
    intro H.
    (* Use sinhabitant to extract from the SProp existential *)
    (* First build SInhabited (exists y : x1, P y) from H *)
    apply sinhabitant.
    (* Now need: SInhabited (exists y : x1, P y) *)
    (* Use the eliminator for Imported.ex to build SInhabited *)
    refine (Imported.ex_indl x2 Q (fun _ => SInhabited (exists y : x1, P y))
             (fun (w : x2) (Hw : Q w) => _)
             H).
    (* We have w : x2, Hw : Q w, need to build SInhabited (exists y : x1, P y) *)
    apply sinhabits.
    pose (w1 := from hx w).
    (* HP w1 (hx w1) eq_refl : Iso (P w1) (Q (hx w1)) *)
    (* We need Q (hx w1), but we have Q w *)
    (* Use to_from to transport: *)
    pose (Hw' := match to_from hx w in IsomorphismDefinitions.eq _ z return Q z -> Q (to hx w1) with
                 | IsomorphismDefinitions.eq_refl => fun x => x
                 end Hw).
    pose (Hw1 := from (HP w1 (to hx w1) IsomorphismDefinitions.eq_refl) Hw').
    exact (ex_intro _ w1 Hw1).
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. apply prop_to_iso_eq_ex.
Defined.

Instance: KnownConstant ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor ex ex_iso := {}.
Instance: IsoStatementProofBetween ex Imported.ex ex_iso := {}.