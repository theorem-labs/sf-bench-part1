From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_and : SProp -> SProp -> SProp := Imported.and.

(* Build conversion functions *)
Definition and_to (x1 : Prop) (x2 : SProp) (iso1 : Iso x1 x2) (x3 : Prop) (x4 : SProp) (iso2 : Iso x3 x4) 
  (p : and x1 x3) : imported_and x2 x4 :=
  match p with
  | conj a b => @Imported.and_intro x2 x4 (@IsomorphismDefinitions.to x1 x2 iso1 a) (@IsomorphismDefinitions.to x3 x4 iso2 b)
  end.

Definition and_from (x1 : Prop) (x2 : SProp) (iso1 : Iso x1 x2) (x3 : Prop) (x4 : SProp) (iso2 : Iso x3 x4)
  (p : imported_and x2 x4) : and x1 x3 :=
  conj (@IsomorphismDefinitions.from x1 x2 iso1 (@Imported.left x2 x4 p)) (@IsomorphismDefinitions.from x3 x4 iso2 (@Imported.right x2 x4 p)).

(* Build the isomorphism for and *)
Instance and_iso : (forall (x1 : Prop) (x2 : SProp) (iso1 : Iso x1 x2) (x3 : Prop) (x4 : SProp) (iso2 : Iso x3 x4), Iso (and x1 x3) (imported_and x2 x4)).
Proof.
  intros x1 x2 iso1 x3 x4 iso2.
  unshelve eapply Build_Iso.
  - exact (and_to iso1 iso2).
  - exact (and_from iso1 iso2).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x as [a b].
    unfold and_from, and_to. simpl.
    (* Need to show: IsomorphismDefinitions.eq (conj (from iso1 (to iso1 a)) (from iso2 (to iso2 b))) (conj a b) *)
    pose proof (@IsomorphismDefinitions.from_to x1 x2 iso1 a) as H1.
    pose proof (@IsomorphismDefinitions.from_to x3 x4 iso2 b) as H2.
    (* Use IsoEq.f_equal2 *)
    exact (f_equal2 (@conj x1 x3) H1 H2).
Defined.
Instance: KnownConstant and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor and and_iso := {}.
Instance: IsoStatementProofBetween and Imported.and and_iso := {}.