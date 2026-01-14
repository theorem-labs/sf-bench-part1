From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From Stdlib Require Import ProofIrrelevance.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_and : SProp -> SProp -> SProp := Imported.and.

(* Helper to convert stdlib eq to IsomorphismDefinitions.eq for Props *)
Definition prop_eq_to_iso_eq : forall (P : Prop) (p1 p2 : P), p1 = p2 -> IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 H => match H with Logic.eq_refl => IsomorphismDefinitions.eq_refl end.

(* Helper functions for the isomorphism *)
Definition and_iso_to (x1 : Prop) (x2 : SProp) (H1 : Iso x1 x2) 
                      (x3 : Prop) (x4 : SProp) (H2 : Iso x3 x4)
  : (x1 /\ x3) -> imported_and x2 x4 :=
  fun p => match p with
           | conj p1 p3 => Imported.and_intro x2 x4 (H1 p1) (H2 p3)
           end.

Definition and_iso_from (x1 : Prop) (x2 : SProp) (H1 : Iso x1 x2) 
                        (x3 : Prop) (x4 : SProp) (H2 : Iso x3 x4)
  : imported_and x2 x4 -> (x1 /\ x3) :=
  fun q => conj (from H1 (@Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso__hyg7 x2 x4 q))
                (from H2 (@Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso__hyg9 x2 x4 q)).

Instance and_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (and x1 x3) (imported_and x2 x4)).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  apply Build_Iso with (to := and_iso_to H1 H2) (from := and_iso_from H1 H2).
  - (* to_from *)
    intro x. unfold and_iso_to, and_iso_from. simpl.
    pose proof (to_from H1 (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso__hyg7 x2 x4 x)) as E1.
    pose proof (to_from H2 (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso__hyg9 x2 x4 x)) as E2.
    refine (eq_trans (f_equal2 (Imported.and_intro x2 x4) E1 E2) _).
    exact IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. unfold and_iso_to, and_iso_from. simpl.
    (* Since x1 /\ x3 is a Prop, we can use proof irrelevance *)
    apply prop_eq_to_iso_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor and and_iso := {}.
Instance: IsoStatementProofBetween and Imported.and and_iso := {}.