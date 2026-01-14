From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq : forall x : Type, x -> x -> SProp := (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq).

(* Both Original.eq and Imported.eq are singleton types (in Prop and SProp respectively).
   The isomorphism between them is essentially trivial because:
   1. Both have exactly one constructor (eq_refl)
   2. For any two proofs of the same statement, they are equal (proof irrelevance)
   
   The key insight is that both Prop and SProp have proof irrelevance, so any two
   inhabitants of these types are indistinguishable. We can build the isomorphism
   by mapping any proof to any proof.
   
   rel_iso Hx x y means: IsomorphismDefinitions.eq (to Hx x) y (in SProp)
*)

(* Helper: any two proofs of a Prop are equal in SProp *)
Lemma sprop_proof_irrel : forall (A : Prop) (x y : A), IsomorphismDefinitions.eq x y.
Proof. 
  intros.
  assert (H : x = y) by apply ProofIrrelevance.proof_irrelevance.
  destruct H.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.eq x3 x5) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x4 x6).
Proof.
  intros x1 x2 Hx x3 x4 Hx0 x5 x6 Hx1.
  (* Both Original.eq (Prop) and Imported.eq (SProp) are proof-irrelevant singleton types.
     The isomorphism is straightforward because:
     - We can eliminate from Prop to SProp (and vice versa with appropriate constructions)
     - The round-trip proofs to_from and from_to are in SProp, so any proof works *)
  
  unshelve eapply Build_Iso.
  - (* to: Original.eq x3 x5 -> Imported.eq x4 x6 *)
    intro e.
    destruct e.
    (* Now x3 = x5 definitionally (both are x), and:
       Hx0 : rel_iso Hx x x4, i.e., eq (to Hx x) x4
       Hx1 : rel_iso Hx x x6, i.e., eq (to Hx x) x6
       So by transitivity: eq x4 x6 *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym Hx0) Hx1) as H46.
    exact (@IsoEq.eq_srect x2 x4 (fun y => Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x2 x4 y)
             (Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_eq_refl x2 x4) x6 H46).
  - (* from: Imported.eq x4 x6 -> Original.eq x3 x5 *)
    intro e.
    destruct e.
    (* Now x4 = x6 definitionally (both are x4), and:
       Hx0 : rel_iso Hx x3 x4, i.e., eq (to Hx x3) x4
       Hx1 : rel_iso Hx x5 x4, i.e., eq (to Hx x5) x4
       From these we can derive eq x3 x5 *)
    pose proof (IsoEq.eq_trans Hx0 (IsoEq.eq_sym Hx1)) as H_to.
    pose proof (IsoEq.f_equal (from Hx) H_to) as H_from.
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym (from_to Hx x3)) 
                (IsoEq.eq_trans H_from (from_to Hx x5))) as H35.
    exact (@IsoEq.eq_srect x1 x3 (fun y => Original.LF_DOT_ProofObjects.LF.ProofObjects.eq x3 y)
             (Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_refl x3) x5 H35).
  - (* to_from: in SProp *)
    intro e. 
    (* e : imported_eq x4 x6 (SProp), goal: eq (to (from e)) e (SProp) *)
    (* Since imported_eq is in SProp, any two inhabitants are equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: in SProp *)
    intro e.
    (* e : Original.eq x3 x5 (Prop), goal: eq (from (to e)) e (SProp) *)
    (* Both from (to e) and e are proofs of the same Prop, so by proof irrelevance they are equal. *)
    apply sprop_proof_irrel.
Defined.
Instance: KnownConstant (@Original.LF_DOT_ProofObjects.LF.ProofObjects.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_ProofObjects.LF.ProofObjects.eq) Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_ProofObjects.LF.ProofObjects.eq) (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq) Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso := {}.