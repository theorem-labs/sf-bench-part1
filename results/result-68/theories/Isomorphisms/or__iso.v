From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* The fundamental approach: 
   We cannot pattern match on SProp to produce Prop.
   But we CAN:
   1. Pattern match on SProp to produce SProp
   2. Use the axiom eq_SInhabited_inhabited to relate SProp and Prop
   
   Key equations:
   - eq_SInhabited_inhabited : forall x : SProp, SInhabited (inhabited x) = x
   - sinhabitant : forall A : Prop, SInhabited A -> A
   
   Strategy:
   - Build an SProp function: Lean.Or x2 x4 -> SInhabited (x1 \/ x3)
     (We CAN pattern match on SProp to produce SProp)
   - Then use sinhabitant to extract the Prop
*)

(* Helper: convert Prop or to SProp imported_or *)
Definition or_to_imported_or {P Q : Prop} {P' Q' : SProp} 
    (iso_P : Iso P P') (iso_Q : Iso Q Q') : P \/ Q -> imported_or P' Q' :=
  fun pq => match pq with
    | or_introl p => Lean.Or_inl P' Q' (iso_P.(to) p)
    | or_intror q => Lean.Or_inr P' Q' (iso_Q.(to) q)
  end.

(* Helper: convert SProp imported_or to SProp SInhabited (or P Q) *)
(* This is SProp -> SProp, so pattern matching is allowed! *)
Definition imported_or_to_sinhabited_or {P Q : Prop} {P' Q' : SProp}
    (iso_P : Iso P P') (iso_Q : Iso Q Q') 
    : imported_or P' Q' -> SInhabited (P \/ Q) :=
  fun pq => match pq with
    | Lean.Or_inl _ _ p' => sinhabits (or_introl (iso_P.(from) p'))
    | Lean.Or_inr _ _ q' => sinhabits (or_intror (iso_Q.(from) q'))
  end.

(* Now we can build the from function using sinhabitant *)
Definition imported_or_to_or {P Q : Prop} {P' Q' : SProp}
    (iso_P : Iso P P') (iso_Q : Iso Q Q') 
    : imported_or P' Q' -> P \/ Q :=
  fun pq => sinhabitant (imported_or_to_sinhabited_or iso_P iso_Q pq).

Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (h1 : Iso x1 x2) (x3 : Prop) (x4 : SProp) (h2 : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)).
Proof.
  intros x1 x2 h1 x3 x4 h2.
  refine {|
    to := or_to_imported_or h1 h2;
    from := imported_or_to_or h1 h2;
  |}.
  - intro pq'. 
    (* to (from pq') = pq' in SProp *)
    (* In SProp, all proofs are equal, so this is trivial *)
    (* We use the fact that IsomorphismDefinitions.eq in SProp is proof irrelevant *)
    unfold imported_or_to_or, imported_or_to_sinhabited_or, or_to_imported_or.
    destruct pq' as [p' | q'].
    + (* Need: Or_inl (to h1 (from h1 p')) = Or_inl p' *)
      (* But there's sinhabitant in between - we need to handle that *)
      (* Actually, sinhabitant (sinhabits (or_introl ...)) needs to simplify first *)
      (* Use proof_irrelevance to equate sinhabitant (sinhabits x) with x *)
      simpl.
      set (lhs := sinhabitant (sinhabits (or_introl (from h1 p')))).
      assert (Hlhs : lhs = or_introl (from h1 p')) by (apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance).
      clearbody lhs.
      rewrite Hlhs.
      simpl. apply f_equal. apply h1.(to_from).
    + simpl.
      set (lhs := sinhabitant (sinhabits (or_intror (from h2 q')))).
      assert (Hlhs : lhs = or_intror (from h2 q')) by (apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance).
      clearbody lhs.
      rewrite Hlhs.
      simpl. apply f_equal. apply h2.(to_from).
  - intro pq.
    (* from (to pq) = pq *)
    unfold imported_or_to_or, imported_or_to_sinhabited_or, or_to_imported_or.
    destruct pq as [p | q].
    + simpl.
      set (lhs := sinhabitant (sinhabits (or_introl (from h1 (to h1 p))))).
      assert (Hlhs : lhs = or_introl (from h1 (to h1 p))) by (apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance).
      clearbody lhs.
      rewrite Hlhs.
      simpl. apply f_equal. apply h1.(from_to).
    + simpl.
      set (lhs := sinhabitant (sinhabits (or_intror (from h2 (to h2 q))))).
      assert (Hlhs : lhs = or_intror (from h2 (to h2 q))) by (apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance).
      clearbody lhs.
      rewrite Hlhs.
      simpl. apply f_equal. apply h2.(from_to).
Defined.

Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.