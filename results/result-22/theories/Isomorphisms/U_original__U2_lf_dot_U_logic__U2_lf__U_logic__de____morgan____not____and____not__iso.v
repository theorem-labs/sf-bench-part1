From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* 
Original: forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q : Prop
Imported: forall P Q : SProp, Not (Lean.And (Not P) (Not Q)) -> Lean.Or P Q : SProp

We need to build an isomorphism between these two propositions.
Since both are propositions (one in Prop, one in SProp), the isomorphism is 
essentially showing they are logically equivalent, using proof irrelevance.
*)

Definition imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.

(* Helper: convert Prop False to SProp Imported.False *)
Definition prop_false_to_sprop_false (pf : Logic.False) : Imported.False :=
  match pf return Imported.False with end.
  
(* Better approach: use sinhabitant trick *)
Definition sprop_false_to_prop_false : Imported.False -> Logic.False.
Proof.
  intro sf.
  (* Imported.False is an empty SProp, so we can eliminate to any SProp *)
  (* Then extract from SInhabited *)
  exact (sinhabitant (Imported.False_indl (fun _ => SInhabited Logic.False) sf)).
Defined.

(* Helper: convert ~ inhabited P (Prop) to Imported.Not P (SProp) *)
Definition not_prop_to_not_sprop (P : SProp) (hnp : ~ inhabited P) : Imported.Not P.
Proof.
  unfold Imported.Not.
  intro hp.
  (* hp : P (SProp), we need Imported.False (SProp) *)
  (* hnp : inhabited P -> Logic.False *)
  (* So hnp (inhabits hp) : Logic.False *)
  exact (prop_false_to_sprop_false (hnp (inhabits hp))).
Defined.

(* Helper: convert Imported.Not (SProp) to ~ inhabited _ (Prop) *)
Definition not_sprop_to_not_prop (P : SProp) : Imported.Not P -> ~ inhabited P.
Proof.
  unfold Imported.Not, not.
  intros hnp [hp].
  exact (sprop_false_to_prop_false (hnp hp)).
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not_iso : Iso Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
Proof.
  (* 
  Original: forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q : Prop
  Imported: forall P Q : SProp, Not (Lean.And (Not P) (Not Q)) -> Lean.Or P Q : SProp
  *)
  unshelve eapply Build_Iso.
  - (* to: Original -> Imported *)
    unfold Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
    unfold Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
    intro orig_proof.
    (* Need: forall P Q : SProp, Not (Lean.And (Not P) (Not Q)) -> Lean.Or P Q *)
    intros P Q hnna.
    (* Apply the original proof with P' := inhabited P, Q' := inhabited Q *)
    pose proof (orig_proof (inhabited P) (inhabited Q)) as H.
    (* H : ~ (~ inhabited P /\ ~ inhabited Q) -> inhabited P \/ inhabited Q *)
    assert (~ (~ inhabited P /\ ~ inhabited Q)) as premise.
    {
      unfold not.
      intro hand.
      destruct hand as [np nq].
      (* hnna : Imported.Not (Lean.And (Imported.Not P) (Imported.Not Q))
         which is: Lean.And (Imported.Not P) (Imported.Not Q) -> Imported.False *)
      (* We need to prove False (Prop), so convert *)
      apply sprop_false_to_prop_false.
      apply hnna.
      apply (Lean.And_intro (Imported.Not P) (Imported.Not Q)).
      - exact (@not_prop_to_not_sprop P np).
      - exact (@not_prop_to_not_sprop Q nq).
    }
    pose proof (H premise) as Hconc.
    destruct Hconc as [[hp] | [hq]].
    + exact (Lean.Or_inl P Q hp).
    + exact (Lean.Or_inr P Q hq).
  - (* from: Imported -> Original *)
    unfold Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
    unfold Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
    intro imp_proof.
    (* Need: forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q *)
    intros P Q hnna.
    (* Apply the imported proof with P' := SInhabited P, Q' := SInhabited Q *)
    pose proof (imp_proof (SInhabited P) (SInhabited Q)) as H.
    (* H : Imported.Not (Lean.And (Imported.Not (SInhabited P)) (Imported.Not (SInhabited Q))) -> Lean.Or (SInhabited P) (SInhabited Q) *)
    assert (Imported.Not (Lean.And (Imported.Not (SInhabited P)) (Imported.Not (SInhabited Q)))) as premise.
    {
      unfold Imported.Not.
      intro hand.
      destruct hand as [np nq].
      (* np : SInhabited P -> Imported.False *)
      (* nq : SInhabited Q -> Imported.False *)
      (* We need Imported.False. But hnna : ~ (~ P /\ ~ Q) gives Logic.False *)
      (* We want to prove Logic.False from hnna, then convert to Imported.False *)
      apply prop_false_to_sprop_false.
      apply hnna.
      split.
      - intro hp. exact (sprop_false_to_prop_false (np (sinhabits hp))).
      - intro hq. exact (sprop_false_to_prop_false (nq (sinhabits hq))).
    }
    pose proof (H premise) as Hconc.
    (* We need to eliminate Lean.Or (SInhabited P) (SInhabited Q) which is in SProp 
       to get P \/ Q which is in Prop. Use Or_indl with motive producing an SProp,
       then convert. *)
    (* Actually, we can eliminate to inhabited (P \/ Q) since that's SProp *)
    pose proof (Imported.Or_indl (SInhabited P) (SInhabited Q) 
                  (fun _ => SInhabited (P \/ Q))
                  (fun sp => sinhabits (or_introl (sinhabitant sp)))
                  (fun sq => sinhabits (or_intror (sinhabitant sq)))
                  Hconc) as result.
    exact (sinhabitant result).
  - (* to_from: in SProp, proof is automatic *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: in Prop, use proof irrelevance *)
    intro x.
    (* x : Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not (which is a Prop) *)
    (* Both sides are proofs of the same Prop - use proof irrelevance *)
    exact (IsoEq.seq_of_peq_t (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ _ _)).
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not_iso := {}.