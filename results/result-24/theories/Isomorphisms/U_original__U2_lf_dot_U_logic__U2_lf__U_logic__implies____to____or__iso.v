From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)

(* The original is: forall P Q : Prop, (P -> Q) -> ~ P \/ Q : Prop *)
(* The imported is: forall P Q : SProp, (P -> Q) -> Lean.Or (Not P) Q : SProp *)

Definition imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_implies__to__or.

(* Build explicit functions between the two statement types *)
Definition to_imported : Original.LF_DOT_Logic.LF.Logic.implies_to_or -> imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or.
Proof.
  unfold Original.LF_DOT_Logic.LF.Logic.implies_to_or.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_implies__to__or.
  unfold Imported.Not.
  (* Original: forall P Q : Prop, (P -> Q) -> ~ P \/ Q *)
  (* Imported: forall P Q : SProp, (P -> Q) -> Lean.Or (P -> Imported.False) Q *)
  intro H.
  intros P Q HPQ.
  (* H : forall P Q : Prop, (P -> Q) -> ~P \/ Q *)
  (* Goal: Lean.Or (P -> Imported.False) Q where P Q : SProp *)
  (* Use inhabited to convert SProp to Prop *)
  pose proof (H (inhabited P) (inhabited Q)) as Hpq.
  assert (Himp : inhabited P -> inhabited Q).
  { intro hp. destruct hp as [p]. exact (inhabits (HPQ p)). }
  specialize (Hpq Himp).
  destruct Hpq as [Hnp | Hq].
  - left. intro p. 
    (* Hnp : ~ inhabited P, p : P *)
    (* Goal: Imported.False *)
    exfalso. apply Hnp. exact (inhabits p).
  - right. destruct Hq as [q]. exact q.
Defined.

Definition from_imported : imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or -> Original.LF_DOT_Logic.LF.Logic.implies_to_or.
Proof.
  unfold Original.LF_DOT_Logic.LF.Logic.implies_to_or.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_implies__to__or.
  intro H.
  intros P Q HPQ.
  (* H : forall P Q : SProp, (P -> Q) -> Lean.Or (Not P) Q *)
  (* Goal: ~ P \/ Q where P Q : Prop *)
  pose proof (H (SInhabited P) (SInhabited Q)) as Hpq.
  assert (Himp : SInhabited P -> SInhabited Q).
  { intro hp. destruct hp as [p]. exact (sinhabits (HPQ p)). }
  specialize (Hpq Himp).
  (* Hpq : Lean.Or (Imported.Not (SInhabited P)) (SInhabited Q) *)
  (* We need to convert this SProp disjunction to a Prop disjunction *)
  (* Use inhabited to wrap and then we can eliminate *)
  assert (Hpq_prop : inhabited (Lean.Or (Imported.Not (SInhabited P)) (SInhabited Q))).
  { exact (inhabits Hpq). }
  destruct Hpq_prop as [Hpq'].
  (* Now use Or_indl to analyze Hpq' *)
  (* But we need to produce a Prop, not an SProp... *)
  (* Actually we can use a trick: produce SInhabited (~ P \/ Q) and extract *)
  assert (Hresult : SInhabited (~ P \/ Q)).
  {
    revert Hpq'.
    apply Imported.Or_indl.
    - intro Hnp. apply sinhabits. left. intro p. 
      unfold Imported.Not in Hnp. 
      pose proof (Hnp (sinhabits p)) as Hfalse.
      destruct Hfalse.
    - intro Hq. apply sinhabits. right. exact (sinhabitant Hq).
  }
  exact (sinhabitant Hresult).
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso : Iso Original.LF_DOT_Logic.LF.Logic.implies_to_or imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or.
Proof.
  apply Build_Iso with (to := to_imported) (from := from_imported).
  (* to_from: forall x : SProp, eq (to (from x)) x - in SProp all proofs are equal *)
  - intro x. exact IsomorphismDefinitions.eq_refl.
  (* from_to: forall x : Prop, eq (from (to x)) x - use proof irrelevance *)
  - intro x. apply seq_of_eq. apply ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.implies_to_or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_implies__to__or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.implies_to_or Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.implies_to_or Imported.Original_LF__DOT__Logic_LF_Logic_implies__to__or Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso := {}.