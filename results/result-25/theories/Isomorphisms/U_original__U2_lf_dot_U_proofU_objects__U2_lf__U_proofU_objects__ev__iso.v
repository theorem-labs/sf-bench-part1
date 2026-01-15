From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : imported_nat -> SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.

(* We need to prove that Original.ev n (in Prop) is isomorphic to Imported.ev (nat_to_imported n) (in SProp) *)

(* First establish that ev n -> Imported.ev (nat_to_imported n) *)
Lemma ev_to_imported : forall n : nat, Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n -> Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat_to_imported n).
Proof.
  fix IH 2.
  intros n Hev.
  destruct Hev as [ | m Hev'].
  - apply Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev_0.
  - apply Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev_SS.
    apply IH. exact Hev'.
Qed.

(* For the reverse direction: SProp to Prop *)
(* The key is that ev is decidable, and if it's true, we can construct the proof *)
(* If it's false, the SProp type is empty, so the function is vacuously total *)

Fixpoint even_nat (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S m) => even_nat m
  end.

Fixpoint ev_of_even (n : nat) : even_nat n = true -> Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n :=
  match n return even_nat n = true -> Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n with
  | O => fun _ => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_0
  | S O => fun H => match Bool.diff_false_true H with end
  | S (S m) => fun H => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_SS m (ev_of_even m H)
  end.

(* Define an SProp unit type for use in elimination *)
Inductive sUnit : SProp := stt : sUnit.

Fixpoint even_imported (m : Imported.nat) : bool :=
  match m with
  | Imported.nat_O => true
  | Imported.nat_S Imported.nat_O => false
  | Imported.nat_S (Imported.nat_S p) => even_imported p
  end.

(* Prove even is preserved by nat_to_imported *)
Lemma even_nat_to_imported : forall n, even_imported (nat_to_imported n) = even_nat n.
Proof.
  fix IH 1.
  intro n. destruct n as [| [| m]].
  - reflexivity.
  - reflexivity.
  - simpl. apply IH.
Qed.

(* If imported ev holds and even is false, we have a contradiction in SProp *)
Lemma imported_ev_false_absurd : forall m : Imported.nat, 
  even_imported m = false -> 
  Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev m -> Lean.sEmpty.
Proof.
  fix IH 3.
  intros m Hf Hev.
  destruct Hev as [ | p Hev'].
  - (* m = nat_O, but even_imported nat_O = true, contradiction *)
    discriminate Hf.
  - (* m = nat_S (nat_S p), Hev' : ev p *)
    (* even_imported (nat_S (nat_S p)) = false means even_imported p = false *)
    simpl in Hf.
    apply (IH p Hf Hev').
Qed.

(* Now we can define the reverse direction *)
Definition ev_from_imported (n : nat) (Hev : Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat_to_imported n)) : Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n.
Proof.
  destruct (even_nat n) eqn:E.
  - exact (ev_of_even n E).
  - (* even_nat n = false, derive contradiction *)
    apply Lean.sEmpty_rect.
    apply imported_ev_false_absurd with (m := nat_to_imported n).
    + exact (Logic.eq_trans (even_nat_to_imported n) E).
    + exact Hev.
Defined.

Require Import Stdlib.Logic.ProofIrrelevance.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2),
   Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.ev x1) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev x2)).
Proof.
  intros x1 x2 [Hrel].
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.
  simpl in Hrel.
  destruct Hrel.
  refine (@Build_Iso 
           (Original.LF_DOT_ProofObjects.LF.ProofObjects.ev x1)
           (Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat_to_imported x1))
           (@ev_to_imported x1)
           (@ev_from_imported x1)
           (fun _ => IsomorphismDefinitions.eq_refl)
           _).
  (* from_to: need eq (ev_from_imported (ev_to_imported e)) e *)
  intro e.
  (* Use proof irrelevance: both are proofs of ev x1 *)
  pose proof (proof_irrelevance _ (@ev_from_imported x1 (@ev_to_imported x1 e)) e) as H.
  destruct H.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso := {}.