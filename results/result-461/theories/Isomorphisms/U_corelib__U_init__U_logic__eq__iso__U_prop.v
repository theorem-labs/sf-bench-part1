From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

From Stdlib Require Import Logic.Eqdep_dec.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal_prop : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop (SProp in imported), we need a version that works with Type->SProp isomorphisms *)
(* Since x2 : SProp is proof irrelevant, and x4, x6 : x2, we use that fact *)

(* Helper to extract eq from the imported SProp equality *)
Definition seq_prop_to_eq {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) {x3 x5 : x1}
  (H : Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) : x3 = x5.
Proof.
  (* Since x2 is SProp and hx is an isomorphism, we need to show x3 = x5 *)
  (* The from function gives us back x1 elements from x2 elements *)
  (* Since all elements in SProp are equal, to hx x3 = to hx x5 in SProp *)
  (* So from (to hx x3) = from (to hx x5) *)
  (* Therefore x3 = x5 *)
  pose proof (from_to hx x3) as E3.
  pose proof (from_to hx x5) as E5.
  destruct E3. destruct E5.
  reflexivity.
Defined.

(* Use a lemma for the roundtrip proof *)
Lemma seq_prop_roundtrip {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 : x1) :
  seq_prop_to_eq hx (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)) = Logic.eq_refl.
Proof.
  apply eq_proofs_equal_prop.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + intro Hseq.
    destruct H34. destruct H56.
    exact (seq_prop_to_eq hx Hseq).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    (* Use the roundtrip lemma *)
    rewrite seq_prop_roundtrip.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
