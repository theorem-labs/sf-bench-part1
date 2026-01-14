From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop takes SProp and returns equality over SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: extract equality from Imported.Corelib_Init_Logic_eq_Prop *)
Definition seq_to_eq_Prop {A : SProp} {x y : A} (H : Imported.Corelib_Init_Logic_eq_Prop A x y) : IsomorphismDefinitions.eq x y :=
  match H with Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => IsomorphismDefinitions.eq_refl _ end.

(* We define the isomorphism by providing explicit functions *)
Definition eq_iso_to_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

Definition eq_iso_from_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  (* Now we have: Hseq : Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
  (* We need to show x3 = x5 *)
  (* Since x1 : Type and x2 : SProp, we use from_to *)
  pose proof (seq_to_eq_Prop Hseq) as Hseq'.
  (* Hseq' : IsomorphismDefinitions.eq (to hx x3) (to hx x5) *)
  (* Use f_equal with from to get eq (from (to hx x3)) (from (to hx x5)) *)
  pose proof (IsoEq.f_equal (from hx) Hseq') as Hfrom.
  (* Hfrom : eq (from hx (to hx x3)) (from hx (to hx x5)) *)
  pose proof (from_to hx x3) as Hft3.
  pose proof (from_to hx x5) as Hft5.
  (* Hft3 : eq (from hx (to hx x3)) x3 *)
  (* Hft5 : eq (from hx (to hx x5)) x5 *)
  apply eq_of_seq.
  exact (IsoEq.eq_trans (IsoEq.eq_sym Hft3) (IsoEq.eq_trans Hfrom Hft5)).
Defined.

From Stdlib Require Import Logic.Eqdep_dec.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal_Prop : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + exact (@eq_iso_to_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + exact (@eq_iso_from_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    unfold eq_iso_from_Prop, eq_iso_to_Prop. simpl.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
