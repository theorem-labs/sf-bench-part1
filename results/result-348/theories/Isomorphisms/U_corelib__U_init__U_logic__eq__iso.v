From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Require Import Stdlib.Logic.ProofIrrelevance.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper for to direction *)
Definition Corelib_Init_Logic_eq_iso_to 
  (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (h34 : @rel_iso x1 x2 hx x3 x4) 
  (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6)
  (e : @Corelib.Init.Logic.eq x1 x3 x5) : @imported_Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  destruct e.
  simpl in *.
  assert (Heq' : IsomorphismDefinitions.eq x4 x6).
  { eapply eq_trans. eapply eq_sym. exact h34. exact h56. }
  destruct Heq'.
  exact (Imported.Corelib_Init_Logic_eq_refl x2 x4).
Defined.

(* Helper for from direction *)
Definition Corelib_Init_Logic_eq_iso_from
  (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (h34 : @rel_iso x1 x2 hx x3 x4) 
  (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6)
  (e : @imported_Corelib_Init_Logic_eq x2 x4 x6) : @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  unfold rel_iso in *. simpl in *.
  destruct e.
  assert (H : IsomorphismDefinitions.eq (to hx x3) (to hx x5)).
  { eapply eq_trans. exact h34. eapply eq_sym. exact h56. }
  assert (H2 : IsomorphismDefinitions.eq (from hx (to hx x3)) (from hx (to hx x5))).
  { apply f_equal. exact H. }
  assert (H3 : IsomorphismDefinitions.eq x3 (from hx (to hx x5))).
  { eapply eq_trans. eapply eq_sym. apply from_to. exact H2. }
  assert (H4 : IsomorphismDefinitions.eq x3 x5).
  { eapply eq_trans. exact H3. apply from_to. }
  destruct H4. exact Corelib.Init.Logic.eq_refl.
Defined.

(* from_to lemma using proof irrelevance *)
Lemma from_to_eq (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) 
  (h34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) 
  (h56 : @rel_iso x1 x2 hx x5 x6) (e : x3 = x5) :
  IsomorphismDefinitions.eq 
    (@Corelib_Init_Logic_eq_iso_from x1 x2 hx x3 x4 h34 x5 x6 h56
       (@Corelib_Init_Logic_eq_iso_to x1 x2 hx x3 x4 h34 x5 x6 h56 e))
    e.
Proof.
  apply seq_of_eq.
  apply proof_irrelevance.
Qed.

(* Build the isomorphism for equality *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  exact (Build_Iso 
    (@Corelib_Init_Logic_eq_iso_to x1 x2 hx x3 x4 h34 x5 x6 h56)
    (@Corelib_Init_Logic_eq_iso_from x1 x2 hx x3 x4 h34 x5 x6 h56)
    (fun y => match y with Imported.Corelib_Init_Logic_eq_refl _ _ => IsomorphismDefinitions.eq_refl end)
    (@from_to_eq x1 x2 hx x3 x4 h34 x5 x6 h56)).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.