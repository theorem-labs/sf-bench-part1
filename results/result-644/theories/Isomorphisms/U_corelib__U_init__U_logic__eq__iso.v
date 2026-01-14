From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The interface expects SProp equality. Now Imported.Corelib_Init_Logic_eq is in SProp. *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp :=
  @Imported.Corelib_Init_Logic_eq.

(* Helper function for the to direction *)
Definition eq_iso_to (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2)
  (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) 
  (H56 : @rel_iso x1 x2 hx x5 x6) (Heq : @Corelib.Init.Logic.eq x1 x3 x5)
  : @Imported.Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  destruct Heq.
  (* H34 : eq (to hx x3) x4, H56 : eq (to hx x3) x6, so x4 = x6 *)
  (* We need Imported.Corelib_Init_Logic_eq x4 x6, i.e. x4 = x6 in the imported SProp eq *)
  (* We have rel_iso which gives us to hx x3 = x4 and to hx x5 = x6 *)
  (* Since x3 = x5, we get to hx x3 = to hx x5, so x4 = x6 *)
  pose proof (eq_trans (eq_sym H34) H56) as H.
  exact (match H in IsomorphismDefinitions.eq _ y return Imported.Corelib_Init_Logic_eq x2 x4 y with
         | IsomorphismDefinitions.eq_refl => Imported.Corelib_Init_Logic_eq_refl x2 x4
         end).
Defined.

(* Helper function for the from direction *)  
Definition eq_iso_from (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2)
  (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2)
  (H56 : @rel_iso x1 x2 hx x5 x6) (Heq : @Imported.Corelib_Init_Logic_eq x2 x4 x6)
  : @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  (* Heq : Imported.Corelib_Init_Logic_eq x4 x6, which is in SProp *)
  (* We need Logic.eq x3 x5 *)
  (* Since Heq is in SProp, we can use destruct directly *)
  destruct Heq.
  (* Now we have x4 = x6, i.e., to hx x3 = to hx x5 (from H34 and H56) *)
  apply eq_of_seq.
  pose proof (from_to hx x3) as Hft3.
  pose proof (from_to hx x5) as Hft5.
  (* Hft3 : eq (from hx (to hx x3)) x3 *)
  (* Hft5 : eq (from hx (to hx x5)) x5 *)
  (* H34 : eq (to hx x3) x4 *)
  (* H56 : eq (to hx x5) x4 (since x6 = x4 after destruct) *)
  exact (eq_trans (eq_sym Hft3) (eq_trans (f_equal (from hx) H34) (eq_trans (f_equal (from hx) (eq_sym H56)) Hft5))).
Defined.

Require Import Stdlib.Logic.Eqdep_dec.

(* UIP for decidable types is available. For general types, we use proof irrelevance. *)
Lemma eq_iso_from_to (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2)
  (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2)
  (H56 : @rel_iso x1 x2 hx x5 x6) (Heq : @Corelib.Init.Logic.eq x1 x3 x5)
  : IsomorphismDefinitions.eq (@eq_iso_from x1 x2 hx x3 x4 H34 x5 x6 H56 (@eq_iso_to x1 x2 hx x3 x4 H34 x5 x6 H56 Heq)) Heq.
Proof.
  destruct Heq.
  (* Both are proofs of x3 = x3. We need UIP or proof irrelevance. *)
  (* Use proof irrelevance from SProp *)
  apply seq_of_eq.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq.
  exact {|
    to := @eq_iso_to x1 x2 hx x3 x4 H34 x5 x6 H56;
    from := @eq_iso_from x1 x2 hx x3 x4 H34 x5 x6 H56;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := @eq_iso_from_to x1 x2 hx x3 x4 H34 x5 x6 H56
  |}.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@imported_Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@imported_Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
