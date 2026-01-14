From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From LeanImport Require Import Lean.

Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Imported.

Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Since SProp is strictly proof-irrelevant, we can use eq_sind for rewriting *)
Definition eq_sind_gen {A : Type} {a : A} (P : A -> SProp) 
  (f : P a) {b : A} (e : IsomorphismDefinitions.eq a b) : P b :=
  match e in IsomorphismDefinitions.eq _ b return P b with
  | IsomorphismDefinitions.eq_refl => f
  end.

(* Helper: convert imported eq to standard eq via SProp elimination into Prop *)
Definition imported_eq_elim {A : Type} {x y : A} 
  (p : Imported.Corelib_Init_Logic_eq A x y) : x = y.
Proof.
  destruct p. reflexivity.
Defined.

(* For equality types: since both sides are proof-irrelevant, 
   we need to be careful about the types matching up *)

(* Build the iso after destructing H1 and H2 *)
Definition eq_iso_helper (x1 x2 : Type) (hx : Iso x1 x2) (x3 x5 : x1) :
  Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq x2 (to hx x3) (to hx x5)).
Proof.
  unshelve eapply Build_Iso.
  - (* to *)
    intro p. destruct p.
    exact (Imported.Corelib_Init_Logic_eq_refl x2 (to hx x3)).
  - (* from *)
    intro p.
    pose proof (imported_eq_elim p) as H.
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    pose proof (IsoEq.f_equal (from hx) (seq_of_eq H)) as H'.
    exact (eq_of_seq (eq_trans (eq_sym FT3) (eq_trans H' FT5))).
  - (* to_from *)
    intro p. exact IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro p. 
    (* The goal is IsomorphismDefinitions.eq (from (to p)) p 
       where from (to p) : x3 = x5 and p : x3 = x5.
       sUIPt gives us eq between two Prop equalities. *)
    apply sUIPt.
Defined.

(* Now use transport to handle the general case *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H1 x5 x6 H2.
  unfold rel_iso in H1, H2. simpl in H1, H2.
  (* H1 : IsomorphismDefinitions.eq (to hx x3) x4, H2 : IsomorphismDefinitions.eq (to hx x5) x6 *)
  destruct H1. destruct H2.
  exact (@eq_iso_helper x1 x2 hx x3 x5).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
