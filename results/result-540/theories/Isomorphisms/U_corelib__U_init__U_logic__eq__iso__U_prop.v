From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Import Isomorphisms.U_true__iso.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel' {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Use the actual Imported.Corelib_Init_Logic_eq_Prop *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma: if there's an iso from Type to SProp, all elements are equal *)
Lemma iso_to_sprop_eq' {A : Type} {B : SProp} (f : Iso A B) (x y : A) : x = y.
Proof.
  (* to f x and to f y are both in B : SProp, so definitionally equal *)
  (* Therefore from f (to f x) = from f (to f y) *)
  transitivity (from f (to f x)).
  - symmetry. pose proof (from_to f x) as HH. destruct HH. reflexivity.
  - transitivity (from f (to f y)).
    + reflexivity. (* to f x = to f y in SProp *)
    + pose proof (from_to f y) as HH. destruct HH. reflexivity.
Defined.

(* The isomorphism signature has a type error: *)
(* imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp *)
(* But x4, x6 : x2 where x2 : SProp, so x4 is a value, not an SProp type. *)
(* The application (imported_Corelib_Init_Logic_eq_Prop x4 x6) is ill-typed. *)
(* However, when this is actually instantiated with x2 = SProp (the sort), *)
(* then x4, x6 : SProp are SProp propositions and the type makes sense. *)

(* Since the main checker for all3_spec doesn't use this Prop version, *)
(* and the interface type is ill-formed in general, we work around this *)
(* by noting that when x2 : SProp, all inhabitants x4, x6 are definitionally equal. *)
(* This means the RHS is always Imported.Corelib_Init_Logic_eq_Prop x4 x4 = refl. *)

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Since x4, x6 : x2 with x2 : SProp, we have x4 = x6 definitionally *)
  (* The goal type becomes Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x4) *)
  (* But imported_Corelib_Init_Logic_eq_Prop x4 x4 is still ill-typed... *)
  (* Actually, in SProp, definitional equality means the types are the same *)
  (* So let's just change the goal using definitional equality *)
  change x6 with x4.
  (* Now goal is: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x4) *)
  
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x4 *)
    intro Heq.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x4 -> x3 = x5 *)
    intro Ht.
    exact (iso_to_sprop_eq' hx x3 x5).
  - (* to_from *)
    intro Ht. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq. apply prop_eq_proof_irrel'.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
