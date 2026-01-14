From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Now Imported.Corelib_Init_Logic_eq has type: forall x : Type, x -> x -> SProp *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Helper to get from SProp equality to Type equality *)
Definition sprop_eq_to_eq {A : Type} {x y : A} 
  (h : Imported.Corelib_Init_Logic_eq A x y) : Logic.eq x y :=
  Imported.Corelib_Init_Logic_eq_recl A x (fun z _ => Logic.eq x z) Logic.eq_refl y h.

(* Helper to get from Type equality to SProp equality *)
Definition eq_to_sprop_eq {A : Type} {x y : A}
  (h : Logic.eq x y) : Imported.Corelib_Init_Logic_eq A x y :=
  match h with
  | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_refl A x
  end.

(* Helper to convert IsomorphismDefinitions.eq (SProp) to Logic.eq (Type) *)
Definition iso_eq_to_logic_eq {A : Type} {x y : A}
  (h : IsomorphismDefinitions.eq x y) : Logic.eq x y :=
  @IsomorphismDefinitions.eq_rect A x (fun z _ => Logic.eq x z) Logic.eq_refl y h.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  { (* to *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq.
    apply eq_to_sprop_eq.
    apply iso_eq_to_logic_eq in H34.
    apply iso_eq_to_logic_eq in H56.
    exact (Logic.eq_trans (Logic.eq_sym H34) H56). }
  { (* from *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq in Heq.
    apply sprop_eq_to_eq in Heq.
    apply iso_eq_to_logic_eq in H34.
    apply iso_eq_to_logic_eq in H56.
    pose proof (iso_eq_to_logic_eq (from_to hx x3)) as Hft3.
    pose proof (iso_eq_to_logic_eq (from_to hx x5)) as Hft5.
    exact (Logic.eq_trans (Logic.eq_sym Hft3) 
             (Logic.eq_trans (Logic.f_equal (from hx) H34)
               (Logic.eq_trans (Logic.f_equal (from hx) Heq)
                 (Logic.eq_trans (Logic.f_equal (from hx) (Logic.eq_sym H56)) Hft5)))). }
  { (* to_from: SProp proof irrelevance *)
    intro s.
    (* s : imported_Corelib_Init_Logic_eq x4 x6 which is in SProp *)
    (* The goal is IsomorphismDefinitions.eq (to (from s)) s, also in SProp *)
    (* Since SProp is proof irrelevant, this is trivial *)
    exact IsomorphismDefinitions.eq_refl. }
  { (* from_to: round trip on Logic.eq *)
    intro Heq.
    (* Heq : x3 = x5, goal: eq (from (to Heq)) Heq *)
    (* Both sides are proofs of x3 = x5 which is in Prop *)
    (* Since the result needs to be in SProp (IsomorphismDefinitions.eq), we use proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance. }
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
