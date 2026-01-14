From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

(* Since x1 is isomorphic to an SProp x2, x1 should be a subsingleton.
   We use Streicher's K axiom to handle equality proofs. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  
  (* Prove x3 = x5 using the isomorphism *)
  assert (x3_eq_x5 : x3 = x5).
  { pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    apply eq_of_seq in Hft3.
    apply eq_of_seq in Hft5.
    rewrite <- Hft3, <- Hft5.
    reflexivity. }
  
  (* Subst x5 with x3 *)
  subst x5.
  
  refine {|
    to := fun e => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4;
    from := fun _ => Logic.eq_refl;
    to_from := _;
    from_to := _
  |}.
  - (* to_from: proof irrelevance in SProp *)
    intros e. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: e : x3 = x3, show eq_refl = e *)
    intros e.
    apply seq_of_eq.
    (* Use UIP / K: any proof of x = x is eq_refl *)
    (* Since x1 is isomorphic to SProp, it is a subsingleton, hence UIP holds *)
    apply UIP.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
