From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Build the isomorphism for equality *)
(* Both Corelib.Init.Logic.eq (Prop) and Imported.Corelib_Init_Logic_eq (SProp) are propositions *)
(* We need to transport using the SProp eliminators *)

(* Helper: transport along h34 : IsomorphismDefinitions.eq (to hx x3) x4 *)
(* Use eq_sind for SProp targets *)
Definition eq_iso_to_helper {x1 x2 : Type} (hx : Iso x1 x2) (x3 : x1) (x4 : x2) 
  (h34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6)
  (pf : x3 = x5) : Imported.Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  (* h34 : eq (to x3) x4 in SProp *)
  (* h56 : eq (to x5) x6 in SProp *)
  (* pf : x3 = x5 in Prop *)
  (* Goal: Imported.Corelib_Init_Logic_eq x2 x4 x6 in SProp *)
  subst x5.
  (* Now h34 and h56 both involve x3 *)
  (* h34 : eq (to x3) x4, h56 : eq (to x3) x6 *)
  (* Use eq_sind (SProp eliminator) for transporting to SProp target *)
  pose (base := Imported.Corelib_Init_Logic_eq_refl x2 (@to _ _ hx x3)).
  (* Transport base along h56 in the second argument *)
  pose (step1 := @IsomorphismDefinitions.eq_sind x2 (@to _ _ hx x3) 
    (fun y _ => Imported.Corelib_Init_Logic_eq x2 (@to _ _ hx x3) y) 
    base x6 h56).
  (* Transport step1 along h34 in the first argument *)
  exact (@IsomorphismDefinitions.eq_sind x2 (@to _ _ hx x3) 
    (fun y _ => Imported.Corelib_Init_Logic_eq x2 y x6) 
    step1 x4 h34).
Defined.

Definition eq_iso_from_helper {x1 x2 : Type} (hx : Iso x1 x2) (x3 : x1) (x4 : x2)
  (h34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6)
  (pf : Imported.Corelib_Init_Logic_eq x2 x4 x6) : x3 = x5.
Proof.
  (* Use from_to and transport *)
  pose proof (from_to hx x3) as ft3. (* eq (from (to x3)) x3 in SProp *)
  pose proof (from_to hx x5) as ft5. (* eq (from (to x5)) x5 in SProp *)
  (* h34 : eq (to x3) x4 in SProp *)
  (* h56 : eq (to x5) x6 in SProp *)
  (* pf : Imported eq x4 x6 in SProp *)
  
  (* Compute from x4 = from x6 from pf - use recl since result is Type (Prop) *)
  (* Use explicit Corelib.Init.Logic.eq for Prop equality *)
  pose proof (@Imported.Corelib_Init_Logic_eq_recl x2 x4 
    (fun y _ => Corelib.Init.Logic.eq (@from _ _ hx x4) (@from _ _ hx y))
    (Corelib.Init.Logic.eq_refl) x6 pf) as step1.
  (* step1 : from x4 = from x6 *)
  
  (* Build: from (to x3) = from x4 using h34 *)
  pose proof (@IsomorphismDefinitions.eq_rect x2 (@to _ _ hx x3) 
    (fun y _ => Corelib.Init.Logic.eq (@from _ _ hx (@to _ _ hx x3)) (@from _ _ hx y))
    (Corelib.Init.Logic.eq_refl) x4 h34) as step2.
  (* step2 : from (to x3) = from x4 *)
  
  (* Build: from x6 = from (to x5) using h56 *)
  pose proof (@IsomorphismDefinitions.eq_rect x2 (@to _ _ hx x5)
    (fun y _ => Corelib.Init.Logic.eq (@from _ _ hx y) (@from _ _ hx (@to _ _ hx x5)))
    (Corelib.Init.Logic.eq_refl) x6 h56) as step3.
  (* step3 : from x6 = from (to x5) *)
  
  (* Build: from (to x3) = x3 and from (to x5) = x5 *)
  pose proof (@IsomorphismDefinitions.eq_rect x1 (@from _ _ hx (@to _ _ hx x3))
    (fun y _ => Corelib.Init.Logic.eq y (@from _ _ hx (@to _ _ hx x3)))
    (Corelib.Init.Logic.eq_refl) x3 ft3) as step4.
  (* step4 : x3 = from (to x3) *)
  
  pose proof (@IsomorphismDefinitions.eq_rect x1 (@from _ _ hx (@to _ _ hx x5))
    (fun y _ => Corelib.Init.Logic.eq (@from _ _ hx (@to _ _ hx x5)) y)
    (Corelib.Init.Logic.eq_refl) x5 ft5) as step5.
  (* step5 : from (to x5) = x5 *)
  
  (* Chain: x3 = from(to x3) = from x4 = from x6 = from(to x5) = x5 *)
  transitivity (@from _ _ hx (@to _ _ hx x3)); [exact step4 |].
  transitivity (@from _ _ hx x4); [exact step2 |].
  transitivity (@from _ _ hx x6); [exact step1 |].
  transitivity (@from _ _ hx (@to _ _ hx x5)); [exact step3 |].
  exact step5.
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (h34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  apply Build_Iso with 
    (to := @eq_iso_to_helper x1 x2 hx x3 x4 h34 x5 x6 h56)
    (from := @eq_iso_from_helper x1 x2 hx x3 x4 h34 x5 x6 h56).
  - (* to_from: eq (to (from x)) x in SProp *)
    (* Imported.Corelib_Init_Logic_eq is in SProp, so SProp proof irrelevance applies *)
    intro pf. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: eq (from (to x)) x in SProp *)
    (* Need to show eq (eq_iso_from_helper ... (eq_iso_to_helper ... pf)) pf *)
    (* Both are proofs of x3 = x5, which is a Prop. Use proof irrelevance. *)
    intro pf.
    (* The goal is IsomorphismDefinitions.eq (...) pf where both are proofs of x3 = x5 *)
    (* Since x3 = x5 is a Prop, we can use proof irrelevance to convert to SProp eq *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance 
      (x3 = x5) 
      (@eq_iso_from_helper x1 x2 hx x3 x4 h34 x5 x6 h56 
        (@eq_iso_to_helper x1 x2 hx x3 x4 h34 x5 x6 h56 pf)) 
      pf) as H.
    exact (seq_of_eq H).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.