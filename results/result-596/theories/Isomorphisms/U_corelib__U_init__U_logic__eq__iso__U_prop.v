From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop is now in SProp (since we defined it as Prop in Lean) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: transport along IsomorphismDefinitions.eq to construct Imported.Corelib_Init_Logic_eq_Prop *)
Definition imported_eq_Prop_transport {A : SProp} {x y z : A} 
  (H1 : IsomorphismDefinitions.eq x y) (H2 : IsomorphismDefinitions.eq x z) 
  : Imported.Corelib_Init_Logic_eq_Prop A y z :=
  IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop A w z) 
    (IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop A x w) 
      (Imported.Corelib_Init_Logic_eq_Prop_refl A x) H2) H1.

(* Helper to convert Imported eq to IsomorphismDefinitions eq *)
Definition imported_eq_Prop_to_iso_eq {A : SProp} {x y : A} 
  (H : Imported.Corelib_Init_Logic_eq_Prop A x y) : IsomorphismDefinitions.eq x y :=
  Imported.Corelib_Init_Logic_eq_Prop_indl A x 
    (fun z _ => IsomorphismDefinitions.eq x z) 
    IsomorphismDefinitions.eq_refl y H.

(* Since we need equality in Prop but imported gives us SProp, we need to handle this carefully *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* This is a cross-universe isomorphism between eq (Prop) and eq (SProp) *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* H34 : rel_iso hx x3 x4, i.e. IsomorphismDefinitions.eq (to hx x3) x4 
       H56 : rel_iso hx x5 x6, i.e. IsomorphismDefinitions.eq (to hx x5) x6
       But x3 = x5 now after destruct, so we need Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    exact (imported_eq_Prop_transport H34 H56).
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    (* H34 : IsomorphismDefinitions.eq (to hx x3) x4 *)
    (* H56 : IsomorphismDefinitions.eq (to hx x5) x6 *)
    (* Heq : Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    (* Need: x3 = x5 (in Prop) *)
    pose proof (from_to hx x3) as Hx3.  (* eq (from hx (to hx x3)) x3 *)
    pose proof (from_to hx x5) as Hx5.  (* eq (from hx (to hx x5)) x5 *)
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34. (* eq (from hx (to hx x3)) (from hx x4) *)
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56. (* eq (from hx (to hx x5)) (from hx x6) *)
    (* Convert Heq to IsomorphismDefinitions.eq *)
    pose proof (imported_eq_Prop_to_iso_eq Heq) as HfeqHeq. (* eq x4 x6 *)
    pose proof (IsoEq.f_equal (from hx) HfeqHeq) as HfromHeq. (* eq (from hx x4) (from hx x6) *)
    (* x3 = from hx (to hx x3) = from hx x4 = from hx x6 = from hx (to hx x5) = x5 *)
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from *)
    intro Heq.
    (* SProp proof irrelevance - all proofs are equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
