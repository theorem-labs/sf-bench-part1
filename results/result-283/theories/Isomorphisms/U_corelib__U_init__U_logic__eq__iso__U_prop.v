From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop takes SProp values and returns SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.
Arguments imported_Corelib_Init_Logic_eq_Prop x%_type_scope _ _.

(* For SProp, we have proof irrelevance - all inhabitants are equal *)
(* The isomorphism between Corelib.Init.Logic.eq (when instantiated at Prop) and the imported version *)
(* Note: Prop in the original corresponds to SProp in imported *)
(* The Interface specifies (x1 : Type) not (x1 : Prop), but the hint is for Prop sorts *)
(* We use the fact that when used, x1 will be a Prop, so x3 = x5 is in Prop *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Both (x3 = x5) and (imported_Corelib_Init_Logic_eq_Prop x4 x6) are proposition types *)
  (* (x3 = x5) is a Prop, (imported_Corelib_Init_Logic_eq_Prop x4 x6) is an SProp *)
  (* We can build an iso between them *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop, Imported.Corelib_Init_Logic_eq_Prop.
    (* In SProp, all inhabitants are equal, so we just need to provide any inhabitant *)
    apply Imported.Corelib_Init_Logic_eq_refl_inst1.
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Heq.
    (* We need x3 = x5 in Type. Since hx : Iso x1 x2 where x2 : SProp, 
       there's an iso between x1 and an SProp. We use from_to to get equality. *)
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    (* H34 : eq (to hx x3) x4, H56 : eq (to hx x5) x6 *)
    (* In SProp, x4 = x6 trivially (proof irrelevance for SProp) *)
    (* to hx x3 = x4 and to hx x5 = x6, and x4 = x6 in SProp *)
    (* So to hx x3 = to hx x5 in SProp, which means from hx (to hx x3) = from hx (to hx x5) *)
    (* Combined with from_to: x3 = from hx (to hx x3) and x5 = from hx (to hx x5) *)
    apply eq_of_seq.
    apply (eq_trans (eq_sym Hx3)).
    apply (eq_trans (f_equal (from hx) H34)).
    apply (eq_trans (f_equal (from hx) (eq_sym H56))).
    exact Hx5.
  - (* to_from *)
    intro Heq.
    (* SProp proof irrelevance - all proofs are equal by definition *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    (* In Type, we need UIP or proof irrelevance for equality proofs *)
    (* Since from_to returns IsomorphismDefinitions.eq which is in SProp, this is trivial *)
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
