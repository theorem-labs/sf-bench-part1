From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The imported version for SProp - use the one from Imported *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp, all proofs are equal (proof irrelevance in SProp) so we can use a simpler approach *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), 
  rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct Heq.
    (* x3 = x3, and we need Imported.eq' x2 x4 x6 *)
    (* We have H34 : eq (to hx x3) x4 and H56 : eq (to hx x3) x6 *)
    (* By transitivity via IsomorphismDefinitions.eq, we get x4 = x6 *)
    unfold imported_Corelib_Init_Logic_eq_Prop, Imported.Corelib_Init_Logic_eq_Prop.
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as H46.
    unfold Imported.Corelib_Init_Logic_eq_Prop.
    exact (eq_srect_nodep (fun z => Imported.eq'_inst1 x2 x4 z) 
           (Imported.eq'_refl_inst1 x2 x4) H46).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Heq.
    (* We have H34, H56 and Heq. We need x3 = x5 in Prop. *)
    (* from hx x4 = x3 (via from_to and H34) *)
    (* from hx x6 = x5 (via from_to and H56) *)
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    (* from hx (to hx x3) = x3 *)
    assert (from hx x4 = x3) as HX3.
    { apply eq_of_seq.
      exact (IsoEq.eq_trans 
        (f_equal (from hx) H34)
        FT3). }
    assert (from hx x6 = x5) as HX5.
    { apply eq_of_seq.
      exact (IsoEq.eq_trans 
        (f_equal (from hx) H56)
        FT5). }
    (* from hx x4 = from hx x6 *)
    (* We need to show from hx x4 = from hx x6 using Heq : eq'_inst1 x2 x4 x6 *)
    (* Use eq'_inst1_indl with motive returning SProp, then extract via sinhabitant *)
    pose proof (Imported.eq'_inst1_indl x2 x4 
        (fun z _ => SInhabited (from hx x4 = from hx z)) 
        (sinhabits Corelib.Init.Logic.eq_refl) x6 Heq) as HSInh.
    pose proof (sinhabitant HSInh) as Hfrom.
    exact (Corelib.Init.Logic.eq_trans 
           (Corelib.Init.Logic.eq_sym HX3) 
           (Corelib.Init.Logic.eq_trans Hfrom HX5)).
  - (* to_from *)
    intro Heq.
    (* Both sides in SProp, so trivially equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    (* All proofs of x3 = x3 are equal by proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
