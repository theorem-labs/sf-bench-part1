From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__csf__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_cs : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_cs.

(* Helper: convert from SProp eq to standard eq *)
Definition sprop_eq_to_prop_eq {A : Type} {x y : A} (H : Imported.Corelib_Init_Logic_eq A x y) : x = y :=
  match H in (Imported.Corelib_Init_Logic_eq _ _ z) return (x = z) with
  | Imported.Corelib_Init_Logic_eq_refl _ _ => Corelib.Init.Logic.eq_refl x
  end.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_cs_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.cs x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_cs x2 x4).
Proof.
  unfold rel_iso. simpl.
  intros x1 x2 H12 x3 x4 H34.
  unfold Original.LF_DOT_IndProp.LF.IndProp.cs.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_cs.
  (* Goal: Iso (csf x1 = x3) (Corelib_Init_Logic_eq (imported_csf x2) x4) *)
  
  (* Destruct H12 and H34 to simplify: x2 = nat_to_imported x1, x4 = nat_to_imported x3 *)
  destruct H12. destruct H34.
  (* Now goal: Iso (csf x1 = x3) (Corelib_Init_Logic_eq (imported_csf (nat_to_imported x1)) (nat_to_imported x3)) *)
  
  (* Both propositions express the same semantic content:
     - LHS: csf x1 = x3 (Prop eq on nat)
     - RHS: Corelib_Init_Logic_eq (imported_csf (nat_to_imported x1)) (nat_to_imported x3) (SProp eq on imported_nat)
     Since x1 <-> nat_to_imported x1 and csf commutes with nat_to_imported,
     these are logically equivalent. Use proof irrelevance for the round-trips. *)
  unshelve eapply Build_Iso.
  - (* to *)
    intro H. subst x3.
    pose proof (csf_commutes x1) as Hcsf_comm.
    unfold imported_Original_LF__DOT__IndProp_LF_IndProp_cs.
    exact (@eq_srect_r imported_nat 
             (Imported.Original_LF__DOT__IndProp_LF_IndProp_csf (nat_to_imported x1))
             (fun y => Imported.Corelib_Init_Logic_eq imported_nat (Imported.Original_LF__DOT__IndProp_LF_IndProp_csf (nat_to_imported x1)) y) 
             (Imported.Corelib_Init_Logic_eq_refl imported_nat _)
             (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.csf x1))
             Hcsf_comm).
  - (* from *)
    intro H.
    unfold imported_Original_LF__DOT__IndProp_LF_IndProp_cs in H.
    pose proof (sprop_eq_to_prop_eq H) as Hprop.
    pose proof (csf_commutes x1) as Hcsf_comm.
    pose proof (@eq_of_seq imported_nat _ _ Hcsf_comm) as Hcsf_comm'.
    pose proof (@eq_of_seq nat _ _ (nat_from_to (Original.LF_DOT_IndProp.LF.IndProp.csf x1))) as Hft_csf.
    pose proof (@eq_of_seq nat _ _ (nat_from_to x3)) as Hft3.
    (* Build the chain using eq_trans *)
    pose proof (Corelib.Init.Logic.eq_trans Hcsf_comm' Hprop) as Hmain.
    apply (Corelib.Init.Logic.f_equal imported_to_nat) in Hmain.
    exact (Corelib.Init.Logic.eq_trans (Corelib.Init.Logic.eq_sym Hft_csf) (Corelib.Init.Logic.eq_trans Hmain Hft3)).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply prop_eq_proof_irrel.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.cs := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_cs := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.cs Original_LF__DOT__IndProp_LF_IndProp_cs_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.cs Imported.Original_LF__DOT__IndProp_LF_IndProp_cs Original_LF__DOT__IndProp_LF_IndProp_cs_iso := {}.