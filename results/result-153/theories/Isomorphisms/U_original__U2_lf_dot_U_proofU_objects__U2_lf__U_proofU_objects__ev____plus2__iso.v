From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2 : SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2.

Require Import Stdlib.Logic.ProofIrrelevance.

(* Helper: transport ev along IsomorphismDefinitions.eq *)
Definition transport_ev {m n : Imported.nat} 
  (Heq : IsomorphismDefinitions.eq m n)
  (Hev : Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev m) 
  : Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n.
Proof. destruct Heq. exact Hev. Defined.

(* We need a correspondence lemma for addition *)
Fixpoint add_correspondence (n_imp : Imported.nat) : 
  IsomorphismDefinitions.eq 
    (nat_to_imported (imported_to_nat n_imp + 2))
    (Imported.nat_add n_imp (Imported.nat_succ (Imported.nat_succ Imported.nat_zero))) :=
  match n_imp as m return 
    IsomorphismDefinitions.eq 
      (nat_to_imported (imported_to_nat m + 2))
      (Imported.nat_add m (Imported.nat_succ (Imported.nat_succ Imported.nat_zero)))
  with
  | Imported.nat_zero => IsomorphismDefinitions.eq_refl
  | Imported.nat_succ k => IsoEq.f_equal Imported.nat_succ (add_correspondence k)
  end.

Definition ev_plus2_to : Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2 -> 
                          Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2.
Proof.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2.
  intro H.
  intro n_imp.
  intro Hev_imp.
  pose proof (transport_ev (IsoEq.eq_sym (nat_to_from n_imp)) Hev_imp) as Hev_conv.
  pose proof (@ev_from_imported (imported_to_nat n_imp) Hev_conv) as Hev.
  specialize (H (imported_to_nat n_imp) Hev).
  apply (@ev_to_imported (imported_to_nat n_imp + 2)) in H.
  (* Transport H to the right index *)
  exact (transport_ev (add_correspondence n_imp) H).
Defined.

(* Correspondence for the other direction *)
Fixpoint add_correspondence2 (n : nat) :
  IsomorphismDefinitions.eq
    (Imported.nat_add (nat_to_imported n) (Imported.nat_succ (Imported.nat_succ Imported.nat_zero)))
    (nat_to_imported (n + 2)) :=
  match n as m return
    IsomorphismDefinitions.eq
      (Imported.nat_add (nat_to_imported m) (Imported.nat_succ (Imported.nat_succ Imported.nat_zero)))
      (nat_to_imported (m + 2))
  with
  | O => IsomorphismDefinitions.eq_refl
  | S k => IsoEq.f_equal Imported.nat_succ (add_correspondence2 k)
  end.

Definition ev_plus2_from : Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2 -> 
                            Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2.
Proof.
  intro H.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2.
  intros n Hev.
  apply (@ev_to_imported n) in Hev.
  specialize (H (nat_to_imported n) Hev).
  apply (@ev_from_imported (n + 2)).
  exact (transport_ev (add_correspondence2 n) H).
Defined.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2 imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2.
Proof.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2.
  refine (Build_Iso ev_plus2_to ev_plus2_from _ _).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x.
    pose proof (proof_irrelevance _ (ev_plus2_from (ev_plus2_to x)) x) as Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2 := {}. 
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2 := {}. 
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2 Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2 Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2 Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2_iso := {}.
