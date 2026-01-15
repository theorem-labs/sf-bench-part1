From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Isomorphisms.U_s__iso.

Monomorphic Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4'' : forall (n : imported_nat),
  imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n ->
  imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_Nat_add (imported_S (imported_S (imported_S (imported_S imported_0)))) n) := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4''.
Arguments imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4'' n H : clear implicits.

Require Import Stdlib.Logic.ProofIrrelevance.

Monomorphic Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4''_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_ProofObjects.LF.ProofObjects.ev x1) (x4 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev x2),
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (Nat_add_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) hx))
    (Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus4'' x1 x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4'' x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hev.
  destruct hx as [Hn]. simpl in Hn.
  destruct Hn.
  destruct hev as [Hev]. simpl in Hev.
  constructor. simpl.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4''.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus4''.
  (* Both sides apply ev_SS twice. Since ev_to_imported maps ev_SS to ev_SS, *)
  (* the result should follow *)
  (* ev_to_imported is defined by fix on the ev proof structure *)
  (* ev_plus4'' x1 x3 = ev_SS (S (S x1)) (ev_SS x1 x3) *)
  (* We need: ev_to_imported (4 + x1) (ev_SS (S (S x1)) (ev_SS x1 x3)) *)
  (*        = Imported.ev_plus4'' (nat_to_imported x1) x4 *)
  (* The RHS unfolds to: ev_SS (S (S (nat_to_imported x1))) (ev_SS (nat_to_imported x1) x4) *)
  (* By the computation of ev_to_imported on ev_SS: *)
  (* ev_to_imported (4 + x1) (ev_SS (S (S x1)) H') *)
  (*   = ev_SS (nat_to_imported (S (S x1))) (ev_to_imported (S (S x1)) H') *)
  (* So we need Hev to relate x3 to x4 *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus4'' := {}.
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4'' := {}.
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus4'' Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4''_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus4'' Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4'' Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4''_iso := {}.
