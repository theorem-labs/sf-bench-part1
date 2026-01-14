From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Isomorphisms.U_s__iso.

(* 
   The original theorem not_even_1001' is Admitted in Original.v, 
   so we are allowed to admit the isomorphism.
   We need to prove that Imported.n1001 equals the expected representation,
   but both sides compute to the same value (S^1001(0)).
*)

(* Define the imported function by casting *)
Definition imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' : 
  imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 998 imported_0)))) -> imported_False.
Proof.
  intro H.
  (* We need to transport H to have type Even Imported.n1001 *)
  (* Both represent S^1001(0), but via different definitions *)
  (* Since they compute to the same value, we use a native_cast or proof *)
  assert (Heq : imported_S (imported_S (imported_S (iterate1 imported_S 998 imported_0))) = Imported.n1001).
  { unfold imported_S, imported_0, Imported.n1001, Imported.n998.
    (* This should be definitionally equal after unfolding *)
    native_compute. reflexivity. }
  rewrite Heq in H.
  exact (Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001' H).
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso : forall (x1 : Original.LF_DOT_Logic.LF.Logic.Even 1001) (x2 : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 998 imported_0))))),
  rel_iso
    {|
      to := Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 998 O imported_0 _0_iso))));
      from := from (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 998 O imported_0 _0_iso)))));
      to_from :=
        fun x : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 998 imported_0)))) =>
        to_from (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 998 O imported_0 _0_iso))))) x;
      from_to :=
        fun x : Original.LF_DOT_Logic.LF.Logic.Even 1001 =>
        seq_p_of_t (from_to (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 998 O imported_0 _0_iso))))) x)
    |} x1 x2 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.not_even_1001' x1) (imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001' x2).
Proof.
  intros x1 x2 Hrel.
  (* Both x1 and x2 are proofs of Even 1001, and the conclusion is about False values *)
  (* Since the results are both in SProp (imported_False), they are equal *)
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.not_even_1001' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_even_1001' Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_even_1001' Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001' Original_LF__DOT__Logic_LF_Logic_not__even__1001'_iso := {}.