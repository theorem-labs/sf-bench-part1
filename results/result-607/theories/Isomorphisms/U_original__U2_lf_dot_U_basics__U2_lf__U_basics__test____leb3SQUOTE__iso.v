From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__leb3' : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_S (imported_S imported_0)))
    imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__Basics_LF_Basics_test__leb3'.

(* Both Original.LF_DOT_Basics.LF.Basics.test_leb3' and Imported.Original_LF__DOT__Basics_LF_Basics_test__leb3' 
   are axioms (Admitted statements), so we need to prove they are related.
   Since the types are isomorphic and both are inhabited (by the axioms themselves),
   we can use the iso_SInhabited lemma. *)

(* First, let's compute what the iso type looks like *)
Definition the_iso := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (S_iso (S_iso _0_iso))) Original_LF__DOT__Basics_LF_Basics_false_iso.

(* The Imported type reduces to imported_Corelib_Init_Logic_eq applied to imported terms *)
(* We need to show rel_iso the_iso Original.LF_DOT_Basics.LF.Basics.test_leb3' imported_Original_LF__DOT__Basics_LF_Basics_test__leb3' *)

Instance Original_LF__DOT__Basics_LF_Basics_test__leb3'_iso : rel_iso
    {|
      to := to the_iso;
      from := from the_iso;
      to_from := to_from the_iso;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.leb 4 2 = Original.LF_DOT_Basics.LF.Basics.false =>
        seq_p_of_t (from_to the_iso x)
    |} Original.LF_DOT_Basics.LF.Basics.test_leb3' imported_Original_LF__DOT__Basics_LF_Basics_test__leb3'.
Proof.
  unfold rel_iso.
  (* We need to prove: to the_iso Original.LF_DOT_Basics.LF.Basics.test_leb3' = imported_Original_LF__DOT__Basics_LF_Basics_test__leb3' *)
  (* Both are in SProp (imported_Corelib_Init_Logic_eq ... ... is an SProp type) *)
  (* SProp terms are proof-irrelevant, so any two terms are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_leb3' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__leb3' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_leb3' Original_LF__DOT__Basics_LF_Basics_test__leb3'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_leb3' Imported.Original_LF__DOT__Basics_LF_Basics_test__leb3' Original_LF__DOT__Basics_LF_Basics_test__leb3'_iso := {}.