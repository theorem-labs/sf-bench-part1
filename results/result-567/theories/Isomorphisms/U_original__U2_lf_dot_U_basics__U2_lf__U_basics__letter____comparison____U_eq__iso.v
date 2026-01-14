From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__letter____comparison__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq : forall x : imported_Original_LF__DOT__Basics_LF_Basics_letter,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_letter__comparison x x) imported_Original_LF__DOT__Basics_LF_Basics_Eq := Imported.Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq.

(* This is an isomorphism between axioms - both sides are axiomatic proofs of equality.
   The rel_iso condition says that the images under the isomorphism are equal.
   Since the target is in SProp (imported_Corelib_Init_Logic_eq is SProp-valued),
   all proofs are equal by proof irrelevance. *)
Instance Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.letter) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_letter) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_letter_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_letter__comparison_iso hx hx) Original_LF__DOT__Basics_LF_Basics_Eq_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_letter__comparison_iso hx hx) Original_LF__DOT__Basics_LF_Basics_Eq_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_letter__comparison x2 x2) imported_Original_LF__DOT__Basics_LF_Basics_Eq =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_letter__comparison_iso hx hx) Original_LF__DOT__Basics_LF_Basics_Eq_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.letter_comparison x1 x1 = Original.LF_DOT_Basics.LF.Basics.Eq =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_letter__comparison_iso hx hx) Original_LF__DOT__Basics_LF_Basics_Eq_iso) x)
    |} (Original.LF_DOT_Basics.LF.Basics.letter_comparison_Eq x1) (imported_Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq x2).
Proof.
  intros x1 x2 hx.
  (* rel_iso for this Iso means: 
     to (letter_comparison_Eq x1) = imported_letter_comparison_Eq x2 
     in SProp, all proofs are equal, so this is trivial *)
  unfold rel_iso. simpl.
  (* The target type is in SProp, so by proof irrelevance, the two sides are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.letter_comparison_Eq := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.letter_comparison_Eq Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.letter_comparison_Eq Imported.Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq Original_LF__DOT__Basics_LF_Basics_letter__comparison__Eq_iso := {}.