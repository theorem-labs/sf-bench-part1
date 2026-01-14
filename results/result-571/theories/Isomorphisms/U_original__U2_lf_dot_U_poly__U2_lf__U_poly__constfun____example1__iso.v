From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__ftrue__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_constfun__example1 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_ftrue imported_0) imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example1.

(* Both Original.LF_DOT_Poly.LF.Poly.constfun_example1 and 
   Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example1 are axioms.
   We can use iso_SInhabited to prove the isomorphism between SProp proofs. *)
Instance Original_LF__DOT__Poly_LF_Poly_constfun__example1_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_ftrue_iso _0_iso) Original_LF__DOT__Basics_LF_Basics_true_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_ftrue_iso _0_iso) Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_ftrue imported_0) imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_ftrue_iso _0_iso) Original_LF__DOT__Basics_LF_Basics_true_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Poly.LF.Poly.ftrue 0 = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_ftrue_iso _0_iso) Original_LF__DOT__Basics_LF_Basics_true_iso) x)
    |} Original.LF_DOT_Poly.LF.Poly.constfun_example1 imported_Original_LF__DOT__Poly_LF_Poly_constfun__example1.
Proof.
  unfold rel_iso. simpl.
  (* The iso maps Prop equality to SProp equality. Since both are inhabited 
     (by the axiom on the original side and the imported axiom), 
     and the codomain is SProp, we can use proof irrelevance. *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.constfun_example1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.constfun_example1 Original_LF__DOT__Poly_LF_Poly_constfun__example1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.constfun_example1 Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example1 Original_LF__DOT__Poly_LF_Poly_constfun__example1_iso := {}.