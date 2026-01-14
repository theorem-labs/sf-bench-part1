From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_s__iso.

(* The imported axiom uses forty_two which is S^42 0 *)
Definition imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 : forall x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat,
  imported_Original_LF__DOT__Logic_LF_Logic_In Imported.forty_two x ->
  imported_Corelib_Init_Logic_eq x (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat) -> imported_False := Imported.Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2.

(* First we need to show that forty_two corresponds to 42 *)
Lemma forty_two_is_42 : rel_iso nat_iso 42%nat Imported.forty_two.
Proof.
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.

(* The main isomorphism for the axiom. Since this is an axiom, we use iso_Prop_SProp 
   which works because both sides are propositions with the same logical content. *)
Instance Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.list Datatypes.nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2)
    (x3 : Original.LF_DOT_Logic.LF.Logic.In (42 : Datatypes.nat) x1)
    (x4 : imported_Original_LF__DOT__Logic_LF_Logic_In
            (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))))))))))))))))))))))))))))))))))))
            x2),
  rel_iso
    (Original_LF__DOT__Logic_LF_Logic_In_iso
       (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))))))))))))))))))))))))))))))))))
       hx)
    x3 x4 ->
  forall (x5 : x1 = Original.LF_DOT_Poly.LF.Poly.nil) (x6 : imported_Corelib_Init_Logic_eq x2 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso);
      from := from (Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq x2 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat) =>
        to_from (Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)) x;
      from_to := fun x : x1 = Original.LF_DOT_Poly.LF.Poly.nil => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)) x)
    |} x5 x6 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  (* Both sides are False/Original_False which are empty types, so the isomorphism is trivial *)
  unfold rel_iso. simpl.
  (* The to function of False_iso takes False to imported_False *)
  (* Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 returns False *)
  (* imported_... returns Imported.Original_False *)
  (* Since both are empty, the isomorphism is vacuously true *)
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 Imported.Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso := {}.
