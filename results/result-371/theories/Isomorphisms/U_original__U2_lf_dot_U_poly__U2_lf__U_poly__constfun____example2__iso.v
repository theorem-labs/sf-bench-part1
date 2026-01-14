From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__constfun__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

(* Define 5 and 99 in nat (Datatypes.nat) *)
Definition five_nat : Datatypes.nat := 5.
Definition ninetynine_nat : Datatypes.nat := 99.

(* Helper to build nat values as imported_nat *)
Fixpoint repeat_S (n : Datatypes.nat) : imported_nat :=
  match n with
  | Datatypes.O => Imported._0
  | Datatypes.S n' => Imported.S (repeat_S n')
  end.

Definition imported_five : imported_nat := repeat_S five_nat.
Definition imported_99 : imported_nat := repeat_S ninetynine_nat.

Lemma five_conv : repeat_S five_nat = Imported.five.
Proof. unfold five_nat, Imported.five, Imported.S, Imported._0. reflexivity. Qed.

Lemma ninetynine_conv : repeat_S ninetynine_nat = Imported.ninetynine.
Proof. unfold ninetynine_nat, Imported.ninetynine, Imported.S, Imported._0. reflexivity. Qed.

(* The imported statement *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_constfun__example2 : 
  imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_constfun imported_five imported_99)
    imported_five.
Proof.
  unfold imported_Corelib_Init_Logic_eq, imported_Original_LF__DOT__Poly_LF_Poly_constfun.
  unfold imported_five, imported_99.
  rewrite five_conv, ninetynine_conv.
  exact Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example2.
Qed.

(* Helper: build the S_iso chains (in SProp) *)
Definition S5_iso : rel_iso nat_iso five_nat imported_five.
Proof.
  unfold five_nat, imported_five, repeat_S.
  apply S_iso. apply S_iso. apply S_iso. apply S_iso. apply S_iso. apply _0_iso.
Defined.

Definition S99_iso : rel_iso nat_iso ninetynine_nat imported_99.
Proof.
  unfold ninetynine_nat, imported_99, repeat_S.
  do 99 apply S_iso. apply _0_iso.
Defined.

(* Wrap to get rel_iso_sort *)
Definition S5_iso_wrapped : rel_iso_sort (@RelaxIsoOrSort false _ _ nat_iso) five_nat imported_five :=
  {| unwrap_sprop := S5_iso |}.

Definition S99_iso_wrapped : rel_iso_sort (@RelaxIsoOrSort false _ _ nat_iso) ninetynine_nat imported_99 :=
  {| unwrap_sprop := S99_iso |}.

(* Build the constfun isomorphism *)
Definition constfun_5_99_iso : rel_iso_sort (@RelaxIsoOrSort false _ _ nat_iso) 
    (Original.LF_DOT_Poly.LF.Poly.constfun five_nat ninetynine_nat)
    (imported_Original_LF__DOT__Poly_LF_Poly_constfun imported_five imported_99).
Proof.
  apply (Original_LF__DOT__Poly_LF_Poly_constfun_iso (@RelaxIsoOrSort false _ _ nat_iso)
           five_nat imported_five S5_iso_wrapped S99_iso).
Defined.

(* The Iso for the equality type - using explicit argument application *)
Definition eq_iso_instance : Iso 
    (Original.LF_DOT_Poly.LF.Poly.constfun five_nat ninetynine_nat = five_nat)
    (imported_Corelib_Init_Logic_eq 
       (imported_Original_LF__DOT__Poly_LF_Poly_constfun imported_five imported_99)
       imported_five).
Proof.
  exact (@Corelib_Init_Logic_eq_iso nat imported_nat nat_iso 
           (Original.LF_DOT_Poly.LF.Poly.constfun five_nat ninetynine_nat)
           (imported_Original_LF__DOT__Poly_LF_Poly_constfun imported_five imported_99)
           (unwrap_sprop constfun_5_99_iso)
           five_nat imported_five
           S5_iso).
Defined.

(* The isomorphism between Original and Imported constfun_example2 *)
(* We use rel_iso_refl since eq_iso_instance maps the original proof to the imported proof *)
Instance Original_LF__DOT__Poly_LF_Poly_constfun__example2_iso : 
   rel_iso eq_iso_instance
   Original.LF_DOT_Poly.LF.Poly.constfun_example2 
   imported_Original_LF__DOT__Poly_LF_Poly_constfun__example2.
Proof.
  (* We need to show that applying the iso to the original statement gives the imported one *)
  (* rel_iso_refl gives us: rel_iso i x (i x) *)
  (* But we need to show that (i x) equals our imported statement *)
  (* Since both are in SProp, we can just use proof irrelevance *)
  pose proof (rel_iso_refl (i := eq_iso_instance) (x := Original.LF_DOT_Poly.LF.Poly.constfun_example2)) as H.
  (* H : rel_iso eq_iso_instance Original.LF_DOT_Poly.LF.Poly.constfun_example2 
               (eq_iso_instance Original.LF_DOT_Poly.LF.Poly.constfun_example2) *)
  (* The target type is in SProp, so any two inhabitants are equal *)
  exact H.
Qed.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.constfun_example2 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example2 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.constfun_example2 Original_LF__DOT__Poly_LF_Poly_constfun__example2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.constfun_example2 Imported.Original_LF__DOT__Poly_LF_Poly_constfun__example2 Original_LF__DOT__Poly_LF_Poly_constfun__example2_iso := {}.
