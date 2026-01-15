From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Unset Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Require Import Stdlib.Logic.ProofIrrelevance.

From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_Even : imported_nat -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

Definition Even_orig := Original.LF_DOT_Logic.LF.Logic.Even.
Definition Even_imp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

(* Proof irrelevance helper *)
Definition prop_proof_irrel_to_seq2 : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

(* Prove double_commutes gives us a Logic.eq *)
Lemma double_commutes_eq (n : nat) : 
  Logic.eq (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n)) 
           (Imported.Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported n)).
Proof.
  pose proof (double_commutes n) as H.
  apply eq_of_seq in H. exact H.
Qed.

(* Even_to: Prop -> SProp direction *)
Definition Even_to (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_orig x1) : Even_imp x2.
Proof.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even in H.
  unfold Even_imp, Imported.Original_LF__DOT__Logic_LF_Logic_Even.
  destruct H as [n Hn].
  apply (Imported.ex_intro Imported.nat _ (nat_to_imported n)).
  destruct Hx.
  subst x1.
  pose proof (double_commutes_eq n) as Hdc.
  rewrite Hdc.
  apply Imported.Corelib_Init_Logic_eq_refl.
Defined.

(* Helper: convert Imported.Corelib_Init_Logic_eq to Logic.eq *)
Definition imported_eq_to_logic_eq {A : Type} {x y : A} (H : Imported.Corelib_Init_Logic_eq A x y) : @Logic.eq A x y :=
  match H in (Imported.Corelib_Init_Logic_eq _ _ z) return @Logic.eq A x z with
  | Imported.Corelib_Init_Logic_eq_refl _ _ => Logic.eq_refl
  end.

(* Helper: convert imported double to original double *)
Lemma double_imported_to_orig (n : Imported.nat) :
  imported_to_nat (Imported.Original_LF__DOT__Induction_LF_Induction_double n) = 
  Original.LF_DOT_Induction.LF.Induction.double (imported_to_nat n).
Proof.
  pose proof (double_commutes_eq (imported_to_nat n)) as Hdc.
  rewrite imported_nat_roundtrip in Hdc.
  transitivity (imported_to_nat (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double (imported_to_nat n)))).
  - f_equal. symmetry. exact Hdc.
  - apply nat_roundtrip.
Qed.

(* Even_from: SProp -> Prop direction using SInhabited *)
Definition Even_from_SInhabited : forall (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_imp x2), SInhabited (Even_orig x1).
Proof.
  intros x1 x2 Hx H.
  unfold Even_imp, Imported.Original_LF__DOT__Logic_LF_Logic_Even in H.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even.
  destruct Hx.
  destruct H as [n Hn].
  apply sinhabits.
  exists (imported_to_nat n).
  pose proof (imported_eq_to_logic_eq Hn) as Hn'.
  transitivity (imported_to_nat (nat_to_imported x1)).
  - symmetry. apply nat_roundtrip.
  - transitivity (imported_to_nat (Imported.Original_LF__DOT__Induction_LF_Induction_double n)).
    + f_equal. exact Hn'.
    + apply double_imported_to_orig.
Defined.

Definition Even_from (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_imp x2) : Even_orig x1 :=
  sinhabitant (Even_from_SInhabited x1 x2 Hx H).

Instance Original_LF__DOT__Logic_LF_Logic_Even_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2), Iso (Original.LF_DOT_Logic.LF.Logic.Even x1) (imported_Original_LF__DOT__Logic_LF_Logic_Even x2)).
Proof.
  intros x1 x2 Hx.
  destruct Hx as [Hx]. simpl in Hx.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_Even.
  refine {|
    to := @Even_to x1 x2 Hx;
    from := @Even_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := fun e => prop_proof_irrel_to_seq2 _ _ _
  |}.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.Even := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_Even := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.Even Imported.Original_LF__DOT__Logic_LF_Logic_Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.
