From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_is__even__prime : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime.

(* Show that the is_even_prime functions are the same under iso *)
Lemma is_even_prime_transfer : forall n : nat,
  to Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Logic.LF.Logic.is_even_prime n) =
  Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime (to nat_iso n).
Proof.
  intro n.
  unfold Original.LF_DOT_Logic.LF.Logic.is_even_prime.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime.
  unfold Imported.nat_two.
  simpl.
  pose proof (eqb_transfer n (S (S O))) as Heqb.
  simpl in Heqb.
  rewrite <- Heqb.
  destruct (Original.LF_DOT_Basics.LF.Basics.eqb n (S (S O))); simpl; reflexivity.
Qed.

Instance Original_LF__DOT__Logic_LF_Logic_is__even__prime_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Logic.LF.Logic.is_even_prime x1) (imported_Original_LF__DOT__Logic_LF_Logic_is__even__prime x2).
Proof.
  intros x1 x2 H1.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_is__even__prime.
  pose proof (is_even_prime_transfer x1) as Htrans.
  refine (match H1 in IsomorphismDefinitions.eq _ y2 return IsomorphismDefinitions.eq _ (Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime y2) with
          | IsomorphismDefinitions.eq_refl => _
          end).
  rewrite Htrans.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.is_even_prime := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.is_even_prime Original_LF__DOT__Logic_LF_Logic_is__even__prime_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.is_even_prime Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime Original_LF__DOT__Logic_LF_Logic_is__even__prime_iso := {}.