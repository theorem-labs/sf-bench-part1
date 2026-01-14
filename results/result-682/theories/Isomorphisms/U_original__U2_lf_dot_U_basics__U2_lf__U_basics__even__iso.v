From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_even : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_even.

(* Define the lemma using fix - n'' is structurally smaller than S (S n'') *)
Definition even_commutes : forall n, 
  IsomorphismDefinitions.eq 
    (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
    (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n)) :=
  fix IH (n : nat) : IsomorphismDefinitions.eq 
    (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
    (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n)) :=
  match n with
  | O => IsomorphismDefinitions.eq_refl
  | S O => IsomorphismDefinitions.eq_refl
  | S (S n'') => IH n''
  end.

Instance Original_LF__DOT__Basics_LF_Basics_even_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.even x1) (imported_Original_LF__DOT__Basics_LF_Basics_even x2).
Proof.
  intros x1 x2 Hx.
  unfold rel_iso in *. simpl in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_even.
  pose proof (even_commutes x1) as Hc.
  apply (eq_trans Hc).
  apply f_equal. exact Hx.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.even Original_LF__DOT__Basics_LF_Basics_even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.even Imported.Original_LF__DOT__Basics_LF_Basics_even Original_LF__DOT__Basics_LF_Basics_even_iso := {}.