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

Lemma even_iso_aux : forall (x1 : nat),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.even x1) (imported_Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported x1)).
Proof.
  fix IH 1.
  intros x1.
  destruct x1 as [| n1'].
  - (* O case *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* S case *)
    destruct n1' as [| n1''].
    + (* S O case *)
      simpl. apply IsomorphismDefinitions.eq_refl.
    + (* S (S n'') case *)
      simpl. apply IH.
Defined.

Instance Original_LF__DOT__Basics_LF_Basics_even_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.even x1) (imported_Original_LF__DOT__Basics_LF_Basics_even x2).
Proof.
  intros x1 x2 Hrel.
  destruct Hrel.
  apply even_iso_aux.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.even Original_LF__DOT__Basics_LF_Basics_even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.even Imported.Original_LF__DOT__Basics_LF_Basics_even Original_LF__DOT__Basics_LF_Basics_even_iso := {}.