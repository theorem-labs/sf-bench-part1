From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd' : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd'.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_snd'_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.snd' x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd' x2).
Proof.
  intros x1 x2 Hrel.
  unfold rel_iso in *.
  simpl in *.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_snd'.
  (* Hrel : eq (natprod_to_lean x1) x2 *)
  (* We need: eq (nat_to_lean (snd' x1)) (snd' x2) *)
  (* snd' x2 = snd' (natprod_to_lean x1) by Hrel *)
  (* So we can use f_equal snd' on Hrel *)
  pose proof (IsoEq.f_equal Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd' Hrel) as H.
  (* H : eq (snd' (natprod_to_lean x1)) (snd' x2) *)
  (* Now we need to show that snd' (natprod_to_lean x1) = nat_to_lean (snd' x1) *)
  destruct x1 as [n1 n2].
  simpl in *.
  (* H : eq (nat_to_lean n2) (snd' x2) *)
  (* Goal: eq (nat_to_lean n2) (snd' x2) *)
  exact H.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.snd' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.snd' Original_LF__DOT__Lists_LF_Lists_NatList_snd'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.snd' Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd' Original_LF__DOT__Lists_LF_Lists_NatList_snd'_iso := {}.