From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import List.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. - disabled *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.list__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__tokenize____helper__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__string____of____list__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__list____of____string__iso.

Definition imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize : imported_String_string -> imported_list imported_String_string := Imported.Original_LF__DOT__ImpParser_LF_ImpParser_tokenize.

(* Helper: map preserves isomorphism for lists *)
Lemma map_string_of_list_iso : forall (l : list (list Ascii.ascii)),
  IsomorphismDefinitions.eq 
    ((list_iso String_string_iso).(to) (List.map Original.LF_DOT_ImpParser.LF.ImpParser.string_of_list l))
    (Imported.map _ _ Imported.Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list ((list_iso (list_iso Ascii_ascii_iso)).(to) l)).
Proof.
  fix IH 1.
  intros l.
  destruct l as [|h t].
  - (* l = [] *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* l = h :: t *)
    simpl.
    apply (IsoEq.f_equal2 (Imported.list_cons _)).
    + (* string_of_list h ~ imported_string_of_list (to h) *)
      set (h' := (list_iso Ascii_ascii_iso).(to) h).
      assert (Hrel : rel_iso (list_iso Ascii_ascii_iso) h h').
      { apply Build_rel_iso. unfold h'. simpl. apply IsomorphismDefinitions.eq_refl. }
      exact (proj_rel_iso (@Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list_iso h h' Hrel)).
    + (* IH on t *)
      apply IH.
Qed.

Instance Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso (list_iso String_string_iso) (Original.LF_DOT_ImpParser.LF.ImpParser.tokenize x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize x2).
Proof.
  intros x1 x2 Hx.
  unfold imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize.
  unfold Original.LF_DOT_ImpParser.LF.ImpParser.tokenize.
  unfold Imported.Original_LF__DOT__ImpParser_LF_ImpParser_tokenize.
  apply Build_rel_iso. simpl.
  
  (* Step 1: Apply map isomorphism *)
  eapply IsoEq.eq_trans.
  { apply map_string_of_list_iso. }
  
  (* Step 2: Now we need to show:
     Imported.map ... (to (tokenize_helper white [] (list_of_string x1))) 
     = Imported.map ... (Imported.tokenize_helper white [] (Imported.list_of_string x2)) *)
  apply (IsoEq.f_equal (Imported.map _ _ _)).
  
  (* Step 3: Show tokenize_helper results are equal *)
  (* Get the list_of_string iso: we need Hx as a rel_iso *)
  assert (HxR : rel_iso String_string_iso x1 x2).
  { exact Hx. }
  
  pose proof (@Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string_iso x1 x2 HxR) as Hlos.
  
  assert (Hwhite : rel_iso Original_LF__DOT__ImpParser_LF_ImpParser_chartype_iso 
    Original.LF_DOT_ImpParser.LF.ImpParser.white 
    Imported.Original_LF__DOT__ImpParser_LF_ImpParser_chartype_white).
  { apply Build_rel_iso. simpl. apply IsomorphismDefinitions.eq_refl. }
  
  assert (Hnil : rel_iso (list_iso Ascii_ascii_iso) nil (Imported.list_nil _)).
  { apply Build_rel_iso. simpl. apply IsomorphismDefinitions.eq_refl. }
  
  pose proof (@Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper_iso 
    Original.LF_DOT_ImpParser.LF.ImpParser.white
    Imported.Original_LF__DOT__ImpParser_LF_ImpParser_chartype_white
    Hwhite
    nil
    (Imported.list_nil _)
    Hnil
    (Original.LF_DOT_ImpParser.LF.ImpParser.list_of_string x1)
    (Imported.Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string x2)
    Hlos) as Hth.
  exact (proj_rel_iso Hth).
Defined.
Instance: KnownConstant Original.LF_DOT_ImpParser.LF.ImpParser.tokenize := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ImpParser_LF_ImpParser_tokenize := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.tokenize Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.tokenize Imported.Original_LF__DOT__ImpParser_LF_ImpParser_tokenize Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso := {}.