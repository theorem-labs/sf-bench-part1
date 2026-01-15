From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Typeclasses Opaque rel_iso. *) (* for speed *)

From Stdlib Require Import Arith.
From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo : imported_nat -> SProp := 
  Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo.

(* Helper: nat_to_imported 42 = Imported.fortytwo *)
Lemma nat_to_imported_42 : nat_to_imported 42 = Imported.fortytwo.
Proof. reflexivity. Qed.

(* Build SInhabited (x = 42) from Imported.is_fortytwo (nat_to_imported x).
   The imported is_fortytwo has a single constructor at fortytwo.
   If x = 42, then nat_to_imported 42 = fortytwo and the constructor applies.
   If x <> 42, then there's no proof.
   
   We can match on the SProp proof to produce SInhabited (SProp).
*)
Definition imported_is_fortytwo_to_sinhabited (x : Datatypes.nat)
  (H : Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo (nat_to_imported x)) 
  : SInhabited (x = 42%nat).
Proof.
  (* H is in SProp. The type Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo (nat_to_imported x)
     is only inhabited when nat_to_imported x = Imported.fortytwo = nat_to_imported 42.
     Since nat_to_imported is injective, this means x = 42.
     
     We can match on H to refine the index. *)
  (* When we match on H, the only constructor is at fortytwo.
     So nat_to_imported x must equal fortytwo = nat_to_imported 42.
     By injectivity, x = 42. *)
  
  (* Use decidability since we can't directly eliminate SProp to Prop *)
  destruct (Nat.eq_dec x 42%nat) as [Heq | Hneq].
  - exact (sinhabits Heq).
  - (* This case is impossible because H exists only when x = 42.
       But we can't derive False from SProp H.
       
       However, we can try to use H. Since we're producing SProp (SInhabited),
       we can try to eliminate H.
       
       Actually, we can match on H since both H and the goal are SProp.
       The match will refine the index to fortytwo. *)
    (* Let's try a match *)
    refine (match H in Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo n 
                  return (n = nat_to_imported x -> SInhabited (x = 42%nat)) with
            | Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo_intro => _
            end Logic.eq_refl).
    (* Now n = fortytwo and we need to show: 
       fortytwo = nat_to_imported x -> SInhabited (x = 42) *)
    intro Heq'.
    (* Heq' : fortytwo = nat_to_imported x *)
    (* Since nat_to_imported is injective and fortytwo = nat_to_imported 42,
       we get 42 = x from Heq'. *)
    assert (Hx : x = 42%nat).
    { pose proof (Logic.f_equal imported_to_nat Heq') as Heq''.
      rewrite nat_roundtrip in Heq''.
      simpl in Heq''.
      symmetry. exact Heq''. }
    exact (sinhabits Hx).
Defined.

Definition is_fortytwo_from (x : Datatypes.nat) 
  (H : Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo (nat_to_imported x)) : x = 42%nat :=
  sinhabitant (imported_is_fortytwo_to_sinhabited x H).

Instance Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo_iso : 
  forall (x1 : Datatypes.nat) (x2 : imported_nat), 
  rel_iso nat_iso x1 x2 -> 
  Iso (Original.LF_DOT_AltAuto.LF.AltAuto.is_fortytwo x1) 
      (imported_Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo x2).
Proof.
  intros x1 x2 Hrel.
  unfold Original.LF_DOT_AltAuto.LF.AltAuto.is_fortytwo.
  unfold imported_Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo.
  cbn in Hrel.
  pose proof (eq_of_seq (proj_rel_iso Hrel)) as Heq.
  subst x2.
  
  (* Goal: Iso (x1 = 42) (Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo (nat_to_imported x1)) *)
  unshelve eexists.
  - (* to: x1 = 42 -> Imported.is_fortytwo (nat_to_imported x1) *) 
    intro H. 
    rewrite H.
    exact Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo_intro.
  - (* from: Imported.is_fortytwo (nat_to_imported x1) -> x1 = 42 *)
    exact (is_fortytwo_from x1).
  - (* to_from *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro H. apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.is_fortytwo := {}.
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo := {}.
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.is_fortytwo Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.is_fortytwo Imported.Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo_iso := {}.
