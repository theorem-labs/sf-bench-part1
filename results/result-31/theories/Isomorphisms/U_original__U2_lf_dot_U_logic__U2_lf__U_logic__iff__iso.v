From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Logic_LF_Logic_iff : SProp -> SProp -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_iff.

Instance Original_LF__DOT__Logic_LF_Logic_iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (Original.LF_DOT_Logic.LF.Logic.iff x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_iff x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold Original.LF_DOT_Logic.LF.Logic.iff.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_iff.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_iff.
  (* We need: Iso ((x1 -> x3) /\ (x3 -> x1)) (SAnd (x2 -> x4) (x4 -> x2)) *)
  apply Build_Iso with
    (to := fun pq => 
      match pq with
      | conj f g => Imported.SAnd_intro _ _ 
          (fun y2 => to H34 (f (from H12 y2))) 
          (fun y4 => to H12 (g (from H34 y4)))
      end)
    (from := fun sq => 
      conj 
        (fun y1 => from H34 (Imported.left _ _ sq (to H12 y1))) 
        (fun y3 => from H12 (Imported.right _ _ sq (to H34 y3)))).
  - (* to_from *) intros sq. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *) intros pq. destruct pq as [f g].
    simpl.
    (* Need to prove: IsomorphismDefinitions.eq 
         (conj (fun y1 => from H34 (to H34 (f (from H12 (to H12 y1))))) 
               (fun y3 => from H12 (to H12 (g (from H34 (to H34 y3)))))) 
         (conj f g) *)
    apply f_equal2.
    + apply functional_extensionality_dep. intros y1.
      pose proof (from_to H12 y1) as Hy1.
      pose proof (from_to H34 (f (from H12 (to H12 y1)))) as Hfy1.
      apply (eq_trans Hfy1).
      apply f_equal.
      exact Hy1.
    + apply functional_extensionality_dep. intros y3.
      pose proof (from_to H34 y3) as Hy3.
      pose proof (from_to H12 (g (from H34 (to H34 y3)))) as Hgy3.
      apply (eq_trans Hgy3).
      apply f_equal.
      exact Hy3.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.iff Original_LF__DOT__Logic_LF_Logic_iff_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.iff Imported.Original_LF__DOT__Logic_LF_Logic_iff Original_LF__DOT__Logic_LF_Logic_iff_iso := {}.