From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.and__iso.
Require Import Stdlib.Logic.ProofIrrelevance.

Monomorphic Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1'' : forall x x0 : SProp, imported_and x x0 -> x := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1''.

(* proj1'' P Q (HPQ : P /\ Q) : P := match HPQ with conj HP HQ => HP end *)
(* imported version: forall x x0 : SProp, and x x0 -> x *)
(* The relation says: given and_iso relating (P /\ Q) to (imported_and x2 x4), 
   the result proj1'' should relate to imported_proj1'' *)

Monomorphic Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1''_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 /\ x3) (x6 : imported_and x2 x4),
  rel_iso (and_iso hx hx0) x5 x6 -> rel_iso hx (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.proj1'' x1 x3 x5) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1'' x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hrel.
  (* x5 : x1 /\ x3, x6 : imported_and x2 x4 *)
  (* Goal: rel_iso hx (proj1'' x5) (imported_proj1'' x6) *)
  (* i.e. IsomorphismDefinitions.eq (to hx (proj1'' x5)) (imported_proj1'' x6) *)
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.proj1''.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1''.
  unfold Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1''.
  destruct x5 as [HP HQ].
  (* Now we have HP : x1, goal is rel_iso hx HP (Imported.proj1'' x6) *)
  (* We need: eq (to hx HP) (imported_proj1'' x6) *)
  (* From Hrel, we know to (and_iso hx hx0) (conj HP HQ) = x6 *)
  (* The to function of and_iso maps (conj HP HQ) to (and_intro (to hx HP) (to hx0 HQ)) *)
  (* So x6 has (to hx HP) as its first component *)
  (* imported_proj1'' extracts the first component *)
  destruct Hrel as [Hrel].
  simpl in Hrel.
  (* Hrel : eq (and_intro (to hx HP) (to hx0 HQ)) x6 *)
  destruct Hrel.
  (* Now x6 = and_intro (to hx HP) (to hx0 HQ) *)
  constructor.
  (* Goal: eq (to hx HP) (imported_proj1'' (and_intro (to hx HP) (to hx0 HQ))) *)
  (* imported_proj1'' (and_intro a b) = a by definition *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.proj1'' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1'' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.proj1'' Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1''_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.proj1'' Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1'' Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_proj1''_iso := {}.