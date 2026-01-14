From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper: convert eq a1 b1 to Imported_Corelib_Init_Logic_eq a2 b2 *)
Definition eq_to_imported {x1 x2 : Type} (hx : Iso x1 x2) 
  (a1 : x1) (a2 : x2) (ha : @rel_iso x1 x2 hx a1 a2)
  (b1 : x1) (b2 : x2) (hb : @rel_iso x1 x2 hx b1 b2)
  : Corelib.Init.Logic.eq a1 b1 -> imported_Corelib_Init_Logic_eq a2 b2.
Proof.
  intro Heq.
  destruct Heq.
  unfold rel_iso in ha, hb. simpl in ha, hb.
  (* ha : eq (to hx a1) a2 *)
  (* hb : eq (to hx a1) b2 (since b1 = a1 after destruct) *)
  pose proof (eq_trans (eq_sym ha) hb) as Hab.
  (* Hab : eq a2 b2 *)
  destruct Hab.
  exact (Imported.Corelib_Init_Logic_eq_refl x2 a2).
Defined.

(* Helper: convert Imported_Corelib_Init_Logic_eq a2 b2 to eq a1 b1 *)
Definition imported_to_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  (a1 : x1) (a2 : x2) (ha : @rel_iso x1 x2 hx a1 a2)
  (b1 : x1) (b2 : x2) (hb : @rel_iso x1 x2 hx b1 b2)
  : imported_Corelib_Init_Logic_eq a2 b2 -> Corelib.Init.Logic.eq a1 b1.
Proof.
  intro Heq.
  destruct Heq.
  unfold rel_iso in ha, hb. simpl in ha, hb.
  (* ha : eq (to hx a1) a2 *)
  (* hb : eq (to hx b1) a2 (since b2 = a2 after destruct) *)
  (* We need to prove a1 = b1 *)
  (* From ha: to hx a1 = a2 *)
  (* From hb: to hx b1 = a2 *)
  (* So to hx a1 = to hx b1 *)
  (* We can transport using from_to to get a1 = b1 *)
  pose proof (eq_trans ha (eq_sym hb)) as Hab.
  (* Hab : eq (to hx a1) (to hx b1) *)
  (* Use injectivity of to (via from) *)
  pose proof (from_to hx a1) as Hfta1.
  pose proof (from_to hx b1) as Hftb1.
  (* Hfta1 : eq (from hx (to hx a1)) a1 *)
  (* Hftb1 : eq (from hx (to hx b1)) b1 *)
  (* So from hx (to hx a1) = a1 and from hx (to hx b1) = b1 *)
  (* But to hx a1 = to hx b1, so from hx (to hx a1) = from hx (to hx b1) *)
  (* Hence a1 = b1 *)
  apply eq_of_seq.
  eapply eq_trans.
  - apply eq_sym. exact Hfta1.
  - eapply eq_trans.
    + apply f_equal. exact Hab.
    + exact Hftb1.
Defined.

(* The Iso between eq and Imported_Corelib_Init_Logic_eq *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx a1 a2 ha b1 b2 hb.
  (* Both Corelib.Init.Logic.eq (in Prop) and imported_Corelib_Init_Logic_eq (in SProp) are proof irrelevant.
     The to_from and from_to hold because:
     - for to_from: we need eq (to (from i)) i where i : SProp. In SProp, all proofs are equal, so eq_refl works.
     - for from_to: we need eq (from (to e)) e where e : Prop. Use proof irrelevance. *)
  exact {|
    to := @eq_to_imported x1 x2 hx a1 a2 ha b1 b2 hb;
    from := @imported_to_eq x1 x2 hx a1 a2 ha b1 b2 hb;
    (* SProp is definitionally proof irrelevant, so eq_refl always works *)
    to_from := fun i => IsomorphismDefinitions.eq_refl _;
    (* For Prop, we need proof irrelevance: use seq_of_eq with standard proof irrelevance *)
    from_to := fun e => seq_of_eq (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ _ _)
  |}.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.