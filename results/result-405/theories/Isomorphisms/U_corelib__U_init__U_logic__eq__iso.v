From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq.
  unfold rel_iso in *.
  simpl in *.
  (* H34 : to x3 = x4, H56 : to x5 = x6 (in IsomorphismDefinitions.eq / SProp) *)
  pose proof (eq_of_seq H34) as E34.
  pose proof (eq_of_seq H56) as E56.
  
  (* Define to direction *)
  assert (to_dir : Logic.eq x3 x5 -> Imported.Corelib_Init_Logic_eq x2 x4 x6).
  { intro e. destruct e.
    (* Now x3 = x5, so we need eq x4 x6 *)
    (* From E34 : to x3 = x4 and E56 : to x3 = x6 *)
    rewrite <- E34, <- E56.
    apply Imported.Corelib_Init_Logic_eq_refl. }
  
  (* Define from direction *)
  assert (from_dir : Imported.Corelib_Init_Logic_eq x2 x4 x6 -> Logic.eq x3 x5).
  { intro e.
    (* e : eq x4 x6 in SProp *)
    (* We need eq x3 x5 in Prop *)
    (* x3 = from (to x3) = from x4 *)
    (* x5 = from (to x5) = from x6 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    transitivity (from hx (to hx x3)).
    { symmetry. apply eq_of_seq. exact Hft3. }
    transitivity (from hx (to hx x5)).
    2:{ apply eq_of_seq. exact Hft5. }
    (* Now need: from (to x3) = from (to x5) *)
    (* to x3 = x4, to x5 = x6 *)
    (* Use f_equal with from *)
    apply Logic.f_equal.
    (* Need: to x3 = to x5 *)
    transitivity x4. { exact E34. }
    transitivity x6. 
    2:{ symmetry. exact E56. }
    (* Need: x4 = x6 *)
    destruct e.
    reflexivity. }
  
  refine {|
    to := to_dir;
    from := from_dir;
    to_from := _;
    from_to := _
  |}.
  - (* to_from: proof irrelevance in SProp *)
    intros e. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use proof irrelevance *)
    intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.