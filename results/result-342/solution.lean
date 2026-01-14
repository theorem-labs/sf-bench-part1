import Lean

/-!
This module only needs to provide the constant
`Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval__deterministic` so that the Lean
exporter can generate `Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval__deterministic`.

We mirror the Rocq interface type but keep all other objects abstract.
-/

universe u

opaque imported_String_string : Type u
opaque imported_nat : Type u
opaque imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com : Type u
opaque imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result : Type u

/-- SProp is represented by Prop on the Lean side; the Coq importer will map it to SProp. -/
abbrev SProp := Prop

opaque imported_and : SProp → SProp → SProp
opaque imported_Corelib_Init_Logic_eq : {α : Type u} → α → α → SProp

opaque imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval :
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com →
  (imported_String_string → imported_nat) →
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result →
  (imported_String_string → imported_nat) → SProp

/-- Axiom required by the task. -/
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval__deterministic :
  ∀ (x : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
    (x0 x1 x2 : imported_String_string → imported_nat)
    (x3 x4 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
    imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x (fun x5 => x0 x5) x3 (fun x5 => x1 x5) →
    imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x (fun x5 => x0 x5) x4 (fun x5 => x2 x5) →
    imported_and (imported_Corelib_Init_Logic_eq (fun x18 => x1 x18) (fun x18 => x2 x18))
                 (imported_Corelib_Init_Logic_eq x3 x4)
