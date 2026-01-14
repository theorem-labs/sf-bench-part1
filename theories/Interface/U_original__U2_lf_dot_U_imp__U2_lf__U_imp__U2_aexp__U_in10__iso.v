From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.list__iso Interface.U_list__U_in__iso Interface.cons__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso Interface.nil__iso.

Module Export CodeBlocks.

  Export (hints) Interface.list__iso Interface.U_list__U_in__iso Interface.cons__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso Interface.nil__iso.

  Export Interface.list__iso.CodeBlocks Interface.U_list__U_in__iso.CodeBlocks Interface.cons__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.nil__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.list__iso.Interface <+ Interface.U_list__U_in__iso.Interface <+ Interface.cons__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.nil__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_In10 : imported_List_In (imported_S (imported_S (imported_S (iterate1 imported_S 7 imported_0))))
    (imported_cons (imported_S imported_0)
       (imported_cons (imported_S (imported_S imported_0))
          (imported_cons (imported_S (imported_S (imported_S imported_0)))
             (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
                (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))
                   (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 3 imported_0))))
                      (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 4 imported_0))))
                         (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 5 imported_0))))
                            (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 6 imported_0))))
                               (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 7 imported_0)))) (imported_nil imported_nat))))))))))).
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso : rel_iso
    (List_In_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 7 0 imported_0 _0_iso))))
       (cons_iso (S_iso _0_iso)
          (cons_iso (S_iso (S_iso _0_iso))
             (cons_iso (S_iso (S_iso (S_iso _0_iso)))
                (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))
                   (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))))
                      (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 3 0 imported_0 _0_iso))))
                         (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 4 0 imported_0 _0_iso))))
                            (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 5 0 imported_0 _0_iso))))
                               (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 6 0 imported_0 _0_iso))))
                                  (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 7 0 imported_0 _0_iso)))) (nil_iso nat_iso))))))))))))
    Original.LF_DOT_Imp.LF.Imp.AExp.In10 imported_Original_LF__DOT__Imp_LF_Imp_AExp_In10.
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.In10 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.In10 imported_Original_LF__DOT__Imp_LF_Imp_AExp_In10 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso; constructor : typeclass_instances.


End Interface.