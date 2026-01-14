From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_toy__iso Interface.ex__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_toy__iso Interface.ex__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_toy__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_toy__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct : imported_ex
    (fun H : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
     imported_ex
       (fun H0 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
        forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
        (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (H a'0)) ->
        (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H0 a'0 a'1)) ->
        forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)).
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct_iso : rel_iso
    {|
      to :=
        ex_iso
          (fun f : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
           exists g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy,
             forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
             (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (f b)) ->
             (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
          (fun H : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
           imported_ex
             (fun H0 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
              forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
              (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (H a'0)) ->
              (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H0 a'0 a'1)) ->
              forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0))
          (fun (x1 : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
             (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
             (hx : rel_iso (IsoArrow Original_LF__DOT__Basics_LF_Basics_bool_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso) x1 x2) =>
           ex_iso
             (fun g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
              forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
              (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (x1 b)) ->
              (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
             (fun H : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
              forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
              (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
              (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H a'0 a'1)) ->
              forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
             (fun (x3 : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                (x4 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                (hx0 : rel_iso (IsoArrow nat_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso)) x3 x4) =>
              IsoForall
                (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop =>
                 (forall b : Original.LF_DOT_Basics.LF.Basics.bool, a (x1 b)) ->
                 (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), a t -> a (x3 n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, a t)
                (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp =>
                 (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                 (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (x4 a'0 a'1)) ->
                 forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                (fun (x5 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop) (x6 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp)
                   (hx1 : rel_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso iso_Prop_SProp) x5 x6) =>
                 IsoArrow
                   (IsoForall (fun a : Original.LF_DOT_Basics.LF.Basics.bool => x5 (x1 a)) (fun a' : imported_Original_LF__DOT__Basics_LF_Basics_bool => x6 (x2 a'))
                      (fun (x7 : Original.LF_DOT_Basics.LF.Basics.bool) (x8 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx2 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x7 x8) =>
                       iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND hx hx2))))
                   (IsoArrow
                      (IsoForall (fun a : nat => forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, x5 t -> x5 (x3 a t))
                         (fun a' : imported_nat => forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, x6 a'0 -> x6 (x4 a' a'0))
                         (fun (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) =>
                          IsoForall (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy => x5 a -> x5 (x3 x7 a))
                            (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy => x6 a' -> x6 (x4 x8 a'))
                            (fun (x9 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x10 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                               (hx3 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x9 x10) =>
                             IsoArrow (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx3)) (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND (IsoUnFunND hx0 hx2) hx3))))))
                      (IsoForall x5 x6
                         (fun (x7 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x8 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                            (hx2 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x7 x8) =>
                          iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx2)))))));
      from :=
        from
          (ex_iso
             (fun f : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
              exists g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy,
                forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (f b)) ->
                (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
             (fun H : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
              imported_ex
                (fun H0 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                 forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                 (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (H a'0)) ->
                 (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H0 a'0 a'1)) ->
                 forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0))
             (fun (x1 : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                (hx : rel_iso (IsoArrow Original_LF__DOT__Basics_LF_Basics_bool_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso) x1 x2) =>
              ex_iso
                (fun g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
                 forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                 (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (x1 b)) ->
                 (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
                (fun H : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                 forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                 (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                 (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H a'0 a'1)) ->
                 forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                (fun (x3 : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                   (x4 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                   (hx0 : rel_iso (IsoArrow nat_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso)) x3 x4) =>
                 IsoForall
                   (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop =>
                    (forall b : Original.LF_DOT_Basics.LF.Basics.bool, a (x1 b)) ->
                    (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), a t -> a (x3 n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, a t)
                   (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp =>
                    (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                    (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (x4 a'0 a'1)) ->
                    forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                   (fun (x5 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop) (x6 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp)
                      (hx1 : rel_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso iso_Prop_SProp) x5 x6) =>
                    IsoArrow
                      (IsoForall (fun a : Original.LF_DOT_Basics.LF.Basics.bool => x5 (x1 a)) (fun a' : imported_Original_LF__DOT__Basics_LF_Basics_bool => x6 (x2 a'))
                         (fun (x7 : Original.LF_DOT_Basics.LF.Basics.bool) (x8 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx2 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x7 x8) =>
                          iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND hx hx2))))
                      (IsoArrow
                         (IsoForall (fun a : nat => forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, x5 t -> x5 (x3 a t))
                            (fun a' : imported_nat => forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, x6 a'0 -> x6 (x4 a' a'0))
                            (fun (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) =>
                             IsoForall (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy => x5 a -> x5 (x3 x7 a))
                               (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy => x6 a' -> x6 (x4 x8 a'))
                               (fun (x9 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x10 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                                  (hx3 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x9 x10) =>
                                IsoArrow (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx3)) (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND (IsoUnFunND hx0 hx2) hx3))))))
                         (IsoForall x5 x6
                            (fun (x7 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x8 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                               (hx2 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x7 x8) =>
                             iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx2))))))));
      to_from :=
        fun
          x : imported_ex
                (fun H : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                 imported_ex
                   (fun H0 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                    forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                    (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (H a'0)) ->
                    (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H0 a'0 a'1)) ->
                    forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)) =>
        to_from
          (ex_iso
             (fun f : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
              exists g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy,
                forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (f b)) ->
                (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
             (fun H : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
              imported_ex
                (fun H0 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                 forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                 (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (H a'0)) ->
                 (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H0 a'0 a'1)) ->
                 forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0))
             (fun (x1 : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                (hx : rel_iso (IsoArrow Original_LF__DOT__Basics_LF_Basics_bool_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso) x1 x2) =>
              ex_iso
                (fun g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
                 forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                 (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (x1 b)) ->
                 (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
                (fun H : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                 forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                 (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                 (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H a'0 a'1)) ->
                 forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                (fun (x3 : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                   (x4 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                   (hx0 : rel_iso (IsoArrow nat_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso)) x3 x4) =>
                 IsoForall
                   (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop =>
                    (forall b : Original.LF_DOT_Basics.LF.Basics.bool, a (x1 b)) ->
                    (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), a t -> a (x3 n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, a t)
                   (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp =>
                    (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                    (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (x4 a'0 a'1)) ->
                    forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                   (fun (x5 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop) (x6 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp)
                      (hx1 : rel_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso iso_Prop_SProp) x5 x6) =>
                    IsoArrow
                      (IsoForall (fun a : Original.LF_DOT_Basics.LF.Basics.bool => x5 (x1 a)) (fun a' : imported_Original_LF__DOT__Basics_LF_Basics_bool => x6 (x2 a'))
                         (fun (x7 : Original.LF_DOT_Basics.LF.Basics.bool) (x8 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx2 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x7 x8) =>
                          iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND hx hx2))))
                      (IsoArrow
                         (IsoForall (fun a : nat => forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, x5 t -> x5 (x3 a t))
                            (fun a' : imported_nat => forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, x6 a'0 -> x6 (x4 a' a'0))
                            (fun (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) =>
                             IsoForall (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy => x5 a -> x5 (x3 x7 a))
                               (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy => x6 a' -> x6 (x4 x8 a'))
                               (fun (x9 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x10 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                                  (hx3 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x9 x10) =>
                                IsoArrow (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx3)) (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND (IsoUnFunND hx0 hx2) hx3))))))
                         (IsoForall x5 x6
                            (fun (x7 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x8 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                               (hx2 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x7 x8) =>
                             iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx2))))))))
          x;
      from_to :=
        fun
          x : exists
                (y : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (g : nat ->
                                                                                                                       Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy ->
                                                                                                                       Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy),
                forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (y b)) ->
                (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t =>
        seq_p_of_t
          (from_to
             (ex_iso
                (fun f : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
                 exists g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy,
                   forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                   (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (f b)) ->
                   (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
                (fun H : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                 imported_ex
                   (fun H0 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                    forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                    (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (H a'0)) ->
                    (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H0 a'0 a'1)) ->
                    forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0))
                (fun (x1 : Original.LF_DOT_Basics.LF.Basics.bool -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                   (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                   (hx : rel_iso (IsoArrow Original_LF__DOT__Basics_LF_Basics_bool_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso) x1 x2) =>
                 ex_iso
                   (fun g : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy =>
                    forall P : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop,
                    (forall b : Original.LF_DOT_Basics.LF.Basics.bool, P (x1 b)) ->
                    (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), P t -> P (g n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, P t)
                   (fun H : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
                    forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp,
                    (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                    (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (H a'0 a'1)) ->
                    forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                   (fun (x3 : nat -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy)
                      (x4 : imported_nat -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                      (hx0 : rel_iso (IsoArrow nat_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso)) x3 x4) =>
                    IsoForall
                      (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop =>
                       (forall b : Original.LF_DOT_Basics.LF.Basics.bool, a (x1 b)) ->
                       (forall (n : nat) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy), a t -> a (x3 n t)) -> forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, a t)
                      (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp =>
                       (forall a'0 : imported_Original_LF__DOT__Basics_LF_Basics_bool, a' (x2 a'0)) ->
                       (forall (a'0 : imported_nat) (a'1 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), a' a'1 -> a' (x4 a'0 a'1)) ->
                       forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, a' a'0)
                      (fun (x5 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy -> Prop) (x6 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy -> SProp)
                         (hx1 : rel_iso (IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso iso_Prop_SProp) x5 x6) =>
                       IsoArrow
                         (IsoForall (fun a : Original.LF_DOT_Basics.LF.Basics.bool => x5 (x1 a)) (fun a' : imported_Original_LF__DOT__Basics_LF_Basics_bool => x6 (x2 a'))
                            (fun (x7 : Original.LF_DOT_Basics.LF.Basics.bool) (x8 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx2 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x7 x8) =>
                             iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND hx hx2))))
                         (IsoArrow
                            (IsoForall (fun a : nat => forall t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy, x5 t -> x5 (x3 a t))
                               (fun a' : imported_nat => forall a'0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, x6 a'0 -> x6 (x4 a' a'0))
                               (fun (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) =>
                                IsoForall (fun a : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy => x5 a -> x5 (x3 x7 a))
                                  (fun a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy => x6 a' -> x6 (x4 x8 a'))
                                  (fun (x9 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x10 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                                     (hx3 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x9 x10) =>
                                   IsoArrow (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx3)) (iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 (IsoUnFunND (IsoUnFunND hx0 hx2) hx3))))))
                            (IsoForall x5 x6
                               (fun (x7 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy) (x8 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy)
                                  (hx2 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy_iso x7 x8) =>
                                iso_of_rel_iso_iso_sort_PropSProp_T (IsoUnFunND hx1 hx2))))))))
             x)
    |} Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy_correct imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct.
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy_correct ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.Toy_correct imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct_iso; constructor : typeclass_instances.


End Interface.