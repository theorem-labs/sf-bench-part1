-- Lean translation for In10' theorem
-- In10' : In 10 [1;2;3;4;5;6;7;8;9;10]

-- Natural numbers
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- List type
inductive list (A : Type) : Type
| nil : list A
| cons : A → list A → list A

-- Export constructors for list
def list_nil (A : Type) : list A := list.nil
def list_cons (A : Type) : A → list A → list A := list.cons

-- Aliases for Coq list names
def nil (A : Type) : list A := list.nil
def cons {A : Type} (h : A) (t : list A) : list A := list.cons h t

-- List.In definition (in Prop, which becomes SProp in Rocq)
-- Uses standard Lean False and Or
def List_In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | list.nil => _root_.False
  | list.cons h t => h = x ∨ List_In x t

-- In10' axiom: In 10 [1;2;3;4;5;6;7;8;9;10]
-- This is Admitted in Original.v so we represent it as an axiom
axiom Original_LF__DOT__Imp_LF_Imp_AExp_In10' : List_In
  (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))  -- 10
  (list.cons (nat.S nat.O)  -- 1
    (list.cons (nat.S (nat.S nat.O))  -- 2
      (list.cons (nat.S (nat.S (nat.S nat.O)))  -- 3
        (list.cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
          (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
            (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))  -- 6
              (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))  -- 7
                (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))  -- 8
                  (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))  -- 9
                    (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))  -- 10
                      list.nil))))))))))
