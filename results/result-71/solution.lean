-- Lean 4 translation of Rocq ImpParser tokenize_ex1 and dependencies
set_option linter.unusedVariables false

-- Boolean type (matching Rocq's bool)
inductive Coqbool : Type where
  | Coqtrue : Coqbool
  | Coqfalse : Coqbool

-- mybool is an alias used in definitions
def mybool : Type := Coqbool

-- Exported names for bool constructors
def Coqtrue : Coqbool := Coqbool.Coqtrue
def Coqfalse : Coqbool := Coqbool.Coqfalse

-- bool alias for Imported.bool (use mybool_ prefix to avoid clash with Lean's bool)
def mybool_ : Type := Coqbool
def mytrue : mybool_ := Coqbool.Coqtrue
def myfalse : mybool_ := Coqbool.Coqfalse

-- True proposition (for U_true__iso)
inductive myTrue : Prop where
  | I : myTrue

def myTrue_I : myTrue := myTrue.I

-- False proposition (empty type)
inductive myFalse : Prop where

-- Ascii type: 8 booleans
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Alias for the constructor, needed for export
def Ascii_Ascii (b0 b1 b2 b3 b4 b5 b6 b7 : mybool) : Ascii_ascii := 
  Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7

-- String type
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

-- Natural numbers
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def option_None (A : Type) : option A := option.None
def option_Some (A : Type) (a : A) : option A := option.Some a

-- Prod type (pairs)
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def prod_pair (A B : Type) (a : A) (b : B) : prod A B := prod.pair a b

def nil (A : Type) : list A := list.nil
def cons (A : Type) (h : A) (t : list A) : list A := list.cons h t

-- optionE
inductive Original_LF__DOT__ImpParser_LF_ImpParser_optionE (X : Type) : Type where
  | SomeE : X → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X
  | NoneE : String_string → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X

def Original_LF__DOT__ImpParser_LF_ImpParser_SomeE (X : Type) : X → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X :=
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE.SomeE

def Original_LF__DOT__ImpParser_LF_ImpParser_NoneE (X : Type) : String_string → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X :=
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE.NoneE

-- chartype inductive
inductive Original_LF__DOT__ImpParser_LF_ImpParser_chartype : Type where
  | white : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | alpha : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | digit : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | other : Original_LF__DOT__ImpParser_LF_ImpParser_chartype

-- token type alias
def Original_LF__DOT__ImpParser_LF_ImpParser_token : Type := String_string

-- Nat comparison helpers
def mynat_eqb : mynat → mynat → mybool
  | mynat.O, mynat.O => Coqbool.Coqtrue
  | mynat.S n, mynat.S m => mynat_eqb n m
  | _, _ => Coqbool.Coqfalse

def mynat_leb : mynat → mynat → mybool
  | mynat.O, _ => Coqbool.Coqtrue
  | mynat.S _, mynat.O => Coqbool.Coqfalse
  | mynat.S n, mynat.S m => mynat_leb n m

-- Boolean operations
def orb : mybool → mybool → mybool
  | Coqbool.Coqtrue, _ => Coqbool.Coqtrue
  | Coqbool.Coqfalse, b => b

def andb : mybool → mybool → mybool
  | Coqbool.Coqtrue, b => b
  | Coqbool.Coqfalse, _ => Coqbool.Coqfalse

-- Addition for nat
def mynat_add : mynat → mynat → mynat
  | mynat.O, m => m
  | mynat.S n, m => mynat.S (mynat_add n m)

-- Helper to convert a bit to its place value
def bit_val (b : mybool) (place : mynat) : mynat :=
  match b with
  | Coqbool.Coqtrue => place
  | Coqbool.Coqfalse => mynat.O

-- Powers of 2 as mynat
def mynat_1 : mynat := mynat.S mynat.O
def mynat_2 : mynat := mynat.S mynat_1
def mynat_4 : mynat := mynat.S (mynat.S mynat_2)
def mynat_8 : mynat := mynat.S (mynat.S (mynat.S (mynat.S mynat_4)))
def mynat_16 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_8)))))))
def mynat_32' : mynat := mynat_add mynat_16 mynat_16
def mynat_64 : mynat := mynat_add mynat_32' mynat_32'
def mynat_128 : mynat := mynat_add mynat_64 mynat_64

-- Convert ascii to nat (nat_of_ascii)
def nat_of_ascii (c : Ascii_ascii) : mynat :=
  match c with
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    mynat_add (mynat_add (mynat_add (mynat_add (mynat_add (mynat_add (mynat_add
      (bit_val b0 mynat_1)
      (bit_val b1 mynat_2))
      (bit_val b2 mynat_4))
      (bit_val b3 mynat_8))
      (bit_val b4 mynat_16))
      (bit_val b5 mynat_32'))
      (bit_val b6 mynat_64))
      (bit_val b7 mynat_128)

-- Helper for creating specific numbers
def mynat_32 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat.O)))))))))))))))))))))))))))))))
def mynat_9 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat.O))))))))
def mynat_10 : mynat := mynat.S mynat_9
def mynat_13 : mynat := mynat.S (mynat.S (mynat.S (mynat.S mynat_9)))
def mynat_40 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_32)))))))
def mynat_41 : mynat := mynat.S mynat_40
def mynat_48 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_32)))))))))))))))
def mynat_57 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_48))))))))
def mynat_65 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_57)))))))
def mynat_90 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_65))))))))))))))))))))))))
def mynat_97 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_90))))))
def mynat_122 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_97))))))))))))))))))))))))

-- isWhite: check if character is whitespace (32, 9, 10, 13)
def Original_LF__DOT__ImpParser_LF_ImpParser_isWhite (c : Ascii_ascii) : mybool :=
  let n := nat_of_ascii c
  orb (orb (mynat_eqb n mynat_32) (mynat_eqb n mynat_9))
      (orb (mynat_eqb n mynat_10) (mynat_eqb n mynat_13))

-- isAlpha: check if character is alphabetic (65-90 or 97-122)
def Original_LF__DOT__ImpParser_LF_ImpParser_isAlpha (c : Ascii_ascii) : mybool :=
  let n := nat_of_ascii c
  orb (andb (mynat_leb mynat_65 n) (mynat_leb n mynat_90))
      (andb (mynat_leb mynat_97 n) (mynat_leb n mynat_122))

-- isDigit: check if character is a digit (48-57)
def Original_LF__DOT__ImpParser_LF_ImpParser_isDigit (c : Ascii_ascii) : mybool :=
  let n := nat_of_ascii c
  andb (mynat_leb mynat_48 n) (mynat_leb n mynat_57)

-- classifyChar
def Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar (c : Ascii_ascii) : Original_LF__DOT__ImpParser_LF_ImpParser_chartype :=
  match Original_LF__DOT__ImpParser_LF_ImpParser_isWhite c with
  | Coqbool.Coqtrue => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white
  | Coqbool.Coqfalse =>
    match Original_LF__DOT__ImpParser_LF_ImpParser_isAlpha c with
    | Coqbool.Coqtrue => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha
    | Coqbool.Coqfalse =>
      match Original_LF__DOT__ImpParser_LF_ImpParser_isDigit c with
      | Coqbool.Coqtrue => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit
      | Coqbool.Coqfalse => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other

-- list_of_string
def Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string : String_string → list Ascii_ascii
  | String_string.EmptyString => list.nil
  | String_string.String c s => list.cons c (Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string s)

-- fold_right for string_of_list
def fold_right {A B : Type} (f : A → B → B) (b : B) : list A → B
  | list.nil => b
  | list.cons h t => f h (fold_right f b t)

-- string_of_list
def Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list (l : list Ascii_ascii) : String_string :=
  fold_right String_string.String String_string.EmptyString l

-- rev_append
def rev_append {A : Type} : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons h t, l2 => rev_append t (list.cons h l2)

-- rev
def rev {A : Type} (l : list A) : list A := rev_append l list.nil

-- app (list append)
def app {A : Type} : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons h t, l2 => list.cons h (app t l2)

-- map
def map {A B : Type} (f : A → B) : list A → list B
  | list.nil => list.nil
  | list.cons h t => list.cons (f h) (map f t)

-- ASCII characters for '(' and ')'
-- '(' is ASCII 40 = 00101000
-- ')' is ASCII 41 = 00101001
def ascii_lparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def ascii_rparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse

-- Ascii equality
def ascii_eqb (a1 a2 : Ascii_ascii) : mybool :=
  match a1, a2 with
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    andb (andb (andb (match b0, c0 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse)
                     (match b1, c1 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse))
               (andb (match b2, c2 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse)
                     (match b3, c3 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse)))
         (andb (andb (match b4, c4 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse)
                     (match b5, c5 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse))
               (andb (match b6, c6 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse)
                     (match b7, c7 with | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue | _, _ => Coqbool.Coqfalse)))

-- tokenize_helper
def Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper (cls : Original_LF__DOT__ImpParser_LF_ImpParser_chartype) (acc : list Ascii_ascii) (xs : list Ascii_ascii) : list (list Ascii_ascii) :=
  let tk := match acc with
            | list.nil => list.nil
            | list.cons _ _ => list.cons (rev acc) list.nil
  match xs with
  | list.nil => tk
  | list.cons x xs' =>
    -- Check for '(' and ')'
    match ascii_eqb x ascii_lparen with
    | Coqbool.Coqtrue => app tk (list.cons (list.cons ascii_lparen list.nil) (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other list.nil xs'))
    | Coqbool.Coqfalse =>
      match ascii_eqb x ascii_rparen with
      | Coqbool.Coqtrue => app tk (list.cons (list.cons ascii_rparen list.nil) (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other list.nil xs'))
      | Coqbool.Coqfalse =>
        let tp := Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar x
        match tp with
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white =>
          app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white list.nil xs')
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha =>
          match cls with
          | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha => Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha (list.cons x acc) xs'
          | _ => app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha (list.cons x list.nil) xs')
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit =>
          match cls with
          | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit => Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit (list.cons x acc) xs'
          | _ => app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit (list.cons x list.nil) xs')
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other =>
          match cls with
          | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other => Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other (list.cons x acc) xs'
          | _ => app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other (list.cons x list.nil) xs')

-- tokenize
def Original_LF__DOT__ImpParser_LF_ImpParser_tokenize (s : String_string) : list String_string :=
  map Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list
      (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper
         Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white
         list.nil
         (Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string s))

-- Equality type for Type (imports as SProp eq in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True type
inductive TrueType : Prop where
  | I : TrueType

-- tokenize_ex1: the admitted example in Original.v
-- tokenize "abc12=3  223*(3+(a+c))" = ["abc"; "12"; "="; "3"; "223"; "*"; "("; "3"; "+"; "("; "a"; "+"; "c"; ")"; ")"]
-- Since this is Admitted in the original, we use an axiom

-- Build the input string "abc12=3  223*(3+(a+c))"
-- 'a' = 97 = 01100001 (true,false,false,false,false,true,true,false)
-- 'b' = 98 = 01100010 (false,true,false,false,false,true,true,false)
-- 'c' = 99 = 01100011 (true,true,false,false,false,true,true,false)
-- '1' = 49 = 00110001 (true,false,false,false,true,true,false,false)
-- '2' = 50 = 00110010 (false,true,false,false,true,true,false,false)
-- '3' = 51 = 00110011 (true,true,false,false,true,true,false,false)
-- '=' = 61 = 00111101 (true,false,true,true,true,true,false,false)
-- ' ' = 32 = 00100000 (false,false,false,false,false,true,false,false)
-- '*' = 42 = 00101010 (false,true,false,true,false,true,false,false)
-- '(' = 40 = 00101000 (false,false,false,true,false,true,false,false)
-- '+' = 43 = 00101011 (true,true,false,true,false,true,false,false)
-- ')' = 41 = 00101001 (true,false,false,true,false,true,false,false)

def char_a : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_b : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_c : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_1 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_2 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_3 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_eq : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_space : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_star : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_lparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_plus : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_rparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse

-- Input string: "abc12=3  223*(3+(a+c))"
def input_string : String_string :=
  String_String char_a
  (String_String char_b
  (String_String char_c
  (String_String char_1
  (String_String char_2
  (String_String char_eq
  (String_String char_3
  (String_String char_space
  (String_String char_space
  (String_String char_2
  (String_String char_2
  (String_String char_3
  (String_String char_star
  (String_String char_lparen
  (String_String char_3
  (String_String char_plus
  (String_String char_lparen
  (String_String char_a
  (String_String char_plus
  (String_String char_c
  (String_String char_rparen
  (String_String char_rparen
  String_EmptyString)))))))))))))))))))))

-- Expected output tokens
def str_abc : String_string := String_String char_a (String_String char_b (String_String char_c String_EmptyString))
def str_12 : String_string := String_String char_1 (String_String char_2 String_EmptyString)
def str_eq : String_string := String_String char_eq String_EmptyString
def str_3 : String_string := String_String char_3 String_EmptyString
def str_223 : String_string := String_String char_2 (String_String char_2 (String_String char_3 String_EmptyString))
def str_star : String_string := String_String char_star String_EmptyString
def str_lparen : String_string := String_String char_lparen String_EmptyString
def str_plus : String_string := String_String char_plus String_EmptyString
def str_rparen : String_string := String_String char_rparen String_EmptyString
def str_a : String_string := String_String char_a String_EmptyString
def str_c : String_string := String_String char_c String_EmptyString

def expected_output : list String_string :=
  list.cons str_abc
  (list.cons str_12
  (list.cons str_eq
  (list.cons str_3
  (list.cons str_223
  (list.cons str_star
  (list.cons str_lparen
  (list.cons str_3
  (list.cons str_plus
  (list.cons str_lparen
  (list.cons str_a
  (list.cons str_plus
  (list.cons str_c
  (list.cons str_rparen
  (list.cons str_rparen
  list.nil))))))))))))))

-- The tokenize_ex1 axiom (corresponds to Admitted in Original.v)
axiom Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1 :
  Corelib_Init_Logic_eq (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize input_string) expected_output

-- Equality for Prop arguments (becomes SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Note: myFalse and myTrue are already defined earlier in the file
-- CoqTrue and CoqTrue_I are also defined earlier (myTrue with same structure)
-- CoqTrue is used by the Checker

-- Define aliases from myTrue if needed
def CoqTrue := myTrue
def CoqTrue_I : CoqTrue := myTrue.I

-- Reduction lemma: base case (empty xs, empty acc)
theorem tokenize_helper_nil_nil (cls : Original_LF__DOT__ImpParser_LF_ImpParser_chartype) :
  Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper cls list.nil list.nil = list.nil :=
  rfl

-- Reduction lemma: base case (empty xs, nonempty acc)
theorem tokenize_helper_nil_cons (cls : Original_LF__DOT__ImpParser_LF_ImpParser_chartype) (h : Ascii_ascii) (t : list Ascii_ascii) :
  Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper cls (list.cons h t) list.nil = 
  list.cons (rev (list.cons h t)) list.nil :=
  rfl

-- Helper to convert Nat to mynat
def make_nat (n : Nat) : mynat :=
  match n with
  | Nat.zero => mynat.O
  | Nat.succ m => mynat.S (make_nat m)

-- testParsing: wraps a parser with tokenize
def Original_LF__DOT__ImpParser_LF_ImpParser_testParsing {X : Type}
  (p : mynat → list Original_LF__DOT__ImpParser_LF_ImpParser_token → 
       Original_LF__DOT__ImpParser_LF_ImpParser_optionE (prod X (list Original_LF__DOT__ImpParser_LF_ImpParser_token)))
  (s : String_string) : 
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE (prod X (list Original_LF__DOT__ImpParser_LF_ImpParser_token)) :=
  let t := Original_LF__DOT__ImpParser_LF_ImpParser_tokenize s
  p (make_nat 100) t

-- manual_grade definitions (None)
def Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec : option (prod mynat String_string) := 
  option.None

def Original_LF__DOT__Induction_LF_Induction_manual__grade__for__eqb__refl__informal : option (prod mynat String_string) := 
  option.None
