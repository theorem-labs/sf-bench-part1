-- Lean 4 translation of Rocq ImpParser tokenize and dependencies
set_option linter.unusedVariables false

-- Boolean type (matching Rocq's bool)
inductive Coqbool : Type where
  | Coqtrue : Coqbool
  | Coqfalse : Coqbool

-- mybool is an alias used in definitions  
def mybool : Type := Coqbool

-- Ascii type: 8 booleans
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Alias for Ascii.Ascii (expected by checker)
abbrev Ascii_Ascii := Ascii_ascii.Ascii
abbrev Ascii_ascii_Ascii := Ascii_ascii.Ascii

-- String type
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Aliases for String_string
abbrev String_string_EmptyString := String_string.EmptyString
abbrev String_string_String := String_string.String

-- Natural numbers
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

-- Alias for export as "nat"
abbrev «nat» := mynat
abbrev nat_O := mynat.O
abbrev nat_S := mynat.S

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

-- Aliases for list
abbrev list_nil := @list.nil
abbrev list_cons := @list.cons

-- chartype inductive
inductive Original_LF__DOT__ImpParser_LF_ImpParser_chartype : Type where
  | white : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | alpha : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | digit : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | other : Original_LF__DOT__ImpParser_LF_ImpParser_chartype

-- Nat comparison helpers
def mynat_eqb : mynat → mynat → Coqbool
  | mynat.O, mynat.O => Coqbool.Coqtrue
  | mynat.S n, mynat.S m => mynat_eqb n m
  | _, _ => Coqbool.Coqfalse

def mynat_leb : mynat → mynat → Coqbool
  | mynat.O, _ => Coqbool.Coqtrue
  | mynat.S _, mynat.O => Coqbool.Coqfalse
  | mynat.S n, mynat.S m => mynat_leb n m

-- Boolean operations
def orb : Coqbool → Coqbool → Coqbool
  | Coqbool.Coqtrue, _ => Coqbool.Coqtrue
  | Coqbool.Coqfalse, b => b

def andb : Coqbool → Coqbool → Coqbool
  | Coqbool.Coqtrue, b => b
  | Coqbool.Coqfalse, _ => Coqbool.Coqfalse

-- Addition for nat
def mynat_add : mynat → mynat → mynat
  | mynat.O, m => m
  | mynat.S n, m => mynat.S (mynat_add n m)

-- Helper to convert a bit to its place value
def bit_val (b : Coqbool) (place : mynat) : mynat :=
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
def Original_LF__DOT__ImpParser_LF_ImpParser_isWhite (c : Ascii_ascii) : Coqbool :=
  let n := nat_of_ascii c
  orb (orb (mynat_eqb n mynat_32) (mynat_eqb n mynat_9))
      (orb (mynat_eqb n mynat_10) (mynat_eqb n mynat_13))

-- isAlpha: check if character is alphabetic (65-90 or 97-122)
def Original_LF__DOT__ImpParser_LF_ImpParser_isAlpha (c : Ascii_ascii) : Coqbool :=
  let n := nat_of_ascii c
  orb (andb (mynat_leb mynat_65 n) (mynat_leb n mynat_90))
      (andb (mynat_leb mynat_97 n) (mynat_leb n mynat_122))

-- isDigit: check if character is digit (48-57)
def Original_LF__DOT__ImpParser_LF_ImpParser_isDigit (c : Ascii_ascii) : Coqbool :=
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

-- string_of_list (fold_right String EmptyString xs)
def Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list : list Ascii_ascii → String_string
  | list.nil => String_string.EmptyString
  | list.cons c rest => String_string.String c (Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list rest)

-- rev_append for list reversal
def rev_append {A : Type} : list A → list A → list A
  | list.nil, acc => acc
  | list.cons h t, acc => rev_append t (list.cons h acc)

-- rev
def rev {A : Type} (l : list A) : list A := rev_append l list.nil

-- app (list concatenation)
def app {A : Type} : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons h t, l2 => list.cons h (app t l2)

-- map
def map {A B : Type} (f : A → B) : list A → list B
  | list.nil => list.nil
  | list.cons h t => list.cons (f h) (map f t)

-- ASCII characters for '(' and ')'
def ascii_lparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse  -- 40
def ascii_rparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse   -- 41

-- Helper: check if ascii char equals '(' (40)
def is_lparen (c : Ascii_ascii) : Coqbool := mynat_eqb (nat_of_ascii c) mynat_40

-- Helper: check if ascii char equals ')' (41)
def is_rparen (c : Ascii_ascii) : Coqbool := mynat_eqb (nat_of_ascii c) mynat_41

-- tokenize_helper: matches exactly the Rocq Fixpoint structure
def Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper (cls : Original_LF__DOT__ImpParser_LF_ImpParser_chartype) (acc : list Ascii_ascii) (xs : list Ascii_ascii) : list (list Ascii_ascii) :=
  let tk := match acc with
            | list.nil => list.nil
            | list.cons _ _ => list.cons (rev acc) list.nil
  match xs with
  | list.nil => tk
  | list.cons x xs' =>
    match is_lparen x with
    | Coqbool.Coqtrue => app tk (list.cons (list.cons ascii_lparen list.nil) (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other list.nil xs'))
    | Coqbool.Coqfalse =>
      match is_rparen x with
      | Coqbool.Coqtrue => app tk (list.cons (list.cons ascii_rparen list.nil) (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other list.nil xs'))
      | Coqbool.Coqfalse =>
        match Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar x with
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

-- prod type
inductive prod (A B : Type) : Type where
  | mk : A → B → prod A B

-- Alias for prod
abbrev prod_mk := @prod.mk

-- token is string
def Original_LF__DOT__ImpParser_LF_ImpParser_token : Type := String_string

-- optionE type
inductive Original_LF__DOT__ImpParser_LF_ImpParser_optionE (X : Type) : Type where
  | SomeE : X → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X
  | NoneE : String_string → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X

-- mynat 100
def mynat_50 : mynat :=
  mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S
  (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S
  (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S
  (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S
  (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S
  mynat.O)))))))))))))))))))))))))))))))))))))))))))))))))

def mynat_100 : mynat := mynat_add mynat_50 mynat_50

-- testParsing
def Original_LF__DOT__ImpParser_LF_ImpParser_testParsing {X : Type}
    (p : mynat → list Original_LF__DOT__ImpParser_LF_ImpParser_token →
         Original_LF__DOT__ImpParser_LF_ImpParser_optionE (prod X (list Original_LF__DOT__ImpParser_LF_ImpParser_token)))
    (s : String_string) : Original_LF__DOT__ImpParser_LF_ImpParser_optionE (prod X (list Original_LF__DOT__ImpParser_LF_ImpParser_token)) :=
  let t := Original_LF__DOT__ImpParser_LF_ImpParser_tokenize s
  p mynat_100 t
