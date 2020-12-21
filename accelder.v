(* Accelder - Petru Ciocirlan 2E1, FII UAIC *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(* TYPE: Naturals *)
Inductive typeNat :=
(*
| errNatDivide0 : typeNat
| errNatModulo0 : typeNat
| errNatNegative : typeNat
*)
| errNat : typeNat
| number : nat -> typeNat.

Coercion number : nat >-> typeNat.

Inductive AExp :=
| aVar : string -> AExp
| aNum : typeNat -> AExp
| aAdd : typeNat -> typeNat -> AExp
| aSub : typeNat -> typeNat -> AExp
| aMul : typeNat -> typeNat -> AExp
| aDiv : typeNat -> typeNat -> AExp
| aMod : typeNat -> typeNat -> AExp.

Coercion aVar : string >-> AExp.
Coercion aNum : typeNat >-> AExp.

Notation "A +' B" := (aAdd A B)(at level 50, left associativity).
Notation "A -' B" := (aSub A B)(at level 50, left associativity).
Notation "A *' B" := (aMul A B)(at level 48, left associativity).
Notation "A /' B" := (aDiv A B)(at level 48, left associativity).
Notation "A %' B" := (aMod A B)(at level 45, left associativity).

(* TYPE: Booleans *)
Inductive typeBool :=
| errBool : typeBool
| boolTrue : typeBool
| boolFalse : typeBool
| boolean : bool -> typeBool.

Coercion boolean: bool >-> typeBool.

Inductive BExp :=
| bVar : string -> BExp
| bBool : typeBool -> BExp
| bNot : typeBool -> BExp
| bAnd : typeBool -> typeBool -> BExp
| bOr : typeBool -> typeBool -> BExp
| bXor : typeBool -> typeBool -> BExp
| bLessThan : typeNat -> typeNat -> BExp
| bEqual : typeNat -> typeNat -> BExp.

Coercion bVar : string >-> BExp.
Coercion bBool : typeBool >-> BExp.

Notation "!' A" := (bNot A)(at level 51, left associativity).
Notation "A &&' B" := (bAnd A B)(at level 52, left associativity).
Notation "A ||' B" := (bOr A B)(at level 53, left associativity).
Notation "A ^' B" := (bXor A B)(at level 54, left associativity).
Notation "A <' B" := (bLessThan A B) (at level 70).
Notation "A ==' B" := (bEqual A B) (at level 70).

(* TYPE: Declarations *)

Inductive Attribute :=
| static
| constant
| volatile. (* default *)

Inductive Decl :=
| declVar : Attribute -> string -> Decl
| declNat : Decl -> Decl
| declBool : Decl -> Decl
| declarations : Decl -> Decl -> Decl.

Notation "'static' 'var' X" := (declVar static X) (at level 41).
Notation "'constant' 'var' X" := (declVar constant X) (at level 41).
Notation "'var' X" := (declVar volatile X) (at level 42).
Notation "X ':' 'NAT'" := (declNat X) (at level 43).
Notation "X ':' 'BOOL'" := (declBool X) (at level 43).
Notation "X ',' Y" := (declarations X Y) (at level 44).

(* TYPE: result - value (reference for functions) *)
Inductive Result :=
| errUndeclared : Result
| undeclared : Result
| resultNat : typeNat -> Result
| resultBool : typeBool -> Result.
(*| codeRef : Stmt -> Result.*)

(*Inductive Cases :=
| caseDefault
| case : Result -> Cases
| *)

(* TYPE: Instructions *)
Inductive Stmt :=
| declAuto : Decl -> Result -> Stmt
| assignNat : string -> AExp -> Stmt
| assignBool : string -> BExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| forloop : Stmt -> BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ternary : BExp -> Stmt -> Stmt -> Stmt
(*| switch : *)
| function : string -> Decl -> Stmt -> Stmt.

Notation "A ':N=' B" := (assignNat A B) (at level 90).
Notation "A ':B=' B" := (assignBool A B) (at level 90).
Notation "A ':auto=' B" := (declAuto A B) (at level 90).
Notation "S1 ':D' S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'if' '(' cond ')' '{' S1 '}' 'else' '{' S2 '}'" := (ifthenelse cond S1 S2) (at level 94).
Notation "'if' '(' cond ')' '{' S '}'" := (ifthen cond S) (at level 95).
Notation "'(' cond ')' '?' '(' Strue ')' ':' '(' Sfalse ')'" := (ternary cond Strue Sfalse) (at level 95).
Notation "'while' '(' cond ')' '{' S '}'" := (while cond S) (at level 96).
Notation "'forloop' ( A ~ B ~ C ) { S }" := (A :D while (B) { S :D C }) (at level 97).
Notation "'def' N '(' P ')' '{' S '}'" := (function N P S) (at level 89).










