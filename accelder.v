(* Accelder - Petru Ciocirlan 2E1, FII UAIC *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(* TYPE: Natural *)
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
| aAdd : AExp -> AExp -> AExp
| aSub : AExp -> AExp -> AExp
| aMul : AExp -> AExp -> AExp
| aDiv : AExp -> AExp -> AExp
| aMod : AExp -> AExp -> AExp.

Coercion aVar : string >-> AExp.
Coercion aNum : typeNat >-> AExp.

Notation "A +' B" := (aAdd A B)(at level 50, left associativity).
Notation "A -' B" := (aSub A B)(at level 50, left associativity).
Notation "A *' B" := (aMul A B)(at level 48, left associativity).
Notation "A /' B" := (aDiv A B)(at level 48, left associativity).
Notation "A %' B" := (aMod A B)(at level 45, left associativity).

(* TYPE: Boolean *)
Inductive typeBool :=
| errBool : typeBool
| boolTrue : typeBool
| boolFalse : typeBool
| boolean : bool -> typeBool.

Coercion boolean: bool >-> typeBool.

Inductive BExp :=
| bVar : string -> BExp
| bBool : typeBool -> BExp
| bNot : BExp -> BExp
| bAnd : BExp -> BExp -> BExp
| bOr : BExp -> BExp -> BExp
| bXor : BExp -> BExp -> BExp
| bLessThan : AExp -> AExp -> BExp
| bEqual : AExp -> AExp -> BExp.

Coercion bVar : string >-> BExp.
Coercion bBool : typeBool >-> BExp.

Notation "!' A" := (bNot A)(at level 51, left associativity).
Notation "A &&' B" := (bAnd A B)(at level 52, left associativity).
Notation "A ||' B" := (bOr A B)(at level 53, left associativity).
Notation "A ^' B" := (bXor A B)(at level 54, left associativity).
Notation "A <' B" := (bLessThan A B) (at level 70).
Notation "A ==' B" := (bEqual A B) (at level 70).

(* TYPE: Integer *)
Require Import ZArith.

(* TYPE: Float *)
Require Import Floats.

(* TYPE: Character (ASCII) *)
Require Import Ascii.

(* TYPE: String *)
(* Require Import String. already imported *)

(* TYPE: Pointer? *)

(* TYPE: Declarations *)

Inductive Attribute :=
| static
| constant
| volatile. (* default *)

Inductive Decl :=
| voidParam
| declVar : Attribute -> string -> Decl
| declNat : Decl -> Decl
| declBool : Decl -> Decl
| declarations : Decl -> Decl -> Decl
| declUserType : string -> Decl -> Decl.

Notation "'static' 'var' X" := (declVar static X) (at level 41).
Notation "'constant' 'var' X" := (declVar constant X) (at level 41).
Notation "'var' X" := (declVar volatile X) (at level 42).
Notation "X ':' 'NAT'" := (declNat X) (at level 43).
Notation "X ':' 'BOOL'" := (declBool X) (at level 43).
Notation "X ',' Y" := (declarations X Y) (at level 44).
Notation "'struct' X '{>' Y '<}'" := (declUserType X Y) (at level 45).

(* TYPE: result - value (reference for functions) *)
Inductive Result :=
| errUndeclared : Result
| undeclared : Result
| resultNat : typeNat -> Result
| resultBool : typeBool -> Result.
(*| codeRef : Stmt -> Result.*)

Coercion resultNat : typeNat >-> Result.
Coercion resultBool : typeBool >-> Result.

(*Inductive Cases :=
| caseDefault
| case : Result -> Cases
| *)

Inductive Arguments :=
| voidArg
| argument : string -> Arguments
| arguments : Arguments -> Arguments -> Arguments.

Coercion argument: string >-> Arguments.
Notation "A 'si' B" := (arguments A B) (at level 98).

(* TYPE: Instructions *)
Inductive Stmt :=
| nop
| decl: Decl -> Stmt
| declAutoLvalue : Decl -> string -> Stmt
| declAutoRvalue : Decl -> Result -> Stmt
| assignNat : string -> AExp -> Stmt
| assignBool : string -> BExp -> Stmt
| call : string -> Arguments -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ternary : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| forloop : Stmt -> BExp -> Stmt -> Stmt
| break
| continue.
(*| switch : *)

Coercion decl: Decl >-> Stmt.

Notation "A ':N=' B" := (assignNat A B) (at level 90).
Notation "A ':B=' B" := (assignBool A B) (at level 90).
Notation "A ':autoL=' B" := (declAutoLvalue A B) (at level 91).
Notation "A ':autoR=' B" := (declAutoRvalue A B) (at level 91).
Notation "A '(>' B '<)' 'call!'" := (call A B) (at level 91).
Notation "S1 ':D' S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'if*' '(' cond ')' '{' S1 '}' 'else*' '{' S2 '}' 'endif'" := (ifthenelse cond S1 S2) (at level 94).
Notation "'if*' '(' cond ')' '{' S '}' 'endif'" := (ifthen cond S) (at level 95).
Notation "'(t' cond 't)' '?*' '(' Strue ')' ':' '(' Sfalse ')'" := (ternary cond Strue Sfalse) (at level 95).
Notation "'while' '(' cond ')' '{' S '}'" := (while cond S) (at level 96).
Notation "'forloop' '(' A '~*' B '~*' C ')' '{' S '}' 'endfor'" := (A :D while (B) { S :D C }) (at level 97).

Inductive Program :=
| function : string -> Decl -> Stmt -> Program
| globalDecl : Decl -> Program
| program : Program -> Program -> Program.

Coercion globalDecl : Decl >-> Program.

Notation "'def' N '(!' P '!)' '{' S '}'" := (function N P S) (at level 92).
Notation "P1 :P P2" := (program P1 P2) (at level 99).

Definition programX :=
  def "foobar" (! voidParam !)
  {
    nop
  } :P
  
  def "wow" (! var "first" : NAT, var "second" : NAT !)
  {
    nop
  } :P
  
  struct "mystruct" {>
    var "a" : NAT,
    var "b" : BOOL
  <} :P

  def "main" (! var "num" : NAT, var "option" : BOOL !)
  {
    static var "hello" : NAT :D
    "hello" :N= 0 :D
    var "test" :autoL= "first_param" :D
    if* ( "second_param" )
    {
      while ( "hello" <' "first_param" )
      {
        "hello" :N= "hello" +' 1 :D
        "second_param" :B= !' "second_param" :D
        if* ( "second_param" )
        {
          continue
        } endif
      }
    } endif :D
    
    "foobar"(> voidArg <) call! :D
    "foobar"(> "hello" si "option" <) call! :D
    
    forloop ( var "counter" :autoR= 0 ~* "counter" <' 128 ~* "counter" :N= "counter" +' 1 )
    {
      "foobar"(> voidArg <) call! :D
      (t "counter" %' 13 ==' 5 t) ?* ( break ) : ( continue )
    } endfor :D
    
    var "that's it" : BOOL
  }
  .

Check programX.
