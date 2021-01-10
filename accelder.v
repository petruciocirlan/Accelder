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
(*| acVar : string -> AExp*)
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
| boolean : bool -> typeBool.

Coercion boolean: bool >-> typeBool.

Inductive BExp :=
| boolTrue : BExp
| boolFalse : BExp
| bVar : string -> BExp
(*| bcVar : string -> BExp*)
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
(*| static*)
(*| constant*)
| volatile. (* default *)

Inductive Decl :=
| voidParam
| declVar : Attribute -> string -> Decl
| declNat : Decl -> Decl
| declBool : Decl -> Decl
| declarations : Decl -> Decl -> Decl.
(*| declUserType : string -> Decl -> Decl.*)

(*Notation "'static' 'var' X" := (declVar static X) (at level 41).*)
(*Notation "'constant' 'var' X" := (declVar constant X) (at level 41).*)
Notation "'var' X" := (declVar volatile X) (at level 42).
Notation "X ':' 'NAT'" := (declNat X) (at level 43).
Notation "X ':' 'BOOL'" := (declBool X) (at level 43).
Notation "X ',' Y" := (declarations X Y) (at level 44).
(*Notation "'struct' X '{>' Y '<}'" := (declUserType X Y) (at level 45).*)

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
| declStmt: Decl -> Stmt
| declAutovalue : Decl -> string -> Stmt
(*| declAutoRvalue : Decl -> Result -> Stmt*)
| assignNat : string -> AExp -> Stmt
| assignBool : string -> BExp -> Stmt
| call : string -> Arguments -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ternary : BExp -> Stmt -> Stmt -> Stmt
| whileloop : BExp -> Stmt -> Stmt
(*| forloopst : Stmt -> BExp -> Stmt -> Stmt -> Stmt*)
| break
| continue.
(*| switch : *)

Coercion declStmt: Decl >-> Stmt.

Notation "A ':N=' B" := (assignNat A B) (at level 90).
Notation "A ':B=' B" := (assignBool A B) (at level 90).
Notation "A ':auto=' B" := (declAutovalue A B) (at level 91).
(*Notation "A ':autoR=' B" := (declAutoRvalue A B) (at level 91).*)
Notation "A '(>' B '<)' 'call!'" := (call A B) (at level 91).
Notation "S1 ':D' S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'if*' '(' cond ')' '{' S1 '}' 'else*' '{' S2 '}' 'endif'" := (ifthenelse cond S1 S2) (at level 94).
Notation "'if*' '(' cond ')' '{' S '}' 'endif'" := (ifthen cond S) (at level 95).
Notation "'(t' cond 't)' '?*' '(' Strue ')' ':' '(' Sfalse ')'" := (ternary cond Strue Sfalse) (at level 95).
Notation "'while' '(' cond ')' '{' S '}'" := (whileloop cond S) (at level 96).
Notation "'forloop' '(' A '~*' B '~*' C ')' '{' S '}' 'endfor'" := (A :D while (B) { S :D C }) (at level 97).

Inductive typeFunction :=
| func : Decl -> Stmt -> typeFunction
| funcUndeclared : typeFunction.

Inductive Program :=
| function : string -> typeFunction -> Program
| globalDecl : Decl -> Program
| seqProgram : Program -> Program -> Program.

Coercion globalDecl : Decl >-> Program.

Notation "'def' N '(!' P '!)' '{' S '}'" := (function N (func P S)) (at level 92).
Notation "P1 :P P2" := (seqProgram P1 P2) (at level 99).

(* TYPE: result - value *)
Inductive Result :=
| errAssign : Result
| errRedeclared : Result
| errUndeclared : Result
| undeclared : Result
| resultNat : typeNat -> Result
| resultBool : typeBool -> Result
| resultFunc : typeFunction -> Result.

Coercion resultNat : typeNat >-> Result.
Coercion resultBool : typeBool >-> Result.
Coercion resultFunc : typeFunction >-> Result.

Definition check_eq_over_types ( t1 : Result) ( t2 : Result) : bool :=
  match t1 with
    | errAssign => match t2 with
      | errAssign => true
      | _ => false
      end

    | errRedeclared => match t2 with
      | errRedeclared => true
      | _ => false
      end

    | errUndeclared => match t2 with
      | errUndeclared => true
      | _ => false
      end

    | undeclared => true

    | resultNat a => match t2 with
      | resultNat b => true
      | _ => false
      end

    | resultBool a => match t2 with
      | resultBool b => true
      | _ => false
      end

    | resultFunc a => match t2 with
      | resultFunc b => true
      | _ => false
      end
  end.

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)

Scheme Equality for Mem.

(* Environment *)
Definition Env := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> Result.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack -> Config.

(* Function for updating the environment *)
Definition update_env (env: Env) (x: string) (n: Mem) : Env :=
  fun y =>
      (* If the variable has assigned a default memory zone, 
         then it will be updated with the current memory offset *)
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default))
      then
        n
      else
        (env y).

Definition env0 : Env := fun x => mem_default.

(* Function for updating the memory layer *)
Definition update_mem (mem : MemLayer) (env : Env) (x : string) (zone : Mem) (v : Result) : MemLayer :=
  fun y =>
      if (Mem_beq y zone)
      then
        if (Mem_beq (env x) mem_default)
        then errUndeclared
        else
          if (Mem_beq (env x) y)
          then 
            if (check_eq_over_types (mem y) v)
            then v
            else errAssign
          else mem y
      else mem y.
    (* To be implemented based on the functionalities of your own language
       This implementation should be similar to the "update" function from "Week_7.v" *)

(* Each variable/function name is initially mapped to undeclared *)
Definition mem0 : MemLayer := fun x => undeclared.

Definition update_conf (conf : Config) (zone : nat) (env : Env) (mem : MemLayer) (stack : Stack) : Config :=
  config zone env mem stack.

Fixpoint aeval (exp : AExp) (conf : Config) : typeNat :=
  match conf with
  | config level env mem stack =>
    match exp with
    | aVar symbol => match (mem (env symbol)) with
      | resultNat X => X
      | _ => errNat
      end

    | aNum num => num

    | aAdd exp1 exp2 => match (aeval exp1 conf) with
      | number X => match (aeval exp2 conf) with
        | number Y => Nat.add X Y
        | errNat => errNat
        end
      | errNat => errNat
      end

    | aSub exp1 exp2 => match (aeval exp1 conf) with
      | number X => match (aeval exp2 conf) with
        | number Y => if (Nat.ltb X Y)
                      then errNat
                      else Nat.sub X Y
        | errNat => errNat
        end
      | errNat => errNat
      end

    | aMul exp1 exp2 => match (aeval exp1 conf) with
      | number X => match (aeval exp2 conf) with
        | number Y => Nat.mul X Y
        | errNat => errNat
        end
      | errNat => errNat
      end

    | aDiv exp1 exp2 => match (aeval exp1 conf) with
      | number X => match (aeval exp2 conf) with
        | number Y => if (Nat.eqb Y 0)
                      then errNat
                      else Nat.div X Y
        | errNat => errNat
        end
      | errNat => errNat
      end

    | aMod exp1 exp2 => match (aeval exp1 conf) with
      | number X => match (aeval exp2 conf) with
        | number Y => if (Nat.eqb Y 0)
                      then errNat
                      else Nat.modulo X Y
        | errNat => errNat
        end
      | errNat => errNat
      end
    end
  end.

Fixpoint beval (bexp : BExp) (conf : Config) : typeBool :=
  match conf with
  | config level env mem stack =>
    match bexp with
    | boolTrue => true

    | boolFalse => false

    | bVar symbol => match (mem (env symbol)) with
      | resultBool X => X
      | _ => errBool
      end

    | bBool X => X

    | bNot b => match (beval b conf) with
      | boolean X => X
      | errBool => errBool
      end

    | bAnd b1 b2 => match (beval b1 conf) with
      | boolean X => match (beval b2 conf) with
        | boolean Y => andb X Y
        | errBool => errBool
        end
      | errBool => errBool
      end

    | bOr b1 b2 => match (beval b1 conf) with
      | boolean X => match (beval b2 conf) with
        | boolean Y => orb X Y
        | errBool => errBool
        end
      | errBool => errBool
      end

    | bXor b1 b2 => match (beval b1 conf) with
      | boolean X => match (beval b2 conf) with
        | boolean Y => xorb X Y
        | errBool => errBool
        end
      | errBool => errBool
      end

    | bLessThan a1 a2 => match (aeval a1 conf) with
      | number X => match (aeval a2 conf) with
        | number Y => Nat.leb X Y
        | errNat => errBool
        end
      | errNat => errBool
      end

    | bEqual a1 a2 => match (aeval a1 conf) with
      | number X => match (aeval a2 conf) with
        | number Y => Nat.eqb X Y
        | errNat => errBool
        end
      | errNat => errBool
      end
    end
  end.

Definition get_fn_signature (conf : Config) (symbol : string) : typeFunction :=
  match conf with
  | config level env mem stack => match mem (env symbol) with
                                  | resultFunc X => X
                                  | _ => funcUndeclared
                                  end
  end.

Definition check_if_fn_exists (conf : Config) (symbol : string) : bool :=
  match get_fn_signature conf symbol with
  | funcUndeclared => false
  | _ => true
  end.

Fixpoint check_fn_arguments (conf : Config) (params : Decl) (args : Arguments) : bool :=
  match params with
  | voidParam => match args with
    | voidArg => true
    | _ => false
    end
  | declVar attr symbol => false
  | declNat D => match args with
    | argument symbol => match conf with
      | config zone env mem stack => check_eq_over_types (mem (env symbol)) (number 0)
      end
    | _ => false
    end
  | declBool D => match args with
    | argument symbol => match conf with
      | config zone env mem stack => check_eq_over_types (mem (env symbol)) true
      end
    | _ => false
    end
  | declarations D1 D2 => match args with
    | arguments A1 A2 => (check_fn_arguments conf D1 A1) && (check_fn_arguments conf D2 A2)
    | _ => false
    end
  end.

Fixpoint update_conf_decls (decls : Decl) (conf : Config) (gas : nat) : Config :=
  match gas with
  | 0 => conf
  | S gas' => match conf with
    | config zone env mem stack => match decls with
      | voidParam => conf
      | declVar attr symbol => conf (*err*)
      | declNat D => match D with
        | declVar attr symbol => match attr with
          (*| constant => conf (*err*)*)
          | volatile =>
            if (Mem_beq (env symbol) mem_default)
            then update_conf conf zone env (update_mem mem env symbol (env symbol) errRedeclared) stack
            else update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) (number 0)) stack
          end
        | _ => conf (*err*)
        end
      | declBool D => match D with
        | declVar attr symbol => match attr with
          (*| constant => ...*)
          | volatile =>
            if (Mem_beq (env symbol) mem_default)
            then update_conf conf zone env (update_mem mem env symbol (env symbol) errRedeclared) stack
            else update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) false) stack
          end
        | _ => conf (*err*)
        end
      | declarations D1 D2 => update_conf_decls D2 (update_conf_decls D1 conf gas') gas'
      end
    end
  end.

(*
Fixpoint parseDecls (decls : Decl) (conf : Config) (gas : nat) : Config :=
  match gas with
  | 0 => conf
  | S gas' => match conf with
    | config zone env mem stack => match decls with
      | voidParam => conf
      | declVar attr symbol => conf (*err*)
      | declNat D => match D with
        | declVar attr symbol => match attr with
          (*| constant => conf (*err*)*)
          | volatile => update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) (number 0)) stack
          end
        | _ => conf (*err*)
        end
      | declBool D => match D with
        | declVar attr symbol => match attr with
          (*| constant => ...*)
          | volatile => update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) false) stack
          end
        | _ => conf (*err*)
        end
      | declarations D1 D2 => parseDecls D2 (parseDecls D1 conf gas') gas'
      end
    end
  end.
*)

Fixpoint parseInit (program : Program) (conf : Config) (gas : nat) : Config :=
  match gas with
  | 0 => conf
  | S gas' => match conf with
    | config zone env mem stack => match program with
      | seqProgram P1 P2 => parseInit P2 (parseInit P1 conf gas') gas'
      | function symbol signature => update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) signature) stack
      | globalDecl X => update_conf_decls X conf gas'
      end
    end
  end.

Definition update_conf_argument (param : Decl) (arg : Arguments) (conf : Config) : Config :=
  match param with
  | declNat D => match D with
    | declVar attr symbol => match arg with
      | argument argname => match conf with
        | config zone env mem stack => update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) (mem (env argname))) stack
        end
      | _ => conf (*err*)
      end
    | _ => conf (*err*)
    end
  | _ => conf (*err*)
  end.

Fixpoint update_conf_arguments (params : Decl) (args : Arguments) (conf : Config) (gas : nat) : Config :=
  match gas with
  | 0 => conf
  | S gas' => match params with
    | declarations D1 D2 => match args with
      | arguments A1 A2 => update_conf_arguments D2 A2 (update_conf_arguments D1 A1 conf gas') gas'
      | _ => conf (*err*)
      end
    | declNat D => match args with
      | argument A => update_conf_argument D A conf
      | _ => conf (*err*)
      end
    | declBool D => match args with
      | argument A => update_conf_argument D A conf
      | _ => conf (*err*)
      end
    | _ => conf (*err*)
    end
  end.


Fixpoint evalStmts (stmts : Stmt) (conf : Config) (gas : nat) : Config :=
  match gas with
  | 0 => conf
  | S gas' => match stmts with
    | nop (*no operation*) => conf

    | declStmt D => update_conf_decls D conf 32

    | declAutovalue D esymbol => match D with
      | declVar attr nsymbol =>
        match conf with
        | config zone env mem stack =>
          if (Mem_beq (env nsymbol) mem_default)
          then
            if (Mem_beq (env esymbol) mem_default)
            then update_conf conf zone env (update_mem mem env nsymbol (env nsymbol) errUndeclared) stack
            else update_conf conf (S zone) (update_env env nsymbol (offset (S zone))) (update_mem mem (update_env env nsymbol (offset (S zone))) nsymbol (offset (S zone)) (mem (env esymbol))) stack
          else update_conf conf zone env (update_mem mem env nsymbol (env nsymbol) errRedeclared) stack
        end
      | _ => conf (*err*)
      end

    | assignNat symbol aexp =>
      match conf with
      | config zone env mem stack =>
        if (Mem_beq (env symbol) mem_default)
        then update_conf conf zone env (update_mem mem env symbol (env symbol) errUndeclared) stack
        else update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) (aeval aexp conf)) stack
      end

    | assignBool symbol bexp =>
      match conf with
      | config zone env mem stack =>
        if (Mem_beq (env symbol) mem_default)
        then update_conf conf zone env (update_mem mem env symbol (env symbol) errUndeclared) stack
        else update_conf conf (S zone) (update_env env symbol (offset (S zone))) (update_mem mem (update_env env symbol (offset (S zone))) symbol (offset (S zone)) (resultBool (beval bexp conf))) stack
      end

    | call symbol args =>
      if (check_if_fn_exists conf symbol)
      then
        match (get_fn_signature conf symbol) with
        | func D St =>
          if (check_fn_arguments conf D args)
          then
            match conf with
            | config zone env mem stack =>
              match (update_conf_arguments D args (update_conf conf zone env0 mem stack) 32) with
              | config zone1 env1 mem1 stack1 =>
                match evalStmts St (update_conf (config zone1 env1 mem1 stack1) zone1 env1 mem1 (env :: stack1)) gas' with
                | config zoneR envR memR stackR =>
                  update_conf (config zoneR envR memR stackR) zoneR env memR stack
                end
              end
            end
          else conf
        | _ => conf (*err*)
        end
      else conf

    | sequence S1 S2 => evalStmts S2 (evalStmts S1 conf gas') gas'

    | ifthenelse cond S1 S2 => if (beval cond conf)
                               then evalStmts S1 conf gas'
                               else evalStmts S2 conf gas'

    | ifthen cond St =>
      match (beval cond conf) with
      | boolean b =>
        if (b)
        then evalStmts St conf gas'
        else conf
      | _ => conf
      end

    | ternary cond S1 S2 => evalStmts (ifthenelse cond S1 S2) conf gas'

    | whileloop cond St =>
      if (beval cond conf)
      then evalStmts (whileloop cond St) (evalStmts St conf gas') gas'
      else conf
(*
    | forloop Si cond Sr Sb => match evalStmts Si conf gas' with
      | conf2 => evalStmts (whileloop cond (sequence Sb Sr)) conf2 gas'
      end
*)
    | _ => conf
    end
  end.

Definition evalMain (func : Result) (conf : Config) : Config :=
  match func with
  | resultFunc fn => match fn with
    | func D stmts => match D with
      | voidParam => evalStmts stmts conf 32
      | _ => conf
      end
    | funcUndeclared => conf
    end
  | _ => conf (*err*)
  end.

Definition run (program : Program) : Config :=
  match (parseInit program (config 0 env0 mem0 nil) 32) with
  | config level env mem stack => evalMain (mem (env "main")) (config level env mem stack)
  (* eval <entry function> <environment - vars> <environmnet - functions> *)
  end.

Definition programX :=
  def "foobar" (! voidParam !)
  {
    nop
  } :P
  
  def "wow" (! var "first" : NAT, var "second" : NAT !)
  {
    nop
  } :P
  
  (*struct "mystruct" {>
    var "a" : NAT,
    var "b" : BOOL
  <} :P*)

  def "main" (! voidParam !)
  {
    var "hello" : NAT :D
    "hello" :N= 0 :D
    
    var "boooool" : BOOL :D
    "boooool" :B= true :D
    
    var "test" :auto= "boooool" :D
    if* ( "test" )
    {
      "boooool" :B= 32 <' "hello" :D
      while ( "hello" <' 32 )
      {
        "hello" :N= "hello" +' 1
      }
    } endif :D
    
    "foobar"(> voidArg <) call! :D
    (*"foobar"(> "hello" si "option" <) call! :D*)
    
    var "counter" : NAT :D
    forloop ( "counter" :N= 0 ~* "counter" <' 128 ~* "counter" :N= "counter" +' 1 )
    {
      "foobar"(> voidArg <) call!
      (*(t "counter" %' 13 ==' 5 t) ?* ( break ) : ( continue )*)
    } endfor :D
    
    var "that's it" : BOOL
  }
  .

Definition programY :=
  def "main" (! voidParam !)
  {
    var "hello" : NAT :D
    
    (*"hello" :N= 9 :D*)
    
    (*var "hah" :auto= "hello" :D*)
    
    var "hah" : NAT :D
    
    (*"hah" :N= "hah" +' 3 +' "hello" :D*)
    
    var "end" : BOOL
  }.

Check programY.

Compute match (run programX) with
  | config zone env mem stack =>
    (mem (env "hello"))
  end.
















