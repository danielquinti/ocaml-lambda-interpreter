
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token IN
%token BOOL
%token NAT
%token LETREC

%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token COLON
%token ARROW
%token SEMICOLON
%token EOF
%token PROJ_1
%token PROJ_2
%token BRACKETS_1
%token BRACKETS_2
%token COMMA
%token <int> INTV
%token <string> STRINGV

%start s
%type <Lambda.instruction> s

%%

s :
    term EOF
      { Eval $1 }
    | STRINGV EQ term EOF
      {Assign($1,$3)}

term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA STRINGV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET STRINGV EQ term IN term
      { TmLet ($2, $4, $6) }
  | LETREC STRINGV COLON ty EQ term IN term 
    { TmLet ($2, TmFix (TmAbs ($2, $4, $6)), $8) }
  | term PROJ_1
      {TmProj1($1)}
  | term PROJ_2
      {TmProj2($1)}
  | pair
      {$1}
  | record {$1}
  | term DOT STRINGV {TmProj($1,$3)}

pair: BRACKETS_1 term COMMA term BRACKETS_2
    { TmPair ($2,$4) }

record: BRACKETS_1 field_list BRACKETS_2{TmRecord($2)}

field_list: field {$1}
|field COMMA field_list {List.append $1 $3}

field: STRINGV EQ term {[($1,$3)]}

appTerm :
    atomicTerm
      { $1 }
  | SUCC atomicTerm
      { TmSucc $2 }
  | PRED atomicTerm
      { TmPred $2 }
  | ISZERO atomicTerm
      { TmIsZero $2 }
  | appTerm atomicTerm
      { TmApp ($1, $2) }

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | TRUE
      { TmTrue }
  | FALSE
      { TmFalse }
  | STRINGV
      { TmVar $1 }
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }

ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }
  | BRACKETS_1 ty COMMA ty BRACKETS_2
      { TyProd($2,$4)}
  | BRACKETS_1 field_type_list BRACKETS_2{TyRecord($2)}


field_type_list: 
  field_type {$1}
  |field_type COMMA field_type_list {List.append $1 $3}

field_type: STRINGV COLON ty {[($1,$3)]}

atomicTy :
    LPAREN ty RPAREN  
      { $2 } 
  | BOOL
      { TyBool }
  | NAT
      { TyNat }

