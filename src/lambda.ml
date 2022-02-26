
(* TYPE DEFINITIONS *)
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  (***********************************************************)
  | TyProd of ty * ty (*pair type*)
  | TyRecord of (string*ty) list (*record type*)

type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVar of string
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLet of string * term * term
  (***********************************************************)
  | TmFix of term  (*fixed point combinator of an abstraction*)
  | TmPair of term * term
  | TmProj1 of term (*pair projections*)
  | TmProj2 of term (*pair projections*)
  | TmRecord of (string * term) list (*"label=term"*)
  | TmProj of term * string
;;
type instruction=
(*this distinction becomes relevant in execute_instruction*)
  Eval of term
  |Assign of string * term

type context =
  (string * ty) list
;;

(*global variable context*)
type ncontext =
  (string * term) list (*"id=term"*)
;;

(* CONTEXT MANAGEMENT *)

let emptyctx =
  []
;;

let addbinding ctx x bind =
  (x, bind) :: ctx
;;

let getbinding ctx x =
  List.assoc x ctx
;;

(* VARIABLE CONTEXT MANAGEMENT *)

let emptynctx =
  []
;;

let addvariable ctx x term =
  (x, term) :: ctx
;;


(* TYPE MANAGEMENT (TYPING) *)
let rec string_of_ty ty = match ty with
    TyBool ->
      "Bool"
  | TyNat ->
      "Nat"
  | TyArr (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ ")" ^ " -> " ^ "(" ^ string_of_ty ty2 ^ ")"
  (***********************************************************)
  | TyProd (ty1,ty2)->
      "{" ^ string_of_ty ty1 ^ "," ^ string_of_ty ty2 ^ "}" 
  | TyRecord(list)-> 
    let fieldtype=function(name,ty)->name^":"^(string_of_ty ty) 
    in "{"^String.concat ", "(List.map fieldtype list)^"}"
;;

exception Type_error of string
;;
exception Naming_error of string
;;

let rec subtype tyS tyT =
  (*if the types match, nothing else is checked*)
  (=) tyS tyT ||
    match (tyS,tyT) with
      (TyRecord(fS), TyRecord(fT)) ->
      List.for_all 
      (fun (li,tyTi) ->
        try 
          let tySi = List.assoc li fS in
          subtype tySi tyTi
        with
          Not_found -> false)
      (*the list of fields from the supertype candidate is traversed
        looking for homologous fields in the subtype candidate*)
      fT
    | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      (*contravariant changes in the argument types*)
      (*covariant changes in result types*)
      (subtype tyT1 tyS1) && (subtype tyS2 tyT2)
    | (_,_) ->
      false;;

(* TERMS MANAGEMENT (EVALUATION) *)

let rec string_of_term = function
    TmTrue ->
      "true"
  | TmFalse ->
      "false"
  | TmIf (t1,t2,t3) ->
      "if " ^ "(" ^ string_of_term t1 ^ ")" ^
      " then " ^ "(" ^ string_of_term t2 ^ ")" ^
      " else " ^ "(" ^ string_of_term t3 ^ ")"
  | TmZero ->
      "0"
  | TmSucc t ->
     let rec f n t' = match t' with
          TmZero -> string_of_int n
        | TmSucc s -> f (n+1) s
        | _ -> "succ " ^ "(" ^ string_of_term t ^ ")"
      in f 1 t
  | TmPred t ->
      "pred " ^ "(" ^ string_of_term t ^ ")"
  | TmIsZero t ->
      "iszero " ^ "(" ^ string_of_term t ^ ")"
  | TmVar s ->
      s
  | TmAbs (s, tyS, t) ->
      "(lambda " ^ s ^ ":" ^ string_of_ty tyS ^ ". " ^ string_of_term t ^ ")"
  | TmApp (t1, t2) ->
      "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"
  (************************************)
  | TmFix(abs)->
        string_of_term abs
  | TmLet (s, t1, t2) ->
      (match t1 with
      (*the let rec expression is a special let containing a fix combinator, and is printed as such*)
      |TmFix(TmAbs(s1, tyS, t))->"let rec " ^ s ^ " : " ^ string_of_ty (tyS) ^ " = " ^ string_of_term t ^ " in " ^ string_of_term t2
      |_->"let " ^ s ^ " = " ^ string_of_term t1 ^ " in " ^ string_of_term t2)
  | TmPair(t1,t2)->
       "{" ^ string_of_term t1 ^ "," ^ string_of_term t2 ^ "}"
  | TmProj1(t)-> string_of_term t ^ ".1"
  | TmProj2(t)-> string_of_term t ^ ".2"
  | TmRecord(list)->
    let fieldterm=
      function(name,term)->name^"="^(string_of_term term) 
    in "{"^String.concat ", "(List.map fieldterm list)^"}"
  | TmProj(record,label)->(string_of_term record) ^ "."^label
;;

let rec typeof nctx ctx tm = match tm with
    (* T-True *)
  |  TmTrue ->
      TyBool

    (* T-False *)
  | TmFalse ->
      TyBool

    (* T-If *)
  | TmIf (t1, t2, t3) ->
      if typeof nctx ctx t1 = TyBool then
        let tyT2 = typeof nctx ctx t2 in
        if typeof nctx ctx t3 = tyT2 then tyT2
        else raise (Type_error "arms of conditional have different types")
      else
        raise (Type_error "guard of conditional not a boolean")
      
    (* T-Zero *)
  | TmZero ->
      TyNat

    (* T-Succ *)
  | TmSucc t1 ->
      if typeof nctx ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")

    (* T-Pred *)
  | TmPred t1 ->
      if typeof nctx ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")

    (* T-Iszero *)
  | TmIsZero t1 ->
      if typeof nctx ctx t1 = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")

    (* T-Var *)
  | TmVar x ->
    (*The global variable context is checked before concluding the variable has not been declared*)
      (try getbinding ctx x with
       Not_found -> (try typeof nctx ctx (List.assoc x nctx) with
          Not_found->raise (Type_error ("no binding type for variable " ^ x))))

    (* T-Abs *)
  | TmAbs (x, tyT1, t2) ->
      let ctx' = addbinding ctx x tyT1 in
      let tyT2 = typeof nctx ctx' t2 in
      TyArr (tyT1, tyT2)

  (* T-Pair *)
  | TmPair (t1,t2)->
    (*this allows nested pairs*)
    TyProd(typeof nctx ctx t1, typeof nctx ctx t2) 

  (* T-Proj1 *)
  | TmProj1(t)->
    (*this allows nested projections*)
    (match typeof nctx ctx t with 
        TyProd(a,b)->a
        |_->raise(Type_error"projections can only be applied to pairs or records"))
  (* T-Proj2 *)
  | TmProj2(t)->
    (*this allows nested projections*)
    (match typeof nctx ctx t with 
        TyProd(a,b)->b
        |_->raise(Type_error"projections can only be applied to pairs or records"))

    (* T-App *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof nctx ctx t1 in
      let tyT2 = typeof nctx ctx t2 in
      (match tyT1 with
        TyArr (tyT11, tyT12) ->
          (*an abstraction is well-typed if the following holds*)
          if subtype tyT2 tyT11 then tyT12
          else raise (Type_error "parameter type mismatch")
      | _ -> raise (Type_error "arrow type expected"))

    (* T-Let *)
  | TmLet (x, t1, t2) ->
    let tyT1 = typeof nctx ctx t1 in
    let ctx' = addbinding ctx x tyT1 in
    typeof nctx ctx' t2

  (* T-Fix *)
  | TmFix t->
    (match typeof nctx ctx t with
      TyArr(tyT1,tyT2)->
        (*the type changes w.r.t. simple application because of its recursive nature*)
        if subtype tyT1 tyT2 then tyT1
        else raise (Type_error "recursive type mismatch")
    |_->raise (Type_error "arrow type expected"))

  (*T-Rcd*)
  | TmRecord list->
    let fieldtype =
      function (s, t) -> (s, typeof nctx ctx t) in
    (*every field needs to be well-typed*)
    TyRecord (List.map fieldtype list)

  (*T-Proj*)
  | TmProj(rcd,label)->
    (match (typeof nctx ctx rcd) with 
      (*A projection is well-typed if its record is well-typed*)
      TyRecord(list)->
        try 
          List.assoc label list 
        with
          Not_found->raise(Type_error "the label does not exist")
      |_-> raise (Type_error "projections can only be applied to pairs or records"))
;;




let rec ldif l1 l2 = match l1 with
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;

let rec lunion l1 l2 = match l1 with
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;

let rec free_vars tm =
   match tm with
    TmTrue ->
      []
  | TmFalse ->
      []
  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero ->
      []
  | TmSucc t ->
      free_vars t
  | TmPred t ->
      free_vars t
  | TmIsZero t ->
      free_vars t
  | TmVar s ->
      [s]
  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]
  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmLet (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmFix (abs)->
    free_vars abs
  | TmRecord(list)->
      let rec aux l acc=match l with
        (name,term)::b-> aux b (lunion (free_vars term) acc)
        |[]->acc
      in aux list []
  | TmProj(rcd,label)-> free_vars rcd
;;

let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm = 
  match tm with
    TmTrue ->
      TmTrue
  | TmFalse ->
      TmFalse
  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero ->
      TmZero
  | TmSucc t ->
      TmSucc (subst x s t)
  | TmPred t ->
      TmPred (subst x s t)
  | TmIsZero t ->
      TmIsZero (subst x s t)
  | TmVar y ->
      if y = x then s else tm
  | TmAbs (y, tyY, t) -> 
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t))  
  | TmApp (t1, t2) ->
      TmApp (subst x s t1, subst x s t2)
  | TmLet (y, t1, t2) ->
      if y = x then TmLet (y, subst x s t1, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLet (y, subst x s t1, subst x s t2)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLet (z, subst x s t1, subst x s (subst y (TmVar z) t2))
  (**********************************************************************)
    (*pair substitution entails substituting the two values*)
  | TmPair(t1,t2)->TmPair(subst x s t1, subst x s t2)
    (*to substitute with a projection, the pair is substituted first*)
  | TmProj1(pair)->(match (subst x s pair) with TmPair(a,b)->a)
  | TmProj2(pair)->(match (subst x s pair) with TmPair(a,b)->b)
    (*to substitute with a projection, the record is substituted first*)
    (*List.assoc is safe because it was checked during typechecking*)
  | TmProj(rcd,label)->
    (match (subst x s rcd) with 
        TmRecord(list)->List.assoc label list
        |_->tm)
    (*record substitution is performed field by field*) 
  | TmRecord(list)-> 
    let subst_field= 
      function(name,term)->(name,subst x s term)
    in TmRecord(List.map subst_field list)
  | TmFix(t)-> 
    (match t with 
      (*this substitution grants general recursion*)
      TmAbs (y, tyY, t)->subst y tm t)
;;

let rec isnumericval tm = match tm with
    TmZero -> true
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | t when isnumericval t -> true
  (*Pairs and records are checked field by field*)
  | TmPair(t1,t2)-> (isval t1) && (isval t2)
  | TmRecord(list)->
    let isval_field= 
      function(name,term)->isval term
    in List.for_all isval_field list
  | _ -> false
;;

exception NoRuleApplies
;;

let rec eval1 tm nctx debug =
  (*the debug flag is maintained during recursion*)
  if debug then Printf.printf "#%s\n" (string_of_term tm);
  match tm with
    (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 t1 nctx debug  in
      TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 t1 nctx debug  in
      TmSucc t1'

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 t1 nctx debug  in
      TmPred t1'

    (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse

    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 t1 nctx debug  in
      TmIsZero t1'

    (* E-AppAbs *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 t2 nctx debug  in
      TmApp (v1, t2')

    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 t1 nctx debug  in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLet (x, v1, t2) when isval v1 ->
      subst x v1 t2
    (* E-Let *)
  | TmLet(x, t1, t2) ->
      let t1' = eval1 t1 nctx debug  in
      TmLet (x, t1', t2) 
  (*******************************************************)
    (*Beta rules require terms to be values, so they are more specific and ought to be written before
      more generic rules*)
    (*E-FixBeta*)
    (*substitute the name of the function by the fix combinator in the body of the function*)
  | TmFix(TmAbs(s,tyY,t))-> subst s tm t
    (*E-Fix*)
  | TmFix (t1)->
    let t1'= eval1 t1 nctx debug  in
      TmFix (t1')
    (*E-PairBeta1*)
  | TmProj1(TmPair(t1,t2) as pair) when (isval pair)-> t1
    (*E-PairBeta2*)
  | TmProj2(TmPair(t1,t2) as pair) when (isval pair)-> t2
    (*E-Proj1*)
  | TmProj1(pair)->
      let tm'= eval1 pair nctx debug  in
        TmProj1(tm')
    (*E-Proj2*)
  | TmProj2(pair)->
      let tm'= eval1 pair nctx debug  in
        TmProj2(tm')
    (*E-Pair2*)
  | TmPair(t1,t2) when isval t1->
      let t2'= eval1 t2 nctx debug  in
        TmPair(t1,t2')
    (*E-Pair1*)
  | TmPair(t1,t2)->
      let t1'= eval1 t1 nctx debug  in
        TmPair(t1',t2)
  |TmVar(name)->List.assoc name nctx
    (*E-Record*)
  |TmRecord(list)->
    (*eval2 ensures the evaluation of nested records*)
    let rec eval2 tm nctx=
        try
          let tm' = eval1 tm nctx debug  in
          eval2 tm' nctx
        with
          NoRuleApplies -> tm
      in 
        let field_eval=
          function(name,term)->(name,(eval2 term nctx)) 
        in TmRecord(List.rev (List.map field_eval (list)))
    (*E-ProjRCD*)
  |TmProj(TmRecord(list) as rcd,label) when isval rcd-> List.assoc label list
  (*E-Proj*)
  | TmProj(rcd,label)->
      let tm'= eval1 rcd nctx debug  in
        TmProj(tm',label)
  | _ ->
      raise NoRuleApplies
;;

let rec eval tm nctx debug =
  try
    let tm' = eval1 tm nctx debug  in
    eval tm' nctx debug
  with
    (*given that the typechecker works, if no rule applies the term is a value*)
    NoRuleApplies -> tm
;;


let execute_instruction ctx nctx debug= function
  Eval(tm)->
    (*the typechecker is executed before evaluating to ensure type safety*)
    let tyTm=typeof nctx ctx tm in
    let evTm=eval tm nctx debug in
    print_endline ("-: " ^ string_of_term evTm ^ " : " ^ string_of_ty tyTm);
    (*the return value is the unchanged variable context*)
    nctx
  |Assign(name,tm)->
    (*the typechecker is executed before evaluating to ensure type safety*)
    let tyTm=typeof nctx ctx tm in
    let evTm=eval tm nctx debug in
      print_endline ("-: " ^ name ^ "="^string_of_term evTm ^ " : " ^ string_of_ty (tyTm));
      (*the assignment adds a variable into the variable context*)
      (name,evTm)::(List.remove_assoc name nctx);;