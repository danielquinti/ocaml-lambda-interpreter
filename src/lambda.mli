
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyProd of ty * ty
  | TyRecord of (string*ty) list

type context =
  (string * ty) list
;;

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
  | TmFix of term
  | TmPair of term * term
  | TmProj1 of term
  | TmProj2 of term
  | TmRecord of (string * term) list
  | TmProj of term * string
;;

type instruction=
  Eval of term
  |Assign of string * term

type ncontext =
  (string * term) list
;;




val emptyctx : context;;
val addbinding : context -> string -> ty -> context;;
val getbinding : context -> string -> ty;;

val emptynctx : ncontext;;


val string_of_ty : ty -> string;;
exception Type_error of string;;
exception Naming_error of string;;

val string_of_term : term -> string;;
exception NoRuleApplies;;
val eval : term -> ncontext-> bool->term;;

val execute_instruction: context->ncontext->bool->instruction->ncontext