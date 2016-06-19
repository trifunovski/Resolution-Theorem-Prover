(* Prenex normal form converter for first-order logic
   COMP 360 *)
structure Definitions =
struct
  exception Cannot_Unify
  exception Resolution_Error
  exception Cannot_Resolve
  exception BOX_FOUND

  datatype term =
      TVar of string
    | TConst of string
    | TFunction of string * int * term list (* name, arity, args *)

  datatype formula =
      FTruth (* ⊤ *)
    | FFalsity (* ⊥ *)
    | FConj of formula * formula
    | FDisj of formula * formula
    | FImp of formula * formula
    | FNeg of formula
    | FForall of string * formula
    | FExists of string * formula
    | FRel of string * int * term list (* name, arity, args *)

  type substitution = (term * term) list

  type literal = formula
  type clause = literal list
  type set = clause list

end
