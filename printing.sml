(* put separator element between elements of the list *)
structure Printing =
struct
  open Definitions
  
  fun intersperse(sep : 'a, xs : 'a list) : 'a list =
    case xs of
      []        => []
    | (x :: []) => x :: []
    | (x :: xs) => x :: sep :: intersperse(sep, xs)

  fun showTerm(t : term) : string =
    case t of
      TConst c => c
    | TVar s => s
    | TFunction(f, _, xs) =>
        f ^ "(" ^ concat(intersperse(",", map showTerm xs)) ^ ")"

  fun showTerms ((t1,t2) : (term * term)) : string = "{" ^ (showTerm t1) ^ " = " ^ (showTerm t2) ^ "}"

  fun printTermList (xs : substitution) : unit = (print (concat(intersperse(" , ", map showTerms xs))); print "\n")

  fun showSubs ((t1,t2) : (term * term)) : string = "{" ^ (showTerm t1) ^ " / " ^ (showTerm t2) ^ "}"

  fun printTermSubs (xs : substitution) : unit = (print (concat(intersperse(" , ", map showSubs xs))); print "\n")

  fun show(x : formula) : string =
    case x of
      FTruth => "⊤"
    | FFalsity => "⊥"
    | FConj(y, z) => "(" ^ show y ^ " ∧ " ^ show z ^ ")"
    | FDisj(y, z) => "(" ^ show y ^ " ∨ " ^ show z ^ ")"
    | FImp(y, z) => "(" ^ show y ^ " → " ^ show z ^ ")"
    | FNeg y => "(" ^ "¬" ^ show y ^ ")"
    | FForall(var, y) => "∀" ^ var ^ ". " ^ "(" ^ show y ^ ")"
    | FExists(var, y) => "∃" ^ var ^ ". " ^ "(" ^ show y ^ ")"
    | FRel(name, 0, []) => name
    | FRel(name, _, xs) =>
        name ^ "(" ^ concat(intersperse(",", map showTerm xs)) ^ ")"

  (* print formula *)
  fun printFormula(x : formula) : unit = (print (show x); print "\n")

  fun showClause (c : clause) : string =
    case c of
      [] => ""
    | [l] => show l
    | l :: ls => (show l) ^ ", " ^ (showClause ls)
  and showSet (s : set) : string =
    case s of
      [] => ""
    | [c] => "{ " ^ (showClause c) ^ " }"
    | c::cs => "{ " ^ (showClause c) ^ " } , " ^ (showSet cs)
  and printSet (s : set) : unit =
    (print "{ "; print (showSet s); print" } \n")
end
