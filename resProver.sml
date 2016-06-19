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

val sub1 = [(TVar "X",TFunction ("f",1,[TVar "Y"])), (TFunction ("g",1,[TVar "Y"]), TFunction ("g",1,[TVar "X"]))]

val sub2 = [(TFunction ("f",2,[TVar "X1", TConst "c"]) , (TFunction ("f",2,[TConst "c", TVar "X1"]))) ,
            (TFunction ("g",2,[TConst "d", TVar "X1"]) , (TFunction ("g",2,[TVar "X2", TVar "X3"]))) ,
            (TFunction ("h",1,[TVar "X2"]) , TConst "c")]

val sub3 = [(TFunction ("P",3,[TConst "a", TVar "Y", TFunction ("f",1,[TVar "Y"])]) ,
             TFunction ("P",3,[TVar "Z", TVar "Z", TVar "U"]))]

val sub4 = [(TVar "X", TFunction("f", 1, [TVar "Y"]))]
val sub5 = [(TFunction("f", 2, [TVar "X", TFunction("c", 0, [])]),
             TFunction("f", 2, [TFunction("c", 0, []), TVar "X"])),
             (TFunction("g", 2, [TFunction("d", 0, []), TVar "X1"]),
             TFunction("g", 2, [TVar "X2", TVar "X3"])),
             (TFunction("h", 1, [TVar "X2"]), TFunction("c", 0, []))
             ]

val sub6 = [(TConst "a",TConst "a")]
val sub7 = [(TVar "X", TVar "X")]
val sub8 = [(TConst "a", TVar "X")]
val sub9 = [(TConst "a",TConst "b")]
val sub10 = [(TVar "X", TVar "Y")]
val sub11 = [(TFunction("f", 2, [TConst "a", TVar "X"]),
               TFunction("f", 2, [TConst "a", TConst "b"]))]
val sub12 = [(TFunction("f", 1, [TConst "a"]),
             TFunction("g", 1, [TConst "a"]))]
val sub13 = [(TFunction("f", 1, [TVar "X"]),
             TFunction("f", 1, [TVar "Y"]))]
val sub14 = [(TFunction("f", 1, [TFunction("g", 1, [TVar "X"])]),
             TFunction("f", 1, [TVar "Y"]))]
val sub15 = [(TFunction("f", 1, [TFunction("g", 1, [TVar "X"]), TVar "X"]),
             TFunction("f", 1, [TVar "Y", TConst "a"]))]
val sub16 = [(TVar "X", TVar "Y"), (TVar "Y", TConst "a")]
val sub17 = [(TVar "X", TConst "a"), (TConst "b", TVar "X")]

(* Propositional symbols are relations with arity 0 *)
fun pSym (s : string) : formula = FRel (s, 0, [])

(* (∀x. (R(x)) → ∃x. (R(x))) *)
val e1 = FImp ((FForall ("x", (FRel ("R", 1, [TVar "x"])))),
               (FExists ("x", (FRel ("R", 1, [TVar "x"])))))

val e2 = FImp ((FExists ("x", (FRel ("R", 1, [TVar "x"])))),
               (FExists ("x", (FRel ("R", 1, [TVar "x"])))))


(* ∀x. ((∃y. (ϕ(y)) ∨ (∃z. (ψ(z)) → ρ(x)))) *)
val e3 =
  FForall ("x",
           FDisj
             ((FExists ("y", FRel ("ϕ", 1, [TVar "y"]))),
              (FImp (FExists ("z", FRel ("ψ", 1, [TVar "z"])),
                     (FRel ("ρ", 1, [TVar "x"])) ))))

val e4 = FNeg (FDisj (FExists ("x", FRel ("P",1,[TVar "x"])),
                      FExists ("x", FRel ("Q",1,[TVar "x"]))))

val e5 = FImp (FConj (FImp (pSym "P", pSym "Q"), pSym "P"), pSym "Q")

val e6 = FDisj (FDisj (FConj (pSym "A", pSym "B"), FConj (pSym "C", pSym "D")), pSym "E")

val e7 = (FImp (FConj (FImp (pSym "A", pSym "B") , pSym "A") , pSym "B"))

val e8 = FRel("R", 1, [TVar "x"])
val e9 = FNeg(FRel("R", 1, [TVar "x"]))
val e10 = FImp (FDisj(FConj(pSym "A", pSym "B"), FDisj(FConj(pSym "C", pSym "D"), pSym "E")) , FDisj(FDisj(pSym "E", FConj(pSym "C", pSym "D")), FConj(pSym "A", pSym "B")))
val e11 = FDisj(FDisj(pSym "E", FConj(pSym "C", pSym "D")), FConj(pSym "A", pSym "B"))

val e12 = FImp (FExists ("x", FDisj (FRel ("P", 1, [TVar "x"]), FRel ("Q", 1 , [TVar "x"]))) ,
                FDisj (FExists ("x" , FRel ("P", 1, [TVar "x"])) , FExists("x" , FRel ("Q" , 1, [TVar "x"])) )
               )
val e13 = FImp (FConj (FForall ("x", FNeg(FRel ("P" , 1, [TVar "x"]) )) ,
                       FForall ("x", FImp (FRel ("Q",1,[TVar "x"]) , FRel ("P",1,[TVar "x"]))))
                       , FForall ("x", FNeg (FRel ("Q", 1, [TVar "x"]))))

val drinkPar = FExists ("y" , FImp (FRel ("D", 1, [TVar "y"]) , FForall ("x", FRel ("D", 1, [TVar "x"]))))


(* put separator element between elements of the list *)
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

fun applyToSubformula (f : formula -> formula) (x : formula) : formula =
  case x of
    FConj(y, z) => FConj (f y, f z)
  | FDisj(y, z) => FDisj (f y, f z)
  | FImp(y, z) => FImp (f y, f z)
  | FNeg y => FNeg (f y)
  | FForall(var, y) => FForall (var, f y)
  | FExists(var, y) => FExists (var, f y)
  | _ => x

fun removeImp (x : formula) : formula =
  case x of
    FImp(y, z) => FDisj(FNeg (removeImp y), (removeImp z))
  | _ => applyToSubformula removeImp x

fun applyDeMorgan (x : formula) : formula =
  case x of
    FNeg (FNeg y) => applyDeMorgan y
  | FNeg (FConj (z, w)) => FDisj ( applyDeMorgan (FNeg z), applyDeMorgan (FNeg w))
  | FNeg (FDisj (z, w)) => FConj ( applyDeMorgan (FNeg z), applyDeMorgan (FNeg w))
  | _ => applyToSubformula applyDeMorgan x

fun distributeStep (x : formula) : formula =
  case x of
    FDisj ((FConj (y1, y2)), z) => FConj (distributeStep (FDisj (z, y1)), distributeStep (FDisj (z, y2)))
  | FDisj (y , (FConj (z1, z2))) => FConj (distributeStep (FDisj (y, z1)), distributeStep (FDisj (y, z2)))
  | _ => x

fun distribute (x : formula) : formula =
  case x of
    FDisj (y, z) => let val (y', z') = (distribute y, distribute z)
                    in distributeStep (FDisj (y' , z'))
                    end
  | _ => applyToSubformula distribute x

fun convertToCNF (x : formula) : formula =
  (distribute (applyDeMorgan (removeImp x)))

fun isQuantifierFree(x : formula) : bool =
  case x of
    FConj(y, z) => isQuantifierFree y andalso isQuantifierFree z
  | FDisj(y, z) => isQuantifierFree y andalso isQuantifierFree z
  | FImp(y, z) => isQuantifierFree y andalso isQuantifierFree z
  | FNeg y => isQuantifierFree y
  | FForall(var, y) => false
  | FExists(var, y) => false
  | _ => true

fun isPrenex(x : formula) : bool =
  case x of
    FForall(_, y) => isPrenex y
  | FExists(_, y) => isPrenex y
  | _ => isQuantifierFree x

val freshCount : int ref = ref 0

fun renameTerm(x : term, old : string, new : string) : term =
  case x of
    TConst c => TConst c
  | TVar s => TVar (if s = old then new else s)
  | TFunction(name, a, xs) =>
      TFunction(name, a, map (fn t => renameTerm (t, old, new)) xs)

fun renameFormula(x : formula, old : string, new : string) : formula =
  case x of
    FForall(var, y) =>
      if var = old then x else FForall(var, renameFormula (y, old, new))
  | FExists(var, y) =>
      if var = old then x else FExists(var, renameFormula (y, old, new))
  | FRel(name, a, xs) =>
      FRel(name, a, map (fn t => renameTerm (t, old, new)) xs)
  | _ => applyToSubformula (fn y => renameFormula (y, old, new)) x

(* Only changes the names of bounded variables *)
(* Assumes that the users wouldn't name their variables beginning with _
*  Can be checked, of course, but seemed unnecessary *)
fun renameBoundedVars(x : formula) : formula =
  case x of
    FForall(var, y) =>
      let val () = freshCount := (!freshCount) + 1
          val new = "_z" ^ Int.toString (!freshCount)
      in FForall(new, renameFormula(y, var, new)) end
  | FExists(var, y) =>
      let val () = freshCount := (!freshCount) + 1
          val new = "_z" ^ Int.toString (!freshCount)
      in FExists(new, renameFormula(y, var, new)) end
  | FRel(name, a, xs) => x
  | _ => applyToSubformula renameBoundedVars x

fun prenexRule (x : formula) : formula =
  case x of
  (* Negation rules *)
    FNeg(FExists(var, y)) => FForall(var, FNeg(y))
  | FNeg(FForall(var, y)) => FExists(var, FNeg(y))
  (* Conjunction rules *)
  | FConj(FForall (var, y), z) => FForall(var, FConj(y, z))
  | FConj(y, FForall (var, z)) => FForall(var, FConj(y, z))
  | FConj(FExists (var, y), z) => FExists(var, FConj(y, z))
  | FConj(y, FExists (var, z)) => FExists(var, FConj(y, z))
  (* Disjunction rules *)
  | FDisj(FForall (var, y), z) => FForall(var, FDisj(y, z))
  | FDisj(y, FForall (var, z)) => FForall(var, FDisj(y, z))
  | FDisj(FExists (var, y), z) => FExists(var, FDisj(y, z))
  | FDisj(y, FExists (var, z)) => FExists(var, FDisj(y, z))
  (* Implication antecedent rules *)
  | FImp(FForall(var, y), z) => FExists(var, FImp(y, z))
  | FImp(FExists(var, y), z) => FForall(var, FImp(y, z))
  (* Implication consequent rules *)
  | FImp(y, FForall(var, z)) => FForall(var, FImp(y, z))
  | FImp(y, FExists(var, z)) => FExists(var, FImp(y, z))
  | _ => x

(*
* This is a hacky implementation, can be made more efficient.
* You can mark quantifier free formulae so that you wouldn't have to
* run toPrenex on them again later.
*)
fun applyPrenex(x : formula) : formula =
  if isPrenex x
  then x
  else applyPrenex (prenexRule (applyToSubformula applyPrenex x))

(*
* First we rename all bounded variables with fresh names,
* because we don't want to deal with substitutions.
* We don't have to do aggressive renaming, but this makes the code cleaner.
*)
val toPrenex = applyPrenex o renameBoundedVars


fun getNewPairs (l1 : term list) (l2 : term list) (total : (term * term) list) : (term * term) list =
  case (l1,l2) of
    ([],[]) => total
  | (x::xs,y::ys) => getNewPairs xs ys ((x,y)::total)

fun occurs (x : string) (t : term) : bool =
  case t of
    TConst _ => false
  | TVar y => x = y
  | TFunction (_,_,ts) => occurs_inList x ts
and occurs_inList (x : string) (l : term list) : bool =
  case l of
    [] => false
  | t :: ts => (occurs x t) orelse (occurs_inList x ts)


fun applySubstitution ((x, t2) : (string * term)) (l : substitution) =
  case l of
    [] => []
  | (tm1, TConst c)::tms => (tm1, TConst c)::(applySubstitution (x,t2) tms)
  | (tm1, TVar y)::tms => if y = x then (tm1,t2)::(applySubstitution (x,t2) tms)
                      else (tm1,TVar y)::(applySubstitution (x,t2) tms)
  | (tm1, TFunction (f,n,terms))::tms => (tm1, TFunction (f, n, appSubList (x, t2) terms))::(applySubstitution (x,t2) tms)
and appSubInRelationList (l : term list) (s : substitution) =
  case s of
    [] => l
  | (TVar x, t)::subs => appSubInRelationList (appSubList (x,t) l) subs
and appSubList ((x, t2) : (string * term)) (l : term list) =
  case l of
    [] => []
  | t::ts => (appSingleSub (x, t2) t)::(appSubList (x, t2) ts)
and appSingleSub ((x, t2) : (string * term)) (t : term) =
  case t of
    TConst c => TConst c
  | TVar y => if y = x then t2 else TVar y
  | TFunction (f,n,terms) => TFunction (f, n, appSubList (x, t2) terms)
and applySubToNormalList ((x, t) : (string * term)) (l : (term * term) list) =
  case l of
    [] => []
  | (t1,t2)::ts => let val t1' = appSingleSub (x, t) t1
                       val t2' = appSingleSub (x, t) t2
                   in (t1',t2')::(applySubToNormalList (x,t) ts) end

fun unify (s : (term * term) list) (sub : substitution) : substitution =
  case s of
    [] => sub
  | (t1, t2)::ts => if t1=t2 then unify ts sub
                    else (* let val () = print ("This is the set: ")
                             val () = (printTermList s)
                             val () = print ("This is the substitution: ")
                             val () = printTermSubs sub
                         in *)
                      (case (t1,t2) of
                        (TFunction (xName, xArity, xList), TFunction (yName, yArity, yList)) =>
                          if xName<>yName orelse xArity<>yArity then raise Cannot_Unify
                          else unify (getNewPairs xList yList ts) sub
                      | (TVar x, _) => if occurs x t2 then raise Cannot_Unify
                                       else
                                          let val newTermList = applySubToNormalList (x,t2) ts
                                              val newSubstitution = (applySubstitution (x,t2) sub) @ [(t1,t2)]
                                          in unify newTermList newSubstitution
                                          end
                      | (_, TVar x) => unify ((t2,t1)::ts) sub
                      | (_, _) => raise Cannot_Unify)
                      (* end *)

fun unification (s : (term * term) list) : unit = printTermSubs (unify s [])

fun replaceTerm (var : string) (newTerm : term) (oldTerm : term) =
  case oldTerm of
    TVar x => if var = x then newTerm else oldTerm
  | TConst c => oldTerm
  | TFunction (str, ar, l) => TFunction (str, ar, (replaceList var newTerm l) )

and replaceList (var : string) (newTerm : term) (l : term list) =
  case l of
   [] => []
   | t :: ts => (replaceTerm var newTerm t) :: (replaceList var newTerm ts)

fun replace (var : string) (newTerm : term) (f : formula) =
  case f of
    FRel (str, ar, l) => FRel (str, ar , replaceList var newTerm l)
  | _ => applyToSubformula (replace var newTerm) f

fun getSkolem (vars : string list) (arity : int) (terms : term list) : term =
  case vars of
    [] => let val () = freshCount := (!freshCount) + 1
          val new = "_f" ^  Int.toString (!freshCount)
          in TFunction (new , arity , terms)
          end
  | x :: xs => getSkolem xs (arity + 1) ((TVar x) :: terms)

fun skolemize (f : formula) (vars : string list)  : formula =
  case f of
    FExists (var , rest) => let val newTerm = getSkolem vars 0 []
                            in skolemize (replace var newTerm rest) vars
                            end
  | FForall (var , rest) => skolemize rest (var :: vars)
  | _ => f


fun getClauses (f : formula) : clause =
  case f of
      FNeg (FRel (_,_,_)) => [f]
    | FRel(_,_,_) => [f]
    | FDisj(y , z) => (getClauses y) @ (getClauses z)
    | _ => raise Resolution_Error

fun makeSet (f : formula) : set =
  case f of
    FConj(y, z) => (makeSet y) @ (makeSet z)
  | _ => [getClauses f]

fun zip (l1 : term list) (l2 : term list) : (term * term) list =
  case (l1,l2) of
    ([],[]) => []
  | (x::xs, y::ys) => (x,y) :: (zip xs ys)

fun tryUnify (l1 : term list) (l2 : term list) : substitution option =
  SOME (unify (zip l1 l2) [])
  handle
    Cannot_Unify => NONE

fun termInList (t : term) (l : term list) =
  case l of
    [] => false
  | tm :: tms => if t = tm then true else termInList t tms

fun newVarsList (l : term list) (alrdReplaced : term list) =
  case l of
    [] => ([],alrdReplaced)
  | (TVar x)::rest => if termInList (TVar x) alrdReplaced then
                      let val (finish, replacements) = newVarsList rest alrdReplaced
                      in ((TVar x) :: finish , replacements)
                      end
                      else let val () = freshCount := (!freshCount) + 1
                               val new = "_w" ^ Int.toString (!freshCount)
                               val replaced = appSubList (x , TVar new) rest
                               val (finish, repl) = newVarsList replaced ((TVar new)::alrdReplaced)
                           in
                              ((TVar new) :: finish , repl)
                           end
  | (TFunction (n , a, tms))::ls => let val (finish, replacements) = newVarsList tms alrdReplaced
                                        val (newFin, newRepl) = newVarsList ls replacements
                                    in ((TFunction (n, a, finish))::newFin, newRepl)
                                    end
  | _ => (l, alrdReplaced)

fun newVars (l : literal) =
  case l of
    FRel (n1 , a1 , l1) => FRel (n1 , a1 , #1(newVarsList l1 []))
  | FNeg (FRel (n1 , a1 , l1)) => FNeg (FRel (n1 , a1 , #1(newVarsList l1 [])))
  | _ => raise Resolution_Error

fun findSingleCont (l : literal) (c2 : clause) : (literal * clause * substitution) option =
  case (l , c2) of
    (_ , []) => NONE
  | ((FRel (n1,a1,l1)), (FNeg(FRel (n2,a2,l2)))::rest) =>
            if n1 = n2 andalso a1=a2
            then (case tryUnify l1 (#1(newVarsList l2 [])) of
                    NONE => (case findSingleCont l rest of
                              NONE => NONE
                            | SOME (r1 , r2 , sub) => SOME (r1 , (FNeg(FRel (n2,a2,l2)))::r2, sub))
                  | SOME sub => SOME ((FNeg(FRel (n2,a2,l2))) , rest , sub))
            else (case findSingleCont l rest of
                      NONE => NONE
                    | SOME (r1 , r2 , sub) => SOME (r1 , (FNeg(FRel (n2,a2,l2)))::r2, sub))
  | (FNeg(FRel (n1,a1,l1)), (FRel (n2,a2,l2))::rest) =>
            if n1 = n2 andalso a1=a2
            then (case tryUnify l1 (#1(newVarsList l2 [])) of
                    NONE => (case findSingleCont l rest of
                              NONE => NONE
                            | SOME (r1 , r2 , sub) => SOME (r1 , (FRel (n2,a2,l2))::r2 , sub))
                  | SOME sub => SOME ((FRel (n2,a2,l2)) , rest , sub))
            else (case findSingleCont l rest of
                      NONE => NONE
                    | SOME (r1 , r2 , sub) => SOME (r1 , (FRel (n2,a2,l2))::r2 , sub))
  | (l , r :: rest) => (case findSingleCont l rest of
            NONE => NONE
          | SOME (r1 , r2 , sub) => SOME (r1 , r::r2 , sub))

fun findPossibleCont (c1 : clause) (c2 : clause) : (literal * clause * literal * clause * substitution) option =
  case c1 of
    [] => NONE
  | c :: restOfc1 => (case findSingleCont c c2 of
                      NONE => (case findPossibleCont restOfc1 c2 of
                                  NONE => NONE
                                | SOME (res1, resl1, res2, resl2, sub) => SOME (res1, c::resl1, res2, resl2, sub))
                    | SOME (rc , restOfc2 , sub) => SOME (c, restOfc1 , rc , restOfc2 , sub))

fun tryRes (c : clause) (rest : set) : (literal * clause * literal * clause * substitution * set) option =
  case rest of
    [] => NONE
  | r :: rs => (case findPossibleCont c r of
                  NONE => (case tryRes c rs of
                            NONE => NONE
                          | SOME (r1, restOfc1, r2, restOfc2 , sub , restOfSet) => SOME (r1, restOfc1, r2, restOfc2 , sub, r::restOfSet))
                | SOME (r1, restOfc1, r2, restOfc2, sub) => SOME (r1, restOfc1, r2, restOfc2 , sub, rs))

fun resolveWithNew (newSet : set) : (literal * clause * literal * clause * substitution * set) option =
  case newSet of
    [] => NONE
  | c :: cs => (case tryRes c cs of
                  SOME x => SOME x
                | NONE => (case resolveWithNew cs of
                            NONE => NONE
                          | SOME (r1, restOfc1, r2, restOfc2, sub, restOfSet) => SOME (r1, restOfc1, r2, restOfc2, sub , c::restOfSet)))

fun resolveWithOld (newSet : set) (oldSet : set) : (literal * clause * literal * clause * substitution * set * set) option =
  case newSet of
    [] => NONE
  | c::cs => (case tryRes c oldSet of
                  SOME (r1, restOfc1, r2, restOfc2, sub, restOfSet ) => SOME (r1, restOfc1, r2, restOfc2, sub, cs, oldSet)
              |   NONE => (case resolveWithOld cs oldSet of
                              NONE => NONE
                            | SOME (r1, restOfc1, r2, restOfc2, sub, restOfNewSet, oldSet) =>
                                  SOME (r1, restOfc1, r2, restOfc2, sub, c::restOfNewSet, oldSet)))

fun subLiteral (l : literal) (s : substitution) : literal =
  case l of
    FNeg x => FNeg (subLiteral x s)
  | FRel (n , a , tms) => FRel ( n , a , appSubInRelationList tms s )

fun subToClause (c : clause) (s : substitution) : clause =
  case c of
    [] => []
  | c :: cs => (subLiteral c s) :: (subToClause cs s)

fun isIn (l : literal) (c : clause) : bool =
  case c of
    [] => false
  | x :: xs => if l = x then true else isIn l xs

fun combine (c1 : clause) (c2 : clause) : clause =
  case c1 of
    [] => c2
  | c::cs => if isIn c c2 then combine cs c2 else c::(combine cs c2)

fun resolve (newSet : set) (oldSet : set) : (set * set) option =
  case resolveWithNew newSet of
     SOME (r1, restOfc1, r2, restOfc2, sub, restOfSet) =>
              let val () = ((print ("Resolving " ^ (show r1) ^ " with " ^ (show r2) ^ " from the Clauses {"
                  ^ (showClause (r1::restOfc1)) ^ "} and {" ^ (showClause (r2::restOfc2)) ^ "} with substitution "));
                    (printTermSubs sub))
              in
              (case (combine restOfc1 restOfc2) of
                [] => raise BOX_FOUND
              | notempty => SOME ((subToClause notempty sub)::restOfSet , (r1::restOfc1)::(r2::restOfc2)::oldSet))
              end
  |  NONE =>  (case resolveWithOld newSet oldSet of
                NONE => NONE
              | SOME (r1, restOfc1, r2, restOfc2, sub, restOfNewSet, _) =>
              let val () = ((print ("Resolving " ^ (show r1) ^ " with " ^ (show r2) ^ " from the Clauses {"
                  ^ (showClause (r1::restOfc1)) ^ "} and {" ^ (showClause (r2::restOfc2)) ^ "} with substitution "));
                    (printTermSubs sub))
              in
                (case (combine restOfc1 restOfc2) of
                  [] => raise BOX_FOUND
                | notempty => SOME ( (subToClause notempty sub)::restOfNewSet, (r1::restOfc1)::oldSet))
              end
              )



fun whileNotEmpty (newSet : set) (oldSet : set) =
let val () = (print "Set of new clauses : "; printSet newSet)
    val () = (print "Set of old clauses : "; printSet oldSet) in
  case newSet of
    [] => raise Cannot_Resolve
  | _ => (case resolve newSet oldSet of
            NONE => raise Cannot_Resolve
          | SOME (ns , os) => whileNotEmpty ns os)
end
  handle
    Cannot_Resolve => print "The formula could not be proven. \n"
  | BOX_FOUND => print "A contradiction has been found! \n"

fun resolution (f : formula) =
  let val neg = FNeg f
      val () = (print "Negated formula : "; printFormula neg)
      val prenex = toPrenex neg
      val () = (print "Formula in prenex : "; printFormula prenex)
      val skolemized = skolemize prenex []
      val () = (print "Skolemized formula : "; printFormula skolemized)
      val CNF = convertToCNF skolemized
      val () = (print "Formula in CNF : "; printFormula CNF)
      val set = makeSet CNF
  in whileNotEmpty set []
  end
