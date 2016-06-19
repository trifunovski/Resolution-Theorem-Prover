structure Helpers =
struct
  open Printing
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
end
