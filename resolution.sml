structure Resolution =
struct
  open Helpers
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
end
