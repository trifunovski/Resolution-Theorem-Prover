structure Examples =
struct
  open Resolution
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
end
