module Tests where

testcases :: [(String, String)]
testcases =
  [ ("true", "Imp a a")
  , ("false", "Neg (Neg (Imp a a))")
  , ("negations", "Imp (Neg p) (Neg (Neg (Neg p)))")
  , ("excludedMiddle", "Dis a (Neg a)")
  , ("excludedMiddle2", "Dis (Neg a) a")
  , ("impNeg", "Dis p (Imp p q)")
  , ("extraCon", "Imp (Con p q) (Imp r (Con p r))")
  , ("bigCon", "Con (Con (Imp a a) (Imp b b)) (Con (Imp c c) (Imp d d))")
  , ("deMorganUni", "Imp (Neg (Uni p[0])) (Exi (Neg (p[0])))")
  , ("deMorganExi", "Imp (Neg (Exi p[0])) (Uni (Neg (p[0])))")
  , ("ex7.2a", "Imp (Con (Uni p[0]) (Uni q[0])) (Uni (Con p[0] q[0]))")
  , ("ex7.2b", "Imp (Uni (Imp p[0] q[0])) (Imp (Uni p[0]) (Uni q[0]))")
  , ("ex7.3a", "Con (Imp (Exi (Imp A[0] B[0])) (Imp (Uni A[0]) (Exi B[0]))) (Imp (Imp (Uni A[0]) (Exi B[0])) (Exi (Imp A[0] B[0])))")
  , ("ex7.3b", "Imp (Imp (Exi A[0]) (Uni B[0])) (Uni (Imp A[0] B[0]))")
  , ("ex7.3c", "Imp (Uni (Dis A[0] B[0])) (Dis (Uni A[0]) (Exi B[0]))")
  , ("ex7.3d", "Imp (Uni (Imp A[0] B[0])) (Imp (Exi A[0]) (Exi B[0]))")
  , ("ex8.5", "Con (Imp (Uni (Imp p[0] q)) (Uni (Imp (Neg q) (Neg p[0])))) (Imp (Uni (Imp (Neg q) (Neg p[0]))) (Uni (Imp p[0] q)))")
  , ("ex8.6", "Imp (Uni (Con (Imp p[0] q[0]) (Imp q[0] p[0]))) (Con (Imp (Uni p[0]) (Uni q[0])) (Imp (Uni q[0]) (Uni p[0])))")
  , ("ex8.8a", "Con (Imp (Uni (Imp A B[0])) (Imp A (Uni B[0]))) (Imp (Imp A (Uni B[0])) (Uni (Imp A B[0])))")
  , ("ex8.8b", "Con (Imp (Exi (Imp A B[0])) (Imp A (Exi B[0]))) (Imp (Imp A (Exi B[0])) (Exi (Imp A B[0])))")
  , ("ex9.4a", "Imp (Uni A[0, f[0]]) (Uni (Exi A[1,0]))")
  ]
