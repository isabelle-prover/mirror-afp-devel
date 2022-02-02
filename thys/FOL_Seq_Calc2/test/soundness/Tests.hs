module Tests where

testcases :: [(String, String)]
testcases =
  [ ("imp", "Imp a b"),
    ("con", "Con a a"),
    ("p", "p"),
    ("functions", "p[a, f[a], f[f[a]]]"),
    ("ImpDisCon", "Imp (Dis p q) (Con p q)"),
    ("UniExi", "Imp (Exi p[0]) (Uni p[0])"),
    ("LEM-dual", "Con p (Neg p)"),
    ("negBasic", "Neg (Dis p p)"),
    ("negImp", "Neg (Imp p p)"),
    ("wrongImp", "Imp (Imp q (Imp p q)) p"),
    ("tripleNeg", "Neg (Neg (Neg (Dis p (Neg p))))"),
    ("doubleNeg", "Neg (Neg p)"),
    ("DisCon", "Dis (Con a b) (Con b a)"),
    ("WrongPre", "Imp (Uni p[0]) q[a]"),
    ("WrongFun", "Imp p[a] p[b]"),
    ("WrongUniVar", "Imp (Uni p[1]) p[a]"),
    ("ExiNotUni", "Imp (Exi p[0]) p[a]"),
    ("notAbsorb1", "Neg (Imp (Con p (Dis p q)) p)"),
    ("notAbsorb2", "Neg (Imp (Dis p (Con p q)) p)"),
    ("ex7.2b", "Imp (Imp (Uni p[0]) (Uni q[0])) (Uni (Imp p[0] q[0]))"),
    ("ex7.4b", "Imp (Uni (Imp A[0] B[0])) (Imp (Exi A[0]) (Uni B[0]))"),
    ("ex7.4c", "Imp (Dis (Uni A[0]) (Exi B[0])) (Uni (Dis A[0] B[0]))"),
    ("ex7.4d", "Imp (Imp (Exi A[0]) (Exi B[0])) (Uni (Imp A[0] B[0]))"),
    ("ex7.9", "Imp (Imp (Uni p[0]) (Uni q[0])) (Uni (Imp p[0] q[0]))"),
    ("ex9.4", "Imp (Uni (Exi A[1,0])) (Uni A[0, f[0]])"),
    ("multiDelta", "Dis (Uni P[0]) (Uni (Neg P[0]))")
  ]
