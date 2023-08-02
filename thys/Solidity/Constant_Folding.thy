section\<open>Constant Folding\<close>
theory Constant_Folding
imports
  Solidity_Main 
begin
text\<open>
  The following function optimizes expressions w.r.t. gas consumption.
\<close>
primrec eupdate :: "E \<Rightarrow> E" 
and lupdate :: "L \<Rightarrow> L"
where
  "lupdate (Id i) = Id i"
| "lupdate (Ref i xs) = Ref i (map eupdate xs)"
| "eupdate (E.INT b v) =
    (if (b\<in>vbits)
      then if v \<ge> 0
        then E.INT b (-(2^(b-1)) + (v+2^(b-1)) mod (2^b))
        else E.INT b (2^(b-1) - (-v+2^(b-1)-1) mod (2^b) - 1)
      else E.INT b v)"
| "eupdate (UINT b v) = (if (b\<in>vbits) then UINT b (v mod (2^b)) else UINT b v)"
| "eupdate (ADDRESS a) = ADDRESS a"
| "eupdate (BALANCE a) = BALANCE a"
| "eupdate THIS = THIS"
| "eupdate SENDER = SENDER"
| "eupdate VALUE = VALUE"
| "eupdate TRUE = TRUE"
| "eupdate FALSE = FALSE"
| "eupdate (LVAL l) = LVAL (lupdate l)"
| "eupdate (PLUS ex1 ex2) =
    (case (eupdate ex1) of
      E.INT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits
                then let v=v1+v2 in
                  if v \<ge> 0
                    then E.INT (max b1 b2) (-(2^((max b1 b2)-1)) + (v+2^((max b1 b2)-1)) mod (2^(max b1 b2)))
                    else E.INT (max b1 b2) (2^((max b1 b2)-1) - (-v+2^((max b1 b2)-1)-1) mod (2^(max b1 b2)) - 1)
                else (PLUS (E.INT b1 v1) (E.INT b2 v2))
          | UINT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b2 < b1
                then let v=v1+v2 in
                  if v \<ge> 0
                    then E.INT b1 (-(2^(b1-1)) + (v+2^(b1-1)) mod (2^b1))
                    else E.INT b1 (2^(b1-1) - (-v+2^(b1-1)-1) mod (2^b1) - 1)
                else PLUS (E.INT b1 v1) (UINT b2 v2)
          | _ \<Rightarrow> PLUS (E.INT b1 v1) (eupdate ex2))
        else PLUS (E.INT b1 v1) (eupdate ex2)
    | UINT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            UINT b2 v2 \<Rightarrow>
              if b2 \<in> vbits
                then UINT (max b1 b2) ((v1 + v2) mod (2^(max b1 b2)))
                else (PLUS (UINT b1 v1) (UINT b2 v2))
          | E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b1 < b2
                then let v=v1+v2 in
                  if v \<ge> 0
                    then E.INT b2 (-(2^(b2-1)) + (v+2^(b2-1)) mod (2^b2))
                    else E.INT b2 (2^(b2-1) - (-v+2^(b2-1)-1) mod (2^b2) - 1)
                else PLUS (UINT b1 v1) (E.INT b2 v2)
          | _ \<Rightarrow> PLUS (UINT b1 v1) (eupdate ex2))
        else PLUS (UINT b1 v1) (eupdate ex2)
    | _ \<Rightarrow> PLUS (eupdate ex1) (eupdate ex2))"
| "eupdate (MINUS ex1 ex2) =
    (case (eupdate ex1) of
      E.INT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits
                then let v=v1-v2 in
                  if v \<ge> 0
                    then E.INT (max b1 b2) (-(2^((max b1 b2)-1)) + (v+2^((max b1 b2)-1)) mod (2^(max b1 b2)))
                    else E.INT (max b1 b2) (2^((max b1 b2)-1) - (-v+2^((max b1 b2)-1)-1) mod (2^(max b1 b2)) - 1)
                else (MINUS (E.INT b1 v1) (E.INT b2 v2))
          | UINT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b2 < b1
                then let v=v1-v2 in
                  if v \<ge> 0
                    then E.INT b1 (-(2^(b1-1)) + (v+2^(b1-1)) mod (2^b1))
                    else E.INT b1 (2^(b1-1) - (-v+2^(b1-1)-1) mod (2^b1) - 1)
                else MINUS (E.INT b1 v1) (UINT b2 v2)
          | _ \<Rightarrow> MINUS (E.INT b1 v1) (eupdate ex2))
        else MINUS (E.INT b1 v1) (eupdate ex2)
    | UINT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            UINT b2 v2 \<Rightarrow>
              if b2 \<in> vbits
                then UINT (max b1 b2) ((v1 - v2) mod (2^(max b1 b2)))
                else (MINUS (UINT b1 v1) (UINT b2 v2))
          | E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b1 < b2
                then let v=v1-v2 in
                  if v \<ge> 0
                    then E.INT b2 (-(2^(b2-1)) + (v+2^(b2-1)) mod (2^b2))
                    else E.INT b2 (2^(b2-1) - (-v+2^(b2-1)-1) mod (2^b2) - 1)
                else MINUS (UINT b1 v1) (E.INT b2 v2)
          | _ \<Rightarrow> MINUS (UINT b1 v1) (eupdate ex2))
        else MINUS (UINT b1 v1) (eupdate ex2)
    | _ \<Rightarrow> MINUS (eupdate ex1) (eupdate ex2))"
| "eupdate (EQUAL ex1 ex2) =
    (case (eupdate ex1) of
      E.INT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits
                then if v1 = v2
                  then TRUE
                  else FALSE
                else EQUAL (E.INT b1 v1) (E.INT b2 v2)
          | UINT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b2 < b1
                then if v1 = v2
                  then TRUE
                  else FALSE
                else EQUAL (E.INT b1 v1) (UINT b2 v2)
          | _ \<Rightarrow> EQUAL (E.INT b1 v1) (eupdate ex2))
        else EQUAL (E.INT b1 v1) (eupdate ex2)
    | UINT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            UINT b2 v2 \<Rightarrow>
              if b2 \<in> vbits
                then if v1 = v2
                  then TRUE
                  else FALSE
                else EQUAL (E.INT b1 v1) (UINT b2 v2)
          | E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b1 < b2
                then if v1 = v2
                    then TRUE
                    else FALSE
                else EQUAL (UINT b1 v1) (E.INT b2 v2)
          | _ \<Rightarrow> EQUAL (UINT b1 v1) (eupdate ex2))
        else EQUAL (UINT b1 v1) (eupdate ex2)
    | _ \<Rightarrow> EQUAL (eupdate ex1) (eupdate ex2))"
| "eupdate (LESS ex1 ex2) =
    (case (eupdate ex1) of
      E.INT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits
                then if v1 < v2
                  then TRUE
                  else FALSE
                else LESS (E.INT b1 v1) (E.INT b2 v2)
          | UINT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b2 < b1
                then if v1 < v2
                  then TRUE
                  else FALSE
                else LESS (E.INT b1 v1) (UINT b2 v2)
          | _ \<Rightarrow> LESS (E.INT b1 v1) (eupdate ex2))
        else LESS (E.INT b1 v1) (eupdate ex2)
    | UINT b1 v1 \<Rightarrow>
        if b1 \<in> vbits
          then (case (eupdate ex2) of
            UINT b2 v2 \<Rightarrow>
              if b2 \<in> vbits
                then if v1 < v2
                  then TRUE
                  else FALSE
                else LESS (E.INT b1 v1) (UINT b2 v2)
          | E.INT b2 v2 \<Rightarrow>
              if b2\<in>vbits \<and> b1 < b2
                then if v1 < v2
                    then TRUE
                    else FALSE
                else LESS (UINT b1 v1) (E.INT b2 v2)
          | _ \<Rightarrow> LESS (UINT b1 v1) (eupdate ex2))
        else LESS (UINT b1 v1) (eupdate ex2)
    | _ \<Rightarrow> LESS (eupdate ex1) (eupdate ex2))"
| "eupdate (AND ex1 ex2) =
    (case (eupdate ex1) of
      TRUE \<Rightarrow> (case (eupdate ex2) of
                TRUE \<Rightarrow> TRUE
              | FALSE \<Rightarrow> FALSE
              | _ \<Rightarrow> AND TRUE (eupdate ex2))
    | FALSE \<Rightarrow> (case (eupdate ex2) of
                TRUE \<Rightarrow> FALSE
              | FALSE \<Rightarrow> FALSE
              | _ \<Rightarrow> AND FALSE (eupdate ex2))
    | _ \<Rightarrow> AND (eupdate ex1) (eupdate ex2))"
| "eupdate (OR ex1 ex2) =
    (case (eupdate ex1) of
      TRUE \<Rightarrow> (case (eupdate ex2) of
                TRUE \<Rightarrow> TRUE
              | FALSE \<Rightarrow> TRUE
              | _ \<Rightarrow> OR TRUE (eupdate ex2))
    | FALSE \<Rightarrow> (case (eupdate ex2) of
                TRUE \<Rightarrow> TRUE
              | FALSE \<Rightarrow> FALSE
              | _ \<Rightarrow> OR FALSE (eupdate ex2))
    | _ \<Rightarrow> OR (eupdate ex1) (eupdate ex2))"
| "eupdate (NOT ex1) =
    (case (eupdate ex1) of
      TRUE \<Rightarrow> FALSE
    | FALSE \<Rightarrow> TRUE
    | _ \<Rightarrow> NOT (eupdate ex1))"
| "eupdate (CALL i xs) = CALL i xs"
| "eupdate (ECALL e i xs) = ECALL e i xs"
| "eupdate CONTRACTS = CONTRACTS"

lemma "eupdate (UINT 8 250)
      =UINT 8 250"
  by(simp)
lemma "eupdate (UINT 8 500)
      = UINT 8 244"
  by(simp)
lemma "eupdate (E.INT 8 (-100))
      = E.INT 8 (- 100)"
  by(simp)
lemma "eupdate (E.INT 8 (-150))
      = E.INT 8 106"
  by(simp)
lemma "eupdate (PLUS (UINT 8 100) (UINT 8 100))
      = UINT 8 200"
  by(simp)
lemma "eupdate (PLUS (UINT 8 257) (UINT 16 100))
      = UINT 16 101"
  by(simp)
lemma "eupdate (PLUS (E.INT 8 100) (UINT 8 250)) 
      = PLUS (E.INT 8 100) (UINT 8 250)"
  by(simp)
lemma  "eupdate (PLUS (E.INT 8 250) (UINT 8 500)) 
      = PLUS (E.INT 8 (- 6)) (UINT 8 244)"
  by(simp)
lemma "eupdate (PLUS (E.INT 16 250) (UINT 8 500)) 
      = E.INT 16 494"
  by(simp)
lemma "eupdate (EQUAL (UINT 16 250) (UINT 8 250))
      = TRUE"
  by(simp)
lemma  "eupdate (EQUAL (E.INT 16 100) (UINT 8 100))
      = TRUE"
  by(simp)
lemma "eupdate (EQUAL (E.INT 8 100) (UINT 8 100)) 
      = EQUAL (E.INT 8 100) (UINT 8 100)"
  by(simp)

lemma update_bounds_int:
  assumes "eupdate ex = (E.INT b v)" and "b\<in>vbits"
  shows "(v < 2^(b-1)) \<and> v \<ge> -(2^(b-1))"
proof (cases ex)
  case (INT b' v')
  then show ?thesis
  proof cases
    assume "b'\<in>vbits"
    show ?thesis
    proof cases
      let ?x="-(2^(b'-1)) + (v'+2^(b'-1)) mod 2^b'"
      assume "v'\<ge>0"
      with `b'\<in>vbits` have "eupdate (E.INT b' v') = E.INT b' ?x" by simp
      with assms have "b=b'" and "v=?x" using INT by (simp,simp)
      moreover from `b'\<in>vbits` have "b'>0" by auto
      hence "?x < 2 ^(b'-1)" using upper_bound2[of b' "(v' + 2 ^ (b' - 1)) mod 2^b'"] by simp
      moreover have "?x \<ge> -(2^(b'-1))" by simp
      ultimately show ?thesis by simp
    next
      let ?x="2^(b'-1) - (-v'+2^(b'-1)-1) mod (2^b') - 1"
      assume "\<not>v'\<ge>0"
      with `b'\<in>vbits` have "eupdate (E.INT b' v') = E.INT b' ?x" by simp
      with assms have "b=b'" and "v=?x" using INT by (simp,simp)
      moreover have "(-v'+2^(b'-1)-1) mod (2^b')\<ge>0" by simp
      hence "?x < 2 ^(b'-1)" by arith
      moreover from `b'\<in>vbits` have "b'>0" by auto
      hence "?x \<ge> -(2^(b'-1))" using lower_bound2[of b' v'] by simp
      ultimately show ?thesis by simp
    qed
  next
    assume "\<not> b'\<in>vbits"
    with assms show ?thesis using INT by simp
  qed
next
  case (UINT b' v')
  with assms show ?thesis
  proof cases
    assume "b'\<in>vbits"
    with assms show ?thesis using UINT by simp
  next
    assume "\<not> b'\<in>vbits"
    with assms show ?thesis using UINT by simp
  qed
next
  case (ADDRESS x3)
  with assms show ?thesis by simp
next
  case (BALANCE x4)
  with assms show ?thesis by simp
next
  case THIS
  with assms show ?thesis by simp
next
  case SENDER
  with assms show ?thesis by simp
next
  case VALUE
  with assms show ?thesis by simp
next
  case TRUE
  with assms show ?thesis by simp
next
  case FALSE
  with assms show ?thesis by simp
next
  case (LVAL x7)
  with assms show ?thesis by simp
next
  case p: (PLUS e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            let ?x="-(2^((max b1 b2)-1)) + (?v+2^((max b1 b2)-1)) mod 2^(max b1 b2)"
            assume "?v\<ge>0"
            with `b1\<in>vbits` `b2\<in>vbits` i i2 have "eupdate (PLUS e1 e2) = E.INT (max b1 b2) ?x" by simp
            with assms have "b=max b1 b2" and "v=?x" using p by (simp,simp)
            moreover from `b1\<in>vbits` have "max b1 b2>0" by auto
            hence "?x < 2 ^(max b1 b2 - 1)"
              using upper_bound2[of "max b1 b2" "(?v + 2 ^ (max b1 b2 - 1)) mod 2^max b1 b2"] by simp
            moreover have "?x \<ge> -(2^(max b1 b2-1))" by simp
            ultimately show ?thesis by simp
          next
            let ?x="2^((max b1 b2)-1) - (-?v+2^((max b1 b2)-1)-1) mod (2^(max b1 b2)) - 1"
            assume "\<not>?v\<ge>0"
            with `b1\<in>vbits` `b2\<in>vbits` i i2 have "eupdate (PLUS e1 e2) = E.INT (max b1 b2) ?x" by simp
            with assms have "b=max b1 b2" and "v=?x" using p by (simp,simp)
            moreover have "(-?v+2^(max b1 b2-1)-1) mod (2^max b1 b2)\<ge>0" by simp
            hence "?x < 2 ^(max b1 b2-1)" by arith
            moreover from `b1\<in>vbits` have "max b1 b2>0" by auto
            hence "?x \<ge> -(2^(max b1 b2-1))" using lower_bound2[of "max b1 b2" ?v] by simp
            ultimately show ?thesis by simp
          qed
        next
          assume "b2\<notin>vbits"
          with p i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            then show ?thesis
            proof cases
              let ?x="(-(2^(b1-1)) + (?v+2^(b1-1)) mod (2^b1))"
              assume "?v\<ge>0"
              with `b1\<in>vbits` `b2\<in>vbits` `b2<b1` i u have "eupdate (PLUS e1 e2) = E.INT b1 ?x" by simp
              with assms have "b=b1" and "v=?x" using p by (simp,simp)
              moreover from `b1\<in>vbits` have "b1>0" by auto
              hence "?x < 2 ^(b1 - 1)" using upper_bound2[of b1] by simp
              moreover have "?x \<ge> -(2^(b1-1))" by simp
              ultimately show ?thesis by simp
            next
              let ?x="2^(b1-1) - (-?v+2^(b1-1)-1) mod (2^b1) - 1"
              assume "\<not>?v\<ge>0"
              with `b1\<in>vbits` `b2\<in>vbits` `b2<b1` i u have "eupdate (PLUS e1 e2) = E.INT b1 ?x" by simp
              with assms have "b=b1" and "v=?x" using p i u by (simp,simp)
              moreover have "(-?v+2^(b1-1)-1) mod 2^b1\<ge>0" by simp
              hence "?x < 2 ^(b1-1)" by arith
              moreover from `b1\<in>vbits` have "b1>0" by auto
              hence "?x \<ge> -(2^(b1-1))" using lower_bound2[of b1 ?v] by simp
              ultimately show ?thesis by simp
            qed
          next
            assume "\<not> b2<b1"
            with p i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with p i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with p i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            then show ?thesis
            proof cases
              let ?x="(-(2^(b2-1)) + (?v+2^(b2-1)) mod (2^b2))"
              assume "?v\<ge>0"
              with `b1\<in>vbits` `b2\<in>vbits` `b1<b2` i u have "eupdate (PLUS e1 e2) = E.INT b2 ?x" by simp
              with assms have "b=b2" and "v=?x" using p by (simp,simp)
              moreover from `b2\<in>vbits` have "b2>0" by auto
              hence "?x < 2 ^(b2 - 1)" using upper_bound2[of b2] by simp
              moreover have "?x \<ge> -(2^(b2-1))" by simp
              ultimately show ?thesis by simp
            next
              let ?x="2^(b2-1) - (-?v+2^(b2-1)-1) mod (2^b2) - 1"
              assume "\<not>?v\<ge>0"
              with `b1\<in>vbits` `b2\<in>vbits` `b1<b2` i u have "eupdate (PLUS e1 e2) = E.INT b2 ?x" by simp
              with assms have "b=b2" and "v=?x" using p i u by (simp,simp)
              moreover have "(-?v+2^(b2-1)-1) mod 2^b2\<ge>0" by simp
              hence "?x < 2 ^(b2-1)" by arith
              moreover from `b2\<in>vbits` have "b2>0" by auto
              hence "?x \<ge> -(2^(b2-1))" using lower_bound2[of b2 ?v] by simp
              ultimately show ?thesis by simp
            qed
          next
            assume "\<not> b1<b2"
            with p i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with p i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          with `b1\<in>vbits` u u2 p show ?thesis using assms by simp
        next
          assume "\<not>b2\<in>vbits"
          with p u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with p u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with p show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with p show ?thesis using assms by simp
  next
    case THIS
    with p show ?thesis using assms by simp
  next
    case SENDER
    with p show ?thesis using assms by simp
  next
    case VALUE
    with p show ?thesis using assms by simp
  next
    case TRUE
    with p show ?thesis using assms by simp
  next
    case FALSE
    with p show ?thesis using assms by simp
  next
    case (LVAL x7)
    with p show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with p show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with p show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with p show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with p show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with p show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with p show ?thesis using assms by simp
  next
    case (NOT x131)
    with p show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with p show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with p show ?thesis using assms by simp
  next
    case CONTRACTS
    with p show ?thesis using assms by simp
  qed
next
  case m: (MINUS e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with m show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1-v2"
          assume "b2\<in>vbits"
          with `b1 \<in> vbits` have
            u_def: "eupdate (MINUS e1 e2) =
            (let v = v1 - v2
              in if 0 \<le> v
                then E.INT (max b1 b2)
                  (- (2 ^ (max b1 b2 - 1)) + (v + 2 ^ (max b1 b2 - 1)) mod 2 ^ max b1 b2)
                else E.INT (max b1 b2)
                  (2 ^ (max b1 b2 - 1) - (- v + 2 ^ (max b1 b2 - 1) - 1) mod 2 ^ max b1 b2 - 1))"
            using i i2 eupdate.simps(11)[of e1 e2] by simp
          show ?thesis
          proof cases
            let ?x="-(2^((max b1 b2)-1)) + (?v+2^((max b1 b2)-1)) mod 2^(max b1 b2)"
            assume "?v\<ge>0"
            with u_def have "eupdate (MINUS e1 e2) = E.INT (max b1 b2) ?x" by simp
            with assms have "b=max b1 b2" and "v=?x" using m by (simp,simp)
            moreover from `b1\<in>vbits` have "max b1 b2>0" by auto
            hence "?x < 2 ^(max b1 b2 - 1)"
              using upper_bound2[of "max b1 b2" "(?v + 2 ^ (max b1 b2 - 1)) mod 2^max b1 b2"] by simp
            moreover have "?x \<ge> -(2^(max b1 b2-1))" by simp
            ultimately show ?thesis by simp
          next
            let ?x="2^((max b1 b2)-1) - (-?v+2^((max b1 b2)-1)-1) mod (2^(max b1 b2)) - 1"
            assume "\<not>?v\<ge>0"
            with u_def have "eupdate (MINUS e1 e2) = E.INT (max b1 b2) ?x" using u_def by simp
            with assms have "b=max b1 b2" and "v=?x" using m by (simp,simp)
            moreover have "(-?v+2^(max b1 b2-1)-1) mod (2^max b1 b2)\<ge>0" by simp
            hence "?x < 2 ^(max b1 b2-1)" by arith
            moreover from `b1\<in>vbits` have "max b1 b2>0" by auto
            hence "?x \<ge> -(2^(max b1 b2-1))" using lower_bound2[of "max b1 b2" ?v] by simp
            ultimately show ?thesis by simp
          qed
        next
          assume "b2\<notin>vbits"
          with m i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1-v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            with `b1 \<in> vbits` `b2 \<in> vbits` have
              u_def: "eupdate (MINUS e1 e2) =
              (let v = v1 - v2
                in if 0 \<le> v
                  then E.INT b1 (- (2 ^ (b1 - 1)) + (v + 2 ^ (b1 - 1)) mod 2 ^ b1)
                  else E.INT b1 (2 ^ (b1 - 1) - (- v + 2 ^ (b1 - 1) - 1) mod 2 ^ b1 - 1))"
              using i u eupdate.simps(11)[of e1 e2] by simp
            then show ?thesis
            proof cases
              let ?x="(-(2^(b1-1)) + (?v+2^(b1-1)) mod (2^b1))"
              assume "?v\<ge>0"
              with u_def have "eupdate (MINUS e1 e2) = E.INT b1 ?x" by simp
              with assms have "b=b1" and "v=?x" using m by (simp,simp)
              moreover from `b1\<in>vbits` have "b1>0" by auto
              hence "?x < 2 ^(b1 - 1)" using upper_bound2[of b1] by simp
              moreover have "?x \<ge> -(2^(b1-1))" by simp
              ultimately show ?thesis by simp
            next
              let ?x="2^(b1-1) - (-?v+2^(b1-1)-1) mod (2^b1) - 1"
              assume "\<not>?v\<ge>0"
              with u_def have "eupdate (MINUS e1 e2) = E.INT b1 ?x" by simp
              with assms have "b=b1" and "v=?x" using m i u by (simp,simp)
              moreover have "(-?v+2^(b1-1)-1) mod 2^b1\<ge>0" by simp
              hence "?x < 2 ^(b1-1)" by arith
              moreover from `b1\<in>vbits` have "b1>0" by auto
              hence "?x \<ge> -(2^(b1-1))" using lower_bound2[of b1 ?v] by simp
              ultimately show ?thesis by simp
            qed
          next
            assume "\<not> b2<b1"
            with m i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with m i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with m i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1-v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            with `b1 \<in> vbits` `b2 \<in> vbits` have
              u_def: "eupdate (MINUS e1 e2) =
              (let v = v1 - v2
                in if 0 \<le> v
                  then E.INT b2 (- (2 ^ (b2 - 1)) + (v + 2 ^ (b2 - 1)) mod 2 ^ b2)
                  else E.INT b2 (2 ^ (b2 - 1) - (- v + 2 ^ (b2 - 1) - 1) mod 2 ^ b2 - 1))"
              using i u eupdate.simps(11)[of e1 e2] by simp
            then show ?thesis
            proof cases
              let ?x="(-(2^(b2-1)) + (?v+2^(b2-1)) mod (2^b2))"
              assume "?v\<ge>0"
              with u_def have "eupdate (MINUS e1 e2) = E.INT b2 ?x" by simp
              with assms have "b=b2" and "v=?x" using m by (simp,simp)
              moreover from `b2\<in>vbits` have "b2>0" by auto
              hence "?x < 2 ^(b2 - 1)" using upper_bound2[of b2] by simp
              moreover have "?x \<ge> -(2^(b2-1))" by simp
              ultimately show ?thesis by simp
            next
              let ?x="2^(b2-1) - (-?v+2^(b2-1)-1) mod (2^b2) - 1"
              assume "\<not>?v\<ge>0"
              with u_def have "eupdate (MINUS e1 e2) = E.INT b2 ?x" by simp
              with assms have "b=b2" and "v=?x" using m i u by (simp,simp)
              moreover have "(-?v+2^(b2-1)-1) mod 2^b2\<ge>0" by simp
              hence "?x < 2 ^(b2-1)" by arith
              moreover from `b2\<in>vbits` have "b2>0" by auto
              hence "?x \<ge> -(2^(b2-1))" using lower_bound2[of b2 ?v] by simp
              ultimately show ?thesis by simp
            qed
          next
            assume "\<not> b1<b2"
            with m i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with m i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          with `b1\<in>vbits` u u2 m show ?thesis using assms by simp
        next
          assume "\<not>b2\<in>vbits"
          with m u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with m u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with m show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with m show ?thesis using assms by simp
  next
    case THIS
    with m show ?thesis using assms by simp
  next
    case SENDER
    with m show ?thesis using assms by simp
  next
    case VALUE
    with m show ?thesis using assms by simp
  next
    case TRUE
    with m show ?thesis using assms by simp
  next
    case FALSE
    with m show ?thesis using assms by simp
  next
    case (LVAL x7)
    with m show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with m show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with m show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with m show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with m show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with m show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with m show ?thesis using assms by simp
  next
    case (NOT x131)
    with m show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with m show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with m show ?thesis using assms by simp
  next
    case CONTRACTS
    with m show ?thesis using assms by simp
  qed
next
  case e: (EQUAL e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1=v2"
            with assms show ?thesis using e i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1=v2"
            with assms show ?thesis using e i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "b2\<notin>vbits"
          with e i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            then show ?thesis
            proof cases
              assume "v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            next
              assume "\<not> v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            qed
          next
            assume "\<not> b2<b1"
            with e i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with e i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with e i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            then show ?thesis
            proof cases
              assume "v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            next
              assume "\<not> v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            qed
          next
            assume "\<not> b1<b2"
            with e i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with e i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1=v2"
            with assms show ?thesis using e u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1=v2"
            with assms show ?thesis using e u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "\<not>b2\<in>vbits"
          with e u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with e u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with e show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with e show ?thesis using assms by simp
  next
    case THIS
    with e show ?thesis using assms by simp
  next
    case SENDER
    with e show ?thesis using assms by simp
  next
    case VALUE
    with e show ?thesis using assms by simp
  next
    case TRUE
    with e show ?thesis using assms by simp
  next
    case FALSE
    with e show ?thesis using assms by simp
  next
    case (LVAL x7)
    with e show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with e show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with e show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with e show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with e show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with e show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with e show ?thesis using assms by simp
  next
    case (NOT x131)
    with e show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with e show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with e show ?thesis using assms by simp
  next
    case CONTRACTS
    with e show ?thesis using assms by simp
  qed
next
  case l: (LESS e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1<v2"
            with assms show ?thesis using l i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1<v2"
            with assms show ?thesis using l i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "b2\<notin>vbits"
          with l i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            then show ?thesis
            proof cases
              assume "v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            next
              assume "\<not> v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            qed
          next
            assume "\<not> b2<b1"
            with l i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with l i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with l i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            then show ?thesis
            proof cases
              assume "v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            next
              assume "\<not> v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            qed
          next
            assume "\<not> b1<b2"
            with l i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with l i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1<v2"
            with assms show ?thesis using l u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1<v2"
            with assms show ?thesis using l u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "\<not>b2\<in>vbits"
          with l u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with l u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with l show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with l show ?thesis using assms by simp
  next
    case THIS
    with l show ?thesis using assms by simp
  next
    case SENDER
    with l show ?thesis using assms by simp
  next
    case VALUE
    with l show ?thesis using assms by simp
  next
    case TRUE
    with l show ?thesis using assms by simp
  next
    case FALSE
    with l show ?thesis using assms by simp
  next
    case (LVAL x7)
    with l show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with l show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with l show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with l show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with l show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with l show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with l show ?thesis using assms by simp
  next
    case (NOT x131)
    with l show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with l show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with l show ?thesis using assms by simp
  next
    case CONTRACTS
    with l show ?thesis using assms by simp
  qed
next
  case a: (AND e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with a show ?thesis using assms by simp
  next
    case (UINT x21 x22)
    with a show ?thesis using assms by simp
  next
    case (ADDRESS x3)
    with a show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with a show ?thesis using assms by simp
  next
    case THIS
    with a show ?thesis using assms by simp
  next
    case SENDER
    with a show ?thesis using assms by simp
  next
    case VALUE
    with a show ?thesis using assms by simp
  next
    case t: TRUE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with a t show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with a t show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with a t show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with a t show ?thesis using assms by simp
    next
      case THIS
      with a t show ?thesis using assms by simp
    next
      case SENDER
      with a t show ?thesis using assms by simp
    next
      case VALUE
      with a t show ?thesis using assms by simp
    next
      case TRUE
      with a t show ?thesis using assms by simp
    next
      case FALSE
      with a t show ?thesis using assms by simp
    next
      case (LVAL x7)
      with a t show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with a t show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with a t show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with a t show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with a t show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with a t show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with a t show ?thesis using assms by simp
    next
      case (NOT x131)
      with a t show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with a t show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with a t show ?thesis using assms by simp
    next
      case CONTRACTS
      with a t show ?thesis using assms by simp
    qed
  next
    case f: FALSE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with a f show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with a f show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with a f show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with a f show ?thesis using assms by simp
    next
      case THIS
      with a f show ?thesis using assms by simp
    next
      case SENDER
      with a f show ?thesis using assms by simp
    next
      case VALUE
      with a f show ?thesis using assms by simp
    next
      case TRUE
      with a f show ?thesis using assms by simp
    next
      case FALSE
      with a f show ?thesis using assms by simp
    next
      case (LVAL x7)
      with a f show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with a f show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with a f show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with a f show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with a f show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with a f show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with a f show ?thesis using assms by simp
    next
      case (NOT x131)
      with a f show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with a f show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with a f show ?thesis using assms by simp
    next
      case CONTRACTS
      with a f show ?thesis using assms by simp
    qed
  next
    case (LVAL x7)
    with a show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with a show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with a show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with a show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with a show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with a show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with a show ?thesis using assms by simp
  next
    case (NOT x131)
    with a show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with a show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with a show ?thesis using assms by simp
  next
    case CONTRACTS
    with a show ?thesis using assms by simp
  qed
next
  case o: (OR e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with o show ?thesis using assms by simp
  next
    case (UINT x21 x22)
    with o show ?thesis using assms by simp
  next
    case (ADDRESS x3)
    with o show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with o show ?thesis using assms by simp
  next
    case THIS
    with o show ?thesis using assms by simp
  next
    case SENDER
    with o show ?thesis using assms by simp
  next
    case VALUE
    with o show ?thesis using assms by simp
  next
    case t: TRUE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with o t show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with o t show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with o t show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with o t show ?thesis using assms by simp
    next
      case THIS
      with o t show ?thesis using assms by simp
    next
      case SENDER
      with o t show ?thesis using assms by simp
    next
      case VALUE
      with o t show ?thesis using assms by simp
    next
      case TRUE
      with o t show ?thesis using assms by simp
    next
      case FALSE
      with o t show ?thesis using assms by simp
    next
      case (LVAL x7)
      with o t show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with o t show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with o t show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with o t show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with o t show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with o t show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with o t show ?thesis using assms by simp
    next
      case (NOT x131)
      with o t show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with o t show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with o t show ?thesis using assms by simp
    next
      case CONTRACTS
      with o t show ?thesis using assms by simp
    qed
  next
    case f: FALSE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with o f show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with o f show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with o f show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with o f show ?thesis using assms by simp
    next
      case THIS
      with o f show ?thesis using assms by simp
    next
      case SENDER
      with o f show ?thesis using assms by simp
    next
      case VALUE
      with o f show ?thesis using assms by simp
    next
      case TRUE
      with o f show ?thesis using assms by simp
    next
      case FALSE
      with o f show ?thesis using assms by simp
    next
      case (LVAL x7)
      with o f show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with o f show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with o f show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with o f show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with o f show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with o f show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with o f show ?thesis using assms by simp
    next
      case (NOT x131)
      with o f show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with o f show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with o f show ?thesis using assms by simp
    next
      case CONTRACTS
      with o f show ?thesis using assms by simp
    qed
  next
    case (LVAL x7)
    with o show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with o show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with o show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with o show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with o show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with o show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with o show ?thesis using assms by simp
  next
    case (NOT x131)
    with o show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with o show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with o show ?thesis using assms by simp
  next
    case CONTRACTS
    with o show ?thesis using assms by simp
  qed
next
  case o: (NOT e1)
  show ?thesis
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with o show ?thesis using assms by simp
  next
    case (UINT x21 x22)
    with o show ?thesis using assms by simp
  next
    case (ADDRESS x3)
    with o show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with o show ?thesis using assms by simp
  next
    case THIS
    with o show ?thesis using assms by simp
  next
    case SENDER
    with o show ?thesis using assms by simp
  next
    case VALUE
    with o show ?thesis using assms by simp
  next
    case t: TRUE
    with o show ?thesis using assms by simp
  next
    case f: FALSE
    with o show ?thesis using assms by simp
  next
    case (LVAL x7)
    with o show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with o show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with o show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with o show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with o show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with o show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with o show ?thesis using assms by simp
  next
    case (NOT x131)
    with o show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with o show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with o show ?thesis using assms by simp
  next
    case CONTRACTS
    with o show ?thesis using assms by simp
  qed
next
  case (CALL x181 x182)
  with assms show ?thesis by simp
next
  case (ECALL x191 x192 x193)
  with assms show ?thesis by simp
next
  case CONTRACTS
  with assms show ?thesis by simp
qed

lemma update_bounds_uint:
  assumes "eupdate ex = UINT b v" and "b\<in>vbits"
  shows "v < 2^b \<and> v \<ge> 0"
proof (cases ex)
  case (INT b' v')
  with assms show ?thesis
  proof cases
    assume "b'\<in>vbits"
    show ?thesis
    proof cases
      assume "v'\<ge>0"
      with INT show ?thesis using assms `b'\<in>vbits` by simp
    next
      assume "\<not> v'\<ge>0"
      with INT show ?thesis using assms `b'\<in>vbits` by simp
    qed
  next
    assume "\<not> b'\<in>vbits"
    with INT show ?thesis using assms by simp
  qed
next
  case (UINT b' v')
  then show ?thesis
  proof cases
    assume "b'\<in>vbits"
    with UINT show ?thesis using assms by auto
  next
    assume "\<not> b'\<in>vbits"
    with UINT show ?thesis using assms by auto
  qed
next
  case (ADDRESS x3)
  with assms show ?thesis by simp
next
  case (BALANCE x4)
  with assms show ?thesis by simp
next
  case THIS
  with assms show ?thesis by simp
next
  case SENDER
  with assms show ?thesis by simp
next
  case VALUE
  with assms show ?thesis by simp
next
  case TRUE
  with assms show ?thesis by simp
next
  case FALSE
  with assms show ?thesis by simp
next
  case (LVAL x7)
  with assms show ?thesis by simp
next
  case p: (PLUS e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with p show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "?v\<ge>0"
            with assms show ?thesis using p i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not>?v\<ge>0"
            with assms show ?thesis using p i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "b2\<notin>vbits"
          with p i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            then show ?thesis
            proof cases
              assume "?v\<ge>0"
              with assms show ?thesis using p i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            next
              assume "\<not>?v\<ge>0"
              with assms show ?thesis using p i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            qed
          next
            assume "\<not> b2<b1"
            with p i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with p i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with p i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with p i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    with p show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            then show ?thesis
            proof cases
              assume "?v\<ge>0"
              with assms show ?thesis using p i u `b1\<in>vbits`  `b2\<in>vbits` `b1<b2` by simp
            next
              assume "\<not>?v\<ge>0"
              with assms show ?thesis using p i u `b1\<in>vbits`  `b2\<in>vbits` `b1<b2` by simp
            qed
          next
            assume "\<not> b1<b2"
            with p i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with p i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          let ?x="((v1 + v2) mod (2^(max b1 b2)))"
          assume "b2\<in>vbits"
          with `b1\<in>vbits` u u2 have "eupdate (PLUS e1 e2) = UINT (max b1 b2) ?x" by simp
          with assms have "b=max b1 b2" and "v=?x" using p by (simp,simp)
          moreover from `b1\<in>vbits` have "max b1 b2>0" by auto
          hence "?x < 2 ^(max b1 b2)" by simp
          moreover have "?x \<ge> 0" by simp
          ultimately show ?thesis by simp
        next
          assume "\<not>b2\<in>vbits"
          with p u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with p u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with p u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with p show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with p show ?thesis using assms by simp
  next
    case THIS
    with p show ?thesis using assms by simp
  next
    case SENDER
    with p show ?thesis using assms by simp
  next
    case VALUE
    with p show ?thesis using assms by simp
  next
    case TRUE
    with p show ?thesis using assms by simp
  next
    case FALSE
    with p show ?thesis using assms by simp
  next
    case (LVAL x7)
    with p show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with p show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with p show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with p show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with p show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with p show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with p show ?thesis using assms by simp
  next
    case (NOT x131)
    with p show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with p show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with p show ?thesis using assms by simp
  next
    case CONTRACTS
    with p show ?thesis using assms by simp
  qed
next
  case m: (MINUS e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with m show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1-v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "?v\<ge>0"
            with assms show ?thesis using m i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not>?v\<ge>0"
            with assms show ?thesis using m i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "b2\<notin>vbits"
          with m i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1-v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            show ?thesis
            proof cases
              assume "?v\<ge>0"
              with assms show ?thesis using m i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            next
              assume "\<not>?v\<ge>0"
              with assms show ?thesis using m i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            qed
          next
            assume "\<not> b2<b1"
            with m i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with m i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with m i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with m i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    with m show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1-v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            show ?thesis
            proof cases
              assume "?v\<ge>0"
              with assms show ?thesis using m i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            next
              assume "\<not>?v\<ge>0"
              with assms show ?thesis using m i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            qed
          next
            assume "\<not> b1<b2"
            with m i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with m i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          let ?x="((v1 - v2) mod (2^(max b1 b2)))"
          assume "b2\<in>vbits"
          with `b1\<in>vbits` u u2 have "eupdate (MINUS e1 e2) = UINT (max b1 b2) ?x" by simp
          with assms have "b=max b1 b2" and "v=?x" using m by (simp,simp)
          moreover from `b1\<in>vbits` have "max b1 b2>0" by auto
          hence "?x < 2 ^(max b1 b2)" by simp
          moreover have "?x \<ge> 0" by simp
          ultimately show ?thesis by simp
        next
          assume "\<not>b2\<in>vbits"
          with m u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with m u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with m u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with m show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with m show ?thesis using assms by simp
  next
    case THIS
    with m show ?thesis using assms by simp
  next
    case SENDER
    with m show ?thesis using assms by simp
  next
    case VALUE
    with m show ?thesis using assms by simp
  next
    case TRUE
    with m show ?thesis using assms by simp
  next
    case FALSE
    with m show ?thesis using assms by simp
  next
    case (LVAL x7)
    with m show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with m show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with m show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with m show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with m show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with m show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with m show ?thesis using assms by simp
  next
    case (NOT x131)
    with m show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with m show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with m show ?thesis using assms by simp
  next
    case CONTRACTS
    with m show ?thesis using assms by simp
  qed
next
  case e: (EQUAL e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1=v2"
            with assms show ?thesis using e i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1=v2"
            with assms show ?thesis using e i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "b2\<notin>vbits"
          with e i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            then show ?thesis
            proof cases
              assume "v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            next
              assume "\<not> v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            qed
          next
            assume "\<not> b2<b1"
            with e i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with e i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with e i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with e i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            then show ?thesis
            proof cases
              assume "v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            next
              assume "\<not> v1=v2"
              with assms show ?thesis using e i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            qed
          next
            assume "\<not> b1<b2"
            with e i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with e i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1=v2"
            with assms show ?thesis using e u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1=v2"
            with assms show ?thesis using e u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "\<not>b2\<in>vbits"
          with e u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with e u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with e u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with e show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with e show ?thesis using assms by simp
  next
    case THIS
    with e show ?thesis using assms by simp
  next
    case SENDER
    with e show ?thesis using assms by simp
  next
    case VALUE
    with e show ?thesis using assms by simp
  next
    case TRUE
    with e show ?thesis using assms by simp
  next
    case FALSE
    with e show ?thesis using assms by simp
  next
    case (LVAL x7)
    with e show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with e show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with e show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with e show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with e show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with e show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with e show ?thesis using assms by simp
  next
    case (NOT x131)
    with e show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with e show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with e show ?thesis using assms by simp
  next
    case CONTRACTS
    with e show ?thesis using assms by simp
  qed
next
  case l: (LESS e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i2: (INT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1<v2"
            with assms show ?thesis using l i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1<v2"
            with assms show ?thesis using l i i2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "b2\<notin>vbits"
          with l i i2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b2<b1"
            then show ?thesis
            proof cases
              assume "v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            next
              assume "\<not> v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b2<b1` by simp
            qed
          next
            assume "\<not> b2<b1"
            with l i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with l i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with l i `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with l i show ?thesis using assms by simp
    qed
  next
    case u: (UINT b1 v1)
    show ?thesis
    proof cases
      assume "b1\<in>vbits"
      show ?thesis
      proof (cases "eupdate e2")
        case i: (INT b2 v2)
        then show ?thesis
        proof cases
          let ?v="v1+v2"
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "b1<b2"
            then show ?thesis
            proof cases
              assume "v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            next
              assume "\<not> v1<v2"
              with assms show ?thesis using l i u `b1\<in>vbits` `b2\<in>vbits` `b1<b2` by simp
            qed
          next
            assume "\<not> b1<b2"
            with l i u `b1\<in>vbits` show ?thesis using assms by simp
          qed
        next
          assume "b2\<notin>vbits"
          with l i u `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case u2: (UINT b2 v2)
        then show ?thesis
        proof cases
          assume "b2\<in>vbits"
          show ?thesis
          proof cases
            assume "v1<v2"
            with assms show ?thesis using l u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          next
            assume "\<not> v1<v2"
            with assms show ?thesis using l u u2 `b1\<in>vbits` `b2\<in>vbits` by simp
          qed
        next
          assume "\<not>b2\<in>vbits"
          with l u u2 `b1\<in>vbits` show ?thesis using assms by simp
        qed
      next
        case (ADDRESS x3)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (BALANCE x4)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case THIS
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case SENDER
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case VALUE
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case TRUE
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case FALSE
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LVAL x7)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (PLUS x81 x82)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (MINUS x91 x92)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (EQUAL x101 x102)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (LESS x111 x112)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (AND x121 x122)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (OR x131 x132)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (NOT x131)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (CALL x181 x182)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case (ECALL x191 x192 x193)
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      next
        case CONTRACTS
        with l u `b1\<in>vbits` show ?thesis using assms by simp
      qed
    next
      assume "\<not> b1\<in>vbits"
      with l u show ?thesis using assms by simp
    qed
  next
    case (ADDRESS x3)
    with l show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with l show ?thesis using assms by simp
  next
    case THIS
    with l show ?thesis using assms by simp
  next
    case SENDER
    with l show ?thesis using assms by simp
  next
    case VALUE
    with l show ?thesis using assms by simp
  next
    case TRUE
    with l show ?thesis using assms by simp
  next
    case FALSE
    with l show ?thesis using assms by simp
  next
    case (LVAL x7)
    with l show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with l show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with l show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with l show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with l show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with l show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with l show ?thesis using assms by simp
  next
    case (NOT x131)
    with l show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with l show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with l show ?thesis using assms by simp
  next
    case CONTRACTS
    with l show ?thesis using assms by simp
  qed
next
  case a: (AND e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with a show ?thesis using assms by simp
  next
    case (UINT x21 x22)
    with a show ?thesis using assms by simp
  next
    case (ADDRESS x3)
    with a show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with a show ?thesis using assms by simp
  next
    case THIS
    with a show ?thesis using assms by simp
  next
    case SENDER
    with a show ?thesis using assms by simp
  next
    case VALUE
    with a show ?thesis using assms by simp
  next
    case t: TRUE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with a t show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with a t show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with a t show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with a t show ?thesis using assms by simp
    next
      case THIS
      with a t show ?thesis using assms by simp
    next
      case SENDER
      with a t show ?thesis using assms by simp
    next
      case VALUE
      with a t show ?thesis using assms by simp
    next
      case TRUE
      with a t show ?thesis using assms by simp
    next
      case FALSE
      with a t show ?thesis using assms by simp
    next
      case (LVAL x7)
      with a t show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with a t show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with a t show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with a t show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with a t show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with a t show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with a t show ?thesis using assms by simp
    next
      case (NOT x131)
      with a t show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with a t show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with a t show ?thesis using assms by simp
    next
      case CONTRACTS
      with a t show ?thesis using assms by simp
    qed
  next
    case f: FALSE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with a f show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with a f show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with a f show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with a f show ?thesis using assms by simp
    next
      case THIS
      with a f show ?thesis using assms by simp
    next
      case SENDER
      with a f show ?thesis using assms by simp
    next
      case VALUE
      with a f show ?thesis using assms by simp
    next
      case TRUE
      with a f show ?thesis using assms by simp
    next
      case FALSE
      with a f show ?thesis using assms by simp
    next
      case (LVAL x7)
      with a f show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with a f show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with a f show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with a f show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with a f show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with a f show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with a f show ?thesis using assms by simp
    next
      case (NOT x131)
      with a f show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with a f show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with a f show ?thesis using assms by simp
    next
      case CONTRACTS
      with a f show ?thesis using assms by simp
    qed
  next
    case (LVAL x7)
    with a show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with a show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with a show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with a show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with a show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with a show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with a show ?thesis using assms by simp
  next
    case (NOT x131)
    with a show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with a show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with a show ?thesis using assms by simp
  next
    case CONTRACTS
    with a show ?thesis using assms by simp
  qed
next
  case o: (OR e1 e2)
  show ?thesis
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with o show ?thesis using assms by simp
  next
    case (UINT x21 x22)
    with o show ?thesis using assms by simp
  next
    case (ADDRESS x3)
    with o show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with o show ?thesis using assms by simp
  next
    case THIS
    with o show ?thesis using assms by simp
  next
    case SENDER
    with o show ?thesis using assms by simp
  next
    case VALUE
    with o show ?thesis using assms by simp
  next
    case t: TRUE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with o t show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with o t show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with o t show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with o t show ?thesis using assms by simp
    next
      case THIS
      with o t show ?thesis using assms by simp
    next
      case SENDER
      with o t show ?thesis using assms by simp
    next
      case VALUE
      with o t show ?thesis using assms by simp
    next
      case TRUE
      with o t show ?thesis using assms by simp
    next
      case FALSE
      with o t show ?thesis using assms by simp
    next
      case (LVAL x7)
      with o t show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with o t show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with o t show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with o t show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with o t show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with o t show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with o t show ?thesis using assms by simp
    next
      case (NOT x131)
      with o t show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with o t show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with o t show ?thesis using assms by simp
    next
      case CONTRACTS
      with o t show ?thesis using assms by simp
    qed
  next
    case f: FALSE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with o f show ?thesis using assms by simp
    next
      case (UINT x21 x22)
      with o f show ?thesis using assms by simp
    next
      case (ADDRESS x3)
      with o f show ?thesis using assms by simp
    next
      case (BALANCE x4)
      with o f show ?thesis using assms by simp
    next
      case THIS
      with o f show ?thesis using assms by simp
    next
      case SENDER
      with o f show ?thesis using assms by simp
    next
      case VALUE
      with o f show ?thesis using assms by simp
    next
      case TRUE
      with o f show ?thesis using assms by simp
    next
      case FALSE
      with o f show ?thesis using assms by simp
    next
      case (LVAL x7)
      with o f show ?thesis using assms by simp
    next
      case (PLUS x81 x82)
      with o f show ?thesis using assms by simp
    next
      case (MINUS x91 x92)
      with o f show ?thesis using assms by simp
    next
      case (EQUAL x101 x102)
      with o f show ?thesis using assms by simp
    next
      case (LESS x111 x112)
      with o f show ?thesis using assms by simp
    next
      case (AND x121 x122)
      with o f show ?thesis using assms by simp
    next
      case (OR x131 x132)
      with o f show ?thesis using assms by simp
    next
      case (NOT x131)
      with o f show ?thesis using assms by simp
    next
      case (CALL x181 x182)
      with o f show ?thesis using assms by simp
    next
      case (ECALL x191 x192 x193)
      with o f show ?thesis using assms by simp
    next
      case CONTRACTS
      with o f show ?thesis using assms by simp
    qed
  next
    case (LVAL x7)
    with o show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with o show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with o show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with o show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with o show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with o show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with o show ?thesis using assms by simp
  next
    case (NOT x131)
    with o show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with o show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with o show ?thesis using assms by simp
  next
    case CONTRACTS
    with o show ?thesis using assms by simp
  qed
next
  case o: (NOT x)
  show ?thesis
  proof (cases "eupdate x")
    case (INT x11 x12)
    with o show ?thesis using assms by simp
  next
    case (UINT x21 x22)
    with o show ?thesis using assms by simp
  next
    case (ADDRESS x3)
    with o show ?thesis using assms by simp
  next
    case (BALANCE x4)
    with o show ?thesis using assms by simp
  next
    case THIS
    with o show ?thesis using assms by simp
  next
    case SENDER
    with o show ?thesis using assms by simp
  next
    case VALUE
    with o show ?thesis using assms by simp
  next
    case t: TRUE
    with o show ?thesis using assms by simp
  next
    case f: FALSE
    with o show ?thesis using assms by simp
  next
    case (LVAL x7)
    with o show ?thesis using assms by simp
  next
    case (PLUS x81 x82)
    with o show ?thesis using assms by simp
  next
    case (MINUS x91 x92)
    with o show ?thesis using assms by simp
  next
    case (EQUAL x101 x102)
    with o show ?thesis using assms by simp
  next
    case (LESS x111 x112)
    with o show ?thesis using assms by simp
  next
    case (AND x121 x122)
    with o show ?thesis using assms by simp
  next
    case (OR x131 x132)
    with o show ?thesis using assms by simp
  next
    case (NOT x131)
    with o show ?thesis using assms by simp
  next
    case (CALL x181 x182)
    with o show ?thesis using assms by simp
  next
    case (ECALL x191 x192 x193)
    with o show ?thesis using assms by simp
  next
    case CONTRACTS
    with o show ?thesis using assms by simp
  qed
next
  case (CALL x181 x182)
  with assms show ?thesis by simp
next
  case (ECALL x191 x192 x193)
  with assms show ?thesis by simp
next
  case CONTRACTS
  with assms show ?thesis by simp
qed

lemma no_gas:
  assumes "\<not> g > costs_ex ex env cd st"
  shows "expr ex env cd st g = Exception Gas"
proof (cases ex)
  case (INT x11 x12)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (UINT x21 x22)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (ADDRESS x3)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (BALANCE x4)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case THIS
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case SENDER
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case VALUE
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case TRUE
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case FALSE
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (LVAL x10)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (PLUS x111 x112)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (MINUS x121 x122)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (EQUAL x131 x132)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (LESS x141 x142)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (AND x151 x152)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (OR x161 x162)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (NOT x17)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (CALL x181 x182)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case (ECALL x191 x192 x193)
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
next
  case CONTRACTS
  with assms show ?thesis by (simp add: Statements.solidity.expr.simps)
qed

lemma lift_eq:
  assumes "expr e1 env cd st g = expr e1' env cd st g"
      and "\<And>g' rv. expr e1 env cd st g = Normal (rv, g') \<Longrightarrow> expr e2 env cd st g'= expr e2' env cd st g'"
    shows "lift expr f e1 e2 env cd st g =lift expr f e1' e2' env cd st g"
proof (cases "expr e1 env cd st g")
  case s1: (n a g')
  then show ?thesis
  proof (cases a)
    case f1:(Pair a b)
    then show ?thesis
    proof (cases a)
      case k1:(KValue x1)
      then show ?thesis
      proof (cases b)
        case v1: (Value x1)
        then show ?thesis
        proof (cases "expr e2 env cd st g'")
          case s2: (n a' g'')
          then show ?thesis
          proof (cases a')
            case f2:(Pair a' b')
            then show ?thesis
            proof (cases a')
              case (KValue x1')
              with s1 f1 k1 v1 assms(1) assms(2) show ?thesis by auto
            next
              case (KCDptr x2)
              with s1 f1 k1 v1 assms(1) assms(2) show ?thesis by auto
            next
              case (KMemptr x2')
              with s1 f1 k1 v1 assms(1) assms(2) show ?thesis by auto
            next
              case (KStoptr x3')
              with s1 f1 k1 v1 assms(1) assms(2) show ?thesis by auto
            qed
          qed
        next
          case (e e)
          then show ?thesis using k1 s1 v1 assms(1) assms(2) f1 by auto
        qed
      next
        case (Calldata x2)
        then show ?thesis using k1 s1 assms(1) f1 by auto
      next
        case (Memory x2)
        then show ?thesis using k1 s1 assms(1) f1 by auto
      next
        case (Storage x3)
        then show ?thesis using k1 s1 assms(1) f1 by auto
      qed
    next
      case (KCDptr x2)
      then show ?thesis using s1 assms(1) f1 by fastforce
    next
      case (KMemptr x2)
      then show ?thesis using s1 assms(1) f1 by fastforce
    next
      case (KStoptr x3)
      then show ?thesis using s1 assms(1) f1 by fastforce
    qed
  qed
next
  case (e e)
  then show ?thesis using assms(1) by simp
qed

lemma ssel_eq_ssel:
  "(\<And>i g. i \<in> set ix \<Longrightarrow> expr i env cd st g = expr (f i) env cd st g)
  \<Longrightarrow> ssel tp loc ix env cd st g = ssel tp loc (map f ix) env cd st g"
proof (induction ix arbitrary: tp loc env cd st g)
  case Nil
  then show ?case by simp
next
  case c1: (Cons i ix)
  then show ?case
  proof (cases tp)
    case tp1: (STArray al tp)
    then show ?thesis
    proof (cases "expr i env cd st g")
      case s1: (n a g')
      then show ?thesis
      proof (cases a)
        case f1: (Pair a b)
        then show ?thesis
        proof (cases a)
          case k1: (KValue v)
          then show ?thesis
          proof (cases b)
            case v1: (Value t)
            then show ?thesis
            proof (cases "less t (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al)")
              case None
              with v1 k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
            next
              case s2: (Some a)
              then show ?thesis
              proof (cases a)
                case p1: (Pair a b)
                then show ?thesis
                proof (cases b)
                  case (TSInt x1)
                  with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
                next
                  case (TUInt x2)
                  with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
                next
                  case b1: TBool
                  show ?thesis
                  proof cases
                    assume "a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                    from c1.IH[OF c1.prems] have
                      "ssel tp (hash loc v) ix env cd st g' = ssel tp (hash loc v) (map f ix) env cd st g'"
                      by simp
                    with mp s2 b1 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
                  next
                    assume "\<not> a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                    with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
                  qed
                next
                  case TAddr
                  with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
                qed
              qed
            qed
          next
            case (Calldata x2)
            with k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
          next
            case (Memory x2)
            with k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
          next
            case (Storage x3)
            with k1 tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
          qed
        next
          case (KCDptr x2)
          with tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        next
          case (KMemptr x2)
          with tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        next
          case (KStoptr x3)
          with tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        qed
      qed
    next
      case (e e)
      with tp1 c1.prems show ?thesis by (simp add:Statements.solidity.ssel.simps)
    qed
  next
    case tp1: (STMap _ t)
    then show ?thesis
    proof (cases "expr i env cd st g")
      case s1: (n a g')
      then show ?thesis
      proof (cases a)
        case f1: (Pair a b)
        then show ?thesis
        proof (cases a)
          case k1: (KValue v)
          from c1.IH[OF c1.prems] have
            "ssel tp (hash loc v) ix env cd st g = ssel tp (hash loc v) (map f ix) env cd st g" by simp
          with k1 tp1 s1 c1 f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        next
          case (KCDptr x2)
          with tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        next
          case (KMemptr x2)
          with tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        next
          case (KStoptr x3)
          with tp1 s1 c1.prems f1 show ?thesis by (simp add:Statements.solidity.ssel.simps)
        qed
      qed
    next
      case (e e)
      with tp1 c1.prems show ?thesis by (simp add:Statements.solidity.ssel.simps)
    qed
  next
    case (STValue x2)
    then show ?thesis by (simp add:Statements.solidity.ssel.simps)
  qed
qed

lemma msel_eq_msel:
"(\<And>i g. i \<in> set ix \<Longrightarrow> expr i env cd st g = expr (f i) env cd st g) \<Longrightarrow>
          msel c tp loc ix env cd st g = msel c tp loc (map f ix) env cd st g"
proof (induction ix arbitrary: c tp loc env cd st g)
  case Nil
  then show ?case by simp
next
  case c1: (Cons i ix)
  then show ?case
  proof (cases tp)
    case tp1: (MTArray al tp)
    then show ?thesis
    proof (cases ix)
      case Nil
      thus ?thesis using tp1 c1.prems by (auto simp add:Statements.solidity.msel.simps)
    next
      case c2: (Cons a list)
      then show ?thesis
      proof (cases "expr i env cd st g")
        case s1: (n a g')
        then show ?thesis
        proof (cases a)
          case f1: (Pair a b)
          then show ?thesis
          proof (cases a)
            case k1: (KValue v)
            then show ?thesis
            proof (cases b)
              case v1: (Value t)
              then show ?thesis
              proof (cases "less t (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al)")
                case None
                with v1 k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
              next
                case s2: (Some a)
                then show ?thesis
                proof (cases a)
                  case p1: (Pair a b)
                  then show ?thesis
                  proof (cases b)
                    case (TSInt x1)
                    with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                  next
                    case (TUInt x2)
                    with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                  next
                    case b1: TBool
                    show ?thesis
                    proof cases
                      assume "a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                      then show ?thesis
                      proof (cases c)
                        case True
                        then show ?thesis
                        proof (cases "accessStore (hash loc v) (memory st)")
                          case None
                          with s2 b1 p1 v1 k1 tp1 s1 c1.prems f1 True show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (MValue x1)
                            with s2 s3 b1 p1 v1 k1 tp1 s1 c1.prems f1 True show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                          next
                            case mp: (MPointer l)
                            from c1.IH[OF c1.prems]
                              have "msel c tp l ix env cd st g' = msel c tp l (map f ix) env cd st g'" by simp
                            with mp s2 s3 b1 p1 v1 k1 tp1 s1 c1.prems f1 True show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                          qed
                        qed
                      next
                        case False
                        then show ?thesis
                        proof (cases "accessStore (hash loc v) cd")
                          case None
                          with s2 b1 p1 v1 k1 tp1 s1 c1.prems f1 False show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (MValue x1)
                            with s2 s3 b1 p1 v1 k1 tp1 s1 c1.prems f1 False show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                          next
                            case mp: (MPointer l)
                            from c1.IH[OF c1.prems]
                              have "msel c tp l ix env cd st g' = msel c tp l (map f ix) env cd st g'" by simp
                            with mp s2 s3 b1 p1 v1 k1 tp1 s1 c1.prems f1 False show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                          qed
                        qed
                      qed
                    next
                      assume "\<not> a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                      with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                    qed
                  next
                    case TAddr
                    with s2 p1 v1 k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
                  qed
                qed
              qed
            next
              case (Calldata x2)
              with k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
            next
              case (Memory x2)
              with k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
            next
              case (Storage x3)
              with k1 tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
            qed
          next
            case (KCDptr x2)
            with tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
          next
            case (KMemptr x2)
            with tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
          next
            case (KStoptr x3)
            with tp1 s1 c1.prems f1 show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
          qed
        qed
      next
        case (e e)
        with tp1 c1.prems show ?thesis using c2 by (simp add:Statements.solidity.msel.simps)
      qed
    qed
  next
    case (MTValue x2)
    then show ?thesis by (simp add:Statements.solidity.msel.simps)
  qed
qed

lemma ref_eq:
  assumes "\<And>e g. e \<in> set ex \<Longrightarrow> expr e env cd st g = expr (f e) env cd st g"
  shows "rexp (Ref i ex) env cd st g = rexp (Ref i (map f ex)) env cd st g"
proof (cases "fmlookup (denvalue env) i")
  case None
  then show ?thesis by (simp add:Statements.solidity.rexp.simps)
next
  case s1: (Some a)
  then show ?thesis
  proof (cases a)
    case p1: (Pair tp b)
    then show ?thesis
    proof (cases b)
      case k1: (Stackloc l)
      then show ?thesis
      proof (cases "accessStore l (stack st)")
        case None
        with s1 p1 k1 show ?thesis by (simp add:Statements.solidity.rexp.simps)
      next
        case s2: (Some a')
        then show ?thesis
        proof (cases a')
          case (KValue _)
          with s1 s2 p1 k1 show ?thesis by (simp add:Statements.solidity.rexp.simps)
        next
          case cp: (KCDptr cp)
          then show ?thesis
          proof (cases tp)
            case (Value x1)
            with cp s1 s2 p1 k1 show ?thesis by (simp add:Statements.solidity.rexp.simps)
          next
            case mt: (Calldata ct)
            from msel_eq_msel have
              "msel False ct cp ex env cd st=msel False ct cp (map f ex) env cd st" using assms by blast
            thus ?thesis using s1 s2 p1 k1 mt cp by (simp add:Statements.solidity.rexp.simps)
          next
            case mt: (Memory mt)
            from msel_eq_msel have
              "msel True mt cp ex env cd st=msel True mt cp (map f ex) env cd st" using assms by blast
            thus ?thesis using s1 s2 p1 k1 mt cp by (simp add:Statements.solidity.rexp.simps)
          next
            case (Storage x3)
            with cp s1 s2 p1 k1 show ?thesis by (simp add:Statements.solidity.rexp.simps)
          qed
        next
          case mp: (KMemptr mp)
          then show ?thesis
          proof (cases tp)
            case (Value x1)
            with mp s1 s2 p1 k1 show ?thesis by (simp add:Statements.solidity.rexp.simps)
          next
            case mt: (Calldata ct)
            from msel_eq_msel have
              "msel True ct mp ex env cd st=msel True ct mp (map f ex) env cd st" using assms by blast
            thus ?thesis using s1 s2 p1 k1 mt mp by (simp add:Statements.solidity.rexp.simps)
          next
            case mt: (Memory mt)
            from msel_eq_msel have
              "msel True mt mp ex env cd st=msel True mt mp (map f ex) env cd st" using assms by blast
            thus ?thesis using s1 s2 p1 k1 mt mp by (simp add:Statements.solidity.rexp.simps)
          next
            case (Storage x3)
            with mp s1 s2 p1 k1 show ?thesis by (simp add:Statements.solidity.rexp.simps)
          qed
        next
          case sp: (KStoptr sp)
          then show ?thesis
          proof (cases tp)
            case (Value x1)
            then show ?thesis using s1 s2 p1 k1 sp by (simp add:Statements.solidity.rexp.simps)
          next
            case (Calldata x2)
            then show ?thesis using s1 s2 p1 k1 sp by (simp add:Statements.solidity.rexp.simps)
          next
            case (Memory x2)
            then show ?thesis using s1 s2 p1 k1 sp by (simp add:Statements.solidity.rexp.simps)
          next
            case st: (Storage stp)
            from ssel_eq_ssel have
              "ssel stp sp ex env cd st=ssel stp sp (map f ex) env cd st" using assms by blast
            thus ?thesis using s1 s2 p1 k1 st sp by (simp add:Statements.solidity.rexp.simps)
          qed
        qed
      qed
    next
      case sl:(Storeloc sl)
      then show ?thesis
      proof (cases tp)
        case (Value x1)
        then show ?thesis using s1 p1 sl by (simp add:Statements.solidity.rexp.simps)
      next
        case (Calldata x2)
        then show ?thesis using s1 p1 sl by (simp add:Statements.solidity.rexp.simps)
      next
        case (Memory x2)
        then show ?thesis using s1 p1 sl by (simp add:Statements.solidity.rexp.simps)
      next
        case st: (Storage stp)
        from ssel_eq_ssel have
          "ssel stp sl ex env cd st=ssel stp sl (map f ex) env cd st" using assms by blast
        thus ?thesis using s1 sl p1 st by (simp add:Statements.solidity.rexp.simps)
      qed
    qed
  qed
qed

text\<open>
  The following theorem proves that the update function preserves the semantics of expressions.
\<close>
theorem update_correctness:
    "\<And>g. expr ex env cd st g = expr (eupdate ex) env cd st g"
    "\<And>g. rexp lv env cd st g = rexp (lupdate lv) env cd st g"
proof (induction ex and lv)
  case (Id x g)
  then show ?case by simp
next
  case (Ref d ix g)
  then show ?case using ref_eq[where f="eupdate"] by simp
next
  case (INT b v g)
  then show ?case
  proof (cases "g > 0")
    case True
    then show ?thesis
    proof cases
      assume "b\<in>vbits"
      show ?thesis
      proof cases
        let ?m_def = "(-(2^(b-1)) + (v+2^(b-1)) mod (2^b))"
        assume "v \<ge> 0"
  
        from `b\<in>vbits` True have
          "expr (E.INT b v) env cd st g = Normal ((KValue (createSInt b v), Value (TSInt b)), g)" 
          by (simp add:Statements.solidity.expr.simps)
        also have "createSInt b v = createSInt b ?m_def" using `b\<in>vbits` `v \<ge> 0` unfolding createSInt_def by auto
        also from `v \<ge> 0` `b\<in>vbits` True have
          "Normal ((KValue (createSInt b ?m_def), Value (TSInt b)),g) = expr (eupdate (E.INT b v)) env cd st g"
          by (simp add:Statements.solidity.expr.simps)
        finally show "expr (E.INT b v) env cd st g = expr (eupdate (E.INT b v)) env cd st g" by simp
      next
        let ?m_def = "(2^(b-1) - (-v+2^(b-1)-1) mod (2^b) - 1)"
        assume "\<not> v \<ge> 0"
  
        from `b\<in>vbits` True have
          "expr (E.INT b v) env cd st g = Normal ((KValue (createSInt b v), Value (TSInt b)), g)" by (simp add:Statements.solidity.expr.simps)
        also have "createSInt b v = createSInt b ?m_def" using `b\<in>vbits` `\<not> v \<ge> 0` unfolding createSInt_def by auto
        also from `\<not> v \<ge> 0` `b\<in>vbits` True have
          "Normal ((KValue (createSInt b ?m_def), Value (TSInt b)),g) =expr (eupdate (E.INT b v)) env cd st g"
          by (simp add:Statements.solidity.expr.simps)
        finally show "expr (E.INT b v) env cd st g = expr (eupdate (E.INT b v)) env cd st g" by simp
      qed
    next
      assume "\<not> b\<in>vbits"
      thus ?thesis by auto
    qed
  next
    case False
    then show ?thesis using no_gas by simp
  qed
next
  case (UINT x1 x2)
  then show ?case by (simp add:Statements.solidity.expr.simps createUInt_def)
next
  case (ADDRESS x)
  then show ?case by simp
next
  case (BALANCE x)
  then show ?case by simp
next
  case THIS
  then show ?case by simp
next
  case SENDER
  then show ?case by simp
next
  case VALUE
  then show ?case by simp
next
  case TRUE
  then show ?case by simp
next
  case FALSE
  then show ?case by simp
next
  case (LVAL x)
  then show ?case by (simp add:Statements.solidity.expr.simps createUInt_def)
next
  case p: (PLUS e1 e2 g)
  show ?case
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with p.IH have expr1: "expr e1 env cd st g = expr (E.INT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      then show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createSInt b1 v1), Value (TSInt b1)), g)" by (simp add:Statements.solidity.expr.simps createSInt_def)
        moreover from i `b1 \<in> vbits`
          have "v1 < 2^(b1-1)" and "v1 \<ge> -(2^(b1-1))" using update_bounds_int by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TSInt b1)),g)"
          using createSInt_id[of v1 b1] by simp
        thus ?thesis
        proof (cases "eupdate e2")
          case i2: (INT b2 v2)
          with p.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 + v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i2 `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              let ?x="- (2 ^ (max b1 b2 - 1)) + (?v + 2 ^ (max b1 b2 - 1)) mod 2 ^ max b1 b2"
              assume "?v\<ge>0"
              hence "createSInt (max b1 b2) ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" by (simp add: createSInt_def)
              moreover have "add (TSInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                = Some (createSInt (max b1 b2) ?v, TSInt (max b1 b2))"
                using Read_ShowL_id add_def olift.simps(1)[of "(+)" b1 b2] by simp
              ultimately have "expr (PLUS e1 e2) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
              moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
              proof -
                from `b1 \<in> vbits` `b2 \<in> vbits` `?v\<ge>0`
                  have "eupdate (PLUS e1 e2) = E.INT (max b1 b2) ?x" using i i2 by simp
                moreover have "expr (E.INT (max b1 b2) ?x) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` have "max b1 b2 \<in> vbits" using vbits_max by simp
                  with True have "expr (E.INT (max b1 b2) ?x) env cd st g
                    = Normal ((KValue (createSInt (max b1 b2) ?x), Value (TSInt (max b1 b2))),g)" by (simp add:Statements.solidity.expr.simps)
                  moreover from `0 < b1`
                    have "?x < 2 ^ (max b1 b2 - 1)" using upper_bound3 by simp
                  moreover from `0 < b1` have "0 < max b1 b2" using max_def by simp
                  ultimately show ?thesis using createSInt_id[of ?x "max b1 b2"] by simp
                qed
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            next
              let ?x="2^(max b1 b2 -1) - (-?v+2^(max b1 b2-1)-1) mod (2^max b1 b2) - 1"
              assume "\<not> ?v\<ge>0"
              hence "createSInt (max b1 b2) ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
              moreover have "add (TSInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                = Some (createSInt (max b1 b2) ?v, TSInt (max b1 b2))"
                using Read_ShowL_id add_def olift.simps(1)[of "(+)" b1 b2] by simp
              ultimately have "expr (PLUS e1 e2) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)" using True r1 r2 by (simp add:Statements.solidity.expr.simps)
              moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
              proof -
                from `b1 \<in> vbits` `b2 \<in> vbits` `\<not>?v\<ge>0`
                  have "eupdate (PLUS e1 e2) = E.INT (max b1 b2) ?x" using i i2 by simp
                moreover have "expr (E.INT (max b1 b2) ?x) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` have "max b1 b2 \<in> vbits" using vbits_max by simp
                  with True have "expr (E.INT (max b1 b2) ?x) env cd st g
                    = Normal ((KValue (createSInt (max b1 b2) ?x), Value (TSInt (max b1 b2))),g)" by (simp add:Statements.solidity.expr.simps)
                  moreover from `0 < b1`
                    have "?x \<ge> - (2 ^ (max b1 b2 - 1))" using lower_bound2[of "max b1 b2" ?v] by simp
                  moreover from `b1 > 0` have "2^(max b1 b2 -1) > (0::nat)" by simp
                    hence "2^(max b1 b2 -1) - (-?v+2^(max b1 b2-1)-1) mod (2^max b1 b2) - 1 < 2 ^ (max b1 b2 - 1)"
                      by (simp add: algebra_simps flip: zle_diff1_eq)
                  moreover from `0 < b1` have "0 < max b1 b2" using max_def by simp
                  ultimately show ?thesis using createSInt_id[of ?x "max b1 b2"] by simp
                qed
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with p i i2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case u2: (UINT b2 v2)
          with p.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 + v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u2 `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              using createUInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b2<b1"
              thus ?thesis
              proof (cases)
                let ?x="- (2 ^ (b1 - 1)) + (?v + 2 ^ (b1 - 1)) mod 2 ^ b1"
                assume "?v\<ge>0"
                hence "createSInt b1 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" using `b2<b1` unfolding createSInt_def by auto
                moreover have "add (TSInt b1) (TUInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b1 ?v, TSInt b1)"
                  using Read_ShowL_id add_def olift.simps(3)[of "(+)" b1 b2] `b2<b1` by simp
                ultimately have "expr (PLUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` `?v\<ge>0` `b2<b1`
                    have "eupdate (PLUS e1 e2) = E.INT b1 ?x" using i u2 by simp
                  moreover have "expr (E.INT b1 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                  proof -
                    from `b1 \<in> vbits` True have "expr (E.INT b1 ?x) env cd st g
                      = Normal ((KValue (createSInt b1 ?x), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b1` have "?x < 2 ^ (b1 - 1)" using upper_bound2 by simp
                    ultimately show ?thesis using createSInt_id[of ?x "b1"] `0 < b1` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              next
                let ?x="2^(b1 -1) - (-?v+2^(b1-1)-1) mod (2^b1) - 1"
                assume "\<not> ?v\<ge>0"
                hence "createSInt b1 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
                moreover have "add (TSInt b1) (TUInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b1 ?v, TSInt b1)"
                  using Read_ShowL_id add_def olift.simps(3)[of "(+)" b1 b2] `b2<b1` by simp
                ultimately have "expr (PLUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` `\<not>?v\<ge>0` `b2<b1`
                    have "eupdate (PLUS e1 e2) = E.INT b1 ?x" using i u2 by simp
                  moreover have "expr (E.INT b1 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                  proof -
                    from `b1 \<in> vbits` True have "expr (E.INT b1 ?x) env cd st g
                      = Normal ((KValue (createSInt b1 ?x), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b1` have "?x \<ge> - (2 ^ (b1 - 1))" using upper_bound2 by simp
                    moreover have "2^(b1-1) - (-?v+2^(b1-1)-1) mod (2^b1) - 1 < 2 ^ (b1 - 1)"
                      by (simp add: algebra_simps flip: int_one_le_iff_zero_less)
                    ultimately show ?thesis using createSInt_id[of ?x b1] `0 < b1` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              qed
            next
              assume "\<not> b2 < b1"
              with i u2 have "eupdate (PLUS e1 e2) = PLUS (eupdate e1) (eupdate e2)" by simp
              with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with p i u2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with p i show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case u: (UINT b1 v1)
    with p.IH have expr1: "expr e1 env cd st g = expr (UINT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      then show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createUInt b1 v1), Value (TUInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from u `b1 \<in> vbits`
          have "v1 < 2^b1" and "v1 \<ge> 0" using update_bounds_uint by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TUInt b1)),g)"
          by (simp add:Statements.solidity.expr.simps createUInt_def)
        thus ?thesis
        proof (cases "eupdate e2")
          case u2: (UINT b2 v2)
          with p.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 + v2"
            let ?x="?v mod 2 ^ max b1 b2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u2 `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              by (simp add:Statements.solidity.expr.simps createUInt_def)
            moreover have "add (TUInt b1) (TUInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
              = Some (createUInt (max b1 b2) ?v, TUInt (max b1 b2))"
              using Read_ShowL_id add_def olift.simps(2)[of "(+)" b1 b2] by simp
            ultimately have "expr (PLUS e1 e2) env cd st g
              = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TUInt (max b1 b2))),g)" using r1 True by (simp add:Statements.solidity.expr.simps createUInt_def)
            moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
              = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TUInt (max b1 b2))),g)"
            proof -
              from `b1 \<in> vbits` `b2 \<in> vbits`
                have "eupdate (PLUS e1 e2) = UINT (max b1 b2) ?x" using u u2 by simp
              moreover have "expr (UINT (max b1 b2) ?x) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TUInt (max b1 b2))),g)"
              proof -
                from `b1 \<in> vbits` `b2 \<in> vbits` have "max b1 b2 \<in> vbits" using vbits_max by simp
                with True have "expr (UINT (max b1 b2) ?x) env cd st g
                  = Normal ((KValue (createUInt (max b1 b2) ?x), Value (TUInt (max b1 b2))),g)" by (simp add:Statements.solidity.expr.simps)
                moreover from `0 < b1`
                  have "?x < 2 ^ (max b1 b2)" by simp
                moreover from `0 < b1` have "0 < max b1 b2" using max_def by simp
                ultimately show ?thesis by (simp add:Statements.solidity.expr.simps createUInt_def)
              qed
              ultimately show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          next
            assume "\<not> b2 \<in> vbits"
            with p u u2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case i2: (INT b2 v2)
          with p.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 + v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i2 `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b1<b2"
              thus ?thesis
              proof (cases)
                let ?x="- (2 ^ (b2 - 1)) + (?v + 2 ^ (b2 - 1)) mod 2 ^ b2"
                assume "?v\<ge>0"
                hence "createSInt b2 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" using `b1<b2` unfolding createSInt_def by auto
                moreover have "add (TUInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b2 ?v, TSInt b2)"
                  using Read_ShowL_id add_def olift.simps(4)[of "(+)" b1 b2] `b1<b2` by simp
                ultimately have "expr (PLUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` `?v\<ge>0` `b1<b2`
                    have "eupdate (PLUS e1 e2) = E.INT b2 ?x" using u i2 by simp
                  moreover have "expr (E.INT b2 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                  proof -
                    from `b2 \<in> vbits` True have "expr (E.INT b2 ?x) env cd st g
                      = Normal ((KValue (createSInt b2 ?x), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b2` have "?x < 2 ^ (b2 - 1)" using upper_bound2 by simp
                    ultimately show ?thesis using createSInt_id[of ?x "b2"] `0 < b2` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              next
                let ?x="2^(b2 -1) - (-?v+2^(b2-1)-1) mod (2^b2) - 1"
                assume "\<not> ?v\<ge>0"
                hence "createSInt b2 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
                moreover have "add (TUInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b2 ?v, TSInt b2)"
                  using Read_ShowL_id add_def olift.simps(4)[of "(+)" b1 b2] `b1<b2` by simp
                ultimately have "expr (PLUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (PLUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` `\<not>?v\<ge>0` `b1<b2`
                    have "eupdate (PLUS e1 e2) = E.INT b2 ?x" using u i2 by simp
                  moreover have "expr (E.INT b2 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                  proof -
                    from `b2 \<in> vbits` True have "expr (E.INT b2 ?x) env cd st g
                      = Normal ((KValue (createSInt b2 ?x), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b2` have "?x \<ge> - (2 ^ (b2 - 1))" using upper_bound2 by simp
                    moreover have "2^(b2-1) - (-?v+2^(b2-1)-1) mod (2^b2) - 1 < 2 ^ (b2 - 1)"
                      by (simp add: algebra_simps flip: int_one_le_iff_zero_less)
                    ultimately show ?thesis using createSInt_id[of ?x b2] `0 < b2` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              qed
            next
              assume "\<not> b1 < b2"
              with p u i2 show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with p u i2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with p u show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case (ADDRESS x3)
    with p show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with p show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with p show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with p show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case TRUE
    with p show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case FALSE
    with p show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (LVAL x7)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (PLUS x81 x82)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with p show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  qed
next
  case m: (MINUS e1 e2 g)
  show ?case
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with m.IH have expr1: "expr e1 env cd st g = expr (E.INT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createSInt b1 v1), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from i `b1 \<in> vbits`
          have "v1 < 2^(b1-1)" and "v1 \<ge> -(2^(b1-1))" using update_bounds_int by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TSInt b1)),g)"
          using createSInt_id[of v1 b1] by simp
        thus ?thesis
        proof (cases "eupdate e2")
          case i2: (INT b2 v2)
          with m.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 - v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i2 `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
  
            from `b1 \<in> vbits` `b2 \<in> vbits` have
              u_def: "eupdate (MINUS e1 e2) =
              (let v = v1 - v2
                in if 0 \<le> v
                  then E.INT (max b1 b2)
                    (- (2 ^ (max b1 b2 - 1)) + (v + 2 ^ (max b1 b2 - 1)) mod 2 ^ max b1 b2)
                  else E.INT (max b1 b2)
                    (2 ^ (max b1 b2 - 1) - (- v + 2 ^ (max b1 b2 - 1) - 1) mod 2 ^ max b1 b2 - 1))"
              using i i2 eupdate.simps(11)[of e1 e2] by simp
  
            show ?thesis
            proof (cases)
              let ?x="- (2 ^ (max b1 b2 - 1)) + (?v + 2 ^ (max b1 b2 - 1)) mod 2 ^ max b1 b2"
              assume "?v\<ge>0"
              hence "createSInt (max b1 b2) ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
              moreover have "sub (TSInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                = Some (createSInt (max b1 b2) ?v, TSInt (max b1 b2))"
                using Read_ShowL_id sub_def olift.simps(1)[of "(-)" b1 b2] by simp
              ultimately have "expr (MINUS e1 e2) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
              moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
              proof -
                from u_def have "eupdate (MINUS e1 e2) = E.INT (max b1 b2) ?x" using `?v\<ge>0` by simp
                moreover have "expr (E.INT (max b1 b2) ?x) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` have "max b1 b2 \<in> vbits" using vbits_max by simp
                  with True have "expr (E.INT (max b1 b2) ?x) env cd st g
                    = Normal ((KValue (createSInt (max b1 b2) ?x), Value (TSInt (max b1 b2))),g)" by (simp add:Statements.solidity.expr.simps)
                  moreover from `0 < b1`
                    have "?x < 2 ^ (max b1 b2 - 1)" using upper_bound2 by simp
                  moreover from `0 < b1` have "0 < max b1 b2" using max_def by simp
                  ultimately show ?thesis using createSInt_id[of ?x "max b1 b2"] by simp
                qed
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            next
              let ?x="2^(max b1 b2 -1) - (-?v+2^(max b1 b2-1)-1) mod (2^max b1 b2) - 1"
              assume "\<not> ?v\<ge>0"
              hence "createSInt (max b1 b2) ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
              moreover have "sub (TSInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                = Some (createSInt (max b1 b2) ?v, TSInt (max b1 b2))"
                using Read_ShowL_id sub_def olift.simps(1)[of "(-)" b1 b2] by simp
              ultimately have "expr (MINUS e1 e2) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
              moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
              proof -
                from u_def have "eupdate (MINUS e1 e2) = E.INT (max b1 b2) ?x" using `\<not> ?v\<ge>0` by simp
                moreover have "expr (E.INT (max b1 b2) ?x) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt (max b1 b2))),g)"
                proof -
                  from `b1 \<in> vbits` `b2 \<in> vbits` have "max b1 b2 \<in> vbits" using vbits_max by simp
                  with True have "expr (E.INT (max b1 b2) ?x) env cd st g
                    = Normal ((KValue (createSInt (max b1 b2) ?x), Value (TSInt (max b1 b2))),g)" by (simp add:Statements.solidity.expr.simps createSInt_def)
                  moreover from `0 < b1`
                    have "?x \<ge> - (2 ^ (max b1 b2 - 1))" using lower_bound2[of "max b1 b2" ?v] by simp
                  moreover from `b1 > 0` have "2^(max b1 b2 -1) > (0::nat)" by simp
                    hence "2^(max b1 b2 -1) - (-?v+2^(max b1 b2-1)-1) mod (2^max b1 b2) - 1 < 2 ^ (max b1 b2 - 1)"
                    by (simp add: algebra_simps flip: int_one_le_iff_zero_less)
                  moreover from `0 < b1` have "0 < max b1 b2" using max_def by simp
                  ultimately show ?thesis using createSInt_id[of ?x "max b1 b2"] by simp
                qed
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis by simp
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with m i i2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case u: (UINT b2 v2)
          with m.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 - v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              using createUInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b2<b1"
              with `b1 \<in> vbits` `b2 \<in> vbits` have
                u_def: "eupdate (MINUS e1 e2) =
                (let v = v1 - v2
                  in if 0 \<le> v
                    then E.INT b1 (- (2 ^ (b1 - 1)) + (v + 2 ^ (b1 - 1)) mod 2 ^ b1)
                    else E.INT b1 (2 ^ (b1 - 1) - (- v + 2 ^ (b1 - 1) - 1) mod 2 ^ b1 - 1))"
                using i u eupdate.simps(11)[of e1 e2] by simp
              show ?thesis
              proof (cases)
                let ?x="- (2 ^ (b1 - 1)) + (?v + 2 ^ (b1 - 1)) mod 2 ^ b1"
                assume "?v\<ge>0"
                hence "createSInt b1 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" using `b2<b1` unfolding createSInt_def by auto
                moreover have "sub (TSInt b1) (TUInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b1 ?v, TSInt b1)"
                  using Read_ShowL_id sub_def olift.simps(3)[of "(-)" b1 b2] `b2<b1` by simp
                ultimately have "expr (MINUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                proof -
                  from u_def have "eupdate (MINUS e1 e2) = E.INT b1 ?x" using `?v\<ge>0` by simp
                  moreover have "expr (E.INT b1 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                  proof -
                    from `b1 \<in> vbits` True have "expr (E.INT b1 ?x) env cd st g
                      = Normal ((KValue (createSInt b1 ?x), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b1` have "?x < 2 ^ (b1 - 1)" using upper_bound2 by simp
                    ultimately show ?thesis using createSInt_id[of ?x "b1"] `0 < b1` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              next
                let ?x="2^(b1 -1) - (-?v+2^(b1-1)-1) mod (2^b1) - 1"
                assume "\<not> ?v\<ge>0"
                hence "createSInt b1 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
                moreover have "sub (TSInt b1) (TUInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b1 ?v, TSInt b1)"
                  using Read_ShowL_id sub_def olift.simps(3)[of "(-)" b1 b2] `b2<b1` by simp
                ultimately have "expr (MINUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                proof -
                  from u_def have "eupdate (MINUS e1 e2) = E.INT b1 ?x" using `\<not> ?v\<ge>0` by simp
                  moreover have "expr (E.INT b1 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b1)),g)"
                  proof -
                    from `b1 \<in> vbits` True have "expr (E.INT b1 ?x) env cd st g
                      = Normal ((KValue (createSInt b1 ?x), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b1` have "?x \<ge> - (2 ^ (b1 - 1))" using upper_bound2 by simp
                    moreover have "2^(b1-1) - (-?v+2^(b1-1)-1) mod (2^b1) - 1 < 2 ^ (b1 - 1)"
                      by (simp add: algebra_simps flip: int_one_le_iff_zero_less)
                    ultimately show ?thesis using createSInt_id[of ?x b1] `0 < b1` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              qed
            next
              assume "\<not> b2 < b1"
              with i u have "eupdate (MINUS e1 e2) = MINUS (eupdate e1) (eupdate e2)" by simp
              with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with m i u show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with m i show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case u: (UINT b1 v1)
    with m.IH have expr1: "expr e1 env cd st g = expr (UINT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createUInt b1 v1), Value (TUInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from u `b1 \<in> vbits`
          have "v1 < 2^b1" and "v1 \<ge> 0" using update_bounds_uint by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TUInt b1)),g)"
          by (simp add:Statements.solidity.expr.simps createUInt_def)
        thus ?thesis
        proof (cases "eupdate e2")
          case u2: (UINT b2 v2)
          with m.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 - v2"
            let ?x="?v mod 2 ^ max b1 b2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u2 `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              by (simp add:Statements.solidity.expr.simps createUInt_def)
            moreover have "sub (TUInt b1) (TUInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
              = Some (createUInt (max b1 b2) ?v, TUInt (max b1 b2))"
              using Read_ShowL_id sub_def olift.simps(2)[of "(-)" b1 b2] by simp
            ultimately have "expr (MINUS e1 e2) env cd st g
              = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TUInt (max b1 b2))),g)" using r1 True by (simp add:Statements.solidity.expr.simps createUInt_def)
            moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
              = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TUInt (max b1 b2))),g)"
            proof -
              from `b1 \<in> vbits` `b2 \<in> vbits`
                have "eupdate (MINUS e1 e2) = UINT (max b1 b2) ?x" using u u2 by simp
              moreover have "expr (UINT (max b1 b2) ?x) env cd st g
                = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TUInt (max b1 b2))),g)"
              proof -
                from `b1 \<in> vbits` `b2 \<in> vbits` have "max b1 b2 \<in> vbits" using vbits_max by simp
                with True have "expr (UINT (max b1 b2) ?x) env cd st g
                  = Normal ((KValue (createUInt (max b1 b2) ?x), Value (TUInt (max b1 b2))),g)" by (simp add:Statements.solidity.expr.simps)
                moreover from `0 < b1`
                  have "?x < 2 ^ (max b1 b2)" by simp
                moreover from `0 < b1` have "0 < max b1 b2" using max_def by simp
                ultimately show ?thesis by (simp add:Statements.solidity.expr.simps createUInt_def)
              qed
              ultimately show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          next
            assume "\<not> b2 \<in> vbits"
            with m u u2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case i: (INT b2 v2)
          with m.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 - v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b1<b2"
              with `b1 \<in> vbits` `b2 \<in> vbits` have
                u_def: "eupdate (MINUS e1 e2) =
                (let v = v1 - v2
                  in if 0 \<le> v
                    then E.INT b2 (- (2 ^ (b2 - 1)) + (v + 2 ^ (b2 - 1)) mod 2 ^ b2)
                    else E.INT b2 (2 ^ (b2 - 1) - (- v + 2 ^ (b2 - 1) - 1) mod 2 ^ b2 - 1))"
                using u i by simp
              show ?thesis
              proof (cases)
                let ?x="- (2 ^ (b2 - 1)) + (?v + 2 ^ (b2 - 1)) mod 2 ^ b2"
                assume "?v\<ge>0"
                hence "createSInt b2 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" using `b1<b2` unfolding createSInt_def by auto
                moreover have "sub (TUInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b2 ?v, TSInt b2)"
                  using Read_ShowL_id sub_def olift.simps(4)[of "(-)" b1 b2] `b1<b2` by simp
                ultimately have "expr (MINUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                proof -
                  from u_def have "eupdate (MINUS e1 e2) = E.INT b2 ?x" using `?v\<ge>0` by simp
                  moreover have "expr (E.INT b2 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                  proof -
                    from `b2 \<in> vbits` True have "expr (E.INT b2 ?x) env cd st g
                      = Normal ((KValue (createSInt b2 ?x), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b2` have "?x < 2 ^ (b2 - 1)" using upper_bound2 by simp
                    ultimately show ?thesis using createSInt_id[of ?x "b2"] `0 < b2` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              next
                let ?x="2^(b2 -1) - (-?v+2^(b2-1)-1) mod (2^b2) - 1"
                assume "\<not> ?v\<ge>0"
                hence "createSInt b2 ?v = (ShowL\<^sub>i\<^sub>n\<^sub>t ?x)" unfolding createSInt_def by simp
                moreover have "sub (TUInt b1) (TSInt b2) (ShowL\<^sub>i\<^sub>n\<^sub>t v1) (ShowL\<^sub>i\<^sub>n\<^sub>t v2)
                  = Some (createSInt b2 ?v, TSInt b2)"
                  using Read_ShowL_id sub_def olift.simps(4)[of "(-)" b1 b2] `b1<b2` by simp
                ultimately have "expr (MINUS e1 e2) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)" using r1 r2 True by (simp add:Statements.solidity.expr.simps)
                moreover have "expr (eupdate (MINUS e1 e2)) env cd st g
                  = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                proof -
                  from u_def have "eupdate (MINUS e1 e2) = E.INT b2 ?x" using `\<not> ?v\<ge>0` by simp
                  moreover have "expr (E.INT b2 ?x) env cd st g
                    = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t ?x), Value (TSInt b2)),g)"
                  proof -
                    from `b2 \<in> vbits` True have "expr (E.INT b2 ?x) env cd st g
                      = Normal ((KValue (createSInt b2 ?x), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
                    moreover from `0 < b2` have "?x \<ge> - (2 ^ (b2 - 1))" using upper_bound2 by simp
                    moreover have "2^(b2-1) - (-?v+2^(b2-1)-1) mod (2^b2) - 1 < 2 ^ (b2 - 1)"
                      by (simp add: algebra_simps flip: int_one_le_iff_zero_less)
                    ultimately show ?thesis using createSInt_id[of ?x b2] `0 < b2` by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                ultimately show ?thesis by simp
              qed
            next
              assume "\<not> b1 < b2"
              with m u i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with m u i show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with m u show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case (ADDRESS x3)
    with m show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with m show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with m show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with m show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case TRUE
    with m show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case FALSE
    with m show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (LVAL x7)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (PLUS x81 x82)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with m show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  qed
next
  case e: (EQUAL e1 e2 g)
  show ?case
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with e.IH have expr1: "expr e1 env cd st g = expr (E.INT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      then show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createSInt b1 v1), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from i `b1 \<in> vbits`
          have "v1 < 2^(b1-1)" and "v1 \<ge> -(2^(b1-1))" using update_bounds_int by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TSInt b1)),g)"
          using createSInt_id[of v1 b1] by simp
        thus ?thesis
        proof (cases "eupdate e2")
          case i2: (INT b2 v2)
          with e.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i2 `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            with r1 True have "expr (EQUAL e1 e2) env cd st g =
              Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))=((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
              using equal_def plift.simps(1)[of "(=)"] by (simp add:Statements.solidity.expr.simps)
            hence "expr (EQUAL e1 e2) env cd st g = Normal ((KValue (createBool (v1=v2)), Value TBool),g)"
              using Read_ShowL_id by simp
            with `b1 \<in> vbits` `b2 \<in> vbits` True show ?thesis using i i2 by (simp add:Statements.solidity.expr.simps createBool_def)
          next
            assume "\<not> b2 \<in> vbits"
            with e i i2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case u: (UINT b2 v2)
          with e.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              using createUInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b2<b1"
              with r1 r2 True have "expr (EQUAL e1 e2) env cd st g =
                Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))=((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
                using equal_def plift.simps(3)[of "(=)"] by (simp add:Statements.solidity.expr.simps)
              hence "expr (EQUAL e1 e2) env cd st g = Normal ((KValue (createBool (v1=v2)), Value TBool),g)"
                using Read_ShowL_id by simp
              with `b1 \<in> vbits` `b2 \<in> vbits` `b2<b1` True show ?thesis using i u by (simp add:Statements.solidity.expr.simps createBool_def)
            next
              assume "\<not> b2 < b1"
              with i u have "eupdate (EQUAL e1 e2) = EQUAL (eupdate e1) (eupdate e2)" by simp
              with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with e i u show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with e i show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case u: (UINT b1 v1)
    with e.IH have expr1: "expr e1 env cd st g = expr (UINT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      then show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createUInt b1 v1), Value (TUInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from u `b1 \<in> vbits`
          have "v1 < 2^b1" and "v1 \<ge> 0" using update_bounds_uint by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TUInt b1)),g)"
          by (simp add:Statements.solidity.expr.simps createUInt_def)
        thus ?thesis
        proof (cases "eupdate e2")
          case u2: (UINT b2 v2)
          with e.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u2 `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              by (simp add:Statements.solidity.expr.simps createUInt_def)
            with r1 True have "expr (EQUAL e1 e2) env cd st g =
              Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))=((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
              using equal_def plift.simps(2)[of "(=)"] by (simp add:Statements.solidity.expr.simps createUInt_def)
            hence "expr (EQUAL e1 e2) env cd st g = Normal ((KValue (createBool (v1=v2)), Value TBool),g)"
              using Read_ShowL_id by simp
            with `b1 \<in> vbits` `b2 \<in> vbits` show ?thesis using u u2 True by (simp add:Statements.solidity.expr.simps createBool_def)
          next
            assume "\<not> b2 \<in> vbits"
            with e u u2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case i: (INT b2 v2)
          with e.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 + v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b1<b2"
              with r1 r2 True have "expr (EQUAL e1 e2) env cd st g =
                Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))=((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
                using equal_def plift.simps(4)[of "(=)"] by (simp add:Statements.solidity.expr.simps)
              hence "expr (EQUAL e1 e2) env cd st g = Normal ((KValue (createBool (v1=v2)), Value TBool),g)"
                using Read_ShowL_id by simp
              with `b1 \<in> vbits` `b2 \<in> vbits` `b1<b2` True show ?thesis using u i by (simp add:Statements.solidity.expr.simps createBool_def)
            next
              assume "\<not> b1 < b2"
              with e u i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with e u i show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with e u show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case (ADDRESS x3)
    with e show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with e show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with e show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with e show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case TRUE
    with e show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case FALSE
    with e show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (LVAL x7)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (PLUS x81 x82)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with e show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  qed
next
  case l: (LESS e1 e2)
  show ?case
  proof (cases "eupdate e1")
    case i: (INT b1 v1)
    with l.IH have expr1: "expr e1 env cd st g = expr (E.INT b1 v1) env cd st g" by (simp add:Statements.solidity.expr.simps)
    then show ?thesis
    proof (cases "g > 0")
      case True
      then show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g =Normal ((KValue (createSInt b1 v1), Value (TSInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from i `b1 \<in> vbits`
          have "v1 < 2^(b1-1)" and "v1 \<ge> -(2^(b1-1))" using update_bounds_int by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TSInt b1)),g)"
          using createSInt_id[of v1 b1] by (simp add:Statements.solidity.expr.simps)
        thus ?thesis
        proof (cases "eupdate e2")
          case i2: (INT b2 v2)
          with l.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i2 `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            with r1 True have "expr (LESS e1 e2) env cd st g =
              Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))<((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
              using less_def plift.simps(1)[of "(<)"] by (simp add:Statements.solidity.expr.simps)
            hence "expr (LESS e1 e2) env cd st g = Normal ((KValue (createBool (v1<v2)), Value TBool),g)"
              using Read_ShowL_id by simp
            with `b1 \<in> vbits` `b2 \<in> vbits` show ?thesis using i i2 True by (simp add:Statements.solidity.expr.simps createBool_def)
          next
            assume "\<not> b2 \<in> vbits"
            with l i i2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case u: (UINT b2 v2)
          with l.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              using createUInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b2<b1"
              with r1 r2 True have "expr (LESS e1 e2) env cd st g =
                Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))<((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
                using less_def plift.simps(3)[of "(<)"] by (simp add:Statements.solidity.expr.simps)
              hence "expr (LESS e1 e2) env cd st g = Normal ((KValue (createBool (v1<v2)), Value TBool),g)"
                using Read_ShowL_id by simp
              with `b1 \<in> vbits` `b2 \<in> vbits` `b2<b1` show ?thesis using i u True by (simp add:Statements.solidity.expr.simps createBool_def)
            next
              assume "\<not> b2 < b1"
              with i u have "eupdate (LESS e1 e2) = LESS (eupdate e1) (eupdate e2)" by simp
              with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with l i u show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with l i show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by (simp add:Statements.solidity.expr.simps)
    qed
  next
    case u: (UINT b1 v1)
    with l.IH have expr1: "expr e1 env cd st g = expr (UINT b1 v1) env cd st g" by simp
    then show ?thesis
    proof (cases "g > 0")
      case True
      then show ?thesis
      proof (cases)
        assume "b1 \<in> vbits"
        with expr1 True
          have "expr e1 env cd st g = Normal ((KValue (createUInt b1 v1), Value (TUInt b1)),g)" by (simp add:Statements.solidity.expr.simps)
        moreover from u `b1 \<in> vbits`
          have "v1 < 2^b1" and "v1 \<ge> 0" using update_bounds_uint by auto
        moreover from `b1 \<in> vbits` have "0 < b1" by auto
        ultimately have r1: "expr e1 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v1), Value (TUInt b1)),g)"
          by (simp add:Statements.solidity.expr.simps createUInt_def)
        thus ?thesis
        proof (cases "eupdate e2")
          case u2: (UINT b2 v2)
          with l.IH have expr2: "expr e2 env cd st g = expr (UINT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createUInt b2 v2), Value (TUInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from u2 `b2 \<in> vbits`
              have "v2 < 2^b2" and "v2 \<ge> 0" using update_bounds_uint by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TUInt b2)),g)"
              by (simp add:Statements.solidity.expr.simps createUInt_def)
            with r1 True have "expr (LESS e1 e2) env cd st g = Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))<((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)" using less_def plift.simps(2)[of "(<)"] by (simp add:Statements.solidity.expr.simps)
            hence "expr (LESS e1 e2) env cd st g = Normal ((KValue (createBool (v1<v2)), Value TBool),g)" using Read_ShowL_id by simp
            with `b1 \<in> vbits` `b2 \<in> vbits` show ?thesis using u u2 True by (simp add:Statements.solidity.expr.simps createBool_def)
          next
            assume "\<not> b2 \<in> vbits"
            with l u u2 show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case i: (INT b2 v2)
          with l.IH have expr2: "expr e2 env cd st g = expr (E.INT b2 v2) env cd st g" by simp
          then show ?thesis
          proof (cases)
            let ?v="v1 + v2"
            assume "b2 \<in> vbits"
            with expr2 True
              have "expr e2 env cd st g = Normal ((KValue (createSInt b2 v2), Value (TSInt b2)),g)" by (simp add:Statements.solidity.expr.simps)
            moreover from i `b2 \<in> vbits`
              have "v2 < 2^(b2-1)" and "v2 \<ge> -(2^(b2-1))" using update_bounds_int by auto
            moreover from `b2 \<in> vbits` have "0 < b2" by auto
            ultimately have r2: "expr e2 env cd st g = Normal ((KValue (ShowL\<^sub>i\<^sub>n\<^sub>t v2), Value (TSInt b2)),g)"
              using createSInt_id[of v2 b2] by simp
            thus ?thesis
            proof (cases)
              assume "b1<b2"
              with r1 r2 True have "expr (LESS e1 e2) env cd st g =
                Normal ((KValue (createBool ((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v1))<((ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t v2))))), Value TBool),g)"
                using less_def plift.simps(4)[of "(<)"] by (simp add:Statements.solidity.expr.simps)
              hence "expr (LESS e1 e2) env cd st g = Normal ((KValue (createBool (v1<v2)), Value TBool),g)"
                using Read_ShowL_id by simp
              with `b1 \<in> vbits` `b2 \<in> vbits` `b1<b2` show ?thesis using u i True by (simp add:Statements.solidity.expr.simps createBool_def)
            next
              assume "\<not> b1 < b2"
              with l u i show ?thesis by (simp add:Statements.solidity.expr.simps)
            qed
          next
            assume "\<not> b2 \<in> vbits"
            with l u i show ?thesis by (simp add:Statements.solidity.expr.simps)
          qed
        next
          case (ADDRESS _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (BALANCE _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case THIS
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case SENDER
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case VALUE
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case TRUE
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case FALSE
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LVAL _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (PLUS _ _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (MINUS _ _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (EQUAL _ _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (LESS _ _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (AND _ _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (OR _ _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (NOT _)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (CALL x181 x182)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case (ECALL x191 x192 x193)
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        next
          case CONTRACTS
          with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
        qed
      next
        assume "\<not> b1 \<in> vbits"
        with l u show ?thesis by (simp add:Statements.solidity.expr.simps)
      qed
    next
      case False
      then show ?thesis using no_gas by simp
    qed
  next
    case (ADDRESS x3)
    with l show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with l show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with l show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with l show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case TRUE
    with l show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case FALSE
    with l show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (LVAL x7)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (PLUS x81 x82)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with l show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  qed
next
  case a: (AND e1 e2)
  show ?case
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with a show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (UINT x21 x22)
    with a show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (ADDRESS x3)
    with a show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with a show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with a show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with a show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case t: TRUE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (UINT x21 x22)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ADDRESS x3)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (BALANCE x4)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case THIS
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case SENDER
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case VALUE
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case TRUE
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps vtand.simps)
    next
      case FALSE
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps vtand.simps)
    next
      case (LVAL x7)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (PLUS x81 x82)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (MINUS x91 x92)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (EQUAL x101 x102)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (LESS x111 x112)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (AND x121 x122)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (OR x131 x132)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (NOT x131)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (CALL x181 x182)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ECALL x191 x192 x193)
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case CONTRACTS
      with a t show ?thesis by (simp add:Statements.solidity.expr.simps)
    qed
  next
    case f: FALSE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT b v)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (UINT b v)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ADDRESS x3)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (BALANCE x4)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case THIS
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case SENDER
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case VALUE
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case TRUE
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps vtand.simps)
    next
      case FALSE
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps vtand.simps)
    next
      case (LVAL x7)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (PLUS x81 x82)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (MINUS x91 x92)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (EQUAL x101 x102)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (LESS x111 x112)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (AND x121 x122)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (OR x131 x132)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (NOT x131)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (CALL x181 x182)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ECALL x191 x192 x193)
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case CONTRACTS
      with a f show ?thesis by (simp add:Statements.solidity.expr.simps)
    qed
  next
    case (LVAL x7)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case p: (PLUS x81 x82)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with a show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  qed
next
  case o: (OR e1 e2)
  show ?case
  proof (cases "eupdate e1")
    case (INT x11 x12)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (UINT x21 x22)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (ADDRESS x3)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case t: TRUE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT x11 x12)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (UINT x21 x22)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ADDRESS x3)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (BALANCE x4)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case THIS
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case SENDER
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case VALUE
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case TRUE
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps vtor.simps)
    next
      case FALSE
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps vtor.simps)
    next
      case (LVAL x7)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (PLUS x81 x82)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (MINUS x91 x92)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (EQUAL x101 x102)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (LESS x111 x112)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (AND x121 x122)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (OR x131 x132)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (NOT x131)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (CALL x181 x182)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ECALL x191 x192 x193)
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case CONTRACTS
      with o t show ?thesis by (simp add:Statements.solidity.expr.simps)
    qed
  next
    case f: FALSE
    show ?thesis
    proof (cases "eupdate e2")
      case (INT b v)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (UINT b v)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ADDRESS x3)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (BALANCE x4)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case THIS
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case SENDER
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case VALUE
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case TRUE
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps vtor.simps)
    next
      case FALSE
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps vtor.simps)
    next
      case (LVAL x7)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (PLUS x81 x82)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (MINUS x91 x92)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (EQUAL x101 x102)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (LESS x111 x112)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (AND x121 x122)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (OR x131 x132)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (NOT x131)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (CALL x181 x182)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case (ECALL x191 x192 x193)
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    next
      case CONTRACTS
      with o f show ?thesis by (simp add:Statements.solidity.expr.simps)
    qed
  next
    case (LVAL x7)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case p: (PLUS x81 x82)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with o show ?thesis using lift_eq[of e1 env cd st g "eupdate e1" e2 "eupdate e2"] by (auto simp add:Statements.solidity.expr.simps)
  qed
next
  case o: (NOT e)
  show ?case
  proof (cases "eupdate e")
    case (INT x11 x12)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (UINT x21 x22)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (ADDRESS x3)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (BALANCE x4)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case THIS
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case SENDER
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case VALUE
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case t: TRUE
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case f: FALSE
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (LVAL x7)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case p: (PLUS x81 x82)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (MINUS x91 x92)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (EQUAL x101 x102)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (LESS x111 x112)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (AND x121 x122)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (OR x131 x132)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (NOT x131)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (CALL x181 x182)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case (ECALL x191 x192 x193)
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  next
    case CONTRACTS
    with o show ?thesis by (simp add:Statements.solidity.expr.simps)
  qed
next
  case (CALL x181 x182)
  show ?case by simp
next
  case (ECALL x191 x192 x193 x194)
  show ?case by simp
next
  case CONTRACTS
  show ?case by simp
qed

end
