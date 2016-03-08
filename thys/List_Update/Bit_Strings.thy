(*  Title:       Lemmas about lists of bools
    Author:      Max Haslbeck
*)
theory Bit_Strings
imports Complex_Main
begin

section "Lemmas about BitStrings and sets theirof"


subsection "the set of bitstring of length m is finite"
lemma bitstrings_finite: "finite {xs::bool list. length xs = m}"
apply(induct m)
proof -
  fix m
  assume iH: "finite {xs::bool list. length xs = m}"
  have erl: "{xs::bool list. length xs = Suc m} =  {True#xs |xs. length xs = m} \<union>  {False#xs| xs. length xs = m}"
  apply(auto) by (metis (full_types) Suc_length_conv)

  {fix a::bool
    have 2: "{a#xs |xs. length xs = m} = (\<lambda>x. a#x) ` {xs. length xs = m}" by auto
    have "finite {a#xs |xs. length xs = m}" 
        unfolding 2 apply(rule finite_imageI) by(fact iH)
  }
  hence "finite ( {True#xs |xs::bool list. length xs = m} \<union>  {False#xs| xs. length xs = m})"
    by auto
  then show "finite {xs::bool list. length xs = Suc m}" by(simp only: erl)
qed simp


subsection "how to calculate the cardinality of the set of bitstrings with certain bits already set"


lemma fbool: "finite {xs. (\<forall>i\<in>X. xs ! i) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = m \<and> xs!e=b}"
  by(rule finite_subset[where B="{xs. length xs = m}"])
     (auto simp: bitstrings_finite)

fun witness :: "nat set \<Rightarrow> nat \<Rightarrow> bool list" where
 "witness X 0 = []"
|"witness X (Suc n) = (witness X n) @ [n \<in> X]"

lemma witness_length: "length (witness X n) = n"
apply(induct n) by auto

lemma iswitness: "r<n \<Longrightarrow> ((witness X n)!r) = (r\<in>X)"
apply(induct n)
proof -
  case (Suc n)

  have "witness X (Suc n) ! r = ((witness X n) @ [n \<in> X]) ! r" by simp
  also have "\<dots> = (if r < length (witness X n) then (witness X n) ! r else [n \<in> X] ! (r - length (witness X n)))" by(rule nth_append)
  also have "\<dots> = (if r < n then (witness X n) ! r else [n \<in> X] ! (r - n))" by (simp add: witness_length)
  finally have 1: "witness X (Suc n) ! r = (if r < n then (witness X n) ! r else [n \<in> X] ! (r - n))" .
  
  show ?case
  proof (cases "r < n")
    case True
    with 1 have a: "witness X (Suc n) ! r = (witness X n) ! r" by auto
    from Suc True have b: "witness X n ! r = (r \<in> X)" by auto
    from a b show ?thesis by auto
  next
    case False
    with Suc have "r = n" by auto
    with 1 show "witness X (Suc n) ! r = (r \<in> X)" by auto
  qed
qed simp

lemma card1: "finite S \<Longrightarrow> finite X \<Longrightarrow> finite Y \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> S \<inter> (X \<union> Y) = {} \<Longrightarrow> S\<union>X\<union>Y={0..<m} \<Longrightarrow> 
    card {xs. (\<forall>i\<in>X. xs ! i) \<and> (\<forall>i\<in>Y. \<not> xs ! i)  \<and> length xs = m} = 2^(m - card X - card Y)"
proof(induct arbitrary: X Y rule: finite_induct)
  case empty
  then have x: "X \<subseteq> {0..<m}" and y: "Y \<subseteq> {0..<m}" and xy: "X\<union> Y = {0..<m}" by auto
  then have "card (X \<union> Y) = m" by auto
  thm card_Un_Int
  with empty(3) have cardXY: "card X + card Y = m" using card_Un_Int[OF empty(1) empty(2)] by auto

  
  from empty have ents: "\<forall>i<m. (i\<in>Y) = (i\<notin>X)" by auto

  have "(\<exists>! w. (\<forall>i\<in>X. w ! i) \<and> (\<forall>i\<in>Y. \<not> w ! i) \<and>  length w = m)"
  proof (rule ex1I, goal_cases)
    case 1
    show "(\<forall>i\<in>X. (witness X m) ! i) \<and> (\<forall>i\<in>Y. \<not> (witness X m) ! i) \<and> length (witness X m) = m"
    proof (safe, goal_cases)
      case (2 i)
      with y have a: "i < m" by auto
      with iswitness have "witness X m ! i = (i \<in> X)" by auto
      with a ents 2 have "~ witness X m ! i" by auto
      with 2(2) show "False" by auto
    next
      case (1 i)
      with x have a: "i < m" by auto
      with iswitness have "witness X m ! i = (i \<in> X)" by auto
      with a ents 1 show "witness X m ! i" by auto
    qed (rule witness_length)
  next
    case (2 w)
    show "w = witness X m"
    proof -
      have "(length w = length (witness X m) \<and> (\<forall>i<length w. w ! i = (witness X m) ! i))"
       using 2 apply(simp add: witness_length)
       proof 
        fix i 
        assume as: "(\<forall>i\<in>X. w ! i) \<and> (\<forall>i\<in>Y. \<not> w ! i) \<and>  length w = m"
        have "i < m \<longrightarrow> (witness X m) ! i = (i \<in> X)" using iswitness by auto
        then show "i < m \<longrightarrow> w ! i = (witness X m) ! i" using ents as by auto
       qed
      then show ?thesis using list_eq_iff_nth_eq by auto
    qed
  qed
  then obtain w where " {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i)  \<and> length xs = m}
         = { w }" using Nitpick.Ex1_unfold[where P="(\<lambda>xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i)  \<and> length xs = m)"]
         by auto

  then have "card {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i)  \<and> length xs = m} = card { w }" by auto
  also have "\<dots> = 1" by auto 
  also have "\<dots> = 2^(m - card X - card Y)" using cardXY by auto
  finally show ?case .
next
  case (insert e S)
  then have eX: "e \<notin> X" and eY: "e \<notin> Y"  by auto
  from insert(8) have "insert e S \<subseteq> {0..<m}" by auto
  then have ebetween0m: "e\<in>{0..<m}" by auto

  have fm: "finite {0..<m}" by auto
  have cardm: "card {0..<m} =   m" by auto
  from insert(8) eX eY ebetween0m have sub: "X \<union> Y \<subset> {0..<m}" by auto
  from insert have "card (X \<inter> Y) = 0" by auto
  then have cardXY: "card (X \<union> Y) = card X + card Y" using card_Un_Int[OF insert(4) insert(5)] by auto
  
  have "  m > card X + card Y" using psubset_card_mono[OF fm sub] cardm cardXY by(auto)
  then have carde: "1 + (  m - card X - card Y - 1) =   m - card X - card Y" by auto

  thm card_Un_Int
  have is1: "{xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> xs!e}
          = {xs. Ball (insert e X) (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m}" by auto
  have is2: "{xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> ~xs!e}
          = {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>(insert e Y). \<not> xs ! i) \<and> length xs =   m}" by auto
         
  thm bitstrings_finite fbool[where b="True", simplified]

  have 2: "{xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> xs!e}
        \<union> {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> ~xs!e}
          = {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m}" by auto

  have 3: "{xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> xs!e}
      \<inter> {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> ~xs!e} = {}" by auto

  have fX: "finite (insert e X)" 
    and disjeXY: "insert e X \<inter> Y = {}" 
    and cutX: "S \<inter> (insert e X \<union> Y) = {}"
    and uniX: "S \<union> insert e X \<union> Y = {0..<m}" using insert by auto
  have fY: "finite (insert e Y)"
    and disjXeY: "X \<inter> (insert e Y) = {}" 
    and cutY: "S \<inter> (X \<union> insert e Y) = {}"
    and uniY: "S \<union>  X \<union> insert e Y = {0..<m}" using insert by auto

  thm insert(3)
  have "card {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m}
      = card {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> xs!e}
        + card {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m \<and> ~xs!e}"
        apply(simp only: card_Un_Int[OF fbool[where b="True", simplified] fbool[where b="False", simplified]]) using 2 3 by auto
  also
  have "\<dots> = card {xs. Ball (insert e X) (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs =   m}
        + card {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>(insert e Y). \<not> xs ! i) \<and> length xs =   m}" by (simp only: is1 is2)
  
  also
  have "\<dots> = 2 ^ (  m - card (insert e X) - card Y)
        + 2 ^ (  m - card X - card (insert e Y))" 
          apply(simp only: insert(3)[of "insert e X" Y, OF fX insert(5) disjeXY cutX uniX])
          by(simp only: insert(3)[of "X" "insert e Y", OF insert(4) fY disjXeY cutY uniY])
  also
  have "\<dots> = 2 ^ (  m - card X - card Y - 1)
        + 2 ^ (  m - card X - card Y - 1)" using insert(4,5) eX eY by auto
  also
  have "\<dots> = 2 * 2 ^ (  m - card X - card Y - 1)"  by auto
  also have "\<dots> = 2 ^ (1 + (  m - card X - card Y - 1))" by auto
  also have "\<dots> = 2 ^ (  m - card X - card Y)" using carde by auto
  finally show ?case .
qed

thm card1
lemma card2: assumes "finite X" and "finite Y" and "X \<inter> Y = {}" and x: "X \<union> Y \<subseteq> {0..<m}"
  shows "card {xs. (\<forall>i\<in>X. xs ! i) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = m} = 2 ^ (m - card X - card Y)"
proof -
  let ?S = "{0..<m}-(X \<union> Y)"
  from x have a: "?S \<union> X \<union> Y = {0..<m}" by auto
  have b: "?S \<inter> (X \<union> Y) = {}" by auto  
  show ?thesis apply(rule card1[where ?S="?S"]) by(simp_all add: assms a b)
qed
 
subsection "average out the second sum for free-absch"
 
lemma Expactation2or1: "finite S \<Longrightarrow> finite Tr \<Longrightarrow> finite Fa \<Longrightarrow> card Tr + card Fa + card S \<le> l \<Longrightarrow>
  S \<inter> (Tr \<union> Fa) = {} \<Longrightarrow> Tr \<inter> Fa = {} \<Longrightarrow> S \<union> Tr \<union> Fa \<subseteq> {0..<l} \<Longrightarrow>
  (\<Sum>x\<in>{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. \<Sum>j\<in>S. if x ! j then 2 else 1)
      = 3 / 2 * real (card S) * 2 ^ (l - card Tr - card Fa)"
proof (induct arbitrary: Tr Fa rule: finite_induct)
  case (insert e S)
  have myhelp: "1 + real (card S) = real (1 + card S)" by auto

  thm insert

  from insert(7) have "e \<in> (insert e S)" and eTr: "e \<notin> Tr" and eFa: "e \<notin> Fa" by auto (* wenn ein element drin ist, dann nimm mal eins davon *)
  
  from insert(9) have  tra: "Tr \<subseteq> {0..<l}" and trb: "Fa \<subseteq> {0..<l}" and  trc: "e < l" by auto

  from insert have ja: "S \<inter> (insert e Tr \<union> Fa) = {}" by auto
  from insert have ji: "(insert e Tr \<inter> Fa) = {}" by auto
  from insert have jp: "S \<union> insert e Tr \<union> Fa \<subseteq> {0..<l}" by auto
  from insert have jo: "finite (insert e Tr)" by auto
  from insert have je: "l \<ge> (card (insert e Tr) + card Fa + card S)" by auto
  from insert have ja2: "S \<inter> (Tr \<union> insert e Fa) = {}" by auto
  from insert have ji2: "(Tr \<inter> insert e Fa) = {}" by auto
  from insert have jo2: "finite (insert e Fa)" by auto
  from insert have je2: "l \<ge> (card Tr + card (insert e Fa) + card S)" by auto
  from insert have jp2: "S \<union> Tr \<union> insert e Fa \<subseteq> {0..<l}" by auto

  have ntrFa: "l > (card Tr + card Fa)" using insert(6) card_insert_if insert(1,2) by auto

  have myhelp2: "1 + (l - card Tr - card Fa -1) = l - card Tr - card Fa" using ntrFa by auto
 
  (* have myhelp3: "(2::real) * 2^m + 1 * 2^m = (2+1)* 2^m" by simp *)

  have juhuTr: "{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l \<and> xs!e}  
      = {xs. (\<forall>i\<in>(insert e Tr). xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}"
       using eTr by auto
  have juhuFa: "{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l \<and> ~xs!e}  
      = {xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}"
       using eTr by auto

  thm card2[of "(insert e Tr)" Fa l']
  have "card {xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l} =
2 ^ (l - card (insert e Tr) - card Fa)"
          apply(rule card2[of "(insert e Tr)" Fa l])
            by(simp_all add: insert eFa tra trb trc)

            term "setsum"
  thm setsum_constant
  then have resi: "card {xs.  Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l} = 2^(l - card Tr - card Fa - 1)" using insert(4) eTr by auto
  
  term "of_nat"
  have "(\<Sum>x\<in>{xs.  Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. 2::real) = of_nat (card {xs.  Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}) * 2"  by(rule setsum_constant) 
  also have "\<dots> = of_nat (2^(l - card Tr - card Fa - 1)) * 2" using resi by auto
  also have "\<dots> = 2 * 2^(l - card Tr - card Fa - 1)" by (simp add: of_nat_power power_commutes)
  finally have yabaTr: " (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. 2::real) =
2 * 2 ^ (l - card Tr - card Fa - 1)" . 

  have "card {xs. Ball (Tr) (op ! xs) \<and> (\<forall>i\<in>insert e Fa. \<not> xs ! i) \<and> length xs = l} =
2 ^ (l - card Tr - card (insert e Fa))"
          apply(rule card2[of Tr "insert e Fa" l])
            by (simp_all add: insert eTr tra trb trc)
  then have resi2: "card {xs.  Ball (Tr) (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l} = 2^(l - card Tr - card Fa - 1)" using insert(5) eFa by auto
  have "(\<Sum>x\<in>{xs.  Ball Tr (op ! xs) \<and> (\<forall>i\<in>insert e Fa. \<not> xs ! i) \<and> length xs = l}. 1::real) = of_nat (card {xs.  Ball Tr (op ! xs) \<and> (\<forall>i\<in>insert e Fa. \<not> xs ! i) \<and> length xs = l}) * 1"  by(rule setsum_constant) 
  also have "\<dots> = of_nat (2^(l - card Tr - card Fa - 1)) * 1" using resi2 by auto
  also have "\<dots> = 1 * 2^(l - card Tr - card Fa - 1)" by (simp add: of_nat_power power_commutes)
  finally have yabaFa: "(\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>insert e Fa. \<not> xs ! i) \<and> length xs = l}. 1::real) = 1 * 2 ^ (l - card Tr - card Fa - 1)"
  . 
                                                                    
  term "setsum"
  note fTrue=fbool[where e="e" and m="l" and X="Tr" and Y="Fa" and  b="True", simplified]
  note fFalse=fbool[where e="e" and m="l" and X="Tr" and Y="Fa" and b="False", simplified]
  thm setsum_Un[OF fTrue fFalse]

  {
      fix X Y
      have "{xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = l \<and> xs!e}
        \<union> {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = l \<and> ~xs!e}
          = {xs. Ball X (op ! xs) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = l}" by auto
  } note 2=this
  { fix X Y
      have "{xs. (\<forall>i\<in>X. xs ! i) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = l \<and> xs!e}
          \<inter> {xs. (\<forall>i\<in>X. xs ! i) \<and> (\<forall>i\<in>Y. \<not> xs ! i) \<and> length xs = l \<and> ~xs!e} = {}" by auto
  } note 3=this

  {
     fix x::"nat"
     have "x - 0 = x" by auto
  } note bla=this

  (* split it! *)
  have "(\<Sum>x\<in>{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. \<Sum>j\<in>(insert e S). if x ! j then (2::real) else 1)
      = (\<Sum>x\<in>{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l \<and> xs!e}. \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)
        + (\<Sum>x\<in>{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l \<and> ~xs!e}. \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)" 
        proof -
          let ?all="{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}"
          let ?allT="{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l \<and> xs!e}"
          let ?allF="{xs. (\<forall>i\<in>Tr. xs ! i) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l \<and> ~xs!e}"
          have "(\<Sum>x\<in>?all. \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)
            = (\<Sum>x\<in>(?allT \<union> ?allF). \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)" using 2 by auto
          thm setsum_Un[OF fTrue fFalse]
          also have"\<dots> = ((\<Sum>x\<in>(?allT). \<Sum>j\<in>(insert e S). if x ! j then (2::real) else 1) 
                      + (\<Sum>x\<in>(?allF). \<Sum>j\<in>(insert e S). if x ! j then (2::real) else 1))
                      - (\<Sum>x\<in>(?allT \<inter> ?allF). \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)" 
                   by(simp add: setsum_Un[OF fTrue fFalse])
          also have "\<dots> =  (\<Sum>x\<in>(?allT). \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)
                        + (\<Sum>x\<in>(?allF). \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)"
                by(simp add: 3) 
          finally show ?thesis .
        qed 
  also 
  have "\<dots> = (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)
        + (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. \<Sum>j\<in>(insert e S). if x ! j then 2 else 1)" 
       using juhuTr juhuFa by auto
  also 
  have "\<dots> =  (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. (if x ! e then 2 else 1) + (\<Sum>j\<in>S. if x ! j then 2 else 1))
        + (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (if x ! e then 2 else 1) + (\<Sum>j\<in>S. if x ! j then 2 else 1))" 
        using insert(1,2) by auto
  also
  have "\<dots> =  (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. (\<lambda>x. 2) x + (\<lambda>x. (\<Sum>j\<in>S. if x ! j then 2 else 1)) x)
        + (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (\<lambda>x. 1) x + (\<lambda>x. (\<Sum>j\<in>S. if x ! j then 2 else 1)) x)" 
        by auto
  also
  have "\<dots> =  (\<Sum>x\<in>{xs.  Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. 2) +
          (\<Sum>x\<in>{xs.  Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1))
        + ((\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. 1) +
          (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1)))"
          by (simp only: Groups_Big.comm_monoid_add_class.setsum.distrib)
  also
  have "\<dots> =  2 * 2^(l - card Tr - card Fa - 1) +
          (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1))
        + (1 * 2^(l - card Tr - card Fa - 1) +
          (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1)))" 
        by(simp only: yabaTr yabaFa)
  also
  have "\<dots> =  (2::real) * 2^(l - card Tr - card Fa - 1) +
          (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1))
        + (1::real) * 2^(l - card Tr - card Fa - 1) +
          (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1))" 
        by auto
  also          
  have "\<dots> =  (3::real) * 2^(l - card Tr - card Fa - 1) +
          (\<Sum>x\<in>{xs. Ball (insert e Tr) (op ! xs) \<and> (\<forall>i\<in>Fa. \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1)) +
          (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1))" 
        by simp
  thm insert(3)[of "insert e Tr" Fa, OF jo insert(5) je ja ji jp]
  also
  have "\<dots> =  3 * 2^(l - card Tr - card Fa - 1) +
          3 / 2 * real (card S) * 2 ^ (l - card (insert e Tr) - card Fa) +
          (\<Sum>x\<in>{xs. Ball Tr (op ! xs) \<and> (\<forall>i\<in>(insert e Fa). \<not> xs ! i) \<and> length xs = l}. (\<Sum>j\<in>S. if x ! j then 2 else 1))" 
        using insert(3)[of "insert e Tr" Fa, OF jo insert(5) je ja ji jp] by simp 
  also
  have "\<dots> =  3 * 2^(l - card Tr - card Fa - 1) +
          3 / 2 * real (card S) * 2 ^ (l - card (insert e Tr) - card Fa) +
           3 / 2 * real (card S) * 2 ^ (l - card Tr - card (insert e Fa))"
        using insert(3)[of "Tr" "insert e Fa", OF insert(4) jo2 je2 ja2 ji2 jp2] by simp
  also
  have "\<dots> =  3 * 2^(l - card Tr - card Fa - 1) +
          3 / 2 * real (card S) * 2^ (l - (card Tr + 1) - card Fa) +
           3 / 2 * real (card S) * 2^ (l - card Tr - (card Fa + 1))" using card_insert_if insert(4,5) eTr eFa by auto
  also
  have "\<dots> =  3  * 2^(l - card Tr - card Fa - 1) +
          3 / 2 * real (card S) * 2^ (l - card Tr - card Fa - 1) +
           3 / 2 * real (card S) * 2^ (l - card Tr - card Fa - 1)" by auto
  also
  have "\<dots> =  3  * 2^(l - card Tr - card Fa - 1) +
          2 *  3 / 2 * real (card S) * 2^ (l - card Tr - card Fa - 1)" by algebra
  also
  have "\<dots> =  ( 3/2 * 2  +  2 *  3 / 2 * real (card S)) * 2^ (l - card Tr - card Fa - 1)" by algebra
  also
  have "\<dots> =  (   3 / 2 * (1 + real (card S))) * 2 * 2^ (l - card Tr - card Fa - 1 )" by simp 
  also
  have "\<dots> =  (   3 / 2 * (1 + real (card S))) * 2^ (Suc (l - card Tr - card Fa -1 ))" by simp
  also
  have "\<dots> =  (   3 / 2 * (1 + real (card S))) * 2^ (1 + (l - card Tr - card Fa -1))" by simp
  also
  have "\<dots> =  (   3 / 2 * (1 + real (card S))) * 2^ (l - card Tr - card Fa )" using myhelp2 by auto
  also
  have "\<dots> =  (   3 / 2 * (real (1 + card S))) * 2^ (l - card Tr - card Fa )" by(simp only: myhelp)
  also
  have "\<dots> =  (   3 / 2 * real (card (insert e S))) * 2^ (l - card Tr - card Fa)" using insert(1,2) by auto
  finally show ?case  .
qed auto




end
