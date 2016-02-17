theory MTF_2comp_on2
imports 
Phase_Partitioning
Partial_Cost_Model
begin




subsection "taken from MTF.thy"


 
lemma MTF_internal_state: "snd (config\<^sub>p MTF init xs) = ()" by simp

definition s_mtf :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "s_mtf n init qs = fst (config MTF init (take n qs))"  
 
lemma [simp]: "s_mtf 0 init qs = init" unfolding s_mtf_def by(simp)

lemma s_mtf_Suc[simp]: "n<length qs \<Longrightarrow> s_mtf (Suc n) init qs = mtf2 (length (s_mtf n init qs) - 1) (qs!n) (s_mtf n init qs)"
by (simp add: s_mtf_def take_Suc_conv_app_nth config'_append2 MTF_def Step_def step_def) 
 

lemma s_mtf_append: "i\<le>length xs \<Longrightarrow> s_mtf i init xs = s_mtf i init (xs@ys)"
  by(simp add: s_mtf_def take_Suc_conv_app_nth) 

lemma s_mtf_append2: "s_mtf (length xs + i) init (xs @ ys) = s_mtf i (s_mtf (length xs) init xs) ys"
proof(induct i)
  case 0
  show ?case using s_mtf_def  s_mtf_append by simp
next
  case (Suc i)
  then show ?case apply (simp add: take_Suc_conv_app_nth) sorry
qed

 
definition t_mtf where
"t_mtf n init qs = index (s_mtf n init qs) (qs!n)"

term "T_on_n"
lemma t_mtf_eq: "t_mtf n init qs = T_on_n MTF init qs n" 
unfolding t_mtf_def by(simp add: s_mtf_def  t\<^sub>p_def MTF_def) 



definition T_mtf :: "nat\<Rightarrow>nat list\<Rightarrow>nat list\<Rightarrow>nat" where
"T_mtf n init qs = (\<Sum>i<n. t_mtf i init qs)"

lemma T_mtf_eq: "T_mtf (length qs) init qs = T_on MTF init qs"
unfolding T_mtf_def T_on_as_sum using t_mtf_eq by auto 


lemma splitSum: " (\<Sum>i<a + b. (f::nat\<Rightarrow>nat) i) = (\<Sum>i<a. f i) +  (\<Sum>i = a..<a + b. f i)"
apply(induct b) by simp_all

lemma myreindex: "(\<Sum>i = (a::nat)..<a + b. f (i-a)) = (\<Sum>i<b. f i)"
proof -
  have A: "(\<lambda>(i::nat). i+a) ` {..<b} =  {a..<a+b}"
      unfolding image_def
      proof (safe)
        case goal2
        then have x_ge_a: "x\<ge>a" and x_le_ab: "x<a+b" by auto
        show ?case
        proof 
          show "x = (x-a)+a" using x_ge_a by(simp)
          show "x-a : {..<b}" using x_ge_a x_le_ab by(simp)
      qed
  qed simp 
  have "(\<Sum>i = a..<a + b. f (i-a)) = setsum (\<lambda>i. f(i-a)) ((\<lambda>i. i+a) ` {..<b})"
      using A by auto
  also have "\<dots> = setsum ((\<lambda>i. f(i-a)) \<circ> (\<lambda>i. i+a)) {..<b}" 
    apply(rule setsum.reindex)
      by(simp)
  finally show ?thesis by simp
qed



lemma splitquerylist: "T\<^sub>p_on MTF init (xs@ys) 
     = T\<^sub>p_on MTF init xs + T\<^sub>p_on MTF (s_mtf (length xs) init xs) ys " 
proof -
  thm nth_append s_mtf_append

  have "(\<Sum>i<length (xs @ ys). index (s_mtf i init (xs @ ys)) ((xs @ ys) ! i)) =
    (\<Sum>i<length xs + length ys. (if i<length xs
                  then index (s_mtf i init (xs @ ys)) ((xs @ ys) ! i)
                  else index (s_mtf i init (xs @ ys)) ((xs @ ys) ! i)))" by auto
  also have "\<dots> = 
    (\<Sum>i<length xs + length ys. (if i<length xs
                  then index (s_mtf i init xs) (xs ! i)
                  else index (s_mtf (length xs + (i - length xs)) init (xs @ ys)) (ys ! (i - length xs))))"
     apply(rule setsum.cong)
        apply(simp)
        by(simp add: nth_append s_mtf_append[symmetric])
  thm s_mtf_append2
  also have "\<dots> = 
    (\<Sum>i\<in>{..<length xs + length ys}. (if i<length xs
                  then index (s_mtf i init xs) (xs ! i)
                  else index (s_mtf (i - length xs) (s_mtf (length xs) init xs) ys) (ys ! (i - length xs))))" 
     apply(rule setsum.cong)
        apply(simp)
        by(simp only: s_mtf_append2)
   also have "\<dots> = 
    (\<Sum>i\<in>{..<length xs}. (if i<length xs
                  then index (s_mtf i init xs) (xs ! i)
                  else index (s_mtf (i - length xs) (s_mtf (length xs) init xs) ys) (ys ! (i - length xs))))
    + (\<Sum>i\<in>{length xs..<length xs + length ys}. (if i<length xs
                  then index (s_mtf i init xs) (xs ! i)
                  else index (s_mtf (i - length xs) (s_mtf (length xs) init xs) ys) (ys ! (i - length xs))))"
            by(rule splitSum)
   also have "\<dots> = 
    (\<Sum>i<length xs. index (s_mtf i init xs) (xs ! i)) +
    (\<Sum>i<length ys. index (s_mtf i (s_mtf (length xs) init xs) ys) (ys ! i))"
    using myreindex[of "(%i. index (s_mtf i (s_mtf (length xs) init xs) ys) (ys ! i))" "length xs" "length ys"]
    by(simp)
   finally show ?thesis 
      unfolding T_mtf_eq[symmetric] T_mtf_def t_mtf_def by auto
qed


subsection "now the proof"
 
lemma MTF_config: "i\<le>length \<sigma> \<Longrightarrow> s_mtf i [x,y] \<sigma> \<in> {[x,y],[y,x]}" 
proof(induct i)
  case (Suc i)
  then show ?case
  apply(cases "s_mtf i [x, y] \<sigma> = [x, y]")
    by(simp_all add: mtf2_def swap_def)
qed (simp add: s_mtf_def)


subsubsection "go through the four phase types"



lemma mtf_yx: "x \<noteq> y \<Longrightarrow> qs \<in> lang (Star(Times (Atom y) (Atom x)))
       \<Longrightarrow> T_mtf (length (qs@r)) [x,y] (qs@r) = length qs + T_mtf (length r) [x,y] r  "
proof -
  case goal1
  then have "qs \<in> star ({[y]} @@ {[x]})" by (simp)
  from this goal1 show ?case
  proof (induct qs rule: star_induct)
    case (append u v)
    then have uyx: "u = [y,x]" by auto 
     
    have yy: "T_mtf (length (v@r)) [x,y] (v @ r) = length v + T_mtf (length r) [x, y] r"
        apply(rule append(3)) 
          apply(fact) 
          using append(2) by(simp)

    have s0: "s_mtf 0 [x, y] [y, x] = [x,y]" by (simp)
    then have s1: "s_mtf (Suc 0) [x, y] [y, x] = [y,x]" by (simp add: mtf2_def swap_def)
    then have s2: "s_mtf (length u) [x, y] u  = [x,y]" 
      unfolding uyx by (simp add: mtf2_def swap_def)
      
    have ta: "T_mtf (length u) [x, y] u = 2"
        unfolding T_mtf_def uyx apply(simp) unfolding t_mtf_def
        unfolding s0 s1 using goal1(1) by (simp)          

    thm splitquerylist
    have "T_mtf (length (u@v@r)) [x, y]((u @ v) @ r) = T_mtf (length (u@(v@r))) [x, y] (u @ (v @ r))"
        by auto
    also have "\<dots>
        = T_mtf (length u) [x, y] u + T_mtf (length (v@r)) (s_mtf (length u) [x,y] u) (v @ r)"
       using splitquerylist[unfolded T_mtf_eq[symmetric], of u "v@r" "[x,y]"] by auto 
    also have "\<dots> = T_mtf (length u) [x, y] u + T_mtf (length (v@r)) [x,y] (v @ r)"
      by(simp only: s2) 
    also have "\<dots> = T_mtf (length u) [x, y] u + length v + T_mtf (length r) [x, y]  r" by(simp only: yy) 
    also have "\<dots> = 2 + length v + T_mtf (length r) [x, y]  r" by(simp only: ta) 
    also have "\<dots> = length (u @ v) + T_mtf (length r) [x, y]  r" using uyx by auto 
    finally show ?case by simp
  qed simp
qed

lemma mtf_yxyx: "x \<noteq> y
       \<Longrightarrow> qs \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
       \<Longrightarrow> T_mtf (length (qs@r)) [x,y] (qs@r) = length qs + T_mtf (length r) [x,y] r"
proof -
  case goal1
  obtain u v where uu: "u \<in> lang (Times (Atom y) (Atom x))"
                      and vv: "v \<in> lang (seq[ Star(Times (Atom y) (Atom x))])"
                      and qsuv: "qs = u @ v" 
                      using goal1(2)
                      by (auto simp: conc_def)  
  from uu have uyx: "u = [y,x]" by(auto)

  from qsuv uyx have vqs: "length v = length qs - 2" by auto
  from qsuv uyx  have vqs2: "length v + 2 = length qs" by auto

  
  have s0: "s_mtf 0 [x, y] [y, x] = [x,y]" by (simp)
  then have s1: "s_mtf (Suc 0) [x, y] [y, x] = [y,x]"  by(simp add: mtf2_def swap_def)
  then have s2: "s_mtf (length u) [x, y] u = [x,y]" unfolding uyx by(simp add: mtf2_def swap_def) 
     
    have ta: "T_mtf (length u) [x, y] u = 2"
      unfolding T_mtf_def uyx apply(simp) unfolding t_mtf_def
      unfolding s0 s1 using goal1(1) by (simp)

      (* instead of TS_b1 use TS_yx *)
      thm mtf_yx

   
    have tat: "T_mtf (length (v@r)) [x,y] (v@r) =  length v + T_mtf (length r) [x, y] r" 
        apply(rule mtf_yx)
      apply(fact)
      using vv by(simp)
 
 
  thm splitquerylist[unfolded T_mtf_eq[symmetric]]
  have "T_mtf (length (qs@r)) [x, y] (qs@r) = T_mtf (length (u@(v@r))) [x, y] (u @ (v @ r))"
    using qsuv  by auto
  also have "\<dots>
      = T_mtf (length u) [x, y] u + T_mtf (length (v@r)) (s_mtf (length u) [x,y] u) (v @ r)"
     using  splitquerylist[unfolded T_mtf_eq[symmetric], of u "v@r" "[x,y]"]
     by auto 
  also have "\<dots> = T_mtf (length u) [x, y] u + T_mtf (length (v@r)) [x,y] (v@r)"
    by(simp only: s2) 
  also have "\<dots> = T_mtf (length u) [x, y] u + length v + T_mtf (length r) [x, y] r"
      by (simp only: tat) 
  also have "\<dots> = 2 + length v + T_mtf (length r) [x, y] r" by(simp only: ta) 
  also have "\<dots> = length qs + T_mtf (length r) [x, y] r" using vqs2 by auto
  finally show ?case .                         
qed




lemma mtf_a: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y \<Longrightarrow>
  qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y]) \<Longrightarrow>
   T\<^sub>p_on MTF [x,y] qs  \<le> 2 * T\<^sub>p [x,y] qs (OPT2 qs [x,y]) "
unfolding T_mtf_eq[symmetric] T_mtf_def
  using OPT2_A
  by (auto simp add: conc_def t_mtf_def mtf2_def swap_def mtf_def step_def t\<^sub>p_def)



lemma mtf_b: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y 
    \<Longrightarrow> qs \<in> lang (seq[Plus (Atom x) One, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom y, Atom y])
       \<Longrightarrow> T\<^sub>p_on MTF [x,y] qs  \<le> 2 * T\<^sub>p [x,y]  qs (OPT2 qs [x,y]) "
proof -
  case goal1
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
        and qsuv: "qs = u @ v" 
        using goal1
        by (auto simp: conc_def) 
  from vv have lenvmod: "length v mod 2 = 0" apply(simp)
  proof -
    assume "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}"
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[y]} @@ {[y]}" by (metis concE)
    then have "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length v = 4+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show "length v mod 2 = 0" by auto
  qed
        
  from uu have setux: "set u \<subseteq> {x}" using atoms_lang by fastforce
 
   
  thm mtf_yxyx

  have T_prefix: "T_mtf (length u) [x, y] u = 0"
      unfolding T_mtf_def t_mtf_def using uu by auto 

  have s_prefix: "s_mtf (length u) [x,y] u = [x,y]"
    using uu by(auto simp: mtf2_def swap_def)
 
  from vv have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom y, Atom y])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom y, Atom y])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[y,y]" by auto
  from aa have lena: "length a > 0" by auto
 
  from mtf_yxyx goal1(2) aa have stars: "T_mtf (length (a@b)) [x, y] (a @ b) =
    length a + T_mtf (length b) [x, y] b"  by auto

  have "T_mtf (length b) [x, y] b = 1"
    unfolding bb T_mtf_def t_mtf_def using goal1(2) by(auto simp: mtf2_def swap_def)  
 
  with stars have "T_mtf (length (a@b)) [x, y]  (a @ b) = length a + 1" by auto
  then have whatineed: "T_mtf (length v) [x, y]  v = (length v - 1)" using vab bb by auto

  have "T_mtf (length qs) [x, y] qs = T_mtf (length (u@v)) [x, y] (u @ v)"
    using qsuv by auto
  also have "\<dots>
      = T_mtf (length u) [x, y] u + T_mtf (length v) (s_mtf (length u) [x,y] u) v"
      using splitquerylist[unfolded T_mtf_eq[symmetric], of u v "[x,y]"] by auto
  also have "\<dots>
      = T_mtf (length u) [x, y] u + T_mtf (length v) [x,y] v" by(simp add: s_prefix)
  also have "\<dots> = T_mtf (length u) [x, y] u + (length v - 1)" by (simp only: whatineed)
  also have "\<dots> = (length v - 1)" by (simp add: T_prefix)
  finally have MTF: "T_mtf (length qs) [x,y] qs = (length v - 1)" .

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom y, Atom y])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_B) by(fact)+

  show ?case unfolding T_mtf_eq[symmetric]   MTF OPT by auto
qed


lemma mtf_c: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y \<Longrightarrow>
  qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x])
  \<Longrightarrow> T\<^sub>p_on MTF [x,y] qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
proof -
  case goal1
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
        and qsuv: "qs = u @ v" 
        using goal1
        by (auto simp: conc_def) 
  from vv have lenvmod: "length v mod 2 = 1" apply(simp)
  proof -
    assume "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}"
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in> {[x]}" by (metis concE)
    then have "p = [y,x]" "r=[x]" by auto
    with pqr have a: "length v = 3+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show "length v mod 2 = Suc 0" by auto
  qed
        
  from uu have setux: "set u \<subseteq> {x}" using atoms_lang by fastforce
 
   
  thm mtf_yxyx

  have T_prefix: "T_mtf (length u) [x, y] u = 0"
      unfolding T_mtf_def t_mtf_def using uu by auto 

  have s_prefix: "s_mtf (length u) [x,y] u = [x,y]"
    using uu by(auto simp: mtf2_def swap_def)
 
  from vv have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom x])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom x])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[x]" by auto
  from aa have lena: "length a > 0" by auto
 
  from mtf_yxyx goal1(2) aa have stars: "T_mtf (length (a@b)) [x, y] (a @ b) =
    length a + T_mtf (length b) [x, y] b"  by auto

  have "T_mtf (length b) [x, y] b = 0"
    unfolding bb 
      unfolding T_mtf_def t_mtf_def using uu by auto  
 
  with stars have "T_mtf (length (a@b)) [x, y]  (a @ b) = length a" by auto
  then have whatineed: "T_mtf (length v) [x, y]  v = (length v - 1)" using vab bb by auto

  have "T_mtf (length qs) [x, y] qs = T_mtf (length (u@v)) [x, y] (u @ v)"
    using qsuv by auto
  also have "\<dots>
      = T_mtf (length u) [x, y] u + T_mtf (length v) (s_mtf (length u) [x,y] u) v"
      using splitquerylist[unfolded T_mtf_eq[symmetric], of u v "[x,y]"] by auto
  also have "\<dots>
      = T_mtf (length u) [x, y] u + T_mtf (length v) [x,y] v" by(simp add: s_prefix)
  also have "\<dots> = T_mtf (length u) [x, y] u + (length v - 1)" by (simp only: whatineed)
  also have "\<dots> = (length v - 1)" by (simp add: T_prefix)
  finally have MTF: "T_mtf (length qs) [x,y] qs = (length v - 1)" .

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom x])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_C) by(fact)+

  show ?case unfolding T_mtf_eq[symmetric] MTF OPT by auto
qed



lemma mtf_d: "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow> 
    qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow>
    T\<^sub>p_on MTF [x,y] qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
unfolding T_mtf_eq[symmetric]
by(auto simp add: conc_def T_mtf_def t_mtf_def mtf2_def swap_def)


lemma D: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y \<Longrightarrow>  
      T\<^sub>p_on MTF [x,y] qs  \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
apply(rule LxxI[where P="(\<lambda>x y qs.  T\<^sub>p_on MTF  [x,y] qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]))"])
  apply(fact mtf_d)
  apply(fact mtf_b)
  apply(fact mtf_c)
  apply(fact mtf_a)
  by (simp)





theorem MTF_OPT2: "(x::nat) \<noteq> y \<Longrightarrow> set \<sigma> \<subseteq> {x,y}
     \<Longrightarrow> T\<^sub>p_on MTF [x,y] \<sigma>  \<le> 2 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
 proof (induction "length \<sigma>" arbitrary: \<sigma> x y rule: less_induct)
  case (less \<sigma>)
  show ?case
  proof (cases "\<exists>xs ys. \<sigma>=xs@ys \<and> xs \<in> Lxx x y")
    case True
    then obtain xs ys where qs: "\<sigma>=xs@ys" and xsLxx: "xs \<in> Lxx x y" by auto

    with Lxx1 have len: "length ys < length \<sigma>" by fastforce
    from qs(1) less(3) have ysxy: "set ys \<subseteq> {x,y}" by auto

    have xsset: "set xs \<subseteq> {x, y}" using less(3) qs by auto
    from xsLxx Lxx1 have "length xs \<ge> 2" by auto
    then have xs_not_Nil: "xs \<noteq> []" by auto

    from D[OF xsLxx less(2) ]
      have D1: "T\<^sub>p_on MTF  [x,y] xs \<le> 2 * T\<^sub>p [x, y] xs (OPT2 xs [x, y])"  by auto

    have it: "s_mtf (length xs) [x,y] xs \<in> {[x,y],[y,x]}" using MTF_config by auto

    with less(2) obtain x' y' where config': "(s_mtf (length xs) [x, y] xs) = [x',y']"
                  and  xy': "x'\<in>{x,y}" "y'\<in>{x,y}" "x'\<noteq>y'" by auto

                  thm ccontr
    have lastisx': "x' = last xs"
    proof (rule ccontr)
      assume contra: "x' \<noteq> last xs"
      from xs_not_Nil have "last xs \<in> set xs" by auto
      with xsset have "last xs \<in> {x,y}" by auto
      with xy' have "last xs \<in> {x',y'}" by auto
      with contra have "last xs = y'" by auto
      with xs_not_Nil have A: "xs = butlast xs @ [y']" by auto
      from xy' have C: "{[x,y],[y,x]} = {[x',y'],[y',x']}" by auto 
      have "s_mtf (length (butlast xs)) [x,y] (butlast xs) \<in> {[x,y],[y,x]}"
        using MTF_config by auto 
        thm s_mtf_append
      then have it': "s_mtf (length (butlast xs)) [x,y] (butlast xs @ [y']) \<in> {[x',y'],[y',x']}"
        unfolding C  by(simp only: s_mtf_append[symmetric])
      have B: "((butlast xs @ [y']) ! (length xs - 1)) = y'"
        apply(simp only:  length_butlast[symmetric])
        apply(simp only:  nth_append_length_plus[where n=0, simplified]) by auto

      have "(s_mtf (length (butlast xs @ [y'])) [x, y] (butlast xs @ [y'])) = [y',x']"
        apply(cases "s_mtf (length (butlast xs)) [x,y] (butlast xs @ [y']) = [x',y']")
          apply(simp) unfolding B[simplified] apply(simp add: mtf2_def swap_def)
          using it' xy'(3) apply(auto) unfolding B[simplified] by(simp add: mtf2_def swap_def)
       from this[unfolded A[symmetric]] config' xy'(3) show "False" by auto
    qed

    from Lxx_ends_in_two_equal xsLxx obtain pref e where "xs = pref @ [e,e]" by metis
    then have "xs =  pref@[last xs, last xs]" by auto
    then have "xs = pref@[x', x']" using lastisx' by auto
    then have it3: "xs =  pref@[hd [x',y'], hd [x',y']]" by auto


    have ys': "set ys \<subseteq> {x', y'}"  using ysxy xy' by blast

    from len have c: "T\<^sub>p_on MTF [x', y'] ys \<le> 2 * T\<^sub>p [x', y'] ys (OPT2 ys [x', y']) + 2"       
            apply(rule less(1))
              by(fact)+ 

    have well: "T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + T\<^sub>p [x',y'] ys (OPT2 ys [x',y'])
        = T\<^sub>p [x, y] (xs @ ys) (OPT2 (xs @ ys) [x, y])"
          apply(rule OPTauseinander[where pref=pref])
            apply(fact)
            using less(3) qs apply(simp)
            using less(3) qs apply(simp)
            using xy' less(2) apply(cases "x=x'") apply(simp)+
            apply(fact lastisx')
            by(fact it3)
            
  

    have E0: " T\<^sub>p_on MTF  [x,y] \<sigma>
          =  T\<^sub>p_on MTF  [x,y] (xs@ys)" using qs by auto


    also have E1: "\<dots> = T\<^sub>p_on MTF  [x,y] xs + T\<^sub>p_on MTF  (s_mtf (length xs) [x, y] xs) ys"
        by (rule splitquerylist)
    also have E2: "\<dots> \<le> T\<^sub>p_on MTF [x,y] xs + 2 * T\<^sub>p [x', y'] ys (OPT2 ys [x', y']) + 2"
      unfolding config'
        using c by simp
    also have E3: "\<dots> \<le> 2 * T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + 2 * T\<^sub>p [x', y'] ys (OPT2 ys [x', y']) + 2"
        using D1 by simp
        
    also have "\<dots> \<le> 2 * (T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p [x', y'] ys (OPT2 ys [x', y'])) + 2"
        by(auto)
    also have  "\<dots> = 2 * (T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])) + 2"
      using well by auto 
    also have E4: "\<dots> = 2 * (T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y])) + 2"
        using qs by auto
    finally show ?thesis .
 

  next
    case False
    note f1=this
    from Lxx_othercase[OF less(3) this, unfolded hideit_def] have
        nodouble: "\<sigma> = [] \<or> \<sigma> \<in> lang (nodouble x y)" by  auto
    show ?thesis
    proof (cases "\<sigma> = []")
      case True
      then show ?thesis  by(simp)
    next
      case False
      (* with padding *)
      from False nodouble have qsnodouble: "\<sigma> \<in> lang (nodouble x y)" by auto
      let ?padded = "pad \<sigma> x y"
      from False pad_adds2[of \<sigma> x y] less(3) obtain addum where ui: "pad \<sigma> x y = \<sigma> @ [last \<sigma>]" by auto
      from nodouble_padded[OF False qsnodouble] have pLxx: "?padded \<in> Lxx x y" .

      have E0: "T\<^sub>p_on MTF [x, y] \<sigma>  \<le> T\<^sub>p_on MTF [x, y] ?padded "
      proof -
        thm splitquerylist
        have "T\<^sub>p_on MTF [x, y] ?padded = T\<^sub>p_on MTF [x, y] \<sigma>  + T\<^sub>p_on MTF (s_mtf (length \<sigma>) [x, y] \<sigma>) [last \<sigma>]"
          unfolding ui(1) using splitquerylist by auto
        also have "\<dots> \<ge> T\<^sub>p_on MTF [x, y] \<sigma>" unfolding MTF_def by auto
        finally show ?thesis by auto
      qed  

      thm D[OF pLxx less(2) ]
      also from pLxx have E1: "\<dots> \<le> 2 * T\<^sub>p [x,y] ?padded (OPT2 ?padded [x,y])"
        using D[OF pLxx less(2) ] by simp
      also have E2: "\<dots> \<le> 2 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
      proof -
        from False less(2) obtain \<sigma>' x' y' where qs': "\<sigma> = \<sigma>' @ [x']" and x': "x' = last \<sigma>" "y'\<noteq>x'" "y' \<in>{x,y}" 
            by (metis append_butlast_last_id insert_iff)
        have tla: "last \<sigma> \<in> {x,y}" using less(3) False last_in_set by blast
        with x' have grgr: "{x,y} = {x',y'}" by auto
        then have "(x = x' \<and> y = y') \<or> (x = y' \<and> y = x')" using less(2) by auto
        then have tts: "[x, y] \<in> {[x', y'], [y', x']}" by blast
        
        from qs' ui have pd: "?padded = \<sigma>' @ [x', x']" by auto 

        have "T\<^sub>p [x,y] (?padded) (OPT2 (?padded) [x,y])
              = T\<^sub>p [x,y] (\<sigma>' @ [x', x']) (OPT2 (\<sigma>' @ [x', x']) [x,y])"
                unfolding pd by simp
        also have gr: "\<dots>
            \<le> T\<^sub>p [x,y] (\<sigma>' @ [x']) (OPT2 (\<sigma>' @ [x']) [x,y]) + 1"
              apply(rule OPT2_padded[where x="x'" and y="y'"])
                apply(fact)
                using grgr qs' less(3) by auto
        also have "\<dots> \<le> T\<^sub>p [x,y] (\<sigma>) (OPT2 (\<sigma>) [x,y]) + 1" 
              unfolding qs' by simp
        finally show ?thesis by auto
      qed
      finally show ?thesis .  
    qed
  qed 
qed  



end