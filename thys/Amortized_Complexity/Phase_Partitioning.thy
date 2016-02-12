theory Phase_Partitioning
imports OPT2
begin




definition "other a x y = (if a=x then y else x)"


definition Lxx where
  "Lxx (x::nat) y = lang (L_lasthasxx x y)"

lemma Lxx_not_nullable: "[] \<notin> Lxx x y"
unfolding Lxx_def L_lasthasxx_def by simp

(*
lemma Lxx_gt2: "xs \<in> Lxx x y \<Longrightarrow> length xs \<ge> 2"
unfolding Lxx_def L_lasthasxx_def apply(auto)
proof -
  case goal1
  then have "xs
    \<in> ({[], [x]} @@ star ({[y]} @@ {[x]}))
        @@ ({[y]} @@ {[y]})" by (simp add: conc_assoc)
  then obtain A B where xs: "xs=A@B" and "A\<in>({[], [x]} @@ star ({[y]} @@ {[x]}))"
      and "B\<in>({[y]} @@ {[y]})" by auto
  then have "B=[y,y]" by auto
  with xs show ?case by auto
next 
  case goal2
  then have "xs
    \<in> ({[], [y]} @@ star ({[x]} @@ {[y]}))
        @@ ({[x]} @@ {[x]})" by (simp add: conc_assoc)
  then obtain A B where xs: "xs=A@B" and "A\<in>({[], [y]} @@ star ({[x]} @@ {[y]}))"
      and "B\<in>({[x]} @@ {[x]})" by auto
  then have "B=[x,x]" by auto
  with xs show ?case by auto
qed
*) 

lemma Lxx_ends_in_two_equal: "xs \<in> Lxx x y \<Longrightarrow> \<exists>pref e. xs = pref @ [e,e]"
unfolding Lxx_def L_lasthasxx_def
apply(auto)
proof -
  case goal1
  have A: "{[y]} @@ {[y]} = {[y,y]}" unfolding conc_def by(simp)
  from goal1[unfolded A] have "xs \<in> ({[], [x]} @@ star ({[y]} @@ {[x]})) @@ {[y,y]}" 
    by(simp add: conc_assoc)
  then show ?case by auto 
next 
  case goal2
  have A: "{[x]} @@ {[x]} = {[x,x]}" unfolding conc_def by(simp)
  from goal2[unfolded A] have "xs \<in> ({[], [y]} @@ star ({[x]} @@ {[y]})) @@ {[x,x]}" 
    by(simp add: conc_assoc)
  then show ?case by auto 
qed


lemma "Lxx x y = Lxx y x" unfolding Lxx_def by(rule lastxx_com)

definition "hideit x y = (Plus rexp.One (nodouble x y))"

lemma Lxx_othercase: "set qs \<subseteq> {x,y} \<Longrightarrow> \<not> (\<exists>xs ys. qs = xs @ ys \<and> xs \<in> Lxx x y) \<Longrightarrow> qs \<in> lang (hideit x y)"
proof -
  assume "set qs \<subseteq> {x,y}"
  then have "qs \<in> lang (myUNIV x y)" using myUNIV_alle[of x y] by blast
  thm myUNIV_char
  then have "qs \<in> star (lang (L_lasthasxx x y)) @@  lang (hideit x y)" unfolding hideit_def
    by(auto simp add: myUNIV_char)
  then have qs: "qs \<in> star (Lxx x y) @@  lang (hideit x y)" by(simp add: Lxx_def)
  assume notpos: "\<not> (\<exists>xs ys. qs = xs @ ys \<and> xs \<in> Lxx x y)"
  show "qs \<in> lang (hideit x y)"
  proof -
    from qs obtain A B where qsAB: "qs=A@B" and A: "A\<in>star (Lxx x y)" and B: "B\<in>lang (hideit x y)" by auto
    with notpos have notin: "A \<notin> (Lxx x y)" by blast
    thm  Lxx_not_nullable[of x y] 
    
    from A have 1: "A = [] \<or> A \<in> (Lxx x y) @@ star (Lxx x y)" using Regular_Set.star_unfold_left by auto
    have 2: "A \<notin> (Lxx x y) @@ star (Lxx x y)"
    proof (rule ccontr)
      assume "\<not> A \<notin> Lxx x y @@ star (Lxx x y)"
      then have " A \<in> Lxx x y @@ star (Lxx x y)" by auto
      then obtain A1 A2 where "A=A1@A2" and A1: "A1\<in>(Lxx x y)" and "A2\<in> star (Lxx x y)" by auto
      with qsAB have "qs=A1@(A2@B)" "A1\<in>(Lxx x y)" by auto
      with notpos have "A1 \<notin> (Lxx x y)" by blast
      with A1 show "False" by auto
    qed
    from 1 2 have "A=[]" by auto
    with qsAB have "qs=B" by auto
    with B show ?thesis by simp
  qed
qed


fun pad where "pad xs x y = (if xs=[] then [x,x] else 
                                    (if last xs = x then xs @ [x] else xs @ [y]))"

lemma pad_adds2: "qs \<noteq> [] \<Longrightarrow> set qs \<subseteq> {x,y} \<Longrightarrow> pad qs x y = qs @ [last qs]"
apply(auto) by (metis insertE insert_absorb insert_not_empty last_in_set subset_iff) 


lemma nodouble_padded: "qs \<noteq> [] \<Longrightarrow> qs \<in> lang (nodouble x y) \<Longrightarrow> pad qs x y \<in> Lxx x y"
proof -
  assume nn: "qs \<noteq> []"
  assume "qs \<in> lang (nodouble x y)"
  then have a: "qs \<in> lang         (seq
          [Plus (Atom x) rexp.One,
           Star (Times (Atom y) (Atom x)),
           Atom y]) \<or> qs \<in> lang
        (seq
          [Plus (Atom y) rexp.One,
           Star (Times (Atom x) (Atom y)),
           Atom x])"  unfolding nodouble_def by auto


  show ?thesis
  proof (cases "qs \<in> lang (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)), Atom y])")
    case True
    then have "qs \<in> lang (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x))]) @@ {[y]}"
      by(simp add: conc_assoc)
    then have "last qs = y" by auto
    with nn have p: "pad qs x y = qs @ [y]" by auto
    have A: "pad qs x y \<in> lang  (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)),
             Atom y]) @@ {[y]}" unfolding p
             apply(simp)
             apply(rule concI)
              using True by auto
    have B: "lang  (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)),
             Atom y]) @@ {[y]} = lang  (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)),
             Atom y, Atom y])" by (simp add: conc_assoc)
    show "pad qs x y \<in> Lxx x y" unfolding Lxx_def L_lasthasxx_def 
      using B A by auto
  next
    case False
    with a have T: "qs \<in> lang (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)), Atom x])" by auto

    then have "qs \<in> lang (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y))]) @@ {[x]}"
      by(simp add: conc_assoc)
    then have "last qs = x" by auto
    with nn have p: "pad qs x y = qs @ [x]" by auto
    have A: "pad qs x y \<in> lang  (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)),
             Atom x]) @@ {[x]}" unfolding p
             apply(simp)
             apply(rule concI)
              using T by auto
    have B: "lang  (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)),
             Atom x]) @@ {[x]} = lang  (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)),
             Atom x, Atom x])" by (simp add: conc_assoc)
    show "pad qs x y \<in> Lxx x y" unfolding Lxx_def L_lasthasxx_def 
      using B A by auto
 qed
qed


lemma LxxI: "(qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom y]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> Lxx x y \<Longrightarrow> P x y qs)"
unfolding Lxx_def lastxx_is_4cases[symmetric] L_4cases_def apply(simp only: question_def verund.simps lang.simps)
  by blast


lemma Lxx1: "xs \<in> Lxx x y \<Longrightarrow> length xs \<ge> 2"
  apply(rule LxxI[where P="(\<lambda>x y qs. length qs \<ge> 2)"])
  apply(auto) by(auto simp: conc_def)




section "OPT2 Splitting"

         

lemma ayay: "length qs = length as \<Longrightarrow> T\<^sub>p s (qs@[q]) (as@[a]) = T\<^sub>p s qs as + t\<^sub>p (steps s qs as) q a"
apply(induct qs as arbitrary: s rule: list_induct2) by simp_all

lemma tlofOPT2: "Q \<in> {x,y} \<Longrightarrow> set QS \<subseteq> {x,y} \<Longrightarrow> R \<in> {[x, y], [y, x]} \<Longrightarrow> tl (OPT2 ((Q # QS) @ [x, x]) R) =
    OPT2 (QS @ [x, x]) (step R Q (hd (OPT2 ((Q # QS) @ [x, x]) R)))"
      apply(cases "Q=x")
        apply(cases "R=[x,y]")
          apply(simp add: OPT2x step_def)
          apply(simp)
            apply(cases QS)
                apply(simp add: step_def mtf2_def swap_def)
                apply(simp add: step_def mtf2_def swap_def)
        apply(cases "R=[x,y]")
          apply(simp)
            apply(cases QS)
                apply(simp add: step_def mtf2_def swap_def)
                apply(simp add: step_def mtf2_def swap_def)
          by(simp add: OPT2x step_def)


lemma T\<^sub>p_split: "length qs1=length as1 \<Longrightarrow> T\<^sub>p s (qs1@qs2) (as1@as2) = T\<^sub>p s qs1 as1 + T\<^sub>p (steps s qs1 as1) qs2 as2"
apply(induct qs1 as1 arbitrary: s rule: list_induct2) by(simp_all)
 
lemma T\<^sub>p_spliting: "x\<noteq>y \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> set ys \<subseteq> {x,y} \<Longrightarrow>
      R \<in> {[x,y],[y,x]} \<Longrightarrow>
      T\<^sub>p R (xs@[x,x]) (OPT2 (xs@[x,x]) R) + T\<^sub>p [x,y] ys (OPT2 ys [x,y])
      = T\<^sub>p R (xs@[x,x]@ys) (OPT2 (xs@[x,x]@ys) R)"
proof -
  assume nxy: "x\<noteq>y"
  assume XSxy: "set xs \<subseteq> {x,y}"
  assume YSxy: "set ys \<subseteq> {x,y}"
  assume R: "R \<in> {[x,y],[y,x]}"
  {
    fix R
    assume XSxy: "set xs \<subseteq> {x,y}"
    have "R\<in>{[x,y],[y,x]} \<Longrightarrow> set xs \<subseteq> {x,y}  \<Longrightarrow> steps R (xs@[x,x]) (OPT2 (xs@[x,x]) R) = [x,y]"
    proof(induct xs arbitrary: R)
      case Nil
      then show ?case
        apply(cases "R=[x,y]")
          apply(simp add: step_def)
          by(simp add: step_def mtf2_def swap_def)
    next
      case (Cons Q QS)
      let ?R'="(step R Q (hd (OPT2 ((Q # QS) @ [x, x]) R)))"

      have a: "Q \<in> {x,y}"  and b: "set QS \<subseteq> {x,y}" using Cons by auto 
      have t: "?R' \<in> {[x,y],[y,x]}"
        apply(rule stepxy) using nxy Cons by auto
      then have "length (OPT2 (QS @ [x, x]) ?R') > 0" 
        apply(cases "?R' = [x,y]") by(simp_all add: OPT2_length)
      then have "OPT2 (QS @ [x, x]) ?R' \<noteq> []" by auto
      then have hdtl: "OPT2 (QS @ [x, x]) ?R' = hd (OPT2 (QS @ [x, x]) ?R') # tl (OPT2 (QS @ [x, x]) ?R')" 
         by auto

      have maa: "(tl (OPT2 ((Q # QS) @ [x, x]) R)) = OPT2 (QS @ [x, x]) ?R' "
        using tlofOPT2[OF a b Cons(2)] by auto

      
      from Cons(2) have "length (OPT2 ((Q # QS) @ [x, x]) R) > 0" 
        apply(cases "R = [x,y]") by(simp_all add: OPT2_length)
      then have nempty: "OPT2 ((Q # QS) @ [x, x]) R \<noteq> []" by auto
      then have "steps R ((Q # QS) @ [x, x]) (OPT2 ((Q # QS) @ [x, x]) R)
        = steps R ((Q # QS) @ [x, x]) (hd(OPT2 ((Q # QS) @ [x, x]) R) #  tl(OPT2 ((Q # QS) @ [x, x]) R))"
          by(simp)
      also have "\<dots>    
        = steps ?R' (QS @ [x,x]) (tl (OPT2 ((Q # QS) @ [x, x]) R))"
          unfolding maa by auto
      also have "\<dots> = steps ?R' (QS @ [x,x]) (OPT2 (QS @ [x, x]) ?R')" using maa by auto
      also with Cons(1)[OF t b] have "\<dots> = [x,y]" by auto
      
        
      finally show ?case .
    qed
  } note aa=this

    from aa XSxy R have ll: "steps R (xs@[x,x]) (OPT2 (xs@[x,x]) R)
      = [x,y]" by auto


    thm OPT2_split11 steps_append 
  have uer: " length (xs @ [x, x]) = length (OPT2 (xs @ [x, x]) R)"
    using R  by (auto simp: OPT2_length)

  have "OPT2 (xs @ [x, x] @ ys) R = OPT2 (xs @ [x, x]) R @ OPT2 ys [x, y]" 
    apply(rule OPT2_split11)
      using nxy XSxy YSxy R by auto


  then have "T\<^sub>p R (xs@[x,x]@ys) (OPT2 (xs@[x,x]@ys) R)
        = T\<^sub>p R ((xs@[x,x])@ys) (OPT2 (xs @ [x, x]) R @ OPT2 ys [x, y])"  by auto
  thm T\<^sub>p_split
  also have "\<dots> = T\<^sub>p R (xs@[x,x]) (OPT2 (xs @ [x, x]) R)
                + T\<^sub>p [x,y] ys (OPT2 ys [x, y])"
                  using T\<^sub>p_split[of "xs@[x,x]" "OPT2 (xs @ [x, x]) R" R ys "OPT2 ys [x, y]", OF uer, unfolded ll] 
                by auto
  finally show ?thesis by simp
qed


lemma OPTauseinander: "x\<noteq>y \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> set ys \<subseteq> {x,y} \<Longrightarrow>
      LTS \<in> {[x,y],[y,x]} \<Longrightarrow> hd LTS = last xs \<Longrightarrow>
     xs = (pref @ [hd LTS, hd LTS]) \<Longrightarrow> 
      T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p LTS ys (OPT2 ys LTS)
      = T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])"
proof -
  assume nxy: "x\<noteq>y"
  assume xsxy: "set xs \<subseteq> {x,y}"
  assume ysxy: "set ys \<subseteq> {x,y}"
  assume L: "LTS \<in> {[x,y],[y,x]}"
  assume "hd LTS = last xs"
  assume prefix: "xs = (pref @ [hd LTS, hd LTS])"
  show ?thesis
    proof (cases "LTS = [x,y]")
      case True
      show ?thesis unfolding True prefix
        apply(simp)
        apply(rule T\<^sub>p_spliting[simplified])
          using nxy xsxy ysxy prefix by auto
    next
      case False
      with L have TT: "LTS = [y,x]" by auto
      show ?thesis unfolding TT prefix
        apply(simp)
        apply(rule T\<^sub>p_spliting[simplified])
          using nxy xsxy ysxy prefix by auto
   qed
qed





end