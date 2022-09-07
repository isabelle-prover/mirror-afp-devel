(* Title: thys/ComposableTMs.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Modifications and comments by Franz Regensburger (FABR) 02/2022

   * added function mk_composable0 that generates composable TMs from non-composable TMs
     such that the overall behaviour of the TM is preserved.

     This is important for the proof of the existence of uncomputable functions
     respectively undecidable sets and relations.
 *)

theory ComposableTMs
  imports Turing
begin

section \<open>Making Turing Machines composable\<close>

(* Well-formedness of Turing machine programs
 *
 * For certain inputs programs tm with \<not>(composable_tm tm) may reach
 * the final state with a standard tape!
 *
 * These machines are no junk. They are simply not composable via |+|
 *)

abbreviation "is_even n \<equiv> (n::nat) mod 2 = 0"
abbreviation "is_odd n \<equiv> (n::nat) mod 2 \<noteq> 0"

fun 
  composable_tm :: "tprog \<Rightarrow> bool"
  where
    "composable_tm (p, off) = (length p \<ge> 2 \<and> is_even (length p) \<and> 
                    (\<forall>(a, s) \<in> set p. s \<le> length p div 2 + off \<and> s \<ge> off))"

abbreviation
  "composable_tm0 p \<equiv> composable_tm (p, 0)"

lemma step_in_range: 
  assumes h1: "\<not> is_final (step0 c A)"
    and h2: "composable_tm (A, 0)"
  shows "fst (step0 c A) \<le> length A div 2"
  using h1 h2
  apply(cases c;cases "fst c";cases "hd (snd (snd c))")
  by(auto simp add: Let_def case_prod_beta')

lemma steps_in_range: 
  assumes h1: "\<not> is_final (steps0 (1, tap) A stp)"
    and h2: "composable_tm (A, 0)"
  shows "fst (steps0 (1, tap) A stp) \<le> length A div 2"
  using h1
proof(induct stp)
  case 0
  then show "fst (steps0 (1, tap) A 0) \<le> length A div 2" using h2
    by (auto)
next
  case (Suc stp)
  have ih: "\<not> is_final (steps0 (1, tap) A stp) \<Longrightarrow> fst (steps0 (1, tap) A stp) \<le> length A div 2" by fact
  have h: "\<not> is_final (steps0 (1, tap) A (Suc stp))" by fact
  from ih h h2 show "fst (steps0 (1, tap) A (Suc stp)) \<le> length A div 2"
    by (metis step_in_range step_red)
qed

(* ------------------------------------------------------------------------ *)
(* New by FABR                                                              *)
(* ------------------------------------------------------------------------ *)

subsection \<open>Definitin of function fix\_jumps and mk\_composable0\<close>

fun fix_jumps  :: "nat \<Rightarrow> tprog0 \<Rightarrow> tprog0" where
  "fix_jumps smax [] = []" |
  "fix_jumps smax (ins#inss) = (if (snd ins) \<le> smax
                                then ins # fix_jumps smax inss
                                else ((fst ins),0)#fix_jumps smax inss)"

fun mk_composable0 :: "tprog0 \<Rightarrow> tprog0" where
  "mk_composable0 []   = [(Nop,0),(Nop,0)]" |
  "mk_composable0 [i1] = fix_jumps 1 [i1,(Nop,0)]" |
  "mk_composable0 (i1#i2#ins) = (let l = 2 + length ins
                        in if is_even l
                           then fix_jumps (l div 2)       (i1#i2#ins)
                           else fix_jumps ((l div 2) + 1) ((i1#i2#ins)@[(Nop,0)]))"


subsection \<open>Properties of function fix\_jumps\<close>

lemma fix_jumps_len: "length (fix_jumps smax insl) = length insl"
  by (induct insl) auto

lemma fix_jumps_le_smax: "\<forall>x \<in> set (fix_jumps smax tm). (snd x) \<le> smax"
proof (rule filter_id_conv[THEN iffD1])
  show "filter (\<lambda>x. snd x \<le> smax) (fix_jumps smax tm) = fix_jumps smax tm"
    by (induct tm)(auto)
qed

lemma fix_jumps_nth_no_fix:
  assumes "n < length tm" and "tm!n = ins" and "(snd ins) \<le> smax"
  shows "(fix_jumps smax tm)!n = ins"
proof -
  have "n < length tm \<and> tm!n = ins \<and> (snd ins) \<le> smax \<longrightarrow> (fix_jumps smax tm)!n = ins"
  proof (induct tm arbitrary: n ins)
    case Nil
    then show ?case by auto
  next
    fix a tm n ins
    assume IV: "\<And>n' ins'. n' < length tm \<and> tm ! n' = ins' \<and> snd ins' \<le> smax \<longrightarrow> fix_jumps smax tm ! n' = ins'"
    show "n < length (a # tm) \<and> (a # tm) ! n = ins \<and> snd ins \<le> smax \<longrightarrow> fix_jumps smax (a # tm) ! n = ins"
    proof (cases n)
      case 0
      then show ?thesis by auto
    next
      fix nat
      assume "n = Suc nat"
      show "n < length (a # tm) \<and> (a # tm) ! n = ins \<and> snd ins \<le> smax \<longrightarrow> fix_jumps smax (a # tm) ! n = ins"
      proof
        assume A: "n < length (a # tm) \<and> (a # tm) ! n = ins \<and> snd ins \<le> smax"
        show "fix_jumps smax (a # tm) ! n = ins"
        proof (cases "(snd a) \<le> smax")
          case True
          then have "fix_jumps smax (a # tm) ! (Suc nat) =  (a # (fix_jumps smax tm)) ! Suc nat" by auto
          also have "... = (fix_jumps smax tm) !nat" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = (fix_jumps smax tm) !nat" by auto
          also with \<open>n = Suc nat\<close> A and IV have "... = ins" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = ins" by auto
          with \<open>n = Suc nat\<close> show "fix_jumps smax (a # tm) ! n = ins" by auto
        next
          case False
          then have "fix_jumps smax (a # tm) ! (Suc nat) =  (((fst a),0) # (fix_jumps smax tm)) ! Suc nat" by auto
          also have "... = (fix_jumps smax tm) !nat" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = (fix_jumps smax tm) !nat" by auto
          also with \<open>n = Suc nat\<close> A and IV have "... = ins" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = ins" by auto
          with \<open>n = Suc nat\<close> show "fix_jumps smax (a # tm) ! n = ins" by auto
        qed
      qed
    qed
  qed
  with assms show ?thesis by auto
qed

lemma fix_jumps_nth_fix:
  assumes "n < length tm" and "tm!n = ins" and "\<not>(snd ins) \<le> smax"
  shows "(fix_jumps smax tm)!n = ((fst ins),0)"
proof -
  have "n < length tm \<and> tm!n = ins \<and> \<not>(snd ins) \<le> smax \<longrightarrow> (fix_jumps smax tm)!n = ((fst ins),0)"
  proof (induct tm arbitrary: n ins)
    case Nil
    then show ?case by auto
  next
    fix a tm n ins
    assume IV: "\<And>n' ins'. n' < length tm \<and> tm ! n' = ins' \<and> \<not>(snd ins') \<le> smax \<longrightarrow> fix_jumps smax tm ! n' = (fst ins', 0)"
    show "n < length (a # tm) \<and> (a # tm) ! n = ins \<and> \<not> snd ins \<le> smax \<longrightarrow> fix_jumps smax (a # tm) ! n = (fst ins, 0)"
    proof (cases n)
      case 0
      then show ?thesis by auto
    next
      fix nat
      assume "n = Suc nat"
      show "n < length (a # tm) \<and> (a # tm) ! n = ins \<and> \<not> snd ins \<le> smax \<longrightarrow> fix_jumps smax (a # tm) ! n = (fst ins, 0)"
      proof
        assume A: "n < length (a # tm) \<and> (a # tm) ! n = ins \<and> \<not> snd ins \<le> smax"
        show "fix_jumps smax (a # tm) ! n = (fst ins, 0)"
        proof (cases "(snd a) \<le> smax")
          case True
          then have "fix_jumps smax (a # tm) ! (Suc nat) =  (a # (fix_jumps smax tm)) ! Suc nat" by auto
          also have "... = (fix_jumps smax tm) !nat" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = (fix_jumps smax tm) !nat" by auto
          also with \<open>n = Suc nat\<close> A and IV have "... = (fst ins, 0)" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = (fst ins, 0)" by auto
          with \<open>n = Suc nat\<close> show "fix_jumps smax (a # tm) ! n = (fst ins, 0)" by auto
        next
          case False
          then have "fix_jumps smax (a # tm) ! (Suc nat) =  (((fst a),0) # (fix_jumps smax tm)) ! Suc nat" by auto
          also have "... = (fix_jumps smax tm) !nat" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = (fix_jumps smax tm) !nat" by auto
          also with \<open>n = Suc nat\<close> A and IV have "... = (fst ins, 0)" by auto
          finally have "fix_jumps smax (a # tm) ! Suc nat = (fst ins, 0)" by auto
          with \<open>n = Suc nat\<close> show "fix_jumps smax (a # tm) ! n = (fst ins, 0)" by auto
        qed
      qed
    qed
  qed
  with assms show ?thesis by auto
qed

subsection \<open>Functions fix\_jumps and mk\_composable0 generate composable Turing Machines.\<close>

lemma composable_tm0_fix_jumps_pre:
  assumes "length tm \<ge> 2" and "is_even (length tm)"
  shows "length (fix_jumps (length tm div 2) tm) \<ge> 2 \<and>
          is_even (length (fix_jumps (length tm div 2) tm)) \<and> 
          (\<forall>x \<in> set (fix_jumps (length tm div 2) tm).
             (snd x) \<le> length (fix_jumps (length tm div 2) tm) div 2 + 0 \<and> (snd x) \<ge> 0)"
proof
  show "2 \<le> length (fix_jumps (length tm div 2) tm)"
    using assms by (auto simp add: fix_jumps_len)
next
  show "is_even (length (fix_jumps (length tm div 2) tm)) \<and>
        (\<forall>x\<in>set (fix_jumps (length tm div 2) tm). snd x \<le> length (fix_jumps (length tm div 2) tm) div 2 + 0 \<and> 0 \<le> snd x)"
  proof
    show "is_even (length (fix_jumps (length tm div 2) tm))"
      using assms by (auto simp add: fix_jumps_len)
  next
    show "\<forall>x\<in>set (fix_jumps (length tm div 2) tm). snd x \<le> length (fix_jumps (length tm div 2) tm) div 2 + 0 \<and> 0 \<le> snd x"
      by (auto simp add: fix_jumps_le_smax fix_jumps_len)
  qed
qed

lemma composable_tm0_fix_jumps:
  assumes "length tm \<ge> 2" and "is_even (length tm)"
  shows "composable_tm0 (fix_jumps (length tm div 2) tm)"
proof -
  from assms have "length (fix_jumps (length tm div 2) tm) \<ge> 2 \<and>
                   is_even (length (fix_jumps (length tm div 2) tm)) \<and> 
                   (\<forall>x \<in> set (fix_jumps (length tm div 2) tm).
                      (snd x) \<le> length (fix_jumps (length tm div 2) tm) div 2 + 0 \<and> (snd x) \<ge> 0)"
    by (rule composable_tm0_fix_jumps_pre)
  then show ?thesis by auto
qed


lemma fix_jumps_composable0_eq:
  assumes "composable_tm0 tm"
  shows "(fix_jumps (length tm div 2) tm) = tm"
proof -
  from assms have major: "\<forall>(a, s) \<in> set tm. s \<le> length tm div 2" by auto
  then show "(fix_jumps (length tm div 2) tm) = tm"
    by  (induct rule: fix_jumps.induct)(auto)
qed

lemma composable_tm0_mk_composable0: "composable_tm0 (mk_composable0 tm)"
proof (rule mk_composable0.cases)
  assume "tm = []"
  then show "composable_tm0 (mk_composable0 tm)"
    by (auto simp add: composable_tm0_fix_jumps)
next
  fix i1
  assume "tm = [i1]"
  then show "composable_tm0 (mk_composable0 tm)"
    by (auto simp add: composable_tm0_fix_jumps)
next
  fix i1 i2 ins
  assume A: "tm = i1 # i2 # ins"
  then show "composable_tm0 (mk_composable0 tm)"
  proof (cases "is_even (2 + length ins)")
    case True
    then have "is_even (2 + length ins)" .
    then have "mk_composable0 (i1 # i2 # ins) = fix_jumps ((2 + length ins) div 2) (i1#i2#ins)"
      by auto
    also have "... = fix_jumps (length (i1#i2#ins) div 2) (i1#i2#ins)"
      by auto
    finally have "mk_composable0 (i1 # i2 # ins) = fix_jumps (length (i1#i2#ins) div 2) (i1#i2#ins)"
      by auto
    moreover have "composable_tm0 (fix_jumps (length (i1#i2#ins) div 2) (i1#i2#ins))"
    proof (rule composable_tm0_fix_jumps)
      show "2 \<le> length (i1 # i2 # ins)" by auto
    next
      from \<open>is_even (2 + length ins)\<close> show "is_even (length (i1 # i2 # ins))" 
        by (auto)
    qed
    ultimately show "composable_tm0 (mk_composable0 tm)" using A by auto
  next
    case False
    then have "(2 + length ins) mod 2 \<noteq> 0" .
    then have "mk_composable0 (i1 # i2 # ins) = fix_jumps (((2 + length ins) div 2) +1) ((i1#i2#ins)@[(Nop,0)])"
      by auto
    also have "... = fix_jumps ((length (i1#i2#ins) div 2) +1) ((i1#i2#ins)@[(Nop,0)])"
      by auto
    also have "... = fix_jumps (length (i1#i2#ins@[(Nop,0)]) div 2) ((i1#i2#ins)@[(Nop,0)])"
    proof -
      from \<open>(2 + length ins) mod 2 \<noteq> 0\<close>
      have "length ins mod 2 \<noteq> 0" by arith
      then have "length (i1 # i2 # ins ) mod 2  \<noteq> 0" by auto

      have "(length (i1 # i2 # ins ) div 2) + 1 = length (i1 # i2 # ins @ [(Nop, 0)]) div 2"
      proof -
        from \<open>length (i1 # i2 # ins ) mod 2  \<noteq> 0\<close>
        have "(length (i1 # i2 # ins ) div 2) + 1 = (length (i1 # i2 # ins) +1) div 2"
          by (rule odd_div2_plus_1_eq)
        also have "... = length (i1 # i2 # ins @ [(Nop, 0)]) div 2" by auto
        finally show ?thesis by auto
      qed

      then show "fix_jumps (length (i1 # i2 # ins) div 2 + 1) ((i1 # i2 # ins) @ [(Nop, 0)]) =
                 fix_jumps (length (i1 # i2 # ins @ [(Nop, 0)]) div 2) ((i1 # i2 # ins) @ [(Nop, 0)])"
        by auto
    qed
    finally have "mk_composable0 (i1 # i2 # ins) =
                   fix_jumps (length (i1 # i2 # ins @ [(Nop, 0)]) div 2) ((i1 # i2 # ins) @ [(Nop, 0)])"
      by auto

    moreover have "composable_tm0 (fix_jumps (length (i1 # i2 # ins @ [(Nop, 0)]) div 2) (i1 # i2 # ins @ [(Nop, 0)]))"
    proof (rule composable_tm0_fix_jumps)
      show " 2 \<le> length (i1 # i2 # ins @ [(Nop, 0)])" by auto
    next
      show "is_even (length (i1 # i2 # ins @ [(Nop, 0)]))"
      proof -
        from \<open>(2 + length ins) mod 2 \<noteq> 0\<close> have "length (i1 # i2 # ins) mod 2  \<noteq> 0" by auto
        then have "is_even (length (i1 # i2 # ins) +1)" by arith
        moreover have "length (i1 # i2 # ins) +1 = length (i1 # i2 # ins @ [(Nop, 0)])" by auto
        ultimately show "is_even (length (i1 # i2 # ins @ [(Nop, 0)]))" by auto
      qed
    qed
    ultimately show "composable_tm0 (mk_composable0 tm)" using A by auto
  qed
qed

subsection \<open>Functions mk\_composable0 is the identity on composable Turing Machines\<close>

lemma mk_composable0_eq:
  assumes "composable_tm0 tm"
  shows "mk_composable0 tm = tm"
proof -
  from assms have major: "length tm \<ge> 2 \<and> is_even (length tm)" by auto
  show "mk_composable0 tm = tm"
  proof (rule mk_composable0.cases)
    assume "tm = []"
    with major have False by auto
    then show "mk_composable0 tm = tm" by auto
  next
    fix i1
    assume "tm = [i1]"
    with major have False by auto
    then show "mk_composable0 tm = tm" by auto
  next
    fix i1 i2 ins
    assume A: "tm = i1 # i2 # ins"
    then show " mk_composable0 tm = tm"
    proof (cases "is_even (2 + length ins)")
      case True
      then have "is_even (2 + length ins)" .
      then have "mk_composable0 (i1 # i2 # ins) = fix_jumps ((2 + length ins) div 2) (i1#i2#ins)"
        by auto
      also have "... = fix_jumps (length (i1#i2#ins) div 2) (i1#i2#ins)"
        by auto
      finally have "mk_composable0 (i1 # i2 # ins) = fix_jumps (length (i1#i2#ins) div 2) (i1#i2#ins)"
        by auto
      also have "fix_jumps (length (i1#i2#ins) div 2) (i1#i2#ins) = (i1#i2#ins)"
      proof (rule fix_jumps_composable0_eq)
        from assms and A show "composable_tm0 (i1 # i2 # ins)"
          by auto
      qed
      finally have "mk_composable0 (i1 # i2 # ins) = i1 # i2 # ins" by auto
      with A show "mk_composable0 tm = tm" by auto
    next
      case False
      then have "(2 + length ins) mod 2 \<noteq> 0" by auto
      then have "length (i1 # i2 # ins) mod 2 \<noteq> 0" by auto
      with A have "length tm   mod 2 \<noteq> 0" by auto
      with assms have False by auto
      then show ?thesis by auto
    qed
  qed
qed

(* ----------------------------------------------- *)
(* About the length of (mk_composable0 tm)                 *)
(* ----------------------------------------------- *)

subsection \<open>About the length of mk\_composable0 tm\<close>

lemma length_mk_composable0_nil: "length (mk_composable0 []) = 2"
  by auto

lemma length_mk_composable0_singleton: "length (mk_composable0 [i1]) = 2"
  by auto

lemma length_mk_composable0_gt2_even: "is_even (length (i1 # i2 # ins)) \<Longrightarrow> length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)"
proof -
  assume "is_even (length (i1 # i2 # ins))"
  then have "length (mk_composable0 (i1 # i2 # ins)) = length (fix_jumps ((length (i1 # i2 # ins)) div 2) (i1#i2#ins))" by auto
  also have "... = length (i1#i2#ins)" by (auto simp add: fix_jumps_len)
  finally show "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)" by auto
qed

lemma length_mk_composable0_gt2_odd: "\<not>is_even (length (i1 # i2 # ins)) \<Longrightarrow> length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)+1"
proof -
  assume "\<not>is_even (length (i1 # i2 # ins))"
  then have "length (mk_composable0 (i1 # i2 # ins)) = length (fix_jumps (((length (i1 # i2 # ins)) div 2)+1) ((i1#i2#ins)@[(Nop,0)]))" by auto
  also have "... = length ((i1#i2#ins)@[(Nop,0)])" by (auto simp add: fix_jumps_len)
  finally show "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins) + 1" by auto
qed

lemma length_mk_composable0_even: "\<lbrakk>0 < length tm ; is_even (length tm) \<rbrakk> \<Longrightarrow> length (mk_composable0 tm) = length tm"
proof (rule mk_composable0.cases[of tm])
  assume "0 < length tm"
    and  "is_even (length tm)"
    and "tm = []"
  then show ?thesis by auto
next
  fix i1
  assume "0 < length tm" and "is_even (length tm)" and "tm = [i1]"
  then show ?thesis by auto
next
  fix i1 i2 ins
  assume "0 < length tm" and "is_even (length tm)" and "tm = i1 # i2 # ins"
  then show ?thesis
  proof (cases "is_even (2 + length ins)")
    case True
    then have "is_even (2 + length ins)" .
    then have "mk_composable0 (i1 # i2 # ins) = fix_jumps ((2 + length ins) div 2) (i1#i2#ins)" by auto
    moreover have "length (fix_jumps ((2 + length ins) div 2) (i1#i2#ins)) = length (i1#i2#ins)"
      by (rule fix_jumps_len)
    ultimately have "length (mk_composable0 (i1 # i2 # ins)) =  length (i1#i2#ins)" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  next
    case False
    with \<open>is_even (length tm)\<close> and  \<open>tm = i1 # i2 # ins\<close> have False by auto
    then show ?thesis by auto
  qed
qed

lemma length_mk_composable0_odd: "\<lbrakk>0 < length tm ; \<not>is_even (length tm) \<rbrakk> \<Longrightarrow> length (mk_composable0 tm) = 1 + length tm"
proof (rule mk_composable0.cases[of tm])
  assume "0 < length tm"
    and  "\<not> is_even (length tm)"
    and "tm = []"
  then show ?thesis by auto
next
  fix i1
  assume "0 < length tm" and "\<not>is_even (length tm)" and "tm = [i1]"
  then show ?thesis by auto
next
  fix i1 i2 ins
  assume "0 < length tm" and "\<not>is_even (length tm)" and "tm = i1 # i2 # ins"
  then show ?thesis
  proof (cases "is_even (2 + length ins)")
    case True
    with \<open>\<not>is_even (length tm)\<close> and \<open>tm = i1 # i2 # ins\<close> have False by auto
    then show ?thesis by auto
  next
    case False
    then have "\<not>is_even (2 + length ins)" by auto
    then have "mk_composable0 (i1 # i2 # ins) = fix_jumps (((2 + length ins) div 2)+1 ) ((i1#i2#ins)@[(Nop,0)])"
      by auto
    moreover have "length (fix_jumps ( ((2 + length ins) div 2)+1 ) ((i1#i2#ins)@[(Nop,0)])) = length ((i1#i2#ins)@[(Nop,0)])"
      by (rule fix_jumps_len)
    ultimately have "length (mk_composable0 (i1 # i2 # ins)) =  1 + length (i1#i2#ins)" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  qed
qed

lemma length_tm_le_mk_composable0: "length tm \<le> length (mk_composable0 tm)"
proof (cases "length tm")
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then have A: "length tm = Suc nat" .
  show ?thesis
  proof (cases "is_even (length tm)")
    case True
    with A show ?thesis by (auto simp add: length_mk_composable0_even)
  next
    case False
    with A show ?thesis by (auto simp add: length_mk_composable0_odd)
  qed
qed


subsection \<open>Properties of function fetch with respect to function mk\_composable0\<close>

(* ----------------------------------------------- *)
(* Fetching instructions from  (mk_composable0 tm)         *)
(* ----------------------------------------------- *)

lemma fetch_mk_composable0_Bk_too_short_Suc:
  assumes "b = Bk" and "length tm \<le> 2*s"
  shows "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0::nat)"
proof (rule mk_composable0.cases[of tm])
  assume "tm = []"
  then have "length (mk_composable0 tm) = 2" by auto
  with \<open>tm = []\<close> have "(mk_composable0 tm) = [(Nop,0),(Nop,0)]" by auto
  show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0)"
  proof (cases s)
    assume "s=0"
    with \<open>length (mk_composable0 tm) = 2\<close> 
    have "fetch (mk_composable0 tm) (Suc s) Bk = ((mk_composable0 tm) ! (2*s))"
      by (auto)
    also with \<open>s=0\<close> and  \<open>(mk_composable0 tm) = [(Nop,0),(Nop,0)]\<close> have "... = (Nop, 0::nat)" by auto
    finally have "fetch (mk_composable0 tm) (Suc s) Bk = (Nop, 0::nat)" by auto
    with \<open>b = Bk\<close> show ?thesis by auto
  next
    case (Suc nat)
    then have "s = Suc nat" .
    with \<open>length (mk_composable0 tm) = 2\<close> have "length (mk_composable0 tm) \<le> 2*s" by auto
    with \<open>b = Bk\<close> show ?thesis by (auto)
  qed
next
  fix i1
  assume "tm = [i1]"
  then have "mk_composable0 tm = fix_jumps 1 [i1,(Nop,0)]" by auto
  moreover have "length (fix_jumps 1 [i1,(Nop,0)]) = length [i1] +1" using fix_jumps_len by auto
  ultimately  have "length (mk_composable0 tm) = 2" using \<open>tm = [i1]\<close> by auto
  show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0)"
  proof (cases s)
    case 0
    with \<open>tm = [i1]\<close> and \<open>length tm \<le> 2*s\<close> have False by auto
    then show ?thesis by auto
  next
    case (Suc nat)
    then have "s = Suc nat" .
    with \<open>length (mk_composable0 tm) = 2\<close> have "length (mk_composable0 tm) \<le> 2*s" by arith
    with \<open>b = Bk\<close> show ?thesis by (auto)
  qed
next
  fix i1 i2 ins
  assume "tm = i1 # i2 # ins"
  show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0)"
  proof (cases "is_even (2 + length ins)")
    case True
    then have "is_even (2 + length ins)" .
    with \<open>tm = i1 # i2 # ins\<close> have "mk_composable0 tm = fix_jumps ((2 + length ins) div 2) tm" by auto
    moreover have "length(fix_jumps ((2 + length ins) div 2) tm) = length tm" using fix_jumps_len by auto
    ultimately have "length (mk_composable0 tm) = length tm" by auto  
    with \<open>length tm \<le> 2*s\<close> have "length (mk_composable0 tm) \<le> 2*s" by auto
    with \<open>b = Bk\<close> show ?thesis by auto
  next
    case False
    then have "\<not>is_even (2 + length ins)" .
    with \<open>tm = i1 # i2 # ins\<close>
    have "mk_composable0 tm = fix_jumps (((2 + length ins) div 2)+1) (tm@[(Nop,0)])" by auto
    moreover
    have "length(fix_jumps (((2 + length ins) div 2)+1) (tm@[(Nop,0)])) = length (tm@[(Nop,0)])" using fix_jumps_len by auto
    ultimately have "length (mk_composable0 tm) = length tm +1" by auto  
    moreover from \<open>\<not>is_even (2 + length ins)\<close> and  \<open>tm = i1 # i2 # ins\<close> have "\<not>is_even (length tm)" by auto
    with \<open>length tm \<le> 2*s\<close> have "length tm +1 \<le> 2*s" by arith
    with \<open>length (mk_composable0 tm) = length tm +1\<close> have "length (mk_composable0 tm) \<le> 2*s" by auto
    with \<open>b = Bk\<close> show ?thesis by auto
  qed
qed


lemma fetch_mk_composable0_Oc_too_short_Suc:
  assumes "b = Oc" and "length tm \<le> 2*s+1"
  shows "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0::nat)"
proof (rule mk_composable0.cases[of tm])
  assume "tm = []"
  then have "length (mk_composable0 tm) = 2" by auto
  with \<open>tm = []\<close> have "(mk_composable0 tm) = [(Nop,0),(Nop,0)]" by auto
  show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0)"
  proof (cases s)
    assume "s=0"
    with \<open>length (mk_composable0 tm) = 2\<close> 
    have "fetch (mk_composable0 tm) (Suc s) Oc = ((mk_composable0 tm) ! (2*s+1))"
      by (auto)
    also with \<open>s=0\<close> and  \<open>(mk_composable0 tm) = [(Nop,0),(Nop,0)]\<close> have "... = (Nop, 0::nat)" by auto
    finally have "fetch (mk_composable0 tm) (Suc s) Oc = (Nop, 0::nat)" by auto
    with \<open>b = Oc\<close> show ?thesis by auto
  next
    case (Suc nat)
    then have "s = Suc nat" .
    with \<open>length (mk_composable0 tm) = 2\<close> have "length (mk_composable0 tm) \<le> 2*s" by auto
    with \<open>b = Oc\<close> show ?thesis by (auto)
  qed
next
  fix i1
  assume "tm = [i1]"
  then have "mk_composable0 tm = fix_jumps 1 [i1,(Nop,0)]" by auto
  moreover have "length (fix_jumps 1 [i1,(Nop,0)]) = length [i1] +1" using fix_jumps_len by auto
  ultimately  have "length (mk_composable0 tm) = 2" using \<open>tm = [i1]\<close> by auto
  show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0)"
  proof (cases s)
    case 0
    then have "s=0" .
    with \<open>length (mk_composable0 tm) = 2\<close> have "fetch (mk_composable0 tm) (Suc s) Oc = ((mk_composable0 tm) ! 1)"
      by (auto)
    also with \<open>mk_composable0 tm = fix_jumps 1 [i1,(Nop,0)]\<close> have "... = ((fix_jumps 1 [i1,(Nop,0)]) ! 1)"
      by auto
    also have "... = (Nop, 0)" by (cases "(snd i1) \<le> 1")(auto)
    finally have "fetch (mk_composable0 tm) (Suc s) Oc = (Nop, 0)" by auto
    with \<open>b = Oc\<close> show ?thesis by auto
  next
    case (Suc nat)
    then have "s = Suc nat" .
    with \<open>length (mk_composable0 tm) = 2\<close> have "length (mk_composable0 tm) \<le> 2*s+1" by arith
    with \<open>b = Oc\<close> show ?thesis by (auto)
  qed
next
  fix i1 i2 ins
  assume "tm = i1 # i2 # ins"
  show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0)"
  proof (cases "is_even (2 + length ins)")
    case True
    then have "is_even (2 + length ins)" .
    with \<open>tm = i1 # i2 # ins\<close> have "mk_composable0 tm = fix_jumps ((2 + length ins) div 2) tm" by auto
    moreover have "length(fix_jumps ((2 + length ins) div 2) tm) = length tm" using fix_jumps_len by auto
    ultimately have "length (mk_composable0 tm) = length tm" by auto  
    with \<open>length tm \<le> 2*s+1\<close> have "length (mk_composable0 tm) \<le> 2*s+1" by auto
    with \<open>b = Oc\<close> show ?thesis by auto
  next
    case False
    then have "\<not>is_even (2 + length ins)" .
    with \<open>tm = i1 # i2 # ins\<close>
    have F1: "mk_composable0 tm = fix_jumps (((2 + length ins) div 2)+1) (tm@[(Nop,0)])" by auto
    moreover
    have "length(fix_jumps (((2 + length ins) div 2)+1) (tm@[(Nop,0)])) = length (tm@[(Nop,0)])"
      using fix_jumps_len by auto
    ultimately have "length (mk_composable0 tm) = length tm +1" by auto

    moreover from \<open>\<not>is_even (2 + length ins)\<close> and  \<open>tm = i1 # i2 # ins\<close>
    have "\<not>is_even (length tm)" by auto

    from \<open>length tm \<le> 2*s+1\<close> have  "(length tm) = (2*s+1) \<or> (length tm) < 2*s+1" by auto
    then show ?thesis
    proof
      assume "length tm = 2 * s + 1"
      from \<open>length tm = 2 * s + 1\<close> and \<open>length (mk_composable0 tm) = length tm +1\<close> have "length (mk_composable0 tm) = 2*s + 2" by auto
      from \<open>length tm = 2 * s + 1\<close> and \<open>length (mk_composable0 tm) = length tm +1\<close> have "length (mk_composable0 tm) > 2*s+1" by arith
      with \<open>b = Oc\<close> have "fetch (mk_composable0 tm) (Suc s) b = ((mk_composable0 tm) ! (2*s+1))" by (auto )
      also with \<open>length (mk_composable0 tm) = 2 * s + 2\<close> have "... = (mk_composable0 tm) ! (length (mk_composable0 tm)-1)" by auto
      also with F1 have "... = (fix_jumps (((2 + length ins) div 2)+1) (tm@[(Nop,0)])) ! (length (mk_composable0 tm)-1)" by auto
      also have "... = (Nop, 0)"
      proof (rule fix_jumps_nth_no_fix)
        show "snd (Nop, 0) \<le> (2 + length ins) div 2 + 1" by auto
      next
        from \<open>length (mk_composable0 tm) = length tm +1\<close> show "length (mk_composable0 tm) - 1 < length (tm @ [(Nop, 0)])" by auto
      next 
        from  \<open>length (mk_composable0 tm) = length tm +1\<close> show "(tm @ [(Nop, 0)]) ! (length (mk_composable0 tm) - 1) = (Nop, 0)" by auto
      qed
      finally show "fetch (mk_composable0 tm) (Suc s) b =  (Nop, 0)" by auto
    next
      assume "length tm < 2 * s + 1 "
      with \<open>\<not>is_even (length tm)\<close> have "length tm +1 \<le> 2 * s + 1" by auto
      with \<open>length (mk_composable0 tm) = length tm +1\<close> have "length (mk_composable0 tm)  \<le> 2 * s + 1" by auto
      with \<open>b = Oc\<close> show "fetch (mk_composable0 tm) (Suc s) b = (Nop, 0::nat)"
        by (auto)
    qed
  qed
qed

lemma nth_append': "n < length xs \<Longrightarrow> (xs @ ys) ! n = xs ! n" by (auto simp add: nth_append)

lemma fetch_mk_composable0_Bk_Suc_no_fix:
  assumes "b = Bk"
    and "2*s < length tm"
    and "fetch tm (Suc s) b = (a, s')"
    and "s' \<le> length (mk_composable0 tm) div 2"
  shows "fetch (mk_composable0 tm) (Suc s) b = fetch tm (Suc s) b"
proof (rule mk_composable0.cases[of tm])
  assume "tm = []"
  with \<open>length tm > 2*s\<close> show ?thesis by auto
next
  fix i1
  assume "tm = [i1]"
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s)"
    using \<open>tm = [i1]\<close> assms by auto
  also have "(mk_composable0 tm)!(2*s) = (a, s')"
  proof -
    from \<open>tm = [i1]\<close> have "length (mk_composable0 tm) = 2" by auto
    have "(mk_composable0 [i1])!(2*s) = (fix_jumps 1 [i1,(Nop,0)])!(2*s)" by auto
    also have "... = (a, s')"
    proof (rule fix_jumps_nth_no_fix)
      from assms and  \<open>tm = [i1]\<close> show "2 * s < length [i1, (Nop, 0)]" by auto
    next
      from assms and  \<open>tm = [i1]\<close> show "[i1, (Nop, 0)] ! (2 * s) = (a, s')" by auto
    next
      from assms and  \<open>tm = [i1]\<close> and \<open>length (mk_composable0 tm) = 2\<close> show "snd (a, s') \<le> 1" by auto
    qed
    finally have "(mk_composable0 [i1])!(2*s) = (a, s')" by auto
    with  \<open>tm = [i1]\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, s')" by auto
  with assms show ?thesis by auto
next
  fix i1 i2 ins
  assume "tm = i1 # i2 # ins"
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s)"
  proof -
    have "\<not> length (mk_composable0 tm) \<le> 2 * Suc s - 2"
      by (metis (no_types) add_diff_cancel_left' assms(2) le_trans length_tm_le_mk_composable0 mult_Suc_right not_less)
    then show ?thesis
      by (simp add: assms(1))
  qed
    
    also have "(mk_composable0 tm)!(2*s) = (a, s')"
  proof (cases "is_even (length tm)")
    case True
    then have "is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)" by (rule length_mk_composable0_gt2_even)

    from \<open>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (fix_jumps ((length (i1 # i2 # ins)) div 2) (i1#i2#ins))!(2*s)" by auto
    also have "... = (a, s')"
    proof (rule fix_jumps_nth_no_fix)
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "2 * s < length (i1 # i2 # ins)" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "(i1 # i2 # ins) ! (2 * s) = (a, s')" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)\<close>
      show "snd (a, s') \<le> length (i1 # i2 # ins) div 2" by auto
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (a, s')" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  next
    case False
    then have "\<not>is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "\<not>is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins) +1" by (rule length_mk_composable0_gt2_odd)

    from \<open>\<not>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (fix_jumps (((length (i1 # i2 # ins)) div 2)+1) ((i1#i2#ins)@[(Nop,0)]))!(2*s)" by auto
    also have "... = (a, s')"
    proof (rule fix_jumps_nth_no_fix)
      from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s < length ((i1 # i2 # ins) @ [(Nop, 0)])" by auto
    next
      have "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s) = ((i1 # i2 # ins)) ! (2 * s)"
      proof (rule nth_append')
        from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s < length (i1 # i2 # ins)" by auto
      qed
      also from assms and \<open>tm = i1 # i2 # ins\<close> have "((i1 # i2 # ins)) ! (2 * s) = (a, s')" by auto
      finally show "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s) = (a, s')" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length ((i1#i2#ins)) + 1\<close>
      show "snd (a, s') \<le> length (i1 # i2 # ins) div 2 + 1" by auto 
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (a, s')" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, s')" by auto
  with assms show ?thesis by auto
qed

lemma fetch_mk_composable0_Bk_Suc_fix:
assumes "b = Bk"
    and "2*s < length tm"
    and "fetch tm (Suc s) b = (a, s')"
    and "length (mk_composable0 tm) div 2 < s'"
shows "fetch (mk_composable0 tm) (Suc s) b = (a, 0)"
proof (rule mk_composable0.cases[of tm])
  assume "tm = []"
  with \<open>length tm > 2*s\<close> show ?thesis by auto
next
  fix i1
  assume "tm = [i1]"
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s)"
    using \<open>tm = [i1]\<close> assms(1) assms(2) by auto
  also have "(mk_composable0 tm)!(2*s) = (a, 0)"
  proof -
    from \<open>tm = [i1]\<close> have "length (mk_composable0 tm) = 2" by auto
    have "(mk_composable0 [i1])!(2*s) = (fix_jumps 1 [i1,(Nop,0)])!(2*s)" by auto
    also have "... = (fst(a,s'), 0)"
    proof (rule fix_jumps_nth_fix)
      from assms and  \<open>tm = [i1]\<close> show "2 * s < length [i1, (Nop, 0)]" by auto
    next
      from assms and  \<open>tm = [i1]\<close> show "[i1, (Nop, 0)] ! (2 * s) = (a, s')" by auto
    next
      from assms and  \<open>tm = [i1]\<close> and \<open>length (mk_composable0 tm) = 2\<close> show "\<not>snd (a, s') \<le> 1" by auto
    qed
    finally have "(mk_composable0 [i1])!(2*s) = (a, 0)" by auto
    with  \<open>tm = [i1]\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, 0)" by auto
  with assms show ?thesis by auto
next
  fix i1 i2 ins
  assume "tm = i1 # i2 # ins"
  from assms have "fetch tm (Suc s) b = (tm ! (2*s))"
    by (auto)
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s)"
    using assms(1) assms(3) assms(4) le_trans length_tm_le_mk_composable0
    by fastforce
  also have "(mk_composable0 tm)!(2*s) = (a, 0)"
  proof (cases "is_even (length tm)")
    case True
    then have "is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)" by (rule length_mk_composable0_gt2_even)

    from \<open>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (fix_jumps ((length (i1 # i2 # ins)) div 2) (i1#i2#ins))!(2*s)" by auto
    also have "... = (fst(a,s'),0)"

    proof (rule fix_jumps_nth_fix)
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "2 * s < length (i1 # i2 # ins)" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "(i1 # i2 # ins) ! (2 * s) = (a, s')" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)\<close>
      show "\<not>snd (a, s') \<le> length (i1 # i2 # ins) div 2" by auto
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (fst(a,s'),0)" by auto
    then have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (a,0)" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  next
    case False
    then have "\<not>is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "\<not>is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins) +1" by (rule length_mk_composable0_gt2_odd)
    from \<open>\<not>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (fix_jumps (((length (i1 # i2 # ins)) div 2)+1) ((i1#i2#ins)@[(Nop,0)]))!(2*s)" by auto
    also have "... = (fst(a,s'), 0)"
    proof (rule fix_jumps_nth_fix)
      from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s < length ((i1 # i2 # ins) @ [(Nop, 0)])" by auto
    next
      have "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s) = ((i1 # i2 # ins)) ! (2 * s)"
      proof (rule nth_append')
        from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s < length (i1 # i2 # ins)" by auto
      qed
      also from assms and \<open>tm = i1 # i2 # ins\<close> have "((i1 # i2 # ins)) ! (2 * s) = (a, s')" by auto
      finally show "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s) = (a, s')" by auto
    next
      from assms and \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length ((i1#i2#ins)) + 1\<close>
      have "s' > (length (i1 # i2 # ins) + 1) div 2" by auto
      with \<open>\<not>is_even (length (i1 # i2 # ins))\<close> have "s' > length (i1 # i2 # ins) div 2 + 1" by arith
      then show "\<not> snd (a, s') \<le> length (i1 # i2 # ins) div 2 + 1" by auto 
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s) = (a, 0)" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, 0)" by auto
  with assms show ?thesis by auto
qed

lemma fetch_mk_composable0_Oc_Suc_no_fix:
  assumes "b = Oc"
    and "2*s+1 < length tm"
    and "fetch tm (Suc s) b = (a, s')"

    and "s' \<le> length (mk_composable0 tm) div 2"
  shows "fetch (mk_composable0 tm) (Suc s) b = fetch tm (Suc s) b"
proof (rule mk_composable0.cases[of tm])
  assume "tm = []"
  with \<open>2*s+1 < length tm\<close> show ?thesis by auto
next
  fix i1
  assume "tm = [i1]"
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s+1)"
    using \<open>tm = [i1]\<close> assms(2) by auto
  also have "(mk_composable0 tm)!(2*s+1) = (a, s')"
  proof -
    from \<open>tm = [i1]\<close> have "length (mk_composable0 tm) = 2" by auto
    have "(mk_composable0 [i1])!(2*s+1) = (fix_jumps 1 [i1,(Nop,0)])!(2*s+1)" by auto
    also have "... = (a, s')"
    proof (rule fix_jumps_nth_no_fix)
      from assms and  \<open>tm = [i1]\<close> show "2 * s  +1 < length [i1, (Nop, 0)]" by auto
    next
      from assms and  \<open>tm = [i1]\<close> show "[i1, (Nop, 0)] ! (2 * s +1) = (a, s')" by auto
    next
      from assms and  \<open>tm = [i1]\<close> and \<open>length (mk_composable0 tm) = 2\<close> show "snd (a, s') \<le> 1" by auto
    qed
    finally have "(mk_composable0 [i1])!(2*s+1) = (a, s')" by auto
    with  \<open>tm = [i1]\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, s')" by auto
  with assms show ?thesis by auto
next
  fix i1 i2 ins
  assume "tm = i1 # i2 # ins"
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s+1)"
  proof -
    have "\<not> length (mk_composable0 tm) \<le> 2 * s + 1"
      by (meson assms(2) le_trans length_tm_le_mk_composable0 not_less)
    then show ?thesis
      by (simp add: assms(1))
  qed
  also have "(mk_composable0 tm)!(2*s+1) = (a, s')"
  proof (cases "is_even (length tm)")
    case True
    then have "is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)" by (rule length_mk_composable0_gt2_even)

    from \<open>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (fix_jumps ((length (i1 # i2 # ins)) div 2) (i1#i2#ins))!(2*s+1)" by auto
    also have "... = (a, s')"
    proof (rule fix_jumps_nth_no_fix)
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "2 * s+1 < length (i1 # i2 # ins)" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "(i1 # i2 # ins) ! (2 * s+1) = (a, s')" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)\<close>
      show "snd (a, s') \<le> length (i1 # i2 # ins) div 2" by auto
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (a, s')" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  next
    case False
    then have "\<not>is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "\<not>is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins) +1" by (rule length_mk_composable0_gt2_odd)

    from \<open>\<not>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (fix_jumps (((length (i1 # i2 # ins)) div 2)+1) ((i1#i2#ins)@[(Nop,0)]))!(2*s+1)" by auto
    also have "... = (a, s')"
    proof (rule fix_jumps_nth_no_fix)
      from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s +1< length ((i1 # i2 # ins) @ [(Nop, 0)])" by auto
    next
      have "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s+1) = ((i1 # i2 # ins)) ! (2 * s+1)"
      proof (rule nth_append')
        from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s+1 < length (i1 # i2 # ins)" by auto
      qed
      also from assms and \<open>tm = i1 # i2 # ins\<close> have "((i1 # i2 # ins)) ! (2 * s+1) = (a, s')" by auto
      finally show "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s+1) = (a, s')" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length ((i1#i2#ins)) + 1\<close>
      show "snd (a, s') \<le> length (i1 # i2 # ins) div 2 + 1" by auto 
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (a, s')" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, s')" by auto
  with assms show ?thesis by auto
qed


lemma fetch_mk_composable0_Oc_Suc_fix:
assumes "b = Oc"
    and "2*s+1 < length tm"
    and "fetch tm (Suc s) b = (a, s')"

    and "length (mk_composable0 tm) div 2 < s'"
shows "fetch (mk_composable0 tm) (Suc s) b = (a, 0)"
proof (rule mk_composable0.cases[of tm])
  assume "tm = []"
  with \<open>length tm > 2*s+1\<close> show ?thesis by auto
next
  fix i1
  assume "tm = [i1]"
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s+1)"
    using \<open>tm = [i1]\<close> assms(2) by auto
  also have "(mk_composable0 tm)!(2*s+1) = (a, 0)"
  proof -
    from \<open>tm = [i1]\<close> have "length (mk_composable0 tm) = 2" by auto
    have "(mk_composable0 [i1])!(2*s+1) = (fix_jumps 1 [i1,(Nop,0)])!(2*s+1)" by auto
    also have "... = (fst(a,s'), 0)"
    proof (rule fix_jumps_nth_fix)
      from assms and  \<open>tm = [i1]\<close> show "2 * s+1 < length [i1, (Nop, 0)]" by auto
    next
      from assms and  \<open>tm = [i1]\<close> show "[i1, (Nop, 0)] ! (2 * s+1) = (a, s')" by auto
    next
      from assms and  \<open>tm = [i1]\<close> and \<open>length (mk_composable0 tm) = 2\<close> show "\<not>snd (a, s') \<le> 1" by auto
    qed
    finally have "(mk_composable0 [i1])!(2*s+1) = (a, 0)" by auto
    with  \<open>tm = [i1]\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, 0)" by auto
  with assms show ?thesis by auto
next
  fix i1 i2 ins
  assume "tm = i1 # i2 # ins"
  from assms have "fetch tm (Suc s) b = (tm ! (2*s+1))"
    by (auto)
  have "fetch (mk_composable0 tm) (Suc s) b = (mk_composable0 tm)!(2*s+1)"
  proof -
    have "\<not> length (mk_composable0 tm) \<le> 2 * s + 1"
      by (meson assms(2) le_trans length_tm_le_mk_composable0 not_less)
    then show ?thesis
      by (simp add: assms(1))
  qed
  also have "(mk_composable0 tm)!(2*s+1) = (a, 0)"
  proof (cases "is_even (length tm)")
    case True
    then have "is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)" by (rule length_mk_composable0_gt2_even)

    from \<open>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (fix_jumps ((length (i1 # i2 # ins)) div 2) (i1#i2#ins))!(2*s+1)" by auto
    also have "... = (fst(a,s'),0)"

    proof (rule fix_jumps_nth_fix)
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "2 * s +1 < length (i1 # i2 # ins)" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> show "(i1 # i2 # ins) ! (2 * s +1) = (a, s')" by auto
    next
      from assms and  \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins)\<close>
      show "\<not>snd (a, s') \<le> length (i1 # i2 # ins) div 2" by auto
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (fst(a,s'),0)" by auto
    then have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (a,0)" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  next
    case False
    then have "\<not>is_even (length tm)" .
    with \<open>tm = i1 # i2 # ins\<close> have  "\<not>is_even (length (i1 # i2 # ins))" by auto
    then have "length (mk_composable0 (i1 # i2 # ins)) = length (i1#i2#ins) +1" by (rule length_mk_composable0_gt2_odd)
    from \<open>\<not>is_even (length (i1 # i2 # ins))\<close>
    have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (fix_jumps (((length (i1 # i2 # ins)) div 2)+1) ((i1#i2#ins)@[(Nop,0)]))!(2*s+1)" by auto
    also have "... = (fst(a,s'), 0)"
    proof (rule fix_jumps_nth_fix)
      from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s+1 < length ((i1 # i2 # ins) @ [(Nop, 0)])" by auto
    next
      have "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s +1) = ((i1 # i2 # ins)) ! (2 * s +1)"
      proof (rule nth_append')
        from assms and \<open>tm = i1 # i2 # ins\<close> show "2 * s +1 < length (i1 # i2 # ins)" by auto
      qed
      also from assms and \<open>tm = i1 # i2 # ins\<close> have "((i1 # i2 # ins)) ! (2 * s +1) = (a, s')" by auto
      finally show "((i1 # i2 # ins)@ [(Nop, 0)]) ! (2 * s +1) = (a, s')" by auto
    next
      from assms and \<open>tm = i1 # i2 # ins\<close> and \<open>length (mk_composable0 (i1 # i2 # ins)) = length ((i1#i2#ins)) + 1\<close>
      have "s' > (length (i1 # i2 # ins) + 1) div 2" by auto
      with \<open>\<not>is_even (length (i1 # i2 # ins))\<close> have "s' > length (i1 # i2 # ins) div 2 + 1" by arith
      then show "\<not> snd (a, s') \<le> length (i1 # i2 # ins) div 2 + 1" by auto 
    qed
    finally have "(mk_composable0 (i1 # i2 # ins))!(2*s+1) = (a, 0)" by auto
    with \<open>tm = i1 # i2 # ins\<close> show ?thesis by auto
  qed
  finally have "fetch (mk_composable0 tm) (Suc s) b = (a, 0)" by auto
  with assms show ?thesis by auto
qed


subsection \<open>Properties of function step0 with respect to function mk\_composable0\<close>

lemma length_mk_composable0_div2_lt_imp_length_tm_le_times2:
  assumes "length (mk_composable0 tm) div 2 < s'"
    and "s' = Suc s2"
  shows "length tm \<le> 2 * s2"
proof (cases "length tm")
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then have "length tm = Suc nat" .
  then show ?thesis
  proof (cases  "is_even (length tm)")
    case True
    then have "is_even (length tm)" .

    from  \<open>length (mk_composable0 tm) div 2 < s'\<close>
      and \<open>s' = Suc s2\<close> have "length (mk_composable0 tm) div 2 < Suc s2" by auto
    moreover from \<open>is_even (length tm)\<close> and \<open>length tm = Suc nat\<close>
    have "length (mk_composable0 tm) = length tm"
      by (auto simp add: length_mk_composable0_even)
    ultimately have "length tm div 2 < Suc s2" by auto
    with \<open>is_even (length tm)\<close> show ?thesis by (auto simp add: even_le_div2_imp_le_times_2)
  next
    case False
    then have "\<not> is_even (length tm)" .
    from  \<open>length (mk_composable0 tm) div 2 < s'\<close> and \<open>s' = Suc s2\<close>
    have "length (mk_composable0 tm) div 2 < Suc s2" by auto
    moreover from \<open>\<not>is_even (length tm)\<close>
      and \<open>length tm = Suc nat\<close> have "length (mk_composable0 tm) = length tm +1"
      by (auto simp add: length_mk_composable0_odd)
    ultimately have "(length tm +1) div 2 < Suc s2" by auto
    with \<open>\<not>is_even (length tm)\<close> show ?thesis by (auto simp add: odd_le_div2_imp_le_times_2)
  qed
qed

lemma jump_out_of_pgm_is_final_next_step:
  assumes "step0 (s, l, r) tm = (s', update a1 (l, r))"
    and "s' = Suc s2" and "length (mk_composable0 tm) div 2 < s'"
  shows "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm))"
proof -
  from \<open>length (mk_composable0 tm) div 2 < s'\<close> and \<open>s' = Suc s2\<close> have "length tm \<le> 2 * s2"
    by (rule length_mk_composable0_div2_lt_imp_length_tm_le_times2)
  with assms have  "step0 (step0 (s, l, r) tm) tm = step0 (s', update a1 (l, r)) tm" by auto
  also have "... = (0::nat, update a1 (l, r))"
  proof (cases "update a1 (l, r)")
    fix l2 r2
    assume "update a1 (l, r) = (l2, r2)"
    then show ?thesis 
    proof (cases "read r2")
      case Bk
      then have "read r2 = Bk" .
      moreover with \<open>length tm \<le> 2 * s2\<close> and \<open>s' = Suc s2\<close> fetch.simps
      have "fetch tm s' Bk = (Nop, 0::nat)" by auto
      ultimately show ?thesis by (auto simp add: \<open>update a1 (l, r) = (l2, r2)\<close> )
    next
      case Oc
      then have "read r2 = Oc" .
      moreover with \<open>length tm \<le> 2 * s2\<close> and \<open>s' = Suc s2\<close> fetch.simps
      have "fetch tm s' Oc = (Nop, 0::nat)" by auto
      ultimately show ?thesis by (auto simp add: \<open>update a1 (l, r) = (l2, r2)\<close> )
    qed
  qed
  finally have "step0 (step0 (s, l, r) tm) tm = (0, update a1 (l, r)) " by auto

  with \<open>step0 (s, l, r) tm = (s', update a1 (l, r))\<close> show ?thesis by auto
qed



lemma step0_mk_composable0_after_one_step:
  assumes "step0 (s, (l, r)) tm \<noteq> step0 (s, l, r) (mk_composable0 tm)"
  shows "step0 (step0 (s, (l, r)) tm) tm = (0, snd((step0 (s, (l, r)) tm))) \<and>
         step0 (s, l, r) (mk_composable0 tm)     = (0, snd((step0 (s, (l, r)) tm)))"
proof (cases "(read r)"; cases s)
  assume "read r = Bk" and "s = 0"
  show "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm)) \<and> step0 (s, l, r) (mk_composable0 tm) = (0, snd (step0 (s, l, r) tm))"
  proof (cases "length tm \<le> 2*s")
    case True
    with \<open>s = 0\<close> show ?thesis by auto
  next  
    case False
    then have "2 * s < length tm" by auto
    with \<open>s = 0\<close> show ?thesis by auto
  qed
next
  assume "read r = Oc" and "s = 0"
  show "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm)) \<and> step0 (s, l, r) (mk_composable0 tm) = (0, snd (step0 (s, l, r) tm))"
  proof (cases "length tm \<le> 2*s")
    case True
    then have "length tm \<le> 2 * s" .
    with \<open>s = 0\<close> show ?thesis by auto
  next  
    case False
    then have "2 * s < length tm" by auto
    with \<open>s = 0\<close> show ?thesis by auto
  qed
next
  fix s1
  assume "read r = Bk" and "s = Suc s1"
  show ?thesis
  proof (cases "length tm \<le> 2*s1")  (* both programs will fetch a Nop *)
    assume "length tm \<le> 2 * s1"
    with \<open>read r = Bk\<close> and \<open>s = Suc s1\<close> have "fetch tm (Suc s1) (read r) = (Nop, 0::nat)"
      by (auto)
    moreover have "fetch (mk_composable0 tm) (Suc s1) (read r) = (Nop, 0::nat)"
      by (rule fetch_mk_composable0_Bk_too_short_Suc)(auto simp add: \<open>read r = Bk\<close> \<open>length tm \<le> 2 * s1\<close>)
    ultimately have "fetch tm (Suc s1) (read r) = fetch (mk_composable0 tm) (Suc s1) (read r)" by auto
    with \<open>(read r) = Bk\<close> and \<open>s = Suc s1\<close> have "step0 (s, l, r) tm = step0 (s, l, r) (mk_composable0 tm)" by auto
    with assms have False by auto
    then show ?thesis by auto
  next
    assume "\<not> length tm \<le> 2 * s1"    (* a case hard to prove *)
      (* both programs will fetch some action in state s = Suc s1, which is explicitly specified in tm already*)
    then have  "2*s1 < length tm" by auto
    show "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm)) \<and>
          step0 (s, l, r) (mk_composable0 tm) = (0, snd (step0 (s, l, r) tm))"
    proof (cases "fetch tm (Suc s1) (read r)")
      fix a1 s'
      assume "fetch tm (Suc s1) (read r) = (a1, s')"
      show ?thesis
      proof (cases "s' \<le> length (mk_composable0 tm) div 2")
        assume "s' \<le> length (mk_composable0 tm) div 2"

        from \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
          and \<open>2*s1 < length tm\<close>
          and \<open>(read r) = Bk\<close>
          and \<open>s' \<le> length (mk_composable0 tm) div 2\<close>
        have "fetch (mk_composable0 tm) (Suc s1) (read r) = fetch tm (Suc s1) (read r)"
          using fetch_mk_composable0_Bk_Suc_no_fix by auto

        with \<open>(read r) = Bk\<close> and \<open>s = Suc s1\<close> have "step0 (s, l, r) tm = step0 (s, l, r) (mk_composable0 tm)" by auto
        with assms have False by auto
        then show ?thesis by auto
      next
        assume "\<not> s' \<le> length (mk_composable0 tm) div 2"
        then have "length (mk_composable0 tm) div 2 < s'" by auto
        then show ?thesis
        proof (cases s')
          assume "s' = 0"
          with \<open>length (mk_composable0 tm) div 2 < s'\<close> have False by auto
          then show ?thesis by auto
        next
          fix s2
          assume "s' = Suc s2"

          from \<open>(read r) = Bk\<close> and \<open>s = Suc s1\<close> and \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
          have "step0 (s, l, r) tm = (s', update a1 (l, r))" by auto

          from this and \<open>s' = Suc s2\<close> and \<open>length (mk_composable0 tm) div 2 < s'\<close>
          have "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm))"
            by (rule jump_out_of_pgm_is_final_next_step)
          moreover have "step0 (s, l, r) (mk_composable0 tm) = (0, snd (step0 (s, l, r) tm))"
          proof -
            from \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
              and \<open>2*s1 < length tm\<close>
              and \<open>(read r) = Bk\<close>
              and \<open>length (mk_composable0 tm) div 2 < s'\<close>
            have "fetch (mk_composable0 tm) (Suc s1) (read r) = (a1, 0)" using fetch_mk_composable0_Bk_Suc_fix by auto
            with  \<open>(read r) = Bk\<close> and \<open>s = Suc s1\<close> and \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
            show ?thesis by auto
          qed
          ultimately  show ?thesis by auto
        qed
      qed
    qed
  qed
next
  fix s1
  assume "read r = Oc" and "s = Suc s1"
  show ?thesis

  proof (cases "length tm \<le> 2*s1+1")  (* both programs will fetch a Nop *)
    assume "length tm \<le> 2 * s1+1"
    with \<open>read r = Oc\<close> and \<open>s = Suc s1\<close> have "fetch tm (Suc s1) (read r) = (Nop, 0::nat)"
      by (auto)
    moreover have "fetch (mk_composable0 tm) (Suc s1) (read r) = (Nop, 0::nat)"
    proof (rule fetch_mk_composable0_Oc_too_short_Suc)
      from \<open>(read r) = Oc\<close> show "(read r) = Oc" .
    next
      from \<open>length tm \<le> 2 * s1+1\<close> show "length tm \<le> 2 * s1+1" .
    qed
    ultimately have "fetch tm (Suc s1) (read r) = fetch (mk_composable0 tm) (Suc s1) (read r)" by auto
    with \<open>(read r) = Oc\<close> and \<open>s = Suc s1\<close> have "step0 (s, l, r) tm = step0 (s, l, r) (mk_composable0 tm)" by auto
    with assms have False by auto
    then show ?thesis by auto
  next
    assume "\<not> length tm \<le> 2 * s1+1"  (* a case hard to prove *)
      (* both programs will fetch some action in state s = Suc s1, which is explicitly specified in tm already*)
    then have  "2*s1+1 < length tm" by auto
    show "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm)) \<and>
          step0 (s, l, r) (mk_composable0 tm) = (0, snd (step0 (s, l, r) tm))"
    proof (cases "fetch tm (Suc s1) (read r)")
      fix a1 s'
      assume "fetch tm (Suc s1) (read r) = (a1, s')"
      show ?thesis
      proof (cases "s' \<le> length (mk_composable0 tm) div 2")
        assume "s' \<le> length (mk_composable0 tm) div 2"

        from \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
          and \<open>2*s1+1 < length tm\<close>
          and \<open>(read r) = Oc\<close>
          and \<open>s' \<le> length (mk_composable0 tm) div 2\<close>
        have "fetch (mk_composable0 tm) (Suc s1) (read r) = fetch tm (Suc s1) (read r)"
          using fetch_mk_composable0_Oc_Suc_no_fix by auto

        with \<open>(read r) = Oc\<close> and \<open>s = Suc s1\<close> have "step0 (s, l, r) tm = step0 (s, l, r) (mk_composable0 tm)" by auto
        with assms have False by auto
        then show ?thesis by auto

      next
        assume "\<not> s' \<le> length (mk_composable0 tm) div 2"
        then have "length (mk_composable0 tm) div 2 < s'" by auto
        then show ?thesis
        proof (cases s')
          assume "s' = 0"
          with \<open>length (mk_composable0 tm) div 2 < s'\<close> have False by auto
          then show ?thesis by auto
        next
          fix s2
          assume "s' = Suc s2"

          from \<open>(read r) = Oc\<close> and \<open>s = Suc s1\<close> and \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
          have "step0 (s, l, r) tm = (s', update a1 (l, r))" by auto

          from this and \<open>s' = Suc s2\<close> and \<open>length (mk_composable0 tm) div 2 < s'\<close>
          have "step0 (step0 (s, l, r) tm) tm = (0, snd (step0 (s, l, r) tm))"
            by (rule jump_out_of_pgm_is_final_next_step)
          moreover have "step0 (s, l, r) (mk_composable0 tm) = (0, snd (step0 (s, l, r) tm))"
          proof -
            from \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
              and \<open>2*s1+1 < length tm\<close>
              and \<open>(read r) = Oc\<close>
              and \<open>length (mk_composable0 tm) div 2 < s'\<close>
            have "fetch (mk_composable0 tm) (Suc s1) (read r) = (a1, 0)" using fetch_mk_composable0_Oc_Suc_fix by auto
            with  \<open>(read r) = Oc\<close> and \<open>s = Suc s1\<close> and \<open>fetch tm (Suc s1) (read r) = (a1, s')\<close>
            show ?thesis by auto
          qed
          ultimately  show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma step0_mk_composable0_eq_after_two_steps:
  assumes "step0 (s, (l, r)) tm \<noteq> step0 (s, l, r) (mk_composable0 tm)"
  shows "step0 (step0 (s, (l, r)) tm) tm = (0, snd((step0 (s, (l, r)) tm))) \<and>
         step0 (step0 (s, (l, r)) (mk_composable0 tm)) (mk_composable0 tm) = step0 (step0 (s, (l, r)) tm) tm"
proof -
  from assms have A: "step0 (step0 (s, (l, r)) tm) tm = (0, snd((step0 (s, (l, r)) tm))) \<and>
         step0 (s, l, r) (mk_composable0 tm)     = (0, snd((step0 (s, (l, r)) tm)))"
    by (rule step0_mk_composable0_after_one_step)
  from A have A1: "step0 (step0 (s, (l, r)) tm) tm = (0, snd((step0 (s, (l, r)) tm)))" by auto
  from A have A2: "step0 (s, l, r) (mk_composable0 tm) = (0, snd((step0 (s, (l, r)) tm)))" by auto

  show ?thesis
  proof (cases "snd((step0 (s, (l, r)) tm))")
    case (Pair a b)
    assume "snd (step0 (s, l, r) tm) = (a, b)"
    show ?thesis
    proof -
      from \<open>snd (step0 (s, l, r) tm) = (a, b)\<close> and \<open>step0 (s, l, r) (mk_composable0 tm) = (0, snd((step0 (s, (l, r)) tm)))\<close>
      have "step0 (s, l, r) (mk_composable0 tm) = (0, (a,b))" by auto

      then have "step0 (step0 (s, (l, r)) (mk_composable0 tm)) (mk_composable0 tm) = step0 (0, (a,b))  (mk_composable0 tm)" by auto
      also have "... = (0, (a,b))" by auto
      finally have "step0 (step0 (s, (l, r)) (mk_composable0 tm)) (mk_composable0 tm) = (0, (a,b))" by auto

      moreover from A1 and  \<open>snd (step0 (s, l, r) tm) = (a, b)\<close>
      have "step0 (step0 (s, (l, r)) tm) tm = (0, (a,b))" by auto

      ultimately have "step0 (step0 (s, (l, r)) (mk_composable0 tm)) (mk_composable0 tm) = step0 (step0 (s, (l, r)) tm) tm" by auto
      with A1 show ?thesis by auto
    qed
  qed
qed

(* ------------------------------------------------------------------ *)

subsection \<open>Properties of function steps0 with respect to function mk\_composable0\<close>

lemma "steps0 (s, (l, r)) tm 0 = steps0 (s, l, r) (mk_composable0 tm) 0"
  by auto

lemma mk_composable0_tm_at_most_one_diff_pre:
  assumes "steps0 (s, (l, r)) tm stp \<noteq> steps0 (s, l, r) (mk_composable0 tm) stp"
  shows "0<stp \<and> (\<exists>k. k<stp 
            \<and> (\<forall>i \<le> k. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i)
            \<and> (\<forall>j > k+1.
                    steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm (k+1))) \<and> 
                    steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j))"
proof -
  have "\<exists>k<stp. (\<forall>i\<le>k. \<not> steps0 (s, l, r) tm i \<noteq> steps0 (s, l, r) (mk_composable0 tm) i) \<and> steps0 (s, l, r) tm (Suc k) \<noteq> steps0 (s, l, r) (mk_composable0 tm) (Suc k)"
  proof (rule ex_least_nat_less)
    show "\<not> steps0 (s, l, r) tm 0 \<noteq> steps0 (s, l, r) (mk_composable0 tm) 0" by auto
  next
    from assms show "steps0 (s, l, r) tm stp \<noteq> steps0 (s, l, r) (mk_composable0 tm) stp" by auto
  qed
  then obtain k where w_k: "k < stp \<and> (\<forall>i\<le>k. \<not> steps0 (s, l, r) tm i \<noteq> steps0 (s, l, r) (mk_composable0 tm) i) \<and> steps0 (s, l, r) tm (Suc k) \<noteq> steps0 (s, l, r) (mk_composable0 tm) (Suc k)" by blast
  from w_k have F1: "k < stp" by auto
  from w_k have F2: "\<And>i. i\<le>k \<Longrightarrow> \<not> steps0 (s, l, r) tm i \<noteq> steps0 (s, l, r) (mk_composable0 tm) i" by auto
  from w_k have F3: "steps0 (s, l, r) tm (k + 1) \<noteq> steps0 (s, l, r) (mk_composable0 tm) (k + 1)" by auto

  from F3 have F3': "(steps0 (s, l, r) tm (Suc k)) \<noteq> (steps0 (s, l, r) (mk_composable0 tm) (Suc k))" by auto

  have "\<not>(steps0 (s, l, r) tm k \<noteq> steps0 (s, l, r) (mk_composable0 tm) k)" using F2 by auto
  then have F4: "steps0 (s, l, r) tm k = steps0 (s, l, r) (mk_composable0 tm) k" by auto

  have X1: "steps0 (s, l, r) (mk_composable0 tm) (Suc k) = step0 (steps0 (s, l, r) (mk_composable0 tm) k) (mk_composable0 tm)" by (rule step_red)
  have X2: "steps0 (s, l, r) tm (Suc k) = step0 (steps0 (s, l, r) tm k) tm" by (rule step_red)

  from X1 and X2 and F3'
  have "step0 (steps0 (s, l, r) tm k) tm \<noteq> step0 (steps0 (s, l, r) (mk_composable0 tm) k) (mk_composable0 tm)" by auto

  then have "\<exists> sk lk rk. steps0 (s, l, r) tm k = (sk, lk, rk) \<and>
                         steps0 (s, l, r) (mk_composable0 tm) k = (sk, lk, rk) \<and>
                         step0 (sk, (lk, rk)) tm \<noteq> step0 (sk, lk, rk) (mk_composable0 tm)"
  proof (cases "steps0 (s, l, r) tm k")
    case (fields s' l' r')
    then have "steps0 (s, l, r) tm k = (s', l', r')" .
    moreover with \<open>step0 (steps0 (s, l, r) tm k) tm \<noteq> step0 (steps0 (s, l, r) (mk_composable0 tm) k) (mk_composable0 tm)\<close> and F4
    have "step0 (s', (l', r')) tm \<noteq> step0 (s', l', r') (mk_composable0 tm)" by auto

    moreover from \<open>steps0 (s, l, r) tm k = (s', l', r')\<close> and F4
    have "steps0 (s, l, r) (mk_composable0 tm) k = (s', l', r')" by auto
    ultimately have "steps0 (s, l, r) tm k = (s', l', r') \<and> steps0 (s, l, r) (mk_composable0 tm) k = (s', l', r') \<and>
                     step0 (s', (l', r')) tm \<noteq> step0 (s', l', r') (mk_composable0 tm)" by auto

    then show ?thesis by blast
  qed

  then obtain sk lk rk where
    w_sk_lk_rk: "steps0 (s, l, r) tm k = (sk, lk, rk) \<and>
                 steps0 (s, l, r) (mk_composable0 tm) k = (sk, lk, rk) \<and>
                 step0 (sk, (lk, rk)) tm \<noteq> step0 (sk, lk, rk) (mk_composable0 tm)" by blast

  have Y1: "step0 (step0 (sk, (lk, rk)) tm) tm = (0, snd((step0 (sk, (lk, rk)) tm))) \<and>
         step0 (step0 (sk, (lk, rk)) (mk_composable0 tm)) (mk_composable0 tm) = step0 (step0 (sk, (lk, rk)) tm) tm"
  proof (rule  step0_mk_composable0_eq_after_two_steps)
    from w_sk_lk_rk show "step0 (sk, lk, rk) tm \<noteq> step0 (sk, lk, rk) (mk_composable0 tm)" by auto
  qed

  from Y1 and w_sk_lk_rk
  have "step0 (step0 (steps0 (s, l, r) tm k) tm) tm = (0, snd((step0 (steps0 (s, l, r) tm k) tm)))" by auto

  from Y1 and w_sk_lk_rk
  have "step0 (step0 (steps0 (s, l, r) (mk_composable0 tm) k) (mk_composable0 tm)) (mk_composable0 tm) = step0 (step0 (steps0 (s, l, r) tm k) tm) tm" by auto

  have "steps0 (s, l, r) (mk_composable0 tm) (k+2) = step0 (step0 (steps0 (s, l, r) (mk_composable0 tm) k) (mk_composable0 tm)) (mk_composable0 tm)"
    by (auto simp add: step_red[symmetric])

  have "steps0 (s, l, r) tm (k+2) = step0 (step0 (steps0 (s, l, r) tm k) tm) tm"
    by (auto simp add: step_red[symmetric])

  from \<open>step0 (step0 (steps0 (s, l, r) tm k) tm) tm = (0, snd((step0 (steps0 (s, l, r) tm k) tm)))\<close>
    and \<open>steps0 (s, l, r) tm (k+2) = step0 (step0 (steps0 (s, l, r) tm k) tm) tm\<close>
  have "steps0 (s, l, r) tm (k+2) = (0, snd((step0 (steps0 (s, l, r) tm k) tm)))" by auto
  then have N1: "steps0 (s, l, r) tm (k+2) = (0, snd(steps0 (s, l, r) tm (k+1)))" by (auto simp add: step_red[symmetric])

  from \<open>step0 (step0 (steps0 (s, l, r) (mk_composable0 tm) k) (mk_composable0 tm)) (mk_composable0 tm) = step0 (step0 (steps0 (s, l, r) tm k) tm) tm\<close>
  have N2: "steps0 (s, l, r) (mk_composable0 tm) (k+2) = steps0 (s, l, r) tm (k+2)" by (auto simp add: step_red[symmetric])

  have N4: "\<forall>j > k+1.
         steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm (k+1))) \<and> 
         steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j"
  proof
    fix j
    show "k + 1 < j \<longrightarrow> steps0 (s, l, r) tm j = (0, snd (steps0 (s, l, r) tm (k+1))) \<and> steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j"
    proof (induct j)
      case 0
      then show ?case by auto
    next
      fix  j
      assume IV: "k + 1 < j \<longrightarrow> steps0 (s, l, r) tm j = (0, snd (steps0 (s, l, r) tm (k+1))) \<and> steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j"
      show "k + 1 < Suc j \<longrightarrow> steps0 (s, l, r) tm (Suc j) = (0, snd (steps0 (s, l, r) tm (k+1))) \<and> steps0 (s, l, r) (mk_composable0 tm) (Suc j) = steps0 (s, l, r) tm (Suc j)"
      proof
        assume "k + 1 < Suc j"
        then have "k + 1 \<le> j" by arith
        then have "k + 1 = j \<or> k+1 < j" by arith 
        then show "steps0 (s, l, r) tm (Suc j) = (0, snd (steps0 (s, l, r) tm (k+1))) \<and> steps0 (s, l, r) (mk_composable0 tm) (Suc j) = steps0 (s, l, r) tm (Suc j)"
        proof
          assume "k + 1 = j"
          with N1 and N2 show "steps0 (s, l, r) tm (Suc j) = (0, snd (steps0 (s, l, r) tm (k+1))) \<and>
                               steps0 (s, l, r) (mk_composable0 tm) (Suc j) = steps0 (s, l, r) tm (Suc j)"
            by force
        next
          assume "k + 1 < j"
          with IV
          have Y4: "steps0 (s, l, r) tm j = (0, snd (steps0 (s, l, r) tm (k+1))) \<and> steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j" by auto
          show "steps0 (s, l, r) tm (Suc j) = (0, snd (steps0 (s, l, r) tm (k+1))) \<and> steps0 (s, l, r) (mk_composable0 tm) (Suc j) = steps0 (s, l, r) tm (Suc j)"
          proof (cases " snd (steps0 (s, l, r) tm (k+1))")
            case (Pair a b)
            then have "snd (steps0 (s, l, r) tm (k + 1)) = (a, b)" .
            with Y4 have "steps0 (s, l, r) tm j = (0,a,b) \<and> steps0 (s, l, r) (mk_composable0 tm) j = (0,a,b)" by auto
            then have "steps0 (s, l, r) tm (j+1) = (0,a,b) \<and> steps0 (s, l, r) (mk_composable0 tm) (j+1) = (0,a,b)"
            proof
              assume "steps0 (s, l, r) tm j = (0, a, b)" and "steps0 (s, l, r) (mk_composable0 tm) j = (0, a, b)"
              show "steps0 (s, l, r) tm (j + 1) = (0, a, b) \<and> steps0 (s, l, r) (mk_composable0 tm) (j + 1) = (0, a, b)"
              proof
                from \<open>steps0 (s, l, r) tm j = (0, a, b)\<close> show "steps0 (s, l, r) tm (j + 1) = (0, a, b)" by (rule stable_config_after_final_add_2)
              next
                from \<open>steps0 (s, l, r) (mk_composable0 tm) j = (0, a, b)\<close> show "steps0 (s, l, r) (mk_composable0 tm) (j + 1) = (0, a, b)" by (rule stable_config_after_final_add_2)
              qed
            qed       
            then have "steps0 (s, l, r) tm (Suc j) = (0, a, b) \<and> steps0 (s, l, r) (mk_composable0 tm) (Suc j) = (0, a, b)" by auto
            with \<open>snd (steps0 (s, l, r) tm (k + 1)) = (a, b)\<close> show ?thesis by auto
          qed
        qed
      qed
    qed
  qed

  from F1 and F2 and N4 show ?thesis
    by (metis neq0_conv not_less_zero)
qed

(* ----------------- *)

lemma mk_composable0_tm_at_most_one_diff:
  assumes "steps0 (s, l, r) (mk_composable0 tm) stp \<noteq> steps0 (s, (l, r)) tm stp"
  shows "0<stp \<and>  
         (\<forall>i < stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
         (\<forall>j > stp. steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm stp)) \<and> 
                    steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j)"
proof -
  from assms have "steps0 (s, (l, r)) tm stp \<noteq> steps0 (s, l, r) (mk_composable0 tm) stp" by auto
  then have A:
    "0<stp \<and> (\<exists>k. k<stp 
            \<and> (\<forall>i \<le> k. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i)
            \<and> (\<forall>j > k+1.
                    steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm (k+1))) \<and> 
                    steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j))"
    by (rule mk_composable0_tm_at_most_one_diff_pre)
  then have F1: "0<stp" by auto
  from A have "(\<exists>k. k<stp 
            \<and> (\<forall>i \<le> k. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i)
            \<and> (\<forall>j > k+1.
                    steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm (k+1))) \<and> 
                    steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j))" by auto
  then obtain k where w_k:
    "k<stp 
            \<and> (\<forall>i \<le> k. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i)
            \<and> (\<forall>j > k+1.
                    steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm (k+1))) \<and> 
                    steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j)" by blast
  then have "stp = k+1 \<or> k+1 < stp" by arith
  then show ?thesis
  proof
    assume "stp = k+1"
    show ?thesis
    proof
      from F1 show "0 < stp" by auto
    next
      from \<open>stp = k+1\<close> and w_k
      show  "(\<forall>i<stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
    (\<forall>j>stp. steps0 (s, l, r) tm j = (0, snd (steps0 (s, l, r) tm stp)) \<and> steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j)" by auto
    qed
  next
    assume "k+1 < stp"
    with w_k and assms have False by auto
    then show ?thesis by auto
  qed
qed


lemma mk_composable0_tm_at_most_one_diff':
  assumes "steps0 (s, l, r) (mk_composable0 tm) stp \<noteq> steps0 (s, (l, r)) tm stp"
  shows "0 < stp \<and> (\<exists>fl fr. snd(steps0 (s, l, r) tm stp) = (fl, fr) \<and>      
                   (\<forall>i < stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
                   (\<forall>j > stp. steps0 (s, l, r)  tm         j = (0, fl, fr) \<and> 
                              steps0 (s, l, r) (mk_composable0 tm) j = (0, fl, fr) ))"
proof -
  from assms have major: "0 < stp \<and>  
         (\<forall>i < stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
         (\<forall>j > stp. steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm stp)) \<and> 
                    steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j)"
    by (rule mk_composable0_tm_at_most_one_diff)
  from major have F1: "0 < stp" by auto
  from major have F2: "(\<forall>i < stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
                       (\<forall>j > stp. steps0 (s, l, r) tm (j) = (0, snd(steps0 (s, l, r) tm stp)) \<and> 
                                  steps0 (s, l, r) (mk_composable0 tm) j = steps0 (s, l, r) tm j)" by auto
  then have "snd(steps0 (s, l, r) tm stp) = (fst(snd(steps0 (s, l, r) tm stp)), snd(snd(steps0 (s, l, r) tm stp)) )" by auto
  with F2 have "snd(steps0 (s, l, r) tm stp) = (fst(snd(steps0 (s, l, r) tm stp)), snd(snd(steps0 (s, l, r) tm stp)) ) \<and>
                       (\<forall>i < stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
                       (\<forall>j > stp. steps0 (s, l, r) tm j = (0, (fst(snd(steps0 (s, l, r) tm stp)), snd(snd(steps0 (s, l, r) tm stp)) )) \<and>
                                  steps0 (s, l, r) (mk_composable0 tm) j = (0, (fst(snd(steps0 (s, l, r) tm stp)), snd(snd(steps0 (s, l, r) tm stp)) )))"
    by auto
  then have  "(\<exists>fl fr.  snd(steps0 (s, l, r) tm stp) = (fl, fr) \<and>
                       (\<forall>i < stp. steps0 (s, l, r) (mk_composable0 tm) i = steps0 (s, l, r) tm i) \<and>
                       (\<forall>j > stp. steps0 (s, l, r) tm j = (0, fl, fr) \<and>
                                  steps0 (s, l, r) (mk_composable0 tm) j = (0, fl, fr)))" by blast
  with F1 show ?thesis by auto
qed

end

