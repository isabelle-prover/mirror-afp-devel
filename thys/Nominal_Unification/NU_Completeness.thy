(*<*)
theory NU_Completeness
imports NU_Soundness
begin
(*>*)

section\<open>Completeness\<close>

text\<open>Defines a reflexive-transitive relation from Freshness and Nominal Equational decomposition
and an inductive schema for proving completeness.\<close>

text\<open>The reflexive-transitive closures of sred and cred.\<close>

inductive sred_rtc :: "problem_type \<Rightarrow> substs \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto>\<^sup>* _" [80,80,80] 80)
  where
sred_refl[intro!]: "P1 \<turnstile> [] \<leadsto>\<^sup>* P1" |
sred_rtc_step[intro!]: "\<lbrakk>P1 \<turnstile> s1 \<leadsto> P2; P2 \<turnstile> s2 \<leadsto>\<^sup>* P3\<rbrakk> \<Longrightarrow> P1 \<turnstile> (s2 \<bullet> s1) \<leadsto>\<^sup>* P3"


inductive cred_rtc :: "problem_type \<Rightarrow> fresh_envs \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow>\<^sup>* _ " [80,80,80] 80)
  where
cred_refl[intro!] : "P1 \<turnstile> {} \<rightarrow>\<^sup>* P1" |
cred_rtc_step[intro!] : "\<lbrakk>P1 \<turnstile> nabla1 \<rightarrow> P2; P2 \<turnstile> nabla2 \<rightarrow>\<^sup>* P3\<rbrakk> \<Longrightarrow> P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P3"

text\<open>Either the measure reduces or the problem stays the same under equation reductions.\<close>

lemma rank_r_sred_rtc:
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2"
  shows "(P2, P1) \<in> rank_r \<or> P1 = P2"
using assms
proof (induct rule: sred_rtc.induct)
  case (sred_refl P1)
  then show "(P1, P1) \<in> rank_r \<or> P1 = P1" by simp
next
  case (sred_rtc_step P1 s1 P' s2 P2)
  then have "(P', P1) \<in> rank_r"
    using rank_r_sred by blast
  moreover have "(P2, P') \<in> rank_r \<or> P' = P2"
    using sred_rtc_step by simp
  ultimately show "(P2, P1) \<in> rank_r \<or> P1 = P2"
    using sred_rtc_step rank_r_trans by blast
qed

text\<open>If the problem does not change under the reflexive-transitive closure of sred,
the substitution must be empty.\<close>

lemma sred_rtc_no_cycle:
  assumes "P \<turnstile> s \<leadsto>\<^sup>* P"
  shows "s = []"
proof(rule ccontr)
  assume "s \<noteq> []"
  hence "(P,P) \<in> rank_r"
  proof(cases rule: sred_rtc.cases[OF assms])
    case (1 P1)
    then show ?thesis
      using \<open>s \<noteq> []\<close> by auto
  next
    case (2 P1 s1 P2 s2 P3)
    hence "(P2,P1) \<in> rank_r" 
      using rank_r_sred by simp
    moreover have "P1 = P3" 
      using 2(1,3) by simp
    moreover have "(P3, P2) \<in> rank_r \<or> P2=P3"
      using 2(5) rank_r_sred_rtc by simp
    ultimately have "(P3,P3) \<in> rank_r" 
      using rank_r_trans by blast
    then show "(P, P) \<in> rank_r" 
      using 2(3) by simp
  qed
  thus "False" using wf_rank_r by simp
qed

text\<open>If P1 reduces to a diferent P2 under steps of sred, then it reduces via \<open>red_plus\<close>.\<close>

lemma sred_rtc_to_redplus:
  assumes "P1 \<noteq> P2"  "P1 \<turnstile> s \<leadsto>\<^sup>* P2"
  shows "P1 \<Turnstile> ({}, s) \<Rightarrow> P2"
  using assms
proof(induct rule: sred_rtc.induct[OF assms(2)])
  case (1 P1)
  then show ?case by simp
next
  case (2 P1 s1 P' s2 P2)
  then show "P1 \<Turnstile> ({}, s2 \<bullet> s1) \<Rightarrow> P2"
    proof(cases "P' = P2")
      case True
      with 2(1,2) have 
        i: "P1 \<turnstile> s1 \<leadsto> P2" "P2 \<turnstile> s2 \<leadsto>\<^sup>* P2" by simp+
      hence "s2 = []" 
        using sred_rtc_no_cycle by simp
      with i have "P1 \<turnstile> (s2\<bullet>s1) \<leadsto> P2" by simp
      then show "P1 \<Turnstile> ({}, s2 \<bullet> s1) \<Rightarrow> P2 " 
        using sred_single by simp
    next
      case False
      with 2(2,3) have "P' \<Turnstile> ({}, s2) \<Rightarrow> P2" 
        by simp
      with 2(1) show "P1 \<Turnstile> ({}, s2 \<bullet> s1) \<Rightarrow> P2" 
        using sred_step by simp
    qed
qed

text\<open>The following two lemmas guarantee that we don't apply any non-trivial step of equational
reductions after applying a freshness reduction.\<close>

lemma no_nontrivial_sred_after_cred_aux:
  assumes "P1 \<turnstile> nabla \<rightarrow> P2" and "P2 \<turnstile> s \<leadsto>\<^sup>* P3"
  shows "P2 = P3"
  using assms
proof(induct rule: sred_rtc.induct[OF assms(2)])
  case (1 P2)
  then show ?case by simp
next
  case (2 P2 s' P' s2 P3)
  hence "fst P2 = []"
    using c_red_eqs_empty by auto
  moreover have "fst P2 \<noteq> []" 
    using 2(1) sred_eqs_not_empty by simp
  ultimately have False by auto
  then show ?case by simp
qed

lemma no_nontrivial_sred_after_cred:
  assumes "P1 \<turnstile> nabla1 \<rightarrow> P2"
    and "P2 \<turnstile> s \<leadsto>\<^sup>* P'" and "P' \<turnstile> nabla2 \<rightarrow>\<^sup>* P3"
  shows "P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P3"
  using assms
proof-
  from assms(1,2) have "P2 = P'" 
    using no_nontrivial_sred_after_cred_aux by simp
  hence "P2 \<turnstile> nabla2 \<rightarrow>\<^sup>* P3" 
    using assms(3) by simp
  with assms(1) show "P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P3"
    using cred_rtc_step by simp
qed

text\<open>If there is a reduction from P1 to P2 via \<open>red_plus\<close>, we can split into equational reductions
first and freshness reductions after.\<close>

lemma red_plus_decompose:
  assumes "P1 \<Turnstile> (nabla, s) \<Rightarrow> P2"
  shows "\<exists> P3. P1 \<turnstile> s \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla \<rightarrow>\<^sup>* P2"
  using assms
proof (induction P1\<equiv>"P1" nablas\<equiv>"(nabla, s)" P2\<equiv>"P2" arbitrary: nabla s P1 P2 rule: red_plus.induct)
  case (sred_single P1 s1 P2)
  hence "P1 \<turnstile> s1 \<leadsto>\<^sup>* P2"
    using sred_rtc_step[OF sred_single sred_refl] by simp
  moreover have "P2 \<turnstile> {} \<rightarrow>\<^sup>* P2"
   using cred_refl by simp
  ultimately show "\<exists>P3. P1 \<turnstile> s1 \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> {} \<rightarrow>\<^sup>* P2" by blast
next
  case (cred_single P1 nabla1 P2)
  hence "P1 \<turnstile> nabla1 \<rightarrow>\<^sup>* P2"
    using cred_rtc_step[OF cred_single cred_refl] by simp
  moreover have "P1 \<turnstile> [] \<leadsto>\<^sup>* P1"
    using sred_refl by simp
  ultimately show "\<exists>P3. P1 \<turnstile> [] \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla1 \<rightarrow>\<^sup>* P2" by blast
next
  case (sred_step P1 s1 P' nabla2 s2 P2)
  have "P1 \<turnstile> s1 \<leadsto> P'" by fact
  moreover obtain P3 where
    IH: "P' \<turnstile> s2 \<leadsto>\<^sup>* P3" "P3 \<turnstile> nabla2 \<rightarrow>\<^sup>* P2"
    using sred_step(3) by auto
  ultimately have "P1 \<turnstile> s2 \<bullet> s1 \<leadsto>\<^sup>* P3" 
    using sred_rtc_step by simp
  with IH(2) show "\<exists>P3. P1 \<turnstile> s2 \<bullet> s1 \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla2 \<rightarrow>\<^sup>* P2"
    by blast
next
  case (cred_step P1 nabla1 P' nabla2 P2)
  have i: "P1 \<turnstile> nabla1 \<rightarrow> P'" by fact
  moreover obtain P3 where
    IH: "P' \<turnstile> [] \<leadsto>\<^sup>* P3" "P3 \<turnstile> nabla2 \<rightarrow>\<^sup>* P2"
    using cred_step(3) by auto
  ultimately have "P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P2"
    using no_nontrivial_sred_after_cred by simp
  moreover have "P1 \<turnstile> [] \<leadsto>\<^sup>* P1"
    using sred_refl by simp
  ultimately show "\<exists>P3. P1 \<turnstile> [] \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P2"
    by blast
qed

text\<open>A form of transitivity of \<open>red_plus\<close>.\<close>

lemma red_plus_transitivity:
  assumes "P1 \<Turnstile> (nabla1, s1) \<Rightarrow> P2"
      and "P2 \<Turnstile> (nabla2, s2) \<Rightarrow> P3"
    shows "\<exists> nabla3 s3. P1 \<Turnstile> (nabla3, s3) \<Rightarrow> P3"
  using assms
proof (induction rule: red_plus.induct[OF assms(1)])
  case (2 P1 nabla1 P2)
  then obtain P' where
  i: "P2 \<turnstile> s2 \<leadsto>\<^sup>* P'"
    using red_plus_decompose by blast
  with 2(1) have "P2 = P'" 
   using no_nontrivial_sred_after_cred_aux by simp
  hence "s2 = []" 
    using i(1) sred_rtc_no_cycle by simp
  hence "P2 \<Turnstile> (nabla2, []) \<Rightarrow> P3" 
    using 2(3) by simp
  with 2(1) show "\<exists>nabla3 s3. P1 \<Turnstile> (nabla3, s3) \<Rightarrow> P3"
    using cred_step by auto
next
  case (4 P1 nabla P' nabla' P2)
  then obtain nabla3 s3 where
    P_prime_to_P3: "P' \<Turnstile> (nabla3, s3) \<Rightarrow> P3" by auto
  then obtain P'' where "P' \<turnstile> s3 \<leadsto>\<^sup>* P''" "P'' \<turnstile> nabla3 \<rightarrow>\<^sup>* P3"
    using red_plus_decompose by blast
  with 4(1) have "P' = P''" 
    using  no_nontrivial_sred_after_cred_aux by simp
  moreover have "s3 =[]"
    using \<open>P' \<turnstile> s3 \<leadsto>\<^sup>* P''\<close> sred_rtc_no_cycle calculation by simp
  hence "P' \<Turnstile> (nabla3, []) \<Rightarrow> P3" 
    using P_prime_to_P3 by simp
  with 4(1) show "\<exists>nabla3 s3. P1 \<Turnstile> (nabla3, s3) \<Rightarrow> P3"
    using cred_step by auto
qed (auto)



text\<open>Every problem has a normal form.\<close>

lemma normal_form_exists:
  shows "P \<in> stuck \<or> (\<exists> P2 nabla s. P \<Turnstile>(nabla,s)\<Rightarrow>P2 \<and> P2\<in>stuck )"
proof(induction P rule: wf_induct_rule[OF wf_rank_r])
  case (1 P)
  then show "P \<in> stuck \<or> (\<exists>P2 nabla s. P \<Turnstile> (nabla, s) \<Rightarrow> P2  \<and> P2 \<in> stuck)"
  proof (cases "P \<in> stuck")
    case True
    then show "P \<in> stuck \<or> (\<exists>P2 nabla s. P \<Turnstile> (nabla, s) \<Rightarrow> P2  \<and> P2 \<in> stuck)" by simp
  next
    case False
    then obtain P' nabla s where P_to_P_prime:
      "P \<Turnstile>(nabla,s)\<Rightarrow>P'"
      unfolding stuck_def by auto
    hence "(P', P) \<in> rank_r"
      using rank_r_red_plus by simp
    hence aux: "P' \<in> stuck \<or> (\<exists>P2 nabla s. P' \<Turnstile> (nabla, s) \<Rightarrow> P2 \<and> P2 \<in> stuck)"
      using 1 by simp
    then show "P \<in> stuck \<or> (\<exists>P2 nabla s. P \<Turnstile> (nabla, s) \<Rightarrow> P2  \<and> P2 \<in> stuck)"
    proof(cases "P' \<in> stuck")
      case True
      then show ?thesis 
        using P_to_P_prime by blast
    next
      case False
      then obtain P2 nabla' s' where
      P_prime_to_P2: "P' \<Turnstile> (nabla', s') \<Rightarrow> P2" "P2 \<in> stuck"
        using aux by auto
      then obtain nabla1 s1 where "P \<Turnstile> (nabla1, s1) \<Rightarrow> P2" "P2\<in> stuck"
        using P_to_P_prime red_plus_transitivity by blast
      then show ?thesis by blast
    qed
  qed
qed


text\<open>The procedure is complete, i.e., if a non-empty problem has a solution, then \<open>red_plus\<close> finds
the most general solution.\<close>

theorem completeness:
  assumes "P1 \<noteq> ([],[])" "U P1 \<noteq> {}"
  shows "\<exists> nabla' s'. P1 \<Turnstile> (nabla', s') \<Rightarrow> ([],[]) \<and> mgu P1 (nabla', s')"
proof-
  have P1_not_stuck: "P1 \<notin> stuck" 
  proof
    assume "P1\<in> stuck"
    hence "P1 = ([],[])\<or> fail P1" 
      unfolding stuck_equiv by simp
    hence "P1 =([],[])"
      using assms(2) fail_then_empty by blast
    thus False using assms(1) by simp
  qed
  then obtain P2 nabla' s' where 
    normal_form: "P1 \<Turnstile> (nabla', s') \<Rightarrow> P2" "P2 \<in> stuck"
    using normal_form_exists by blast
  hence "P2 \<in> normal_form P1" 
    using P1_not_stuck unfolding normal_form_def by auto
  hence "P2=([],[])"
    using not_empty_then_not_fail[OF assms(2)] normal_form(2) stuck_equiv by auto
  with normal_form(1) have "P1 \<Turnstile> (nabla', s') \<Rightarrow> ([],[])" by simp
  moreover have "mgu P1 (nabla',s')" 
    using mgu calculation by simp
  ultimately show "\<exists>nabla' s'. P1 \<Turnstile> (nabla', s') \<Rightarrow> ([], [])  \<and> mgu P1 (nabla', s')"
    by auto
qed
  

(*<*)
end
(*>*)