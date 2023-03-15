theory LexicalVals3
  imports Lexer3 "HOL-Library.Sublist"
begin

section \<open> Sets of Lexical Values \<close>

text \<open>
  Shows that lexical values are finite for a given regex and string.
\<close>

definition
  LV :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> ('a val) set"
where  "LV r s \<equiv> {v. \<turnstile> v : r \<and> flat v = s}"

lemma LV_simps:
  shows "LV Zero s = {}"
  and   "LV One s = (if s = [] then {Void} else {})"
  and   "LV (Atom c) s = (if s = [c] then {Atm c} else {})"
  and   "LV (Plus r1 r2) s = Left ` LV r1 s \<union> Right ` LV r2 s"
  and   "LV (NTimes r 0) s = (if s = [] then {Stars []} else {})"
  and   "LV (Rec l r) s = {Recv l v | v. v \<in> LV r s}"
  and   "LV (Charset cs) s = (if length s = 1 \<and> (hd s) \<in> cs then {Atm (hd s)} else {})"
unfolding LV_def
  apply(auto intro: Prf.intros elim: Prf.cases)
  apply(simp add: Prf_NTimes_empty)
  by (metis Suc_length_conv length_0_conv list.sel(1))  

abbreviation
  "Prefixes s \<equiv> {s'. prefix s' s}"

abbreviation
  "Suffixes s \<equiv> {s'. suffix s' s}"

abbreviation
  "SSuffixes s \<equiv> {s'. strict_suffix s' s}"

lemma Suffixes_cons [simp]:
  shows "Suffixes (c # s) = Suffixes s \<union> {c # s}"
by (auto simp add: suffix_def Cons_eq_append_conv)


lemma finite_Suffixes: 
  shows "finite (Suffixes s)"
by (induct s) (simp_all)

lemma finite_SSuffixes: 
  shows "finite (SSuffixes s)"
proof -
  have "SSuffixes s \<subseteq> Suffixes s"
   unfolding strict_suffix_def suffix_def by auto
  then show "finite (SSuffixes s)"
   using finite_Suffixes finite_subset by blast
qed

lemma finite_Prefixes: 
  shows "finite (Prefixes s)"
proof -
  have "finite (Suffixes (rev s))" 
    by (rule finite_Suffixes)
  then have "finite (rev ` Suffixes (rev s))" by simp
  moreover
  have "rev ` (Suffixes (rev s)) = Prefixes s"
  unfolding suffix_def prefix_def image_def
   by (auto)(metis rev_append rev_rev_ident)+
  ultimately show "finite (Prefixes s)" by simp
qed

lemma LV_STAR_finite:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (Star r) s)"
proof(induct s rule: length_induct)
  fix s::"'a list"
  assume "\<forall>s'. length s' < length s \<longrightarrow> finite (LV (Star r) s')"
  then have IH: "\<forall>s' \<in> SSuffixes s. finite (LV (Star r) s')"
    by (force simp add: strict_suffix_def suffix_def) 
  define f where "f \<equiv> \<lambda>(v::'a val, vs). Stars (v # vs)"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r s'"
  define S2 where "S2 \<equiv> \<Union>s2 \<in> SSuffixes s. Stars -` (LV (Star r) s2)"
  have "finite S1" using assms
    unfolding S1_def by (simp_all add: finite_Prefixes)
  moreover 
  with IH have "finite S2" unfolding S2_def
    by (auto simp add: finite_SSuffixes inj_on_def finite_vimageI)
  ultimately 
  have "finite ({Stars []} \<union> f ` (S1 \<times> S2))" by simp
  moreover 
  have "LV (Star r) s \<subseteq> {Stars []} \<union> f ` (S1 \<times> S2)" 
  unfolding S1_def S2_def f_def
  unfolding LV_def image_def prefix_def strict_suffix_def 
  apply(auto)
  apply(case_tac x)
  apply(auto elim: Prf_elims)
  apply(erule Prf_elims)
  apply(auto)
  apply(case_tac vs)
  apply(auto intro: Prf.intros)  
  apply(rule exI)
  apply(rule conjI)
  apply(rule_tac x="flat a" in exI)
  apply(rule conjI)
  apply(rule_tac x="flats list" in exI)
  apply(simp)
  apply(blast)
  apply(simp add: suffix_def)
  using Prf.intros(6) by blast  
  ultimately
  show "finite (LV (Star r) s)" by (simp add: finite_subset)
qed  

definition
  "Stars_Cons V Vs \<equiv> {Stars (v # vs) | v vs. v \<in> V \<and> Stars vs \<in> Vs}"

definition
  "Stars_Append Vs1 Vs2 \<equiv> {Stars (vs1 @ vs2) | vs1 vs2. Stars vs1 \<in> Vs1 \<and> Stars vs2 \<in> Vs2}"

fun Stars_Pow :: "('a val) set \<Rightarrow> nat \<Rightarrow> ('a val) set"
where  
  "Stars_Pow Vs 0 = {Stars []}"
| "Stars_Pow Vs (Suc n) = Stars_Cons Vs (Stars_Pow Vs n)"
  
lemma finite_Stars_Cons:
  assumes "finite V" "finite Vs"
  shows "finite (Stars_Cons V Vs)"
  using assms  
proof -
  from assms(2) have "finite (Stars -` Vs)"
    by(simp add: finite_vimageI inj_on_def) 
  with assms(1) have "finite (V \<times> (Stars -` Vs))"
    by(simp)
  then have "finite ((\<lambda>(v, vs). Stars (v # vs)) ` (V \<times> (Stars -` Vs)))"
    by simp
  moreover have "Stars_Cons V Vs = (\<lambda>(v, vs). Stars (v # vs)) ` (V \<times> (Stars -` Vs))"
    unfolding Stars_Cons_def by auto    
  ultimately show "finite (Stars_Cons V Vs)"   
    by simp
qed

lemma finite_Stars_Append:
  assumes "finite Vs1" "finite Vs2"
  shows "finite (Stars_Append Vs1 Vs2)"
  using assms  
proof -
  define UVs1 where "UVs1 \<equiv> Stars -` Vs1"
  define UVs2 where "UVs2 \<equiv> Stars -` Vs2"  
  from assms have "finite UVs1" "finite UVs2"
    unfolding UVs1_def UVs2_def
    by(simp_all add: finite_vimageI inj_on_def) 
  then have "finite ((\<lambda>(vs1, vs2). Stars (vs1 @ vs2)) ` (UVs1 \<times> UVs2))"
    by simp
  moreover 
    have "Stars_Append Vs1 Vs2 = (\<lambda>(vs1, vs2). Stars (vs1 @ vs2)) ` (UVs1 \<times> UVs2)"
    unfolding Stars_Append_def UVs1_def UVs2_def by auto    
  ultimately show "finite (Stars_Append Vs1 Vs2)"   
    by simp
qed 
 
lemma finite_Stars_Pow:
  assumes "finite Vs"
  shows "finite (Stars_Pow Vs n)"    
by (induct n) (simp_all add: finite_Stars_Cons assms)

lemma LV_NTimes_5:
  "LV (NTimes r n) s \<subseteq> Stars_Append (LV (Star r) s) (\<Union>i\<le>n. LV (NTimes r i) [])"
apply(auto simp add: LV_def)
apply(auto elim!: Prf_elims)
  apply(auto simp add: Stars_Append_def)
  apply(rule_tac x="vs1" in exI)
  apply(rule_tac x="vs2" in exI)  
  apply(auto)
    using Prf.intros(6) apply(auto)
      apply(rule_tac x="length vs2" in bexI)
    thm Prf.intros
      apply(subst append.simps(1)[symmetric])
    apply(rule Prf.intros)
      apply(auto)[1]
      apply(auto)[1]
     apply(simp)
    apply(simp)
      done

lemma LV_NTIMES_3:
  shows "LV (NTimes r (Suc n)) [] = 
     (\<lambda>(v, vs). Stars (v#vs)) ` (LV r [] \<times> (Stars -` (LV (NTimes r n) [])))"
unfolding LV_def
apply(auto elim!: Prf_elims simp add: image_def)
apply(case_tac vs1)
apply(auto)
apply(case_tac vs2)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
apply(auto)
  done 

lemma finite_NTimes_empty:
  assumes "\<And>s. finite (LV r s)" 
  shows "finite (LV (NTimes r n) [])"
  using assms
  apply(induct n)
   apply(auto simp add: LV_simps)
  apply(subst LV_NTIMES_3)
  apply(rule finite_imageI)
  apply(rule finite_cartesian_product)
  using assms apply simp 
  apply(rule finite_vimageI)
  apply(simp)
  apply(simp add: inj_on_def)
  done

lemma LV_From_5:
  shows "LV (From r n) s \<subseteq> Stars_Append (LV (Star r) s) (\<Union>i\<le>n. LV (From r i) [])"
apply(auto simp add: LV_def)
apply(auto elim!: Prf_elims)
apply(auto simp add: Stars_Append_def)
apply(rule_tac x="vs1" in exI)
apply(rule_tac x="vs2" in exI)  
apply(auto)
    using Prf.intros(6) apply(auto)
      apply(rule_tac x="length vs2" in bexI)
    thm Prf.intros
      apply(subst append.simps(1)[symmetric])
    apply(rule Prf.intros)
      apply(auto)[1]
      apply(auto)[1]
     apply(simp)
     apply(simp)
      apply(rule_tac x="vs" in exI)
    apply(rule_tac x="[]" in exI) 
    apply(auto)
    by (metis Prf.intros(9) append_Nil atMost_iff empty_iff le_imp_less_Suc less_antisym list.set(1) nth_mem zero_le)

lemma LV_FROMNTIMES_3:
  shows "LV (From r (Suc n)) [] = 
    (\<lambda>(v,vs). Stars (v#vs)) ` (LV r [] \<times> (Stars -` (LV (From r n) [])))"
unfolding LV_def
apply(auto elim!: Prf_elims simp add: image_def)
apply(case_tac vs1)
apply(auto)
apply(case_tac vs2)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
     apply(auto)
  apply (metis le_imp_less_Suc length_greater_0_conv less_antisym list.exhaust list.set_intros(1) not_less_eq zero_le)
  prefer 2
  using nth_mem apply blast
  apply(case_tac vs1)
  apply (smt Groups.add_ac(2) Prf.intros(9) add.right_neutral add_Suc_right append.simps(1) insert_iff length_append list.set(2) list.size(3) list.size(4))
    apply(auto)
done   

lemma LV_From_empty:
 "LV (From r n) [] = Stars_Pow (LV r []) n" 
  apply(induct n)
   apply(simp add: LV_def)    
   apply(auto elim: Prf_elims simp add: image_def)[1]
   prefer 2
    apply(subst append.simps[symmetric])
    apply(rule Prf.intros)
      apply(simp_all)
   apply(erule Prf_elims) 
    apply(case_tac vs1)
     apply(simp)
    apply(simp)
   apply(case_tac x)
    apply(simp_all)
    apply(simp add: LV_FROMNTIMES_3 image_def Stars_Cons_def)
  apply blast
 done   

lemma finite_From_empty:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (From r n) s)"
  apply(rule finite_subset)
   apply(rule LV_From_5)
  apply(rule finite_Stars_Append)
    apply(rule LV_STAR_finite)
   apply(rule assms)
  apply(rule finite_UN_I)
   apply(auto)
  by (simp add: assms finite_Stars_Pow LV_From_empty)
    

lemma subseteq_Upto_Star:
  shows "LV (Upto r n) s \<subseteq> LV (Star r) s"
  apply(auto simp add: LV_def)
  by (metis Prf.intros(6) Prf_elims(8))


lemma LV_finite:
  shows "finite (LV r s)"
proof(induct r arbitrary: s)
  case (Zero s) 
  show "finite (LV Zero s)" by (simp add: LV_simps)
next
  case (One s)
  show "finite (LV One s)" by (simp add: LV_simps)
next
  case (Atom c s)
  show "finite (LV (Atom c) s)" by (simp add: LV_simps)
next 
  case (Plus r1 r2 s)
  then show "finite (LV (Plus r1 r2) s)" by (simp add: LV_simps)
next 
  case (Times r1 r2 s)
  define f where "f \<equiv> \<lambda>(v1::'a val, v2). Seq v1 v2"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r1 s'"
  define S2 where "S2 \<equiv> \<Union>s' \<in> Suffixes s. LV r2 s'"
  have IHs: "\<And>s. finite (LV r1 s)" "\<And>s. finite (LV r2 s)" by fact+
  then have "finite S1" "finite S2" unfolding S1_def S2_def
    by (simp_all add: finite_Prefixes finite_Suffixes)
  moreover
  have "LV (Times r1 r2) s \<subseteq> f ` (S1 \<times> S2)"
    unfolding f_def S1_def S2_def 
    unfolding LV_def image_def prefix_def suffix_def
    apply (auto elim!: Prf_elims)
    by (metis (mono_tags, lifting) mem_Collect_eq)  
  ultimately 
  show "finite (LV (Times r1 r2) s)"
    by (simp add: finite_subset)
next
  case (Star r s)
  then show "finite (LV (Star r) s)" by (simp add: LV_STAR_finite)
next
  case (NTimes r n s)
  have "\<And>s. finite (LV r s)" by fact
  then have "finite (Stars_Append (LV (Star r) s) (\<Union>i\<le>n. LV (NTimes r i) []))" 
    apply(rule_tac finite_Stars_Append)
     apply (simp add: LV_STAR_finite)
    using finite_NTimes_empty by blast
  then show "finite (LV (NTimes r n) s)"
    by (metis LV_NTimes_5 finite_subset)
next
  case (Upto r n s)
  then have "finite (LV (Star r) s)" by (simp add: LV_STAR_finite)
  moreover
  have "LV (Upto r n) s \<subseteq> LV (Star r) s"
    by (meson subseteq_Upto_Star) 
  ultimately show "finite (LV (Upto r n) s)"
    using rev_finite_subset by blast 
next 
  case (From r n)
  then show "finite (LV (From r n) s)"
    by (simp add: finite_From_empty)
next 
  case (Rec l r)
  have "\<And>s. finite (LV r s)" by fact
  then show "finite (LV (Rec l r) s)"
    by(simp add: LV_simps)
next
  case (Charset cs s)
  show "finite (LV (Charset cs) s)" by (simp add: LV_simps)
qed



text \<open>
  Our POSIX values are lexical values.
\<close>


lemma Posix_LV:
  assumes "s \<in> r \<rightarrow> v"
  shows "v \<in> LV r s"
  using assms unfolding LV_def
  apply(induct rule: Posix.induct)
  using Prf.intros(4) flat.simps(1) apply blast
  apply (simp add: Prf.intros(5))
  apply (simp add: Prf.intros(2))
  apply (simp add: Prf.intros(3))
  apply (simp add: Prf.intros(1))
  apply (smt (verit, best) CollectI Posix1(2) Posix1a Posix_Star1)
  apply (simp add: Prf.intros(6))
  apply (smt (verit, best) Posix1(2) Posix1a Posix_NTimes1 mem_Collect_eq)
  using Posix1a Posix_NTimes2 apply fastforce
  apply (smt (verit, ccfv_threshold) Posix1(2) Posix1a Posix_Upto1 mem_Collect_eq)
  using Posix1a Posix_Upto2 apply fastforce
  using Posix1a Posix_From2 apply fastforce
  apply (smt (verit, best) Posix1(2) Posix1a Posix_From1 mem_Collect_eq)
  apply (smt (verit, best) Posix1a Posix_From3 flat.simps(7) mem_Collect_eq)
  apply(simp add: Prf.intros(11))
  by (simp add: Prf.intros(12))
  

lemma Posix_Prf:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r"
  using assms Posix_LV LV_def
  by blast

end