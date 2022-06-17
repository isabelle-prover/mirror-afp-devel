theory LexicalVals
  imports Lexer "HOL-Library.Sublist"
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
unfolding LV_def
by (auto intro: Prf.intros elim: Prf.cases)

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
qed



text \<open>
  Our POSIX values are lexical values.
\<close>

lemma Posix_LV:
  assumes "s \<in> r \<rightarrow> v"
  shows "v \<in> LV r s"
  using assms unfolding LV_def
  apply(induct rule: Posix.induct)
  apply(auto simp add: intro!: Prf.intros elim!: Prf_elims)
  done

lemma Posix_Prf:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r"
  using assms Posix_LV LV_def
  by blast


end