section \<open>Renaming-Enriched Sets (Rensets)\<close>

theory Rensets
  imports Lambda_Terms
begin

text \<open>This theory defines rensets and proves their basic properties. \<close>

subsection \<open>Rensets\<close>

locale Renset = 
  fixes vsubstA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A"
  assumes 
    vsubstA_id[simp]: "\<And>x a. vsubstA a x x = a"
    and 
    vsubstA_idem[simp]: "\<And>x y1 y2 a. y1 \<noteq> x \<Longrightarrow> vsubstA (vsubstA a y1 x) y2 x = vsubstA a y1 x"
    and 
    vsubstA_chain: "\<And>u x1 x2 x3 a. 
  u \<noteq> x2 \<Longrightarrow> 
  vsubstA (vsubstA (vsubstA a u x2) x2 x1) x3 x2 = 
  vsubstA (vsubstA a u x2) x3 x1"
    and 
    vsubstA_commute_diff: 
    "\<And> x y u a v. x \<noteq> v \<Longrightarrow> y \<noteq> u \<Longrightarrow> x \<noteq> y \<Longrightarrow> 
vsubstA (vsubstA a u x) v y = vsubstA (vsubstA a v y) u x"
begin

(* nominal-style freshness: *)
definition freshA where "freshA x a \<equiv> finite {y. vsubstA a y x \<noteq> a}"

lemma freshA_vsubstA_idle:  
  assumes n: "freshA x a" and xy: "x \<noteq> y"
  shows "vsubstA a y x = a"
proof-
  obtain yy where yy: "vsubstA a yy x = a" "yy \<noteq> x"
    using n unfolding freshA_def using exists_var by force
  hence "vsubstA a y x = vsubstA (vsubstA a yy x) y x" by simp 
  also have "\<dots> = vsubstA a yy x" by (simp add: yy(2))
  also have "\<dots> = a" using yy(1) .
  finally show ?thesis .
qed

lemma vsubstA_chain_freshA:
  assumes "freshA x2 a"  
  shows "vsubstA (vsubstA a x2 x1) x3 x2 = vsubstA a x3 x1"
proof-
  obtain yy where yy: "yy \<noteq> x2"
    by (metis(full_types) list.set_intros(1) pickFresh_var)
  have 0: "a = vsubstA a yy x2" 
  	using assms freshA_vsubstA_idle yy by presburger
  show ?thesis
    by (metis "0" vsubstA_chain yy)
qed

lemma freshA_vsubstA:  
  assumes "freshA u a" and "u \<noteq> y"
  shows "freshA u (vsubstA a y x)"
proof-
  have "{ya. vsubstA (vsubstA a y x) ya u \<noteq> vsubstA a y x} \<subseteq> {y. vsubstA a y u \<noteq> a} \<union> {x,y,u} \<union> {y. \<not> freshA y a}"   
    using assms by auto (metis vsubstA_commute_diff vsubstA_idem)  
  show ?thesis using assms unfolding freshA_def 
    by (smt (verit, best) Collect_mono_iff finite_subset vsubstA_commute_diff vsubstA_id vsubstA_idem) 	 
qed

lemma freshA_vsubstA2:
  assumes "freshA z a \<or> z = x" and "freshA x a \<or> z \<noteq> y"
  shows "freshA z (vsubstA a y x)"
proof(cases "z = y")
  case True
  thus ?thesis using assms by (metis freshA_vsubstA_idle vsubstA_id)
next
  case False
  hence "{ya. vsubstA (vsubstA a y x) ya z \<noteq> vsubstA a y x} \<subseteq>  
  {ya. vsubstA a ya z \<noteq> a} \<union> {ya. vsubstA a ya y \<noteq> a} \<union> {x}" 
    by auto (metis vsubstA_commute_diff vsubstA_idem)
  thus ?thesis 
    using assms unfolding freshA_def  
    by (smt (verit, best) False assms(1) freshA_vsubstA freshA_vsubstA_idle not_finite_existsD vsubstA_idem) 
qed

(* *)

lemma vsubstA_idle_freshA:  
  assumes "vsubstA a y x = a" and xy: "x \<noteq> y"
  shows "freshA x a"
  by (smt (verit, best) assms(1) freshA_def not_finite_existsD vsubstA_idem xy)

lemma freshA_iff_ex_vvsubstA_idle:
  "freshA x a \<longleftrightarrow> (\<exists>y. y\<noteq>x \<and> vsubstA a y x = a)"
  by (smt (z3) CollectI exists_var finite.insertI insertCI freshA_def vsubstA_idle_freshA)

lemma freshA_iff_all_vvsubstA_idle:
  "freshA x a \<longleftrightarrow> (\<forall>y. y\<noteq>x \<longrightarrow> vsubstA a y x = a)"
  by (metis list.set_intros(1) freshA_vsubstA_idle pickFresh_var vsubstA_idle_freshA)

end (* locale Renset *)


subsection \<open>Finitely supported rensets\<close>

(* adding the finite support assumption, also in the style of nominal  *)
locale Renset_FinSupp = Renset vsubstA
  for vsubstA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A" 
    +
  assumes cofinite_freshA: "\<And>a. finite {x. \<not> freshA x a}"
begin

(* Picking fresh operator (mirrors the one for terms): *)
definition pickFreshSA :: "var set \<Rightarrow> var list \<Rightarrow> 'A list \<Rightarrow> var" where 
  "pickFreshSA X xs ds \<equiv> SOME z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>a \<in> set ds. freshA z a)" 

lemma exists_freshA_set:
  assumes "finite X"
  shows "\<exists> z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>a \<in> set ds. freshA z a)"
proof-
  have 1: "{x. \<exists>a\<in>set ds. \<not> freshA x a} = \<Union> {{x. \<not> freshA x a} | a. a\<in>set ds}" by auto
  have "finite {x. \<exists>a\<in>set ds. \<not> freshA x a}" 
    unfolding 1 apply(rule finite_Union) 
    using assms cofinite_freshA by auto
  hence 0: "finite (X \<union> set xs \<union> {x. \<exists>a\<in>set ds. \<not> freshA x a})" 
    using assms by blast
  show ?thesis using exists_var[OF 0] by simp
qed

lemma exists_freshA:
  "\<exists> z. z \<notin> set xs \<and> (\<forall>a \<in> set ds. freshA z a)"
  using exists_freshA_set by blast

lemma pickFreshSA: 
  assumes "finite X"
  shows 
    "pickFreshSA X xs ds \<notin> X \<and> 
 pickFreshSA X xs ds \<notin> set xs \<and> 
 (\<forall>a \<in> set ds. freshA (pickFreshSA X xs ds) a)"
  using exists_freshA_set[OF assms] unfolding pickFreshSA_def 
  by (rule someI_ex)

lemmas pickFreshSA_set = pickFreshSA[THEN conjunct1]
  and pickFreshSA_var = pickFreshSA[THEN conjunct2, THEN conjunct1]
  and pickFreshSA_freshA = pickFreshSA[THEN conjunct2, THEN conjunct2, unfolded Ball_def, rule_format]

(* Unconditional form of pick-fresh, without any set: *)
definition "pickFreshA \<equiv> pickFreshSA {}"

lemmas pickFreshA = pickFreshSA[OF finite.emptyI, unfolded pickFreshA_def[symmetric], simplified]
lemmas pickFreshA_var = pickFreshSA_var[OF finite.emptyI, unfolded pickFreshA_def[symmetric]]
  and pickFreshA_freshA = pickFreshSA_freshA[OF finite.emptyI, unfolded pickFreshA_def[symmetric]]

end (* contex Renset_FinSupp *)


subsection \<open>Morphisms between rensets\<close>

locale Renset_Morphism = 
  A: Renset_FinSupp substA + B: Renset_FinSupp substB
  for substA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A" and substB :: "'B \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'B"
    +
  fixes f :: "'A \<Rightarrow> 'B"
  assumes f_substA_substB: "\<And>a y z. f (substA a y z) = substB (f a) y z"


end 