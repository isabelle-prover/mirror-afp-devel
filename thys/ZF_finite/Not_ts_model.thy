(*  Author:     Štěpán Holub, Department of Algebra, Charles University
    Author:     Zuzana Haniková, Institute of Computer Science of the Czech Academy of Sciences
*)

section \<open>Independence of transitive superset\<close>
theory Not_ts_model
imports Permutation_models
begin 

text  \<open>We explore the model defined by the permutation transposing \<open>n\<close> and \<open>{n+1}\<^sub>M\<close> for each natural number \<open>n\<close>.
The membership in the model is not well-founded since there is an infinite decreasing chain \<open>... 2 \<epsilon>\<^sup>f 1 \<epsilon>\<^sup>f 0\<close>.

Despite that if the native memebership satisfies regularity and finiteness, the permuted model also satisfies regularity and finiteness.

Consequently, \<open>0\<close> (the empty set) has not transitive superset, since it sould be infinite if it existed. 
As a corollary, the permutation model does not satisfy schema of regularity (or, equivalently, epsilon induction) 
since it entails transitive superset axiom.

The construction is given in Rieger in \<^cite>\<open>Rieger1957\<close> and also in \<^cite>\<open>ManciniZambella2001\<close> who underscore that the model is recursive. 
The statement that regularity schema does not follow from regularity was also proved in \<^cite>\<open>VopenkaHajek1963\<close>.
\<close>

context L_setext_empty_power_union_repl_reg

begin

fun regperm :: "'a \<Rightarrow> 'a" where
   "regperm a = (if natM a then {setsucM a a}\<^sub>M else 
                   if (\<exists> b. natM b \<and> a = {setsucM b b}\<^sub>M) then THE b. a = {setsucM b b}\<^sub>M else a)"

lemma two_natM: "natM (setsucM ({\<emptyset>}\<^sub>M)({\<emptyset>}\<^sub>M))"
  using nat_suc_nat[OF one_natM]. 

lemma suc_sing_not_nat: "\<not> natM ({setsucM b b}\<^sub>M)"
proof
  assume "natM ({setsucM b b}\<^sub>M)"
  hence "ordM ({setsucM b b}\<^sub>M)"
    unfolding natM_def using natM_D  by blast 
  from ordM_D1[OF this, of "setsucM b b"]  
  have "b = setsucM b b"
    unfolding singleton_def' subsetM_def by force
  moreover have "b \<epsilon> setsucM b b"
    unfolding set_defs by blast
  ultimately show False         
    using mem_not_refl[of b] by simp
qed

lemma regperm_image_nat: assumes "natM a"
  shows "regperm a = {setsucM a a}\<^sub>M"
  using assms by simp

lemma regperm_image_plus: assumes "natM b"
  shows "regperm ({setsucM b b}\<^sub>M) = b"
proof-
  have  aux: "(THE c. ({setsucM b b}\<^sub>M) = ({setsucM c c}\<^sub>M)) = regperm ({setsucM b b}\<^sub>M)"
    using \<open>natM b\<close> suc_sing_not_nat by fastforce
  have aux': "{setsucM b b}\<^sub>M = {setsucM x x}\<^sub>M \<Longrightarrow> x = b" for x
    using suc_unique[of x b] unfolding setext singleton_def' by blast
  show ?thesis
    using  the_equality[of "\<lambda> c. {setsucM b b}\<^sub>M = {setsucM c c}\<^sub>M", OF refl aux']
    unfolding aux by blast    
qed 

lemma regperm_image_else: assumes "\<not> natM a" "\<nexists> b. natM b \<and> a = {setsucM b b}\<^sub>M"
  shows "regperm a = a"
  using assms by force

lemma regperm_bij: "bij regperm"
proof (rule involuntory_imp_bij)
  fix a
  show "regperm (regperm a) = a"
    by  (cases "natM a", use regperm_image_nat regperm_image_plus in force)
    (cases "\<exists> b. natM b \<and> a = {setsucM b b}\<^sub>M", use regperm_image_nat regperm_image_plus in metis, auto)
qed

lemma SR_regperm_eq: "SetRelation (\<lambda> x y. regperm x = y)"
proof-
  let ?Def = "\<lambda> x y. (natM x \<and> y = {setsucM x x}\<^sub>M) \<or> (\<not> natM x \<and> (\<exists> b. natM b \<and> x = {setsucM b b}\<^sub>M \<and> y = b))
       \<or> (\<not> natM x \<and> (\<nexists>b. natM b \<and> x = {setsucM b b}\<^sub>M) \<and> y = x)"
  have iff: "?Def x y \<longleftrightarrow> regperm x = y" for x y
  proof-
    consider "natM x" | "\<not> natM x \<and> (\<exists> b. natM b \<and> x = {setsucM b b}\<^sub>M)" | 
              "\<not> natM x \<and> (\<nexists> b. natM b \<and> x = {setsucM b b}\<^sub>M)" by blast
    then show ?thesis
      by (cases, force) (use regperm_image_plus in blast, use regperm_image_else in auto)
  qed
  have "SetRelation ?Def"
    unfolding SetRelation_def logsimps set_defs by (rule SFP_rules)+
  thus ?thesis 
    unfolding iff.
qed

lemma SR_regperm_mem: "SetRelation (\<lambda> x y. x \<epsilon> regperm y)"
proof-
  have "SetRelation (\<lambda> x y. \<exists> z. x \<epsilon> z \<and> regperm y = z)"
    unfolding SetRelation_def logsimps 
    by (rule SFP_rules)+
    (use transform_variables[OF SR_regperm_eq[unfolded SetRelation_def], of "id(0:=1, 1:=_)"] in simp)
  thus ?thesis
    by metis
qed

end

context  L_setext_empty_power_union_repl_reg_fin

begin  

interpretation perm: permutation_model "(\<epsilon>)" regperm
  by unfold_locales (use regperm_bij SR_regperm_mem in blast)+  

\<comment> \<open>membership in the model\<close>
abbreviation fmem (infix "\<epsilon>\<^sup>f" 51)  where 
  "fmem x y \<equiv>  perm.perm_mem x y"

interpretation fm: L_setext_empty_power_union_repl fmem
    using perm.perm_model. 

lemma regperm_mem_nat: assumes "natM a"
  shows "u \<epsilon>\<^sup>f a \<longleftrightarrow> u = (setsucM a a)"
  unfolding regperm_image_nat[OF assms] singleton_def'..

\<comment> \<open>First meta-theorem : not used in the main meta-theorem below.\<close>
lemma fmem_not_wf: "\<not> (wfp (\<epsilon>\<^sup>f))"
proof-
  let ?B = "{x . natM x}"
  have "?B \<noteq> {}"
    using Collect_empty_eq one_natM by metis
  moreover have "z \<in> ?B \<Longrightarrow> (setsucM z z) \<epsilon>\<^sup>f z"  for z
    unfolding mem_Collect_eq using regperm_image_nat unfolding setext singleton_def' by blast
  moreover have "z \<in> ?B \<Longrightarrow> (setsucM z z) \<in> ?B"  for z
    unfolding mem_Collect_eq using nat_suc_nat.
  ultimately show ?thesis
    unfolding wfp_iff_ex_minimal by metis
qed

text \<open>The main meta-theorem. The axiom of the transitive superset does not hold in the model 
since the transitive closure of \<open>\<emptyset>\<close> would be an infinite set.\<close>

theorem regperm_not_ts: "\<not> L_ts (\<epsilon>\<^sup>f)" 
proof
  assume "L_ts (\<epsilon>\<^sup>f)"
  then interpret L_ts "(\<epsilon>\<^sup>f)".
      \<comment> \<open>take the transitive closure of \<open>\<emptyset>\<close>\<close>
  interpret L_setext_sep_ts "(\<epsilon>\<^sup>f)"
    by unfold_locales
  obtain t where "fm.subsetM \<emptyset> t" "fm.transM t" and least: "\<forall>u. u \<epsilon>\<^sup>f t \<longleftrightarrow> (\<forall>s. fm.transM s \<and>  fm.subsetM \<emptyset> s \<longrightarrow> u \<epsilon>\<^sup>f s)"
    using least_ts_is_transitive[of \<emptyset>]  least_ts_def'[of _ \<emptyset>] fm.subsetM_def by force  
  have trans_t: "z \<epsilon>\<^sup>f t" if  "y \<epsilon>\<^sup>f t" "z \<epsilon>\<^sup>f y" for y z
    using \<open>fm.transM t\<close> that unfolding fm.transM_def fm.subsetM_def by blast
      \<comment> \<open>\<open>t\<close> contains an infinite \<open>\<epsilon>\<^sup>f\<close> chain of natural numbers\<close>
  have suc_t: "setsucM u u  \<epsilon>\<^sup>f t" if "natM u" "u \<epsilon>\<^sup>f t" for u
    using trans_t[OF \<open>u \<epsilon>\<^sup>f t\<close>] using regperm_mem_nat[OF \<open>natM u\<close>] by blast
      \<comment> \<open>we show that \<open>\<epsilon>\<^sup>f\<close> coincides with \<open>\<epsilon>\<close> in \<open>t\<close>\<close>
  have one_in_t: "{\<emptyset>}\<^sub>M \<epsilon>\<^sup>f t"
    using \<open>fm.subsetM \<emptyset> t\<close>unfolding fm.subsetM_def using regperm_mem_nat[OF emp_natM]
      setsuc_empty_sing by fastforce
  have two_in_t: "setsucM ({\<emptyset>}\<^sub>M) ({\<emptyset>}\<^sub>M) \<epsilon>\<^sup>f t"
    using one_in_t suc_t[OF one_natM] by blast
  have tmem:  "u \<epsilon>\<^sup>f t \<longleftrightarrow> u \<epsilon> t" for u
  proof-
    have "\<not> natM t"
    proof
      assume "natM t"
      have iff: "u \<epsilon>\<^sup>f t \<longleftrightarrow> u = setsucM t t" for u
        unfolding regperm_image_nat[OF \<open>natM t\<close>] singleton_def'..
      have "\<not> {\<emptyset>}\<^sub>M \<epsilon> setsucM ({\<emptyset>}\<^sub>M) ({\<emptyset>}\<^sub>M)"
        unfolding two_in_t[unfolded iff, folded one_in_t[unfolded iff]]
        by (rule mem_not_refl)
      then show False 
        unfolding setsuc_def' by blast
    qed
    have "\<nexists> b.  natM b \<and> t = {setsucM b b}\<^sub>M"
    proof
      assume "\<exists>b. natM b \<and> t = {setsucM b b}\<^sub>M"
      then obtain b where "natM b" "t = {setsucM b b}\<^sub>M"
        by blast
      hence iff: "u \<epsilon>\<^sup>f t \<longleftrightarrow> u \<epsilon> b" for u
        using regperm_image_plus by auto
      have "b \<noteq> \<emptyset>"
        using iff one_in_t by auto
      hence  "\<emptyset> \<epsilon> b"
        using \<open>natM b\<close> by (simp add: empty_mem_ord natM_def) 
      have "setsucM y y \<epsilon> b" if "y \<epsilon> b" for y
        using suc_t[unfolded iff, OF _ that] nat_mem_nat[OF _ that] \<open>natM b\<close> by blast 
      then show False
        using \<open>\<emptyset> \<epsilon> b\<close> fin by blast
    qed
    show ?thesis
      by (simp add: \<open>\<nexists>b. natM b \<and> t = {setsucM b b}\<^sub>M\<close> \<open>\<not> natM t\<close>)
  qed  
  \<comment> \<open>We get a contradiction with the finiteness axiom since the subset of \<open>t\<close> consisting of natural numbers is an inductive set.\<close> 
  thm notE[OF fin[unfolded not_ex, rule_format]] 
  show False
  proof (rule notE[OF fin[unfolded not_ex, rule_format]], rule conjI)
    define tnatM where "tnatM = separationM t natM"
    have tnat:  "u \<epsilon> tnatM \<longleftrightarrow> natM u \<and> u \<epsilon> t" for u
    using separ_def_SP tnatM_def by auto
    show "\<emptyset> \<epsilon> setsucM tnatM \<emptyset>"
      unfolding set_defs by simp 
    show "\<forall>y. y \<epsilon> setsucM tnatM \<emptyset> \<longrightarrow> setsucM y y \<epsilon> setsucM tnatM \<emptyset>"
    proof (rule allI, rule impI)
      fix y
      assume "y \<epsilon> setsucM tnatM \<emptyset>"
      then consider "y = \<emptyset>" | "y \<epsilon> tnatM"
        unfolding set_defs by blast 
      then show "setsucM y y \<epsilon> setsucM tnatM \<emptyset>"
      proof (cases) 
        assume "y = \<emptyset>"
        then show ?thesis 
          using one_in_t[unfolded tmem] setsuc_empty_sing tnat unfolding binunion_def' by simp 
      next
        assume "y \<epsilon> tnatM"
        then show ?thesis 
          unfolding tnat  binunion_def' setsuc_def'  using   suc_t[unfolded tmem, of y] nat_suc_nat[of y] by blast
      qed
    qed
  qed
qed

\<comment> \<open>It follows that the scheme of regularity does not hold in the model, since it entails transitive supersets.\<close>
theorem regperm_not_regsch: "\<not> L_regsch (\<epsilon>\<^sup>f)"
    using regperm_not_ts epsind_regsch_iff fm.epsind_implies_ts by blast 

lemma regperm_reg:
  shows "L_setext_empty_power_union_repl_reg (\<epsilon>\<^sup>f)"
proof (unfold_locales, rule allI, rule impI) 
  fix a
  assume "\<exists>y. y \<epsilon>\<^sup>f a"
  show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
  proof-
    consider "\<exists> n. natM n \<and> n \<epsilon>\<^sup>f a" | "(\<nexists> n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<exists> m. natM m \<and> ({setsucM m m}\<^sub>M) \<epsilon>\<^sup>f a)" | 
              "(\<nexists> n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<nexists> m. natM m \<and> ({setsucM m m}\<^sub>M) \<epsilon>\<^sup>f a)" by blast
    then show ?thesis
    proof (cases)
      assume "\<exists> n. natM n \<and> n \<epsilon>\<^sup>f a"
      then obtain k where "natM k" "k \<epsilon>\<^sup>f a" and "\<And> k'. natM k' \<Longrightarrow> k' \<epsilon>\<^sup>f a \<Longrightarrow> \<not> k \<subset>\<^sub>M k'"
        using max_mem[OF _ _ SP_nat, of _ "regperm a"] by fast
      then have max_k: "\<And> k'. natM k' \<Longrightarrow> k' \<epsilon>\<^sup>f a \<Longrightarrow> k' \<noteq> k \<Longrightarrow> k' \<epsilon> k"
        unfolding proper_subset_def' using natM_D ordM_D1 ordM_total natM_def by metis 
      show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
      proof (rule exI[of _ k], rule conjI, fact)
        show "\<forall>v. \<not> (v \<epsilon>\<^sup>f k \<and> v \<epsilon>\<^sup>f a)"
        proof (rule allI, rule notI)
          fix v 
          assume "v \<epsilon>\<^sup>f k \<and> v \<epsilon>\<^sup>f a"
          hence "v \<epsilon>\<^sup>f a" "v \<epsilon>\<^sup>f k" "v = setsucM k k"
            unfolding regperm_image_nat[OF \<open>natM k\<close>] singleton_def' by blast+
          show False
            using max_k[of v, OF _ \<open>v \<epsilon>\<^sup>f a\<close>, unfolded \<open>v = setsucM k k\<close>]
              \<open>natM k\<close> mem_antisym nat_suc_nat setsuc_def' natM_def by blast 
        qed
      qed
    next
      assume "(\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<exists>m. natM m \<and> {setsucM m m}\<^sub>M \<epsilon>\<^sup>f a)"
      then obtain m where "natM m" "{setsucM m m}\<^sub>M \<epsilon>\<^sup>f a" "\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a"
        by blast
      show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
      proof (rule exI[of _ "{setsucM m m}\<^sub>M"], rule conjI, fact)
        show "\<forall>v. \<not> (v \<epsilon>\<^sup>f {setsucM m m}\<^sub>M \<and> v \<epsilon>\<^sup>f a)"
          unfolding  regperm_image_plus[OF \<open>natM m\<close>]
          using \<open>\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a\<close> \<open>natM m\<close> nat_mem_nat by blast
      qed
    next
      assume case3: "(\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<nexists>m. natM m \<and> {setsucM m m}\<^sub>M \<epsilon>\<^sup>f a)"
      hence "\<not> natM a"
        using nat_suc_nat[of a]
          singleton_def' by force
      have "\<nexists> b. natM b \<and> a = {setsucM b b}\<^sub>M"
        using case3 \<open>\<exists>y. y \<epsilon>\<^sup>f a\<close> nat_mem_nat regperm_image_plus by metis 
      hence a_mem: "u \<epsilon>\<^sup>f a \<longleftrightarrow> u \<epsilon> a" for u
        using \<open>\<not> natM a\<close> by auto
      have "a \<noteq> \<emptyset>"
        using \<open>\<not> natM a\<close> emp_natM by blast 
      then obtain b where "b \<epsilon> a" "\<forall> v. \<not> (v \<epsilon> b \<and> v \<epsilon> a)"
        using reg by (metis min_subset_ex) 
      have "\<not> natM b" "\<nexists> m. natM m \<and> b = {setsucM m m}\<^sub>M"
        using \<open>b \<epsilon> a\<close> case3 unfolding a_mem by blast+
      hence b_mem: "u \<epsilon>\<^sup>f b \<longleftrightarrow> u \<epsilon> b" for u
        by auto
      show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
        by (rule exI[of _ b], rule conjI, unfold a_mem b_mem) fact+ 
    qed
  qed
qed

lemma perm_empty: "fm.emptysetM = {{\<emptyset>}\<^sub>M}\<^sub>M"
proof (rule sym, unfold fm.emptyset_def') 
  have "regperm ({{\<emptyset>}\<^sub>M}\<^sub>M) = \<emptyset>"
    using regperm_image_plus[OF emp_natM] unfolding setsuc_empty_sing.
  show "\<forall>u. \<not> u \<epsilon> (regperm ({{\<emptyset>}\<^sub>M}\<^sub>M))"
    unfolding \<open>regperm ({{\<emptyset>}\<^sub>M}\<^sub>M) = \<emptyset>\<close> by (fact empty_is_empty) 
qed

lemma perm_one: "fm.binunionM fm.emptysetM (fm.singletonM fm.emptysetM) = {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M"
proof-
  have L: "z \<epsilon>\<^sup>f fm.binunionM fm.emptysetM (fm.singletonM fm.emptysetM) \<longleftrightarrow> z = fm.emptysetM" for z
    unfolding fm.setext fm.binunion_def' fm.singleton_def'
    using fm.nemp_setI fm.setsuc_def' by blast 
  have "z \<epsilon>\<^sup>f {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<longleftrightarrow> z \<epsilon> {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M" for z
    using singleton_def' binunion_emp nat_mem_nat nat_suc_nat
        regperm_image_else[of "{{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M"] suc_sing_not_nat[of \<emptyset>] unfolding setsuc_empty_sing  by metis 
  hence R: "z \<epsilon>\<^sup>f {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<longleftrightarrow> z = fm.emptysetM" for z
    unfolding perm_empty singleton_def'.   
  show ?thesis 
    unfolding fm.setext L R by blast
qed

lemma perm_else_setsuc_else: assumes "\<not> natM u" "\<nexists> b. natM b \<and> u = {setsucM b b}\<^sub>M"
  shows "\<not> natM (setsucM u u)" "\<nexists> b. natM b \<and> setsucM u u = {setsucM b b}\<^sub>M"
  using assms by (meson nat_mem_nat setsuc_def') (metis mem_not_refl singleton_def' setsuc_def')   

lemma perm_setsuc: assumes "\<not> natM u" "\<nexists> b. natM b \<and> u = {setsucM b b}\<^sub>M"
  shows "fm.setsucM u u = setsucM u u"
  unfolding fm.setext unfolding fm.binunion_def' regperm_image_else[OF perm_else_setsuc_else[OF assms]] 
  regperm_image_else[OF assms] binunion_def' singleton_def' fm.singleton_def' setsuc_def'
  using \<open>regperm u = u\<close> fm.setsuc_def' by auto 

lemma perm_fin: "L_fin (\<epsilon>\<^sup>f)"
proof(unfold_locales, rule notI)
  assume "\<exists>x. fm.emptysetM \<epsilon>\<^sup>f x \<and> (\<forall>y. y \<epsilon>\<^sup>f x \<longrightarrow> fm.setsucM y y \<epsilon>\<^sup>f x)"
  then obtain x where xf: "fm.emptysetM \<epsilon>\<^sup>f x" "\<forall>y. y \<epsilon>\<^sup>f x \<longrightarrow> fm.setsucM y y \<epsilon>\<^sup>f x"
    by blast   
  hence mem0: "{{\<emptyset>}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f x" 
    using perm_empty by force
  from xf(2)[rule_format, OF xf(1), unfolded perm_one] 
  have mem1: "{{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f x"
    using fm.binunion_emp fm.setsuc_empty_sing perm_one by force
  hence not1: "\<not> natM x"
    using mem0 by (metis mem_neq_singleton regperm_mem_nat) 
  have not2: "\<nexists>b. natM b \<and> x = {setsucM b b}\<^sub>M"
    using mem0 mem1
    using binunion_emp nat_mem_nat regperm_image_plus suc_sing_not_nat setsuc_empty_sing by metis
  from regperm_image_else[OF not1 not2]
  have x: "{{\<emptyset>}\<^sub>M}\<^sub>M \<epsilon> x" "\<forall>y. y \<epsilon> x \<longrightarrow> fm.setsucM y y \<epsilon> x"
    using xf perm_empty by force+
  let ?P = "\<lambda> u. (\<not> natM u \<and> (\<nexists> b. natM b \<and> (u = {setsucM b b}\<^sub>M)))"
  have sp: "SetProperty ?P"
    unfolding SetProperty_def set_defs logsimps by (rule SFP_rules)+
  from sep_SP[OF this, rule_format, of x]
  obtain x' where x': "\<forall>u. (u \<epsilon> x') = (u \<epsilon> x \<and> \<not> natM u \<and> (\<nexists>b. natM b \<and> u = {setsucM b b}\<^sub>M))"
    by blast
  have "{{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<epsilon> x'"
    using mem1  unfolding x'[rule_format] \<open>regperm x = x\<close>
    using binunion_emp nat_mem_nat nat_suc_nat singleton_def' suc_sing_not_nat setsuc_empty_sing by metis 
  hence "x' \<noteq> \<emptyset>"
    by force
  have x'_setsuc: "setsucM u u \<epsilon> x'" if "u \<epsilon> x'" for u
    unfolding x'[rule_format]
  proof(unfold conj_assoc[symmetric], rule conjI, rule conjI)  
    note u = \<open>u \<epsilon> x'\<close>[unfolded x'[rule_format]]
    have red: "fm.setsucM u u = setsucM u u"
      by (rule perm_setsuc)
      (use  \<open>u \<epsilon> x'\<close>[unfolded x'[rule_format]] in blast)+
    show "setsucM u u \<epsilon> x"
      by (rule  x(2)[rule_format, of u, unfolded red]) (simp add: u)
    show "\<not> natM (setsucM u u)" "\<nexists>b. natM b \<and> setsucM u u = {setsucM b b}\<^sub>M"
      using u perm_else_setsuc_else by blast+
  qed
  with max_subset_ex[OF \<open>x' \<noteq> \<emptyset>\<close>]
  show False
    using suc_subset by blast
qed     

interpretation find: L_setind "(\<epsilon>\<^sup>f)"
  using L_setext_empty_power_union_repl_reg.fin_implies_setind regperm_reg perm_fin by blast

end

text\<open>Summary of results. 
We have shown that if a type admits a membership relation satisfying certain axioms of finite sets
(namely axioms of ZF where inf is replaced by fin), 
it does not follow that the membership on the type satisfies the existence of transitive supersets or the regularity schema.\<close>

theorem not_reg_setind_implies_regsch_ts: 
  assumes "L_setext_empty_power_union_repl_reg_fin (m :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  shows "\<not> (\<forall> (mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl_reg mem \<and> L_setind mem \<longrightarrow> L_regsch mem \<or> L_ts mem)"
proof (rule notI)
  assume contr: "\<forall>(mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl_reg mem \<and> L_setind mem \<longrightarrow> L_regsch mem \<or> L_ts mem"
  interpret L_setext_empty_power_union_repl_reg_fin m
    using assms.
  have L1: "L_setind fmem"
    using L_setext_empty_power_union_repl_reg.fin_implies_setind regperm_reg perm_fin by blast
  have L2: "L_setext_empty_power_union_repl_reg fmem"
    using L_setext_empty_power_union_repl_def L_setext_empty_power_union_repl_reg_def regperm_reg
    by blast
  have L3: "L_regsch fmem \<or> L_ts fmem"
    using L1 L2 contr by blast
  interpret i2: L_setext_empty_power_union_repl_reg fmem
    using L2.
  show False
    using L3 regperm_not_regsch regperm_not_ts by blast
qed 

end