(*  Author:     Štěpán Holub, Department of Algebra, Charles University
    Author:     Zuzana Haniková, Institute of Computer Science of the Czech Academy of Sciences
*)


section \<open>Regularity\<close>
theory Not_regular_model
imports Permutation_models
begin

text \<open>
Axioms of extensionality, empty set, powerset, union, replacement and set induction 
are not sufficient to prove regularity, even in the presence of transitive superset axiom.

We prove this using permutation models.
It is enough to transpose \<open>0\<close> and \<open>1\<close> in order to obtain a model which violates regularity, cf. \<^cite>\<open>"Theorem 13" in BaratellaFerro1993\<close>
\<close>

context L_setext_empty_power_union_repl

begin

definition swap_zero_one :: "'a \<Rightarrow> 'a" where 
  "swap_zero_one x = (if x = \<emptyset> then {\<emptyset>}\<^sub>M else (if x = {\<emptyset>}\<^sub>M then \<emptyset> else x))"

lemma swap_zero_one_involution[simp]: "swap_zero_one (swap_zero_one x) = x"
  by (simp add: swap_zero_one_def)

lemma bij_swap_zero_one: "bij swap_zero_one"
  by (simp add: involuntory_imp_bij swap_zero_one_def)
  
lemma swap_zero_one_mem: "a \<epsilon> swap_zero_one b \<longleftrightarrow> (b \<noteq> {\<emptyset>}\<^sub>M \<and> a \<epsilon> b) \<or> (a = \<emptyset> \<and> b = \<emptyset>)"
  unfolding swap_zero_one_def  by (simp add: singleton_def')

lemma swap_zero_one_perm_model: "permutation_model (\<epsilon>) swap_zero_one"
proof
  show "SetRelation (\<lambda>x y. x \<epsilon> swap_zero_one y)"
    unfolding SetRelation_def swap_zero_one_mem logsimps singleton_eq set_defs by (rule SFP_rules)+  
qed (rule bij_swap_zero_one)

interpretation swap: permutation_model "(\<epsilon>)" swap_zero_one
  using swap_zero_one_perm_model by blast

notation swap.perm_mem (infix \<open>\<epsilon>\<^sup>s\<close> 50)

interpretation swap: L_setext_empty_power_union_repl "(\<epsilon>\<^sup>s)"
  using swap.perm_model.

notation swap.emptysetM (\<open>\<emptyset>\<^sup>s\<close>)

notation swap.setsucM (\<open>\<ss>\<uu>\<cc>\<^sup>s\<close>)

\<comment> \<open>\<open>{\<emptyset>}\<close> is the empty set in the permuted model\<close>
lemma one_swap: "\<not> (a \<epsilon>\<^sup>s {\<emptyset>}\<^sub>M)"
  unfolding  swap_zero_one_mem using singleton_def' by force 

lemma swap_empty: "\<emptyset>\<^sup>s = {\<emptyset>}\<^sub>M"
  using emptyset_def' swap.emptyset_def' swap_zero_one_mem by blast 

\<comment> \<open>\<open>\<emptyset>\<close> is a singleton loop in the permuted model\<close>
lemma zero_swap_mem_iff: "a \<epsilon>\<^sup>s \<emptyset> \<longleftrightarrow> a = \<emptyset>"
  unfolding  swap_zero_one_mem  by auto

text \<open>Since \<open>\<emptyset> \<epsilon>\<^sup>s \<emptyset>\<close>, the permuted model is not regular.\<close>

theorem not_reg_swap_zero_one: "\<not> (L_reg (\<epsilon>\<^sup>s))" 
  unfolding L_reg_def swap_zero_one_mem by force

text \<open>In order to show that the model with memebership \<open>\<epsilon>\<^sup>s\<close> satisfies \<open>L_setind\<close> (\<open>L_ts\<close> resp.) if the original model does, we first show how the modified successor behaves.\<close>

lemma swap_mem_mem: "\<not> (x = \<emptyset> \<and> y = \<emptyset>) \<Longrightarrow> x \<epsilon>\<^sup>s y \<Longrightarrow> x \<epsilon> y"
  using swap_zero_one_mem by auto

lemma swap_setsuc_1_y: assumes "y \<noteq> \<emptyset>" shows "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) y = {y}\<^sub>M"
proof-
  have "swap_zero_one ({y}\<^sub>M) = {y}\<^sub>M"
    by (metis assms empty_is_empty singleton_def' swap_zero_one_def)
  have "u \<epsilon>\<^sup>s \<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) y \<longleftrightarrow> u = y" for u
    using one_swap by auto
  hence "swap_zero_one (\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) y) = {y}\<^sub>M"
     unfolding setext singleton_def' by fast
  from arg_cong[OF this, of  swap_zero_one]
  show "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) y = {y}\<^sub>M"
    unfolding \<open>swap_zero_one ({y}\<^sub>M) = {y}\<^sub>M\<close> by simp
qed     
       
lemma swap_setsuc_0_y: assumes "y \<noteq> \<emptyset>" shows "\<ss>\<uu>\<cc>\<^sup>s \<emptyset> y = {\<emptyset>,y}\<^sub>M"
proof-
  have "{\<emptyset>,y}\<^sub>M \<noteq> \<emptyset> \<and> {\<emptyset>,y}\<^sub>M \<noteq> {\<emptyset>}\<^sub>M"
    unfolding setext unfolding pair_def' singleton_def' using assms by auto   
  hence "swap_zero_one ({\<emptyset>,y}\<^sub>M) = {\<emptyset>,y}\<^sub>M"
    by (simp add: swap_zero_one_def)
  have "u \<epsilon>\<^sup>s \<ss>\<uu>\<cc>\<^sup>s \<emptyset> y \<longleftrightarrow> u = \<emptyset> \<or> u = y" for u
    by (simp add: zero_swap_mem_iff)
  hence "swap_zero_one (\<ss>\<uu>\<cc>\<^sup>s \<emptyset> y) = {\<emptyset>,y}\<^sub>M"
     unfolding setext pair_def' by fast
  from arg_cong[OF this, of  swap_zero_one]
  show "\<ss>\<uu>\<cc>\<^sup>s \<emptyset> y = {\<emptyset>,y}\<^sub>M"
    unfolding \<open>swap_zero_one ({\<emptyset>,y}\<^sub>M) = {\<emptyset>,y}\<^sub>M\<close> by simp
qed     

lemma swap_setsuc_0_0: "\<ss>\<uu>\<cc>\<^sup>s \<emptyset> \<emptyset> = \<emptyset>"
  using zero_swap_mem_iff by auto 

lemma swap_setsuc_1_0: "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset> = \<emptyset>"
proof-
  have "u \<epsilon>\<^sup>s \<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset> \<longleftrightarrow> u = \<emptyset>" for u
    using one_swap by auto
  hence "swap_zero_one (\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset>) = {\<emptyset>}\<^sub>M"
    unfolding setext singleton_def' by blast
  from arg_cong[OF this, of  swap_zero_one]
  show "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset> = \<emptyset>"
    by (simp add: emptyset_def' one_swap)
qed

lemma swap_setsuc_1_1: "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) ({\<emptyset>}\<^sub>M) = {{\<emptyset>}\<^sub>M}\<^sub>M"
proof-
  have "{{\<emptyset>}\<^sub>M}\<^sub>M \<noteq> \<emptyset> \<and> {{\<emptyset>}\<^sub>M}\<^sub>M \<noteq> {\<emptyset>}\<^sub>M"
    unfolding setext[of "{_}\<^sub>M"] by (metis empty_is_empty singleton_def')  
  hence "swap_zero_one ({{\<emptyset>}\<^sub>M}\<^sub>M) = {{\<emptyset>}\<^sub>M}\<^sub>M"
    by (simp add: swap_zero_one_def)
  have "u \<epsilon>\<^sup>s \<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) ({\<emptyset>}\<^sub>M) \<longleftrightarrow> u = {\<emptyset>}\<^sub>M" for u
    using one_swap by auto
  hence "swap_zero_one (\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) ({\<emptyset>}\<^sub>M)) = {{\<emptyset>}\<^sub>M}\<^sub>M"
    unfolding setext singleton_def' by blast
  from arg_cong[OF this, of swap_zero_one]
  show "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) ({\<emptyset>}\<^sub>M) = {{\<emptyset>}\<^sub>M}\<^sub>M"
    unfolding \<open>swap_zero_one ({{\<emptyset>}\<^sub>M}\<^sub>M) = {{\<emptyset>}\<^sub>M}\<^sub>M\<close> by simp 
qed

lemma setsuc_setsuc': assumes "x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M"
  shows "\<ss>\<uu>\<cc>\<^sup>s x y = \<ss>\<uu>\<cc> x y"
proof-
  have "\<ss>\<uu>\<cc> x y \<noteq> {\<emptyset>}\<^sub>M" "\<ss>\<uu>\<cc> x y \<noteq> \<emptyset>"
    by (metis assms emptyset_def' setsuc_def' setsuc_triv singleton_def') (use emptyset_def' in auto)
  hence aux: "z \<epsilon>\<^sup>s \<ss>\<uu>\<cc> x y \<longleftrightarrow> z \<epsilon> \<ss>\<uu>\<cc> x y" "z \<epsilon>\<^sup>s x \<longleftrightarrow> z \<epsilon> x" for z
    by (simp_all add: assms swap_zero_one_mem)
  thus ?thesis
    unfolding swap.setext[of _ "\<ss>\<uu>\<cc> x y"] unfolding  aux swap.setsuc_def'[rule_format] setsuc_def'[rule_format] 
    by blast
qed

theorem setind_swap_setind: "L_setind (\<epsilon>) \<longrightarrow> L_setind (\<epsilon>\<^sup>s)"
proof
  assume "L_setind (\<epsilon>)"
  then interpret L_setind "(\<epsilon>)".
  show "L_setind (\<epsilon>\<^sup>s)" 
  proof (unfold_locales, rule impI, rule impI, rule allI)
    fix P :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and w and \<Xi>
    let ?P = "\<lambda> x. P(\<Xi>(0:= x))"
    assume "?P \<emptyset>\<^sup>s" and step: "\<forall>x y. ?P x \<longrightarrow> ?P (\<ss>\<uu>\<cc>\<^sup>s x y)" and SFP: "swap.SetFormulaPredicate P"
    hence "?P ({\<emptyset>}\<^sub>M)"
      using swap_empty by auto
    have aux: "(\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset>) = \<emptyset> \<longleftrightarrow> (\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset>) \<epsilon>\<^sup>s (\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset>)"
      using swap.setsuc_def' swap_zero_one_mem by blast
    have "\<ss>\<uu>\<cc>\<^sup>s ({\<emptyset>}\<^sub>M) \<emptyset> = \<emptyset>"
      by (metis swap.setsuc_empty_sing swap.singleton_eq swap_empty zero_swap_mem_iff)
    hence "?P \<emptyset>"
      using step[rule_format, OF \<open>?P ({\<emptyset>}\<^sub>M)\<close>, of \<emptyset>]   by simp
    have "SetFormulaPredicate P"
      by (simp add: SFP swap.permSFP_SFP)
    show "?P w"
    proof (rule setind[OF \<open>SetFormulaPredicate P\<close>, of \<Xi>, rule_format])
      show "?P \<emptyset>"
        by fact
    next
      fix x y
      assume "?P x"  
      show "?P (\<ss>\<uu>\<cc> x y)"
      proof-
        consider "x = \<emptyset> \<and> y = \<emptyset>" | "x = \<emptyset> \<and> y \<noteq> \<emptyset>"  | "x = {\<emptyset>}\<^sub>M \<and> y = \<emptyset>"  |  "x = {\<emptyset>}\<^sub>M \<and> y \<noteq> \<emptyset>" | "x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M"
          by blast
        then show ?thesis
        proof (cases) 
          assume "x = \<emptyset> \<and> y = \<emptyset>"
          then show "?P (\<ss>\<uu>\<cc> x y)"
            using \<open>P (\<Xi>(0 := {\<emptyset>}\<^sub>M))\<close> setsuc_empty_sing by auto
        next
          assume "x = \<emptyset> \<and> y \<noteq> \<emptyset>"
          then show "?P (\<ss>\<uu>\<cc> x y)"
            using step[rule_format, OF \<open>?P ({\<emptyset>}\<^sub>M)\<close>, of y] setsuc_empty_sing swap_setsuc_1_y by force
        next
          assume "x = {\<emptyset>}\<^sub>M \<and> y = \<emptyset>"
          then show "?P (\<ss>\<uu>\<cc> x y)"
            using \<open>P (\<Xi>(0 := x))\<close> singleton_def' by auto
        next
          assume "x = {\<emptyset>}\<^sub>M \<and> y \<noteq> \<emptyset>"
          hence "\<ss>\<uu>\<cc> x y = {\<emptyset>,y}\<^sub>M" 
            unfolding setext setsuc_def' singleton_def' pair_def' by force 
          hence "\<ss>\<uu>\<cc>\<^sup>s \<emptyset> y = \<ss>\<uu>\<cc> x y" 
            by (simp add: swap_setsuc_0_y \<open>x = {\<emptyset>}\<^sub>M \<and> y \<noteq> \<emptyset>\<close>) 
          then show "?P (\<ss>\<uu>\<cc> x y)"
            using step[rule_format, OF \<open>?P \<emptyset>\<close>, of y] by presburger
        next
          assume "x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M"
          then show "?P (\<ss>\<uu>\<cc> x y)"
            using setsuc_setsuc' step[rule_format, OF \<open>?P x\<close>] by force
        qed
      qed
    qed
  qed
qed

lemma ts_swap_ts: "L_ts (\<epsilon>) \<longrightarrow> L_ts (\<epsilon>\<^sup>s)"
proof
  assume "L_ts (\<epsilon>)"
  then interpret L_setext_sep_binunion_ts "(\<epsilon>)"
    by (simp add: L_binunion_axioms L_sep_axioms L_setext_axioms L_setext_sep_binunion_ts.intro) 
  have suc: "x \<union>\<^sub>M {\<emptyset>}\<^sub>M = \<ss>\<uu>\<cc> x \<emptyset>" for x
    unfolding binunion_def' singleton_def' setsuc_def' setext by blast
  have empts: "least_tsM ({\<emptyset>}\<^sub>M) = {\<emptyset>}\<^sub>M"
    unfolding setext unfolding least_ts_def' singleton_def'
    by (metis subsetM_def transM_def set_two_mem powerset_def' set_one_mem)
  show "L_ts (\<epsilon>\<^sup>s)"
  proof (unfold_locales, rule allI, unfold set_signature.transM_def set_signature.subsetM_def)
    fix x :: 'a
    consider "x = \<emptyset>" | "x = {\<emptyset>}\<^sub>M" | "x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M"
      by blast
    then show "\<exists>z. (\<forall>y. y \<epsilon>\<^sup>s z \<longrightarrow> (\<forall>za. za \<epsilon>\<^sup>s y \<longrightarrow> za \<epsilon>\<^sup>s z)) \<and>
             (\<forall>za. za \<epsilon>\<^sup>s x \<longrightarrow> za \<epsilon>\<^sup>s z)"
    proof (cases)
      assume "x = \<emptyset>"
      show ?thesis
        by (rule exI[of _ \<emptyset>], simp add: \<open>x = \<emptyset>\<close> swap_zero_one_mem)
    next
      assume "x = {\<emptyset>}\<^sub>M"
      show ?thesis
        by (rule exI[of _ "{\<emptyset>}\<^sub>M"], simp add: \<open>x = {\<emptyset>}\<^sub>M\<close> swap_zero_one_mem)  
    next
      assume "x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M"
      let ?t = "least_tsM (setsucM x \<emptyset>)" 
      have t: "?t = (least_tsM x) \<union>\<^sub>M {\<emptyset>}\<^sub>M"
        by (metis empts leastTS_union suc) 
      have "?t \<noteq> \<emptyset>"
        unfolding t setext binunion_def' singleton_def' by auto
      have esimp: "a \<epsilon>\<^sup>s ?t \<longleftrightarrow> a \<epsilon> least_tsM x \<or> a = \<emptyset>" for a
      proof  
        assume "a \<epsilon>\<^sup>s ?t"
        from swap_mem_mem[OF _ this]
        have "a \<epsilon> ?t"
          using \<open>x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M\<close> \<open>?t \<noteq> \<emptyset>\<close> by blast    
        show "a \<epsilon> least_tsM x \<or> a = \<emptyset>"
        proof (cases "a = \<emptyset>")
          assume "a \<noteq> \<emptyset>"
          have "a \<epsilon> least_tsM x"
            unfolding least_ts_def'
          proof (rule ccontr)
            assume "\<not> (\<forall>v. transM v \<and> x \<subseteq>\<^sub>M v \<longrightarrow> a \<epsilon> v)"
            then obtain v where "transM v" "x \<subseteq>\<^sub>M v" "\<not> a \<epsilon> v"
              by blast
            let ?v = "setsucM v \<emptyset>" 
            have "transM ?v" "\<ss>\<uu>\<cc> x \<emptyset> \<subseteq>\<^sub>M ?v"
              using \<open>transM v\<close> \<open>x \<subseteq>\<^sub>M v\<close> unfolding transM_def subsetM_def setsuc_def' by force+
            hence "a \<epsilon> ?v"
              using \<open>a \<epsilon> least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)\<close>[unfolded least_ts_def'] by blast
            thus False
              using \<open>\<not> a \<epsilon> v\<close> \<open>a \<noteq> \<emptyset>\<close> unfolding setsuc_def' by blast
          qed
          thus "a \<epsilon> least_tsM x \<or> a = \<emptyset>"
            by blast
        qed simp
      next
        assume "a \<epsilon> least_tsM x \<or> a = \<emptyset>" 
        hence "a \<epsilon> least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)"
          by (simp add: binunion_def' singleton_def' t)
        have "least_tsM (\<ss>\<uu>\<cc> x \<emptyset>) \<noteq> {\<emptyset>}\<^sub>M"
        proof
          assume "least_tsM (\<ss>\<uu>\<cc> x \<emptyset>) = {\<emptyset>}\<^sub>M"
          have "x \<subseteq>\<^sub>M least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)"
            by (simp add: least_ts_def' subsetM_def)
          show False  
            using \<open>x \<noteq> \<emptyset> \<and> x \<noteq> {\<emptyset>}\<^sub>M\<close>
            by (metis \<open>least_tsM (\<ss>\<uu>\<cc> x \<emptyset>) = {\<emptyset>}\<^sub>M\<close> \<open>x \<subseteq>\<^sub>M least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)\<close> powerset_def' set_one_def set_two_mem)
        qed
        then show "a \<epsilon>\<^sup>sleast_tsM (\<ss>\<uu>\<cc> x \<emptyset>)"
          by (simp add: \<open>a \<epsilon> least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)\<close> swap_zero_one_mem)
      qed
      show  "\<exists>z. (\<forall>y. y \<epsilon>\<^sup>s z \<longrightarrow> (\<forall>za. za \<epsilon>\<^sup>s y \<longrightarrow> za \<epsilon>\<^sup>s z)) \<and>
        (\<forall>za. za \<epsilon>\<^sup>s x \<longrightarrow> za \<epsilon>\<^sup>s z)"
      proof (rule exI[of _ ?t], rule conjI, rule allI, rule impI)
        fix y assume "y \<epsilon>\<^sup>s least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)"
        then show "\<forall>za. za \<epsilon>\<^sup>s y \<longrightarrow> za \<epsilon>\<^sup>s least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)"
          unfolding esimp by (metis  empty_mem_false least_ts_is_transitive set_signature.subsetM_def swap_zero_one_mem transM_def)
      next
        show "\<forall>za. za \<epsilon>\<^sup>s x \<longrightarrow> za \<epsilon>\<^sup>s least_tsM (\<ss>\<uu>\<cc> x \<emptyset>)"
          unfolding esimp using least_ts_def' subsetM_def swap_mem_mem by blast 
      qed
    qed
  qed
qed

end

theorem not_reg_model: assumes "L_setext_empty_power_union_repl (mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool)" "L_setind mem" "L_ts mem"
  shows "\<not> (\<forall> (m :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl m \<and> L_setind m \<and> L_ts m \<longrightarrow> L_reg m)"
proof (rule notI)
  assume contr: "\<forall>(m :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl m \<and> L_setind m \<and> L_ts m \<longrightarrow> L_reg m"
  interpret L_setext_empty_power_union_repl mem
    using assms by simp
  interpret L_setind mem 
    using assms by simp
  interpret permutation_model mem swap_zero_one
    using swap_zero_one_perm_model.
  have "L_setext_empty_power_union_repl perm_mem \<and> L_setind perm_mem \<and> L_ts perm_mem"
    by (simp add: perm_model setind_swap_setind ts_swap_ts \<open>L_setind mem\<close> \<open>L_ts mem\<close>)
  from contr[rule_format, OF this]
  show False
    using not_reg_swap_zero_one by blast 
qed

end