header {* \isaheader {ICF-Style Iterators} *}
theory Iterator_Locale
imports Main
begin

text {*
  The following locale makes explicit the iterator-concept as used in
  the Isabelle Collection Framework.

  Eventually, this theory is to be merged with the ICF.
*}

text {*
  Type of an iterator over elements of type @{text "'x"} and state of type 
  @{text "'\<sigma>"}.
*}
type_synonym ('x,'\<sigma>) iteratori_tmpl = "('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('x\<Rightarrow>'\<sigma>\<Rightarrow>'\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"

locale set_iteratori =
  fixes iterate::"('x,'\<sigma>) iteratori_tmpl" and S0::"'x set"
  assumes iterate_rule:
    "\<lbrakk> I S0 \<sigma>0; 
       \<And>S \<sigma> x. \<lbrakk> c \<sigma>; x\<in>S; I S \<sigma>; S\<subseteq>S0 \<rbrakk> \<Longrightarrow> I (S-{x}) (f x \<sigma>)
     \<rbrakk> \<Longrightarrow> 
      I {} (iterate c f \<sigma>0) \<or> 
      (\<exists>S. S \<subseteq> S0 \<and> S \<noteq> {} \<and> 
            \<not> (c (iterate c f \<sigma>0)) \<and> 
            I S (iterate c f \<sigma>0))"
begin
  lemma iterate_rule_P':
    "\<lbrakk>
      I S0 \<sigma>0;
      !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> 
                  \<Longrightarrow> I (S - {x}) (f x \<sigma>);
      \<lbrakk> I {} (iterate c f \<sigma>0)\<rbrakk>  \<Longrightarrow> P;
      !!S. \<lbrakk> S \<subseteq> S0; S \<noteq> {}; 
              \<not> (c (iterate c f \<sigma>0)); 
              I S (iterate c f \<sigma>0) \<rbrakk> \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P"
  proof -
    assume 
      I: "I S0 \<sigma>0" and 
      R: "\<And>S \<sigma> x. \<lbrakk>c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0\<rbrakk> \<Longrightarrow> I (S - {x}) (f x \<sigma>)" and
      C1: "I {} (iterate c f \<sigma>0) \<Longrightarrow> P" and
      C2:"\<And>S. \<lbrakk>S \<subseteq> S0; S \<noteq> {}; \<not> c (iterate c f \<sigma>0); I S (iterate c f \<sigma>0)\<rbrakk> 
            \<Longrightarrow> P"
      
    have "I {} (iterate c f \<sigma>0) \<or> 
      (\<exists>S. S \<subseteq> S0 \<and> S \<noteq> {} \<and> 
            \<not> (c (iterate c f \<sigma>0)) \<and> 
            I S (iterate c f \<sigma>0))"
      apply (rule iterate_rule[of I, OF I])
      apply (rule R)
      by auto
    with C1 C2 show P by blast
  qed

  lemma iterate_rule_P:
    "\<lbrakk>
      I S0 \<sigma>0;
      !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> 
                    \<Longrightarrow> I (S - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> {}; \<not> c \<sigma>; I S \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iterate c f \<sigma>0)"
    by (rule iterate_rule_P')
end
end
