theory VectorSpace
  imports Main HOL.Real "HOL-Types_To_Sets.Linear_Algebra_On_With"

begin

locale vector_space_with_domain =
  fixes dom :: "'a set"
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"      
    and zero :: "'a"
    and smult :: "real \<Rightarrow> 'a \<Rightarrow> 'a"   
  assumes add_closed: "\<lbrakk>x \<in> dom; y \<in> dom\<rbrakk> \<Longrightarrow> add x y \<in> dom" 
    and zero_in_dom: "zero \<in> dom"      
    and add_assoc: "\<lbrakk>x \<in> dom; y \<in> dom; z\<in> dom\<rbrakk> \<Longrightarrow>add (add x y) z = add x (add y z)"
    and add_comm: "\<lbrakk>x \<in> dom; y \<in> dom\<rbrakk> \<Longrightarrow> add x y = add y x"
    and add_zero: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> add x zero = x"
    and add_inv: "x \<in> dom \<Longrightarrow> \<exists>y \<in> dom. add x y = zero"
    and smult_closed: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> smult a x \<in> dom"
    and smult_distr_sadd: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow>smult (a + b) x = add (smult a x) (smult b x)"
    and smult_assoc: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> smult a  (smult b x) = smult (a * b)  x"
    and smult_one: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> smult 1 x = x" 
    and smult_distr_sadd2: "\<lbrakk>x \<in> dom; y\<in>dom\<rbrakk> \<Longrightarrow> smult a (add x y) = add (smult a x) (smult a y)"

begin

lemma inv_unique:
  assumes "a\<in>dom" "z1\<in>dom" "z2\<in>dom"
      "add a z1 = zero"
      "add a z2 = zero"
    shows "z1=z2"
  by (metis add_assoc add_comm add_zero assms)

definition inv::"'a\<Rightarrow>'a" where 
    "inv a = (if a\<in>dom then (THE z. (z\<in>dom \<and> add a z = zero)) else undefined)"

definition minus::"'a\<Rightarrow>'a\<Rightarrow>'a" where
    "minus a b = (if a\<in>dom \<and> b\<in>dom then add a (inv b) else undefined)"

lemma module_on_with_is_this:
  shows "module_on_with dom add minus inv zero smult"
  unfolding module_on_with_def
proof
  show "ab_group_add_on_with dom add zero local.minus local.inv"
    unfolding ab_group_add_on_with_def
  proof
    show "comm_monoid_add_on_with dom add zero"
      by (smt (verit, del_insts) ab_semigroup_add_on_with_Ball_def add_assoc add_closed add_comm add_zero comm_monoid_add_on_with_Ball_def semigroup_add_on_with_def zero_in_dom)
    next
    show "ab_group_add_on_with_axioms dom add zero local.minus local.inv"
      unfolding ab_group_add_on_with_axioms_def
    proof
      show "\<forall>a. a \<in> dom \<longrightarrow> add (local.inv a) a = zero"
      proof-
        {fix a 
          assume "a\<in>dom"
          obtain "z" where "z\<in>dom \<and> add z a = zero"
            using \<open>a \<in> dom\<close> add_comm add_inv by blast
          moreover have "local.inv a = z"
            using \<open>a \<in> dom\<close> add_comm calculation inv_unique local.inv_def by auto
          ultimately have " add (local.inv a) a = zero"
          using `a\<in>dom`
          by fastforce
          
      }
      show ?thesis 
        using \<open>\<And>aa. aa \<in> dom \<Longrightarrow> add (local.inv aa) aa = zero\<close> by blast
    qed
  next
    show " (\<forall>a b. a \<in> dom \<longrightarrow> b \<in> dom \<longrightarrow> local.minus a b = add a (local.inv b)) \<and>
    (\<forall>a. a \<in> dom \<longrightarrow> local.inv a \<in> dom)"
    proof
      show "\<forall>a b. a \<in> dom \<longrightarrow> b \<in> dom \<longrightarrow> local.minus a b = add a (local.inv b)"
        using minus_def by auto
    next
      show "\<forall>a. a \<in> dom \<longrightarrow> local.inv a \<in> dom"
      proof-
        {fix a 
        assume "a\<in>dom"
        have "local.inv a \<in>dom"
          by (smt (z3) \<open>a \<in> dom\<close> add_assoc add_comm add_inv add_zero local.inv_def theI')
      }
      show ?thesis 
        using \<open>\<And>aa. aa \<in> dom \<Longrightarrow> local.inv aa \<in> dom\<close> by fastforce
        qed
      qed
  qed  
  qed
next
  show " ((\<forall>a. \<forall>x\<in>dom. \<forall>y\<in>dom. smult a (add x y) = add (smult a x) (smult a y)) \<and>
     (\<forall>a b. \<forall>x\<in>dom. smult (a + b) x = add (smult a x) (smult b x))) \<and>
    (\<forall>a b. \<forall>x\<in>dom. smult a (smult b x) = smult (a * b) x) \<and>
    (\<forall>x\<in>dom. smult 1 x = x) \<and> (\<forall>a. \<forall>x\<in>dom. smult a x \<in> dom)"
    using smult_one smult_distr_sadd smult_assoc smult_closed
      smult_distr_sadd2
    by auto
qed

lemma vector_space_on_with_is_this:
  shows "vector_space_on_with dom add minus inv zero smult"
  by (simp add: module_on_with_is_this vector_space_on_with_def)

end

end
