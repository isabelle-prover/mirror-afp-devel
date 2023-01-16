theory Strict_Omega_Category
imports Globular_Set

begin

section \<open>Strict $\omega$-categories\<close>

text \<open>
  First, we define a locale \<open>pre_strict_omega_category\<close> that holds the data of a strict
  $\omega$-category without the associativity, unity and exchange axioms
  \cite[Def 1.4.8 (a) - (b)]{Leinster2004}. We do this in order to set up convenient notation
  before we state the remaining axioms.
\<close>

locale pre_strict_omega_category = globular_set +
  fixes comp :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and i :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes comp_fun: "is_composable_pair m n x' x \<Longrightarrow> comp m n x' x \<in> X m"
    and i_fun: "i n \<in> X n \<rightarrow> X (Suc n)"
    and s_comp_Suc: "is_composable_pair (Suc m) m x' x \<Longrightarrow> s m (comp (Suc m) m x' x) = s m x"
    and t_comp_Suc: "is_composable_pair (Suc m) m x' x \<Longrightarrow> t m (comp (Suc m) m x' x) = t m x'"
    and s_comp: "\<lbrakk>is_composable_pair (Suc m) n x' x; n < m\<rbrakk> \<Longrightarrow>
          s m (comp (Suc m) n x' x) = comp m n (s m x') (s m x)"
    and t_comp: "\<lbrakk>is_composable_pair (Suc m) n x' x; n < m\<rbrakk> \<Longrightarrow>
          t m (comp (Suc m) n x' x) = comp m n (t m x') (s m x)"
    and s_i: "x \<in> X n \<Longrightarrow> s n (i n x) = x"
    and t_i: "x \<in> X n \<Longrightarrow> t n (i n x) = x"
begin

text \<open>Similar to the generalised source and target maps in \<open>globular_set\<close>, we defined a generalised
identity map. The first argument gives the dimension of the resulting identity cell, while the
second gives the dimension of the input cell.\<close>

fun i' :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"i' 0 0 = id" |
"i' 0 (Suc n) = undefined" |
"i' (Suc m) n = (if Suc m < n then undefined
  else if Suc m = n then id
  else i m \<circ> i' m n)"

lemma i'_n_n [simp]: "i' n n = id"
  by (metis i'.elims i'.simps(1) less_irrefl_nat)

lemma i'_Suc_n_n [simp]: "i' (Suc n) n = i n"
  by simp

lemma i'_Suc [simp]: "n \<le> m \<Longrightarrow> i' (Suc m) n = i m \<circ> i' m n"
  by fastforce

lemma i'_Suc': "n < m \<Longrightarrow> i' m n = i' m (Suc n) \<circ> i n"
proof (induction m arbitrary: n)
  case 0
  then show ?case by blast
next
  case (Suc m)
  then show ?case by force
qed

lemma i'_fun: "n \<le> m \<Longrightarrow> i' m n \<in> X n \<rightarrow> X m"
proof (induction m arbitrary: n)
  case 0
  then show ?case by fastforce
next
  case (Suc m)
  thus ?case proof (cases "n = Suc m")
    case True
    then show ?thesis by auto
  next
    case False
    hence "n \<le> m" using `n \<le> Suc m` by force
    thus ?thesis using Suc.IH i_fun by auto
  qed
qed
  
end

text \<open>Now we may define a strict $\omega$-category including the composition, unity and exchange
  axioms \cite[Def 1.4.8 (c) - (f)]{Leinster2004}.\<close>

locale strict_omega_category = pre_strict_omega_category +
  assumes comp_assoc: "\<lbrakk>is_composable_pair m n x' x; is_composable_pair m n x'' x'\<rbrakk> \<Longrightarrow> 
            comp m n (comp m n x'' x') x = comp m n x'' (comp m n x' x)"
    and i_comp: "\<lbrakk>n < m; x \<in> X m\<rbrakk> \<Longrightarrow> comp m n (i' m n (t' m n x)) x = x"
    and comp_i: "\<lbrakk>n < m; x \<in> X m\<rbrakk> \<Longrightarrow> comp m n x (i' m n (s' m n x)) = x"
    and bin_interchange: "\<lbrakk>q < p; p < m;
          is_composable_pair m p y' y; is_composable_pair m p x' x;
          is_composable_pair m q y' x'; is_composable_pair m q y x\<rbrakk> \<Longrightarrow>
          comp m q (comp m p y' y) (comp m p x' x) = comp m p (comp m q y' x') (comp m q y x)"
    and null_interchange: "\<lbrakk>q < p; is_composable_pair p q x' x\<rbrakk> \<Longrightarrow>
          comp (Suc p) q (i p x') (i p x) = i p (comp p q x' x)"

locale strict_omega_functor = globular_map + 
  source: strict_omega_category X s\<^sub>X t\<^sub>X comp\<^sub>X i\<^sub>X + 
  target: strict_omega_category Y s\<^sub>Y t\<^sub>Y comp\<^sub>Y i\<^sub>Y 
  for comp\<^sub>X i\<^sub>X comp\<^sub>Y i\<^sub>Y +
  assumes commute_with_comp: "is_composable_pair m n x' x \<Longrightarrow>
      \<phi> m (comp\<^sub>X m n x' x) = comp\<^sub>Y m n (\<phi> m x') (\<phi> m x)"
    and commute_with_id: "x \<in> X n \<Longrightarrow> \<phi> (Suc n) (i\<^sub>X n x) = i\<^sub>Y n (\<phi> n x)"

end