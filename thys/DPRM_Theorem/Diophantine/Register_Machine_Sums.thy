subsubsection \<open>Preliminary: Register machine sums are Diophantine\<close>

theory Register_Machine_Sums imports Diophantine_Relations
                                     "../Register_Machine/RegisterMachineSimulation"

begin

fun sum_polynomial :: "(nat \<Rightarrow> polynomial) \<Rightarrow> nat list \<Rightarrow> polynomial" where
  "sum_polynomial f [] = Const 0" |
  "sum_polynomial f (i#idxs) = f i [+] sum_polynomial f idxs" 

lemma sum_polynomial_eval: 
  "peval (sum_polynomial f idxs) a = (\<Sum>k=0..<length idxs. peval (f (idxs!k)) a)"
proof (induction "idxs" rule: List.rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  moreover have suc: "peval (sum_polynomial f (xs @ [x])) a = peval (sum_polynomial f (x # xs)) a"
    by (induction xs, auto)
  moreover have list_property: "xa < length xs \<Longrightarrow> (xs ! xa) = (xs @ [x]) ! xa" for xa
    by (simp add: nth_append)
  ultimately show ?case by auto 
qed
  
 
definition sum_program :: "program \<Rightarrow> (nat \<Rightarrow> polynomial) \<Rightarrow> polynomial" 
  ("[\<Sum>_] _" [100, 100] 100) where
  "[\<Sum>p] f \<equiv> sum_polynomial f [0..<length p]" 

lemma sum_program_push: "m = length ns \<Longrightarrow> length l = length p \<Longrightarrow>
  peval ([\<Sum>p] (\<lambda>k. if g k then map (\<lambda>x. push_param x m) l ! k else h k)) (push_list a ns)
    = peval ([\<Sum>p] (\<lambda>k. if g k then l ! k else h k)) a"
  unfolding sum_program_def apply (induction p, auto)
  oops

definition sum_radd_polynomial :: "program \<Rightarrow> register \<Rightarrow> (nat \<Rightarrow> polynomial) \<Rightarrow> polynomial" 
  ("[\<Sum>R+] _ _ _") where
  "[\<Sum>R+] p l f \<equiv> [\<Sum>p] (\<lambda>k. if isadd (p!k) \<and> l = modifies (p!k) then f k else Const 0)"

lemma sum_radd_polynomial_eval[defs]:
  assumes "length p > 0"
  shows "peval ([\<Sum>R+] p l f) a = (\<Sum>R+ p l (\<lambda>x. peval (f x) a))"
proof - 
  have 1: "x \<le> length p - Suc 0 \<Longrightarrow> x < length p" for x using assms by linarith
  have 2: "x \<le> length p - Suc 0 \<Longrightarrow> peval (f ([0..<length p] ! x)) a = peval (f x) a" for x 
    using assms
    by (metis diff_Suc_less less_imp_diff_less less_le_not_le nat_neq_iff nth_upt plus_nat.add_0)
  show ?thesis 
  unfolding sum_radd_polynomial_def sum_program_def sum_radd.simps sum_polynomial_eval
  by (auto, rule sum.cong, auto simp: 1 2)
qed

definition sum_rsub_polynomial :: "program \<Rightarrow> register \<Rightarrow> (nat \<Rightarrow> polynomial) \<Rightarrow> polynomial" 
  ("[\<Sum>R-] _ _ _") where
  "[\<Sum>R-] p l f \<equiv> [\<Sum>p] (\<lambda>k. if issub (p!k) \<and> l = modifies (p!k) then f k else Const 0)"

lemma sum_rsub_polynomial_eval[defs]:
  assumes "length p > 0"
  shows "peval ([\<Sum>R-] p l f) a = (\<Sum>R- p l (\<lambda>x. peval (f x) a))"
proof - 
  have 1: "x \<le> length p - Suc 0 \<Longrightarrow> x < length p" for x using assms by linarith
  have 2: "x \<le> length p - Suc 0 \<Longrightarrow> peval (f ([0..<length p] ! x)) a = peval (f x) a" for x 
    using assms
    by (metis diff_Suc_less less_imp_diff_less less_le_not_le nat_neq_iff nth_upt plus_nat.add_0)
  show ?thesis 
  unfolding sum_rsub_polynomial_def sum_program_def sum_rsub.simps sum_polynomial_eval
  by (auto, rule sum.cong, auto simp: 1 2)
qed

definition sum_sadd_polynomial :: "program \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> polynomial) \<Rightarrow> polynomial" 
  ("[\<Sum>S+] _ _ _") where
  "[\<Sum>S+] p d f \<equiv> [\<Sum>p] (\<lambda>k. if isadd (p!k) \<and> d = goes_to (p!k) then f k else Const 0)"

lemma sum_sadd_polynomial_eval[defs]:
  assumes "length p > 0"
  shows "peval ([\<Sum>S+] p d f) a = (\<Sum>S+ p d (\<lambda>x. peval (f x) a))"
proof - 
  have 1: "x \<le> length p - Suc 0 \<Longrightarrow> x < length p" for x using assms by linarith
  have 2: "x \<le> length p - Suc 0 \<Longrightarrow> peval (f ([0..<length p] ! x)) a = peval (f x) a" for x 
    using assms
    by (metis diff_Suc_less less_imp_diff_less less_le_not_le nat_neq_iff nth_upt plus_nat.add_0)
  show ?thesis 
  unfolding sum_sadd_polynomial_def sum_program_def sum_sadd.simps sum_polynomial_eval
  by (auto, rule sum.cong, auto simp: 1 2)
qed

definition sum_ssub_nzero_polynomial :: "program \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> polynomial) \<Rightarrow> polynomial" 
  ("[\<Sum>S-] _ _ _") where
  "[\<Sum>S-] p d f \<equiv> [\<Sum>p] (\<lambda>k. if issub (p!k) \<and> d = goes_to (p!k) then f k else Const 0)"

lemma sum_ssub_nzero_polynomial_eval[defs]:
  assumes "length p > 0"
  shows "peval ([\<Sum>S-] p d f) a = (\<Sum>S- p d (\<lambda>x. peval (f x) a))" 
proof -
  have 1: "x \<le> length p - Suc 0 \<Longrightarrow> x < length p" for x using assms by linarith
  have 2: "x \<le> length p - Suc 0 \<Longrightarrow> peval (f ([0..<length p] ! x)) a = peval (f x) a" for x 
    using assms
    by (metis diff_Suc_less less_imp_diff_less less_le_not_le nat_neq_iff nth_upt plus_nat.add_0)
  show ?thesis 
  unfolding sum_ssub_nzero_polynomial_def sum_program_def sum_ssub_nzero.simps sum_polynomial_eval
  by (auto, rule sum.cong, auto simp: 1 2)
qed

definition sum_ssub_zero_polynomial :: "program \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> polynomial) \<Rightarrow> polynomial" 
  ("[\<Sum>S0] _ _ _") where
  "[\<Sum>S0] p d f \<equiv> [\<Sum>p] (\<lambda>k. if issub (p!k) \<and> d = goes_to_alt (p!k) then f k else Const 0)"

lemma sum_ssub_zero_polynomial_eval[defs]:
  assumes "length p > 0"
  shows "peval ([\<Sum>S0] p d f) a = (\<Sum>S0 p d (\<lambda>x. peval (f x) a))"
proof - 
  have 1: "x \<le> length p - Suc 0 \<Longrightarrow> x < length p" for x using assms by linarith
  have 2: "x \<le> length p - Suc 0 \<Longrightarrow> peval (f ([0..<length p] ! x)) a = peval (f x) a" for x 
    using assms
    by (metis diff_Suc_less less_imp_diff_less less_le_not_le nat_neq_iff nth_upt plus_nat.add_0)
  show ?thesis 
  unfolding sum_ssub_zero_polynomial_def sum_program_def sum_ssub_zero.simps sum_polynomial_eval
  by (auto, rule sum.cong, auto simp: 1 2)
qed


end