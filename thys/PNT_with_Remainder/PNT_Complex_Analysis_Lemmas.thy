theory PNT_Complex_Analysis_Lemmas
imports
  "PNT_Remainder_Library"
begin
unbundle pnt_syntax

section \<open>Some basic theorems in complex analysis\<close>

subsection \<open>Introduction rules for holomorphic functions and analytic functions\<close>

lemma holomorphic_on_shift [holomorphic_intros]:
  assumes "f holomorphic_on ((\<lambda>z. s + z) ` A)"
  shows "(\<lambda>z. f (s + z)) holomorphic_on A"
proof -
  have "(f \<circ> (\<lambda>z. s + z)) holomorphic_on A"
    using assms by (intro holomorphic_on_compose holomorphic_intros)
  thus ?thesis unfolding comp_def by auto
qed

lemma holomorphic_logderiv [holomorphic_intros]:
  assumes "f holomorphic_on A" "open A" "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>s. logderiv f s) holomorphic_on A"
  using assms unfolding logderiv_def by (intro holomorphic_intros)

lemma holomorphic_glue_to_analytic:
  assumes o: "open S" "open T"
     and hf: "f holomorphic_on S"
     and hg: "g holomorphic_on T"
     and hI: "\<And>z. z \<in> S \<Longrightarrow> z \<in> T \<Longrightarrow> f z = g z"
     and hU: "U \<subseteq> S \<union> T"
  obtains h
   where "h analytic_on U"
         "\<And>z. z \<in> S \<Longrightarrow> h z = f z"
         "\<And>z. z \<in> T \<Longrightarrow> h z = g z"
proof -
  define h where "h z \<equiv> if z \<in> S then f z else g z" for z
  show ?thesis proof
    have "h holomorphic_on S \<union> T"
      unfolding h_def by (rule holomorphic_on_If_Un) (use assms in auto)
    thus "h analytic_on U"
      by (subst analytic_on_holomorphic) (use hU o in auto)
  next
    fix z assume *:"z \<in> S"
    show "h z = f z" unfolding h_def using * by auto
  next
    fix z assume *:"z \<in> T"
    show "h z = g z" unfolding h_def using * hI by auto
  qed
qed

lemma analytic_on_powr_right [analytic_intros]:
  assumes "f analytic_on s"
  shows "(\<lambda>z. w powr f z) analytic_on s"
proof (cases "w = 0")
  case False
  with assms show ?thesis
    unfolding analytic_on_def holomorphic_on_def field_differentiable_def
    by (metis (full_types) DERIV_chain' has_field_derivative_powr_right)
qed simp

subsection \<open>Factorization of analytic function on compact region\<close>

definition not_zero_on (infixr \<open>not'_zero'_on\<close> 46)
  where "f not_zero_on S \<equiv> \<exists>z \<in> S. f z \<noteq> 0"

lemma not_zero_on_obtain:
  assumes "f not_zero_on S" and "S \<subseteq> T"
  obtains t where "f t \<noteq> 0" and "t \<in> T"
using assms unfolding not_zero_on_def by auto

lemma analytic_on_holomorphic_connected:
  assumes hf: "f analytic_on S"
    and con: "connected A"
    and ne: "\<xi> \<in> A" and AS: "A \<subseteq> S"
  obtains T T' where
    "f holomorphic_on T" "f holomorphic_on T'"
    "open T" "open T'" "A \<subseteq> T" "S \<subseteq> T'" "connected T"
proof -
  obtain T'
  where oT': "open T'" and sT': "S \<subseteq> T'"
    and holf': "f holomorphic_on T'"
    using analytic_on_holomorphic hf by blast
  define T where "T \<equiv> connected_component_set T' \<xi>"
  have TT': "T \<subseteq> T'" unfolding T_def by (rule connected_component_subset)
  hence holf: "f holomorphic_on T" using holf' by auto
  have opT: "open T" unfolding T_def using oT' by (rule open_connected_component)
  have conT: "connected T" unfolding T_def by (rule connected_connected_component)
  have "A \<subseteq> T'" using AS sT' by blast
  hence AT: "A \<subseteq> T" unfolding T_def using ne con by (intro connected_component_maximal)
  show ?thesis using holf holf' opT oT' AT sT' conT that by blast
qed

lemma analytic_factor_zero:
  assumes hf: "f analytic_on S"
    and KS: "K \<subseteq> S" and con: "connected K"
    and \<xi>K: "\<xi> \<in> K" and \<xi>z: "f \<xi> = 0"
    and nz: "f not_zero_on K"
  obtains g r n
    where "0 < n" "0 < r"
          "g analytic_on S" "g not_zero_on K"
          "\<And>z. z \<in> S \<Longrightarrow> f z = (z - \<xi>)^n * g z"
          "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> g z \<noteq> 0"
proof -
  have "f analytic_on S" "connected K"
       "\<xi> \<in> K" "K \<subseteq> S" using assms by auto
  then obtain T T'
  where holf: "f holomorphic_on T"
    and holf': "f holomorphic_on T'"
    and opT: "open T" and oT': "open T'"
    and KT: "K \<subseteq> T" and ST': "S \<subseteq> T'"
    and conT: "connected T"
    by (rule analytic_on_holomorphic_connected)
  obtain \<eta> where f\<eta>: "f \<eta> \<noteq> 0" and \<eta>K: "\<eta> \<in> K"
    using nz by (rule not_zero_on_obtain, blast)
  hence \<xi>T: "\<xi> \<in> T" and \<xi>T': "\<xi> \<in> T'"
    and \<eta>T: "\<eta> \<in> T" using \<xi>K \<eta>K KT KS ST' by blast+
  hence nc: "\<not> f constant_on T" using f\<eta> \<xi>z unfolding constant_on_def by fastforce
  obtain g r n
  where 1: "0 < n" and 2: "0 < r"
    and bT: "ball \<xi> r \<subseteq> T"
    and hg: "g holomorphic_on ball \<xi> r"
    and fw: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> f z = (z - \<xi>) ^ n * g z"
    and gw: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> g z \<noteq> 0"
    by (rule holomorphic_factor_zero_nonconstant, (rule holf opT conT \<xi>T \<xi>z nc)+, blast)
  have sT: "S \<subseteq> T' - {\<xi>} \<union> ball \<xi> r" using 2 ST' by auto
  have hz: "(\<lambda>z. f z / (z - \<xi>) ^ n) holomorphic_on (T' - {\<xi>})"
    using holf' by ((intro holomorphic_intros)+, auto)
  obtain h
   where 3: "h analytic_on S"
     and hf: "\<And>z. z \<in> T' - {\<xi>} \<Longrightarrow> h z = f z / (z - \<xi>) ^ n"
     and hb: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> h z = g z"
    by (rule holomorphic_glue_to_analytic
       [where f = "\<lambda>z. f z / (z - \<xi>) ^ n" and
         g = g and S = "T' - {\<xi>}" and T = "ball \<xi> r" and U = S])
       (use oT' 2 ST' hg fw hz in \<open>auto simp add: holomorphic_intros\<close>)
  have "\<xi> \<in> ball \<xi> r" using 2 by auto
  hence "h \<xi> \<noteq> 0" using hb gw 2 by auto
  hence 4: "h not_zero_on K" unfolding not_zero_on_def using \<xi>K by auto
  have 5: "f z = (z - \<xi>)^n * h z" if *: "z \<in> S" for z
  proof -
    consider "z = \<xi>" | "z \<in> S - {\<xi>}" using * by auto
    thus ?thesis proof cases
      assume *: "z = \<xi>"
      show ?thesis using \<xi>z 1 by (subst (1 2) *, auto)
    next
      assume *: "z \<in> S - {\<xi>}"
      show ?thesis using hf ST' * by (auto simp add: field_simps)
    qed
  qed
  have 6: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> h w \<noteq> 0" using hb gw by auto
  show ?thesis by ((standard; rule 1 2 3 4 5 6), blast+)
qed

lemma analytic_compact_finite_zeros:
  assumes af: "f analytic_on S"
    and KS: "K \<subseteq> S"
    and con: "connected K"
    and cm: "compact K"
    and nz: "f not_zero_on K"
  shows "finite {z \<in> K. f z = 0}"
proof (cases "f constant_on K")
  assume *: "f constant_on K"
  have "\<And>z. z \<in> K \<Longrightarrow> f z \<noteq> 0" using nz * unfolding not_zero_on_def constant_on_def by auto
  hence **: "{z \<in> K. f z = 0} = {}" by auto
  thus ?thesis by (subst **, auto)
next
  assume *: "\<not> f constant_on K"
  obtain \<xi> where ne: "\<xi> \<in> K" using not_zero_on_obtain nz by blast
  obtain T T' where opT: "open T" and conT: "connected T"
    and ST: "K \<subseteq> T" and holf: "f holomorphic_on T"
    and "f holomorphic_on T'"
    by (metis af KS con ne analytic_on_holomorphic_connected)
  have "\<not> f constant_on T" using ST * unfolding constant_on_def by blast
  thus ?thesis using holf opT conT cm ST by (intro holomorphic_compact_finite_zeros)
qed

subsubsection \<open>Auxiliary propositions for theorem \<open>analytic_factorization\<close>\<close>

definition analytic_factor_p' where
 \<open>analytic_factor_p' f S K \<equiv>
  \<exists>g n. \<exists>\<alpha> :: nat \<Rightarrow> complex.
        g analytic_on S
      \<and> (\<forall>z \<in> K. g z \<noteq> 0)
      \<and> (\<forall>z \<in> S. f z = g z * (\<Prod>k<n. z - \<alpha> k))
      \<and> \<alpha> ` {..<n} \<subseteq> K\<close>

definition analytic_factor_p where
 \<open>analytic_factor_p F \<equiv>
  \<forall>f S K. f analytic_on S
    \<longrightarrow> K \<subseteq> S
    \<longrightarrow> connected K
    \<longrightarrow> compact K
    \<longrightarrow> f not_zero_on K
    \<longrightarrow> {z \<in> K. f z = 0} = F
    \<longrightarrow> analytic_factor_p' f S K\<close>

lemma analytic_factorization_E:
  shows "analytic_factor_p {}"
unfolding analytic_factor_p_def
proof (intro conjI allI impI)
  fix f S K
  assume af: "f analytic_on S"
     and KS: "K \<subseteq> S"
     and con: "connected K"
     and cm: "compact K"
     and nz: "{z \<in> K. f z = 0} = {}"
  show "analytic_factor_p' f S K"
  unfolding analytic_factor_p'_def
  proof (intro ballI conjI exI)
    show "f analytic_on S" "\<And>z. z \<in> K \<Longrightarrow> f z \<noteq> 0"
         "\<And>z. z \<in> S \<Longrightarrow> f z = f z * (\<Prod>k<(0 :: nat). z - (\<lambda>_. 0) k)"
      by (rule af, use nz in auto)
    show "(\<lambda>k :: nat. 0) ` {..<0} \<subseteq> K" by auto
  qed
qed

lemma analytic_factorization_I:
  assumes ind: "analytic_factor_p F"
    and \<xi>ni: "\<xi> \<notin> F"
  shows "analytic_factor_p (insert \<xi> F)"
unfolding analytic_factor_p_def
proof (intro allI impI)
  fix f S K
  assume af: "f analytic_on S"
    and KS: "K \<subseteq> S"
    and con: "connected K"
    and nz: "f not_zero_on K"
    and cm: "compact K"
    and zr: "{z \<in> K. f z = 0} = insert \<xi> F"
  show "analytic_factor_p' f S K"
  proof -
    have "f analytic_on S" "K \<subseteq> S" "connected K"
         "\<xi> \<in> K" "f \<xi> = 0" "f not_zero_on K"
    using af KS con zr nz by auto
    then obtain h r k
    where "0 < k" and "0 < r" and ah: "h analytic_on S"
      and nh: "h not_zero_on K"
      and f_z: "\<And>z. z \<in> S \<Longrightarrow> f z = (z - \<xi>) ^ k * h z"
      and ball: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> h z \<noteq> 0"
    by (rule analytic_factor_zero) blast
    hence h\<xi>: "h \<xi> \<noteq> 0" using ball by auto
    hence "\<And>z. z \<in> K \<Longrightarrow> h z = 0 \<longleftrightarrow> f z = 0 \<and> z \<noteq> \<xi>" by (subst f_z) (use KS in auto)
    hence "{z \<in> K. h z = 0} = {z \<in> K. f z = 0} - {\<xi>}" by auto
    also have "\<dots> = F" by (subst zr, intro Diff_insert_absorb \<xi>ni)
    finally have "{z \<in> K. h z = 0} = F" .
    hence "analytic_factor_p' h S K"
      using ind ah KS con cm nh
      unfolding analytic_factor_p_def by auto
    then obtain g n and \<alpha> :: "nat \<Rightarrow> complex"
    where ag: "g analytic_on S" and
      ng: "\<And>z. z \<in> K \<Longrightarrow> g z \<noteq> 0" and
      h_z: "\<And>z. z \<in> S \<Longrightarrow> h z = g z * (\<Prod>k<n. z - \<alpha> k)" and
      Im\<alpha>: "\<alpha> ` {..<n} \<subseteq> K"
    unfolding analytic_factor_p'_def by fastforce
    define \<beta> where "\<beta> j \<equiv> if j < n then \<alpha> j else \<xi>" for j
    show ?thesis
    unfolding analytic_factor_p'_def
    proof (intro ballI conjI exI)
      show "g analytic_on S" "\<And>z. z \<in> K \<Longrightarrow> g z \<noteq> 0"
        by (rule ag, rule ng)
    next
      fix z assume *: "z \<in> S"
      show "f z = g z * (\<Prod>j<n+k. z - \<beta> j)"
      proof -
        have "(\<Prod>j<n. z - \<beta> j) = (\<Prod>j<n. z - \<alpha> j)"
            "(\<Prod>j=n..<n+k. z - \<beta> j) = (z - \<xi>) ^ k"
        unfolding \<beta>_def by auto
        moreover have "(\<Prod>j<n+k. z - \<beta> j) = (\<Prod>j<n. z - \<beta> j) * (\<Prod>j=n..<n+k. z - \<beta> j)"
        by (metis Metric_Arith.nnf_simps(8) atLeast0LessThan
           not_add_less1 prod.atLeastLessThan_concat zero_order(1))
        ultimately have "(\<Prod>j<n+k. z - \<beta> j) = (z - \<xi>) ^ k * (\<Prod>j<n. z - \<alpha> j)" by auto
        moreover have "f z = g z * ((z - \<xi>) ^ k * (\<Prod>j<n. z - \<alpha> j))"
        by (subst f_z; (subst h_z)?, use * in auto)
        ultimately show ?thesis by auto
      qed
    next
      show "\<beta> ` {..<n + k} \<subseteq> K" unfolding \<beta>_def using Im\<alpha> \<open>\<xi> \<in> K\<close> by auto
    qed
  qed
qed

text \<open>A nontrivial analytic function on connected compact region can
  be factorized as a everywhere-non-zero function and linear terms $z - s_0$
  for all zeros $s_0$. Note that the connected assumption of $K$ may be
  removed, but we remain it just for simplicity of proof.\<close>

(* TODO: Move to library? *)
theorem analytic_factorization:
  assumes af: "f analytic_on S"
    and KS: "K \<subseteq> S"
    and con: "connected K"
    and "compact K"
    and "f not_zero_on K"
  obtains g n and \<alpha> :: "nat \<Rightarrow> complex" where
    "g analytic_on S"
    "\<And>z. z \<in> K \<Longrightarrow> g z \<noteq> 0"
    "\<And>z. z \<in> S \<Longrightarrow> f z = g z * (\<Prod>k<n. (z - \<alpha> k))"
    "\<alpha> ` {..<n} \<subseteq> K"
proof -
  have \<open>finite {z \<in> K. f z = 0}\<close> using assms by (rule analytic_compact_finite_zeros)
  moreover have \<open>finite F \<Longrightarrow> analytic_factor_p F\<close> for F
    by (induct rule: finite_induct; rule analytic_factorization_E analytic_factorization_I)
  ultimately have "analytic_factor_p {z \<in> K. f z = 0}" by auto
  hence "analytic_factor_p' f S K" unfolding analytic_factor_p_def using assms by auto
  thus ?thesis unfolding analytic_factor_p'_def using assms that by metis
qed

subsection \<open>Schwarz theorem in complex analysis\<close>

lemma Schwarz_Lemma1:
  fixes f :: "complex \<Rightarrow> complex"
    and \<xi> :: "complex"
  assumes "f holomorphic_on ball 0 1"
    and "f 0 = 0"
    and "\<And>z. \<parallel>z\<parallel> < 1 \<Longrightarrow> \<parallel>f z\<parallel> \<le> 1"
    and "\<parallel>\<xi>\<parallel> < 1"
  shows "\<parallel>f \<xi>\<parallel> \<le> \<parallel>\<xi>\<parallel>"
proof (cases "f constant_on ball 0 1")
  assume "f constant_on ball 0 1"
  thus ?thesis unfolding constant_on_def
    using assms by auto
next
  assume nc: "\<not>f constant_on ball 0 1"
  have "\<And>z. \<parallel>z\<parallel> < 1 \<Longrightarrow> \<parallel>f z\<parallel> < 1"
  proof -
    fix z :: complex assume *: "\<parallel>z\<parallel> < 1"
    have "\<parallel>f z\<parallel> \<noteq> 1"
    proof
      assume "\<parallel>f z\<parallel> = 1"
      hence "\<And>w. w \<in> ball 0 1 \<Longrightarrow> \<parallel>f w\<parallel> \<le> \<parallel>f z\<parallel>"
        using assms(3) by auto
      hence "f constant_on ball 0 1"
        by (intro maximum_modulus_principle [where U = "ball 0 1" and \<xi> = z])
           (use * assms(1) in auto)
      thus False using nc by blast
    qed
    with assms(3) [OF *] show "\<parallel>f z\<parallel> < 1" by auto
  qed
  thus "\<parallel>f \<xi>\<parallel> \<le> \<parallel>\<xi>\<parallel>" by (intro Schwarz_Lemma(1), use assms in auto)
qed

theorem Schwarz_Lemma2:
  fixes f :: "complex \<Rightarrow> complex"
    and \<xi> :: "complex"
  assumes holf: "f holomorphic_on ball 0 R"
    and hR: "0 < R" and nz: "f 0 = 0"
    and bn: "\<And>z. \<parallel>z\<parallel> < R \<Longrightarrow> \<parallel>f z\<parallel> \<le> 1"
    and \<xi>R: "\<parallel>\<xi>\<parallel> < R"
  shows "\<parallel>f \<xi>\<parallel> \<le> \<parallel>\<xi>\<parallel> / R"
proof -
  define \<phi> where "\<phi> z \<equiv> f (R * z)" for z :: complex
  have "\<parallel>\<xi> / R\<parallel> < 1" using \<xi>R hR by (subst nonzero_norm_divide, auto)
  moreover have "f holomorphic_on (*) (R :: complex) ` ball 0 1"
    by (rule holomorphic_on_subset, rule holf)
       (use hR in \<open>auto simp: norm_mult\<close>)
  hence "(f \<circ> (\<lambda>z. R * z)) holomorphic_on ball 0 1"
    by (auto intro: holomorphic_on_compose)
  moreover have "\<phi> 0 = 0" unfolding \<phi>_def using nz by auto
  moreover have "\<And>z. \<parallel>z\<parallel> < 1 \<Longrightarrow> \<parallel>\<phi> z\<parallel> \<le> 1"
  proof -
    fix z :: complex assume *: "\<parallel>z\<parallel> < 1"
    have "\<parallel>R*z\<parallel> < R" using hR * by (fold scaleR_conv_of_real) auto
    thus "\<parallel>\<phi> z\<parallel> \<le> 1" unfolding \<phi>_def using bn by auto
  qed
  ultimately have "\<parallel>\<phi> (\<xi> / R)\<parallel> \<le> \<parallel>\<xi> / R\<parallel>"
    unfolding comp_def by (fold \<phi>_def, intro Schwarz_Lemma1)
  thus ?thesis unfolding \<phi>_def using hR by (subst (asm) nonzero_norm_divide, auto)
qed

subsection \<open>Borel-Carathedory theorem\<close>

text \<open>Borel-Carathedory theorem, from book
  \<open>Theorem 5.5, The Theory of Functions, E. C. Titchmarsh\<close>\<close>

lemma Borel_Caratheodory1:
  assumes hr: "0 < R" "0 < r" "r < R"
    and f0: "f 0 = 0"
    and hf: "\<And>z. \<parallel>z\<parallel> < R \<Longrightarrow> Re (f z) \<le> A"
    and holf: "f holomorphic_on (ball 0 R)"
    and zr: "\<parallel>z\<parallel> \<le> r"
  shows "\<parallel>f z\<parallel> \<le> 2*r/(R-r) * A"
proof -
  have A_ge_0: "A \<ge> 0"
  using f0 hf by (metis hr(1) norm_zero zero_complex.simps(1))
  then consider "A = 0" | "A > 0" by linarith
  thus "\<parallel>f z\<parallel> \<le> 2 * r/(R-r) * A"
  proof (cases)
    assume *: "A = 0"
    have 1: "\<And>w. w \<in> ball 0 R \<Longrightarrow> \<parallel>exp (f w)\<parallel> \<le> \<parallel>exp (f 0)\<parallel>" using hf f0 * by auto
    have 2: "exp \<circ> f constant_on (ball 0 R)"
      by (rule maximum_modulus_principle [where f = "exp \<circ> f" and U = "ball 0 R"])
          (use 1 hr(1) in \<open>auto intro: holomorphic_on_compose holf holomorphic_on_exp\<close>)
    have "f constant_on (ball 0 R)"
    proof (rule classical)
      assume *: "\<not> f constant_on ball 0 R"
      have "open (f ` (ball 0 R))"
        by (rule open_mapping_thm [where S = "ball 0 R"], use holf * in auto)
      then obtain e where "e > 0" and "cball 0 e \<subseteq> f ` (ball 0 R)"
        by (metis hr(1) f0 centre_in_ball imageI open_contains_cball)
      then obtain w
        where hw: "w \<in> ball 0 R" "f w = e"
        by (metis abs_of_nonneg imageE less_eq_real_def mem_cball_0 norm_of_real subset_eq)
      have "exp e = exp (f w)"
        using hw(2) by (fold exp_of_real) auto
      also have "\<dots> = exp (f 0)"
        using hw(1) 2 hr(1) unfolding constant_on_def comp_def by auto
      also have "\<dots> = exp (0 :: real)" by (subst f0) auto
      finally have "e = 0" by auto
      with \<open>e > 0\<close> show ?thesis by blast
    qed
    hence "f z = 0" using f0 hr zr unfolding constant_on_def by auto
    hence "\<parallel>f z\<parallel> = 0" by auto
    also have "\<dots> \<le> 2 * r/(R-r) * A" using hr \<open>A \<ge> 0\<close> by auto
    finally show ?thesis .
  next
    assume A_gt_0: "A > 0"
    define \<phi> where "\<phi> z \<equiv> (f z)/(2*A - f z)" for z :: complex
    have \<phi>_bound: "\<parallel>\<phi> z\<parallel> \<le> 1" if *: "\<parallel>z\<parallel> < R" for z
    proof -
      define u v where "u \<equiv> Re (f z)" and "v \<equiv> Im (f z)"
      hence "u \<le> A" unfolding u_def using hf * by blast
      hence "u\<^sup>2 \<le> (2*A-u)\<^sup>2" using A_ge_0 by (simp add: sqrt_ge_absD)
      hence "u\<^sup>2 + v\<^sup>2 \<le> (2*A-u)\<^sup>2 + (-v)\<^sup>2" by auto
      moreover have "2*A - f z = Complex (2*A-u) (-v)" by (simp add: complex_eq_iff u_def v_def)
      hence "\<parallel>f z\<parallel>\<^sup>2 = u\<^sup>2 + v\<^sup>2"
            "\<parallel>2*A - f z\<parallel>\<^sup>2 = (2*A-u)\<^sup>2 + (-v)\<^sup>2"
      unfolding u_def v_def using cmod_power2 complex.sel by presburger+
      ultimately have "\<parallel>f z\<parallel>\<^sup>2 \<le> \<parallel>2*A - f z\<parallel>\<^sup>2" by auto
      hence "\<parallel>f z\<parallel> \<le> \<parallel>2*A - f z\<parallel>" by auto
      thus ?thesis unfolding \<phi>_def by (subst norm_divide) (simp add: divide_le_eq_1)
    qed
    moreover have nz: "\<And>z :: complex. z \<in> ball 0 R \<Longrightarrow> 2*A - f z \<noteq> 0"
    proof
      fix z :: complex
      assume *: "z \<in> ball 0 R"
        and eq: "2*A - f z = 0"
      hence "Re (f z) \<le> A" using hf by auto
      moreover have "Re (f z) = 2*A"
        by (metis eq Re_complex_of_real right_minus_eq)
      ultimately show False using A_gt_0 by auto
    qed
    ultimately have "\<phi> holomorphic_on ball 0 R"
      unfolding \<phi>_def comp_def by (intro holomorphic_intros holf)
    moreover have "\<phi> 0 = 0" unfolding \<phi>_def using f0 by auto
    ultimately have *: "\<parallel>\<phi> z\<parallel> \<le> \<parallel>z\<parallel> / R"
      using hr(1) \<phi>_bound zr hr Schwarz_Lemma2 by auto
    also have "... < 1" using zr hr by auto
    finally have h\<phi>: "\<parallel>\<phi> z\<parallel> \<le> r / R" "\<parallel>\<phi> z\<parallel> < 1" "1 + \<phi> z \<noteq> 0"
    proof (safe)
      show "\<parallel>\<phi> z\<parallel> \<le> r / R" using * zr hr(1)
        by (metis divide_le_cancel dual_order.trans nle_le)
    next
      assume "1 + \<phi> z = 0"
      hence "\<phi> z = -1" using add_eq_0_iff by blast
      thus "\<parallel>\<phi> z\<parallel> < 1 \<Longrightarrow> False" by auto
    qed
    have "2*A - f z \<noteq> 0" using nz hr(3) zr by auto
    hence "f z = 2*A*\<phi> z / (1 + \<phi> z)"
      using h\<phi>(3) unfolding \<phi>_def by (auto simp add: field_simps)
    hence "\<parallel>f z\<parallel> = 2*A*\<parallel>\<phi> z\<parallel> / \<parallel>1 + \<phi> z\<parallel>"
      by (auto simp add: norm_divide norm_mult A_ge_0)
    also have "\<dots> \<le> 2*A*(\<parallel>\<phi> z\<parallel> / (1 - \<parallel>\<phi> z\<parallel>))"
    proof -
      have "\<parallel>1 + \<phi> z\<parallel> \<ge> 1 - \<parallel>\<phi> z\<parallel>"
        by (metis norm_diff_ineq norm_one)
      thus ?thesis
        by (simp, rule divide_left_mono, use A_ge_0 in auto)
           (intro mult_pos_pos, use h\<phi>(2) in auto)
    qed
    also have "\<dots> \<le> 2*A*((r/R) / (1 - r/R))"
    proof -
      have *: "a / (1 - a) \<le> b / (1 - b)"
        if "a < 1" "b < 1" "a \<le> b" for a b :: real
      using that by (auto simp add: field_simps)
      have "\<parallel>\<phi> z\<parallel> / (1 - \<parallel>\<phi> z\<parallel>) \<le> (r/R) / (1 - r/R)"
        by (rule *; (intro h\<phi>)?) (use hr in auto)
      thus ?thesis by (rule mult_left_mono, use A_ge_0 in auto)
    qed
    also have "\<dots> = 2*r/(R-r) * A" using hr(1) by (auto simp add: field_simps)
    finally show ?thesis .
  qed
qed

lemma Borel_Caratheodory2:
  assumes hr: "0 < R" "0 < r" "r < R"
    and hf: "\<And>z. \<parallel>z\<parallel> < R \<Longrightarrow> Re (f z - f 0) \<le> A"
    and holf: "f holomorphic_on (ball 0 R)"
    and zr: "\<parallel>z\<parallel> \<le> r"
  shows "\<parallel>f z - f 0\<parallel> \<le> 2*r/(R-r) * A"
proof -
  define g where "g z \<equiv> f z - f 0" for z
  show ?thesis
    by (fold g_def, rule Borel_Caratheodory1)
       (unfold g_def, insert assms, auto intro: holomorphic_intros)
qed

theorem Borel_Caratheodory3:
  assumes hr: "0 < R" "0 < r" "r < R"
    and hf: "\<And>w. w \<in> ball s R \<Longrightarrow> Re (f w - f s) \<le> A"
    and holf: "f holomorphic_on (ball s R)"
    and zr: "z \<in> ball s r"
  shows "\<parallel>f z - f s\<parallel> \<le> 2*r/(R-r) * A"
proof -
  define g where "g w \<equiv> f (s + w)" for w
  have "\<And>w. \<parallel>w\<parallel> < R \<Longrightarrow> Re (f (s + w) - f s) \<le> A"
    by (intro hf) (auto simp add: dist_complex_def)
  hence "\<parallel>g (z - s) - g 0\<parallel> \<le> 2*r/(R-r) * A"
    by (intro Borel_Caratheodory2, unfold g_def, insert assms)
       (auto intro: holomorphic_intros simp add: dist_complex_def norm_minus_commute)
  thus ?thesis unfolding g_def by auto
qed

subsection \<open>Lemma 3.9\<close>

text\<open>These lemmas is referred to the following material: Theorem 3.9,
  \<open>The Theory of the Riemann Zeta-Function, E. C. Titchmarsh, D. R. Heath-Brown\<close>.\<close>

lemma lemma_3_9_beta1:
  fixes f M r s\<^sub>0
  assumes zl: "0 < r" "0 \<le> M"
    and hf: "f holomorphic_on ball 0 r"
    and ne: "\<And>z. z \<in> ball 0 r \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> ball 0 r \<Longrightarrow> \<parallel>f z / f 0\<parallel> \<le> exp M"
  shows "\<parallel>logderiv f 0\<parallel> \<le> 4 * M / r"
    and "\<forall>s\<in>cball 0 (r / 4). \<parallel>logderiv f s\<parallel> \<le> 8 * M / r" 
proof (goal_cases)
  obtain g
  where holg: "g holomorphic_on ball 0 r"
    and exp_g: "\<And>x. x \<in> ball 0 r \<Longrightarrow> exp (g x) = f x"
    by (rule holomorphic_logarithm_exists [of "ball 0 r" f 0])
       (use zl(1) ne hf in auto)
  have f0: "exp (g 0) = f 0" using exp_g zl(1) by auto
  have "Re (g z - g 0) \<le> M" if *: "\<parallel>z\<parallel> < r" for z
  proof -
    have "exp (Re (g z - g 0)) = \<parallel>exp (g z - g 0)\<parallel>"
      by (rule norm_exp_eq_Re [symmetric])
    also have "\<dots> = \<parallel>f z / f 0\<parallel>"
      by (subst exp_diff, subst f0, subst exp_g)
         (use * in auto)
    also have "\<dots> \<le> exp M" by (rule bn) (use * in auto)
    finally show ?thesis by auto
  qed
  hence "\<parallel>g z - g 0\<parallel> \<le> 2 * (r / 2) / (r - r / 2) * M"
    if *: "\<parallel>z\<parallel> \<le> r / 2" for z
    by (intro Borel_Caratheodory2 [where f = g])
       (use zl(1) holg * in auto)
  also have "\<dots> = 2 * M" using zl(1) by auto
  finally have hg: "\<And>z. \<parallel>z\<parallel> \<le> r / 2 \<Longrightarrow> \<parallel>g z - g 0\<parallel> \<le> 2 * M" .
  have result: "\<parallel>logderiv f s\<parallel> \<le> 2 * M / r'"
    when "cball s r' \<subseteq> cball 0 (r / 2)" "0 < r'" "\<parallel>s\<parallel> < r / 2" for s r'
  proof -
    have contain: "\<And>z. \<parallel>s - z\<parallel> \<le> r' \<Longrightarrow> \<parallel>z\<parallel> \<le> r / 2"
      using that by (auto simp add: cball_def subset_eq dist_complex_def)
    have contain': "\<parallel>z\<parallel> < r" when "\<parallel>s - z\<parallel> \<le> r'" for z
      using zl(1) contain [of z] that by auto
    have s_in_ball: "s \<in> ball 0 r" using that(3) zl(1) by auto
    have "deriv f s = deriv (\<lambda>x. exp (g x)) s"
      by (rule deriv_cong_ev, subst eventually_nhds)
         (rule exI [where x = "ball 0 (r / 2)"], use exp_g zl(1) that(3) in auto)
    also have "\<dots> = exp (g s) * deriv g s"
      by (intro DERIV_fun_exp [THEN DERIV_imp_deriv] field_differentiable_derivI)
         (meson holg open_ball s_in_ball holomorphic_on_imp_differentiable_at)
    finally have df: "logderiv f s = deriv g s"
    proof -
      assume "deriv f s = exp (g s) * deriv g s"
      moreover have "f s \<noteq> 0" by (intro ne s_in_ball)
      ultimately show ?thesis
        unfolding logderiv_def using exp_g [OF s_in_ball] by auto
    qed
    have "\<And>z. \<parallel>s - z\<parallel> = r' \<Longrightarrow> \<parallel>g z - g 0\<parallel> \<le> 2 * M"
      using contain by (intro hg) auto
    moreover have "(\<lambda>z. g z - g 0) holomorphic_on cball s r'"
      by (rule holomorphic_on_subset [where s="ball 0 r"], insert holg)
         (auto intro: holomorphic_intros contain' simp add: dist_complex_def)
    moreover hence "continuous_on (cball s r') (\<lambda>z. g z - g 0)"
      by (rule holomorphic_on_imp_continuous_on)
    ultimately have "\<parallel>(deriv ^^ 1) (\<lambda>z. g z - g 0) s\<parallel> \<le> fact 1 * (2 * M) / r' ^ 1"
      using that(2) by (intro Cauchy_inequality) auto
    also have "\<dots> = 2 * M / r'" by auto
    also have "deriv g s = deriv (\<lambda>z. g z - g 0) s"
      by (subst deriv_diff, auto)
         (rule holomorphic_on_imp_differentiable_at, use holg s_in_ball in auto)
    hence "\<parallel>deriv g s\<parallel> = \<parallel>(deriv ^^ 1) (\<lambda>z. g z - g 0) s\<parallel>"
      by (auto simp add: derivative_intros)
    ultimately show ?thesis by (subst df) auto
  qed
  case 1 show ?case using result [of 0 "r / 2"] zl(1) by auto
  case 2 show ?case proof safe
    fix s :: complex assume hs: "s \<in> cball 0 (r / 4)"
    hence "z \<in> cball s (r / 4) \<Longrightarrow> \<parallel>z\<parallel> \<le> r / 2" for z
      using norm_triangle_sub [of "z" "s"]
      by (auto simp add: dist_complex_def norm_minus_commute)
    hence "\<parallel>logderiv f s\<parallel> \<le> 2 * M / (r / 4)"
      by (intro result) (use zl(1) hs in auto)
    also have "\<dots> = 8 * M / r" by auto
    finally show "\<parallel>logderiv f s\<parallel> \<le> 8 * M / r" .
  qed
qed

lemma lemma_3_9_beta1':
  fixes f M r s\<^sub>0
  assumes zl: "0 < r" "0 \<le> M"
    and hf: "f holomorphic_on ball s r"
    and ne: "\<And>z. z \<in> ball s r \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> ball s r \<Longrightarrow> \<parallel>f z / f s\<parallel> \<le> exp M"
    and hs: "z \<in> cball s (r / 4)"
  shows "\<parallel>logderiv f z\<parallel> \<le> 8 * M / r" 
proof -
  define g where "g z \<equiv> f (s + z)" for z
  have "\<forall>z \<in> cball 0 (r / 4). \<parallel>logderiv g z\<parallel> \<le> 8 * M / r"
    by (intro lemma_3_9_beta1 assms, unfold g_def)
       (auto simp add: dist_complex_def intro!: assms holomorphic_on_shift)
  note bspec [OF this, of "z - s"]
  moreover have "f field_differentiable at z"
    by (rule holomorphic_on_imp_differentiable_at [where ?s = "ball s r"])
       (insert hs zl(1), auto intro: hf simp add: dist_complex_def)
  ultimately show ?thesis unfolding g_def using hs
    by (auto simp add: dist_complex_def logderiv_shift)
qed

lemma lemma_3_9_beta2:
  fixes f M r
  assumes zl: "0 < r" "0 \<le> M"
    and af: "f analytic_on cball 0 r"
    and f0: "f 0 \<noteq> 0"
    and rz: "\<And>z. z \<in> cball 0 r \<Longrightarrow> Re z > 0 \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> cball 0 r \<Longrightarrow> \<parallel>f z / f 0\<parallel> \<le> exp M"
    and hg: "\<Gamma> \<subseteq> {z \<in> cball 0 (r / 2). f z = 0 \<and> Re z \<le> 0}"
  shows "- Re (logderiv f 0) \<le> 8 * M / r + Re (\<Sum>z\<in>\<Gamma>. 1 / z)"
proof -
  have nz': "f not_zero_on cball 0 (r / 2)"
    unfolding not_zero_on_def using f0 zl(1) by auto
  hence fin_zeros: "finite {z \<in> cball 0 (r / 2). f z = 0}"
    by (intro analytic_compact_finite_zeros [where S = "cball 0 r"])
       (use af zl in auto)
  obtain g n and \<alpha> :: "nat \<Rightarrow> complex"
  where ag: "g analytic_on cball 0 r"
    and ng: "\<And>z. z \<in> cball 0 (r / 2) \<Longrightarrow> g z \<noteq> 0"
    and fac: "\<And>z. z \<in> cball 0 r \<Longrightarrow> f z = g z * (\<Prod>k<n. (z - \<alpha> k))"
    and Im\<alpha>: "\<alpha> ` {..<n} \<subseteq> cball 0 (r / 2)"
    by (rule analytic_factorization [
      where K = "cball 0 (r / 2)"
        and S = "cball 0 r" and f = f])
       (use zl(1) af nz' in auto)
  have g0: "\<parallel>g 0\<parallel> \<noteq> 0" using ng zl(1) by auto
  hence "g holomorphic_on cball 0 r"
        "(\<lambda>z. g z / g 0) holomorphic_on cball 0 r"
    using ag by (auto simp add: analytic_intros intro: analytic_imp_holomorphic)
  hence holg:
      "g holomorphic_on ball 0 r"
      "(\<lambda>z. g z / g 0) holomorphic_on ball 0 r"
      "continuous_on (cball 0 r) (\<lambda>z. g z / g 0)"
    by (auto intro!: holomorphic_on_imp_continuous_on
                     holomorphic_on_subset [where t = "ball 0 r"])
  have nz_\<alpha>: "\<And>k. k < n \<Longrightarrow> \<alpha> k \<noteq> 0" using zl(1) f0 fac by auto
  have "\<parallel>g z / g 0\<parallel> \<le> exp M" if *: "z \<in> sphere 0 r" for z
  proof -
    let ?p = "\<parallel>(\<Prod>k<n. (z - \<alpha> k)) / (\<Prod>k<n. (0 - \<alpha> k))\<parallel>"
    have 1: "\<parallel>f z / f 0\<parallel> \<le> exp M" using bn * by auto
    have 2: "\<parallel>f z / f 0\<parallel> = \<parallel>g z / g 0\<parallel> * ?p"
      by (subst norm_mult [symmetric], subst (1 2) fac)
         (use that zl(1) in auto)
    have "?p = (\<Prod>k<n. (\<parallel>z - \<alpha> k\<parallel> / \<parallel>0 - \<alpha> k\<parallel>))"
      by (auto simp add: prod_norm [symmetric] norm_divide prod_dividef)
    also have "\<parallel>z - \<alpha> k\<parallel> \<ge> \<parallel>0 - \<alpha> k\<parallel>" if "k < n" for k
    proof (rule ccontr)
      assume **: "\<not> \<parallel>z - \<alpha> k\<parallel> \<ge> \<parallel>0 - \<alpha> k\<parallel>"
      have "r = \<parallel>z\<parallel>" using * by auto
      also have "... \<le> \<parallel>0 - \<alpha> k\<parallel> + \<parallel>z - \<alpha> k\<parallel>" by (simp add: norm_triangle_sub)
      also have "... < 2 * \<parallel>\<alpha> k\<parallel>" using ** by auto
      also have "\<alpha> k \<in> cball 0 (r / 2)" using Im\<alpha> that by blast
      hence "2 * \<parallel>\<alpha> k\<parallel> \<le> r" by auto
      finally show False by linarith
    qed
    hence "\<And>k. k < n \<Longrightarrow> \<parallel>z - \<alpha> k\<parallel> / \<parallel>0 - \<alpha> k\<parallel> \<ge> 1"
      using nz_\<alpha> by (subst le_divide_eq_1_pos) auto
    hence "(\<Prod>k<n. (\<parallel>z - \<alpha> k\<parallel> / \<parallel>0 - \<alpha> k\<parallel>)) \<ge> 1" by (rule prod_ge_1) simp
    finally have 3: "?p \<ge> 1" .
    have rule1: "b = a * c \<Longrightarrow> a \<ge> 0 \<Longrightarrow> c \<ge> 1 \<Longrightarrow> a \<le> b" for a b c :: real
      by (metis landau_omega.R_mult_left_mono more_arith_simps(6))
    have "\<parallel>g z / g 0\<parallel> \<le> \<parallel>f z / f 0\<parallel>"
      by (rule rule1) (rule 2 3 norm_ge_zero)+
    thus ?thesis using 1 by linarith
  qed
  hence "\<And>z. z \<in> cball 0 r \<Longrightarrow> \<parallel>g z / g 0\<parallel> \<le> exp M"
    using holg
    by (auto intro: maximum_modulus_frontier
       [where f = "\<lambda>z. g z / g 0" and S = "cball 0 r"])
  hence bn': "\<And>z. z \<in> cball 0 (r / 2) \<Longrightarrow> \<parallel>g z / g 0\<parallel> \<le> exp M" using zl(1) by auto
  have ag': "g analytic_on cball 0 (r / 2)"
    by (rule analytic_on_subset [where S = "cball 0 r"])
       (use ag zl(1) in auto)
  have "\<parallel>logderiv g 0\<parallel> \<le> 4 * M / (r / 2)"
    by (rule lemma_3_9_beta1(1) [where f = g])
       (use zl ng bn' holg in auto)
  also have "\<dots> = 8 * M / r" by auto
  finally have bn_g: "\<parallel>logderiv g 0\<parallel> \<le> 8 * M / r" unfolding logderiv_def by auto
  let ?P = "\<lambda>w. \<Prod>k<n. (w - \<alpha> k)"
  let ?S' = "\<Sum>k<n. logderiv (\<lambda>z. z - \<alpha> k) 0"
  let ?S = "\<Sum>k<n. - (1 / \<alpha> k)"
  have "g field_differentiable at 0" using holg zl(1)
    by (auto intro!: holomorphic_on_imp_differentiable_at)
  hence ld_g: "g log_differentiable 0" unfolding log_differentiable_def using g0 by auto
  have "logderiv ?P 0 = ?S'" and ld_P: "?P log_differentiable 0"
    by (auto intro!: logderiv_linear nz_\<alpha> logderiv_prod)
  note this(1)
  also have "?S' = ?S"
    by (rule sum.cong)
       (use nz_\<alpha> in "auto cong: logderiv_linear(1)")
  finally have cd_P: "logderiv ?P 0 = ?S" .
  have "logderiv f 0 = logderiv (\<lambda>z. g z * ?P z) 0"
    by (rule logderiv_cong_ev, subst eventually_nhds)
       (intro exI [where x = "ball 0 r"], use fac zl(1) in auto)
  also have "\<dots> = logderiv g 0 + logderiv ?P 0"
    by (subst logderiv_mult) (use ld_g ld_P in auto)
  also have "\<dots> = logderiv g 0 + ?S" using cd_P by auto
  finally have "Re (logderiv f 0) = Re (logderiv g 0) + Re ?S" by simp
  moreover have "- Re (\<Sum>z\<in>\<Gamma>. 1 / z) \<le> Re ?S"
  proof -
    have "- Re (\<Sum>z\<in>\<Gamma>. 1 / z) = (\<Sum>z\<in>\<Gamma>. Re (- (1 / z)))" by (auto simp add: sum_negf)
    also have "\<dots> \<le> (\<Sum>k<n. Re (- (1 / \<alpha> k)))"
    proof (rule sum_le_included)
      show "\<forall>z\<in>\<Gamma>. \<exists>k\<in>{..<n}. \<alpha> k = z \<and> Re (- (1 / z)) \<le> Re (- (1 / \<alpha> k))"
           (is "Ball _ ?P")
      proof
        fix z assume hz: "z \<in> \<Gamma>"
        have "\<exists>k\<in>{..<n}. \<alpha> k = z"
        proof (rule ccontr)
          assume ne_\<alpha>: "\<not> (\<exists>k\<in>{..<n}. \<alpha> k = z)"
          have z_in: "z \<in> cball 0 (r / 2)" "z \<in> cball 0 r" using hg hz zl(1) by auto
          hence "g z \<noteq> 0" using ng by auto
          moreover have "(\<Prod>k<n. (z - \<alpha> k)) \<noteq> 0" using ne_\<alpha> hz by auto
          ultimately have "f z \<noteq> 0" using fac z_in by auto
          moreover have "f z = 0" using hz hg by auto
          ultimately show False by auto
        qed
        thus "?P z" by auto
      qed
      show "\<forall>k\<in>{..<n}. 0 \<le> Re (- (1 / \<alpha> k))" (is "Ball _ ?P")
      proof
        fix k assume *: "k\<in>{..<n}"
        have 1: "\<alpha> k \<in> cball 0 r" using Im\<alpha> zl(1) * by auto
        hence "(\<Prod>j<n. (\<alpha> k - \<alpha> j)) = 0"
          by (subst prod_zero_iff) (use * in auto)
        with 1 have "f (\<alpha> k) = 0" by (subst fac) auto
        hence "Re (\<alpha> k) \<le> 0" using "1" rz f0 by fastforce
        hence "Re (1 * cnj (\<alpha> k)) \<le> 0" by auto
        thus "?P k" using Re_complex_div_le_0 by auto
      qed
      show "finite {..<n}" by auto
      have "\<Gamma> \<subseteq> {z \<in> cball 0 (r / 2). f z = 0}" using hg by auto
      thus "finite \<Gamma>" using fin_zeros by (rule finite_subset)
    qed
    also have "\<dots> = Re ?S" by auto
    finally show ?thesis .
  qed
  ultimately have "- Re (logderiv f 0) - Re (\<Sum>z\<in>\<Gamma>. 1 / z) \<le> Re (- logderiv g 0)" by auto
  also have "\<dots> \<le> \<parallel>- logderiv g 0\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> \<le> 8 * M / r" by simp (rule bn_g)
  finally show ?thesis by auto
qed

theorem lemma_3_9_beta3:
  fixes f M r and s :: complex
  assumes zl: "0 < r" "0 \<le> M"
    and af: "f analytic_on cball s r"
    and f0: "f s \<noteq> 0"
    and rz: "\<And>z. z \<in> cball s r \<Longrightarrow> Re z > Re s \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> cball s r \<Longrightarrow> \<parallel>f z / f s\<parallel> \<le> exp M"
    and hg: "\<Gamma> \<subseteq> {z \<in> cball s (r / 2). f z = 0 \<and> Re z \<le> Re s}"
  shows "- Re (logderiv f s) \<le> 8 * M / r + Re (\<Sum>z\<in>\<Gamma>. 1 / (z - s))"
proof -
  define g where "g \<equiv> f \<circ> (\<lambda>z. s + z)"
  define \<Delta> where "\<Delta> \<equiv> (\<lambda>z. z - s) ` \<Gamma>"
  hence 1: "g analytic_on cball 0 r"
    unfolding g_def using af
    by (intro analytic_on_compose) (auto simp add: analytic_intros)
  moreover have "g 0 \<noteq> 0" unfolding g_def using f0 by auto
  moreover have "(Re z > 0 \<longrightarrow> g z \<noteq> 0) \<and> \<parallel>g z / g 0\<parallel> \<le> exp M"
    if hz: "z \<in> cball 0 r" for z
  proof (intro impI conjI)
    assume hz': "0 < Re z"
    thus "g z \<noteq> 0" unfolding g_def comp_def
      using hz by (intro rz) (auto simp add: dist_complex_def)
  next
    show "\<parallel>g z / g 0\<parallel> \<le> exp M"
      unfolding g_def comp_def using hz
      by (auto simp add: dist_complex_def intro!: bn)
  qed
  moreover have "\<Delta> \<subseteq> {z \<in> cball 0 (r / 2). g z = 0 \<and> Re z \<le> 0}"
  proof safe
    fix z assume "z \<in> \<Delta>"
    hence "s + z \<in> \<Gamma>" unfolding \<Delta>_def by auto
    thus "g z = 0" "Re z \<le> 0" "z \<in> cball 0 (r / 2)"
      unfolding g_def comp_def using hg by (auto simp add: dist_complex_def)
  qed
  ultimately have "- Re (logderiv g 0) \<le> 8 * M / r +  Re (\<Sum>z\<in>\<Delta>. 1 / z)"
    by (intro lemma_3_9_beta2) (use zl in auto)
  also have "\<dots> = 8 * M / r +  Re (\<Sum>z\<in>\<Gamma>. 1 / (z - s))"
    unfolding \<Delta>_def by (subst sum.reindex) (unfold inj_on_def, auto)
  finally show ?thesis
    unfolding g_def comp_def using zl(1)
    by (subst (asm) logderiv_shift)
       (auto intro: analytic_on_imp_differentiable_at [OF af])
qed

unbundle no_pnt_syntax
end