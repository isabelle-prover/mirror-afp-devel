(*
  Theory: PDF_Semantics.thy
  Author: Manuel Eberl

  Defines the expressions of the PDF language and their typing rules and semantics
  as well as a number of standard semantics-related theorems such as substitution.
*)

theory PDF_Semantics
imports PDF_Values Poisson
begin

section {* Built-in Probability Distributions *}

subsection {* Bernoulli *}

definition bernoulli_density :: "real \<Rightarrow> bool \<Rightarrow> ereal" where
  "bernoulli_density p b = (if p \<in> {0..1} then (if b then p else 1 - p) else 0)"

definition bernoulli :: "val \<Rightarrow> val measure" where
  "bernoulli = (\<lambda> RealVal p \<Rightarrow> density (count_space (range BoolVal)) 
                                   (\<lambda>BoolVal b \<Rightarrow> bernoulli_density p b))"

lemma measurable_kernel_space_density:
  assumes "sigma_finite_measure N"
  assumes "space N \<noteq> {}"
  assumes [measurable]: "split f \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> (\<integral>\<^sup>+y. f x y \<partial>N) \<le> 1"
  shows "(\<lambda>x. density N (f x)) \<in> measurable M (kernel_space N)"
proof (rule measurable_kernel_space)
  fix x assume "x \<in> space M"
  with assms show "subprob_space (density N (f x))"
    by (intro subprob_spaceI) (auto simp: emeasure_density_space)
next
  interpret sigma_finite_measure N by fact
  fix X assume X: "X \<in> sets N"
  hence "(\<lambda>x. (\<integral>\<^sup>+y. f x y * indicator X y \<partial>N)) \<in> borel_measurable M" by simp
  moreover from X and assms have 
      "\<And>x. x \<in> space M \<Longrightarrow> emeasure (density N (f x)) X = (\<integral>\<^sup>+y. f x y * indicator X y \<partial>N)"
    by (simp add: emeasure_density)
  ultimately show "(\<lambda>x. emeasure (density N (f x)) X) \<in> borel_measurable M"
    by (simp only: cong: measurable_cong)
qed simp_all

lemma measurable_bernoulli_density[measurable]:
    "split bernoulli_density \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
  unfolding bernoulli_density_def[abs_def] by measurable

lemma measurable_bernoulli[measurable]:
  "bernoulli \<in> measurable (embed_measure lborel RealVal) (kernel_space (count_space (range BoolVal)))"
proof (subst measurable_cong)
  fix p assume "p \<in> space (embed_measure lborel RealVal)"
  thus "bernoulli p = density (count_space (range BoolVal)) 
                           (bernoulli_density (extract_real p) \<circ> extract_bool)"
    by (auto intro!: density_cong AE_I2 simp: bernoulli_def extract_real_def 
          extract_bool_def o_def space_embed_measure)
next
  show "(\<lambda>p. density (count_space (range BoolVal)) 
                 (bernoulli_density (extract_real p) \<circ> extract_bool))
           \<in> measurable (embed_measure lborel RealVal) (kernel_space (count_space (range BoolVal)))"
  proof (rule measurable_kernel_space_density)
    show "(\<lambda>(p, b). (bernoulli_density (extract_real p) \<circ> extract_bool) b)
              \<in> borel_measurable (embed_measure lborel RealVal \<Otimes>\<^sub>M count_space (range BoolVal))"
       unfolding o_def by measurable
  next
    have [simp]: "range BoolVal = {TRUE, FALSE}" by auto
    fix p assume "p \<in> space (embed_measure lborel RealVal)"
    thus "(\<integral>\<^sup>+b. (bernoulli_density (extract_real p) \<circ> extract_bool) b
              \<partial>count_space (range BoolVal)) \<le> 1"
      by (auto simp: o_def nn_integral_count_space_finite max_def bernoulli_density_def 
                     extract_real_def extract_bool_def)
  qed (auto intro!: sigma_finite_measure_count_space_finite)
qed


subsection {* Uniform *}

definition uniform_real_density :: "real \<times> real \<Rightarrow> real \<Rightarrow> ereal" where
  "uniform_real_density \<equiv> \<lambda>(a,b) x. (if a < b \<and> x \<in> {a..b} then inverse (b - a) else 0)"

definition uniform_int_density :: "int \<times> int \<Rightarrow> int \<Rightarrow> ereal" where
  "uniform_int_density \<equiv> \<lambda>(a,b) x. (if x \<in> {a..b} then inverse (b - a + 1) else 0)"

lemma measurable_uniform_density_int[measurable]:
  "(split uniform_int_density)
       \<in> borel_measurable ((count_space UNIV \<Otimes>\<^sub>M count_space UNIV) \<Otimes>\<^sub>M count_space UNIV)"
  by (simp add: pair_measure_countable)

lemma measurable_uniform_density_real[measurable]:
  "(split uniform_real_density) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
proof-
  have "(split uniform_real_density) =
            (\<lambda>x. uniform_real_density (fst (fst x), snd (fst x)) (snd x))"
      by (rule ext) (simp split: prod.split)
  also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
      unfolding uniform_real_density_def
      by (simp only: prod.case) (simp add: borel_prod'[symmetric])
  finally show ?thesis .
qed

definition uniform_int :: "val \<Rightarrow> val measure" where
  "uniform_int = (\<lambda> <| IntVal l, IntVal u |> \<Rightarrow> density (count_space (range IntVal))
                                                    (\<lambda> IntVal x \<Rightarrow> uniform_int_density (l,u) x))"

definition uniform_real :: "val \<Rightarrow> val measure" where
  "uniform_real = (\<lambda> <| RealVal l, RealVal u |> \<Rightarrow> density (embed_measure lborel RealVal)
                                                      (\<lambda> RealVal x \<Rightarrow> uniform_real_density (l,u) x))"

lemma measurable_uniform_int[measurable]:
  "uniform_int \<in> measurable (embed_measure (count_space (range IntVal \<times> range IntVal))
                              (split PairVal)) (kernel_space (count_space (range IntVal)))"
    (is "_ \<in> ?M")
proof (subst measurable_cong)
  fix x assume "x \<in> space (embed_measure (count_space (range IntVal\<times>range IntVal)) (split PairVal))"
  thus "uniform_int x = density (count_space (range IntVal))
                            (\<lambda>y. uniform_int_density (extract_int_pair x) (extract_int y))"
   unfolding uniform_int_def 
   by (auto simp: space_embed_measure extract_int_def extract_int_pair_def 
            intro!: density_cong[OF _ _ AE_I2])
next
  let ?f = "\<lambda>x. density (count_space (range IntVal))
                            (\<lambda>y. uniform_int_density (extract_int_pair x) (extract_int y))"
  show "?f \<in> ?M"
  proof (rule measurable_kernel_space_density)
    fix x assume "x \<in> space (embed_measure (count_space (range IntVal \<times> range IntVal)) (split PairVal))"
    then obtain l u where [simp]: "x = <|IntVal l, IntVal u|>" by (auto simp: space_embed_measure)
    show "(\<integral>\<^sup>+y. uniform_int_density (extract_int_pair x) (extract_int y) 
             \<partial>count_space (range IntVal)) \<le> 1"
    proof (cases "l \<le> u")
      case True
      let ?M = "count_space (range IntVal)"
      have "(\<integral>\<^sup>+y. uniform_int_density (extract_int_pair x) (extract_int y) \<partial>?M) = 
                integral\<^sup>N (count_space UNIV) (uniform_int_density (l, u))"
        by (subst embed_measure_count_space[symmetric], simp, subst embed_measure_eq_distr, simp,
            subst nn_integral_distr)
           (simp_all add: space_embed_measure extract_int_pair_def extract_int_def)
      also have "... = ereal (real_of_nat (card {a. l \<le> a \<and> a \<le> u}) * inverse (real u - real l + 1))"
        by (subst nn_integral_count_space) (simp_all add: uniform_int_density_def)
      also have "{a. l \<le> a \<and> a \<le> u} = {l..u}" by auto
      also have "real_of_nat (card ...) = real u - real l + 1" using True
        by (subst real_of_nat_def[symmetric]) simp
      also have "ereal ((real u - real l + 1) * inverse (real u - real l + 1)) \<le> 1"
        by (simp add: field_simps)
      finally show ?thesis .
    next
      case False
      hence "\<And>y. uniform_int_density (extract_int_pair x) y = 0"
        by (simp add: uniform_int_density_def extract_int_def extract_int_pair_def)
      thus ?thesis by simp
    qed
  qed (simp_all add: sigma_finite_measure_count_space_countable)
qed

lemma density_cong':
  "(\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> density M f = density M g"
  unfolding density_def using assms
  by (auto dest: sets.sets_into_space intro!: nn_integral_cong measure_of_eq)

lemma measurable_uniform_real[measurable]:
  "uniform_real \<in> measurable (embed_measure (embed_measure lborel RealVal \<Otimes>\<^sub>M
                     embed_measure lborel RealVal) (split PairVal)) 
                  (kernel_space (embed_measure lborel RealVal))" (is "_ \<in> measurable ?M ?N")
proof (subst measurable_cong)
  fix x assume "x \<in> space ?M"
  then obtain l u where [simp]: "x = <|RealVal l, RealVal u|>" 
    by (auto simp: space_embed_measure space_pair_measure)
  show "uniform_real x = density (embed_measure lborel RealVal)
                            (\<lambda>y. uniform_real_density (extract_real_pair x) (extract_real y))"
   unfolding uniform_real_def 
   by (auto simp: space_embed_measure extract_real_def extract_real_pair_def space_pair_measure
            intro!: density_cong')
next
  let ?f = "\<lambda>x. density (embed_measure lborel RealVal)
                            (\<lambda>y. uniform_real_density (extract_real_pair x) (extract_real y))"
  show "?f \<in> measurable ?M ?N"
  proof (rule measurable_kernel_space_density)
    fix x assume "x \<in> space ?M"
    then obtain l u where [simp]: "x = <|RealVal l, RealVal u|>" 
      by (auto simp: space_embed_measure space_pair_measure)
    show "(\<integral>\<^sup>+y. uniform_real_density (extract_real_pair x) (extract_real y) 
             \<partial>embed_measure lborel RealVal) \<le> 1"
    proof (cases "l < u")
      case True
      let ?M = "embed_measure lborel RealVal"
      have "(\<integral>\<^sup>+y. uniform_real_density (extract_real_pair x) (extract_real y) \<partial>?M) = 
                integral\<^sup>N lborel (uniform_real_density (l, u))"
        by (subst nn_integral_RealVal, simp)
           (simp_all add: space_embed_measure extract_real_pair_def extract_real_def)
      also have "... = \<integral>\<^sup>+x. indicator {l..u} x * inverse (u - l) \<partial>lborel" using True
          by (intro nn_integral_cong) (simp add: uniform_real_density_def)
      also have "... = (\<integral>\<^sup>+x. indicator {l..u} x \<partial>lborel) * inverse (u - l)" using True
        by (subst nn_integral_multc[symmetric]) 
           (auto intro!: nn_integral_cong split: split_indicator)
      also have "... \<le> 1" using True by (simp add: field_simps)
      finally show ?thesis .
    next
      case False
      hence "\<And>y. uniform_real_density (extract_real_pair x) y = 0"
        by (simp add: uniform_real_density_def extract_real_def extract_real_pair_def)
      thus ?thesis by simp
    qed
  qed (simp_all add: stock_measure.simps[symmetric] del: stock_measure.simps)
qed


subsection {* Gaussian *}

definition gaussian_density :: "real \<times> real \<Rightarrow> real \<Rightarrow> ereal" where
  "gaussian_density \<equiv> 
      \<lambda>(m,s) x. (if s > 0 then exp (-(x - m)\<^sup>2 / (2 * s\<^sup>2)) / sqrt (2 * pi * s\<^sup>2) else 0)"

lemma measurable_gaussian_density[measurable]:
  "split gaussian_density \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
proof-
  have "split gaussian_density = 
              (\<lambda>(x,y). (if snd x > 0 then exp (-((y - fst x)^2) / (2 * snd x^2)) /
                             sqrt (2 * pi * snd x^2) else 0))"
    unfolding gaussian_density_def by (intro ext) (simp split: prod.split)
  also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (simp add: borel_prod'[symmetric])
  finally show ?thesis .
qed

definition gaussian :: "val \<Rightarrow> val measure" where
  "gaussian = (\<lambda> <|RealVal m, RealVal s|> \<Rightarrow> 
                  density (embed_measure lborel RealVal) (\<lambda> RealVal x \<Rightarrow> gaussian_density (m,s) x))"

lemma measurable_gaussian[measurable]:
  "gaussian \<in> measurable (embed_measure (embed_measure lborel RealVal \<Otimes>\<^sub>M embed_measure lborel RealVal)
                              (\<lambda>(a, b). <|a , b|>)) (kernel_space (embed_measure lborel RealVal))"
    (is "gaussian \<in> measurable ?M ?N")
proof (subst measurable_cong)
  fix x assume "x \<in> space ?M"
  then obtain \<mu> \<sigma> where [simp]: "x = <|RealVal \<mu>, RealVal \<sigma>|>"
    by (auto simp: space_embed_measure space_pair_measure)
  show "gaussian x = density (embed_measure lborel RealVal)
                         (\<lambda>y. gaussian_density (extract_real_pair x) (extract_real y))"
    unfolding gaussian_def
    by (auto intro!: density_cong' simp: extract_real_pair_def extract_real_def space_embed_measure)
next
  let ?f = "(\<lambda>w. density (embed_measure lborel RealVal)
                    (\<lambda>y. gaussian_density (extract_real_pair w) (extract_real y)))"
  show "?f \<in> measurable ?M ?N"
  proof (rule measurable_kernel_space_density)
    fix x assume "x \<in> space ?M"
    then obtain \<mu> \<sigma> where [simp]: "x = <|RealVal \<mu>, RealVal \<sigma>|>" 
      by (auto simp: space_embed_measure space_pair_measure)
    show "(\<integral>\<^sup>+y. gaussian_density (extract_real_pair x) (extract_real y) 
             \<partial>embed_measure lborel RealVal) \<le> 1"
    proof (cases "\<sigma> > 0")
      case True
      have "(\<integral>\<^sup>+y. gaussian_density (extract_real_pair x) (extract_real y) 
               \<partial>embed_measure lborel RealVal) =  \<integral>\<^sup>+x. normal_density \<mu> \<sigma> x \<partial>lborel" using True
        by (subst nn_integral_RealVal) (simp, simp add: extract_real_pair_def extract_real_def 
                                                     gaussian_density_def normal_density_def)
      also have "... \<le> 1" 
        using integral_normal_density integrable_normal_density normal_density_nonneg True
        by (subst nn_integral_eq_integral) auto
      finally show ?thesis .
    next
      case False
      hence "\<And>y. gaussian_density (extract_real_pair x) (extract_real y) = 0"
        by (simp add: gaussian_density_def extract_real_pair_def)
      thus ?thesis by simp
    qed
  qed (simp_all add: stock_measure.simps[symmetric] del: stock_measure.simps)
qed


subsection {* Poisson *}

definition poisson_density' :: "real \<Rightarrow> int \<Rightarrow> ereal" where
  "poisson_density' rate k = (if rate \<ge> 0 then poisson_density rate k else 0)"

lemma measurable_poisson_density'[measurable]:
    "split poisson_density' \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
  unfolding poisson_density'_def[abs_def] by simp

definition poisson :: "val \<Rightarrow> val measure" where
  "poisson = (\<lambda> RealVal rate \<Rightarrow> density (count_space (range IntVal)) 
                    (\<lambda> IntVal k \<Rightarrow> poisson_density' rate k))"

lemma measurable_poisson[measurable]:
  "poisson \<in> measurable (embed_measure lborel RealVal) (kernel_space (count_space (range IntVal)))"
      (is "_ \<in> measurable ?M (kernel_space ?N)")
proof (subst measurable_cong)
  let ?f = "\<lambda>rate k. if rate \<ge> 0 then poisson_density rate (extract_int k) else 0"
  fix rate' assume "rate' \<in> space ?M"
  then obtain rate where v: "rate' = RealVal rate" by (auto simp: space_embed_measure)  
  thus "poisson rate' = density (count_space (range IntVal)) (?f (extract_real rate'))"
    by (auto simp: poisson_def poisson_density'_def extract_real_def extract_int_def 
             intro!: density_cong')
next
  let ?f = "\<lambda>rate k. if rate \<ge> 0 then poisson_density rate (extract_int k) else 0"
  show "(\<lambda>rate. density (count_space (range IntVal)) (?f (extract_real rate))) \<in>
            measurable (embed_measure lborel RealVal) (kernel_space (count_space (range IntVal)))"
  proof (rule measurable_kernel_space_density)
    show "(\<lambda>(x, y). ?f (extract_real x) y) \<in> 
              borel_measurable (embed_measure lborel RealVal \<Otimes>\<^sub>M count_space (range IntVal))"
      by (subst measurable_split_conv, rule measurable_If', simp, simp,
          rule measurable_compose[OF measurable_fst],
          simp add: measurable_compose[OF measurable_extract_real])
  next
    fix rate assume "rate \<in> space (embed_measure lborel RealVal)"
    thus "(\<integral>\<^sup>+y. (if 0 \<le> extract_real rate then 
                    poisson_density (extract_real rate) (extract_int y) else 0) 
             \<partial>count_space (range IntVal)) \<le> 1"
      by (cases "extract_real rate \<ge> 0")
         (auto simp: nn_integral_IntVal extract_int_def poisson_density_integral_eq_1)
  qed (auto intro!: sigma_finite_measure_count_space_countable)
qed

section {* Source Language Syntax and Semantics *}

subsection {* Expressions *}

class expr = fixes free_vars :: "'a \<Rightarrow> vname set"

datatype pdf_dist = Bernoulli | UniformInt | UniformReal | Poisson | Gaussian

datatype pdf_operator = Fst | Snd | Add | Mult | Minus | Less | Equals | And | Not | Or | Pow | 
                        Sqrt | Exp | Ln | Fact | Inverse | Pi | Cast pdf_type

datatype expr =
      Var vname 
    | Val val
    | LetVar expr expr ("LET _ IN _" [0, 60] 61)
    | Operator pdf_operator expr (infixl "$$" 999)
    | Pair expr expr  ("<_ ,  _>"  [0, 60] 1000)
    | Random pdf_dist expr
    | IfThenElse expr expr expr ("IF _ THEN _ ELSE _" [0, 0, 70] 71)
    | Fail pdf_type

type_synonym tyenv = "vname \<Rightarrow> pdf_type"

instantiation expr :: expr
begin

primrec free_vars_expr :: "expr \<Rightarrow> vname set" where
  "free_vars_expr (Var x) = {x}"
| "free_vars_expr (Val _) = {}"
| "free_vars_expr (LetVar e1 e2) = free_vars_expr e1 \<union> Suc -` free_vars_expr e2"
| "free_vars_expr (Operator _ e) = free_vars_expr e"
| "free_vars_expr (<e1, e2>) = free_vars_expr e1 \<union> free_vars_expr e2"
| "free_vars_expr (Random _ e) = free_vars_expr e"
| "free_vars_expr (IF b THEN e1 ELSE e2) = 
       free_vars_expr b \<union> free_vars_expr e1 \<union> free_vars_expr e2"
| "free_vars_expr (Fail _) = {}"

instance ..
end

primrec free_vars_expr_code :: "expr \<Rightarrow> vname set" where
  "free_vars_expr_code (Var x) = {x}"
| "free_vars_expr_code (Val _) = {}"
| "free_vars_expr_code (LetVar e1 e2) = 
      free_vars_expr_code e1 \<union> (\<lambda>x. x - 1) ` (free_vars_expr_code e2 - {0})"
| "free_vars_expr_code (Operator _ e) = free_vars_expr_code e"
| "free_vars_expr_code (<e1, e2>) = free_vars_expr_code e1 \<union> free_vars_expr_code e2"
| "free_vars_expr_code (Random _ e) = free_vars_expr_code e"
| "free_vars_expr_code (IF b THEN e1 ELSE e2) = 
       free_vars_expr_code b \<union> free_vars_expr_code e1 \<union> free_vars_expr_code e2"
| "free_vars_expr_code (Fail _) = {}"

lemma free_vars_expr_code[code]:
  "free_vars (e::expr) = free_vars_expr_code e"
proof-
  have "\<And>A. Suc -` A = (\<lambda>x. x - 1) ` (A - {0})" by force
  thus ?thesis by (induction e) simp_all
qed


primrec dist_param_type where
  "dist_param_type Bernoulli = REAL"
| "dist_param_type Poisson = REAL"
| "dist_param_type Gaussian = PRODUCT REAL REAL"
| "dist_param_type UniformInt = PRODUCT INTEG INTEG"
| "dist_param_type UniformReal = PRODUCT REAL REAL"

primrec dist_result_type where
  "dist_result_type Bernoulli = BOOL"
| "dist_result_type UniformInt = INTEG"
| "dist_result_type UniformReal = REAL"
| "dist_result_type Poisson = INTEG"
| "dist_result_type Gaussian = REAL"

primrec dist_measure :: "pdf_dist \<Rightarrow> val \<Rightarrow> val measure" where
  "dist_measure Bernoulli = bernoulli"
| "dist_measure UniformInt = uniform_int"
| "dist_measure UniformReal = uniform_real"
| "dist_measure Poisson = poisson"
| "dist_measure Gaussian = gaussian"

lemma sets_dist_measure[simp]:
  "val_type x = dist_param_type dst \<Longrightarrow> 
       sets (dist_measure dst x) = sets (stock_measure (dist_result_type dst))"
  by (cases dst) (auto simp: bernoulli_def uniform_int_def uniform_real_def 
                             poisson_def gaussian_def split: val.split)
lemma space_dist_measure[simp]:
  "val_type x = dist_param_type dst \<Longrightarrow> 
       space (dist_measure dst x) = type_universe (dist_result_type dst)"
  by (subst space_stock_measure[symmetric]) (intro sets_eq_imp_space_eq sets_dist_measure)

lemma measurable_dist_measure[measurable]:
    "dist_measure d \<in> measurable (stock_measure (dist_param_type d)) 
                                 (kernel_space (stock_measure (dist_result_type d)))"
  by (cases d) simp_all

primrec dist_dens :: "pdf_dist \<Rightarrow> val \<Rightarrow> val \<Rightarrow> ereal" where
  "dist_dens Bernoulli x y = bernoulli_density (extract_real x) (extract_bool y)"
| "dist_dens UniformInt x y = uniform_int_density (extract_int_pair x) (extract_int y)"
| "dist_dens UniformReal x y = uniform_real_density (extract_real_pair x) (extract_real y)"
| "dist_dens Gaussian x y = gaussian_density (extract_real_pair x) (extract_real y)"
| "dist_dens Poisson x y = poisson_density' (extract_real x) (extract_int y)"

lemma measurable_dist_dens[measurable]:
    assumes "f \<in> measurable M (stock_measure (dist_param_type dst))" (is "_ \<in> measurable M ?N")
    assumes "g \<in> measurable M (stock_measure (dist_result_type dst))" (is "_ \<in> measurable M ?R")
    shows "(\<lambda>x. dist_dens dst (f x) (g x)) \<in> borel_measurable M"
  apply (rule measurable_Pair_compose_split[of "dist_dens dst", OF _ assms])
  apply (subst dist_dens_def, cases dst, simp_all)
  done

lemma dist_dens_nonneg:
    assumes "x \<in> type_universe (dist_param_type dst)"
    assumes "y \<in> type_universe (dist_result_type dst)"
    shows "dist_dens dst x y \<ge> 0"
  using assms
  by (subst dist_dens_def, cases dst)
     (auto simp: space_stock_measure[symmetric] space_embed_measure bernoulli_density_def
                 uniform_int_density_def uniform_real_density_def poisson_density'_def 
                 gaussian_density_def extract_int_def extract_real_def extract_bool_def
                  extract_int_pair_def extract_real_pair_def space_pair_measure poisson_density_ge_0 
           simp del: space_stock_measure)

lemma dist_measure_has_density:
  "v \<in> type_universe (dist_param_type dst) \<Longrightarrow> 
       has_density (dist_measure dst v) (stock_measure (dist_result_type dst)) (dist_dens dst v)"
proof (intro has_densityI)
  fix v assume "v \<in> type_universe (dist_param_type dst)"
  thus "dist_measure dst v = density (stock_measure (dist_result_type dst)) (dist_dens dst v)"
    by (cases dst)
       (auto simp: bernoulli_def uniform_int_def uniform_real_def poisson_def gaussian_def
                   space_stock_measure[symmetric] space_embed_measure space_pair_measure
                   extract_int_def extract_real_def extract_bool_def extract_int_pair_def
                   extract_real_pair_def
             simp del: space_stock_measure intro!: density_cong')
qed (insert dist_dens_nonneg, simp_all)

lemma subprob_space_dist_measure: 
    "v \<in> type_universe (dist_param_type dst) \<Longrightarrow> subprob_space (dist_measure dst v)"
  using subprob_space_kernel[OF measurable_dist_measure, of v dst] by simp

lemma dist_measure_has_subprob_density:
  "v \<in> type_universe (dist_param_type dst) \<Longrightarrow> 
       has_subprob_density (dist_measure dst v) (stock_measure (dist_result_type dst)) (dist_dens dst v)"
  unfolding has_subprob_density_def 
  by (auto intro: subprob_space_dist_measure dist_measure_has_density)

lemma dist_dens_integral_space:
  assumes "v \<in> type_universe (dist_param_type dst)"
  shows "(\<integral>\<^sup>+u. dist_dens dst v u \<partial>stock_measure (dist_result_type dst)) \<le> 1"
proof-
  let ?M = "density (stock_measure (dist_result_type dst)) (dist_dens dst v)"
  from assms have "(\<integral>\<^sup>+u. dist_dens dst v u \<partial>stock_measure (dist_result_type dst)) =
                       emeasure ?M (space ?M)"
    by (subst space_density, subst emeasure_density_space)
       (auto intro!: measurable_dist_dens simp:)
  also have "?M = dist_measure dst v" using dist_measure_has_density[OF assms]
    by (auto dest: has_densityD)
  also from assms have "emeasure ... (space ...) \<le> 1"
    by (intro subprob_space.emeasure_space_le_1 subprob_space_dist_measure)
  finally show ?thesis .
qed


subsection {* Typing *}

primrec op_type :: "pdf_operator \<Rightarrow> pdf_type \<Rightarrow> pdf_type option" where
  "op_type Add x = 
      (case x of 
         PRODUCT INTEG INTEG \<Rightarrow> Some INTEG
       | PRODUCT REAL REAL \<Rightarrow> Some REAL
       | _ \<Rightarrow> None)"
| "op_type Mult x = 
      (case x of 
         PRODUCT INTEG INTEG \<Rightarrow> Some INTEG
       | PRODUCT REAL REAL \<Rightarrow> Some REAL
       | _ \<Rightarrow> None)"
| "op_type Minus x = 
      (case x of
         INTEG \<Rightarrow> Some INTEG
       | REAL \<Rightarrow> Some REAL
       | _ \<Rightarrow> None)"
| "op_type Equals x = 
      (case x of 
         PRODUCT t1 t2 \<Rightarrow> if t1 = t2 then Some BOOL else None
       | _ \<Rightarrow> None)"
| "op_type Less x = 
      (case x of
         PRODUCT INTEG INTEG \<Rightarrow> Some BOOL
       | PRODUCT REAL REAL \<Rightarrow> Some BOOL
       | _ \<Rightarrow> None)"
| "op_type (Cast t) x =
      (case (x, t) of
         (BOOL, INTEG) \<Rightarrow> Some INTEG
       | (BOOL, REAL) \<Rightarrow> Some REAL
       | (INTEG, REAL) \<Rightarrow> Some REAL
       | (REAL, INTEG) \<Rightarrow> Some INTEG
       | _ \<Rightarrow> None)"
| "op_type Or x = (case x of PRODUCT BOOL BOOL \<Rightarrow> Some BOOL | _ \<Rightarrow> None)"
| "op_type And x = (case x of PRODUCT BOOL BOOL \<Rightarrow> Some BOOL | _ \<Rightarrow> None)"
| "op_type Not x = (case x of BOOL \<Rightarrow> Some BOOL | _ \<Rightarrow> None)"
| "op_type Inverse x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Fact x = (case x of INTEG \<Rightarrow> Some INTEG | _ \<Rightarrow> None)"
| "op_type Sqrt x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Exp x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Ln x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Pi x = (case x of UNIT \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Pow x = (case x of 
                      PRODUCT REAL INTEG \<Rightarrow> Some REAL
                    | PRODUCT INTEG INTEG \<Rightarrow> Some INTEG
                    | _ \<Rightarrow> None)"
| "op_type Fst x = (case x of PRODUCT t _  \<Rightarrow> Some t | _ \<Rightarrow> None)"
| "op_type Snd x = (case x of PRODUCT _ t  \<Rightarrow> Some t | _ \<Rightarrow> None)"


subsection {* Semantics *}

abbreviation (input) de_bruijn_insert (infixr "\<cdot>" 65) where
  "de_bruijn_insert x f \<equiv> case_nat x f"

inductive expr_typing :: "tyenv \<Rightarrow> expr \<Rightarrow> pdf_type \<Rightarrow> bool" ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50) where
  et_var:  "\<Gamma> \<turnstile> Var x : \<Gamma> x" 
| et_val:  "\<Gamma> \<turnstile> Val v : val_type v" 
| et_let:  "\<Gamma> \<turnstile> e1 : t1 \<Longrightarrow> t1 \<cdot> \<Gamma> \<turnstile> e2 : t2 \<Longrightarrow> \<Gamma> \<turnstile> LetVar e1 e2 : t2"
| et_op:   "\<Gamma> \<turnstile> e : t \<Longrightarrow> op_type oper t = Some t' \<Longrightarrow> \<Gamma> \<turnstile> Operator oper e : t'"
| et_pair: "\<Gamma> \<turnstile> e1 : t1  \<Longrightarrow> \<Gamma> \<turnstile> e2 : t2 \<Longrightarrow>  \<Gamma> \<turnstile> <e1, e2> : PRODUCT t1 t2"
| et_rand: "\<Gamma> \<turnstile> e : dist_param_type dst \<Longrightarrow> \<Gamma> \<turnstile> Random dst e :  dist_result_type dst"
| et_if:   "\<Gamma> \<turnstile> b : BOOL \<Longrightarrow> \<Gamma> \<turnstile> e1 : t \<Longrightarrow> \<Gamma> \<turnstile> e2 : t \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN e1 ELSE e2 : t"
| et_fail: "\<Gamma> \<turnstile> Fail t : t"

lemma expr_typing_cong':
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> (\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma> x = \<Gamma>' x) \<Longrightarrow> \<Gamma>' \<turnstile> e : t"
proof (induction arbitrary: \<Gamma>' rule: expr_typing.induct)
  case (et_let \<Gamma> e1 t1 e2 t2 \<Gamma>')
  have "\<Gamma>' \<turnstile> e1 : t1" using et_let.prems by (intro et_let.IH(1)) auto
  moreover have "case_nat t1 \<Gamma>' \<turnstile> e2 : t2" 
    using et_let.prems by (intro et_let.IH(2)) (auto split: nat.split)
  ultimately show ?case by (auto intro!: expr_typing.intros)
qed (auto intro!: expr_typing.intros)

lemma expr_typing_cong:
  "(\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma> x = \<Gamma>' x) \<Longrightarrow> \<Gamma> \<turnstile> e : t \<longleftrightarrow> \<Gamma>' \<turnstile> e : t"
  by (intro iffI) (simp_all add: expr_typing_cong')

inductive_cases expr_typing_valE[elim]:  "\<Gamma> \<turnstile> Val v : t"
inductive_cases expr_typing_varE[elim]:  "\<Gamma> \<turnstile> Var x : t"
inductive_cases expr_typing_letE[elim]:  "\<Gamma> \<turnstile> LetVar e1 e2 : t"
inductive_cases expr_typing_ifE[elim]:  "\<Gamma> \<turnstile> IfThenElse b e1 e2 : t"
inductive_cases expr_typing_opE[elim]:   "\<Gamma> \<turnstile> Operator oper e : t"
inductive_cases expr_typing_pairE[elim]: "\<Gamma> \<turnstile> <e1, e2> : t"
inductive_cases expr_typing_randE[elim]: "\<Gamma> \<turnstile> Random dst e : t"
inductive_cases expr_typing_failE[elim]: "\<Gamma> \<turnstile> Fail t : t'"

lemma expr_typing_unique:
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile> e : t' \<Longrightarrow> t = t'"
  apply (induction arbitrary: t' rule: expr_typing.induct)
  apply blast
  apply blast
  apply (erule expr_typing_letE, blast)
  apply (erule expr_typing_opE, simp)
  apply (erule expr_typing_pairE, blast)
  apply (erule expr_typing_randE, blast)
  apply (erule expr_typing_ifE, blast)
  apply blast
  done

fun expr_type :: "tyenv \<Rightarrow> expr \<Rightarrow> pdf_type option" where
  "expr_type \<Gamma> (Var x) = Some (\<Gamma> x)"
| "expr_type \<Gamma> (Val v) = Some (val_type v)"
| "expr_type \<Gamma> (LetVar e1 e2) =
       (case expr_type \<Gamma> e1 of
          Some t \<Rightarrow> expr_type (case_nat t \<Gamma>) e2
        | None \<Rightarrow> None)"
| "expr_type \<Gamma> (Operator oper e) = 
       (case expr_type \<Gamma> e of Some t \<Rightarrow> op_type oper t | None \<Rightarrow> None)"
| "expr_type \<Gamma> (<e1, e2>) = 
       (case (expr_type \<Gamma> e1, expr_type \<Gamma> e2) of
          (Some t1, Some t2) \<Rightarrow> Some (PRODUCT t1 t2)
        |  _ \<Rightarrow> None)"
| "expr_type \<Gamma> (Random dst e) = 
       (if expr_type \<Gamma> e = Some (dist_param_type dst) then
           Some (dist_result_type dst)
        else None)"
| "expr_type \<Gamma> (IF b THEN e1 ELSE e2) =
       (if expr_type \<Gamma> b = Some BOOL then
          (case (expr_type \<Gamma> e1, expr_type \<Gamma> e2) of
             (Some t, Some t') \<Rightarrow> if t = t' then Some t else None
           | _ \<Rightarrow> None) else None)"
| "expr_type \<Gamma> (Fail t) = Some t"

lemma expr_type_Some_iff: "expr_type \<Gamma> e = Some t \<longleftrightarrow> \<Gamma> \<turnstile> e : t"
  apply rule
  apply (induction e arbitrary: \<Gamma> t, 
         auto intro!: expr_typing.intros split: option.split_asm split_if_asm) []
  apply (induction rule: expr_typing.induct, auto simp del: fun_upd_apply)
  done

lemmas expr_typing_code[code_unfold] = expr_type_Some_iff[symmetric]


subsubsection {* Countable types *}

primrec countable_type :: "pdf_type \<Rightarrow> bool" where
  "countable_type UNIT = True"
| "countable_type BOOL = True"
| "countable_type INTEG = True"
| "countable_type REAL = False"
| "countable_type (PRODUCT t1 t2) = (countable_type t1 \<and> countable_type t2)"

lemma countable_type_countable[dest]:
    "countable_type t \<Longrightarrow> countable (space (stock_measure t))"
  by (induction t) (auto simp: pair_measure_countable space_embed_measure space_pair_measure)

lemma countable_type_imp_count_space: 
  "countable_type t \<Longrightarrow> stock_measure t = count_space (type_universe t)"
proof (subst space_stock_measure[symmetric], induction t)
  case (PRODUCT t1 t2)
    hence countable: "countable_type t1" "countable_type t2" by simp_all
    note A = PRODUCT.IH(1)[OF countable(1)] and B = PRODUCT.IH(2)[OF countable(2)]
    show "stock_measure (PRODUCT t1 t2) = count_space (space (stock_measure (PRODUCT t1 t2)))"
      apply (subst (1 2) stock_measure.simps)
      apply (subst (1 2) A, subst (1 2) B)
      apply (subst (1 2) pair_measure_countable)
      apply (auto intro: countable_type_countable simp: countable simp del: space_stock_measure) [2]
      apply (subst (1 2) embed_measure_count_space, force intro: injI)
      apply (simp add: count_space_image)
      done
qed simp_all

lemma return_val_countable:
  assumes "countable_type (val_type v)"
  shows "return_val v = density (stock_measure (val_type v)) (indicator {v})" (is "?M1 = ?M2")
proof (rule measure_eqI)
  let ?M3 = "count_space (type_universe (val_type v))"
  fix X assume asm: "X \<in> ?M1"
  with assms have "emeasure ?M2 X = \<integral>\<^sup>+ x. indicator {v} x * indicator X x 
                                              \<partial>count_space (type_universe (val_type v))"
    by (simp add: return_val_def emeasure_density countable_type_imp_count_space)
  also have "(\<lambda>x. indicator {v} x * indicator X x :: ereal) = (\<lambda>x. indicator (X \<inter> {v}) x)"
    by (rule ext, subst Int_commute) (simp split: split_indicator)
  also have "nn_integral ?M3 ... = emeasure ?M3 (X \<inter> {v})"
    by (subst nn_integral_indicator[symmetric]) auto
  also from asm have "... = emeasure ?M1 X" by (auto simp: return_val_def split: split_indicator)
  finally show "emeasure ?M1 X = emeasure ?M2 X" ..
qed (simp add: return_val_def)



subsection {* Semantics *}

definition bool_to_int :: "bool \<Rightarrow> int" where
  "bool_to_int b = (if b then 1 else 0)"

lemma measurable_bool_to_int[measurable]: 
  "bool_to_int \<in> measurable (count_space UNIV) (count_space UNIV)"
  by (rule measurable_count_space)

definition bool_to_real :: "bool \<Rightarrow> real" where
  "bool_to_real b = (if b then 1 else 0)"

lemma measurable_bool_to_real[measurable]: 
  "bool_to_real \<in> borel_measurable (count_space UNIV)"
  by (rule borel_measurable_count_space)

definition safe_ln :: "real \<Rightarrow> real" where
  "safe_ln x = (if x > 0 then ln x else 0)"

lemma safe_ln_gt_0[simp]: "x > 0 \<Longrightarrow> safe_ln x = ln x"
  by (simp add: safe_ln_def)

lemma borel_measurable_safe_ln[measurable]: "safe_ln \<in> borel_measurable borel"
  unfolding safe_ln_def[abs_def] by simp


definition safe_sqrt :: "real \<Rightarrow> real" where
  "safe_sqrt x = (if x \<ge> 0 then sqrt x else 0)"

lemma safe_sqrt_ge_0[simp]: "x \<ge> 0 \<Longrightarrow> safe_sqrt x = sqrt x"
  by (simp add: safe_sqrt_def)

lemma borel_measurable_safe_sqrt[measurable]: "safe_sqrt \<in> borel_measurable borel"
  unfolding safe_sqrt_def[abs_def] by simp


fun op_sem :: "pdf_operator \<Rightarrow> val \<Rightarrow> val" where
  "op_sem Add = lift_RealIntVal2 op+ op+"
| "op_sem Mult = lift_RealIntVal2 op* op*"
| "op_sem Minus = lift_RealIntVal uminus uminus"
| "op_sem Equals = (\<lambda> <|v1, v2|> \<Rightarrow> BoolVal (v1 = v2))"
| "op_sem Less = lift_Comp op< op<"
| "op_sem Or = (\<lambda> <|BoolVal a, BoolVal b|> \<Rightarrow> BoolVal (a \<or> b))"
| "op_sem And = (\<lambda> <|BoolVal a, BoolVal b|> \<Rightarrow> BoolVal (a \<and> b))"
| "op_sem Not = (\<lambda> BoolVal a \<Rightarrow> BoolVal (\<not>a))"
| "op_sem (Cast t) = (case t of
                        INTEG \<Rightarrow> (\<lambda> BoolVal b \<Rightarrow> IntVal (bool_to_int b)
                                  | RealVal r \<Rightarrow> IntVal (floor r))
                      | REAL \<Rightarrow>  (\<lambda> BoolVal b \<Rightarrow> RealVal (bool_to_real b)
                                  | IntVal i \<Rightarrow> RealVal (real i)))"
| "op_sem Inverse = lift_RealVal inverse"
| "op_sem Fact = lift_IntVal fact"
| "op_sem Sqrt = lift_RealVal safe_sqrt"
| "op_sem Exp = lift_RealVal exp"
| "op_sem Ln = lift_RealVal safe_ln"
| "op_sem Pi = (\<lambda>_. RealVal pi)"
| "op_sem Pow = (\<lambda> <|RealVal x, IntVal n|> \<Rightarrow> if n < 0 then RealVal 0 else RealVal (x ^ nat n)
                 | <|IntVal x, IntVal n|> \<Rightarrow> if n < 0 then IntVal 0 else IntVal (x ^ nat n))"
| "op_sem Fst = fst \<circ> extract_pair"
| "op_sem Snd = snd \<circ> extract_pair"


text {* The semantics of expressions. Assumes that the expression given is well-typed. *}

primrec expr_sem :: "state \<Rightarrow> expr \<Rightarrow> val measure" where
  "expr_sem \<sigma> (Var x) = return_val (\<sigma> x)"
| "expr_sem \<sigma> (Val v) = return_val v"
| "expr_sem \<sigma> (LET e1 IN e2) = 
      do {
        v \<leftarrow> expr_sem \<sigma> e1;
        expr_sem (v \<cdot> \<sigma>) e2
      }"
| "expr_sem \<sigma> (oper $$ e) = 
      do {
        x \<leftarrow> expr_sem \<sigma> e; 
        return_val (op_sem oper x)
      }"
| "expr_sem \<sigma> <v, w> = 
      do {
        x \<leftarrow> expr_sem \<sigma> v; 
        y \<leftarrow> expr_sem \<sigma> w; 
        return_val <|x, y|>
      }"
| "expr_sem \<sigma> (IF b THEN e1 ELSE e2) =
     do {
       b' \<leftarrow> expr_sem \<sigma> b;
       if b' = TRUE then expr_sem \<sigma> e1 else expr_sem \<sigma> e2
     }"
| "expr_sem \<sigma> (Random dst e) =
     do {
       x \<leftarrow> expr_sem \<sigma> e; 
       dist_measure dst x
     }"
| "expr_sem \<sigma> (Fail t) = null_measure (stock_measure t)"

lemma expr_sem_pair_vars:
  "expr_sem \<sigma> <Var x, Var y> = return_val <|\<sigma> x, \<sigma> y|>"
proof-
  let ?M = "return (stock_measure (val_type (\<sigma> x))) (\<sigma> x)"
  let ?N = "return (stock_measure (val_type (\<sigma> y))) (\<sigma> y)"
  let ?R = "stock_measure (PRODUCT (val_type (\<sigma> x)) (val_type (\<sigma> y)))"
  have "expr_sem \<sigma> <Var x, Var y> = do {v \<leftarrow> ?M; w \<leftarrow> ?N; return_val <|v, w|>}"
    by (simp add: return_val_def)
  also have "... = do {v \<leftarrow> ?M; w \<leftarrow> ?N; return ?R <|v, w|>}"
    by (intro bind_cong ballI) (simp add: return_val_def)
  also have "... = do {w \<leftarrow> ?N; return ?R <|\<sigma> x, w|>}" unfolding return_val_def
    by (subst bind_return)
       (auto simp: measurable_split_conv[symmetric] 
             intro!: measurable_bind measurable_embed_measure2 inj_PairVal 
                     measurable_compose[OF _ return_measurable])
  also have A: "(\<lambda>w. return ?R <|\<sigma> x, w|>) = return ?R \<circ> split PairVal \<circ> (\<lambda>w. (\<sigma> x, w))"
    by (intro ext) simp
  have \<sigma>x: "\<sigma> x \<in> space (stock_measure (val_type (\<sigma> x)))" by (simp add:)
  have "(\<lambda>w. return ?R <|\<sigma> x, w|>) \<in> measurable (stock_measure (val_type (\<sigma> y))) (kernel_space ?R)"
    by (subst A, intro measurable_comp)
       (rule measurable_Pair1', rule \<sigma>x, rule measurable_embed_measure2, 
        simp_all add: return_measurable inj_PairVal)
  hence "do {w \<leftarrow> ?N; return ?R <|\<sigma> x, w|>} = return ?R <|\<sigma> x, \<sigma> y|>"
    by (subst bind_return) (simp_all add:)
  finally show ?thesis by (simp add: return_val_def)
qed

text {* 
  Well-typed expressions produce a result in the measure space that corresponds to their type
*}

lemma op_sem_val_type:
    "op_type oper (val_type v) = Some t' \<Longrightarrow> val_type (op_sem oper v) = t'"
  by (cases oper) (auto split: val.split split_if_asm pdf_type.split_asm 
                        simp: extract_pair_def lift_RealIntVal_def lift_Comp_def
                              lift_IntVal_def lift_RealVal_def lift_RealIntVal2_def)

lemma sets_expr_sem:
  "\<Gamma> \<turnstile> w : t \<Longrightarrow> (\<forall>x \<in> free_vars w. val_type (\<sigma> x) = \<Gamma> x) \<Longrightarrow> 
       sets (expr_sem \<sigma> w) = sets (stock_measure t)"
proof (induction arbitrary: \<sigma> rule: expr_typing.induct)
  case (et_var \<Gamma> x \<sigma>)
  thus ?case by (simp add: return_val_def)
next
  case (et_val \<Gamma> v \<sigma>)
  thus ?case by (simp add: return_val_def)
next
  case (et_let \<Gamma> e1 t1 e2 t2 \<sigma>)
  hence "sets (expr_sem \<sigma> e1) = sets (stock_measure t1)" by simp
  from sets_eq_imp_space_eq[OF this]
    have A: "space (expr_sem \<sigma> e1) = type_universe t1" by (simp add:)
  hence B: "(SOME x. x \<in> space (expr_sem \<sigma> e1)) \<in> space (expr_sem \<sigma> e1)" (is "?v \<in> _")
    by (rule_tac someI_ex) (simp add: ex_in_conv)   
  with A et_let have "sets (expr_sem (case_nat ?v \<sigma>) e2) = sets (stock_measure t2)"
    by (intro et_let.IH(2)) (auto split: nat.split)
  with B show "sets (expr_sem \<sigma> (LetVar e1 e2)) = sets (stock_measure t2)"
    by (subst expr_sem.simps, subst bind_nonempty) auto
next
  case (et_op \<Gamma> e t oper t' \<sigma>)
  from et_op.IH[of \<sigma>] and et_op.prems 
      have [simp]: "sets (expr_sem \<sigma> e) = sets (stock_measure t)" by simp
  from sets_eq_imp_space_eq[OF this] 
      have [simp]: "space (expr_sem \<sigma> e) = type_universe t" by (simp add:)
  have "(SOME x. x \<in> space (expr_sem \<sigma> e)) \<in> space (expr_sem \<sigma> e)"
     by (rule_tac someI_ex) (simp add: ex_in_conv)
  with et_op show ?case by (simp add: bind_nonempty return_val_def op_sem_val_type)
next
  case (et_pair \<Gamma> e1 t1 e2 t2 \<sigma>)
  hence [simp]: "space (expr_sem \<sigma> e1) = type_universe t1" 
                "space (expr_sem \<sigma> e2) = type_universe t2"
    by (simp_all add: sets_eq_imp_space_eq)
  have "(SOME x. x \<in> space (expr_sem \<sigma> e1)) \<in> space (expr_sem \<sigma> e1)"
       "(SOME x. x \<in> space (expr_sem \<sigma> e2)) \<in> space (expr_sem \<sigma> e2)"
    by (rule_tac someI_ex, simp add: ex_in_conv)+
  with et_pair.hyps show ?case by (simp add: bind_nonempty return_val_def)
next
  case (et_rand \<Gamma> e dst \<sigma>)
  hence "space (expr_sem \<sigma> e) = space (stock_measure (dist_param_type dst))"
    by (intro sets_eq_imp_space_eq)  simp
  hence "space (expr_sem \<sigma> e) \<noteq> {}" by (simp add:)
  with et_rand show ?case by simp
next
  case (et_if \<Gamma> b e1 t e2 \<sigma>)
  have "sets (expr_sem \<sigma> b) = sets (stock_measure BOOL)"
    using et_if.prems by (intro et_if.IH) simp
  from sets_eq_imp_space_eq[OF this] 
    have "space (expr_sem \<sigma> b) \<noteq> {}" by simp
  moreover have "sets (expr_sem \<sigma> e1) = sets (stock_measure t)"
                "sets (expr_sem \<sigma> e2) = sets (stock_measure t)"
    using et_if.prems by (intro et_if.IH, simp)+
  ultimately show ?case by (simp add: bind_nonempty)
qed simp_all

lemma space_expr_sem:
    "\<Gamma> \<turnstile> w : t \<Longrightarrow> (\<forall>x \<in> free_vars w. val_type (\<sigma> x) = \<Gamma> x) 
      \<Longrightarrow> space (expr_sem \<sigma> w) = type_universe t"
  by (subst space_stock_measure[symmetric]) (intro sets_expr_sem sets_eq_imp_space_eq)

lemma measurable_expr_sem_eq:
    "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow> 
       measurable (expr_sem \<sigma> e) = measurable (stock_measure t)"
  by (intro ext measurable_cong_sets sets_expr_sem)
     (auto simp: state_measure_def space_PiM dest: PiE_mem)

lemma measurable_expr_semI:
    "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow> 
       f \<in> measurable (stock_measure t) M \<Longrightarrow> f \<in> measurable (expr_sem \<sigma> e) M"
  by (subst measurable_expr_sem_eq)

lemma expr_sem_eq_on_vars: 
  "(\<And>x. x\<in>free_vars e \<Longrightarrow> \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x) \<Longrightarrow> expr_sem \<sigma>\<^sub>1 e = expr_sem \<sigma>\<^sub>2 e"
proof (induction e arbitrary: \<sigma>\<^sub>1 \<sigma>\<^sub>2)
  case (LetVar e1 e2 \<sigma>1 \<sigma>2)
    from LetVar.prems have A: "expr_sem \<sigma>1 e1 = expr_sem \<sigma>2 e1" by (rule LetVar.IH(1)) simp_all
    from LetVar.prems show ?case 
      by (subst (1 2) expr_sem.simps, subst A) 
         (auto intro!: bind_cong LetVar.IH(2) split: nat.split)
next
  case (Operator oper e \<sigma>1 \<sigma>2)
  from Operator.IH[OF Operator.prems] show ?case by simp
next
  case (Pair e1 e2 \<sigma>1 \<sigma>2)
  from Pair.prems have "expr_sem \<sigma>1 e1 = expr_sem \<sigma>2 e1" by (intro Pair.IH) auto
  moreover from Pair.prems have "expr_sem \<sigma>1 e2 = expr_sem \<sigma>2 e2" by (intro Pair.IH) auto
  ultimately show ?case by simp
next
  case (Random dst e \<sigma>1 \<sigma>2)
  from Random.prems have A: "expr_sem \<sigma>1 e = expr_sem \<sigma>2 e" by (rule Random.IH) simp_all
  show ?case
    by (subst (1 2) expr_sem.simps, subst A) (auto intro!: bind_cong)
next
  case (IfThenElse b e1 e2 \<sigma>1 \<sigma>2)
  have A: "expr_sem \<sigma>1 b = expr_sem \<sigma>2 b" 
          "expr_sem \<sigma>1 e1 = expr_sem \<sigma>2 e1" 
          "expr_sem \<sigma>1 e2 = expr_sem \<sigma>2 e2"
    using IfThenElse.prems by (intro IfThenElse.IH, simp)+
  thus ?case by (simp only: expr_sem.simps A)
qed simp_all


subsection {* Measurability *}

lemma measurable_equals:
    "(\<lambda>(x,y). x = y) \<in> measurable (stock_measure t \<Otimes>\<^sub>M stock_measure t) (count_space UNIV)"
proof (induction t)
  case REAL
    let ?f = "\<lambda>x. (extract_real (fst x) - extract_real (snd x) = 0)"
    show ?case
    proof (subst measurable_cong)
      fix x assume "x \<in> space (stock_measure REAL \<Otimes>\<^sub>M stock_measure REAL)"
      thus "(\<lambda>(x,y). x = y) x = ?f x"
          by (auto simp: space_pair_measure space_embed_measure extract_real_def)
    next
      show "?f \<in> measurable (stock_measure REAL \<Otimes>\<^sub>M stock_measure REAL) (count_space UNIV)"
        by (subst (1 2) stock_measure.simps, rule pred_eq_const1, rule borel_measurable_diff)
           (auto intro: measurable_compose[OF _ measurable_extract_real])
    qed
next
  case (PRODUCT t1 t2)
    let ?g = "\<lambda>(x,y). x = y"
    let ?f = "\<lambda>x. ?g (fst (extract_pair (fst x)), fst (extract_pair (snd x))) \<and>
                  ?g (snd (extract_pair (fst x)), snd (extract_pair (snd x)))"
    show ?case
    proof (subst measurable_cong)
      fix x assume "x \<in> space (stock_measure (PRODUCT t1 t2) \<Otimes>\<^sub>M stock_measure (PRODUCT t1 t2))"
      thus "(\<lambda>(x,y). x = y) x = ?f x"
          by (auto simp: space_pair_measure space_embed_measure extract_pair_def)
    next
      note [measurable] = PRODUCT.IH
      show "Measurable.pred (stock_measure (PRODUCT t1 t2) \<Otimes>\<^sub>M stock_measure (PRODUCT t1 t2)) ?f"
          by simp
    qed
qed (simp_all add: pair_measure_countable)


lemma measurable_op_sem:
  assumes "op_type oper t = Some t'"
  shows "op_sem oper \<in> measurable (stock_measure t) (stock_measure t')"
proof (cases oper)
  case Fst
    with assms show ?thesis by (auto split: pdf_type.split_asm cong: measurable_cong)
next
  case Snd
    with assms show ?thesis by (auto split: pdf_type.split_asm cong: measurable_cong)
next
  case Equals
    with assms obtain t'' where T: "t = PRODUCT t'' t''" "t' = BOOL"
        by (auto split: pdf_type.split_asm split_if_asm)
    let ?f = "BoolVal \<circ> (\<lambda>(x,y). x = y) \<circ> extract_pair"
    show ?thesis
    proof (subst measurable_cong)
      fix x assume "x \<in> space (stock_measure t)"
      with Equals assms show "op_sem oper x = ?f x"
          by (auto simp: space_embed_measure space_pair_measure extract_pair_def 
                   simp del: space_stock_measure
                   split: pdf_type.split_asm)
    next
      show "?f \<in> measurable (stock_measure t) (stock_measure t')"
          by (simp only: T stock_measure.simps)
             (intro measurable_comp, rule measurable_extract_pair, rule measurable_equals, simp)
    qed
next
  case Pow
    show ?thesis
    proof (cases "t' = REAL")
      case True
        with assms Pow have t: "t = PRODUCT REAL INTEG" by (auto split: pdf_type.split_asm)
        let ?f = "RealVal \<circ> (\<lambda>(x,y). if y \<ge> 0 then x ^ nat y else 0) \<circ> 
                      (\<lambda>(x,y). (extract_real x, extract_int y)) \<circ> extract_pair"
        show ?thesis
        proof (subst measurable_cong)
          fix x assume "x \<in> space (stock_measure t)"
          with Pow True show "op_sem oper x = ?f x"
              by (auto split: val.split simp: t extract_real_def extract_int_def extract_pair_def 
                                              space_embed_measure space_pair_measure)
        next
          from True show "?f \<in> measurable (stock_measure t) (stock_measure t')"
            apply (simp only: t stock_measure.simps embed_measure_comp)
            apply (rule measurable_comp[OF measurable_extract_pair])
            apply (rule measurable_comp[of _ _ "borel \<Otimes>\<^sub>M count_space UNIV"])
            apply simp
            apply (rule measurable_comp[OF _ measurable_embed_measure2])
            apply (subst measurable_split_conv, rule measurable_If')
            apply simp
            apply simp
            apply (rule measurable_compose[OF measurable_snd])
            apply simp_all
            done
        qed
    qed (insert assms Pow, auto intro!: measurable_embed_measure1 split: pdf_type.split_asm)
next
  case Less
    with assms have "t = PRODUCT INTEG INTEG \<or> t = PRODUCT REAL REAL" "t' = BOOL"
      by (auto split: pdf_type.split_asm)
    with Less show ?thesis
      apply (elim disjE)
      apply (simp_all only: op_sem.simps stock_measure.simps measurable_lift_Comp_IntVal)
      apply (rule measurable_lift_Comp_RealVal, simp)
      done
qed (insert assms, auto split: pdf_type.split_asm simp: space_embed_measure
                        intro!: measurable_embed_measure1 simp del: space_stock_measure)


definition shift_var_set :: "vname set \<Rightarrow> vname set" where
  "shift_var_set V = insert 0 (Suc ` V)"

lemma shift_var_set_0[simp]: "0 \<in> shift_var_set V"
  by (simp add: shift_var_set_def)

lemma shift_var_set_Suc[simp]: "Suc x \<in> shift_var_set V \<longleftrightarrow> x \<in> V"
  by (auto simp add: shift_var_set_def)

lemma case_nat_update_0[simp]: "(case_nat x \<sigma>)(0 := y) = case_nat y \<sigma>"
  by (intro ext) (simp split: nat.split)

lemma case_nat_delete_var_1[simp]: 
    "case_nat x (case_nat y \<sigma>) \<circ> case_nat 0 (\<lambda>x. Suc (Suc x)) = case_nat x \<sigma>"
  by (intro ext) (simp split: nat.split)

lemma delete_var_1_vimage[simp]:
    "case_nat 0 (\<lambda>x. Suc (Suc x)) -` (shift_var_set (shift_var_set V)) = shift_var_set V"
  by (auto simp: shift_var_set_def split: nat.split_asm)


lemma measurable_case_nat[measurable]:
  assumes "g \<in> measurable R N" "h \<in> measurable R (Pi\<^sub>M V M)"
  shows "(\<lambda>x. case_nat (g x) (h x)) \<in> measurable R (Pi\<^sub>M (shift_var_set V) (case_nat N M))"
proof (rule measurable_Pair_compose_split[OF _ assms])
  have "(\<lambda>(t,f). \<lambda>x\<in>shift_var_set V. case_nat t f x) 
          \<in> measurable (N \<Otimes>\<^sub>M PiM V M) (PiM (shift_var_set V) (case_nat N M))" (is ?P)
    unfolding shift_var_set_def
    by (subst measurable_split_conv, rule measurable_restrict) (auto split: nat.split_asm)
  also have "\<And>x f. f \<in> space (PiM V M) \<Longrightarrow> x \<notin> V \<Longrightarrow> undefined = f x"
    by (rule sym, subst (asm) space_PiM, erule PiE_arb)
  hence "?P \<longleftrightarrow> (\<lambda>(t,f). case_nat t f)
           \<in> measurable (N \<Otimes>\<^sub>M PiM V M) (PiM (shift_var_set V) (case_nat N M))" (is "_ = ?P")
    by (intro measurable_cong ext)
       (auto split: nat.split simp: inj_image_mem_iff space_pair_measure shift_var_set_def)
  finally show ?P .
qed

lemma measurable_case_nat'[measurable]:
  assumes "g \<in> measurable R (stock_measure t)" "h \<in> measurable R (state_measure V \<Gamma>)"
  shows "(\<lambda>x. case_nat (g x) (h x)) \<in> 
           measurable R (state_measure (shift_var_set V) (case_nat t \<Gamma>))"
proof-
  have A: "(\<lambda>x. stock_measure (case_nat t \<Gamma> x)) =
                 case_nat (stock_measure t) (\<lambda>x. stock_measure (\<Gamma> x))"
    by (intro ext) (simp split: nat.split)
  show ?thesis using assms unfolding state_measure_def by (simp add: A)
qed

lemma case_nat_in_state_measure[intro]:
  assumes "x \<in> type_universe t1" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "case_nat x \<sigma> \<in> space (state_measure (shift_var_set V) (case_nat t1 \<Gamma>))"
  apply (rule measurable_space[OF measurable_case_nat'])
  apply (rule measurable_ident_sets[OF refl], rule measurable_const[OF assms(2)])
  apply (simp add: assms(1))
  done

lemma subset_shift_var_set:
    "Suc -` A \<subseteq> V \<Longrightarrow> A \<subseteq> shift_var_set V"
  by (rule subsetI, rename_tac x, case_tac x) (auto simp: shift_var_set_def)

lemma measurable_expr_sem:
  assumes "\<Gamma> \<turnstile> e : t" and "free_vars e \<subseteq> V"
  shows "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> measurable (state_measure V \<Gamma>) 
                                         (kernel_space (stock_measure t))"
using assms
proof (induction arbitrary: V rule: expr_typing.induct)
  case (et_var \<Gamma> x)
  have A: "(\<lambda>\<sigma>. expr_sem \<sigma> (Var x)) = return_val \<circ> (\<lambda>\<sigma>. \<sigma> x)" by (simp add: o_def)
  with et_var show ?case unfolding state_measure_def
    by (subst A) (rule measurable_comp[OF measurable_component_singleton], simp_all)
next
  case (et_val \<Gamma> v)
  thus ?case by (auto intro!: measurable_const subprob_space_return 
                      simp: space_kernel_space return_val_def)
next
  case (et_let \<Gamma> e1 t1 e2 t2 V)
    have A: "(\<lambda>v. stock_measure (case_nat t1 \<Gamma> v)) = 
                 case_nat (stock_measure t1) (\<lambda>v. stock_measure (\<Gamma> v))" 
      by (rule ext) (simp split: nat.split)
    from et_let.prems and et_let.hyps show ?case
      apply (subst expr_sem.simps, intro measurable_bind)
      apply (rule et_let.IH(1), simp)
      apply (rule measurable_compose[OF _ et_let.IH(2)[of "shift_var_set V"]])
      apply (simp_all add: subset_shift_var_set)
      done
next
  case (et_op \<Gamma> e t oper t') 
  thus ?case by (auto intro!: measurable_bind2 measurable_compose[OF _ measurable_return_val] 
                              measurable_op_sem cong: measurable_cong)
next
  case (et_pair t t1 t2 \<Gamma> e1 e2)
  have "inj (\<lambda>(a,b). <|a, b|>)" by (auto intro: injI)
  with et_pair show ?case
      apply (subst expr_sem.simps)
      apply (rule measurable_bind, (auto) [])
      apply (rule measurable_bind[OF measurable_compose[OF measurable_fst]], (auto) [])
      apply (rule measurable_compose[OF _ measurable_return_val], simp)
      done
next
  case (et_rand \<Gamma> e dst V)
  from et_rand.prems and et_rand.hyps show ?case
    by (auto intro!: et_rand.IH measurable_compose[OF measurable_snd]
                     measurable_bind measurable_dist_measure)
next
  case (et_if \<Gamma> b e1 t e2 V)
  let ?M = "\<lambda>e t. (\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> 
                      measurable (state_measure V \<Gamma>) (kernel_space (stock_measure t))"
  from et_if.prems have A[measurable]: "?M b BOOL" "?M e1 t" "?M e2 t" by (intro et_if.IH, simp)+
  show ?case by (subst expr_sem.simps, rule measurable_bind[OF A(1)]) simp_all
next
  case (et_fail \<Gamma> t V)
  show ?case
    by (auto intro!: measurable_kernel_space subprob_spaceI simp:)
qed


subsection {* Randomfree expressions *}

fun randomfree :: "expr \<Rightarrow> bool" where
  "randomfree (Val _) = True"
| "randomfree (Var _) = True"
| "randomfree (Pair e1 e2) = (randomfree e1 \<and> randomfree e2)"
| "randomfree (Operator _ e) = randomfree e"
| "randomfree (LetVar e1 e2) = (randomfree e1 \<and> randomfree e2)"
| "randomfree (IfThenElse b e1 e2) = (randomfree b \<and> randomfree e1 \<and> randomfree e2)"
| "randomfree (Random _ _) = False"
| "randomfree (Fail _) = False"

primrec expr_sem_rf :: "state \<Rightarrow> expr \<Rightarrow> val" where
  "expr_sem_rf _ (Val v) = v"
| "expr_sem_rf \<sigma> (Var x) = \<sigma> x"
| "expr_sem_rf \<sigma> (<e1, e2>) = <|expr_sem_rf \<sigma> e1, expr_sem_rf \<sigma> e2|>"
| "expr_sem_rf \<sigma> (Operator oper e) = op_sem oper (expr_sem_rf \<sigma> e)"
| "expr_sem_rf \<sigma> (LetVar e1 e2) = expr_sem_rf (expr_sem_rf \<sigma> e1 \<cdot> \<sigma>) e2"
| "expr_sem_rf \<sigma> (IfThenElse b e1 e2) = 
      (if expr_sem_rf \<sigma> b = BoolVal True then expr_sem_rf \<sigma> e1 else expr_sem_rf \<sigma> e2)"
| "expr_sem_rf _ (Random _ _) = undefined"
| "expr_sem_rf _ (Fail _) = undefined"


lemma measurable_expr_sem_rf:
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> randomfree e \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow> 
       (\<lambda>\<sigma>. expr_sem_rf \<sigma> e) \<in> measurable (state_measure V \<Gamma>) (stock_measure t)"
proof (induction arbitrary: V rule: expr_typing.induct)
  case (et_val \<Gamma> v V)
  thus ?case by (auto intro!: measurable_const simp:)
next
  case (et_var \<Gamma> x V)
  thus ?case by (auto simp: state_measure_def intro!: measurable_component_singleton)
next
  case (et_pair \<Gamma> e1 t1 e2 t2 V)
  have "inj (\<lambda>(x,y). <|x, y|>)" by (auto intro: injI)
  with et_pair show ?case by simp
next
  case (et_op \<Gamma> e t oper t' V)
  thus ?case by (auto intro!: measurable_compose[OF _ measurable_op_sem])
next
  case (et_let \<Gamma> e1 t1 e2 t2 V)
  hence M1: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e1) \<in> measurable (state_measure V \<Gamma>) (stock_measure t1)"
    and M2: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e2) \<in> measurable (state_measure (shift_var_set V) (case_nat t1 \<Gamma>)) 
                                           (stock_measure t2)"
    using subset_shift_var_set
    by (auto intro!: et_let.IH(1)[of V] et_let.IH(2)[of "shift_var_set V"])
  have "(\<lambda>\<sigma>. expr_sem_rf \<sigma> (LetVar e1 e2)) = 
            (\<lambda>\<sigma>. expr_sem_rf \<sigma> e2) \<circ> (\<lambda>(\<sigma>,y). case_nat y \<sigma>) \<circ> (\<lambda>\<sigma>. (\<sigma>, expr_sem_rf \<sigma> e1))" (is "_ = ?f")
    by (intro ext) simp
  also have "?f \<in> measurable (state_measure V \<Gamma>) (stock_measure t2)"
    apply (intro measurable_comp, rule measurable_Pair, rule measurable_ident_sets[OF refl])
    apply (rule M1, subst measurable_split_conv, rule measurable_case_nat')
    apply (rule measurable_snd, rule measurable_fst, rule M2)
    done
  finally show ?case .
qed (simp_all add: expr_sem_rf_def)

lemma expr_sem_rf_sound:
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> randomfree e \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow>
       return_val (expr_sem_rf \<sigma> e) = expr_sem \<sigma> e"
proof (induction arbitrary: V \<sigma> rule: expr_typing.induct)
  case (et_val \<Gamma> v)
  thus ?case by simp
next
  case (et_var \<Gamma> x)
 thus ?case by simp
next
  case (et_pair \<Gamma> e1 t1 e2 t2 V \<sigma>)
  let ?M = "state_measure V \<Gamma>"
  from et_pair.hyps and et_pair.prems
    have e1: "return_val (expr_sem_rf \<sigma> e1) = expr_sem \<sigma> e1" and
         e2: "return_val (expr_sem_rf \<sigma> e2) = expr_sem \<sigma> e2" 
      by (auto intro!: et_pair.IH[of V])

  from e1 and et_pair.prems have "space (return_val (expr_sem_rf \<sigma> e1)) = type_universe t1"
    by (subst e1, subst space_expr_sem[OF et_pair.hyps(1)])
       (auto dest: state_measure_var_type)
  hence A: "val_type (expr_sem_rf \<sigma> e1) = t1" "expr_sem_rf \<sigma> e1 \<in> type_universe t1" 
      by (auto simp add: return_val_def)
  from e2 and et_pair.prems have "space (return_val (expr_sem_rf \<sigma> e2)) = type_universe t2"
    by (subst e2, subst space_expr_sem[OF et_pair.hyps(2)])
       (auto dest: state_measure_var_type)
  hence B: "val_type (expr_sem_rf \<sigma> e2) = t2" "expr_sem_rf \<sigma> e2 \<in> type_universe t2" 
      by (auto simp add: return_val_def)

  have "expr_sem \<sigma> (<e1, e2>) = expr_sem \<sigma> e1 \<guillemotright>= 
            (\<lambda>v. expr_sem \<sigma> e2 \<guillemotright>= (\<lambda>w. return_val (<|v,w|>)))" by simp
  also have "expr_sem \<sigma> e1 = return (stock_measure t1) (expr_sem_rf \<sigma> e1)"
    using e1 by (simp add: et_pair.prems return_val_def A)
  also have "... \<guillemotright>= (\<lambda>v. expr_sem \<sigma> e2 \<guillemotright>= (\<lambda>w. return_val (<|v,w|>))) =
          ... \<guillemotright>= (\<lambda>v. return_val (<|v, expr_sem_rf \<sigma> e2|>))"
  proof (intro bind_cong ballI)
    fix v assume "v \<in> space (return (stock_measure t1) (expr_sem_rf \<sigma> e1))"
    hence v: "val_type v = t1" "v \<in> type_universe t1" by (simp_all add:)
    have "expr_sem \<sigma> e2 \<guillemotright>= (\<lambda>w. return_val (<|v,w|>)) = 
              return (stock_measure t2) (expr_sem_rf \<sigma> e2) \<guillemotright>= (\<lambda>w. return_val (<|v,w|>))"
      using e2 by (simp add: et_pair.prems return_val_def B)
    also have "... = return (stock_measure t2) (expr_sem_rf \<sigma> e2) \<guillemotright>= 
                         (\<lambda>w. return (stock_measure (PRODUCT t1 t2)) (<|v,w|>))"
    proof (intro bind_cong ballI)
      fix w assume "w \<in> space (return (stock_measure t2) (expr_sem_rf \<sigma> e2))"
      hence w: "val_type w = t2" by (simp add:)
      thus "return_val (<|v,w|>) = return (stock_measure (PRODUCT t1 t2)) (<|v,w|>)"
        by (auto simp: return_val_def v w)
    qed
    also have "... = return_val (<|v, expr_sem_rf \<sigma> e2|>)"
      by (subst bind_return, rule measurable_compose[OF _ return_measurable], 
          subst stock_measure.simps, measurable)
         (auto intro!: measurable_const injI simp: v B return_val_def)
    finally show "expr_sem \<sigma> e2 \<guillemotright>= (\<lambda>w. return_val (<|v,w|>)) = 
                      return_val (<|v, expr_sem_rf \<sigma> e2|>)" .
  qed
  also have "(\<lambda>v. <|v, expr_sem_rf \<sigma> e2|>) \<in> measurable (stock_measure t1) (stock_measure (PRODUCT t1 t2))"
    by (subst stock_measure.simps, measurable) (auto intro!: injI simp: B)
  hence "return (stock_measure t1) (expr_sem_rf \<sigma> e1) \<guillemotright>= (\<lambda>v. return_val (<|v, expr_sem_rf \<sigma> e2|>)) = 
             return_val (<|expr_sem_rf \<sigma> e1, expr_sem_rf \<sigma> e2|>)"
    by (subst bind_return, rule measurable_compose[OF _ measurable_return_val])
       (auto simp: A)
  finally show "return_val (expr_sem_rf \<sigma> (<e1,e2>)) = expr_sem \<sigma> (<e1, e2>)" by simp
next
  case (et_if \<Gamma> b e1 t e2 V \<sigma>)
  let ?P = "\<lambda>e. expr_sem \<sigma> e = return_val (expr_sem_rf \<sigma> e)"
  from et_if.prems have A: "?P b" "?P e1" "?P e2" by ((intro et_if.IH[symmetric], simp_all) [])+
  from et_if.prems and et_if.hyps have "space (expr_sem \<sigma> b) = type_universe BOOL"
    by (intro space_expr_sem) (auto simp: state_measure_var_type)
  hence [simp]: "val_type (expr_sem_rf \<sigma> b) = BOOL" by (simp add: A return_val_def)
  have B: "return_val (expr_sem_rf \<sigma> e1) \<in> space (kernel_space (stock_measure t))"
          "return_val (expr_sem_rf \<sigma> e2) \<in> space (kernel_space (stock_measure t))"
    using et_if.hyps and et_if.prems 
    by ((subst A[symmetric], intro measurable_space[OF measurable_expr_sem], auto) [])+
  thus ?case by (simp only: expr_sem.simps A, subst bind_return_val'') (auto intro!: measurable_If)
next
  case (et_op \<Gamma> e t oper t' V)
  let ?M = "PiM V (\<lambda>x. stock_measure (\<Gamma> x))"
  from et_op.prems have e: "return_val (expr_sem_rf \<sigma> e) = expr_sem \<sigma> e"
    by (intro et_op.IH[of V]) auto

  with et_op.prems have "space (return_val (expr_sem_rf \<sigma> e)) = type_universe t"
    by (subst e, subst space_expr_sem[OF et_op.hyps(1)])
       (auto dest: state_measure_var_type)
  hence A: "val_type (expr_sem_rf \<sigma> e) = t" "expr_sem_rf \<sigma> e \<in> type_universe t" 
    by (auto simp add: return_val_def)
  from et_op.prems e
    have "expr_sem \<sigma> (Operator oper e) = 
                 return_val (expr_sem_rf \<sigma> e) \<guillemotright>= (\<lambda>v. return_val (op_sem oper v))" by simp
  also have "... = return_val (op_sem oper (expr_sem_rf \<sigma> e))"
    by (subst return_val_def, rule bind_return,
        rule measurable_compose[OF measurable_op_sem measurable_return_val])
       (auto simp: A et_op.hyps)
  finally show "return_val (expr_sem_rf \<sigma> (Operator oper e)) = expr_sem \<sigma> (Operator oper e)" by simp
next
  case (et_let \<Gamma> e1 t1 e2 t2 V)
  let ?M = "state_measure V \<Gamma>" and ?N = "state_measure (shift_var_set V) (case_nat t1 \<Gamma>)"
  let ?\<sigma>' = "case_nat (expr_sem_rf \<sigma> e1) \<sigma>"
  from et_let.prems have e1: "return_val (expr_sem_rf \<sigma> e1) = expr_sem \<sigma> e1"
    by (auto intro!: et_let.IH(1)[of V])
  from et_let.prems have S: "space (return_val (expr_sem_rf \<sigma> e1)) = type_universe t1"
    by (subst e1, subst space_expr_sem[OF et_let.hyps(1)])
       (auto dest: state_measure_var_type)
  hence A: "val_type (expr_sem_rf \<sigma> e1) = t1" "expr_sem_rf \<sigma> e1 \<in> type_universe t1" 
    by (auto simp add: return_val_def)
  with et_let.prems have e2: "\<And>\<sigma>. \<sigma> \<in> space ?N \<Longrightarrow> return_val (expr_sem_rf \<sigma> e2) = expr_sem \<sigma> e2"
    using subset_shift_var_set
    by (intro et_let.IH(2)[of "shift_var_set V"]) (auto simp del: fun_upd_apply)

  from et_let.prems have "expr_sem \<sigma> (LetVar e1 e2) = 
                              return_val (expr_sem_rf \<sigma> e1) \<guillemotright>= (\<lambda>v. expr_sem (case_nat v \<sigma>) e2)" 
    by (simp add: e1)
  also from et_let.prems 
    have "... = return_val (expr_sem_rf \<sigma> e1) \<guillemotright>= (\<lambda>v. return_val (expr_sem_rf (case_nat v \<sigma>) e2))"
    by (intro bind_cong ballI, subst e2) (auto simp: S)
  also from et_let have Me2[measurable]: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e2) \<in> measurable ?N (stock_measure t2)"
    using subset_shift_var_set by (intro measurable_expr_sem_rf) auto
  have "(\<lambda>(\<sigma>,y). case_nat y \<sigma>) \<circ> (\<lambda>y. (\<sigma>, y)) \<in> measurable (stock_measure t1) ?N"
    using `\<sigma> \<in> space ?M` by simp
  have  "return_val (expr_sem_rf \<sigma> e1) \<guillemotright>= (\<lambda>v. return_val (expr_sem_rf (case_nat v \<sigma>) e2)) = 
              return_val (expr_sem_rf ?\<sigma>' e2)" using `\<sigma> \<in> space ?M`
  by (subst return_val_def, intro bind_return, subst A)
     (rule measurable_compose[OF _ measurable_return_val[of t2]], simp_all)
  finally show ?case by simp
qed simp_all

lemma val_type_expr_sem_rf:
  assumes "\<Gamma> \<turnstile> e : t" "randomfree e" "free_vars e \<subseteq> V" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "val_type (expr_sem_rf \<sigma> e) = t"
proof-
  have "type_universe (val_type (expr_sem_rf \<sigma> e)) = space (return_val (expr_sem_rf \<sigma> e))"
    by (simp add: return_val_def)
  also from assms have "return_val (expr_sem_rf \<sigma> e) = expr_sem \<sigma> e"
    by (intro expr_sem_rf_sound) auto
  also from assms have "space ... = type_universe t"
    by (intro space_expr_sem[of \<Gamma>]) 
       (auto simp: state_measure_def space_PiM  dest: PiE_mem)
  finally show ?thesis by simp
qed

lemma expr_sem_rf_eq_on_vars:
  "(\<And>x. x\<in>free_vars e \<Longrightarrow> \<sigma>1 x = \<sigma>2 x) \<Longrightarrow> expr_sem_rf \<sigma>1 e = expr_sem_rf \<sigma>2 e"
proof (induction e arbitrary: \<sigma>1 \<sigma>2)
  case (Operator oper e \<sigma>1 \<sigma>2)
  hence "expr_sem_rf \<sigma>1 e = expr_sem_rf \<sigma>2 e" by (intro Operator.IH) auto
  thus ?case by simp
next
  case (LetVar e1 e2 \<sigma>1 \<sigma>2)
  hence A: "expr_sem_rf \<sigma>1 e1 = expr_sem_rf \<sigma>2 e1" by (intro LetVar.IH) auto
  {
    fix y assume "y \<in> free_vars e2"
    hence "case_nat (expr_sem_rf \<sigma>1 e1) \<sigma>1 y = case_nat (expr_sem_rf \<sigma>2 e1) \<sigma>2 y"
      using LetVar(3) by (auto simp add: A split: nat.split)
  }
  hence "expr_sem_rf (case_nat (expr_sem_rf \<sigma>1 e1) \<sigma>1) e2 = 
           expr_sem_rf (case_nat (expr_sem_rf \<sigma>2 e1) \<sigma>2) e2" by (intro LetVar.IH) simp
  thus ?case by simp
next
  case (Pair e1 e2 \<sigma>1 \<sigma>2)
  have "expr_sem_rf \<sigma>1 e1 = expr_sem_rf \<sigma>2 e1" "expr_sem_rf \<sigma>1 e2 = expr_sem_rf \<sigma>2 e2"
    by (intro Pair.IH, simp add: Pair)+
  thus ?case by simp
next
  case (IfThenElse b e1 e2 \<sigma>1 \<sigma>2)
  have "expr_sem_rf \<sigma>1 b = expr_sem_rf \<sigma>2 b" "expr_sem_rf \<sigma>1 e1 = expr_sem_rf \<sigma>2 e1"
       "expr_sem_rf \<sigma>1 e2 = expr_sem_rf \<sigma>2 e2" by (intro IfThenElse.IH, simp add: IfThenElse)+
  thus ?case by simp
next
  case (Random dst e \<sigma>1 \<sigma>2)
  have "expr_sem_rf \<sigma>1 e = expr_sem_rf \<sigma>2 e" by (intro Random.IH) (simp add: Random)
  thus ?case by simp
qed auto


(*
subsection {* Substitution of free variables *}

primrec expr_subst :: "expr \<Rightarrow> expr \<Rightarrow> vname \<Rightarrow> expr" ("_\<langle>_'/_\<rangle>" [1000,0,0] 999) where
  "(Val v)\<langle>_/_\<rangle> = Val v"
| "(Var y)\<langle>f/x\<rangle> = (if y = x then f else Var y)"
| "<e1,e2>\<langle>f/x\<rangle> = <e1\<langle>f/x\<rangle>, e2\<langle>f/x\<rangle>>"
| "(<oper> e)\<langle>f/x\<rangle> = <oper> (e\<langle>f/x\<rangle>)"
| "(LET e1 IN e2)\<langle>f/x\<rangle> = LET y = e1\<langle>f/x\<rangle> IN if y = x then e2 else e2\<langle>f/x\<rangle>"
| "(IF b THEN e1 ELSE e2)\<langle>f/x\<rangle> = IF b\<langle>f/x\<rangle> THEN e1\<langle>f/x\<rangle> ELSE e2\<langle>f/x\<rangle>"
| "(Random dst e)\<langle>f/x\<rangle> = Random dst (e\<langle>f/x\<rangle>)"
| "(Fail t)\<langle>f/x\<rangle> = Fail t"

primrec bound_vars :: "expr \<Rightarrow> vname set" where
  "bound_vars (Val _) = {}"
| "bound_vars (Var _) = {}"
| "bound_vars <e1,e2> = bound_vars e1 \<union> bound_vars e2"
| "bound_vars (<_> e) = bound_vars e"
| "bound_vars (LET x = e1 IN e2) = {x} \<union> bound_vars e1 \<union> bound_vars e2"
| "bound_vars (IF b THEN e1 ELSE e2) = bound_vars b \<union> bound_vars e1 \<union> bound_vars e2"
| "bound_vars (Random _ e) = bound_vars e"
| "bound_vars (Fail _) = {}"

lemma expr_typing_eq_on_free_vars:
  "\<Gamma>1 \<turnstile> e : t \<Longrightarrow> (\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma>1 x = \<Gamma>2 x) \<Longrightarrow> \<Gamma>2 \<turnstile> e : t"
proof (induction arbitrary: \<Gamma>2 rule: expr_typing.induct)
  case et_let
  thus ?case by (intro expr_typing.intros) auto
qed (auto intro!: expr_typing.intros simp del: fun_upd_apply)

lemma expr_typing_subst:
  assumes "\<Gamma> \<turnstile> e : t1" "\<Gamma> \<turnstile> f : t'" "\<Gamma> x = t'" "free_vars f \<inter> bound_vars e = {}"
  shows "\<Gamma> \<turnstile> e\<langle>f/x\<rangle> : t1"
using assms
proof (induction rule: expr_typing.induct)
  case (et_let \<Gamma> e1 t1 y e2 t2)
  from et_let.prems have A: "\<Gamma> \<turnstile> e1\<langle>f/x\<rangle> : t1" by (intro et_let.IH) auto
  show ?case
  proof (cases "y = x")
    assume "y \<noteq> x"
    from et_let.prems have "\<Gamma>(y := t1) \<turnstile> f : t'"
      by (intro expr_typing_eq_on_free_vars[OF `\<Gamma> \<turnstile> f : t'`]) auto
    moreover from `y \<noteq> x` have "(\<Gamma>(y := t1)) x = \<Gamma> x" by simp
    ultimately have "\<Gamma>(y := t1) \<turnstile> e2\<langle>f/x\<rangle> : t2" using et_let.prems
      by (intro et_let.IH) (auto simp del: fun_upd_apply)
    with A and `y \<noteq> x` show ?thesis by (auto intro: expr_typing.intros)
  qed (insert et_let, auto intro!: expr_typing.intros simp del: fun_upd_apply)
qed (insert assms(2), auto intro: expr_typing.intros)

lemma expr_subst_randomfree:
  assumes "\<Gamma> \<turnstile> f : t" "randomfree f" "free_vars f \<subseteq> V" "free_vars f \<inter> bound_vars e = {}" 
          "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows   "expr_sem \<sigma> (e\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e"
using assms(1,3,4,5)
proof (induction e arbitrary: \<sigma> V \<Gamma>)
  case (Pair e1 e2 \<sigma> V \<Gamma>)
    from Pair.prems have "expr_sem \<sigma> (e1\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1"
                     and "expr_sem \<sigma> (e2\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e2"
      by (auto intro!: Pair.IH[of \<Gamma> V \<sigma>])
    thus ?case by (simp del: fun_upd_apply)
next
  case (IfThenElse b e1 e2 \<sigma> V \<Gamma>)
    from IfThenElse.prems 
      have "expr_sem \<sigma> (b\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) b"
           "expr_sem \<sigma> (e1\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1"
           "expr_sem \<sigma> (e2\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e2"
      by (auto intro!: IfThenElse.IH[of \<Gamma> V \<sigma>])
    thus ?case by (simp only: expr_sem.simps expr_subst.simps)
next
  case (LetVar y e1 e2)
  from LetVar.prems have A: "expr_sem \<sigma> (e1\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1" 
    by (intro LetVar.IH) auto
  show ?case
  proof (cases "y = x")
    assume "y = x"
    with LetVar.prems show ?case by (auto simp add: A simp del: fun_upd_apply)
  next
    assume "y \<noteq> x"
    {
      fix v assume "v \<in> space (expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1)"
      let ?\<sigma>' = "\<sigma>(y := v)" and ?\<Gamma>' = "\<Gamma>(y := val_type v)"
      from LetVar.prems have "\<Gamma>(y := val_type v) \<turnstile> f : t" by (auto intro: expr_typing_eq_on_free_vars)
      moreover from LetVar.prems have "?\<sigma>' \<in> space (state_measure (insert y V) ?\<Gamma>')"
        by (auto simp: state_measure_def space_PiM split: split_if_asm)
      ultimately have "expr_sem ?\<sigma>' (e2\<langle>f/x\<rangle>) = expr_sem (?\<sigma>'(x := expr_sem_rf f ?\<sigma>')) e2"
        using LetVar.prems and `y \<noteq> x`
        by (intro LetVar.IH(2)[of "\<Gamma>(y := val_type v)" "insert y V"]) (auto simp del: fun_upd_apply)
      also from LetVar.prems have "expr_sem_rf f ?\<sigma>' = expr_sem_rf f \<sigma>"
        by (intro expr_sem_rf_eq_on_vars) auto
      finally have "expr_sem (\<sigma>(y := v)) (e2\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>, y := v)) e2"
        using `y \<noteq> x` by (subst fun_upd_twist) (simp_all del: fun_upd_apply)
    }
    with A and `y \<noteq> x` show ?thesis by (auto simp del: fun_upd_apply intro!: bind_cong)
  qed
qed (simp_all add: expr_sem_rf_sound assms)

lemma stock_measure_context_upd:
  "(\<lambda>y. stock_measure ((\<Gamma>(x := t)) y)) = (\<lambda>y. stock_measure (\<Gamma> y))(x := stock_measure t)"
  by (intro ext) simp

lemma Let_det_eq_subst:
  assumes "\<Gamma> \<turnstile> LET x = f IN e : t" "randomfree f" "free_vars (LET x = f IN e) \<subseteq> V"
          "free_vars f \<inter> bound_vars e = {}" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows   "expr_sem \<sigma> (LET x = f IN e) = expr_sem \<sigma> (e\<langle>f/x\<rangle>)"
proof-
  from assms(1) obtain t' where t1: "\<Gamma> \<turnstile> f : t'" and t2: "\<Gamma>(x := t') \<turnstile> e : t" by auto
  with assms have "expr_sem \<sigma> (LET x = f IN e) = 
                       return_val (expr_sem_rf f \<sigma>) \<guillemotright>= (\<lambda>v. expr_sem (\<sigma>(x := v)) e)" (is "_ = ?M")
    by (auto simp: expr_sem_rf_sound)
  also have "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<circ> (\<lambda>(\<sigma>,v). \<sigma>(x := v)) \<circ> (\<lambda>v. (\<sigma>,v)) \<in> 
                 measurable (stock_measure ((\<Gamma>(x := t')) x)) (kernel_space (stock_measure t))"
    apply (intro measurable_comp, rule measurable_Pair1', rule assms)
    apply (subst fun_upd_same, unfold state_measure_def)
    apply (rule measurable_add_dim', subst stock_measure_context_upd[symmetric])
    apply (insert assms, auto intro!: measurable_expr_sem[unfolded state_measure_def] t1 t2 
                              simp del: fun_upd_apply)
    done                   
  hence "(\<lambda>v. expr_sem (\<sigma>(x := v)) e) \<in> 
                 measurable (stock_measure ((\<Gamma>(x := t')) x)) (kernel_space (stock_measure t))"
    by (simp add: o_def)
  with assms have "?M = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e"
    unfolding return_val_def 
    by (intro bind_return) (auto simp: val_type_expr_sem_rf[OF t1] 
                                       type_universe_def simp del: type_universe_type)
  also from assms t1 t2 have "... = expr_sem \<sigma> (e\<langle>f/x\<rangle>)"
    by (intro expr_subst_randomfree[symmetric]) auto
  finally show ?thesis .
qed *)

end
