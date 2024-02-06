(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Multivariate Polynomials: Instance\<close>

theory Concrete_Multivariate_Polynomials
  imports 
    "../Generalized_Sumcheck_Protocol/Sumcheck_as_Public_Coin_Proof"
    Polynomial_Instantiation
    Roots_Bounds
begin

declare total_degree_zero [simp del]

subsection \<open>Auxiliary lemmas\<close>

lemma card_indep_bound: 
  assumes "P \<Longrightarrow> card {x. Q x} \<le> d"
  shows "card {x. P \<and> Q x} \<le> d" 
  using assms
  by (cases P) auto
 
lemma sum_point_neq_zero [simp]: "(\<Sum>x' | x' = x \<and> f x' \<noteq> 0. f x') = f x"
proof - 
  have \<open>(\<Sum>x' | x' = x \<and> f x' \<noteq> 0. f x') = (\<Sum>x' | x' = x \<and> f x \<noteq> 0. f x')\<close> 
    by (intro sum.cong) auto
  also have \<open>\<dots> = f x\<close> 
    by (cases "f x = 0") (simp_all)
  finally show ?thesis .
qed


subsection \<open>Proving the assumptions of the locale\<close>

subsubsection \<open>Variables\<close>

\<comment> \<open>The term @{term vars} is already defined in @{theory "Polynomials.More_MPoly_Type"}.\<close>

\<comment> \<open>We show the assumptions @{thm [source] "multi_variate_polynomial.vars_finite"}, 
@{thm [source] "multi_variate_polynomial.vars_add"}, 
@{thm [source] "multi_variate_polynomial.vars_zero"} and 
@{thm [source] "multi_variate_polynomial.vars_inst"} from the locale 
@{locale "multi_variate_polynomial"}.\<close>

lemma vars_zero: \<open>vars 0 = {}\<close>
  by (simp add: vars_def zero_mpoly.rep_eq)

lemma vars_inst: \<open>vars (inst p \<sigma>) \<subseteq> vars p - dom \<sigma>\<close>
  by (auto simp add: vars_def inst_defs keys_def MPoly_inverse
                     finite_inst_fun_keys lookup_inst_monom_resid 
           elim!: sum.not_neutral_contains_not_neutral split: if_splits)  
   

\<comment> \<open>Lemmas for to translate the roots bound to the format of the locale assumption.\<close>

lemma vars_minus: \<open>vars p = vars (-p)\<close>
  by(simp add: vars_def uminus_mpoly.rep_eq)

lemma vars_subtr: 
  fixes p q :: \<open>'a::comm_ring mpoly\<close>
  shows \<open>vars (p - q) \<subseteq> vars p \<union> vars q\<close>
  by(simp add: vars_add[where ?p1.0 = "p" and ?p2.0 = "-q", simplified] vars_minus[where p = "q"])


subsubsection \<open>Degree\<close>

\<comment> \<open>We define the degree of a multivariate polynomial as its total degree\<close>

abbreviation deg :: \<open>('a::zero) mpoly \<Rightarrow> nat\<close> where
  \<open>deg p \<equiv> total_degree p\<close> 


\<comment> \<open>We show the assumptions @{thm [source] "multi_variate_polynomial.deg_zero"}, 
@{thm [source] "multi_variate_polynomial.deg_add"} and @{thm [source] "multi_variate_polynomial.deg_inst"}.\<close>

lemma deg_zero: \<open>deg 0 = 0\<close> by (fact total_degree_zero)

lemma deg_add: \<open>deg (p + q) \<le> max (deg p) (deg q)\<close> 
proof - 
  have \<open>deg (p + q) = Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of p + mapping_of q)))\<close>
    by (simp add: total_degree.rep_eq plus_mpoly.rep_eq)
  also have \<open>... \<le> Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` (keys (mapping_of p) \<union> keys (mapping_of q))))\<close>
    by (intro Max_mono Set.insert_mono image_mono Poly_Mapping.keys_add) (auto)
  also have \<open>... = Max ((insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of p)))
                      \<union> (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of q))))\<close>
    by (simp add: image_Un)
  also have \<open>... = max (Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of p)))) 
                        (Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of q))))\<close>
    by (intro Max_Un) (auto)
  also have \<open>... = max (deg p) (deg q)\<close>
    by (simp add: total_degree.rep_eq)
  finally show ?thesis .
qed

lemma deg_inst: \<open>deg (inst p \<sigma>) \<le> deg p\<close> 
proof (transfer)
  fix p :: \<open>(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a\<close> and \<sigma> :: "(nat, 'a) subst"
  show \<open>Max (insert 0 ((\<lambda>m. sum (lookup m) (keys m)) ` keys (inst_aux p \<sigma>))) 
      \<le> Max (insert 0 ((\<lambda>m. sum (lookup m) (keys m)) ` keys p))\<close> 
    by (auto simp add: keys_def inst_defs finite_inst_fun_keys lookup_inst_monom_resid
             elim!: sum.not_neutral_contains_not_neutral)
       (fastforce simp add: Max_ge_iff intro!: disjI2  intro: sum_mono2)
qed


\<comment> \<open>Lemmas for translating the roots bound to the format of the locale assumption.\<close>

lemma deg_minus: \<open>deg p = deg (-p)\<close>
  by(auto simp add: total_degree_def uminus_mpoly.rep_eq)

lemma deg_subtr:
  fixes p q :: \<open>'a::comm_ring mpoly\<close>
  shows \<open>deg (p - q) \<le> max (deg p) (deg (q))\<close>
  by(auto simp add: deg_add[where p = "p" and q = "-q", simplified] deg_minus[where p = "q"])


subsubsection \<open>Evaluation\<close>

\<comment> \<open>Our evaluation is defined as insertion in MPoly_Type\<close>

abbreviation eval :: \<open>'a mpoly \<Rightarrow> (nat, 'a) subst \<Rightarrow> ('a::comm_semiring_1)\<close> where 
  \<open>eval p \<sigma> \<equiv> insertion (the o \<sigma>) p\<close>

\<comment> \<open>We show the assumptions @{thm [source] "multi_variate_polynomial.eval_zero"}, 
@{thm [source] "multi_variate_polynomial.eval_add"} and @{thm [source] "multi_variate_polynomial.eval_inst"}.\<close>

lemma eval_zero: \<open>eval 0 \<sigma> = 0\<close> 
  by (fact insertion_zero)

lemma eval_add: \<open>vars p \<union> vars q \<subseteq> dom \<sigma> \<Longrightarrow> eval (p + q) \<sigma> = eval p \<sigma> + eval q \<sigma>\<close> 
  by (intro insertion_add)

\<comment> \<open>evaluation and instantiation\<close>

lemma eval_inst: \<open>eval (inst p \<sigma>) \<rho> = eval p (\<rho> ++ \<sigma>)\<close>
proof (transfer, transfer)
  fix p :: \<open>(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a\<close> and \<sigma> \<rho> :: \<open>(nat, 'a) subst\<close> 
  assume fin: \<open>finite {m. p m \<noteq> 0}\<close>  
  show \<open>insertion_fun (the \<circ> \<rho>) (inst_fun p \<sigma>) = insertion_fun (the \<circ> \<rho> ++ \<sigma>) p\<close> 
  proof -
    let ?mon = \<open>\<lambda>\<sigma> m v. the (\<sigma> v) ^ lookup m v\<close>

    have \<open>x ^ lookup m v \<noteq> 1 \<Longrightarrow> v \<in> keys m\<close> for x :: "'a" and v and m :: "nat \<Rightarrow>\<^sub>0 nat"
      using zero_less_iff_neq_zero by (fastforce simp add: in_keys_iff)
    then have exp_fin: \<open>finite {v. P v \<and> f v ^ lookup m v \<noteq> 1}\<close> 
      for f :: "nat \<Rightarrow> 'a" and m :: "nat \<Rightarrow>\<^sub>0 nat" and P :: "nat \<Rightarrow> bool"
      by (auto intro: finite_subset[where B="keys m"])

    note fin_simps [simp] = fin this this[where P1="\<lambda>_. True", simplified]
    note map_add_simps [simp] = map_add_dom_app_simps(1,3)

    have \<open>insertion_fun (the \<circ> \<rho>) (inst_fun p \<sigma>) = 
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0. 
              p m' * inst_monom_coeff m' \<sigma>) * (\<Prod>v. ?mon \<rho> m v))\<close>
      by (simp add: insertion_fun_def inst_fun_def)

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0. 
              p m' * inst_monom_coeff m' \<sigma> * (\<Prod>v. ?mon \<rho> m v)))\<close>
      by (intro Sum_any.cong) (simp add: sum_distrib_right)

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0. 
              p m' * inst_monom_coeff m' \<sigma> * (\<Prod>v | v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon \<rho> m' v)))\<close>
      by (intro Sum_any.cong sum.cong)
         (auto simp add: lookup_inst_monom_resid Prod_any.expand_set intro: arg_cong)

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> 
                    (\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1. ?mon \<sigma> m' v) \<noteq> 0. 
              p m' * 
              ((\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1. ?mon (\<rho> ++ \<sigma>) m' v) * 
               (\<Prod>v | v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon (\<rho> ++ \<sigma>) m' v))))\<close>
      by (simp add: inst_monom_coeff_def mult.assoc)

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> 
                    (\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1. ?mon \<sigma> m' v) \<noteq> 0 \<and>
                    (\<Prod>v | v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon \<rho> m' v) \<noteq> 0. 
              p m' * 
              ((\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1. ?mon (\<rho> ++ \<sigma>) m' v) * 
               (\<Prod>v | v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon (\<rho> ++ \<sigma>) m' v))))\<close>
      by (intro Sum_any.cong sum.mono_neutral_right) (auto)

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> 
                    (\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1. ?mon \<sigma> m' v) \<noteq> 0 \<and>
                    (\<Prod>v | v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon \<rho> m' v) \<noteq> 0. 
              p m' * 
              (\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1 \<or> v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon (\<rho> ++ \<sigma>) m' v)))\<close>
      by (subst prod.union_disjoint[symmetric])
         (auto  intro!: Sum_any.cong sum.cong prod.cong intro: arg_cong)

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> 
                    (\<Prod>v | v \<in> dom \<sigma> \<and> ?mon \<sigma> m' v \<noteq> 1. ?mon \<sigma> m' v) \<noteq> 0 \<and>
                    (\<Prod>v | v \<notin> dom \<sigma> \<and> ?mon \<rho> m' v \<noteq> 1. ?mon \<rho> m' v) \<noteq> 0. 
                    p m' * (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v)))\<close>
      apply (intro Sum_any.cong sum.cong arg_cong[where f="(*) x" for x], simp)
      apply (simp add: Prod_any.expand_set)
      apply (intro prod.cong, simp_all)
      by (metis (no_types, opaque_lifting) map_add_dom_app_simps(1,3))

    also have \<open>\<dots> =
      (\<Sum>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v) \<noteq> 0. 
                    p m' * (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v)))\<close>
      apply (intro Sum_any.cong sum.mono_neutral_right, simp_all)
       apply (safe, simp_all)
       \<comment> \<open>fixme: cannot get auto/fastforce to do instantiations below\<close>
       subgoal for m v z    
         by (auto dest: Prod_any_not_zero[rotated, where a=v])
      subgoal for m' v
        by (auto simp add: domIff dest: Prod_any_not_zero[rotated, where a=v])
      done

    also have \<open>\<dots> = 
      (\<Sum>m. (sum 
              (\<lambda>m'. p m' * (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v)) 
              {m' \<in> {m'. p m' \<noteq> 0 \<and> (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v) \<noteq> 0}. 
                    inst_monom_resid m' \<sigma> = m}))\<close>
      by (intro Sum_any.cong sum.cong) (auto)

    also have \<open>\<dots> = 
      (\<Sum>m \<in> (\<lambda>m'. inst_monom_resid m' \<sigma>) ` {m'. p m' \<noteq> 0 \<and> (\<Prod>v. the ((\<rho> ++ \<sigma>) v) ^ lookup m' v) \<noteq> 0}.
            (sum 
              (\<lambda>m'. p m' * (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v)) 
              {m' \<in> {m'. p m' \<noteq> 0 \<and> (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m' v) \<noteq> 0}. 
                    inst_monom_resid m' \<sigma> = m}))\<close>
      by (intro Sum_any.expand_superset) (auto elim: sum.not_neutral_contains_not_neutral)

    also have \<open>\<dots> = (\<Sum>m. p m * (\<Prod>v. ?mon (\<rho> ++ \<sigma>) m v))\<close>
      by (subst Sum_any.expand_set, subst sum.group) (auto)

    also have \<open>\<dots> = insertion_fun (the \<circ> \<rho> ++ \<sigma>) p\<close>
      by (simp add: insertion_fun_def)
    finally show ?thesis .
  qed
qed

\<comment> \<open>Lemmas for translating the roots bound to the format of the locale assumption.\<close>

lemma eval_minus:
  fixes p :: \<open>'a::comm_ring_1 mpoly\<close>
  shows \<open>eval (-p) \<sigma> = - eval p \<sigma>\<close>
  using sum_negf[where f = "\<lambda>a . (lookup (mapping_of p) a * (\<Prod>aa. the (\<sigma> aa) ^ lookup a aa))"]
  by(auto simp add: uminus_mpoly.rep_eq insertion_def insertion_aux_def insertion_fun_def)
    (smt (verit) Collect_cong Sum_any.expand_set add.inverse_neutral neg_equal_iff_equal)

lemma eval_subtr:
  fixes p q :: \<open>'a::comm_ring_1 mpoly\<close>
  assumes \<open>vars p \<subseteq> dom \<sigma>\<close> \<open>vars q \<subseteq> dom \<sigma>\<close>
  shows \<open>eval (p - q) \<sigma> = eval p \<sigma> - eval q \<sigma>\<close>
  using assms
  by(auto simp add: vars_minus[where p = "q"] eval_minus[where p = "q"]
                    eval_add[where p = "p" and q = "-q", simplified])


subsubsection \<open>Roots assumption\<close>

lemma univariate_eval_as_insertion: 
  fixes p::\<open>'a::comm_ring_1 mpoly\<close> and r
  assumes "vars p \<subseteq> {x}"
  shows "eval p [x \<mapsto> r] = insertion (\<lambda>x. r) p"
  using assms 
  by (intro insertion_irrelevant_vars) auto

lemma univariate_mpoly_roots_bound_eval:   \<comment> \<open>variant using @{term eval}\<close>
  fixes p::"'a::idom mpoly"
  assumes \<open>vars p \<subseteq> {x}\<close> \<open>p \<noteq> 0\<close> 
  shows \<open>card {r. eval p [x \<mapsto> r] = 0} \<le> deg p\<close>
  using assms
  by (simp add: univariate_eval_as_insertion univariate_mpoly_roots_bound)

lemma mpoly_roots:
  fixes p q :: \<open>'a::idom mpoly\<close> and d x 
  shows \<open>card {r. deg p \<le> d \<and> vars p \<subseteq> {x} \<and> deg q \<le> d \<and> vars q \<subseteq> {x} \<and> 
                  p \<noteq> q \<and> eval p [x \<mapsto> r] = eval q [x \<mapsto> r]} \<le> d\<close>
proof (intro card_indep_bound)
  assume \<open>deg p \<le> d\<close> \<open>vars p \<subseteq> {x}\<close> \<open>deg q \<le> d\<close> \<open>vars q \<subseteq> {x}\<close> \<open>p \<noteq> q\<close>
  show \<open>card {r. eval p [x \<mapsto> r] = eval q [x \<mapsto> r]} \<le> d\<close>
  proof -
    have \<open>card {r. eval p [x \<mapsto> r] = eval q [x \<mapsto> r]} = card {r. eval (p - q) [x \<mapsto> r] = 0}\<close>
      using \<open>vars p \<subseteq> {x}\<close> \<open>vars q \<subseteq> {x}\<close> by (simp add: eval_subtr)
    also have \<open>\<dots> \<le>  deg (p - q)\<close> 
      using \<open>vars p \<subseteq> {x}\<close> \<open>vars q \<subseteq> {x}\<close> \<open>p \<noteq> q\<close>
      by (intro univariate_mpoly_roots_bound_eval subset_trans[OF vars_subtr]) (auto)
    also have \<open>\<dots> \<le>  d\<close> using \<open>deg p \<le> d\<close> \<open>deg q \<le> d\<close> 
      by (intro le_trans[OF deg_subtr]) (simp)
    finally show ?thesis .
  qed
qed


subsection \<open>Locale interpretation\<close>

text \<open>Finally, collect all relevant lemmas and instantiate the abstract polynomials locale.\<close>

lemmas multi_variate_polynomial_lemmas = 
  vars_finite vars_zero vars_add vars_inst 
  deg_zero deg_add deg_inst
  eval_zero eval_add eval_inst
  mpoly_roots

interpretation mpoly: 
  multi_variate_polynomial vars "deg :: 'a::{finite, idom} mpoly \<Rightarrow> nat" eval inst 
  by (unfold_locales) (auto simp add: multi_variate_polynomial_lemmas)


text \<open>Here are the main results, spezialized for type @{typ \<open>'a mpoly\<close>}. 
The completeness theorem for this type is @{thm [display] "mpoly.completeness"}
and the soundness theorem reads @{thm [display] "mpoly.soundness"}.
\<close>

end
