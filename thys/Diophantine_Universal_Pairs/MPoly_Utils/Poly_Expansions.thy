theory Poly_Expansions
  imports Total_Degree
begin

subsection \<open>Explicit expansions\<close>

lemma mpoly_keys_subset: "keys (mapping_of P) \<subseteq> Abs_poly_mapping ` (!\<^sub>0) ` 
  {i. length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P}"
proof 
  fix k assume assm: "k \<in> keys (mapping_of P)"
  define l::"nat list" where "l \<equiv> map (lookup k \<circ> nat) [0..max_vars P]"

  have 0: "lookup k i = l!\<^sub>0i" for i
  proof (cases "i \<le> max_vars P")
    case True
    have "l!\<^sub>0i = (lookup k \<circ> nat) ([0..max_vars P]!i)"
      by (smt (verit, best) Suc_as_int True l_def le_imp_less_Suc length_map length_upto nth0_nth
          nth_map)
    also have "... = lookup k i"
      by (simp add: True)
    finally show ?thesis 
      by simp
  next
    case False    
    hence "lookup k i = 0"
      unfolding max_vars_def vars_def
      by (metis Suc_eq_plus1 after_max_vars assm in_keys_iff max_vars_def not_less_eq_eq vars_def)
    thus ?thesis 
      using False by (simp add: l_def nth0_0)
  qed

  have 1: "k = Abs_poly_mapping ((!\<^sub>0) l)"
    by (simp add: 0 poly_mapping_eqI)

  have "sum_list l = (\<Sum>i=0..<length l. l!\<^sub>0i)"
    using sum_list_sum_nth by (metis nth0_nth sum.ivl_cong)
  also have "... = sum (lookup k) (keys k)"
    by (metis "1" calculation keys.rep_eq lookup_Abs_poly_mapping_nth0 nth0_sum_list)
  also have "... \<le> total_degree P"
    unfolding total_degree_def using assm by simp
  finally have 2: "sum_list l \<le> total_degree P" .

  show "k \<in> Abs_poly_mapping ` (!\<^sub>0) ` {i. length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P}"
    using 1 2 l_def by simp
qed

lemma monom_single: "monom (Poly_Mapping.single v p) a = Const a * (Var v) ^ p"
proof (induction p)
  case 0
  show ?case by (simp add: Const.abs_eq Const\<^sub>0_def monom.abs_eq)
next
  case (Suc p)
  show ?case
    unfolding power_Suc2 semigroup_mult_class.mult.assoc[symmetric] Suc[symmetric]
    by (metis Suc_eq_plus1 Var.abs_eq Var\<^sub>0_def monom.abs_eq mult.right_neutral mult_monom single_add)
qed

lemma coeff_monom :
"coeff (monom m a) m' = (if m=m' then a else 0)"
  unfolding coeff_def monom_def using lookup_single_eq lookup_single_not_eq
  by (metis monom.rep_eq monom_def)

lemma monom_eq_var:
"monom (Abs_poly_mapping (\<lambda>v'. (Suc 0) when v=v')) 1 = MPoly (Var\<^sub>0 v)"
proof -
  have 0: "Poly_Mapping.single (Abs_poly_mapping (\<lambda>v'. Suc 0 when v=v')) 1 = Var\<^sub>0 v"
    unfolding Var\<^sub>0_def single_def by simp
  hence "MPoly (Poly_Mapping.single (Abs_poly_mapping (\<lambda>v'. Suc 0 when v=v')) 1) = MPoly (Var\<^sub>0 v)"
    by metis
  thus ?thesis unfolding monom_def by simp
qed

lemma monom_eq_power_var:
  "monom (Abs_poly_mapping (\<lambda>v'. n when v = v')) 1 = MPoly (Var\<^sub>0 v)^n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note t=this
  have 0: "lookup (Abs_poly_mapping (\<lambda>v'. n when v = v')) = (\<lambda>v'. n when v = v')
      \<and> lookup (Abs_poly_mapping (\<lambda>v'. Suc 0 when v = v')) = (\<lambda>v'. Suc 0 when v = v')"
    using lookup_Abs_poly_mapping by (simp add: when_def)
  hence "(\<lambda>k. lookup (Abs_poly_mapping (\<lambda>v'. n when v = v')) k
         + lookup (Abs_poly_mapping (\<lambda>v'. Suc 0 when v = v')) k)
      = (\<lambda>k. (\<lambda>v'. n when v = v') k + (\<lambda>v'. Suc 0 when v = v') k)"
    by simp
  also have "... = (\<lambda>k. Suc n when v = k)"
    by (metis "when"(1) "when"(2) add_0_iff add_Suc_right)
  finally have 0: "(\<lambda>k. lookup (Abs_poly_mapping (\<lambda>v'. n when v = v')) k
         + lookup (Abs_poly_mapping (\<lambda>v'. Suc 0 when v = v')) k)
      = (\<lambda>k. Suc n when v = k)" by blast
  have "Abs_poly_mapping (\<lambda>v'. n when v = v') + Abs_poly_mapping (\<lambda>v'. Suc 0 when v = v')
      = Abs_poly_mapping (\<lambda>v'. Suc n when v = v')"
    unfolding plus_poly_mapping_def apply simp using 0 by simp
  then show ?case using monom_eq_var[of v] mult_monom[of "Abs_poly_mapping (\<lambda>v'. n when v = v')" 1
        "Abs_poly_mapping (\<lambda>v'. Suc 0 when v = v')" 1] power_Suc2 lambda_one t by metis
qed

lemma coeff_prod_monom_not_enough:
  fixes m m' a
  assumes "\<exists>k. lookup m k < lookup m' k"
  shows "coeff (monom m' a * Q) m = 0"
proof -
  from assms obtain k where "lookup m k < lookup m' k" by auto
  hence 0: "lookup m k \<noteq> lookup m' k + v" for v
    by simp
  have "m \<noteq> m' + m''" for m''
    unfolding lookup_inject[symmetric]
    using 0[of "lookup m'' k"]
    by (auto simp: lookup_add)
  thus ?thesis
    unfolding coeff_def times_mpoly.rep_eq times_poly_mapping.rep_eq prod_fun_def
    unfolding coeff_def[symmetric] coeff_monom
    unfolding when_def[symmetric] when_mult Sum_any_when_equal'
    apply (subst zero_class.when(2))
    by auto
qed

lemma finite_sum_mpoly_commute:
  "finite S \<Longrightarrow> (\<Sum>m\<in>S. MPoly (f m)) = MPoly (\<Sum>m\<in>S. f m)"
  by (simp add: add_to_finite_sum plus_mpoly.abs_eq zero_mpoly_def)

lemma finite_prod_mpoly_commute:
  "finite S \<Longrightarrow> (\<Prod>m\<in>S. MPoly (f m)) = MPoly (\<Prod>m\<in>S. f m)"
  by (simp add: mult_to_finite_prod one_mpoly_def times_mpoly.abs_eq)

lemma power_mpoly_commute: "MPoly a ^ p = MPoly (a ^ p)"
  by (transfer; auto)

lemma finite_sum_poly_mapping_commute :
"finite S \<Longrightarrow> (\<And>m. finite {x. f m x\<noteq>0}) \<Longrightarrow>
(\<Sum>m\<in>S. Abs_poly_mapping (f m)) = Abs_poly_mapping (\<lambda>x. \<Sum>m\<in>S. f m x)"
proof (induction "card S" arbitrary:S)
  case 0
  then show ?case by force
next
  case (Suc n)
  then obtain y where y_prop: "y\<in>S" by fastforce
  define S' where "S' = S - {y}"
  hence card_S':"card S' = n" using Suc by (simp add: y_prop)
  hence IH: "(\<Sum>m\<in>S'. Abs_poly_mapping (f m)) = Abs_poly_mapping (\<lambda>x. \<Sum>m\<in>S'. f m x)"
    using Suc by force
  have sum_disj: "(\<Sum>m\<in>S'. f m x) + f y x = (\<Sum>m\<in>S. f m x)" for x using S'_def
    by (metis Suc.prems(1) add.commute sum.remove y_prop)
  have "finite S'" by (simp add: S'_def Suc.prems(1))
  hence "(\<forall>m\<in>S'. f m x = 0) \<Longrightarrow> (\<Sum>m\<in>S'. f m x) = 0" for x by simp
  hence "{x. (\<Sum>m\<in>S'. f m x) \<noteq> 0} \<subseteq> (\<Union>m\<in>S'. {x. f m x \<noteq> 0})"
    by (smt (verit, best) UN_I mem_Collect_eq subsetI)
  hence fin_sum: "finite {x. (\<Sum>m\<in>S'. f m x) \<noteq> 0}" using Suc(4) \<open>finite S'\<close> finite_subset by blast
  have "(\<Sum>m\<in>S. Abs_poly_mapping (f m)) = (\<Sum>m\<in>S'. Abs_poly_mapping (f m)) + Abs_poly_mapping (f y)"
    using S'_def by (metis Suc.prems(1) add.commute sum.remove y_prop)
  also have "... = Abs_poly_mapping (\<lambda>x. \<Sum>m\<in>S'. f m x) + Abs_poly_mapping (f y)" using IH by argo
  also have "... = Abs_poly_mapping (\<lambda>x. (\<Sum>m\<in>S'. f m x) + f y x)"
    unfolding plus_poly_mapping_def apply simp
    using lookup_Abs_poly_mapping fin_sum Suc(4)[of y] by force
  also have "... = Abs_poly_mapping (\<lambda>x. (\<Sum>m\<in>S. f m x))" using sum_disj by presburger
  finally show ?case by blast
qed

lemma coeff_sum_monom:
  assumes "finite {m. f m\<noteq>0}"
  shows "coeff (Sum_any (\<lambda>m. monom m (f m))) = f"
proof -
  define S where "S = {m. f m\<noteq>0}"
  have fin_S: "finite S" unfolding S_def using assms by simp
  have "Sum_any (\<lambda>m. monom m (f m)) = Sum_any (\<lambda>m. MPoly (Poly_Mapping.single m (f m)))"
    unfolding monom_def by simp
  also have "... = (\<Sum>m\<in>S. MPoly (Poly_Mapping.single m (f m)))"
    unfolding S_def                   
    by (metis (mono_tags, lifting) Collect_mono Sum_any.expand_superset assms single_zero zero_mpoly_def)
  also have "... = MPoly (\<Sum>m\<in>S. (Poly_Mapping.single m (f m)))"
    using finite_sum_mpoly_commute fin_S by fastforce
  finally have 0: "Sum_any (\<lambda>m. monom m (f m)) = (MPoly (\<Sum>a\<in>S. (Poly_Mapping.single a (f a))))"
    by simp

  have 1:"(\<Sum>a\<in>S. (Poly_Mapping.single a (f a))) = Abs_poly_mapping (\<lambda>m. \<Sum>a\<in>S. f a when a = m)"
    unfolding single_def apply simp
    using finite_sum_poly_mapping_commute[of S "(\<lambda>a. (\<lambda>k'. f a when a = k'))"] fin_S by fastforce
  have "(\<Sum>a\<in>S. f a when a = m) = f m" for m
  proof (cases "m\<in>S")
    case True
    hence "finite S \<and> S = (S-{m})\<union>{m} \<and> (S-{m})\<inter>{m}={}" using fin_S by blast
    hence "(\<Sum>a\<in>S. f a when a = m) = (\<Sum>a\<in>(S-{m}). f a when a = m) + (\<Sum>a\<in>{m}. f a when a = m)"
      by (meson True bot.extremum insert_subset sum.subset_diff)
    also have "... = f m" by auto
    finally show ?thesis using \<open>m\<in>S\<close> by presburger
  next
    case False
    hence "a\<in>S \<Longrightarrow> (f a when a = m) = 0" for a unfolding when_def by force
    hence "(\<Sum>a\<in>S. f a when a = m) = 0" by simp
    then show ?thesis using \<open>m\<notin>S\<close> S_def by force
  qed
  hence "(\<Sum>a\<in>S. (Poly_Mapping.single a (f a))) = Abs_poly_mapping f"
    using 1 by force
  hence "coeff (Sum_any (\<lambda>m. monom m (f m))) = lookup (mapping_of (MPoly (Abs_poly_mapping f)))"
    using 0 coeff_def by force
  thus ?thesis using MPoly_inverse UNIV_I lookup_Abs_poly_mapping[of f] assms by metis
qed

lemma coeff_sum_monom_bis:
  assumes "finite {m. f m\<noteq>0}" and "finite S"
  shows "coeff (\<Sum>m\<in>S. monom m (f m)) m'= (if m'\<in> S then f m' else 0)"
proof -
  define g where "g = (\<lambda>m. if m\<in>S then f m else 0)"
  hence "{m. g m \<noteq> 0} \<subseteq> {m. f m \<noteq> 0}" by auto
  hence fin_g: "finite {m. g m \<noteq> 0}" using assms finite_subset by blast
  hence "(\<Sum>m\<in>S. monom m (f m)) = Sum_any (\<lambda>m. monom m (g m))" using assms(2)
    by (smt (verit, best) Sum_any.conditionalize Sum_any.cong g_def monom.abs_eq monom_zero 
        single_zero)
  hence "coeff (\<Sum>m\<in>S. monom m (f m)) m' = coeff (Sum_any (\<lambda>m. monom m (g m))) m'" by simp
  also have "... = g m'" using fin_g coeff_sum_monom by fastforce
  finally show ?thesis unfolding g_def by blast
qed


lemma cst_poly_times_monom: "MPoly (Const\<^sub>0 (a::('a::semiring_1))) * monom m b = monom m (a*b)"
proof -
  have "MPoly (Const\<^sub>0 a) * monom m b = monom 0 a * monom m b"
    using Const\<^sub>0_def by (metis monom.abs_eq)
  also have "... = monom m (a*b)"
    using mult_monom[of 0 a m b] by simp
  finally show ?thesis by simp
qed

lemma cst_poly_times_monom_one: "MPoly (Const\<^sub>0 (a::('a::semiring_1))) * monom m 1 = monom m a"
  using cst_poly_times_monom[of a m 1] by simp

lemma poly_eq_sum_monom: "P = Sum_any (\<lambda>m. monom m (coeff P m))"
proof -
  have "\<And>m'. coeff P m' = coeff (Sum_any (\<lambda>m. monom m (coeff P m))) m'"
    using coeff_sum_monom coeff_def
    by (metis (full_types) finite_lookup)
  thus ?thesis using coeff_eq by blast
qed

lemma poly_eq_sum_monom_alt: "P = (\<Sum>m\<in>(keys (mapping_of P)). monom m (coeff P m))"
  using poly_eq_sum_monom[of P]
  by (smt (verit) Sum_any.conditionalize Sum_any.cong coeff_keys finite_keys monom.abs_eq monom_zero single_zero)

lemma coeff_sum:
  fixes P::"_ \<Rightarrow> 'a::comm_monoid_add mpoly"
  assumes S_fin: "finite S"
  shows "coeff (sum P S) m = (\<Sum>i\<in>S. coeff (P i) m)"
proof (induct rule: finite_induct[OF S_fin])
  case 1 thus ?case by (simp add: coeff_def zero_mpoly.rep_eq)
next
  case (2 x S)
  have "coeff (sum P (insert x S)) m = coeff (sum P S + P x) m"
    by (simp add: "2.hyps"(1) "2.hyps"(2) add.commute)
  also have "... = coeff (sum P S) m + coeff (P x) m"
    by (simp add: coeff_add)
  also have "... = (\<Sum>i\<in>S. coeff (P i) m) + coeff (P x) m"
    by (simp add: "2")
  finally show ?case
    by (simp add: "2.hyps"(1) "2.hyps"(2) add.commute)
qed

lemma coeff_var_power_le:
  "j \<le> i \<Longrightarrow> MPoly_Type.coeff (Var v ^ j * P) (Poly_Mapping.single v i)
             = MPoly_Type.coeff P (Poly_Mapping.single v (i - j))"
proof -
  assume "j \<le> i"
  then have eqi: "i = j + (i - j)"
    by auto

  show ?thesis
    apply (subst eqi)
    unfolding Var.abs_eq monom_eq_power_var[symmetric] Poly_Mapping.single_add
      Poly_Mapping.single.abs_eq[symmetric]
    apply (subst More_MPoly_Type.coeff_monom_mult)
    by simp
qed

lemma coeff_var_power_eq: "MPoly_Type.coeff (Var v ^ i) (Poly_Mapping.single v i) = 1"
  using coeff_var_power_le[of i i v 1]
  unfolding insertion_trivial[symmetric] MPoly_Type.coeff_def one_mpoly.rep_eq
  by auto

lemma coeff_const: "i > 0 \<Longrightarrow> MPoly_Type.coeff (Const c) (Poly_Mapping.single v i) = 0"
  unfolding MPoly_Type.coeff_def Const.rep_eq Const\<^sub>0_def lookup_single
  unfolding single_zero[of v, symmetric]
  apply (rule "when"(2))
  by (metis lookup_single_eq nat_less_le)

lemma mpoly_univariate_expansion:
  fixes P::"'a::comm_semiring_1 mpoly" and v::nat
  assumes univariate: "vars P \<subseteq> {v}"
  shows "P = Sum_any (\<lambda>i. monom (Poly_Mapping.single v i) (coeff P (Poly_Mapping.single v i)))"
proof -
  define K where "K = keys (mapping_of P)"
  define f where "f = (\<lambda>m::nat\<Rightarrow>\<^sub>0nat. lookup m v)"

  have rewrite_monom: "m\<in>K \<Longrightarrow> m = Poly_Mapping.single v (f m)" for m
  proof -
    assume "m\<in>K" 
    hence "keys m \<subseteq> vars P" 
      unfolding vars_def K_def by auto
    hence "keys m \<subseteq> {v}" 
      using univariate by auto
    thus ?thesis 
      unfolding f_def
      by (metis diff_shunt_var keys_eq_empty lookup_single_eq remove_key_keys 
          remove_key_single remove_key_sum)
  qed

  have f_inj: "inj_on f K" 
    using rewrite_monom by (metis inj_onI) 

  have coeff_null: "i \<notin> f ` K \<Longrightarrow> 
    monom (Poly_Mapping.single v i) (coeff P (Poly_Mapping.single v i)) = 0" for i
  proof -
    assume "i \<notin> f ` K"
    hence "Poly_Mapping.single v i \<notin> K" 
      unfolding f_def by force
    hence "coeff P (Poly_Mapping.single v i) = 0" 
      unfolding K_def coeff_def by (simp add: in_keys_iff)
    thus ?thesis by (metis mult_zero_left smult_0 smult_monom)
  qed

  have "P = (\<Sum>m\<in>K. monom m (coeff P m))"
    by (simp add: K_def poly_eq_sum_monom_alt)
  also have "... = (\<Sum>m\<in>K. monom (Poly_Mapping.single v (f m)) (coeff P (Poly_Mapping.single v (f m))))"
    using rewrite_monom by simp
  also have "... = (\<Sum>i\<in>f ` K. monom (Poly_Mapping.single v i) (coeff P (Poly_Mapping.single v i)))"
    by (metis (mono_tags, lifting) f_inj sum.reindex_cong)
  also have "... = Sum_any (\<lambda>i. monom (Poly_Mapping.single v i) (coeff P (Poly_Mapping.single v i)))"
    using coeff_null
    by (smt (verit) K_def Sum_any.conditionalize Sum_any.cong finite_imageI finite_keys)
  finally show ?thesis .
qed


lemma term_expansion_lemma_1: "i \<noteq> [] \<Longrightarrow>
  Poly_Mapping.single (Abs_poly_mapping ((!\<^sub>0) i)) (1 :: 'a::comm_semiring_1) =
  (\<Prod>s = 0..(length i - 1). Var\<^sub>0 s ^ (i ! s))"
proof (induction i rule: length_induct)
  case (1 i)
  show ?case proof (cases i rule: rev_exhaust)
    case Nil
    thus ?thesis using 1 by auto
  next
    case (snoc i' x)
    show ?thesis proof cases
      assume i'_def: "i' = []"
      have "Poly_Mapping.single (Abs_poly_mapping ((!\<^sub>0) [x])) 1 = Var\<^sub>0 0 ^ x"
        unfolding MPoly_Type.Var\<^sub>0_power by auto
      thus ?thesis unfolding snoc i'_def by auto
    next
      assume i'_non_empty: "i' \<noteq> []"
      have "(\<Prod>s = 0..length i'. Var\<^sub>0 s ^ ((i' @ [x]) ! s)) =
        Poly_Mapping.single (Abs_poly_mapping ((!\<^sub>0) (i' @ [x]))) (1 :: 'a)" proof -
        have "(\<Prod>s = 0..length i'. Var\<^sub>0 s ^ ((i' @ [x]) ! s)) =
          (\<Prod>s = 0..Suc (length i' - 1). Var\<^sub>0 s ^ ((i' @ [x]) ! s))"
          using i'_non_empty by auto
        also have "... = (\<Prod>s = 0..length i' - 1. Var\<^sub>0 s ^ ((i' @ [x]) ! s)) *
          Var\<^sub>0 (Suc (length i' - 1)) ^ ((i' @ [x]) ! (Suc (length i' - 1)))"
          using prod.atLeast0_atMost_Suc by auto
        also have "... = (\<Prod>s = 0..length i' - 1. Var\<^sub>0 s ^ ((i' @ [x]) ! s)) *
          Var\<^sub>0 (length i') ^ ((i' @ [x]) ! (length i'))"
          using i'_non_empty by auto
        also have "... = (\<Prod>s = 0..length i' - 1. Var\<^sub>0 s ^ ((i' @ [x]) ! s)) *
          Var\<^sub>0 (length i') ^ x" by auto
        also have "... = (\<Prod>s = 0..length i' - 1. Var\<^sub>0 s ^ (i' ! s)) *
          Var\<^sub>0 (length i') ^ x"
          by (auto simp add: List.nth_append i'_non_empty order_le_less_trans)
        also have "... = Poly_Mapping.single (Abs_poly_mapping ((!\<^sub>0) i'))
          (1 :: 'a) * Var\<^sub>0 (length i') ^ x" using 1 snoc i'_non_empty by auto
        also have "... = Poly_Mapping.single (Abs_poly_mapping ((!\<^sub>0) i')) 1 *
          Poly_Mapping.single (Poly_Mapping.single (length i') x) 1"
          unfolding MPoly_Type.Var\<^sub>0_power by simp
        also have "... = Poly_Mapping.single (Abs_poly_mapping ((!\<^sub>0) i))
          (1 :: 'a)" proof -
          have "Abs_poly_mapping ((!\<^sub>0) i') + Poly_Mapping.single (length i') x =
            Abs_poly_mapping ((!\<^sub>0) i)" unfolding snoc by auto
          thus ?thesis by (simp add: Poly_Mapping.mult_single)
        qed
        finally show ?thesis unfolding snoc .
      qed
      thus ?thesis unfolding snoc by auto
    qed
  qed
qed

lemma term_expansion_lemma_2: "i \<noteq> [] \<Longrightarrow>
  monom (Abs_poly_mapping ((!\<^sub>0) i)) c =
  MPoly (Const\<^sub>0 c) * MPoly (\<Prod>s = 0..length i - 1. Var\<^sub>0 s ^ (i ! s))"
  unfolding term_expansion_lemma_1[symmetric] monom.abs_eq[symmetric]
    cst_poly_times_monom_one by simp

lemma term_expansion: "i \<noteq> [] \<Longrightarrow>
  monom (Abs_poly_mapping ((!\<^sub>0) i)) c =
  Const c * (\<Prod>s = 0..length i - 1. Var s ^ (i ! s))"
  unfolding MPoly_Type.Const.abs_eq MPoly_Type.Var.abs_eq term_expansion_lemma_2
  by (simp add: finite_prod_mpoly_commute power_mpoly_commute)

fun sample_prefix :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "sample_prefix 0 f = []" |
  "sample_prefix (Suc l) f = sample_prefix l f @ [f l]"

lemma sample_prefix_length[simp]: "length (sample_prefix l f) = l"
  by (induction l; auto)

lemma sample_prefix_cong:
  "(\<forall>x<n. f x = g x) \<Longrightarrow> sample_prefix n f = sample_prefix n g"
proof -
  assume "\<forall>x<n. f x = g x"
  hence "l \<le> n \<Longrightarrow> sample_prefix l f = sample_prefix l g" for l
    by (induction l; auto)
  thus ?thesis by auto
qed

lemma sample_prefix_inv_nth0: "(\<forall>i\<ge>n. f i = 0) \<Longrightarrow> f = (!\<^sub>0) (sample_prefix n f)"
proof (induction n arbitrary: f)
  case 0
  thus ?case unfolding nth0_def by simp
next
  case (Suc n)
  let ?g = "\<lambda>x. f x when x < n"
  have "?g = (!\<^sub>0) (sample_prefix n ?g)" using Suc by auto
  also have "... = (!\<^sub>0) (sample_prefix n f)"
    using sample_prefix_cong[of n f ?g] by auto
  finally have 0: "?g = (!\<^sub>0) (sample_prefix n f)" .
  have "f = (\<lambda>x. if x = n then f n else ?g x)" unfolding when_def using Suc by auto
  also have "... = (\<lambda>x. if x = n then f n else (!\<^sub>0) (sample_prefix n f) x)"
    unfolding 0[symmetric] by simp
  also have "... = (!\<^sub>0) (sample_prefix (Suc n) f)"
    apply (rule ext)
    subgoal for x
      apply (cases "x = n")
      unfolding nth0_def apply simp_all
      unfolding List.nth_append apply simp_all
      done
    done
  finally show ?case .
qed

lemma sample_prefix_inj:
  "inj_on (\<lambda>f. sample_prefix n f) {f. \<forall>i\<ge>n. (f i :: 'a::zero) = 0}"
proof
  fix g h
  assume "g \<in> {f. \<forall>i\<ge>n. (f i :: 'a::zero) = 0}"
  hence 0: "\<forall>i\<ge>n. g i = 0" by auto
  assume "h \<in> {f. \<forall>i\<ge>n. (f i :: 'a::zero) = 0}"
  hence 1: "\<forall>i\<ge>n. h i = 0" by auto
  assume "sample_prefix n g = sample_prefix n h"
  hence "(!\<^sub>0) (sample_prefix n g) = (!\<^sub>0) (sample_prefix n h)" by auto
  thus "g = h" using 0 1 by (simp add: sample_prefix_inv_nth0[symmetric])
qed

lemma lookup_nth0_total_degree:
  "lookup (mapping_of P) (Abs_poly_mapping ((!\<^sub>0) i)) \<noteq> 0 \<Longrightarrow>
  sum_list i \<le> total_degree P"
  apply transfer
  apply (rule Max_ge)
  subgoal for P i
    apply simp
    done
  subgoal for P i
    unfolding image_def keys_def apply simp
    using nth0_sum_list[of i] apply auto
    done
  done

lemma prod_monom: "finite S \<Longrightarrow> prod (\<lambda>s. monom (x s) (a s)) S = monom (sum x S) (prod a S)"
proof (induction "card S" arbitrary:S)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain y where y_prop: "y\<in>S" by fastforce
  define S' where "S' = S - {y}"
  with Suc(3) have "finite S'" by auto
  from S'_def have card_S': "card S' = n" using Suc by (simp add: y_prop)
  have disj_un_S: "S = S'\<union>{y} \<and> S'\<inter>{y}={}\<and>finite S" using y_prop S'_def Suc by force
  hence "(\<Prod>s\<in>S. monom (x s) (a s)) = (\<Prod>s\<in>S'. monom (x s) (a s)) * (\<Prod>s\<in>{y}. monom (x s) (a s))"
    by (meson finite_Un prod.union_disjoint)
  also have "... = monom (sum x S') (prod a S') * monom (x y) (a y)"
    using Suc(1)[of "S'"] card_S' \<open>finite S'\<close> by auto
  also have "... = monom (sum x S' + x y) (prod a S' * a y)"
    using mult_monom by auto
  finally show "(\<Prod>s\<in>S. monom (x s) (a s)) = monom (sum x S) (prod a S)"
    using S'_def Suc
    by (smt (verit, ccfv_threshold) add.commute mult.commute prod.remove sum.remove y_prop)
qed

lemma poly_mapping_expansion: "x = (\<Sum>s\<in>keys x. Abs_poly_mapping (\<lambda>v'. lookup x s when s = v'))"
proof - 
  have h0: "(\<Sum>xa\<in>keys x. lookup (Abs_poly_mapping (\<lambda>v'. lookup x xa when xa = v')) i)
         = (\<Sum>xa\<in>keys x. (\<lambda>v'. lookup x xa when xa = v') i)" for i
    by (rule sum.cong, auto)
  define x_fun where "x_fun \<equiv> lookup x"
  have h1: "lookup x i = (\<Sum>xa\<in>keys x. lookup x xa when xa = i)" for i
    apply (cases "i \<in> keys x", simp add: sum.remove[OF finite_keys])
    unfolding keys.rep_eq x_fun_def[symmetric]
    by (smt (verit, ccfv_SIG) mem_Collect_eq sum.neutral when_simps(2))

  thus ?thesis
    unfolding lookup_inject[symmetric] lookup_sum h0 by blast
qed

lemma monom_expansion:
  shows "monom x c = Const c * (\<Prod>s\<in>keys x. Var s ^ (lookup x s))"
  unfolding Var.abs_eq monom_eq_power_var[symmetric]
  apply (subst prod_monom[OF finite_keys, where ?a = "\<lambda>_. 1"])
  apply (simp add: Const.abs_eq cst_poly_times_monom)
  by (subst poly_mapping_expansion) simp

lemma monom_expansion':
  fixes P :: "'a::{ring_no_zero_divisors,comm_semiring_1} mpoly"
  assumes "x \<in> keys (mapping_of P)"
  shows "monom x (coeff P x) = Const (coeff P x) * (\<Prod>s = 0..max_vars P. Var s ^ (lookup x s))"
proof (cases "vars P = {}")
  case True
  then show ?thesis 
    by (metis (no_types, lifting) Poly_Expansions.coeff_monom assms
        atLeastAtMost_singleton coeff_keys empty_iff finite.emptyI keys_zero
        lookup_zero max_vars_Const monom_expansion mult.commute mult_1 power_0
        prod.empty prod.insert vars_empty)
next
  case False
  then show ?thesis 
  unfolding max_vars_of_nonempty[OF False]
  apply (subst monom_expansion)
  apply (subst mult_cancel_left, rule disjI2)
  apply (rule prod.mono_neutral_cong_left)
  using assms apply simp_all
  subgoal 
    by (metis Max_ge UN_I atLeastAtMost_iff le0 subsetI vars_def
        vars_finite)
  subgoal
    by (simp add: in_keys_iff)
  done
qed

lemma mpoly_multivariate_expansion':
  fixes P::"'a::{ring_no_zero_divisors,comm_semiring_1} mpoly"
  shows "P = (\<Sum>m\<in>keys (mapping_of P). 
                  Const (coeff P m) * (\<Prod>s = 0..max_vars P. (Var s) ^ (lookup m s)))"
  apply (subst poly_eq_sum_monom_alt)
  by (rule sum.cong, simp_all add: monom_expansion')

lemma mpoly_multivariate_expansion:
  fixes P::"'a::comm_semiring_1 mpoly"
  shows "P = (\<Sum>i | length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P. 
    Const (coeff P (Abs_poly_mapping ((!\<^sub>0) i))) *
    (\<Prod>s = 0..max_vars P. (Var s) ^ (i ! s)))"
proof -
  let ?t = "\<lambda>m. (sample_prefix (max_vars P + 1) (lookup m))"
  have "P = (\<Sum>m\<in>keys (mapping_of P). monom m (coeff P m))"
    by (rule poly_eq_sum_monom_alt)
  also have "... = (\<Sum>m | lookup (mapping_of P) m \<noteq> 0. monom m (coeff P m))"
    unfolding Poly_Mapping.in_keys_iff[symmetric] by auto
  also have "... = (\<Sum>m | lookup (mapping_of P) m \<noteq> 0.
    monom (Abs_poly_mapping (lookup m)) (coeff P (Abs_poly_mapping (lookup m))))"
    by auto
  also have "... = (\<Sum>i | length i = max_vars P + 1 \<and>
    lookup (mapping_of P) (Abs_poly_mapping ((!\<^sub>0) i)) \<noteq> 0.
    monom (Abs_poly_mapping ((!\<^sub>0) i)) (coeff P (Abs_poly_mapping ((!\<^sub>0) i))))"
  proof (rule sum.reindex_cong[symmetric, of ?t])
    let ?S = "{m. lookup (mapping_of P) m \<noteq> 0}"
    let ?T = "{i. length i = max_vars P + 1 \<and>
      lookup (mapping_of P) (Abs_poly_mapping ((!\<^sub>0) i)) \<noteq> 0}"
    show "inj_on ?t ?S" 
      proof
        fix m1 m2
        assume "m1 \<in> {m. lookup (mapping_of P) m \<noteq> 0}"
        hence 1: "\<forall>v\<ge>(max_vars P + 1). lookup m1 v = 0" using after_max_vars by auto
        assume "m2 \<in> {m. lookup (mapping_of P) m \<noteq> 0}"
        hence 2: "\<forall>v\<ge>(max_vars P + 1). lookup m2 v = 0" using after_max_vars by auto
        assume "sample_prefix (max_vars P + 1) (lookup m1) =
          sample_prefix (max_vars P + 1) (lookup m2)"
        hence "lookup m1 = lookup m2"
          using sample_prefix_inj[of "max_vars P + 1"] 1 2
          unfolding inj_on_def by blast
        thus "m1 = m2" by auto
      qed
    show "?T = ?t ` ?S" 
    proof (rule set_eqI; rule iffI)
      fix i
      assume 3: "i \<in> ?T"
      let ?m = "Abs_poly_mapping ((!\<^sub>0) i)"
      from 3 have 4: "lookup (mapping_of P) ?m \<noteq> 0" by auto
      have "lookup ?m = (!\<^sub>0) (sample_prefix (max_vars P + 1) (lookup ?m))"
        apply (rule sample_prefix_inv_nth0)
        using after_max_vars[of P ?m] 4 by auto
      hence "(!\<^sub>0) i = (!\<^sub>0) (sample_prefix (max_vars P + 1) (lookup ?m))" by auto
      hence 5: "i = (sample_prefix (max_vars P + 1) (lookup ?m))"
        using nth0_inj[of i] 3 by auto
      from 4 5 have "\<exists>m. lookup (mapping_of P) m \<noteq> 0 \<and>
        i = sample_prefix (max_vars P + 1) (lookup m)" by blast
      thus "i \<in> ?t ` ?S" unfolding image_def by auto
    next
      fix i
      assume "i \<in> ?t ` ?S"
      then obtain m where 6: "lookup (mapping_of P) m \<noteq> 0"
        "i = sample_prefix (max_vars P + 1) (lookup m)" by blast
      have 7: "length i = max_vars P + 1" using 6 by auto
      have "lookup m = (!\<^sub>0) (sample_prefix (max_vars P + 1) (lookup m))"
        apply (rule sample_prefix_inv_nth0)
        using after_max_vars[of P m] 6 apply auto
        done
      hence 8: "lookup (mapping_of P) (Abs_poly_mapping ((!\<^sub>0) i)) \<noteq> 0"
        using 6 by auto
      from 7 8 show "i \<in> ?T" by blast
    qed
    show "m \<in> ?S \<Longrightarrow>
      monom (Abs_poly_mapping ((!\<^sub>0) (?t m)))
        (coeff P (Abs_poly_mapping ((!\<^sub>0) (?t m)))) =
      monom (Abs_poly_mapping (lookup m))
        (coeff P (Abs_poly_mapping (lookup m)))" for m
    proof -
      assume 9: "m \<in> ?S"
      have "lookup m = (!\<^sub>0) (sample_prefix (max_vars P + 1) (lookup m))"
        apply (rule sample_prefix_inv_nth0)
        using after_max_vars[of P m] 9 apply auto
        done
      thus ?thesis by auto
    qed
  qed
  also have "... = (\<Sum>i | length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P.
    monom (Abs_poly_mapping ((!\<^sub>0) i)) (coeff P (Abs_poly_mapping ((!\<^sub>0) i))))"
  proof (rule sum.mono_neutral_left)
    let ?A = "{i. length i = max_vars P + 1 \<and>
     lookup (mapping_of P) (Abs_poly_mapping ((!\<^sub>0) i)) \<noteq> 0}"
    let ?B = "{i. length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P}"
    have "?B \<subseteq> {i. set i \<subseteq> {0..total_degree P} \<and> length i = max_vars P + 1}"
      using member_le_sum_list by fastforce
    also have "finite ..."  using List.finite_lists_length_eq by auto
    ultimately show "finite ?B" using Finite_Set.finite_subset by auto
    show "?A \<subseteq> ?B" using lookup_nth0_total_degree by auto
    show "\<forall>i\<in>?B - ?A. monom (Abs_poly_mapping ((!\<^sub>0) i))
      (coeff P (Abs_poly_mapping ((!\<^sub>0) i))) = 0"
      by (simp add: coeff_all_0 coeff_def)
  qed
  also have "... = (\<Sum>i | length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P.
    Const (coeff P (Abs_poly_mapping ((!\<^sub>0) i))) *
    (\<Prod>s = 0..max_vars P. (Var s) ^ (i ! s)))"
  proof (rule sum.cong[OF refl])
    fix i
    assume i_porp:
      "i \<in> {i. length i = max_vars P + 1 \<and> sum_list i \<le> total_degree P}"
    hence "i \<noteq> []" "length i - 1 = max_vars P" by auto
    thus "monom (Abs_poly_mapping ((!\<^sub>0) i)) (coeff P (Abs_poly_mapping ((!\<^sub>0) i))) =
      Const (coeff P (Abs_poly_mapping ((!\<^sub>0) i))) *
      (\<Prod>s = 0..max_vars P. Var s ^ i ! s)"
      by (simp add: term_expansion)
  qed
  finally show ?thesis .
qed


lemma mpoly_univariate_expansion_sum:
  fixes P :: "('a::comm_ring_1) mpoly"
  assumes "vars P \<subseteq> {v}"
  defines "q \<equiv> MPoly_Type.degree P v"
  defines "coeff_P \<equiv> (\<lambda>d. coeff P (Poly_Mapping.single v d))"
  shows "P = (\<Sum>d = 0..q. Const (coeff_P d) * (Var v) ^ d)"
  unfolding coeff_P_def
  apply (subst mpoly_univariate_expansion[of P v, OF assms(1)])
  unfolding monom_single
  unfolding Sum_any.expand_set
  apply (rule sum.mono_neutral_cong_left)
  subgoal by auto
  subgoal unfolding q_def degree.rep_eq
  proof -
    have "Const (coeff P (Poly_Mapping.single v p)) * Var v ^ p \<noteq> 0 \<Longrightarrow>
      p \<in> {0..Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P)))}" for p
    proof -
      assume "Const (coeff P (Poly_Mapping.single v p)) * Var v ^ p \<noteq> 0"
      hence "coeff P (Poly_Mapping.single v p) \<noteq> 0"
        by (metis Const_zero lambda_zero)
      hence "p \<in> (\<lambda>m. lookup m v) ` keys (mapping_of P)"
        by (metis coeff_def imageI in_keys_iff lookup_single_eq)
      thus "p \<in> {0..Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P)))}"
        by simp
    qed
    thus "{a. Const (coeff P (Poly_Mapping.single v a)) * Var v ^ a \<noteq> 0}
      \<subseteq> {0..Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P)))}"
      by blast
  qed
  subgoal by auto
  subgoal by auto
  done

end