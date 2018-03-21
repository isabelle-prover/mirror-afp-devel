(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Gram-Schmidt\<close>

theory Gram_Schmidt_2
  imports Jordan_Normal_Form.Gram_Schmidt
    Jordan_Normal_Form.Show_Matrix
    Jordan_Normal_Form.Matrix_Impl
    Norms
begin

(* TODO: unify *)
no_notation Gram_Schmidt.cscalar_prod (infix "\<bullet>c" 70)

lemma vec_conjugate_connect[simp]: "Gram_Schmidt.vec_conjugate = conjugate"
  by (auto simp: vec_conjugate_def conjugate_vec_def)

lemma scalar_prod_ge_0: "(x :: 'a :: linordered_idom vec) \<bullet> x \<ge> 0" 
  unfolding scalar_prod_def
  by (rule sum_nonneg, auto)

class trivial_conjugatable_ordered_field = 
  conjugatable_ordered_field + linordered_idom +
  assumes conjugate_id [simp]: "conjugate x = x"

lemma cscalar_prod_is_scalar_prod[simp]: "(x :: 'a :: trivial_conjugatable_ordered_field vec) \<bullet>c y = x \<bullet> y"
  unfolding conjugate_id
  by (rule arg_cong[of _ _ "scalar_prod x"], auto)

lemma corthogonal_is_orthogonal[simp]: 
  "corthogonal (xs :: 'a :: trivial_conjugatable_ordered_field vec list) = orthogonal xs"
  unfolding corthogonal_def orthogonal_def by simp

instance rat :: trivial_conjugatable_ordered_field 
  by (standard, auto)

instance real :: trivial_conjugatable_ordered_field 
  by (standard, auto)

(* TODO: move *)
lemma vec_right_zero[simp]: 
  "(v :: 'a :: monoid_add vec) \<in> carrier_vec n  \<Longrightarrow> v + 0\<^sub>v n = v" 
  by auto

context vec_module begin

lemma sumlist_dim: assumes "\<And> x. x \<in> set xs \<Longrightarrow> x \<in> carrier_vec n"
  shows "dim_vec (sumlist xs) = n"
  using sumlist_carrier assms
  by fastforce
    
lemma sumlist_vec_index: assumes "\<And> x. x \<in> set xs \<Longrightarrow> x \<in> carrier_vec n"
  and "i < n" 
shows "sumlist xs $ i = sum_list (map (\<lambda> x. x $ i) xs)" 
  unfolding M.sumlist_def using assms(1) proof(induct xs)
  case (Cons a xs)
  hence cond:"\<And> x. x \<in> set xs \<Longrightarrow> x \<in> carrier_vec n" by auto
  from Cons(1)[OF cond] have IH:"foldr (+) xs (0\<^sub>v n) $ i = (\<Sum>x\<leftarrow>xs. x $ i)" by auto
  have "(a + foldr (+) xs (0\<^sub>v n)) $ i = a $ i + (\<Sum>x\<leftarrow>xs. x $ i)" 
    apply(subst index_add_vec) unfolding IH
    using sumlist_dim[OF cond,unfolded M.sumlist_def] assms by auto
  then show ?case by auto next
  case Nil thus ?case using assms by auto
qed
 
lemma scalar_prod_left_sum_distrib: 
  assumes vs: "\<And> v. v \<in> set vvs \<Longrightarrow> v \<in> carrier_vec n" and w: "w \<in> carrier_vec n" 
  shows "sumlist vvs \<bullet> w = sum_list (map (\<lambda> v. v \<bullet> w) vvs)"
  using vs
proof (induct vvs)
  case (Cons v vs)
  from Cons have v: "v \<in> carrier_vec n" and vs: "sumlist vs \<in> carrier_vec n" 
    by (auto intro!: sumlist_carrier)
  have "sumlist (v # vs) \<bullet> w = sumlist ([v] @ vs) \<bullet> w " by auto
  also have "\<dots> = (v + sumlist vs) \<bullet> w" 
    by (subst sumlist_append, insert Cons v vs, auto)
  also have "\<dots> = v \<bullet> w + (sumlist vs \<bullet> w)" 
    by (rule add_scalar_prod_distrib[OF v vs w])
  finally show ?case using Cons by auto
qed (insert w, auto)   

definition lattice_of :: "'a vec list \<Rightarrow> 'a vec set" where
  "lattice_of fs = range (\<lambda> c. sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs]))"

lemma in_latticeE: assumes "f \<in> lattice_of fs" obtains c where
    "f = sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])" 
  using assms unfolding lattice_of_def by auto
    
lemma in_latticeI: assumes "f = sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])" 
  shows "f \<in> lattice_of fs" 
  using assms unfolding lattice_of_def by auto
    
lemma basis_in_latticeI: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and f: "f \<in> set fs" 
shows "f \<in> lattice_of fs" 
proof -
  from f obtain i where f: "f = fs ! i" and i: "i < length fs" unfolding set_conv_nth by auto
  let ?c = "\<lambda> j. if j = i then 1 else 0" 
  have id: "[0 ..< length fs] = [0 ..< i] @ [i] @ [Suc i ..< length fs]"
    by (rule nth_equalityI, insert i, auto simp: nth_append, rename_tac k, case_tac "k = i", auto)
  from fs have fs[intro!]: "\<And> i. i < length fs \<Longrightarrow> fs ! i \<in> carrier_vec n" unfolding set_conv_nth by auto
  have [simp]: "\<And> i. i < length fs \<Longrightarrow> dim_vec (fs ! i) = n" using fs by auto
  show ?thesis unfolding f
    apply (rule in_latticeI[of _ ?c], unfold id map_append, insert i)
    apply (subst sumlist_append,force,force, subst sumlist_append, force, force)
    by (subst sumlist_neutral, force, subst sumlist_neutral, force, auto)
qed

lemma lattice_of_swap: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and ij: "i < length fs" "j < length fs" "i \<noteq> j" 
  and gs: "gs = fs[ i := fs ! j, j := fs ! i]" 
shows "lattice_of gs = lattice_of fs" 
proof -
  {
    fix i j and fs :: "'a vec list" 
    assume *: "i < j" "j < length fs" and fs: "set fs \<subseteq> carrier_vec n"
    let ?gs = "fs[ i := fs ! j, j := fs ! i]"
    let ?len = "[0..<i] @ [i] @ [Suc i..<j] @ [j] @ [Suc j..<length fs]" 
    have "[0 ..< length fs] = [0 ..< j] @ [j] @ [Suc j ..< length fs]" using *
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
          upt_conv_Cons zero_less_Suc)
    also have "[0 ..< j] = [0 ..< i] @ [i] @ [Suc i ..< j]" using *
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
          upt_conv_Cons zero_less_Suc)
    finally have len: "[0..<length fs] = ?len" by simp
    from fs have fs: "\<And> i. i < length fs \<Longrightarrow> fs ! i \<in> carrier_vec n" unfolding set_conv_nth by auto
    {
      fix f
      assume "f \<in> lattice_of fs" 
      from in_latticeE[OF this, unfolded len] obtain c where
        f: "f = sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs ! i) ?len)" by auto
      define sc where "sc = (\<lambda> xs. sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs ! i) xs))"
      define d where "d = (\<lambda> k. if k = i then c j else if k = j then c i else c k)"
      define sd where "sd = (\<lambda> xs. sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) xs))"
      have isc: "set is \<subseteq> {0 ..< length fs} \<Longrightarrow> sc is \<in> carrier_vec n" for "is" 
        unfolding sc_def by (intro sumlist_carrier, auto simp: fs)
      let ?a = "sc [0..<i]" let ?b = "sc [i]" let ?c = "sc [Suc i ..< j]" let ?d = "sc [j]" 
      let ?e = "sc [Suc j ..< length fs]" 
      let ?A = "sd [0..<i]" let ?B = "sd [i]" let ?C = "sd [Suc i ..< j]" let ?D = "sd [j]" 
      let ?E = "sd [Suc j ..< length fs]" 
      let ?CC = "carrier_vec n" 
      have ae: "?a \<in> ?CC" "?b \<in> ?CC" "?c \<in> ?CC" "?d \<in> ?CC" "?e \<in> ?CC"  
        using * by (auto intro: isc)
      have sc_sd: "{i,j} \<inter> set is \<subseteq> {} \<Longrightarrow> sc is = sd is" for "is" 
        unfolding sc_def sd_def by (rule arg_cong[of _ _ sumlist], rule map_cong, auto simp: d_def)
      have "f = ?a + (?b + (?c + (?d + ?e)))"         
        unfolding f map_append sc_def using fs *
        by ((subst sumlist_append, force, force)+, simp)
      also have "\<dots> = ?a + (?d + (?c + (?b + ?e)))" using * by auto
      also have "\<dots> = ?A + (?d + (?C + (?b + ?E)))" 
        using * by (auto simp: sc_sd)
      also have "?b = ?D" unfolding sd_def sc_def d_def using * by (auto simp: d_def)
      also have "?d = ?B" unfolding sd_def sc_def using * by (auto simp: d_def)    
      finally have "f = ?A + (?B + (?C + (?D + ?E)))" .
      also have "\<dots> = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) ?len)" 
        unfolding f map_append sd_def using fs *
        by ((subst sumlist_append, force, force)+, simp)
      also have "\<dots> = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) [0 ..< length ?gs])"
        unfolding len[symmetric] by simp
      finally have "f = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) [0 ..< length ?gs])" .
      from in_latticeI[OF this] have "f \<in> lattice_of ?gs" .
    }
    hence "lattice_of fs \<subseteq> lattice_of ?gs" by blast
  } note main = this
  {
    fix i j and fs :: "'a vec list" 
    assume *: "i < length fs" "j < length fs" "i \<noteq> j" and fs: "set fs \<subseteq> carrier_vec n"
    let ?gs = "fs[ i := fs ! j, j := fs ! i]"
    have "lattice_of fs \<subseteq> lattice_of ?gs" 
    proof (cases "i < j")
      case True
      from main[OF this *(2) fs] show ?thesis .
    next
      case False
      with *(3) have "j < i" by auto
      from main[OF this *(1) fs] 
      have "lattice_of fs \<subseteq> lattice_of (fs[j := fs ! i, i := fs ! j])" .
      also have "fs[j := fs ! i, i := fs ! j] = ?gs" using * 
        by (metis list_update_swap)
      finally show ?thesis .
    qed
  } note sub = this
  from sub[OF ij fs] 
  have one: "lattice_of fs \<subseteq> lattice_of gs" unfolding gs .
  have "lattice_of gs \<subseteq> lattice_of (gs[i := gs ! j, j := gs ! i])" 
    by (rule sub, insert ij fs, auto simp: gs)
  also have "gs[i := gs ! j, j := gs ! i] = fs" unfolding gs using ij 
    by (intro nth_equalityI, force, intro allI, 
      rename_tac k, case_tac "k = i", force, case_tac "k = j", auto)
  finally show ?thesis using one by auto
qed  
    
lemma lattice_of_add: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and ij: "i < length fs" "j < length fs" "i \<noteq> j" 
  and gs: "gs = fs[ i := fs ! i + of_int l \<cdot>\<^sub>v fs ! j]" 
shows "lattice_of gs = lattice_of fs" 
proof -
  {
    fix i j l and fs :: "'a vec list" 
    assume *: "i < j" "j < length fs" and fs: "set fs \<subseteq> carrier_vec n"
    note * = ij(1) *
    let ?gs = "fs[ i := fs ! i + of_int l \<cdot>\<^sub>v fs ! j]"
    let ?len = "[0..<i] @ [i] @ [Suc i..<j] @ [j] @ [Suc j..<length fs]" 
    have "[0 ..< length fs] = [0 ..< j] @ [j] @ [Suc j ..< length fs]" using *
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
          upt_conv_Cons zero_less_Suc)
    also have "[0 ..< j] = [0 ..< i] @ [i] @ [Suc i ..< j]" using *
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
          upt_conv_Cons zero_less_Suc)
    finally have len: "[0..<length fs] = ?len" by simp
    from fs have fs: "\<And> i. i < length fs \<Longrightarrow> fs ! i \<in> carrier_vec n" unfolding set_conv_nth by auto
    from fs have fsd: "\<And> i. i < length fs \<Longrightarrow> dim_vec (fs ! i) = n" by auto
    from fsd[of i] fsd[of j] * have fsd: "dim_vec (fs ! i) = n" "dim_vec (fs ! j) = n" by auto
    {
      fix f
      assume "f \<in> lattice_of fs" 
      from in_latticeE[OF this, unfolded len] obtain c where
        f: "f = sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs ! i) ?len)" by auto
      define sc where "sc = (\<lambda> xs. sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs ! i) xs))"
      define d where "d = (\<lambda> k. if k = j then c j - c i * l else c k)"
      define sd where "sd = (\<lambda> xs. sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) xs))"
      have isc: "set is \<subseteq> {0 ..< length fs} \<Longrightarrow> sc is \<in> carrier_vec n" for "is" 
        unfolding sc_def by (intro sumlist_carrier, auto simp: fs)
      have isd: "set is \<subseteq> {0 ..< length fs} \<Longrightarrow> sd is \<in> carrier_vec n" for "is" 
        unfolding sd_def using * by (intro sumlist_carrier, auto, rename_tac k,
        case_tac "k = i", auto simp: fs)
      let ?a = "sc [0..<i]" let ?b = "sc [i]" let ?c = "sc [Suc i ..< j]" let ?d = "sc [j]" 
      let ?e = "sc [Suc j ..< length fs]" 
      let ?A = "sd [0..<i]" let ?B = "sd [i]" let ?C = "sd [Suc i ..< j]" let ?D = "sd [j]" 
      let ?E = "sd [Suc j ..< length fs]" 
      let ?CC = "carrier_vec n" 
      have ae: "?a \<in> ?CC" "?b \<in> ?CC" "?c \<in> ?CC" "?d \<in> ?CC" "?e \<in> ?CC"  
        using * by (auto intro: isc)
      have AE: "?A \<in> ?CC" "?B \<in> ?CC" "?C \<in> ?CC" "?D \<in> ?CC" "?E \<in> ?CC"  
        using * by (auto intro: isd)
      have sc_sd: "{i,j} \<inter> set is \<subseteq> {} \<Longrightarrow> sc is = sd is" for "is" 
        unfolding sc_def sd_def by (rule arg_cong[of _ _ sumlist], rule map_cong, auto simp: d_def,
        rename_tac k, case_tac "i = k", auto)
      have "f = ?a + (?b + (?c + (?d + ?e)))"         
        unfolding f map_append sc_def using fs *
        by ((subst sumlist_append, force, force)+, simp)
      also have "\<dots> = ?a + ((?b + ?d) + (?c + ?e))" using ae by auto          
      also have "\<dots> = ?A + ((?b + ?d) + (?C + ?E))" 
        using * by (auto simp: sc_sd)
      also have "?b + ?d = ?B + ?D" unfolding sd_def sc_def d_def sumlist_def
        by (rule eq_vecI, insert * fsd, auto simp: algebra_simps)
      finally have "f = ?A + (?B + (?C + (?D + ?E)))" using AE by auto
      also have "\<dots> = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) ?len)" 
        unfolding f map_append sd_def using fs *
        by ((subst sumlist_append, force, force)+, simp)
      also have "\<dots> = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) [0 ..< length ?gs])"
        unfolding len[symmetric] by simp
      finally have "f = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) [0 ..< length ?gs])" .
      from in_latticeI[OF this] have "f \<in> lattice_of ?gs" .
    }
    hence "lattice_of fs \<subseteq> lattice_of ?gs" by blast
  } note main = this 
  {
    fix i j and fs :: "'a vec list" 
    assume *: "i < j" "j < length fs" and fs: "set fs \<subseteq> carrier_vec n"
    let ?gs = "fs[ i := fs ! i + of_int l \<cdot>\<^sub>v fs ! j]"
    define gs where "gs = ?gs" 
    from main[OF * fs, of l, folded gs_def]
    have one: "lattice_of fs \<subseteq> lattice_of gs" .
    have *: "i < j" "j < length gs" "set gs \<subseteq> carrier_vec n" using * fs unfolding gs_def set_conv_nth
      by (auto, rename_tac k, case_tac "k = i", (force intro!: add_carrier_vec)+)
    from fs have fs: "\<And> i. i < length fs \<Longrightarrow> fs ! i \<in> carrier_vec n" unfolding set_conv_nth by auto
    from fs have fsd: "\<And> i. i < length fs \<Longrightarrow> dim_vec (fs ! i) = n" by auto
    from fsd[of i] fsd[of j] * have fsd: "dim_vec (fs ! i) = n" "dim_vec (fs ! j) = n" by (auto simp: gs_def)
    from main[OF *, of "-l"]
    have "lattice_of gs \<subseteq> lattice_of (gs[i := gs ! i + of_int (- l) \<cdot>\<^sub>v gs ! j])" .
    also have "gs[i := gs ! i + of_int (- l) \<cdot>\<^sub>v gs ! j] = fs" unfolding gs_def
      by (rule nth_equalityI, auto, insert * fsd, rename_tac k, case_tac "k = i", auto)
    ultimately have "lattice_of fs = lattice_of ?gs" using one unfolding gs_def by auto
  } note main = this
  show ?thesis
  proof (cases "i < j")
    case True
    from main[OF this ij(2) fs] show ?thesis unfolding gs by simp
  next
    case False
    with ij have ji: "j < i" by auto
    define hs where "hs = fs[i := fs ! j, j := fs ! i]" 
    define ks where "ks = hs[j := hs ! j + of_int l \<cdot>\<^sub>v hs ! i]" 
    from ij fs have ij': "i < length hs" "set hs \<subseteq> carrier_vec n" unfolding hs_def by auto
    hence ij'': "set ks \<subseteq> carrier_vec n" "i < length ks" "j < length ks" "i \<noteq> j" 
      using ji unfolding ks_def set_conv_nth by (auto, rename_tac k, case_tac "k = i", 
        force, case_tac "k = j", (force intro!: add_carrier_vec)+)
    from lattice_of_swap[OF fs ij refl] 
    have "lattice_of fs = lattice_of hs" unfolding hs_def by auto
    also have "\<dots> = lattice_of ks" 
      using main[OF ji ij'] unfolding ks_def .
    also have "\<dots> = lattice_of (ks[i := ks ! j, j := ks ! i])" 
      by (rule sym, rule lattice_of_swap[OF ij'' refl])
    also have "ks[i := ks ! j, j := ks ! i] = gs" unfolding gs ks_def hs_def
      by (rule nth_equalityI, insert ij, auto, 
       rename_tac k, case_tac "k = i", force, case_tac "k = j", auto)
    finally show ?thesis by simp
  qed
qed

definition "orthogonal_complement W = {x. x \<in> carrier_vec n \<and> (\<forall>y \<in> W. x \<bullet> y = 0)}"

lemma orthogonal_complement_subset:
  assumes "A \<subseteq> B"
  shows "orthogonal_complement B \<subseteq> orthogonal_complement A"
unfolding orthogonal_complement_def using assms by auto

end

context vec_space
begin
sublocale vec_module _ n .


lemma in_orthogonal_complement_span[simp]:
  assumes [intro]:"S \<subseteq> carrier_vec n"
  shows "orthogonal_complement (span S) = orthogonal_complement S"
proof
  show "orthogonal_complement (span S) \<subseteq> orthogonal_complement S"
    by(fact orthogonal_complement_subset[OF in_own_span[OF assms]])
  {fix x :: "'a vec"
    fix a fix A :: "'a vec set"
    assume x [intro]:"x \<in> carrier_vec n" and f: "finite A" and S:"A \<subseteq> S"
    assume i0:"\<forall>y\<in>S. x \<bullet> y = 0"
    have "x \<bullet> lincomb a A = 0"
      unfolding comm_scalar_prod[OF x lincomb_closed[OF subset_trans[OF S assms]]]
    proof(insert S,atomize(full),rule finite_induct[OF f],goal_cases)
      case 1 thus ?case using assms x by force
    next
      case (2 f F)
      { assume i:"insert f F \<subseteq> S"
        hence F:"F \<subseteq> S" and f: "f \<in> S" by auto
        from F f assms
        have [intro]:"F \<subseteq> carrier_vec n"
          and fc[intro]:"f \<in> carrier_vec n"
          and [intro]:"x \<in> F \<Longrightarrow> x \<in> carrier_vec n" for x by auto
        have laf:"lincomb a F \<bullet> x = 0" using F 2 by auto
        have [simp]:"(\<Sum>u\<in>F. (a u \<cdot>\<^sub>v u) \<bullet> x) = 0"
          by(insert laf[unfolded lincomb_def],atomize(full),subst finsum_scalar_prod_sum) auto
        from f i0 have [simp]:"f \<bullet> x = 0" by (subst comm_scalar_prod) auto
        from lincomb_closed[OF subset_trans[OF i assms]]
        have "lincomb a (insert f F) \<bullet> x = 0" unfolding lincomb_def
          apply(subst finsum_scalar_prod_sum,force,force)
          using 2(1,2) smult_scalar_prod_distrib[OF fc x] by auto
      } thus ?case by auto
      qed
  }
  thus "orthogonal_complement S \<subseteq> orthogonal_complement (span S)"
    unfolding orthogonal_complement_def span_def by auto
qed

lemma lincomb_list_add_vec_2: assumes us: "set us \<subseteq> carrier_vec n" 
  and x: "x = lincomb_list lc (us [i := us ! i + c \<cdot>\<^sub>v us ! j])"
  and i: "j < length us" "i < length us" "i \<noteq> j" 
shows "x = lincomb_list (lc (j := lc j + lc i * c)) us" (is "_ = ?x")
proof -
  let ?xx = "lc j + lc i * c" 
  let ?i = "us ! i" 
  let ?j = "us ! j" 
  let ?v = "?i + c \<cdot>\<^sub>v ?j" 
  let ?ws = "us [i := us ! i + c \<cdot>\<^sub>v us ! j]"
  from us have usk: "k < length us \<Longrightarrow> us ! k \<in> carrier_vec n" for k by auto
  from usk i have ij: "?i \<in> carrier_vec n" "?j \<in> carrier_vec n" by auto
  hence v: "c \<cdot>\<^sub>v ?j \<in> carrier_vec n" "?v \<in> carrier_vec n" by auto
  with us have ws: "set ?ws \<subseteq> carrier_vec n" unfolding set_conv_nth using i 
    by (auto, rename_tac k, case_tac "k = i", auto)
  from us have us': "\<forall>w\<in>set us. dim_vec w = n" by auto 
  from ws have ws': "\<forall>w\<in>set ?ws. dim_vec w = n" by auto 
  have mset: "mset_set {0..<length us} = {#i#} + {#j#} + (mset_set ({0..<length us} - {i,j}))" 
    by (rule multiset_eqI, insert i, auto, rename_tac x, case_tac "x \<in> {0 ..< length us}", auto)
  define M2 where "M2 = M.summset
      {#lc ia \<cdot>\<^sub>v ?ws ! ia. ia \<in># mset_set ({0..<length us} - {i, j})#}" 
  define M1 where "M1 = M.summset {#(if i = j then ?xx else lc i) \<cdot>\<^sub>v us ! i. i \<in># mset_set ({0..<length us} - {i, j})#}" 
  have M1: "M1 \<in> carrier_vec n" unfolding M1_def using usk by fastforce
  have M2: "M1 = M2" unfolding M2_def M1_def
    by (rule arg_cong[of _ _ M.summset], rule multiset.map_cong0, insert i usk, auto) 
  have x1: "x = lc j \<cdot>\<^sub>v ?j + (lc i \<cdot>\<^sub>v ?i + lc i \<cdot>\<^sub>v (c \<cdot>\<^sub>v ?j) + M1)" 
    unfolding x lincomb_list_def M2 M2_def
    apply (subst sumlist_as_summset, (insert us ws i v ij, auto simp: set_conv_nth)[1], insert i ij v us ws usk, 
      simp add: mset smult_add_distrib_vec[OF ij(1) v(1)])
    by (subst M.summset_add_mset, auto)+
  have x2: "?x = ?xx \<cdot>\<^sub>v ?j + (lc i \<cdot>\<^sub>v ?i + M1)"
    unfolding x lincomb_list_def M1_def
    apply (subst sumlist_as_summset, (insert us ws i v ij, auto simp: set_conv_nth)[1], insert i ij v us ws usk, 
      simp add: mset smult_add_distrib_vec[OF ij(1) v(1)])
    by (subst M.summset_add_mset, auto)+
  show ?thesis unfolding x1 x2 using M1 ij
    by (intro eq_vecI, auto simp: field_simps)
qed

lemma lincomb_list_add_vec_1: assumes us: "set us \<subseteq> carrier_vec n" 
  and x: "x = lincomb_list lc us"
  and i: "j < length us" "i < length us" "i \<noteq> j" 
shows "x = lincomb_list (lc (j := lc j - lc i * c)) (us [i := us ! i + c \<cdot>\<^sub>v us ! j])" (is "_ = ?x")
proof -
  let ?i = "us ! i" 
  let ?j = "us ! j" 
  let ?v = "?i + c \<cdot>\<^sub>v ?j" 
  let ?ws = "us [i := us ! i + c \<cdot>\<^sub>v us ! j]"
  from us have usk: "k < length us \<Longrightarrow> us ! k \<in> carrier_vec n" for k by auto
  from usk i have ij: "?i \<in> carrier_vec n" "?j \<in> carrier_vec n" by auto
  hence v: "c \<cdot>\<^sub>v ?j \<in> carrier_vec n" "?v \<in> carrier_vec n" by auto
  with us have ws: "set ?ws \<subseteq> carrier_vec n" unfolding set_conv_nth using i 
    by (auto, rename_tac k, case_tac "k = i", auto)
  from us have us': "\<forall>w\<in>set us. dim_vec w = n" by auto 
  from ws have ws': "\<forall>w\<in>set ?ws. dim_vec w = n" by auto 
  have mset: "mset_set {0..<length us} = {#i#} + {#j#} + (mset_set ({0..<length us} - {i,j}))" 
    by (rule multiset_eqI, insert i, auto, rename_tac x, case_tac "x \<in> {0 ..< length us}", auto)
  define M2 where "M2 = M.summset
      {#(if ia = j then lc j - lc i * c else lc ia) \<cdot>\<^sub>v ?ws ! ia
      . ia \<in># mset_set ({0..<length us} - {i, j})#}" 
  define M1 where "M1 = M.summset {#lc i \<cdot>\<^sub>v us ! i. i \<in># mset_set ({0..<length us} - {i, j})#}" 
  have M1: "M1 \<in> carrier_vec n" unfolding M1_def using usk by fastforce
  have M2: "M1 = M2" unfolding M2_def M1_def
    by (rule arg_cong[of _ _ M.summset], rule multiset.map_cong0, insert i usk, auto) 
  have x1: "x = lc j \<cdot>\<^sub>v ?j + (lc i \<cdot>\<^sub>v ?i + M1)" 
    unfolding x lincomb_list_def M1_def
    apply (subst sumlist_as_summset, (insert us ws i v ij, auto simp: set_conv_nth)[1], insert i ij v us ws usk, 
      simp add: mset smult_add_distrib_vec[OF ij(1) v(1)])
    by (subst M.summset_add_mset, auto)+
  have x2: "?x = (lc j - lc i * c) \<cdot>\<^sub>v ?j + (lc i \<cdot>\<^sub>v ?i + lc i \<cdot>\<^sub>v (c \<cdot>\<^sub>v ?j) + M1)"
    unfolding x lincomb_list_def M2 M2_def
    apply (subst sumlist_as_summset, (insert us ws i v ij, auto simp: set_conv_nth)[1], insert i ij v us ws usk, 
      simp add: mset smult_add_distrib_vec[OF ij(1) v(1)])
    by (subst M.summset_add_mset, auto)+
  show ?thesis unfolding x1 x2 using M1 ij
    by (intro eq_vecI, auto simp: field_simps)
qed

lemma add_vec_span: assumes us: "set us \<subseteq> carrier_vec n" 
  and i: "j < length us" "i < length us" "i \<noteq> j" 
shows "span (set us) = span (set (us [i := us ! i + c \<cdot>\<^sub>v us ! j]))" (is "_ = span (set ?ws)")
proof -
  let ?i = "us ! i" 
  let ?j = "us ! j" 
  let ?v = "?i + c \<cdot>\<^sub>v ?j" 
  from us i have ij: "?i \<in> carrier_vec n" "?j \<in> carrier_vec n" by auto
  hence v: "?v \<in> carrier_vec n" by auto
  with us have ws: "set ?ws \<subseteq> carrier_vec n" unfolding set_conv_nth using i 
    by (auto, rename_tac k, case_tac "k = i", auto)
  have "span (set us) = span_list us" unfolding span_list_as_span[OF us] ..
  also have "\<dots> = span_list ?ws"
  proof -
    {
      fix x
      assume "x \<in> span_list us" 
      then obtain lc where "x = lincomb_list lc us" by (metis in_span_listE)
      from lincomb_list_add_vec_1[OF us this i, of c]
      have "x \<in> span_list ?ws" unfolding span_list_def by auto
    }
    moreover
    {
      fix x
      assume "x \<in> span_list ?ws" 
      then obtain lc where "x = lincomb_list lc ?ws" by (metis in_span_listE)
      from lincomb_list_add_vec_2[OF us this i]
      have "x \<in> span_list us" unfolding span_list_def by auto
    }
    ultimately show ?thesis by blast
  qed
  also have "\<dots> = span (set ?ws)" unfolding span_list_as_span[OF ws] ..
  finally show ?thesis .
qed

lemma prod_in_span[intro!]:
  assumes "b \<in> carrier_vec n" "S \<subseteq> carrier_vec n" "a = 0 \<or> b \<in> span S"
  shows "a \<cdot>\<^sub>v b \<in> span S"
proof(cases "a = 0")
  case True
  then show ?thesis by (auto simp:lmult_0[OF assms(1)] span_zero)
next
  case False with assms have "b \<in> span S" by auto
  from this[THEN in_spanE]
  obtain aa A where a[intro!]: "b = lincomb aa A" "finite A" "A \<subseteq> S" by auto
  hence [intro!]:"(\<lambda>v. aa v \<cdot>\<^sub>v v) \<in> A \<rightarrow> carrier_vec n" using assms by auto 
  show ?thesis proof
    show "a \<cdot>\<^sub>v b = lincomb (\<lambda> v. a * aa v) A" using a(1) unfolding lincomb_def smult_smult_assoc[symmetric]
      by(subst finsum_smult[symmetric]) force+
  qed auto
qed

lemma det_nonzero_congruence:
  assumes eq:"A * M = B * M" and det:"det (M::'a mat) \<noteq> 0"
  and M: "M \<in> carrier_mat n n" and carr:"A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A = B"
proof -
  have "1\<^sub>m n \<in> carrier_mat n n" by auto
  from det_non_zero_imp_unit[OF M det] gauss_jordan_check_invertable[OF M this]
  have gj_fst:"(fst (gauss_jordan M (1\<^sub>m n)) = 1\<^sub>m n)" by metis
  define Mi where "Mi = snd (gauss_jordan M (1\<^sub>m n))"
  with gj_fst have gj:"gauss_jordan M (1\<^sub>m n) = (1\<^sub>m n, Mi)"
    unfolding fst_def snd_def by (auto split:prod.split)
  from gauss_jordan_compute_inverse(1,3)[OF M gj]
  have Mi: "Mi \<in> carrier_mat n n" and is1:"M * Mi = 1\<^sub>m n" by metis+
  from arg_cong[OF eq, of "\<lambda> M. M * Mi"]
  show "A = B" unfolding carr[THEN assoc_mult_mat[OF _ M Mi]] is1 carr[THEN right_mult_one_mat].
qed

end

context cof_vec_space
begin

definition lin_indpt_list :: "'a vec list \<Rightarrow> bool" where
  "lin_indpt_list fs = (set fs \<subseteq> carrier_vec n \<and> distinct fs \<and> lin_indpt (set fs))" 

definition basis_list :: "'a vec list \<Rightarrow> bool" where
  "basis_list fs = (set fs \<subseteq> carrier_vec n \<and> length fs = n \<and> carrier_vec n \<subseteq> span (set fs))"

lemma upper_triangular_imp_lin_indpt_list:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "lin_indpt_list (rows A)"
  using upper_triangular_imp_distinct[OF assms]
  using upper_triangular_imp_lin_indpt_rows[OF assms] A
  unfolding lin_indpt_list_def by (auto simp: rows_def)

lemma basis_list_basis: assumes "basis_list fs" 
  shows "distinct fs" "lin_indpt (set fs)" "basis (set fs)" 
proof -
  from assms[unfolded basis_list_def] 
  have len: "length fs = n" and C: "set fs \<subseteq> carrier_vec n" 
    and span: "carrier_vec n \<subseteq> span (set fs)" by auto
  show b: "basis (set fs)" 
  proof (rule dim_gen_is_basis[OF finite_set C])
    show "card (set fs) \<le> dim" unfolding dim_is_n unfolding len[symmetric] by (rule card_length)
    show "span (set fs) = carrier_vec n" using span C by auto
  qed
  thus "lin_indpt (set fs)" unfolding basis_def by auto  
  show "distinct fs" 
  proof (rule ccontr)
    assume "\<not> distinct fs" 
    hence "card (set fs) < length fs" using antisym_conv1 card_distinct card_length by auto
    also have "\<dots> = dim" unfolding len dim_is_n ..
    finally have "card (set fs) < dim" by auto
    also have "\<dots> \<le> card (set fs)" using span finite_set[of fs] 
      using b basis_def gen_ge_dim by auto
    finally show False by simp
  qed
qed

lemma basis_list_imp_lin_indpt_list: assumes "basis_list fs" shows "lin_indpt_list fs" 
  using basis_list_basis[OF assms] assms unfolding lin_indpt_list_def basis_list_def by auto

lemma mat_of_rows_mult_as_finsum:
  assumes "v \<in> carrier_vec (length lst)" "\<And> i. i < length lst \<Longrightarrow> lst ! i \<in> carrier_vec n"
  defines "f l \<equiv> sum (\<lambda> i. if l = lst ! i then v $ i else 0) {0..<length lst}"
  shows mat_of_cols_mult_as_finsum:"mat_of_cols n lst *\<^sub>v v = lincomb f (set lst)"
proof -
  from assms have "\<forall> i < length lst. lst ! i \<in> carrier_vec n" by blast
  note an = all_nth_imp_all_set[OF this] hence slc:"set lst \<subseteq> carrier_vec n" by auto
  hence dn [simp]:"\<And> x. x \<in> set lst \<Longrightarrow> dim_vec x = n" by auto
  have dl [simp]:"dim_vec (lincomb f (set lst)) = n" using an by (intro lincomb_dim,auto)
  show ?thesis proof
    show "dim_vec (mat_of_cols n lst *\<^sub>v v) = dim_vec (lincomb f (set lst))" using assms(1,2) by auto
    fix i assume i:"i < dim_vec (lincomb f (set lst))" hence i':"i < n" by auto
    with an have fcarr:"(\<lambda>v. f v \<cdot>\<^sub>v v) \<in> set lst \<rightarrow> carrier_vec n" by auto
    from i' have "(mat_of_cols n lst *\<^sub>v v) $ i = row (mat_of_cols n lst) i \<bullet> v" by auto
    also have "\<dots> = (\<Sum>ia = 0..<dim_vec v. lst ! ia $ i * v $ ia)"
      unfolding mat_of_cols_def row_def scalar_prod_def
      apply(rule sum.cong[OF refl]) using i an assms(1) by auto
    also have "\<dots> = (\<Sum>ia = 0..<length lst. lst ! ia $ i * v $ ia)" using assms(1) by auto
    also have "\<dots> = (\<Sum>x\<in>set lst. f x * x $ i)"
      unfolding f_def sum_distrib_right apply (subst sum.swap)
      apply(rule sum.cong[OF refl])
      unfolding if_distrib if_distrib_ap mult_zero_left sum.delta[OF finite_set] by auto
    also have "\<dots> = (\<Sum>x\<in>set lst. (f x \<cdot>\<^sub>v x) $ i)"
      apply(rule sum.cong[OF refl],subst index_smult_vec) using i slc by auto
    also have "\<dots> = (\<Oplus>\<^bsub>V\<^esub>v\<in>set lst. f v \<cdot>\<^sub>v v) $ i"
      unfolding finsum_index[OF i' fcarr slc] by auto
    finally show "(mat_of_cols n lst *\<^sub>v v) $ i = lincomb f (set lst) $ i"
      by (auto simp:lincomb_def)
  qed
qed

lemma basis_det_nonzero:
  assumes db:"basis (set G)" and len:"length G = n"
  shows "det (mat_of_rows n G) \<noteq> 0"
proof -
  have M_car1:"mat_of_rows n G \<in> carrier_mat n n" using assms by auto
  hence M_car:"(mat_of_rows n G)\<^sup>T \<in> carrier_mat n n" by auto
  have li:"lin_indpt (set G)"
   and inc_2:"set G \<subseteq> carrier_vec n"
   and issp:"carrier_vec n = span (set G)"
   and RG_in_carr:"\<And>i. i < length G \<Longrightarrow> G ! i \<in> carrier_vec n"
    using assms[unfolded basis_def] by auto
  hence "basis_list G" unfolding basis_list_def using len by auto
  from basis_list_basis[OF this] have di:"distinct G" by auto
  have "det ((mat_of_rows n G)\<^sup>T) \<noteq> 0" unfolding det_0_iff_vec_prod_zero[OF M_car] 
  proof
    assume "\<exists>v. v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> (mat_of_rows n G)\<^sup>T *\<^sub>v v = 0\<^sub>v n"
    then obtain v where v:"v \<in> span (set G)"
                          "v \<noteq> 0\<^sub>v n" "(mat_of_rows n G)\<^sup>T *\<^sub>v v = 0\<^sub>v n"
      unfolding issp by blast
    from finite_in_span[OF finite_set inc_2 v(1)] obtain a
      where aA: "v = lincomb a (set G)" by blast
    from v(1,2)[folded issp] obtain i where i:"v $ i \<noteq> 0" "i < n" by fastforce
    hence inG:"G ! i \<in> set G" using len by auto
    have di2: "distinct [0..<length G]" by auto
    define f where "f = (\<lambda>l. \<Sum>i \<in> set [0..<length G]. if l = G ! i then v $ i else 0)"
    hence f':"f (G ! i) = (\<Sum>ia\<leftarrow>[0..<n]. if G ! ia = G ! i then v $ ia else 0)"
      unfolding f_def sum.distinct_set_conv_list[OF di2] unfolding len by metis
    from v have "mat_of_cols n G *\<^sub>v v = 0\<^sub>v n"
      unfolding transpose_mat_of_rows by auto
    with mat_of_cols_mult_as_finsum[OF v(1)[folded issp len] RG_in_carr]
    have f:"lincomb f (set G) = 0\<^sub>v n" unfolding len f_def by auto
    note [simp] = list_trisect[OF i(2)[folded len],unfolded len]
    note x = i(2)[folded len]
    have [simp]:"(\<Sum>x\<leftarrow>[0..<i]. if G ! x = G ! i then v $ x else 0) = 0"
      by (rule sum_list_0,auto simp: nth_eq_iff_index_eq[OF di less_trans[OF _ x] x])
    have [simp]:"(\<Sum>x\<leftarrow>[Suc i..<n]. if G ! x = G ! i then v $ x else 0) = 0"
      apply (rule sum_list_0) using nth_eq_iff_index_eq[OF di _ x] len by auto
    from i(1) have "f (G ! i) \<noteq> 0" unfolding f' by auto
  from lin_dep_crit[OF finite_set subset_refl TrueI inG this f]
    have "lin_dep (set G)".
    thus False using li by auto
  qed
  thus det0:"det (mat_of_rows n G) \<noteq> 0" by (unfold det_transpose[OF M_car1])
qed

lemma lin_indpt_list_add_vec: assumes  
      i: "j < length us" "i < length us" "i \<noteq> j" 
   and indep: "lin_indpt_list  us" 
shows "lin_indpt_list (us [i := us ! i + c \<cdot>\<^sub>v us ! j])" (is "lin_indpt_list ?V")
proof -
  from indep[unfolded lin_indpt_list_def] have us: "set us \<subseteq> carrier_vec n" 
    and dist: "distinct us" and indep: "lin_indpt (set us)" by auto
  let ?E = "set us - {us ! i}" 
  let ?us = "insert (us ! i) ?E"
  let ?v = "us ! i + c \<cdot>\<^sub>v us ! j"     
  from us i have usi: "us ! i \<in> carrier_vec n" "us ! i \<notin> ?E" "us ! i \<in> set us" 
    and usj: "us ! j \<in> carrier_vec n" by auto
  from usi usj have v: "?v \<in> carrier_vec n" by auto      
  have fin: "finite ?E" by auto
  have id: "set us = insert (us ! i) (set us - {us ! i})" using i(2) by auto
  from dist i have diff': "us ! i \<noteq> us ! j" unfolding distinct_conv_nth by auto
  from subset_li_is_li[OF indep] have indepE: "lin_indpt ?E" by auto
  have Vid: "set ?V = insert ?v ?E" using set_update_distinct[OF dist i(2)] by auto
  have E: "?E \<subseteq> carrier_vec n" using us by auto
  have V: "set ?V \<subseteq> carrier_vec n" using us v unfolding Vid by auto
  from dist i have diff: "us ! i \<noteq> us ! j" unfolding distinct_conv_nth by auto
  have vspan: "?v \<notin> span ?E"
  proof
    assume mem: "?v \<in> span ?E" 
    from diff i have "us ! j \<in> ?E" by auto
    hence "us ! j \<in> span ?E" using E by (metis span_mem)
    hence "- c \<cdot>\<^sub>v us ! j \<in> span ?E" using smult_in_span[OF E] by auto
    from span_add1[OF E mem this] have "?v + (- c \<cdot>\<^sub>v us ! j) \<in> span ?E" .
    also have "?v + (- c \<cdot>\<^sub>v us ! j) = us ! i" using usi usj by auto
    finally have mem: "us ! i \<in> span ?E" .
    from in_spanE[OF this] obtain a A where lc: "us ! i = lincomb a A" and A: "finite A" 
      "A \<subseteq> set us - {us ! i}" 
      by auto
    let ?a = "a (us ! i := -1)" let ?A = "insert (us ! i) A" 
    from A have fin: "finite ?A" by auto
    have lc: "lincomb ?a A = us ! i" unfolding lc
      by (rule lincomb_cong, insert A us lc, auto)
    have "lincomb ?a ?A = 0\<^sub>v n" 
      by (subst lincomb_insert2[OF A(1)], insert A us lc usi diff, auto)
    from not_lindepD[OF indep _ _ _ this] A usi 
    show False by auto
  qed
  hence vmem: "?v \<notin> ?E" using span_mem[OF E, of ?v] by auto
  from lin_dep_iff_in_span[OF E indepE v this] vspan 
  have indep1: "lin_indpt (set ?V)" unfolding Vid by auto
  from vmem dist have "distinct ?V" by (metis distinct_list_update)
  with indep1 V show ?thesis unfolding lin_indpt_list_def by auto
qed

lemma scalar_prod_lincomb_orthogonal: assumes ortho: "orthogonal gs" and gs: "set gs \<subseteq> carrier_vec n" 
  shows "k \<le> length gs \<Longrightarrow> sumlist (map (\<lambda> i. g i \<cdot>\<^sub>v gs ! i) [0 ..< k]) \<bullet> sumlist (map (\<lambda> i. g i \<cdot>\<^sub>v gs ! i) [0 ..< k])
  = sum_list (map (\<lambda> i. g i * g i * (gs ! i \<bullet> gs ! i)) [0 ..< k])"
proof (induct k)
  case (Suc k)
  note ortho = orthogonalD[OF ortho]
  let ?m = "length gs" 
  from gs Suc(2) have gsi[simp]: "\<And> i. i \<le> k \<Longrightarrow> gs ! i \<in> carrier_vec n" by auto
  from Suc have kn: "k \<le> ?m" and k: "k < ?m" by auto
  let ?v1 = "sumlist (map (\<lambda>i. g i \<cdot>\<^sub>v gs ! i) [0..<k])" 
  let ?v2 = "(g k \<cdot>\<^sub>v gs ! k)" 
  from Suc have id: "[0 ..< Suc k] = [0 ..< k] @ [k]" by simp
  have id: "sumlist (map (\<lambda>i. g i \<cdot>\<^sub>v gs ! i) [0..<Suc k]) = ?v1 + ?v2" 
    unfolding id map_append
    by (subst sumlist_append, insert Suc(2), auto)
  have v1: "?v1 \<in> carrier_vec n" by (rule sumlist_carrier, insert Suc(2), auto)
  have v2: "?v2 \<in> carrier_vec n" by (insert Suc(2), auto)
  have gsk: "gs ! k \<in> carrier_vec n" by simp
  have v12: "?v1 + ?v2 \<in> carrier_vec n" using v1 v2 by auto
  have 0: "i < k \<Longrightarrow> (g i \<cdot>\<^sub>v gs ! i) \<bullet> (g k \<cdot>\<^sub>v gs ! k) = 0" for i
    by (subst scalar_prod_smult_distrib[OF _ gsk], (insert k, auto)[1],
    subst smult_scalar_prod_distrib[OF _ gsk], (insert k, auto)[1], insert ortho[of i k] k, auto)
  have 0: "?v1 \<bullet> ?v2 = 0" 
    by (subst scalar_prod_left_sum_distrib[OF _ v2], (insert Suc(2), auto)[1], rule sum_list_neutral, 
        insert 0, auto)     
  show ?case unfolding id
    unfolding scalar_prod_add_distrib[OF v12 v1 v2]
      add_scalar_prod_distrib[OF v1 v2 v1]
      add_scalar_prod_distrib[OF v1 v2 v2]
      scalar_prod_smult_distrib[OF v2 gsk]
      smult_scalar_prod_distrib[OF gsk gsk]
    unfolding Suc(1)[OF kn]
    by (simp add: 0 comm_scalar_prod[OF v2 v1])
qed auto  
end


locale gram_schmidt = cof_vec_space n f_ty
  for n :: nat and f_ty :: "'a :: trivial_conjugatable_ordered_field itself"
begin

definition Gramian_matrix where
  "Gramian_matrix G k = (let M = mat k n (\<lambda> (i,j). (G ! i) $ j) in M * M\<^sup>T)"

lemma Gramian_matrix_alt_def: "k \<le> length G \<Longrightarrow> 
  Gramian_matrix G k = (let M = mat_of_rows n (take k G) in M * M\<^sup>T)"
  unfolding Gramian_matrix_def Let_def
  by (rule arg_cong[of _ _ "\<lambda> x. x * x\<^sup>T"], unfold mat_of_rows_def, intro eq_matI, auto)

definition Gramian_determinant where
  "Gramian_determinant G k = det (Gramian_matrix G k)"

lemma orthogonal_imp_lin_indpt_list: 
  assumes ortho: "orthogonal gs" and gs: "set gs \<subseteq> carrier_vec n"
  shows "lin_indpt_list gs" 
proof -
  from corthogonal_distinct[of gs] ortho have dist: "distinct gs" by simp
  show ?thesis unfolding lin_indpt_list_def
  proof (intro conjI gs dist finite_lin_indpt2 finite_set)
    fix lc
    assume 0: "lincomb lc (set gs) = 0\<^sub>v n" (is "?lc = _") 
    have lc: "?lc \<in> carrier_vec n" by (rule lincomb_closed[OF gs])
    let ?m = "length gs" 
    from 0 have "0 = ?lc \<bullet> ?lc" by simp
    also have "?lc = lincomb_list (\<lambda>i. lc (gs ! i)) gs" 
      unfolding lincomb_as_lincomb_list_distinct[OF gs dist] ..
    also have "\<dots> = sumlist (map (\<lambda>i. lc (gs ! i) \<cdot>\<^sub>v gs ! i) [0..< ?m])" 
      unfolding lincomb_list_def by auto 
    also have "\<dots> \<bullet> \<dots> = (\<Sum>i\<leftarrow>[0..<?m]. (lc (gs ! i) * lc (gs ! i)) * sq_norm (gs ! i))" (is "_ = sum_list ?sum")
      unfolding scalar_prod_lincomb_orthogonal[OF ortho gs le_refl]
      by (auto simp: sq_norm_vec_as_cscalar_prod power2_eq_square)
    finally have sum_0: "sum_list ?sum = 0" ..
    have nonneg: "\<And> x. x \<in> set ?sum \<Longrightarrow> x \<ge> 0" 
      using zero_le_square[of "lc (gs ! i)" for i] sq_norm_vec_ge_0[of "gs ! i" for i] by auto  
    {
      fix x
      assume x: "x \<in> set gs" 
      then obtain i where i: "i < ?m" and x: "x = gs ! i" unfolding set_conv_nth 
        by auto
      hence "lc x * lc x * sq_norm x \<in> set ?sum" by auto
      with sum_list_nonneg_eq_0_iff[of ?sum, OF nonneg] sum_0 
      have "lc x = 0 \<or> sq_norm x = 0" by auto
      with orthogonalD[OF ortho, OF i i, folded x]
      have "lc x = 0" by (auto simp: sq_norm_vec_as_cscalar_prod)
    }
    thus "\<forall>v\<in>set gs. lc v = 0" by auto
  qed
qed

lemma orthocompl_span:
  assumes "\<And> x. x \<in> S \<Longrightarrow> v \<bullet> x = 0" "S \<subseteq> carrier_vec n" and [intro]: "v \<in> carrier_vec n"
  and "y \<in> span S" 
  shows "v \<bullet> y = 0"
proof -
  {fix a A
   assume "y = lincomb a A" "finite A" "A \<subseteq> S"
   note assms = assms this
   hence [intro!]:"lincomb a A \<in> carrier_vec n" "(\<lambda>v. a v \<cdot>\<^sub>v v) \<in> A \<rightarrow> carrier_vec n" by auto
   have "\<forall>x\<in>A. (a x \<cdot>\<^sub>v x) \<bullet> v = 0" proof fix x assume "x \<in> A" note assms = assms this
     hence x:"x \<in> S" by auto
     with assms have [intro]:"x \<in> carrier_vec n" by auto
     from assms(1)[OF x] have "x \<bullet> v = 0" by(subst comm_scalar_prod) force+
     thus "(a x \<cdot>\<^sub>v x) \<bullet> v = 0"
       apply(subst smult_scalar_prod_distrib) by force+
   qed
   hence "v \<bullet> lincomb a A = 0" apply(subst comm_scalar_prod) apply force+ unfolding lincomb_def
     apply(subst finsum_scalar_prod_sum) by force+
  }
  thus ?thesis using \<open>y \<in> span S\<close> unfolding span_def by auto
qed

lemma orthogonal_sumlist:
  assumes ortho: "\<And> x. x \<in> set S \<Longrightarrow> v \<bullet> x = 0" and S: "set S \<subseteq> carrier_vec n" and v: "v \<in> carrier_vec n"
  shows "v \<bullet> sumlist S = 0"
  by (rule orthocompl_span[OF ortho S v sumlist_in_span[OF S span_mem[OF S]]])

lemma projection_alt_def:
  assumes carr:"(W::'a vec set) \<subseteq> carrier_vec n" "x \<in> carrier_vec n"
      and alt1:"y1 \<in> W" "x - y1 \<in> orthogonal_complement W"
      and alt2:"y2 \<in> W" "x - y2 \<in> orthogonal_complement W"
  shows  "y1 = y2"
proof -
  have carr:"y1 \<in> carrier_vec n" "y2 \<in> carrier_vec n" "x \<in> carrier_vec n" "- y1 \<in> carrier_vec n" 
    "0\<^sub>v n \<in> carrier_vec n"
    using alt1 alt2 carr by auto
  hence "y1 - y2 \<in> carrier_vec n" by auto
  note carr = this carr
  from alt1 have "ya\<in>W \<Longrightarrow> (x - y1) \<bullet> ya = 0" for ya
    unfolding orthogonal_complement_def by blast
  hence "(x - y1) \<bullet> y2 = 0" "(x - y1) \<bullet> y1 = 0" using alt2 alt1 by auto
  hence eq1:"y1 \<bullet> y2 = x \<bullet> y2" "y1 \<bullet> y1 = x \<bullet> y1" using carr minus_scalar_prod_distrib by force+
  from this(1) have eq2:"y2 \<bullet> y1 = x \<bullet> y2" using carr comm_scalar_prod by force
  from alt2 have "ya\<in>W \<Longrightarrow> (x - y2) \<bullet> ya = 0" for ya
    unfolding orthogonal_complement_def by blast
  hence "(x - y2) \<bullet> y1 = 0" "(x - y2) \<bullet> y2 = 0" using alt2 alt1 by auto
  hence eq3:"y2 \<bullet> y2 = x \<bullet> y2" "y2 \<bullet> y1 = x \<bullet> y1" using carr minus_scalar_prod_distrib by force+
  with eq2 have eq4:"x \<bullet> y1 = x \<bullet> y2" by auto
  have "\<parallel>(y1 - y2)\<parallel>\<^sup>2 = 0" unfolding sq_norm_vec_as_cscalar_prod cscalar_prod_is_scalar_prod using carr
    apply(subst minus_scalar_prod_distrib) apply force+
    apply(subst (0 0) scalar_prod_minus_distrib) apply force+
    unfolding eq1 eq2 eq3 eq4 by auto
  with sq_norm_vec_eq_0[of "(y1 - y2)"] carr have "y1 - y2 = 0\<^sub>v n" by fastforce
  hence "y1 - y2 + y2 = y2" using carr by fastforce
  also have "y1 - y2 + y2 = y1" using carr by auto
  finally show "y1 = y2" .
qed

definition weakly_reduced :: "'a \<Rightarrow> nat \<Rightarrow> 'a vec list \<Rightarrow> bool" 
  (* for k = n, this is reduced according to "Modern Computer Algebra" *)
  where "weakly_reduced \<alpha> k gs = (\<forall> i. Suc i < k \<longrightarrow> 
    sq_norm (gs ! i) \<le> \<alpha> * sq_norm (gs ! (Suc i)))" 
  
definition strictly_reduced :: "nat \<Rightarrow> 'a \<Rightarrow> 'a vec list \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> bool" 
  (* this is reduced according to LLL original paper *)
  where "strictly_reduced N \<alpha> gs mu = (weakly_reduced \<alpha> N gs \<and> 
    (\<forall> i j. i < N \<longrightarrow> j < i \<longrightarrow> abs (mu i j) \<le> 1/2))"

definition
  "is_projection w S v = (w \<in> carrier_vec n \<and> v - w \<in> span S \<and> (\<forall> u. u \<in> S \<longrightarrow> w \<bullet> u = 0))"

lemma is_projection_sq_norm: assumes "is_projection w S v"
  and S: "S \<subseteq> carrier_vec n" 
  and v: "v \<in> carrier_vec n" 
shows "sq_norm w \<le> sq_norm v" 
proof -
  from assms[unfolded is_projection_def]
  have w: "w \<in> carrier_vec n" 
    and vw: "v - w \<in> span S" and ortho: "\<And> u. u \<in> S \<Longrightarrow> w \<bullet> u = 0" by auto
  have "sq_norm v = sq_norm ((v - w) + w)" using v w 
    by (intro arg_cong[of _ _ sq_norm_vec], auto)
  also have "\<dots> = ((v - w) + w) \<bullet> ((v - w) + w)" unfolding sq_norm_vec_as_cscalar_prod
    by simp
  also have "\<dots> = (v - w) \<bullet> ((v - w) + w) + w \<bullet> ((v - w) + w)" 
    by (rule add_scalar_prod_distrib, insert v w, auto)
  also have "\<dots> = ((v - w) \<bullet> (v - w) + (v - w) \<bullet> w) + (w \<bullet> (v - w) + w \<bullet> w)" 
    by (subst (1 2) scalar_prod_add_distrib, insert v w, auto)
  also have "\<dots> = sq_norm (v - w) + 2 * (w \<bullet> (v - w)) + sq_norm w" 
    unfolding sq_norm_vec_as_cscalar_prod using v w by (auto simp: comm_scalar_prod[of w _ "v - w"])
  also have "\<dots> \<ge> 2 * (w \<bullet> (v - w)) + sq_norm w" using sq_norm_vec_ge_0[of "v - w"] by auto
  also have "w \<bullet> (v - w) = 0" using orthocompl_span[OF ortho S w vw] by auto
  finally show ?thesis by auto
qed

definition projection where
"projection S fi \<equiv> (SOME v. is_projection v S fi)"

context
  fixes fs :: "'a vec list" 
begin
  
fun gso and \<mu> where
  "gso i = fs ! i + sumlist (map (\<lambda> j. - \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< i])" 
| "\<mu> i j = (if j < i then (fs ! i \<bullet> gso j)/ sq_norm (gso j) else if i = j then 1 else 0)" 
    
declare gso.simps[simp del]
declare \<mu>.simps[simp del]
  
fun adjuster_wit :: "'a list \<Rightarrow> 'a vec \<Rightarrow> 'a vec list \<Rightarrow> 'a list \<times> 'a vec"
  where "adjuster_wit wits w [] = (wits, 0\<^sub>v n)"
  |  "adjuster_wit wits w (u#us) = (let a = (w \<bullet> u)/ sq_norm u in 
            case adjuster_wit (a # wits) w us of (wit, v)
         \<Rightarrow> (wit, -a \<cdot>\<^sub>v u + v))"

fun sub2_wit where
    "sub2_wit us [] = ([], [])"
  | "sub2_wit us (w # ws) =
     (case adjuster_wit (1 # replicate (n - length us - 1) 0) w us of (wit,aw) \<Rightarrow> let u = aw + w in
      case sub2_wit (u # us) ws of (wits, vvs) \<Rightarrow> (wit # wits, u # vvs))"  
    
definition main :: "'a vec list \<Rightarrow> 'a list list \<times> 'a vec list" where 
  "main us = sub2_wit [] us" 

lemma gso_carrier'[intro]:
  assumes "\<And> i. i \<le> j \<Longrightarrow> fs ! i \<in> carrier_vec n"
  shows "gso j \<in> carrier_vec n"
using assms proof(induct j rule:nat_less_induct[rule_format])
  case (1 j)
  then show ?case unfolding gso.simps[of j] by (auto intro!:sumlist_carrier add_carrier_vec)
qed

lemma adjuster_wit: assumes res: "adjuster_wit wits w us = (wits',a)"
  and w: "w \<in> carrier_vec n"
    and us: "\<And> i. i \<le> j \<Longrightarrow> fs ! i \<in> carrier_vec n"
    and us_gs: "us = map gso (rev [0 ..< j])" 
    and wits: "wits = map (\<mu> i) [j ..< n]" 
    and j: "j \<le> n" "j \<le> i" 
    and wi: "w = fs ! i" 
  shows "adjuster n w us = a \<and> a \<in> carrier_vec n \<and> wits' = map (\<mu> i) [0 ..< n] \<and>
      (a = sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<j]))"
  using res us us_gs wits j
proof (induct us arbitrary: wits wits' a j)
  case (Cons u us wits wits' a j)
  note us_gs = Cons(4)
  note wits = Cons(5)
  note jn = Cons(6-7)
  from us_gs obtain jj where j: "j = Suc jj" by (cases j, auto)
  from jn j have jj: "jj \<le> n" "jj < n" "jj \<le> i" "jj < i" by auto
  have zj: "[0 ..< j] = [0 ..< jj] @ [jj]" unfolding j by simp
  have jjn: "[jj ..< n] = jj # [j ..< n]" using jj(2) unfolding j by (rule upt_conv_Cons)
  from us_gs[unfolded zj] have ugs: "u = gso jj" and us: "us = map gso (rev [0..<jj])" by auto
  let ?w = "w \<bullet> u / (u \<bullet> u)" 
  have muij: "?w = \<mu> i jj" unfolding \<mu>.simps[of i jj] ugs wi sq_norm_vec_as_cscalar_prod using jj by auto
  have wwits: "?w # wits = map (\<mu> i) [jj..<n]" unfolding jjn wits muij by simp
  obtain wwits b where rec: "adjuster_wit (?w # wits) w us = (wwits,b)" by force
  from Cons(1)[OF this Cons(3) us wwits jj(1,3),unfolded j] have IH: 
     "adjuster n w us = b" "wwits = map (\<mu> i) [0..<n]"
     "b = sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<jj])"
      and b: "b \<in> carrier_vec n" by auto
  from Cons(2)[simplified, unfolded Let_def rec split sq_norm_vec_as_cscalar_prod 
      cscalar_prod_is_scalar_prod]
  have id: "wits' = wwits" and a: "a = - ?w \<cdot>\<^sub>v u + b" by auto
  have 1: "adjuster n w (u # us) = a" unfolding a IH(1)[symmetric] by auto     
  from id IH(2) have wits': "wits' =  map (\<mu> i) [0..<n]" by simp
  have carr:"set (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<j]) \<subseteq> carrier_vec n"
            "set (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<jj]) \<subseteq> carrier_vec n" and u:"u \<in> carrier_vec n" 
    using Cons j by (auto intro!:gso_carrier')
  from u b a have ac: "a \<in> carrier_vec n" "dim_vec (-?w \<cdot>\<^sub>v u) = n" "dim_vec b = n" "dim_vec u = n" by auto
  show ?case
    apply (intro conjI[OF 1] ac exI conjI wits')
    unfolding carr a IH zj muij ugs[symmetric] map_append
    apply (subst sumlist_append)
    using Cons.prems j apply force
    using b u ugs IH(3) by auto
qed auto

lemma sub2_wit:
  assumes "set us \<subseteq> carrier_vec n" "set ws \<subseteq> carrier_vec n" "length us + length ws = m" 
    and "ws = map (\<lambda> i. fs ! i) [i ..< m]"
    and "us = map gso (rev [0 ..< i])" 
    and us: "\<And> j. j < m \<Longrightarrow> fs ! j \<in> carrier_vec n"
    and mn: "m \<le> n" 
  shows "snd (sub2_wit us ws) = vvs \<Longrightarrow> gram_schmidt_sub2 n us ws = vvs 
    \<and> vvs = map gso [i ..< m]"
  using assms(1-6)
proof (induct ws arbitrary: us vvs i)
  case (Cons w ws us vs)  
  note us = Cons(3) note wws = Cons(4)
  note wsf' = Cons(6)
  note us_gs = Cons(7)
  from wsf' have "i < m" "i \<le> m" by (cases "i < m", auto)+
  hence i_m: "[i ..< m] = i # [Suc i ..< m]" by (metis upt_conv_Cons)
  from \<open>i < m\<close> mn have "i < n" "i \<le> n" "i \<le> m" by auto
  hence i_n: "[i ..< n] = i # [Suc i ..< n]" by (metis upt_conv_Cons)
  from wsf' i_m have wsf: "ws = map (\<lambda> i. fs ! i) [Suc i ..< m]" 
    and fiw: "fs !  i = w" by auto
  from wws have w: "w \<in> carrier_vec n" and ws: "set ws \<subseteq> carrier_vec n" by auto
  let ?list = "1 # replicate (n - Suc (length us)) 0" 
  have "map (\<mu> i) [Suc i ..< n] = map (\<lambda> i. 0) [Suc i ..< n]" 
    by (rule map_cong[OF refl], unfold \<mu>.simps[of i], auto)
  moreover have "\<mu> i i = 1" unfolding \<mu>.simps by simp
  ultimately have "map (\<mu> i) [i ..< n] = 1 # map (\<lambda> i. 0) [Suc i ..< n]" unfolding i_n by auto
  also have "\<dots> = ?list" using \<open>i < n\<close> unfolding map_replicate_const by (auto simp: us_gs)
  finally have list: "?list = map (\<mu> i) [i ..< n]" by auto
  let ?a = "adjuster_wit ?list w us" 
  obtain wit a where a: "?a = (wit,a)" by force
  obtain vv where gs: "snd (sub2_wit ((a + w) # us) ws) = vv" by force      
  from adjuster_wit[OF a w Cons(8) us_gs list \<open>i \<le> n\<close> _ fiw[symmetric]] us wws \<open>i < m\<close>
  have awus: "set ((a + w) # us) \<subseteq> carrier_vec n"  
     and aa: "adjuster n w us = a" "a \<in> carrier_vec n" 
     and aaa: "a = sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"  
     and wit: "wit = map (\<mu> i) [0..<n]" 
    by auto
  have aw_gs: "a + w = gso i" unfolding gso.simps[of i] fiw aaa[symmetric] using aa(2) w by auto
  with us_gs have us_gs': "(a + w) # us = map gso (rev [0..<Suc i])" by auto
  from Cons(1)[OF gs awus ws _ wsf us_gs' Cons(8)] Cons(5) 
  have IH: "gram_schmidt_sub2 n ((a + w) # us) ws = vv"  
    and vv: "vv = map gso [Suc i..<m]" by auto
  from gs a aa IH Cons(5) 
  have gs_vs: "gram_schmidt_sub2 n us (w # ws) = vs" and vs: "vs = (a + w) # vv" using Cons(2)
    by (auto simp add: Let_def snd_def split:prod.splits)
  from vs vv aw_gs have vs: "vs = map gso [i ..< m]" unfolding i_m by auto
  with gs_vs show ?case by auto
qed auto
  
lemma inv_in_span:
  assumes incarr[intro]:"U \<subseteq> carrier_vec n" and insp:"a \<in> span U"
  shows "- a \<in> span U"
proof -
  from insp[THEN in_spanE] obtain aa A where a:"a = lincomb aa A" "finite A" "A \<subseteq> U" by auto
  with assms have [intro!]:"(\<lambda>v. aa v \<cdot>\<^sub>v v) \<in> A \<rightarrow> carrier_vec n" by auto
  from a(1) have e1:"- a = lincomb (\<lambda> x. - 1 * aa x) A" unfolding smult_smult_assoc[symmetric] lincomb_def
    by(subst finsum_smult[symmetric]) force+
  show ?thesis using e1 a span_def by blast
qed

lemma non_span_det_zero:
  assumes len: "length G = n"
  and nonb:"\<not> (carrier_vec n \<subseteq> span (set G))"
  and carr:"set G \<subseteq> carrier_vec n"
  shows "det (mat_of_rows n G) = 0" unfolding det_0_iff_vec_prod_zero
proof -
  let ?A = "(mat_of_rows n G)\<^sup>T" let ?B = "1\<^sub>m n"
  from carr have carr_mat:"?A \<in> carrier_mat n n" "?B \<in> carrier_mat n n" "mat_of_rows n G \<in> carrier_mat n n"
    using len mat_of_rows_carrier(1) by auto
  from carr have g_len:"\<And> i. i < length G \<Longrightarrow> G ! i \<in> carrier_vec n" by auto
  from nonb obtain v where v:"v \<in> carrier_vec n" "v \<notin> span (set G)" by fast
  hence "v \<noteq> 0\<^sub>v n" using span_zero by auto
  obtain B C where gj:"gauss_jordan ?A ?B = (B,C)" by force
  note gj = carr_mat(1,2) gj
  hence B:"B = fst (gauss_jordan ?A ?B)" by auto
  from gauss_jordan[OF gj] have BC:"B \<in> carrier_mat n n" by auto
  from gauss_jordan_transform[OF gj] obtain P where
   P:"P\<in>Units (ring_mat TYPE('a) n ?B)"  "B = P * ?A" by fast
  hence PC:"P \<in> carrier_mat n n" unfolding Units_def by (simp add: ring_mat_simps)
  from mat_inverse[OF PC] P obtain PI where "mat_inverse P = Some PI" by fast
  from mat_inverse(2)[OF PC this]
  have PI:"P * PI = 1\<^sub>m n" "PI * P = 1\<^sub>m n" "PI \<in> carrier_mat n n" by auto
  have "B \<noteq> 1\<^sub>m n" proof
    assume "B = ?B"
    hence "?A * P = ?B" unfolding P
      using PC P(2) carr_mat(1) mat_mult_left_right_inverse by blast
    hence "?A * P *\<^sub>v v = v" using v by auto
    hence "?A *\<^sub>v (P *\<^sub>v v) = v" unfolding assoc_mult_mat_vec[OF carr_mat(1) PC v(1)].
    hence v_eq:"mat_of_cols n G *\<^sub>v (P *\<^sub>v v) = v"
      unfolding transpose_mat_of_rows by auto
    have pvc:"P *\<^sub>v v \<in> carrier_vec (length G)" using PC v len by auto
    from mat_of_cols_mult_as_finsum[OF pvc g_len,unfolded v_eq] obtain a where
      "v = lincomb a (set G)" by auto
    hence "v \<in> span (set G)" by (intro in_spanI[OF _ finite_set subset_refl])
    thus False using v by auto
  qed
  with det_non_zero_imp_unit[OF carr_mat(1)] show ?thesis
    unfolding gauss_jordan_check_invertable[OF carr_mat(1,2)] B det_transpose[OF carr_mat(3)]
    by metis
qed

lemma span_basis_det_zero_iff:
assumes "length G = n" "set G \<subseteq> carrier_vec n"
shows "carrier_vec n \<subseteq> span (set G) \<longleftrightarrow> det (mat_of_rows n G) \<noteq> 0" (is ?q1)
      "carrier_vec n \<subseteq> span (set G) \<longleftrightarrow> basis (set G)" (is ?q2)
      "det (mat_of_rows n G) \<noteq> 0 \<longleftrightarrow> basis (set G)" (is ?q3)
proof -
  have dc:"det (mat_of_rows n G) \<noteq> 0 \<Longrightarrow> carrier_vec n \<subseteq> span (set G)"
    using assms non_span_det_zero by auto
  have cb:"carrier_vec n \<subseteq> span (set G) \<Longrightarrow> basis (set G)" using assms basis_list_basis 
    by (auto simp: basis_list_def)
  have bd:"basis (set G) \<Longrightarrow> det (mat_of_rows n G) \<noteq> 0" using assms basis_det_nonzero by auto
  show ?q1 ?q2 ?q3 using dc cb bd by metis+
qed

lemma partial_connect: fixes vs
  assumes "length fs = m" "k \<le> m" "m \<le> n" "set us \<subseteq> carrier_vec n" "snd (main us) = vs" 
  "us = take k fs" "set fs \<subseteq> carrier_vec n"
shows "gram_schmidt n us = vs" 
    "vs = map gso [0..<k]" 
proof -
  have [simp]: "map ((!) fs) [0..<k] = take k fs" using assms(1,2) by (intro nth_equalityI, auto)
  have carr: "j < m \<Longrightarrow> fs ! j \<in> carrier_vec n" for j using assms by auto
  from sub2_wit[OF _ assms(4) _ _ _ carr _ assms(5)[unfolded main_def], of k 0] assms
  show "gram_schmidt n us = vs" "vs = map gso [0..<k]" unfolding gram_schmidt_code by auto
qed

lemma adjuster_wit_small:
  "(adjuster_wit v a xs) = (x1,x2)
  \<longleftrightarrow> (fst (adjuster_wit v a xs) = x1 \<and> x2 = adjuster n a xs)"
proof(induct xs arbitrary: a v x1 x2)
  case (Cons a xs)
  then show ?case
    by (auto simp:Let_def sq_norm_vec_as_cscalar_prod split:prod.splits) 
qed auto

lemma rev_unsimp: "rev xs @ (r # rs) = rev (r#xs) @ rs" by(induct xs,auto)

lemma sub2: "rev xs @ snd (sub2_wit xs us) = rev (gram_schmidt_sub n xs us)"
proof -
  have "sub2_wit xs us = (x1, x2) \<Longrightarrow> rev xs @ x2 = rev (gram_schmidt_sub n xs us)"
    for x1 x2 xs us
    apply(induct us arbitrary: xs x1 x2)
    by (auto simp:Let_def rev_unsimp adjuster_wit_small split:prod.splits simp del:rev.simps)
  thus ?thesis 
    apply (cases us)
    by (auto simp:Let_def rev_unsimp adjuster_wit_small split:prod.splits simp del:rev.simps)
qed

lemma gso_connect: "snd (main us) = gram_schmidt n us" unfolding main_def gram_schmidt_def
  using sub2[of Nil us] by auto

lemma lin_indpt_list_nonzero:
  assumes "lin_indpt_list G" 
  shows "0\<^sub>v n \<notin> set G"
proof-
  from assms[unfolded lin_indpt_list_def] have "lin_indpt (set G)" by auto
  from vs_zero_lin_dep[OF _ this] assms[unfolded lin_indpt_list_def] show zero: "0\<^sub>v n \<notin> set G" by auto
qed


context
  fixes m :: nat
begin
definition M where "M \<equiv> mat m m (\<lambda> (i,j). \<mu> i j)"

context
  fixes vs 
  assumes indep: "lin_indpt_list fs"
   and len_fs: "length fs = m" 
   and snd_main: "snd (main fs) = vs" 
begin

lemma fs_carrier[simp]: "set fs \<subseteq> carrier_vec n" 
  and dist: "distinct fs"
  and lin_indpt: "lin_indpt (set fs)" 
  using indep[unfolded lin_indpt_list_def] by auto

lemmas assm = len_fs fs_carrier snd_main
  
lemma f_carrier[simp]: "i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" 
  using fs_carrier len_fs unfolding set_conv_nth by force

lemma gso_carrier[simp]: "i < m \<Longrightarrow> gso i \<in> carrier_vec n" 
  using gso_carrier' f_carrier by auto

lemma gso_dim[simp]: "i < m \<Longrightarrow> dim_vec (gso i) = n" by auto
lemma f_dim[simp]: "i < m \<Longrightarrow> dim_vec (fs ! i) = n" by auto

lemma mn: "m \<le> n" 
proof -
  have n: "n = dim" by (simp add: dim_is_n)
  have m: "m = card (set fs)" unfolding len_fs[symmetric] 
    using distinct_card[OF dist] by simp
  from m n have mn: "m \<le> n \<longleftrightarrow> card (set fs) \<le> dim" by simp
  show ?thesis unfolding mn
    by (rule li_le_dim[OF _ fs_carrier lin_indpt], simp)
qed

lemma main_connect: 
  "gram_schmidt n fs = vs"  
  "vs = map gso [0..<m]"
proof -
  have "gram_schmidt_sub2 n [] fs = vs \<and> vs = map gso [0..<m]" 
    by (rule sub2_wit[OF _ assm(2) _ _ _ _ mn], insert snd_main len_fs, 
      auto simp: main_def intro!: nth_equalityI)
  thus "gram_schmidt n fs = vs" "vs = map gso [0..<m]" by (auto simp: gram_schmidt_code)
qed

lemma reduced_vs_E: "weakly_reduced \<alpha> k vs \<Longrightarrow> k \<le> m \<Longrightarrow> Suc i < k \<Longrightarrow> 
  sq_norm (gso i) \<le> \<alpha> * sq_norm (gso (Suc i))" 
  unfolding weakly_reduced_def main_connect(2) by auto
      
abbreviation (input) FF where "FF \<equiv> mat_of_rows n fs"
abbreviation (input) Fs where "Fs \<equiv> mat_of_rows n vs" 
  
lemma FF_dim[simp]: "dim_row FF = m" "dim_col FF = n" "FF \<in> carrier_mat m n" 
  unfolding mat_of_rows_def by (auto simp: assm len_fs)

lemma Fs_dim[simp]: "dim_row Fs = m" "dim_col Fs = n" "Fs \<in> carrier_mat m n" 
  unfolding mat_of_rows_def by (auto simp: assm main_connect)

lemma M_dim[simp]: "dim_row M = m" "dim_col M = m" "M \<in> carrier_mat m m" unfolding M_def by auto
    
lemma FF_index[simp]: "i < m \<Longrightarrow> j < n \<Longrightarrow> FF $$ (i,j) = fs ! i $ j" 
  unfolding mat_of_rows_def using assm by auto

lemma M_index[simp]:"i < m \<Longrightarrow> j < m \<Longrightarrow> M $$ (i,j) = \<mu> i j"
  unfolding M_def by auto
    
(* equation 2 on page 463 of textbook *)      
lemma matrix_equality: "FF = M * Fs" 
proof - 
  let ?P = "M * Fs" 
  have dim: "dim_row FF = m" "dim_col FF = n" "dim_row ?P = m" "dim_col ?P = n" "dim_row M = m" "dim_col M = m" 
      "dim_row Fs = m" "dim_col Fs = n" 
    by (auto simp: assm mat_of_rows_def mat_of_rows_list_def main_connect len_fs)
  show ?thesis 
  proof (rule eq_matI; unfold dim)
    fix i j
    assume i: "i < m" and j: "j < n" 
    from i have split: "[0 ..< m] = [0 ..< i] @ [i] @ [Suc i ..< m]"
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append upt_rec zero_less_Suc)
    let ?prod = "\<lambda> k. \<mu> i k * gso k $ j" 
    have dim2: "dim_vec (col Fs j) = m" using j dim by auto
    define idx where "idx = [0..<i]" 
    have idx: "set idx \<subseteq> {0 ..< i}" unfolding idx_def using i by auto
    let ?vec = "sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) idx)" 
    have vec: "?vec \<in> carrier_vec n" by (rule sumlist_carrier, insert idx gso_carrier i, auto)
    hence dimv: "dim_vec ?vec = n" by auto
    have "?P $$ (i,j) = row M i \<bullet> col Fs j" using dim i j by auto
    also have "\<dots> = (\<Sum> k = 0..<m. row M i $ k * col Fs j $ k)" 
      unfolding scalar_prod_def dim2 by auto
    also have "\<dots> = (\<Sum> k = 0..<m. ?prod k)" 
      by (rule sum.cong[OF refl], insert i j dim, auto simp: mat_of_rows_list_def mat_of_rows_def main_connect(2))
    also have "\<dots> = sum_list (map ?prod [0 ..< m])"       
      by (subst sum_list_distinct_conv_sum_set, auto)
    also have "\<dots> = sum_list (map ?prod idx) + ?prod i + sum_list (map ?prod [Suc i ..< m])" 
      unfolding split idx_def by auto
    also have "?prod i = gso i $ j" unfolding \<mu>.simps by simp
    also have "\<dots> = fs ! i $ j + sum_list (map (\<lambda>k. - \<mu> i k * gso k $ j) idx)" unfolding gso.simps[of i] idx_def[symmetric]
      by (subst index_add_vec, unfold dimv, rule j, subst sumlist_vec_index[OF _ j], insert idx gso_carrier i j, 
      auto simp: o_def intro!: arg_cong[OF map_cong])
    also have "sum_list (map (\<lambda>k. - \<mu> i k * gso k $ j) idx) = - sum_list (map (\<lambda>k. \<mu> i k * gso k $ j) idx)" 
      by (induct idx, auto)
    also have "sum_list (map ?prod [Suc i ..< m]) = 0"
      by (rule sum_list_neutral, auto simp: \<mu>.simps)
    finally have "?P $$ (i,j) = fs ! i $ j" by simp
    with FF_index[OF i j]
    show "FF $$ (i,j) = ?P $$ (i,j)" by simp
  qed auto
qed
  
lemma fi_is_sum_of_mu_gso: assumes i: "i < m" 
  shows "fs ! i = sumlist (map (\<lambda> j. \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< Suc i])" 
proof -
  let ?l = "sumlist (map (\<lambda> j. \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< Suc i])" 
  have "?l \<in> carrier_vec n" by (rule sumlist_carrier, insert gso_carrier i, auto)
  hence dim: "dim_vec ?l = n" by (rule carrier_vecD)
  show ?thesis 
  proof (rule eq_vecI, unfold dim f_dim[OF i])
    fix j
    assume j: "j < n"     
    from i have split: "[0 ..< m] = [0 ..< Suc i] @ [Suc i ..< m]"
      by (metis Suc_lessI append.assoc append_same_eq less_imp_add_positive order_refl upt_add_eq_append zero_le)
    let ?prod = "\<lambda> k. \<mu> i k * gso k $ j" 
    have "fs ! i $ j = FF $$ (i,j)" using i j by simp
    also have "\<dots> = (M * Fs) $$ (i,j)" using matrix_equality by simp
    also have "\<dots> = row M i \<bullet> col Fs j" using i j by auto
    also have "\<dots> = (\<Sum> k = 0..<m. row M i $ k * col Fs j $ k)" 
      unfolding scalar_prod_def by (auto simp: main_connect(2))
    also have "\<dots> = (\<Sum> k = 0..<m. ?prod k)" 
      by (rule sum.cong[OF refl], insert i j dim, auto simp: mat_of_rows_list_def mat_of_rows_def main_connect(2))
    also have "\<dots> = sum_list (map ?prod [0 ..< m])"       
      by (subst sum_list_distinct_conv_sum_set, auto)
    also have "\<dots> = sum_list (map ?prod [0 ..< Suc i]) + sum_list (map ?prod [Suc i ..< m])" 
      unfolding split by auto
    also have "sum_list (map ?prod [Suc i ..< m]) = 0" 
      by (rule sum_list_neutral, auto simp: \<mu>.simps)
    also have "sum_list (map ?prod [0 ..< Suc i]) = ?l $ j" 
      by (subst sumlist_vec_index[OF _ j], (insert i, auto simp: intro!: gso_carrier)[1], 
        rule arg_cong[of _ _ sum_list], insert i j, auto)
    finally show "fs ! i $ j = ?l $ j" by simp
  qed simp
qed

lemma vs:
  shows "set vs \<subseteq> carrier_vec n" "distinct vs" "corthogonal (rev vs)"
        "span (set fs) = span (set vs)" "length vs = length fs"
proof -
  from main_connect(1)[unfolded gram_schmidt_def] have e:"gram_schmidt_sub n [] fs = rev vs" by auto
  have "set [] \<subseteq> carrier_vec n" "distinct ([] @ fs)" "lin_indpt (set ([] @ fs))"
       "corthogonal []" using assm lin_indpt dist by auto
  from cof_vec_space.gram_schmidt_sub_result[OF e assm(2) this]
  show "set vs \<subseteq> carrier_vec n" "distinct vs" " corthogonal (rev vs)"
    "span (set fs) = span (set vs)" "length vs = length fs"
    by auto
qed

lemma gso_inj[intro]:
  shows "i < m \<Longrightarrow> inj_on gso {0..<i}"
proof
  fix x y assume assms:"i < m" "x \<in> {0..<i}" "y \<in> {0..<i}" "gso x = gso y"
  have "distinct vs" "x < length vs" "y < length vs" using vs assms assm by auto
  from nth_eq_iff_index_eq[OF this] assms main_connect show "x = y" by auto
qed

lemmas gram_schmidt = cof_vec_space.gram_schmidt_result[OF fs_carrier dist lin_indpt main_connect(1)[symmetric]]

lemma partial_span: assumes i: "i \<le> m" shows "span (gso ` {0 ..< i}) = span (set (take i fs))" 
proof -
  let ?f = "\<lambda> i. fs ! i" 
  let ?us = "take i fs" 
  have len: "length ?us = i" using len_fs i by auto
  from fs_carrier len_fs i have us: "set ?us \<subseteq> carrier_vec n" 
    by (meson set_take_subset subset_trans)
  obtain vi where main: "snd (main ?us) = vi" by force
  from dist have dist: "distinct ?us" by auto
  from lin_indpt have indpt: "lin_indpt (set ?us)" 
    using supset_ld_is_ld[of "set ?us", of "set (?us @ drop i fs)"] 
    by (auto simp: set_take_subset)
  from partial_connect[OF len_fs i mn us main refl fs_carrier]
  have gso: "vi = gram_schmidt n ?us" and vi: "vi = map gso [0 ..< i]" by auto
  from cof_vec_space.gram_schmidt_result(1)[OF us dist indpt gso, unfolded vi]
  show ?thesis by auto
qed

lemma partial_span': assumes i: "i \<le> m" shows "span (gso ` {0 ..< i}) = span ((\<lambda> j. fs ! j) ` {0 ..< i})" 
  unfolding partial_span[OF i]
  by (rule arg_cong[of _ _ span], subst nth_image, insert i len_fs, auto)

(* Theorem 16.5 (iv) *)  
lemma det: assumes m: "m = n" shows "det FF = det Fs" 
  unfolding matrix_equality
  apply (subst det_mult[OF M_dim(3)], (insert Fs_dim(3) m, auto)[1])
  apply (subst det_lower_triangular[OF _ M_dim(3)]) 
  by (subst M_index, (auto simp: \<mu>.simps)[3], unfold prod_list_diag_prod, auto simp: \<mu>.simps) 

(* Theorem 16.5 (iii) *)  
lemma orthogonal: "i < m \<Longrightarrow> j < m \<Longrightarrow> i \<noteq> j \<Longrightarrow> gso i \<bullet> gso j = 0" 
  using gram_schmidt(2)[unfolded main_connect corthogonal_def] by auto

(* Theorem 16.5 (i) not in full general form *)  
lemma same_base: "span (set fs) = span (gso ` {0..<m})" 
  using gram_schmidt(1)[unfolded _ main_connect] by auto

(* Theorem 16.5 (ii), second half *)
lemma sq_norm_gso_le_f: assumes i: "i < m"
  shows "sq_norm (gso i) \<le> sq_norm (fs ! i)"
proof -
  have id: "[0 ..< Suc i] = [0 ..< i] @ [i]" by simp
  let ?sum = "sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])" 
  have sum: "?sum \<in> carrier_vec n" and gsoi: "gso i \<in> carrier_vec n" using i
    by (auto intro!: sumlist_carrier gso_carrier)
  from fi_is_sum_of_mu_gso[OF i, unfolded id]
  have "sq_norm (fs ! i) = sq_norm (sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<i] @ [gso i]))" by (simp add: \<mu>.simps)
  also have "\<dots> = sq_norm (?sum + gso i)" 
    by (subst sumlist_append, insert gso_carrier i, auto)
  also have "\<dots> = (?sum + gso i) \<bullet> (?sum + gso i)" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "\<dots> = ?sum \<bullet> (?sum + gso i) + gso i \<bullet> (?sum + gso i)" 
    by (rule add_scalar_prod_distrib[OF sum gsoi], insert sum gsoi, auto)
  also have "\<dots> = (?sum \<bullet> ?sum + ?sum \<bullet> gso i) + (gso i \<bullet> ?sum + gso i \<bullet> gso i)" 
    by (subst (1 2) scalar_prod_add_distrib[of _ n], insert sum gsoi, auto)
  also have "?sum \<bullet> ?sum = sq_norm ?sum" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "gso i \<bullet> gso i = sq_norm (gso i)" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "gso i \<bullet> ?sum = ?sum \<bullet> gso i" using gsoi sum by (simp add: comm_scalar_prod)
  finally have "sq_norm (fs ! i) = sq_norm ?sum + 2 * (?sum \<bullet> gso i) + sq_norm (gso i)" by simp
  also have "\<dots> \<ge> 2 * (?sum \<bullet> gso i) + sq_norm (gso i)" using sq_norm_vec_ge_0[of ?sum] by simp
  also have "?sum \<bullet> gso i = (\<Sum>v\<leftarrow>map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<i]. v \<bullet> gso i)" 
    by (subst scalar_prod_left_sum_distrib[OF _ gsoi], insert i gso_carrier, auto)
  also have "\<dots> = 0" 
  proof (rule sum_list_neutral, goal_cases)
    case (1 x)
    then obtain j where j: "j < i" and x: "x = (\<mu> i j \<cdot>\<^sub>v gso j) \<bullet> gso i" by auto
    from j i have gsoj: "gso j \<in> carrier_vec n" by auto
    have "x = \<mu> i j * (gso j \<bullet> gso i)" using gsoi gsoj unfolding x by simp
    also have "gso j \<bullet> gso i = 0" 
      by (rule orthogonal, insert j i, auto)
    finally show "x = 0" by simp
  qed
  finally show ?thesis by simp
qed

(* Theorem 16.5 (ii), first half *)
lemma projection_exist:
  assumes "i < m" 
  shows "fs ! i - gso i \<in> span (gso ` {0..<i})"
proof
  let ?A = "gso ` {0..<i}"
  show finA:"finite ?A" by auto
  have carA[intro!]:"?A \<subseteq> carrier_vec n" using gso_dim assms by auto
  let "?a v" = "\<Sum>n\<leftarrow>[0..<i]. if v = gso n then \<mu> i n else 0"
  have d:"(sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])) \<in> carrier_vec n"
    using gso.simps[of i] gso_dim[OF assms] unfolding carrier_vec_def by auto
  note [intro] = f_carrier[OF assms] gso_carrier[OF assms] d
  have [intro!]:"(\<lambda>v. ?a v \<cdot>\<^sub>v v) \<in> gso ` {0..<i} \<rightarrow> carrier_vec n"
     using gso_carrier assms by auto
  {fix ia assume ia[intro]:"ia < n"
    have "(\<Sum>x\<in>gso ` {0..<i}. (?a x \<cdot>\<^sub>v x) $ ia) =
      - (\<Sum>x\<leftarrow>map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i]. x $ ia)"
    unfolding map_map comm_monoid_add_class.sum.reindex[OF gso_inj[OF assms]]
    unfolding atLeastLessThan_upt sum_set_upt_conv_sum_list_nat uminus_sum_list_map o_def
    proof(rule arg_cong[OF map_cong, OF refl],goal_cases)
      case (1 x) hence x:"x < m" "x < i" using assms by auto
      hence d:"insert x (set [0..<i]) = {0..<i}"
              "count (mset [0..<i]) x = 1" by auto
      hence "inj_on gso (insert x (set [0..<i]))" using gso_inj[OF assms] by auto
      from inj_on_filter_key_eq[OF this,folded replicate_count_mset_eq_filter_eq]
      have "[n\<leftarrow>[0..<i] . gso x = gso n] = [x]" using x assms d replicate.simps(2)[of 0] by auto
      hence "(\<Sum>n\<leftarrow>[0..<i]. if gso x = gso n then \<mu> i n else 0) = \<mu> i x"
        unfolding sum_list_map_filter'[symmetric] by auto
      with ia gso_dim x show ?case apply(subst index_smult_vec) by force+
    qed
    hence "(\<Oplus>\<^bsub>V\<^esub>v\<in>gso ` {0..<i}. ?a v \<cdot>\<^sub>v v) $ ia =
          (- local.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])) $ ia"
      using d assms
      apply (subst (0 0) finsum_index index_uminus_vec) apply force+
      apply (subst sumlist_vec_index) by force+
  }
  hence id: "(\<Oplus>\<^bsub>V\<^esub>v\<in>?A. ?a v \<cdot>\<^sub>v v) = - sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"
    using d lincomb_dim[OF finA carA,unfolded lincomb_def] by(intro eq_vecI,auto)
  show "fs ! i - gso i = lincomb ?a ?A" unfolding lincomb_def gso.simps[of i] id
    by (rule eq_vecI, auto)
qed auto

lemma projection_unique:
  assumes "i < m" 
          "v \<in> carrier_vec n"
          "\<And> x. x \<in> gso ` {0..<i} \<Longrightarrow> v \<bullet> x = 0"
          "fs ! i - v \<in> span (gso ` {0..<i})"
  shows "v = gso i"
proof -
  from assms have carr_span:"span (gso ` {0..<i}) \<subseteq> carrier_vec n" by(intro span_is_subset2) auto
  from assms have carr: "gso ` {0..<i} \<subseteq> carrier_vec n" by auto
  from assms have eq:"fs ! i - (fs ! i - v) = v" for v by auto
  from orthocompl_span[OF assms(3) carr assms(2)]
  have "y \<in> span (gso ` {0..<i}) \<Longrightarrow> v \<bullet> y = 0" for y by auto
  hence oc1:"fs ! i - (fs ! i - v) \<in> orthogonal_complement (span (gso ` {0..< i}))"
    unfolding eq orthogonal_complement_def using assms by auto
  have "x \<in> gso ` {0..<i} \<Longrightarrow> gso i \<bullet> x = 0" for x using assms orthogonal by auto
  hence "y \<in> span (gso ` {0..<i}) \<Longrightarrow> gso i \<bullet> y = 0" for y
    by (rule orthocompl_span[OF _ carr gso_carrier[OF assms(1)],rule_format])
  hence oc2:"fs ! i - (fs ! i - gso i) \<in> orthogonal_complement (span (gso ` {0..< i}))"
    unfolding eq orthogonal_complement_def using assms by auto
  note pe= projection_exist[OF assms(1)]
  note prerec = carr_span f_carrier[OF assms(1)] assms(4) oc1 projection_exist[OF assms(1)] oc2
  have gsoi: "gso i \<in> carrier_vec n" "fs ! i \<in> carrier_vec n" by (rule gso_carrier[OF \<open>i < m\<close>], rule f_carrier[OF \<open>i < m\<close>])
  note main = arg_cong[OF projection_alt_def[OF carr_span f_carrier[OF assms(1)] assms(4) oc1 pe oc2], 
     of "\<lambda> v. - v $ j + fs ! i $ j" for j]
  show "v = gso i" 
  proof (intro eq_vecI)
    fix j
    show "j < dim_vec (gso i) \<Longrightarrow> v $ j = gso i $ j" 
      using assms(2) gsoi main[of j] by auto
  qed (insert assms(2) gsoi, auto)
qed

lemma gso_projection:
  assumes "i < m"
  shows "gso i = projection (gso ` {0..<i}) (fs ! i)"
  unfolding projection_def is_projection_def
proof (rule some_equality[symmetric,OF _ projection_unique[OF assms]])
  have orthogonal:"\<And> xa. xa < i \<Longrightarrow> gso i \<bullet> gso xa = 0" by (rule orthogonal,insert assms, auto)
  show "gso i \<in> carrier_vec n \<and>
        fs ! i - gso i \<in> span (gso ` {0..<i}) \<and>
        (\<forall>x. x \<in> gso ` {0..<i} \<longrightarrow> gso i \<bullet> x = 0)"
    using gso_carrier[OF assms] projection_exist[OF assms] orthogonal by auto
qed auto

lemma gso_projection_span:
  assumes "i < m"
  shows "gso i = projection (span (gso ` {0..<i})) (fs ! i)"
    and "is_projection (gso i) (span (gso ` {0..<i})) (fs ! i)"
  unfolding projection_def is_projection_def
proof (rule some_equality[symmetric,OF _ projection_unique[OF assms]])
  let "?P v" = "v \<in> carrier_vec n \<and> fs ! i - v \<in> span (span (gso ` {0..<i})) 
    \<and> (\<forall>x. x \<in> span (gso ` {0..<i}) \<longrightarrow> v \<bullet> x = 0)"
  have carr:"gso ` {0..<i} \<subseteq> carrier_vec n" using assms by auto
  have *: "\<And> xa. xa < i \<Longrightarrow> gso i \<bullet> gso xa = 0" by (rule orthogonal,insert assms, auto)
  have orthogonal:"\<And>x. x \<in> span (gso ` {0..<i}) \<Longrightarrow> gso i \<bullet> x = 0"
    apply(rule orthocompl_span) using assms * by auto
  show "?P (gso i)" "?P (gso i)" unfolding span_span[OF carr]
    using gso_carrier[OF assms] projection_exist[OF assms] orthogonal by auto
  fix v assume p:"?P v"
  then show "v \<in> carrier_vec n" by auto
  from p show "fs ! i - v \<in> span (gso ` {0..<i})" unfolding span_span[OF carr] by auto
  fix xa assume "xa \<in> gso ` {0..<i}"
  hence "xa \<in> span (gso ` {0..<i})" using in_own_span[OF carr] by auto
  thus "v \<bullet> xa = 0" using p by auto
qed

lemma is_projection_eq:
  assumes ispr:"is_projection a S v" "is_projection b S v" 
    and carr: "S \<subseteq> carrier_vec n" "v \<in> carrier_vec n"
  shows "a = b"
proof -
  from carr have c2:"span S \<subseteq> carrier_vec n" "v \<in> carrier_vec n" by auto
  have a:"v - (v - a) = a" using carr ispr by auto
  have b:"v - (v - b) = b" using carr ispr by auto
  have "(v - a) = (v - b)" 
    apply(rule projection_alt_def[OF c2])
    using ispr a b unfolding in_orthogonal_complement_span[OF carr(1)]
    unfolding orthogonal_complement_def is_projection_def by auto
  hence "v - (v - a) = v - (v - b)" by metis
  thus ?thesis unfolding a b.
qed


lemma scalar_prod_lincomb_gso: assumes k: "k \<le> m"
  shows "sumlist (map (\<lambda> i. g i \<cdot>\<^sub>v gso i) [0 ..< k]) \<bullet> sumlist (map (\<lambda> i. g i \<cdot>\<^sub>v gso i) [0 ..< k])
    = sum_list (map (\<lambda> i. g i * g i * (gso i \<bullet> gso i)) [0 ..< k])" 
proof -
  have id1: "map (\<lambda>i. g i \<cdot>\<^sub>v map gso [0..<m] ! i) [0..<k] = map (\<lambda>i. g i \<cdot>\<^sub>v gso i) [0..<k]" using k
    by auto
  have id2: "(\<Sum>i\<leftarrow>[0..<k]. g i * g i * (map gso [0..<m] ! i \<bullet> map gso [0..<m] ! i)) 
    = (\<Sum>i\<leftarrow>[0..<k]. g i * g i * (gso i \<bullet> gso i))" using k
    by (intro arg_cong[OF map_cong], auto)
  from k len_fs gram_schmidt have "orthogonal vs" "set vs \<subseteq> carrier_vec n" "k \<le> length vs" by auto
  from scalar_prod_lincomb_orthogonal[OF this, of g, unfolded main_connect(2) id1 id2] 
  show ?thesis .
qed

lemma gso_times_self_is_norm:
  assumes "j < m" shows "fs ! j \<bullet> gso j = sq_norm_vec (gso j)" (is "?lhs = ?rhs")
proof -
  have "?lhs = fs ! j \<bullet>c gso j + 0" by auto
  also have "0 = M.sumlist (map (\<lambda>ja. - \<mu> j ja \<cdot>\<^sub>v gso ja) [0..<j]) \<bullet>c gso j" using assms orthogonal
    apply(subst scalar_prod_left_sum_distrib,force,force)
    by(intro sum_list_0[symmetric],auto)
  finally show ?thesis unfolding sq_norm_vec_as_cscalar_prod vec_conjugate_rat using assms
    apply(subst (2) gso.simps)
    apply(subst add_scalar_prod_distrib[OF f_carrier M.sumlist_carrier])
    by auto
qed

(* Lemma 16.7 *)
lemma gram_schmidt_short_vector: assumes in_L: "h \<in> lattice_of fs - {0\<^sub>v n}" 
shows "\<exists> i < m. \<parallel>h\<parallel>\<^sup>2 \<ge> \<parallel>gso i\<parallel>\<^sup>2"
proof -
  from in_L have non_0: "h \<noteq> 0\<^sub>v n" by auto
  from in_L[unfolded lattice_of_def] obtain lam where 
    h: "h =  sumlist (map (\<lambda> i. of_int (lam i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])" 
    by auto
  have in_L: "h = sumlist (map (\<lambda> i. of_int (lam i) \<cdot>\<^sub>v fs ! i) [0 ..< m])" unfolding assm length_map h
    by (rule arg_cong[of _ _ sumlist], rule map_cong, auto simp: len_fs)
  let ?n = "[0 ..< m]" 
  let ?f = "(\<lambda> i. of_int (lam i) \<cdot>\<^sub>v fs ! i)" 
  let ?vs = "map ?f ?n" 
  let ?P = "\<lambda> k. k < m \<and> lam k \<noteq> 0" 
  define k where "k = (GREATEST kk. ?P kk)" 
  { 
    assume *: "\<forall> i < m. lam i = 0" 
    have vs: "?vs = map (\<lambda> i. 0\<^sub>v n) ?n"
      by (rule map_cong, insert f_dim *, auto)
    have "h = 0\<^sub>v n" unfolding in_L vs
      by (rule sumlist_neutral, auto)
    with non_0 have False by auto
  }  
  then obtain kk where "?P kk" by auto
  from GreatestI_nat[of ?P, OF this, of m] have Pk: "?P k" unfolding k_def by auto      
  hence kn: "k < m" by auto
  let ?gso = "(\<lambda>i j. \<mu> i j \<cdot>\<^sub>v gso j)" 
  have k: "k < i \<Longrightarrow> i < m \<Longrightarrow> lam i = 0" for i
    using Greatest_le_nat[of ?P i m, folded k_def] by auto
  define l where "l = lam k" 
  from Pk have l: "l \<noteq> 0" unfolding l_def by auto
  define idx where "idx = [0 ..< k]" 
  have idx: "\<And> i. i \<in> set idx \<Longrightarrow> i < k" "\<And> i. i \<in> set idx \<Longrightarrow> i < m"  unfolding idx_def using kn by auto
  from Pk have split: "[0 ..< m] = idx @ [k] @ [Suc k ..< m]" unfolding idx_def
    by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
        upt_rec zero_less_Suc)  
  define gg where "gg = sumlist 
    (map (\<lambda>i. of_int (lam i) \<cdot>\<^sub>v fs ! i) idx) + of_int l \<cdot>\<^sub>v sumlist (map (\<lambda>j. \<mu> k j \<cdot>\<^sub>v gso j) idx)" 
  have "h = sumlist ?vs" unfolding in_L ..
  also have "\<dots> = sumlist ((map ?f idx @ [?f k]) @ map ?f [Suc k ..< m])" unfolding split by auto
  also have "\<dots> = sumlist (map ?f idx @ [?f k]) + sumlist (map ?f [Suc k ..< m])" 
    by (rule sumlist_append, auto intro!: f_carrier, insert Pk idx, auto)
  also have "sumlist (map ?f [Suc k ..< m]) = 0\<^sub>v n" by (rule sumlist_neutral, auto simp: k)
  also have "sumlist (map ?f idx @ [?f k]) = sumlist (map ?f idx) + ?f k" 
    by (subst sumlist_append, auto intro!: f_carrier, insert Pk idx, auto)
  also have "fs ! k = sumlist (map (?gso k) [0..<Suc k])" using fi_is_sum_of_mu_gso[OF kn] by simp
  also have "\<dots> = sumlist (map (?gso k) idx @ [gso k])" by (simp add: \<mu>.simps[of k k] idx_def)
  also have "\<dots> = sumlist (map (?gso k) idx) + gso k" 
    by (subst sumlist_append, auto intro!: f_carrier, insert Pk idx, auto)
  also have "of_int (lam k) \<cdot>\<^sub>v \<dots> = of_int (lam k) \<cdot>\<^sub>v (sumlist (map (?gso k) idx)) 
    + of_int (lam k) \<cdot>\<^sub>v gso k" 
    unfolding idx_def
    by (rule smult_add_distrib_vec[OF sumlist_carrier], auto intro!: gso_carrier, insert kn, auto)
  finally have "h = sumlist (map ?f idx) +
       (of_int (lam k) \<cdot>\<^sub>v sumlist (map (?gso k) idx) + of_int (lam k) \<cdot>\<^sub>v gso k) + 0\<^sub>v n " by simp 
  also have "\<dots> = gg + of_int l \<cdot>\<^sub>v gso k" unfolding gg_def l_def
    by (rule eq_vecI, insert idx kn, auto simp: sumlist_vec_index,
      subst index_add_vec, auto simp: sumlist_dim kn, subst sumlist_dim, auto)
  finally have hgg: "h = gg + of_int l \<cdot>\<^sub>v gso k" .      
  let ?k = "[0 ..< k]" 
  define R where "R = {gg. \<exists> nu. gg = sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)}" 
  {
    fix nu
    have "dim_vec (sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)) = n" 
      by (rule sumlist_dim, insert kn, auto simp: idx_def)
  } note dim_nu[simp] = this
  define kk where "kk = ?k" 
  {
    fix v
    assume "v \<in> R"
    then obtain nu where v: "v = sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)" unfolding R_def by auto
    have "dim_vec v = n" unfolding gg_def v by simp
  } note dim_R = this
  {
    fix v1 v2
    assume "v1 \<in> R" "v2 \<in> R" 
    then obtain nu1 nu2 where v1: "v1 = sumlist (map (\<lambda> i. nu1 i \<cdot>\<^sub>v gso i) idx)" and
      v2: "v2 = sumlist (map (\<lambda> i. nu2 i \<cdot>\<^sub>v gso i) idx)"
      unfolding R_def by auto
    have "v1 + v2 \<in> R" unfolding R_def
      by (standard, rule exI[of _ "\<lambda> i. nu1 i + nu2 i"], unfold v1 v2, rule eq_vecI, 
        (subst sumlist_vec_index, insert idx, auto intro!: gso_carrier simp: o_def)+, 
        unfold sum_list_addf[symmetric], induct idx, auto simp: algebra_simps)
  } note add_R = this
  have "gg \<in> R" unfolding gg_def
  proof (rule add_R)
    show "of_int l \<cdot>\<^sub>v sumlist (map (\<lambda>j. \<mu> k j \<cdot>\<^sub>v gso j) idx) \<in> R" 
      unfolding R_def
      by (standard, rule exI[of _ "\<lambda>i. of_int l * \<mu> k i"], rule eq_vecI,
       (subst sumlist_vec_index, insert idx, auto intro!: gso_carrier simp: o_def)+, 
       induct idx, auto simp: algebra_simps)
    show "sumlist (map ?f idx) \<in> R" using idx
    proof (induct idx)
      case Nil
      show ?case by (simp add: R_def, intro exI[of _ "\<lambda> i. 0"], rule eq_vecI,
        (subst sumlist_vec_index, insert idx, auto intro!: gso_carrier simp: o_def)+, 
        induct idx, auto)
    next      
      case (Cons i idxs)
      have "sumlist (map ?f (i # idxs)) = sumlist ([?f i] @ map ?f idxs)" by simp
      also have "\<dots> = ?f i + sumlist (map ?f idxs)" 
        by (subst sumlist_append, insert Cons(3), auto intro!: f_carrier)
      finally have id: "sumlist (map ?f (i # idxs)) = ?f i + sumlist (map ?f idxs)" .
      show ?case unfolding id
      proof (rule add_R[OF _ Cons(1)[OF Cons(2-3)]])
        from Cons(2-3) have i: "i < m" "i < k" by auto
        hence idx_split: "idx = [0 ..< Suc i] @ [Suc i ..< k]" unfolding idx_def 
          by (metis Suc_lessI append_Nil2 less_imp_add_positive upt_add_eq_append upt_rec zero_le)
        {
          fix j
          assume j: "j < n" 
          define idxs where "idxs = [0 ..< Suc i]"
          let ?f = "\<lambda> x. ((if x < Suc i then of_int (lam i) * \<mu> i x else 0) \<cdot>\<^sub>v gso x) $ j" 
          have "(\<Sum>x\<leftarrow>idx. ?f x) = (\<Sum>x\<leftarrow>[0 ..< Suc i]. ?f x) + (\<Sum>x\<leftarrow> [Suc i ..< k]. ?f x)" 
            unfolding idx_split by auto
          also have "(\<Sum>x\<leftarrow> [Suc i ..< k]. ?f x) = 0" by (rule sum_list_neutral, insert j kn, auto)          
          also have "(\<Sum>x\<leftarrow>[0 ..< Suc i]. ?f x) = (\<Sum>x\<leftarrow>idxs. of_int (lam i) * (\<mu> i x \<cdot>\<^sub>v gso x) $ j)" 
            unfolding idxs_def by (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl], 
                subst index_smult_vec, insert j i kn, auto)
          also have "\<dots> = of_int (lam i) * ((\<Sum>x\<leftarrow>[0..<Suc i]. (\<mu> i x \<cdot>\<^sub>v gso x) $ j))" 
            unfolding idxs_def[symmetric] by (induct idxs, auto simp: algebra_simps)
          finally have "(\<Sum>x\<leftarrow>idx. ?f x) = of_int (lam i) * ((\<Sum>x\<leftarrow>[0..<Suc i]. (\<mu> i x \<cdot>\<^sub>v gso x) $ j))" 
            by simp
        } note main = this
        show "?f i \<in> R" unfolding fi_is_sum_of_mu_gso[OF i(1)] R_def
          apply (standard, rule exI[of _ "\<lambda> j. if j < Suc i then of_int (lam i) * \<mu> i j else 0"], rule eq_vecI)
           apply (subst sumlist_vec_index, insert idx i, auto intro!: gso_carrier sumlist_dim simp: o_def)
          apply (subst index_smult_vec, subst sumlist_dim, auto) 
          apply (subst sumlist_vec_index, auto, insert idx i main, auto simp: o_def)
        done
      qed auto
    qed
  qed
  then obtain nu where gg: "gg = sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)" unfolding R_def by auto
  let ?ff = "sumlist (map (\<lambda>i. nu i \<cdot>\<^sub>v gso i) idx) + of_int l \<cdot>\<^sub>v gso k" 
  define hh where "hh = (\<lambda> i. (if i < k then nu i else of_int l))" 
  let ?hh = "sumlist (map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< Suc k])" 
  have ffhh: "?hh = sumlist (map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< k] @ [hh k \<cdot>\<^sub>v gso k])" 
    by simp
  also have "\<dots> = sumlist (map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< k]) + sumlist [hh k \<cdot>\<^sub>v gso k]" 
    by (rule sumlist_append, insert kn, auto)
  also have "sumlist [hh k \<cdot>\<^sub>v gso k] = hh k \<cdot>\<^sub>v gso k" using kn by auto
  also have "\<dots> = of_int l \<cdot>\<^sub>v gso k" unfolding hh_def by auto
  also have "map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< k] = map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) [0 ..< k]" 
    by (rule map_cong, auto simp: hh_def)
  finally have ffhh: "?ff = ?hh" by (simp add: idx_def)
  from hgg[unfolded gg] 
  have h: "h = ?ff" by auto
  have "gso k \<bullet> gso k \<le> 1 * (gso k \<bullet> gso k)" by simp
  also have "\<dots> \<le> of_int (l * l) * (gso k \<bullet> gso k)" 
  proof (rule mult_right_mono)
    from l have "l * l \<ge> 1" by (meson eq_iff int_one_le_iff_zero_less mult_le_0_iff not_le)
    thus "1 \<le> (of_int (l * l) :: 'a)" by presburger     
    show "0 \<le> gso k \<bullet> gso k" by (rule scalar_prod_ge_0)
  qed
  also have "\<dots> = 0 + of_int (l * l) * (gso k \<bullet> gso k)" by simp
  also have "\<dots> \<le> sum_list (map (\<lambda> i. (nu i * nu i) * (gso i \<bullet> gso i)) idx) + of_int (l * l) * (gso k \<bullet> gso k)" 
    by (rule add_right_mono, rule sum_list_nonneg, auto, rule mult_nonneg_nonneg, auto simp: scalar_prod_ge_0)
  also have "map (\<lambda> i. (nu i * nu i) * (gso i \<bullet> gso i)) idx = map (\<lambda> i. hh i * hh i * (gso i \<bullet> gso i)) [0..<k]" 
    unfolding idx_def by (rule map_cong, auto simp: hh_def) 
  also have "of_int (l * l) = hh k * hh k" unfolding hh_def by auto
  also have "(\<Sum>i\<leftarrow>[0..<k]. hh i * hh i * (gso i \<bullet> gso i)) + hh k * hh k * (gso k \<bullet> gso k)
     = (\<Sum>i\<leftarrow>[0..<Suc k]. hh i * hh i * (gso i \<bullet> gso i))" by simp
  also have "\<dots> = ?hh \<bullet> ?hh" by (rule sym, rule scalar_prod_lincomb_gso, insert kn, auto)
  also have "\<dots> = ?ff \<bullet> ?ff" by (simp add: ffhh)
  also have "\<dots> = h \<bullet> h" unfolding h ..
  finally show ?thesis using kn unfolding sq_norm_vec_as_cscalar_prod by auto
qed
  
lemma fs0_gso0: "0 < m \<Longrightarrow> fs ! 0 = gso 0" 
  unfolding gso.simps[of 0] using f_dim[of 0] arg_cong[OF assm(3), of hd] len_fs 
  by (cases fs, auto simp add: upt_rec)
   
(* Theorem 16.9 
  (bound in textbook looks better as it uses 2^((n-1)/2), but this difference
  is caused by the fact that we here we look at the squared norms) *)
lemma weakly_reduced_imp_short_vector: assumes "weakly_reduced \<alpha> m vs"
  and in_L: "h \<in> lattice_of fs - {0\<^sub>v n}" and \<alpha>_pos:"\<alpha> \<ge> 1"
shows "fs \<noteq> [] \<and> sq_norm (fs ! 0) \<le> \<alpha>^(m-1) * sq_norm h"
proof -
  from gram_schmidt_short_vector[OF in_L] obtain i where 
    i: "i < m" and le: "sq_norm (gso i) \<le> sq_norm h" by auto
  have small: "sq_norm (fs ! 0) \<le> \<alpha>^i * sq_norm (gso i)" using i
  proof (induct i)
    case 0
    show ?case unfolding fs0_gso0[OF 0] by auto
  next
    case (Suc i)
    hence "sq_norm (fs ! 0) \<le> \<alpha>^i * sq_norm (gso i)" by auto
    also have "\<dots> \<le> \<alpha>^i * (\<alpha> * (sq_norm (gso (Suc i))))" 
      using reduced_vs_E[OF assms(1) le_refl Suc(2)] \<alpha>_pos by auto
    finally show ?case unfolding class_semiring.nat_pow_Suc[of \<alpha> i] by auto
  qed
  also have "\<dots> \<le> \<alpha>^(m-1) * sq_norm h" 
    by (rule mult_mono[OF power_increasing le], insert i \<alpha>_pos, auto)
  finally show ?thesis using i assm by (cases fs, auto)
qed

lemma sq_norm_pos: assumes j: "j < m" 
  shows "sq_norm (vs ! j) > 0" 
proof -
  have len_vs: "length vs = m" using main_connect(2) by simp
  have "corthogonal vs" by (rule gram_schmidt)
  from corthogonalD[OF this, unfolded len_vs, OF j j]
  have "sq_norm (vs ! j) \<noteq> 0" by (simp add: sq_norm_vec_as_cscalar_prod)    
  moreover have "sq_norm (vs ! j) \<ge> 0" by auto
  ultimately show "0 < sq_norm (vs ! j)" by auto
qed

lemma Gramian_determinant: assumes k: "k \<le> m" 
shows "Gramian_determinant fs k = (\<Prod> j<k. sq_norm (vs ! j))"
  "Gramian_determinant fs k > 0" 
proof -
  define Gk where "Gk = mat k n (\<lambda> (i,j). fs ! i $ j)" 
  have Gk: "Gk \<in> carrier_mat k n" unfolding Gk_def by auto
  define Mk where "Mk = mat k k (\<lambda> (i,j). \<mu> i j)" 
  have Mk_\<mu>: "i < k \<Longrightarrow> j < k \<Longrightarrow> Mk $$ (i,j) = \<mu> i j" for i j
    unfolding Mk_def using k by auto
  have Mk: "Mk \<in> carrier_mat k k" and [simp]: "dim_row Mk = k" "dim_col Mk = k" unfolding Mk_def by auto
  have "det Mk = prod_list (diag_mat Mk)" 
    by (rule det_lower_triangular[OF _ Mk], auto simp: Mk_\<mu> \<mu>.simps)
  also have "\<dots> = 1" 
    by (rule prod_list_neutral, auto simp: diag_mat_def Mk_\<mu> \<mu>.simps)
  finally have detMk: "det Mk = 1" .
  define Gsk where "Gsk = mat k n (\<lambda> (i,j). vs ! i $ j)" 
  have Gsk: "Gsk \<in> carrier_mat k n" unfolding Gsk_def by auto
  have Gsk': "Gsk\<^sup>T \<in> carrier_mat n k" using Gsk by auto
  have len_vs: "length vs = m" using main_connect(2) by simp
  let ?Rn = "carrier_vec n" 
  have id: "Gk = Mk * Gsk" 
  proof (rule eq_matI)
    from Gk Mk Gsk 
    have dim: "dim_row Gk = k" "dim_row (Mk * Gsk) = k" "dim_col Gk = n" "dim_col (Mk * Gsk) = n" by auto
    from dim show "dim_row Gk = dim_row (Mk * Gsk)" "dim_col Gk = dim_col (Mk * Gsk)" by auto
    fix i j
    assume "i < dim_row (Mk * Gsk)" "j < dim_col (Mk * Gsk)"     
    hence ij: "i < k" "j < n" and i: "i < m" using dim k by auto    
    have Gi: "fs ! i \<in> ?Rn" using i by simp
    have "Gk $$ (i, j) = fs ! i $ j" unfolding Gk_def using ij k Gi by auto
    also have "... = FF $$ (i,j)" using ij i by simp
    also have "FF = M * Fs" by (rule matrix_equality)
    also have "\<dots> $$ (i,j) = row M i \<bullet> col Fs j" 
      by (rule index_mult_mat(1), insert i ij, auto simp: mat_of_rows_list_def)
    also have "row M i = vec m (\<lambda> j. if j < k then Mk $$ (i,j) else 0)" 
      (is "_ = vec m ?Mk") 
      unfolding Mk_def using ij i
      by (auto simp: mat_of_rows_list_def \<mu>.simps)
    also have "col Fs j = vec m (\<lambda> i'. if i' < k then Gsk $$ (i',j) else (Fs $$ (i',j)))" 
      (is "_ = vec m ?Gsk") 
      unfolding Gsk_def using ij i len_vs by (auto simp: mat_of_rows_def)
    also have "vec m ?Mk \<bullet> vec m ?Gsk = (\<Sum> i \<in> {0 ..< m}. ?Mk i * ?Gsk i)" 
      unfolding scalar_prod_def by auto
    also have "\<dots> = (\<Sum> i \<in> {0 ..< k} \<union> {k ..< m}. ?Mk i * ?Gsk i)"
      by (rule sum.cong, insert k, auto)
    also have "\<dots> = (\<Sum> i \<in> {0 ..< k}. ?Mk i * ?Gsk i) + (\<Sum> i \<in> {k ..< m}. ?Mk i * ?Gsk i)" 
      by (rule sum.union_disjoint, auto)
    also have "(\<Sum> i \<in> {k ..< m}. ?Mk i * ?Gsk i) = 0" 
      by (rule sum.neutral, auto)
    also have "(\<Sum> i \<in> {0 ..< k}. ?Mk i * ?Gsk i) = (\<Sum> i' \<in> {0 ..< k}. Mk $$ (i,i') * Gsk $$ (i',j))"
      by (rule sum.cong, auto)
    also have "\<dots> = row Mk i \<bullet> col Gsk j" unfolding scalar_prod_def using ij 
      by (auto simp: Gsk_def Mk_def)
    also have "\<dots> = (Mk * Gsk) $$ (i, j)" using ij Mk Gsk by simp
    finally show "Gk $$ (i, j) = (Mk * Gsk) $$ (i, j)" by simp
  qed
  have cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by auto
  have "Gramian_determinant fs k = det (Gk * Gk\<^sup>T)" 
    unfolding Gramian_determinant_def Gramian_matrix_def Let_def
    by (rule arg_cong[of _ _ det], rule cong, insert k, auto simp: Gk_def assm(3)) 
  also have "Gk\<^sup>T = Gsk\<^sup>T * Mk\<^sup>T" (is "_ = ?TGsk * ?TMk") unfolding id 
    by (rule transpose_mult[OF Mk Gsk])
  also have "Gk = Mk * Gsk" by fact
  also have "\<dots> * (?TGsk * ?TMk) = Mk * (Gsk * (?TGsk * ?TMk))" 
    by (rule assoc_mult_mat[OF Mk Gsk, of _ k], insert Gsk Mk, auto)
  also have "det \<dots> = det Mk * det (Gsk * (?TGsk * ?TMk))" 
    by (rule det_mult[OF Mk], insert Gsk Mk, auto)
  also have "\<dots> = det (Gsk * (?TGsk * ?TMk))" using detMk by simp
  also have "Gsk * (?TGsk * ?TMk) = (Gsk * ?TGsk) * ?TMk" 
    by (rule assoc_mult_mat[symmetric, OF Gsk], insert Gsk Mk, auto)
  also have "det \<dots> = det (Gsk * ?TGsk) * det ?TMk" 
    by (rule det_mult, insert Gsk Mk, auto)
  also have "\<dots> = det (Gsk * ?TGsk)" using detMk det_transpose[OF Mk] by simp
  also have "Gsk * ?TGsk = mat k k (\<lambda> (i,j). if i = j then sq_norm (vs ! j) else 0)" (is "_ = ?M")
  proof (rule eq_matI)
    show "dim_row (Gsk * ?TGsk) = dim_row ?M" unfolding Gsk_def by auto
    show "dim_col (Gsk * ?TGsk) = dim_col ?M" unfolding Gsk_def by auto
    fix i j
    assume "i < dim_row ?M" "j < dim_col ?M" 
    hence ij: "i < k" "j < k" and ijn: "i < m" "j < m" using k by auto
    {
      fix i
      assume "i < k" 
      hence "i < m" using k by auto
      hence Gs: "vs ! i \<in> ?Rn" using len_vs vs(1) by auto
      have "row Gsk i = vs ! i" unfolding row_def Gsk_def
        by (rule eq_vecI, insert Gs \<open>i < k\<close>, auto)
    } note row = this
    have "(Gsk * ?TGsk) $$ (i,j) = row Gsk i \<bullet> row Gsk j" using ij Gsk by auto
    also have "\<dots> = vs ! i \<bullet>c vs ! j" using row ij by simp
    also have "\<dots> = (if i = j then sq_norm (vs ! j) else 0)" 
    proof (cases "i = j")
      assume "i = j" 
      thus ?thesis by (simp add: sq_norm_vec_as_cscalar_prod) 
    next
      assume "i \<noteq> j" 
      have "corthogonal vs" by (rule gram_schmidt)
      from \<open>i \<noteq> j\<close> corthogonalD[OF this, unfolded len_vs, OF ijn]
      show ?thesis by auto
    qed
    also have "\<dots> = ?M $$ (i,j)" using ij by simp
    finally show "(Gsk * ?TGsk) $$ (i,j) = ?M $$ (i,j)" .
  qed
  also have "det ?M = prod_list (diag_mat ?M)" 
    by (rule det_upper_triangular, auto)
  also have "diag_mat ?M = map (\<lambda> j. sq_norm (vs ! j)) [0 ..< k]" unfolding diag_mat_def by auto
  also have "prod_list \<dots> = (\<Prod> j < k. sq_norm (vs ! j))"
    by (subst prod.distinct_set_conv_list[symmetric], force, rule prod.cong, auto) 
  finally show "Gramian_determinant fs k = (\<Prod>j<k. \<parallel>vs ! j\<parallel>\<^sup>2)" .
  also have "\<dots> > 0" 
    by (rule prod_pos, intro ballI sq_norm_pos, insert k, auto)
  finally show "0 < Gramian_determinant fs k" by auto
qed
end
end
end
end

lemma prod_list_le_mono: fixes us :: "'a :: {linordered_nonzero_semiring,ordered_ring} list" 
  assumes "length us = length vs" 
  and "\<And> i. i < length vs \<Longrightarrow> 0 \<le> us ! i \<and> us ! i \<le> vs ! i" 
shows "0 \<le> prod_list us \<and> prod_list us \<le> prod_list vs" 
  using assms 
proof (induction us vs rule: list_induct2)
  case (Cons u us v vs)
  have "0 \<le> prod_list us \<and> prod_list us \<le> prod_list vs" 
    by (rule Cons.IH, insert Cons.prems[of "Suc i" for i], auto)
  moreover have "0 \<le> u \<and> u \<le> v" using Cons.prems[of 0] by auto
  ultimately show ?case by (auto intro: mult_mono)
qed simp

lemma lattice_of_of_int: assumes G: "set F \<subseteq> carrier_vec n" 
  and "f \<in> vec_module.lattice_of n F"     
shows "map_vec rat_of_int f \<in> vec_module.lattice_of n (map (map_vec of_int) F)" 
  (is "?f \<in> vec_module.lattice_of _ ?F")
proof -
  let ?sl = "abelian_monoid.sumlist (module_vec TYPE('a::semiring_1) n)" 
  note d = vec_module.lattice_of_def
  note dim = vec_module.sumlist_dim
  note sumlist_vec_index = vec_module.sumlist_vec_index
  from G have Gi: "\<And> i. i < length F \<Longrightarrow> F ! i \<in> carrier_vec n" by auto
  from Gi have Gid: "\<And> i. i < length F \<Longrightarrow> dim_vec (F ! i) = n" by auto
  from assms(2)[unfolded d]
  obtain c where 
    ffc: "f = ?sl (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v F ! i) [0..<length F])" (is "_ = ?g") by auto   
  have "?f = ?sl (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ?F ! i) [0..<length ?F])" (is "_ = ?gg")
  proof -
    have d1[simp]: "dim_vec ?g = n" by (subst dim, auto simp: Gi)
    have d2[simp]: "dim_vec ?gg = n" unfolding length_map by (subst vec_module.sumlist_dim, auto simp: Gi G)
    show ?thesis
      unfolding ffc length_map
      apply (rule eq_vecI)
       apply (insert d1 d2, auto)[2]
      apply (subst (1 2) sumlist_vec_index, auto simp: o_def Gi G)
      apply (unfold of_int_hom.hom_sum_list)
      apply (intro arg_cong[of _ _ sum_list] map_cong)
        by (auto simp: G Gi, (subst index_smult_vec, simp add: Gid)+,
         subst index_map_vec, auto simp: Gid)
  qed
  thus "?f \<in> vec_module.lattice_of n ?F" unfolding d by auto
qed


(* Theorem 16.6, difficult part *)
lemma Hadamard's_inequality: 
  fixes A::"real mat"
  assumes A: "A \<in> carrier_mat n n" 
  shows  "abs (det A) \<le> sqrt (prod_list (map sq_norm (rows A)))" 
proof -
  interpret gso: gram_schmidt n "TYPE(real)" .
  let ?us = "map (row A) [0 ..< n]" 
  have len: "length ?us = n" by simp
  have us: "set ?us \<subseteq> carrier_vec n" using A by auto
  obtain vs where main: "snd (gso.main ?us) = vs" by force
  show ?thesis
  proof (cases "carrier_vec n \<subseteq> gso.span (set ?us)")
    case True
    with us len have basis: "gso.basis_list ?us" unfolding gso.basis_list_def by auto
    note conn = gso.basis_list_imp_lin_indpt_list[OF basis] len main
    note gram = gso.gram_schmidt[OF conn]
    note main = gso.main_connect[OF conn]
    from main have len_vs: "length vs = n" by simp
    have last: "0 \<le> prod_list (map sq_norm vs) \<and> prod_list (map sq_norm vs) \<le> prod_list (map sq_norm ?us)" 
    proof (rule prod_list_le_mono, force simp: main(2), unfold length_map length_upt)
      fix i
      assume "i < n - 0" 
      hence i: "i < n" by simp
      have vsi: "map sq_norm vs ! i = sq_norm (vs ! i)" using main(2) i by simp
      have usi: "map sq_norm ?us ! i = sq_norm (row A i)" using i by simp
      have zero: "0 \<le> sq_norm (vs ! i)" by auto
      have le: "sq_norm (vs ! i) \<le> sq_norm (row A i)" using gso.sq_norm_gso_le_f[OF conn i]
        unfolding main(2) using i by simp
      show "0 \<le> map sq_norm vs ! i \<and> map sq_norm vs ! i \<le> map sq_norm ?us ! i" 
        unfolding vsi usi using zero le by auto
    qed
    have Fs: "gso.Fs ?us \<in> carrier_mat n n" by auto
    have A_Fs: "A = gso.Fs ?us" 
      by (rule eq_matI, subst gso.FF_index[OF conn], insert A, auto)
    hence "abs (det A) = abs (det (gso.Fs ?us))" by simp
    (* the following three steps are based on a discussion with Bertram Felgenhauer *)
    also have "\<dots> = abs (sqrt (det (gso.Fs ?us) * det (gso.Fs ?us)))" by simp
    also have "det (gso.Fs ?us) * det (gso.Fs ?us) = det (gso.Fs ?us) * det (gso.Fs ?us)\<^sup>T" 
      unfolding det_transpose[OF Fs] ..
    also have "\<dots> = det (gso.Fs ?us * (gso.Fs ?us)\<^sup>T)" 
      by (subst det_mult[OF Fs], insert Fs, auto)
    also have "\<dots> = gso.Gramian_determinant ?us n" 
      unfolding gso.Gramian_matrix_def gso.Gramian_determinant_def Let_def A_Fs[symmetric]
      by (rule arg_cong[of _ _ det], rule arg_cong2[of _ _ _ _ "( * )"], insert A, auto)
    also have "\<dots> = (\<Prod>j \<in> set [0 ..< n]. \<parallel>vs ! j\<parallel>\<^sup>2)" unfolding gso.Gramian_determinant[OF conn le_refl] 
      by (rule prod.cong, auto)
    also have "\<dots> = prod_list (map (\<lambda> i. sq_norm (vs ! i)) [0 ..< n])"
      by (subst prod.distinct_set_conv_list, auto)
    also have "map (\<lambda> i. sq_norm (vs ! i)) [0 ..< n] = map sq_norm vs" 
      using len_vs by (intro nth_equalityI, auto)
    also have "abs (sqrt (prod_list \<dots>)) \<le> sqrt (prod_list (map sq_norm ?us))" 
      using last by simp
    also have "?us = rows A" unfolding rows_def using A by simp
    finally show ?thesis .
  next
    case False
    from mat_of_rows_rows[unfolded rows_def,of A] A gram_schmidt.non_span_det_zero[OF len False us]
    have zero: "det A = 0" by auto
    have ge: "prod_list (map sq_norm (rows A)) \<ge> 0" 
      by (rule prod_list_nonneg, auto simp: sq_norm_vec_ge_0)
    show ?thesis unfolding zero using ge by simp
  qed
qed


definition "gram_schmidt_wit = gram_schmidt.main" 
lemmas gram_schmidt_wit = gram_schmidt.weakly_reduced_imp_short_vector[folded gram_schmidt_wit_def]
declare gram_schmidt.adjuster_wit.simps[code]
declare gram_schmidt.sub2_wit.simps[code]
declare gram_schmidt.main_def[code]
      
definition gram_schmidt_int :: "nat \<Rightarrow> int vec list \<Rightarrow> rat list list \<times> rat vec list" where
  "gram_schmidt_int n us = gram_schmidt_wit n (map (map_vec of_int) us)" 

lemma snd_gram_schmidt_int : "snd (gram_schmidt_int n us) = gram_schmidt n (map (map_vec of_int) us)"
  unfolding gram_schmidt_int_def gram_schmidt_wit_def gram_schmidt.gso_connect by metis

(* Faster implementation for trivial conjugatable ordered fields which also avoid recomputations
  of square-norms *)

fun adjuster_triv :: "nat \<Rightarrow> 'a :: trivial_conjugatable_ordered_field vec \<Rightarrow> ('a vec \<times> 'a) list \<Rightarrow> 'a vec"
  where "adjuster_triv n w [] = 0\<^sub>v n"
    |  "adjuster_triv n w ((u,nu)#us) = -(w \<bullet> u)/ nu \<cdot>\<^sub>v u + adjuster_triv n w us"

fun gram_schmidt_sub_triv
  where "gram_schmidt_sub_triv n us [] = us"
  | "gram_schmidt_sub_triv n us (w # ws) = (let u = adjuster_triv n w us + w in
     gram_schmidt_sub_triv n ((u, sq_norm u) # us) ws)"

definition gram_schmidt_triv :: "nat \<Rightarrow> 'a :: trivial_conjugatable_ordered_field vec list \<Rightarrow> ('a vec \<times> 'a) list"
  where "gram_schmidt_triv n ws = rev (gram_schmidt_sub_triv n [] ws)"

lemma adjuster_triv: "adjuster_triv n w (map (\<lambda> x. (x,sq_norm x)) us) = adjuster n w us" 
  by (induct us, auto simp: sq_norm_vec_as_cscalar_prod) 

lemma gram_schmidt_sub_triv: "gram_schmidt_sub_triv n ((map (\<lambda> x. (x,sq_norm x)) us)) ws = 
  map (\<lambda> x. (x, sq_norm x)) (gram_schmidt_sub n us ws)" 
  by (rule sym, induct ws arbitrary: us, auto simp: adjuster_triv o_def Let_def)

lemma gram_schmidt_triv[simp]: "gram_schmidt_triv n ws = map (\<lambda> x. (x,sq_norm x)) (gram_schmidt n ws)" 
  unfolding gram_schmidt_def gram_schmidt_triv_def rev_map[symmetric] 
  by (auto simp: gram_schmidt_sub_triv[symmetric])

end
