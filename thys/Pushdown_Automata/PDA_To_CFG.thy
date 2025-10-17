subsection \<open>PDA to CFG\<close>

text \<open>Starting from a PDA that accepts by empty stack, we construct an equivalent CFG.
The formalization is based on the Lean formalization by Leichtfried\cite{lean}.\<close>

theory PDA_To_CFG
imports
  Pushdown_Automata
  Context_Free_Grammar.Context_Free_Grammar
begin

datatype ('q, 's) pda_nt = Start_sym | Single_sym 'q 's 'q | List_sym 'q "'s list" 'q

context pda begin

abbreviation all_pushes :: "'s list set" where 
  "all_pushes \<equiv> {\<alpha>. \<exists> p q a z. (p, \<alpha>) \<in> \<delta> M q a z} \<union> {\<alpha>.\<exists>p q z. (p, \<alpha>) \<in> \<delta>\<epsilon> M q z}"

abbreviation max_push :: nat where 
  "max_push \<equiv> Suc (Max (length ` all_pushes))"

abbreviation is_allowed_nt :: "('q, 's) pda_nt set" where 
  "is_allowed_nt \<equiv> {List_sym p \<alpha> q| p \<alpha> q. length \<alpha> \<le> max_push} \<union> (\<Union>p Z q. {Single_sym p Z q}) \<union> {Start_sym}"

abbreviation empty_rule :: "'q \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "empty_rule q \<equiv> {(List_sym q [] q, [])}"

abbreviation trans_rule :: "'q \<Rightarrow> 'q \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "trans_rule q\<^sub>0 q\<^sub>1 a Z \<equiv> (\<lambda>(p, \<alpha>). (Single_sym q\<^sub>0 Z q\<^sub>1, [Tm a, Nt (List_sym p \<alpha> q\<^sub>1)])) ` \<delta> M q\<^sub>0 a Z"

abbreviation eps_rule :: "'q \<Rightarrow> 'q \<Rightarrow> 's \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "eps_rule q\<^sub>0 q\<^sub>1 Z \<equiv> (\<lambda>(p, \<alpha>). (Single_sym q\<^sub>0 Z q\<^sub>1, [Nt (List_sym p \<alpha> q\<^sub>1)])) ` \<delta>\<epsilon> M q\<^sub>0 Z"

fun split_rule :: "'q \<Rightarrow> ('q, 's) pda_nt \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "split_rule q (List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1) = {(List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1, [Nt (Single_sym p\<^sub>0 Z q), Nt (List_sym q \<alpha> p\<^sub>1)])}"
| "split_rule _ _ = {}"

abbreviation start_rule :: "'q \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "start_rule q \<equiv> {(Start_sym, [Nt (List_sym (init_state M) [init_symbol M] q)])}"

abbreviation rule_set :: "(('q, 's) pda_nt, 'a) Prods" where
  "rule_set \<equiv> (\<Union>q. empty_rule q) \<union> (\<Union>q p a Z. trans_rule q p a Z) \<union> (\<Union>q p Z. eps_rule q p Z) \<union> 
                 \<Union> {split_rule q nt| q nt. nt \<in> is_allowed_nt} \<union> (\<Union>q. start_rule q)"

definition G :: "(('q, 's) pda_nt,'a) Cfg" where
  "G \<equiv> Cfg rule_set Start_sym"

lemma finite_is_allowed_nt: "finite (is_allowed_nt)"
proof (intro finite_UnI)
  show "finite {List_sym (p :: 'q) (\<alpha> :: 's list) q| p \<alpha> q. length \<alpha> \<le> max_push}"
  proof -
    let ?A = "\<Union>(\<Union>((\<lambda>s. (\<lambda>f. f ` UNIV) ` s) ` ((\<lambda>f. f ` {xs :: 's list. set xs \<subseteq> UNIV \<and> length xs \<le> max_push}) ` (List_sym ` (UNIV :: 'q set)))))"

    have "{List_sym p \<alpha> q| p \<alpha> q. length \<alpha> \<le> max_push} = ?A"
      by auto

    moreover have "finite ?A" (is "finite (\<Union>?B)")
    proof (rule finite_Union)
      show "finite ?B" (is "finite (\<Union>?C)")
      proof (rule finite_Union)
        show "finite ?C" by simp
      next
        show "\<And>M. M \<in> ?C \<Longrightarrow> finite M" 
          using finite_lists_length_le[of UNIV max_push] by force
      qed
    next
      show "\<And>M. M \<in> ?B \<Longrightarrow> finite M" by fastforce
    qed

    ultimately show ?thesis by simp
  qed
next
  show "finite (\<Union>(p :: 'q) (Z :: 's) q. {Single_sym p Z q})"
    by (rule, simp)+
qed simp

lemma finite_split_rule: "finite (split_rule q nt)"
  by (induction q nt rule: split_rule.induct) auto

lemma "finite (Prods G)"
proof -
  have "finite (\<Union>q. empty_rule q)" by simp

  moreover have "finite (\<Union>q p a Z. trans_rule q p a Z)"
    by (simp add: finite_delta)

  moreover have "finite (\<Union>q p Z. eps_rule q p Z)"
    by (simp add: finite_delta_eps)

  moreover have "finite (\<Union> {split_rule q nt| q nt. nt \<in> is_allowed_nt})"
  proof -
    have "{split_rule q nt| q nt. nt \<in> is_allowed_nt} = \<Union> ((\<lambda>f. f ` is_allowed_nt) ` (split_rule ` UNIV))"
      by fastforce

    moreover have "finite (\<Union> (\<Union> ((\<lambda>f. f ` is_allowed_nt) ` (split_rule ` UNIV))))" (is "finite (\<Union>?A)")
    proof (rule finite_Union)
      show "finite ?A" (is "finite (\<Union>?B)")
      proof (rule finite_Union)
        show "finite ?B" by simp
      next
        show "\<And>M. M \<in> ?B \<Longrightarrow> finite M"
          using finite_is_allowed_nt by blast
      qed
    next
      show "\<And>M. M \<in> ?A \<Longrightarrow> finite M"
        by (auto simp: finite_split_rule)
    qed

    ultimately show ?thesis by simp
  qed

  moreover have "finite (\<Union>q. start_rule q)" by simp

  ultimately show ?thesis
    by (simp add: G_def)
qed

lemma split_rule_simp:
  "(A, w) \<in> split_rule q nt \<longleftrightarrow>
   (\<exists>p\<^sub>0 Z \<alpha> p\<^sub>1. nt = (List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1) \<and> 
                A = List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1 \<and> w = [Nt (Single_sym p\<^sub>0 Z q), Nt (List_sym q \<alpha> p\<^sub>1)])"
by (induction q nt rule: split_rule.induct) auto

lemma pda_to_cfg_derive_empty:
  "Prods G \<turnstile> [Nt (List_sym p\<^sub>1 [] p\<^sub>2)] \<Rightarrow> x \<longleftrightarrow> p\<^sub>2 = p\<^sub>1 \<and> x = []"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by auto

lemma finite_all_pushes: "finite all_pushes"
proof -
  let ?A = "(\<lambda>(p, \<alpha>). \<alpha>) ` (\<Union>q a Z. \<delta> M q a Z \<union> (\<Union>q Z. \<delta>\<epsilon> M q Z))" 
  have "all_pushes = ?A" by fast

  moreover have "finite ?A" 
    by (rule, simp add: finite_delta finite_delta_eps)+

  ultimately show ?thesis by simp
qed

lemma push_trans_leq_max:
  "(p, \<alpha>) \<in> \<delta> M q a Z \<Longrightarrow> length \<alpha> \<le> max_push"
proof -
  have "(p, \<alpha>) \<in> \<delta> M q a Z \<Longrightarrow> length \<alpha> \<le> Max (length ` all_pushes)" 
    by (rule Max_ge) (use finite_all_pushes in blast)+ 
  thus "(p, \<alpha>) \<in> \<delta> M q a Z \<Longrightarrow> length \<alpha> \<le> max_push" by simp
qed

lemma push_eps_leq_max:
  "(p, \<alpha>) \<in> \<delta>\<epsilon> M q Z \<Longrightarrow> length \<alpha> \<le> max_push"
proof -
  have "(p, \<alpha>) \<in> \<delta>\<epsilon> M q Z \<Longrightarrow> length \<alpha> \<le> Max (length ` all_pushes)"
    by (rule Max_ge) (use finite_all_pushes in blast)+ 
  thus "(p, \<alpha>) \<in> \<delta>\<epsilon> M q Z \<Longrightarrow> length \<alpha> \<le> max_push" by simp
qed

lemma pda_to_cfg_derive_split:
 "Prods G \<turnstile> [Nt (List_sym p\<^sub>1 (Z#\<alpha>) p\<^sub>2)] \<Rightarrow> w \<longleftrightarrow>
  (\<exists>q. length (Z#\<alpha>) \<le> max_push \<and> w = [Nt (Single_sym p\<^sub>1 Z q), Nt (List_sym q \<alpha> p\<^sub>2)])"
(is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  hence "(List_sym p\<^sub>1 (Z # \<alpha>) p\<^sub>2, w) \<in> rule_set"
    using derive_singleton[of "Prods G" "Nt (List_sym p\<^sub>1 (Z # \<alpha>) p\<^sub>2)" w] by (simp add: G_def)
  thus ?r
    by (auto simp: split_rule_simp)
next
  assume ?r
  then obtain q where len_\<alpha>: "length (Z#\<alpha>) \<le> max_push" and w_def: "w = [Nt (Single_sym p\<^sub>1 Z q), Nt (List_sym q \<alpha> p\<^sub>2)]" by blast
  from w_def have "(List_sym p\<^sub>1 (Z#\<alpha>) p\<^sub>2, w) \<in> split_rule q (List_sym p\<^sub>1 (Z # \<alpha>) p\<^sub>2)" by simp
  with len_\<alpha> have "(List_sym p\<^sub>1 (Z#\<alpha>) p\<^sub>2, w) \<in> \<Union> {split_rule q nt| q nt. nt \<in> is_allowed_nt}"
    by (subst Union_iff) fast
  hence "(List_sym p\<^sub>1 (Z#\<alpha>) p\<^sub>2, w) \<in> rule_set" by simp
  thus ?l
    using derive_singleton[of "Prods G" "Nt (List_sym p\<^sub>1 (Z # \<alpha>) p\<^sub>2)" w] by (simp add: G_def)
qed

lemma pda_to_cfg_derive_single:
"Prods G \<turnstile> [Nt (Single_sym q\<^sub>0 Z q\<^sub>1)] \<Rightarrow> w \<longleftrightarrow> 
   (\<exists>p \<alpha> a. (p, \<alpha>) \<in> \<delta> M q\<^sub>0 a Z \<and> w = [Tm a, Nt (List_sym p \<alpha> q\<^sub>1)]) \<or> 
      (\<exists>p \<alpha>. (p, \<alpha>) \<in> \<delta>\<epsilon> M q\<^sub>0 Z  \<and> w = [Nt (List_sym p \<alpha> q\<^sub>1)])"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by fastforce

lemma pda_to_cfg_derive_start:
"Prods G \<turnstile> [Nt Start_sym] \<Rightarrow> w \<longleftrightarrow> (\<exists>q. w = [Nt (List_sym (init_state M) [init_symbol M] q)])"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by auto

lemma pda_to_cfg_derives_if_stepn:
  assumes "(q, x, \<gamma>) \<leadsto>(n) (p, [], [])"
      and "length \<gamma> \<le> max_push"
    shows "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>* map Tm x"
using assms proof (induction n arbitrary: x p q \<gamma> rule: less_induct)
  case (less n)
  then show ?case proof (cases \<gamma>)
    case Nil
    from less(2) have "(q, x, \<gamma>) \<leadsto>* (p, [], [])"
      using stepn_steps by blast
    with Nil have "q = p \<and> x = []"
      using steps_empty_stack by simp
    with Nil show ?thesis
      using pda_to_cfg_derive_empty by auto
  next
    case (Cons Z \<alpha>)
    with less(2) obtain n' q' x' \<gamma>' where n_def: "n = Suc n'" and 
                                          step1: "(q, x, \<gamma>) \<leadsto> (q', x', \<gamma>')" and 
                                          stepn: "(q', x', \<gamma>') \<leadsto>(n') (p, [], [])"
      using stepn_not_refl_split_first by blast
    from Cons step1 have rule: "(\<exists>\<beta>. x' = x \<and> \<gamma>' = \<beta>@\<alpha> \<and> (q', \<beta>) \<in> \<delta>\<epsilon> M q Z) 
                            \<or> (\<exists>a \<beta>. x = a # x' \<and> \<gamma>' = \<beta>@\<alpha> \<and> (q',\<beta>) \<in> \<delta> M q a Z)" (is "?l \<or> ?r")
      using step\<^sub>1_rule by simp
    show ?thesis proof (rule disjE[OF rule])
      assume ?l
      then obtain \<beta> where x_def: "x' = x" and \<gamma>'_split: "\<gamma>' = \<beta>@\<alpha>" and eps: "(q', \<beta>) \<in> \<delta>\<epsilon> M q Z" by blast
      from stepn \<gamma>'_split obtain p' m\<^sub>1 m\<^sub>2 y y' where x'_def: "x' = y @ y'" and m1_m2_n': "m\<^sub>1 + m\<^sub>2 = n'" 
                  and stepm1: "stepn m\<^sub>1 (q', y, \<beta>) (p', [], [])" and stepm2: "stepn m\<^sub>2 (p', y', \<alpha>) (p, [], [])"
        using split_stack[of n' q' x' \<beta> \<alpha> p] by blast
      from n_def m1_m2_n' have m1_less_n: "m\<^sub>1 < n" by simp
      from n_def m1_m2_n' have m2_less_n: "m\<^sub>2 < n" by simp
      from eps have len_\<beta>: "length \<beta> \<le> max_push"
        using push_eps_leq_max by blast

      from Cons less(3) have "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_split by simp

      moreover from eps have "Prods G \<turnstile> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow> 
                                  [Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_single derive_append[of "Prods G" "[Nt (Single_sym q Z p')]" "[Nt (List_sym q' \<beta> p')]"
                                                            "[Nt (List_sym p' \<alpha> p)]"] by simp
      
      moreover have "Prods G \<turnstile> [Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow>* map Tm y @ [Nt (List_sym p' \<alpha> p)]"
        using derives_append[OF less(1)[OF m1_less_n stepm1 len_\<beta>]] by simp

      moreover from x_def x'_def Cons less(3) have "Prods G \<turnstile> map Tm y @ [Nt (List_sym p' \<alpha> p)] \<Rightarrow>* map Tm x"
        using derives_prepend[OF less(1)[OF m2_less_n stepm2]] by auto

      ultimately show ?thesis by simp
    next
      assume ?r
      then obtain a \<beta> where x_def: "x = a # x'" and \<gamma>'_split: "\<gamma>' = \<beta>@\<alpha>" and trans: "(q', \<beta>) \<in> \<delta> M q a Z" by blast
      from stepn \<gamma>'_split obtain p' m\<^sub>1 m\<^sub>2 y y' where x'_def: "x' = y @ y'" and m1_m2_n': "m\<^sub>1 + m\<^sub>2 = n'" 
                  and stepm1: "stepn m\<^sub>1 (q', y, \<beta>) (p', [], [])" and stepm2: "stepn m\<^sub>2 (p', y', \<alpha>) (p, [], [])"
        using split_stack[of n' q' x' \<beta> \<alpha> p] by blast
      from n_def m1_m2_n' have m1_less_n: "m\<^sub>1 < n" by simp
      from n_def m1_m2_n' have m2_less_n: "m\<^sub>2 < n" by simp
      from trans have len_\<beta>: "length \<beta> \<le> max_push"
        using push_trans_leq_max by blast

      from Cons less(3) have "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_split by simp

      moreover from trans have "Prods G \<turnstile> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow>
                                    [Tm a, Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_single derive_append[of "Prods G" "[Nt (Single_sym q Z p')]" "[Tm a, Nt (List_sym q' \<beta> p')]"
                                                            "[Nt (List_sym p' \<alpha> p)]"] by simp

      moreover have "Prods G \<turnstile> [Tm a, Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow>*
                                      Tm a # map Tm y @ [Nt (List_sym p' \<alpha> p)]"
        using derives_append[OF less(1)[OF m1_less_n stepm1 len_\<beta>]] by (simp add: derives_Tm_Cons)

      moreover from x'_def x_def Cons less(3) have "Prods G \<turnstile> Tm a # map Tm y @ [Nt (List_sym p' \<alpha> p)] \<Rightarrow>* map Tm x"
        using derives_prepend[OF less(1)[OF m2_less_n stepm2], of "Tm a # map Tm y"] by simp

      ultimately show ?thesis by simp
    qed
  qed
qed

(* TODO: CFG? *)
lemma derivel_append_decomp:
  "P \<turnstile> u@v \<Rightarrow>l w \<longleftrightarrow>
  (\<exists>u'. w = u'@v \<and> P \<turnstile> u \<Rightarrow>l u') \<or> (\<exists>u' v'. w = u@v' \<and> u = map Tm u' \<and> P \<turnstile> v \<Rightarrow>l v')"
(is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain A r u1 u2
    where Ar: "(A,r) \<in> P"
      and uv: "u@v = map Tm u1 @ Nt A # u2"
      and w: "w = map Tm u1 @ r @ u2"
    by (auto simp: derivel_iff)
  from uv have case_dist: "(\<exists>s. u2 = s @ v \<and> u = map Tm u1 @ Nt A # s) \<or>
  (\<exists>s. map Tm u1 = u @ s  \<and> v = s @ Nt A # u2)" (is "?h1 \<or> ?h2")
    by (auto simp: append_eq_append_conv2 append_eq_Cons_conv)
  show ?r proof (rule disjE[OF case_dist])
    assume ?h1
    with Ar w show ?thesis by (fastforce simp: derivel_iff)
  next
    assume ?h2
    then obtain s where map_u1_def: "map Tm u1 = u @ s" and v_def: "v = s @ Nt A # u2" by blast
    from map_u1_def obtain u' s' where u_def: "u = map Tm u'" and s_def: "s = map Tm s'"
      using append_eq_map_conv[of u s Tm u1] by auto

    from w map_u1_def s_def have "w = u @ (map Tm s' @ r @ u2)" by simp

    moreover from Ar v_def s_def have "P \<turnstile> v \<Rightarrow>l map Tm s' @ r @ u2"
      using derivel_iff[of P] by blast

    ultimately show ?thesis
      using u_def by blast
  qed
next
  show "?r \<Longrightarrow> ?l"
    by (auto simp add: derivel_append derivel_map_Tm_append)
qed

(* TODO: CFG? *)
lemma split_derivel':
  assumes "P \<turnstile> x#v \<Rightarrow>l(n) u"
  shows "(\<exists>u'. u = u' @ v \<and> P \<turnstile> [x] \<Rightarrow>l(n) u') \<or> (\<exists>w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> u = map Tm w\<^sub>1 @ u\<^sub>2 
                                                    \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2)"
using assms proof (induction n arbitrary: u)
  case (Suc n)
  from Suc(2) obtain w where x_v_deriveln_w: "P \<turnstile> x # v \<Rightarrow>l(n) w" and w_derivel_u: "P \<turnstile> w \<Rightarrow>l u" by auto
  from Suc(1)[OF x_v_deriveln_w] have IH: "(\<exists>u'. w = u' @ v \<and> P \<turnstile> [x] \<Rightarrow>l(n) u') \<or>
  (\<exists>w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> w = map Tm w\<^sub>1 @ u\<^sub>2 \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2)" (is "?l \<or> ?r") .
  show ?case proof (rule disjE[OF IH])
    assume ?l
    then obtain u' where w_def: "w = u' @ v" and x_deriveln_u': "P \<turnstile> [x] \<Rightarrow>l(n) u'" by blast
    from w_def w_derivel_u have "P \<turnstile> u' @ v \<Rightarrow>l u" by simp
    hence case_dist: "(\<exists>u\<^sub>0. u = u\<^sub>0 @ v \<and> P \<turnstile> u' \<Rightarrow>l u\<^sub>0) \<or>
                  (\<exists>u\<^sub>1 u\<^sub>2. u = u' @ u\<^sub>2 \<and> u' = map Tm u\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l u\<^sub>2)" (is "?h1 \<or> ?h2")
      using derivel_append_decomp[of P u' v u] by simp
    show ?thesis proof (rule disjE[OF case_dist])
      assume ?h1
      then obtain u\<^sub>0 where u_def: "u = u\<^sub>0 @ v" and u'_derivel_u0: "P \<turnstile> u' \<Rightarrow>l u\<^sub>0" by blast
      from x_deriveln_u' u'_derivel_u0 have "P \<turnstile> [x] \<Rightarrow>l(Suc n) u\<^sub>0" by auto
      with u_def show ?thesis by blast
    next
      assume ?h2
      then obtain u\<^sub>1 u\<^sub>2 where u_def: "u = u' @ u\<^sub>2" and u'_def: "u' = map Tm u\<^sub>1" and v_derivel_u2: "P \<turnstile> v \<Rightarrow>l u\<^sub>2" by blast
      from x_deriveln_u' u'_def have "P \<turnstile> [x] \<Rightarrow>l(n) map Tm u\<^sub>1" by simp
      with u_def u'_def v_derivel_u2 show ?thesis by fastforce
    qed
  next
    assume ?r
    then obtain w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" and w_def: "w = map Tm w\<^sub>1 @ u\<^sub>2" and 
                                      x_derivelm1_w1: "P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" and v_derivelm2_u2: "P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2" by blast
    from w_def w_derivel_u have "P \<turnstile> map Tm w\<^sub>1 @ u\<^sub>2 \<Rightarrow>l u" by simp
    then obtain u' where u_def: "u = map Tm w\<^sub>1 @ u'" and u2_derivel_u': "P \<turnstile> u\<^sub>2 \<Rightarrow>l u'"
      using derivel_map_Tm_append by blast

    from m1_m2_n have "m\<^sub>1 + Suc m\<^sub>2 = Suc n" by simp

    moreover from v_derivelm2_u2 u2_derivel_u' have "P \<turnstile> v \<Rightarrow>l(Suc m\<^sub>2) u'" by auto

    ultimately show ?thesis
      using u_def x_derivelm1_w1 by blast
  qed
qed simp

(* TODO: CFG? *)
lemma split_derivel:
  assumes "P \<turnstile> x#v \<Rightarrow>l(n) map Tm w"
  shows "\<exists>w\<^sub>1 w\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> w = w\<^sub>1 @ w\<^sub>2 \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) map Tm w\<^sub>2"
proof -
  have case_dist: "(\<exists>u'. map Tm w = u' @ v \<and> P \<turnstile> [x] \<Rightarrow>l(n) u') \<or> (\<exists>w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> map Tm w = map Tm w\<^sub>1 @ u\<^sub>2 
                                                    \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2)" (is "?l \<or> ?r")
    using split_derivel'[OF assms] by simp
  show ?thesis proof (rule disjE[OF case_dist])
    assume ?l
    then obtain u' where map_w_def: "map Tm w = u' @ v" and x_derives_u': "P \<turnstile> [x] \<Rightarrow>l(n) u'" by blast
    from map_w_def obtain w\<^sub>1 w\<^sub>2 where "w = w\<^sub>1 @ w\<^sub>2" and map_w\<^sub>1_def: "map Tm w\<^sub>1 = u'" and "map Tm w\<^sub>2 = v"
      using map_eq_append_conv[of Tm w u' v] by blast

    moreover from x_derives_u' map_w\<^sub>1_def have "P \<turnstile> [x] \<Rightarrow>l(n) map Tm w\<^sub>1" by simp

    moreover have "P \<turnstile> map Tm w\<^sub>2 \<Rightarrow>l(0) map Tm w\<^sub>2" by simp

    ultimately show ?thesis by force
  next
    assume ?r
    then obtain w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" and map_w_def: "map Tm w = map Tm w\<^sub>1 @ u\<^sub>2" 
                                               and x_derivelm1_w1: "P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" and v_derivelm2_u2: "P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2" by blast
    from map_w_def obtain w\<^sub>1' u\<^sub>2' where "w = w\<^sub>1' @ u\<^sub>2'" and "map (Tm :: 'c \<Rightarrow> ('b, 'c) sym) w\<^sub>1 = map Tm w\<^sub>1'" and "u\<^sub>2 = map (Tm :: 'c \<Rightarrow> ('b, 'c) sym) u\<^sub>2'"
      using map_eq_append_conv[of "Tm :: 'c \<Rightarrow> ('b, 'c) sym" w "map Tm w\<^sub>1" u\<^sub>2] by blast
    with m1_m2_n x_derivelm1_w1 v_derivelm2_u2 show ?thesis by auto
  qed                    
qed

lemma pda_to_cfg_steps_if_derivel:
  assumes "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>l(n) map Tm x"
  shows "(q, x, \<gamma>) \<leadsto>* (p, [], [])"
using assms proof (induction n arbitrary: x p q \<gamma> rule: less_induct)
  case (less n)
  then show ?case proof (cases \<gamma>)
    case Nil
    have derives: "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>* map Tm x"
      using derivels_imp_derives[OF relpowp_imp_rtranclp[OF less(2)]] .
    have "p = q \<and> x = []"
    proof -
      from derives_start1[OF derives] obtain \<alpha> where d1: "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow> \<alpha>" and 
                                                        ds: "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm x"
        using derive_singleton by blast
      from Nil d1 have *: "p = q" and \<alpha>_def: "\<alpha> = []"
        using pda_to_cfg_derive_empty by simp_all
      from \<alpha>_def ds have **: "x = []" by simp
      from * ** show ?thesis by simp
    qed
    with Nil show ?thesis
      by (simp add: steps_refl)
  next
    case (Cons Z \<alpha>)
    from less(2) have "n > 0"
      using gr0I by fastforce
    then obtain n' where n_def: "n = Suc n'"
      using not0_implies_Suc by blast
    with less(2) obtain \<gamma>' where l1: "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>l \<gamma>'" and ln': "Prods G \<turnstile> \<gamma>' \<Rightarrow>l(n') map Tm x"
      using relpowp_Suc_E2[of n' "derivel (Prods G)" "[Nt (List_sym q \<gamma> p)]" "map Tm x"] by blast
    from Cons obtain q' where \<gamma>'_def: "\<gamma>' = [Nt (Single_sym q Z q'), Nt (List_sym q' \<alpha> p)]"
      using pda_to_cfg_derive_split derivel_imp_derive[OF l1] by blast
    with ln' have "n' > 0"
      using gr0I by fastforce
    then obtain n'' where n'_def: "n' = Suc n''"
      using not0_implies_Suc by blast
    with ln' \<gamma>'_def obtain \<gamma>'' where l2: "Prods G \<turnstile> [Nt (Single_sym q Z q'), Nt (List_sym q' \<alpha> p)] \<Rightarrow>l \<gamma>''" and
                                      ln'': "Prods G \<turnstile> \<gamma>'' \<Rightarrow>l(n'') map Tm x"
      using relpowp_Suc_E2[of n'' "derivel (Prods G)" "[Nt (Single_sym q Z q'), Nt (List_sym q' \<alpha> p)]" "map Tm x"] by blast
    from l2 obtain \<gamma>''\<^sub>2 where l2': "Prods G \<turnstile> [Nt (Single_sym q Z q')] \<Rightarrow>l \<gamma>''\<^sub>2" and \<gamma>''_split: "\<gamma>'' = \<gamma>''\<^sub>2 @ [Nt (List_sym q' \<alpha> p)]"
      using derivel_Nt_Cons by (metis append.right_neutral) 
    have "(\<exists>q'' \<alpha>'' a. (q'', \<alpha>'') \<in> \<delta> M q a Z \<and> \<gamma>''\<^sub>2 = [Tm a, Nt (List_sym q'' \<alpha>'' q')]) \<or> 
                    (\<exists>q'' \<alpha>''. (q'', \<alpha>'') \<in> \<delta>\<epsilon> M q Z  \<and> \<gamma>''\<^sub>2 = [Nt (List_sym q'' \<alpha>'' q')])"
      using pda_to_cfg_derive_single derivel_imp_derive[OF l2'] by simp
    with \<gamma>''_split have rule: "(\<exists>q'' \<alpha>'' a. (q'', \<alpha>'') \<in> \<delta> M q a Z \<and> 
                                  \<gamma>'' = [Tm a, Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]) \<or> 
                            (\<exists>q'' \<alpha>''. (q'', \<alpha>'') \<in> \<delta>\<epsilon> M q Z  \<and> 
                                  \<gamma>'' = [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)])" (is "?l \<or> ?r") by simp
    show ?thesis proof (rule disjE[OF rule])
      assume ?l
      then obtain q'' \<alpha>'' a where trans: "(q'', \<alpha>'') \<in> \<delta> M q a Z" and 
                                     \<gamma>''_def: "\<gamma>'' = [Tm a, Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]" by blast
      from \<gamma>''_def ln'' obtain x' where x_def: "x = a#x'" and 
                               split: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(n'') map Tm x'"
        using deriveln_Tm_Cons[of n'' "Prods G" a "[Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]" "map Tm x"] by auto
      obtain w\<^sub>1 w\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n''': "m\<^sub>1 + m\<^sub>2 = n''" and x'_def: "x' = w\<^sub>1 @ w\<^sub>2" 
                                    and m1_path: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q')] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" 
                                    and m2_path: "Prods G \<turnstile> [Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(m\<^sub>2) map Tm w\<^sub>2" 
        using split_derivel[OF split] by blast
      from m1_m2_n''' n_def n'_def have m1_lessn: "m\<^sub>1 < n" by simp
      from m1_m2_n''' n_def n'_def have m2_lessn: "m\<^sub>2 < n" by simp

      from trans x_def Cons have "(q, x, \<gamma>) \<leadsto> (q'', x', \<alpha>'' @ \<alpha>)"
        using step\<^sub>1_rule by simp

      moreover from x'_def have "(q'', x', \<alpha>'' @ \<alpha>) \<leadsto>* (q', w\<^sub>2, \<alpha>)"
        using steps_stack_app[OF less(1)[OF m1_lessn m1_path], of \<alpha>] 
              steps_word_app[of q'' w\<^sub>1 "\<alpha>'' @ \<alpha>" q' "[]" \<alpha> w\<^sub>2] by simp

      moreover have "(q', w\<^sub>2, \<alpha>) \<leadsto>* (p, [], [])"
        using less(1)[OF m2_lessn m2_path] .

      ultimately show ?thesis
        unfolding steps_def
        by (meson converse_rtranclp_into_rtranclp rtranclp_trans)
    next
      assume ?r
      then obtain q'' \<alpha>'' where eps: "(q'', \<alpha>'') \<in> \<delta>\<epsilon> M q Z" and  
                                  \<gamma>''_def: "\<gamma>'' = [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]" by blast
      from \<gamma>''_def ln'' have split: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(n'') map Tm x" by simp
      obtain w\<^sub>1 w\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n''': "m\<^sub>1 + m\<^sub>2 = n''" and x_def: "x = w\<^sub>1 @ w\<^sub>2" 
                             and m1_path: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q')] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" 
                             and m2_path: "Prods G \<turnstile> [Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(m\<^sub>2) map Tm w\<^sub>2"
        using split_derivel[OF split] by blast
      from m1_m2_n''' n_def n'_def have m1_lessn: "m\<^sub>1 < n" by simp
      from m1_m2_n''' n_def n'_def have m2_lessn: "m\<^sub>2 < n" by simp

      from eps Cons have "(q, x, \<gamma>) \<leadsto> (q'', x, \<alpha>'' @ \<alpha>)"
        using step\<^sub>1_rule by simp

      moreover from x_def have "(q'', x, \<alpha>'' @ \<alpha>) \<leadsto>* (q', w\<^sub>2, \<alpha>)"
        using steps_stack_app[OF less(1)[OF m1_lessn m1_path], of \<alpha>] 
              steps_word_app[of q'' w\<^sub>1 "\<alpha>'' @ \<alpha>" q' "[]" \<alpha> w\<^sub>2] by simp

      moreover have "(q', w\<^sub>2, \<alpha>) \<leadsto>* (p, [], [])"
        using less(1)[OF m2_lessn m2_path] .

      ultimately show ?thesis
        using step\<^sub>1_steps steps_trans by metis
    qed
  qed
qed

lemma pda_to_cfg: "LangS G = accept_stack" (is "?L = ?P")
proof
  show "?L \<subseteq> ?P"
  proof
    fix x
    assume "x \<in> ?L"
    hence derives: "Prods G \<turnstile> [Nt Start_sym] \<Rightarrow>* map Tm x"
      by (simp add: G_def Lang_def)
    then obtain \<gamma> where fs: "Prods G \<turnstile> [Nt Start_sym] \<Rightarrow> \<gamma>" and ls: "Prods G \<turnstile> \<gamma> \<Rightarrow>* map Tm x"
      using converse_rtranclpE[OF derives] by blast
    from fs obtain q where "\<gamma> = [Nt (List_sym (init_state M) [init_symbol M] q)]"
      using pda_to_cfg_derive_start[of \<gamma>] by blast
    with ls obtain n where "Prods G \<turnstile> [Nt (List_sym (init_state M) [init_symbol M] q)] \<Rightarrow>l(n) map Tm x"
      using derivels_iff_derives[of "Prods G" \<gamma> x] rtranclp_power[of "derivel (Prods G)" \<gamma> "map Tm x"] by blast
    hence "steps (init_state M, x, [init_symbol M]) (q, [], [])"
      using pda_to_cfg_steps_if_derivel by simp
    thus "x \<in> ?P"
      by (auto simp: accept_stack_def)
  qed
next
  show "?P \<subseteq> ?L"
  proof
    fix x
    assume "x \<in> ?P"
    then obtain q where "steps (init_state M, x, [init_symbol M]) (q, [], [])"
      by (auto simp: accept_stack_def)
    then obtain n where "(init_state M, x, [init_symbol M]) \<leadsto>(n) (q, [], [])"
      using stepn_steps by blast

    hence "Prods G \<turnstile> [Nt (List_sym (init_state M) [init_symbol M] q)] \<Rightarrow>* map Tm x"
      using pda_to_cfg_derives_if_stepn by simp

    moreover have "Prods G \<turnstile> [Nt Start_sym] \<Rightarrow> [Nt (List_sym (init_state M) [init_symbol M] q)]"
      using pda_to_cfg_derive_start by simp

    ultimately have "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* map Tm x"
      by (simp add: G_def)

    thus "x \<in> ?L"
      by (simp add: Lang_def)
  qed
qed

end
end