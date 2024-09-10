section \<open>The Zigzag Lemma\<close>
                                                        
theory Zigzag imports Bounding_X

begin                  
          
subsection \<open>Lemma 8.1 (the actual Zigzag Lemma)\<close>

definition "Big_ZZ_8_2 \<equiv> \<lambda>k. (1 + eps k powr (1/2)) \<ge> (1 + eps k) powr (eps k powr (-1/4))"
                                                 
text \<open>An inequality that pops up in the proof of (39)\<close>
definition "Big39 \<equiv> \<lambda>k. 1/2 \<le> (1 + eps k) powr (-2 * eps k powr (-1/2))"

text \<open>Two inequalities that pops up in the proof of (42)\<close>
definition "Big42a \<equiv> \<lambda>k. (1 + eps k)\<^sup>2 / (1 - eps k powr (1/2)) \<le> 1 + 2 * k powr (-1/16)" 

definition "Big42b \<equiv> \<lambda>k. 2 * k powr (-1/16) * k
                        + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / (1 - eps k powr (1/2))
                       \<le> real k powr (19/20)"

definition "Big_ZZ_8_1 \<equiv>
   \<lambda>\<mu> l. Big_Blue_4_1 \<mu> l \<and> Big_Red_5_1 \<mu> l \<and> Big_Red_5_3 \<mu> l \<and> Big_Y_6_5_Bblue l
        \<and> (\<forall>k. k\<ge>l \<longrightarrow> Big_height_upper_bound k \<and> Big_ZZ_8_2 k \<and> k\<ge>16 \<and> Big39 k
                      \<and> Big42a k \<and> Big42b k)"

text \<open>@{term "k\<ge>16"} is for @{text Y_6_5_Red}\<close>


lemma Big_ZZ_8_1:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_ZZ_8_1 \<mu> l"
  using assms Big_Blue_4_1 Big_Red_5_1 Big_Red_5_3 Big_Y_6_5_Bblue
  unfolding Big_ZZ_8_1_def Big_ZZ_8_2_def Big39_def Big42a_def Big42b_def
            eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: eventually_conj_iff eventually_frequently_const_simps)   
  apply (intro conjI strip eventually_all_ge_at_top Big_height_upper_bound; real_asymp)
  done

lemma (in Book) ZZ_8_1:
  assumes big: "Big_ZZ_8_1 \<mu> l" 
  defines "\<R> \<equiv> Step_class {red_step}"
  defines "sum_SS \<equiv> (\<Sum>i\<in>dboost_star. (1 - beta i) / beta i)"
  shows "sum_SS \<le> real (card \<R>) + k powr (19/20)"
proof -
  define pp where "pp \<equiv> \<lambda>i h. if h=1 then min (pee i) (qfun 1)
                          else if pee i \<le> qfun (h-1) then qfun (h-1) 
                          else if pee i \<ge> qfun h then qfun h
                          else pee i"
  define \<Delta> where "\<Delta> \<equiv> \<lambda>i. pee (Suc i) - pee i"
  define \<Delta>\<Delta> where "\<Delta>\<Delta> \<equiv> \<lambda>i h. pp (Suc i) h - pp i h"
  have pp_eq: "pp i h = (if h=1 then min (pee i) (qfun 1)
                          else max (qfun (h-1)) (min (pee i) (qfun h)))" for i h
    using qfun_mono [of "h-1" h] by (auto simp: pp_def max_def)

  define maxh where "maxh \<equiv> nat\<lfloor>2 * ln k / eps k\<rfloor> + 1"  
  have maxh: "\<And>pee. pee\<le>1 \<Longrightarrow> hgt pee \<le> 2 * ln k / eps k" and "k\<ge>16"
    using big l_le_k by (auto simp: Big_ZZ_8_1_def height_upper_bound)
  then have "1 \<le> 2 * ln k / eps k"
    using hgt_gt0 [of 1] by force
  then have "maxh > 1"
    by (simp add: maxh_def eps_gt0)
  have "hgt pee < maxh" if "pee\<le>1"for pee
    using that kn0 maxh[of "pee"] unfolding maxh_def by linarith
  then have hgt_le_maxh: "hgt (pee i) < maxh" for i
    using pee_le1 by auto

  have pp_eq_hgt [simp]: "pp i (hgt (pee i)) = pee i" for i
    using hgt_less_imp_qfun_less [of "hgt (pee i) - 1" "pee i"]  
    using hgt_works [of "pee i"] hgt_gt0 [of "pee i"] kn0 pp_eq by force

  have pp_less_hgt [simp]: "pp i h = qfun h" if "0<h" "h < hgt (pee i)" for h i
  proof (cases "h=1")
    case True
    then show ?thesis
      using hgt_less_imp_qfun_less pp_def that by auto
  next
    case False
    with that show ?thesis
      using alpha_def alpha_ge0 hgt_less_imp_qfun_less pp_eq by force
  qed

  have pp_gt_hgt [simp]: "pp i h = qfun (h-1)" if "h > hgt (pee i)" for h i
    using hgt_gt0 [of "pee i"] kn0 that
    by (simp add: pp_def hgt_le_imp_qfun_ge)

  have \<Delta>0: "\<Delta> i \<ge> 0 \<longleftrightarrow> (\<forall>h>0. \<Delta>\<Delta> i h \<ge> 0)" for i
  proof (intro iffI strip)
    fix h::nat
    assume "0 \<le> \<Delta> i" "0 < h" then show "0 \<le> \<Delta>\<Delta> i h"
      using qfun_mono [of "h-1" h] kn0 by (auto simp: \<Delta>_def \<Delta>\<Delta>_def pp_def) 
  next
    assume "\<forall>h>0. 0 \<le> \<Delta>\<Delta> i h"
    then have "pee i \<le> pp (Suc i) (hgt (pee i))"
      unfolding \<Delta>\<Delta>_def
      by (smt (verit, best) hgt_gt0 pp_eq_hgt)
    then show "0 \<le> \<Delta> i"
      using hgt_less_imp_qfun_less [of "hgt (pee i) - 1" "pee i"]  
      using hgt_gt0 [of "pee i"] kn0
      by (simp add: \<Delta>_def pp_def split: if_split_asm)
  qed

  have sum_pp_aux: "(\<Sum>h=Suc 0..n. pp i h) 
                  = (if hgt (pee i) \<le> n then pee i + (\<Sum>h=1..<n. qfun h) else (\<Sum>h=1..n. qfun h))" 
    if "n>0" for n i
    using that
  proof (induction n)
    case (Suc n)
    show ?case
    proof (cases "n=0")
      case True
      then show ?thesis
        using kn0 hgt_Least [of 1 "pee i"]
        by (simp add: pp_def hgt_le_imp_qfun_ge min_def)
    next
      case False
      with Suc show ?thesis
        by (simp split: if_split_asm) (smt (verit) le_Suc_eq not_less_eq pp_eq_hgt sum.head_if)
    qed
  qed auto
  have sum_pp: "(\<Sum>h=Suc 0..maxh. pp i h) = pee i + (\<Sum>h=1..<maxh. qfun h)" for i
    using \<open>1 < maxh\<close> by (simp add: hgt_le_maxh less_or_eq_imp_le sum_pp_aux)
  have 33: "\<Delta> i = (\<Sum>h=1..maxh. \<Delta>\<Delta> i h)" for i
    by (simp add: \<Delta>\<Delta>_def \<Delta>_def sum_subtractf sum_pp)

  have "(\<Sum>i<halted_point. \<Delta>\<Delta> i h) = 0" 
    if "\<And>i. i\<le>halted_point \<Longrightarrow> h > hgt (pee i)" for h
    using that by (simp add: sum.neutral \<Delta>\<Delta>_def)
  then have B: "(\<Sum>i<halted_point. \<Delta>\<Delta> i h) = 0" if "h \<ge> maxh" for h
    by (meson hgt_le_maxh le_simps le_trans not_less_eq that)
  have "(\<Sum>h=Suc 0..maxh. \<Sum>i<halted_point. \<Delta>\<Delta> i h / alpha h) \<le> (\<Sum>h=Suc 0..maxh. 1)"
  proof (intro sum_mono)
    fix h
    assume "h \<in> {Suc 0..maxh}"
    have "(\<Sum>i<halted_point. \<Delta>\<Delta> i h) \<le> alpha h"
      using qfun_mono [of "h-1" h] kn0
      unfolding \<Delta>\<Delta>_def alpha_def sum_lessThan_telescope [where f = "\<lambda>i. pp i h"]
      by (auto simp: pp_def pee_eq_p0)
    then show "(\<Sum>i<halted_point. \<Delta>\<Delta> i h / alpha h) \<le> 1"
      using alpha_ge0 [of h] by (simp add: divide_simps flip: sum_divide_distrib) 
  qed
  also have "\<dots> \<le> 1 + 2 * ln k / eps k"
    using \<open>maxh > 1\<close> by (simp add: maxh_def)
  finally have 34: "(\<Sum>h=Suc 0..maxh. \<Sum>i<halted_point. \<Delta>\<Delta> i h / alpha h) \<le> 1 + 2 * ln k / eps k" .

  define \<D> where "\<D> \<equiv> Step_class {dreg_step}" 
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}" 
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}" 
  have "dboost_star \<subseteq> \<S>"
    unfolding dboost_star_def \<S>_def dboost_star_def by auto
  have BD_disj: "\<B>\<inter>\<D> = {}" and disj: "\<R>\<inter>\<B> = {}" "\<S>\<inter>\<B> = {}" "\<R>\<inter>\<D> = {}" "\<S>\<inter>\<D> = {}" "\<R>\<inter>\<S> = {}"
    by (auto simp: \<D>_def \<R>_def \<B>_def \<S>_def Step_class_def)

  have [simp]: "finite \<D>" "finite \<B>" "finite \<R>" "finite \<S>"
    using finite_components assms 
    by (auto simp: \<D>_def \<B>_def \<R>_def \<S>_def Step_class_insert_NO_MATCH)
  have "card \<R> < k"
    using red_step_limit by (auto simp: \<R>_def)

  have R52: "pee (Suc i) - pee i \<ge> (1 - eps k) * ((1 - beta i) / beta i) * alpha (hgt (pee i))"
    and beta_gt0: "beta i > 0"
    and R53: "pee (Suc i) \<ge> pee i \<and> beta i \<ge> 1 / (real k)\<^sup>2"
        if "i \<in> \<S>" for i
    using big Red_5_2 that by (auto simp: Big_ZZ_8_1_def Red_5_3 \<B>_def \<S>_def)
  have card\<B>: "card \<B> \<le> l powr (3/4)" and bigY65B: "Big_Y_6_5_Bblue l"
    using big bblue_step_limit by (auto simp: Big_ZZ_8_1_def \<B>_def)

  have \<Delta>\<Delta>_ge0: "\<Delta>\<Delta> i h \<ge> 0" if "i \<in> \<S>" "h \<ge> 1" for i h
    using that R53 [OF \<open>i \<in> \<S>\<close>] by (fastforce simp: \<Delta>\<Delta>_def pp_eq)
  have \<Delta>\<Delta>_eq_0: "\<Delta>\<Delta> i h = 0" if "hgt (pee i) \<le> hgt (pee (Suc i))" "hgt (pee (Suc i)) < h" for h i
    using \<Delta>\<Delta>_def that by fastforce
  define oneminus where "oneminus \<equiv> 1 - eps k powr (1/2)"
  have 35: "oneminus * ((1 - beta i) / beta i)
          \<le> (\<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha h)"   (is "?L \<le> ?R")
    if "i \<in> dboost_star" for i
  proof -
    have "i \<in> \<S>"
      using \<open>dboost_star \<subseteq> \<S>\<close> that by blast
    have [simp]: "real (hgt x - Suc 0) = real (hgt x) - 1" for x
      using hgt_gt0 [of x] by linarith
    have 36: "(1 - eps k) * ((1 - beta i) / beta i) \<le> \<Delta> i / alpha (hgt (pee i))"
      using R52 alpha_gt0 [OF hgt_gt0] beta_gt0 that \<open>dboost_star \<subseteq> \<S>\<close> by (force simp: \<Delta>_def divide_simps)
    have k_big: "(1 + eps k powr (1/2)) \<ge> (1 + eps k) powr (eps k powr (-1/4))"
      using big l_le_k by (auto simp: Big_ZZ_8_1_def Big_ZZ_8_2_def)
    have *: "\<And>x::real. x > 0 \<Longrightarrow> (1 - x powr (1/2)) * (1 + x powr (1/2)) = 1 - x"
      by (simp add: algebra_simps flip: powr_add)
    have "?L = (1 - eps k) * ((1 - beta i) / beta i) / (1 + eps k powr (1/2))"
      using beta_gt0 [OF \<open>i \<in> \<S>\<close>] eps_gt0 [OF kn0] k_big 
      by (force simp: oneminus_def divide_simps *)
    also have "\<dots> \<le> \<Delta> i / alpha (hgt (pee i)) / (1 + eps k powr (1/2))"
      by (intro 36 divide_right_mono) auto
    also have "\<dots> \<le> \<Delta> i / alpha (hgt (pee i)) / (1 + eps k) powr (real (hgt (pee (Suc i))) - hgt (pee i))"
    proof (intro divide_left_mono mult_pos_pos)
      have "real (hgt (pee (Suc i))) - hgt (pee i) \<le> eps k powr (-1/4)"
        using that by (simp add: dboost_star_def)
      then show "(1 + eps k) powr (real (hgt (pee (Suc i))) - real (hgt (pee i))) \<le> 1 + eps k powr (1/2)"
        using k_big by (smt (verit) eps_ge0 powr_mono)
      show "0 \<le> \<Delta> i / alpha (hgt (pee i))"
        by (simp add: \<Delta>0 \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close> alpha_ge0)
      show "0 < (1 + eps k) powr (real (hgt (pee (Suc i))) - real (hgt (pee i)))"
        using eps_gt0 [OF kn0] by auto
    qed (auto simp: add_strict_increasing)
    also have "\<dots> \<le> \<Delta> i / alpha (hgt (pee (Suc i)))"
    proof -
      have "alpha (hgt (pee (Suc i))) \<le> alpha (hgt (pee i)) * (1 + eps k) powr (real (hgt (pee (Suc i))) - real (hgt (pee i)))"
        using eps_gt0[OF kn0] hgt_gt0
        by (simp add: alpha_eq divide_right_mono flip: powr_realpow powr_add)
      moreover have "0 \<le> \<Delta> i"
        by (simp add: \<Delta>0 \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close>)
      moreover have "0 < alpha (hgt (pee (Suc i)))"
        by (simp add: alpha_gt0 hgt_gt0 kn0)
      ultimately show ?thesis
        by (simp add: divide_left_mono)
    qed
    also have "\<dots> \<le> ?R"
      unfolding 33 sum_divide_distrib
    proof (intro sum_mono)
      fix h
      assume h: "h \<in> {1..maxh}"
      show "\<Delta>\<Delta> i h / alpha (hgt (pee (Suc i))) \<le> \<Delta>\<Delta> i h / alpha h"
      proof (cases  "hgt (pee i) \<le> hgt (pee (Suc i)) \<and> hgt (pee (Suc i)) < h")
        case False
        then consider "hgt (pee i) > hgt (pee (Suc i))" | "hgt (pee (Suc i)) \<ge> h"
          by linarith
        then show ?thesis
        proof cases
          case 1
          then show ?thesis
            using R53 \<open>i \<in> \<S>\<close> hgt_mono' kn0 by force
        next
          case 2
          have "alpha h \<le> alpha (hgt (pee (Suc i)))"
            using "2" alpha_mono h by auto
          moreover have "0 \<le> \<Delta>\<Delta> i h"
            using \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close> h by presburger
          moreover have "0 < alpha h"
            using h kn0 by (simp add: alpha_gt0 hgt_gt0)
          ultimately show ?thesis
            by (simp add: divide_left_mono)
        qed
      qed (auto simp: \<Delta>\<Delta>_eq_0)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>now we are able to prove claim 8.2\<close>
  have "oneminus * sum_SS = (\<Sum>i\<in>dboost_star. oneminus * ((1 - beta i) / beta i))"
    using sum_distrib_left sum_SS_def by blast
  also have "\<dots> \<le> (\<Sum>i\<in>dboost_star. \<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha h)"
    by (intro sum_mono 35)
  also have "\<dots> = (\<Sum>h=1..maxh. \<Sum>i\<in>dboost_star. \<Delta>\<Delta> i h / alpha h)"
    using sum.swap by fastforce
  also have "\<dots> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha h)"
    by (intro sum_mono sum_mono2) (auto simp: \<open>dboost_star \<subseteq> \<S>\<close> \<Delta>\<Delta>_ge0 alpha_ge0)
  finally have 82: "oneminus * sum_SS
      \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha h)" .
  \<comment> \<open>leading onto claim 8.3\<close>
  have \<Delta>alpha: "- 1 \<le> \<Delta> i / alpha (hgt (pee i))" if "i \<in> \<R>" for i
    using Y_6_4_Red [of i] \<open>i \<in> \<R>\<close> 
    unfolding \<Delta>_def \<R>_def
    by (smt (verit, best) hgt_gt0 alpha_gt0 divide_minus_left less_divide_eq_1_pos)

  have "(\<Sum>i\<in>\<R>. - (1 + eps k)\<^sup>2) \<le> (\<Sum>i\<in>\<R>. \<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha h)"
  proof (intro sum_mono)
    fix i :: nat
    assume "i \<in> \<R>"
    show "- (1 + eps k)\<^sup>2 \<le> (\<Sum>h = 1..maxh. \<Delta>\<Delta> i h / alpha h)"
    proof (cases "\<Delta> i < 0")
      case True
      have "(1 + eps k)\<^sup>2 * -1 \<le> (1 + eps k)\<^sup>2 * (\<Delta> i / alpha (hgt (pee i)))"
        using \<Delta>alpha 
        by (smt (verit, best) power2_less_0 \<open>i \<in> \<R>\<close> mult_le_cancel_left2 mult_minus_right)
      also have "\<dots> \<le> (\<Sum>h = 1..maxh. \<Delta>\<Delta> i h / alpha h)"
      proof -
        have le0: "\<Delta>\<Delta> i h \<le> 0" for h 
          using True by (auto simp: \<Delta>\<Delta>_def \<Delta>_def pp_eq)
        have eq0: "\<Delta>\<Delta> i h = 0" if "1 \<le> h" "h < hgt (pee i) - 2" for h 
        proof -
          have "hgt (pee i) - 2 \<le> hgt (pee (Suc i))"
            using Y_6_5_Red \<open>16 \<le> k\<close> \<open>i \<in> \<R>\<close> unfolding \<R>_def by blast
          then show ?thesis
            using that pp_less_hgt[of h] by (auto simp: \<Delta>\<Delta>_def pp_def)
        qed
        show ?thesis
          unfolding 33 sum_distrib_left sum_divide_distrib
        proof (intro sum_mono)
          fix h :: nat
          assume "h \<in> {1..maxh}"
          then have "1 \<le> h" "h \<le> maxh" by auto
          show "(1 + eps k)\<^sup>2 * (\<Delta>\<Delta> i h / alpha (hgt (pee i))) \<le> \<Delta>\<Delta> i h / alpha h"
          proof (cases "h < hgt (pee i) - 2")
            case True
            then show ?thesis
              using \<open>1 \<le> h\<close> eq0 by force
          next
            case False
            have *: "(1 + eps k) ^ (hgt (pee i) - Suc 0) \<le> (1 + eps k)\<^sup>2 * (1 + eps k) ^ (h - Suc 0)"
              using False eps_ge0 unfolding power_add [symmetric] 
              by (intro power_increasing) auto
            have **: "(1 + eps k)\<^sup>2 * alpha h \<ge> alpha (hgt (pee i))"
              using \<open>1 \<le> h\<close> mult_left_mono [OF *, of "eps k"] eps_ge0
              by (simp add: alpha_eq hgt_gt0 mult_ac divide_right_mono)
            show ?thesis
              using le0 alpha_gt0 \<open>h\<ge>1\<close> hgt_gt0 mult_left_mono_neg [OF **, of "\<Delta>\<Delta> i h"]
              by (simp add: divide_simps mult_ac)
          qed
        qed
      qed
      finally show ?thesis
        by linarith 
    next
      case False
      then have "\<Delta>\<Delta> i h \<ge> 0" for h
        using \<Delta>\<Delta>_def \<Delta>_def pp_eq by auto
      then have "(\<Sum>h = 1..maxh. \<Delta>\<Delta> i h / alpha h) \<ge> 0"
        by (simp add: alpha_ge0 sum_nonneg)
      then show ?thesis
        by (smt (verit, ccfv_SIG) sum_power2_ge_zero)
    qed
  qed
  then have 83: "- (1 + eps k)\<^sup>2 * card \<R> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<R>. \<Delta>\<Delta> i h / alpha h)" 
    by (simp add: mult.commute sum.swap [of _ \<R>])

  \<comment> \<open>now to tackle claim 8.4\<close>

  have \<Delta>0: "\<Delta> i \<ge> 0" if "i \<in> \<D>" for i
    using Y_6_4_DegreeReg that unfolding \<D>_def \<Delta>_def by auto

  have 39: "-2 * eps k powr(-1/2) \<le> (\<Sum>h = 1..maxh. (\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h) / alpha h)" (is "?L \<le> ?R")
    if "i \<in> \<B>" for i
  proof -
    have "odd i"
      using step_odd that by (force simp: Step_class_insert_NO_MATCH \<B>_def)
    then have "i>0"
      using odd_pos by auto
    show ?thesis
    proof (cases "\<Delta> (i-1) + \<Delta> i \<ge> 0")
      case True
      with \<open>i>0\<close> have "\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h \<ge> 0" if "h\<ge>1" for h
        by (fastforce simp: \<Delta>\<Delta>_def \<Delta>_def pp_eq)
      then have "(\<Sum>h = 1..maxh. (\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h) / alpha h) \<ge> 0"
        by (force simp: alpha_ge0 intro: sum_nonneg)
      then show ?thesis
        by (smt (verit, ccfv_SIG) powr_ge_zero)
    next
      case False
      then have \<Delta>\<Delta>_le0: "\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h \<le> 0" if "h\<ge>1" for h
        by (smt (verit, best) One_nat_def \<Delta>\<Delta>_def \<Delta>_def \<open>odd i\<close> odd_Suc_minus_one pp_eq)
      have hge: "hgt (pee (Suc i)) \<ge> hgt (pee (i-1)) - 2 * eps k powr (-1/2)"
        using bigY65B that Y_6_5_Bblue by (fastforce simp: \<B>_def)
      have \<Delta>\<Delta>0: "\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h = 0" if "0<h" "h < hgt (pee (i-1)) - 2 * eps k powr (-1/2)" for h
        using \<open>odd i\<close> that hge unfolding \<Delta>\<Delta>_def One_nat_def
        by (smt (verit) of_nat_less_iff odd_Suc_minus_one powr_non_neg pp_less_hgt)
      have big39: "1/2 \<le> (1 + eps k) powr (-2 * eps k powr (-1/2))"
        using big l_le_k by (auto simp: Big_ZZ_8_1_def Big39_def)
      have "?L * alpha (hgt (pee (i-1))) * (1 + eps k) powr (-2 * eps k powr (-1/2))
           \<le> - (eps k powr (-1/2)) * alpha (hgt (pee (i-1)))"
        using mult_left_mono_neg [OF big39, of "- (eps k powr (-1/2)) * alpha (hgt (pee (i-1))) / 2"]
        using alpha_ge0 [of "hgt (pee (i-1))"] eps_ge0 [of k]
        by (simp add: mult_ac)
      also have "\<dots> \<le> \<Delta> (i-1) + \<Delta> i"
      proof -
        have "pee (Suc i) \<ge> pee (i-1) - (eps k powr (-1/2)) * alpha (hgt (pee (i-1)))"
          using Y_6_4_Bblue that \<B>_def by blast
        with \<open>i>0\<close> show ?thesis
          by (simp add: \<Delta>_def)
      qed
      finally have "?L * alpha (hgt (pee (i-1))) * (1 + eps k) powr (-2 * eps k powr (-1/2)) \<le> \<Delta> (i-1) + \<Delta> i" .
      then have "?L \<le> (1 + eps k) powr (2 * eps k powr (-1/2)) * (\<Delta> (i-1) + \<Delta> i) / alpha (hgt (pee (i-1)))"
        using alpha_ge0 [of "hgt (pee (i-1))"] eps_ge0 [of k]
        by (simp add: powr_minus divide_simps mult_ac)
      also have "\<dots> \<le> ?R"
      proof -
        have "(1 + eps k) powr (2 * eps k powr(-1/2)) * (\<Delta>\<Delta> (i - Suc 0) h + \<Delta>\<Delta> i h) / alpha (hgt (pee (i - Suc 0))) 
           \<le> (\<Delta>\<Delta> (i - Suc 0) h + \<Delta>\<Delta> i h) / alpha h"
          if h: "Suc 0 \<le> h" "h \<le> maxh" for h
        proof (cases "h < hgt (pee (i-1)) - 2 * eps k powr(-1/2)")
          case False
          then have "hgt (pee (i-1)) - 1 \<le> 2 * eps k powr(-1/2) + (h - 1)"
            using hgt_gt0 by (simp add: nat_less_real_le)
          then have *: "(1 + eps k) powr (2 * eps k powr(-1/2)) / alpha (hgt (pee (i-1))) \<ge> 1 / alpha h"
            using that eps_gt0[of k] kn0 hgt_gt0
            by (simp add: alpha_eq divide_simps flip: powr_realpow powr_add)
          show ?thesis
            using mult_left_mono_neg [OF * \<Delta>\<Delta>_le0] that by (simp add: Groups.mult_ac) 
        qed (use h \<Delta>\<Delta>0 in auto)
        then show ?thesis
          by (force simp: 33 sum_distrib_left sum_divide_distrib simp flip: sum.distrib intro: sum_mono)
      qed
      finally show ?thesis .
    qed
  qed

  have B34: "card \<B> \<le> k powr (3/4)"
    by (smt (verit) card\<B> l_le_k of_nat_0_le_iff of_nat_mono powr_mono2 zero_le_divide_iff)
  have "-2 * k powr (7/8) \<le> -2 * eps k powr(-1/2) * k powr (3/4)"
    by (simp add: eps_def powr_powr flip: powr_add)
  also have "\<dots> \<le> -2 * eps k powr(-1/2) * card \<B>"
    using B34 by (intro mult_left_mono_neg powr_mono2) auto
  also have "\<dots> = (\<Sum>i\<in>\<B>. -2 * eps k powr(-1/2))"
    by simp
  also have "\<dots> \<le> (\<Sum>h = 1..maxh. \<Sum>i\<in>\<B>. (\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h) / alpha h)"
    unfolding sum.swap [of _ \<B>] by (intro sum_mono 39)
  also have "\<dots> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<B>\<union>\<D>. \<Delta>\<Delta> i h / alpha h)"
  proof (intro sum_mono)
    fix h
    assume "h \<in> {1..maxh}"
    have "\<B> \<subseteq> {0<..}"
      using odd_pos [OF step_odd] by (auto simp: \<B>_def Step_class_insert_NO_MATCH)
    with inj_on_diff_nat [of \<B> 1] have inj_pred: "inj_on (\<lambda>i. i - Suc 0) \<B>"
      by (simp add: Suc_leI subset_eq)
    have "(\<Sum>i\<in>\<B>. \<Delta>\<Delta> (i - Suc 0) h) = (\<Sum>i \<in> (\<lambda>i. i-1) ` \<B>. \<Delta>\<Delta> i h)"
      by (simp add: sum.reindex [OF inj_pred])
    also have "\<dots> \<le> (\<Sum>i\<in>\<D>. \<Delta>\<Delta> i h)"
    proof (intro sum_mono2)
      show "(\<lambda>i. i - 1) ` \<B> \<subseteq> \<D>"
        by (force simp: \<D>_def \<B>_def Step_class_insert_NO_MATCH intro: dreg_before_step')
      show "0 \<le> \<Delta>\<Delta> i h" if "i \<in> \<D> \<setminus> (\<lambda>i. i - 1) ` \<B>" for i
        using that \<Delta>0 \<Delta>\<Delta>_def \<Delta>_def pp_eq by fastforce
    qed auto
    finally have "(\<Sum>i\<in>\<B>. \<Delta>\<Delta> (i - Suc 0) h) \<le> (\<Sum>i\<in>\<D>. \<Delta>\<Delta> i h)" .
    with alpha_ge0 [of h]
    show "(\<Sum>i\<in>\<B>. (\<Delta>\<Delta> (i - 1) h + \<Delta>\<Delta> i h) / alpha h) \<le> (\<Sum>i \<in> \<B>\<union>\<D>. \<Delta>\<Delta> i h / alpha h)"
      by (simp add: BD_disj divide_right_mono sum.distrib sum.union_disjoint flip: sum_divide_distrib)
    qed
  finally have 84: "-2 * k powr (7/8) \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<B>\<union>\<D>. \<Delta>\<Delta> i h / alpha h)" .

  have m_eq: "{..<halted_point} = \<R> \<union> \<S> \<union> (\<B> \<union> \<D>)"
    using before_halted_eq by (auto simp: \<B>_def \<D>_def \<S>_def \<R>_def Step_class_insert_NO_MATCH)

  have "- (1 + eps k)\<^sup>2 * real (card \<R>)
     + oneminus * sum_SS 
     - 2 * real k powr (7/8) \<le> (\<Sum>h = Suc 0..maxh. \<Sum>i\<in>\<R>. \<Delta>\<Delta> i h / alpha h)
      + (\<Sum>h = Suc 0..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha h)
      + (\<Sum>h = Suc 0..maxh. \<Sum>i \<in> \<B> \<union> \<D>. \<Delta>\<Delta> i h / alpha h) "
    using 82 83 84 by simp
  also have "\<dots> = (\<Sum>h = Suc 0..maxh. \<Sum>i \<in> \<R> \<union> \<S> \<union> (\<B> \<union> \<D>). \<Delta>\<Delta> i h / alpha h)"
    by (simp add: sum.distrib disj sum.union_disjoint Int_Un_distrib Int_Un_distrib2)
  also have "\<dots> \<le> 1 + 2 * ln (real k) / eps k"
    using 34 by (simp add: m_eq)
  finally
  have 41: "oneminus * sum_SS - (1 + eps k)\<^sup>2 * card \<R> - 2 * k powr (7/8)
          \<le> 1 + 2 * ln k / eps k" 
    by simp
  have big42: "(1 + eps k)\<^sup>2 / oneminus \<le> 1 + 2 * k powr (-1/16)"
              "2 * k powr (-1/16) * k
             + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus
       \<le> real k powr (19/20)"
    using big l_le_k by (auto simp: Big_ZZ_8_1_def Big42a_def Big42b_def oneminus_def)
  have "oneminus > 0"
    using \<open>16 \<le> k\<close> eps_gt0 eps_less1 powr01_less_one by (auto simp: oneminus_def)
  with 41 have "sum_SS
        \<le> (1 + 2 * ln k / eps k + (1 + eps k)\<^sup>2 * card \<R> + 2 * k powr (7/8)) / oneminus" 
    by (simp add: mult_ac pos_le_divide_eq diff_le_eq)
  also have "\<dots> \<le> card \<R> * (((1 + eps k)\<^sup>2) / oneminus) 
                 + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus"
    by (simp add: field_simps add_divide_distrib)
  also have "\<dots> \<le> card \<R> * (1 + 2 * k powr (-1/16)) 
                 + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus"
    using big42 \<open>oneminus > 0\<close> by (intro add_mono mult_mono) auto
  also have "\<dots> \<le> card \<R> + 2 * k powr (-1/16) * k
                 + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus"
    using \<open>card \<R> < k\<close> by (intro add_mono mult_mono) (auto simp: algebra_simps)
  also have "\<dots> \<le> real (card \<R>) + real k powr (19/20)"
    using big42 by force
  finally show ?thesis .
qed

subsection \<open>Lemma 8.5\<close>

text \<open>An inequality that pops up in the proof of (39)\<close>
definition "inequality85 \<equiv> \<lambda>k. 3 * eps k powr (1/4) * k \<le> k powr (19/20)"

definition "Big_ZZ_8_5 \<equiv>     
   \<lambda>\<mu> l. Big_X_7_5 \<mu> l \<and> Big_ZZ_8_1 \<mu> l \<and> Big_Red_5_3 \<mu> l
      \<and> (\<forall>k\<ge>l. inequality85 k)"

lemma Big_ZZ_8_5:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_ZZ_8_5 \<mu> l"
  using assms Big_Red_5_3 Big_X_7_5 Big_ZZ_8_1
  unfolding Big_ZZ_8_5_def inequality85_def eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)       
  apply (intro conjI strip eventually_all_ge_at_top; real_asymp)     
  done

lemma (in Book) ZZ_8_5:
  assumes big: "Big_ZZ_8_5 \<mu> l" 
  defines "\<R> \<equiv> Step_class {red_step}" and "\<S> \<equiv> Step_class {dboost_step}"
  shows "card \<S> \<le> (bigbeta / (1 - bigbeta)) * card \<R> 
        + (2 / (1-\<mu>)) * k powr (19/20)"
proof -
  have [simp]: "finite \<S>"
    by (simp add: \<S>_def)
  moreover have "dboost_star \<subseteq> \<S>"
    by (auto simp: dboost_star_def \<S>_def)
  ultimately have "real (card \<S>) - real (card dboost_star) = card (\<S>\<setminus>dboost_star)"
    by (metis card_Diff_subset card_mono finite_subset of_nat_diff)
  also have "\<dots> \<le> 3 * eps k powr (1/4) * k"
    using \<mu>01 big X_7_5 by (auto simp: Big_ZZ_8_5_def dboost_star_def \<S>_def)
  also have "\<dots> \<le> k powr (19/20)"
    using big l_le_k by (auto simp: Big_ZZ_8_5_def inequality85_def)
  finally have *: "real (card \<S>) - card dboost_star \<le> k powr (19/20)" .
  have bigbeta_lt1: "bigbeta < 1" and bigbeta_gt0: "0 < bigbeta" and beta_gt0: "\<And>i. i \<in> \<S> \<Longrightarrow> beta i > 0" 
    using bigbeta_ge0 big by (auto simp: Big_ZZ_8_5_def \<S>_def beta_gt0 bigbeta_gt0 bigbeta_less1)
  then have ge0: "bigbeta / (1 - bigbeta) \<ge> 0"
    by auto
  show ?thesis
  proof (cases "dboost_star = {}")
    case True
    with * have "card \<S> \<le> k powr (19/20)"
      by simp
    also have "\<dots> \<le> (2 / (1-\<mu>)) * k powr (19/20)"
      using \<mu>01 kn0 by (simp add: divide_simps)
    finally show ?thesis
      by (smt (verit, ccfv_SIG) mult_nonneg_nonneg of_nat_0_le_iff ge0) 
  next
    case False    
    have bb_le: "bigbeta \<le> \<mu>"
      using big bigbeta_le by (auto simp: Big_ZZ_8_5_def)
    have "(card \<S> - k powr (19/20)) / bigbeta \<le> card dboost_star / bigbeta"
      by (smt (verit) "*" bigbeta_ge0 divide_right_mono)
    also have "\<dots> = (\<Sum>i\<in>dboost_star. 1 / beta i)"
    proof (cases "card dboost_star = 0")
      case False
      then show ?thesis
        by (simp add: bigbeta_def Let_def inverse_eq_divide)
    qed (simp add: False card_eq_0_iff)
    also have "\<dots> \<le> real(card dboost_star) + card \<R> + k powr (19/20)"
    proof -
      have "(\<Sum>i\<in>dboost_star. (1 - beta i) / beta i)
            \<le> real (card \<R>) + k powr (19/20)"
        using ZZ_8_1 big unfolding Big_ZZ_8_5_def \<R>_def by blast
      moreover have "(\<Sum>i\<in>dboost_star. beta i / beta i) = (\<Sum>i\<in>dboost_star. 1)"
        using \<open>dboost_star \<subseteq> \<S>\<close> beta_gt0 by (intro sum.cong) force+
      ultimately show ?thesis
        by (simp add: field_simps diff_divide_distrib sum_subtractf)
    qed
    also have "\<dots> \<le> real(card \<S>) + card \<R> + k powr (19/20)"
      by (simp add: \<open>dboost_star \<subseteq> \<S>\<close> card_mono)
    finally have "(card \<S> - k powr (19/20)) / bigbeta \<le> real (card \<S>) + card \<R> + k powr (19/20)" .
    then have "card \<S> - k powr (19/20) \<le> (real (card \<S>) + card \<R> + k powr (19/20)) * bigbeta"
      using bigbeta_gt0 by (simp add: field_simps)
    then have "card \<S> * (1 - bigbeta) \<le> bigbeta * card \<R> + (1 + bigbeta) * k powr (19/20)"
      by (simp add: algebra_simps)
    then have "card \<S> \<le> (bigbeta * card \<R> + (1 + bigbeta) * k powr (19/20)) / (1 - bigbeta)"
      using bigbeta_lt1 by (simp add: field_simps)
    also have "\<dots> = (bigbeta / (1 - bigbeta)) * card \<R> 
                  + ((1 + bigbeta) / (1 - bigbeta)) * k powr (19/20)"
      using bigbeta_gt0 bigbeta_lt1 by (simp add: divide_simps)
    also have "\<dots> \<le> (bigbeta / (1 - bigbeta)) * card \<R> + (2 / (1-\<mu>)) * k powr (19/20)"
      using \<mu>01 bb_le by (intro add_mono order_refl mult_right_mono frac_le) auto
    finally show ?thesis .
  qed
qed

subsection \<open>Lemma 8.6\<close>

text \<open>For some reason this was harder than it should have been.
      It does require a further small limit argument.\<close>

definition "Big_ZZ_8_6 \<equiv>     
   \<lambda>\<mu> l. Big_ZZ_8_5 \<mu> l \<and> (\<forall>k\<ge>l. 2 / (1-\<mu>) * k powr (19/20) < k powr (39/40))"

lemma Big_ZZ_8_6:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_ZZ_8_6 \<mu> l"
  using assms Big_ZZ_8_5
  unfolding Big_ZZ_8_6_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
  apply (intro conjI strip eventually_all_ge_at_top eventually_all_geI1 [where L=1])   
   apply real_asymp
  by (smt (verit, ccfv_SIG) frac_le powr_ge_zero)

lemma (in Book) ZZ_8_6:
  assumes big: "Big_ZZ_8_6 \<mu> l" 
  defines "\<R> \<equiv> Step_class {red_step}" and "\<S> \<equiv> Step_class {dboost_step}"
    and "a \<equiv> 2 / (1-\<mu>)"
  assumes s_ge: "card \<S> \<ge> k powr (39/40)"
  shows "bigbeta \<ge> (1 - a * k powr (-1/40)) * (card \<S> / (card \<S> + card \<R>))"
proof -
  have bigbeta_lt1: "bigbeta < 1" and bigbeta_gt0: "0 < bigbeta"
    using bigbeta_ge0 big 
    by (auto simp: Big_ZZ_8_6_def Big_ZZ_8_5_def bigbeta_less1 bigbeta_gt0 \<S>_def)
  have "a > 0"
    using \<mu>01 by (simp add: a_def)
  have s_gt_a: "a * k powr (19/20) < card \<S>"
        and 85: "card \<S> \<le> (bigbeta / (1 - bigbeta)) * card \<R> + a * k powr (19/20)"
    using big l_le_k assms
    unfolding \<R>_def \<S>_def a_def Big_ZZ_8_6_def by (fastforce intro: ZZ_8_5)+
  then have t_non0: "card \<R> \<noteq> 0"   \<comment> \<open>seemingly not provable without our assumption\<close>
    using mult_eq_0_iff by fastforce
  then have "(card \<S> - a * k powr (19/20)) / card \<R> \<le> bigbeta / (1 - bigbeta)"
    using 85 bigbeta_gt0 bigbeta_lt1 t_non0 by (simp add: pos_divide_le_eq)
  then have "bigbeta \<ge> (1 - bigbeta) * (card \<S> - a * k powr (19/20)) / card \<R>"
    by (smt (verit, ccfv_threshold) bigbeta_lt1 mult.commute le_divide_eq times_divide_eq_left)
  then have *: "bigbeta * (card \<R> + card \<S> - a * k powr (19/20)) \<ge> card \<S> - a * k powr (19/20)"
    using t_non0 by (simp add: field_simps)
  have "(1 - a * k powr - (1/40)) * card \<S> \<le> card \<S> - a * k powr (19/20)"
    using s_ge kn0 \<open>a>0\<close> t_non0 by (simp add: powr_minus field_simps flip: powr_add)
  then have "(1 - a * k powr (-1/40)) * (card \<S> / (card \<S> + card \<R>)) 
          \<le> (card \<S> - a * k powr (19/20)) / (card \<S> + card \<R>)"
    by (force simp: divide_right_mono)
  also have "\<dots> \<le> (card \<S> - a * k powr (19/20)) / (card \<R> + card \<S> - a * k powr (19/20))"
    using s_gt_a \<open>a>0\<close> t_non0 by (intro divide_left_mono) auto
  also have "\<dots> \<le> bigbeta"
    using * s_gt_a
    by (simp add: divide_simps split: if_split_asm)
  finally show ?thesis .
qed

end
