theory MLTL_Language_Partition_Proof

imports MLTL_Language_Partition_Algorithm

begin

section \<open> Properties of convert nnf ext \<close>

lemma convert_nnf_and_convert_nnf_ext:
  shows "to_mltl (convert_nnf_ext \<phi>) = 
    convert_nnf (to_mltl \<phi>)"
proof (induct "depth_mltl (to_mltl \<phi>)" arbitrary: \<phi> rule: less_induct)
  case less
  have not: "(\<And>\<phi>. depth_mltl (to_mltl \<phi>)
                < Suc (depth_mltl (to_mltl \<psi>)) \<Longrightarrow>
                to_mltl (convert_nnf_ext \<phi>) =
                convert_nnf (to_mltl \<phi>)) \<Longrightarrow>
          \<phi> = Not\<^sub>c \<psi> \<Longrightarrow>
          to_mltl (convert_nnf_ext (Not\<^sub>c \<psi>)) =
          convert_nnf (Not\<^sub>m (to_mltl \<psi>))" for \<psi>
  proof-
    assume ih: "(\<And>\<phi>. depth_mltl (to_mltl \<phi>)
                < Suc (depth_mltl (to_mltl \<psi>)) \<Longrightarrow>
                to_mltl (convert_nnf_ext \<phi>) =
                convert_nnf (to_mltl \<phi>))"
    assume shape: "\<phi> = Not\<^sub>c \<psi>"
    show ?thesis
      using less ih shape by (induct \<psi>) simp_all
  qed
  show ?case using less not
    by(cases \<phi>) auto
qed

  
lemma convert_nnf_ext_to_mltl_commute: 
  shows "(convert_nnf (to_mltl \<phi>)) = (to_mltl (convert_nnf_ext \<phi>))"
proof(induct "depth_mltl (to_mltl \<phi>)" arbitrary: \<phi> rule: less_induct)
  case less
  then show ?case 
  proof (cases \<phi>)
    case True_mltl_ext
    then show ?thesis 
      unfolding True_mltl_ext convert_nnf.simps convert_nnf_ext.simps to_mltl.simps semantic_equiv_def
      by simp
  next
    case False_mltl_ext
    then show ?thesis 
      unfolding False_mltl_ext convert_nnf.simps convert_nnf_ext.simps to_mltl.simps semantic_equiv_def
      by simp
  next
    case (Prop_mltl_ext p)
    then show ?thesis 
      unfolding Prop_mltl_ext convert_nnf.simps convert_nnf_ext.simps to_mltl.simps semantic_equiv_def
      by simp
  next
    case (Not_mltl_ext F)
    then have \<phi>_is: "\<phi> = Not\<^sub>c F"
      by blast
    show ?thesis 
    proof(cases F)
      case True_mltl_ext
      then show ?thesis using \<phi>_is less semantic_equiv_def by auto
    next
      case False_mltl_ext
      then show ?thesis using \<phi>_is less semantic_equiv_def by auto
    next
      case (Prop_mltl_ext p)
      then show ?thesis using \<phi>_is less semantic_equiv_def by auto
    next
      case (Not_mltl_ext F1)
      then show ?thesis using \<phi>_is less semantic_equiv_def by auto
    next
      case (And_mltl_ext F1 F2)
      have r1: "Not\<^sub>m (to_mltl F1) = to_mltl (Not\<^sub>c F1)"
        by simp
      have r2: "Not\<^sub>m (to_mltl F2) = to_mltl (Not\<^sub>c F2)"
        by simp
      have rewrite: "(Or_mltl (convert_nnf (Not\<^sub>m (to_mltl F1)))
                              (convert_nnf (Not\<^sub>m (to_mltl F2)))) = 
          (Or_mltl (convert_nnf (to_mltl (Not\<^sub>c F1)))
                   (convert_nnf (to_mltl (Not\<^sub>c F2))))"
        using r1 r2 by simp
      have ih1: "(convert_nnf (to_mltl (Not\<^sub>c F1))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F1)))"
        using less[of "Not\<^sub>c F1"] unfolding And_mltl_ext \<phi>_is by simp
      have ih2: "(convert_nnf (to_mltl (Not\<^sub>c F2))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F2)))"
        using less[of "Not\<^sub>c F2"] unfolding And_mltl_ext \<phi>_is by simp
      have "(Or_mltl (convert_nnf (to_mltl (Not\<^sub>c F1)))
                   (convert_nnf (to_mltl (Not\<^sub>c F2))))
     = (Or_mltl (to_mltl (convert_nnf_ext (Not\<^sub>c F1)))
       (to_mltl (convert_nnf_ext (Not\<^sub>c F2))))"
        using ih1 ih2 unfolding semantic_equiv_def by auto
      then show ?thesis 
        unfolding \<phi>_is And_mltl_ext to_mltl.simps convert_nnf.simps  
        unfolding convert_nnf_ext.simps to_mltl.simps 
        by simp
    next
      case (Or_mltl_ext F1 F2)
      have r1: "Not\<^sub>m (to_mltl F1) = to_mltl (Not\<^sub>c F1)"
        by simp
      have r2: "Not\<^sub>m (to_mltl F2) = to_mltl (Not\<^sub>c F2)"
        by simp
      have rewrite: "(Or_mltl (convert_nnf (Not\<^sub>m (to_mltl F1)))
                              (convert_nnf (Not\<^sub>m (to_mltl F2)))) = 
          (Or_mltl (convert_nnf (to_mltl (Not\<^sub>c F1)))
                   (convert_nnf (to_mltl (Not\<^sub>c F2))))"
        using r1 r2 by simp
      have ih1: "(convert_nnf (to_mltl (Not\<^sub>c F1))) = 
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F1)))"
        using less[of "Not\<^sub>c F1"] unfolding Or_mltl_ext \<phi>_is by simp
      have ih2: "(convert_nnf (to_mltl (Not\<^sub>c F2))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F2)))"
        using less[of "Not\<^sub>c F2"] unfolding Or_mltl_ext \<phi>_is by simp
      have "
     (And_mltl (convert_nnf (to_mltl (Not\<^sub>c F1)))
                   (convert_nnf (to_mltl (Not\<^sub>c F2)))) =
     (And_mltl (to_mltl (convert_nnf_ext (Not\<^sub>c F1)))
       (to_mltl (convert_nnf_ext (Not\<^sub>c F2))))"
        using ih1 ih2 unfolding semantic_equiv_def by auto
      then show ?thesis 
        unfolding \<phi>_is Or_mltl_ext to_mltl.simps convert_nnf.simps  
        unfolding convert_nnf_ext.simps to_mltl.simps 
        by blast
    next
      case (Future_mltl_ext a b L F)
      have r1: "Not\<^sub>m (to_mltl F) = to_mltl (Not\<^sub>c F)"
        by simp
      then have rewrite: "(Global_mltl a b (convert_nnf (Not\<^sub>m (to_mltl F)))) = 
                 (Global_mltl a b (convert_nnf (to_mltl (Not\<^sub>c F))))"
        by simp
      have ih: "(convert_nnf (to_mltl (Not\<^sub>c F))) =
                               (to_mltl (convert_nnf_ext (Not\<^sub>c F)))"
        using less[of "Not\<^sub>c F"] \<phi>_is unfolding Future_mltl_ext by simp
      have "(Global_mltl a b (convert_nnf (to_mltl (Not\<^sub>c F)))) =
     (Global_mltl a b (to_mltl (convert_nnf_ext (Not\<^sub>c F))))"
        using ih unfolding semantic_equiv_def by auto
      then show ?thesis 
        unfolding \<phi>_is Future_mltl_ext to_mltl.simps convert_nnf.simps
        unfolding convert_nnf_ext.simps to_mltl.simps 
        using rewrite by blast
    next
      case (Global_mltl_ext a b L F)
      have r1: "Not\<^sub>m (to_mltl F) = to_mltl (Not\<^sub>c F)"
        by simp
      then have rewrite: "(Global_mltl a b (convert_nnf (Not\<^sub>m (to_mltl F)))) = 
                 (Global_mltl a b (convert_nnf (to_mltl (Not\<^sub>c F))))"
        by simp
      have ih: "(convert_nnf (to_mltl (Not\<^sub>c F))) =
                               (to_mltl (convert_nnf_ext (Not\<^sub>c F)))"
        using less[of "Not\<^sub>c F"] \<phi>_is unfolding Global_mltl_ext by simp
      have "(Future_mltl a b (convert_nnf (to_mltl (Not\<^sub>c F)))) =
     (Future_mltl a b (to_mltl (convert_nnf_ext (Not\<^sub>c F))))"
        using ih unfolding semantic_equiv_def by auto
      then show ?thesis 
        unfolding \<phi>_is Global_mltl_ext to_mltl.simps convert_nnf.simps
        unfolding convert_nnf_ext.simps to_mltl.simps 
        using rewrite by simp
    next
      case (Until_mltl_ext F1 a b L F2)
      have r1: "Not\<^sub>m (to_mltl F1) = to_mltl (Not\<^sub>c F1)"
        by simp
      have r2: "Not\<^sub>m (to_mltl F2) = to_mltl (Not\<^sub>c F2)"
        by simp
      have rewrite: "(Or_mltl (convert_nnf (Not\<^sub>m (to_mltl F1)))
                              (convert_nnf (Not\<^sub>m (to_mltl F2)))) = 
          (Or_mltl (convert_nnf (to_mltl (Not\<^sub>c F1)))
                   (convert_nnf (to_mltl (Not\<^sub>c F2))))"
        using r1 r2 by simp
      have ih1: "(convert_nnf (to_mltl (Not\<^sub>c F1))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F1)))"
        using less[of "Not\<^sub>c F1"] unfolding Until_mltl_ext \<phi>_is by simp
      have ih2: "(convert_nnf (to_mltl (Not\<^sub>c F2))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F2)))"
        using less[of "Not\<^sub>c F2"] unfolding Until_mltl_ext \<phi>_is by simp
      have "
     (Release_mltl (convert_nnf (to_mltl (Not\<^sub>c F1))) a b
                   (convert_nnf (to_mltl (Not\<^sub>c F2)))) =
     (Release_mltl (to_mltl (convert_nnf_ext (Not\<^sub>c F1))) a b
       (to_mltl (convert_nnf_ext (Not\<^sub>c F2))))"
        using ih1 ih2 unfolding semantic_equiv_def by auto
      then show ?thesis 
        unfolding \<phi>_is Until_mltl_ext to_mltl.simps convert_nnf.simps  
        unfolding convert_nnf_ext.simps to_mltl.simps 
        by blast
    next
      case (Release_mltl_ext F1 a b L F2)
      have r1: "Not\<^sub>m (to_mltl F1) = to_mltl (Not\<^sub>c F1)"
        by simp
      have r2: "Not\<^sub>m (to_mltl F2) = to_mltl (Not\<^sub>c F2)"
        by simp
      have rewrite: "(Or_mltl (convert_nnf (Not\<^sub>m (to_mltl F1)))
                              (convert_nnf (Not\<^sub>m (to_mltl F2)))) = 
          (Or_mltl (convert_nnf (to_mltl (Not\<^sub>c F1)))
                   (convert_nnf (to_mltl (Not\<^sub>c F2))))"
        using r1 r2 by simp
      have ih1: "(convert_nnf (to_mltl (Not\<^sub>c F1))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F1)))"
        using less[of "Not\<^sub>c F1"] unfolding Release_mltl_ext \<phi>_is by simp
      have ih2: "(convert_nnf (to_mltl (Not\<^sub>c F2))) =
                           (to_mltl (convert_nnf_ext (Not\<^sub>c F2)))"
        using less[of "Not\<^sub>c F2"] unfolding Release_mltl_ext \<phi>_is by simp
      have "
     (Until_mltl (convert_nnf (to_mltl (Not\<^sub>c F1))) a b
                   (convert_nnf (to_mltl (Not\<^sub>c F2)))) =
     (Until_mltl (to_mltl (convert_nnf_ext (Not\<^sub>c F1))) a b
       (to_mltl (convert_nnf_ext (Not\<^sub>c F2))))"
        using ih1 ih2 unfolding semantic_equiv_def by auto
      then show ?thesis 
        unfolding \<phi>_is Release_mltl_ext to_mltl.simps convert_nnf.simps  
        unfolding convert_nnf_ext.simps to_mltl.simps 
        by blast
    qed
  next
    case (And_mltl_ext F1 F2)
    show ?thesis 
      unfolding And_mltl_ext to_mltl.simps convert_nnf.simps convert_nnf_ext.simps semantic_equiv_def
      using less[of F1] less[of F2] And_mltl_ext unfolding semantics_mltl.simps semantic_equiv_def by auto
  next
    case (Or_mltl_ext F1 F2)
    then show ?thesis 
      unfolding Or_mltl_ext to_mltl.simps convert_nnf.simps convert_nnf_ext.simps semantic_equiv_def
      using less[of F1] less[of F2] Or_mltl_ext unfolding semantics_mltl.simps semantic_equiv_def by simp
  next
    case (Future_mltl_ext a b L F)
    show ?thesis 
      unfolding Future_mltl_ext to_mltl.simps convert_nnf.simps convert_nnf_ext.simps to_mltl.simps
      using less[of F] Future_mltl_ext unfolding semantic_equiv_def semantics_mltl.simps by simp
  next
    case (Global_mltl_ext a b L F)
    then show ?thesis 
      unfolding Global_mltl_ext to_mltl.simps convert_nnf.simps convert_nnf_ext.simps to_mltl.simps
      using less[of F] Global_mltl_ext unfolding semantic_equiv_def semantics_mltl.simps by simp
  next
    case (Until_mltl_ext F1 a b L F2)
    then show ?thesis 
      unfolding Until_mltl_ext to_mltl.simps convert_nnf.simps convert_nnf_ext.simps to_mltl.simps
      using less[of F1] less[of F2] Until_mltl_ext unfolding semantic_equiv_def semantics_mltl.simps by simp
  next
    case (Release_mltl_ext F1 a b L F2)
    then show ?thesis 
      unfolding Release_mltl_ext to_mltl.simps convert_nnf.simps convert_nnf_ext.simps to_mltl.simps
      using less[of F1] less[of F2] Release_mltl_ext unfolding semantic_equiv_def semantics_mltl.simps by simp
  qed
qed

lemma convert_nnf_ext_preserves_semantics:
  assumes "intervals_welldef (to_mltl \<phi>)"
  shows "(convert_nnf_ext \<phi>) \<equiv>\<^sub>c \<phi>"
proof-
  have "semantic_equiv (convert_nnf (to_mltl \<phi>)) (to_mltl \<phi>)"
    using assms convert_nnf_preserves_semantics[of "(to_mltl \<phi>)"]
    unfolding semantic_equiv_ext_def semantic_equiv_def by blast
  then show ?thesis 
    using convert_nnf_ext_to_mltl_commute 
    unfolding semantic_equiv_ext_def semantic_equiv_def by metis
qed


lemma convert_nnf_ext_convert_nnf_ext: 
  shows "convert_nnf_ext \<phi> = convert_nnf_ext (convert_nnf_ext \<phi>)"
proof(induction "depth_mltl (to_mltl \<phi>)" arbitrary: \<phi> rule: less_induct)
  case less
  have not_case: "(\<And>F. depth_mltl (to_mltl F) < 
                       Suc (depth_mltl (to_mltl G)) \<Longrightarrow>
           convert_nnf_ext (convert_nnf_ext F) = convert_nnf_ext F) \<Longrightarrow>
           \<phi> = Not\<^sub>c G \<Longrightarrow>
           convert_nnf_ext (convert_nnf_ext (Not\<^sub>c G)) = 
           convert_nnf_ext (Not\<^sub>c G)" for "G"
  proof -
    assume ind_h: "(\<And>F. depth_mltl (to_mltl F) < 
                       Suc (depth_mltl (to_mltl G)) \<Longrightarrow>
           convert_nnf_ext (convert_nnf_ext F) = convert_nnf_ext F)"
    assume \<phi>_is: "\<phi> = Not\<^sub>c G"
    show ?thesis using less \<phi>_is by (cases G) simp_all
  qed
  show ?case using less not_case
    by (cases \<phi>) fastforce+
qed


subsection \<open>Cases where to mltl is bijective\<close>
lemma to_mltl_true_bijective:
  assumes "to_mltl \<phi> = True\<^sub>m"
  shows "\<phi> = True\<^sub>c"
  using assms by (cases \<phi>) simp_all

lemma to_mltl_false_bijective:
  assumes "to_mltl \<phi> = False\<^sub>m"
  shows "\<phi> = False\<^sub>c"
  using assms by (cases \<phi>) simp_all

lemma to_mltl_prop_bijective:
  assumes "to_mltl \<phi> = Prop\<^sub>m (p)"
  shows "\<phi> = Prop\<^sub>c (p)"
  using assms by (cases \<phi>) simp_all

lemma to_mltl_not_prop_bijective:
  assumes "to_mltl \<phi> = Not\<^sub>m (Prop\<^sub>m (p))"
  shows "\<phi> = Not\<^sub>c (Prop\<^sub>c (p))"
  using assms by (cases \<phi>) (simp_all add: to_mltl_prop_bijective)


section \<open>Lemmas about Integer Composition\<close>

lemma composition_length_ub:
  fixes n::"nat" and L::"nat list"
  assumes "is_composition n L"
  shows "length L \<le> n"
  using assms unfolding is_composition_def 
proof (induct L arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a L)
  have listsum: "sum_list (a # L) = a + sum_list L"
    by simp
  then have ls_L: "sum_list L = n - a"
    using Cons(2) by auto
  then have Lprop: "(\<forall>i. List.member L i \<longrightarrow> 0 < i) \<and> sum_list L = n - a "
    using Cons(2)
    by (meson member_rec(1)) 
  then have len_leq: "length L \<le> n - a"
    using Cons(1)[OF Lprop]
    by auto
  have "a > 0"
    using Cons(2) 
    by (meson member_rec(1))
  then show ?case using len_leq
    using Cons.prems listsum by auto
qed

lemma composition_length_lb: 
  fixes n::"nat" and L::"nat list"
  assumes "is_composition n L"
  assumes "n > 0"
  shows "0 < length L"
proof-
  have "\<not>(0 < length L) \<Longrightarrow> False"
  proof-
    assume "\<not>(0 < length L)"
    then have "length L = 0"
      by simp
    then have "sum_list L = 0"
      by simp
    then show ?thesis 
      using assms unfolding is_composition_def 
      by simp
  qed
  then show ?thesis using assms by blast
qed


lemma interval_times_length: 
  fixes a::"nat" and L::"nat list"
  shows "length (interval_times a L) = length L + 1"
  unfolding interval_times_def by auto


lemma interval_times_first: 
  fixes a::"nat" and L::"nat list"
  shows "(interval_times a L)!0 = a"
proof-
  have "map (\<lambda>i. a + partial_sum L i) [0..<length L + 1] ! 0 =
       (\<lambda>i. a + partial_sum L i) 0"
    by (metis Nat.add_0_right add_gr_0 less_numeral_extra(1) nth_map_upt zero_less_diff) 
  then have "map (\<lambda>i. a + partial_sum L i) [0..<length L + 1] ! 0 = a"
    unfolding partial_sum_def by auto
  then show ?thesis
    unfolding interval_times_def by blast
qed

lemma interval_times_last: 
  fixes a b::"nat" and L::"nat list"
  assumes int_welldef: "a \<le> b"
  assumes composition: "is_composition (b-a+1) L"
  shows "(interval_times a L)!(length L) = b+1"
proof -
  have "partial_sum L (length L) = sum_list L"
    unfolding partial_sum_def by auto
  then have "a + partial_sum L (length L) = b+1"
    using assms  unfolding is_composition_def
    by simp
  then show ?thesis
    unfolding interval_times_def
    by (metis add_0 add_diff_cancel_left' less_add_one nth_map_upt)
qed


lemma interval_times_diff:
  fixes a b i::"nat" and L::"nat list"
  assumes int_welldef: "a \<le> b"
  assumes composition: "is_composition (b-a+1) L"
  assumes i_index: "i < length L"
  assumes s_is: "s = interval_times a L"
  shows "s!(i+1) - s!(i) = L!i"
proof-
  have ip1: "s ! (i+1) = a + partial_sum L (i+1)"
    using s_is i_index unfolding interval_times_def 
    by (metis (no_types, lifting) add_0 add_mono1 diff_zero nth_map_upt)
  have i: "s ! i = a + partial_sum L i"
    using s_is i_index unfolding interval_times_def 
    by (metis (no_types, lifting) add.commute add_0 add_strict_increasing diff_zero less_numeral_extra(1) less_or_eq_imp_le nth_map_upt)
  have s_iat: "s ! (i+1) - s ! i = partial_sum L (i+1) - partial_sum L i"
    using ip1 i
    by auto
  have take_is: "take (i+1) L = (take i L) @ [L ! i] "
    by (simp add: i_index take_Suc_conv_app_nth)
  have li: "foldr (+) [L ! i] 0 = L ! i"
    by force
  have "\<And>a::nat. foldr (+) L a = a + foldr (+) L 0" for L::"nat list"
  proof (induct L)
    case Nil
    then show ?case by auto
  next
    case (Cons h T)
    then show ?case 
      by (metis add.left_commute foldr.simps(2) o_apply)
  qed
  then have "foldr (+) (take i L) (L!i) = L ! i + foldr (+) (take i L) 0"
    by blast
  then have "foldr (+) ((take i L) @ [L ! i]) 0 - foldr (+) (take i L) 0 = L ! i"
    using  foldr_append[of "(+)" "take i L" "[L ! i]" 0] li
    by simp
  then have "sum_list (take (i + 1) L) - sum_list (take i L) =  L ! i"
    using i_index take_is by simp
    then show ?thesis
    using i_index composition unfolding is_composition_def 
    partial_sum_def s_iat by blast
qed

lemma interval_times_diff_ge:
  fixes a b i::"nat" and L::"nat list"
  assumes int_welldef: "a \<le> b"
  assumes composition: "is_composition (b-a+1) L"
  assumes i_index: "i < length L"
  assumes s_is: "s = interval_times a L"
  shows "s!(i+1) > s!(i)"
proof-
  have diff: "s!(i+1) - s!(i) = L!i"
    using assms interval_times_diff by blast
  have gap: "L!i > 0" using assms(2) unfolding is_composition_def
    by (meson i_index in_set_member nth_mem) 
  show ?thesis using diff gap by simp
qed

lemma interval_times_diff_ge_general:
  fixes a b i j::"nat" and L::"nat list"
  assumes int_welldef: "a \<le> b"
  assumes composition: "is_composition (b-a+1) L"
  assumes j_index: "j \<le> length L"
  assumes i_le_j: "i < j"
  assumes s_is: "s = interval_times a L"
  shows "s!j > s!i"
  using assms
proof (induct "j-1" arbitrary: i j)
  case 0 
  then have "i = 0" and "j = 1" 
     by simp_all
  then show ?case
    using interval_times_diff_ge 0 by fastforce
next
  case (Suc x)
  then have j_eq: "j = x+2"
    by simp
  have high: "s ! (x + 1) < s ! (x + 2)"
    using interval_times_diff_ge[of a b L "x+1" s] Suc by simp
  {
    assume i_eq: "i = x+1"
    then have ?case unfolding i_eq j_eq
      using high by simp
  } moreover {
    assume i_eq: "i \<le> x"
    then have "s ! i < s ! (x + 1)"
      using Suc.hyps(1)[of "x+1" i] Suc by force
    then have ?case using high i_eq j_eq by simp
  }
  ultimately show ?case using Suc j_eq by linarith
qed

lemma trivial_composition: 
  assumes "n > 0"
  shows "is_composition n [n]"
proof-
  have pos: "(\<forall>i. List.member [n] i \<longrightarrow> 0 < i)"
    unfolding List.member_def
    by (simp add: assms) 
  have sum: " sum_list [n] = n"
    by simp
  show ?thesis unfolding is_composition_def
    using pos sum by blast
qed


lemma sum_list_pos: "(\<And>x. x \<in> set (xs::nat list) \<Longrightarrow> 0 < x) 
                      \<Longrightarrow> length xs > 0 \<Longrightarrow> 0 < sum_list xs"
  by (induction xs) auto

lemma take_prefix: 
  assumes "L = H@[t]"
  assumes "k \<le> length L - 1"
  shows "take k H = take k L"
  using assms by auto

lemma take_interval_times:
  assumes "length L \<ge> k"
  shows "take (k+1) (interval_times a L) = interval_times a (take k L)"
  using assms
proof(induct "length L" arbitrary: L)
  case 0
  then show ?case
    by (simp add: interval_times_length) 
next
  case (Suc x)
  then obtain H t where L_eq: "L = H@[t]"
    by (metis length_Suc_conv_rev)
  have ih: "take (k + 1) (interval_times a H) = interval_times a (take k H)"  
    using Suc.hyps(1)[of H] Suc L_eq
    by (metis Suc_eq_plus1 add_left_cancel interval_times_length le_SucE le_add1 length_append_singleton plus_1_eq_Suc take_all_iff)
  have length_it: "length (interval_times a L) = length L + 1" 
    unfolding interval_times_def by auto
  {
    assume *: "k \<le> length L - 1"
    then have eq1: "(take k H) = (take k L)"
      by (simp add: L_eq)
    have "(interval_times a H)@[a+(sum_list L)] = interval_times a L"
      using L_eq unfolding interval_times_def partial_sum_def by auto
    then have eq2: "take (k + 1) (interval_times a H) = take (k + 1) (interval_times a L)"
      using take_prefix[of "interval_times a L" "interval_times a H" "a + sum_list L"]
      by (metis Suc_eq_plus1 diff_Suc_1 eq1 ih interval_times_length not_less_eq_eq take_all)
    have ?case using eq1 eq2 ih by argo
  } moreover {
    assume *: "k = length L"
    then have ?case
      by (simp add: length_it) 
  }
  ultimately show ?case using Suc by linarith
qed

lemma index_list_index: 
  fixes k::"nat"
  assumes "j < k"
  shows "[0 ..< k] ! j = j" 
  using assms by simp


lemma interval_times_obtain_aux: 
  assumes "a \<le> b"
  assumes "is_composition (b - a + 1) L"
  assumes "s = interval_times a L"
  assumes "(s ! 1) \<le> t \<and> t \<le> b"
  shows "\<exists>i. s ! i \<le> t \<and> t \<le> s ! (i + 1) - 1 \<and> 1 \<le> i \<and> i < length L"
proof-
  have length_s: "length s = length L + 1" 
    using assms interval_times_length by auto
  have first: "s!0 = a"
    using interval_times_first assms by blast
  have last: "s!(length L) = b+1"
    using interval_times_last assms by blast
  {
    assume length_L: "length L = 0"
    then have ?thesis using assms
      by (metis first last less_add_one verit_comp_simplify1(3)) 
  } moreover {
    assume length_L: "length L \<ge> 1"
    have ?thesis using assms first last length_s length_L
    proof(induct "length L - 1" arbitrary: s L a b t)
      case 0
      then show ?case by auto
    next
      case (Suc x)
      then have length_L: "length L \<ge> 2" by linarith
      then have length_s: "length s \<ge> 3" using Suc by linarith
      {
        assume *: "t < s!(length L-1)"
        let ?L' = "take (length L-1) L"
        let ?s' = "take (length L) s"
        let ?b' = "b - (List.last L)"
        have pos_L: "(\<forall>i. List.member L i \<longrightarrow> 0 < i)" and 
             sum_L: "sum_list L = b - a + 1"
          using Suc(4) unfolding is_composition_def by auto
        have "List.member L (last L)" unfolding List.member_def
          by (metis Suc.prems(8) last_in_set length_0_conv not_one_le_zero)
        have sum_list_eq: "sum_list L = sum_list (take (length L-1) L) + last L"
          using length_L
        proof(induct "length L" arbitrary: L)
          case 0
          then show ?case by auto
        next
          case (Suc xa)
          then obtain h T where L_eq: "L = h#T"
            by (meson Suc_length_conv) 
          then have L_decomp: "sum_list L = sum_list T + h" by simp
          {
            assume "length L = 2"
            then obtain x1 x2 where "L = [x1, x2]"
              by (metis Suc_1 Suc_length_conv gen_length_code(1) gen_length_def impossible_Cons le_add2 list.exhaust plus_1_eq_Suc) 
            then have ?case by auto
          } moreover {
            assume length_L: "length L > 2"
            then have last: "last T = last L" 
              using L_eq by auto
            have *: "sum_list T = sum_list (take (length T - 1) T) + last T"
              using Suc.hyps(1)[of T] L_decomp L_eq length_L
              by (metis Suc.hyps(2) add_diff_cancel_left' length_Cons less_Suc_eq_le plus_1_eq_Suc) 
            have **: "h + sum_list (take (length T - 1) T) = sum_list (take (length L - 1) L)"
              using L_eq
              by (metis (no_types, opaque_lifting) Suc.prems Suc_1 Suc_eq_plus1 Suc_le_D add_diff_cancel_right' add_le_same_cancel2 length_Cons not_less_eq_eq sum_list.Cons take_Suc_Cons) 
            have ?case using * ** last
              using L_decomp by presburger 
          }
          ultimately show ?case using Suc.prems by fastforce
        qed
        have pos_preL: "(\<And>x. x \<in> set (take (length L - 1) L) \<Longrightarrow> 0 < x)"
          using pos_L
          by (metis in_set_member in_set_takeD) 
        have length_preL: "0 < length (take (length L - 1) L)"
          using length_L by auto
        have sum_preL_pos: "sum_list (take (length L-1) L) > 0"
          using sum_list_pos[of "take (length L - 1) L"] 
          using pos_preL length_preL by blast
        then have sum_last: "sum_list L > last L" using pos_L length_L
          using sum_list_pos sum_list_eq by linarith
        then have b_lastL: "b \<ge> last L"
          using sum_L by auto
        then have ba_lastL: "last L \<le> b - a" 
          using sum_L sum_last by auto
        have first: "s!0 = a"
          using Suc interval_times_first by blast
        have last: "s!(length L) = b+1" 
          using Suc interval_times_last by blast
        have c1: "x = length (take (length L - 1) L) - 1" 
          using Suc by auto
        have c2: "a \<le> b - last L" 
          using Suc(3) b_lastL ba_lastL by auto
        have c3 :"is_composition (b - last L - a + 1) (take (length L - 1) L)"
          using Suc.prems(2) unfolding is_composition_def
          by (metis Suc_diff_1 Suc_eq_plus1 \<open>0 < sum_list (take (length L - 1) L)\<close> add_diff_cancel_right diff_right_commute in_set_member plus_1_eq_Suc pos_preL sum_list_eq) 
        have c4: "take (length L) s = interval_times a (take (length L - 1) L)"
          unfolding Suc(5) using length_L take_interval_times
          by (metis Suc.prems(8) diff_add diff_le_self) 
        have c5: "take (length L) s ! 1 \<le> t \<and> t \<le> b - last L"
        proof-
          have "s!(length L-1) = a + sum_list (take (length L-1) L)"
            unfolding Suc(5) interval_times_def partial_sum_def
            by (metis (no_types, lifting) Suc.prems(8) add.commute add_0 add_mono_thms_linordered_field(3) le_add_same_cancel2 less_numeral_extra(1) nth_map_upt ordered_cancel_comm_monoid_diff_class.add_diff_inverse zero_le) 
          then have part1: "(s ! (length L - 1))-1 \<le> b - last L"
            using last sum_list_eq
            by (metis (no_types, lifting) One_nat_def Suc_leI sum_preL_pos c2 c3 diff_add_inverse2 eq_imp_le is_composition_def order_eq_refl ordered_cancel_comm_monoid_diff_class.add_diff_inverse ordered_cancel_comm_monoid_diff_class.diff_add_assoc) 
          have part2: "take (length L) s ! 1 \<le> t"
            using Suc.hyps(2) Suc.prems(4) by auto
          then show ?thesis using * part1 part2 
            by linarith
        qed
        have c6: "take (length L) s ! 0 = a"
          by (simp add: c4 interval_times_first)
        have c7: "take (length L) s ! length (take (length L - 1) L) = b - last L + 1"
        proof-
          have idx: "length (take (length L - 1) L) = length L-1" by simp            
          have p1: "a + partial_sum L (length L-1) = b - last L + 1"
            unfolding partial_sum_def
            by (metis add.assoc c2 c3 is_composition_def ordered_cancel_comm_monoid_diff_class.add_diff_inverse) 
          have p2: "take (length L) (map (\<lambda>i. a + partial_sum L i) [0..<length L + 1]) ! (length L - 1)
                = (map (\<lambda>i. a + partial_sum L i) [0..<length L + 1]) ! (length L - 1)"
            by (meson Suc.prems(2) add_gr_0 composition_length_lb diff_less nth_take zero_less_one) 
          have p3: "(map (\<lambda>i. a + partial_sum L i) [0..<length L + 1]) ! (length L - 1) 
                = a + partial_sum L (length L-1)" 
          proof-
            have fact1: "map (\<lambda>i. a + partial_sum L i) [0..<length L + 1] ! (length L - 1) =
                  a + partial_sum L ([0..<length L + 1] ! (length L - 1))"
              using nth_map[of "(length L-1)" "[0..<length L + 1]" "(\<lambda>i. a + partial_sum L i)"]
              by simp
            have "length L \<ge> 0"
              using Suc(2) by auto
            then have fact2: "([(0::nat)..<length L + 1] ! (length L - 1)) = length L -1"
              using index_list_index[of "length L-1" "length L + 1"] by simp
            then show ?thesis using fact1 fact2 by argo
          qed
          then have "take (length L) s ! (length L-1) = b - last L + 1"
            unfolding Suc(5) interval_times_def 
            using p1 p2 p3 by argo
          then show ?thesis using idx by argo
        qed
        have c8: "length (take (length L) s) = length (take (length L - 1) L) + 1"
          using c4 interval_times_length by presburger
        have c9: "1 \<le> length (take (length L - 1) L)"
          using length_preL by linarith
        have ih: "\<exists>i. take (length L) s ! i \<le> t \<and> t \<le> take (length L) s ! (i + 1) - 1 
                  \<and> 1 \<le> i \<and> i < length (take (length L - 1) L)" 
          using Suc(1)[of "(take (length L - 1) L)" a "b - last L" "take (length L) s" t,
                       OF c1 c2 c3 c4 c5 c6 c7 c8 c9] by blast
        then obtain i where t_bound: "take (length L) s ! i \<le> t \<and> t \<le> take (length L) s ! (i + 1) - 1"
                        and i_bound: "1 \<le> i \<and> i < length (take (length L - 1) L)"
          by blast
        have i_bound_L: "1 \<le> i \<and> i < length L" 
          using i_bound by auto
        then have t_bound_L: "s ! i \<le> t \<and> t \<le> s ! (i + 1) - 1"
          using t_bound
          by (metis Suc.hyps(2) c1 c9 i_bound le_add_diff_inverse less_diff_conv nth_take plus_1_eq_Suc) 
        then have ?case using i_bound_L t_bound by auto
      } moreover {
        assume *: "t \<ge> s!(length L-1)"
        then have ?case
          by (metis Suc.hyps(2) Suc.prems(4) Suc.prems(6) Suc.prems(8) add_diff_cancel_right' diff_less le_add1 le_add_diff_inverse2 less_numeral_extra(1) order_less_le_trans plus_1_eq_Suc) 
      }
      ultimately show ?case by fastforce
    qed
  }
  ultimately show ?thesis
    by (meson less_one verit_comp_simplify1(3)) 
qed


lemma interval_times_obtain: 
  assumes "a \<le> b"
  assumes "is_composition (b - a + 1) L"
  assumes "s = interval_times a L"
  assumes "a \<le> t \<and> t \<le> b"
  shows "\<exists>i. s ! i \<le> t \<and> t \<le> s ! (i + 1) - 1 \<and> 0 \<le> i \<and> i < length L"
proof-
  {
    assume *: "(s ! 1) \<le> t"
    from interval_times_obtain_aux[OF assms(1-3), of "t"] * assms(4)
    obtain i where "s ! i \<le> t \<and> t \<le> s ! (i + 1) - 1 \<and> 1 \<le> i \<and> i < length L"
      by auto
    then have ?thesis by blast
  } moreover {
    assume *: "t < s!1"
    have sfirst: "s!0 = a"
      using interval_times_first unfolding assms by auto
    have length_L: "0 < length L"
      using composition_length_lb[OF assms(2)] using assms by auto
    have "t \<le> s ! 1 - 1"
      using * by simp
    then have "s ! 0 \<le> t \<and> t \<le> s ! 1 - 1 \<and> 0 \<le> (0::nat) \<and> 0 < length L"
      using * assms unfolding sfirst using length_L by blast
    then have ?thesis by auto
  }
  ultimately show ?thesis by force
qed

lemma list_allones: 
  assumes "\<forall>i<length L. L!i = 1"
  shows "L = map (\<lambda>i. 1) [0 ..< length L]"
  using assms 
proof(induct L)
  case Nil
  then show ?case by simp
next
  case (Cons a L)
  then show ?case
    by (metis (no_types, lifting) length_map list_eq_iff_nth_eq map_nth nth_map) 
qed

lemma sum_list_constants:
  fixes L::"nat list" and k::"nat"
  assumes "\<forall>i<length L. L ! i = k"
  shows "sum_list L = k*(length L)"
  using assms by(induct L) force+

lemma length_is_composition_allones:
  assumes "is_composition_allones n L"
  shows "length L = n"
  using assms unfolding is_composition_allones_def is_composition_def
  by (metis mult_1 sum_list_constants)
  

lemma partial_sum_allones:
  assumes "(\<forall>i<length L. L ! i = 1)"
  assumes "i \<le> length L"
  shows "partial_sum L i = i"
  using assms
proof(induct "length L" arbitrary: i L)
  case 0
  then have i0: "i = 0" by auto
  have L_empty: "L = []" using 0 by auto
  show ?case using L_empty i0
    unfolding partial_sum_def by simp
next
  case (Suc x)
  then obtain H t where L_is: "L = H@[t]"
    by (metis length_Suc_conv_rev)
  have L_ones: "L = map (\<lambda>i. 1) [0..<length L]"
    using list_allones Suc by blast
  {
    assume *: "i = length L"
    then have takeall: "take i L = L"
      using take_all[of L i] by simp
    have ?case unfolding takeall partial_sum_def 
      using Suc(3) * sum_list_constants[of L 1] by simp 
  } moreover {
    assume *: "i < length L"
    have cond1: "x = length H"
      using Suc L_is by simp
    have cond2: "\<forall>i<length H. H ! i = 1"
      using Suc(3) unfolding L_is
      by (metis L_is Suc.hyps(2) Suc_lessD Suc_mono butlast_snoc cond1 nth_butlast) 
    have cond3: "i \<le> length H"
      using * L_is by auto
    then have ?case
      using Suc(1)[of H i, OF cond1 cond2 cond3]  
      unfolding partial_sum_def L_is by simp
  }
  ultimately show ?case using L_is Suc by fastforce
qed

lemma interval_times_allones: 
  assumes "a \<le> b"
  assumes "is_composition_allones (b - a + 1) L"
  assumes "i < length (interval_times a L)"
  shows "(interval_times a L)!i = a+i"
proof-
  have *: "map (\<lambda>i. a + partial_sum L i) [0..<length L + 1] ! i = a + partial_sum L i"
    using assms
    by (metis interval_times_def length_map length_upt nth_map_upt plus_nat.add_0) 
  have allones: "\<forall>i<length L. L!i = 1"
    using assms(2) unfolding is_composition_allones_def
    by blast
  have "length (interval_times a L) = length L + 1"
    using interval_times_length by simp
  then have "partial_sum L i = i"
    using partial_sum_allones[of L i]
    using allones assms by simp
  then have "a + partial_sum L i = a + i"
    by auto 
  then show ?thesis 
    unfolding interval_times_def
    using * by auto
qed

lemma allones_implies_is_composition:
  assumes "is_composition_allones n L"
  shows "is_composition n L"
  using assms unfolding is_composition_allones_def by blast

lemma allones_implies_is_composition_MLTL:
  assumes "is_composition_MLTL_allones \<phi>"
  shows "is_composition_MLTL \<phi>"
  using assms allones_implies_is_composition 
  by (induct \<phi>) simp_all


section \<open>MLTL Decomposition Lemmas\<close>

lemma LP_mltl_nnf: 
  fixes \<phi>::"'a mltl_ext" and \<psi>::"'a mltl" and k::"nat"
  assumes \<psi>_coformula: "\<psi> \<in> set (LP_mltl \<phi> k)"
  shows "\<exists>\<psi>_init. \<psi> = convert_nnf \<psi>_init"
proof-
  obtain \<psi>_init where "\<psi> = to_mltl (convert_nnf_ext \<psi>_init)"
    using assms unfolding LP_mltl.simps by auto
  then have "\<psi> = convert_nnf (to_mltl \<psi>_init)"
    using convert_nnf_ext_to_mltl_commute by metis
  then show ?thesis
    by blast
qed

lemma LP_mltl_element:
  fixes \<psi>::"'a mltl" and \<phi>::"'a mltl_ext"
  shows "\<psi> \<in> set (LP_mltl \<phi> k) \<longleftrightarrow> 
         (\<exists>\<psi>_ext \<in> set (LP_mltl_aux (convert_nnf_ext \<phi>) k). 
         \<psi> = to_mltl (convert_nnf_ext \<psi>_ext))"
  unfolding LP_mltl.simps by auto


section \<open>Lemmas for MLTL operators that operate over lists of mltl formulas\<close>

lemma pairs_alt: 
  shows "set (pairs L1 (h2#T2)) =  
         set ((map (\<lambda>x. (x, h2)) L1) @ (pairs L1 T2))"
proof(induct L1 arbitrary: h2 T2)
  case Nil
  then show ?case by simp
next
  case (Cons a L1)
  have pairs_fact: "set (pairs (a#L1) (h2#T2)) = set (map (Pair a) (h2 # T2) @ pairs L1 (h2 # T2))"
    unfolding pairs.simps by auto       
  have ih: "set (pairs L1 (h2 # T2)) = set (map (\<lambda>x. (x, h2)) L1 @ pairs L1 T2)"
    using Cons.hyps[of h2 T2] by simp
  have *: "set (pairs (a#L1) (h2#T2)) = 
  set (map (Pair a) (h2 # T2)) \<union> set (map (\<lambda>x. (x, h2)) L1 @ pairs L1 T2)"
    using pairs_fact ih by auto
  have **: "set (pairs (a # L1) T2) = set (map (Pair a) T2 @ pairs L1 T2)"
    using pairs.simps by simp
  then show ?case using * ** by auto
qed

lemma list_concat_set_union:
  shows "set(A@B) = set A \<union> set B"
  by simp

lemma pairs_empty_list: 
  shows "pairs A [] = []"
proof(induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  then show ?case by auto
qed

subsection \<open>Forward Direction Proofs\<close>
lemma pairs_member_fst_forward:
  assumes "List.member (pairs A B) x"
  shows "List.member A (fst x)" 
  using assms
proof(induct A)
  case Nil
  then have "pairs [] B = []" unfolding pairs.simps by simp
  then show ?case using member_rec(2) 
    by (metis Nil)
next
  case (Cons a A)
  {assume fst_x_is_a: "fst x = a"
    then have ?case 
      using Cons member_rec(1) by metis
  } moreover {
    assume fst_x_not_a: "fst x \<noteq> a"
    then have "\<not>(List.member (map (Pair a) B) x)"
      using in_set_member by force
    then have "List.member (pairs A B) x"
      using Cons(2) unfolding pairs.simps List.member_def by auto
    then have ih: "List.member A (fst x)"
      using Cons.hyps by blast
    then have "List.member (a # A) (fst x)"
      unfolding List.member_def by simp
    then have ?case
      using ih by blast
  }
  ultimately show ?case by blast
qed

lemma pairs_member_snd_forward:
  assumes "List.member (pairs A B) x"
  shows "List.member B (snd x)" 
  using assms
proof(induct B)
  case Nil
  have "pairs A [] = []"
    using pairs_empty_list by blast
  then show ?case
    by (metis local.Nil member_rec(2)) 
next
  case (Cons b B)
  have pairs_rec: "set (pairs A (b # B)) = set (map (\<lambda>x. (x, b)) A @ pairs A B)"
    using pairs_alt[of A b B] by blast
  {assume snd_x_is_b: "snd x = b"
    then have ?case 
      using Cons member_rec(1) by metis 
  } moreover {
    assume snd_x_not_b: "snd x \<noteq> b"
    then have "\<not>(List.member (map (\<lambda>x. (x, b)) A) x)"
      using in_set_member pairs_rec by force
    then have "List.member (pairs A B) x"
      using Cons(2) unfolding pairs_rec List.member_def by simp
    then have ih: "List.member B (snd x)"
      using Cons.hyps by blast
    then have "List.member (b # B) (snd x)"
      unfolding List.member_def by simp
    then have ?case
      using ih by blast
  }
  ultimately show ?case by blast
qed

lemma pairs_member_forward:
  assumes "List.member (pairs A B) x"
  shows "List.member A (fst x) \<and> List.member B (snd x)" 
  using assms pairs_member_fst_forward pairs_member_snd_forward by blast
  
lemma And_mltl_list_member_forward: 
  assumes "List.member (And_mltl_list D_x D_y) \<psi>"
  shows "\<exists>\<psi>1 \<psi>2. \<psi> = And_mltl_ext \<psi>1 \<psi>2 
  \<and> List.member D_x \<psi>1 \<and> List.member D_y \<psi>2"
proof-
  obtain x where "\<psi> = And_mltl_ext (fst x) (snd x) \<and> x \<in> set (pairs D_x D_y)"
    using assms unfolding And_mltl_list.simps List.member_def by auto
  then show ?thesis
    using pairs_member_forward[of D_x D_y x]
    by (simp add: in_set_member) 
qed 


subsection \<open>Converse Direction Proofs\<close>

lemma pairs_member_converse:
  assumes "List.member A (fst x)"
  assumes "List.member B (snd x)" 
  shows "List.member (pairs A B) x" 
  using assms
proof(induct A)
  case Nil
  then show ?case unfolding List.member_def by simp
next
  case (Cons a A)
  {assume *: "fst x = a"
    then have ?case using Cons
      unfolding pairs.simps List.member_def by force
  } moreover {
    assume *: "fst x \<in> set A"
    then have "List.member (pairs A B) x"
      using Cons.hyps Cons(3) unfolding List.member_def by simp
    then have ?case unfolding pairs.simps List.member_def by simp
  }
  ultimately show ?case using Cons(2) unfolding List.member_def by force
qed


lemma And_mltl_list_member_converse: 
  assumes "\<exists>\<psi>1 \<psi>2. \<psi> = And_mltl_ext \<psi>1 \<psi>2 
  \<and> List.member D_x \<psi>1 \<and> List.member D_y \<psi>2"
  shows "List.member (And_mltl_list D_x D_y) \<psi>"
proof-
  from assms obtain \<psi>1 \<psi>2 where "\<psi> = And_mltl_ext \<psi>1 \<psi>2 \<and> List.member D_x \<psi>1 \<and> List.member D_y \<psi>2" 
    by blast
  then show ?thesis using pairs_member_converse
    unfolding And_mltl_list.simps List.member_def by force
qed


subsection \<open>Biconditional Lemmas\<close>

lemma pairs_member:
  shows "(List.member A (fst x) \<and> List.member B (snd x)) \<longleftrightarrow> 
         List.member (pairs A B) x"
  using pairs_member_forward pairs_member_converse by blast
  
lemma And_mltl_list_member: 
  shows "(\<exists>\<psi>1 \<psi>2. \<psi> = And_mltl_ext \<psi>1 \<psi>2 
  \<and> List.member D_x \<psi>1 \<and> List.member D_y \<psi>2) \<longleftrightarrow>
        List.member (And_mltl_list D_x D_y) \<psi>"
  using And_mltl_list_member_forward And_mltl_list_member_converse by blast


section \<open>MLTL Decomposition Top Level Correctness\<close>

fun wpd_mltl:: "'a mltl \<Rightarrow> nat"
  where "wpd_mltl False\<^sub>m = 1"
  | "wpd_mltl True\<^sub>m = 1"
  | "wpd_mltl (Prop\<^sub>m (p)) = 1"
  | "wpd_mltl (Not\<^sub>m \<phi>) = wpd_mltl \<phi>"
  | "wpd_mltl (\<phi> And\<^sub>m \<psi>) = max (wpd_mltl \<phi>) (wpd_mltl \<psi>)"
  | "wpd_mltl (\<phi> Or\<^sub>m \<psi>) = max (wpd_mltl \<phi>) (wpd_mltl \<psi>)"
  | "wpd_mltl (G\<^sub>m[a,b] \<phi>) = b + (wpd_mltl \<phi>)"
  | "wpd_mltl (F\<^sub>m[a,b] \<phi>) = b + (wpd_mltl \<phi>)"
  | "wpd_mltl (\<phi> R\<^sub>m [a,b] \<psi>) = b + (max ((wpd_mltl \<phi>)) (wpd_mltl \<psi>))"
  | "wpd_mltl (\<phi> U\<^sub>m [a,b] \<psi>) = b + (max ((wpd_mltl \<phi>)) (wpd_mltl \<psi>))"

subsection \<open>Helper Lemmas\<close>

lemma wpd_geq_one: 
  shows "wpd_mltl \<phi> \<ge> 1"
  by (induct \<phi>) simp_all

lemma wpd_convert_nnf:
  fixes \<phi>::"'a mltl"
  shows "wpd_mltl (convert_nnf \<phi>) = wpd_mltl \<phi>"
proof(induction "depth_mltl \<phi>" arbitrary: \<phi> rule: less_induct)
  case less
  have not: "(\<And>\<phi>. depth_mltl \<phi> < Suc (depth_mltl p) \<Longrightarrow>
                wpd_mltl (convert_nnf \<phi>) = wpd_mltl \<phi>) \<Longrightarrow>
          \<phi> = Not\<^sub>m p \<Longrightarrow>
          wpd_mltl (convert_nnf (Not\<^sub>m p)) = wpd_mltl p" for p
  proof-
    assume ih: "\<And>\<phi>. depth_mltl \<phi> < Suc (depth_mltl p) \<Longrightarrow>
                wpd_mltl (convert_nnf \<phi>) = wpd_mltl \<phi>"
    assume notcase: "\<phi> = Not\<^sub>m p"
    show ?thesis using ih notcase less by (induct p) simp_all
  qed
  show ?case using less not by (cases \<phi>) auto
qed

lemma convert_nnf_ext_preserves_wpd: 
  shows "wpd_mltl (to_mltl (convert_nnf_ext \<phi>)) = 
         wpd_mltl (to_mltl \<phi>)"
proof(induction "depth_mltl (to_mltl \<phi>)" arbitrary: \<phi> rule: less_induct)
  case less
  have not: "(\<And>\<phi>. depth_mltl (to_mltl \<phi>)
                < Suc (depth_mltl (to_mltl x)) \<Longrightarrow>
                wpd_mltl (to_mltl (convert_nnf_ext \<phi>)) =
                wpd_mltl (to_mltl \<phi>)) \<Longrightarrow>
          \<phi> = Not\<^sub>c x \<Longrightarrow>
          wpd_mltl (to_mltl (convert_nnf_ext (Not\<^sub>c x))) =
          wpd_mltl (to_mltl x)" for x
  proof-
    assume ih: "(\<And>\<phi>. depth_mltl (to_mltl \<phi>)
                < Suc (depth_mltl (to_mltl x)) \<Longrightarrow>
                wpd_mltl (to_mltl (convert_nnf_ext \<phi>)) =
                wpd_mltl (to_mltl \<phi>))"
    assume shape: "\<phi> = Not\<^sub>c x"
    show ?thesis using ih shape less by (induct x) simp_all
  qed
  show ?case using less not
    by (cases \<phi>) auto
qed  


lemma nnf_intervals_welldef:
  assumes "intervals_welldef F1"
  shows "intervals_welldef (convert_nnf F1)"
  using assms
proof (induct "depth_mltl F1" arbitrary: F1 rule: less_induct)
  case less
  have iwd: "intervals_welldef F2 \<Longrightarrow>
          F1 = Not\<^sub>m F2 \<Longrightarrow>
          intervals_welldef (convert_nnf (Not\<^sub>m F2))"
    for F2  using less by (cases F2) simp_all
  then show ?case using less by (cases F1) simp_all
qed

lemma is_composition_convert_nnf_ext: 
  fixes \<phi>::"'a mltl_ext"
  assumes "intervals_welldef (to_mltl \<phi>)"
  assumes "is_composition_MLTL \<phi>"
  shows "is_composition_MLTL (convert_nnf_ext \<phi>)"
  using assms
proof(induct "depth_mltl (to_mltl \<phi>)" arbitrary: \<phi> rule: less_induct)
  case less
  have not_case: "(\<And>\<phi>. depth_mltl (to_mltl \<phi>)
                < Suc (depth_mltl (to_mltl x4)) \<Longrightarrow>
                intervals_welldef (to_mltl \<phi>) \<Longrightarrow>
                is_composition_MLTL \<phi> \<Longrightarrow>
                is_composition_MLTL (convert_nnf_ext \<phi>)) \<Longrightarrow>
          intervals_welldef (to_mltl x4) \<Longrightarrow>
          is_composition_MLTL x4 \<Longrightarrow>
          \<phi> = Not\<^sub>c x4 \<Longrightarrow>
          is_composition_MLTL (convert_nnf_ext (Not\<^sub>c x4))" for x4
    using less by (induct x4) simp_all 
   show ?case using less not_case by (cases \<phi>) auto
qed


lemma is_composition_allones_convert_nnf_ext: 
  fixes \<phi>::"'a mltl_ext"
  assumes "intervals_welldef (to_mltl \<phi>)"
  assumes "is_composition_MLTL_allones \<phi>"
  shows "is_composition_MLTL_allones (convert_nnf_ext \<phi>)"
  using assms
proof(induct "depth_mltl (to_mltl \<phi>)" arbitrary: \<phi> rule: less_induct)
  case less
  have not_case: "(\<And>\<phi>. depth_mltl (to_mltl \<phi>)
                < Suc (depth_mltl (to_mltl x4)) \<Longrightarrow>
                intervals_welldef (to_mltl \<phi>) \<Longrightarrow>
                is_composition_MLTL_allones \<phi> \<Longrightarrow>
                is_composition_MLTL_allones (convert_nnf_ext \<phi>)) \<Longrightarrow>
          intervals_welldef (to_mltl x4) \<Longrightarrow>
          is_composition_MLTL_allones x4 \<Longrightarrow>
          \<phi> = Not\<^sub>c x4 \<Longrightarrow>
          is_composition_MLTL_allones (convert_nnf_ext (Not\<^sub>c x4))" for x4
    using less by (induct x4) simp_all 
   show ?case using less not_case
     by (cases \<phi>) auto
qed


(*This function is not executable since it's used only in the proofs*)
function Ands_mltl_ext:: "'a mltl_ext list \<Rightarrow> 'a mltl_ext"
  where "Ands_mltl_ext [] = True_mltl_ext"
  | "Ands_mltl_ext (H@[t]) = (if (length H = 0) then t 
     else (And_mltl_ext (Ands_mltl_ext H) t))"
  using rev_exhaust by auto
termination by (relation  "measure (\<lambda>L. length L)") auto


lemma Ands_mltl_semantics: 
  assumes "length X \<ge> 1"
  shows "semantics_mltl_ext \<pi> (Ands_mltl_ext X) \<longleftrightarrow>
         (\<forall>x \<in> set X. semantics_mltl_ext \<pi> x)"
  using assms
proof(induct "length X-1" arbitrary: X)
  case 0
  then obtain x where X_is: "X = [x]"
    by (metis butlast_snoc diff_is_0_eq le_antisym length_0_conv length_butlast list.exhaust rotate1.simps(2) rotate1_length01 zero_neq_one) 
  then show ?case unfolding X_is 
    using Ands_mltl_ext.simps(2)[of "[]" x] by simp
next
  case (Suc n)
  then obtain H t where X_is: "X = H@[t]"
    by (metis Ands_mltl_ext.cases One_nat_def Suc_n_not_le_n gen_length_code(1) length_code)
  then have length_H: "length H = n+1" using Suc by auto
  then have cond1: "n = length H - 1" by simp
  have cond2: "length H \<ge> 1" using length_H by simp
  have semantics_H: "semantics_mltl_ext \<pi> (Ands_mltl_ext H) =
    (\<forall>x. x \<in> set H \<longrightarrow> semantics_mltl_ext \<pi> x)"
    using Suc(1)[OF cond1 cond2] unfolding Ball_def by simp
  have "(semantics_mltl_ext \<pi> (Ands_mltl_ext H) \<and> 
         semantics_mltl_ext \<pi> t) \<longleftrightarrow> 
        (\<forall>x. x \<in> set (H @ [t]) \<longrightarrow> semantics_mltl_ext \<pi> x)"
    using semantics_H by auto 
  then have "semantics_mltl_ext \<pi> (And_mltl_ext (Ands_mltl_ext H) t) =
    (\<forall>x. x \<in> set (H @ [t]) \<longrightarrow> semantics_mltl_ext \<pi> x)"
    unfolding semantics_mltl_ext_def to_mltl.simps by simp
  then show ?case unfolding Ball_def X_is Ands_mltl_ext.simps
    using length_H by simp
qed

lemma in_Global_mltl_decomp: 
  assumes "length D_\<phi> > 1"
  assumes "\<psi> \<in> set (Global_mltl_decomp D_\<phi> a n L)"
  shows "\<exists>X. ((\<psi> = Ands_mltl_ext X \<and> 
             (\<forall>x. List.member X x \<longrightarrow> 
             (\<exists>y \<in> set D_\<phi>. (\<exists>k. a \<le> k \<and> k \<le> (a+n) \<and> x = Global_mltl_ext k k [1] y)))) \<and>
             (length X = Suc n))"
  using assms
proof(induct n arbitrary: D_\<phi> \<psi> a)
  case 0
  then obtain x where x_in: "x \<in> set D_\<phi>" and 
                      \<psi>_is: "\<psi> = Global_mltl_ext a a [1] x" 
    unfolding Global_mltl_decomp.simps Global_mltl_list.simps by auto
  then have "\<psi> = Ands_mltl_ext [Global_mltl_ext a a [1] x]" 
    using Ands_mltl_ext.simps(2)[of "[]" "Global_mltl_ext a a [1] x"] by auto
  then show ?case
    by (metis add.right_neutral length_Cons list.size(3) member_rec(1) member_rec(2) order_refl x_in) 
next
  case (Suc x)
  then have "\<psi> \<in> set (And_mltl_list (Global_mltl_decomp D_\<phi> a x L)
               (Global_mltl_list D_\<phi> (a + Suc x) (a + Suc x) [1]))"
    unfolding Global_mltl_decomp.simps by force
  then obtain first second where \<psi>_is: "\<psi> = And_mltl_ext first second" 
      and first_in: "first \<in> set (Global_mltl_decomp D_\<phi> a x L)" 
      and second_in: "second \<in> set (Global_mltl_list D_\<phi> (a + Suc x) (a + Suc x) [1])"
    using And_mltl_list_member by (metis in_set_member) 
  from Suc.hyps[OF Suc.prems(1) first_in] obtain X where 
      X1: "first = Ands_mltl_ext X" and 
      X2: "(\<forall>xa. List.member X xa \<longrightarrow>
            (\<exists>y\<in>set D_\<phi>. \<exists>k\<ge>a. k \<le> a + x \<and> xa = Global_mltl_ext k k [1] y))" and
      X3: "length X = (Suc x)"
    by blast
  from second_in obtain x_second where 
      second_is: "second = Global_mltl_ext (a + Suc x) (a + Suc x) [1] x_second"
  and x_second_in: "x_second \<in> set D_\<phi>" by auto
  have prop1: "\<psi> = Ands_mltl_ext (X@[second])" using \<psi>_is X1 
    unfolding Ands_mltl_ext.simps using X3 by auto
  have prop2: "(\<exists>y\<in>set D_\<phi>. \<exists>k\<ge>a. k \<le> a + Suc x \<and> xa = Global_mltl_ext k k [1] y)"
    if prem: "List.member (X@[second]) xa" for xa
    using X2 second_is 
  proof-
    have split: "(List.member X xa) \<or> xa = second"
      using prem
      by (metis in_set_member member_rec(1) rotate1.simps(2) set_rotate1) 
    {assume in_X: "List.member X xa"
      have ?thesis using X2 in_X by force
    } moreover {
      assume in_second: "xa = second"
      have ?thesis using in_second second_is
        by (simp add: x_second_in) 
    }
    ultimately show ?thesis using split by blast
  qed
  have prop3: "length (X@[second]) = Suc (Suc x)"
    using X3 by simp
  then show ?case 
    using prop1 prop2 prop3 by blast
qed


lemma in_Global_mltl_decomp_exact_forward: 
  assumes "length D_\<phi> > 1"
  assumes "\<psi> \<in> set (Global_mltl_decomp D_\<phi> a n L)"
  shows "\<exists>X. ((\<psi> = Ands_mltl_ext X \<and> 
             (\<forall>i < length X. (\<exists>y \<in> set D_\<phi>. (X!i) = Global_mltl_ext (a+i) (a+i) [1] y)))) \<and>
             (length X = Suc n)"
  using assms
proof(induct n arbitrary: D_\<phi> \<psi> a)
  case 0
  then obtain x where x_in: "x \<in> set D_\<phi>" and 
                      \<psi>_is: "\<psi> = Global_mltl_ext a a [1] x" 
    unfolding Global_mltl_decomp.simps Global_mltl_list.simps by auto
  then have "\<psi> = Ands_mltl_ext [Global_mltl_ext a a [1] x]" 
    using Ands_mltl_ext.simps(2)[of "[]" "Global_mltl_ext a a [1] x"] by auto
  then show ?case
    using x_in by auto 
next
  case (Suc n)
  obtain H t where \<psi>_is: "\<psi> = And_mltl_ext H t"
               and H_in: "H \<in> set (Global_mltl_decomp D_\<phi> a n L)"
               and t_in: "t \<in> set (Global_mltl_list D_\<phi> (a + Suc n) (a + Suc n) [1])"
    using Suc(3) unfolding Global_mltl_decomp.simps 
    using And_mltl_list_member unfolding List.member_def
    by (metis add_diff_cancel_left' plus_1_eq_Suc) 
  obtain x where t_is: "t = Global_mltl_ext (a+Suc n) (a+Suc n) [1] x"
             and x_in: "x \<in> set D_\<phi>"
    using t_in unfolding Global_mltl_list.simps by auto
  have "\<exists>X. (H = Ands_mltl_ext X \<and>
       (\<forall>i<length X. \<exists>y\<in>set D_\<phi>. X ! i = Global_mltl_ext (a + i) (a + i) [1] y)) \<and>
      length X = Suc n"
    using Suc.hyps[of D_\<phi> H a] Suc.prems H_in by blast
  then obtain X where H_is: "H = Ands_mltl_ext X" 
                  and X_prop: "\<forall>i<length X. \<exists>y\<in>set D_\<phi>. X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
                  and length_X: "length X = Suc n"
    by blast
  have \<psi>_is: "\<psi> = Ands_mltl_ext (X@[t])"
    unfolding Ands_mltl_ext.simps using length_X \<psi>_is
    by (simp add: H_is) 
  have property: "\<exists>y\<in>set D_\<phi>. (X@[t]) ! i = Global_mltl_ext (a + i) (a + i) [1] y"
    if i_bound: "i<length (X@[t])" for i
  proof-
    {
      assume *: "i < length X"
      then have "X ! i = (X@[t])!i" using length_X
        by (simp add: nth_append) 
      then have ?thesis using X_prop length_X * by metis
    } moreover {
      assume *: "i = length X"
      have "(X@[t])!i = t"
        using length_X *
        by (metis nth_append_length) 
      then have ?thesis using t_is * length_X
        by (simp add: x_in) 
    }
    ultimately show ?thesis using i_bound by fastforce
  qed
  have len: "length (X@[t]) = Suc (Suc n)"
    using length_X by auto
  then show ?case
    using \<psi>_is property len by blast
qed

lemma in_Global_mltl_decomp_exact_converse: 
  fixes n::"nat" and X::"'a mltl_ext list"
  assumes "length D_\<phi> > 1"
  assumes "\<psi> = Ands_mltl_ext X"
  assumes "(\<forall>i < length X. (\<exists>y \<in> set D_\<phi>. 
           (X!i) = Global_mltl_ext (a+i) (a+i) [1] y))"
  assumes "length X = n+1"
  shows "\<psi> \<in> set (Global_mltl_decomp D_\<phi> a n L)"
  using assms
proof(induct n arbitrary: X \<psi> a)
  case 0
  then have length_X: "length X = 1" by auto
  then have "\<exists>x. X = [x]"
    by (metis Suc_eq_plus1 add_cancel_right_left length_Cons list.size(3) neq_Nil_conv zero_eq_add_iff_both_eq_0 zero_neq_one) 
  then obtain x where X_is: "X = [x]" by blast
  then obtain y where x_is: "x = Global_mltl_ext a a [1] y"
                  and y_in: "y \<in> set D_\<phi>"
    using 0 by auto
  then show ?case unfolding 0(2) X_is
    using Ands_mltl_ext.simps(2)[of "[]" x] by simp
next
  case (Suc n)
  then have length_X: "length X = n+2" by simp
  then obtain H t where X_is: "X = H@[t]"
    by (metis Suc.prems(4) Suc_eq_plus1 length_Suc_conv_rev) 
  have length_H: "length H = n+1" using length_X X_is by auto
  have \<psi>_is: "\<psi> = And_mltl_ext (Ands_mltl_ext H) t"
    using Suc(3) unfolding X_is Ands_mltl_ext.simps 
    using length_H by simp
  have H_prop: "\<exists>y\<in>set D_\<phi>. H ! i = Global_mltl_ext (a + i) (a + i) [1] y"
    if i_bound: "i<length H" for i
  proof-
    have index: "(H @ [t]) ! i = H!i"
      using i_bound by (simp add: nth_append) 
    then have "\<exists>y\<in>set D_\<phi>. (H @ [t]) ! i = Global_mltl_ext (a + i) (a + i) [1] y"
      using i_bound Suc(4) unfolding X_is
      by (metis Suc.prems(4) Suc_eq_plus1 X_is length_H plus_1_eq_Suc trans_less_add2) 
    then show ?thesis
      using index by auto
  qed
  then have H_prop: "\<forall>i<length H.
       \<exists>y\<in>set D_\<phi>. H ! i = Global_mltl_ext (a + i) (a + i) [1] y"
    by blast
  have H_in: "Ands_mltl_ext H \<in> set (Global_mltl_decomp D_\<phi> a n L)"
    using Suc(1)[OF Suc(2) _ H_prop, of "(Ands_mltl_ext H)"] 
    using length_H by blast
  have t_is: "\<exists>y\<in>set D_\<phi>. t = Global_mltl_ext (a + n + 1) (a + n + 1) [1] y"
    using Suc(4) unfolding X_is using length_X
    by (metis X_is add.assoc length_H less_add_one nth_append_length one_add_one)
  then obtain y where t_is: "t = Global_mltl_ext (a + n + 1) (a + n + 1) [1] y"
                  and y_in: "y \<in> set D_\<phi>"
    by blast
  have t_in: "t \<in> set (Global_mltl_list D_\<phi> (a + Suc n) (a + Suc n) [1])"
    using y_in t_is by simp
  show ?case unfolding \<psi>_is Global_mltl_decomp.simps
    using t_in H_in And_mltl_list_member[of \<psi> "(Global_mltl_decomp D_\<phi> a n) L" "(Global_mltl_list D_\<phi> (a + Suc n) (a + Suc n) [1])"] 
    unfolding List.member_def \<psi>_is by auto
qed

lemma case_split_helper: 
  assumes "x \<in> A \<union> B \<union> C"
  assumes "x \<in> A \<Longrightarrow> P x" and "x \<in> B \<Longrightarrow> P x" and "x \<in> C \<Longrightarrow> P x"
  shows "P x"
  using assms by blast

lemma LP_mltl_aux_intervals_welldef:
  fixes \<phi> \<psi>::"'a mltl_ext"
  assumes "intervals_welldef (to_mltl \<phi>)"
  assumes "\<psi> \<in> set (LP_mltl_aux (convert_nnf_ext \<phi>) k)"
  assumes "is_composition_MLTL \<phi>"
  shows "intervals_welldef (to_mltl \<psi>)"
  using assms
proof(induct k arbitrary: \<phi> \<psi>)
  case 0
  then show ?case unfolding LP_mltl_aux.simps
    by (simp add: convert_nnf_and_convert_nnf_ext nnf_intervals_welldef)
next
  case (Suc k)
  then show ?case 
  proof(cases "convert_nnf_ext \<phi>")
    case True_mltl_ext
    then show ?thesis using Suc by simp
  next
    case False_mltl_ext
    then show ?thesis using Suc by simp
  next
    case (Prop_mltl_ext p)
    then show ?thesis using Suc by simp
  next
    case (Not_mltl_ext q)
    then have "\<exists>p. q = Prop_mltl_ext p"
      using convert_nnf_form_Not_Implies_Prop
      by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
    then obtain p where "q = Prop_mltl_ext p" by auto
    then show ?thesis using Suc
      by (simp add: Not_mltl_ext) 
  next
    case (And_mltl_ext \<alpha> \<beta>)
    obtain x y where \<psi>_is: "\<psi> = And_mltl_ext x y" 
               and x_in: "x \<in> set (LP_mltl_aux (convert_nnf_ext \<alpha>) k)"
               and y_in: "y \<in> set (LP_mltl_aux (convert_nnf_ext \<beta>) k)"
      using Suc(3) unfolding And_mltl_ext LP_mltl_aux.simps
      by (meson And_mltl_list_member in_set_member) 
    then show ?thesis unfolding \<psi>_is to_mltl.simps intervals_welldef.simps
      using Suc.hyps x_in y_in
      by (metis And_mltl_ext Suc.prems(1) Suc.prems(3) convert_nnf_ext_to_mltl_commute intervals_welldef.simps(5) nnf_intervals_welldef is_composition_MLTL.simps(1) is_composition_convert_nnf_ext to_mltl.simps(5)) 
  next
    case (Or_mltl_ext \<alpha> \<beta>)
    let ?Dx = "LP_mltl_aux (convert_nnf_ext \<alpha>) k"
    let ?Dy = "LP_mltl_aux (convert_nnf_ext \<beta>) k"
    {assume *: "\<psi> \<in> set (And_mltl_list ?Dx ?Dy)"
      then obtain x y where \<psi>_is: "\<psi> = And_mltl_ext x y" 
               and x_in: "x \<in> set ?Dx" and y_in: "y \<in> set ?Dy"
        using Suc(3) LP_mltl_aux.simps
        by (meson And_mltl_list_member in_set_member) 
    then have ?thesis unfolding Or_mltl_ext
      by (metis Or_mltl_ext Suc.hyps Suc.prems(1) Suc.prems(3) convert_nnf_ext_to_mltl_commute intervals_welldef.simps(5) intervals_welldef.simps(6) nnf_intervals_welldef is_composition_MLTL.simps(2) is_composition_convert_nnf_ext to_mltl.simps(5) to_mltl.simps(6))
    } moreover {
      assume *: "\<psi> \<in> set (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy)"
      then obtain y where \<psi>_is: "\<psi> = And_mltl_ext (Not\<^sub>c \<alpha>) y" 
               and y_in: "y \<in> set ?Dy"
        using Suc(3) 
        using And_mltl_list_member[of \<psi> ?Dy "[Not\<^sub>c \<alpha>]"] by auto
      have lhs_welldef: "intervals_welldef (to_mltl \<alpha>)"
        by (metis Or_mltl_ext Suc.prems(1) convert_nnf_ext_to_mltl_commute intervals_welldef.simps(6) nnf_intervals_welldef to_mltl.simps(6))
      have rhs_welldef: "intervals_welldef (to_mltl y)"
        using y_in Suc.prems unfolding Or_mltl_ext
        by (metis Or_mltl_ext Suc.hyps convert_nnf_ext_to_mltl_commute intervals_welldef.simps(6) nnf_intervals_welldef is_composition_MLTL.simps(2) is_composition_convert_nnf_ext to_mltl.simps(6))
      then have ?thesis
        unfolding \<psi>_is to_mltl.simps intervals_welldef.simps
        using lhs_welldef rhs_welldef by blast
    } moreover {
      assume *: "\<psi> \<in> set (And_mltl_list ?Dx [Not\<^sub>c \<beta>])"
      then obtain x where \<psi>_is: "\<psi> = And_mltl_ext x (Not\<^sub>c \<beta>)" 
               and x_in: "x \<in> set ?Dx"
        using Suc(3) And_mltl_list_member[of \<psi> ?Dx "[Not\<^sub>c \<beta>]"]
        by (metis in_set_member member_rec(1) member_rec(2)) 
      have lhs_welldef: "intervals_welldef (to_mltl \<beta>)"
        by (metis Or_mltl_ext Suc.prems(1) convert_nnf_ext_to_mltl_commute intervals_welldef.simps(6) nnf_intervals_welldef to_mltl.simps(6))
      have rhs_welldef: "intervals_welldef (to_mltl x)"
        using x_in Suc.prems unfolding Or_mltl_ext
        by (metis Or_mltl_ext Suc.hyps convert_nnf_ext_to_mltl_commute intervals_welldef.simps(6) nnf_intervals_welldef is_composition_MLTL.simps(2) is_composition_convert_nnf_ext to_mltl.simps(6))
      then have ?thesis
        unfolding \<psi>_is to_mltl.simps intervals_welldef.simps
        using lhs_welldef rhs_welldef by blast
    }
    ultimately show ?thesis 
      using Suc(3) unfolding Or_mltl_ext LP_mltl_aux.simps 
      using list_concat_set_union
      by (metis UnE) 
  next
    case (Future_mltl_ext a b L \<alpha>)
    let ?D = "LP_mltl_aux (convert_nnf_ext \<alpha>) k"
    let ?s = "interval_times a L"
    have "convert_nnf (to_mltl \<phi>) = Future_mltl a b (to_mltl \<alpha>)"
      using Future_mltl_ext convert_nnf_and_convert_nnf_ext
      by (simp add: convert_nnf_ext_to_mltl_commute)
    then have a_leq_b: "a \<le> b"
      using Suc (2) Future_mltl_ext nnf_intervals_welldef 
      by fastforce
    from is_composition_convert_nnf_ext[OF Suc(2) Suc(4)]
        have "is_composition_MLTL (convert_nnf_ext \<phi>)"
          .
      then have is_comp: "is_composition (b-a+1) L"
        unfolding Future_mltl_ext is_composition_MLTL.simps by blast
    {assume *: "\<psi> \<in> set (Future_mltl_list ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
      then obtain x where \<psi>_is: "\<psi> = Future_mltl_ext (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] x"
                    and x_in: "x \<in> set ?D"
        unfolding Future_mltl_list.simps by fastforce
      from is_comp have welldef: "?s ! 0 \<le> ?s ! 1 -1"
        using interval_times_diff_ge[OF a_leq_b is_comp _ , of 0 ?s]
        by (metis a_leq_b add_0 add_le_imp_le_diff gr_zeroI interval_times_first interval_times_last less_iff_succ_less_eq order_less_irrefl)
      have ih: "intervals_welldef (to_mltl x)"
        using Suc x_in
        by (metis Future_mltl_ext convert_nnf_ext_to_mltl_commute intervals_welldef.simps(7) nnf_intervals_welldef is_composition_MLTL.simps(5) is_composition_convert_nnf_ext to_mltl.simps(7)) 
      then have ?thesis 
        unfolding \<psi>_is to_mltl.simps intervals_welldef.simps 
        using welldef ih by blast 
    } moreover {
      assume *: "\<psi> \<in> set (concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext (?s ! 0)
                              (?s ! i - 1) [?s!i-?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i]))
                  [1..<length L]))"
      then obtain i where \<psi>_is: "\<psi> \<in> set ((And_mltl_list
                            [Global_mltl_ext (?s ! 0)
                              (?s ! i - 1) [?s!i-?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i])
                  ))"
        and i_in: "i \<in> {1..<length L}"
        by force
      then obtain x where \<psi>_is: "\<psi> = ((And_mltl_ext
                            (Global_mltl_ext (?s ! 0)
                              (?s ! i - 1) [?s!i-?s!0] (Not\<^sub>c \<alpha>))
                            (Future_mltl_ext (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i] x)))"
        and x_in: "x \<in> set ?D"
        by auto
      from is_comp have welldef1: "interval_times a L ! 0 \<le> interval_times a L ! i - 1"
        using i_in 
        using interval_times_diff_ge_general[OF a_leq_b is_comp _ , of i 0 ?s]
        by force
      have welldef2: "interval_times a L ! i \<le> interval_times a L ! (i + 1) - 1 "
        using i_in 
        by (metis a_leq_b add.commute add_le_imp_le_diff atLeastLessThan_iff interval_times_diff_ge is_comp less_eq_Suc_le plus_1_eq_Suc)
        
      have ih1: "intervals_welldef (to_mltl \<alpha>)"
        using Suc x_in
        by (metis \<open>convert_nnf (to_mltl \<phi>) = Future_mltl a b (to_mltl \<alpha>)\<close> intervals_welldef.simps(7) nnf_intervals_welldef) 
      have ih2: "intervals_welldef (to_mltl x)"
        using Suc 
        by (metis Future_mltl_ext \<open>is_composition_MLTL (convert_nnf_ext \<phi>)\<close> ih1 is_composition_MLTL.simps(5) x_in)
      have ?thesis unfolding \<psi>_is to_mltl.simps intervals_welldef.simps 
        using ih1 ih2 welldef1 welldef2
        by auto
    }
    ultimately show ?thesis 
      using Suc(3) unfolding Future_mltl_ext LP_mltl_aux.simps 
      using list_concat_set_union
      by (metis (no_types, lifting) Un_iff) 
  next
    case (Global_mltl_ext a b L \<alpha>)
    let ?D_\<phi> = "LP_mltl_aux (convert_nnf_ext \<alpha>) k"
    have nnf_\<phi>: "convert_nnf (to_mltl \<phi>) = Global_mltl a b (to_mltl \<alpha>)"
      using Global_mltl_ext convert_nnf_and_convert_nnf_ext
      by (simp add: convert_nnf_ext_to_mltl_commute)
    then have a_leq_b: "a \<le> b"
      using Suc (2) Global_mltl_ext nnf_intervals_welldef 
      by fastforce
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
      using Suc(4) Global_mltl_ext Suc.prems(1) is_composition_convert_nnf_ext by fastforce
    have L_composition: "is_composition (b-a+1) L"
      by (metis Global_mltl_ext Suc.prems(1) Suc.prems(3) is_composition_MLTL.simps(3) is_composition_convert_nnf_ext) 
    {assume *: "length ?D_\<phi> \<le> 1"
      then have \<psi>: "\<psi> = Global_mltl_ext a b L \<alpha>"
        using Suc(3)
        unfolding Global_mltl_ext LP_mltl_aux.simps
        by simp
      have ih1: "intervals_welldef (to_mltl \<alpha>)"
        using Suc nnf_\<phi>
        by (metis intervals_welldef.simps(8) nnf_intervals_welldef)
      then have ?thesis 
        using a_leq_b unfolding \<psi> to_mltl.simps
        intervals_welldef.simps by auto
    } moreover {assume *: "length ?D_\<phi> > 1"
      then have \<psi>_in: "\<psi> \<in> set (Global_mltl_decomp ?D_\<phi> a (b - a) L)"
        using Suc(3)
        unfolding Global_mltl_ext LP_mltl_aux.simps
        by simp
      then obtain X where \<psi>_is: "\<psi> = Ands_mltl_ext X" and
         X_fact: "(\<forall>x \<in> set X. 
              (\<exists>y\<in>set (LP_mltl_aux (convert_nnf_ext \<alpha>) k).
                  \<exists>k\<ge>a. k \<le> a + (b - a) \<and> x = Global_mltl_ext k k [1] y))"
        and length_X: "length X = Suc (b - a)"
        using in_Global_mltl_decomp[OF * \<psi>_in] 
        unfolding List.member_def by blast
      have X_ih: "intervals_welldef (to_mltl x)"
        if x_in: "x \<in> set X" for x
      proof- 
        obtain y k where y_in: "y \<in> set ?D_\<phi>" 
                     and k_bound: "a \<le> k \<and> k \<le> b"
                     and x_is: "x = Global_mltl_ext k k [1] y"
          using X_fact a_leq_b x_in by fastforce 
        show ?thesis using y_in Suc
          unfolding x_is to_mltl.simps intervals_welldef.simps
          by (metis Global_mltl_ext intervals_welldef.simps(8) is_composition_MLTL.simps(3) is_composition_convert_nnf_ext nnf_\<phi> nnf_intervals_welldef order_refl) 
      qed
      have ?thesis 
        using \<psi>_is X_ih length_X
      proof(induct "b-a" arbitrary: b a \<psi> X)
        case 0
        then obtain x where X_is: "X = [x]"
          by (metis length_0_conv length_Suc_conv) 
        have "\<psi> = x"
          using Ands_mltl_ext.simps(2) 0
          by (metis X_is append_self_conv2 length_0_conv)  
        then show ?case using 0(3)[of x] unfolding X_is by auto
      next
        case (Suc n)
        then have "length X = n + 2" by linarith
        then obtain H t where X_is: "X = H@[t]" and length_H: "length H = length X-1"
          by (metis Suc.prems(3) diff_Suc_1 length_Suc_conv_rev)
        have \<psi>_is: "\<psi> = And_mltl_ext (Ands_mltl_ext H) t"
          using Suc(3) unfolding X_is Ands_mltl_ext.simps using length_H
          by (metis One_nat_def Suc.hyps(2) Suc.prems(3) diff_Suc_1' nat.distinct(1)) 
        have t_ih: "intervals_welldef (to_mltl t)"
          using X_is Suc by force
        have "(\<And>x. x \<in> set H \<Longrightarrow> intervals_welldef (to_mltl x))"
          using Suc.prems unfolding X_is by auto
        then have H_ih: "intervals_welldef (to_mltl (Ands_mltl_ext H))"
          using Suc.hyps(1)[of _ _ "Ands_mltl_ext H" H]
          by (metis Suc.hyps(2) Suc.prems(3) diff_Suc_1 length_H) 
        show ?case unfolding \<psi>_is to_mltl.simps
          using t_ih H_ih by simp
      qed
    }
    ultimately show ?thesis
      by linarith
  next
    case (Until_mltl_ext \<alpha> a b L \<beta>)
    let ?D_\<beta> = "LP_mltl_aux (convert_nnf_ext \<beta>) k"
    let ?s = "interval_times a L"
    have a_leq_b: "a \<le> b" using Suc(2)
        by (metis Until_mltl_ext convert_nnf_ext_to_mltl_commute intervals_welldef.simps(9) to_mltl.simps(9) nnf_intervals_welldef) 
    have composition: "is_composition_MLTL (Until_mltl_ext \<alpha> a b L \<beta>)"
          using Suc(4) Until_mltl_ext
          by (metis Suc.prems(1) is_composition_convert_nnf_ext) 
    have interval_composition: "is_composition (b - a + 1) L"
      using composition by simp 
    have length_L: "0 < length L"
      using interval_composition
      by (meson add_gr_0 composition_length_lb less_numeral_extra(1))
    have \<alpha>_ih: "intervals_welldef (to_mltl \<alpha>)"
      using Suc Until_mltl_ext convert_nnf_ext_to_mltl_commute
      by (metis  intervals_welldef.simps(9) to_mltl.simps(9) nnf_intervals_welldef) 
    have \<beta>_ih: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) Until_mltl_ext
      by (metis convert_nnf_ext_to_mltl_commute intervals_welldef.simps(9) to_mltl.simps(9) nnf_intervals_welldef)
    {assume *: "\<psi> \<in> set (Until_mltl_list \<alpha> ?D_\<beta> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
      then obtain x where \<psi>_is: "\<psi> = Until_mltl_ext \<alpha> (?s!0) (?s!1-1) [?s!1-?s!0] x"
                      and x_in: "x \<in> set (?D_\<beta>)"
        by auto
      have fact1: "interval_times a L ! 0 \<le> interval_times a L ! 1 - 1"
        unfolding is_composition_def 
        using interval_times_diff_ge[OF a_leq_b interval_composition length_L, of ?s] 
        by auto 
      have x_ih: "intervals_welldef (to_mltl x)"
        using x_in Suc.hyps[of \<beta> x] Suc.prems
        using \<beta>_ih composition is_composition_MLTL.simps(6) by blast
      have ?thesis unfolding \<psi>_is unfolding to_mltl.simps
        unfolding intervals_welldef.simps
        using fact1 \<alpha>_ih x_ih by blast
    } moreover {
      assume *: "\<psi> \<in> set (concat
                (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext
                              (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))]
                            (Until_mltl_list \<alpha> ?D_\<beta> (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i]))
                  [1..<length L]))"
      then obtain i x where 
      \<psi>_is: "\<psi> = And_mltl_ext (Global_mltl_ext (?s!0) (?s!i-1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
             (Until_mltl_ext \<alpha> (?s!i) (?s!(i+1)-1) [(?s!(i+1)) - (?s!i)] x)"
      and i_bound: "1 \<le> i \<and> i < length L" 
      and x_in: "x \<in> set ?D_\<beta>"
        by auto
      have fact1: "interval_times a L ! 0 \<le> interval_times a L ! i - 1"
        using i_bound a_leq_b
        using interval_times_diff_ge_general[OF a_leq_b interval_composition, of i 0 ?s]
        by force
      have fact2: "interval_times a L ! i \<le> interval_times a L ! (i + 1) - 1"
        using i_bound
        using interval_times_diff_ge[OF a_leq_b interval_composition, of i ?s]
        by auto
      have x_ih: "intervals_welldef (to_mltl x)"
        using Suc.hyps \<beta>_ih composition is_composition_MLTL.simps(6) x_in by blast
      have ?thesis unfolding \<psi>_is to_mltl.simps 
        unfolding intervals_welldef.simps 
        using fact1 fact2 \<alpha>_ih \<beta>_ih x_ih by blast
    }
    ultimately show ?thesis using Suc(3) list_concat_set_union
      unfolding Until_mltl_ext LP_mltl_aux.simps
      by (metis (mono_tags, lifting) UnE) 
  next
    case (Release_mltl_ext \<alpha> a b L \<beta>)
    let ?D = "LP_mltl_aux (convert_nnf_ext \<alpha>) k"
    let ?s = "interval_times a L"
    have \<alpha>_ih: "intervals_welldef (to_mltl \<alpha>)"
      using Suc(2) Release_mltl_ext convert_nnf_ext_to_mltl_commute
      by (metis intervals_welldef.simps(10) to_mltl.simps(10) nnf_intervals_welldef)
    have \<beta>_ih: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) Release_mltl_ext convert_nnf_ext_to_mltl_commute
      by (metis intervals_welldef.simps(10) to_mltl.simps(10) nnf_intervals_welldef)
    have a_leq_b: "a \<le> b" using Suc(2) Release_mltl_ext
      by (metis convert_nnf_ext_to_mltl_commute intervals_welldef.simps(10) to_mltl.simps(10) nnf_intervals_welldef) 
    have composition: "is_composition_MLTL (Release_mltl_ext \<alpha> a b L \<beta>)"
      using Suc.prems(3) Release_mltl_ext
      by (metis Suc.prems(1) is_composition_convert_nnf_ext) 
    then have composition_L: "is_composition (b-a+1) L" 
          and composition_\<alpha>: "is_composition_MLTL \<alpha>" 
          and composition_\<beta>: "is_composition_MLTL \<beta>"
      unfolding is_composition_MLTL.simps by simp_all 
    have length_L: "length L > 0"
      using composition_length_lb composition_L by auto
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b composition_L] by blast
    let ?front = "set [Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]"
    let ?middle = "set (Mighty_Release_mltl_list ?D \<beta> (?s ! 0) (?s ! 1 - 1)
                [?s ! 1 - ?s ! 0])"
    let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext
                              (?s ! 0)
                              (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                            (Mighty_Release_mltl_list ?D \<beta> (?s ! i)
                              (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                  [1..<length L]))"
    have split: "\<psi> \<in> ?front \<union> ?middle \<union> ?back"
      using Suc(3) unfolding Release_mltl_ext LP_mltl_aux.simps 
      using list_concat_set_union
      by (metis append.assoc) 
    {
      assume *: "\<psi> \<in> ?front"
      then have \<psi>_is: "\<psi> = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
        by auto
      have ?thesis unfolding \<psi>_is to_mltl.simps intervals_welldef.simps
        using \<alpha>_ih \<beta>_ih a_leq_b by blast
    } moreover {
      assume *: "\<psi> \<in> ?middle"
      then obtain x where \<psi>_is: "\<psi> = Mighty_Release_mltl_ext x \<beta>
             (interval_times a L ! 0) (interval_times a L ! 1 - 1)
             [interval_times a L ! 1 - interval_times a L ! 0]"
                      and x_in: "x \<in> set ?D"
        by auto
      have x_ih: "intervals_welldef (to_mltl x)"
        using Suc(1)[OF \<alpha>_ih x_in composition_\<alpha>] by blast
      have welldef: "interval_times a L ! 0 \<le> interval_times a L ! 1 - 1"
        using interval_times_diff_ge[OF a_leq_b composition_L, of 0 ?s]
        using length_L by auto
      then have ?thesis unfolding \<psi>_is to_mltl.simps Mighty_Release_mltl_ext.simps intervals_welldef.simps
        using x_ih \<alpha>_ih \<beta>_ih by blast
    } moreover {
      assume *: "\<psi> \<in> ?back"
      then obtain i x where \<psi>_is: "\<psi> = And_mltl_ext
                         (Global_mltl_ext
                           (interval_times a L ! 0)
                           (interval_times a L ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                         (Mighty_Release_mltl_ext x \<beta>
                           (interval_times a L ! i)
                           (interval_times a L ! (i + 1) - 1)
                           [interval_times a L ! (i + 1) -
                            interval_times a L ! i])"
                      and x_in: "x \<in> set ?D"
                      and i_bound: "1 \<le> i \<and> i < length L"
        by auto
      have lb: "a < ?s!i"
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of i 0 ?s]
        using sfirst i_bound by simp
      have welldef: "(interval_times a L ! i) < (interval_times a L ! (i + 1))"
        using interval_times_diff_ge[OF a_leq_b composition_L, of i ?s]
        using i_bound by simp
      have ub: "?s!(i+1) \<le> b+1"
        using slast i_bound
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" "i+1" ?s]
        by (metis Orderings.order_eq_iff less_iff_succ_less_eq order_le_imp_less_or_eq order_less_imp_le)
      have x_ih: "intervals_welldef (to_mltl x)"
        using Suc(1)
        using \<alpha>_ih composition_\<alpha> x_in by blast 
      have ?thesis unfolding \<psi>_is to_mltl.simps intervals_welldef.simps Mighty_Release_mltl_ext.simps
        using x_ih \<alpha>_ih \<beta>_ih ub lb welldef
        by (simp add: add_le_imp_le_diff sfirst) 
    }
    ultimately show ?thesis
      using Suc(3) unfolding Release_mltl_ext LP_mltl_aux.simps 
      using split by blast
    qed
qed


lemma LP_mltl_aux_wpd: 
  assumes "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes "intervals_welldef (to_mltl \<phi>)"
  assumes "\<psi> \<in> set (LP_mltl_aux \<phi> k)"
  assumes "is_composition_MLTL \<phi>"
  shows "wpd_mltl (to_mltl \<psi>) \<le> wpd_mltl (to_mltl \<phi>)"
  using assms 
proof(induct k arbitrary: \<phi> \<psi>)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case 
  proof(cases \<phi>)
    case True_mltl_ext
    then show ?thesis using Suc by auto
  next
    case False_mltl_ext
    then show ?thesis using Suc by auto
  next
    case (Prop_mltl_ext p)
    then show ?thesis using Suc by auto
  next
    case (Not_mltl_ext q)
    then have "\<exists>p. q = Prop_mltl_ext p"
      using convert_nnf_form_Not_Implies_Prop Suc
      by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
    then obtain p where "q = Prop_mltl_ext p" by blast 
    then show ?thesis 
      using Not_mltl_ext Suc.prems(3) by fastforce 
  next
    case (And_mltl_ext \<alpha> \<beta>)
    obtain x y where \<psi>_is: "\<psi> = And_mltl_ext x y" 
               and x_in: "x \<in> set (LP_mltl_aux \<alpha> k)"
               and y_in: "y \<in> set (LP_mltl_aux \<beta> k)"
      using Suc unfolding And_mltl_ext LP_mltl_aux.simps
      by (metis And_mltl_list_member convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext in_set_member mltl_ext.inject(3)) 
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding And_mltl_ext
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding And_mltl_ext
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3)) 
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(3) unfolding And_mltl_ext by simp_all
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and 
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(5) unfolding And_mltl_ext is_composition_MLTL.simps by simp_all
    have x_ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
      using Suc.hyps[of \<alpha> x, OF \<alpha>_nnf \<alpha>_welldef x_in \<alpha>_composition] by blast
    have y_ih: "wpd_mltl (to_mltl y) \<le> wpd_mltl (to_mltl \<beta>)"
      using Suc.hyps[of \<beta> y, OF \<beta>_nnf \<beta>_welldef y_in \<beta>_composition] by blast      
    show ?thesis 
      unfolding And_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps 
      using x_ih y_ih by linarith
  next
    case (Or_mltl_ext \<alpha> \<beta>)
    let ?Dx = "LP_mltl_aux \<alpha> k"
    let ?Dy = "LP_mltl_aux \<beta> k"
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(3) unfolding Or_mltl_ext by simp_all
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and 
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(5) unfolding Or_mltl_ext is_composition_MLTL.simps by simp_all
    {
      assume *: "\<psi> \<in> set (And_mltl_list ?Dx ?Dy)"
      then obtain x y where \<psi>_is: "\<psi> = And_mltl_ext x y" 
               and x_in: "x \<in> set ?Dx" and y_in: "y \<in> set ?Dy"
        using And_mltl_list_member[of \<psi> ?Dx ?Dy]
        by (metis in_set_member) 
      have x_ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
        using Suc.hyps[of \<alpha> x, OF \<alpha>_nnf \<alpha>_welldef x_in \<alpha>_composition] by blast
      have y_ih: "wpd_mltl (to_mltl y) \<le> wpd_mltl (to_mltl \<beta>)"
        using Suc.hyps[of \<beta> y, OF \<beta>_nnf \<beta>_welldef y_in \<beta>_composition] by blast      
      have ?thesis 
        unfolding Or_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps 
        using x_ih y_ih by linarith
    } moreover {
      assume *: "\<psi> \<in> set (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy)"
      then obtain y where \<psi>_is: "\<psi> = And_mltl_ext (Not\<^sub>c \<alpha>) y" 
                      and y_in: "y \<in> set ?Dy" 
        using And_mltl_list_member[of \<psi> "[Not\<^sub>c \<alpha>]" ?Dy]
        by auto
      have y_ih: "wpd_mltl (to_mltl y) \<le> wpd_mltl (to_mltl \<beta>)"
        using Suc.hyps[of \<beta> y, OF \<beta>_nnf \<beta>_welldef y_in \<beta>_composition] by blast      
      have ?thesis
        unfolding Or_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps 
        using y_ih by auto
    } moreover {
      assume *: "\<psi> \<in> set (And_mltl_list ?Dx [Not\<^sub>c \<beta>])"
      then obtain x where \<psi>_is: "\<psi> = And_mltl_ext x (Not\<^sub>c \<beta>)" 
                      and x_in: "x \<in> set ?Dx" 
        using And_mltl_list_member[of \<psi> ?Dx "[Not\<^sub>c \<beta>]"]
        by (metis in_set_member member_rec(1) member_rec(2))
      have x_ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
        using Suc.hyps[of \<alpha> x, OF \<alpha>_nnf \<alpha>_welldef x_in \<alpha>_composition] by blast     
      have ?thesis
        unfolding Or_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps 
        using x_ih by auto
    }
    ultimately show ?thesis 
      using Suc unfolding Or_mltl_ext LP_mltl_aux.simps 
      using list_concat_set_union
      by (metis UnE \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext) 
  next
    case (Future_mltl_ext a b L \<alpha>)
    let ?D = "LP_mltl_aux \<alpha> k"
    let ?s = "interval_times a L"
    let ?front = "(Future_mltl_list ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
    let ?back = "(concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext (?s ! 0)
                              (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i]))
                  [1..<length L]))"
    have a_leq_b: "a \<le> b" using Suc(3) 
      unfolding Future_mltl_ext to_mltl.simps intervals_welldef.simps
      by blast
    have composition_L: "is_composition (b-a+1) L" and
         composition_\<alpha>: "is_composition_MLTL \<alpha>" using Suc(5)
      unfolding Future_mltl_ext is_composition_MLTL.simps by simp_all 
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Future_mltl_ext 
      by (metis convert_nnf_ext.simps(6) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(5)) 
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(3) unfolding Future_mltl_ext by simp
    have nnf: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have slast: "interval_times a L ! (length L) = b+1"
        using interval_times_last[OF a_leq_b composition_L] by blast
    then have split: "\<psi> \<in> (set ?front) \<union> (set ?back)"
      using Suc(4) unfolding Future_mltl_ext LP_mltl_aux.simps nnf
      using list_concat_set_union[of ?front ?back] by metis      
    {
      assume *: "\<psi> \<in> set ?front"
      then obtain x where \<psi>_is: "\<psi> = Future_mltl_ext (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] x"
                    and x_in: "x \<in> set ?D"
        unfolding Future_mltl_list.simps by fastforce
      have length_s: "1 < length ?s" using \<psi>_is
        by (metis One_nat_def add.commute add_gr_0 add_less_cancel_right composition_L composition_length_lb interval_times_length plus_1_eq_Suc zero_less_one) 
      then have length_L: "1 \<le> length L"
        unfolding interval_times_def
        by (simp add: less_eq_iff_succ_less) 
      have "interval_times a L ! 1 \<le> interval_times a L ! (length L)"
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" 1 ?s]
        using length_L by force
      then have bound: "interval_times a L ! 1 - 1 \<le> b"
        using slast by auto
      have ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
        using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef x_in composition_\<alpha>] by blast
      have ?thesis 
        unfolding \<psi>_is Future_mltl_ext to_mltl.simps wpd_mltl.simps
        using bound ih by simp
    } moreover {
      assume *: "\<psi> \<in> set ?back"
      then obtain i where \<psi>_is: "\<psi> \<in> set ((And_mltl_list
                            [Global_mltl_ext (?s ! 0)
                              (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i])
                  ))"
        and i_in: "i \<in> {1..<length L}"
        by force
      then obtain x where \<psi>_is: "\<psi> = ((And_mltl_ext
                            (Global_mltl_ext (?s ! 0)
                              (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>))
                            (Future_mltl_ext (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i] x)))"
        and x_in: "x \<in> set ?D"
        by auto
      have ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
        using Suc.hyps(1)[OF \<alpha>_nnf \<alpha>_welldef x_in composition_\<alpha>] by blast
      have bound: "interval_times a L ! i < interval_times a L ! (i + 1)"
        using interval_times_diff_ge[OF a_leq_b composition_L, of i ?s] 
        using i_in by simp
      have "(interval_times a L ! (i + 1) - 1) \<le> b" using slast 
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" "i+1" ?s] i_in
        by (metis Suc_eq_plus1 atLeastLessThan_iff le_Suc_eq le_diff_conv linorder_not_less order_less_imp_le verit_comp_simplify1(2)) 
      then have ?thesis 
        unfolding \<psi>_is Future_mltl_ext to_mltl.simps wpd_mltl.simps
        using ih bound by linarith
    }
    ultimately show ?thesis using split by blast
  next
    case (Global_mltl_ext a b L \<alpha>)
    let ?D_\<alpha> = "LP_mltl_aux \<alpha> k"
    have a_leq_b: "a \<le> b" and \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(3) 
      unfolding Global_mltl_ext to_mltl.simps intervals_welldef.simps
       by simp_all 
    have composition_\<alpha>: "is_composition_MLTL \<alpha>" using Suc(5)
      unfolding Global_mltl_ext is_composition_MLTL.simps by simp_all 
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Global_mltl_ext 
      by (metis convert_nnf_ext.simps(7) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(6)) 
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(3) unfolding Global_mltl_ext by simp
    have nnf: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    {
      assume *: "length ?D_\<alpha> \<le> 1"
      then have \<psi>_is: "\<psi> = Global_mltl_ext a b L \<alpha>"
        using Suc unfolding Global_mltl_ext LP_mltl_aux.simps
        using nnf by fastforce 
      have ?thesis unfolding \<psi>_is Global_mltl_ext by simp
    } moreover {
      assume *: "length ?D_\<alpha> > 1"
      then have \<psi>_in: "\<psi> \<in> set (Global_mltl_decomp ?D_\<alpha> a (b - a) L)"
        using Suc nnf unfolding Global_mltl_ext LP_mltl_aux.simps
        by simp
      then obtain X where \<psi>_is: "\<psi> = Ands_mltl_ext X" 
                    and X_fact: "\<forall>i<length X. \<exists>y\<in>set (LP_mltl_aux \<alpha> k). 
                                 X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
                    and length_X: "length X = Suc (b - a)"
        using in_Global_mltl_decomp_exact_forward[OF * \<psi>_in] nnf a_leq_b
        unfolding List.member_def by blast
      have X_ih: "wpd_mltl (to_mltl (X!i)) \<le> b+wpd_mltl (to_mltl \<alpha>)"
        if i_bound: "i < length X" for i
      proof- 
        obtain x where x_in: "x \<in> set ?D_\<alpha>" 
                     and Xi_is: "X!i = Global_mltl_ext (a+i) (a+i) [1] x"
          using X_fact a_leq_b i_bound by blast
        have "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
          using Suc.hyps[OF \<alpha>_nnf \<alpha>_welldef x_in composition_\<alpha>] by simp  
        then show ?thesis unfolding Xi_is to_mltl.simps wpd_mltl.simps
          using a_leq_b length_X i_bound by auto
      qed
      have ?thesis 
        unfolding \<psi>_is Global_mltl_ext to_mltl.simps wpd_mltl.simps
        using X_ih length_X X_fact Suc(1)
      proof(induct "b-a" arbitrary:X a b)
        case 0
        then have "length X = 1"
          by simp
        then obtain x where X_is: "X = [x]"
          by (metis One_nat_def Suc_length_conv length_0_conv)
        show ?case using 0(2)[of 0] unfolding X_is 
          using Ands_mltl_ext.simps(2)
          by (metis X_is \<open>length X = 1\<close> length_0_conv less_one nth_Cons' self_append_conv2) 
      next
        case (Suc n)
        then have length_X: "length X = n + 2" by linarith
        then obtain H t where X_is: "X = H@[t]" and length_H: "length H = length X-1"
          by (metis Suc.prems(2) diff_Suc_1 length_Suc_conv_rev) 
        have Ands: "Ands_mltl_ext X = And_mltl_ext (Ands_mltl_ext H) t"
          unfolding X_is Ands_mltl_ext.simps using length_H length_X by simp
        have t_bound: "(wpd_mltl (to_mltl t)) \<le> b + wpd_mltl (to_mltl \<alpha>)"
          using Suc(3)[of "length X-1"] unfolding X_is by auto
        have cond1: "n = b - 1 - a" using Suc by auto
        have cond2: "wpd_mltl (to_mltl (H ! i))
                    \<le> b + wpd_mltl (to_mltl \<alpha>)-1"
          if i_bound: "i < length H" for i
        proof-
          have Hi_is: "H!i = X!i" using X_is i_bound
            by (simp add: nth_append) 
          have "\<exists>y\<in>set (LP_mltl_aux \<alpha> k). X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
            using Suc(3)[of i] Suc(5) i_bound
            by (metis Suc.prems(2) add_diff_cancel_left' length_H less_Suc_eq plus_1_eq_Suc) 
          then obtain y where Xi_is: "X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
                          and y_in: "y \<in> set (LP_mltl_aux \<alpha> k)"
            by auto
          have ih: "wpd_mltl (to_mltl (X ! i)) \<le> b + wpd_mltl (to_mltl \<alpha>)"
            using i_bound Suc(3)[of i] X_is by auto
          have bound: "a+i < b"
            using i_bound length_H length_X
            by (simp add: Suc.prems(2)) 
          have "wpd_mltl (to_mltl y) \<le> wpd_mltl (to_mltl \<alpha>)"
            using Suc(6)[OF \<alpha>_nnf \<alpha>_welldef y_in composition_\<alpha>] by blast
          then show ?thesis unfolding Hi_is Xi_is to_mltl.simps wpd_mltl.simps
            using bound by simp
        qed
        have cond3: "length H = Suc (b - 1 - a)"
          using length_H length_X Suc.hyps(2) by simp
        have cond4: "\<exists>y\<in>set (LP_mltl_aux \<alpha> k). H ! i = Global_mltl_ext (a + i) (a + i) [1] y"
          if i_bound: "i<length H" for i
        proof-
          have "\<exists>y\<in>set (LP_mltl_aux \<alpha> k). X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
            using Suc(5) i_bound length_H by auto
          then obtain y where y_in: "y\<in>set (LP_mltl_aux \<alpha> k)" and 
                              Xi_is: "X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
            by blast
          then have Hi_is: "H!i = X!i" using i_bound length_H
            by (metis X_is nth_append) 
          then show ?thesis unfolding Xi_is using y_in by blast
        qed
        have ih: "wpd_mltl (to_mltl (Ands_mltl_ext H))
    \<le> b - 1 + wpd_mltl (to_mltl \<alpha>)"
          using Suc.hyps(1)[of "b-1" a H, OF cond1 _ cond3] cond2 cond4 Suc.prems(4)
          by force
        show ?case unfolding Ands wpd_mltl.simps to_mltl.simps
          using t_bound ih by simp
      qed
    }
    ultimately show ?thesis by linarith
  next
    case (Until_mltl_ext \<alpha> a b L \<beta>)
    let ?D_\<alpha> = "LP_mltl_aux \<alpha> k"
    let ?D_\<beta> = "LP_mltl_aux \<beta> k"
    let ?s = "interval_times a L"
    have a_leq_b: "a \<le> b" and \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
                          and \<beta>_weldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(3) 
      unfolding Until_mltl_ext to_mltl.simps intervals_welldef.simps
       by simp_all 
    have composition_\<alpha>: "is_composition_MLTL \<alpha>" and 
         composition_\<beta>: "is_composition_MLTL \<beta>" and 
         composition_L: "is_composition (b-a+1) L" using Suc(5)
      unfolding Until_mltl_ext is_composition_MLTL.simps by simp_all 
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Until_mltl_ext 
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Until_mltl_ext 
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(3) unfolding Until_mltl_ext by simp_all
    have convert_\<alpha>: "convert_nnf_ext \<alpha> = \<alpha>"
      by (metis \<alpha>_nnf convert_nnf_ext_convert_nnf_ext)
    have convert_\<beta>: "convert_nnf_ext \<beta> = \<beta>"
      by (metis Suc.prems(1) Until_mltl_ext convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have slast: "interval_times a L ! (length L) = b+1"
        using interval_times_last[OF a_leq_b composition_L] by blast
    let ?front = "(Until_mltl_list \<alpha> ?D_\<beta> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
    let ?back = "(concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext
                              (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))]
                            (Until_mltl_list \<alpha> ?D_\<beta> (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i])) [1..<length L]))" 
    have split: "\<psi> \<in> (set ?front) \<union> (set ?back)"
      using Suc(4) unfolding Until_mltl_ext LP_mltl_aux.simps
      using convert_\<alpha> convert_\<beta> list_concat_set_union by metis
    {
      assume *: "\<psi> \<in> set ?front"
      then obtain y where \<psi>_is: "\<psi> = Until_mltl_ext \<alpha> (interval_times a L ! 0) 
                      (interval_times a L ! 1 - 1) [interval_times a L ! 1 - interval_times a L ! 0] y"
                      and y_in: "y \<in> set ?D_\<beta>"   
        by auto
      have length_s: "1 < length ?s" using \<psi>_is
        by (metis One_nat_def add.commute add_gr_0 add_less_cancel_right composition_L composition_length_lb interval_times_length plus_1_eq_Suc zero_less_one) 
      then have length_L: "1 \<le> length L"
        unfolding interval_times_def
        by (simp add: less_eq_iff_succ_less) 
      have "interval_times a L ! 1 \<le> interval_times a L ! (length L)"
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" 1 ?s]
        using length_L by force
      then have bound: "interval_times a L ! 1 - 1 \<le> b"
        using slast by auto
      have \<beta>_ih: "wpd_mltl (to_mltl y) \<le> wpd_mltl (to_mltl \<beta>)"
        using Suc.hyps(1)[OF \<beta>_nnf \<beta>_welldef y_in composition_\<beta>] by blast
      have ?thesis 
        unfolding \<psi>_is Until_mltl_ext to_mltl.simps wpd_mltl.simps
        using \<beta>_ih bound by linarith
    } moreover {
      assume *: "\<psi> \<in> set ?back"
      then obtain i y where 
      \<psi>_is: "\<psi> = And_mltl_ext (Global_mltl_ext (?s!0) (?s!i-1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
             (Until_mltl_ext \<alpha> (?s!i) (?s!(i+1)-1) [(?s!(i+1)) - (?s!i)] y)"
      and i_bound: "1 \<le> i \<and> i < length L" 
      and y_in: "y \<in> set ?D_\<beta>"
        by auto
      have bound1: "interval_times a L ! i < interval_times a L ! (i+1)"
        using interval_times_diff_ge[OF a_leq_b composition_L, of i ?s] 
        using i_bound by blast
      have "interval_times a L ! (i + 1) \<le> interval_times a L ! (length L)"
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" "i+1" ?s]
        using i_bound by (metis less_iff_succ_less_eq order_le_less) 
      then have bound2: "interval_times a L ! (i+1) \<le> b+1"
        using slast by simp
      have \<beta>_ih: "wpd_mltl (to_mltl y) \<le> wpd_mltl (to_mltl \<beta>)"
        using Suc.hyps(1)[OF \<beta>_nnf \<beta>_welldef y_in composition_\<beta>] by blast
      have "interval_times a L ! i > interval_times a L ! 0"
        using i_bound interval_times_diff_ge_general[OF a_leq_b composition_L, of i 0 ?s]
        by auto
      then have "interval_times a L ! i > 0"
        unfolding interval_times_def by simp
      then have "b > interval_times a L ! i - 1"
        using bound1 bound2 by simp
      then have case1: "(interval_times a L ! i - 1 +
         max (wpd_mltl (to_mltl \<alpha>))
          (wpd_mltl (to_mltl \<beta>))) \<le> 
            b + max (wpd_mltl (to_mltl \<alpha>))
            (wpd_mltl (to_mltl \<beta>))"
        using bound1 bound2 \<beta>_ih by linarith
      have case2: "(interval_times a L ! (i + 1) - 1 +
      max (wpd_mltl (to_mltl \<alpha>))
       (wpd_mltl (to_mltl y))) \<le> 
            b + max (wpd_mltl (to_mltl \<alpha>))
            (wpd_mltl (to_mltl \<beta>))"
        using bound1 bound2 \<beta>_ih by linarith
      have ?thesis
        unfolding Until_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps
        using case1 case2 
        by presburger
    }
    ultimately show ?thesis using split by blast
  next
    case (Release_mltl_ext \<alpha> a b L \<beta>)
    let ?D = "LP_mltl_aux \<alpha> k"
    let ?s = "interval_times a L"
    have a_leq_b: "a \<le> b" and \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
                          and \<beta>_weldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(3) 
      unfolding Release_mltl_ext to_mltl.simps intervals_welldef.simps
       by simp_all 
    have composition_\<alpha>: "is_composition_MLTL \<alpha>" and 
         composition_\<beta>: "is_composition_MLTL \<beta>" and 
         composition_L: "is_composition (b-a+1) L" using Suc(5)
      unfolding Release_mltl_ext is_composition_MLTL.simps by simp_all 
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Release_mltl_ext 
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Release_mltl_ext 
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8))
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<alpha>)"
      using Suc(3) unfolding Release_mltl_ext by simp_all
    have convert_\<alpha>: "convert_nnf_ext \<alpha> = \<alpha>"
      by (metis \<alpha>_nnf convert_nnf_ext_convert_nnf_ext)
    have convert_\<beta>: "convert_nnf_ext \<beta> = \<beta>" 
      by (metis Suc.prems(1) Release_mltl_ext convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8))
    have slast: "interval_times a L ! (length L) = b+1"
      using interval_times_last[OF a_leq_b composition_L] by blast
    have sfirst: "?s!0 = a"
      using interval_times_first by blast
    have length_L: "length L > 0"
      using composition_length_lb composition_L by simp
    let ?front = "set [Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]"
    let ?middle = "set (Mighty_Release_mltl_list ?D \<beta> (?s ! 0) (?s ! 1 - 1)
                [?s ! 1 - ?s ! 0])"
    let ?back = "set (concat
                (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext
                              (?s ! 0)
                              (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                            (Mighty_Release_mltl_list ?D \<beta> (?s ! i)
                              (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                  [1..<length L]))"
    have split: "\<psi> \<in> ?front \<union> ?middle \<union> ?back"
      using Suc(4) unfolding Release_mltl_ext LP_mltl_aux.simps
      using list_concat_set_union
      by (metis append.assoc convert_\<alpha>) 
    {
      assume *: "\<psi> \<in> ?front"
      then have \<psi>_is: "\<psi> = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
        by simp
      have ?thesis unfolding Release_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps
        by linarith
    } moreover {
      assume *: "\<psi> \<in> ?middle"
      then obtain x where \<psi>_is: "\<psi> = Mighty_Release_mltl_ext x \<beta> (interval_times a L ! 0)
             (interval_times a L ! 1 - 1)
             [interval_times a L ! 1 - interval_times a L ! 0]"
                    and x_in: "x \<in> set ?D"
        by auto
      have ub: "interval_times a L ! 1 - 1 \<le> b"
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" 1 ?s]
        using slast length_L
        by (metis diff_add_inverse2 diff_le_self dual_order.strict_iff_order dual_order.trans less_eq_iff_succ_less zero_less_diff) 
      have x_ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
        using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef x_in composition_\<alpha>]
        by blast                                                                                       
      then have ?thesis unfolding \<psi>_is Release_mltl_ext to_mltl.simps wpd_mltl.simps Mighty_Release_mltl_ext.simps
        using ub by auto
    } moreover {
      assume *: "\<psi> \<in> ?back"
      then obtain x i where \<psi>_is: "\<psi> = And_mltl_ext
                         (Global_mltl_ext
                           (interval_times a L ! 0)
                           (interval_times a L ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                         (Mighty_Release_mltl_ext x \<beta>
                           (interval_times a L ! i)
                           (interval_times a L ! (i + 1) - 1)
                           [interval_times a L ! (i + 1) -
                            interval_times a L ! i])"
                      and x_in: "x \<in> set ?D"
                      and i_bound: "1 \<le> i \<and> i < length L"
        by auto
      have x_ih: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<alpha>)"
        using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef x_in composition_\<alpha>] by blast
      have lb: "a < ?s!i"
        using interval_times_diff_ge_general sfirst
        by (smt (verit, ccfv_SIG) a_leq_b composition_L i_bound less_or_eq_imp_le order_less_le_trans zero_less_one) 
      have welldef: "?s!i < ?s!(i+1)"
        using interval_times_diff_ge[OF a_leq_b composition_L]
        using i_bound length_L by blast
      have ub: "?s!(i+1) \<le> b+1"
        using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" "i+1" ?s]
        using i_bound slast
        by (metis less_iff_succ_less_eq order_le_imp_less_or_eq order_less_imp_le order_refl) 
      have ?thesis unfolding Release_mltl_ext \<psi>_is to_mltl.simps wpd_mltl.simps Mighty_Release_mltl_ext.simps
        using lb welldef ub x_ih by auto
    }
    ultimately show ?thesis
      using split by blast
  qed
qed

lemma And_mltl_list_nonempty: 
  assumes "A \<noteq> []" and "B \<noteq> []"
  shows "And_mltl_list A B \<noteq> []"
proof-
  have "length A > 0"
    using assms by blast
  then obtain ha Ta where A: "A = ha#Ta"
    using list.exhaust by auto
  have "length B > 0"
    using assms by blast
  then obtain hb Tb where B: "B = hb#Tb"
    using list.exhaust by auto
  show ?thesis
    using assms unfolding And_mltl_list.simps A B pairs.simps 
    by blast
qed

lemma Global_mltl_decomp_nonempty: 
  assumes "D \<noteq> []"
  shows "Global_mltl_decomp D a n L \<noteq> []"
  using assms
proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case unfolding Global_mltl_decomp.simps Global_mltl_list.simps
    using And_mltl_list_nonempty by auto
qed

lemma LP_mltl_aux_nonempty: 
  assumes "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes "intervals_welldef (to_mltl \<phi>)"
  assumes "is_composition_MLTL \<phi>"
  shows "LP_mltl_aux \<phi> k \<noteq> []" 
  using assms
proof(induct k arbitrary: \<phi>)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case 
  proof(cases \<phi>)
    case True_mltl_ext
    then show ?thesis by simp
  next
    case False_mltl_ext
    then show ?thesis by simp
  next
    case (Prop_mltl_ext p)
    then show ?thesis by simp
  next
    case (Not_mltl_ext q)
    then have "\<exists>p. q = Prop_mltl_ext p"
      using convert_nnf_form_Not_Implies_Prop Suc
      by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
    then obtain p where "q = Prop_mltl_ext p" by blast 
    then show ?thesis 
      unfolding Not_mltl_ext by simp
  next
    case (And_mltl_ext \<alpha> \<beta>)
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding And_mltl_ext 
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding And_mltl_ext 
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3))
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(3) unfolding And_mltl_ext by simp_all
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(4) unfolding And_mltl_ext is_composition_MLTL.simps 
      by simp_all
    have \<alpha>_ih: "LP_mltl_aux \<alpha> k \<noteq> []"
      using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef \<alpha>_composition] by simp
    have \<beta>_ih: "LP_mltl_aux \<beta> k \<noteq> []"
      using Suc(1)[OF \<beta>_nnf \<beta>_welldef \<beta>_composition] by simp
    show ?thesis
      unfolding And_mltl_ext LP_mltl_aux.simps And_mltl_list.simps 
      using pairs.simps(2) \<alpha>_ih \<beta>_ih
      by (metis (no_types, lifting) \<alpha>_nnf \<beta>_nnf append_is_Nil_conv convert_nnf_ext_convert_nnf_ext list.map_disc_iff pairs.elims) 
  next
    case (Or_mltl_ext \<alpha> \<beta>)
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Or_mltl_ext 
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Or_mltl_ext 
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4))
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(3) unfolding Or_mltl_ext by simp_all
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(4) unfolding Or_mltl_ext is_composition_MLTL.simps 
      by simp_all
    have \<alpha>_ih: "LP_mltl_aux \<alpha> k \<noteq> []"
      using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef \<alpha>_composition] by simp
    have \<beta>_ih: "LP_mltl_aux \<beta> k \<noteq> []"
      using Suc(1)[OF \<beta>_nnf \<beta>_welldef \<beta>_composition] by simp
    then show ?thesis 
      unfolding Or_mltl_ext LP_mltl_aux.simps And_mltl_list.simps
      by (metis (no_types, lifting) \<alpha>_ih \<alpha>_nnf concat.simps(1) concat_eq_append_conv convert_nnf_ext_convert_nnf_ext list.map_disc_iff not_Cons_self2 pairs.elims) 
  next
    case (Future_mltl_ext a b L \<alpha>)
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Future_mltl_ext 
      by (metis convert_nnf_ext.simps(6) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(5)) 
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
      using Suc(3) unfolding Future_mltl_ext by simp_all
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" 
      using Suc(4) unfolding Future_mltl_ext is_composition_MLTL.simps 
      by simp_all
    have \<alpha>_ih: "LP_mltl_aux \<alpha> k \<noteq> []"
      using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef \<alpha>_composition] by simp
    then show ?thesis 
      unfolding Future_mltl_ext LP_mltl_aux.simps And_mltl_list.simps
      by (metis (no_types, lifting) Future_mltl_list.elims \<alpha>_nnf append_is_Nil_conv convert_nnf_ext_convert_nnf_ext map_is_Nil_conv) 
  next
    case (Global_mltl_ext a b L \<alpha>)
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Global_mltl_ext 
      by (metis convert_nnf_ext.simps(7) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(6)) 
    then have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
      using Suc(3) unfolding Global_mltl_ext by simp_all
     have \<alpha>_composition: "is_composition_MLTL \<alpha>" 
      using Suc(4) unfolding Global_mltl_ext is_composition_MLTL.simps 
      by simp_all
    have \<alpha>_ih: "LP_mltl_aux \<alpha> k \<noteq> []"
      using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef \<alpha>_composition] by simp
    let ?D = "LP_mltl_aux \<alpha> k"
    {
      assume *: "length ?D \<le> 1"
      then have ?thesis unfolding Global_mltl_ext LP_mltl_aux.simps 
        using \<alpha>_ih \<alpha>_convert by simp
    } moreover {
      assume *: "length ?D > 1"
      have D_is: "LP_mltl_aux \<phi> (Suc k) = Global_mltl_decomp ?D a (b - a) L"
        unfolding Global_mltl_ext LP_mltl_aux.simps 
        using * \<alpha>_convert by auto
      have ?thesis unfolding D_is 
        using Global_mltl_decomp_nonempty \<alpha>_ih by blast
    }
    ultimately show ?thesis by linarith
  next
    case (Until_mltl_ext \<alpha> a b L \<beta>)
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(2) unfolding Until_mltl_ext 
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)" and
         a_leq_b: "a \<le> b"
      using Suc(3) unfolding Until_mltl_ext by simp_all
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>" and 
         L_composition: "is_composition (b-a+1) L"
      using Suc(4) unfolding Until_mltl_ext is_composition_MLTL.simps 
      by simp_all
    have \<alpha>_ih: "LP_mltl_aux \<alpha> k \<noteq> []"
      using Suc(1)[OF \<alpha>_nnf \<alpha>_welldef \<alpha>_composition] by simp
    have \<beta>_ih: "LP_mltl_aux \<beta> k \<noteq> []"
      using Suc(1)[OF \<beta>_nnf \<beta>_welldef \<beta>_composition] by simp
    show ?thesis unfolding Until_mltl_ext LP_mltl_aux.simps
      using \<alpha>_ih \<beta>_ih 
      by (metis (no_types, lifting) Until_mltl_list.elims \<beta>_nnf append_is_Nil_conv convert_nnf_ext_convert_nnf_ext map_is_Nil_conv) 
  next
    case (Release_mltl_ext \<alpha> a b L \<beta>)
    show ?thesis unfolding LP_mltl_aux.simps Release_mltl_ext
      by (meson append_is_Nil_conv not_Cons_self2) 
  qed
qed

subsection \<open>Union Theorem\<close>

paragraph \<open>Forward Direction\<close>

lemma exist_first: 
  fixes lb i::"nat"
  assumes lowerbound: "lb \<le> i" and iprop: "(P i)"
  shows "\<exists>j. (lb \<le> j \<and> j \<le> i \<and> (P j) 
         \<and> (\<forall>l. (lb \<le> l \<and> l < j) \<longrightarrow> \<not>(P l)))"
  using lowerbound iprop
proof(induct "i-lb" arbitrary: i rule: less_induct)
  case less
  {
    assume *: "\<forall>l\<ge>lb. l < i \<longrightarrow> \<not>(P l)"
    then have ?case
      using less by blast
  } moreover {
    assume *: "\<exists>i'\<ge>lb. i' < i \<and> (P i')"
    then obtain i' where "lb \<le> i' \<and> i' < i \<and> P i'"
      by blast
    then have ?case 
      using less.hyps(1)[of i'] by fastforce
  }
  ultimately show ?case by blast
qed


lemma exist_bound_split:
  fixes a m b::"nat"
  assumes "a \<le> b" 
  assumes "\<exists>i. a \<le> i \<and> i \<le> b \<and> P i"
  shows "(\<exists>i. a \<le> i \<and> i \<le> m-1 \<and> P i) \<or> 
         (\<exists>i. m \<le> i \<and> i \<le> b \<and> P i \<and> \<not>(\<exists>j. a \<le> j \<and> j < m \<and> P j))"
  using assms by fastforce

lemma Global_mltl_ext_obtain: 
  fixes D::"'a mltl_ext list" and \<pi>::"'a set list" 
   and \<alpha>::"'a mltl_ext" and a b k::"nat"
  assumes a_leq_b: "a \<le> b" 
  assumes length_\<pi>: "length \<pi> \<ge> b + wpd_mltl (to_mltl \<alpha>)"
  assumes semantics: "semantics_mltl_ext \<pi> (Global_mltl_ext a b L \<alpha>)"
  assumes ih: "\<And>trace. semantics_mltl_ext trace \<alpha> \<Longrightarrow>
                wpd_mltl (to_mltl \<alpha>) \<le> length trace \<Longrightarrow>
                \<exists>x\<in>set D. semantics_mltl_ext trace x"
  shows "\<exists>X. (length X = b-a+1) \<and> 
        (\<forall>i<length X. (X!i \<in> set D) \<and> semantics_mltl_ext (drop (a+i) \<pi>) (X!i))"
proof-
  have semantics: "\<And>i. a \<le> i \<and> i \<le> b \<Longrightarrow> semantics_mltl_ext (drop i \<pi>) \<alpha>" 
    using semantics length_\<pi> a_leq_b
    unfolding semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
    by (metis add_diff_cancel_left' wpd_geq_one diff_add_zero le_less_Suc_eq le_trans less_add_Suc1 not_one_le_zero)
  have ih: "\<exists>x\<in>set D. semantics_mltl_ext (drop i \<pi>) x"
    if i_bound: "a \<le> i \<and> i \<le> b" for i
  proof-
    have cond1: "semantics_mltl_ext (drop i \<pi>) \<alpha>"
      using semantics[of i] i_bound by blast
    have cond2: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop i \<pi>)"
      using length_\<pi> a_leq_b i_bound by auto
    show ?thesis
      using ih[OF cond1 cond2] by blast
  qed
  show ?thesis using ih a_leq_b
  proof(induct "b-a" arbitrary: a b)
    case 0
    then have aeqb: "a = b" by simp
    then obtain x where semantics_x: "semantics_mltl_ext (drop a \<pi>) x"
                  and x_in: "x \<in> set D"
      using 0(2)[of a] by blast 
    let ?X = "[x]"
    have length_X: "length ?X = b - a + 1" using aeqb by simp 
    have "?X ! i \<in> set D \<and> semantics_mltl_ext (drop (a+i) \<pi>) (?X ! i)"
      if i_bound: "i<length ?X" for i
      using semantics_x that x_in by force 
    then show ?case using length_X by blast
  next
    case (Suc n)
    then have n_eq: "n = b - 1 - a" by simp
    have "\<exists>X. length X = b - 1 - a + 1 \<and>
      (\<forall>i<length X.
          X ! i \<in> set D \<and> semantics_mltl_ext (drop (a + i) \<pi>) (X ! i))"
      using Suc(1)[OF n_eq] unfolding Bex_def
      using Suc.hyps(2) Suc.prems(1) diff_diff_left diff_le_self plus_1_eq_Suc by fastforce 
    then obtain X where length_X: "length X = b-a" and
      X_prop: "\<forall>i<length X. X ! i \<in> set D \<and> semantics_mltl_ext (drop (a + i) \<pi>) (X ! i)"
      by (metis Suc.hyps(2) Suc_eq_plus1 n_eq)
    obtain x where x_in: "x \<in> set D" 
    and semantics_x: "semantics_mltl_ext (drop b \<pi>) x"
      using Suc(3)[of b] unfolding Bex_def using Suc(4) by blast
    let ?L = "X@[x]"
    have length_L: "length ?L = b - a + 1"
      using length_X by simp
    have "?L ! i \<in> set D \<and> semantics_mltl_ext (drop (a + i) \<pi>) (?L ! i)"
      if i_bound: "i < length ?L" for i
    proof-
      {
        assume *: "i < b-a"
        have ?thesis
          using X_prop length_X
          by (metis "*" nth_append) 
      } moreover {
        assume *: "i = b-a"
        then have x_is: "(X @ [x]) ! i = x"
          using length_L by (metis length_X nth_append_length) 
        have ?thesis unfolding x_is 
          using x_in Suc semantics_x unfolding * by simp
      }
      ultimately show ?thesis using i_bound length_L by fastforce
    qed
    then show ?case using length_L by blast
  qed
qed


lemma Release_semantics_split: 
  assumes "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) \<or>
    (\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
            (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                 semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
  shows "((\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) 
          \<and>(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (Not\<^sub>m (to_mltl \<alpha>))))
        \<or> (\<exists>j\<ge>a. j \<le> b \<and>
             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
proof-
  {assume *: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) \<and>
          \<not>(\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
            (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                 semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
    then have semantics: "\<forall>j. a \<le> j \<and> j \<le> b-1 \<longrightarrow> \<not>semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<or>
           \<not>(\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                 semantics_mltl (drop k \<pi>) (to_mltl \<beta>))"
      by blast
    then have "\<not>semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)" 
      if j_bound: "a \<le> j \<and> j \<le> b-1" for j
    proof-
      have "semantics_mltl (drop k \<pi>) (to_mltl \<beta>)"
        if k_bound: " a \<le> k \<and> k \<le> j" for k
        using k_bound j_bound * by auto
      then show ?thesis using semantics j_bound by blast
    qed
    then have ?thesis using *
      by (metis dual_order.trans semantics_mltl.simps(4)) 
  } moreover { 
    assume "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) \<and>
          (\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
            (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                 semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
    then have ?thesis
      by (meson diff_le_self le_trans) 
  } moreover {
    assume "(\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
            (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                 semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
    then have ?thesis
      by (meson diff_le_self le_trans) 
  } 
  ultimately show ?thesis using assms
    by blast 
qed


theorem LP_mltl_aux_language_union_forward:
   fixes \<phi>::"'a mltl_ext" and k::"nat" and \<pi>::"'a set list"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes D_is: "D = LP_mltl_aux \<phi> k"
  assumes semantics: "semantics_mltl_ext \<pi> \<phi>"
  assumes trace_length: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
  shows "\<exists>\<psi> \<in> set D. semantics_mltl_ext \<pi> \<psi>"
  using assms
proof(induct k arbitrary: \<phi> D \<pi>)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case 
  proof(cases \<phi>)
    case True_mltl_ext
    then show ?thesis using Suc by simp
  next
    case False_mltl_ext
    then show ?thesis using Suc by simp
  next
    case (Prop_mltl_ext x3)
    then show ?thesis using Suc by simp
  next
    case (Not_mltl_ext x4)
    then have "\<exists>p. x4 = Prop_mltl_ext p"
      using convert_nnf_form_Not_Implies_Prop Suc(3)
      by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
    then show ?thesis using Suc
      by (metis LP_mltl_aux.simps(5) ListMem_iff Not_mltl_ext elem) 
  next
    case (And_mltl_ext \<alpha> \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) unfolding And_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding And_mltl_ext
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3))
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      by (metis And_mltl_ext Suc.prems(2) convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3)) 
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and 
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(4) unfolding And_mltl_ext is_composition_MLTL.simps 
      by simp_all
    have \<alpha>_semantics: "semantics_mltl_ext \<pi> \<alpha>" and 
         \<beta>_semantics: "semantics_mltl_ext \<pi> \<beta>"
      using Suc(6) unfolding And_mltl_ext semantics_mltl_ext_def 
       by simp_all
    have \<alpha>_wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>" and
         \<beta>_wpd: "wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using Suc(7) unfolding And_mltl_ext to_mltl.simps wpd_mltl.simps 
      by simp_all
    have \<alpha>_ih: "\<exists>xa\<in>set (LP_mltl_aux \<alpha> k). semantics_mltl_ext \<pi> xa"
      using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition _ \<alpha>_semantics \<alpha>_wpd] by blast
    have \<beta>_ih: "\<exists>xb\<in>set (LP_mltl_aux \<beta> k). semantics_mltl_ext \<pi> xb"
      using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition _ \<beta>_semantics \<beta>_wpd] by blast
    then obtain xa where xa_in: "xa \<in> set (LP_mltl_aux \<alpha> k)" and xa_semantics: "semantics_mltl_ext \<pi> xa"
      using \<alpha>_ih by blast
    then obtain xb where xb_in: "xb \<in> set (LP_mltl_aux \<beta> k)" and xb_semantics: "semantics_mltl_ext \<pi> xb"
      using \<beta>_ih by blast
    have xab_in: "And_mltl_ext xa xb \<in> set D"
      unfolding Suc(5) And_mltl_ext LP_mltl_aux.simps 
      using xa_in xb_in And_mltl_list_member
      by (metis \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext in_set_member) 
    have xab_semantics: "semantics_mltl_ext \<pi> (And_mltl_ext xa xb)"
      using xa_semantics xb_semantics unfolding semantics_mltl_ext_def 
      by simp
    show ?thesis using xab_in xab_semantics by blast
  next
    case (Or_mltl_ext \<alpha> \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) unfolding Or_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      by (metis Or_mltl_ext Suc.prems(2) convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and 
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(4) unfolding Or_mltl_ext is_composition_MLTL.simps 
       by simp_all
    have \<alpha>_wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>" and
         \<beta>_wpd: "wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using Suc(7) unfolding Or_mltl_ext to_mltl.simps wpd_mltl.simps 
      by simp_all
    have \<alpha>\<beta>_semantics: "semantics_mltl_ext \<pi> \<alpha> \<or> semantics_mltl_ext \<pi> \<beta>"
      using Suc(6) unfolding Or_mltl_ext semantics_mltl_ext_def 
      by simp
    let ?D_\<alpha> = "LP_mltl_aux \<alpha> k" and ?D_\<beta> = "LP_mltl_aux \<beta> k"
    {
      assume *: "semantics_mltl_ext \<pi> \<alpha> \<and> \<not>semantics_mltl_ext \<pi> \<beta>"
      have \<alpha>_ih: "\<exists>xa\<in>set (LP_mltl_aux \<alpha> k). semantics_mltl_ext \<pi> xa" 
        using * Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition _ _ \<alpha>_wpd] by blast
      then obtain xa where xa_in: "xa \<in> set ?D_\<alpha>" and xa_semantics: "semantics_mltl_ext \<pi> xa"
        using \<alpha>_ih by blast  
      let ?\<psi> = "And_mltl_ext xa (Not\<^sub>c \<beta>)"
      have xa\<beta>_in: "?\<psi> \<in> set (And_mltl_list ?D_\<alpha> [Not\<^sub>c \<beta>])"
        using xa_in And_mltl_list_member unfolding List.member_def
        by (metis list.set_intros(1)) 
      then have xa\<beta>_in: "?\<psi> \<in> set D"
        unfolding Suc(5) Or_mltl_ext LP_mltl_aux.simps 
        using list_concat_set_union
        [of "And_mltl_list ?D_\<alpha> ?D_\<beta> @ And_mltl_list [Not\<^sub>c \<alpha>] ?D_\<beta>" 
            "And_mltl_list (LP_mltl_aux \<alpha> k) [Not\<^sub>c \<beta>]"]
        by (metis UnCI \<alpha>_nnf \<beta>_nnf append_assoc convert_nnf_ext_convert_nnf_ext) 
      have xa\<beta>_semantics: "semantics_mltl_ext \<pi> ?\<psi>" using * xa_semantics
        unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps 
        by simp
      have ?thesis using xa\<beta>_in xa\<beta>_semantics by blast
    } moreover {
      assume *: "\<not>semantics_mltl_ext \<pi> \<alpha> \<and> semantics_mltl_ext \<pi> \<beta>"
      have \<beta>_ih: "\<exists>xb\<in>set (LP_mltl_aux \<beta> k). semantics_mltl_ext \<pi> xb" 
        using * Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition _ _ \<beta>_wpd] by blast
      then obtain xb where xa_in: "xb \<in> set ?D_\<beta>" and xa_semantics: "semantics_mltl_ext \<pi> xb"
        using \<beta>_ih by blast  
      let ?\<psi> = "And_mltl_ext (Not\<^sub>c \<alpha>) xb"
      have \<alpha>xb_in: "?\<psi> \<in> set (And_mltl_list [Not\<^sub>c \<alpha>] ?D_\<beta>)"
        using xa_in And_mltl_list_member unfolding List.member_def
        by (metis list.set_intros(1)) 
      then have \<alpha>xb_in: "?\<psi> \<in> set (And_mltl_list ?D_\<alpha> ?D_\<beta> @ And_mltl_list [Not\<^sub>c \<alpha>] ?D_\<beta>)"
        using list_concat_set_union[of "And_mltl_list ?D_\<alpha> ?D_\<beta>" "And_mltl_list [Not\<^sub>c \<alpha>] ?D_\<beta>"]
        by blast
      then have \<alpha>xb_in: "?\<psi> \<in> set D"
        unfolding Suc(5) Or_mltl_ext LP_mltl_aux.simps 
        using list_concat_set_union 
        [of "And_mltl_list ?D_\<alpha> ?D_\<beta> @ And_mltl_list [Not\<^sub>c \<alpha>] ?D_\<beta>" 
            "And_mltl_list (LP_mltl_aux \<alpha> k) [Not\<^sub>c \<beta>]"]
        by (metis UnCI \<alpha>_nnf \<beta>_nnf append_assoc convert_nnf_ext_convert_nnf_ext)
      have \<alpha>xb_semantics: "semantics_mltl_ext \<pi> ?\<psi>" using * xa_semantics
        unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps 
        by simp
      have ?thesis using \<alpha>xb_in \<alpha>xb_semantics by blast
    } moreover {
      assume *: "semantics_mltl_ext \<pi> \<alpha> \<and> semantics_mltl_ext \<pi> \<beta>"
      have \<alpha>_ih: "\<exists>xa\<in>set (LP_mltl_aux \<alpha> k). semantics_mltl_ext \<pi> xa"
        using * Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition _ _ \<alpha>_wpd] by blast
      have \<beta>_ih: "\<exists>xb\<in>set (LP_mltl_aux \<beta> k). semantics_mltl_ext \<pi> xb"
      using * Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition _ _ \<beta>_wpd] by blast
      then obtain xa where xa_in: "xa \<in> set (LP_mltl_aux \<alpha> k)" and xa_semantics: "semantics_mltl_ext \<pi> xa"
        using \<alpha>_ih by blast  
      then obtain xb where xb_in: "xb \<in> set (LP_mltl_aux \<beta> k)" and xb_semantics: "semantics_mltl_ext \<pi> xb"
          using \<beta>_ih by blast
      have xab_in: "And_mltl_ext xa xb \<in> set D"
        unfolding Suc(5) Or_mltl_ext LP_mltl_aux.simps
        using xa_in xb_in And_mltl_list_member list_concat_set_union 
        unfolding List.member_def
        by (metis UnCI \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext) 
      have xab_semantics: "semantics_mltl_ext \<pi> (And_mltl_ext xa xb)"
        using xa_semantics xb_semantics unfolding semantics_mltl_ext_def 
        by simp
      have ?thesis using xab_in xab_semantics by blast
    }
    ultimately show ?thesis using \<alpha>\<beta>_semantics by blast
  next
    case (Future_mltl_ext a b L \<alpha>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(2) unfolding Future_mltl_ext by auto
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Future_mltl_ext
      by (metis convert_nnf_ext.simps(6) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(5))
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
      using Suc(4) unfolding Future_mltl_ext is_composition_MLTL.simps by blast
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
      using Suc(7) unfolding Future_mltl_ext to_mltl.simps wpd_mltl.simps 
      by simp
    have a_leq_b: "a \<le> b" and length_\<pi>_geq_b: "b < length \<pi>" and length_\<pi>_ge_a: "a < length \<pi>"
     and semantics: "\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
      using Suc(6) \<alpha>_wpd 
      unfolding Future_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
      using wpd_geq_one[of "(to_mltl \<alpha>)"]
      by simp_all
    have composition_L: "is_composition (b - a + 1) L"
      using Suc(4) unfolding Future_mltl_ext is_composition_MLTL.simps by blast
    then have s0: "(interval_times a L ! 0) = a"
      using interval_times_first by auto
    have slast: "interval_times a L ! (length L) = b+1"
      using interval_times_last[OF a_leq_b composition_L] by blast
    have length_L: "length L \<ge> 0"
      using composition_L composition_length_lb by blast
    let ?s = "interval_times a L"
    let ?D_\<alpha> = "LP_mltl_aux \<alpha> k"
    let ?decomp = "(concat(map (\<lambda>i. And_mltl_list
                             [Global_mltl_ext (?s ! 0)
                               (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                             (Future_mltl_list ?D_\<alpha> (?s ! i) (?s ! (i + 1) - 1)
                               [?s ! (i + 1) - ?s ! i]))
                   [1..<length L]))"
    {
      assume *: "\<exists>i. (a \<le> i \<and> i \<le> (?s!1-1)) \<and> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
      then obtain i where i_bounds: "a \<le> i \<and> i \<le> (?s!1-1)" and 
           semantics: "semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)" by blast
      have length_s: "length ?s \<ge> 2"
        using i_bounds
        by (metis a_leq_b add_less_same_cancel2 antisym_conv3 interval_times_first interval_times_length less_eq_iff_succ_less less_iff_succ_less_eq less_nat_zero_code one_add_one slast verit_comp_simplify1(1)) 
      have dropi_length: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop i \<pi>)"
      proof-
        have "1 \<le> length L"
          using length_s unfolding interval_times_def by simp
        then have "interval_times a L ! 1 \<le> interval_times a L ! length L"
          using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" 1 ?s]
          by fastforce
        then have "interval_times a L ! 1 - 1 \<le> b"
          using slast by auto
        then show ?thesis
          using \<alpha>_wpd i_bounds by force
      qed
      have "\<exists>x\<in>set (LP_mltl_aux \<alpha> k). semantics_mltl_ext (drop i \<pi>) x"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of ?D_\<alpha> "drop i \<pi>"] semantics
        using semantics_mltl_ext_def \<alpha>_wpd dropi_length by blast
      then obtain x where x_in: "x\<in>set (LP_mltl_aux \<alpha> k)" and 
                          x_semantics: "semantics_mltl_ext (drop i \<pi>) x"
        by blast
      let ?\<psi> = "Future_mltl_ext (?s!0) (?s!1-1) [?s!1 - ?s!0] x"
      have \<psi>_in: "?\<psi> \<in> set (Future_mltl_list ?D_\<alpha> (?s!0) (?s!1-1) [?s!1 - ?s!0])"
        unfolding Future_mltl_list.simps using x_in by simp
      then have \<psi>_in: "?\<psi> \<in> set ((Future_mltl_list ?D_\<alpha> (?s!0) (?s!1-1) [?s!1 - ?s!0]) @
                (concat
                 (map (\<lambda>i. And_mltl_list
                             [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                             (Future_mltl_list ?D_\<alpha> (?s ! i) (?s ! (i + 1) - 1)
                               [?s ! (i + 1) - ?s ! i]))
                   [1..<length L])))"
        by force
      have \<psi>_semantics: "semantics_mltl_ext \<pi> ?\<psi>"
        using x_semantics unfolding s0 semantics_mltl_ext_def 
        unfolding semantics_mltl.simps to_mltl.simps 
        using i_bounds length_\<pi>_geq_b length_\<pi>_ge_a by auto
      have ?thesis unfolding Suc(5) Future_mltl_ext LP_mltl_aux.simps 
        using \<psi>_in \<psi>_semantics
      proof -
        have "convert_nnf_ext \<alpha> = \<alpha>"
          by (metis (full_types) \<alpha>_nnf convert_nnf_ext_convert_nnf_ext)
        then have "Future_mltl_ext (interval_times a L ! 0) 
(interval_times a L ! 1 - 1) [interval_times a L ! 1 - interval_times a L ! 0] x \<in> 
set (Future_mltl_list (LP_mltl_aux (convert_nnf_ext \<alpha>) k) 
(interval_times a L ! 0) (interval_times a L ! 1 - 1) 
[interval_times a L ! 1 - interval_times a L ! 0] @
 concat (map (\<lambda>n. And_mltl_list [Global_mltl_ext
 (interval_times a L ! 0) (interval_times a L ! n - 1) [?s!n - ?s!0] (Not\<^sub>c \<alpha>)] 
(Future_mltl_list (LP_mltl_aux (convert_nnf_ext \<alpha>) k) 
(interval_times a L ! n) (interval_times a L ! (n + 1) - 1) 
[interval_times a L ! (n + 1) - interval_times a L ! n])) [1..<length L]))"
          using \<psi>_in by presburger
        then show "\<exists>m\<in>set (let ms = LP_mltl_aux (convert_nnf_ext \<alpha>) k; ns = interval_times a L in Future_mltl_list ms (ns ! 0) (ns ! 1 - 1) [ns ! 1 - ns ! 0] @ concat (map (\<lambda>n. And_mltl_list [Global_mltl_ext (ns ! 0) (ns ! n - 1) [ns!n - ns!0] (Not\<^sub>c \<alpha>)] (Future_mltl_list ms (ns ! n) (ns ! (n + 1) - 1) [ns ! (n + 1) - ns ! n])) [1..<length L])). semantics_mltl_ext \<pi> m"
          by (meson \<psi>_semantics)
      qed 
    } moreover {
      assume *: "\<exists>i. ((?s!1) \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
                 \<not>(\<exists>i. (a \<le> i \<and> i \<le> (?s!1-1)) \<and> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>))"
      obtain t' where t'_facts: "((?s!1) \<le> t' \<and> t' \<le> b) \<and> semantics_mltl (drop t' \<pi>) (to_mltl \<alpha>)"
        using * by blast
      then have "\<exists>j. (interval_times a L ! 1 \<le> j \<and> j \<le> t') \<and>
        semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
        (\<forall>l. (interval_times a L ! 1 \<le> l \<and> l < j) \<longrightarrow>
             \<not> semantics_mltl (drop l \<pi>) (to_mltl \<alpha>))"
        using exist_first[of "(?s!1)" t' "\<lambda>i. semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"]
        by simp
      then obtain t where 
           t_bounds: "(interval_times a L ! 1 \<le> t \<and> t \<le> t')" and
           t_semantics: "semantics_mltl (drop t \<pi>) (to_mltl \<alpha>)" and
           t_minimal: "(\<forall>l. (interval_times a L ! 1 \<le> l \<and> l < t) \<longrightarrow>
             \<not> semantics_mltl (drop l \<pi>) (to_mltl \<alpha>))" by auto
      have dropt_length: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop t \<pi>)"
      proof-
        have "t' \<le> b"
          using t'_facts by blast
        then show ?thesis
          using \<alpha>_wpd t_bounds by auto
      qed
      have "\<exists>i. interval_times a L ! i \<le> t \<and>
      t \<le> interval_times a L ! (i + 1) - 1 \<and> 1 \<le> i \<and> i < length L" 
        using interval_times_obtain_aux[of a b L ?s t]
        using a_leq_b composition_L t_bounds t_semantics
        using le_trans t'_facts by blast 
      then obtain i where t_bound: "interval_times a L ! i \<le> t \<and> t \<le> interval_times a L ! (i + 1) - 1"
                    and i_bound: "1 \<le> i \<and> i < length L"
        by blast
      have "\<exists>x\<in>set (LP_mltl_aux \<alpha> k). semantics_mltl_ext (drop t \<pi>) x"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of ?D_\<alpha> "drop t \<pi>"]
        using semantics_mltl_ext_def t_semantics dropt_length by blast
      then obtain x where x_in: "x\<in>set (LP_mltl_aux \<alpha> k)" and
                          x_semantics: "semantics_mltl_ext (drop t \<pi>) x"
        by blast
      let ?\<psi> = "And_mltl_ext
                 (Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>))
                 (Future_mltl_ext (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i] x)"
      have "?\<psi> \<in> set ?decomp" 
      proof-
        have "?\<psi> \<in> set (And_mltl_list
                             [Global_mltl_ext (?s ! 0)
                               (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                             (Future_mltl_list ?D_\<alpha> (?s ! i) (?s ! (i + 1) - 1)
                               [?s ! (i + 1) - ?s ! i]))"
          using x_in unfolding Future_mltl_list.simps by auto
        then have "?\<psi> \<in> set ((map (\<lambda>i. And_mltl_list
                         [Global_mltl_ext
                           (interval_times a L ! 0)
                           (interval_times a L ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                         (Future_mltl_list (LP_mltl_aux \<alpha> k)
                           (interval_times a L ! i)
                           (interval_times a L ! (i + 1) - 1)
                           [interval_times a L ! (i + 1) -
                            interval_times a L ! i]))
               [1..<length L])!(i-1))" using i_bound by auto
        then show ?thesis 
          using set_concat i_bound by fastforce
      qed
      then have \<psi>_in: "?\<psi> \<in> set (Future_mltl_list ?D_\<alpha> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] @
                concat(map (\<lambda>i. And_mltl_list
                             [Global_mltl_ext (?s ! 0)
                               (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                             (Future_mltl_list ?D_\<alpha> (?s ! i) (?s ! (i + 1) - 1)
                               [?s ! (i + 1) - ?s ! i]))
                   [1..<length L]))"
        by simp
      have \<psi>_semantics: "semantics_mltl_ext \<pi> ?\<psi>"
      proof-
        have bound: "interval_times a L ! 0 \<le> interval_times a L ! i - 1"
          using interval_times_diff_ge_general[OF a_leq_b composition_L, of _ 0] length_L i_bound
          by (simp add: add_le_imp_le_diff less_iff_succ_less_eq) 
        have not_semantics: "\<not> semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>)" 
          if ia_bound: "(interval_times a L ! 0 \<le> ia \<and> ia \<le> interval_times a L ! i - 1)" for ia
        proof-
          {
            assume ia_location: "ia \<le> interval_times a L ! 1 - 1"
            have ?thesis using * ia_bound
              using ia_location s0 by auto 
          } moreover {
            assume ia_location: "ia > interval_times a L ! 1 - 1"
            have "interval_times a L ! i - 1 < interval_times a L ! i"
              using interval_times_diff_ge[OF a_leq_b composition_L, of "i-1" ?s]
              using i_bound by fastforce
            then have "ia < t"
              using t_bound ia_bound by auto
            then have ia_cond: "interval_times a L ! 1 \<le> ia \<and> ia < t"
              using ia_location by simp
            then have ?thesis using t_minimal by blast
          }
          ultimately show ?thesis by linarith
        qed
        then have global_not: "semantics_mltl_ext \<pi>
         (Global_mltl_ext (interval_times a L ! 0) (interval_times a L ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>))"
          unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
          using bound not_semantics by blast
        have future: "semantics_mltl_ext \<pi> (Future_mltl_ext (interval_times a L ! i)
         (interval_times a L ! (i + 1) - 1) [interval_times a L ! (i + 1) - interval_times a L ! i] x)"
        proof-
          have "interval_times a L ! i \<le> b"
            using interval_times_diff_ge_general[OF a_leq_b composition_L, of "length L" i ?s]
            unfolding slast using i_bound by auto
          then have trace_length: "interval_times a L ! i < length \<pi>"
            using length_\<pi>_geq_b by auto
          have semantics: "(\<exists>ia. (interval_times a L ! i \<le> ia \<and>
           ia \<le> interval_times a L ! (i + 1) - 1) \<and>
          semantics_mltl (drop ia \<pi>) (to_mltl x))"
            using x_semantics t_bound semantics_mltl_ext_def 
            by auto 
          have "interval_times a L ! i \<le> interval_times a L ! (i + 1) - 1"
            using interval_times_diff_ge[OF a_leq_b composition_L, of i ?s]
            using i_bound by simp
          then show ?thesis unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
            using trace_length semantics by blast
        qed
        show ?thesis using global_not future 
          unfolding semantics_mltl_ext_def semantics_mltl.simps by simp
      qed
      have ?thesis
        unfolding Suc(5) Future_mltl_ext LP_mltl_aux.simps 
        using \<psi>_in \<psi>_semantics 
      proof -
        have "convert_nnf_ext \<alpha> = \<alpha>"
          by (metis \<alpha>_nnf convert_nnf_ext_convert_nnf_ext)
        then have "And_mltl_ext (Global_mltl_ext (interval_times a L ! 0) (interval_times a L ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)) 
(Future_mltl_ext (interval_times a L ! i) (interval_times a L ! (i + 1) - 1) 
[interval_times a L ! (i + 1) - interval_times a L ! i] x) \<in> 
set (Future_mltl_list (LP_mltl_aux (convert_nnf_ext \<alpha>) k) (interval_times a L ! 0) (interval_times a L ! 1 - 1) 
[interval_times a L ! 1 - interval_times a L ! 0] 
@ concat (map (\<lambda>n. And_mltl_list [Global_mltl_ext (interval_times a L ! 0) (interval_times a L ! n - 1) [?s!n - ?s!0] (Not\<^sub>c \<alpha>)] 
(Future_mltl_list (LP_mltl_aux (convert_nnf_ext \<alpha>) k) (interval_times a L ! n) (interval_times a L ! (n + 1) - 1) [interval_times a L ! (n + 1) - interval_times a L ! n])) [1..<length L]))"
          using \<psi>_in by presburger
        then show "\<exists>m\<in>set (let ms = LP_mltl_aux (convert_nnf_ext \<alpha>) k; 
ns = interval_times a L in Future_mltl_list ms (ns ! 0) (ns ! 1 - 1) 
[ns ! 1 - ns ! 0] @ concat (map (\<lambda>n. And_mltl_list 
[Global_mltl_ext (ns ! 0) (ns ! n - 1) [ns!n - ns!0] (Not\<^sub>c \<alpha>)] (Future_mltl_list ms (ns ! n) (ns ! (n + 1) - 1) [ns ! (n + 1) - ns ! n])) [1..<length L])). semantics_mltl_ext \<pi> m"
          by (meson \<psi>_semantics)
      qed 
    }
    ultimately show ?thesis using semantics by force
  next
    case (Global_mltl_ext a b L \<alpha>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
      using Suc(2) unfolding Global_mltl_ext by auto
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Global_mltl_ext
      by (metis convert_nnf_ext.simps(7) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(6))
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
      using Suc(4) unfolding Global_mltl_ext is_composition_MLTL.simps by blast
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
      using Suc(7) unfolding Global_mltl_ext to_mltl.simps wpd_mltl.simps 
      by simp
    have a_leq_b: "a \<le> b"
      using Suc(6) \<alpha>_wpd unfolding Global_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
      by blast
    have length_\<pi>_geq_b: "b < length \<pi>"
    and semantics: "\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
      using Suc(6) \<alpha>_wpd unfolding Global_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
      using wpd_geq_one[of "(to_mltl \<alpha>)"] by auto
    let ?D_\<alpha> = "LP_mltl_aux \<alpha> k"
    {
      assume *: "length ?D_\<alpha> \<le> 1"
      let ?\<psi> = "Global_mltl_ext a b L \<alpha>"
      have semantics: "semantics_mltl \<pi> (to_mltl ?\<psi>)"
        using Suc(6) unfolding Global_mltl_ext semantics_mltl_ext_def
        by blast
      have \<psi>_in: "?\<psi> \<in> set D" using Suc(5) *
        unfolding Global_mltl_ext LP_mltl_aux.simps
        by (metis (full_types) \<alpha>_nnf convert_nnf_ext_convert_nnf_ext list.set_intros(1)) 
      have ?thesis 
        using semantics \<psi>_in Global_mltl_ext Suc.prems(5) by auto 
    } moreover {
      assume *: "length ?D_\<alpha> > 1"
      then have D_is: "D = Global_mltl_decomp ?D_\<alpha> a (b - a) L"
        using Suc(5) * unfolding Global_mltl_ext LP_mltl_aux.simps
        by (metis (full_types) \<alpha>_nnf convert_nnf_ext_convert_nnf_ext leD)
      have semantics_global: "semantics_mltl_ext \<pi> (Global_mltl_ext a b L \<alpha>)"
        using Suc(6) unfolding Global_mltl_ext by blast
      have length_\<pi>: "length \<pi> \<ge> b + wpd_mltl (to_mltl \<alpha>)"
        using Suc(6) \<alpha>_wpd unfolding Global_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        using wpd_geq_one[of "(to_mltl \<alpha>)"] by blast
      have ih: "\<And>trace. semantics_mltl_ext trace \<alpha> \<Longrightarrow>
                wpd_mltl (to_mltl \<alpha>) \<le> length trace \<Longrightarrow>
                \<exists>a\<in>set (LP_mltl_aux \<alpha> k). semantics_mltl_ext trace a"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of ?D_\<alpha>] by blast
      have "\<exists>X. length X = b - a + 1 \<and>
            (\<forall>i<length X. X ! i \<in> set (LP_mltl_aux \<alpha> k) \<and>
            semantics_mltl_ext (drop (a+i) \<pi>) (X ! i))"
        using Global_mltl_ext_obtain[OF a_leq_b length_\<pi> semantics_global ih] 
        by blast
      then obtain Y where length_Y: "length Y = b - a + 1"
        and Y_prop: "\<forall>i<length Y. Y!i \<in> set ?D_\<alpha> \<and>
                      semantics_mltl_ext (drop (a+i) \<pi>) (Y ! i)"
        by blast
      let ?X = "map (\<lambda>i. Global_mltl_ext (a+i) (a+i) [1] (Y!i)) [0..<length Y]"
      let ?\<psi> = "Ands_mltl_ext ?X"
      have cond1: "?\<psi> = ?\<psi>" by auto
      have length_X: "length ?X = b-a+1"
        using length_Y by simp
      have cond2: "\<forall>i<length ?X.
      \<exists>y\<in>set ?D_\<alpha>. ?X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
        using Y_prop by simp
      have \<psi>_in: "?\<psi> \<in> set D"
        using in_Global_mltl_decomp_exact_converse[OF * cond1 cond2 length_X]
        unfolding D_is by blast
      have \<psi>_semantics: "semantics_mltl_ext \<pi> ?\<psi>"
      proof-
        have cond1: "length ?X \<ge> 1" using length_X by simp
        have "semantics_mltl_ext \<pi> (?X!i)"
          if i_bound: "i < length ?X" for i
        proof-
          have Xi_is: "?X!i = Global_mltl_ext (a + i) (a + i) [1] (Y ! i)"
            using i_bound by auto
          show ?thesis unfolding Xi_is
            using Y_prop i_bound unfolding semantics_mltl_ext_def
            unfolding semantics_mltl.simps by auto
        qed
        then have "(\<forall>x\<in>set ?X. semantics_mltl_ext \<pi> x)"
          by auto 
        then show ?thesis 
          using Ands_mltl_semantics[of ?X \<pi>, OF cond1] by blast
      qed
      have ?thesis using D_is \<psi>_in \<psi>_semantics by blast
    }
    ultimately show ?thesis by linarith
  next
    case (Until_mltl_ext \<alpha> a b L \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
     and \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) unfolding Until_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
     and \<beta>_composition: "is_composition_MLTL \<beta>"
     and L_composition: "is_composition (b-a+1) L"
      using Suc(4) unfolding Until_mltl_ext is_composition_MLTL.simps 
      by simp_all 
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>)-1 \<le> length \<pi>"
     and \<beta>_wpd: "b + wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using Suc(7) unfolding Until_mltl_ext to_mltl.simps wpd_mltl.simps 
      by simp_all
    have a_leq_b: "a \<le> b" and length_\<pi>_ge_b: "b < length \<pi>" 
    and semantics: "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
         semantics_mltl (drop i \<pi>) (to_mltl \<beta>) \<and>
         (\<forall>j. a \<le> j \<and> j < i \<longrightarrow>
              semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)))"
      using Suc(6) \<alpha>_wpd unfolding Until_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
      using wpd_geq_one[of "to_mltl \<beta>"] \<beta>_wpd
      by simp_all
    let ?D_\<beta> = "LP_mltl_aux \<beta> k"
    let ?s = "interval_times a L"
    have sfirst: "?s!0 = a"
      using interval_times_first by auto
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] by auto
    have length_L: "length L \<ge> 1"
      using composition_length_lb[OF L_composition] by linarith
    have s_second_lb: "a \<le> interval_times a L ! 1 - 1"
      using sfirst interval_times_diff_ge[OF a_leq_b L_composition, of 0 ?s]
      using length_L by force
    have s_second_ub: "interval_times a L ! 1 - 1 \<le> b"
      using slast length_L
      using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" 1 ?s]
      by force
    let ?front = "(Until_mltl_list \<alpha> ?D_\<beta> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
    let ?back = "(concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext
                              (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))]
                            (Until_mltl_list \<alpha> ?D_\<beta> (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i])) [1..<length L]))" 
    have D_union: "set D = (set ?front) \<union> (set ?back)"
      unfolding Suc(5) Until_mltl_ext LP_mltl_aux.simps
      using \<alpha>_convert \<beta>_convert list_concat_set_union by metis
    let ?P = "\<lambda>i. semantics_mltl (drop i \<pi>) (to_mltl \<beta>) \<and>
      (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
    {
      assume *: "\<exists>i. (a \<le> i) \<and> (i \<le> (?s!1)-1) \<and> ?P i"
      then obtain i where i_bound: "(a \<le> i \<and> i \<le> (?s!1)-1)" and
      semantics: "semantics_mltl (drop i \<pi>) (to_mltl \<beta>) \<and>
      (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
        by blast
      have semantics_dropi: "semantics_mltl_ext (drop i \<pi>) \<beta>"
        using semantics unfolding semantics_mltl_ext_def by blast
      have length_dropi: "wpd_mltl (to_mltl \<beta>) \<le> length (drop i \<pi>)"
        using \<beta>_wpd length_\<pi>_ge_b i_bound a_leq_b s_second_ub by auto
      obtain x where x_semantics: "semantics_mltl_ext (drop i \<pi>) x"
                 and x_in: "x \<in> set ?D_\<beta>"
        using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition _ semantics_dropi length_dropi, of ?D_\<beta>]
        by blast
      let ?\<psi> = "(Until_mltl_ext \<alpha> a ((?s!1)-1) [(?s!1) - a] x)"
      have \<psi>_semantics: "semantics_mltl_ext \<pi> ?\<psi>"
        using semantics length_\<pi>_ge_b a_leq_b i_bound x_semantics
        unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
        by auto 
      have "?\<psi> \<in> set ?front"
        using x_in unfolding Until_mltl_list.simps sfirst by auto
      then have \<psi>_in: "?\<psi> \<in> set D"
        unfolding D_union by blast
      have ?thesis 
        using \<psi>_semantics \<psi>_in by blast
    } moreover {
      assume *: "\<exists>i. ((?s!1) \<le> i) \<and> (i \<le> b) \<and> ?P i \<and>
                 \<not>(\<exists>j. a \<le> j \<and> j < (?s!1) \<and> ?P j)"
      then obtain t' where t'_bound: "((?s!1) \<le> t') \<and> (t' \<le> b)" and 
           semantics: "?P t'" and not_semantics: "\<not>(\<exists>j. a \<le> j \<and> j < (?s!1) \<and> ?P j)"
        by blast
      have "\<exists>j\<ge>interval_times a L ! 1. j \<le> t' \<and> 
            ?P j \<and> (\<forall>l. interval_times a L ! 1 \<le> l \<and> l < j \<longrightarrow> \<not> ?P l)"
      proof-
        have cond1: "interval_times a L ! 1 \<le> t'"
          using t'_bound by auto
        show ?thesis
          using exist_first[of "?s!1" t' ?P, OF cond1 semantics] by blast
      qed
      then obtain t where 
            t_bound: "interval_times a L ! 1 \<le> t \<and> t \<le> t'" and
            t_semantics: "?P t" and 
            t_minimal: "\<forall>l. interval_times a L ! 1 \<le> l \<and> l < t \<longrightarrow> \<not> ?P l"
        by blast
      have "\<exists>i. interval_times a L ! i \<le> t \<and>
      t \<le> interval_times a L ! (i + 1) - 1 \<and> 1 \<le> i \<and> i < length L"
        using interval_times_obtain_aux[OF a_leq_b L_composition, of ?s t]
        using t_bound t'_bound by simp
      then obtain i where t_bound: "interval_times a L ! i \<le> t 
                                  \<and> t \<le> interval_times a L ! (i + 1) - 1"
                      and i_bound: "1 \<le> i \<and> i < length L"
        by blast
      have bound1: "interval_times a L ! i < interval_times a L ! (i+1)"
        using interval_times_diff_ge[OF a_leq_b L_composition, of i ?s]
        using i_bound by blast
      have bound2: "a \<le> interval_times a L ! i - 1"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i" 0 ?s]
        using i_bound sfirst by simp
      have positive_i: "interval_times a L ! i > 0"
        using i_bound sfirst 
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i" 0 ?s]
        by auto
      have global_\<alpha>: "semantics_mltl_ext \<pi> (Global_mltl_ext a (?s ! i - 1) [?s!i - ?s!0] \<alpha>)"
      proof-
        have "semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>)"
          if ia_bound: "a \<le> ia \<and> ia \<le> interval_times a L ! i - 1" for ia
        proof- 
          have "a \<le> ia \<and> ia < t"
            using ia_bound t_bound positive_i by auto
          then show ?thesis
            using t_semantics by blast
        qed
        then show ?thesis
          using bound2
          unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
          by blast
      qed
      have global_not_\<beta>: "semantics_mltl_ext \<pi> (Global_mltl_ext a (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<beta>))"
      proof-
        have "\<not> semantics_mltl (drop ia \<pi>) (to_mltl \<beta>)"
          if ia_bound: "a \<le> ia \<and> ia \<le> interval_times a L ! i - 1" for ia
        proof-
          have globally: "(\<forall>j. a \<le> j \<and> j < ia \<longrightarrow>
                 semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
            using global_\<alpha> unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
            using length_\<pi>_ge_b a_leq_b
            using antisym dual_order.trans that by auto 
          have "a \<le> ia \<and> ia < t"
            using ia_bound t_bound positive_i by auto
          then show ?thesis
            using t_minimal globally
            by (meson linorder_le_less_linear not_semantics) 
        qed
        then show ?thesis
          unfolding semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
          using bound2 by blast
      qed
      let ?\<psi>1 = "Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))"
      have \<psi>1_semantics: "semantics_mltl_ext \<pi> ?\<psi>1"
      proof-
        have p1: "semantics_mltl \<pi> (Global_mltl (?s ! 0) (?s ! i - 1) (to_mltl \<alpha>))"
          using global_\<alpha> unfolding semantics_mltl_ext_def to_mltl.simps sfirst by blast
        have p2: "semantics_mltl \<pi> (Global_mltl (?s ! 0) (?s ! i - 1) (Not\<^sub>m (to_mltl \<beta>)))"
          using global_not_\<beta> unfolding semantics_mltl_ext_def to_mltl.simps sfirst by blast
        show ?thesis unfolding semantics_mltl_ext_def to_mltl.simps
          using p1 p2 global_and_distribute by auto
      qed
      have "interval_times a L ! (i + 1) \<le> ?s!(length L)"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i+1" ?s]
        using i_bound
        by (metis le_eq_less_or_eq less_iff_succ_less_eq) 
      then have "interval_times a L ! (i + 1)-1 \<le> b"
        using slast by auto
      then have "t \<le> b"
        using t_bound by simp
      then have "wpd_mltl (to_mltl \<beta>) \<le> length (drop t \<pi>)"
        using \<beta>_wpd by simp 
      then obtain x where x_semantics: "semantics_mltl_ext (drop t \<pi>) x"
                      and x_in: "x \<in> set ?D_\<beta>"
        using t_semantics
        using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition, of ?D_\<beta> "(drop t \<pi>)"]
        unfolding semantics_mltl_ext_def by blast
      let ?\<psi>2 = "Until_mltl_ext \<alpha> (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i] x"      
      have \<psi>2_semantics: "semantics_mltl_ext \<pi> ?\<psi>2"
      proof-
        have "(\<forall>j. interval_times a L ! i \<le> j \<and> j < t \<longrightarrow>
              semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
          using t_minimal not_semantics
          by (metis bound2 diff_less dual_order.strict_trans1 dual_order.strict_trans2 less_numeral_extra(1) nless_le positive_i t_semantics) 
        then have "semantics_mltl (drop t \<pi>) (to_mltl x) \<and>
         (\<forall>j. interval_times a L ! i \<le> j \<and> j < t \<longrightarrow>
              semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
          using x_semantics unfolding semantics_mltl_ext_def by blast
        then have "(\<exists>ia. (interval_times a L ! i \<le> ia \<and>
           ia \<le> interval_times a L ! (i + 1) - 1) \<and>
          semantics_mltl (drop ia \<pi>) (to_mltl x) \<and>
          (\<forall>j. interval_times a L ! i \<le> j \<and> j < ia \<longrightarrow>
               semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)))"
          using t_bound by blast
        then show ?thesis         
          unfolding semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using bound1
          by (smt (verit) \<open>interval_times a L ! (i + 1) - 1 \<le> b\<close> le_antisym le_neq_implies_less le_trans length_\<pi>_ge_b less_or_eq_imp_le) 
      qed
      let ?\<psi> = "And_mltl_ext ?\<psi>1 ?\<psi>2"
      have \<psi>_semantics: "semantics_mltl_ext \<pi> ?\<psi>"
        using \<psi>1_semantics \<psi>2_semantics unfolding semantics_mltl_ext_def by simp
      have "?\<psi> \<in> set ?back"
        using x_in i_bound
        unfolding Until_mltl_list.simps by auto
      then have \<psi>_in: "?\<psi> \<in> set D"
        using D_union by blast
      have ?thesis using \<psi>_semantics \<psi>_in by auto
    }
    ultimately show ?thesis 
      using exist_bound_split[OF a_leq_b, of ?P "?s!1"] semantics by blast
  next
    case (Release_mltl_ext \<alpha> a b L \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" 
     and \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) unfolding Release_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Release_mltl_ext
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8))
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Release_mltl_ext
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8))
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
     and \<beta>_composition: "is_composition_MLTL \<beta>"
     and L_composition: "is_composition (b-a+1) L"
      using Suc(4) unfolding Release_mltl_ext is_composition_MLTL.simps 
      by simp_all 
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
     and \<beta>_wpd: "b + wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using Suc(7) unfolding Release_mltl_ext to_mltl.simps wpd_mltl.simps 
       by simp_all
    have length_\<pi>_ge_b: "b < length \<pi>" 
      using wpd_geq_one[of "to_mltl \<beta>"] \<beta>_wpd
      by auto
    have a_leq_b: "a \<le> b"
      using Suc(6) \<alpha>_wpd unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
      by blast
    have semantics: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
          semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) \<or>
     (\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
      using Suc(6) unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
      using length_\<pi>_ge_b by auto
    let ?D = "LP_mltl_aux \<alpha> k"
    let ?s = "interval_times a L"
    have sfirst: "?s!0 = a"
      using interval_times_first by auto
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] by auto
    let ?front = "set [Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]"
    let ?middle = "set (Mighty_Release_mltl_list ?D \<beta> (?s ! 0) (?s ! 1 - 1)
                 [?s ! 1 - ?s ! 0])"
    let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                             [Global_mltl_ext
                               (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                             (Mighty_Release_mltl_list ?D \<beta> (?s ! i)
                               (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                   [1..<length L]))"
    let ?P = "\<lambda>j. (semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
    have D_is: "set D = ?front \<union> ?middle \<union> ?back"
      unfolding Suc(5) Release_mltl_ext LP_mltl_aux.simps 
      using \<alpha>_convert list_concat_set_union
      by (metis append_assoc) 
    {
      assume *: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) 
                \<and>(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) (Not\<^sub>m (to_mltl \<alpha>)))"
      let ?\<psi> = "Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
      have \<psi>_in: "?\<psi> \<in> set D"
        using D_is by auto
      have "semantics_mltl_ext \<pi> ?\<psi>"
        unfolding semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        using a_leq_b * by auto
      then have ?thesis using \<psi>_in by blast
    } moreover {
      assume *: "\<exists>i. a \<le> i \<and> i \<le> b \<and> ?P i"
      then obtain t' where t'_semantics: "?P t'"
                       and t'_bound: "a \<le> t' \<and> t' \<le> b"
        by blast
      then obtain t where t_semantics: "?P t"
                      and t_bound: "a \<le> t \<and> t \<le> t'"
                      and t_minimal: "\<forall>j. (a \<le> j \<and> j < t) \<longrightarrow> \<not> ?P j"
        using exist_first[of a t' ?P] by blast
      have globally_not\<alpha>: "\<forall>i. (a \<le> i \<and> i < t) \<longrightarrow> 
                \<not> (semantics_mltl_ext (drop i \<pi>) \<alpha>)"
        using t_minimal t_semantics unfolding semantics_mltl_ext_def by auto
      have \<alpha>_semantics: "semantics_mltl_ext (drop t \<pi>) \<alpha>"
        using t_semantics unfolding semantics_mltl_ext_def by blast
      have globally_\<beta>: "\<forall>i. (a \<le> i \<and> i \<le> t) \<longrightarrow> (semantics_mltl_ext (drop i \<pi>) \<beta>)"
        using t_semantics unfolding semantics_mltl_ext_def by blast
      obtain i where t_bound: "?s!i \<le> t \<and> t \<le> ?s!(i+1)-1"
                 and i_bound: "0 \<le> i \<and> i < length L"
        using interval_times_obtain[OF a_leq_b L_composition, of ?s t]
        using t_bound t'_bound by auto
      have lb: "a \<le> ?s!i"
        using i_bound sfirst interval_times_diff_ge_general[OF a_leq_b L_composition, of i 0 ?s]
        by force
      have welldef: "?s!i < ?s!(i+1)"
        using i_bound 
        using interval_times_diff_ge[OF a_leq_b L_composition, of i ?s]
        by blast
      have ub: "?s!(i+1) \<le> b+1"         
        using i_bound slast interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i+1" ?s]
        by (metis Orderings.order_eq_iff less_iff_succ_less_eq order_le_imp_less_or_eq order_less_imp_le)
      have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop t \<pi>)"
          using \<alpha>_wpd t_bound i_bound sfirst welldef ub by auto
      then obtain x where x_semantics: "semantics_mltl_ext (drop t \<pi>) x"
                      and x_in: "x \<in> set (LP_mltl_aux \<alpha> k)"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition _ \<alpha>_semantics, of ?D]
        by blast
      {
        assume i_bound: "i = 0"
        let ?\<psi> = "Mighty_Release_mltl_ext x \<beta> a (interval_times a L ! 1 - 1) [interval_times a L ! 1 - a]"
        have \<psi>_in: "?\<psi> \<in> ?middle" using x_in unfolding sfirst by auto
        then have \<psi>_in: "?\<psi> \<in> set D" using D_is by blast
        have "semantics_mltl_ext \<pi> ?\<psi>"
        proof-
          have sem1: "(\<forall>i. a \<le> i \<and> i \<le> interval_times a L ! 1 - 1 \<longrightarrow>
           semantics_mltl (drop i \<pi>) (to_mltl \<beta>)) \<or>
      (\<exists>j\<ge>a. j \<le> interval_times a L ! 1 - 1 - 1 \<and>
              semantics_mltl (drop j \<pi>) (to_mltl x) \<and>
              (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                   semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
          proof-
            {
              assume t_loc: "t = ?s ! (i + 1) - 1"
              then have ?thesis
                using globally_\<beta>
                by (simp add: i_bound t_semantics) 
            } moreover {
              assume t_loc: "?s ! i \<le> t \<and> t \<le> ?s ! (i + 1) - 1 -1"
              then have ?thesis
                using t_semantics i_bound globally_\<beta>
                by (metis add_cancel_right_left semantics_mltl_ext_def sfirst x_semantics) 
            }
            ultimately show ?thesis using t_bound by fastforce
          qed
          have sem2: "(\<exists>i. (a \<le> i \<and> i \<le> interval_times a L ! 1 - 1) \<and>
         semantics_mltl (drop i \<pi>) (to_mltl x))"
            using x_semantics t_bound ub lb welldef unfolding semantics_mltl_ext_def
            using i_bound sfirst by auto 
          show ?thesis unfolding Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using welldef i_bound sem1 sem2 length_\<pi>_ge_b a_leq_b by auto
        qed
        then have ?thesis
          using \<psi>_in by auto
      } moreover {
        assume i_bound: "0 < i \<and> i < length L"
        have lb: "a < ?s!i"
          using i_bound sfirst interval_times_diff_ge_general[OF a_leq_b L_composition, of i 0 ?s]
          by force
        let ?\<psi> = "And_mltl_ext
                    (Global_mltl_ext
                      a (interval_times a L ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                    (Mighty_Release_mltl_ext x \<beta>
                      (interval_times a L ! i) (interval_times a L ! (i + 1) - 1)
                      [interval_times a L ! (i + 1) - interval_times a L ! i])"
        have "?\<psi> \<in> ?back"
          using x_in i_bound sfirst by auto
        then have \<psi>_in: "?\<psi> \<in> set D" using D_is by blast
        have "semantics_mltl_ext \<pi> ?\<psi>"
        proof-
          have p1: "(\<forall>ia. a \<le> ia \<and> ia \<le> interval_times a L ! i - 1 \<longrightarrow>
            \<not> semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>) \<and>
            semantics_mltl (drop ia \<pi>) (to_mltl \<beta>))"
            using globally_not\<alpha> globally_\<beta> t_bound lb ub welldef
            unfolding semantics_mltl_ext_def by auto
          have p2: "(\<forall>ia. interval_times a L ! i \<le> ia \<and>
            ia \<le> interval_times a L ! (i + 1) - 1 \<longrightarrow>
            semantics_mltl (drop ia \<pi>) (to_mltl \<beta>)) \<or>
      (\<exists>j\<ge>interval_times a L ! i.
          j \<le> interval_times a L ! (i + 1) - 1 - 1 \<and>
          semantics_mltl (drop j \<pi>) (to_mltl x) \<and>
          (\<forall>k. interval_times a L ! i \<le> k \<and> k \<le> j \<longrightarrow>
               semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
          proof-
            {
              assume t_loc: "t = interval_times a L ! (i + 1) - 1"
              then have ?thesis
                using globally_\<beta> t_bound ub lb welldef
                by (metis le_trans less_or_eq_imp_le t_semantics) 
            } moreover {
              assume t_loc: "t \<le> interval_times a L ! (i + 1) - 1-1"
              then have ?thesis
                using x_semantics globally_\<beta> t_bound ub lb welldef
                by (meson le_trans less_imp_le_nat semantics_mltl_ext_def)
            }
            ultimately show ?thesis using t_bound by fastforce
          qed
          have p3: "(\<exists>ia. (interval_times a L ! i \<le> ia \<and>
           ia \<le> interval_times a L ! (i + 1) - 1) \<and>
          semantics_mltl (drop ia \<pi>) (to_mltl x))"
            using x_semantics i_bound lb ub welldef  
            unfolding semantics_mltl_ext_def
            using t_bound by auto 
          have tracelen: "interval_times a L ! i < length \<pi>"
            using length_\<pi>_ge_b ub welldef by simp
          then show ?thesis unfolding semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            using lb ub welldef p1 p2 p3 by auto
        qed
        then have ?thesis
          using \<psi>_in by auto
      }
      ultimately have ?thesis using i_bound by blast
    }
    ultimately show ?thesis using semantics Release_semantics_split 
      by blast 
  qed
qed


paragraph \<open>Converse Direction\<close>

lemma LP_mltl_aux_language_union_converse:
  fixes \<phi>::"'a mltl_ext" and k::"nat" and \<pi>::"'a set list"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes trace_length: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
  assumes D_is: "D = LP_mltl_aux \<phi> k"
  assumes "\<exists>\<psi> \<in> set D. semantics_mltl_ext \<pi> \<psi>"
  shows "semantics_mltl_ext \<pi> \<phi>"
  using assms
proof(induct k arbitrary: D \<phi> \<pi>)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case 
  proof(cases \<phi>)
    case True_mltl_ext
    then show ?thesis unfolding semantics_mltl_ext_def by simp
  next
    case False_mltl_ext
    then show ?thesis using assms unfolding semantics_mltl_ext_def
      by (metis LP_mltl_aux.simps(3) Suc.prems(5) Suc.prems(6) empty_iff empty_set semantics_mltl_ext_def set_ConsD)
  next
    case (Prop_mltl_ext p)
    then show ?thesis using Suc
      unfolding semantics_mltl_ext_def by simp
  next
    case (Not_mltl_ext q)
    then have "\<exists>p. q = Prop_mltl_ext p"
      using convert_nnf_form_Not_Implies_Prop Suc
      by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
    then obtain p where "q = Prop_mltl_ext p" by blast 
    then show ?thesis 
      using Not_mltl_ext Suc by simp
  next
    case (And_mltl_ext \<alpha> \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) unfolding And_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding And_mltl_ext
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding And_mltl_ext
      by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3)) 
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and 
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(4) unfolding And_mltl_ext is_composition_MLTL.simps by simp_all
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_wpd: "length \<pi> \<ge> wpd_mltl (to_mltl \<alpha>)" and
         \<beta>_wpd: "length \<pi> \<ge> wpd_mltl (to_mltl \<beta>)"
      using Suc(5) unfolding And_mltl_ext to_mltl.simps wpd_mltl.simps
      by simp_all
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D"
               and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    let ?Da = "LP_mltl_aux \<alpha> k"
    let ?Db = "LP_mltl_aux \<beta> k"
    obtain x y where \<psi>_is: "\<psi> = And_mltl_ext x y" 
               and x_in: "x \<in> set ?Da"
               and y_in: "y \<in> set ?Db"
      using \<psi>_in unfolding Suc(6) And_mltl_ext LP_mltl_aux.simps 
      using And_mltl_list_member unfolding List.member_def
      using \<alpha>_convert \<beta>_convert by metis
    have x_semantics: "semantics_mltl_ext \<pi> x" and
         y_semantics: "semantics_mltl_ext \<pi> y"
      using \<psi>_semantics unfolding semantics_mltl_ext_def \<psi>_is to_mltl.simps
      by simp_all
    have \<alpha>_ih: "semantics_mltl_ext \<pi> \<alpha>"
      using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition \<alpha>_wpd, of ?Da]
      using x_in x_semantics by blast
    have \<beta>_ih: "semantics_mltl_ext \<pi> \<beta>"
      using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition \<beta>_wpd, of ?Db]
      using y_in y_semantics by blast
    show ?thesis
      using \<alpha>_ih \<beta>_ih unfolding And_mltl_ext semantics_mltl_ext_def by auto
  next
    case (Or_mltl_ext \<alpha> \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using Suc(2) unfolding Or_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4)) 
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and 
         \<beta>_composition: "is_composition_MLTL \<beta>"
      using Suc(4) unfolding Or_mltl_ext is_composition_MLTL.simps by simp_all
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_wpd: "length \<pi> \<ge> wpd_mltl (to_mltl \<alpha>)" and
         \<beta>_wpd: "length \<pi> \<ge> wpd_mltl (to_mltl \<beta>)"
      using Suc(5) unfolding Or_mltl_ext to_mltl.simps wpd_mltl.simps
      by simp_all
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D"
               and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    let ?Da = "LP_mltl_aux \<alpha> k"
    let ?Db = "LP_mltl_aux \<beta> k"
    let ?front = "And_mltl_list ?Da ?Db"
    let ?middle = "And_mltl_list [Not\<^sub>c \<alpha>] ?Db"
    let ?back = "And_mltl_list ?Da [Not\<^sub>c \<beta>]"
    have cases: "\<psi> \<in> (set ?front) \<union> (set ?middle) \<union> (set ?back)"
      using Suc(6) unfolding Or_mltl_ext LP_mltl_aux.simps using \<psi>_in
      by (metis \<alpha>_convert \<beta>_convert boolean_algebra_cancel.sup1 set_append) 
    {
      assume *: "\<psi> \<in> set ?front"
      obtain x y where \<psi>_is: "\<psi> = And_mltl_ext x y" 
               and x_in: "x \<in> set ?Da"
               and y_in: "y \<in> set ?Db"
        using \<psi>_in * unfolding Or_mltl_ext LP_mltl_aux.simps 
        using And_mltl_list_member unfolding List.member_def
        using \<alpha>_convert \<beta>_convert by metis
      have x_semantics: "semantics_mltl_ext \<pi> x" and
           y_semantics: "semantics_mltl_ext \<pi> y"
        using \<psi>_semantics unfolding semantics_mltl_ext_def \<psi>_is to_mltl.simps
        by simp_all
      have \<alpha>_ih: "semantics_mltl_ext \<pi> \<alpha>"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition \<alpha>_wpd, of ?Da]
        using x_in x_semantics by blast
      have \<beta>_ih: "semantics_mltl_ext \<pi> \<beta>"
        using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition \<beta>_wpd, of ?Db]
        using y_in y_semantics by blast
      have ?thesis
        using \<alpha>_ih \<beta>_ih unfolding Or_mltl_ext semantics_mltl_ext_def by auto
    } moreover {
      assume *: "\<psi> \<in> set ?middle"
      obtain y where \<psi>_is: "\<psi> = And_mltl_ext (Not\<^sub>c \<alpha>) y" 
               and y_in: "y \<in> set ?Db"
        using \<psi>_in * unfolding Or_mltl_ext LP_mltl_aux.simps 
        using And_mltl_list_member unfolding List.member_def
        using \<alpha>_convert \<beta>_convert by auto
      have x_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<alpha>)" and
           y_semantics: "semantics_mltl_ext \<pi> y"
        using \<psi>_semantics unfolding semantics_mltl_ext_def \<psi>_is to_mltl.simps
        by simp_all
      have \<beta>_ih: "semantics_mltl_ext \<pi> \<beta>"
        using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition \<beta>_wpd, of ?Db]
        using y_in y_semantics by blast
      have ?thesis
        using \<beta>_ih unfolding Or_mltl_ext semantics_mltl_ext_def by auto
    } moreover {
      assume *: "\<psi> \<in> set ?back"
      obtain x where \<psi>_is: "\<psi> = And_mltl_ext x (Not\<^sub>c \<beta>)" 
               and x_in: "x \<in> set ?Da"
        using \<psi>_in * unfolding Or_mltl_ext LP_mltl_aux.simps 
        using And_mltl_list_member unfolding List.member_def
        using \<alpha>_convert \<beta>_convert
        by (metis empty_iff empty_set set_ConsD)
      have x_semantics: "semantics_mltl_ext \<pi> x" and
           y_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<beta>)"
        using \<psi>_semantics unfolding semantics_mltl_ext_def \<psi>_is to_mltl.simps
        by simp_all
      have \<alpha>_ih: "semantics_mltl_ext \<pi> \<alpha>"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition \<alpha>_wpd, of ?Da]
        using x_in x_semantics by blast
      have ?thesis
        using \<alpha>_ih unfolding Or_mltl_ext semantics_mltl_ext_def by auto
    }
    ultimately show ?thesis using cases by blast
  next
    case (Future_mltl_ext a b L \<alpha>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         a_leq_b: "a \<le> b"
      using Suc(2) unfolding Future_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Future_mltl_ext
      by (metis convert_nnf_ext.simps(6) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(5)) 
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         L_composition: "is_composition (b-a+1) L"
      using Suc(4) unfolding Future_mltl_ext is_composition_MLTL.simps by simp_all
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis 
    have \<alpha>_wpd: "length \<pi> \<ge> b + wpd_mltl (to_mltl \<alpha>)"
      using Suc(5) unfolding Future_mltl_ext to_mltl.simps wpd_mltl.simps
      by simp_all
    then have length_\<pi>_ge_b: "length \<pi> > b"
      using wpd_geq_one[of "to_mltl \<alpha>"] by auto
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D"
               and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    let ?D = "LP_mltl_aux \<alpha> k"
    let ?s = "interval_times a L"
    have length_L: "1 \<le> length L"
      using composition_length_lb[OF L_composition] a_leq_b by linarith
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] by blast
    let ?front = "(Future_mltl_list ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
    let ?back = "(concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                  [1..<length L]))"
    have cases: "\<psi> \<in> (set ?front) \<union> (set ?back)"
      using \<psi>_in using Suc(6) unfolding Future_mltl_ext LP_mltl_aux.simps
      using list_concat_set_union[of ?front ?back] \<alpha>_convert by metis
    {
      assume *: "\<psi> \<in> set ?front"
      then obtain x where \<psi>_is: "\<psi> = Future_mltl_ext (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] x"
                    and x_in: "x \<in> set ?D"
        unfolding Future_mltl_list.simps by fastforce
      obtain l where x_semantics: "semantics_mltl (drop l \<pi>) (to_mltl x)" and
                     l_bound: "a \<le> l \<and> l \<le> interval_times a L ! 1 - 1"
        using \<psi>_semantics 
        unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps sfirst
        by blast
      have bound: "interval_times a L ! 1 - 1 \<le> b"
        using slast length_L l_bound
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" 1 ?s]
        by force
      then have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop l \<pi>)"
        using \<alpha>_wpd l_bound by auto
      then have \<alpha>_ih: "semantics_mltl_ext (drop l \<pi>) \<alpha>"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop l \<pi>" ?D]
        using x_in x_semantics semantics_mltl_ext_def by auto 
      then have ?thesis unfolding Future_mltl_ext semantics_mltl_ext_def
        unfolding to_mltl.simps semantics_mltl.simps
        using length_\<pi>_ge_b a_leq_b l_bound bound by auto
    } moreover {
      assume *: "\<psi> \<in> set ?back"
      then obtain i where \<psi>_is: "\<psi> \<in> set (And_mltl_list
                            [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))"
        and i_bound: "1 \<le> i \<and> i < length L"
        by force
      obtain x where \<psi>_is: "\<psi> = And_mltl_ext
                            (Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>))
                            (Future_mltl_ext (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i] x)"
                      and x_in: "x \<in> set ?D"
        using \<psi>_is unfolding Future_mltl_list.simps by auto
      obtain l where x_semantics: "semantics_mltl (drop l \<pi>) (to_mltl x)" and
                     l_bound: "?s ! i \<le> l \<and> l \<le> ?s ! (i + 1) - 1"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by auto
      have "interval_times a L ! (i + 1) \<le> interval_times a L ! length L"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i+1" ?s]
        using i_bound
        by (metis less_iff_succ_less_eq order_le_less) 
      then have bound: "interval_times a L ! (i + 1) \<le> b+1"
        unfolding slast by blast
      then have "l \<le> b"
        using l_bound slast by auto
      then have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop l \<pi>)"
        using l_bound \<alpha>_wpd by simp
      then have \<alpha>_ih: "semantics_mltl_ext (drop l \<pi>) \<alpha>"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop l \<pi>" ?D]
        using x_in x_semantics semantics_mltl_ext_def by blast
      have lb: "a \<le> interval_times a L ! i"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of i 0 ?s]
        using sfirst i_bound by auto
      have ?thesis unfolding Future_mltl_ext semantics_mltl_ext_def
        unfolding to_mltl.simps semantics_mltl.simps
        using length_\<pi>_ge_b a_leq_b l_bound \<alpha>_ih lb bound unfolding semantics_mltl_ext_def
        by (metis \<open>l \<le> b\<close> dual_order.trans order_le_less_trans)
    }
    ultimately show ?thesis using cases by blast
  next
    case (Global_mltl_ext a b L \<alpha>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         a_leq_b: "a \<le> b"
      using Suc(2) unfolding Global_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Global_mltl_ext
      by (metis convert_nnf_ext.simps(7) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(6)) 
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
      using Suc(4) unfolding Global_mltl_ext is_composition_MLTL.simps by simp_all
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis 
    have \<alpha>_wpd: "length \<pi> \<ge> b + wpd_mltl (to_mltl \<alpha>)"
      using Suc(5) unfolding Global_mltl_ext to_mltl.simps wpd_mltl.simps
      by simp_all
    then have length_\<pi>_ge_b: "length \<pi> > b"
      using wpd_geq_one[of "to_mltl \<alpha>"] by auto
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D"
               and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    let ?D = "LP_mltl_aux \<alpha> k"
    {
      assume *: "length ?D \<le> 1"
      have "D = [Global_mltl_ext a b L \<alpha>]"
        using Suc(6) unfolding Global_mltl_ext LP_mltl_aux.simps
        using * \<alpha>_convert by auto
      then have ?thesis using Suc
        by (simp add: Global_mltl_ext)  
    } moreover {
      assume *: "length ?D > 1"
      then have D_is: "D = (Global_mltl_decomp ?D a (b - a) L)"
        using Suc \<alpha>_nnf \<alpha>_convert unfolding Global_mltl_ext LP_mltl_aux.simps
        by simp
      obtain \<psi> where \<psi>_in: "\<psi> \<in> set (Global_mltl_decomp ?D a (b - a) L)"
                      and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
        using Suc(7) unfolding D_is by blast
      then obtain X where \<psi>_is: "\<psi> = Ands_mltl_ext X" 
                    and X_fact: "\<forall>i<length X. \<exists>y\<in>set (LP_mltl_aux \<alpha> k). 
                                 X ! i = Global_mltl_ext (a + i) (a + i) [1] y"
                    and length_X: "length X = Suc (b - a)"
        using in_Global_mltl_decomp_exact_forward[OF * \<psi>_in] by blast
      have "semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
        if i_bound: "a \<le> i \<and> i \<le> b" for i
      proof-
        have "i-a < length X"
          using i_bound length_X a_leq_b by linarith
        then obtain y where y_in: "y \<in> set ?D"
                   and Xi_is: "X!(i-a) = Global_mltl_ext (a+i-a) (a+i-a) [1] y"
          using X_fact i_bound by auto
        have "semantics_mltl_ext (drop i \<pi>) y"
        proof-
          have i_length_trace: "i< length \<pi>"
            using i_bound length_\<pi>_ge_b by auto
          have Ands_semantics: "(\<forall>x\<in>set X. semantics_mltl_ext \<pi> x)"
            using \<psi>_semantics unfolding \<psi>_is
            using Ands_mltl_semantics[of X \<pi>] length_X by auto
          have "(Global_mltl_ext i i [1] y) \<in> set X"
            using Xi_is i_bound \<open>i - a < length X\<close> nth_mem by fastforce 
          then have "semantics_mltl_ext \<pi> (Global_mltl_ext i i [1] y)"
            using Ands_semantics by blast
          then show ?thesis unfolding semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using i_length_trace by simp
        qed
        then have semantics: "\<exists>a\<in>set ?D. semantics_mltl_ext (drop i \<pi>) a"
          using y_in by blast
        have wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop i \<pi>)"
          using length_\<pi>_ge_b \<alpha>_wpd i_bound by auto
        show ?thesis
          using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop i \<pi>" ?D]
          using wpd semantics unfolding semantics_mltl_ext_def by blast
      qed
      then have ?thesis unfolding Global_mltl_ext semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
        using a_leq_b length_\<pi>_ge_b by blast
    }
    ultimately show ?thesis by linarith
  next
    case (Until_mltl_ext \<alpha> a b L \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)" and
         a_leq_b: "a \<le> b"
      using Suc(2) unfolding Until_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7))
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>" and
         L_composition: "is_composition (b-a+1) L"
      using Suc(4) unfolding Until_mltl_ext is_composition_MLTL.simps by simp_all
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_wpd: "length \<pi> \<ge> b+wpd_mltl (to_mltl \<alpha>)-1" and
         \<beta>_wpd: "length \<pi> \<ge> b+wpd_mltl (to_mltl \<beta>)"
      using Suc(5) unfolding Until_mltl_ext to_mltl.simps wpd_mltl.simps
      by simp_all
    then have length_\<pi>_ge_b: "length \<pi> > b"
      using wpd_geq_one[of "to_mltl \<beta>"] by auto
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D"
               and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    let ?D = "LP_mltl_aux \<beta> k"
    let ?s = "interval_times a L"
    have length_L: "1 \<le> length L"
      using composition_length_lb[OF L_composition] a_leq_b by linarith
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] by blast
    let ?front = "(Until_mltl_list \<alpha> ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
    let ?back = "(concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext
                              (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))]
                            (Until_mltl_list \<alpha> ?D (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i])) [1..<length L]))" 
    have D_union: "set D = (set ?front) \<union> (set ?back)"
      using Suc(6) unfolding Until_mltl_ext LP_mltl_aux.simps
      using \<alpha>_convert \<beta>_convert list_concat_set_union by metis
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D" and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    {
      assume *: "\<psi> \<in> set ?front"
      then obtain y where \<psi>_is: "\<psi> = Until_mltl_ext \<alpha> (interval_times a L ! 0) 
                      (interval_times a L ! 1 - 1) [interval_times a L ! 1 - interval_times a L ! 0] y"
                      and y_in: "y \<in> set ?D"   
        by auto
      have length_s: "1 < length ?s" using \<psi>_is
        by (metis One_nat_def add.commute add_gr_0 add_less_cancel_right L_composition composition_length_lb interval_times_length plus_1_eq_Suc zero_less_one) 
      then have length_L: "1 \<le> length L"
        unfolding interval_times_def
        by (simp add: less_eq_iff_succ_less) 
      have "interval_times a L ! 1 \<le> interval_times a L ! (length L)"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" 1 ?s]
        using length_L by force
      then have ub: "interval_times a L ! 1 - 1 \<le> b"
        using slast by auto
      obtain l where y_semantics: "semantics_mltl_ext (drop l \<pi>) y"
                 and \<alpha>_global: "(\<forall>j. interval_times a L ! 0 \<le> j \<and> j < l \<longrightarrow>
            semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
                 and l_bound: "?s ! 0 \<le> l \<and> l \<le> ?s ! 1 - 1"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by blast
      have l_ab: "a \<le> l \<and> l \<le> b"
        using l_bound sfirst ub by simp
      have sem: "\<exists>a\<in>set (LP_mltl_aux \<beta> k). semantics_mltl_ext (drop l \<pi>) a"
          using y_in y_semantics by blast
      have "wpd_mltl (to_mltl \<beta>) \<le> length (drop l \<pi>)"
        using l_bound length_\<pi>_ge_b \<beta>_wpd ub by auto
      then have ih: "semantics_mltl_ext (drop l \<pi>) \<beta>"
        using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition, of "drop l \<pi>" ?D]
        using sem by blast
      have "semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)"
        if j_bound: "a \<le> j \<and> j < l" for j
        using \<alpha>_global unfolding sfirst using j_bound l_bound ub by blast
      then have "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
         semantics_mltl (drop i \<pi>) (to_mltl \<beta>) \<and>
         (\<forall>j. a \<le> j \<and> j < i \<longrightarrow>
              semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)))"
        using ih l_ab unfolding semantics_mltl_ext_def by blast
      then have ?thesis unfolding Until_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        using a_leq_b length_\<pi>_ge_b by simp
    } moreover {
      assume *: "\<psi> \<in> set ?back"
      then obtain i y where 
      \<psi>_is: "\<psi> = And_mltl_ext (Global_mltl_ext (?s!0) (?s!i-1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
             (Until_mltl_ext \<alpha> (?s!i) (?s!(i+1)-1) [(?s!(i+1)) - (?s!i)] y)"
      and i_bound: "1 \<le> i \<and> i < length L" 
      and y_in: "y \<in> set ?D"
        by auto
      have bound1: "interval_times a L ! i < interval_times a L ! (i+1)"
        using interval_times_diff_ge[OF a_leq_b L_composition, of i ?s] 
        using i_bound by blast
      have "interval_times a L ! (i + 1) \<le> interval_times a L ! (length L)"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i+1" ?s]
        using i_bound by (metis less_iff_succ_less_eq order_le_less) 
      then have bound2: "interval_times a L ! (i+1) \<le> b+1"
        using slast by simp
      have "interval_times a L ! i > interval_times a L ! 0"
        using i_bound interval_times_diff_ge_general[OF a_leq_b L_composition, of i 0 ?s]
        by auto
      then have "interval_times a L ! i > 0"
        unfolding interval_times_def by simp
      then have "interval_times a L ! i \<le> b"
        using bound1 bound2 by simp
      have \<alpha>\<beta>_global: "(\<forall>ia. a \<le> ia \<and> ia \<le> interval_times a L ! i - 1 \<longrightarrow>
          semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>) \<and>
          \<not> semantics_mltl (drop ia \<pi>) (to_mltl \<beta>))"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        unfolding sfirst by auto
      have until: "(\<exists>ia. (interval_times a L ! i \<le> ia \<and>
         ia \<le> interval_times a L ! (i + 1) - 1) \<and>
        semantics_mltl (drop ia \<pi>) (to_mltl y) \<and>
        (\<forall>j. interval_times a L ! i \<le> j \<and> j < ia \<longrightarrow>
             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)))"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        unfolding sfirst by auto
      obtain l where y_semantics: "semantics_mltl_ext (drop l \<pi>) y"
                 and \<alpha>_global: "(\<forall>j. ?s ! i \<le> j \<and> j < l \<longrightarrow>
            semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
                 and l_bound: "?s ! i \<le> l \<and> l \<le> ?s ! (i+1) - 1"
        using until unfolding semantics_mltl_ext_def by blast
      have ub: "?s ! (i+1) - 1 \<le> b"
        using i_bound bound2 by auto 
      have lb: "a < ?s!i"
        using i_bound interval_times_diff_ge_general[OF a_leq_b L_composition, of "i" 0 ?s]
        using sfirst by auto
      have l_ab: "a \<le> l \<and> l \<le> b"
        using l_bound using ub lb by simp
      have sem: "\<exists>a\<in>set (LP_mltl_aux \<beta> k). semantics_mltl_ext (drop l \<pi>) a"
        using y_in y_semantics by blast
      have "wpd_mltl (to_mltl \<beta>) \<le> length (drop l \<pi>)"
        using \<beta>_wpd l_bound length_\<pi>_ge_b ub by auto
      then have ih: "semantics_mltl_ext (drop l \<pi>) \<beta>"
        using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition _ _ sem] by blast
      have l_ab: "a \<le> l \<and> l \<le> b"
        using l_bound lb ub by simp
      have "semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)"
        if j_bound: "a \<le> j \<and> j < l" for j
      proof-
        have case1: "\<forall>ia. a \<le> ia \<and> ia \<le> ?s ! i - 1 \<longrightarrow>
         semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>)"
          using \<alpha>\<beta>_global by blast
        {
          assume *: "a \<le> j \<and> j \<le> ?s ! i - 1"
          then have ?thesis
            using case1 by blast
        } moreover {
          assume *: "?s!i \<le> j \<and> j < l"
          then have ?thesis
            using \<alpha>_global by blast
        }
        ultimately show ?thesis using j_bound by linarith
      qed
      then have "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
         semantics_mltl (drop i \<pi>) (to_mltl \<beta>) \<and>
         (\<forall>j. a \<le> j \<and> j < i \<longrightarrow>
              semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)))"
        using ih l_ab semantics_mltl_ext_def by auto 
      then have ?thesis unfolding Until_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        using a_leq_b length_\<pi>_ge_b by simp
    }
    ultimately show ?thesis using D_union \<psi>_in by blast
  next
    case (Release_mltl_ext \<alpha> a b L \<beta>)
    have \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)" and
         a_leq_b: "a \<le> b"
      using Suc(2) unfolding Release_mltl_ext by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Release_mltl_ext
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8))
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using Suc(3) unfolding Release_mltl_ext
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8))
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>" and
         L_composition: "is_composition (b-a+1) L"
      using Suc(4) unfolding Release_mltl_ext is_composition_MLTL.simps by simp_all
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_wpd: "length \<pi> \<ge> b+wpd_mltl (to_mltl \<alpha>)" and
         \<beta>_wpd: "length \<pi> \<ge> b+wpd_mltl (to_mltl \<beta>)"
      using Suc(5) unfolding Release_mltl_ext to_mltl.simps wpd_mltl.simps
      by simp_all
    then have length_\<pi>_ge_b: "length \<pi> > b"
      using wpd_geq_one[of "to_mltl \<beta>"] by auto
    obtain \<psi> where \<psi>_in: "\<psi> \<in> set D"
               and \<psi>_semantics: "semantics_mltl_ext \<pi> \<psi>"
      using Suc(7) by blast
    let ?D = "LP_mltl_aux \<alpha> k"
    let ?s = "interval_times a L"
    have length_L: "1 \<le> length L"
      using composition_length_lb[OF L_composition] a_leq_b by linarith
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] by blast
    let ?front = "set [Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]"
    let ?middle = "set (Mighty_Release_mltl_list ?D \<beta> (?s ! 0) (?s ! 1 - 1)
                 [?s ! 1 - ?s ! 0])"
    let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                             [Global_mltl_ext
                               (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                             (Mighty_Release_mltl_list ?D \<beta> (?s ! i)
                               (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                   [1..<length L]))"
    let ?P = "\<lambda>j. (semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
    have D_is: "set D = ?front \<union> ?middle \<union> ?back"
      unfolding Suc(6) Release_mltl_ext LP_mltl_aux.simps 
      using \<alpha>_convert list_concat_set_union
      by (metis append_assoc) 
    have split: "\<psi> \<in> ?front \<union> ?middle \<union> ?back"
      using \<psi>_in D_is by blast
    {
      assume *: "\<psi> \<in> ?front"
      then have \<psi>_is: "\<psi> = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
        by auto
      then have ?thesis using \<psi>_semantics unfolding \<psi>_is
        unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by blast
    } moreover {
      assume *: "\<psi> \<in> ?middle"
      then obtain x where \<psi>_is: "\<psi> = Mighty_Release_mltl_ext x \<beta> a (?s ! 1 - 1) [?s ! 1 - a]"
                      and x_in: "x \<in> set ?D"
        using sfirst by auto
      have welldef: "a < ?s!1" using sfirst
        using interval_times_diff_ge[OF a_leq_b L_composition, of 0 ?s]
        using length_L by force
      have ub: "?s!1 \<le> b+1" 
        using length_L slast         
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" 1 ?s]
        by force
      obtain i where i_bound: "a \<le> i \<and> i \<le> interval_times a L ! 1 - 1" 
                 and x_semantics: "semantics_mltl (drop i \<pi>) (to_mltl x)"
        using \<psi>_semantics unfolding \<psi>_is Mighty_Release_mltl_ext.simps
        unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by auto
      have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop i \<pi>)"
        using \<alpha>_wpd i_bound ub by auto
      then have \<alpha>_semantics: "semantics_mltl_ext (drop i \<pi>) \<alpha>"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop i \<pi>" ?D]
        using x_in x_semantics unfolding semantics_mltl_ext_def by blast
      let ?globally_\<beta> = "(\<forall>i. a \<le> i \<and> i \<le> interval_times a L ! 1 - 1 \<longrightarrow>
           semantics_mltl (drop i \<pi>) (to_mltl \<beta>))"
      let ?release = "(\<exists>j\<ge>a. j \<le> interval_times a L ! 1 - 1 - 1 \<and>
            semantics_mltl (drop j \<pi>) (to_mltl x) \<and>
            (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                 semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
      have eo: "?globally_\<beta> \<or> ?release"  
        using \<psi>_semantics unfolding \<psi>_is Mighty_Release_mltl_ext.simps
        unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by auto
      {
        assume **: "?globally_\<beta>"
        {
          assume "interval_times a L ! 1 - 1 = b"
          then have ?thesis unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using ** a_leq_b by simp
        } moreover {
          assume s1_bound: "interval_times a L ! 1 - 1 < b"
          have "semantics_mltl (drop k \<pi>) (to_mltl \<beta>)"
            if k_bound: "a \<le> k \<and> k \<le> i" for k
            using ** k_bound i_bound s1_bound by auto
          then have ?thesis using ** \<alpha>_semantics i_bound ub a_leq_b 
            unfolding semantics_mltl_ext_def Release_mltl_ext to_mltl.simps semantics_mltl.simps
            using s1_bound by force
        }
        ultimately have ?thesis using ub by linarith
      } moreover {
        assume **: "?release"
        have bound: "interval_times a L ! 1 - 1 - 1 \<le> b-1"
          using ub by simp
        then obtain j where sem: "a \<le> j \<and> j \<le> interval_times a L ! 1 - 1 - 1 \<and>
         semantics_mltl (drop j \<pi>) (to_mltl x) \<and>
         (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
              semantics_mltl (drop k \<pi>) (to_mltl \<beta>))"
          using ** by blast
        have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop j \<pi>)"
          using \<alpha>_wpd sem ub by auto
        then have "semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)"
          using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop j \<pi>" ?D]
          using sem x_in unfolding semantics_mltl_ext_def by blast
        then have "(\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
          using sem ub by auto
        then have ?thesis 
          unfolding semantics_mltl_ext_def Release_mltl_ext to_mltl.simps semantics_mltl.simps
          using a_leq_b by blast
      }
      ultimately have ?thesis using eo by blast
    } moreover {
      assume *: "\<psi> \<in> ?back"
      then obtain i x where \<psi>_is: "\<psi> = And_mltl_ext
                         (Global_mltl_ext
                           (interval_times a L ! 0)
                           (interval_times a L ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                         (Mighty_Release_mltl_ext x \<beta>
                           (interval_times a L ! i)
                           (interval_times a L ! (i + 1) - 1)
                           [interval_times a L ! (i + 1) -
                            interval_times a L ! i])"
                      and x_in: "x \<in> set ?D"
                      and i_bound: "1 \<le> i \<and> i < length L"
        by auto
      have lb: "a < ?s!i"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of i 0 ?s]
        using sfirst i_bound by simp
      have welldef: "(interval_times a L ! i) < (interval_times a L ! (i + 1))"
        using interval_times_diff_ge[OF a_leq_b L_composition, of i ?s]
        using i_bound by simp
      have ub: "?s!(i+1) \<le> b+1"
        using slast i_bound
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i+1" ?s]
        by (metis Orderings.order_eq_iff less_iff_succ_less_eq order_le_imp_less_or_eq order_less_imp_le)

      have globally_before: "\<forall>ia. interval_times a L ! 0 \<le> ia \<and> ia \<le> interval_times a L ! i - 1 \<longrightarrow>
          \<not> semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>) \<and>
          semantics_mltl (drop ia \<pi>) (to_mltl \<beta>)"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps Mighty_Release_mltl_ext.simps
        using length_\<pi>_ge_b a_leq_b sfirst by auto
      have release: "(\<forall>ia. interval_times a L ! i \<le> ia \<and>
          ia \<le> interval_times a L ! (i + 1) - 1 \<longrightarrow>
          semantics_mltl (drop ia \<pi>) (to_mltl \<beta>)) \<or>
    (\<exists>j\<ge>interval_times a L ! i.
        j \<le> interval_times a L ! (i + 1) - 1 - 1 \<and>
        semantics_mltl (drop j \<pi>) (to_mltl x) \<and>
        (\<forall>k. interval_times a L ! i \<le> k \<and> k \<le> j \<longrightarrow>
             semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps Mighty_Release_mltl_ext.simps
        by auto
      obtain ia where ia_bound: "interval_times a L ! i \<le> ia \<and>
         ia \<le> interval_times a L ! (i + 1) - 1" 
                       and x_semantics: "semantics_mltl (drop ia \<pi>) (to_mltl x)"
        using \<psi>_semantics unfolding \<psi>_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps Mighty_Release_mltl_ext.simps
        by blast
      have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop ia \<pi>)"
        using \<alpha>_wpd ia_bound ub by auto
      then have \<alpha>_semantics: "semantics_mltl (drop ia \<pi>) (to_mltl \<alpha>)"
        using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop ia \<pi>" ?D]
        using x_semantics x_in unfolding semantics_mltl_ext_def by blast
      {
        assume global_\<beta>: "(\<forall>ia. interval_times a L ! i \<le> ia \<and>
          ia \<le> interval_times a L ! (i + 1) - 1 \<longrightarrow>
          semantics_mltl (drop ia \<pi>) (to_mltl \<beta>))"
        {
          assume eq: "interval_times a L ! (i + 1) - 1 = b"
          have "semantics_mltl (drop j \<pi>) (to_mltl \<beta>)"
            if j_bound: "a \<le> j \<and> j \<le> b" for j
          proof-
            have 1: "j \<le> interval_times a L ! i - 1 \<Longrightarrow> ?thesis"
              using globally_before j_bound unfolding sfirst by blast
            have 2: "j \<ge> interval_times a L ! i \<Longrightarrow> ?thesis"
              using global_\<beta> j_bound eq by blast
            show ?thesis
              using 1 2 by linarith              
          qed
          then have ?thesis          
            unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using a_leq_b by blast
        } moreover {
          assume le: "interval_times a L ! (i + 1) - 1 < b"
          have 1: "semantics_mltl (drop k \<pi>) (to_mltl \<beta>)"
            if k_bound: "a \<le> k \<and> k \<le> ia" for k
          proof-
            have 1: "k \<le> interval_times a L ! i - 1 \<Longrightarrow> ?thesis"
              using globally_before k_bound sfirst ia_bound by auto
            have 2: "k \<ge> interval_times a L ! i \<Longrightarrow> ?thesis"
              using global_\<beta> ia_bound k_bound by auto
            show ?thesis
              using 1 2 by linarith              
          qed  
          have 2: "a \<le> ia \<and> ia \<le> b - 1"
            using ia_bound ub lb le by auto
          then have "(\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
            using \<alpha>_semantics ia_bound le ub lb welldef 1 2 by blast 
          then have ?thesis
            unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using a_leq_b by auto
        }
        ultimately have ?thesis using ub by linarith
      } moreover {
        assume "(\<exists>j\<ge>interval_times a L ! i.
        j \<le> interval_times a L ! (i + 1) - 1 - 1 \<and>
        semantics_mltl (drop j \<pi>) (to_mltl x) \<and>
        (\<forall>k. interval_times a L ! i \<le> k \<and> k \<le> j \<longrightarrow>
             semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
        then obtain j where j_bound: "interval_times a L ! i \<le> j \<and> j \<le> interval_times a L ! (i + 1) - 1 - 1"
                        and x_semantics: "semantics_mltl (drop j \<pi>) (to_mltl x)"
                        and global: "\<forall>k. interval_times a L ! i \<le> k \<and> k \<le> j \<longrightarrow>
             semantics_mltl (drop k \<pi>) (to_mltl \<beta>)"
          by blast
        have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop j \<pi>)"
          using \<alpha>_wpd j_bound ub by auto
        then have \<alpha>_semantics: "semantics_mltl (drop j \<pi>) (to_mltl \<alpha>)"
          using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop j \<pi>" ?D]
          using x_in x_semantics unfolding semantics_mltl_ext_def by blast
        have g: "semantics_mltl (drop k \<pi>) (to_mltl \<beta>)"
          if k_bound: "a \<le> k \<and> k \<le> j" for k
          proof-
            have 1: "k \<le> interval_times a L ! i - 1 \<Longrightarrow> ?thesis"
              using globally_before k_bound sfirst ia_bound by auto
            have 2: "k \<ge> interval_times a L ! i \<Longrightarrow> ?thesis"
              using global ia_bound k_bound by auto
            show ?thesis
              using 1 2 by linarith              
          qed
        have "a \<le> j \<and> j \<le> b - 1"
          using j_bound ub lb by auto
        then have "(\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>) \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                  semantics_mltl (drop k \<pi>) (to_mltl \<beta>)))"
          using \<alpha>_semantics g by blast 
        then have ?thesis
          unfolding Release_mltl_ext semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using a_leq_b by blast 
      }
      ultimately have ?thesis using release by blast
    }
    ultimately show ?thesis using split by blast
  qed
qed

paragraph \<open>Top Level Union Theorem\<close>

lemma LP_mltl_aux_language_union:
  fixes \<phi>::"'a mltl_ext" and k::"nat" and \<pi>::"'a set list"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes trace_length: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes D_is: "D = LP_mltl_aux \<phi> k"
  shows "semantics_mltl_ext \<pi> \<phi> \<longleftrightarrow>
         (\<exists>\<psi> \<in> set D. semantics_mltl_ext \<pi> \<psi>)"
  using assms
  using LP_mltl_aux_language_union_converse
  using LP_mltl_aux_language_union_forward by fast

theorem LP_mltl_language_union_explicit:
  fixes \<phi>::"'a mltl_ext" and k::"nat" and \<pi>::"'a set list"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes D_is: "D = set (LP_mltl \<phi> k)"
  assumes trace_length: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
  shows "semantics_mltl_ext \<pi> \<phi> \<longleftrightarrow> (\<exists>\<psi>\<in>D. semantics_mltl \<pi> \<psi>)"
proof-
  have "D = set (map to_mltl
        (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k)))"
    using D_is unfolding LP_mltl.simps by blast
  let ?D_aux = "LP_mltl_aux (convert_nnf_ext \<phi>) k"
  let ?\<phi>_nnf = "convert_nnf_ext \<phi>"
  have wpd_decomp: "wpd_mltl \<psi> \<le> wpd_mltl (to_mltl \<phi>)"
    if \<psi>_in : "\<psi> \<in> D" for \<psi>
  proof-
    obtain x where \<psi>_is: "\<psi> = to_mltl (convert_nnf_ext x)"
               and x_in: "x \<in> set (LP_mltl_aux (convert_nnf_ext \<phi>) k)"
      using \<psi>_in unfolding D_is LP_mltl.simps by auto
    have xphi: "wpd_mltl (to_mltl x) \<le> wpd_mltl (to_mltl \<phi>)"
      using LP_mltl_aux_wpd[of "(convert_nnf_ext \<phi>)" x k]
      by (metis composition convert_nnf_ext_to_mltl_commute intervals_welldef is_composition_convert_nnf_ext nnf_intervals_welldef wpd_convert_nnf x_in)
    have "wpd_mltl (to_mltl x) = wpd_mltl \<psi>"
      unfolding \<psi>_is using convert_nnf_ext_to_mltl_commute
      by (metis wpd_convert_nnf) 
    then show ?thesis using xphi by auto
  qed
  have len_biconditional: "\<And>\<pi>. length \<pi> \<ge> wpd_mltl (to_mltl \<phi>) \<Longrightarrow> 
        (semantics_mltl \<pi> (to_mltl \<phi>) \<longleftrightarrow> (\<exists>\<psi>\<in>D. semantics_mltl \<pi> \<psi>))"
  proof-
    fix \<pi>::"'a set list"
    assume *: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
    let ?thesis = "semantics_mltl \<pi> (to_mltl \<phi>) \<longleftrightarrow>
        (\<exists>\<psi>\<in>D. semantics_mltl \<pi> \<psi>)"
    have "intervals_welldef (convert_nnf (to_mltl \<phi>))"
      using intervals_welldef nnf_intervals_welldef by blast
    then have cond1: "intervals_welldef (to_mltl (convert_nnf_ext \<phi>))"
      by (simp add: convert_nnf_ext_to_mltl_commute)
    have "?\<phi>_nnf = convert_nnf_ext (?\<phi>_nnf)"
      using convert_nnf_ext_convert_nnf_ext by blast
    then have cond2: "\<exists>\<phi>_init. convert_nnf_ext \<phi> = convert_nnf_ext \<phi>_init"
      by blast
    have cond3: "wpd_mltl (to_mltl (convert_nnf_ext \<phi>)) \<le> length \<pi>"
    proof-
      have "wpd_mltl (convert_nnf (to_mltl \<phi>)) \<le> length \<pi>"
        using * by (simp add: wpd_convert_nnf)
      then show ?thesis
        using convert_nnf_ext_to_mltl_commute by metis
    qed
    have cond4: "is_composition_MLTL (convert_nnf_ext \<phi>)"
      using composition intervals_welldef is_composition_convert_nnf_ext 
      by blast
    have aux_fact: "semantics_mltl_ext \<pi> (convert_nnf_ext \<phi>) =
  (\<exists>\<psi>\<in>set (LP_mltl_aux (convert_nnf_ext \<phi>) k). semantics_mltl_ext \<pi> \<psi>)"
      using LP_mltl_aux_language_union[OF cond1 cond2 cond3 cond4] by blast
    have forward: "(\<exists>\<psi>\<in>set (LP_mltl_aux (convert_nnf_ext \<phi>) k).
      semantics_mltl \<pi> (to_mltl \<psi>)) \<Longrightarrow> 
      (\<exists>\<psi>\<in>set (map to_mltl
               (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k))).
        semantics_mltl \<pi> \<psi>)"
    proof-
      assume "\<exists>\<psi>\<in>set (LP_mltl_aux (convert_nnf_ext \<phi>) k).
      semantics_mltl \<pi> (to_mltl \<psi>)"
      then obtain \<psi> where *: "\<psi>\<in>set (LP_mltl_aux (convert_nnf_ext \<phi>) k)" and 
                          **: "semantics_mltl \<pi> (to_mltl \<psi>)"
        by blast
      have in_set: "(to_mltl (convert_nnf_ext \<psi>)) \<in> set (map to_mltl
              (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k)))"
        using * by auto
      have "intervals_welldef (to_mltl \<psi>)"
        using intervals_welldef *
        using LP_mltl_aux_intervals_welldef
        using composition by auto 
      then have "semantics_mltl \<pi> (convert_nnf (to_mltl \<psi>))"
        using ** convert_nnf_preserves_semantics[of "to_mltl \<psi>" \<pi>] 
        by blast
      then have semantics: "semantics_mltl \<pi> (to_mltl (convert_nnf_ext \<psi>))"
        by (simp add: convert_nnf_ext_to_mltl_commute)
      show ?thesis using in_set semantics by blast
    qed
    have converse: "(\<exists>\<psi>\<in>set (map to_mltl
               (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k))).
        semantics_mltl \<pi> \<psi>) \<Longrightarrow> (\<exists>\<psi>\<in>set (LP_mltl_aux (convert_nnf_ext \<phi>) k).
      semantics_mltl \<pi> (to_mltl \<psi>))"
    proof-
      assume "\<exists>\<psi>\<in>set (map to_mltl
               (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k))).
        semantics_mltl \<pi> \<psi>"
      then obtain \<psi> where *: "\<psi>\<in>set (map to_mltl
               (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k)))" 
                 and **: "semantics_mltl \<pi> \<psi>"
        by blast
      obtain \<psi>_aux where aux_in: "\<psi>_aux \<in> set (LP_mltl_aux (convert_nnf_ext \<phi>) k)" and
                         is_aux: "\<psi> = to_mltl (convert_nnf_ext \<psi>_aux)"
        using "*" D_is LP_mltl_element \<open>D = set (map to_mltl (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k)))\<close> by blast
      have semantics: "semantics_mltl \<pi> (to_mltl \<psi>_aux)"
        using ** unfolding is_aux
        by (metis LP_mltl_aux_intervals_welldef aux_in composition convert_nnf_ext_to_mltl_commute convert_nnf_preserves_semantics intervals_welldef)
      show ?thesis using aux_in semantics by blast
    qed
    have "(\<exists>\<psi>\<in>set (LP_mltl_aux (convert_nnf_ext \<phi>) k).
      semantics_mltl \<pi> (to_mltl \<psi>)) = 
      (\<exists>\<psi>\<in>set (map to_mltl
               (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext \<phi>) k))).
        semantics_mltl \<pi> \<psi>)"
      using forward converse by blast
    then show ?thesis
      unfolding D_is LP_mltl.simps semantics_mltl_ext_def 
      using aux_fact convert_nnf_ext_to_mltl_commute convert_nnf_preserves_semantics
      by (metis intervals_welldef semantics_mltl_ext_def) 
  qed
  show ?thesis 
    using len_biconditional[of \<pi>] assms(4) 
    unfolding semantics_mltl_ext_def by blast
qed

theorem LP_mltl_language_union:
  fixes \<phi>::"'a mltl_ext" and k::"nat"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes D_is: "D = set (LP_mltl \<phi> k)"
  assumes r: "r = wpd_mltl (to_mltl \<phi>)"
  shows "language_mltl_r (to_mltl \<phi>) r
         = (\<Union> \<psi>\<in>D. language_mltl_r \<psi> r)"
proof-
  have "\<pi> \<in> language_mltl_r (to_mltl \<phi>) r \<longleftrightarrow>
        \<pi> \<in> (\<Union>\<psi>\<in>D. language_mltl_r \<psi> r)" 
    if length: "length \<pi> \<ge> r" for \<pi>
  proof-
    have equiv: "(\<exists>\<psi>\<in>D. semantics_mltl \<pi> \<psi>) \<longleftrightarrow> \<pi> \<in> (\<Union>\<psi>\<in>D. language_mltl_r \<psi> r)"
      unfolding language_mltl_r_def using length by blast
    have "semantics_mltl_ext \<pi> \<phi> = (\<exists>\<psi>\<in>D. semantics_mltl \<pi> \<psi>)"
      using LP_mltl_language_union_explicit[of \<phi> D k \<pi>]
      using assms length by blast
    then show ?thesis 
      using equiv length 
      unfolding language_mltl_r_def semantics_mltl_ext_def by blast
  qed
  then show ?thesis unfolding language_mltl_r_def
    by blast  
qed

subsection \<open>Disjointedness Theorem\<close>

lemma LP_mltl_language_disjoint_aux_helper:
  fixes \<phi> \<psi>1 \<psi>2::"'a mltl_ext" and k::"nat" and \<pi>::"'a set list"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes composition_allones: "is_composition_MLTL_allones \<phi>"
  assumes tracelen: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
  assumes D_decomp: "D = set (LP_mltl_aux \<phi> k)"
  assumes diff_formulas: "(\<psi>1 \<in> D) \<and> (\<psi>2 \<in> D) \<and> \<psi>1 \<noteq> \<psi>2"
  assumes sat1: "semantics_mltl_ext \<pi> \<psi>1"
  assumes sat2: "semantics_mltl_ext \<pi> \<psi>2"
  shows "False"
  using assms
  proof(induction k arbitrary: D \<phi> \<psi>1 \<psi>2 \<pi>)
    case 0
    then show ?case unfolding LP_mltl.simps LP_mltl_aux.simps
      by auto
  next
    case (Suc k)
    then show ?case 
    proof(cases \<phi>)
      case True_mltl_ext
      then show ?thesis  using Suc 
        unfolding True_mltl_ext LP_mltl.simps LP_mltl_aux.simps
        by auto
    next
      case False_mltl_ext
      then show ?thesis using Suc
        unfolding False_mltl_ext LP_mltl.simps LP_mltl_aux.simps
        by auto
    next
      case (Prop_mltl_ext p)
      then show ?thesis using Suc
        unfolding Prop_mltl_ext LP_mltl.simps LP_mltl_aux.simps
        by auto
    next
      case (Not_mltl_ext q)
      then have "\<exists>p. q = Prop_mltl_ext p"
        using convert_nnf_form_Not_Implies_Prop Suc
        by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
      then obtain p where "q = Prop_mltl_ext p" by blast 
      then show ?thesis
        using Suc unfolding Not_mltl_ext LP_mltl.simps LP_mltl_aux.simps
        by auto
    next
      case (And_mltl_ext \<alpha> \<beta>)
      let ?Dx = "LP_mltl_aux \<alpha> k"
      let ?Dy = "LP_mltl_aux \<beta> k"
      obtain x1 y1 where \<psi>1_is: "\<psi>1 = And_mltl_ext x1 y1" 
                     and x1_in: "x1 \<in> set ?Dx" and y1_in: "y1 \<in> set ?Dy"
        using And_mltl_list_member Suc.prems
        by (metis (no_types, lifting) And_mltl_ext LP_mltl_aux.simps(6) convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext in_set_member mltl_ext.inject(3))
      obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                     and x2_in: "x2 \<in> set ?Dx" and y2_in: "y2 \<in> set ?Dy"
        using And_mltl_list_member Suc.prems
        by (metis (no_types, lifting) And_mltl_ext LP_mltl_aux.simps(6) convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext in_set_member mltl_ext.inject(3))
      have eo: "x1 \<noteq> x2 \<or> y1 \<noteq> y2"
        using Suc(7) \<psi>1_is \<psi>2_is by blast
      have \<alpha>iwd: "intervals_welldef (to_mltl \<alpha>)" and
           \<beta>iwd: "intervals_welldef (to_mltl \<beta>)"
          using Suc(2) unfolding And_mltl_ext by simp_all
      have \<alpha>nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding And_mltl_ext
        by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3))
      have \<beta>nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding And_mltl_ext
        by (metis convert_nnf_ext.simps(4) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(3))
      have \<alpha>is_comp_allones: "is_composition_MLTL_allones \<alpha>" and
           \<beta>is_comp_allones: "is_composition_MLTL_allones \<beta>"
        using Suc(4) unfolding And_mltl_ext is_composition_MLTL_allones.simps by simp_all
      have \<alpha>is_comp: "is_composition_MLTL \<alpha>"
        using \<alpha>is_comp_allones allones_implies_is_composition_MLTL 
        by blast
      have \<beta>is_comp: "is_composition_MLTL \<beta>"
        using \<beta>is_comp_allones allones_implies_is_composition_MLTL 
        by blast
      have \<alpha>wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>" and
           \<beta>wpd: "wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
        using Suc(5) unfolding And_mltl_ext by simp_all
      let ?r = "wpd_mltl (to_mltl \<alpha>)"
      {
        assume xs_neq: "x1 \<noteq> x2"
        have x1_semantics: "semantics_mltl_ext \<pi> x1"
          using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def by simp
        have x2_semantics: "semantics_mltl_ext \<pi> x2"
          using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def by simp
        have ?thesis
          using Suc(1)[OF \<alpha>iwd \<alpha>nnf \<alpha>is_comp_allones \<alpha>wpd, of "set ?Dx" x1 x2]
          using \<alpha>wpd xs_neq x1_in x2_in x1_semantics x2_semantics by blast
      } moreover {
        assume ys_neq: "y1 \<noteq> y2"
        have y1_semantics: "semantics_mltl_ext \<pi> y1"
          using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def by simp
        have y2_semantics: "semantics_mltl_ext \<pi> y2"
          using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def by simp
        have ?thesis
          using Suc(1)[OF \<beta>iwd \<beta>nnf \<beta>is_comp_allones \<beta>wpd, of "set ?Dy" y1 y2]
          using \<beta>wpd ys_neq y1_in y2_in y1_semantics y2_semantics by blast
      }
      (* Use IH on x1 x2 or y1 y2, depending *)
      ultimately show ?thesis 
        using eo by argo
    next
      case (Or_mltl_ext \<alpha> \<beta>)
      let ?Dx = "LP_mltl_aux (convert_nnf_ext \<alpha>) k"
      let ?Dy = "LP_mltl_aux (convert_nnf_ext \<beta>) k"
      have D_is: "D = set ( And_mltl_list ?Dx ?Dy @
              And_mltl_list [Not\<^sub>c \<alpha>] ?Dy @
              And_mltl_list ?Dx [Not\<^sub>c \<beta>])"
        using Suc(6) unfolding Or_mltl_ext LP_mltl_aux.simps 
        by metis
      then have \<psi>1_eo: "List.member (And_mltl_list ?Dx ?Dy) \<psi>1 \<or>
          List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>1 \<or>
           List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>1"
        using Suc(7) by (simp add: member_def)
      have \<psi>2_eo: "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 \<or>
          List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2 \<or>
           List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
        using D_is Suc(7) by (simp add: member_def)
      (* prove some properties of \<alpha> *)
      have \<alpha>_iwd: "intervals_welldef (to_mltl \<alpha>)"
        using Suc(2) unfolding Or_mltl_ext by simp
      have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Or_mltl_ext
        by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4))
      have \<alpha>_is_comp: "is_composition_MLTL_allones \<alpha>"
        using Suc(4) unfolding Or_mltl_ext by simp
      have \<alpha>_wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
        using Suc(5) unfolding Or_mltl_ext by simp
      have \<alpha>_conv_same: "set (LP_mltl_aux (convert_nnf_ext \<alpha>) k) = set (LP_mltl_aux \<alpha> k)"
        by (metis \<alpha>_nnf convert_nnf_ext_convert_nnf_ext)
      (* prove some properties of \<beta> *)
      have \<beta>_iwd: "intervals_welldef (to_mltl \<beta>)"
        using Suc(2) unfolding Or_mltl_ext
        by simp
      have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Or_mltl_ext
        by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4))
      have \<beta>_is_comp: "is_composition_MLTL_allones \<beta>"
        using Suc(4) unfolding Or_mltl_ext
        by simp
      have \<beta>_wpd: "wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
        using Suc(5) unfolding Or_mltl_ext by simp
      have \<beta>_conv_same: "set (LP_mltl_aux (convert_nnf_ext \<beta>) k) = set (LP_mltl_aux \<beta> k)"
        by (metis \<beta>_nnf convert_nnf_ext_convert_nnf_ext)
      (* Top-level case split on structure of \<psi>1 *)
      {
        assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>1 "
        then obtain x1 y1 where \<psi>1_is: "\<psi>1 = And_mltl_ext x1 y1" 
                     and x1y1: "(x1 \<in> set ?Dx \<and> y1 \<in> set ?Dy) "
          using And_mltl_list_member
          by (metis in_set_member)
        have x1_semantics: "semantics_mltl_ext \<pi> x1" and 
             y1_semantics: "semantics_mltl_ext \<pi> y1"
          using Suc(8) unfolding semantics_mltl_ext_def \<psi>1_is by simp_all
        have \<alpha>_semantics: "semantics_mltl_ext \<pi> \<alpha>" using LP_mltl_aux_language_union_converse
          by (metis \<alpha>_wpd \<alpha>_is_comp \<alpha>_iwd \<alpha>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x1_semantics x1y1)
        have \<beta>_semantics: "semantics_mltl_ext \<pi> \<beta>" using LP_mltl_aux_language_union_converse
          by (metis \<beta>_wpd \<beta>_is_comp \<beta>_iwd \<beta>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x1y1 y1_semantics)
        (* Inner case split on \<psi>2*)
        {
          assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 "
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                       and x2y2: "(x2 \<in> set ?Dx \<and> y2 \<in> set ?Dy) "
            using And_mltl_list_member
            by (metis in_set_member)
          have x2_semantics: "semantics_mltl_ext \<pi> x2" and 
               y2_semantics: "semantics_mltl_ext \<pi> y2"
            using Suc(9) unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
          have xs_ys_eo: "x1 \<noteq> x2 \<or> y1 \<noteq> y2"
            using x1y1 x2y2 Suc(7) \<psi>1_is \<psi>2_is by blast
          have xs_neq: "x1 \<noteq> x2 \<Longrightarrow> False" 
            using Suc(1)[OF \<alpha>_iwd \<alpha>_nnf \<alpha>_is_comp \<alpha>_wpd \<alpha>_conv_same, of x1 x2] 
            using x1y1 x2y2 x1_semantics x2_semantics by blast
          have ys_neq: "y1 \<noteq> y2 \<Longrightarrow> False"
            using Suc(1)[OF \<beta>_iwd \<beta>_nnf \<beta>_is_comp \<beta>_wpd \<beta>_conv_same, of y1 y2]
            using x1y1 x2y2 y1_semantics y2_semantics by blast
          have ?thesis
            using xs_neq ys_neq xs_ys_eo by blast
        } moreover {
          assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                       and x2y2: "(x2 = Not\<^sub>c \<alpha> \<and> y2 \<in> set ?Dy)"
            using And_mltl_list_member
            by (metis member_def member_rec(1) member_rec(2))
          have x2_is: "x2 = Not\<^sub>c \<alpha>"
            using x2y2 by auto
          have x2_semantics: "semantics_mltl_ext \<pi> x2" and 
               y2_semantics: "semantics_mltl_ext \<pi> y2"
            using Suc(9) unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
          have xs_ys_eo: "x1 \<noteq> x2 \<or> y1 \<noteq> y2"
            using x1y1 x2y2 Suc(7) \<psi>1_is \<psi>2_is by blast
          have ?thesis
            using \<alpha>_semantics x2_semantics unfolding x2_is semantics_mltl_ext_def
            by simp
        } moreover {
          assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                       and x2y2: "(x2 \<in> set ?Dx \<and> y2 = Not\<^sub>c \<beta>)"
            using And_mltl_list_member
            by (metis member_def member_rec(1) member_rec(2))
          have y2_is: "y2 = Not\<^sub>c \<beta>"
            using x2y2 by auto
          have x2_semantics: "semantics_mltl_ext \<pi> x2" and 
               y2_semantics: "semantics_mltl_ext \<pi> y2"
            using Suc(9) unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
          have xs_ys_eo: "x1 \<noteq> x2 \<or> y1 \<noteq> y2"
            using x1y1 x2y2 Suc(7) \<psi>1_is \<psi>2_is by blast
          have ?thesis
            using \<beta>_semantics y2_semantics unfolding y2_is semantics_mltl_ext_def
            by simp
        }      
        ultimately have ?thesis
          using \<psi>2_eo by argo
      } moreover {
        assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>1"
        then obtain x1 y1 where \<psi>1_is: "\<psi>1 = And_mltl_ext x1 y1" 
                     and x1y1: "(x1 = Not\<^sub>c \<alpha> \<and> y1 \<in> set ?Dy)"
          using And_mltl_list_member
          by (metis member_def member_rec(1) member_rec(2))
        have x1_semantics: "semantics_mltl_ext \<pi> x1" and 
             y1_semantics: "semantics_mltl_ext \<pi> y1"
          using Suc(8) unfolding semantics_mltl_ext_def \<psi>1_is by simp_all
        have x1_is: "x1 = Not\<^sub>c \<alpha>"
            using x1y1 by auto
        have not_\<alpha>_semantics: "\<not>semantics_mltl_ext \<pi> \<alpha>"
          using x1y1 x1_semantics unfolding semantics_mltl_ext_def by auto
        have \<beta>_semantics: "semantics_mltl_ext \<pi> \<beta>" using LP_mltl_aux_language_union_converse
          by (metis \<beta>_wpd \<beta>_is_comp \<beta>_iwd \<beta>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x1y1 y1_semantics)
        (* Inner case split on \<psi>2*)
        {
          assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 "
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                       and x2y2: "(x2 \<in> set ?Dx \<and> y2 \<in> set ?Dy) "
            using And_mltl_list_member
            by (metis in_set_member)
          have x1_semantics: "semantics_mltl_ext \<pi> x2" 
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps by simp
          have "semantics_mltl_ext \<pi> \<alpha>"
            using LP_mltl_aux_language_union_converse
            by (metis \<alpha>_wpd \<alpha>_is_comp \<alpha>_iwd \<alpha>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x1_semantics x2y2)
          then have ?thesis using not_\<alpha>_semantics by blast
        } moreover {
          assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                           and x2y2: "(x2 = Not\<^sub>c \<alpha> \<and> y2 \<in> set ?Dy)"
            using And_mltl_list_member
            by (metis member_def member_rec(1) member_rec(2))
            (* Modify the first case *)
          have y2_semantics: "semantics_mltl_ext \<pi> y2" 
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps by simp
          have ys_neq: "y1 \<noteq> y2"
            using x1y1 x2y2 Suc(7) \<psi>1_is \<psi>2_is by blast
          then have ?thesis
            using Suc(1)
            using \<beta>_wpd \<beta>_conv_same \<beta>_is_comp \<beta>_iwd \<beta>_nnf x1y1 x2y2 y1_semantics y2_semantics by blast 
        } moreover {
          assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                       and x2y2: "(x2 \<in> set ?Dx \<and> y2 = Not\<^sub>c \<beta>)"
            using And_mltl_list_member
            by (metis member_def member_rec(1) member_rec(2))
          have x2_semantics: "semantics_mltl_ext \<pi> x2" 
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps by simp 
          have ?thesis
            by (metis LP_mltl_aux_language_union_converse \<alpha>_wpd \<alpha>_is_comp \<alpha>_iwd \<alpha>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext not_\<alpha>_semantics x2_semantics x2y2)
        }      
        ultimately have ?thesis
          using \<psi>2_eo by argo
      } moreover {
        assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>1"
        then obtain x1 y1 where \<psi>1_is: "\<psi>1 = And_mltl_ext x1 y1" 
                   and x1y1: "(x1 \<in> set ?Dx \<and> y1 = Not\<^sub>c \<beta>)"
          using And_mltl_list_member
          by (metis member_def member_rec(1) member_rec(2)) 
        have x1_semantics: "semantics_mltl_ext \<pi> x1" and 
             y1_semantics: "semantics_mltl_ext \<pi> y1"
          using Suc(8) unfolding semantics_mltl_ext_def \<psi>1_is by simp_all
        have x1_is: "y1 = Not\<^sub>c \<beta>"
            using x1y1 by auto
        have not_\<beta>_semantics: "\<not>semantics_mltl_ext \<pi> \<beta>"
          using x1y1 y1_semantics unfolding semantics_mltl_ext_def by auto
        have \<alpha>_semantics: "semantics_mltl_ext \<pi> \<alpha>" using LP_mltl_aux_language_union_converse
          by (metis \<alpha>_wpd \<alpha>_is_comp \<alpha>_iwd \<alpha>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x1_semantics x1y1)
      (* Inner case split on \<psi>2*)
        {
          assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                            and x2y2: "(x2 \<in> set ?Dx \<and> y2 \<in> set ?Dy) "
            using And_mltl_list_member
            by (metis in_set_member)
          have "semantics_mltl_ext \<pi> y2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps by auto
          then have \<beta>_semantics: "semantics_mltl_ext \<pi> \<beta>"
            using LP_mltl_aux_language_union_converse
            by (metis \<beta>_wpd \<beta>_is_comp \<beta>_iwd \<beta>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x2y2)
          then have ?thesis
            by (simp add: not_\<beta>_semantics)
        } moreover {
          assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                         and x2y2: "(x2 = Not\<^sub>c \<alpha> \<and> y2 \<in> set ?Dy)"
            using And_mltl_list_member
            by (metis member_def member_rec(1) member_rec(2))
          have "semantics_mltl_ext \<pi> y2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps by auto
          then have \<beta>_semantics: "semantics_mltl_ext \<pi> \<beta>"
            using LP_mltl_aux_language_union_converse
            by (metis \<beta>_wpd \<beta>_is_comp \<beta>_iwd \<beta>_nnf allones_implies_is_composition_MLTL convert_nnf_ext_convert_nnf_ext x2y2)
          then have ?thesis
            by (simp add: not_\<beta>_semantics)
        } moreover {
          assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
          then obtain x2 y2 where \<psi>2_is: "\<psi>2 = And_mltl_ext x2 y2" 
                         and x2y2: "(x2 \<in> set ?Dx \<and> y2 = Not\<^sub>c \<beta>)"
              using And_mltl_list_member
              by (metis member_def member_rec(1) member_rec(2))
          have "semantics_mltl_ext \<pi> x2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps by auto
          then have ?thesis
            using Suc.IH Suc.prems(6) \<alpha>_wpd \<alpha>_conv_same \<alpha>_is_comp \<alpha>_iwd \<alpha>_nnf \<psi>1_is \<psi>2_is x1_semantics x1y1 x2y2 by blast 
        }      
        ultimately have ?thesis
          using \<psi>2_eo by argo
      }      
      ultimately show ?thesis 
        using \<psi>1_eo by argo
    next
      case (Future_mltl_ext a b L \<alpha>)
      have a_leq_b: "a \<le> b" and
           \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
        using Suc(2) unfolding intervals_welldef.simps Future_mltl_ext to_mltl.simps
         by simp_all
      have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Future_mltl_ext
        by (metis convert_nnf_ext.simps(6) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(5)) 
      have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
        using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
      have \<alpha>_composition_allones: "is_composition_MLTL_allones \<alpha>" and
           L_composition_allones: "is_composition_allones (b-a+1) L"
        using Future_mltl_ext Suc.prems(3) by simp_all
      have \<alpha>_composition: "is_composition_MLTL \<alpha>"
        using Future_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL by auto
      have L_composition: "is_composition (b-a+1) L"
        using Future_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL is_composition_MLTL.simps(5) by blast
      have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
        using Suc(5) unfolding Future_mltl_ext to_mltl.simps wpd_mltl.simps
        by auto
      let ?D = "LP_mltl_aux \<alpha> k"
      let ?s = "interval_times a L"
      have length_L: "1 \<le> length L"
        using composition_length_lb[OF L_composition] a_leq_b by linarith
      have length_L_allones: "length L = b-a+1"
        using L_composition_allones
        by (simp add: length_is_composition_allones) 
      have sfirst: "?s!0 = a"
        using interval_times_first by simp
      have slast: "?s!(length L) = b+1"
        using interval_times_last[OF a_leq_b L_composition] by blast
      have length_s: "length ?s = length L + 1"
        using interval_times_length by simp
      let ?front = "set (Future_mltl_list ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
      let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                              [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                              (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                    [1..<length L]))"
      have D_is: "D = ?front \<union> ?back"
        using Suc(6) unfolding Future_mltl_ext LP_mltl_aux.simps to_mltl.simps
        using \<alpha>_convert list_concat_set_union by metis
      have s1: "?s!1 = a+1"
        using interval_times_allones[OF a_leq_b L_composition_allones] length_s length_L
        by force
      have dropa_wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop a \<pi>)"
        using \<alpha>_wpd a_leq_b by simp
      {
        assume *: "\<psi>1 \<in> ?front"
        obtain x1 where \<psi>1_is: "\<psi>1 = Future_mltl_ext a a [1] x1"
                    and x1_in: "x1 \<in> set ?D"
          using * unfolding sfirst s1 Future_mltl_list.simps by auto
        have x1_semantics: "semantics_mltl_ext (drop a \<pi>) x1"
          using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by auto
        have \<alpha>_semantics: "semantics_mltl_ext (drop a \<pi>) \<alpha>"
          using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition dropa_wpd, of ?D k]
          using x1_semantics x1_in by blast
        {
          assume **: "\<psi>2 \<in> ?front"
          obtain x2 where \<psi>2_is: "\<psi>2 = Future_mltl_ext a a [1] x2"
                      and x2_in: "x2 \<in> set ?D"
            using ** unfolding sfirst s1 Future_mltl_list.simps by auto
          have x2_semantics: "semantics_mltl_ext (drop a \<pi>) x2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
          have xs_neq: "x1 \<noteq> x2"
            using Suc(7) unfolding \<psi>1_is \<psi>2_is by blast
          have ?thesis using dropa_wpd
            using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition_allones, of "drop a \<pi>" "set ?D" x1 x2]
            using xs_neq x1_in x2_in x1_semantics x2_semantics by blast
        } moreover {
          assume **: "\<psi>2 \<in> ?back"
          then obtain i where \<psi>2_is: "\<psi>2 \<in> set ((And_mltl_list
                            [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i])))"
            and i_bound: "1 \<le> i \<and> i < length L"
            by force
          have si: "?s!i = a+i"
            using interval_times_allones
            using L_composition_allones a_leq_b i_bound length_s by auto 
          have si1: "?s!(i+1) = a+i+1"
            using interval_times_allones 
            using L_composition_allones a_leq_b i_bound length_s by auto
          obtain x2 where \<psi>2_is: "\<psi>2 = And_mltl_ext (Global_mltl_ext a (a+i-1) [i] (Not\<^sub>c \<alpha>))
                                                    (Future_mltl_ext (a+i) (a+i) [1] x2)"
                      and x2_in: "x2 \<in> set ?D" 
            using \<psi>2_is si si1 sfirst by auto 
          then have ?thesis using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using i_bound \<alpha>_wpd
            by (metis \<alpha>_semantics wpd_geq_one drop_eq_Nil2 dropa_wpd eq_imp_le le_neq_implies_less length_0_conv less_nat_zero_code not_one_le_zero semantics_mltl_ext_def) 
        }
        ultimately have ?thesis
          using Suc(7) D_is by blast
      } moreover {
        assume *: "\<psi>1 \<in> ?back"
        then obtain i1 where \<psi>1_is: "\<psi>1 \<in> set ((And_mltl_list
                            [Global_mltl_ext (?s ! 0) (?s ! i1 - 1) [?s!i1 - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i1) (?s ! (i1 + 1) - 1) [?s ! (i1 + 1) - ?s ! i1])))"
            and i1_bound: "1 \<le> i1 \<and> i1 < length L"
            by force
        have si1: "?s!i1 = a+i1"
          using interval_times_allones
          using L_composition_allones a_leq_b i1_bound length_s by auto 
        have si'1: "?s!(i1+1) = a+i1+1"
          using interval_times_allones 
          using L_composition_allones a_leq_b i1_bound length_s by auto
        obtain x1 where \<psi>1_is: "\<psi>1 = And_mltl_ext (Global_mltl_ext a (a+i1-1) [?s!i1 - ?s!0] (Not\<^sub>c \<alpha>))
                                                  (Future_mltl_ext (a+i1) (a+i1) [1] x1)"
                    and x1_in: "x1 \<in> set ?D" 
          using \<psi>1_is si1 si'1 sfirst by auto 
        have not_\<alpha>_semantics: "\<not>semantics_mltl_ext (drop a \<pi>) \<alpha>"
          using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by auto
        {
          assume **: "\<psi>2 \<in> ?front"
          obtain x2 where \<psi>2_is: "\<psi>2 = Future_mltl_ext a a [1] x2"
                      and x2_in: "x2 \<in> set ?D"
            using ** unfolding sfirst s1 Future_mltl_list.simps by auto
          have x2_semantics: "semantics_mltl_ext (drop a \<pi>) x2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
          have \<alpha>_semantics: "semantics_mltl_ext (drop a \<pi>) \<alpha>"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition dropa_wpd, of ?D k]
            using x2_semantics x2_in by blast
          then have ?thesis using not_\<alpha>_semantics by blast
        } moreover {
          assume **: "\<psi>2 \<in> ?back"
          then obtain i2 where \<psi>2_is: "\<psi>2 \<in> set ((And_mltl_list
                            [Global_mltl_ext (?s ! 0) (?s ! i2 - 1) [?s!i2 - ?s!0] (Not\<^sub>c \<alpha>)]
                            (Future_mltl_list ?D (?s ! i2) (?s ! (i2 + 1) - 1) [?s ! (i2 + 1) - ?s ! i2])))"
            and i2_bound: "1 \<le> i2 \<and> i2 < length L"
            by force
          have si2: "?s!i2 = a+i2"
            using interval_times_allones
            using L_composition_allones a_leq_b i2_bound length_s by auto 
          have si'2: "?s!(i2+1) = a+i2+1"
            using interval_times_allones 
            using L_composition_allones a_leq_b i2_bound length_s by auto
          obtain x2 where \<psi>2_is: "\<psi>2 = And_mltl_ext (Global_mltl_ext a (a+i2-1) [?s!i2 - ?s!0] (Not\<^sub>c \<alpha>))
                                                    (Future_mltl_ext (a+i2) (a+i2) [1] x2)"
                      and x2_in: "x2 \<in> set ?D" 
            using \<psi>2_is si2 si'2 sfirst by auto
          have x1_semantics: "semantics_mltl_ext (drop (a+i1) \<pi>) x1"
            using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using i1_bound \<alpha>_wpd by auto
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i1) \<pi>)"
            using i1_bound unfolding length_L_allones 
            using a_leq_b \<alpha>_wpd by auto
          then have \<alpha>_semantics: "semantics_mltl_ext (drop (a+i1) \<pi>) \<alpha>"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop (a+i1) \<pi>" ?D k]
            using x1_semantics x1_in by blast
          have x2_semantics: "semantics_mltl_ext (drop (a+i2) \<pi>) x2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using i2_bound \<alpha>_wpd by auto
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i2) \<pi>)"
            using i2_bound unfolding length_L_allones 
            using a_leq_b \<alpha>_wpd by auto
          then have \<alpha>_semantics2: "semantics_mltl_ext (drop (a+i2) \<pi>) \<alpha>"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop (a+i2) \<pi>" ?D k]
            using x2_semantics x2_in by blast
          {
            assume i1_eq_i2: "i1 = i2"
            have wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i1) \<pi>)"
              using i1_bound \<alpha>_wpd a_leq_b unfolding length_L_allones by auto
            have "x1 \<noteq> x2"
              using i1_eq_i2 \<psi>1_is \<psi>2_is Suc(7) by blast
            then have ?thesis 
              using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition_allones, of "drop (a+i1) \<pi>" "set ?D" x1 x2]
              using x1_in x1_semantics x2_in x2_semantics wpd i1_eq_i2 by blast
          } moreover {
            assume i1_le_i2: "i1 < i2"
            then have "a \<le> a+i1 \<and> a+i1 \<le> a + i2 - 1" 
              by simp
            then have x1_semantics: "\<not>semantics_mltl_ext (drop (a+i1) \<pi>) \<alpha>"
              using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
              using i2_bound \<alpha>_wpd a_leq_b by auto
            then have ?thesis using \<alpha>_semantics by blast
          } moreover {
            assume i1_ge_i2: "i1 > i2"
            then have "a \<le> a+i2 \<and> a+i2 \<le> a + i1 - 1" 
              by simp
            then have x2_semantics: "\<not>semantics_mltl_ext (drop (a+i2) \<pi>) \<alpha>"
              using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
              using i1_bound \<alpha>_wpd a_leq_b by auto
            then have ?thesis using \<alpha>_semantics2 by blast
          }
          ultimately have ?thesis by linarith
        }
        ultimately have ?thesis
          using Suc(7) D_is by blast
      }
      ultimately show ?thesis 
        using Suc(7) D_is by blast
    next
      case (Global_mltl_ext a b L \<alpha>)
      have a_leq_b: "a \<le> b" and
           \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
        using Suc(2) unfolding intervals_welldef.simps Global_mltl_ext to_mltl.simps
         by simp_all
      have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Global_mltl_ext
        by (metis convert_nnf_ext.simps(7) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(6)) 
      have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
        using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
      have \<alpha>_composition_allones: "is_composition_MLTL_allones \<alpha>"
        using Global_mltl_ext Suc.prems(3) by simp_all
      have \<alpha>_composition: "is_composition_MLTL \<alpha>"
        using Global_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL by auto
      have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
        using Suc(5) unfolding Global_mltl_ext to_mltl.simps wpd_mltl.simps
        by auto
      let ?D = "LP_mltl_aux \<alpha> k"
      {
        assume *: "length ?D \<le> 1"
        then have D_is: "D = {Global_mltl_ext a b L \<alpha>}"
          using Suc(6) unfolding Global_mltl_ext LP_mltl_aux.simps
          using \<alpha>_convert by auto 
        then have ?thesis 
          using Suc(7) by blast
      } moreover {
        assume *: "length ?D > 1"
        then have D_is: "D = set (Global_mltl_decomp ?D a (b - a) L)"
          using Suc(6) unfolding Global_mltl_ext LP_mltl_aux.simps
          using \<alpha>_convert by auto
        obtain X1 where \<psi>1_is: "\<psi>1 = Ands_mltl_ext X1" 
                    and X1_fact: "\<forall>i<length X1. \<exists>y\<in>set (LP_mltl_aux \<alpha> k). 
                                 X1 ! i = Global_mltl_ext (a + i) (a + i) [1] y"
                    and length_X1: "length X1 = Suc (b - a)"
          using in_Global_mltl_decomp_exact_forward[OF *]
          using Suc(7) D_is by blast
        obtain X2 where \<psi>2_is: "\<psi>2 = Ands_mltl_ext X2" 
                    and X2_fact: "\<forall>i<length X2. \<exists>y\<in>set (LP_mltl_aux \<alpha> k). 
                                 X2 ! i = Global_mltl_ext (a + i) (a + i) [1] y"
                    and length_X2: "length X2 = Suc (b - a)"
          using in_Global_mltl_decomp_exact_forward[OF *]
          using Suc(7) D_is by blast
        have X1_neq_X2: "X1 \<noteq> X2"
          using Suc(7) \<psi>1_is \<psi>2_is by blast
        then have "\<exists>i < b-a+1. X1!i \<noteq> X2!i" 
          using length_X1 length_X2
          by (metis add.commute nth_equalityI plus_1_eq_Suc)
        then obtain i where i_bound: "i < b-a+1" 
                        and X1i_neq_X2i: "X1!i \<noteq> X2!i" by blast
        obtain y1 where X1i_is: "X1!i = Global_mltl_ext (a + i) (a + i) [1] y1"
                    and y1_in: "y1 \<in> set ?D"
          using X1_fact i_bound length_X1 by auto
        obtain y2 where X2i_is: "X2!i = Global_mltl_ext (a + i) (a + i) [1] y2"
                    and y2_in: "y2 \<in> set ?D"
          using X2_fact i_bound length_X2 by auto
        have y1_neq_y2: "y1 \<noteq> y2"
          using X1i_is X2i_is X1i_neq_X2i by simp
        have "semantics_mltl_ext \<pi> (X1!i)"
          using Ands_mltl_semantics[of X1 \<pi>] Suc(8) unfolding \<psi>1_is
          by (metis Suc_eq_plus1 i_bound le_add2 length_X1 nth_mem)
        then have y1_semantics: "semantics_mltl_ext (drop (a+i) \<pi>) y1"
          unfolding X1i_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using i_bound \<alpha>_wpd a_leq_b 
          by (metis Nat.add_diff_assoc Nat.le_diff_conv2 add_leD1 wpd_geq_one diff_add_inverse diff_add_inverse2 less_eq_iff_succ_less not_add_less1 order_refl)
          (*takes about 20 seconds to load*)
        have "semantics_mltl_ext \<pi> (X2!i)"
          using Ands_mltl_semantics[of X2 \<pi>] Suc(9) unfolding \<psi>2_is
          by (metis Suc_eq_plus1 i_bound le_add2 length_X2 nth_mem)
        then have y2_semantics: "semantics_mltl_ext (drop (a+i) \<pi>) y2"
          unfolding X2i_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using i_bound \<alpha>_wpd a_leq_b
          by (metis Nat.add_diff_assoc Nat.le_diff_conv2 add_leD1 wpd_geq_one diff_add_inverse diff_add_inverse2 less_eq_iff_succ_less not_add_less1 order_refl)
          (*takes about 20 seconds to load*)
        have wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a+i) \<pi>)"
          using \<alpha>_wpd i_bound a_leq_b by auto
        have ?thesis
          using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition_allones wpd, of "set ?D" y1 y2]
          using y1_in y2_in y1_semantics y2_semantics y1_neq_y2 by simp
      }
      ultimately show ?thesis by linarith
    next
      case (Until_mltl_ext \<alpha> a b L \<beta>)
      have a_leq_b: "a \<le> b" and
           \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
           \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
        using Suc(2) unfolding intervals_welldef.simps Until_mltl_ext to_mltl.simps
        by simp_all
      have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Until_mltl_ext
        by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7)) 
      have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
        using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
      have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Until_mltl_ext
        by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7)) 
      have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
        using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
      have \<alpha>_composition_allones: "is_composition_MLTL_allones \<alpha>" and
           \<beta>_composition_allones: "is_composition_MLTL_allones \<beta>" and
           L_composition_allones: "is_composition_allones (b-a+1) L"
        using Until_mltl_ext Suc.prems(3) by simp_all
      have \<alpha>_composition: "is_composition_MLTL \<alpha>"
        using Until_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL by auto
      have \<beta>_composition: "is_composition_MLTL \<beta>"
        using Until_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL is_composition_MLTL.simps(5) 
        by force
      have L_composition: "is_composition (b-a+1) L"
        using L_composition_allones allones_implies_is_composition by auto 
      have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>)-1 \<le> length \<pi>" and
           \<beta>_wpd: "b + wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
        using Suc(5) unfolding Until_mltl_ext to_mltl.simps wpd_mltl.simps
        by auto
      let ?D = "LP_mltl_aux \<beta> k"
      let ?s = "interval_times a L"
      have length_L: "1 \<le> length L"
        using composition_length_lb[OF L_composition] a_leq_b by linarith
      have length_L_allones: "length L = b-a+1"
        using L_composition_allones 
        by (simp add: length_is_composition_allones) 
      have sfirst: "?s!0 = a"
        using interval_times_first by simp
      have slast: "?s!(length L) = b+1"
        using interval_times_last[OF a_leq_b L_composition] 
        by blast
      have length_s: "length ?s = length L + 1"
        using interval_times_length by simp
      have s1: "?s ! 1 = a+1"
        using interval_times_allones
        by (metis L_composition_allones a_leq_b length_L length_s less_eq_iff_succ_less)
      let ?front = "set (Until_mltl_list \<alpha> ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
      let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                              [Global_mltl_ext
                                (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))]
                              (Until_mltl_list \<alpha> ?D (?s ! i) (?s ! (i + 1) - 1)
                                [?s ! (i + 1) - ?s ! i])) [1..<length L]))" 
      have split: "D = ?front \<union> ?back"
        using Suc(6) unfolding Until_mltl_ext LP_mltl_aux.simps
        using \<alpha>_convert \<beta>_convert list_concat_set_union  
        by metis 
      {
        assume *: "\<psi>1 \<in> ?front"
        then obtain x1 where \<psi>1_is: "\<psi>1 = Until_mltl_ext \<alpha> a a [1] x1"
                         and x1_in: "x1 \<in> set ?D"
          unfolding sfirst s1 by auto
        have x1_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x1)"
          using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by auto
        have wpd_dropa: "wpd_mltl (to_mltl \<beta>) \<le> length (drop a \<pi>)"
          using \<beta>_wpd a_leq_b by simp
        then have \<beta>_semantics: "semantics_mltl_ext (drop a \<pi>) \<beta>"
          unfolding semantics_mltl_ext_def
          using LP_mltl_aux_language_union_converse[OF \<beta>_welldef \<beta>_nnf \<beta>_composition, of "drop a \<pi>" ?D k]
          using x1_semantics x1_in unfolding semantics_mltl_ext_def by blast
        {
          assume **: "\<psi>2 \<in> ?front"
          then obtain x2 where \<psi>2_is: "\<psi>2 = Until_mltl_ext \<alpha> a a [1] x2"
                         and x2_in: "x2 \<in> set ?D"
            unfolding sfirst s1 by auto
          have x2_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
          have x1_neq_x2: "x1 \<noteq> x2"
            using Suc(7) \<psi>1_is \<psi>2_is by simp
          have ?thesis
            using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition_allones, of "drop a \<pi>" "set ?D" x1 x2]
            using x1_semantics x1_in x2_semantics x2_in x1_neq_x2
            using semantics_mltl_ext_def wpd_dropa by blast 
        } moreover {
          assume **: "\<psi>2 \<in> ?back"
          then obtain i y2 where 
              \<psi>2_is: "\<psi>2 = And_mltl_ext (Global_mltl_ext (?s!0) (?s!i-1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
                 (Until_mltl_ext \<alpha> (?s!i) (?s!(i+1)-1) [(?s!(i+1)) - (?s!i)] y2)"
          and i_bound: "1 \<le> i \<and> i < length L" 
          and y2_in: "y2 \<in> set ?D" 
            by auto
          have p: "\<not>semantics_mltl_ext (drop a \<pi>) \<beta>"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using i_bound length_L_allones
            by (metis wpd_dropa wpd_geq_one drop_all eq_imp_le le_neq_implies_less length_0_conv less_nat_zero_code not_one_le_zero sfirst) 
          have ?thesis using \<beta>_semantics p
            by metis
        }
        ultimately have ?thesis using Suc(7) split by blast
      } moreover {
        assume *: "\<psi>1 \<in> ?back"
        then obtain i1 y1 where 
            \<psi>1_is: "\<psi>1 = And_mltl_ext (Global_mltl_ext (?s!0) (?s!i1-1) [?s!i1 - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
               (Until_mltl_ext \<alpha> (?s!i1) (?s!(i1+1)-1) [(?s!(i1+1)) - (?s!i1)] y1)"
        and i1_bound: "1 \<le> i1 \<and> i1 < length L" 
        and y1_in: "y1 \<in> set ?D" 
          by auto
        have si1: "?s!i1 = a + i1"
          using interval_times_allones
          using L_composition_allones a_leq_b i1_bound length_s by auto
        have si1': "?s!(i1+1) = a+i1+1"
          using interval_times_allones
          using L_composition_allones a_leq_b i1_bound length_s by auto 
        have \<psi>1_is: "\<psi>1 = And_mltl_ext (Global_mltl_ext a (a+i1-1) [i1] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
               (Until_mltl_ext \<alpha> (a+i1) (a+i1) [1] y1)"
          using si1 si1' sfirst \<psi>1_is by auto
        have y1_semantics: "semantics_mltl_ext (drop (a+i1) \<pi>) y1"
          using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by auto
        have "wpd_mltl (to_mltl \<beta>) \<le> length (drop (a + i1) \<pi>)"
          using \<beta>_wpd i1_bound length_L_allones by auto
        then have \<beta>_semantics1: "semantics_mltl_ext (drop (a+i1) \<pi>) \<beta>"
          using LP_mltl_aux_language_union_converse[OF \<beta>_welldef \<beta>_nnf \<beta>_composition, of "drop (a+i1) \<pi>" ?D k]
          using y1_semantics y1_in by blast
        {
          assume **: "\<psi>2 \<in> ?front"
          then obtain x2 where \<psi>2_is: "\<psi>2 = Until_mltl_ext \<alpha> a a [1] x2"
                         and x2_in: "x2 \<in> set ?D"
            unfolding sfirst s1 by auto
          have x2_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
          have "wpd_mltl (to_mltl \<beta>) \<le> length (drop a \<pi>)"
            using \<beta>_wpd a_leq_b by auto
          then have \<beta>_semantics2: "semantics_mltl (drop a \<pi>) (to_mltl \<beta>)"
            using LP_mltl_aux_language_union_converse[OF \<beta>_welldef \<beta>_nnf \<beta>_composition, of "drop a \<pi>" ?D k]
            using x2_semantics x2_in unfolding semantics_mltl_ext_def
            by blast
          then have ?thesis
            using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
        } moreover {
          assume **: "\<psi>2 \<in> ?back"
          then obtain i2 y2 where 
            \<psi>2_is: "\<psi>2 = And_mltl_ext (Global_mltl_ext (?s!0) (?s!i2-1) [?s!i2 - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
               (Until_mltl_ext \<alpha> (?s!i2) (?s!(i2+1)-1) [(?s!(i2+1)) - (?s!i2)] y2)"
          and i2_bound: "1 \<le> i2 \<and> i2 < length L" 
          and y2_in: "y2 \<in> set ?D" 
            by auto
          have si2: "?s!i2 = a + i2"
            using interval_times_allones
            using L_composition_allones a_leq_b i2_bound length_s by auto
          have si2': "?s!(i2+1) = a+i2+1"
            using interval_times_allones
            using L_composition_allones a_leq_b i2_bound length_s by auto 
          have \<psi>2_is: "\<psi>2 = And_mltl_ext (Global_mltl_ext a (a+i2-1) [i2] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
                 (Until_mltl_ext \<alpha> (a+i2) (a+i2) [1] y2)"
            using si2 si2' sfirst \<psi>2_is by auto
          have y2_semantics: "semantics_mltl_ext (drop (a+i2) \<pi>) y2"
            using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
          have wpd_dropi2: "wpd_mltl (to_mltl \<beta>) \<le> length (drop (a + i2) \<pi>)"
            using \<beta>_wpd i2_bound length_L_allones by auto
          then have \<beta>_semantics2: "semantics_mltl_ext (drop (a+i2) \<pi>) \<beta>"
            using LP_mltl_aux_language_union_converse[OF \<beta>_welldef \<beta>_nnf \<beta>_composition, of "drop (a+i2) \<pi>" ?D k]
            using y2_semantics y2_in by blast
          {
            assume i1_eq_i2: "i1 = i2"
            then have y1_neq_y2: "y1 \<noteq> y2"
              using \<psi>1_is \<psi>2_is Suc(7) by blast
            then have ?thesis
              using Suc(1)[OF \<beta>_welldef \<beta>_nnf \<beta>_composition_allones, of "drop (a+i1) \<pi>" "set ?D" y1 y2]
              using wpd_dropi2 i1_eq_i2 y1_semantics y1_in y2_semantics y2_in
              by blast
          } moreover {
            assume i1_le_i2: "i1 < i2"
            then have "\<not>semantics_mltl_ext (drop (a + i1) \<pi>) \<beta>"
              using Suc(9) unfolding \<psi>2_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
              using add.assoc add_le_imp_le_diff by force
            then have ?thesis
              using \<beta>_semantics1 by blast
          } moreover {
            assume i1_ge_i2: "i1 > i2"
            then have "\<not>semantics_mltl_ext (drop (a + i2) \<pi>) \<beta>"
              using Suc(8) unfolding \<psi>1_is semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
              using add.assoc add_le_imp_le_diff by force
            then have ?thesis
              using \<beta>_semantics2 by blast
          }
          ultimately have ?thesis by linarith
        }
        ultimately have ?thesis
          using split Suc(7) by blast
      }
      ultimately show ?thesis 
        using split Suc(7) by blast
    next
      case (Release_mltl_ext \<alpha> a b L \<beta>)
      have a_leq_b: "a \<le> b" and
           \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
           \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
        using Suc(2) unfolding intervals_welldef.simps Release_mltl_ext to_mltl.simps
        by simp_all
      have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Release_mltl_ext
        by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8)) 
      have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
        using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
      have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
        using Suc(3) unfolding Release_mltl_ext
        by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8)) 
      have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
        using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
      have \<alpha>_composition_allones: "is_composition_MLTL_allones \<alpha>" and
           \<beta>_composition_allones: "is_composition_MLTL_allones \<beta>" and
           L_composition_allones: "is_composition_allones (b-a+1) L"
        using Release_mltl_ext Suc.prems(3) by simp_all
      have \<alpha>_composition: "is_composition_MLTL \<alpha>"
        using Release_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL by auto
      have \<beta>_composition: "is_composition_MLTL \<beta>" 
        using Release_mltl_ext Suc.prems(3) allones_implies_is_composition_MLTL is_composition_MLTL.simps(5) 
        by force
      have L_composition: "is_composition (b-a+1) L"
        using L_composition_allones allones_implies_is_composition by auto 
      have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>" and
           \<beta>_wpd: "b + wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
        using Suc(5) unfolding Release_mltl_ext to_mltl.simps wpd_mltl.simps
        by auto
      let ?D = "LP_mltl_aux \<alpha> k"
      let ?s = "interval_times a L"
      have length_L: "1 \<le> length L"
        using composition_length_lb[OF L_composition] a_leq_b by linarith
      have length_L_allones: "length L = b-a+1"
        using L_composition_allones 
        by (simp add: length_is_composition_allones) 
      have sfirst: "?s!0 = a"
        using interval_times_first by simp
      have slast: "?s!(length L) = b+1"
        using interval_times_last[OF a_leq_b L_composition] 
        by blast
      have length_s: "length ?s = length L + 1"
        using interval_times_length by simp
      have length_L: "length L = b-a+1"
        using length_is_composition_allones[OF L_composition_allones]
        by blast
      have s1: "?s ! 1 = a+1"
        using interval_times_allones
        using L_composition L_composition_allones a_leq_b add_gr_0 composition_length_lb length_s by auto 
      have length_\<pi>_ge_b: "length \<pi> > b"
        using \<alpha>_wpd wpd_geq_one
        by (metis One_nat_def Suc_n_not_le_n add_diff_cancel_left' add_leD1 diff_is_0_eq' le_neq_implies_less) 
      let ?front = "set [Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]"
      let ?middle = "set (Mighty_Release_mltl_list ?D \<beta> (?s ! 0) (?s ! 1 - 1)
                   [?s ! 1 - ?s ! 0])"
      let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                               [Global_mltl_ext
                                 (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                               (Mighty_Release_mltl_list ?D \<beta> (?s ! i)
                                 (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                     [1..<length L]))"
      have D_is: "D = ?front \<union> ?middle \<union> ?back"
        using Suc(6) unfolding Release_mltl_ext LP_mltl_aux.simps 
        using \<alpha>_convert list_concat_set_union
        by (metis append_assoc) 
      {
        assume *: "\<psi>1 \<in> ?front"
        then have \<psi>1: "\<psi>1 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
          by auto
        {
          assume **: "\<psi>2 \<in> ?front"
          have ?thesis using * ** Suc(7) by auto
        } moreover {
          assume **: "\<psi>2 \<in> ?middle"
          then obtain x where \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext x \<beta>
              a (?s ! 1 - 1) [?s ! 1 - a]"
                          and x_in: "x \<in> set ?D"
            using sfirst by auto
          have \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext x \<beta> a a [1]"
            using s1 \<psi>2 by simp
          have x_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x)"
            using Suc(9) unfolding \<psi>1 \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            by force
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop a \<pi>)"
            using \<alpha>_wpd a_leq_b by auto
          then have "semantics_mltl (drop a \<pi>) (to_mltl \<alpha>)"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop a \<pi>" ?D k]
            using x_semantics x_in unfolding semantics_mltl_ext_def by blast
          then have ?thesis 
            using Suc(8) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            using length_\<pi>_ge_b by auto
        } moreover {
          assume **: "\<psi>2 \<in> ?back"
          then obtain i2 where \<psi>2_in: "\<psi>2 \<in> set (And_mltl_list
                          [Global_mltl_ext
                            (interval_times a L ! 0)
                            (interval_times a L ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                          (Mighty_Release_mltl_list (LP_mltl_aux \<alpha> k) \<beta>
                            (interval_times a L ! i2)
                            (interval_times a L ! (i2 + 1) - 1)
                            [interval_times a L ! (i2 + 1) -
                             interval_times a L ! i2]))"
                          and i2_bound: "1 \<le> i2 \<and> i2 < length L"
            by force
          have si2: "?s!i2 = a+i2"
            using interval_times_allones[OF a_leq_b L_composition_allones, of i2]
            using i2_bound length_L length_s by auto
          have si2': "?s!(i2+1) = a+i2+1"
            using interval_times_allones[OF a_leq_b L_composition_allones, of "i2+1"]
            using i2_bound length_L length_s by auto
          obtain x2 where \<psi>2: "\<psi>2 = And_mltl_ext
                          (Global_mltl_ext a (a + i2 - 1) [i2] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                          (Mighty_Release_mltl_ext x2 \<beta> (a+ i2) (a+ i2) [1])"
                     and x2_in: "x2 \<in> set ?D"
            using \<psi>2_in sfirst si2 si2' by auto
          have x2_semantics: "semantics_mltl (drop (a + i2) \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            by force
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i2) \<pi>)"
            using \<alpha>_wpd a_leq_b i2_bound length_L by auto
          then have "semantics_mltl (drop (a + i2) \<pi>) (to_mltl \<alpha>)"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop (a + i2) \<pi>" ?D k]
            using x2_semantics x2_in unfolding semantics_mltl_ext_def by blast
          then have ?thesis 
            using Suc(8) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            using length_\<pi>_ge_b i2_bound length_L by auto
        }
        ultimately have ?thesis using Suc(7) D_is by blast
      } moreover {
        assume *: "\<psi>1 \<in> ?middle"
        then obtain x1 where \<psi>1: "\<psi>1 = Mighty_Release_mltl_ext x1 \<beta>
            a (?s ! 1 - 1) [?s ! 1 - a]"
                        and x1_in: "x1 \<in> set ?D"
          using sfirst by auto
        have \<psi>1: "\<psi>1 = Mighty_Release_mltl_ext x1 \<beta> a a [1]"
          using s1 \<psi>1 by simp
        have x1_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x1)"
          using Suc(8) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
          by force
        have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop a \<pi>)"
          using \<alpha>_wpd a_leq_b by auto
        then have \<alpha>_semantics: "semantics_mltl (drop a \<pi>) (to_mltl \<alpha>)"
          using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop a \<pi>" ?D k]
          using x1_semantics x1_in unfolding semantics_mltl_ext_def by blast
        {
          assume **: "\<psi>2 \<in> ?front"
          then have \<psi>2: "\<psi>2 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
            by auto
          have ?thesis
            using \<alpha>_semantics using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using a_leq_b length_\<pi>_ge_b by simp
        } moreover {
          assume **: "\<psi>2 \<in> ?middle"
          then obtain x2 where \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext x2 \<beta>
              a (?s ! 1 - 1) [?s ! 1 - a]"
                          and x2_in: "x2 \<in> set ?D"
            using sfirst by auto
          have \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext x2 \<beta> a a [1]"
            using s1 \<psi>2 by simp
          have x2_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            by force
          have x1_neq_x2: "x1 \<noteq> x2"
            using Suc(7) \<psi>1 \<psi>2 by blast
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop a \<pi>)"
            using \<alpha>_wpd a_leq_b by simp
          then have ?thesis
            using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition_allones, of "drop a \<pi>" "set ?D" x1 x2]
            using x1_neq_x2 x1_semantics x2_semantics x1_in x2_in 
            unfolding semantics_mltl_ext_def by blast
        } moreover {
          assume **: "\<psi>2 \<in> ?back"
          then obtain i2 where \<psi>2_in: "\<psi>2 \<in> set (And_mltl_list
                          [Global_mltl_ext
                            (interval_times a L ! 0)
                            (interval_times a L ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                          (Mighty_Release_mltl_list (LP_mltl_aux \<alpha> k) \<beta>
                            (interval_times a L ! i2)
                            (interval_times a L ! (i2 + 1) - 1)
                            [interval_times a L ! (i2 + 1) -
                             interval_times a L ! i2]))"
                          and i2_bound: "1 \<le> i2 \<and> i2 < length L"
            by force
          have si2: "?s!i2 = a+i2"
            using interval_times_allones[OF a_leq_b L_composition_allones, of i2]
            using i2_bound length_L length_s by auto
          have si2': "?s!(i2+1) = a+i2+1"
            using interval_times_allones[OF a_leq_b L_composition_allones, of "i2+1"]
            using i2_bound length_L length_s by auto
          obtain x2 where \<psi>2: "\<psi>2 = And_mltl_ext
                          (Global_mltl_ext a (a + i2 - 1) [i2] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                          (Mighty_Release_mltl_ext x2 \<beta> (a+ i2) (a+ i2) [1])"
                     and x2_in: "x2 \<in> set ?D"
            using \<psi>2_in sfirst si2 si2' by auto
          have x2_semantics: "semantics_mltl (drop (a + i2) \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            by force
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i2) \<pi>)"
            using \<alpha>_wpd a_leq_b i2_bound length_L by auto
          then have "semantics_mltl (drop (a + i2) \<pi>) (to_mltl \<alpha>)"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop (a + i2) \<pi>" ?D k]
            using x2_semantics x2_in unfolding semantics_mltl_ext_def by blast
          have ?thesis using \<alpha>_semantics 
            using Suc(9) unfolding \<psi>2 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            by auto
        }
        ultimately have ?thesis using Suc(7) D_is by blast
      } moreover {
        assume *: "\<psi>1 \<in> ?back"
        then obtain i1 where \<psi>1_in: "\<psi>1 \<in> set (And_mltl_list
                        [Global_mltl_ext
                          (interval_times a L ! 0)
                          (interval_times a L ! i1 - 1) [?s!i1 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                        (Mighty_Release_mltl_list (LP_mltl_aux \<alpha> k) \<beta>
                          (interval_times a L ! i1)
                          (interval_times a L ! (i1 + 1) - 1)
                          [interval_times a L ! (i1 + 1) -
                           interval_times a L ! i1]))"
                        and i1_bound: "1 \<le> i1 \<and> i1 < length L"
          by force
        have si1: "?s!i1 = a+i1"
          using interval_times_allones[OF a_leq_b L_composition_allones, of i1]
          using i1_bound length_L length_s by auto
        have si1': "?s!(i1+1) = a+i1+1"
          using interval_times_allones[OF a_leq_b L_composition_allones, of "i1+1"]
          using i1_bound length_L length_s by auto
        obtain x1 where \<psi>1: "\<psi>1 = And_mltl_ext
                        (Global_mltl_ext a (a + i1 - 1) [i1] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                        (Mighty_Release_mltl_ext x1 \<beta> (a+ i1) (a+ i1) [1])"
                   and x1_in: "x1 \<in> set ?D"
          using \<psi>1_in sfirst si1 si1' by auto
        have x1_semantics: "semantics_mltl (drop (a + i1) \<pi>) (to_mltl x1)"
          using Suc(8) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
          by force
        have complen1: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i1) \<pi>)"
          using \<alpha>_wpd a_leq_b i1_bound length_L by auto
        then have \<alpha>_semantics1: "semantics_mltl (drop (a + i1) \<pi>) (to_mltl \<alpha>)"
          using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop (a + i1) \<pi>" ?D k]
          using x1_semantics x1_in unfolding semantics_mltl_ext_def by blast
        {
          assume *: "\<psi>2 \<in> ?front"
          then have \<psi>2: "\<psi>2 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
            by auto
          have ?thesis 
            using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            using length_\<pi>_ge_b i1_bound length_L
            by (smt (verit, best) \<open>semantics_mltl (drop (a + i1) \<pi>) (to_mltl \<alpha>)\<close> diff_add_inverse diff_le_mono le_antisym le_trans less_eq_iff_succ_less less_irrefl_nat less_or_eq_imp_le nat_le_iff_add nat_le_linear) 
        } moreover {
          assume *: "\<psi>2 \<in> ?middle"
          then obtain x2 where \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext x2 \<beta>
              a (?s ! 1 - 1) [?s ! 1 - a]"
                          and x2_in: "x2 \<in> set ?D"
            using sfirst by auto
          have \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext x2 \<beta> a a [1]"
            using s1 \<psi>2 by simp
          have x2_semantics: "semantics_mltl (drop a \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            by force
          have "wpd_mltl (to_mltl \<alpha>) \<le> length (drop a \<pi>)"
            using \<alpha>_wpd a_leq_b by auto
          then have \<alpha>_semantics: "semantics_mltl (drop a \<pi>) (to_mltl \<alpha>)"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop a \<pi>" ?D k]
            using x2_semantics x2_in unfolding semantics_mltl_ext_def by blast
          have ?thesis
            using Suc(8) unfolding \<psi>1 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
            using \<alpha>_semantics by auto
        } moreover {
          assume *: "\<psi>2 \<in> ?back"
          then obtain i2 where \<psi>2_in: "\<psi>2 \<in> set (And_mltl_list
                          [Global_mltl_ext
                            (interval_times a L ! 0)
                            (interval_times a L ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                          (Mighty_Release_mltl_list (LP_mltl_aux \<alpha> k) \<beta>
                            (interval_times a L ! i2)
                            (interval_times a L ! (i2 + 1) - 1)
                            [interval_times a L ! (i2 + 1) -
                             interval_times a L ! i2]))"
                          and i2_bound: "1 \<le> i2 \<and> i2 < length L"
            by force
          have si2: "?s!i2 = a+i2"
            using interval_times_allones[OF a_leq_b L_composition_allones, of i2]
            using i2_bound length_L length_s by auto
          have si2': "?s!(i2+1) = a+i2+1"
            using interval_times_allones[OF a_leq_b L_composition_allones, of "i2+1"]
            using i2_bound length_L length_s by auto
          obtain x2 where \<psi>2: "\<psi>2 = And_mltl_ext
                          (Global_mltl_ext a (a + i2 - 1) [i2] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                          (Mighty_Release_mltl_ext x2 \<beta> (a+ i2) (a+ i2) [1])"
                     and x2_in: "x2 \<in> set ?D"
            using \<psi>2_in sfirst si2 si2' by auto
          have x2_semantics: "semantics_mltl (drop (a + i2) \<pi>) (to_mltl x2)"
            using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps Mighty_Release_mltl_ext.simps semantics_mltl.simps
            by force
          have complen2: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop (a + i2) \<pi>)"
            using \<alpha>_wpd a_leq_b i2_bound length_L by auto
          then have \<alpha>_semantics2: "semantics_mltl (drop (a + i2) \<pi>) (to_mltl \<alpha>)"
            using LP_mltl_aux_language_union_converse[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition, of "drop (a + i2) \<pi>" ?D k]
            using x2_semantics x2_in unfolding semantics_mltl_ext_def by blast
          {
            assume eq: "i1 = i2"
            then have x1_neq_x2: "x1 \<noteq> x2"
              using Suc(7) \<psi>1 \<psi>2 by blast
            have ?thesis using eq
              using Suc(1)[OF \<alpha>_welldef \<alpha>_nnf \<alpha>_composition_allones complen1, of "set ?D" x1 x2]
              using x1_in x2_in x1_semantics x2_semantics x1_neq_x2 unfolding semantics_mltl_ext_def
              by blast
          } moreover {
            assume le: "i1 < i2"
            then have "\<not>semantics_mltl (drop (a + i1) \<pi>) (to_mltl \<alpha>)"
              using Suc(9) unfolding \<psi>2 semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
              using length_\<pi>_ge_b a_leq_b by simp
            then have ?thesis
              using \<alpha>_semantics1 by blast
          } moreover {
            assume ge: "i1 > i2"
            then have "\<not>semantics_mltl (drop (a + i2) \<pi>) (to_mltl \<alpha>)"
              using Suc(8) unfolding \<psi>1 semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
              using length_\<pi>_ge_b a_leq_b by simp
            then have ?thesis
              using \<alpha>_semantics2 by blast
          }
          ultimately have ?thesis by linarith
        }
        ultimately have ?thesis using Suc(7) D_is by blast
      }
      ultimately show ?thesis using Suc(7) D_is by blast
    qed
  qed

lemma LP_mltl_language_disjoint_aux:
  fixes \<phi>::"'a mltl_ext" and \<psi>1 \<psi>2::"'a mltl_ext" and k::"nat"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes composition: "is_composition_MLTL_allones \<phi>"
  assumes D_decomp: "D = set (LP_mltl_aux \<phi> k)"
  assumes diff_formulas: "(\<psi>1 \<in> D) \<and> (\<psi>2 \<in> D) \<and> \<psi>1 \<noteq> \<psi>2"
  assumes r_wpd: "r \<ge> wpd_mltl (to_mltl \<phi>)"
  shows "(language_mltl_r (to_mltl \<psi>1) r)
       \<inter> (language_mltl_r (to_mltl \<psi>2) r) = {}"
proof-
  {
    assume contra: "(language_mltl_r (to_mltl \<psi>1) r) 
       \<inter> (language_mltl_r (to_mltl \<psi>2) r) \<noteq> {}"
    then have "\<exists>\<pi>. \<pi> \<in> (language_mltl_r (to_mltl \<psi>1) r) \<and>
                    \<pi> \<in> (language_mltl_r (to_mltl \<psi>2) r)"
      by auto
    then obtain \<pi> where in1: "\<pi> \<in> (language_mltl_r (to_mltl \<psi>1) r)"
               and in2: "\<pi> \<in> (language_mltl_r (to_mltl \<psi>2) r)"
      by blast
    have sem1: "semantics_mltl_ext \<pi> \<psi>1" and
         sem2: "semantics_mltl_ext \<pi> \<psi>2" and
         len: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
      using in1 in2 assms(6)
      unfolding language_mltl_r_def semantics_mltl_ext_def
        by simp_all 
    have "False"
      using LP_mltl_language_disjoint_aux_helper[OF assms(1-3) len assms(4, 5) sem1 sem2]
      by simp
  }
  then show ?thesis by blast
qed
  

theorem LP_mltl_language_disjoint:
  fixes \<phi>::"'a mltl_ext" and \<psi>1 \<psi>2::"'a mltl" and k::"nat"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes composition: "is_composition_MLTL_allones \<phi>"
  assumes D_decomp: "D = set (LP_mltl \<phi> k)"
  assumes diff_formulas: "(\<psi>1 \<in> D) \<and> (\<psi>2 \<in> D) \<and> \<psi>1 \<noteq> \<psi>2"
  assumes r_wpd: "r \<ge> wpd_mltl (to_mltl \<phi>)"
  shows "(language_mltl_r \<psi>1 r) \<inter> (language_mltl_r \<psi>2 r) = {}"
proof-
  let ?D = "LP_mltl_aux (convert_nnf_ext \<phi>) k"
  let ?\<phi> = "convert_nnf_ext \<phi>"
  have cond1: "intervals_welldef (to_mltl (convert_nnf_ext \<phi>))"
    using intervals_welldef
    by (metis convert_nnf_ext_to_mltl_commute nnf_intervals_welldef)
  have cond2: "\<exists>\<phi>_init. convert_nnf_ext \<phi> = convert_nnf_ext \<phi>_init"
    by blast
  have cond3: "is_composition_MLTL_allones (convert_nnf_ext \<phi>)"
    using composition
    by (simp add: intervals_welldef is_composition_allones_convert_nnf_ext) 
  have cond4: "set (LP_mltl_aux (convert_nnf_ext \<phi>) k) =
               set (LP_mltl_aux (convert_nnf_ext \<phi>) k)"
    by blast
  obtain \<psi>1' \<psi>2' where \<psi>1: "\<psi>1 = to_mltl (convert_nnf_ext \<psi>1')"
                   and \<psi>1'_in: "\<psi>1' \<in> set ?D"
                   and \<psi>2: "\<psi>2 = to_mltl (convert_nnf_ext \<psi>2')"
                   and \<psi>2'_in: "\<psi>2' \<in> set ?D"
    using D_decomp unfolding LP_mltl.simps
    using diff_formulas by auto
  have \<psi>'s_neq: "\<psi>1' \<noteq> \<psi>2'"
    using diff_formulas \<psi>1 \<psi>2 by blast
  have \<psi>1_welldef: "intervals_welldef \<psi>1"
    using assms(4) D_decomp unfolding LP_mltl.simps
    using LP_mltl_aux_intervals_welldef
    by (metis \<psi>1 \<psi>1'_in allones_implies_is_composition_MLTL composition convert_nnf_ext_to_mltl_commute intervals_welldef nnf_intervals_welldef) 
  then have \<psi>1'_welldef: "intervals_welldef (to_mltl \<psi>1')"
    using \<psi>1
    using LP_mltl_aux_intervals_welldef \<psi>1'_in allones_implies_is_composition_MLTL composition intervals_welldef by auto 
  have \<psi>2_welldef: "intervals_welldef \<psi>2"
    using assms(4) D_decomp unfolding LP_mltl.simps
    using LP_mltl_aux_intervals_welldef
    by (metis \<psi>2 \<psi>2'_in allones_implies_is_composition_MLTL composition convert_nnf_ext_to_mltl_commute intervals_welldef nnf_intervals_welldef) 
  then have \<psi>2'_welldef: "intervals_welldef (to_mltl \<psi>2')"
    using \<psi>2
    using LP_mltl_aux_intervals_welldef \<psi>2'_in allones_implies_is_composition_MLTL composition intervals_welldef by auto 
  have intersect: "language_mltl_r (to_mltl \<psi>1') r \<inter>
        language_mltl_r (to_mltl \<psi>2') r = {}"
    using LP_mltl_language_disjoint_aux[OF cond1 cond2 cond3 cond4, of \<psi>1' \<psi>2' r]
    using \<psi>1'_in \<psi>2'_in \<psi>'s_neq r_wpd
    by (metis convert_nnf_ext_preserves_wpd) 
  have "semantics_mltl \<pi> (to_mltl (convert_nnf_ext \<phi>)) = 
        semantics_mltl \<pi> (to_mltl \<phi>)" 
    if "intervals_welldef (to_mltl \<phi>)"
    for \<phi>::"'a mltl_ext" and \<pi>
    using that unfolding semantic_equiv_ext_def
    by (metis convert_nnf_ext_to_mltl_commute convert_nnf_preserves_semantics) 
  then show ?thesis using intersect
    unfolding language_mltl_r_def \<psi>1 \<psi>2 
    using \<psi>1'_welldef \<psi>2'_welldef
    by auto
qed


subsection \<open>Disjointedness Theorem (special case of k=1)\<close>

lemma LP_mltl_language_disjoint_aux_helper_k1:
  fixes \<phi> \<psi>1 \<psi>2::"'a mltl_ext" and \<pi>::"'a set list"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes tracelen: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
  assumes D_decomp: "D = set (LP_mltl_aux \<phi> (Suc 0))"
  assumes diff_formulas: "(\<psi>1 \<in> D) \<and> (\<psi>2 \<in> D) \<and> \<psi>1 \<noteq> \<psi>2"
  assumes sat1: "semantics_mltl_ext \<pi> \<psi>1"
  assumes sat2: "semantics_mltl_ext \<pi> \<psi>2"
  shows "False"
proof(cases \<phi>)
    case True_mltl_ext
    then show ?thesis using assms 
      unfolding True_mltl_ext LP_mltl.simps LP_mltl_aux.simps
      by auto
  next
    case False_mltl_ext
    then show ?thesis using assms
      unfolding False_mltl_ext LP_mltl.simps LP_mltl_aux.simps
      by auto
  next
    case (Prop_mltl_ext p)
    then show ?thesis using assms
      unfolding Prop_mltl_ext LP_mltl.simps LP_mltl_aux.simps
      by auto
  next
    case (Not_mltl_ext q)
    then have "\<exists>p. q = Prop_mltl_ext p"
      using convert_nnf_form_Not_Implies_Prop assms
      by (metis convert_nnf_ext_to_mltl_commute to_mltl.simps(4) to_mltl_prop_bijective) 
    then obtain p where "q = Prop_mltl_ext p" by blast 
    then show ?thesis
      using assms unfolding Not_mltl_ext LP_mltl.simps LP_mltl_aux.simps
      by auto
  next
    case (And_mltl_ext \<alpha> \<beta>)
    show ?thesis 
      using assms(5) unfolding And_mltl_ext LP_mltl_aux.simps 
      using assms(6) by auto
  next
    case (Or_mltl_ext \<alpha> \<beta>)
    let ?Dx = "[convert_nnf_ext \<alpha>]"
    let ?Dy = "[convert_nnf_ext \<beta>]"
    have D_is: "D = set ( And_mltl_list ?Dx ?Dy @
            And_mltl_list [Not\<^sub>c \<alpha>] ?Dy @
            And_mltl_list ?Dx [Not\<^sub>c \<beta>])"
      using assms(5) unfolding Or_mltl_ext LP_mltl_aux.simps 
      by metis
    then have \<psi>1_eo: "List.member (And_mltl_list ?Dx ?Dy) \<psi>1 \<or>
        List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>1 \<or>
         List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>1"
      using assms(6) by (simp add: member_def)
    have \<psi>2_eo: "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 \<or>
        List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2 \<or>
         List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
      using D_is assms(6) by (simp add: member_def)
    (* prove some properties of \<alpha> *)
    have \<alpha>_iwd: "intervals_welldef (to_mltl \<alpha>)"
      using assms(1) unfolding Or_mltl_ext by simp
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using assms(2) unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4))
    have \<alpha>_is_comp: "is_composition_MLTL \<alpha>"
      using assms unfolding Or_mltl_ext by simp
    have \<alpha>_wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
      using assms unfolding Or_mltl_ext by simp
    have \<alpha>_conv_same: "set (LP_mltl_aux (convert_nnf_ext \<alpha>) 1) = set (LP_mltl_aux \<alpha> 1)"
      by (metis \<alpha>_nnf convert_nnf_ext_convert_nnf_ext)
    (* prove some properties of \<beta> *)
    have \<beta>_iwd: "intervals_welldef (to_mltl \<beta>)"
      using assms unfolding Or_mltl_ext
      by simp
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using assms unfolding Or_mltl_ext
      by (metis convert_nnf_ext.simps(5) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(4))
    have \<beta>_is_comp: "is_composition_MLTL \<beta>"
      using assms unfolding Or_mltl_ext
      by simp
    have \<beta>_wpd: "wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using assms unfolding Or_mltl_ext by simp
    have \<beta>_conv_same: "set (LP_mltl_aux (convert_nnf_ext \<beta>) k) = set (LP_mltl_aux \<beta> k)"
      by (metis \<beta>_nnf convert_nnf_ext_convert_nnf_ext)
    (* Top-level case split on structure of \<psi>1 *)
    {
      assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>1 "
      then have \<psi>1_is: "\<psi>1 = And_mltl_ext \<alpha> \<beta>" 
        unfolding List.member_def 
        using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
        by (metis And_mltl_list_member \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [convert_nnf_ext \<beta>]) \<psi>1\<close> member_rec(1) member_rec(2))
      have x1_semantics: "semantics_mltl_ext \<pi> \<alpha>" and 
           y1_semantics: "semantics_mltl_ext \<pi> \<beta>"
        using assms(7) unfolding \<psi>1_is semantics_mltl_ext_def by simp_all
      {
        assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 "
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext \<alpha> \<beta>" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member_forward \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [convert_nnf_ext \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        then have ?thesis
          using \<psi>1_is assms by blast
      } moreover {
        assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2"
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [Not\<^sub>c \<alpha>] [convert_nnf_ext \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have x2_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<alpha>)" and 
             y2_semantics: "semantics_mltl_ext \<pi> \<beta>"
          using assms unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
        then have ?thesis
          using x1_semantics unfolding semantics_mltl_ext_def by simp
      } moreover {
        assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [Not\<^sub>c \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have x2_semantics: "semantics_mltl_ext \<pi> \<alpha>" and 
             y2_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<beta>)"
          using assms unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
        then have ?thesis
          using y1_semantics unfolding semantics_mltl_ext_def by simp
      }      
      ultimately have ?thesis
        using \<psi>2_eo by argo
    } moreover {
      assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>1"
      then have \<psi>1_is: "\<psi>1 = And_mltl_ext (Not\<^sub>c \<alpha>) (\<beta>)" 
        unfolding List.member_def 
        using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
        by (metis And_mltl_list_member \<open>List.member (And_mltl_list [Not\<^sub>c \<alpha>] [convert_nnf_ext \<beta>]) \<psi>1\<close> member_rec(1) member_rec(2))
      have x1_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<alpha>)" and 
           y1_semantics: "semantics_mltl_ext \<pi> (\<beta>)"
        using assms unfolding semantics_mltl_ext_def \<psi>1_is by simp_all
      (* Inner case split on \<psi>2*)
      {
        assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 "
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext \<alpha> \<beta>" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [convert_nnf_ext \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have ?thesis
          using assms(7,8) unfolding \<psi>1_is \<psi>2_is semantics_mltl_ext_def by auto
      } moreover {
        assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2"
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [Not\<^sub>c \<alpha>] [convert_nnf_ext \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have x2_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<alpha>)" and 
             y2_semantics: "semantics_mltl_ext \<pi> \<beta>"
          using assms unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
        then have ?thesis
          using \<psi>1_is \<psi>2_is assms by blast
      } moreover {
        assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [Not\<^sub>c \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have x2_semantics: "semantics_mltl_ext \<pi> \<alpha>" and 
             y2_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<beta>)"
          using assms unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
        then have ?thesis
          using y1_semantics unfolding semantics_mltl_ext_def by simp
      }      
      ultimately have ?thesis
        using \<psi>2_eo by argo
    } moreover {
      assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>1"
      then have \<psi>1_is: "\<psi>1 = And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)" 
        unfolding List.member_def 
        using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
        by (metis And_mltl_list_member \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [Not\<^sub>c \<beta>]) \<psi>1\<close> member_rec(1) member_rec(2))
      have x1_semantics: "semantics_mltl_ext \<pi> \<alpha>" and 
           y1_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<beta>)"
        using assms unfolding semantics_mltl_ext_def \<psi>1_is by simp_all
    (* Inner case split on \<psi>2*)
      {
        assume "List.member (And_mltl_list ?Dx ?Dy) \<psi>2 "
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext \<alpha> \<beta>" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member_forward \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [convert_nnf_ext \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have ?thesis
          using assms(7,8) unfolding \<psi>1_is \<psi>2_is semantics_mltl_ext_def by auto
      } moreover {
        assume " List.member (And_mltl_list [Not\<^sub>c \<alpha>] ?Dy) \<psi>2"
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [Not\<^sub>c \<alpha>] [convert_nnf_ext \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have x2_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<alpha>)" and 
             y2_semantics: "semantics_mltl_ext \<pi> \<beta>"
          using assms unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
        then have ?thesis
          using x1_semantics x2_semantics unfolding semantics_mltl_ext_def by auto
      } moreover {
        assume "List.member (And_mltl_list ?Dx [Not\<^sub>c \<beta>]) \<psi>2"
        then have \<psi>2_is: "\<psi>2 = And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)" 
          unfolding List.member_def 
          using \<alpha>_nnf \<beta>_nnf convert_nnf_ext_convert_nnf_ext
          by (metis And_mltl_list_member \<open>List.member (And_mltl_list [convert_nnf_ext \<alpha>] [Not\<^sub>c \<beta>]) \<psi>2\<close> member_rec(1) member_rec(2))
        have x2_semantics: "semantics_mltl_ext \<pi> \<alpha>" and 
             y2_semantics: "semantics_mltl_ext \<pi> (Not\<^sub>c \<beta>)"
          using assms unfolding semantics_mltl_ext_def \<psi>2_is by simp_all
        then have ?thesis
          using \<psi>1_is \<psi>2_is assms by blast
      }       
      ultimately have ?thesis
        using \<psi>2_eo by argo
    }      
    ultimately show ?thesis 
      using \<psi>1_eo by argo
  next
    case (Future_mltl_ext a b L \<alpha>)
    have a_leq_b: "a \<le> b" and
         \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
      using assms unfolding intervals_welldef.simps Future_mltl_ext to_mltl.simps
       by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using assms unfolding Future_mltl_ext
      by (metis convert_nnf_ext.simps(6) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(5)) 
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         L_composition: "is_composition (b-a+1) L"
      using Future_mltl_ext assms by simp_all
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
      using assms unfolding Future_mltl_ext to_mltl.simps wpd_mltl.simps
      by auto
    let ?D = "[\<alpha>]"
    let ?s = "interval_times a L"
    have length_L: "1 \<le> length L"
      using composition_length_lb[OF L_composition] a_leq_b by linarith
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] by blast
    have length_s: "length ?s = length L + 1"
      using interval_times_length by simp
    let ?front = "set [Future_mltl_ext (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] \<alpha>]"
    let ?back = "set (concat (map (\<lambda>i. And_mltl_list
                            [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                            [Future_mltl_ext (?s ! i) (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i] \<alpha>])
                  [1..<length L]))"
    have front_eq: "set (Future_mltl_list ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0]) = ?front"
      by simp
    have back_eq: "?back = set (concat
           (map (\<lambda>i. And_mltl_list
                       [Global_mltl_ext (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (Not\<^sub>c \<alpha>)]
                       (Future_mltl_list ?D (?s ! i) (?s ! (i + 1) - 1)
                         [?s ! (i + 1) - ?s ! i]))
             [1..<length L]))"
      by auto
    have D_is: "D = ?front \<union> ?back"
      using assms(5) unfolding Future_mltl_ext LP_mltl_aux.simps to_mltl.simps
      using list_concat_set_union unfolding \<alpha>_convert
      using front_eq back_eq
      by (metis (no_types, lifting)) 
    have dropa_wpd: "wpd_mltl (to_mltl \<alpha>) \<le> length (drop a \<pi>)"
      using \<alpha>_wpd a_leq_b by simp
    {
      assume *: "\<psi>1 \<in> ?front"
      then have \<psi>1: "\<psi>1 = Future_mltl_ext (?s!0) (?s!1-1) [?s!1 - ?s!0] \<alpha>"
        by auto
      obtain j1 where \<alpha>_semantics1: "semantics_mltl_ext (drop j1 \<pi>) \<alpha>"
                      and j1_bound: "a \<le> j1 \<and> j1 \<le> ?s!1-1"
        using assms(7) unfolding sfirst \<psi>1 semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
        by blast
      {
        assume **: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Future_mltl_ext (?s!0) (?s!1-1) [?s!1 - ?s!0] \<alpha>"
          by auto
        obtain j2 where \<alpha>_semantics_2: "semantics_mltl_ext (drop j2 \<pi>) \<alpha>"
                        and j2_bound: "a \<le> j2 \<and> j2 \<le> ?s!1-1"
          using assms(8) unfolding sfirst \<psi>2 semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
          by blast
        have ?thesis 
          using assms(6) \<psi>1 \<psi>2 by blast
      } moreover {
        assume **: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = (And_mltl_ext
                          (Global_mltl_ext (?s ! 0) (?s ! i2 - 1) [?s!i2 - ?s!0] (Not\<^sub>c \<alpha>))
                          (Future_mltl_ext (?s ! i2) (?s ! (i2 + 1) - 1) [?s ! (i2 + 1) - ?s ! i2] \<alpha>))"
          and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by force
        obtain j2 where \<alpha>_semantics2: "semantics_mltl_ext (drop j2 \<pi>) \<alpha>"
                    and j2_bound: "?s!i2 \<le> j2 \<and> j2 \<le> ?s!(i2+1)-1"
                    and global_before2: "\<forall>i. a \<le> i \<and> i \<le> ?s ! i2 - 1 \<longrightarrow>
                        \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          unfolding sfirst using \<alpha>_wpd a_leq_b by auto
        have bound1: "interval_times a L ! 1 \<le> interval_times a L ! i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 1 ?s]
          using i2_bound by force
        have ?thesis using bound1
          using \<alpha>_semantics1 global_before2 j1_bound unfolding semantics_mltl_ext_def
          by auto
      }
      ultimately have ?thesis
        using assms(6) D_is by blast
    } moreover {
      assume *: "\<psi>1 \<in> ?back"
      then obtain i1 where \<psi>1: "\<psi>1 = (And_mltl_ext
                          (Global_mltl_ext (?s ! 0) (?s ! i1 - 1) [?s!i1 - ?s!0] (Not\<^sub>c \<alpha>))
                          (Future_mltl_ext (?s ! i1) (?s ! (i1 + 1) - 1) [?s ! (i1 + 1) - ?s ! i1] \<alpha>))"
          and i1_bound: "1 \<le> i1 \<and> i1 < length L"
        by force
      have lb1: "a \<le> ?s!i1"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i1" 0 ?s]
        unfolding sfirst using i1_bound by simp
      have welldef1: "?s!i1 < ?s!(i1+1)"
        using interval_times_diff_ge[OF a_leq_b L_composition, of "i1" ?s]
        using i1_bound by blast
      have ub1: "?s!(i1+1)-1 \<le> b"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i1+1" ?s]
        using slast i1_bound
        by (metis le_diff_conv le_eq_less_or_eq less_iff_succ_less_eq) 
      obtain j1 where \<alpha>_semantics1: "semantics_mltl_ext (drop j1 \<pi>) \<alpha>"
                  and j1_bound: "?s!i1 \<le> j1 \<and> j1 \<le> ?s!(i1+1)-1"
                  and global_before1: "\<forall>i. a \<le> i \<and> i \<le> ?s ! i1 - 1 \<longrightarrow>
                      \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
        using assms(7) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        unfolding sfirst using \<alpha>_wpd a_leq_b by auto
      have bound1: "interval_times a L ! 1 \<le> interval_times a L ! i1" 
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i1" 1 ?s]
        using i1_bound by force
      {
        assume **: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Future_mltl_ext (?s!0) (?s!1-1) [?s!1 - ?s!0] \<alpha>"
          by auto
        obtain j2 where \<alpha>_semantics2: "semantics_mltl_ext (drop j2 \<pi>) \<alpha>"
                        and j2_bound: "a \<le> j2 \<and> j2 \<le> ?s!1-1"
          using assms(8) unfolding sfirst \<psi>2 semantics_mltl_ext_def semantics_mltl.simps to_mltl.simps
          by blast
        then have ?thesis 
          using global_before1 \<alpha>_semantics2 bound1 
          unfolding semantics_mltl_ext_def by auto
      } moreover {
        assume **: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = (And_mltl_ext
                          (Global_mltl_ext (?s ! 0) (?s ! i2 - 1) [?s!i2 - ?s!0] (Not\<^sub>c \<alpha>))
                          (Future_mltl_ext (?s ! i2) (?s ! (i2 + 1) - 1) [?s ! (i2 + 1) - ?s ! i2] \<alpha>))"
          and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by force
        obtain j2 where \<alpha>_semantics2: "semantics_mltl_ext (drop j2 \<pi>) \<alpha>"
                    and j2_bound: "?s!i2 \<le> j2 \<and> j2 \<le> ?s!(i2+1)-1"
                    and global_before2: "\<forall>i. a \<le> i \<and> i \<le> ?s ! i2 - 1 \<longrightarrow>
                        \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>)"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          unfolding sfirst using \<alpha>_wpd a_leq_b by auto
        have lb2: "a \<le> ?s!i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 0 ?s]
          unfolding sfirst using i2_bound by simp
        have welldef2: "?s!i2 < ?s!(i2+1)"
          using interval_times_diff_ge[OF a_leq_b L_composition, of "i2" ?s]
          using i2_bound by blast
        have ub2: "?s!(i2+1)-1 \<le> b"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i2+1" ?s]
          using slast i2_bound
          by (metis le_diff_conv le_eq_less_or_eq less_iff_succ_less_eq)
        {
          assume i1_eq_i2: "i1 = i2"
          then have ?thesis 
            using assms(6) \<psi>1 \<psi>2 by blast
        } moreover {
          assume i1_le_i2: "i1 < i2"
          then have "?s ! (i1 + 1) \<le> ?s ! i2"
            using interval_times_diff_ge_general[OF a_leq_b L_composition, of i2 "i1+1" ?s]
            using i1_bound i2_bound
            by (metis le_eq_less_or_eq less_iff_succ_less_eq)
          then have "j1 \<le> interval_times a L ! i2 - 1" 
            using j1_bound by auto
          then have ?thesis
            using \<alpha>_semantics1 global_before2 j1_bound lb1
            unfolding semantics_mltl_ext_def by simp
        } moreover {
          assume i1_ge_i2: "i1 > i2"
          then have "?s ! (i2 + 1) \<le> ?s ! i1"
            using interval_times_diff_ge_general[OF a_leq_b L_composition, of i1 "i2+1" ?s]
            using i2_bound i1_bound
            by (metis le_eq_less_or_eq less_iff_succ_less_eq)
          then have "j2 \<le> interval_times a L ! i1 - 1" 
            using j2_bound by auto
          then have ?thesis
            using \<alpha>_semantics2 global_before1 j2_bound lb2
            unfolding semantics_mltl_ext_def by simp
        }
        ultimately have ?thesis by linarith
      }
      ultimately have ?thesis
        using assms(6) D_is by blast
    }
    ultimately show ?thesis 
      using assms(6) D_is by blast
  next
    case (Global_mltl_ext a b L \<alpha>)
    have a_leq_b: "a \<le> b" and
         \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)"
      using assms unfolding intervals_welldef.simps Global_mltl_ext to_mltl.simps
       by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using assms unfolding Global_mltl_ext
      by (metis convert_nnf_ext.simps(7) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(6)) 
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_composition: "is_composition_MLTL \<alpha>"
      using Global_mltl_ext assms by simp_all
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>"
      using assms unfolding Global_mltl_ext to_mltl.simps wpd_mltl.simps
      by auto
    have D_is: "D = {Global_mltl_ext a b L \<alpha>}"
      using assms(5) unfolding Global_mltl_ext LP_mltl_aux.simps \<alpha>_convert
      by auto
    then show ?thesis
      using assms by blast
  next 
    case (Until_mltl_ext \<alpha> a b L \<beta>)
    have a_leq_b: "a \<le> b" and
         \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using assms unfolding intervals_welldef.simps Until_mltl_ext to_mltl.simps
      by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using assms unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7)) 
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using assms unfolding Until_mltl_ext
      by (metis convert_nnf_ext.simps(8) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(7)) 
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>" and
         L_composition: "is_composition (b-a+1) L"
      using Until_mltl_ext assms by simp_all
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>" and
         \<beta>_wpd: "b + wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using assms unfolding Until_mltl_ext to_mltl.simps wpd_mltl.simps
      by auto
    let ?s = "interval_times a L"
    have length_L: "1 \<le> length L"
      using composition_length_lb[OF L_composition] a_leq_b by linarith
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] 
      by blast
    have length_s: "length ?s = length L + 1"
      using interval_times_length by simp
    let ?D = "[\<beta>]"
    let ?front = "{Until_mltl_ext \<alpha> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] \<beta>}"
    let ?back = "set (map (\<lambda>i. And_mltl_ext
                            (Global_mltl_ext
                              (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
                            (Until_mltl_ext \<alpha> (?s ! i) (?s ! (i + 1) - 1)
                              [?s ! (i + 1) - ?s ! i] \<beta>)) [1..<length L])" 
    have front_eq: "?front = set (Until_mltl_list \<alpha> ?D (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
      by simp
    have back_eq: "?back = set (concat
             (map (\<lambda>i. And_mltl_list
                         [Global_mltl_ext
                           (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>))]
                         (Until_mltl_list \<alpha> ?D (?s ! i) (?s ! (i + 1) - 1)
                           [?s ! (i + 1) - ?s ! i]))
               [1..<length L]))"
      by simp
    have D_is: "D = ?front \<union> ?back"
      using assms(5) unfolding Until_mltl_ext LP_mltl_aux.simps
      using \<alpha>_convert \<beta>_convert list_concat_set_union using front_eq back_eq
      by (smt (verit) map_eq_conv) 
    {
      assume *: "\<psi>1 \<in> ?front"
      then have \<psi>1: "\<psi>1 = Until_mltl_ext \<alpha> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] \<beta>"
        by blast
      obtain j1 where j1_bound: "?s!0 \<le> j1 \<and> j1 \<le> ?s!1-1"
                  and \<beta>_semantics1: "semantics_mltl_ext (drop j1 \<pi>) \<beta>"
                  and \<alpha>_semantics1: "\<forall>j. (?s!0 \<le> j \<and> j < j1) \<longrightarrow> (semantics_mltl_ext (drop j \<pi>) \<alpha>)"
        using assms(7) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by blast
      {
        assume **: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Until_mltl_ext \<alpha> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] \<beta>"
          by blast
        obtain j2 where j2_bound: "?s!0 \<le> j2 \<and> j2 \<le> ?s!1-1"
                    and \<beta>_semantics2: "semantics_mltl_ext (drop j2 \<pi>) \<beta>"
                    and \<alpha>_semantics2: "\<forall>j. (?s!0 \<le> j \<and> j < j2) \<longrightarrow> (semantics_mltl_ext (drop j2 \<pi>) \<alpha>)"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps    
          using \<psi>1 \<psi>2 diff_formulas by blast
        have ?thesis
          using \<psi>1 \<psi>2 diff_formulas by blast
      } moreover {
        assume **: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = And_mltl_ext
                       (Global_mltl_ext (?s ! 0) (?s ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
                       (Until_mltl_ext \<alpha> (?s ! i2) (?s ! (i2 + 1) - 1) [?s ! (i2 + 1) - ?s ! i2] \<beta>)" 
                        and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by auto
        obtain j2 where j2_bound: "(?s ! i2) \<le> j2 \<and> j2 \<le> (?s ! (i2 + 1) - 1)"
                    and \<beta>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<beta>)"
                    and \<alpha>_semantics2: "(\<forall>j. interval_times a L ! i2 \<le> j \<and> j < j2 \<longrightarrow>
                             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
                    and global_before2: "\<forall>i. ?s ! 0 \<le> i \<and> i \<le> ?s ! i2 - 1 \<longrightarrow>
                           semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
                           \<not> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using \<alpha>_wpd by auto
        have bound1: "?s ! 1 \<le> ?s ! i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of i2 1 ?s]
          using i2_bound by force
        then have ?thesis 
          using \<beta>_semantics1 global_before2 j1_bound unfolding sfirst
          unfolding semantics_mltl_ext_def by auto
      }
      ultimately have ?thesis using D_is assms by blast
    } moreover {
      assume *: "\<psi>1 \<in> ?back"
      then obtain i1 where \<psi>1: "\<psi>1 = And_mltl_ext
                     (Global_mltl_ext (?s ! 0) (?s ! i1 - 1) [?s!i1 - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
                     (Until_mltl_ext \<alpha> (?s ! i1) (?s ! (i1 + 1) - 1) [?s ! (i1 + 1) - ?s ! i1] \<beta>)" 
                      and i1_bound: "1 \<le> i1 \<and> i1 < length L"
        by auto
      have lb1: "a \<le> ?s!i1"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i1" 0 ?s]
        unfolding sfirst using i1_bound by simp
      have welldef1: "?s!i1 < ?s!(i1+1)"
        using interval_times_diff_ge[OF a_leq_b L_composition, of "i1" ?s]
        using i1_bound by blast
      have ub1: "?s!(i1+1)-1 \<le> b"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i1+1" ?s]
        using slast i1_bound
        by (metis le_diff_conv le_eq_less_or_eq less_iff_succ_less_eq)
      obtain j1 where j1_bound: "(?s ! i1) \<le> j1 \<and> j1 \<le> (?s ! (i1 + 1) - 1)"
                  and \<beta>_semantics1: "semantics_mltl (drop j1 \<pi>) (to_mltl \<beta>)"
                  and \<alpha>_semantics1: "(\<forall>j. interval_times a L ! i1 \<le> j \<and> j < j1 \<longrightarrow>
                           semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
                  and global_before1: "\<forall>i. ?s ! 0 \<le> i \<and> i \<le> ?s ! i1 - 1 \<longrightarrow>
                         semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
                         \<not> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)"
        using assms(7) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        using \<alpha>_wpd by auto
      have bound1: "?s ! 1 \<le> ?s ! i1"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of i1 1 ?s]
        using i1_bound by force
      {
        assume **: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Until_mltl_ext \<alpha> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0] \<beta>"
          by blast
        have ?thesis
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps    
          unfolding sfirst
          by (smt (verit, ccfv_SIG) bound1 diff_is_0_eq' global_before1 interval_times_first le0 le_trans nat_le_linear ordered_cancel_comm_monoid_diff_class.le_diff_conv2)
      } moreover {
        assume **: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = And_mltl_ext
                       (Global_mltl_ext (?s ! 0) (?s ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext \<alpha> (Not\<^sub>c \<beta>)))
                       (Until_mltl_ext \<alpha> (?s ! i2) (?s ! (i2 + 1) - 1) [?s ! (i2 + 1) - ?s ! i2] \<beta>)" 
                        and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by auto
        have lb2: "a \<le> ?s!i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 0 ?s]
          unfolding sfirst using i2_bound by simp
        have welldef2: "?s!i2 < ?s!(i2+1)"
          using interval_times_diff_ge[OF a_leq_b L_composition, of "i2" ?s]
          using i2_bound by blast
        have ub2: "?s!(i2+1)-1 \<le> b"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i2+1" ?s]
          using slast i2_bound
          by (metis le_diff_conv le_eq_less_or_eq less_iff_succ_less_eq)
        obtain j2 where j2_bound: "(?s ! i2) \<le> j2 \<and> j2 \<le> (?s ! (i2 + 1) - 1)"
                    and \<beta>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<beta>)"
                    and \<alpha>_semantics2: "(\<forall>j. interval_times a L ! i2 \<le> j \<and> j < j2 \<longrightarrow>
                             semantics_mltl (drop j \<pi>) (to_mltl \<alpha>))"
                    and global_before2: "\<forall>i. ?s ! 0 \<le> i \<and> i \<le> ?s ! i2 - 1 \<longrightarrow>
                           semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
                           \<not> semantics_mltl (drop i \<pi>) (to_mltl \<beta>)"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using \<alpha>_wpd by auto
        {
          assume i1_eq_i2: "i1 = i2"
          then have ?thesis
            using assms(6) \<psi>1 \<psi>2 by blast
        } moreover {
          assume i1_le_i2: "i1 < i2"
          then have "?s ! (i1 + 1) \<le> ?s ! i2"
            using interval_times_diff_ge_general[OF a_leq_b L_composition, of i2 "i1+1" ?s]
            using i1_bound i2_bound
            by (metis le_eq_less_or_eq less_iff_succ_less_eq)
          then have ?thesis
            using \<beta>_semantics1 global_before2 j1_bound unfolding sfirst
            using lb1 by auto
        } moreover {
          assume i1_ge_i2: "i1 > i2"
          then have "?s ! (i2 + 1) \<le> ?s ! i1"
            using interval_times_diff_ge_general[OF a_leq_b L_composition, of i1 "i2+1" ?s]
            using i1_bound i2_bound
            by (metis le_eq_less_or_eq less_iff_succ_less_eq)
          then have ?thesis
            using \<beta>_semantics2 global_before1 j2_bound unfolding sfirst
            using lb2 by auto
        }
        ultimately have ?thesis by linarith
      }
      ultimately have ?thesis
        using D_is assms by blast
    }
    ultimately show ?thesis 
      using D_is assms by blast
  next
    case (Release_mltl_ext \<alpha> a b L \<beta>)
    have a_leq_b: "a \<le> b" and
         \<alpha>_welldef: "intervals_welldef (to_mltl \<alpha>)" and 
         \<beta>_welldef: "intervals_welldef (to_mltl \<beta>)"
      using assms unfolding intervals_welldef.simps Release_mltl_ext to_mltl.simps
      by simp_all
    have \<alpha>_nnf: "\<exists>\<phi>_init. \<alpha> = convert_nnf_ext \<phi>_init"
      using assms unfolding Release_mltl_ext
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8)) 
    have \<alpha>_convert: "convert_nnf_ext \<alpha> = \<alpha>"
      using \<alpha>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<beta>_nnf: "\<exists>\<phi>_init. \<beta> = convert_nnf_ext \<phi>_init"
      using assms unfolding Release_mltl_ext
      by (metis convert_nnf_ext.simps(9) convert_nnf_ext_convert_nnf_ext mltl_ext.inject(8)) 
    have \<beta>_convert: "convert_nnf_ext \<beta> = \<beta>"
      using \<beta>_nnf convert_nnf_ext_convert_nnf_ext by metis
    have \<alpha>_composition: "is_composition_MLTL \<alpha>" and
         \<beta>_composition: "is_composition_MLTL \<beta>" and
         L_composition: "is_composition (b-a+1) L"
      using Release_mltl_ext assms by simp_all
    have \<alpha>_wpd: "b + wpd_mltl (to_mltl \<alpha>) \<le> length \<pi>" and
         \<beta>_wpd: "b + wpd_mltl (to_mltl \<beta>) \<le> length \<pi>"
      using assms unfolding Release_mltl_ext to_mltl.simps wpd_mltl.simps
      by auto
    let ?s = "interval_times a L"
    have length_L: "1 \<le> length L"
      using composition_length_lb[OF L_composition] a_leq_b by linarith
    have sfirst: "?s!0 = a"
      using interval_times_first by simp
    have slast: "?s!(length L) = b+1"
      using interval_times_last[OF a_leq_b L_composition] 
      by blast
    have length_s: "length ?s = length L + 1"
      using interval_times_length by simp
    let ?D = "[\<alpha>]"
    let ?front = "{Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)}"
    let ?middle = "{Mighty_Release_mltl_ext \<alpha> \<beta> (?s ! 0) (?s ! 1 - 1)
                 [?s ! 1 - ?s ! 0]}"
    let ?back = "set (map (\<lambda>i. And_mltl_ext
                             (Global_mltl_ext
                               (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                             (Mighty_Release_mltl_ext \<alpha> \<beta> (?s ! i)
                               (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
                   [1..<length L])"
    have middle_eq: "?middle = set (Mighty_Release_mltl_list ?D \<beta> (?s ! 0) (?s ! 1 - 1) [?s ! 1 - ?s ! 0])"
      by simp
    have back_eq: "?back = set (concat
             (map (\<lambda>i. And_mltl_list
                         [Global_mltl_ext
                           (?s ! 0) (?s ! i - 1) [?s!i - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)]
                         (Mighty_Release_mltl_list ?D \<beta> (?s ! i)
                           (?s ! (i + 1) - 1) [?s ! (i + 1) - ?s ! i]))
               [1..<length L]))"
      by simp
    have D_is: "D = ?front \<union> ?middle \<union> ?back"
      using assms(5) unfolding Release_mltl_ext LP_mltl_aux.simps 
      using \<alpha>_convert list_concat_set_union
      using middle_eq back_eq
      by (smt (verit, ccfv_SIG) append.assoc empty_set list.simps(15) map_eq_conv)
      (*takes a few seconds to load*)
    {
      assume *: "\<psi>1 \<in> ?front"
      then have \<psi>1: "\<psi>1 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
        by auto
      have global1: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
        \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
        semantics_mltl (drop i \<pi>) (to_mltl \<beta>))"
        using assms(7) unfolding \<psi>1 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        using \<alpha>_wpd a_leq_b
        by (metis add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel dual_order.trans le_add1 not_one_le_zero order_antisym_conv wpd_geq_one) 
      {
        assume **: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
          by auto
        have global2: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
          \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
          semantics_mltl (drop i \<pi>) (to_mltl \<beta>))"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using \<alpha>_wpd a_leq_b
          by (metis add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel dual_order.trans le_add1 not_one_le_zero order_antisym_conv wpd_geq_one) 
        have ?thesis using * ** assms by auto
      } moreover {
        assume **: "\<psi>2 \<in> ?middle"
        then have \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext \<alpha> \<beta> (?s ! 0)
          (?s ! 1 - 1) [?s ! 1 - ?s ! 0]"
          by blast
        obtain j2 where j2_bound: "(?s ! 0 \<le> j2 \<and> j2 \<le> ?s ! 1 - 1)"
                    and \<alpha>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<alpha>)"
          using assms(8) unfolding \<psi>2 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by blast
        have bound1: "interval_times a L ! 1 - 1 \<le> b"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" 1 ?s]
          using slast length_L by force
        then have ?thesis using \<alpha>_semantics2 global1 j2_bound unfolding sfirst
          by simp
      } moreover {
        assume **: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = And_mltl_ext
                       (Global_mltl_ext
                         (interval_times a L ! 0) (interval_times a L ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                       (Mighty_Release_mltl_ext \<alpha> \<beta> (interval_times a L ! i2)
                         (interval_times a L ! (i2 + 1) - 1)
                         [interval_times a L ! (i2 + 1) - interval_times a L ! i2])"
                        and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by auto
        obtain j2 where j2_bound: "((?s ! i2) \<le> j2 \<and> j2 \<le> ?s ! (i2 + 1) - 1)"
                    and \<alpha>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<alpha>)"
          using assms(8) unfolding \<psi>2 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by blast
        have lb2: "a \<le> ?s!i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 0 ?s]
          unfolding sfirst using i2_bound by simp
        have welldef2: "?s!i2 < ?s!(i2+1)"
          using interval_times_diff_ge[OF a_leq_b L_composition, of "i2" ?s]
          using i2_bound by blast
        have ub2: "interval_times a L ! (i2 + 1) - 1 \<le> b"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i2+1" ?s]
          using slast i2_bound
          by (metis add.commute diff_diff_left diff_is_0_eq le_neq_implies_less less_iff_succ_less_eq less_or_eq_imp_le) 
        have ?thesis using \<alpha>_semantics2 global1 j2_bound 
          unfolding sfirst using lb2 ub2 by simp
      }
      ultimately have ?thesis using assms D_is by blast
    } moreover {
      assume *: "\<psi>1 \<in> ?middle"
      then have \<psi>1: "\<psi>1 = Mighty_Release_mltl_ext \<alpha> \<beta> (?s ! 0)
        (?s ! 1 - 1) [?s ! 1 - ?s ! 0]"
        by blast
      obtain j1 where j1_bound: "(?s ! 0 \<le> j1 \<and> j1 \<le> ?s ! 1 - 1)"
                  and \<alpha>_semantics1: "semantics_mltl (drop j1 \<pi>) (to_mltl \<alpha>)"
        using assms(7) unfolding \<psi>1 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        by blast
      have bound1: "interval_times a L ! 1 - 1 \<le> b"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" 1 ?s]
        using slast length_L by force
      {
        assume **: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
          by auto
        have global2: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
          \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
          semantics_mltl (drop i \<pi>) (to_mltl \<beta>))"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using \<alpha>_wpd a_leq_b
          by (metis add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel dual_order.trans le_add1 not_one_le_zero order_antisym_conv wpd_geq_one) 
        have ?thesis
          using global2 \<alpha>_semantics1 j1_bound unfolding sfirst using bound1 by simp
      } moreover {
        assume **: "\<psi>2 \<in> ?middle"
        then have \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext \<alpha> \<beta> (?s ! 0)
          (?s ! 1 - 1) [?s ! 1 - ?s ! 0]"
          by blast
        then have ?thesis using \<psi>1 assms by blast
      } moreover {
        assume **: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = And_mltl_ext
                       (Global_mltl_ext
                         (interval_times a L ! 0) (interval_times a L ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                       (Mighty_Release_mltl_ext \<alpha> \<beta> (interval_times a L ! i2)
                         (interval_times a L ! (i2 + 1) - 1)
                         [interval_times a L ! (i2 + 1) - interval_times a L ! i2])"
                        and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by auto
        obtain j2 where j2_bound: "((?s ! i2) \<le> j2 \<and> j2 \<le> ?s ! (i2 + 1) - 1)"
                    and \<alpha>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<alpha>)"
                    and global_before2: "\<forall>i. interval_times a L ! 0 \<le> i \<and> i \<le> interval_times a L ! i2 - 1 \<longrightarrow>
         \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
         semantics_mltl (drop i \<pi>) (to_mltl \<beta>)"
          using assms(8) unfolding \<psi>2 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          unfolding sfirst using \<alpha>_wpd by auto
        have lb2: "a \<le> ?s!i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 0 ?s]
          unfolding sfirst using i2_bound by simp
        have welldef2: "?s!i2 < ?s!(i2+1)"
          using interval_times_diff_ge[OF a_leq_b L_composition, of "i2" ?s]
          using i2_bound by blast
        have ub2: "interval_times a L ! (i2 + 1) - 1 \<le> b"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i2+1" ?s]
          using slast i2_bound
          by (metis add.commute diff_diff_left diff_is_0_eq le_neq_implies_less less_iff_succ_less_eq less_or_eq_imp_le) 
        have bound1: "interval_times a L ! 1 \<le> interval_times a L ! i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 1 ?s]
          using i2_bound by force
        have ?thesis using global_before2 \<alpha>_semantics1 bound1
          using j1_bound unfolding sfirst by auto
      }
      ultimately have ?thesis using assms D_is by blast
    } moreover {
      assume *: "\<psi>1 \<in> ?back"
      then obtain i1 where \<psi>1: "\<psi>1 = And_mltl_ext
                     (Global_mltl_ext
                       (interval_times a L ! 0) (interval_times a L ! i1 - 1) [?s!i1 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                     (Mighty_Release_mltl_ext \<alpha> \<beta> (interval_times a L ! i1)
                       (interval_times a L ! (i1 + 1) - 1)
                       [interval_times a L ! (i1 + 1) - interval_times a L ! i1])"
                      and i1_bound: "1 \<le> i1 \<and> i1 < length L"
        by auto
      obtain j1 where j1_bound: "((?s ! i1) \<le> j1 \<and> j1 \<le> ?s ! (i1 + 1) - 1)"
                  and \<alpha>_semantics1: "semantics_mltl (drop j1 \<pi>) (to_mltl \<alpha>)"
                  and global_before1: "\<forall>i. interval_times a L ! 0 \<le> i \<and> i \<le> interval_times a L ! i1 - 1 \<longrightarrow>
       \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
       semantics_mltl (drop i \<pi>) (to_mltl \<beta>)"
        using assms(7) unfolding \<psi>1 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
        unfolding sfirst using \<alpha>_wpd by auto
      have lb1: "a \<le> ?s!i1"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i1" 0 ?s]
        unfolding sfirst using i1_bound by simp
      have welldef1: "?s!i1 < ?s!(i1+1)"
        using interval_times_diff_ge[OF a_leq_b L_composition, of "i1" ?s]
        using i1_bound by blast
      have ub1: "interval_times a L ! (i1 + 1) - 1 \<le> b"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i1+1" ?s]
        using slast i1_bound
        by (metis add.commute diff_diff_left diff_is_0_eq le_neq_implies_less less_iff_succ_less_eq less_or_eq_imp_le) 
      have bound1: "interval_times a L ! 1 \<le> interval_times a L ! i1"
        using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i1" 1 ?s]
        using i1_bound by force
      {
        assume *: "\<psi>2 \<in> ?front"
        then have \<psi>2: "\<psi>2 = Global_mltl_ext a b L (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>)"
          by auto
        have global2: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
          \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
          semantics_mltl (drop i \<pi>) (to_mltl \<beta>))"
          using assms(8) unfolding \<psi>2 semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          using \<alpha>_wpd a_leq_b
          by (metis add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel dual_order.trans le_add1 not_one_le_zero order_antisym_conv wpd_geq_one) 
        have ?thesis using \<alpha>_semantics1 global2 j1_bound 
          unfolding sfirst using lb1 ub1 by simp
      } moreover {
        assume *: "\<psi>2 \<in> ?middle"
        then have \<psi>2: "\<psi>2 = Mighty_Release_mltl_ext \<alpha> \<beta> (?s ! 0)
          (?s ! 1 - 1) [?s ! 1 - ?s ! 0]"
          by blast
        obtain j2 where j2_bound: "(?s ! 0 \<le> j2 \<and> j2 \<le> ?s ! 1 - 1)"
                    and \<alpha>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<alpha>)"
          using assms(8) unfolding \<psi>2 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          by blast
        have bound1: "interval_times a L ! 1 \<le> interval_times a L ! i1"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i1" 1 ?s]
          using i1_bound by force
        then have ?thesis
          using \<alpha>_semantics2 global_before1 
          using j2_bound unfolding sfirst by auto
      } moreover {
        assume *: "\<psi>2 \<in> ?back"
        then obtain i2 where \<psi>2: "\<psi>2 = And_mltl_ext
                       (Global_mltl_ext
                         (interval_times a L ! 0) (interval_times a L ! i2 - 1) [?s!i2 - ?s!0] (And_mltl_ext (Not\<^sub>c \<alpha>) \<beta>))
                       (Mighty_Release_mltl_ext \<alpha> \<beta> (interval_times a L ! i2)
                         (interval_times a L ! (i2 + 1) - 1)
                         [interval_times a L ! (i2 + 1) - interval_times a L ! i2])"
                        and i2_bound: "1 \<le> i2 \<and> i2 < length L"
          by auto
        obtain j2 where j2_bound: "((?s ! i2) \<le> j2 \<and> j2 \<le> ?s ! (i2 + 1) - 1)"
                    and \<alpha>_semantics2: "semantics_mltl (drop j2 \<pi>) (to_mltl \<alpha>)"
                    and global_before2: "\<forall>i. interval_times a L ! 0 \<le> i \<and> i \<le> interval_times a L ! i2 - 1 \<longrightarrow>
       \<not> semantics_mltl (drop i \<pi>) (to_mltl \<alpha>) \<and>
       semantics_mltl (drop i \<pi>) (to_mltl \<beta>)"
          using assms(8) unfolding \<psi>2 Mighty_Release_mltl_ext.simps semantics_mltl_ext_def to_mltl.simps semantics_mltl.simps
          unfolding sfirst using \<alpha>_wpd by auto
        have lb2: "a \<le> ?s!i2"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "i2" 0 ?s]
          unfolding sfirst using i2_bound by simp
        have welldef2: "?s!i2 < ?s!(i2+1)"
          using interval_times_diff_ge[OF a_leq_b L_composition, of "i2" ?s]
          using i2_bound by blast
        have ub2: "interval_times a L ! (i2 + 1) - 1 \<le> b"
          using interval_times_diff_ge_general[OF a_leq_b L_composition, of "length L" "i2+1" ?s]
          using slast i2_bound
          by (metis add.commute diff_diff_left diff_is_0_eq le_neq_implies_less less_iff_succ_less_eq less_or_eq_imp_le) 
        {
          assume eq: "i1 = i2"
          then have ?thesis
            using assms(6) \<psi>1 \<psi>2 by blast
        } moreover {
          assume le: "i1 < i2"
          then have "interval_times a L ! (i1 + 1) \<le> interval_times a L ! (i2)"
            using interval_times_diff_ge_general[OF a_leq_b L_composition, of i2 "i1+1" ?s]
            using i1_bound i2_bound
            by (metis le_eq_less_or_eq less_iff_succ_less_eq)  
          then have ?thesis
            using \<alpha>_semantics1 global_before2 j1_bound
            using lb1 unfolding sfirst by auto
        } moreover {
          assume ge: "i1 > i2"
          then have "interval_times a L ! (i2 + 1) \<le> interval_times a L ! (i1)"
            using interval_times_diff_ge_general[OF a_leq_b L_composition, of i1 "i2+1" ?s]
            using i1_bound i2_bound
            by (metis le_eq_less_or_eq less_iff_succ_less_eq)  
          then have ?thesis
            using \<alpha>_semantics2 global_before1 j2_bound
            using lb2 unfolding sfirst by auto
        }
        ultimately have ?thesis by linarith
      }
      ultimately have ?thesis using assms D_is by blast
    }
    ultimately show ?thesis using assms D_is by blast
  qed

lemma LP_mltl_language_disjoint_aux_k1:
  fixes \<phi>::"'a mltl_ext" and \<psi>1 \<psi>2::"'a mltl_ext" and k::"nat"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes is_nnf: "\<exists>\<phi>_init. \<phi> = convert_nnf_ext \<phi>_init"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes D_decomp: "D = set (LP_mltl_aux \<phi> 1)"
  assumes diff_formulas: "(\<psi>1 \<in> D) \<and> (\<psi>2 \<in> D) \<and> \<psi>1 \<noteq> \<psi>2"
  assumes r_wpd: "r \<ge> wpd_mltl (to_mltl \<phi>)"
  shows "(language_mltl_r (to_mltl \<psi>1) r)
       \<inter> (language_mltl_r (to_mltl \<psi>2) r) = {}"
proof-
  {
    assume contra: "(language_mltl_r (to_mltl \<psi>1) r) 
       \<inter> (language_mltl_r (to_mltl \<psi>2) r) \<noteq> {}"
    then have "\<exists>\<pi>. \<pi> \<in> (language_mltl_r (to_mltl \<psi>1) r) \<and>
                    \<pi> \<in> (language_mltl_r (to_mltl \<psi>2) r)"
      by auto
    then obtain \<pi> where in1: "\<pi> \<in> (language_mltl_r (to_mltl \<psi>1) r)"
               and in2: "\<pi> \<in> (language_mltl_r (to_mltl \<psi>2) r)"
      by blast
    have sem1: "semantics_mltl_ext \<pi> \<psi>1" and
         sem2: "semantics_mltl_ext \<pi> \<psi>2" and
         len: "length \<pi> \<ge> wpd_mltl (to_mltl \<phi>)"
      using in1 in2 assms(6)
      unfolding language_mltl_r_def semantics_mltl_ext_def
        by simp_all 
    have "False"
      by (metis D_decomp LP_mltl_language_disjoint_aux_helper_k1 One_nat_def composition diff_formulas intervals_welldef is_nnf len sem1 sem2) 
  }
  then show ?thesis by blast
qed

  

theorem LP_mltl_language_disjoint_k1:
  fixes \<phi>::"'a mltl_ext" and \<psi>1 \<psi>2::"'a mltl" and k::"nat"
  assumes intervals_welldef: "intervals_welldef (to_mltl \<phi>)"
  assumes composition: "is_composition_MLTL \<phi>"
  assumes D_decomp: "D = set (LP_mltl \<phi> 1)"
  assumes diff_formulas: "(\<psi>1 \<in> D) \<and> (\<psi>2 \<in> D) \<and> \<psi>1 \<noteq> \<psi>2"
  assumes r_wpd: "r \<ge> wpd_mltl (to_mltl \<phi>)"
  shows "(language_mltl_r \<psi>1 r) \<inter> (language_mltl_r \<psi>2 r) = {}"
proof-
  let ?D = "LP_mltl_aux (convert_nnf_ext \<phi>) 1"
  let ?\<phi> = "convert_nnf_ext \<phi>"
  have cond1: "intervals_welldef (to_mltl (convert_nnf_ext \<phi>))"
    using intervals_welldef
    by (metis convert_nnf_ext_to_mltl_commute nnf_intervals_welldef)
  have cond2: "\<exists>\<phi>_init. convert_nnf_ext \<phi> = convert_nnf_ext \<phi>_init"
    by blast
  have cond3: "is_composition_MLTL (convert_nnf_ext \<phi>)"
    using composition 
    by (simp add: intervals_welldef is_composition_convert_nnf_ext) 
  have cond4: "set (LP_mltl_aux (convert_nnf_ext \<phi>) 1) =
               set (LP_mltl_aux (convert_nnf_ext \<phi>) 1)"
    by blast
  obtain \<psi>1' \<psi>2' where \<psi>1: "\<psi>1 = to_mltl (convert_nnf_ext \<psi>1')"
                   and \<psi>1'_in: "\<psi>1' \<in> set ?D"
                   and \<psi>2: "\<psi>2 = to_mltl (convert_nnf_ext \<psi>2')"
                   and \<psi>2'_in: "\<psi>2' \<in> set ?D"
    using D_decomp unfolding LP_mltl.simps
    using diff_formulas by auto
  have \<psi>'s_neq: "\<psi>1' \<noteq> \<psi>2'"
    using diff_formulas \<psi>1 \<psi>2 by blast
  have \<psi>1_welldef: "intervals_welldef \<psi>1"
    using assms(4) D_decomp unfolding LP_mltl.simps
    using LP_mltl_aux_intervals_welldef
    by (metis \<psi>1 \<psi>1'_in composition convert_nnf_ext_to_mltl_commute intervals_welldef nnf_intervals_welldef) 
  then have \<psi>1'_welldef: "intervals_welldef (to_mltl \<psi>1')"
    using \<psi>1
    using LP_mltl_aux_intervals_welldef \<psi>1'_in allones_implies_is_composition_MLTL composition intervals_welldef by auto 
  have \<psi>2_welldef: "intervals_welldef \<psi>2"
    using assms(4) D_decomp unfolding LP_mltl.simps
    using LP_mltl_aux_intervals_welldef
    by (metis \<psi>2 \<psi>2'_in composition convert_nnf_ext_to_mltl_commute intervals_welldef nnf_intervals_welldef) 
  then have \<psi>2'_welldef: "intervals_welldef (to_mltl \<psi>2')"
    using \<psi>2
    using LP_mltl_aux_intervals_welldef \<psi>2'_in allones_implies_is_composition_MLTL composition intervals_welldef by auto 
  have intersect: "language_mltl_r (to_mltl \<psi>1') r \<inter>
        language_mltl_r (to_mltl \<psi>2') r = {}"
    using LP_mltl_language_disjoint_aux_k1[OF cond1 cond2 cond3 cond4, of \<psi>1' \<psi>2' r]
    using \<psi>1'_in \<psi>2'_in \<psi>'s_neq r_wpd
    by (metis convert_nnf_ext_preserves_wpd) 
  have "semantics_mltl \<pi> (to_mltl (convert_nnf_ext \<phi>)) = 
        semantics_mltl \<pi> (to_mltl \<phi>)" 
    if "intervals_welldef (to_mltl \<phi>)"
    for \<phi>::"'a mltl_ext" and \<pi>
    using that unfolding semantic_equiv_ext_def
    by (metis convert_nnf_ext_to_mltl_commute convert_nnf_preserves_semantics) 
  then show ?thesis using intersect
    unfolding language_mltl_r_def \<psi>1 \<psi>2 
    using \<psi>1'_welldef \<psi>2'_welldef
    by auto
qed

end
