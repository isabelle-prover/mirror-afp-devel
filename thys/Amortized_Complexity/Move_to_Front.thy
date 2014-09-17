theory Move_to_Front
imports Complex_Main Inversion
begin

section "Online Algorithm Move-to-Front"

text{* It was first proved by Sleator and Tarjan~\cite{SleatorT-CACM85} that
the Move-to-Front algorithm is 2-competitive. *}

(* The core idea, not used: *)
lemma sum_telescope:
fixes f :: "nat \<Rightarrow> 'a::linordered_ab_group_add"
shows "(\<Sum>i=0..<k. f(Suc i) - f i) = f k - f 0"
by(induction k) auto

(* The version with upper bounds, used: *)
lemma potential:
fixes t :: "nat \<Rightarrow> 'a::linordered_ab_group_add" and p :: "nat \<Rightarrow> 'a"
assumes p0: "p 0 = 0" and ppos: "\<And>n. p n \<ge> 0"
and ub: "\<And>n. t n + p(n+1) - p n \<le> u n"
shows "(\<Sum>i<n. t i) \<le> (\<Sum>i<n. u i)"
proof-
  let ?a = "\<lambda>n. t n + p(n+1) - p n"
  have 1: "(\<Sum>i<n. t i) = (\<Sum>i<n. ?a i) - p(n)"
    by(induction n) (simp_all add: p0)
  thus ?thesis
    by (metis (erased, lifting) add.commute diff_add_cancel le_add_same_cancel2 order.trans ppos setsum_mono ub)
qed

abbreviation "before x xs \<equiv> {y. y < x in xs}"
abbreviation "after x xs \<equiv> {y. x < y in xs}"

lemma finite_before[simp]: "finite (before x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD1)
done

lemma finite_after[simp]: "finite (after x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD2)
done

lemma before_conv_take:
  "x : set xs \<Longrightarrow> before x xs = set(take (index xs x) xs)"
by (auto simp add: before_in_def set_take_if_index index_le_size) (metis index_take leI)

lemma card_before: "distinct xs \<Longrightarrow> x : set xs \<Longrightarrow> card (before x xs) = index xs x"
using  index_le_size[of xs x]
by(simp add: before_conv_take distinct_card[OF distinct_take] min_def)

lemma card_subset_before:
  "distinct xs \<Longrightarrow> x : set xs \<Longrightarrow> A \<subseteq> before x xs \<Longrightarrow> card(A) \<le> index xs x"
by (metis before_conv_take card_before card_mono[OF finite_set])

lemma before_Un: "set xs = set ys \<Longrightarrow> x : set xs \<Longrightarrow>
  before x ys = before x xs \<inter> before x ys Un after x xs \<inter> before x ys"
by(auto)(metis before_in_setD1 not_before_in)

lemma before_disj: "dist_perm xs ys \<Longrightarrow> x : set xs \<Longrightarrow>
  before x xs \<inter> before x ys \<inter> (after x xs \<inter> before x ys) = {}"
by auto (metis no_before_inI)

lemma phi_diff_aux:
  "card (Inv xs ys \<union>
             {(y, x) |y. y < x in xs \<and> y < x in ys} -
             {(x, y) |y. x < y in xs \<and> y < x in ys}) =
   card(Inv xs ys) + card(before x xs \<inter> before x ys)
   - int(card(after x xs \<inter> before x ys))"
  (is "card(?I \<union> ?B - ?A) = card ?I + card ?b - int(card ?a)")
proof-
  have 1: "?I \<inter> ?B = {}" by(auto simp: Inv_def) (metis no_before_inI)
  have 2: "?A \<subseteq> ?I \<union> ?B" by(auto simp: Inv_def)
  have 3: "?A \<subseteq> ?I" by(auto simp: Inv_def)
  have "int(card(?I \<union> ?B - ?A)) = int(card ?I + card ?B) - int(card ?A)"
    using  card_mono[OF _ 3]
    by(simp add: card_Un_disjoint[OF _ _ 1] card_Diff_subset[OF _ 2])
  also have "card ?B = card (fst ` ?B)" by(auto simp: card_image inj_on_def)
  also have "fst ` ?B = ?b" by force
  also have "card ?A = card (snd ` ?A)" by(auto simp: card_image inj_on_def)
  also have "snd ` ?A = ?a" by force
  finally show ?thesis .
qed


lemma foldr_swap_inv:
  "\<forall>i\<in>set sws. Suc i < length xs \<Longrightarrow>
  set (foldr swapSuc sws xs) = set xs \<and>
  size(foldr swapSuc sws xs) = size xs \<and>
  distinct(foldr swapSuc sws xs) = distinct xs"
by (induct sws arbitrary: xs) (simp_all add: swapSuc_def)

lemma card_Inv_foldr_swapSuc:
  "\<forall>i\<in>set sws. Suc i < length xs \<Longrightarrow> distinct xs \<Longrightarrow>
  card (Inv xs (foldr swapSuc sws xs)) \<le> length sws"
by(induction sws)
  (auto simp add: Inv_swap foldr_swap_inv card_insert_if card_Diff_singleton_if)

locale MTF_Off =
fixes q :: "nat \<Rightarrow> 'a"
fixes init :: "'a list"
fixes sw_off :: "nat \<Rightarrow> nat list"
assumes dist_init[simp]: "distinct init" 
assumes sw_off_size: "\<forall>i \<in> set(sw_off n). Suc i < size init"
begin

fun s_off :: "nat \<Rightarrow> 'a list" where
"s_off 0 = init" |
"s_off(Suc n) = foldr swapSuc (sw_off n) (s_off n)"

lemma length_s_off[simp]: "length(s_off n) = length init"
by (induction n) (simp_all add: foldr_swap_inv sw_off_size)

lemma dist_s_off[simp]: "distinct(s_off n)" 
by(induction n)(simp_all add: foldr_swap_inv sw_off_size)

lemma set_s_off[simp]: "set(s_off n) = set init"
by(induction n)(simp_all add: foldr_swap_inv sw_off_size)


fun s_mtf :: "nat \<Rightarrow> 'a list" where
"s_mtf 0 = init" |
"s_mtf (Suc n) = mtf (q n) (s_mtf n)"

definition t_mtf :: "nat \<Rightarrow> int" where
"t_mtf n = index (s_mtf n) (q n) + 1"

definition T_mtf :: "nat \<Rightarrow> int" where
"T_mtf n = (\<Sum>i<n. t_mtf i)"

definition c_off :: "nat \<Rightarrow> int" where
"c_off n = index (s_off n) (q n) + 1"

definition p_off :: "nat \<Rightarrow> int" where
"p_off n = size(sw_off n)"

definition t_off :: "nat \<Rightarrow> int" where
"t_off n = c_off n + p_off n"

definition T_off :: "nat \<Rightarrow> int" where
"T_off n = (\<Sum>i<n. t_off i)"

lemma length_s_mtf[simp]: "length(s_mtf n) = length init"
by (induction n) simp_all

lemma dist_s_mtf[simp]: "distinct(s_mtf n)"
apply(induction n)
apply (simp)
apply (auto simp: mtf_def index_take set_drop_if_index)
apply (metis set_drop_if_index index_take less_Suc_eq_le linear)
done

lemma set_s_mtf[simp]: "set (s_mtf n) = set init"
by (induction n) (simp_all)

lemma dperm_inv: "dist_perm (s_off n) (s_mtf n)"
by (metis dist_s_mtf dist_s_off set_s_mtf set_s_off)

definition Phi :: "nat \<Rightarrow> int" ("\<Phi>") where
"Phi n = card(Inv (s_off n) (s_mtf n))"

lemma phi0: "Phi 0 = 0"
by(simp add: Phi_def)

lemma phi_pos: "Phi n \<ge> 0"
by(simp add: Phi_def)

lemma mtf_ub: "t_mtf n + Phi (n+1) - Phi n \<le> 2 * c_off n - 1 + p_off n"
proof -
  let ?xs = "s_off n" let ?ys = "s_mtf n" let ?x = "q n"
  let ?xs' = "foldr swapSuc (sw_off n) ?xs" let ?ys' = "mtf ?x ?ys"
  show ?thesis
  proof cases
  assume xin: "?x \<in> set ?ys"
  let ?bb = "before ?x ?xs \<inter> before ?x ?ys"
  let ?ab = "after ?x ?xs \<inter> before ?x ?ys"
  have phi_diff:
    "Phi (Suc n) - Phi n \<le> card ?bb - int(card ?ab) + size(sw_off n)"
  proof -
    have "Phi (Suc n) - Phi n = card (Inv ?xs' ?ys') - int(card (Inv ?xs ?ys))"
      by(simp add: Phi_def)
    also have "int(card (Inv ?xs' ?ys')) \<le> card(Inv ?xs' ?xs) + int(card(Inv ?xs ?ys'))"
      using card_Inv_tri_ineq[of ?xs' ?xs ?ys'] xin
      by (simp add: foldr_swap_inv sw_off_size)
    also have "card(Inv ?xs' ?xs) = card(Inv ?xs ?xs')"
      by (rule card_Inv_sym)
    also have "card(Inv ?xs ?xs') \<le> size(sw_off n)"
      by (metis card_Inv_foldr_swapSuc dist_s_off sw_off_size length_s_off)
    also have "card(Inv ?xs ?ys') \<le>
        card(Inv ?xs ?ys) + card ?bb - int(card ?ab)"
      using xin by(simp add: Inv_mtf phi_diff_aux)
    finally show ?thesis by(fastforce simp: Let_def)
  qed
  have t_mtf: "t_mtf n = card ?bb + card ?ab + 1"
  proof -
    have "index ?ys ?x = card (before ?x ?ys)" using xin
      by(simp add: card_before[OF dist_s_mtf])
    also have "\<dots> = card(?bb \<union> ?ab)"
      by (metis before_Un set_s_mtf set_s_off xin)
    also have "\<dots> = card ?bb + card ?ab"
      using xin by(simp add: card_Un_disjoint before_disj dperm_inv)
    finally show ?thesis by(simp add: t_mtf_def Let_def)
  qed
  show ?thesis using xin phi_diff card_subset_before[of "s_off n" "q n" "?bb"]
    by(simp add: t_mtf c_off_def p_off_def Let_def)
  next
    assume notin: "?x \<notin> set ?ys"
    have "int (card (Inv ?xs' ?ys)) - card (Inv ?xs ?ys) \<le> card(Inv ?xs ?xs')"
      using card_Inv_tri_ineq[OF _ dperm_inv, of ?xs' n]
            foldr_swap_inv[of "sw_off n" "s_off n"] sw_off_size[of n]
      by(simp add: card_Inv_sym)
    also have "\<dots> \<le> size(sw_off n)"
      by(simp add: card_Inv_foldr_swapSuc sw_off_size dperm_inv)
    finally show ?thesis using notin
      by(simp add: t_mtf_def c_off_def p_off_def Phi_def)
  qed
qed

text{* We ignore free exchanges because they are not necessary in an offline algorithm: *}

theorem Sleator_Tarjan: "T_mtf n \<le> (\<Sum>i<n. 2*c_off i + p_off i) - n"
proof-
  have "(\<Sum>i<n. t_mtf i) \<le> (\<Sum>i<n. 2*c_off i - 1 + p_off i)"
    by(rule potential[where p=Phi,OF phi0 phi_pos mtf_ub])
  also have "\<dots> = (\<Sum>i<n. (2*c_off i + p_off i) - 1)"
    by (simp add: diff_add_eq)
  also have "\<dots> = (\<Sum>i<n. 2*c_off i + p_off i) - n"
    by(simp add: sumr_diff_mult_const2[symmetric])
  finally show ?thesis by(simp add: T_mtf_def)
qed

lemma T_off_nneg: "0 \<le> (T_off n)"
by(auto simp add: setsum_nonneg T_off_def t_off_def c_off_def p_off_def)

lemma T_mtf_ub: "\<forall>i<n. q i \<in> set init \<Longrightarrow> (T_mtf n) \<le> n * size init"
proof(induction n)
  case 0 show ?case by(simp add: T_mtf_def)
next
  case (Suc n)  thus ?case
    using index_less_size_conv[of "s_mtf n" "q n"]
      by(simp add: T_mtf_def t_mtf_def less_Suc_eq del: index_less)
qed

corollary MTF_competitive: assumes "init \<noteq> []" and "\<forall>i<n. q i \<in> set init"
shows "T_mtf n \<le> (2 - 1/(size init)) * T_off n"
proof cases
  assume 0: "real(T_off n) \<le> n * (size init)"
  have "T_mtf n \<le> 2 * T_off n - n"
  proof -
    have "T_mtf n \<le> (\<Sum>i<n. 2*c_off i + p_off i) - n" by(rule Sleator_Tarjan)
    also have "(\<Sum>i<n. 2*c_off i + p_off i) \<le> (\<Sum>i<n. 2*(c_off i + p_off i))"
      by(rule setsum_mono) (simp add: p_off_def)
    also have "\<dots> \<le> 2 * T_off n" by (simp add: setsum_right_distrib T_off_def t_off_def)
    finally show ?thesis by simp
  qed
  hence "real(T_mtf n) \<le> 2 * real(T_off n) - n" by linarith
  also have "\<dots> = 2 * real(T_off n) - (n * size init) / size init"
    using assms(1) by simp
  also have "\<dots> \<le> 2 * real(T_off n) - T_off n / size init"
    by(rule diff_left_mono[OF  divide_right_mono[OF 0]]) simp
  also have "\<dots> = (2 - 1 / size init) * T_off n" by algebra
  finally show ?thesis .
next
  assume 0: "\<not> real(T_off n) \<le> n * (size init)"
  have "2 - 1 / size init \<ge> 1" using assms(1)
    by (auto simp add: field_simps neq_Nil_conv)
  have "real (T_mtf n) \<le> n * size init" using T_mtf_ub[OF assms(2)] by linarith
  also have "\<dots> < real(T_off n)" using 0 by linarith
  also have "\<dots> \<le> (2 - 1 / size init) * T_off n" using assms(1) T_off_nneg[of n]
    by(auto simp add: mult_le_cancel_right1 field_simps neq_Nil_conv
        simp del: real_of_int_setsum)
  finally show ?thesis by linarith
qed

end

end
