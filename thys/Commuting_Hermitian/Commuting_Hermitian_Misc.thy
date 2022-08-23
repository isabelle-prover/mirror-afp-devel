(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Commuting_Hermitian_Misc imports "Jordan_Normal_Form.Matrix"

begin
section \<open>Misc\<close>

fun n_sum where
  "n_sum 0 l = 0"
| "n_sum (Suc n) l = (hd l) + (n_sum n (tl l))"

lemma n_sum_last:
  fixes l::"'a::{comm_monoid_add} list"
  assumes "i < length l"
  shows "n_sum (Suc i) l = n_sum i l + l!i" using assms
proof (induct i arbitrary:l)
  case 0
  hence "l = hd l # tl l" by simp
  then show ?case
    using "0.prems" hd_conv_nth by auto
next
  case (Suc i)
  hence "n_sum (Suc (Suc i)) l = hd l + n_sum (Suc i) (tl l)" by simp
  also have "... = hd l + n_sum i (tl l) + tl l!i" using Suc
    by (metis Groups.add_ac(1) drop_Suc drop_eq_Nil2 leD leI) 
  also have "... = n_sum (Suc i) l + tl l!i" by simp
  also have "... = n_sum (Suc i) l + l!(Suc i)"
    by (metis Suc(2) Suc_lessD hd_Cons_tl list.sel(2) nth_Cons_Suc nth_tl) 
  finally show ?case .
qed

lemma n_sum_last_lt:
  fixes l::"'a::{comm_monoid_add, ordered_cancel_ab_semigroup_add} list"
  assumes "j < l!i"
  and "i < length l"
  shows "n_sum i l + j < n_sum (Suc i) l"
proof -
  have "n_sum i l + j < n_sum i l + l!i" 
    using assms add_strict_left_mono[of j "l!i"] by simp
  also have "... = n_sum (Suc i) l" using n_sum_last[of i l] assms 
    by simp
  finally show ?thesis .
qed

lemma sum_list_tl_leq:
  assumes "sum_list l \<le> (n::nat)"
  and "l\<noteq> []"
  and "hd l \<le> n"
  shows "sum_list (tl l) \<le> n - hd l"
proof -
  have "hd l + sum_list (tl l) = sum_list l" using assms
    by (metis list.exhaust_sel sum_list_simps(2))
  also have "... \<le> n" using assms by simp
  finally have "hd l + sum_list (tl l) \<le> n" .
  thus ?thesis by simp
qed

lemma diag_mat_length:
  shows "length (diag_mat A) = dim_row A" unfolding diag_mat_def by simp

lemma sum_list_geq_tl:
  fixes l::"'a::{comm_monoid_add, ordered_ab_semigroup_add_imp_le} list"
  assumes  "l\<noteq>[]"
  and "\<forall>j < length l. 0 \<le> l!j"
shows "sum_list (tl l) \<le> sum_list l" using assms
proof (induct l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  hence "0 \<le> a"
    by (metis length_greater_0_conv nth_Cons_0)
  have "sum_list (tl (a#l)) = sum_list l" by simp
  also have "... \<le> a + sum_list l" using \<open>0 \<le> a\<close>
    by (metis add_0 add_le_cancel_right)
  also have "... = sum_list (a#l)" by simp
  finally show ?case .
qed

lemma sum_list_geq_0:
  fixes l::"'a::{comm_monoid_add, ordered_ab_semigroup_add_imp_le} list"
  assumes  "l\<noteq>[]"
  and "\<forall>j < length l. 0 \<le> l!j"
shows "0 \<le> sum_list l" using assms
proof (induct l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  hence "0 \<le> a"
    by (metis length_greater_0_conv nth_Cons_0)
  show ?case
  proof (cases "l = []")
    case True
    hence "sum_list (a#l) = a" by simp
    then show ?thesis using \<open>0 \<le> a\<close> by simp
  next
    case False
    hence "0 \<le> sum_list l" using Cons by force
    also have "... = sum_list (tl (a#l))" by simp
    also have "... \<le> sum_list (a#l)" using sum_list_geq_tl Cons by metis
    finally show ?thesis .
  qed
qed

lemma sum_list_cong:
  assumes "length l = length m"
  and "\<forall>i < length l. l!i = m!i"
shows "sum_list l = sum_list m" using assms
proof (induct l arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  hence "0 < length m" by auto
  hence "m = hd m # (tl m)" by simp
  have "sum_list (a#l) = a + sum_list l" by simp
  also have "... = hd m + sum_list l" using Cons
    by (metis \<open>0 < length m\<close> \<open>m = hd m # tl m\<close> nth_Cons_0)
  also have "... = hd m + sum_list (tl m)"
    by (metis Cons.prems(1) Cons.prems(2) \<open>m = hd m # tl m\<close> 
        calculation nth_equalityI sum_list.Cons) 
  also have "... = sum_list m"
    by (metis \<open>m = hd m # tl m\<close> sum_list.Cons)
  finally show ?case .
qed

lemma n_sum_sum_list:
  fixes l::"'a::{comm_monoid_add, ordered_ab_semigroup_add_imp_le} list"
  assumes "i \<le> length l"
  and "\<forall>j < length l. 0 \<le> l!j"
  shows "n_sum i l \<le> sum_list l" using assms
proof (induct i arbitrary: l)
  case 0
  then show ?case
    by (metis n_sum.simps(1) order.eq_iff sum_list_geq_0 sum_list_simps(1))   
next
  case (Suc i)
  hence "1 \<le> length l" by presburger
  hence "l = hd l#(tl l)"
    by (metis hd_Cons_tl list.size(3) rel_simps(45))
  have "n_sum (Suc i) l \<le> hd l + sum_list (tl l)" 
  proof -
    have "n_sum i (tl l) \<le> sum_list (tl l)"
    proof (rule Suc(1))
      show "i \<le> length (tl l)" using Suc by simp
      show "\<forall>j<length (tl l). 0 \<le> tl l ! j" using Suc
        by (metis Nitpick.size_list_simp(2) le_simps(3) nth_tl 
            verit_comp_simplify1(3) zero_less_Suc) 
    qed
    thus ?thesis by simp
  qed
  also have "... = sum_list l"
    by (metis \<open>l = hd l # tl l\<close> sum_list.Cons) 
  finally show ?case .
qed

lemma map2_commute:
  assumes "length l = length m"
  and "\<forall>i < length l. f (l!i) (m!i) = f (m!i) (l!i)"
shows "map2 f l m = map2 f m l" using assms
proof (induct l arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  hence "0 < length m" by auto
  hence "m = hd m#(tl m)" by simp
  hence "map2 f (a#l) m = f a (hd m) # (map2 f l (tl m))"
    by (metis (no_types, lifting) list.map(2) prod.simps(2) zip_Cons_Cons) 
  also have "... = f (hd m) a # (map2 f l (tl m))" using Cons
    by (metis \<open>0 < length m\<close> \<open>m = hd m # tl m\<close> nth_Cons_0)
  also have "... = f (hd m) a # (map2 f (tl m) l)" using Cons
    by (metis Suc_less_eq \<open>m = hd m # tl m\<close> length_Cons nat.simps(1) 
        nth_Cons_Suc)
  also have "... = map2 f m (a#l)"
    by (metis (no_types, lifting) Cons_eq_map_conv \<open>m = hd m # tl m\<close> 
        prod.simps(2) zip_Cons_Cons)
  finally show ?case .
qed

lemma map2_length:
  assumes "length Al = length Bl"
  shows "length (map2 f Al Bl) = length Al" using assms by simp


end