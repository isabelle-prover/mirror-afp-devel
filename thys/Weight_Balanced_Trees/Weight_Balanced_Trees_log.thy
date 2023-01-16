(* Author: Tobias Nipkow *)

section \<open>Weight-Balanced Trees Have Logarithmic Height, and More\<close>

theory Weight_Balanced_Trees_log
imports
  Complex_Main
  "HOL-Library.Tree"
begin

(* FIXME add these to field_simps *)
lemmas neq0_if = less_imp_neq dual_order.strict_implies_not_eq

subsection \<open>Logarithmic Height\<close>

text \<open>The locale below is parameterized wrt to \<open>\<Delta>\<close>. The original definition of weight-balanced trees
\<^cite>\<open>"NievergeltR72" and "NievergeltR73"\<close> uses \<open>\<alpha>\<close>. The constants \<open>\<alpha>\<close> and \<open>\<Delta>\<close> are interdefinable.
Below we start from \<open>\<Delta>\<close> but derive \<open>\<alpha>\<close>-versions of theorems as well.\<close>

locale WBT0 =
fixes \<Delta> :: real
begin

fun balanced1 :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> bool" where
"balanced1 t1 t2 = (size1 t1 \<le> \<Delta> * size1 t2)"

fun wbt :: "'a tree \<Rightarrow> bool" where
"wbt Leaf = True" |
"wbt (Node l _ r) = (balanced1 l r \<and> balanced1 r l \<and> wbt l \<and> wbt r)"

end

locale WBT1 = WBT0 +
assumes Delta: "\<Delta> \<ge> 1"
begin

definition \<alpha> :: real where
"\<alpha> = 1/(\<Delta>+1)"

lemma Delta_def: "\<Delta> = 1/\<alpha> - 1"
unfolding \<alpha>_def by auto

lemma shows alpha_pos: "0 < \<alpha>" and alpha_ub: "\<alpha> \<le> 1/2"
unfolding \<alpha>_def using Delta by auto

lemma wbt_Node_alpha: "wbt (Node l x r) =
 ((let q = size1 l / (size1 l + size1 r)
   in \<alpha> \<le> q \<and> q \<le> 1 - \<alpha>) \<and>
  wbt l \<and> wbt r)"
proof -
  have "l > 0 \<Longrightarrow> r > 0 \<Longrightarrow>
    (1/(\<Delta>+1) \<le> l/(l+r) \<longleftrightarrow> r/l \<le> \<Delta>) \<and>
    (1/(\<Delta>+1) \<le> r/(l+r) \<longleftrightarrow> l/r \<le> \<Delta>) \<and>
    (l/(l+r) \<le> 1 - 1/(\<Delta>+1) \<longleftrightarrow> l/r \<le> \<Delta>) \<and>
    (r/(l+r) \<le> 1 - 1/(\<Delta>+1) \<longleftrightarrow> r/l \<le> \<Delta>)" for l r
    using Delta by (simp add: field_simps divide_le_eq)
  thus ?thesis using Delta by(auto simp: \<alpha>_def Let_def pos_divide_le_eq add_pos_pos)
qed

lemma height_size1_Delta:
  "wbt t \<Longrightarrow> (1 + 1/\<Delta>) ^ (height t) \<le> size1 t"
proof(induction  t)
  case Leaf thus ?case by simp
next
  case (Node l a r)
  let ?t = "Node l a r" let ?s = "size1 ?t" let ?d = "1 + 1/\<Delta>"
  from Node.prems(1) have 1: "size1 l * ?d \<le> ?s" and 2: "size1 r * ?d  \<le> ?s"
    using Delta by (auto simp: Let_def field_simps add_pos_pos neq0_if)
  show ?case
  proof (cases "height l \<le> height r")
    case True
    hence "?d ^ (height ?t) = ?d ^ (height r) * ?d" by(simp)
    also have "\<dots> \<le> size1 r * ?d"
      using Node.IH(2) Node.prems Delta unfolding wbt.simps
      by (smt (verit) divide_nonneg_nonneg mult_mono of_nat_0_le_iff)
    also have "\<dots> \<le> ?s" using 2 by (simp)
    finally show ?thesis .
  next
    case False
    hence "?d ^ (height ?t) = ?d ^ (height l) * ?d" by(simp)
    also have "\<dots> \<le> size1 l * ?d"
      using Node.IH(1) Node.prems Delta unfolding wbt.simps
      by (smt (verit) divide_nonneg_nonneg mult_mono of_nat_0_le_iff)
    also have "\<dots> \<le> ?s" using 1 by (simp)
    finally show ?thesis .
  qed
qed

lemma height_size1_alpha:
  "wbt t \<Longrightarrow> (1/(1-\<alpha>)) ^ (height t) \<le> size1 t"
proof(induction  t)
  case Leaf thus ?case by simp
next
  note wbt.simps[simp del] wbt_Node_alpha[simp]
  case (Node l a r)
  let ?t = "Node l a r" let ?s = "size1 ?t"
  from Node.prems(1) have 1: "size1 l / (1-\<alpha>) \<le> ?s" and 2: "size1 r / (1-\<alpha>)  \<le> ?s"
    using alpha_ub by (auto simp: Let_def field_simps add_pos_pos neq0_if)
  show ?case
  proof (cases "height l \<le> height r")
    case True
    hence "(1/(1-\<alpha>)) ^ (height ?t) = (1/(1-\<alpha>)) ^ (height r) * (1/(1-\<alpha>))" by(simp)
    also have "\<dots> \<le> size1 r * (1/(1-\<alpha>))"
      using Node.IH(2) Node.prems unfolding wbt_Node_alpha
      by (smt (verit) mult_right_mono zero_le_divide_1_iff)
    also have "\<dots> \<le> ?s" using 2 by (simp)
    finally show ?thesis .
  next
    case False
    hence "(1/(1-\<alpha>)) ^ (height ?t) = (1/(1-\<alpha>)) ^ (height l) * (1/(1-\<alpha>))" by(simp)
    also have "\<dots> \<le> size1 l * (1/(1-\<alpha>))"
      using Node.IH(1) Node.prems unfolding wbt_Node_alpha
      by (smt (verit) mult_right_mono zero_le_divide_1_iff)
    also have "\<dots> \<le> ?s" using 1 by (simp)
    finally show ?thesis .
  qed
qed

lemma height_size1_log_Delta: assumes "wbt t"
shows "height t \<le> log 2 (size1 t) / log 2 (1 + 1/\<Delta>)"
proof -
  from height_size1_Delta[OF assms]
  have "height t \<le> log (1 + 1/\<Delta>) (size1 t)"
    using Delta le_log_of_power by auto 
  also have "\<dots> = log 2 (size1 t) / log 2 (1 + 1/\<Delta>)"
    by (simp add: log_base_change)
  finally show ?thesis .
qed

lemma height_size1_log_alpha: assumes "wbt t"
shows "height t \<le> log 2 (size1 t) / log 2 (1/(1-\<alpha>))"
proof -
  from height_size1_alpha[OF assms]
  have "height t \<le> log (1/(1-\<alpha>)) (size1 t)"
    using alpha_pos alpha_ub le_log_of_power by auto 
  also have "\<dots> = log 2 (size1 t) / log 2 (1/(1-\<alpha>))"
    by (simp add: log_base_change)
  finally show ?thesis .
qed

end

subsection \<open>Every \<open>1 \<le> \<Delta> < 2\<close> Yields Exactly the Complete Trees\<close>

declare WBT0.wbt.simps [simp] WBT0.balanced1.simps [simp]

lemma wbt1_if_complete: assumes "1 \<le> \<Delta>" shows "complete t \<Longrightarrow> WBT0.wbt \<Delta> t"
apply(induction t)
 apply simp
apply (simp add: assms size1_if_complete)
done

lemma complete_if_wbt2: assumes "\<Delta> < 2" shows "WBT0.wbt \<Delta> t \<Longrightarrow> complete t"
proof(induction t)
  case Leaf
  then show ?case by simp
next
  case (Node t1 x t2)
  let ?h1 = "height t1" let ?h2 = "height t2"
  from Node have *: "complete t1 \<and> complete t2" by auto
  hence sz: "size1 t1 = 2 ^ ?h1 \<and> size1 t2 = 2 ^ ?h2"
    using size1_if_complete by blast
  show ?case
  proof (rule ccontr)
    assume "\<not> complete \<langle>t1, x, t2\<rangle>"
    hence "?h1 \<noteq> ?h2" using * by auto
    thus False
    proof (cases "?h1 < ?h2")
      case True
      hence "2 * (2::real) ^ ?h1 \<le> 2 ^ ?h2"
        by (metis Suc_leI one_le_numeral power_Suc power_increasing)
      also have "\<dots> \<le> \<Delta> * 2 ^ ?h1" using sz Node.prems by (simp)
      finally show False using \<open>\<Delta> < 2\<close> by simp
    next
      case False
      with \<open>?h1 \<noteq> ?h2\<close> have "?h2 < ?h1" by linarith
      hence "2 * (2::real) ^ ?h2 \<le> 2 ^ ?h1"
        by (metis Suc_leI one_le_numeral power_Suc power_increasing)
      also have "\<dots> \<le> \<Delta> * 2 ^ ?h2" using sz Node.prems by (simp)
      finally show False using \<open>\<Delta> < 2\<close> by simp
    qed
  qed
qed

end
