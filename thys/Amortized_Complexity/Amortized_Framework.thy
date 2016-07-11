section "Amortized Complexity Framework"

theory Amortized_Framework
imports Complex_Main
begin

text{* This theory provides a framework for amortized analysis. *}

datatype 'a rose_tree = T 'a "'a rose_tree list"

declare length_Suc_conv [simp]

locale Amortized =
fixes arity :: "'op \<Rightarrow> nat"
fixes exec :: "'op \<Rightarrow> 's list \<Rightarrow> 's"
fixes inv :: "'s \<Rightarrow> bool"
fixes cost :: "'op \<Rightarrow> 's list \<Rightarrow> nat"
fixes \<Phi> :: "'s \<Rightarrow> real"
fixes U :: "'op \<Rightarrow> 's list \<Rightarrow> real"
assumes inv_exec: "\<lbrakk>\<forall>s \<in> set ss. inv s; length ss = arity f \<rbrakk> \<Longrightarrow> inv(exec f ss)"
assumes ppos: "inv s \<Longrightarrow> \<Phi> s \<ge> 0"
assumes p0: "arity f = 0 \<Longrightarrow> \<Phi> (exec f []) = 0"
assumes U: "\<lbrakk> \<forall>s \<in> set ss. inv s; length ss = arity f \<rbrakk>
 \<Longrightarrow> cost f ss + \<Phi>(exec f ss) - listsum (map \<Phi> ss) \<le> U f ss"
begin

fun wf :: "'op rose_tree \<Rightarrow> bool" where
"wf (T f ts) = (length ts = arity f \<and> (\<forall>t \<in> set ts. wf t))"

fun state :: "'op rose_tree \<Rightarrow> 's" where
"state (T f ts) = exec f (map state ts)"

lemma inv_state: "wf ot \<Longrightarrow> inv(state ot)"
by(induction ot)(simp_all add: inv_exec)

definition acost :: "'op \<Rightarrow> 's list \<Rightarrow> real" where
"acost f ss = cost f ss + \<Phi> (exec f ss) - listsum (map \<Phi> ss)"

fun acost_sum :: "'op rose_tree \<Rightarrow> real" where
"acost_sum (T f ts) = acost f (map state ts) + listsum (map acost_sum ts)"

fun cost_sum :: "'op rose_tree \<Rightarrow> real" where
"cost_sum (T f ts) = cost f (map state ts) + listsum (map cost_sum ts)"

fun U_sum :: "'op rose_tree \<Rightarrow> real" where
"U_sum (T f ts) = U f (map state ts) + listsum (map U_sum ts)"

lemma t_sum_a_sum: "wf ot \<Longrightarrow> cost_sum ot = acost_sum ot - \<Phi>(state ot)"
apply(induction ot)
apply (auto simp: acost_def p0 Let_def listsum_subtractf cong: listsum_cong)
apply (simp add: o_def)
done

corollary t_sum_le_a_sum: "wf ot \<Longrightarrow> cost_sum ot \<le> acost_sum ot"
by (metis add.commute t_sum_a_sum diff_add_cancel le_add_same_cancel2 ppos[OF inv_state])

lemma a_le_U: "\<lbrakk> \<forall>s \<in> set ss. inv s; length ss = arity f \<rbrakk> \<Longrightarrow> acost f ss \<le> U f ss"
by(simp add: acost_def U)

lemma u_sum_le_U_sum: "wf ot \<Longrightarrow> acost_sum ot \<le> U_sum ot"
proof(induction ot)
  case (T f ts)
  with a_le_U[of "map state ts" f] listsum_mono show ?case
    by (force simp: inv_state)
qed

corollary t_sum_le_U_sum: "wf ot \<Longrightarrow> cost_sum ot \<le> U_sum ot"
by (blast intro: t_sum_le_a_sum u_sum_le_U_sum order.trans)

end

hide_const T

end
