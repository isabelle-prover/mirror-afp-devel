\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Monotonicity Conditions\<close>
theory Transport_Functions_Mono_Conditions
  imports
    Transport_Functions_Base
begin

paragraph \<open>Summary\<close>
text \<open>In the dependent function relator case, we need to stipulate monotonicity conditions,
which we formalize here.\<close>

context transport_Dep_Fun_Rel
begin

definition "mono_cond_left_rel \<equiv> ((x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)) \<Rightarrow> \<lparr>x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3\<rparr> \<Rrightarrow> (\<le>)) L2"

lemma mono_cond_left_relI [intro]:
  assumes "((x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)) \<Rightarrow> \<lparr>x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3\<rparr> \<Rrightarrow> (\<le>)) L2"
  shows mono_cond_left_rel
  using assms unfolding mono_cond_left_rel_def by auto

lemma mono_cond_left_relD [dest]:
  assumes mono_cond_left_rel
  shows "((x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)) \<Rightarrow> \<lparr>x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3\<rparr> \<Rrightarrow> (\<le>)) L2"
  using assms unfolding mono_cond_left_rel_def by auto

end

context transport_Dep_Fun_Rel
begin

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

definition "mono_cond_right_rel \<equiv> flip.mono_cond_left_rel"

lemma mono_cond_right_relI [intro]:
  assumes "((x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)) \<Rightarrow> \<lparr>x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'\<rparr> \<Rrightarrow> (\<le>)) R2"
  shows mono_cond_right_rel
  using assms unfolding mono_cond_right_rel_def by (rule flip.mono_cond_left_relI)

lemma mono_cond_right_relD [dest]:
  assumes mono_cond_right_rel
  shows "((x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)) \<Rightarrow> \<lparr>x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'\<rparr> \<Rrightarrow> (\<le>)) R2"
  using assms unfolding mono_cond_right_rel_def by (rule flip.mono_cond_left_relD)

definition "mono_conds_rel \<equiv> mono_cond_left_rel \<and> mono_cond_right_rel"

lemma mono_conds_relI [intro]:
  assumes mono_cond_left_rel
  and mono_cond_right_rel
  shows mono_conds_rel
  using assms unfolding mono_conds_rel_def by auto

lemma mono_conds_relE [elim]:
  assumes mono_conds_rel
  obtains mono_cond_left_rel mono_cond_right_rel
  using assms unfolding mono_conds_rel_def by auto

definition "mono_cond_left_fun \<equiv> ((x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)) \<Rightarrow> (x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1') \<Rrightarrow>
  in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>) \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"

lemma mono_cond_left_funI [intro]:
  assumes "((x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)) \<Rightarrow> (x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1') \<Rrightarrow>
    in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>) \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  shows mono_cond_left_fun
  using assms unfolding mono_cond_left_fun_def by auto

lemma mono_cond_left_funD [dest]:
  assumes mono_cond_left_fun
  shows "((x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)) \<Rightarrow> (x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1') \<Rrightarrow>
    in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>) \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  using assms unfolding mono_cond_left_fun_def by auto

definition "mono_cond_right_fun \<equiv> ((x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)) \<Rightarrow> (x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1') \<Rrightarrow>
  in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>) \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"

lemma mono_cond_right_funI [intro]:
  assumes "((x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)) \<Rightarrow> (x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1') \<Rrightarrow>
    in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>) \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  shows mono_cond_right_fun
  using assms unfolding mono_cond_right_fun_def by simp

lemma mono_cond_right_funD [dest]:
  assumes mono_cond_right_fun
  shows "((x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)) \<Rightarrow> (x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1') \<Rrightarrow>
    in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>) \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  using assms unfolding mono_cond_right_fun_def by simp

definition "mono_conds_fun \<equiv> mono_cond_left_fun \<and> mono_cond_right_fun"

lemma mono_conds_funI [intro]:
  assumes mono_cond_left_fun
  and mono_cond_right_fun
  shows "mono_conds_fun"
  using assms unfolding mono_conds_fun_def by auto

lemma mono_conds_funE [elim]:
  assumes "mono_conds_fun"
  obtains mono_cond_left_fun mono_cond_right_fun
  using assms unfolding mono_conds_fun_def by auto

definition "mono_conds \<equiv> mono_conds_rel \<and> mono_conds_fun"

lemma mono_condsI [intro]:
  assumes mono_conds_rel
  and mono_conds_fun
  shows mono_conds
  using assms unfolding mono_conds_def by auto

lemma mono_condsE [elim]:
  assumes mono_conds
  obtains mono_conds_rel mono_conds_fun
  using assms unfolding mono_conds_def by auto

lemmas mono_cond_intros =
  mono_cond_left_relI mono_cond_right_relI mono_conds_relI
  mono_cond_left_funI mono_cond_right_funI mono_conds_funI
  mono_condsI

end
end