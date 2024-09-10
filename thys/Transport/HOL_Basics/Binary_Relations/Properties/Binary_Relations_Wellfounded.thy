\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsubsection \<open>Well-Founded Relations\<close>
theory Binary_Relations_Wellfounded
  imports
    Functions_Monotone
begin

consts wellfounded_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  wellfounded_on_pred \<equiv> "wellfounded_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellfounded_on_pred (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
    \<equiv> \<forall>Q. (\<exists>x : P. Q x) \<longrightarrow> (\<exists>m : P. Q m \<and> (\<forall>y : P. R y m \<longrightarrow> \<not>(Q y)))"
end

lemma wellfounded_onI:
  assumes "\<And>Q x. P x \<Longrightarrow> Q x \<Longrightarrow> \<exists>m : P. Q m \<and> (\<forall>y : P. R y m \<longrightarrow> \<not>(Q y))"
  shows "wellfounded_on P R"
  using assms unfolding wellfounded_on_pred_def by blast

lemma wellfounded_onE:
  assumes "wellfounded_on P R" "P x" "Q x"
  obtains m where "P m" "Q m" "\<And>y. P y \<Longrightarrow> R y m \<Longrightarrow> \<not>(Q y)"
proof -
  from assms obtain m where "P m" "Q m" "\<forall>y : P. R y m \<longrightarrow> \<not>(Q y)"
    unfolding wellfounded_on_pred_def by auto
  then show ?thesis using that by blast
qed

lemma wellfounded_on_induct [consumes 1, case_names step]:
  assumes "wellfounded_on P R" "P z"
  assumes step: "\<And>x. P x \<Longrightarrow> (\<And>y. P y \<Longrightarrow> R y x \<Longrightarrow> Q y) \<Longrightarrow> Q x"
  shows "Q z"
proof (rule ccontr)
  assume "\<not>(Q z)"
  then obtain m where "P m" "\<not>(Q m)" "\<And>y. P y \<Longrightarrow> R y m \<Longrightarrow> Q y"
    using assms by (blast elim!: wellfounded_onE[where Q = "\<lambda>x. \<not>(Q x)"])
  then show "False" using step by auto
qed

lemma wellfounded_on_rel_map_if_mono_wrt_pred_if_wellfounded_on:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool"
  assumes wf: "wellfounded_on A R"
  and "(B \<Rightarrow> A) f"
  shows "wellfounded_on B (rel_map f R)"
proof (intro wellfounded_onI)
  fix Q and x :: 'b assume "B x" "Q x"
  moreover define U where "U \<equiv> has_inverse_on (B \<sqinter> Q) f"
  ultimately have "A (f x)" "U (f x)" using \<open>(B \<Rightarrow> A) f\<close> by auto
  then obtain m\<^sub>U where "A m\<^sub>U" "U m\<^sub>U" and min: "\<And>a. A a \<Longrightarrow> R a m\<^sub>U \<Longrightarrow> \<not>(U a)"
    using wf by (blast elim!: wellfounded_onE)
  from \<open>U m\<^sub>U\<close> obtain m\<^sub>Q where "B m\<^sub>Q" "f m\<^sub>Q = m\<^sub>U" "Q m\<^sub>Q" unfolding U_def by blast
  have "\<not>(Q b)" if "B b" "rel_map f R b m\<^sub>Q" for b
  proof -
    from that have "R (f b) m\<^sub>U" using \<open>f m\<^sub>Q = m\<^sub>U\<close> by auto
    then have "\<not>(U (f b))" using \<open>B b\<close> \<open>(B \<Rightarrow> A) f\<close> min by blast
    then show ?thesis unfolding U_def using \<open>B b\<close> by blast
  qed
  then show "\<exists>m : B. Q m \<and> (\<forall>b : B. rel_map f R b m \<longrightarrow> \<not>(Q b))" using \<open>B m\<^sub>Q\<close> \<open>Q m\<^sub>Q\<close> by blast
qed

corollary wellfounded_on_if_le_pred_if_wellfounded_on:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellfounded_on P R" "Q \<le> P"
  shows "wellfounded_on Q R"
proof -
  have "(Q \<Rightarrow> P) id" using \<open>Q \<le> P\<close> by force
  then have "wellfounded_on Q (rel_map id R)"
    using assms wellfounded_on_rel_map_if_mono_wrt_pred_if_wellfounded_on by blast
  then show ?thesis by simp
qed

lemma wellfounded_on_if_le_rel_if_wellfounded_on:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellfounded_on P R" "S \<le> R"
  shows "wellfounded_on P S"
proof (intro wellfounded_onI)
  fix Q and x :: 'a assume "P x" "Q x"
  then obtain m where "P m" "Q m" "\<And>y. P y \<Longrightarrow> R y m \<Longrightarrow> \<not> Q y"
    using assms by (force elim!: wellfounded_onE)
  then show "\<exists>m : P. Q m \<and> (\<forall>y : P. S y m \<longrightarrow> \<not> Q y)" using \<open>S \<le> R\<close> by blast
qed

corollary antimono_wellfounded_on:
  "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<ge>)) (wellfounded_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  using wellfounded_on_if_le_pred_if_wellfounded_on wellfounded_on_if_le_rel_if_wellfounded_on
  by (intro mono_wrt_relI Fun_Rel_relI) blast


consts wellfounded :: "'a \<Rightarrow> bool"

overloading
  wellfounded \<equiv> "wellfounded :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(wellfounded :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> wellfounded_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma wellfounded_eq_wellfounded_on:
  "(wellfounded :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = wellfounded_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding wellfounded_def ..

lemma wellfounded_eq_wellfounded_on_uhint [uhint]:
  "P \<equiv> (\<top> :: 'a \<Rightarrow> bool) \<Longrightarrow> (wellfounded :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> wellfounded_on P"
  by (simp add: wellfounded_eq_wellfounded_on)

lemma wellfoundedI [intro]:
  assumes "\<And>Q x. Q x \<Longrightarrow> (\<exists>m : Q. \<forall>y. R y m \<longrightarrow> \<not>(Q y))"
  shows "wellfounded R"
  by (urule wellfounded_onI) (use assms in fastforce)

lemma wellfoundedE:
  assumes "wellfounded R" "Q x"
  obtains m where "Q m" "\<And>y. R y m \<Longrightarrow> \<not>(Q y)"
  by (urule wellfounded_onE) (urule assms | simp)+

lemma wellfounded_on_if_wellfounded:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellfounded R"
  shows "wellfounded_on P R"
  using assms by (urule wellfounded_on_if_le_pred_if_wellfounded_on) auto

lemma wellfounded_induct [consumes 1, case_names step]:
  assumes "wellfounded R"
  assumes "\<And>x. (\<And>y. R y x \<Longrightarrow> Q y) \<Longrightarrow> Q x"
  shows "Q x"
  using assms(1) by (urule wellfounded_on_induct) (use assms(2-) in auto)

lemma wellfounded_rel_restrict_if_wellfounded_on:
  assumes "wellfounded_on P R"
  shows "wellfounded R\<up>\<^bsub>P\<^esub>"
proof (intro wellfoundedI)
  fix Q and x :: 'a assume "Q x"
  show "\<exists>m : Q. \<forall>y. R\<up>\<^bsub>P\<^esub> y m \<longrightarrow> \<not>(Q y)"
  proof (cases "\<exists>s : P. Q s")
    case True
    then show ?thesis using assms by (fast elim!: wellfounded_onE)
  next
    case False
    then show ?thesis using \<open>Q x\<close> by blast
  qed
qed


end