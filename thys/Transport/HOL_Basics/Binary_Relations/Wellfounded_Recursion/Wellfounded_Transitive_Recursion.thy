\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Well-Founded Transitive Recursion\<close>
theory Wellfounded_Transitive_Recursion
  imports
    Binary_Relations_Transitive
    Binary_Relations_Wellfounded
    Binary_Relation_Functions
    Functions_Restrict
begin

paragraph \<open>Summary\<close>
text \<open>Well-founded recursion on transitive, well-founded relations. One can extend this to
well-founded recursion on non-transitive, well-founded relations since the transitive closure of a
well-founded relation is well-founded.\<close>

context
  includes fun_restrict_syntax and no_rel_restrict_syntax
begin

definition "fun_rel_restrict f R y \<equiv> f\<restriction>\<^bsub>R\<inverse> y :: 'a \<Rightarrow> bool\<^esub>"

lemma fun_rel_restrict_eq [simp]:
  assumes "R x y"
  shows "fun_rel_restrict f R y x = f x"
  using assms unfolding fun_rel_restrict_def by auto

lemma fun_rel_restrict_if_not [simp]:
  assumes "\<not>(R x y)"
  shows "fun_rel_restrict f R y x = undefined"
  using assms unfolding fun_rel_restrict_def by auto

lemma fun_rel_restrict_eq_fun_restrict: "fun_rel_restrict f R y = f\<restriction>\<^bsub>R\<inverse> y\<^esub>"
  unfolding fun_rel_restrict_def by auto

lemma fun_rel_restrict_cong [cong]:
  assumes "y = y'"
  and "\<And>x. R x y' \<longleftrightarrow> R' x y'"
  and "\<And>x. R' x y' \<Longrightarrow> f x = g x"
  shows "fun_rel_restrict f R y = fun_rel_restrict g R' y"
  using assms by (intro ext) (auto simp: fun_rel_restrict_eq_fun_restrict fun_restrict_eq_if)

lemma fun_rel_restrict_rel_restrict_eq_fun_restrict_fun_rel_restrictI [simp]:
  assumes "P x"
  shows "fun_rel_restrict f (rel_restrict R P) x = (fun_rel_restrict f R x)\<restriction>\<^bsub>P\<^esub>"
  using assms unfolding fun_rel_restrict_eq_fun_restrict fun_restrict_eq_if by fastforce


context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and step :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
begin

definition "wf_rec_step f x = step (fun_rel_restrict (f x) R x) x"

lemma wf_rec_step_eq: "wf_rec_step f x = step (fun_rel_restrict (f x) R x) x"
  unfolding wf_rec_step_def by simp

definition "is_recfun X f \<equiv> f = fun_rel_restrict (wf_rec_step (\<lambda>_. f)) R X"

definition "the_recfun X = (THE f. is_recfun X f)"

lemma is_recfunI [intro]:
  assumes "\<And>x. R x X \<Longrightarrow> f x = wf_rec_step (\<lambda>_. f) x"
  and "\<And>x. \<not>(R x X) \<Longrightarrow> f x = undefined"
  shows "is_recfun X f"
  using assms unfolding is_recfun_def wf_rec_step_eq fun_rel_restrict_eq_fun_restrict fun_restrict_eq_if
  by (intro ext) simp

lemma is_recfunE [elim]:
  assumes "is_recfun X f"
  obtains "\<And>x. R x X \<Longrightarrow> f x = wf_rec_step (\<lambda>_. f) x"
    "\<And>x. \<not>(R x X) \<Longrightarrow> f x = undefined"
  using assms[unfolded is_recfun_def, THEN fun_cong]
  unfolding fun_rel_restrict_eq_fun_restrict fun_restrict_eq_if
  by simp

lemma eq_if_rel_if_is_recfun:
  assumes "is_recfun X f"
  and "R x X"
  shows "f x = wf_rec_step (\<lambda>_. f) x"
  using assms by auto

lemma eq_if_not_rel_if_is_recfun:
  assumes "is_recfun X f"
  and "\<not>(R x X)"
  shows "f x = undefined"
  using assms by auto

context
  assumes wf: "wellfounded R"
  and trans: "transitive R"
begin

lemma app_eq_app_if_is_recfunI:
  assumes "is_recfun X f" "is_recfun Y g"
  and "R Z X" "R Z Y"
  shows "f Z = g Z"
using wf \<open>R Z X\<close> \<open>R Z Y\<close>
proof (induction Z rule: wellfounded_induct)
  case (step Z)
  then have "f z = g z" if "R z Z" for z using that trans by auto
  moreover have "f Z = wf_rec_step (\<lambda>_. f) Z" "g Z = wf_rec_step (\<lambda>_. g) Z" using assms step.prems by auto
  ultimately show ?case by (auto simp: wf_rec_step_eq)
qed

corollary eq_if_is_recfunI:
  assumes "is_recfun X f" "is_recfun X g"
  shows "f = g"
proof (intro ext)
  fix x from assms app_eq_app_if_is_recfunI show "f x = g x" by (cases "R x X") force+
qed

corollary is_recfun_the_recfun_if_is_recfunI:
  assumes "is_recfun X f"
  shows "is_recfun X (the_recfun X)"
proof -
  from assms eq_if_is_recfunI have "\<exists>!g. is_recfun X g" by auto
  from theI'[OF this] show ?thesis unfolding the_recfun_def by auto
qed

corollary fun_rel_restrict_eq_fun_rel_restrict_if_is_recfunI:
  assumes recfuns: "is_recfun x f" "is_recfun X g"
  and "R x X"
  shows "fun_rel_restrict f R x = fun_rel_restrict g R x"
proof -
  have "f y = g y" if "R y x" for y
    using app_eq_app_if_is_recfunI[OF recfuns] \<open>R y x\<close> \<open>R x X\<close> trans by blast
  then show ?thesis by auto
qed

definition "wft_rec \<equiv> wf_rec_step the_recfun"

lemma ex_is_recfunI: "\<exists>f. is_recfun X f"
using wf
proof (induction X rule: wellfounded_induct)
  case (step X)
  then have is_recfun: "is_recfun x (the_recfun x)" if "R x X" for x
    using is_recfun_the_recfun_if_is_recfunI that by blast
  define f where "f \<equiv> fun_rel_restrict wft_rec R X"
  have "fun_rel_restrict f R x = fun_rel_restrict (the_recfun x) R x" if "R x X" for x
  proof -
    have "f y = (the_recfun x) y" if "R y x" for y
    proof -
      have "is_recfun y (the_recfun y)" "is_recfun x (the_recfun x)"
        using is_recfun \<open>R x X\<close> \<open>R y x\<close> trans by auto
      with fun_rel_restrict_eq_fun_rel_restrict_if_is_recfunI have
        "fun_rel_restrict (the_recfun y) R y = fun_rel_restrict (the_recfun x) R y"
        using \<open>R y x\<close> by auto
      moreover have "f y = wft_rec y"
        unfolding f_def using \<open>R y x\<close> \<open>R x X\<close> trans by auto
      moreover have "wf_rec_step (\<lambda>_. the_recfun x) y = (the_recfun x) y"
        using \<open>R y x\<close> \<open>R x X\<close> is_recfun by fastforce
      ultimately show ?thesis by (auto simp: wft_rec_def wf_rec_step_eq)
    qed
    then show ?thesis by auto
  qed
  then have "is_recfun X f" unfolding f_def by (auto simp: wft_rec_def wf_rec_step_eq)
  then show ?case by auto
qed

corollary is_recfun_the_recfunI: "is_recfun X (the_recfun X)"
  using is_recfun_the_recfun_if_is_recfunI ex_is_recfunI by blast

theorem wft_rec_eq_wf_rec_stepI: "wft_rec X = wf_rec_step (\<lambda>_. wft_rec) X"
proof -
  have "(the_recfun X) x = wf_rec_step the_recfun x" if "R x X" for x
  proof -
    have "(the_recfun X) x = wf_rec_step (\<lambda>_. the_recfun X) x"
      using is_recfun_the_recfunI \<open>R x X\<close> by auto
    moreover have "fun_rel_restrict (the_recfun x) R x = fun_rel_restrict (the_recfun X) R x"
      using fun_rel_restrict_eq_fun_rel_restrict_if_is_recfunI is_recfun_the_recfunI \<open>R x X\<close>
      by blast
    ultimately show ?thesis by (auto simp: wf_rec_step_eq)
  qed
  then have "fun_rel_restrict (the_recfun X) R X = fun_rel_restrict (wf_rec_step the_recfun) R X" by simp
  then show ?thesis by (simp add: wft_rec_def wf_rec_step_eq)
qed

end
end
end

end