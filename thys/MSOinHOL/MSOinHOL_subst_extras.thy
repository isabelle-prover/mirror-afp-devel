theory MSOinHOL_subst_extras
  imports MSOinHOL_deep_subst_lemma
begin

text \<open>Explicit rename-evaluation lemmas: renaming a bound variable to a
  fresh \<open>f\<close> and updating the assignment preserves truth---the semantic
  core behind \<open>L21\<close> / \<open>N21\<close>.\<close>

text \<open>First-order: rename \<open>y\<close> to a fresh \<open>f\<close>, then evaluate.\<close>

lemma rename_eval:
  assumes "fresh \<phi> \<le> f" and "y < f"
  shows "(\<langle>I,D,E\<rangle>,g[f\<leftarrow>d],G \<Turnstile>\<^sup>d [y\<leftarrow>f](\<phi>)) = (\<langle>I,D,E\<rangle>,g[y\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>)"
proof -
  let ?g' = "g[f\<leftarrow>d]"
  have fy: "f \<noteq> y" using assms(2) by simp
  have nf: "f not_free_in \<phi>" using assms(1) by (meson L6 leD)
  have "f not_in \<phi>" using assms(1) by (meson L5 L6 leD)
  hence sub: "f is_subst_for y in \<phi>" by (rule L18)
  have swap: "?g'[y\<leftarrow>d] = (g[y\<leftarrow>d])[f\<leftarrow>d]"
    using fy by (rule L2)
  have "(\<langle>I,D,E\<rangle>,?g',G \<Turnstile>\<^sup>d [y\<leftarrow>f](\<phi>)) = (\<langle>I,D,E\<rangle>,?g'[y\<leftarrow>(?g' f)],G \<Turnstile>\<^sup>d \<phi>)"
    using sub by (rule SubstitutionLemma)
  also have "\<dots> = (\<langle>I,D,E\<rangle>,?g'[y\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>)" by simp
  also have "\<dots> = (\<langle>I,D,E\<rangle>,(g[y\<leftarrow>d])[f\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>)"
    using swap by simp
  also have "\<dots> = (\<langle>I,D,E\<rangle>,g[y\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>)"
    using nf by (simp add: L12)
  finally show ?thesis .
qed

text \<open>Second-order: rename \<open>Y\<close> to a fresh \<open>f\<close>, then evaluate.  (The
  monadic-set twin of \<open>rename_eval\<close>.)\<close>

lemma rename_eval2:
  assumes "fresh2 \<phi> \<le> f" and "Y < f"
  shows "(\<langle>I,D,E\<rangle>,g,G\<langle>f\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d [Y\<leftarrow>\<^sub>2f](\<phi>)) = (\<langle>I,D,E\<rangle>,g,G\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>)"
proof -
  let ?G' = "G\<langle>f\<leftarrow>S\<rangle>"
  have fy: "f \<noteq> Y" using assms(2) by simp
  have nf: "f not_free2_in \<phi>" using assms(1) by (meson N6 leD)
  have "f not2_in \<phi>" using assms(1) by (meson N5 N6 leD)
  hence sub: "f is_subst2_for Y in \<phi>" by (rule N18)
  have swap: "?G'\<langle>Y\<leftarrow>S\<rangle> = G\<langle>Y\<leftarrow>S\<rangle>\<langle>f\<leftarrow>S\<rangle>"
    using fy by (rule M2)
  have "(\<langle>I,D,E\<rangle>,g,?G' \<Turnstile>\<^sup>d [Y\<leftarrow>\<^sub>2f](\<phi>)) = (\<langle>I,D,E\<rangle>,g,?G'\<langle>Y\<leftarrow>(?G' f)\<rangle> \<Turnstile>\<^sup>d \<phi>)"
    using sub by (rule SubstitutionLemma2)
  also have "\<dots> = (\<langle>I,D,E\<rangle>,g,?G'\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>)" by simp
  also have "\<dots> = (\<langle>I,D,E\<rangle>,g,(G\<langle>Y\<leftarrow>S\<rangle>)\<langle>f\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>)"
    using swap by simp
  also have "\<dots> = (\<langle>I,D,E\<rangle>,g,G\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>)"
    using nf by (simp add: N12)
  finally show ?thesis .
qed

end
