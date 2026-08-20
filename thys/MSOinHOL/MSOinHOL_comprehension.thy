theory MSOinHOL_comprehension
  imports MSOinHOL_deep_subst_lemma
begin

text \<open>Monadic comprehension as a derived schema: under the full
  second-order domain (@{text "ValD'"}, \<open>E = Univ\<close>) comprehension holds
  for every \<open>\<phi>\<close> with \<open>X\<close> not free; the witness is the set defined by
  \<open>\<phi>\<close>.\<close>

theorem comprehension_schema:
  assumes "X not_free2_in \<phi>"
  shows "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>dx. ((X\<^sup>d(x)) \<longleftrightarrow>\<^sup>d \<phi>))"
  unfolding ValD'_def
proof (intro allI)
  fix I g G
  let ?S = "\<lambda>d. \<langle>I,Univ,Univ\<rangle>,g[x\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>"
  have "\<langle>I,Univ,Univ\<rangle>,g,G\<langle>X\<leftarrow>?S\<rangle> \<Turnstile>\<^sup>d (\<forall>\<^sup>dx. ((X\<^sup>d(x)) \<longleftrightarrow>\<^sup>d \<phi>))"
    using assms by (simp add: DefD N12)
  thus "\<langle>I,Univ,Univ\<rangle>,g,G \<Turnstile>\<^sup>d (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>dx. ((X\<^sup>d(x)) \<longleftrightarrow>\<^sup>d \<phi>))"
    by auto
qed

text \<open>Headline instance (cf. \<open>comprehension_d\<close>): the set of
  \<open>r\<close>-self-related individuals exists.\<close>

corollary comprehension_atom:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2X. \<forall>\<^sup>dx. ((X\<^sup>d(x)) \<longleftrightarrow>\<^sup>d (r\<^sup>d(x,x))))"
  by (rule comprehension_schema) simp

text \<open>Standard vs.\ weak (Henkin): \<open>comprehension_schema\<close> needs
  \<open>E = Univ\<close> and fails for general @{text "ValD"}---the
  standard-vs-Henkin gap behind the Loewenheim--Skolem problem, treated
  in the next section (\emph{Downward Löwenheim--Skolem}).\<close>

end
