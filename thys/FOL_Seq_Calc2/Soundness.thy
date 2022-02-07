section \<open>Soundness\<close>

theory Soundness
  imports ProverLemmas
begin

text \<open>In this theory, we prove that the prover is sound with regards to the SeCaV proof system 
  using the abstract soundness framework.\<close>

text \<open>If some suffix of the sequents in all of the children of a state are provable, so is some
  suffix of the sequent in the current state, with the prefix in each sequent being the same.
  (As a side condition, the lists of terms need to be compatible.)\<close>
lemma SeCaV_children_pre:
  assumes \<open>\<forall>z' \<in> set (children A r z). (\<tturnstile> pre @ z')\<close>
    and \<open>paramss (pre @ z) \<subseteq> paramsts A\<close> 
  shows \<open>\<tturnstile> pre @ z\<close>
  using assms
proof (induct z arbitrary: pre A)
  case Nil
  then show ?case
    by simp
next
  case (Cons p z)
  then have ih: \<open>\<forall>z' \<in> set (children A r z). (\<tturnstile> pre @ z') \<Longrightarrow> (\<tturnstile> pre @ z)\<close>
    if \<open>paramss (pre @ z) \<subseteq> paramsts A\<close> for pre A
    using that by simp

  let ?A = \<open>remdups (A @ subtermFms (concat (parts A r p)))\<close>

  have A: \<open>paramss (pre @ p # z) \<subseteq> paramsts ?A\<close>
    using paramsts_subset Cons.prems(2) by fastforce

  have \<open>\<forall>z' \<in> set (list_prod (parts A r p) (children ?A r z)). (\<tturnstile> pre @ z')\<close>
    using Cons.prems by (metis children.simps(2))
  then have \<open>\<forall>z' \<in> {hs @ ts |hs ts. hs \<in> set (parts A r p) \<and> ts \<in> set (children ?A r z)}.
      (\<tturnstile> pre @ z')\<close>
    using list_prod_is_cartesian by blast
  then have *:
    \<open>\<forall>hs \<in> set (parts A r p). \<forall>ts \<in> set (children ?A r z). (\<tturnstile> pre @ hs @ ts)\<close>
    by blast
  then show ?case
  proof (cases r p rule: parts_exhaust)
    case (AlphaDis p q)
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ p # q # z')\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [p, q]) @ z')\<close>
      by simp
    then have \<open>\<tturnstile> pre @ p # q # z\<close>
      using AlphaDis ih[where pre=\<open>pre @ [p, q]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> p # q # pre @ z\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Dis p q # pre @ z\<close>
      using SeCaV.AlphaDis by blast
    then show ?thesis
      using AlphaDis Ext by simp
  next
    case (AlphaImp p q)
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg p # q # z')\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [Neg p, q]) @ z')\<close>
      by simp
    then have \<open>\<tturnstile> pre @ Neg p # q # z\<close>
      using AlphaImp ih[where pre=\<open>pre @ [Neg p, q]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> Neg p # q # pre @ z\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Imp p q # pre @ z\<close>
      using SeCaV.AlphaImp by blast
    then show ?thesis
      using AlphaImp Ext by simp
  next
    case (AlphaCon p q)
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg p # Neg q # z')\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [Neg p, Neg q]) @ z')\<close>
      by simp
    then have \<open>\<tturnstile> pre @ Neg p # Neg q # z\<close>
      using AlphaCon ih[where pre=\<open>pre @ [Neg p, Neg q]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> Neg p # Neg q # pre @ z\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Neg (Con p q) # pre @ z\<close>
      using SeCaV.AlphaCon by blast
    then show ?thesis
      using AlphaCon Ext by simp
  next
    case (BetaCon p q)
    then have
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ p # z')\<close>
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ q # z')\<close>
      using * unfolding parts_def by simp_all
    then have
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [p]) @ z')\<close>
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [q]) @ z')\<close>
      by simp_all
    then have \<open>\<tturnstile> pre @ p # z\<close> \<open>\<tturnstile> pre @ q # z\<close>
      using BetaCon ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp_all
    then have \<open>\<tturnstile> p # pre @ z\<close> \<open>\<tturnstile> q # pre @ z\<close>
      using Ext by simp_all
    then have \<open>\<tturnstile> Con p q # pre @ z\<close>
      using SeCaV.BetaCon by blast
    then show ?thesis
      using BetaCon Ext by simp
  next
    case (BetaImp p q)
    then have
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ p # z')\<close>
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg q # z')\<close>
      using * unfolding parts_def by simp_all
    then have
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [p]) @ z')\<close>
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [Neg q]) @ z')\<close>
      by simp_all
    then have \<open>\<tturnstile> pre @ p # z\<close> \<open>\<tturnstile> pre @ Neg q # z\<close>
      using BetaImp ih ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp_all
    then have \<open>\<tturnstile> p # pre @ z\<close> \<open>\<tturnstile> Neg q # pre @ z\<close>
      using Ext by simp_all
    then have \<open>\<tturnstile> Neg (Imp p q) # pre @ z\<close>
      using SeCaV.BetaImp by blast
    then show ?thesis
      using BetaImp Ext by simp
  next
    case (BetaDis p q)
    then have
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg p # z')\<close>
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg q # z')\<close>
      using * unfolding parts_def by simp_all
    then have
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [Neg p]) @ z')\<close>
      \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [Neg q]) @ z')\<close>
      by simp_all
    then have \<open>\<tturnstile> pre @ Neg p # z\<close> \<open>\<tturnstile> pre @ Neg q # z\<close>
      using BetaDis ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp_all
    then have \<open>\<tturnstile> Neg p # pre @ z\<close> \<open>\<tturnstile> Neg q # pre @ z\<close>
      using Ext by simp_all
    then have \<open>\<tturnstile> Neg (Dis p q) # pre @ z\<close>
      using SeCaV.BetaDis by blast
    then show ?thesis
      using BetaDis Ext by simp
  next
    case (DeltaUni p)
    let ?i = \<open>generateNew A\<close>
    have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ sub 0 (Fun ?i []) p # z')\<close>
      using DeltaUni * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [sub 0 (Fun ?i []) p]) @ z')\<close>
      by simp
    moreover have \<open>set (subtermFm (sub 0 (Fun ?i []) p)) \<subseteq> set ?A\<close>
      using DeltaUni unfolding parts_def by simp
    then have \<open>params (sub 0 (Fun ?i []) p) \<subseteq> paramsts ?A\<close>
      using subtermFm_subset_params by blast
    ultimately have \<open>\<tturnstile> pre @ sub 0 (Fun ?i []) p # z\<close>
      using DeltaUni ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp 
    then have \<open>\<tturnstile> sub 0 (Fun ?i []) p # pre @ z\<close>
      using Ext by simp
    moreover have \<open>?i \<notin> paramsts A\<close>
      by (induct A) (metis Suc_max_new generateNew_def listFunTm_paramst(2) plus_1_eq_Suc)+
    then have \<open>news ?i (p # pre @ z)\<close>
      using DeltaUni Cons.prems(2) news_paramss by auto
    ultimately have \<open>\<tturnstile> Uni p # pre @ z\<close>
      using SeCaV.DeltaUni by blast
    then show ?thesis
      using DeltaUni Ext by simp
  next
    case (DeltaExi p)
    let ?i = \<open>generateNew A\<close>
    have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg (sub 0 (Fun ?i []) p) # z')\<close>
      using DeltaExi * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [Neg (sub 0 (Fun ?i []) p)]) @ z')\<close>
      by simp
    moreover have \<open>set (subtermFm (sub 0 (Fun ?i []) p)) \<subseteq> set ?A\<close>
      using DeltaExi unfolding parts_def by simp
    then have \<open>params (sub 0 (Fun ?i []) p) \<subseteq> paramsts ?A\<close>
      using subtermFm_subset_params by blast
    ultimately have \<open>\<tturnstile> pre @ Neg (sub 0 (Fun ?i []) p) # z\<close>
      using DeltaExi ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> Neg (sub 0 (Fun ?i []) p) # pre @ z\<close>
      using Ext by simp
    moreover have \<open>?i \<notin> paramsts A\<close>
      by (induct A) (metis Suc_max_new generateNew_def listFunTm_paramst(2) plus_1_eq_Suc)+
    then have \<open>news ?i (p # pre @ z)\<close>
      using DeltaExi Cons.prems(2) news_paramss by auto
   ultimately have \<open>\<tturnstile> Neg (Exi p) # pre @ z\<close>
      using SeCaV.DeltaExi by blast
    then show ?thesis
      using DeltaExi Ext by simp
  next
    case (NegNeg p)
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ p # z')\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [p]) @ z')\<close>
      by simp
    then have \<open>\<tturnstile> pre @ p # z\<close>
      using NegNeg ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> p # pre @ z\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Neg (Neg p) # pre @ z\<close>
      using SeCaV.Neg by blast
    then show ?thesis
      using NegNeg Ext by simp
  next
    case (GammaExi p)
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ z')\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> ((pre @ Exi p # map (\<lambda>t. sub 0 t p) A) @ z'))\<close>
      by simp
    moreover have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts A \<union> params p\<close>
      using params_sub by fastforce
    then have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts ?A\<close>
        using GammaExi A by fastforce
    then have \<open>paramss (map (\<lambda>t. sub 0 t p) A) \<subseteq> paramsts ?A\<close>
      by auto
    ultimately have \<open>\<tturnstile> pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ z\<close>
      using GammaExi ih[where pre=\<open>pre @ Exi p # map _ A\<close> and A=\<open>?A\<close>] A by simp
    moreover have \<open>ext (map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ z)
          (pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ z)\<close>
      by auto
    ultimately have \<open>\<tturnstile> map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ z\<close>
      using Ext by blast
    then have \<open>\<tturnstile> Exi p # pre @ z\<close>
    proof (induct A)
      case Nil
      then show ?case
        by simp
    next
      case (Cons a A)
      then have \<open>\<tturnstile> Exi p # map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ z\<close>
        using SeCaV.GammaExi by simp
      then have \<open>\<tturnstile> map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ z\<close>
        using Ext by simp
      then show ?case
        using Cons.hyps by blast
    qed
    then show ?thesis
      using GammaExi Ext by simp
  next
    case (GammaUni p)
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ z')\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> ((pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A) @ z'))\<close>
      by simp
    moreover have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts A \<union> params p\<close>
      using params_sub by fastforce
    then have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts ?A\<close>
        using GammaUni A by fastforce
    then have \<open>paramss (map (\<lambda>t. sub 0 t p) A) \<subseteq> paramsts ?A\<close>
      by auto
    ultimately have \<open>\<tturnstile> pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ z\<close>
      using GammaUni ih[where pre=\<open>pre @ Neg (Uni p) # map _ A\<close> and A=\<open>?A\<close>] A by simp
    moreover have \<open>ext (map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ z)
          (pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ z)\<close>
      by auto
    ultimately have \<open>\<tturnstile> map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ z\<close>
      using Ext by blast
    then have \<open>\<tturnstile> Neg (Uni p) # pre @ z\<close>
    proof (induct A)
      case Nil
      then show ?case
        by simp
    next
      case (Cons a A)
      then have \<open>\<tturnstile> Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ z\<close>
        using SeCaV.GammaUni by simp
      then have \<open>\<tturnstile> map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ z\<close>
        using Ext by simp
      then show ?case
        using Cons.hyps by blast
    qed
    then show ?thesis
      using GammaUni Ext by simp
  next
    case Other
    then have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> (pre @ [p]) @ z')\<close>
      using * by simp
    then show ?thesis
      using ih[where pre=\<open>pre @ [p]\<close> and A=\<open>?A\<close>] A by simp
  qed
qed

text \<open>As a special case, the prefix can be empty.\<close>
corollary SeCaV_children:
  assumes \<open>\<forall>z' \<in> set (children A r z). (\<tturnstile> z')\<close> and \<open>paramss z \<subseteq> paramsts A\<close>
  shows \<open>\<tturnstile> z\<close>
  using SeCaV_children_pre assms by (metis append_Nil)

text \<open>Using this lemma, we can instantiate the abstract soundness framework.\<close>
interpretation Soundness eff rules UNIV \<open>\<lambda>_ (A, z). (\<tturnstile> z)\<close>
  unfolding Soundness_def
proof safe
  fix r A z ss S
  assume r_enabled: \<open>eff r (A, z) ss\<close>

  assume \<open>\<forall>s'. s' |\<in>| ss \<longrightarrow> (\<forall>S \<in> UNIV. case s' of (A, z) \<Rightarrow> \<tturnstile> z)\<close>
  then have next_sound: \<open>\<forall>B z. (B, z) |\<in>| ss \<longrightarrow> (\<tturnstile> z)\<close>
    by simp

  show \<open>\<tturnstile> z\<close>
  proof (cases \<open>branchDone z\<close>)
    case True
    then obtain p where \<open>p \<in> set z\<close> \<open>Neg p \<in> set z\<close>
      using branchDone_contradiction by blast
    then show ?thesis
      using Ext Basic by fastforce
  next
    case False
    let ?A = \<open>remdups (A @ subtermFms z)\<close>
    have \<open>\<forall>z' \<in> set (children ?A r z). (\<tturnstile> z')\<close>
      using False r_enabled eff_children next_sound by blast
    moreover have \<open>set (subtermFms z) \<subseteq> set ?A\<close>
      by simp
    then have \<open>paramss z \<subseteq> paramsts ?A\<close>
      using subtermFm_subset_params by fastforce
    ultimately show \<open>\<tturnstile> z\<close>
      using SeCaV_children by blast
  qed
qed

text \<open>Using the result from the abstract soundness framework, we can finally state our soundness
  result: for a finite, well-formed proof tree, the sequent at the root of the tree is provable in
  the SeCaV proof system.\<close>
theorem prover_soundness_SeCaV:
  assumes \<open>tfinite t\<close> and \<open>wf t\<close>
  shows \<open>\<tturnstile> rootSequent t\<close>
  using assms soundness by fastforce

end
