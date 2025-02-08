(*<*)
theory Regex_Proof_System
imports Regex
begin
(*>*)

context begin

qualified inductive
  SAT :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Regex.regex \<Rightarrow> bool"
  for sat where
  STest: "i = j \<Longrightarrow> sat i x \<Longrightarrow> SAT sat i j (Regex.Test x)"
| SSkip: "j = i + n \<Longrightarrow> SAT sat i j (Regex.Skip n)"
| SPlusL: "SAT sat i j r \<Longrightarrow> SAT sat i j (Regex.Plus r s)"
| SPlusR: "SAT sat i j s \<Longrightarrow> SAT sat i j (Regex.Plus r s)"
| STimes: "SAT sat i k r \<Longrightarrow> SAT sat k j s \<Longrightarrow> SAT sat i j (Regex.Times r s)"
| SStar_eps: "i = j \<Longrightarrow> SAT sat i j (Regex.Star r)"
| SStar: "i < j \<Longrightarrow> (\<exists>zs. xs = i # zs @ [j]) \<Longrightarrow>
    \<forall>k \<in> {0 ..< length xs - 1}. xs ! k < xs ! (Suc k) \<Longrightarrow>
    \<forall>k \<in> {0 ..< length xs - 1}. SAT sat (xs ! k) (xs ! (Suc k)) r \<Longrightarrow>
    SAT sat i j (Regex.Star r)"

lemma SAT_mono[mono]:
  assumes "X \<le> Y"
  shows "SAT X \<le> SAT Y"
  unfolding le_fun_def le_bool_def
proof safe
  fix i j r
  assume "SAT X i j r"
  then show "SAT Y i j r"
    by (induct i j r rule: SAT.induct) (use assms in \<open>auto 0 3 intro: SAT.intros\<close>)
qed

abbreviation "rm S \<equiv> {(i, j) \<in> S. i < j}"

qualified inductive
  VIO :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Regex.regex \<Rightarrow> bool"
  for vio where
  VSkip: "j \<noteq> i + n \<Longrightarrow> VIO vio i j (Regex.Skip n)"
| VTest: "i = j \<Longrightarrow> vio i x \<Longrightarrow> VIO vio i j (Regex.Test x)"
| VTest_neq: "i \<noteq> j \<Longrightarrow> VIO vio i j (Regex.Test x)"
| VPlus: "VIO vio i j r \<Longrightarrow> VIO vio i j s \<Longrightarrow> VIO vio i j (Regex.Plus r s)"
| VTimes: "\<forall>k \<in> {i .. j}. VIO vio i k r \<or> VIO vio k j s \<Longrightarrow> VIO vio i j (Regex.Times r s)"
| VStar: "i < j \<Longrightarrow> i \<in> S \<Longrightarrow> j \<in> T \<Longrightarrow> S \<union> T = {i .. j} \<Longrightarrow> S \<inter> T = {} \<Longrightarrow>
    \<forall>(s, t) \<in> rm (S \<times> T). VIO vio s t r \<Longrightarrow> VIO vio i j (Regex.Star r)"
| VStar_gt: "i > j \<Longrightarrow> VIO vio i j (Regex.Star r)"

lemma VIO_mono[mono]:
  assumes "X \<le> Y"
  shows "VIO X \<le> VIO Y"
  unfolding le_fun_def le_bool_def
proof safe
  fix i j r
  assume "VIO X i j r"
  then show "VIO Y i j r"
    by (induct i j r rule: VIO.induct) (use assms in \<open>auto 5 3 intro: VIO.intros\<close>)
qed

inductive chain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
	chain_singleton: "chain R [x]"
| chain_cons: "chain R (y # xs) \<Longrightarrow> R x y \<Longrightarrow> chain R (x # y # xs)"

lemma
  chain_Nil[simp]: "\<not> chain R []" and
  chain_not_Nil: "chain R xs \<Longrightarrow> xs \<noteq> []"
  by (auto elim: chain.cases)

lemma chain_rtranclp: "chain R xs \<Longrightarrow> R\<^sup>*\<^sup>* (hd xs) (last xs)"
  by (induct xs rule: chain.induct) auto

lemma chain_append:
  assumes "chain R xs" "chain R ys" "R (last xs) (hd ys)"
  shows "chain R (xs @ ys)"
  using assms
proof (induct xs arbitrary: ys rule: chain.induct)
  case (chain_singleton x)
  then show ?case by (cases ys) (auto intro: chain.intros)
qed (auto intro: chain.intros)

lemma tranclp_imp_exists_finite_chain_list:
  "R\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists>xs. chain R (x # xs @ [y])"
proof (induct rule: tranclp.induct)
  case (r_into_trancl x y)
  then have "chain R (x # [] @ [y])"
    by (auto intro: chain.intros)
  then show ?case
    by blast
next
  case (trancl_into_trancl x y z)
  note rstar_xy = this(1) and ih = this(2) and r_yz = this(3)
  obtain xs where xs: "chain R (x # xs @ [y])" using ih by blast
  define ys where "ys = xs @ [y]"
  have "chain R (x # ys @ [z])"
    unfolding ys_def using r_yz chain_append[OF xs chain_singleton, of z] by auto
  then show ?case by blast
qed

lemma chain_pairwise:
  "chain R xs \<Longrightarrow> Suc i < length xs \<Longrightarrow> R (xs ! i) (xs ! Suc i)"
  by (induct xs arbitrary: i rule: chain.induct)
    (force simp: nth_Cons' not_le Suc_less_eq2 elim: chain.cases)+

lemma chain_sorted_remdups:
  "chain R xs \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> x \<le> y) \<Longrightarrow> sorted xs \<and> chain R (remdups xs)"
proof (induct xs rule: chain.induct)
  case (chain_cons y xs x)
  then show ?case
    using sorted_remdups[of xs] set_remdups[of xs] eq_iff[of y "hd (remdups xs)"]
    by (cases "remdups xs"; cases "y = hd (remdups xs)")
      (auto intro!: chain.intros intro: order_trans elim: chain.cases)
qed (auto intro: chain.intros)

lemma sorted_remdups: "sorted xs \<Longrightarrow> sorted_wrt (<) (remdups xs)"
  by (induct xs) (auto dest: le_neq_trans)

lemma remdups_sorted_start_end:
  "sorted (i # xs @ [j]) \<Longrightarrow> i \<noteq> j \<Longrightarrow>
  remdups (i # xs @ [j]) = i # remdups (removeAll j (removeAll i xs)) @ [j]"
  by (induct xs) auto

lemma tranclp_to_list:
  fixes R :: "'a :: linorder \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "R\<^sup>+\<^sup>+ i j" "i \<noteq> j" "\<And>x y. R x y \<Longrightarrow> x \<le> y"
  obtains xs zs where "xs = i # zs @ [j]"
    "\<forall>k \<in> {0 ..< length xs - 1}. xs ! k < xs ! (Suc k) \<and> R (xs ! k) (xs ! (Suc k))"
proof atomize_elim
  from \<open>R\<^sup>+\<^sup>+ i j\<close> obtain zs where "chain R (i # zs @ [j])"
    using tranclp_imp_exists_finite_chain_list by fast
  then have zs: "sorted (i # zs @ [j])" "chain R (remdups (i # zs @ [j]))"
    using chain_sorted_remdups assms(3) by blast+
  then have sorted_wrt: "sorted_wrt (<) (remdups (i # zs @ [j]))"
    using sorted_remdups by blast
  let ?zs = "remdups (removeAll j (removeAll i zs))"
  from zs sorted_wrt have "chain R (i # ?zs @ [j])" "sorted_wrt (<) (i # ?zs @ [j])"
    using remdups_sorted_start_end[of i zs j] assms(2) by auto
  then show "\<exists>xs zs. xs = i # zs @ [j] \<and>
    (\<forall>k\<in>{0..<length xs - 1}. xs ! k < xs ! Suc k \<and> R (xs ! k) (xs ! Suc k))"
    by (subst ex_comm, unfold simp_thms, intro exI[of _ ?zs])
      (auto 0 3 dest: chain_pairwise simp del: remdups.simps
      simp: sorted_wrt_iff_nth_less)
qed


abbreviation match_rel where
  "match_rel test r xs k \<equiv> (xs ! k < xs ! (Suc k) \<and> Regex.match test r (xs ! k) (xs ! (Suc k)))"

lemma list_to_chain:
  "xs \<noteq> [] \<Longrightarrow> \<forall>k \<in> {0 ..< length xs - 1}. R (xs ! k) (xs ! Suc k) \<Longrightarrow> chain R xs"
proof (induct xs)
  case (Cons a xs)
  then show ?case
  proof (cases xs)
    case tail: (Cons b ys)
    with Cons(2,3) show ?thesis
      by (force intro!: chain.intros Cons(1)[unfolded tail])
  qed (auto intro: chain.intros)
qed simp

lemma match_rel_list_to_tranclp:
  "\<exists>xs zs. xs = i # zs @ [j] \<and> (\<forall>k \<in> {0 ..< length xs - 1}. match_rel test r xs k) \<Longrightarrow> i \<noteq> j \<Longrightarrow>
  (Regex.match test r)\<^sup>+\<^sup>+ i j"
  using chain_rtranclp[OF list_to_chain, THEN rtranclpD, of "i # _ @ [j]" "Regex.match test r"]
  by fastforce

lemma completeness_SAT: 
  "\<forall>x \<in> Regex.atms r. \<forall>i. test i x \<longrightarrow> sat i x \<Longrightarrow> Regex.match test r i j \<Longrightarrow> SAT sat i j r"
proof (induct r arbitrary: i j)
  case (Skip x)
  then show ?case
    by (auto intro: SAT.SSkip)
next
  case (Test x)
  then show ?case
    by (auto intro: SAT.STest)
next
  case (Plus r1 r2)
  then show ?case
    by (auto intro: SAT.SPlusL SPlusR)
next
  case (Times r1 r2)
  then obtain k where k_def: "k \<in> {i .. j} \<and> SAT sat i k r1 \<and> SAT sat k j r2"
    using match_le by fastforce
  then show ?case by (auto intro: SAT.STimes)
next
  case (Star r)
  then have "i = j \<or> (i \<noteq> j \<and> (Regex.match test r)\<^sup>+\<^sup>+ i j)"
    using rtranclpD[of "Regex.match test r" i j] tranclpD[of "Regex.match test r" i j]
    by auto
  moreover
  {
    assume i_eq_j: "i = j"
    then have "SAT sat i j (Regex.Star r)" by (auto intro: SAT.SStar_eps)
  }
  moreover
  {
    assume i_neq_j: "i \<noteq> j" and tranclp_ij: "(Regex.match test r)\<^sup>+\<^sup>+ i j"
    then have i_less: "i < j" using Star
      by (auto simp add: le_neq_implies_less match_rtranclp_le)
    then obtain xs and zs where xs_def: "xs = i # zs @ [j] \<and> (\<forall>k \<in> {0 ..< length xs - 1}. xs ! k < xs ! (Suc k) \<and> Regex.match test r (xs ! k) (xs ! (Suc k)))"
      using tranclp_to_list[OF tranclp_ij i_neq_j match_le[of test r]] by auto
    then have "SAT sat i j (Regex.Star r)" using i_less Star
      by (auto intro: SAT.SStar)
  }
  ultimately show ?case by auto
qed

lemma completeness_VIO: 
  "\<forall>x \<in> Regex.atms r. \<forall>i. \<not> test i x \<longrightarrow> vio i x \<Longrightarrow> i \<le> j \<Longrightarrow> \<not> Regex.match test r i j \<Longrightarrow> VIO vio i j r"
proof (induct r arbitrary: i j)
  case (Skip x)
  then show ?case
    by (auto intro: VIO.VSkip)
next
  case (Test x)
  then show ?case
    by (auto intro: VIO.VTest VIO.VTest_neq)
next
  case (Plus r1 r2)
  then show ?case
    by (auto intro: VIO.VPlus)
next
  case (Times r1 r2)
  then have "\<forall>k \<in> {i .. j}. VIO vio i k r1 \<or> VIO vio k j r2"
    by fastforce
  then show ?case
    by (auto intro: VIO.VTimes)
next
  case (Star r)
  define V where V_def: "V = {i .. j}"
  define S where S_def: "S = {k \<in> V. (Regex.match test r)\<^sup>*\<^sup>* i k} \<union> {i}"
  define T where T_def: "T = V - S"
  from S_def V_def have j_notin_S: "j \<notin> S" using Star
    by auto
  from S_def have i_in_S: "i \<in> S"
    by auto
  then have j_in_T: "j \<in> T" using j_notin_S V_def T_def Star(3)
    by auto    
  from Star have nmatch_ij: "\<not> (Regex.match test r)\<^sup>*\<^sup>* i j"
    by auto
  from S_def T_def V_def Star(3) have union_ST: "S \<union> T = {i .. j}"
    by auto
  from S_def T_def V_def Star(4) have inter_ST: "S \<inter> T = {}"
    by auto
  with i_in_S j_in_T Star(3) have i_less_j: "i < j"
    using le_eq_less_or_eq by blast
  {
    assume not_viost: "\<not> (\<forall>(s,t) \<in> rm (S \<times> T). VIO vio s t r)"
    then obtain s and t where st_def: "(s, t) \<in> rm (S \<times> T) \<and> \<not> VIO vio s t r"
      by auto
    then have "Regex.match test r s t" using Star
      by auto
    then have "(Regex.match test r)\<^sup>*\<^sup>* i t" using st_def S_def
      by auto
    then have False using T_def st_def S_def
      by auto
  }
  then have no_path: "\<forall>(s,t) \<in> rm (S \<times> T). VIO vio s t r"
    by auto
  then show ?case
    by (auto intro: VIO.VStar[OF i_less_j i_in_S j_in_T union_ST inter_ST no_path])
qed

lemma soundness_SAT:
  "\<forall>x \<in> Regex.atms r. \<forall>i. sat i x \<longrightarrow> test i x \<Longrightarrow> SAT sat i j r \<Longrightarrow> Regex.match test r i j"
proof(induct r arbitrary: i j)
  case (Skip x)
  then show ?case using SAT.simps[of sat i j "Regex.Skip x"]
    by auto
next
  case (Test x)
  then show ?case using SAT.simps[of sat i j "Regex.Test x"]
    by auto
next
  case (Plus r1 r2)
  then show ?case using SAT.simps[of sat i j "Regex.Plus r1 r2"]
    by auto
next
  case (Times r1 r2)
  then show ?case using SAT.simps[of sat i j "Regex.Times r1 r2"]
    by fastforce
next
  case (Star r)
  then show ?case
  proof(cases "i = j")
    case True
    then show ?thesis
      by auto
  next
    case False
    then obtain xs and zs where xs_form: "xs = i # zs @ [j]" and
      xs_props: "\<forall>k \<in> {0 ..< length xs - 1}. xs ! k < xs ! (Suc k) \<and> SAT sat (xs ! k) (xs ! (Suc k)) r"
      using Star(3) SAT.simps[of sat i j "Regex.Star r"]
      by blast
    then have kmatch: "\<forall>k \<in> {0 ..< length xs - 1}. Regex.match test r (xs ! k) (xs ! Suc k)"
      using Star
      by auto
    then have ex_lists: "\<exists>xs zs. xs = i # zs @ [j] \<and>
      (\<forall>k \<in> {0 ..< length xs - 1}. xs ! k < xs ! (Suc k) \<and> Regex.match test r (xs ! k) (xs ! (Suc k)))"
      using xs_form xs_props by auto
    then have "(Regex.match test r)\<^sup>+\<^sup>+ i j"
      using match_rel_list_to_tranclp[OF ex_lists False] by auto
    then show ?thesis
      by auto
  qed
qed

lemma soundness_VIO:
"\<forall>x \<in> Regex.atms r. \<forall>i. vio i x \<longrightarrow> \<not> test i x \<Longrightarrow> i \<le> j \<Longrightarrow> VIO vio i j r \<Longrightarrow> \<not> Regex.match test r i j"
proof(induct r arbitrary: i j)
  case (Skip x)
  then show ?case using VIO.simps[of vio i j "Regex.Skip x"]
    by auto
next
  case (Test x)
  then show ?case using VIO.simps[of vio i j "Regex.Test x"]
    by auto
next
  case (Plus r1 r2)
  then show ?case using VIO.simps[of vio i j "Regex.Plus r1 r2"]
    by auto
next
  case (Times r1 r2)
  then have kvio: "\<forall>k \<in> {i .. j}. VIO vio i k r1 \<or> VIO vio k j r2"
    using VIO.simps[of vio i j "Regex.Times r1 r2"]
    by auto
  have "\<forall>k. Regex.match test r i k \<and> Regex.match test r k j \<longrightarrow> k \<in> {i .. j}"
    using match_le
    by auto
  then show ?case using Times kvio match_le[of test]
    unfolding Ball_def atLeastAtMost_iff match.simps regex.simps relcompp_apply
    by (metis Un_iff)
next
  case (Star r)
  then obtain S and T where S_def: "i \<in> S" and T_def: "j \<in> T" and
    ST_props: "S \<union> T = {i .. j} \<and> S \<inter> T = {}" and
    st_vio: "\<forall>(s,t) \<in> rm (S \<times> T). VIO vio s t r"
    using Star(4) VIO.simps[of vio i j "Regex.Star r"]
    by auto
  then have nmatch_st: "\<forall>(s,t) \<in> rm (S \<times> T). \<not> Regex.match test r s t"
    using Star
    by auto
  from S_def T_def ST_props have i_neq_j: "i \<noteq> j"
    by auto
  {
    assume rtranclp_ij: "(Regex.match test r)\<^sup>*\<^sup>* i j"
    then have tranclp_ij: "(Regex.match test r)\<^sup>+\<^sup>+ i j"
      using rtranclpD[of "Regex.match test r" i j] i_neq_j
      by auto

    obtain xs and zs where xs_def: "xs = i # zs @ [j]" and
      xs_prop: "\<forall>k \<in> {0 ..< length xs - 1}.  match_rel test r xs k"
      using tranclp_to_list[OF tranclp_ij i_neq_j match_le[of test r]]
      by auto

    with S_def T_def ST_props have "\<exists>k \<in> {0 ..< length xs - 1}. (xs ! k) \<in> S \<and> (xs ! (Suc k)) \<in> T"
    proof (induction zs arbitrary: S T i j xs)
      case Nil
      then show ?case using S_def T_def xs_def
        by auto
    next
      case (Cons a zs')
      from Cons(2-6) have match: "Regex.match test r i a"
        by force
      show ?case
      proof (cases "a \<in> T")
        case True
        then have "xs ! 0 \<in> S \<and> xs ! Suc 0 \<in> T" using S_def Cons
          by (auto simp: xs_def)
        then show ?thesis using S_def Cons(1)[of _ _ _ _ xs] Cons(2-5)
          by force
      next
        case False
        from Cons(5,6) have "chain (<) (i # (a # zs') @ [j])"
          by (intro list_to_chain) auto
        then have "sorted (i # (a # zs') @ [j])"
          using chain_sorted_remdups[of "(<)" "i # (a # zs') @ [j]"]
          by auto
        then have "a \<in> {i .. j}"
          by auto
        with Cons(2-6) False have "\<exists>k\<in>{0..<length (tl xs) - 1}. tl xs ! k \<in> {i \<in> S. a \<le> i} \<and> tl xs ! Suc k \<in> {i \<in> T. a \<le> i}"
          by (intro Cons(1)[of a _ j]) (auto dest: bspec[of _ _ "Suc _"])
        with Cons show ?thesis
          by (auto intro: bexI[of _ "Suc _"])
      qed
    qed
    then have False using nmatch_st xs_prop
      by auto
  }
  then show ?case
    by auto
qed

end

(*<*)
end
(*>*)
