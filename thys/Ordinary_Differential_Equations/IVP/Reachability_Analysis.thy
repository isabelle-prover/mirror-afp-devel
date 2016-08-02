theory Reachability_Analysis
imports
  Flow
begin

subsection \<open>explicit representation of hyperplane\<close>

datatype 'a sctn = Sctn (normal: 'a) (pstn: real)

definition "le_halfspace sctn x \<longleftrightarrow> x \<bullet> normal sctn \<le> pstn sctn"
definition "plane_of sctn = {x. x \<bullet> normal sctn = pstn sctn}"


subsection \<open>predicates for reachability analysis\<close>

locale auto_ll_on_open_euclidean = auto_ll_on_open f X for f::"'a::euclidean_space \<Rightarrow> _" and X
begin

definition "flowpipe X0 hl hu CX X1 \<longleftrightarrow> 0 \<le> hl \<and> hl \<le> hu \<and> X0 \<subseteq> X \<and> CX \<subseteq> X \<and> X1 \<subseteq> X \<and>
  (\<forall>x0 \<in> X0. \<forall>h \<in> {hl .. hu}. h \<in> existence_ivl0 x0 \<and> flow0 x0 h \<in> X1 \<and> (\<forall>h' \<in> {0 .. h}. flow0 x0 h' \<in> CX))"

lemma flowpipeD:
  assumes "flowpipe X0 hl hu CX X1"
  shows flowpipe_safeD: "X0 \<union> CX \<union> X1 \<subseteq> X"
    and flowpipe_nonneg: "0 \<le> hl" "hl \<le> hu"
    and flowpipe_exivl: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> x0 \<in> X0 \<Longrightarrow> h \<in> existence_ivl0 x0"
    and flowpipe_discrete: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> x0 \<in> X0 \<Longrightarrow> flow0 x0 h \<in> X1"
    and flowpipe_cont: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> x0 \<in> X0 \<Longrightarrow> 0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> flow0 x0 h' \<in> CX"
  using assms
  by (auto simp: flowpipe_def)


definition "flowsto X0 CX Y \<longleftrightarrow> X0 \<subseteq> X \<and> CX \<subseteq> X \<and> Y \<subseteq> X \<and>
  (\<forall>x \<in> X0. \<exists>t\<ge>0. t \<in> existence_ivl0 x \<and> (\<forall>s \<in> {0 .. t}. flow0 x s \<in> CX) \<and> flow0 x t \<in> Y)"

lemma flowsto_self:
  "X0 \<subseteq> CX \<Longrightarrow> CX \<subseteq> X \<Longrightarrow> flowsto X0 CX X0"
  by (force simp: flowsto_def)

lemma flowsto_self_overappr:
  "X0 \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> flowsto X0 X0 Y"
  by (auto simp: flowsto_def subset_iff intro!: exI[where x=0])

lemma flowsto_unionI:
  "flowsto X0 CX Y \<Longrightarrow> flowsto Z CZ W \<Longrightarrow> flowsto (X0 \<union> Z) (CX \<union> CZ) (Y \<union> W)"
  by (fastforce simp: flowsto_def dest: bspec)

lemma flowsto_inter1: "flowsto X0 CX Y \<Longrightarrow> flowsto (X0 \<inter> Z) CX Y"
  and flowsto_inter2: "flowsto X0 CX Y \<Longrightarrow> flowsto (Z \<inter> X0) CX Y"
  by (auto simp: flowsto_def)

lemma flowsto_trans_Un: "flowsto X0 CX (Y \<union> Z) \<Longrightarrow> flowsto Y CY W \<Longrightarrow> flowsto X0 (CY \<union> CX) (W \<union> Z)"
proof (auto simp: flowsto_def, goal_cases)
  case hyps: (1 x)
  then obtain t where t: "t \<ge> 0" "t \<in> existence_ivl0 x"
    "(\<forall>s\<in>{0..t}. flow0 x s \<in> CX)"
    "flow0 x t \<in> Y \<or> flow0 x t \<in> Z"
    by auto
  from t(4) show ?case
  proof
    assume "flow0 x t \<in> Y"
    with hyps t obtain s where s: "s \<ge> 0" "s \<in> existence_ivl0 (flow0 x t)"
      "(\<forall>s'\<in>{0..s}. flow0 (flow0 x t) s' \<in> CY)"
      "flow0 (flow0 x t) s \<in> W"
      by auto
    show ?case
      apply (rule exI[where x="t + s"])
      apply safe
      subgoal using s t by simp
      subgoal by (intro existence_ivl_trans t s)
      subgoal for s'
        apply (cases "s' \<le> t")
        subgoal using t by simp
        subgoal premises goal1
        proof -
          from goal1 s t have st: "s' = t + (s' - t)" "s' - t \<ge> 0" "s' - t \<le> s" by auto
          then have "flow0 (flow0 x t) (s' - t) \<in> CY"
            using s by auto
          then show ?thesis
            apply (subst (asm) flow_trans[symmetric])
            subgoal using t by simp
            subgoal
            proof -
              from st have "s' + - 1 * t \<in> {0..s}" by auto
              moreover
              have "s' - t = s' + - 1 * t" by auto
              ultimately show "s' - t \<in> existence_ivl0 (flow0 x t)"
                using s
                by (metis contra_subsetD ivl_subset_existence_ivl)
            qed
            subgoal using s by simp
            done
        qed
        done
      using hyps
      subgoal by (force simp add: flow_trans s(2) s(4) t(2))
      done
  next
    assume "flow0 x t \<in> Z"
    thus ?case
      using t
      by (auto simp: intro!: exI[where x=t])
  qed
qed

lemma flowsto_trans:
  assumes "flowsto X0 CX Y" "flowsto Y CY Z"
  shows "flowsto X0 (CX \<union> CY) Z"
proof -
  from assms have "flowsto X0 (CX \<union> CY) (Y \<union> Z)"
    by (metis flowsto_inter2 flowsto_unionI sup_inf_absorb)
  then have "\<not> CY \<subseteq> CX \<union> CY \<or> flowsto X0 (CX \<union> CY) Z"
    using assms by (metis flowsto_trans_Un sup.absorb_iff2 sup.idem)
  then show ?thesis
    by (metis sup.cobounded2)
qed

lemma flowsto_UnE:
  assumes "flowsto X0 CX (Y \<union> Z)"
  obtains X1 X2 where "X0 = X1 \<union> X2" "flowsto X1 CX Y" "flowsto X2 CX Z"
proof -
  let ?X1 = "{x\<in>X0. flowsto {x} CX Y}"
  let ?X2 = "{x\<in>X0. flowsto {x} CX Z}"
  from assms have "X0 = ?X1 \<union> ?X2" "flowsto ?X1 CX Y" "flowsto ?X2 CX Z"
    by (auto simp: flowsto_def)
  thus ?thesis ..
qed

lemma flowsto_subset:
  "flowsto X0 CX Y \<Longrightarrow> W \<subseteq> X0 \<Longrightarrow>Y \<subseteq> Z \<Longrightarrow> CX \<subseteq> CZ \<Longrightarrow> Z \<subseteq> X \<Longrightarrow> CZ \<subseteq> X \<Longrightarrow> flowsto W CZ Z"
  unfolding flowsto_def
  apply safe
  subgoal by force
  subgoal premises prems for x
  proof -
    have f6: "\<forall>A Aa. (A \<subseteq> Aa) = (\<forall>a. (a::'a) \<notin> A \<or> a \<in> Aa)"
      by auto
    then have "x \<in> X0"
      using prems by metis
    then obtain rr :: "'a \<Rightarrow> real" where
      f7: "0 \<le> rr x \<and> rr x \<in> existence_ivl0 x \<and> (\<forall>r. r \<notin> {0..rr x} \<or> flow0 x r \<in> CX) \<and> flow0 x (rr x) \<in> Y"
      using prems by metis
    then have f8: "flow0 x (rr x) \<in> Z"
      using f6 prems by metis
    have "\<forall>a. a \<notin> CX \<or> a \<in> CZ"
      using f6 prems by metis
    then show "\<exists>r\<ge>0. r \<in> existence_ivl0 x \<and> (\<forall>r\<in>{0..r}. flow0 x r \<in> CZ) \<and> flow0 x r \<in> Z"
      using f8 f7 by metis
  qed
  done

lemma flowsto_safeD:
  assumes "flowsto X0 CX Y"
  shows "X0 \<union> CX \<union> Y \<subseteq> X"
  using assms
  by (auto simp: flowsto_def)

lemma flowsto_trans_minus: "flowsto X0 CX Y \<Longrightarrow> flowsto (Y - Z) CZ (Z - Y) \<Longrightarrow> CX \<subseteq> CZ \<Longrightarrow> flowsto X0 CZ Z"
  by (rule flowsto_subset[OF flowsto_trans_Un[of X0 CX "Y - Z" "Z \<inter> Y" CZ "Z - Y"]])
    (auto simp: dest: flowsto_safeD intro: flowsto_subset)

lemma flowpipe_imp_flowsto:
  "flowpipe Y h h CY Z \<Longrightarrow> flowsto Y CY Z"
  unfolding flowpipe_def flowsto_def
  by auto

abbreviation "below_halfspace sctn \<equiv> Collect (le_halfspace sctn)"
lemma below_halfspace_def: "below_halfspace sctn = {x. x \<bullet> normal sctn \<le> pstn sctn}"
  by (auto simp: le_halfspace_def)

lemma connected_le_halfspace:
  assumes "le_halfspace sctn x"
  assumes "x \<in> S" "connected S"
  assumes "S \<inter> plane_of sctn = {}"
  shows "S \<subseteq> Collect (le_halfspace sctn)"
proof -
  note \<open>connected S\<close>
  moreover
  have "open {x. x \<bullet> normal sctn < pstn sctn}" (is "open ?X")
    and "open {x. x \<bullet> normal sctn > pstn sctn}" (is "open ?Y")
    by (auto intro!: open_Collect_less continuous_intros)
  moreover have "S \<subseteq> ?X \<union> ?Y" "?X \<inter> ?Y \<inter> S = {}"
    using assms by (auto simp: plane_of_def)
  ultimately have "?X \<inter> S = {} \<or> ?Y \<inter> S = {}"
    by (rule connectedD)
  then show ?thesis
    using assms
    by (force simp: le_halfspace_def plane_of_def)
qed

lemma connected_not_le_halfspace:
  assumes "\<not>le_halfspace sctn x"
  assumes "x \<in> S" "connected S"
  assumes "S \<inter> plane_of sctn = {}"
  shows "S \<subseteq> Collect (- le_halfspace sctn)"
proof -
  note \<open>connected S\<close>
  moreover
  have "open {x. x \<bullet> normal sctn < pstn sctn}" (is "open ?X")
    and "open {x. x \<bullet> normal sctn > pstn sctn}" (is "open ?Y")
    by (auto intro!: open_Collect_less continuous_intros)
  moreover have "S \<subseteq> ?X \<union> ?Y" "?X \<inter> ?Y \<inter> S = {}"
    using assms by (auto simp: plane_of_def)
  ultimately have "?X \<inter> S = {} \<or> ?Y \<inter> S = {}"
    by (rule connectedD)
  then show ?thesis
    using assms
    by (force simp: le_halfspace_def plane_of_def)
qed

lemma
  inter_Collect_eq_empty:
  assumes "\<And>x. x \<in> X0 \<Longrightarrow> \<not> g x" shows "X0 \<inter> Collect g = {}"
  using assms by auto

definition flowsto_plane where
  "flowsto_plane sctn X0 CX P R \<longleftrightarrow>
    (X0 \<subseteq> X) \<and>
    (P \<subseteq> X) \<and>
    (R \<subseteq> X) \<and>
    (CX \<subseteq> X) \<and>
    flowsto (X0 \<inter> below_halfspace sctn) CX (P \<inter> plane_of sctn \<union> R \<inter> below_halfspace sctn)"

lemma flowsto_plane_safeD:
  "flowsto_plane sctn XS CX PS RS \<Longrightarrow> XS \<union> PS \<union> RS \<union> CX \<subseteq> X"
  by (auto simp: flowsto_plane_def)

lemma flowsto_plane_self:
  assumes "XS \<subseteq> CXS" "CXS \<subseteq> X"
  shows "flowsto_plane sctn XS CXS {} XS"
  using assms
  by (auto simp: flowsto_plane_def intro!: flowsto_self)

lemma flowsto_plane_subset:
  assumes "flowsto_plane sctn XS CXS PS RS"
  assumes "YS \<subseteq> XS" "PS \<subseteq> QS" "RS \<subseteq> TS" "CXS \<subseteq> CYS"
  assumes "QS \<subseteq> X" "TS \<subseteq> X" "CYS \<subseteq> X"
  shows "flowsto_plane sctn YS CYS QS TS"
  unfolding flowsto_plane_def
proof safe
  show safe: "x \<in> YS \<Longrightarrow> x \<in> X" "x \<in> QS \<Longrightarrow> x \<in> X" "x \<in> TS \<Longrightarrow> x \<in> X" "x \<in> CYS \<Longrightarrow> x \<in> X" for x
    using assms by (force dest: flowsto_plane_safeD)+
  from assms have "CXS \<subseteq> X"
    "flowsto (XS \<inter> Collect (le_halfspace sctn)) CXS (PS \<inter> plane_of sctn \<union> RS \<inter> Collect (le_halfspace sctn))"
    by (auto simp: flowsto_plane_def)
  then show "flowsto (YS \<inter> Collect (le_halfspace sctn)) CYS (QS \<inter> plane_of sctn \<union> TS \<inter> Collect (le_halfspace sctn))"
    using assms safe
    apply -
    apply (rule flowsto_subset)
    apply assumption
    by auto
qed

lemma flowsto_plane_subset3:
  assumes "flowsto_plane sctn XS CXS PS RS2"
  assumes "RS2 \<subseteq> RS" "RS \<subseteq> X"
  shows "flowsto_plane sctn XS CXS PS RS"
  using assms
  unfolding flowsto_plane_def
  apply safe
  by (rule flowsto_subset, assumption) auto

lemma flowsto_plane_step:
  assumes "flowsto_plane sctn XS CXS PS RS"
  assumes "flowsto (CS \<inter> Collect (le_halfspace sctn)) CY (CSP \<inter> plane_of sctn \<union> CSR \<inter> below_halfspace sctn)"
  assumes "CSP \<subseteq> X" "CSR \<subseteq> X" "CY \<subseteq> X"
  shows "flowsto_plane sctn XS (CXS \<union> CY) (PS \<union> CSP) (RS - CS \<union> CSR)"
  using assms unfolding flowsto_plane_def
  apply (intro conjI)
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal proof (safe, goal_cases)
    case hyps: (1 )
    from \<open>flowsto (XS \<inter> Collect (le_halfspace sctn)) CXS (PS \<inter> plane_of sctn \<union> RS \<inter> Collect (le_halfspace sctn))\<close>
    have
      "flowsto (XS \<inter> Collect (le_halfspace sctn)) CXS
        (CS \<inter> Collect (le_halfspace sctn) \<union> (PS \<inter> plane_of sctn \<union> (RS - CS) \<inter> Collect (le_halfspace sctn)))"
      apply (rule flowsto_subset)
      using hyps
      by (auto dest: flowsto_safeD)
    from flowsto_trans_Un[OF this hyps(1)]
    have "flowsto (XS \<inter> Collect (le_halfspace sctn)) (CY \<union> CXS)
      (CSP \<inter> plane_of sctn \<union> CSR \<inter> Collect (le_halfspace sctn) \<union>
        (PS \<inter> plane_of sctn \<union> (RS - CS) \<inter> Collect (le_halfspace sctn)))"
      by simp
    then show ?case
      apply (rule flowsto_subset)
      subgoal by force
      subgoal by auto
      subgoal by force
      subgoal using hyps by force
      subgoal using hyps by (auto dest: flowsto_safeD flowsto_plane_safeD)
      done
  qed
  done

lemma flowsto_above_section:
  assumes fp: "flowsto_plane sctn XS CXS YS ZS"
  assumes "flowsto WS CW VS" "connected CW"
  assumes "CW \<inter> plane_of sctn = {}"
  shows "flowsto_plane sctn XS (CXS \<union> CW) YS (ZS - WS \<union> VS)"
proof -
  have "flowsto (WS \<inter> Collect (le_halfspace sctn)) CW
    (VS \<inter> Collect (le_halfspace sctn))"
    unfolding flowsto_def
  proof safe
    fix x assume "x \<in> WS" "le_halfspace sctn x"
    with \<open>flowsto _ _ _\<close>
    obtain t where t: "t \<ge> 0" "t \<in> existence_ivl0 x" "\<forall>s\<in>{0..t}. flow0 x s \<in> CW" "flow0 x t \<in> VS"
      and [simp]: "x \<in> X"
      using \<open>flowsto WS CW VS\<close>
      by (force simp add: flowsto_def)
    moreover
    from \<open>le_halfspace sctn x\<close>
    have "CW \<subseteq> Collect (le_halfspace sctn)"
    proof (rule connected_le_halfspace)
      show "x \<in> CW"
        using t
        by (auto dest!: bspec[where x=0])
    qed fact+
    with t have "flow0 x t \<in> Collect (le_halfspace sctn)"
      using \<open>le_halfspace sctn x\<close>
      by force
    ultimately
    show "\<exists>t\<ge>0. t \<in> existence_ivl0 x \<and> (\<forall>s\<in>{0..t}. flow0 x s \<in> CW) \<and> flow0 x t \<in> VS \<inter> Collect (le_halfspace sctn)"
      by blast
  qed (insert assms, auto dest: flowsto_safeD)
  then have "flowsto (WS \<inter> Collect (le_halfspace sctn)) CW ({} \<inter> plane_of sctn \<union> VS \<inter> Collect (le_halfspace sctn))"
    by simp
  with fp have "flowsto_plane sctn XS (CXS \<union> CW) (YS \<union> {}) (ZS - WS \<union> VS)"
    apply (rule flowsto_plane_step)
    using assms by (auto dest: flowsto_safeD)
  then show ?thesis by simp
qed

lemma flowsto_imp_flowsto_plane:
  assumes "flowsto (X0 \<inter> Collect (le_halfspace sctn)) CX (X1 \<inter> plane_of sctn \<union> X2 \<inter> Collect (le_halfspace sctn))"
  assumes "X0 \<subseteq> X"
  assumes "X1 \<subseteq> X"
  assumes "X2 \<subseteq> X"
  shows "flowsto_plane sctn X0 CX X1 X2"
  unfolding flowsto_plane_def
  using assms
  by (auto dest: flowsto_safeD)

lemma flowsto_intersection:
assumes flowpipe: "flowpipe Y h h CY Z"
  and flowsto: "flowsto X0 CYS (Y \<inter> Collect (le_halfspace sctn) \<union> PS \<inter> plane_of sctn)"
  and"CY \<subseteq> CYr" "CYr \<inter> plane_of sctn \<subseteq> CYi" "CYi \<subseteq> X"
  and safe: "PS \<subseteq> X"
shows "flowsto X0 (CY \<union> CYS) (Z \<inter> Collect (le_halfspace sctn) \<union> (CYi \<union> PS) \<inter> plane_of sctn)"
proof -
  have safe: "Y \<subseteq> X" "Z \<subseteq> X" "CY \<subseteq> X"
    "CYi \<subseteq> X" "CYS \<subseteq> X" using assms
    by (auto dest!: flowsto_safeD flowpipe_safeD)
  moreover
  have "flowsto (Y \<inter> Collect (le_halfspace sctn)) CY (Z \<inter> Collect (le_halfspace sctn) \<union> CYi \<inter> plane_of sctn)"
    unfolding flowsto_def
    using safe
    apply safe
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal for y
      apply (cases "le_halfspace sctn (flow0 y h)")
      subgoal
        using flowpipe unfolding flowpipe_def
        by (force intro!: exI[where x=h])
      subgoal premises prems
      proof -
        let ?f = "\<lambda>t. flow0 y t \<bullet> normal sctn"
        from flowpipe prems
        have y:
          "0 \<le> h" "h \<in> existence_ivl0 y" "flow0 y h \<in> Z" "\<And>h'. 0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> flow0 y h' \<in> CY" "y \<in> X"
          unfolding flowpipe_def
          by auto
        with ivl_subset_existence_ivl[OF \<open>h \<in> _\<close>]
        have "?f 0 \<le> pstn sctn" "pstn sctn \<le> ?f h" "0 \<le> h"
          "\<forall>x. 0 \<le> x \<and> x \<le> h \<longrightarrow> isCont (\<lambda>a. flow0 y a \<bullet> normal sctn) x"
          using y \<open>le_halfspace sctn y\<close> \<open>\<not> le_halfspace sctn (flow0 y h)\<close>
          by (auto simp: le_halfspace_def intro!: continuous_intros flow_continuous)
        from IVT[OF this]
        obtain h' where h': "0 \<le> h'" "h' \<le> h" "flow0 y h' \<in> plane_of sctn"
          by (auto simp: plane_of_def)
        then have "flow0 y h' \<in> CYi" using y \<open>CY \<subseteq> CYr\<close> \<open>CYr \<inter> plane_of sctn \<subseteq> CYi\<close>
          by auto
        then show ?thesis
          using ivl_subset_existence_ivl[OF \<open>h \<in> _\<close>] y h'
          by (auto intro!: exI[where x=h'])
      qed
      done
    done
  then
  have "flowsto (X0) (CY \<union> CYS)
     (Z \<inter> Collect (le_halfspace sctn) \<union> (CYi \<inter> plane_of sctn) \<union> (PS) \<inter> plane_of sctn)"
    apply (intro flowsto_trans_Un[where Y="Y \<inter> Collect (le_halfspace sctn)"])
    apply (rule flowsto_subset[OF flowsto]; insert safe \<open>PS \<subseteq> X\<close>, force)
    apply assumption
    done
  moreover have "Z \<inter> Collect (le_halfspace sctn) \<union> (CYi \<inter> plane_of sctn) \<union> (PS) \<inter> plane_of sctn =
    Z \<inter> Collect (le_halfspace sctn) \<union> (CYi \<union> PS) \<inter> plane_of sctn"
    by auto
  ultimately show ?thesis by simp
qed


lemma flowsto_plane_subset24:
  assumes "flowsto_plane sctn XS CXS PS RS"
  assumes "CXS \<subseteq> CYS" "CYS \<subseteq> X"
  assumes "RS \<subseteq> RS2" "RS2 \<subseteq> X"
  shows "flowsto_plane sctn XS CYS PS RS2"
  using assms(1)
  apply (rule flowsto_plane_subset)
  using assms
  by (auto dest: flowsto_plane_safeD)

lemma
  flowsto_plane_trans:
  assumes "flowsto_plane sctn a b c d"
  assumes "flowsto_plane sctn e I g h"
  shows "flowsto_plane sctn a (b \<union> I) (c \<union> g) (d - e \<union> h)"
  using assms
  by (intro flowsto_plane_step) (auto simp: flowsto_plane_def)

lemma
  flowsto_plane_weaken_intersection:
  assumes "flowsto_plane sctn X0 CX (C \<union> Y) Z"
  shows "flowsto_plane sctn X0 CX C (Z \<union> Y)"
  using assms
  unfolding flowsto_plane_def
  apply safe
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by (rule flowsto_subset, assumption) (auto simp: plane_of_def le_halfspace_def)
  done

end

end
