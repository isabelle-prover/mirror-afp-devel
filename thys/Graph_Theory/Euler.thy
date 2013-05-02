(* Title:  Euler.thy
   Author: Lars Noschinski, TU München
*)
theory Euler imports
  Arc_Walk
  Digraph_Component
  Digraph_Isomorphism
begin

section {* Euler Trails in Digraphs *}

text {*
  In this section we prove the well-known theorem characterizing the
  existence of an Euler Trail in an directed graph
*}

subsection {* Trails and Euler Trails *}

definition (in pre_digraph) trail :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "trail u p v \<equiv> awalk u p v \<and> distinct p"

definition (in pre_digraph) euler_trail :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "euler_trail u p v \<equiv> trail u p v \<and> set p = arcs G \<and> set (awalk_verts u p) = verts G"

lemma (in wf_digraph) rotate_awalkE:
  assumes "awalk u p u" "w \<in> set (awalk_verts u p)"
  obtains q r where "p = q @ r" "awalk w (r @ q) w" "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
proof -
  from assms obtain q r where A: "p = q @ r" and A': "awalk u q w" "awalk w r u"
    by atomize_elim (rule awalk_decomp)
  
  then have B: "awalk w (r @ q) w" by auto

  have C: "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
    using `awalk u p u` A A' by (auto simp: set_awalk_verts_append)

  from A B C show ?thesis ..
qed

lemma (in wf_digraph) rotate_trailE:
  assumes "trail u p u" "w \<in> set (awalk_verts u p)"
  obtains q r where "p = q @ r" "trail w (r @ q) w" "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
  using assms by - (rule rotate_awalkE[where u=u and p=p and w=w], auto simp: trail_def)

lemma (in wf_digraph) rotate_trailE':
  assumes "trail u p u" "w \<in> set (awalk_verts u p)"
  obtains q where "trail w q w" "set q = set p" "set (awalk_verts w q) = set (awalk_verts u p)"
proof -
  from assms obtain q r where "p = q @ r" "trail w (r @ q) w" "set (awalk_verts w (r @ q)) = set (awalk_verts u p)"
    by (rule rotate_trailE)
  then have "set (r @ q) = set p" by auto
  show ?thesis by (rule that) fact+
qed

lemma (in wf_digraph) trail_merge:
  assumes t: "trail u p u" "trail v q v"
  assumes no_common_arcs: "set p \<inter> set q = {}"
  assumes common_vert: "set (awalk_verts u p) \<inter> set (awalk_verts v q) \<noteq> {}"
  obtains w r where "trail w r w" "set r = set p \<union> set q"
proof -
  from common_vert obtain w where "w \<in> set (awalk_verts u p)" "w \<in> set (awalk_verts v q)"
    by auto
  from `trail u p u` `w \<in> set (awalk_verts u p)` obtain p' where
      "trail w p' w" "set p' = set p" by (rule rotate_trailE')
  moreover
  from `trail v q v` `w \<in> set (awalk_verts v q)` obtain q' where
      "trail w q' w" "set q' = set q" by (rule rotate_trailE')
  ultimately
  have p'q': "trail w (p' @ q') w" "set (p' @ q') = set p \<union> set q"
    using no_common_arcs by (auto simp: trail_def awlast_of_awalk)
  then show ?thesis ..
qed 

lemma (in wf_digraph) sym_reachableI_in_awalk:
  assumes walk: "awalk u p v" and
    w1: "w1 \<in> set (awalk_verts u p)" and w2: "w2 \<in> set (awalk_verts u p)"
  shows "w1 \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> w2"
proof -
  from walk w1 obtain q r where "p = q @ r" "awalk u q w1" "awalk w1 r v"
    by (atomize_elim) (rule awalk_decomp)
  then have w2_in: "w2 \<in> set (awalk_verts u q) \<union> set (awalk_verts w1 r)"
    using w2 by (auto simp: set_awalk_verts_append)

  show ?thesis
  proof cases
    assume A: "w2 \<in> set (awalk_verts u q)"
    obtain s where "awalk w2 s w1"
      using awalk_decomp[OF `awalk u q w1` A] by blast
    then have "w2 \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> w1" 
      by (intro reachable_awalkI reachable_mk_symmetricI)
    with symmetric_mk_symmetric show ?thesis by (rule symmetric_reachable)
  next
    assume "w2 \<notin> set (awalk_verts u q)"
    then have A: "w2 \<in> set (awalk_verts w1 r)"
      using w2_in by blast
    obtain s where "awalk w1 s w2"
      using awalk_decomp[OF `awalk w1 r v` A] by blast
    then show "w1 \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> w2" 
      by (intro reachable_awalkI reachable_mk_symmetricI)
  qed
qed

lemma (in wf_digraph) euler_imp_connected:
  assumes "euler_trail u p v" shows "connected G"
proof -
  { fix w1 w2 assume "w1 \<in> verts G" "w2 \<in> verts G"
    then have "awalk u p v " "w1 \<in> set (awalk_verts u p)" "w2 \<in> set (awalk_verts u p)"
      using assms by (auto simp: euler_trail_def trail_def)
    then have "w1 \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> w2" by (rule sym_reachableI_in_awalk) }
  then show "connected G" by (rule connectedI)
qed





subsection {* Arc Balance of Walks *}

definition (in pre_digraph) arc_balance :: "'a \<Rightarrow> 'b awalk \<Rightarrow> int" where
  "arc_balance w p = int (card (in_arcs G w \<inter> set p)) - int (card (out_arcs G w \<inter> set p))"

definition (in pre_digraph) balanced :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "balanced u p v \<equiv>
      if u = v then (\<forall>w \<in> verts G. arc_balance w p = 0)
      else (\<forall>w \<in> verts G. (w \<noteq> u \<and> w \<noteq> v) \<longrightarrow> arc_balance w p = 0)
        \<and> arc_balance u p = -1
        \<and> arc_balance v p = 1"

lemma (in wf_digraph) arc_balance_Cons:
  assumes "trail u (e # es) v"
  shows "arc_balance w (e # es) = arc_balance w [e] + arc_balance w es"
proof -
  from assms have "e \<notin> set es" "e \<in> arcs G" by (auto simp: trail_def)

  with `e \<notin> set es` show ?thesis
    apply (cases "w = tail G e")
    apply (case_tac [!] "w = head G e")
    apply (auto simp: arc_balance_def)
    done
qed

lemma (in wf_digraph) balancedI_trail:
  assumes "trail u p v" shows "balanced u p v"
  using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by (auto simp: balanced_def arc_balance_def trail_def)
next
  case (Cons e es)
  then have A: "balanced (head G e) es v" "u = tail G e" "e \<in> arcs G"
    by (auto simp: awalk_Cons_iff trail_def)

  have C: "\<And>w. arc_balance w [e] = (if w = tail G e \<and> tail G e \<noteq> head G e then -1
      else if w = head G e \<and> tail G e \<noteq> head G e then 1 else 0)"
      using `e \<in> _` by (case_tac "w = tail G e") (auto simp: arc_balance_def)

  show ?case
    using `balanced _ _ _`
    apply (cases "tail G e = head G e")
    apply (case_tac [!] "head G e = v")
    apply (auto simp: balanced_def arc_balance_Cons[OF `trail u _ _`] A C)
    done
qed

lemma (in wf_digraph) trail_arc_balanceE:
  assumes "trail u p v"
  obtains "\<And>w. \<lbrakk> u = v \<or> (w \<noteq> u \<and> w \<noteq> v); w \<in> verts G \<rbrakk>
      \<Longrightarrow> arc_balance w p = 0"
    and "\<lbrakk> u \<noteq> v \<rbrakk> \<Longrightarrow> arc_balance u p = - 1"
    and "\<lbrakk> u \<noteq> v \<rbrakk> \<Longrightarrow> arc_balance v p = 1"
  using balancedI_trail[OF assms] unfolding balanced_def by (intro that) (metis,presburger+)



subsection {* Cycle decomposition of a graph *}

definition (in pseudo_digraph) graph_cycle_decomp :: "'b awalk set \<Rightarrow> bool" where
  "graph_cycle_decomp S \<equiv> (\<forall>p \<in> S. cycle p) \<and> (\<Union>p \<in> S. set p) = arcs G
    \<and> (\<forall>p \<in> S. \<forall>q \<in> S. p \<noteq> q \<longrightarrow> set p \<inter> set q = {})"

definition (in pseudo_digraph) graph_trail_decomp ::  "'b list set \<Rightarrow> bool" where
  "graph_trail_decomp S \<equiv> (\<forall>p \<in> S. \<exists>u. trail u p u)
    \<and> (\<Union>p \<in> S. set p) = arcs G \<and> (\<forall>p \<in> S. \<forall>q \<in> S. p \<noteq> q \<longrightarrow> set p \<inter> set q = {})"


lemma (in wf_digraph) closed_w_imp_cycle:
  assumes "closed_w p" shows "\<exists>p. cycle p"
  using assms
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  then obtain u where *: "awalk u p u" "p \<noteq> []" by (auto simp: closed_w_def)
  show ?thesis
  proof cases
    assume "distinct (tl (awalk_verts u p))"
    with less show ?thesis by (auto simp: closed_w_def cycle_altdef)
  next
    assume A: "\<not>distinct (tl (awalk_verts u p))"
    then obtain e es where "p = e # es" by (cases p) auto
    with A * have **: "awalk (head G e) es u" "\<not>distinct (awalk_verts (head G e) es)"
      by (auto simp: awalk_Cons_iff)
    obtain q r s where "es = q @ r @ s" "\<exists>w. awalk w r w" "closed_w r"
      using awalk_not_distinct_decomp[OF **] by (auto simp: closed_w_def)
    then have "length r < length p" using `p = _` by auto
    then show ?thesis using `closed_w r` by (rule less)
  qed
qed

lemma (in wf_digraph) cycle_imp_apath_eq_awalk:
  assumes "\<And>p. \<not>cycle p" shows "apath u p v = awalk u p v"
proof
  assume A: "awalk u p v"
  show "apath u p v"
  proof (rule ccontr)
    assume B: "\<not>?thesis"
    then have "\<not>distinct (awalk_verts u p)" using A by (auto simp: apath_def)
    with `awalk u p v` obtain r where "closed_w r"
      by (rule awalk_cyc_decompE')
    with assms show False by (auto dest: closed_w_imp_cycle)
  qed
qed (auto intro: awalkI_apath)

lemma GreatestM_finite_setI:
  fixes m :: "'a \<Rightarrow> nat" 
  assumes "S \<noteq> {}" "finite S"
  shows "GreatestM m (\<lambda>x. x \<in> S) \<in> S"
proof -
  from assms obtain x where "x \<in> S" by auto
  moreover
  from assms have "\<forall>y. y \<in> S \<longrightarrow> m y \<le> Max (m ` S)"
    by auto
  then have "\<forall>y. y \<in> S \<longrightarrow> m y < Max (m ` S) + 1"
    by auto
  ultimately show ?thesis
    by (rule GreatestM_natI)
qed

lemma GreatestM_finite_set_le:
  fixes m :: "'a \<Rightarrow> nat" 
  assumes "x \<in> S" "finite S"
  shows "m x \<le> m (GreatestM m (\<lambda>x. x \<in> S))"
proof -
  from assms have "\<forall>y. y \<in> S \<longrightarrow> m y \<le> Max (m ` S)"
    by auto
  then have "\<forall>y. y \<in> S \<longrightarrow> m y < Max (m ` S) + 1"
    by auto
  with assms(1) show ?thesis by (rule GreatestM_nat_le)
qed

lemma zero_less_out_degreeE:
  assumes "0 < out_degree G u" obtains e where "e \<in> arcs G" "tail G e = u"
proof -
  from assms have "out_arcs G u \<noteq> {}" by (auto simp: out_degree_def)
  then obtain e where "e \<in> arcs G" "tail G e = u" by (auto simp: out_arcs_def)
  then show ?thesis ..
qed

lemma (in pseudo_digraph) zero_less_degree_imp_cycle:
  assumes deg: "\<And>u. u \<in> verts G \<Longrightarrow> 0 < out_degree G u"
  assumes "verts G \<noteq> {}"
  shows "\<exists>p. cycle p"
proof (rule ccontr)
  assume A:"\<not>?thesis"
  let ?S = "{p. \<exists>u v. awalk u p v}"
  def p \<equiv> "GreatestM length (\<lambda>p. p \<in> ?S)"
  have "p \<in> ?S" and longest: "\<And>q. q \<in> ?S \<Longrightarrow> length q \<le> length p"
  proof -
    have "finite (\<Union>u \<in> verts G. \<Union>v \<in> verts G. {p. awalk u p v})" (is "finite ?T")
      using A by (simp add: cycle_imp_apath_eq_awalk[symmetric] apaths_finite)
    also have "?T = ?S"
      by (auto intro: awalk_hd_in_verts awalk_last_in_verts)
    finally have fin: "finite ?S" .
    have nonempty: "\<exists>q. q \<in> ?S"
      using assms by (intro exI[where x="[]"]) (auto simp: awalk_Nil_iff)
    with fin show "\<And>q. q \<in> ?S \<Longrightarrow> length q \<le> length p"
      unfolding p_def by (intro GreatestM_finite_set_le) auto
    show "p \<in> ?S" unfolding p_def using nonempty fin by (intro GreatestM_finite_setI) auto
  qed

  from `p \<in> ?S` obtain u v where "awalk u p v" by auto
  then have "0 < out_degree G v"
    by (intro deg awalk_last_in_verts)
  then obtain e where "e \<in> arcs G" "tail G e = v"
    by (elim zero_less_out_degreeE)
  with `awalk u p v` have "awalk u (p @ [e]) (head G e)"
    by (auto simp: awalk_simps awlast_of_awalk)
  then show False using longest[of "p @ [e]"] by (auto simp del: awalk_append_iff)
qed

lemma (in pseudo_digraph) Ex_graph_cycl_decomp:
  assumes deg: "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u"
    "\<And>u. u \<in> verts G \<Longrightarrow> 0 < in_degree G u"
  shows "\<exists>S. graph_cycle_decomp S"
  unfolding graph_cycle_decomp_def
  using assms pseudo_digraph
proof (induct "card (arcs G)" arbitrary: G rule: less_induct)
  case less
  interpret G: pseudo_digraph G by (rule less)
  show ?case
  proof cases
    assume "arcs G = {}" then show ?thesis by (intro exI[where x="{}"]) auto
  next
    assume "arcs G \<noteq> {}"
    then have "verts G \<noteq> {}" by (metis G.head_in_verts all_not_in_conv)
    with less.prems obtain p where "G.cycle p" by atomize_elim (auto intro: G.zero_less_degree_imp_cycle)
    then obtain u where "G.trail u p u" by (auto simp: G.cycle_conv G.trail_def)
    then have awalk_p: "G.awalk u p u" by (auto simp: G.trail_def)

    def H \<equiv> "let E = arcs G - set p in \<lparr> verts = tail G ` E \<union> head G ` E, arcs = E, tail = tail G, head = head G \<rparr>"
    interpret H: pseudo_digraph H by unfold_locales (auto simp: H_def Let_def)
    have "subgraph H G"
      by rule (auto simp: H_def Let_def compatible_def)

    have [simp]: "arcs H = arcs G - set p"
        "verts H = tail G ` (arcs G - set p) \<union> head G ` (arcs G - set p)"
        "head H = head G" "tail H = tail G"
      by (auto simp: H_def Let_def)

    have arcs_psubset: "card (arcs H) < card (arcs G)"
    proof (rule psubset_card_mono)
      from `G.cycle p` have "set p \<noteq> {}" "set p \<subseteq> arcs G"
        by (auto simp: G.cycle_def)
      then show "arcs H \<subset> arcs G"
        by (cases p) auto
    qed auto

    { fix w assume "w \<in> verts H"
      then have "w \<in> verts G" by auto

      have "in_degree H w = card (in_arcs H w)" by (simp add: in_degree_def)
      also have "in_arcs H w = in_arcs G w - set p"
        by auto
      also have "\<dots> = in_arcs G w - (in_arcs G w \<inter> set p)"
        by blast
      also have "card \<dots> = card (out_arcs G w) - card (in_arcs G w \<inter> set p)"
        by (auto simp: card_Diff_subset
          less.prems(1)[OF `w \<in> verts G`, unfolded in_degree_def out_degree_def])
      also have "\<dots> = card (out_arcs G w) - card (out_arcs G w \<inter> set p)"
        using `G.trail u p u` `w \<in> verts G` by (auto simp: G.arc_balance_def elim: G.trail_arc_balanceE)
      also have "\<dots> = card (out_arcs G w - out_arcs G w \<inter> set p)"
         by (auto simp: card_Diff_subset)
      also have "out_arcs G w - out_arcs G w \<inter> set p = out_arcs G w - set p"
         by blast
      also have "\<dots> = out_arcs H w"
        by (auto simp: out_degree_def out_arcs_def)
      also have "card \<dots> = out_degree H w" by (simp add: out_degree_def)
      finally have "in_degree H w = out_degree H w" . }
    note io_degree = this

    { fix w
      assume "w \<in> verts H"
      then have "in_arcs H w \<noteq> {} \<or> out_arcs H w \<noteq> {}"
        by (auto simp: in_arcs_def out_arcs_def)
      with io_degree[OF `w \<in> verts H`] have "0 < in_degree H w"
        by (auto simp: in_degree_def out_degree_def H.finite_in_arcs H.finite_out_arcs) }
    note nonempty_ie = this

    have "\<exists>S. (\<forall>p \<in> S. H.cycle p) \<and> (\<Union>p \<in> S. set p) = arcs H \<and> (\<forall>p \<in> S. \<forall>q \<in> S. p \<noteq> q \<longrightarrow> set p \<inter> set q = {})"
    proof cases
      assume "verts H = {}"
      then have "arcs H = {}" by (metis H.head_in_verts all_not_in_conv)
      then show ?thesis by (intro exI[where x="{}"]) auto
    next
      assume "verts H \<noteq> {}"
      from arcs_psubset io_degree nonempty_ie show ?thesis by (rule less) auto
    qed
    then obtain S where S: "(\<forall>p \<in> S. H.cycle p)" "(\<Union>p \<in> S. set p) = arcs H"
        "(\<forall>p \<in> S. \<forall>q \<in> S. p\<noteq>q \<longrightarrow> set p \<inter> set q = {})" by auto

    show ?case
    proof (intro exI[where x="insert p S"] conjI)
      show "\<forall>q \<in> insert p S. G.cycle q"
        using `subgraph H G` `G.cycle p` S(1) by (auto simp: G.subgraph_cycle)

      show "(\<Union>q \<in> insert p S. set q) = arcs G"
        using S(2) awalk_p by auto

      from S(1) have "\<And>q. q \<in> S \<Longrightarrow> set q \<subseteq> arcs H"
        by (fastforce simp: H.cycle_def)
      then show "\<forall>q\<in>insert p S. \<forall>r\<in>insert p S. q \<noteq> r \<longrightarrow> set q \<inter> set r = {}"
        using S(3) by auto
    qed
  qed
qed

lemma (in wf_digraph) cycle_is_trail: "cycle p \<Longrightarrow> p \<noteq> [] \<and> (\<exists>u. trail u p u)"
  by (auto simp: cycle_conv trail_def)

lemma (in pseudo_digraph) graph_trail_decomp:
  assumes deg: "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u"
    "\<And>u. u \<in> verts G \<Longrightarrow> 0 < in_degree G u"
  obtains S where "graph_trail_decomp S"
proof -
  from assms obtain S where "graph_cycle_decomp S" by atomize_elim (rule Ex_graph_cycl_decomp)
  then have "graph_trail_decomp S"
    unfolding graph_cycle_decomp_def by (auto simp: cycle_is_trail graph_trail_decomp_def)
  then show ?thesis ..
qed

lemma (in pseudo_digraph) graph_trail_decompI:
  assumes "\<And>p. p \<in> S \<Longrightarrow> \<exists>u. trail u p u"
          "arcs G = (\<Union>p \<in> S. set p)"
          "\<And>p q. p \<in> S \<Longrightarrow> q \<in> S \<Longrightarrow> p \<noteq> q \<Longrightarrow> set p \<inter> set q = {}"
  shows "graph_trail_decomp S"
  using assms unfolding graph_trail_decomp_def by auto

lemma (in pseudo_digraph) graph_trail_decompE:
  assumes "graph_trail_decomp S"
  obtains "\<And>p. p \<in> S \<Longrightarrow> \<exists>u. trail u p u"
          "arcs G = (\<Union>p \<in> S. set p)"
          "\<And>p q. p \<in> S \<Longrightarrow> q \<in> S \<Longrightarrow> p \<noteq> q \<Longrightarrow> set p \<inter> set q = {}"
  using assms unfolding graph_trail_decomp_def by auto

lemma (in pseudo_digraph) finite_graph_trail_decomp:
  assumes "graph_trail_decomp S" shows "finite S"
proof -
  have A: "\<And>s t. s \<in> S \<Longrightarrow> t \<in> S \<Longrightarrow> s \<noteq> t \<Longrightarrow> set s \<inter> set t = {}" and
       B: "arcs G = (\<Union>s \<in> S. set s) "
    using assms finite_arcs by (blast elim: graph_trail_decompE)+

  from B have "finite (\<Union>(set ` S))" using finite_arcs by auto
  then have "finite (set ` S)" by (rule finite_UnionD)
  then show "finite S"
  proof (rule finite_imageD)
    { fix s t assume "s \<in> S" "t \<in> S" "set s = set t"
      then have "s = t" using A[of s t] by fastforce }
    then show "inj_on set S" by (rule inj_onI)
  qed
qed



subsection {* Closed Euler Trails *}

lemma (in wf_digraph) awalk_vertex_props:
  assumes "awalk u p v" "p \<noteq> []"
  assumes "\<And>w. w \<in> set (awalk_verts u p) \<Longrightarrow> P w \<or> Q w"
  assumes "P u" "Q v"
  shows "\<exists>e \<in> set p. P (tail G e) \<and> Q (head G e)"
  using assms(2,1,3-)
proof (induct p arbitrary: u rule: list_nonempty_induct)
  case (cons e es)
  show ?case
  proof (cases "P (tail G e) \<and> Q (head G e)")
    case False
    then have "P (head G e) \<or> Q (head G e)"
      using cons.prems(1) cons.prems(2)[of "head G e"]
      by (auto simp: awalk_Cons_iff set_awalk_verts)
    then have "P (tail G e) \<and> P (head G e)"
      using False using cons.prems(1,3) by auto
    
    then have "\<exists>e \<in> set es. P (tail G e) \<and> Q (head G e)"
      using cons by (auto intro: cons simp: awalk_Cons_iff)
    then show ?thesis by auto
  qed auto
qed (simp add: awalk_simps)

lemma (in wf_digraph) connected_verts:
  assumes "connected G" "arcs G \<noteq> {}"
  shows "verts G = tail G ` arcs G \<union> head G ` arcs G"
proof -
  { assume "verts G = {}" then have ?thesis by (auto dest: tail_in_verts) }
  moreover
  { assume "\<exists>v. verts G = {v}"
    then obtain v where "verts G = {v}" by (auto simp: card_Suc_eq)
    moreover
    with `arcs G \<noteq> {}` obtain e where "e \<in> arcs G" "tail G e = v" "head G e = v"
      by (auto dest: tail_in_verts head_in_verts)
    moreover have "tail G ` arcs G \<union> head G ` arcs G \<subseteq> verts G" by auto 
    ultimately have ?thesis by auto }
  moreover
  { assume A: "\<exists>u v. u \<in> verts G \<and> v \<in> verts G \<and> u \<noteq> v"
    { fix u assume "u \<in> verts G"

      interpret S: pair_wf_digraph "mk_symmetric G" by rule
      from A obtain v where "v \<in> verts G" "u \<noteq> v" by blast
      then obtain p where "S.awalk u p v"
        using `connected G` `u \<in> verts G` by (auto elim: connected_awalkE)
      with `u \<noteq> v` obtain e where "e \<in> parcs (mk_symmetric G)" "fst e = u"
        by (metis S.awalk_Cons_iff S.awalk_empty_ends list_exhaust2)
      then obtain e' where "tail G e' = u \<or> head G e' = u" "e' \<in> arcs G"
        by (force simp: parcs_mk_symmetric)
      then have "u \<in> tail G ` arcs G \<union> head G `arcs G" by auto }
    then have ?thesis by auto }
  ultimately show ?thesis by blast
qed

lemma (in wf_digraph) connected_arcs_empty:
  assumes "connected G" "arcs G = {}" "verts G \<noteq> {}" obtains v where "verts G = {v}"
proof (atomize_elim, rule ccontr)
  assume A: "\<not> (\<exists>v. verts G = {v})"

  interpret S: pair_wf_digraph "mk_symmetric G" by rule

  from `verts G \<noteq> {}` obtain u where "u \<in> verts G" by auto
  with A obtain v where "v \<in> verts G" "u \<noteq> v" by auto

  from `connected G` `u \<in> verts G` `v \<in> verts G`
  obtain p where "S.awalk u p v"
    using `connected G` `u \<in> verts G` by (auto elim: connected_awalkE)
  with `u \<noteq> v` obtain e where "e \<in> parcs (mk_symmetric G)"
    by (metis S.awalk_Cons_iff S.awalk_empty_ends list_exhaust2)
  with `arcs G = {}` show False
    by (auto simp: parcs_mk_symmetric)
qed

lemma (in wf_digraph) trail_connected:
  assumes "connected G"
  assumes "trail u p v"
  assumes "set p \<noteq> arcs G"
  shows "\<exists>e. e \<in> arcs G - set p \<and> (tail G e \<in> set (awalk_verts u p) \<or> head G e \<in> set (awalk_verts u p))"
proof (rule ccontr)
  assume A: "\<not>?thesis"

  obtain e where "e \<in> arcs G - set p"
    using assms by (auto simp: trail_def)
  with A have "tail G e \<notin> set (awalk_verts u p)" "tail G e \<in> verts G"
    by auto

  interpret S: pair_wf_digraph "mk_symmetric G" ..

  have "u \<in> verts G" using `trail u p v` by (auto simp: trail_def awalk_hd_in_verts)
  with `tail G e \<in> _` and `connected G`
  obtain q where q: "S.awalk u q (tail G e)"
    by (auto elim: connected_awalkE)

  have "u \<in> set (awalk_verts u p)"
    using `trail u p v` by (auto simp: trail_def set_awalk_verts)

  have "q \<noteq> []" using `u \<in> set _` `tail G e \<notin> _` q by auto

  have "\<exists>e \<in> set q. fst e \<in> set (awalk_verts u p) \<and> snd e \<notin> set (awalk_verts u p)"
    by (rule S.awalk_vertex_props[OF `S.awalk _ _ _` `q \<noteq> []`]) (auto simp: `u \<in> set _` `tail G e \<notin> _`)
  then obtain se' where se': "se' \<in> set q" "fst se' \<in> set (awalk_verts u p)" "snd se' \<notin> set (awalk_verts u p)"
    by auto

  from se' have "se' \<in> parcs (mk_symmetric G)" using q by auto
  then obtain e' where "e' \<in> arcs G" "(tail G e' = fst se' \<and> head G e' = snd se') \<or> (tail G e' = snd se' \<and> head G e' = fst se')"
    by (auto simp: parcs_mk_symmetric)
  moreover
  then have "e' \<notin> set p" using se' `trail u p v`
    by (auto simp: trail_def dest: awalk_verts_arc2 awalk_verts_arc1)
  ultimately show False using se'
    using A by auto
qed

lemma (in pseudo_digraph) zero_less_in_degree_connectedI:
  assumes con: "connected G"
  assumes deg: "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u"
  assumes arcs: "arcs G \<noteq> {}" and u: "u \<in> verts G"
  shows "0 < in_degree G u"
proof -
  interpret S: pair_wf_digraph "mk_symmetric G" by rule

  { assume "verts G = {u}"
    from arcs obtain e where "e \<in> arcs G" by auto
    with `verts G = _` have "e \<in> in_arcs G u"
       by (auto dest: head_in_verts)
    then have ?thesis
      by (auto simp: card_gt_0_iff in_degree_def simp del: in_in_arcs_conv) }
  moreover
  { assume "verts G \<noteq> {u}"
    with u obtain v where "v \<in> verts G" "u \<noteq> v" by blast
    with con u obtain p where "S.awalk u p v"
      by (auto elim: connected_awalkE)
    with `u \<noteq> v` obtain e where "e \<in> parcs (mk_symmetric G)" "fst e = u"
      by (metis S.awalk_Cons_iff S.awalk_empty_ends list_exhaust2)
    then obtain e' where "e' \<in> arcs G" "tail G e' = u \<or> head G e' = u"
      by (auto simp: parcs_mk_symmetric)
    then have "e' \<in> in_arcs G u \<or> e' \<in> out_arcs G u"
      by auto
    then have "0 < in_degree G u \<or> 0 < out_degree G u"
      by (auto simp: in_degree_def out_degree_def card_gt_0_iff
          simp del: in_in_arcs_conv in_out_arcs_conv)
    then have ?thesis using deg u by auto }
  ultimately show ?thesis by fast
qed

lemma (in pseudo_digraph) graph_trail_decomp_insertI:
  assumes gtd: "graph_trail_decomp S"
  assumes t: "trail u p u"
  assumes sets: "set p = (\<Union>s \<in> T. set s)" "T \<subseteq> S"
  shows "graph_trail_decomp (insert p (S - T))" (is "graph_trail_decomp ?S'")
proof (rule graph_trail_decompI)
  fix q assume "q \<in> ?S'" with gtd t show "\<exists>u. trail u q u" by (auto elim: graph_trail_decompE)
next
  show "arcs G = (\<Union>q\<in>?S'. set q)" using gtd sets by (elim graph_trail_decompE) auto
next
  fix q r assume A: "q \<in> ?S'" "r \<in> ?S'" "q \<noteq> r"

  { fix q assume B: "q \<in> S - T" have "set p \<inter> set q = {}"
    proof (rule ccontr)
      assume "\<not>?thesis"
      then obtain p' where "p' \<in> T" "set p' \<inter> set q \<noteq> {}" using sets by auto
      then have "p' \<in> S" "q \<in> S" "p' \<noteq> q" "set p' \<inter> set q \<noteq> {}" using B sets by auto
      then show False using gtd by (blast elim: graph_trail_decompE)
    qed }
  with gtd A show "set q \<inter> set r = {}" by (blast elim!: graph_trail_decompE)
qed

theorem (in pseudo_digraph) closed_euler1:
  assumes con: "connected G" and verts: "verts G \<noteq> {}"
  assumes deg: "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u"
  shows "\<exists>u p. euler_trail u p u"
proof (cases "arcs G = {}")
  case True
  with con obtain v where "verts G = {v}"
    using verts by (rule connected_arcs_empty)
  with True show ?thesis
    by (auto simp: euler_trail_def trail_def awalk_Nil_iff)
next
  case False

  obtain S where gtd: "graph_trail_decomp S"
  proof -
    have "\<And>u. u \<in> verts G \<Longrightarrow> 0 < in_degree G u"
      using con deg False by (rule zero_less_in_degree_connectedI)
    with deg show ?thesis
      by (rule graph_trail_decomp) (auto intro: that)
  qed

  from gtd have "finite S" by (rule finite_graph_trail_decomp)
  then show ?thesis
    using `graph_trail_decomp S`
  proof (induct "card S" arbitrary: S)
    case 0
    then have "arcs G = {}" by (auto elim: graph_trail_decompE)
    with con `verts G \<noteq> {}` show ?case
      by (elim connected_arcs_empty) (auto simp: euler_trail_def trail_def awalk_Nil_iff)
  next
    case (Suc n)

    from `Suc n = card S`[symmetric] `finite S` obtain s where "s \<in> S"
      by (auto simp: card_Suc_eq)
    then obtain u where "trail u s u" using `graph_trail_decomp S`
      by (blast elim: graph_trail_decompE)

    show ?case
    proof (cases "set s = arcs G")
      case True
      with `arcs G \<noteq> {}` have "\<And>v. v \<in> verts G \<Longrightarrow> v \<in> set (awalk_verts u s)"
        using `trail u s u` con unfolding trail_def 
        by (auto simp: set_awalk_verts connected_verts)
      then have "euler_trail u s u" using True `trail u s u`
        by (auto simp: euler_trail_def trail_def) 
      then show ?thesis by blast
    next
      case False
      from con `trail u s u` False
      obtain e where e: "e \<in> arcs G - set s" "(tail G e \<in> set (awalk_verts u s) \<or> head G e \<in> set (awalk_verts u s))"
        by atomize_elim (rule trail_connected)
      from e(1) obtain v t where "t \<in> S" "e \<in> set t" "trail v t v"
        using `graph_trail_decomp S` unfolding graph_trail_decomp_def
        by blast

      have "s \<noteq> t" using e(1) `e \<in> set t` by auto

      note `trail u s u` `trail v t v`
      moreover
      have "set s \<inter> set t = {}"
        using `s \<noteq> t` `s \<in> S` `t \<in> S` `graph_trail_decomp S`
        by (elim graph_trail_decompE) auto
      moreover
      have "set (awalk_verts u s) \<inter> set (awalk_verts v t) \<noteq> {}"
        using e(2) `e \<in> set t` `trail u s u` `trail v t v`
        by (auto simp: set_awalk_verts trail_def)
      ultimately
      obtain w p where "trail w p w" "set p = set s \<union> set t"
        by (rule trail_merge)

      let ?T = "insert p (S - {s,t})"

      have "n = card ?T"
      proof -
        have "p \<notin> S - {s,t}"
          using `e \<in> set t` `set p = set s \<union> set t` `t \<in> S` `graph_trail_decomp S`
          by (blast elim: graph_trail_decompE)
        have "{s, t} \<subseteq> S" "card {s,t} = 2"
          using `s \<in> S` `t \<in> S` `s \<noteq> t` by (auto simp: eval_nat_numeral)
        with `finite S` have "2 \<le> card S" by (metis card_mono)
        then show ?thesis
          using `finite S` `Suc n = _` `s \<noteq> t` `p \<notin> S - {s,t}` `s \<in> S` `t \<in> S`
          by simp
      qed
      moreover
      have "finite ?T" using `finite S` by auto
      moreover
      have "graph_trail_decomp ?T"
        using `graph_trail_decomp S` `trail w p w`  `set p = set s \<union> set t` `s \<in> S` `t \<in> S`
        by (auto intro: graph_trail_decomp_insertI)
      ultimately
      show ?thesis
        by (rule Suc.hyps)
    qed
  qed
qed

lemma (in wf_digraph) closed_euler_imp_eq_degree:
  assumes "euler_trail u p u"
  assumes "v \<in> verts G"
  shows "in_degree G v = out_degree G v"
proof -
  from assms have "balanced u p u" "set p = arcs G"
    unfolding euler_trail_def by (auto simp: balancedI_trail)
  with assms have "arc_balance v p = 0"
    unfolding balanced_def by auto
  moreover
  from `set p = _` have "in_arcs G v \<inter> set p = in_arcs G v" "out_arcs G v \<inter> set p = out_arcs G v"
    by (auto intro: in_arcs_in_arcs out_arcs_in_arcs)
  ultimately
  show ?thesis unfolding arc_balance_def in_degree_def out_degree_def by auto
qed



theorem (in pseudo_digraph) closed_euler2:
  assumes "euler_trail u p u"
  shows "connected G" "verts G \<noteq> {}"
    and "\<And>u. u \<in> verts G \<Longrightarrow> in_degree G u = out_degree G u" (is "\<And>u. _ \<Longrightarrow> ?eq_deg u")
proof -
  from assms show "connected G" by (rule euler_imp_connected)
next
  from assms show "verts G \<noteq> {}" by (auto simp: euler_trail_def)
next
  fix v assume A: "v \<in> verts G"
  with assms show "?eq_deg v" by (rule closed_euler_imp_eq_degree)
qed

corollary (in pseudo_digraph) closed_euler:
  "(\<exists>u p. euler_trail u p u) \<longleftrightarrow> connected G \<and> verts G \<noteq> {} \<and> (\<forall>u \<in> verts G. in_degree G u = out_degree G u)"
  by (auto dest: closed_euler1 closed_euler2)



subsection {* Open euler trails *}

text {*
  Intuitively, a graph has an open euler trail if and only if it is possible to add
  an arc, such that the resulting graph has a closed euler trail. However, this is
  not true in our formalization, as the arc type @{typ 'b} might be finite:

  Consider for example the graph
  @{term "\<lparr> verts = {0,1}, arcs = {()}, tail = \<lambda>_. 0, head = \<lambda>_. 1 \<rparr>"}. This graph
  obviously has an open euler trail, but we cannot add another arc, as we already
  exhausted the universe.

  However, for each @{term "pseudo_digraph G"} there exist an isomorphic graph
  @{term H} with arc type @{typ "'a \<times> nat \<times> 'a"}. Hence, we first characterize
  the existence of euler trail for the infinite arc type @{typ "'a \<times> nat \<times> 'a"}
  and transfer that result back to arbitrary arc types.
*}

lemma open_euler_infinite_label:
  fixes G :: "('a, 'a \<times> nat \<times> 'a) pre_digraph"
  assumes "pseudo_digraph G"
  assumes [simp]: "tail G = fst" "head G = snd o snd"
  assumes con: "connected G"
  assumes uv: "u \<in> verts G" "v \<in> verts G"
  assumes deg: "\<And>w. \<lbrakk>w \<in> verts G; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow> in_degree G w = out_degree G w"
  assumes deg_in: "in_degree G u + 1 = out_degree G u"
  assumes deg_out: "out_degree G v + 1 = in_degree G v"
  shows "\<exists>p. pre_digraph.euler_trail G u p v \<and> u \<noteq> v"
proof -
  def [simp]: label \<equiv> "fst o snd :: 'a \<times> nat \<times> 'a \<Rightarrow> nat"

  interpret pseudo_digraph G by fact

  have "finite (label ` arcs G)" by auto
  moreover have "\<not>finite (UNIV :: nat set)" by blast
  ultimately obtain l where "l \<notin> label ` arcs G" by atomize_elim (rule ex_new_if_finite)

  from deg_in deg_out have "u \<noteq> v" by auto

  let ?e = "(v,l,u)"

  have e_notin:"?e \<notin> arcs G"
    using `l \<notin> _` by (auto simp: image_def)

  def H \<equiv> "\<lparr> verts = verts G , arcs = arcs G \<union> {?e}, tail = fst, head = snd o snd \<rparr>"
    -- "We define a graph which has an closed euler trail"
  interpret H: pseudo_digraph H
    using uv by unfold_locales (auto simp: H_def dest: wellformed)

  have [simp]: "verts H = verts G" "tail H = fst" "head H = snd o snd"
    and arcs_H: "arcs H = arcs G \<union> {?e}" by (auto simp: H_def)
  have [simp]: "compatible G H" by (simp add: compatible_def)

  have "\<exists>u p. H.euler_trail u p u"
  proof (rule H.closed_euler1)
    show "connected H"
    proof (rule H.connectedI)
      interpret sH: pair_pseudo_digraph "mk_symmetric H" ..
      fix u v assume "u \<in> verts H" "v \<in> verts H"
      with con have "u \<rightarrow>\<^isup>*\<^bsub>mk_symmetric G\<^esub> v" by (auto simp: connected_def)
      moreover
      have "subgraph G H" by (auto simp: subgraph_def H_def compatible_def) unfold_locales
      ultimately show "u \<rightarrow>\<^isup>*\<^bsub>with_proj (mk_symmetric H)\<^esub> v"
        by (blast intro: sH.reachable_mono subgraph_mk_symmetric)
    qed
  next
    show "verts H \<noteq> {}" using uv by auto
  next
    fix w assume "w \<in> verts H"
    then have "w \<in> verts G" by simp
    { assume [simp]: "w = u"
      have "in_degree H w = card (in_arcs H w)" unfolding in_degree_def ..
      also have "in_arcs H w = in_arcs G u \<union> {?e}"
        by (auto simp: H_def)
      also have "card \<dots> = out_degree G u"
        unfolding deg_in[symmetric] in_degree_def using e_notin by (auto simp: finite_in_arcs)
      also have "\<dots> = out_degree H w"
        unfolding out_degree_def using `u \<noteq> v` e_notin
        by (intro arg_cong[where f=card]) (auto, auto simp: H_def)
      finally have "in_degree H w = out_degree H w" . }
    moreover
    { assume [simp]: "w = v"
      have "in_degree H w = in_degree G v"
        unfolding in_degree_def out_arcs_def using `u \<noteq> v` e_notin
        by (intro arg_cong[where f=card]) (auto, auto simp: H_def)
      also have "\<dots> = out_degree G v + 1" by (simp only: deg_out)
      also have "\<dots> = card (insert ?e (out_arcs G v))"
        unfolding out_degree_def using e_notin by (auto simp: finite_out_arcs)
      also have "insert ?e (out_arcs G v) = out_arcs H w"
        by (auto simp: H_def)
      finally have "in_degree H w = out_degree H w" unfolding out_degree_def . }
    moreover
    { assume w: "w \<noteq> u" "w \<noteq> v"
      have "in_degree H w = card (in_arcs H w)" by (simp add: in_degree_def)
      also have "in_arcs H w = in_arcs G w" using w by (auto simp: in_arcs_def H_def)
      also have "card \<dots> = card (out_arcs G w)"
        using deg[OF `w \<in> verts G`] w by (simp add: in_degree_def out_degree_def)
      also have "out_arcs G w = out_arcs H w" using w by (auto simp: out_arcs_def H_def)
      also have "card \<dots> = out_degree H w" by (simp add: out_degree_def)
      finally have "in_degree H w = out_degree H w" . }
    ultimately 
    show "in_degree H w = out_degree H w"
      by fast
  qed

  then obtain w p where Het: "H.euler_trail w p w" by blast
  then have "?e \<in> set p" by (auto simp: pre_digraph.euler_trail_def H_def)
  then obtain q r where p_decomp: "p = q @ [?e] @ r"
    by (auto simp: in_set_conv_decomp)
    -- "We show now that removing the additional arc of @{term H}
      from p yields an euler trail in G "

  have "euler_trail u (r @ q) v"
  proof (unfold euler_trail_def, intro conjI)
    from Het have Ht': "H.trail (tail G ?e) (?e # r @ q) (tail G ?e)"
      by (auto simp: H.euler_trail_def H.trail_def H.awalk_Cons_iff p_decomp)
    then have "H.trail u (r @ q) v" "?e \<notin> set (r @ q)"
      by (auto simp: H.trail_def H.awalk_Cons_iff)
    then show t': "trail u (r @ q) v"
      by (auto simp: trail_def H.trail_def awalk_def H.awalk_def arcs_H compatible_cas[OF `compatible G H`])

    show "set (r @ q) = arcs G"
    proof -
      have "arcs G = arcs H - {?e}" using e_notin by (auto simp: H_def)
      also have "arcs H = set p" using Het
        by (auto simp: pre_digraph.euler_trail_def pre_digraph.trail_def)
      finally show ?thesis using `?e \<notin> set _` by (auto simp: p_decomp)
    qed
    
    show "set (awalk_verts u (r @ q)) = verts G"
    proof -
      have *: "cas v [(v,l,u)] u" "cas u r w" "cas w q v"
            "awlast u r = w" "awlast v [(v,l,u)] = u"
        using Het Ht' unfolding H.euler_trail_def H.trail_def
        by (auto simp: H.awalk_simps uv p_decomp
          compatible_cas[OF `compatible G H`] compatible_awalk_verts[OF `compatible G H`])
      have "set (awalk_verts u (r @ q)) = set (awalk_verts (tail G ?e) ([?e] @ r @ q))"
        using t' by (auto simp: trail_def simp del: awalk_append_iff)
      also have "\<dots> = set (awalk_verts w p)"
        using * unfolding p_decomp by (auto simp: set_awalk_verts_append_cas)
      finally
      show ?thesis using Het
        unfolding H.euler_trail_def by (simp add: compatible_awalk_verts[OF `compatible G H`])
    qed
  qed
  with `u \<noteq> v` show ?thesis by blast
qed

context wf_digraph begin

lemma trail_relabelI:
  assumes t: "trail u p v"
    and hom: "digraph_isomorphism hom"
  shows "pre_digraph.trail (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from t hom have i: "inj_on (iso_arcs hom) (set p)"
     unfolding trail_def digraph_isomorphism_def by (auto dest:subset_inj_on[where A="set p"])
  then have "distinct (map (iso_arcs hom) p) = distinct p"
    by (auto simp: distinct_map dest: inj_onD)
  with t hom show ?thesis
    by (auto simp: pre_digraph.trail_def awalk_relabelI)
qed

lemma euler_trail_relabelI:
  assumes t: "euler_trail u p v"
    and hom: "digraph_isomorphism hom"
  shows "pre_digraph.euler_trail (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  from t have "awalk u p v" by (auto simp: euler_trail_def trail_def)
  with assms show ?thesis
   by (auto simp: pre_digraph.euler_trail_def trail_relabelI arcs_app_iso awalk_verts_app_iso_eq)
qed

end

theorem (in pseudo_digraph) open_euler1:
  assumes "connected G"
  assumes "u \<in> verts G" "v \<in> verts G"
  assumes "\<And>w. \<lbrakk>w \<in> verts G; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow> in_degree G w = out_degree G w"
  assumes "in_degree G u + 1 = out_degree G u"
  assumes "out_degree G v + 1 = in_degree G v"
  obtains p where "euler_trail u p v"
proof -
  obtain f and n :: nat where "f ` arcs G = {i. i < n}"
      and i: "inj_on f (arcs G)"
    by atomize_elim (rule finite_imp_inj_to_nat_seg, auto)

  def iso_f \<equiv> "\<lparr> iso_verts = id, iso_arcs = (\<lambda>a. (tail G a, f a, head G a)),
    head = snd o snd, tail = fst \<rparr>"
  have [simp]: "iso_verts iso_f = id" "iso_head iso_f = snd o snd" "iso_tail iso_f = fst"
    unfolding iso_f_def by auto
  have di_iso_f: "digraph_isomorphism iso_f" unfolding digraph_isomorphism_def iso_f_def
    by (auto intro: inj_onI dest: inj_onD[OF i])

  let ?H = "app_iso iso_f G"
  interpret H: pseudo_digraph ?H using di_iso_f ..

  have "\<exists>p. H.euler_trail u p v \<and> u \<noteq> v"
    using assms i
    by (intro open_euler_infinite_label)
       (auto simp: connectedI_app_iso[OF _ di_iso_f] app_iso_eq[OF di_iso_f, simplified])
  then obtain p where Het: "H.euler_trail u p v" by blast

  let ?g = "the_inv_into (arcs G) f"
  def iso_g \<equiv> "\<lparr> iso_verts = id, iso_arcs = (\<lambda>(_ :: 'a,a,_ :: 'a). ?g a), head = head G, tail = tail G \<rparr>"
  have [simp]: "iso_verts iso_g = id" "iso_head iso_g = head G" "iso_tail iso_g = tail G"
    unfolding iso_g_def by auto
  have di_iso_g: "H.digraph_isomorphism iso_g"
    unfolding H.digraph_isomorphism_def iso_g_def using i
    by (auto simp: arcs_app_iso iso_f_def the_inv_into_f_f split: prod.splits intro: inj_onI)

  from Het di_iso_g
  have "pre_digraph.euler_trail (app_iso iso_g ?H) (iso_verts iso_g u) (map (iso_arcs iso_g) p) (iso_verts iso_g v)"
    by (rule H.euler_trail_relabelI)
  also have "app_iso iso_g (app_iso iso_f G) = G"
    by (rule pre_digraph.equality)
       (auto simp: arcs_app_iso iso_f_def iso_g_def the_inv_into_f_f[OF i] image_image intro: rev_image_eqI)
  finally show ?thesis
    by simp rule
qed

theorem (in pseudo_digraph) open_euler2:
  assumes et: "euler_trail u p v" and "u \<noteq> v"
  shows "connected G \<and>
    (\<forall>w \<in> verts G. u \<noteq> w \<longrightarrow> v \<noteq> w \<longrightarrow> in_degree G w = out_degree G w) \<and>
    in_degree G u + 1 = out_degree G u \<and>
    out_degree G v + 1 = in_degree G v"
proof -
  from et have *: "trail u p v" "u \<in> verts G" "v \<in> verts G"
    by (auto simp: euler_trail_def trail_def awalk_hd_in_verts)

  from et have [simp]: "\<And>u. card (in_arcs G u \<inter> set p) = in_degree G u"
      "\<And>u. card (out_arcs G u \<inter> set p) = out_degree G u"
    by (auto simp: in_degree_def out_degree_def euler_trail_def intro: arg_cong[where f=card])

  from assms * show ?thesis
    by (auto simp: arc_balance_def elim: trail_arc_balanceE
        intro: euler_imp_connected)
qed

corollary (in pseudo_digraph) open_euler:
  "(\<exists>u p v. euler_trail u p v \<and> u \<noteq> v) \<longleftrightarrow>
    connected G \<and> (\<exists>u v. u \<in> verts G \<and> v \<in> verts G \<and>
      (\<forall>w \<in> verts G. u \<noteq> w \<longrightarrow> v \<noteq> w \<longrightarrow> in_degree G w = out_degree G w) \<and>
      in_degree G u + 1 = out_degree G u \<and>
      out_degree G v + 1 = in_degree G v)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain u p v where *: "euler_trail u p v" "u \<noteq> v"
    by auto
  then have "u \<in> verts G" "v \<in> verts G"
    by (auto simp: euler_trail_def trail_def awalk_hd_in_verts)
  then show ?R using open_euler2[OF *] by blast
next
  assume ?R
  then obtain u v where *:
    "connected G" "u \<in> verts G" "v \<in> verts G"
    "\<And>w. \<lbrakk>w \<in> verts G; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow> in_degree G w = out_degree G w"
    "in_degree G u + 1 = out_degree G u"
    "out_degree G v + 1 = in_degree G v"
    by blast
  then have "u \<noteq> v" by auto
  from * show ?L by (rule open_euler1) (assumption | metis `u \<noteq> v`)+
qed



end
