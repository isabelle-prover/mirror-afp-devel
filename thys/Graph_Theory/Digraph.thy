(* Title:  Digraph.thy
   Author: Lars Noschinski, TU München
   Author: René Neumann
*)

theory Digraph
imports
  Main
  Rtrancl_On
  Stuff
begin

section {* Digraphs *}

record ('a,'b) pre_digraph =
  verts :: "'a set"
  arcs :: "'b set"
  tail :: "'b \<Rightarrow> 'a"
  head :: "'b \<Rightarrow> 'a"

definition arc_to_ends :: "('a,'b) pre_digraph \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'a" where
  "arc_to_ends G e \<equiv> (tail G e, head G e)"

locale pre_digraph =
  fixes G :: "('a, 'b) pre_digraph" (structure)

locale wf_digraph = pre_digraph +
  assumes tail_in_verts[simp]: "e \<in> arcs G \<Longrightarrow> tail G e \<in> verts G"
  assumes head_in_verts[simp]: "e \<in> arcs G \<Longrightarrow> head G e \<in> verts G"
begin

lemmas wellformed = tail_in_verts head_in_verts

end

text {*
  The definition we give here differs from the one given in \cite{bangjensen2009digraphs}
  in that we do not exclude the null graph. For a discussion of that topic,
  see also \cite{harary1974nullgraph}.
*}
locale pseudo_digraph = wf_digraph +
  assumes finite_verts[simp]: "finite (verts G)"
    and finite_arcs[simp]: "finite (arcs G)"

definition arcs_ends :: "('a,'b) pre_digraph \<Rightarrow> ('a \<times> 'a) set" where
  "arcs_ends G \<equiv> arc_to_ends G ` arcs G"

definition symmetric :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "symmetric G \<equiv> sym (arcs_ends G)"

locale digraph = pseudo_digraph +
  assumes no_loops: "e \<in> arcs G \<Longrightarrow> tail G e \<noteq> head G e"
  assumes no_multi_arcs: "\<And>e1 e2. \<lbrakk>e1 \<in> arcs G; e2 \<in> arcs G;
     arc_to_ends G e1 = arc_to_ends G e2\<rbrakk> \<Longrightarrow> e1 = e2"

text {*
  We model graphs as symmetric digraphs. This is fine for many purposes,
  but not for all. For example, the path $a,b,a$ is considered to be a cycle
  in a digraph (and hence in a symmetric digraph), but not in an undirected
  graph.
 *}
locale pseudo_graph = pseudo_digraph +
  assumes sym_arcs[intro]: "symmetric G"

locale graph = digraph + pseudo_graph

lemma (in wf_digraph) pseudo_digraphI[intro]:
  assumes "finite (verts G)"
  assumes "finite (arcs G)"
  shows "pseudo_digraph G"
using assms by unfold_locales

lemma (in digraph) graphI[intro]:
  assumes "symmetric G"
  shows "graph G"
using assms by unfold_locales



definition (in wf_digraph) arc :: "'b \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "arc e uv \<equiv> e \<in> arcs G \<and> tail G e = fst uv \<and> head G e = snd uv"


lemma (in pseudo_digraph) pseudo_digraph: "pseudo_digraph G"
  by unfold_locales

lemma arcs_ends_conv: "arcs_ends G = (\<lambda>e. (tail G e, head G e)) ` arcs G"
  by (auto simp: arc_to_ends_def arcs_ends_def)

lemma symmetric_conv: "symmetric G \<longleftrightarrow> (\<forall>e1 \<in> arcs G. \<exists>e2 \<in> arcs G. tail G e1 = head G e2 \<and> head G e1 = tail G e2)"
  unfolding symmetric_def arcs_ends_conv sym_def by auto

lemma arcs_ends_symmetric:
  assumes "symmetric G"
  shows "(u,v) \<in> arcs_ends G \<Longrightarrow> (v,u) \<in> arcs_ends G"
  using assms unfolding symmetric_def sym_def by auto



subsection {* Reachability *}

abbreviation dominates :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<index> _" [100,100] 40) where
  "dominates G u v \<equiv> (u,v) \<in> arcs_ends G"

abbreviation reachable1 :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^isup>+\<index> _" [100,100] 40) where
  "reachable1 G u v \<equiv> (u,v) \<in> (arcs_ends G)^+"

definition reachable :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^isup>*\<index> _" [100,100] 40) where
  "reachable G u v \<equiv> (u,v) \<in> rtrancl_on (verts G) (arcs_ends G)"

lemma reachableE[elim]:
  assumes "u \<rightarrow>\<^bsub>G\<^esub> v"
  obtains e where "e \<in> arcs G" "tail G e = u" "head G e = v"
using assms by (auto simp add: arcs_ends_conv)

lemma (in digraph) adj_not_same:
  assumes "a \<rightarrow> a" shows "False"
  using assms by (rule reachableE) (auto dest: no_loops)

lemma reachable_in_vertsE:
  assumes "u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v" obtains "u \<in> verts G" "v \<in> verts G"
  using assms unfolding reachable_def by induct auto

lemma symmetric_reachable:
  assumes "symmetric G" "v \<rightarrow>\<^isup>*\<^bsub>G\<^esub> w" shows "w \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v"
proof -
  have "sym (rtrancl_on (verts G) (arcs_ends G))"
    using assms by (auto simp add: symmetric_def dest: rtrancl_on_sym)
  then show ?thesis using assms unfolding reachable_def by (blast elim: symE)
qed

lemma reachable_rtranclI:
  "u \<rightarrow>\<^isup>*\<^bsub>G \<^esub> v \<Longrightarrow> (u, v) \<in> (arcs_ends G)\<^sup>*"
  unfolding reachable_def by (rule rtrancl_on_rtranclI)


context wf_digraph begin

lemma adj_in_verts:
  assumes "u \<rightarrow>\<^bsub>G\<^esub> v" shows "u \<in> verts G" "v \<in> verts G"
  using assms unfolding arcs_ends_conv by auto

lemma reachable_refl [intro!, Pure.intro!, simp]: "v \<in> verts G \<Longrightarrow> v \<rightarrow>\<^isup>* v"
  unfolding reachable_def by auto

lemma adj_reachable_trans[trans]:
  assumes "a \<rightarrow>\<^bsub>G\<^esub> b" "b \<rightarrow>\<^isup>*\<^bsub>G\<^esub> c" shows "a \<rightarrow>\<^isup>*\<^bsub>G\<^esub> c"
  using assms by (auto simp: reachable_def intro: converse_rtrancl_on_into_rtrancl_on adj_in_verts)

lemma reachable_adj_trans[trans]:
  assumes "a \<rightarrow>\<^isup>*\<^bsub>G\<^esub> b" "b \<rightarrow>\<^bsub>G\<^esub> c" shows "a \<rightarrow>\<^isup>*\<^bsub>G\<^esub> c"
  using assms by (auto simp: reachable_def intro: rtrancl_on_into_rtrancl_on adj_in_verts)

lemma reachable_adjI [intro, simp]: "u \<rightarrow> v \<Longrightarrow> u \<rightarrow>\<^isup>* v"
  by (auto intro: adj_reachable_trans adj_in_verts)

lemma reachable_trans[trans]:
  assumes "u \<rightarrow>\<^isup>*v" "v \<rightarrow>\<^isup>* w" shows "u \<rightarrow>\<^isup>* w"
  using assms unfolding reachable_def by (rule rtrancl_on_trans)

lemma converse_reachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v"
    and cases: "v \<in> verts G \<Longrightarrow> P v"
       "\<And>x y. \<lbrakk>x \<rightarrow>\<^bsub>G\<^esub> y; y \<rightarrow>\<^isup>*\<^bsub>G\<^esub> v; P y\<rbrakk> \<Longrightarrow> P x"
  shows "P u"
  using assms unfolding reachable_def by (rule converse_rtrancl_on_induct) auto

lemma reachable_in_verts:
  assumes "u \<rightarrow>\<^isup>* v" shows "u \<in> verts G" "v \<in> verts G"
  using assms by induct (simp_all add: adj_in_verts)

lemma reachable1_in_verts:
  assumes "u \<rightarrow>\<^isup>+ v" shows "u \<in> verts G" "v \<in> verts G"
  using assms
  by induct (simp_all add: adj_in_verts)

lemma reachable1_reachable[intro]:
  "v \<rightarrow>\<^isup>+ w \<Longrightarrow> v \<rightarrow>\<^isup>* w"
  unfolding reachable_def
  by (rule rtrancl_consistent_rtrancl_on) (simp_all add: reachable1_in_verts adj_in_verts)

lemmas reachable1_reachableE[elim] = reachable1_reachable[elim_format]

lemma reachable_neq_reachable1[intro]:
  assumes reach: "v \<rightarrow>\<^isup>* w"
  and neq: "v \<noteq> w"
  shows "v \<rightarrow>\<^isup>+ w"
proof -
  from reach have "(v,w) \<in> (arcs_ends G)^*" by (rule reachable_rtranclI)
  with neq show ?thesis by (auto dest: rtranclD)
qed

lemmas reachable_neq_reachable1E[elim] = reachable_neq_reachable1[elim_format]

lemma reachable1_reachable_trans [trans]:
  "u \<rightarrow>\<^isup>+ v \<Longrightarrow> v \<rightarrow>\<^isup>* w \<Longrightarrow> u \<rightarrow>\<^isup>+ w"
by (metis trancl_trans reachable_neq_reachable1)

lemma reachable_reachable1_trans [trans]:
  "u \<rightarrow>\<^isup>* v \<Longrightarrow> v \<rightarrow>\<^isup>+ w \<Longrightarrow> u \<rightarrow>\<^isup>+ w"
by (metis trancl_trans reachable_neq_reachable1)

end




subsection {* Degrees of vertices *}

definition in_arcs :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "in_arcs G v \<equiv> {e \<in> arcs G. head G e = v}"

definition out_arcs :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "out_arcs G v \<equiv> {e \<in> arcs G. tail G e = v}"

definition in_degree :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> nat" where
  "in_degree G v \<equiv> card (in_arcs G v)"

definition out_degree :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> nat" where
  "out_degree G v \<equiv> card (out_arcs G v)"

lemma (in pseudo_digraph) finite_in_arcs[intro]:
  "finite (in_arcs G v)"
  unfolding in_arcs_def by auto

lemma (in pseudo_digraph) finite_out_arcs[intro]:
  "finite (out_arcs G v)"
  unfolding out_arcs_def by auto

lemma in_in_arcs_conv[simp]:
  "e \<in> in_arcs G v \<longleftrightarrow> e \<in> arcs G \<and> head G e = v"
  unfolding in_arcs_def by auto

lemma in_out_arcs_conv[simp]:
  "e \<in> out_arcs G v \<longleftrightarrow> e \<in> arcs G \<and> tail G e = v"
  unfolding out_arcs_def by auto

lemma inout_arcs_simps[simp]:
  assumes "e \<in> arcs G"
  shows "tail G e = u \<Longrightarrow> out_arcs G u \<inter> insert e E = insert e (out_arcs G u \<inter> E)"
        "tail G e \<noteq> u \<Longrightarrow> out_arcs G u \<inter> insert e E = out_arcs G u \<inter> E"
        "out_arcs G u \<inter> {} = {}"
        "head G e = u \<Longrightarrow> in_arcs G u \<inter> insert e E = insert e (in_arcs G u \<inter> E)"
        "head G e \<noteq> u \<Longrightarrow> in_arcs G u \<inter> insert e E = in_arcs G u \<inter> E"
        "in_arcs G u \<inter> {} = {}"
  using assms by auto

lemma in_arcs_in_arcs: "x \<in> in_arcs G u \<Longrightarrow> x \<in> arcs G"
  and out_arcs_in_arcs: "x \<in> out_arcs G u \<Longrightarrow> x \<in> arcs G"
  by (auto simp: in_arcs_def out_arcs_def)





end
