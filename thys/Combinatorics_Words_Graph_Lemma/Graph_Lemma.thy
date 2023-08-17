(*  Title:      Graph Lemma
    File:       Combinatorics_Words_Graph_Lemma.Graph_Lemma
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Graph_Lemma
  imports Combinatorics_Words.Submonoids Glued_Codes

begin

chapter \<open>Graph Lemma\<close>

text\<open>The Graph Lemma is an important tool for gaining information about systems of word equations.
It yields an upper bound on the rank of the solution, that is, on the number of factors into all images of unknowns can be factorized.
The most straightforward application is showing that a system of equations admits periodic solutions only, which
in particular holds for any nontrivial equation over two words.

The name refers to a graph whose vertices are the unknowns of the system, and edges connect front letters of the left- and right-
hand sides of equations. The bound mentioned above is then the number of connected components of the graph.

We formalize the algebraic proof from @{cite Berstel1979}. Key ingredients of the proof are in the @{theory "Combinatorics_Words_Graph_Lemma.Glued_Codes"}.\<close>

section \<open>Graph lemma\<close>

theorem graph_lemma_last: "\<BB>\<^sub>F G = {last (Dec (\<BB>\<^sub>F G) g) | g. g \<in> G \<and> g \<noteq> \<epsilon>}"
proof
  interpret code "\<BB>\<^sub>F G"
    using free_basis_code.
  \<comment> \<open>the core is to show that each element of the free basis must be a last of some word\<close>
  show "\<BB>\<^sub>F G \<subseteq> {last (Dec \<BB>\<^sub>F G g) |g. g \<in> G \<and> g \<noteq> \<epsilon>}"
  proof (rule ccontr)
    \<comment> \<open>Assume the contrary.\<close>
    assume "\<not> \<BB>\<^sub>F G \<subseteq> {last (Dec \<BB>\<^sub>F G g) |g. g \<in> G \<and> g \<noteq> \<epsilon>}"
    \<comment> \<open>And let w be the not-last\<close>
    then obtain w
      where "w \<in> \<BB>\<^sub>F G"
        and hd_dec_neq: "\<And>g. g \<in> G \<Longrightarrow> g \<noteq> \<epsilon> \<Longrightarrow> last (Dec (\<BB>\<^sub>F G) g) \<noteq> w"
      by blast
    \<comment> \<open>For contradiction: We have a free hull which does not contain w but contains G.\<close>
    have "G \<subseteq> \<langle>glued_gens w (\<BB>\<^sub>F G)\<rangle>"
      by (blast intro!: gen_in_free_hull hd_dec_neq del: notI)
    then have "\<langle>\<BB>\<^sub>F G\<rangle> \<subseteq> \<langle>glued_gens w (\<BB>\<^sub>F G)\<rangle>"
      unfolding basis_gen_hull_free
      by (intro code.free_hull_min glued_gens_code \<open>w \<in> \<BB>\<^sub>F G\<close>)
    then show False
      using \<open>w \<in> \<BB>\<^sub>F G\<close> glued_not_in_glued_hull by blast
  qed
  \<comment> \<open>The opposite inclusion is easy\<close>
  show "{last (Dec \<BB>\<^sub>F G g) |g. g \<in> G \<and> g \<noteq> \<epsilon>} \<subseteq> \<BB>\<^sub>F G"
    by (auto intro!: dec_in_lists lists_hd_in_set[reversed] gen_in_free_hull del: notI)
qed

theorem graph_lemma: "\<BB>\<^sub>F G = {hd (Dec (\<BB>\<^sub>F G) g) | g. g \<in> G \<and> g \<noteq> \<epsilon>}"
proof -
  have *: "rev u = last (Dec rev ` (\<BB>\<^sub>F G) (rev g)) \<and> g \<in> G \<and> g \<noteq> \<epsilon>
           \<longleftrightarrow> u = hd (Dec (\<BB>\<^sub>F G) g) \<and> g \<in> G \<and> g \<noteq> \<epsilon>" for u g
    by (cases "g \<in> G \<and> g \<noteq> \<epsilon>") (simp add: gen_in_free_hull last_rev hd_map code.dec_rev, blast)
  show ?thesis
    using graph_lemma_last[reversed, of G] unfolding *.
qed

section \<open>Binary code\<close>

text \<open>We illustrate the use of the Graph Lemma in an alternative proof of the fact that two non-commuting words form a code.
See also @{thm no_comm_bin_code [no_vars]} in @{theory "Combinatorics_Words.CoWBasic"}.

First, we prove a lemma which is the core of the alternative proof.\<close>

lemma non_comm_hds_neq: assumes "u \<cdot> v \<noteq> v \<cdot> u" shows "hd (Dec \<BB>\<^sub>F {u,v} u) \<noteq> hd (Dec \<BB>\<^sub>F {u,v} v)"
using assms proof (rule contrapos_nn)
  assume hds_eq: "hd (Dec \<BB>\<^sub>F {u,v} u) = hd (Dec \<BB>\<^sub>F {u,v} v)"
  have **: "\<BB>\<^sub>F {u,v} = {hd (Dec \<BB>\<^sub>F {u,v} u)}"
    using graph_lemma by (rule trans) (use assms in \<open>auto intro: hds_eq[symmetric]\<close>)
  show "u \<cdot> v = v \<cdot> u"
    by (intro comm_rootI[of _ "hd (Dec \<BB>\<^sub>F {u,v} u)"] sing_gen)
       (simp_all add: **[symmetric] gen_in_free_hull)
qed

theorem assumes "u \<cdot> v \<noteq> v \<cdot> u" shows "code {u, v}"
proof
  have *: "w \<in> {u, v} \<Longrightarrow> w \<noteq> \<epsilon>" for w
    using \<open>u \<cdot> v \<noteq> v \<cdot> u\<close> by blast
  fix xs ys
  show "xs \<in> lists {u, v} \<Longrightarrow> ys \<in> lists {u, v} \<Longrightarrow> concat xs = concat ys \<Longrightarrow> xs = ys"
  proof (induction xs ys rule: list_induct2')
    case (4 x xs y ys)
      have **: "hd (Dec \<BB>\<^sub>F {u,v} (concat (z # zs))) = hd (Dec \<BB>\<^sub>F {u,v} z)"
        if "z # zs \<in> lists {u, v}" for z zs
        using that by (elim listsE) (simp del: insert_iff
          add: concat_in_hull' gen_in set_mp[OF hull_sub_free_hull]
               free_basis_dec_morph * basis_gen_hull_free)
      have "hd (Dec \<BB>\<^sub>F {u,v} x) = hd (Dec \<BB>\<^sub>F {u,v} y)"
        using "4.prems" by (simp only: **[symmetric])
      then have "x = y"
        using "4.prems"(1-2) non_comm_hds_neq[OF \<open>u \<cdot> v \<noteq> v \<cdot> u\<close>]
        by (elim listsE insertE emptyE) simp_all
      with 4 show "x # xs = y # ys" by simp
  qed (simp_all add: *)
qed

end
