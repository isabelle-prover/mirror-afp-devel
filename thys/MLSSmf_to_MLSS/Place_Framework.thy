theory Place_Framework
  imports HereditarilyFinite.HF MLSS_Extras MLSS_Decision_Proc.MLSS_Realisation
begin

definition places :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) set" where
  "places V \<equiv> (\<lambda>\<alpha>. (\<lambda>v. v \<in> \<alpha>)) ` Pow V"

lemma places_domain:"\<pi> \<in> places V \<Longrightarrow> x \<notin> V \<Longrightarrow> \<not> \<pi> x"
  unfolding places_def by blast

fun place_membership :: "'a pset_fm set \<Rightarrow> ('a \<Rightarrow> bool) set \<Rightarrow> (('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> bool)) set" where
  "place_membership \<C> PI = {(\<pi>\<^sub>1, \<pi>\<^sub>2) |\<pi>\<^sub>1 \<pi>\<^sub>2. \<pi>\<^sub>1 \<in> PI \<and> \<pi>\<^sub>2 \<in> PI \<and> (\<exists>x y. AT (Var x =\<^sub>s Single (Var y)) \<in> \<C> \<and> \<pi>\<^sub>1 y \<and> \<pi>\<^sub>2 x)}"

fun place_mem_graph :: "'a pset_fm set \<Rightarrow> ('a \<Rightarrow> bool) set \<Rightarrow> ('a \<Rightarrow> bool, ('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> bool)) pre_digraph" where
  "place_mem_graph \<C> PI = \<lparr> verts = PI, arcs = place_membership \<C> PI, tail = fst, head = snd \<rparr>"

lemma place_mem_graph_wf_digraph: "wf_digraph (place_mem_graph \<C> PI)"
proof
  fix e assume "e \<in> arcs (place_mem_graph \<C> PI)"
  then have "e \<in> place_membership \<C> PI" by simp
  have "tail (place_mem_graph \<C> PI) e = fst e" by simp
  also have "... \<in> PI" using \<open>e \<in> place_membership \<C> PI\<close> by auto
  also have "... = verts (place_mem_graph \<C> PI)" by simp
  finally show "tail (place_mem_graph \<C> PI) e \<in> verts (place_mem_graph \<C> PI)" by simp
next
  fix e assume "e \<in> arcs (place_mem_graph \<C> PI)"
  then have "e \<in> place_membership \<C> PI" by simp
  have "head (place_mem_graph \<C> PI) e = snd e" by simp
  also have "... \<in> PI" using \<open>e \<in> place_membership \<C> PI\<close> by auto
  also have "... = verts (place_mem_graph \<C> PI)" by simp
  finally show "head (place_mem_graph \<C> PI) e \<in> verts (place_mem_graph \<C> PI)" by simp
qed

locale adequate_place_framework =
  normalized_MLSS_clause \<C> for \<C> +
    fixes PI :: "('a \<Rightarrow> bool) set"
  assumes PI_subset_places_V: "PI \<subseteq> places V"

    fixes at\<^sub>p :: "('a \<times> ('a \<Rightarrow> bool)) set"
  assumes dom_at\<^sub>p: "Domain at\<^sub>p = W"
      and range_at\<^sub>p: "Range at\<^sub>p \<subseteq> PI"
      and single_valued_at\<^sub>p: "single_valued at\<^sub>p"
    \<comment> \<open>dom_at_p together with single_valued_at_p and the definition of W are also part of C5.1 in the original paper\<close>

  assumes membership_irreflexive: "(\<pi>, \<pi>) \<notin> place_membership \<C> PI" (* Otherwise \<C> cannot hold *)
      and C6: "dag (place_mem_graph \<C> PI)"

  assumes C1_1: "\<exists>n. AT (Var x =\<^sub>s \<emptyset> n) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI. \<not> \<pi> x"
      and C1_2: "AT (Var x =\<^sub>s Var y) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI. \<pi> x \<longleftrightarrow> \<pi> y"
      and C2: "AT (Var x =\<^sub>s Var y \<squnion>\<^sub>s Var z) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI. \<pi> x \<longleftrightarrow> \<pi> y \<or> \<pi> z"
      and C3: "AT (Var x =\<^sub>s Var y -\<^sub>s Var z) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI. \<pi> x \<longleftrightarrow> \<pi> y \<and> \<not> \<pi> z"
      and C4: "AF (Var x =\<^sub>s Var y) \<in> \<C> \<Longrightarrow> \<exists>\<pi> \<in> PI. \<pi> x \<longleftrightarrow> \<not> \<pi> y"
      and C5_1: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C> \<Longrightarrow> \<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p \<and> \<pi> x \<and> (\<forall>\<pi>' \<in> PI. \<pi>' \<noteq> \<pi> \<longrightarrow> \<not> \<pi>' x)"
      and C5_2: "\<lbrakk>y \<in> W; z \<in> W; \<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p \<and> (z, \<pi>) \<in> at\<^sub>p\<rbrakk> \<Longrightarrow>
                 \<forall>\<pi> \<in> PI. \<pi> y \<longleftrightarrow> \<pi> z"
      and C5_3: "\<lbrakk>y \<in> W; y' \<in> W; \<forall>\<pi> \<in> PI. \<pi> y' \<longleftrightarrow> \<pi> y\<rbrakk> \<Longrightarrow> \<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p \<and> (y', \<pi>) \<in> at\<^sub>p"

      and C7: "\<lbrakk>\<pi>\<^sub>1 \<in> Range at\<^sub>p - Range (place_membership \<C> PI);
                \<pi>\<^sub>2 \<in> Range at\<^sub>p - Range (place_membership \<C> PI)\<rbrakk> \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2"
begin

lemma finite_PI: "finite PI"
proof -
  from finite_\<C> have "finite V" by (simp add: finite_vars_fm)
  then have "finite (places V)" unfolding places_def by simp
  then show ?thesis using PI_subset_places_V
    by (simp add: finite_subset)
qed

end

end