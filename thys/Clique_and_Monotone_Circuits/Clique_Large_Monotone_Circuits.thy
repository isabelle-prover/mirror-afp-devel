theory Clique_Large_Monotone_Circuits
  imports 
  Sunflowers.Erdos_Rado_Sunflower
  Preliminaries
  Assumptions_and_Approximations
  Monotone_Formula
begin

text \<open>disable list-syntax\<close>
no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]")
no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]")

hide_const (open) Sigma_Algebra.measure

subsection \<open>Plain Graphs\<close>

definition binprod :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" (infixl "\<cdot>" 60) where
  "X \<cdot> Y = {{x,y} | x y. x \<in> X \<and> y \<in> Y \<and> x \<noteq> y}"

abbreviation sameprod :: "'a set \<Rightarrow> 'a set set" ("(_)^\<two>") where
  "X^\<two> \<equiv> X \<cdot> X" 

lemma sameprod_altdef: "X^\<two> = {Y. Y \<subseteq> X \<and> card Y = 2}" 
  unfolding binprod_def by (auto simp: card_2_iff)

definition numbers :: "nat \<Rightarrow> nat set" ("[(_)]") where
  "[n] \<equiv> {..<n}" 

lemma card_sameprod: "finite X \<Longrightarrow> card (X^\<two>) = card X choose 2" 
  unfolding sameprod_altdef
  by (subst n_subsets, auto)

lemma sameprod_mono: "X \<subseteq> Y \<Longrightarrow> X^\<two> \<subseteq> Y^\<two>"
  unfolding sameprod_altdef by auto

lemma sameprod_finite: "finite X \<Longrightarrow> finite (X^\<two>)" 
  unfolding sameprod_altdef by simp

lemma numbers2_mono: "x \<le> y \<Longrightarrow> [x]^\<two> \<subseteq> [y]^\<two>"
  by (rule sameprod_mono, auto simp: numbers_def)

lemma card_numbers[simp]: "card [n] = n" 
  by (simp add: numbers_def)

lemma card_numbers2[simp]: "card ([n]^\<two>) = n choose 2" 
  by (subst card_sameprod, auto simp: numbers_def)


type_synonym vertex = nat
type_synonym graph = "vertex set set" 

definition Graphs :: "vertex set \<Rightarrow> graph set" where
  "Graphs V = { G. G \<subseteq> V^\<two> }"  

definition Clique :: "vertex set \<Rightarrow> nat \<Rightarrow> graph set" where
  "Clique V k = { G. G \<in> Graphs V \<and> (\<exists> C \<subseteq> V. C^\<two> \<subseteq> G \<and> card C = k) }" 

context first_assumptions
begin

abbreviation \<G> where "\<G> \<equiv> Graphs [m]" 

lemmas \<G>_def = Graphs_def[of "[m]"]

lemma empty_\<G>[simp]: "{} \<in> \<G>" unfolding \<G>_def by auto

definition v :: "graph \<Rightarrow> vertex set" where
 "v G = { x . \<exists> y. {x,y} \<in> G}" 

lemma v_union: "v (G \<union> H) = v G \<union> v H" 
  unfolding v_def by auto

definition \<K> :: "graph set" where
  "\<K> = { K . K \<in> \<G> \<and> card (v K) = k \<and> K = (v K)^\<two> }" 

lemma v_\<G>: "G \<in> \<G> \<Longrightarrow> v G \<subseteq> [m]" 
  unfolding v_def \<G>_def sameprod_altdef by auto

lemma v_mono: "G \<subseteq> H \<Longrightarrow> v G \<subseteq> v H" unfolding v_def by auto

lemma v_sameprod[simp]: assumes "card X \<ge> 2" 
  shows "v (X^\<two>) = X" 
proof -
  from obtain_subset_with_card_n[OF assms] obtain Y where "Y \<subseteq> X" 
    and Y: "card Y = 2" by auto
  then obtain x y where "x \<in> X" "y \<in> X" and "x \<noteq> y"
    by (auto simp: card_2_iff)
  thus ?thesis unfolding sameprod_altdef v_def
    by (auto simp: card_2_iff doubleton_eq_iff) blast
qed

lemma v_mem_sub: assumes "card e = 2" "e \<in> G" shows "e \<subseteq> v G" 
proof -
  obtain x y where e: "e = {x,y}" and xy: "x \<noteq> y" using assms
    by (auto simp: card_2_iff)
  from assms(2) have x: "x \<in> v G" unfolding e
    by (auto simp: v_def)
  from e have e: "e = {y,x}" unfolding e by auto
  from assms(2) have y: "y \<in> v G" unfolding e
    by (auto simp: v_def)
  show "e \<subseteq> v G" using x y unfolding e by auto
qed

lemma v_\<G>_2: assumes "G \<in> \<G>" shows "G \<subseteq> (v G)^\<two>" 
proof
  fix e
  assume eG: "e \<in> G" 
  with assms[unfolded \<G>_def binprod_def] obtain x y where e: "e = {x,y}" and xy: "x \<noteq> y" by auto
  from eG e xy have x: "x \<in> v G" by (auto simp: v_def)
  from e have e: "e = {y,x}" unfolding e by auto
  from eG e xy have y: "y \<in> v G" by (auto simp: v_def)
  from x y xy show "e \<in> (v G)^\<two>" unfolding binprod_def e by auto
qed

  
lemma v_numbers2[simp]: "x \<ge> 2 \<Longrightarrow> v ([x]^\<two>) = [x]" 
  by (rule v_sameprod, auto)

lemma sameprod_\<G>: assumes "X \<subseteq> [m]" "card X \<ge> 2" 
  shows "X^\<two> \<in> \<G>" 
  unfolding \<G>_def using assms(2) sameprod_mono[OF assms(1)] 
  by auto

lemma finite_numbers[simp,intro]: "finite [n]" 
  unfolding numbers_def by auto

lemma finite_numbers2[simp,intro]: "finite ([n]^\<two>)" 
  unfolding sameprod_altdef using finite_subset[of _ "[m]"] by auto

lemma finite_members_\<G>: "G \<in> \<G> \<Longrightarrow> finite G"
  unfolding \<G>_def using finite_subset[of G "[m]^\<two>"] by auto

lemma finite_\<G>[simp,intro]: "finite \<G>" 
  unfolding \<G>_def by simp

lemma finite_vG: assumes "G \<in> \<G>"
  shows "finite (v G)"
proof -
  from finite_members_\<G>[OF assms]
  show ?thesis 
  proof (induct rule: finite_induct)
    case (insert xy F)
    show ?case
    proof (cases "\<exists> x y. xy = {x,y}")
      case False
      hence "v (insert xy F) = v F" unfolding v_def by auto
      thus ?thesis using insert by auto
    next
      case True
      then obtain x y where xy: "xy = {x,y}" by auto
      hence "v (insert xy F) = insert x (insert y (v F))" 
        unfolding v_def by auto
      thus ?thesis using insert by auto
    qed
  qed (auto simp: v_def)
qed

lemma v_empty[simp]: "v {} = {}" unfolding v_def by auto

lemma v_card2: assumes "G \<in> \<G>" "G \<noteq> {}" 
  shows "2 \<le> card (v G)" 
proof -
  from assms[unfolded \<G>_def] obtain edge where *: "edge \<in> G" "edge \<in> [m]^\<two>" by auto
  then obtain x y where edge: "edge = {x,y}" "x \<noteq> y" unfolding binprod_def by auto
  with * have sub: "{x,y} \<subseteq> v G" unfolding v_def
    by (smt (verit, best) insert_commute insert_compr mem_Collect_eq singleton_iff subsetI)
  from assms finite_vG have "finite (v G)" by auto
  from sub \<open>x \<noteq> y\<close> this show "2 \<le> card (v G)"
    by (metis card_2_iff card_mono)
qed


lemma \<K>_altdef: "\<K> = {V^\<two> | V. V \<subseteq> [m] \<and> card V = k}" 
  (is "_ = ?R")
proof -
  {
    fix K 
    assume "K \<in> \<K>"
    hence K: "K \<in> \<G>" and card: "card (v K) = k" and KvK: "K = (v K)^\<two>" 
      unfolding \<K>_def by auto
    from v_\<G>[OF K] card KvK have "K \<in> ?R" by auto
  }
  moreover
  {
    fix V
    assume 1: "V \<subseteq> [m]" and "card V = k" 
    hence "V^\<two> \<in> \<K>" unfolding \<K>_def using k2 sameprod_\<G>[OF 1]
      by auto
  }
  ultimately show ?thesis by auto
qed
    
lemma \<K>_\<G>: "\<K> \<subseteq> \<G>" 
  unfolding \<K>_def by auto
  
definition CLIQUE :: "graph set" where
  "CLIQUE = { G. G \<in> \<G> \<and> (\<exists> K \<in> \<K>. K \<subseteq> G) }" 

lemma empty_CLIQUE[simp]: "{} \<notin> CLIQUE" unfolding CLIQUE_def \<K>_def using k2 by (auto simp: v_def)

subsection \<open>Test Graphs\<close>

text \<open>Positive test graphs are precisely the cliques of size @{term k}.\<close>

abbreviation "POS \<equiv> \<K>"

lemma POS_\<G>: "POS \<subseteq> \<G>" by (rule \<K>_\<G>)

text \<open>Negative tests are coloring-functions of vertices that encode graphs
  which have cliques of size at most @{term "k - 1"}.\<close>

type_synonym colorf = "vertex \<Rightarrow> nat" 

definition \<F> :: "colorf set" where
  "\<F> = [m] \<rightarrow>\<^sub>E [k - 1]" 

lemma finite_\<F>: "finite \<F>"
  unfolding \<F>_def numbers_def
  by (meson finite_PiE finite_lessThan)

definition C :: "colorf \<Rightarrow> graph" where
  "C f = { {x, y} | x y . {x,y} \<in> [m]^\<two> \<and> f x \<noteq> f y}" 

definition NEG :: "graph set" where
  "NEG = C ` \<F>"

paragraph \<open>Lemma 1\<close>

lemma CLIQUE_NEG: "CLIQUE \<inter> NEG = {}" 
proof -
  {
    fix G
    assume GC: "G \<in> CLIQUE" and GN: "G \<in> NEG" 
    from GC[unfolded CLIQUE_def] obtain K where 
      K: "K \<in> \<K>" and G: "G \<in> \<G>" and KsubG: "K \<subseteq> G" by auto
    from GN[unfolded NEG_def] obtain f where fF: "f \<in> \<F>" and 
      GCf: "G = C f" by auto
    from K[unfolded \<K>_def] have KG: "K \<in> \<G>" and 
      KvK: "K = v K^\<two>" and card1: "card (v K) = k" by auto
    from k2 card1 have ineq: "card (v K) > card [k - 1]" by auto
    from v_\<G>[OF KG] have vKm: "v K \<subseteq> [m]" by auto
    from fF[unfolded \<F>_def] vKm have f: "f \<in> v K \<rightarrow> [k - 1]"  
      by auto
    from card_inj[OF f] ineq 
    have "\<not> inj_on f (v K)" by auto
    then obtain x y where *: "x \<in> v K" "y \<in> v K" "x \<noteq> y" and ineq: "f x = f y" 
      unfolding inj_on_def by auto
    have "{x,y} \<notin> G" unfolding GCf C_def using ineq
      by (auto simp: doubleton_eq_iff)
    with KsubG KvK have "{x,y} \<notin> v K^\<two>" by auto
    with * have False unfolding binprod_def by auto
  }
  thus ?thesis by auto
qed

lemma NEG_\<G>: "NEG \<subseteq> \<G>" 
proof -
  {
    fix f
    assume "f \<in> \<F>" 
    hence "C f \<in> \<G>" 
      unfolding NEG_def C_def \<G>_def 
      by (auto simp: sameprod_altdef)
  }
  thus "NEG \<subseteq> \<G>" unfolding NEG_def by auto
qed

lemma finite_POS_NEG: "finite (POS \<union> NEG)" 
  using POS_\<G> NEG_\<G> 
  by (intro finite_subset[OF _ finite_\<G>], auto)

lemma POS_sub_CLIQUE: "POS \<subseteq> CLIQUE" 
  unfolding CLIQUE_def using \<K>_\<G> by auto

lemma POS_CLIQUE: "POS \<subset> CLIQUE" 
proof -
  have "[k+1]^\<two> \<in> CLIQUE" 
    unfolding CLIQUE_def
  proof (standard, intro conjI bexI[of _ "[k]^\<two>"])
    show "[k]^\<two> \<subseteq> [k+1]^\<two>" 
      by (rule numbers2_mono, auto)
    show "[k]^\<two> \<in> \<K>" unfolding \<K>_altdef using km 
      by (auto intro!: exI[of _ "[k]"], auto simp: numbers_def)
    show "[k+1]^\<two> \<in> \<G>" using km k2
      by (intro sameprod_\<G>, auto simp: numbers_def)
  qed
  moreover have "[k+1]^\<two> \<notin> POS" unfolding \<K>_def using v_numbers2[of "k + 1"] k2 
    by auto
  ultimately show ?thesis using POS_sub_CLIQUE by blast
qed

lemma card_POS: "card POS = m choose k" 
proof -
  have "m choose k =
    card {B. B \<subseteq> [m] \<and> card B = k}" (is "_ = card ?A")
    by (subst n_subsets[of "[m]" k], auto simp: numbers_def) 
  also have "\<dots> = card (sameprod ` ?A)" 
  proof (rule card_image[symmetric])
    { 
      fix A
      assume "A \<in> ?A" 
      hence "v (sameprod A) = A" using k2
        by (subst v_sameprod, auto)
    }
    thus "inj_on sameprod ?A" by (rule inj_on_inverseI)
  qed
  also have "sameprod ` {B. B \<subseteq> [m] \<and> card B = k} = POS" 
    unfolding \<K>_altdef by auto
  finally show ?thesis by simp
qed

subsection \<open>Basic operations on sets of graphs\<close>

definition odot :: "graph set \<Rightarrow> graph set \<Rightarrow> graph set" (infixl "\<odot>" 65) where 
  "X \<odot> Y = { D \<union> E | D E. D \<in> X \<and> E \<in> Y}" 

lemma union_\<G>[intro]: "G \<in> \<G> \<Longrightarrow> H \<in> \<G> \<Longrightarrow> G \<union> H \<in> \<G>" 
  unfolding \<G>_def by auto

lemma odot_\<G>: "X \<subseteq> \<G> \<Longrightarrow> Y \<subseteq> \<G> \<Longrightarrow> X \<odot> Y \<subseteq> \<G>" 
  unfolding odot_def by auto

subsection \<open>Acceptability\<close>

text \<open>Definition 2\<close>

definition accepts :: "graph set \<Rightarrow> graph \<Rightarrow> bool" (infixl "\<tturnstile>" 55) where
  "(X \<tturnstile> G) = (\<exists> D \<in> X. D \<subseteq> G)" 


lemma acceptsI[intro]: "D \<subseteq> G \<Longrightarrow> D \<in> X \<Longrightarrow> X \<tturnstile> G" 
  unfolding accepts_def by auto

definition ACC :: "graph set \<Rightarrow> graph set" where
  "ACC X = { G. G \<in> \<G> \<and> X \<tturnstile> G}" 

definition ACC_cf :: "graph set \<Rightarrow> colorf set" where
  "ACC_cf X = { F. F \<in> \<F> \<and> X \<tturnstile> C F}" 

lemma ACC_cf_\<F>: "ACC_cf X \<subseteq> \<F>" 
  unfolding ACC_cf_def by auto

lemma finite_ACC[intro,simp]: "finite (ACC_cf X)" 
  by (rule finite_subset[OF ACC_cf_\<F> finite_\<F>])

lemma ACC_I[intro]: "G \<in> \<G> \<Longrightarrow> X \<tturnstile> G \<Longrightarrow> G \<in> ACC X" 
  unfolding ACC_def by auto

lemma ACC_cf_I[intro]: "F \<in> \<F> \<Longrightarrow> X \<tturnstile> C F \<Longrightarrow> F \<in> ACC_cf X" 
  unfolding ACC_cf_def by auto

lemma ACC_cf_mono: "X \<subseteq> Y \<Longrightarrow> ACC_cf X \<subseteq> ACC_cf Y"
  unfolding ACC_cf_def accepts_def by auto

text \<open>Lemma 3\<close>

lemma ACC_cf_empty: "ACC_cf {} = {}" 
  unfolding ACC_cf_def accepts_def by auto

lemma ACC_empty[simp]: "ACC {} = {}" 
  unfolding ACC_def accepts_def by auto

lemma ACC_cf_union: "ACC_cf (X \<union> Y) = ACC_cf X \<union> ACC_cf Y" 
  unfolding ACC_cf_def accepts_def by blast

lemma ACC_union: "ACC (X \<union> Y) = ACC X \<union> ACC Y" 
  unfolding ACC_def accepts_def by blast

lemma ACC_odot: "ACC (X \<odot> Y) = ACC X \<inter> ACC Y"
proof -
  {
    fix G
    assume "G \<in> ACC (X \<odot> Y)" 
    from this[unfolded ACC_def accepts_def]
    obtain D E F :: graph where *: "D \<in> X" "E \<in> Y" "G \<in> \<G>" "D \<union> E \<subseteq> G"       
      by (force simp: odot_def)
    hence "G \<in> ACC X \<inter> ACC Y" 
      unfolding ACC_def accepts_def by auto
  }
  moreover
  {
    fix G
    assume "G \<in> ACC X \<inter> ACC Y" 
    from this[unfolded ACC_def accepts_def]
    obtain D E where *: "D \<in> X" "E \<in> Y" "G \<in> \<G>" "D \<subseteq> G" "E \<subseteq> G" 
      by auto
    let ?F = "D \<union> E" 
    from * have "?F \<in> X \<odot> Y" unfolding odot_def using * by blast
    moreover have "?F \<subseteq> G" using * by auto
    ultimately have "G \<in> ACC (X \<odot> Y)" using *
      unfolding ACC_def accepts_def by blast
  }
  ultimately show ?thesis by blast
qed

lemma ACC_cf_odot: "ACC_cf (X \<odot> Y) = ACC_cf X \<inter> ACC_cf Y"
proof -
  {
    fix G
    assume "G \<in> ACC_cf (X \<odot> Y)" 
    from this[unfolded ACC_cf_def accepts_def]
    obtain D E :: graph where *: "D \<in> X" "E \<in> Y" "G \<in> \<F>" "D \<union> E \<subseteq> C G"       
      by (force simp: odot_def)
    hence "G \<in> ACC_cf X \<inter> ACC_cf Y" 
      unfolding ACC_cf_def accepts_def by auto
  }
  moreover
  {
    fix F
    assume "F \<in> ACC_cf X \<inter> ACC_cf Y" 
    from this[unfolded ACC_cf_def accepts_def]
    obtain D E where *: "D \<in> X" "E \<in> Y" "F \<in> \<F>" "D \<subseteq> C F" "E \<subseteq> C F" 
      by auto
    let ?F = "D \<union> E" 
    from * have "?F \<in> X \<odot> Y" unfolding odot_def using * by blast
    moreover have "?F \<subseteq> C F" using * by auto
    ultimately have "F \<in> ACC_cf (X \<odot> Y)" using *
      unfolding ACC_cf_def accepts_def by blast 
  }
  ultimately show ?thesis by blast
qed

subsection \<open>Approximations and deviations\<close>

definition \<G>l :: "graph set" where 
  "\<G>l = { G. G \<in> \<G> \<and> card (v G) \<le> l }" 

definition v_gs :: "graph set \<Rightarrow> vertex set set" where
  "v_gs X = v ` X" 

lemma v_gs_empty[simp]: "v_gs {} = {}" 
  unfolding v_gs_def by auto

lemma v_gs_union: "v_gs (X \<union> Y) = v_gs X \<union> v_gs Y"
  unfolding v_gs_def by auto

lemma v_gs_mono: "X \<subseteq> Y \<Longrightarrow> v_gs X \<subseteq> v_gs Y" 
  using v_gs_def by auto  

lemma finite_v_gs: assumes "X \<subseteq> \<G>" 
  shows "finite (v_gs X)" 
proof -
  have "v_gs X \<subseteq> v ` \<G>"
    using assms unfolding v_gs_def by force
  moreover have "finite \<G>" using finite_\<G> by auto
  ultimately show ?thesis by (metis finite_surj)
qed

lemma finite_v_gs_Gl: assumes "X \<subseteq> \<G>l" 
  shows "finite (v_gs X)" 
  by (rule finite_v_gs, insert assms, auto simp: \<G>l_def)


definition \<P>L\<G>l :: "graph set set" where
  "\<P>L\<G>l = { X . X \<subseteq> \<G>l \<and> card (v_gs X) \<le> L}"

definition odotl :: "graph set \<Rightarrow> graph set \<Rightarrow> graph set" (infixl "\<odot>l" 65) where
  "X \<odot>l Y = (X \<odot> Y) \<inter> \<G>l" 


lemma joinl_join: "X \<odot>l Y \<subseteq> X \<odot> Y" 
  unfolding odot_def odotl_def by blast

lemma card_v_gs_join: assumes X: "X \<subseteq> \<G>" and Y: "Y \<subseteq> \<G>" 
  and Z: "Z \<subseteq> X \<odot> Y" 
  shows "card (v_gs Z) \<le> card (v_gs X) * card (v_gs Y)" 
proof -
  note fin = finite_v_gs[OF X] finite_v_gs[OF Y]
  have "card (v_gs Z) \<le> card ((\<lambda> (A, B). A \<union> B) ` (v_gs X \<times> v_gs Y))" 
  proof (rule card_mono[OF finite_imageI])
    show "finite (v_gs X \<times> v_gs Y)" 
      using fin by auto
    have "v_gs Z \<subseteq> v_gs (X \<odot> Y)" 
      using v_gs_mono[OF Z] .
    also have "\<dots> \<subseteq> (\<lambda>(x, y). x \<union> y) ` (v_gs X \<times> v_gs Y)" (is "?L \<subseteq> ?R")
      unfolding odot_def v_gs_def by (force split: if_splits simp: v_union)
    finally show "v_gs Z \<subseteq> (\<lambda>(x, y). x \<union> y) ` (v_gs X \<times> v_gs Y)" .
  qed
  also have "\<dots> \<le> card (v_gs X \<times> v_gs Y)" 
    by (rule card_image_le, insert fin, auto)
  also have "\<dots> = card (v_gs X) * card (v_gs Y)" 
    by (rule card_cartesian_product)
  finally show ?thesis .
qed

text \<open>Definition 6 -- elementary plucking step\<close>

definition plucking_step :: "graph set \<Rightarrow> graph set" where
  "plucking_step X = (let vXp = v_gs X;
      S = (SOME S. S \<subseteq> vXp \<and> sunflower S \<and> card S = p);
      U = {E \<in> X. v E \<in> S};
      Vs = \<Inter> S;
      Gs = Vs^\<two>
     in X - U \<union> {Gs})"
end

context second_assumptions
begin

text \<open>Lemma 9 -- for elementary plucking step\<close>

lemma v_sameprod_subset: "v (Vs^\<two>) \<subseteq> Vs" unfolding binprod_def v_def
  by (auto simp: doubleton_eq_iff)

lemma plucking_step: assumes X: "X \<subseteq> \<G>l"
  and L: "card (v_gs X) > L" 
  and Y: "Y = plucking_step X" 
shows "card (v_gs Y) \<le> card (v_gs X) - p + 1" 
  "Y \<subseteq> \<G>l" 
  "POS \<inter> ACC X \<subseteq> ACC Y" 
  "2 ^ p * card (ACC_cf Y - ACC_cf X) \<le> (k - 1) ^ m"
  "Y \<noteq> {}"
proof -
  let ?vXp = "v_gs X"
  have sf_precond: "\<forall>A\<in> ?vXp. finite A \<and> card A \<le> l" 
    using X unfolding \<G>l_def \<G>l_def v_gs_def by (auto intro: finite_vG intro!: v_\<G> v_card2)
  note sunflower = Erdos_Rado_sunflower[OF sf_precond]
  from p have p0: "p \<noteq> 0" by auto
  have "(p - 1) ^ l * fact l < card ?vXp"  using L[unfolded L_def]
    by (simp add: ac_simps)
  note sunflower = sunflower[OF this]
  define S where "S = (SOME S. S \<subseteq> ?vXp \<and> sunflower S \<and> card S = p)" 
  define U where "U = {E \<in> X. v E \<in> S}" 
  define Vs where "Vs = \<Inter> S"
  define Gs where "Gs = Vs^\<two>"
  let ?U = U 
  let ?New = "Gs :: graph" 
  have Y: "Y = X - U \<union> {?New}" 
    using Y[unfolded plucking_step_def Let_def, folded S_def, folded U_def, 
        folded Vs_def, folded Gs_def] .
  have U: "U \<subseteq> \<G>l" using X unfolding U_def by auto 
  hence "U \<subseteq> \<G>" unfolding \<G>l_def by auto
  from sunflower
  have "\<exists> S. S \<subseteq> ?vXp \<and> sunflower S \<and> card S = p" by auto
  from someI_ex[OF this, folded S_def]
  have S: "S \<subseteq> ?vXp" "sunflower S" "card S = p" by (auto simp: Vs_def)
  have fin1: "finite ?vXp" using finite_v_gs_Gl[OF X] .
  from X have finX: "finite X" unfolding \<G>l_def 
    using finite_subset[of X, OF _  finite_\<G>] by auto
  from fin1 S have finS: "finite S" by (metis finite_subset)
  from finite_subset[OF _ finX] have finU: "finite U" unfolding U_def by auto
  from S p have Snempty: "S \<noteq> {}" by auto  
  have UX: "U \<subseteq> X" unfolding U_def by auto
  {
    from Snempty obtain s where sS: "s \<in> S" by auto
    with S have "s \<in> v_gs X" by auto
    then obtain Sp where "Sp \<in> X" and sSp: "s = v Sp" 
      unfolding v_gs_def by auto
    hence *: "Sp \<in> U" using \<open>s \<in> S\<close> unfolding U_def by auto
    from * X UX have le: "card (v Sp) \<le> l" "finite (v Sp)" "Sp \<in> \<G>" 
      unfolding \<G>l_def \<G>l_def using finite_vG[of Sp] by auto
    hence m: "v Sp \<subseteq> [m]" by (intro v_\<G>)
    have "Vs \<subseteq> v Sp" using sS sSp unfolding Vs_def by auto
    with card_mono[OF \<open>finite (v Sp)\<close> this] finite_subset[OF this \<open>finite (v Sp)\<close>] le * m
    have "card Vs \<le> l" "U \<noteq> {}" "finite Vs" "Vs \<subseteq> [m]" by auto
  } 
  hence card_Vs: "card Vs \<le> l" and Unempty: "U \<noteq> {}" 
    and fin_Vs: "finite Vs" and Vsm: "Vs \<subseteq> [m]" by auto
  have vGs: "v Gs \<subseteq> Vs" unfolding Gs_def by (rule v_sameprod_subset)
  have GsG: "Gs \<in> \<G>" unfolding Gs_def \<G>_def
    by (intro CollectI Inter_subset sameprod_mono Vsm)
  have GsGl: "Gs \<in> \<G>l" unfolding \<G>l_def using GsG vGs card_Vs card_mono[OF _ vGs] 
    by (simp add: fin_Vs)
  hence DsDl: "?New \<in> \<G>l" using UX  
    unfolding \<G>l_def \<G>_def \<G>l_def \<G>_def by auto
  with X U show "Y \<subseteq> \<G>l" unfolding Y by auto
  from X have XD: "X \<subseteq> \<G>" unfolding \<G>l_def by auto
  have vplus_dsU: "v_gs U = S" using S(1)
    unfolding v_gs_def U_def by force
  have vplus_dsXU: "v_gs (X - U) = v_gs X - v_gs U"
    unfolding v_gs_def U_def by auto
  have "card (v_gs Y) = card (v_gs (X - U \<union> {?New}))"  
    unfolding Y by simp
  also have "v_gs (X - U \<union> {?New}) = v_gs (X - U) \<union> v_gs ({?New})"
    unfolding v_gs_union ..
  also have "v_gs ({?New}) = {v (Gs)}" unfolding v_gs_def image_comp o_def by simp
  also have "card (v_gs (X - U) \<union> \<dots>) \<le> card (v_gs (X - U)) + card \<dots>"
    by (rule card_Un_le)
  also have "\<dots> \<le> card (v_gs (X - U)) + 1" by auto
  also have "v_gs (X - U) = v_gs X - v_gs U" by fact
  also have "card \<dots> = card (v_gs X) - card (v_gs U)" 
    by (rule card_Diff_subset, force simp: vplus_dsU finS, 
      insert UX, auto simp: v_gs_def)
  also have "card (v_gs U) = card S" unfolding vplus_dsU ..
  finally show "card (v_gs Y) \<le> card (v_gs X) - p + 1" 
    using S by auto
  show "Y \<noteq> {}" unfolding Y using Unempty by auto
  {
    fix G
    assume "G \<in> ACC X" and GPOS: "G \<in> POS"  
    from this[unfolded ACC_def] POS_\<G> have G: "G \<in> \<G>" "X \<tturnstile> G" by auto
    from this[unfolded accepts_def] obtain D :: graph where 
      D: "D \<in> X" "D \<subseteq> G" by auto
    have "G \<in> ACC Y" 
    proof (cases "D \<in> Y")
      case True
      with D G show ?thesis unfolding accepts_def ACC_def by auto
    next
      case False
      with D have DU: "D \<in> U" unfolding Y by auto
      from GPOS[unfolded POS_def \<K>_def] obtain K where GK: "G = (v K)^\<two>" "card (v K) = k" by auto
      from DU[unfolded U_def] have "v D \<in> S" by auto
      hence "Vs \<subseteq> v D" unfolding Vs_def by auto
      also have "\<dots> \<subseteq> v G" 
        by (intro v_mono D)
      also have "\<dots> = v K" unfolding GK 
        by (rule v_sameprod, unfold GK, insert k2, auto)
      finally have "Gs \<subseteq> G" unfolding Gs_def GK
        by (intro sameprod_mono)
      with D DU have "D \<in> ?U" "?New \<subseteq> G" by (auto)
      hence "Y \<tturnstile> G" unfolding accepts_def Y by auto 
      thus ?thesis using G by auto
    qed
  }
  thus "POS \<inter> ACC X \<subseteq> ACC Y" by auto

  from ex_bij_betw_nat_finite[OF finS, unfolded \<open>card S = p\<close>]
  obtain Si where Si: "bij_betw Si {0 ..< p} S" by auto
  define G where "G = (\<lambda> i. SOME Gb. Gb \<in> X \<and> v Gb = Si i)" 
  {
    fix i
    assume "i < p" 
    with Si have SiS: "Si i \<in> S" unfolding bij_betw_def by auto
    with S have "Si i \<in> v_gs X" by auto
    hence "\<exists> G. G \<in> X \<and> v G = Si i" 
      unfolding v_gs_def by auto
    from someI_ex[OF this] 
    have "(G i) \<in> X \<and> v (G i) = Si i" 
      unfolding G_def by blast
    hence "G i \<in> X" "v (G i) = Si i" 
      "G i \<in> U" "v (G i) \<in> S" using SiS unfolding U_def 
      by auto
  } note G = this
  have SvG: "S = v ` G ` {0 ..< p}" unfolding Si[unfolded bij_betw_def, 
        THEN conjunct2, symmetric] image_comp o_def using G(2) by auto
  have injG: "inj_on G {0 ..< p}" 
  proof (standard, goal_cases)
    case (1 i j)
    hence "Si i = Si j" using G[of i] G[of j] by simp
    with 1(1,2) Si show "i = j"  
      by (metis Si bij_betw_iff_bijections)
  qed
  define r where "r = card U" 
  have rq: "r \<ge> p" unfolding r_def \<open>card S = p\<close>[symmetric] vplus_dsU[symmetric]
    unfolding v_gs_def
    by (rule card_image_le[OF finU])

  let ?Vi = "\<lambda> i. v (G i)"
  let ?Vis = "\<lambda> i. ?Vi i - Vs"
  define s where "s = card Vs" 
  define si where "si i = card (?Vi i)" for i
  define ti where "ti i = card (?Vis i)" for i
  {
    fix i
    assume i: "i < p" 
    have Vs_Vi: "Vs \<subseteq> ?Vi i" using i unfolding Vs_def 
      using G[OF i] unfolding SvG by auto
    have finVi: "finite (?Vi i)"  
      using G(4)[OF i] S(1) sf_precond
      by (meson finite_numbers finite_subset subset_eq)
    from S(1) have "G i \<in> \<G>" using G(1)[OF i] X unfolding \<G>l_def \<G>_def \<G>l_def by auto
    hence finGi: "finite (G i)"
      using finite_members_\<G> by auto
    have ti: "ti i = si i - s" unfolding ti_def si_def s_def
      by (rule card_Diff_subset[OF fin_Vs Vs_Vi])
    have size1: "s \<le> si i" unfolding s_def si_def
      by (intro card_mono finVi Vs_Vi)
    have size2: "si i \<le> l" unfolding si_def using G(4)[OF i] S(1) sf_precond by auto
    note Vs_Vi finVi ti size1 size2 finGi \<open>G i \<in> \<G>\<close>
  } note i_props = this
  define fstt where "fstt e = (SOME x. x \<in> e \<and> x \<notin> Vs)" for e
  define sndd where "sndd e = (SOME x. x \<in> e \<and> x \<noteq> fstt e)" for e
  {
    fix e :: "nat set" 
    assume *: "card e = 2" "\<not> e \<subseteq> Vs" 
    from *(1) obtain x y where e: "e = {x,y}" "x \<noteq> y" 
      by (meson card_2_iff)
    with * have "\<exists> x. x \<in> e \<and> x \<notin> Vs" by auto
    from someI_ex[OF this, folded fstt_def]
    have fst: "fstt e \<in> e" "fstt e \<notin> Vs" by auto
    with * e have "\<exists> x. x \<in> e \<and> x \<noteq> fstt e"
      by (metis insertCI)
    from someI_ex[OF this, folded sndd_def] have snd: "sndd e \<in> e" "sndd e \<noteq> fstt e" by auto
    from fst snd e have "{fstt e, sndd e} = e" "fstt e \<notin> Vs" "fstt e \<noteq> sndd e" by auto
  } note fstt = this
  {
    fix f
    assume "f \<in> ACC_cf Y - ACC_cf X" 
    hence fake: "f \<in> ACC_cf {?New} - ACC_cf U" unfolding Y ACC_cf_def accepts_def 
      Diff_iff U_def Un_iff mem_Collect_eq by blast
    hence f: "f \<in> \<F>" using ACC_cf_\<F> by auto
    hence "C f \<in> NEG" unfolding NEG_def by auto
    with NEG_\<G> have Cf: "C f \<in> \<G>" by auto
    from fake have "f \<in> ACC_cf {?New}" by auto
    from this[unfolded ACC_cf_def accepts_def] Cf
    have GsCf: "Gs \<subseteq> C f" and Cf: "C f \<in> \<G>" by auto
    from fake have "f \<notin> ACC_cf U" by auto
    from this[unfolded ACC_cf_def] Cf f have "\<not> (U \<tturnstile> C f)" by auto
    from this[unfolded accepts_def] 
    have UCf: "D \<in> U \<Longrightarrow> \<not> D \<subseteq> C f" for D by auto
    let ?prop = "\<lambda> i e. fstt e \<in> v (G i) - Vs \<and> 
           sndd e \<in> v (G i) \<and> e \<in> G i \<inter> ([m]^\<two>)
         \<and> f (fstt e) = f (sndd e) \<and> f (sndd e) \<in> [k - 1] \<and> {fstt e, sndd e} = e" 
    define pair where "pair i = (if i < p then (SOME pair. ?prop i pair) else undefined)" for i 
    define u where "u i = fstt (pair i)" for i
    define w where "w i = sndd (pair i)" for i
    {
      fix i
      assume i: "i < p" 
      from i have "?Vi i \<in> S" unfolding SvG by auto
      hence "Vs \<subseteq> ?Vi i" unfolding Vs_def by auto
      from sameprod_mono[OF this, folded Gs_def] 
      have *: "Gs \<subseteq> v (G i)^\<two>" .  
      from i have Gi: "G i \<in> U" using G[OF i] by auto
      from UCf[OF Gi] i_props[OF i] have "\<not> G i \<subseteq> C f" and Gi: "G i \<in> \<G>" by auto
      then obtain edge where 
        edgep: "edge \<in> G i" and edgen: "edge \<notin> C f" by auto
      from edgep Gi obtain x y where edge: "edge = {x,y}" 
        and xy: "{x,y} \<in> [m]^\<two>" "{x,y} \<subseteq> [m]" "card {x,y} = 2" unfolding \<G>_def binprod_def
        by force        
      define a where "a = fstt edge" 
      define b where "b = sndd edge" 
      from edgen[unfolded C_def edge] xy have id: "f x = f y" by simp
      from edgen GsCf edge have edgen: "{x,y} \<notin> Gs" by auto
      from edgen[unfolded Gs_def sameprod_altdef] xy have "\<not> {x,y} \<subseteq> Vs" by auto
      from fstt[OF \<open>card {x,y} = 2\<close> this, folded edge, folded a_def b_def] edge
      have  a: "a \<notin> Vs" and id_ab: "{x,y} = {a,b}" by auto
      from id_ab id have id: "f a = f b" by (auto simp: doubleton_eq_iff)
      let ?pair = "(a,b)" 
      note ab = xy[unfolded id_ab]
      from f[unfolded \<F>_def] ab have fb: "f b \<in> [k - 1]" by auto
      note edge = edge[unfolded id_ab]
      from edgep[unfolded edge] v_mem_sub[OF \<open>card {a,b} = 2\<close>, of "G i"] id
      have "?prop i edge" using edge ab a fb unfolding a_def b_def by auto
      from someI[of "?prop i", OF this] have "?prop i (pair i)" using i unfolding pair_def by auto
      from this[folded u_def w_def] edgep
      have "u i \<in> v (G i) - Vs" "w i \<in> v (G i)" "pair i \<in> G i \<inter> [m]^\<two>" 
        "f (u i) = f (w i)" "f (w i) \<in> [k - 1]" "pair i = {u i, w i}" 
        by auto
    } note uw = this
    from uw(3) have Pi: "pair \<in> Pi\<^sub>E {0 ..< p} G" unfolding pair_def by auto
    define Us where "Us = u ` {0 ..< p}" 
    define Ws where "Ws = [m] - Us"
    {
      fix i
      assume i: "i < p"
      note uwi = uw[OF this]
      from uwi have ex: "\<exists> x \<in> [k - 1]. f ` {u i, w i} = {x}" by auto
      from uwi have *: "u i \<in> [m]" "w i \<in> [m]" "{u i, w i} \<in> G i" by (auto simp: sameprod_altdef)
      have "w i \<notin> Us" 
      proof
        assume "w i \<in> Us" 
        then obtain j where j: "j < p" and wij: "w i = u j" unfolding Us_def by auto
        with uwi have ij: "i \<noteq> j" unfolding binprod_def by auto
        note uwj = uw[OF j]
        from ij i j Si[unfolded bij_betw_def] 
        have diff: "v (G i) \<noteq> v (G j)" unfolding G(2)[OF i] G(2)[OF j] inj_on_def by auto      
        from uwi wij have uj: "u j \<in> v (G i)" by auto
        with \<open>sunflower S\<close>[unfolded sunflower_def, rule_format] G(4)[OF i] G(4)[OF j] uwj(1) diff
        have "u j \<in> \<Inter> S" by blast
        with uwj(1)[unfolded Vs_def] show False by simp
      qed
      with * have wi: "w i \<in> Ws" unfolding Ws_def by auto
      from uwi have wi2: "w i \<in> v (G i)" by auto
      define W where "W = Ws \<inter> v (G i)" 
      from G(1)[OF i] X[unfolded \<G>l_def \<G>l_def] i_props[OF i] 
      have "finite (v (G i))" "card (v (G i)) \<le> l" by auto
      with card_mono[OF this(1), of W] have 
        W: "finite W" "card W \<le> l" "W \<subseteq> [m] - Us" unfolding W_def Ws_def by auto
      from wi wi2 have wi: "w i \<in> W" unfolding W_def by auto
      from wi ex W * have "{u i, w i} \<in> G i \<and> u i \<in> [m] \<and> w i \<in> [m] - Us \<and> f (u i) = f (w i)" by force
    } note uw1 = this
    have inj: "inj_on u {0 ..< p}" 
    proof -
      {
        fix i j
        assume i: "i < p" and j: "j < p" 
          and id: "u i = u j" and ij: "i \<noteq> j" 
        from ij i j Si[unfolded bij_betw_def] 
        have diff: "v (G i) \<noteq> v (G j)" unfolding G(2)[OF i] G(2)[OF j] inj_on_def by auto      
        from uw[OF i] have ui: "u i \<in> v (G i) - Vs" by auto
        from uw[OF j, folded id] have uj: "u i \<in> v (G j)" by auto
        with \<open>sunflower S\<close>[unfolded sunflower_def, rule_format] G(4)[OF i] G(4)[OF j] uw[OF i] diff
        have "u i \<in> \<Inter> S" by blast
        with ui have False unfolding Vs_def by auto
      }
      thus ?thesis unfolding inj_on_def by fastforce
    qed
    have card: "card ([m] - Us) = m - p" 
    proof (subst card_Diff_subset)
      show "finite Us" unfolding Us_def by auto
      show "Us \<subseteq> [m]" unfolding Us_def using uw1 by auto
      have "card Us = p" unfolding Us_def using inj
        by (simp add: card_image)
      thus "card [m] - card Us = m - p" by simp
    qed
    hence "(\<forall> i < p. pair i \<in> G i) \<and> inj_on u {0 ..< p} \<and> (\<forall> i < p. w i \<in> [m] - u ` {0 ..< p} \<and> f (u i) = f (w i))" 
      using inj uw1 uw unfolding Us_def by auto
    from this[unfolded u_def w_def] Pi card[unfolded Us_def u_def w_def]
    have "\<exists> e \<in> Pi\<^sub>E {0..<p} G. (\<forall>i<p. e i \<in> G i) \<and>
      card ([m] - (\<lambda>i. fstt (e i)) ` {0..<p}) = m - p \<and>
      (\<forall>i<p. sndd (e i) \<in> [m] - (\<lambda>i. fstt (e i)) ` {0..<p} \<and> f (fstt (e i)) = f (sndd (e i)))" 
      by blast
  } note fMem = this
  define Pi2 where "Pi2 W = Pi\<^sub>E ([m] - W) (\<lambda> _. [k - 1])" for W
  define merge where "merge = 
    (\<lambda> e  (g :: nat \<Rightarrow> nat) v. if v \<in> (\<lambda> i. fstt (e i)) ` {0 ..< p} then g (sndd (e (SOME i. i < p \<and> v = fstt (e i)))) else g v)"     
  let ?W = "\<lambda> e. (\<lambda> i. fstt (e i)) ` {0..<p}" 
  have "ACC_cf Y - ACC_cf X \<subseteq> { merge e g | e g. e \<in> Pi\<^sub>E {0..<p} G \<and> card ([m] - ?W e) = m - p \<and> g \<in> Pi2 (?W e)}"
    (is "_ \<subseteq> ?R")
  proof
    fix f
    assume mem: "f \<in> ACC_cf Y - ACC_cf X" 
    with ACC_cf_\<F> have "f \<in> \<F>" by auto
    hence f: "f \<in> [m] \<rightarrow>\<^sub>E [k - 1]" unfolding \<F>_def .
    from fMem[OF mem] obtain e where e: "e \<in> Pi\<^sub>E {0..<p} G" 
     "\<And> i. i<p \<Longrightarrow> e i \<in> G i" 
     "card ([m] - ?W e) = m - p" 
     "\<And> i. i<p \<Longrightarrow> sndd (e i) \<in> [m] - ?W e \<and> f (fstt (e i)) = f (sndd (e i))" by auto
    define W where "W = ?W e" 
    note e = e[folded W_def]
    let ?g = "restrict f ([m] - W)" 
    let ?h = "merge e ?g" 
    have "f \<in> ?R"
    proof (intro CollectI exI[of _ e] exI[of _ ?g], unfold W_def[symmetric], intro conjI e)
      show "?g \<in> Pi2 W" unfolding Pi2_def using f by auto
      {
        fix v :: nat
        have "?h v = f v" 
        proof (cases "v \<in> W")
          case False
          thus ?thesis using f unfolding merge_def unfolding W_def[symmetric] by auto
        next
          case True
          from this[unfolded W_def] obtain i where i: "i < p" and v: "v = fstt (e i)" by auto
          define j where "j = (SOME j. j < p \<and> v = fstt (e j))" 
          from i v have "\<exists> j. j < p \<and> v = fstt (e j)" by auto
          from someI_ex[OF this, folded j_def] have j: "j < p" and v: "v = fstt (e j)" by auto
          have "?h v = restrict f ([m] - W) (sndd (e j))" 
            unfolding merge_def unfolding W_def[symmetric] j_def using True by auto
          also have "\<dots> = f (sndd (e j))" using e(4)[OF j] by auto
          also have "\<dots> = f (fstt (e j))" using e(4)[OF j] by auto
          also have "\<dots> = f v" using v by simp
          finally show ?thesis .
        qed
      }
      thus "f = ?h" by auto
    qed
    thus "f \<in> ?R" by auto
  qed
  also have "\<dots> \<subseteq> (\<lambda> (e,g). (merge e g)) ` (Sigma (Pi\<^sub>E {0..<p} G \<inter> {e. card ([m] - ?W e) = m - p}) (\<lambda> e. Pi2 (?W e)))" 
    (is "_ \<subseteq> ?f ` ?R")
    by auto
  finally have sub: "ACC_cf Y - ACC_cf X \<subseteq> ?f ` ?R" .
  have fin[simp,intro]: "finite [m]" "finite [k - Suc 0]" unfolding numbers_def by auto
  have finPie[simp, intro]: "finite (Pi\<^sub>E {0..<p} G)" 
    by (intro finite_PiE, auto intro: i_props)
  have finR: "finite ?R" unfolding Pi2_def
    by (intro finite_SigmaI finite_Int allI finite_PiE i_props, auto)
  have "card (ACC_cf Y - ACC_cf X) \<le> card (?f ` ?R)" 
    by (rule card_mono[OF finite_imageI[OF finR] sub])
  also have "\<dots> \<le> card ?R" 
    by (rule card_image_le[OF finR])
  also have "\<dots> = (\<Sum>e\<in>(Pi\<^sub>E {0..<p} G \<inter> {e. card ([m] - ?W e) = m - p}). card (Pi2 (?W e)))" 
    by (rule card_SigmaI, unfold Pi2_def,
    (intro finite_SigmaI allI finite_Int finite_PiE i_props, auto)+)
  also have "\<dots> = (\<Sum>e\<in>Pi\<^sub>E {0..<p} G \<inter> {e. card ([m] - ?W e) = m - p}. (k - 1) ^ (card ([m] - ?W e)))" 
    by (rule sum.cong[OF refl], unfold Pi2_def, subst card_PiE, auto)
  also have "\<dots> = (\<Sum>e\<in>Pi\<^sub>E {0..<p} G \<inter> {e. card ([m] - ?W e) = m - p}. (k - 1) ^ (m - p))" 
    by (rule sum.cong[OF refl], rule arg_cong[of _ _ "\<lambda> n. (k - 1)^n"], auto)
  also have "\<dots> \<le> (\<Sum>e\<in>Pi\<^sub>E {0..<p} G. (k - 1) ^ (m - p))" 
    by (rule sum_mono2, auto)
  also have "\<dots> = card (Pi\<^sub>E {0..<p} G) * (k - 1) ^ (m - p)" by simp
  also have "\<dots> = (\<Prod>i = 0..<p. card (G i)) * (k - 1) ^ (m - p)"
    by (subst card_PiE, auto)
  also have "\<dots> \<le> (\<Prod>i = 0..<p. (k - 1) div 2) * (k - 1) ^ (m - p)"
  proof - 
    {
      fix i
      assume i: "i < p" 
      from G[OF i] X
      have GiG: "G i \<in> \<G>"
        unfolding \<G>l_def \<G>_def \<G>_def sameprod_altdef by force
      from i_props[OF i] have finGi: "finite (G i)" by auto
      have finvGi: "finite (v (G i))" by (rule finite_vG, insert i_props[OF i], auto)
      have "card (G i) \<le> card ((v (G i))^\<two>)" 
        by (intro card_mono[OF sameprod_finite], rule finvGi, rule v_\<G>_2[OF GiG])
      also have "\<dots> \<le> l choose 2"
      proof (subst card_sameprod[OF finvGi], rule choose_mono)
        show "card (v (G i)) \<le> l" using i_props[OF i] unfolding ti_def si_def by simp
      qed
      also have "l choose 2 = l * (l - 1) div 2" unfolding choose_two by simp
      also have "l * (l - 1) = k - l" unfolding kl2 power2_eq_square by (simp add: algebra_simps)
      also have "\<dots> div 2 \<le> (k - 1) div 2" 
        by (rule div_le_mono, insert l2, auto)    
      finally have "card (G i) \<le> (k - 1) div 2" .
    } 
    thus ?thesis by (intro mult_right_mono prod_mono, auto)
  qed
  also have "\<dots> = ((k - 1) div 2) ^ p * (k - 1) ^ (m - p)" 
    by simp
  also have "\<dots> \<le> ((k - 1) ^ p div (2^p)) * (k - 1) ^ (m - p)" 
    by (rule mult_right_mono; auto simp: div_mult_pow_le)
  also have "\<dots> \<le> ((k - 1) ^ p * (k - 1) ^ (m - p)) div 2^p" 
    by (rule div_mult_le)
  also have "\<dots> = (k - 1)^m div 2^p"  
  proof - 
    have "p + (m - p) = m" using mp by simp
    thus ?thesis by (subst power_add[symmetric], simp)
  qed
  finally have "card (ACC_cf Y - ACC_cf X) \<le> (k - 1) ^ m div 2 ^ p" .
  hence "2 ^ p * card (ACC_cf Y - ACC_cf X) \<le> 2^p * ((k - 1) ^ m div 2 ^ p)" by simp
  also have "\<dots> \<le> (k - 1)^m"  by simp
  finally show "2^p * card (ACC_cf Y - ACC_cf X) \<le> (k - 1) ^ m" .
qed


text \<open>Definition 6\<close>

function PLU_main :: "graph set \<Rightarrow> graph set \<times> nat" where
  "PLU_main X = (if X \<subseteq> \<G>l \<and> L < card (v_gs X) then
     map_prod id Suc (PLU_main (plucking_step X)) else
     (X, 0))"
  by pat_completeness auto

termination 
proof (relation "measure (\<lambda> X. card (v_gs X))", force, goal_cases)
  case (1 X)
  hence "X \<subseteq> \<G>l" and LL: "L < card (v_gs X)" by auto
  from plucking_step(1)[OF this refl]
  have "card (v_gs (plucking_step X)) \<le> card (v_gs X) - p + 1" .
  also have "\<dots> < card (v_gs X)" using p L3 LL
    by auto
  finally show ?case by simp
qed

declare PLU_main.simps[simp del]

definition PLU :: "graph set \<Rightarrow> graph set" where
  "PLU X = fst (PLU_main X)" 

text \<open>Lemma 7\<close>

lemma PLU_main_n: assumes "X \<subseteq> \<G>l" and "PLU_main X = (Z, n)" 
  shows "n * (p - 1) \<le> card (v_gs X)" 
  using assms 
proof (induct X  arbitrary: Z n  rule: PLU_main.induct)
  case (1 X Z n)
  note [simp] = PLU_main.simps[of X]
  show ?case
  proof (cases "card (v_gs X) \<le> L")
    case True
    thus ?thesis using 1 by auto
  next
    case False
    define Y where "Y = plucking_step X" 
    obtain q where PLU: "PLU_main Y = (Z, q)" and n: "n = Suc q" 
      using \<open>PLU_main X = (Z,n)\<close>[unfolded PLU_main.simps[of X], folded Y_def] using False 1(2) by (cases "PLU_main Y", auto)    
    from False have L: "card (v_gs X) > L" by auto
    note step = plucking_step[OF 1(2) this Y_def]
    from False 1 have "X \<subseteq> \<G>l \<and> L < card (v_gs X)" by auto
    note IH = 1(1)[folded Y_def, OF this step(2) PLU]
    have "n * (p - 1) = (p - 1) + q * (p - 1)" unfolding n by simp
    also have "\<dots> \<le> (p - 1) + card (v_gs Y)" using IH by simp
    also have "\<dots> \<le> p - 1 + (card (v_gs X) - p + 1)" using step(1) by simp
    also have "\<dots> = card (v_gs X)" using L Lp p by simp
    finally show ?thesis .
  qed
qed

text \<open>Definition 8\<close>

definition sqcup :: "graph set \<Rightarrow> graph set \<Rightarrow> graph set" (infixl "\<squnion>" 65) where
  "X \<squnion> Y = PLU (X \<union> Y)" 

definition sqcap :: "graph set \<Rightarrow> graph set \<Rightarrow> graph set" (infixl "\<sqinter>" 65) where
  "X \<sqinter> Y = PLU (X \<odot>l Y)" 

definition deviate_pos_cup :: "graph set \<Rightarrow> graph set \<Rightarrow> graph set" ("\<partial>\<squnion>Pos") where
  "\<partial>\<squnion>Pos X Y = POS \<inter> ACC (X \<union> Y) - ACC (X \<squnion> Y)" 

definition deviate_pos_cap :: "graph set \<Rightarrow> graph set \<Rightarrow> graph set" ("\<partial>\<sqinter>Pos") where
  "\<partial>\<sqinter>Pos X Y = POS \<inter> ACC (X \<odot> Y) - ACC (X \<sqinter> Y)" 

definition deviate_neg_cup :: "graph set \<Rightarrow> graph set \<Rightarrow> colorf set" ("\<partial>\<squnion>Neg") where
  "\<partial>\<squnion>Neg X Y = ACC_cf (X \<squnion> Y) - ACC_cf (X \<union> Y)" 

definition deviate_neg_cap :: "graph set \<Rightarrow> graph set \<Rightarrow> colorf set" ("\<partial>\<sqinter>Neg") where
  "\<partial>\<sqinter>Neg X Y = ACC_cf (X \<sqinter> Y) - ACC_cf (X \<odot> Y)" 

text \<open>Lemma 9 -- without applying Lemma 7\<close>

lemma PLU_main: assumes "X \<subseteq> \<G>l" 
  and "PLU_main X = (Z, n)" 
shows "Z \<in> \<P>L\<G>l
  \<and> (Z = {} \<longleftrightarrow> X = {})
  \<and> POS \<inter> ACC X \<subseteq> ACC Z
  \<and> 2 ^ p * card (ACC_cf Z - ACC_cf X) \<le> (k - 1) ^ m * n" 
  using assms
proof (induct X  arbitrary: Z n  rule: PLU_main.induct)
  case (1 X Z n)
  note [simp] = PLU_main.simps[of X]
  show ?case
  proof (cases "card (v_gs X) \<le> L")
    case True
    from True show ?thesis using 1 by (auto simp: id \<P>L\<G>l_def)
  next
    case False
    define Y where "Y = plucking_step X" 
    obtain q where PLU: "PLU_main Y = (Z, q)" and n: "n = Suc q" 
      using \<open>PLU_main X = (Z,n)\<close>[unfolded PLU_main.simps[of X], folded Y_def] using False 1(2) by (cases "PLU_main Y", auto)    
    from False have "card (v_gs X) > L" by auto
    note step = plucking_step[OF 1(2) this Y_def]
    from False 1 have "X \<subseteq> \<G>l \<and> L < card (v_gs X)" by auto
    note IH = 1(1)[folded Y_def, OF this step(2) PLU] \<open>Y \<noteq> {}\<close>
    let ?Diff = "\<lambda> X Y. ACC_cf X - ACC_cf Y" 
    have finNEG: "finite NEG"
      using NEG_\<G> infinite_super by blast
    have "?Diff Z X \<subseteq> ?Diff Z Y \<union> ?Diff Y X" by auto
    from card_mono[OF finite_subset[OF _ finite_\<F>] this] ACC_cf_\<F>
    have "2 ^ p * card (?Diff Z X) \<le> 2 ^ p * card (?Diff Z Y \<union> ?Diff Y X)" by auto
    also have "\<dots> \<le> 2 ^ p * (card (?Diff Z Y) + card (?Diff Y X))" 
      by (rule mult_left_mono, rule card_Un_le, simp)
    also have "\<dots> = 2 ^ p * card (?Diff Z Y) + 2 ^ p * card (?Diff Y X)" 
      by (simp add: algebra_simps)
    also have "\<dots> \<le> ((k - 1) ^ m) * q + (k - 1) ^ m" using IH step by auto
    also have "\<dots> = ((k - 1) ^ m) * Suc q" by (simp add: ac_simps)
    finally have c: "2 ^ p * card (ACC_cf Z - ACC_cf X) \<le> ((k - 1) ^ m) * Suc q" by simp
    from False have "X \<noteq> {}" by auto
    thus ?thesis unfolding n using IH step c by auto
  qed
qed

text \<open>Lemma 9\<close>

lemma assumes X: "X \<in> \<P>L\<G>l" and Y: "Y \<in> \<P>L\<G>l"
  shows PLU_union: "PLU (X \<union> Y) \<in> \<P>L\<G>l" and
  sqcup: "X \<squnion> Y \<in> \<P>L\<G>l" and
  sqcup_sub: "POS \<inter> ACC (X \<union> Y) \<subseteq> ACC (X \<squnion> Y)" and
  deviate_pos_cup: "\<partial>\<squnion>Pos X Y = {}" and
  deviate_neg_cup: "card (\<partial>\<squnion>Neg X Y) < (k - 1)^m * L / 2^(p - 1)" 
proof -
  obtain Z n where res: "PLU_main (X \<union> Y) = (Z, n)" by force
  hence PLU: "PLU (X \<union> Y) = Z" unfolding PLU_def by simp
  from X Y have XY: "X \<union> Y \<subseteq> \<G>l" unfolding \<P>L\<G>l_def by auto
  note main = PLU_main[OF this(1) res]
  from main show "PLU (X \<union> Y) \<in> \<P>L\<G>l" unfolding PLU by simp
  thus "X \<squnion> Y \<in> \<P>L\<G>l" unfolding sqcup_def .
  from main show "POS \<inter> ACC (X \<union> Y) \<subseteq> ACC (X \<squnion> Y)" 
    unfolding sqcup_def PLU by simp
  thus "\<partial>\<squnion>Pos X Y = {}" unfolding deviate_pos_cup_def PLU sqcup_def by auto
  have "card (v_gs (X \<union> Y)) \<le> card (v_gs X) + card (v_gs Y)" 
    unfolding v_gs_union by (rule card_Un_le)
  also have "\<dots> \<le> L + L" using X Y unfolding \<P>L\<G>l_def by simp
  finally have "card (v_gs (X \<union> Y)) \<le> 2 * L" by simp
  with PLU_main_n[OF XY(1) res] have "n * (p - 1) \<le> 2 * L" by simp
  with p Lm m2 have n: "n < 2 * L" by (cases n, auto, cases "p - 1", auto)
  let ?r = real
  have *: "(k - 1) ^ m > 0" using k l2 by simp
  have "2 ^ p * card (\<partial>\<squnion>Neg X Y) \<le> 2 ^ p * card (ACC_cf Z - ACC_cf (X \<union> Y))" unfolding deviate_neg_cup_def PLU sqcup_def
    by (rule mult_left_mono, rule card_mono[OF finite_subset[OF _ finite_\<F>]], insert ACC_cf_\<F>, force, auto)
  also have "\<dots> \<le> (k - 1) ^ m * n" using main by simp
  also have "\<dots> < (k - 1) ^ m * (2 * L)" unfolding mult_less_cancel1 using n * by simp
  also have "\<dots> = 2 * ((k - 1) ^ m * L)" by simp
  finally have "2 * (2^(p - 1) * card (\<partial>\<squnion>Neg X Y)) < 2 * ((k - 1) ^ m * L)" using p by (cases p, auto)
  hence "2 ^ (p - 1) * card (\<partial>\<squnion>Neg X Y) < (k - 1)^m * L" by simp
  hence "?r (2 ^ (p - 1) * card (\<partial>\<squnion>Neg X Y)) < ?r ((k - 1)^m * L)" by linarith
  thus "card (\<partial>\<squnion>Neg X Y) < (k - 1)^m * L / 2^(p - 1)" by (simp add: field_simps)
qed

text \<open>Lemma 10\<close>

lemma assumes X: "X \<in> \<P>L\<G>l" and Y: "Y \<in> \<P>L\<G>l"
  shows PLU_joinl: "PLU (X \<odot>l Y) \<in> \<P>L\<G>l" and
  sqcap: "X \<sqinter> Y \<in> \<P>L\<G>l" and
  deviate_neg_cap: "card (\<partial>\<sqinter>Neg X Y) < (k - 1)^m * L^2 / 2^(p - 1)" and
  deviate_pos_cap: "card (\<partial>\<sqinter>Pos X Y) \<le> ((m - l - 1) choose (k - l - 1)) * L^2" 
proof -
  obtain Z n where res: "PLU_main (X \<odot>l Y) = (Z, n)" by force
  hence PLU: "PLU (X \<odot>l Y) = Z" unfolding PLU_def by simp
  from X Y have XY: "X \<subseteq> \<G>l" "Y \<subseteq> \<G>l" "X \<subseteq> \<G>" "Y \<subseteq> \<G>" unfolding \<P>L\<G>l_def \<G>l_def by auto  
  have sub: "X \<odot>l Y \<subseteq> \<G>l" unfolding odotl_def using XY 
    by (auto split: option.splits)
  note main = PLU_main[OF sub res]
  note finV = finite_v_gs_Gl[OF XY(1)] finite_v_gs_Gl[OF XY(2)]
  have "X \<odot> Y \<subseteq> \<G>" by (rule odot_\<G>, insert XY, auto simp: \<G>l_def) 
  hence XYD: "X \<odot> Y \<subseteq> \<G>" by auto
  have finvXY: "finite (v_gs (X \<odot> Y))" by (rule finite_v_gs[OF XYD])
  have "card (v_gs (X \<odot> Y)) \<le> card (v_gs X) * card (v_gs Y)" 
    using XY(1-2) by (intro card_v_gs_join, auto simp: \<G>l_def)
  also have "\<dots> \<le> L * L" using X Y unfolding \<P>L\<G>l_def 
    by (intro mult_mono, auto)
  also have "\<dots> = L^2" by algebra
  finally have card_join: "card (v_gs (X \<odot> Y)) \<le> L^2" .
  with card_mono[OF finvXY v_gs_mono[OF joinl_join]]
  have card: "card (v_gs (X \<odot>l Y)) \<le> L^2" by simp
  with PLU_main_n[OF sub res] have "n * (p - 1) \<le> L^2" by simp
  with p Lm m2 have n: "n < 2 * L^2" by (cases n, auto, cases "p - 1", auto)
  have *: "(k - 1) ^ m > 0" using k l2 by simp
  show "PLU (X \<odot>l Y) \<in> \<P>L\<G>l" unfolding PLU using main by auto
  thus "X \<sqinter> Y \<in> \<P>L\<G>l" unfolding sqcap_def .
  let ?r = real
  have "2^p * card (\<partial>\<sqinter>Neg X Y) \<le> 2 ^ p * card (ACC_cf Z - ACC_cf (X \<odot>l Y))"
    unfolding deviate_neg_cap_def PLU sqcap_def
    by (rule mult_left_mono, rule card_mono[OF finite_subset[OF _ finite_\<F>]], insert ACC_cf_\<F>, force, 
      insert ACC_cf_mono[OF joinl_join, of X Y], auto)
  also have "\<dots> \<le> (k - 1) ^ m * n" using main by simp
  also have "\<dots> < (k - 1) ^ m * (2 * L^2)" unfolding mult_less_cancel1 using n * by simp
  finally have "2 * (2^(p - 1) * card (\<partial>\<sqinter>Neg X Y)) < 2 * ((k - 1) ^ m * L^2)" using p by (cases p, auto)
  hence "2 ^ (p - 1) * card (\<partial>\<sqinter>Neg X Y) < (k - 1)^m * L^2" by simp
  hence "?r (2 ^ (p - 1) * card (\<partial>\<sqinter>Neg X Y)) < (k - 1)^m * L^2" by linarith
  thus "card (\<partial>\<sqinter>Neg X Y) < (k - 1)^m * L^2 / 2^(p - 1)" by (simp add: field_simps)
  (* now for the next approximation *)
  define Vs where "Vs = v_gs (X \<odot> Y) \<inter> {V . V \<subseteq> [m] \<and> card V \<ge> Suc l}" 
  define C where "C (V :: nat set) = (SOME C. C \<subseteq> V \<and> card C = Suc l)" for V
  define K where "K C = { W. W \<subseteq> [m] - C \<and> card W = k - Suc l }" for C
  define merge where "merge C V = (C \<union> V)^\<two>" for C V :: "nat set" 
  define GS where "GS = { merge (C V) W | V W. V \<in> Vs \<and> W \<in> K (C V)}"
  {
    fix V
    assume V: "V \<in> Vs" 
    hence card: "card V \<ge> Suc l" and Vm: "V \<subseteq> [m]" unfolding Vs_def by auto
    from card obtain D where C: "D \<subseteq> V" and cardV: "card D = Suc l" 
      by (rule obtain_subset_with_card_n)
    hence "\<exists> C. C \<subseteq> V \<and> card C = Suc l" by blast
    from someI_ex[OF this, folded C_def] have *: "C V \<subseteq> V" "card (C V) = Suc l" 
      by blast+
    with Vm have sub: "C V \<subseteq> [m]" by auto
    from finite_subset[OF this] have finCV: "finite (C V)" unfolding numbers_def by simp
    have "card (K (C V)) = (m - Suc l) choose (k - Suc l)" unfolding K_def
    proof (subst n_subsets, (rule finite_subset[of _ "[m]"], auto)[1], rule arg_cong[of _ _ "\<lambda> x. x choose _"])
      show "card ([m] - C V) = m - Suc l" 
        by (subst card_Diff_subset, insert sub * finCV, auto)
    qed
    note * finCV sub this
  } note Vs_C = this
  have finK: "finite (K V)" for V unfolding K_def by auto
  {
    fix G
    assume G: "G \<in> POS \<inter> ACC (X \<odot> Y)" 
    have "G \<in> ACC (X \<odot>l Y) \<union> GS"
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      with G have G: "G \<in> POS" "G \<in> ACC (X \<odot> Y)" "G \<notin> ACC (X \<odot>l Y)" 
        and contra: "G \<notin> GS" by auto
      from G(1)[unfolded \<K>_def] have "card (v G) = k \<and> (v G)^\<two> = G" and G0: "G \<in> \<G>"
        by auto
      hence vGk: "card (v G) = k" "(v G)^\<two> = G" by auto
      from G0 have vm: "v G \<subseteq> [m]" by (rule v_\<G>)
      from G(2-3)[unfolded ACC_def accepts_def] obtain H 
        where H: "H \<in> X \<odot> Y" "H \<notin> X \<odot>l Y" 
          and HG: "H \<subseteq> G" by auto
      from v_mono[OF HG] have vHG: "v H \<subseteq> v G" by auto
      {
        from H(1)[unfolded odot_def] obtain D E where D: "D \<in> X" and E: "E \<in> Y" and HDE: "H = D \<union> E" 
          by force
        from D E X Y have Dl: "D \<in> \<G>l" "E \<in> \<G>l" unfolding \<P>L\<G>l_def by auto
        have Dp: "D \<in> \<G>" using Dl by (auto simp: \<G>l_def)
        have Ep: "E \<in> \<G>" using Dl by (auto simp: \<G>l_def)
        from Dl HDE have HD: "H \<in> \<G>" unfolding \<G>l_def by auto
        have HG0: "H \<in> \<G>" using Dp Ep unfolding HDE by auto
        have HDL: "H \<notin> \<G>l"
        proof
          assume "H \<in> \<G>l"
          hence "H \<in> X \<odot>l Y"
            unfolding odotl_def HDE odot_def using D E by blast
          thus False using H by auto
        qed
        from HDL HD have HGl: "H \<notin> \<G>l" unfolding \<G>l_def by auto
        have vm: "v H \<subseteq> [m]" using HG0 by (rule v_\<G>)
        have lower: "l < card (v H)" using HGl HG0 unfolding \<G>l_def by auto
        have "v H \<in> Vs" unfolding Vs_def using lower vm H unfolding v_gs_def by auto
      } note in_Vs = this
      note C = Vs_C[OF this]
      let ?C = "C (v H)" 
      from C vHG have CG: "?C \<subseteq> v G" by auto
      hence id: "v G = ?C \<union> (v G - ?C)" by auto
      from arg_cong[OF this, of card] vGk(1) C
      have "card (v G - ?C) = k - Suc l"
        by (metis CG card_Diff_subset)
      hence "v G - ?C \<in> K ?C" unfolding K_def using vm by auto
      hence "merge ?C (v G - ?C) \<in> GS" unfolding GS_def using in_Vs by auto
      also have "merge ?C (v G - ?C) = v G^\<two>" unfolding merge_def
        by (rule arg_cong[of _ _ sameprod], insert id, auto)
      also have "\<dots> = G" by fact
      finally have "G \<in> GS" .
      with contra show False ..
    qed
  }
  hence "\<partial>\<sqinter>Pos X Y \<subseteq> (POS \<inter> ACC (X \<odot>l Y) - ACC (X \<sqinter> Y)) \<union> GS"
    unfolding deviate_pos_cap_def by auto
  also have "POS \<inter> ACC (X \<odot>l Y) - ACC (X \<sqinter> Y) = {}"
  proof -
    have "POS - ACC (X \<sqinter> Y) \<subseteq> UNIV - ACC (X \<odot>l Y)" 
      unfolding sqcap_def using PLU main by auto
    thus ?thesis by auto
  qed
  finally have sub: "\<partial>\<sqinter>Pos X Y \<subseteq> GS" by auto
  have finVs: "finite Vs" unfolding Vs_def numbers_def by simp 
  let ?Sig = "Sigma Vs (\<lambda> V. K (C V))" 
  have GS_def: "GS = (\<lambda> (V,W). merge (C V) W) ` ?Sig" unfolding GS_def 
    by auto
  have finSig: "finite ?Sig" using finVs finK by simp
  have finGS: "finite GS" unfolding GS_def 
    by (rule finite_imageI[OF finSig])
  have "card (\<partial>\<sqinter>Pos X Y) \<le> card GS" by (rule card_mono[OF finGS sub])
  also have "\<dots> \<le> card ?Sig" unfolding GS_def
    by (rule card_image_le[OF finSig])
  also have "\<dots> = (\<Sum>a\<in>Vs. card (K (C a)))"
    by (rule card_SigmaI[OF finVs], auto simp: finK)
  also have "\<dots> = (\<Sum>a\<in>Vs. (m - Suc l) choose (k - Suc l))" using Vs_C
    by (intro sum.cong, auto)
  also have "\<dots> = ((m - Suc l) choose (k - Suc l)) * card Vs" 
    by simp
  also have "\<dots> \<le> ((m - Suc l) choose (k - Suc l)) * L^2" 
  proof (rule mult_left_mono)
    have "card Vs \<le> card (v_gs (X \<odot> Y))" 
      by (rule card_mono[OF finvXY], auto simp: Vs_def)
    also have "\<dots> \<le> L^2" by fact
    finally show "card Vs \<le> L^2" .
  qed simp
  finally show "card (\<partial>\<sqinter>Pos X Y) \<le> ((m - l - 1) choose (k - l - 1)) * L^2"
    by simp 
qed
end

  
subsection \<open>Formalism\<close>

text \<open>Fix a variable set of cardinality m over 2.\<close>

locale forth_assumptions = third_assumptions + 
  fixes \<V> :: "'a set" and \<pi> :: "'a \<Rightarrow> vertex set" 
  assumes cV: "card \<V> = (m choose 2)" 
  and bij_betw_\<pi>: "bij_betw \<pi> \<V> ([m]^\<two>)" 
begin

definition n where "n = (m choose 2)" 

text \<open>the formulas over the fixed variable set\<close>

definition \<A> :: "'a mformula set" where
  "\<A> = { \<phi>. vars \<phi> \<subseteq> \<V>}" 

lemma \<A>_simps[simp]: 
  "FALSE \<in> \<A>" 
  "(Var x \<in> \<A>) = (x \<in> \<V>)" 
  "(Conj \<phi> \<psi> \<in> \<A>) = (\<phi> \<in> \<A> \<and> \<psi> \<in> \<A>)" 
  "(Disj \<phi> \<psi> \<in> \<A>) = (\<phi> \<in> \<A> \<and> \<psi> \<in> \<A>)" 
  by (auto simp: \<A>_def)

lemma inj_on_\<pi>: "inj_on \<pi> \<V>"
  using bij_betw_\<pi> by (metis bij_betw_imp_inj_on) 

lemma \<pi>m2[simp,intro]: "x \<in> \<V> \<Longrightarrow> \<pi> x \<in> [m]^\<two>" 
  using bij_betw_\<pi> by (rule bij_betw_apply)

lemma card_v_\<pi>[simp,intro]: assumes "x \<in> \<V>" 
  shows "card (v {\<pi> x}) = 2" 
proof -
  from \<pi>m2[OF assms] have mem: "\<pi> x \<in> [m]^\<two>" by auto
  from this[unfolded binprod_def] obtain a b where \<pi>: "\<pi> x = {a,b}" and diff: "a \<noteq> b" 
    by auto
  hence "v {\<pi> x} = {a,b}" unfolding v_def by auto
  thus ?thesis using diff by simp
qed

lemma \<pi>_singleton[simp,intro]: assumes "x \<in> \<V>"
  shows "{\<pi> x} \<in> \<G>"  
    "{{\<pi> x}} \<in> \<P>L\<G>l"  
  using assms L3 l2
  by (auto simp: \<G>_def \<P>L\<G>l_def v_gs_def \<G>l_def)

lemma empty_\<P>L\<G>l[simp,intro]: "{} \<in> \<P>L\<G>l" 
  by (auto simp: \<G>_def \<P>L\<G>l_def v_gs_def \<G>l_def)

fun SET :: "'a mformula \<Rightarrow> graph set" where
  "SET FALSE = {}" 
| "SET (Var x) = {{\<pi> x}}" 
| "SET (Disj \<phi> \<psi>) = SET \<phi> \<union> SET \<psi>" 
| "SET (Conj \<phi> \<psi>) = SET \<phi> \<odot> SET \<psi>" 

lemma ACC_cf_SET[simp]: 
  "ACC_cf (SET (Var x)) = {f \<in> \<F>. \<pi> x \<in> C f}" 
  "ACC_cf (SET FALSE) = {}"
  "ACC_cf (SET (Disj \<phi> \<psi>)) = ACC_cf (SET \<phi>) \<union> ACC_cf (SET \<psi>)"
  "ACC_cf (SET (Conj \<phi> \<psi>)) = ACC_cf (SET \<phi>) \<inter> ACC_cf (SET \<psi>)"
  using ACC_cf_odot 
  by (auto simp: ACC_cf_union ACC_cf_empty, auto simp: ACC_cf_def accepts_def)

lemma ACC_SET[simp]: 
  "ACC (SET (Var x)) = {G \<in> \<G>. \<pi> x \<in> G}" 
  "ACC (SET FALSE) = {}"
  "ACC (SET (Disj \<phi> \<psi>)) = ACC (SET \<phi>) \<union> ACC (SET \<psi>)"
  "ACC (SET (Conj \<phi> \<psi>)) = ACC (SET \<phi>) \<inter> ACC (SET \<psi>)"
  by (auto simp: ACC_union ACC_odot, auto simp: ACC_def accepts_def)

lemma SET_\<G>: "\<phi> \<in> tf_mformula \<Longrightarrow> \<phi> \<in> \<A> \<Longrightarrow> SET \<phi> \<subseteq> \<G>" 
proof (induct \<phi> rule: tf_mformula.induct)
  case (tf_Conj \<phi> \<psi>)
  hence "SET \<phi> \<subseteq> \<G>" "SET \<psi> \<subseteq> \<G>" by auto
  from odot_\<G>[OF this] show ?case by simp
qed auto
  
fun APR :: "'a mformula \<Rightarrow> graph set" where
  "APR FALSE = {}" 
| "APR (Var x) = {{\<pi> x}}" 
| "APR (Disj \<phi> \<psi>) = APR \<phi> \<squnion> APR \<psi>" 
| "APR (Conj \<phi> \<psi>) = APR \<phi> \<sqinter> APR \<psi>" 

lemma APR: "\<phi> \<in> tf_mformula \<Longrightarrow> \<phi> \<in> \<A> \<Longrightarrow> APR \<phi> \<in> \<P>L\<G>l"
  by (induct \<phi> rule: tf_mformula.induct, auto intro!: sqcup sqcap)

definition ACC_cf_mf :: "'a mformula \<Rightarrow> colorf set" where
  "ACC_cf_mf \<phi> = ACC_cf (SET \<phi>)" 

definition ACC_mf :: "'a mformula \<Rightarrow> graph set" where
  "ACC_mf \<phi> = ACC (SET \<phi>)" 

definition deviate_pos :: "'a mformula \<Rightarrow> graph set" ("\<partial>Pos") where
  "\<partial>Pos \<phi> = POS \<inter> ACC_mf \<phi> - ACC (APR \<phi>)" 

definition deviate_neg :: "'a mformula \<Rightarrow> colorf set" ("\<partial>Neg") where
  "\<partial>Neg \<phi> = ACC_cf (APR \<phi>) - ACC_cf_mf \<phi>" 

text \<open>Lemma 11.1\<close>

lemma deviate_subset_Disj: 
  "\<partial>Pos (Disj \<phi> \<psi>) \<subseteq> \<partial>\<squnion>Pos (APR \<phi>) (APR \<psi>) \<union> \<partial>Pos \<phi> \<union> \<partial>Pos \<psi>"
  "\<partial>Neg (Disj \<phi> \<psi>) \<subseteq> \<partial>\<squnion>Neg (APR \<phi>) (APR \<psi>) \<union> \<partial>Neg \<phi> \<union> \<partial>Neg \<psi>"
  unfolding 
    deviate_pos_def deviate_pos_cup_def  
    deviate_neg_def deviate_neg_cup_def 
    ACC_cf_mf_def ACC_cf_SET ACC_cf_union 
    ACC_mf_def ACC_SET ACC_union 
  by auto

text \<open>Lemma 11.2\<close>

lemma deviate_subset_Conj: 
  "\<partial>Pos (Conj \<phi> \<psi>) \<subseteq> \<partial>\<sqinter>Pos (APR \<phi>) (APR \<psi>) \<union> \<partial>Pos \<phi> \<union> \<partial>Pos \<psi>" 
  "\<partial>Neg (Conj \<phi> \<psi>) \<subseteq> \<partial>\<sqinter>Neg (APR \<phi>) (APR \<psi>) \<union> \<partial>Neg \<phi> \<union> \<partial>Neg \<psi>" 
   unfolding 
    deviate_pos_def deviate_pos_cap_def 
    ACC_mf_def ACC_SET ACC_odot
    deviate_neg_def deviate_neg_cap_def 
    ACC_cf_mf_def ACC_cf_SET ACC_cf_odot 
   by auto 

lemmas deviate_subset = deviate_subset_Disj deviate_subset_Conj

lemma deviate_finite: 
  "finite (\<partial>Pos \<phi>)" 
  "finite (\<partial>Neg \<phi>)" 
  "finite (\<partial>\<squnion>Pos A B)" 
  "finite (\<partial>\<squnion>Neg A B)" 
  "finite (\<partial>\<sqinter>Pos A B)" 
  "finite (\<partial>\<sqinter>Neg A B)" 
  unfolding 
    deviate_pos_def deviate_pos_cup_def deviate_pos_cap_def 
    deviate_neg_def deviate_neg_cup_def deviate_neg_cap_def 
  by (intro finite_subset[OF _ finite_POS_NEG], auto)+

text \<open>Lemma 12\<close>

lemma no_deviation[simp]: 
  "\<partial>Pos FALSE = {}"
  "\<partial>Neg FALSE = {}"
  "\<partial>Pos (Var x) = {}"
  "\<partial>Neg (Var x) = {}"
  unfolding deviate_pos_def deviate_neg_def
  by (auto simp add: ACC_cf_mf_def ACC_mf_def)

text \<open>Lemma 12.1-2\<close>

fun approx_pos where
  "approx_pos (Conj phi psi) = \<partial>\<sqinter>Pos (APR phi) (APR psi)" 
| "approx_pos _ = {}" 

fun approx_neg where
  "approx_neg (Conj phi psi) = \<partial>\<sqinter>Neg (APR phi) (APR psi)" 
| "approx_neg (Disj phi psi) = \<partial>\<squnion>Neg (APR phi) (APR psi)" 
| "approx_neg _ = {}"  

lemma finite_approx_pos: "finite (approx_pos \<phi>)"
  by (cases \<phi>, auto intro: deviate_finite)

lemma finite_approx_neg: "finite (approx_neg \<phi>)"
  by (cases \<phi>, auto intro: deviate_finite)

lemma card_deviate_Pos: assumes phi: "\<phi> \<in> tf_mformula" "\<phi> \<in> \<A>" 
  shows "card (\<partial>Pos \<phi>) \<le> cs \<phi> * L\<^sup>2 * ( (m - l - 1) choose (k - l - 1))" 
proof -
  let ?Pos = "\<lambda> \<phi>. \<Union> (approx_pos ` SUB \<phi>)"  
  have "\<partial>Pos \<phi> \<subseteq> ?Pos \<phi>" 
    using phi
  proof (induct \<phi> rule: tf_mformula.induct)
    case (tf_Disj \<phi> \<psi>)
    from tf_Disj have *: "\<phi> \<in> tf_mformula" "\<psi> \<in> tf_mformula" "\<phi> \<in> \<A>" "\<psi> \<in> \<A>" by auto
    note IH = tf_Disj(2)[OF *(3)] tf_Disj(4)[OF *(4)]
    have "\<partial>Pos (Disj \<phi> \<psi>) \<subseteq> \<partial>\<squnion>Pos (APR \<phi>) (APR \<psi>) \<union> \<partial>Pos \<phi> \<union> \<partial>Pos \<psi>"
      by (rule deviate_subset)
    also have "\<partial>\<squnion>Pos (APR \<phi>) (APR \<psi>) = {}"  
      by (rule deviate_pos_cup; intro APR * )
    also have "\<dots> \<union> \<partial>Pos \<phi> \<union> \<partial>Pos \<psi> \<subseteq> ?Pos \<phi> \<union> ?Pos \<psi>" using IH by auto
    also have "\<dots> \<subseteq> ?Pos (Disj \<phi> \<psi>) \<union> ?Pos (Disj \<phi> \<psi>)" 
      by (intro Un_mono, auto)
    finally show ?case by simp
  next
    case (tf_Conj \<phi> \<psi>)
    from tf_Conj have *: "\<phi> \<in> \<A>" "\<psi> \<in> \<A>"  
      by (auto intro: tf_mformula.intros)
    note IH = tf_Conj(2)[OF *(1)] tf_Conj(4)[OF *(2)]
    have "\<partial>Pos (Conj \<phi> \<psi>) \<subseteq> \<partial>\<sqinter>Pos (APR \<phi>) (APR \<psi>) \<union> \<partial>Pos \<phi> \<union> \<partial>Pos \<psi>"
      by (rule deviate_subset)
    also have "\<dots> \<subseteq> \<partial>\<sqinter>Pos (APR \<phi>) (APR \<psi>) \<union> ?Pos \<phi> \<union> ?Pos \<psi>" using IH by auto
    also have "\<dots> \<subseteq> ?Pos (Conj \<phi> \<psi>) \<union> ?Pos (Conj \<phi> \<psi>) \<union> ?Pos (Conj \<phi> \<psi>)" 
      by (intro Un_mono, insert *, auto)
    finally show ?case by simp
  qed auto
  from card_mono[OF finite_UN_I[OF finite_SUB finite_approx_pos] this]
  have "card (\<partial>Pos \<phi>) \<le> card (\<Union> (approx_pos ` SUB \<phi>))" by simp
  also have "\<dots> \<le> (\<Sum>i\<in>SUB \<phi>. card (approx_pos i))" 
    by (rule card_UN_le[OF finite_SUB])
  also have "\<dots> \<le> (\<Sum>i\<in>SUB \<phi>. L\<^sup>2 * ( (m - l - 1) choose (k - l - 1)))" 
  proof (rule sum_mono, goal_cases)
    case (1 psi)
    from phi 1 have psi: "psi \<in> tf_mformula" "psi \<in> \<A>"
      by (induct \<phi> rule: tf_mformula.induct, auto intro: tf_mformula.intros)
    show ?case 
    proof (cases psi)
      case (Conj phi1 phi2)
      from psi this have *: "phi1 \<in> tf_mformula" "phi1 \<in> \<A>" "phi2 \<in> tf_mformula" "phi2 \<in> \<A>" 
        by (cases rule: tf_mformula.cases, auto)+
      from deviate_pos_cap[OF APR[OF *(1-2)] APR[OF *(3-4)]]
      show ?thesis unfolding Conj by (simp add: ac_simps)
    qed auto
  qed
  also have "\<dots> = cs \<phi> * L\<^sup>2 * ( (m - l - 1) choose (k - l - 1))" unfolding cs_def by simp
  finally show "card (\<partial>Pos \<phi>) \<le> cs \<phi> * L\<^sup>2 * (m - l - 1 choose (k - l - 1))" by simp
qed

lemma card_deviate_Neg: assumes phi: "\<phi> \<in> tf_mformula" "\<phi> \<in> \<A>" 
  shows "card (\<partial>Neg \<phi>) \<le> cs \<phi> * L\<^sup>2 * (k - 1)^m / 2^(p - 1)"
proof -
  let ?r = real
  let ?Neg = "\<lambda> \<phi>. \<Union> (approx_neg ` SUB \<phi>)"  
  have "\<partial>Neg \<phi> \<subseteq> ?Neg \<phi>" 
    using phi
  proof (induct \<phi> rule: tf_mformula.induct)
    case (tf_Disj \<phi> \<psi>)
    from tf_Disj have *: "\<phi> \<in> tf_mformula" "\<psi> \<in> tf_mformula" "\<phi> \<in> \<A>" "\<psi> \<in> \<A>" by auto
    note IH = tf_Disj(2)[OF *(3)] tf_Disj(4)[OF *(4)]
    have "\<partial>Neg (Disj \<phi> \<psi>) \<subseteq> \<partial>\<squnion>Neg (APR \<phi>) (APR \<psi>) \<union> \<partial>Neg \<phi> \<union> \<partial>Neg \<psi>"
      by (rule deviate_subset)
    also have "\<dots> \<subseteq> \<partial>\<squnion>Neg (APR \<phi>) (APR \<psi>) \<union> ?Neg \<phi> \<union> ?Neg \<psi>" using IH by auto
    also have "\<dots> \<subseteq> ?Neg (Disj \<phi> \<psi>) \<union> ?Neg (Disj \<phi> \<psi>)  \<union> ?Neg (Disj \<phi> \<psi>)" 
      by (intro Un_mono, auto)
    finally show ?case by simp
  next
    case (tf_Conj \<phi> \<psi>)
    from tf_Conj have *: "\<phi> \<in> \<A>" "\<psi> \<in> \<A>"  
      by (auto intro: tf_mformula.intros)
    note IH = tf_Conj(2)[OF *(1)] tf_Conj(4)[OF *(2)]
    have "\<partial>Neg (Conj \<phi> \<psi>) \<subseteq> \<partial>\<sqinter>Neg (APR \<phi>) (APR \<psi>) \<union> \<partial>Neg \<phi> \<union> \<partial>Neg \<psi>"
      by (rule deviate_subset)
    also have "\<dots> \<subseteq> \<partial>\<sqinter>Neg (APR \<phi>) (APR \<psi>) \<union> ?Neg \<phi> \<union> ?Neg \<psi>" using IH by auto
    also have "\<dots> \<subseteq> ?Neg (Conj \<phi> \<psi>) \<union> ?Neg (Conj \<phi> \<psi>)  \<union> ?Neg (Conj \<phi> \<psi>)" 
      by (intro Un_mono, auto)
    finally show ?case by simp
  qed auto
  hence "\<partial>Neg \<phi> \<subseteq> \<Union> (approx_neg ` SUB \<phi>)" by auto
  from card_mono[OF finite_UN_I[OF finite_SUB finite_approx_neg] this]
  have "card (\<partial>Neg \<phi>) \<le> card (\<Union> (approx_neg ` SUB \<phi>))" .
  also have "\<dots> \<le> (\<Sum>i\<in>SUB \<phi>. card (approx_neg i))" 
    by (rule card_UN_le[OF finite_SUB])
  finally have "?r (card (\<partial>Neg \<phi>)) \<le> (\<Sum>i\<in>SUB \<phi>. card (approx_neg i))" by linarith
  also have "\<dots> = (\<Sum>i\<in>SUB \<phi>. ?r (card (approx_neg i)))" by simp 
  also have "\<dots> \<le> (\<Sum>i\<in>SUB \<phi>. L^2 * (k - 1)^m / 2^(p - 1))" 
  proof (rule sum_mono, goal_cases)
    case (1 psi)
    from phi 1 have psi: "psi \<in> tf_mformula" "psi \<in> \<A>"
      by (induct \<phi> rule: tf_mformula.induct, auto intro: tf_mformula.intros)
    show ?case 
    proof (cases psi)
      case (Conj phi1 phi2)
      from psi this have *: "phi1 \<in> tf_mformula" "phi1 \<in> \<A>" "phi2 \<in> tf_mformula" "phi2 \<in> \<A>" 
        by (cases rule: tf_mformula.cases, auto)+
      from deviate_neg_cap[OF APR[OF *(1-2)] APR[OF *(3-4)]]
      show ?thesis unfolding Conj by (simp add: ac_simps)
    next
      case (Disj phi1 phi2)
      from psi this have *: "phi1 \<in> tf_mformula" "phi1 \<in> \<A>" "phi2 \<in> tf_mformula" "phi2 \<in> \<A>" 
        by (cases rule: tf_mformula.cases, auto)+
      from deviate_neg_cup[OF APR[OF *(1-2)] APR[OF *(3-4)]]
      have "card (approx_neg psi) \<le> ((L * 1) * (k - 1) ^ m) / 2 ^ (p - 1)" 
        unfolding Disj by (simp add: ac_simps)
      also have "\<dots> \<le> ((L * L) * (k - 1) ^ m) / 2 ^ (p - 1)" 
        by (intro divide_right_mono, unfold of_nat_le_iff, intro mult_mono, insert L3, auto)  
      finally show ?thesis unfolding power2_eq_square by simp
    qed auto
  qed
  also have "\<dots> = cs \<phi> * L^2 * (k - 1)^m / 2^(p - 1)" unfolding cs_def by simp
  finally show "card (\<partial>Neg \<phi>) \<le> cs \<phi> * L\<^sup>2 * (k - 1)^m / 2^(p - 1)" . 
qed


text \<open>Lemma 12.3\<close>

lemma ACC_cf_non_empty_approx: assumes phi: "\<phi> \<in> tf_mformula" "\<phi> \<in> \<A>"
  and ne: "APR \<phi> \<noteq> {}" 
shows "card (ACC_cf (APR \<phi>)) > (k - 1)^m / 3" 
proof -
  from ne obtain E :: graph where Ephi: "E \<in> APR \<phi>"   
    by (auto simp: ACC_def accepts_def)
  from APR[OF phi, unfolded \<P>L\<G>l_def] Ephi 
  have EDl: "E \<in> \<G>l" by auto
  hence vEl: "card (v E) \<le> l" and ED: "E \<in> \<G>" 
    unfolding \<G>l_def \<G>l_def by auto
  have E: "E \<in> \<G>" using ED[unfolded \<G>l_def] by auto
  have sub: "v E \<subseteq> [m]" by (rule v_\<G>[OF E]) 
  have "l \<le> card [m]" using lm by auto
  from exists_subset_between[OF vEl this sub finite_numbers]
  obtain V where V: "v E \<subseteq> V" "V \<subseteq> [m]" "card V = l" by auto
  from finite_subset[OF V(2)] have finV: "finite V" by auto
  have finPart: "finite A" if "A \<subseteq> {P. partition_on [n] P}" for n A
    by (rule finite_subset[OF that finitely_many_partition_on], simp)
  have finmv: "finite ([m] - V)" using finite_numbers[of m] by auto
  have finK: "finite [k - 1]" unfolding numbers_def by auto
  define F where "F = {f \<in> [m] \<rightarrow>\<^sub>E [k - 1]. inj_on f V}" 
  have FF: "F \<subseteq> \<F>" unfolding \<F>_def F_def by auto
  {
    fix f
    assume f: "f \<in> F" 
    {
      from this[unfolded F_def]
      have f: "f \<in> [m] \<rightarrow>\<^sub>E [k - 1]" and inj: "inj_on f V" by auto
      from V l2 have 2: "card V \<ge> 2" by auto
      then obtain x where x: "x \<in> V" by (cases "V = {}", auto)
      have "card V = card (V - {x}) + 1" using x finV
        by (metis One_nat_def add.right_neutral add_Suc_right card_Suc_Diff1)
      with 2 have "card (V - {x}) > 0" by auto
      hence "V - {x} \<noteq> {}" by fastforce
      then obtain y where y: "y \<in> V" and diff: "x \<noteq> y" by auto
      from inj diff x y have neq: "f x \<noteq> f y" by (auto simp: inj_on_def)
      from x y diff V have "{x, y} \<in> [m]^\<two>" unfolding sameprod_altdef by auto
      with neq have "{x,y} \<in> C f" unfolding C_def by auto
      hence "C f \<noteq> {}" by auto
    }
    with NEG_\<G> FF f have CfG: "C f \<in> \<G>" "C f \<noteq> {}" by (auto simp: NEG_def)
    have "E \<subseteq> C f" 
    proof
      fix e
      assume eE: "e \<in> E" 
      with E[unfolded \<G>_def] have em: "e \<in> [m]^\<two>" by auto
      then obtain x y where e: "e = {x,y}" "x \<noteq> y" "{x,y} \<subseteq> [m]" 
        and card: "card e = 2" 
        unfolding binprod_def by auto
      from v_mem_sub[OF card eE]
      have "{x,y} \<subseteq> v E" using e by auto
      hence "{x,y} \<subseteq> V" using V by auto
      hence "f x \<noteq> f y" using e(2) f[unfolded F_def] by (auto simp: inj_on_def)
      thus "e \<in> C f" unfolding C_def using em e by auto
    qed
    with Ephi CfG have "APR \<phi> \<tturnstile> C f" 
      unfolding accepts_def by auto
    hence "f \<in> ACC_cf (APR \<phi>)" using CfG f FF unfolding ACC_cf_def by auto
  }  
  with FF have sub: "F \<subseteq> ACC_cf (APR \<phi>)" by auto
  from card_mono[OF finite_subset[OF _ finite_ACC] this]
  have approx: "card F \<le> card (ACC_cf (APR \<phi>))" by auto
  from card_inj_on_subset_funcset[OF finite_numbers finK V(2), unfolded card_numbers V(3),
      folded F_def]
  have "real (card F) = (real (k - 1)) ^ (m - l) * prod (\<lambda> i. real (k - 1 - i)) {0..<l}" 
    by simp
  also have "\<dots> > (real (k - 1)) ^ m / 3" 
    by (rule approximation1)
  finally have cardF: "card F > (k - 1) ^ m / 3" by simp
  with approx show ?thesis by simp
qed

text \<open>Theorem 13\<close>
                                
lemma theorem_13: assumes phi: "\<phi> \<in> tf_mformula" "\<phi> \<in> \<A>" 
  and sub: "POS \<subseteq> ACC_mf \<phi>" "ACC_cf_mf \<phi> = {}" 
shows "cs \<phi> > k powr (4 / 7 * sqrt k)" 
proof -
  let ?r = "real :: nat \<Rightarrow> real" 
  have "cs \<phi> > ((m - l) / k)^l / (6 * L^2)" 
  proof (cases "POS \<inter> ACC (APR \<phi>) = {}")
    case empty: True
    have "\<partial>Pos \<phi> = POS \<inter> ACC_mf \<phi> - ACC (APR \<phi>)" unfolding deviate_pos_def by auto
    also have "\<dots> = POS - ACC (APR \<phi>)" using sub by blast
    also have "\<dots> = POS" using empty by auto
    finally have id: "\<partial>Pos \<phi> = POS" by simp 
    have "m choose k = card POS" by (simp add: card_POS)
    also have "\<dots> = card (\<partial>Pos \<phi>)" unfolding id by simp
    also have "\<dots> \<le> cs \<phi> * L\<^sup>2 * (m - l - 1 choose (k - l - 1))" using card_deviate_Pos[OF phi] by auto
    finally have "m choose k \<le> cs \<phi> * L\<^sup>2 * (m - l - 1 choose (k - l - 1))" 
      by simp
    from approximation2[OF this]
    show "((m - l) / k)^l / (6 * L^2) < cs \<phi>" by simp
  next
    case False    
    have "POS \<inter> ACC (APR \<phi>) \<noteq> {}" by fact
    hence nempty: "APR \<phi> \<noteq> {}" by auto
    have "card (\<partial>Neg \<phi>) = card (ACC_cf (APR \<phi>) - ACC_cf_mf \<phi>)" unfolding deviate_neg_def by auto
    also have "\<dots> = card (ACC_cf (APR \<phi>))" using sub by auto
    also have "\<dots> > (k - 1)^m / 3" using ACC_cf_non_empty_approx[OF phi nempty] . 
    finally have "(k - 1)^m / 3 < card (\<partial>Neg \<phi>)" .
    also have "\<dots> \<le> cs \<phi> * L\<^sup>2 * (k - 1) ^ m / 2 ^ (p - 1)" 
      using card_deviate_Neg[OF phi] sub by auto
    finally have "(k - 1)^m / 3 < (cs \<phi> * (L\<^sup>2 * (k - 1) ^ m)) / 2 ^ (p - 1)" by simp
    from approximation3[OF this] show ?thesis .
  qed
  hence part1: "cs \<phi> > ((m - l) / k)^l / (6 * L^2)" .
  from approximation4[OF this] show ?thesis using k2 by simp
qed

text \<open>Definition 14\<close>

definition eval_g :: "'a VAS \<Rightarrow> graph \<Rightarrow> bool" where
  "eval_g \<theta> G = (\<forall> v \<in> \<V>. (\<pi> v \<in> G \<longrightarrow> \<theta> v))" 

definition eval_gs :: "'a VAS \<Rightarrow> graph set \<Rightarrow> bool" where
  "eval_gs \<theta> X = (\<exists> G \<in> X. eval_g \<theta> G)" 


lemmas eval_simps = eval_g_def eval_gs_def eval.simps

lemma eval_gs_union: 
  "eval_gs \<theta> (X \<union> Y) = (eval_gs \<theta> X \<or> eval_gs \<theta> Y)" 
  by (auto simp: eval_gs_def)

lemma eval_gs_odot: assumes "X \<subseteq> \<G>" "Y \<subseteq> \<G>"  
  shows "eval_gs \<theta> (X \<odot> Y) = (eval_gs \<theta> X \<and> eval_gs \<theta> Y)" 
proof
  assume "eval_gs \<theta> (X \<odot> Y)" 
  from this[unfolded eval_gs_def] obtain DE where DE: "DE \<in> X \<odot> Y"  
    and eval: "eval_g \<theta> DE" by auto
  from DE[unfolded odot_def] obtain D E where id: "DE = D \<union> E" and DE: "D \<in> X" "E \<in> Y" 
    by auto
  from eval have "eval_g \<theta> D" "eval_g \<theta> E" unfolding id eval_g_def
    by auto
  with DE show "eval_gs \<theta> X \<and> eval_gs \<theta> Y" unfolding eval_gs_def by auto
next
  assume "eval_gs \<theta> X \<and> eval_gs \<theta> Y" 
  then obtain D E where DE: "D \<in> X" "E \<in> Y" and eval: "eval_g \<theta> D" "eval_g \<theta> E" 
    unfolding eval_gs_def by auto
  from DE assms have D: "D \<in> \<G>" "E \<in> \<G>" by auto  
  let ?U = "D \<union> E" 
  from eval have eval: "eval_g \<theta> ?U" 
    unfolding eval_g_def by auto
  from DE have 1: "?U \<in> X \<odot> Y" unfolding odot_def by auto
  with 1 eval show "eval_gs \<theta> (X \<odot> Y)" unfolding eval_gs_def by auto
qed 


text \<open>Lemma 15\<close>

lemma eval_set: assumes phi: "\<phi> \<in> tf_mformula" "\<phi> \<in> \<A>"  
  shows "eval \<theta> \<phi> = eval_gs \<theta> (SET \<phi>)" 
  using phi
proof (induct \<phi> rule: tf_mformula.induct)
  case tf_False
  then show ?case unfolding eval_simps by simp
next
  case (tf_Var x)
  then show ?case using inj_on_\<pi> unfolding eval_simps 
    by (auto simp add: inj_on_def)
next
  case (tf_Disj \<phi>1 \<phi>2)
  thus ?case by (auto simp: eval_gs_union)
next
  case (tf_Conj \<phi>1 \<phi>2)
  thus ?case by (simp, intro eval_gs_odot[symmetric]; intro SET_\<G>, auto)
qed

definition \<theta>\<^sub>g :: "graph \<Rightarrow> 'a VAS" where
  "\<theta>\<^sub>g G x = (x \<in> \<V> \<and> \<pi> x \<in> G)" 

text \<open>From here on we deviate from Gordeev's paper as we do not use positive bases, but a more
  direct approach.\<close>

lemma eval_ACC: assumes phi: "\<phi> \<in> tf_mformula"  "\<phi> \<in> \<A>" 
  and G: "G \<in> \<G>" 
shows "eval (\<theta>\<^sub>g G) \<phi> = (G \<in> ACC_mf \<phi>)"  
  using phi unfolding ACC_mf_def
proof (induct \<phi> rule: tf_mformula.induct)
  case (tf_Var x)
  thus ?case by (auto simp: ACC_def G accepts_def \<theta>\<^sub>g_def)
next
  case (tf_Disj phi psi)
  thus ?case by (auto simp: ACC_union)
next
  case (tf_Conj phi psi)
  thus ?case by (auto simp: ACC_odot)
qed simp

lemma CLIQUE_solution_imp_POS_sub_ACC: assumes solution: "\<forall> G \<in> \<G>. G \<in> CLIQUE \<longleftrightarrow> eval (\<theta>\<^sub>g G) \<phi>" 
    and tf: "\<phi> \<in> tf_mformula"
    and phi: "\<phi> \<in> \<A>" 
  shows "POS \<subseteq> ACC_mf \<phi>" 
proof 
  fix G
  assume POS: "G \<in> POS" 
  with POS_\<G> have G: "G \<in> \<G>" by auto
  with POS solution POS_CLIQUE 
  have "eval (\<theta>\<^sub>g G) \<phi>" by auto
  thus "G \<in> ACC_mf \<phi>" unfolding eval_ACC[OF tf phi G] .
qed

lemma CLIQUE_solution_imp_ACC_cf_empty: assumes solution: "\<forall> G \<in> \<G>. G \<in> CLIQUE \<longleftrightarrow> eval (\<theta>\<^sub>g G) \<phi>" 
    and tf: "\<phi> \<in> tf_mformula"
    and phi: "\<phi> \<in> \<A>" 
  shows "ACC_cf_mf \<phi> = {}" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  from this[unfolded ACC_cf_mf_def ACC_cf_def]
  obtain F where F: "F \<in> \<F>" "SET \<phi> \<tturnstile> C F" by auto
  define G where "G = C F" 
  have NEG: "G \<in> NEG" unfolding NEG_def G_def using F by auto
  hence "G \<notin> CLIQUE" using CLIQUE_NEG by auto
  have GG: "G \<in> \<G>" unfolding G_def using F
    using G_def NEG NEG_\<G> by blast
  have GAcc: "SET \<phi> \<tturnstile> G" using F[folded G_def] by auto  
  then obtain D :: graph where 
    D: "D \<in> SET \<phi>" and sub: "D \<subseteq> G"
    unfolding accepts_def by blast  
  from SET_\<G>[OF tf phi] D 
  have DG: "D \<in> \<G>" by auto
  have eval: "eval (\<theta>\<^sub>g D) \<phi>" unfolding eval_set[OF tf phi] eval_gs_def
    by (intro bexI[OF _ D], unfold eval_g_def, insert DG, auto simp: \<theta>\<^sub>g_def) 
  hence "D \<in> CLIQUE" using solution[rule_format, OF DG] by auto
  hence "G \<in> CLIQUE" using GG sub unfolding CLIQUE_def by blast
  with \<open>G \<notin> CLIQUE\<close> show False by auto
qed

subsection \<open>Conclusion\<close>

text \<open>Theorem 22\<close>

text \<open>We first consider monotone formulas without TRUE.\<close>

theorem Clique_not_solvable_by_small_tf_mformula: assumes solution: "\<forall> G \<in> \<G>. G \<in> CLIQUE \<longleftrightarrow> eval (\<theta>\<^sub>g G) \<phi>" 
  and tf: "\<phi> \<in> tf_mformula"
  and phi: "\<phi> \<in> \<A>" 
shows "cs \<phi> > k powr (4 / 7 * sqrt k)"
proof -
  from CLIQUE_solution_imp_POS_sub_ACC[OF solution tf phi] have POS: "POS \<subseteq> ACC_mf \<phi>" .
  from CLIQUE_solution_imp_ACC_cf_empty[OF solution tf phi] have CF: "ACC_cf_mf \<phi> = {}" .
  from theorem_13[OF tf phi POS CF]
  show ?thesis by auto 
qed

text \<open>Next we consider general monotone formulas.\<close>

theorem Clique_not_solvable_by_poly_mono: assumes solution: "\<forall> G \<in> \<G>. G \<in> CLIQUE \<longleftrightarrow> eval (\<theta>\<^sub>g G) \<phi>" 
  and phi: "\<phi> \<in> \<A>" 
shows "cs \<phi> > k powr (4 / 7 * sqrt k)"
proof -
  note vars = phi[unfolded \<A>_def]
  have CL: "CLIQUE = Clique [k^4] k" "\<G> = Graphs [k^4]" 
    unfolding CLIQUE_def \<K>_altdef m_def Clique_def by auto
  with empty_CLIQUE have "{} \<notin> Clique [k^4] k" by simp
  with solution[rule_format, of "{}"] 
  have "\<not> eval (\<theta>\<^sub>g {}) \<phi>" by (auto simp: Graphs_def)
  from to_tf_mformula[OF this]
  obtain \<psi> where *: "\<psi> \<in> tf_mformula" 
    "(\<forall>\<theta>. eval \<theta> \<phi> = eval \<theta> \<psi>)" "vars \<psi> \<subseteq> vars \<phi>" "cs \<psi> \<le> cs \<phi>" by auto
  with phi solution have psi: "\<psi> \<in> \<A>" 
    and solution: "\<forall>G\<in>\<G>. (G \<in> CLIQUE) = eval (\<theta>\<^sub>g G) \<psi>" unfolding \<A>_def by auto
  from Clique_not_solvable_by_small_tf_mformula[OF solution *(1) psi]
  show ?thesis using *(4) by auto
qed

text \<open>We next expand all abbreviations and definitions of the locale, but stay within the locale\<close>

theorem Clique_not_solvable_by_small_monotone_circuit_in_locale: assumes phi_solves_clique: 
  "\<forall> G \<in> Graphs [k^4]. G \<in> Clique [k^4] k \<longleftrightarrow> eval (\<lambda> x. \<pi> x \<in> G) \<phi>" 
  and vars: "vars \<phi> \<subseteq> \<V>" 
shows "cs \<phi> > k powr (4 / 7 * sqrt k)"
proof - 
  {
    fix G
    assume G: "G \<in> \<G>" 
    have "eval (\<lambda> x. \<pi> x \<in> G) \<phi> = eval (\<theta>\<^sub>g G) \<phi>" using vars
      by (intro eval_vars, auto simp: \<theta>\<^sub>g_def)
  }
  have CL: "CLIQUE = Clique [k^4] k" "\<G> = Graphs [k^4]" 
    unfolding CLIQUE_def \<K>_altdef m_def Clique_def by auto
  {
    fix G
    assume G: "G \<in> \<G>" 
    have "eval (\<lambda> x. \<pi> x \<in> G) \<phi> = eval (\<theta>\<^sub>g G) \<phi>" using vars
      by (intro eval_vars, auto simp: \<theta>\<^sub>g_def)
  }
  with phi_solves_clique  CL have solves: "\<forall> G \<in> \<G>. G \<in> CLIQUE \<longleftrightarrow> eval (\<theta>\<^sub>g G) \<phi>"
    by auto
  from vars have inA: "\<phi> \<in> \<A>" by (auto simp: \<A>_def)
  from Clique_not_solvable_by_poly_mono[OF solves inA] 
  show ?thesis by auto
qed
end


text \<open>Let us now move the theorem outside the locale\<close>

definition Large_Number where "Large_Number = Max {64, L0''^2, L0^2, L0'^2, M0, M0'}" 

theorem Clique_not_solvable_by_small_monotone_circuit_squared: 
  fixes \<phi> :: "'a mformula" 
  assumes k: "\<exists> l. k = l^2" 
  and LARGE: "k \<ge> Large_Number" 
  and \<pi>: "bij_betw \<pi> V [k^4]^\<two>" 
  and solution: "\<forall>G\<in>Graphs [k ^ 4]. (G \<in> Clique [k ^ 4] k) = eval (\<lambda> x. \<pi> x \<in> G) \<phi>" 
  and vars: "vars \<phi> \<subseteq> V" 
  shows "cs \<phi> > k powr (4 / 7 * sqrt k)" 
proof -
  from k obtain l where kk: "k = l^2" by auto
  note LARGE = LARGE[unfolded Large_Number_def]
  have k8: "k \<ge> 8^2" using LARGE by auto
  from this[unfolded kk power2_nat_le_eq_le] 
  have l8: "l \<ge> 8" .  
  define p where "p = nat (ceiling (l * log 2 (k^4)))"  
  have tedious: "l * log 2 (k ^ 4) \<ge> 0" using l8 k8 by auto
  have "int p = ceiling (l * log 2 (k ^ 4))" unfolding p_def
    by (rule nat_0_le, insert tedious, auto)
  from arg_cong[OF this, of real_of_int]
  have rp: "real p = ceiling (l * log 2 (k ^ 4))" by simp  
  have one: "real l * log 2 (k ^ 4) \<le> p" unfolding rp by simp
  have two: "p \<le> real l * log 2 (k ^ 4) + 1" unfolding rp by simp
  have "real l < real l + 1 " by simp
  also have "\<dots> \<le> real l + real l" using l8 by simp
  also have "\<dots> = real l * 2" by simp
  also have "\<dots> = real l * log 2 (2^2)" 
    by (subst log_pow_cancel, auto)
  also have "\<dots> \<le> real l * log 2 (k ^ 4)" 
  proof (intro mult_left_mono, subst log_le_cancel_iff)
    have "(4 :: real) \<le> 2^4" by simp
    also have "\<dots> \<le> real k^4" 
      by (rule power_mono, insert k8, auto)
    finally show "2\<^sup>2 \<le> real (k ^ 4)" by simp
  qed (insert k8, auto)
  also have "\<dots> \<le> p" by fact
  finally have lp: "l < p" by auto  
  interpret second_assumptions l p k
  proof (unfold_locales)
    show "2 < l" using l8 by auto
    show "8 \<le> l" by fact
    show "k = l^2" by fact
    show "l < p" by fact
    from LARGE have "L0''^2 \<le> k" by auto
    from this[unfolded kk power2_nat_le_eq_le] 
    have L0''l: "L0'' \<le> l" .
    have "p \<le> real l * log 2 (k ^ 4) + 1" by fact
    also have "\<dots> < k" unfolding kk 
      by (intro L0'' L0''l)
    finally show "p < k" by simp
  qed    
  interpret third_assumptions l p k  
  proof 
    show "real l * log 2 (real m) \<le> p" using one unfolding m_def .
    show "p \<le> real l * log 2 (real m) + 1" using two unfolding m_def .
    from LARGE have "L0^2 \<le> k" by auto
    from this[unfolded kk power2_nat_le_eq_le] 
    show "L0 \<le> l" .
    from LARGE have "L0'^2 \<le> k" by auto
    from this[unfolded kk power2_nat_le_eq_le] 
    show "L0' \<le> l" .
    show "M0' \<le> m" using km LARGE by simp
    show "M0 \<le> m" using km LARGE by simp
  qed
  interpret forth_assumptions l p k V \<pi> 
    by (standard, insert \<pi> m_def, auto simp: bij_betw_same_card[OF \<pi>])
  from Clique_not_solvable_by_small_monotone_circuit_in_locale[OF solution vars] 
  show ?thesis .
qed

text \<open>A variant where we get rid of the @{term "k = l^2"}-assumption by just taking squares everywhere.\<close>

theorem Clique_not_solvable_by_small_monotone_circuit: 
  fixes \<phi> :: "'a mformula" 
  assumes LARGE: "k \<ge> Large_Number" 
  and \<pi>: "bij_betw \<pi> V [k^8]^\<two>" 
  and solution: "\<forall>G\<in>Graphs [k ^ 8]. (G \<in> Clique [k ^ 8] (k^2)) = eval (\<lambda> x. \<pi> x \<in> G) \<phi>" 
  and vars: "vars \<phi> \<subseteq> V" 
shows "cs \<phi> > k powr (8 / 7 * k)" 
proof -
  from LARGE have LARGE: "Large_Number \<le> k\<^sup>2" 
    by (simp add: power2_nat_le_imp_le)
  have id: "k\<^sup>2 ^ 4 = k^8" "sqrt (k^2) = k" by auto
  from Clique_not_solvable_by_small_monotone_circuit_squared[of "k^2", unfolded id, OF _ LARGE \<pi> solution vars]
  have "cs \<phi> > (k^2) powr (4 / 7 * k)" by auto
  also have "(k^2) powr (4 / 7 * k) = k powr (8 / 7 * k)"
    unfolding of_nat_power using powr_powr[of "real k" 2] by simp
  finally show ?thesis .
qed

definition large_number where "large_number = Large_Number^8" 

text \<open>Finally a variant, where the size is formulated depending on $n$, the number of vertices.\<close>

theorem Clique_with_n_nodes_not_solvable_by_small_monotone_circuit:
  fixes \<phi> :: "'a mformula" 
  assumes large: "n \<ge> large_number" 
  and kn: "\<exists> k. n = k^8" 
  and \<pi>: "bij_betw \<pi> V [n]^\<two>" 
  and s: "s = root 4 n" 
  and solution: "\<forall>G\<in>Graphs [n]. (G \<in> Clique [n] s) = eval (\<lambda> x. \<pi> x \<in> G) \<phi>" 
  and vars: "vars \<phi> \<subseteq> V" 
shows "cs \<phi> > (root 7 n) powr (root 8 n)" 
proof -
  from kn obtain k where nk: "n = k^8" by auto
  have kn: "k = root 8 n" unfolding nk of_nat_power
    by (subst real_root_pos2, auto)
  have "root 4 n = root 4 ((real (k^2))^4)" unfolding nk by simp
  also have "\<dots> = k^2" by (simp add: real_root_pos_unique)
  finally have r4: "root 4 n = k^2" by simp
  have s: "s = k^2" using s unfolding r4 by simp
  from large[unfolded nk large_number_def] have Large: "k \<ge> Large_Number" by simp
  have "0 < Large_Number" unfolding Large_Number_def by simp
  with Large have k0: "k > 0" by auto
  hence n0: "n > 0" using nk by simp
  from Clique_not_solvable_by_small_monotone_circuit[OF Large \<pi>[unfolded nk] _ vars]
    solution[unfolded s] nk
  have "real k powr (8 / 7 * real k) < cs \<phi>" by auto
  also have "real k powr (8 / 7 * real k) = root 8 n powr (8 / 7 * root 8 n)" 
    unfolding kn by simp
  also have "\<dots> = ((root 8 n) powr (8 / 7)) powr (root 8 n)" 
    unfolding powr_powr by simp
  also have "(root 8 n) powr (8 / 7) = root 7 n" using n0
    by (simp add: root_powr_inverse powr_powr)
  finally show ?thesis .
qed

end
