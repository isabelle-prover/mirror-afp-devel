section \<open>Generic laws about complements\<close>

theory Laws_Complement
  imports Laws Axioms_Complement
begin

unbundle register_syntax
notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

definition \<open>complements F G \<longleftrightarrow> compatible F G \<and> iso_register (F;G)\<close>

lemma complementsI: \<open>compatible F G \<Longrightarrow> iso_register (F;G) \<Longrightarrow> complements F G\<close>
  using complements_def by blast

lemma complement_exists: 
  fixes F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>
  assumes \<open>register F\<close>
  shows \<open>let 'c::domain = cdc F in
          \<exists>G :: 'c update \<Rightarrow> 'b update. complements F G\<close>
  by (simp add: assms complement_exists complements_def)

lemma complements_sym: \<open>complements G F\<close> if \<open>complements F G\<close>
proof (rule complementsI)
  show [simp]: \<open>compatible G F\<close>
    using compatible_sym complements_def that by blast
  from that have \<open>iso_register (F;G)\<close>
    by (meson complements_def)
  then obtain I where [simp]: \<open>register I\<close> and \<open>(F;G) o I = id\<close> and \<open>I o (F;G) = id\<close>
    using iso_register_def by blast
  have \<open>register (swap o I)\<close>
    using \<open>register I\<close> register_comp register_swap by blast
  moreover have \<open>(G;F) o (swap o I) = id\<close>
    by (simp add: \<open>(F;G) \<circ> I = id\<close> rewriteL_comp_comp)
  moreover have \<open>(swap o I) o (G;F) = id\<close>
    by (metis (no_types, opaque_lifting) swap_swap \<open>I \<circ> (F;G) = id\<close> calculation(2) comp_def eq_id_iff)
  ultimately show \<open>iso_register (G;F)\<close>
    using \<open>compatible G F\<close> iso_register_def pair_is_register by blast
qed

definition complement :: \<open>('a::domain update \<Rightarrow> 'b::domain_with_simple_complement update) \<Rightarrow> (('a,'b) complement_domain_simple update \<Rightarrow> 'b update)\<close> where
  \<open>complement F = (SOME G :: ('a, 'b) complement_domain_simple update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G))\<close>

lemma register_complement[simp]: \<open>register (complement F)\<close> if \<open>register F\<close>
  using complement_exists_simple[OF that]
  by (metis (no_types, lifting) compatible_def complement_def some_eq_imp)

lemma complement_is_complement[simp]:
  assumes \<open>register F\<close>
  shows \<open>complements F (complement F)\<close>
  using complement_exists_simple[OF assms] unfolding complements_def
  by (metis (mono_tags, lifting) complement_def some_eq_imp)

lemma complement_unique:
  assumes \<open>complements F G\<close>
  assumes \<open>complements F G'\<close>
  shows \<open>equivalent_registers G G'\<close>
  apply (rule complement_unique[where F=F])
  using assms unfolding complements_def by auto

lemma complement_unique':
  assumes \<open>complements F G\<close>
  shows \<open>equivalent_registers G (complement F)\<close>
  apply (rule complement_unique[where F=F])
  using assms unfolding complements_def using compatible_register1 complement_is_complement complements_def by blast+

lemma compatible_complement[simp]: \<open>register F \<Longrightarrow> compatible F (complement F)\<close>
  using complement_is_complement complements_def by blast

lemma complements_register_tensor:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  shows \<open>complements (F \<otimes>\<^sub>r G) (complement F \<otimes>\<^sub>r complement G)\<close>
proof (rule complementsI)
  have [iff]: \<open>iso_register (F;complement F)\<close>   \<open>iso_register (G;complement G)\<close>
    using complements_def by fastforce+

  have sep4: \<open>separating TYPE('z::domain) {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u (c \<otimes>\<^sub>u d) |a b c d. True}\<close>
    apply (rule separating_tensor'[where A=\<open>{(a \<otimes>\<^sub>u b) |a b. True}\<close> and B=\<open>{(c \<otimes>\<^sub>u d) |c d. True}\<close>])
      apply (rule separating_tensor'[where A=UNIV and B=UNIV]) apply auto[3]
     apply (rule separating_tensor'[where A=UNIV and B=UNIV]) apply auto[3]
    by auto
  show compat: \<open>compatible (F \<otimes>\<^sub>r G) (complement F \<otimes>\<^sub>r complement G)\<close>
    by (metis assms(1) assms(2) compatible_register_tensor complement_is_complement complements_def)
  let ?reorder = \<open>((Fst o Fst; Snd o Fst); (Fst o Snd; Snd o Snd))\<close>
  have [simp]: \<open>register ?reorder\<close>
    by auto
  have [simp]: \<open>?reorder ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u (c \<otimes>\<^sub>u d)) = ((a \<otimes>\<^sub>u c) \<otimes>\<^sub>u (b \<otimes>\<^sub>u d))\<close> 
    for a::\<open>'t::domain update\<close> and b::\<open>'u::domain update\<close> and c::\<open>'v::domain update\<close> and d::\<open>'w::domain update\<close>
    by (simp add: register_pair_apply Fst_def Snd_def tensor_update_mult)
  have [simp]: \<open>iso_register ?reorder\<close>
    apply (rule iso_registerI[of _ ?reorder]) apply auto[2]
     apply (rule register_eqI[OF sep4]) apply auto[3]
    apply (rule register_eqI[OF sep4]) by auto
  have \<open>(F \<otimes>\<^sub>r G; complement F \<otimes>\<^sub>r complement G) = ((F; complement F) \<otimes>\<^sub>r (G; complement G)) o ?reorder\<close>
    apply (rule register_eqI[OF sep4])
    by (auto intro!: register_preregister register_comp register_tensor_is_register pair_is_register
        simp: compat register_pair_apply tensor_update_mult)
  moreover have \<open>iso_register \<dots>\<close>
    using assms complement_is_complement complements_def 
    by (auto intro!: iso_register_comp iso_register_tensor_is_iso_register)
  ultimately show \<open>iso_register (F \<otimes>\<^sub>r G;complement F \<otimes>\<^sub>r complement G)\<close>
    by simp
qed

definition is_unit_register where
  \<open>is_unit_register U \<longleftrightarrow> complements U id\<close>

lemma register_unit_register[simp]: \<open>is_unit_register U \<Longrightarrow> register U\<close>
  by (simp add: compatible_def complements_def is_unit_register_def)

lemma unit_register_compatible[simp]: \<open>compatible U X\<close> if \<open>is_unit_register U\<close> \<open>register X\<close>
  by (metis compatible_comp_right complements_def id_comp is_unit_register_def that(1) that(2))

lemma unit_register_compatible'[simp]: \<open>compatible X U\<close> if \<open>is_unit_register U\<close> \<open>register X\<close>
  using compatible_sym that(1) that(2) unit_register_compatible by blast

lemma compatible_complement_left[simp]: \<open>register X \<Longrightarrow> compatible (complement X) X\<close>
  using compatible_sym complement_is_complement complements_def by blast

lemma compatible_complement_right[simp]: \<open>register X \<Longrightarrow> compatible X (complement X)\<close>
  using complement_is_complement complements_def by blast

lemma unit_register_pair[simp]: \<open>equivalent_registers X (U; X)\<close> if [simp]: \<open>is_unit_register U\<close> \<open>register X\<close>
proof -
  from complement_exists[OF \<open>register X\<close>]
  have \<open>let 'x::domain = cdc X in equivalent_registers X (U; X)\<close>
  proof with_type_mp
    note [[simproc del: compatibility_warn]]
    (* assume \<open>\<exists>G :: 'x update \<Rightarrow> 'b update. complements X G\<close> *)
    with_type_case
    then obtain compX :: \<open>'x update \<Rightarrow> 'b update\<close> where compX: \<open>complements X compX\<close>
      by blast
    then have [simp]: \<open>register compX\<close> \<open>compatible X compX\<close>
      by (auto simp add: compatible_def complements_def)
    have [iff]: \<open>iso_register (X;compX)\<close>
      using compX complements_def by blast

    have \<open>equivalent_registers id (U; id)\<close>
      using complements_def is_unit_register_def iso_register_equivalent_id that(1) by blast
    also have \<open>equivalent_registers \<dots> (U; (X; compX))\<close>
      apply (rule equivalent_registers_pair_right)
      by (auto intro!: unit_register_compatible)
    also have \<open>equivalent_registers \<dots> ((U; X); compX)\<close>
      apply (rule equivalent_registers_assoc)
      by auto
    finally have \<open>complements (U; X) compX\<close>
      by (auto simp: equivalent_registers_def complements_def)
    moreover have \<open>equivalent_registers (X; compX) id\<close>
      using compX complements_def equivalent_registers_sym iso_register_equivalent_id by blast
    ultimately show \<open>equivalent_registers X (U; X)\<close>
      by (meson complement_unique compX complements_sym)
  qed
  from this[cancel_with_type]
  show \<open>equivalent_registers X (U; X)\<close>
    by -
qed


lemma unit_register_compose_left:
  assumes [simp]: \<open>is_unit_register U\<close>
  assumes [simp]: \<open>register A\<close>
  shows \<open>is_unit_register (A o U)\<close>
proof -
  from complement_exists[OF \<open>register A\<close>]
  have \<open>let 'x::domain = cdc A in is_unit_register (A o U)\<close>
  proof with_type_mp
    note [[simproc del: compatibility_warn]]
    with_type_case 
    then obtain compA :: \<open>'x update \<Rightarrow> 'c update\<close> where compX: \<open>complements A compA\<close>
      by blast
    then have [simp]: \<open>register compA\<close> \<open>compatible A compA\<close>
      by (auto simp add: compatible_def complements_def)
    have [iff]: \<open>iso_register (A;compA)\<close>
      using compX complements_def by blast

    have \<open>compatible (A \<circ> U) A\<close>
      by (metis assms(1) assms(2) comp_id compatible_comp_inner complements_def is_unit_register_def)
    then have compat'[simp]: \<open>compatible (A o U) (A; compA)\<close>
      by (auto intro!: compatible3')
    moreover have \<open>equivalent_registers (A; compA) id\<close>
      using compX complements_def equivalent_registers_sym iso_register_equivalent_id by blast
    ultimately have compat[simp]: \<open>compatible (A o U) id\<close>
      using equivalent_registers_compatible2 by blast

    have aux: \<open>equivalent_registers (U;id) id\<close>
      using assms(1) equivalent_registers_sym register_id unit_register_pair by blast

    have \<open>equivalent_registers (A o U; id) (A o U; (A; compA))\<close>
      by (auto intro!: equivalent_registers_pair_right)
    also have \<open>equivalent_registers \<dots> (A o U; (A o id; compA))\<close>
      by (auto intro!: equivalent_registers_refl pair_is_register)
    also have \<open>equivalent_registers \<dots> ((A o U; A o id); compA)\<close>
      apply (intro equivalent_registers_assoc compatible_comp_inner)
      by auto
    also have \<open>equivalent_registers \<dots> (A o (U; id); compA)\<close>
      by (metis (no_types, opaque_lifting) assms(1) assms(2) calculation complements_def equivalent_registers_sym equivalent_registers_trans is_unit_register_def register_comp_pair)
    also have \<open>equivalent_registers \<dots> (A o id; compA)\<close>
      apply (intro equivalent_registers_pair_left equivalent_registers_comp)
      using aux by (auto simp: assms)
    also have \<open>equivalent_registers \<dots> id\<close>
      by (simp add: \<open>equivalent_registers (A;compA) id\<close>)
    finally show \<open>is_unit_register (A o U)\<close>
      using compat complementsI equivalent_registers_sym is_unit_register_def iso_register_equivalent_id by blast
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma unit_register_compose_right:
  assumes [simp]: \<open>is_unit_register U\<close>
  assumes [simp]: \<open>iso_register A\<close>
  shows \<open>is_unit_register (U o A)\<close>
proof (unfold is_unit_register_def, rule complementsI)
  show \<open>compatible (U \<circ> A) id\<close>
    by (simp add: iso_register_is_register)
  have 1: \<open>iso_register ((U;id) \<circ> A \<otimes>\<^sub>r id)\<close>
    by (meson assms(1) assms(2) complements_def is_unit_register_def iso_register_comp iso_register_id iso_register_tensor_is_iso_register)
  have 2: \<open>id \<circ> ((U;id) \<circ> A \<otimes>\<^sub>r id) = (U \<circ> A;id)\<close>
    by (metis assms(1) assms(2) complements_def fun.map_id is_unit_register_def iso_register_id iso_register_is_register pair_o_tensor)
  show \<open>iso_register (U \<circ> A;id)\<close>
    using 1 2 by auto
qed

lemma unit_register_unique:
  assumes \<open>is_unit_register F\<close>
  assumes \<open>is_unit_register G\<close>
  shows \<open>equivalent_registers F G\<close>
proof -
  have \<open>complements F id\<close> \<open>complements G id\<close>
    using assms by (metis complements_def equivalent_registers_def id_comp is_unit_register_def)+
  then show ?thesis
    by (meson complement_unique complements_sym equivalent_registers_sym equivalent_registers_trans)
qed

lemma unit_register_domains_isomorphic:
  fixes F :: \<open>'a::domain update \<Rightarrow> 'c::domain update\<close>
  fixes G :: \<open>'b::domain update \<Rightarrow> 'd::domain update\<close>
  assumes \<open>is_unit_register F\<close>
  assumes \<open>is_unit_register G\<close>
  shows \<open>\<exists>I :: 'a update \<Rightarrow> 'b update. iso_register I\<close>
proof -
  have \<open>is_unit_register ((\<lambda>d. tensor_update id_update d) o G)\<close>
    by (simp add: assms(2) unit_register_compose_left)
  moreover have \<open>is_unit_register ((\<lambda>c. tensor_update c id_update) o F)\<close>
    using assms(1) register_tensor_left unit_register_compose_left by blast
  ultimately have \<open>equivalent_registers ((\<lambda>d. tensor_update id_update d) o G) ((\<lambda>c. tensor_update c id_update) o F)\<close>
    using unit_register_unique by blast
  then show ?thesis
    unfolding equivalent_registers_def by auto
qed


lemma id_complement_is_unit_register[simp]: \<open>is_unit_register (complement id)\<close>
  by (metis is_unit_register_def complement_is_complement complements_def complements_sym equivalent_registers_def id_comp register_id)

type_synonym unit_register_domain = \<open>(some_domain, some_domain) complement_domain_simple\<close>
definition unit_register :: \<open>unit_register_domain update \<Rightarrow> 'a::domain update\<close> where \<open>unit_register = (SOME U. is_unit_register U)\<close>

lemma unit_register_is_unit_register[simp]: \<open>is_unit_register (unit_register :: unit_register_domain update \<Rightarrow> 'a::domain update)\<close>
proof -
  note [[simproc del: compatibility_warn]]
  let ?U = \<open>unit_register :: unit_register_domain update \<Rightarrow> 'a::domain update\<close>
  let ?U1 = \<open>complement id :: unit_register_domain update \<Rightarrow> some_domain update\<close>
  from complement_exists[OF register_id[where 'a='a]]
  have \<open>let 'x::domain = cdc (id::'a update \<Rightarrow> _) in is_unit_register ?U\<close>
  proof with_type_mp
    with_type_case
    then obtain U2 :: \<open>'x update \<Rightarrow> 'a update\<close> where comp1: \<open>complements id U2\<close>
      by blast
    then have [simp]: \<open>register U2\<close> \<open>compatible id U2\<close> \<open>compatible id U2\<close>
      by (auto simp add: compatible_def complements_def)

    have \<open>is_unit_register ?U1\<close> \<open>is_unit_register U2\<close>
       by (auto simp: comp1 complements_sym is_unit_register_def)

    then obtain I :: \<open>unit_register_domain update \<Rightarrow> 'x update\<close> where \<open>iso_register I\<close>
      apply atomize_elim by (rule unit_register_domains_isomorphic)
    with \<open>is_unit_register U2\<close> have \<open>is_unit_register (U2 o I)\<close>
      by (rule unit_register_compose_right)
    then show \<open>is_unit_register ?U\<close>
      by (metis someI_ex unit_register_def)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma unit_register_domain_tensor_unit:
  fixes U :: \<open>'a::domain update \<Rightarrow> _\<close>
  assumes \<open>is_unit_register U\<close>
  shows \<open>\<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_register I\<close>
  (* Can we show that I = (\<lambda>x. tensor_update id_update x) ? It would be nice but I do not see how to prove it. *)
proof -
  from complement_exists[OF register_id[where 'a='b]]
  have \<open>let 'x::domain = cdc (id :: 'b update \<Rightarrow> _) in
        \<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_register I\<close>
  proof with_type_mp
    note [[simproc del: compatibility_warn]]
    with_type_case
    assume \<open>\<exists>G :: 'x update \<Rightarrow> 'b update. complements id G\<close>
    then obtain U' :: \<open>'x update \<Rightarrow> 'b update\<close> where comp: \<open>complements id U'\<close>
      by blast
    then have [simp]: \<open>register U'\<close> \<open>compatible id U'\<close> \<open>compatible U' id\<close>
      by (auto simp add: compatible_def complements_def)
    have \<open>is_unit_register U'\<close>
      by (simp add: comp complements_sym is_unit_register_def)

    have \<open>equivalent_registers (id :: 'b update \<Rightarrow> _) (U'; id)\<close>
      using comp complements_def complements_sym iso_register_equivalent_id by blast
    then obtain J :: \<open>'b update \<Rightarrow> (('x * 'b) update)\<close> where \<open>iso_register J\<close>
      using equivalent_registers_def iso_register_inv by blast
    moreover obtain K :: \<open>'x update \<Rightarrow> 'a update\<close> where \<open>iso_register K\<close>
      apply atomize_elim 
      using \<open>is_unit_register U'\<close> assms
      by (rule unit_register_domains_isomorphic)
    ultimately have \<open>iso_register ((K \<otimes>\<^sub>r id) o J)\<close>
      by auto
    then show \<open>\<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_register I\<close>
      by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by-
qed

lemma compatible_complement_pair1:
  assumes \<open>compatible F G\<close>
  shows \<open>compatible F (complement (F;G))\<close>
  by (metis assms compatible_comp_left compatible_complement_right pair_is_register register_Fst register_pair_Fst)

lemma compatible_complement_pair2:
  assumes [simp]: \<open>compatible F G\<close>
  shows \<open>compatible G (complement (F;G))\<close>
proof -
  have \<open>compatible (F;G) (complement (F;G))\<close>
    by simp
  then have \<open>compatible ((F;G) o Snd) (complement (F;G))\<close>
    by auto
  then show ?thesis
    by (auto simp: register_pair_Snd)
qed

lemma equivalent_complements:
  assumes \<open>complements F G\<close>
  assumes \<open>equivalent_registers G G'\<close>
  shows \<open>complements F G'\<close>
  apply (rule complementsI)
   apply (metis assms(1) assms(2) compatible_comp_right complements_def equivalent_registers_def iso_register_is_register)
  by (metis assms(1) assms(2) complements_def equivalent_registers_def equivalent_registers_pair_right iso_register_comp)

lemma complements_complement_pair:
  assumes [simp]: \<open>compatible F G\<close>
  assumes FG': \<open>complements (F;G) FG'\<close>
  shows \<open>complements F (G; FG')\<close>
proof (rule complementsI)
  note [[simproc del: compatibility_warn]]
  have \<open>compatible (F;G) FG'\<close>
    using FG' complements_def by auto
  then have [simp]: \<open>compatible F FG'\<close>
    by (smt (verit)assms(1) compatibleI compatible_register1 compatible_register2 id_update_right register_of_id register_pair_apply' swap_registers)
  have [simp]: \<open>compatible G FG'\<close>
    by (smt (verit) register_pair_apply \<open>compatible (F;G) FG'\<close> assms(1) compatibleI compatible_register1 compatible_register2 id_update_right register_of_id swap_registers)

  have \<open>equivalent_registers (F; (G; FG')) ((F;G); FG')\<close>
    apply (rule equivalent_registers_assoc)
      apply simp
     apply (smt (verit) \<open>compatible (F;G) FG'\<close> assms(1) compatibleI compatible_register1 compatible_register2 id_update_right register_of_id register_pair_apply' swap_registers)
    by (smt (verit) register_pair_apply \<open>compatible (F;G) FG'\<close> assms(1) compatibleI compatible_register1 compatible_register2 id_update_right register_of_id swap_registers)
  also have \<open>equivalent_registers \<dots> id\<close>
    by (meson assms complement_is_complement complements_def equivalent_registers_sym iso_register_equivalent_id pair_is_register)
  finally show \<open>iso_register (F;(G;FG'))\<close>
    using equivalent_registers_sym iso_register_equivalent_id by blast
  show \<open>compatible F (G;FG')\<close>
    by (auto intro!: compatible3')
qed

lemma equivalent_registers_complement:
  assumes \<open>equivalent_registers F G\<close>
  assumes \<open>complements F F'\<close>
  assumes \<open>complements G G'\<close>
  shows \<open>equivalent_registers F' G'\<close>
  by (meson complement_unique assms(1) assms(2) assms(3) complements_sym equivalent_complements)

lemma equivalent_registers_complement':
  assumes \<open>equivalent_registers F G\<close>
  shows \<open>equivalent_registers (complement F) (complement G)\<close>
  using assms apply (rule equivalent_registers_complement)
  using assms complement_is_complement equivalent_registers_register_left equivalent_registers_register_right
  by blast+

lemma complements_complement_pair':
  assumes [simp]: \<open>compatible F G\<close>
  assumes FG': \<open>complements (F;G) FG'\<close>
  shows \<open>complements G (F; FG')\<close>
proof -
  have \<open>equivalent_registers (F;G) (G;F)\<close>
    using assms(1) equivalent_registers_def iso_register_swap pair_is_register pair_o_swap by blast
  with FG' have *: \<open>complements (G;F) FG'\<close>
    by (meson complements_sym equivalent_complements)
  show ?thesis
    apply (rule complements_complement_pair)
    using * by (simp_all add: compatible_sym)
qed

lemma complements_chain: 
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  shows \<open>complements (F o G) (complement F; F o complement G)\<close>
proof (rule complementsI)
  show \<open>compatible (F o G) (complement F; F o complement G)\<close>
    by auto
  have \<open>equivalent_registers (F \<circ> G;(complement F;F \<circ> complement G)) (F \<circ> G;(F \<circ> complement G;complement F))\<close>
    apply (rule equivalent_registersI[where I=\<open>id \<otimes>\<^sub>r swap\<close>])
    by (auto intro!: iso_register_tensor_is_iso_register simp: pair_o_tensor)
  also have \<open>equivalent_registers \<dots> ((F \<circ> G;F \<circ> complement G);complement F)\<close>
    apply (rule equivalent_registersI[where I=assoc])
    by (auto intro!: iso_register_tensor_is_iso_register simp: pair_o_tensor)
  also have \<open>equivalent_registers \<dots> (F o (G; complement G);complement F)\<close>
    by (metis (no_types, lifting) assms(1) assms(2) calculation compatible_complement_right
        equivalent_registers_sym equivalent_registers_trans register_comp_pair)
  also have \<open>equivalent_registers \<dots> (F o id;complement F)\<close>
    apply (rule equivalent_registers_pair_left, simp)
    apply (rule equivalent_registers_comp, simp)
    by (metis assms(2) complement_is_complement complements_def equivalent_registers_def iso_register_def)
  also have \<open>equivalent_registers \<dots> id\<close>
    by (metis assms(1) comp_id complement_is_complement complements_def equivalent_registers_def iso_register_def)
  finally show \<open>iso_register (F \<circ> G;(complement F;F \<circ> complement G))\<close>
    using equivalent_registers_sym iso_register_equivalent_id by blast
qed

lemma complements_Fst_Snd[simp]: \<open>complements Fst Snd\<close>
  by (auto intro!: complementsI simp: pair_Fst_Snd)

lemma complements_Snd_Fst[simp]: \<open>complements Snd Fst\<close>
  by (auto intro!: complementsI simp flip: swap_def)

lemma compatible_unit_register[simp]: \<open>register F \<Longrightarrow> compatible F unit_register\<close>
  using compatible_sym unit_register_compatible unit_register_is_unit_register by blast

lemma complements_id_unit_register[simp]: \<open>complements id unit_register\<close>
  using complements_sym is_unit_register_def unit_register_is_unit_register by blast

lemma complements_iso_unit_register: \<open>iso_register I \<Longrightarrow> is_unit_register U \<Longrightarrow> complements I U\<close>
  using complements_sym equivalent_complements is_unit_register_def iso_register_equivalent_id by blast

lemma iso_register_complement_is_unit_register[simp]:
  assumes \<open>iso_register F\<close>
  shows \<open>is_unit_register (complement F)\<close>
  by (meson assms complement_is_complement complements_sym equivalent_complements equivalent_registers_sym is_unit_register_def iso_register_equivalent_id iso_register_is_register)

text \<open>Adding support for \<^term>\<open>is_unit_register F\<close> and \<^term>\<open>complements F G\<close> to the [@{attribute register}] attribute\<close>
lemmas [register_attribute_rule] = is_unit_register_def[THEN iffD1] complements_def[THEN iffD1]
lemmas [register_attribute_rule_immediate] = asm_rl[of \<open>is_unit_register _\<close>]

no_notation comp_update (infixl "*\<^sub>u" 55)
no_notation tensor_update (infixr "\<otimes>\<^sub>u" 70)
unbundle no register_syntax


end
