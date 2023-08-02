(* Title:      An Operation to Select Components in Algebras with Minimisation
   Author:     Nicolas Robinson-O'Brien
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>An Operation to Select Components in Algebras with Minimisation\<close>

text \<open>
In this theory we show that an operation to select components of a graph can be defined in m-Kleene Algebras.
This work is by Nicolas Robinson-O'Brien.
\<close>

theory M_Choose_Component

imports
  Stone_Relation_Algebras.Choose_Component
  Matrix_Aggregation_Algebras

begin

text \<open>
Every \<open>m_kleene_algebra\<close> is an instance of \<open>choose_component_algebra\<close> when the \<open>choose_component\<close> operation is defined as follows:
\<close>

context m_kleene_algebra
begin

definition "m_choose_component e v \<equiv>
  if vector_classes e v then
    e * minarc(v) * top
  else
    bot"

sublocale m_choose_component_algebra: choose_component_algebra where choose_component = m_choose_component
proof
  fix e v
  show "m_choose_component e v \<le> -- v"
  proof (cases "vector_classes e v")
    case True
    hence "m_choose_component e v = e * minarc(v) * top"
      by (simp add: m_choose_component_def)
    also have "... \<le> e * --v * top"
      by (simp add: comp_isotone minarc_below)
    also have "... = e * v * top"
      using True vector_classes_def by auto
    also have "... \<le> v * top"
      using True vector_classes_def mult_assoc by auto
    finally show ?thesis
      using True vector_classes_def by auto
  next
    case False
    hence "m_choose_component e v = bot"
      using False m_choose_component_def by auto
    thus ?thesis
      by simp
  qed
next
  fix e v
  show "vector (m_choose_component e v)"
  proof (cases "vector_classes e v")
    case True
    thus ?thesis
      by (simp add: mult_assoc m_choose_component_def)
  next
    case False
    thus ?thesis
      by (simp add: m_choose_component_def)
  qed
next
  fix e v
  show "regular (m_choose_component e v)"
    using minarc_regular regular_mult_closed vector_classes_def m_choose_component_def by auto
next
  fix e v
  show "m_choose_component e v * (m_choose_component e v)\<^sup>T \<le> e"
  proof (cases "vector_classes e v")
    case True
    assume 1: "vector_classes e v"
    hence "m_choose_component e v * (m_choose_component e v)\<^sup>T = e * minarc(v) * top * (e * minarc(v) * top)\<^sup>T"
      by (simp add: m_choose_component_def)
    also have "... = e * minarc(v) * top * top\<^sup>T * minarc(v)\<^sup>T * e\<^sup>T"
      by (metis comp_associative conv_dist_comp)
    also have "... = e * minarc(v) * top * top * minarc(v)\<^sup>T * e"
      using True vector_classes_def by auto
    also have "... = e * minarc(v) * top * minarc(v)\<^sup>T * e"
      by (simp add: comp_associative)
    also have "... \<le> e"
    proof (cases "v = bot")
      case True
      thus ?thesis
        by (simp add: True minarc_bot)
    next
      case False
      assume 3: "v \<noteq> bot"
      hence "e * minarc(v) * top * minarc(v)\<^sup>T \<le> e * 1"
        using 3 minarc_arc arc_expanded comp_associative mult_right_isotone by fastforce
      hence "e * minarc(v) * top * minarc(v)\<^sup>T * e \<le> e * 1 * e"
        using mult_left_isotone by auto
      also have "... = e"
        using True preorder_idempotent vector_classes_def by auto
      thus ?thesis
        using calculation by auto
    qed
    thus ?thesis
      by (simp add: calculation)
  next
    case False
    thus ?thesis
      by (simp add: m_choose_component_def)
  qed
next
  fix e v
  show "e * m_choose_component e v \<le> m_choose_component e v"
  proof (cases "vector_classes e v")
    case True
    thus ?thesis
      using comp_right_one dual_order.eq_iff mult_isotone vector_classes_def m_choose_component_def mult_assoc by metis
  next
    case False
    thus ?thesis
      by (simp add: m_choose_component_def)
  qed
next
  fix e v
  show "vector_classes e v \<longrightarrow> m_choose_component e v \<noteq> bot"
  proof (cases "vector_classes e v")
    case True
    hence "m_choose_component e v \<ge> minarc(v) * top"
      using vector_classes_def m_choose_component_def comp_associative minarc_arc shunt_bijective by fastforce
    also have "... \<ge> minarc(v)"
      using calculation dual_order.trans top_right_mult_increasing by blast
    thus ?thesis
      using le_bot minarc_bot_iff vector_classes_def by fastforce
  next
    case False
    thus ?thesis
      by blast
  qed
qed

sublocale m_choose_component_algebra_tarski: choose_component_algebra_tarski where choose_component = m_choose_component
  ..

end

class m_kleene_algebra_choose_component = m_kleene_algebra + choose_component_algebra

end

