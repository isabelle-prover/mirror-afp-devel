(*  Title:       CategoryWithBoundedPushouts
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Categories with Bounded Pushouts"

subsection "Bounded Spans"

text\<open>
We call a span in a category ``bounded'' if it can be completed to a
commuting square.  A category with bounded pushouts is a category in which
every bounded span has a pushout.
\<close>

theory CategoryWithBoundedPushouts
imports Category3.EpiMonoIso Category3.CategoryWithPullbacks
begin

  context category
  begin

    definition bounded_span
    where "bounded_span h k \<equiv> \<exists>f g. commutative_square f g h k"

    lemma bounded_spanI [intro]:
    assumes "commutative_square f g h k"
    shows "bounded_span h k"
      using assms bounded_span_def by auto

    lemma bounded_spanE [elim]:
    assumes "bounded_span h k"
    obtains f g where "commutative_square f g h k"
      using assms bounded_span_def by auto

    lemma bounded_span_sym:
    shows "bounded_span h k \<Longrightarrow> bounded_span k h"
      unfolding bounded_span_def commutative_square_def
      by (metis seqE seqI)

  end

  subsection "Pushouts"

  text\<open>
    Here we give a definition of the notion ``pushout square'' in a category, and prove that
    pushout squares compose.  The definition here is currently a ``free-standing'' one,
    because it has been stated on its own, without deriving it from a general notion of colimit.
    At some future time, once the general development of limits given in \<^cite>\<open>"Category3-AFP"\<close>
    has been suitably dualized to obtain a corresponding development of colimits,
    this formal connection should be made.
  \<close>

  context category
  begin

    definition pushout_square
    where "pushout_square f g h k \<equiv>
             commutative_square f g h k \<and>
             (\<forall>f' g'. commutative_square f' g' h k \<longrightarrow> (\<exists>!l. l \<cdot> f = f' \<and> l \<cdot> g = g'))"

    lemma pushout_squareI [intro]:
    assumes "cospan f g" and "span h k" and "dom f = cod h" and "f \<cdot> h = g \<cdot> k"
    and "\<And>f' g'. commutative_square f' g' h k \<Longrightarrow> \<exists>!l. l \<cdot> f = f' \<and> l \<cdot> g = g'"
    shows "pushout_square f g h k"
      using assms pushout_square_def by simp

    lemma composition_of_pushouts:
    assumes "pushout_square u' t' t u" and "pushout_square v' t'' t' v"
    shows "pushout_square (v' \<cdot> u') t'' t (v \<cdot> u)"
    proof
      show 1: "cospan (v' \<cdot> u') t''"
        using assms
        by (metis (mono_tags, lifting) commutative_square_def seqI cod_comp
            pushout_square_def)
      show "span t (v \<cdot> u)"
        using assms pushout_square_def by fastforce
      show "dom (v' \<cdot> u') = cod t"
        using assms
        by (metis 1 commutative_squareE dom_comp pushout_square_def)
      show "(v' \<cdot> u') \<cdot> t = t'' \<cdot> v \<cdot> u"
        using assms
        by (metis commutative_squareE comp_assoc pushout_square_def)
      fix w x
      assume wx: "commutative_square w x t (v \<cdot> u)"
      show "\<exists>!l. l \<cdot> v' \<cdot> u' = w \<and> l \<cdot> t'' = x"
      proof -
        have 1: "commutative_square w (x \<cdot> v) t u"
          using wx
          by (metis (mono_tags, lifting) cod_comp commutative_square_def
              dom_comp comp_assoc seqE seqI)
        hence *: "\<exists>!z. z \<cdot> u' = w \<and> z \<cdot> t' = x \<cdot> v"
          using assms pushout_square_def by auto
        obtain z where z: "z \<cdot> u' = w \<and> z \<cdot> t' = x \<cdot> v"
          using * by auto
        have 2: "commutative_square z x t' v"
          using z
          by (metis (mono_tags, lifting) 1 cod_comp commutative_square_def
              dom_comp seqE)
        hence **: "\<exists>l. l \<cdot> v' = z \<and> l \<cdot> t'' = x"
          by (meson assms(2) pushout_square_def)
        obtain l where l: "l \<cdot> v' = z \<and> l \<cdot> t'' = x"
          using ** by auto
        have "l \<cdot> v' \<cdot> u' = w \<and> l \<cdot> t'' = x"
          using l comp_assoc z by force
        moreover have "\<And>l l'. \<lbrakk>l \<cdot> v' \<cdot> u' = w \<and> l \<cdot> t'' = x;
                               l' \<cdot> v' \<cdot> u' = w \<and> l' \<cdot> t'' = x\<rbrakk>
                                 \<Longrightarrow> l = l'"
        proof -
          fix l l'
          assume l: "l \<cdot> v' \<cdot> u' = w \<and> l \<cdot> t'' = x"
          assume l': "l' \<cdot> v' \<cdot> u' = w \<and> l' \<cdot> t'' = x"
          have "(l \<cdot> v') \<cdot> u' = w \<and> (l \<cdot> v') \<cdot> t' = x \<cdot> v \<and>
                (l' \<cdot> v') \<cdot> u' = w \<and> (l' \<cdot> v') \<cdot> t' = x \<cdot> v"
            using assms(2)
            by (metis commutative_squareE pushout_square_def l l' comp_assoc)
          thus "l = l'"
            by (metis * 2 assms(2) l l' pushout_square_def z)
        qed
        ultimately show ?thesis by blast
      qed
    qed

  end

  locale elementary_category_with_bounded_pushouts =
    category C
  for C :: "'a comp"            (infixr \<open>\<cdot>\<close> 55)
  and inj0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (\<open>\<i>\<^sub>0[_, _]\<close>)
  and inj1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (\<open>\<i>\<^sub>1[_, _]\<close>) +
  assumes inj0_ext: "\<not> bounded_span h k \<Longrightarrow> \<i>\<^sub>0[h, k] = null"
  and inj1_ext: "\<not> bounded_span h k \<Longrightarrow> \<i>\<^sub>1[h, k] = null"
  and pushout_commutes [intro]:
        "bounded_span h k \<Longrightarrow> commutative_square \<i>\<^sub>1[h, k] \<i>\<^sub>0[h, k] h k"
  and pushout_universal:
        "commutative_square f g h k \<Longrightarrow> \<exists>!l. l \<cdot> \<i>\<^sub>1[h, k] = f \<and> l \<cdot> \<i>\<^sub>0[h, k] = g"
  begin

    lemma dom_inj [simp]:
    assumes "bounded_span h k"
    shows "dom \<i>\<^sub>0[h, k] = cod k" and "dom \<i>\<^sub>1[h, k] = cod h"
      using assms pushout_commutes by blast+

    lemma cod_inj:
    assumes "bounded_span h k"
    shows "cod \<i>\<^sub>1[h, k] = cod \<i>\<^sub>0[h, k]"
      using assms pushout_commutes by auto

    lemma has_bounded_pushouts:
    assumes "bounded_span h k"
    shows "pushout_square \<i>\<^sub>1[h, k] \<i>\<^sub>0[h, k] h k"
      using assms pushout_square_def pushout_commutes pushout_universal by simp

  end

end
