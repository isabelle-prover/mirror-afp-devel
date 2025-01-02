(*  Title:      Schutz_Spacetime/TemporalOrderExtra.thy
    Authors:    Richard Schmoetten, Jake Palmer and Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)
theory TemporalOrderExtra
  imports Main Minkowski TernaryOrdering TemporalOrderOnPath "HOL-Algebra.Order"
begin

section \<open>Ternary-to-binary\<close>

context MinkowskiSpacetime
begin

\<comment> \<open>The cases we need to cover where x <= y if we take a < b as our ordering basis:
    [abxy], [axby], [axyb],
    [xaby], [xayb], [xyab].
\<close>
abbreviation betw_gorder :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a gorder" where
  "betw_gorder a b Q \<equiv> \<lparr>carrier = Q, eq = (=),
                        le = (\<lambda>x y. x = y
                                 \<comment> \<open>Base case. Everything from here is < really.\<close>
                                 \<or> x = a \<and> y = b
                                 \<comment> \<open>a < y\<noteq>b case (\<noteq> fact is covered by [___].\<close>
                                 \<or> x = a \<and> ([a;b;y] \<or> [a;y;b])
                                 \<comment> \<open>b < y case. Can't have [b a y].\<close>
                                 \<or> x = b \<and> [a;b;y]
                                 \<comment> \<open>x < a\<close>
                                 \<or> y = a \<and> [x;a;b]
                                 \<comment> \<open>x < b\<close>
                                 \<or> y = b \<and> ([x;a;b] \<or> [a;x;b])
                                 \<comment> \<open>4-event cases.\<close>
                                 \<or> [a;b;x;y] \<or> [a;x;b;y] \<or> [a;x;y;b]
                                 \<or> [x;a;b;y] \<or> [x;a;y;b] \<or> [x;y;a;b]
                             )
                         \<rparr>"

lemma betw_total_order_on_path:
  fixes a b :: 'a
    and Q :: "'a set"
  assumes "Q \<in> \<P>"
      and "a \<in> Q"
      and "b \<in> Q"
      and "a \<noteq> b"
  shows "total_order (betw_gorder a b Q)" (is "total_order ?o")
proof
  show "\<And>x. x \<in> carrier ?o \<Longrightarrow> x .=\<^bsub>?o\<^esub> x"
    by simp
next
  show "\<And>x y. \<lbrakk>x .=\<^bsub>?o\<^esub> y; x \<in> carrier ?o; y \<in> carrier ?o\<rbrakk> \<Longrightarrow> y .=\<^bsub>?o\<^esub> x"
    by simp
next
  show "\<And>x y z. \<lbrakk>x .=\<^bsub>?o\<^esub> y; y .=\<^bsub>?o\<^esub> z; x \<in> carrier ?o;
                 y \<in> carrier ?o; z \<in> carrier ?o\<rbrakk>
        \<Longrightarrow> x .=\<^bsub>?o\<^esub> z"
    by simp
next
  show "\<And>x. x \<in> carrier ?o \<Longrightarrow> x \<sqsubseteq>\<^bsub>?o\<^esub> x"
    by simp
next
  show "\<And>x y. \<lbrakk>x \<sqsubseteq>\<^bsub>?o\<^esub> y; y \<sqsubseteq>\<^bsub>?o\<^esub> x; x \<in> carrier ?o; y \<in> carrier ?o\<rbrakk> \<Longrightarrow> x .=\<^bsub>?o\<^esub> y"
    by (smt abc_abc_neq abcd_dcba_only(18) betw4_sym betw4_weak eq_object.select_convs(1)
      gorder.select_convs(1))
next
  show "\<And>x y z.
       \<lbrakk>x \<sqsubseteq>\<^bsub>?o\<^esub> y; y \<sqsubseteq>\<^bsub>?o\<^esub> z; x \<in> carrier ?o;
        y \<in> carrier ?o; z \<in> carrier ?o\<rbrakk>
       \<Longrightarrow> x \<sqsubseteq>\<^bsub>?o\<^esub> z"
    by (smt (z3) abc_acd_abd abc_acd_bcd abc_bcd_acd abc_only_cba(1,4) assms(1)
      gorder.select_convs(1) partial_object.select_convs(1) some_betw2)
next
  show "\<And>x y z w.
       \<lbrakk>x .=\<^bsub>?o\<^esub> y; z .=\<^bsub>?o\<^esub> w; x \<in> carrier ?o;
        y \<in> carrier ?o; z \<in> carrier ?o; w \<in> carrier ?o\<rbrakk>
       \<Longrightarrow> (x \<sqsubseteq>\<^bsub>?o\<^esub> z) = (y \<sqsubseteq>\<^bsub>?o\<^esub> w)"
    by simp
next
  show "(.=\<^bsub>?o\<^esub>) = (=)"
    by simp
next
  show "\<And>x y. \<lbrakk>x \<in> carrier (betw_gorder a b Q); y \<in> carrier (betw_gorder a b Q)\<rbrakk>
           \<Longrightarrow> x \<sqsubseteq>\<^bsub>betw_gorder a b Q\<^esub> y \<or> y \<sqsubseteq>\<^bsub>betw_gorder a b Q\<^esub> x"
    by (smt (z3) abc_sym assms gorder.select_convs(1) partial_object.select_convs(1)
      some_betw2 some_betw4b)
qed

end

end