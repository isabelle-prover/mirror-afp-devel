\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generic Compositions\<close>
subsection \<open>Basic Setup\<close>
theory Transport_Compositions_Generic_Base
  imports
    Transport_Base
begin

locale transport_comp =
  t1 : transport L1 R1 l1 r1 + t2 : transport L2 R2 l2 r2
  for L1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R1 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l1 :: "'a \<Rightarrow> 'b"
  and r1 :: "'b \<Rightarrow> 'a"
  and L2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and R2 :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and l2 :: "'b \<Rightarrow> 'c"
  and r2 :: "'c \<Rightarrow> 'b"
begin

text \<open>This locale collects results about the composition of transportable
components under some generic compatibility conditions on @{term "R1"} and
@{term "L2"} (cf. below). The composition is rather subtle, but in return can
cover quite general cases.

Explanations and intuition about the construction can be found in \<^cite>\<open>"transport"\<close>.\<close>

notation L1 (infix "\<le>\<^bsub>L1\<^esub>" 50)
notation R1 (infix "\<le>\<^bsub>R1\<^esub>" 50)
notation L2 (infix "\<le>\<^bsub>L2\<^esub>" 50)
notation R2 (infix "\<le>\<^bsub>R2\<^esub>" 50)

notation t1.ge_left (infix "\<ge>\<^bsub>L1\<^esub>" 50)
notation t1.ge_right (infix "\<ge>\<^bsub>R1\<^esub>" 50)
notation t2.ge_left (infix "\<ge>\<^bsub>L2\<^esub>" 50)
notation t2.ge_right (infix "\<ge>\<^bsub>R2\<^esub>" 50)

notation t1.left_Galois (infix "\<^bsub>L1\<^esub>\<lessapprox>" 50)
notation t1.right_Galois (infix "\<^bsub>R1\<^esub>\<lessapprox>" 50)
notation t2.left_Galois (infix "\<^bsub>L2\<^esub>\<lessapprox>" 50)
notation t2.right_Galois (infix "\<^bsub>R2\<^esub>\<lessapprox>" 50)

notation t1.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L1\<^esub>" 50)
notation t1.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R1\<^esub>" 50)
notation t2.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L2\<^esub>" 50)
notation t2.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R2\<^esub>" 50)

notation t1.right_ge_Galois (infix "\<^bsub>R1\<^esub>\<greaterapprox>" 50)
notation t1.Galois_right (infix "\<lessapprox>\<^bsub>R1\<^esub>" 50)
notation t2.right_ge_Galois (infix "\<^bsub>R2\<^esub>\<greaterapprox>" 50)
notation t2.Galois_right (infix "\<lessapprox>\<^bsub>R2\<^esub>" 50)

notation t1.left_ge_Galois (infix "\<^bsub>L1\<^esub>\<greaterapprox>" 50)
notation t1.Galois_left (infix "\<lessapprox>\<^bsub>L1\<^esub>" 50)
notation t2.left_ge_Galois (infix "\<^bsub>L2\<^esub>\<greaterapprox>" 50)
notation t2.Galois_left (infix "\<lessapprox>\<^bsub>L2\<^esub>" 50)

notation t1.unit ("\<eta>\<^sub>1")
notation t1.counit ("\<epsilon>\<^sub>1")
notation t2.unit ("\<eta>\<^sub>2")
notation t2.counit ("\<epsilon>\<^sub>2")

definition "L \<equiv> (\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<^bsub>R1\<^esub>\<lessapprox>)"

lemma left_rel_eq_comp: "L = (\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<^bsub>R1\<^esub>\<lessapprox>)"
  unfolding L_def ..

definition "l \<equiv> l2 \<circ> l1"

lemma left_eq_comp: "l = l2 \<circ> l1"
  unfolding l_def ..

lemma left_eq [simp]: "l x = l2 (l1 x)"
  unfolding left_eq_comp by simp

context
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1 .

abbreviation "R \<equiv> flip.L"
abbreviation "r \<equiv> flip.l"

lemma right_rel_eq_comp: "R = (\<^bsub>R2\<^esub>\<lessapprox>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)"
  unfolding flip.L_def ..

lemma right_eq_comp: "r = r1 \<circ> r2"
  unfolding flip.l_def ..

lemma right_eq [simp]: "r z = r1 (r2 z)"
  unfolding right_eq_comp by simp

lemmas transport_defs = left_rel_eq_comp left_eq_comp right_rel_eq_comp right_eq_comp

end

sublocale transport L R l r .

(*FIXME: somehow the notation for the fixed parameters L and R, defined in
Order_Functions_Base.thy, is lost. We hence re-declare it here.*)
notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

lemma left_relI [intro]:
  assumes "x \<^bsub>L1\<^esub>\<lessapprox> y"
  and "y \<le>\<^bsub>L2\<^esub> y'"
  and "y' \<^bsub>R1\<^esub>\<lessapprox> x'"
  shows "x \<le>\<^bsub>L\<^esub> x'"
  unfolding left_rel_eq_comp using assms by blast

lemma left_relE [elim]:
  assumes "x \<le>\<^bsub>L\<^esub> x'"
  obtains y y' where "x \<^bsub>L1\<^esub>\<lessapprox> y" "y \<le>\<^bsub>L2\<^esub> y'" "y' \<^bsub>R1\<^esub>\<lessapprox> x'"
  using assms unfolding left_rel_eq_comp by blast

context
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1 .
interpretation inv : transport_comp "(\<ge>\<^bsub>L1\<^esub>)" "(\<ge>\<^bsub>R1\<^esub>)" l1 r1 "(\<ge>\<^bsub>L2\<^esub>)" "(\<ge>\<^bsub>R2\<^esub>)" l2 r2 .

lemma ge_left_rel_eq_left_rel_inv_if_galois_prop [simp]:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>R1\<^esub>) \<unlhd> (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  shows "(\<ge>\<^bsub>L\<^esub>) = transport_comp.L (\<ge>\<^bsub>L1\<^esub>) (\<ge>\<^bsub>R1\<^esub>) l1 r1 (\<ge>\<^bsub>L2\<^esub>)"
  using assms unfolding left_rel_eq_comp inv.left_rel_eq_comp
  by (simp add: rel_comp_assoc)

corollary left_rel_inv_iff_left_rel_if_galois_prop [iff]:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>R1\<^esub>) \<unlhd> (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  shows "(transport_comp.L (\<ge>\<^bsub>L1\<^esub>) (\<ge>\<^bsub>R1\<^esub>) l1 r1 (\<ge>\<^bsub>L2\<^esub>)) x x' \<longleftrightarrow> x' \<le>\<^bsub>L\<^esub> x"
  using assms by (simp flip: ge_left_rel_eq_left_rel_inv_if_galois_prop)


subsubsection \<open>Simplification of Relations\<close>

lemma left_rel_le_left_rel1I:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and mono_l1: "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))) l1"
  shows "(\<le>\<^bsub>L\<^esub>) \<le> (\<le>\<^bsub>L1\<^esub>)"
proof (rule le_relI)
  fix x x' assume "x \<le>\<^bsub>L\<^esub> x'"
  with mono_l1 obtain y where "l1 x \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>R1\<^esub> l1 x'" by blast
  with \<open>((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> \<open>x \<le>\<^bsub>L\<^esub> x'\<close> have "x \<le>\<^bsub>L1\<^esub> r1 y" by blast
  moreover from \<open>((\<le>\<^bsub>R1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L1\<^esub>)) r1 l1\<close> \<open>y \<le>\<^bsub>R1\<^esub> l1 x'\<close> \<open>x \<le>\<^bsub>L\<^esub> x'\<close>
    have "... \<le>\<^bsub>L1\<^esub> x'" by blast
  ultimately show "x \<le>\<^bsub>L1\<^esub> x'" using trans_L1 by blast
qed

lemma left_rel1_le_left_relI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and mono_l1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))) l1"
  shows "(\<le>\<^bsub>L1\<^esub>) \<le> (\<le>\<^bsub>L\<^esub>)"
proof (rule le_relI)
  fix x x' assume "x \<le>\<^bsub>L1\<^esub> x'"
  with mono_l1 obtain y y' where
    "l1 x \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>L2\<^esub> y'" "y' \<le>\<^bsub>R1\<^esub> l1 x'" by blast
  with \<open>((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> \<open>x \<le>\<^bsub>L1\<^esub> x'\<close> have "x \<^bsub>L1\<^esub>\<lessapprox> y" by blast
  moreover note \<open>y \<le>\<^bsub>L2\<^esub> y'\<close>
  moreover from \<open>y' \<le>\<^bsub>R1\<^esub> l1 x'\<close> \<open>x \<le>\<^bsub>L1\<^esub> x'\<close> have "y' \<^bsub>R1\<^esub>\<lessapprox> x'" by blast
  ultimately show "x \<le>\<^bsub>L\<^esub> x'" by blast
qed

corollary left_rel_eq_left_rel1I:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L1\<^esub>)) r1 l1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))) l1"
  shows "(\<le>\<^bsub>L\<^esub>) = (\<le>\<^bsub>L1\<^esub>)"
  using assms by (intro antisym left_rel_le_left_rel1I left_rel1_le_left_relI)

text \<open>Note that we may not necessarily have @{term "(\<le>\<^bsub>L\<^esub>) = (\<le>\<^bsub>L1\<^esub>)"}, even in
case of equivalence relations. Depending on the use case, one thus may wish to
use an alternative composition operation.\<close>

lemma ex_order_equiv_left_rel_neq_left_rel1:
  "\<exists>(L1 :: bool \<Rightarrow> _) (R1 :: bool \<Rightarrow> _) l1 r1
    (L2 :: bool \<Rightarrow> _) (R2 :: bool \<Rightarrow> _) l2 r2.
    (L1 \<equiv>\<^sub>o R1) l1 r1
    \<and> equivalence_rel L1 \<and> equivalence_rel R1
    \<and> (L2 \<equiv>\<^sub>o R2) l2 r2
    \<and> equivalence_rel L2 \<and> equivalence_rel R2
    \<and> transport_comp.L L1 R1 l1 r1 L2 \<noteq> L1"
proof (intro exI conjI)
  let ?L1 = "(=) :: bool \<Rightarrow> _" let ?R1 = ?L1 let ?l1 = id let ?r1 = ?l1
  let ?L2 = "\<top> :: bool \<Rightarrow> bool \<Rightarrow> bool" let ?R2 = ?L2 let ?l2 = id let ?r2 = ?l2
  interpret tc : transport_comp ?L1 ?R1 ?l1 ?r1 ?L2 ?R2 ?l2 ?r2 .
  show "(?L1 \<equiv>\<^sub>o ?R1) ?l1 ?r1" by fastforce
  show "equivalence_rel ?L1" "equivalence_rel ?R1" by (fact equivalence_eq)+
  show "(?L2 \<equiv>\<^sub>o ?R2) ?l2 ?r2" by fastforce
  show "equivalence_rel ?L2" "equivalence_rel ?R2" by (fact equivalence_top)+
  show "tc.L \<noteq> ?L1"
  proof -
    have "\<not>(?L1 False True)" by blast
    moreover have "tc.L False True" by (intro tc.left_relI) auto
    ultimately show ?thesis by auto
  qed
qed

end


subsubsection \<open>Generic Left to Right Introduction Rules\<close>

text \<open>The following lemmas generalise the proof outline used, for example,
when proving monotonicity and the Galois property (cf. the paper \<^cite>\<open>"transport"\<close>).\<close>

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1 .

lemma right_rel_if_left_relI:
  assumes "x \<le>\<^bsub>L\<^esub> x'"
  and l1_R1_if_L1_r1: "\<And>y. in_codom (\<le>\<^bsub>R1\<^esub>) y \<Longrightarrow> x \<le>\<^bsub>L1\<^esub> r1 y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> y"
  and t_R1_if_l1_R1: "\<And>y. l1 x \<le>\<^bsub>R1\<^esub> y \<Longrightarrow> t y \<le>\<^bsub>R1\<^esub> y"
  and R2_l2_if_t_L2_if_l1_R1:
    "\<And>y y'. l1 x \<le>\<^bsub>R1\<^esub> y \<Longrightarrow> t y \<le>\<^bsub>L2\<^esub> y' \<Longrightarrow> z \<le>\<^bsub>R2\<^esub> l2 y'"
  and R1_b_if_R1_l1_if_R1_l1:
    "\<And>y y'. y \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> y' \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> y' \<le>\<^bsub>R1\<^esub> b y"
  and b_L2_r2_if_in_codom_L2_b_if_R1_l1:
    "\<And>y. y \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> in_codom (\<le>\<^bsub>L2\<^esub>) (b y) \<Longrightarrow> b y \<le>\<^bsub>L2\<^esub> r2 z'"
  and in_codom_R2_if_in_codom_L2_b_if_R1_l1:
    "\<And>y. y \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> in_codom (\<le>\<^bsub>L2\<^esub>) (b y) \<Longrightarrow> in_codom (\<le>\<^bsub>R2\<^esub>) z'"
  and rel_comp_le: "(\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<le> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)"
  and in_codom_rel_comp_le: "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  shows "z \<le>\<^bsub>R\<^esub> z'"
proof -
  from \<open>x \<le>\<^bsub>L\<^esub> x'\<close> obtain yl yl' where "l1 x \<le>\<^bsub>R1\<^esub> yl" "yl \<le>\<^bsub>L2\<^esub> yl'" "yl' \<le>\<^bsub>R1\<^esub> l1 x'"
    using l1_R1_if_L1_r1 by blast
  moreover then have "t yl \<le>\<^bsub>R1\<^esub> yl" by (intro t_R1_if_l1_R1)
  ultimately have "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) (t yl) (l1 x')" using rel_comp_le by blast
  then obtain y where "t yl \<le>\<^bsub>L2\<^esub> y" "y \<le>\<^bsub>R1\<^esub> l1 x'" by blast
  show "z \<le>\<^bsub>R\<^esub> z'"
  proof (rule flip.left_relI)
    from \<open>t yl \<le>\<^bsub>L2\<^esub> y\<close> \<open>l1 x \<le>\<^bsub>R1\<^esub> yl\<close> show "z \<^bsub>R2\<^esub>\<lessapprox> y"
      by (auto intro: R2_l2_if_t_L2_if_l1_R1)
    from \<open>yl' \<le>\<^bsub>R1\<^esub> l1 x'\<close> \<open>y \<le>\<^bsub>R1\<^esub> l1 x'\<close> show "y \<le>\<^bsub>R1\<^esub> b yl'"
      by (rule R1_b_if_R1_l1_if_R1_l1)
    show "b yl' \<^bsub>L2\<^esub>\<lessapprox> z'"
    proof (rule t2.left_GaloisI)
      from \<open>yl' \<le>\<^bsub>R1\<^esub> l1 x'\<close> have "yl' \<le>\<^bsub>R1\<^esub> b yl'"
        by (intro R1_b_if_R1_l1_if_R1_l1)
      with \<open>l1 x \<le>\<^bsub>R1\<^esub> yl\<close> \<open>yl \<le>\<^bsub>L2\<^esub> yl'\<close> in_codom_rel_comp_le
        have "in_codom (\<le>\<^bsub>L2\<^esub>) (b yl')" by blast
      with \<open>yl' \<le>\<^bsub>R1\<^esub> l1 x'\<close> show "b yl' \<le>\<^bsub>L2\<^esub> r2 z'" "in_codom (\<le>\<^bsub>R2\<^esub>) z'"
        by (auto intro: b_L2_r2_if_in_codom_L2_b_if_R1_l1
          in_codom_R2_if_in_codom_L2_b_if_R1_l1)
    qed
  qed
qed

lemma right_rel_if_left_relI':
  assumes "x \<le>\<^bsub>L\<^esub> x'"
  and l1_R1_if_L1_r1: "\<And>y. in_codom (\<le>\<^bsub>R1\<^esub>) y \<Longrightarrow> x \<le>\<^bsub>L1\<^esub> r1 y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> y"
  and R1_b_if_R1_l1: "\<And>y. y \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> y \<le>\<^bsub>R1\<^esub> b y"
  and L2_r2_if_L2_b_if_R1_l1:
    "\<And>y y'. y \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> y' \<le>\<^bsub>L2\<^esub> b y \<Longrightarrow> y' \<le>\<^bsub>L2\<^esub> r2 z'"
  and in_codom_R2_if_L2_b_if_R1_l1:
    "\<And>y y'. y \<le>\<^bsub>R1\<^esub> l1 x' \<Longrightarrow> y' \<le>\<^bsub>L2\<^esub> b y \<Longrightarrow> in_codom (\<le>\<^bsub>R2\<^esub>) z'"
  and t_R1_if_R1_l1_if_l1_R1:
    "\<And>y y' y''. l1 x \<le>\<^bsub>R1\<^esub> y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> y' \<Longrightarrow> t y \<le>\<^bsub>R1\<^esub> y'"
  and R2_l2_t_if_in_dom_L2_t_if_l1_R1:
    "\<And>y y'. l1 x \<le>\<^bsub>R1\<^esub> y \<Longrightarrow> in_dom (\<le>\<^bsub>L2\<^esub>) (t y) \<Longrightarrow> z \<le>\<^bsub>R2\<^esub> l2 (t y)"
  and in_codom_L2_t_if_in_dom_L2_t_if_l1_R1:
    "\<And>y y'. l1 x \<le>\<^bsub>R1\<^esub> y \<Longrightarrow> in_dom (\<le>\<^bsub>L2\<^esub>) (t y) \<Longrightarrow> in_codom (\<le>\<^bsub>L2\<^esub>) (t y)"
  and rel_comp_le: "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and in_dom_rel_comp_le: "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  shows "z \<le>\<^bsub>R\<^esub> z'"
proof -
  from \<open>x \<le>\<^bsub>L\<^esub> x'\<close> obtain yl yl' where "l1 x \<le>\<^bsub>R1\<^esub> yl" "yl \<le>\<^bsub>L2\<^esub> yl'" "yl' \<le>\<^bsub>R1\<^esub> l1 x'"
    using l1_R1_if_L1_r1 by blast
  moreover then have "yl' \<le>\<^bsub>R1\<^esub> b yl'" by (intro R1_b_if_R1_l1)
  ultimately have "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) (l1 x) (b yl')" using rel_comp_le by blast
  then obtain y where "l1 x \<le>\<^bsub>R1\<^esub> y" "y \<le>\<^bsub>L2\<^esub> b yl'" by blast
  show "z \<le>\<^bsub>R\<^esub> z'"
  proof (rule flip.left_relI)
    from \<open>yl' \<le>\<^bsub>R1\<^esub> l1 x'\<close> \<open>y \<le>\<^bsub>L2\<^esub> b yl'\<close>
      have "in_codom (\<le>\<^bsub>R2\<^esub>) z'" "y \<le>\<^bsub>L2\<^esub> r2 z'"
      by (auto intro: in_codom_R2_if_L2_b_if_R1_l1 L2_r2_if_L2_b_if_R1_l1)
    then show "y \<^bsub>L2\<^esub>\<lessapprox> z'" by blast
    from \<open>l1 x \<le>\<^bsub>R1\<^esub> yl\<close> \<open>l1 x \<le>\<^bsub>R1\<^esub> y\<close> show "t yl \<le>\<^bsub>R1\<^esub> y" by (rule t_R1_if_R1_l1_if_l1_R1)
    show "z \<^bsub>R2\<^esub>\<lessapprox> t yl"
    proof (rule flip.t1.left_GaloisI)
      from \<open>l1 x \<le>\<^bsub>R1\<^esub> yl\<close> have "t yl \<le>\<^bsub>R1\<^esub> yl" by (intro t_R1_if_R1_l1_if_l1_R1)
      with \<open>yl \<le>\<^bsub>L2\<^esub> yl'\<close> \<open>yl' \<le>\<^bsub>R1\<^esub> l1 x'\<close> in_dom_rel_comp_le have "in_dom (\<le>\<^bsub>L2\<^esub>) (t yl)"
        by blast
      with \<open>l1 x \<le>\<^bsub>R1\<^esub> yl\<close>
        show "z \<le>\<^bsub>R2\<^esub> l2 (t yl)" "in_codom (\<le>\<^bsub>L2\<^esub>) (t yl)" by (auto intro:
          R2_l2_t_if_in_dom_L2_t_if_l1_R1 in_codom_L2_t_if_in_dom_L2_t_if_l1_R1)
    qed
  qed
qed


subsubsection \<open>Simplification of Monotonicity Assumptions\<close>

text \<open>Some sufficient conditions for monotonicity assumptions that repeatedly
arise in various places.\<close>

lemma mono_in_dom_left_rel_left1_if_in_dom_rel_comp_le:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  shows "([in_dom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  using assms by (intro dep_mono_wrt_predI) blast

lemma mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  shows "([in_codom (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
  using assms by (intro dep_mono_wrt_predI) blast


subsubsection \<open>Simplification of Compatibility Conditions\<close>

text \<open>Most results will depend on certain compatibility conditions between
@{term "(\<le>\<^bsub>R1\<^esub>)"} and @{term "(\<le>\<^bsub>L2\<^esub>)"}. We next derive some sufficient assumptions
for these conditions.\<close>

end

lemma rel_comp_comp_le_rel_comp_if_rel_comp_comp_if_in_dom_leI:
  assumes trans_R: "transitive R"
  and refl_S: "reflexive_on P S"
  and in_dom_le: "in_dom (R \<circ>\<circ> S \<circ>\<circ> R) \<le> P"
  and rel_comp_le: "(S \<circ>\<circ> R \<circ>\<circ> S) \<le> (S \<circ>\<circ> R)"
  shows "(R \<circ>\<circ> S \<circ>\<circ> R) \<le> (S \<circ>\<circ> R)"
proof (intro le_relI)
  fix x y assume "(R \<circ>\<circ> S \<circ>\<circ> R) x y"
  moreover with in_dom_le refl_S have "S x x" by blast
  ultimately have "((S \<circ>\<circ> R \<circ>\<circ> S) \<circ>\<circ> R) x y" by blast
  with rel_comp_le have "(S \<circ>\<circ> R \<circ>\<circ> R) x y" by blast
  with trans_R show "(S \<circ>\<circ> R) x y" by blast
qed

lemma rel_comp_comp_le_rel_comp_if_rel_comp_comp_if_in_codom_leI:
  assumes trans_R: "transitive R"
  and refl_S: "reflexive_on P S"
  and in_codom_le: "in_codom (R \<circ>\<circ> S \<circ>\<circ> R) \<le> P"
  and rel_comp_le: "(S \<circ>\<circ> R \<circ>\<circ> S) \<le> (R \<circ>\<circ> S)"
  shows "(R \<circ>\<circ> S \<circ>\<circ> R) \<le> (R \<circ>\<circ> S)"
proof (intro le_relI)
  fix x y assume "(R \<circ>\<circ> S \<circ>\<circ> R) x y"
  moreover with in_codom_le refl_S have "S y y" by blast
  ultimately have "(R \<circ>\<circ> (S \<circ>\<circ> R \<circ>\<circ> S)) x y" by blast
  with rel_comp_le have "(R \<circ>\<circ> R \<circ>\<circ> S) x y" by blast
  with trans_R show "(R \<circ>\<circ> S) x y" by blast
qed

lemma rel_comp_comp_le_rel_comp_if_rel_comp_le_if_transitive:
  assumes trans_R: "transitive R"
  and R_S_le: "(R \<circ>\<circ> S) \<le> (S \<circ>\<circ> R)"
  shows "(R \<circ>\<circ> S \<circ>\<circ> R) \<le> (S \<circ>\<circ> R)"
proof -
  from trans_R have R_R_le: "(R \<circ>\<circ> R) \<le> R" by (intro rel_comp_le_self_if_transitive)
  have "(R \<circ>\<circ> S \<circ>\<circ> R) \<le> (S \<circ>\<circ> R \<circ>\<circ> R)"
    using monoD[OF mono_rel_comp1 R_S_le] by blast
  also have "... \<le> (S \<circ>\<circ> R)"
    using monoD[OF mono_rel_comp2 R_R_le] by (auto simp flip: rel_comp_assoc)
  finally show ?thesis .
qed

lemma rel_comp_comp_le_rel_comp_if_rel_comp_le_if_transitive':
  assumes trans_R: "transitive R"
  and S_R_le: "(S \<circ>\<circ> R) \<le> (R \<circ>\<circ> S)"
  shows "(R \<circ>\<circ> S \<circ>\<circ> R) \<le> (R \<circ>\<circ> S)"
proof -
  from trans_R have R_R_le: "(R \<circ>\<circ> R) \<le> R" by (intro rel_comp_le_self_if_transitive)
  have "(R \<circ>\<circ> S \<circ>\<circ> R) \<le> (R \<circ>\<circ> R \<circ>\<circ> S)"
    using monoD[OF mono_rel_comp2 S_R_le] by (auto simp flip: rel_comp_assoc)
  also have "... \<le> (R \<circ>\<circ> S)" using monoD[OF mono_rel_comp1 R_R_le] by blast
  finally show ?thesis .
qed

lemma rel_comp_eq_rel_comp_if_le_if_transitive_if_reflexive:
  assumes refl_R: "reflexive_on (in_field S) R"
  and trans_S: "transitive S"
  and R_le: "R \<le> S \<squnion> (=)"
  shows "(R \<circ>\<circ> S) = (S \<circ>\<circ> R)"
proof (intro ext iffI)
  fix x y assume "(R \<circ>\<circ> S) x y"
  then obtain z where "R x z" "S z y" by blast
  with R_le have "(S \<squnion> (=)) x z" by blast
  with \<open>S z y\<close> trans_S have "S x y" by auto
  moreover from \<open>S z y\<close> refl_R have "R y y" by blast
  ultimately show "(S \<circ>\<circ> R) x y" by blast
next
  fix x y assume "(S \<circ>\<circ> R) x y"
  then obtain z where "S x z" "R z y" by blast
  with R_le have "(S \<squnion> (=)) z y" by blast
  with \<open>S x z\<close> trans_S have "S x y" by auto
  moreover from \<open>S x y\<close> refl_R have "R x x" by blast
  ultimately show "(R \<circ>\<circ> S) x y" by blast
qed

lemma rel_comp_eq_rel_comp_if_in_field_le_if_le_eq:
  assumes le_eq: "R \<le> (=)"
  and in_field_le: "in_field S \<le> in_field R"
  shows "(R \<circ>\<circ> S) = (S \<circ>\<circ> R)"
proof (intro ext iffI)
  fix x y assume "(R \<circ>\<circ> S) x y"
  then obtain z where "R x z" "S z y" by blast
  with le_eq have "S x y" by blast
  with assms show "(S \<circ>\<circ> R) x y" by blast
next
  fix x y assume "(S \<circ>\<circ> R) x y"
  then obtain z where "S x z" "R z y" by blast
  with le_eq have "S x y" by blast
  with assms show "(R \<circ>\<circ> S) x y" by blast
qed

context transport_comp
begin

lemma left2_right1_left2_le_left2_right1_if_right1_left2_right1_le_left2_right1:
  assumes "reflexive_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  using assms by (intro rel_comp_comp_le_rel_comp_if_rel_comp_comp_if_in_codom_leI)
  auto

lemma left2_right1_left2_le_right1_left2_if_right1_left2_right1_le_right1_left2I:
  assumes "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  using assms by (intro rel_comp_comp_le_rel_comp_if_rel_comp_comp_if_in_dom_leI)
  auto

lemma in_dom_right1_left2_right1_le_if_right1_left2_right1_le:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  shows "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  using monoD[OF mono_in_dom assms] by (auto intro: in_dom_if_in_dom_rel_comp)

lemma in_codom_right1_left2_right1_le_if_right1_left2_right1_le:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  shows "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  using monoD[OF mono_in_codom assms]
  by (auto intro: in_codom_if_in_codom_rel_comp)

text \<open>Our main results will be derivable for two different sets of compatibility
conditions. The next two lemmas show the equivalence between those two sets
under certain assumptions. In cases where these assumptions are met, we will
only state the result for one of the two compatibility conditions. The other one
will then be derivable using one of the following lemmas.\<close>

definition "middle_compatible_dom \<equiv>
  (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)
  \<and> in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)
  \<and> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))
  \<and> in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom (\<le>\<^bsub>R1\<^esub>)"

lemma middle_compatible_domI [intro]:
  assumes "(\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)"
  and "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom (\<le>\<^bsub>R1\<^esub>)"
  shows "middle_compatible_dom"
  unfolding middle_compatible_dom_def using assms by blast

lemma middle_compatible_domE [elim]:
  assumes "middle_compatible_dom"
  obtains "(\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)"
  and "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_dom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_dom (\<le>\<^bsub>R1\<^esub>)"
  using assms unfolding middle_compatible_dom_def by blast

definition "middle_compatible_codom \<equiv>
  ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))
  \<and> in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)
  \<and> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)
  \<and> in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"

lemma middle_compatible_codomI [intro]:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "(\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "middle_compatible_codom"
  unfolding middle_compatible_codom_def using assms by blast

lemma middle_compatible_codomE [elim]:
  assumes "middle_compatible_codom"
  obtains "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "(\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<le> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  using assms unfolding middle_compatible_codom_def by blast

context
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1 .

lemma rel_comp_comp_le_assms_if_in_codom_rel_comp_comp_leI:
  assumes "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_codom"
  shows "middle_compatible_dom"
  using assms by (intro middle_compatible_domI)
  (auto intro!:
    left2_right1_left2_le_left2_right1_if_right1_left2_right1_le_left2_right1
    flip.left2_right1_left2_le_left2_right1_if_right1_left2_right1_le_left2_right1
    in_dom_right1_left2_right1_le_if_right1_left2_right1_le
    flip.in_dom_right1_left2_right1_le_if_right1_left2_right1_le
    intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)

lemma rel_comp_comp_le_assms_if_in_dom_rel_comp_comp_leI:
  assumes "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "middle_compatible_dom"
  shows "middle_compatible_codom"
  using assms by (intro middle_compatible_codomI)
  (auto intro!:
    left2_right1_left2_le_right1_left2_if_right1_left2_right1_le_right1_left2I
    flip.left2_right1_left2_le_right1_left2_if_right1_left2_right1_le_right1_left2I
    in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    flip.in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)

lemma middle_compatible_dom_iff_middle_compatible_codom_if_preorder_on:
  assumes "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  shows "middle_compatible_dom \<longleftrightarrow> middle_compatible_codom"
  using assms by (intro iffI rel_comp_comp_le_assms_if_in_codom_rel_comp_comp_leI)
  (auto intro!: rel_comp_comp_le_assms_if_in_dom_rel_comp_comp_leI)

end

text \<open>Finally we derive some sufficient assumptions for the compatibility
conditions.\<close>

lemma right1_left2_right1_le_assms_if_right1_left2_eqI:
  assumes "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) = ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  shows "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  using assms rel_comp_comp_le_rel_comp_if_rel_comp_le_if_transitive[of R1 L2]
  by auto

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) = ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<equiv> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) = ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  by (simp only: eq_commute)

lemma middle_compatible_codom_if_rel_comp_eq_if_transitive:
  assumes "transitive (\<le>\<^bsub>R1\<^esub>)" "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) = ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  shows "middle_compatible_codom"
  using assms by (intro middle_compatible_codomI
    in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    flip.in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    right1_left2_right1_le_assms_if_right1_left2_eqI
    flip.right1_left2_right1_le_assms_if_right1_left2_eqI)
  auto

lemma middle_compatible_codom_if_right1_le_left2_eqI:
  assumes "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)" "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "(\<le>\<^bsub>R1\<^esub>) \<le> (\<le>\<^bsub>L2\<^esub>) \<squnion> (=)"
  and "in_field (\<le>\<^bsub>L2\<^esub>) \<le> in_field (\<le>\<^bsub>R1\<^esub>)"
  shows "middle_compatible_codom"
  using assms by (intro middle_compatible_codomI
    in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    flip.in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    right1_left2_right1_le_assms_if_right1_left2_eqI
    flip.right1_left2_right1_le_assms_if_right1_left2_eqI
    rel_comp_eq_rel_comp_if_le_if_transitive_if_reflexive)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on)

lemma middle_compatible_codom_if_right1_le_eqI:
  assumes "(\<le>\<^bsub>R1\<^esub>) \<le> (=)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "in_field (\<le>\<^bsub>L2\<^esub>) \<le> in_field (\<le>\<^bsub>R1\<^esub>)"
  shows "middle_compatible_codom"
  using assms by (intro middle_compatible_codomI
    in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    flip.in_codom_right1_left2_right1_le_if_right1_left2_right1_le
    right1_left2_right1_le_assms_if_right1_left2_eqI
    flip.right1_left2_right1_le_assms_if_right1_left2_eqI
    rel_comp_eq_rel_comp_if_in_field_le_if_le_eq)
  auto

end


end
