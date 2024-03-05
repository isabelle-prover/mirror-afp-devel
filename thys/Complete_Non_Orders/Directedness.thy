theory Directedness
  imports Binary_Relations Well_Relations
begin

text \<open>Directed sets:\<close>

locale directed =
  fixes A and less_eq (infix "\<sqsubseteq>" 50)
  assumes pair_bounded: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<exists>z \<in> A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"

lemmas directedI[intro] = directed.intro

lemmas directedD = directed_def[unfolded atomize_eq, THEN iffD1, rule_format]

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma directedE:
  assumes "directed A (\<sqsubseteq>)" and "x \<in> A" and "y \<in> A"
    and "\<And>z. z \<in> A \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto dest: directedD)

lemma directed_empty[simp]: "directed {} (\<sqsubseteq>)" by auto

lemma directed_union:
  assumes dX: "directed X (\<sqsubseteq>)" and dY: "directed Y (\<sqsubseteq>)"
    and XY: "\<forall>x\<in>X. \<forall>y\<in>Y. \<exists>z \<in> X \<union> Y. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  shows "directed (X \<union> Y) (\<sqsubseteq>)"
  using directedD[OF dX] directedD[OF dY] XY
  apply (intro directedI) by blast

lemma directed_extend:
  assumes X: "directed X (\<sqsubseteq>)" and Y: "directed Y (\<sqsubseteq>)" and XY: "\<forall>x\<in>X. \<forall>y\<in>Y. x \<sqsubseteq> y"
  shows "directed (X \<union> Y) (\<sqsubseteq>)"
proof -
  { fix x y
    assume xX: "x \<in> X" and yY: "y \<in> Y"
    let ?g = "\<exists>z\<in>X \<union> Y. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    from directedD[OF Y yY yY] obtain z where zY: "z \<in> Y" and yz: "y \<sqsubseteq> z" by auto
    from xX XY zY yz have ?g by auto
  }
  then show ?thesis by (auto intro!: directed_union[OF X Y])
qed

end

sublocale connex \<subseteq> directed
proof
  fix x y
  assume x: "x \<in> A" and y: "y \<in> A"
  then show "\<exists>z\<in>A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  proof (cases rule: comparable_cases)
    case le
    with refl[OF y] y show ?thesis by (intro bexI[of _ y], auto)
  next
    case ge
    with refl[OF x] x show ?thesis by (intro bexI[of _ x], auto)
  qed
qed

lemmas(in connex) directed = directed_axioms

lemma monotone_directed_image:
  fixes ir (infix "\<preceq>" 50) and r (infix "\<sqsubseteq>" 50)
  assumes mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f" and dir: "directed I (\<preceq>)"
  shows "directed (f ` I) (\<sqsubseteq>)"
proof (rule directedI, safe)
  fix x y assume x: "x \<in> I" and y: "y \<in> I"
  with dir obtain z where z: "z \<in> I" and "x \<preceq> z" and "y \<preceq> z" by (auto elim: directedE)
  with mono x y have "f x \<sqsubseteq> f z" and "f y \<sqsubseteq> f z" by (auto dest: monotone_onD)
  with z show "\<exists>fz \<in> f ` I. f x \<sqsubseteq> fz \<and> f y \<sqsubseteq> fz" by auto
qed


definition "directed_set A (\<sqsubseteq>) \<equiv> \<forall>X \<subseteq> A. finite X \<longrightarrow> (\<exists>b \<in> A. bound X (\<sqsubseteq>) b)"
  for less_eq (infix "\<sqsubseteq>" 50)

lemmas directed_setI = directed_set_def[unfolded atomize_eq, THEN iffD2, rule_format]
lemmas directed_setD = directed_set_def[unfolded atomize_eq, THEN iffD1, rule_format]

lemma directed_imp_nonempty:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  shows "directed_set A (\<sqsubseteq>) \<Longrightarrow> A \<noteq> {}"
  by (auto simp: directed_set_def)

lemma directedD2:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes dir: "directed_set A (\<sqsubseteq>)" and xA: "x \<in> A" and yA: "y \<in> A"
  shows "\<exists>z \<in> A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  using directed_setD[OF dir, of "{x,y}"] xA yA by auto

lemma monotone_directed_set_image:
  fixes ir (infix "\<preceq>" 50) and r (infix "\<sqsubseteq>" 50)
  assumes mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f" and dir: "directed_set I (\<preceq>)"
  shows "directed_set (f ` I) (\<sqsubseteq>)"
proof (rule directed_setI)
  fix X assume "finite X" and "X \<subseteq> f ` I"
  from finite_subset_image[OF this]
  obtain J where JI: "J \<subseteq> I" and Jfin: "finite J" and X: "X = f ` J" by auto
  from directed_setD[OF dir JI Jfin]
  obtain b where bI: "b \<in> I" and Jb: "bound J (\<preceq>) b" by auto
  from monotone_image_bound[OF mono JI bI Jb] bI
  show "Bex (f ` I) (bound X (\<sqsubseteq>))" by (auto simp: X)
qed


lemma directed_set_iff_extremed:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes Dfin: "finite D"
  shows "directed_set D (\<sqsubseteq>) \<longleftrightarrow> extremed D (\<sqsubseteq>)"
proof (intro iffI directed_setI conjI)
  assume "directed_set D (\<sqsubseteq>)"
  from directed_setD[OF this order.refl Dfin]
  show "extremed D (\<sqsubseteq>)" by (auto intro: extremedI)
next
  fix X assume XD: "X \<subseteq> D" and Xfin: "finite X"
  assume "extremed D (\<sqsubseteq>)"
  then obtain b where "b \<in> D" and "extreme D (\<sqsubseteq>) b" by (auto elim!: extremedE)
  with XD show "\<exists>b \<in> D. bound X (\<sqsubseteq>) b" by auto
qed

lemma (in transitive) directed_iff_nonempty_pair_bounded:
  "directed_set A (\<sqsubseteq>) \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>x\<in>A. \<forall>y\<in>A. \<exists>z\<in>A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z)"
  (is "?l \<longleftrightarrow> _ \<and> ?r")
proof (safe intro!: directed_setI del: notI subset_antisym)
  assume dir: ?l
  from directed_imp_nonempty[OF dir] show "A \<noteq> {}".
  fix x y assume "x \<in> A" "y \<in> A"
  with directed_setD[OF dir, of "{x,y}"]
  show "\<exists>z\<in>A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
next
  fix X
  assume A0: "A \<noteq> {}" and r: ?r
  assume "finite X" and "X \<subseteq> A"
  then show "Bex A (bound X (\<sqsubseteq>))"
  proof (induct)
    case empty
    with A0 show ?case by (auto simp: bound_empty ex_in_conv)
  next
    case (insert x X)
    then obtain y where xA: "x \<in> A" and XA: "X \<subseteq> A" and yA: "y \<in> A" and Xy: "bound X (\<sqsubseteq>) y" by auto
    from r yA xA obtain z where zA: "z \<in> A" and xz: "x \<sqsubseteq> z" and yz: "y \<sqsubseteq> z" by auto
    from bound_trans[OF Xy yz XA yA zA] xz zA
    show ?case by auto
  qed
qed

lemma (in transitive) directed_set_iff_nonempty_directed:
  "directed_set A (\<sqsubseteq>) \<longleftrightarrow> A \<noteq> {} \<and> directed A (\<sqsubseteq>)"
  apply (unfold directed_iff_nonempty_pair_bounded)
  by (auto simp: directed_def)

lemma (in well_related_set) finite_sets_extremed:
  assumes fin: "finite X" and X0: "X \<noteq> {}" and XA: "X \<subseteq> A"
  shows "extremed X (\<sqsubseteq>)"
proof-
  interpret less_eq_asymmetrize.
  from fin X0 XA show ?thesis
  proof (induct "card X" arbitrary: X)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    note XA = \<open>X \<subseteq> A\<close> and X0 = \<open>X \<noteq> {}\<close> and Sn = \<open>Suc n = card X\<close> and finX = \<open>finite X\<close>
    note IH = Suc(1)
    from nonempty_imp_ex_extreme[OF XA X0]
    obtain l where l: "extreme X (\<sqsupseteq>) l" by auto
    from l have lX: "l \<in> X" by auto
    with XA have lA: "l \<in> A" by auto
    from Sn lX have n: "n = card (X-{l})" by auto
    show ?case
    proof (cases "X - {l} = {}")
      case True
      with lA lX show ?thesis by (auto intro!: extremedI)
    next
      case False
      from IH[OF n _ this] finX XA
      obtain e where e: "extreme (X - {l}) (\<sqsubseteq>) e" by (auto elim!: extremedE)
      with l show ?thesis by (auto intro!: extremedI[of _ _ e] extremeI)
    qed
  qed
qed

lemma (in well_related_set) directed_set:
  assumes A0: "A \<noteq> {}" shows "directed_set A (\<sqsubseteq>)"
proof (intro directed_setI)
  fix X assume XA: "X \<subseteq> A" and Xfin: "finite X"
  show "Bex A (bound X (\<sqsubseteq>))"
  proof (cases "X = {}")
    case True
    with A0 show ?thesis by (auto simp: bound_empty ex_in_conv)
  next
    case False
    from finite_sets_extremed[OF Xfin this] XA
    show ?thesis by (auto elim!: extremedE)
  qed
qed

lemma prod_directed:
  fixes leA (infix "\<sqsubseteq>\<^sub>A" 50) and leB (infix "\<sqsubseteq>\<^sub>B" 50)
  assumes dir: "directed X (rel_prod (\<sqsubseteq>\<^sub>A) (\<sqsubseteq>\<^sub>B))"
  shows "directed (fst ` X) (\<sqsubseteq>\<^sub>A)" and "directed (snd ` X) (\<sqsubseteq>\<^sub>B)"
proof (safe intro!: directedI)
  fix a b x y assume "(a,x) \<in> X" and "(b,y) \<in> X"
  from directedD[OF dir this]
  obtain c z where cz: "(c,z) \<in> X" and ac: "a \<sqsubseteq>\<^sub>A c" and bc: "b \<sqsubseteq>\<^sub>A c" and "x \<sqsubseteq>\<^sub>B z" and "y \<sqsubseteq>\<^sub>B z" by auto
  then show "\<exists>z\<in>fst ` X. fst (a,x) \<sqsubseteq>\<^sub>A z \<and> fst (b,y) \<sqsubseteq>\<^sub>A z"
    and "\<exists>z\<in>snd ` X. snd (a,x) \<sqsubseteq>\<^sub>B z \<and> snd (b,y) \<sqsubseteq>\<^sub>B z"
    by (auto intro!: bexI[OF _ cz])
qed

class dir = ord + assumes "directed UNIV (\<le>)"
begin

sublocale order: directed UNIV "(\<le>)"
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using dir_axioms[unfolded class.dir_def]
  by (auto simp: atomize_eq)

end

class filt = ord +
  assumes "directed UNIV (\<ge>)"
begin

sublocale order.dual: directed UNIV "(\<ge>)"
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using filt_axioms[unfolded class.filt_def]
  by (auto simp: atomize_eq)

end

subclass (in linqorder) dir..

subclass (in linqorder) filt..

thm order.directed_axioms[where 'a = "'a ::dir"]

thm order.dual.directed_axioms[where 'a = "'a ::filt"]

end