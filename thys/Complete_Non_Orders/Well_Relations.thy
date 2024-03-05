theory Well_Relations
  imports Binary_Relations
begin

section \<open>Well-Relations\<close>

text \<open>
A related set $\tp{A,\SLE}$ is called \emph{topped} if there is a ``top'' element $\top \in A$,
a greatest element in $A$.
Note that there might be multiple tops if $(\SLE)$ is not antisymmetric.\<close>

definition "extremed A r \<equiv> \<exists>e. extreme A r e"

lemma extremedI: "extreme A r e \<Longrightarrow> extremed A r"
  by (auto simp: extremed_def)

lemma extremedE: "extremed A r \<Longrightarrow> (\<And>e. extreme A r e \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: extremed_def)

lemma extremed_imp_ex_bound: "extremed A r \<Longrightarrow> X \<subseteq> A \<Longrightarrow> \<exists>b \<in> A. bound X r b"
  by (auto simp: extremed_def)

locale well_founded = related_set _ "(\<sqsubset>)" + less_syntax +
  assumes induct[consumes 1, case_names less, induct set]:
    "a \<in> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
begin

sublocale asymmetric
proof (intro asymmetric.intro notI)
  fix x y
  assume xA: "x \<in> A"
  then show "y \<in> A \<Longrightarrow> x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
    by (induct arbitrary: y rule: induct, auto)
qed

lemma prefixed_Imagep_imp_empty:
  assumes a: "X \<subseteq> ((\<sqsubset>) ``` X) \<inter> A" shows "X = {}"
proof -
  from a have XA: "X \<subseteq> A" by auto
  have "x \<in> A \<Longrightarrow> x \<notin> X" for x
  proof (induct x rule: induct)
    case (less x)
    with a show ?case by (auto simp: Imagep_def)
  qed
  with XA show ?thesis by auto
qed

lemma nonempty_imp_ex_extremal:
  assumes QA: "Q \<subseteq> A" and Q: "Q \<noteq> {}"
  shows "\<exists>z \<in> Q. \<forall>y \<in> Q. \<not> y \<sqsubset> z"
  using Q prefixed_Imagep_imp_empty[of Q] QA by (auto simp: Imagep_def)

interpretation Restrp: well_founded UNIV "(\<sqsubset>)\<restriction>A"
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "(\<sqsubset>)\<restriction>A\<restriction>UNIV = (\<sqsubset>)\<restriction>A"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
proof -
  have "(\<And>x. (\<And>y. ((\<sqsubset>) \<restriction> A) y x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a" for a P
    using induct[of a P] by (auto simp: Restrp_def)
  then show "well_founded UNIV ((\<sqsubset>)\<restriction>A)" apply unfold_locales by auto
qed auto

lemmas Restrp_well_founded = Restrp.well_founded_axioms
lemmas Restrp_induct[consumes 0, case_names less] = Restrp.induct

interpretation Restrp.tranclp: well_founded UNIV "((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ \<restriction> UNIV = ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
    and "(((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+)\<^sup>+\<^sup>+ = ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
proof-
  { fix P x
    assume induct_step: "\<And>x. (\<And>y. ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ y x \<Longrightarrow> P y) \<Longrightarrow> P x"
    have "P x"
    proof (rule induct_step)
      show "\<And>y. ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ y x \<Longrightarrow> P y"
      proof (induct x rule: Restrp_induct)
        case (less x)
        from \<open>((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ y x\<close>
        show ?case
        proof (cases rule: tranclp.cases)
          case r_into_trancl
          with induct_step less show ?thesis by auto
        next
          case (trancl_into_trancl b)
          with less show ?thesis by auto
        qed
      qed
    qed
  }
  then show "well_founded UNIV ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+" by unfold_locales auto
qed auto

lemmas Restrp_tranclp_well_founded = Restrp.tranclp.well_founded_axioms
lemmas Restrp_tranclp_induct[consumes 0, case_names less] = Restrp.tranclp.induct

end

context
  fixes A :: "'a set" and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
begin

lemma well_foundedI_pf:
  assumes pre: "\<And>X. X \<subseteq> A \<Longrightarrow> X \<subseteq> ((\<sqsubset>) ``` X) \<inter> A \<Longrightarrow> X = {}"
  shows "well_founded A (\<sqsubset>)"
proof
  fix P a assume aA: "a \<in> A" and Ind: "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> P y) \<Longrightarrow> P x"
  from Ind have "{a\<in>A. \<not>P a} \<subseteq> ((\<sqsubset>) ``` {a\<in>A. \<not>P a}) \<inter> A" by (auto simp: Imagep_def)
  from pre[OF _ this] aA
  show "P a" by auto
qed

lemma well_foundedI_extremal:
  assumes a: "\<And>X. X \<subseteq> A \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x \<in> X. \<forall>y \<in> X. \<not> y \<sqsubset> x"
  shows "well_founded A (\<sqsubset>)"
proof (rule well_foundedI_pf)
  fix X assume XA: "X \<subseteq> A" and pf: "X \<subseteq> ((\<sqsubset>) ``` X) \<inter> A"
  from a[OF XA] pf show "X = {}" by (auto simp: Imagep_def)
qed

lemma well_founded_iff_ex_extremal:
  "well_founded A (\<sqsubset>) \<longleftrightarrow> (\<forall>X \<subseteq> A. X \<noteq> {} \<longrightarrow> (\<exists>x \<in> X. \<forall>z \<in> X. \<not> z \<sqsubset> x))"
  using well_founded.nonempty_imp_ex_extremal well_foundedI_extremal by blast

end

lemma well_founded_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
    and A: "\<And>a b. r' a b \<Longrightarrow> a \<in> A \<longleftrightarrow> a \<in> A'"
    and B: "\<And>a b. r' a b \<Longrightarrow> b \<in> A \<longleftrightarrow> b \<in> A'"
  shows "well_founded A r \<longleftrightarrow> well_founded A' r'"
proof (intro iffI)
  assume wf: "well_founded A r"
  show "well_founded A' r'"
  proof (intro well_foundedI_extremal)
    fix X
    assume X: "X \<subseteq> A'" and X0: "X \<noteq> {}"
    show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r' y x"
    proof (cases "X \<inter> A = {}")
      case True
      from X0 obtain x where xX: "x \<in> X" by auto
      with True have "x \<notin> A" by auto
      with xX X have "\<forall>y\<in>X. \<not> r' y x" by (auto simp: B)
      with xX show ?thesis by auto
    next
      case False
      from well_founded.nonempty_imp_ex_extremal[OF wf _ this]
      obtain x where x: "x \<in> X \<inter> A" and Ar: "\<And>y. y \<in> X \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> r y x" by auto
      have "\<forall>y \<in> X. \<not> r' y x"
      proof (intro ballI notI)
        fix y assume yX: "y \<in> X" and yx: "r' y x"
        from yX X have yA': "y \<in> A'" by auto
        show False
        proof (cases "y \<in> A")
          case True with x Ar[OF yX] yx r show ?thesis by auto
        next
          case False with yA' x A[OF yx] r X show ?thesis by (auto simp:)
        qed
      qed
      with x show "\<exists>x \<in> X. \<forall>y \<in> X. \<not> r' y x" by auto
    qed
  qed
next
  assume wf: "well_founded A' r'"
  show "well_founded A r"
  proof (intro well_foundedI_extremal)
    fix X
    assume X: "X \<subseteq> A" and X0: "X \<noteq> {}"
    show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r y x"
    proof (cases "X \<inter> A' = {}")
      case True
      from X0 obtain x where xX: "x \<in> X" by auto
      with True have "x \<notin> A'" by auto
      with xX X B have "\<forall>y\<in>X. \<not> r y x" by (auto simp: r in_mono)
      with xX show ?thesis by auto
    next
      case False
      from well_founded.nonempty_imp_ex_extremal[OF wf _ this]
      obtain x where x: "x \<in> X \<inter> A'" and Ar: "\<And>y. y \<in> X \<Longrightarrow> y \<in> A' \<Longrightarrow> \<not> r' y x" by auto
      have "\<forall>y \<in> X. \<not> r y x"
      proof (intro ballI notI)
        fix y assume yX: "y \<in> X" and yx: "r y x"
        from yX X have y: "y \<in> A" by auto
        show False
        proof (cases "y \<in> A'")
          case True with x Ar[OF yX] yx r X y show ?thesis by auto
        next
          case False with y x A yx r X show ?thesis by auto
        qed
      qed
      with x show "\<exists>x \<in> X. \<forall>y \<in> X. \<not> r y x" by auto
    qed
  qed
qed

lemma wfP_iff_well_founded_UNIV: "wfP r \<longleftrightarrow> well_founded UNIV r"
  by (auto simp: wfP_def wf_def well_founded_def)

lemma well_founded_empty[intro!]: "well_founded {} r"
  by (auto simp: well_founded_iff_ex_extremal)

lemma well_founded_singleton:
  assumes "\<not>r x x" shows "well_founded {x} r"
  using assms by (auto simp: well_founded_iff_ex_extremal)

lemma well_founded_Restrp[simp]: "well_founded A (r\<restriction>B) \<longleftrightarrow> well_founded (A\<inter>B) r" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI well_foundedI_extremal)
  assume l: ?l
  fix X assume XAB: "X \<subseteq> A \<inter> B" and X0: "X \<noteq> {}"
  with l[THEN well_founded.nonempty_imp_ex_extremal]
  have "\<exists>x\<in>X. \<forall>z\<in>X. \<not> (r \<restriction> B) z x" by auto
  with XAB show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r y x" by (auto simp: Restrp_def)
next
  assume r: ?r
  fix X assume XA: "X \<subseteq> A" and X0: "X \<noteq> {}"
  show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> (r \<restriction> B) y x"
  proof (cases "X \<subseteq> B")
    case True
    with r[THEN well_founded.nonempty_imp_ex_extremal, of X] XA X0
    have "\<exists>z\<in>X. \<forall>y\<in>X. \<not> r y z" by auto
    then show ?thesis by auto
  next
    case False
    then obtain x where x: "x \<in> X - B" by auto
    then have "\<forall>y\<in>X. \<not> (r \<restriction> B) y x" by auto
    with x show ?thesis by auto
  qed
qed

lemma Restrp_tranclp_well_founded_iff:
  fixes less (infix "\<sqsubset>" 50)
  shows "well_founded UNIV ((\<sqsubset>) \<restriction> A)\<^sup>+\<^sup>+ \<longleftrightarrow> well_founded A (\<sqsubset>)" (is "?l \<longleftrightarrow> ?r")
proof (rule iffI)
  show "?r \<Longrightarrow> ?l" by (fact well_founded.Restrp_tranclp_well_founded)
  assume ?l
  then interpret well_founded UNIV "((\<sqsubset>) \<restriction> A)\<^sup>+\<^sup>+".
  show ?r
  proof (unfold well_founded_iff_ex_extremal, intro allI impI)
    fix X assume XA: "X \<subseteq> A" and X0: "X \<noteq> {}"
    from nonempty_imp_ex_extremal[OF _ X0]
    obtain z where zX: "z \<in> X" and Xz: "\<forall>y\<in>X. \<not> ((\<sqsubset>) \<restriction> A)\<^sup>+\<^sup>+ y z" by auto
    show "\<exists>z \<in> X. \<forall>y \<in> X. \<not> y \<sqsubset> z"
    proof (intro bexI[OF _ zX] ballI notI)
      fix y assume yX: "y \<in> X" and yz: "y \<sqsubset> z"
      from yX yz zX XA have "((\<sqsubset>) \<restriction> A) y z" by auto
      with yX Xz show False by auto
    qed
  qed
qed

lemma (in well_founded) well_founded_subset:
  assumes "B \<subseteq> A" shows "well_founded B (\<sqsubset>)"
  using assms well_founded_axioms by (auto simp: well_founded_iff_ex_extremal)

lemma well_founded_extend:
  fixes less (infix "\<sqsubset>" 50)
  assumes A: "well_founded A (\<sqsubset>)"
  assumes B: "well_founded B (\<sqsubset>)"
  assumes AB: "\<forall>a \<in> A. \<forall>b \<in> B. \<not>b \<sqsubset> a"
  shows "well_founded (A \<union> B) (\<sqsubset>)"
proof (intro well_foundedI_extremal)
  interpret A: well_founded A "(\<sqsubset>)" using A.
  interpret B: well_founded B "(\<sqsubset>)" using B.
  fix X assume XAB: "X \<subseteq> A \<union> B" and X0: "X \<noteq> {}"
  show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> y \<sqsubset> x"
  proof (cases "X \<inter> A = {}")
    case True
    with XAB have XB: "X \<subseteq> B" by auto
    from B.nonempty_imp_ex_extremal[OF XB X0] show ?thesis.
  next
    case False
    with A.nonempty_imp_ex_extremal[OF _ this]
    obtain e where XAe: "e \<in> X \<inter> A" "\<forall>y\<in>X \<inter> A. \<not> y \<sqsubset> e" by auto
    then have eX: "e \<in> X" and eA: "e \<in> A" by auto
    { fix x assume xX: "x \<in> X"
      have "\<not>x \<sqsubset> e"
      proof (cases "x \<in> A")
        case True with XAe xX show ?thesis by auto
      next
        case False
        with xX XAB have "x \<in> B" by auto
        with AB eA show ?thesis by auto
      qed
    }
    with eX show ?thesis by auto
  qed
qed

lemma closed_UN_well_founded:
  fixes r (infix "\<sqsubset>" 50)
  assumes XX: "\<forall>X\<in>XX. well_founded X (\<sqsubset>) \<and> (\<forall>x\<in>X. \<forall>y\<in>\<Union>XX. y \<sqsubset> x \<longrightarrow> y \<in> X)"
  shows "well_founded (\<Union>XX) (\<sqsubset>)"
proof (intro well_foundedI_extremal)
  have *: "X \<in> XX \<Longrightarrow> x\<in>X \<Longrightarrow> y \<in> \<Union>XX \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> y \<in> X" for X x y using XX by blast
  fix S
  assume S: "S \<subseteq> \<Union>XX" and S0: "S \<noteq> {}"
  from S0 obtain x where xS: "x \<in> S" by auto
  with S obtain X where X: "X \<in> XX" and xX: "x \<in> X" by auto
  from xS xX have Sx0: "S \<inter> X \<noteq> {}" by auto
  from X XX interpret well_founded X "(\<sqsubset>)" by auto
  from nonempty_imp_ex_extremal[OF _ Sx0]
  obtain z where zS: "z \<in> S" and zX: "z \<in> X" and min: "\<forall>y \<in> S \<inter> X. \<not> y \<sqsubset> z" by auto
  show "\<exists>x\<in>S. \<forall>y\<in>S. \<not> y \<sqsubset> x"
  proof (intro bexI[OF _ zS] ballI notI)
    fix y
    assume yS: "y \<in> S" and yz: "y \<sqsubset> z"
    have yXX: "y \<in> \<Union> XX" using S yS by auto
    from *[OF X zX yXX yz] yS have "y \<in> X \<inter> S" by auto
    with min yz show False by auto
  qed
qed

lemma well_founded_cmono:
  assumes r': "r' \<le> r" and wf: "well_founded A r"
  shows "well_founded A r'"
proof (intro well_foundedI_extremal)
  fix X assume "X \<subseteq> A" and "X \<noteq> {}"
  from well_founded.nonempty_imp_ex_extremal[OF wf this]
  show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r' y x" using r' by auto
qed

locale well_founded_ordered_set = well_founded + transitive _ "(\<sqsubset>)"
begin

sublocale strict_ordered_set..

interpretation Restrp: strict_ordered_set UNIV "(\<sqsubset>)\<restriction>A" + Restrp: well_founded UNIV "(\<sqsubset>)\<restriction>A"
  using Restrp_strict_order Restrp_well_founded .

lemma Restrp_well_founded_order: "well_founded_ordered_set UNIV ((\<sqsubset>)\<restriction>A)"..

lemma well_founded_ordered_subset: "B \<subseteq> A \<Longrightarrow> well_founded_ordered_set B (\<sqsubset>)"
  apply intro_locales
  using well_founded_subset transitive_subset by auto

end

lemmas well_founded_ordered_setI = well_founded_ordered_set.intro

lemma well_founded_ordered_set_empty[intro!]: "well_founded_ordered_set {} r"
  by (auto intro!: well_founded_ordered_setI)


locale well_related_set = related_set +
  assumes nonempty_imp_ex_extreme: "X \<subseteq> A \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>e. extreme X (\<sqsubseteq>)\<^sup>- e"
begin

sublocale connex
proof
  fix x y assume "x \<in> A" and "y \<in> A"
  with nonempty_imp_ex_extreme[of "{x,y}"] show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by auto 
qed

lemmas connex = connex_axioms(* I'd like to access well_related_set.connex_axioms,
  but it's not visible without interpretation. *)

interpretation less_eq_asymmetrize.

sublocale asym: well_founded A "(\<sqsubset>)"
proof (unfold well_founded_iff_ex_extremal, intro allI impI)
  fix X
  assume XA: "X \<subseteq> A" and X0: "X \<noteq> {}"
  from nonempty_imp_ex_extreme[OF XA X0] obtain e where "extreme X (\<sqsubseteq>)\<^sup>- e" by auto
  then show "\<exists>x\<in>X. \<forall>z\<in>X. \<not>z \<sqsubset> x" by (auto intro!: bexI[of _ e])
qed

lemma well_related_subset: "B \<subseteq> A \<Longrightarrow> well_related_set B (\<sqsubseteq>)"
  by (auto intro!: well_related_set.intro nonempty_imp_ex_extreme)

lemma monotone_image_well_related:
  fixes leB (infix "\<unlhd>" 50)
  assumes mono: "monotone_on A (\<sqsubseteq>) (\<unlhd>) f" shows "well_related_set (f ` A) (\<unlhd>)"
proof (intro well_related_set.intro)
  interpret less_eq_dualize.
  fix X' assume X'fA: "X' \<subseteq> f ` A" and X'0: "X' \<noteq> {}"
  then obtain X where XA: "X \<subseteq> A" and X': "X' = f ` X" and X0: "X \<noteq> {}"
    by (auto elim!: subset_imageE)
  from nonempty_imp_ex_extreme[OF XA X0]
  obtain e where Xe: "extreme X (\<sqsupseteq>) e" by auto
  note monotone_on_subset[OF mono XA]
  note monotone_on_dual[OF this]
  from monotone_image_extreme[OF this Xe]
  show "\<exists>e'. extreme X' (\<unlhd>)\<^sup>- e'" by (auto simp: X')
qed

end

sublocale well_related_set \<subseteq> reflexive using local.reflexive_axioms.

lemmas well_related_setI = well_related_set.intro

lemmas well_related_iff_ex_extreme = well_related_set_def

lemma well_related_set_empty[intro!]: "well_related_set {} r"
  by (auto intro!: well_related_setI)

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma well_related_iff_neg_well_founded:
  "well_related_set A (\<sqsubseteq>) \<longleftrightarrow> well_founded A (\<lambda>x y. \<not> y \<sqsubseteq> x)"
  by (simp add: well_related_set_def well_founded_iff_ex_extremal extreme_def Bex_def)

lemma well_related_singleton_refl: 
  assumes "x \<sqsubseteq> x" shows "well_related_set {x} (\<sqsubseteq>)"
  by (intro well_related_set.intro exI[of _ x], auto simp: subset_singleton_iff assms)

lemma closed_UN_well_related:
  assumes XX: "\<forall>X\<in>XX. well_related_set X (\<sqsubseteq>) \<and> (\<forall>x\<in>X. \<forall>y\<in>\<Union>XX. \<not>x \<sqsubseteq> y \<longrightarrow> y \<in> X)"
  shows "well_related_set (\<Union>XX) (\<sqsubseteq>)"
  using XX
  apply (unfold well_related_iff_neg_well_founded)
  using closed_UN_well_founded[of _ "\<lambda>x y. \<not> y \<sqsubseteq> x"].

end

lemma well_related_extend:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes "well_related_set A (\<sqsubseteq>)" and "well_related_set B (\<sqsubseteq>)" and "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b"
  shows "well_related_set (A \<union> B) (\<sqsubseteq>)"
  using well_founded_extend[of _ "\<lambda>x y. \<not> y \<sqsubseteq> x", folded well_related_iff_neg_well_founded]
  using assms by auto

lemma pair_well_related:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes "i \<sqsubseteq> i" and "i \<sqsubseteq> j" and "j \<sqsubseteq> j"
  shows "well_related_set {i, j} (\<sqsubseteq>)"
proof (intro well_related_setI)
  fix X assume "X \<subseteq> {i,j}" and "X \<noteq> {}"
  then have "X = {i,j} \<or> X = {i} \<or> X = {j}" by auto
  with assms show "\<exists>e. extreme X (\<sqsubseteq>)\<^sup>- e" by auto
qed

locale pre_well_ordered_set = semiattractive + well_related_set
begin

interpretation less_eq_asymmetrize.

sublocale transitive
proof
  fix x y z assume xy: "x \<sqsubseteq> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  from x y z have "\<exists>e. extreme {x,y,z} (\<sqsupseteq>) e" (is "\<exists>e. ?P e") by (auto intro!: nonempty_imp_ex_extreme)
  then have "?P x \<or> ?P y \<or> ?P z" by auto
  then show "x \<sqsubseteq> z"
  proof (elim disjE)
    assume "?P x"
    then show ?thesis by auto
  next
    assume "?P y"
    then have "y \<sqsubseteq> x" by auto
    from attract[OF xy this yz] x y z show ?thesis by auto
  next
    assume "?P z"
    then have zx: "z \<sqsubseteq> x" and zy: "z \<sqsubseteq> y" by auto
    from attract[OF yz zy zx] x y z have yx: "y \<sqsubseteq> x" by auto
    from attract[OF xy yx yz] x y z show ?thesis by auto
  qed
qed

sublocale total_quasi_ordered_set..

end

lemmas pre_well_ordered_iff_semiattractive_well_related =
  pre_well_ordered_set_def[unfolded atomize_eq]

lemma pre_well_ordered_set_empty[intro!]: "pre_well_ordered_set {} r"
  by (auto simp: pre_well_ordered_iff_semiattractive_well_related)

lemma pre_well_ordered_iff:
  "pre_well_ordered_set A r \<longleftrightarrow> total_quasi_ordered_set A r \<and> well_founded A (asympartp r)"
  (is "?p \<longleftrightarrow> ?t \<and> ?w")
proof safe
  assume ?p
  then interpret pre_well_ordered_set A r.
  show ?t ?w by unfold_locales
next
  assume ?t
  then interpret total_quasi_ordered_set A r.
  assume ?w
  then have "well_founded UNIV (asympartp r \<restriction> A)" by simp
  also have "asympartp r \<restriction> A = (\<lambda>x y. \<not> r y x) \<restriction> A" by (intro ext, auto simp: not_iff_asym)
  finally have "well_related_set A r" by (simp add: well_related_iff_neg_well_founded)
  then show ?p by intro_locales
qed

lemma (in semiattractive) pre_well_ordered_iff_well_related:
  assumes XA: "X \<subseteq> A"
  shows "pre_well_ordered_set X (\<sqsubseteq>) \<longleftrightarrow> well_related_set X (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  interpret X: semiattractive X using semiattractive_subset[OF XA].
  { assume ?l
    then interpret X: pre_well_ordered_set X.
    show ?r by unfold_locales
  }
  assume ?r
  then interpret X: well_related_set X.
  show ?l by unfold_locales
qed

lemma semiattractive_extend:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes A: "semiattractive A (\<sqsubseteq>)" and B: "semiattractive B (\<sqsubseteq>)"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<and> \<not> b \<sqsubseteq> a"
  shows "semiattractive (A \<union> B) (\<sqsubseteq>)"
proof-
  interpret A: semiattractive A "(\<sqsubseteq>)" using A.
  interpret B: semiattractive B "(\<sqsubseteq>)" using B.
  {
    fix x y z
    assume yB: "y \<in> B" and zA: "z \<in> A" and yz: "y \<sqsubseteq> z"
    have False using AB[rule_format, OF zA yB] yz by auto
  }
  note * = this
  show ?thesis 
    by (auto intro!: semiattractive.intro dest:* AB[rule_format] A.attract B.attract)
qed

lemma pre_well_order_extend:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes A: "pre_well_ordered_set A (\<sqsubseteq>)" and B: "pre_well_ordered_set B (\<sqsubseteq>)"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<and> \<not> b \<sqsubseteq> a"
  shows "pre_well_ordered_set (A\<union>B) (\<sqsubseteq>)"
proof-
  interpret A: pre_well_ordered_set A "(\<sqsubseteq>)" using A.
  interpret B: pre_well_ordered_set B "(\<sqsubseteq>)" using B.
  show ?thesis
    apply (intro pre_well_ordered_set.intro well_related_extend semiattractive_extend)
    apply unfold_locales
    by (auto dest: AB[rule_format])
qed

lemma (in well_related_set) monotone_image_pre_well_ordered:
  fixes leB (infix "\<sqsubseteq>''" 50)
  assumes mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>') f"
    and image: "semiattractive (f ` A) (\<sqsubseteq>')"
  shows "pre_well_ordered_set (f ` A) (\<sqsubseteq>')"
  by (intro pre_well_ordered_set.intro monotone_image_well_related[OF mono] image)

locale well_ordered_set = antisymmetric + well_related_set
begin

sublocale pre_well_ordered_set..

sublocale total_ordered_set..

lemma well_ordered_subset: "B \<subseteq> A \<Longrightarrow> well_ordered_set B (\<sqsubseteq>)"
  using well_related_subset antisymmetric_subset by (intro well_ordered_set.intro)

sublocale asym: well_founded_ordered_set A "asympartp (\<sqsubseteq>)"
  by (intro well_founded_ordered_set.intro asym.well_founded_axioms asympartp_transitive)

end

lemmas well_ordered_iff_antisymmetric_well_related = well_ordered_set_def[unfolded atomize_eq]

lemma well_ordered_set_empty[intro!]: "well_ordered_set {} r"
  by (auto simp: well_ordered_iff_antisymmetric_well_related)

lemma (in antisymmetric) well_ordered_iff_well_related:
  assumes XA: "X \<subseteq> A"
  shows "well_ordered_set X (\<sqsubseteq>) \<longleftrightarrow> well_related_set X (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  interpret X: antisymmetric X using antisymmetric_subset[OF XA].
  { assume ?l
    then interpret X: well_ordered_set X.
    show ?r by unfold_locales
  }
  assume ?r
  then interpret X: well_related_set X.
  show ?l by unfold_locales
qed

context
  fixes A :: "'a set" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

context
  assumes A: "\<forall>a \<in> A. \<forall>b \<in> A. a \<sqsubseteq> b"
begin

interpretation well_related_set A "(\<sqsubseteq>)"
  apply unfold_locales
  using A by blast

lemmas trivial_well_related = well_related_set_axioms

lemma trivial_pre_well_order: "pre_well_ordered_set A (\<sqsubseteq>)"
  apply unfold_locales
  using A by blast

end

interpretation less_eq_asymmetrize.

lemma well_ordered_iff_well_founded_total_ordered:
  "well_ordered_set A (\<sqsubseteq>) \<longleftrightarrow> total_ordered_set A (\<sqsubseteq>) \<and> well_founded A (\<sqsubset>)"
proof (safe)
  assume "well_ordered_set A (\<sqsubseteq>)"
  then interpret well_ordered_set A "(\<sqsubseteq>)".
  show "total_ordered_set A (\<sqsubseteq>)" "well_founded A (\<sqsubset>)" by unfold_locales
next
  assume "total_ordered_set A (\<sqsubseteq>)" and "well_founded A (\<sqsubset>)"
  then interpret total_ordered_set A "(\<sqsubseteq>)" + asympartp: well_founded A "(\<sqsubset>)".
  show "well_ordered_set A (\<sqsubseteq>)"
  proof
    fix X assume XA: "X \<subseteq> A" and "X \<noteq> {}"
    from XA asympartp.nonempty_imp_ex_extremal[OF this] 
    show "\<exists>e. extreme X (\<sqsupseteq>) e" by (auto simp: not_asym_iff subsetD)
  qed
qed

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma well_order_extend:
  assumes A: "well_ordered_set A (\<sqsubseteq>)" and B: "well_ordered_set B (\<sqsubseteq>)"
    and ABa: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<longrightarrow> b \<sqsubseteq> a \<longrightarrow> a = b"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b"
  shows "well_ordered_set (A\<union>B) (\<sqsubseteq>)"
proof-
  interpret A: well_ordered_set A "(\<sqsubseteq>)" using A.
  interpret B: well_ordered_set B "(\<sqsubseteq>)" using B.
  show ?thesis
    apply (intro well_ordered_set.intro antisymmetric_union well_related_extend ABa AB)
    by unfold_locales
qed

interpretation singleton: antisymmetric "{a}" "(\<sqsubseteq>)" for a apply unfold_locales by auto

lemmas singleton_antisymmetric[intro!] = singleton.antisymmetric_axioms

lemma singleton_well_ordered[intro!]: "a \<sqsubseteq> a \<Longrightarrow> well_ordered_set {a} (\<sqsubseteq>)"
  apply unfold_locales by auto

lemma closed_UN_well_ordered:
  assumes anti: "antisymmetric (\<Union> XX) (\<sqsubseteq>)"
    and XX: "\<forall>X\<in>XX. well_ordered_set X (\<sqsubseteq>) \<and> (\<forall>x\<in>X. \<forall>y\<in>\<Union>XX. \<not> x \<sqsubseteq> y \<longrightarrow> y \<in> X)"
  shows "well_ordered_set (\<Union>XX) (\<sqsubseteq>)"
  apply (intro well_ordered_set.intro closed_UN_well_related anti)
  using XX well_ordered_set.axioms by fast

end

lemma (in well_related_set) monotone_image_well_ordered:
  fixes leB (infix "\<sqsubseteq>''" 50)
  assumes mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>') f"
    and image: "antisymmetric (f ` A) (\<sqsubseteq>')"
  shows "well_ordered_set (f ` A) (\<sqsubseteq>')"
  by (intro well_ordered_set.intro monotone_image_well_related[OF mono] image)


subsection \<open>Relating to Classes\<close>

locale well_founded_quasi_ordering = quasi_ordering + well_founded
begin

lemma well_founded_quasi_ordering_subset:
  assumes "X \<subseteq> A" shows "well_founded_quasi_ordering X (\<sqsubseteq>) (\<sqsubset>)"
  by (intro well_founded_quasi_ordering.intro quasi_ordering_subset well_founded_subset assms)

end

class wf_qorder = ord +
  assumes "well_founded_quasi_ordering UNIV (\<le>) (<)"
begin

interpretation well_founded_quasi_ordering UNIV
  using wf_qorder_axioms unfolding class.wf_qorder_def by auto

subclass qorder ..

sublocale order: well_founded_quasi_ordering UNIV
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
  apply unfold_locales by (auto simp:atomize_eq)

end

context wellorder begin

subclass wf_qorder
  apply (unfold_locales)
  using less_induct by auto

sublocale order: well_ordered_set UNIV
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
  apply (unfold well_ordered_iff_well_founded_total_ordered)
  apply (intro conjI order.total_ordered_set_axioms)
  by (auto simp: order.well_founded_axioms atomize_eq)

end

thm order.nonempty_imp_ex_extreme

subsection \<open>omega-Chains\<close>

definition "omega_chain A r \<equiv> \<exists>f :: nat \<Rightarrow> 'a. monotone (\<le>) r f \<and> range f = A"

lemma omega_chainI:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "monotone (\<le>) r f" "range f = A" shows "omega_chain A r"
  using assms by (auto simp: omega_chain_def)

lemma omega_chainE:
  assumes "omega_chain A r"
    and "\<And>f :: nat \<Rightarrow> 'a. monotone (\<le>) r f \<Longrightarrow> range f = A \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: omega_chain_def)

lemma (in transitive) local_chain:
  assumes CA: "range C \<subseteq> A"
  shows "(\<forall>i::nat. C i \<sqsubseteq> C (Suc i)) \<longleftrightarrow> monotone (<) (\<sqsubseteq>) C"
proof (intro iffI allI monotoneI)
  fix i j :: nat
  assume loc: "\<forall>i. C i \<sqsubseteq> C (Suc i)" and ij: "i < j"
  have "C i \<sqsubseteq> C (i+k+1)" for k
  proof (induct k)
    case 0
    from loc show ?case by auto
  next
    case (Suc k)
    also have "C (i+k+1) \<sqsubseteq> C (i+k+Suc 1)" using loc by auto
    finally show ?case using CA by auto
  qed
  from this[of "j-i-1"] ij show "C i \<sqsubseteq> C j" by auto
next
  fix i
  assume "monotone (<) (\<sqsubseteq>) C"
  then show "C i \<sqsubseteq> C (Suc i)" by (auto dest: monotoneD)
qed

lemma pair_omega_chain:
  assumes "r a a" "r b b" "r a b" shows "omega_chain {a,b} r"
  using assms by (auto intro!: omega_chainI[of r "\<lambda>i. if i = 0 then a else b"] monotoneI)

text \<open>Every omega-chain is a well-order.\<close>

lemma omega_chain_imp_well_related:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes A: "omega_chain A (\<sqsubseteq>)" shows "well_related_set A (\<sqsubseteq>)"
proof
  interpret less_eq_dualize.
  from A obtain f :: "nat \<Rightarrow> 'a" where mono: "monotone_on UNIV (\<le>) (\<sqsubseteq>) f" and A: "A = range f"
    by (auto elim!: omega_chainE)
  fix X assume XA: "X \<subseteq> A" and "X \<noteq> {}"
  then obtain I where X: "X = f ` I" and I0: "I \<noteq> {}" by (auto simp: A subset_image_iff)
  from order.nonempty_imp_ex_extreme[OF I0]
  obtain i where "least I i" by auto
  with mono 
  show "\<exists>e. extreme X (\<sqsupseteq>) e" by (auto intro!: exI[of _ "f i"] extremeI simp: X monotoneD)
qed

lemma (in semiattractive) omega_chain_imp_pre_well_ordered:
  assumes "omega_chain A (\<sqsubseteq>)" shows "pre_well_ordered_set A (\<sqsubseteq>)"
  apply (intro pre_well_ordered_set.intro omega_chain_imp_well_related assms)..

lemma (in antisymmetric) omega_chain_imp_well_ordered:
  assumes "omega_chain A (\<sqsubseteq>)" shows "well_ordered_set A (\<sqsubseteq>)"
  by (intro well_ordered_set.intro omega_chain_imp_well_related assms antisymmetric_axioms)

subsubsection \<open>Relation image that preserves well-orderedness.\<close>

definition "well_image f A (\<sqsubseteq>) fa fb \<equiv>
  \<forall>a b. extreme {x\<in>A. fa = f x} (\<sqsubseteq>)\<^sup>- a \<longrightarrow> extreme {y\<in>A. fb = f y} (\<sqsubseteq>)\<^sup>- b \<longrightarrow> a \<sqsubseteq> b"
  for less_eq (infix "\<sqsubseteq>" 50)

lemmas well_imageI = well_image_def[unfolded atomize_eq, THEN iffD2, rule_format]
lemmas well_imageD = well_image_def[unfolded atomize_eq, THEN iffD1, rule_format]

lemma (in pre_well_ordered_set)
  well_image_well_related: "pre_well_ordered_set (f`A) (well_image f A (\<sqsubseteq>))"
proof-
  interpret less_eq_dualize.
  interpret im: transitive "f`A" "well_image f A (\<sqsubseteq>)"
  proof (safe intro!: transitiveI well_imageI)
    interpret less_eq_dualize.
    fix x y z a c
    assume fxfy: "well_image f A (\<sqsubseteq>) (f x) (f y)"
      and fyfz: "well_image f A (\<sqsubseteq>) (f y) (f z)"
      and xA: "x \<in> A" and yA: "y \<in> A" and zA: "z \<in> A"
      and a: "extreme {a \<in> A. f x = f a} (\<sqsupseteq>) a"
      and c: "extreme {c \<in> A. f z = f c} (\<sqsupseteq>) c"
    have "\<exists>b. extreme {b \<in> A. f y = f b} (\<sqsupseteq>) b"
      apply (rule nonempty_imp_ex_extreme) using yA by auto
    then obtain b where b: "extreme {b \<in> A. f y = f b} (\<sqsupseteq>) b" by auto
    from trans[OF well_imageD[OF fxfy a b] well_imageD[OF fyfz b c]] a b c
    show "a \<sqsubseteq> c" by auto
  qed
  interpret im: well_related_set "f`A" "well_image f A (\<sqsubseteq>)"
  proof
    fix fX
    assume fXfA: "fX \<subseteq> f ` A" and fX0: "fX \<noteq> {}"
    define X where "X \<equiv> {x\<in>A. f x \<in> fX}"
    with fXfA fX0 have XA: "X \<subseteq> A" and "X \<noteq> {}" by (auto simp: ex_in_conv[symmetric])
    from nonempty_imp_ex_extreme[OF this] obtain e where Xe: "extreme X (\<sqsupseteq>) e" by auto
    with XA have eA: "e \<in> A" by auto
    from fXfA have fX: "f ` X = fX" by (auto simp: X_def intro!: equalityI)
    show "\<exists>fe. extreme fX (well_image f A (\<sqsubseteq>))\<^sup>- fe"
    proof (safe intro!: exI extremeI elim!: subset_imageE)
      from Xe fX show fefX: "f e \<in> fX" by auto
      fix fx assume fxfX: "fx \<in> fX"
      show "well_image f A (\<sqsubseteq>) (f e) fx"
      proof (intro well_imageI)
        fix a b
        assume fea: "extreme {a \<in> A. f e = f a} (\<sqsupseteq>) a"
          and feb: "extreme {b \<in> A. fx = f b} (\<sqsupseteq>) b"
        from fea eA have aA: "a \<in> A" and ae: "a \<sqsubseteq> e" by auto
        from feb fxfX have bA: "b \<in> A" and bX: "b \<in> X" by (auto simp: X_def)
        with Xe have eb: "e \<sqsubseteq> b" by auto
        from trans[OF ae eb aA eA bA]
        show "a \<sqsubseteq> b".
      qed
    qed
  qed
  show ?thesis by unfold_locales
qed


end