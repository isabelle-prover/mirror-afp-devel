section\<open>Library of basic $\mathit{ZF}$ results\label{sec:zf-lib}\<close>

theory ZF_Library_Relative
  imports
    Aleph_Relative\<comment> \<open>must be before Cardinal\_AC\_Relative!\<close>
    Cardinal_AC_Relative
    FiniteFun_Relative
begin

no_notation sum (infixr \<open>+\<close> 65)
notation oadd (infixl \<open>+\<close> 65)

lemma (in M_cardinal_arith_jump) csucc_rel_cardinal_rel:
  assumes "Ord(\<kappa>)" "M(\<kappa>)"
  shows "(|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup> = (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
proof (intro le_anti_sym)\<comment> \<open>show both inequalities\<close>
  from assms
  have hips:"M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "Ord((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "\<kappa> < (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using Card_rel_csucc_rel[THEN Card_rel_is_Ord]
      csucc_rel_basic by simp_all
  then
  show "(|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup> \<le> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using Ord_cardinal_rel_le[THEN lt_trans1]
      Card_rel_csucc_rel
    unfolding csucc_rel_def
    by (rule_tac Least_antitone) (assumption, simp_all add:assms)
  from assms
  have "\<kappa> < L" if "Card\<^bsup>M\<^esup>(L)" "|\<kappa>|\<^bsup>M\<^esup> < L" "M(L)" for L
    using (* Card_rel_le_iff[THEN iffD1, THEN le_trans, of \<kappa> _ L] *) that
      Card_rel_is_Ord leI Card_rel_le_iff[of \<kappa> L]
    by (rule_tac ccontr, auto dest:not_lt_imp_le) (fast dest: le_imp_not_lt)
  with hips
  show "(\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<le> (|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
    using Ord_cardinal_rel_le[THEN lt_trans1] Card_rel_csucc_rel
    unfolding csucc_rel_def
    by (rule_tac Least_antitone) (assumption, auto simp add:assms)
qed

lemma (in M_cardinal_arith_jump) csucc_rel_le_mono:
  assumes "\<kappa> \<le> \<nu>" "M(\<kappa>)" "M(\<nu>)"
  shows "(\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<le> (\<nu>\<^sup>+)\<^bsup>M\<^esup>"
proof (cases "\<kappa> = \<nu>")
  case True
  with assms
  show ?thesis using Card_rel_csucc_rel [THEN Card_rel_is_Ord] by simp
next
  case False
  with assms
  have "\<kappa> < \<nu>" using le_neq_imp_lt by simp
  show ?thesis\<comment> \<open>by way of contradiction\<close>
  proof (rule ccontr)
    assume "\<not> (\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<le> (\<nu>\<^sup>+)\<^bsup>M\<^esup>"
    with assms
    have "(\<nu>\<^sup>+)\<^bsup>M\<^esup> < (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
      using Card_rel_csucc_rel[THEN Card_rel_is_Ord] le_Ord2 lt_Ord
      by (intro not_le_iff_lt[THEN iffD1]) auto
    with assms
    have "(\<nu>\<^sup>+)\<^bsup>M\<^esup> \<le> |\<kappa>|\<^bsup>M\<^esup>"
      using le_Ord2[THEN Card_rel_csucc_rel, of \<kappa> \<nu>]
        Card_rel_lt_csucc_rel_iff[of "(\<nu>\<^sup>+)\<^bsup>M\<^esup>" "|\<kappa>|\<^bsup>M\<^esup>", THEN iffD1]
        csucc_rel_cardinal_rel[OF lt_Ord] leI[of "(\<nu>\<^sup>+)\<^bsup>M\<^esup>" "(\<kappa>\<^sup>+)\<^bsup>M\<^esup>"]
      by simp
    with assms
    have "(\<nu>\<^sup>+)\<^bsup>M\<^esup> \<le> \<kappa>"
      using Ord_cardinal_rel_le[OF lt_Ord] le_trans by auto
    with assms
    have "\<nu> < \<kappa>"
      using csucc_rel_basic le_Ord2[THEN Card_rel_csucc_rel, of \<kappa> \<nu>] Card_rel_is_Ord
        le_Ord2
      by (rule_tac j="(\<nu>\<^sup>+)\<^bsup>M\<^esup>" in lt_trans2) simp_all
    with \<open>\<kappa> < \<nu>\<close>
    show "False" using le_imp_not_lt leI by blast
  qed
qed

lemma (in M_cardinal_AC) cardinal_rel_succ_not_0:   "|A|\<^bsup>M\<^esup> = succ(n) \<Longrightarrow> M(A) \<Longrightarrow> M(n) \<Longrightarrow> A \<noteq> 0"
  by auto

(* "Finite_to_one(X,Y) \<equiv> {f:X\<rightarrow>Y. \<forall>y\<in>Y. Finite({x\<in>X . f`x = y})}" *)
reldb_add functional "Finite" "Finite" \<comment> \<open>wrongly done? Finite is absolute\<close>
relativize functional "Finite_to_one" "Finite_to_one_rel" external
  (* reldb_add relational "Finite" "is_Finite" \<comment> \<open>don't have is_Finite yet\<close>
relationalize "Finite_to_one_rel" "is_Finite_to_one" *)

notation Finite_to_one_rel (\<open>Finite'_to'_one\<^bsup>_\<^esup>'(_,_')\<close>)

abbreviation
  Finite_to_one_r_set :: "[i,i,i] \<Rightarrow> i" (\<open>Finite'_to'_one\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Finite_to_one\<^bsup>M\<^esup>(X,Y) \<equiv> Finite_to_one_rel(##M,X,Y)"

locale M_ZF_library = M_aleph + M_FiniteFun
begin

lemma Finite_Collect_imp: "Finite({x\<in>X . Q(x)}) \<Longrightarrow> Finite({x\<in>X . M(x) \<and> Q(x)})"
  (is "Finite(?A) \<Longrightarrow> Finite(?B)")
  using subset_Finite[of ?B ?A] by auto

lemma Finite_to_one_relI[intro]:
  assumes "f:X\<rightarrow>\<^bsup>M\<^esup>Y" "\<And>y. y\<in>Y \<Longrightarrow> Finite({x\<in>X . f`x = y})"
    and types:"M(f)" "M(X)" "M(Y)"
  shows "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y)"
  using assms Finite_Collect_imp unfolding Finite_to_one_rel_def
  by (simp)

lemma Finite_to_one_relI'[intro]:
  assumes "f:X\<rightarrow>\<^bsup>M\<^esup>Y" "\<And>y. y\<in>Y \<Longrightarrow> Finite({x\<in>X . M(x) \<and> f`x = y})"
    and types:"M(f)" "M(X)" "M(Y)"
  shows "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y)"
  using assms unfolding Finite_to_one_rel_def
  by (simp)

lemma Finite_to_one_relD[dest]:
  "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y) \<Longrightarrow>f:X\<rightarrow>\<^bsup>M\<^esup>Y"
  "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y) \<Longrightarrow> y\<in>Y \<Longrightarrow> M(Y) \<Longrightarrow> Finite({x\<in>X . M(x) \<and> f`x = y})"
  unfolding Finite_to_one_rel_def by simp_all

lemma Diff_bij_rel:
  assumes "\<forall>A\<in>F. X \<subseteq> A"
    and types: "M(F)" "M(X)" shows "(\<lambda>A\<in>F. A-X) \<in> bij\<^bsup>M\<^esup>(F, {A-X. A\<in>F})"
  using assms  def_inj_rel def_surj_rel unfolding bij_rel_def
  apply (auto)
   apply (subgoal_tac "M(\<lambda>A\<in>F. A - X)" "M({A - X . A \<in> F})")
     apply (auto simp add:mem_function_space_rel_abs)
      apply (rule_tac lam_type, auto)
     prefer 4
     apply (subgoal_tac "M(\<lambda>A\<in>F. A - X)" "M({A - X . A \<in> F})")
       apply(tactic \<open>distinct_subgoals_tac\<close>)
     apply (auto simp add:mem_function_space_rel_abs)
     apply (rule_tac lam_type, auto) prefer 3
    apply (subst subset_Diff_Un[of X])
     apply auto
proof -
  from types
  show "M({A - X . A \<in> F})"
    using diff_replacement
    by (rule_tac RepFun_closed) (auto dest:transM[of _ F])
  from types
  show "M(\<lambda>A\<in>F. A - X)"
    using Pair_diff_replacement
    by (rule_tac lam_closed, auto dest:transM)
qed

lemma function_space_rel_nonempty:
  assumes "b\<in>B"  and types: "M(B)" "M(A)"
  shows "(\<lambda>x\<in>A. b) : A \<rightarrow>\<^bsup>M\<^esup> B"
proof -
  note assms
  moreover from this
  have "M(\<lambda>x\<in>A. b)"
    using tag_replacement by (rule_tac lam_closed, auto dest:transM)
  ultimately
  show ?thesis
    by (simp add:mem_function_space_rel_abs)
qed

lemma mem_function_space_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup> y" "M(A)" "M(y)"
  shows  "f \<in> A \<rightarrow> y"
  using assms function_space_rel_char by simp

lemmas range_fun_rel_subset_codomain = range_fun_subset_codomain[OF mem_function_space_rel]

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

context M_Pi_assumptions
begin

lemma mem_Pi_rel: "f \<in> Pi\<^bsup>M\<^esup>(A,B) \<Longrightarrow> f \<in> Pi(A, B)"
  using trans_closed mem_Pi_rel_abs
  by force

lemmas Pi_rel_rangeD = Pi_rangeD[OF mem_Pi_rel]

lemmas rel_apply_Pair = apply_Pair[OF mem_Pi_rel]

lemmas rel_apply_rangeI = apply_rangeI[OF mem_Pi_rel]

lemmas Pi_rel_range_eq = Pi_range_eq[OF mem_Pi_rel]

lemmas Pi_rel_vimage_subset = Pi_vimage_subset[OF mem_Pi_rel]

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions\<close>\<close>

context M_ZF_library
begin

lemmas rel_apply_in_range = apply_in_codomain_Ord[OF _ _ mem_function_space_rel]

lemmas rel_range_eq_image = ZF_Library.range_eq_image[OF mem_function_space_rel]

lemmas rel_Image_sub_codomain = Image_sub_codomain[OF mem_function_space_rel]

lemma rel_inj_to_Image: "\<lbrakk>f:A\<rightarrow>\<^bsup>M\<^esup>B; f \<in> inj\<^bsup>M\<^esup>(A,B); M(A); M(B)\<rbrakk> \<Longrightarrow> f \<in> inj\<^bsup>M\<^esup>(A,f``A)"
  using inj_to_Image[OF mem_function_space_rel mem_inj_rel]
    transM[OF _ function_space_rel_closed] by simp

lemma inj_rel_imp_surj_rel:
  fixes f b
  defines [simp]: "ifx(x) \<equiv> if x\<in>range(f) then converse(f)`x else b"
  assumes "f \<in> inj\<^bsup>M\<^esup>(B,A)" "b\<in>B" and types: "M(f)" "M(B)" "M(A)"
  shows "(\<lambda>x\<in>A. ifx(x)) \<in> surj\<^bsup>M\<^esup>(A,B)"
proof -
  from types and \<open>b\<in>B\<close>
  have "M(\<lambda>x\<in>A. ifx(x))"
    using ifx_replacement by (rule_tac lam_closed) (auto dest:transM)
  with assms(2-)
  show ?thesis
    using inj_imp_surj mem_surj_abs by simp
qed

lemma function_space_rel_disjoint_Un:
  assumes "f \<in> A\<rightarrow>\<^bsup>M\<^esup>B" "g \<in> C\<rightarrow>\<^bsup>M\<^esup>D"  "A \<inter> C = 0"
    and types:"M(A)" "M(B)" "M(C)" "M(D)"
  shows "f \<union> g \<in> (A \<union> C)\<rightarrow>\<^bsup>M\<^esup> (B \<union> D)"
  using assms fun_Pi_disjoint_Un[OF mem_function_space_rel
      mem_function_space_rel, OF assms(1) _ _ assms(2)]
    function_space_rel_char by auto

lemma restrict_eq_imp_Un_into_function_space_rel:
  assumes "f \<in> A\<rightarrow>\<^bsup>M\<^esup>B" "g \<in> C\<rightarrow>\<^bsup>M\<^esup>D"  "restrict(f, A \<inter> C) = restrict(g, A \<inter> C)"
    and types:"M(A)" "M(B)" "M(C)" "M(D)"
  shows "f \<union> g \<in> (A \<union> C)\<rightarrow>\<^bsup>M\<^esup> (B \<union> D)"
  using assms restrict_eq_imp_Un_into_Pi[OF mem_function_space_rel
      mem_function_space_rel, OF assms(1) _ _ assms(2)]
    function_space_rel_char by auto

lemma lepoll_relD[dest]: "A \<lesssim>\<^bsup>M\<^esup> B \<Longrightarrow> \<exists>f[M]. f \<in> inj\<^bsup>M\<^esup>(A, B)"
  unfolding lepoll_rel_def .

\<comment> \<open>Should the assumptions be on \<^term>\<open>f\<close> or on \<^term>\<open>A\<close> and \<^term>\<open>B\<close>?
    Should BOTH be intro rules?\<close>
lemma lepoll_relI[intro]: "f \<in> inj\<^bsup>M\<^esup>(A, B) \<Longrightarrow> M(f) \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> B"
  unfolding lepoll_rel_def by blast

lemma eqpollD[dest]: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> \<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(A, B)"
  unfolding eqpoll_rel_def .

\<comment> \<open>Same as @{thm lepoll_relI}\<close>
lemma bij_rel_imp_eqpoll_rel[intro]: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(f) \<Longrightarrow> A \<approx>\<^bsup>M\<^esup> B"
  unfolding eqpoll_rel_def by blast

lemma restrict_bij_rel:\<comment> \<open>Unused\<close>
  assumes "f \<in> inj\<^bsup>M\<^esup>(A,B)"  "C\<subseteq>A"
    and types:"M(A)" "M(B)" "M(C)"
  shows "restrict(f,C)\<in> bij\<^bsup>M\<^esup>(C, f``C)"
  using assms restrict_bij inj_rel_char bij_rel_char by auto

lemma range_of_subset_eqpoll_rel:
  assumes "f \<in> inj\<^bsup>M\<^esup>(X,Y)" "S \<subseteq> X"
    and types:"M(X)" "M(Y)" "M(S)"
  shows "S \<approx>\<^bsup>M\<^esup> f `` S"
  using assms restrict_bij bij_rel_char
    trans_inj_rel_closed[OF \<open>f \<in> inj\<^bsup>M\<^esup>(X,Y)\<close>]
  unfolding eqpoll_rel_def
  by (rule_tac x="restrict(f,S)" in rexI) auto

lemmas inj_rel_is_fun = inj_is_fun[OF mem_inj_rel]

lemma inj_rel_bij_rel_range: "f \<in> inj\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> bij\<^bsup>M\<^esup>(A,range(f))"
  using bij_rel_char inj_rel_char inj_bij_range by force

lemma bij_rel_is_inj_rel: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> inj\<^bsup>M\<^esup>(A,B)"
  unfolding bij_rel_def by simp

lemma inj_rel_weaken_type: "[| f \<in> inj\<^bsup>M\<^esup>(A,B);  B\<subseteq>D; M(A); M(B); M(D) |] ==> f \<in> inj\<^bsup>M\<^esup>(A,D)"
  using inj_rel_char inj_rel_is_fun inj_weaken_type by auto

lemma bij_rel_converse_bij_rel [TC]: "f \<in> bij\<^bsup>M\<^esup>(A,B)  \<Longrightarrow> M(A) \<Longrightarrow> M(B) ==> converse(f): bij\<^bsup>M\<^esup>(B,A)"
  using bij_rel_char by force

lemma bij_rel_is_fun_rel: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow>  f \<in> A\<rightarrow>\<^bsup>M\<^esup>B"
  using bij_rel_char mem_function_space_rel_abs bij_is_fun by simp

lemmas bij_rel_is_fun = bij_rel_is_fun_rel[THEN mem_function_space_rel]

lemma comp_bij_rel:
  "g \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> f \<in> bij\<^bsup>M\<^esup>(B,C) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (f O g) \<in> bij\<^bsup>M\<^esup>(A,C)"
  using bij_rel_char comp_bij by force

lemma inj_rel_converse_fun: "f \<in> inj\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> converse(f) \<in> range(f)\<rightarrow>\<^bsup>M\<^esup>A"
proof -
  assume "f \<in> inj\<^bsup>M\<^esup>(A,B)" "M(A)" "M(B)"
  then
  have "M(f)" "M(converse(f))" "M(range(f))" "f\<in>inj(A,B)"
    using inj_rel_char converse_closed range_closed
    by auto
  then
  show ?thesis
    using inj_converse_inj function_space_rel_char inj_is_fun \<open>M(A)\<close> by auto
qed

lemma fg_imp_bijective_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup>B"  "g \<in> B\<rightarrow>\<^bsup>M\<^esup>A"  "f O g = id(B)" "g O f = id(A)" "M(A)" "M(B)"
  shows "f \<in> bij\<^bsup>M\<^esup>(A,B)"
  using assms mem_bij_abs fg_imp_bijective mem_function_space_rel_abs[THEN iffD2] function_space_rel_char
  by auto

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

(*************   Discipline for cexp   ****************)
relativize functional "cexp" "cexp_rel" external
relationalize "cexp_rel" "is_cexp"

context M_ZF_library
begin

is_iff_rel for "cexp"
  using is_cardinal_iff is_function_space_iff unfolding cexp_rel_def is_cexp_def
  by (simp)

rel_closed for "cexp" unfolding cexp_rel_def by simp

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

synthesize "is_cexp" from_definition assuming "nonempty"
notation is_cexp_fm (\<open>\<cdot>_\<^bsup>\<up>_\<^esup> is _\<cdot>\<close>)
arity_theorem for "is_cexp_fm"

abbreviation
  cexp_r :: "[i,i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>_\<^bsup>\<up>_,_\<^esup>\<close>) where
  "cexp_r(x,y,M) \<equiv> cexp_rel(M,x,y)"

abbreviation
  cexp_r_set :: "[i,i,i] \<Rightarrow> i"  (\<open>_\<^bsup>\<up>_,_\<^esup>\<close>) where
  "cexp_r_set(x,y,M) \<equiv> cexp_rel(##M,x,y)"

context M_ZF_library
begin

lemma Card_rel_cexp_rel: "M(\<kappa>) \<Longrightarrow> M(\<nu>) \<Longrightarrow> Card\<^bsup>M\<^esup>(\<kappa>\<^bsup>\<up>\<nu>,M\<^esup>)"
  unfolding cexp_rel_def by simp

\<comment> \<open>Restoring congruence rule, but NOTE: beware\<close>
declare conj_cong[cong]

lemma eq_csucc_rel_ord:
  "Ord(i) \<Longrightarrow> M(i) \<Longrightarrow> (i\<^sup>+)\<^bsup>M\<^esup> = (|i|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
  using Card_rel_lt_iff Least_cong unfolding csucc_rel_def by auto

lemma lesspoll_succ_rel:
  assumes "Ord(\<kappa>)" "M(\<kappa>)"
  shows "\<kappa> \<lesssim>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
  using csucc_rel_basic assms lt_Card_rel_imp_lesspoll_rel
    Card_rel_csucc_rel lepoll_rel_iff_leqpoll_rel
  by auto

lemma lesspoll_rel_csucc_rel:
  assumes "Ord(\<kappa>)"
    and types:"M(\<kappa>)" "M(d)"
  shows "d \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<longleftrightarrow> d \<lesssim>\<^bsup>M\<^esup> \<kappa>"
proof
  assume "d \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
  moreover
  note Card_rel_csucc_rel assms Card_rel_is_Ord
  moreover from calculation
  have "Card\<^bsup>M\<^esup>((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "Ord((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)"
    using Card_rel_is_Ord by simp_all
  moreover from calculation
  have "d \<prec>\<^bsup>M\<^esup> (|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>" "d \<approx>\<^bsup>M\<^esup> |d|\<^bsup>M\<^esup>"
    using eq_csucc_rel_ord[OF _ \<open>M(\<kappa>)\<close>]
      lesspoll_rel_imp_eqpoll_rel eqpoll_rel_sym by simp_all
  moreover from calculation
  have "|d|\<^bsup>M\<^esup> < (|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
    using lesspoll_cardinal_lt_rel by simp
  moreover from calculation
  have "|d|\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> |\<kappa>|\<^bsup>M\<^esup>"
    using Card_rel_lt_csucc_rel_iff le_imp_lepoll_rel by simp
  moreover from calculation
  have "|d|\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> \<kappa>"
    using Ord_cardinal_rel_eqpoll_rel lepoll_rel_eq_trans
    by simp
  ultimately
  show "d \<lesssim>\<^bsup>M\<^esup> \<kappa>"
    using eq_lepoll_rel_trans by simp
next
  from \<open>Ord(\<kappa>)\<close>
  have "\<kappa> < (\<kappa>\<^sup>+)\<^bsup>M\<^esup>" "Card\<^bsup>M\<^esup>((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)"
    using Card_rel_csucc_rel lt_csucc_rel_iff types eq_csucc_rel_ord[OF _ \<open>M(\<kappa>)\<close>]
    by simp_all
  then
  have "\<kappa> \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using lt_Card_rel_imp_lesspoll_rel[OF _ \<open>\<kappa> <_\<close>] types by simp
  moreover
  assume "d \<lesssim>\<^bsup>M\<^esup> \<kappa>"
  ultimately
  have "d \<lesssim>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using Card_rel_csucc_rel types lesspoll_succ_rel lepoll_rel_trans \<open>Ord(\<kappa>)\<close>
    by simp
  moreover
  from \<open>d \<lesssim>\<^bsup>M\<^esup> \<kappa>\<close> \<open>Ord(\<kappa>)\<close>
  have "(\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> \<kappa>" if "d \<approx>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using eqpoll_rel_sym[OF that] types eq_lepoll_rel_trans[OF _ \<open>d\<lesssim>\<^bsup>M\<^esup>\<kappa>\<close>]
    by simp
  moreover from calculation \<open>\<kappa> \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>\<close>
  have False if "d \<approx>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using lesspoll_rel_irrefl[OF _ \<open>M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)\<close>] lesspoll_rel_trans1 types that
    by auto
  ultimately
  show "d \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    unfolding lesspoll_rel_def by auto
qed

lemma Infinite_imp_nats_lepoll:
  assumes "Infinite(X)" "n \<in> \<omega>"
  shows "n \<lesssim> X"
  using \<open>n \<in> \<omega>\<close>
proof (induct)
  case 0
  then
  show ?case using empty_lepollI by simp
next
  case (succ x)
  show ?case
  proof -
    from \<open>Infinite(X)\<close> and \<open>x \<in> \<omega>\<close>
    have "\<not> (x \<approx> X)"
      using eqpoll_sym unfolding Finite_def by auto
    with \<open>x \<lesssim> X\<close>
    obtain f where "f \<in> inj(x,X)" "f \<notin> surj(x,X)"
      unfolding bij_def eqpoll_def by auto
    moreover from this
    obtain b where "b \<in> X" "\<forall>a\<in>x. f`a \<noteq> b"
      using inj_is_fun unfolding surj_def by auto
    ultimately
    have "f \<in> inj(x,X-{b})"
      unfolding inj_def by (auto intro:Pi_type)
    then
    have "cons(\<langle>x, b\<rangle>, f) \<in> inj(succ(x), cons(b, X - {b}))"
      using inj_extend[of f x "X-{b}" x b] unfolding succ_def
      by (auto dest:mem_irrefl)
    moreover from \<open>b\<in>X\<close>
    have "cons(b, X - {b}) = X" by auto
    ultimately
    show "succ(x) \<lesssim> X" by auto
  qed
qed

lemma nepoll_imp_nepoll_rel :
  assumes "\<not> x \<approx> X" "M(x)" "M(X)"
  shows "\<not> (x \<approx>\<^bsup>M\<^esup> X)"
  using assms unfolding eqpoll_def eqpoll_rel_def by simp

lemma Infinite_imp_nats_lepoll_rel:
  assumes "Infinite(X)" "n \<in> \<omega>"
    and types: "M(X)"
  shows "n \<lesssim>\<^bsup>M\<^esup> X"
  using \<open>n \<in> \<omega>\<close>
proof (induct)
  case 0
  then
  show ?case using empty_lepoll_relI types by simp
next
  case (succ x)
  show ?case
  proof -
    from \<open>Infinite(X)\<close> and \<open>x \<in> \<omega>\<close>
    have "\<not> (x \<approx> X)" "M(x)" "M(succ(x))"
      using eqpoll_sym unfolding Finite_def by auto
    then
    have "\<not> (x \<approx>\<^bsup>M\<^esup> X)"
      using nepoll_imp_nepoll_rel types by simp
    with \<open>x \<lesssim>\<^bsup>M\<^esup> X\<close>
    obtain f where "f \<in> inj\<^bsup>M\<^esup>(x,X)" "f \<notin> surj\<^bsup>M\<^esup>(x,X)" "M(f)"
      unfolding bij_rel_def eqpoll_rel_def by auto
    with \<open>M(X)\<close> \<open>M(x)\<close>
    have "f\<notin>surj(x,X)" "f\<in>inj(x,X)"
      using surj_rel_char by simp_all
    moreover
    from this
    obtain b where "b \<in> X" "\<forall>a\<in>x. f`a \<noteq> b"
      using inj_is_fun unfolding surj_def by auto
    moreover
    from this calculation \<open>M(x)\<close>
    have "f \<in> inj(x,X-{b})" "M(<x,b>)"
      unfolding inj_def using transM[OF _ \<open>M(X)\<close>]
      by (auto intro:Pi_type)
    moreover
    from this
    have "cons(\<langle>x, b\<rangle>, f) \<in> inj(succ(x), cons(b, X - {b}))" (is "?g\<in>_")
      using inj_extend[of f x "X-{b}" x b] unfolding succ_def
      by (auto dest:mem_irrefl)
    moreover
    note \<open>M(<x,b>)\<close> \<open>M(f)\<close> \<open>b\<in>X\<close> \<open>M(X)\<close> \<open>M(succ(x))\<close>
    moreover from this
    have "M(?g)" "cons(b, X - {b}) = X" by auto
    moreover from calculation
    have "?g\<in>inj_rel(M,succ(x),X)"
      using mem_inj_abs by simp
    with \<open>M(?g)\<close>
    show "succ(x) \<lesssim>\<^bsup>M\<^esup> X" using lepoll_relI by simp
  qed
qed

lemma lepoll_rel_imp_lepoll: "A \<lesssim>\<^bsup>M\<^esup> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<lesssim> B"
  unfolding lepoll_rel_def by auto

lemma zero_lesspoll_rel: assumes "0<\<kappa>" "M(\<kappa>)" shows "0 \<prec>\<^bsup>M\<^esup> \<kappa>"
  using assms eqpoll_rel_0_iff[THEN iffD1, of \<kappa>] eqpoll_rel_sym
  unfolding lesspoll_rel_def lepoll_rel_def
  by (auto simp add:inj_def)

lemma lepoll_rel_nat_imp_Infinite: "\<omega> \<lesssim>\<^bsup>M\<^esup> X \<Longrightarrow> M(X) \<Longrightarrow> Infinite(X)"
  using  lepoll_nat_imp_Infinite lepoll_rel_imp_lepoll by simp

lemma InfCard_rel_imp_Infinite: "InfCard\<^bsup>M\<^esup>(\<kappa>) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> Infinite(\<kappa>)"
  using le_imp_lepoll_rel[THEN lepoll_rel_nat_imp_Infinite, of \<kappa>]
  unfolding InfCard_rel_def by simp

lemma lt_surj_rel_empty_imp_Card_rel:
  assumes "Ord(\<kappa>)" "\<And>\<alpha>. \<alpha> < \<kappa> \<Longrightarrow> surj\<^bsup>M\<^esup>(\<alpha>,\<kappa>) = 0"
    and types:"M(\<kappa>)"
  shows "Card\<^bsup>M\<^esup>(\<kappa>)"
proof -
  {
    define min where "min\<equiv>\<mu> x. \<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(x,\<kappa>)"
    moreover
    note \<open>Ord(\<kappa>)\<close> \<open>M(\<kappa>)\<close>
    moreover
    assume "|\<kappa>|\<^bsup>M\<^esup> < \<kappa>"
    moreover from calculation
    have "\<exists>f. f \<in> bij\<^bsup>M\<^esup>(min,\<kappa>)"
      using LeastI[of "\<lambda>i. i \<approx>\<^bsup>M\<^esup> \<kappa>" \<kappa>, OF eqpoll_rel_refl]
      unfolding Card_rel_def cardinal_rel_def eqpoll_rel_def
      by (auto)
    moreover from calculation
    have "min < \<kappa>"
      using lt_trans1[of min "\<mu> i. M(i) \<and> (\<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(i, \<kappa>))" \<kappa>]
        Least_le[of "\<lambda>i. i \<approx>\<^bsup>M\<^esup> \<kappa>" "|\<kappa>|\<^bsup>M\<^esup>", OF Ord_cardinal_rel_eqpoll_rel]
      unfolding Card_rel_def cardinal_rel_def eqpoll_rel_def
      by (simp)
    moreover
    note \<open>min < \<kappa> \<Longrightarrow> surj\<^bsup>M\<^esup>(min,\<kappa>) = 0\<close>
    ultimately
    have "False"
      unfolding bij_rel_def by simp
  }
  with assms
  show ?thesis
    using Ord_cardinal_rel_le[of \<kappa>] not_lt_imp_le[of "|\<kappa>|\<^bsup>M\<^esup>" \<kappa>] le_anti_sym
    unfolding Card_rel_def by auto
qed

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

relativize functional "mono_map" "mono_map_rel" external
relationalize "mono_map_rel" "is_mono_map"
synthesize "is_mono_map" from_definition assuming "nonempty"

notation mono_map_rel (\<open>mono'_map\<^bsup>_\<^esup>'(_,_,_,_')\<close>)

abbreviation
  mono_map_r_set  :: "[i,i,i,i,i]\<Rightarrow>i"  (\<open>mono'_map\<^bsup>_\<^esup>'(_,_,_,_')\<close>) where
  "mono_map\<^bsup>M\<^esup>(a,r,b,s) \<equiv> mono_map_rel(##M,a,r,b,s)"

context M_ZF_library
begin

lemma mono_map_rel_char:
  assumes "M(a)" "M(b)"
  shows "mono_map\<^bsup>M\<^esup>(a,r,b,s) = {f\<in>mono_map(a,r,b,s) . M(f)}"
  using assms function_space_rel_char unfolding mono_map_rel_def mono_map_def
  by auto

text\<open>Just a sample of porting results on \<^term>\<open>mono_map\<close>\<close>
lemma mono_map_rel_mono:
  assumes
    "f \<in> mono_map\<^bsup>M\<^esup>(A,r,B,s)" "B \<subseteq> C"
    and types:"M(A)" "M(B)" "M(C)"
  shows
    "f \<in> mono_map\<^bsup>M\<^esup>(A,r,C,s)"
  using assms mono_map_mono mono_map_rel_char by auto

lemma nats_le_InfCard_rel:
  assumes "n \<in> \<omega>" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
  shows "n \<le> \<kappa>"
  using assms Ord_is_Transset
    le_trans[of n \<omega> \<kappa>, OF le_subset_iff[THEN iffD2]]
  unfolding InfCard_rel_def Transset_def by simp

lemma nat_into_InfCard_rel:
  assumes "n \<in> \<omega>" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
  shows "n \<in> \<kappa>"
  using assms  le_imp_subset[of \<omega> \<kappa>]
  unfolding InfCard_rel_def by auto

lemma Finite_lesspoll_rel_nat:
  assumes "Finite(x)" "M(x)"
  shows "x \<prec>\<^bsup>M\<^esup> nat"
proof -
  note assms
  moreover from this
  obtain n where "n \<in> \<omega>" "M(n)" "x \<approx> n"
    unfolding Finite_def by auto
  moreover from calculation
  obtain f where "f \<in> bij(x,n)" "f: x-||>n"
    using Finite_Fin[THEN fun_FiniteFunI, OF _ subset_refl] bij_is_fun
    unfolding eqpoll_def by auto
  ultimately
  have "x\<approx>\<^bsup>M\<^esup> n" unfolding eqpoll_rel_def by (auto dest:transM)
  with assms and \<open>M(n)\<close>
  have "n \<approx>\<^bsup>M\<^esup> x" using eqpoll_rel_sym by simp
  moreover
  note \<open>n\<in>\<omega>\<close> \<open>M(n)\<close>
  ultimately
  show ?thesis
    using assms eq_lesspoll_rel_trans[OF \<open>x\<approx>\<^bsup>M\<^esup> n\<close> n_lesspoll_rel_nat]
    by simp
qed

lemma Finite_cardinal_rel_in_nat [simp]:
  assumes "Finite(A)" "M(A)" shows "|A|\<^bsup>M\<^esup> \<in> \<omega>"
proof -
  note assms
  moreover from this
  obtain n where "n \<in> \<omega>" "M(n)" "A \<approx> n"
    unfolding Finite_def by auto
  moreover from calculation
  obtain f where "f \<in> bij(A,n)" "f: A-||>n"
    using Finite_Fin[THEN fun_FiniteFunI, OF _ subset_refl] bij_is_fun
    unfolding eqpoll_def by auto
  ultimately
  have "A \<approx>\<^bsup>M\<^esup> n" unfolding eqpoll_rel_def by (auto dest:transM)
  with assms and \<open>M(n)\<close>
  have "n \<approx>\<^bsup>M\<^esup> A" using eqpoll_rel_sym by simp
  moreover
  note \<open>n\<in>\<omega>\<close> \<open>M(n)\<close>
  ultimately
  show ?thesis
    using assms Least_le[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A" n]
      lt_trans1[of _ n \<omega>, THEN ltD]
    unfolding cardinal_rel_def Finite_def
    by (auto dest!:naturals_lt_nat)
qed

lemma Finite_cardinal_rel_eq_cardinal:
  assumes "Finite(A)" "M(A)" shows "|A|\<^bsup>M\<^esup> = |A|"
proof -
  \<comment> \<open>Copy-paste from @{thm Finite_cardinal_rel_in_nat}\<close>
  note assms
  moreover from this
  obtain n where "n \<in> \<omega>" "M(n)" "A \<approx> n"
    unfolding Finite_def by auto
  moreover from this
  have "|A| = n"
    using cardinal_cong[of A n]
      nat_into_Card[THEN Card_cardinal_eq, of n] by simp
  moreover from calculation
  obtain f where "f \<in> bij(A,n)" "f: A-||>n"
    using Finite_Fin[THEN fun_FiniteFunI, OF _ subset_refl] bij_is_fun
    unfolding eqpoll_def by auto
  ultimately
  have "A \<approx>\<^bsup>M\<^esup> n" unfolding eqpoll_rel_def by (auto dest:transM)
  with assms and \<open>M(n)\<close> \<open>n\<in>\<omega>\<close>
  have "|A|\<^bsup>M\<^esup> = n"
    using cardinal_rel_cong[of A n]
      nat_into_Card_rel[THEN Card_rel_cardinal_rel_eq, of n]
    by simp
  with \<open>|A| = n\<close>
  show ?thesis by simp
qed

lemma Finite_imp_cardinal_rel_cons:
  assumes FA: "Finite(A)" and a: "a\<notin>A" and types:"M(A)" "M(a)"
  shows "|cons(a,A)|\<^bsup>M\<^esup> = succ(|A|\<^bsup>M\<^esup>)"
  using assms Finite_imp_cardinal_cons Finite_cardinal_rel_eq_cardinal by simp

lemma Finite_imp_succ_cardinal_rel_Diff:
  assumes "Finite(A)" "a \<in> A" "M(A)"
  shows "succ(|A-{a}|\<^bsup>M\<^esup>) = |A|\<^bsup>M\<^esup>"
proof -
  from assms
  have inM: "M(A-{a})" "M(a)" "M(A)" by (auto dest:transM)
  with \<open>Finite(A)\<close>
  have "succ(|A-{a}|\<^bsup>M\<^esup>) = succ(|A-{a}|)"
    using Diff_subset[THEN subset_Finite,
        THEN Finite_cardinal_rel_eq_cardinal, of A "{a}"] by simp
  also from assms
  have "\<dots> = |A|"
    using Finite_imp_succ_cardinal_Diff by simp
  also from assms
  have "\<dots> = |A|\<^bsup>M\<^esup>" using Finite_cardinal_rel_eq_cardinal by simp
  finally
  show ?thesis .
qed

lemma InfCard_rel_Aleph_rel:
  notes Aleph_rel_zero[simp]
  assumes "Ord(\<alpha>)"
    and types: "M(\<alpha>)"
  shows "InfCard\<^bsup>M\<^esup>(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
proof -
  have "\<not> (\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> \<in> \<omega>)"
  proof (cases "\<alpha>=0")
    case True
    then show ?thesis using mem_irrefl by auto
  next
    case False
    with assms
    have "\<omega> \<in> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>" using Ord_0_lt[of \<alpha>] ltD by (auto dest:Aleph_rel_increasing)
    then show ?thesis using foundation by blast
  qed
  with assms
  have "\<not> (|\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> \<in> \<omega>)"
    using Card_rel_cardinal_rel_eq by auto
  with assms
  have "Infinite(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)" using Ord_Aleph_rel by clarsimp
  with assms
  show ?thesis
    using Inf_Card_rel_is_InfCard_rel by simp
qed

lemmas Limit_Aleph_rel = InfCard_rel_Aleph_rel[THEN InfCard_rel_is_Limit]

bundle Ord_dests = Limit_is_Ord[dest] Card_rel_is_Ord[dest]
bundle Aleph_rel_dests = Aleph_rel_cont[dest]
bundle Aleph_rel_intros = Aleph_rel_increasing[intro!]
bundle Aleph_rel_mem_dests = Aleph_rel_increasing[OF ltI, THEN ltD, dest]

lemma f_imp_injective_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup> B" "\<forall>x\<in>A. d(f ` x) = x" "M(A)" "M(B)"
  shows "f \<in> inj\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (simp (no_asm_simp) add: def_inj_rel)
  apply (auto intro: subst_context [THEN box_equals])
  done

lemma lam_injective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x"
    "\<forall>x[M]. M(c(x))" "lam_replacement(M,c)"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> inj\<^bsup>M\<^esup>(A, B)"
  using assms function_space_rel_char lam_replacement_iff_lam_closed
  by (rule_tac d = d in f_imp_injective_rel)
    (auto simp add: lam_type)

lemma f_imp_surjective_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup> B" "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A" "\<And>y. y \<in> B \<Longrightarrow> f ` d(y) = y"
    "M(A)" "M(B)"
  shows "f \<in> surj\<^bsup>M\<^esup>(A, B)"
  using assms
  by (simp add: def_surj_rel, blast)

lemma lam_surjective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A"
    "\<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y"
    "\<forall>x[M]. M(c(x))" "lam_replacement(M,c)"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> surj\<^bsup>M\<^esup>(A, B)"
  using assms function_space_rel_char lam_replacement_iff_lam_closed
  by (rule_tac d = d in f_imp_surjective_rel)
    (auto simp add: lam_type)

lemma lam_bijective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A"
    "\<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x"
    "\<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y"
    "\<forall>x[M]. M(c(x))" "lam_replacement(M,c)"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> bij\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (unfold bij_rel_def)
  apply (blast intro!: lam_injective_rel lam_surjective_rel)
  done

lemma function_space_rel_eqpoll_rel_cong:
  assumes
    "A \<approx>\<^bsup>M\<^esup> A'" "B \<approx>\<^bsup>M\<^esup> B'" "M(A)" "M(A')" "M(B)" "M(B')"
  shows
    "A \<rightarrow>\<^bsup>M\<^esup> B \<approx>\<^bsup>M\<^esup> A' \<rightarrow>\<^bsup>M\<^esup> B'"
proof -
  from assms(1)[THEN eqpoll_rel_sym] assms(2) assms lam_type
  obtain f g where "f \<in> bij\<^bsup>M\<^esup>(A',A)" "g \<in> bij\<^bsup>M\<^esup>(B,B')"
    by blast
  with assms
  have "converse(g) : bij\<^bsup>M\<^esup>(B', B)" "converse(f): bij\<^bsup>M\<^esup>(A, A')"
    using bij_converse_bij by auto
  let ?H="\<lambda> h \<in> A \<rightarrow>\<^bsup>M\<^esup> B . g O h O f"
  let ?I="\<lambda> h \<in> A' \<rightarrow>\<^bsup>M\<^esup> B' . converse(g) O h O converse(f)"
  have go:"g O F O f : A' \<rightarrow>\<^bsup>M\<^esup> B'" if "F: A \<rightarrow>\<^bsup>M\<^esup> B" for F
  proof -
    note assms \<open>f\<in>_\<close> \<open>g\<in>_\<close> that
    moreover from this
    have "g O F O f : A' \<rightarrow> B'"
      using bij_rel_is_fun[OF \<open>g\<in>_\<close>] bij_rel_is_fun[OF \<open>f\<in>_\<close>] comp_fun
        mem_function_space_rel[OF \<open>F\<in>_\<close>]
      by blast
    ultimately
    show "g O F O f : A' \<rightarrow>\<^bsup>M\<^esup> B'"
      using comp_closed function_space_rel_char bij_rel_char
      by auto
  qed
  have og:"converse(g) O F O converse(f) : A \<rightarrow>\<^bsup>M\<^esup> B" if "F: A' \<rightarrow>\<^bsup>M\<^esup> B'" for F
  proof -
    note assms that \<open>converse(f) \<in> _\<close> \<open>converse(g) \<in> _\<close>
    moreover from this
    have "converse(g) O F O converse(f) : A \<rightarrow> B"
      using bij_rel_is_fun[OF \<open>converse(g)\<in>_\<close>] bij_rel_is_fun[OF \<open>converse(f)\<in>_\<close>] comp_fun
        mem_function_space_rel[OF \<open>F\<in>_\<close>]
      by blast
    ultimately
    show "converse(g) O F O converse(f) : A \<rightarrow>\<^bsup>M\<^esup> B" (is "?G\<in>_")
      using comp_closed function_space_rel_char bij_rel_char
      by auto
  qed
  with go
  have tc:"?H \<in> (A \<rightarrow>\<^bsup>M\<^esup> B) \<rightarrow> (A'\<rightarrow>\<^bsup>M\<^esup> B')" "?I \<in> (A' \<rightarrow>\<^bsup>M\<^esup> B') \<rightarrow> (A\<rightarrow>\<^bsup>M\<^esup> B)"
    using lam_type by auto
  with assms \<open>f\<in>_\<close> \<open>g\<in>_\<close>
  have "M(g O x O f)" and "M(converse(g) O x O converse(f))" if "M(x)" for x
    using bij_rel_char comp_closed that by auto
  with assms \<open>f\<in>_\<close> \<open>g\<in>_\<close>
  have "M(?H)" "M(?I)"
    using lam_replacement_iff_lam_closed[THEN iffD1,OF _ lam_replacement_comp']
      bij_rel_char by auto
  show ?thesis
    unfolding eqpoll_rel_def
  proof (intro rexI[of _ ?H] fg_imp_bijective_rel)
    from og go
    have "(\<And>x. x \<in> A' \<rightarrow>\<^bsup>M\<^esup> B' \<Longrightarrow> converse(g) O x O converse(f) \<in> A \<rightarrow>\<^bsup>M\<^esup> B)"
      by simp
  next
    show "M(A \<rightarrow>\<^bsup>M\<^esup> B)" using assms by simp
  next
    show "M(A' \<rightarrow>\<^bsup>M\<^esup> B')" using assms by simp
  next
    from og assms
    have "?H O ?I = (\<lambda>x\<in>A' \<rightarrow>\<^bsup>M\<^esup> B' . (g O converse(g)) O x O (converse(f) O f))"
      using lam_cong[OF refl[of "A' \<rightarrow>\<^bsup>M\<^esup> B'"]] comp_assoc comp_lam
      by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow>\<^bsup>M\<^esup> B' . id(B') O x O (id(A')))"
      using left_comp_inverse[OF mem_inj_rel[OF bij_rel_is_inj_rel]] \<open>f\<in>_\<close>
        right_comp_inverse[OF bij_is_surj[OF mem_bij_rel]] \<open>g\<in>_\<close> assms
      by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow>\<^bsup>M\<^esup> B' . x)"
      using left_comp_id[OF fun_is_rel[OF mem_function_space_rel]]
        right_comp_id[OF fun_is_rel[OF mem_function_space_rel]] assms
      by auto
    also
    have "... = id(A'\<rightarrow>\<^bsup>M\<^esup>B')" unfolding id_def by simp
    finally
    show "?H O ?I = id(A' \<rightarrow>\<^bsup>M\<^esup> B')" .
  next
    from go assms
    have "?I O ?H = (\<lambda>x\<in>A \<rightarrow>\<^bsup>M\<^esup> B . (converse(g) O g) O x O (f O converse(f)))"
      using lam_cong[OF refl[of "A \<rightarrow>\<^bsup>M\<^esup> B"]] comp_assoc comp_lam by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow>\<^bsup>M\<^esup> B . id(B) O x O (id(A)))"
      using
        left_comp_inverse[OF mem_inj_rel[OF bij_rel_is_inj_rel[OF \<open>g\<in>_\<close>]]]
        right_comp_inverse[OF bij_is_surj[OF mem_bij_rel[OF \<open>f\<in>_\<close>]]] assms
      by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow>\<^bsup>M\<^esup> B . x)"
      using left_comp_id[OF fun_is_rel[OF mem_function_space_rel]]
        right_comp_id[OF fun_is_rel[OF mem_function_space_rel]]
        assms
      by auto
    also
    have "... = id(A\<rightarrow>\<^bsup>M\<^esup>B)" unfolding id_def by simp
    finally
    show "?I O ?H = id(A \<rightarrow>\<^bsup>M\<^esup> B)" .
  next
    from assms tc \<open>M(?H)\<close> \<open>M(?I)\<close>
    show "?H \<in> (A\<rightarrow>\<^bsup>M\<^esup> B) \<rightarrow>\<^bsup>M\<^esup> (A'\<rightarrow>\<^bsup>M\<^esup> B')" "M(?H)"
      "?I \<in> (A'\<rightarrow>\<^bsup>M\<^esup> B') \<rightarrow>\<^bsup>M\<^esup> (A\<rightarrow>\<^bsup>M\<^esup> B)"
      using mem_function_space_rel_abs by auto
  qed
qed

lemma curry_eqpoll_rel:
  fixes \<nu>1 \<nu>2  \<kappa>
  assumes  "M(\<nu>1)" "M(\<nu>2)" "M(\<kappa>)"
  shows "\<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>) \<approx>\<^bsup>M\<^esup> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>"
  unfolding eqpoll_rel_def
proof (intro rexI, rule lam_bijective_rel,
    rule_tac [1-2] mem_function_space_rel_abs[THEN iffD2],
    rule_tac [4] lam_type, rule_tac [8] lam_type,
    rule_tac [8] mem_function_space_rel_abs[THEN iffD2],
    rule_tac [11] lam_type, simp_all add:assms)
  let ?cur="\<lambda>x. \<lambda>w\<in>\<nu>1 \<times> \<nu>2. x ` fst(w) ` snd(w)"
  fix f z
  assume "f : \<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)"
  moreover
  note assms
  moreover from calculation
  have "M(\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)"
    using function_space_rel_closed by simp
  moreover from calculation
  have "M(f)" "f : \<nu>1 \<rightarrow> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)"
    using function_space_rel_char by (auto dest:transM)
  moreover from calculation
  have "x \<in> \<nu>1 \<Longrightarrow> f`x : \<nu>2 \<rightarrow> \<kappa>" for x
    by (auto dest:transM intro!:mem_function_space_rel_abs[THEN iffD1])
  moreover from this
  show "(\<lambda>a\<in>\<nu>1. \<lambda>b\<in>\<nu>2. ?cur(f) ` \<langle>a, b\<rangle>) = f"
    using Pi_type[OF \<open>f \<in> \<nu>1 \<rightarrow> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>\<close>, of "\<lambda>_.\<nu>2 \<rightarrow> \<kappa>"] by simp
  moreover
  assume "z \<in> \<nu>1 \<times> \<nu>2"
  moreover from calculation
  have "f`fst(z): \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>" by simp
  ultimately
  show "f`fst(z)`snd(z) \<in> \<kappa>"
    using mem_function_space_rel_abs by (auto dest:transM)
next \<comment> \<open>one composition is the identity:\<close>
  let ?cur="\<lambda>x. \<lambda>w\<in>\<nu>1 \<times> \<nu>2. x ` fst(w) ` snd(w)"
  fix f
  assume "f : \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>"
  with assms
  show "?cur(\<lambda>x\<in>\<nu>1. \<lambda>xa\<in>\<nu>2. f ` \<langle>x, xa\<rangle>) = f"
    using function_space_rel_char mem_function_space_rel_abs
    by (auto dest:transM intro:fun_extension)
  fix x y
  assume "x\<in>\<nu>1" "y\<in>\<nu>2"
  with assms \<open>f : \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>\<close>
  show "f`\<langle>x,y\<rangle> \<in> \<kappa>"
    using function_space_rel_char mem_function_space_rel_abs
    by (auto dest:transM[of _ "\<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>"])
next
  let ?cur="\<lambda>x. \<lambda>w\<in>\<nu>1 \<times> \<nu>2. x ` fst(w) ` snd(w)"
  note assms
  moreover from this
  show "\<forall>x[M]. M(?cur(x))"
    using  lam_replacement_fst lam_replacement_snd
      lam_replacement_apply2[THEN [5] lam_replacement_hcomp2,
        THEN [1] lam_replacement_hcomp2, where h="(`)", OF
        lam_replacement_constant] lam_replacement_apply2
    by (auto intro: lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
  moreover from calculation
  show "x \<in> \<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>) \<Longrightarrow> M(?cur(x))" for x
    by (auto dest:transM)
  moreover from assms
  show "lam_replacement(M, ?cur)"
    using lam_replacement_Lambda_apply_fst_snd by simp
  ultimately
  show "M(\<lambda>x\<in>\<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>). ?cur(x))"
    using lam_replacement_iff_lam_closed
    by (auto dest:transM)
  from assms
  show "y \<in> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa> \<Longrightarrow> x \<in> \<nu>1 \<Longrightarrow> M(\<lambda>xa\<in>\<nu>2. y ` \<langle>x, xa\<rangle>)" for x y
    using lam_replacement_apply_const_id
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
      (auto dest:transM)
  from assms
  show "y \<in> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa> \<Longrightarrow> M(\<lambda>x\<in>\<nu>1. \<lambda>xa\<in>\<nu>2. y ` \<langle>x, xa\<rangle>)" for y
    using lam_replacement_apply2[THEN [5] lam_replacement_hcomp2,
        OF lam_replacement_constant lam_replacement_const_id]
      lam_replacement_Lambda_apply_Pair[of \<nu>2]
    by (auto dest:transM
        intro!: lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
qed

lemma Pow_rel_eqpoll_rel_function_space_rel:
  fixes d X
  notes bool_of_o_def [simp]
  defines [simp]:"d(A) \<equiv> (\<lambda>x\<in>X. bool_of_o(x\<in>A))"
    \<comment> \<open>the witnessing map for the thesis:\<close>
  assumes "M(X)"
  shows "Pow\<^bsup>M\<^esup>(X) \<approx>\<^bsup>M\<^esup> X \<rightarrow>\<^bsup>M\<^esup> 2"
proof -
  from assms
  interpret M_Pi_assumptions M X "\<lambda>_. 2"
    using Pi_replacement Pi_separation lam_replacement_identity
      lam_replacement_Sigfun[THEN lam_replacement_imp_strong_replacement]
      Pi_replacement1[of _ 2] transM[of _ X] lam_replacement_constant
    by unfold_locales auto
  have "lam_replacement(M, \<lambda>x. bool_of_o(x\<in>A))" if "M(A)" for A
    using that lam_replacement_if lam_replacement_constant
      separation_in_constant by simp
  with assms
  have "lam_replacement(M, \<lambda>x. d(x))"
    using separation_in_constant[THEN [3] lam_replacement_if, of "\<lambda>_.1" "\<lambda>_.0"]
      lam_replacement_identity lam_replacement_constant lam_replacement_Lambda_if_mem
    by simp
  show ?thesis
    unfolding eqpoll_rel_def
  proof (intro rexI, rule lam_bijective_rel)
    \<comment> \<open>We give explicit mutual inverses\<close>
    fix A
    assume "A\<in>Pow\<^bsup>M\<^esup>(X)"
    moreover
    note \<open>M(X)\<close>
    moreover from calculation
    have "M(A)" by (auto dest:transM)
    moreover
    note \<open>_ \<Longrightarrow> lam_replacement(M, \<lambda>x. bool_of_o(x\<in>A))\<close>
    ultimately
    show "d(A) : X \<rightarrow>\<^bsup>M\<^esup> 2"
      using function_space_rel_char lam_replacement_iff_lam_closed[THEN iffD1]
      by (simp, rule_tac lam_type[of X "\<lambda>x. bool_of_o(x\<in>A)" "\<lambda>_. 2", simplified])
        auto
    from \<open>A\<in>Pow\<^bsup>M\<^esup>(X)\<close> \<open>M(X)\<close>
    show "{y\<in>X. d(A)`y = 1} = A"
      using Pow_rel_char by auto
  next
    fix f
    assume "f: X\<rightarrow>\<^bsup>M\<^esup> 2"
    with assms
    have "f: X\<rightarrow> 2" "M(f)" using function_space_rel_char by simp_all
    then
    show "d({y \<in> X . f ` y = 1}) = f"
      using apply_type[OF \<open>f: X\<rightarrow>2\<close>] by (force intro:fun_extension)
    from \<open>M(X)\<close> \<open>M(f)\<close>
    show "{ya \<in> X . f ` ya = 1} \<in> Pow\<^bsup>M\<^esup>(X)"
      using Pow_rel_char separation_equal_apply by auto
  next
    from assms \<open>lam_replacement(M, \<lambda>x. d(x))\<close>
      \<open>\<And>A. _ \<Longrightarrow> lam_replacement(M, \<lambda>x. bool_of_o(x\<in>A))\<close>
    show "M(\<lambda>x\<in>Pow\<^bsup>M\<^esup>(X). d(x))" "lam_replacement(M, \<lambda>x. d(x))"
      "\<forall>x[M]. M(d(x))"
      using lam_replacement_iff_lam_closed[THEN iffD1] by auto
  qed (auto simp:\<open>M(X)\<close>)
qed

lemma Pow_rel_bottom: "M(B) \<Longrightarrow> 0 \<in> Pow\<^bsup>M\<^esup>(B)"
  using Pow_rel_char by simp

lemma cantor_surj_rel:
  assumes "M(f)" "M(A)"
  shows "f \<notin> surj\<^bsup>M\<^esup>(A,Pow\<^bsup>M\<^esup>(A))"
proof
  assume "f \<in> surj\<^bsup>M\<^esup>(A,Pow\<^bsup>M\<^esup>(A))"
  with assms
  have "f \<in> surj(A,Pow\<^bsup>M\<^esup>(A))" using surj_rel_char by simp
  moreover
  note assms
  moreover from this
  have "M({x \<in> A . x \<in> f ` x})" "{x \<in> A . x \<notin> f ` x} = A - {x \<in> A . x \<in> f ` x}"
    using lam_replacement_apply[THEN [4] separation_in, of  "\<lambda>x. x"]
      lam_replacement_identity lam_replacement_constant by auto
  with \<open>M(A)\<close>
  have "{x\<in>A . x \<notin> f`x} \<in> Pow\<^bsup>M\<^esup>(A)"
    by (intro mem_Pow_rel_abs[THEN iffD2]) auto
  ultimately
  obtain d where "d\<in>A" "f`d = {x\<in>A . x \<notin> f`x}"
    unfolding surj_def by blast
  show False
  proof (cases "d \<in> f`d")
    case True
    note \<open>d \<in> f`d\<close>
    also
    note \<open>f`d = {x\<in>A . x \<notin> f`x}\<close>
    finally
    have "d \<notin> f`d" using \<open>d\<in>A\<close> by simp
    then
    show False using \<open>d \<in> f ` d\<close> by simp
  next
    case False
    with \<open>d\<in>A\<close>
    have "d \<in> {x\<in>A . x \<notin> f`x}" by simp
    also from \<open>f`d = \<dots>\<close>
    have "\<dots> = f`d" by simp
    finally
    show False using \<open>d \<notin> f`d\<close> by simp
  qed
qed

lemma cantor_inj_rel: "M(f) \<Longrightarrow> M(A) \<Longrightarrow> f \<notin> inj\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A),A)"
  using inj_rel_imp_surj_rel[OF _ Pow_rel_bottom, of f A A]
    cantor_surj_rel[of "\<lambda>x\<in>A. if x \<in> range(f) then converse(f) ` x else 0" A]
    lam_replacement_if separation_in_constant[of "range(f)"]
    lam_replacement_converse_app[THEN [5] lam_replacement_hcomp2]
    lam_replacement_identity lam_replacement_constant
    lam_replacement_iff_lam_closed by auto

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

end