section\<open>Relative, Cardinal Arithmetic Using AC\<close>

theory Cardinal_AC_Relative
  imports
    CardinalArith_Relative

begin

locale M_AC =
  fixes M
  assumes
    choice_ax: "choice_ax(M)"

locale M_cardinal_AC = M_cardinal_arith + M_AC
begin

lemma well_ord_surj_imp_lepoll_rel:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)" and
    types:"M(A)" "M(r)" "M(h)" "M(B)"
  shows "B \<lesssim>\<^bsup>M\<^esup> A"
proof -
  note eq=vimage_fun_sing[OF surj_is_fun[OF \<open>h\<in>_\<close>]]
  from assms
  have "(\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})) \<in> inj(B,A)" (is "?f\<in>_")
    using well_ord_surj_imp_inj_inverse assms(1,2) by simp
  with assms
  have "M(?f`b)" if "b\<in>B" for b
    using apply_type[OF inj_is_fun[OF \<open>?f\<in>_\<close>]] that transM[OF _ \<open>M(A)\<close>] by simp
  with assms
  have "M(?f)"
    using lam_closed surj_imp_inj_replacement4 eq by auto
  with \<open>?f\<in>_\<close> assms
  have "?f \<in> inj\<^bsup>M\<^esup>(B,A)"
    using mem_inj_abs by simp
  with \<open>M(?f)\<close>
  show ?thesis unfolding lepoll_rel_def by auto
qed

lemma surj_imp_well_ord_M:
  assumes wos: "well_ord(A,r)" "h \<in> surj(A,B)"
    and
    types: "M(A)" "M(r)" "M(h)" "M(B)"
  shows "\<exists>s[M]. well_ord(B,s)"
  using assms lepoll_rel_well_ord
    well_ord_surj_imp_lepoll_rel by fast


lemma choice_ax_well_ord: "M(S) \<Longrightarrow> \<exists>r[M]. well_ord(S,r)"
  using choice_ax well_ord_Memrel[THEN surj_imp_well_ord_M]
  unfolding choice_ax_def by auto

lemma Finite_cardinal_rel_Finite:
  assumes "Finite(|i|\<^bsup>M\<^esup>)" "M(i)"
  shows "Finite(i)"
proof -
  note assms
  moreover from this
  obtain r where "M(r)" "well_ord(i,r)"
    using choice_ax_well_ord by auto
  moreover from calculation
  have "|i|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> i"
    using well_ord_cardinal_rel_eqpoll_rel
    by auto
  ultimately
  show ?thesis
    using eqpoll_rel_imp_Finite
    by auto
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_AC\<close>\<close>

locale M_Pi_assumptions_choice = M_Pi_assumptions + M_cardinal_AC +
  assumes
    B_replacement: "strong_replacement(M, \<lambda>x y. y = B(x))"
    and
    \<comment> \<open>The next one should be derivable from (some variant)
        of B\_replacement. Proving both instances each time seems
        inconvenient.\<close>
    minimum_replacement: "M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, B(x))\<rangle>)"
begin

lemma AC_M:
  assumes "a \<in> A" "\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> B(x)"
  shows "\<exists>z[M]. z \<in> Pi\<^bsup>M\<^esup>(A, B)"
proof -
  have "M(\<Union>x\<in>A. B(x))" using assms family_union_closed Pi_assumptions B_replacement by simp
  then
  obtain r where "well_ord(\<Union>x\<in>A. B(x),r)" "M(r)"
    using choice_ax_well_ord by blast
  let ?f="\<lambda>x\<in>A. minimum(r,B(x))"
  have "M(minimum(r, B(x)))" if "x\<in>A" for x
  proof -
    from \<open>well_ord(_,r)\<close> \<open>x\<in>A\<close>
    have "well_ord(B(x),r)" using well_ord_subset UN_upper by simp
    with assms \<open>x\<in>A\<close> \<open>M(r)\<close>
    show ?thesis using Pi_assumptions by blast
  qed
  with assms and \<open>M(r)\<close>
  have "M(?f)"
    using Pi_assumptions minimum_replacement lam_closed
    by simp
  moreover from assms and calculation
  have "?f \<in> Pi\<^bsup>M\<^esup>(A,B)"
    using lam_type[OF minimum_in, OF \<open>well_ord(\<Union>x\<in>A. B(x),r)\<close>, of A B]
      Pi_rel_char by auto
  ultimately
  show ?thesis by blast
qed

lemma AC_Pi_rel: assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> B(x)"
  shows "\<exists>z[M]. z \<in> Pi\<^bsup>M\<^esup>(A, B)"
proof (cases "A=0")
  interpret Pi0:M_Pi_assumptions_0
    using Pi_assumptions by unfold_locales auto
  case True
  then
  show ?thesis using assms by simp
next
  case False
  then
  obtain a where "a \<in> A" by auto
      \<comment> \<open>It is noteworthy that without obtaining an element of
        \<^term>\<open>A\<close>, the final step won't work\<close>
  with assms
  show ?thesis by (blast intro!: AC_M)
qed

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions_choice\<close>\<close>


context M_cardinal_AC
begin

subsection\<open>Strengthened Forms of Existing Theorems on Cardinals\<close>

lemma cardinal_rel_eqpoll_rel: "M(A) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> A"
  apply (rule choice_ax_well_ord [THEN rexE])
   apply (auto intro:well_ord_cardinal_rel_eqpoll_rel)
  done

lemmas cardinal_rel_idem = cardinal_rel_eqpoll_rel [THEN cardinal_rel_cong, simp]

lemma cardinal_rel_eqE: "|X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup> ==> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>\<^bsup>M\<^esup> Y"
  apply (rule choice_ax_well_ord [THEN rexE], assumption)
  apply (rule choice_ax_well_ord [THEN rexE, of Y], assumption)
  apply (rule well_ord_cardinal_rel_eqE, assumption+)
  done

lemma cardinal_rel_eqpoll_rel_iff: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> |X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup> \<longleftrightarrow> X \<approx>\<^bsup>M\<^esup> Y"
  by (blast intro: cardinal_rel_cong cardinal_rel_eqE)

lemma cardinal_rel_disjoint_Un:
  "[| |A|\<^bsup>M\<^esup>=|B|\<^bsup>M\<^esup>;  |C|\<^bsup>M\<^esup>=|D|\<^bsup>M\<^esup>;  A \<inter> C = 0;  B \<inter> D = 0; M(A); M(B); M(C); M(D)|]
      ==> |A \<union> C|\<^bsup>M\<^esup> = |B \<union> D|\<^bsup>M\<^esup>"
  by (simp add: cardinal_rel_eqpoll_rel_iff eqpoll_rel_disjoint_Un)

lemma lepoll_rel_imp_cardinal_rel_le: "A \<lesssim>\<^bsup>M\<^esup> B ==> M(A) \<Longrightarrow> M(B) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (erule well_ord_lepoll_rel_imp_cardinal_rel_le, assumption+)
  done

lemma cadd_rel_assoc: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<oplus>\<^bsup>M\<^esup> j) \<oplus>\<^bsup>M\<^esup> k = i \<oplus>\<^bsup>M\<^esup> (j \<oplus>\<^bsup>M\<^esup> k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cadd_rel_assoc, assumption+)
  done

lemma cmult_rel_assoc: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<otimes>\<^bsup>M\<^esup> j) \<otimes>\<^bsup>M\<^esup> k = i \<otimes>\<^bsup>M\<^esup> (j \<otimes>\<^bsup>M\<^esup> k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cmult_rel_assoc, assumption+)
  done

lemma cadd_cmult_distrib: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<oplus>\<^bsup>M\<^esup> j) \<otimes>\<^bsup>M\<^esup> k = (i \<otimes>\<^bsup>M\<^esup> k) \<oplus>\<^bsup>M\<^esup> (j \<otimes>\<^bsup>M\<^esup> k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cadd_cmult_distrib, assumption+)
  done


lemma InfCard_rel_square_eq: "InfCard\<^bsup>M\<^esup>(|A|\<^bsup>M\<^esup>) \<Longrightarrow> M(A) \<Longrightarrow> A\<times>A \<approx>\<^bsup>M\<^esup> A"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (erule well_ord_InfCard_rel_square_eq, assumption, simp_all)
  done

subsection \<open>The relationship between cardinality and le-pollence\<close>

lemma Card_rel_le_imp_lepoll_rel:
  assumes "|A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
    and types: "M(A)" "M(B)"
  shows "A \<lesssim>\<^bsup>M\<^esup> B"
proof -
  have "A \<approx>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
    by (rule cardinal_rel_eqpoll_rel [THEN eqpoll_rel_sym], simp_all add:types)
  also have "... \<lesssim>\<^bsup>M\<^esup> |B|\<^bsup>M\<^esup>"
    by (rule le_imp_subset [THEN subset_imp_lepoll_rel]) (rule assms, simp_all add:types)
  also have "... \<approx>\<^bsup>M\<^esup> B"
    by (rule cardinal_rel_eqpoll_rel, simp_all add:types)
  finally show ?thesis by (simp_all add:types)
qed

lemma le_Card_rel_iff: "Card\<^bsup>M\<^esup>(K) ==> M(K) \<Longrightarrow> M(A) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> K \<longleftrightarrow> A \<lesssim>\<^bsup>M\<^esup> K"
  apply (erule Card_rel_cardinal_rel_eq [THEN subst], assumption, rule iffI,
      erule Card_rel_le_imp_lepoll_rel, assumption+)
  apply (erule lepoll_rel_imp_cardinal_rel_le, assumption+)
  done

lemma cardinal_rel_0_iff_0 [simp]: "M(A) \<Longrightarrow> |A|\<^bsup>M\<^esup> = 0 \<longleftrightarrow> A = 0"
  using cardinal_rel_0 eqpoll_rel_0_iff [THEN iffD1]
    cardinal_rel_eqpoll_rel_iff [THEN iffD1, OF _ nonempty]
  by auto

lemma cardinal_rel_lt_iff_lesspoll_rel:
  assumes i: "Ord(i)" and
    types: "M(i)" "M(A)"
  shows "i < |A|\<^bsup>M\<^esup> \<longleftrightarrow> i \<prec>\<^bsup>M\<^esup> A"
proof
  assume "i < |A|\<^bsup>M\<^esup>"
  hence  "i \<prec>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
    by (blast intro: lt_Card_rel_imp_lesspoll_rel types)
  also have "...  \<approx>\<^bsup>M\<^esup> A"
    by (rule cardinal_rel_eqpoll_rel) (simp_all add:types)
  finally show "i \<prec>\<^bsup>M\<^esup> A" by (simp_all add:types)
next
  assume "i \<prec>\<^bsup>M\<^esup> A"
  also have "...  \<approx>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
    by (blast intro: cardinal_rel_eqpoll_rel eqpoll_rel_sym types)
  finally have "i \<prec>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>" by (simp_all add:types)
  thus  "i < |A|\<^bsup>M\<^esup>" using i types
    by (force intro: cardinal_rel_lt_imp_lt lesspoll_rel_cardinal_rel_lt)
qed

lemma cardinal_rel_le_imp_lepoll_rel: " i \<le> |A|\<^bsup>M\<^esup> ==> M(i) \<Longrightarrow> M(A) \<Longrightarrow>i \<lesssim>\<^bsup>M\<^esup> A"
  by (blast intro: lt_Ord Card_rel_le_imp_lepoll_rel Ord_cardinal_rel_le le_trans)


subsection\<open>Other Applications of AC\<close>

text\<open>We have an example of instantiating a locale involving higher
order variables inside a proof, by using the assumptions of the
first order, active locale.\<close>

lemma surj_rel_implies_inj_rel:
  assumes f: "f \<in> surj\<^bsup>M\<^esup>(X,Y)" and
    types: "M(f)" "M(X)" "M(Y)"
  shows "\<exists>g[M]. g \<in> inj\<^bsup>M\<^esup>(Y,X)"
proof -
  from types
  interpret M_Pi_assumptions_choice _ Y "\<lambda>y. f-``{y}"
    by unfold_locales (auto intro:surj_imp_inj_replacement dest:transM)
  from f AC_Pi_rel
  obtain z where z: "z \<in> Pi\<^bsup>M\<^esup>(Y, \<lambda>y. f -`` {y})"
    \<comment> \<open>In this and the following ported result, it is not clear how
        uniformly are "\_char" theorems to be used\<close>
    using surj_rel_char
    by (auto simp add: surj_def types) (fast dest: apply_Pair)
  show ?thesis
  proof
    show "z \<in> inj\<^bsup>M\<^esup>(Y, X)" "M(z)"
      using z surj_is_fun[of f X Y] f Pi_rel_char
      by (auto dest: apply_type Pi_memberD
          intro: apply_equality Pi_type f_imp_injective
          simp add:types mem_surj_abs)
  qed
qed


text\<open>Kunen's Lemma 10.20\<close>
lemma surj_rel_implies_cardinal_rel_le:
  assumes f: "f \<in> surj\<^bsup>M\<^esup>(X,Y)" and
    types:"M(f)" "M(X)" "M(Y)"
  shows "|Y|\<^bsup>M\<^esup> \<le> |X|\<^bsup>M\<^esup>"
proof (rule lepoll_rel_imp_cardinal_rel_le)
  from f [THEN surj_rel_implies_inj_rel]
  obtain g where "g \<in> inj\<^bsup>M\<^esup>(Y,X)"
    by (blast intro:types)
  then
  show "Y \<lesssim>\<^bsup>M\<^esup> X"
    using inj_rel_char
    by (auto simp add: def_lepoll_rel types)
qed (simp_all add:types)

end \<comment> \<open>\<^locale>\<open>M_cardinal_AC\<close>\<close>

text\<open>The set-theoretic universe.\<close>

abbreviation
  Universe :: "i\<Rightarrow>o" (\<open>\<V>\<close>) where
  "\<V>(x) \<equiv> True"

lemma separation_absolute: "separation(\<V>, P)"
  unfolding separation_def
  by (rule rallI, rule_tac x="{x\<in>_ . P(x)}" in rexI) auto

lemma univalent_absolute:
  assumes "univalent(\<V>, A, P)" "P(x, b)" "x \<in> A"
  shows "P(x, y) \<Longrightarrow> y = b"
  using assms
  unfolding univalent_def by force

lemma replacement_absolute: "strong_replacement(\<V>, P)"
  unfolding strong_replacement_def
proof (intro rallI impI)
  fix A
  assume "univalent(\<V>, A, P)"
  then
  show "\<exists>Y[\<V>]. \<forall>b[\<V>]. b \<in> Y \<longleftrightarrow> (\<exists>x[\<V>]. x \<in> A \<and> P(x, b))"
    by (rule_tac x="{y. x\<in>A , P(x,y)}" in rexI)
      (auto dest:univalent_absolute[of _ P])
qed

lemma Union_ax_absolute: "Union_ax(\<V>)"
  unfolding Union_ax_def big_union_def
  by (auto intro:rexI[of _ "\<Union>_"])

lemma upair_ax_absolute: "upair_ax(\<V>)"
  unfolding upair_ax_def upair_def rall_def rex_def
  by (auto)

lemma power_ax_absolute:"power_ax(\<V>)"
proof -
  {
    fix x
    have "\<forall>y[\<V>]. y \<in> Pow(x) \<longleftrightarrow> (\<forall>z[\<V>]. z \<in> y \<longrightarrow> z \<in> x)"
      by auto
  }
  then
  show "power_ax(\<V>)"
    unfolding power_ax_def powerset_def subset_def by blast
qed

locale M_cardinal_UN =  M_Pi_assumptions_choice _ K X for K X +
  assumes
    \<comment> \<open>The next assumption is required by @{thm Least_closed}\<close>
    X_witness_in_M: "w \<in> X(x) \<Longrightarrow> M(x)"
    and
    lam_m_replacement:"M(f) \<Longrightarrow> strong_replacement(M,
      \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> X(i), f ` (\<mu> i. x \<in> X(i)) ` x\<rangle>)"
    and
    inj_replacement:
    "M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(X(x), K) \<and> z = {\<langle>x, y\<rangle>})"
    "strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(X(x), K))"
    "strong_replacement(M,
      \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(X(i), K)))"
    "M(r) \<Longrightarrow> strong_replacement(M,
      \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(X(x), K))\<rangle>)"

begin

lemma UN_closed: "M(\<Union>i\<in>K. X(i))"
  using family_union_closed B_replacement Pi_assumptions by simp

text\<open>Kunen's Lemma 10.21\<close>
lemma cardinal_rel_UN_le:
  assumes K: "InfCard\<^bsup>M\<^esup>(K)"
  shows "(\<And>i. i\<in>K \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K) \<Longrightarrow> |\<Union>i\<in>K. X(i)|\<^bsup>M\<^esup> \<le> K"
proof (simp add: K InfCard_rel_is_Card_rel le_Card_rel_iff Pi_assumptions)
  have "M(f) \<Longrightarrow> M(\<lambda>x\<in>(\<Union>x\<in>K. X(x)). \<langle>\<mu> i. x \<in> X(i), f ` (\<mu> i. x \<in> X(i)) ` x\<rangle>)" for f
    using lam_m_replacement X_witness_in_M Least_closed' Pi_assumptions UN_closed
    by (rule_tac lam_closed) (auto dest:transM)
  note types = this Pi_assumptions UN_closed
  have [intro]: "Ord(K)" by (blast intro: InfCard_rel_is_Card_rel
        Card_rel_is_Ord K types)
  interpret pii:M_Pi_assumptions_choice _ K "\<lambda>i. inj\<^bsup>M\<^esup>(X(i), K)"
    using inj_replacement Pi_assumptions transM[of _ K]
    by unfold_locales (simp_all del:mem_inj_abs)
  assume asm:"\<And>i. i\<in>K \<Longrightarrow> X(i) \<lesssim>\<^bsup>M\<^esup> K"
  then
  have "\<And>i. i\<in>K \<Longrightarrow> M(inj\<^bsup>M\<^esup>(X(i), K))"
    by (auto simp add: types)
  interpret V:M_N_Perm M "\<V>"
    using separation_absolute replacement_absolute Union_ax_absolute
      power_ax_absolute upair_ax_absolute
    by unfold_locales auto
  note bad_simps[simp del] = V.N.Forall_in_M_iff V.N.Equal_in_M_iff
    V.N.nonempty
  have abs:"inj_rel(\<V>,x,y) = inj(x,y)" for x y
    using V.N.inj_rel_char by simp
  from asm
  have "\<And>i. i\<in>K \<Longrightarrow> \<exists>f[M]. f \<in> inj\<^bsup>M\<^esup>(X(i), K)"
    by (simp add: types def_lepoll_rel)
  then
  obtain f where "f \<in> (\<Prod>i\<in>K. inj\<^bsup>M\<^esup>(X(i), K))" "M(f)"
    using pii.AC_Pi_rel pii.Pi_rel_char by auto
  with abs
  have f:"f \<in> (\<Prod>i\<in>K. inj(X(i), K))"
    using Pi_weaken_type[OF _ V.inj_rel_transfer, of f K X "\<lambda>_. K"]
      Pi_assumptions by simp
  { fix z
    assume z: "z \<in> (\<Union>i\<in>K. X(i))"
    then obtain i where i: "i \<in> K" "Ord(i)" "z \<in> X(i)"
      by (blast intro: Ord_in_Ord [of K])
    hence "(\<mu> i. z \<in> X(i)) \<le> i" by (fast intro: Least_le)
    hence "(\<mu> i. z \<in> X(i)) < K" by (best intro: lt_trans1 ltI i)
    hence "(\<mu> i. z \<in> X(i)) \<in> K" and "z \<in> X(\<mu> i. z \<in> X(i))"
      by (auto intro: LeastI ltD i)
  } note mems = this
  have "(\<Union>i\<in>K. X(i)) \<lesssim>\<^bsup>M\<^esup> K \<times> K"
  proof (simp add:types def_lepoll_rel)
    show "\<exists>f[M]. f \<in> inj(\<Union>x\<in>K. X(x), K \<times> K)"
      apply (rule rexI)
       apply (rule_tac c = "\<lambda>z. \<langle>\<mu> i. z \<in> X(i), f ` (\<mu> i. z \<in> X(i)) ` z\<rangle>"
          and d = "\<lambda>\<langle>i,j\<rangle>. converse (f`i) ` j" in lam_injective)
        apply (force intro: f inj_is_fun mems apply_type Perm.left_inverse)+
      apply (simp add:types \<open>M(f)\<close>)
      done
  qed
  also have "... \<approx>\<^bsup>M\<^esup> K"
    by (simp add: K InfCard_rel_square_eq InfCard_rel_is_Card_rel
        Card_rel_cardinal_rel_eq types)
  finally have "(\<Union>i\<in>K. X(i)) \<lesssim>\<^bsup>M\<^esup> K" by (simp_all add:types)
  then
  show ?thesis
    by (simp add: K InfCard_rel_is_Card_rel le_Card_rel_iff types)
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_UN\<close>\<close>

end