section\<open>Cardinal Arithmetic under Choice\label{sec:cardinal-lib-rel}\<close>

theory Cardinal_Library_Relative
  imports
    Replacement_Lepoll
begin

locale M_library = M_ZF_library + M_cardinal_AC +
  assumes
    separation_cardinal_rel_lesspoll_rel: "M(\<kappa>) \<Longrightarrow> separation(M, \<lambda>x . x \<prec>\<^bsup>M\<^esup> \<kappa>)"
begin

declare eqpoll_rel_refl [simp]

subsection\<open>Miscellaneous\<close>

lemma cardinal_rel_RepFun_apply_le:
  assumes "S \<in> A\<rightarrow>B" "M(S)" "M(A)" "M(B)"
  shows "|{S`a . a\<in>A}|\<^bsup>M\<^esup> \<le> |A|\<^bsup>M\<^esup>"
proof -
  note assms
  moreover from this
  have "{S ` a . a \<in> A} = S``A"
    using image_eq_UN RepFun_def UN_iff by force
  moreover from calculation
  have "M(\<lambda>x\<in>A. S ` x)" "M({S ` a . a \<in> A})"
    using lam_closed[of "\<lambda> x. S`x"] apply_type[OF \<open>S\<in>_\<close>]
      transM[OF _ \<open>M(B)\<close>] image_closed
    by auto
  moreover from assms this
  have "(\<lambda>x\<in>A. S`x) \<in> surj_rel(M,A, {S`a . a\<in>A})"
    using mem_surj_abs lam_funtype[of A "\<lambda>x . S`x"]
    unfolding surj_def by auto
  ultimately
  show ?thesis
    using surj_rel_char surj_rel_implies_cardinal_rel_le by simp
qed

(* TODO: Check if we can use this lemma to prove the previous one and
    not the other way around *)
lemma cardinal_rel_RepFun_le:
  assumes lrf:"lam_replacement(M,f)" and f_closed:"\<forall>x[M]. M(f(x))" and "M(X)"
  shows "|{f(x) . x \<in> X}|\<^bsup>M\<^esup> \<le> |X|\<^bsup>M\<^esup>"
  using \<open>M(X)\<close> f_closed cardinal_rel_RepFun_apply_le[OF lam_funtype, of X _, OF
      lrf[THEN [2] lam_replacement_iff_lam_closed[THEN iffD1, THEN rspec]]]
    lrf[THEN lam_replacement_imp_strong_replacement]
  by simp (auto simp flip:setclass_iff intro!:RepFun_closed dest:transM)

lemma subset_imp_le_cardinal_rel: "A \<subseteq> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
  using subset_imp_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le] .

lemma lt_cardinal_rel_imp_not_subset: "|A|\<^bsup>M\<^esup> < |B|\<^bsup>M\<^esup> \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> \<not> B \<subseteq> A"
  using subset_imp_le_cardinal_rel le_imp_not_lt  by blast

lemma cardinal_rel_lt_csucc_rel_iff:
  "Card_rel(M,K) \<Longrightarrow> M(K) \<Longrightarrow> M(K') \<Longrightarrow> |K'|\<^bsup>M\<^esup> < (K\<^sup>+)\<^bsup>M\<^esup> \<longleftrightarrow> |K'|\<^bsup>M\<^esup> \<le> K"
  by (simp add: Card_rel_lt_csucc_rel_iff)

end \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

locale M_cardinal_UN_nat = M_cardinal_UN _ \<omega> X for X
begin
lemma cardinal_rel_UN_le_nat:
  assumes "\<And>i. i\<in>\<omega> \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> \<omega>"
  shows "|\<Union>i\<in>\<omega>. X(i)|\<^bsup>M\<^esup> \<le> \<omega>"
proof -
  from assms
  show ?thesis
    by (simp add: cardinal_rel_UN_le InfCard_rel_nat)
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_UN_nat\<close>\<close>

locale M_cardinal_UN_inj = M_library +
  j:M_cardinal_UN _ J +
  y:M_cardinal_UN _ K "\<lambda>k. if k\<in>range(f) then X(converse(f)`k) else 0" for J K f +
assumes
  f_inj: "f \<in> inj_rel(M,J,K)"
begin

lemma inj_rel_imp_cardinal_rel_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  fixes Y
  defines "Y(k) \<equiv> if k\<in>range(f) then X(converse(f)`k) else 0"
  assumes "InfCard\<^bsup>M\<^esup>(K)" "\<And>i. i\<in>J \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K"
  shows "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
proof -
  have "M(K)" "M(J)" "\<And>w x. w \<in> X(x) \<Longrightarrow> M(x)"
    using y.Pi_assumptions j.Pi_assumptions j.X_witness_in_M by simp_all
  then
  have "M(f)"
    using inj_rel_char f_inj by simp
  note inM = \<open>M(f)\<close> \<open>M(K)\<close> \<open>M(J)\<close> \<open>\<And>w x. w \<in> X(x) \<Longrightarrow> M(x)\<close>
  have "i\<in>J \<Longrightarrow> f`i \<in> K" for i
    using inj_rel_is_fun[OF f_inj] apply_type
      function_space_rel_char by (auto simp add:inM)
  have "(\<Union>i\<in>J. X(i)) \<subseteq> (\<Union>i\<in>K. Y(i))"
  proof (standard, elim UN_E)
    fix x i
    assume "i\<in>J" "x\<in>X(i)"
    with \<open>i\<in>J \<Longrightarrow> f`i \<in> K\<close>
    have "x \<in> Y(f`i)" "f`i \<in> K"
      unfolding Y_def
      using inj_is_fun right_inverse f_inj
      by (auto simp add:inM Y_def intro: apply_rangeI)
    then
    show "x \<in> (\<Union>i\<in>K. Y(i))" by auto
  qed
  then
  have "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> |\<Union>i\<in>K. Y(i)|\<^bsup>M\<^esup>"
    using subset_imp_le_cardinal_rel j.UN_closed y.UN_closed
    unfolding Y_def by (simp add:inM)
  moreover
  note assms \<open>\<And>i. i\<in>J \<Longrightarrow> f`i \<in> K\<close> inM
  moreover from this
  have "k\<in>range(f) \<Longrightarrow> converse(f)`k \<in> J" for k
    using inj_rel_converse_fun[OF f_inj]
      range_fun_subset_codomain function_space_rel_char by simp
  ultimately
  show "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
    using InfCard_rel_is_Card_rel[THEN Card_rel_is_Ord,THEN Ord_0_le, of K]
    by (rule_tac le_trans[OF _ y.cardinal_rel_UN_le])
      (auto intro:Ord_0_le simp:Y_def)+
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_UN_inj\<close>\<close>

locale M_cardinal_UN_lepoll = M_library + M_replacement_lepoll _ "\<lambda>_. X" +
  j:M_cardinal_UN _ J for J
begin

(* FIXME: this "LEQpoll" should be "LEPOLL"; same correction in Delta System *)
lemma leqpoll_rel_imp_cardinal_rel_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  assumes "InfCard\<^bsup>M\<^esup>(K)" "J \<lesssim>\<^bsup>M\<^esup> K" "\<And>i. i\<in>J \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K"
    "M(K)"
  shows "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
proof -
  from \<open>J \<lesssim>\<^bsup>M\<^esup> K\<close>
  obtain f where "f \<in> inj_rel(M,J,K)" "M(f)" by blast
  moreover
  let ?Y="\<lambda>k. if k\<in>range(f) then X(converse(f)`k) else 0"
  note \<open>M(K)\<close>
  moreover from calculation
  have "k \<in> range(f) \<Longrightarrow> converse(f)`k \<in> J" for k
    using mem_inj_rel[THEN inj_converse_fun, THEN apply_type]
      j.Pi_assumptions by blast
  moreover from \<open>M(f)\<close>
  have "w \<in> ?Y(x) \<Longrightarrow> M(x)" for w x
    by (cases "x\<in>range(f)") (auto dest:transM)
  moreover from calculation
  interpret M_Pi_assumptions_choice _ K ?Y
    using j.Pi_assumptions lepoll_assumptions
  proof (unfold_locales, auto dest:transM)
    show "strong_replacement(M, \<lambda>y z. False)"
      unfolding strong_replacement_def by auto
  qed
  from calculation
  interpret M_cardinal_UN_inj _ _ _ _ f
    using lepoll_assumptions
    by unfold_locales auto
  from assms
  show ?thesis using inj_rel_imp_cardinal_rel_UN_le by simp
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_UN_lepoll\<close>\<close>

context M_library
begin

lemma cardinal_rel_lt_csucc_rel_iff':
  includes Ord_dests
  assumes "Card_rel(M,\<kappa>)"
    and types:"M(\<kappa>)" "M(X)"
  shows "\<kappa> < |X|\<^bsup>M\<^esup> \<longleftrightarrow> (\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<le> |X|\<^bsup>M\<^esup>"
  using assms cardinal_rel_lt_csucc_rel_iff[of \<kappa> X] Card_rel_csucc_rel[of \<kappa>]
    not_le_iff_lt[of "(\<kappa>\<^sup>+)\<^bsup>M\<^esup>" "|X|\<^bsup>M\<^esup>"] not_le_iff_lt[of "|X|\<^bsup>M\<^esup>" \<kappa>]
  by blast

lemma lepoll_rel_imp_subset_bij_rel:
  assumes "M(X)" "M(Y)"
  shows "X \<lesssim>\<^bsup>M\<^esup> Y \<longleftrightarrow> (\<exists>Z[M]. Z \<subseteq> Y \<and> Z \<approx>\<^bsup>M\<^esup> X)"
proof
  assume "X \<lesssim>\<^bsup>M\<^esup> Y"
  then
  obtain j where  "j \<in> inj_rel(M,X,Y)"
    by blast
  with assms
  have "range(j) \<subseteq> Y" "j \<in> bij_rel(M,X,range(j))" "M(range(j))" "M(j)"
    using inj_rel_bij_rel_range inj_rel_char
      inj_rel_is_fun[THEN range_fun_subset_codomain,of j X Y]
    by auto
  with assms
  have "range(j) \<subseteq> Y" "X \<approx>\<^bsup>M\<^esup> range(j)"
    unfolding eqpoll_rel_def by auto
  with assms \<open>M(j)\<close>
  show "\<exists>Z[M]. Z \<subseteq> Y \<and> Z \<approx>\<^bsup>M\<^esup> X"
    using eqpoll_rel_sym[OF \<open>X \<approx>\<^bsup>M\<^esup> range(j)\<close>]
    by auto
next
  assume "\<exists>Z[M]. Z \<subseteq> Y \<and> Z \<approx>\<^bsup>M\<^esup> X"
  then
  obtain Z f where "f \<in> bij_rel(M,Z,X)" "Z \<subseteq> Y" "M(Z)" "M(f)"
    unfolding eqpoll_rel_def by blast
  with assms
  have "converse(f) \<in> inj_rel(M,X,Y)" "M(converse(f))"
    using inj_rel_weaken_type[OF bij_rel_converse_bij_rel[THEN bij_rel_is_inj_rel],of f Z X Y]
    by auto
  then
  show "X \<lesssim>\<^bsup>M\<^esup> Y"
    unfolding lepoll_rel_def by auto
qed

text\<open>The following result proves to be very useful when combining
     \<^term>\<open>cardinal_rel\<close> and \<^term>\<open>eqpoll_rel\<close> in a calculation.\<close>

lemma cardinal_rel_Card_rel_eqpoll_rel_iff:
  "Card_rel(M,\<kappa>) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> M(X) \<Longrightarrow> |X|\<^bsup>M\<^esup> = \<kappa> \<longleftrightarrow> X \<approx>\<^bsup>M\<^esup> \<kappa>"
  using Card_rel_cardinal_rel_eq[of \<kappa>] cardinal_rel_eqpoll_rel_iff[of X \<kappa>] by auto

lemma lepoll_rel_imp_lepoll_rel_cardinal_rel:
  assumes"X \<lesssim>\<^bsup>M\<^esup> Y"  "M(X)" "M(Y)"
  shows "X \<lesssim>\<^bsup>M\<^esup> |Y|\<^bsup>M\<^esup>"
  using assms cardinal_rel_Card_rel_eqpoll_rel_iff[of "|Y|\<^bsup>M\<^esup>" Y]
    Card_rel_cardinal_rel
    lepoll_rel_eq_trans[of _ _ "|Y|\<^bsup>M\<^esup>"] by simp

lemma lepoll_rel_Un:
  assumes "InfCard_rel(M,\<kappa>)" "A \<lesssim>\<^bsup>M\<^esup> \<kappa>" "B \<lesssim>\<^bsup>M\<^esup> \<kappa>" "M(A)" "M(B)" "M(\<kappa>)"
  shows "A \<union> B \<lesssim>\<^bsup>M\<^esup> \<kappa>"
proof -
  from assms
  have "A \<union> B \<lesssim>\<^bsup>M\<^esup> sum(A,B)"
    using Un_lepoll_rel_sum by simp
  moreover
  note assms
  moreover from this
  have "|sum(A,B)|\<^bsup>M\<^esup> \<le> \<kappa> \<oplus>\<^bsup>M\<^esup> \<kappa>"
    using sum_lepoll_rel_mono[of A \<kappa> B \<kappa>] lepoll_rel_imp_cardinal_rel_le
    unfolding cadd_rel_def by auto
  ultimately
  show ?thesis
    using InfCard_rel_cdouble_eq Card_rel_cardinal_rel_eq
      InfCard_rel_is_Card_rel Card_rel_le_imp_lepoll_rel[of "sum(A,B)" \<kappa>]
      lepoll_rel_trans[of "A\<union>B"]
    by auto
qed

lemma cardinal_rel_Un_le:
  assumes "InfCard_rel(M,\<kappa>)" "|A|\<^bsup>M\<^esup> \<le> \<kappa>" "|B|\<^bsup>M\<^esup> \<le> \<kappa>" "M(\<kappa>)" "M(A)" "M(B)"
  shows "|A \<union> B|\<^bsup>M\<^esup> \<le> \<kappa>"
  using assms lepoll_rel_Un le_Card_rel_iff InfCard_rel_is_Card_rel by auto

lemma Finite_cardinal_rel_iff': "M(i) \<Longrightarrow> Finite(|i|\<^bsup>M\<^esup>) \<longleftrightarrow> Finite(i)"
  using eqpoll_rel_imp_Finite_iff[OF cardinal_rel_eqpoll_rel]
  by auto

lemma cardinal_rel_subset_of_Card_rel:
  assumes "Card_rel(M,\<gamma>)" "a \<subseteq> \<gamma>" "M(a)" "M(\<gamma>)"
  shows "|a|\<^bsup>M\<^esup> < \<gamma> \<or> |a|\<^bsup>M\<^esup> = \<gamma>"
proof -
  from assms
  have "|a|\<^bsup>M\<^esup> < |\<gamma>|\<^bsup>M\<^esup> \<or> |a|\<^bsup>M\<^esup> = |\<gamma>|\<^bsup>M\<^esup>"
    using subset_imp_le_cardinal_rel[THEN le_iff[THEN iffD1]] by simp
  with assms
  show ?thesis
    using Card_rel_cardinal_rel_eq by auto
qed

lemma cardinal_rel_cases:
  includes Ord_dests
  assumes "M(\<gamma>)" "M(X)"
  shows "Card_rel(M,\<gamma>) \<Longrightarrow> |X|\<^bsup>M\<^esup> < \<gamma> \<longleftrightarrow> \<not> |X|\<^bsup>M\<^esup> \<ge> \<gamma>"
  using assms not_le_iff_lt Card_rel_is_Ord Ord_cardinal_rel
  by auto

end \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

subsection\<open>Countable and uncountable sets\<close>

definition (* FIXME: From Cardinal_Library, on the context of AC *)
  countable :: "i\<Rightarrow>o" where
  "countable(X) \<equiv> X \<lesssim> \<omega>"

relativize functional "countable" "countable_rel" external
relationalize "countable_rel" "is_countable"

notation countable_rel (\<open>countable\<^bsup>_\<^esup>'(_')\<close>)

abbreviation
  countable_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>countable\<^bsup>_\<^esup>'(_')\<close>) where
  "countable\<^bsup>M\<^esup>(i) \<equiv> countable_rel(##M,i)"

context M_library
begin

lemma countableI[intro]: "X \<lesssim>\<^bsup>M\<^esup> \<omega> \<Longrightarrow> countable_rel(M,X)"
  unfolding countable_rel_def by simp

lemma countableD[dest]: "countable_rel(M,X) \<Longrightarrow> X \<lesssim>\<^bsup>M\<^esup> \<omega>"
  unfolding countable_rel_def by simp

lemma countable_rel_iff_cardinal_rel_le_nat: "M(X) \<Longrightarrow> countable_rel(M,X) \<longleftrightarrow> |X|\<^bsup>M\<^esup> \<le> \<omega>"
  using le_Card_rel_iff[of \<omega> X] Card_rel_nat
  unfolding countable_rel_def by simp

lemma lepoll_rel_countable_rel: "X \<lesssim>\<^bsup>M\<^esup> Y \<Longrightarrow> countable_rel(M,Y) \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> countable_rel(M,X)"
  using lepoll_rel_trans[of X Y] by blast

\<comment> \<open>Next lemma can be proved without using AC\<close>
lemma surj_rel_countable_rel:
  "countable_rel(M,X) \<Longrightarrow> f \<in> surj_rel(M,X,Y) \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> M(f) \<Longrightarrow> countable_rel(M,Y)"
  using surj_rel_implies_cardinal_rel_le[of f X Y, THEN le_trans]
    countable_rel_iff_cardinal_rel_le_nat by simp

lemma Finite_imp_countable_rel: "Finite_rel(M,X) \<Longrightarrow> M(X) \<Longrightarrow> countable_rel(M,X)"
  unfolding Finite_rel_def
  by (auto intro:InfCard_rel_nat nats_le_InfCard_rel[of _ \<omega>,
        THEN le_imp_lepoll_rel] dest!:eq_lepoll_rel_trans[of X _ \<omega>] )

end \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

lemma (in M_cardinal_UN_lepoll) countable_rel_imp_countable_rel_UN:
  assumes "countable_rel(M,J)" "\<And>i. i\<in>J \<Longrightarrow> countable_rel(M,X(i))"
  shows "countable_rel(M,\<Union>i\<in>J. X(i))"
  using assms leqpoll_rel_imp_cardinal_rel_UN_le[of \<omega>] InfCard_rel_nat
    InfCard_rel_is_Card_rel j.UN_closed
    countable_rel_iff_cardinal_rel_le_nat j.Pi_assumptions
    Card_rel_le_imp_lepoll_rel[of J \<omega>] Card_rel_cardinal_rel_eq[of \<omega>]
  by auto

locale M_cardinal_library = M_library + M_replacement +
  assumes
    lam_replacement_inj_rel:"lam_replacement(M, \<lambda>x. inj\<^bsup>M\<^esup>(fst(x),snd(x)))"
    and
    cardinal_lib_assms1:
    "M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow>
       separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. if M(x) then x else 0,b,f,i)\<rangle>)"
    and
    cardinal_lib_assms2:
    "M(A') \<Longrightarrow> M(G) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow>
        separation(M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. if M(a) then G`a else 0,b,f,i)\<rangle>)"
    and
    cardinal_lib_assms3:
    "M(A') \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow> M(F) \<Longrightarrow>
        separation(M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. if M(a) then F-``{a} else 0,b,f,i)\<rangle>)"
    and
    cardinal_rel_separation :
    "separation(M, \<lambda>\<langle>x,y\<rangle>. cardinal_rel(M,x) = y)"
    and
    separation_cardinal_rel_lt :
    "M(\<gamma>) \<Longrightarrow> separation(M, \<lambda>Z . cardinal_rel(M,Z) < \<gamma>)"

begin

lemma cdlt_assms: "M(G) \<Longrightarrow> M(Q) \<Longrightarrow> separation(M, \<lambda>p. \<forall>x\<in>G. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> Q))"
  using lam_replacement_snd lam_replacement_fst lam_replacement_hcomp separation_in
    lam_replacement_Pair[THEN [5] lam_replacement_hcomp2]
  by (rule_tac separation_ball,simp_all,rule_tac separation_iff',auto)
    (rule_tac separation_all,auto simp:lam_replacement_constant)

lemma cdlt_assms': "M(x) \<Longrightarrow> M(Q) \<Longrightarrow> separation(M, \<lambda>a .  \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q)"
  using separation_in[OF _
      lam_replacement_hcomp2[OF _ _ _ _ lam_replacement_Pair] _
      lam_replacement_constant]
    separation_ball lam_replacement_hcomp lam_replacement_fst lam_replacement_snd
  by simp_all

lemma countable_rel_union_countable_rel:
  assumes "\<And>x. x \<in> C \<Longrightarrow> countable_rel(M,x)" "countable_rel(M,C)" "M(C)"
  shows "countable_rel(M,\<Union>C)"
proof -
  have "x \<in> (if M(i) then i else 0) \<Longrightarrow> M(i)" for x i
    by (cases "M(i)") auto
  then
  interpret M_replacement_lepoll M "\<lambda>_ x. if M(x) then x else 0"
    using  lam_replacement_if[OF lam_replacement_identity
        lam_replacement_constant[OF nonempty], where b=M] lam_replacement_inj_rel
      lam_replacement_minimum
  proof(unfold_locales,auto simp add: separation_def)
    fix b f
    assume "M(b)" "M(f)"
    show "lam_replacement(M, \<lambda>x. \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. if M(x) then x else 0, b, f, i))"
    proof (cases "b=0")
      case True
      with \<open>M(f)\<close>
      show ?thesis
        using cardinal_lib_assms1
        by (simp_all; rule_tac lam_Least_assumption_ifM_b0)+
    next
      case False
      with \<open>M(f)\<close> \<open>M(b)\<close>
      show ?thesis
        using cardinal_lib_assms1 separation_Ord lam_replacement_minimum
        by (rule_tac lam_Least_assumption_ifM_bnot0) auto
    qed
  qed
  note \<open>M(C)\<close>
  moreover
  have  "w \<in> (if M(x) then x else 0) \<Longrightarrow> M(x)" for w x
    by (cases "M(x)") auto
  ultimately
  interpret M_cardinal_UN_lepoll _ "\<lambda>c. if M(c) then c else 0" C
    using lepoll_assumptions lam_replacement_minimum
    by unfold_locales auto
  have "(if M(i) then i else 0) = i" if "i\<in>C" for i
    using transM[OF _ \<open>M(C)\<close>] that by simp
  then
  show ?thesis
    using assms countable_rel_imp_countable_rel_UN by simp
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_library\<close>\<close>

abbreviation
  uncountable_rel :: "[i\<Rightarrow>o,i]\<Rightarrow>o" where
  "uncountable_rel(M,X) \<equiv> \<not> countable_rel(M,X)"

context M_library
begin

lemma uncountable_rel_iff_nat_lt_cardinal_rel:
  "M(X) \<Longrightarrow> uncountable_rel(M,X) \<longleftrightarrow> \<omega> < |X|\<^bsup>M\<^esup>"
  using countable_rel_iff_cardinal_rel_le_nat not_le_iff_lt by simp

lemma uncountable_rel_not_empty: "uncountable_rel(M,X) \<Longrightarrow> X \<noteq> 0"
  using empty_lepoll_relI by auto

lemma uncountable_rel_imp_Infinite: "uncountable_rel(M,X) \<Longrightarrow> M(X) \<Longrightarrow> Infinite(X)"
  using uncountable_rel_iff_nat_lt_cardinal_rel[of X] lepoll_rel_nat_imp_Infinite[of X]
    cardinal_rel_le_imp_lepoll_rel[of \<omega> X] leI
  by simp

lemma uncountable_rel_not_subset_countable_rel:
  assumes "countable_rel(M,X)" "uncountable_rel(M,Y)" "M(X)" "M(Y)"
  shows "\<not> (Y \<subseteq> X)"
  using assms lepoll_rel_trans subset_imp_lepoll_rel[of Y X]
  by blast


subsection\<open>Results on Aleph\_rels\<close>

lemma nat_lt_Aleph_rel1: "\<omega> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  by (simp add: Aleph_rel_succ Aleph_rel_zero lt_csucc_rel)

lemma zero_lt_Aleph_rel1: "0 < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  by (rule lt_trans[of _ "\<omega>"], auto simp add: ltI nat_lt_Aleph_rel1)

lemma le_Aleph_rel1_nat: "M(k) \<Longrightarrow> Card_rel(M,k) \<Longrightarrow> k<\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> k \<le> \<omega>"
  by (simp add: Aleph_rel_succ Aleph_rel_zero Card_rel_lt_csucc_rel_iff Card_rel_nat)

lemma lesspoll_rel_Aleph_rel_succ:
  assumes "Ord(\<alpha>)"
    and types:"M(\<alpha>)" "M(d)"
  shows "d \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> \<longleftrightarrow> d \<lesssim>\<^bsup>M\<^esup> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>"
  using assms Aleph_rel_succ Card_rel_is_Ord Ord_Aleph_rel lesspoll_rel_csucc_rel
  by simp

lemma cardinal_rel_Aleph_rel [simp]: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> |\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> = \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>"
  using Card_rel_cardinal_rel_eq by simp

\<comment> \<open>Could be proved without using AC\<close>
lemma Aleph_rel_lesspoll_rel_increasing:
  includes Aleph_rel_intros
  assumes "M(b)" "M(a)"
  shows "a < b \<Longrightarrow> \<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
  using assms
    cardinal_rel_lt_iff_lesspoll_rel[of "\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"]
    Aleph_rel_increasing[of a b] Card_rel_cardinal_rel_eq[of "\<aleph>\<^bsub>b\<^esub>"]
    lt_Ord lt_Ord2 Card_rel_Aleph_rel[THEN Card_rel_is_Ord]
  by auto

lemma uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1:
  includes Ord_dests
  assumes "M(X)"
  notes Aleph_rel_zero[simp] Card_rel_nat[simp] Aleph_rel_succ[simp]
  shows "uncountable_rel(M,X) \<longleftrightarrow> (\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
proof
  assume "uncountable_rel(M,X)"
  with \<open>M(X)\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> X"
    using uncountable_rel_iff_nat_lt_cardinal_rel cardinal_rel_lt_csucc_rel_iff'
      cardinal_rel_le_imp_lepoll_rel by auto
  with \<open>M(X)\<close>
  obtain S where "M(S)" "S \<subseteq> X" "S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using lepoll_rel_imp_subset_bij_rel by auto
  then
  show "\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using cardinal_rel_cong Card_rel_csucc_rel[of \<omega>] Card_rel_cardinal_rel_eq by auto
next
  note Aleph_rel_lesspoll_rel_increasing[of 1 0,simplified]
  assume "\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  moreover
  have eq:"\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = (\<omega>\<^sup>+)\<^bsup>M\<^esup>" by auto
  moreover from calculation \<open>M(X)\<close>
  have A:"(\<omega>\<^sup>+)\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> X"
    using subset_imp_lepoll_rel[THEN [2] eq_lepoll_rel_trans, of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" _ X,
        OF eqpoll_rel_sym] by auto
  with \<open>M(X)\<close>
  show "uncountable_rel(M,X)"
    using
      lesspoll_rel_trans1[OF lepoll_rel_trans[OF A _] \<open>\<omega> \<prec>\<^bsup>M\<^esup> (\<omega>\<^sup>+)\<^bsup>M\<^esup>\<close>]
      lesspoll_rel_not_refl
    by auto
qed

lemma UN_if_zero: "M(K) \<Longrightarrow> (\<Union>x\<in>K. if M(x) then G ` x else 0) =(\<Union>x\<in>K. G ` x)"
  using transM[of _ K] by auto

lemma mem_F_bound1:
  fixes F G
  defines "F \<equiv> \<lambda>_ x. if M(x) then G`x else 0"
  shows "x\<in>F(A,c) \<Longrightarrow> c \<in> (range(f) \<union> domain(G) )"
  using apply_0 unfolding F_def
  by (cases "M(c)", auto simp:F_def drSR_Y_def dC_F_def)

end \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

context M_cardinal_library
begin

lemma lt_Aleph_rel_imp_cardinal_rel_UN_le_nat: "function(G) \<Longrightarrow> domain(G) \<lesssim>\<^bsup>M\<^esup> \<omega> \<Longrightarrow>
   \<forall>n\<in>domain(G). |G`n|\<^bsup>M\<^esup><\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> M(G) \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<^bsup>M\<^esup>\<le>\<omega>"
proof -
  assume "M(G)"
  moreover from this
  have "x \<in> (if M(i) then G ` i else 0) \<Longrightarrow> M(i)" for x i
    by (cases "M(i)") auto
  moreover
  have "separation(M, M)" unfolding separation_def by auto
  ultimately
  interpret M_replacement_lepoll M "\<lambda>_ x. if M(x) then G`x else 0"
    using lam_replacement_inj_rel cardinal_lib_assms2 mem_F_bound1[of _ _ G]
      lam_if_then_replacement_apply lam_replacement_minimum
    by (unfold_locales, simp_all)
      (rule lam_Least_assumption_general[where U="\<lambda>_. domain(G)"], auto)
  note \<open>M(G)\<close>
  moreover
  have  "w \<in> (if M(x) then G ` x else 0) \<Longrightarrow> M(x)" for w x
    by (cases "M(x)") auto
  ultimately
  interpret M_cardinal_UN_lepoll _  "\<lambda>n. if M(n) then G`n else 0" "domain(G)"
    using lepoll_assumptions1[where S="domain(G)",unfolded lepoll_assumptions1_def]
      cardinal_lib_assms2 lepoll_assumptions
    by (unfold_locales, auto)
  assume "function(G)"
  let ?N="domain(G)" and ?R="\<Union>n\<in>domain(G). G`n"
  assume "?N \<lesssim>\<^bsup>M\<^esup> \<omega>"
  assume Eq1: "\<forall>n\<in>?N. |G`n|\<^bsup>M\<^esup><\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  {
    fix n
    assume "n\<in>?N"
    with Eq1 \<open>M(G)\<close>
    have "|G`n|\<^bsup>M\<^esup> \<le> \<omega>"
      using le_Aleph_rel1_nat[of "|G ` n|\<^bsup>M\<^esup>"] leqpoll_rel_imp_cardinal_rel_UN_le
        UN_if_zero[of "domain(G)" G]
      by (auto dest:transM)
  }
  then
  have "n\<in>?N \<Longrightarrow> |G`n|\<^bsup>M\<^esup> \<le> \<omega>" for n .
  moreover
  note \<open>?N \<lesssim>\<^bsup>M\<^esup> \<omega>\<close> \<open>M(G)\<close>
  moreover
  have "(if M(i) then G ` i else 0) \<subseteq> G ` i" for i
    by auto
  with \<open>M(G)\<close>
  have "|if M(i) then G ` i else 0|\<^bsup>M\<^esup> \<le> |G ` i|\<^bsup>M\<^esup>" for i
  proof(cases "M(i)")
    case True
    with \<open>M(G)\<close> show ?thesis using Ord_cardinal_rel[OF apply_closed]
      by simp
  next
    case False
    then
    have "i\<notin>domain(G)"
      using transM[OF _ domain_closed[OF \<open>M(G)\<close>]] by auto
    then
    show ?thesis
      using Ord_cardinal_rel[OF apply_closed] apply_0 by simp
  qed
  ultimately
  show ?thesis
    using InfCard_rel_nat leqpoll_rel_imp_cardinal_rel_UN_le[of \<omega>]
      UN_if_zero[of "domain(G)" G]
      le_trans[of "|if M(_) then G ` _ else 0|\<^bsup>M\<^esup>" "|G ` _|\<^bsup>M\<^esup>" \<omega>]
    by auto blast
qed

lemma Aleph_rel1_eq_cardinal_rel_vimage: "f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<^bsup>M\<^esup>\<omega> \<Longrightarrow> \<exists>n\<in>\<omega>. |f-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  assume "f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<^bsup>M\<^esup>\<omega>"
  then
  have "function(f)" "domain(f) = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "range(f)\<subseteq>\<omega>" "f\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>" "M(f)"
    using mem_function_space_rel[OF \<open>f\<in>_\<close>] domain_of_fun fun_is_function range_fun_subset_codomain
      function_space_rel_char
    by auto
  let ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close>
  have "range(f) \<subseteq> \<omega>" "domain(?G) = range(f)"
    using range_fun_subset_codomain
    by simp_all
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close> \<open>M(f)\<close> \<open>range(f) \<subseteq> \<omega>\<close>
  have "M(f-``{n})" if "n \<in> range(f)" for n
    using that transM[of _ \<omega>] by auto
  with \<open>M(f)\<close> \<open>range(f) \<subseteq> \<omega>\<close>
  have "domain(?G) \<lesssim>\<^bsup>M\<^esup> \<omega>" "M(?G)"
    using subset_imp_lepoll_rel lam_closed[of "\<lambda>x . f-``{x}"] cardinal_lib_assms4
    by simp_all
  have "function(?G)" by (simp add:function_lam)
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close>
  have "n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" for n
    using Pi_vimage_subset by simp
  with \<open>range(f) \<subseteq> \<omega>\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = (\<Union>n\<in>range(f). f-``{n})"
  proof (intro equalityI, intro subsetI)
    fix x
    assume "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    with \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)"
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed auto
  {
    assume "\<forall>n\<in>range(f). |f-``{n}|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    then
    have "\<forall>n\<in>domain(?G). |?G`n|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
      using zero_lt_Aleph_rel1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim>\<^bsup>M\<^esup> \<omega>\<close> \<open>M(?G)\<close>
    have "|\<Union>n\<in>domain(?G). ?G`n|\<^bsup>M\<^esup>\<le>\<omega>"
      using lt_Aleph_rel_imp_cardinal_rel_UN_le_nat[of ?G]
      by auto
    then
    have "|\<Union>n\<in>range(f). f-``{n}|\<^bsup>M\<^esup>\<le>\<omega>" by simp
    with \<open>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = _\<close>
    have "|\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> \<le> \<omega>" by auto
    then
    have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<le> \<omega>"
      using Card_rel_Aleph_rel Card_rel_cardinal_rel_eq
      by auto
    then
    have "False"
      using nat_lt_Aleph_rel1 by (blast dest:lt_trans2)
  }
  with \<open>range(f)\<subseteq>\<omega>\<close> \<open>M(f)\<close>
  obtain n where "n\<in>\<omega>" "\<not>(|f -`` {n}|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "M(f -`` {n})"
    using nat_into_M by auto
  moreover from this
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<le> |f-``{n}|\<^bsup>M\<^esup>"
    using not_lt_iff_le Card_rel_is_Ord by simp
  moreover
  note \<open>n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
  ultimately
  show ?thesis
    using subset_imp_le_cardinal_rel[THEN le_anti_sym, of _ "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_Aleph_rel Card_rel_cardinal_rel_eq
    by auto
qed

\<comment> \<open>There is some asymmetry between assumptions and conclusion
    (\<^term>\<open>eqpoll_rel\<close> versus \<^term>\<open>cardinal_rel\<close>)\<close>

lemma eqpoll_rel_Aleph_rel1_cardinal_rel_vimage:
  assumes "Z \<approx>\<^bsup>M\<^esup> (\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "f \<in> Z \<rightarrow>\<^bsup>M\<^esup> \<omega>" "M(Z)"
  shows "\<exists>n\<in>\<omega>. |f-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  have "M(1)" "M(\<omega>)" by simp_all
  then
  have "M(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" by simp
  with assms \<open>M(1)\<close>
  obtain g where A:"g\<in>bij_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,Z)" "M(g)"
    using eqpoll_rel_sym unfolding eqpoll_rel_def by blast
  with \<open>f : Z \<rightarrow>\<^bsup>M\<^esup> \<omega>\<close> assms
  have "M(f)" "converse(g) \<in> bij_rel(M,Z, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "f\<in>Z\<rightarrow>\<omega>" "g\<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>Z"
    using bij_rel_is_fun_rel bij_rel_converse_bij_rel bij_rel_char function_space_rel_char
    by simp_all
  with \<open>g\<in>bij_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,Z)\<close> \<open>M(g)\<close>
  have "f O g : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow>\<^bsup>M\<^esup> \<omega>" "M(converse(g))"
    using comp_fun[OF _ \<open>f\<in> Z\<rightarrow>_\<close>,of g] function_space_rel_char
    by simp_all
  then
  obtain n where "n\<in>\<omega>" "|(f O g)-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using Aleph_rel1_eq_cardinal_rel_vimage
    by auto
  with \<open>M(f)\<close> \<open>M(converse(g))\<close>
  have "M(converse(g) `` (f -`` {n}))" "f -`` {n} \<subseteq> Z"
    using image_comp converse_comp Pi_iff[THEN iffD1,OF \<open>f\<in>Z\<rightarrow>\<omega>\<close>] vimage_subset
    unfolding vimage_def
    using transM[OF \<open>n\<in>\<omega>\<close>]
    by auto
  from \<open>n\<in>\<omega>\<close> \<open>|(f O g)-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = |converse(g) `` (f -``{n})|\<^bsup>M\<^esup>"
    using image_comp converse_comp unfolding vimage_def
    by auto
  also from \<open>converse(g) \<in> bij_rel(M,Z, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close> \<open>f: Z\<rightarrow>\<^bsup>M\<^esup> \<omega>\<close> \<open>M(Z)\<close> \<open>M(f)\<close> \<open>M(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close>
    \<open>M(converse(g) `` (f -`` {n}))\<close>
  have "\<dots> = |f -``{n}|\<^bsup>M\<^esup>"
    using range_of_subset_eqpoll_rel[of "converse(g)" Z  _ "f -``{n}",
        OF bij_rel_is_inj_rel[OF \<open>converse(g)\<in>_\<close>] \<open>f -`` {n} \<subseteq> Z\<close>]
      cardinal_rel_cong vimage_closed[OF singleton_closed[OF transM[OF \<open>n\<in>\<omega>\<close>]],of f]
    by auto
  finally
  show ?thesis using \<open>n\<in>_\<close> by auto
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_library\<close>\<close>

subsection\<open>Applications of transfinite recursive constructions\<close>

locale M_cardinal_library_extra = M_cardinal_library +
  assumes
    replacement_trans_apply_image:
    "M(f) \<Longrightarrow> M(\<beta>) \<Longrightarrow> Ord(\<beta>) \<Longrightarrow>
      strong_replacement(M, \<lambda>x y. x\<in>\<beta> \<and> y = \<langle>x, transrec(x, \<lambda>a g. f ` (g `` a))\<rangle>)"
begin

lemma rec_constr_type_rel:
  assumes "f:Pow_rel(M,G)\<rightarrow>\<^bsup>M\<^esup> G" "Ord(\<alpha>)" "M(G)"
  shows "M(\<alpha>) \<Longrightarrow> rec_constr(f,\<alpha>) \<in> G"
  using assms(2)
proof(induct rule:trans_induct)
  case (step \<beta>)
  with assms
  have "{rec_constr(f, x) . x \<in> \<beta>} = {y . x \<in> \<beta>, y=rec_constr(f, x)}" (is "_ = ?Y")
    "M(f)"
    using transM[OF _ \<open>M(\<beta>)\<close>] function_space_rel_char  Ord_in_Ord
    by auto
  moreover from assms this step \<open>M(\<beta>)\<close> \<open>Ord(\<beta>)\<close>
  have "M({y . x \<in> \<beta>, y=<x,rec_constr(f, x)>})" (is "M(?Z)")
    using strong_replacement_closed[OF replacement_trans_apply_image,of f \<beta> \<beta>,OF _ _ _ _
        univalent_conjI2[where P="\<lambda>x _ . x\<in>\<beta>",OF univalent_triv]]
      transM[OF _ \<open>M(\<beta>)\<close>] transM[OF step(2) \<open>M(G)\<close>] Ord_in_Ord
    unfolding rec_constr_def
    by auto
  moreover from assms this step \<open>M(\<beta>)\<close> \<open>Ord(\<beta>)\<close>
  have "?Y = {snd(y) . y\<in>?Z}"
  proof(intro equalityI, auto)
    fix u
    assume "u\<in>\<beta>"
    with assms this step \<open>M(\<beta>)\<close> \<open>Ord(\<beta>)\<close>
    have "<u,rec_constr(f,u)> \<in> ?Z"  "rec_constr(f, u) = snd(<u,rec_constr(f,u)>)"
      by auto
    then
    show "\<exists>x\<in>{y . x \<in> \<beta>, y = \<langle>x, rec_constr(f, x)\<rangle>}. rec_constr(f, u) = snd(x)"
      using bexI[of _ u] by force
  qed
  moreover from \<open>M(?Z)\<close> \<open>?Y = _\<close>
  have "M(?Y)"
    using
      RepFun_closed[OF lam_replacement_imp_strong_replacement[OF lam_replacement_snd] \<open>M(?Z)\<close>]
      fst_snd_closed[THEN conjunct2] transM[OF _ \<open>M(?Z)\<close>]
    by simp
  moreover from assms step
  have "{rec_constr(f, x) . x \<in> \<beta>} \<in> Pow(G)" (is "?X\<in>_")
    using transM[OF _ \<open>M(\<beta>)\<close>] function_space_rel_char
    by auto
  moreover from assms calculation step
  have "M(?X)"
    by simp
  moreover from calculation \<open>M(G)\<close>
  have "?X\<in>Pow_rel(M,G)"
    using Pow_rel_char by simp
  ultimately
  have "f`?X \<in> G"
    using assms apply_type[OF mem_function_space_rel[of f],of "Pow_rel(M,G)" G ?X]
    by auto
  then
  show ?case
    by (subst rec_constr_unfold,simp)
qed

lemma rec_constr_closed :
  assumes "f:Pow_rel(M,G)\<rightarrow>\<^bsup>M\<^esup> G" "Ord(\<alpha>)" "M(G)" "M(\<alpha>)"
  shows "M(rec_constr(f,\<alpha>))"
  using transM[OF rec_constr_type_rel \<open>M(G)\<close>] assms by auto

lemma lambda_rec_constr_closed :
  assumes "Ord(\<gamma>)" "M(\<gamma>)" "M(f)" "f:Pow_rel(M,G)\<rightarrow>\<^bsup>M\<^esup> G" "M(G)"
  shows "M(\<lambda>\<alpha>\<in>\<gamma> . rec_constr(f,\<alpha>))"
  using lam_closed2[OF replacement_trans_apply_image,unfolded rec_constr_def[symmetric],of f \<gamma>]
    rec_constr_type_rel[OF \<open>f\<in>_\<close> Ord_in_Ord[of \<gamma>]] transM[OF _ \<open>M(G)\<close>] assms
  by simp

text\<open>The next lemma is an application of recursive constructions.
     It works under the assumption that whenever the already constructed
     subsequence is small enough, another element can be added.\<close>

lemma bounded_cardinal_rel_selection:
  includes Ord_dests
  assumes
    "\<And>Z. |Z|\<^bsup>M\<^esup> < \<gamma> \<Longrightarrow> Z \<subseteq> G \<Longrightarrow> M(Z) \<Longrightarrow> \<exists>a\<in>G. \<forall>s\<in>Z. <s,a>\<in>Q" "b\<in>G" "Card_rel(M,\<gamma>)"
    "M(G)" "M(Q)" "M(\<gamma>)"
  shows
    "\<exists>S[M]. S : \<gamma> \<rightarrow>\<^bsup>M\<^esup> G \<and> (\<forall>\<alpha> \<in> \<gamma>. \<forall>\<beta> \<in> \<gamma>.  \<alpha><\<beta> \<longrightarrow> <S`\<alpha>,S`\<beta>>\<in>Q)"
proof -
  from assms
  have "M(x) \<Longrightarrow> M({a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q})" for x
    using separation_orthogonal by simp
  let ?cdlt\<gamma>="{Z\<in>Pow_rel(M,G) . |Z|\<^bsup>M\<^esup><\<gamma>}" \<comment> \<open>“cardinal\_rel less than \<^term>\<open>\<gamma>\<close>”\<close>
    and ?inQ="\<lambda>Y.{a\<in>G. \<forall>s\<in>Y. <s,a>\<in>Q}"
  from \<open>M(G)\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close>
  have "M(?cdlt\<gamma>)" "Ord(\<gamma>)"
    using separation_cardinal_rel_lt[OF \<open>M(\<gamma>)\<close>] Card_rel_is_Ord
    by simp_all
  from assms
  have H:"\<exists>a. a \<in> ?inQ(Y)" if "Y\<in>?cdlt\<gamma>" for Y
  proof -
    {
      fix Y
      assume "Y\<in>?cdlt\<gamma>"
      then
      have A:"Y\<in>Pow_rel(M,G)" "|Y|\<^bsup>M\<^esup><\<gamma>"  by simp_all
      then
      have "Y\<subseteq>G" "M(Y)" using Pow_rel_char[OF \<open>M(G)\<close>] by simp_all
      with A
      obtain a where "a\<in>G" "\<forall>s\<in>Y. <s,a>\<in>Q"
        using assms(1) by force
      with \<open>M(G)\<close>
      have "\<exists>a. a \<in> ?inQ(Y)" by auto
    }
    then show ?thesis using that by simp
  qed
  then
  have "\<exists>f[M]. f \<in> Pi_rel(M,?cdlt\<gamma>,?inQ) \<and> f \<in> Pi(?cdlt\<gamma>,?inQ)"
  proof -
    from \<open>\<And>x. M(x) \<Longrightarrow> M({a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q})\<close> \<open>M(G)\<close>
    have "x \<in> {Z \<in> Pow\<^bsup>M\<^esup>(G) . |Z|\<^bsup>M\<^esup> < \<gamma>} \<Longrightarrow> M({a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q})" for x
      by (auto dest:transM)
    with\<open>M(G)\<close> \<open>\<And>x. M(x) \<Longrightarrow> M({a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q})\<close> \<open>M(Q)\<close> \<open>M(?cdlt\<gamma>)\<close>
    interpret M_Pi_assumptions_choice M ?cdlt\<gamma> ?inQ
      using cdlt_assms[where Q=Q] lam_replacement_Collect_ball_Pair[THEN
          lam_replacement_imp_strong_replacement] surj_imp_inj_replacement3
        lam_replacement_hcomp2[OF lam_replacement_constant
          lam_replacement_Collect_ball_Pair _ _ lam_replacement_minimum,
          unfolded lam_replacement_def]
        lam_replacement_hcomp lam_replacement_Sigfun[OF
          lam_replacement_Collect_ball_Pair, of G Q, THEN
          lam_replacement_imp_strong_replacement] separation_orthogonal
      by unfold_locales (blast dest: transM, auto dest:transM)
    show ?thesis using AC_Pi_rel Pi_rel_char H by auto
  qed
  then
  obtain f where f_type:"f \<in> Pi_rel(M,?cdlt\<gamma>,?inQ)" "f \<in> Pi(?cdlt\<gamma>,?inQ)" and "M(f)"
    by auto
  moreover
  define Cb where "Cb \<equiv> \<lambda>_\<in>Pow_rel(M,G)-?cdlt\<gamma>. b"
  moreover from \<open>b\<in>G\<close> \<open>M(?cdlt\<gamma>)\<close> \<open>M(G)\<close>
  have "Cb \<in> Pow_rel(M,G)-?cdlt\<gamma> \<rightarrow> G" "M(Cb)"
    using lam_closed[of "\<lambda>_.b" "Pow_rel(M,G)-?cdlt\<gamma>"]
      tag_replacement transM[OF \<open>b\<in>G\<close>]
    unfolding Cb_def by auto
  moreover
  note \<open>Card_rel(M,\<gamma>)\<close>
  ultimately
  have "f \<union> Cb : (\<Prod>x\<in>Pow_rel(M,G). ?inQ(x) \<union> G)" using
      fun_Pi_disjoint_Un[ of f ?cdlt\<gamma>  ?inQ Cb "Pow_rel(M,G)-?cdlt\<gamma>" "\<lambda>_.G"]
      Diff_partition[of "{Z\<in>Pow_rel(M,G). |Z|\<^bsup>M\<^esup><\<gamma>}" "Pow_rel(M,G)", OF Collect_subset]
    by auto
  moreover
  have "?inQ(x) \<union> G = G" for x by auto
  moreover from calculation
  have "f \<union> Cb : Pow_rel(M,G) \<rightarrow> G"
    using function_space_rel_char by simp
  ultimately
  have "f \<union> Cb : Pow_rel(M,G) \<rightarrow>\<^bsup>M\<^esup> G"
    using function_space_rel_char \<open>M(f)\<close> \<open>M(Cb)\<close> Pow_rel_closed \<open>M(G)\<close>
    by auto
  define S where "S\<equiv>\<lambda>\<alpha>\<in>\<gamma>. rec_constr(f \<union> Cb, \<alpha>)"
  from \<open>f \<union> Cb: Pow_rel(M,G) \<rightarrow>\<^bsup>M\<^esup> G\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close> \<open>M(G)\<close>
  have "S : \<gamma> \<rightarrow> G" "M(f \<union> Cb)"
    unfolding S_def
    using Ord_in_Ord[OF Card_rel_is_Ord] rec_constr_type_rel lam_type transM[OF _ \<open>M(\<gamma>)\<close>]
      function_space_rel_char
    by auto
  moreover from \<open>f\<union>Cb \<in> _\<rightarrow>\<^bsup>M\<^esup> G\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close> \<open>M(G)\<close> \<open>M(f \<union> Cb)\<close> \<open>Ord(\<gamma>)\<close>
  have "M(S)"
    unfolding S_def
    using lambda_rec_constr_closed
    by simp
  moreover
  have "\<forall>\<alpha>\<in>\<gamma>. \<forall>\<beta>\<in>\<gamma>. \<alpha> < \<beta> \<longrightarrow> \<langle>S`\<alpha>, S`\<beta>\<rangle> \<in> Q"
  proof (intro ballI impI)
    fix \<alpha> \<beta>
    assume "\<beta>\<in>\<gamma>"
    with \<open>Card_rel(M,\<gamma>)\<close> \<open>M(S)\<close> \<open>M(\<gamma>)\<close>
    have "\<beta>\<subseteq>\<gamma>" "M(S``\<beta>)" "M(\<beta>)" "{S`x . x \<in> \<beta>} = {restrict(S,\<beta>)`x . x \<in> \<beta>}"
      using transM[OF \<open>\<beta>\<in>\<gamma>\<close> \<open>M(\<gamma>)\<close>] image_closed Card_rel_is_Ord OrdmemD
      by auto
    with \<open>\<beta>\<in>_\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close>
    have "{rec_constr(f \<union> Cb, x) . x\<in>\<beta>} = {S`x . x \<in> \<beta>}"
      using Ord_trans[OF _ _ Card_rel_is_Ord, of _ \<beta> \<gamma>]
      unfolding S_def
      by auto
    moreover from \<open>\<beta>\<in>\<gamma>\<close> \<open>S : \<gamma> \<rightarrow> G\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close> \<open>M(S``\<beta>)\<close>
    have "{S`x . x \<in> \<beta>} \<subseteq> G" "M({S`x . x \<in> \<beta>})"
      using Ord_trans[OF _ _ Card_rel_is_Ord, of _ \<beta> \<gamma>]
        apply_type[of S \<gamma> "\<lambda>_. G"]
      by(auto,simp add:image_fun_subset[OF \<open>S\<in>_\<close> \<open>\<beta>\<subseteq>_\<close>])
    moreover from \<open>Card_rel(M,\<gamma>)\<close> \<open>\<beta>\<in>\<gamma>\<close> \<open>S\<in>_\<close> \<open>\<beta>\<subseteq>\<gamma>\<close> \<open>M(S)\<close> \<open>M(\<beta>)\<close> \<open>M(G)\<close> \<open>M(\<gamma>)\<close>
    have "|{S`x . x \<in> \<beta>}|\<^bsup>M\<^esup> < \<gamma>"
      using
        \<open>{S`x . x\<in>\<beta>} = {restrict(S,\<beta>)`x . x\<in>\<beta>}\<close>[symmetric]
        cardinal_rel_RepFun_apply_le[of "restrict(S,\<beta>)" \<beta> G,
          OF restrict_type2[of S \<gamma> "\<lambda>_.G" \<beta>] restrict_closed]
        Ord_in_Ord Ord_cardinal_rel
        lt_trans1[of "|{S`x . x \<in> \<beta>}|\<^bsup>M\<^esup>" "|\<beta>|\<^bsup>M\<^esup>" \<gamma>]
        Card_rel_lt_iff[THEN iffD2, of \<beta> \<gamma>, OF _ _ _ _ ltI]
        Card_rel_is_Ord
      by auto
    moreover
    have "\<forall>x\<in>\<beta>. <S`x, f ` {S`x . x \<in> \<beta>}> \<in> Q"
    proof -
      from calculation and f_type
      have "f ` {S`x . x \<in> \<beta>} \<in> {a\<in>G. \<forall>x\<in>\<beta>. <S`x,a>\<in>Q}"
        using apply_type[of f ?cdlt\<gamma> ?inQ "{S`x . x \<in> \<beta>}"]
          Pow_rel_char[OF \<open>M(G)\<close>]
        by simp
      then
      show ?thesis by simp
    qed
    moreover
    assume "\<alpha>\<in>\<gamma>" "\<alpha> < \<beta>"
    moreover from this
    have "\<alpha>\<in>\<beta>" using ltD by simp
    moreover
    note \<open>\<beta>\<in>\<gamma>\<close> \<open>Cb \<in> Pow_rel(M,G)-?cdlt\<gamma> \<rightarrow> G\<close>
    ultimately
    show "\<langle>S`\<alpha>, S`\<beta>\<rangle>\<in>Q"
      using fun_disjoint_apply1[of "{S`x . x \<in> \<beta>}" Cb f]
        domain_of_fun[of Cb] ltD[of \<alpha> \<beta>]
      by (subst (2) S_def, auto) (subst rec_constr_unfold, auto)
  qed
  moreover
  note \<open>M(G)\<close> \<open>M(\<gamma>)\<close>
  ultimately
  show ?thesis using function_space_rel_char by auto
qed

text\<open>The following basic result can, in turn, be proved by a
     bounded-cardinal\_rel selection.\<close>
lemma Infinite_iff_lepoll_rel_nat: "M(Z) \<Longrightarrow> Infinite(Z) \<longleftrightarrow> \<omega> \<lesssim>\<^bsup>M\<^esup> Z"
proof
  define Distinct where "Distinct = {<x,y> \<in> Z\<times>Z . x\<noteq>y}"
  have "Distinct = {xy \<in> Z\<times>Z . \<exists>a b. xy = \<langle>a, b\<rangle> \<and> a \<noteq> b}" (is "_=?A")
    unfolding Distinct_def by auto
  moreover
  assume "Infinite(Z)" "M(Z)"
  moreover from calculation
  have "M(Distinct)"
    using separation_dist by simp
  from \<open>Infinite(Z)\<close> \<open>M(Z)\<close>
  obtain b where "b\<in>Z"
    using Infinite_not_empty by auto
  {
    fix Y
    assume "|Y|\<^bsup>M\<^esup> < \<omega>" "M(Y)"
    then
    have "Finite(Y)"
      using Finite_cardinal_rel_iff' ltD nat_into_Finite by auto
    with \<open>Infinite(Z)\<close>
    have "Z \<noteq> Y" by auto
  }
  moreover
  have "(\<And>W. M(W) \<Longrightarrow> |W|\<^bsup>M\<^esup> < \<omega> \<Longrightarrow> W \<subseteq> Z \<Longrightarrow> \<exists>a\<in>Z. \<forall>s\<in>W. <s,a>\<in>Distinct)"
  proof -
    fix W
    assume "M(W)" "|W|\<^bsup>M\<^esup> < \<omega>" "W \<subseteq> Z"
    moreover from this
    have "Finite_rel(M,W)"
      using
        cardinal_rel_closed[OF \<open>M(W)\<close>] Card_rel_nat
        lt_Card_rel_imp_lesspoll_rel[of \<omega>,simplified,OF _ \<open>|W|\<^bsup>M\<^esup> < \<omega>\<close>]
        lesspoll_rel_nat_is_Finite_rel[of W]
        eqpoll_rel_imp_lepoll_rel eqpoll_rel_sym[OF cardinal_rel_eqpoll_rel,of W]
        lesspoll_rel_trans1[of W "|W|\<^bsup>M\<^esup>" \<omega>] by auto
    moreover from calculation
    have "\<not>Z\<subseteq>W"
      using equalityI \<open>Infinite(Z)\<close> by auto
    moreover from calculation
    show "\<exists>a\<in>Z. \<forall>s\<in>W. <s,a>\<in>Distinct"
      unfolding Distinct_def by auto
  qed
  moreover from \<open>b\<in>Z\<close> \<open>M(Z)\<close> \<open>M(Distinct)\<close> this
  obtain S where "S : \<omega> \<rightarrow>\<^bsup>M\<^esup> Z" "M(S)" "\<forall>\<alpha>\<in>\<omega>. \<forall>\<beta>\<in>\<omega>. \<alpha> < \<beta> \<longrightarrow> <S`\<alpha>,S`\<beta>> \<in> Distinct"
    using bounded_cardinal_rel_selection[OF _ \<open>b\<in>Z\<close> Card_rel_nat,of Distinct]
    by blast
  moreover from this
  have "\<alpha> \<in> \<omega> \<Longrightarrow> \<beta> \<in> \<omega> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<noteq> S`\<beta>" for \<alpha> \<beta>
    unfolding Distinct_def
    by (rule_tac lt_neq_symmetry[of "\<omega>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<noteq> S`\<beta>"])
      auto
  moreover from this \<open>S\<in>_\<close> \<open>M(Z)\<close>
  have "S\<in>inj(\<omega>,Z)" using function_space_rel_char unfolding inj_def by auto
  ultimately
  show "\<omega> \<lesssim>\<^bsup>M\<^esup> Z"
    unfolding lepoll_rel_def using inj_rel_char \<open>M(Z)\<close> by auto
next
  assume "\<omega> \<lesssim>\<^bsup>M\<^esup> Z" "M(Z)"
  then
  show "Infinite(Z)" using lepoll_rel_nat_imp_Infinite by simp
qed

lemma Infinite_InfCard_rel_cardinal_rel: "Infinite(Z) \<Longrightarrow> M(Z) \<Longrightarrow> InfCard_rel(M,|Z|\<^bsup>M\<^esup>)"
  using lepoll_rel_eq_trans eqpoll_rel_sym lepoll_rel_nat_imp_Infinite
    Infinite_iff_lepoll_rel_nat Inf_Card_rel_is_InfCard_rel cardinal_rel_eqpoll_rel
  by simp

lemma (in M_trans) mem_F_bound2:
  fixes F A
  defines "F \<equiv> \<lambda>_ x. if M(x) then A-``{x} else 0"
  shows "x\<in>F(A,c) \<Longrightarrow> c \<in> (range(f) \<union> range(A))"
  using apply_0 unfolding F_def
  by (cases "M(c)", auto simp:F_def drSR_Y_def dC_F_def)

lemma Finite_to_one_rel_surj_rel_imp_cardinal_rel_eq:
  assumes "F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)" "Infinite(Z)" "M(Z)" "M(Y)"
  shows "|Y|\<^bsup>M\<^esup> = |Z|\<^bsup>M\<^esup>"
proof -
  have sep_true: "separation(M, M)" unfolding separation_def by auto
  note \<open>M(Z)\<close> \<open>M(Y)\<close>
  moreover from this assms
  have "M(F)" "F \<in> Z \<rightarrow> Y"
    unfolding Finite_to_one_rel_def
    using function_space_rel_char by simp_all
  moreover from this
  have "x \<in> (if M(i) then F -`` {i} else 0) \<Longrightarrow> M(i)" for x i
    by (cases "M(i)") auto
  moreover from calculation
  interpret M_replacement_lepoll M "\<lambda>_ x. if M(x) then F-``{x} else 0"
    using lam_replacement_inj_rel mem_F_bound2 cardinal_lib_assms3
      lam_replacement_vimage_sing_fun lam_replacement_minimum
      lam_replacement_if[OF _
        lam_replacement_constant[OF nonempty],where b=M] sep_true
    by (unfold_locales, simp_all)
      (rule lam_Least_assumption_general[where U="\<lambda>_. range(F)"], auto)
  have "w \<in> (if M(y) then F-``{y} else 0) \<Longrightarrow> M(y)" for w y
    by (cases "M(y)") auto
  moreover from \<open>F\<in>_\<inter>_\<close>
  have 0:"Finite(F-``{y})" if "y\<in>Y" for y
    unfolding Finite_to_one_rel_def
    using vimage_fun_sing \<open>F\<in>Z\<rightarrow>Y\<close> transM[OF that \<open>M(Y)\<close>] transM[OF _ \<open>M(Z)\<close>] that by simp
  ultimately
  interpret M_cardinal_UN_lepoll _ "\<lambda>y. if M(y) then F-``{y} else 0" Y
    using cardinal_lib_assms3 lepoll_assumptions
    by unfold_locales  (auto dest:transM simp del:mem_inj_abs)
  from \<open>F\<in>Z\<rightarrow>Y\<close>
  have "Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})"
    using apply_type by auto
  then
  show ?thesis
  proof (cases "Finite(Y)")
    case True
    with \<open>Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})\<close> and assms and \<open>F\<in>Z\<rightarrow>Y\<close>
    show ?thesis
      using Finite_RepFun[THEN [2] Finite_Union, of Y "\<lambda>y. F-``{y}"] 0 vimage_fun_sing[OF \<open>F\<in>Z\<rightarrow>Y\<close>]
      by simp
  next
    case False
    moreover from this \<open>M(Y)\<close>
    have "Y \<lesssim>\<^bsup>M\<^esup> |Y|\<^bsup>M\<^esup>"
      using cardinal_rel_eqpoll_rel eqpoll_rel_sym eqpoll_rel_imp_lepoll_rel by auto
    moreover
    note assms
    moreover from \<open>F\<in>_\<inter>_\<close>
    have "Finite({x\<in>Z . F`x = y})" "M(F-``{y})" if "y\<in>Y" for y
      unfolding Finite_to_one_rel_def
      using transM[OF that  \<open>M(Y)\<close>] transM[OF _ \<open>M(Z)\<close>] vimage_fun_sing[OF \<open>F\<in>Z\<rightarrow>Y\<close>] that
      by simp_all
    moreover from calculation
    have "|{x\<in>Z . F`x = y}|\<^bsup>M\<^esup> \<in> \<omega>" if "y\<in>Y" for y
      using Finite_cardinal_rel_in_nat that transM[OF that \<open>M(Y)\<close>] vimage_fun_sing[OF \<open>F\<in>Z\<rightarrow>Y\<close>] that
      by simp
    moreover from calculation
    have "|{x\<in>Z . F`x = y}|\<^bsup>M\<^esup> \<le> |Y|\<^bsup>M\<^esup>" if "y\<in>Y" for y
      using Infinite_imp_nats_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le,
          of _ "|{x\<in>Z . F`x = y}|\<^bsup>M\<^esup>"]
        that cardinal_rel_idem transM[OF that \<open>M(Y)\<close>] vimage_fun_sing[OF \<open>F\<in>Z\<rightarrow>Y\<close>]
      by auto
    ultimately
    have "|\<Union>y\<in>Y. {x\<in>Z . F`x = y}|\<^bsup>M\<^esup> \<le> |Y|\<^bsup>M\<^esup>"
      using leqpoll_rel_imp_cardinal_rel_UN_le
        Infinite_InfCard_rel_cardinal_rel[of Y] vimage_fun_sing[OF \<open>F\<in>Z\<rightarrow>Y\<close>]
      by(auto simp add:transM[OF _ \<open>M(Y)\<close>])
    moreover from \<open>F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)\<close> \<open>M(Z)\<close> \<open>M(F)\<close> \<open>M(Y)\<close>
    have "|Y|\<^bsup>M\<^esup> \<le> |Z|\<^bsup>M\<^esup>"
      using surj_rel_implies_cardinal_rel_le by auto
    moreover
    note \<open>Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})\<close>
    ultimately
    show ?thesis
      using le_anti_sym by auto
  qed
qed

lemma cardinal_rel_map_Un:
  assumes "Infinite(X)" "Finite(b)" "M(X)" "M(b)"
  shows "|{a \<union> b . a \<in> X}|\<^bsup>M\<^esup> = |X|\<^bsup>M\<^esup>"
proof -
  have "(\<lambda>a\<in>X. a \<union> b) \<in> Finite_to_one_rel(M,X,{a \<union> b . a \<in> X})"
    "(\<lambda>a\<in>X. a \<union> b) \<in>  surj_rel(M,X,{a \<union> b . a \<in> X})"
    "M({a \<union> b . a \<in> X})"
    unfolding def_surj_rel
  proof
    fix d
    have "Finite({a \<in> X . a \<union> b = d})" (is "Finite(?Y(b,d))")
      using \<open>Finite(b)\<close>
    proof (induct arbitrary:d)
      case 0
      have "{a \<in> X . a \<union> 0 = d} = (if d\<in>X then {d} else 0)"
        by auto
      then
      show ?case by simp
    next
      case (cons c b)
      from \<open>c \<notin> b\<close>
      have "?Y(cons(c,b),d) \<subseteq> (if c\<in>d then ?Y(b,d) \<union> ?Y(b,d-{c}) else 0)"
        by auto
      with cons
      show ?case
        using subset_Finite
        by simp
    qed
    moreover
    assume "d \<in> {x \<union> b . x \<in> X}"
    ultimately
    show "Finite({a \<in> X . M(a) \<and> (\<lambda>x\<in>X. x \<union> b) ` a = d})"
      using subset_Finite[of "{a \<in> X . M(a) \<and> (\<lambda>x\<in>X. x \<union> b) ` a = d}"
          "{a \<in> X . (\<lambda>x\<in>X. x \<union> b) ` a = d}"] by auto
  next
    note \<open>M(X)\<close> \<open>M(b)\<close>
    moreover
    show "M(\<lambda>a\<in>X. a \<union> b)"
      using lam_closed[of "\<lambda> x . x\<union>b",OF _ \<open>M(X)\<close>] Un_closed[OF transM[OF _ \<open>M(X)\<close>] \<open>M(b)\<close>]
        tag_union_replacement[OF \<open>M(b)\<close>]
      by simp
    moreover from this
    have "{a \<union> b . a \<in> X} = (\<lambda>x\<in>X. x \<union> b) `` X"
      using image_lam by simp
    with calculation
    show "M({a \<union> b . a \<in> X})" by auto
    moreover from calculation
    show "(\<lambda>a\<in>X. a \<union> b) \<in> X \<rightarrow>\<^bsup>M\<^esup> {a \<union> b . a \<in> X}"
      using function_space_rel_char by (auto intro:lam_funtype)
    ultimately
    show "(\<lambda>a\<in>X. a \<union> b) \<in> surj\<^bsup>M\<^esup>(X,{a \<union> b . a \<in> X})" "M({a \<union> b . a \<in> X})"
      using surj_rel_char function_space_rel_char
      unfolding surj_def by auto
  next
  qed (simp add:\<open>M(X)\<close>)
  moreover from assms this
  show ?thesis
    using Finite_to_one_rel_surj_rel_imp_cardinal_rel_eq by simp
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_library_extra\<close>\<close>

context M_library
begin

subsection\<open>Results on relative cardinal exponentiation\<close>

lemma cexp_rel_eqpoll_rel_cong:
  assumes
    "A \<approx>\<^bsup>M\<^esup> A'" "B \<approx>\<^bsup>M\<^esup> B'" "M(A)" "M(A')" "M(B)" "M(B')"
  shows
    "A\<^bsup>\<up>B,M\<^esup> = A'\<^bsup>\<up>B',M\<^esup>"
  unfolding cexp_rel_def using cardinal_rel_eqpoll_rel_iff
    function_space_rel_eqpoll_rel_cong assms
  by simp

lemma cexp_rel_cexp_rel_cmult:
  assumes "M(\<kappa>)" "M(\<nu>1)" "M(\<nu>2)"
  shows "(\<kappa>\<^bsup>\<up>\<nu>1,M\<^esup>)\<^bsup>\<up>\<nu>2,M\<^esup> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes>\<^bsup>M\<^esup> \<nu>1,M\<^esup>"
proof -
  have "(\<kappa>\<^bsup>\<up>\<nu>1,M\<^esup>)\<^bsup>\<up>\<nu>2,M\<^esup> = (\<nu>1 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)\<^bsup>\<up>\<nu>2,M\<^esup>"
    using cardinal_rel_eqpoll_rel
    by (intro cexp_rel_eqpoll_rel_cong) (simp_all add:assms cexp_rel_def)
  also from assms
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<times> \<nu>1,M\<^esup>"
    unfolding cexp_rel_def using curry_eqpoll_rel[THEN cardinal_rel_cong] by blast
  also
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes>\<^bsup>M\<^esup> \<nu>1,M\<^esup>"
    using cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym]
    unfolding cmult_rel_def by (intro cexp_rel_eqpoll_rel_cong) (auto simp add:assms)
  finally
  show ?thesis .
qed

lemma cardinal_rel_Pow_rel: "M(X) \<Longrightarrow> |Pow_rel(M,X)|\<^bsup>M\<^esup> = 2\<^bsup>\<up>X,M\<^esup>" \<comment> \<open>Perhaps it's better with |X|\<close>
  using cardinal_rel_eqpoll_rel_iff[THEN iffD2,
      OF _ _ Pow_rel_eqpoll_rel_function_space_rel]
  unfolding cexp_rel_def by simp

lemma cantor_cexp_rel:
  assumes "Card_rel(M,\<nu>)" "M(\<nu>)"
  shows "\<nu> < 2\<^bsup>\<up>\<nu>,M\<^esup>"
  using assms Card_rel_is_Ord Card_rel_cexp_rel
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "2\<^bsup>\<up>\<nu>,M\<^esup> \<le> \<nu>"
  with assms
  have "|Pow_rel(M,\<nu>)|\<^bsup>M\<^esup> \<le> \<nu>"
    using cardinal_rel_Pow_rel[of \<nu>] by simp
  with assms
  have "Pow_rel(M,\<nu>) \<lesssim>\<^bsup>M\<^esup> \<nu>"
    using cardinal_rel_eqpoll_rel_iff Card_rel_le_imp_lepoll_rel Card_rel_cardinal_rel_eq
    by auto
  then
  obtain g where "g \<in> inj_rel(M,Pow_rel(M,\<nu>), \<nu>)"
    by blast
  moreover
  note \<open>M(\<nu>)\<close>
  moreover from calculation
  have "M(g)" by (auto dest:transM)
  ultimately
  show "False"
    using cantor_inj_rel by simp
qed simp

lemma countable_iff_lesspoll_rel_Aleph_rel_one:
  notes iff_trans[trans]
  assumes "M(C)"
  shows "countable\<^bsup>M\<^esup>(C) \<longleftrightarrow> C \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  using assms lesspoll_rel_csucc_rel[of \<omega> C] Aleph_rel_succ Aleph_rel_zero
  unfolding countable_rel_def by simp


lemma countable_iff_le_rel_Aleph_rel_one:
  notes iff_trans[trans]
  assumes "M(C)"
  shows "countable\<^bsup>M\<^esup>(C) \<longleftrightarrow> |C|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  from assms
  have "countable\<^bsup>M\<^esup>(C) \<longleftrightarrow> C \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using countable_iff_lesspoll_rel_Aleph_rel_one
    by simp
  also from assms
  have "\<dots> \<longleftrightarrow> |C|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym, THEN eq_lesspoll_rel_trans]
    by (auto intro:cardinal_rel_eqpoll_rel[THEN eq_lesspoll_rel_trans])
  finally
  show ?thesis .
qed

end \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

(* TODO: This can be generalized. *)
lemma (in M_cardinal_library) countable_fun_imp_countable_image:
  assumes "f:C \<rightarrow>\<^bsup>M\<^esup> B" "countable\<^bsup>M\<^esup>(C)" "\<And>c. c\<in>C \<Longrightarrow> countable\<^bsup>M\<^esup>(f`c)"
    "M(C)" "M(B)"
  shows "countable\<^bsup>M\<^esup>(\<Union>(f``C))"
  using assms function_space_rel_char image_fun[of f]
    cardinal_rel_RepFun_apply_le[of f C B]
    countable_rel_iff_cardinal_rel_le_nat[THEN iffD1, THEN [2] le_trans, of _ ]
    countable_rel_iff_cardinal_rel_le_nat
  by (rule_tac countable_rel_union_countable_rel)
    (auto dest:transM del:imageE)

end