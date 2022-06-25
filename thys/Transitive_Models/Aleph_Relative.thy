theory Aleph_Relative
  imports
    CardinalArith_Relative
begin

definition
  HAleph :: "[i,i] \<Rightarrow> i" where
  "HAleph(i,r) \<equiv> if(\<not>(Ord(i)),i,if(i=0, nat, if(\<not>Limit(i) \<and> i\<noteq>0,
                            csucc(r`( \<Union> i )),
                                   \<Union>j\<in>i. r`j)))"

reldb_add functional "Limit" "Limit"
relationalize "Limit" "is_Limit" external
synthesize "is_Limit" from_definition
arity_theorem for "is_Limit_fm"

relativize functional "HAleph" "HAleph_rel"
relationalize "HAleph_rel" "is_HAleph"

synthesize "is_HAleph" from_definition assuming "nonempty"
arity_theorem intermediate for "is_HAleph_fm"

lemma arity_is_HAleph_fm_aux:
  assumes
    "i \<in> nat" "r \<in> nat"
    \<comment> \<open>NOTE: assumptions are \<^bold>\<open>not\<close> used, but if omitted, next lemma fails!\<close>
  shows
    "arity(Replace_fm(8 +\<^sub>\<omega> i, \<cdot>10 +\<^sub>\<omega> r`0 is 1\<cdot>, 3)) = 9 +\<^sub>\<omega> i \<union> pred(pred(11 +\<^sub>\<omega> r))"
  using arity_Replace_fm[of "\<cdot> (10+\<^sub>\<omega>r)`0 is 1\<cdot>" "8+\<^sub>\<omega>i" 3 "(11+\<^sub>\<omega>r) \<union> 1 \<union> 2"]
    ord_simp_union
  by (auto simp:arity)

lemma arity_is_HAleph_fm[arity]:
  assumes
    "i \<in> nat" "r \<in> nat" "l \<in> nat"
  shows
    "arity(is_HAleph_fm(i, r, l)) =  succ(i) \<union> succ(l) \<union> succ(r)"
  using assms pred_Un arity_is_HAleph_fm_aux arity_is_HAleph_fm'
  by auto

definition
  Aleph' :: "i => i"  where
  "Aleph'(a) == transrec(a,\<lambda>i r. HAleph(i,r))"

relativize functional "Aleph'" "Aleph_rel"
relationalize "Aleph_rel" "is_Aleph"

txt\<open>The extra assumptions \<^term>\<open>a < length(env)\<close> and \<^term>\<open>c < length(env)\<close>
    in this schematic goal (and the following results on synthesis that
    depend on it) are imposed by @{thm is_transrec_iff_sats}.\<close>
schematic_goal sats_is_Aleph_fm_auto:
  "a \<in> nat \<Longrightarrow> c \<in> nat \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
  a < length(env) \<Longrightarrow> c < length(env) \<Longrightarrow> 0 \<in> A \<Longrightarrow>
  is_Aleph(##A, nth(a, env), nth(c, env)) \<longleftrightarrow> A, env \<Turnstile> ?fm(a, c)"
  unfolding is_Aleph_def
proof (rule is_transrec_iff_sats, rule_tac [1] is_HAleph_iff_sats)
  fix a0 a1 a2 a3 a4 a5 a6 a7
  let ?env' = "Cons(a0, Cons(a1, Cons(a2, Cons(a3, Cons(a4, Cons(a5, Cons(a6, Cons(a7, env))))))))"
  show "nth(2, ?env') = a2"
    "nth(1, ?env') = a1"
    "nth(0, ?env') = a0"
    "nth(c, env) = nth(c, env)"
    by simp_all
qed simp_all

synthesize_notc "is_Aleph" from_schematic

notation is_Aleph_fm (\<open>\<cdot>\<aleph>'(_') is _\<cdot>\<close>)

lemma is_Aleph_fm_type [TC]: "a \<in> nat \<Longrightarrow> c \<in> nat \<Longrightarrow> is_Aleph_fm(a, c) \<in> formula"
  unfolding is_Aleph_fm_def by simp

lemma sats_is_Aleph_fm:
  assumes "f\<in>nat" "r\<in>nat" "env \<in> list(A)" "0\<in>A" "f < length(env)" "r< length(env)"
  shows "is_Aleph(##A, nth(f, env), nth(r, env)) \<longleftrightarrow> A, env \<Turnstile> is_Aleph_fm(f,r)"
  using assms sats_is_Aleph_fm_auto unfolding is_Aleph_def is_Aleph_fm_def by simp

lemma is_Aleph_iff_sats [iff_sats]:
  assumes
    "nth(f, env) = fa" "nth(r, env) = ra" "f < length(env)" "r< length(env)"
    "f \<in> nat" "r \<in> nat" "env \<in> list(A)" "0\<in>A"
  shows "is_Aleph(##A,fa,ra) \<longleftrightarrow> A, env \<Turnstile> is_Aleph_fm(f,r)"
  using assms sats_is_Aleph_fm[of f r env A] by simp

arity_theorem for "is_Aleph_fm"

lemma (in M_cardinal_arith_jump) is_Limit_iff:
  assumes "M(a)"
  shows "is_Limit(M,a) \<longleftrightarrow> Limit(a)"
  unfolding is_Limit_def Limit_def using lt_abs transM[OF ltD \<open>M(a)\<close>] assms
  by auto

lemma HAleph_eq_Aleph_recursive:
  "Ord(i) \<Longrightarrow> HAleph(i,r) = (if i = 0 then nat
                else if \<exists>j. i = succ(j) then csucc(r ` (THE j. i = succ(j))) else \<Union>j<i. r ` j)"
proof -
  assume "Ord(i)"
  moreover from this
  have "i = succ(j) \<Longrightarrow> (\<Union>succ(j)) = j" for j
    using Ord_Union_succ_eq by simp
  moreover from \<open>Ord(i)\<close>
  have "(\<exists>j. i = succ(j)) \<longleftrightarrow> \<not>Limit(i) \<and> i \<noteq> 0"
    using Ord_cases_disj by auto
  ultimately
  show ?thesis
    unfolding HAleph_def OUnion_def
    by auto
qed

lemma Aleph'_eq_Aleph: "Ord(a) \<Longrightarrow> Aleph'(a) = Aleph(a)"
  unfolding Aleph'_def Aleph_def transrec2_def
  using HAleph_eq_Aleph_recursive
  by (intro transrec_equal_on_Ord) auto

reldb_rem functional "Aleph'"
reldb_rem relational "is_Aleph"
reldb_add functional "Aleph" "Aleph_rel"
reldb_add relational "Aleph" "is_Aleph"

abbreviation
  Aleph_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r(a,M) \<equiv> Aleph_rel(M,a)"

abbreviation
  Aleph_r_set :: "[i,i] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r_set(a,M) \<equiv> Aleph_rel(##M,a)"

lemma Aleph_rel_def': "Aleph_rel(M,a) \<equiv> transrec(a, \<lambda>i r. HAleph_rel(M, i, r))"
  unfolding Aleph_rel_def .

lemma succ_mem_Limit: "Limit(j) \<Longrightarrow> i \<in> j \<Longrightarrow> succ(i) \<in> j"
  using Limit_has_succ[THEN ltD] ltI Limit_is_Ord by auto

locale M_pre_aleph = M_eclose + M_cardinal_arith_jump +
  assumes
    haleph_transrec_replacement: "M(a) \<Longrightarrow> transrec_replacement(M,is_HAleph(M),a)"

begin

lemma aux_ex_Replace_funapply:
  assumes "M(a)" "M(f)"
  shows "\<exists>x[M]. is_Replace(M, a, \<lambda>j y. f ` j = y, x)"
proof -
  have "{f`j . j\<in>a} = {y . j\<in>a , f ` j=y}"
    "{y . j\<in>a , f ` j=y} = {y . j\<in>a , y =f ` j}"
    by auto
  moreover
  note assms
  moreover from calculation
  have "x \<in> a \<Longrightarrow> y = f `x \<Longrightarrow> M(y)" for x y
    using transM[OF _ \<open>M(a)\<close>] by auto
  moreover from assms
  have "M({f`j . j\<in>a})"
    using transM[OF _ \<open>M(a)\<close>] RepFun_closed[OF apply_replacement] by simp
  ultimately
  have 2:"is_Replace(M, a, \<lambda>j y. y = f ` j, {f`j . j\<in>a})"
    using Replace_abs[of _ _ "\<lambda>j y. y = f ` j",OF \<open>M(a)\<close>,THEN iffD2]
    by auto
  with \<open>M({f`j . j\<in>a})\<close>
  show ?thesis
    using
      is_Replace_cong[of _ _ M "\<lambda>j y. y = f ` j" "\<lambda>j y. f ` j = y", THEN iffD1,OF _ _ _ 2]
    by auto
qed

lemma is_HAleph_zero:
  assumes "M(f)"
  shows "is_HAleph(M,0,f,res) \<longleftrightarrow> res = nat"
  unfolding is_HAleph_def
  using Ord_0 If_abs is_Limit_iff is_csucc_iff assms aux_ex_Replace_funapply
  by auto

lemma is_HAleph_succ:
  assumes "M(f)" "M(x)" "Ord(x)" "M(res)"
  shows "is_HAleph(M,succ(x),f,res) \<longleftrightarrow> res = csucc_rel(M,f`x)"
  unfolding is_HAleph_def
  using assms is_Limit_iff is_csucc_iff aux_ex_Replace_funapply If_abs Ord_Union_succ_eq
  by simp

lemma is_HAleph_limit:
  assumes "M(f)" "M(x)" "Limit(x)" "M(res)"
  shows "is_HAleph(M,x,f,res) \<longleftrightarrow> res = (\<Union>{y . i\<in>x ,M(i) \<and> M(y) \<and> y = f`i})"
proof -
  from assms
  have "univalent(M, x, \<lambda>j y. y = f ` j  )"
    "(\<And>xa y. xa \<in> x \<Longrightarrow> f ` xa = y \<Longrightarrow> M(y))"
    "{y . x \<in> x, f ` x = y} = {y . i\<in>x ,M(i) \<and> M(y) \<and> y = f`i}"
    using univalent_triv[of M x "\<lambda>j .f ` j"] transM[OF _ \<open>M(x)\<close>]
    by auto
  moreover
  from this
  have "univalent(M, x, \<lambda>j y. f ` j = y )"
    by (rule_tac univalent_cong[of x x M " \<lambda>j y. y = f ` j" " \<lambda>j y. f ` j=y",THEN iffD1], auto)
  moreover
  from this
  have "univalent(M, x, \<lambda>j y. M(j) \<and> M(y) \<and> f ` j = y )"
    by auto
  ultimately
  show ?thesis
    unfolding is_HAleph_def
    using assms is_Limit_iff Limit_is_Ord zero_not_Limit If_abs is_csucc_iff
      Replace_abs apply_replacement
    by auto
qed

lemma is_HAleph_iff:
  assumes "M(a)" "M(f)" "M(res)"
  shows "is_HAleph(M, a, f, res) \<longleftrightarrow> res = HAleph_rel(M, a, f)"
proof(cases "Ord(a)")
  case True
  note Ord_cases[OF \<open>Ord(a)\<close>]
  then
  show ?thesis
  proof(cases )
    case 1
    with True assms
    show ?thesis
      using is_HAleph_zero unfolding HAleph_rel_def
      by simp
  next
    case (2 j)
    with True assms
    show ?thesis
      using is_HAleph_succ Ord_Union_succ_eq
      unfolding HAleph_rel_def
      by simp
  next
    case 3
    with assms
    show ?thesis
      using is_HAleph_limit zero_not_Limit Limit_is_Ord
      unfolding HAleph_rel_def
      by auto
  qed
next
  case False
  then
  have "\<not>Limit(a)" "a\<noteq>0" "\<And> x . Ord(x) \<Longrightarrow> a\<noteq>succ(x)"
    using Limit_is_Ord by auto
  with False
  show ?thesis
    unfolding is_HAleph_def HAleph_rel_def
    using assms is_Limit_iff If_abs is_csucc_iff aux_ex_Replace_funapply
    by auto
qed

lemma HAleph_rel_closed [intro,simp]:
  assumes "function(f)" "M(a)" "M(f)"
  shows "M(HAleph_rel(M,a,f))"
  unfolding HAleph_rel_def
  using assms apply_replacement
  by simp

lemma Aleph_rel_closed[intro, simp]:
  assumes "Ord(a)" "M(a)"
  shows "M(Aleph_rel(M,a))"
proof -
  have "relation2(M, is_HAleph(M), HAleph_rel(M))"
    unfolding relation2_def using is_HAleph_iff assms by simp
  moreover
  have "\<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(HAleph_rel(M, x, g))"
    using HAleph_rel_closed by simp
  moreover
  note assms
  ultimately
  show ?thesis
    unfolding Aleph_rel_def
    using transrec_closed[of "is_HAleph(M)" a "HAleph_rel(M)"]
      haleph_transrec_replacement  by simp
qed

lemma Aleph_rel_zero: "\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup> = nat"
  using def_transrec [OF Aleph_rel_def',of _ 0]
  unfolding HAleph_rel_def by simp

lemma Aleph_rel_succ: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> = (\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
  using Ord_Union_succ_eq
  by (subst def_transrec [OF Aleph_rel_def'])
    (simp add:HAleph_rel_def)

lemma Aleph_rel_limit:
  assumes "Limit(\<alpha>)" "M(\<alpha>)"
  shows "\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> = \<Union>{\<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup> . j \<in> \<alpha>}"
proof -
  note trans=transM[OF _ \<open>M(\<alpha>)\<close>]
  from \<open>M(\<alpha>)\<close>
  have "\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> = HAleph_rel(M, \<alpha>, \<lambda>x\<in>\<alpha>. \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)"
    using def_transrec [OF Aleph_rel_def',of M \<alpha>] by simp
  also
  have "... = \<Union>{a . j \<in> \<alpha>, M(a) \<and> a = \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>}"
    unfolding HAleph_rel_def
    using assms zero_not_Limit Limit_is_Ord trans by auto
  also
  have "... = \<Union>{\<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup> . j \<in> \<alpha>}"
    using Aleph_rel_closed[OF _ trans] Ord_in_Ord Limit_is_Ord[OF \<open>Limit(\<alpha>)\<close>] by auto
  finally
  show ?thesis .
qed

lemma is_Aleph_iff:
  assumes "Ord(a)" "M(a)" "M(res)"
  shows "is_Aleph(M, a, res) \<longleftrightarrow> res = \<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>"
proof -
  have "relation2(M, is_HAleph(M), HAleph_rel(M))"
    unfolding relation2_def using is_HAleph_iff assms by simp
  moreover
  have "\<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(HAleph_rel(M, x, g))"
    using HAleph_rel_closed by simp
  ultimately
  show ?thesis
    using assms transrec_abs haleph_transrec_replacement
    unfolding is_Aleph_def Aleph_rel_def
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_pre_aleph\<close>\<close>

locale M_aleph = M_pre_aleph +
  assumes
    aleph_rel_replacement: "strong_replacement(M, \<lambda>x y. Ord(x) \<and> y = \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)"
begin

lemma Aleph_rel_cont: "Limit(l) \<Longrightarrow> M(l) \<Longrightarrow> \<aleph>\<^bsub>l\<^esub>\<^bsup>M\<^esup> = (\<Union>i<l. \<aleph>\<^bsub>i\<^esub>\<^bsup>M\<^esup>)"
  using Limit_is_Ord Aleph_rel_limit
  by (simp add:OUnion_def)

lemma Ord_Aleph_rel:
  assumes "Ord(a)"
  shows "M(a) \<Longrightarrow> Ord(\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>)"
  using \<open>Ord(a)\<close>
proof(induct a rule:trans_induct3)
  case 0
  show ?case using Aleph_rel_zero by simp
next
  case (succ x)
  with \<open>Ord(x)\<close>
  have "M(x)" "Ord(\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)" by simp_all
  with \<open>Ord(x)\<close>
  have "Ord(csucc_rel(M,\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>))"
    using Card_rel_is_Ord Card_rel_csucc_rel
    by simp
  with \<open>Ord(x)\<close> \<open>M(x)\<close>
  show ?case using Aleph_rel_succ by simp
next
  case (limit x)
  note trans=transM[OF _ \<open>M(x)\<close>]
  from limit
  have "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> = (\<Union>i\<in>x. \<aleph>\<^bsub>i\<^esub>\<^bsup>M\<^esup>)"
    using Aleph_rel_cont OUnion_def Limit_is_Ord
    by auto
  with limit
  show ?case using Ord_UN trans by auto
qed

lemma Card_rel_Aleph_rel [simp, intro]:
  assumes "Ord(a)" and types: "M(a)" shows "Card\<^bsup>M\<^esup>(\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>)"
  using assms
proof (induct rule:trans_induct3)
  case 0
  then
  show ?case
    using Aleph_rel_zero Card_rel_nat by simp
next
  case (succ x)
  then
  show ?case
    using Card_rel_csucc_rel Ord_Aleph_rel Aleph_rel_succ
    by simp
next
  case (limit x)
  moreover
  from this
  have "M({y . z \<in> x, M(y) \<and> M(z) \<and> Ord(z) \<and> y = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>})"
    using aleph_rel_replacement
    by auto
  moreover
  have "{y . z \<in> x, M(y) \<and> M(z) \<and> y = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>} = {y . z \<in> x, M(y) \<and> M(z) \<and> Ord(z) \<and> y = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>}"
    using Ord_in_Ord Limit_is_Ord[OF limit(1)] by simp
  ultimately
  show ?case
    using Ord_Aleph_rel Card_nat Limit_is_Ord Card_relI
    by (subst def_transrec [OF Aleph_rel_def'])
      (auto simp add:HAleph_rel_def)
qed

lemma Aleph_rel_increasing:
  assumes "a < b" and types: "M(a)" "M(b)"
  shows "\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
proof -
  { fix x
    from assms
    have "Ord(b)"
      by (blast intro: lt_Ord2)
    moreover
    assume "M(x)"
    moreover
    note \<open>M(b)\<close>
    ultimately
    have "x < b \<Longrightarrow> \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
    proof (induct b arbitrary: x rule: trans_induct3)
      case 0 thus ?case by simp
    next
      case (succ b)
      then
      show ?case
        using Card_rel_csucc_rel Ord_Aleph_rel Ord_Union_succ_eq lt_csucc_rel
          lt_trans[of _ "\<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>" "csucc\<^bsup>M\<^esup>(\<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>)"]
        by (subst (2) def_transrec[OF Aleph_rel_def'])
          (auto simp add: le_iff HAleph_rel_def)
    next
      case (limit l)
      then
      have sc: "succ(x) < l"
        by (blast intro: Limit_has_succ)
      then
      have "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> < (\<Union>j<l. \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>)"
        using limit Ord_Aleph_rel Ord_OUN
      proof(rule_tac OUN_upper_lt,blast intro: Card_rel_is_Ord ltD lt_Ord)
        from \<open>x<l\<close> \<open>Limit(l)\<close>
        have "Ord(x)"
          using Limit_is_Ord Ord_in_Ord
          by (auto dest!:ltD)
        with \<open>M(x)\<close>
        show "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>succ(x)\<^esub>\<^bsup>M\<^esup>"
          using Card_rel_csucc_rel Ord_Aleph_rel lt_csucc_rel
            ltD[THEN [2] Ord_in_Ord] succ_in_MI[OF \<open>M(x)\<close>]
            Aleph_rel_succ[of x]
          by (simp)
      next
        from \<open>M(l)\<close> \<open>Limit(l)\<close>
        show "Ord(\<Union>j<l. \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>)"
          using Ord_Aleph_rel lt_Ord Limit_is_Ord Ord_in_Ord
          by (rule_tac Ord_OUN)
            (auto dest:transM ltD intro!:Ord_Aleph_rel)
      qed
      then
      show ?case using limit Aleph_rel_cont by simp
    qed
  }
  with types assms
  show ?thesis by simp
qed

lemmas nat_subset_Aleph_rel_1 =
  Ord_lt_subset[OF Ord_Aleph_rel[of 1] Aleph_rel_increasing[of 0 1,simplified],simplified]

end \<comment> \<open>\<^locale>\<open>M_aleph\<close>\<close>

end