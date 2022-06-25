section\<open>Relative DC\<close>

theory Pointed_DC_Relative
  imports
    Cardinal_Library_Relative

begin

consts dc_witness :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
primrec
  wit0   : "dc_witness(0,A,a,s,R) = a"
  witrec : "dc_witness(succ(n),A,a,s,R) = s`{x\<in>A. \<langle>dc_witness(n,A,a,s,R),x\<rangle>\<in>R}"

lemmas dc_witness_def = dc_witness_nat_def

relativize functional "dc_witness" "dc_witness_rel"
relationalize "dc_witness_rel" "is_dc_witness"
  (* definition
  is_dc_witness_fm where
  "is_dc_witness_fm(na, A, a, s, R, e) \<equiv> is_transrec_fm
                  (is_nat_case_fm
                    (a +\<^sub>\<omega> 8, (\<cdot>\<exists>\<cdot>\<cdot>4`2 is 0\<cdot> \<and> (\<cdot>\<exists>\<cdot>\<cdot>s +\<^sub>\<omega> 12`0 is 2\<cdot> \<and> Collect_fm(A +\<^sub>\<omega> 12, \<cdot>(\<cdot>\<exists>\<cdot>0 = 0\<cdot>\<cdot>) \<and> (\<cdot>\<exists>\<cdot>\<cdot>0 \<in> R +\<^sub>\<omega> 14\<cdot> \<and> pair_fm(3, 1, 0) \<cdot>\<cdot>)\<cdot>, 0) \<cdot>\<cdot>)\<cdot>\<cdot>), 2,
                     0), na, e)"
 *)
schematic_goal sats_is_dc_witness_fm_auto:
  assumes "na < length(env)" "e < length(env)"
  shows
    "   na \<in> \<omega> \<Longrightarrow>
    A \<in> \<omega> \<Longrightarrow>
    a \<in> \<omega> \<Longrightarrow>
    s \<in> \<omega> \<Longrightarrow>
    R \<in> \<omega> \<Longrightarrow>
    e \<in> \<omega> \<Longrightarrow>
    env \<in> list(Aa) \<Longrightarrow>
    0 \<in> Aa \<Longrightarrow>
    is_dc_witness(##Aa, nth(na, env), nth(A, env), nth(a, env), nth(s, env), nth(R, env), nth(e, env)) \<longleftrightarrow>
    Aa, env \<Turnstile> ?fm(nat, A, a, s, R, e)"
  unfolding is_dc_witness_def is_recursor_def
  by (rule is_transrec_iff_sats | simp_all)
    (rule iff_sats is_nat_case_iff_sats is_eclose_iff_sats sep_rules | simp add:assms)+

synthesize "is_dc_witness" from_schematic

manual_arity for "is_dc_witness_fm"
  unfolding is_dc_witness_fm_def apply (subst arity_transrec_fm)
       apply (simp add:arity) defer 3
      apply (simp add:arity) defer
     apply (subst arity_is_nat_case_fm)
           apply (simp add:arity del:arity_transrec_fm) prefer 5
  by (simp add:arity del:arity_transrec_fm)+

definition dcwit_body :: "[i,i,i,i,i] \<Rightarrow> o" where
  "dcwit_body(A,a,g,R) \<equiv> \<lambda>p. snd(p) = dc_witness(fst(p), A, a, g, R)"

relativize functional "dcwit_body" "dcwit_body_rel"
relationalize "dcwit_body_rel" "is_dcwit_body"

synthesize "is_dcwit_body" from_definition assuming "nonempty"
arity_theorem for "is_dcwit_body_fm"

context M_replacement
begin

lemma dc_witness_closed[intro,simp]:
  assumes "M(n)" "M(A)" "M(a)" "M(s)" "M(R)" "n\<in>nat"
  shows "M(dc_witness(n,A,a,s,R))"
  using \<open>n\<in>nat\<close>
proof(induct)
  case 0
  with \<open>M(a)\<close>
  show ?case
    unfolding dc_witness_def by simp
next
  case (succ x)
  with assms
  have "M(dc_witness(x,A,a,s,R))" (is "M(?b)")
    by simp
  moreover from this assms
  have "M(({?b}\<times>A)\<inter>R)" (is "M(?X)") by auto
  moreover
  have "{x\<in>A. \<langle>?b,x\<rangle>\<in>R} = {snd(y) . y\<in>?X}" (is "_ = ?Y")
    by(intro equalityI subsetI,force,auto)
  moreover from calculation
  have "M(?Y)"
    using lam_replacement_snd lam_replacement_imp_strong_replacement RepFun_closed
      snd_closed[OF transM]
    by auto
  ultimately
  show ?case
    using \<open>M(s)\<close> apply_closed
    unfolding dc_witness_def by simp
qed

lemma dc_witness_rel_char:
  assumes "M(A)"
  shows "dc_witness_rel(M,n,A,a,s,R) = dc_witness(n,A,a,s,R)"
proof -
  from assms
  have "{x \<in> A . \<langle>rec, x\<rangle> \<in> R} =  {x \<in> A . M(x) \<and> \<langle>rec, x\<rangle> \<in> R}" for rec
    by (auto dest:transM)
  then
  show ?thesis
    unfolding dc_witness_def dc_witness_rel_def by simp
qed

lemma (in M_basic) first_section_closed:
  assumes
    "M(A)" "M(a)" "M(R)"
  shows "M({x \<in> A . \<langle>a, x\<rangle> \<in> R})"
proof -
  have "{x \<in> A . \<langle>a, x\<rangle> \<in> R} = range({a} \<times> range(R) \<inter> R) \<inter> A"
    by (intro equalityI) auto
  with assms
  show ?thesis
    by simp
qed

lemma witness_into_A [TC]:
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>A"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0" "n\<in>nat"
    "M(A)" "M(a)" "M(s)" "M(R)"
  shows "dc_witness(n, A, a, s, R)\<in>A"
  using \<open>n\<in>nat\<close>
proof(induct n)
  case 0
  then show ?case using \<open>a\<in>A\<close> by simp
next
  case (succ x)
  with succ assms(1,3-)
  show ?case
    using nat_into_M first_section_closed
    by (simp, rule_tac rev_subsetD, rule_tac assms(2)[rule_format])
      auto
qed

end \<comment> \<open>\<^locale>\<open>M_replacement\<close>\<close>

locale M_DC = M_trancl + M_replacement + M_eclose +
  assumes
    separation_is_dcwit_body:
    "M(A) \<Longrightarrow> M(a) \<Longrightarrow> M(g) \<Longrightarrow> M(R) \<Longrightarrow> separation(M,is_dcwit_body(M, A, a, g, R))"
    and
    dcwit_replacement:"Ord(na) \<Longrightarrow>
    M(na) \<Longrightarrow>
    M(A) \<Longrightarrow>
    M(a) \<Longrightarrow>
    M(s) \<Longrightarrow>
    M(R) \<Longrightarrow>
    transrec_replacement
     (M, \<lambda>n f ntc.
            is_nat_case
             (M, a,
              \<lambda>m bmfm.
                 \<exists>fm[M]. \<exists>cp[M].
                    is_apply(M, f, m, fm) \<and>
                    is_Collect(M, A, \<lambda>x. \<exists>fmx[M]. (M(x) \<and> fmx \<in> R) \<and> pair(M, fm, x, fmx), cp) \<and>
                    is_apply(M, s, cp, bmfm),
              n, ntc),na)"
begin

lemma is_dc_witness_iff:
  assumes "Ord(na)" "M(na)" "M(A)" "M(a)" "M(s)" "M(R)" "M(res)"
  shows "is_dc_witness(M, na, A, a, s, R, res) \<longleftrightarrow> res = dc_witness_rel(M, na, A, a, s, R)"
proof -
  note assms
  moreover from this
  have "{x \<in> A . M(x) \<and> \<langle>f, x\<rangle> \<in> R} = {x \<in> A . \<langle>f, x\<rangle> \<in> R}" for f
    by (auto dest:transM)
  moreover from calculation
  have "M(fm) \<Longrightarrow> M({x \<in> A . M(x) \<and> \<langle>fm, x\<rangle> \<in> R})" for fm
    using first_section_closed by (auto dest:transM)
  moreover from calculation
  have "M(x) \<Longrightarrow> M(z) \<Longrightarrow> M(mesa) \<Longrightarrow>
    (\<exists>ya[M]. pair(M, x, ya, z) \<and>
      is_wfrec(M, \<lambda>n f. is_nat_case(M, a, \<lambda>m bmfm. \<exists>fm[M]. is_apply(M, f, m, fm) \<and>
        is_apply(M, s, {x \<in> A . \<langle>fm, x\<rangle> \<in> R}, bmfm), n), mesa, x, ya))
    \<longleftrightarrow>
    (\<exists>y[M]. pair(M, x, y, z) \<and>
      is_wfrec(M, \<lambda>n f. is_nat_case(M, a,
        \<lambda>m bmfm.
          \<exists>fm[M]. \<exists>cp[M]. is_apply(M, f, m, fm) \<and>
            is_Collect(M, A, \<lambda>x. M(x) \<and> \<langle>fm, x\<rangle> \<in> R, cp) \<and>  is_apply(M, s, cp, bmfm),n),
        mesa, x, y))" for x z mesa by simp
  moreover from calculation
  show ?thesis
    using assms dcwit_replacement[of na A a s R]
    unfolding is_dc_witness_def dc_witness_rel_def
    by (rule_tac recursor_abs) (auto dest:transM)
qed

lemma dcwit_body_abs:
  "fst(x) \<in> \<omega> \<Longrightarrow> M(A) \<Longrightarrow> M(a) \<Longrightarrow> M(g) \<Longrightarrow> M(R) \<Longrightarrow> M(x) \<Longrightarrow>
   is_dcwit_body(M,A,a,g,R,x) \<longleftrightarrow> dcwit_body(A,a,g,R,x)"
  using pair_in_M_iff apply_closed transM[of _ A]
    is_dc_witness_iff[of "fst(x)" "A" "a" "g" "R" "snd(x)"]
    fst_snd_closed dc_witness_closed
  unfolding dcwit_body_def is_dcwit_body_def
  by (auto dest:transM simp:absolut dc_witness_rel_char del:bexI intro!:bexI)

lemma separation_eq_dc_witness:
  "M(A) \<Longrightarrow>
    M(a) \<Longrightarrow>
    M(g) \<Longrightarrow>
    M(R) \<Longrightarrow>  separation(M,\<lambda>p. fst(p)\<in>\<omega> \<longrightarrow> snd(p) = dc_witness(fst(p), A, a, g, R))"
  using separation_is_dcwit_body dcwit_body_abs unfolding is_dcwit_body_def
  oops

lemma Lambda_dc_witness_closed:
  assumes "g \<in> Pow\<^bsup>M\<^esup>(A)-{0} \<rightarrow> A" "a\<in>A" "\<forall>y\<in>A. {x \<in> A . \<langle>y, x\<rangle> \<in> R} \<noteq> 0"
    "M(g)" "M(A)" "M(a)" "M(R)"
  shows "M(\<lambda>n\<in>nat. dc_witness(n,A,a,g,R))"
proof -
  from assms
  have "(\<lambda>n\<in>nat. dc_witness(n,A,a,g,R)) = {p \<in> \<omega> \<times> A . is_dcwit_body(M,A,a,g,R,p)}"
    using witness_into_A[of a A g R]
      Pow_rel_char apply_type[of g "{x \<in> Pow(A) . M(x)}-{0}" "\<lambda>_.A"]
    unfolding lam_def split_def
    apply (intro equalityI subsetI)
     apply (auto) (* slow *)
    by (subst dcwit_body_abs, simp_all add:transM[of _ \<omega>] dcwit_body_def,
        subst (asm) dcwit_body_abs, auto dest:transM simp:dcwit_body_def)
      (* by (intro equalityI subsetI, auto) (* Extremely slow *)
    (subst dcwit_body_abs, simp_all add:transM[of _ \<omega>] dcwit_body_def,
      subst (asm) dcwit_body_abs, auto dest:transM simp:dcwit_body_def) *)
  with assms
  show ?thesis
    using separation_is_dcwit_body dc_witness_rel_char unfolding split_def by simp
qed

lemma witness_related:
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0" "n\<in>nat"
    "M(a)" "M(A)" "M(s)" "M(R)" "M(n)"
  shows "\<langle>dc_witness(n, A, a, s, R),dc_witness(succ(n), A, a, s, R)\<rangle>\<in>R"
proof -
  note assms
  moreover from this
  have "(\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>A)" by auto
  moreover from calculation
  have "dc_witness(n, A, a, s, R)\<in>A" (is "?x \<in> A")
    using witness_into_A[of _ _ s R n] by simp
  moreover from assms
  have "M({x \<in> A . \<langle>dc_witness(n, A, a, s, R), x\<rangle> \<in> R})"
    using first_section_closed[of A "dc_witness(n, A, a, s, R)"]
    by simp
  ultimately
  show ?thesis by auto
qed

lemma witness_funtype:
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X \<in> A"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R} \<noteq> 0"
    "M(A)" "M(a)" "M(s)" "M(R)"
  shows "(\<lambda>n\<in>nat. dc_witness(n, A, a, s, R)) \<in> nat \<rightarrow> A" (is "?f \<in> _ \<rightarrow> _")
proof -
  have "?f \<in> nat \<rightarrow> {dc_witness(n, A, a, s, R). n\<in>nat}" (is "_ \<in> _ \<rightarrow> ?B")
    using lam_funtype assms by simp
  then
  have "?B \<subseteq> A"
    using witness_into_A assms by auto
  with \<open>?f \<in> _\<close>
  show ?thesis
    using fun_weaken_type
    by simp
qed

lemma witness_to_fun:
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>A"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0"
    "M(A)" "M(a)" "M(s)" "M(R)"
  shows "\<exists>f \<in> nat\<rightarrow>A. \<forall>n\<in>nat. f`n =dc_witness(n,A,a,s,R)"
  using assms bexI[of _ "\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)"] witness_funtype
  by simp

end \<comment> \<open>\<^locale>\<open>M_DC\<close>\<close>

locale M_library_DC = M_library + M_DC
begin

(* Should port the whole AC theory, including the absolute version
  of the following theorem *)
lemma AC_M_func:
  assumes "\<And>x. x \<in> A \<Longrightarrow> (\<exists>y. y \<in> x)" "M(A)"
  shows "\<exists>f \<in> A \<rightarrow>\<^bsup>M\<^esup> \<Union>(A). \<forall>x \<in> A. f`x \<in> x"
proof -
  from \<open>M(A)\<close>
  interpret mpiA:M_Pi_assumptions _ A "\<lambda>x. x"
    using Pi_replacement Pi_separation lam_replacement_identity
      lam_replacement_Sigfun[THEN lam_replacement_imp_strong_replacement]
    by unfold_locales (simp_all add:transM[of _ A])
  from \<open>M(A)\<close>
  interpret mpic_A:M_Pi_assumptions_choice _ A "\<lambda>x. x"
    apply unfold_locales
    using lam_replacement_constant lam_replacement_identity
      lam_replacement_identity[THEN lam_replacement_imp_strong_replacement]
      lam_replacement_minimum[THEN [5] lam_replacement_hcomp2]
    unfolding lam_replacement_def[symmetric]
    by auto
  from \<open>M(A)\<close>
  interpret mpi2:M_Pi_assumptions2 _ A "\<lambda>_. \<Union>A" "\<lambda>x. x"
    using Pi_replacement Pi_separation lam_replacement_constant
      lam_replacement_Sigfun[THEN lam_replacement_imp_strong_replacement,
        of  "\<lambda>_. \<Union>A"] Pi_replacement1[of _  "\<Union>A"] transM[of _  "A"]
    by unfold_locales auto
  from assms
  show ?thesis
    using mpi2.Pi_rel_type apply_type mpiA.mem_Pi_rel_abs mpi2.mem_Pi_rel_abs
      function_space_rel_char
    by (rule_tac mpic_A.AC_Pi_rel[THEN rexE], simp, rule_tac x=x in bexI)
      (auto, rule_tac C="\<lambda>x. x" in Pi_type, auto)
qed

lemma non_empty_family: "[| 0 \<notin> A;  x \<in> A |] ==> \<exists>y. y \<in> x"
  by (subgoal_tac "x \<noteq> 0", blast+)

lemma AC_M_func0: "0 \<notin> A \<Longrightarrow> M(A) \<Longrightarrow> \<exists>f \<in> A \<rightarrow>\<^bsup>M\<^esup> \<Union>(A). \<forall>x \<in> A. f`x \<in> x"
  by (rule AC_M_func) (simp_all add: non_empty_family)

lemma AC_M_func_Pow_rel:
  assumes "M(C)"
  shows "\<exists>f \<in> (Pow\<^bsup>M\<^esup>(C)-{0}) \<rightarrow>\<^bsup>M\<^esup> C. \<forall>x \<in> Pow\<^bsup>M\<^esup>(C)-{0}. f`x \<in> x"
proof -
  have "0\<notin>Pow\<^bsup>M\<^esup>(C)-{0}" by simp
  with assms
  obtain f where "f \<in> (Pow\<^bsup>M\<^esup>(C)-{0}) \<rightarrow>\<^bsup>M\<^esup> \<Union>(Pow\<^bsup>M\<^esup>(C)-{0})" "\<forall>x \<in> Pow\<^bsup>M\<^esup>(C)-{0}. f`x \<in> x"
    using AC_M_func0[OF \<open>0\<notin>_\<close>] by auto
  moreover
  have "x\<subseteq>C" if "x \<in> Pow\<^bsup>M\<^esup>(C) - {0}" for x
    using that Pow_rel_char assms
    by auto
  moreover
  have "\<Union>(Pow\<^bsup>M\<^esup>(C) - {0}) \<subseteq> C"
    using assms Pow_rel_char by auto
  ultimately
  show ?thesis
    using assms function_space_rel_char
    by (rule_tac bexI,auto,rule_tac Pi_weaken_type,simp_all)
qed

theorem pointed_DC:
  assumes "\<forall>x\<in>A. \<exists>y\<in>A. \<langle>x,y\<rangle>\<in> R" "M(A)" "M(R)"
  shows "\<forall>a\<in>A. \<exists>f \<in> nat\<rightarrow>\<^bsup>M\<^esup> A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>R)"
proof -
  have 0:"\<forall>y\<in>A. {x \<in> A . \<langle>y, x\<rangle> \<in> R} \<noteq> 0"
    using assms by auto
  from \<open>M(A)\<close>
  obtain g where 1: "g \<in> Pow\<^bsup>M\<^esup>(A)-{0} \<rightarrow> A" "\<forall>X[M]. X \<noteq> 0 \<and> X \<subseteq> A \<longrightarrow> g ` X \<in> X"
    "M(g)"
    using AC_M_func_Pow_rel[of A] mem_Pow_rel_abs
      function_space_rel_char[of "Pow\<^bsup>M\<^esup>(A)-{0}" A] by auto
  then
  have 2:"\<forall>X[M]. X \<noteq> 0 \<and> X \<subseteq> A \<longrightarrow> g ` X \<in> A" by auto
  {
    fix a
    assume "a\<in>A"
    let ?f ="\<lambda>n\<in>nat. dc_witness(n,A,a,g,R)"
    note \<open>a\<in>A\<close>
    moreover from this
    have f0: "?f`0 = a" by simp
    moreover
    note \<open>a\<in>A\<close> \<open>M(g)\<close> \<open>M(A)\<close> \<open>M(R)\<close>
    moreover from calculation
    have "\<langle>?f ` n, ?f ` succ(n)\<rangle> \<in> R" if "n\<in>nat" for n
      using witness_related[OF \<open>a\<in>A\<close> _ 0, of g n] 1 that
      by (auto dest:transM)
    ultimately
    have "\<exists>f[M]. f\<in>nat \<rightarrow> A \<and> f ` 0 = a \<and> (\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> R)"
      using 0 1 \<open>a\<in>_\<close>
      by (rule_tac x="(\<lambda>n\<in>\<omega>. dc_witness(n, A, a, g, R))" in rexI)
        (simp_all, rule_tac witness_funtype,
          auto intro!: Lambda_dc_witness_closed dest:transM)
  }
  with \<open>M(A)\<close>
  show ?thesis using function_space_rel_char by auto
qed

lemma aux_DC_on_AxNat2 : "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R \<Longrightarrow>
                  \<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> {\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  by (rule ballI, erule_tac x="x" in ballE, simp_all)

lemma infer_snd : "c\<in> A\<times>B \<Longrightarrow> snd(c) = k \<Longrightarrow> c=\<langle>fst(c),k\<rangle>"
  by auto

corollary DC_on_A_x_nat :
  assumes "(\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R)" "a\<in>A" "M(A)" "M(R)"
  shows "\<exists>f \<in> nat\<rightarrow>\<^bsup>M\<^esup>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>\<langle>f`n,n\<rangle>,\<langle>f`succ(n),succ(n)\<rangle>\<rangle>\<in>R)" (is "\<exists>x\<in>_.?P(x)")
proof -
  let ?R'="{\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  from assms(1)
  have "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> ?R'"
    using aux_DC_on_AxNat2 by simp
  moreover
  note \<open>a\<in>_\<close> \<open>M(A)\<close>
  moreover from this
  have "M(A \<times> \<omega>)" by simp
  have "lam_replacement(M, \<lambda>x. succ(snd(fst(x))))"
    using lam_replacement_fst lam_replacement_snd lam_replacement_hcomp
      lam_replacement_hcomp[of _ "\<lambda>x. succ(snd(x))"]
      lam_replacement_succ by simp
  with \<open>M(R)\<close>
  have "M(?R')"
    using separation_eq lam_replacement_fst lam_replacement_snd
      lam_replacement_succ lam_replacement_hcomp lam_replacement_identity
    unfolding split_def by simp
  ultimately
  obtain f where
    F:"f\<in>nat\<rightarrow>\<^bsup>M\<^esup> A\<times>\<omega>" "f ` 0 = \<langle>a,0\<rangle>"  "\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> ?R'"
    using pointed_DC[of "A\<times>nat" ?R'] by blast
  with \<open>M(A)\<close>
  have "M(f)" using function_space_rel_char by simp
  then
  have "M(\<lambda>x\<in>nat. fst(f`x))" (is "M(?f)")
    using lam_replacement_fst lam_replacement_hcomp
      lam_replacement_constant lam_replacement_identity
      lam_replacement_apply
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
      auto
  with F \<open>M(A)\<close>
  have "?f\<in>nat\<rightarrow>\<^bsup>M\<^esup> A" "?f ` 0 = a" using function_space_rel_char by auto
  have 1:"n\<in> nat \<Longrightarrow> f`n= \<langle>?f`n, n\<rangle>" for n
  proof(induct n set:nat)
    case 0
    then show ?case using F by simp
  next
    case (succ x)
    with \<open>M(A)\<close>
    have "\<langle>f`x, f`succ(x)\<rangle> \<in> ?R'" "f`x \<in> A\<times>nat" "f`succ(x)\<in>A\<times>nat"
      using F function_space_rel_char[of \<omega> "A\<times>\<omega>"] by auto
    then
    have "snd(f`succ(x)) = succ(snd(f`x))" by simp
    with succ \<open>f`x\<in>_\<close>
    show ?case using infer_snd[OF \<open>f`succ(_)\<in>_\<close>] by auto
  qed
  have "\<langle>\<langle>?f`n,n\<rangle>,\<langle>?f`succ(n),succ(n)\<rangle>\<rangle> \<in> R" if "n\<in>nat" for n
    using that 1[of "succ(n)"] 1[OF \<open>n\<in>_\<close>] F(3) by simp
  with \<open>f`0=\<langle>a,0\<rangle>\<close>
  show ?thesis
    using rev_bexI[OF \<open>?f\<in>_\<close>] by simp
qed

lemma aux_sequence_DC :
  assumes "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n"
    "R={\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle> \<in> (A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  shows "\<forall> x\<in>A\<times>nat . \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R"
  using assms Pair_fst_snd_eq by auto

lemma aux_sequence_DC2 : "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n \<Longrightarrow>
        \<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> {\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle>\<in>(A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  by auto

lemma sequence_DC:
  assumes "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n" "M(A)" "M(S)"
  shows "\<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>\<^bsup>M\<^esup> A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>S`succ(n)))"
proof -
  from \<open>M(S)\<close>
  have "lam_replacement(M, \<lambda>x. S ` snd(snd(x)))"
    using lam_replacement_snd lam_replacement_hcomp
      lam_replacement_hcomp[of _ "\<lambda>x. S`snd(x)"] lam_replacement_apply by simp
  with assms
  have "M({x \<in> (A \<times> \<omega>) \<times> A \<times> \<omega> . (\<lambda>\<langle>\<langle>x,n\<rangle>,y,m\<rangle>. \<langle>x, y\<rangle> \<in> S ` m)(x)})"
    using lam_replacement_fst lam_replacement_snd
      lam_replacement_Pair[THEN [5] lam_replacement_hcomp2,
        of "\<lambda>x. fst(fst(x))" "\<lambda>x. fst(snd(x))", THEN [2] separation_in,
        of "\<lambda>x. S ` snd(snd(x))"] lam_replacement_apply[of S]
      lam_replacement_hcomp unfolding split_def by simp
  with assms
  show ?thesis
    by (rule_tac ballI) (drule aux_sequence_DC2, drule DC_on_A_x_nat, auto)
qed

end \<comment> \<open>\<^locale>\<open>M_library_DC\<close>\<close>

end