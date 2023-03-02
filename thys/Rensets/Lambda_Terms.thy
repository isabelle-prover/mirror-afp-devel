section \<open> Lambda Terms \<close>

theory Lambda_Terms
  imports Main
begin

text \<open>This theory defines pre-terms and alpha-equivalence, and then 
defines terms as alpha-equivalence classes of pre-terms.\<close>

hide_type var

abbreviation (input) "any \<equiv> undefined"


subsection \<open>Variables\<close>

datatype var = Variable nat


subsection \<open>Pre-terms and operators on them\<close>

datatype ptrm = PVr var | PAp ptrm ptrm | PLm var ptrm


(* Freshness: *)

inductive pfresh :: "var \<Rightarrow> ptrm \<Rightarrow> bool" where 
  PVr[intro]: "z \<noteq> x \<Longrightarrow> pfresh z (PVr x)"
|PAp[intro]: "pfresh z t1 \<Longrightarrow> pfresh z t2 \<Longrightarrow> pfresh z (PAp t1 t2)"
|PLm[intro]: "z = x \<or> pfresh z t \<Longrightarrow> pfresh z (PLm x t)"

lemma pfresh_simps[simp]: 
  "pfresh z (PVr x) \<longleftrightarrow> z \<noteq> x"
  "pfresh z (PAp t1 t2) \<longleftrightarrow> pfresh z t1 \<and> pfresh z t2"
  "pfresh z (PLm x t) \<longleftrightarrow> z = x \<or> pfresh z t"
  using pfresh.cases by blast+


(* Pick pfresh: *)
lemma inj_Variable: "inj Variable"
  unfolding inj_def by auto

lemma infinite_var: "infinite (UNIV::var set)"  
  using infinite_iff_countable_subset inj_Variable by auto

lemma exists_var:
  assumes "finite X"
  shows "\<exists> x::var. x \<notin> X"
  by (simp add: assms ex_new_if_finite infinite_var)

lemma finite_neg_imp: 
  assumes "finite {x. \<not> \<phi> x}" and "finite {x. \<chi> x}"
  shows "finite {x. \<phi> x \<longrightarrow> \<chi> x}"
  using finite_UnI[OF assms]  by (simp add: Collect_imp_eq Collect_neg_eq)

lemma cofinite_pfresh: "finite {x . \<not> pfresh x t}"
  by (induct t) (simp_all add: finite_neg_imp)

lemma cofinite_list_ptrm: "finite {x . \<exists> t \<in> set ts. \<not> pfresh x t}"
proof (induct ts) 
  case Nil
  then show ?case using infinite_var by auto
next
  case (Cons t ts)
  have "{x. \<exists>t\<in>set (t # ts). \<not> pfresh x t} \<subseteq> 
   {x. \<not> pfresh x t} \<union> {x. \<exists>s\<in>set ts. \<not> pfresh x s}" by auto 
  then show ?case using Cons
    by (simp add: cofinite_pfresh finite_subset)
qed 

lemma exists_pfresh_set:
  assumes "finite X"
  shows "\<exists> z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>t \<in> set ts. pfresh z t)"
proof-
  have 0: "finite (X \<union> set xs \<union> {x. \<exists>s\<in>set ts. \<not> pfresh x s})" 
    using assms by (simp add: cofinite_list_ptrm)
  show ?thesis using exists_var[OF 0] by simp
qed

lemma exists_pfresh:
  "\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set ts. pfresh z t)"
  using exists_pfresh_set by blast

definition pickFreshS :: "var set \<Rightarrow> var list \<Rightarrow> ptrm list \<Rightarrow> var" where 
  "pickFreshS X xs ts \<equiv> SOME z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>t \<in> set ts. pfresh z t)" 

lemma pickFreshS: 
  assumes "finite X"
  shows "pickFreshS X xs ts \<notin> X \<and> pickFreshS X xs ts \<notin> set xs \<and> 
       (\<forall>t \<in> set ts. pfresh (pickFreshS X xs ts) t)"
  using exists_pfresh_set[OF assms] unfolding pickFreshS_def 
  by (rule someI_ex)

lemmas pickFreshS_set = pickFreshS[THEN conjunct1]
  and pickFreshS_var = pickFreshS[THEN conjunct2, THEN conjunct1]
  and pickFreshS_ptrm = pickFreshS[THEN conjunct2, THEN conjunct2, unfolded Ball_def, rule_format]

(* Unconditional form of pick-pfresh, without any set: *)
definition "pickFresh \<equiv> pickFreshS {}"

lemmas pickFresh_var = pickFreshS_var[OF finite.emptyI, unfolded pickFresh_def[symmetric]]
  and pickFresh_ptrm = pickFreshS_ptrm[OF finite.emptyI, unfolded pickFresh_def[symmetric]]

(* Swapping *)

definition sw :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" where 
  "sw x y z \<equiv> if x = y then z else if x = z then y else x"

lemma sw_eqL[simp,intro!]: "\<And> x y z. sw x x y = y"
  and sw_eqR[simp,intro!]: "\<And> x y z. sw x y x = y"
  and sw_diff[simp]: "\<And> x y z. x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> sw x y z = x"
  unfolding sw_def by auto

lemma sw_sym: "sw x y z = sw x z y"
  and sw_id[simp]: "sw x y y = x"
  and sw_sw: "sw (sw x y z) y1 z1 = sw (sw x y1 z1) (sw y y1 z1) (sw z y1 z1)"
  and sw_invol[simp]: "sw (sw x y z) y z = x"
  unfolding sw_def by auto

lemma sw_invol2: "sw (sw x y z) z y = x"
  by (simp add: sw_sym)

lemma sw_inj[iff]: "sw x z1 z2 = sw y z1 z2 \<longleftrightarrow> x = y"
  unfolding sw_def by auto

lemma sw_surj: "\<exists>y. x = sw y z1 z2"
  by (metis sw_invol)

fun pswap :: "ptrm \<Rightarrow> var \<Rightarrow> var \<Rightarrow> ptrm" where 
  PVr: "pswap (PVr x) z1 z2 = PVr (sw x z1 z2)"
|PAp: "pswap (PAp s t) z1 z2 = PAp (pswap s z1 z2) (pswap t z1 z2)"
|PLm: "pswap (PLm x t) z1 z2 = PLm (sw x z1 z2) (pswap t z1 z2)"

lemma pswap_sym: "pswap s y z = pswap s z y"
  by (induct s) (auto simp: sw_sym)

lemma pswap_id[simp]: "pswap s y y = s"
  by (induct s) auto

lemma pswap_pswap: 
  "pswap (pswap s y z) y1 z1 = pswap (pswap s y1 z1) (sw y y1 z1) (sw z y1 z1)"
  using sw_sw by (induct s) auto 

lemma pswap_invol[simp]: "pswap (pswap s y z) y z = s"
  by (induct s) auto

lemma pswap_invol2: "pswap (pswap s y z) z y = s"
  by (simp add: pswap_sym)

lemma pswap_inj[iff]: "pswap s z1 z2 = pswap t z1 z2 \<longleftrightarrow> s = t"
  by (metis pswap_invol)

lemma pswap_surj: "\<exists>t. s = pswap t z1 z2"
  by (metis pswap_invol)

lemma pswap_pfresh_iff[simp]: 
  "pfresh (sw x z1 z2) (pswap s z1 z2) \<longleftrightarrow> pfresh x s"
  by (induct s) auto

lemma pfresh_pswap_iff: 
  "pfresh x (pswap s z1 z2) = pfresh (sw x z1 z2) s"
  by (metis sw_invol pswap_pfresh_iff)

inductive alpha :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" where 
  PVr[intro]: "alpha (PVr x) (PVr x)"
|PAp[intro]: "alpha s s' \<Longrightarrow> alpha t t' \<Longrightarrow> alpha (PAp s t) (PAp s' t')"
|PLm[intro]: 
  "(z = x \<or> pfresh z t) \<Longrightarrow> (z = x' \<or> pfresh z t') 
 \<Longrightarrow> alpha (pswap t z x) (pswap t' z x') \<Longrightarrow> alpha (PLm x t) (PLm x' t')"

lemma alpha_PVr_eq[simp]: "alpha (PVr x) t \<longleftrightarrow> t = PVr x"
  by (auto elim: alpha.cases)

lemma alpha_eq_PVr[simp]: "alpha t (PVr x) \<longleftrightarrow> t = PVr x"
  by (auto elim: alpha.cases)

lemma alpha_PAp_cases[elim, case_names PApc]: 
  assumes "alpha (PAp s1 s2) t"
  obtains t1 t2 where "t = PAp t1 t2" and "alpha s1 t1" and "alpha s2 t2"
  using assms by (auto elim: alpha.cases)

lemma alpha_PAp_cases2[elim, case_names PApc]: 
  assumes "alpha t (PAp s1 s2)"  
  obtains t1 t2 where "t = PAp t1 t2" and "alpha t1 s1" and "alpha t2 s2"
  using assms by (auto elim: alpha.cases)

lemma alpha_PLm_cases[elim, case_names PLmc]: 
  assumes "alpha (PLm x s) t'"
  obtains x' s' z where "t' = PLm x' s'" 
    and "z = x \<or> pfresh z s" and "z = x' \<or> pfresh z s'" 
    and "alpha (pswap s z x) (pswap s' z x')"
  using assms by cases auto

lemma alpha_pswap: 
  assumes "alpha s s'" shows "alpha (pswap s z1 z2) (pswap s' z1 z2)"
  using assms proof induct
  case (PLm z x t x' t')
  thus ?case  
    by (auto intro!: alpha.PLm[of "sw z z1 z2"] 
        simp: pswap_pswap[of t' x x'] pswap_pswap[of t x' x] 
        pswap_pswap[of t z x] pswap_pswap[of t' z x']) 
qed auto 

lemma alpha_refl[simp,intro!]: "alpha s s"
  by (induct s) auto

lemma alpha_sym: 
  assumes "alpha s t" shows "alpha t s" 
  using assms by induct auto

lemma alpha_pfresh_imp: 
  assumes "alpha s t" and "pfresh x s" shows "pfresh x t"
  using assms apply induct  
  by simp_all (metis pfresh_pswap_iff sw_diff sw_eqR)

lemma alpha_pfresh_iff: 
  assumes "alpha s t"  
  shows "pfresh x s \<longleftrightarrow> pfresh x t"
  using alpha_pfresh_imp alpha_sym assms by blast

lemma pswap_pfresh_alpha: 
  assumes "pfresh z1 t" and "pfresh z2 t"
  shows "alpha (pswap t z1 z2) t"
  using assms proof(induct t)
  case (PLm z x t)
  thus ?case using alpha.PLm sw_def pswap_sym by fastforce
qed auto

(* The depth of a pre-term: *)

fun depth :: "ptrm \<Rightarrow> nat" where 
  "depth (PVr x) = 0" 
|"depth (PAp t1 t2) = depth t1 + depth t2 + 1" 
|"depth (PLm x t) = depth t + 1" 

lemma pswap_same_depth: 
  "depth (pswap t1 x y) = depth t1"
  by(induct t1, simp_all)

lemma alpha_same_depth: 
  assumes "alpha t1 t2" shows "depth t1 = depth t2"
  using assms pswap_same_depth by induct auto

lemma alpha_trans:
  assumes "alpha s t" and "alpha t u" 
  shows "alpha s u"
  using assms proof(induct s arbitrary: t u rule: measure_induct_rule[of depth])
  case (less s) 
  show ?case
  proof(cases s)
    case (PVr x1)
    then show ?thesis using less.prems by fastforce
  next
    case (PAp s1 s2)
    then obtain t1 t2 where "alpha s1 t1" "alpha s2 t2" "t = PAp t1 t2"
      using less.prems by blast
    moreover then obtain u1 u2 where "alpha t1 u1" "alpha t2 u2" "u = PAp u1 u2"
      using less.prems by blast
    ultimately show ?thesis 
    	by (smt (verit, ccfv_threshold) add.right_neutral add_less_le_mono alpha.PAp depth.simps(2) 
    	    dual_order.strict_trans2 le_add_same_cancel2 less.hyps less_add_same_cancel1 
    	    PAp neq0_conv zero_le zero_less_one)
  next
    case (PLm x s')
    obtain t' z y where t: "t = PLm y t'" "z = x \<or> pfresh z s'" 
      "z = y \<or> pfresh z t'" "alpha (pswap s' z x) (pswap t' z y)"
      using PLm less.prems by blast
    obtain u' zz w where u: "u = PLm w u'" "zz = y \<or> pfresh zz t'" 
      "zz = w \<or> pfresh zz u'" "alpha (pswap t' zz y) (pswap u' zz w)"
      using less.prems t by blast
    obtain zf where zf: "zf \<noteq> x" "zf \<noteq> y" "zf \<noteq> z" "zf \<noteq> w" "zf \<noteq> zz"
      "pfresh zf s'" "pfresh zf t'" "pfresh zf u'" 
      using exists_pfresh[of "[x,y,z,w,zz]" "[s',t',u']"] by auto

    {have "alpha (pswap s' zf x) (pswap (pswap s' z x) z zf)"
        by (smt (verit, del_insts) alpha_pswap alpha_sym pswap_pfresh_alpha 
            pswap_pswap pswap_sym sw_diff sw_eqL t(2) zf(1) zf(6))
      moreover have "alpha (pswap (pswap t' z y) z zf) (pswap t' zf y)"
        by (smt (verit, ccfv_threshold) pswap_pswap alpha_pswap 
            sw_diff sw_eqL pswap_pfresh_alpha pswap_sym t(3) zf(2) zf(7)) 
      ultimately have "alpha (pswap s' zf x) (pswap t' zf y)"
        by (metis alpha_pswap depth.simps(3) less.hyps less_add_same_cancel1 
            less_numeral_extra(1) local.PLm pswap_same_depth t(4))
    }
    moreover
    {have "alpha (pswap t' zf y) (pswap (pswap t' zz y) zz zf)"
        by (smt (z3) pswap_pswap alpha_pswap alpha_sym sw_diff sw_eqL pswap_pfresh_alpha pswap_sym 
            u(2) zf(2) zf(7))
      moreover have "alpha (pswap (pswap u' zz w) zz zf) (pswap u' zf w)"
        by (smt (verit, ccfv_threshold) pswap_pswap alpha_pswap sw_diff sw_eqL 
            pswap_pfresh_alpha pswap_sym u(3) zf(4) zf(8))
      ultimately have "alpha (pswap t' zf y) (pswap u' zf w)"
        by (smt (verit, best) alpha_same_depth alpha_pswap depth.simps(3) less.hyps
            less.prems less_add_same_cancel1 pswap_same_depth u(1) u(4) zero_less_one)
    }
    ultimately show ?thesis 
    	by (metis alpha.PLm depth.simps(3) less.hyps less_add_same_cancel1 
    	    local.PLm pswap_same_depth u(1) zero_less_one zf(6) zf(8))
  qed
qed

lemma alpha_PLm_strong_elim: 
  assumes "alpha (PLm x t) (PLm x' t')"
    and "z = x \<or> pfresh z t" and "z = x' \<or> pfresh z t'"
  shows "alpha (pswap t z x) (pswap t' z x')"
proof-
  obtain zz where zz: "zz = x \<or> pfresh zz t" "zz = x' \<or> pfresh zz t'"
    "alpha (pswap t zz x) (pswap t' zz x')"
    using alpha_PLm_cases[OF assms(1)] by (smt ptrm.inject(3))
  have sw1: "alpha (pswap t z x) (pswap (pswap t zz x) zz z)"
    unfolding pswap_pswap[of t zz x] 
    by (metis alpha_refl alpha_pswap assms(2) 
        sw_diff sw_eqL sw_eqR pswap_pfresh_alpha pswap_id pswap_invol pswap_sym zz(1))
  have sw2: "alpha (pswap (pswap t' zz x') zz z) (pswap t' z x')"
    unfolding pswap_pswap[of t' zz x'] 
    by (metis alpha_refl alpha_pswap assms(3) sw_diff sw_eqL sw_eqR 
        pswap_pfresh_alpha pswap_id pswap_invol pswap_sym zz(2))
  show ?thesis
    by (meson alpha_pswap alpha_trans sw1 sw2 zz(3))
qed

lemma pfresh_pswap_alpha: 
  assumes "y = x \<or> pfresh y t" and "z = x \<or> pfresh z t"
  shows "alpha (pswap (pswap t y x) z y) (pswap t z x)"
  by (smt assms pswap_pswap alpha_refl alpha_pswap sw_diff sw_eqR pswap_pfresh_alpha pswap_id pswap_invol2)

lemma pfresh_sw_pswap_pswap: 
  assumes "sw y' z1 z2 \<noteq> y" and "y = sw x z1 z2 \<or> pfresh y (pswap t z1 z2)"
    and "y' = x \<or> pfresh y' t"  
  shows "pfresh (sw y' z1 z2) (pswap (pswap t z1 z2) y (sw x z1 z2))"
  using assms pfresh_pswap_iff sw_diff sw_eqR sw_invol by smt



subsection \<open> Terms via quotienting pre-terms \<close>

quotient_type trm = ptrm / alpha
  unfolding equivp_def fun_eq_iff using alpha_sym alpha_trans alpha_refl by blast

(* Lifted concepts, from terms to tterms: *)
lift_definition Vr :: "var \<Rightarrow> trm" is PVr .
lift_definition Ap :: "trm \<Rightarrow> trm \<Rightarrow> trm" is PAp by auto
lift_definition Lm :: "var \<Rightarrow> trm \<Rightarrow> trm" is PLm by auto
lift_definition swap :: "trm \<Rightarrow> var \<Rightarrow> var \<Rightarrow> trm" is pswap 
  using alpha_pswap by auto
lift_definition fresh :: "var \<Rightarrow> trm \<Rightarrow> bool" is pfresh
  using alpha_pfresh_iff by blast
lift_definition ddepth :: "trm \<Rightarrow> nat" is depth
  using alpha_same_depth by blast

lemma abs_trm_rep_trm[simp]: "abs_trm (rep_trm t) = t"  
  by (meson Quotient3_abs_rep Quotient3_trm)

lemma alpha_rep_trm_abs_trm[simp,intro!]: "alpha (rep_trm (abs_trm t)) t" 
  by (simp add: Quotient3_trm rep_abs_rsp_left)

lemma pfresh_rep_trm_abs_trm[simp]: "pfresh z (rep_trm (abs_trm t)) \<longleftrightarrow> pfresh z t"
  using fresh.abs_eq fresh.rep_eq by auto

lemma swap_id[simp]:
  "swap (swap t z x) z x = t"
  by transfer simp

lemma fresh_PVr[simp]: "fresh x (Vr y) \<longleftrightarrow> x \<noteq> y" 
	by (simp add: Vr_def fresh.abs_eq)

lemma fresh_Ap[simp]: "fresh z (Ap t1 t2) \<longleftrightarrow> fresh z t1 \<and> fresh z t2"
  by transfer auto

lemma fresh_Lm[simp]: "fresh z (Lm x t) \<longleftrightarrow> (z = x \<or> fresh z t)"
  by transfer auto

lemma Lm_swap_rename: 
  assumes "z = x \<or> fresh z t "
  shows "Lm z (swap t z x) = Lm x t" 
  using assms apply transfer 
  using alpha.PLm by auto 

lemma abs_trm_PVr: "abs_trm (PVr x) = Vr x"
  by (simp add: Vr.abs_eq)

lemma abs_trm_PAp: "abs_trm (PAp t1 t2) = Ap (abs_trm t1) (abs_trm t2)"
  by (simp add: Ap.abs_eq)

lemma abs_trm_PLm: "abs_trm (PLm x t) = Lm x (abs_trm t)"
  by (simp add: Lm.abs_eq)

lemma abs_trm_pswap: "abs_trm (pswap t z1 z2) = swap (abs_trm t) z1 z2"
  by (simp add: swap.abs_eq)

lemma swap_Vr[simp]: "swap (Vr x) z1 z2 = Vr (sw x z1 z2)"
  by transfer simp 

lemma swap_Ap[simp]: "swap (Ap t1 t2) z1 z2 = Ap (swap t1 z1 z2) (swap t2 z1 z2)"
  by transfer simp

lemma swap_Lm[simp]: "swap (Lm x t) z1 z2 = Lm (sw x z1 z2) (swap t z1 z2)"
  by transfer simp 

lemma Lm_sameVar_inj[simp]: "Lm x t = Lm x t1 \<longleftrightarrow> t = t1" 
  by transfer (metis alpha.PLm alpha_PLm_strong_elim pswap_id)

lemma Lm_eq_swap: 
  assumes "Lm x t = Lm x1 t1"
  shows "t = swap t1 x x1" 
proof(cases "x = x1")
  case True
  thus ?thesis using assms Lm_swap_rename by fastforce
next
  case False
  thus ?thesis  
  	by (metis Lm_sameVar_inj Lm_swap_rename assms fresh_Lm)
qed

lemma alpha_rep_abs_trm: "alpha (rep_trm (abs_trm t)) t" 
  by simp

lemma swap_fresh_eq: assumes x:"fresh x t" and y:"fresh y t"
  shows "swap t x y = t"
  using pswap_pfresh_alpha x y unfolding fresh.rep_eq
  by (metis (full_types) Quotient3_abs_rep Quotient3_trm swap.abs_eq trm.abs_eq_iff)

lemma bij_sw:"bij (\<lambda> x. sw x z1 z2)"
  unfolding sw_def bij_def inj_def surj_def by smt

lemma sw_set: "x \<in> X = ((sw x z1 z2) \<in> (\<lambda> x. sw x z1 z2) ` X)"
  using bij_sw by blast

lemma ddepth_Vr[simp]: "ddepth (Vr x) = 0"
  by transfer simp

lemma ddepth_Ap[simp]: "ddepth (Ap t1 t2) = Suc (ddepth t1 + ddepth t2)"
  by transfer simp

lemma ddepth_Lm[simp]: "ddepth (Lm x t) = Suc (ddepth t)"
  by transfer simp

lemma trm_nchotomy: 
  "(\<exists>x. tt = Vr x) \<or> (\<exists>t1 t2. tt = Ap t1 t2) \<or> (\<exists>x t. tt = Lm x t)"
  apply transfer using ptrm.nchotomy by (metis alpha_refl ptrm.exhaust) 

lemma trm_exhaust[case_names Vr Ap Lm, cases type: trm]:
  "(\<And>x. tt = Vr x \<Longrightarrow> P) \<Longrightarrow>
(\<And>t1 t2. tt = Ap t1 t2 \<Longrightarrow> P) \<Longrightarrow> (\<And>x t. tt = Lm x t \<Longrightarrow> P) \<Longrightarrow> P"
  using trm_nchotomy by blast

lemma Vr_Ap_diff[simp]: "Vr x \<noteq> Ap t1 t2"  "Ap t1 t2 \<noteq> Vr x" 
	by (metis Zero_not_Suc ddepth_Ap ddepth_Vr)+

lemma Vr_Lm_diff[simp]: "Vr x \<noteq> Lm y t"  "Lm y t \<noteq> Vr x" 
	by (metis Zero_not_Suc ddepth_Lm ddepth_Vr)+

lemma Ap_Lm_diff[simp]: "Ap t1 t2 \<noteq> Lm y t"  "Lm y t \<noteq> Ap t1 t2" 
	by (transfer,blast)+

lemma Vr_inj[simp]: "(Vr x = Vr y) \<longleftrightarrow> x = y"  
  by transfer auto

lemma Ap_inj[simp]: "(Ap t1 t2 = Ap t1' t2') \<longleftrightarrow> t1 = t1' \<and> t2 = t2'"  
  by transfer auto

(* free variables as an abbreviation *)

abbreviation Fvars :: "ptrm \<Rightarrow> var set" where 
  "Fvars t \<equiv> {x. \<not> pfresh x t}"
abbreviation FFvars :: "trm \<Rightarrow> var set" where 
  "FFvars t \<equiv> {x. \<not> fresh x t}"

lemma cofinite_fresh: "finite (FFvars t)"
  unfolding fresh.rep_eq using cofinite_pfresh by simp   

lemma exists_fresh_set:
  assumes "finite X"
  shows "\<exists> z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>t \<in> set ts. fresh z t)"
  using assms apply transfer 
	using exists_pfresh_set by presburger

definition ppickFreshS :: "var set \<Rightarrow> var list \<Rightarrow> trm list \<Rightarrow> var" where 
  "ppickFreshS X xs ts \<equiv> SOME z. z \<notin> X \<and> z \<notin> set xs \<and> 
                 (\<forall>t \<in> set ts. fresh z t)" 

lemma ppickFreshS: 
  assumes "finite X"
  shows 
    "ppickFreshS X xs ts \<notin> X \<and> 
 ppickFreshS X xs ts \<notin> set xs \<and> 
 (\<forall>t \<in> set ts. fresh (ppickFreshS X xs ts) t)"
  using exists_fresh_set[OF assms] unfolding ppickFreshS_def 
  by (rule someI_ex)

lemmas ppickFreshS_set = ppickFreshS[THEN conjunct1]
  and ppickFreshS_var = ppickFreshS[THEN conjunct2, THEN conjunct1]
  and ppickFreshS_ptrm = ppickFreshS[THEN conjunct2, THEN conjunct2, unfolded Ball_def, rule_format]

(* Unconditional form of pick-pfresh, without any set: *)
definition "ppickFresh \<equiv> ppickFreshS {}"

lemmas ppickFresh_var = ppickFreshS_var[OF finite.emptyI, unfolded ppickFresh_def[symmetric]]
  and ppickFresh_ptrm = ppickFreshS_ptrm[OF finite.emptyI, unfolded ppickFresh_def[symmetric]]

lemma fresh_swap_nominal_style: 
  "fresh x t \<longleftrightarrow> finite {y. swap t y x \<noteq> t}"
proof
  assume "fresh x t"
  hence "{y. swap t y x \<noteq> t} \<subseteq> {y. \<not> fresh y t}"
  	by (auto, meson swap_fresh_eq)
  thus "finite {y. swap t y x \<noteq> t}" 
  	using cofinite_fresh rev_finite_subset by blast
next
  assume "finite {y. swap t y x \<noteq> t}"
  moreover have "finite {y. \<not> fresh y t}" using cofinite_fresh .
  ultimately have "finite {y. \<not> fresh y t \<or> swap t y x \<noteq> t \<or> y = x}" 
    by (metis (full_types) finite_Collect_disjI finite_insert insert_compr)
  then obtain y where "fresh y t" and "y \<noteq> x" and "swap t y x = t" 
    using exists_var by auto
  thus "fresh x t" by (metis Lm_swap_rename fresh_Lm)
qed


subsection \<open>Fresh induction\<close>

lemma swap_induct[case_names Vr Ap Lm]: 
  assumes Vr: "\<And>x. \<phi> (Vr x)" 
    and Ap: "\<And>t1 t2. \<phi> t1 \<Longrightarrow> \<phi> t2 \<Longrightarrow> \<phi> (Ap t1 t2)"
    and Lm: "\<And>x t. (\<forall>z. \<phi> (swap t z x)) \<Longrightarrow> \<phi> (Lm x t)"
  shows "\<phi> t"
proof(induct rule: measure_induct[of ddepth])
  case (1 tt)
  show ?case using trm_nchotomy[of tt] apply safe
    subgoal using Vr 1 by auto
    subgoal using Ap 1 by auto
    subgoal by (metis 1 Lm Lm_swap_rename ddepth_Lm fresh_Lm lessI 
          old.nat.inject swap_Lm) .
qed

lemma fresh_induct[consumes 1, case_names Vr Ap Lm]: 
  assumes "finite X" and "\<And>x. \<phi> (Vr x)" 
    and "\<And>t1 t2. \<phi> t1 \<Longrightarrow> \<phi> t2 \<Longrightarrow> \<phi> (Ap t1 t2)"
    and "\<And>x t. \<phi> t \<Longrightarrow> x \<notin> X \<Longrightarrow> \<phi> (Lm x t)"
  shows "\<phi> t"
  apply(induct rule: swap_induct)
  using assms 
  by auto (metis Collect_mem_eq Collect_mono Lm_swap_rename cofinite_fresh 
      finite_Collect_not infinite_var rev_finite_subset)

lemma plain_induct[case_names Vr Ap Lm]: 
  assumes "\<And>x. \<phi> (Vr x)" 
    and "\<And>t1 t2. \<phi> t1 \<Longrightarrow> \<phi> t2 \<Longrightarrow> \<phi> (Ap t1 t2)"
    and "\<And>x t. \<phi> t \<Longrightarrow> \<phi> (Lm x t)"
  shows "\<phi> t"
	by (metis assms fresh_induct finite.emptyI)


subsection \<open>Substitution\<close>

inductive substRel :: "trm \<Rightarrow> trm \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> bool" where 
  substRel_Vr_same: 
  "substRel (Vr x) s x s"
|substRel_Vr_diff: 
  "x \<noteq> y \<Longrightarrow> substRel (Vr x) s y (Vr x)"
|substRel_Ap: 
  "substRel t1 s y t1' \<Longrightarrow> substRel t2 s y t2' \<Longrightarrow>
 substRel (Ap t1 t2) s y (Ap t1' t2')"
|substRel_Lm: 
  "x \<noteq> y \<Longrightarrow> fresh x s \<Longrightarrow> substRel t s y t' \<Longrightarrow> 
 substRel (Lm x t) s y (Lm x t')"

lemma substRel_Vr_invert: 
  assumes "substRel (Vr x) t y t'" 
  shows "(x = y \<and> t = t') \<or> (x \<noteq> y \<and> t' = Vr x)"
  using assms by (cases rule: substRel.cases) auto

lemma substRel_Ap_invert: 
  assumes "substRel (Ap t1 t2) s y t'" 
  shows "\<exists>t1' t2'. t' = Ap t1' t2' \<and> substRel t1 s y t1' \<and> substRel t2 s y t2'"
  using assms by (cases rule: substRel.cases) auto

lemma substRel_Lm_invert_aux: 
  assumes "substRel (Lm x t) s y tt'" 
  shows "\<exists>x1 t1 t1'. 
  x1 \<noteq> y \<and> fresh x1 s \<and> 
  Lm x t = Lm x1 t1 \<and> tt' = Lm x1 t1' \<and> substRel t1 s y t1'"
  using assms by (cases rule: substRel.cases) auto

lemma substRel_swap: 
  assumes "substRel t s y tt" 
  shows "substRel (swap t z1 z2) (swap s z1 z2) (sw y z1 z2) (swap tt z1 z2)"
  using assms apply induct
  by (auto intro: substRel.intros) (simp add: fresh.rep_eq substRel_Lm swap_def)

lemma substRel_fresh: 
  assumes "substRel t s y t'" and "fresh x1 t" "x1 \<noteq> y" "fresh x1 s" 
  shows "fresh x1 t'"
  using assms by induct auto

lemma substRel_Lm_invert: 
  assumes "substRel (Lm x t) s y tt'" and 0: "x \<noteq> y" "fresh x s"
  shows "\<exists>t'. tt' = Lm x t' \<and> substRel t s y t'"
  using substRel_Lm_invert_aux[OF assms(1)] proof(elim exE conjE)
  fix x1 t1 t1'
  assume 1: "x1 \<noteq> y" "fresh x1 s" "Lm x t = Lm x1 t1"
    "substRel t1 s y t1'" "tt' = Lm x1 t1'"
  have 2: "t = swap t1 x x1" by (simp add: "1"(3) Lm_eq_swap) 
  hence 3: "x = x1 \<or> fresh x t1"  
  	by (metis "1"(3) fresh_Lm) 
  have 4: "s = swap s x x1" "y = sw y x x1"
    apply (simp add: "1"(2) assms(3) swap_fresh_eq) 
    using "1"(1) assms(2) sw_def by presburger
  show ?thesis
    apply(rule exI[of _ "swap t1' x x1"], safe) 
    subgoal unfolding 1 apply(rule sym, rule Lm_swap_rename)
      using 3 substRel_fresh[OF 1(4) _ 0] by auto
    subgoal unfolding 2 apply(subst 4(1), subst 4(2)) 
      using substRel_swap[OF 1(4)] . . 
qed

lemma substRel_total: 
  "\<exists>t'. substRel t s y t'"
proof-
  have "finite ({y} \<union> FFvars s)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis apply(induct t rule: fresh_induct) 
    subgoal by (metis substRel_Vr_diff substRel_Vr_same)
    subgoal by(auto intro: substRel_Ap)
    by(auto intro: substRel_Lm)
qed

lemma substRel_functional: 
  assumes "substRel t s y t'" and "substRel t s y tt'"
  shows "t' = tt'"
proof-
  have "finite ({y} \<union> FFvars s)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis 
    using assms apply(induct t arbitrary: t' tt' rule: fresh_induct)
    subgoal using substRel_Vr_invert by blast
    subgoal  by (metis substRel_Ap_invert)
    subgoal by (metis CollectI UnI1 UnI2 singleton_iff substRel_Lm_invert) .
qed


definition subst :: "trm \<Rightarrow> trm \<Rightarrow> var \<Rightarrow> trm" where 
  "subst t s x \<equiv> SOME tt. substRel t s x tt"

lemma substRel_subst: "substRel t s x (subst t s x)"
  by (simp add: someI_ex substRel_total subst_def)

lemma substRel_subst_unique: "substRel t s x tt \<Longrightarrow> tt = subst t s x"
  by (simp add: substRel_functional substRel_subst)

lemma 
  subst_Vr[simp]: "subst (Vr x) t z = (if x = z then t else Vr x)"
  and 
  subst_Ap[simp]: "subst (Ap s1 s2) t z = Ap (subst s1 t z) (subst s2 t z)"
  and
  subst_Lm[simp]: 
  "x \<noteq> z \<Longrightarrow> fresh x t \<Longrightarrow> subst (Lm x s) t z = Lm x (subst s t z)" 
  subgoal by (metis substRel_Vr_invert substRel_subst)
  subgoal by (metis substRel_Ap substRel_subst substRel_subst_unique)
  subgoal by (meson substRel_Lm substRel_functional substRel_subst) . 

lemma fresh_subst:
  "fresh z (subst s t x) \<longleftrightarrow> (z = x \<or> fresh z s) \<and> (fresh x s \<or> fresh z t)"
proof-
  have "finite ({x,z} \<union> FFvars t)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis apply(induct s rule: fresh_induct) by auto
qed

lemma fresh_subst_id[simp]: 
  assumes "fresh x s" shows "subst s t x = s"
proof-
  have "finite (FFvars t \<union> {x})"   
  	by (simp add: cofinite_fresh)
  thus ?thesis using assms apply(induct s rule: fresh_induct) by auto
qed

lemma subst_Vr_id[simp]: "subst s (Vr x) x = s"
proof-
  have "finite {x}" by auto
  thus ?thesis by (induct s rule: fresh_induct) auto
qed

lemma Lm_swap_cong:
  assumes "z = x \<or> fresh z s" "z = y \<or> fresh z t" and "swap s z x = swap t z y"
  shows "Lm x s = Lm y t"
  using assms by (metis Lm_swap_rename)

lemma fresh_swap[simp]: "fresh x (swap t z1 z2) \<longleftrightarrow> fresh (sw x z1 z2) t"
  apply(induct t rule: plain_induct) by auto

lemma swap_subst: 
  "swap (subst s t x) z1 z2 = subst (swap s z1 z2) (swap t z1 z2) (sw x z1 z2)"
proof-
  have "finite (FFvars t \<union> {x,z1,z2})"   
  	by (simp add: cofinite_fresh)
  thus ?thesis apply(induct s rule: fresh_induct)  
  	using fresh_swap subst_Lm sw_def by auto
qed

lemma subst_Lm_same[simp]: "subst (Lm x s) t x = Lm x s"
  by simp

lemma fresh_subst_same: 
  assumes "y \<noteq> z" shows "fresh y (subst t (Vr z) y)"
proof-
  have "finite ({y,z})"   
  	by (simp add: cofinite_fresh)
  thus ?thesis using assms apply(induct t rule: fresh_induct) by auto
qed

lemma subst_comp_same: 
  "subst (subst s t x) t1 x = subst s (subst t t1 x) x"
proof-
  have "finite ({x} \<union> FFvars t \<union> FFvars t1)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis apply(induct s rule: fresh_induct)  
  	using fresh_subst subst_Lm by auto
qed


lemma subst_comp_diff: 
  assumes "x \<noteq> x1" "fresh x t1"
  shows "subst (subst s t x) t1 x1 = subst (subst s t1 x1) (subst t t1 x1) x"
proof-
  have "finite ({x,x1} \<union> FFvars t \<union> FFvars t1)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis using assms apply(induct s rule: fresh_induct)   
  	using fresh_subst subst_Lm by auto
qed

lemma subst_comp_diff_var: 
  assumes "x \<noteq> x1" "x \<noteq> z1"
  shows "subst (subst s t x) (Vr z1) x1 = 
       subst (subst s (Vr z1) x1) (subst t (Vr z1) x1) x"
  apply(rule subst_comp_diff)
  using assms by auto

lemma subst_chain: 
  assumes "fresh u s" 
  shows "subst (subst s (Vr u) x) t u = subst s t x"
proof-
  have "finite ({x,u} \<union> FFvars t \<union> FFvars s)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis using assms apply(induct s rule: fresh_induct)   
    by auto
qed

lemma subst_repeated_Vr: 
  "subst (subst t (Vr x) y) (Vr u) x = 
 subst (subst t (Vr u) x) (Vr u) y"
proof-
  have "finite ({x,y,u} \<union> FFvars t)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis apply(induct t rule: fresh_induct)   
  	using fresh_subst subst_Lm by auto
qed

lemma subst_commute_same: 
  "subst (subst d (Vr u) x) (Vr u) y = subst (subst d (Vr u) y) (Vr u) x"
  by (metis subst_Vr_id subst_repeated_Vr)

lemma subst_commute_diff: 
  assumes "x \<noteq> v" "y \<noteq> u" "x \<noteq> y"
  shows "subst (subst t (Vr u) x) (Vr v) y = subst (subst t (Vr v) y) (Vr u) x"
proof-
  have "finite ({u,v,x,y})"   
  	by (simp add: cofinite_fresh)
  thus ?thesis using assms apply(induct t rule: fresh_induct) by auto
qed

lemma subst_same_id: 
  assumes "z1 \<noteq> y"
  shows "subst (subst t (Vr z1) y) (Vr z2) y = subst t (Vr z1) y"
  using assms subst_Vr subst_comp_same by presburger

lemma swap_from_subst: 
  assumes yy: "yy\<notin>{z1,z2}" "fresh yy t"  
  shows "swap t z1 z2 = subst (subst (subst t (Vr yy) z1) (Vr z1) z2) (Vr z2) yy"
proof-
  have "finite ({z1,z2,yy} \<union> FFvars t)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis using assms apply(induct t rule: fresh_induct) by auto
qed

lemma subst_two_ways': 
  fixes t yy x
  assumes yy: "yy\<notin>{z1,z2}"  "yy'\<notin>{z1,z2}"  "x \<notin> {yy,yy'}"
  defines "tt \<equiv> subst (subst t (Vr x) yy) (Vr x) yy'"
  shows "subst (subst (subst tt (Vr yy) z1) (Vr z1) z2) (Vr z2) yy = 
       subst (subst (subst tt (Vr yy') z1) (Vr z1) z2) (Vr z2) yy'"
    (is "?L = ?R")
proof-
  have "?L = swap tt z1 z2"
    apply(rule sym, rule swap_from_subst)
    using assms fresh_PVr fresh_subst by auto
  also have "\<dots> = ?R" apply(rule swap_from_subst)
    using assms fresh_PVr fresh_subst by auto
  finally show ?thesis .
qed

lemma subst_two_ways'': 
  assumes "xx \<notin> {x, z1, z2, uu, vv} \<and> fresh xx t"
    "vv \<notin> {x, z1, z2} \<and> fresh vv t"
    "yy \<notin> {z1, z2} \<and> fresh yy t"
  shows 
    "subst (subst (subst (subst (subst t (Vr xx) x) (Vr vv) z1) (Vr z1) z2) (Vr z2) vv) (Vr vv) xx =
 subst (subst (subst (subst t (Vr yy) z1) (Vr z1) z2) (Vr z2) yy) (Vr vv) (sw x z1 z2)"
    (is "?L = ?R")
proof-
  have "?L = subst (swap (subst t (Vr xx) x) z1 z2) (Vr vv) xx"
    by (metis assms(1,2) fresh_PVr fresh_subst insertCI swap_from_subst)
  also have "\<dots> = ?R"
    using assms(1,3) subst_chain sw_diff swap_from_subst swap_subst by auto
  finally show ?thesis .
qed

(* Equational reformulation of the above, to be transported to the models: 
We take advantage of the fact that z1 is different from all the items assumed 
pfresh in the previous lemma. *)
lemma subst_two_ways''_aux: 
  fixes t z1 xx z2 vv   
  assumes "xx \<notin> {x, z1, z2, uu, vv}"
    "vv \<notin> {x, z1, z2}"
    "yy \<notin> {z1, z2}" 
  defines "tt \<equiv> subst (subst (subst t (Vr z1) xx) (Vr z1) yy) (Vr z1) vv"
  shows 
    "subst (subst (subst (subst (subst tt (Vr xx) x) (Vr vv) z1) (Vr z1) z2) (Vr z2) vv) (Vr vv) xx =
 subst (subst (subst (subst tt (Vr yy) z1) (Vr z1) z2) (Vr z2) yy) (Vr vv) (sw x z1 z2)"
  by (metis assms fresh_PVr fresh_subst insertCI subst_two_ways'')

lemma fresh_cases[cases pred: fresh, case_names Vr Ap Lm]:
  "fresh a1 a2 \<Longrightarrow>
(\<And>z x. a1 = z \<Longrightarrow> a2 = Vr x \<Longrightarrow> z \<noteq> x \<Longrightarrow> P) \<Longrightarrow>
(\<And>z t1 t2. a1 = z \<Longrightarrow> a2 = Ap t1 t2 \<Longrightarrow> fresh z t1 \<Longrightarrow> fresh z t2 \<Longrightarrow> P) \<Longrightarrow>
(\<And>z x t. a1 = z \<Longrightarrow> a2 = Lm x t \<Longrightarrow> z = x \<or> fresh z t \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis fresh_Ap fresh_Lm fresh_PVr trm_nchotomy)


(* Var-for-var psubstitution on variables: *)
definition vss :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" where 
  "vss x y z = (if x = z then y else x)"


lemma fresh_subst_eq_swap: 
  assumes "fresh z t"
  shows "subst t (Vr z) x = swap t z x" 
proof-
  have "finite ({z,x})"   
  	by simp
  thus ?thesis using assms by (induct t rule: fresh_induct) auto
qed

lemma Lm_subst_rename: 
  assumes "z = x \<or> fresh z t"
  shows "Lm z (subst t (Vr z) x) = Lm x t"
  using Lm_swap_rename assms fresh_subst_eq_swap subst_Vr_id by presburger

lemma Lm_subst_cong: 
  "z = x \<or> fresh z s \<Longrightarrow> z = y \<or> fresh z t \<Longrightarrow> 
subst s (Vr z) x = subst t (Vr z) y \<Longrightarrow> Lm x s = Lm y t"
  by (metis Lm_subst_rename)

lemma Lm_eq_elim:  
  "Lm x s = Lm y t \<Longrightarrow> z = x \<or> fresh z s \<Longrightarrow> z = y \<or> fresh z t 
 \<Longrightarrow>  swap s z x = swap t z y"
  by (simp add: Lm_eq_swap Lm_swap_rename) 

lemma Lm_eq_elim_subst:  
  "Lm x s = Lm y t \<Longrightarrow> z = x \<or> fresh z s \<Longrightarrow> z = y \<or> fresh z t 
 \<Longrightarrow> 
 subst s (Vr z) x = subst t (Vr z) y"
  by (smt (verit, ccfv_threshold) Lm_eq_elim Lm_subst_rename swap_id)


subsection \<open>Renaming (a.k.a. variable-for-variable substitution) \<close>

abbreviation vsubst where "vsubst \<equiv> \<lambda>t x y. subst t (Vr x) y" 

(* The relation of being connected by a chain of renamings *)
inductive substConnect :: "trm \<Rightarrow> trm \<Rightarrow> bool" where 
  Refl: "substConnect t t"
| Step: "substConnect t t' \<Longrightarrow> substConnect t (vsubst t' z x)"

lemma ddepth_swap: 
  "ddepth (swap t z x) = ddepth t"
  by (metis ddepth.abs_eq ddepth.rep_eq map_fun_apply swap_def pswap_same_depth)

lemma ddepth_subst_Vr[simp]: 
  "ddepth (vsubst t z x) = ddepth t"
proof-
  have "finite ({z,x})"   
  	by simp
  thus ?thesis by (induct t rule: fresh_induct) auto
qed

lemma substConnect_depth: 
  assumes "substConnect t t'" shows "ddepth t = ddepth t'"
  using assms by (induct, auto) 

lemma substConnect_induct[case_names Vr Ap Lm]: 
  assumes Vr: "\<And>x. \<phi> (Vr x)" 
    and Ap: "\<And>t1 t2. \<phi> t1 \<Longrightarrow> \<phi> t2 \<Longrightarrow> \<phi> (Ap t1 t2)"
    and Lm: "\<And>x t. (\<forall>t'. substConnect t t' \<longrightarrow> \<phi> t') \<Longrightarrow> \<phi> (Lm x t)"
  shows "\<phi> t"
proof(induct rule: measure_induct[of ddepth])
  case (1 tt)
  show ?case using trm_nchotomy[of tt]
    using "1" Ap Lm Vr substConnect_depth by auto
qed


subsection \<open>Syntactic environments\<close>

(* Environments map variables to terms *)

typedef fenv = "{f :: var \<Rightarrow> trm . finite {x. f x \<noteq> Vr x}}"
  using not_finite_existsD by auto

definition get :: "fenv \<Rightarrow> var \<Rightarrow> trm" where 
  "get f x \<equiv> Rep_fenv f x"

definition upd :: "fenv \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> fenv" where 
  "upd f x t = Abs_fenv ((Rep_fenv f)(x:=t))"

definition supp :: "fenv \<Rightarrow> var set" where 
  "supp f \<equiv> {x. get f x \<noteq> Vr x}"

lemma finite_supp: "finite (supp f)" 
  using Rep_fenv get_def supp_def by auto

lemma finite_upd: 
  assumes "finite {x. f x \<noteq> Vr x}"
  shows "finite {x. (f(y:=t)) x \<noteq> Vr x}"
proof-
  have "{x. (f(y:=t)) x \<noteq> Vr x} \<subseteq> {x. f x \<noteq> Vr x} \<union> {y}"
    by auto
  thus ?thesis 
    by (metis (full_types) assms finite_insert insert_is_Un rev_finite_subset sup.commute)
qed

lemma get_upd_same[simp]: "get (upd f x t) x = t"
  and get_upd_diff[simp]: "x \<noteq> y \<Longrightarrow> get (upd f x t) y = get f y"
  and upd_upd_same[simp]: "upd (upd f x t) x s = upd f x s"
  and upd_upd_diff: "x \<noteq> y \<Longrightarrow> upd (upd f x t) y s = upd (upd f y s) x t"
  and supp_get[simp]: "x \<notin> supp \<rho> \<Longrightarrow> get \<rho> x = Vr x"
  unfolding get_def upd_def using Rep_fenv finite_upd 
  by (auto simp: fun_upd_twist Abs_fenv_inverse get_def supp_def)  



end