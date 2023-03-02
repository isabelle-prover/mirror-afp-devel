section \<open>Renset-based Recursion\<close>

theory FRBCE_Rensets
  imports Rensets 
begin

text \<open>In this theory we prove that lambda-terms (modulo alpha) form 
the initial renset. This gives rise to a recursion principle, which we 
further enhance with support for the Barendregt variable convention 
(similarly to the nominal recursion). \<close>

section \<open>Full-fledged, Barendregt-constrctor-enriched recursion\<close>

(* "FR BCE" stands for "Full-fledged recursion, Barendregt-constructor-enriched" *)

locale FR_BCE_Renset = Renset vsubstA
  for vsubstA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A"
    +
  fixes 
    X :: "var set"
    (* Constructor-like operators: *)
    and VrA :: "var \<Rightarrow> 'A"
    and ApA :: "trm \<Rightarrow> 'A \<Rightarrow> trm \<Rightarrow> 'A \<Rightarrow> 'A"
    and LmA :: "var \<Rightarrow> trm \<Rightarrow> 'A \<Rightarrow> 'A"
  assumes 
    finite_X[simp,intro!]: "finite X"
    and 
    vsubstA_VrA: "\<And> x y z. {y,z} \<inter> X = {} \<Longrightarrow>
  vsubstA (VrA x) y z = (if x = z then VrA y else VrA x)"
    and 
    vsubstA_ApA: "\<And> y z t1 a1 t2 a2. {y,z} \<inter> X = {} \<Longrightarrow>
  vsubstA (ApA t1 a1 t2 a2) y z =  
  ApA (vsubst t1 y z) (vsubstA a1 y z) 
      (vsubst t2 y z) (vsubstA a2 y z)"
    and 
    vsubstA_LmA: "\<And> t a z x y. {x,y,z} \<inter> X = {} \<Longrightarrow>
  x \<noteq> y \<Longrightarrow> 
  vsubstA (LmA x t a) y z = 
  (if x = z then LmA x t a else LmA x (vsubst t y z) (vsubstA a y z))"
    and 
    LmA_rename: "\<And> x y z t a. {x,y,z} \<inter> X = {} \<Longrightarrow>
  z \<noteq> y \<Longrightarrow> 
 LmA x (vsubst t z y) (vsubstA a z y) = 
 LmA y (vsubst (vsubst t z y) y x) (vsubstA (vsubstA a z y) y x)"
begin 

lemma LmA_cong: 
  "{u,z,x,x'} \<inter> X = {} \<Longrightarrow> 
 z \<noteq> u \<Longrightarrow> 
 z \<noteq> x \<Longrightarrow> z \<noteq> x' \<Longrightarrow> 
 vsubst (vsubst t u z) z x = vsubst (vsubst t' u z) z x' \<Longrightarrow> 
 vsubstA (vsubstA a u z) z x = vsubstA (vsubstA a' u z) z x'
 \<Longrightarrow> LmA x (vsubst t u z) (vsubstA a u z) = 
     LmA x' (vsubst t' u z) (vsubstA a' u z)"
	using LmA_rename using Int_commute disjoint_insert(2) by metis

lemma vsubstA_LmA_same: 
  "{x,y} \<inter> X = {} \<Longrightarrow> vsubstA (LmA x t a) y x = LmA x t a" 
  by (metis insert_disjoint(1) vsubstA_LmA vsubstA_id)

lemma vsubstA_LmA_diff: 
  "{x,y,z} \<inter> X = {} \<Longrightarrow>  
 x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> vsubstA (LmA x t a) y z = LmA x (vsubst t y z) (vsubstA a y z)"
  using vsubstA_LmA by meson

lemma freshA_2_vsubstA: 
  assumes "freshA z a" "freshA z a'" 
  shows "\<exists>u. u \<notin> X \<and> u \<noteq> z \<and> vsubstA a u z = a \<and> vsubstA a' u z = a'"
  using assms unfolding freshA_def 
	by (metis assms exists_var finite.insertI finite_X insertCI freshA_vsubstA_idle)

lemma LmA_cong_freshA:  
  assumes "{z,x,x'} \<inter> X = {}"
    and "z \<noteq> x" "fresh z t" "freshA z a"
    and "z \<noteq> x'" "fresh z t'" "freshA z a'" 
    and "vsubst t z x = vsubst t' z x'"
    and "vsubstA a z x = vsubstA a' z x'"
  shows "LmA x t a = LmA x' t' a'"
proof-
  obtain u where 1: "u \<notin> X \<union> {z}"  
  	by (metis Un_insert_right boolean_algebra_cancel.sup0 exists_var finite_X finite_insert)
  hence 0: "t = vsubst t u z"  "a = vsubstA a u z" 
    "t' = vsubst t' u z"  "a' = vsubstA a' u z"
  	using assms freshA_iff_all_vvsubstA_idle by auto
  show ?thesis apply(subst 0(1), subst 0(2), subst 0(3), subst 0(4))
    apply(rule LmA_cong) using assms 1 0 by auto
qed

lemma freshA_VrA: "z \<notin> X \<Longrightarrow> z \<noteq> x \<Longrightarrow> freshA z (VrA x)"
  using freshA_def vsubstA_VrA 
	by (metis Int_commute Int_insert_right_if0 
	    freshA_iff_ex_vvsubstA_idle exists_fresh_set finite_X inf_bot_right insertI1 list.set(2))

lemma freshA_ApA: "z \<notin> X \<Longrightarrow> 
  fresh z t1 \<Longrightarrow> freshA z a1 \<Longrightarrow> 
  fresh z t2 \<Longrightarrow> freshA z a2 \<Longrightarrow> 
  freshA z (ApA t1 a1 t2 a2)"
  using freshA_2_vsubstA[of z a1 a2] freshA_vsubstA2 vsubstA_ApA
  by (metis Diff_disjoint Diff_insert_absorb Int_insert_left_if0 fresh_subst_id)

lemma freshA_LmA_same: 
  assumes "x \<notin> X"
  shows "freshA x (LmA x t a)"
proof-
  have "{y. vsubstA (LmA x t a) y x \<noteq> LmA x t a} \<subseteq> X"  
  	using assms vsubstA_LmA_same[of x _ t a] by blast 
  thus ?thesis unfolding freshA_def finite_X 
  	by (meson finite_X rev_finite_subset)
qed

lemma freshA_LmA': 
  assumes "{x,z} \<inter> X = {}" "fresh z t"  "freshA z a"  
  shows "freshA z (LmA x t a)"
proof(cases "x = z")
  case True 
  thus ?thesis 
    using assms(1) freshA_LmA_same by auto 
next
  case False
  hence "{y. vsubstA (LmA x t a) y z \<noteq> LmA x t a} \<subseteq> 
    {y. vsubst t y z \<noteq> t} \<union> {y. vsubstA a y z \<noteq> a} \<union> {x} \<union> X" 
    using assms(1) vsubstA_LmA by force  
  hence "finite {y. vsubstA (LmA x t a) y z \<noteq> LmA x t a}" 
    by (smt (verit, best) Collect_empty_eq assms(2) assms(3) 
        fresh_subst_id finite.simps finite_UnI finite_X freshA_2_vsubstA rev_finite_subset vsubstA_idem)
  thus ?thesis unfolding freshA_def by auto
qed

lemma LmA_rename_freshA:
  assumes "{x,z} \<inter> X = {}" "z \<noteq> x" "fresh z t"  "freshA z a" 
  shows "LmA x t a = LmA z (vsubst t z x) (vsubstA a z x)"
  using assms 
  by simp (smt (verit, ccfv_SIG) Int_insert_left LmA_rename assms(1) 
      freshA_iff_ex_vvsubstA_idle subst_Vr_id subst_chain 
      vsubstA_chain vsubstA_id) 

lemma freshA_LmA: 
  "{x,z} \<inter> X = {} \<Longrightarrow> z = x \<or> (fresh z t \<and> freshA z a) \<Longrightarrow> freshA z (LmA x t a)"
  using freshA_LmA' freshA_LmA_same by (meson insert_disjoint(1))

end (* context FR_BCE_Renset *)


subsection \<open>The relational version of the recursor \<close>

context FR_BCE_Renset
begin 

text \<open>The recursor is first defined relationally. Then it will be proved to be functional. \<close>

inductive R :: "trm \<Rightarrow> 'A \<Rightarrow> bool" where 
  Vr: "R (Vr x) (VrA x)" 
|
  Ap: "R t1 a1 \<Longrightarrow> R t2 a2 \<Longrightarrow> R (Ap t1 t2) (ApA t1 a1 t2 a2)" 
|
  Lm: "R t a \<Longrightarrow> x \<notin> X \<Longrightarrow> R (Lm x t) (LmA x t a)"

lemma F_Vr_elim[simp]: "R (Vr x) a \<longleftrightarrow> a = VrA x"
  apply safe
  subgoal using R.cases by fastforce  
  subgoal by (auto intro: R.intros) .

lemma F_Ap_elim: 
  assumes "R (Ap t1 t2) a"
  shows "\<exists>a1 a2. R t1 a1 \<and> R t2 a2 \<and> a = ApA t1 a1 t2 a2"
  by (metis Ap_Lm_diff(1) Ap_inj R.cases Vr_Ap_diff(1) assms)

lemma F_Lm_elim: 
  assumes "R (Lm x t) a"
  shows "\<exists>x' t' e. R t' e \<and> x' \<notin> X \<and> Lm x t = Lm x' t' \<and> a = LmA x' t' e"
  using assms by (cases rule: R.cases) auto

lemma F_total: "\<exists>a. R t a"
  using finite_X apply(induct rule: fresh_induct) by (auto intro: R.intros)

text \<open>The main lemma needed in the recursion theorem: It states that 
the relational version of the recursor is (1) functional, (2) preserves freshness 
and (3) preserves renaming. These three facts must be proved mutually recursively. \<close>

lemma F_main: 
  "(\<forall>a a'. R t a \<longrightarrow> R t a' \<longrightarrow> a = a') \<and> 
 (\<forall>a x. x \<notin> X \<and> fresh x t \<and> R t a \<longrightarrow> freshA x a) \<and> 
 (\<forall>a x y. x \<notin> X \<and> y \<notin> X \<longrightarrow> R t a \<longrightarrow> R (vsubst t y x) (vsubstA a y x))"
proof(induct t rule: substConnect_induct)
  case (Vr x)
  then show ?case by (auto simp: freshA_VrA vsubstA_VrA)
next
  case (Ap t1 t2)
  then show ?case apply safe  
      apply (metis F_Ap_elim) 
     apply (metis F_Ap_elim freshA_ApA fresh_Ap)
    by (smt (verit, ccfv_SIG) Diff_disjoint Diff_insert_absorb R.simps F_Ap_elim Int_commute 
        Int_insert_right_if0 subst_Ap vsubstA_ApA) 
next
  case (Lm x t)
  show ?case
  proof safe
    fix a1 a2 assume "R (Lm x t) a1" "R (Lm x t) a2" 
    then obtain x1' t1' a1' x2' t2' a2'
      where 1: "x1' \<notin> X" "R t1' a1'" "Lm x t = Lm x1' t1'" "a1 = LmA x1' t1' a1'"
        and   2: "x2' \<notin> X"  "R t2' a2'" "Lm x t = Lm x2' t2'" "a2 = LmA x2' t2' a2'"
      using F_Lm_elim by metis

    define z where "z = ppickFreshS X [x,x1',x2'] [t,t1',t2']"
    have z: "z \<notin> {x,x1',x2'}" "fresh z t" "fresh z t1'" "fresh z t2'" "z \<notin> X" 
      unfolding z_def using ppickFreshS[of X "[x,x1',x2']" "[t,t1',t2']"] by auto

    have 11: "vsubst t z x = vsubst t1' z x1'"
      using "1"(3) Lm_eq_elim_subst z by blast
    hence tt1': "substConnect t t1'"  
    	by (metis substConnect.simps subst_Vr_id subst_chain z(3))
    have 22: "subst t (Vr z) x = subst t2' (Vr z) x2'"
      using "2"(3) Lm_eq_elim_subst z by blast
    hence tt2': "substConnect t t2'"  
      by (metis Refl Step subst_Vr_id subst_chain z(4)) 

    show "a1 = a2" unfolding 1 2 apply(rule LmA_cong_freshA[of z])
      subgoal using z by (simp add: "1"(1) "2"(1))
      subgoal using z(1) by force
      subgoal by (simp add: z)
      subgoal apply(rule Lm[rule_format, OF tt1', 
              THEN conjunct2, THEN conjunct1, rule_format])
        using 1 z by auto
      subgoal using z by simp
      subgoal by (simp add: z)
      subgoal apply(rule Lm[rule_format, OF tt2', 
              THEN conjunct2, THEN conjunct1, rule_format])
        using 2 z by auto
      subgoal using "11" "22" by presburger
      subgoal by (metis "1"(1) "1"(2) "11" "2"(1) "2"(2) "22" Lm.hyps Step tt1' 
            tt2' z(5)) .
        (* *)
  next
    fix a y assume yX: "y \<notin> X"
      and fr: "fresh y (Lm x t)" "R (Lm x t) a"
    then obtain x' t' a'  
      where 0: "x' \<notin> X" "R t' a'" "Lm x t = Lm x' t'" "a = LmA x' t' a'" 
      using F_Lm_elim by metis

    define z where "z = ppickFreshS X [x,x'] [t,t']"
    have z: "z \<notin> {x,x'}" "fresh z t" "fresh z t'" "z \<notin> X"  
      unfolding z_def using ppickFreshS[of X "[x,x']" "[t,t']"] by auto

    have 00: "subst t (Vr z) x = subst t' (Vr z) x'"
      using 0(3) Lm_eq_elim_subst z by blast
    hence tt1': "substConnect t t'"  
    	by (metis substConnect.simps subst_Vr_id subst_chain z(3))

    show "freshA y a" unfolding 0
      apply(rule freshA_LmA)
       apply (simp add: "0"(1) yX)
      apply(subst disj_commute, safe) 
       apply (metis "0"(3) fresh_Lm fr(1))
      apply(rule Lm[rule_format,THEN conjunct2, THEN conjunct1, rule_format, of t']) 
      subgoal using tt1' .
      subgoal apply safe
        subgoal using yX by blast
        subgoal using fr(1) unfolding 0 by simp
        subgoal using 0(2) . . .

(* *)
  next 
    fix a yy y assume yy_y: "yy \<notin> X" "y \<notin> X" and "R (Lm x t) a" 
    then obtain x' t' a'  
      where 0: "x' \<notin> X" "R t' a'" "Lm x t = Lm x' t'" "a = LmA x' t' a'" 
      using F_Lm_elim by metis

    define z where "z = ppickFreshS X [x,x',y,yy] [t,t']"
    have z: "z \<notin> {x,x',y,yy}" "fresh z t" "fresh z t'" "z \<notin> X"
      unfolding z_def using ppickFreshS[of X "[x,x',y,yy]" "[t,t']"] by auto

    have 00: "subst t (Vr z) x = subst t' (Vr z) x'"
      using 0(3) Lm_eq_elim_subst z by blast
    hence tt1': "substConnect t t'"  
    	by (metis substConnect.simps subst_Vr_id subst_chain z(3))

    define t'' where "t'' \<equiv> subst t' (Vr z) x'" 

    have 1: "Lm x' t' = Lm z t''" unfolding t''_def  
    	by (simp add: Lm_subst_rename z(3))

    have tt'': "substConnect t t''" 
    	using Step t''_def tt1' by blast

    define a'' where "a'' \<equiv> vsubstA a' z x'" 

    have 11: "LmA x' t' a' = LmA z t'' a''" unfolding a''_def  
    	using "0"(1,2) LmA_rename_freshA Lm.hyps tt1' z(1) z(3,4) 
    	unfolding t''_def by auto 

    show "R (subst (Lm x t) (Vr y) yy) (vsubstA a y yy)"
      unfolding 0 1 11 using z apply (simp add: yy_y vsubstA_LmA)
      apply(rule R.Lm)
       apply(rule Lm[rule_format,THEN conjunct2, THEN conjunct2, rule_format])
      subgoal using tt'' .
      subgoal using yy_y(1) yy_y(2) by auto
      subgoal unfolding t''_def a''_def
        apply(rule Lm[rule_format,THEN conjunct2, THEN conjunct2, rule_format])
        subgoal using tt1' .
        subgoal using "0"(1) by blast
        subgoal using 0(2) . . 
      subgoal using z(4) . .  
  qed   
qed

lemmas F_functional = F_main[THEN conjunct1]
lemmas F_fresh = F_main[THEN conjunct2, THEN conjunct1]
lemmas F_subst = F_main[THEN conjunct2, THEN conjunct2]

subsection \<open>The functional version of the recursor \<close>

definition f :: "trm \<Rightarrow> 'A" where "f t \<equiv> SOME a. R t a"

lemma F_f: "R t (f t)"
  by (simp add: F_total f_def someI_ex)

lemma f_eq_F: "f t = a \<longleftrightarrow> R t a"
  by (meson F_f F_functional)


subsection \<open>The full-fledged recursion theorem \<close>

theorem f_Vr[simp]: "f (Vr x) = VrA x"
  unfolding f_eq_F by (auto simp: F_f intro: R.intros)

theorem f_Ap[simp]: "f (Ap t1 t2) = ApA t1 (f t1) t2 (f t2)"
  unfolding f_eq_F by (auto simp: F_f intro: R.intros)

theorem f_Lm[simp]: 
  "x \<notin> X \<Longrightarrow> f (Lm x t) = LmA x t (f t)"
  unfolding f_eq_F by (auto simp: F_f intro: R.intros)

theorem f_subst: 
  "y \<notin> X \<Longrightarrow> z \<notin> X \<Longrightarrow> f (subst t (Vr y) z) = vsubstA (f t) y z"
  using F_subst f_eq_F by blast

theorem f_fresh: 
  assumes "z \<notin> X" "fresh z t" 
  shows "freshA z (f t)"
  using F_f F_fresh assms by blast

(* Uniqueness: *)
theorem f_unique: 
  assumes [simp]: "\<And>x. g (Vr x) = VrA x" 
    "\<And>t1 t2. g (Ap t1 t2) = ApA t1 (g t1) t2 (g t2)" 
    "\<And>x t. x \<notin> X \<Longrightarrow> g (Lm x t) = LmA x t (g t)"
  shows "g = f"
  apply(rule ext)
  subgoal for t using finite_X by (induct t rule: fresh_induct, auto) .

end (* contex FR_FR_BCE_Renset *)



subsection \<open>The particular case of iteration \<close>

locale BCE_Renset = Renset vsubstA
  for vsubstA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A"
    +
  fixes 
    X :: "var set"
    (* Constructor-like operators: *)
    and VrA :: "var \<Rightarrow> 'A"
    and ApA :: "'A \<Rightarrow> 'A \<Rightarrow> 'A"
    and LmA :: "var \<Rightarrow> 'A \<Rightarrow> 'A"
  assumes 
    finite_X'[simp,intro!]: "finite X"
    and 
    vsubstA_VrA': "\<And> x y z. {y,z} \<inter> X = {} \<Longrightarrow>
  vsubstA (VrA x) y z = (if x = z then VrA y else VrA x)"
    and 
    vsubstA_ApA': "\<And> y z a1 a2. {y,z} \<inter> X = {} \<Longrightarrow>
  vsubstA (ApA a1 a2) y z =  
  ApA (vsubstA a1 y z) 
      (vsubstA a2 y z)"
    and 
    vsubstA_LmA': "\<And> a z x y. {x,y,z} \<inter> X = {} \<Longrightarrow>
  x \<noteq> y \<Longrightarrow> 
  vsubstA (LmA x a) y z = (if x = z then LmA x a else LmA x (vsubstA a y z))"
    and 
    LmA_rename': "\<And> x y z a. {x,y,z} \<inter> X = {} \<Longrightarrow>
  z \<noteq> y \<Longrightarrow> LmA x (vsubstA a z y) = LmA y (vsubstA (vsubstA a z y) y x)"
begin 

sublocale FR_BCE_Renset where 
  VrA = VrA and 
  ApA = "\<lambda>t1 a1 t2 a2. ApA a1 a2" and 
  LmA = "\<lambda>x t a. LmA x a" 
  apply standard by (auto simp: vsubstA_VrA' vsubstA_ApA' vsubstA_LmA' LmA_rename')

(* The recursion Theorem 11 from the paper: *) 
lemmas f_clauses = f_Vr f_Ap f_Lm f_subst f_unique

end (* context BCE_Renset *)


locale CE_Renset = Renset vsubstA
  for vsubstA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A"
    +
  fixes 
    (* Constructor-like operators: *)
    VrA :: "var \<Rightarrow> 'A"
    and ApA :: "'A \<Rightarrow> 'A \<Rightarrow> 'A"
    and LmA :: "var \<Rightarrow> 'A \<Rightarrow> 'A"
  assumes 
    vsubstA_VrA'': "\<And> x y z. 
  vsubstA (VrA x) y z = (if x = z then VrA y else VrA x)"
    and 
    vsubstA_ApA'': "\<And> y z a1 a2. 
  vsubstA (ApA a1 a2) y z =  
  ApA (vsubstA a1 y z) 
      (vsubstA a2 y z)"
    and 
    vsubstA_LmA'': "\<And> a z x y. 
  x \<noteq> y \<Longrightarrow> 
  vsubstA (LmA x a) y z = (if x = z then LmA x a else LmA x (vsubstA a y z))"
    and 
    LmA_rename'': "\<And> x y z a.  
  z \<noteq> y \<Longrightarrow> LmA x (vsubstA a z y) = LmA y (vsubstA (vsubstA a z y) y x)"
begin

sublocale BCE_Renset where X = "{}"
  apply standard by (auto simp: vsubstA_VrA'' vsubstA_ApA'' vsubstA_LmA'' LmA_rename'')

lemma triv: "x\<notin>{}" by simp

text \<open>The initiality theorem \<close>
lemmas f_clauses_init = f_Vr f_Ap f_Lm[OF triv] f_subst[OF triv triv] f_unique[simplified] 

end (* context CE_Renset *)




end 