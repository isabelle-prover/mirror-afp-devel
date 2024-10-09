theory DataRefinement
imports NREST
begin

subsection \<open>Data Refinement\<close>


lemma "{(1,2),(2,4)}``{1,2}={2,4}" by auto


definition conc_fun ("\<Down>") where
  "conc_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
                                                                  (* ^- not so sure here *)
definition abs_fun ("\<Up>") where
  "abs_fun R m \<equiv> case m of FAILi \<Rightarrow> FAILT 
    | REST X \<Rightarrow> if dom X\<subseteq>Domain R then REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R}) else FAILT"
                                                (* ^- not so sure here *)
lemma 
  conc_fun_FAIL[simp]: "\<Down>R FAILT = FAILT" and
  conc_fun_RES: "\<Down>R (REST X) = REST (\<lambda>c. Sup {X a| a. (c,a)\<in>R})"
  unfolding conc_fun_def by (auto split: nrest.split)


lemma nrest_Rel_mono: "A \<le> B \<Longrightarrow> \<Down> R A \<le> \<Down> R B"
  unfolding conc_fun_def by (fastforce split: nrest.split simp: le_fun_def intro!: Sup_mono)
 
subsubsection \<open>Examples\<close>

definition Rset where "Rset = { (c,a)| c a. set c = a}"
                                     
lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  by (auto simp add: le_fun_def conc_fun_def RETURNT_def Rset_def)
  
lemma "RETURNT [1,2,3] \<le> \<Down>Rset (RETURNT {1,2,3})"
  by (auto simp add: le_fun_def conc_fun_def RETURNT_def Rset_def)

definition Reven where "Reven = { (c,a)| c a. even c = a}"

lemma "RETURNT 3 \<le> \<Down>Reven (RETURNT False)"
  by (auto simp add: le_fun_def conc_fun_def RETURNT_def Reven_def)

lemma "m \<le> \<Down>Id m"
  unfolding conc_fun_def RETURNT_def by (cases m) auto


lemma "m \<le> \<Down>{} m \<longleftrightarrow> (m=FAILT \<or> m = SPECT bot)"
  unfolding conc_fun_def RETURNT_def by (cases m) (auto simp add: bot.extremum_uniqueI le_fun_def)

lemma abs_fun_simps[simp]: 
  "\<Up>R FAILT = FAILT"
  "dom X\<subseteq>Domain R \<Longrightarrow> \<Up>R (REST X) = REST (\<lambda>a. Sup {X c| c. (c,a)\<in>R})"
  "\<not>(dom X\<subseteq>Domain R) \<Longrightarrow> \<Up>R (REST X) = FAILT"
  unfolding abs_fun_def by (auto split: nrest.split)
 
context fixes R assumes SV: "single_valued R" begin

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Sup_sv: "(c, a') \<in> R \<Longrightarrow>  Sup {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma indomD: " M c = Some y \<Longrightarrow> dom M \<subseteq> Domain R \<Longrightarrow> (\<exists>a. (c,a)\<in>R)"
  by auto

lemma conc_abs_swap: "m' \<le> \<Down>R m \<longleftrightarrow> \<Up>R m' \<le> m"
proof(cases m; cases m')
  fix M M'
  note [simp] = conc_fun_def abs_fun_def
  assume b[simp]: "m = REST M" "m' = REST M'"
  show ?thesis
  proof
    assume a: "m' \<le> \<Down> R m"
    from a b have R: "m' \<le> REST (\<lambda>c. \<Squnion> {M a |a. (c, a) \<in> R})"
      using conc_fun_RES by metis
    with R have Domain: "dom M' \<subseteq> Domain R"
      by (auto simp add: le_fun_def Sup_option_def split: if_splits option.splits)
    from R have " M' x' \<le> M x" if "(x',x) \<in> R" for x x'
      by (auto simp add: Sup_sv[OF that] intro: le_funI dest: le_funD[of _ _ x'])
    with R SV Domain show "\<Up> R m' \<le> m"
      by (auto intro!: le_funI simp add: Sup_le_iff)
  next
    assume a: "\<Up> R m' \<le> m"
    show "m' \<le> \<Down>R m"
    proof(cases "dom M' \<subseteq> Domain R")
      case True(* 
      with a have " M' x' \<le> M x" if "(x',x) \<in> R" for x x'
        apply  (auto simp add: Sup_sv[OF that] intro: le_funI dest: le_funD[of _ _ x']) sorry *)
      
      have "M' x \<le> \<Squnion> {M a |a. (x, a) \<in> R}" for x
      proof(cases "M' x")
        case (Some y)
        with True obtain x' where x_x': "(x,x') \<in> R" 
          by blast
        with a SV show ?thesis
          by (force simp add: Sup_sv[OF x_x'] Sup_le_iff dest!: le_funD[of _ _ x'] split: if_splits)
      qed auto
      then show "m' \<le> \<Down> R m"
        by (auto intro!: le_funI)
    next
      case False
      with a show ?thesis
        by auto
    qed
  qed
qed (auto simp add: conc_fun_def abs_fun_def)

lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows
  Inf_sv: "(c, a') \<in> R \<Longrightarrow>  Inf {m a| a. (c,a) \<in> R} = m a'"
proof -
  assume "(c,a') \<in> R"
  with SV have singleton: "{m a| a. (c,a) \<in> R} = {m a'}" by(auto dest: single_valuedD) 
  show ?thesis unfolding singleton by simp
qed 

lemma ac_galois: "galois_connection (\<Up>R) (\<Down>R)"
  by (unfold_locales) (rule conc_abs_swap)


lemma 
  fixes m :: "'b \<Rightarrow> enat option"
  shows Sup_some_svD: "Sup {m a |a. (c, a) \<in> R} = Some t' \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> m a = Some t')"
  by (frule Sup_Some) (use SV in \<open>auto simp add: single_valued_def Sup_sv\<close>)

end 


lemma pw_abs_nofail[refine_pw_simps]: 
  "nofailT (\<Up>R M) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. (\<exists>t. inresT M x t) \<longrightarrow> x\<in>Domain R))" (is "?l \<longleftrightarrow> ?r")
proof (cases M)
  case FAILi
  then show ?thesis
    by auto
next
  case [simp]: (REST m)
  show ?thesis
  proof
    assume "?l"
    then show ?r
      by (auto simp: abs_fun_def split: if_splits)
  next
    assume a: ?r
    with REST have "x\<in>Domain R" if "m x = Some y" for x y
    proof-
      have "enat 0 \<le> y"
        by (simp add: enat_0)
      with that REST a show ?thesis
        by auto
    qed
    then show ?l 
      by (auto simp: abs_fun_def)
  qed
qed

lemma pw_conc_nofail[refine_pw_simps]: 
  "nofailT (\<Down>R S) = nofailT S"
  by (cases S) (auto simp: conc_fun_RES)

lemma "single_valued A \<Longrightarrow> single_valued B \<Longrightarrow> single_valued (A O B)"
  by (simp add: single_valued_relcomp)

lemma Sup_enatoption_less2: " Sup X = Some \<infinity> \<Longrightarrow> (\<exists>x. Some x \<in> X \<and> enat t < x)"
  using Sup_enat_less2
  by (metis Sup_option_def in_these_eq option.distinct(1) option.sel)

lemma pw_conc_inres[refine_pw_simps]:
  "inresT (\<Down>R S') s t = (nofailT S' 
  \<longrightarrow> ((\<exists>s'. (s,s')\<in>R \<and> inresT S' s' t)))" (is "?l \<longleftrightarrow> ?r")
proof(cases S')
  case [simp]: (REST m')
  show ?thesis
  proof
    assume a: ?l
    from this obtain t' where t': "enat t \<le> t'" "\<Squnion> {m' a |a. (s, a) \<in> R} = Some t'"
      by (auto simp: conc_fun_RES) 
    then obtain a t'' where "(s, a) \<in> R" "m' a = Some t''" "enat t \<le> t''"
    proof(cases t')
      case (enat n)
      with t' that[where t''=n] show ?thesis 
        by(auto dest: Sup_finite_enat)
    next
      case infinity
      with t' that show ?thesis 
        by (force dest!: Sup_enatoption_less2[where t=t] simp add: less_le_not_le t'(1))
    qed
    then show ?r
      by auto
  next
    assume a: ?r
    then obtain s' t' where s'_t': "(s,s') \<in> R" "m' s' = Some t'" "enat t \<le> t'"
      by (auto simp: conc_fun_RES)
    then have "\<exists>t'\<ge>enat t. \<Squnion> {m' a |a. (s, a) \<in> R} \<ge> Some t'"
      by (intro exI[of _ t']) (force intro: Sup_upper)
    then show ?l
      by (auto simp: conc_fun_RES elim!: le_some_optE)
  qed
qed simp

lemma sv_the: "single_valued R \<Longrightarrow> (c,a) \<in> R \<Longrightarrow> (THE a. (c, a) \<in> R) = a"
  by (simp add: single_valued_def the_equality)

lemma
  conc_fun_RES_sv:
  assumes SV: "single_valued R"
  shows "\<Down>R (REST X) = REST (\<lambda>c. if c\<in>Domain R then X (THE a. (c,a)\<in>R) else None )"
  using SV by (auto simp add: Sup_sv sv_the Domain_iff conc_fun_def bot_option_def
      intro!: ext split: nrest.split)

lemma conc_fun_mono[simp, intro!]: 
  shows "mono (\<Down>R)"
  by (rule monoI) (auto simp: pw_le_iff refine_pw_simps) 


lemma conc_fun_R_mono:
  assumes "R \<subseteq> R'" 
  shows "\<Down>R M \<le> \<Down>R' M"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)



lemma SupSup_2: "Sup {m a |a. (c, a) \<in> R O S} =  Sup {m a |a b. (b,a)\<in>S \<and> (c,b)\<in>R }"
proof -
  have i: "\<And>a. (c,a) \<in> R O S \<longleftrightarrow> (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)" by auto
  have "Sup {m a |a. (c, a) \<in> R O S} = Sup {m a |a. (\<exists>b. (b,a)\<in>S \<and> (c,b)\<in>R)}" 
      unfolding i by auto
    also have "...  = Sup {m a |a b. (b,a)\<in>S \<and> (c,b)\<in>R}" by auto
    finally show ?thesis .
  qed

lemma 
  fixes m :: "'a \<Rightarrow> enat option"
  shows SupSup: "Sup {Sup {m aa |aa. P a aa c} |a. Q a c} = Sup {m aa |a aa. P a aa c \<and> Q a c}"
  by (rule antisym) (auto intro: Sup_least Sup_subset_mono Sup_upper2)

lemma 
  fixes m :: "'a \<Rightarrow> enat option"
  shows 
    SupSup_1: "Sup {Sup {m aa |aa. (a, aa) \<in> S} |a. (c, a) \<in> R} = Sup {m aa |a aa. (a,aa)\<in>S \<and> (c,a)\<in>R}"
  by(rule SupSup)


lemma conc_fun_chain:
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
proof(cases M)
  case [simp]: (REST x)
  have "\<Squnion> {\<Squnion> {x aa |aa. (a, aa) \<in> S} |a. (c, a) \<in> R} = \<Squnion> {x a |a. (c, a) \<in> R O S}" for c
    by (unfold SupSup_1 SupSup_2) meson
  then show ?thesis 
    by (simp add: conc_fun_RES)
qed auto 

lemma conc_fun_chain_sv:
  assumes SVR: "single_valued R" and SVS: "single_valued S"
  shows "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  using assms conc_fun_chain by blast


lemma conc_Id[simp]: "\<Down>Id = id"
  unfolding conc_fun_def [abs_def] by (auto split: nrest.split)

                                 
lemma conc_fun_fail_iff[simp]: 
  "\<Down>R S = FAILT \<longleftrightarrow> S=FAILT"
  "FAILT = \<Down>R S \<longleftrightarrow> S=FAILT"
  by (auto simp add: pw_eq_iff refine_pw_simps)

lemma conc_trans[trans]:
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

lemma conc_trans_sv:
  assumes SV: "single_valued R" "single_valued R'"
    and A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

text \<open>WARNING: The order of the single statements is important here!\<close>
lemma conc_trans_additional[trans]:
  assumes "single_valued R"
  shows
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>R  C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>\<Down>R  C"

  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>    B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  using assms conc_trans[where R=R and R'=Id]
  by (auto intro: order_trans)

lemma RETURNT_refine:
  assumes "(x,x')\<in>R"
  shows "RETURNT x \<le> \<Down>R (RETURNT x')"
  using assms
  by (auto simp: RETURNT_def conc_fun_RES le_fun_def Sup_upper)  

lemma bindT_refine':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x' t . \<lbrakk> (x,x')\<in>R'; inresT M x t; inresT M' x' t;
    nofailT M; nofailT M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bindT M' (\<lambda>x'. f' x'))"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast

lemma bindT_refine:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bindT M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  apply (rule bindT_refine') using assms by auto

subsection \<open>WHILET refine\<close>

lemma RECT_refine:
  assumes M: "mono2 body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (RECT (\<lambda>f' x'. body' f' x') x')"
proof(cases "mono2 body'")
  case True
  have "flatf_gfp body x \<le> \<Down> S (flatf_gfp body' x')"
    by  (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp body" 
    and B'=body 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
    (use True in \<open>auto intro: RS dest: trimonoD_flatf_ge\<close>)
  then show ?thesis 
    by (auto simp add: M RECT_flat_gfp_def)
qed (auto simp add: RECT_flat_gfp_def)
                                         
lemma WHILET_refine:
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "whileT b f x \<le> \<Down>R (whileT b' f' x')"
  unfolding whileT_def
  apply (rule RECT_refine[OF _ R0])
   subgoal by refine_mono
   subgoal by (auto simp add: COND_REF STEP_REF RETURNT_refine intro: bindT_refine[where R'=R])  
  done

lemma SPECT_refines_conc_fun':
  assumes a: "\<And>m c.  M = SPECT m
          \<Longrightarrow> c \<in> dom n \<Longrightarrow> (\<exists>a. (c,a)\<in>R \<and> n c \<le> m a)"
  shows "SPECT n \<le> \<Down> R M"
proof - 
  have "n c \<le> \<Squnion> {m a |a. (c, a) \<in> R}" if "M = SPECT m" for c m 
  proof (cases "c \<in> dom n")
    case True
    with that a obtain a where k: "(c,a)\<in>R" "n c \<le> m a" by blast 
    then show ?thesis 
      by (intro Sup_upper2) auto
  next
    case False
    then show ?thesis 
      by (simp add: domIff)
  qed 
  then show ?thesis
    unfolding conc_fun_def by (auto simp add: le_fun_def split: nrest.split) 
qed

lemma SPECT_refines_conc_fun:
  assumes a: "\<And>m c. (\<exists>a. (c,a)\<in>R \<and> n c \<le> m a)"
  shows "SPECT n \<le> \<Down> R (SPECT m)"
  by (rule SPECT_refines_conc_fun') (use a in auto)


lemma conc_fun_br: "\<Down> (br \<alpha> I1) (SPECT (emb I2 t))
        = (SPECT (emb (\<lambda>x. I1 x \<and> I2 (\<alpha> x)) t))"
  unfolding conc_fun_RES
    using Sup_Some by (auto simp: emb'_def br_def bot_option_def Sup_option_def) 

end