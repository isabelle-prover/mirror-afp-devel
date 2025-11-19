subsection \<open>The Parallel Rewrite Relation\<close>

theory Parallel_Rewriting
  imports
    Trs
    Multihole_Context
begin

text \<open>The parallel rewrite relation as inductive definition\<close>
inductive_set par_rstep :: "('f,'v)trs \<Rightarrow> ('f,'v)trs" for R :: "('f,'v)trs"
  where root_step[intro]: "(s,t) \<in> R \<Longrightarrow> (s \<cdot> \<sigma>,t \<cdot> \<sigma>) \<in> par_rstep R"
  |  par_step_fun[intro]: "\<lbrakk>\<And> i. i < length ts \<Longrightarrow> (ss ! i,ts ! i) \<in> par_rstep R\<rbrakk> \<Longrightarrow> length ss = length ts
             \<Longrightarrow> (Fun f ss, Fun f ts) \<in> par_rstep R"
  |  par_step_var[intro]: "(Var x, Var x) \<in> par_rstep R"

lemma par_rstep_refl[intro]: "(t,t) \<in> par_rstep R"
  by (induct t, auto)

lemma all_ctxt_closed_par_rstep[intro]: "all_ctxt_closed F (par_rstep R)"
  unfolding all_ctxt_closed_def                  
  by auto

lemma args_par_rstep_pow_imp_par_rstep_pow:
  "length xs = length ys \<Longrightarrow> \<forall>i<length xs. (xs ! i, ys ! i) \<in> par_rstep R ^^ n \<Longrightarrow>
  (Fun f xs, Fun f ys) \<in> par_rstep R ^^ n"
proof(induct n arbitrary:ys)
  case 0
  then have "\<forall>i<length xs. (xs ! i = ys ! i)" by simp
  with 0 show ?case using relpow_0_I list_eq_iff_nth_eq by metis
next
  case (Suc n)
  let ?c = "\<lambda> z i. (xs ! i, z) \<in> par_rstep R ^^ n \<and> (z, ys ! i) \<in> par_rstep R"
  { fix i assume "i < length xs"
    from relpow_Suc_E[OF Suc(3)[rule_format, OF this]]
    have "\<exists> z. (?c z i)" by metis
  }
  with choice have "\<exists> zf. \<forall> i < length xs. (?c (zf i) i)" by meson
  then obtain zf where a:"\<forall> i < length xs. (?c (zf i) i)" by auto
  let ?zs = "map zf [0..<length xs]"
  have len:"length xs = length ?zs" by simp
  from a map_nth have  "\<forall>i<length xs.  (xs ! i, ?zs ! i) \<in> par_rstep R ^^ n" by auto
  from Suc(1)[OF len this] have n:"(Fun f xs, Fun f ?zs) \<in> par_rstep R ^^ n" by auto
  from a map_nth have  "\<forall>i<length xs. (?zs ! i, ys ! i) \<in> par_rstep R" by auto
  with par_step_fun len Suc(2) have "(Fun f ?zs, Fun f ys) \<in> par_rstep R" by auto
  with n show ?case by auto
qed

lemma ctxt_closed_par_rstep[intro]: "ctxt.closed (par_rstep R)"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume st: "(s,t) \<in> par_rstep R"
  let ?ss = "bef @ s # aft"
  let ?ts = "bef @ t # aft"
  show "(Fun f ?ss, Fun f ?ts) \<in> par_rstep R"
  proof (rule par_step_fun)
    fix i
    assume "i < length ?ts"
    show "(?ss ! i, ?ts ! i) \<in> par_rstep R"
      using par_rstep_refl[of "?ts ! i" R] st by (cases "i = length bef", auto simp: nth_append)
  qed simp
qed

lemma subst_closed_par_rstep: "(s,t) \<in> par_rstep R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> par_rstep R"
proof (induct rule: par_rstep.induct)
  case (root_step s t \<tau>)
  show ?case
    using par_rstep.root_step[OF root_step, of "\<tau> \<circ>\<^sub>s \<sigma>"] by auto
next
  case (par_step_var x)
  show ?case by auto
next
  case (par_step_fun ss ts f)
  show ?case unfolding eval_term.simps
    by (rule par_rstep.par_step_fun, insert par_step_fun(2-3), auto)
qed

lemma R_par_rstep: "R \<subseteq> par_rstep R"
  using root_step[of _ _ R Var] by auto

lemma par_rstep_rsteps: "par_rstep R \<subseteq> (rstep R)\<^sup>*"
proof
  fix s t
  assume "(s,t) \<in> par_rstep R"
  then show "(s,t) \<in> (rstep R)\<^sup>*"
  proof (induct rule: par_rstep.induct)
    case (root_step s t sigma)
    then show ?case by auto
  next
    case (par_step_var x)
    then show ?case by auto
  next
    case (par_step_fun ts ss f)
    from all_ctxt_closedD[of UNIV, OF all_ctxt_closed_rsteps _ par_step_fun(3) par_step_fun(2)]
    show ?case unfolding par_step_fun(3) by simp
  qed
qed

lemma rstep_par_rstep: "rstep R \<subseteq> par_rstep R"
  by (rule rstep_subset[OF ctxt_closed_par_rstep subst.closedI R_par_rstep],
      insert subst_closed_par_rstep, auto)

lemma par_rsteps_rsteps: "(par_rstep R)\<^sup>* = (rstep R)\<^sup>*" (is "?P = ?R")
proof
  from rtrancl_mono[OF par_rstep_rsteps[of R]] show "?P \<subseteq> ?R" by simp
  from rtrancl_mono[OF rstep_par_rstep] show "?R \<subseteq> ?P" .
qed

lemma par_rsteps_union: "(par_rstep A \<union> par_rstep B)\<^sup>* =
    (rstep (A \<union> B))\<^sup>*" 
proof
  show "(par_rstep A \<union> par_rstep B)\<^sup>* \<subseteq> (rstep (A \<union> B))\<^sup>*"
    by (metis par_rsteps_rsteps rstep_union rtrancl_Un_rtrancl set_eq_subset)
  show "(rstep (A \<union> B))\<^sup>* \<subseteq> (par_rstep A \<union> par_rstep B)\<^sup>*" unfolding rstep_union
    by (meson rstep_par_rstep rtrancl_mono sup_mono)
qed

lemma par_rstep_inverse: "par_rstep (R^-1) = (par_rstep R)^-1" 
proof -
  {
    fix s t :: "('a,'b)term" and R
    assume "(s,t) \<in> par_rstep (R^-1)" 
    hence "(t,s) \<in> par_rstep R" 
      by (induct s t, auto)
  }
  from this[of _ _ R] this[of _ _ "R^-1"]
  show ?thesis by auto
qed

lemma par_rstep_conversion: "(rstep R)\<^sup>\<leftrightarrow>\<^sup>* = (par_rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
  unfolding conversion_def 
  by (metis par_rsteps_rsteps rtrancl_Un_rtrancl rtrancl_converse)

lemma par_rstep_mono: assumes "R \<subseteq> S"
  shows "par_rstep R \<subseteq> par_rstep S" 
proof 
  fix s t
  show "(s, t) \<in> par_rstep R \<Longrightarrow> (s, t) \<in> par_rstep S" 
    by (induct s t rule: par_rstep.induct, insert assms, auto)
qed

lemma wf_trs_par_rstep: assumes wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and step: "(Var x, t) \<in> par_rstep R"
shows "t = Var x"
  using step
proof (cases rule: par_rstep.cases)
  case (root_step l r \<sigma>)
  from root_step(1) wf[OF root_step(3)] show ?thesis by (cases l, auto)
qed auto

text \<open>main lemma which tells us, that either a parallel rewrite step of \<open>l \<cdot> \<sigma>\<close> is inside \<open>l\<close>, or
  we can do the step completely inside \<open>\<sigma>\<close>\<close>
lemma par_rstep_linear_subst: assumes lin: "linear_term l"
  and step: "(l \<cdot> \<sigma>, t) \<in> par_rstep R"
shows "(\<exists> \<tau>. t = l \<cdot> \<tau> \<and> (\<forall> x \<in> vars_term l. (\<sigma> x, \<tau> x) \<in> par_rstep R) \<or>
               (\<exists> C l'' l' r'. l = C\<langle>l''\<rangle> \<and> is_Fun l'' \<and> (l',r') \<in> R \<and> (l'' \<cdot> \<sigma> = l' \<cdot> \<tau>) \<and> ((C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> \<tau> \<rangle>, t) \<in> par_rstep R))"
  using lin step
proof (induction l arbitrary: t)
  case (Var x t)
  let ?tau = "\<lambda> y. t"
  show ?case
    by (rule exI[of _ ?tau], rule disjI1, insert Var(2), auto)
next
  case (Fun f ss)
  let ?ss = "map (\<lambda> s. s \<cdot> \<sigma>) ss"
  let ?R = "par_rstep R"
  from Fun(3)
  show ?case
  proof (cases rule: par_rstep.cases)
    case (root_step l r \<tau>)
    show ?thesis
    proof (rule exI, rule disjI2, intro exI conjI)
      show "(l,r) \<in> R" by (rule root_step(3))
      show "Fun f ss = \<box>\<langle>Fun f ss\<rangle>" by simp
      show "(Fun f ss) \<cdot> \<sigma> = l \<cdot> \<tau>" by (rule root_step(1))
      show "((\<box> \<cdot>\<^sub>c \<sigma>)\<langle> r \<cdot> \<tau> \<rangle>, t) \<in> ?R" unfolding root_step(2) using par_rstep_refl by simp
    qed simp
  next
    case (par_step_var x)
    then show ?thesis by simp
  next
    case (par_step_fun ts ss1 g)
    then have id: "ss1 = ?ss" "g = f" and len: "length ts = length ss" by auto
    let ?p1 = "\<lambda> \<tau> i. ts ! i = ss ! i \<cdot> \<tau> \<and> (\<forall> x \<in> vars_term (ss ! i). (\<sigma> x, \<tau> x) \<in> ?R)"
    let ?p2 = "\<lambda> \<tau> i. (\<exists> C l'' l' r'. ss ! i = C\<langle> l''\<rangle> \<and> is_Fun l'' \<and> (l',r') \<in> R \<and> l'' \<cdot> \<sigma> = l' \<cdot> \<tau> \<and> ((C \<cdot>\<^sub>c \<sigma>)\<langle> r' \<cdot> \<tau> \<rangle>, (ts ! i)) \<in> ?R)"
    let ?p = "\<lambda> \<tau> i. ?p1 \<tau> i \<or> ?p2 \<tau> i"
    {
      fix i
      assume i: "i < length ss"
      with par_step_fun(4) id have i2: "i < length ts" by auto
      from par_step_fun(3)[OF i2] have step: "(ss ! i \<cdot> \<sigma>, ts ! i) \<in> par_rstep R" unfolding id nth_map[OF i] .
      from i have mem: "ss ! i \<in> set ss" by auto
      from Fun.prems(1) mem have "linear_term (ss ! i)" by auto
      from Fun.IH[OF mem this step] have "\<exists> \<tau>. ?p \<tau> i" .
    }
    then have "\<forall> i. \<exists> tau. i < length ss \<longrightarrow> ?p tau i" by blast
    from choice[OF this] obtain taus where taus: "\<And> i. i < length ss \<Longrightarrow> ?p (taus i) i" by blast
    show ?thesis
    proof (cases "\<exists> i. i < length ss \<and> ?p2 (taus i) i")
      case True
      then obtain i where i: "i < length ss" and p2: "?p2 (taus i) i" by blast+
      from par_step_fun(2)[unfolded id] have t: "t = Fun f ts" .
      from i have i': "i < length ts" unfolding len .
      from p2 obtain C l'' l' r' where ssi: "ss ! i = C \<langle>l''\<rangle>" and "is_Fun l''" "(l',r') \<in> R" "l'' \<cdot> \<sigma> = l' \<cdot> taus i"
        and tsi: "((C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> taus i \<rangle>, ts ! i) \<in> ?R" by blast
      from id_take_nth_drop[OF i, unfolded ssi] obtain bef aft where ss: "ss = bef @ C \<langle> l'' \<rangle> # aft"
        and bef: "bef = take i ss"
        and aft: "aft = drop (Suc i) ss" by blast
      let ?C = "More f bef C aft"
      let ?r = "(C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> taus i \<rangle>"
      let ?sig = "map (\<lambda> s. s \<cdot> \<sigma>)"
      let ?bra = "?sig bef @ ?r # ?sig aft"
      have C: "(?C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> taus i \<rangle> = Fun f ?bra" by simp
      show ?thesis unfolding ss
      proof (rule exI[of _ "taus i"], rule disjI2, rule exI[of _ ?C], intro exI conjI)
        show "is_Fun l''" by fact
        show "(l',r') \<in> R" by fact
        show "l'' \<cdot> \<sigma> = l' \<cdot> taus i" by fact
        show "((?C \<cdot>\<^sub>c \<sigma>) \<langle> r' \<cdot> taus i \<rangle>, t) \<in> ?R" unfolding C t
        proof  (rule par_rstep.par_step_fun)
          show "length ?bra = length ts"
            unfolding len unfolding ss by simp
        next
          fix j
          assume j: "j < length ts"
          show "(?bra ! j, ts ! j) \<in> ?R"
          proof (cases "j = i")
            case True
            then have "?bra ! j = ?r" using bef i by (simp add: nth_append)
            then show ?thesis using tsi True by simp
          next
            case False
            from bef i have "min (length ss) i = i" by simp
            then have "?bra ! j = (?sig bef @ (C \<langle> l'' \<rangle> \<cdot> \<sigma>) # ?sig aft) ! j" using False bef i by (simp add: nth_append)
            also have "... = ?sig ss ! j" unfolding ss by simp
            also have "... = ss1 ! j" unfolding id ..
            finally show ?thesis
              using par_step_fun(3)[OF j] by auto
          qed
        qed
      qed simp
    next
      case False
      with taus have taus: "\<And> i. i < length ss \<Longrightarrow> ?p1 (taus i) i" by blast
      from Fun(2) have "is_partition (map vars_term ss)" by simp
      from subst_merge[OF this, of taus] obtain \<tau> where tau: "\<And> i x. i < length ss \<Longrightarrow> x \<in> vars_term (ss ! i) \<Longrightarrow> \<tau> x = taus i x" by auto
      let ?tau = \<tau>
      {
        fix i
        assume i: "i < length ss"
        then have mem: "ss ! i \<in> set ss" by auto
        from taus[OF i] have p1: "?p1 (taus i) i" .
        have id: "ss ! i \<cdot> (taus i) = ss ! i \<cdot> \<tau>"
          by (rule term_subst_eq, rule tau[OF i, symmetric])
        have "?p1 ?tau i"
        proof (rule conjI[OF _ ballI])
          fix x
          assume x: "x \<in> vars_term (ss ! i)"
          with p1 have step: "(\<sigma> x, taus i x) \<in> par_rstep R" by auto
          with tau[OF i x]
          show "(\<sigma> x, ?tau x) \<in> par_rstep R" by simp
        qed (insert p1[unfolded id], auto)
      } note p1 = this
      have p1: "\<And> i. i < length ss \<Longrightarrow> ?p1 \<tau> i" by (rule p1)
      let ?ss = "map (\<lambda> s. s \<cdot> \<tau>) ss"
      show ?thesis unfolding par_step_fun(2) id
      proof (rule exI[of _ \<tau>], rule disjI1, rule conjI[OF _ ballI])
        have "ts = map (\<lambda> i. ts ! i) [0 ..< (length ts)]" by (rule map_nth[symmetric])
        also have "...  = map (\<lambda> i. ?ss ! i) [0 ..< length ?ss]" unfolding len using p1 by auto
        also have "... = ?ss" by (rule map_nth)
        finally have ts: "ts = ?ss" .
        show "Fun f ts = Fun f ss \<cdot> \<tau>" unfolding ts by auto
      next
        fix x
        assume "x \<in> vars_term (Fun f ss)"
        then obtain s where s: "s \<in> set ss" and x: "x \<in> vars_term s" by auto
        from s[unfolded set_conv_nth] obtain i where i: "i < length ss" and s: "s = ss ! i" by auto
        from p1[OF i] x[unfolded s]
        show "(\<sigma> x, \<tau> x) \<in> par_rstep R" by blast
      qed
    qed
  qed
qed

lemma par_rstep_id:
  "(s, t) \<in> R \<Longrightarrow> (s, t) \<in> par_rstep R"
  using par_rstep.root_step [of s t R Var] by simp

subsection \<open>Parallel Rewriting using Multihole Contexts\<close>

datatype ('f,'v)par_info = Par_Info 
  (par_left: "('f,'v)term") 
  (par_right: "('f,'v)term")
  (par_rule: "('f,'v)rule")

abbreviation par_lefts where "par_lefts \<equiv> map par_left" 
abbreviation par_rights where "par_rights \<equiv> map par_right" 
abbreviation par_rules where "par_rules \<equiv> (\<lambda> info. par_rule ` set info)" 

definition par_cond :: "('f,'v)trs \<Rightarrow> ('f,'v)par_info \<Rightarrow> bool" where
  "par_cond R info = (par_rule info \<in> R \<and> (par_left info, par_right info) \<in> rrstep {par_rule info})" 

abbreviation par_conds where "par_conds R \<equiv> \<lambda> infos. Ball (set infos) (par_cond R)"

lemma par_cond_imp_rrstep: assumes "par_cond R info"
  shows "(par_left info, par_right info) \<in> rrstep R" 
  using assms unfolding par_cond_def 
  by (metis rrstepE rrstepI singletonD)

lemma par_conds_imp_rrstep: assumes "par_conds R infos"
  and "s = par_lefts infos ! i" "t = par_rights infos ! i"
  and "i < length infos" 
shows "(s, t) \<in> rrstep R"
proof -
  from assms have eq: "s = par_left (infos ! i)" "t = par_right (infos ! i)" and pc: "par_cond R (infos ! i)" 
    by auto
  show ?thesis unfolding eq using par_cond_imp_rrstep[OF pc] .
qed

definition par_rstep_mctxt where 
  "par_rstep_mctxt R C infos = {(s, t). s =\<^sub>f (C, par_lefts infos) \<and> t =\<^sub>f (C, par_rights infos) \<and> par_conds R infos}"

lemma par_rstep_mctxtI: assumes "s =\<^sub>f (C, par_lefts infos)" "t =\<^sub>f (C, par_rights infos)" "par_conds R infos" 
  shows "(s,t) \<in> par_rstep_mctxt R C infos" 
  unfolding par_rstep_mctxt_def using assms by auto

lemma par_rstep_mctxt_reflI: "(s,s) \<in> par_rstep_mctxt R (mctxt_of_term s) []" 
  by (intro par_rstep_mctxtI, auto)

lemma par_rstep_mctxt_varI: "(Var x, Var x) \<in> par_rstep_mctxt R (MVar x) []" 
  by (intro par_rstep_mctxtI, auto)

lemma par_rstep_mctxt_MHoleI: "(l,r) \<in> R \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow> infos = [Par_Info s t (l,r)] 
  \<Longrightarrow> (s,t) \<in> par_rstep_mctxt R MHole infos" 
  by (intro par_rstep_mctxtI, auto simp: par_cond_def)

lemma par_rstep_mctxt_funI: 
  assumes rec: "\<And> i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> par_rstep_mctxt R (Cs ! i) (infos ! i)" 
    and len: "length ss = length ts" "length Cs = length ts" "length infos = length ts" 
  shows "(Fun f ss, Fun f ts) \<in> par_rstep_mctxt R (MFun f Cs) (concat infos)"
  unfolding par_rstep_mctxt_def
proof (standard, unfold split, intro conjI)
  {
    fix i
    assume "i < length ts" 
    from rec[OF this, unfolded par_rstep_mctxt_def]
    have "ss ! i =\<^sub>f (Cs ! i, par_lefts (infos ! i))" "ts ! i =\<^sub>f (Cs ! i, par_rights (infos ! i))" 
      "par_conds R (infos ! i)" by auto
  } note * = this
  from *(3)[folded len(3)] show "par_conds R (concat infos)"
    by (metis in_set_conv_nth nth_concat_split)
  show "Fun f ss =\<^sub>f (MFun f Cs, par_lefts (concat infos))" unfolding map_concat
    by (intro eqf_MFunI, insert *(1) len, auto)
  show "Fun f ts =\<^sub>f (MFun f Cs, par_rights (concat infos))" unfolding map_concat
    by (intro eqf_MFunI, insert *(2) len, auto)
qed

lemma par_rstep_mctxt_funI_ex: 
  assumes "\<And> i. i < length ts \<Longrightarrow> \<exists> C infos. (ss ! i, ts ! i) \<in> par_rstep_mctxt R C infos" 
    and "length ss = length ts" 
  shows "\<exists> C infos. (Fun f ss, Fun f ts) \<in> par_rstep_mctxt R C infos \<and> C \<noteq> MHole" 
proof -
  let ?n = "length ts" 
  from assms(1) have "\<forall> i. \<exists> C infos. i < ?n \<longrightarrow> (ss ! i, ts ! i) \<in> par_rstep_mctxt R C infos"  by auto
  from choice[OF this] obtain C where "\<forall> i. \<exists> infos. i < ?n \<longrightarrow> (ss ! i, ts ! i) \<in> par_rstep_mctxt R (C i) infos" by auto
  from choice[OF this] obtain infos where steps: "\<And> i. i < ?n \<Longrightarrow> (ss ! i, ts ! i) \<in> par_rstep_mctxt R (C i) (infos i)" by auto
  let ?Cs = "map C [0 ..< ?n]" 
  let ?Is = "map infos [0 ..< ?n]" 
  show ?thesis
  proof (intro exI conjI, rule par_rstep_mctxt_funI)
    show "length ?Cs = ?n" by simp
    show "length ?Is = ?n" by simp
  qed (insert assms(2) steps, auto)
qed

text \<open>Parallel rewriting is closed under multihole-contexts.\<close>
lemma par_rstep_mctxt:
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> par_rstep R"
  shows "(s, t) \<in> par_rstep R"
proof -
  have [simp]: "length ss = length ts" using assms by (auto dest!: eqfE)
  have [simp]: "t = fill_holes C ts" using assms by (auto dest: eqfE)
  have "(s, fill_holes C ts) \<in> par_rstep R"
    using assms by (intro eqf_all_ctxt_closed_step [of UNIV _ s C ss, THEN conjunct1]) auto
  then show ?thesis by simp
qed

lemma par_rstep_mctxt_rrstepI :
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> rrstep R"
  shows "(s, t) \<in> par_rstep R"
  by (meson assms contra_subsetD par_rstep_mctxt rrstep_imp_rstep rstep_par_rstep)


lemma par_rstep_mctxtD:
  assumes "(s, t) \<in> par_rstep R"
  shows "\<exists>C ss ts. s =\<^sub>f (C, ss) \<and> t =\<^sub>f (C, ts) \<and> (\<forall>i<length ss. (ss ! i, ts ! i) \<in> rrstep R)"
    (is "\<exists>C ss ts. ?P s t C ss ts")
  using assms
proof (induct)
  case (root_step s t \<sigma>)
  then have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rrstep R" by auto
  moreover have "s \<cdot> \<sigma> =\<^sub>f (MHole, [s \<cdot> \<sigma>])" and "t \<cdot> \<sigma> =\<^sub>f (MHole, [t \<cdot> \<sigma>])" by auto
  ultimately show ?case by force
next
  case (par_step_var x)
  have "Var x =\<^sub>f (MVar x, [])" by auto
  then show ?case by force
next
  case (par_step_fun ts ss f)
  then have "\<forall>i<length ts. \<exists>x. ?P (ss ! i) (ts ! i) (fst x) (fst (snd x)) (snd (snd x))" by force
  then obtain g where "\<forall>i<length ts. ?P (ss ! i) (ts ! i) (fst (g i)) (fst (snd (g i))) (snd (snd (g i)))"
    unfolding choice_iff' by blast
  moreover
  define Cs us vs where "Cs = map (\<lambda>i. fst (g i)) [0 ..< length ts]"
    and "us = map (\<lambda>i. fst (snd (g i))) [0 ..< length ts]"
    and "vs = map (\<lambda>i. snd (snd (g i))) [0 ..< length ts]"
  ultimately have [simp]: "length Cs = length ts"
    "length us = length ts" "length vs = length ts"
    and *: "\<forall>i<length us. ss ! i =\<^sub>f (Cs ! i, us ! i) \<and> ts ! i =\<^sub>f (Cs ! i, vs ! i) \<and>
      (\<forall>j<length (us ! i). (us ! i ! j, vs ! i ! j) \<in> rrstep R)"
    by simp_all
  define C where "C = MFun f Cs"
  have "Fun f ss =\<^sub>f (C, concat us)" and "Fun f ts =\<^sub>f (C, concat vs)"
    using * by (auto simp: C_def \<open>length ss = length ts\<close> intro: eqf_MFunI)
  moreover have "\<forall>i<length (concat us). (concat us ! i, concat vs ! i) \<in> rrstep R"
    using * by (intro concat_all_nth) (auto dest!: eqfE)
  ultimately show ?case by blast
qed

lemma par_rstep_mctxt_mono: assumes "R \<subseteq> S"
  shows "par_rstep_mctxt R C infos \<subseteq> par_rstep_mctxt S C infos" 
  using assms unfolding par_rstep_mctxt_def par_cond_def by auto


lemma par_rstep_mctxtE:
  assumes "(s, t) \<in> par_rstep R"
  obtains C infos where "s =\<^sub>f (C, par_lefts infos)" and "t =\<^sub>f (C, par_rights infos)"
    and "par_conds R infos"
proof -
  have "\<exists> C infos. s =\<^sub>f (C, par_lefts infos) \<and> t =\<^sub>f (C, par_rights infos) \<and> par_conds R infos" (is "\<exists>C infos. ?P s t C infos")
    using assms
  proof (induct)
    case (root_step s t \<sigma>)
    thus ?case by (intro exI[of _ MHole] exI[of _ "[Par_Info (s \<cdot> \<sigma>) (t \<cdot> \<sigma>) (s,t)]"], auto simp: par_cond_def)
  next
    case (par_step_var x)
    show ?case by (intro exI[of _ "MVar x"] exI[of _ Nil], auto)
  next
    case (par_step_fun ts ss f)
    have "\<exists>C infos. (Fun f ss, Fun f ts) \<in> par_rstep_mctxt R C infos \<and> C \<noteq> MHole" 
      by (intro par_rstep_mctxt_funI_ex, insert par_step_fun, auto simp: par_rstep_mctxt_def)
    then obtain C infos where "(Fun f ss, Fun f ts) \<in> par_rstep_mctxt R C infos" by auto
    hence "?P (Fun f ss) (Fun f ts) C infos" 
      by (auto simp: par_rstep_mctxt_def)
    thus ?case by blast
  qed
  with that show ?thesis by blast
qed

lemma par_rstep_par_rstep_mctxt_conv:
  "(s, t) \<in> par_rstep R \<longleftrightarrow> (\<exists>C infos. (s, t) \<in> par_rstep_mctxt R C infos)"
proof
  assume "(s, t) \<in> par_rstep R"
  from par_rstep_mctxtE[OF this] obtain C infos
    where "s =\<^sub>f (C, par_lefts infos)" and "t =\<^sub>f (C, par_rights infos)" and "par_conds R infos" 
    by metis
  then show "\<exists>C infos. (s, t) \<in> par_rstep_mctxt R C infos" by (auto simp: par_rstep_mctxt_def)
next
  assume "\<exists>C infos. (s, t) \<in> par_rstep_mctxt R C infos"
  then show "(s, t) \<in> par_rstep R"
    by (force simp: par_rstep_mctxt_def par_cond_def rrstep_def' set_conv_nth intro!: par_rstep_mctxt_rrstepI)
qed

fun subst_apply_par_info :: "('f,'v)par_info \<Rightarrow> ('f,'v)subst \<Rightarrow> ('f,'v)par_info" (infixl "\<cdot>pi" 67) where
  "Par_Info s t r \<cdot>pi \<sigma> = Par_Info (s \<cdot> \<sigma>) (t \<cdot> \<sigma>) r" 

lemma subst_apply_par_info_simps[simp]: 
  "par_left (info \<cdot>pi \<sigma>) = par_left info \<cdot> \<sigma>"
  "par_right (info \<cdot>pi \<sigma>) = par_right info \<cdot> \<sigma>"
  "par_rule (info \<cdot>pi \<sigma>) = par_rule info"
  "par_cond R info \<Longrightarrow> par_cond R (info \<cdot>pi \<sigma>)"
  unfolding par_cond_def
  by (cases info; force simp: subst.closedD subst_closed_rrstep)+

lemma par_rstep_mctxt_subst: assumes "(s,t) \<in> par_rstep_mctxt R C infos" 
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> par_rstep_mctxt R (C \<cdot>mc \<sigma>) (map (\<lambda> i. i \<cdot>pi \<sigma>) infos)" 
  using assms unfolding par_rstep_mctxt_def by (auto simp: o_def dest!: subst_apply_mctxt_sound[of _ C _ \<sigma>])

lemma par_rstep_mctxt_MVarE: 
  assumes "(s,t) \<in> par_rstep_mctxt R (MVar x) infos" 
  shows "s = Var x" "t = Var x" "infos = []" 
  using assms[unfolded par_rstep_mctxt_def]
  by (auto dest: eqf_MVarE)

lemma par_rstep_mctxt_MHoleE: 
  assumes "(s,t) \<in> par_rstep_mctxt R MHole infos" 
  obtains info where 
    "par_left info = s" 
    "par_right info = t" 
    "infos = [info]" 
    "(s, t) \<in> rrstep R" 
    "par_cond R info" 
proof -
  from assms[unfolded par_rstep_mctxt_def, simplified]
  have "s =\<^sub>f (MHole, par_lefts infos)" "t =\<^sub>f (MHole, par_rights infos)" and "par_conds R infos" by auto
  from eqf_MHoleE[OF this(1)] eqf_MHoleE[OF this(2)] this(3)
  obtain info where *: "infos = [info]" "s = par_left info" "t = par_right info" "par_cond R info"  
    by (cases infos, auto)
  from par_cond_imp_rrstep[OF *(4)] *
  have "(s,t) \<in> rrstep R" by auto
  with * have "\<exists> info. par_left info = s \<and> par_right info = t \<and> infos = [info] \<and> (s, t) \<in> rrstep R \<and> 
    par_cond R info" by auto
  thus "(\<And>info.
        par_left info = s \<Longrightarrow>
        par_right info = t \<Longrightarrow>
        infos = [info] \<Longrightarrow>
        (s, t) \<in> rrstep R \<Longrightarrow> par_cond R info \<Longrightarrow> thesis) \<Longrightarrow>
    thesis" by blast
qed

lemma par_rstep_mctxt_MFunD: 
  assumes "(s,t) \<in> par_rstep_mctxt R (MFun f Cs) infos" 
  shows "\<exists> ss ts Infos. 
    s = Fun f ss \<and>
    t = Fun f ts \<and>
    length ss = length Cs \<and>
    length ts = length Cs \<and>
    length Infos = length Cs \<and> 
    infos = concat Infos \<and>
    (\<forall> i < length Cs. (ss ! i, ts ! i) \<in> par_rstep_mctxt R (Cs ! i) (Infos ! i))"
proof -
  from assms[unfolded par_rstep_mctxt_def]
  have eq: "s =\<^sub>f (MFun f Cs, par_lefts infos)" "t =\<^sub>f (MFun f Cs, par_rights infos)" 
    and pc: "par_conds R infos" 
    by auto
  define Infos where "Infos = partition_holes infos Cs" 
  let ?sss = "map par_lefts Infos" 
  let ?tss = "map par_rights Infos" 
  let ?n = "length Cs" 
  let ?is = "[0..<?n]"
  from eqfE[OF eq(1)]
  have s: "s = Fun f (map (\<lambda>i. fill_holes (Cs ! i) (?sss ! i)) ?is)" 
    and num: "num_holes (MFun f Cs) = length infos" 
    and len: "length Infos = ?n"
    and infos: "infos = concat Infos"
    and lens: "\<And> i. i < ?n \<Longrightarrow> num_holes (Cs ! i) = length (Infos ! i)" 
    by (auto simp: Infos_def)
  note pc = pc[unfolded infos set_concat]
  from eqfE[OF eq(2)] num
  have t: "t = Fun f (map (\<lambda>i. fill_holes (Cs ! i) (?tss ! i)) ?is)" 
    by (auto simp: Infos_def)
  show ?thesis
    apply (intro exI[of _ Infos] exI conjI infos len allI impI)
        apply (rule s)
       apply (rule t)
      apply force
     apply force
    apply (intro par_rstep_mctxtI, insert lens len pc, auto)
    done
qed


subsection\<open>Variable Restricted Parallel Rewriting\<close>
  (* a parallel rewrite relation that restricts instantiation of variables,
   relevant for Toyama's refinement on joining parallel critical pairs *)

(* it is assumed that the context-positions are within the term *)
fun vars_below_hole :: "('f,'v)term \<Rightarrow> ('f,'v)mctxt \<Rightarrow> 'v set" where
  "vars_below_hole t MHole = vars_term t" 
| "vars_below_hole t (MVar y) = {}" 
| "vars_below_hole (Fun _ ts) (MFun _ Cs) = 
     \<Union> (set (map (\<lambda> (t,C). vars_below_hole t C) (zip ts Cs)))" 
| "vars_below_hole (Var _) (MFun _ _) = Code.abort (STR ''assumption in vars_below_hole violated'') (\<lambda> _. {})" 

lemma vars_below_hole_no_hole: "hole_poss C = {} \<Longrightarrow> vars_below_hole t C = {}" 
  by (induct t C rule: vars_below_hole.induct, auto simp: set_zip, blast)

lemma vars_below_hole_mctxt_of_term[simp]: "vars_below_hole t (mctxt_of_term u) = {}" 
  by (rule vars_below_hole_no_hole, auto)

lemma vars_below_hole_vars_term: "vars_below_hole t C \<subseteq> vars_term t" 
  by (induct t C rule: vars_below_hole.induct; force simp: set_zip set_conv_nth)

lemma vars_below_hole_subst[simp]: "vars_below_hole t (C \<cdot>mc \<sigma>) = vars_below_hole t C" 
  by (induct t C rule: vars_below_hole.induct; fastforce simp: set_zip)

lemma vars_below_hole_Fun: assumes "length ls = length Cs" 
  shows "vars_below_hole (Fun f ls) (MFun f Cs) = \<Union> {vars_below_hole (ls ! i) (Cs ! i) | i. i < length Cs}" 
  using assms by (auto simp: set_zip)  

lemma vars_below_hole_term_subst: 
  "hole_poss D \<subseteq> poss t \<Longrightarrow> vars_below_hole (t \<cdot> \<sigma>) D = \<Union> (vars_term ` \<sigma> ` vars_below_hole t D)"
proof (induct t D rule: vars_below_hole.induct)
  case (1 t)
  then show ?case by (auto simp: vars_term_subst)
next
  case (3 f ts g Cs)
  then show ?case by (fastforce simp: set_zip)
next
  case (4 x f Cs)
  hence hp: "hole_poss (MFun f Cs) = {}" by auto
  show ?case unfolding vars_below_hole_no_hole[OF hp] by auto
qed auto


lemma vars_below_hole_eqf: assumes "t =\<^sub>f (C, ts)"
  shows "vars_below_hole t C = \<Union> (vars_term ` set ts)" 
  using assms
proof (induct C arbitrary: t ts)
  case (MVar x)
  from eqf_MVarE[OF MVar(1)]  
  show ?case by auto
next
  case MHole
  from eqf_MHoleE[OF MHole(1)]
  show ?case by auto
next
  case (MFun f Cs t ss)
  from eqf_MFunE[OF MFun(2)] obtain ts sss where
    *: "t = Fun f ts" "length ts = length Cs" "length sss = length Cs" 
    "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>f (Cs ! i, sss ! i)"
    "ss = concat sss" by blast
  {
    fix i
    assume i: "i < length Cs" 
    hence mem: "Cs ! i \<in> set Cs" by auto
    from MFun(1)[OF mem *(4)[OF i]]
    have "vars_below_hole (ts ! i) (Cs ! i) = \<Union> (vars_term ` set (sss ! i))" .
  } note IH = this
  show ?case unfolding *(1) *(5) set_concat set_conv_nth[of sss] using IH *(2,3)
    by (auto simp: set_zip)
qed

(* The variable restricted parallel rewrite relation *)

definition "par_rstep_var_restr R V = {(s,t) | s t C infos. 
  (s, t) \<in> par_rstep_mctxt R C infos \<and> vars_below_hole t C \<inter> V = {}}" 

lemma par_rstep_var_restr_mono: assumes "R \<subseteq> S" "W \<subseteq> V" 
  shows "par_rstep_var_restr R V \<subseteq> par_rstep_var_restr S W" 
  unfolding par_rstep_var_restr_def using par_rstep_mctxt_mono[OF assms(1)] assms(2)
  by blast

lemma par_rstep_var_restr_refl[simp]: "(t, t) \<in> par_rstep_var_restr R V" 
  unfolding par_rstep_var_restr_def
  by (intro CollectI exI conjI refl, force, rule par_rstep_mctxt_reflI, auto)

text \<open>the most important property: a substitution step and a parallel step 
  can be merged into a single parallel step\<close>
lemma merge_par_rstep_var_restr: 
  assumes subst_R: "\<And> x. (\<delta> x, \<gamma> x) \<in> par_rstep R" 
    and st: "(s, t) \<in> par_rstep_var_restr R V" 
    and subst_eq: "\<And> x. x \<notin> V \<Longrightarrow> \<delta> x = \<gamma> x"
  shows "(s \<cdot> \<delta>, t \<cdot> \<gamma>) \<in> par_rstep R"
proof -
  from st[unfolded par_rstep_var_restr_def] subst_eq
  obtain C infos where st: "(s, t) \<in> par_rstep_mctxt R C infos" 
    and subst_eq: "\<And> x. x \<in> vars_below_hole t C \<Longrightarrow> \<delta> x = \<gamma> x"
    by auto
  thus ?thesis  
  proof (induct C arbitrary: s t infos)
    case (MVar x)
    from par_rstep_mctxt_MVarE[OF this(1)]
    show ?case using subst_R by auto
  next
    case (MHole s t)
    have "(s,t) \<in> par_rstep R" 
      using MHole.prems(1) par_rstep_par_rstep_mctxt_conv by blast
    hence step: "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> par_rstep R" 
      by (rule subst_closed_par_rstep)
    have "vars_below_hole t MHole = vars_term t" by simp
    with MHole(2) have t: "t \<cdot> \<delta> = t \<cdot> \<gamma>" by (auto intro: term_subst_eq)
    thus ?case using step by auto
  next
    case (MFun f Cs s t infos)
    let ?n = "length Cs" 
    let ?is = "[0..<?n]" 

    from par_rstep_mctxt_MFunD[OF MFun(2)]
    obtain ss ts Infos
      where s: "s = Fun f ss" 
        and t: "t = Fun f ts" 
        and len: "length ss = length Cs" 
        "length ts = length Cs"
        "length Infos = length Cs" 
        and infos: "infos = concat Infos" 
        and steps: "\<And> i. i<length Cs \<Longrightarrow> (ss ! i, ts ! i) \<in> par_rstep_mctxt R (Cs ! i) (Infos ! i)" 
      by blast
    {
      fix i
      assume i: "i < ?n"
      hence mem: "Cs ! i \<in> set Cs" by auto
      have IH: "(ss ! i \<cdot> \<delta>, ts ! i \<cdot> \<gamma>) \<in> par_rstep R" 
      proof (rule MFun(1)[OF mem steps[OF i]])
        fix x
        assume "x \<in> vars_below_hole (ts ! i) (Cs ! i)" 
        hence "x \<in> vars_below_hole t (MFun f Cs)" unfolding t using i len(2)
          by (auto simp: set_zip)
        from MFun(3)[OF this] show "\<delta> x = \<gamma> x" .
      qed
    }
    thus ?case unfolding s t using len(1-2) MFun(1-2) by auto
  qed
qed

text \<open>the variable restricted parallel rewrite relation is closed under variable renamings, 
  provided that the set of forbidden variables is also renamed (in the inverse way)\<close>
lemma par_rstep_var_restr_subst: 
  assumes "(s,t) \<in> par_rstep_var_restr R (\<gamma> ` V)" 
    and "\<And> x. \<sigma> x \<cdot> (Var o \<gamma>) = Var x" 
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> par_rstep_var_restr R V"
proof -
  from assms(1)[unfolded par_rstep_var_restr_def, simplified]
  obtain C infos where step: "(s, t) \<in> par_rstep_mctxt R C infos" and vars: "vars_below_hole t C \<inter> \<gamma> ` V = {}"
    by auto
  from step[unfolded par_rstep_mctxt_def, simplified] 
  have "t =\<^sub>f (C, par_rights infos)" by auto
  hence "hole_poss C \<subseteq> poss t" by (metis hole_poss_subset_poss)
  hence hp: "hole_poss (C \<cdot>mc \<sigma>) \<subseteq> poss t" 
    using hole_poss_subst by auto
  from par_rstep_mctxt_subst[OF step, of \<sigma>]
  have step: "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> par_rstep_mctxt R (C \<cdot>mc \<sigma>) (map (\<lambda>i. i \<cdot>pi \<sigma>) infos)" .
  show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> par_rstep_var_restr R V" 
    unfolding par_rstep_var_restr_def
  proof (standard, intro exI conjI, rule refl, rule step)
    show "vars_below_hole (t \<cdot> \<sigma>) (C \<cdot>mc \<sigma>) \<inter> V = {}" 
      unfolding vars_below_hole_term_subst[OF hp] 
      unfolding vars_below_hole_subst
    proof (intro equals0I, elim IntE)
      fix x
      assume "x \<in> \<Union> (vars_term ` \<sigma> ` vars_below_hole t C)" 
      then obtain y where y: "y \<in> vars_below_hole t C" and x: "x \<in> vars_term (\<sigma> y)" by auto
      from y vars have y: "y \<notin> \<gamma> ` V" by auto
      assume "x \<in> V"
      with assms(2)[of y] y x show False unfolding o_def by (cases "\<sigma> y", auto)
    qed
  qed
qed

end