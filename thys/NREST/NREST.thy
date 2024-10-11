theory NREST
  imports "HOL-Library.Extended_Nat" "Refine_Monadic.RefineG_Domain" Refine_Monadic.Refine_Misc  
  "HOL-Library.Monad_Syntax" NREST_Auxiliaries
begin

section "NREST"

datatype 'a nrest = FAILi | REST "'a \<Rightarrow> enat option"

instantiation nrest :: (type) complete_lattice
begin

fun less_eq_nrest where
  "_ \<le> FAILi \<longleftrightarrow> True" |
  "(REST a) \<le> (REST b) \<longleftrightarrow> a \<le> b" |
  "FAILi \<le> (REST _) \<longleftrightarrow> False"

fun less_nrest where
  "FAILi < _ \<longleftrightarrow> False" |
  "(REST _) < FAILi \<longleftrightarrow> True" |
  "(REST a) < (REST b) \<longleftrightarrow> a < b"

fun sup_nrest where
  "sup _ FAILi = FAILi" |
  "sup FAILi _ = FAILi" |
  "sup (REST a) (REST b) = REST (\<lambda>x. max (a x) (b x))"

fun inf_nrest where 
  "inf x FAILi = x" |
  "inf FAILi x = x" |
  "inf (REST a) (REST b) = REST (\<lambda>x. min (a x) (b x))"

lemma "min (None) (Some (1::enat)) = None" by simp
lemma "max (None) (Some (1::enat)) = Some 1" by eval

definition "Sup X \<equiv> if FAILi\<in>X then FAILi else REST (Sup {f . REST f \<in> X})"
definition "Inf X \<equiv> if \<exists>f. REST f\<in>X then REST (Inf {f . REST f \<in> X}) else FAILi"

definition "bot \<equiv> REST (Map.empty)"
definition "top \<equiv> FAILi"

instance
proof(intro_classes, goal_cases)
  case (1 x y)
  then show ?case
    by (cases x; cases y) auto
next
  case (2 x)
  then show ?case
    by (cases x) auto
next
  case (3 x y z)
  then show ?case 
    by (cases x; cases y; cases z) auto
next
  case (4 x y)
  then show ?case 
    by (cases x; cases y) auto
next
  case (5 x y)
  then show ?case 
    by (cases x; cases y) (auto intro: le_funI)
next
  case (6 x y)
  then show ?case 
    by (cases x; cases y) (auto intro: le_funI)
next
  case (7 x y z)
  then show ?case
    by (cases x; cases y; cases z) (auto intro!: le_funI dest: le_funD)
next
  case (8 x y)
  then show ?case 
    by (cases x; cases y) (auto intro: le_funI)
next
  case (9 y x)
  then show ?case 
    by (cases x; cases y) (auto intro: le_funI)
next
  case (10 y x z)
  then show ?case
    by (cases x; cases y; cases z) (auto intro!: le_funI dest: le_funD)
next
  case (11 x A)
  then show ?case
    by (cases x) (auto simp add: Inf_nrest_def Inf_lower)
next
  case (12 A z)
  then show ?case
    by (cases z) (fastforce simp add: Inf_nrest_def le_Inf_iff)+
next
  case (13 x A)
  then show ?case
    by (cases x) (auto simp add: Sup_nrest_def Sup_upper)
next
  case (14 A z)
  then show ?case 
    by (cases z) (fastforce simp add: Sup_nrest_def Sup_le_iff)+
next
  case 15
  then show ?case
    by (auto simp add: Inf_nrest_def top_nrest_def)
next
  case 16
  then show ?case
    by (auto simp add: Sup_nrest_def bot_nrest_def bot_option_def)
qed
end


definition "RETURNT x \<equiv> REST (\<lambda>e. if e=x then Some 0 else None)"
abbreviation "FAILT \<equiv> top::'a nrest"
abbreviation "SUCCEEDT \<equiv> bot::'a nrest"
abbreviation SPECT where "SPECT \<equiv> REST"

lemma RETURNT_alt: "RETURNT x = REST [x\<mapsto>0]"
  unfolding RETURNT_def by auto

lemma nrest_inequalities[simp]: 
  "FAILT \<noteq> REST X"
  "FAILT \<noteq> SUCCEEDT" 
  "FAILT \<noteq> RETURNT x"
  "SUCCEEDT \<noteq> FAILT"
  "SUCCEEDT \<noteq> RETURNT x"
  "REST X \<noteq> FAILT"
  "RETURNT x \<noteq> FAILT"
  "RETURNT x \<noteq> SUCCEEDT"
  unfolding top_nrest_def bot_nrest_def RETURNT_def  
  by simp_all (metis option.distinct(1))+

lemma nrest_more_simps[simp]:
  "SUCCEEDT = REST X \<longleftrightarrow> X=Map.empty" 
  "REST X = SUCCEEDT \<longleftrightarrow> X=Map.empty" 
  "REST X = RETURNT x \<longleftrightarrow> X=[x\<mapsto>0]" 
  "REST X = REST Y \<longleftrightarrow> X=Y"
  "RETURNT x = REST X \<longleftrightarrow> X=[x\<mapsto>0]"
  "RETURNT x = RETURNT y \<longleftrightarrow> x=y" 
  unfolding top_nrest_def bot_nrest_def RETURNT_def
  by (auto simp add: fun_eq_iff)

lemma nres_simp_internals: 
  "REST Map.empty = SUCCEEDT"
   "FAILi = FAILT" 
  unfolding top_nrest_def bot_nrest_def by simp_all

lemma nres_order_simps[simp]:
  "\<not> FAILT \<le> REST M" 
  "REST M \<le> REST M' \<longleftrightarrow> (M\<le>M')"
  by (auto simp: nres_simp_internals[symmetric])   

lemma nres_top_unique[simp]:" FAILT \<le> S' \<longleftrightarrow> S' = FAILT"
  by (rule top_unique) 

lemma FAILT_cases[simp]: "(case FAILT of FAILi \<Rightarrow> P | REST x \<Rightarrow> Q x) = P"
  by (auto simp: nres_simp_internals[symmetric])  

lemma nrest_Sup_FAILT: 
  "Sup X = FAILT \<longleftrightarrow> FAILT \<in> X"
  "FAILT = Sup X \<longleftrightarrow> FAILT \<in> X"
  by (auto simp: nres_simp_internals Sup_nrest_def)

lemma nrest_Sup_SPECT_D: "Sup X = SPECT m \<Longrightarrow> m x = Sup {f x | f. REST f \<in> X}"
  unfolding Sup_nrest_def by(auto split: if_splits intro!: arg_cong[where f=Sup])

declare nres_simp_internals(2)[simp]

lemma nrest_noREST_FAILT[simp]: "(\<forall>x2. m \<noteq> REST x2) \<longleftrightarrow> m=FAILT"
  by (cases m) auto

lemma no_FAILTE:  
  assumes "g xa \<noteq> FAILT" 
  obtains X where "g xa = REST X" 
  using assms by (cases "g xa") auto

lemma case_prod_refine:
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c nrest"
  assumes "\<And>a b. P a b \<le> Q a b"
  shows "(case x of (a,b) \<Rightarrow> P a b) \<le> (case x of (a,b) \<Rightarrow> Q a b)"
  using assms by (simp add: split_def)

lemma case_option_refine: (* obsolete ? *)
  fixes P Q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c nrest"
  assumes
    "PN \<le> QN"
    "\<And>a. PS a \<le> QS a"
  shows "(case x of None \<Rightarrow> PN | Some a \<Rightarrow> PS a ) \<le> (case x of None \<Rightarrow> QN | Some a \<Rightarrow> QS a )"
  using assms by (auto split: option.splits)

lemma SPECT_Map_empty[simp]: "SPECT Map.empty \<le> a" 
  by (cases a) (auto simp: le_fun_def)

lemma FAILT_SUP: "(FAILT \<in> X) \<Longrightarrow> Sup X = FAILT "
  by (simp add: nrest_Sup_FAILT)

section "pointwise reasoning"

named_theorems refine_pw_simps 
ML \<open>
  structure refine_pw_simps = Named_Thms
    ( val name = @{binding refine_pw_simps}
      val description = "Refinement Framework: " ^
        "Simplifier rules for pointwise reasoning" )
\<close>    
  
definition nofailT :: "'a nrest \<Rightarrow> bool" where "nofailT S \<equiv> S\<noteq>FAILT"

definition le_or_fail :: "'a nrest \<Rightarrow> 'a nrest \<Rightarrow> bool" (infix \<open>\<le>\<^sub>n\<close> 50) where
  "m \<le>\<^sub>n m' \<equiv> nofailT m \<longrightarrow> m \<le> m'"

lemma nofailT_simps[simp]:
  "nofailT FAILT \<longleftrightarrow> False"
  "nofailT (REST X) \<longleftrightarrow> True"
  "nofailT (RETURNT x) \<longleftrightarrow> True"
  "nofailT SUCCEEDT \<longleftrightarrow> True"
  unfolding nofailT_def
  by (simp_all add: RETURNT_def)

definition inresT :: "'a nrest \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where 
  "inresT S x t \<equiv> (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  enat t\<le>t'))"

lemma inresT_alt: "inresT S x t \<longleftrightarrow> REST ([x\<mapsto>enat t]) \<le> S"
  unfolding inresT_def by (cases S) (auto dest!: le_funD[where x=x] simp: le_funI less_eq_option_def split: option.splits)


lemma inresT_mono: "inresT S x t \<Longrightarrow> t' \<le> t \<Longrightarrow> inresT S x t'"
  unfolding inresT_def by (cases S) (auto simp add: order_subst2)

lemma inresT_RETURNT[simp]: "inresT (RETURNT x) y t \<longleftrightarrow> t = 0 \<and> y = x"
  by(auto simp: inresT_def RETURNT_def enat_0_iff split: nrest.splits)

lemma inresT_FAILT[simp]: "inresT FAILT r t"
  by(simp add: inresT_def)

lemma fail_inresT[refine_pw_simps]: "\<not> nofailT M \<Longrightarrow> inresT M x t"
  unfolding nofailT_def by simp

lemma pw_inresT_Sup[refine_pw_simps]: "inresT (Sup X) r t \<longleftrightarrow> (\<exists>M\<in>X. \<exists>t'\<ge>t.  inresT M r t')"
proof
  assume a: "inresT (Sup X) r t"
  show "(\<exists>M\<in>X. \<exists>t'\<ge>t.  inresT M r t')"
  proof(cases "Sup X")
    case FAILi
    then show ?thesis 
      by (force simp: nrest_Sup_FAILT)
  next
    case (REST Y)
    with a obtain t' where t': "Y r = Some t'" "enat t\<le>t'"
      by (auto simp add: inresT_def)
    from REST have Y: "Y = (\<Squnion> {f. SPECT f \<in> X})"
      by (auto simp add: Sup_nrest_def split: if_splits)
    with t' REST have "(\<Squnion> {f r | f . SPECT f \<in> X}) = Some t'"
      using nrest_Sup_SPECT_D by fastforce

    with t' Y obtain f t'' where f_t'': "SPECT f \<in> X" "f r = Some t''" "t' = Sup {t' | f t'. SPECT f\<in>X \<and> f r = Some t'}"
      by (auto simp add: SUP_eq_Some_iff Sup_apply[where A=" {f. SPECT f \<in> X}"]) 
    from f_t''(3) t'(2) have "enat t \<le> Sup {t' | f t'. SPECT f\<in>X \<and> f r = Some t'}" 
      by blast
    with f_t'' obtain f' t''' where "SPECT f' \<in> X" "f' r = Some t'''" "enat t \<le> t'''"
      by (smt (verit) Sup_enat_less empty_iff mem_Collect_eq option.sel)
    with REST show ?thesis 
      by (intro bexI[of _ "SPECT f'"] exI[of _ "t"]) (auto simp add: inresT_def)
  qed
next
  assume a: "(\<exists>M\<in>X. \<exists>t'\<ge>t.  inresT M r t')"
  from this obtain M t' where M_t': "M\<in>X" "t'\<ge>t" "inresT M r t'"
    by blast

  show "inresT (Sup X) r t"
  proof (cases "Sup X")
    case FAILi
    then show ?thesis 
      by (auto simp: nrest_Sup_FAILT top_Sup)
  next
    case (REST Y)
    with M_t' have "Y = \<Squnion> {f. SPECT f \<in> X}" 
      by (auto simp add: Sup_nrest_def split: if_splits)
    from REST have nf: "FAILT \<notin> X"
      using FAILT_SUP by fastforce
    with M_t' REST obtain f t'' where "SPECT f \<in> X" "f r = Some t''" "enat t' \<le> t''" 
      by (auto simp add: inresT_def split: nrest.splits)
    with REST  M_t'(2) obtain a where "Y r = Some a" "enat t \<le> a"
      by (metis Sup_upper enat_ord_simps(1) le_fun_def le_some_optE nres_order_simps(2) order_trans)
    then show ?thesis
      by (auto simp: REST inresT_def)
  qed
qed
lemma inresT_REST[simp]:
  "inresT (REST X) x t \<longleftrightarrow> (\<exists>t'\<ge>t. X x = Some t')" 
  unfolding inresT_def 
  by auto

lemma pw_Sup_nofail[refine_pw_simps]: "nofailT (Sup X) \<longleftrightarrow> (\<forall>x\<in>X. nofailT x)"
  by (cases "Sup X") (auto simp add: Sup_nrest_def nofailT_def split: if_splits)

lemma inres_simps[simp]:
  "inresT FAILT = (\<lambda>_ _. True)" 
  "inresT SUCCEEDT = (\<lambda>_ _ . False)"
  unfolding inresT_def [abs_def]
  by (auto split: nrest.splits simp add: RETURNT_def) 

lemma pw_le_iff: 
  "S \<le> S' \<longleftrightarrow> (nofailT S'\<longrightarrow> (nofailT S \<and> (\<forall>x t. inresT S x t \<longrightarrow> inresT S' x t)))"
proof (cases S; cases S')
  fix R R'
  assume a[simp]: "S=SPECT R" "S'=SPECT R'"
  show "S \<le> S' \<longleftrightarrow> (nofailT S'\<longrightarrow> (nofailT S \<and> (\<forall>x t. inresT S x t \<longrightarrow> inresT S' x t)))" (is "?l \<longleftrightarrow> ?r")
  proof (rule iffI; safe)
    assume b: "nofailT S" "\<forall>x t. inresT S x t \<longrightarrow> inresT S' x t" 
    hence b_2': "inresT S x t \<Longrightarrow> inresT S' x t" for x t
      by blast
    from b(1) have "nofailT S'"
      by auto
    with a b_2' have nf: "R x \<noteq> None \<Longrightarrow> R' x \<noteq> None" for x
      by simp (metis enat_ile nle_le not_Some_eq)
    have "R x \<le> R' x" for x
    proof (cases "R x"; cases "R' x")
      fix r r'
      assume c[simp]: "R x = Some r" "R' x = Some r'"
      show ?thesis
      proof(rule ccontr)
        assume "\<not> R x \<le> R' x"
        from this obtain vt where "inresT S x vt" "\<not>inresT S' x vt"
          by simp (metis Suc_ile_eq enat.exhaust linorder_le_less_linear order_less_irrefl)
        with b_2' show False
          by blast
      qed
    qed (use nf in \<open>auto simp add: inresT_def nofailT_def\<close>) 
    then show "S \<le> S'" 
      by (auto intro!: le_funI)
  qed(fastforce simp add: less_eq_option_def le_fun_def split: option.splits)+
qed auto

lemma RETURN_le_RETURN_iff[simp]: "RETURNT x \<le> RETURNT y \<longleftrightarrow> x=y"
  by (auto simp add: pw_le_iff)

lemma "S\<le>S' \<Longrightarrow> inresT S x t \<Longrightarrow> inresT S' x t"
  unfolding inresT_alt by auto

lemma pw_eq_iff:
  "S=S' \<longleftrightarrow> (nofailT S = nofailT S' \<and> (\<forall>x t. inresT S x t \<longleftrightarrow> inresT S' x t))"
  by (auto intro: antisym simp add: pw_le_iff)

lemma pw_flat_ge_iff: "flat_ge S S' \<longleftrightarrow> 
  (nofailT S) \<longrightarrow> nofailT S' \<and> (\<forall>x t. inresT S x t \<longleftrightarrow> inresT S' x t)"
  by (metis flat_ord_def nofailT_def pw_eq_iff)

lemma pw_eqI: 
  assumes "nofailT S = nofailT S'" 
  assumes "\<And>x t. inresT S x t \<longleftrightarrow> inresT S' x t" 
  shows "S=S'"
  using assms by (simp add: pw_eq_iff)
 
definition "consume M t \<equiv> case M of 
          FAILi \<Rightarrow> FAILT |
          REST X \<Rightarrow> REST (map_option ((+) t) o (X))"

definition "SPEC P t = REST (\<lambda>v. if P v then Some (t v) else None)"

lemma consume_mono: 
  assumes "t\<le>t'" "M \<le> M'" 
  shows "consume M t \<le> consume M' t'"
proof(cases M; cases M')
  fix m m' 
  assume a[simp]: "M=REST m" "M'=REST m'"
  from assms(2) have p: "m x \<le> m' x" for x
    by (auto dest: le_funD)
  from assms(1) have "map_option ((+) t) (m x) \<le> map_option ((+) t') (m' x)" for x
    using p[of x] by (cases "m' x"; cases "m x") (auto intro: add_mono)
  then show ?thesis
    by (auto intro: le_funI simp add: consume_def)
qed (use assms(2) in \<open>auto simp add: consume_def\<close>)

lemma nofailT_SPEC[refine_pw_simps]: "nofailT (SPEC a b)"
  unfolding SPEC_def by auto

lemma inresT_SPEC[refine_pw_simps]: "inresT (SPEC a b) = (\<lambda>x t. a x \<and>  b x \<ge> t)"
  unfolding SPEC_def inresT_REST by (auto split: if_splits)

section \<open>Monad Operators\<close>

definition bindT :: "'b nrest \<Rightarrow> ('b \<Rightarrow> 'a nrest) \<Rightarrow> 'a nrest" where
  "bindT M f \<equiv> case M of 
  FAILi \<Rightarrow> FAILT |
  REST X \<Rightarrow> Sup { (case f x of FAILi \<Rightarrow> FAILT 
                | REST m2 \<Rightarrow> REST (map_option ((+) t1) o (m2) ))
                    |x t1. X x = Some t1}"

lemma bindT_alt: "bindT M f = (case M of 
  FAILi \<Rightarrow> FAILT | 
  REST X \<Rightarrow> Sup { consume (f x) t1 |x t1. X x = Some t1})"
  unfolding bindT_def consume_def by simp

lemma "bindT (REST X) f = 
  (\<Squnion>x \<in> dom X. consume (f x) (the (X x)))"
proof -
  have *: "\<And>f X. { f x t |x t. X x = Some t}
      = (\<lambda>x. f x (the (X x))) ` (dom X)"
    by force
  show ?thesis by (auto simp: bindT_alt *)
qed

adhoc_overloading
  Monad_Syntax.bind NREST.bindT

lemma bindT_FAIL[simp]: "bindT FAILT g = FAILT"
  by (auto simp: bindT_def)       

lemma "bindT SUCCEEDT f = SUCCEEDT"
  unfolding bindT_def by (auto split: nrest.split simp add: bot_nrest_def) 

lemma "m r = Some \<infinity> \<Longrightarrow> inresT (REST m) r t"
  by auto 

lemma pw_inresT_bindT_aux: "inresT (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t \<le> t' + t''))" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI impI)
  assume ?l and "nofailT m"
  show "\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t \<le> t' + t''"
  proof(cases m)
    case [simp]: (REST X)
    with \<open>?l\<close> obtain M x t1 t' where 
      parts: "X x = Some t1"
      "(\<forall>x2. f x = SPECT x2 \<longrightarrow>
         M = SPECT (map_option ((+) t1) \<circ> x2))"
       "t'\<ge>t" "inresT M r t'"
      by (auto simp add: pw_inresT_Sup bindT_def simp flip: nrest_noREST_FAILT split: nrest.splits)

    show ?thesis
    proof(cases "f x")
      case FAILi
      show ?thesis
        by (rule exI[where x=x], cases t1) (auto intro: le_add2 simp add: FAILi parts(1))
    next
      case [simp]: (REST re)
      with parts(2) have M: "M = SPECT (map_option ((+) t1) \<circ> re)"
        by blast
      with parts(4) obtain rer where rer[simp]: "re r = Some rer"
        by auto 
      show ?thesis
      proof(rule exI[where x=x])
        from M parts(1,3,4) show "\<exists>t' t''. inresT m x t' \<and> inresT (f x) r t'' \<and> t \<le> t' + t''"
          by (cases "t1";cases rer) (fastforce intro: le_add2)+ 
      qed
    qed
  qed (use \<open>nofailT m\<close> in auto)
next
  assume "?r"
  show "?l"
  proof(cases m)
    case [simp]: (REST X)
    then show ?thesis
    proof(cases "nofailT m")
      case True
      with \<open>?r\<close> obtain t' t'' t''' r' where
        parts: "enat t' \<le> t'''"
        "X r' = Some t'''"
        "inresT (f r') r t''"
        "t \<le> t' + t''"
        by (auto simp: bindT_def split: nrest.splits)
      then show ?thesis
      proof(cases "f r'")
        case FAILi
        with parts(2) show ?thesis 
          by (fastforce simp add: pw_inresT_Sup bindT_def split: nrest.splits)
      next
        case [simp]: (REST x)
        from parts(3) obtain ta where ta: "x r = Some ta" "enat t''\<le>ta"
          by auto
        with parts True obtain tf where tf: "tf\<ge>t" "enat tf \<le> t''' + ta"
          using add_mono by fastforce
        with ta parts True show ?thesis
          by (force simp add: pw_inresT_Sup bindT_def split: nrest.splits
              intro!: exI[where x="REST (map_option ((+) t''') \<circ> x)"]) (* Witness here *)
      qed
    qed auto
  qed auto
qed

lemma pw_inresT_bindT[refine_pw_simps]: "inresT (bindT m f) r t \<longleftrightarrow>
     (nofailT m \<longrightarrow> (\<exists>r' t' t''. inresT m r' t' \<and> inresT (f r') r t'' \<and> t = t' + t''))"
  by (simp add: pw_inresT_bindT_aux) (metis add_le_imp_le_left inresT_mono le_iff_add nat_le_linear)

lemma pw_bindT_nofailT[refine_pw_simps]: "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x t. inresT M x t \<longrightarrow> nofailT (f x)))" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then show ?r
    by (force elim: no_FAILTE simp: bindT_def refine_pw_simps split: nrest.splits )  
next
  assume ?r
  hence a: "nofailT M" "\<And>x t . inresT M x t \<Longrightarrow> nofailT (f x)"
    by auto
  show ?l
  proof(cases M)
    case FAILi
    then show ?thesis
      using \<open>?r\<close> by (simp add: nofailT_def)
  next
    case [simp]: (REST m)
    with a have "f x \<noteq> FAILi" if "m x \<noteq> None" for x
      using that i0_lb by (auto simp add: nofailT_def zero_enat_def)
    then show ?thesis
      by (force simp add: bindT_def nofailT_def nrest_Sup_FAILT split: nrest.splits)
  qed
qed

lemma nat_plus_0_is_id[simp]: "((+) (0::enat)) = id" by auto

declare map_option.id[simp] 

section \<open>Monad Rules\<close>

lemma nres_bind_left_identity[simp]: "bindT (RETURNT x) f = f x"
  unfolding bindT_def RETURNT_def 
  by(auto split: nrest.split ) 

lemma nres_bind_right_identity[simp]: "bindT M RETURNT = M" 
  by(auto intro!: pw_eqI simp: refine_pw_simps) 

lemma nres_bind_assoc[simp]: "bindT (bindT M (\<lambda>x. f x)) g = bindT M (%x. bindT (f x) g)"
proof (rule pw_eqI)
  fix x t
  show "inresT (M \<bind> f \<bind> g) x t = inresT (M \<bind> (\<lambda>x. f x \<bind> g)) x t"
    by (simp add: refine_pw_simps) (use inresT_mono in \<open>fastforce\<close>)
qed (fastforce simp add: refine_pw_simps)

section \<open>Monotonicity lemmas\<close>

lemma bindT_mono: 
  "m \<le> m' \<Longrightarrow> (\<And>x. (\<exists>t. inresT m x t) \<Longrightarrow> nofailT m' \<Longrightarrow>  f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  by(fastforce simp: pw_le_iff refine_pw_simps) 

lemma bindT_mono'[refine_mono]: 
  "m \<le> m' \<Longrightarrow> (\<And>x.   f x \<le> f' x)
 \<Longrightarrow> bindT m f \<le> bindT  m' f'"
  by (erule bindT_mono)

lemma bindT_flat_mono[refine_mono]:  
  "\<lbrakk> flat_ge M M'; \<And>x. flat_ge (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_ge (bindT M f) (bindT M' f')" 
  by (fastforce simp: refine_pw_simps pw_flat_ge_iff)

subsection \<open> Derived Program Constructs \<close>

subsubsection \<open>Assertion\<close> 

definition "iASSERT ret \<Phi> \<equiv> if \<Phi> then ret () else top"

definition ASSERT where "ASSERT \<equiv> iASSERT RETURNT"

lemma ASSERT_True[simp]: "ASSERT True = RETURNT ()" 
  by (auto simp: ASSERT_def iASSERT_def)
lemma ASSERT_False[simp]: "ASSERT False = FAILT" 
  by (auto simp: ASSERT_def iASSERT_def) 

lemma bind_ASSERT_eq_if: "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAILT)"
  unfolding ASSERT_def iASSERT_def by simp

lemma pw_ASSERT[refine_pw_simps]:
  "nofailT (ASSERT \<Phi>) \<longleftrightarrow> \<Phi>"
  "inresT (ASSERT \<Phi>) x 0"
  by (cases \<Phi>, simp_all)+

lemma ASSERT_refine: "(Q \<Longrightarrow> P) \<Longrightarrow> ASSERT P \<le> ASSERT Q"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma ASSERT_leI: "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> M'"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma le_ASSERTI: "(\<Phi> \<Longrightarrow> M \<le> M') \<Longrightarrow> M \<le> ASSERT \<Phi> \<bind> (\<lambda>_. M')"
  by(auto simp: pw_le_iff refine_pw_simps)

lemma inresT_ASSERT: "inresT (ASSERT Q \<bind> (\<lambda>_. M)) x ta = (Q \<longrightarrow> inresT M x ta)"
  unfolding ASSERT_def iASSERT_def by auto

lemma nofailT_ASSERT_bind: "nofailT (ASSERT P \<bind> (\<lambda>_. M)) \<longleftrightarrow> (P \<and> nofailT M)"
  by(auto simp: pw_bindT_nofailT pw_ASSERT)

subsection \<open>SELECT\<close>

definition emb' where "\<And>Q T. emb' Q (T::'a \<Rightarrow> enat) = (\<lambda>x. if Q x then Some (T x) else None)"

abbreviation "emb Q t \<equiv> emb' Q (\<lambda>_. t)" 

lemma emb_eq_Some_conv: "\<And>T. emb' Q T x = Some t' \<longleftrightarrow> (t'=T x \<and> Q x)"
  by (auto simp: emb'_def)

lemma emb_le_Some_conv: "\<And>T. Some t' \<le> emb' Q T x \<longleftrightarrow> ( t'\<le>T x \<and> Q x)"
  by (auto simp: emb'_def)

lemma SPEC_REST_emb'_conv: "SPEC P t = REST (emb' P t)"
  unfolding SPEC_def emb'_def by auto

lemma SPECT_ub: "T\<le>T' \<Longrightarrow> SPECT (emb' M' T) \<le> SPECT (emb' M' T')"
  unfolding emb'_def by (auto simp: pw_le_iff le_funD order_trans refine_pw_simps)

text \<open>Select some value with given property, or \<open>None\<close> if there is none.\<close>  
definition SELECT :: "('a \<Rightarrow> bool) \<Rightarrow> enat \<Rightarrow> 'a option nrest"
  where "SELECT P tf \<equiv> if \<exists>x. P x then REST (emb (\<lambda>r. case r of Some p \<Rightarrow> P p | None \<Rightarrow> False) tf)
               else REST [None \<mapsto> tf]"
                    
lemma inresT_SELECT_Some: "inresT (SELECT Q tt) (Some x) t' \<longleftrightarrow> (Q x  \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 

lemma inresT_SELECT_None: "inresT (SELECT Q tt) None t' \<longleftrightarrow> (\<not>(\<exists>x. Q x) \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 

lemma inresT_SELECT[refine_pw_simps]:
 "inresT (SELECT Q tt) x t' \<longleftrightarrow> ((case x of None \<Rightarrow> \<not>(\<exists>x. Q x) | Some x \<Rightarrow> Q x)  \<and> (t' \<le> tt))"
  by(auto simp: inresT_def SELECT_def emb'_def) 


lemma nofailT_SELECT[refine_pw_simps]: "nofailT (SELECT Q tt)"
  by(auto simp: nofailT_def SELECT_def)

lemma s1: "SELECT P T \<le> (SELECT P T') \<longleftrightarrow> T \<le> T'"
  by (cases "\<exists>x. P x"; cases T; cases T')(auto simp: pw_le_iff refine_pw_simps not_le split: option.splits)
     
lemma s2: "SELECT P T \<le> (SELECT P' T) \<longleftrightarrow> (
    (Ex P' \<longrightarrow> Ex P)  \<and> (\<forall>x. P x \<longrightarrow> P' x)) "
  by (cases T) (auto simp: pw_le_iff refine_pw_simps split: option.splits)
 
lemma SELECT_refine:
  assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
  assumes "\<And>x. P x \<Longrightarrow>   P' x"
  assumes "T \<le> T'"
  shows "SELECT P T \<le> (SELECT P' T')"
proof -
  have "SELECT P T \<le> SELECT P T'"
    using s1 assms(3) by auto
  also have "\<dots> \<le> SELECT P' T'"
    unfolding s2 using assms(1,2) by auto  
  finally show ?thesis .
qed


section \<open>RECT\<close>

definition "mono2 B \<equiv> flatf_mono_ge B \<and>  mono B"


lemma trimonoD_flatf_ge: "mono2 B \<Longrightarrow> flatf_mono_ge B"
  unfolding mono2_def by auto

lemma trimonoD_mono: "mono2 B \<Longrightarrow> mono B"
  unfolding mono2_def by auto

definition "RECT B x = 
  (if mono2 B then (gfp B x) else (top::'a::complete_lattice))"

lemma RECT_flat_gfp_def: "RECT B x = 
  (if mono2 B then (flatf_gfp B x) else (top::'a::complete_lattice))"
  unfolding RECT_def
  by (auto simp: gfp_eq_flatf_gfp[OF trimonoD_flatf_ge trimonoD_mono])

lemma RECT_unfold: "\<lbrakk>mono2 B\<rbrakk> \<Longrightarrow> RECT B = B (RECT B)"
  unfolding RECT_def [abs_def]  
  by (auto dest: trimonoD_mono simp: gfp_unfold[ symmetric])


definition whileT :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "whileT b c = RECT (\<lambda>whileT s. (if b s then bindT (c s) whileT else RETURNT s))"

definition  whileIET :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "\<And>E c. whileIET I E b c = whileT b c"

definition whileTI :: "('a \<Rightarrow> enat option) \<Rightarrow> ( ('a\<times>'a) set) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nrest) \<Rightarrow> 'a \<Rightarrow> 'a nrest" where
  "whileTI I R b c s = whileT b c s"

lemma trimonoI[refine_mono]: 
  "\<lbrakk>flatf_mono_ge B; mono B\<rbrakk> \<Longrightarrow> mono2 B"
  unfolding mono2_def by auto

(* Naming *)
lemma mono_fun_transform[refine_mono]: "(\<And>f g x. (\<And>x. f x \<le> g x) \<Longrightarrow> B f x \<le> B g x) \<Longrightarrow> mono B"
  by (intro monoI le_funI) (simp add: le_funD)

lemma whileT_unfold: "whileT b c = (\<lambda>s. (if b s then bindT (c s) (whileT b c) else RETURNT s))"
  unfolding whileT_def by (rule RECT_unfold) (refine_mono)   


lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono2 B'"
  assumes LE: "\<And>F x. (B' F x) \<le> (B F x) "
  shows " (RECT B' x) \<le> (RECT B x)"
  unfolding RECT_def by simp (meson LE gfp_mono le_fun_def)  

lemma whileT_mono: 
  assumes "\<And>x. b x \<Longrightarrow> c x \<le> c' x"
  shows " (whileT b c x) \<le> (whileT b c' x)"
unfolding whileT_def proof (rule RECT_mono)
  show "(if b x then c x \<bind> F else RETURNT x) \<le> (if b x then c' x \<bind> F else RETURNT x)" for F x
    using assms by (auto intro: bindT_mono)
qed refine_mono

lemma wf_fp_induct:
  assumes fp: "\<And>x. f x = B (f) x"
  assumes wf: "wf R"
  assumes "\<And>x D. \<lbrakk>\<And>y. (y,x)\<in>R \<Longrightarrow> P y (D y)\<rbrakk> \<Longrightarrow> P x (B D x)"
  shows "P x (f x)"
  using wf
  apply induction
  apply (subst fp)
  apply fact  
  done

lemma RECT_wf_induct_aux:
  assumes wf: "wf R"
  assumes mono: "mono2 B"
  assumes "(\<And>x D. (\<And>y. (y, x) \<in> R \<Longrightarrow> P y (D y)) \<Longrightarrow> P x (B D x))"
  shows "P x (RECT B x)"
  using wf_fp_induct[where f="RECT B" and B=B] RECT_unfold assms 
     by metis 

theorem RECT_wf_induct[consumes 1]:
  assumes "RECT B x = r"
  assumes "wf R"
    and "mono2 B"
    and "\<And>x D r. (\<And>y r. (y, x) \<in> R \<Longrightarrow> D y = r \<Longrightarrow> P y r) \<Longrightarrow> B D x = r \<Longrightarrow> P x r"
  shows "P x r"
 (* using RECT_wf_induct_aux[where P = "\<lambda>x fx. \<forall>r. fx=r \<longrightarrow> P x fx"] assms by metis *)
  using RECT_wf_induct_aux[where P = "\<lambda>x fx.  P x fx"] assms by metis



definition "monadic_WHILEIT I b f s \<equiv> do {
  RECT (\<lambda>D s. do {
    ASSERT (I s);
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {RETURNT s}
  }) s
}"

section \<open>Generalized Weakest Precondition\<close>

subsection "mm"

definition mm :: "( 'a \<Rightarrow> enat option) \<Rightarrow> ( 'a \<Rightarrow> enat option) \<Rightarrow> ( 'a \<Rightarrow> enat option)" where
  "mm R m = (\<lambda>x. (case m x of None \<Rightarrow> Some \<infinity>
                                | Some mt \<Rightarrow>
                                  (case R x of None \<Rightarrow> None | Some rt \<Rightarrow> (if rt < mt then None else Some (rt - mt)))))"

lemma mm_mono: "Q1 x \<le> Q2 x \<Longrightarrow> mm Q1 M x \<le> mm Q2 M x"
  unfolding mm_def by (cases "M x") (auto split: option.splits elim!: le_some_optE intro!: helper)


lemma mm_antimono: "M1 x \<ge> M2 x \<Longrightarrow> mm Q M1 x \<le> mm Q M2 x"
  unfolding mm_def by (auto split: option.splits intro: helper2)

lemma mm_continous: "mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = Inf {u. \<exists>y. u = mm (f y) m x}" 
proof(rule antisym)
  show "mm (\<lambda>x. \<Sqinter> {u. \<exists>y. u = f y x}) m x \<le> \<Sqinter> {u. \<exists>y. u = mm (f y) m x}"
  proof (rule Inf_greatest, drule CollectD)
    fix z
    assume z: "\<exists>y. z = mm (f y) m x"
    from this obtain y where y: "z = mm (f y) m x"
      by blast

    show "mm (\<lambda>x. \<Sqinter> {u. \<exists>y. u = f y x}) m x \<le> z"
    proof (cases "Inf {u. \<exists>y. u = f y x}")
      case None
      with z show ?thesis 
        by (cases "m x") (auto simp add: mm_def None)
    next
      case Some_Inf[simp]: (Some l)
      then have i: "\<And>y. f y x \<ge> Some l"
        by (metis (mono_tags, lifting) Inf_lower mem_Collect_eq) 
      then have I: "\<And>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
        by (intro mm_mono) simp
      show ?thesis
      proof(cases "m x")
        case None
        with y show ?thesis 
          by (auto simp add: mm_def)
      next
        case [simp]: (Some a)
        with y I show ?thesis
          by (auto simp add: mm_def)
      qed
    qed
  qed
  show "\<Sqinter> {u. \<exists>y. u = mm (f y) m x} \<le> mm (\<lambda>x. \<Sqinter> {u. \<exists>y. u = f y x}) m x"
  proof(rule Inf_lower, rule CollectI)
    have "\<exists>y. Inf {u. \<exists>y. u = f y x} = f y x"
    proof (cases "Option.these {u. \<exists>y. u = f y x} = {}")
      case True
      then show ?thesis 
        by (simp add: Inf_option_def Inf_enat_def these_empty_eq) blast
    next
      case False
      then show ?thesis 
        by (auto simp add: Inf_option_def Inf_enat_def in_these_eq intro: LeastI)
    qed
    then obtain y where z: "Inf {u. \<exists>y. u = f y x} = f y x"
      by blast
    show "\<exists>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = mm (f y) m x"
      by (rule exI[where x=y]) (unfold mm_def z, rule refl)
  qed
qed

definition mm2 :: "(  enat option) \<Rightarrow> (   enat option) \<Rightarrow> (   enat option)" where
  "mm2 r m = (case m  of None \<Rightarrow> Some \<infinity>
                                | Some mt \<Rightarrow>
                                  (case r of None \<Rightarrow> None | Some rt \<Rightarrow> (if rt < mt then None else Some (rt - mt))))"


lemma mm_alt: "mm R m x = mm2 (R x) (m x)" unfolding mm_def mm2_def ..

lemma mm2_None[simp]: "mm2 q None = Some \<infinity>" unfolding mm2_def by auto

lemma mm2_Some0[simp]: "mm2 q (Some 0) = q" unfolding mm2_def by (auto split: option.splits)

lemma mm2_antimono: "x \<le> y \<Longrightarrow> mm2 q x \<ge> mm2 q y"
  unfolding mm2_def by (auto split: option.splits intro: helper2)

lemma mm2_contiuous2:
  assumes "\<forall>x\<in>X. t \<le> mm2 q x" shows "t \<le> mm2 q (Sup X)"
proof (cases q; cases "Sup X")
  fix q' assume q[simp]: "q = Some q'"
  fix S assume SupX[]: "Sup X = Some S"

  have "t \<le> (if q' < S then None else Some (q' - S))"
  proof(cases "q' < S")
    case True
    with SupX obtain x where "x \<in> Option.these X" "q' < x"
      using less_Sup_iff by (auto simp add: Sup_option_def split: if_splits)
    hence "Some x \<in> X" "q < Some x"
      by (auto simp add: in_these_eq)
    with True assms show ?thesis
      by (auto simp add: mm2_def)
  next
    case False
    with assms SupX show ?thesis
      by (cases q'; cases S) (force simp: mm2_def dest: Sup_finite_enat)+
  qed
  then show ?thesis 
    by (auto simp add: mm2_def SupX)
qed (use assms in \<open>auto simp add: mm2_def Sup_option_def split: option.splits if_splits\<close>)
 
lemma fl: "(a::enat) - b = \<infinity> \<Longrightarrow> a = \<infinity>"
  by(cases b; cases a) auto

lemma mm_inf1: "mm R m x = Some \<infinity> \<Longrightarrow> m x = None \<or> R x = Some \<infinity>"
  by (auto simp: mm_def split: option.splits if_splits intro: fl)

lemma mm_inf2: "m x = None \<Longrightarrow> mm R m x = Some \<infinity>" 
  by(auto simp: mm_def split: option.splits if_splits)  

lemma mm_inf3: " R x = Some \<infinity> \<Longrightarrow> mm R m x = Some \<infinity>" 
  by(auto simp: mm_def split: option.splits if_splits)  

lemma mm_inf: "mm R m x = Some \<infinity> \<longleftrightarrow> m x = None \<or> R x = Some \<infinity>"
  using mm_inf1 mm_inf2 mm_inf3  by metis

lemma InfQ_E: "Inf Q = Some t \<Longrightarrow> None \<notin> Q"
  unfolding Inf_option_def by auto

lemma InfQ_iff: "(\<exists>t'\<ge>enat t. Inf Q = Some t') \<longleftrightarrow> None \<notin> Q \<and> Inf (Option.these Q) \<ge> t"
  unfolding Inf_option_def 
  by auto

lemma mm2_fst_None[simp]: "mm2 None q = (case q of None \<Rightarrow> Some \<infinity> | _ \<Rightarrow> None)"
  by (cases q) (auto simp: mm2_def)


lemma mm2_auxXX1: "Some t \<le> mm2 (Q x) (Some t') \<Longrightarrow> Some t' \<le> mm2 (Q x) (Some t)"
  by (auto dest: fl simp: less_eq_enat_def mm2_def split: enat.splits option.splits if_splits)
 
subsection "mii"

definition mii :: "('a \<Rightarrow> enat option) \<Rightarrow> 'a nrest \<Rightarrow> 'a \<Rightarrow> enat option" where 
  "mii Qf M x =  (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm Qf Mf) x)"


lemma mii_alt: "mii Qf M x = (case M of FAILi \<Rightarrow> None 
                                             | REST Mf \<Rightarrow> (mm2 (Qf x) (Mf x)) )"
  unfolding mii_def mm_alt ..

lemma mii_continuous: "mii (\<lambda>x. Inf {f y x|y. True}) m x = Inf {mii (%x. f y x) m x|y. True}"
  unfolding mii_def by (cases m) (auto simp add: mm_continous)
 
lemma mii_continuous2: "(mii Q (Sup {F x t1 |x t1. P x t1}) x \<ge> t) = (\<forall>y t1. P y t1 \<longrightarrow> mii Q (F y t1) x \<ge> t)"
proof(intro iffI allI impI)
  fix y t1
  assume a: "t \<le> mii Q (\<Squnion> {F x t1 |x t1. P x t1}) x" "P y t1"
  then show "t \<le> mii Q (F y t1) x"
  proof(cases "F y t1")
    case REST_F[simp]: (REST Ff)
    then show ?thesis
    proof(cases "(\<Squnion> {F x t1 |x t1. P x t1})")
      case FAILi
      with a show ?thesis
        using a by (simp add: mii_alt less_eq_option_None_is_None')
    next
      case [simp]: (REST Sf)
      note Sf_x = nrest_Sup_SPECT_D[OF this, where x=x]
      from a(1) have "t \<le> mm2 (Q x) (Sf x)" 
        by (auto simp add: mii_alt)
      also from a(2) have "mm2 (Q x) (Sf x) \<le> mm2 (Q x) (Ff x)"
        by (intro mm2_antimono) (force intro: Sup_upper simp add: Sf_x)
      finally show ?thesis
        by (simp add: mii_alt)
    qed
  qed (auto simp: mii_alt  Sup_nrest_def split: if_splits) 
next
  assume "\<forall>y t1. P y t1 \<longrightarrow> t \<le> mii Q (F y t1) x"
  then show "t \<le> mii Q (\<Squnion> {F x t1 |x t1. P x t1}) x"
    by (auto simp: mii_alt Sup_nrest_def split: nrest.splits intro: mm2_contiuous2)
qed

lemma mii_inf: "mii Qf M x = Some \<infinity> \<longleftrightarrow> (\<exists>Mf. M = SPECT Mf \<and> (Mf x = None \<or> Qf x = Some \<infinity>))"
  by (auto simp: mii_def mm_inf split: nrest.split )

lemma miiFailt: "mii Q FAILT x = None" 
  unfolding mii_def by auto

subsection "lst - latest starting time"

definition lst :: "'a nrest \<Rightarrow> ('a \<Rightarrow> enat option) \<Rightarrow> enat option" 
  where "lst M Qf =  Inf { mii Qf M x | x. True}"

lemma T_alt_def: "lst M Qf = Inf ( (mii Qf M) ` UNIV )"
  unfolding lst_def by (simp add: full_SetCompr_eq) 


lemma T_pw: "lst M Q \<ge> t \<longleftrightarrow> (\<forall>x. mii Q M x \<ge> t)"
  by (auto simp add: T_alt_def mii_alt le_Inf_iff)

lemma T_specifies_I: 
  assumes "lst m Q \<ge> Some 0" shows "m \<le> SPECT Q"
proof (cases m)
  case [simp]: (REST q)
  from assms have "q x \<le> Q x" for x
    by (cases "q x"; cases "Q x") 
      (force simp add: T_alt_def mii_alt mm2_def le_Inf_iff split: option.splits if_splits nrest.splits)+
  then show ?thesis
    by (auto intro: le_funI)
qed (use assms in \<open>auto simp add: T_alt_def mii_alt\<close>)

lemma T_specifies_rev: 
  assumes "m \<le> SPECT Q" shows "lst m Q \<ge> Some 0" 
proof (cases m)
  case [simp]: (REST q)
  with assms have le: "q x \<le> Q x " for x
    by (auto dest: le_funD)
  show ?thesis
  proof(subst T_pw, rule allI)
    fix x
    from le[of x] show "Some 0 \<le> mii Q m x"
      by (cases "q x"; cases "Q x") (auto simp add: mii_alt mm2_def)
  qed
qed (use assms in \<open>auto simp add: T_alt_def mii_alt\<close>)

lemma T_specifies: "lst m Q \<ge> Some 0 = (m \<le> SPECT Q)"
  using T_specifies_I T_specifies_rev by metis

lemma pointwise_lesseq:
  fixes x :: "'a::order"
  shows "(\<forall>t. x \<ge> t \<longrightarrow> x' \<ge> t) \<Longrightarrow> x \<le> x'"
  by simp

subsection "pointwise reasoning about lst via nres3"


definition nres3 where "nres3 Q M x t \<longleftrightarrow> mii Q M x \<ge> t"


lemma pw_T_le:
  assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
  shows "lst  M Q \<le> lst  M' Q'"
  apply(rule pointwise_lesseq)
  using assms unfolding T_pw nres3_def by metis 

lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) = (\<forall>x. nres3 Q' M' x t)" 
  shows pw_T_eq_iff: "lst M Q  = lst M' Q'"
  apply (rule antisym)
   apply(rule pw_T_le) using assms apply metis
  apply(rule pw_T_le) using assms apply metis
  done 

lemma assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
      "\<And>t. (\<forall>x. nres3 Q' M' x t) \<Longrightarrow> (\<forall>x. nres3 Q M x t)"
  shows pw_T_eqI: "lst M Q = lst M' Q'"
  apply (rule antisym)
   apply(rule pw_T_le) 
   apply fact
  apply(rule pw_T_le) 
  apply fact 
  done 

lemma lem: "\<forall>t1. M y = Some t1 \<longrightarrow> t \<le> mii Q (SPECT (map_option ((+) t1) \<circ> x2)) x \<Longrightarrow> f y = SPECT x2 \<Longrightarrow> t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y"
proof(cases "M y"; cases t)
  fix m' t'
  assume a: "\<forall>t1. M y = Some t1 \<longrightarrow> t \<le> mii Q (SPECT (map_option ((+) t1) \<circ> x2)) x" "f y = SPECT x2"
  assume c[simp]: "M y = Some m'" "t = Some t'"

  from a c show "t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y"
  proof (cases "x2 x"; cases "Q x")
    fix x2' Q' 
    assume c'[simp]: "x2 x = Some x2'" "Q x = Some Q'"
    from a c show ?thesis 
      by (cases m'; cases x2'; cases Q') (auto split: option.splits if_splits simp add: add.commute mii_def mm_def)
  qed (auto split: option.splits if_splits simp add: add.commute mii_def mm_def)
qed(auto simp add: mii_def mm_def)

(* TODO Move *)
lemma diff_diff_add_enat:"a - (b+c) = a - b - (c::enat)" 
  by (cases a; cases b; cases c) auto


lemma lem2: "t \<le> mii (\<lambda>y. mii Q (f y) x) (SPECT M) y \<Longrightarrow> M y = Some t1 \<Longrightarrow> f y = SPECT fF \<Longrightarrow> t \<le> mii Q (SPECT (map_option ((+) t1) \<circ> fF)) x"
  by (cases "fF x"; cases "Q x"; cases t)  (auto simp add: mii_def mm_def enat_plus_minus_aux2
      add.commute linorder_not_less diff_diff_add_enat split: if_splits)

lemma fixes m :: "'b nrest"
  shows mii_bindT: "(t \<le> mii Q (bindT m f) x) \<longleftrightarrow> (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y)"
proof -
  { fix M
    assume mM: "m = SPECT M"
    let ?P = "%x t1. M x = Some t1"
    let ?F = "%x t1. case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (map_option ((+) t1) \<circ> m2)"
    let ?Sup = "(Sup {?F x t1 |x t1. ?P x t1})" 

    { fix y 
      have 1: "mii (\<lambda>y. mii Q (f y) x) (SPECT M) y = None" if "f y = FAILT" "M y \<noteq> None"
        using that by (auto simp add: mii_def mm_def less_eq_option_None_is_None' )
      have "(\<forall>t1. ?P y t1 \<longrightarrow> mii Q (?F y t1) x \<ge> t)
              = (t \<le> mii (\<lambda>y. mii Q (f y) x) m y)"
        by (cases "f y") (auto intro: lem lem2 meta_le_everything_if_top simp add: 1 mM miiFailt mii_inf 
            top_enat_def top_option_def less_eq_option_None_is_None')
    } note h=this


    from mM have "mii Q (bindT m f) x = mii Q ?Sup x" by (auto simp: bindT_def)
    then have "(t \<le> mii Q (bindT m f) x) = (t \<le> mii Q ?Sup x)" by simp
    also have "\<dots> = (\<forall>y t1. ?P y t1 \<longrightarrow> mii Q (?F y t1) x \<ge> t)" by (rule mii_continuous2)  
    also have "\<dots> = (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y)" by (simp only: h)
    finally have ?thesis .
  } note bl=this

  show ?thesis
  proof(cases m)
    case FAILi
    then show ?thesis 
      by (simp add: mii_def)
  next
    case (REST x2)
    then show ?thesis
      by (rule bl)
  qed
qed


lemma nres3_bindT: "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>y. nres3 (\<lambda>y. lst (f y) Q) m y t)"
proof -
  have t: "\<And>f and t::enat option. (\<forall>y. t \<le> f y) \<longleftrightarrow> (t\<le>Inf {f y|y. True})"  
    using le_Inf_iff by fastforce   

  have "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>x.  t \<le> mii Q (bindT m f) x)" unfolding nres3_def by auto
  also have "\<dots> = (\<forall>x. (\<forall>y. t \<le> mii (\<lambda>y. mii Q (f y) x) m y))" by(simp only: mii_bindT)
  also have "\<dots> = (\<forall>y. (\<forall>x. t \<le> mii (\<lambda>y. mii Q (f y) x) m y))" by blast
  also have "\<dots> = (\<forall>y.  t \<le> mii (\<lambda>y. Inf {mii Q (f y) x|x. True}) m y)"
    using t by (fastforce simp only: mii_continuous)
  also have "\<dots> = (\<forall>y.  t \<le> mii (\<lambda>y. lst (f y) Q) m y)" unfolding lst_def by auto
  also have "\<dots> = (\<forall>y. nres3 (\<lambda>y. lst (f y) Q) m y t)" unfolding nres3_def by auto
  finally show ?thesis .
  have "(\<forall>y.  t \<le> mii (\<lambda>y. lst (f y) Q) m y) = (t \<le> Inf{ mii (\<lambda>y. lst (f y) Q) m y|y. True})" using t by metis
qed


subsection "rules for lst"

lemma T_bindT: "lst (bindT M f) Q  = lst M (\<lambda>y. lst (f y) Q)"
  by (rule pw_T_eq_iff, rule nres3_bindT) 

lemma T_REST: "lst (REST [x\<mapsto>t]) Q = mm2 (Q x) (Some t)"
proof- 
  have *: "Inf {uu. \<exists>xa. (xa = x \<longrightarrow> uu= v) \<and> (xa \<noteq> x \<longrightarrow> uu = Some \<infinity>)} = v"  (is "Inf ?S = v") for v :: "enat option"
  proof -
    have "?S \<in> { {v} \<union> {Some \<infinity>}, {v}  }" by auto 
    then show ?thesis 
      by safe (simp_all add: top_enat_def[symmetric] top_option_def[symmetric] ) 
  qed
  then show ?thesis
    unfolding lst_def mii_alt by auto
qed


lemma T_RETURNT: "lst (RETURNT x) Q = Q x"
  unfolding RETURNT_alt by (rule trans, rule T_REST) simp
             
lemma T_SELECT: 
  assumes  
    "\<forall>x. \<not> P x \<Longrightarrow> Some tt \<le> lst (SPECT [None \<mapsto> tf]) Q"
  and p: "(\<And>x. P x \<Longrightarrow> Some tt \<le> lst (SPECT [Some x \<mapsto> tf]) Q)"
  shows "Some tt \<le> lst (SELECT P tf) Q"
proof(cases "\<exists>x. P x")
  case True
  from p[unfolded T_pw mii_alt] have
    p': "\<And>y x. P y \<Longrightarrow> Some tt \<le> mm2 (Q x) ([Some y \<mapsto> tf] x)"
    by auto
  hence p'': "\<And>y x. P y \<Longrightarrow> x=Some y \<Longrightarrow> Some tt \<le> mm2 (Q x) (Some tf)"
    by (metis fun_upd_same)
  with True show ?thesis
    by (auto simp: SELECT_def emb'_def T_pw mii_alt split: if_splits option.splits)
next
  case False
  with assms show ?thesis 
    by (auto simp: SELECT_def)
qed 



section \<open>consequence rules\<close>
   
lemma aux1: "Some t \<le> mm2 Q (Some t') \<longleftrightarrow> Some (t+t') \<le> Q"
proof (cases t; cases t'; cases Q) 
  fix n n' t''
  assume a[simp]: "t = enat n" "t' = enat n'" "Q = Some t''"
  show ?thesis
    by (cases t'') (auto simp: mm2_def)
qed (auto simp: mm2_def elim: less_enatE split: option.splits)

lemma aux1a: "(\<forall>x t''. Q' x = Some t'' \<longrightarrow> (Q x) \<ge> Some (t + t''))
      = (\<forall>x. mm2 (Q x) (Q' x) \<ge> Some t)"
proof(intro iffI allI impI)
  fix x
  assume a: "\<forall>x t''. Q' x = Some t'' \<longrightarrow> Some (t + t'') \<le> Q x"
  then show "Some t \<le> mm2 (Q x) (Q' x)"
    by (cases "Q' x") (simp_all add: aux1)
next
  fix x t''
  assume a: "\<forall>x. Some t \<le> mm2 (Q x) (Q' x)" "Q' x = Some t''"
  then show "Some (t + t'') \<le> Q x"
    using aux1 by metis
qed

lemma T_conseq4:
  assumes 
    "lst f Q' \<ge> Some t'"
    "\<And>x t'' M. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" 
  shows "lst f Q  \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t' \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t''. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" by auto
    from i ii have "Some t \<le> mii Q f x"
    proof (cases f)
      case [simp]: (REST Mf)
      then show ?thesis
      proof(cases "Mf x")
        case [simp]: (Some a)
        have arith: "t' + a \<le> b \<Longrightarrow> t - t' + b \<le> b' \<Longrightarrow> t + a \<le> b'" for b b'
          by (cases t; cases t'; cases a; cases b; cases b') auto
        with i ii show ?thesis
          by (cases "Q' x"; cases "Q x") (auto simp add: mii_alt aux1)
      qed (auto simp add: mii_alt)
    qed (auto simp add: mii_alt)
  } 
  thus ?thesis
    unfolding T_pw ..
qed

lemma T_conseq6:
  assumes 
    "lst f Q' \<ge> Some t"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')" 
  shows "lst f Q \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t'' M.  f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')"
      by auto
    from i ii have "Some t \<le> mii Q f x"
    proof (cases f)
      case [simp]: (REST Mf)
      then show ?thesis
      proof(cases "Mf x")
        case [simp]: (Some a)
        with i ii show ?thesis
          by (cases "Q' x"; cases "Q x") (fastforce simp add: mii_alt aux1)+
      qed (auto simp add: mii_alt)
    qed (auto simp add: mii_alt)
  } 
  thus ?thesis
    unfolding T_pw ..
qed



lemma T_conseq6':
  assumes 
    "lst f Q' \<ge> Some t"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow>   (Q x) \<ge> Q' x" 
  shows "lst f Q \<ge> Some t"
  by (rule T_conseq6) (auto intro: assms(1) dest: assms(2))

lemma T_conseq5:
  assumes 
    "lst f Q' \<ge> Some t'"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" 
  shows "lst f Q \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded T_pw] have i: "Some t' \<le> mii Q' f x" by auto
    from assms(2) have ii: "\<And>t'' M.  f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" by auto
    from i ii have "Some t \<le> mii Q f x"
    
    proof (cases f)
      case [simp]: (REST Mf)
      then show ?thesis
      proof(cases "Mf x")
        case [simp]: (Some a)
        have arith: "t' + a \<le> b \<Longrightarrow> t - t' + b \<le> b' \<Longrightarrow> t + a \<le> b'" for b b' 
          by (cases a; cases b; cases b'; cases t; cases t') auto
        with i ii show ?thesis
          by (cases "Q' x"; cases "Q x") (fastforce simp add: mii_alt aux1)+
      qed (auto simp add: mii_alt)
    qed (auto simp add: mii_alt)
  } 
  thus ?thesis
    unfolding T_pw ..
qed

lemma T_conseq3: 
  assumes 
    "lst f Q' \<ge> Some t'"
    "\<And>x. mm2 (Q x) (Q' x) \<ge> Some (t - t')" 
  shows "lst f Q \<ge> Some t"
  using assms T_conseq4 aux1a by metis
             
section "Experimental Hoare reasoning"

named_theorems vcg_rules

method vcg uses rls = ((rule rls vcg_rules[THEN T_conseq4] | clarsimp simp: emb_eq_Some_conv emb_le_Some_conv T_bindT T_RETURNT)+)

experiment
begin

definition P where "P f g = bindT f (\<lambda>x. bindT g (\<lambda>y. RETURNT (x+(y::nat))))"

lemma assumes
  f_spec[vcg_rules]: "lst f ( emb' (\<lambda>x. x > 2) (enat o ((*) 2)) ) \<ge> Some 0"
and 
  g_spec[vcg_rules]: "lst g ( emb' (\<lambda>x. x > 2) (enat) ) \<ge> Some 0"
shows "lst (P f g) ( emb' (\<lambda>x. x > 5) (enat o (*) 3) ) \<ge> Some 0"
proof -
  have ?thesis
    unfolding P_def by vcg

  have ?thesis
    unfolding P_def
    apply(simp add: T_bindT )
    apply(simp add: T_RETURNT)
    apply(rule T_conseq4[OF f_spec])
    apply(clarsimp simp: emb_eq_Some_conv)
    apply(rule T_conseq4[OF g_spec])
    apply (clarsimp simp: emb_eq_Some_conv emb_le_Some_conv)
    done
  thus ?thesis .
qed
end


section \<open>VCG\<close>

named_theorems vcg_simp_rules
lemmas [vcg_simp_rules] = T_RETURNT

lemma TbindT_I: "Some t \<le>  lst M (\<lambda>y. lst (f y) Q) \<Longrightarrow>  Some t \<le> lst (M \<bind> f) Q"
  by(simp add: T_bindT)

method vcg' uses rls = ((rule rls TbindT_I vcg_rules[THEN T_conseq6] | clarsimp split: if_splits simp:  vcg_simp_rules)+)

lemma mm2_refl: "A < \<infinity> \<Longrightarrow> mm2 (Some A) (Some A) = Some 0"
  unfolding mm2_def by auto
 
definition mm3 where
  "mm3 t A = (case A of None \<Rightarrow> None | Some t' \<Rightarrow> if t'\<le>t then Some (enat (t-t')) else None)"

lemma mm3_same[simp]: "mm3 t0 (Some t0) = Some 0"  by (auto simp: mm3_def zero_enat_def)

lemma mm3_Some_conv: "(mm3 t0 A = Some t) = (\<exists>t'. A = Some t' \<and> t0 \<ge> t' \<and> t=t0-t')"
  unfolding mm3_def by(auto split: option.splits)

lemma mm3_None[simp]: "mm3 t0 None = None" unfolding mm3_def by auto

lemma T_FAILT[simp]: "lst FAILT Q = None"
  unfolding lst_def mii_alt by simp

definition "progress m \<equiv> \<forall>s' M. m = SPECT M \<longrightarrow> M s' \<noteq> None \<longrightarrow> M s' > Some 0"
lemma progressD: "progress m \<Longrightarrow> m=SPECT M \<Longrightarrow> M s' \<noteq> None \<Longrightarrow> M s' > Some 0"
  by (auto simp: progress_def)

lemma progress_FAILT[simp]: "progress FAILT" by(auto simp: progress_def)

subsection \<open>Progress rules\<close>

named_theorems progress_rules

lemma progress_SELECT_iff: "progress (SELECT P t) \<longleftrightarrow> t > 0"
  unfolding progress_def SELECT_def emb'_def by (auto split: option.splits)

lemmas [progress_rules] = progress_SELECT_iff[THEN iffD2]

lemma progress_REST_iff: "progress (REST [x \<mapsto> t]) \<longleftrightarrow> t>0"
  by (auto simp: progress_def)

lemmas [progress_rules] = progress_REST_iff[THEN iffD2]

lemma progress_ASSERT_bind[progress_rules]: "\<lbrakk>\<Phi> \<Longrightarrow> progress (f ()) \<rbrakk> \<Longrightarrow> progress (ASSERT \<Phi>\<bind>f)"
  by (cases \<Phi>) (auto simp: progress_def)

lemma progress_SPECT_emb[progress_rules]: "t > 0 \<Longrightarrow> progress (SPECT (emb P t))" by(auto simp: progress_def emb'_def)

lemma Sup_Some: "Sup (S::enat option set) = Some e \<Longrightarrow> \<exists>x\<in>S. (\<exists>i. x = Some i)"
  unfolding Sup_option_def by (auto split: if_splits)

lemma progress_bind[progress_rules]: assumes "progress m \<or> (\<forall>x. progress (f x))"
  shows "progress (m\<bind>f)"
proof (cases m)
  case FAILi
  then show ?thesis by (auto simp: progress_def)
next
  case (REST x2)   
  then show ?thesis unfolding bindT_def progress_def
  proof (safe, goal_cases)
    case (1 s' M y)
    let ?P = "\<lambda>fa. \<exists>x. f x \<noteq> FAILT \<and>
             (\<exists>t1. \<forall>x2a. f x = SPECT x2a \<longrightarrow> fa = map_option ((+) t1) \<circ> x2a \<and> x2 x = Some t1)"
    from 1 have A: "Sup {fa s' |fa. ?P fa} = Some y"
      by (auto dest: nrest_Sup_SPECT_D[where x=s'] split: nrest.splits)
    from Sup_Some[OF this] obtain fa i where P: "?P fa" and 3: "fa s' = Some i"   by blast 
    then obtain x t1 x2a  where  a3: "f x = SPECT x2a"
      and "\<forall>x2a. f x = SPECT x2a \<longrightarrow> fa = map_option ((+) t1) \<circ> x2a" and a2: "x2 x = Some t1"  
      by fastforce 
    then have a1: " fa = map_option ((+) t1) \<circ> x2a" by auto
    have "progress m \<Longrightarrow> t1 > 0" 
      by (drule progressD) (use 1(1) a2 a1 a3 in auto)  
    moreover
    have "progress (f x) \<Longrightarrow> x2a s' > Some 0"  
      using a1 1(1) a2 3 by (auto dest!: progressD[OF _ a3])   
    ultimately
    have " t1 > 0 \<or> x2a s' > Some 0" using assms by auto

    then have "Some 0 < fa s'" using   a1  3 by auto
    also have "\<dots> \<le> Sup {fa s'|fa. ?P fa}" 
      by (rule Sup_upper) (blast intro: P)
    also have "\<dots> = M s'" using A 1(3) by simp
    finally show ?case .
  qed 
qed

lemma mm2SomeleSome_conv: "mm2 (Qf) (Some t) \<ge> Some 0 \<longleftrightarrow> Qf \<ge> Some t"
  unfolding mm2_def  by (auto split: option.split)                              

section "rules for whileT"

lemma
  assumes "whileT b c s = r"
  assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' \<Longrightarrow> b s 
           \<Longrightarrow>    lst (c s) (\<lambda>s'. if (s',s)\<in>R then I s' else None) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes "I s = Some t"
  assumes wf: "wf R"
  shows whileT_rule'': "lst r (\<lambda>x. if b x then None else I x) \<ge> Some t"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH[vcg_rules] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems show ?case 
    by simp vcg'      
qed

lemma
  fixes I :: "'a \<Rightarrow> nat option"
  assumes "whileT b c s0 = r"
  assumes progress: "\<And>s. progress (c s)" 
  assumes IS[vcg_rules]: "\<And>s t t'. I s = Some t \<Longrightarrow>  b s  \<Longrightarrow> 
           lst (c s) (\<lambda>s'. mm3 t (I s') ) \<ge> Some 0"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes [simp]: "I s0 = Some t0" 
    (*  assumes wf: "wf R" *)                         
  shows whileT_rule''': "lst r (\<lambda>x. if b x then None else mm3 t0 (I x)) \<ge> Some 0"  
  apply(rule T_conseq4)
   apply(rule whileT_rule''[where I="\<lambda>s. mm3 t0 (I s)"
        and R="measure (the_enat o the o I)", OF assms(1)])
  subgoal for s t'
    apply(cases "I s"; simp)
    subgoal for ti
      using IS[of s ti]  
      apply (cases "c s"; simp) 
      subgoal for M
        \<comment> \<open>TODO\<close>
        using progress[of s, THEN progressD, of M]
        apply(auto simp: T_pw mm3_Some_conv mii_alt mm2_def mm3_def split: option.splits if_splits)
            apply fastforce 
           apply (metis enat_ord_simps(1) le_diff_iff le_less_trans option.distinct(1)) 
          apply (metis diff_is_0_eq' leI less_option_Some option.simps(3) zero_enat_def) 
         apply (smt Nat.add_diff_assoc enat_ile enat_ord_code(1) idiff_enat_enat leI 
                le_add_diff_inverse2 nat_le_iff_add option.simps(3)) 
        using dual_order.trans by blast 
      done
    done
  by auto

lemma whileIET_rule[THEN T_conseq6, vcg_rules]:
  fixes E
  assumes 
    "(\<And>s t t'.
    (if I s then Some (E s) else None) = Some t \<Longrightarrow>
    b s \<Longrightarrow> Some 0 \<le> lst (C s) (\<lambda>s'. mm3 t (if I s' then Some (E s') else None)))" 
  "\<And>s. progress (C s)"
  "I s0" 
shows "Some 0 \<le> lst (whileIET I E b C s0) (\<lambda>x. if b x then None else mm3 (E s0) (if I x then Some (E x) else None))"
  unfolding whileIET_def  
  apply(rule whileT_rule'''[OF refl, where I="(\<lambda>e. if I e
                then Some (E e) else None)"])
  using assms by auto 

 

lemma transf:
  assumes "I s \<Longrightarrow>  b s \<Longrightarrow> Some 0 \<le> lst (C s) (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None))" 
  shows "
    (if I s then Some (E s) else None) = Some t \<Longrightarrow>
    b s \<Longrightarrow> Some 0 \<le> lst (C s) (\<lambda>s'. mm3 t (if I s' then Some (E s') else None))"
  using assms by (cases "I s") auto

lemma whileIET_rule':
  fixes E
  assumes 
    "(\<And>s t t'. I s \<Longrightarrow>  b s \<Longrightarrow> Some 0 \<le> lst (C s) (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)))" 
  "\<And>s. progress (C s)"
  "I s0" 
shows "Some 0 \<le> lst (whileIET I E b C s0) (\<lambda>x. if b x then None else mm3 (E s0) (if I x then Some (E x) else None))" 
  by (rule whileIET_rule, rule transf[where b=b]) (use assms in auto)

section "some Monadic Refinement Automation"


ML \<open>
structure Refine = struct

  structure vcg = Named_Thms
    ( val name = @{binding refine_vcg}
      val description = "Refinement Framework: " ^ 
        "Verification condition generation rules (intro)" )

  structure vcg_cons = Named_Thms
    ( val name = @{binding refine_vcg_cons}
      val description = "Refinement Framework: " ^
        "Consequence rules tried by VCG" )

  structure refine0 = Named_Thms
    ( val name = @{binding refine0}
      val description = "Refinement Framework: " ^
        "Refinement rules applied first (intro)" )

  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )

  structure refine2 = Named_Thms
    ( val name = @{binding refine2}
      val description = "Refinement Framework: " ^
        "Refinement rules 2nd stage (intro)" )

  (* If set to true, the product splitter of refine_rcg is disabled. *)
  val no_prod_split = 
    Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

  fun rcg_tac add_thms ctxt = 
    let 
      val cons_thms = vcg_cons.get ctxt
      val ref_thms = (refine0.get ctxt 
        @ add_thms @ refine.get ctxt @ refine2.get ctxt);
      val prod_ss = (Splitter.add_split @{thm prod.split} 
        (put_simpset HOL_basic_ss ctxt));
      val prod_simp_tac = 
        if Config.get ctxt no_prod_split then 
          K no_tac
        else
          (simp_tac prod_ss THEN' 
            REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}));
    in
      REPEAT_ALL_NEW_FWD (DETERM o FIRST' [
        resolve_tac ctxt ref_thms,
        resolve_tac ctxt cons_thms THEN' resolve_tac ctxt ref_thms,
        prod_simp_tac
      ])
    end;

  fun post_tac ctxt = REPEAT_ALL_NEW_FWD (FIRST' [
    eq_assume_tac,
    (*match_tac ctxt thms,*)
    SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
         

end;
\<close>
setup \<open>Refine.vcg.setup\<close>
setup \<open>Refine.vcg_cons.setup\<close>
setup \<open>Refine.refine0.setup\<close>
setup \<open>Refine.refine.setup\<close>
setup \<open>Refine.refine2.setup\<close>
(*setup {* Refine.refine_post.setup *}*)

method_setup refine_rcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac add_thms ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement conditions"     

method_setup refine_vcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac (add_thms @ Refine.vcg.get ctxt) ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement and verification conditions"

end
