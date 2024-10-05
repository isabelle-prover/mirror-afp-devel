(*<*)
theory Formula
  imports Trace
begin
(*>*)

section \<open>Metric First-Order Temporal Logic\<close>

subsection \<open>Syntax\<close>

type_synonym ('n, 'a) event = "('n \<times> 'a list)"
type_synonym ('n, 'a) database = "('n, 'a) event set"
type_synonym ('n, 'a) prefix = "('n \<times> 'a list) prefix"
type_synonym ('n, 'a) trace = "('n \<times> 'a list) trace"
type_synonym ('n, 'a) env = "'n \<Rightarrow> 'a"
type_synonym ('n, 'a) envset = "'n \<Rightarrow> 'a set"

datatype (fv_trm: 'n, 'a) trm = is_Var: Var 'n (\<open>\<^bold>v\<close>) | is_Const: Const 'a (\<open>\<^bold>c\<close>)

lemma in_fv_trm_conv: "x \<in> fv_trm t \<longleftrightarrow> t = \<^bold>v x"
  by (cases t) auto

datatype ('n, 'a) formula = 
  TT                                            (\<open>\<top>\<close>)
| FF                                            (\<open>\<bottom>\<close>)
| Eq_Const 'n 'a                                (\<open>_ \<^bold>\<approx> _\<close> [85, 85] 85)
| Pred 'n "('n, 'a) trm list"                   (\<open>_ \<dagger> _\<close> [85, 85] 85)
| Neg "('n, 'a) formula"                        (\<open>\<not>\<^sub>F _\<close> [82] 82)
| Or "('n, 'a) formula" "('n, 'a) formula"      (infixr \<open>\<or>\<^sub>F\<close> 80)
| And "('n, 'a) formula" "('n, 'a) formula"     (infixr \<open>\<and>\<^sub>F\<close> 80)
| Imp "('n, 'a) formula" "('n, 'a) formula"     (infixr \<open>\<longrightarrow>\<^sub>F\<close> 79)
| Iff "('n, 'a) formula" "('n, 'a) formula"     (infixr \<open>\<longleftrightarrow>\<^sub>F\<close> 79)
| Exists "'n" "('n, 'a) formula"                (\<open>\<exists>\<^sub>F_. _\<close> [70,70] 70)
| Forall "'n" "('n, 'a) formula"                (\<open>\<forall>\<^sub>F_. _\<close> [70,70] 70)
| Prev \<I> "('n, 'a) formula"                     (\<open>\<^bold>Y _ _\<close> [1000, 65] 65)
| Next \<I> "('n, 'a) formula"                     (\<open>\<^bold>X _ _\<close> [1000, 65] 65)
| Once \<I> "('n, 'a) formula"                     (\<open>\<^bold>P _ _\<close> [1000, 65] 65)
| Historically \<I> "('n, 'a) formula"             (\<open>\<^bold>H _ _\<close> [1000, 65] 65)
| Eventually \<I> "('n, 'a) formula"               (\<open>\<^bold>F _ _\<close> [1000, 65] 65)
| Always \<I> "('n, 'a) formula"                   (\<open>\<^bold>G _ _\<close> [1000, 65] 65)
| Since "('n, 'a) formula" \<I> "('n, 'a) formula" (\<open>_ \<^bold>S _ _\<close> [60,1000,60] 60)
| Until "('n, 'a) formula" \<I> "('n, 'a) formula" (\<open>_ \<^bold>U _ _\<close> [60,1000,60] 60)

primrec fv :: "('n, 'a) formula \<Rightarrow> 'n set" where
  "fv (r \<dagger> ts) = \<Union> (fv_trm ` set ts)"
| "fv \<top> = {}"
| "fv \<bottom> = {}"
| "fv (x \<^bold>\<approx> c) = {x}"
| "fv (\<not>\<^sub>F \<phi>) = fv \<phi>"
| "fv (\<phi> \<or>\<^sub>F \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (\<phi> \<and>\<^sub>F \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (\<phi> \<longrightarrow>\<^sub>F \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (\<phi> \<longleftrightarrow>\<^sub>F \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (\<exists>\<^sub>Fx. \<phi>) = fv \<phi> - {x}"
| "fv (\<forall>\<^sub>Fx. \<phi>) = fv \<phi> - {x}"
| "fv (\<^bold>Y I \<phi>) = fv \<phi>"
| "fv (\<^bold>X I \<phi>) = fv \<phi>"
| "fv (\<^bold>P I \<phi>) = fv \<phi>"
| "fv (\<^bold>H I \<phi>) = fv \<phi>"
| "fv (\<^bold>F I \<phi>) = fv \<phi>"
| "fv (\<^bold>G I \<phi>) = fv \<phi>"
| "fv (\<phi> \<^bold>S I \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (\<phi> \<^bold>U I \<psi>) = fv \<phi> \<union> fv \<psi>"

primrec "consts" :: "('n, 'a) formula \<Rightarrow> 'a set" where
  "consts (r \<dagger> ts) = {}" \<comment> \<open>terms may also contain constants,
     but these only filter out values from the trace and do not introduce
     new values of interest (i.e., do not extend the active domain)\<close>
| "consts \<top> = {}"
| "consts \<bottom> = {}"
| "consts (x \<^bold>\<approx> c) = {c}"
| "consts (\<not>\<^sub>F \<phi>) = consts \<phi>"
| "consts (\<phi> \<or>\<^sub>F \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (\<phi> \<and>\<^sub>F \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (\<phi> \<longrightarrow>\<^sub>F \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (\<phi> \<longleftrightarrow>\<^sub>F \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (\<exists>\<^sub>Fx. \<phi>) = consts \<phi>"
| "consts (\<forall>\<^sub>Fx. \<phi>) = consts \<phi>"
| "consts (\<^bold>Y I \<phi>) = consts \<phi>"
| "consts (\<^bold>X I \<phi>) = consts \<phi>"
| "consts (\<^bold>P I \<phi>) = consts \<phi>"
| "consts (\<^bold>H I \<phi>) = consts \<phi>"
| "consts (\<^bold>F I \<phi>) = consts \<phi>"
| "consts (\<^bold>G I \<phi>) = consts \<phi>"
| "consts (\<phi> \<^bold>S I \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (\<phi> \<^bold>U I \<psi>) = consts \<phi> \<union> consts \<psi>"

lemma finite_fv_trm[simp]: "finite (fv_trm t)"
  by (cases t) simp_all

lemma finite_fv[simp]: "finite (fv \<phi>)"
  by (induction \<phi>) simp_all

lemma finite_consts[simp]: "finite (consts \<phi>)"
  by (induction \<phi>) simp_all

definition nfv :: "('n, 'a) formula \<Rightarrow> nat" where
  "nfv \<phi> = card (fv \<phi>)"

fun future_bounded :: "('n, 'a) formula \<Rightarrow> bool" where
  "future_bounded \<top> = True"
| "future_bounded \<bottom> = True"
| "future_bounded (_ \<dagger> _) = True"
| "future_bounded (_ \<^bold>\<approx> _) = True"
| "future_bounded (\<not>\<^sub>F \<phi>) = future_bounded \<phi>"
| "future_bounded (\<phi> \<or>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<and>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<longrightarrow>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<longleftrightarrow>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<exists>\<^sub>F_. \<phi>) = future_bounded \<phi>"
| "future_bounded (\<forall>\<^sub>F_. \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>Y I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>X I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>P I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>H I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>F I \<phi>) = (future_bounded \<phi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (\<^bold>G I \<phi>) = (future_bounded \<phi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (\<phi> \<^bold>S I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<^bold>U I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> right I \<noteq> \<infinity>)"

subsection \<open>Semantics\<close>

primrec eval_trm :: "('n, 'a) env \<Rightarrow> ('n, 'a) trm \<Rightarrow> 'a"(\<open>_\<lbrakk>_\<rbrakk>\<close> [70,89] 89) where
  "eval_trm v (\<^bold>v x) = v x"
| "eval_trm v (\<^bold>c x) = x"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v x = v' x \<Longrightarrow> v\<lbrakk>t\<rbrakk> = v'\<lbrakk>t\<rbrakk>"
  by (induction t) simp_all

definition eval_trms :: "('n, 'a) env \<Rightarrow> ('n, 'a) trm list \<Rightarrow> 'a list" (\<open>_\<^bold>\<lbrakk>_\<^bold>\<rbrakk>\<close> [70,89] 89) where
  "eval_trms v ts = map (eval_trm v) ts"

lemma eval_trms_fv_cong: 
  "\<forall>t\<in>set ts. \<forall>x\<in>fv_trm t. v x = v' x \<Longrightarrow> v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk> = v'\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>"
  using eval_trm_fv_cong[of _ v v']
  by (auto simp: eval_trms_def)

(* vs :: "'a envset" is used whenever we define executable functions *)
primrec eval_trm_set :: "('n, 'a) envset \<Rightarrow> ('n, 'a) trm \<Rightarrow> ('n, 'a) trm \<times> 'a set"(\<open>_\<lbrace>_\<rbrace>\<close> [70,89] 89) where
  "eval_trm_set vs (\<^bold>v x) = (\<^bold>v x, vs x)"
| "eval_trm_set vs (\<^bold>c x) = (\<^bold>c x, {x})"

definition eval_trms_set :: "('n, 'a) envset \<Rightarrow> ('n, 'a) trm list \<Rightarrow> (('n, 'a) trm \<times> 'a set) list" (\<open>_\<^bold>\<lbrace>_\<^bold>\<rbrace>\<close> [70,89] 89)
  where "eval_trms_set vs ts = map (eval_trm_set vs) ts"

lemma eval_trms_set_Nil: "vs\<^bold>\<lbrace>[]\<^bold>\<rbrace> = []"
  by (simp add: eval_trms_set_def)

lemma eval_trms_set_Cons: 
  "vs\<^bold>\<lbrace>(t # ts)\<^bold>\<rbrace> = vs\<lbrace>t\<rbrace> # vs\<^bold>\<lbrace>ts\<^bold>\<rbrace>"
  by (simp add: eval_trms_set_def)

primrec sat :: "('n, 'a) trace \<Rightarrow> ('n, 'a) env \<Rightarrow> nat \<Rightarrow> ('n, 'a) formula \<Rightarrow> bool" (\<open>\<langle>_, _, _\<rangle> \<Turnstile> _\<close> [56, 56, 56, 56] 55) where
  "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<top> = True"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<bottom> = False"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> r \<dagger> ts = ((r, v\<^bold>\<lbrakk>ts\<^bold>\<rbrakk>) \<in> \<Gamma> \<sigma> i)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> x \<^bold>\<approx> c = (v x = c)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<not>\<^sub>F \<phi> = (\<not> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<or>\<^sub>F \<psi> = (\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<or> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<psi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<and>\<^sub>F \<psi> = (\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<psi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<longrightarrow>\<^sub>F \<psi> = (\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<psi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<longleftrightarrow>\<^sub>F \<psi> = (\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<longleftrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<psi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<exists>\<^sub>Fx. \<phi> = (\<exists>z. \<langle>\<sigma>, v(x := z), i\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<forall>\<^sub>Fx. \<phi> = (\<forall>z. \<langle>\<sigma>, v(x := z), i\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>Y I \<phi> = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>X I \<phi> = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> \<langle>\<sigma>, v, Suc i\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>P I \<phi> = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>H I \<phi> = (\<forall>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<longrightarrow> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>F I \<phi> = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>G I \<phi> = (\<forall>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<longrightarrow> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<phi>)"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi> = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi> \<and> (\<forall>k\<in>{j<..i}. \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi>))"
| "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>U I \<psi> = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> \<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi> \<and> (\<forall>k\<in>{i..<j}. \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi>))"

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v x = v' x \<Longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> = \<langle>\<sigma>, v', i\<rangle> \<Turnstile> \<phi>"
proof (induct \<phi> arbitrary: v v' i)
  case (Pred n ts)
  thus ?case
    by (simp cong: map_cong eval_trms_fv_cong[rule_format, OF Pred[simplified, rule_format]] 
        split: option.splits)
next
  case (Exists t \<phi>)
  then show ?case unfolding sat.simps 
    by (intro iff_exI) (simp add: nth_Cons')
next
  case (Forall t \<phi>)
  then show ?case unfolding sat.simps 
    by (intro iff_allI) (simp add: nth_Cons')
qed (auto 10 0 simp: Let_def split: nat.splits intro!: iff_exI eval_trm_fv_cong)

lemma sat_Until_rec: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>U I \<psi> \<longleftrightarrow>
  (mem 0 I \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<psi> \<or>
   \<Delta> \<sigma> (i + 1) \<le> right I \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<and> \<langle>\<sigma>, v, i + 1\<rangle> \<Turnstile> \<phi> \<^bold>U (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>" "\<forall>k \<in> {i ..< j}. \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "\<Delta> \<sigma> (i + 1) \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>" by auto
    moreover from False j have "\<langle>\<sigma>, v, i + 1\<rangle> \<Turnstile> \<phi> \<^bold>U (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "\<Delta> \<sigma> (i + 1) \<le> right I" and now: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>" and
   "next": "\<langle>\<sigma>, v, i + 1\<rangle> \<Turnstile> \<phi> \<^bold>U (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>"
  from "next" obtain j where j: "i + 1 \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1)) (subtract (\<Delta> \<sigma> (i + 1)) I)"
      "\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>" "\<forall>k \<in> {i + 1 ..< j}. \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi>"
    by auto
  from \<Delta> j(1,2) have "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi> \<longleftrightarrow>
  mem 0 I \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<psi> \<or>
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<and> \<langle>\<sigma>, v, i - 1\<rangle> \<Turnstile> \<phi> \<^bold>S (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>" "\<forall>k \<in> {j <.. i}. \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "\<Delta> \<sigma> i \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>" by auto
    moreover from False j have "\<langle>\<sigma>, v, i - 1\<rangle> \<Turnstile> \<phi> \<^bold>S (subtract (\<Delta> \<sigma> i) I) \<psi>"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "\<Delta> \<sigma> i \<le> right I" and now: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>" and
   "prev": "\<langle>\<sigma>, v, i - 1\<rangle> \<Turnstile> \<phi> \<^bold>S (subtract (\<Delta> \<sigma> i) I) \<psi>"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) ((subtract (\<Delta> \<sigma> i) I))"
      "\<langle>\<sigma>, v, j\<rangle> \<Turnstile> \<psi>" "\<forall>k \<in> {j <.. i - 1}. \<langle>\<sigma>, v, k\<rangle> \<Turnstile> \<phi>"
    by auto
  from \<Delta> i j(1,2) have "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_Since_0: "\<langle>\<sigma>, v, 0\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi> \<longleftrightarrow> mem 0 I \<and> \<langle>\<sigma>, v, 0\<rangle> \<Turnstile> \<psi>"
  by auto

lemma sat_Since_point: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi> \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S (point t) \<psi> \<Longrightarrow> mem t I \<Longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<^bold>S I \<psi>"
  by auto

lemma sat_Once_Since: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>P I \<phi> = \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<top> \<^bold>S I \<phi>"
  by auto

lemma sat_Once_rec: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>P I \<phi> \<longleftrightarrow>
  mem 0 I \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<or> 
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> \<langle>\<sigma>, v, i - 1\<rangle> \<Turnstile> \<^bold>P (subtract (\<Delta> \<sigma> i) I) \<phi>)"
  unfolding sat_Once_Since
  by (subst sat_Since_rec) auto

lemma sat_Historically_Once: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>H I \<phi> = \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<not>\<^sub>F (\<^bold>P I \<not>\<^sub>F \<phi>)"
  by auto

lemma sat_Historically_rec: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>H I \<phi> \<longleftrightarrow>
  (mem 0 I \<longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>) \<and> 
  (i > 0 \<longrightarrow> \<Delta> \<sigma> i \<le> right I \<longrightarrow> \<langle>\<sigma>, v, i - 1\<rangle> \<Turnstile> \<^bold>H (subtract (\<Delta> \<sigma> i) I) \<phi>)"
  unfolding sat_Historically_Once sat.simps(5)
  by (subst sat_Once_rec) auto

lemma sat_Eventually_Until: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>F I \<phi> = \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<top> \<^bold>U I \<phi>"
  by auto

lemma sat_Eventually_rec: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>F I \<phi> \<longleftrightarrow>
  mem 0 I \<and> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi> \<or> 
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> \<langle>\<sigma>, v, i + 1\<rangle> \<Turnstile> \<^bold>F (subtract (\<Delta> \<sigma> (i + 1)) I) \<phi>)"
  unfolding sat_Eventually_Until
  by (subst sat_Until_rec) auto

lemma sat_Always_Eventually: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>G I \<phi> = \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<not>\<^sub>F (\<^bold>F I \<not>\<^sub>F \<phi>)"
  by auto

lemma sat_Always_rec: "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>G I \<phi> \<longleftrightarrow>
  (mem 0 I \<longrightarrow> \<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<phi>) \<and> 
  (\<Delta> \<sigma> (i + 1) \<le> right I \<longrightarrow> \<langle>\<sigma>, v, i + 1\<rangle> \<Turnstile> \<^bold>G (subtract (\<Delta> \<sigma> (i + 1)) I) \<phi>)"
  unfolding sat_Always_Eventually sat.simps(5)
  by (subst sat_Eventually_rec) auto

bundle MFOTL_syntax
begin

text \<open> For bold font, type ``backslash'' followed by the word ``bold''  \<close>
notation Var (\<open>\<^bold>v\<close>)
     and Const (\<open>\<^bold>c\<close>)

text \<open> For subscripts type ``backslash'' followed by ``sub''  \<close>
notation TT (\<open>\<top>\<close>)
     and FF (\<open>\<bottom>\<close>)
     and Pred (\<open>_ \<dagger> _\<close> [85, 85] 85)
     and Eq_Const (\<open>_ \<^bold>\<approx> _\<close> [85, 85] 85)
     and Neg (\<open>\<not>\<^sub>F _\<close> [82] 82)
     and And (infixr \<open>\<and>\<^sub>F\<close> 80)
     and Or (infixr \<open>\<or>\<^sub>F\<close> 80)
     and Imp (infixr \<open>\<longrightarrow>\<^sub>F\<close> 79)
     and Iff (infixr \<open>\<longleftrightarrow>\<^sub>F\<close> 79)
     and Exists (\<open>\<exists>\<^sub>F_. _\<close> [70,70] 70)
     and Forall (\<open>\<forall>\<^sub>F_. _\<close> [70,70] 70)
     and Prev (\<open>\<^bold>Y _ _\<close> [1000, 65] 65)
     and Next (\<open>\<^bold>X _ _\<close> [1000, 65] 65)
     and Once (\<open>\<^bold>P _ _\<close> [1000, 65] 65)
     and Eventually (\<open>\<^bold>F _ _\<close> [1000, 65] 65)
     and Historically (\<open>\<^bold>H _ _\<close> [1000, 65] 65)
     and Always (\<open>\<^bold>G _ _\<close> [1000, 65] 65)
     and Since (\<open>_ \<^bold>S _ _\<close> [60,1000,60] 60)
     and Until (\<open>_ \<^bold>U _ _\<close> [60,1000,60] 60)

notation eval_trm (\<open>_\<lbrakk>_\<rbrakk>\<close> [70,89] 89)
     and eval_trms (\<open>_\<^bold>\<lbrakk>_\<^bold>\<rbrakk>\<close> [70,89] 89)
     and eval_trm_set (\<open>_\<lbrace>_\<rbrace>\<close> [70,89] 89)
     and eval_trms_set (\<open>_\<^bold>\<lbrace>_\<^bold>\<rbrace>\<close> [70,89] 89)
     and sat (\<open>\<langle>_, _, _\<rangle> \<Turnstile> _\<close> [56, 56, 56, 56] 55)
     and Interval.interval (\<open>\<^bold>[_,_\<^bold>]\<close>)

end

unbundle no MFOTL_syntax

(*<*)
end
(*>*)