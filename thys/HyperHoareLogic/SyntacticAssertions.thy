section \<open>Syntactic Assertions\<close>

theory SyntacticAssertions
  imports Logic Loops ProgramHyperproperties Compositionality
begin

subsection \<open>Preliminaries: Types, expressions, 'a assertions\<close>

type_synonym var = nat
type_synonym qstate = nat
type_synonym qvar = nat

type_synonym 'a nstate = "(var, 'a, var, 'a) state"
type_synonym 'a npstate = "(var, 'a) pstate"

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"
type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> bool"

text \<open>Quantified variables and quantified states are represented as de Bruijn indices (natural numbers).\<close>

datatype 'a exp =
  EPVar qstate var    \<comment>\<open>\<open>\<phi>\<^sup>P(x)\<close>: Program variable\<close>
  | ELVar qstate var  \<comment>\<open>\<open>\<phi>\<^sup>L(x)\<close>: Logical variable\<close>
  | EQVar qvar        \<comment>\<open>\<open>y\<close>: Quantified variable\<close>
  | EConst 'a
  | EBinop "'a exp" "'a binop" "'a exp" \<comment>\<open>\<open>e \<oplus> e\<close>\<close>
  | EFun "'a \<Rightarrow> 'a" "'a exp"            \<comment>\<open>\<open>f(e)\<close>\<close>

text \<open>Quantified variables and quantified states are represented as de Bruijn indices (natural numbers).
Thus, quantifiers do not have a name for the variable or state they quantify over.\<close>

datatype 'a assertion =
  AConst bool
  | AComp "'a exp" "'a comp" "'a exp"  \<comment>\<open>\<open>e \<succeq> e\<close>\<close>
  | AForallState "'a assertion"        \<comment>\<open>\<open>\<forall><\<phi>>. A\<close>\<close>
  | AExistsState "'a assertion"        \<comment>\<open>\<open>\<exists><\<phi>>. A\<close>\<close>
  | AForall "'a assertion"             \<comment>\<open>\<open>\<forall>y. A\<close>\<close>
  | AExists "'a assertion"             \<comment>\<open>\<open>\<exists>y. A\<close>\<close>
  | AOr "'a assertion" "'a assertion"  \<comment>\<open>\<open>A \<or> A\<close>\<close>
  | AAnd "'a assertion" "'a assertion" \<comment>\<open>\<open>A \<and> A\<close>\<close>

text \<open>We use a list of values and a list of states to track quantified values and states, respectively.\<close>

fun interp_exp :: "'a list \<Rightarrow> 'a nstate list \<Rightarrow> 'a exp \<Rightarrow> 'a" where
  "interp_exp vals states (EPVar st x) = snd (states ! st) x"
| "interp_exp vals states (ELVar st x) = fst (states ! st) x"
| "interp_exp vals states (EQVar x) = vals ! x"
| "interp_exp vals states (EConst v) = v"
| "interp_exp vals states (EBinop e1 op e2) = op (interp_exp vals states e1) (interp_exp vals states e2)"
| "interp_exp vals states (EFun f e) = f (interp_exp vals states e)"

fun sat_assertion :: "'a list \<Rightarrow> 'a nstate list \<Rightarrow> 'a assertion \<Rightarrow> 'a nstate set \<Rightarrow> bool" where
  "sat_assertion vals states (AConst b) _ \<longleftrightarrow> b"
| "sat_assertion vals states (AComp e1 cmp e2) _ \<longleftrightarrow> cmp (interp_exp vals states e1) (interp_exp vals states e2)"
| "sat_assertion vals states (AForallState A) S \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # states) A S)"
| "sat_assertion vals states (AExistsState A) S \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # states) A S)"
| "sat_assertion vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A S)"
| "sat_assertion vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A S)"
| "sat_assertion vals states (AAnd A B) S \<longleftrightarrow> (sat_assertion vals states A S \<and> sat_assertion vals states B S)"
| "sat_assertion vals states (AOr A B) S \<longleftrightarrow> (sat_assertion vals states A S \<or> sat_assertion vals states B S)"

text \<open>Negation and implication are defined on top of this base language.\<close>

definition neg_cmp :: "'a comp \<Rightarrow> 'a comp" where
  "neg_cmp cmp v1 v2 \<longleftrightarrow> \<not> (cmp v1 v2)"

fun ANot where
  "ANot (AConst b) = AConst (\<not> b)"
| "ANot (AComp e1 cmp e2) = AComp e1 (neg_cmp cmp) e2"
| "ANot (AForallState A) = AExistsState (ANot A)"
| "ANot (AExistsState A) = AForallState (ANot A)"
| "ANot (AOr A B) = AAnd (ANot A) (ANot B)"
| "ANot (AAnd A B) = AOr (ANot A) (ANot B)"
| "ANot (AForall A) = AExists (ANot A)"
| "ANot (AExists A) = AForall (ANot A)"

definition AImp where
  "AImp A B = AOr (ANot A) B"

lemma sat_assertion_Not:
  "sat_assertion vals states (ANot A) S \<longleftrightarrow> \<not>(sat_assertion vals states A S)"
  by (induct A arbitrary: vals states) (simp_all add: neg_cmp_def)

lemma sat_assertion_Imp:
  "sat_assertion vals states (AImp A B) S \<longleftrightarrow> (sat_assertion vals states A S \<longrightarrow> sat_assertion vals states B S)"
  by (simp add: AImp_def sat_assertion_Not)

abbreviation interp_assert where "interp_assert \<equiv> sat_assertion [] []"


subsection \<open>Assume rule\<close>

fun transform_assume :: "'a assertion \<Rightarrow> 'a assertion \<Rightarrow> 'a assertion" where
  "transform_assume _ (AConst b) = AConst b"
| "transform_assume _ (AComp e1 cmp e2) = AComp e1 cmp e2"
| "transform_assume b (AForallState A) = AForallState (AImp b (transform_assume b A))"
| "transform_assume b (AExistsState A) = AExistsState (AAnd b (transform_assume b A))"
| "transform_assume b (AForall A) = AForall (transform_assume b A)"
| "transform_assume b (AExists A) = AExists (transform_assume b A)"
| "transform_assume b (AAnd A B) = AAnd (transform_assume b A) (transform_assume b B)"
| "transform_assume b (AOr A B) = AOr (transform_assume b A) (transform_assume b B)"


definition same_syn_sem :: "'a assertion \<Rightarrow> ('a npstate \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "same_syn_sem bsyn bsem \<longleftrightarrow>
  (\<forall>states vals S. length states > 0 \<longrightarrow> bsem (snd (hd states)) = sat_assertion vals states bsyn S)"

lemma same_syn_semI:
  assumes "\<And>states vals S. length states > 0 \<Longrightarrow> bsem (snd (hd states)) \<longleftrightarrow> sat_assertion vals states bsyn S"
  shows "same_syn_sem bsyn bsem"
  by (simp add: assms same_syn_sem_def)

lemma transform_assume_valid:
  assumes "same_syn_sem bsyn bsem"
  shows "sat_assertion vals states A (Set.filter (bsem \<circ> snd) S)
  \<longleftrightarrow> sat_assertion vals states (transform_assume bsyn A) S"
proof (induct A arbitrary: vals states)
  case (AForallState A)
  let ?S = "Set.filter (bsem \<circ> snd) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AForallState A) ?S \<longleftrightarrow> (\<forall>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) ?A S)"
    using AForallState by presburger
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. bsem (snd \<phi>) \<longrightarrow> sat_assertion vals (\<phi> # states) ?A S)"
    by fastforce
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # states) bsyn S \<longrightarrow> sat_assertion vals (\<phi> # states) ?A S)"
    using assms same_syn_sem_def[of bsyn bsem] by auto
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # states) (AImp bsyn ?A) S)"
    using sat_assertion_Imp by fast
  also have "... \<longleftrightarrow> sat_assertion vals states (AForallState (AImp bsyn ?A)) S"
    using sat_assertion.simps(2) by force
  finally show ?case
    using transform_assume.simps(1) by fastforce
next
  case (AExistsState A)
  let ?S = "Set.filter (bsem \<circ> snd) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AExistsState A) ?S \<longleftrightarrow> (\<exists>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) ?A S)"
    using AExistsState by presburger
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. bsem (snd \<phi>) \<and> sat_assertion vals (\<phi> # states) ?A S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # states) bsyn S \<and> sat_assertion vals (\<phi> # states) ?A S)"
    using assms same_syn_sem_def[of bsyn bsem] by auto
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # states) (AAnd bsyn ?A) S)"
    by simp
  also have "... \<longleftrightarrow> sat_assertion vals states (AExistsState (AAnd bsyn ?A)) S"
    using sat_assertion.simps(3) by force
  then show ?case
    using calculation transform_assume.simps(2) by fastforce
next
  case (AForall A)
  let ?S = "Set.filter (bsem \<circ> snd) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AForall A) ?S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states ?A S)"
    using AForall by presburger
  also have "... \<longleftrightarrow> sat_assertion vals states (AForall ?A) S"
    by simp
  then show ?case
    using calculation transform_assume.simps(3) by fastforce
next
  case (AExists A)
  let ?S = "Set.filter (bsem \<circ> snd) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AExists A) ?S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states ?A S)"
    using AExists by presburger
  also have "... \<longleftrightarrow> sat_assertion vals states (AExists ?A) S"
    by simp
  then show ?case
    using calculation transform_assume.simps(4) by fastforce
qed (simp_all)



subsubsection \<open>Program expressions (values)\<close>

datatype 'a pexp =
  PVar var \<comment>\<open>Normal variable, like x\<close>
  | PConst 'a
  | PBinop "'a pexp" "'a binop" "'a pexp"
  | PFun "'a \<Rightarrow> 'a" "'a pexp"


fun interp_pexp :: "'a pexp \<Rightarrow> 'a npstate \<Rightarrow> 'a"
  where
  "interp_pexp (PVar x) \<phi> = \<phi> x"
| "interp_pexp (PConst n) _ = n"
| "interp_pexp (PBinop p1 op p2) \<phi> = op (interp_pexp p1 \<phi>) (interp_pexp p2 \<phi>)"
| "interp_pexp (PFun f p) \<phi> = f (interp_pexp p \<phi>)"

fun pexp_to_exp where
  "pexp_to_exp st (PVar x) = EPVar st x"
| "pexp_to_exp _ (PConst n) = EConst n"
| "pexp_to_exp st (PBinop p1 op p2) = EBinop (pexp_to_exp st p1) op (pexp_to_exp st p2)"
| "pexp_to_exp st (PFun f p) = EFun f (pexp_to_exp st p)"

lemma same_syn_sem_exp:
  "interp_pexp p (snd (states ! st)) = interp_exp vals states (pexp_to_exp st p)"
proof (induct p)
  case (PVar x)
  then show ?case
    using hd_conv_nth by force
qed (simp_all)


subsubsection \<open>Program expressions (booleans)\<close>

datatype 'a pbexp =
  PBConst bool
  | PBAnd "'a pbexp" "'a pbexp"
  | PBOr "'a pbexp" "'a pbexp"
  | PBComp "'a pexp" "'a comp" "'a pexp"

fun interp_pbexp :: "'a pbexp \<Rightarrow> 'a npstate \<Rightarrow> bool"
  where
  "interp_pbexp (PBConst b) _ \<longleftrightarrow> b"
| "interp_pbexp (PBAnd pb1 pb2) \<phi> \<longleftrightarrow> interp_pbexp pb1 \<phi> \<and> interp_pbexp pb2 \<phi>"
| "interp_pbexp (PBOr pb1 pb2) \<phi> \<longleftrightarrow> interp_pbexp pb1 \<phi> \<or> interp_pbexp pb2 \<phi>"
| "interp_pbexp (PBComp p1 cmp p2) \<phi> \<longleftrightarrow> cmp (interp_pexp p1 \<phi>) (interp_pexp p2 \<phi>)"

fun pbexp_to_assertion where
  "pbexp_to_assertion _ (PBConst b) = AConst b"
| "pbexp_to_assertion st (PBAnd pb1 pb2) = AAnd (pbexp_to_assertion st pb1) (pbexp_to_assertion st pb2)"
| "pbexp_to_assertion st (PBOr pb1 pb2) = AOr (pbexp_to_assertion st pb1) (pbexp_to_assertion st pb2)"
| "pbexp_to_assertion st (PBComp p1 cmp p2) = AComp (pexp_to_exp st p1) cmp (pexp_to_exp st p2)"

lemma same_syn_sem_assertion:
  "interp_pbexp pb (snd (states ! st)) = sat_assertion vals states (pbexp_to_assertion st pb) S"
proof (induct pb)
  case (PBComp x1 x2 x3)
  then show ?case
    by (metis interp_pbexp.simps(4) pbexp_to_assertion.simps(4) same_syn_sem_exp sat_assertion.simps(2))
qed (simp_all)

lemma pexp_to_exp_same:
  shows "same_syn_sem (pbexp_to_assertion 0 pb) (interp_pbexp pb)"
proof (rule same_syn_semI)
  fix states :: "'a nstate list"
  fix vals S
  assume "0 < length states"
  then have "sat_assertion vals states (pbexp_to_assertion 0 pb) S = sat_assertion [] states (pbexp_to_assertion 0 pb) S"
    using same_syn_sem_assertion by blast
  then show "interp_pbexp pb (snd (hd states)) = sat_assertion vals states (pbexp_to_assertion 0 pb) S"
    by (metis \<open>0 < length states\<close> hd_conv_nth length_greater_0_conv same_syn_sem_assertion)
qed



subsubsection \<open>Syntactic rule for assume\<close>

theorem rule_assume_syntactic_general:
  "\<Turnstile> { sat_assertion states vals (transform_assume (pbexp_to_assertion 0 pb) P) } Assume (interp_pbexp pb) {sat_assertion states vals P}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "sat_assertion states vals (transform_assume (pbexp_to_assertion 0 pb) P) S"
  then have "sat_assertion states vals P (Set.filter (interp_pbexp pb \<circ> snd) S)"
    using pexp_to_exp_same transform_assume_valid by blast
  then show "sat_assertion states vals P (sem (Assume (interp_pbexp pb)) S)"
    by (simp add: assume_sem)
qed

theorem rule_assume_syntactic:
  "\<Turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 pb) P) } Assume (interp_pbexp pb) {interp_assert P}"
  by (simp add: rule_assume_syntactic_general)



subsection \<open>Havoc rule\<close>

subsubsection \<open>Shifting variables\<close>

fun insert_at where
  "insert_at 0 x l = x # l"
| "insert_at (Suc n) x (t # q) = t # (insert_at n x q)"
| "insert_at (Suc n) x [] = [x]"

lemma length_insert_at:
  "length (insert_at n x l) = length l + 1"
proof (induct n arbitrary: l)
  case (Suc n)
  then show ?case
  proof (cases l)
    case (Cons t q)
    then show ?thesis
      by (simp add: Suc)
  qed (simp)
qed (simp_all)


lemma insert_at_charact_1:
  "n \<le> length l \<Longrightarrow> k < n \<Longrightarrow> (insert_at n x l) ! k = l ! k"
proof (induct k arbitrary: l n)
  case 0
  then show ?case
    by (metis bot_nat_0.not_eq_extremum insert_at.elims le_zero_eq list.size(3) nth_Cons_0)
next
  case (Suc k)
  then obtain nn t q where "n = Suc nn" "l = t # q"
    by (metis Suc_less_eq2 le_antisym list.exhaust list.size(3) not_less_zero zero_le)
  then show ?case
    using Suc.hyps Suc.prems(1) Suc.prems(2) by force
qed

lemma insert_at_charact_2:
  "n  \<le> length l \<Longrightarrow> (insert_at n x l) ! n = x"
proof (induct n arbitrary: l)
  case (Suc n)
  then show ?case
    by (metis Suc_le_length_iff insert_at.simps(2) nth_Cons_Suc)
qed (simp)

lemma insert_at_charact_3:
  "n  \<le> length l \<Longrightarrow> k \<ge> n \<Longrightarrow> (insert_at n x l) ! (Suc k) = l ! k"
proof (induct n arbitrary: l k)
  case (Suc xa)
  then obtain t q kk where "k = Suc kk" "l = t # q"
    by (meson Suc_le_D Suc_le_length_iff)
  then show ?case
    using Suc.hyps Suc.prems(1) Suc.prems(2) by auto
qed (simp)


(* Shift only stuff above *)
fun shift_vars_exp where
  "shift_vars_exp n (EQVar x) = (if x \<ge> n then EQVar (Suc x) else EQVar x)"
| "shift_vars_exp n (EBinop e1 op e2) = EBinop (shift_vars_exp n e1) op (shift_vars_exp n e2)"
| "shift_vars_exp n (EFun p e) = EFun p (shift_vars_exp n e)"
| "shift_vars_exp _ e = e"

fun shift_states_exp where
  "shift_states_exp n (EPVar \<phi> x) = (if \<phi> \<ge> n then EPVar (Suc \<phi>) x else EPVar \<phi> x)"
| "shift_states_exp n (ELVar \<phi> x) = (if \<phi> \<ge> n then ELVar (Suc \<phi>) x else ELVar \<phi> x)"
| "shift_states_exp n (EBinop e1 op e2) = EBinop (shift_states_exp n e1) op (shift_states_exp n e2)"
| "shift_states_exp n (EFun p e) = EFun p (shift_states_exp n e)"
| "shift_states_exp _ e = e"

fun wf_exp :: "nat \<Rightarrow> nat \<Rightarrow> 'a exp \<Rightarrow> bool" where
  "wf_exp nv ns (EPVar st _) \<longleftrightarrow> st < ns"
| "wf_exp nv ns (ELVar st _) \<longleftrightarrow> st < ns"
| "wf_exp nv ns (EQVar x) \<longleftrightarrow> x < nv"
| "wf_exp nv ns (EBinop e1 _ e2) \<longleftrightarrow> wf_exp nv ns e1 \<and> wf_exp nv ns e2"
| "wf_exp nv ns (EFun f e) \<longleftrightarrow> wf_exp nv ns e"
| "wf_exp nv ns (EConst _) \<longleftrightarrow> True"

lemma wf_shift_vars_exp:
  assumes "wf_exp nv ns e"
  shows "wf_exp (Suc nv) ns (shift_vars_exp n e)"
  using assms
  by (induct e) simp_all

lemma wf_shift_states_exp:
  assumes "wf_exp nv ns e"
  shows "wf_exp nv (Suc ns) (shift_states_exp n e)"
  using assms
  by (induct e) simp_all

lemma shift_vars_exp_charact:
  assumes "n \<le> length vals"
  shows "interp_exp vals states e = interp_exp (insert_at n v vals) states (shift_vars_exp n e)"
  using assms
proof (induct e)
  case (EQVar x)
  then show ?case
    by (simp add: insert_at_charact_1 insert_at_charact_3)
qed (simp_all)

lemma shift_states_exp_charact:
  assumes "n \<le> length states"
  shows "interp_exp vals states e = interp_exp vals (insert_at n \<phi> states) (shift_states_exp n e)"
  using assms
proof (induct e)
  case (EPVar x1 x2)
  then show ?case
    by (simp add: insert_at_charact_1 insert_at_charact_3)
next
  case (ELVar x1 x2)
  then show ?case
    by (simp add: insert_at_charact_1 insert_at_charact_3)
qed (simp_all)


fun shift_vars where
  "shift_vars n (AConst b) = AConst b"
| "shift_vars n (AComp e1 cmp e2) = AComp (shift_vars_exp n e1) cmp (shift_vars_exp n e2)"
| "shift_vars n (AForall A) = AForall (shift_vars (Suc n) A)"
| "shift_vars n (AExists A) = AExists (shift_vars (Suc n) A)"
| "shift_vars n (AForallState A) = AForallState (shift_vars n A)"
| "shift_vars n (AExistsState A) = AExistsState (shift_vars n A)"
| "shift_vars n (AOr A B) = AOr (shift_vars n A) (shift_vars n B)"
| "shift_vars n (AAnd A B) = AAnd (shift_vars n A) (shift_vars n B)"

lemma shift_vars_charact:
  assumes "n \<le> length vals"
  shows "sat_assertion vals states A S \<longleftrightarrow> sat_assertion (insert_at n x vals) states (shift_vars n A) S"
  using assms
proof (induct A arbitrary: vals states n)
  case (AComp x1a x2 x3a)
  then show ?case
    using shift_vars_exp_charact by fastforce
next
  case (AForall A)
  have "sat_assertion vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (insert_at (Suc n) x (v # vals)) states (shift_vars (Suc n) A) S)"
    using AForall(2) AForall(1)[of "Suc n" _ states] by simp
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # insert_at n x vals) states (shift_vars (Suc n) A) S)"
    by simp
  also have "... \<longleftrightarrow> sat_assertion (insert_at n x vals) states (AForall (shift_vars (Suc n) A)) S"
    by simp
  then show "sat_assertion vals states (AForall A) S = sat_assertion (insert_at n x vals) states (shift_vars n (AForall A)) S"
    using calculation by simp
next
  case (AExists A)
  have "sat_assertion vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (insert_at (Suc n) x (v # vals)) states (shift_vars (Suc n) A) S)"
    using AExists(2) AExists(1)[of "Suc n" _ states] by simp
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # insert_at n x vals) states (shift_vars (Suc n) A) S)"
    by simp
  also have "... \<longleftrightarrow> sat_assertion (insert_at n x vals) states (AExists (shift_vars (Suc n) A)) S"
    by simp
  then show "sat_assertion vals states (AExists A) S = sat_assertion (insert_at n x vals) states (shift_vars n (AExists A)) S"
    using calculation by simp
qed (simp_all)



subsubsection \<open>Expressions (Boolean and values)\<close>

definition update_state where
  "update_state \<phi> x v = (fst \<phi>, (snd \<phi>)(x := v))"


(* Replacing \<phi>(x) by v *)
(* for havoc, should be used with (EQVar v) *)
fun subst_exp_single :: "qstate \<Rightarrow> var \<Rightarrow> 'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a exp" where
  "subst_exp_single \<phi> x e' (EPVar st y) = (if \<phi> = st \<and> x = y then e' else EPVar st y)"
| "subst_exp_single \<phi> x e' (EBinop e1 bop e2) = EBinop (subst_exp_single \<phi> x e' e1) bop (subst_exp_single \<phi> x e' e2)"
| "subst_exp_single \<phi> x e' (EFun f e) = EFun f (subst_exp_single \<phi> x e' e)"
| "subst_exp_single _ _ _ e = e" (* Logical variables, quantified variables, constants *)

lemma wf_subst_exp:
  assumes "wf_exp nv ns e"
      and "wf_exp nv ns e'"
    shows "wf_exp nv ns (subst_exp_single \<phi> x e' e)"
  using assms
  by (induct e) simp_all



lemma subst_exp_single_charact:
  assumes "interp_exp vals states e' = snd (states ! st) x"
  shows "interp_exp vals states (subst_exp_single st x e' e) = interp_exp vals states e"
  using assms
  by (induct e) simp_all


definition subst_state where
  "subst_state x pe \<phi> = (fst \<phi>, (snd \<phi>)(x := interp_pexp pe (snd \<phi>)))"

definition update_state_at where
  "update_state_at states n x v = list_update states n (update_state (states ! n) x v)"

lemma update_state_at_fst:
  "fst (update_state_at states n x v ! st) = fst (states ! st)"
proof (cases "n = st")
  case True
  then show ?thesis
    by (metis fst_conv linorder_not_less list_update_beyond nth_list_update_eq update_state_at_def update_state_def)
next
  case False
  then show ?thesis
    by (simp add: update_state_at_def)
qed

lemma update_state_at_snd_1:
  "x \<noteq> y \<Longrightarrow> snd (update_state_at states n x v ! st) y = snd (states ! st) y"
  apply (cases "n = st")
   apply (metis fun_upd_other linorder_not_less list_update_beyond nth_list_update_eq snd_conv update_state_at_def update_state_def)
  by (simp add: update_state_at_def)

lemma update_state_at_snd_2:
  "st \<noteq> n \<Longrightarrow> snd (update_state_at states n x v ! st) y = snd (states ! st) y"
  by (simp add: update_state_at_def)

lemma update_state_at_snd_3:
  assumes "n < length states"
  shows "snd (update_state_at states n x v ! n) x = v"
  by (simp add: assms update_state_at_def update_state_def)

lemma subst_exp_more_complex_charact:
  assumes "states' = update_state_at states st x (interp_exp vals states e')"
      and "st < length states"
  shows "interp_exp vals states (subst_exp_single st x e' e) = interp_exp vals states' e"
  using assms
proof (induct e)
  case (EPVar \<phi> y)
  then show ?case
    by (metis interp_exp.simps(1) subst_exp_single.simps(1) update_state_at_snd_1 update_state_at_snd_2 update_state_at_snd_3)
next
  case (ELVar x1 x2)
  then show ?case
    by (simp add: update_state_at_fst)
qed (simp_all)


subsubsection \<open>Assertions\<close>

fun subst_assertion_single :: "qstate \<Rightarrow> var \<Rightarrow> 'a exp \<Rightarrow> 'a assertion \<Rightarrow> 'a assertion" where
  "subst_assertion_single st x e (AConst b) = AConst b"
| "subst_assertion_single st x e (AComp e1 cmp e2) = AComp (subst_exp_single st x e e1) cmp (subst_exp_single st x e e2)"
| "subst_assertion_single st x e (AForall A) = AForall (subst_assertion_single st x (shift_vars_exp 0 e) A)"
| "subst_assertion_single st x e (AExists A) = AExists (subst_assertion_single st x (shift_vars_exp 0 e) A)"
| "subst_assertion_single st x e (AOr A B) = AOr (subst_assertion_single st x e A) (subst_assertion_single st x e B)"
| "subst_assertion_single st x e (AAnd A B) = AAnd (subst_assertion_single st x e A) (subst_assertion_single st x e B)"
| "subst_assertion_single st x e (AForallState A) = AForallState (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A)"
| "subst_assertion_single st x e (AExistsState A) = AExistsState (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A)"

fun wf_assertion_aux :: "nat \<Rightarrow> nat \<Rightarrow> 'a assertion \<Rightarrow> bool" where
  "wf_assertion_aux nv ns (AConst b) \<longleftrightarrow> True"
| "wf_assertion_aux nv ns (AComp e1 cmp e2) \<longleftrightarrow> wf_exp nv ns e1 \<and> wf_exp nv ns e2"
| "wf_assertion_aux nv ns (AAnd A B) \<longleftrightarrow> wf_assertion_aux nv ns A \<and> wf_assertion_aux nv ns B"
| "wf_assertion_aux nv ns (AOr A B) \<longleftrightarrow> wf_assertion_aux nv ns A \<and> wf_assertion_aux nv ns B"

| "wf_assertion_aux nv ns (AForall A) \<longleftrightarrow> wf_assertion_aux (Suc nv) ns A"
| "wf_assertion_aux nv ns (AExists A) \<longleftrightarrow> wf_assertion_aux (Suc nv) ns A"
| "wf_assertion_aux nv ns (AForallState A) \<longleftrightarrow> wf_assertion_aux nv (Suc ns) A"
| "wf_assertion_aux nv ns (AExistsState A) \<longleftrightarrow> wf_assertion_aux nv (Suc ns) A"


abbreviation wf_assertion where "wf_assertion \<equiv> wf_assertion_aux 0 0"


lemma wf_shift_vars:
  assumes "wf_assertion_aux nv ns A"
  shows "wf_assertion_aux (Suc nv) ns (shift_vars n A)"
  using assms
  by (induct A arbitrary: n nv ns) (simp_all add: wf_shift_vars_exp)

lemma wf_subst_assertion:
  assumes "wf_assertion_aux nv ns A"
      and "wf_exp nv ns e"
    shows "wf_assertion_aux nv ns (subst_assertion_single \<phi> x e A)"
  using assms
proof (induct A arbitrary: nv ns e \<phi>)
  case (AComp x1a x2 x3a)
  then show ?case
    by (simp add: wf_subst_exp)
qed (simp_all add: wf_shift_vars_exp wf_shift_states_exp)

lemma subst_assertion_single_charact:
  assumes "interp_exp vals states e = snd (states ! st) x"
  shows "sat_assertion vals states (subst_assertion_single st x e A) S \<longleftrightarrow> sat_assertion vals states A S"
  using assms
proof (induct A arbitrary: vals states st e)
  case (AForallState A)
  have "sat_assertion vals states (AForallState A) S \<longleftrightarrow> (\<forall>\<phi> \<in> S. sat_assertion vals (\<phi> # states) A S)"
    by simp
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S. sat_assertion vals (\<phi> # states) (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A) S)"
    using AForallState(1)[of vals _ "shift_states_exp 0 e" "Suc st"] AForallState(2)
    by (metis insert_at.simps(1) nth_Cons_Suc shift_states_exp_charact zero_le)
  finally show ?case by simp
next
  case (AExistsState A)
  have "sat_assertion vals states (AExistsState A) S \<longleftrightarrow> (\<exists>\<phi> \<in> S. sat_assertion vals (\<phi> # states) A S)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S. sat_assertion vals (\<phi> # states) (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A) S)"
    by (metis AExistsState.hyps AExistsState.prems insert_at.simps(1) nth_Cons_Suc shift_states_exp_charact zero_le)
  finally show ?case by simp
next
  case (AForall A)
  have "sat_assertion vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (metis AForall.hyps AForall.prems insert_at.simps(1) shift_vars_exp_charact zero_le)
  finally show ?case
    by simp
next
  case (AExists A)
  have "sat_assertion vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (metis AExists.hyps AExists.prems insert_at.simps(1) shift_vars_exp_charact zero_le)
  finally show ?case
    by simp
next
  case (AComp e1 cmp e2)
  then show ?case
    using subst_exp_single_charact[of vals states e st x] by auto
qed (simp_all)



lemma update_state_at_cons:
  "update_state_at (\<phi> # states) (Suc n) x v = \<phi> # update_state_at states n x v"
  by (simp add: update_state_at_def)


lemma subst_assertion_single_charact_better:
  assumes "states' = update_state_at states st x (interp_exp vals states e)"
      and "st < length states"
    shows "sat_assertion vals states (subst_assertion_single st x e A) S \<longleftrightarrow> sat_assertion vals states' A S"
  using assms
proof (induct A arbitrary: vals states states' st e)
  case (AComp x1a x2 x3a)
  then show ?case
    by (simp add: subst_exp_more_complex_charact)
next
  case (AForallState A)
  have "sat_assertion vals states (subst_assertion_single st x e (AForallState A)) S
  \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (update_state_at (\<phi> # states) (Suc st) x (interp_exp vals (\<phi> # states) (shift_states_exp 0 e))) A S)"
    by (simp add: AForallState.hyps AForallState.prems(2))
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # update_state_at states st x (interp_exp vals states e)) A S)"
    by (metis update_state_at_cons insert_at.simps(1) shift_states_exp_charact zero_le)
  finally show "sat_assertion vals states (subst_assertion_single st x e (AForallState A)) S = sat_assertion vals states' (AForallState A) S"
    by (simp add: AForallState.prems(1))
next
  case (AExistsState A)
  have "sat_assertion vals states (subst_assertion_single st x e (AExistsState A)) S
  \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (update_state_at (\<phi> # states) (Suc st) x (interp_exp vals (\<phi> # states) (shift_states_exp 0 e))) A S)"
    by (simp add: AExistsState.hyps AExistsState.prems(2))
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # update_state_at states st x (interp_exp vals states e)) A S)"
    by (metis update_state_at_cons insert_at.simps(1) shift_states_exp_charact zero_le)
  finally show "sat_assertion vals states (subst_assertion_single st x e (AExistsState A)) S = sat_assertion vals states' (AExistsState A) S"
    by (simp add: AExistsState.prems(1))
next
  case (AForall A)
  have "sat_assertion vals states (subst_assertion_single st x e (AForall A)) S
  \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (simp add: AForall.hyps AForall.prems(2))
  then show ?case
    by (metis AForall.hyps AForall.prems(1) AForall.prems(2) insert_at.simps(1) sat_assertion.simps(5) shift_vars_exp_charact zero_le)
next
  case (AExists A)
  have "sat_assertion vals states (subst_assertion_single st x e (AExists A)) S
  \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (simp add: AExists.hyps AExists.prems(2))
  then show ?case
    by (metis AExists.hyps AExists.prems(1) AExists.prems(2) insert_at.simps(1) sat_assertion.simps(6) shift_vars_exp_charact zero_le)
qed (simp_all)


subsubsection \<open>Transformation for havoc\<close>


fun transform_havoc where
  "transform_havoc x (AForallState A) = AForallState (AForall (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x A))))"
| "transform_havoc x (AExistsState A) = AExistsState (AExists (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x A))))"
| "transform_havoc x (AExists A) = AExists (transform_havoc x A)"
| "transform_havoc x (AForall A) = AForall (transform_havoc x A)"
| "transform_havoc x (AOr A B) = AOr (transform_havoc x A) (transform_havoc x B)"
| "transform_havoc x (AAnd A B) = AAnd (transform_havoc x A) (transform_havoc x B)"
| "transform_havoc x (AConst b) = AConst b"
| "transform_havoc x (AComp e1 cmp e2) = AComp e1 cmp e2"


lemma sem_havoc_bis:
  "sem (Havoc x) S = {(fst \<phi>, (snd \<phi>)(x := v)) |\<phi> v. \<phi> \<in> S}" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
    using sem_havoc by fastforce
  show "?A \<subseteq> ?B"
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain l \<sigma> v where "\<phi> = (l, \<sigma>(x := v))" "(l, \<sigma>) \<in> S"
      by (metis in_sem prod.collapse single_sem_Havoc_elim)
    then show "\<phi> \<in> ?B"
      by auto
  qed
qed

lemma helper_update_state:
  "(v # vals) ! 0 = snd ((update_state \<phi> x v # states) ! 0) x"
  by (simp add: update_state_def)

lemma helper_S_update_states:
  assumes "S' = { update_state \<phi> x v |\<phi> v. \<phi> \<in> S}"
  shows "(\<forall>\<phi> \<in> S'. Q \<phi>) \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<forall>v. Q (update_state \<phi> x v))"
proof
  show "\<forall>\<phi>\<in>S'. Q \<phi> \<Longrightarrow> \<forall>\<phi>\<in>S. \<forall>v. Q (update_state \<phi> x v)"
    using assms by blast
  show "\<forall>\<phi>\<in>S. \<forall>v. Q (update_state \<phi> x v) \<Longrightarrow> \<forall>\<phi>\<in>S'. Q \<phi>"
    using assms by force
qed

lemma helper_S_update_states_exists:
  assumes "S' = { update_state \<phi> x v |\<phi> v. \<phi> \<in> S}"
  shows "(\<exists>\<phi> \<in> S'. Q \<phi>) \<longleftrightarrow> (\<exists>\<phi> \<in> S. \<exists>v. Q (update_state \<phi> x v))"
proof
  show "\<exists>\<phi>\<in>S'. Q \<phi> \<Longrightarrow> \<exists>\<phi>\<in>S. \<exists>v. Q (update_state \<phi> x v)"
    using assms by force
  show "\<exists>\<phi>\<in>S. \<exists>v. Q (update_state \<phi> x v) \<Longrightarrow> \<exists>\<phi>\<in>S'. Q \<phi>"
    using assms by blast
qed



lemma equiv_havoc_transform:
  assumes "S' = { update_state \<phi> x v |\<phi> v. \<phi> \<in> S}"
  shows "sat_assertion vals states P S' \<longleftrightarrow> sat_assertion vals states (transform_havoc x P) S"
proof (induct P arbitrary: vals states)
  case (AForallState P)

  let ?PP = "shift_vars 0 (transform_havoc x P)"
  let ?P = "subst_assertion_single 0 x (EQVar 0) ?PP"

  have rr: "\<And>\<phi> v. sat_assertion (v # vals) (\<phi> # states) ?P S
   \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
  proof -
    fix \<phi> v
    have "sat_assertion (v # vals) (insert_at 0 \<phi> states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S =
sat_assertion (v # vals) (insert_at 0 (update_state \<phi> x v) states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S"
      by (metis (no_types, lifting) One_nat_def helper_update_state insert_at.simps(1) interp_exp.simps(3) length_insert_at list_update_code(2) nth_Cons_0 subst_assertion_single_charact subst_assertion_single_charact_better trans_less_add2 update_state_at_def zero_less_Suc)
    then show "sat_assertion (v # vals) (\<phi> # states) ?P S \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
      by simp
  qed
  have "sat_assertion vals states (transform_havoc x (AForallState P)) S \<longleftrightarrow> sat_assertion vals states (AForallState (AForall ?P)) S"
    by simp
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<forall>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S)"
    using rr by simp
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<forall>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?PP S)"
    using rr subst_assertion_single_charact[of _ _ _ _ x ?PP S] helper_update_state
    by (metis interp_exp.simps(3))
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<forall>v. sat_assertion vals (update_state \<phi> x v # states) (transform_havoc x P) S)"
    by (metis insert_at.simps(1) le0 shift_vars_charact)
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<forall>v. sat_assertion vals (update_state \<phi> x v # states) P S')"
    using AForallState.hyps AForallState.prems by force
  also have "... \<longleftrightarrow> sat_assertion vals states (AForallState P) S'"
    using helper_S_update_states[of S' x S "\<lambda>\<phi>. sat_assertion vals (\<phi> # states) P S'"] assms by force
  then show ?case
    using calculation by blast
next
  case (AExistsState P)

  let ?PP = "shift_vars 0 (transform_havoc x P)"
  let ?P = "subst_assertion_single 0 x (EQVar 0) ?PP"

  have rr: "\<And>\<phi> v. sat_assertion (v # vals) (\<phi> # states) ?P S
   \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
  proof -
    fix \<phi> v
    have "sat_assertion (v # vals) (insert_at 0 \<phi> states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S =
sat_assertion (v # vals) (insert_at 0 (update_state \<phi> x v) states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S"
      by (metis (no_types, lifting) One_nat_def helper_update_state insert_at.simps(1) insert_at_charact_2 interp_exp.simps(3) length_insert_at list_update_code(2) subst_assertion_single_charact subst_assertion_single_charact_better trans_less_add2 update_state_at_def zero_le zero_less_Suc)
    then show "sat_assertion (v # vals) (\<phi> # states) ?P S \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
      by simp
  qed
  have "sat_assertion vals states (transform_havoc x (AExistsState P)) S \<longleftrightarrow> sat_assertion vals states (AExistsState (AExists ?P)) S"
    by simp
  also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S. \<exists>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S)"
    using rr by simp
  also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S. \<exists>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?PP S)"
    by (metis helper_update_state interp_exp.simps(3) subst_assertion_single_charact)
  also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S. \<exists>v. sat_assertion vals (update_state \<phi> x v # states) (transform_havoc x P) S)"
    by (metis insert_at.simps(1) le0 shift_vars_charact)
  also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S. \<exists>v. sat_assertion vals (update_state \<phi> x v # states) P S')"
    using AExistsState.hyps AExistsState.prems by force
  also have "... \<longleftrightarrow> sat_assertion vals states (AExistsState P) S'"
    using helper_S_update_states_exists[of S' x S "\<lambda>\<phi>. sat_assertion vals (\<phi> # states) P S'"] assms
    by simp
  then show ?case
    using calculation by blast
qed (simp_all)




subsubsection \<open>Syntactic rule for havoc\<close>

theorem rule_havoc_syntactic_general:
  "\<Turnstile> { sat_assertion states vals (transform_havoc x P) } Havoc x {sat_assertion states vals P}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "sat_assertion states vals (transform_havoc x P) S"
  let ?S = "sem (Havoc x) S"
  have "sat_assertion states vals P ?S \<longleftrightarrow> sat_assertion states vals (transform_havoc x P) S"
  proof (rule equiv_havoc_transform)
    show "sem (Havoc x) S = {update_state \<phi> x v |\<phi> v. \<phi> \<in> S}"
      by (simp add: sem_havoc_bis update_state_def)
  qed
  then show "sat_assertion states vals P (sem (Havoc x) S)"
    using asm0 by fastforce
qed


theorem rule_havoc_syntactic:
  "\<Turnstile> { interp_assert (transform_havoc x P) } Havoc x {interp_assert P}"
  by (simp add: rule_havoc_syntactic_general)











subsection \<open>Assignment rule\<close>

subsubsection \<open>Program expressions\<close>

fun subst_pexp :: "var \<Rightarrow> 'a pexp \<Rightarrow> 'a pexp \<Rightarrow> 'a pexp" where
  "subst_pexp x e (PVar y) = (if x = y then e else PVar y)"
| "subst_pexp x e (PBinop p1 op p2) = PBinop (subst_pexp x e p1) op (subst_pexp x e p2)"
| "subst_pexp x e (PFun f p) = PFun f (subst_pexp x e p)"
| "subst_pexp _ _ e = e" (* Constants and quantified vars *)

lemma subst_pexp_charact:
  "interp_pexp (subst_pexp x e' e) \<sigma> = interp_pexp e (\<sigma>(x := interp_pexp e' \<sigma>))"
proof (induct e)
  case (PVar x)
  then show ?case
    by (metis fun_upd_apply interp_pexp.simps(1) subst_pexp.simps(1))
qed (simp_all)

fun subst_pbexp :: "var \<Rightarrow> 'a pexp \<Rightarrow> 'a pbexp \<Rightarrow> 'a pbexp" where
  "subst_pbexp x e (PBAnd pb1 pb2) = PBAnd (subst_pbexp x e pb1) (subst_pbexp x e pb2)"
| "subst_pbexp x e (PBOr pb1 pb2) = PBOr (subst_pbexp x e pb1) (subst_pbexp x e pb2)"
| "subst_pbexp x e (PBComp p1 cmp p2) = PBComp (subst_pexp x e p1) cmp (subst_pexp x e p2)"
| "subst_pbexp _ _ (PBConst b) = PBConst b"

lemma subst_pbexp_charact:
  "interp_pbexp (subst_pbexp x e pb) \<sigma> \<longleftrightarrow> interp_pbexp pb (\<sigma>(x := interp_pexp e \<sigma>))"
proof (induct pb)
  case (PBComp x1 x2 x3)
  then show ?case
    using interp_pbexp.simps(4) subst_pexp_charact
    by (metis subst_pbexp.simps(3))
qed (simp_all)


subsubsection \<open>Expressions (Boolean and values)\<close>


definition subst_all_states where
  "subst_all_states x pe states = map (subst_state x pe) states"

fun subst_exp :: "var \<Rightarrow> 'a pexp \<Rightarrow> 'a exp \<Rightarrow> 'a exp" where
  "subst_exp x pe (EPVar st y) = (if x = y then pexp_to_exp st pe else EPVar st y)"
| "subst_exp x pe (EBinop e1 bop e2) = EBinop (subst_exp x pe e1) bop (subst_exp x pe e2)"
| "subst_exp x pe (EFun f e) = EFun f (subst_exp x pe e)"
| "subst_exp _ _ e = e" (* Logical variables, quantified variables, constants *)


lemma subst_exp_charact_aux:
  "snd (subst_state x pe (states ! st)) x = interp_exp vals states (pexp_to_exp st pe)"
  by (induct pe) (simp_all add: subst_state_def)

lemma subst_exp_charact:
  assumes "wf_exp nv (length states) e"
    shows "interp_exp vals states (subst_exp x pe e) = interp_exp vals (subst_all_states x pe states) e"
  using assms
proof (induct e)
  case (EPVar st y)
  let ?states = "subst_all_states x pe states"
  have "snd (subst_state x pe (states ! st)) = snd (?states ! st)"
    by (metis EPVar.prems(1) nth_map subst_all_states_def wf_exp.simps(1))
  show "interp_exp vals states (subst_exp x pe (EPVar st y)) = interp_exp vals ?states (EPVar st y)"
  proof (cases "x = y")
    case True
    then have "interp_exp vals states (subst_exp x pe (EPVar st y)) = interp_exp vals states (pexp_to_exp st pe)"
      by simp
    moreover have "interp_exp vals ?states (EPVar st y) = snd (?states ! st) y"
      by simp
    moreover have "... = snd (subst_state x pe (states ! st)) y"
      by (simp add: \<open>snd (subst_state x pe (states ! st)) = snd (subst_all_states x pe states ! st)\<close>)
    moreover have "snd (subst_state x pe (states ! st)) x = interp_exp vals states (pexp_to_exp st pe)"
      by (metis subst_exp_charact_aux)
    ultimately show ?thesis
      using True by fastforce
  next
    case False
    then show ?thesis
      by (metis \<open>snd (subst_state x pe (states ! st)) = snd (subst_all_states x pe states ! st)\<close> fun_upd_other interp_exp.simps(1) snd_conv subst_exp.simps(1) subst_state_def)
  qed
next
  case (ELVar st y)
  let ?states = "subst_all_states x pe states"
  have "fst (states ! st) = fst (?states ! st)"
    by (metis ELVar.prems(1) fst_conv nth_map subst_all_states_def subst_state_def wf_exp.simps(2))
  have "interp_exp vals states (subst_exp x pe (ELVar st y)) = interp_exp vals states (ELVar st y)"
    by simp
  also have "... = fst (states ! st) y"
    by simp
  also have "... = fst (?states ! st) y"
    by (simp add: \<open>fst (states ! st) = fst (subst_all_states x pe states ! st)\<close>)
  also have "... = interp_exp vals ?states (ELVar st y)"
    by auto
  then show "interp_exp vals states (subst_exp x pe (ELVar st y)) = interp_exp vals ?states (ELVar st y)"
    using calculation by presburger
qed (simp_all)



subsubsection \<open>Assertions\<close>

fun transform_assign where
  "transform_assign x pe (AForallState A) = AForallState (subst_assertion_single 0 x (pexp_to_exp 0 pe) (transform_assign x pe A))"
| "transform_assign x pe (AExistsState A) = AExistsState (subst_assertion_single 0 x (pexp_to_exp 0 pe) (transform_assign x pe A))"
| "transform_assign x pe (AExists A) = AExists (transform_assign x pe A)"
| "transform_assign x pe (AForall A) = AForall (transform_assign x pe A)"
| "transform_assign x pe (AOr A B) = AOr (transform_assign x pe A) (transform_assign x pe B)"
| "transform_assign x pe (AAnd A B) = AAnd (transform_assign x pe A) (transform_assign x pe B)"
| "transform_assign x pe (AConst b) = AConst b"
| "transform_assign x pe (AComp e1 cmp e2) = AComp e1 cmp e2"


lemma transform_assign_works:
  "sat_assertion vals states (transform_assign x pe A) S = sat_assertion vals states A (subst_state x pe ` S)"
proof (induct A arbitrary: vals states)
  case (AForallState A)
  have "sat_assertion vals states (transform_assign x pe (AForallState A)) S
  \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # states) (subst_assertion_single 0 x (pexp_to_exp 0 pe) (transform_assign x pe A)) S)"
    by auto
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (update_state_at (\<phi> # states) 0 x (interp_exp vals (\<phi> # states) (pexp_to_exp 0 pe))) (transform_assign x pe A) S)"
    by (simp add: subst_assertion_single_charact_better)
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (update_state_at (\<phi> # states) 0 x (interp_exp vals (\<phi> # states) (pexp_to_exp 0 pe))) A (subst_state x pe ` S))"
    using AForallState by presburger
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (update_state \<phi> x (interp_exp vals (\<phi> # states) (pexp_to_exp 0 pe)) # states) A (subst_state x pe ` S))"
    using update_state_at_def
    by (metis list_update_code(2) nth_Cons_0)
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (update_state \<phi> x (interp_pexp pe (snd \<phi>)) # states) A (subst_state x pe ` S))"
    by (metis nth_Cons_0 same_syn_sem_exp)
  finally show "sat_assertion vals states (transform_assign x pe (AForallState A)) S = sat_assertion vals states (AForallState A) (subst_state x pe ` S)"
    by (simp add: subst_state_def update_state_def)
next
  case (AExistsState A)
  have "sat_assertion vals states (transform_assign x pe (AExistsState A)) S
  \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # states) (subst_assertion_single 0 x (pexp_to_exp 0 pe) (transform_assign x pe A)) S)"
    by auto
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (update_state_at (\<phi> # states) 0 x (interp_exp vals (\<phi> # states) (pexp_to_exp 0 pe))) (transform_assign x pe A) S)"
    by (simp add: subst_assertion_single_charact_better)
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (update_state_at (\<phi> # states) 0 x (interp_exp vals (\<phi> # states) (pexp_to_exp 0 pe))) A (subst_state x pe ` S))"
    using AExistsState by presburger
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (update_state \<phi> x (interp_exp vals (\<phi> # states) (pexp_to_exp 0 pe)) # states) A (subst_state x pe ` S))"
    using update_state_at_def
    by (metis list_update_code(2) nth_Cons_0)
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (update_state \<phi> x (interp_pexp pe (snd \<phi>)) # states) A (subst_state x pe ` S))"
    by (metis nth_Cons_0 same_syn_sem_exp)
  finally show "sat_assertion vals states (transform_assign x pe (AExistsState A)) S = sat_assertion vals states (AExistsState A) (subst_state x pe ` S)"
    by (simp add: subst_state_def update_state_def)
qed (simp_all)


subsubsection \<open>Syntactic rule for assignments\<close>

theorem rule_assign_syntactic_general:
  "\<Turnstile> { sat_assertion vals states (transform_assign x pe P) } Assign x (interp_pexp pe) {sat_assertion vals states P}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "sat_assertion vals states (transform_assign x pe P) S"
  then have "sat_assertion vals states P (subst_state x pe ` S)"
    using transform_assign_works by blast
  moreover have "{(l, \<sigma>(x := interp_pexp pe \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S} = subst_state x pe ` S" (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
    proof
      fix \<phi> assume "\<phi> \<in> ?A"
      then obtain l \<sigma> where "\<phi> = (l, \<sigma>(x := interp_pexp pe \<sigma>))" "(l, \<sigma>) \<in> S"
        by blast
      then show "\<phi> \<in> ?B"
        by (metis (mono_tags, lifting) fst_conv image_iff snd_conv subst_state_def)
    qed
    show "?B \<subseteq> ?A"
      using subst_state_def by fastforce
  qed
  ultimately show "sat_assertion vals states P (sem (Assign x (interp_pexp pe)) S)"
    by (simp add: sem_assign)
qed



theorem rule_assign_syntactic:
  "\<Turnstile> { interp_assert (transform_assign x pe P) } Assign x (interp_pexp pe) {interp_assert P}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "interp_assert (transform_assign x pe P) S"
  then have "sat_assertion [] [] P (subst_state x pe ` S)"
    using transform_assign_works by blast
  moreover have "{(l, \<sigma>(x := interp_pexp pe \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S} = subst_state x pe ` S" (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
    proof
      fix \<phi> assume "\<phi> \<in> ?A"
      then obtain l \<sigma> where "\<phi> = (l, \<sigma>(x := interp_pexp pe \<sigma>))" "(l, \<sigma>) \<in> S"
        by blast
      then show "\<phi> \<in> ?B"
        by (metis (mono_tags, lifting) fst_conv image_iff snd_conv subst_state_def)
    qed
    show "?B \<subseteq> ?A"
      using subst_state_def by fastforce
  qed
  ultimately show "interp_assert P (sem (Assign x (interp_pexp pe)) S)"
    by (simp add: sem_assign)
qed





subsection \<open>Loop rules\<close>


fun no_exists_state :: "'a assertion \<Rightarrow> bool"
  where
  "no_exists_state (AConst _) \<longleftrightarrow> True"
| "no_exists_state (AComp _ _ _) \<longleftrightarrow> True"
| "no_exists_state (AForallState A) \<longleftrightarrow> no_exists_state A"
| "no_exists_state (AExistsState A) \<longleftrightarrow> False"
| "no_exists_state (AForall A) \<longleftrightarrow> no_exists_state A"
| "no_exists_state (AExists A) \<longleftrightarrow> no_exists_state A"
| "no_exists_state (AAnd A B) \<longleftrightarrow> no_exists_state A \<and> no_exists_state B"
| "no_exists_state (AOr A B) \<longleftrightarrow> no_exists_state A \<and> no_exists_state B"

lemma mono_sym_then_up_closed:
  assumes "no_exists_state A"
      and "S \<subseteq> S'"
      and "sat_assertion vals states A S'"
    shows "sat_assertion vals states A S"
  using assms
proof (induct A arbitrary: vals states)
  case (AExistsState A)
  then show ?case
    by (metis no_exists_state.simps(4))
qed (auto)

definition up_closed where
  "up_closed A \<longleftrightarrow> (\<forall>S S' vals states. S \<subseteq> S' \<and> sat_assertion vals states A S \<longrightarrow> sat_assertion vals states A S')"

lemma up_closedE:
  assumes "up_closed A"
      and "S \<subseteq> S'"
      and "sat_assertion vals states A S"
    shows "sat_assertion vals states A S'"
  using assms(1) assms(2) assms(3) up_closed_def by blast



lemma sat_assertion_aforallstateI:
  assumes "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> sat_assertion vals (\<phi> # states) A S"
  shows "sat_assertion vals states (AForallState A) S"
  using assms sat_assertion.simps(3) by blast


lemma join_entails:
  assumes "up_closed A"
      and "sat_assertion vals states (AForallState A) S1"
      and "sat_assertion vals states (AForallState A) S2"
    shows "sat_assertion vals states (AForallState A) (S1 \<union> S2)"
proof (rule sat_assertion_aforallstateI)
  fix \<phi>
  assume asm0: "\<phi> \<in> S1 \<union> S2"
  show "sat_assertion vals (\<phi> # states) A (S1 \<union> S2)"
  proof (cases "\<phi> \<in> S1")
    case True
    then have "sat_assertion vals (\<phi> # states) A S1"
      using assms(2) sat_assertion.simps(3) by blast
    then show ?thesis
      by (meson assms(1) sup_ge1 up_closedE)
  next
    case False
    then show ?thesis
      by (metis UnE asm0 assms(1) assms(3) sat_assertion.simps(3) sup_ge2 up_closedE)
  qed
qed


lemma general_join_entails:
  assumes "up_closed A"
      and "\<And>x. sat_assertion vals states (AForallState A) (F x)"
    shows "sat_assertion vals states (AForallState A) (\<Union>x. F x)"
proof (rule sat_assertion_aforallstateI)
  fix \<phi>
  assume asm0: "\<phi> \<in> \<Union> (range F)"
  then obtain x where "\<phi> \<in> F x"
    by blast
  then have "sat_assertion vals (\<phi> # states) A (F x)"
    using assms(2) by force
  then show "sat_assertion vals (\<phi> # states) A (\<Union> (range F))"
    by (meson Union_upper assms(1) range_eqI up_closedE)
qed



fun no_forall_state :: "'a assertion \<Rightarrow> bool"
  where
  "no_forall_state (AConst _) \<longleftrightarrow> True"
| "no_forall_state (AComp _ _ _) \<longleftrightarrow> True"
| "no_forall_state (AForallState A) \<longleftrightarrow> False"
| "no_forall_state (AExistsState A) \<longleftrightarrow> no_forall_state A"
| "no_forall_state (AForall A) \<longleftrightarrow> no_forall_state A"
| "no_forall_state (AExists A) \<longleftrightarrow> no_forall_state A"
| "no_forall_state (AAnd A B) \<longleftrightarrow> no_forall_state A \<and> no_forall_state B"
| "no_forall_state (AOr A B) \<longleftrightarrow> no_forall_state A \<and> no_forall_state B"

lemma no_forall_exists_state_not:
  "no_forall_state A \<equiv> no_exists_state (ANot A)"
  by (induct A) auto



fun no_forall_state_after_existential :: "'a assertion \<Rightarrow> bool"
  where
  "no_forall_state_after_existential (AConst _) \<longleftrightarrow> True"
| "no_forall_state_after_existential (AComp _ _ _) \<longleftrightarrow> True"
| "no_forall_state_after_existential (AForallState A) \<longleftrightarrow> no_forall_state_after_existential A"
| "no_forall_state_after_existential (AForall A) \<longleftrightarrow> no_forall_state_after_existential A"
| "no_forall_state_after_existential (AAnd A B) \<longleftrightarrow> no_forall_state_after_existential A \<and> no_forall_state_after_existential B"
| "no_forall_state_after_existential (AOr A B) \<longleftrightarrow> no_forall_state_after_existential A \<and> no_forall_state_after_existential B"
| "no_forall_state_after_existential (AExists A) \<longleftrightarrow> no_forall_state A"
| "no_forall_state_after_existential (AExistsState A) \<longleftrightarrow> no_forall_state A"


lemma up_closed_from_no_exists_state_false:
  assumes "no_forall_state A"
      and "sat_assertion vals states A (S n)"
    shows "sat_assertion vals states A (\<Union>n. S n)"
  using assms
proof (induct A)
  case (AExistsState A)
  then show ?case
    by (meson UN_upper no_forall_exists_state_not iso_tuple_UNIV_I mono_sym_then_up_closed sat_assertion_Not)
next
  case (AForall A)
  then show ?case
    by (meson UN_upper no_forall_exists_state_not iso_tuple_UNIV_I mono_sym_then_up_closed sat_assertion_Not)
next
  case (AExists A)
  then show ?case
    by (meson UNIV_I no_forall_exists_state_not UN_upper mono_sym_then_up_closed sat_assertion_Not)
qed (force+)


definition shift_sequence :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)"
  where
  "shift_sequence S n m = S (m + n)"

lemma shift_sequence_properties:
  assumes "ascending S"
    shows "ascending (shift_sequence S n)"
      and "(\<Union>m. S m) = (\<Union>m. (shift_sequence S n) m)" (is "?A = ?B")
  apply (metis (mono_tags, lifting) Suc_n_not_le_n add_Suc ascendingI ascending_def assms nle_le shift_sequence_def)
proof
  show "?B \<subseteq> ?A"
    by (simp add: SUP_le_iff UN_upper shift_sequence_def)
  show "?A \<subseteq> ?B"
    by (metis SUP_mono' ascending_def assms le_add1 shift_sequence_def)
qed

fun extract_indices_sat_P where
  "extract_indices_sat_P P S 0 = (SOME n. P (S n))"
| "extract_indices_sat_P P S (Suc m) = (SOME n. P (S n) \<and> n > extract_indices_sat_P P S m)"

definition holds_infinitely_often where
  "holds_infinitely_often P S \<longleftrightarrow> (\<forall>m. \<exists>n. n > m \<and> P (S n))"

lemma extract_indices_sat_P_properties:
  assumes "holds_infinitely_often P S"
    shows "P (S (extract_indices_sat_P P S 0))"
      and "n > 0 \<Longrightarrow> P (S (extract_indices_sat_P P S n))
  \<and> extract_indices_sat_P P S n > extract_indices_sat_P P S (n - 1)"
  apply (metis assms extract_indices_sat_P.simps(1) holds_infinitely_often_def someI_ex)
  using assms
proof (induct n)
  case (Suc n)
  then have "P (S (extract_indices_sat_P P S n))"
    by (metis bot_nat_0.not_eq_extremum extract_indices_sat_P.simps(1) holds_infinitely_often_def someI_ex)
  let ?P = "\<lambda>m. P (S m) \<and> m > extract_indices_sat_P P S n"
  have "?P (SOME m. ?P m)"
  proof (rule someI_ex)
    show "\<exists>x. P (S x) \<and> extract_indices_sat_P P S n < x"
      by (meson Suc.prems(2) holds_infinitely_often_def)
  qed
  then show ?case
    by simp
qed (simp)

lemma extract_indices_sat_P_larger:
  assumes "holds_infinitely_often P S"
  shows "extract_indices_sat_P P S n \<ge> n"
  using assms
proof (induct n)
  case (Suc n)
  then show ?case
    by (metis Suc_leI diff_Suc_1 diff_diff_cancel extract_indices_sat_P_properties(2) less_imp_diff_less zero_less_Suc)
qed (simp)

definition subseq_sat where
  "subseq_sat P S n = S (extract_indices_sat_P P S n)"

lemma subseq_sat_properties:
  assumes "holds_infinitely_often P S"
      and "ascending S"
    shows "ascending (subseq_sat P S)"
      and "\<And>n. P (subseq_sat P S n)"
      and "(\<Union>n. S n) = (\<Union>n. subseq_sat P S n)" (is "?A = ?B")
proof (rule ascendingI)
  fix n
  have "extract_indices_sat_P P S (Suc n) > extract_indices_sat_P P S n"
    by (metis assms(1) diff_Suc_1 extract_indices_sat_P_properties(2) zero_less_Suc)
  then show "subseq_sat P S n \<subseteq> subseq_sat P S (Suc n)"
    by (metis ascending_def assms(2) less_imp_le_nat subseq_sat_def)
  fix n show "P (subseq_sat P S n)"
    by (metis assms(1) extract_indices_sat_P_properties(1) extract_indices_sat_P_properties(2) gr0I subseq_sat_def)
next
  show "?A = ?B"
  proof
    show "?B \<subseteq> ?A"
      by (simp add: SUP_le_iff UN_upper subseq_sat_def)
    show "?A \<subseteq> ?B"
    proof
      fix x assume "x \<in> \<Union> (range S)"
      then obtain n where "x \<in> S n" by blast
      then have "x \<in> subseq_sat P S n"
        by (metis ascending_def assms(1) assms(2) extract_indices_sat_P_larger subseq_sat_def subsetD)
      then show "x \<in> ?B" by blast
    qed
  qed
qed


lemma no_forall_state_after_existential_sem:
  assumes "no_forall_state_after_existential A"
      and "ascending S"
      and "\<And>n. sat_assertion vals states A (S n)"
    shows "sat_assertion vals states A (\<Union>n. S n)"
  using assms
proof (induct A arbitrary: vals states S)
  case (AForallState A)
  show ?case
  proof (rule sat_assertion_aforallstateI)
    fix \<phi>
    assume "\<phi> \<in> \<Union> (range S)"
    then obtain n where "\<phi> \<in> S n" by blast
    then have "\<And>m. m \<ge> n \<Longrightarrow> sat_assertion vals (\<phi> # states) A (S m)"
      by (meson AForallState.prems(2) AForallState.prems(3) ascending_def sat_assertion.simps(3) subsetD)
    let ?S = "shift_sequence S n"
    have "sat_assertion vals (\<phi> # states) A (\<Union> (range ?S))"
    proof (rule AForallState(1))
      show "no_forall_state_after_existential A"
        using AForallState.prems(1) by auto
      show "ascending ?S"
        by (simp add: AForallState.prems(2) shift_sequence_properties(1))
      fix m show "sat_assertion vals (\<phi> # states) A (shift_sequence S n m)"
        by (simp add: \<open>\<And>m. n \<le> m \<Longrightarrow> sat_assertion vals (\<phi> # states) A (S m)\<close> shift_sequence_def)
    qed
    then show "sat_assertion vals (\<phi> # states) A (\<Union> (range S))"
      by (metis AForallState.prems(2) shift_sequence_properties(2))
  qed
next
  case (AExistsState A)
  then show ?case
    by (meson no_forall_state.simps(4) no_forall_state_after_existential.simps(8) up_closed_from_no_exists_state_false)
next
  case (AExists A)
  then show ?case
    by (meson no_forall_state.simps(6) no_forall_state_after_existential.simps(7) up_closed_from_no_exists_state_false)
next
  case (AOr A1 A2)
(* either A1 is infinitely often true, or either A2 is... *)
  show ?case
  proof (cases "holds_infinitely_often (sat_assertion vals states A1) S")
    case True
    then have "sat_assertion vals states A1 (\<Union> (range (subseq_sat (sat_assertion vals states A1) S)))"
      using AOr.hyps(1) AOr.prems(1) AOr.prems(2) subseq_sat_properties(1) subseq_sat_properties(2) no_forall_state_after_existential.simps(6) by blast
    then show ?thesis
      using AOr.prems(2) True subseq_sat_properties(3) by fastforce
  next
    case False
    then have "holds_infinitely_often (sat_assertion vals states A2) S"
      using AOr.prems(3) sat_assertion.simps(8) holds_infinitely_often_def
      by (metis gt_ex max_less_iff_conj)
    then have "sat_assertion vals states A2 (\<Union> (range (subseq_sat (sat_assertion vals states A2) S)))"
      using AOr.hyps(2) AOr.prems(1) AOr.prems(2) subseq_sat_properties(1) subseq_sat_properties(2) no_forall_state_after_existential.simps(6) by blast
    then show ?thesis
      using AOr.prems(2) \<open>holds_infinitely_often (sat_assertion vals states A2) S\<close> subseq_sat_properties(3) by fastforce
  qed
next
  case (AAnd A1 A2)
  then show ?case
    using sat_assertion.simps(7) no_forall_state_after_existential.simps(5) by blast
qed (simp_all)


(* Can be used with while rule! *)
lemma upwards_closed_syn_sem_practical:
  assumes "no_forall_state_after_existential A"
  shows "upwards_closed (\<lambda>n. interp_assert A) (interp_assert A)"
  by (simp add: assms no_forall_state_after_existential_sem upwards_closed_def)

theorem while_general_syntactic:
  assumes "\<And>n. \<Turnstile> {P n} if_then b C {P (Suc n)}"
      and "\<And>n. \<Turnstile> {P n} Assume (lnot b) {interp_assert A}"
      and "no_forall_state_after_existential A"
    shows "\<Turnstile> {P 0} while_cond b C {conj (interp_assert A) (holds_forall (lnot b))}"
  by (metis assms(1) assms(2) assms(3) upwards_closed_syn_sem_practical while_general)

theorem while_forall_exists_simpler:
  assumes "\<Turnstile> {I} if_then b C {I}"
      and "\<Turnstile> {I} Assume (lnot b) {interp_assert Q}"
      and "no_forall_state_after_existential Q"
    shows "\<Turnstile> {I} while_cond b C {conj (interp_assert Q) (holds_forall (lnot b))}"
  by (metis assms(1) assms(2) assms(3) upwards_closed_syn_sem_practical while_general)

(* Side-conditions: No normal existential on the left of a forallstate, no existential state *)
theorem while_d_syntactic:
  assumes "\<Turnstile> { interp_assert A } if_then b C { interp_assert A }"
      and "no_forall_state_after_existential A"
      and "no_exists_state A"
    shows "\<Turnstile> { interp_assert A } while_cond b C {conj (interp_assert A) (holds_forall (lnot b))}"
  using assms(1)
proof (rule while_d)
  show "upwards_closed (\<lambda>a. interp_assert A) (interp_assert A)"
    by (simp add: assms(2) no_forall_state_after_existential_sem upwards_closed_def)
  fix n show "downwards_closed (interp_assert A)"
    using assms(3) downwards_closed_def mono_sym_then_up_closed by fastforce
qed



lemma downwards_closed_is_hypersafety:
  "hypersafety P \<longleftrightarrow> downwards_closed P"
  using downwards_closed_def hypersafety_def by metis


subsection \<open>Rewrite rules for 'a assertions\<close>

definition equiv where
  "equiv A B \<longleftrightarrow> (\<forall>vals states S. sat_assertion vals states A S \<longleftrightarrow> sat_assertion vals states B S)"

lemma forall_commute:
  "equiv (AForallState (AForall A)) (AForall (AForallState A))"
  using equiv_def by force

lemma exists_commute:
  "equiv (AExistsState (AExists A)) (AExists (AExistsState A))"
  using equiv_def by force

lemma forall_state_and:
  "equiv (AForallState (AAnd A B)) (AAnd (AForallState A) (AForallState B))"
  using equiv_def by force

lemma exists_state_or:
  "equiv (AExistsState (AOr A B)) (AOr (AExistsState A) (AExistsState B))"
  using equiv_def by force

lemma forall_and:
  "equiv (AForall (AAnd A B)) (AAnd (AForall A) (AForall B))"
  using equiv_def by force

lemma exists_or:
  "equiv (AExists (AOr A B)) (AOr (AExists A) (AExists B))"
  using equiv_def by force

lemma entailment_natural_partition:
  assumes "no_forall_state P"
  shows "entails (natural_partition (\<lambda>(n::nat). interp_assert (AForallState P))) (interp_assert (AForallState P))"
proof (rule entailsI)
  fix S :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"

  assume asm0: "natural_partition (\<lambda>(n::nat). interp_assert (AForallState P)) S"
  then obtain F where "S = (\<Union>(n::nat). F n)" "\<And>n. interp_assert (AForallState P) (F n)"
    using natural_partitionE[of "\<lambda>n. interp_assert (AForallState P)" S] by blast
  then have "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> sat_assertion [] [\<phi>] P S"    
    by (meson UN_iff assms sat_assertion.simps(3) up_closed_from_no_exists_state_false)
  then show "interp_assert (AForallState P) S"
    by simp
qed


lemma no_forall_state_mono:
  assumes "no_forall_state A"
      and "sat_assertion vals states A S"
      and "S \<subseteq> S'"
    shows "sat_assertion vals states A S'"
by (metis assms(1) assms(2) assms(3) mono_sym_then_up_closed no_forall_exists_state_not sat_assertion_Not)


lemma entailment_loop_join:
  assumes "no_forall_state P"
  shows "entails (join (interp_assert (AForallState P)) (interp_assert (AForallState P))) (interp_assert (AForallState P))"
proof (rule entailsI)
  fix S :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"

  assume asm0: "join (interp_assert (AForallState P)) (interp_assert (AForallState P)) S"
  then obtain S1 S2 where r: "S = S1 \<union> S2" "interp_assert (AForallState P) S1" "interp_assert (AForallState P) S2"
    by (metis join_def)
  have "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> sat_assertion [] [\<phi>] P S"    
  proof -
    fix \<phi> assume asm1: "\<phi> \<in> S"
    then show "sat_assertion [] [\<phi>] P S"
      by (metis Un_iff r assms no_forall_state_mono sat_assertion.simps(3) sup_ge1 sup_ge2)
  qed
  then show "interp_assert (AForallState P) S"
    by simp
qed




subsection \<open>Free variables and safe frame rule\<close>

fun wr :: "(nat, nat) stmt \<Rightarrow> nat set" where
  "wr Skip = {}"
| "wr (Assign x _) = {x}"
| "wr (Havoc x) = {x}"
| "wr (Assume b) = {}"
| "wr (C1;; C2) = wr C1 \<union> wr C2"
| "wr (If C1 C2) = wr C1 \<union> wr C2"
| "wr (While C) = wr C"


definition agree_on where
  "agree_on V \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>x\<in>V. \<sigma> x = \<sigma>' x)"

lemma agree_onI:
  assumes "\<And>x. x\<in>V \<Longrightarrow> \<sigma> x = \<sigma>' x"
  shows "agree_on V \<sigma> \<sigma>'"
  using agree_on_def assms by blast

lemma agree_onE:
  assumes "agree_on V \<sigma> \<sigma>'"
      and "x \<in> V"
    shows "\<sigma> x = \<sigma>' x"
  by (meson agree_on_def assms(1) assms(2))

lemma agree_on_subset:
  assumes "agree_on V' \<sigma> \<sigma>'"
      and "V \<subseteq> V'"
    shows "agree_on V \<sigma> \<sigma>'"
  by (meson agree_on_def assms(1) assms(2) in_mono)

lemma agree_on_trans:
  assumes "agree_on V \<sigma> \<sigma>'"
      and "agree_on V \<sigma>' \<sigma>''"
    shows "agree_on V \<sigma> \<sigma>''"
proof (rule agree_onI)
  fix x assume "x \<in> V"
  then show "\<sigma> x = \<sigma>'' x"
    by (metis agree_on_def assms(1) assms(2))
qed

lemma agree_on_sym:
  assumes "agree_on V \<sigma> \<sigma>'"
  shows "agree_on V \<sigma>' \<sigma>"
  by (metis agree_on_def assms)

lemma wr_charact:
  assumes "single_sem C \<sigma> \<sigma>'"
      and "wr C \<inter> V = {}"
  shows "agree_on V \<sigma> \<sigma>'"
  using assms
proof (induct rule: single_sem.induct)
  case (SemSeq C1 \<sigma> \<sigma>1 C2 \<sigma>2)
  then show ?case
    by (metis Un_empty agree_on_trans inf_sup_distrib2 wr.simps(5))
qed (auto simp add: agree_on_def)

fun fv_exp :: "'a exp \<Rightarrow> var set" where
  "fv_exp (EBinop e1 _ e2) = fv_exp e1 \<union> fv_exp e2"
| "fv_exp (EPVar _ x) = {x}"
| "fv_exp (EFun _ e) = fv_exp e"
| "fv_exp _ = {}"

lemma fv_wr_charact_exp:
(* all program variables *)
  assumes "agree_on (fv_exp e) \<sigma> \<sigma>'"
      and "n \<le> length states"
      and "wf_exp nv (Suc (length states)) e"
    shows "interp_exp vals (insert_at n (l, \<sigma>) states) e = interp_exp vals (insert_at n (l, \<sigma>') states) e"
  using assms
proof (induct e)
  case (EPVar st x)
  then show ?case
  proof (cases "st < n")
    case True
    then show ?thesis
      by (simp add: assms(2) insert_at_charact_1)
  next
    case False
    then have "st \<ge> n" by simp
    then show ?thesis
    proof (cases "st = n")
      case True
      then have "interp_exp vals (insert_at n (l, \<sigma>) states) (EPVar st x) = \<sigma> x"
        by (simp add: assms(2) insert_at_charact_2)
      also have "... = \<sigma>' x"
        by (metis EPVar.prems(1) agree_on_def fv_exp.simps(2) insertCI)
      then show ?thesis
        by (simp add: True assms(2) insert_at_charact_2)
    next
      case False
      then have "interp_exp vals (insert_at n (l, \<sigma>) states) (EPVar st x) = snd ((insert_at n (l, \<sigma>) states) ! st) x"
        by simp
      also have "... = snd (states ! (st - 1)) x"        
        by (metis False One_nat_def \<open>n \<le> st\<close> add_diff_inverse_nat assms(2) dual_order.antisym insert_at_charact_3 le_less_Suc_eq le_zero_eq not_less_eq_eq plus_1_eq_Suc)
      then show ?thesis
        by (metis False One_nat_def \<open>n \<le> st\<close> add_diff_inverse_nat assms(2) dual_order.antisym insert_at_charact_3 interp_exp.simps(1) le_less_Suc_eq le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    qed
  qed
next
  case (ELVar st x)
  then show ?case
  proof (cases "st < n")
    case True
    then show ?thesis
      by (simp add: assms(2) insert_at_charact_1)
  next
    case False
    then have "st \<ge> n" by simp
    then show ?thesis
    proof (cases "st = n")
      case True
      then have "interp_exp vals (insert_at n (l, \<sigma>) states) (ELVar st x) = l x"
        by (simp add: assms(2) insert_at_charact_2)
      then show ?thesis
        by (simp add: True assms(2) insert_at_charact_2)
    next
      case False
      then have "interp_exp vals (insert_at n (l, \<sigma>) states) (ELVar st x) = fst ((insert_at n (l, \<sigma>) states) ! st) x"
        by simp
      also have "... = fst (states ! (st - 1)) x"        
        by (metis False One_nat_def \<open>n \<le> st\<close> add_diff_inverse_nat assms(2) dual_order.antisym insert_at_charact_3 le_less_Suc_eq le_zero_eq not_less_eq_eq plus_1_eq_Suc)
      then show ?thesis
        by (metis False One_nat_def \<open>n \<le> st\<close> add_diff_inverse_nat assms(2) dual_order.antisym insert_at_charact_3 interp_exp.simps(2) le_less_Suc_eq le_zero_eq not_less_eq_eq plus_1_eq_Suc)
    qed
  qed
next
  case (EBinop e1 x2 e2)
  then show ?case
    by (simp add: agree_on_def)
qed (simp_all)


(* program variables... *)
fun fv where
  "fv (AAnd F1 F2) = fv F1 \<union> fv F2"
| "fv (AOr F1 F2) = fv F1 \<union> fv F2"
| "fv (AForall F) = fv F"
| "fv (AExists F) = fv F"
| "fv (AForallState F) = fv F"
| "fv (AExistsState F) = fv F"
| "fv (AConst b) = {}"
| "fv (AComp e1 cmp e2) = fv_exp e1 \<union> fv_exp e2"




lemma fv_wr_charact_aux:
(* all program variables *)
  assumes "agree_on (fv F) \<sigma> \<sigma>'"
      and "n \<le> length states"
      and "sat_assertion vals (insert_at n (l, \<sigma>) states) F S"
      and "wf_assertion_aux nv (Suc (length states)) F"
    shows "sat_assertion vals (insert_at n (l, \<sigma>') states) F S"
  using assms
proof (induct F arbitrary: vals states n nv)
  case (AExists F)
  then show ?case
    by (metis fv.simps(4) sat_assertion.simps(6) wf_assertion_aux.simps(6))
next
  case (AComp e1 cmp e2)
  then have "interp_exp vals (insert_at n (l, \<sigma>) states) e1 = interp_exp vals (insert_at n (l, \<sigma>') states) e1"
    using fv_wr_charact_exp[of e1 \<sigma> \<sigma>' n states nv vals l] agree_on_subset by fastforce
  moreover have "interp_exp vals (insert_at n (l, \<sigma>) states) e2 = interp_exp vals (insert_at n (l, \<sigma>') states) e2"
    using fv_wr_charact_exp[of e2 \<sigma> \<sigma>' n states nv vals l] agree_on_subset AComp by auto
  ultimately show "sat_assertion vals (insert_at n (l, \<sigma>') states) (AComp e1 cmp e2) S"
    using AComp.prems(3) by auto
next
  case (AForallState F)
  then have "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> sat_assertion vals (insert_at (Suc n) (l, \<sigma>) (\<phi> # states)) F S"
    by simp
  then have "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> sat_assertion vals (insert_at (Suc n) (l, \<sigma>') (\<phi> # states)) F S"
    by (metis AForallState.hyps AForallState.prems(1) AForallState.prems(2) AForallState.prems(4) Suc_le_mono fv.simps(5) length_Cons wf_assertion_aux.simps(7))
  then show ?case by simp
next
  case (AExistsState F)
  then obtain \<phi> where asm0: "\<phi> \<in> S" "sat_assertion vals (insert_at (Suc n) (l, \<sigma>) (\<phi> # states)) F S"
    by auto
  then have "sat_assertion vals (insert_at (Suc n) (l, \<sigma>') (\<phi> # states)) F S"
    by (metis AExistsState.hyps AExistsState.prems(1) AExistsState.prems(2) AExistsState.prems(4) Suc_le_mono fv.simps(6) length_Cons wf_assertion_aux.simps(8))
  then show ?case using asm0 by auto
qed (auto simp add: agree_on_def)


lemma fv_wr_charact:
  assumes "agree_on (fv F) \<sigma> \<sigma>'"
      and "sat_assertion vals ((l, \<sigma>) # states) F S"
      and "wf_assertion_aux nv (Suc (length states)) F"
    shows "sat_assertion vals ((l, \<sigma>') # states) F S"
proof -
  have "sat_assertion vals (insert_at 0 (l, \<sigma>') states) F S"
    using assms fv_wr_charact_aux by fastforce
  then show ?thesis
    by simp
qed


lemma syntactic_safe_frame_preserved:
  assumes "wr C \<inter> fv F = {}"
      and "sat_assertion vals states F S"
      and "wf_assertion_aux nv (length states) F"
      and "no_exists_state F"
    shows "sat_assertion vals states F (sem C S)"
  using assms
proof (induct F arbitrary: vals states nv)
  case (AForallState F)
  then have "\<And>\<phi>. \<phi> \<in> sem C S \<Longrightarrow> sat_assertion vals (\<phi> # states) F (sem C S)"
  proof -
    fix \<phi> assume asm0: "\<phi> \<in> sem C S"
    then obtain \<sigma> where "single_sem C \<sigma> (snd \<phi>)" "(fst \<phi>, \<sigma>) \<in> S"
      using in_sem by blast
    then have "sat_assertion vals ((fst \<phi>, \<sigma>) # states) F (sem C S)"
      using AForallState.hyps AForallState.prems assms(1) by auto
    moreover have "agree_on (fv F) \<sigma> (snd \<phi>)"
      using AForallState.prems(1) \<open>\<langle>(C::(nat, nat) stmt), \<sigma>::nat \<Rightarrow> nat\<rangle> \<rightarrow> snd (\<phi>::(nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat))\<close> wr_charact by auto
    moreover have "wf_assertion_aux nv (Suc (length states)) F"
      using AForallState.prems(3) by auto
    ultimately have "sat_assertion vals ((fst \<phi>, snd \<phi>) # states) F (sem C S)"
      using fv_wr_charact[of F \<sigma> "snd \<phi>" vals "fst \<phi>" states "sem C S"]
      by fast
    then show "sat_assertion vals (\<phi> # states) F (sem C S)"
      by simp
  qed
  then show ?case
    using AForallState.hyps AForallState.prems(2) assms(1) by auto
qed (fastforce+)

theorem safe_frame_rule_syntactic:
  assumes "wr C \<inter> fv F = {}"
      and "wf_assertion F"
      and "no_exists_state F"
    shows "\<Turnstile> {interp_assert F} C {interp_assert F}"
  by (metis assms(1) assms(2) assms(3) hyper_hoare_tripleI list.size(3) syntactic_safe_frame_preserved)

theorem LUpdateS:
  assumes "\<Turnstile> { (\<lambda>S. P S \<and> e_recorded_in_t e t S) } C { Q }"
      and "not_fv_hyper t P"
      and "not_fv_hyper t Q"
  shows "\<Turnstile> { P } C { Q }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm: "P S"
  let ?S = "assign_exp_to_lvar_set e t S"
  have "Q (sem C ?S)"
    using asm assms(1) assms(2) e_recorded_in_t_if_assigned hyper_hoare_tripleE not_fv_hyper_assign_exp by fastforce
  then show "Q (sem C S)"
    by (meson assign_exp_to_lvar_set_same_mod_updates assms(3) not_fv_hyper_def same_mod_updates_sym sem_update_commute)
qed


end