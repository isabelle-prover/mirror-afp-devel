(*
Authors (in alph. order):  
  Guillaume Allais,
  Martin Avanzini
  Julian Nagele
  Christian Sternagel,  
  Thomas Sternagel
  René Thiemann
  Sarah Winkler
*)

section \<open>More Results on Terms\<close>

text \<open>In this theory we introduce many more concepts of terms,
  we provide several results that link various notions, e.g., positions, 
  subterms, contexts, substitutions, etc.\<close>

theory Term_More
  imports
    Position
    Subterm_and_Context
    Polynomial_Factorization.Missing_List
begin

text \<open>@{text "showl"}-Instance for Terms\<close>

fun showsl_term' :: "('f \<Rightarrow> showsl) \<Rightarrow> ('v \<Rightarrow> showsl) \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl"
where
  "showsl_term' fun var (Var x) = var x" |
  "showsl_term' fun var (Fun f ts) =
    fun f \<circ> showsl_list_gen id (STR '''') (STR ''('') (STR '', '') (STR '')'') (map (showsl_term' fun var) ts)"

abbreviation showsl_nat_var :: "nat \<Rightarrow> showsl"
  where
    "showsl_nat_var i \<equiv> showsl_lit (STR ''x'') \<circ> showsl i"

abbreviation showsl_nat_term :: "('f::showl, nat) term \<Rightarrow> showsl"
  where
    "showsl_nat_term \<equiv> showsl_term' showsl showsl_nat_var"

instantiation "term" :: (showl,showl)showl
begin
definition "showsl (t :: ('a,'b)term) = showsl_term' showsl showsl t"
definition "showsl_list (xs :: ('a,'b)term list) = default_showsl_list showsl xs"
instance ..
end


text \<open>@{class "showl"}-Instance for Contexts\<close>

fun showsl_ctxt' :: "('f \<Rightarrow> showsl) \<Rightarrow> ('v \<Rightarrow> showsl) \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> showsl" where
  "showsl_ctxt' fun var (Hole) = showsl_lit (STR ''[]'')"
| "showsl_ctxt' fun var (More f ss1 D ss2) = (
    fun f \<circ> showsl (STR ''('') \<circ>
    showsl_list_gen (showsl_term' fun var) (STR '''') (STR '''') (STR '', '') (STR '', '') ss1 \<circ>
    showsl_ctxt' fun var D \<circ>
    showsl_list_gen (showsl_term' fun var) (STR '')'') (STR '', '') (STR '', '') (STR '')'') ss2
  )"

instantiation ctxt :: (showl,showl)showl
begin
definition "showsl (t :: ('a,'b)ctxt) = showsl_ctxt' showsl showsl t"
definition "showsl_list (xs :: ('a,'b)ctxt list) = default_showsl_list showsl xs"
instance ..
end


text \<open>General Folds on Terms\<close>

context
begin
qualified fun
  fold :: "('v \<Rightarrow> 'a) \<Rightarrow> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> ('f, 'v) term \<Rightarrow> 'a"
  where
    "fold var fun (Var x) = var x" |
    "fold var fun (Fun f ts) = fun f (map (fold var fun) ts)"
end

declare term.disc [intro]

abbreviation "num_args t \<equiv> length (args t)"

definition funas_args_term :: "('f, 'v) term \<Rightarrow> 'f sig"
  where
    "funas_args_term t = \<Union>(set (map funas_term (args t)))"

fun eroot :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) + 'v"
  where
    "eroot (Fun f ts) = Inl (f, length ts)" |
    "eroot (Var x) = Inr x"

abbreviation "root_set \<equiv> set_option \<circ> root"

lemma funas_term_conv:
  "funas_term t = set_option (root t) \<union> funas_args_term t"
  by (cases t) (simp_all add: funas_args_term_def)

text \<open>The \emph{depth} of a term is defined as follows:\<close>
fun depth :: "('f, 'v) term \<Rightarrow> nat"
  where
    "depth (Var _) = 0" |
    "depth (Fun _ []) = 0" |
    "depth (Fun _ ts) = 1 + Max (set (map depth ts))"

declare conj_cong [fundef_cong]
text \<open>The positions of a term\<close>
fun poss :: "('f, 'v) term \<Rightarrow> pos set" where
  "poss (Var x) = {[]}" |
  "poss (Fun f ss) = {[]} \<union> {i # p | i p. i < length ss \<and> p \<in> poss (ss ! i)}"
declare conj_cong [fundef_cong del]

lemma Cons_poss_Var [simp]:
  "i # p \<in> poss (Var x) \<longleftrightarrow> False"
  by simp

lemma elem_size_size_list_size [termination_simp]:
  "x \<in> set xs \<Longrightarrow> size x < size_list size xs"
  by (induct xs) auto

text \<open>The set of function positions of a term\<close>
fun fun_poss :: "('f, 'v) term \<Rightarrow> pos set"
  where
    "fun_poss (Var x) = {}" |
    "fun_poss (Fun f ts) = {[]} \<union> (\<Union>i<length ts. {i # p | p. p \<in> fun_poss (ts ! i)})"

lemma fun_poss_imp_poss:
  assumes "p \<in> fun_poss t"
  shows "p \<in> poss t"
  using assms by (induct t arbitrary: p) auto

lemma finite_fun_poss:
  "finite (fun_poss t)"
  by (induct t) auto

text \<open>The set of variable positions of a term\<close>
fun var_poss :: "('f, 'v) term \<Rightarrow> pos set"
  where
    "var_poss (Var x) = {[]}" |
    "var_poss (Fun f ts) = (\<Union>i<length ts. {i # p | p. p \<in> var_poss (ts ! i)})"

lemma var_poss_imp_poss:
  assumes "p \<in> var_poss t"
  shows "p \<in> poss t"
  using assms by (induct t arbitrary: p) auto

lemma finite_var_poss:
  "finite (var_poss t)"
  by (induct t) auto

lemma poss_simps [symmetric, simp]:
  "poss t = fun_poss t \<union> var_poss t"
  "poss t = var_poss t \<union> fun_poss t"
  "fun_poss t = poss t - var_poss t"
  "var_poss t = poss t - fun_poss t"
  by (induct_tac [!] t) auto

lemma finite_poss [simp]:
  "finite (poss t)"
  by (subst poss_simps [symmetric]) (metis finite_Un finite_fun_poss finite_var_poss)

text \<open>The subterm of a term~@{text s} at position~@{text p} is defined as follows:\<close>
fun subt_at :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) term" (infixl "|'_" 67)
  where
    "s |_ [] = s" |
    "Fun f ss |_ (i # p) = (ss ! i) |_ p"

lemma var_poss_iff:
  "p \<in> var_poss t \<longleftrightarrow> (\<exists>x. p \<in> poss t \<and> t |_ p = Var x)"
  by (induct t arbitrary: p) auto

lemma fun_poss_fun_conv:
  assumes "p \<in> fun_poss t"
  shows "\<exists> f ts. t |_ p = Fun f ts"
proof (cases "t |_ p")
  case (Var x)
  have p_in_t: "p \<in> poss t" using fun_poss_imp_poss[OF assms].
  then have "p \<in> poss t - fun_poss t" using Var(1) var_poss_iff by auto
  then show ?thesis using assms by blast
next
  case (Fun f ts) then show ?thesis by auto
qed

lemma pos_append_poss:
  "p \<in> poss t \<Longrightarrow> q \<in> poss (t |_ p) \<Longrightarrow> p @ q \<in> poss t"
proof (induct t arbitrary: p q)
  case (Fun f ts p q)
  show ?case
  proof (cases p)
    case Nil then show ?thesis using Fun by auto
  next
    case (Cons i p')
    with Fun have i: "i < length ts" and p': "p' \<in> poss (ts ! i)" by auto
    then have mem: "ts ! i \<in> set ts" by auto
    from Fun(3) have "q \<in> poss (ts ! i |_ p')" by (auto simp: Cons)
    from Fun(1) [OF mem p' this]
    show ?thesis by (auto simp: Cons i)
  qed
qed simp

text \<open>Creating a context from a term by adding a hole at a specific position.\<close>
fun
  ctxt_of_pos_term :: "pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) ctxt"
  where
    "ctxt_of_pos_term [] t = \<box>" |
    "ctxt_of_pos_term (i # ps) (Fun f ts) =
    More f (take i ts) (ctxt_of_pos_term ps (ts!i)) (drop (Suc i) ts)"

lemma ctxt_supt_id:
  assumes "p \<in> poss t"
  shows "(ctxt_of_pos_term p t)\<langle>t |_ p\<rangle> = t"
  using assms by (induct t arbitrary: p) (auto simp: id_take_nth_drop [symmetric])

text \<open>
  Let @{text s} and @{text t} be terms. The following three statements are equivalent:
  \begin{enumerate}
   \item \label{A}@{text "s \<unrhd> t"}
   \item \label{B}@{text "\<exists>p\<in>poss s. s|_p = t"}
   \item \label{C}@{text "\<exists>C. s = C\<langle>t\<rangle>"}
  \end{enumerate}
\<close>

text \<open>The position of the hole in a context is uniquely determined.\<close>
fun
  hole_pos :: "('f, 'v) ctxt \<Rightarrow> pos"
  where
    "hole_pos \<box> = []" |
    "hole_pos (More f ss D ts) = length ss # hole_pos D"

lemma hole_pos_ctxt_of_pos_term [simp]:
  assumes "p \<in> poss t"
  shows "hole_pos (ctxt_of_pos_term p t) = p"
  using assms
proof (induct t arbitrary: p)
  case (Fun f ts)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis using Fun by auto
  next
    case (Cons i q)
    with Fun(2) have i: "i < length ts" and q: "q \<in> poss (ts ! i)" by auto
    then have "ts ! i \<in> set ts" by auto
    from Fun(1)[OF this q] Cons i show ?thesis by simp
  qed
qed simp

lemma hole_pos_id_ctxt:
  assumes "C\<langle>s\<rangle> = t"
  shows "ctxt_of_pos_term (hole_pos C) t = C"
  using assms
proof (induct C arbitrary: t)
  case (More f bef C aft)
  then show ?case
  proof (cases t)
    case (Fun g ts)
    with More have [simp]: "g = f" by simp
    from Fun More have bef: "take (length bef) ts = bef" by auto
    from Fun More have aft: "drop (Suc (length bef)) ts = aft" by auto
    from Fun More have Cs: "C\<langle>s\<rangle> = ts ! length bef" by auto
    from Fun More show ?thesis by (simp add: bef aft More(1)[OF Cs])
  qed simp
qed simp

lemma supteq_imp_subt_at:
  assumes "s \<unrhd> t" 
  shows "\<exists>p\<in>poss s. s|_p = t"
  using assms proof (induct s t rule: supteq.induct)
  case (refl s)
  have "[] \<in> poss s" by (induct s rule: term.induct) auto
  have "s|_[] = s" by simp
  from \<open>[] \<in> poss s\<close> and \<open>s|_[] = s\<close> show ?case by best
next
  case (subt u ss t f)
  then obtain p where "p \<in> poss u" and "u|_p = t" by best
  from \<open>u \<in> set ss\<close> obtain i
    where "i < length ss" and "u = ss!i" by (auto simp: in_set_conv_nth)
  from \<open>i < length ss\<close> and \<open>p \<in> poss u\<close>
  have "i#p \<in> poss (Fun f ss)" unfolding \<open>u = ss!i\<close> by simp
  have "Fun f ss|_ (i#p) = t"
    unfolding subt_at.simps unfolding \<open>u = ss!i\<close>[symmetric] by (rule \<open>u|_p = t\<close>)
  with \<open>i#p \<in> poss (Fun f ss)\<close> show ?case by best
qed

lemma subt_at_imp_ctxt:
  assumes "p \<in> poss s" 
  shows "\<exists>C. C\<langle>s|_p\<rangle> = s"
  using assms proof (induct p arbitrary: s)
  case (Nil s)
  have "\<box>\<langle>s|_[]\<rangle> = s" by simp
  then show ?case by best
next
  case (Cons i p s)
  then obtain f ss where "s = Fun f ss" by (cases s) auto
  with \<open>i#p \<in> poss s\<close> obtain u :: "('a,'b) term"
    where "u = ss!i" and "p \<in> poss u" and "i < length ss" by auto
  from Cons and \<open>p\<in>poss u\<close> obtain D where "D\<langle>u|_p\<rangle> = u" by auto
  let ?ss1 = "take i ss" and ?ss2 = "drop (Suc i) ss"
  let ?E = "More f ?ss1 D ?ss2"
  have "?ss1@D\<langle>u|_p\<rangle>#?ss2 = ss" (is "?ss = ss") unfolding \<open>D\<langle>u|_p\<rangle> = u\<close> unfolding \<open>u = ss!i\<close>
    unfolding id_take_nth_drop[OF \<open>i < length ss\<close>, symmetric] ..
  have "s|_ (i#p) = u|_p" unfolding \<open>s = Fun f ss\<close> using \<open>u = ss!i\<close> by simp
  have "?E\<langle>s|_(i#p)\<rangle> = s"
    unfolding ctxt_apply_term.simps \<open>s|_(i#p) = u|_p\<close> \<open>?ss = ss\<close> unfolding \<open>s = Fun f ss\<close> ..
  then show ?case by best
qed

lemma subt_at_imp_supteq':
  assumes "p \<in> poss s" and "s|_p = t" 
  shows "s \<unrhd> t"
proof -
  from \<open>p \<in> poss s\<close> obtain C where "C\<langle>s|_p\<rangle> = s" using subt_at_imp_ctxt by best
  then show ?thesis unfolding \<open>s|_p = t\<close> using ctxt_imp_supteq by auto
qed

lemma subt_at_imp_supteq: "p \<in> poss s \<Longrightarrow> s \<unrhd> s|_p"
  by (simp add: subt_at_imp_supteq')

lemma fun_poss_ctxt_apply_term:
  assumes "p \<in> fun_poss C\<langle>s\<rangle>"
  shows "(\<forall>t. p \<in> fun_poss C\<langle>t\<rangle>) \<or> (\<exists>q. p = (hole_pos C) @ q \<and> q \<in> fun_poss s)"
  using assms
proof (induct p arbitrary: C)
  case Nil then show ?case by (cases C) auto
next
  case (Cons i p)
  then show ?case
  proof (cases C)
    case (More f bef C' aft)
    with Cons(2) have "i < length (bef @ C'\<langle>s\<rangle> # aft)" by auto
    consider "i < length bef" | (C') "i = length bef" | "i > length bef"
      by (cases "i < length bef", auto, cases "i = length bef", auto)
    then show ?thesis
    proof (cases)
      case C'
      then have "p \<in> fun_poss C'\<langle>s\<rangle>" using More Cons by auto
      from Cons(1)[OF this] More C' show ?thesis by auto
    qed (insert More Cons, auto simp: nth_append)
  qed auto
qed

text \<open>Conversions between contexts and proper subterms.\<close>

text \<open>
By adding \emph{non-empty} to statements \ref{B} and \ref{C} a similar characterisation for
proper subterms is obtained:
\begin{enumerate}
 \item @{text "s \<rhd> t"}
 \item @{text "\<exists>i p. i#p\<in>poss s \<and> s|_(i#p) = t"}
 \item @{text "\<exists>C. C \<noteq> \<box> \<and> s = C\<langle>t\<rangle>"}
\end{enumerate}
\<close>

lemma supt_imp_subt_at_nepos:
  assumes "s \<rhd> t" shows "\<exists>i p. i#p \<in> poss s \<and> s|_ (i#p) = t"
proof -
  from assms have "s \<unrhd> t" and "s \<noteq> t" unfolding supt_supteq_conv by auto
  then obtain p where supteq: "p \<in> poss s" "s|_p = t" using supteq_imp_subt_at by best
  have "p \<noteq> []"
  proof
    assume "p = []" then have "s = t" using \<open>s|_p = t\<close> by simp
    then show False using \<open>s \<noteq> t\<close> by simp
  qed
  then obtain i q where "p = i#q" by (cases p) simp
  with supteq show ?thesis by auto
qed


lemma arg_neq:
  assumes "i < length ss" and "ss!i = Fun f ss" shows "False"
proof -
  from \<open>i < length ss\<close> have "(ss!i) \<in> set ss" by auto
  with assms show False by simp
qed

lemma subt_at_nepos_neq:
  assumes "i#p \<in> poss s" shows "s|_(i#p) \<noteq> s"
proof (cases s)
  fix x assume "s = Var x"
  then have "i#p \<notin> poss s" by simp
  with assms show ?thesis by simp
next
  fix f ss assume "s = Fun f ss" show ?thesis
  proof
    assume "s|_ (i#p) = s"
    from assms have "i < length ss" unfolding \<open>s = Fun f ss\<close> by auto
    then have "ss!i \<in> set ss" by simp
    then have "Fun f ss \<rhd> ss!i" by (rule supt.arg)
    then have "Fun f ss \<noteq> ss!i" unfolding supt_supteq_conv by simp
    from \<open>s|_(i#p) = s\<close> and assms
    have "ss!i \<unrhd> Fun f ss" using subt_at_imp_supteq' unfolding \<open>s = Fun f ss\<close> by auto
    with supt_not_sym[OF \<open>Fun f ss \<rhd> ss!i\<close>] have "ss!i = Fun f ss" by auto
    with \<open>i < length ss\<close> show False by (rule arg_neq)
  qed
qed

lemma subt_at_nepos_imp_supt:
  assumes "i#p \<in> poss s" shows "s \<rhd> s |_ (i#p)"
proof -
  from assms have "s \<unrhd> s|_(i#p)" by (rule subt_at_imp_supteq)
  from assms have "s|_(i#p) \<noteq> s" by (rule subt_at_nepos_neq)
  from \<open>s \<unrhd> s|_(i#p)\<close> and \<open>s|_(i#p) \<noteq> s\<close> show ?thesis by (auto simp: supt_supteq_conv)
qed

lemma subt_at_nepos_imp_nectxt:
  assumes "i#p \<in> poss s" and "s|_(i#p) = t" shows "\<exists>C. C \<noteq> \<box> \<and> C\<langle>t\<rangle> = s"
proof -
  from assms obtain C where "C\<langle>s|_(i#p)\<rangle> = s" using subt_at_imp_ctxt by best
  from \<open>i#p \<in> poss s\<close>
  have "t \<noteq> s" unfolding \<open>s|_(i#p) = t\<close>[symmetric] using subt_at_nepos_neq by best
  from assms and \<open>C\<langle>s|_(i#p)\<rangle> = s\<close> have "C\<langle>t\<rangle> = s" by simp
  have "C \<noteq> \<box>"
  proof
    assume "C = \<box>"
    with \<open>C\<langle>t\<rangle> = s\<close> have "t = s" by simp
    with \<open>t \<noteq> s\<close> show False by simp
  qed
  with \<open>C\<langle>t\<rangle> = s\<close> show ?thesis by auto
qed

lemma supteq_subst_cases':
  "s \<cdot> \<sigma> \<unrhd> t \<Longrightarrow> (\<exists> u. s \<unrhd> u \<and> is_Fun u \<and> t = u \<cdot> \<sigma>) \<or> (\<exists> x. x \<in> vars_term s \<and> \<sigma> x \<unrhd> t)"
proof (induct s)
  case (Fun f ss)
  from Fun(2)
  show ?case
  proof (cases rule: supteq.cases)
    case refl
    show ?thesis
      by (intro disjI1 exI[of _ "Fun f ss"], auto simp: refl)
  next
    case (subt v ts g)
    then obtain si where si: "si \<in> set ss" "si \<cdot> \<sigma> \<unrhd> t" by auto
    from Fun(1)[OF this] si(1) show ?thesis by auto
  qed
qed simp

lemma size_const_subst[simp]: "size (t \<cdot> (\<lambda> _ . Fun f [])) = size t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts, auto)
qed simp

type_synonym ('f, 'v) terms = "('f, 'v) term set"

lemma supteq_subst_cases [consumes 1, case_names in_term in_subst]:
  "s \<cdot> \<sigma> \<unrhd> t \<Longrightarrow>
  (\<And> u. s \<unrhd> u \<Longrightarrow> is_Fun u \<Longrightarrow> t = u \<cdot> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
  (\<And> x. x \<in> vars_term s \<Longrightarrow> \<sigma> x \<unrhd> t \<Longrightarrow> P) \<Longrightarrow>
  P"
  using supteq_subst_cases' by blast

lemma poss_subst_apply_term:
  assumes "p \<in> poss (t \<cdot> \<sigma>)" and "p \<notin> fun_poss t"
  obtains q r x where "p = q @ r" and "q \<in> poss t" and "t |_ q = Var x" and "r \<in> poss (\<sigma> x)"
  using assms
proof (induct t arbitrary: p)
  case (Fun f ts)
  then show ?case by (auto) (metis append_Cons nth_mem subt_at.simps(2))
qed simp

lemma subt_at_subst [simp]:
  assumes "p \<in> poss t" shows "(t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>"
  using assms by (induct t arbitrary: p) auto

lemma vars_term_size:
  assumes "x \<in> vars_term t"
  shows "size (\<sigma> x) \<le> size (t \<cdot> \<sigma>)"
  using assms
  by (induct t)
    (auto, metis (no_types) comp_apply le_SucI size_list_estimation')

text \<open>Restrict a substitution to a set of variables.\<close>

definition
  subst_restrict :: "('f, 'v) subst \<Rightarrow> 'v set \<Rightarrow> ('f, 'v) subst"
  (infix "|s" 67)
  where
    "\<sigma> |s V = (\<lambda>x. if x \<in> V then \<sigma>(x) else Var x)"

lemma subst_restrict_Int [simp]:
  "(\<sigma> |s V ) |s W = \<sigma> |s (V \<inter> W)"
  by (rule ext) (simp add: subst_restrict_def)

lemma subst_domain_Var_conv [iff]:
  "subst_domain \<sigma> = {} \<longleftrightarrow> \<sigma> = Var"
proof
  assume "subst_domain \<sigma> = {}"
  show "\<sigma> = Var"
  proof (rule ext)
    fix x show "\<sigma>(x) = Var x"
    proof (rule ccontr)
      assume "\<sigma>(x) \<noteq> Var x"
      then have "x \<in> subst_domain \<sigma>" by (simp add: subst_domain_def)
      with \<open>subst_domain \<sigma> = {}\<close> show False by simp
    qed
  qed
next
  assume "\<sigma> = Var" then show "subst_domain \<sigma> = {}" by simp
qed

lemma subst_compose_Var[simp]: "\<sigma> \<circ>\<^sub>s Var = \<sigma>" by (simp add: subst_compose_def)

lemma Var_subst_compose[simp]: "Var \<circ>\<^sub>s \<sigma> = \<sigma>" by (simp add: subst_compose_def)

text \<open>We use the same logical constant as for the power operations on
functions and relations, in order to share their syntax.\<close>
overloading
  substpow \<equiv> "compow :: nat \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
begin

primrec substpow :: "nat \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" where
  "substpow 0 \<sigma> = Var"
| "substpow (Suc n) \<sigma> = \<sigma> \<circ>\<^sub>s substpow n \<sigma>"

end

lemma subst_power_compose_distrib:
  "\<mu> ^^ (m + n) = (\<mu> ^^ m \<circ>\<^sub>s \<mu> ^^ n)" by (induct m) (simp_all add: ac_simps)

lemma subst_power_Suc: "\<mu> ^^ (Suc i) = \<mu> ^^ i \<circ>\<^sub>s \<mu>"
proof -
  have "\<mu> ^^ (Suc i) = \<mu> ^^ (i + Suc 0)" by simp
  then show ?thesis unfolding  subst_power_compose_distrib by simp
qed

lemma subst_pow_mult: "((\<sigma> :: ('f,'v)subst)^^ n) ^^ m = \<sigma> ^^ (n * m)"
  by (induct m arbitrary: n, auto simp: subst_power_compose_distrib)

lemma subst_domain_pow: "subst_domain (\<sigma> ^^ n) \<subseteq> subst_domain \<sigma>"
  unfolding subst_domain_def
  by (induct n, auto simp: subst_compose_def)

lemma subt_at_Cons_distr [simp]:
  assumes "i # p \<in> poss t" and "p \<noteq> []" (*avoid simplifier loop*)
  shows "t |_ (i # p) = (t |_ [i]) |_ p"
  using assms by (induct t) auto

lemma subt_at_append [simp]:
  "p \<in> poss t \<Longrightarrow> t |_ (p @ q) = (t |_ p) |_ q"
proof (induct t arbitrary: p)
  case (Fun f ts)
  show ?case
  proof (cases p)
    case (Cons i p')
    with Fun(2) have i: "i < length ts" and p': "p' \<in> poss (ts ! i)" by auto
    from i have ti: "ts ! i \<in> set ts" by auto
    show ?thesis using Fun(1)[OF ti p'] unfolding Cons by auto
  qed auto
qed auto

lemma subt_at_pos_diff:
  assumes "p <\<^sub>p q" and p: "p \<in> poss s"
  shows "s |_ p |_ pos_diff q p = s |_ q"
  using assms unfolding subt_at_append [OF p, symmetric] by simp

lemma empty_pos_in_poss[simp]: "[] \<in> poss t" by (induct t) auto

lemma poss_append_poss[simp]: "(p @ q \<in> poss t) = (p \<in> poss t \<and> q \<in> poss (t |_ p))" (is "?l = ?r")
proof
  assume ?r
  with pos_append_poss[of p t q] show ?l by auto
next
  assume ?l
  then show ?r
  proof (induct p arbitrary: t)
    case (Cons i p t)
    then obtain f ts where t: "t = Fun f ts" by (cases t, auto)
    note IH = Cons[unfolded t]
    from IH(2) have i: "i < length ts" and rec: "p @ q \<in> poss (ts ! i)" by auto
    from IH(1)[OF rec] i show ?case unfolding t by auto
  qed auto
qed

lemma subterm_poss_conv:
  assumes "p \<in> poss t" and [simp]: "p = q @ r" and "t |_ q = s"
  shows "t |_ p = s |_ r \<and> r \<in> poss s" (is "?A \<and> ?B")
proof -
  have qr: "q @ r \<in> poss t" using assms(1) by simp
  then have q_in_t: "q \<in> poss t" using poss_append_poss by auto
  show ?thesis
  proof
    have "t |_ p = t |_ (q @ r)" by simp
    also have "... = s |_ r" using subt_at_append[OF q_in_t] assms(3) by simp
    finally show "?A" .
  next
    show "?B" using poss_append_poss qr assms(3) by auto
  qed
qed

lemma poss_imp_subst_poss [simp]:
  assumes "p \<in> poss t"
  shows "p \<in> poss (t \<cdot> \<sigma>)"
  using assms by (induct t arbitrary: p) auto

lemma iterate_term:
  assumes id: "t \<cdot> \<sigma> |_ p = t" and pos: "p \<in> poss (t \<cdot> \<sigma>)"
  shows "t \<cdot> \<sigma> ^^ n |_ (p^n) = t \<and> p ^ n \<in> poss (t \<cdot> \<sigma> ^^ n)"
proof (induct n)
  case (Suc n)
  then have p: "p ^ n \<in> poss (t \<cdot> \<sigma> ^^ n)" by simp
  note p' = poss_imp_subst_poss[OF p]
  note p'' = subt_at_append[OF p']
  have idt: "t \<cdot> \<sigma> ^^ (Suc n) = t \<cdot> \<sigma>^^ n \<cdot> \<sigma>" unfolding subst_power_Suc by simp
  have "t \<cdot> \<sigma> ^^ (Suc n) |_ (p ^ Suc n)
    = t \<cdot> \<sigma> ^^ n \<cdot> \<sigma> |_ (p ^ n @ p)" unfolding idt power_pos_Suc ..
  also have "... = ((t \<cdot> \<sigma> ^^ n |_ p ^ n) \<cdot> \<sigma>) |_ p" unfolding p'' subt_at_subst[OF p] ..
  also have "... = t \<cdot> \<sigma> |_ p" unfolding Suc[THEN conjunct1] ..
  also have "... = t" unfolding id ..
  finally have one: "t \<cdot> \<sigma> ^^ Suc n |_ (p ^ Suc n) = t" .
  show ?case
  proof (rule conjI[OF one])
    show "p ^ Suc n \<in> poss (t \<cdot> \<sigma> ^^ Suc n)"
      unfolding power_pos_Suc poss_append_poss idt
    proof (rule conjI[OF poss_imp_subst_poss[OF p]])
      have "t \<cdot> \<sigma> ^^ n \<cdot> \<sigma> |_ (p ^ n) = t \<cdot> \<sigma> ^^ n |_ (p ^ n) \<cdot> \<sigma>"
        by (rule subt_at_subst[OF p])
      also have "... = t \<cdot> \<sigma>" using Suc by simp
      finally show "p \<in> poss (t \<cdot> \<sigma> ^^ n \<cdot> \<sigma> |_ p ^ n)" using pos by auto
    qed
  qed
qed simp

lemma hole_pos_poss [simp]: "hole_pos C \<in> poss (C\<langle>t\<rangle>)"
  by (induct C) auto

lemma hole_pos_poss_conv: "(hole_pos C @ q) \<in> poss (C\<langle>t\<rangle>) \<longleftrightarrow> q \<in> poss t"
  by (induct C) auto

lemma subt_at_hole_pos [simp]: "C\<langle>t\<rangle> |_ hole_pos C = t"
  by (induct C) auto

lemma hole_pos_power_poss [simp]: "(hole_pos C) ^ (n::nat) \<in> poss ((C ^ n)\<langle>t\<rangle>)"
  by (induct n) (auto simp: hole_pos_poss_conv)

lemma poss_imp_ctxt_subst_poss [simp]:
  assumes "p \<in> poss (C\<langle>t\<rangle>)" 
  shows "p \<in> poss ((C \<cdot>\<^sub>c \<sigma>)\<langle>t \<cdot> \<sigma>\<rangle>)"
proof -
  have "p \<in> poss (C\<langle>t\<rangle> \<cdot> \<sigma>)" by (rule poss_imp_subst_poss [OF assms])
  then show ?thesis by simp
qed

lemma poss_Cons_poss[simp]: "(i # p \<in> poss t) = (i < length (args t) \<and> p \<in> poss (args t ! i))"
  by (cases t, auto)

lemma less_pos_imp_supt:
  assumes less: "p' <\<^sub>p p" and p: "p \<in> poss t"
  shows "t |_ p \<lhd> t |_ p'"
proof -
  from less obtain p'' where p'': "p = p' @ p''" unfolding less_pos_def less_eq_pos_def by auto
  with less have ne: "p'' \<noteq> []" by auto
  then obtain i q where ne: "p'' = i # q" by (cases p'', auto)
  from p have p': "p' \<in> poss t" unfolding p'' by simp
  from p have "p'' \<in> poss (t |_ p')" unfolding p''  by simp
  from subt_at_nepos_imp_supt[OF this[unfolded ne]] have "t |_ p' \<rhd> t |_ p' |_ p''" unfolding ne by simp
  then show "t |_ p' \<rhd> t |_ p" unfolding p'' subt_at_append[OF p'] .
qed

lemma less_eq_pos_imp_supt_eq:
  assumes less_eq: "p' \<le>\<^sub>p p" and p: "p \<in> poss t"
  shows "t |_ p \<unlhd> t |_ p'"
proof -
  from less_eq obtain p'' where p'': "p = p' @ p''" unfolding less_eq_pos_def by auto
  from p have p': "p' \<in> poss t" unfolding p'' by simp
  from p have "p'' \<in> poss (t |_ p')" unfolding p'' by simp
  from subt_at_imp_supteq[OF this] have "t |_ p' \<unrhd> t |_ p' |_ p''" by simp
  then show "t |_ p' \<unrhd> t |_ p" unfolding p'' subt_at_append[OF p'] .
qed

lemma funas_term_poss_conv:
  "funas_term t = {(f, length ts) | p f ts. p \<in> poss t \<and> t|_p = Fun f ts}"
proof (induct t)
  case (Fun f ts)
  let ?f = "\<lambda> f ts. (f,length ts)"
  let ?fs = "\<lambda> t. {?f f ts | p f ts. p \<in> poss t \<and> t|_p = Fun f ts}"
  let ?l = "funas_term (Fun f ts)"
  let ?r = "?fs (Fun f ts)"
  {
    fix gn
    have "(gn \<in> ?l) = (gn \<in> ?r)"
    proof (cases "gn = (f,length ts)")
      case False
      obtain g n where gn: "gn = (g,n)" by force
      have "(gn \<in> ?l) = (\<exists> t \<in> set ts. gn \<in> funas_term t)" using False by auto
      also have "... = (\<exists> i < length ts. gn \<in> funas_term (ts ! i))" unfolding set_conv_nth by auto
      also have "... = (\<exists> i < length ts. (g,n) \<in> ?fs (ts ! i))" using Fun[unfolded set_conv_nth] gn by blast
      also have "... = ((g,n) \<in> ?fs (Fun f ts))" (is "?l' = ?r'")
      proof
        assume ?l'
        then obtain i p ss where p: "p \<in> poss (ts ! i)" "ts ! i |_ p = Fun g ss" "n = length ss" "i < length ts" by auto
        show ?r'
          by (rule, rule exI[of _ "i # p"], intro exI conjI, unfold p(3), rule refl, insert p(1) p(2) p(4), auto)
      next
        assume ?r'
        then obtain p ss where p: "p \<in> poss (Fun f ts)" "Fun f ts |_ p = Fun g ss" "n = length ss" by auto
        from p False gn obtain i p' where pp: "p = i # p'" by (cases p, auto)
        show ?l'
          by (rule exI[of _ i], insert p pp, auto)
      qed
      finally show ?thesis unfolding gn .
    qed force
  }
  then show ?case by blast
qed simp

inductive
  subst_instance :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" ("(_/ \<preceq> _)" [56, 56] 55)
  where
    subst_instanceI [intro]:
    "s \<cdot> \<sigma> = t \<Longrightarrow> s \<preceq> t"

lemma subst_instance_trans[trans]:
  assumes "s \<preceq> t" and "t \<preceq> u" shows "s \<preceq> u"
proof -
  from \<open>s \<preceq> t\<close> obtain \<sigma> where "s\<cdot>\<sigma> = t" by (cases rule: subst_instance.cases) best
  from \<open>t \<preceq> u\<close> obtain \<tau> where "t\<cdot>\<tau> = u" by (cases rule: subst_instance.cases) best
  then have "(s\<cdot>\<sigma>)\<cdot>\<tau> = u" unfolding \<open>s\<cdot>\<sigma> = t\<close> .
  then have "s\<cdot>(\<sigma> \<circ>\<^sub>s \<tau>) = u" by simp
  then show ?thesis by (rule subst_instanceI)
qed

lemma subst_instance_refl: "s \<preceq> s"
  using subst_instanceI[where \<sigma> = "Var" and s = s and t = s] by simp

lemma subst_neutral: "subst_domain \<sigma> \<subseteq> V \<Longrightarrow> (Var x)\<cdot>(\<sigma> |s (V - {x})) = (Var x)"
  by (auto simp: subst_domain_def subst_restrict_def)

lemma subst_restrict_domain[simp]: "\<sigma> |s subst_domain \<sigma> = \<sigma>"
proof -
  have "\<sigma> |s subst_domain \<sigma> = (\<lambda>x. if x \<in> subst_domain \<sigma> then \<sigma>(x) else Var x)"
    by (simp add: subst_restrict_def)
  also have "\<dots> = \<sigma>" by (rule ext) (simp add: subst_domain_def)
  finally show ?thesis .
qed

lemma notin_subst_domain_imp_Var:
  assumes "x \<notin> subst_domain \<sigma>" 
  shows "\<sigma> x = Var x"
  using assms by (auto simp: subst_domain_def)

lemma subst_domain_neutral[simp]:
  assumes "subst_domain \<sigma> \<subseteq> V" 
  shows "(\<sigma> |s V) = \<sigma>"
proof -
  {
    fix x
    have "(if x \<in> V then \<sigma>(x) else Var x) = (if x \<in> subst_domain \<sigma> then \<sigma>(x) else Var x)"
    proof (cases "x \<in> subst_domain \<sigma>")
      case True
      then have x: "x \<in> V = True" using assms by auto
      show ?thesis unfolding x using True by simp
    next
      case False
      then have x: "x \<notin> subst_domain (\<sigma>)" .
      show ?thesis unfolding notin_subst_domain_imp_Var[OF x] if_cancel ..
    qed
  }
  then have "\<And>x.(if x \<in> V then \<sigma> x else Var x) = (if x \<in> subst_domain \<sigma> then \<sigma> x else Var x)" .
  then have "\<And>x.(\<lambda>x. if x \<in> V then \<sigma> x else Var x) x = (\<lambda>x. if x \<in> subst_domain \<sigma> then \<sigma> x else Var x) x" .
  then have "\<And>x. (\<lambda>x. if x \<in> V then \<sigma> x else Var x) x = \<sigma> x" by (auto simp: subst_domain_def)
  then have "(\<lambda>x. if x \<in> V then \<sigma> x else Var x) = \<sigma>" by (rule ext)
  then have "\<sigma> |s V = \<sigma>" by (simp add: subst_restrict_def)
  then show ?thesis .
qed

lemma subst_restrict_UNIV[simp]: "\<sigma> |s UNIV = \<sigma>" by (auto simp: subst_restrict_def)

lemma subst_restrict_empty[simp]: "\<sigma> |s {} = Var" by (simp add: subst_restrict_def)

lemma vars_term_subst_pow:
  "vars_term (t \<cdot> \<sigma>^^n) \<subseteq> vars_term t \<union> \<Union>(vars_term ` subst_range \<sigma>)" (is "_ \<subseteq> ?R t")
  unfolding vars_term_subst
proof (induct n arbitrary: t)
  case (Suc n t)
  show ?case
  proof
    fix x
    assume "x \<in> \<Union>(vars_term ` (\<sigma> ^^ Suc n) ` vars_term t)"
    then obtain y u where 1: "y \<in> vars_term t" "u = (\<sigma> ^^ Suc n) y" "x \<in> vars_term u"
      by auto
    from 1(2) have "u = \<sigma> y \<cdot> \<sigma> ^^ n" by (auto simp: subst_compose_def)
    from 1(3)[unfolded this, unfolded vars_term_subst]
    have "x \<in> \<Union>(vars_term ` (\<sigma> ^^ n) ` vars_term (\<sigma> y))" .
    with Suc[of "\<sigma> y"] have x: "x \<in> ?R (\<sigma> y)" by auto
    then show "x \<in> ?R t"
    proof
      assume "x \<in> vars_term (\<sigma> y)"
      then show ?thesis using 1(1) by (cases "\<sigma> y = Var y", auto simp: subst_domain_def)
    qed auto
  qed
qed auto

lemma coincidence_lemma:
  "t \<cdot> \<sigma> = t \<cdot> (\<sigma> |s vars_term t)"
  unfolding term_subst_eq_conv subst_restrict_def by auto

lemma subst_domain_vars_term_subset:
  "subst_domain (\<sigma>  |s  vars_term t) \<subseteq> vars_term t"
  by (auto simp: subst_domain_def subst_restrict_def)

lemma subst_restrict_single_Var [simp]:
  assumes "x \<notin> subst_domain \<sigma>" shows "\<sigma> |s {x} = Var"
proof -
  have A: "\<And>x. x \<notin> subst_domain \<sigma> \<Longrightarrow> \<sigma> x = Var x" by (simp add: subst_domain_def)
  have "\<sigma> |s {x} = (\<lambda>y. if y \<in> {x} then \<sigma> y else Var y)" by (simp add: subst_restrict_def)
  also have "\<dots> = (\<lambda>y. if y = x then \<sigma> y else Var y)" by simp
  also have "\<dots> = (\<lambda>y. if y = x then \<sigma> x else Var y)" by (simp cong: if_cong)
  also have "\<dots> = (\<lambda>y. if y = x then Var x else Var y)" unfolding A[OF assms] by simp
  also have "\<dots> = (\<lambda>y. if y = x then Var y else Var y)" by (simp cong: if_cong)
  also have "\<dots> = (\<lambda>y. Var y)" by simp
  finally show ?thesis by simp
qed

lemma subst_restrict_single_Var':
  assumes "x \<notin> subst_domain \<sigma>" and "\<sigma> |s V = Var" shows "\<sigma> |s ({x} \<union> V) = Var"
proof -
  have "(\<lambda>y. if y \<in> V then \<sigma> y else Var y) = (\<lambda>y. Var y)"
    using \<open>\<sigma> |s V = Var\<close>  by (simp add: subst_restrict_def)
  then have "(\<lambda>y. if y \<in> V then \<sigma> y else Var y) = (\<lambda>y. Var y)" by simp
  then have A: "\<And>y. (if y \<in> V then \<sigma> y else Var y) = Var y" by (rule fun_cong)
  {
    fix y
    have "(if y \<in> {x} \<union> V then \<sigma> y else Var y) = Var y"
    proof (cases "y = x")
      assume "y = x" then show ?thesis using \<open>x \<notin> subst_domain \<sigma>\<close> by (auto simp: subst_domain_def)
    next
      assume "y \<noteq> x" then show ?thesis using A by simp
    qed
  }
  then have "\<And>y. (if y \<in> {x} \<union> V then \<sigma> y else Var y) = Var y" by simp
  then show ?thesis by (auto simp: subst_restrict_def)
qed

lemma subst_restrict_empty_set:
  "finite V \<Longrightarrow> V \<inter> subst_domain \<sigma> = {} \<Longrightarrow> \<sigma> |s V = Var"
proof (induct rule: finite.induct)
  case (insertI V x)
  then have "V \<inter> subst_domain \<sigma> = {}" by simp
  with insertI have "\<sigma> |s V = Var" by simp
  then show ?case using insertI subst_restrict_single_Var'[where \<sigma> = \<sigma> and x = x and V = V] by simp
qed auto

lemma subst_restrict_Var: "x \<noteq> y \<Longrightarrow> Var y \<cdot> (\<sigma> |s (UNIV - {x})) = Var y \<cdot> \<sigma>"
  by (auto simp: subst_restrict_def)

lemma var_cond_stable:
  assumes "vars_term r \<subseteq> vars_term l"
  shows "vars_term (r \<cdot> \<mu>) \<subseteq> vars_term (l \<cdot> \<mu>)"
  unfolding vars_term_subst using assms by blast

lemma instance_no_supt_imp_no_supt:
  assumes "\<not> s \<cdot> \<sigma> \<rhd> t \<cdot> \<sigma>"
  shows "\<not> s \<rhd> t"
proof 
  assume "s \<rhd> t"
  hence "s \<cdot> \<sigma> \<rhd> t \<cdot> \<sigma>" by (rule supt_subst)
  with assms show "False" by simp
qed

lemma subst_image_subterm:
  assumes "x \<in> vars_term (Fun f ss)"
  shows "Fun f ss \<cdot> \<sigma> \<rhd> \<sigma> x"
proof -
  have "Fun f ss \<unrhd> Var x" using supteq_Var[OF assms(1)] .
  then have "Fun f ss \<rhd> Var x" by cases auto
  from supt_subst [OF this]
  show ?thesis by simp
qed

lemma funas_term_subst_pow:
  "funas_term (t \<cdot> \<sigma>^^n) \<subseteq> funas_term t \<union> \<Union>(funas_term ` subst_range \<sigma>)"
proof -
  {
    fix Xs
    have "\<Union>(funas_term ` (\<sigma> ^^ n) ` Xs) \<subseteq> \<Union>(funas_term ` subst_range \<sigma>)"
    proof (induct n arbitrary: Xs)
      case (Suc n Xs)
      show ?case (is "\<Union> ?L \<subseteq> ?R")
      proof (rule subsetI)
        fix f
        assume "f \<in> \<Union> ?L"
        then obtain x where "f \<in> funas_term ((\<sigma> ^^ Suc n) x)" by auto
        then have "f \<in> funas_term (\<sigma> x \<cdot> \<sigma> ^^ n)" by (auto simp: subst_compose_def)
        from this[unfolded funas_term_subst]
        show "f \<in> ?R" using Suc[of "vars_term (\<sigma> x)"]
          unfolding subst_range.simps subst_domain_def by (cases "\<sigma> x = Var x", auto)
      qed
    qed auto
  }
  then show ?thesis unfolding funas_term_subst by auto
qed

lemma funas_term_subterm_args:
  assumes sF: "funas_term s \<subseteq> F"
    and q: "q \<in> poss s"
  shows "\<Union>(funas_term ` set (args (s |_ q))) \<subseteq> F"
proof -
  from subt_at_imp_ctxt[OF q] obtain C where s: "s = C \<langle> s |_ q \<rangle>" by metis
  from sF arg_cong[OF this, of "funas_term"] have "funas_term (s |_ q) \<subseteq> F" by auto
  then show ?thesis by (cases "s |_ q", auto)
qed

lemma get_var_or_const: "\<exists> C t. s = C\<langle>t\<rangle> \<and> args t = []"
proof (induct s)
  case (Var y)
  show ?case by (rule exI[of _ Hole], auto)
next
  case (Fun f ts)
  show ?case
  proof (cases ts)
    case Nil
    show ?thesis unfolding Nil
      by (rule exI[of _ Hole], auto)
  next
    case (Cons s ss)
    then have "s \<in> set ts" by auto
    from Fun[OF this] obtain C where C: "\<exists> t. s = C\<langle>t\<rangle> \<and> args t = []" by auto
    show ?thesis unfolding Cons
      by (rule exI[of _ "More f [] C ss"], insert C, auto)
  qed
qed

lemma supteq_Var_id [simp]:
  assumes "Var x \<unrhd> s" shows "s = Var x"
  using assms by (cases)

lemma arg_not_term [simp]:
  assumes "t \<in> set ts" shows "Fun f ts \<noteq> t"
proof (rule ccontr)
  assume "\<not> Fun f ts \<noteq>  t"
  then have "size (Fun f ts) = size t" by simp
  moreover have "size t < size_list size ts" using assms by (induct ts) auto
  ultimately show False by simp
qed

lemma arg_subteq [simp]: "t \<in> set ts \<Longrightarrow> Fun f ts \<unrhd> t"
  by auto

lemma supt_imp_args:
  assumes "\<forall>t. s \<rhd> t \<longrightarrow> P t" 
  shows "\<forall>t\<in>set (args s). P t"
  using assms by (cases s) simp_all

lemma ctxt_apply_eq_False[simp]: "(More f ss1 D ss2)\<langle>t\<rangle> \<noteq> t" (is "?C\<langle>_\<rangle> \<noteq> _")
proof 
  assume eq: "?C\<langle>t\<rangle> = t" 
  have "?C \<noteq> \<box>" by auto
  from ctxt_supt[OF this eq[symmetric]]
  have "t \<rhd> t" .
  then show False by auto
qed

lemma supteq_imp_funs_term_subset: "t \<unrhd> s \<Longrightarrow> funs_term s \<subseteq> funs_term t"
  by (induct rule:supteq.induct) auto

lemma funs_term_subst: "funs_term (t \<cdot> \<sigma>) = funs_term t \<union> \<Union> ((\<lambda> x. funs_term (\<sigma> x)) ` (vars_term t))"
  by (induct t) auto

lemma set_set_cons:
  assumes "P x" and "\<And>y. y \<in> set xs \<Longrightarrow> P y"
  shows "y \<in> set (x # xs) \<Longrightarrow> P y"
  using assms by auto

lemma ctxt_power_compose_distr: "C ^ (m + n) = C ^ m \<circ>\<^sub>c C ^ n"
  by (induct m) (simp_all add: ac_simps)

lemma subst_apply_id':
  assumes "vars_term t \<inter> V = {}" 
  shows "t \<cdot> (\<sigma> |s V) = t"
  using assms
proof (induct t)
  case (Var x) then show ?case by (simp add: subst_restrict_def)
next
  case (Fun f ts)
  then have "\<forall>s\<in>set ts. s \<cdot> (\<sigma> |s V) = s" by auto
  with map_idI [of ts "\<lambda>t. t \<cdot> (\<sigma> |s V)"] show ?case by simp
qed

lemma subst_apply_ctxt_id:
  assumes "vars_ctxt C \<inter> V = {}" 
  shows "C \<cdot>\<^sub>c (\<sigma> |s V) = C"
  using assms
proof (induct C)
  case (More f ss1 D ss2)
  then have IH: "D \<cdot>\<^sub>c (\<sigma> |s V) = D" by auto
  from More have "\<forall>s\<in>set(ss1@ss2). vars_term s \<inter> V = {}" by auto
  with subst_apply_id' have args: "\<forall>s\<in>set(ss1@ss2). s\<cdot>(\<sigma> |s V) = s" by best
  from args have "\<forall>s\<in>set ss1. s\<cdot>(\<sigma> |s V) = s" by simp
  with map_idI[of ss1 "\<lambda>t. t\<cdot>(\<sigma> |s V)"] have ss1: "map (\<lambda>s. s\<cdot>(\<sigma> |s V)) ss1 = ss1" by best
  from args have "\<forall>s\<in>set ss2. s\<cdot>(\<sigma> |s V) = s" by simp
  with map_idI[of ss2 "\<lambda>t. t\<cdot>(\<sigma> |s V)"] have ss2: "map (\<lambda>s. s\<cdot>(\<sigma> |s V)) ss2 = ss2" by best
  show ?case by (simp add: ss1 ss2 IH)
qed simp

lemma vars_term_Var_id: "vars_term o Var = (\<lambda>x. {x})"
  by (rule ext) simp

lemma ctxt_exhaust_rev[case_names Hole More]:
  assumes "C = \<box> \<Longrightarrow> P" and 
    "\<And>D f ss1 ss2. C = D \<circ>\<^sub>c (More f ss1 \<box> ss2) \<Longrightarrow> P" 
  shows "P"
proof (cases C)
  case Hole with assms show ?thesis by simp
next
  case (More g ts1 E ts2)
  then have "\<exists>D f ss1 ss2. C = D \<circ>\<^sub>c (More f ss1 \<box> ss2)"
  proof (induct E arbitrary: C g ts1 ts2)
    case Hole then have "C = \<box> \<circ>\<^sub>c (More g ts1 \<box> ts2)" by simp
    then show ?case by best
  next
    case (More h us1 F us2)
    from More(1)[of "More h us1 F us2"]
    obtain G i vs1 vs2 where IH: "More h us1 F us2 = G \<circ>\<^sub>c More i vs1 \<box> vs2" by force
    from More have "C = (More g ts1 \<box> ts2 \<circ>\<^sub>c G) \<circ>\<^sub>c More i vs1 \<box> vs2" unfolding IH by simp
    then show ?case by best
  qed
  then show ?thesis using assms by auto
qed

fun
  subst_extend :: "('f, 'v, 'w) gsubst \<Rightarrow> ('v \<times> ('f, 'w) term) list \<Rightarrow> ('f, 'v, 'w) gsubst"
  where
    "subst_extend \<sigma> vts = (\<lambda>x.
    (case map_of vts x of
      Some t \<Rightarrow> t
    | None   \<Rightarrow> \<sigma>(x)))"

lemma subst_extend_id:
  assumes "V \<inter> set vs = {}" and "vars_term t \<subseteq> V"
  shows "t \<cdot> subst_extend \<sigma> (zip vs ts) = t \<cdot> \<sigma>"
  using assms
proof (induct t)
  case (Var x) then show ?case
    using map_of_SomeD[of "zip vs ts" x]
    using set_zip_leftD [of x _ vs ts]
    using IntI [of x V "set vs"]
    using emptyE
    by (case_tac "map_of (zip vs ts) x") auto
qed auto

lemma funas_term_args:
  "\<Union>(funas_term ` set (args t)) \<subseteq> funas_term t"
  by (cases t) auto

lemma subst_extend_absorb:
  assumes "distinct vs" and "length vs = length ss"
  shows "map (\<lambda>t. t \<cdot> subst_extend \<sigma> (zip vs ss)) (map Var vs) = ss" (is "?ss = _")
proof -
  let ?\<sigma> = "subst_extend \<sigma> (zip vs ss)"
  from assms have "length vs \<le> length ss" by simp
  from assms have "length ?ss = length ss" by simp
  moreover have "\<forall>i<length ?ss. ?ss ! i = ss ! i"
  proof (intro allI impI)
    fix i assume "i < length ?ss"
    then have i: "i < length (map Var vs)" by simp
    then have len: "i < length vs" by simp
    have "?ss!i = (map Var vs ! i) \<cdot> ?\<sigma>" unfolding nth_map[OF i, of "\<lambda>t. t\<cdot>?\<sigma>"] by simp
    also have "\<dots> = Var(vs!i)\<cdot>?\<sigma>" unfolding nth_map[OF len] by simp
    also have "\<dots> = (case map_of (zip vs ss) (vs ! i) of None \<Rightarrow> \<sigma> (vs ! i) | Some t \<Rightarrow> t)" by simp
    also have "\<dots> = ss ! i" using \<open>distinct vs\<close> \<open>length vs \<le> length ss\<close> len 
      by (simp add: assms(2) map_of_zip_nth)
    finally show "?ss!i = ss!i" by simp
  qed
  ultimately show ?thesis by (metis nth_equalityI)
qed

abbreviation "map_funs_term f \<equiv> term.map_term f (\<lambda>x. x)"
abbreviation "map_funs_ctxt f \<equiv> ctxt.map_ctxt f (\<lambda>x. x)"

lemma funs_term_map_funs_term_id: "(\<And> f. f \<in> funs_term t \<Longrightarrow> h f = f) \<Longrightarrow> map_funs_term h t = t"
proof (induct t)
  case (Fun f ts)
  then have "\<And> t. t \<in> set ts \<Longrightarrow> map_funs_term h t = t" by auto
  with Fun(2)[of f] show ?case
    by (auto intro: nth_equalityI)
qed simp

lemma funs_term_map_funs_term:
  "funs_term (map_funs_term h t) \<subseteq> range h"
  by (induct t) auto

fun map_funs_subst :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('g, 'v) subst" where
  "map_funs_subst fg \<sigma> = (\<lambda>x. map_funs_term fg (\<sigma> x))"

lemma map_funs_term_comp:
  "map_funs_term fg (map_funs_term gh t) = map_funs_term (fg \<circ> gh) t"
  by (induct t) simp_all

lemma map_funs_subst_distrib [simp]:
  "map_funs_term fg (t \<cdot> \<sigma>) = map_funs_term fg t \<cdot> map_funs_subst fg \<sigma>"
  by (induct t) simp_all

lemma size_map_funs_term [simp]:
  "size (map_funs_term fg t) = size t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts) auto
qed simp

lemma fold_ident [simp]: "Term_More.fold Var Fun t = t"
  by (induct t) (auto simp: map_ext [of _ "Term_More.fold Var Fun" id])

lemma map_funs_term_ident [simp]:
  "map_funs_term id t = t"
  by (induct t) (simp_all add: map_idI)

lemma ground_map_funs_term [simp]:
  "ground (map_funs_term fg t) = ground t"
  by (induct t) auto

lemma map_funs_term_power:
  fixes f :: "'f \<Rightarrow> 'f"
  shows "((map_funs_term f) ^^ n) = map_funs_term (f ^^ n)"
proof (rule sym, intro ext)
  fix t :: "('f,'v)term"
  show "map_funs_term (f ^^ n) t = (map_funs_term f ^^ n) t"
  proof (induct n)
    case 0
    show ?case by (simp add: term.map_ident)
  next
    case (Suc n)
    show ?case by (simp add: Suc[symmetric] map_funs_term_comp o_def)
  qed
qed

lemma map_funs_term_ctxt_distrib [simp]:
  "map_funs_term fg (C\<langle>t\<rangle>) = (map_funs_ctxt fg C)\<langle>map_funs_term fg t\<rangle>"
  by  (induct C) (auto)

text \<open>mapping function symbols (w)ith (a)rities taken into account (wa)\<close>

fun map_funs_term_wa :: "('f \<times> nat \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('g, 'v) term"
  where
    "map_funs_term_wa fg (Var x) = Var x" |
    "map_funs_term_wa fg (Fun f ts) = Fun (fg (f, length ts)) (map (map_funs_term_wa fg) ts)"

lemma map_funs_term_map_funs_term_wa:
  "map_funs_term (fg :: ('f \<Rightarrow> 'g)) = map_funs_term_wa (\<lambda> (f,n). (fg f))"
proof (intro ext)
  fix t :: "('f,'v)term"
  show "map_funs_term fg t = map_funs_term_wa (\<lambda> (f,n). fg f) t"
    by (induct t, auto)
qed

fun map_funs_ctxt_wa :: "('f \<times> nat \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('g, 'v) ctxt"
  where
    "map_funs_ctxt_wa fg \<box> = \<box>" |
    "map_funs_ctxt_wa fg (More f bef C aft) =
    More (fg (f, Suc (length bef + length aft))) (map (map_funs_term_wa fg) bef) (map_funs_ctxt_wa fg C) (map (map_funs_term_wa fg) aft)"

abbreviation map_funs_subst_wa :: "('f \<times> nat \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('g, 'v) subst" where
  "map_funs_subst_wa fg \<sigma> \<equiv> (\<lambda>x. map_funs_term_wa fg (\<sigma> x))"

lemma map_funs_term_wa_subst [simp]:
  "map_funs_term_wa fg (t \<cdot> \<sigma>) = map_funs_term_wa fg t \<cdot> map_funs_subst_wa fg \<sigma>"
  by (induct t, auto)

lemma map_funs_term_wa_ctxt [simp]:
  "map_funs_term_wa fg (C\<langle>t\<rangle>) = (map_funs_ctxt_wa fg C) \<langle>map_funs_term_wa fg t\<rangle>"
  by (induct C, auto)

lemma map_funs_term_wa_funas_term_id:
  assumes t: "funas_term t \<subseteq> F"
    and id: "\<And> f n. (f,n) \<in> F \<Longrightarrow> fg (f,n) = f"
  shows "map_funs_term_wa fg t = t"
  using t
proof (induct t)
  case (Fun f ss)
  then have IH: "\<And> s. s \<in> set ss \<Longrightarrow> map_funs_term_wa fg s = s" by auto
  from Fun(2) id have [simp]: "fg (f, length ss) = f" by simp
  show ?case by (simp, insert IH, induct ss, auto)
qed simp

lemma funas_term_map_funs_term_wa:
  "funas_term (map_funs_term_wa fg t) = (\<lambda> (f,n). (fg (f,n),n)) ` (funas_term t)"
  by (induct t) auto+

lemma notin_subst_restrict [simp]:
  assumes "x \<notin> V" shows "(\<sigma>  |s  V) x = Var x"
  using assms by (auto simp: subst_restrict_def)

lemma in_subst_restrict [simp]:
  assumes "x \<in> V" shows "(\<sigma>  |s  V) x = \<sigma> x"
  using assms by (auto simp: subst_restrict_def)

lemma coincidence_lemma':
  assumes "vars_term t \<subseteq> V"
  shows "t \<cdot> (\<sigma> |s V) = t \<cdot> \<sigma>"
  using assms by (metis in_mono in_subst_restrict term_subst_eq)

lemma vars_term_map_funs_term [simp]:
  "vars_term \<circ> map_funs_term (f :: ('f \<Rightarrow> 'g)) = vars_term"
proof
  fix t :: "('f,'v)term"
  show "(vars_term \<circ> map_funs_term f) t = vars_term t"
    by (induct t) (auto)
qed

lemma vars_term_map_funs_term2 [simp]:
  "vars_term (map_funs_term f t) = vars_term t"
  using fun_cong [OF vars_term_map_funs_term, of f t]
  by (simp del: vars_term_map_funs_term)

lemma map_funs_term_wa_ctxt_split:
  assumes "map_funs_term_wa fg s = lC\<langle>lt\<rangle>"
  shows "\<exists> C t. s = C\<langle>t\<rangle> \<and> map_funs_term_wa fg t = lt \<and> map_funs_ctxt_wa fg C = lC"
  using assms
proof (induct lC arbitrary: s)
  case Hole
  show ?case
    by (rule exI[of _ Hole], insert Hole, auto)
next
  case (More lf lbef lC laft s)
  from More(2) obtain fs ss where s: "s = Fun fs ss" by (cases s, auto)
  note More = More[unfolded s, simplified]
  let ?lb = "length lbef"
  let ?la = "length laft"
  let ?n = "Suc (?lb + ?la)"
  let ?m = "map_funs_term_wa fg"
  from More(2) have rec: "map ?m ss = lbef @ lC\<langle>lt\<rangle> # laft"
    and lf: "lf = fg (fs,length ss)" by blast+
  from arg_cong[OF rec, of length] have len: "length ss = ?n" by auto
  then have lb: "?lb < length ss" by auto
  note ss = id_take_nth_drop[OF this]
  from rec ss have "map ?m (take ?lb ss @ ss ! ?lb # drop (Suc ?lb) ss) = lbef @ lC\<langle>lt\<rangle> # laft" by auto
  then have id: "take ?lb (map ?m ss) @ ?m (ss ! ?lb) # drop (Suc ?lb) (map ?m ss) = lbef @ lC\<langle>lt\<rangle> # laft"
    (is "?l1 @ ?l2 # ?l3 = ?r1 @ ?r2 # ?r3")
    unfolding take_map drop_map
    by auto
  from len have len2: "\<And> P. length ?l1 = length ?r1 \<or> P"
    unfolding length_take by auto
  from id[unfolded List.append_eq_append_conv[OF len2]]
  have id: "?l1 = ?r1" "?l2 = ?r2" "?l3 = ?r3" by auto
  from More(1)[OF id(2)] obtain C t where sb: "ss ! ?lb = C\<langle>t\<rangle>" and map: "map_funs_term_wa fg t = lt" and ma: "map_funs_ctxt_wa fg C = lC" by auto
  let ?C = "More fs (take ?lb ss) C (drop (Suc ?lb) ss)"
  have s: "s = ?C\<langle>t\<rangle>"
    unfolding s using ss[unfolded sb] by simp
  have len3: "Suc (length (take ?lb ss) + length (drop (Suc ?lb) ss)) = length ss"
    unfolding length_take length_drop len by auto
  show ?case
  proof (intro exI conjI, rule s, rule map)
    show "map_funs_ctxt_wa fg ?C = More lf lbef lC laft"
      unfolding map_funs_ctxt_wa.simps
      unfolding len3
      using id ma lf
      unfolding take_map drop_map
      by auto
  qed
qed

lemma subst_extend_flat_ctxt:
  assumes dist: "distinct vs"
    and len1: "length(take i (map Var vs)) = length ss1"
    and len2: "length(drop (Suc i) (map Var vs)) = length ss2"
    and i: "i < length vs"
  shows "More f (take i (map Var vs)) \<box> (drop (Suc i) (map Var vs)) \<cdot>\<^sub>c subst_extend \<sigma> (zip (take i vs@drop (Suc i) vs) (ss1@ss2)) = More f ss1 \<box> ss2"
proof -
  let ?V = "map Var vs"
  let ?vs1 = "take i vs" and ?vs2 = "drop (Suc i) vs"
  let ?ss1 = "take i ?V" and ?ss2 = "drop (Suc i) ?V"
  let ?\<sigma> = "subst_extend \<sigma> (zip (?vs1@?vs2) (ss1@ss2))"
  from len1 and len2 have len: "length(?vs1@?vs2) = length(ss1@ss2)" using i by simp
  from dist i have "distinct(?vs1@?vs2)" 
    by (simp add: set_take_disj_set_drop_if_distinct)
  from subst_extend_absorb[OF this len,of "\<sigma>"]
  have map: "map (\<lambda>t. t\<cdot>?\<sigma>) (?ss1@?ss2) = ss1@ss2" unfolding take_map drop_map map_append .
  from len1 and map have "map (\<lambda>t. t\<cdot>?\<sigma>) ?ss1 = ss1" by auto
  moreover from len2 and map have "map (\<lambda>t. t\<cdot>?\<sigma>) ?ss2 = ss2" by auto
  ultimately show ?thesis by simp
qed

lemma subst_extend_flat_ctxt'':
  assumes dist: "distinct vs"
    and len1: "length(take i (map Var vs)) = length ss1"
    and len2: "length(drop i (map Var vs)) = length ss2"
    and i: "i < length vs"
  shows "More f (take i (map Var vs)) \<box> (drop i (map Var vs)) \<cdot>\<^sub>c subst_extend \<sigma> (zip (take i vs@drop i vs) (ss1@ss2)) = More f ss1 \<box> ss2"
proof -
  let ?V = "map Var vs"
  let ?vs1 = "take i vs" and ?vs2 = "drop i vs"
  let ?ss1 = "take i ?V" and ?ss2 = "drop i ?V"
  let ?\<sigma> = "subst_extend \<sigma> (zip (?vs1@?vs2) (ss1@ss2))"
  from len1 and len2 have len: "length(?vs1@?vs2) = length(ss1@ss2)" using i by simp
  have "distinct(?vs1@?vs2)" using dist unfolding append_take_drop_id by simp
  from subst_extend_absorb[OF this len,of "\<sigma>"]
  have map: "map (\<lambda>t. t\<cdot>?\<sigma>) (?ss1@?ss2) = ss1@ss2" unfolding take_map drop_map map_append .
  from len1 and map have "map (\<lambda>t. t\<cdot>?\<sigma>) ?ss1 = ss1" unfolding map_append by auto
  moreover from len2 and map have "map (\<lambda>t. t\<cdot>?\<sigma>) ?ss2 = ss2" unfolding map_append by auto
  ultimately show ?thesis by simp
qed

lemma distinct_map_Var:
  assumes "distinct xs" shows "distinct (map Var xs)"
  using assms by (induct xs) auto

lemma variants_imp_is_Var:
  assumes "s \<cdot> \<sigma> = t" and "t \<cdot> \<tau> = s"
  shows "\<forall>x\<in>vars_term s. is_Var (\<sigma> x)"
  using assms
proof (induct s arbitrary: t)
  case (Var x)
  then show ?case by (cases "\<sigma> x") auto
next
  case (Fun f ts)
  then show ?case
    by (auto simp: o_def) (metis map_eq_conv map_ident)
qed

text \<open>The range (in a functional sense) of a substitution.\<close>
definition subst_fun_range :: "('f, 'v, 'w) gsubst \<Rightarrow> 'w set"
  where
    "subst_fun_range \<sigma> = \<Union>(vars_term ` range \<sigma>)"

lemma subst_variants_imp_is_Var:
  assumes "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" and "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
  shows "\<forall>x\<in>subst_fun_range \<sigma>. is_Var (\<sigma>' x)"
  using assms by (auto simp: subst_compose_def subst_fun_range_def) (metis variants_imp_is_Var)

lemma variants_imp_image_vars_term_eq:
  assumes "s \<cdot> \<sigma> = t" and "t \<cdot> \<tau> = s"
  shows "(the_Var \<circ> \<sigma>) ` vars_term s = vars_term t"
  using assms
proof (induct s arbitrary: t)
  case (Var x)
  then show ?case by (cases t) auto
next
  case (Fun f ss)
  then have IH: "\<And>t. \<forall>i<length ss. (ss ! i) \<cdot> \<sigma> = t \<and> t \<cdot> \<tau> = ss ! i \<longrightarrow>
    (the_Var \<circ> \<sigma>) ` vars_term (ss ! i) = vars_term t"
    by (auto simp: o_def)
  from Fun.prems have t: "t = Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ss)"
    and ss: "ss = map (\<lambda>t. t \<cdot> \<sigma> \<cdot> \<tau>) ss" by (auto simp: o_def)
  have "\<forall>i<length ss. (the_Var \<circ> \<sigma>) ` vars_term (ss ! i) = vars_term (ss ! i \<cdot> \<sigma>)"
  proof (intro allI impI)
    fix i
    assume *: "i < length ss"
    have "(ss ! i) \<cdot> \<sigma> = (ss ! i) \<cdot> \<sigma>" by simp
    moreover have "(ss ! i) \<cdot> \<sigma> \<cdot> \<tau> = ss ! i"
      using * by (subst (2) ss) simp
    ultimately show "(the_Var \<circ> \<sigma>) ` vars_term (ss ! i) = vars_term ((ss ! i) \<cdot> \<sigma>)"
      using IH and * by blast
  qed
  then have "\<forall>s\<in>set ss. (the_Var \<circ> \<sigma>) ` vars_term s = vars_term (s \<cdot> \<sigma>)" by (metis in_set_conv_nth)
  then show ?case by (simp add: o_def t image_UN)
qed

lemma terms_to_vars:
  assumes "\<forall>t\<in>set ts. is_Var t"
  shows "\<Union>(set (map vars_term ts)) = set (map the_Var ts)"
  using assms by (induct ts) auto

lemma Var_the_Var_id:
  assumes "\<forall>t\<in>set ts. is_Var t"
  shows "map Var (map the_Var ts) = ts"
  using assms by (induct ts) auto

lemma distinct_the_vars:
  assumes "\<forall>t\<in>set ts. is_Var t"
    and "distinct ts"
  shows "distinct (map the_Var ts)"
  using assms by (induct ts) auto

lemma map_funs_term_eq_imp_map_funs_term_map_vars_term_eq:
  "map_funs_term fg s = map_funs_term fg t \<Longrightarrow> map_funs_term fg (map_vars_term vw s) = map_funs_term fg (map_vars_term vw t)"
proof (induct s arbitrary: t)
  case (Var x t)
  then show ?case by (cases t, auto)
next
  case (Fun f ss t)
  then obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  from Fun(2)[unfolded t, simplified]
  have f: "fg f = fg g" and ss: "map (map_funs_term fg) ss = map (map_funs_term fg) ts" by auto
  from arg_cong[OF ss, of length] have "length ss = length ts" by simp
  from this ss Fun(1) have "map (map_funs_term fg \<circ> map_vars_term vw) ss = map (map_funs_term fg \<circ> map_vars_term vw) ts"
    by (induct ss ts rule: list_induct2, auto)
  then show ?case unfolding t by (simp add: f)
qed

lemma var_type_conversion:
  assumes inf: "infinite (UNIV :: 'v set)"
    and fin: "finite (T :: ('f, 'w) terms)"
  shows "\<exists> (\<sigma> :: ('f, 'w, 'v) gsubst) \<tau>. \<forall>t\<in>T. t = t \<cdot> \<sigma> \<cdot> \<tau>"
proof -
  obtain V where V: "V = \<Union>(vars_term ` T)" by auto
  have fin: "finite V" unfolding V
    by (rule, rule, rule fin,
        insert finite_vars_term, auto)
  from finite_imp_inj_to_nat_seg[OF fin] obtain to_nat :: "'w \<Rightarrow> nat" and n :: nat
    where to_nat: "to_nat ` V = {i. i < n}" "inj_on to_nat V" by blast+
  from infinite_countable_subset[OF inf] obtain of_nat :: "nat \<Rightarrow> 'v" where
    of_nat: "range of_nat \<subseteq> UNIV" "inj of_nat"  by auto
  let ?conv = "\<lambda> v. of_nat (to_nat v)"
  have inj: "inj_on ?conv V" using of_nat(2) to_nat(2) unfolding inj_on_def by auto
  let ?rev = "the_inv_into V ?conv"
  note rev = the_inv_into_f_eq[OF inj]
  obtain \<sigma> where \<sigma>: "\<sigma> = (\<lambda> v. Var (?conv v) :: ('f,'v)term)" by simp
  obtain \<tau> where \<tau>: "\<tau> = (\<lambda> v. Var (?rev v) :: ('f,'w)term)" by simp
  show ?thesis
  proof (rule exI[of _ \<sigma>], rule exI[of _ \<tau>], intro ballI)
    fix t
    assume t: "t \<in> T"
    have "t \<cdot> \<sigma> \<cdot> \<tau> = t \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)" by simp
    also have "... = t \<cdot> Var"
    proof (rule term_subst_eq)
      fix x
      assume "x \<in> vars_term t"
      with t have x: "x \<in> V" unfolding V by auto
      show "(\<sigma> \<circ>\<^sub>s \<tau>) x = Var x" unfolding \<sigma> \<tau> subst_compose_def
          eval_term.simps term.simps
        by (rule rev[OF refl x])
    qed
    finally show "t = t \<cdot> \<sigma> \<cdot> \<tau>" by simp
  qed
qed

text \<open>combine two substitutions via sum-type\<close>
fun
  merge_substs :: "('f, 'u, 'v) gsubst \<Rightarrow> ('f, 'w, 'v) gsubst \<Rightarrow> ('f, 'u + 'w, 'v) gsubst"
  where
    "merge_substs \<sigma> \<tau> = (\<lambda>x.
    (case x of
      Inl y \<Rightarrow> \<sigma> y
    | Inr y \<Rightarrow> \<tau> y))"

lemma merge_substs_left:
  "map_vars_term Inl s \<cdot> (merge_substs \<sigma> \<delta>) = s \<cdot> \<sigma>"
  by (induct s) auto

lemma merge_substs_right:
  "map_vars_term Inr s \<cdot> (merge_substs \<sigma> \<delta>) = s \<cdot> \<delta>"
  by (induct s) auto

fun map_vars_subst_ran :: "('w \<Rightarrow> 'u) \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'v, 'u) gsubst"
  where
    "map_vars_subst_ran m \<sigma> = (\<lambda>v. map_vars_term m (\<sigma> v))"

lemma map_vars_subst_ran:
  shows "map_vars_term m (t \<cdot> \<sigma>) = t \<cdot> map_vars_subst_ran m \<sigma>"
  by (induct t) (auto)

lemma size_subst: "size t \<le> size (t \<cdot> \<sigma>)"
proof (induct t)
  case (Var x)
  then show ?case by (cases "\<sigma> x") auto
next
  case (Fun f ss)
  then show ?case
    by (simp add: o_def, induct ss, force+)
qed

lemma eq_ctxt_subst_iff [simp]:
  "(t = C\<langle>t \<cdot> \<sigma>\<rangle>) \<longleftrightarrow> C = \<box> \<and> (\<forall>x\<in>vars_term t. \<sigma> x = Var x)" (is "?L = ?R")
proof
  assume t: "?L"
  then have "size t = size (C\<langle>t \<cdot> \<sigma>\<rangle>)" by simp
  with size_ne_ctxt [of C "t \<cdot> \<sigma>"] and size_subst [of t \<sigma>]
  have [simp]: "C = \<box>" by auto
  have "\<forall>x\<in>vars_term t. \<sigma> x = Var x" using t and term_subst_eq_conv [of t Var] by simp
  then show ?R by auto
next
  assume ?R
  then show ?L using term_subst_eq_conv [of t Var] by simp
qed

lemma Fun_Nil_supt[elim!]: "Fun f [] \<rhd> t \<Longrightarrow> P" by auto

lemma map_vars_term_vars_term:
  assumes "\<And> x. x \<in> vars_term t \<Longrightarrow> f x = g x"
  shows "map_vars_term f t = map_vars_term g t"
  using assms
proof (induct t)
  case (Fun h ts)
  {
    fix t
    assume t: "t \<in> set ts"
    with Fun(2) have "\<And> x. x \<in> vars_term t \<Longrightarrow> f x = g x"
      by auto
    from Fun(1)[OF t this] have "map_vars_term f t = map_vars_term g t" by simp
  }
  then show ?case by auto
qed simp

lemma map_funs_term_ctxt_decomp:
  assumes "map_funs_term fg t = C\<langle>s\<rangle>"
  shows "\<exists> D u. C = map_funs_ctxt fg D \<and> s = map_funs_term fg u \<and> t = D\<langle>u\<rangle>"
  using assms
proof (induct C arbitrary: t)
  case Hole
  show ?case
    by (rule exI[of _ Hole], rule exI[of _ t], insert Hole, auto)
next
  case (More g bef C aft)
  from More(2) obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from More(2)[unfolded t] have f: "fg f = g" and ts: "map (map_funs_term fg) ts = bef @ C\<langle>s\<rangle> # aft" (is "?ts = ?bca") by auto
  from ts have "length ?ts = length ?bca" by auto
  then have len: "length ts = length ?bca" by auto
  let ?i = "length bef"
  from len have i: "?i < length ts" by auto
  from arg_cong[OF ts, of "\<lambda> xs. xs ! ?i"] len 
  have "map_funs_term fg (ts ! ?i) = C\<langle>s\<rangle>" by auto
  from More(1)[OF this] obtain D u where D: "C = map_funs_ctxt fg D" and
    u: "s = map_funs_term fg u" and id: "ts ! ?i = D\<langle>u\<rangle>" by auto
  from ts have "take ?i ?ts = take ?i ?bca" by simp
  also have "... = bef" by simp
  finally have bef: "map (map_funs_term fg) (take ?i ts) = bef" by (simp add: take_map)
  from ts have "drop (Suc ?i) ?ts = drop (Suc ?i) ?bca" by simp
  also have "... = aft" by simp
  finally have aft: "map (map_funs_term fg) (drop (Suc ?i) ts) = aft" by (simp add:drop_map)
  let ?bda = "take ?i ts @ D\<langle>u\<rangle> # drop (Suc ?i) ts"
  show ?case
  proof (rule exI[of _ "More f (take ?i ts) D (drop (Suc ?i) ts)"],
      rule exI[of _ u], simp add: u f D bef aft t)
    have "ts = take ?i ts @ ts ! ?i # drop (Suc ?i) ts"
      by (rule id_take_nth_drop[OF i])
    also have "... = ?bda" by (simp add: id)
    finally show "ts = ?bda" .
  qed
qed

lemma funas_term_map_vars_term [simp]:
  "funas_term (map_vars_term \<tau> t) = funas_term t"
  by (induct t) auto

lemma funs_term_funas_term:
  "funs_term t = fst ` (funas_term t)"
  by (induct t) auto

lemma funas_term_map_funs_term:
  "funas_term (map_funs_term fg t) = (\<lambda> (f,n). (fg f,n)) ` (funas_term t)"
  by (induct t) auto+

lemma supt_imp_arg_or_supt_of_arg:
  assumes "Fun f ss \<rhd> t"
  shows "t \<in> set ss \<or> (\<exists>s \<in> set ss. s \<rhd> t)"
  using assms by (rule supt.cases) auto

lemma supt_Fun_imp_arg_supteq:
  assumes "Fun f ss \<rhd> t" shows "\<exists>s \<in> set ss. s \<unrhd> t"
  using assms by (cases rule: supt.cases) auto

lemma subt_iff_eq_or_subt_of_arg:
  assumes "s = Fun f ss"
  shows "{t. s \<unrhd> t} = ((\<Union>u \<in> set ss. {t. u \<unrhd> t})\<union>{s})"
  using assms proof (induct s)
  case (Var x) then show ?case by auto
next
  case (Fun g ts)
  then have "g = f" and "ts = ss" by auto
  show ?case
  proof
    show "{a. Fun g ts \<unrhd> a} \<subseteq> (\<Union>u\<in>set ss. {a. u \<unrhd> a}) \<union> {Fun g ts}"
    proof
      fix x
      assume "x \<in> {a. Fun g ts \<unrhd> a}"
      then have "Fun g ts \<unrhd> x" by simp
      then have "Fun g ts \<rhd> x \<or> Fun g ts = x" by auto
      then show "x \<in> (\<Union>u\<in>set ss. {a. u \<unrhd>a}) \<union> {Fun g ts}"
      proof
        assume "Fun g ts \<rhd> x"
        then obtain u where "u \<in> set ts" and "u \<unrhd> x" using supt_Fun_imp_arg_supteq by best
        then have "x \<in> {a. u \<unrhd> a}" by simp
        with \<open>u \<in> set ts\<close> have "x \<in> (\<Union>u\<in>set ts. {a. u \<unrhd> a})" by auto
        then show ?thesis unfolding \<open>ts = ss\<close> by simp
      next
        assume "Fun g ts = x" then show ?thesis by simp
      qed
    qed
  next
    show "(\<Union>u\<in>set ss. {a. u \<unrhd> a}) \<union> {Fun g ts} \<subseteq> {a. Fun g ts \<unrhd> a}"
    proof
      fix x
      assume "x \<in> (\<Union>u\<in>set ss. {a. u \<unrhd> a}) \<union> {Fun g ts}"
      then have "x \<in> (\<Union>u\<in>set ss. {a. u \<unrhd> a}) \<or> x = Fun g ts" by auto
      then show "x \<in> {a. Fun g ts \<unrhd> a}"
      proof
        assume "x \<in> (\<Union>u\<in>set ss. {a. u \<unrhd> a})"
        then obtain u where "u \<in> set ss" and "u \<unrhd> x" by auto
        then show ?thesis unfolding \<open>ts = ss\<close> by auto
      next
        assume "x = Fun g ts" then show ?thesis by auto
      qed
    qed
  qed
qed

text \<open>The set of subterms of a term is finite.\<close>
lemma finite_subterms: "finite {s. t \<unrhd> s}"
proof (induct t)
  case (Var x)
  then have "\<And>s. (Var x \<unrhd> s) = (Var x = s)" using supteq.cases by best
  then show ?case unfolding \<open>\<And>s. (Var x \<unrhd> s) = (Var x = s)\<close> by simp
next
  case (Fun f ss)
  have "Fun f ss = Fun f ss" by simp
  from Fun show ?case
    unfolding subt_iff_eq_or_subt_of_arg[OF \<open>Fun f ss = Fun f ss\<close>] by auto
qed

lemma Fun_supteq: "Fun f ts \<unrhd> u \<longleftrightarrow> Fun f ts = u \<or> (\<exists>t\<in>set ts. t \<unrhd> u)"
  using subt_iff_eq_or_subt_of_arg[of "Fun f ts" f ts] by auto

lemma subst_ctxt_distr: "s = C\<langle>t\<rangle>\<cdot>\<sigma> \<Longrightarrow> \<exists>D. s = D\<langle>t\<cdot>\<sigma>\<rangle>"
  using subst_apply_term_ctxt_apply_distrib by auto

lemma ctxt_of_pos_term_subst:
  assumes "p \<in> poss t"
  shows "ctxt_of_pos_term p (t \<cdot> \<sigma>) = ctxt_of_pos_term p t \<cdot>\<^sub>c \<sigma>"
  using assms
proof (induct p arbitrary: t)
  case (Cons i p t)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)" by (cases t, auto)
  note id = id_take_nth_drop[OF i, symmetric]
  with t have t: "t = Fun f (take i ts @ ts ! i # drop (Suc i) ts)" by auto
  from i have i': "min (length ts) i = i" by simp
  show ?case unfolding t using Cons(1)[OF p, symmetric] i'
    by (simp add: id, insert i, auto simp: take_map drop_map)
qed simp

lemma subt_at_ctxt_of_pos_term:
  assumes t: "(ctxt_of_pos_term p t)\<langle>u\<rangle> = t" and p: "p \<in> poss t"
  shows "t |_ p = u"
proof -
  let ?C = "ctxt_of_pos_term p t"
  from t and ctxt_supt_id [OF p] have "?C\<langle>u\<rangle> = ?C\<langle>t |_ p\<rangle>" by simp
  then show ?thesis by simp
qed

lemma subst_ext:
  assumes "\<forall>x\<in>V. \<sigma> x = \<tau> x" shows "\<sigma> |s V = \<tau> |s V"
proof
  fix x show "(\<sigma> |s V) x = (\<tau> |s V) x" using assms
    unfolding subst_restrict_def by (cases "x \<in> V") auto
qed

abbreviation "map_vars_ctxt f \<equiv> ctxt.map_ctxt (\<lambda>x. x) f"

lemma map_vars_term_ctxt_commute:
  "map_vars_term m (c\<langle>t\<rangle>) = (map_vars_ctxt m c)\<langle>map_vars_term m t\<rangle>"
  by (induct c) auto

lemma map_vars_term_inj_compose:
  assumes inj: "\<And> x. n (m x) = x"
  shows "map_vars_term n (map_vars_term m t) = t"
  unfolding map_vars_term_compose o_def inj by (auto simp: term.map_ident)

lemma inj_map_vars_term_the_inv:
  assumes "inj f"
  shows "map_vars_term (the_inv f) (map_vars_term f t) = t"
  unfolding map_vars_term_compose o_def the_inv_f_f[OF assms]
  by (simp add: term.map_ident)

lemma map_vars_ctxt_subst:
  "map_vars_ctxt m (C \<cdot>\<^sub>c \<sigma>) = C \<cdot>\<^sub>c map_vars_subst_ran m \<sigma>"
  by (induct C) (auto simp: map_vars_subst_ran)

lemma poss_map_vars_term [simp]:
  "poss (map_vars_term f t) = poss t"
  by (induct t) auto

lemma map_vars_term_subt_at [simp]:
  "p \<in> poss t \<Longrightarrow> map_vars_term f (t |_ p) = (map_vars_term f t) |_ p"
proof (induct p arbitrary: t)
  case Nil show ?case by auto
next
  case (Cons i p t)
  from Cons(2) obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  from Cons show ?case unfolding t by auto
qed

lemma hole_pos_subst[simp]: "hole_pos (C \<cdot>\<^sub>c \<sigma>) = hole_pos C"
  by (induct C, auto)

lemma hole_pos_ctxt_compose[simp]: "hole_pos (C \<circ>\<^sub>c D) = hole_pos C @ hole_pos D"
  by (induct C, auto)

lemma subst_left_right: "t \<cdot> \<mu>^^n \<cdot> \<mu> = t \<cdot> \<mu> \<cdot> \<mu>^^n"
proof -
  have "t \<cdot> \<mu> ^^ n \<cdot> \<mu> = t \<cdot> (\<mu> ^^ n \<circ>\<^sub>s \<mu>)" by simp
  also have "... = t \<cdot> (\<mu> \<circ>\<^sub>s \<mu> ^^ n)"
    using subst_power_compose_distrib[of n "Suc 0" \<mu>] by auto
  finally show ?thesis by simp
qed

lemma subst_right_left: "t \<cdot> \<mu> \<cdot> \<mu>^^n = t \<cdot> \<mu>^^n \<cdot> \<mu>" unfolding subst_left_right ..

lemma subt_at_id_imp_eps:
  assumes p: "p \<in> poss t" and id: "t |_ p = t"
  shows "p = []"
proof (cases p)
  case (Cons i q)
  from subt_at_nepos_imp_supt[OF p[unfolded Cons], unfolded Cons[symmetric]
      , unfolded id] have False by simp
  then show ?thesis by auto
qed simp

lemma pos_into_subst:
  assumes t: "t \<cdot> \<sigma> = s" and p: "p \<in> poss s" and nt: "\<not> (p \<in> poss t \<and> is_Fun (t |_ p))"
  shows "\<exists>q q' x. p = q @ q' \<and> q \<in> poss t \<and> t |_ q = Var x"
  using p nt unfolding t[symmetric]
proof (induct t arbitrary: p)
  case (Var x)
  show ?case
    by (rule exI[of _ "[]"], rule exI[of _ p], rule exI[of _ x], insert Var, auto)
next
  case (Fun f ts)
  from Fun(3) obtain i q where p: "p = i # q" by (cases p, auto)
  note Fun = Fun[unfolded p]
  from Fun(2) have i: "i < length ts" and q: "q \<in> poss (ts ! i \<cdot> \<sigma>)" by auto
  then have mem: "ts ! i \<in> set ts" by auto
  from Fun(3) i have "\<not> (q \<in> poss (ts ! i) \<and> is_Fun (ts ! i |_ q))" by auto
  from Fun(1)[OF mem q this]
  obtain r r' x where q: "q = r @ r' \<and> r \<in> poss (ts ! i) \<and> ts ! i |_ r = Var x" by blast
  show ?case
    by (rule exI[of _ "i # r"], rule exI[of _ r'], rule exI[of _ x],
        unfold p, insert i q, auto)
qed

abbreviation (input) "replace_at t p s \<equiv> (ctxt_of_pos_term p t)\<langle>s\<rangle>"

(*may lead to nontermination as [simp]*)
lemma replace_at_ident:
  assumes "p \<in> poss t" and "t |_ p = s"
  shows "replace_at t p s = t"
  using assms by (metis ctxt_supt_id)

lemma ctxt_of_pos_term_append:
  assumes "p \<in> poss t"
  shows "ctxt_of_pos_term (p @ q) t = ctxt_of_pos_term p t \<circ>\<^sub>c ctxt_of_pos_term q (t |_ p)"
  using assms
proof (induct p arbitrary: t)
  case Nil show ?case by simp
next
  case (Cons i p t)
  from Cons(2) obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)" by (cases t, auto)
  from Cons(1)[OF p]
  show ?case unfolding t using i by auto
qed

lemma parallel_replace_at:
  fixes p1 :: pos
  assumes parallel: "p1 \<bottom> p2"
    and p1: "p1 \<in> poss t"
    and p2: "p2 \<in> poss t"
  shows "replace_at (replace_at t p1 s1) p2 s2 = replace_at (replace_at t p2 s2) p1 s1"
proof -
  from parallel_remove_prefix[OF parallel]
  obtain p i j q1 q2 where p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2"
    and ij: "i \<noteq> j" by blast
  from p1 p2 show ?thesis unfolding p1_id p2_id
  proof (induct p arbitrary: t)
    case (Cons k p)
    from Cons(3) obtain f ts where t: "t = Fun f ts" and k: "k < length ts" by (cases t, auto)
    note Cons = Cons[unfolded t]
    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"
    from Cons(2) Cons(3) have "?p1 \<in> poss (ts ! k)" "?p2 \<in> poss (ts ! k)" by auto
    from Cons(1)[OF this] have rec: "replace_at (replace_at (ts ! k) ?p1 s1) ?p2 s2 = replace_at (replace_at (ts ! k) ?p2 s2) ?p1 s1" .
    from k have min: "min (length ts) k = k" by simp
    show ?case unfolding t using rec min k
      by (simp add: nth_append)
  next
    case Nil
    from Nil(2) obtain f ts where t: "t = Fun f ts" and j: "j < length ts" by (cases t, auto)
    note Nil = Nil[unfolded t]
    from Nil have i: "i < length ts" by auto
    let ?p1 = "i # q1"
    let ?p2 = "j # q2"
    let ?s1 = "replace_at (ts ! i) q1 s1"
    let ?s2 = "replace_at (ts ! j) q2 s2"
    let ?ts1 = "ts[i := ?s1]"
    let ?ts2 = "ts[j := ?s2]"
    from j have j': "j < length ?ts1" by simp
    from i have i': "i < length ?ts2" by simp
    have "replace_at (replace_at t ?p1 s1) ?p2 s2 = replace_at (Fun f ?ts1) ?p2 s2" 
      unfolding t upd_conv_take_nth_drop[OF i] by simp
    also have "... = Fun f (?ts1[j := ?s2])"
      unfolding upd_conv_take_nth_drop[OF j'] using ij by simp
    also have "... = Fun f (?ts2[i := ?s1])" using list_update_swap[OF ij]
      by simp
    also have "... = replace_at (Fun f ?ts2) ?p1 s1"
      unfolding upd_conv_take_nth_drop[OF i'] using ij by simp
    also have "... = replace_at (replace_at t ?p2 s2) ?p1 s1" unfolding t
        upd_conv_take_nth_drop[OF j] by simp
    finally show ?case by simp
  qed
qed

lemma parallel_replace_at_subt_at:
  fixes p1 :: pos
  assumes parallel: "p1 \<bottom> p2"
    and p1: "p1 \<in> poss t"
    and p2: "p2 \<in> poss t"
  shows " (replace_at t p1 s1) |_ p2 = t |_ p2"
proof -
  from parallel_remove_prefix[OF parallel]
  obtain p i j q1 q2 where p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2"
    and ij: "i \<noteq> j" by blast
  from p1 p2 show ?thesis unfolding p1_id p2_id
  proof (induct p arbitrary: t)
    case (Cons k p)
    from Cons(3) obtain f ts where t: "t = Fun f ts" and k: "k < length ts" by (cases t, auto)
    note Cons = Cons[unfolded t]
    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"
    from Cons(2) Cons(3) have "?p1 \<in> poss (ts ! k)" "?p2 \<in> poss (ts ! k)" by auto
    from Cons(1)[OF this] have rec: "(replace_at (ts ! k) ?p1 s1) |_ ?p2 = (ts ! k) |_ ?p2" .
    from k have min: "min (length ts) k = k" by simp
    show ?case unfolding t using rec min k
      by (simp add: nth_append)
  next
    case Nil
    from Nil(2) obtain f ts where t: "t = Fun f ts" and j: "j < length ts" by (cases t, auto)
    note Nil = Nil[unfolded t]
    from Nil have i: "i < length ts" by auto
    let ?p1 = "i # q1"
    let ?p2 = "j # q2"
    let ?s1 = "replace_at (ts ! i) q1 s1"
    let ?ts1 = "ts[i := ?s1]"
    from j have j': "j < length ?ts1" by simp
    have "(replace_at t ?p1 s1) |_ ?p2 = (Fun f ?ts1) |_ ?p2" unfolding t upd_conv_take_nth_drop[OF i] by simp
    also have "... = ts ! j |_ q2" using ij by simp
    finally show ?case unfolding t by simp
  qed
qed

lemma parallel_poss_replace_at:
  fixes p1 :: pos
  assumes parallel: "p1 \<bottom> p2"
    and p1: "p1 \<in> poss t"
  shows "(p2 \<in> poss (replace_at t p1 s1)) = (p2 \<in> poss t)"
proof -
  from parallel_remove_prefix[OF parallel]
  obtain p i j q1 q2 where p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2"
    and ij: "i \<noteq> j" by blast
  from p1 show ?thesis unfolding p1_id p2_id
  proof (induct p arbitrary: t)
    case (Cons k p)
    from Cons(2) obtain f ts where t: "t = Fun f ts" and k: "k < length ts" by (cases t, auto)
    note Cons = Cons[unfolded t]
    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"
    from Cons(2) have "?p1 \<in> poss (ts ! k)" by auto
    from Cons(1)[OF this] have rec: "(?p2 \<in> poss (replace_at (ts ! k) ?p1 s1)) = (?p2 \<in> poss (ts ! k))" .
    from k have min: "min (length ts) k = k" by simp
    show ?case unfolding t using rec min k
      by (auto simp: nth_append)
  next
    case Nil
    then obtain f ts where t: "t = Fun f ts" and i: "i < length ts" by (cases t, auto)
    let ?p1 = "i # q1"
    let ?s1 = "replace_at (ts ! i) q1 s1"
    have "replace_at t ?p1 s1 = Fun f (ts[i := ?s1])" unfolding t upd_conv_take_nth_drop[OF i] by simp
    then show ?case unfolding t using ij by auto
  qed
qed

lemma replace_at_subt_at: "p \<in> poss t \<Longrightarrow> (replace_at t p s) |_ p = s"
  by (metis hole_pos_ctxt_of_pos_term subt_at_hole_pos)

lemma replace_at_below_poss:
  assumes p: "p' \<in> poss t" and le: "p \<le>\<^sub>p p'"
  shows "p \<in> poss (replace_at t p' s)"
proof -
  from le obtain p'' where p'': "p' = p @ p''" unfolding less_eq_pos_def by auto
  from p show ?thesis  unfolding p''
    by (metis hole_pos_ctxt_of_pos_term hole_pos_poss poss_append_poss)
qed

lemma ctxt_of_pos_term_replace_at_below:
  assumes p: "p \<in> poss t" and le: "p \<le>\<^sub>p p'"
  shows "ctxt_of_pos_term p (replace_at t p' u) = ctxt_of_pos_term p t"
proof -
  from le obtain p'' where p': "p' = p @ p''" unfolding less_eq_pos_def by auto
  from p show ?thesis unfolding p'
  proof (induct p arbitrary: t)
    case (Cons i p)
    from Cons(2) obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
      by (cases t, auto)
    from i have min: "min (length ts) i = i" by simp
    show ?case unfolding t using Cons(1)[OF p] i by (auto simp: nth_append min)
  next
    case Nil show ?case by simp
  qed
qed

lemma ctxt_of_pos_term_hole_pos[simp]:
  "ctxt_of_pos_term (hole_pos C) (C\<langle>t\<rangle>) = C"
  by (induct C) simp_all

lemma ctxt_poss_imp_ctxt_subst_poss:
  assumes p:"p' \<in> poss C\<langle>t\<rangle>" shows "p' \<in> poss C\<langle>t \<cdot> \<mu>\<rangle>"
proof(rule disjE[OF pos_cases[of p' "hole_pos C"]])
  assume "p' \<le>\<^sub>p hole_pos C"
  then show ?thesis using hole_pos_poss by (metis less_eq_pos_def poss_append_poss)
next
  assume or:"hole_pos C <\<^sub>p p' \<or> p' \<bottom> hole_pos C"
  show ?thesis proof(rule disjE[OF or])
    assume "hole_pos C <\<^sub>p p'"
    then obtain q where dec:"p' = hole_pos C @ q" unfolding less_pos_def less_eq_pos_def by auto
    with p have "q \<in> poss (t \<cdot> \<mu>)" using hole_pos_poss_conv poss_imp_subst_poss by auto
    then show ?thesis using dec hole_pos_poss_conv by auto
  next
    assume "p' \<bottom> hole_pos C"
    then have par:"hole_pos C \<bottom> p'" by (rule parallel_pos_sym)
    have aux:"hole_pos C \<in> poss C\<langle>t \<cdot> \<mu>\<rangle>" using hole_pos_poss by auto
    from p show ?thesis using parallel_poss_replace_at[OF par aux,unfolded ctxt_of_pos_term_hole_pos] by fast
  qed
qed

lemma var_pos_maximal:
  assumes pt:"p \<in> poss t" and x:"t |_ p = Var x" and "q \<noteq> []"
  shows "p @ q \<notin> poss t"
proof-
  from assms have "q \<notin> poss (Var x)" by force
  with poss_append_poss[of p q] pt x show ?thesis by simp
qed

text \<open>Positions in a context\<close>
definition possc :: "('f, 'v) ctxt \<Rightarrow> pos set"  where "possc C \<equiv> {p | p. \<forall>t. p \<in> poss C\<langle>t\<rangle>}"

lemma poss_imp_possc: "p \<in> possc C \<Longrightarrow> p \<in> poss C\<langle>t\<rangle>" unfolding possc_def by auto

lemma less_eq_hole_pos_in_possc:
  assumes pleq:"p \<le>\<^sub>p hole_pos C" shows "p \<in> possc C"
  unfolding possc_def
  using replace_at_below_poss[OF hole_pos_poss pleq, unfolded hole_pos_id_ctxt[OF refl]] by simp

lemma hole_pos_in_possc:"hole_pos C \<in> possc C"
  using less_eq_hole_pos_in_possc order_refl by blast

lemma par_hole_pos_in_possc:
  assumes par:"hole_pos C \<bottom> p" and ex:"p \<in> poss C\<langle>t\<rangle>" shows "p \<in> possc C"
  using parallel_poss_replace_at[OF par hole_pos_poss, unfolded hole_pos_id_ctxt[OF refl], of t] ex
  unfolding possc_def by simp

lemma possc_not_below_hole_pos:
  assumes "p \<in> possc (C::('a,'b) ctxt)" shows "\<not> (hole_pos C <\<^sub>p p)"
proof(rule notI)
  assume "hole_pos C <\<^sub>p p"
  then obtain r where p':"p = hole_pos C @ r" and r:"r \<noteq> []"
    unfolding less_pos_def less_eq_pos_def by auto
  fix x::'b from r have n:"r \<notin> poss (Var x)" using poss.simps(1) by auto
  from assms have "p \<in> (poss C\<langle>Var x\<rangle>)" unfolding possc_def by auto
  with this[unfolded p'] hole_pos_poss_conv[of C r] have "r \<in> poss (Var x)" by auto
  with n show False by simp
qed

lemma possc_subst_not_possc_not_poss:
  assumes y:"p \<in> possc (C \<cdot>\<^sub>c \<sigma>)" and n:"p \<notin> possc C" shows "p \<notin> poss C\<langle>t\<rangle>"
proof-
  from n obtain u where a:"p \<notin> poss C\<langle>u\<rangle>" unfolding possc_def by auto
  from possc_not_below_hole_pos[OF y] have b:"\<not> (hole_pos C <\<^sub>p p)"
    unfolding hole_pos_subst[of C \<sigma>] by auto
  from n a have c:"\<not> (p \<le>\<^sub>p hole_pos C)" unfolding less_pos_def using less_eq_hole_pos_in_possc by blast
  with pos_cases b have "p \<bottom> hole_pos C" by blast
  with par_hole_pos_in_possc[OF parallel_pos_sym[OF this]] n show "p \<notin> poss (C\<langle>t\<rangle>)" by fast
qed

text \<open>All proper terms in a context\<close>
fun ctxt_to_term_list :: "('f, 'v) ctxt \<Rightarrow> ('f, 'v) term list"
  where
    "ctxt_to_term_list Hole = []" |
    "ctxt_to_term_list (More f bef C aft) = ctxt_to_term_list C @ bef @ aft"

lemma ctxt_to_term_list_supt: "t \<in> set (ctxt_to_term_list C) \<Longrightarrow> C\<langle>s\<rangle> \<rhd> t"
proof (induct C)
  case (More f bef C aft)
  from More(2) have choice: "t \<in> set (ctxt_to_term_list C) \<or> t \<in> set bef \<or> t \<in> set aft" by simp
  {
    assume "t \<in> set bef \<or> t \<in> set aft"
    then have "t \<in> set (bef @ C\<langle>s\<rangle> # aft)" by auto
    then have ?case by auto
  }
  moreover
  {
    assume t: "t \<in> set (ctxt_to_term_list C)"
    have "(More f bef C aft)\<langle>s\<rangle> \<rhd> C\<langle>s\<rangle>" by auto
    moreover have "C\<langle>s\<rangle> \<rhd> t"
      by (rule More(1)[OF t])
    ultimately have ?case
      by (rule supt_trans)
  }
  ultimately show ?case using choice by auto
qed auto

lemma subteq_Var_imp_in_vars_term:
  "r \<unrhd> Var x \<Longrightarrow> x \<in> vars_term r"
proof (induct r rule: term.induct)
  case (Var y) 
  then have "x = y" by (cases rule: supteq.cases) auto
  then show ?case by simp
next
  case (Fun f ss)
  from \<open>Fun f ss \<unrhd> Var x\<close> have "(Fun f ss = Var x) \<or> (Fun f ss \<rhd> Var x)" by auto
  then show ?case
  proof
    assume "Fun f ss = Var x" then show ?thesis by auto
  next
    assume "Fun f ss \<rhd> Var x"
    then obtain s where "s \<in> set ss" and "s \<unrhd> Var x" using supt_Fun_imp_arg_supteq by best
    with Fun have "s \<unrhd> Var x \<Longrightarrow> x \<in> vars_term s" by best
    with \<open>s \<unrhd> Var x\<close> have "x \<in> vars_term s" by simp
    with \<open>s \<in> set ss\<close> show ?thesis by auto
  qed
qed

fun instance_term :: "('f, 'v) term \<Rightarrow> ('f set, 'v) term \<Rightarrow> bool"
  where
    "instance_term (Var x) (Var y) \<longleftrightarrow> x = y" |
    "instance_term (Fun f ts) (Fun fs ss) \<longleftrightarrow>
    f \<in> fs \<and> length ts = length ss \<and> (\<forall>i<length ts. instance_term (ts ! i) (ss ! i))" |
    "instance_term _ _ = False"

fun subt_at_ctxt :: "('f, 'v) ctxt \<Rightarrow> pos \<Rightarrow> ('f, 'v) ctxt" (infixl "|'_c" 67)
  where
    "C |_c [] = C" |
    "More f bef C aft |_c (i#p) = C |_c p"

lemma subt_at_subt_at_ctxt:
  assumes "hole_pos C = p @ q"
  shows "C\<langle>t\<rangle> |_ p = (C |_c p)\<langle>t\<rangle>"
  using assms
proof (induct p arbitrary: C)
  case (Cons i p)
  then obtain f bef D aft where C: "C = More f bef D aft" by (cases C, auto)
  from Cons(2) have "hole_pos D = p @ q" unfolding C by simp
  from Cons(1)[OF this] have id: "(D |_c p) \<langle>t\<rangle> = D\<langle>t\<rangle> |_ p" by simp
  show ?case unfolding C subt_at_ctxt.simps id using Cons(2) C by auto
qed simp

lemma hole_pos_subt_at_ctxt:
  assumes "hole_pos C = p @ q"
  shows "hole_pos (C |_c p) = q"
  using assms
proof (induct p arbitrary: C)
  case (Cons i p)
  then obtain f bef D aft where C: "C = More f bef D aft" by (cases C, auto)
  show ?case unfolding C subt_at_ctxt.simps
    by (rule Cons(1), insert Cons(2) C, auto)
qed simp

lemma subt_at_ctxt_compose[simp]: "(C \<circ>\<^sub>c D) |_c hole_pos C = D"
  by (induct C, auto)

lemma split_ctxt:
  assumes "hole_pos C = p @ q"
  shows "\<exists> D E. C = D \<circ>\<^sub>c E \<and> hole_pos D = p \<and> hole_pos E = q \<and> E = C |_c p"
  using assms
proof (induct p arbitrary: C)
  case Nil
  show ?case
    by (rule exI[of _ \<box>], rule exI[of _ C], insert Nil, auto)
next
  case (Cons i p)
  then obtain f bef C' aft where C: "C = More f bef C' aft" by (cases C, auto)
  from Cons(2) have "hole_pos C' = p @ q" unfolding C by simp
  from Cons(1)[OF this] obtain D E where C': "C' = D \<circ>\<^sub>c E"
    and p: "hole_pos D = p" and q: "hole_pos E = q" and E: "E = C' |_c p"
    by auto
  show ?case
    by (rule exI[of _ "More f bef D aft"], rule exI[of _ E], unfold C C',
        insert p[symmetric] q E Cons(2) C, simp)
qed

lemma ctxt_subst_id[simp]: "C \<cdot>\<^sub>c Var = C" by (induct C, auto)

text \<open>the strict subterm relation between contexts and terms\<close>
inductive_set
  suptc :: "(('f, 'v) ctxt \<times> ('f, 'v) term) set"
  where
    arg: "s \<in> set bef \<union> set aft \<Longrightarrow> s \<unrhd> t \<Longrightarrow> (More f bef C aft, t) \<in> suptc"
  |  ctxt: "(C,s) \<in> suptc \<Longrightarrow> (D \<circ>\<^sub>c C, s) \<in> suptc"

hide_const suptcp

abbreviation suptc_pred where "suptc_pred C t \<equiv> (C, t) \<in> suptc"

notation
  suptc_pred ("(_/ \<rhd>c _)" [56, 56] 55)

lemma suptc_subst: "C \<rhd>c s \<Longrightarrow> C \<cdot>\<^sub>c \<sigma> \<rhd>c s \<cdot> \<sigma>"
proof (induct rule: suptc.induct)
  case (arg s bef aft t f C)
  let ?s = "\<lambda> t. t \<cdot> \<sigma>"
  let ?m = "map ?s"
  have id: "More f bef C aft \<cdot>\<^sub>c \<sigma> = More f (?m bef) (C \<cdot>\<^sub>c \<sigma>) (?m aft)" by simp
  show ?case unfolding id
    by (rule suptc.arg[OF _ supteq_subst[OF arg(2)]],
        insert arg(1), auto)
next
  case (ctxt C s D)
  have id: "D \<circ>\<^sub>c C \<cdot>\<^sub>c \<sigma> = (D \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c (C \<cdot>\<^sub>c \<sigma>)" by simp
  show ?case unfolding id
    by (rule suptc.ctxt[OF ctxt(2)])
qed

lemma suptc_imp_supt: "C \<rhd>c s \<Longrightarrow> C\<langle>t\<rangle> \<rhd> s"
proof (induct rule: suptc.induct)
  case (arg s bef aft u f C)
  let ?C = "(More f bef C aft)"
  from arg(1) have "s \<in> set (args (?C\<langle>t\<rangle>))" by auto
  then have "?C\<langle>t\<rangle> \<rhd> s" by auto
  from supt_supteq_trans[OF this arg(2)]
  show ?case .
next
  case (ctxt C s D)
  have supteq: "(D \<circ>\<^sub>c C)\<langle>t\<rangle> \<unrhd> C\<langle>t\<rangle>" by auto
  from supteq_supt_trans[OF this ctxt(2)]
  show ?case .
qed

lemma suptc_supteq_trans: "C \<rhd>c s \<Longrightarrow> s \<unrhd> t \<Longrightarrow> C \<rhd>c t"
proof (induct rule: suptc.induct)
  case (arg s bef aft u f C)
  show ?case
    by (rule suptc.arg[OF arg(1) supteq_trans[OF arg(2) arg(3)]])
next
  case (ctxt C s D)
  then have supt: "C \<rhd>c t" by auto
  then show ?case by (rule suptc.ctxt)
qed

lemma supteq_suptc_trans: "C = D \<circ>\<^sub>c E \<Longrightarrow> E \<rhd>c s \<Longrightarrow> C \<rhd>c s"
  by (auto intro: suptc.ctxt)

hide_fact (open)
  suptcp.arg suptcp.cases suptcp.induct suptcp.intros suptc.arg suptc.ctxt

lemma supteq_ctxt_cases': "C \<langle> t \<rangle> \<unrhd> u \<Longrightarrow>
  C \<rhd>c u \<or> t \<unrhd> u \<or> (\<exists> D C'. C = D \<circ>\<^sub>c C' \<and> u = C' \<langle> t \<rangle> \<and> C' \<noteq> \<box>)"
proof (induct C)
  case (More f bef C aft)
  let ?C = "More f bef C aft"
  let ?ba = "bef @ C \<langle> t \<rangle> # aft"
  from More(2) have "Fun f ?ba \<unrhd> u" by simp
  then show ?case
  proof (cases rule: supteq.cases)
    case refl
    show ?thesis unfolding refl
      by (intro disjI2, rule exI[of _ Hole], rule exI[of _ ?C], auto)
  next
    case (subt v)
    show ?thesis
    proof (cases "v \<in> set bef \<union> set aft")
      case True
      from suptc.arg[OF this subt(2)]
      show ?thesis by simp
    next
      case False
      with subt have "C\<langle> t \<rangle> \<unrhd> u" by simp
      from More(1)[OF this]
      show ?thesis
      proof (elim disjE exE conjE)
        assume "C \<rhd>c u"
        from suptc.ctxt[OF this, of "More f bef \<box> aft"] show ?thesis by simp
      next
        fix D C'
        assume *: "C = D \<circ>\<^sub>c C'" "u = C'\<langle>t\<rangle>" "C' \<noteq> \<box>"
        show ?thesis
          by (intro disjI2 conjI, rule exI[of _ "More f bef D aft"], rule exI[of _ C'],
              insert *, auto)
      qed simp
    qed
  qed
qed simp

lemma supteq_ctxt_cases[consumes 1, case_names in_ctxt in_term sub_ctxt]: "C \<langle> t \<rangle> \<unrhd> u \<Longrightarrow>
  (C \<rhd>c u \<Longrightarrow> P) \<Longrightarrow>
  (t \<unrhd> u \<Longrightarrow> P) \<Longrightarrow>
  (\<And> D C'. C = D \<circ>\<^sub>c C' \<Longrightarrow> u = C' \<langle> t \<rangle> \<Longrightarrow> C' \<noteq> \<box> \<Longrightarrow> P) \<Longrightarrow> P"
  using supteq_ctxt_cases' by blast

definition vars_subst :: "('f, 'v) subst \<Rightarrow> 'v set"
  where
    "vars_subst \<sigma> = subst_domain \<sigma> \<union> \<Union>(vars_term ` subst_range \<sigma>)"

lemma range_vars_subst_compose_subset:
  "range_vars (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> (range_vars \<sigma> - subst_domain \<tau>) \<union> range_vars \<tau>" (is "?L \<subseteq> ?R")
proof
  fix x
  assume "x \<in> ?L"
  then obtain y where "y \<in> subst_domain (\<sigma> \<circ>\<^sub>s \<tau>)"
    and "x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y)" by (auto simp: range_vars_def)
  then show "x \<in> ?R"
  proof (cases)
    assume "y \<in> subst_domain \<sigma>" and "x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y)"
    moreover then obtain v where "v \<in> vars_term (\<sigma> y)"
      and "x \<in> vars_term (\<tau> v)" by (auto simp: subst_compose_def vars_term_subst)
    ultimately show ?thesis
      by (cases "v \<in> subst_domain \<tau>") (auto simp: range_vars_def subst_domain_def)
  qed (auto simp: range_vars_def subst_compose_def subst_domain_def)
qed

text \<open>
  A substitution is idempotent iff the variables in its range are disjoint from its domain. See also
  "Term Rewriting and All That" Lemma 4.5.7.
\<close>
lemma subst_idemp_iff:
  "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma> \<longleftrightarrow> subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
proof
  assume "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>"
  then have "\<And>x. \<sigma> x \<cdot> \<sigma> = \<sigma> x \<cdot> Var" by simp (metis subst_compose_def)
  then have *: "\<And>x. \<forall>y\<in>vars_term (\<sigma> x). \<sigma> y = Var y"
    unfolding term_subst_eq_conv by simp
  { fix x y
    assume "\<sigma> x \<noteq> Var x" and "x \<in> vars_term (\<sigma> y)"
    with * [of y] have False by simp }
  then show "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
    by (auto simp: subst_domain_def range_vars_def)
next
  assume "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
  then have *: "\<And>x y. \<sigma> x = Var x \<or> \<sigma> y = Var y \<or> x \<notin> vars_term (\<sigma> y)"
    by (auto simp: subst_domain_def range_vars_def)
  have "\<And>x. \<forall>y\<in>vars_term (\<sigma> x). \<sigma> y = Var y"
  proof
    fix x y
    assume "y \<in> vars_term (\<sigma> x)"
    with * [of y x] show "\<sigma> y = Var y" by auto
  qed
  then show "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>"
    by (simp add: subst_compose_def term_subst_eq_conv [symmetric])
qed

definition subst_compose' :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" where
  "subst_compose' \<sigma> \<tau> = (\<lambda> x. if (x \<in> subst_domain \<sigma>) then \<sigma> x \<cdot> \<tau> else Var x)"

lemma vars_subst_compose':
  assumes "vars_subst \<tau> \<inter> subst_domain \<sigma> = {}"
  shows "\<sigma> \<circ>\<^sub>s \<tau> = \<tau> \<circ>\<^sub>s (subst_compose' \<sigma> \<tau>)" (is "?l = ?r")
proof
  fix x
  show "?l x = ?r x"
  proof (cases "x \<in> subst_domain \<sigma>")
    case True
    with assms have nmem: "x \<notin> vars_subst \<tau>" by auto
    then have nmem: "x \<notin> subst_domain \<tau>" unfolding vars_subst_def by auto
    then have id: "\<tau> x = Var x" unfolding subst_domain_def by auto
    have "?l x = \<sigma> x \<cdot> \<tau>" unfolding subst_compose_def by simp
    also have  "... = ?r x" unfolding subst_compose'_def subst_compose_def using True unfolding id by simp
    finally show ?thesis .
  next
    case False
    then have l: "?l x = \<tau> x \<cdot> Var" unfolding subst_domain_def subst_compose_def by auto
    let ?\<sigma>\<tau> = "(\<lambda> x. if x \<in> subst_domain \<sigma> then \<sigma> x \<cdot> \<tau> else Var x)"
    have r: "?r x = \<tau> x \<cdot> ?\<sigma>\<tau>"
      unfolding subst_compose'_def subst_compose_def ..
    show "?l x = ?r x" unfolding l r
    proof (rule term_subst_eq)
      fix y
      assume y: "y \<in> vars_term (\<tau> x)"
      have "y \<in> vars_subst \<tau> \<or> \<tau> x = Var x"
      proof (cases "x \<in> subst_domain \<tau>")
        case True then show ?thesis using y unfolding vars_subst_def by auto
      next
        case False
        then show ?thesis  unfolding subst_domain_def by auto
      qed
      then show "Var y = ?\<sigma>\<tau> y"
      proof
        assume "y \<in> vars_subst \<tau>"
        with assms have "y \<notin> subst_domain \<sigma>" by auto
        then show ?thesis by simp
      next
        assume "\<tau> x = Var x"
        with y have y: "y = x" by simp
        show ?thesis unfolding y using False by auto
      qed
    qed
  qed
qed

lemma vars_subst_compose'_pow:
  assumes "vars_subst \<tau> \<inter> subst_domain \<sigma> = {}"
  shows "\<sigma> ^^ n \<circ>\<^sub>s \<tau> = \<tau> \<circ>\<^sub>s (subst_compose' \<sigma> \<tau>) ^^ n"
proof (induct n)
  case 0 then show ?case by auto
next
  case (Suc n)
  let ?\<sigma>\<tau> = "subst_compose' \<sigma> \<tau>"
  have "\<sigma> ^^ Suc n \<circ>\<^sub>s \<tau> = \<sigma> \<circ>\<^sub>s (\<sigma> ^^ n \<circ>\<^sub>s \<tau>)" by (simp add: ac_simps)
  also have "... = \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s ?\<sigma>\<tau>^^n)" unfolding Suc ..
  also have "... = (\<sigma> \<circ>\<^sub>s \<tau>) \<circ>\<^sub>s ?\<sigma>\<tau> ^^ n" by (auto simp: ac_simps)
  also have "... = (\<tau> \<circ>\<^sub>s ?\<sigma>\<tau>) \<circ>\<^sub>s ?\<sigma>\<tau> ^^ n" unfolding vars_subst_compose'[OF assms] ..
  finally show ?case by (simp add: ac_simps)
qed

lemma subst_pow_commute:
  assumes "\<sigma> \<circ>\<^sub>s \<tau> = \<tau> \<circ>\<^sub>s \<sigma>"
  shows "\<sigma> \<circ>\<^sub>s (\<tau> ^^ n) = \<tau> ^^ n \<circ>\<^sub>s \<sigma>"
proof (induct n)
  case (Suc n)
  have "\<sigma> \<circ>\<^sub>s \<tau> ^^ Suc n = (\<sigma> \<circ>\<^sub>s \<tau>) \<circ>\<^sub>s \<tau> ^^ n" by (simp add: ac_simps)
  also have "... = \<tau> \<circ>\<^sub>s (\<sigma> \<circ>\<^sub>s \<tau> ^^ n)" unfolding assms by (simp add: ac_simps)
  also have "... = \<tau> ^^ Suc n \<circ>\<^sub>s \<sigma>" unfolding Suc by (simp add: ac_simps)
  finally show ?case .
qed simp

lemma subst_power_commute:
  assumes "\<sigma> \<circ>\<^sub>s \<tau> = \<tau> \<circ>\<^sub>s \<sigma>"
  shows "(\<sigma> ^^ n) \<circ>\<^sub>s (\<tau> ^^ n) = (\<sigma> \<circ>\<^sub>s \<tau>)^^n"
proof (induct n)
  case (Suc n)
  have "(\<sigma> ^^ Suc n) \<circ>\<^sub>s (\<tau> ^^ Suc n) = (\<sigma>^^n \<circ>\<^sub>s (\<sigma> \<circ>\<^sub>s \<tau> ^^ n) \<circ>\<^sub>s \<tau>)"
    unfolding subst_power_Suc by (simp add: ac_simps)
  also have "... = (\<sigma>^^n \<circ>\<^sub>s \<tau> ^^ n) \<circ>\<^sub>s (\<sigma> \<circ>\<^sub>s \<tau>)"
    unfolding subst_pow_commute[OF assms] by (simp add: ac_simps)
  also have "... = (\<sigma> \<circ>\<^sub>s \<tau>)^^Suc n" unfolding Suc
    unfolding subst_power_Suc ..
  finally show ?case .
qed simp

lemma vars_term_ctxt_apply:
  "vars_term (C\<langle>t\<rangle>) = vars_ctxt C \<union> vars_term t"
  by (induct C) (auto)

lemma vars_ctxt_pos_term:
  assumes "p \<in> poss t"
  shows "vars_term t = vars_ctxt (ctxt_of_pos_term p t) \<union> vars_term (t |_ p)"
proof -
  let ?C = "ctxt_of_pos_term p t"
  have "t = ?C\<langle>t |_ p\<rangle>" using ctxt_supt_id [OF assms] by simp
  then have "vars_term t = vars_term (?C\<langle>t |_ p\<rangle>)" by simp
  then show ?thesis unfolding vars_term_ctxt_apply .
qed

lemma vars_term_subt_at:
  assumes "p \<in> poss t"
  shows "vars_term (t |_ p) \<subseteq> vars_term t"
  using vars_ctxt_pos_term [OF assms] by simp

lemma Var_pow_Var[simp]: "Var ^^ n = Var"
  by (rule, induct n, auto)

definition is_inverse_renaming :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst" where
  "is_inverse_renaming \<sigma> y = (
    if Var y \<in> subst_range \<sigma> then Var (the_inv_into (subst_domain \<sigma>) \<sigma> (Var y))
    else Var y)"

lemma is_renaming_inverse_domain:
  assumes ren: "is_renaming \<sigma>"
    and x: "x \<in> subst_domain \<sigma>"
  shows "Var x \<cdot> \<sigma> \<cdot> is_inverse_renaming \<sigma> = Var x" (is "_ \<cdot> ?\<sigma> = _")
proof -
  note ren = ren[unfolded is_renaming_def]
  from ren obtain y where \<sigma>x: "\<sigma> x = Var y" by force
  from ren have inj: "inj_on \<sigma> (subst_domain \<sigma>)" by auto
  note inj = the_inv_into_f_eq[OF inj, OF \<sigma>x]
  note d = is_inverse_renaming_def
  from x have "Var y \<in> subst_range \<sigma>" using \<sigma>x by force
  then have "?\<sigma> y = Var (the_inv_into (subst_domain \<sigma>) \<sigma> (Var y))" unfolding d by simp
  also have "... = Var x" using inj[OF x] by simp
  finally show ?thesis using \<sigma>x by simp
qed

lemma is_renaming_inverse_range:
  assumes varren: "is_renaming \<sigma>"
    and x: "Var x \<notin> subst_range \<sigma>"
  shows "Var x \<cdot> \<sigma> \<cdot> is_inverse_renaming \<sigma> = Var x" (is "_ \<cdot> ?\<sigma> = _")
proof (cases "x \<in> subst_domain \<sigma>")
  case True
  from is_renaming_inverse_domain[OF varren True]
  show ?thesis .
next
  case False
  then have \<sigma>x: "\<sigma> x = Var x" unfolding subst_domain_def by auto
  note ren = varren[unfolded is_renaming_def]
  note d = is_inverse_renaming_def
  have "Var x \<cdot> \<sigma> \<cdot> ?\<sigma> = ?\<sigma> x" using \<sigma>x by auto
  also have "... = Var x"
    unfolding d using x by simp
  finally show ?thesis .
qed

lemma vars_subst_compose:
  "vars_subst (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> vars_subst \<sigma> \<union> vars_subst \<tau>"
proof
  fix x
  assume "x \<in> vars_subst (\<sigma> \<circ>\<^sub>s \<tau>)"
  from this[unfolded vars_subst_def subst_range.simps]
  obtain y where "y \<in> subst_domain (\<sigma> \<circ>\<^sub>s \<tau>) \<and> (x = y \<or> x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y))" by blast
  with subst_domain_compose[of \<sigma> \<tau>] have y: "y \<in> subst_domain \<sigma> \<union> subst_domain \<tau>" and disj:
    "x = y \<or> (x \<noteq> y \<and> x \<in> vars_term (\<sigma> y \<cdot> \<tau>))" unfolding subst_compose_def by auto
  from disj
  show "x \<in> vars_subst \<sigma> \<union> vars_subst \<tau>"
  proof
    assume "x = y"
    with y show ?thesis unfolding vars_subst_def by auto
  next
    assume "x \<noteq> y \<and> x \<in> vars_term (\<sigma> y \<cdot> \<tau>)"
    then obtain z where neq: "x \<noteq> y" and x: "x \<in> vars_term (\<tau> z)" and z: "z \<in> vars_term (\<sigma> y)" unfolding vars_term_subst by auto
    show ?thesis
    proof (cases "\<tau> z = Var z")
      case False
      with x have "x \<in> vars_subst \<tau>" unfolding vars_subst_def subst_domain_def subst_range.simps by blast
      then show ?thesis by auto
    next
      case True
      with x have x: "z = x" by auto
      with z have y: "x \<in> vars_term (\<sigma> y)" by auto
      show ?thesis
      proof (cases "\<sigma> y = Var y")
        case False
        with y have "x \<in> vars_subst \<sigma>" unfolding vars_subst_def subst_domain_def subst_range.simps by blast
        then show ?thesis by auto
      next
        case True
        with y have "x = y" by auto
        with neq show ?thesis by auto
      qed
    qed
  qed
qed

lemma vars_subst_compose_update:
  assumes x: "x \<notin> vars_subst \<sigma>"
  shows "\<sigma> \<circ>\<^sub>s \<tau>(x := t) = (\<sigma> \<circ>\<^sub>s \<tau>)(x := t)" (is "?l = ?r")
proof
  fix z
  note x = x[unfolded vars_subst_def subst_domain_def]
  from x have xx: "\<sigma> x = Var x" by auto
  show "?l z = ?r z"
  proof (cases "z = x")
    case True
    with xx show ?thesis by (simp add: subst_compose_def)
  next
    case False
    then have "?r z = \<sigma> z \<cdot> \<tau>" unfolding subst_compose_def by auto
    also have "... = ?l z" unfolding subst_compose_def
    proof (rule term_subst_eq)
      fix y
      assume "y \<in> vars_term (\<sigma> z)"
      with False x have v: "y \<noteq> x" unfolding subst_range.simps subst_domain_def by force
      then show "\<tau> y = (\<tau>(x := t)) y" by simp
    qed
    finally show ?thesis by simp
  qed
qed

lemma subst_variants_imp_eq:
  assumes "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" and "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
  shows "\<And>x. \<sigma> x \<cdot> \<sigma>' = \<tau> x" "\<And>x. \<tau> x \<cdot> \<tau>' = \<sigma> x"
  using assms by (metis subst_compose_def)+

lemma poss_subst_choice: assumes "p \<in> poss (t \<cdot> \<sigma>)" shows
  "p \<in> poss t \<and> is_Fun (t |_ p) \<or>
  (\<exists> x q1 q2. q1 \<in> poss t \<and> q2 \<in> poss (\<sigma> x) \<and> t |_ q1 = Var x \<and> x \<in> vars_term t
    \<and> p = q1 @ q2 \<and> t \<cdot> \<sigma> |_ p = \<sigma> x |_ q2)" (is "_ \<or> (\<exists> x q1 q2. ?p x q1 q2 t p)")
  using assms
proof (induct p arbitrary: t)
  case (Cons i p t)
  show ?case
  proof (cases t)
    case (Var x)
    have "?p x [] (i # p) t (i # p)" using Cons(2) unfolding Var by simp
    then show ?thesis by blast
  next
    case (Fun f ts)
    with Cons(2) have i: "i < length ts" and p: "p \<in> poss (ts ! i \<cdot> \<sigma>)" by auto
    from Cons(1)[OF p]
    show ?thesis
    proof
      assume "\<exists> x q1 q2. ?p x q1 q2 (ts ! i) p"
      then obtain x q1 q2 where "?p x q1 q2 (ts ! i) p" by auto
      with Fun i have "?p x (i # q1) q2 (Fun f ts) (i # p)" by auto
      then show ?thesis unfolding Fun by blast
    next
      assume "p \<in> poss (ts ! i) \<and> is_Fun (ts ! i |_ p)"
      then show ?thesis using Fun i by auto
    qed
  qed
next
  case Nil
  show ?case
  proof (cases t)
    case (Var x)
    have "?p x [] [] t []" unfolding Var by auto
    then show ?thesis by auto
  qed simp
qed

fun vars_term_list :: "('f, 'v) term \<Rightarrow> 'v list"
  where
    "vars_term_list (Var x) = [x]" |
    "vars_term_list (Fun _ ts) = concat (map vars_term_list ts)"

lemma set_vars_term_list [simp]:
  "set (vars_term_list t) = vars_term t"
  by (induct t) simp_all

lemma unary_vars_term_list:
  assumes t: "funas_term t \<subseteq> F"
    and unary: "\<And> f n. (f, n) \<in> F \<Longrightarrow> n \<le> 1"
  shows "vars_term_list t = [] \<or> (\<exists> x \<in> vars_term t. vars_term_list t = [x])"
proof -
  from t show ?thesis
  proof (induct t)
    case Var then show ?case by auto
  next
    case (Fun f ss)
    show ?case
    proof (cases ss)
      case Nil
      then show ?thesis by auto
    next
      case (Cons t ts)
      let ?n = "length ss"
      from Fun(2) have "(f,?n) \<in> F" by auto
      from unary[OF this] have n: "?n \<le> Suc 0" by auto
      with Cons have "?n = Suc 0" by simp
      with Cons have ss: "ss = [t]" by (cases ts, auto)
      note IH = Fun(1)[unfolded ss, simplified]
      from ss have id1: "vars_term_list (Fun f ss) = vars_term_list t" by simp
      from ss have id2: "vars_term (Fun f ss) = vars_term t" by simp
      from Fun(2) ss have mem: "funas_term t \<subseteq> F" by auto
      show ?thesis unfolding id1 id2 using IH[OF refl mem] by simp
    qed
  qed
qed

declare vars_term_list.simps [simp del]

text \<open>The list of function symbols in a term (without removing duplicates).\<close>

fun funs_term_list :: "('f, 'v) term \<Rightarrow> 'f list"
  where
    "funs_term_list (Var _) = []" |
    "funs_term_list (Fun f ts) = f # concat (map funs_term_list ts)"

lemma set_funs_term_list [simp]:
  "set (funs_term_list t) = funs_term t"
  by (induct t) simp_all

declare funs_term_list.simps [simp del]

text \<open>The list of function symbol and arity pairs in a term
(without removing duplicates).\<close>

fun funas_term_list :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_term_list (Var _) = []" |
    "funas_term_list (Fun f ts) = (f, length ts) # concat (map funas_term_list ts)"

lemma set_funas_term_list [simp]:
  "set (funas_term_list t) = funas_term t"
  by (induct t) simp_all

declare funas_term_list.simps [simp del]

definition funas_args_term_list :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_args_term_list t = concat (map funas_term_list (args t))"

lemma set_funas_args_term_list [simp]:
  "set (funas_args_term_list t) = funas_args_term t"
  by (simp add: funas_args_term_def funas_args_term_list_def)

lemma vars_term_list_map_funs_term:
  "vars_term_list (map_funs_term fg t) = vars_term_list t"
proof (induct t)
  case (Var x) then show ?case by (simp add: vars_term_list.simps)
next
  case (Fun f ss)
  show ?case by (simp add: vars_term_list.simps o_def, insert Fun, induct ss, auto)
qed

lemma funs_term_list_map_funs_term:
  "funs_term_list (map_funs_term fg t) = map fg (funs_term_list t)"
proof (induct t)
  case (Var x) show ?case by (simp add: funs_term_list.simps)
next
  case (Fun f ts)
  show ?case
    by (simp add: funs_term_list.simps, insert Fun, induct ts, auto)
qed

text \<open>
  Next we provide some functions to compute multisets instead of sets of
  function symbols, variables, etc.
  they may be helpful for non-duplicating TRSs.
\<close>

fun funs_term_ms :: "('f,'v)term \<Rightarrow> 'f multiset"
  where
    "funs_term_ms (Var x) = {#}" |
    "funs_term_ms (Fun f ts) = {#f#} + \<Sum>\<^sub># (mset (map funs_term_ms ts))"

fun funs_ctxt_ms :: "('f,'v)ctxt \<Rightarrow> 'f multiset"
  where
    "funs_ctxt_ms Hole = {#}" |
    "funs_ctxt_ms (More f bef C aft) =
    {#f#} + \<Sum>\<^sub># (mset (map funs_term_ms bef)) +
    funs_ctxt_ms C + \<Sum>\<^sub># (mset (map funs_term_ms aft))"

lemma funs_term_ms_ctxt_apply:
  "funs_term_ms C\<langle>t\<rangle> = funs_ctxt_ms C + funs_term_ms t"
  by (induct C) (auto simp: multiset_eq_iff)

lemma funs_term_ms_subst_apply:
  "funs_term_ms (t \<cdot> \<sigma>) =
    funs_term_ms t + \<Sum>\<^sub># (image_mset (\<lambda> x. funs_term_ms (\<sigma> x)) (vars_term_ms t))"
proof (induct t)
  case (Fun f ts)
  let ?m = "mset"
  let ?f = "funs_term_ms"
  let ?ts = "\<Sum>\<^sub># (?m (map ?f ts))"
  let ?\<sigma>  = "\<Sum>\<^sub># (image_mset (\<lambda>x. ?f (\<sigma> x)) (\<Sum>\<^sub># (?m (map vars_term_ms ts))))"
  let ?ts\<sigma> = "\<Sum>\<^sub># (?m (map (\<lambda> x. ?f (x \<cdot> \<sigma>)) ts))"
  have ind: "?ts\<sigma> = ?ts + ?\<sigma>" using Fun
    by (induct ts, auto simp: multiset_eq_iff)
  then show ?case unfolding multiset_eq_iff by (simp add: o_def)
qed auto

lemma ground_vars_term_ms_empty:
  "ground t = (vars_term_ms t = {#})"
  unfolding ground_vars_term_empty
  unfolding set_mset_vars_term_ms [symmetric]
  by (simp del: set_mset_vars_term_ms)

lemma vars_term_ms_map_funs_term [simp]:
  "vars_term_ms (map_funs_term fg t) = vars_term_ms t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts) auto
qed simp

lemma funs_term_ms_map_funs_term:
  "funs_term_ms (map_funs_term fg t) = image_mset fg (funs_term_ms t)"
proof (induct t)
  case (Fun f ss)
  then show ?case by (induct ss, auto)
qed auto

lemma supteq_imp_vars_term_ms_subset:
  "s \<unrhd> t \<Longrightarrow> vars_term_ms t \<subseteq># vars_term_ms s"
proof (induct rule: supteq.induct)
  case (subt u ss t f)
  from subt(1) obtain bef aft where ss: "ss = bef @ u # aft"
    by (metis in_set_conv_decomp)
  have "vars_term_ms t \<subseteq># vars_term_ms u" by fact
  also have "\<dots> \<subseteq># \<Sum>\<^sub># (mset (map vars_term_ms ss))"
    unfolding ss by (simp add: ac_simps)
  also have "\<dots> = vars_term_ms (Fun f ss)" by auto
  finally show ?case by auto
qed auto

lemma mset_funs_term_list:
  "mset (funs_term_list t) = funs_term_ms t"
proof (induct t)
  case (Var x) show ?case by (simp add: funs_term_list.simps)
next
  case (Fun f ts)
  show ?case
    by (simp add: funs_term_list.simps, insert Fun, induct ts, auto simp: funs_term_list.simps multiset_eq_iff)
qed

text \<open>Creating substitutions from lists\<close>

type_synonym ('f, 'v, 'w) gsubstL = "('v \<times> ('f, 'w) term) list"
type_synonym ('f, 'v) substL = "('f, 'v, 'v) gsubstL"

definition mk_subst :: "('v \<Rightarrow> ('f, 'w) term) \<Rightarrow> ('f, 'v, 'w) gsubstL \<Rightarrow> ('f, 'v, 'w) gsubst" where
  "mk_subst d xts \<equiv>
    (\<lambda>x. case map_of xts x of
      None \<Rightarrow> d x
    | Some t \<Rightarrow> t)"

lemma mk_subst_not_mem:
  assumes x: "x \<notin> set xs"
  shows "mk_subst f (zip xs ts) x = f x"
proof -
  have "map_of (zip xs ts) x = None"
    unfolding map_of_eq_None_iff set_zip using x[unfolded set_conv_nth] by auto
  then show ?thesis unfolding mk_subst_def by auto
qed

lemma mk_subst_not_mem':
  assumes x: "x \<notin> set (map fst ss)"
  shows "mk_subst f ss x = f x"
proof -
  have "map_of ss x = None"
    unfolding map_of_eq_None_iff using x by auto
  then show ?thesis unfolding mk_subst_def by auto
qed

lemma mk_subst_distinct:
  assumes dist: "distinct xs"
    and i: "i < length xs" "i < length ls"
  shows "mk_subst f (zip xs ls) (xs ! i) = ls ! i"
proof - 
  from i have in_zip:"(xs!i, ls!i) \<in> set (zip xs ls)" 
    using nth_zip[OF i] set_zip by auto 
  from dist have dist':"distinct (map fst (zip xs ls))"
    by (simp add: map_fst_zip_take)
  then show ?thesis 
    unfolding mk_subst_def using map_of_is_SomeI[OF dist' in_zip] by simp
qed

lemma mk_subst_Nil [simp]:
  "mk_subst d [] = d"
  by (simp add: mk_subst_def)

lemma mk_subst_concat:
  assumes "x \<notin> set (map fst xs)"
  shows "(mk_subst f (xs@ys)) x = (mk_subst f ys) x"
  using assms unfolding mk_subst_def map_of_append
  by (simp add: dom_map_of_conv_image_fst map_add_dom_app_simps(3)) 

lemma mk_subst_concat_Cons:
  assumes "x \<in> set (map fst ss)"
  shows "mk_subst f (concat (ss#ss')) x = mk_subst f ss x"
proof-
  from assms obtain y where "map_of ss x = Some y"
    by (metis list.set_map map_of_eq_None_iff not_None_eq) 
  then show ?thesis unfolding mk_subst_def concat.simps map_of_append
    by simp
qed

lemma vars_term_var_poss_iff:
  "x \<in> vars_term t \<longleftrightarrow> (\<exists>p. p \<in> var_poss t \<and> Var x = t |_ p)" (is "?L \<longleftrightarrow> ?R")
proof
  assume x: "?L"
  obtain p where "p \<in> poss t" and "Var x = t |_ p"
    using supteq_imp_subt_at [OF supteq_Var [OF x]] by force
  then show "?R" using var_poss_iff by auto
next
  assume p: "?R"
  then obtain p where 1: "p \<in> var_poss t" and 2: "Var x = t |_ p" by auto
  from var_poss_imp_poss [OF 1] have "p \<in> poss t" .
  then show "?L" by (simp add: 2 subt_at_imp_supteq subteq_Var_imp_in_vars_term)
qed

lemma vars_term_poss_subt_at:
  assumes "x \<in> vars_term t"
  obtains q where "q \<in> poss t" and "t |_ q = Var x"
  using assms
proof (induct t)
  case (Fun f ts)
  then obtain t where t:"t \<in> set ts" and x:"x \<in> vars_term t" by auto
  moreover then obtain i where "t = ts ! i" and "i < length ts" using in_set_conv_nth by metis
  ultimately show ?case using Fun(1)[OF t _ x] Fun(2)[of "Cons i q" for q] by auto
qed auto

lemma vars_ctxt_subt_at':
  assumes "x \<in> vars_ctxt C"
    and "p \<in> poss C\<langle>t\<rangle>"
    and "hole_pos C = p"
  shows "\<exists>q. q \<in> poss C\<langle>t\<rangle> \<and> parallel_pos p q \<and> C\<langle>t\<rangle> |_ q = Var x"
  using assms
proof (induct C arbitrary: p)
  case (More f bef C aft)
  then have [simp]: "p = length bef # hole_pos C" by auto
  consider
    (C) "x \<in> vars_ctxt C" |
    (bef) t where "t \<in> set bef" and "x \<in> vars_term t" |
    (aft) t where "t \<in> set aft" and "x \<in> vars_term t"
    using More by auto
  then show ?case
  proof (cases)
    case C
    from More(1)[OF this] obtain q where "q \<in> poss C\<langle>t\<rangle> \<and> hole_pos C \<bottom> q \<and> C\<langle>t\<rangle> |_ q = Var x"
      by fastforce
    then show ?thesis by (force intro!: exI[of _ "length bef # q"])
  next
    case bef
    then obtain q where "q \<in> poss t" and "t |_ q = Var x"
      using vars_term_poss_subt_at by force
    moreover from bef obtain i where "i < length bef" and "bef ! i = t"
      using in_set_conv_nth by metis
    ultimately show ?thesis
      by (force simp: nth_append intro!: exI[of _ "i # q"])
  next
    case aft
    then obtain q where "q \<in> poss t" and "t |_ q = Var x"
      using vars_term_poss_subt_at by force
    moreover from aft obtain i where "i < length aft" and "aft ! i = t"
      using in_set_conv_nth by metis
    ultimately show ?thesis
      by (force simp: nth_append intro!: exI[of _ "(Suc (length bef) + i) # q"])
  qed
qed auto

lemma vars_ctxt_subt_at:
  assumes "x \<in> vars_ctxt C"
    and "p \<in> poss C\<langle>t\<rangle>"
    and "hole_pos C = p"
  obtains q where "q \<in> poss C\<langle>t\<rangle>" and "parallel_pos p q" and "C\<langle>t\<rangle> |_ q = Var x"
  using vars_ctxt_subt_at' assms by force

lemma poss_is_Fun_fun_poss:
  assumes "p \<in> poss t"
    and "is_Fun (t |_ p)"
  shows "p \<in> fun_poss t"
  using assms by (metis DiffI is_Var_def poss_simps(3) var_poss_iff)

lemma fun_poss_map_vars_term:
  "fun_poss (map_vars_term f t) = fun_poss t"
  unfolding map_vars_term_eq proof(induct t)
  case (Fun g ts)
  {fix i assume "i < length ts"
    with Fun have "fun_poss (map (\<lambda>t. t \<cdot> (Var \<circ> f)) ts ! i) = fun_poss (ts!i)"
      by fastforce
    then have "{i # p |p. p \<in> fun_poss (map (\<lambda>t. t \<cdot> (Var \<circ> f)) ts ! i)} = {i # p |p. p \<in> fun_poss (ts ! i)}"
      by presburger
  }
  then show ?case unfolding fun_poss.simps eval_term.simps length_map
    by auto
qed simp

lemma fun_poss_append_poss:
  assumes "p@q \<in> poss t" "q \<noteq> []"
  shows "p \<in> fun_poss t"
  by (meson assms is_Var_def poss_append_poss poss_is_Fun_fun_poss var_pos_maximal)

lemma fun_poss_append_poss':
  assumes "p@q \<in> fun_poss t"
  shows "p \<in> fun_poss t"
  by (metis append.right_neutral assms fun_poss_append_poss fun_poss_imp_poss)

lemma fun_poss_in_ctxt:
  assumes "q@p \<in> fun_poss (C\<langle>t\<rangle>)"
    and "hole_pos C = q"
  shows "p \<in> fun_poss t"
  by (metis Term.term.simps(4) assms fun_poss_fun_conv fun_poss_imp_poss hole_pos_poss hole_pos_poss_conv is_VarE poss_is_Fun_fun_poss subt_at_append subt_at_hole_pos)

lemma args_poss: 
  assumes "i # p \<in> poss t"
  obtains f ts where "t = Fun f ts" "p \<in> poss (ts!i)" "i < length ts"
  by (metis Cons_poss_Var assms poss.elims poss_Cons_poss term.sel(4))

lemma var_poss_parallel:
  assumes "p \<in> var_poss t" and "q \<in> var_poss t" and "p \<noteq> q"
  shows "p \<bottom> q"
  using assms proof(induct t arbitrary:p q)
  case (Fun f ts)
  from Fun(2) obtain i p' where i:"i < length ts" "p' \<in> var_poss (ts!i)" and p:"p = i#p'"
    using var_poss_iff by fastforce 
  with Fun(3) obtain j q' where j:"j < length ts" "q' \<in> var_poss (ts!j)" and q:"q = j#q'"
    using var_poss_iff by fastforce 
  then show ?case proof(cases "i = j")
    case True
    from Fun(4) have "p' \<noteq> q'" 
      unfolding p q True by simp 
    with Fun(1) i j show ?thesis 
      unfolding True p q parallel_pos.simps using nth_mem by blast 
  next
    case False
    then show ?thesis unfolding p q
      by simp
  qed        
qed simp

lemma ctxt_comp_equals:
  assumes poss:"p \<in> poss s" "p \<in> poss t"
    and "ctxt_of_pos_term p s \<circ>\<^sub>c C = ctxt_of_pos_term p t \<circ>\<^sub>c D"
  shows "C = D"
  using assms proof(induct p arbitrary:s t)
  case (Cons i p)
  from Cons(2) obtain f ss where s:"s = Fun f ss" and p:"p \<in> poss (ss!i)"
    using args_poss by blast 
  from Cons(3) obtain g ts where t:"t = Fun g ts" and p':"p \<in> poss (ts!i)"
    using args_poss by blast 
  from Cons(1)[OF p p'] Cons(4) show ?case 
    unfolding s t ctxt_of_pos_term.simps ctxt_compose.simps by simp
qed simp

lemma ctxt_subst_comp_pos:
  assumes "q \<in> poss t" and "p \<in> poss (t \<cdot> \<tau>)"
    and "(ctxt_of_pos_term q t \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c C = ctxt_of_pos_term p (t \<cdot> \<tau>)"
  shows "q \<le>\<^sub>p p"
  using assms by (metis hole_pos_ctxt_compose hole_pos_ctxt_of_pos_term hole_pos_subst less_eq_pos_simps(1)) 

text \<open>Predicate whether a context is ground, i.e., whether the context contains no variables.\<close>
fun ground_ctxt :: "('f,'v)ctxt \<Rightarrow> bool" where
  "ground_ctxt Hole = True"
| "ground_ctxt (More f ss1 C ss2) =
    ((\<forall>s\<in>set ss1. ground s) \<and> (\<forall>s\<in>set ss2. ground s) \<and> ground_ctxt C)"

lemma ground_ctxt_apply[simp]: "ground (C\<langle>t\<rangle>) = (ground_ctxt C \<and> ground t)"
  by (induct C, auto)

lemma ground_ctxt_compose[simp]: "ground_ctxt (C \<circ>\<^sub>c D) = (ground_ctxt C \<and> ground_ctxt D)"
  by (induct C, auto)

text \<open>Linearity of a term\<close>

fun linear_term :: "('f, 'v) term \<Rightarrow> bool"
  where
    "linear_term (Var _) = True" |
    "linear_term (Fun _ ts) = (is_partition (map vars_term ts) \<and> (\<forall>t\<in>set ts. linear_term t))"

lemma subst_merge:
  assumes part: "is_partition (map vars_term ts)"
  shows "\<exists>\<sigma>. \<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i). \<sigma> x = \<tau> i x"
proof -
  let ?\<tau> = "map \<tau> [0 ..< length ts]"
  let ?\<sigma> = "fun_merge ?\<tau> (map vars_term ts)"
  show ?thesis
    by (rule exI[of _ ?\<sigma>], intro allI impI ballI,
        insert fun_merge_part[OF part, of _ _ ?\<tau>], auto)
qed

text \<open>Matching for linear terms\<close>
fun weak_match :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "weak_match _ (Var _) \<longleftrightarrow> True" |
    "weak_match (Var _) (Fun _ _) \<longleftrightarrow> False" |
    "weak_match (Fun f ts) (Fun g ss) \<longleftrightarrow>
    f = g \<and> length ts = length ss \<and> (\<forall>i < length ts. weak_match (ts ! i) (ss ! i))"

lemma weak_match_refl: "weak_match t t"
  by (induct t) auto

lemma weak_match_match: "weak_match (t \<cdot> \<sigma>) t"
  by (induct t) auto

lemma weak_match_map_funs_term:
  "weak_match t s \<Longrightarrow> weak_match (map_funs_term g t) (map_funs_term g s)"
proof (induct s arbitrary: t)
  case (Fun f ss t)
  from Fun(2) obtain ts where t: "t = Fun f ts" by (cases t, auto)
  from Fun(1)[unfolded set_conv_nth] Fun(2)[unfolded t]
  show ?case unfolding t by force
qed simp

lemma linear_weak_match:
  assumes "linear_term l" and "weak_match t s" and "s = l \<cdot> \<sigma>"
  shows "\<exists>\<tau>. t = l\<cdot>\<tau> \<and> (\<forall>x\<in>vars_term l. weak_match (Var x \<cdot> \<tau>) (Var x \<cdot> \<sigma>))"
  using assms proof (induct l arbitrary: s t)
  case (Var x)
  show ?case
  proof (rule exI[of _ "(\<lambda> y. t)"], intro conjI, simp)
    from Var show "\<forall>x\<in>vars_term (Var x). weak_match (Var x \<cdot> (\<lambda>y. t)) (Var x \<cdot> \<sigma>)"
      by force
  qed
next
  case (Fun f ls)
  let ?n = "length ls"
  from Fun(4) obtain ss where s: "s = Fun f ss" and lss: "length ss = ?n"  by (cases s, auto)
  with Fun(4) have match: "\<And> i. i < ?n \<Longrightarrow> ss ! i = (ls ! i) \<cdot> \<sigma>" by auto
  from Fun(3) s lss obtain ts where t: "t = Fun f ts"
    and lts: "length ts = ?n" by (cases t, auto)
  with Fun(3) s have weak_match: "\<And> i. i < ?n \<Longrightarrow> weak_match (ts ! i) (ss ! i)" by auto
  from Fun(2) have linear: "\<And> i. i < ?n \<Longrightarrow> linear_term (ls ! i)" by simp
  let ?cond = "\<lambda> \<tau> i. ts ! i = ls ! i \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term (ls ! i). weak_match (Var x \<cdot> \<tau>) (Var x \<cdot> \<sigma>))"
  {
    fix i
    assume i: "i < ?n"
    then have "ls ! i \<in> set ls" by simp
    from Fun(1)[OF this linear[OF i] weak_match[OF i] match[OF i]]
    have "\<exists> \<tau>. ?cond \<tau> i" .
  }
  then have "\<forall>i. \<exists>\<tau>. (i < ?n \<longrightarrow> ?cond \<tau> i)" by auto
  from choice[OF this] obtain subs where subs: "\<And> i. i < ?n \<Longrightarrow> ?cond (subs i) i" by auto
  from Fun(2) have distinct: "is_partition(map vars_term ls)" by simp
  from subst_merge[OF this, of subs]
  obtain \<tau> where \<tau>: "\<And> i x . i < length ls \<Longrightarrow> x \<in> vars_term (ls ! i) \<Longrightarrow> \<tau> x = subs i x" by auto
  show ?case
  proof (rule exI[of _ \<tau>], simp add: t, intro ballI conjI)
    fix li x
    assume li: "li \<in> set ls" and x: "x \<in> vars_term li"
    from li obtain i where i: "i < ?n" and li: "li = ls ! i" unfolding set_conv_nth by auto
    with x have x: "x \<in> vars_term (ls ! i)" by simp
    from subs[OF i, THEN conjunct2, THEN bspec, OF x] show "weak_match (\<tau> x) (\<sigma> x)" unfolding \<tau>[OF i x[unfolded li]]
      by simp
  next
    show "ts = map (\<lambda> t. t \<cdot> \<tau>) ls"
    proof (rule nth_equalityI, simp add: lts)
      fix i
      assume "i < length ts"
      with lts have i: "i < ?n" by simp
      have "ts ! i = ls ! i \<cdot> subs i"
        by (rule subs[THEN conjunct1, OF i])
      also have "... = ls ! i \<cdot> \<tau>" unfolding term_subst_eq_conv using \<tau>[OF i] by auto
      finally show "ts ! i = map (\<lambda> t. t \<cdot> \<tau>) ls ! i"
        by (simp add: nth_map[OF i])
    qed
  qed
qed

lemma map_funs_subst_split:
  assumes "map_funs_term fg t = s \<cdot> \<sigma>"
    and "linear_term s"
  shows "\<exists> u \<tau>. t = u \<cdot> \<tau> \<and> map_funs_term fg u = s \<and> (\<forall>x\<in>vars_term s. map_funs_term fg (\<tau> x) = (\<sigma> x))"
  using assms
proof (induct s arbitrary: t)
  case (Var x t)
  show ?case
  proof (intro exI conjI)
    show "t = Var x \<cdot> (\<lambda> _. t)" by simp
  qed (insert Var, auto)
next
  case (Fun g ss t)
  from Fun(2) obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  note Fun = Fun[unfolded t, simplified]
  let ?n = "length ss"
  from Fun have rec: "map (map_funs_term fg) ts = map (\<lambda> t. t \<cdot> \<sigma>) ss"
    and g: "fg f = g"
    and lin: "\<And> s. s \<in> set ss \<Longrightarrow> linear_term s"
    and part: "is_partition (map vars_term ss)" by auto
  from arg_cong[OF rec, of length] have len: "length ts = ?n" by simp
  from map_nth_conv[OF rec] have rec: "\<And> i. i < ?n \<Longrightarrow>  map_funs_term fg (ts ! i) = ss ! i \<cdot> \<sigma>" unfolding len by auto
  let ?p = "\<lambda> i u \<tau>. ts ! i = u \<cdot> \<tau> \<and> map_funs_term fg u = ss ! i \<and> (\<forall>x\<in>vars_term (ss ! i). map_funs_term fg (\<tau> x) = \<sigma> x)"
  {
    fix i
    assume i: "i < ?n"
    then have "ss ! i \<in> set ss" by auto
    from Fun(1)[OF this rec[OF i] lin[OF this]]
    have "\<exists> u \<tau>. ?p i u \<tau>" .
  }
  then have "\<forall>i. \<exists>u \<tau>. i < ?n \<longrightarrow> ?p i u \<tau>" by blast
  from choice[OF this] obtain us where "\<forall>i. \<exists>\<tau>. i < ?n \<longrightarrow> ?p i (us i) \<tau>"  ..
  from choice[OF this] obtain \<tau>s where p: "\<And> i. i < ?n \<Longrightarrow> ?p i (us i) (\<tau>s i)" by blast
  from subst_merge[OF part, of \<tau>s] obtain \<tau> where \<tau>: "\<And> i x. i < ?n \<Longrightarrow> x \<in> vars_term (ss ! i) \<Longrightarrow> \<tau> x = \<tau>s i x" by blast
  {
    fix i
    assume i: "i < ?n"
    from p[OF i] have "map_funs_term fg (us i) = ss ! i" by auto
    from arg_cong[OF this, of vars_term] vars_term_map_funs_term[of fg]
    have "vars_term (us i) = vars_term (ss ! i)" by auto
  } note vars = this
  let ?us = "map us [0 ..< ?n]"
  show ?case
  proof (intro exI conjI ballI)
    have ss: "ts = map (\<lambda> t. t \<cdot> \<tau>) ?us"
      unfolding list_eq_iff_nth_eq
      unfolding len
    proof (intro conjI allI impI)
      fix i
      assume i: "i < ?n"
      have us: "?us ! i = us i" using nth_map_upt[of i ?n 0] i by auto
      have "(map (\<lambda> t. t \<cdot> \<tau>) ?us) ! i = us i \<cdot> \<tau>"
        unfolding us[symmetric]
        using nth_map[of i ?us "\<lambda> t. t \<cdot> \<tau>"]  i by force
      also have "... = us i \<cdot> \<tau>s i"
        by (rule term_subst_eq, rule \<tau>[OF i], insert vars[OF i], auto )
      also have "... = ts ! i" using p[OF i] by simp
      finally
      show "ts ! i = map (\<lambda> t. t \<cdot> \<tau>) ?us ! i" ..
    qed auto
    show "t = Fun f ?us  \<cdot> \<tau>"
      unfolding t
      unfolding ss by auto
  next
    show "map_funs_term fg (Fun f ?us) = Fun g ss"
      using p g by (auto simp: list_eq_iff_nth_eq[of _ ss])
  next
    fix x
    assume x: "x \<in> vars_term (Fun g ss)"
    then obtain s where s: "s \<in> set ss" and x: "x \<in> vars_term s" by auto
    from s[unfolded set_conv_nth] obtain i where s: "s = ss ! i" and i: "i < ?n" by auto
    note x = x[unfolded s]
    from p[OF i] vars[OF i] x \<tau>[OF i x]
    show "map_funs_term fg (\<tau> x) = \<sigma> x" by auto
  qed
qed

lemma linear_map_funs_term [simp]:
  "linear_term (map_funs_term f t) = linear_term t"
  by (induct t) simp_all

lemma linear_term_map_inj_on_linear_term:
  assumes "linear_term l"
    and "inj_on f (vars_term l)"
  shows "linear_term (map_vars_term f l)"
  using assms
proof (induct l)
  case (Fun g ls)
  then have part:"is_partition (map vars_term ls)" by auto
  { fix l
    assume l:"l \<in> set ls"
    then have "vars_term l \<subseteq> vars_term (Fun g ls)" by auto
    then have "inj_on f (vars_term l)" using Fun(3) subset_inj_on by blast
    with Fun(1,2) l have "linear_term (map_vars_term f l)" by auto
  }
  moreover have "is_partition (map (vars_term \<circ> map_vars_term f) ls)"
    using is_partition_inj_map[OF part, of f] Fun(3) by (simp add: o_def term.set_map)
  ultimately show ?case by auto
qed auto

lemma linear_term_replace_in_subst:
  assumes "linear_term t"
    and "p \<in> poss t"
    and "t |_ p = Var x"
    and "\<And> y. y \<in> vars_term t \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<sigma> y = \<tau> y"
    and "\<tau> x = s"
  shows "replace_at (t \<cdot> \<sigma>) p s = t \<cdot> \<tau>"
  using assms
proof (induct p arbitrary: t)
  case (Cons i p t)
  then obtain f ts where t [simp]: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t) auto
  from Cons have "linear_term (ts ! i)" and "ts ! i |_ p = Var x" by auto
  have id: "replace_at (ts ! i \<cdot> \<sigma>) p (\<tau> x) = ts ! i \<cdot> \<tau>" using Cons by force
  let ?l = " (take i (map (\<lambda>t. t \<cdot> \<sigma>) ts) @ (ts ! i \<cdot> \<tau>) # drop (Suc i) (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
  from i have len: "length ts = length ?l" by auto
  { fix j
    assume j: "j < length ts"
    have "ts ! j \<cdot> \<tau> = ?l ! j"
    proof (cases "j = i")
      case True
      with i show ?thesis by (auto simp: nth_append)
    next
      case False
      let ?ts = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
      from i j have le:"j \<le> length ?ts" "i \<le> length ?ts" by auto
      from nth_append_take_drop_is_nth_conv[OF le] False have "?l ! j = ?ts ! j" by simp
      also have "... = ts ! j \<cdot> \<sigma>" using j by simp
      also have "... = ts ! j \<cdot> \<tau>"
      proof (rule term_subst_eq)
        fix y
        assume y: "y \<in> vars_term (ts ! j)"
        from p have "ts ! i \<unrhd> ts ! i |_ p" by (rule subt_at_imp_supteq)
        then have x: "x \<in> vars_term (ts ! i)" using \<open>ts ! i |_ p = Var x\<close>
          by (auto intro: subteq_Var_imp_in_vars_term)
        from Cons(2) have "is_partition (map vars_term ts)" by simp
        from this[unfolded is_partition_alt is_partition_alt_def, rule_format] j i False
        have "vars_term (ts ! i) \<inter> vars_term (ts ! j) = {}" by auto
        with y x have "y \<noteq> x" by auto
        with Cons(5) y j show "\<sigma> y = \<tau> y" by force
      qed
      finally show ?thesis by simp
    qed
  }
  then show ?case
    by (auto simp: \<open>\<tau> x = s\<close>[symmetric] id nth_map[OF i, of "\<lambda>t. t \<cdot> \<sigma>"])
      (metis len map_nth_eq_conv[OF len])
qed auto


lemma var_in_linear_args:
  assumes "linear_term (Fun f ts)"
    and "i < length ts" and "x \<in> vars_term (ts!i)" and "j < length ts \<and> j \<noteq> i"
  shows "x \<notin> vars_term (ts!j)"
proof-
  from assms(1) have "is_partition (map vars_term ts)"
    by simp
  with assms show ?thesis unfolding is_partition_alt is_partition_alt_def
    by auto 
qed

lemma subt_at_linear:
  assumes "linear_term t" and "p \<in> poss t"
  shows "linear_term (t|_p)"
  using assms proof(induct p arbitrary:t)
  case (Cons i p)
  then obtain f ts where f:"t = Fun f ts" and i:"i < length ts" and p:"p \<in> poss (ts!i)"
    by (meson args_poss)
  with Cons(2) have "linear_term (ts!i)"
    by force
  then show ?case
    unfolding f subt_at.simps using Cons.hyps p by blast
qed simp

lemma linear_subterms_disjoint_vars:
  assumes "linear_term t"
    and "p \<in> poss t" and "q \<in> poss t" and "p \<bottom> q"
  shows "vars_term (t|_p) \<inter> vars_term (t|_q) = {}"
  using assms proof(induct t arbitrary: p q)
  case (Fun f ts)
  from Fun(3,5) obtain i p' where i:"i < length ts" "p' \<in> poss (ts!i)" and p:"p = i#p'"
    by auto 
  with Fun(4,5) obtain j q' where j:"j < length ts" "q' \<in> poss (ts!j)" and q:"q = j#q'"
    by auto 
  then show ?case proof(cases "i=j")
    case True
    from Fun(5) have "p' \<bottom> q'" 
      unfolding p q True by simp
    with Fun(1,2) i j have "vars_term ((ts!j) |_ p') \<inter> vars_term ((ts!j) |_ q') = {}" 
      unfolding True by auto 
    then show ?thesis unfolding p q subt_at.simps True by simp
  next
    case False
    from i have "vars_term ((Fun f ts)|_p) \<subseteq> vars_term (ts!i)" 
      unfolding p subt_at.simps by (simp add: vars_term_subt_at) 
    moreover from j have "vars_term ((Fun f ts)|_q) \<subseteq> vars_term (ts!j)" 
      unfolding q subt_at.simps by (simp add: vars_term_subt_at) 
    ultimately show ?thesis using False Fun(2) i j
      by (meson disjoint_iff subsetD var_in_linear_args)
  qed
qed simp

lemma ground_imp_linear_term [simp]: "ground t \<Longrightarrow> linear_term t"
  by (induct t) (auto simp add: is_partition_def ground_vars_term_empty)

text \<open>exhaustively apply several maps on function symbols\<close>
fun map_funs_term_enum :: "('f \<Rightarrow> 'g list) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('g, 'v) term list"
where
  "map_funs_term_enum fgs (Var x) = [Var x]" |
  "map_funs_term_enum fgs (Fun f ts) = (
    let
      lts = map (map_funs_term_enum fgs) ts;
      ss = concat_lists lts;
      gs = fgs f
    in concat (map (\<lambda>g. map (Fun g) ss) gs))"


lemma map_funs_term_enum:
  assumes gf: "\<And> f g. g \<in> set (fgs f) \<Longrightarrow> gf g = f"
  shows "set (map_funs_term_enum fgs t) = {u. map_funs_term gf u = t \<and> (\<forall>g n. (g,n) \<in> funas_term u \<longrightarrow> g \<in> set (fgs (gf g)))}"
proof (induct t)
  case (Var x)
  show ?case (is "_ = ?R")
  proof -
    {
      fix t
      assume "t \<in> ?R"
      then have "t = Var x" by (cases t, auto)
    }
    then show ?thesis by auto
  qed
next
  case (Fun f ts)
  show ?case (is "?L = ?R")
  proof -
    {
      fix i
      assume "i < length ts"
      then have "ts ! i \<in> set ts" by auto
      note Fun[OF this]
    } note ind = this
    let ?cf = "\<lambda> u. (\<forall>g n. (g,n) \<in> funas_term u \<longrightarrow> g \<in> set (fgs (gf g)))"
    have id: "?L = {Fun g ss | g ss. g \<in> set (fgs f) \<and> length ss = length ts \<and> (\<forall>i<length ts. ss ! i \<in> set (map_funs_term_enum fgs (ts ! i)))}" (is "_ = ?M1") by auto
    have "?R = {Fun g ss | g ss. map_funs_term gf (Fun g ss) = Fun f ts \<and> ?cf (Fun g ss)}" (is "_ = ?M2")
    proof -
      {
        fix u
        assume u: "u \<in> ?R"
        then obtain g ss where "u = Fun g ss" by (cases u, auto)
        with u have "u \<in> ?M2" by auto
      }
      then have "?R \<subseteq> ?M2" by auto
      moreover have "?M2 \<subseteq> ?R" by blast
      finally show ?thesis by auto
    qed
    also have "... = ?M1"
    proof -
      {
        fix u
        assume "u \<in> ?M1"
        then obtain g ss where u: "u = Fun g ss" and g: "g \<in> set (fgs f)" and
          len: "length ss = length ts" and rec: "\<And> i. i < length ts \<Longrightarrow> ss ! i \<in> set (map_funs_term_enum fgs (ts ! i))" by auto
        from gf[OF g] have gf: "gf g = f" by simp
        {
          fix i
          assume i: "i < length ts"
          from ind[OF i] rec[OF i]
          have "map_funs_term gf (ss ! i) = ts ! i" by auto
        } note ssts = this
        have "map (map_funs_term gf) ss = ts"
          by (unfold map_nth_eq_conv[OF len], insert ssts, auto)
        with gf
        have mt: "map_funs_term gf (Fun g ss) = Fun f ts" by auto
        have "u \<in> ?M2"
        proof (rule, rule, rule, rule, rule u, rule, rule mt, intro allI impI)
          fix h n
          assume h: "(h,n) \<in> funas_term (Fun g ss)"
          show "h \<in> set (fgs (gf h))"
          proof (cases "(h,n) = (g,length ss)")
            case True
            then have "h = g" by auto
            with g gf show ?thesis by auto
          next
            case False
            with h obtain s where s: "s \<in> set ss" and h: "(h,n) \<in> funas_term s" by auto
            from s[unfolded set_conv_nth] obtain i where i: "i < length ss" and si: "s = ss ! i" by force
            from i len have i': "i < length ts" by auto
            from ind[OF i'] rec[OF i'] h[unfolded si] show ?thesis by auto
          qed
        qed
      }
      then have m1m2: "?M1 \<subseteq> ?M2" by blast
      {
        fix u
        assume u: "u \<in> ?M2"
        then obtain g ss where u: "u = Fun g ss"
          and map: "map_funs_term gf (Fun g ss) = Fun f ts"
          and c: "?cf (Fun g ss)"
          by blast
        from map have len: "length ss = length ts" by auto
        from map have g: "gf g = f" by auto
        from map have map: "map (map_funs_term gf) ss = ts" by auto
        from c have g2: "g \<in> set (fgs f)" using g by auto
        have "u \<in> ?M1"
        proof (intro CollectI exI conjI allI impI, rule u, rule g2, rule len)
          fix i
          assume i: "i < length ts"
          with map[unfolded map_nth_eq_conv[OF len]]
          have id: "map_funs_term gf (ss ! i) = ts ! i" by auto
          from i len have si: "ss ! i \<in> set ss" by auto
          show "ss ! i \<in> set (map_funs_term_enum fgs (ts ! i))"
            unfolding ind[OF i]
          proof (intro CollectI conjI impI allI, rule id)
            fix g n
            assume "(g,n) \<in> funas_term (ss ! i)"
            with c si
            show "g \<in> set (fgs (gf g))" by auto
          qed
        qed
      }
      then have m2m1: "?M2 \<subseteq> ?M1" by blast
      show "?M2 = ?M1"
        by (rule, rule m2m1, rule m1m2)
    qed
    finally show ?case unfolding id by simp
  qed
qed

declare map_funs_term_enum.simps[simp del]

end