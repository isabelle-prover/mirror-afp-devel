section \<open>Subterms and Contexts\<close>

text \<open>
  We define the (proper) sub- and superterm relations on first order terms,
  as well as contexts (you can think of contexts as terms with exactly one hole,
  where we can plug-in another term).
  Moreover, we establish several connections between these concepts as well as
  to other concepts such as substitutions.
\<close>

theory Subterm_and_Context
  imports
    Term
    "Abstract-Rewriting.Abstract_Rewriting"
begin

subsection \<open>Subterms\<close>

text \<open>The \<^emph>\<open>superterm\<close> relation.\<close>
inductive_set
  supteq :: "(('f, 'v) term \<times> ('f, 'v) term) set"
  where
    refl [simp, intro]: "(t, t) \<in> supteq" |
    subt [intro]: "u \<in> set ss \<Longrightarrow> (u, t) \<in> supteq \<Longrightarrow> (Fun f ss, t) \<in> supteq"

text \<open>The \<^emph>\<open>proper superterm\<close> relation.\<close>
inductive_set
  supt :: "(('f, 'v) term \<times> ('f, 'v) term) set"
  where
    arg [simp, intro]: "s \<in> set ss \<Longrightarrow> (Fun f ss, s) \<in> supt" |
    subt [intro]: "s \<in> set ss \<Longrightarrow> (s, t) \<in> supt \<Longrightarrow> (Fun f ss, t) \<in> supt"

hide_const suptp supteqp
hide_fact
  suptp.arg suptp.cases suptp.induct suptp.intros suptp.subt suptp_supt_eq
hide_fact
  supteqp.cases supteqp.induct supteqp.intros supteqp.refl supteqp.subt supteqp_supteq_eq

hide_fact (open) supt.arg supt.subt supteq.refl supteq.subt


subsubsection \<open>Syntactic Sugar\<close>

text \<open>Infix syntax.\<close>
abbreviation "supt_pred s t \<equiv> (s, t) \<in> supt"
abbreviation "supteq_pred s t \<equiv> (s, t) \<in> supteq"
abbreviation (input) "subt_pred s t \<equiv> supt_pred t s"
abbreviation (input) "subteq_pred s t \<equiv> supteq_pred t s"

notation
  supt (\<open>{\<rhd>}\<close>) and
  supt_pred (\<open>(_/ \<rhd> _)\<close> [56, 56] 55) and
  subt_pred (infix \<open>\<lhd>\<close> 55) and
  supteq (\<open>{\<unrhd>}\<close>) and
  supteq_pred (\<open>(_/ \<unrhd> _)\<close> [56, 56] 55) and
  subteq_pred (infix \<open>\<unlhd>\<close> 55)

abbreviation subt (\<open>{\<lhd>}\<close>) where "{\<lhd>} \<equiv> {\<rhd>}\<inverse>"
abbreviation subteq (\<open>{\<unlhd>}\<close>) where "{\<unlhd>} \<equiv> {\<unrhd>}\<inverse>"

text \<open>Quantifier syntax.\<close>

syntax
  "_All_supteq" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<forall>_\<unrhd>_./ _)\<close> [0, 0, 10] 10)
  "_Ex_supteq" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<exists>_\<unrhd>_./ _)\<close> [0, 0, 10] 10)
  "_All_supt" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<forall>_\<rhd>_./ _)\<close> [0, 0, 10] 10)
  "_Ex_supt" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<exists>_\<rhd>_./ _)\<close> [0, 0, 10] 10)

"_All_subteq" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<forall>_\<unlhd>_./ _)\<close> [0, 0, 10] 10)
"_Ex_subteq" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<exists>_\<unlhd>_./ _)\<close> [0, 0, 10] 10)
"_All_subt" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<forall>_\<lhd>_./ _)\<close> [0, 0, 10] 10)
"_Ex_subt" :: "[idt, 'a, bool] \<Rightarrow> bool" (\<open>(3\<exists>_\<lhd>_./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_All_supteq" "_All_supt" "_All_subteq" "_All_subt" \<rightleftharpoons> All and
  "_Ex_supteq" "_Ex_supt" "_Ex_subteq" "_Ex_subt" \<rightleftharpoons> Ex

(* for parsing *)
translations
  "\<forall>x\<unrhd>y. P" \<rightharpoonup> "\<forall>x. x \<unrhd> y \<longrightarrow> P"
  "\<exists>x\<unrhd>y. P" \<rightharpoonup> "\<exists>x. x \<unrhd> y \<and> P"
  "\<forall>x\<rhd>y. P" \<rightharpoonup> "\<forall>x. x \<rhd> y \<longrightarrow> P"
  "\<exists>x\<rhd>y. P" \<rightharpoonup> "\<exists>x. x \<rhd> y \<and> P"

"\<forall>x\<unlhd>y. P" \<rightharpoonup> "\<forall>x. x \<unlhd> y \<longrightarrow> P"
"\<exists>x\<unlhd>y. P" \<rightharpoonup> "\<exists>x. x \<unlhd> y \<and> P"
"\<forall>x\<lhd>y. P" \<rightharpoonup> "\<forall>x. x \<lhd> y \<longrightarrow> P"
"\<exists>x\<lhd>y. P" \<rightharpoonup> "\<exists>x. x \<lhd> y \<and> P"

(* for printing *)
print_translation \<open>
let
  val All_binder = Mixfix.binder_name @{const_syntax All};
  val Ex_binder = Mixfix.binder_name @{const_syntax Ex};
  val impl = @{const_syntax "implies"};
  val conj = @{const_syntax "conj"};
  val supt = @{const_syntax "supt_pred"};
  val supteq = @{const_syntax "supteq_pred"};

  val trans =
   [((All_binder, impl, supt), ("_All_supt", "_All_subt")),
    ((All_binder, impl, supteq), ("_All_supteq", "_All_subteq")),
    ((Ex_binder, conj, supt), ("_Ex_supt", "_Ex_subt")),
    ((Ex_binder, conj, supteq), ("_Ex_supteq", "_Ex_subteq"))];

  fun matches_bound v t =
     case t of (Const ("_bound", _) $ Free (v', _)) => (v = v')
              | _ => false
  fun contains_var v = Term.exists_subterm (fn Free (x, _) => x = v | _ => false)
  fun mk x c n P = Syntax.const c $ Syntax_Trans.mark_bound_body x $ n $ P

  fun tr' q = (q,
    K (fn [Const ("_bound", _) $ Free (v, T), Const (c, _) $ (Const (d, _) $ t $ u) $ P] =>
      (case AList.lookup (=) trans (q, c, d) of
        NONE => raise Match
      | SOME (l, g) =>
          if matches_bound v t andalso not (contains_var v u) then mk (v, T) l u P
          else if matches_bound v u andalso not (contains_var v t) then mk (v, T) g t P
          else raise Match)
     | _ => raise Match));
in [tr' All_binder, tr' Ex_binder] end
\<close>


subsubsection \<open>Transitivity Reasoning for Subterms\<close>

lemma supt_trans [trans]:
  "s \<rhd> t \<Longrightarrow> t \<rhd> u \<Longrightarrow> s \<rhd> u"
  by (induct s t rule: supt.induct) auto

lemma trans_supt: "trans {\<rhd>}" by (auto simp: trans_def dest: supt_trans)


lemma supteq_trans [trans]:
  "s \<unrhd> t \<Longrightarrow> t \<unrhd> u \<Longrightarrow> s \<unrhd> u"
  by (induct s t rule: supteq.induct) (auto)

text \<open>Auxiliary lemmas about term size.\<close>
lemma size_simp5:
  "s \<in> set ss \<Longrightarrow> s \<rhd> t \<Longrightarrow> size t < size s \<Longrightarrow> size t < Suc (size_list size ss)"
  by (induct ss) auto

lemma size_simp6:
  "s \<in> set ss \<Longrightarrow> s \<unrhd> t \<Longrightarrow> size t \<le> size s \<Longrightarrow> size t \<le> Suc (size_list size ss)"
  by (induct ss) auto

lemma size_simp1:
  "t \<in> set ts \<Longrightarrow> size t < Suc (size_list size ts)"
  by (induct ts) auto

lemma size_simp2:
  "t \<in> set ts \<Longrightarrow> size t < Suc (Suc (size s + size_list size ts))"
  by (induct ts) auto

lemma size_simp3:
  assumes "(x, y) \<in> set (zip xs ys)"
  shows "size x < Suc (size_list size xs)"
  using set_zip_leftD [OF assms]  size_simp1 by auto

lemma size_simp4:
  assumes "(x, y) \<in> set (zip xs ys)"
  shows "size y < Suc (size_list size ys)"
  using set_zip_rightD [OF assms] using size_simp1 by auto

lemmas size_simps =
  size_simp1 size_simp2 size_simp3 size_simp4 size_simp5 size_simp6

declare size_simps [termination_simp]

lemma supt_size:
  "s \<rhd> t \<Longrightarrow> size s > size t"
  by (induct rule: supt.induct) (auto simp: size_simps)

lemma supteq_size:
  "s \<unrhd> t \<Longrightarrow> size s \<ge> size t"
  by (induct rule: supteq.induct) (auto simp: size_simps)

text \<open>Reflexivity and Asymmetry.\<close>

lemma reflcl_supteq [simp]:
  "supteq\<^sup>= = supteq" by auto

lemma trancl_supteq [simp]:
  "supteq\<^sup>+ = supteq"
  by (rule trancl_id) (auto simp: trans_def intro: supteq_trans)

lemma rtrancl_supteq [simp]:
  "supteq\<^sup>* = supteq"
  unfolding trancl_reflcl[symmetric] by auto

lemma eq_supteq: "s = t \<Longrightarrow> s \<unrhd> t" by auto

lemma supt_neqD: "s \<rhd> t \<Longrightarrow> s \<noteq> t" using supt_size by auto

lemma supteq_Var [simp]:
  "x \<in> vars_term t \<Longrightarrow> t \<unrhd> Var x"
proof (induct t)
  case (Var y) then show ?case by (cases "x = y") auto
next
  case (Fun f ss) then show ?case by (auto)
qed

lemmas vars_term_supteq = supteq_Var

lemma term_not_arg [iff]:
  "Fun f ss \<notin> set ss" (is "?t \<notin> set ss")
proof
  assume "?t \<in> set ss"
  then have "?t \<rhd> ?t" by (auto)
  then have "?t \<noteq> ?t" by (auto dest: supt_neqD)
  then show False by simp
qed

lemma supt_Fun [simp]:
  assumes "s \<rhd> Fun f ss" (is "s \<rhd> ?t") and "s \<in> set ss"
  shows "False"
proof -
  from \<open>s \<in> set ss\<close> have "?t \<rhd> s" by (auto)
  then have "size ?t > size s" by (rule supt_size)
  from \<open>s \<rhd> ?t\<close> have "size s > size ?t" by (rule supt_size)
  with \<open>size ?t > size s\<close> show False by simp
qed

lemma supt_supteq_conv: "s \<rhd> t = (s \<unrhd> t \<and> s \<noteq> t)"
proof
  assume "s \<rhd> t" then show "s \<unrhd> t \<and> s \<noteq> t"
  proof (induct rule: supt.induct)
    case (subt s ss t f)
    have "s \<unrhd> s" ..
    from \<open>s \<in> set ss\<close> have "Fun f ss \<unrhd> s" by (auto)
    from \<open>s \<unrhd> t \<and> s \<noteq> t\<close> have "s \<unrhd> t" ..
    with \<open>Fun f ss \<unrhd> s\<close> have first: "Fun f ss \<unrhd> t" by (rule supteq_trans)
    from \<open>s \<in> set ss\<close> and \<open>s \<rhd> t\<close> have "Fun f ss \<rhd> t" ..
    then have second: "Fun f ss \<noteq> t" by (auto dest: supt_neqD)
    from first and second show "Fun f ss \<unrhd> t \<and> Fun f ss \<noteq> t" by auto
  qed (auto simp: size_simps)
next
  assume "s \<unrhd> t \<and> s \<noteq> t"
  then have "s \<unrhd> t" and "s \<noteq> t" by auto
  then show "s \<rhd> t" by (induct) (auto)
qed

lemma supt_not_sym: "s \<rhd> t \<Longrightarrow> \<not> (t \<rhd> s)"
proof
  assume "s \<rhd> t" and "t \<rhd> s" then have "s \<rhd> s" by (rule supt_trans)
  then show False unfolding supt_supteq_conv by simp
qed

lemma supt_irrefl[iff]: "\<not> t \<rhd> t"
  using supt_not_sym[of t t] by auto

lemma irrefl_subt: "irrefl {\<lhd>}" by (auto simp: irrefl_def)

lemma supt_imp_supteq: "s \<rhd> t \<Longrightarrow> s \<unrhd> t"
  unfolding supt_supteq_conv by auto

lemma supt_supteq_not_supteq: "s \<rhd> t = (s \<unrhd> t \<and> \<not> (t \<unrhd> s))"
  using supt_not_sym unfolding supt_supteq_conv by auto

lemma supteq_supt_conv: "(s \<unrhd> t) = (s \<rhd> t \<or> s = t)" by (auto simp: supt_supteq_conv)

lemma supteq_antisym:
  assumes "s \<unrhd> t" and "t \<unrhd> s" shows "s = t"
  using assms unfolding supteq_supt_conv by (auto simp: supt_not_sym)

text \<open>The subterm relation is an order on terms.\<close>
interpretation subterm: order "(\<unlhd>)" "(\<lhd>)"
  by (unfold_locales)
    (rule supt_supteq_not_supteq, auto intro: supteq_trans supteq_antisym supt_supteq_not_supteq)


text \<open>More transitivity rules.\<close>
lemma supt_supteq_trans[trans]:
  "s \<rhd> t \<Longrightarrow> t \<unrhd> u \<Longrightarrow> s \<rhd> u"
  by (metis subterm.le_less_trans)

lemma supteq_supt_trans[trans]:
  "s \<unrhd> t \<Longrightarrow> t \<rhd> u \<Longrightarrow> s \<rhd> u"
  by (metis subterm.less_le_trans)

declare subterm.le_less_trans[trans]
declare subterm.less_le_trans[trans]

lemma suptE [elim]: "s \<rhd> t \<Longrightarrow> (s \<unrhd> t \<Longrightarrow> P) \<Longrightarrow> (s \<noteq> t \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: supt_supteq_conv)

lemmas suptI [intro] =
  subterm.dual_order.not_eq_order_implies_strict

lemma supt_supteq_set_conv:
  "{\<rhd>} = {\<unrhd>} - Id"
  using supt_supteq_conv [to_set] by auto

lemma supteq_supt_set_conv:
  "{\<unrhd>} = {\<rhd>}\<^sup>="
  by (auto simp: supt_supteq_conv)

lemma supteq_imp_vars_term_subset:
  "s \<unrhd> t \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  by (induct rule: supteq.induct) auto

lemma set_supteq_into_supt [simp]:
  assumes "t \<in> set ts" and "t \<unrhd> s"
  shows "Fun f ts \<rhd> s"
proof -
  from \<open>t \<unrhd> s\<close> have "t = s \<or> t \<rhd> s" by auto
  then show ?thesis
  proof
    assume "t = s"
    with \<open>t \<in> set ts\<close> show ?thesis by auto
  next
    assume "t \<rhd> s"
    from supt.subt[OF \<open>t \<in> set ts\<close> this] show ?thesis .
  qed
qed

text \<open>The superterm relation is strongly normalizing.\<close>
lemma SN_supt:
  "SN {\<rhd>}"
  unfolding SN_iff_wf by (rule wf_subset) (auto intro: supt_size)

lemma supt_not_refl[elim!]:
  assumes "t \<rhd> t" shows False
proof -
  from assms have "t \<noteq> t" by auto
  then show False by simp
qed

lemma supteq_not_supt [elim]:
  assumes "s \<unrhd> t" and "\<not> (s \<rhd> t)"
  shows "s = t"
  using assms by (induct) auto

lemma supteq_not_supt_conv [simp]:
  "{\<unrhd>} - {\<rhd>} = Id" by auto

lemma supteq_subst [simp, intro]:
  assumes "s \<unrhd> t" shows "s \<cdot> \<sigma> \<unrhd> t \<cdot> \<sigma>"
  using assms
proof (induct rule: supteq.induct)
  case (subt u ss t f)
  from \<open>u \<in> set ss\<close> have "u \<cdot> \<sigma> \<in> set (map (\<lambda>t. t \<cdot> \<sigma>) ss)" "u \<cdot> \<sigma> \<unrhd> u \<cdot> \<sigma>" by auto
  then have "Fun f ss \<cdot> \<sigma> \<unrhd> u \<cdot> \<sigma>" unfolding eval_term.simps by blast
  from this and \<open>u \<cdot> \<sigma> \<unrhd> t \<cdot> \<sigma>\<close> show ?case by (rule supteq_trans)
qed auto

lemma supt_subst [simp, intro]:
  assumes "s \<rhd> t" shows "s \<cdot> \<sigma> \<rhd> t \<cdot> \<sigma>"
  using assms
proof (induct rule: supt.induct)
  case (arg s ss f)
  then have "s \<cdot> \<sigma> \<in> set (map (\<lambda>t. t \<cdot> \<sigma>) ss)" by simp
  then show ?case unfolding eval_term.simps by (rule supt.arg)
next
  case (subt u ss t f)
  from \<open>u \<in> set ss\<close> have "u \<cdot> \<sigma> \<in> set (map (\<lambda>t. t \<cdot> \<sigma>) ss)" by simp
  then have "Fun f ss \<cdot> \<sigma> \<rhd> u \<cdot> \<sigma>" unfolding eval_term.simps by (rule supt.arg)
  with \<open>u \<cdot> \<sigma> \<rhd> t \<cdot> \<sigma>\<close> show ?case by (metis supt_trans)
qed


lemma subterm_induct:
  assumes "\<And>t. \<forall>s\<lhd>t. P s \<Longrightarrow> P t"
  shows [case_names subterm]: "P t"
  by (rule wf_induct[OF wf_measure[of size], of P t], rule assms, insert supt_size, auto)


subsection \<open>Contexts\<close>

text \<open>A \<^emph>\<open>context\<close> is a term containing exactly one \<^emph>\<open>hole\<close>.\<close>

text \<open>We generalize contexts to \<^emph>\<open>abstract contexts\<close> so
that arguments can be arbitrary elements.\<close>

datatype ('f,'a) actxt =
  Hole (\<open>\<box>\<close>) | More 'f "'a list" "('f,'a) actxt" "'a list"

declare actxt.map_ident[simp]

type_synonym ('f,'v) ctxt = "('f,('f,'v) term) actxt"

fun map_ctxt where
  "map_ctxt f v \<box> = \<box>"
| "map_ctxt f v (More g ls C rs) =
  More (f g) (map (map_term f v) ls) (map_ctxt f v C) (map (map_term f v) rs)"

fun vars_ctxt where
  "vars_ctxt \<box> = {}"
| "vars_ctxt (More f ls C rs) =
  \<Union>(vars_term ` set ls) \<union> vars_ctxt C \<union> \<Union>(vars_term ` set rs)"

fun funs_ctxt where
  "funs_ctxt \<box> = {}"
| "funs_ctxt (More f ls C rs) =
  insert f (\<Union>(funs_term ` set ls) \<union> funs_ctxt C \<union> \<Union>(funs_term ` set rs))"

text \<open>
  Interpretation of abstract context.
\<close>

primrec intp_actxt (\<open>(1_\<langle>_;/_\<rangle>)\<close>[999,0,0]100) where
  "I\<langle>Hole;a\<rangle> = a"
| "I\<langle>More f ls C rs;a\<rangle> = I f (ls @ I\<langle>C;a\<rangle> # rs)"

text \<open>
  We also say that we apply a context~@{term C} to a term~@{term t} when we
  replace the hole in a @{term C} by @{term t}.
\<close>

abbreviation ctxt_apply_term (\<open>_\<langle>_\<rangle>\<close> [1000, 0] 1000) where
  "C\<langle>s\<rangle> \<equiv> Fun\<langle>C;s\<rangle>"

primrec actxt_compose (infixl \<open>\<circ>\<^sub>c\<close> 75) where
  "Hole \<circ>\<^sub>c D = D"
| "More f ls C rs \<circ>\<^sub>c D = More f ls (C \<circ>\<^sub>c D) rs"

lemma intp_actxt_compose: "I\<langle>C \<circ>\<^sub>c D;a\<rangle> = I\<langle>C;I\<langle>D;a\<rangle>\<rangle>"
  by (induct C, auto)

thm intp_actxt_compose[of Fun]
abbreviation "map_args_actxt \<equiv> map_actxt (\<lambda>x. x)"

abbreviation eval_ctxt (\<open>(1_\<lbrakk>_\<rbrakk>\<^sub>c/ _)\<close>[999,1,100]100) where
  "I\<lbrakk>C\<rbrakk>\<^sub>c \<alpha> \<equiv> map_args_actxt (\<lambda>t. I\<lbrakk>t\<rbrakk>\<alpha>) C"

lemma eval_ctxt_simps:
  "I\<lbrakk>\<box>\<rbrakk>\<^sub>c \<alpha> = \<box>"
  "I\<lbrakk>More f ls C rs\<rbrakk>\<^sub>c \<alpha> = More f [I\<lbrakk>l\<rbrakk>\<alpha>. l \<leftarrow> ls] (I\<lbrakk>C\<rbrakk>\<^sub>c \<alpha>) [I\<lbrakk>r\<rbrakk>\<alpha>. r \<leftarrow> rs]"
  using actxt.map.

lemma eval_ctxt: "I\<lbrakk>C\<langle>s\<rangle>\<rbrakk>\<alpha> = I\<langle>I\<lbrakk>C\<rbrakk>\<^sub>c \<alpha>; I\<lbrakk>s\<rbrakk>\<alpha>\<rangle>"
  by (induct C, auto)

text \<open>Applying substitutions to contexts.\<close>

abbreviation subst_apply_actxt (infixl \<open>\<cdot>\<^sub>c\<close> 67) where
  "C \<cdot>\<^sub>c \<theta> \<equiv> map_args_actxt (\<lambda>t. t \<cdot> \<theta>) C"

lemma apply_ctxt_Var[simp]: "C \<cdot>\<^sub>c Var = C"
  by (simp add: actxt.map_id0[unfolded id_def])

lemma eval_subst_ctxt: "I\<lbrakk>C \<cdot>\<^sub>c \<theta>\<rbrakk>\<^sub>c \<rho> = I\<lbrakk>C\<rbrakk>\<^sub>c I\<lbrakk>\<theta>\<rbrakk>\<^sub>s \<rho>"
  apply (induct C) by (auto simp: eval_subst[symmetric])

lemmas ctxt_subst_subst[simp] = eval_subst_ctxt[of Fun]

lemma ctxt_eq [simp]:
  "(C\<langle>s\<rangle> = C\<langle>t\<rangle>) = (s = t)" by (induct C) auto

lemma size_ctxt: "size t \<le> size (C\<langle>t\<rangle>)"
  by (induct C) simp_all

lemma size_ne_ctxt: "C \<noteq> \<box> \<Longrightarrow> size t < size (C\<langle>t\<rangle>)"
  by (induct C) force+

interpretation ctxt_monoid_mult: monoid_mult "\<box>" "(\<circ>\<^sub>c)"
proof
  fix C D E :: "('f, 'b) actxt"
  show "C \<circ>\<^sub>c D \<circ>\<^sub>c E = C \<circ>\<^sub>c (D \<circ>\<^sub>c E)" by (induct C) simp_all
  show "\<box> \<circ>\<^sub>c C = C" by simp
  show "C \<circ>\<^sub>c \<box> = C" by (induct C) simp_all
qed

instantiation actxt :: (type, type) monoid_mult
begin
definition [simp]: "1 = \<box>"
definition [simp]: "(*) = (\<circ>\<^sub>c)"
instance by (intro_classes) (simp_all add: ac_simps)
end

lemmas ctxt_ctxt_compose[simp] = intp_actxt_compose[of Fun]

lemmas ctxt_ctxt = ctxt_ctxt_compose [symmetric]

lemmas subst_apply_term_ctxt_apply_distrib [simp] = eval_ctxt[of Fun]

lemma eval_ctxt_compose_distrib:
  "I\<lbrakk>C \<circ>\<^sub>c D\<rbrakk>\<^sub>c \<sigma> = (I\<lbrakk>C\<rbrakk>\<^sub>c \<sigma>) \<circ>\<^sub>c (I\<lbrakk>D\<rbrakk>\<^sub>c \<sigma>)"
  by (induct C) auto

lemmas subst_compose_ctxt_compose_distrib [simp] =
  eval_ctxt_compose_distrib[of Fun]

lemma eval_ctxt_eval_subst:
  "I\<lbrakk>C\<rbrakk>\<^sub>c (I\<lbrakk>\<sigma>\<rbrakk>\<^sub>s \<tau>) = I\<lbrakk>C \<cdot>\<^sub>c \<sigma>\<rbrakk>\<^sub>c \<tau>"
  by (induct C) (auto simp: eval_ctxt eval_subst eval_ctxt_compose_distrib)

lemmas ctxt_compose_subst_compose_distrib [simp] =
  eval_ctxt_eval_subst[of Fun]


subsection \<open>The Connection between Contexts and the Superterm Relation\<close>

lemma ctxt_imp_supteq [simp]:
  shows "C\<langle>t\<rangle> \<unrhd> t" by (induct C) auto

lemma supteq_ctxtE[elim]:
  assumes "s \<unrhd> t" obtains C where "s = C\<langle>t\<rangle>"
  using assms proof (induct arbitrary: thesis)
  case (refl s)
  have "s = \<box>\<langle>s\<rangle>" by simp
  from refl[OF this] show ?case .
next
  case (subt u ss t f)
  then obtain C where "u = C\<langle>t\<rangle>" by auto
  from split_list[OF \<open>u \<in> set ss\<close>] obtain ss1 and ss2 where "ss = ss1 @ u # ss2" by auto
  then have "Fun f ss = (More f ss1 C ss2)\<langle>t\<rangle>" using \<open>u = C\<langle>t\<rangle>\<close> by simp
  with subt show ?case by best
qed

lemma ctxt_supteq[intro]:
  assumes "s = C\<langle>t\<rangle>" shows "s \<unrhd> t"
proof (cases C)
  case Hole then show ?thesis using assms by auto
next
  case (More f ss1 D ss2)
  with assms have s: "s = Fun f (ss1 @ D\<langle>t\<rangle> # ss2)" (is "_ = Fun _ ?ss") by simp
  have "D\<langle>t\<rangle> \<in> set ?ss" by simp
  moreover have "D\<langle>t\<rangle> \<unrhd> t" by (induct D) auto
  ultimately show ?thesis unfolding s ..
qed

lemma supteq_ctxt_conv: "(s \<unrhd> t) = (\<exists>C. s = C\<langle>t\<rangle>)" by auto

lemma supt_ctxtE[elim]:
  assumes "s \<rhd> t" obtains C where "C \<noteq> \<box>" and "s = C\<langle>t\<rangle>"
  using assms
proof (induct arbitrary: thesis)
  case (arg s ss f)
  from split_list[OF \<open>s \<in> set ss\<close>] obtain ss1 and ss2 where ss: "ss = ss1 @ s # ss2" by auto
  let ?C = "More f ss1 \<box> ss2"
  have "?C \<noteq> \<box>" by simp
  moreover have "Fun f ss = ?C\<langle>s\<rangle>" by (simp add: ss)
  ultimately show ?case using arg by best
next
  case (subt s ss t f)
  then obtain C where "C \<noteq> \<box>" and "s = C\<langle>t\<rangle>" by auto
  from split_list[OF \<open>s \<in> set ss\<close>] obtain ss1 and ss2 where ss: "ss = ss1 @ s # ss2" by auto
  have "More f ss1 C ss2 \<noteq> \<box>" by simp
  moreover have "Fun f ss = (More f ss1 C ss2)\<langle>t\<rangle>" using \<open>s = C\<langle>t\<rangle>\<close> by (simp add: ss)
  ultimately show ?case using subt(4) by best
qed

lemma ctxt_supt[intro 2]:
  assumes "C \<noteq> \<box>" and "s = C\<langle>t\<rangle>" shows "s \<rhd> t"
proof (cases C)
  case Hole with assms show ?thesis by simp
next
  case (More f ss1 D ss2)
  with assms have s: "s = Fun f (ss1 @ D\<langle>t\<rangle> # ss2)" by simp
  have "D\<langle>t\<rangle> \<in> set (ss1 @ D\<langle>t\<rangle> # ss2)" by simp
  then have "s \<rhd> D\<langle>t\<rangle>" unfolding s ..
  also have "D\<langle>t\<rangle> \<unrhd> t" by (induct D) auto
  finally show "s \<rhd> t" .
qed

lemma supt_ctxt_conv: "(s \<rhd> t) = (\<exists>C. C \<noteq> \<box> \<and> s = C\<langle>t\<rangle>)" (is "_ = ?rhs")
proof
  assume "s \<rhd> t"
  then have "s \<unrhd> t" and "s \<noteq> t" by auto
  from \<open>s \<unrhd> t\<close> obtain C where "s = C\<langle>t\<rangle>" by auto
  with \<open>s \<noteq> t\<close> have "C \<noteq> \<box>" by auto
  with \<open>s = C\<langle>t\<rangle>\<close> show "?rhs" by auto
next
  assume "?rhs" then show "s \<rhd> t" by auto
qed

lemma nectxt_imp_supt_ctxt: "C \<noteq> \<box> \<Longrightarrow> C\<langle>t\<rangle> \<rhd> t" by auto

lemma supt_var: "\<not> (Var x \<rhd> u)"
proof
  assume "Var x \<rhd> u"
  then obtain C where "C \<noteq> \<box>" and "Var x = C\<langle>u\<rangle>" ..
  then show False by (cases C) auto
qed

lemma supt_const: "\<not> (Fun f [] \<rhd> u)"
proof
  assume "Fun f [] \<rhd> u"
  then obtain C where "C \<noteq> \<box>" and "Fun f [] = C\<langle>u\<rangle>" ..
  then show False by (cases C) auto
qed

lemma supteq_var_imp_eq:
  "(Var x \<unrhd> t) = (t = Var x)" (is "_ = (_ = ?x)")
proof
  assume "t = Var x" then show "Var x \<unrhd> t" by auto
next
  assume st: "?x \<unrhd> t"
  from st obtain C where "?x = C\<langle>t\<rangle>" by best
  then show "t = ?x" by (cases C) auto
qed

lemma Var_supt [elim!]:
  assumes "Var x \<rhd> t" shows P
  using assms supt_var[of x t] by simp

lemma Fun_supt [elim]:
  assumes "Fun f ts \<rhd> s" obtains t where "t \<in> set ts" and "t \<unrhd> s"
  using assms by (cases) (auto simp: supt_supteq_conv)

lemma inj_ctxt_apply_term: "inj (ctxt_apply_term C)"
  by (auto simp: inj_on_def)

lemma ctxt_subst_eq: "(\<And>x. x \<in> vars_ctxt C \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> C \<cdot>\<^sub>c \<sigma> = C \<cdot>\<^sub>c \<tau>"
proof (induct C)
  case (More f bef C aft)
  { fix t
    assume t:"t \<in> set bef"
    have "t \<cdot> \<sigma> = t \<cdot> \<tau>" using t More(2) by (auto intro: term_subst_eq)
  }
  moreover
  { fix t
    assume t:"t \<in> set aft"
    have "t \<cdot> \<sigma> = t \<cdot> \<tau>" using t More(2) by (auto intro: term_subst_eq)
  }
  moreover have "C \<cdot>\<^sub>c \<sigma> = C \<cdot>\<^sub>c \<tau>" using More by auto
  ultimately show ?case by auto
qed auto


text \<open>
  A \<^emph>\<open>signature\<close> is a set of function symbol/arity pairs, where the arity of a function symbol,
  denotes the number of arguments it expects.
\<close>
type_synonym 'f sig = "('f \<times> nat) set"

text \<open>The set of all function symbol/ arity pairs occurring in a term.\<close>
fun funas_term :: "('f, 'v) term \<Rightarrow> 'f sig"
  where
    "funas_term (Var _) = {}" |
    "funas_term (Fun f ts) = {(f, length ts)} \<union> \<Union>(set (map funas_term ts))"

lemma finite_funas_term:
  "finite (funas_term t)"
  by (induct t) auto


lemma supt_imp_funas_term_subset:
  assumes "s \<rhd> t"
  shows "funas_term t \<subseteq> funas_term s"
  using assms by induct auto

lemma supteq_imp_funas_term_subset[simp]:
  assumes "s \<unrhd> t"
  shows "funas_term t \<subseteq> funas_term s"
  using assms by induct auto

text \<open>The set of all function symbol/arity pairs occurring in a context.\<close>
fun funas_ctxt :: "('f, 'v) ctxt \<Rightarrow> 'f sig"
  where
    "funas_ctxt Hole = {}" |
    "funas_ctxt (More f ss1 D ss2) = {(f, Suc (length (ss1 @ ss2)))}
     \<union> funas_ctxt D \<union> \<Union>(set (map funas_term (ss1 @ ss2)))"

lemma funas_term_ctxt_apply [simp]:
  "funas_term (C\<langle>t\<rangle>) = funas_ctxt C \<union> funas_term t"
  by (induct C, auto)

lemma funas_term_subst:
  "funas_term (t \<cdot> \<sigma>) = funas_term t \<union> \<Union>(funas_term ` \<sigma> ` vars_term t)"
  by (induct t) auto

lemma funas_ctxt_compose [simp]:
  "funas_ctxt (C \<circ>\<^sub>c D) = funas_ctxt C \<union> funas_ctxt D"
  by (induct C) auto

lemma funas_ctxt_subst [simp]:
  "funas_ctxt (C \<cdot>\<^sub>c \<sigma>) = funas_ctxt C \<union> \<Union>(funas_term ` \<sigma> ` vars_ctxt C)"
  by (induct C, auto simp: funas_term_subst)


end
