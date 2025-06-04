(*
Authors: Tobias Nipkow, Akihisa Yamada
*)

section "Context-Free Grammars"

theory Context_Free_Grammar
imports "HOL-Library.Infinite_Typeclass"
begin

(* TODO: make function fresh executable *)
definition fresh :: "('n::infinite) set \<Rightarrow> 'n" where
"fresh A = (SOME x. x \<notin> A)"

lemma fresh_finite: "finite A \<Longrightarrow> fresh A \<notin> A"
unfolding fresh_def by (metis arb_element someI)

declare relpowp.simps(2)[simp del]

lemma bex_pair_conv: "(\<exists>(x,y) \<in> R. P x y) \<longleftrightarrow> (\<exists>x y. (x,y) \<in> R \<and> P x y)"
  by auto

lemma in_image_map_prod: "fgp \<in> map_prod f g ` R \<longleftrightarrow> (\<exists>(x,y)\<in>R. fgp = (f x,g y))"
  by auto


subsection "Symbols and Context-Free Grammars"

text \<open>Most of the theory is based on arbitrary sets of productions.
Finiteness of the set of productions is only required where necessary.
Finiteness of the type of terminal symbols is only required where necessary.
Whenever fresh nonterminals need to be invented, the type of nonterminals is assumed to be infinite.\<close>

datatype ('n,'t) sym = Nt 'n | Tm 't

type_synonym ('n,'t) syms = "('n,'t) sym list"

type_synonym ('n,'t) prod = "'n \<times> ('n,'t) syms"

type_synonym ('n,'t) prods = "('n,'t) prod list"
type_synonym ('n,'t) Prods = "('n,'t) prod set"

datatype ('n,'t) cfg = cfg (prods : "('n,'t) prods") (start : "'n")
datatype ('n,'t) Cfg = Cfg (Prods : "('n,'t) Prods") (Start : "'n")

definition isTm :: "('n, 't) sym \<Rightarrow> bool" where 
"isTm S = (\<exists>a. S = Tm a)"

definition isNt :: "('n, 't) sym \<Rightarrow> bool" where 
"isNt S = (\<exists>A. S = Nt A)"

fun destTm :: "('n, 't) sym  \<Rightarrow> 't" where 
\<open>destTm (Tm a) = a\<close>

lemma isTm_simps[simp]:
  \<open>isTm (Nt A) = False\<close>
  \<open>isTm (Tm a)\<close> 
by (simp_all add: isTm_def)

lemma filter_isTm_map_Tm[simp]: \<open>filter isTm (map Tm xs) = map Tm xs\<close>
by(induction xs) auto

lemma destTm_o_Tm[simp]: \<open>destTm \<circ> Tm = id\<close>
by auto

definition nts_syms :: "('n,'t)syms \<Rightarrow> 'n set" where
"nts_syms w = {A. Nt A \<in> set w}"

definition tms_syms :: "('n,'t)syms \<Rightarrow> 't set" where
"tms_syms w = {a. Tm a \<in> set w}"

definition Nts :: "('n,'t)Prods \<Rightarrow> 'n set" where
  "Nts P = (\<Union>(A,w)\<in>P. {A} \<union> nts_syms w)"

definition Tms :: "('n,'t)Prods \<Rightarrow> 't set" where 
  "Tms P = (\<Union>(A,w)\<in>P. tms_syms w)"

abbreviation nts :: "('n,'t) prods \<Rightarrow> 'n set" where
  "nts P \<equiv> Nts (set P)"

definition Syms :: "('n,'t)Prods \<Rightarrow> ('n,'t) sym set" where 
  "Syms P = (\<Union>(A,w)\<in>P. {Nt A} \<union> set w)"

abbreviation tms :: "('n,'t) prods \<Rightarrow> 't set" where
  "tms P \<equiv> Tms (set P)"

abbreviation syms :: "('n,'t) prods \<Rightarrow> ('n,'t) sym set" where
  "syms P \<equiv> Syms (set P)"

definition Lhss :: "('n, 't) Prods \<Rightarrow> 'n set" where
"Lhss P = (\<Union>(A,w) \<in> P. {A})"

abbreviation lhss :: "('n, 't) prods \<Rightarrow> 'n set" where
"lhss ps \<equiv> Lhss(set ps)"

definition Rhs_Nts :: "('n, 't) Prods \<Rightarrow> 'n set" where
"Rhs_Nts P = (\<Union>(_,w)\<in>P. nts_syms w)"

definition Rhss :: "('n \<times> 'a) set \<Rightarrow> 'n \<Rightarrow> 'a set" where
"Rhss P A = {w. (A,w) \<in> P}"

lemma inj_Nt: "inj Nt"
by (simp add: inj_def)

lemma map_Tm_inject_iff[simp]: "map Tm xs = map Tm ys \<longleftrightarrow> xs = ys"
by (metis sym.inject(2) list.inj_map_strong)

lemma map_Nt_eq_map_Nt_iff[simp]: "map Nt u = map Nt v \<longleftrightarrow> u = v"
by(rule inj_map_eq_map[OF inj_Nt])

lemma map_Nt_eq_map_Tm_iff[simp]: "map Nt u = map Tm v \<longleftrightarrow> u = [] \<and> v = []"
by (cases u) auto

lemmas map_Tm_eq_map_Nt_iff[simp] = eq_iff_swap[OF map_Nt_eq_map_Tm_iff]

lemma nts_syms_Nil[simp]: "nts_syms [] = {}"
unfolding nts_syms_def by auto

lemma nts_syms_Cons[simp]: "nts_syms (a#v) = (case a of Nt A \<Rightarrow> {A} | _ \<Rightarrow> {}) \<union> nts_syms v"
by (auto simp: nts_syms_def split: sym.split)

lemma nts_syms_append[simp]: "nts_syms (u @ v) = nts_syms u \<union> nts_syms v"
by (auto simp: nts_syms_def)

lemma nts_syms_map_Nt[simp]: "nts_syms (map Nt w) = set w"
unfolding nts_syms_def by auto

lemma nts_syms_map_Tm[simp]: "nts_syms (map Tm w) = {}"
unfolding nts_syms_def by auto

lemma in_Nts_iff_in_Syms: "B \<in> Nts P \<longleftrightarrow> Nt B \<in> Syms P"
unfolding Nts_def Syms_def nts_syms_def by (auto)

lemma Nts_Un: "Nts (P1 \<union> P2) = Nts P1 \<union> Nts P2"
by (simp add: Nts_def)

lemma Nts_Lhss_Rhs_Nts: "Nts P = Lhss P \<union> Rhs_Nts P"
unfolding Nts_def Lhss_def Rhs_Nts_def by auto

lemma Nts_nts_syms: "w \<in> Rhss P A \<Longrightarrow> nts_syms w \<subseteq> Nts P"
unfolding Rhss_def Nts_def by blast

lemma Syms_simps[simp]:
  "Syms {} = {}"
  "Syms(insert (A,w) P) = {Nt A} \<union> set w \<union> Syms P"
  "Syms(P \<union> P') = Syms P \<union> Syms P'"
by(auto simp: Syms_def)

lemma Lhss_simps[simp]:
  "Lhss {} = {}"
  "Lhss(insert (A,w) P) = {A} \<union> Lhss P"
  "Lhss(P \<union> P') = Lhss P \<union> Lhss P'"
by(auto simp: Lhss_def)


subsubsection \<open>Finiteness Lemmas\<close>

lemma finite_nts_syms: "finite (nts_syms w)"
proof -
  have "Nt ` {A. Nt A \<in> set w} \<subseteq> set w" by auto
  from finite_inverse_image[OF _ inj_Nt]
  show ?thesis unfolding nts_syms_def using finite_inverse_image[OF _ inj_Nt] by auto
qed

lemma finite_nts: "finite(nts ps)"
unfolding Nts_def by (simp add: finite_nts_syms split_def)

lemma fresh_nts: "fresh(nts ps) \<notin> nts ps"
by(fact fresh_finite[OF finite_nts])

lemma finite_nts_prods_start: "finite(nts(prods g) \<union> {start g})"
unfolding Nts_def by (simp add: finite_nts_syms split_def)

lemma fresh_nts_prods_start: "fresh(nts(prods g) \<union> {start g}) \<notin> nts(prods g) \<union> {start g}"
by(fact fresh_finite[OF finite_nts_prods_start])

lemma finite_Nts: "finite P \<Longrightarrow> finite (Nts P)"
unfolding Nts_def by (simp add: case_prod_beta finite_nts_syms)

lemma finite_Rhss: "finite P \<Longrightarrow> finite (Rhss P A)"
unfolding Rhss_def by (metis Image_singleton finite_Image)


subsection "Derivations"

subsubsection \<open>The standard derivations \<open>\<Rightarrow>\<close>, \<open>\<Rightarrow>*\<close>, \<open>\<Rightarrow>(n)\<close>\<close>

inductive derive :: "('n,'t) Prods \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t)syms \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_ \<Rightarrow>/ _))" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> u @ [Nt A] @ v \<Rightarrow> u @ \<alpha> @ v"

abbreviation deriven ("(2_ \<turnstile>/ (_ /\<Rightarrow>'(_')/ _))" [50, 0, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>(n) v \<equiv> (derive P ^^ n) u v"

abbreviation derives ("(2_ \<turnstile>/ (_/ \<Rightarrow>*/ _))" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>* v \<equiv> ((derive P) ^**) u v"

definition Ders :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> ('n,'t)syms set" where
"Ders P A = {w. P \<turnstile> [Nt A] \<Rightarrow>* w}"

abbreviation ders :: "('n,'t)prods \<Rightarrow> 'n \<Rightarrow> ('n,'t)syms set" where
"ders ps \<equiv> Ders (set ps)"

lemma DersI:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>* w" shows "w \<in> Ders P A"
  using assms by (auto simp: Ders_def)

lemma DersD:
  assumes "w \<in> Ders P A" shows "P \<turnstile> [Nt A] \<Rightarrow>* w"
  using assms by (auto simp: Ders_def)

lemmas DersE = DersD[elim_format]

definition Lang :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't list set" where
"Lang P A = {w. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w}"

abbreviation lang :: "('n,'t)prods \<Rightarrow> 'n \<Rightarrow> 't list set" where
"lang ps A \<equiv> Lang (set ps) A"

abbreviation LangS :: "('n,'t) Cfg \<Rightarrow> 't list set" where
"LangS G \<equiv> Lang (Prods G) (Start G)"

abbreviation langS :: "('n,'t) cfg \<Rightarrow> 't list set" where
"langS g \<equiv> lang (prods g) (start g)"

lemma Lang_Ders: "map Tm ` (Lang P A) \<subseteq> Ders P A"
unfolding Lang_def Ders_def by auto

lemma Lang_eqI_derives:
  assumes "\<And>v. R \<turnstile> [Nt A] \<Rightarrow>* map Tm v \<longleftrightarrow> S \<turnstile> [Nt A] \<Rightarrow>* map Tm v"
  shows "Lang R A = Lang S A"
  by (auto simp: Lang_def assms)

lemma derive_iff: "R \<turnstile> u \<Rightarrow> v \<longleftrightarrow> (\<exists> (A,w) \<in> R. \<exists>u1 u2. u = u1 @ Nt A # u2 \<and> v = u1 @ w @ u2)"
  apply (rule iffI)
   apply (induction rule: derive.induct)
   apply (fastforce)
  using derive.intros by fastforce 

lemma not_derive_from_Tms: "\<not> P \<turnstile> map Tm as \<Rightarrow> w"
by(auto simp add: derive_iff map_eq_append_conv)

lemma deriven_from_TmsD: "P \<turnstile> map Tm as \<Rightarrow>(n) w \<Longrightarrow> w = map Tm as"
by (metis not_derive_from_Tms relpowp_E2)
 
lemma derives_from_Tms_iff: "P \<turnstile> map Tm as \<Rightarrow>* w \<longleftrightarrow> w = map Tm as"
by (meson deriven_from_TmsD rtranclp.rtrancl_refl rtranclp_power)

lemma Un_derive: "R \<union> S \<turnstile> y \<Rightarrow> z \<longleftrightarrow> R \<turnstile> y \<Rightarrow> z \<or> S \<turnstile> y \<Rightarrow> z"
  by (fastforce simp: derive_iff)

lemma derives_rule:
  assumes 2: "(A,w) \<in> R" and 1: "R \<turnstile> x \<Rightarrow>* y @ Nt A # z" and 3: "R \<turnstile> y@w@z \<Rightarrow>* v"
  shows "R \<turnstile> x \<Rightarrow>* v"
proof-
  note 1
  also have "R \<turnstile> y @ Nt A # z \<Rightarrow> y @ w @ z"
    using derive.intros[OF 2] by simp
  also note 3
  finally show ?thesis.
qed

lemma derives_Cons_rule:
  assumes 1: "(A,w) \<in> R" and 2: "R \<turnstile> w @ u \<Rightarrow>* v" shows "R \<turnstile> Nt A # u \<Rightarrow>* v"
  using derives_rule[OF 1, of "Nt A # u" "[]" u v] 2 by auto

lemma deriven_mono: "P \<subseteq> P' \<Longrightarrow> P \<turnstile> u \<Rightarrow>(n) v \<Longrightarrow> P' \<turnstile> u \<Rightarrow>(n) v"
by (metis Un_derive relpowp_mono subset_Un_eq)

lemma derives_mono: "P \<subseteq> P' \<Longrightarrow> P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> P' \<turnstile> u \<Rightarrow>* v"
by (meson deriven_mono rtranclp_power)

lemma Lang_mono: "P \<subseteq> P' \<Longrightarrow> Lang P A \<subseteq> Lang P' A"
by (auto simp: Lang_def derives_mono)


subsubsection "Customized Induction Principles"

lemma deriven_induct[consumes 1, case_names 0 Suc]:
  assumes "P \<turnstile> xs \<Rightarrow>(n) ys"
  and "Q 0 xs"
  and "\<And>n u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>(n) u @ [Nt A] @ v; Q n (u @ [Nt A] @ v); (A,w) \<in> P \<rbrakk> \<Longrightarrow> Q (Suc n) (u @ w @ v)"
  shows "Q n ys"
using assms(1) proof (induction n arbitrary: ys)
  case 0
  thus ?case using assms(2) by auto
next
  case (Suc n)
  from relpowp_Suc_E[OF Suc.prems]
  obtain xs' where n: "P \<turnstile> xs \<Rightarrow>(n) xs'" and 1: "P \<turnstile> xs' \<Rightarrow> ys" by auto
  from derive.cases[OF 1] obtain u A v w where "xs' = u @ [Nt A] @ v" "(A,w) \<in> P" "ys = u @ w @ v"
    by metis
  with Suc.IH[OF n] assms(3) n
  show ?case by blast
qed

lemma derives_induct[consumes 1, case_names base step]:
  assumes "P \<turnstile> xs \<Rightarrow>* ys"
  and "Q xs"
  and "\<And>u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>* u @ [Nt A] @ v; Q (u @ [Nt A] @ v); (A,w) \<in> P \<rbrakk> \<Longrightarrow> Q (u @ w @ v)"
  shows "Q ys"
using assms
proof (induction rule: rtranclp_induct)
  case base
  from this(1) show ?case .
next
  case step
  from derive.cases[OF step(2)] step(1,3-) show ?case by metis
qed

lemma converse_derives_induct[consumes 1, case_names base step]:
  assumes "P \<turnstile> xs \<Rightarrow>* ys"
  and Base: "Q ys"
  and Step: "\<And>u A v w. \<lbrakk> P \<turnstile> u @ [Nt A] @ v \<Rightarrow>* ys; Q (u @ w @ v); (A,w) \<in> P \<rbrakk> \<Longrightarrow> Q (u @ [Nt A] @ v)"
  shows "Q xs"
  using assms(1)
  apply (induction rule: converse_rtranclp_induct)
  by (auto elim!: derive.cases intro!: Base Step intro: derives_rule)


subsubsection "(De)composing derivations"

lemma derive_append:
  "\<G> \<turnstile> u \<Rightarrow> v \<Longrightarrow> \<G> \<turnstile> u@w \<Rightarrow> v@w"
apply(erule derive.cases)
using derive.intros by fastforce

lemma derive_prepend:
  "\<G> \<turnstile> u \<Rightarrow> v \<Longrightarrow> \<G> \<turnstile> w@u \<Rightarrow> w@v"
apply(erule derive.cases)
by (metis append.assoc derive.intros)

lemma deriven_append:
  "P \<turnstile> u \<Rightarrow>(n) v \<Longrightarrow> P \<turnstile> u @ w \<Rightarrow>(n) v @ w"
  apply (induction n arbitrary: v)
   apply simp
  using derive_append by (fastforce simp: relpowp_Suc_right)

lemma deriven_prepend:
  "P \<turnstile> u \<Rightarrow>(n) v \<Longrightarrow> P \<turnstile> w @ u \<Rightarrow>(n) w @ v"
  apply (induction n arbitrary: v)
   apply simp
  using derive_prepend by (fastforce simp: relpowp_Suc_right)

lemma derives_append:
  "P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> P \<turnstile> u@w \<Rightarrow>* v@w"
  by (metis deriven_append rtranclp_power)

lemma derives_prepend:
  "P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> P \<turnstile> w@u \<Rightarrow>* w@v"
  by (metis deriven_prepend rtranclp_power)

lemma derive_append_decomp:
  "P \<turnstile> u@v \<Rightarrow> w \<longleftrightarrow>
  (\<exists>u'. w = u'@v \<and> P \<turnstile> u \<Rightarrow> u') \<or> (\<exists>v'. w = u@v' \<and> P \<turnstile> v \<Rightarrow> v')"
(is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain A r u1 u2
    where Ar: "(A,r) \<in> P"
      and uv: "u@v = u1 @ Nt A # u2"
      and w: "w = u1 @ r @ u2"
    by (auto simp: derive_iff)
  from uv have "(\<exists>s. u2 = s @ v \<and> u = u1 @ Nt A # s) \<or>
  (\<exists>s. u1 = u@s \<and> v = s @ Nt A # u2)"
    by (auto simp: append_eq_append_conv2 append_eq_Cons_conv)
  with Ar w show "?r" by (fastforce simp: derive_iff)
next
  show "?r \<Longrightarrow> ?l"
    by (auto simp add: derive_append derive_prepend)
qed

lemma deriven_append_decomp:
  "P \<turnstile> u @ v \<Rightarrow>(n) w \<longleftrightarrow>
  (\<exists>n1 n2 w1 w2. n = n1 + n2 \<and> w = w1 @ w2 \<and> P \<turnstile> u \<Rightarrow>(n1) w1 \<and> P \<turnstile> v \<Rightarrow>(n2) w2)"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction n arbitrary: u v)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    from Suc.prems
    obtain u' v'
      where or: "P \<turnstile> u \<Rightarrow> u' \<and> v' = v \<or> u' = u \<and> P \<turnstile> v \<Rightarrow> v'"
        and n: "P \<turnstile> u'@v' \<Rightarrow>(n) w"
      by (fastforce simp: relpowp_Suc_left derive_append_decomp)
    from Suc.IH[OF n] or
    show ?case
      apply (elim disjE)
       apply (metis add_Suc relpowp_Suc_I2)
      by (metis add_Suc_right relpowp_Suc_I2)
  qed
next
  assume ?r
  then obtain n1 n2 w1 w2
    where [simp]: "n = n1 + n2" "w = w1 @ w2"
      and u: "P \<turnstile> u \<Rightarrow>(n1) w1" and v: "P \<turnstile> v \<Rightarrow>(n2) w2"
    by auto
  from u deriven_append
  have "P \<turnstile> u @ v \<Rightarrow>(n1) w1 @ v" by fastforce
  also from v deriven_prepend
  have "P \<turnstile> w1 @ v \<Rightarrow>(n2) w1 @ w2" by fastforce
  finally show ?l by auto
qed

lemma derives_append_decomp:
  "P \<turnstile> u @ v \<Rightarrow>* w \<longleftrightarrow> (\<exists>u' v'. P \<turnstile> u \<Rightarrow>* u' \<and> P \<turnstile> v \<Rightarrow>* v' \<and> w = u' @ v')"
  by (auto simp: rtranclp_power deriven_append_decomp)

lemma derives_concat:
  "\<forall>i \<in> set is. P \<turnstile> f i \<Rightarrow>* g i \<Longrightarrow> P \<turnstile> concat(map f is) \<Rightarrow>* concat(map g is)"
proof(induction "is")
  case Nil
  then show ?case by auto
next
  case Cons
  thus ?case by(auto simp: derives_append_decomp less_Suc_eq)
qed

lemma derives_concat1:
  "\<forall>i \<in> set is. P \<turnstile> [f i] \<Rightarrow>* g i \<Longrightarrow> P \<turnstile> map f is \<Rightarrow>* concat(map g is)"
using derives_concat[where f = "\<lambda>i. [f i]"] by auto

lemma derive_Cons:
"P \<turnstile> u \<Rightarrow> v \<Longrightarrow> P \<turnstile> a#u \<Rightarrow> a#v"
  using derive_prepend[of P u v "[a]"] by auto

lemma derives_Cons:
"R \<turnstile> u \<Rightarrow>* v \<Longrightarrow> R \<turnstile> a#u \<Rightarrow>* a#v"
  using derives_prepend[of _ _ _ "[a]"] by simp

lemma derive_from_empty[simp]:
  "P \<turnstile> [] \<Rightarrow> w \<longleftrightarrow> False"
  by (auto simp: derive_iff)

lemma deriven_from_empty[simp]:
  "P \<turnstile> [] \<Rightarrow>(n) w \<longleftrightarrow> n = 0 \<and> w = []"
  by (induct n, auto simp: relpowp_Suc_left)

lemma derives_from_empty[simp]:
  "\<G> \<turnstile> [] \<Rightarrow>* w \<longleftrightarrow> w = []"
  by (auto elim: converse_rtranclpE)

lemma deriven_start1:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w"
  shows "\<exists>\<alpha> m. n = Suc m \<and> P \<turnstile> \<alpha> \<Rightarrow>(m) (map Tm w) \<and> (A,\<alpha>) \<in> P"
proof (cases n)
  case 0
  thus ?thesis
    using assms by auto
next
  case (Suc m)
  then obtain \<alpha> where *: "P \<turnstile> [Nt A] \<Rightarrow> \<alpha>" "P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w"
    using assms by (meson relpowp_Suc_E2)
  from  derive.cases[OF *(1)] have "(A, \<alpha>) \<in> P"
    by (simp add: Cons_eq_append_conv) blast
  thus ?thesis using *(2) Suc by auto
qed

lemma derives_start1: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w  \<Longrightarrow>  \<exists>\<alpha>. P \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<and> (A,\<alpha>) \<in> P"
using deriven_start1 by (metis rtranclp_power)

lemma Lang_empty_if_notin_Lhss: "A \<notin> Lhss P \<Longrightarrow> Lang P A = {}"
unfolding Lhss_def Lang_def
using derives_start1 by fastforce

lemma derive_Tm_Cons:
  "P \<turnstile> Tm a # u \<Rightarrow> v \<longleftrightarrow> (\<exists>w. v = Tm a # w \<and> P \<turnstile> u \<Rightarrow> w)"
  by (fastforce simp: derive_iff Cons_eq_append_conv)

lemma deriven_Tm_Cons:
  "P \<turnstile> Tm a # u \<Rightarrow>(n) v \<longleftrightarrow> (\<exists>w. v = Tm a # w \<and> P \<turnstile> u \<Rightarrow>(n) w)"
proof (induction n arbitrary: u)
  case 0
  show ?case by auto
next
  case (Suc n)
  then show ?case by (force simp: derive_Tm_Cons relpowp_Suc_left OO_def)
qed

lemma derives_Tm_Cons:
  "P \<turnstile> Tm a # u \<Rightarrow>* v \<longleftrightarrow> (\<exists>w. v = Tm a # w \<and> P \<turnstile> u \<Rightarrow>* w)"
  by (metis deriven_Tm_Cons rtranclp_power)

lemma derives_Tm[simp]: "P \<turnstile> [Tm a] \<Rightarrow>* w \<longleftrightarrow> w = [Tm a]"
by(simp add: derives_Tm_Cons)

lemma derive_singleton: "P \<turnstile> [a] \<Rightarrow> u \<longleftrightarrow> (\<exists>A. (A,u) \<in> P \<and> a = Nt A)"
  by (auto simp: derive_iff Cons_eq_append_conv)

lemma deriven_singleton: "P \<turnstile> [a] \<Rightarrow>(n) u \<longleftrightarrow> (
  case n of 0 \<Rightarrow> u = [a]
   | Suc m \<Rightarrow> \<exists>(A,w) \<in> P. a = Nt A \<and> P \<turnstile> w \<Rightarrow>(m) u)"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      by (smt (verit, ccfv_threshold) case_prod_conv derive_singleton nat.simps(5) relpowp_Suc_E2)
  qed
  show "?r \<Longrightarrow> ?l"
    by (auto simp: derive_singleton relpowp_Suc_I2 split: nat.splits)
qed

lemma deriven_Cons_decomp:
  "P \<turnstile> a # u \<Rightarrow>(n) v \<longleftrightarrow>
  (\<exists>v2. v = a#v2 \<and> P \<turnstile> u \<Rightarrow>(n) v2) \<or>
  (\<exists>n1 n2 A w v1 v2. n = Suc (n1 + n2) \<and> v = v1 @ v2 \<and> a = Nt A \<and>
   (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>(n1) v1 \<and> P \<turnstile> u \<Rightarrow>(n2) v2)"
(is "?l = ?r")
proof
  assume ?l
  then obtain n1 n2 v1 v2
    where [simp]: "n = n1 + n2" "v = v1 @ v2"
      and 1: "P \<turnstile> [a] \<Rightarrow>(n1) v1" and 2: "P \<turnstile> u \<Rightarrow>(n2) v2"
    unfolding deriven_append_decomp[of n P "[a]" u v,simplified]
    by auto
  show ?r
  proof (cases "n1")
    case 0
    with 1 2 show ?thesis by auto
  next
    case [simp]: (Suc m)
    with 1 obtain A w
      where [simp]: "a = Nt A" "(A,w) \<in> P" and w: "P \<turnstile> w \<Rightarrow>(m) v1"
      by (auto simp: deriven_singleton)
    with 2
    have "n = Suc (m + n2) \<and> v = v1 @ v2 \<and> a = Nt A \<and>
   (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>(m) v1 \<and> P \<turnstile> u \<Rightarrow>(n2) v2"
      by auto
    then show ?thesis
      by (auto simp: append_eq_Cons_conv)
  qed
next
  assume "?r"
  then
  show "?l"
  proof (elim disjE exE conjE)
    fix v2
    assume [simp]: "v = a # v2" and u: "P \<turnstile> u \<Rightarrow>(n) v2"
    from deriven_prepend[OF u, of "[a]"]
    show ?thesis
      by auto
  next
    fix n1 n2 A w v1 v2
    assume [simp]: "n = Suc (n1 + n2)" "v = v1 @ v2" "a = Nt A"
      and Aw: "(A, w) \<in> P"
      and w: "P \<turnstile> w \<Rightarrow>(n1) v1"
      and u: "P \<turnstile> u \<Rightarrow>(n2) v2"
    have "P \<turnstile> [a] \<Rightarrow> w"
      by (simp add: Aw derive_singleton)
    with w have "P \<turnstile> [a] \<Rightarrow>(Suc n1) v1"
      by (metis relpowp_Suc_I2)
    from deriven_append[OF this]
    have 1: "P \<turnstile> a#u \<Rightarrow>(Suc n1) v1@u"
      by auto
    also have "P \<turnstile> \<dots> \<Rightarrow>(n2) v1@v2"
      using deriven_prepend[OF u].
    finally
    show ?thesis by simp
  qed
qed

lemma derives_Cons_decomp:
  "P \<turnstile> s # u \<Rightarrow>* v \<longleftrightarrow>
  (\<exists>v2. v = s#v2 \<and> P \<turnstile> u \<Rightarrow>* v2) \<or>
  (\<exists>A w v1 v2. v = v1 @ v2 \<and> s = Nt A \<and> (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>* v1 \<and> P \<turnstile> u \<Rightarrow>* v2)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R using deriven_Cons_decomp[of _ P s u v] by (metis rtranclp_power)
next
  assume ?R thus ?L by (meson derives_Cons derives_Cons_rule derives_append_decomp)
qed

lemma deriven_Suc_decomp_left:
  "P \<turnstile> u \<Rightarrow>(Suc n) v \<longleftrightarrow> (\<exists>p A u2 w v1 v2 n1 n2.
  u = p @ Nt A # u2 \<and> v = p @ v1 @ v2 \<and> n = n1 + n2 \<and>
  (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>(n1) v1 \<and>
  P \<turnstile> u2 \<Rightarrow>(n2) v2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?r \<Longrightarrow> ?l"
    by (auto intro!: deriven_prepend simp: deriven_Cons_decomp)
  show "?l \<Longrightarrow> ?r"
  proof(induction u arbitrary: v n)
    case Nil
    then show ?case by auto
  next
    case (Cons a u)
    from Cons.prems[unfolded deriven_Cons_decomp]
    show ?case
    proof (elim disjE exE conjE, goal_cases)
      case (1 v2)
      with Cons.IH[OF this(2)] show ?thesis
        by (metis append_Cons)
    next
      case (2 n1 n2 A w v1 v2)
      then show ?thesis by (fastforce simp:Cons_eq_append_conv)
    qed
  qed
qed

lemma derives_NilD: "P \<turnstile> w \<Rightarrow>* [] \<Longrightarrow> s \<in> set w \<Longrightarrow> P \<turnstile> [s] \<Rightarrow>* []"
proof(induction arbitrary: s rule: converse_derives_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case using derives_append_decomp[where u="[Nt A]" and v=v]
    by (auto simp: derives_append_decomp)
qed

lemma derive_decomp_Tm: "P \<turnstile> \<alpha> \<Rightarrow>(n) map Tm \<beta> \<Longrightarrow>
  \<exists>\<beta>s ns. \<beta> = concat \<beta>s \<and> length \<alpha> = length \<beta>s \<and> length \<alpha> = length ns \<and> sum_list ns = n
          \<and> (\<forall>i < length \<beta>s. P \<turnstile> [\<alpha> ! i] \<Rightarrow>(ns!i) map Tm (\<beta>s ! i))"
  (is "_ \<Longrightarrow> \<exists>\<beta>s ns. ?G \<alpha> \<beta> n \<beta>s ns")
proof (induction \<alpha> arbitrary: \<beta> n)
  case (Cons s \<alpha>)
  from deriven_Cons_decomp[THEN iffD1, OF Cons.prems]
  show ?case
  proof (elim disjE exE conjE)
    fix \<gamma> assume as: "map Tm \<beta> = s # \<gamma>" "P \<turnstile> \<alpha> \<Rightarrow>(n) \<gamma>"
    then obtain s' \<gamma>' where "\<beta> = s' # \<gamma>'"  "P \<turnstile> \<alpha> \<Rightarrow>(n) map Tm \<gamma>'" "s = Tm s'" by force
    from Cons.IH[OF this(2)] obtain \<beta>s ns where *: "?G \<alpha> \<gamma>' n \<beta>s ns"
      by blast
    let ?\<beta>s = "[s']#\<beta>s"
    let ?ns = "0#ns"
    have "?G (s#\<alpha>) \<beta> n ?\<beta>s ?ns"
      using \<open>\<beta> = _\<close> as * by (auto simp: nth_Cons')
    then show ?thesis by blast
  next
    fix n1 n2 A w \<beta>1 \<beta>2
    assume *: "n = Suc (n1 + n2)" "map Tm \<beta> = \<beta>1 @ \<beta>2" "s = Nt A" "(A, w) \<in> P" "P \<turnstile> w \<Rightarrow>(n1) \<beta>1" "P \<turnstile> \<alpha> \<Rightarrow>(n2) \<beta>2"
    then obtain \<beta>1' \<beta>2' where **: "\<beta> = \<beta>1' @ \<beta>2'" "P \<turnstile> w \<Rightarrow>(n1) map Tm \<beta>1'" "P \<turnstile> \<alpha> \<Rightarrow>(n2) map Tm \<beta>2'"
      by (metis (no_types, lifting) append_eq_map_conv)
    from Cons.IH[OF this(3)] obtain \<beta>s ns
      where ***: "?G \<alpha> \<beta>2' n2 \<beta>s ns"
      by blast
    let ?\<beta>s = "\<beta>1'#\<beta>s"
    let ?ns = "Suc n1 # ns"
    from * ** have "P \<turnstile> [(s#\<alpha>) ! 0] \<Rightarrow>(?ns ! 0) map Tm (?\<beta>s ! 0)"
      by (metis derive_singleton nth_Cons_0 relpowp_Suc_I2)
    then have "?G (s#\<alpha>) \<beta> n ?\<beta>s ?ns"
      using * ** *** by (auto simp add: nth_Cons' derives_Cons_rule fold_plus_sum_list_rev)
    then show ?thesis by blast
  qed
qed simp

lemma derives_simul_rules:
  assumes "\<And>A w. (A,w) \<in> P \<Longrightarrow> P' \<turnstile> [Nt A] \<Rightarrow>* w"
  shows "P \<turnstile> w \<Rightarrow>* w' \<Longrightarrow> P' \<turnstile> w \<Rightarrow>* w'"
proof(induction rule: derives_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case
    by (meson assms derives_append derives_prepend rtranclp_trans)
qed

lemma derives_set_subset:
  "P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> set v \<subseteq> set u \<union> Syms P"
proof (induction rule: derives_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case unfolding Syms_def by (auto)
qed

lemma derives_nts_syms_subset:
  "P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> nts_syms v \<subseteq> nts_syms u \<union> Nts P"
proof (induction rule: derives_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case unfolding Nts_def nts_syms_def by (auto)
qed


text \<open>Bottom-up definition of \<open>\<Rightarrow>*\<close>. Single definition yields more compact inductions.
But \<open>derives_induct\<close> may already do the job.\<close>

inductive derives_bu :: "('n, 't) Prods \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_/ \<Rightarrow>bu/ _))" [50, 0, 50] 50) for P :: "('n, 't) Prods"
  where
bu_refl: "P \<turnstile> \<alpha> \<Rightarrow>bu \<alpha>" |
bu_prod: "(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>bu \<alpha>" |
bu_embed: "\<lbrakk> P \<turnstile> \<alpha> \<Rightarrow>bu \<alpha>\<^sub>1 @ \<alpha>\<^sub>2 @ \<alpha>\<^sub>3; P \<turnstile> \<alpha>\<^sub>2 \<Rightarrow>bu \<beta> \<rbrakk> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>bu \<alpha>\<^sub>1 @ \<beta> @ \<alpha>\<^sub>3"

lemma derives_if_bu: "P \<turnstile> \<alpha> \<Rightarrow>bu \<beta> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
proof(induction rule: derives_bu.induct)
  case (bu_refl) then show ?case by simp
next
  case (bu_prod A \<alpha>) then show ?case by (simp add: derives_Cons_rule)
next
  case (bu_embed \<alpha> \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3 \<beta>) then show ?case
    by (meson derives_append derives_prepend rtranclp_trans)
qed

lemma derives_bu_if: "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>bu \<beta>"
proof(induction rule: derives_induct)
  case base
  then show ?case by (simp add: bu_refl)
next
  case (step u A v w)
  then show ?case
    by (meson bu_embed bu_prod)
qed

lemma derives_bu_iff: "P \<turnstile> \<alpha> \<Rightarrow>bu \<beta> \<longleftrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
by (meson derives_bu_if derives_if_bu)


subsubsection "Leftmost/Rightmost Derivations"

inductive derivel :: "('n,'t) Prods \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t)syms \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_ \<Rightarrow>l/ _))" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> map Tm u @ Nt A # v \<Rightarrow>l map Tm u @ \<alpha> @ v"

abbreviation derivels ("(2_ \<turnstile>/ (_ \<Rightarrow>l*/ _))" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>l* v \<equiv> ((derivel P) ^**) u v"

abbreviation derivels1 ("(2_ \<turnstile>/ (_ \<Rightarrow>l+/ _))" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>l+ v \<equiv> ((derivel P) ^++) u v"

abbreviation deriveln ("(2_ \<turnstile>/ (_ \<Rightarrow>l'(_')/ _))" [50, 0, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>l(n) v \<equiv> ((derivel P) ^^ n) u v"

inductive deriver :: "('n,'t) Prods \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t)syms \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_ \<Rightarrow>r/ _))" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> u @ Nt A # map Tm v \<Rightarrow>r u @ \<alpha> @ map Tm v"

abbreviation derivers ("(2_ \<turnstile>/ (_ \<Rightarrow>r*/ _))" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>r* v \<equiv> ((deriver P) ^**) u v"

abbreviation derivers1 ("(2_ \<turnstile>/ (_ \<Rightarrow>r+/ _))" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>r+ v \<equiv> ((deriver P) ^++) u v"

abbreviation derivern ("(2_ \<turnstile>/ (_ \<Rightarrow>r'(_')/ _))" [50, 0, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>r(n) v \<equiv> ((deriver P) ^^ n) u v"


lemma derivel_iff: "R \<turnstile> u \<Rightarrow>l v \<longleftrightarrow>
 (\<exists> (A,w) \<in> R. \<exists>u1 u2. u = map Tm u1 @ Nt A # u2 \<and> v = map Tm u1 @ w @ u2)"
  by (auto simp: derivel.simps)

lemma derivel_from_empty[simp]:
  "P \<turnstile> [] \<Rightarrow>l w \<longleftrightarrow> False" by (auto simp: derivel_iff)

lemma deriveln_from_empty[simp]:
  "P \<turnstile> [] \<Rightarrow>l(n) w \<longleftrightarrow> n = 0 \<and> w = []"
  by (induct n, auto simp: relpowp_Suc_left)

lemma derivels_from_empty[simp]:
  "\<G> \<turnstile> [] \<Rightarrow>l* w \<longleftrightarrow> w = []"
  by (auto elim: converse_rtranclpE)

lemma Un_derivel: "R \<union> S \<turnstile> y \<Rightarrow>l z \<longleftrightarrow> R \<turnstile> y \<Rightarrow>l z \<or> S \<turnstile> y \<Rightarrow>l z"
  by (fastforce simp: derivel_iff)

lemma derivel_append:
  "P \<turnstile> u \<Rightarrow>l v \<Longrightarrow> P \<turnstile> u @ w \<Rightarrow>l v @ w"
  by (force simp: derivel_iff)

lemma deriveln_append:
  "P \<turnstile> u \<Rightarrow>l(n) v \<Longrightarrow> P \<turnstile> u @ w \<Rightarrow>l(n) v @ w"
proof (induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain y where uy: "P \<turnstile> u \<Rightarrow>l y" and yv: "P \<turnstile> y \<Rightarrow>l(n) v"
    by (auto simp: relpowp_Suc_left)
  have "P \<turnstile> u @ w \<Rightarrow>l y @ w"
    using derivel_append[OF uy].
  also from Suc.IH yv have "P \<turnstile> \<dots> \<Rightarrow>l(n) v @ w" by auto
  finally show ?case.
qed

lemma derivels_append:
  "P \<turnstile> u \<Rightarrow>l* v \<Longrightarrow> P \<turnstile> u @ w \<Rightarrow>l* v @ w"
  by (metis deriveln_append rtranclp_power)

lemma derivels1_append:
  "P \<turnstile> u \<Rightarrow>l+ v \<Longrightarrow> P \<turnstile> u @ w \<Rightarrow>l+ v @ w"
  by (metis deriveln_append tranclp_power)

lemma derivel_Tm_Cons:
  "P \<turnstile> Tm a # u \<Rightarrow>l v \<longleftrightarrow> (\<exists>w. v = Tm a # w \<and> P \<turnstile> u \<Rightarrow>l w)"
apply (cases v)
 apply (simp add: derivel_iff)
apply (fastforce simp: derivel.simps Cons_eq_append_conv Cons_eq_map_conv)
done

lemma deriveln_Tm_Cons:
  "P \<turnstile> Tm a # u \<Rightarrow>l(n) v \<longleftrightarrow> (\<exists>w. v = Tm a # w \<and> P \<turnstile> u \<Rightarrow>l(n) w)"
  by (induction n arbitrary: u v;
      fastforce simp: derivel_Tm_Cons relpowp_Suc_right OO_def)

lemma derivels_Tm_Cons:
  "P \<turnstile> Tm a # u \<Rightarrow>l* v \<longleftrightarrow> (\<exists>w. v = Tm a # w \<and> P \<turnstile> u \<Rightarrow>l* w)"
  by (metis deriveln_Tm_Cons rtranclp_power)

lemma derivel_Nt_Cons:
  "P \<turnstile> Nt A # u \<Rightarrow>l v \<longleftrightarrow> (\<exists>w. (A,w) \<in> P \<and> v = w @ u)"
  by (auto simp: derivel_iff Cons_eq_append_conv Cons_eq_map_conv)

lemma derivels1_Nt_Cons:
  "P \<turnstile> Nt A # u \<Rightarrow>l+ v \<longleftrightarrow> (\<exists>w. (A,w) \<in> P \<and> P \<turnstile> w @ u \<Rightarrow>l* v)"
  by (auto simp: tranclp_unfold_left derivel_Nt_Cons OO_def)

lemma derivels_Nt_Cons:
  "P \<turnstile> Nt A # u \<Rightarrow>l* v \<longleftrightarrow> v = Nt A # u \<or> (\<exists>w. (A,w) \<in> P \<and> P \<turnstile> w @ u \<Rightarrow>l* v)"
  by (auto simp: Nitpick.rtranclp_unfold derivels1_Nt_Cons)

lemma deriveln_Nt_Cons:
  "P \<turnstile> Nt A # u \<Rightarrow>l(n) v \<longleftrightarrow> (
  case n of 0 \<Rightarrow> v = Nt A # u
  | Suc m \<Rightarrow> \<exists>w. (A,w) \<in> P \<and> P \<turnstile> w @ u \<Rightarrow>l(m) v)"
  by (cases n) (auto simp: derivel_Nt_Cons relpowp_Suc_left OO_def)

lemma derivel_map_Tm_append:
  "P \<turnstile> map Tm w @ u \<Rightarrow>l v \<longleftrightarrow> (\<exists>x. v = map Tm w @ x \<and> P \<turnstile> u \<Rightarrow>l x)"
  apply (induction w arbitrary:v)
  by (auto simp: derivel_Tm_Cons Cons_eq_append_conv)

lemma deriveln_map_Tm_append:
  "P \<turnstile> map Tm w @ u \<Rightarrow>l(n) v \<longleftrightarrow> (\<exists>x. v = map Tm w @ x \<and> P \<turnstile> u \<Rightarrow>l(n) x)"
  by (induction n arbitrary: u;
      force simp: derivel_map_Tm_append relpowp_Suc_left OO_def)

lemma derivels_map_Tm_append:
  "P \<turnstile> map Tm w @ u \<Rightarrow>l* v \<longleftrightarrow> (\<exists>x. v = map Tm w @ x \<and> P \<turnstile> u \<Rightarrow>l* x)"
  by (metis deriveln_map_Tm_append rtranclp_power)

lemma derivel_not_elim_Tm:
  assumes "P \<turnstile> xs \<Rightarrow>l map Nt w"
  shows "\<exists>v. xs = map Nt v"
proof -
  from assms obtain A \<alpha> u xs' where
         A_w: "(A, \<alpha>)\<in>P"
      and xs: "xs = map Tm u @ Nt A # xs'"
      and ys: "map Nt w = map Tm u @ \<alpha> @ xs'"
    unfolding derivel_iff by fast

  from ys have u1: "u = []"
    by (metis Nil_is_append_conv Nil_is_map_conv hd_append list.map_sel(1) sym.simps(4))
  moreover from ys obtain u' where "xs' = map Nt u'"
    by (metis append_eq_map_conv)

  ultimately have "xs = map Nt (A # u')"
    by (simp add: xs)
  then show ?thesis by blast
qed

lemma deriveln_not_elim_Tm:
  assumes "P \<turnstile> xs \<Rightarrow>l(n) map Nt w"
  shows "\<exists>v. xs = map Nt v"
using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain z where "P \<turnstile> xs \<Rightarrow>l z" and "P \<turnstile> z \<Rightarrow>l(n) map Nt w"
    using relpowp_Suc_E2 by metis
  with Suc show ?case using derivel_not_elim_Tm
    by blast
qed

lemma decomp_derivel_map_Nts:
  assumes "P \<turnstile> map Nt Xs \<Rightarrow>l map Nt Zs"
  shows "\<exists>X Xs' Ys. Xs = X # Xs' \<and> P \<turnstile> [Nt X] \<Rightarrow>l map Nt Ys \<and> Zs = Ys @ Xs'"
using assms unfolding derivel_iff
by (fastforce simp: map_eq_append_conv split: prod.splits)

lemma derivel_imp_derive: "P \<turnstile> u \<Rightarrow>l v \<Longrightarrow> P \<turnstile> u \<Rightarrow> v"
  using derive.simps derivel.cases self_append_conv2 by fastforce

lemma deriveln_imp_deriven:
  "P \<turnstile> u \<Rightarrow>l(n) v \<Longrightarrow> P \<turnstile> u \<Rightarrow>(n) v"
  using relpowp_mono derivel_imp_derive by metis

lemma derivels_imp_derives:
  "P \<turnstile> u \<Rightarrow>l* v \<Longrightarrow> P \<turnstile> u \<Rightarrow>* v"
  by (metis derivel_imp_derive mono_rtranclp)

lemma deriveln_iff_deriven:
  "P \<turnstile> u \<Rightarrow>l(n) map Tm v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>(n) map Tm v"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" using deriveln_imp_deriven.
  assume ?r
  then show "?l"
  proof (induction n arbitrary: u v rule: less_induct)
    case (less n)
    from \<open>P \<turnstile> u \<Rightarrow>(n) map Tm v\<close>
    show ?case
    proof (induction u arbitrary: v)
      case Nil
      then show ?case by simp
    next
      case (Cons a u)
      show ?case
        using Cons.prems(1) Cons.IH less.IH
        by (auto simp: deriven_Cons_decomp deriveln_Tm_Cons deriveln_Nt_Cons)
           (metis deriven_append_decomp lessI)
    qed
  qed
qed

lemma derivels_iff_derives: "P \<turnstile> u \<Rightarrow>l* map Tm v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>* map Tm v"
  using deriveln_iff_deriven
  by (metis rtranclp_power)

lemma deriver_iff: "R \<turnstile> u \<Rightarrow>r v \<longleftrightarrow>
  (\<exists> (A,w) \<in> R. \<exists>u1 u2. u = u1 @ Nt A # map Tm u2 \<and> v = u1 @ w @ map Tm u2)"
  by (auto simp: deriver.simps)

lemma deriver_imp_derive: "R \<turnstile> u \<Rightarrow>r v \<Longrightarrow> R \<turnstile> u \<Rightarrow> v"
  by (auto simp: deriver_iff derive_iff)

lemma derivern_imp_deriven: "R \<turnstile> u \<Rightarrow>r(n) v \<Longrightarrow> R \<turnstile> u \<Rightarrow>(n) v"
  by (metis (no_types, lifting) deriver_imp_derive relpowp_mono)

lemma derivers_imp_derives: "R \<turnstile> u \<Rightarrow>r* v \<Longrightarrow> R \<turnstile> u \<Rightarrow>* v"
  by (metis deriver_imp_derive mono_rtranclp)

lemma deriver_iff_rev_derivel:
  "P \<turnstile> u \<Rightarrow>r v \<longleftrightarrow> map_prod id rev ` P \<turnstile> rev u \<Rightarrow>l rev v" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain A w u1 u2 where Aw: "(A,w) \<in> P"
    and u: "u = u1 @ Nt A # map Tm u2"
    and v: "v = u1 @ w @ map Tm u2" by (auto simp: deriver.simps)
  from bexI[OF _ Aw] have "(A, rev w) \<in> map_prod id rev ` P" by (auto simp: image_def)
  from derivel.intros[OF this, of "rev u2" "rev u1"] u v
  show ?r by (simp add: rev_map)
next
  assume ?r
  then obtain A w u1 u2 where Aw: "(A,w) \<in> P"
    and u: "u = u1 @ Nt A # map Tm u2"
    and v: "v = u1 @ w @ map Tm u2"
    by (auto simp: derivel_iff rev_eq_append_conv rev_map)
  then show ?l by (auto simp: deriver_iff)
qed

lemma rev_deriver_iff_derivel:
  "map_prod id rev ` P \<turnstile> u \<Rightarrow>r v \<longleftrightarrow> P \<turnstile> rev u \<Rightarrow>l rev v"
  by (simp add: deriver_iff_rev_derivel image_image prod.map_comp o_def)

lemma derivern_iff_rev_deriveln:
  "P \<turnstile> u \<Rightarrow>r(n) v \<longleftrightarrow> map_prod id rev ` P \<turnstile> rev u \<Rightarrow>l(n) rev v"
proof (induction n arbitrary: u)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
    apply (unfold relpowp_Suc_left OO_def)
    apply (unfold Suc deriver_iff_rev_derivel)
    by (metis rev_rev_ident)
qed

lemma rev_derivern_iff_deriveln:
  "map_prod id rev ` P \<turnstile> u \<Rightarrow>r(n) v \<longleftrightarrow> P \<turnstile> rev u \<Rightarrow>l(n) rev v"
  by (simp add: derivern_iff_rev_deriveln image_image prod.map_comp o_def)

lemma derivers_iff_rev_derivels:
  "P \<turnstile> u \<Rightarrow>r* v \<longleftrightarrow> map_prod id rev ` P \<turnstile> rev u \<Rightarrow>l* rev v"
  using derivern_iff_rev_deriveln
  by (metis rtranclp_power)

lemma rev_derivers_iff_derivels:
  "map_prod id rev ` P \<turnstile> u \<Rightarrow>r* v \<longleftrightarrow> P \<turnstile> rev u \<Rightarrow>l* rev v"
  by (simp add: derivers_iff_rev_derivels image_image prod.map_comp o_def)

lemma rev_derive:
  "map_prod id rev ` P \<turnstile> u \<Rightarrow> v \<longleftrightarrow> P \<turnstile> rev u \<Rightarrow> rev v"
  by (force simp: derive_iff rev_eq_append_conv bex_pair_conv in_image_map_prod intro: exI[of _ "rev _"])

lemma rev_deriven:
  "map_prod id rev ` P \<turnstile> u \<Rightarrow>(n) v \<longleftrightarrow> P \<turnstile> rev u \<Rightarrow>(n) rev v"
apply (induction n arbitrary: u)
 apply simp
by (auto simp: relpowp_Suc_left OO_def rev_derive intro: exI[of _ "rev _"])

lemma rev_derives:
  "map_prod id rev ` P \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> P \<turnstile> rev u \<Rightarrow>* rev v"
  using rev_deriven
  by (metis rtranclp_power)

lemma derivern_iff_deriven: "P \<turnstile> u \<Rightarrow>r(n) map Tm v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>(n) map Tm v"
  by (auto simp: derivern_iff_rev_deriveln rev_map deriveln_iff_deriven rev_deriven)

lemma derivers_iff_derives: "P \<turnstile> u \<Rightarrow>r* map Tm v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>* map Tm v"
  by (simp add: derivern_iff_deriven rtranclp_power)

lemma deriver_append_map_Tm:
  "P \<turnstile> u @ map Tm w \<Rightarrow>r v \<longleftrightarrow> (\<exists>x. v = x @ map Tm w \<and> P \<turnstile> u \<Rightarrow>r x)"
  by (fastforce simp: deriver_iff_rev_derivel rev_map derivel_map_Tm_append rev_eq_append_conv)

lemma derivern_append_map_Tm:
  "P \<turnstile> u @ map Tm w \<Rightarrow>r(n) v \<longleftrightarrow> (\<exists>x. v = x @ map Tm w \<and> P \<turnstile> u \<Rightarrow>r(n) x)"
  by (fastforce simp: derivern_iff_rev_deriveln rev_map deriveln_map_Tm_append rev_eq_append_conv)

lemma deriver_snoc_Nt:
  "P \<turnstile> u @ [Nt A] \<Rightarrow>r v \<longleftrightarrow> (\<exists>w. (A,w) \<in> P \<and> v = u @ w)"
  by (force simp: deriver_iff_rev_derivel derivel_Nt_Cons rev_eq_append_conv)

lemma deriver_singleton:
  "P \<turnstile> [Nt A] \<Rightarrow>r v \<longleftrightarrow> (A,v) \<in> P"
  using deriver_snoc_Nt[of P "[]"] by auto

lemma derivers1_snoc_Nt:
  "P \<turnstile> u @ [Nt A] \<Rightarrow>r+ v \<longleftrightarrow> (\<exists>w. (A,w) \<in> P \<and> P \<turnstile> u @ w \<Rightarrow>r* v)"
  by (auto simp: tranclp_unfold_left deriver_snoc_Nt OO_def)

lemma derivers_snoc_Nt:
  "P \<turnstile> u @ [Nt A] \<Rightarrow>r* v \<longleftrightarrow> v = u @ [Nt A] \<or> (\<exists>w. (A,w) \<in> P \<and> P \<turnstile> u @ w \<Rightarrow>r* v)"
  by (auto simp: Nitpick.rtranclp_unfold derivers1_snoc_Nt)

lemma derivern_snoc_Tm:
  "P \<turnstile> u @ [Tm a] \<Rightarrow>r(n) v \<longleftrightarrow> (\<exists>w. v = w @ [Tm a] \<and> P \<turnstile> u \<Rightarrow>r(n) w)"
  by (force simp: derivern_iff_rev_deriveln deriveln_Tm_Cons)

lemma derivern_snoc_Nt:
  "P \<turnstile> u @ [Nt A] \<Rightarrow>r(n) v \<longleftrightarrow> (
  case n of 0 \<Rightarrow> v = u @ [Nt A]
  | Suc m \<Rightarrow> \<exists>w. (A,w) \<in> P \<and> P \<turnstile> u @ w \<Rightarrow>r(m) v)"
  by (cases n) (auto simp: relpowp_Suc_left deriver_snoc_Nt OO_def)

lemma derivern_singleton:
  "P \<turnstile> [Nt A] \<Rightarrow>r(n) v \<longleftrightarrow> (
  case n of 0 \<Rightarrow> v = [Nt A]
  | Suc m \<Rightarrow> \<exists>w. (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>r(m) v)"
  using derivern_snoc_Nt[of n P "[]" A v] by (cases n, auto)


subsection \<open>Substitution in Lists\<close>

text \<open>Function \<open>substs y ys xs\<close> replaces every occurrence of \<open>y\<close> in \<open>xs\<close> with the list \<open>ys\<close>\<close>

fun substs :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"substs y ys [] = []" |
"substs y ys (x#xs) = (if x = y then ys @ substs y ys xs else x # substs y ys xs)"

text \<open>Alternative definition, but apparently no simpler to use:
@{prop "substs y ys xs = concat (map (\<lambda>x. if x=y then ys else [x]) xs)"}\<close>

abbreviation "substsNt A \<equiv> substs (Nt A)"

lemma substs_append[simp]: "substs y ys (xs @ xs') = substs y ys xs @ substs y ys xs'"
by (induction xs) auto

lemma substs_skip: "y \<notin> set xs \<Longrightarrow> substs y ys xs = xs"
by (induction xs) auto

lemma susbstsNT_map_Tm[simp]: "substsNt A \<alpha> (map Tm w) = map Tm w"
by(rule substs_skip) auto

lemma substs_len: "length (substs y [y'] xs) = length xs"
by (induction xs) auto

lemma substs_rev: "y' \<notin> set xs \<Longrightarrow> substs y' [y] (substs y [y'] xs) = xs"
by (induction xs) auto

lemma substs_der:
  "(B,v) \<in> P \<Longrightarrow> P \<turnstile> u \<Rightarrow>* substs (Nt B) v u"
proof (induction u)
  case Nil
  then show ?case by simp
next
  case (Cons a u)
  then show ?case
    by (auto simp add: derives_Cons_rule derives_prepend derives_Cons)
qed


subsection \<open>Epsilon-Freeness\<close>

definition Eps_free where "Eps_free R = (\<forall>(_,r) \<in> R. r \<noteq> [])"

abbreviation "eps_free rs == Eps_free(set rs)"

lemma Eps_freeI:
  assumes "\<And>A r. (A,r) \<in> R \<Longrightarrow> r \<noteq> []" shows "Eps_free R"
  using assms by (auto simp: Eps_free_def)

lemma Eps_free_Nil: "Eps_free R \<Longrightarrow> (A,[]) \<notin> R"
  by (auto simp: Eps_free_def)

lemma Eps_freeE_Cons: "Eps_free R \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> \<exists>a u. w = a#u"
  by (cases w, auto simp: Eps_free_def)

lemma Eps_free_derives_Nil:
  assumes R: "Eps_free R" shows "R \<turnstile> l \<Rightarrow>* [] \<longleftrightarrow> l = []" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction rule: converse_derives_induct)
    case base
    show ?case by simp
  next
    case (step u A v w)
    then show ?case by (auto simp: Eps_free_Nil[OF R])
  qed
qed auto

lemma Eps_free_derivels_Nil: "Eps_free R \<Longrightarrow> R \<turnstile> l \<Rightarrow>l* [] \<longleftrightarrow> l = []"
by (meson Eps_free_derives_Nil derivels_from_empty derivels_imp_derives)

lemma Eps_free_deriveln_Nil: "Eps_free R \<Longrightarrow> R \<turnstile> l \<Rightarrow>l(n) [] \<Longrightarrow> l = []"
by (metis Eps_free_derivels_Nil relpowp_imp_rtranclp)

lemma decomp_deriveln_map_Nts:
  assumes "Eps_free P"
  shows "P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l(n) map Nt Zs \<Longrightarrow>
     \<exists>Ys'. Ys' @ Xs = Zs \<and> P \<turnstile> [Nt X] \<Rightarrow>l(n) map Nt Ys'"
proof (induction n arbitrary: Zs)
  case 0
  then show ?case
    by (auto)
next
  case (Suc n)
  then obtain ys where n: "P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l(n) ys" and "P \<turnstile> ys \<Rightarrow>l map Nt Zs"
    using relpowp_Suc_E by metis
  from \<open>P \<turnstile> ys \<Rightarrow>l map Nt Zs\<close> obtain Ys where "ys = map Nt Ys"
    using derivel_not_elim_Tm by blast
  from Suc.IH[of Ys] this n
  obtain Ys' where "Ys = Ys' @ Xs \<and> P \<turnstile> [Nt X] \<Rightarrow>l(n) map Nt Ys'" by auto
  moreover from \<open>ys = _\<close> \<open>P \<turnstile> ys \<Rightarrow>l map Nt Zs\<close> decomp_derivel_map_Nts[of P Ys Zs]
  obtain Y Xs' Ysa where "Ys = Y # Xs' \<and> P \<turnstile> [Nt Y] \<Rightarrow>l map Nt Ysa \<and> Zs = Ysa @ Xs'" by auto
  ultimately show ?case using Eps_free_deriveln_Nil[OF assms, of n "[Nt X]"]
    by (auto simp: Cons_eq_append_conv derivel_Nt_Cons relpowp_Suc_I)
qed

end