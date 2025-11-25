(*<*)
theory Expansion
  imports Context_Free_Grammar.Context_Free_Grammar
begin
(*>*)

section \<open>Expansion of Grammars\<close>

lemma conc_eq_empty_iff: "X @@ Y = {} \<longleftrightarrow> X = {} \<or> Y = {}"
  by auto

lemma Nts_syms_conc: "\<Union>(Nts_syms ` (X @@ Y)) =
 (if X = {} \<or> Y = {} then {} else \<Union>(Nts_syms ` X) \<union> \<Union>(Nts_syms ` Y))"
  by (force elim!: concE)

text \<open>We consider the set of admissible expansions of grammars.

For a symbol,
one option is not to expand it,
and the other option for (expandable) nonterminals is to expand to the all rhss.\<close>

definition Expand_sym_ops :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set set" where
"Expand_sym_ops P X x =
  insert {[x]} (case x of Nt A \<Rightarrow> if A \<in> X then {Rhss P A} else {} | _ \<Rightarrow> {})"

lemma Expand_sym_ops_simps:
  "Expand_sym_ops P X (Tm a) = {{[Tm a]}}"
  "Expand_sym_ops P X (Nt A) = insert {[Nt A]} (if A \<in> X then {Rhss P A} else {})"
  by (auto simp: Expand_sym_ops_def)

lemma Expand_sym_ops_self: "{[x]} \<in> Expand_sym_ops P X x"
  by (simp add: Expand_sym_ops_def)

text \<open>Mixed words allow all possible combinations of the options for the symbols.\<close>

fun Expand_syms_ops :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms set set" where
  "Expand_syms_ops P X [] = {{[]}}"
| "Expand_syms_ops P X (x#xs) =
   {\<alpha>s @@ \<beta>s | \<alpha>s \<beta>s. \<alpha>s \<in> Expand_sym_ops P X x \<and> \<beta>s \<in> Expand_syms_ops P X xs}"

lemma Expand_syms_ops_self: "{\<alpha>} \<in> Expand_syms_ops P X \<alpha>"
proof (induction \<alpha>)
  case Nil
  show ?case by simp
next
  case (Cons x \<alpha>)
  have "{x # \<alpha>} = {[x]} @@ {\<alpha>}" by (auto simp: insert_conc)
  with Cons show ?case by (auto intro!: Expand_sym_ops_self)
qed

lemma Expand_sym_ops_Lang_of_Cons:
  assumes U: "U \<in> Expand_sym_ops P X x" and X: "Lhss Q \<inter> X = {}"
  shows "Lang_of (P \<union> Q) (x#xs) = Lang_of_set (P \<union> Q) U @@ Lang_of (P \<union> Q) xs"
proof-
  { fix A assume "A \<in> X"
    with X have "A \<notin> Lhss Q" by auto
    then have "Rhss (P \<union> Q) A = Rhss P A" by (auto simp: Rhss_Un notin_Lhss_iff_Rhss)
    with Lang_of_set_Rhss[of "P \<union> Q" A]
    have "Lang_of_set (P \<union> Q) (Rhss P A) = Lang (P \<union> Q) A" by auto
  } note * = this
  from assms
  show ?thesis
    by (auto simp: Expand_sym_ops_simps Lang_of_Cons * split: if_splits sym.splits)
qed

lemma Expand_syms_ops_Lang_of:
  assumes U: "U \<in> Expand_syms_ops P L \<alpha>" and L: "Lhss Q \<inter> L = {}"
  shows "Lang_of (P \<union> Q) \<alpha> = Lang_of_set (P \<union> Q) U"
proof (insert U, induction \<alpha> arbitrary: U)
  case Nil
  then show ?case by simp
next
  case (Cons x \<alpha>)
  from Cons.prems obtain V W
    where U: "U = V @@ W"
      and V: "V \<in> Expand_sym_ops P L x"
      and W: "W \<in> Expand_syms_ops P L \<alpha>"
    by auto
  show ?case by (simp add: U Cons.IH[OF W] Expand_sym_ops_Lang_of_Cons[OF V L] Lang_of_set_conc)
qed

definition Expand :: "(('n,'t) syms \<Rightarrow> ('n,'t) syms set) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Expand f P = {(A,\<alpha>') |A \<alpha>'. \<exists>\<alpha>. (A,\<alpha>) \<in> P \<and> \<alpha>' \<in> f \<alpha>}"

lemma Expand_eq_UN[code]:
  "Expand f P = (\<Union>(A,\<alpha>) \<in> P. Pair A ` f \<alpha>)"
  by (auto simp: Expand_def)

lemma Expand_via_Rhss:
  "Expand f P = {(A,\<alpha>). \<alpha> \<in> \<Union>(f ` Rhss P A)}"
  by (auto simp: Expand_def Rhss_def)

lemma Lhss_Expand: "Lhss (Expand f P) \<subseteq> Lhss P"
  by (auto simp: Lhss_def Expand_def split: prod.splits)

lemma Rhss_Expand: "Rhss (Expand f P) A = \<Union>(f ` Rhss P A)"
  by (auto simp: Rhss_def Expand_def)

lemma Rhs_Nts_Expand: "Rhs_Nts (Expand f P) = (\<Union>(A,\<alpha>) \<in> P. \<Union>\<beta> \<in> f \<alpha>. Nts_syms \<beta>)"
  by (auto simp: Expand_def Rhs_Nts_def)

text \<open>When each production is expanded in an admissible way,
then the language is preserved.\<close>

definition Expand_ops :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> (('n,'t) syms \<Rightarrow> ('n,'t) syms set) set" where
"Expand_ops P X = {f. \<forall>\<alpha>. f \<alpha> \<in> Expand_syms_ops P X \<alpha>}"

theorem Lang_Un_Expand:
  assumes f: "f \<in> Expand_ops P X" and X: "X \<inter> Lhss Q = {}"
  shows "Lang (P \<union> Expand f Q) = Lang (P \<union> Q)"
  unfolding Lang_eq_iff_Lang_of_eq
proof (safe intro!: ext elim!: Lang_ofE_deriven)
  show "P \<union> Expand f Q \<turnstile> xs \<Rightarrow>(n) map Tm w \<Longrightarrow> w \<in> Lang_of (P \<union> Q) xs" for xs w n
  proof (induction n arbitrary: xs w rule: less_induct)
    case (less n)
    show ?case
    proof (cases "\<exists>A. Nt A \<in> set xs")
      case False
      with less.prems have "xs = map Tm w"
        by (metis (no_types, lifting) deriven_from_TmsD destTm.cases ex_map_conv)
      then show ?thesis by (auto simp: Lang_of_map_Tm)
    next
      case True
      then obtain ys zs A where xs: "xs = ys @ Nt A # zs" by (metis split_list) 
      from less.prems[unfolded this deriven_Nt_map_Tm]
      obtain \<delta> m l k v u t where A\<delta>: "(A,\<delta>) \<in> P \<union> Expand f Q"
        and Lys: "P \<union> Expand f Q \<turnstile> ys \<Rightarrow>(m) map Tm v"
        and L\<delta>: "P \<union> Expand f Q \<turnstile> \<delta> \<Rightarrow>(l) map Tm u"
        and Lzs: "P \<union> Expand f Q \<turnstile> zs \<Rightarrow>(k) map Tm t"
        and n: "n = Suc (m + l + k)"
        and w: "w = v @ u @ t" by force
      from n have mn: "m < n" and ln: "l < n" and kn: "k < n" by auto
      with less.IH L\<delta> Lys Lzs
      have u: "u \<in> Lang_of (P \<union> Q) \<delta>"
        and v: "v \<in> Lang_of (P \<union> Q) ys"
        and t: "t \<in> Lang_of (P \<union> Q) zs" by auto
      show ?thesis
      proof (cases "(A,\<delta>) \<in> P")
        case True
        have "Lang_of (P \<union> Q) \<delta> \<subseteq> Lang (P \<union> Q) A"
          apply (rule Lang_of_prod_subset)
          using True by simp
        with u v t
        show ?thesis by (auto simp: xs w Lang_of_append Lang_of_Nt_Cons)
      next
        case False
        with A\<delta> obtain \<alpha> where AQ: "(A,\<alpha>) \<in> Q" and \<delta>: "\<delta> \<in> f \<alpha>" by (auto simp: Expand_def)
        from L\<delta>[unfolded \<delta>] less.IH[of l] n
        have "u \<in> Lang_of (P \<union> Q) \<delta>" by auto
        with \<delta> have "u \<in> Lang_of_set (P \<union> Q) (f \<alpha>)"
          by (auto simp: Lang_of_def)
        also have "\<dots> = Lang_of (P \<union> Q) \<alpha>"
          apply (subst Expand_syms_ops_Lang_of)
          using f AQ X by (auto simp: Expand_ops_def)
        also have "\<dots> \<subseteq> Lang (P \<union> Q) A"
          apply (rule Lang_of_prod_subset)
          using AQ by auto
        finally have u: "u \<in> Lang (P \<union> Q) A" by auto
        with v t
        show ?thesis by (simp add: xs w Lang_of_append Lang_of_Nt_Cons)
      qed
    qed
  qed
next
  show "P \<union> Q \<turnstile> xs \<Rightarrow>(n) map Tm w \<Longrightarrow> w \<in> Lang_of (P \<union> Expand f Q) xs" for xs w n
  proof (induction n arbitrary: xs w rule: less_induct)
    case (less n)
    show ?case
    proof (cases "\<exists>A. Nt A \<in> set xs")
      case False
      with less.prems have "xs = map Tm w"
        by (metis (no_types, lifting) deriven_from_TmsD destTm.cases ex_map_conv)
      then show ?thesis by (auto simp: Lang_of_map_Tm)
    next
      case True
      then obtain ys zs A where xs: "xs = ys @ Nt A # zs" by (metis split_list) 
      from less.prems[unfolded this deriven_Nt_map_Tm]
      obtain \<alpha> m l k v u t where A\<alpha>: "(A,\<alpha>) \<in> P \<union> Q"
        and Rys: "P \<union> Q \<turnstile> ys \<Rightarrow>(m) map Tm v"
        and R\<alpha>: "P \<union> Q \<turnstile> \<alpha> \<Rightarrow>(l) map Tm u"
        and Rzs: "P \<union> Q \<turnstile> zs \<Rightarrow>(k) map Tm t"
        and n: "n = Suc (m + l + k)"
        and w: "w = v @ u @ t" by force
      from n have mn: "m < n" and ln: "l < n" and kn: "k < n" by auto
      with R\<alpha> Rys Rzs
      have u: "u \<in> Lang_of (P \<union> Expand f Q) \<alpha>"
        and v: "v \<in> Lang_of (P \<union> Expand f Q) ys"
        and t: "t \<in> Lang_of (P \<union> Expand f Q) zs" by (auto simp: less.IH)
      show ?thesis
      proof (cases "(A,\<alpha>) \<in> P")
        case True
        then have "(A,\<alpha>) \<in> P \<union> Expand f Q" by simp
        from Lang_of_prod_subset[OF this] u
        have "u \<in> Lang (P \<union> Expand f Q) A" by auto
        with v w t
        show ?thesis by (auto simp: xs w Lang_of_append Lang_of_Nt_Cons)
      next
        case False
        with A\<alpha> have A\<alpha>Q: "(A,\<alpha>) \<in> Q" by simp
        with f have f\<alpha>: "f \<alpha> \<in> Expand_syms_ops P X \<alpha>" by (auto simp: Expand_ops_def)
        from X Lhss_Expand[of f Q]
        have Lhss: "Lhss (Expand f Q) \<inter> X = {}" by auto
        from X A\<alpha>Q have Rhss: "f \<alpha> \<subseteq> Rhss (Expand f Q) A"
          by (auto simp: Rhss_def Expand_def)
        from u Expand_syms_ops_Lang_of[OF f\<alpha> Lhss]
        have "u \<in> Lang_of_set (P \<union> Expand f Q) (f \<alpha>)" by auto
        also have "\<dots> \<subseteq> Lang (P \<union> Expand f Q) A" using Rhss
          by (auto simp flip: Lang_of_set_Rhss simp: Rhss_Un)
        finally have "u \<in> \<dots>".
        with v t show ?thesis by (simp add: xs w Lang_of_append Lang_of_Nt_Cons)
      qed
    qed
  qed
qed

corollary Lang_Expand_Un:
  assumes "f \<in> Expand_ops P X" and "X \<inter> Lhss Q = {}"
  shows "Lang (Expand f Q \<union> P) = Lang (Q \<union> P)"
  using Lang_Un_Expand[OF assms] by (simp add: ac_simps)

subsection \<open>Instances\<close>

text \<open>For symbols, we just provide a function to expand it.\<close>

definition Expand_sym :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set" where
"Expand_sym P X x = (case x of Nt A \<Rightarrow> if A \<in> X then Rhss P A else {[x]} | _ \<Rightarrow> {[x]})"

lemma Expand_sym_ops: "Expand_sym P L x \<in> Expand_sym_ops P L x"
  by (auto simp: Expand_sym_def Expand_sym_ops_simps split: sym.splits)

subsubsection \<open>Expanding all nonterminals\<close>

fun Expand_all_syms :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms set" where
  "Expand_all_syms P X [] = {[]}"
| "Expand_all_syms P X (x#xs) = Expand_sym P X x @@ Expand_all_syms P X xs"

lemma Expand_all_syms_eq_foldr:
  "Expand_all_syms P X \<alpha> = foldr (@@) (map (Expand_sym P X) \<alpha>) {[]}"
  by (induction \<alpha>, simp_all)

lemma Expand_all_syms_append:
  "Expand_all_syms P X (\<alpha>@\<beta>) = Expand_all_syms P X \<alpha> @@ Expand_all_syms P X \<beta>"
  by (induction \<alpha> arbitrary: \<beta>, simp_all add: conc_assoc)

lemma Expand_all_syms_ops: "Expand_all_syms P X \<alpha> \<in> Expand_syms_ops P X \<alpha>"
  by (induction \<alpha>, simp, force simp: Expand_sym_ops)

lemma Expand_all_ops: "Expand_all_syms P X \<in> Expand_ops P X"
  by (auto simp: Expand_ops_def Expand_all_syms_ops)

abbreviation Expand_all :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
  "Expand_all P X Q \<equiv> Expand (Expand_all_syms P X) Q"

corollary Lang_Un_Expand_all:
  assumes "X \<inter> Lhss Q = {}"
  shows "Lang (P \<union> Expand_all P X Q) = Lang (P \<union> Q)"
  using Lang_Un_Expand[OF Expand_all_ops assms].

corollary Lang_Expand_all_Un:
  assumes "X \<inter> Lhss Q = {}"
  shows "Lang (Expand_all P X Q \<union> P) = Lang (Q \<union> P)"
  using Lang_Expand_Un[OF Expand_all_ops assms].

text \<open>@{term Expand_all} removes expanded nonterminals and adds those which the
expanded nonterminals depends.\<close>

lemma Expand_all_syms_eq_empty: "Expand_all_syms P X \<alpha> = {} \<longleftrightarrow> \<not> Nts_syms \<alpha> \<inter> X \<subseteq> Lhss P"
  by (induction \<alpha>)
    (auto simp: Expand_sym_def conc_eq_empty_iff notin_Lhss_iff_Rhss[symmetric] split: sym.splits)

lemma Nts_syms_Expand_all:
  "\<Union>(Nts_syms ` Expand_all_syms P X \<alpha>) =
   (if Nts_syms \<alpha> \<inter> X \<subseteq> Lhss P
    then Nts_syms \<alpha> - X \<union> \<Union>(Nts_syms ` \<Union>(Rhss P ` (Nts_syms \<alpha> \<inter> X)))
    else {})"
proof (induction \<alpha>)
  case Nil
  show ?case by simp
next
  case (Cons x \<alpha>)
  then show ?case
    by (auto simp: Expand_sym_def Nts_syms_conc Cons Expand_all_syms_eq_empty
        notin_Lhss_iff_Rhss[symmetric] split: sym.splits)
qed

lemma Rhs_Nts_Expand_all:
  "Rhs_Nts (Expand_all P X Q) =
   (\<Union>(A,\<alpha>) \<in> Q. if Nts_syms \<alpha> \<inter> X \<subseteq> Lhss P
    then Nts_syms \<alpha> - X \<union> \<Union>(Nts_syms ` \<Union>(Rhss P ` (Nts_syms \<alpha> \<inter> X)))
    else {})"
  apply (unfold Rhs_Nts_Expand)
  apply (rule SUP_cong[OF refl])
  apply (rule prod.case_cong[OF refl])
  by (rule Nts_syms_Expand_all)

lemma Rhs_Nts_Expand_all_le:
  "Rhs_Nts (Expand_all P X Q) \<subseteq> Rhs_Nts Q - X \<union> \<Union>(Nts_syms ` \<Union>(Rhss P ` (Rhs_Nts Q \<inter> X)))"
  (is "?l \<subseteq> ?r")
proof-
  have "?l \<subseteq> (\<Union>(A,\<alpha>) \<in> Q. Nts_syms \<alpha> - X \<union> \<Union>(Nts_syms ` \<Union>(Rhss P ` (Nts_syms \<alpha> \<inter> X))))"
    apply (unfold Rhs_Nts_Expand_all)
    apply (rule SUP_mono')
    by (auto simp: if_splits)
  also have "\<dots> = ?r" by (auto simp: Rhs_Nts_def)
  finally show ?thesis.
qed

text \<open>Approximately, \<open>Expand_all\<close> depends on nonterminals that are not expanded and
those that the expanding grammar depends.\<close>

lemma Rhs_Nts_Expand_all_le_Rhs_Nts:
  "Rhs_Nts (Expand_all P X Q) \<subseteq> Rhs_Nts Q - X \<union> Rhs_Nts P"
  (is "?l \<subseteq> ?r")
proof-
  note Rhs_Nts_Expand_all_le
  also have "Rhs_Nts Q - X \<union> \<Union>(Nts_syms ` \<Union>(Rhss P ` (Rhs_Nts Q \<inter> X))) \<subseteq> ?r"
    by (auto simp: Rhss_def Rhs_Nts_def)
  finally show ?thesis.
qed

text \<open>One can remove a non-recursive part of grammar by expanding others
with respect to it.\<close>

lemma Lang_Expand_all_idem:
  assumes PP: "Rhs_Nts P \<inter> Lhss P = {}"
    and PQ: "Lhss P \<inter> Lhss Q = {}" and AP: "A \<notin> Lhss P"
  shows "Lang (Expand_all P (Lhss P) Q) A = Lang (P \<union> Q) A"
  (is "?l = ?r")
proof-
  have "?l = Lang (P \<union> Expand_all P (Lhss P) Q) A"
    apply (rule Lang_disj_Lhss_Un[symmetric])
    using Rhs_Nts_Expand_all_le_Rhs_Nts[of P "Lhss P" Q] PP AP by auto
  also have "\<dots> = Lang (P \<union> Q) A" by (simp add: Lang_Un_Expand_all[OF PQ])
  finally show ?thesis.
qed

lemma Lang_of_Expand_all_idem:
  assumes PP: "Rhs_Nts P \<inter> Lhss P = {}" and PQ: "Lhss P \<inter> Lhss Q = {}"
    and AP: "Nts_syms \<alpha> \<inter> Lhss P = {}"
  shows "Lang_of (Expand_all P (Lhss P) Q) \<alpha> = Lang_of (P \<union> Q) \<alpha>"
  apply (insert AP, induction \<alpha>)
  using Lang_Expand_all_idem[OF PP PQ]
  by (simp_all split: sym.splits add: Lang_of_Cons)

lemma Lang_Expand_all_idem_new:
  assumes PP: "Rhs_Nts P \<inter> Lhss P = {}" and PQ: "Lhss P \<inter> Lhss Q = {}"
    and AP: "A \<in> Lhss P"
  shows "Lang_of_set (Expand_all P (Lhss P) Q) (Rhss P A) = Lang (P \<union> Q) A"
    (is "?l = ?r")
proof-
  have "\<alpha> \<in> Rhss P A \<Longrightarrow> Lang_of (Expand_all P (Lhss P) Q) \<alpha> = Lang_of (P \<union> Q) \<alpha>" for \<alpha>
    apply (rule Lang_of_Expand_all_idem[OF PP PQ])
    using PP by (auto simp: Rhss_def Rhs_Nts_def)
  then have "?l = Lang_of_set (P \<union> Q) (Rhss P A)" by auto
  moreover have "Rhss P A = Rhss (P \<union> Q) A" using AP PQ by (auto simp: Rhss_def dest: in_LhssI)
  ultimately show ?thesis by (simp add: Lang_of_set_Rhss)
qed

lemma Lang_idem_Un_via_Expand_all:
  assumes PP: "Rhs_Nts P \<inter> Lhss P = {}" and PQ: "Lhss P \<inter> Lhss Q = {}"
  shows "Lang (P \<union> Q) A =
    (if A \<in> Lhss P then Lang_of_set (Expand_all P (Lhss P) Q) (Rhss P A)
     else Lang (Expand_all P (Lhss P) Q) A)"
  using Lang_Expand_all_idem[OF assms] Lang_Expand_all_idem_new[OF assms]
  by auto

corollary Lang_Un_idem_via_Expand_all:
  assumes PQ: "Lhss P \<inter> Lhss Q = {}" and QQ: "Rhs_Nts Q \<inter> Lhss Q = {}"
  shows "Lang (P \<union> Q) A =
    (if A \<in> Lhss Q then Lang_of_set (Expand_all Q (Lhss Q) P) (Rhss Q A)
     else Lang (Expand_all Q (Lhss Q) P) A)"
  using Lang_idem_Un_via_Expand_all[of Q P A] assms by (auto simp: ac_simps)

subsubsection \<open>Expanding head nonterminals\<close>

definition Expand_hd_syms :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms set" where
  "Expand_hd_syms P X \<alpha> = (case \<alpha> of [] \<Rightarrow> {[]} | x#xs \<Rightarrow> Expand_sym P X x @@ {xs})"

lemma Expand_hd_ops: "Expand_hd_syms P X \<in> Expand_ops P X"
  by (auto simp: Expand_hd_syms_def Expand_ops_def intro!: Expand_sym_ops Expand_syms_ops_self split: list.split)

abbreviation Expand_hd :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
  "Expand_hd P X Q \<equiv> Expand (Expand_hd_syms P X) Q"

theorem Lang_Expand_hd:
  assumes "X \<inter> Lhss Q = {}"
  shows "Lang (Expand_hd P X Q \<union> P) = Lang (Q \<union> P)"
  using Lang_Expand_Un[OF Expand_hd_ops assms].

end