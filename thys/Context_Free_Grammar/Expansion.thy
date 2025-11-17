(*<*)
theory Expansion
  imports Context_Free_Grammar.Context_Free_Grammar
begin
(*>*)

section \<open>Expansion of Grammars\<close>

text \<open>We consider the set of admissible expansions of grammars.

For a symbol,
one option is not to expand it,
and the other option for (unlocked) nonterminals is to expand to the all rhss.\<close>

definition Expand_sym_ops :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set set" where
"Expand_sym_ops P L x =
  insert {[x]} (case x of Nt A \<Rightarrow> if A \<in> L then {} else {Rhss P A} | _ \<Rightarrow> {})"

lemma Expand_sym_ops_simps:
  "Expand_sym_ops P L (Tm a) = {{[Tm a]}}"
  "Expand_sym_ops P L (Nt A) = insert {[Nt A]} (if A \<in> L then {} else {Rhss P A})"
  by (auto simp: Expand_sym_ops_def)

lemma Expand_sym_ops_self: "{[x]} \<in> Expand_sym_ops P L x"
  by (simp add: Expand_sym_ops_def)

text \<open>Mixed words allow all possible combinations of the options for the symbols.\<close>

fun Expand_syms_ops where
  "Expand_syms_ops P L [] = {{[]}}"
| "Expand_syms_ops P L (x#xs) =
   {\<alpha>s @@ \<beta>s | \<alpha>s \<beta>s. \<alpha>s \<in> Expand_sym_ops P L x \<and> \<beta>s \<in> Expand_syms_ops P L xs}"

lemma Expand_syms_ops_self: "{\<alpha>} \<in> Expand_syms_ops P L \<alpha>"
proof (induction \<alpha>)
  case Nil
  show ?case by simp
next
  case (Cons x \<alpha>)
  have "{x # \<alpha>} = {[x]} @@ {\<alpha>}" by (auto simp: insert_conc)
  with Cons show ?case by (auto intro!: Expand_sym_ops_self)
qed

lemma Expand_sym_ops_Lang_of_Cons:
  assumes X: "X \<in> Expand_sym_ops P L x" and L: "Lhss Q \<subseteq> L"
  shows "Lang_of (P \<union> Q) (x#xs) = Lang_of_set (P \<union> Q) X @@ Lang_of (P \<union> Q) xs"
proof-
  { fix A assume "A \<notin> L"
    with L have "A \<notin> Lhss Q" by auto
    then have "Rhss (P \<union> Q) A = Rhss P A" by (auto simp: Rhss_Un notin_Lhss_iff_Rhss)
    with Lang_of_set_Rhss[of "P \<union> Q" A]
    have "Lang_of_set (P \<union> Q) (Rhss P A) = Lang (P \<union> Q) A" by auto
  } note * = this
  from assms
  show ?thesis
    by (auto simp: Expand_sym_ops_simps Lang_of_Cons * split: if_splits sym.splits)
qed

lemma Expand_syms_ops_Lang_of:
  assumes X: "X \<in> Expand_syms_ops P L \<alpha>" and L: "Lhss Q \<subseteq> L"
  shows "Lang_of (P \<union> Q) \<alpha> = Lang_of_set (P \<union> Q) X"
proof (insert X, induction \<alpha> arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons x \<alpha>)
  from Cons.prems obtain Y Z
    where X: "X = Y @@ Z"
      and Y: "Y \<in> Expand_sym_ops P L x"
      and Z: "Z \<in> Expand_syms_ops P L \<alpha>"
    by auto
  show ?case by (simp add: X Cons.IH[OF Z] Expand_sym_ops_Lang_of_Cons[OF Y L] Lang_of_set_conc)
qed

definition Expand where
"Expand f Q = (\<Union>(A,\<alpha>) \<in> Q. Pair A ` f \<alpha>)"

lemma Lhss_Expand: "Lhss (Expand f Q) \<subseteq> Lhss Q"
  by (auto simp: Lhss_def Expand_def split: prod.splits)

lemma Rhss_Expand: "Rhss (Expand f Q) A = \<Union>(f ` Rhss Q A)"
  by (auto simp: Rhss_def Expand_def)

text \<open>When each production is expanded in an admissible way,
then the language is preserved.\<close>

theorem Lang_Un_Expand:
  assumes f: "\<forall>(A,\<alpha>) \<in> Q. f \<alpha> \<in> Expand_syms_ops P L \<alpha>" and L: "Lhss Q \<subseteq> L"
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
          using f AQ L by auto
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
        with f have f\<alpha>: "f \<alpha> \<in> Expand_syms_ops P L \<alpha>" by auto
        from L Lhss_Expand[of f Q]
        have Lhss: "Lhss (Expand f Q) \<subseteq> L" by auto
        from L A\<alpha>Q have Rhss: "f \<alpha> \<subseteq> Rhss (Expand f Q) A"
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
  assumes f: "\<forall>(A,\<alpha>) \<in> Q. f \<alpha> \<in> Expand_syms_ops P L \<alpha>" and L: "Lhss Q \<subseteq> L"
  shows "Lang (Expand f Q \<union> P) = Lang (Q \<union> P)"
  using Lang_Un_Expand[OF f L] by (simp add: ac_simps)

subsection \<open>Instances\<close>

text \<open>For symbols, we just provide a function to expand it.\<close>

definition Expand_sym :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set" where
"Expand_sym P L x = (case x of Nt A \<Rightarrow> if A \<in> L then {[x]} else Rhss P A | _ \<Rightarrow> {[x]})"

lemma Expand_sym_ops: "Expand_sym P L x \<in> Expand_sym_ops P L x"
  by (auto simp: Expand_sym_def Expand_sym_ops_simps split: sym.splits)

subsubsection \<open>Expanding all nonterminals\<close>

fun Expand_all_syms where
  "Expand_all_syms P L [] = {[]}"
| "Expand_all_syms P L (x#xs) = Expand_sym P L x @@ Expand_all_syms P L xs"

lemma Expand_all_syms_ops: "Expand_all_syms P L xs \<in> Expand_syms_ops P L xs"
  by (induction xs, simp, force simp: Expand_sym_ops)

abbreviation Expand_all where
  "Expand_all P L Q \<equiv> Expand (Expand_all_syms P L) Q"

theorem Lang_Expand_all:
  assumes "Lhss Q \<subseteq> L"
  shows "Lang (Expand_all P L Q \<union> P) = Lang (Q \<union> P)"
  apply (rule Lang_Expand_Un[OF _ assms])
  by (simp add: Expand_all_syms_ops)

subsubsection \<open>Expanding head nonterminals\<close>

definition Expand_hd_syms where
  "Expand_hd_syms P L \<alpha> = (case \<alpha> of [] \<Rightarrow> {[]} | x#xs \<Rightarrow> Expand_sym P L x @@ {xs})"

lemma Expand_hd_syms_ops: "Expand_hd_syms P L xs \<in> Expand_syms_ops P L xs"
  by (auto simp:Expand_hd_syms_def intro!: Expand_sym_ops Expand_syms_ops_self split: list.split)

abbreviation Expand_hd where
  "Expand_hd P L Q \<equiv> Expand (Expand_hd_syms P L) Q"

theorem Lang_Expand_hd:
  assumes "Lhss Q \<subseteq> L"
  shows "Lang (Expand_hd P L Q \<union> P) = Lang (Q \<union> P)"
  apply (rule Lang_Expand_Un[OF _ assms])
  by (simp add: Expand_hd_syms_ops)

end