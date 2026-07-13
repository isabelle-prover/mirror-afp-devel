theory MSOinHOL_deep_subst_lemma
  imports MSOinHOL_deep
begin

subsection \<open>First-order machinery (Part A)\<close>

text \<open>Free and bound first-order variable occurrences.\<close>

primrec is_free (infix "free'_in" 900)
  where
    "x free_in (r\<^sup>d(u,v)) = (x = u \<or> x = v)"
  | "x free_in (X\<^sup>d(z)) = (x = z)"
  | "x free_in (\<not>\<^sup>d\<phi>) = (x free_in \<phi>)"
  | "x free_in (\<phi> \<and>\<^sup>d \<psi>) = (x free_in \<phi> \<or> x free_in \<psi>)"
  | "x free_in (\<exists>\<^sup>dy. \<phi>) = (x free_in \<phi> \<and> x \<noteq> y)"
  | "x free_in (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (x free_in \<phi>)"

abbreviation is_not_free (infix "not'_free'_in" 900)
  where "x not_free_in \<phi> \<equiv> \<not> (x free_in \<phi>)"

fun is_bound (infix "bound'_in" 900)
  where
    "x bound_in (r\<^sup>d(u,v)) = False"
  | "x bound_in (X\<^sup>d(z)) = False"
  | "x bound_in (\<not>\<^sup>d\<phi>) = (x bound_in \<phi>)"
  | "x bound_in (\<phi> \<and>\<^sup>d \<psi>) = (x bound_in \<phi> \<or> x bound_in \<psi>)"
  | "x bound_in (\<exists>\<^sup>dy. \<phi>) = (x = y \<or> x bound_in \<phi>)"
  | "x bound_in (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (x bound_in \<phi>)"

abbreviation is_not_bound (infix "not'_bound'_in" 900)
  where "x not_bound_in \<phi> \<equiv> \<not> (x bound_in \<phi>)"

abbreviation occurs (infix "occurs'_in" 900)
  where "x occurs_in \<phi> \<equiv> x free_in \<phi> \<or> x bound_in \<phi>"

abbreviation not_in (infix "not'_in" 900)
  where "x not_in \<phi> \<equiv> x not_free_in \<phi> \<and> x not_bound_in \<phi>"

text \<open>A fresh first-order variable: strictly larger than every first-order
  variable occurring in \<open>\<phi>\<close>.\<close>

primrec fresh ("fresh'(_')")
  where
    "fresh (r\<^sup>d(u,v)) = max (u+1) (v+1)"
  | "fresh (X\<^sup>d(z)) = z+1"
  | "fresh (\<not>\<^sup>d\<phi>) = fresh \<phi>"
  | "fresh (\<phi> \<and>\<^sup>d \<psi>) = max (fresh \<phi>) (fresh \<psi>)"
  | "fresh (\<exists>\<^sup>dx. \<phi>) = max (x+1) (fresh \<phi>)"
  | "fresh (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = fresh \<phi>"

lemma L5: "x bound_in \<phi> \<Longrightarrow> x < (fresh \<phi>)"
  by (induct \<phi>) auto

lemma L6: "x free_in \<phi> \<Longrightarrow> x < (fresh \<phi>)"
  by (induct \<phi>) auto

lemma L7: "(fresh \<phi>) not_in \<phi>"
  using L5 L6 by blast

lemma L8: "max (fresh \<phi>) (fresh \<psi>) not_free_in \<phi>"
  by (metis L6 L7 max.absorb3 max_def)

lemma L9: "max (fresh \<phi>) (fresh \<psi>) not_bound_in \<phi>"
  by (metis L5 L7 max.absorb3 max_def)

lemma L10: "max (fresh \<phi>) (fresh \<psi>) not_free_in \<psi>"
  by (metis L8 max.commute)

lemma L11: "max (fresh \<phi>) (fresh \<psi>) not_bound_in \<psi>"
  by (metis L9 max.commute)

text \<open>Irrelevance lemma: updating a non-free first-order variable does not
  affect truth.\<close>

lemma L12:
  "y not_free_in \<phi> \<Longrightarrow> (\<langle>I,D,E\<rangle>,g[y\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  by (induct \<phi> arbitrary: g G; simp; metis L4 L2)

text \<open>First-order variable-for-variable substitution.  The second-order
  binder descends transparently.\<close>

primrec Subst ("[_\<leftarrow>_]'(_')")
  where
    "[x\<leftarrow>z](r\<^sup>d(u,v)) = r\<^sup>d((if x = u then z else u), (if x = v then z else v))"
  | "[x\<leftarrow>z](X\<^sup>d(w)) = X\<^sup>d(if x = w then z else w)"
  | "[x\<leftarrow>z](\<not>\<^sup>d\<phi>) = \<not>\<^sup>d([x\<leftarrow>z](\<phi>))"
  | "[x\<leftarrow>z](\<phi> \<and>\<^sup>d \<psi>) = ([x\<leftarrow>z](\<phi>) \<and>\<^sup>d [x\<leftarrow>z](\<psi>))"
  | "[x\<leftarrow>z](\<exists>\<^sup>dy. \<phi>) = (if x = y then (\<exists>\<^sup>dy. \<phi>) else (\<exists>\<^sup>dy. [x\<leftarrow>z](\<phi>)))"
  | "[x\<leftarrow>z](\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (\<exists>\<^sup>d\<^sub>2Y. [x\<leftarrow>z](\<phi>))"

lemma L13 [simp]: "size [x\<leftarrow>z](\<phi>) = size \<phi>"
  by (induct \<phi>; auto)

lemma L14 [simp]: "[x\<leftarrow>x](\<phi>) = \<phi>"
  by (induct \<phi>; auto)

lemma L15:
  assumes "x \<noteq> a"
  shows "[a\<leftarrow>z]([a\<leftarrow>x](\<phi>)) = [a\<leftarrow>x](\<phi>)"
  using assms by (induct \<phi>) auto

lemma L16 [simp]:
  assumes "a \<noteq> x"
  shows "a not_free_in ([a\<leftarrow>x](\<phi>))"
  using assms by (induct \<phi>) auto

text \<open>Size-based induction principle (size-based on both existential
  binders).\<close>

lemma SInduct:
  assumes "\<And>r u v. P (r\<^sup>d(u,v))"
    and "\<And>X z. P (X\<^sup>d(z))"
    and "\<And>\<phi>. (\<And>\<psi>. size \<psi> \<le> size \<phi> \<Longrightarrow> P \<psi>) \<Longrightarrow> P (\<not>\<^sup>d\<phi>)"
    and "\<And>\<phi> \<psi>. (\<And>\<chi>. size \<chi> \<le> size \<phi> + size \<psi> \<Longrightarrow> P \<chi>) \<Longrightarrow> P (\<phi> \<and>\<^sup>d \<psi>)"
    and "\<And>y \<phi>. (\<And>\<psi>. size \<psi> \<le> size \<phi> \<Longrightarrow> P \<psi>) \<Longrightarrow> P (\<exists>\<^sup>dy. \<phi>)"
    and "\<And>Y \<phi>. (\<And>\<psi>. size \<psi> \<le> size \<phi> \<Longrightarrow> P \<psi>) \<Longrightarrow> P (\<exists>\<^sup>d\<^sub>2Y. \<phi>)"
  shows "P \<phi>"
  using assms
proof (induct "size \<phi>" arbitrary: \<phi> rule: less_induct)
  case less thus ?case by (induct \<phi>) auto
qed

text \<open>Stronger induction: structural for the propositional cases,
  size-based for the two binders.\<close>

lemma QInduct:
  assumes "\<And>r u v. P (r\<^sup>d(u,v))"
    and "\<And>X z. P (X\<^sup>d(z))"
    and "\<And>\<phi>. P \<phi> \<Longrightarrow> P (\<not>\<^sup>d\<phi>)"
    and "\<And>\<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<and>\<^sup>d \<psi>)"
    and "\<And>y \<phi>. (\<And>\<psi>. size \<psi> \<le> size \<phi> \<Longrightarrow> P \<psi>) \<Longrightarrow> P (\<exists>\<^sup>dy. \<phi>)"
    and "\<And>Y \<phi>. (\<And>\<psi>. size \<psi> \<le> size \<phi> \<Longrightarrow> P \<psi>) \<Longrightarrow> P (\<exists>\<^sup>d\<^sub>2Y. \<phi>)"
  shows "P \<phi>"
  using assms by (induct \<phi> rule: SInduct) auto

text \<open>Substitutability predicate: \<open>z\<close> may safely replace \<open>x\<close> in \<open>\<phi>\<close>
  without capture.\<close>

primrec SubstitutableForIn ("_ is'_subst'_for _ in _" [999,1,999] 999)
  where
    "z is_subst_for x in (r\<^sup>d(u,v)) = True"
  | "z is_subst_for x in (X\<^sup>d(w)) = True"
  | "z is_subst_for x in (\<not>\<^sup>d\<phi>) = (z is_subst_for x in \<phi>)"
  | "z is_subst_for x in (\<phi> \<and>\<^sup>d \<psi>) = (z is_subst_for x in \<phi> \<and> z is_subst_for x in \<psi>)"
  | "z is_subst_for x in (\<exists>\<^sup>dy. \<phi>) = (y = x \<or> (x not_free_in \<phi> \<or> y \<noteq> z) \<and> z is_subst_for x in \<phi>)"
  | "z is_subst_for x in (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (z is_subst_for x in \<phi>)"

text \<open>Substitution lemma: a syntactic \<open>z\<close>-for-\<open>x\<close> substitution
  corresponds to updating the assignment.\<close>

lemma SubstitutionLemma [simp]:
  assumes "z is_subst_for x in \<phi>"
  shows "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d ([x\<leftarrow>z](\<phi>))) = (\<langle>I,D,E\<rangle>,g[x\<leftarrow>(g z)],G \<Turnstile>\<^sup>d \<phi>)"
  using assms by (induction \<phi> arbitrary: g G; auto simp: L12 L2)

text \<open>Alphabetic renaming preparing capture-avoiding substitution.\<close>

fun ren_for_subst
  where
    "ren_for_subst x z (r\<^sup>d(u,v)) = r\<^sup>d(u,v)"
  | "ren_for_subst x z (X\<^sup>d(w)) = X\<^sup>d(w)"
  | "ren_for_subst x z (\<not>\<^sup>d\<phi>) = \<not>\<^sup>d(ren_for_subst x z \<phi>)"
  | "ren_for_subst x z (\<phi> \<and>\<^sup>d \<psi>) = (ren_for_subst x z \<phi> \<and>\<^sup>d ren_for_subst x z \<psi>)"
  | "ren_for_subst x z (\<exists>\<^sup>dy. \<phi>) =
       (if y = z \<and> x free_in \<phi>
        then let f = max (fresh \<phi>) (z+1); \<phi>' = [y\<leftarrow>f](\<phi>)
             in (\<exists>\<^sup>df. ren_for_subst x z \<phi>')
        else \<exists>\<^sup>dy. ren_for_subst x z \<phi>)"
  | "ren_for_subst x z (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = \<exists>\<^sup>d\<^sub>2Y. ren_for_subst x z \<phi>"

lemma L17 [simp]: "size (ren_for_subst x z \<phi>) = size \<phi>"
  by (induct \<phi> arbitrary: z x rule: QInduct; simp add: Let_def)

lemma L18: "\<alpha> not_in \<phi> \<Longrightarrow> \<alpha> is_subst_for \<beta> in \<phi>"
  by (induct \<phi>) auto

lemma L19: "x free_in \<psi> \<Longrightarrow> y \<noteq> x \<Longrightarrow> x free_in [y\<leftarrow>z](\<psi>)"
  by (induct \<psi>) auto

lemma L20 [simp]:
  "x free_in ren_for_subst x z \<phi> = (x free_in \<phi>)"
  by (induct \<phi> rule: QInduct; simp add: Let_def)
     (metis L16 L6 L7 L19 max.absorb3 max_def_raw)

lemma L21:
  "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (ren_for_subst x z \<phi>))"
  by (induct \<phi> arbitrary: z g G rule: QInduct;
      simp add: Let_def;
      smt (verit) L12 L18 L2 L3 L5 L6 SubstitutionLemma
        max.strict_order_iff max_def)

lemma L22: "z is_subst_for x in (ren_for_subst x z \<phi>)"
  by (induct \<phi> rule: QInduct; simp;
      metis L13 SubstitutableForIn.simps(5)
        Suc_n_not_le_n dual_order.refl max.cobounded2)

lemma L23: "x is_subst_for x in \<phi>"
  by (induct \<phi>) auto

lemma L24: "x not_free_in \<phi> \<Longrightarrow> [x\<leftarrow>z](\<phi>) = \<phi>"
  by (induct \<phi>) auto

lemma L26 [simp]: "z bound_in [x\<leftarrow>y](\<phi>) = z bound_in \<phi>"
  by (induct \<phi>) auto

text \<open>Safe (capture-avoiding) first-order substitution: rename first, then
  substitute.\<close>

definition ren_subst ("[_ \<leftarrow>\<^sub>r _]'(_')")
  where "[x \<leftarrow>\<^sub>r z](\<phi>) = [x\<leftarrow>z](ren_for_subst x z \<phi>)"

lemma L27 [simp]:
  "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d [x \<leftarrow>\<^sub>r z](\<phi>)) = (\<langle>I,D,E\<rangle>,g[x\<leftarrow>g z],G \<Turnstile>\<^sup>d \<phi>)"
  using L21 L22 ren_subst_def by auto

lemma L28 [simp]: "size ([x \<leftarrow>\<^sub>r z](\<phi>)) = size \<phi>"
  by (induct \<phi> rule: QInduct) (auto simp: ren_subst_def Let_def)

lemma L29:
  "g onto D \<Longrightarrow> (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (\<exists>\<^sup>dx. \<phi>)) = (\<exists>z. \<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d ([x \<leftarrow>\<^sub>r z](\<phi>)))"
  by (induct \<phi> arbitrary: I g G x rule: QInduct; simp; blast)

subsection \<open>Second-order machinery (Part B)\<close>

primrec is_free2 (infix "free2'_in" 900)
  where
    "X free2_in (r\<^sup>d(u,v)) = False"
  | "X free2_in (Y\<^sup>d(z)) = (X = Y)"
  | "X free2_in (\<not>\<^sup>d\<phi>) = (X free2_in \<phi>)"
  | "X free2_in (\<phi> \<and>\<^sup>d \<psi>) = (X free2_in \<phi> \<or> X free2_in \<psi>)"
  | "X free2_in (\<exists>\<^sup>dy. \<phi>) = (X free2_in \<phi>)"
  | "X free2_in (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (X free2_in \<phi> \<and> X \<noteq> Y)"

abbreviation is_not_free2 (infix "not'_free2'_in" 900)
  where "X not_free2_in \<phi> \<equiv> \<not> (X free2_in \<phi>)"

fun is_bound2 (infix "bound2'_in" 900)
  where
    "X bound2_in (r\<^sup>d(u,v)) = False"
  | "X bound2_in (Y\<^sup>d(z)) = False"
  | "X bound2_in (\<not>\<^sup>d\<phi>) = (X bound2_in \<phi>)"
  | "X bound2_in (\<phi> \<and>\<^sup>d \<psi>) = (X bound2_in \<phi> \<or> X bound2_in \<psi>)"
  | "X bound2_in (\<exists>\<^sup>dy. \<phi>) = (X bound2_in \<phi>)"
  | "X bound2_in (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (X = Y \<or> X bound2_in \<phi>)"

abbreviation is_not_bound2 (infix "not'_bound2'_in" 900)
  where "X not_bound2_in \<phi> \<equiv> \<not> (X bound2_in \<phi>)"

abbreviation not_in2 (infix "not2'_in" 900)
  where "X not2_in \<phi> \<equiv> X not_free2_in \<phi> \<and> X not_bound2_in \<phi>"

primrec fresh2
  where
    "fresh2 (r\<^sup>d(u,v)) = 0"
  | "fresh2 (Y\<^sup>d(z)) = Y+1"
  | "fresh2 (\<not>\<^sup>d\<phi>) = fresh2 \<phi>"
  | "fresh2 (\<phi> \<and>\<^sup>d \<psi>) = max (fresh2 \<phi>) (fresh2 \<psi>)"
  | "fresh2 (\<exists>\<^sup>dy. \<phi>) = fresh2 \<phi>"
  | "fresh2 (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = max (Y+1) (fresh2 \<phi>)"

lemma N5: "X bound2_in \<phi> \<Longrightarrow> X < (fresh2 \<phi>)"
  by (induct \<phi>) auto

lemma N6: "X free2_in \<phi> \<Longrightarrow> X < (fresh2 \<phi>)"
  by (induct \<phi>) auto

lemma N7: "(fresh2 \<phi>) not2_in \<phi>"
  using N5 N6 by blast

lemma N8: "max (fresh2 \<phi>) (fresh2 \<psi>) not_free2_in \<phi>"
  by (metis N6 N7 max.absorb3 max_def)

lemma N9: "max (fresh2 \<phi>) (fresh2 \<psi>) not_bound2_in \<phi>"
  by (metis N5 N7 max.absorb3 max_def)

lemma N10: "max (fresh2 \<phi>) (fresh2 \<psi>) not_free2_in \<psi>"
  by (metis N8 max.commute)

lemma N11: "max (fresh2 \<phi>) (fresh2 \<psi>) not_bound2_in \<psi>"
  by (metis N9 max.commute)

text \<open>Irrelevance lemma for second-order assignments.\<close>

lemma N12:
  "Y not_free2_in \<phi> \<Longrightarrow> (\<langle>I,D,E\<rangle>,g,G\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
  by (induct \<phi> arbitrary: g G; simp; metis M4 M2)

text \<open>Second-order variable-for-variable substitution.  The first-order
  binder descends transparently.\<close>

primrec Subst2 ("[_\<leftarrow>\<^sub>2_]'(_')")
  where
    "[X\<leftarrow>\<^sub>2Z](r\<^sup>d(u,v)) = r\<^sup>d(u,v)"
  | "[X\<leftarrow>\<^sub>2Z](Y\<^sup>d(w)) = (if X = Y then Z else Y)\<^sup>d(w)"
  | "[X\<leftarrow>\<^sub>2Z](\<not>\<^sup>d\<phi>) = \<not>\<^sup>d([X\<leftarrow>\<^sub>2Z](\<phi>))"
  | "[X\<leftarrow>\<^sub>2Z](\<phi> \<and>\<^sup>d \<psi>) = ([X\<leftarrow>\<^sub>2Z](\<phi>) \<and>\<^sup>d [X\<leftarrow>\<^sub>2Z](\<psi>))"
  | "[X\<leftarrow>\<^sub>2Z](\<exists>\<^sup>dy. \<phi>) = (\<exists>\<^sup>dy. [X\<leftarrow>\<^sub>2Z](\<phi>))"
  | "[X\<leftarrow>\<^sub>2Z](\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (if X = Y then (\<exists>\<^sup>d\<^sub>2Y. \<phi>) else (\<exists>\<^sup>d\<^sub>2Y. [X\<leftarrow>\<^sub>2Z](\<phi>)))"

lemma N13 [simp]: "size [X\<leftarrow>\<^sub>2Z](\<phi>) = size \<phi>"
  by (induct \<phi>; auto)

lemma N14 [simp]: "[X\<leftarrow>\<^sub>2X](\<phi>) = \<phi>"
  by (induct \<phi>; auto)

lemma N16 [simp]:
  assumes "A \<noteq> X"
  shows "A not_free2_in ([A\<leftarrow>\<^sub>2X](\<phi>))"
  using assms by (induct \<phi>) auto

primrec SubstitutableForIn2 ("_ is'_subst2'_for _ in _" [999,1,999] 999)
  where
    "Z is_subst2_for X in (r\<^sup>d(u,v)) = True"
  | "Z is_subst2_for X in (Y\<^sup>d(w)) = True"
  | "Z is_subst2_for X in (\<not>\<^sup>d\<phi>) = (Z is_subst2_for X in \<phi>)"
  | "Z is_subst2_for X in (\<phi> \<and>\<^sup>d \<psi>) = (Z is_subst2_for X in \<phi> \<and> Z is_subst2_for X in \<psi>)"
  | "Z is_subst2_for X in (\<exists>\<^sup>dy. \<phi>) = (Z is_subst2_for X in \<phi>)"
  | "Z is_subst2_for X in (\<exists>\<^sup>d\<^sub>2Y. \<phi>) = (Y = X \<or> (X not_free2_in \<phi> \<or> Y \<noteq> Z) \<and> Z is_subst2_for X in \<phi>)"

lemma SubstitutionLemma2 [simp]:
  assumes "Z is_subst2_for X in \<phi>"
  shows "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d ([X\<leftarrow>\<^sub>2Z](\<phi>))) = (\<langle>I,D,E\<rangle>,g,G\<langle>X\<leftarrow>(G Z)\<rangle> \<Turnstile>\<^sup>d \<phi>)"
  using assms by (induction \<phi> arbitrary: g G; auto simp: N12 M2)

fun ren_for_subst2
  where
    "ren_for_subst2 X Z (r\<^sup>d(u,v)) = r\<^sup>d(u,v)"
  | "ren_for_subst2 X Z (Y\<^sup>d(w)) = Y\<^sup>d(w)"
  | "ren_for_subst2 X Z (\<not>\<^sup>d\<phi>) = \<not>\<^sup>d(ren_for_subst2 X Z \<phi>)"
  | "ren_for_subst2 X Z (\<phi> \<and>\<^sup>d \<psi>) = (ren_for_subst2 X Z \<phi> \<and>\<^sup>d ren_for_subst2 X Z \<psi>)"
  | "ren_for_subst2 X Z (\<exists>\<^sup>dy. \<phi>) = \<exists>\<^sup>dy. ren_for_subst2 X Z \<phi>"
  | "ren_for_subst2 X Z (\<exists>\<^sup>d\<^sub>2Y. \<phi>) =
       (if Y = Z \<and> X free2_in \<phi>
        then let f = max (fresh2 \<phi>) (Z+1); \<phi>' = [Y\<leftarrow>\<^sub>2f](\<phi>)
             in (\<exists>\<^sup>d\<^sub>2f. ren_for_subst2 X Z \<phi>')
        else \<exists>\<^sup>d\<^sub>2Y. ren_for_subst2 X Z \<phi>)"

lemma N17 [simp]: "size (ren_for_subst2 X Z \<phi>) = size \<phi>"
  by (induct \<phi> arbitrary: Z X rule: QInduct; simp add: Let_def)

lemma N18: "\<alpha> not2_in \<phi> \<Longrightarrow> \<alpha> is_subst2_for \<beta> in \<phi>"
  by (induct \<phi>) auto

lemma N19: "X free2_in \<psi> \<Longrightarrow> Y \<noteq> X \<Longrightarrow> X free2_in [Y\<leftarrow>\<^sub>2Z](\<psi>)"
  by (induct \<psi>) auto

lemma N20 [simp]:
  "X free2_in ren_for_subst2 X Z \<phi> = (X free2_in \<phi>)"
  by (induct \<phi> rule: QInduct; simp add: Let_def)
     (metis N16 N6 N7 N19 max.absorb3 max_def_raw)

lemma N21:
  "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (ren_for_subst2 X Z \<phi>))"
  by (induct \<phi> arbitrary: Z g G rule: QInduct;
      simp add: Let_def;
      smt (verit) N12 N18 M2 M3 N5 N6 SubstitutionLemma2
        max.strict_order_iff max_def)

lemma N22: "Z is_subst2_for X in (ren_for_subst2 X Z \<phi>)"
  by (induct \<phi> rule: QInduct; simp;
      metis N13 SubstitutableForIn2.simps(6)
        Suc_n_not_le_n dual_order.refl max.cobounded2)

definition ren_subst2 ("[_ \<leftarrow>\<^sub>r\<^sub>2 _]'(_')")
  where "[X \<leftarrow>\<^sub>r\<^sub>2 Z](\<phi>) = [X\<leftarrow>\<^sub>2Z](ren_for_subst2 X Z \<phi>)"

lemma N27 [simp]:
  "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d [X \<leftarrow>\<^sub>r\<^sub>2 Z](\<phi>)) = (\<langle>I,D,E\<rangle>,g,G\<langle>X\<leftarrow>G Z\<rangle> \<Turnstile>\<^sup>d \<phi>)"
  using N21 N22 ren_subst2_def by auto

lemma N28 [simp]: "size ([X \<leftarrow>\<^sub>r\<^sub>2 Z](\<phi>)) = size \<phi>"
  by (induct \<phi> rule: QInduct) (auto simp: ren_subst2_def Let_def)

lemma N29:
  "G onto E \<Longrightarrow> (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d (\<exists>\<^sup>d\<^sub>2X. \<phi>)) = (\<exists>Z. \<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d ([X \<leftarrow>\<^sub>r\<^sub>2 Z](\<phi>)))"
  by (induct \<phi> arbitrary: I g G X rule: QInduct; simp; blast)

end
