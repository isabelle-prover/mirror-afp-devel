(*
Authors: Markus Gschoßmann, Tobias Nipkow
*)

section \<open>Renaming Nonterminals\<close>

theory Renaming_CFG
imports Context_Free_Grammar
begin

text \<open>This theory provides lemmas that relate derivations w.r.t. some set of productions \<open>P\<close>
to derivations w.r.t. a renaming of the nonterminals in \<open>P\<close>.\<close>

fun rename_sym :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) sym \<Rightarrow> ('new,'t) sym" where
"rename_sym f (Nt n) = Nt (f n)" |
"rename_sym f (Tm t) = Tm t"

abbreviation "rename_syms f \<equiv> map (rename_sym f)"

fun rename_prod :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) prod \<Rightarrow> ('new,'t) prod" where
"rename_prod f (A,w) = (f A, rename_syms f w)"

abbreviation "rename_Prods f P \<equiv> rename_prod f ` P"

lemma rename_sym_o_Tm[simp]: "rename_sym f \<circ> Tm = Tm"
by(rule ext) simp

lemma Nt_notin_rename_syms_if_notin_range:
  "x \<notin> range f \<Longrightarrow> Nt x \<notin> set (rename_syms f w)"
by(auto elim!: rename_sym.elims[OF sym])

lemma in_Nts_rename_Prods: "B \<in> Nts (rename_Prods f P) = (\<exists>A \<in> Nts P. f A = B)"
unfolding Nts_def nts_syms_def by(force split: prod.splits elim!: rename_sym.elims[OF sym])

lemma rename_preserves_deriven:
   "P \<turnstile> \<alpha> \<Rightarrow>(n) \<beta> \<Longrightarrow> rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>(n) rename_syms f \<beta>"
proof (induction rule: deriven_induct)
  case 0
  then show ?case by simp
next
  let ?F = "rename_syms f"
  case (Suc n u A v w)
  then have "(f A, rename_syms f w) \<in> rename_Prods f P"
    by (metis image_eqI rename_prod.simps) 
  from derive.intros[OF this] have "rename_Prods f P \<turnstile> ?F u @ ?F [Nt A] @ ?F v \<Rightarrow> ?F u @ ?F w @ ?F v"
    by auto
  with Suc show ?case
    by (simp add: relpowp_Suc_I)
qed

lemma rename_preserves_derives:
   "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>* rename_syms f \<beta>"
by (meson rename_preserves_deriven rtranclp_power)

lemma rename_preserves_derivel:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>l \<beta>"
  shows "rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>l rename_syms f \<beta>"
proof -
  from assms obtain A w u1 u2
    where A_w_u1_u2: "(A,w) \<in> P \<and> \<alpha> = map Tm u1 @ Nt A # u2 \<and> \<beta> = map Tm u1 @ w @ u2"
    unfolding derivel_iff by fast
  then have "(f A, rename_syms f w) \<in> (rename_Prods f P) \<and> 
             rename_syms f \<alpha> = map Tm u1 @ Nt (f A) # rename_syms f u2 \<and>
             rename_syms f \<beta> = map Tm u1 @ rename_syms f w @ rename_syms f u2"
    by force
  then have "\<exists> (A,w) \<in> rename_Prods f P.
        \<exists>u1 u2. rename_syms f \<alpha> = map Tm u1 @ Nt A # u2 \<and> rename_syms f \<beta> = map Tm u1 @ w @ u2"
    by blast
  then show ?thesis by (simp only: derivel_iff)
qed

lemma rename_preserves_deriveln:
  "P \<turnstile> \<alpha> \<Rightarrow>l(n) \<beta> \<Longrightarrow> rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>l(n) rename_syms f \<beta>"
proof (induction n arbitrary: \<beta>)
  case 0
  then show ?case by simp
next
  case Suc then show ?case
    by (metis relpowp_Suc_E relpowp_Suc_I rename_preserves_derivel)
qed

lemma rename_preserves_derivels:
  "P \<turnstile> \<alpha> \<Rightarrow>l* \<beta> \<Longrightarrow> rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>l* rename_syms f \<beta>"
by (meson rename_preserves_deriveln rtranclp_power)

lemma rename_deriven_iff_inj:
fixes P :: "('a,'t)Prods"
assumes "inj_on f (Nts P \<union> nts_syms \<alpha> \<union> nts_syms \<beta>)"
shows "rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>(n) rename_syms f \<beta> \<longleftrightarrow> P \<turnstile> \<alpha> \<Rightarrow>(n) \<beta>" (is "?l \<longleftrightarrow> ?r")
proof
  show "?r \<Longrightarrow> ?l" by (rule rename_preserves_deriven)
next
  (* since f is injective, the second direction follows from the first by using the inverse *)
  let ?M = "Nts P \<union> nts_syms \<alpha> \<union> nts_syms \<beta>"
  obtain "g" where "g = the_inv_into ?M f" and inv: "(\<And>x. x \<in> ?M \<Longrightarrow> (g (f x) = x))"
    using assms by (simp add: the_inv_into_f_f inj_on_Un)
  then have "s \<in> Syms P \<union> set \<alpha> \<union> set \<beta> \<Longrightarrow> rename_sym g (rename_sym f s) = s" for s::"('a,'t) sym"
    by (cases s) (auto simp: Nts_def Syms_def nts_syms_def)
  then have inv_rename_syms: "\<And>(ss::('a,'t) syms). set ss \<subseteq> Syms P \<union> set \<alpha> \<union> set \<beta> \<Longrightarrow> rename_syms g (rename_syms f ss) = ss"
    by (simp add: list.map_ident_strong subset_iff)
  with inv have "p \<in> P \<Longrightarrow> rename_prod g (rename_prod f p) = p" for p::"('a,'t) prod"
    by(cases p)(auto simp: Nts_def Syms_def)
  then have inv_rename_prods: "rename_Prods g (rename_Prods f P) = P"
    using image_iff by fastforce
  then show "?l \<Longrightarrow> ?r"
    using rename_preserves_deriven inv_rename_syms by (metis Un_upper2 le_supI1)
qed

lemma rename_derives_iff_inj:
  assumes "inj_on f (Nts P \<union> nts_syms \<alpha> \<union> nts_syms \<beta>)"
  shows "rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>* rename_syms f \<beta> \<longleftrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
by (meson assms relpowp_imp_rtranclp rename_deriven_iff_inj rtranclp_imp_relpowp)

lemma rename_deriveln_iff_inj:
fixes P :: "('a,'t)Prods"
assumes "inj_on f (Nts P \<union> nts_syms \<alpha> \<union> nts_syms \<beta>)"
shows "rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>l(n) rename_syms f \<beta> \<longleftrightarrow> P \<turnstile> \<alpha> \<Rightarrow>l(n) \<beta>" (is "?l \<longleftrightarrow> ?r")
proof
  show "?r \<Longrightarrow> ?l" by (rule rename_preserves_deriveln)
next
  let ?M = "Nts P \<union> nts_syms \<alpha> \<union> nts_syms \<beta>"
  obtain "g" where "g = the_inv_into ?M f" and inv: "(\<And>x. x \<in> ?M \<Longrightarrow> (g (f x) = x))"
    using assms by (simp add: the_inv_into_f_f inj_on_Un)
  then have "s \<in> Syms P \<union> set \<alpha> \<union> set \<beta> \<Longrightarrow> rename_sym g (rename_sym f s) = s" for s::"('a,'t) sym"
    by (cases s) (auto simp: Nts_def Syms_def nts_syms_def)
  then have inv_rename_syms: "\<And>(ss::('a,'t) syms). set ss \<subseteq> Syms P \<union> set \<alpha> \<union> set \<beta> \<Longrightarrow> rename_syms g (rename_syms f ss) = ss"
    by (simp add: list.map_ident_strong subset_iff)
  with inv have "p \<in> P \<Longrightarrow> rename_prod g (rename_prod f p) = p" for p::"('a,'t) prod"
    by(cases p)(auto simp: Nts_def Syms_def)
  then have inv_rename_prods: "rename_Prods g (rename_Prods f P) = P"
    using image_iff by fastforce
  then show "?l \<Longrightarrow> ?r"
    using rename_preserves_deriveln inv_rename_syms by (metis Un_upper2 le_supI1)
qed

lemma rename_derivels_iff_inj:
  assumes "inj_on f (Nts P \<union> nts_syms \<alpha> \<union> nts_syms \<beta>)"
  shows "rename_Prods f P \<turnstile> rename_syms f \<alpha> \<Rightarrow>l* rename_syms f \<beta> \<longleftrightarrow> P \<turnstile> \<alpha> \<Rightarrow>l* \<beta>"
by (meson assms relpowp_imp_rtranclp rename_deriveln_iff_inj rtranclp_imp_relpowp)

lemma Lang_rename_Prods:
  assumes "inj_on f (Nts P \<union> {S})"
  shows "Lang (rename_Prods f P) (f S) = Lang P S"
proof -
  from assms rename_derives_iff_inj[of f P "[Nt S]" "map Tm _"]
  show ?thesis unfolding Lang_def by (simp)
qed

lemma derives_preserves_renaming:
  assumes "rename_Prods f P \<turnstile> rename_syms f u \<Rightarrow>* fv"
  shows "\<exists>v. fv = rename_syms f v"
  using assms
proof(induction rule: derives_induct)
  case base
  then show ?case by auto
next
  case (step u A v w)
  then obtain A' where A'_src: "rename_syms f [Nt A'] = [Nt A]" by auto
  from step obtain drvW where "rename_syms f drvW = u @ [Nt A] @ v" by auto
  then have uAv_split: "u @ rename_syms f [Nt A'] @ v = rename_syms f drvW" using A'_src by simp
  from uAv_split obtain u' where u'_src: "rename_syms f u' = u" by (metis map_eq_append_conv)
  from uAv_split obtain v' where v'_src: "rename_syms f v' = v" by (metis map_eq_append_conv)
  from step obtain w' where "rename_syms f w' = w" by auto
  then have "u @ w @ v = rename_syms f (u' @ w' @ v')" using u'_src v'_src by auto
  then show ?case by fast
qed

end
