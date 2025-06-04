(*
Authors: Tobias Nipkow, Fabian Lehr
*)

section "Context-Free Languages"

theory Context_Free_Language
imports
  "Regular-Sets.Regular_Set"
  Renaming_CFG
  Disjoint_Union_CFG
begin

subsection \<open>Auxiliary: \<open>lfp\<close> as Kleene Fixpoint\<close>
(* TODO rm after next release *)

definition omega_chain :: "(nat \<Rightarrow> ('a::complete_lattice)) \<Rightarrow> bool" where
"omega_chain C = (\<forall>i. C i \<le> C(Suc i))"

definition omega_cont :: "(('a::complete_lattice) \<Rightarrow> ('b::complete_lattice)) \<Rightarrow> bool" where
"omega_cont f = (\<forall>C. omega_chain C \<longrightarrow> f(SUP n. C n) = (SUP n. f(C n)))"

lemma omega_chain_mono: "omega_chain C \<Longrightarrow> i \<le> j \<Longrightarrow> C i \<le> C j"
unfolding omega_chain_def using lift_Suc_mono_le[of C]  
by(induction "j-i" arbitrary: i j)auto

lemma mono_if_omega_cont: fixes f :: "('a::complete_lattice) \<Rightarrow> ('b::complete_lattice)"
  assumes "omega_cont f" shows "mono f"
proof
  fix a b :: "'a" assume "a \<le> b"
  let ?C = "\<lambda>n::nat. if n=0 then a else b"
  have *: "omega_chain ?C" using \<open>a \<le> b\<close> by(auto simp: omega_chain_def)
  have "f a \<le> sup (f a) (SUP n. f(?C n))" by(rule sup.cobounded1)
  also have "\<dots> = sup (f(?C 0)) (SUP n. f(?C n))" by (simp)
  also have "\<dots> = (SUP n. f (?C n))" using SUP_absorb[OF UNIV_I] .
  also have "\<dots> = f (SUP n. ?C n)"
    using assms * by (simp add: omega_cont_def del: if_image_distrib)
  also have "f (SUP n. ?C n) = f b"
    using \<open>a \<le> b\<close> by (auto simp add: gt_ex sup.absorb2 split: if_splits)
  finally show "f a \<le> f b" .
qed

lemma omega_chain_iterates: fixes f :: "('a::complete_lattice) \<Rightarrow> 'a"
  assumes "mono f" shows "omega_chain(\<lambda>n. (f^^n) bot)"
proof-
  have "(f ^^ n) bot \<le> (f ^^ Suc n) bot" for n
  proof (induction n)
    case 0 show ?case by simp
  next
    case (Suc n) thus ?case using assms by (auto simp: mono_def)
  qed
  thus ?thesis by(auto simp: omega_chain_def assms)
qed

theorem Kleene_lfp:
  assumes "omega_cont f" shows "lfp f = (SUP n. (f^^n) bot)" (is "_ = ?U")
proof(rule Orderings.antisym)
  from assms mono_if_omega_cont
  have mono: "(f ^^ n) bot \<le> (f ^^ Suc n) bot" for n
    using funpow_decreasing [of n "Suc n"] by auto
  show "lfp f \<le> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (SUP n. (f^^Suc n) bot)"
      using omega_chain_iterates[OF mono_if_omega_cont[OF assms]] assms
      by(simp add: omega_cont_def)
    also have "\<dots> = ?U" using mono by(blast intro: SUP_eq)
    finally show "f ?U \<le> ?U" by simp
  qed
next
  have "(f^^n) bot \<le> p" if "f p \<le> p" for n p
  proof -
    show ?thesis
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_omega_cont[OF assms] Suc] \<open>f p \<le> p\<close>
      show ?case by simp
    qed
  qed
  thus "?U \<le> lfp f"
    using lfp_unfold[OF mono_if_omega_cont[OF assms]]
    by (simp add: SUP_le_iff)
qed


subsection \<open>Basic Definitions\<close>

text \<open>This definition depends on the type of nonterminals of the grammar.\<close>

definition CFL :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"CFL (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> finite P)"

text \<open>Ideally one would existentially quantify over \<open>'n\<close> on the right-hand side, but we cannot
quantify over types in HOL. But we can prove that the type is irrelevant because we can always
use another type via renaming.\<close>

(* TODO: rm with next release *)
lemma arb_inj_on_finite_infinite: "finite(A :: 'a set) \<Longrightarrow> \<exists>f :: 'a \<Rightarrow> 'b::infinite. inj_on f A"
by (meson arb_finite_subset card_le_inj infinite_imp_nonempty)

lemma CFL_change_Nt_type: assumes "CFL TYPE('t1::infinite) L" shows "CFL TYPE('t2::infinite) L"
proof -
  from assms obtain P and S :: 't1 where "L = Lang P S" and "finite P"
    unfolding CFL_def by blast
  have fin: "finite(Nts P \<union> {S})" using \<open>finite P\<close>
    by(simp add: finite_Nts)
  obtain f :: "'t1 \<Rightarrow> 't2" where "inj_on f (Nts P \<union> {S})"
    using arb_inj_on_finite_infinite[OF fin] by blast
  from Lang_rename_Prods[OF this] \<open>L = _\<close> have "Lang (rename_Prods f P) (f S) = L"
    by blast
  moreover have "finite(rename_Prods f P)" using \<open>finite P\<close>
    by blast
  ultimately show ?thesis unfolding CFL_def by blast
qed

text \<open>For hiding the infinite type of nonterminals:\<close>

abbreviation cfl :: "'a lang \<Rightarrow> bool" where
"cfl L \<equiv> CFL (TYPE(nat)) L"


subsection \<open>Closure Properties\<close>

lemma CFL_Un_closed:
  assumes "CFL TYPE('n1) L1" "CFL TYPE('n2) L2"
  shows "CFL TYPE(('n1+'n2)option) (L1 \<union> L2)"
proof -
  from assms obtain P1 P2 and S1 :: 'n1 and S2 :: 'n2
    where L: "L1 = Lang P1 S1" "L2 = Lang P2 S2" and fin: "finite P1" "finite P2"
    unfolding CFL_def by blast
  let ?f1 = "Some o (Inl:: 'n1 \<Rightarrow> 'n1 + 'n2)"
  let ?f2 = "Some o (Inr:: 'n2 \<Rightarrow> 'n1 + 'n2)"
  let ?P1 = "rename_Prods ?f1 P1"
  let ?P2 = "rename_Prods ?f2 P2"
  let ?S1 = "?f1 S1"
  let ?S2 = "?f2 S2"
  let ?P = "{(None, [Nt ?S1]), (None, [Nt ?S2])} \<union> (?P1 \<union> ?P2)"
  have "Lang ?P None = Lang ?P1 ?S1 \<union> Lang ?P2 ?S2"
    by (rule Lang_disj_Un2)(auto simp: Nts_Un in_Nts_rename_Prods)
  moreover have "\<dots> = Lang P1 S1 \<union> Lang P2 S2"
  proof -
    have "Lang ?P1 ?S1 = L1" unfolding \<open>L1 = _\<close>
      by (meson Lang_rename_Prods comp_inj_on inj_Inl inj_Some)
    moreover have "Lang ?P2 ?S2 = L2" unfolding \<open>L2 = _\<close>
      by (meson Lang_rename_Prods comp_inj_on inj_Inr inj_Some)
    ultimately show ?thesis using L by argo
  qed
  moreover have "finite ?P" using fin by auto
  ultimately show ?thesis
    unfolding CFL_def using L by blast 
qed

lemma CFL_concat_closed: 
assumes "CFL TYPE('n1) L1" and "CFL TYPE('n2) L2"
shows "CFL TYPE(('n1 + 'n2) option) (L1 @@ L2)"
proof -
  obtain P1 S1 where L1_def: "L1 = Lang P1 (S1::'n1)" "finite P1"
    using assms(1) CFL_def[of L1] by auto 
  obtain P2 S2 where L2_def: "L2 = Lang P2 (S2::'n2)" "finite P2"
    using assms(2) CFL_def[of L2] by auto
  let ?f1 = "Some o (Inl:: 'n1 \<Rightarrow> 'n1 + 'n2)"
  let ?f2 = "Some o (Inr:: 'n2 \<Rightarrow> 'n1 + 'n2)"
  let ?P1 = "rename_Prods ?f1 P1"
  let ?P2 = "rename_Prods ?f2 P2"
  let ?S1 = "?f1 S1"
  let ?S2 = "?f2 S2"
  let ?S = "None :: ('n1+'n2)option"
  let ?P = "{(None, [Nt ?S1, Nt ?S2])} \<union> (?P1 \<union> ?P2)"
  have "inj ?f1" by (simp add: inj_on_def) 
  then have L1r_def: "L1 = Lang ?P1 ?S1" 
    using L1_def Lang_rename_Prods[of ?f1 P1 S1] inj_on_def by force
  have "inj ?f2" by (simp add: inj_on_def) 
  then have L2r_def: "L2 = Lang ?P2 ?S2" 
    using L2_def Lang_rename_Prods[of ?f2 P2 S2] inj_on_def by force
  have "Lang ?P ?S = L1 @@ L2" unfolding L1r_def L2r_def  
    by(rule Lang_concat_disj) (auto simp add: disjoint_iff in_Nts_rename_Prods)
  moreover have "finite ?P" using \<open>finite P1\<close> \<open>finite P2\<close> by auto
  ultimately show ?thesis unfolding CFL_def by blast
qed


subsection \<open>CFG as an Equation System\<close>

text \<open>A CFG can be viewed as a system of equations. The least solution is denoted by \<open>Lang_lfp\<close>.\<close>

definition inst_sym :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) sym \<Rightarrow> 't lang" where
"inst_sym L s = (case s of Tm a \<Rightarrow> {[a]} | Nt A \<Rightarrow> L A)"

definition concats :: "'a lang list \<Rightarrow> 'a lang" where
"concats Ls = foldr (@@) Ls {[]}"

definition inst_syms :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) syms \<Rightarrow> 't lang" where
"inst_syms L w = concats (map (inst_sym L) w)"

definition subst_lang :: "('n,'t)Prods \<Rightarrow> ('n \<Rightarrow> 't lang) \<Rightarrow> ('n \<Rightarrow> 't lang)" where
"subst_lang P L = (\<lambda>A. \<Union>w \<in> Rhss P A. inst_syms L w)"

definition Lang_lfp :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't lang" where
"Lang_lfp P = lfp (subst_lang P)"

text \<open>Now we show that this \<open>lfp\<close> is a Kleene fixpoint.\<close>

lemma inst_sym_Sup_range:  "inst_sym (Sup(range F)) = (\<lambda>s. UN i. inst_sym (F i) s)"
  by(auto simp: inst_sym_def fun_eq_iff split: sym.splits)

lemma foldr_map_mono: "F \<le> G \<Longrightarrow> foldr (@@) (map F xs) Ls \<subseteq> foldr (@@) (map G xs) Ls"
by(induction xs)(auto simp add: le_fun_def subset_eq)

lemma inst_sym_mono: "F \<le> G \<Longrightarrow> inst_sym F s \<subseteq> inst_sym G s"
by (auto simp add: inst_sym_def le_fun_def subset_iff split: sym.splits)

lemma foldr_conc_map_inst_sym:
  assumes "omega_chain L"
  shows "foldr (@@) (map (\<lambda>s. \<Union>i. inst_sym (L i) s) xs) Ls = (\<Union>i. foldr (@@) (map (inst_sym (L i)) xs) Ls)"
proof(induction xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  show ?case (is "?l = ?r")
  proof
    show "?l \<subseteq> ?r"
    proof
      fix w assume "w \<in> ?l"
      with Cons obtain u v i j
        where "w = u @ v" "u \<in> inst_sym (L i) a" "v \<in> foldr (@@) (map (inst_sym (L j)) xs) Ls" by(auto)
      then show "w \<in> ?r"
        using omega_chain_mono[OF assms, of i "max i j"] omega_chain_mono[OF assms, of j "max i j"]
          inst_sym_mono foldr_map_mono[of "inst_sym (L j)" "inst_sym (L (max i j))" xs Ls] concI
        unfolding le_fun_def by(simp) blast
    qed
  next
    show "?r \<subseteq> ?l" using Cons by(fastforce)
  qed
qed

lemma omega_cont_Lang_lfp: "omega_cont (subst_lang P)"
unfolding omega_cont_def subst_lang_def
proof (safe)
  fix L :: "nat \<Rightarrow> 'a \<Rightarrow> 'b lang"
  assume o: "omega_chain L"
  show "(\<lambda>A. \<Union> (inst_syms (Sup (range L)) ` Rhss P A)) = (SUP i. (\<lambda>A. \<Union> (inst_syms (L i) ` Rhss P A)))"
    (is "(\<lambda>A. ?l A) = (\<lambda>A. ?r A)")
  proof
    fix A :: 'a
    have "?l A = \<Union>(\<Union>i. (inst_syms (L i) ` Rhss P A))"
      by(auto simp: inst_syms_def inst_sym_Sup_range concats_def foldr_conc_map_inst_sym[OF o])
    also have "\<dots> = ?r A"
      by(auto)
    finally show "?l A = ?r A" .
  qed
qed

theorem Lang_lfp_SUP: "Lang_lfp P = (SUP n. ((subst_lang P)^^n) (\<lambda>A. {}))"
using Kleene_lfp[OF omega_cont_Lang_lfp] unfolding Lang_lfp_def bot_fun_def by blast


subsection \<open>\<open>Lang_lfp = Lang\<close>\<close>

text \<open>We prove that the fixpoint characterization of the language defined by a CFG is equivalent
to the standard language definition via derivations. Both directions are proved separately\<close>

lemma inst_syms_mono: "(\<And>A. R A \<subseteq> R' A) \<Longrightarrow> w \<in> inst_syms R \<alpha> \<Longrightarrow> w \<in> inst_syms R' \<alpha>"
unfolding inst_syms_def concats_def
by (metis (no_types, lifting) foldr_map_mono in_mono inst_sym_mono le_fun_def)

lemma omega_cont_Lang_lfp_iterates: "omega_chain (\<lambda>n. ((subst_lang P)^^n) (\<lambda>A. {}))"
  using omega_chain_iterates[OF mono_if_omega_cont, OF omega_cont_Lang_lfp]
  unfolding bot_fun_def by blast

lemma in_subst_langD_inst_syms: "w \<in> subst_lang P L A \<Longrightarrow> \<exists>\<alpha>. (A,\<alpha>)\<in>P \<and> w \<in> inst_syms L \<alpha>"
unfolding subst_lang_def inst_syms_def Rhss_def by (auto split: prod.splits)

lemma foldr_conc_conc: "foldr (@@) xs {[]} @@ A = foldr (@@) xs A"
by (induction xs)(auto simp: conc_assoc)

lemma derives_if_inst_syms:
  "w \<in> inst_syms (\<lambda>A. {w. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w}) \<alpha> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
proof (induction \<alpha> arbitrary: w)
  case Nil
  then show ?case unfolding inst_syms_def concats_def by(auto)
next
  case (Cons s \<alpha>)
  show ?case
  proof (cases s)
    case (Nt A)
    then show ?thesis using Cons
      unfolding inst_syms_def concats_def inst_sym_def by(fastforce simp: derives_Cons_decomp)
  next
    case (Tm a)
    then show ?thesis using Cons
      unfolding inst_syms_def concats_def inst_sym_def by(auto simp:derives_Tm_Cons)
  qed
qed

lemma derives_if_in_subst_lang: "w \<in> ((subst_lang P)^^n) (\<lambda>A. {}) A \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
proof(induction n arbitrary: w A)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?L = "((subst_lang P)^^n) (\<lambda>A. {})"
  have *: "?L A \<subseteq> {w. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w}" for A
    using Suc.IH by blast
  obtain \<alpha> where \<alpha>: "(A,\<alpha>) \<in> P" "w \<in> inst_syms ?L \<alpha>"
    using in_subst_langD_inst_syms[OF Suc.prems[simplified]] by blast
  show ?case using \<alpha>(1) derives_if_inst_syms[OF inst_syms_mono[OF *, of _ "\<lambda>A. A", OF \<alpha>(2)]]
    by (simp add: derives_Cons_rule)
qed

lemma derives_if_Lang_lfp: "w \<in> Lang_lfp P A \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
  unfolding Lang_lfp_SUP using derives_if_in_subst_lang
  by (metis (mono_tags, lifting) SUP_apply UN_E)

lemma Lang_lfp_subset_Lang: "Lang_lfp P A \<subseteq> Lang P A"
unfolding Lang_def by(blast intro:derives_if_Lang_lfp)

text \<open>The other direction:\<close>

lemma inst_syms_decomp:
  "\<lbrakk> \<forall>i < length ws. ws ! i \<in> inst_sym L (\<alpha> ! i); length \<alpha> = length ws \<rbrakk>
  \<Longrightarrow> concat ws \<in> inst_syms L \<alpha>"
proof (induction ws arbitrary: \<alpha>)
  case Nil
  then show ?case unfolding inst_syms_def concats_def by simp
next
  case (Cons w ws)
  then obtain \<alpha>1 \<alpha>r where *: "\<alpha> = \<alpha>1 # \<alpha>r" by (metis Suc_length_conv)
  with Cons.prems(2) have "length \<alpha>r = length ws" by simp
  moreover from Cons.prems * have "\<forall>i<length ws. ws ! i \<in> inst_sym L (\<alpha>r ! i)" by auto
  ultimately have "concat ws \<in> inst_syms L \<alpha>r" using Cons.IH by blast
  moreover from Cons.prems * have "w \<in> inst_sym L \<alpha>1" by fastforce
  ultimately show ?case unfolding inst_syms_def concats_def using * by force
qed

lemma Lang_lfp_if_derives_aux: "P \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w \<Longrightarrow> w \<in> ((subst_lang P)^^n) (\<lambda>A. {}) A"
proof(induction n arbitrary: w A rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0 then show ?thesis using less.prems by auto
  next
    case (Suc m)
    then obtain \<alpha> where \<alpha>_intro: "(A,\<alpha>) \<in> P" "P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w"
      by (metis deriven_start1 less.prems nat.inject)
    then obtain ws ms where *:
      "w = concat ws \<and> length \<alpha> = length ws \<and> length \<alpha> = length ms
        \<and> sum_list ms = m \<and> (\<forall>i < length ws. P \<turnstile> [\<alpha> ! i] \<Rightarrow>(ms ! i) map Tm (ws ! i))"
      using derive_decomp_Tm by metis

    have "\<forall>i < length ws. ws ! i \<in> inst_sym (\<lambda>A. ((subst_lang P)^^m) (\<lambda>A. {}) A) (\<alpha> ! i)"
    proof (rule allI | rule impI)+
      fix i
      show "i < length ws \<Longrightarrow> ws ! i \<in> inst_sym ((subst_lang P ^^ m) (\<lambda>A. {})) (\<alpha> ! i)"
      unfolding inst_sym_def
      proof (induction "\<alpha> ! i")
        case (Nt B)
        with * have **: "ms ! i \<le> m"
          by (metis elem_le_sum_list)
        with Suc have "ms ! i < n" by force
        from less.IH[OF this, of B "ws ! i"] Nt *
          have "ws ! i \<in> (subst_lang P ^^ (ms ! i)) (\<lambda>A. {}) B" by fastforce
        with omega_chain_mono[OF omega_cont_Lang_lfp_iterates, OF **]
          have "ws ! i \<in> (subst_lang P ^^ m) (\<lambda>A. {}) B" by (metis le_funD subset_iff)
        with Nt show ?case by (metis sym.simps(5))
      next
        case (Tm a)
        with * have "P \<turnstile> map Tm [a] \<Rightarrow>(ms ! i) map Tm (ws ! i)" by fastforce
        then have "ws ! i \<in> {[a]}" using deriven_from_TmsD by fastforce
        with Tm show ?case by (metis sym.simps(6))
      qed
    qed

    from inst_syms_decomp[OF this] * have "w \<in> inst_syms ((subst_lang P ^^ m) (\<lambda>A. {})) \<alpha>" by argo
    with \<alpha>_intro have "w \<in> (subst_lang P) (\<lambda>A. (subst_lang P ^^ m) (\<lambda>A. {}) A) A"
      unfolding subst_lang_def Rhss_def by force
    with Suc show ?thesis by force
  qed
qed


lemma Lang_lfp_if_derives: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w \<Longrightarrow> w \<in> Lang_lfp P A"
proof -
  assume "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
  then obtain n where "P \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w" by (meson rtranclp_power)
  from Lang_lfp_if_derives_aux[OF this] have "w \<in> ((subst_lang P)^^n) (\<lambda>A. {}) A" by argo
  with Lang_lfp_SUP show "w \<in> Lang_lfp P A" by (metis (mono_tags, lifting) SUP_apply UNIV_I UN_iff)
qed

theorem Lang_lfp_eq_Lang: "Lang_lfp P A = Lang P A"
unfolding Lang_def by(blast intro: Lang_lfp_if_derives derives_if_Lang_lfp)

end
