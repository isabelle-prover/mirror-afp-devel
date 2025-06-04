(* Author: Kaan Taskin *)

section \<open>Right-Linear Grammars\<close>

theory Right_Linear
imports Unit_Elimination Binarize
begin

text \<open>This theory defines (strongly) right-linear grammars and proves that every
right-linear grammar can be transformed into a strongly right-linear grammar.\<close>

text\<open>In a \emph{right linear} grammar every production has the form \<open>A \<rightarrow> wB\<close> or \<open>A \<rightarrow> w\<close>
where \<open>w\<close> is a sequence of terminals:\<close>

definition rlin :: "('n, 't) Prods \<Rightarrow> bool" where
  "rlin ps = (\<forall>(A,w) \<in> ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B]))"

definition rlin_noterm :: "('n, 't) Prods \<Rightarrow> bool" where
  "rlin_noterm ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>u B. w = map Tm u @ [Nt B]))"

definition rlin_bin :: "('n, 't) Prods \<Rightarrow> bool" where
  "rlin_bin ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>B. w = [Nt B] \<or> (\<exists>a. w = [Tm a, Nt B])))"

text\<open>In a \emph{strongly right linear} grammar every production has the form \<open>A \<rightarrow> aB\<close> or \<open>A \<rightarrow> \<epsilon>\<close>
where \<open>a\<close> is a terminal:\<close>

definition rlin2 :: "('a, 't) Prods \<Rightarrow> bool" where
  "rlin2 ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>a B. w = [Tm a, Nt B]))"

text\<open>A straightforward property:\<close>

lemma rlin_if_rlin2: 
  assumes "rlin2 ps"
  shows "rlin ps"
proof -
  have "\<exists>u. x2 = map Tm u \<or> (\<exists>B. x2 = map Tm u @ [Nt B])"
    if "\<forall>x\<in>ps. \<forall>x1 x2. x = (x1, x2) \<longrightarrow> x2 = [] \<or> (\<exists>a B. x2 = [Tm a, Nt B])"
      and "(x1, x2) \<in> ps"
    for x1 :: 'a and x2 :: "('a, 'b) sym list"
    using that by (metis append_Cons append_Nil list.simps(8,9))
  with assms show ?thesis
    unfolding rlin_def rlin2_def
    by (auto split: prod.splits)
qed

lemma rlin_cases:
  assumes rlin_ps: "rlin ps" 
      and elem: "(A,w) \<in> ps"
    shows "(\<exists>B. w = [Nt B]) \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"
proof -
  from rlin_ps have "\<forall>(A,w) \<in> ps. (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u \<le> 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"
    using rlin_def by fastforce
  with elem have "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u \<le> 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by auto
  hence "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u = 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by simp
  hence "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = [Nt B])) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by auto
  hence "(\<exists>B. w = [Nt B]) \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by blast
  thus ?thesis .
qed


subsection \<open>From \<open>rlin\<close> to \<open>rlin2\<close>\<close>

text
\<open>The \<open>finalize\<close> function is responsible of the transformation of a production list from \<open>rlin\<close> to \<open>rlin_noterm\<close>, while 
 preserving the language. We make use of fixpoint iteration and define the function \<open>finalize1\<close> that adds a 
 fresh non-terminal \<open>B\<close> at the end of every production that consists only of terminals and has at least length one. The
 function also introduces the new production \<open>(B,[])\<close> in the production list. The step function of the fixpoint iteration is
 then the auxiliary function \<open>finalize'\<close>. We also define the count function as \<open>countfin\<close> which counts the the productions that
 consists only of terminal and has at least length one\<close>

fun finalize1 :: "('n :: infinite, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "finalize1 ps' [] = []"
| "finalize1 ps' ((A,[])#ps) = (A,[]) # finalize1 ps' ps"
| "finalize1 ps' ((A,w)#ps) = 
    (if \<exists>u. w = map Tm u then let B = fresh(nts ps') in (A,w @ [Nt B])#(B,[])#ps else (A,w) # finalize1 ps' ps)"

definition finalize' :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "finalize' ps = finalize1 ps ps"

fun countfin :: "('n::infinite, 't) prods \<Rightarrow> nat" where
  "countfin [] = 0"
| "countfin ((A,[])#ps) = countfin ps"
| "countfin ((A,w) # ps) = (if \<exists>u. w = map Tm u then 1 + countfin ps else countfin ps)"

definition finalize :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "finalize ps = (finalize' ^^ (countfin ps)) ps"

text
\<open>Firstly we show that \<open>finalize\<close> indeed does the intended transformation\<close>

lemma countfin_dec1:
  assumes "finalize1 ps' ps \<noteq> ps" 
  shows "countfin ps > countfin (finalize1 ps' ps)"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v # va = map Tm u")
    case True
    let ?B = "fresh(nts ps')"
    have not_tm: "\<nexists>u. v # va @ [Nt ?B] = map Tm u"
      by (simp add: ex_map_conv)
    from True have "countfin (finalize1 ps' ((A, v # va) # ps)) = countfin ((A,v#va @ [Nt ?B])#(?B,[])#ps)"
      by (metis append_Cons finalize1.simps(3))
    also from not_tm have "... = countfin ps" by simp
    also have "... < countfin ps + 1" by simp
    also from True have "... = countfin ((A, v # va) # ps)" by simp
    finally show ?thesis .
  next
    case False
    with 3 show ?thesis by simp
  qed
qed simp_all

lemma countfin_dec':
  assumes "finalize' ps \<noteq> ps" 
  shows "countfin ps > countfin (finalize' ps)"
  using finalize'_def assms countfin_dec1 by metis

lemma finalize_ffpi:
  "finalize'((finalize' ^^ countfin x) x) = (finalize' ^^ countfin x) x"
proof -
  have "\<And>x. countfin(finalize' x) < countfin x \<or> finalize' x = x"
    using countfin_dec' by blast
  thus ?thesis using funpow_fix by metis
qed

lemma finalize_rlinnoterm1:
  assumes "rlin (set ps)"
      and "ps = finalize1 ps' ps"
    shows "rlin_noterm (set ps)"
  using assms proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  thus ?case
    by (simp add: rlin_noterm_def)
next
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_def rlin_noterm_def)
next
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis 
      by simp (meson list.inject not_Cons_self)
  next
    case False
    with 3 show ?thesis
      by (simp add: rlin_def rlin_noterm_def)
  qed
qed

lemma finalize_rlin1:
  "rlin (set ps) \<Longrightarrow> rlin (set (finalize1 ps' ps))"
proof (induction ps' ps rule: finalize1.induct)
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_def)
next
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis
      by (auto simp: Let_def rlin_def split_beta map_eq_append_conv Cons_eq_append_conv intro: exI[of _ "_ # _"])
  next
    case False
    with 3 show ?thesis
      by (simp add: rlin_def)
  qed
qed simp

lemma finalize_rlin':
  "rlin (set ps) \<Longrightarrow> rlin (set (finalize' ps))"
  unfolding finalize'_def using finalize_rlin1 by blast

lemma finalize_rlin'n:
  "rlin (set ps) \<Longrightarrow> rlin (set ((finalize'^^n) ps))"
  by (induction n) (auto simp add: finalize_rlin')

lemma finalize_rlinnoterm':
  assumes "rlin (set ps)"
      and "ps = finalize' ps"
  shows "rlin_noterm (set ps)"
  using finalize'_def assms finalize_rlinnoterm1 by metis

lemma finalize_rlinnoterm: 
  "rlin (set ps) \<Longrightarrow> rlin_noterm (set (finalize ps))"
proof -
  assume asm: "rlin (set ps)"
  hence 1: "rlin (set ((finalize' ^^ countfin ps) ps))"
    using finalize_rlin'n by auto
  have "finalize'((finalize' ^^ countfin ps) ps) = (finalize' ^^ countfin ps) ps"
    using finalize_ffpi by blast
  with 1 have "rlin_noterm (set ((finalize' ^^ countfin ps) ps))"
    using finalize_rlinnoterm' by metis
  hence "rlin_noterm (set (finalize ps))"
    by (simp add: finalize_def)
  thus ?thesis .
qed

text
\<open>Now proving the language preservation property of \<open>finalize\<close>, similarly to \<open>binarize\<close>\<close>

lemma finalize1_cases:
  "finalize1 ps' ps = ps \<or> (\<exists>A w ps'' B. set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A,w @ [Nt B]),(B,[])} \<union> set ps'' \<and> Nt B \<notin> syms ps')"
proof (induction ps' ps rule: finalize1.induct)
  case (2 ps' C ps)
  thus ?case proof (cases "finalize1 ps' ps = ps")
    case False
    then obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
    using 2 by blast
    from defs have wit: "set ((C, []) # ps) = {(A, w)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit2: "set (finalize1 ps' ((C, []) # ps)) = {(A, w @ [Nt B]), (B, [])} \<union> set ((C, []) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed simp
next
  case (3 ps' C v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    thus ?thesis using fresh_nts in_Nts_iff_in_Syms
      by (simp add: Let_def) fastforce
  next
    case false1: False
    thus ?thesis proof (cases "finalize1 ps' ps = ps")
    case False
    with false1 obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
    using 3 by blast
    from defs have wit: "set ((C, v#va) # ps) = {(A, w)} \<union> set ((C, v#va) # ps'')" by simp
    from defs false1 have wit2: "set (finalize1 ps' ((C, v#va) # ps)) = {(A, w @ [Nt B]), (B, [])} \<union> set ((C, v#va) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed simp
  qed
qed simp

lemma finalize_der':
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize' ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  unfolding finalize'_def proof (cases "finalize1 ps ps = ps")
  case False
  then obtain C w ps'' B where defs: "set ps = {(C, w)} \<union> set ps'' \<and> set (finalize1 ps ps) = {(C, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> syms ps"
    by (meson finalize1_cases)
  from defs have a_not_b: "C \<noteq> B" unfolding Syms_def by fast
  from defs assms have a1: "A \<noteq> B" unfolding Lhss_def Syms_def by auto
  from defs have a2: "Nt B \<notin> set (map Tm x)" by auto
  from defs have a3: "Nt B \<notin> set []" by simp
  from defs have "set ps = set ((C, w) # ps'')" by simp
  with defs a_not_b have a4: "B \<notin> lhss ((C, w @ [Nt B]) # ps'')"
    unfolding Lhss_def Syms_def by auto
  from defs have notB: "Nt B \<notin> syms ps''" unfolding Syms_def by blast
  then have 1: "set ps = set (substP (Nt B) [] ((C, w @ [Nt B]) # ps''))" proof -
    from defs have s1: "Nt B \<notin> syms ps" unfolding Syms_def by meson
    from defs have s2: "(C,w) \<in> set ps" by blast
    from s1 s2 have b_notin_w: "Nt B \<notin> set w" unfolding Syms_def by fastforce
    from defs have "set ps = {(C, w)} \<union> set ps''" by simp
    also have "... = set ((C, w) # ps'')" by simp
    also have "... = set ([(C, w)] @ ps'')" by simp
    also from defs have "... = set ([(C,substsNt B [] (w @ [Nt B]))] @ ps'')" using b_notin_w
      by (simp add: substs_skip)
    also have "... = set ((substP (Nt B) [] [(C, w @ [Nt B])]) @ ps'')" by (simp add: substP_def)
    also have "... = set ((substP (Nt B) [] [(C, w @ [Nt B])]) @ substP (Nt B) [] ps'')" using notB by (simp add: substP_skip2)
    also have "... = set (substP (Nt B) [] ((C, w @ [Nt B]) # ps''))" by (simp add: substP_def)
    finally show ?thesis .
  qed
  from defs have 2: "set (finalize1 ps ps) = set ((C, w @ [Nt B]) # (B, []) # ps'')" by auto
  with 1 2 a1 a2 a3 a4 show "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize1 ps ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by (simp add: derives_inlining insert_commute)
qed simp

lemma lhss_finalize1:
  "lhss ps \<subseteq> lhss (finalize1 ps' ps)"
proof (induction ps' ps rule: finalize1.induct)
  case (2 ps' A ps)
  thus ?case unfolding Lhss_def by auto
next
  case (3 ps' A v va ps)
  thus ?case unfolding Lhss_def by (auto simp: Let_def)
qed simp

lemma lhss_binarize'n:
  "lhss ps \<subseteq> lhss ((finalize'^^n) ps)"
proof (induction n)
  case (Suc n)
  thus ?case unfolding finalize'_def using lhss_finalize1 by auto
qed simp

lemma finalize_der'n: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((finalize'^^n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
using assms proof (induction n)
  case (Suc n)
  hence "A \<in> lhss ((finalize' ^^ n) ps)"
    using lhss_binarize'n by blast
  hence "set ((finalize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize' ((finalize' ^^ n) ps)) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    using finalize_der' by blast
  hence"set ((finalize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((finalize' ^^ Suc n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by simp
  with Suc show ?case by blast
qed simp

lemma finalize_der: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  unfolding finalize_def using finalize_der'n[OF assms] by simp

lemma lang_finalize_lhss:
  assumes "A \<in> lhss ps"
  shows "lang ps A = lang (finalize ps) A"
  using finalize_der[OF assms] Lang_eqI_derives by metis

lemma finalize_syms1:
  assumes  "Nt A \<in> syms ps"
    shows  "Nt A \<in> syms (finalize1 ps' ps)"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis unfolding Syms_def by (auto simp: Let_def)
  next
    case False
    with 3 show ?thesis unfolding Syms_def by auto
  qed
qed auto

lemma finalize_nts'n:
  assumes "A \<in> nts ps"
  shows   "A \<in> nts ((finalize' ^^ n) ps)"
  using assms proof (induction n)
  case (Suc n)
  thus ?case
    unfolding finalize'_def by (simp add: finalize_syms1 in_Nts_iff_in_Syms)
qed simp

lemma finalize_nts:
  assumes "A \<in> nts ps"
  shows   "A \<in> nts (finalize ps)"
  unfolding finalize_def using finalize_nts'n[OF assms] by simp

lemma finalize_lhss_nts1:
  assumes "A \<notin> lhss ps"
      and "A \<in> nts ps'"
    shows "A \<notin> lhss (finalize1 ps' ps)"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis unfolding Lhss_def by (auto simp: Let_def fresh_nts)
  next
    case False
    with 3 show ?thesis unfolding Lhss_def by (auto simp: Let_def)
  qed
qed simp_all

lemma finalize_lhss_nts'n:
  assumes "A \<notin> lhss ps"
      and "A \<in> nts ps"
    shows "A \<notin> lhss ((finalize'^^n) ps) \<and> A \<in> nts ((finalize'^^n) ps)"
  using assms proof (induction n)
  case (Suc n)
  thus ?case
    unfolding finalize'_def by (simp add: finalize_lhss_nts1 finalize_syms1 in_Nts_iff_in_Syms)
qed simp

lemma finalize_lhss_nts:
   assumes "A \<notin> lhss ps"
      and  "A \<in> nts ps"
    shows "A \<notin> lhss (finalize ps) \<and> A \<in> nts (finalize ps)"
  unfolding finalize_def using finalize_lhss_nts'n[OF assms] by simp

lemma lang_finalize: 
  assumes "A \<in> nts ps"
  shows "lang (finalize ps) A = lang ps A"
proof (cases "A \<in> lhss ps")
  case True
  thus ?thesis
    using lang_finalize_lhss by blast
next
  case False
  thus ?thesis
    using assms finalize_lhss_nts Lang_empty_if_notin_Lhss by fast
qed

text
\<open>Next step is to define the transformation from \<open>rlin_noterm\<close> to \<open>rlin_bin\<close>. For this we use the function \<open>binarize\<close>.
 The language preservation property of \<open>binarize\<close> is already proven\<close>

lemma binarize_rlinbin1: 
  assumes "rlin_noterm (set ps)"
      and "ps = binarize1 ps' ps"
  shows "rlin_bin (set ps)"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  thus ?case
    by (simp add: rlin_bin_def)
next
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_noterm_def rlin_bin_def)
next
  case (3 ps' A s0 u ps)
  from "3.prems"(2) have a1: "length u \<le> 1" by simp (meson list.inject not_Cons_self)
  with "3.prems"(2) have a2: "ps = binarize1 ps' ps" by simp
  from "3.prems"(1) have a3: "rlin_noterm (set ps)"
    by (simp add: rlin_noterm_def)
  from a1 a2 a3 have 1: "rlin_bin (set ps)"
    using "3.IH" by blast
  from "3.prems"(1) have ex: "\<exists>v B. s0 # u = map Tm v @ [Nt B]"
    by (simp add: rlin_noterm_def)
  with a1 have 2: "\<exists>B. s0 # u = [Nt B] \<or> (\<exists>a. s0 # u = [Tm a, Nt B])" proof (cases "length u = 0")
    case True
    with ex show ?thesis by simp
  next
    case False
    with a1 have "length u = 1" by linarith
    show ?thesis
    proof -
      have "\<exists>B. s0 = Nt B \<and> u = [] \<or> (\<exists>a. s0 = Tm a) \<and> u = [Nt B]"
        if "length u = Suc 0" and "s0 # u = map Tm v @ [Nt B]"
        for v :: "'b list" and B :: 'a
        using that by (metis append_Cons append_Nil append_butlast_last_id butlast_snoc diff_Suc_1 hd_map last_snoc length_0_conv length_butlast list.sel(1) list.simps(8))
      with ex \<open>length u = 1\<close> show ?thesis
        by auto
    qed
  qed
  from 1 2 show ?case
    by (simp add: rlin_bin_def)
qed

lemma binarize_noterm1:
  "rlin_noterm (set ps) \<Longrightarrow> rlin_noterm (set (binarize1 ps' ps))"
proof (induction ps' ps rule: binarize1.induct)
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_noterm_def)
next
  case (3 ps' A s0 u ps)
  thus ?case proof (cases "length u \<le> 1")
    case True
    with 3 show ?thesis
      by (simp add: rlin_noterm_def)
  next
    case False
    let ?B = "fresh(nts ps')"
    from "3.prems" have a1: "rlin_noterm (set ps)"
      by (simp add: rlin_noterm_def)
    from "3.prems" have ex: "\<exists>v B. s0 # u = map Tm v @ [Nt B]"
      by (simp add: rlin_noterm_def)
    with False have a2: "\<exists>v B. [s0, Nt ?B] = map Tm v @ [Nt B]"
      by (auto simp: Cons_eq_append_conv neq_Nil_conv intro: exI[of _ "[_]"])
    from ex False have a3: "\<exists>v B. u = map Tm v @ [Nt B]"
      by (auto simp: Cons_eq_append_conv)
    from False a1 a2 a3 show ?thesis
      by (auto simp: Let_def rlin_noterm_def)
  qed
qed simp

lemma binarize_noterm':
  "rlin_noterm (set ps) \<Longrightarrow> rlin_noterm (set (binarize' ps))"
  unfolding binarize'_def using binarize_noterm1 by blast

lemma binarize_noterm'n:
  "rlin_noterm (set ps) \<Longrightarrow> rlin_noterm (set ((binarize'^^n) ps))"
  by (induction n) (auto simp add: binarize_noterm')

lemma binarize_rlinbin':
  assumes "rlin_noterm (set ps)"
      and "ps = binarize' ps"
  shows "rlin_bin (set ps)"
  using binarize'_def assms binarize_rlinbin1 by metis

lemma binarize_rlinbin: 
  "rlin_noterm (set ps) \<Longrightarrow> rlin_bin (set (binarize ps))"
proof -
  assume asm: "rlin_noterm (set ps)"
  hence 1: "rlin_noterm (set ((binarize' ^^ count ps) ps))"
    using binarize_noterm'n by auto
  have "binarize'((binarize' ^^ count ps) ps) = (binarize' ^^ count ps) ps"
    using binarize_ffpi by blast
  with 1 have "rlin_bin (set ((binarize' ^^ count ps) ps))"
    using binarize_rlinbin' by fastforce
  hence "rlin_bin (set (binarize ps))"
    by (simp add: binarize_def)
  thus ?thesis .
qed

text
\<open>The last transformation takes a production set from \<open>rlin_bin\<close> and converts it to \<open>rlin2\<close>. That is, we need to remove unit
 productions of the from \<open>(A, [Nt B])\<close>. In \<open>uProds.thy\<close> is the predicate \<open>\<U> ps' ps\<close> defined that is satisfied if \<open>ps\<close> is the
 same production set as \<open>ps'\<close> without the unit productions. The language preservation property is already given\<close>

lemma uppr_rlin2:
  assumes rlinbin: "rlin_bin (set ps')"
    and uppr_ps': "unit_elim_rel ps' ps"
  shows "rlin2 (set ps)"
proof - 
  from rlinbin have "rlin2 (set ps' - {(A,w) \<in> set ps'. \<exists>B. w = [Nt B]})"
    using rlin2_def rlin_bin_def by fastforce
  hence "rlin2 (set ps' - (unit_prods ps'))"
    by (simp add: unit_prods_def)
  hence 1: "rlin2 (unit_rm ps')"
    by (simp add: unit_rm_def)
  hence 2: "rlin2 (new_prods ps')"
    unfolding new_prods_def rlin2_def by fastforce
  from 1 2 have "rlin2 (unit_rm ps' \<union> new_prods ps')"
    unfolding rlin2_def by auto
  with uppr_ps' have "rlin2 (set ps)"
    by (simp add: unit_elim_rel_def)
  thus ?thesis .
qed

text
\<open>The transformation \<open>rlin2_of_rlin\<close> applies the presented functions in the right order. At the end, we show that \<open>rlin2_of_rlin\<close>
 converts a production set from \<open>rlin\<close> to a production set from \<open>rlin2\<close>, without changing the language\<close>

definition rlin2_of_rlin :: "('n::infinite,'t) prods \<Rightarrow> ('n,'t)prods" where
  "rlin2_of_rlin ps = unit_elim (binarize (finalize ps))"

theorem rlin_to_rlin2: 
  assumes "rlin (set ps)" 
  shows "rlin2 (set (rlin2_of_rlin ps))"
using assms proof -
  assume "rlin (set ps)"
  hence "rlin_noterm (set (finalize ps))"
    using finalize_rlinnoterm by blast
  hence "rlin_bin (set (binarize (finalize ps)))"
    by (simp add: binarize_rlinbin)
  hence "rlin2 (set (unit_elim (binarize (finalize ps))))"
    by (simp add: unit_elim_rel_unit_elim uppr_rlin2)
  thus "rlin2 (set (rlin2_of_rlin ps))"
    by (simp add: rlin2_of_rlin_def)
qed

lemma lang_rlin2_of_rlin:
  "A \<in> Nts (set ps) \<Longrightarrow> lang (rlin2_of_rlin ps) A = lang ps A"
by(simp add: rlin2_of_rlin_def lang_unit_elim finalize_nts lang_binarize lang_finalize)


subsection \<open>Properties of \<open>rlin2\<close> derivations\<close>

text
\<open>In the following we present some properties for list of symbols that are derived from a production set satisfying \<open>rlin2\<close>\<close>

lemma map_Tm_single_nt:
  assumes "map Tm w @ [Tm a, Nt A] = u1 @ [Nt B] @ u2"
  shows "u1 = map Tm (w @ [a]) \<and> u2 = []"
proof -
  from assms have *: "map Tm (w @ [a]) @ [Nt A] = u1 @ [Nt B] @ u2" by simp
  have 1: "Nt B \<notin> set (map Tm (w @ [a]))" by auto
  have 2: "Nt B \<in> set (u1 @ [Nt B] @ u2)" by simp
  from * 1 2 have "Nt B \<in> set ([Nt A])"
    by (metis list.set_intros(1) rotate1.simps(2) set_ConsD set_rotate1 sym.inject(1))
  hence "[Nt B] = [Nt A]" by simp
  with 1 * show ?thesis
    by (metis append_Cons append_Cons_eq_iff append_self_conv emptyE empty_set)
qed

text
\<open>A non-terminal can only occur as the rightmost symbol\<close>

lemma rlin2_derive:
  assumes "P \<turnstile> v1 \<Rightarrow>* v2" 
      and "v1 = [Nt A]"
      and "v2 = u1 @ [Nt B] @ u2" 
      and "rlin2 P"
    shows "\<exists>w. u1 = map Tm w \<and> u2 = []"
using assms proof (induction arbitrary: u1 B u2 rule: derives_induct)
  case base
  then show ?case
    by (simp add: append_eq_Cons_conv)
next
  case (step u C v w)
  from step.prems(1) step.prems(3) have "\<exists>w. u = map Tm w \<and> v = []" 
    using step.IH[of u C v] by simp
  then obtain wh where u_def: "u = map Tm wh" by blast
  have v_eps: "v = []"
    using \<open>\<exists>w. u = map Tm w \<and> v = []\<close> by simp
  from step.hyps(2) step.prems(3) have w_cases: "w = [] \<or> (\<exists>d D. w = [Tm d, Nt D])"
    unfolding rlin2_def by auto
  then show ?case proof cases
    assume "w=[]"
    with v_eps step.prems(2) have "u = u1 @ [Nt B] @ u2" by simp
    with u_def show ?thesis by (auto simp: append_eq_map_conv)
  next
    assume "\<not>w=[]"
    then obtain d D where "w = [Tm d, Nt D]" 
      using w_cases by blast
    with u_def v_eps step.prems(2) have "u1 = map Tm (wh @ [d]) \<and> u2 = []"
      using map_Tm_single_nt[of wh d D u1 B u2] by simp
    thus ?thesis by blast
  qed
qed

text
\<open>A new terminal is introduced by a production of the form \<open>(C, [Tm x, Nt B])\<close>\<close>

lemma rlin2_introduce_tm:
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Tm x, Nt B]"
    shows "\<exists>C. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C] \<and> (C,[Tm x, Nt B]) \<in> P"
proof -
  from assms(2) have "\<exists>v. P \<turnstile> [Nt A] \<Rightarrow>* v \<and> P \<turnstile> v \<Rightarrow> map Tm w @ [Tm x, Nt B]"
    using rtranclp.cases by fastforce
  then obtain v where v_star: "P \<turnstile> [Nt A] \<Rightarrow>* v" and v_step: "P \<turnstile> v \<Rightarrow> map Tm w @ [Tm x, Nt B]" by blast
  from v_step have "\<exists>u1 u2 C \<alpha>. v = u1 @ [Nt C] @ u2 \<and> map Tm w @ [Tm x, Nt B] = u1 @ \<alpha> @ u2 \<and> (C,\<alpha>) \<in> P"
    using derive.cases by fastforce
  then obtain u1 u2 C \<alpha> where v_def: "v = u1 @ [Nt C] @ u2" and w_def: "map Tm w @ [Tm x, Nt B] = u1 @ \<alpha> @ u2" 
                          and C_prod: "(C,\<alpha>) \<in> P" by blast
  from assms(1) v_star v_def have u2_eps: "u2 = []"
    using rlin2_derive[of P "[Nt A]"] by simp
  from assms(1) v_star v_def obtain wa where u1_def: "u1 = map Tm wa"
    using rlin2_derive[of P "[Nt A]" "u1 @ [Nt C] @ u2" A u1] by auto
  from w_def u2_eps u1_def have "map Tm w @ [Tm x, Nt B] = map Tm wa @ \<alpha>" by simp
  then have "map Tm (w @ [x]) @ [Nt B] = map Tm wa @ \<alpha>" by simp
  then have "\<alpha> \<noteq> []" 
    by (metis append.assoc append.right_neutral list.distinct(1) map_Tm_single_nt)
  with assms(1) C_prod obtain d D where "\<alpha> = [Tm d, Nt D]"
    using rlin2_def by fastforce
  from w_def u2_eps have x_d: "x = d" 
    using \<open>\<alpha> = [Tm d, Nt D]\<close> by simp
  from w_def u2_eps have B_D: "B = D"
    using \<open>\<alpha> = [Tm d, Nt D]\<close> by simp
  from x_d B_D have alpha_def: "\<alpha> = [Tm x, Nt B]"
    using \<open>\<alpha> = [Tm d, Nt D]\<close> by simp
  from w_def u2_eps alpha_def have "map Tm w = u1" by simp
  with u1_def have w_eq_wa: "w = wa"
    by (metis list.inj_map_strong sym.inject(2))
  from v_def u1_def w_eq_wa u2_eps have "v = map Tm w @ [Nt C]" by simp
  with v_star have 1: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C]" by simp
  from C_prod alpha_def have 2: "(C,[Tm x, Nt B]) \<in> P" by simp
  from 1 2 show ?thesis by auto
qed

lemma rlin2_nts_derive_eq: 
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
    shows "A = B"
proof -
  from assms(2) have star_cases: "[Nt A] = [Nt B] \<or> (\<exists>w. P \<turnstile> [Nt A] \<Rightarrow> w \<and> P \<turnstile> w \<Rightarrow>* [Nt B])"
    using converse_rtranclpE by force
  show ?thesis proof cases
    assume "\<not>[Nt A] = [Nt B]"
    then obtain w where w_step: "P \<turnstile> [Nt A] \<Rightarrow> w" and w_star: "P \<turnstile> w \<Rightarrow>* [Nt B]"
      using star_cases by auto
    from assms(1) w_step have w_cases: "w = [] \<or> (\<exists>a C. w = [Tm a, Nt C])"
      unfolding rlin2_def using derive_singleton[of P "Nt A" w] by auto
    show ?thesis proof cases
      assume "w = []"
      with w_star show ?thesis by simp
    next
      assume "\<not>w = []"
      with w_cases obtain a C where "w = [Tm a, Nt C]" by blast
      with w_star show ?thesis
        using derives_Tm_Cons[of P a "[Nt C]" "[Nt B]"] by simp
    qed
  qed simp
qed

text
\<open>If the list of symbols consists only of terminals, the last production used is of the form \<open>B,[]\<close>\<close>

lemma rlin2_tms_eps:
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
    shows "\<exists>B. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B] \<and> (B,[]) \<in> P"
proof -
  from assms(2) have "\<exists>v. P \<turnstile> [Nt A] \<Rightarrow>* v \<and> P \<turnstile> v \<Rightarrow> map Tm w"
    using rtranclp.cases by force
  then obtain v where v_star: "P \<turnstile> [Nt A] \<Rightarrow>* v" and v_step: "P \<turnstile> v \<Rightarrow> map Tm w" by blast
  from v_step have "\<exists>u1 u2 C \<alpha>. v = u1 @ [Nt C] @ u2 \<and> map Tm w = u1 @ \<alpha> @ u2 \<and> (C,\<alpha>) \<in> P"
    using derive.cases by fastforce
  then obtain u1 u2 C \<alpha> where v_def: "v = u1 @ [Nt C] @ u2" and w_def: "map Tm w = u1 @ \<alpha> @ u2" and C_prod: "(C,\<alpha>) \<in> P" by blast
  have "\<nexists>A. Nt A \<in> set (map Tm w)" by auto
  with w_def have "\<nexists>A. Nt A \<in> set \<alpha>" 
    by (metis Un_iff set_append)
  then have "\<nexists>a A. \<alpha> = [Tm a, Nt A]" by auto
  with assms(1) C_prod have alpha_eps: "\<alpha> = []"
    using rlin2_def by force
  from v_star assms(1) v_def have u2_eps: "u2 = []"
    using rlin2_derive[of P "[Nt A]"] by simp
  from w_def alpha_eps u2_eps have u1_def: "u1 = map Tm w" by simp
  from v_star v_def u1_def u2_eps have 1: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C]" by simp
  from alpha_eps C_prod have 2: "(C,[]) \<in> P"  by simp
  from 1 2 show ?thesis by auto
qed

end