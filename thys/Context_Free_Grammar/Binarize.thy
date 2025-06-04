(* Authors: Kaan Taskin *)

section \<open>Transforming Long Productions Into a Binary Cascade\<close>

theory Binarize
imports Inlining1Prod
begin

(* FFPI *) 
lemma funpow_fix: fixes f :: "'a \<Rightarrow> 'a" and m :: "'a \<Rightarrow> nat"
assumes "\<And>x. m(f x) < m x \<or> f x = x"
shows "f((f ^^ m x) x) = (f ^^ m x) x"
proof -
 have "n + m ((f^^n) x) \<le> m x \<or> f((f^^n) x) = (f^^n) x" for n
 proof(induction n)
   case 0
   then show ?case by simp
 next
   case (Suc n)
   then show ?case
   proof
     assume a1: "n + m ((f ^^ n) x) \<le> m x"
     then show ?thesis
     proof (cases "m ((f ^^ Suc n) x) < m ((f ^^ n) x)")
       case True
       then show ?thesis using a1 by auto
     next
       case False
       with assms have "(f ^^ Suc n) x = (f ^^ n) x" by auto
       then show ?thesis by simp
     qed
   next
     assume "f ((f ^^ n) x) = (f ^^ n) x"
     then show ?thesis by simp
   qed
 qed
  from this[of "m x"] show ?thesis using assms[of "(f ^^ m x) x"] by auto
qed

text
\<open>In a binary grammar, every right-hand side consists of at most two symbols. The \<open>binarize\<close> function should convert an
 arbitrary production list into a binary production list, without changing the language of the grammar. For this we make use
 of fixpoint iteration and define the function \<open>binarize1\<close> for splitting a production, whose right-hand side exceeds the
 maximum number of symbols 2, into two productions. The step function is then defined as the auxiliary function \<open>binarize'\<close>.
 We also define the count function \<open>count\<close> that counts the right-hand sides whose length is more than or equal to 2\<close>

fun binarize1 :: "('n :: infinite, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize1 ps' [] = []"
| "binarize1 ps' ((A, []) # ps) = (A, []) # binarize1 ps' ps"
| "binarize1 ps' ((A, s0 # u) # ps) =
 (if length u \<le> 1 then (A, s0 # u) # binarize1 ps' ps
  else let B = fresh (nts ps') in (A,[s0, Nt B]) # (B, u) # ps)"

definition binarize' :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize' ps = binarize1 ps ps"

fun count :: "('n::infinite, 't) prods \<Rightarrow> nat" where
  "count [] = 0"
| "count ((A,u) # ps) = (if length u \<le> 2 then count ps else length u + count ps)"

definition binarize :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize ps = (binarize' ^^ (count ps)) ps"

text
\<open>Firstly we show that the \<open>binarize\<close> function transforms a production list into a binary production list\<close>

lemma count_dec1:
  assumes "binarize1 ps' ps \<noteq> ps" 
  shows "count ps > count (binarize1 ps' ps)"
using assms proof (induction ps' ps rule: binarize1.induct)
  case (3 ps' A s0 u ps)
  show ?case proof (cases "length u \<le> 1")
    case True
    with "3.prems" have "binarize1 ps' ps \<noteq> ps" by simp
    with True have "count (binarize1 ps' ps) < count ps"
      using "3.IH" by simp
    with True show ?thesis by simp
  next
    case False
    let ?B = "fresh(nts ps')"
    from False have "count (binarize1 ps' ((A, s0 # u) # ps)) = count ((A,[s0, Nt ?B]) # (?B, u) # ps)"
      by (metis binarize1.simps(3))
    also have "... = count ((?B, u) # ps)" by simp
    also from False have "... < count ((A, s0 # u) # ps)" by simp
    finally have "count (binarize1 ps' ((A, s0 # u) # ps)) < count ((A, s0 # u) # ps)" by simp
    thus ?thesis .
  qed
qed simp_all

lemma count_dec':
  assumes "binarize' ps \<noteq> ps" 
  shows "count ps > count (binarize' ps)"
 using binarize'_def assms count_dec1 by metis

lemma binarize_ffpi:
  "binarize'((binarize' ^^ count x) x) = (binarize' ^^ count x) x"
proof -
  have "\<And>x. count(binarize' x) < count x \<or> binarize' x = x"
    using count_dec' by blast
  thus ?thesis using funpow_fix by metis
qed

lemma binarize_binary1: 
  assumes "ps = binarize1 ps' ps"
  shows "(A,w) \<in> set(binarize1 ps' ps) \<Longrightarrow> length w \<le> 2"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (3 ps' C s0 u ps)
  show ?case proof (cases "length u \<le> 1")
    case True
    with 3 show ?thesis by auto
  next
    case False
    hence "(C, s0 # u) # ps \<noteq> binarize1 ps' ((C, s0 # u) # ps)"
      by (metis binarize1.simps(3) list.sel(3) not_Cons_self2)
    with "3.prems"(2) show ?thesis by blast
  qed
qed auto

lemma binarize_binary':
  assumes "ps = binarize' ps"
  shows "(A,w) \<in> set(binarize' ps) \<Longrightarrow> length w \<le> 2"
  using binarize'_def assms binarize_binary1 by metis

lemma binarize_binary: "(A,w) \<in> set(binarize ps) \<Longrightarrow> length w \<le> 2"
  unfolding binarize_def using binarize_ffpi binarize_binary' by metis

text
\<open>Now we prove the property of language preservation\<close>

lemma binarize1_cases:
  "binarize1 ps' ps = ps \<or> (\<exists>A ps'' B u s. set ps = {(A, s#u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A,[s,Nt B]),(B,u)} \<union> set ps'' \<and> Nt B \<notin> syms ps')"
proof (induction ps' ps rule: binarize1.induct)
  case (2 ps' C ps)
  then show ?case
  proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
      using 2 by blast
    from defs have wit: "set ((C, []) # ps) = {(A, s # u)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, []) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (3 ps' C s0 u ps)
  show ?case proof (cases "length u \<le> 1")
    case T1: True
    then show ?thesis proof (cases "binarize1 ps' ps = ps")
      case T2: True
      with T1 show ?thesis by simp
    next
      case False
      with T1 obtain A ps'' B v s where defs: "set ps = {(A, s # v)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, v)} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
        using 3 by blast
      from defs have wit: "set ((C, s0 # u) # ps) = {(A, s # v)} \<union> set ((C, s0 # u) # ps'')" by simp
      from defs T1 have wit2: "set (binarize1 ps' ((C, s0 # u) # ps)) = {(A, [s, Nt B]), (B, v)} \<union> set ((C, s0 # u) # ps'')" by simp
      from defs have wit3: "Nt B \<notin> syms ps'" by simp
      from wit wit2 wit3 show ?thesis by blast
    qed
   next
    case False
    then show ?thesis
      using fresh_nts in_Nts_iff_in_Syms[of "fresh (nts ps')" "set ps'"]
      by (fastforce simp add: Let_def)
  qed
qed simp

text
\<open>We show that a list of terminals \<open>map Tm x\<close> can be derived from the original production set \<open>ps\<close> if and only if \<open>map Tm x\<close>
 can be derived after the transformation of the step function \<open>binarize'\<close>, under the assumption that the starting symbol \<open>A\<close>
 occurs in a left-hand side of at least one production in \<open>ps\<close>. We can then extend this property to the \<open>binarize\<close> function\<close>

lemma binarize_der':
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize' ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  unfolding binarize'_def proof (cases "binarize1 ps ps = ps")
  case False
  then obtain C ps'' B u s where defs: "set ps = {(C, s # u)} \<union> set ps'' \<and> set (binarize1 ps ps) = {(C, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> syms ps"
    by (meson binarize1_cases)
  from defs have a_not_b: "C \<noteq> B" unfolding Syms_def by fast
  from defs assms have a1: "A \<noteq> B" unfolding Lhss_def Syms_def by auto
  from defs have a2: "Nt B \<notin> set (map Tm x)" by auto
  from defs have a3: "Nt B \<notin> set u" unfolding Syms_def by fastforce
  from defs have "set ps = set ((C, s # u) # ps'')" by simp
  with defs a_not_b have a4: "B \<notin> lhss ((C, [s, Nt B]) # ps'')" unfolding Lhss_def Syms_def by auto
  from defs have notB: "Nt B \<notin> syms ps''" by fastforce
  then have 1: "set ps = set (substP (Nt B) u ((C, [s, Nt B]) # ps''))" proof -
    from defs have "set ps = {(C, s # u)} \<union> set ps''" by simp
    also have "... = set ((C, s#u) # ps'')" by simp
    also have "... = set ([(C, s#u)] @ ps'')" by simp
    also from defs have "... = set ([(C,substs (Nt B) u [s, Nt B])] @ ps'')" unfolding Syms_def by fastforce
    also have "... = set ((substP (Nt B) u [(C, [s, Nt B])]) @ ps'')" by (simp add: substP_def)
    also have "... = set ((substP (Nt B) u [(C, [s, Nt B])]) @ substP (Nt B) u ps'')" using notB by (simp add: substP_skip2)
    also have "... = set (substP (Nt B) u ((C, [s, Nt B]) # ps''))" by (simp add: substP_def)
    finally show ?thesis .
  qed
  from defs have 2: "set (binarize1 ps ps) = set ((C, [s, Nt B]) # (B, u) # ps'')" by auto
  with 1 2 a1 a2 a3 a4 show "(set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x) = (set (binarize1 ps ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x)"
    by (simp add: derives_inlining insert_commute)
qed simp

lemma lhss_binarize1:
  "lhss ps \<subseteq> lhss (binarize1 ps' ps)"
proof (induction ps' ps rule: binarize1.induct)
  case (3 ps' A s0 u ps)
  then show ?case proof (cases "length u \<le> 1")
    case True
    with 3 show ?thesis by auto
  next
    case False
    let ?B = "fresh(nts ps')"
    have "lhss ((A, s0 # u) # ps) = {A} \<union> lhss ps" by simp
    also have "... \<subseteq> {A} \<union> {?B} \<union> lhss ps" by blast
    also have "... = lhss ((A,[s0, Nt ?B]) # (?B, u) # ps)" by simp
    also from False have "... = lhss (binarize1 ps' ((A, s0 # u) # ps))"
      by (metis binarize1.simps(3))
    finally show ?thesis .
  qed
qed auto

lemma lhss_binarize'n:
  "lhss ps \<subseteq> lhss ((binarize'^^n) ps)"
proof (induction n)
  case (Suc n)
  thus ?case unfolding binarize'_def using lhss_binarize1 by auto
qed simp

lemma binarize_der'n: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((binarize'^^n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
using assms proof (induction n)
  case (Suc n)
  hence "A \<in> lhss ((binarize' ^^ n) ps)"
    using lhss_binarize'n by blast
  hence "set ((binarize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize' ((binarize' ^^ n) ps)) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    using binarize_der' by blast
  hence "set ((binarize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((binarize' ^^ Suc n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by simp
  with Suc show ?case by blast
qed simp

lemma binarize_der: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  unfolding binarize_def using binarize_der'n[OF assms] by simp

lemma lang_binarize_lhss: 
  assumes "A \<in> lhss ps"
  shows "lang ps A = lang (binarize ps) A"
  using binarize_der[OF assms] Lang_eqI_derives by metis

text
\<open>As a last step, we generalize the language preservation property to also include non-terminals which only occur at right-hand
 sides of the production set\<close>

lemma binarize_syms1:
  assumes  "Nt A \<in> syms ps"
    shows  "Nt A \<in> syms (binarize1 ps' ps)"
using assms proof (induction ps' ps rule: binarize1.induct)
  case (3 ps' A s0 u ps)
  show ?case proof (cases "length u \<le> 1")
    case True
    with 3 show ?thesis by auto
  next
    case False
    with 3 show ?thesis by (auto simp: Syms_def Let_def)
  qed
qed auto

lemma binarize_lhss_nts1:
  assumes "A \<notin> lhss ps"
      and "A \<in> nts ps'"
    shows "A \<notin> lhss (binarize1 ps' ps)"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (3 ps' A s0 u ps)
  thus ?case proof (cases "length u \<le> 1")
    case True
    with 3 show ?thesis by auto
  next
    case False
    with 3 show ?thesis by (auto simp add: Let_def fresh_nts)
  qed
qed simp_all

lemma binarize_lhss_nts'n:
  assumes "A \<notin> lhss ps"
      and "A \<in> nts ps"
    shows "A \<notin> lhss ((binarize'^^n) ps) \<and> A \<in> nts ((binarize'^^n) ps)"
using assms proof (induction n)
  case (Suc n)
  thus ?case 
    unfolding binarize'_def by (simp add: binarize_lhss_nts1 binarize_syms1 in_Nts_iff_in_Syms)
qed simp

lemma binarize_lhss_nts:
   assumes "A \<notin> lhss ps"
      and  "A \<in> nts ps"
    shows "A \<notin> lhss (binarize ps) \<and> A \<in> nts (binarize ps)"
  unfolding binarize_def using binarize_lhss_nts'n[OF assms] by simp

lemma binarize_nts'n:
  assumes "A \<in> nts ps"
  shows   "A \<in> nts ((binarize' ^^ n) ps)"
using assms proof (induction n)
  case (Suc n)
  thus ?case 
    unfolding binarize'_def by (simp add: binarize_syms1 in_Nts_iff_in_Syms)
qed simp

lemma binarize_nts:
  assumes "A \<in> nts ps"
  shows   "A \<in> nts (binarize ps)"
  unfolding binarize_def using assms binarize_nts'n by blast

lemma lang_binarize: 
  assumes "A \<in> nts ps"
  shows "lang (binarize ps) A = lang ps A"
proof (cases "A \<in> lhss ps")
  case True
  thus ?thesis
    using lang_binarize_lhss by blast
next
  case False
  thus ?thesis
    using assms binarize_lhss_nts Lang_empty_if_notin_Lhss by fast
qed

end