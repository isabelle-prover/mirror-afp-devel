section\<open>Relativization of Finite Functions\<close>
theory FiniteFun_Relative
  imports
    Lambda_Replacement
begin

lemma FiniteFunI :
  assumes  "f\<in>Fin(A\<times>B)" "function(f)"
  shows "f \<in> A -||> B"
  using assms
proof(induct)
  case 0
  then show ?case using emptyI by simp
next
  case (cons p f)
  moreover
  from assms this
  have "fst(p)\<in>A" "snd(p)\<in>B" "function(f)"
    using snd_type[OF \<open>p\<in>_\<close>] function_subset
    by auto
  moreover
  from \<open>function(cons(p,f))\<close> \<open>p\<notin>f\<close> \<open>p\<in>_\<close>
  have "fst(p)\<notin>domain(f)"
    unfolding function_def
    by force
  ultimately
  show ?case
    using consI[of "fst(p)" _ "snd(p)"]
    by auto
qed

subsection\<open>The set of finite binary sequences\<close>

text\<open>We implement the poset for adding one Cohen real, the set
$2^{<\omega}$ of finite binary sequences.\<close>

definition
  seqspace :: "[i,i] \<Rightarrow> i" (\<open>_\<^bsup><_\<^esup>\<close> [100,1]100) where
  "B\<^bsup><\<alpha>\<^esup> \<equiv> \<Union>n\<in>\<alpha>. (n\<rightarrow>B)"

schematic_goal seqspace_fm_auto:
  assumes
    "i \<in> nat" "j \<in> nat" "h\<in>nat" "env \<in> list(A)"
  shows
    "(\<exists>om\<in>A. omega(##A,om) \<and> nth(i,env) \<in> om \<and> is_funspace(##A, nth(i,env), nth(h,env), nth(j,env))) \<longleftrightarrow> (A, env \<Turnstile> (?sqsprp(i,j,h)))"
  unfolding is_funspace_def
  by (insert assms ; (rule iff_sats | simp)+)

synthesize "seqspace_rel" from_schematic "seqspace_fm_auto"
arity_theorem for "seqspace_rel_fm"

lemma seqspaceI[intro]: "n\<in>\<alpha> \<Longrightarrow> f:n\<rightarrow>B \<Longrightarrow> f\<in>B\<^bsup><\<alpha>\<^esup>"
  unfolding seqspace_def by blast

lemma seqspaceD[dest]: "f\<in>B\<^bsup><\<alpha>\<^esup> \<Longrightarrow> \<exists>n\<in>\<alpha>. f:n\<rightarrow>B"
  unfolding seqspace_def by blast

locale M_seqspace =  M_trancl + M_replacement +
  assumes
    seqspace_replacement: "M(B) \<Longrightarrow> strong_replacement(M,\<lambda>n z. n\<in>nat \<and> is_funspace(M,n,B,z))"
begin

lemma seqspace_closed:
  "M(B) \<Longrightarrow> M(B\<^bsup><\<omega>\<^esup>)"
  unfolding seqspace_def using seqspace_replacement[of B] RepFun_closed2
  by simp
end

subsection\<open>Representation of finite functions\<close>

text\<open>A function $f\in A\to_{\mathit{fin}}B$ can be represented by a function
$g\in |f| \to A\times B$. It is clear that $f$ can be represented by
any $g' = g \cdot \pi$, where $\pi$ is a permutation $\pi\in dom(g)\to dom(g)$.
We use this representation of $A\to_{\mathit{fin}}B$ to prove that our model is
closed under $\_\to_{\mathit{fin}}\_$.\<close>

text\<open>A function $g\in n\to A\times B$ that is functional in the first components.\<close>
definition cons_like :: "i \<Rightarrow> o" where
  "cons_like(f) \<equiv> \<forall> i\<in>domain(f) . \<forall>j\<in>i . fst(f`i) \<noteq> fst(f`j)"

relativize "cons_like" "cons_like_rel"

lemma (in M_seqspace) cons_like_abs:
  "M(f) \<Longrightarrow> cons_like(f) \<longleftrightarrow> cons_like_rel(M,f)"
  unfolding cons_like_def cons_like_rel_def
  using fst_abs
  by simp

definition FiniteFun_iso :: "[i,i,i,i,i] \<Rightarrow> o" where
  "FiniteFun_iso(A,B,n,g,f) \<equiv>  (\<forall> i\<in>n . g`i \<in> f) \<and> (\<forall> ab\<in>f. (\<exists> i\<in>n. g`i=ab))"

text\<open>From a function $g\in n \to A\times B$ we obtain a finite function in \<^term>\<open>A-||>B\<close>.\<close>

definition to_FiniteFun :: "i \<Rightarrow> i" where
  "to_FiniteFun(f) \<equiv> {f`i. i\<in>domain(f)}"

definition FiniteFun_Repr :: "[i,i] \<Rightarrow> i" where
  "FiniteFun_Repr(A,B) \<equiv> {f \<in> (A\<times>B)\<^bsup><\<omega>\<^esup> . cons_like(f) }"

locale M_FiniteFun =  M_seqspace +
  assumes
    cons_like_separation : "separation(M,\<lambda>f. cons_like_rel(M,f))"
    and
    separation_is_function : "separation(M, is_function(M))"
begin

lemma supset_separation: "separation(M, \<lambda> x. \<exists>a. \<exists>b. x = \<langle>a,b\<rangle> \<and> b \<subseteq> a)"
  using separation_pair separation_subset lam_replacement_fst lam_replacement_snd
  by simp

lemma to_finiteFun_replacement: "strong_replacement(M, \<lambda>x y. y = range(x))"
  using lam_replacement_range lam_replacement_imp_strong_replacement
  by simp

lemma fun_range_eq: "f\<in>A\<rightarrow>B \<Longrightarrow> {f`i . i\<in>domain(f) } = range(f)"
  using ZF_Library.range_eq_image[of f] domain_of_fun image_fun func.apply_rangeI
  by simp

lemma FiniteFun_fst_type:
  assumes "h\<in>A-||>B" "p\<in>h"
  shows  "fst(p)\<in>domain(h)"
  using assms
  by(induct h, auto)

lemma FinFun_closed:
  "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(\<Union>{n\<rightarrow>A\<times>B . n\<in>\<omega>})"
  using cartprod_closed seqspace_closed
  unfolding seqspace_def by simp

lemma cons_like_lt :
  assumes "n\<in>\<omega>" "f\<in>succ(n)\<rightarrow>A\<times>B" "cons_like(f)"
  shows "restrict(f,n)\<in>n\<rightarrow>A\<times>B" "cons_like(restrict(f,n))"
  using assms
proof (auto simp add: le_imp_subset restrict_type2)
  from \<open>f\<in>_\<close>
  have D:"domain(restrict(f,n)) = n" "domain(f) = succ(n)"
    using domain_of_fun domain_restrict by auto
  {
    fix i j
    assume "i\<in>domain(restrict(f,n))" (is "i\<in>?D") "j\<in>i"
    with \<open>n\<in>_\<close> D
    have "j\<in>?D" "i\<in>n" "j\<in>n" using Ord_trans[of j] by simp_all
    with D \<open>cons_like(f)\<close>  \<open>j\<in>n\<close> \<open>i\<in>n\<close> \<open>j\<in>i\<close>
    have "fst(restrict(f,n)`i) \<noteq> fst(restrict(f,n)`j)"
      using restrict_if unfolding cons_like_def by auto
  }
  then show "cons_like(restrict(f,n))"
    unfolding cons_like_def by auto
qed

text\<open>A finite function \<^term>\<open>f \<in> A -||> B\<close> can be represented by a
function $g \in n \to A \times B$, with $n=|f|$.\<close>
lemma FiniteFun_iso_intro1:
  assumes "f \<in> (A -||> B)"
  shows "\<exists>n\<in>\<omega> . \<exists>g\<in>n\<rightarrow>A\<times>B. FiniteFun_iso(A,B,n,g,f) \<and> cons_like(g)"
  using assms
proof(induct f,force simp add:emptyI FiniteFun_iso_def cons_like_def)
  case (consI a b h)
  then obtain n g where
    HI: "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "FiniteFun_iso(A,B,n,g,h)" "cons_like(g)" by auto
  let ?G="\<lambda> i \<in> succ(n) . if i=n then <a,b> else g`i"
  from HI \<open>a\<in>_\<close> \<open>b\<in>_\<close>
  have G: "?G \<in> succ(n)\<rightarrow>A\<times>B"
    by (auto intro:lam_type)
  have "FiniteFun_iso(A,B,succ(n),?G,cons(<a,b>,h))"
    unfolding FiniteFun_iso_def
  proof(intro conjI)
    {
      fix i
      assume "i\<in>succ(n)"
      then consider "i=n" | "i\<in>n\<and>i\<noteq>n" by auto
      then have "?G ` i \<in> cons(<a,b>,h)"
        using HI
        by(cases,simp;auto simp add:HI FiniteFun_iso_def)
    }
    then show "\<forall>i\<in>succ(n). ?G ` i \<in> cons(\<langle>a, b\<rangle>, h)" ..
  next
    { fix ab'
      assume "ab' \<in> cons(<a,b>,h)"
      then
      consider  "ab' = <a,b>" | "ab' \<in> h" using cons_iff by auto
      then
      have "\<exists>i \<in> succ(n) . ?G`i = ab'" unfolding FiniteFun_iso_def
      proof(cases,simp)
        case 2
        with HI obtain i
          where "i\<in>n" "g`i=ab'" unfolding FiniteFun_iso_def by auto
        with HI show ?thesis using  ltI[OF \<open>i\<in>_\<close>] by auto
      qed
    }
    then
    show "\<forall>ab\<in>cons(\<langle>a, b\<rangle>, h). \<exists>i\<in>succ(n). ?G`i = ab"  ..
  qed
  with HI G
  have 1: "?G\<in>succ(n)\<rightarrow>A\<times>B" "FiniteFun_iso(A,B,succ(n),?G,cons(<a,b>,h))" "succ(n)\<in>\<omega>" by simp_all
  have "cons_like(?G)"
  proof -
    from \<open>?G\<in>_\<close> \<open>g\<in>_\<close>
    have "domain(g) = n" using domain_of_fun by simp
    {
      fix i j
      assume "i\<in>domain(?G)" "j\<in>i"
      with \<open>n\<in>_\<close>
      have "j\<in>n" using Ord_trans[of j _ n] by auto
      from \<open>i\<in>_\<close> consider (a) "i=n \<and> i\<notin>n" | (b) "i\<in>n" by auto
      then
      have " fst(?G`i) \<noteq> fst(?G`j)"
      proof(cases)
        case a
        with \<open>j\<in>n\<close> HI
        have "?G`i=<a,b>" "?G`j=g`j" "g`j\<in>h"
          unfolding FiniteFun_iso_def by auto
        with \<open>a\<notin>_\<close> \<open>h\<in>_\<close>
        show ?thesis using  FiniteFun_fst_type by auto
      next
        case b
        with \<open>i\<in>n\<close> \<open>j\<in>i\<close> \<open>j\<in>n\<close> HI \<open>domain(g) = n\<close>
        show ?thesis unfolding cons_like_def
          using mem_not_refl by auto
      qed
    }
    then show ?thesis unfolding cons_like_def by auto
  qed
  with 1 show ?case by auto
qed

text\<open>All the representations of \<^term>\<open>f\<in>A-||>B\<close> are equal.\<close>
lemma FiniteFun_isoD :
  assumes "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "f\<in>A-||>B" "FiniteFun_iso(A,B,n,g,f)"
  shows "to_FiniteFun(g) = f"
proof
  show "to_FiniteFun(g) \<subseteq> f"
  proof
    fix ab
    assume "ab\<in>to_FiniteFun(g)"
    moreover
    note assms
    moreover from calculation
    obtain i where "i\<in>n" "g`i=ab" "ab\<in>A\<times>B"
      unfolding to_FiniteFun_def using domain_of_fun by auto
    ultimately
    show "ab\<in>f" unfolding FiniteFun_iso_def by auto
  qed
next
  show "f \<subseteq> to_FiniteFun(g)"
  proof
    fix ab
    assume "ab\<in>f"
    with assms
    obtain i where "i\<in>n" "g`i=ab" "ab\<in>A\<times>B"
      unfolding FiniteFun_iso_def by auto
    with assms
    show "ab \<in> to_FiniteFun(g)"
      unfolding to_FiniteFun_def
      using domain_of_fun by auto
  qed
qed

lemma to_FiniteFun_succ_eq :
  assumes "n\<in>\<omega>" "f\<in>succ(n) \<rightarrow> A"
  shows "to_FiniteFun(f) = cons(f`n,to_FiniteFun(restrict(f,n)))"
  using assms domain_restrict domain_of_fun
  unfolding to_FiniteFun_def by auto

text\<open>If $g \in n\to A\times B$ is \<^term>\<open>cons_like\<close>, then it is a representation of
\<^term>\<open>to_FiniteFun(g)\<close>.\<close>
lemma FiniteFun_iso_intro_to:
  assumes "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "cons_like(g)"
  shows "to_FiniteFun(g) \<in> (A -||> B) \<and> FiniteFun_iso(A,B,n,g,to_FiniteFun(g))"
  using assms
proof(induct n  arbitrary:g rule:nat_induct)
  case 0
  fix g
  assume "g\<in>0\<rightarrow>A\<times>B"
  then
  have "g=0" by simp
  then have "to_FiniteFun(g)=0" unfolding to_FiniteFun_def by simp
  then show "to_FiniteFun(g) \<in> (A -||> B) \<and> FiniteFun_iso(A,B,0,g,to_FiniteFun(g))"
    using emptyI unfolding FiniteFun_iso_def by simp
next
  case (succ x)
  fix g
  let ?g'="restrict(g,x)"
  assume "g\<in>succ(x)\<rightarrow>A\<times>B" "cons_like(g)"
  with succ.hyps \<open>g\<in>_\<close>
  have "cons_like(?g')" "?g' \<in> x\<rightarrow>A\<times>B" "g`x\<in>A\<times>B" "domain(g) = succ(x)"
    using cons_like_lt succI1 apply_funtype domain_of_fun by simp_all
  with succ.hyps  \<open>?g'\<in>_\<close> \<open>x\<in>\<omega>\<close>
  have HI:
    "to_FiniteFun(?g') \<in> A -||> B" (is "(?h) \<in> _")
    "FiniteFun_iso(A,B,x,?g',to_FiniteFun(?g'))"
    by simp_all
  then
  have "fst(g`x) \<notin> domain(?h)"
  proof -
    {
      assume "fst(g`x) \<in> domain(?h)"
      with HI \<open>x\<in>_\<close>
      obtain i b
        where "i\<in>x" "<fst(?g'`i),b>\<in>?h" "i<x" "fst(g`x) = fst(?g'`i)"
        unfolding FiniteFun_iso_def using ltI by auto
      with \<open>cons_like(g)\<close> \<open>domain(g) = _\<close>
      have False
        unfolding cons_like_def by auto
    }
    then show ?thesis ..
  qed
  with HI assms \<open>g`x\<in>_\<close>
  have "cons(g`x,?h) \<in> A-||>B" (is "?h' \<in>_") using consI by auto
  have "FiniteFun_iso(A,B,succ(x),g,?h')"
    unfolding FiniteFun_iso_def
  proof
    { fix i
      assume "i\<in>succ(x)"
      with \<open>x\<in>_\<close> consider (a) "i=x"| (b) "i\<in>x\<and>i\<noteq>x" by auto
      then have "g`i\<in> ?h'"
      proof(cases,simp)
        case b
        with \<open>FiniteFun_iso(_,_,_,?g',?h)\<close>
        show ?thesis unfolding FiniteFun_iso_def by simp
      qed
    }
    then show "\<forall>i\<in>succ(x). g ` i \<in> cons(g ` x, ?h)" ..
  next
    {
      fix ab
      assume "ab\<in>?h'"
      then consider "ab=g`x" | "ab \<in> ?h" using cons_iff by auto
      then
      have "\<exists>i \<in> succ(x) . g`i = ab" unfolding FiniteFun_iso_def
      proof(cases,simp)
        case 2
        with HI obtain i
          where 2:"i\<in>x" "?g'`i=ab"  unfolding FiniteFun_iso_def by auto
        with \<open>x\<in>_\<close>
        have "i\<noteq>x" "i\<in>succ(x)" using  ltI[OF \<open>i\<in>_\<close>] by auto
        with 2 HI show ?thesis by auto
      qed
    } then show "\<forall>ab\<in>cons(g ` x, ?h). \<exists>i\<in>succ(x). g ` i = ab" ..
  qed
  with \<open>?h'\<in>_\<close>
  show "to_FiniteFun(g) \<in> A -||>B \<and> FiniteFun_iso(A,B,succ(x),g,to_FiniteFun(g))"
    using to_FiniteFun_succ_eq[OF \<open>x\<in>_\<close> \<open>g\<in>_\<close>,symmetric] by auto
qed

lemma FiniteFun_iso_intro2:
  assumes "n\<in>\<omega>" "f\<in>n\<rightarrow>A\<times>B" "cons_like(f)"
  shows "\<exists> g \<in> (A -||> B) . FiniteFun_iso(A,B,n,f,g)"
  using assms FiniteFun_iso_intro_to by blast

lemma FiniteFun_eq_range_Repr :
  shows "{range(h) . h \<in> FiniteFun_Repr(A,B) } = {to_FiniteFun(h) . h \<in> FiniteFun_Repr(A,B) }"
  unfolding FiniteFun_Repr_def to_FiniteFun_def seqspace_def
  using fun_range_eq
  by(intro equalityI subsetI,auto)


lemma FiniteFun_eq_to_FiniteFun_Repr :
  shows "A-||>B = {to_FiniteFun(h) . h \<in> FiniteFun_Repr(A,B) } "
    (is "?Y=?X")
proof
  {
    fix f
    assume "f\<in>A-||>B"
    then obtain n g where
      1: "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "FiniteFun_iso(A,B,n,g,f)" "cons_like(g)"
      using FiniteFun_iso_intro1 by blast
    with \<open>f\<in>_\<close>
    have "cons_like(g)" "f=to_FiniteFun(g)" "domain(g) = n" "g\<in>FiniteFun_Repr(A,B)"
      using FiniteFun_isoD domain_of_fun
      unfolding FiniteFun_Repr_def
      by auto
    with 1 have "f\<in>?X"
      by auto
  } then show "?Y\<subseteq>?X" ..
next
  {
    fix f
    assume "f\<in>?X"
    then obtain g where
      A:"g\<in>FiniteFun_Repr(A,B)" "f=to_FiniteFun(g)" "cons_like(g)"
      using RepFun_iff unfolding FiniteFun_Repr_def by auto
    then obtain n where "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "domain(g) = n"
      unfolding FiniteFun_Repr_def using domain_of_fun by force
    with A
    have "f\<in>?Y"
      using FiniteFun_iso_intro_to by simp
  } then show "?X\<subseteq>?Y" ..
qed

lemma FiniteFun_Repr_closed :
  assumes "M(A)" "M(B)"
  shows "M(FiniteFun_Repr(A,B))"
  unfolding FiniteFun_Repr_def
  using assms cartprod_closed
    seqspace_closed separation_closed cons_like_abs cons_like_separation
  by simp

lemma to_FiniteFun_closed:
  assumes "M(A)" "f\<in>A"
  shows "M(range(f))"
  using assms transM[of _ A] by simp

lemma To_FiniteFun_Repr_closed :
  assumes "M(A)" "M(B)"
  shows "M({range(h) . h \<in> FiniteFun_Repr(A,B) })"
  using assms FiniteFun_Repr_closed
    RepFun_closed  to_finiteFun_replacement
    to_FiniteFun_closed[OF FiniteFun_Repr_closed]
  by simp

lemma FiniteFun_closed[intro,simp] :
  assumes "M(A)" "M(B)"
  shows "M(A -||> B)"
  using assms To_FiniteFun_Repr_closed FiniteFun_eq_to_FiniteFun_Repr
    FiniteFun_eq_range_Repr
  by simp

end \<comment> \<open>\<^locale>\<open>M_FiniteFun\<close>\<close>

end