
(*
Title:         Rules and Methods for Rely-Guarantee Annotated Commands
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

subsection \<open>Introduction-Rules and Methods\<close>

theory RG_Annotated_Methods
imports RG_Annotated_Commands "HOL-Library.Sublist"
begin

text \<open>We begin with some helpers.\<close>

lemma invariant_int_subset_intro: "a \<inter> x \<subseteq> b \<Longrightarrow> a \<inter> x \<subseteq> b \<inter> x"
  by auto

abbreviation prefix_of:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<preceq>" 45) where
"prefix_of t t' \<equiv> prefix t t'"

abbreviation "suffix_of t t' \<equiv> suffix t' t"
abbreviation "longer x \<equiv>  \<lbrace>\<ordmasculine>x \<preceq> \<ordfeminine>x\<rbrace>"
abbreviation "shorter x \<equiv> \<lbrace>suffix_of \<ordmasculine>x \<ordfeminine>x\<rbrace>"

method mintro = ((intro allI impI conjI ballI IntI)? ; (elim conjE)?)

(*----------------------------------------------------------------------------*)
text \<open>The notion @{text \<open>stable_from P I R\<close>} is a weaker version of stability.
It asks if the predicate @{text P} is stable under the relation @{text R} 
from a state that also satsifies the invariant @{text I}
This helps to separate out repeated checks of stability of @{text I}.\<close>

definition stable_from :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "stable_from p i r \<equiv> (\<forall>s s'. s \<in> p \<and> s \<in> i \<longrightarrow> (s, s') \<in> r \<longrightarrow> s' \<in> i \<longrightarrow> s' \<in> p)"

lemma stable_to_stable_from_simp[simp]:
  "stable (pre \<inter> invar) (lift_rely invar rely) = stable_from pre invar rely"
  by (auto simp add: stable_from_def)

lemma stable_from_int_intro: 
  assumes "stable_from p1 (i ) r" and " stable_from p2 (i ) r"
  shows " stable_from (p1 \<inter> p2) i r  "
  using assms by (auto simp add: stable_from_def)

(*============================================================================*)
text \<open>Our proof tactics later in this theory is based on logical \emph{introduction},
which corresponds to the built-in @{text intro} method.
To facilitate the automation, we first devise the specialised introduction-rules
for the types of annotated commands.\<close>

subsubsection NoAnno

theorem intro_NoAnno:
  assumes "\<turnstile> c sat [pre, rely, guar, post]"
  shows "anncom_spec_valid pre rely guar post (NoAnno c)"
  using assms by simp

theorem intro_NoAnno_Basic:
assumes "stable pre rely"
      and "stable post rely"
      and "\<And>s. s \<in> pre \<Longrightarrow> (s, s) \<in> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> (s, f s) \<in> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> f s \<in> post" 
shows "anncom_spec_valid pre rely guar post (NoAnno (Basic f))"
  using assms by auto

theorem intro_NoAnno_Basic_annquin:
assumes "stable pre rely"
      and "stable post rely"
      and "\<And>s. s \<in> pre \<Longrightarrow> (s, s) \<in> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> (s, f s) \<in> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> f s \<in> post" 
shows "annquin_valid {pre, rely}   (NoAnno (Basic f)) {guar, post}"
  using assms by auto

subsubsection BasicAnno

theorem intro_BasicAnno_with_invariant:
  assumes "stable_from pre invar rely"
      and "stable_from post invar rely"
      and "Id \<subseteq> guar"
(*      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> (s, s) \<in> guar" *)
      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> f s \<in> invar"
      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> (s, f s) \<in> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> f s \<in> post" 
    shows "annquin_valid ({pre , rely} (BasicAnno f) \<sslash> invar {guar, post})"
  using assms by (auto simp add: stable_from_def annquin_invar_def)

theorem intro_NoAnno_Basic_with_invariant:
  assumes "stable_from pre invar rely"
      and "stable_from post invar rely"
      and "Id \<subseteq> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> f s \<in> invar"
      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> (s, f s) \<in> guar"
      and "\<And>s. s \<in> pre \<Longrightarrow> s \<in> invar \<Longrightarrow> f s \<in> post" 
    shows "annquin_valid ({pre , rely} (NoAnno (Basic f)) \<sslash> invar {guar, post})"
  using assms by (auto simp add: stable_from_def annquin_invar_def)

theorem intro_SkipAnno:
  assumes "stable pre rely" and
    "stable post rely" and
    "Id \<subseteq> guar" and
    "pre \<subseteq> post"
  shows "anncom_spec_valid pre rely guar post  SKIPa"
  using assms apply auto
  by (meson assms(1) assms(2) rg_skip_named)

theorem intro_SKIPa_with_invariant:
  assumes "stable_from pre invar rely"
      and "stable_from post invar rely"
      and "Id \<subseteq> guar"
      and "pre \<inter> invar \<subseteq> post"
    shows "annquin_valid {pre, rely} SKIPa \<sslash> invar {guar, post}"
  apply (simp add: annquin_invar_def)
  apply (rule rg_skip_named stable_from_def)
  apply (metis assms(1) lift_rely_def stable_to_stable_from_simp)
    apply (metis assms(2) lift_rely_def stable_to_stable_from_simp)
   apply simp
  by (metis assms(4) invariant_int_subset_intro)

subsubsection WeakPre

theorem intro_WeakPre:
  assumes "pre \<subseteq> p'"
    and "anncom_spec_valid p' rely guar post ac"
  shows "anncom_spec_valid pre rely guar post (WeakPre p' ac)"
  using assms by simp

theorem intro_WeakPre_with_invariant:
  assumes "pre \<subseteq> p'"
    and "annquin_valid {p', rely} ac \<sslash>invar {guar, post}"
  shows "annquin_valid {pre, rely}  (WeakPre p' ac) \<sslash> invar {guar, post}"
  using assms(1) assms(2) by (auto simp add: annquin_invar_def)

subsubsection StrongPost

theorem intro_StrongPost:
  assumes "q' \<subseteq> post" and
     "anncom_spec_valid pre rely guar q' ac"
   shows  "anncom_spec_valid pre rely guar post (StrongPost ac q')"
    using assms by simp

theorem intro_StrongPost_with_invariant:
  assumes "q' \<subseteq> post" and
     "annquin_valid {pre , rely} ac \<sslash>invar {guar, q'}"
   shows "annquin_valid {pre, rely}  (StrongPost ac q') \<sslash> invar {guar, post}"
    using assms(1) assms(2) by (auto simp add: annquin_invar_def)

subsubsection SeqAnno

theorem intro_SeqAnno:
  assumes "anncom_spec_valid pre rely guar mid  ac1"
    and "anncom_spec_valid mid rely guar post ac2"
  shows "anncom_spec_valid pre rely guar post (SeqAnno ac1 mid ac2)"
  using assms by simp

theorem intro_SeqAnno_with_invariant:
  assumes "annquin_valid {pre , rely} ac1 \<sslash> invar { guar, mid}"
    and "annquin_valid {mid , rely} ac2 \<sslash> invar { guar, post}"
  shows "annquin_valid {pre , rely}  (ac1 .; {mid} ac2) \<sslash> invar {guar, post}"
  using assms by (auto simp add: annquin_invar_def)

theorem intro_SeqAnno_invar:
  assumes "anncom_spec_valid pre rely guar (mid \<inter> invar)  (add_invar invar ac1)"
      and "anncom_spec_valid (mid \<inter> invar) rely guar post (add_invar invar ac2)"
    shows "anncom_spec_valid pre rely guar post (add_invar invar (SeqAnno ac1 mid ac2))"
  using assms by simp

subsubsection Conditionals

theorem intro_CondAnno:
  assumes 
     "stable pre rely" and
     "Id \<subseteq> guar" and
     "anncom_spec_valid (pre \<inter>  b) rely guar post ac1" and
     "anncom_spec_valid (pre \<inter> -b) rely guar post ac2"
shows "anncom_spec_valid pre rely guar post (CondAnno b ac1 ac2)"
  using assms by simp

theorem intro_CondAnno_annquin:
  assumes 
     "stable pre rely" and
     "Id \<subseteq> guar" and
      "annquin_valid {(pre \<inter>  b), rely} ac1 { guar, post}" and
      "annquin_valid {(pre \<inter> -b), rely} ac2 { guar, post}"
shows "annquin_valid {pre, rely}  (CondAnno b ac1 ac2) {guar, post}"
  using assms by simp

theorem intro_CondAnno_with_invariant:
  assumes 
     "stable_from pre invar rely" and
     "Id \<subseteq> guar" and
     "annquin_valid {pre \<inter>  b , rely} ac1 \<sslash>invar{guar , post}" and
     "annquin_valid {pre \<inter> -b , rely} ac2 \<sslash>invar{guar , post}"
   shows "annquin_valid {pre , rely} (CondAnno b ac1 ac2) \<sslash> invar {guar, post} "
  using assms apply ( simp add: stable_from_def annquin_invar_def  )
  apply(mintro)
   apply (simp add: inf.commute inf_sup_aci(3))
  by (simp add: inf_commute inf_left_commute)

text "Single-branch conditionals"

theorem intro_CondAnno_SkipRight:
  assumes 
    "stable pre rely" and
    "stable post rely" and
     "Id \<subseteq> guar" and
     "anncom_spec_valid (pre \<inter>  b) rely guar post ac1" and
     "stable (pre \<inter> -b) rely" and
     "pre \<inter> -b \<subseteq> post"
shows "anncom_spec_valid pre rely guar post (Cond_Skip_Right b ac1)"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) intro_CondAnno intro_SkipAnno)

theorem intro_CondAnno_SkipRight_with_invariant:
  assumes 
    "stable_from pre invar rely" and
    "stable_from post invar rely" and
    "stable_from (pre \<inter> -b) invar rely" and
    "Id \<subseteq> guar" and
    "pre \<inter> -b \<inter> invar \<subseteq> post" and
    "annquin_valid {pre \<inter>  b, rely} ac1 \<sslash>invar{ guar , post}" 
shows "annquin_valid { pre , rely}  (Cond_Skip_Right b ac1) \<sslash> invar {guar,  post}"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) intro_CondAnno_with_invariant intro_SKIPa_with_invariant)

theorem intro_Cond_SkipRight_NoChange:
  assumes 
    "stable pre rely" and
     "Id \<subseteq> guar" and
     "{(pre \<inter>  b), rely} c { guar ,  pre}" 
   shows "{pre, rely} Cond b c SKIP {guar, pre}"
  apply(rule Cond)
  using assms(1) apply blast
  apply (simp add: assms(3))
  apply (metis assms(1) assms(2) inf.idem inf_commute inf_le2 rg_skip_named strengthen_pre)
  using assms(2) by blast

text "For the special case where the post and preconditions are identical,
such as inside an infinite loop."

theorem intro_CondAnno_SkipRight_NoChange:
  assumes 
      "stable pre rely" and
      "Id \<subseteq> guar" and
      "anncom_spec_valid (pre \<inter>  b) rely guar pre ac1" 
shows "anncom_spec_valid pre rely guar pre (CondAnno b ac1  SKIPa)"
  apply simp
  apply mintro
  apply (meson RG_Hoare.stable_def assms(1))
  apply (simp add: assms(2))
  apply (simp add: assms(3))
  by (meson assms(1) assms(2) equalityD2 inf_le1 rg_skip_named strengthen_pre)

theorem intro_CondAnno_SkipRight_NoChange_with_invariant:
  assumes 
    "stable_from pre invar rely" and
     "annquin_valid {(pre \<inter>  b), rely} ac1 \<sslash>invar{guar, pre}" 
   shows "annquin_valid { pre , rely}  (CondAnno b ac1  SKIPa) \<sslash> invar {guar, pre}"
  apply(simp only: annquin_invar_def annquin_simp add_invar.simps)
  apply(rule intro_CondAnno_SkipRight_NoChange)
  using assms(1) stable_to_stable_from_simp apply blast
  apply simp
  by (smt (verit, ccfv_SIG) Sigma_cong annquin_invar_def annquin_simp assms(2) inf_assoc inf_commute)

(*----------------------------------------------------------------------------*)
subsubsection While

theorem intro_WhileAnno:
 assumes "stable pre rely" and
     "stable post rely" and
     "Id \<subseteq> guar" and
     "pre \<inter> -b \<subseteq> post" and
     "pre \<inter>  b \<subseteq> b'" and
     "anncom_spec_valid (pre \<inter> b') rely guar pre ac"
shows "anncom_spec_valid pre rely guar post (WhileAnno b b' ac)"
  using assms by simp

theorem intro_WhileAnno_annquin:
 assumes "stable pre rely" and
     "stable post rely" and
     "Id \<subseteq> guar" and
     "pre \<inter> -b \<subseteq> post" and
     "pre \<inter>  b \<subseteq> b'" and
     "annquin_valid {(pre \<inter> b'), rely} ac { guar, pre}"
shows "annquin_valid {pre, rely}  (WhileAnno b b' ac) {guar, post}"
  using assms by simp

theorem intro_WhileAnno_with_invariant:
 assumes "stable_from pre invar rely" and
     "stable_from post invar rely" and
     "pre \<inter> -b \<inter> invar \<subseteq> post" and
     "pre \<inter>  b \<inter> invar \<subseteq> b'" and
     "annquin_valid {pre \<inter> b', rely} ac \<sslash> invar { guar , pre}"
shows "annquin_valid {pre , rely}  (WhileAnno b b' ac) \<sslash> invar {guar, post}"
  using assms apply( simp add: stable_from_def annquin_invar_def )
  apply mintro
  using assms apply auto[1]
  apply blast
  apply blast
  by (simp add: Int_left_commute inf_commute)

text SpinLoops

theorem intro_Spinloop:
  assumes 
     "stable pre rely" and
     "stable post rely" and
     "Id \<subseteq> guar" and
     "pre \<inter> -b \<subseteq> post" 
shows "anncom_spec_valid pre rely guar post (Spinloop b)"
  using assms apply auto
  by (meson assms(1) equalityD2 rg_skip_named)
  
theorem intro_Spinloop_with_invariant:
  assumes 
     "stable_from pre invar rely" and
     "stable_from post invar rely" and
     "pre \<inter> -b \<inter> invar \<subseteq> post" 
   shows "annquin_valid { pre, rely} (Spinloop b) \<sslash> invar { guar, post}"
  using assms apply ( simp only:   annquin_invar_def annquin_simp add_invar.simps)
  apply(rule intro_Spinloop)
  using assms apply (auto simp add: stable_from_def   )
  done

subsubsection "Strengthen post"

lemma Basic_sat_implies_post_and_guar: 
   "\<turnstile> Basic f sat [ pre, rely, guar, post] \<Longrightarrow>
 pre \<subseteq> {s. f s \<in> post} \<and> {(s,t). s \<in> pre \<and> (t=f s \<or> t=s)} \<subseteq> guar 
             "
  apply(induct "Basic f" pre rely guar post arbitrary: f rule: rghoare.induct)
   apply blast
  apply mintro
     apply blast
  apply auto[1]
  apply blast
  apply blast
  done

(*
In the following note that "stable q r" is required here, but in general rule Conseq.
This is because of the way induction is used in PN, versus the function style we have
adopted.
*)
lemma anncom_spec_strengthen_post: 
  assumes "anncom_spec_valid p r g q' c"
    and "q' \<subseteq> q" 
    and "stable q r"
  shows "anncom_spec_valid p r g q c"
  using assms apply(induct c arbitrary: p r g q q')
  apply auto[1]
         apply (simp add: weaken_post)
  apply( simp add: ) apply(simp add: subset_iff)
  apply auto[1]
      apply auto[1]


  apply auto[1]
  apply auto[1]
   apply auto[1]

  apply simp
  by (metis (no_types, lifting) Int_mono equalityD2 pair_in_Id_conv)

lemma strengthen_post_with_invariant: 
  assumes  "q' \<inter> I \<subseteq> q" 
and "stable_from q I r"
and "annquin_valid {p, r} c \<sslash>I {g, q'}"

shows "annquin_valid {p, r} c \<sslash>I {g, q}"
  by (smt (verit, best) Int_assoc Int_lower2 anncom_spec_strengthen_post annquin_invar_def annquin_simp assms(1) assms(2) assms(3) inf.absorb_iff1 stable_to_stable_from_simp)



  text Forever

theorem intro_Forever:
  assumes 
    stable_pre: "stable p r"
    and id_guar: "Id \<subseteq> g"
    and "annquin_valid {p,r}c{g,p}"
  shows "annquin_valid {p,r} FOREVER c {g, p}"
  apply (simp add: Forever_def)
  apply(intro conjI)
  apply (meson RG_Hoare.stable_def assms(1))
  apply (simp add: assms(2))
  using annquin_simp assms(3) by blast

theorem intro_Forever_with_invariant:
  assumes 
    stable_pre: "stable_from p invar r"
    and "annquin_valid {p,r}c \<sslash> invar {g,p}"
  shows "annquin_valid {p,r} FOREVER c \<sslash> invar {g, p}"
  apply (simp add: annquin_invar_def  Forever_def)
  apply(intro conjI)
  apply (meson RG_Hoare.stable_def assms(1))
   apply (meson stable_from_def stable_pre)
  using assms(2)
  by (simp add: annquin_invar_def)

theorem intro_Forever_no_post_with_invariant:
  assumes 
    stable_pre: "stable_from p invar r"
    and "annquin_valid {p,r}c \<sslash> invar {g,p}"
  shows "annquin_valid {p,r} FOREVER c \<sslash> invar {g, {}}"
  apply (simp add: annquin_invar_def  Forever_def)
  apply(intro conjI)
  apply (meson RG_Hoare.stable_def assms(1))
  apply (meson stable_from_def stable_pre)
  using assms(2)
  by (simp add: annquin_invar_def)


theorem intro_Forever_strengthened_post_with_invariant:
  assumes 
    stable_pre: "stable_from p invar r"
    and stable_post: "stable_from q invar r"

    and "p \<inter> invar \<subseteq> q"
    and "annquin_valid {p,r}c \<sslash> invar {g,p}"

shows "annquin_valid {p,r} FOREVER c \<sslash> invar {g, q}"
  apply(rule strengthen_post_with_invariant[OF assms(3) assms(2) ])
  by(rule intro_Forever_with_invariant[OF assms(1) assms(4)])


text When

theorem intro_When:
  assumes 
 stable_pre: "stable p r" and
 id_guar: "Id \<subseteq> g" and
 "annquin_valid {p \<inter> b,r}c{g,p}"
shows "annquin_valid {p,r} 
      FOREVER (CondAnno b c SKIPa) 
      {g, p}"
  apply(rule intro_Forever)
  using stable_pre apply blast
  apply (simp add: id_guar)
  by (metis annquin_simp assms(3) id_guar intro_CondAnno_SkipRight_NoChange stable_pre)

theorem intro_When_with_invariant:
  assumes 
 stable_pre: "stable_from p invar r" and
 "annquin_valid {p \<inter> b,r}c \<sslash> invar{g,p}"
shows "annquin_valid {p,r} 
      FOREVER (CondAnno b c SKIPa) \<sslash> invar
      {g, p}"
  by (metis assms(2)  intro_CondAnno_SkipRight_NoChange_with_invariant intro_Forever_with_invariant stable_pre)

(*----------------------------------------------------------------------------*)
subsubsection AwaitAnno

theorem intro_AwaitAnno:
  assumes "stable pre rely" and
     "stable post rely" and
     "\<And>s. anncom_spec_valid (pre \<inter> b \<inter> {s}) Id UNIV ({s'. (s, s') \<in> guar} \<inter> post) ac"
shows "anncom_spec_valid pre rely guar post (AwaitAnno b ac)"
  using assms by simp

theorem intro_AwaitAnno_with_invariant:
  assumes 
     "stable_from pre invar rely" and
     "stable_from post invar rely" and
     "\<And>s. annquin_valid { (pre \<inter> invar \<inter> b \<inter> {s} ), Id} 
        add_invar invar ac
        { UNIV , {s'. (s, s') \<in> (Id \<union> Restr guar invar)} \<inter> post \<inter> invar} "
shows "annquin_valid { pre , rely} (AwaitAnno b ac) \<sslash> invar { guar,  post} "
  using assms apply (auto simp add: stable_from_def  annquin_invar_def )
  by (simp add: inf_assoc )

(*============================================================================*)
subsection "Generalised sequential block effects"

text "Generalise simple sequential blocks inside Awaits into a single Basic proof"

text "Define the shape of simple code for which we can easily derive sequential semantics"
fun simple_sequential_code:: "'a com \<Rightarrow> bool" where
  "simple_sequential_code (Basic s) = True"
| "simple_sequential_code (c1 ;; c2) = ((simple_sequential_code c1) \<and> (simple_sequential_code c2))"
| "simple_sequential_code (Cond b c1 c2) = ((simple_sequential_code c1) \<and> (simple_sequential_code c2))"
| "simple_sequential_code c = False"

fun sequential_semantics:: "'a com \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "sequential_semantics (Basic s) = s"
| "sequential_semantics (c1 ;; c2) = (sequential_semantics c2) o (sequential_semantics c1)"
| "sequential_semantics (Cond b c1 c2) = (\<lambda>s. 
    (if s \<in> b then 
      (sequential_semantics c1) s 
    else 
      (sequential_semantics c2) s))"
| "sequential_semantics c = id"

text "Link sequential semantics to RG via a rely of Id and guar of UNIV"

(*
theorem under_Id_gives_sequential:
  assumes "simple_sequential_code c"
      shows "annquin_valid ({p, Id}  NoAnno c {UNIV, (sequential_semantics c) ` p}) " 
  using assms apply(induct c arbitrary:  p  )
  apply auto
   apply (metis Seq image_image)
  apply (rule Cond)
  apply auto
  apply (meson sup_ge1 weaken_post)
  by (metis Compl_eq Un_upper2 weaken_post)
*)
theorem Basic_compare_guar_location:
  shows "annquin_valid {p , Id} (BasicAnno f) {g, q} \<Longrightarrow>
         sequential_semantics c = f \<Longrightarrow>
         simple_sequential_code c  \<Longrightarrow>
              annquin_valid ({p, Id}  NoAnno c {UNIV, q}) " 
  apply(induct c arbitrary: f p  g q)
  apply simp
  apply mintro
      apply (simp add: rg_basic_named)
     apply simp
  subgoal for c1 c2 f p g q
    apply(rule Seq[where mid = "(sequential_semantics c1) ` p"])
    apply(simp add: subset_iff)
     apply (smt (verit) UNIV_I image_eqI mem_Collect_eq subsetI)
    apply(auto simp add: subset_iff)
  proof(goal_cases)
    case 1
    then show ?case
      apply(rule_tac 1(2)[of "sequential_semantics c1 `p" UNIV "sequential_semantics c2"  q])
      apply mintro
      apply blast
      apply blast
      using 1(2)[of "sequential_semantics c1 `p" UNIV "sequential_semantics c1"  q]
       apply auto
      done
  qed
    apply simp
  apply(rule Cond; (auto simp add: subset_iff))
  apply (metis Int_iff UNIV_I)
    apply (metis Compl_iff Int_iff UNIV_I)
   apply simp_all
  done


theorem Await_sequential_effect_imp:
  assumes "simple_sequential_code c"  and 
    "annquin_valid  {p , Id} (BasicAnno (sequential_semantics c)) {g, q}" and 
    "gq = {s'. (s, s') \<in> g} \<inter> q"
  shows "annquin_valid ({p \<inter> {s}, Id} NoAnno  c {UNIV, gq}) " 
  apply(rule Basic_compare_guar_location)
  using assms apply auto
  done

theorem Await_sequential_effect_imp_com:
  assumes "simple_sequential_code c"
    and "annquin_valid  {p , Id} (BasicAnno (sequential_semantics c)) {g, q}"
    and "gq = {s'. (s, s') \<in> g} \<inter> q"
  shows " ({p \<inter> {s}, Id}   c {UNIV, gq}) " 
  apply (rule anncom_spec_valid_sound_NoAnno)
  using Await_sequential_effect_imp[where c = c and gq = gq and p = p and s = s]
  apply(simp only: annquin_simp)
  using annquin_simp assms(1) assms(2) assms(3) by blast

theorem Atomic_to_Basic_intro:
  assumes "simple_sequential_code c"
    and "annquin_valid  {p , r} (BasicAnno (sequential_semantics c)) {g, q}"
  shows "annquin_valid ({p , r} Atomic  c {g, q}) " 
   apply auto
  apply mintro
  using assms(2) apply auto[1]
  using assms(2) apply auto[1]
  subgoal for s
  apply(rule Await_sequential_effect_imp_com[where gq = "{s'. (s, s') \<in> g} \<inter> q" and g = g and q = q])
  apply (simp add: assms(1))
    using assms(2) apply auto[1]
    by simp
  done

theorem Atomic_to_Basic_intro_spec_valid:
  assumes "simple_sequential_code c"
    and "anncom_spec_valid  p r g q (BasicAnno (sequential_semantics c)) "
  shows "anncom_spec_valid p  r g q (Atomic  c ) " 
   apply auto
  apply mintro
  using assms(2) apply auto[1]
  using assms(2) apply auto[1]
  subgoal for s
  apply(rule Await_sequential_effect_imp_com[where gq = "{s'. (s, s') \<in> g} \<inter> q" and g = g and q = q])
  apply (simp add: assms(1))
    using assms(2) apply auto[1]
    by simp
  done


text "The desired rule: reasoning about an atomic block can be reduced to reasoning about
a Basic using the sequential semantics directly"
theorem Atomic_to_Basic_intro_with_invariant:
  assumes "simple_sequential_code c"
    and "annquin_valid  {p , r} (BasicAnno (sequential_semantics c)) \<sslash> invar {g, q}"
  shows "annquin_valid ({p , r} Atomic  c \<sslash>invar{g, q}) "
  by (metis (mono_tags, lifting) Atomic_to_Basic_intro add_invar.simps(1) add_invar.simps(2) add_invar.simps(8) annquin_invar_def assms(1) assms(2))

(*============================================================================*)
subsection \<open>Main Automated Method\<close>

text \<open>The collection of introduction-rules.\<close>

lemmas anncom_intros_structural = 
  intro_SKIPa_with_invariant

  intro_SkipAnno
  intro_WeakPre_with_invariant
  intro_StrongPost_with_invariant

  intro_WeakPre
  intro_StrongPost
  intro_SeqAnno_with_invariant
  intro_SeqAnno

  intro_CondAnno
  intro_CondAnno_annquin
  intro_CondAnno_with_invariant

  intro_Spinloop_with_invariant
  intro_Spinloop

  intro_When_with_invariant
  intro_Forever_with_invariant
intro_Forever_no_post_with_invariant
  intro_Forever_strengthened_post_with_invariant
  intro_Forever
  
  intro_WhileAnno_with_invariant
  intro_WhileAnno_annquin
  intro_WhileAnno
  Atomic_to_Basic_intro_with_invariant
  Atomic_to_Basic_intro_spec_valid
  Atomic_to_Basic_intro
  intro_AwaitAnno
  
  intro_CondAnno_SkipRight_with_invariant

  valid_3way_parallel_composition_with_invariant
  valid_multipar_explicit_with_invariant
  valid_multipar_explicit2
  valid_multipar_explicit

lemmas anncom_intros =
  anncom_intros_structural
  (*intro_Basic_to_BasicAnno_with_invariant*)
  intro_NoAnno_Basic
  intro_NoAnno_Basic_annquin
  intro_NoAnno_Basic_with_invariant
  intro_BasicAnno_with_invariant

text \<open>The main methods; useful introduction-rules for the RG context.\<close>

method blast4 = blast 4
method blast10 = blast 10

method try_blast4 uses helpers simps = 
  ((simp only: simps)? ; mintro? ; clarsimp? ; use helpers in blast4)?

method try_blast8 uses simps = 
  ((simp add: simps) ; mintro? ; blast 8)?

lemmas rg_foundation_simps =
  stable_from_def 
   
  subset_iff

method rg_foundation_simp uses simps = 
  simp only: rg_foundation_simps simps

method simp_divide_blast uses simps useful =
  ((use useful in rg_foundation_simp )? ; (simp add: simps rg_foundation_simps)?; mintro? ; (use [[simp_depth_limit = 4]] in simp)? ;  try_blast4)

method simp_divide_tryblast uses simps useful =
  ((use useful in rg_foundation_simp )? ; (simp only: simps)?; mintro? ; (use [[simp_depth_limit = 4]] in simp)? ;  blast4)?
(*method expand_annotations = 
  (simp only:  basic_to_basic_anno_syntax.simps)?
*)

method intro_rg_proof_obs uses extras = 
  intro 
    extras
    valid_3way_parallel_composition_with_invariant
    valid_multipar_explicit_with_invariant
    valid_multipar_explicit

    anncom_intros  
    invariant_int_subset_intro  
    (*pred_reln_conditionally_Restr_intro*)
    stable_from_int_intro 

method anncom_intro uses more_intros = 
  (intro_rg_proof_obs extras: more_intros    ) 

method decompose_rg uses intros =
   (intro 
    valid_3way_parallel_composition_with_invariant
    valid_multipar_explicit_with_invariant
    valid_multipar_explicit
  anncom_intros_structural)

method decompose_and_discharge uses simps helpers intros =
  ((((anncom_intro more_intros: intros)? 
        , tactic distinct_subgoals_tac)
  ;
  ((simp add:  )? ; (intro allI impI conjI  ballI intros)? ; simp? ; ((simp add: subset_iff)? ; blast4)?)) 
          , tactic distinct_subgoals_tac) 
  ;
  (try_blast4 helpers: helpers simps: stable_from_def simps subset_iff )

method expand_and_blast uses main_def simps =
  simp add: main_def ; mintro? ; try_blast4 simps: simps

method blast_invariant uses simps =
  expand_and_blast main_def:  simps: simps

end
