(* Title:       	 Syntax Extension for Rely-Guarantee
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

section \<open>Rely-Guarantee (RG) Syntax Extensions\<close>

text \<open>The core extensions to the built-in RG library:
improved syntax of RG sentences in the quintuple- and 
keyword-styles, with data-invariants.

Also: subgoal-generating methods for RG inference-rules that work
with the structured proof-language, Isar.\<close>

theory RG_Syntax_Extensions

imports
  "HOL-Hoare_Parallel.RG_Syntax"
  "HOL-Eisbach.Eisbach"

begin

text \<open>We begin with some basic notions that are used later on.\<close>

text \<open>Notation for forward function-composition:
defined in the built-in @{text \<open>Fun.thy\<close>} but disabled at the 
end of that theory.
%
This operator is useful for modelling atomic primitives such as Swap
and Fetch-And-Increment, and also useful when coupling concrete- and
auxiliary-variable instructions.\<close>

notation fcomp (infixl "\<circ>>" 60)

lemmas definitions [simp] =
  stable_def Pre_def Rely_def Guar_def Post_def Com_def

text \<open>In applications, guarantee-relations often stipulates that Thread
@{text i} should ``preserve the rely-relations of all other threads''.
This pattern is supported by the following higher-order function, where 
@{text j} ranges through all the threads that are not @{text i}.\<close>

abbreviation for_others :: "('index \<Rightarrow> 'state rel) \<Rightarrow> 'index \<Rightarrow> 'state rel" where
  "for_others R i \<equiv> \<Inter> j \<in> -{i}. R j"

text \<open>Relies and guarantees often state that certain variables remain 
unchanged. We support this pattern with the following syntactic sugars.\<close>

abbreviation record_id :: "('record \<Rightarrow> 'field) \<Rightarrow> 'record rel"
  ("id'(_')" [75] 74) where
  "id(c) \<equiv> \<lbrace> \<ordfeminine>c = \<ordmasculine>c \<rbrace>"

abbreviation record_ids :: "('record \<Rightarrow> 'field) set \<Rightarrow> 'record rel"
  ("ids'(_')" [75] 74) where
  "ids(cs) \<equiv> \<Inter> c \<in> cs. id(c)"

abbreviation record_id_indexed ::
  "('record \<Rightarrow> 'index \<Rightarrow> 'field) \<Rightarrow> 'index \<Rightarrow> 'record rel"
  ("id'( _ @ _ ')") where
  "id(c @ self) \<equiv> \<lbrace> \<ordmasculine>c self = \<ordfeminine>c self \<rbrace>"

abbreviation record_ids_indexed ::
  "('record \<Rightarrow> 'index \<Rightarrow> 'field) set \<Rightarrow> 'index \<Rightarrow> 'record rel"
  ("ids'( _ @ _ ')") where
  "ids(cs @ self) \<equiv> \<Inter> c \<in> cs. id(c @ self)"

text \<open>The following simple method performs an optional simplification-step, 
and then tries to apply one of the RG rules, before attempting to discharge 
each subgoal using @{text force}.
%
This method works well on simple RG sentences.\<close>

method method_rg_try_each = 
  (clarsimp | simp)?,
  ( rule Basic | rule Seq | rule Cond | rule While 
  | rule Await | rule Conseq | rule Parallel);
   force+

(* The "clarsimp" was added due to "Example2_param",
   where one of the cases could not be handled by "simp". *)

(*============================================================================*)
subsection \<open>Lifting of Invariants\<close>

text \<open>There are different ways to combine the invariant with the rely
or guarantee, as long as the invariant is preserved.
%
Here, a rely- or guarantee-relation @{term R} is combined with the 
invariant @{term I} into @{term \<open>{(s,s'). (s \<in> I \<longrightarrow> s' \<in> I) \<and> R}\<close>}.\<close>

definition pred_to_rel :: "'a set \<Rightarrow> 'a rel" where
  "pred_to_rel P \<equiv> {(s,s') . s \<in> P \<longrightarrow> s' \<in> P}"

definition invar_and_guar :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "invar_and_guar I G \<equiv> G \<inter> pred_to_rel I" 

lemmas simp_defs [simp] = pred_to_rel_def invar_and_guar_def

(*============================================================================*)
subsection \<open>RG Sentences\<close>

text \<open>The quintuple-style of RG sentences.\<close>
abbreviation rg_quint ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a com \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  ("{_,_} _ {_,_}") where
  "{P, R} C {G, Q} \<equiv> \<turnstile> C sat [P, R, G, Q]"

text \<open>Quintuples with invariants.\<close>

abbreviation rg_quint_invar :: 
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a com \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" 
  ("{_,_} _ \<sslash> _ {_,_}") where
  "{P, R} C \<sslash> I {G, Q} \<equiv> \<turnstile> C sat [
    P \<inter> I, 
    R \<inter> pred_to_rel I, 
    invar_and_guar I G, 
    Q \<inter> I]"

text \<open>The keyword-style of RG sentences.\<close>

abbreviation rg_keyword ::
  "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a com \<Rightarrow> 'a set \<Rightarrow> bool"
  ("rely:_ guar:_ code: {_} _ {_}") where
  "rg_keyword R G P C Q \<equiv> \<turnstile> C sat [P, R, G, Q]"

text \<open>Keyword-style RG sentences with invariants.\<close>

abbreviation rg_keyword_invar ::
  "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a com \<Rightarrow> 'a set \<Rightarrow> bool"
  ("rely:_ guar:_ inv:_ code: {_} _ {_}") where
  "rg_keyword_invar R G I P C Q \<equiv> \<turnstile> C sat [
    P \<inter> I, 
    R \<inter> pred_to_rel I, 
    invar_and_guar I G, 
    Q \<inter> I]"

(*============================================================================*)
subsection \<open>RG Subgoal-Generating Methods\<close>

text \<open>As in Floyd-Hoare logic, in RG we can strengthen (make smaller) the 
precondition and weaken (make larger) the postcondition without affecting the
validity of an RG sentence.\<close>

theorem strengthen_pre:
  assumes "P' \<subseteq> P"
      and "\<turnstile> c sat [P,  R, G, Q]"
    shows "\<turnstile> c sat [P', R, G, Q]"
  using assms Conseq by blast

theorem weaken_post:
  assumes "Q \<subseteq> Q'"
      and "\<turnstile> c sat [P, R, G, Q ]"
    shows "\<turnstile> c sat [P, R, G, Q']"
  using assms Conseq by blast

text \<open>We then develop subgoal-generating methods for various instruction 
types and patterns, to be used in conjunction with the Isar proof-language.\<close>

(*----------------------------------------------------------------------------*)
subsubsection \<open>Basic\<close>

text \<open>A @{text Basic} instruction wraps a state-transformation function.\<close>

theorem rg_basic_named[intro]:
  assumes "stable P R"
      and "stable Q R"
      and "\<forall>s. s \<in> P \<longrightarrow> (s, s) \<in> G"
      and "\<forall>s. s \<in> P \<longrightarrow> (s, f s) \<in> G"
      and "P \<subseteq> \<lbrace> \<acute>f \<in> Q \<rbrace>" 
    shows "{P, R} Basic f {G, Q}"
  using assms apply -
  by (rule Basic; fastforce)

method method_basic =
  rule rg_basic_named,
  goal_cases stable_pre stable_post guar_id establish_guar establish_post

text \<open>The \emph{skip} command is a @{text Basic} instruction whose function is
the identity.\<close>

theorem rg_skip_named: 
  assumes "stable P R"
      and "stable Q R"
      and "Id \<subseteq> G"
      and "P \<subseteq> Q"
    shows "{P, R} SKIP {G, Q}"
  using assms by force

method method_skip =
  rule rg_skip_named,
  goal_cases stab_pre stab_post guar_id est_post

text \<open>An alternative version with an invariant subgoal.\<close>

theorem rg_basic_inv[intro]:
  assumes "stable (P \<inter> I) (R \<inter> pred_to_rel I)"
      and "stable (Q \<inter> I) (R \<inter> pred_to_rel I)"
      and "\<forall>s. s \<in> P \<inter> I \<longrightarrow> (s, s) \<in> G"
      and "\<forall>s. s \<in> P \<inter> I \<longrightarrow> f s \<in> I"
      and "\<forall>s. s \<in> P \<inter> I \<longrightarrow> f s \<in> Q"
      and "\<forall>s. s \<in> P \<inter> I \<longrightarrow> (s, f s) \<in> G"
    shows "\<turnstile> (Basic f) sat [
      P \<inter> I, 
      R \<inter> pred_to_rel I, 
      invar_and_guar I G, 
      Q \<inter> I]"
  using assms apply -
  by (method_basic; fastforce)

method method_basic_inv = rule rg_basic_inv,
  goal_cases stab_pre stab_post id_guar est_inv est_post est_guar

(*----------------------------------------------------------------------------*)
subsubsection \<open>Looping constructs\<close>

theorem rg_general_loop_named[intro]:
  assumes "stable P R"
      and "stable Q R"
      and "Id \<subseteq> G"
      and "P \<inter> -b \<subseteq> Q"
      and "{P \<inter> b, R} c {G, P}"
    shows "{P, R} While b c {G, Q}"
  using assms apply -
  by (rule While; fastforce)

method method_loop =
  rule rg_general_loop_named,
  goal_cases stable_pre stable_post id_guar loop_exit loop_body

text \<open>A similar version but with the @{text loop_body} subgoal having a
weakend precondition.\<close>

theorem rg_general_loop_no_guard[intro]:
  assumes "stable P R"
      and "stable Q R"
      and "Id \<subseteq> G"
      and "P \<inter> -b \<subseteq> Q"
      and "{P, R} c {G, P}"
    shows "{P, R} While b c {G, Q}"
  apply(rule rg_general_loop_named)
  by (fastforce intro!: assms Int_lower1 intro: strengthen_pre)+

method method_loop_no_guard = 
  rule rg_general_loop_no_guard,
  goal_cases stab_pre stab_post guar_id loop_exit loop_body

text \<open>A \emph{spinloop} is a loop with an empty body. Such a loop repeatedly
checks a property, and is a key construct in mutual exclusion algorithms.\<close>

theorem rg_spinloop_named[intro]:
  assumes "stable P R"
      and "stable Q R"
      and "Id \<subseteq> G"
      and "P \<inter> -b \<subseteq> Q"
    shows "{P, R} While b SKIP {G, Q}"
  using assms
  by (fastforce simp: rg_general_loop_no_guard rg_skip_named)


method method_spinloop = 
  rule rg_spinloop_named,
  goal_cases stable_pre stable_post guar_id est_post

theorem rg_infinite_loop:
  assumes "stable P R"
      and "Id \<subseteq> G"
      and "{P, R} C {G, P}"
    shows "{P, R} While UNIV C {G, Q}"
proof -
  have "{P, R} While UNIV C {G, {}}"
    using assms by (fastforce simp: rg_general_loop_no_guard)
  thus ?thesis
    using weaken_post by fastforce
qed

method method_infinite_loop =
  rule rg_infinite_loop,
  goal_cases stable_pre guar_id loop_body,
  clarsimp+

theorem rg_infinite_loop_syntax:
  assumes "stable P R"
      and "Id \<subseteq> G"
      and "{P, R} C {G, P}"
    shows "{P, R} WHILE True DO C OD {G, Q}"
  using assms by (fastforce simp: rg_infinite_loop)

method method_infinite_loop_syntax =
  rule rg_infinite_loop_syntax,
  goal_cases stable_pre guar_id loop_body

text \<open>A \emph{repeat-loop} encodes the pattern where the loop body is executed 
before the first evaluation of the guard.\<close>

theorem rg_repeat_loop[intro]:
  assumes "stable P R"
      and "stable Q R"
      and "Id \<subseteq> G"
      and "P \<inter> b \<subseteq> Q"
      and loop_body: "{P, R} C {G, P}"
    shows "{P, R} C ;; While (-b) C {G, Q}"
  using assms apply -
  apply (rule Seq)
   apply (force intro: loop_body)
  by (method_loop_no_guard; fastforce)

method method_repeat_loop =
  rule rg_repeat_loop,
  goal_cases stab_pre stab_post guar_id loop_exit loop_body

text \<open>When reasoning about repeat-loops, we may need information from @{text P} 
to determine whether we reach the postcondition. In this case we can use the 
following form, which introduces a mid-state.\<close>

theorem rg_repeat_loop_mid[intro]:
  assumes stab_pre:  "stable (P \<inter> M) R"
      and stab_post: "stable Q R"
      and guar_id:   "Id \<subseteq> G"
      and loop_exit: "P \<inter> M \<inter> b \<subseteq> Q"
      and loop_body: "{P, R} C {G, P \<inter> M}"
    shows "{P, R} C ;; While (-b) C {G, Q}"
 using assms apply -
  apply (rule Seq)
   apply (fast intro: loop_body)
  by (method_loop_no_guard; fast intro: loop_body strengthen_pre)

method method_repeat_loop_mid =
  rule rg_repeat_loop_mid,
  goal_cases stab_pre stab_post guar_id loop_exit loop_body

text \<open>We define dedicated syntax for the repeat-loop pattern.\<close>

definition Repeat :: "'a com \<Rightarrow> 'a bexp \<Rightarrow> 'a com" where
  "Repeat c b \<equiv> c ;; While (-b) c"

syntax "_Repeat" :: "'a com \<Rightarrow> 'a bexp \<Rightarrow> 'a com"  ("(0REPEAT _ /UNTIL _ /END)"  [0, 0] 61)
translations "REPEAT c UNTIL b END" \<rightharpoonup> "CONST Repeat c \<lbrace>b\<rbrace>"

theorem rg_repeat_loop_def[intro]:
  assumes stab_pre:  "stable P R"
      and stab_post: "stable Q R"
      and guar_id:   "Id \<subseteq> G"
      and loop_exit: "P \<inter> b \<subseteq> Q"
      and loop_body: "{P, R} C {G, P}"
    shows "{P, R} Repeat C b {G, Q}"
  using assms 
  by (fastforce simp: Repeat_def rg_repeat_loop)

method method_repeat_loop_def =
  rule rg_repeat_loop_def,
  goal_cases stab_pre stab_post guar_id loop_exit loop_body

(*----------------------------------------------------------------------------*)
subsubsection \<open>Conditionals\<close>

text \<open>We first cover conditional-statements with or without the else-branch.\<close>

theorem rg_cond_named[intro]:
  assumes stab_pre:  "stable P R"
      and stab_post: "stable Q R"
      and guar_id:   "Id \<subseteq> G"
      and then_br:   "{P \<inter>  b, R} c1 {G, Q}"
      and else_br:   "{P \<inter> -b, R} c2 {G, Q}"
    shows "{P, R} Cond b c1 c2 {G, Q}"
  using assms apply -
  by (rule Cond; fastforce)

theorem rg_cond2_named[intro]:
  assumes stab_pre:  "stable P R"
      and stab_post: "stable Q R"
      and guar_id:   "Id \<subseteq> G"
      and then_br:   "{P \<inter>  b, R} c1 {G, Q}"
      and else_br:   "P \<inter> -b \<subseteq> Q"
    shows "{P, R} Cond b c1 SKIP {G, Q}"
  using assms apply -
  by (rule rg_cond_named; fastforce simp: rg_skip_named strengthen_pre)
 
method method_cond =
  (rule rg_cond2_named | rule rg_cond_named),
  goal_cases stab_pre stab_post guar_id then_br else_br

text \<open>Variants without the stable-post subgoal.\<close>

theorem rg_cond_no_post[intro]:
  assumes stable_pre: "stable P R"
      and guar_id: "Id \<subseteq> G"
      and then_br: "{P \<inter> b, R} c1 {G, Q}"
      and else_br: "{P \<inter> -b, R} c2 {G, Q}"
    shows "{P, R} Cond b c1 c2 {G, Q}"
  using assms by (fastforce simp: Cond subset_iff)

theorem rg_cond_no_guard_no_post[intro]:
  assumes stable_pre: "stable P R"
      and guar_id: "Id \<subseteq> G"
      and then_br: "{P, R} c1 {G, Q}"
      and else_br: "{P, R} c2 {G, Q}"
    shows "{P, R} Cond b c1 c2 {G, Q}"
  using assms apply -
  by (rule Cond; fastforce intro: strengthen_pre)

method method_cond_no_post =
  (rule rg_cond_no_post | rule rg_cond_no_guard_no_post),
  goal_cases stab_pre guar_id then_br else_br

(*============================================================================*)
subsection \<open>Parallel Compositions\<close>

text \<open>We now turn to the parallel composition, and cover several variants,
from the \emph{binary} parallel composition of two commands, to the
\emph{multi-parallel} composition of an indexed list of commands.
For each variant, we define the syntax and devise the subgoal-generating methods.\<close>

(*----------------------------------------------------------------------------*)
subsubsection \<open>Binary Parallel\<close>

text \<open>The syntax of binary parallel composition, without and with invariant.\<close>

abbreviation binary_parallel :: 
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" 
 ("{_, _}  _ \<parallel> _  {_, _}") where
  "{P, R} C1 \<parallel> C2 {G, Q} \<equiv>
    \<exists> P1 P2 R1 R2 G1 G2 Q1 Q2. 
      \<turnstile> COBEGIN 
          (C1, P1, R1, G1, Q1) 
          \<parallel> 
          (C2, P2, R2, G2, Q2) 
      COEND SAT [P, R, G, Q]"

abbreviation binary_parallel_invar :: 
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" 
 ("{_, _}  _ \<parallel>  _ \<sslash> _ {_, _}") where
  "{P, R} C1 \<parallel> C2 \<sslash> I {G, Q} \<equiv>
    \<exists> P1 P2 R1 R2 G1 G2 Q1 Q2. 
      \<turnstile> COBEGIN 
          (C1, P1, R1, G1, Q1) 
          \<parallel> 
          (C2, P2, R2, G2, Q2) 
      COEND SAT [P \<inter> I, R \<inter> pred_to_rel I, invar_and_guar I G, Q \<inter> I]"

(*----------------------------------------------------------------------------*)
text \<open>Some helper lemmas for later.\<close>

lemma simp_all_2:
  "(\<forall> i < Suc (Suc 0). P i) \<longleftrightarrow> P 0 \<and> P 1"
  by (fastforce simp: less_Suc_eq)

lemma simp_gen_Un_2:
  "(\<Union> x \<in> \<lbrace>\<acute>(<) (Suc (Suc 0)) \<rbrace>. S x) = S 0 \<union> S 1"
  by (fastforce simp: less_Suc_eq)

lemma simp_gen_Un_2_not0:
  "(\<Union> x \<in> \<lbrace>\<acute>(<) (Suc (Suc 0)) \<and> \<acute>(\<noteq>) (Suc 0) \<rbrace>. S x) = S 0"
  by (fastforce simp: less_Suc_eq)

lemma simp_gen_Int_2:
  "(\<Inter> x \<in> \<lbrace>\<acute>(<) (Suc (Suc 0)) \<rbrace>. S x) = S 0 \<inter> S 1"
  by (fastforce simp: less_Suc_eq)

theorem rg_binary_parallel:
  assumes "{P1, R1} (C1::'a com) {G1, Q1}"
      and "{P2, R2} (C2::'a com) {G2, Q2}"
      and "G1 \<subseteq> R2"
      and "G2 \<subseteq> R1"
      and "P \<subseteq> P1 \<inter> P2"
      and "R \<subseteq> R1 \<inter> R2"
      and "G1 \<union> G2 \<subseteq> G"
      and "Q1 \<inter> Q2 \<subseteq> Q" 
    shows "\<turnstile> COBEGIN 
      (C1, P1, R1, G1, Q1) 
       \<parallel> 
      (C2, P2, R2, G2, Q2) 
      COEND SAT [P, R, G, Q]"
  using assms apply -
  apply (rule Parallel)
  by (simp_all add: simp_all_2 simp_gen_Un_2 simp_gen_Int_2 simp_gen_Un_2_not0)

theorem rg_binary_parallel_exists: 
  assumes "{P1, R1} (C1::'a com) {G1, Q1}"
      and "{P2, R2} (C2::'a com) {G2, Q2}"
      and "G1 \<subseteq> R2"
      and "G2 \<subseteq> R1"
      and "P \<subseteq> P1 \<inter> P2"
      and "R \<subseteq> R1 \<inter> R2"
      and "G1 \<union> G2 \<subseteq> G"
      and "Q1 \<inter> Q2 \<subseteq> Q" 
    shows "{P, R} C1 \<parallel> C2 {G, Q}"
  by (metis assms rg_binary_parallel)

theorem rg_binary_parallel_invar_conseq: 
  assumes C1: "{P1, R1} (C1::'a com) \<sslash> I {G1, Q1}"
      and C2: "{P2, R2} (C2::'a com) \<sslash> I {G2, Q2}"
      and "G1 \<subseteq> R2"
      and "G2 \<subseteq> R1"
      and "P \<subseteq> P1 \<inter> P2"
      and "R \<subseteq> R1 \<inter> R2"
      and "Q1 \<inter> Q2 \<subseteq> Q"
      and "G1 \<union> G2 \<subseteq> G"
    shows "{P, R} C1 \<parallel> C2 \<sslash> I {G, Q}"
  using assms apply -
  apply (rule rg_binary_parallel_exists)
  by force+

(*============================================================================*)
subsubsection \<open>Multi-Parallel\<close>

text \<open>The syntax of multi-parallel, without and with invariants.\<close>

syntax multi_parallel ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> idt \<Rightarrow> nat \<Rightarrow>
   (nat \<Rightarrow> 'a set) \<Rightarrow> (nat \<Rightarrow> 'a rel) \<Rightarrow>
   (nat \<Rightarrow> 'a com) \<Rightarrow>
   (nat \<Rightarrow> 'a rel) \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow>
   'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  ("global'_init: _ global'_rely: _ \<parallel>  _ < _ @ {_,_} _ {_,_} global'_guar: _ global'_post: _") 

translations 
  "global_init: Init global_rely: RR \<parallel> i < N @
   {P,R} c {G,Q} global_guar: GG global_post: QQ"
  \<rightharpoonup> "\<turnstile> COBEGIN SCHEME [0 \<le> i < N] (c, P, R, G, Q) COEND
     SAT [Init, RR , GG, QQ]"

syntax multi_parallel_inv ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> idt \<Rightarrow> nat \<Rightarrow>
   (nat \<Rightarrow> 'a set) \<Rightarrow> (nat \<Rightarrow> 'a rel) \<Rightarrow>
   (nat \<Rightarrow> 'a com) \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow>
   (nat \<Rightarrow> 'a rel) \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow>
   'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  ("global'_init: _ global'_rely: _ \<parallel>  _ < _ @ {_,_} _ \<sslash> _ {_,_} global'_guar: _ global'_post: _") 

translations 
  "global_init: Init global_rely: RR \<parallel> i < N @
   {P, R} c \<sslash> I {G, Q} global_guar: GG global_post: QQ"
  \<rightharpoonup> "\<turnstile> COBEGIN SCHEME [0 \<le> i < N] (c,
          P \<inter> I,
          R \<inter> CONST pred_to_rel I,
          CONST invar_and_guar I G,
          Q \<inter> I
        ) COEND
     SAT [Init, RR , GG, QQ]"

(*----------------------------------------------------------------------------*)
text \<open>The subgoal-generating method for multi-parallel.\<close>

theorem rg_multi_parallel_subgoals:
  assumes assm_guar_rely: "\<forall> i j. i \<noteq> j \<longrightarrow> i < N \<longrightarrow> j < N \<longrightarrow> G j \<subseteq> R i"
      and assm_pre:  "\<forall> i < N. P' \<subseteq> P i"
      and assm_rely: "\<forall> i < N. R' \<subseteq> R i"
      and assm_guar: "\<forall> i < N. G i \<subseteq> G'"
      and assm_post: "(\<Inter> i \<in> { i. i < N }. Q i) \<subseteq> Q'"
      and assm_local: "\<forall> i<N. \<turnstile> C i sat [P i, R i, G i, Q i]"
    shows "\<turnstile> COBEGIN SCHEME [0 \<le> i < (N::nat)]
           (C i, P i, R i, G i, Q i)
           COEND SAT [P', R', G', Q']"
proof (rule Parallel, goal_cases)
  case 1 show ?case using assm_rely assm_guar_rely by (simp add: SUP_le_iff)
  case 2 show ?case using assm_guar  by force
  case 3 show ?case using assm_pre   by force
  case 4 show ?case using assm_post  by force
  case 5 show ?case using assm_local by force
qed

method method_multi_parallel = rule rg_multi_parallel_subgoals,
  goal_cases guar_rely pre rely guar post body

theorem rg_multi_parallel_nobound_subgoals:
  assumes assm_guar_rely: "\<forall> i j. i \<noteq> j \<longrightarrow> G j \<subseteq> R i"
      and assm_pre:  "\<forall> i. P' \<subseteq> P i"
      and assm_rely: "\<forall> i. R' \<subseteq> R i"
      and assm_guar: "\<forall> i. G i \<subseteq> G'"
      and assm_post: "(\<Inter> i \<in> { i. i < N }. Q i) \<subseteq> Q'"
      and assm_local: "\<forall> i. \<turnstile> C i sat [P i, R i, G i, Q i]"
    shows "\<turnstile> COBEGIN SCHEME [0 \<le> i < (N::nat)]
           (C i, P i, R i, G i, Q i)
           COEND SAT [P', R', G', Q']"
  using assms apply -
  apply (rule Parallel)
  by (simp_all add: SUP_le_iff INT_greatest)

method method_multi_parallel_nobound =
  rule rg_multi_parallel_nobound_subgoals,
  goal_cases guar_rely pre rely guar post body

(*============================================================================*)
subsection \<open>Syntax of Record-Updates\<close>

text \<open>This section contains syntactic sugars for updating a field of a record.
As we use records to model the states of a program, these record-update
operations correspond to the variable-assignments.

The type @{typ idt} denotes a field of a record. The first syntactic sugar
expresses a Basic command (of type @{typ[cartouche=true] \<open>'a com\<close>}) that
updates a record-field @{term x} that is a function; often @{term x} models
an array. After the update, the new value of @{term[cartouche=true] \<open>x i\<close>}
becomes @{term a}.\<close>

syntax "_record_array_assign" ::
  "idt \<Rightarrow> 'index \<Rightarrow> 'expr \<Rightarrow> 'state com" ("(\<acute>_[_] :=/ _)" [70, 65, 64] 61)
translations "\<acute>x[i] := a"
  \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. \<acute>x(i:= a)))\<guillemotright>"

text \<open>The next two syntactic sugars express a state-transformation
function (rather than a command) that updates record-fields.
The first one simply updates an entire variable @{term x},
while the second updates an array @{term[cartouche=true] \<open>x i\<close>}.\<close>

syntax "_record_update_field" ::
  "idt \<Rightarrow> 'expr \<Rightarrow> ('a \<Rightarrow> 'a)" ("\<acute>_ \<leftarrow>/ _" [70] 61)
translations "\<acute>x \<leftarrow> a"
  \<rightleftharpoons> "\<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"

syntax "_record_update_array" ::
  "idt \<Rightarrow> 'expr \<Rightarrow> 'expr \<Rightarrow> ('a \<Rightarrow> 'a)" ("\<acute>_[_] \<leftarrow>/ _" [70, 71] 61)
translations "\<acute>x[i] \<leftarrow> a"
  \<rightharpoonup> "\<guillemotleft>\<acute>(_update_name x (\<lambda>_. \<acute>x(i:= a)))\<guillemotright>"

text \<open>Syntactic sugars for incrementing variables.\<close>

syntax "_inc_fn" :: "idt \<Rightarrow> 'c \<Rightarrow> 'c"  ("(\<acute>_.++)" 61)
translations "\<acute>x.++ " \<rightharpoonup> 
  " \<guillemotleft>\<acute>(_update_name x (\<lambda>_. \<acute>x + 1))\<guillemotright>"

syntax "_inc" :: "idt \<Rightarrow> 'c com"  ("(\<acute>_++)" 61)
translations "\<acute>x++ " \<rightharpoonup> 
  "CONST Basic (\<acute>x.++)"

end
