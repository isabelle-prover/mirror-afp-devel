(* Title:      	   Annotated Commands for Rely-Guarantee
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

section \<open>Annotated Commands\<close>

theory RG_Annotated_Commands

imports RG_Syntax_Extensions "HOL-Hoare.Hoare_Tac"

begin

datatype 'a anncom =
    NoAnno     "'a com"
  | BasicAnno  "'a \<Rightarrow> 'a"
  | WeakPre    "'a set"    "'a anncom"             ("{_} _" [65,61] 61)
  | StrongPost "'a anncom" "'a set"                ("_ {_}" [61,65] 61)
  | SeqAnno    "'a anncom" "'a set"    "'a anncom"
  | CondAnno   "'a bexp"   "'a anncom" "'a anncom" 
  | WhileAnno  "'a bexp"   "'a set"    "'a anncom" 
  | AwaitAnno  "'a bexp"   "'a anncom" 

fun anncom_to_com :: "'a anncom \<Rightarrow> 'a com" where
    "anncom_to_com (NoAnno c)    = c"
  | "anncom_to_com (BasicAnno f) = Basic f"
  | "anncom_to_com (WeakPre b c)    = anncom_to_com c"
  | "anncom_to_com (StrongPost c b) = anncom_to_com c"
  | "anncom_to_com (SeqAnno c1 mid c2) = Seq     (anncom_to_com c1) (anncom_to_com c2)"
  | "anncom_to_com (CondAnno b c1 c2)  = Cond  b (anncom_to_com c1) (anncom_to_com c2)"
  | "anncom_to_com (WhileAnno b b' c)  = While b (anncom_to_com c)"
  | "anncom_to_com (AwaitAnno b c)     = Await b (anncom_to_com c)"

fun add_invar :: "'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom" where
    "add_invar I (NoAnno c)          = NoAnno c"
  | "add_invar I (BasicAnno f)       = BasicAnno f"
  | "add_invar I (WeakPre b c)       = WeakPre (b \<inter> I) (add_invar I c)"
  | "add_invar I (StrongPost c b)    = StrongPost      (add_invar I c)  (b \<inter> I)"
  | "add_invar I (SeqAnno c1 mid c2) = SeqAnno         (add_invar I c1) (mid \<inter> I) (add_invar I c2)"
  | "add_invar I (CondAnno b c1 c2)  = CondAnno  b     (add_invar I c1) (add_invar I c2)"
  | "add_invar I (WhileAnno b b' c)  = WhileAnno b b'  (add_invar I c)"
  | "add_invar I (AwaitAnno b c)     = AwaitAnno b     (add_invar I c)"

syntax
  "_CondAnno" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0IFa _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cond2Anno" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0IFa _ THEN _ FI)" [0,0] 56)
  "_WhileAnno" :: "'a bexp \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0WHILEa _ /DO {stable'_guard: _ } _ /OD)"  [0, 0] 61)
  "_WhileAnno_simple_b" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0WHILEa _ /DO  _ /OD)"  [0, 0] 61)
  "_AwaitAnno" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0AWAITa _ /THEN /_ /END)"  [0,0] 61)
  "_AtomAnno" :: "'a com \<Rightarrow> 'a anncom"
    ("(\<langle>_\<rangle>a)" 61)
  "_WaitAnno" :: "'a bexp \<Rightarrow> 'a anncom"
    ("(0WAITa _ END)" 61)
  "_CondAnno_NoAnnoions" :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a anncom"
    ("(0IF. _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)

translations
  "IFa b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST CondAnno \<lbrace>b\<rbrace> c1 c2"
  "IFa b THEN c FI" \<rightleftharpoons> "IFa b THEN c ELSE SKIP FI"
  "IF. b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST CondAnno \<lbrace>b\<rbrace> (CONST NoAnno c1) (CONST NoAnno c2)"

  "WHILEa b DO {stable_guard: b'} c OD" \<rightharpoonup> "CONST WhileAnno \<lbrace>b\<rbrace> b' c"
  "WHILEa b DO  c OD" \<rightharpoonup> "CONST WhileAnno \<lbrace>b\<rbrace> \<lbrace>b\<rbrace> c"

  "AWAITa b THEN c END" \<rightleftharpoons> "CONST AwaitAnno \<lbrace>b\<rbrace> c"
  "\<langle>c\<rangle>a" \<rightleftharpoons> "AWAITa CONST True THEN c END"
  "WAITa b END" \<rightleftharpoons> "AWAITa b THEN SKIP END"

abbreviation no_assertions_semicolon ::
  "'a anncom \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
 ("_ .; {_} _" [60,60,61] 60) where
  "c1 .; {m} c2 \<equiv> SeqAnno c1 m c2"

text \<open>Below is a special syntax for Basic commands (type ``com'')
encoded inside NoAnno annotated commands (type ``anncom'').

This allows us to keep our syntactic sugars for Basic commands,
which are mostly assignments (":="), without having to redo them
all for BasicAnno annotated commands.

Hence, we wrap Basic commands with this helper function, which is
only defined for Basic commands.\<close>

fun basic_to_basic_anno_syntax:: "'a com \<Rightarrow> 'a anncom" ("'(_')-") where
  "basic_to_basic_anno_syntax (Basic f) = BasicAnno f"
| "basic_to_basic_anno_syntax c = NoAnno c"

text \<open>The following function defines what it means for an annotated
command to satisfy the given specification components. The soundness
of this definition will be proved later.\<close>

fun anncom_spec_valid :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> bool" where

    "anncom_spec_valid pre rely guar post (NoAnno c)
    = (\<turnstile> c sat [pre, rely, guar, post])"
  
  | "anncom_spec_valid pre rely guar post (BasicAnno f)
    = (stable pre rely \<and>
       stable post rely \<and>
       (\<forall>s. s \<in> pre \<longrightarrow> (s, s) \<in> guar) \<and>
       (\<forall>s. s \<in> pre \<longrightarrow> (s, f s) \<in> guar) \<and>
       pre \<subseteq> \<lbrace> \<acute>f \<in> post \<rbrace>)" 
  
  | "anncom_spec_valid pre rely guar post (WeakPre p' ac)
    = ((pre \<subseteq> p') \<and>
       (anncom_spec_valid p' rely guar post ac))"
  
  | "anncom_spec_valid pre rely guar post (StrongPost ac q')
    = ((q' \<subseteq> post) \<and>
       (anncom_spec_valid pre rely guar q' ac))"
  
  | "anncom_spec_valid pre rely guar post (SeqAnno ac1 mid ac2)
    = ((anncom_spec_valid pre rely guar mid  ac1) \<and>
       (anncom_spec_valid mid rely guar post ac2))"
  
  | "anncom_spec_valid pre rely guar post (CondAnno b ac1 ac2)
    = ((stable pre rely) \<and>
       (Id \<subseteq> guar) \<and>
       (anncom_spec_valid (pre \<inter>  b) rely guar post ac1) \<and>
       (anncom_spec_valid (pre \<inter> -b) rely guar post ac2))"
  
  | "anncom_spec_valid pre rely guar post (WhileAnno b b' ac)
    = ((stable pre rely) \<and>
       (stable post rely) \<and>
       (Id \<subseteq> guar) \<and>
       (pre \<inter> -b \<subseteq> post) \<and>
       (pre \<inter>  b \<subseteq> b') \<and>
       (anncom_spec_valid (pre \<inter> b') rely guar pre ac))"
  
  | "anncom_spec_valid pre rely guar post (AwaitAnno b ac)
    = ((stable pre rely) \<and>
       (stable post rely) \<and>
       (\<forall> s. anncom_spec_valid (pre \<inter> b \<inter> {s}) Id UNIV ({s'. (s, s') \<in> guar} \<inter> post) ac))"

text \<open>The following theorem establishes the soundness of the definition above.\<close>

theorem anncom_spec_valid_sound:
  "anncom_spec_valid pre rely guar post ac \<Longrightarrow> \<turnstile> anncom_to_com ac sat [pre, rely, guar, post]"
proof (induction ac arbitrary: pre rely guar post)
  case (NoAnno x)
  thus ?case 
    by (cases x; fastforce)
next
  case (BasicAnno x)
  thus ?case 
    by (fastforce simp: rg_basic_named)
next
  case (WeakPre pre' ac)
  thus ?case
    by (fastforce dest: Conseq)
next
  case (StrongPost ac x2)
  thus ?case 
    by (fastforce simp: weaken_post)
next
  case (SeqAnno ac1 x2 ac2)
  thus ?case 
    by (fastforce simp: Seq)
next
  case (CondAnno x1a ac1 ac2)
  thus ?case 
    by (fastforce simp: Cond subset_iff)
next
  case (WhileAnno x1a x2 ac)
  thus ?case
    apply clarsimp
    apply (rule While,simp_all)
      apply (metis le_inf_iff Int_lower1 strengthen_pre)
    by fastforce
next
  case (AwaitAnno x1a ac)
  thus ?case  
    apply clarsimp
    apply (rule Await, simp_all)
   by (smt (verit, best) Conseq IdI case_prodE mem_Collect_eq subset_iff)
qed

(*==================================================================*)
subsection \<open>Annotated Quintuples\<close>

text \<open>For convenience, we define the following datatype, which collects
an annotated command with its specification components.\<close>

datatype 'a annquin = AnnQuin "'a set" "'a rel" "'a anncom" "'a rel" "'a set"
  ("{_,_} _ {_,_}" ) 

abbreviation annquin_invar ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a anncom \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a annquin"
  ("{_,_} _ \<sslash> _ {_,_}") where
  "annquin_invar pre rely ac I guar post \<equiv> AnnQuin
    (pre \<inter> I) (rely \<inter> pred_to_rel I)
    (add_invar I ac)
    (invar_and_guar I guar) (post \<inter> I)"

text \<open>Helper functions for extracting the individual components of
an @{typ[cartouche=true] \<open>'a annquin\<close>}.\<close>

fun  preOf :: "'a annquin \<Rightarrow> 'a set"
  where "preOf (AnnQuin pre rely ac guar post) = pre"

fun relyOf :: "'a annquin \<Rightarrow> 'a rel"
  where "relyOf (AnnQuin pre rely ac guar post) = rely"

fun  cmdOf :: "'a annquin \<Rightarrow> 'a anncom"
  where "cmdOf (AnnQuin pre rely ac guar post) = ac"

fun guarOf :: "'a annquin \<Rightarrow> 'a rel"
  where "guarOf (AnnQuin pre rely ac guar post) = guar"

fun postOf :: "'a annquin \<Rightarrow> 'a set"
  where "postOf (AnnQuin pre rely ac guar post) = post"

text \<open>Validity of @{typ[cartouche=true] \<open>'a annquin\<close>} is the same as the
validity of the ``quintuples'' when written out separately.\<close>

abbreviation annquin_valid :: "'a annquin \<Rightarrow> bool" where
  "annquin_valid rgac \<equiv> case rgac of (AnnQuin pre rely ac guar post) \<Rightarrow>
   anncom_spec_valid pre rely guar post ac"

lemma annquin_simp[simp]:
  "annquin_valid (AnnQuin p r c g q) = anncom_spec_valid p r g q c"
  by fastforce

text \<open>Syntax for expressing a valid @{typ[cartouche=true] \<open>'a annquin\<close>}
in terms of its components.\<close>

syntax
  "_valid_annquin"
    :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a set \<Rightarrow> bool"
    ("rely:_ guar:_ anno'_code: {_} _ {_}")
  "_valid_annquin_invar"
    :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a set \<Rightarrow> bool"
    ("rely:_ guar:_ inv:_ anno'_code: {_} _ {_}")

translations
  "rely: R guar: G anno_code: {P} ac {Q}"
  \<rightharpoonup> "CONST annquin_valid (CONST AnnQuin P R ac G Q)"
  "rely: R guar: G inv: I anno_code: {P} ac {Q}"
  \<rightharpoonup> "CONST annquin_valid (CONST AnnQuin
        (P \<inter> I) (R \<inter> CONST pred_to_rel I)
        (CONST add_invar I ac)
        (CONST invar_and_guar I G) (Q \<inter> I))"

(*==================================================================*)
subsection \<open>Structured Tactics for Annotated Commands\<close>

lemma anncom_subgoals_no:
  "\<turnstile> c sat [pre, rely, guar, post] \<Longrightarrow> anncom_spec_valid pre rely guar post (NoAnno c)"
  by fastforce

lemma anncom_subgoals_invar_no:
  assumes "\<turnstile> c sat [pre \<inter> I, rely \<inter> pred_to_rel I, invar_and_guar I guar, post \<inter> I]"
  shows "anncom_spec_valid (pre \<inter> I) (rely \<inter> pred_to_rel I) (invar_and_guar I guar) 
                           (post \<inter> I) (add_invar I (NoAnno c))"
  using assms by fastforce

lemma anncom_subgoals_basicanno_invar:
  assumes stable_pre:     "stable (pre \<inter> I) (rely \<inter> pred_to_rel I)"
      and stable_post:    "stable (post \<inter> I) (rely \<inter> pred_to_rel I)"
      and guar_id:        "\<forall>s. s \<in> (pre \<inter> I) \<longrightarrow> (s, s) \<in> (invar_and_guar I guar)"
      and establish_guar: "\<forall>s. s \<in> (pre \<inter> I) \<longrightarrow> (s, f s) \<in> (invar_and_guar I guar)"
      and establish_post: "(pre \<inter> I) \<subseteq> \<lbrace> \<acute>f \<in> (post \<inter> I) \<rbrace>"
  shows "rely: rely guar: guar inv: I anno_code: {pre} (BasicAnno f) {post}"
  using assms by fastforce

method method_annquin_basicanno =
  rule anncom_subgoals_basicanno_invar,
  goal_cases stable_pre stable_post guar_id est_guar est_post

lemma anncom_subgoals_seq:
  assumes "anncom_spec_valid pre rely guar mid  c1"
      and "anncom_spec_valid mid rely guar post c2"
    shows "anncom_spec_valid pre rely guar post (SeqAnno c1 mid c2)"
  using assms by fastforce

lemma anncom_subgoals_invar_seq:
  assumes "anncom_spec_valid (pre \<inter> I) (rely \<inter> pred_to_rel I) (invar_and_guar I guar) 
                             (mid  \<inter> I) (add_invar I c1)"
      and "anncom_spec_valid (mid \<inter> I) (rely \<inter> pred_to_rel I) (invar_and_guar I guar) 
                             (post \<inter> I) (add_invar I c2)"
    shows "anncom_spec_valid (pre \<inter> I) (rely \<inter> pred_to_rel I) (invar_and_guar I guar) 
                             (post \<inter> I) (add_invar I (SeqAnno c1 mid c2))"
  using Seq assms by fastforce

lemma anncom_subgoals_invar_seq_abbrev:
  assumes "anncom_spec_valid (pre \<inter> I) (rely \<inter> pred_to_rel I) (invar_and_guar I guar) 
                             (mid  \<inter> I) (add_invar I c1)"
      and "anncom_spec_valid (mid \<inter> I) (rely \<inter> pred_to_rel I) (invar_and_guar I guar) 
                             (post \<inter> I) (add_invar I c2)"
    shows "rely: (rely) guar: guar inv: I anno_code: {pre} (c1 .; {mid} c2) {post}"
  using Seq assms by fastforce

method method_annquin_seq =
  (rule anncom_subgoals_invar_seq | rule anncom_subgoals_invar_seq_abbrev), 
  goal_cases c1 c2

lemma anncom_subgoals_while:
  assumes "stable pre rely"
      and "stable post rely"
      and "Id \<subseteq> guar"
      and "pre \<inter> -b \<subseteq> post"
      and "pre \<inter>  b \<subseteq> b'"
      and "anncom_spec_valid (pre \<inter> b') rely guar pre ac"
    shows "anncom_spec_valid pre rely guar post (WhileAnno b b' ac)"
  using assms by fastforce

lemma add_invar_while:
  assumes "anncom_spec_valid (p \<inter> I) (R \<inter> pred_to_rel I) (invar_and_guar I G) 
                             (q \<inter> I) (WhileAnno b b' (add_invar I ac))"
    shows "anncom_spec_valid (p \<inter> I) (R \<inter> pred_to_rel I) (invar_and_guar I G) 
                             (q \<inter> I) (add_invar I (WhileAnno b b' ac))"
  using assms by fastforce

lemma anncom_subgoals_invar_while_abbrev:
  assumes "anncom_spec_valid (p \<inter> I) (R \<inter> pred_to_rel I) (invar_and_guar I G) 
                             (q \<inter> I) (add_invar I (WhileAnno b b' ac))"
    shows "rely: R guar: G inv: I anno_code: {p} (WhileAnno b b' ac) {q}"
  using assms by fastforce

method method_annquin_while =
  rule anncom_subgoals_invar_while_abbrev,
  rule add_invar_while,
  rule anncom_subgoals_while, 
  goal_cases stable_pre stable_post guar_id neg_guard guard body

(*==================================================================*)
subsection \<open>Binary Parallel\<close>

text \<open>This section contains inference rules for two annotated commands
running in parallel. For convenience, we first define a datatype that
encapsulates the components.\<close>

datatype 'a binary_par_quin = ParCode
  "'a set" "'a rel" "'a annquin" "'a annquin" "'a rel" "'a set"
  ("{_,_} _ \<parallel>a _ {_,_}")

text \<open>The next function sets out the proof obligations of binary parallel,
using the datatype @{typ[cartouche=true] \<open>'a binary_par_quin\<close>} above.
It is then followed by the theorem that establishes the soundness of the
inference rule encoded by the function @{term binary_parallel_valid}.\<close>

fun binary_parallel_valid:: "'a binary_par_quin \<Rightarrow> bool" where
 "binary_parallel_valid (ParCode init gr (AnnQuin p1 r1 c1 g1 q1) (AnnQuin p2 r2 c2 g2 q2) gg final)
  = ( annquin_valid (AnnQuin p1 r1 c1 g1 q1)
    \<and> annquin_valid (AnnQuin p2 r2 c2 g2 q2)
    \<and>    init \<subseteq> p1 \<inter> p2
    \<and>      gr \<subseteq> r1 \<inter> r2
    \<and>      g1 \<subseteq> r2
    \<and>      g2 \<subseteq> r1
    \<and> g1 \<union> g2 \<subseteq> gg
    \<and> q1 \<inter> q2 \<subseteq> final)"

theorem valid_binary_parallel:
 "binary_parallel_valid (ParCode init gr (AnnQuin p1 r1 c1 g1 q1) (AnnQuin p2 r2 c2 g2 q2) gg final)
 \<Longrightarrow> \<turnstile> COBEGIN (anncom_to_com c1, p1, r1, g1, q1) \<parallel> (anncom_to_com c2, p2, r2, g2, q2) 
       COEND SAT [init, gr, gg, final]"
  by (rule Parallel; force intro:anncom_spec_valid_sound simp: less_Suc_eq)

text \<open>Variants of the theorem above.\<close>

theorem valid_binary_parallel_exists:
 "binary_parallel_valid (ParCode init gr (AnnQuin p1 r1 c1 g1 q1) (AnnQuin p2 r2 c2 g2 q2) gg final)
 \<Longrightarrow> {init, gr} anncom_to_com c1 \<parallel> anncom_to_com c2 {gg, final}"
  by (fast dest: valid_binary_parallel)

theorem valid_binary_parallel_exists_annotated:
  assumes "binary_parallel_valid (ParCode
           init gr
           (AnnQuin p1 r1 c1' g1 q1) (AnnQuin p2 r2 c2' g2 q2)
           gg final)"
      and "anncom_to_com c1' = c1"
      and "anncom_to_com c2' = c2"
    shows "{init, gr} c1 \<parallel> c2 {gg, final}"
  using assms
  by (fast dest: valid_binary_parallel)

(*==================================================================*)
subsection \<open>Helpers: Index Offsets\<close>

text \<open>Before moving on to multi-parallel programs, we first prepare
some lemmas that help reason about offsets and indices.\<close>

abbreviation nat_range_set_neq_i :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set"
  ("{_..<_\<noteq>_}") where
  "nat_range_set_neq_i lo hi x \<equiv> {lo..<hi} - {x}"

lemma all_set_range_to_offset:
  "(\<forall>i\<in>{lo..<hi::nat}. P (f i)) \<longleftrightarrow> (\<forall>i<(hi-lo). P (f (lo + i)))"
  by (metis add.commute atLeastLessThan_iff less_diff_conv nat_le_iff_add)

lemma Int_set_range_to_offset:
  "(\<Inter>i\<in>{lo..<hi::nat}.  f i) = (\<Inter>i<(hi-lo).  f (lo + i))"
  by (fastforce simp: le_iff_add)

lemma Un_set_range_to_offset:
  "(\<Union>i\<in>{lo..<hi::nat}.  g (f i)) = (\<Union>i<(hi-lo).  g (f (lo + i)))"
  apply standard
   apply clarsimp
   apply (metis add_diff_cancel_left' diff_less_mono lessThan_iff nat_le_iff_add)
  by fastforce

lemma Int_set_range_neq_to_offset: "i = lo + ii
  \<Longrightarrow> (\<Inter>j\<in>{lo..<hi\<noteq>i}.  f j) = (\<Inter>j\<in>{0..<(hi-lo)\<noteq> ii}.  f (lo + j))"
  unfolding Ball_def Bex_def image_def
  apply clarsimp
  by (metis (lifting) diff_add_inverse diff_less_mono less_diff_conv nat_le_iff_add)
  
lemma Int_set_range_neq_to_offset2: "ii< (hi - lo)
  \<Longrightarrow> (\<Inter>j\<in>{lo..<hi\<noteq>(lo + ii)}.  f j) = (\<Inter>j\<in>{0..<(hi-lo)\<noteq> ii}.  f (lo + j))"
  unfolding Ball_def Bex_def image_def
  apply clarsimp
  by (metis (lifting) add.commute add_left_imp_eq less_diff_conv nat_le_iff_add)

lemma forall_range_to_offset:
  "(\<forall>i\<in>{lo..<(hi::nat)}. P i) \<longleftrightarrow> (\<forall>i\<in>{0..<(hi - lo)}. P (lo + i))"
  unfolding Ball_def
  apply clarsimp
  by (metis add.commute le_add1 le_add_diff_inverse less_diff_conv)

lemma SCHEME_map_domain:
  "map (\<lambda>i. rgac i) [lo ..< (N::nat)] = map (\<lambda>i. rgac (lo + i)) [0..<(N-lo)]" 
  by (induct N arbitrary: lo; simp add: Suc_diff_le)

lemma offset_P: "(\<forall>i. lo \<le> i \<and> i < (N::nat) \<longrightarrow> P i) \<Longrightarrow> lo \<le> N \<Longrightarrow> (\<forall>i. i <(N-lo) \<longrightarrow> P (lo + i))"
  by fastforce

lemma INTER_offset: 
  shows "(\<Inter>x<((N::nat) - lo). p (lo + x)) = (\<Inter>x\<in>{lo..<N}. p x)"
  by (simp add: Ball_def Int_set_range_to_offset)

lemma LT_offset: "(\<forall>i. lo \<le> i \<and> i < (N::nat) \<longrightarrow> P i) \<longleftrightarrow> (\<forall>i<N - lo. P (lo + i))"
  by (metis add.commute le_add1 le_add_diff_inverse2 less_diff_conv)

(*==================================================================*)
subsection \<open>Multi-Parallel\<close>

text \<open>This section contains inference rules for multiple annotated
commands running in parallel. Again, for convenience we first define
a datatype that encapsulates the components:
\begin{enumerate}
  \item Global precondition
  \item Global rely
  \item The lower index
  \item The upper index
  \item Sequential programs (each an annotated quintuple),
        indexed by the natural numbers
  \item Global guarantee
  \item Global postcondition
\end{enumerate}
\<close>

datatype 'a multi_par_quin = MultiParCode
  "'a  set" (* global init *)
  "'a  rel" (* global rely *)
   nat nat  (* indices *)
  "nat \<Rightarrow> 'a annquin" (* indexed programs *)
  "'a  rel" (* global guar *)
  "'a  set" (* global post *)

text \<open>Using the datatype above, the inference rules are set out as the
following two functions.\<close>

fun multipar_valid :: "'a multi_par_quin \<Rightarrow> bool" where
  "multipar_valid (MultiParCode init RR lo N iac gg final) =
   ( (\<forall>i\<in>{lo..<N}. annquin_valid (iac i)) \<and>
      init \<subseteq> (\<Inter>i\<in>{lo..<N}.  preOf (iac i)) \<and>
      RR \<subseteq> (\<Inter>i\<in>{lo..<N}. relyOf (iac i)) \<and>
      (\<forall>i\<in>{lo..<N}. guarOf (iac i) \<subseteq> (\<Inter>j\<in>{lo..<N\<noteq>i}. relyOf (iac j))) \<and>
      (\<Union>i\<in>{lo..<N}. guarOf (iac i)) \<subseteq> gg \<and>
      (\<Inter>i\<in>{lo..<N}. postOf (iac i)) \<subseteq> final )"

fun multipar_valid_offset:: "'a multi_par_quin \<Rightarrow> bool" where
  "multipar_valid_offset (MultiParCode init RR lo N iac gg final) =
   ( (\<forall>i<(N-lo). annquin_valid (iac (lo + i))) \<and>
      init \<subseteq> (\<Inter>i<(N-lo).  preOf (iac (lo + i))) \<and>
      RR \<subseteq> (\<Inter>i<(N-lo). relyOf (iac (lo + i))) \<and>
      (\<forall>i<(N-lo). guarOf (iac (lo + i)) \<subseteq> (\<Inter>j\<in>{0..<(N-lo)\<noteq>i}. relyOf (iac (lo + j)))) \<and>
      (\<Union>i<(N-lo). guarOf (iac (lo + i))) \<subseteq> gg \<and>
      (\<Inter>i<(N-lo). postOf (iac (lo + i))) \<subseteq> final )"

text \<open>Alternative syntax that encodes the validity of multi-parallel
statements.\<close>

syntax
  "_multi_parallel_anno"
    :: "'a set \<Rightarrow> 'a rel \<Rightarrow> idt \<Rightarrow> nat \<Rightarrow> 'a annquin \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
    ("annotated global'_init: _ global'_rely: _ \<parallel>  _ < _ @ _ global'_guar: _ global'_post: _") 
  "_multi_parallel_anno_lo_hi"
    :: "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> idt \<Rightarrow> nat \<Rightarrow> 'a annquin \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
    ("annotated global'_init: _ global'_rely: _ \<parallel>  _ \<le> _ < _ @ _ global'_guar: _ global'_post: _") 

translations 
  "annotated global_init: Init global_rely: RR \<parallel> i < N @ rgac global_guar: GG global_post: QQ"
  \<rightharpoonup> "CONST multipar_valid (CONST MultiParCode Init RR 0 N (\<lambda>i. rgac) GG QQ)"
  "annotated global_init: Init global_rely: RR \<parallel> lo \<le> i < hi @ rgac global_guar: GG global_post: QQ"
  \<rightharpoonup> "CONST multipar_valid_offset (CONST MultiParCode Init RR lo hi (\<lambda>i. rgac) GG QQ)"

text \<open>The soundness of the inference rules, in multiple variants.\<close>

lemma multipar_valid_offset_equiv:
  "multipar_valid        (MultiParCode init RR lo hi iac gg final) \<longleftrightarrow>
   multipar_valid_offset (MultiParCode init RR lo hi iac gg final)"
  apply clarsimp
  apply (intro conjI iffI)
             apply fastforce
            apply fastforce
           apply fastforce
          apply fastforce
         apply fastforce
        apply (fastforce simp: Int_set_range_to_offset)
       apply (metis (lifting) atLeastLessThan_iff diff_less_mono le_add_diff_inverse)
      apply (metis (no_types, lifting) ext INTER_offset)
      apply (metis (no_types, lifting) ext INTER_offset)
    apply (simp add: Ball_def)
    apply (smt (verit, ccfv_threshold) Int_set_range_neq_to_offset Sup.SUP_cong le_add_diff_inverse 
                                       le_add_diff_inverse2 less_diff_conv)
   apply (metis Un_set_range_to_offset)
  by (fastforce simp: Int_set_range_to_offset)

theorem valid_multipar:
  "multipar_valid (MultiParCode Init RR lo N rgac GG QQ) \<Longrightarrow>
  \<turnstile> COBEGIN SCHEME [lo \<le> i < N] (
         CONST anncom_to_com (cmdOf (rgac i)),
          preOf (rgac i),
          relyOf (rgac i),
          guarOf (rgac i) ,
          postOf (rgac i) 
        ) COEND
     SAT [Init, RR , GG, QQ]"
  apply (rule Parallel)
       apply (simp add: subset_iff)
      apply (metis Diff_iff add.commute add_left_cancel atLeastLessThan_iff empty_iff insert_iff 
                   le_add1 less_diff_conv nth_upt)
     apply (fastforce intro: Ball_def simp: subset_iff)     
    apply (fastforce simp: subset_iff)
   apply (simp add: subset_iff )
   apply (metis atLeastLessThan_iff diff_less_mono le_add_diff_inverse)
  apply (simp add: subset_iff)
  by (metis (lifting) ext add.commute anncom_spec_valid_sound annquin_simp atLeastLessThan_iff 
                      cmdOf.simps guarOf.simps le_add1 less_diff_conv postOf.elims preOf.simps 
                      relyOf.simps)


theorem valid_multipar_with_internal_rg: 
  "multipar_valid (MultiParCode Init RR lo N (\<lambda>i. AnnQuin (p i) (r i) (ac i) (g i) (q i)) GG QQ) \<Longrightarrow>
  (\<forall>i. anncom_to_com (ac i) = c i) \<Longrightarrow>
  \<turnstile> COBEGIN SCHEME [lo \<le> i < N] ((c i), p i, r i, g i, q i) COEND
    SAT [Init, RR , GG, QQ]"
  unfolding  Ball_def
  apply (rule Parallel, simp_all add: subset_iff)
     apply (metis Diff_iff add.commute atLeastLessThan_iff diff_add_inverse less_diff_conv 
                  nat_le_iff_add nth_upt singletonD)
    apply (metis add.commute atLeastLessThan_iff le_add1 less_diff_conv)
   apply (metis add.commute atLeastLessThan_iff less_diff_conv nat_le_iff_add)
  by (metis add.commute anncom_spec_valid_sound atLeastLessThan_iff le_add1 less_diff_conv)

theorem valid_multipar_explicit:
  assumes 
    local_sat: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> annquin_valid (iac i)" and
    pre:  "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> init \<subseteq>  preOf (iac i)" and
    rely: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> RR \<subseteq> relyOf (iac i)" and     
    guar_imp_rely: "\<And>i j. lo \<le> i \<and> i<N \<Longrightarrow> lo \<le> j \<and> j < N \<Longrightarrow> i \<noteq> j 
                    \<Longrightarrow> guarOf (iac i) \<subseteq> relyOf (iac j)" and 
    guar: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> guarOf (iac i) \<subseteq> gg" and 
    post: "(\<Inter>i\<in>{lo..<N}. postOf (iac i)) \<subseteq> final"
  shows "multipar_valid (MultiParCode init RR lo N iac gg final)"
  using assms by fastforce

theorem valid_multipar_offset_explicit:
  assumes 
    local_sat: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> annquin_valid (iac i)" and
    pre:  "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> init \<subseteq>  preOf (iac i)" and
    rely: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> RR \<subseteq> relyOf (iac i)" and     
    guar_imp_rely: "\<And>i j. lo \<le> i \<and> i<N \<Longrightarrow> lo \<le> j \<and> j < N \<Longrightarrow> i \<noteq> j 
                    \<Longrightarrow> guarOf (iac i) \<subseteq> relyOf (iac j)" and 
    guar: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> guarOf (iac i) \<subseteq> gg" and 
    post: "(\<Inter>i\<in>{lo..<N}. postOf (iac i)) \<subseteq> final"
  shows "multipar_valid_offset (MultiParCode init RR lo N iac gg final)"
  apply clarsimp
  apply (intro conjI, simp_all add: le_INF_iff assms)
    apply (simp add: guar_imp_rely less_diff_conv)
   apply (simp add: SUP_le_iff guar)
  using post by (fastforce simp: nat_le_iff_add SUP_le_iff guar)

theorem valid_multipar_explicit2:
  assumes 
    local_sat: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> annquin_valid {p i,r i} c i {g i ,q i}" and
    pre:  "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> init \<subseteq>  p i" and
    rely: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> RR \<subseteq> r i" and     
    guar_imp_rely: "\<And>i j. lo \<le> i \<and> i<N \<Longrightarrow> lo \<le> j \<and> j < N \<Longrightarrow> i \<noteq> j \<Longrightarrow> g i \<subseteq> r j" and 
    guar: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> g i \<subseteq> gg" and 
    post: "(\<Inter>i\<in>{lo..<N}. q i) \<subseteq> final"
    shows "multipar_valid (MultiParCode init RR lo N (\<lambda>i. {p i,r i} c i {g i ,q i}) gg final)"
  using assms 
  by (force simp: subset_iff)

theorem valid_multipar_explicit_with_invariant:
  assumes 
    local_sat: "\<And>i. i < N \<Longrightarrow> annquin_valid {p i,r i} c i \<sslash> Inv {g i ,q i}" and
    pre:  "\<And>i. i < N \<Longrightarrow> init \<subseteq>  p i \<inter> Inv" and
    rely: "\<And>i. i < N \<Longrightarrow> RR \<subseteq> r i \<inter> pred_to_rel Inv" and     
    guar_imp_rely: "\<And>i j. i<N \<Longrightarrow> j < N \<Longrightarrow> i \<noteq> j 
                    \<Longrightarrow> invar_and_guar Inv (g i) \<subseteq> r j \<inter> pred_to_rel Inv" and 
    guar: "\<And>i. i < N \<Longrightarrow> invar_and_guar Inv (g i) \<subseteq> gg" and 
    post: "(\<Inter>i<N. q i \<inter> Inv) \<subseteq> final"
  shows "multipar_valid (MultiParCode init RR 0 N (\<lambda>i. {p i,r i} c i \<sslash> Inv {g i ,q i}) gg final)"
  apply (rule valid_multipar_explicit2)
  using lessThan_atLeast0 assms by presburger+

method method_annquin_multi_parallel =
  rule valid_multipar_explicit2,
  goal_cases local_sat pre rely guar_imp_rely guar post

(*==================================================================*)
subsection \<open>The Main Tactics\<close>

lemmas rg_syntax_simps_collection =
  multipar_valid.simps 
  multipar_valid_offset.simps 
  add_invar.simps 
  basic_to_basic_anno_syntax.simps 
  postOf.simps preOf.simps relyOf.simps guarOf.simps
  annquin_simp 
  anncom_spec_valid.simps 

method rg_proof_expand = (auto simp only: rg_syntax_simps_collection ; simp?) 

method method_anno_ultimate =
    method_annquin_basicanno
  | method_annquin_seq+
  | method_annquin_while
  | method_annquin_multi_parallel
  | rg_proof_expand

end
