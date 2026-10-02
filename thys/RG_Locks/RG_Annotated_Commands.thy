
(*
Title:         Rely-Guarantee Annotated Commands
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Annotated Commands\<close>

text \<open>This theory defines \emph{annotated commands} on top of the build-in
RG library. It also defines the relevant syntax and subgoal-generating methods.\<close>

theory RG_Annotated_Commands
imports RG_Syntax_Extensions
begin

datatype 'a anncom =
    NoAnno     "'a com"                            ("'(_')-")
  | BasicAnno  "'a \<Rightarrow> 'a"
  | WeakPre    "'a set"    "'a anncom"             ("{_} _"  52)
  | StrongPost "'a anncom" "'a set"                ("_ {_}"  53)
  | SeqAnno    "'a anncom" "'a set"    "'a anncom" ("_ .; {_} _" [60,0,61] 60)
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

(*============================================================================*)
subsection \<open>Syntactic Sugars\<close>

abbreviation "SKIPa \<equiv> NoAnno SKIP"

syntax (* anncom *)
  "_CondAnno" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0IFa _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)

  "_Cond2Anno" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("IFa _ THEN _ FI"  67)

  "_WhileAnno" :: "'a bexp \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0WHILEa _ /DO {stable'_guard: _ } _ /OD)"  [0, 0] 61)

  "_WhileAnno_simple_b" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0WHILEa _ /DO  _ /OD)"  [0, 0] 61)

  "_Spinloop" :: "'a bexp \<Rightarrow> 'a anncom"
    ("(SPIN _)"   63)

  "_AwaitAnno" :: "'a bexp \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(0AWAITa _ /THEN /_ /END)"  [0,0] 61)

 (* "_AtomAnno" :: "'a com \<Rightarrow> 'a anncom"
    ("(\<langle>_\<rangle>a)" 61)*)

  "_WaitAnno" :: "'a bexp \<Rightarrow> 'a anncom"
    ("(0WAITa _ END)" 61)

  "_CondAnno_NoAnnotations" :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a anncom"
    ("(0IF. _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)

translations (* anncom *)
  "IFa b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST CondAnno \<lbrace>b\<rbrace> c1 c2"
  "IFa b THEN c FI" \<rightleftharpoons> "IFa b THEN c ELSE (CONST SKIPa) FI"
  "IF. b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST CondAnno \<lbrace>b\<rbrace> (CONST NoAnno c1) (CONST NoAnno c2)"

  "WHILEa b DO {stable_guard: b'} c OD" \<rightharpoonup> "CONST WhileAnno \<lbrace>b\<rbrace> b' c"
  "WHILEa b DO  c OD" \<rightharpoonup> "CONST WhileAnno \<lbrace>b\<rbrace> \<lbrace>b\<rbrace> c"
  (*"SPIN b " \<rightharpoonup> "CONST WhileAnno \<lbrace>b\<rbrace> CONST UNIV CONST SKIPa"*)

  "AWAITa b THEN c END" \<rightleftharpoons> "CONST AwaitAnno \<lbrace>b\<rbrace> c"
 (* "\<langle>c\<rangle>a" \<rightleftharpoons> "AWAITa CONST True THEN c END"*)
  "WAITa b END" \<rightleftharpoons> "AWAITa b THEN SKIP END"

abbreviation "Cond_Skip_Right b c \<equiv>  CondAnno b c  SKIPa"

abbreviation "Spinloop b \<equiv> WhileAnno b UNIV SKIPa"
translations (* anncom *)
  "SPIN b " \<rightharpoonup> "CONST Spinloop \<lbrace>b\<rbrace> "

definition Forever:: "'a anncom \<Rightarrow> 'a anncom" ("FOREVER _" 55)
  where "FOREVER c \<equiv> WHILEa (CONST True) DO c OD "

syntax  "_When" :: "'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom"
    ("(WHEN _ /DO  _ /OD)"  [0, 0] 61)

translations  "WHEN b DO  c OD" \<rightharpoonup> " FOREVER (IFa b THEN c FI)"

text \<open>We remove the slash notation to avoid ambiguous syntax\<close>
no_notation  inverse_divide    (infixl "'/" 70)

text "Syntax for when you just want to give a block of sequential code to be executed
atomically, with no annotations"
abbreviation Atomic :: "'a com \<Rightarrow> 'a anncom" ("\<langle>_\<rangle>a")
  where "Atomic c \<equiv> AwaitAnno UNIV (NoAnno c)"

abbreviation left_Basic_seq_comp:: "'a com \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom" 
  ("_ ..; _ _" [61, 0, 61] 62) where
  "a ..;m c \<equiv> NoAnno a .;{m} c"

abbreviation left_Atomic_seq_comp:: "'a com \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom" 
  ("\<langle>_\<rangle> .; _ _" [0, 0, 62] 64) where
  "\<langle>a\<rangle> .;m c \<equiv> \<langle>a\<rangle>a .;{m} c"

abbreviation ExplicitPre:: "'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a anncom" 
  ("_ '/ _" [62, 53] 53) where
  "p / c \<equiv> {p} c"

abbreviation ExplicitPost:: "'a anncom \<Rightarrow> 'a set \<Rightarrow> 'a anncom" 
  ("_ '/ _" [56, 64] 56) where
  "c / p \<equiv> c {p}"

lemma 
  "SKIPa = p / (c::'a anncom) .;{m} c / p"

  "SKIPa = p / c .;{m} (SPIN b) / p"
  "SKIPa = p / a ..; m (SPIN b) / p"
  "SKIPa = IFa pp THEN a ..; m c FI"
  "SKIPa = a ..; m IFa pp THEN a ..; m c / p FI"

  "SKIPa = \<langle>x\<rangle> .; m (z)- / p"

  "SKIPa = p / \<langle>x\<rangle> .; m a ..; m \<langle>x\<rangle> .; m (z)- / p"
  "SKIPa = p / \<langle>x\<rangle> .; \<lbrace>q\<rbrace> a ..; m \<langle>x\<rangle> .; m (z)- / p"
  "SKIPa = a ..; \<lbrace>q\<rbrace> a ..; m \<langle>x\<rangle> .; m (z)- "

  "\<langle>kk ;; kk\<rangle> .; \<lbrace>jj \<and> dd\<rbrace> SKIPa = SKIPa"
  oops (* Checking the syntax plays nicely together *)

(*============================================================================*)
subsection \<open>Validity\<close>

fun anncom_spec_valid ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> bool"
  where
  "anncom_spec_valid pre rely guar post (NoAnno c)
  = (\<turnstile> c sat [pre, rely, guar, post])"

| "anncom_spec_valid pre rely guar post (BasicAnno f)
  =
       (stable pre rely
      \<and> stable post rely
      \<and> (\<forall>s. s \<in> pre \<longrightarrow> (s, s) \<in> guar)
      \<and>  (\<forall>s. s \<in> pre \<longrightarrow> (s, f s) \<in> guar)
      \<and>  pre \<subseteq> \<lbrace> \<acute>f \<in> post \<rbrace>)" 

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

theorem anncom_spec_valid_sound:
  "anncom_spec_valid pre rely guar post ac \<Longrightarrow> \<turnstile> anncom_to_com ac sat [pre, rely, guar, post]"
proof (induction ac arbitrary: pre rely guar post)
  case (NoAnno x)
  then show ?case by(cases x ; simp; auto)
next
 case (BasicAnno x)
  then show ?case
    by auto (* Use "simp" if having different definition in "anncom_spec_valid.BasicAnno" *)
next
  case (WeakPre pre' ac)
  then show ?case using Conseq by fastforce
next
  case (StrongPost ac x2)
  then show ?case using weaken_post by fastforce
next
  case (SeqAnno ac1 x2 ac2)
  then show ?case using Seq by fastforce
next
  case (CondAnno x1a ac1 ac2)
  then show ?case by (simp add: Cond subset_iff)
next
  case (WhileAnno x1a x2 ac)
  then show ?case
    apply simp using While
    by (smt (verit, best) Int_subset_iff RG_Hoare.stable_def in_mono inf_le1 pair_in_Id_conv strengthen_pre)
next
  case (AwaitAnno x1a ac)
  then show ?case apply simp 
    apply (rule Await)
    using AwaitAnno.prems anncom_spec_valid.simps(8) apply blast+
    apply auto[1]
    by (smt (verit, best) Conseq IdI case_prodE mem_Collect_eq subset_iff)
qed

theorem anncom_spec_valid_sound_format:
  assumes "anncom_spec_valid pre rely guar post ac"
and "anncom_to_com ac = c"
shows " \<turnstile> c sat [pre, rely, guar, post]"
  using anncom_spec_valid_sound assms(1) assms(2) by blast

theorem anncom_spec_valid_sound_NoAnno:
  assumes "anncom_spec_valid pre rely guar post (NoAnno c)"
shows " \<turnstile> c sat [pre, rely, guar, post]"
  using assms by auto

(*==================================================================*)
subsection \<open>Annotated Quintuples\<close>

text \<open>An annotated quintuple includes an annotated command along with
its top-level pre/post-conditions and rely/guarantee-relations.\<close>

datatype 'a annquin = AnnQuin "'a set" "'a rel" "'a anncom" "'a rel" "'a set"
  ("{_,_} _ {_,_}" ) 

text "Helper functions for extracting the fields from the syntax"

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

text \<open>Where an invariant permeates an annotated command, this can be 
abbreviated by drawing the invariant out to the top level, and
transformed into an annotated quintuple.\<close>

text "Alternative abbreviation for a quintuple using explicit keywords"

abbreviation annquin_keyword ::
  "'a rel \<Rightarrow>  'a rel \<Rightarrow> 'a set \<Rightarrow> 'a anncom  \<Rightarrow> 'a set \<Rightarrow> 'a annquin"
  ("rely:_ guar:_ annotated'_code: {_} _ {_}") where
  "annquin_keyword rely guar pre ac post \<equiv> AnnQuin pre rely ac guar post"

definition annquin_invar ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a anncom \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a annquin"
  ("{_ , _}/_\<sslash>_/{_ , _}") where
  "annquin_invar pre rely ac I guar post
    \<equiv> AnnQuin (pre \<inter> I) (lift_rely I rely) (add_invar I ac) (lift_guar I guar) (post \<inter> I)"

lemma preOf_with_invariant[simp]:
  "preOf  {p, r} c \<sslash> invar {g, q} = p \<inter> invar"
  "relyOf {p, r} c \<sslash> invar {g, q} = lift_rely invar r"
  "guarOf {p, r} c \<sslash> invar {g, q} = lift_guar invar g"
  "postOf {p, r} c \<sslash> invar {g, q} = q \<inter> invar"
  by (auto simp add: annquin_invar_def)

text "Simple abbreviation for particular order of parameters"

abbreviation annquin_valid ::
  "'a annquin \<Rightarrow> bool" where
  "annquin_valid rgac \<equiv> case rgac of (AnnQuin pre rely ac guar post) \<Rightarrow>
   anncom_spec_valid pre rely guar post ac"

lemma annquin_simp:
  "annquin_valid (AnnQuin p r c g q) = anncom_spec_valid p r g q c" (* {p,r} c {g,q} *)
  by simp

abbreviation annquin_keyword_invar ::
  "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a anncom \<Rightarrow> 'a set \<Rightarrow> 'a annquin"
  ("rely:_ guar:_ inv:_ annotated'_code: {_} _ {_}") where
  "annquin_keyword_invar rely guar I pre ac post
    \<equiv> {pre, rely} ac \<sslash> I {guar, post}"

(*============================================================================*)
subsection \<open>Parallel Compositions\<close>

subsubsection \<open>Binary Parallel\<close>

text \<open>Abbreviate all helpers that specialise quantification over n threads to two threads.\<close>
lemmas binpar_from_gen_simps = simp_all_2 simp_gen_Un_2 simp_gen_Un_2_not0 simp_gen_Int_2

text "Encapsulate two processes working parallel, along with the global r/g/p/q"
datatype 'a binary_par_with_rg = ParCode
    "'a set "" 'a rel "" 'a annquin "" 'a annquin "" 'a rel "" 'a set "  ("{_,_} _ \<parallel>a _ {_,_}")

text "Alternative syntax using keywords and bringing g/q up front"
abbreviation binary_par_with_rg_keywords:: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a annquin \<Rightarrow> 'a annquin \<Rightarrow>  'a binary_par_with_rg"
  ("global'_init: _ global'_rely: _ global'_guar: _ global'_post: _ _ \<parallel>a _") where
  "global_init: i global_rely: R global_guar: G global_post: Q c1 \<parallel>a c2 \<equiv> {i, R} c1 \<parallel>a c2 {G, Q}"

text "Make explicit the proof obligations for two processes working in parallel, using the above data type"
fun valid_binary_parallel_composition:: "'a binary_par_with_rg \<Rightarrow> bool" ("validpar:_") where
  "validpar: {init, gr} ac1 \<parallel>a ac2 {gg, final} = 
    ((annquin_valid ac1) \<and>
     (annquin_valid ac2) \<and>
      init \<subseteq> preOf ac1 \<inter> preOf ac2 \<and>
      gr \<subseteq> relyOf ac1 \<inter> relyOf ac2 \<and>
      guarOf ac1 \<subseteq> relyOf ac2 \<and> guarOf ac2 \<subseteq> relyOf ac1 \<and>
      guarOf ac1 \<union> guarOf ac2 \<subseteq> gg \<and>
      postOf ac1 \<inter> postOf ac2 \<subseteq> final)"

text "Make explicit the proof obligations for two processes working in parallel, using the above data type"
lemma valid_binary_parallel_composition_expand:
  "validpar: {init, gr} (rely: r1 guar: g1 annotated_code: {p1}c1{q1}) \<parallel>a (rely: r2 guar: g2 annotated_code: {p2}c2{q2}) {gg, final} = 
    (annquin_valid (rely: r1 guar: g1 annotated_code: {p1}c1{q1}) \<and>
     annquin_valid (rely: r2 guar: g2 annotated_code: {p2}c2{q2}) \<and>
      init \<subseteq> p1 \<inter> p2 \<and>
      gr \<subseteq> r1 \<inter> r2 \<and>
      g1 \<subseteq> r2 \<and> g2 \<subseteq> r1 \<and>
      g1 \<union> g2 \<subseteq> gg \<and>
      q1 \<inter> q2 \<subseteq> final)"
  by auto

text "The following theorem shows that the conditions of ``expand satisfiability binpar'' above are sufficient for the relevant proof in original PN style"
theorem valid_binary_parallel:
 "validpar: {init,gr}
 (rely: r1 guar: g1 annotated_code: {p1} c1 {q1}) \<parallel>a (rely: r2 guar: g2 annotated_code: {p2} c2 {q2}) 
           {gg,final}
 \<Longrightarrow> \<turnstile> COBEGIN (anncom_to_com c1, p1, r1, g1, q1) \<parallel> (anncom_to_com c2, p2, r2, g2, q2) 
       COEND SAT [init, gr, gg, final]"
  apply auto[1]
  apply(rule Parallel)
      apply (simp add: binpar_from_gen_simps)
     using less_Suc_eq apply auto
  by (simp add: anncom_spec_valid_sound)+

text "..and again but for existence of such"
theorem valid_binary_parallel_exists:
 "validpar: {init,gr}
 (rely: r1 guar: g1 annotated_code: {p1} c1 {q1}) \<parallel>a (rely: r2 guar: g2 annotated_code: {p2} c2 {q2}) 
            {gg,final}
 \<Longrightarrow> {init, gr} anncom_to_com c1 \<parallel> anncom_to_com c2 {gg, final}"
  by (meson valid_binary_parallel)

theorem valid_binary_parallel_exists_annotated:
  assumes "validpar:
          {init,gr}
          (rely: r1 guar: g1 annotated_code: {p1} c1' {q1}) \<parallel>a
          (rely: r2 guar: g2 annotated_code: {p2} c2' {q2}) 
          {gg,final}"
     and "anncom_to_com c1' = c1"
     and "anncom_to_com c2' = c2"
   shows "{init, gr} c1 \<parallel> c2 {gg, final}"
  using assms by (meson valid_binary_parallel)

theorem valid_binary_par:
  assumes
    "annquin_valid ac1" and
    "annquin_valid ac2" and
      "init \<subseteq> preOf ac1 \<inter> preOf ac2" and
      "gr \<subseteq> relyOf ac1 \<inter> relyOf ac2" and
      "guarOf ac1 \<subseteq> relyOf ac2 \<and> guarOf ac2 \<subseteq> relyOf ac1" and
      "guarOf ac1 \<union> guarOf ac2 \<subseteq> gg" and
      "postOf ac1 \<inter> postOf ac2 \<subseteq> final" 
    shows
  "validpar: {init, gr} ac1 \<parallel>a ac2 {gg, final}  "
  apply(simp only: valid_binary_parallel_composition.simps)
  using assms by auto


(*----------------------------------------------------------------------------*)
subsubsection \<open>Multi-Parallel\<close>

datatype 'a multi_par_with_rg = MultiParCode
  "'a  set" (* global init *)
  "'a  rel" (* global rely *)
   nat nat  (* indices *)
  "nat \<Rightarrow> 'a annquin" (* indexed program *)
  "'a  rel" (* global guar *)
  "'a  set" (* global post *)

syntax multi_parallel_anno ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> idt \<Rightarrow> nat \<Rightarrow>
   ('a annquin) \<Rightarrow>
   'a rel \<Rightarrow> 'a set \<Rightarrow> 'a multi_par_with_rg"
  ("annotated global'_init: _ global'_rely: _ \<parallel>  _ < _ @ _ global'_guar: _ global'_post: _") 

syntax multi_parallel_anno_lo_hi ::
  "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> idt \<Rightarrow> nat \<Rightarrow> 
   ('a annquin) \<Rightarrow>
   'a rel \<Rightarrow> 'a set \<Rightarrow> 'a multi_par_with_rg"
  ("annotated global'_init: _ global'_rely: _ \<parallel>  _ \<le> _ < _ @ _ global'_guar: _ global'_post: _") 

translations 
  "annotated global_init: Init global_rely: RR \<parallel> i < N @
    rgac global_guar: GG global_post: QQ"
  \<rightharpoonup> "CONST MultiParCode Init RR 0 N (\<lambda>i. rgac) GG QQ"

  "annotated global_init: Init global_rely: RR \<parallel> lo \<le> i < hi @
    rgac global_guar: GG global_post: QQ"
  \<rightharpoonup> "CONST MultiParCode Init RR lo hi (\<lambda>i. rgac) GG QQ"


abbreviation nat_range_set_neq_i:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" ("{_..<_\<noteq>_}") where
  "nat_range_set_neq_i lo hi x \<equiv> {lo..<hi} - {x}"

text "Proof obligations for N processes working in parallel, using the above data type"
fun valid_multi_parallel_composition:: "'a multi_par_with_rg \<Rightarrow> bool" ("valid'_multipar:_") where
  "valid_multipar: MultiParCode init RR lo N iac gg final =
   ( (\<forall>i\<in>{lo..<N}. annquin_valid (iac i)) \<and>
      init \<subseteq> (\<Inter>i\<in>{lo..<N}.  preOf (iac i)) \<and>
      RR \<subseteq> (\<Inter>i\<in>{lo..<N}. relyOf (iac i)) \<and>
      (\<forall>i\<in>{lo..<N}. guarOf (iac i) \<subseteq> (\<Inter>j\<in>{lo..<N\<noteq>i}. relyOf (iac j))) \<and>
      (\<Union>i\<in>{lo..<N}. guarOf (iac i)) \<subseteq> gg \<and>
      (\<Inter>i\<in>{lo..<N}. postOf (iac i)) \<subseteq> final )"

fun valid_multi_parallel_composition_offset:: "'a multi_par_with_rg \<Rightarrow> bool" ("valid'_multipar'_offset:_") where
  "valid_multipar_offset: MultiParCode init RR lo N iac gg final =
   ( (\<forall>i<(N-lo). annquin_valid (iac (lo + i))) \<and>
      init \<subseteq> (\<Inter>i<(N-lo).  preOf (iac (lo + i))) \<and>
      RR \<subseteq> (\<Inter>i<(N-lo). relyOf (iac (lo + i))) \<and>
      (\<forall>i<(N-lo). guarOf (iac (lo + i)) \<subseteq> (\<Inter>j\<in>{0..<(N-lo)\<noteq>i}. relyOf (iac (lo + j)))) \<and>
      (\<Union>i<(N-lo). guarOf (iac (lo + i))) \<subseteq> gg \<and>
      (\<Inter>i<(N-lo). postOf (iac (lo + i))) \<subseteq> final )"

lemma Int_set_range_to_offset: "(\<Inter>i\<in>{lo..<hi::nat}.  f i) = (\<Inter>i<(hi-lo).  f (lo + i))"
  apply auto
  by (metis add.commute le_iff_add lessThan_iff less_diff_conv)

lemma Un_set_range_to_offset: "(\<Union>i\<in>{lo..<hi::nat}.  g (f i)) = (\<Union>i<(hi-lo).  g (f (lo + i)))"
  apply auto
  apply (metis add_diff_cancel_left' diff_less_mono le_Suc_ex lessThan_iff)
  by (metis add.commute atLeastLessThan_iff le_add1 less_diff_conv)

lemma Int_set_range_neq_to_offset: "i = lo + ii \<Longrightarrow> (\<Inter>j\<in>{lo..<hi\<noteq>i}.  f j) = (\<Inter>j\<in>{0..<(hi-lo)\<noteq> ii}.  f (lo + j))"
  apply (auto simp add: Ball_def Bex_def image_def)
  apply (metis add.commute add_left_imp_eq le_add1 less_diff_conv)
  by (metis Nat.add_diff_assoc add_diff_cancel_left' diff_less_mono)

lemma forall_range_to_offset: "(\<forall>i\<in>{lo..<(hi::nat)}. P i) \<longleftrightarrow> (\<forall>i\<in>{0..<(hi - lo)}. P (lo + i))"
  apply (auto simp add: Ball_def)
  by (metis Nat.add_diff_assoc add_diff_cancel_left' diff_less_mono)

lemma valid_multipar_offset_equiv: "valid_multipar: MultiParCode init RR lo hi iac gg final \<longleftrightarrow>
  valid_multipar_offset: MultiParCode init RR lo hi iac  gg final"
  apply simp
  apply (intro conjI iffI impI ; elim conjE)
             apply (simp_all add: Int_set_range_to_offset Un_set_range_to_offset)
    apply(simp add: Ball_def)
  using Int_set_range_neq_to_offset
    apply (smt (verit, ccfv_SIG) Sup.SUP_cong add.commute le_add1 less_diff_conv)
   apply (smt (verit, best) add.commute atLeastLessThan_iff le_iff_add less_diff_conv)
  apply(simp only: forall_range_to_offset[of lo hi] Int_set_range_neq_to_offset)
  by (metis atLeastLessThan_iff)

text "Discharging a ``valid multipar'' wrapped around the syntax of a multiway composition (with proof annotations) 
proves the relevant top-level theorem in PN"

lemma valid_multipar: 
  assumes "valid_multipar: MultiParCode Init RR lo N rgac GG QQ"
  shows "\<turnstile> COBEGIN SCHEME [lo \<le> i < N] (
         CONST anncom_to_com (cmdOf (rgac i)),
          preOf (rgac i),
          relyOf (rgac i),
          guarOf (rgac i) ,
          postOf (rgac i) 
        ) COEND
     SAT [Init, RR , GG, QQ]"
  apply (rule Parallel)
  using assms 
      apply (auto simp add: subset_iff)
     apply(simp_all add: Ball_def)
     apply (metis add.commute add_right_cancel le_add1 less_diff_conv)
    apply (metis add.commute atLeastLessThan_iff le_add1 less_diff_conv)
   apply (metis add.commute add_diff_inverse_nat less_diff_conv not_le)
  by (smt (verit) add.commute anncom_spec_valid_sound annquin_simp bot_nat_0.extremum cmdOf.simps guarOf.simps le_add_same_cancel1 less_diff_conv postOf.elims preOf.simps relyOf.simps)

lemma valid_multipar_with_internal_rg: 
  assumes "valid_multipar: MultiParCode Init RR lo N (\<lambda>i. {p i, r i} ac i {g i, q i}) GG QQ"
and "\<forall>i. anncom_to_com (ac i) = c i"
shows "\<turnstile> COBEGIN SCHEME [lo \<le> i < N] (c i, p i, r i, g i, q i) COEND
     SAT [Init, RR , GG, QQ]"
  apply(rule Parallel)
  using assms apply (simp_all add: subset_iff)
  apply(auto simp add: Ball_def)[1]
  apply (metis add.commute add_left_imp_eq le_add1 less_diff_conv)
  apply (metis add.commute atLeastLessThan_iff le_add1 less_diff_conv)
  apply (metis add.commute atLeastLessThan_iff less_diff_conv nat_le_iff_add)
  by (metis add.commute anncom_spec_valid_sound atLeastLessThan_iff le_add1 less_diff_conv)

theorem valid_multipar_explicit:
  assumes 
    local_sat: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> annquin_valid (iac i)" and
    pre:  "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> init \<subseteq>  preOf (iac i)" and
    rely: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> RR \<subseteq> relyOf (iac i)" and     
    guar_imp_rely: "\<And>i j. lo \<le> i \<and> i<N \<Longrightarrow> lo \<le> j \<and> j < N \<Longrightarrow> i \<noteq> j \<Longrightarrow> guarOf (iac i) \<subseteq> relyOf (iac j)" and 
    guar: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> guarOf (iac i) \<subseteq> gg" and 
    post: "(\<Inter>i\<in>{lo..<N}. postOf (iac i)) \<subseteq> final"
    shows "valid_multipar: MultiParCode init RR lo N iac gg final"
  using assms apply auto
  by blast+

theorem valid_multipar_offset_explicit:
  assumes 
    local_sat: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> annquin_valid (iac i)" and
    pre:  "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> init \<subseteq>  preOf (iac i)" and
    rely: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> RR \<subseteq> relyOf (iac i)" and     
    guar_imp_rely: "\<And>i j. lo \<le> i \<and> i<N \<Longrightarrow> lo \<le> j \<and> j < N \<Longrightarrow> i \<noteq> j \<Longrightarrow> guarOf (iac i) \<subseteq> relyOf (iac j)" and 
    guar: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> guarOf (iac i) \<subseteq> gg" and 
    post: "(\<Inter>i\<in>{lo..<N}. postOf (iac i)) \<subseteq> final"
  shows "valid_multipar_offset: MultiParCode init RR lo N iac gg final"
  apply(simp flip: valid_multipar_offset_equiv )
  using assms apply auto
  apply (auto simp add: subset_iff Ball_def Bex_def image_def)
  apply (metis add.commute add_right_cancel le_add2 less_diff_conv)
  apply (metis add.commute le_add1 less_diff_conv)
  by (metis le_add_diff_inverse le_add_diff_inverse2 less_diff_conv)

lemma LT_offset: "(\<forall>i. lo \<le> i \<and> i < (N::nat) \<longrightarrow> P i) \<longleftrightarrow> (\<forall>i<N - lo. P (lo + i))"
  by (metis add.commute le_add1 le_add_diff_inverse2 less_diff_conv)

theorem valid_multipar_explicit2:
  assumes 
    local_sat: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> annquin_valid {p i,r i} c i {g i ,q i}" and
    pre:  "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> init \<subseteq>  p i" and
    rely: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> RR \<subseteq> r i" and     
    guar_imp_rely: "\<And>i j. lo \<le> i \<and> i<N \<Longrightarrow> lo \<le> j \<and> j < N \<Longrightarrow> i \<noteq> j \<Longrightarrow> g i \<subseteq> r j" and 
    guar: "\<And>i. lo \<le> i \<and> i < N \<Longrightarrow> g i \<subseteq> gg" and 
    post: "(\<Inter>i\<in>{lo..<N}. q i) \<subseteq> final"
    shows "valid_multipar: MultiParCode init RR lo N (\<lambda>i. {p i,r i} c i {g i ,q i}) gg final"
  using assms LT_offset by (auto simp add: subset_iff)

text "With explicit invariant abbreviation"
theorem valid_multipar_explicit_with_invariant:
  assumes 
    local_sat: "\<And>i. i < N \<Longrightarrow> annquin_valid {p i,r i} c i \<sslash> Inv {g i ,q i}" and
    pre:  "\<And>i. i < N \<Longrightarrow> init \<subseteq>  p i \<inter> Inv" and
    rely: "\<And>i. i < N \<Longrightarrow> RR \<subseteq> lift_rely Inv (r i)" and     
    guar_imp_rely: "\<And>i j. i<N \<Longrightarrow> j < N \<Longrightarrow> i \<noteq> j \<Longrightarrow> lift_guar Inv (g i) \<subseteq> r j" and 
    guar: "\<And>i. i < N \<Longrightarrow> lift_guar Inv (g i) \<subseteq> gg" and 
    post: "(\<Inter>i<N. q i \<inter> Inv) \<subseteq> final"
  shows "valid_multipar: MultiParCode init RR 0 N (\<lambda>i. {p i,r i} c i \<sslash> Inv {g i ,q i}) gg final"
  apply (rule valid_multipar_explicit)
  using assms
       apply (simp only: annquin_invar_def)
      apply (metis annquin_invar_def pre preOf.simps)
     apply (simp add: annquin_invar_def)
  using rely 
     apply simp
    apply (simp add: annquin_invar_def subset_iff)
  apply clarsimp
  using guar_imp_rely apply fastforce
   apply (simp add: annquin_invar_def)
  using guar annquin_invar_def
   apply auto[1]
  apply (simp add: annquin_invar_def)
  using post by fastforce

method method_annquin_multi_parallel =
  rule valid_multipar_explicit2,
  goal_cases local_sat pre rely guar_imp_rely guar post

(*----------------------------------------------------------------------------*)
subsubsection \<open>Ternary Parallel\<close>

abbreviation triple_par_with_rg ::
    "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a annquin \<Rightarrow> 'a annquin \<Rightarrow> 'a annquin \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a multi_par_with_rg"  ("{_,_} _ \<parallel>3 _ \<parallel>3 _ {_,_}")
    where
      "{I, R} p1 \<parallel>3 p2 \<parallel>3 p3 {G,Q} \<equiv> 
        MultiParCode I R 0 3 (\<lambda>i. case i of 0 \<Rightarrow> p1 | Suc 0 \<Rightarrow> p2 | Suc (Suc 0) \<Rightarrow> p3) G Q"

theorem valid_3way_parallel_composition:
  assumes 
    "annquin_valid {p1,r1} c1 {g1,q1}"
    "annquin_valid {p2,r2} c2 {g2,q2}"
    "annquin_valid {p3,r3} c3 {g3,q3}"
    "I \<subseteq> p1 \<inter> p2 \<inter> p3"
    "R \<subseteq> r1 \<inter> r2 \<inter> r3"
    "g1 \<subseteq> r2 \<inter> r3"
    "g2 \<subseteq> r1 \<inter> r3"
    "g3 \<subseteq> r1 \<inter> r2"
    "g1 \<union> g2 \<union> g3 \<subseteq> G "
    "q1 \<inter> q2 \<inter> q3 \<subseteq> Q"
  shows   "valid_multipar: ({I, R} ({p1,r1} c1 {g1,q1}) \<parallel>3 ({p2,r2}c2{g2,q2}) \<parallel>3 ({p3,r3}c3{g3,q3}) {G,Q})"
  apply auto
  using assms
       apply (simp_all add: subset_iff)
  subgoal for i apply (cases i; simp)
    subgoal for nat by(cases nat; simp)
    done
      apply(auto  split: nat.split)
    apply (metis (no_types, lifting) guarOf.simps less_2_cases linorder_neqE_nat nat.case(2) not_less_eq numeral_3_eq_3 numerals(2) old.nat.simps(4) relyOf.simps)
   apply (metis Nitpick.case_nat_unfold add_diff_cancel_left' guarOf.simps less_2_cases less_Suc_eq numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc)
  apply(auto simp add: Ball_def)
  by (metis bot_nat_0.extremum_strict lessI less_Suc_numeral nat.case(2) not_less_iff_gr_or_eq numerals(2) old.nat.simps(4) postOf.simps pred_numeral_simps(3))

theorem  valid_3way_parallel_composition_with_invariant:
  assumes 
    "annquin_valid {p1,r1} c1 \<sslash>invar {g1,q1}" and
    "annquin_valid {p2,r2} c2 \<sslash>invar {g2,q2}" and
    "annquin_valid {p3,r3} c3 \<sslash>invar {g3,q3}" and
    "I \<subseteq> invar" and
    "I \<subseteq> p1" and "I \<subseteq> p2" and "I \<subseteq> p3" and
    "R \<subseteq> lift_rely invar r1" and "R \<subseteq> lift_rely invar r2" and "R \<subseteq> lift_rely invar r3" and 
    "lift_guar invar g1 \<subseteq> r2" and "lift_guar invar g1 \<subseteq> r3" and
    "lift_guar invar g2 \<subseteq> r1" and "lift_guar invar g2 \<subseteq> r3" and
    "lift_guar invar g3 \<subseteq> r1" and "lift_guar invar g3 \<subseteq> r2" and
    "Restr g1 invar \<subseteq> G" and "Restr g2 invar \<subseteq> G" and "Restr g3 invar \<subseteq> G" and
    "Id \<subseteq> G" and 
    "q1 \<inter> q2 \<inter> q3 \<inter> invar \<subseteq> Q"
  shows   "valid_multipar: ({I, R} ({p1,r1} c1 \<sslash> invar {g1,q1}) \<parallel>3 ({p2,r2}c2 \<sslash> invar{g2,q2}) \<parallel>3 ({p3,r3}c3\<sslash> invar{g3,q3}) {G,Q})"
  apply(simp only: annquin_invar_def)
  apply(rule valid_3way_parallel_composition)
           apply (metis annquin_invar_def assms(1))
          apply (metis annquin_invar_def assms(2))
         apply (metis annquin_invar_def assms(3))
  using assms(4) assms(5) assms(6) assms(7)
        apply auto[1]
       apply (simp add: assms(10) assms(8) assms(9))
  using assms(10) assms(8) assms(9) apply force
  using assms(11) assms(12) apply auto[1]
  using assms(13) assms(14) apply auto[1]
  using assms(15) assms(16) apply auto[1]
  using assms(17) assms(18) assms(19) apply auto[1]

   apply (simp add: assms(17) assms(18) assms(19))
  using assms(20) apply blast
  using assms(21) by blast

end
