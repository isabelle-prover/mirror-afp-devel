section \<open>Compiler-style equality-saturation certificates\<close>

theory Examples_Compiler
  imports
    EGraph_Explanations
    Extraction_Certificates
    Bounded_Certificate_Search
begin

datatype csym = CMul | CAdd | CShl | COne | CTwo
datatype cvar = VX | VY

abbreviation (input) cmul ::
  "(csym, cvar) term \<Rightarrow> (csym, cvar) term \<Rightarrow> (csym, cvar) term"
  (infixl \<open>\<otimes>\<close> 70) where
  "a \<otimes> b \<equiv> Fun CMul [a, b]"

abbreviation (input) cadd ::
  "(csym, cvar) term \<Rightarrow> (csym, cvar) term \<Rightarrow> (csym, cvar) term"
  (infixl \<open>\<oplus>\<close> 65) where
  "a \<oplus> b \<equiv> Fun CAdd [a, b]"

abbreviation (input) cshl ::
  "(csym, cvar) term \<Rightarrow> (csym, cvar) term \<Rightarrow> (csym, cvar) term"
  (infixl \<open>\<lless>\<close> 60) where
  "a \<lless> b \<equiv> Fun CShl [a, b]"

abbreviation (input) cone :: "(csym, cvar) term" where
  "cone \<equiv> Fun COne []"
abbreviation (input) ctwo :: "(csym, cvar) term" where
  "ctwo \<equiv> Fun CTwo []"
abbreviation (input) vx :: "(csym, cvar) term" where
  "vx \<equiv> Var VX"
abbreviation (input) vy :: "(csym, cvar) term" where
  "vy \<equiv> Var VY"

definition R_comp :: "(csym, cvar) rule list" where
  "R_comp =
    [ (vx \<otimes> ctwo, vx \<oplus> vx)
    , (vx \<lless> cone, vx \<oplus> vx) ]"

subsection \<open>Positional rule explanations\<close>

definition t_strength :: "(csym, cvar) term" where
  "t_strength = (vx \<lless> cone) \<oplus> (vy \<otimes> ctwo)"

definition u_strength :: "(csym, cvar) term" where
  "u_strength = (vx \<oplus> vx) \<oplus> (vy \<oplus> vy)"

definition strength_steps :: "(csym, cvar) certificate_step list" where
  "strength_steps =
    [ Rule_At [0] 1 Forward Var
    , Rule_At [Suc 0] 0 Forward
        (\<lambda>v. if v = VX then vy else Var v) ]"

lemma strength_certificate:
  "check_explanation R_comp [] strength_steps t_strength u_strength"
  by (simp add: check_explanation_def R_comp_def strength_steps_def
      t_strength_def u_strength_def)

theorem strength_reduction_conversion:
  "(t_strength, u_strength) \<in> (rstep (set R_comp))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_rule_explanation_sound[OF strength_certificate])

subsection \<open>Chronological merge reuse\<close>

definition compiler_log :: "(csym, cvar) merge_log" where
  "compiler_log =
    [ ((vx \<otimes> ctwo, vx \<oplus> vx),
        [Rule_At [] 0 Forward Var])
    , ((vy \<otimes> ctwo, vy \<oplus> vy),
        [Rule_At [] 0 Forward
          (\<lambda>v. if v = VX then vy else Var v)]) ]"

lemma compiler_log_accepted:
  "check_merge_log R_comp compiler_log"
  by (simp add: check_merge_log_def compiler_log_def
      check_explanation_def R_comp_def)

definition t_merge :: "(csym, cvar) term" where
  "t_merge = (vx \<otimes> ctwo) \<oplus> (vy \<otimes> ctwo)"

definition u_merge :: "(csym, cvar) term" where
  "u_merge = (vx \<oplus> vx) \<oplus> (vy \<oplus> vy)"

definition merge_reuse_steps :: "(csym, cvar) certificate_step list" where
  "merge_reuse_steps =
    [ Merge_At [0] 0 Forward
    , Merge_At [Suc 0] 1 Forward ]"

lemma merge_reuse_accepted:
  "check_explanation R_comp (recorded_merges compiler_log)
     merge_reuse_steps t_merge u_merge"
  by (simp add: check_explanation_def recorded_merges_def compiler_log_def
      merge_reuse_steps_def t_merge_def u_merge_def)

theorem recorded_merges_are_reusable:
  "(t_merge, u_merge) \<in> (rstep (set R_comp))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule egraph_explanation_sound[
        OF compiler_log_accepted merge_reuse_accepted])

subsection \<open>Candidate-set extraction\<close>

fun compiler_cost :: "csym \<Rightarrow> nat" where
  "compiler_cost CMul = 4"
| "compiler_cost CShl = 4"
| "compiler_cost CAdd = 2"
| "compiler_cost COne = 1"
| "compiler_cost CTwo = 1"

definition compiler_extraction :: "(csym, cvar) extraction" where
  "compiler_extraction =
    \<lparr> ex_source = vx \<otimes> ctwo
    , ex_chosen = vx \<oplus> vx
    , ex_candidates =
        [ (vx \<oplus> vx, [Merge_At [] 0 Forward])
        , (vx \<otimes> ctwo, []) ] \<rparr>"

lemma compiler_extraction_accepted:
  "check_extraction compiler_cost R_comp
     (recorded_merges compiler_log) compiler_extraction"
  by (simp add: check_extraction_def check_explanation_def
      recorded_merges_def compiler_log_def compiler_extraction_def)

theorem compiler_extraction_correct:
  "(ex_source compiler_extraction, ex_chosen compiler_extraction)
     \<in> (rstep (set R_comp))\<^sup>\<leftrightarrow>\<^sup>*"
  "\<forall>v \<in> set (map fst (ex_candidates compiler_extraction)).
     term_cost compiler_cost (ex_chosen compiler_extraction)
       \<le> term_cost compiler_cost v"
  using extraction_over_checked_log_correct[
    OF compiler_log_accepted compiler_extraction_accepted] .

subsection \<open>Certificate production with AFP position enumeration\<close>

definition forward_generator ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) certificate_step list" where
  "forward_generator R t =
    [Rule_At p i Forward Var.
      p \<leftarrow> poss_list t, i \<leftarrow> [0 ..< length R]]"

definition zero :: "(string, string) term" where
  "zero = Fun ''0'' []"
definition aval :: "(string, string) term" where
  "aval = Fun ''a'' []"
definition bval :: "(string, string) term" where
  "bval = Fun ''b'' []"
definition plus_term ::
  "(string, string) term \<Rightarrow> (string, string) term \<Rightarrow>
    (string, string) term" where
  "plus_term s t = Fun ''+'' [s, t]"
definition times_term ::
  "(string, string) term \<Rightarrow> (string, string) term \<Rightarrow>
    (string, string) term" where
  "times_term s t = Fun ''*'' [s, t]"

definition demo_rules :: "(string, string) rule list" where
  "demo_rules =
    [(plus_term aval zero, aval), (plus_term bval zero, bval)]"
definition demo_start :: "(string, string) term" where
  "demo_start = times_term (plus_term aval zero) (plus_term bval zero)"
definition demo_result :: "(string, string) term" where
  "demo_result = times_term aval bval"

lemma demo_search_succeeds:
  "find_explanation demo_rules [] (forward_generator demo_rules) 2
     demo_start demo_result \<noteq> None"
  by eval

theorem produced_certificate_is_sound:
  "(demo_start, demo_result) \<in> (rstep (set demo_rules))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from demo_search_succeeds obtain sts where found:
    "find_explanation demo_rules [] (forward_generator demo_rules) 2
       demo_start demo_result = Some sts"
    by blast
  show ?thesis by (rule find_explanation_sound[OF _ found]) simp
qed

end
