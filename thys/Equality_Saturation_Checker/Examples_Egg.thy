section \<open>End-to-end fixtures emitted by egg 0.11.0\<close>

theory Examples_Egg
  imports Egg_Flat_Explanation
begin

text \<open>
  The first two traces below are literal elements returned by egg 0.11.0's
  flat-string explanation API.  They were generated deterministically with
  explanation-length optimization disabled.  Egg's own proof checker validated
  both traces.  The pinned package checksum and generator setup are recorded in
  the AFP document and README.  The generator used the four named pattern rules
  below in the order given by \<^verbatim>\<open>egg_compiler_rules\<close>.
\<close>

definition egg_compiler_rules :: egg_named_rules where
  "egg_compiler_rules =
    [ (''mul-two'',
        (Fun ''*'' [Var ''x'', Fun ''2'' []],
         Fun ''+'' [Var ''x'', Var ''x'']))
    , (''shl-one'',
        (Fun ''shl'' [Var ''x'', Fun ''1'' []],
         Fun ''+'' [Var ''x'', Var ''x'']))
    , (''mul-one'',
        (Fun ''*'' [Var ''x'', Fun ''1'' []],
         Var ''x''))
    , (''add-zero'',
        (Fun ''+'' [Var ''x'', Fun ''0'' []],
         Var ''x'')) ]"

definition egg_compiler_start :: "(string, string) term" where
  "egg_compiler_start =
    Fun ''+''
      [Fun ''shl'' [Fun ''x'' [], Fun ''1'' []],
       Fun ''*'' [Fun ''y'' [], Fun ''2'' []]]"

definition egg_compiler_final :: "(string, string) term" where
  "egg_compiler_final =
    Fun ''+''
      [Fun ''+'' [Fun ''x'' [], Fun ''x'' []],
       Fun ''+'' [Fun ''y'' [], Fun ''y'' []]]"

definition egg_compiler_flat_output :: "string list" where
  "egg_compiler_flat_output =
    [''(+ (shl x 1) (* y 2))'',
     ''(+ (Rewrite=> shl-one (+ x x)) (* y 2))'',
     ''(+ (+ x x) (Rewrite=> mul-two (+ y y)))'']"

lemma egg_compiler_fixture_accepted:
  "check_egg_explanation egg_compiler_rules egg_compiler_flat_output
    egg_compiler_start egg_compiler_final"
  by eval

theorem egg_compiler_explanation_sound:
  "(egg_compiler_start, egg_compiler_final)
    \<in> (rstep (set (map snd egg_compiler_rules)))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_egg_explanation_sound[OF egg_compiler_fixture_accepted])

text \<open>
  The second fixture reverses the query order after egg has applied
  \<open>mul-one\<close>.  It therefore exercises egg's actual \<open>Rewrite<=\<close> convention:
  applying \<open>mul-one\<close> left-to-right to the current annotated term recovers the
  previous term.
\<close>

definition egg_backward_start :: "(string, string) term" where
  "egg_backward_start = Fun ''z'' []"

definition egg_backward_final :: "(string, string) term" where
  "egg_backward_final = Fun ''*'' [Fun ''z'' [], Fun ''1'' []]"

definition egg_backward_flat_output :: "string list" where
  "egg_backward_flat_output =
    [''z'', ''(Rewrite<= mul-one (* z 1))'']"

lemma egg_backward_fixture_accepted:
  "check_egg_explanation egg_compiler_rules egg_backward_flat_output
    egg_backward_start egg_backward_final"
  by eval

theorem egg_backward_explanation_sound:
  "(egg_backward_start, egg_backward_final)
    \<in> (rstep (set (map snd egg_compiler_rules)))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_egg_explanation_sound[OF egg_backward_fixture_accepted])

text \<open>
  The third egg trace is a parser regression fixture.  Its enclosing binary
  node has an atomic first child and an annotated second child, so the rewrite
  must be located at AFP position \<open>[1]\<close>.
\<close>

definition egg_atomic_child_start :: "(string, string) term" where
  "egg_atomic_child_start =
    Fun ''f''
      [Fun ''y'' [],
       Fun ''+'' [Fun ''z'' [], Fun ''0'' []]]"

definition egg_atomic_child_final :: "(string, string) term" where
  "egg_atomic_child_final = Fun ''f'' [Fun ''y'' [], Fun ''z'' []]"

definition egg_atomic_child_flat_output :: "string list" where
  "egg_atomic_child_flat_output =
    [''(f y (+ z 0))'', ''(f y (Rewrite=> add-zero z))'']"

lemma egg_atomic_child_fixture_accepted:
  "check_egg_explanation egg_compiler_rules egg_atomic_child_flat_output
    egg_atomic_child_start egg_atomic_child_final"
  by eval

theorem egg_atomic_child_explanation_sound:
  "(egg_atomic_child_start, egg_atomic_child_final)
    \<in> (rstep (set (map snd egg_compiler_rules)))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_egg_explanation_sound[
        OF egg_atomic_child_fixture_accepted])

subsection \<open>Rejecting malformed or unsupported traces\<close>

lemma egg_multiple_annotations_rejected:
  "decode_egg_line
    ''(+ (Rewrite=> mul-one x) (Rewrite=> mul-one y))'' = None"
  by eval

lemma egg_unknown_rule_rejected:
  "\<not> check_egg_explanation egg_compiler_rules
    [''x'', ''(Rewrite=> unknown y)'']
    (Fun ''x'' []) (Fun ''y'' [])"
  by eval

end
