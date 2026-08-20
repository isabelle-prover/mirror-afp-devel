section \<open>Importing egg flat explanations\<close>

theory Egg_Flat_Explanation
  imports
    Equality_Saturation_Checker
    First_Order_Terms.Matching
begin

text \<open>
  The public explanation API of egg 0.11.0 emits a flat proof as one
  S-expression per term.  The first term is unannotated.  Every later term
  contains exactly one subexpression of the form
  \<open>(Rewrite=> name term)\<close> or \<open>(Rewrite<= name term)\<close>.  The former rewrites
  the previous term to the current term; the latter applies the named rule to
  the current term to recover the previous term.

  This theory parses that actual textual format (for unquoted atoms), infers
  the substitution with the AFP matcher, compiles every annotation to
  \<^const>\<open>Rule_At\<close>, and finally invokes the independently verified checker.
  Parsing and compilation are therefore outside the trusted claim: malformed
  or mistranslated input is accepted only if replay against the AFP rewrite
  rules succeeds.
\<close>

datatype egg_token = Egg_LParen | Egg_RParen | Egg_Atom string

datatype egg_sexp = Egg_SAtom string | Egg_SList "egg_sexp list"

definition egg_whitespace :: "char set" where
  "egg_whitespace =
    {CHR '' '', CHR ''\<newline>'', CHR 0x09, CHR 0x0D}"

definition emit_egg_atom ::
  "string \<Rightarrow> egg_token list \<Rightarrow> egg_token list" where
  "emit_egg_atom atom toks =
    (if atom = [] then toks else Egg_Atom (rev atom) # toks)"

fun lex_egg ::
  "string \<Rightarrow> string \<Rightarrow> egg_token list \<Rightarrow> egg_token list" where
  "lex_egg [] atom toks = rev (emit_egg_atom atom toks)"
| "lex_egg (c # cs) atom toks =
    (if c \<in> egg_whitespace then
       lex_egg cs [] (emit_egg_atom atom toks)
     else if c = CHR ''('' then
       lex_egg cs [] (Egg_LParen # emit_egg_atom atom toks)
     else if c = CHR '')'' then
       lex_egg cs [] (Egg_RParen # emit_egg_atom atom toks)
     else
       lex_egg cs (c # atom) toks)"

definition tokenize_egg :: "string \<Rightarrow> egg_token list" where
  "tokenize_egg input = lex_egg input [] []"

fun parse_egg_tokens ::
  "egg_token list \<Rightarrow> egg_sexp list list \<Rightarrow> egg_sexp option" where
  "parse_egg_tokens [] stack =
    (case stack of
       [frame] \<Rightarrow>
         (case rev frame of [x] \<Rightarrow> Some x | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"
| "parse_egg_tokens (tok # toks) stack =
    (case tok of
       Egg_Atom atom \<Rightarrow>
         (case stack of
            [] \<Rightarrow> None
          | frame # frames \<Rightarrow>
              parse_egg_tokens toks ((Egg_SAtom atom # frame) # frames))
     | Egg_LParen \<Rightarrow> parse_egg_tokens toks ([] # stack)
     | Egg_RParen \<Rightarrow>
         (case stack of
            frame # parent # frames \<Rightarrow>
              parse_egg_tokens toks
                ((Egg_SList (rev frame) # parent) # frames)
          | _ \<Rightarrow> None))"

definition parse_egg_sexp :: "string \<Rightarrow> egg_sexp option" where
  "parse_egg_sexp input = parse_egg_tokens (tokenize_egg input) [[]]"

fun plain_egg_term ::
  "egg_sexp \<Rightarrow> (string, string) term option" where
  "plain_egg_term (Egg_SAtom atom) = Some (Fun atom [])"
| "plain_egg_term (Egg_SList xs) =
    (case xs of
       Egg_SAtom op_name # children \<Rightarrow>
         (if op_name = ''Rewrite=>'' \<or> op_name = ''Rewrite<='' then
            (case children of
               [Egg_SAtom name, body] \<Rightarrow> plain_egg_term body
             | _ \<Rightarrow> None)
          else map_option (Fun op_name)
            (Option_Monad.mapM plain_egg_term children))
     | _ \<Rightarrow> None)"

fun egg_annotations ::
  "egg_sexp \<Rightarrow> (pos \<times> direction \<times> string) list"
and egg_child_annotations ::
  "nat \<Rightarrow> egg_sexp list \<Rightarrow>
    (pos \<times> direction \<times> string) list" where
  "egg_annotations (Egg_SAtom atom) = []"
| "egg_annotations (Egg_SList xs) =
    (case xs of
       [Egg_SAtom op_name, Egg_SAtom name, body] \<Rightarrow>
         (if op_name = ''Rewrite=>'' then
            ([], Forward, name) # egg_annotations body
          else if op_name = ''Rewrite<='' then
            ([], Backward, name) # egg_annotations body
          else egg_child_annotations 0 [Egg_SAtom name, body])
     | Egg_SAtom op_name # children \<Rightarrow>
         egg_child_annotations 0 children
     | _ \<Rightarrow> [])"
| "egg_child_annotations i [] = []"
| "egg_child_annotations i (x # xs) =
    map (\<lambda>(p, d, name). (i # p, d, name)) (egg_annotations x) @
    egg_child_annotations (Suc i) xs"

record egg_mark =
  egg_pos :: pos
  egg_dir :: direction
  egg_rule_name :: string

record egg_decoded_line =
  egg_term :: "(string, string) term"
  egg_mark :: "egg_mark option"

definition decode_egg_line :: "string \<Rightarrow> egg_decoded_line option" where
  "decode_egg_line input =
    (case parse_egg_sexp input of
       None \<Rightarrow> None
     | Some sexp \<Rightarrow>
         (case plain_egg_term sexp of
            None \<Rightarrow> None
          | Some t \<Rightarrow>
              (case egg_annotations sexp of
                 [] \<Rightarrow> Some \<lparr>egg_term = t, egg_mark = None\<rparr>
               | [(p, d, name)] \<Rightarrow>
                   Some \<lparr>egg_term = t,
                     egg_mark = Some \<lparr>egg_pos = p, egg_dir = d,
                       egg_rule_name = name\<rparr>\<rparr>
               | _ \<Rightarrow> None)))"

type_synonym egg_named_rules =
  "(string \<times> (string, string) rule) list"

fun named_rule_index ::
  "string \<Rightarrow> egg_named_rules \<Rightarrow> nat option" where
  "named_rule_index name [] = None"
| "named_rule_index name ((other, r) # rules) =
    (if name = other then Some 0
     else map_option Suc (named_rule_index name rules))"

definition compile_egg_step ::
  "egg_named_rules \<Rightarrow> (string, string) term \<Rightarrow> string \<Rightarrow>
    ((string, string) certificate_step \<times> (string, string) term) option" where
  "compile_egg_step named previous input =
    (case decode_egg_line input of
       None \<Rightarrow> None
     | Some decoded \<Rightarrow>
         (case egg_mark decoded of
            None \<Rightarrow> None
          | Some mark \<Rightarrow>
              (case named_rule_index (egg_rule_name mark) named of
                 None \<Rightarrow> None
               | Some i \<Rightarrow>
                   (if egg_pos mark \<in> poss previous then
                      (case match (previous |_ egg_pos mark)
                              (fst (orient_pair (egg_dir mark)
                                (map snd named ! i))) of
                         None \<Rightarrow> None
                       | Some \<sigma> \<Rightarrow>
                           (let st = Rule_At (egg_pos mark) i
                               (egg_dir mark) \<sigma>
                            in if apply_step (map snd named) [] st previous =
                                  Some (egg_term decoded)
                               then Some (st, egg_term decoded)
                               else None))
                    else None))))"

fun compile_egg_tail ::
  "egg_named_rules \<Rightarrow> (string, string) term \<Rightarrow> string list \<Rightarrow>
    ((string, string) certificate_step list \<times>
      (string, string) term) option" where
  "compile_egg_tail named current [] = Some ([], current)"
| "compile_egg_tail named current (line # lines) =
    (case compile_egg_step named current line of
       None \<Rightarrow> None
     | Some (st, next) \<Rightarrow>
         (case compile_egg_tail named next lines of
            None \<Rightarrow> None
          | Some (sts, final) \<Rightarrow> Some (st # sts, final)))"

fun compile_egg_explanation ::
  "egg_named_rules \<Rightarrow> string list \<Rightarrow>
    (((string, string) term \<times> (string, string) term) \<times>
      (string, string) certificate_step list) option" where
  "compile_egg_explanation named [] = None"
| "compile_egg_explanation named (line # lines) =
    (case decode_egg_line line of
       None \<Rightarrow> None
     | Some decoded \<Rightarrow>
         (case egg_mark decoded of
            Some mark \<Rightarrow> None
          | None \<Rightarrow>
              (case compile_egg_tail named (egg_term decoded) lines of
                 None \<Rightarrow> None
               | Some (sts, final) \<Rightarrow>
                   Some ((egg_term decoded, final), sts))))"

definition check_egg_explanation ::
  "egg_named_rules \<Rightarrow> string list \<Rightarrow>
    (string, string) term \<Rightarrow> (string, string) term \<Rightarrow> bool" where
  "check_egg_explanation named lines expected_start expected_final =
    (case compile_egg_explanation named lines of
       None \<Rightarrow> False
     | Some ((start, final), sts) \<Rightarrow>
         start = expected_start \<and> final = expected_final \<and>
         check_explanation (map snd named) [] sts start final)"

theorem check_egg_explanation_sound:
  assumes "check_egg_explanation named lines start final"
  shows "(start, final)
    \<in> (rstep (set (map snd named)))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from assms obtain sts where
    "check_explanation (map snd named) [] sts start final"
    unfolding check_egg_explanation_def
    by (auto split: option.splits prod.splits)
  then show ?thesis by (rule check_rule_explanation_sound)
qed

end
