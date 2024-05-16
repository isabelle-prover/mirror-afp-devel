(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter \<open>Setup Lex / Yacc and Translation from C to Simpl\<close>

theory CTranslationSetup
  imports
  "UMM"
  "PackedTypes"
  "PrettyProgs"
  "StaticFun"
  "IndirectCalls"
  "ModifiesProofs"
  "HOL-Eisbach.Eisbach"
  "ML_Record_Antiquotation"
  "Option_Scanner"
  "Misc_Antiquotation"
  "MkTermAntiquote"
  "TermPatternAntiquote"
  "CLocals"
keywords
  "cond_sorry_modifies_proofs" :: thy_decl
and
  "mllex"
  "mlyacc":: thy_load 
begin


ML \<open>
structure Coerce_Syntax =
struct

  val show_types = Ptr_Syntax.show_ptr_types

  fun coerce_tr' cnst ctxt typ ts = if Config.get ctxt show_types then
      case Term.strip_type typ of
        ([S], T) =>
          list_comb
            (Syntax.const cnst $ Syntax_Phases.term_of_typ ctxt S
                               $ Syntax_Phases.term_of_typ ctxt T
            , ts)
        | _ => raise Match
  else raise Match
end
\<close>

definition coerce::"'a::mem_type \<Rightarrow> 'b::mem_type" where
  "coerce v = from_bytes (to_bytes_p v)"

syntax
  "_coerce" :: "type \<Rightarrow> type \<Rightarrow> logic" ("(1COERCE/(1'(_ \<rightarrow> _')))")
translations
  "COERCE('a \<rightarrow> 'b)" => "CONST coerce :: ('a  \<Rightarrow> 'b)"
typed_print_translation
  \<open> [(@{const_syntax coerce}, Coerce_Syntax.coerce_tr' @{syntax_const "_coerce"})] \<close>

lemma coerce_id[simp]: 
  shows "coerce v = v"
  by (simp add: coerce_def)

lemma coerce_cancel_packed[simp]:
  fixes v::"'a::packed_type"
  assumes sz_eq: "size_of (TYPE('a)) = size_of (TYPE('b))"
  shows "coerce ((coerce v)::'b::packed_type) = v"
  using assms
  apply (simp add: coerce_def)
  by (metis (mono_tags, lifting) access_ti\<^sub>0_def access_ti\<^sub>0_to_bytes 
      field_access_update_same(1) inv_p length_replicate length_to_bytes_p 
      packed_type_intro_simps(1) wf_fd)

definition coerce_map:: "('a::mem_type \<Rightarrow> 'a) \<Rightarrow> ('b::mem_type \<Rightarrow> 'b)" where
  "coerce_map f v = coerce (f (coerce v))"

lemma coerce_map_id[simp]: "coerce_map f (coerce v) = f v"
  by (simp add: coerce_map_def)

lemma coerce_coerce_map_cancel_packed[simp]: 
  fixes f::"'a::packed_type \<Rightarrow> 'a"
  fixes v::"'b::packed_type" 
  assumes sz_eq[simp]: "size_of (TYPE('a)) = size_of (TYPE('b))"
  shows "((coerce (coerce_map f v))::'a) = f (coerce v)"
  by (simp add: coerce_map_def)




named_theorems global_const_defs and 
  global_const_array_selectors and 
  global_const_non_array_selectors and
  global_const_selectors

named_theorems fun_ptr_simps
named_theorems fun_ptr_intros
named_theorems fun_ptr_distinct
named_theorems fun_ptr_subtree

text \<open>
We integrate mllex and mlyacc directly into Isabelle:
\<^item> We compile the SML files according to the description in \<^file>\<open>tools/mlyacc/src/FILES\<close>
\<^item> We export the necessary signatures and structures to the Isabelle/ML environment.
\<^item> As mllex / mlyacc operate directly on files we invoke them on temporary files and 
  redirect stdout / stderr to display the messages within PIDE. We wrap this in Isabelle commands
  @{command mllex}, @{command mlyacc}.
\<close>

SML_file \<open>tools/mllex/mllex.ML\<close>
SML_export \<open>structure LexGen = LexGen\<close>

SML_file \<open>tools/mlyacc/mlyacclib/MLY_base-sig.ML\<close>
SML_file \<open>tools/mlyacc/mlyacclib/MLY_stream.ML\<close>
SML_file \<open>tools/mlyacc/mlyacclib/MLY_lrtable.ML\<close>
SML_file \<open>tools/mlyacc/mlyacclib/MLY_join.ML\<close>
SML_file \<open>tools/mlyacc/mlyacclib/MLY_parser2.ML\<close>
SML_file \<open>tools/mlyacc/src/utils.ML\<close>
SML_file \<open>tools/mlyacc/src/sigs.ML\<close>
SML_file \<open>tools/mlyacc/src/hdr.ML\<close>
SML_file \<open>tools/mlyacc/src/yacc-grm-sig.sml\<close>
SML_file \<open>tools/mlyacc/src/yacc-grm.sml\<close>
SML_file \<open>tools/mlyacc/src/yacc.lex.sml\<close>
SML_file \<open>tools/mlyacc/src/parse.ML\<close>
SML_file \<open>tools/mlyacc/src/grammar.ML\<close>
SML_file \<open>tools/mlyacc/src/core.ML\<close>
SML_file \<open>tools/mlyacc/src/coreutils.ML\<close>
SML_file \<open>tools/mlyacc/src/graph.ML\<close>
SML_file \<open>tools/mlyacc/src/look.ML\<close>
SML_file \<open>tools/mlyacc/src/lalr.ML\<close>
SML_file \<open>tools/mlyacc/src/mklrtable.ML\<close>
SML_file \<open>tools/mlyacc/src/mkprstruct.ML\<close>
SML_file \<open>tools/mlyacc/src/shrink.ML\<close>
SML_file \<open>tools/mlyacc/src/verbose.ML\<close>
SML_file \<open>tools/mlyacc/src/absyn-sig.ML\<close>
SML_file \<open>tools/mlyacc/src/absyn.ML\<close>
SML_file \<open>tools/mlyacc/src/yacc.ML\<close>
SML_file \<open>tools/mlyacc/src/link.ML\<close>

SML_export \<open>signature LR_TABLE = LR_TABLE\<close>
SML_export \<open>structure LrTable = LrTable\<close>
SML_export \<open>signature LR_PARSER = LR_PARSER\<close>
SML_export \<open>structure LrParser = LrParser\<close>
SML_export \<open>signature TOKEN = TOKEN\<close>
SML_export \<open>signature PARSER_DATA = PARSER_DATA\<close>
SML_export \<open>signature PARSE_GEN = PARSE_GEN\<close>
SML_export \<open>signature LEXER = LEXER\<close>
SML_export \<open>signature PARSER_DATA = PARSER_DATA\<close>
SML_export \<open>signature PARSER = PARSER\<close>
SML_export \<open>signature ARG_PARSER = ARG_PARSER\<close>
SML_export \<open>structure ParseGen = ParseGen\<close>

SML_export \<open>functor Join(structure Lex : LEXER
             structure ParserData: PARSER_DATA
             structure LrParser : LR_PARSER
             sharing ParserData.LrTable = LrParser.LrTable
             sharing ParserData.Token = LrParser.Token
             sharing type Lex.UserDeclarations.svalue = ParserData.svalue
             sharing type Lex.UserDeclarations.pos = ParserData.pos
             sharing type Lex.UserDeclarations.token = ParserData.Token.token): PARSER =
  Join(structure Lex = Lex 
       structure ParserData = ParserData 
       structure LrParser = LrParser)\<close>
SML_export \<open>functor JoinWithArg(structure Lex : ARG_LEXER
             structure ParserData: PARSER_DATA
             structure LrParser : LR_PARSER
             sharing ParserData.LrTable = LrParser.LrTable
             sharing ParserData.Token = LrParser.Token
             sharing type Lex.UserDeclarations.svalue = ParserData.svalue
             sharing type Lex.UserDeclarations.pos = ParserData.pos
             sharing type Lex.UserDeclarations.token = ParserData.Token.token)
                 : ARG_PARSER  = 
   JoinWithArg(structure Lex = Lex 
       structure ParserData = ParserData 
       structure LrParser = LrParser)
\<close>

ML \<open>
local

val tmp_io = Synchronized.var "tmp_io" ()

fun system_command cmd =
  if Isabelle_System.bash cmd <> 0 then error ("System command failed: " ^ cmd) else ();


fun copy_file qualify_ref src0 dst0 =
  let
    val src = Path.expand src0;
    val dst = Path.expand dst0;
    val target = if File.is_dir dst then Path.append dst (Path.base src) else dst;
  in
    if File.eq (src, target) then 
      ()
    else if qualify_ref then
      ignore (system_command ("sed 's/ ref / Unsynchronized.ref /g' " ^ File.bash_path src  ^ " > " ^ File.bash_path target))
    else 
      ignore (system_command ("cp -f " ^ File.bash_path src ^ " " ^ File.bash_path target))
  end;

fun file_command qualify_ref tag exts f files thy = 
  let
    val (files, thy) = files thy
    val {src_path, lines,...}: Token.file = the_single files
    val filename = Path.file_name src_path
    val full_src_path = Path.append (Resources.master_directory thy) src_path
    val _ = Isabelle_System.with_tmp_dir tag (fn tmp_dir => Synchronized.change tmp_io (fn _ =>
      let
        val orig_stdOut = TextIO.getOutstream TextIO.stdOut
        val orig_stdErr = TextIO.getOutstream TextIO.stdErr
        val out_file = (Utils.sanitized_path thy tmp_dir (Path.ext "out" src_path))
        val err_file = (Utils.sanitized_path thy tmp_dir (Path.ext "err" src_path))
        val dir = Path.dir out_file
        val _ = Isabelle_System.make_directory dir
        val stdOut = TextIO.openOut (File.standard_path out_file)
        val stdErr = TextIO.openOut (File.standard_path err_file)

        val _ = TextIO.setOutstream (TextIO.stdOut, TextIO.getOutstream stdOut)
        val _ = TextIO.setOutstream (TextIO.stdErr, TextIO.getOutstream stdErr)

        val tmp_file = Utils.sanitized_path thy tmp_dir src_path

        val _ = File.write tmp_file (cat_lines lines)
        val res = try f (File.standard_path tmp_file)


        val _ = TextIO.setOutstream (TextIO.stdOut, orig_stdOut)
        val _ = TextIO.setOutstream (TextIO.stdErr, orig_stdErr)
        val _ = TextIO.closeOut stdOut
        val _ = TextIO.closeOut stdErr
        val out = File.read_lines out_file
        val err = File.read_lines err_file
         
        val msg = Pretty.string_of (Pretty.strs (out @ err))

      in 
        case res of
           SOME () => 
            let 
              val result_files = map (fn ext => (Path.ext ext tmp_file, 
                      Path.ext ext full_src_path)) exts
              val _ = app (fn (src, dst) => copy_file qualify_ref src dst) result_files
              val _ = tracing (quote (tag ^ " " ^ filename) ^ " succeeded:\n" ^ msg)
            in () end 
        |  NONE => (error (quote (tag ^ " " ^ filename) ^ " failed:\n" ^ msg); ())
      end))
    
  in 
    thy
  end
in
val _ =
  Outer_Syntax.command
    @{command_keyword "mllex"} "generate lexer" 
   (Resources.provide_parse_files single >> (Toplevel.theory o (file_command true "mllex" ["sml"] LexGen.lexGen)))
val _ =
  Outer_Syntax.command
    @{command_keyword "mlyacc"} "generate parser" 
   (Resources.provide_parse_files single >> (Toplevel.theory o (file_command true "mlyacc" ["sig", "sml"] ParseGen.parseGen)))

end
\<close>


primrec map_of_default :: 
  "('p \<Rightarrow> 'a) \<Rightarrow> ('p * 'a) list \<Rightarrow> 'p \<Rightarrow> 'a"
where
  "map_of_default d [] x = d x"
| "map_of_default d (x # xs) x' = (if fst x = x' then snd x else map_of_default d xs x')"


lemma map_of_default_append: \<open>map_of_default d (xs @ ys) = map_of_default (map_of_default d ys) xs\<close>
  by (induction xs arbitrary: d ys) auto

lemma map_of_default_map_of_conv: 
  \<open>map_of_default d xs p = (case map_of xs p of Some f \<Rightarrow> f | None \<Rightarrow> d p)\<close>
  by (induction xs) (auto simp add: fun_upd_same fun_upd_other)

lemma map_of_default_fallthrough: 
  "p \<notin> set (map fst xs) \<Longrightarrow> map_of_default d xs p = d p"
  by (induct xs) auto

lemma map_of_default_distinct:
  assumes "distinct (map fst xs)"
  shows "list_all (\<lambda>(p, f). map_of_default d xs p = f) xs"
  using assms
  apply  (induction xs)
   apply simp_all
  by (smt (verit, ccfv_SIG) image_iff list.pred_mono_strong prod.case_eq_if)

lemma map_of_default_default_conv:
  assumes "list_all (\<lambda>(p, f). d p = f) xs"
  shows "map_of_default d xs = d"
  using assms
  by (induct xs) auto

lemma map_of_default_monotone_cons[partial_function_mono]:
  assumes f1 [partial_function_mono]: "monotone R X f1"
  assumes [partial_function_mono]: "monotone R X (\<lambda>f. map_of_default d (xs f) p)"
  shows "monotone R X (\<lambda>f. map_of_default d ((p1, f1 f)#xs f) p)"
  apply (simp only: map_of_default.simps fst_conv snd_conv cong: if_cong)
  apply (intro partial_function_mono)
  done

hide_const (open)  StaticFun.Node

primrec tree_of :: "'a list \<Rightarrow> 'a tree" 
where
  "tree_of [] = Tip"
| "tree_of (x#xs) = Node (Tip) x False (tree_of xs)"

lemma set_of_tree_of: "set_of (tree_of xs) = set xs"
  by (induct xs) auto

lemma all_distinct_tree_of:
  assumes "all_distinct (tree_of xs)"
  shows "distinct xs"
  using assms by (induct xs) (auto simp add: set_of_tree_of)

lemma all_distinct_tree_of': 
"all_distinct t \<Longrightarrow> tree_of xs \<equiv> t \<Longrightarrow> distinct xs"
  by (simp add: all_distinct_tree_of)

lemma map_of_default_fallthrough': 
  "map fst xs \<equiv> ps \<Longrightarrow> tree_of ps \<equiv> t \<Longrightarrow> p \<notin> set_of t \<Longrightarrow> map_of_default d xs p = d p"
  apply (rule map_of_default_fallthrough)
  using set_of_tree_of [of "map fst xs"]
  apply simp
  done

primrec list_of :: "'a tree \<Rightarrow> 'a list"
  where
  "list_of Tip = []"
| "list_of (Node l x d r) =  list_of l @ (if d then [] else [x]) @ list_of r"

lemma list_of_tree_of_conv [simp]: "list_of (tree_of xs) = xs"
  by (induct xs) auto

lemma set_list_of_set_of_conv: "set (list_of t) = set_of t"
  by (induct t) auto

lemma all_distinct_list_of:
  assumes "all_distinct t"
  shows "distinct (list_of t)"
  using assms by (induct t) (auto simp add: set_list_of_set_of_conv)

lemma map_of_default_distinct_lookup_list_all: 
  "distinct (map fst xs) \<Longrightarrow> list_all (\<lambda>(p, f). map_of_default d xs p = f) xs"
  by (induct xs) (auto simp add: case_prod_beta' image_iff list.pred_mono_strong)

lemma map_of_default_distinct_lookup_list_all': 
  assumes ps: "map fst xs \<equiv> ps" 
  assumes t: "tree_of ps \<equiv> t"
  assumes dist: "all_distinct t"
  shows "list_all (\<lambda>(p, f). map_of_default d xs p = f) xs"
  using  all_distinct_tree_of' [OF dist t] ps
  by (simp add: map_of_default_distinct_lookup_list_all)

lemma map_of_default_distinct_lookup_list_all'': 
  assumes t: "list_of t \<equiv> ps"
  assumes ps: "map fst xs \<equiv> ps"
  assumes dist: "all_distinct t"
  shows "list_all (\<lambda>(p, f). map_of_default d xs p = f) xs"
  by (metis all_distinct_list_of dist map_of_default_distinct_lookup_list_all ps t)


lemma map_of_default_other_lookup_list_all: 
  "set ps \<inter> set (map fst xs) = {} \<Longrightarrow> list_all (\<lambda>p. map_of_default d xs p = d p) ps"
  using map_of_default_fallthrough [where d=d and xs= xs]
  apply (induct xs) 
   apply (clarsimp simp add: list.pred_True )
  by (smt (verit, best) IntI ball_empty list.pred_set)


lemma delete_Some_subset: "DistinctTreeProver.delete x t = Some t' \<Longrightarrow> set_of t \<subseteq> {x} \<union> set_of t'"
  by (induct t arbitrary: t') (auto split: option.splits if_split_asm)

lemma delete_Some_set_of_union:
  assumes del: "DistinctTreeProver.delete x t = Some t'" shows "set_of t = {x} \<union> set_of t'"
proof -
  from delete_Some_set_of [OF del] have "set_of t' \<subseteq> set_of t" .
  moreover
  from delete_Some_x_set_of [OF del] obtain "x \<in> set_of t"  "x \<notin> set_of t'"
    by simp
  ultimately have "{x} \<union> set_of t' \<subseteq> set_of t"
    by blast
  with delete_Some_subset [OF del]
  show ?thesis by blast
qed

primrec undeleted :: "'a tree \<Rightarrow> bool"
  where
  "undeleted Tip = True"
| "undeleted (Node l y d r) = (\<not> d \<and> undeleted l \<and> undeleted r)"

lemma undeleted_tree_of[simp]: "undeleted (tree_of xs)"
  by (induct xs) auto

lemma subtract_union_subset: 
  "subtract t\<^sub>1 t\<^sub>2 = Some t \<Longrightarrow> undeleted t\<^sub>1 \<Longrightarrow> set_of t\<^sub>2 \<subseteq> set_of t\<^sub>1 \<union> set_of t"
proof (induct t\<^sub>1 arbitrary: t\<^sub>2 t)
  case Tip thus ?case by simp
next
  case (Node l x b r)
  have sub: "subtract (Node l x b r) t\<^sub>2 = Some t" by fact
  from Node.prems obtain not_b: "\<not> b" and undeleted_l: "undeleted l" and undeleted_r: "undeleted r"
    by simp
  from subtract_Some_set_of [OF sub] have sub_t2: "set_of (Node l x b r) \<subseteq> set_of t\<^sub>2" .

  show ?case
  proof (cases "DistinctTreeProver.delete x t\<^sub>2")
    case (Some t\<^sub>2')
    note del_x_Some = this
    from delete_Some_set_of_union [OF Some] 
    have t2'_t2: "set_of t\<^sub>2 = {x} \<union> set_of t\<^sub>2'" .
    show ?thesis
    proof (cases "subtract l t\<^sub>2'")
      case (Some t\<^sub>2'')
      note sub_l_Some = this
      from Node.hyps (1) [OF Some undeleted_l] 
      have t2''_t2': "set_of t\<^sub>2' \<subseteq> set_of l \<union> set_of t\<^sub>2''" .
      show ?thesis
      proof (cases "subtract r t\<^sub>2''")
        case (Some t\<^sub>2''')
        from Node.hyps (2) [OF Some undeleted_r] 
        have "set_of t\<^sub>2'' \<subseteq> set_of r \<union> set_of t\<^sub>2'''" .
        with Some sub_l_Some del_x_Some sub t2''_t2' t2'_t2 not_b
        show ?thesis
          by auto
      next
        case None
        with del_x_Some sub_l_Some sub
        show ?thesis
          by simp
      qed
    next
      case None
      with del_x_Some sub 
      show ?thesis
        by simp
    qed
  next
    case None
    with sub show ?thesis by simp
  qed
qed


lemma subtract_union_eq: 
  assumes sub: "subtract t\<^sub>1 t\<^sub>2 = Some t"
  assumes und: "undeleted t\<^sub>1"
  shows "set_of t\<^sub>2 = set_of t\<^sub>1 \<union> set_of t"
proof
  from sub und
  show "set_of t\<^sub>2 \<subseteq> set_of t\<^sub>1 \<union> set_of t"
    by (rule subtract_union_subset)
next
  from subtract_Some_set_of_res [OF sub] have "set_of t \<subseteq> set_of t\<^sub>2".
  moreover from subtract_Some_set_of [OF sub] have "set_of t\<^sub>1 \<subseteq> set_of t\<^sub>2" .
  ultimately
  show "set_of t\<^sub>1 \<union> set_of t \<subseteq> set_of t\<^sub>2" by blast
qed



lemma subtract_empty:
  assumes sub: "subtract t\<^sub>1 t\<^sub>2 = Some t" 
  assumes und: "undeleted t\<^sub>1"
  assumes empty: "set_of t = {}"
  shows "set_of t\<^sub>1 = set_of t\<^sub>2"
  using subtract_union_eq [OF sub und] empty by simp


lemma map_of_default_other_lookup_Ball:
  assumes ps: "list_of t \<equiv> ps"
  assumes map_fst: "map fst xs \<equiv> ps"
  assumes sub: "subtract t t_all = Some t_sub"
  shows "\<forall>p \<in> set_of t_sub. map_of_default d xs p = d p"
  by (metis disjoint_iff map_fst map_of_default_fallthrough ps set_list_of_set_of_conv sub subtract_Some_dist_res)



lemma subtract_set_of_exchange_first:
  assumes sub1: "subtract t\<^sub>1 t = Some t'" 
  assumes sub2: "subtract t\<^sub>2 t = Some t''" 
  assumes und1: "undeleted t\<^sub>1" 
  assumes und2: "undeleted t\<^sub>2" 
  assumes seq: "set_of t\<^sub>1 = set_of t\<^sub>2" 
  shows "set_of t' = set_of t''"
  using subtract_union_eq [OF sub1 und1] subtract_union_eq [OF sub2 und2] seq
   subtract_Some_dist_res [OF sub1] subtract_Some_dist_res [OF sub2]
  by blast



lemma TWO: "Suc (Suc 0) = 2" by arith

definition
  fun_addr_of :: "int \<Rightarrow> unit ptr" where
  "fun_addr_of i \<equiv> Ptr (word_of_int i)"

definition
  ptr_range :: "'a::c_type ptr \<Rightarrow> addr set" where
  "ptr_range p \<equiv> {ptr_val (p::'a ptr) ..< ptr_val p + word_of_int(int(size_of (TYPE('a)))) }"

lemma guarded_spec_body_wp [vcg_hoare]:
  "P \<subseteq> {s. (\<forall>t. (s,t) \<in> R \<longrightarrow> t \<in> Q) \<and> (Ft \<notin> F \<longrightarrow> (\<exists>t. (s,t) \<in> R))}
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub> P (guarded_spec_body Ft R) Q, A"
  apply (simp add: guarded_spec_body_def)
  apply (cases "Ft \<in> F")
   apply (erule HoarePartialDef.Guarantee)
   apply (rule HoarePartialDef.conseqPre, rule HoarePartialDef.Spec)
   apply auto[1]
  apply (rule HoarePartialDef.conseqPre, rule HoarePartialDef.Guard[where P=P])
   apply (rule HoarePartialDef.conseqPre, rule HoarePartialDef.Spec)
   apply auto[1]
  apply simp
  apply (erule order_trans)
  apply (auto simp: image_def Bex_def)
  done

ML_file "../lib/ml-helpers/StringExtras.ML"
ML_file "topo_sort.ML"
ML_file "isa_termstypes.ML"

mllex "StrictC.lex"
mlyacc "StrictC.grm"

ML_file "StrictC.grm.sig"
ML_file "StrictC.grm.sml"
ML_file "StrictC.lex.sml"

ML_file "StrictCParser.ML"
ML_file "complit.ML"
ML_file "hp_termstypes.ML"
ML_file "termstypes-sig.ML"
term "word_of_int"
ML_file "termstypes.ML"
ML_file "recursive_records/recursive_record_pp.ML"
ML_file "recursive_records/recursive_record_package.ML"
ML_file "UMM_termstypes.ML"
ML_file "expression_typing.ML"
ML_file "program_analysis.ML"



context
begin
ML_file "cached_theory_simproc.ML"
ML_file "UMM_Proofs.ML"
end

simproc_setup size_of_bound (\<open>size_of TYPE('a::c_type) \<le> n\<close>) = \<open>K (fn ctxt => fn ct => 
  let
    val _ = (case Thm.term_of ct of
        @{term_pat "size_of ?T \<le> _ "} => if UMM_Proofs.is_ctype T then () else raise Match
      | _ => raise Match)
    val ctxt' = ctxt addsimps (Named_Theorems.get ctxt @{named_theorems size_simps})
    val eq = Simplifier.asm_full_rewrite ctxt' ct
    val _ = Utils.verbose_msg 5 ctxt (fn _ => "size_of_bound: " ^ Thm.string_of_thm ctxt eq)
    val rhs = Thm.rhs_of eq |> Thm.term_of
  in
    if rhs aconv \<^term>\<open>True\<close> orelse rhs aconv \<^term>\<open>False\<close> then
      SOME eq
    else
      NONE
  end
  handle Match => NONE)
\<close>

ML_file "heapstatetype.ML"
ML_file "MemoryModelExtras-sig.ML"
ML_file "MemoryModelExtras.ML"
ML_file "calculate_state.ML"
ML_file "syntax_transforms.ML"
ML_file "expression_translation.ML"
ML_file "modifies_proofs.ML"
ML_file "HPInter.ML"
ML_file "stmt_translation.ML"


method_setup vcg = \<open>Hoare.vcg (*|> then_shorten_names*)\<close>
    "Simpl 'vcg' followed by C parser 'shorten_names'"

method_setup vcg_step = \<open>Hoare.vcg_step (*|> then_shorten_names*)\<close>
    "Simpl 'vcg_step' followed by C parser 'shorten_names'"

declare typ_info_word [simp del]
declare typ_info_ptr [simp del]

lemma valid_call_Spec_eq_subset:
  "\<Gamma>' procname = Some (Spec R) \<Longrightarrow>
  HoarePartialDef.valid \<Gamma>' NF P (Call procname) Q A = (P \<subseteq> fst ` R \<and> (R \<subseteq> (- P) \<times> UNIV \<union> UNIV \<times> Q))"
  apply (safe; simp?)
  subgoal for x
    apply (clarsimp simp: HoarePartialDef.valid_def)
    apply (rule ccontr)
    apply (drule_tac x="Normal x" in spec, elim allE)
    apply (drule mp, erule exec.Call, rule exec.SpecStuck)
     apply (auto simp: image_def)[2]
    done
   apply (clarsimp simp: HoarePartialDef.valid_def)
   apply (elim allE, drule mp, erule exec.Call, erule exec.Spec)
   apply auto[1]
  apply (clarsimp simp: HoarePartialDef.valid_def)
  apply (erule exec_Normal_elim_cases, simp_all)
  apply (erule exec_Normal_elim_cases, auto)
  done


lemma creturn_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Return)) (rvupd (\<lambda>_. v s) s) \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P creturn exnupd rvupd v Q, A"
  unfolding creturn_def
  by vcg

lemma creturn_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Return)) (rvupd (\<lambda>_. v s) s) \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P creturn exnupd rvupd v Q, A"
  unfolding creturn_def
  by vcg


lemma creturn_void_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Return)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P creturn_void exnupd Q, A"
  unfolding creturn_void_def
  by vcg

lemma creturn_void_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Return)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P creturn_void exnupd Q, A"
  unfolding creturn_void_def
  by vcg


lemma cbreak_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Break)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P cbreak exnupd Q, A"
  unfolding cbreak_def
  by vcg

lemma cbreak_wp_totoal [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Break)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P cbreak exnupd Q, A"
  unfolding cbreak_def
  by vcg

lemma ccatchbrk_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd s = Break \<longrightarrow> s \<in> Q) \<and>
                    (exnupd s \<noteq> Break \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P ccatchbrk exnupd Q, A"
  unfolding ccatchbrk_def
  by vcg

lemma ccatchbrk_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd s = Break \<longrightarrow> s \<in> Q) \<and>
                    (exnupd s \<noteq> Break \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P ccatchbrk exnupd Q, A"
  unfolding ccatchbrk_def
  by vcg

lemma cgoto_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Goto l)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P cgoto l exnupd Q, A"
  unfolding cgoto_def
  by vcg

lemma cgoto_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd (\<lambda>_. Goto l)) s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P cgoto l exnupd Q, A"
  unfolding cgoto_def
  by vcg

lemma ccatchgoto_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd s = Goto l \<longrightarrow> s \<in> Q) \<and>
                    (exnupd s \<noteq> Goto l \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P ccatchgoto l exnupd Q, A"
  unfolding ccatchgoto_def
  by vcg

lemma ccatchgoto_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. (exnupd s = Goto l \<longrightarrow> s \<in> Q) \<and>
                    (exnupd s \<noteq> Goto l \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P ccatchgoto l exnupd Q, A"
  unfolding ccatchgoto_def
  by vcg

lemma ccatchreturn_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. (is_local (exnupd s) \<longrightarrow> s \<in> Q) \<and>
                    (\<not> is_local (exnupd s) \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P ccatchreturn exnupd Q, A"
  unfolding ccatchreturn_def 
  by vcg

lemma ccatchreturn_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. (is_local (exnupd s) \<longrightarrow> s \<in> Q) \<and>
                    (\<not> is_local (exnupd s) \<longrightarrow> s \<in> A)}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P ccatchreturn exnupd Q, A"
  unfolding ccatchreturn_def 
  by vcg

lemma cexit_wp [vcg_hoare]:
  assumes "P \<subseteq> {s. exnupd s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P cexit exnupd Q, A"
  unfolding cexit_def 
  by vcg

lemma cexit_wp_total [vcg_hoare]:
  assumes "P \<subseteq> {s. exnupd s \<in> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P cexit exnupd Q, A"
  unfolding cexit_def 
  by vcg

lemma cchaos_wp [vcg_hoare]:
  assumes "P \<subseteq>  {s. \<forall>x. (v x s) \<in> Q }"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P cchaos v Q, A"
  unfolding cchaos_def
  using assms by (blast intro: HoarePartial.Spec)

lemma cchaos_wp_total [vcg_hoare]:
  assumes "P \<subseteq>  {s. \<forall>x. (v x s) \<in> Q }"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P cchaos v Q, A"
  unfolding cchaos_def
  using assms by (blast intro: HoareTotal.Spec)

lemma lvar_nondet_init_wp [vcg_hoare]:
  "P \<subseteq> {s. \<forall>v. (upd (\<lambda>_. v)) s \<in> Q} \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub> P lvar_nondet_init upd Q, A"
  unfolding lvar_nondet_init_def
  by (rule HoarePartialDef.conseqPre, vcg, auto)

lemma lvar_nondet_init_wp_total [vcg_hoare]:
  "P \<subseteq> {s. \<forall>v. (upd (\<lambda>_. v)) s \<in> Q} \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub> P lvar_nondet_init upd Q, A"
  unfolding lvar_nondet_init_def
  by (rule HoareTotalDef.conseqPre, vcg, auto)

lemma Seq_propagate_precond:
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>1 P,A; \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>2 Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Seq c\<^sub>1 c\<^sub>2) Q,A"
  apply (rule hoarep.Seq)
   apply assumption
  apply assumption
  done

lemma Seq_propagate_precond_total:
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 P,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>2 Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Seq c\<^sub>1 c\<^sub>2) Q,A"
  apply (rule hoaret.Seq)
   apply assumption
  apply assumption
  done

lemma mem_safe_lvar_init [simp,intro]:
  assumes upd: "\<And>g v s. globals_update g (upd (\<lambda>_. v) s) = upd (\<lambda>_. v) (globals_update g s)"
  assumes acc: "\<And>v s. globals (upd (\<lambda>_. v) s) = globals s"
  shows "mem_safe (lvar_nondet_init upd) x"
  apply (clarsimp simp: mem_safe_def lvar_nondet_init_def)
  apply (erule exec.cases; clarsimp simp: restrict_safe_def)
   apply (fastforce simp: restrict_safe_OK_def restrict_htd_def upd acc intro: exec.Spec)
  apply (simp add: exec_fatal_def)
  apply (fastforce simp: exec_fatal_def restrict_htd_def upd acc intro!: exec.SpecStuck)
  done

lemma intra_safe_lvar_nondet_init [simp]:
  "intra_safe (lvar_nondet_init upd :: (('a::heap_state_type','l,'e,'x) state_scheme,'p,'f) com) =
   (\<forall>\<Gamma>. mem_safe (lvar_nondet_init upd :: (('a::heap_state_type','l,'e,'x) state_scheme,'p,'f) com)
                 (\<Gamma> :: (('a,'l,'e,'x) state_scheme,'p,'f) body))"
  by (simp add: lvar_nondet_init_def)


lemma proc_deps_lvar_nondet_init [simp]:
  "proc_deps (lvar_nondet_init upd) \<Gamma> = {}"
  by (simp add: lvar_nondet_init_def)

declare word_neq_0_conv[simp]


declare [[hoare_use_generalise=true]]
end
