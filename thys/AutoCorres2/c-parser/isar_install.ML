(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure CParser_Options =
struct

  @{record \<open>datatype opts = Opts of {
     memsafe: bool option,
     c_types: bool option,
     c_defs: bool option,
     prune_types: bool option,
     machinety: string option,
     ghostty: string option,
     roots: string list option,
     skip_asm: bool option}\<close>
  };

val empty_options = make_opts {memsafe = NONE, c_types = NONE, c_defs = NONE, prune_types = NONE,
  machinety = NONE, ghostty = NONE, roots = NONE, skip_asm = NONE};

val default_options = make_opts {memsafe = SOME false, c_types = SOME true, c_defs = SOME true,
  prune_types = SOME true, machinety = NONE, ghostty = NONE, roots = NONE, skip_asm = SOME false};

end

signature ISAR_INSTALL =
sig
  val timing: bool Config.T
  val cpp_path: string Config.T
  val clang_path: string Config.T

  val gen_umm_types_file : bool -> (theory -> Token.file list * theory) -> Path.T -> theory -> theory
  val do_cpp : Proof.context -> {cpp_path: Path.T option, error_detail: int} ->
               {includes: string list, lines: string list, src_path: Path.T}
               -> (string list * ProgramAnalysis.clang_record_info list)
  val install_C_file : ((theory -> Token.file list * theory)  * CParser_Options.opts) ->
                       theory -> theory

  val extra_trace_filename : string Config.T

  val installed_C_files : theory
    -> {locale_names : string list,
        options: CParser_Options.opts, 
        prototype_dependencies: AstDatatype.dependencies Symtab.table} Symtab.table
  val add_prototype_dependencies: string -> string * AstDatatype.dependencies ->
        theory -> theory
end

structure IsarInstall : ISAR_INSTALL =
struct


type 'a wrap = 'a Region.Wrap.t

local
  val lock = Thread.Mutex.mutex ();
in

fun SYNCHRONIZED name = Multithreading.synchronized name lock;

fun setup_feedback extra_output_filename = let
    val trace_extra = case extra_output_filename of
        NONE => K ()
      | SOME f => let
        val out = BinIO.openOut f
      in fn s => (File_Stream.output out s; BinIO.flushOut out) end
    val add_extra = case extra_output_filename of
        NONE => (fn _ => fn f => f)
      | SOME _ => (fn pfx => fn f => fn msg as (s, _) => (trace_extra (pfx ^ s); f msg))
    
  in
    SYNCHRONIZED "feedback" (fn () => (
    Feedback.errorf := add_extra "ERROR: " Feedback.report_error;
    Feedback.warnf := add_extra "" Feedback.report_warning;
    Feedback.informf := add_extra "" (Feedback.report_inform o apfst Feedback.timestamp)))

  end
end

val do_check_embedded_function_calls = Attrib.setup_config_bool \<^binding>\<open>c_parser_check_embedded_function_calls\<close> (K true)

val extra_trace_filename = Attrib.setup_config_string \<^binding>\<open>c_parser_extra_trace_file\<close> (K "")

fun setup_feedback_thy thy = let
    val str = Config.get_global thy extra_trace_filename
  in setup_feedback (if str = "" then NONE else SOME str) end

val _ = setup_feedback NONE

structure C_Includes = Theory_Data(
  type T = string list
  val empty = []
  val merge = Library.merge (op =)
);

type install_info = {locale_names : string list, options: CParser_Options.opts, 
  prototype_dependencies: AstDatatype.dependencies Symtab.table}


val default_info = {locale_names = [], options = CParser_Options.default_options, 
  prototype_dependencies = Symtab.empty}: install_info

fun map_locale_names f ({locale_names, options, prototype_dependencies}:install_info) =
 ({locale_names = f locale_names, options = options, prototype_dependencies = prototype_dependencies}:install_info)
fun map_options f ({locale_names, options, prototype_dependencies}:install_info) =
 ({locale_names = locale_names, options = f options, prototype_dependencies = prototype_dependencies}:install_info)
fun map_prototype_dependencies f ({locale_names, options, prototype_dependencies}:install_info) =
 ({locale_names = locale_names, options = options, prototype_dependencies = f prototype_dependencies}:install_info)


type install_data = install_info Symtab.table 

structure C_Installs = Theory_Data(
  type T = install_data 
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
);
val installed_C_files = C_Installs.get
fun get_prototype_dependencies thy cname =
  let
    val data = installed_C_files thy
  in the_default (Symtab.empty) (Symtab.lookup data cname |> Option.map #prototype_dependencies) end

fun add_prototype_dependencies cname (fname, deps) thy =
  let
    val map_default_deps = Symtab.map_default (fname, deps) (K deps)
    val default_installs = 
      Symtab.map_default (cname, default_info |> map_prototype_dependencies map_default_deps)
        (map_prototype_dependencies map_default_deps)
  in
    thy |> C_Installs.map (default_installs)
  end

structure IsaPath = Path

val cpp_path = Attrib.setup_config_string \<^binding>\<open>cpp_path\<close> (K "/usr/bin/cpp")
val clang_path = Attrib.setup_config_string \<^binding>\<open>clang_path\<close> (K "/usr/bin/clang")

val munge_info_fname = Attrib.setup_config_string \<^binding>\<open>munge_info_fname\<close> (K "")
val report_cpp_errors = Attrib.setup_config_int \<^binding>\<open>report_cpp_errors\<close> (K 10)

fun group_at P xs =
  let
    fun group x [] = [[x]]
      | group x (xs::xss) = if P x then ([x]::xs::xss) else (x::xs)::xss
  in
    fold group xs [] |> filter_out null |> map rev |> rev
  end

fun explode_list sep xs =
  let
    fun exp (ys::yss) (x::xs) = if sep x then exp ([]::ys::yss) xs else exp ((x::ys)::yss) xs
      | exp yss [] = yss
  in
    rev (exp ([[]]) xs |> map rev) |> filter_out null
  end 

fun trim_whitespace s =
  if String.isPrefix " " s then 
    let
      val (indent, s') = trim_whitespace (String.substring (s, 1, size s - 1))
    in (indent + 1, s') end
  else (0, s)

val to_int = #1 o read_int o Symbol.explode

fun first_some [] x = NONE
  | first_some (f::fs) x = case f x of SOME y => SOME y | NONE => first_some fs x

fun glob_match_with_captures pattern str =
  let
    fun match ([], [], captures) = SOME (rev captures)
      | match ([], _, _) = NONE
      | match (#"*" :: ps, s, captures) = match_star (ps, s, "", captures)
      | match (_ :: _, [], _) = NONE
      | match (p :: ps, c :: cs, captures) = 
          if p = c then match (ps, cs, captures) else NONE
    
    and match_star (ps, s, acc, captures) =
      case match (ps, s, captures) of
        SOME result => SOME (acc :: result)
      | NONE =>
          (case s of
             [] => NONE
           | c :: cs => match_star (ps, cs, acc ^ String.str c, captures))
  in
    match (String.explode pattern, String.explode str, [])
end

val last = hd o rev

val record_name = first_some [
  glob_match_with_captures "*::(unnamed at *:*:*)" #> Option.map (fn [_, file, line, column] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}), 
     NONE)),
  glob_match_with_captures "(unnamed at *:*:*)" #> Option.map (fn [file, line, column] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}), 
     NONE)),
  glob_match_with_captures "*::(anonymous at *:*:*)" #> Option.map (fn [_, file, line, column] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}),
     NONE)),
  glob_match_with_captures "(anonymous at *:*:*)" #> Option.map (fn [file, line, column] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}),
     NONE)),
  glob_match_with_captures "*::(unnamed at *:*:*) *" #> Option.map (fn [_, file, line, column,field_name] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}), 
     if field_name = "" then NONE else SOME field_name)),
  glob_match_with_captures "(unnamed at *:*:*) *" #> Option.map (fn [file, line, column,field_name] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}), 
     if field_name = "" then NONE else SOME field_name)),
  glob_match_with_captures "*::(anonymous at *:*:*) *" #> Option.map (fn [_, file, line, column,field_name] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}),
     if field_name = "" then NONE else SOME field_name)),
  glob_match_with_captures "(anonymous at *:*:*) *" #> Option.map (fn [file, line, column,field_name] => 
    (ProgramAnalysis.Anonymous (SourcePos.make {file=file, line = to_int line, column = to_int column-1, yypos = ~1}),
     if field_name = "" then NONE else SOME field_name)),
  glob_match_with_captures "* *" #> Option.map (fn [name, field_name] =>
    (ProgramAnalysis.Named name, if field_name = "" then NONE else SOME (last (space_explode " " field_name)))),
  fn str => SOME (ProgramAnalysis.Named str, NONE)
]


val kind = first_some [
  glob_match_with_captures "struct *" #> Option.map (fn [name] => 
    let val (record_name, field_name) = the (record_name name) 
    in ProgramAnalysis.Strct {record_name = record_name, field_name = field_name} end),
  glob_match_with_captures "union *" #> Option.map (fn [name] => 
    let val (record_name, field_name) = the (record_name name)
    in ProgramAnalysis.Un {record_name = record_name, field_name = field_name} end),
  fn str => SOME (ProgramAnalysis.Fld (str |> space_explode " " |> split_last |> (fn (tys, name) => {typ = space_implode " " tys, name = name})) )
  ] 

val get_size_align = first_some [
  glob_match_with_captures "| [sizeof=*, align=*]",
  fn _ => NONE
  ]

fun make_record_infos lines: ProgramAnalysis.clang_record_info list =
 let
   fun dest_field str = 
     let
       val (indent, name) = trim_whitespace str
     in
       {level = indent div 2, kind = the (kind name)}
     end
   fun dest_line str = 
     let
       val SOME [offset, field] = glob_match_with_captures "* | *" str
     in {offset = to_int offset, field = dest_field field}  end
   fun mk_record (header::xs) = 
     let
       val (flds, size_align) = split_last xs
       val res = get_size_align size_align
       val SOME [size, align] = res
     in
       {header = dest_line header, flds = map dest_line flds, size = to_int size, align= to_int align}
     end
 in
   lines 
   |> filter_out (fn s => String.size s = 0)
   |> explode_list (fn "*** Dumping AST Record Layout" => true | _ => false)
   |> map (Utils.take_while (fn s => s <> "*** Dumping IRgen Record Layout"))
   |> map (map (snd o trim_whitespace))
   |> map mk_record
 end


fun do_cpp ctxt {error_detail, cpp_path} {includes, src_path, lines} =
  let
    fun dest_cpp_err str =
      let
        val (file:: line:: col:: rest) = str |> space_explode ":"
        val int = #1 o read_int o Symbol.explode
      in
        (SourcePos.make {column = int col, file = file, line = int line, yypos = ~1}, space_implode ":" rest)
      end

    fun report_cpp_errors prfx xs =
      let
        fun dest str = \<^try>\<open>dest_cpp_err str catch _ => (SourcePos.bogus, str)\<close>
        val errs = group_at (can dest_cpp_err) xs
        fun dest_err (x::xs) =
          let
            val (pos, str) = dest x
          in (pos, cat_lines ((prfx ^ " " ^ str)::xs)) end

        val pos_errs = map dest_err errs
      in
        app (fn (p,s) => Feedback.errorStr' ctxt (p,p,s)) pos_errs
      end

  (* fun dest_cpp_errs []  *)
   in
     case cpp_path of
         NONE => (lines, [])
       | SOME p =>
         let
           val filename = Path.file_name src_path
           val thy = Proof_Context.theory_of ctxt
         in
           Isabelle_System.with_tmp_dir "cpp" (fn tmp_dir =>
             let
               fun write_tmp_file orig_path lines =
                 let
                   val tmp = Utils.sanitized_path thy tmp_dir orig_path
                   val dir = Path.dir tmp
                   val _ = Isabelle_System.make_directory dir
                 in File.write tmp (cat_lines lines) end
               val cfiles = map #2 (Symtab.dest (C_Files.get_current_files (Proof_Context.theory_of ctxt)))
               val _ = app (fn ({src_path, lines,...}, _) => write_tmp_file src_path lines) cfiles;
               val tmp = Utils.sanitized_path thy tmp_dir src_path
               fun plural 1 = "" | plural _ = "s"
               val tmp_includes = map (Utils.sanitized_path thy tmp_dir o Path.explode) includes
               val includes_string = String.concat (map (fn path => "-I" ^ File.bash_path path ^ " ")
                     (tmp_dir :: tmp_includes))
               val cmdline = File.bash_path p ^ " " ^ includes_string ^ " -CC " ^ File.bash_path tmp
               val clang = Config.get ctxt clang_path
               val clang_installed = is_some (try Process_Result.check (Isabelle_System.bash_process (Bash.script (clang ^ " --version"))))
               val skip_clang = not clang_installed
               val ll_file = tmp |> Path.drop_ext |> Path.ext "ll"
               val i_file = tmp |> Path.drop_ext |> Path.ext "i"
               val cmdline_clang = clang ^ "  " ^ includes_string ^ 
                 " -D'exit(x)=' -Xclang -fdump-record-layouts-canonical -x c -w -target " ^ Target_Architecture.clang_target_architecture ^ 
                 " " ^ "-S -emit-llvm -o" ^ File.bash_path ll_file ^ " " ^ File.bash_path tmp
               val res = Isabelle_System.bash_process (Bash.script cmdline) |> Process_Result.check
             in
               if Process_Result.ok res then 
                 let
                   val out_lines = Process_Result.out_lines res
                   val _ = File.write_list i_file (map (suffix "\n") (out_lines))
                   val _ = Export.export_file (Proof_Context.theory_of ctxt) (Path.binding (Path.base i_file, \<^here>)) i_file
                 in
                   if skip_clang then (Process_Result.out_lines res, []) else let 
                     val record_dump_res = Isabelle_System.bash_process (Bash.script cmdline_clang)
                     val record_info_lines = Process_Result.out_lines record_dump_res
                     val _ = Feedback.writelns ctxt (1, cmdline_clang ^ " stdout:\n" :: map (suffix "\n") record_info_lines) 
                     val record_infos = make_record_infos record_info_lines
                     val _ = if Process_Result.ok record_dump_res then () else
                       let
                         val err_lines = Process_Result.err_lines record_dump_res
                         val _ = Feedback.writelns ctxt (1, cmdline_clang ^ " stderr:\n" :: map (suffix "\n") err_lines) 
                         val (msg, rest) = err_lines |> chop error_detail
                         val _ = report_cpp_errors "clang" msg
                         val cpp_err = "clang failed on " ^ filename ^ "\nCommand: " ^ cmdline_clang ^ "\n" ^
                           cat_lines err_lines
                           in (error cpp_err) end
                   
                         val _ = Export.export_file (Proof_Context.theory_of ctxt) (Path.binding (Path.base ll_file, \<^here>)) ll_file
                       in (out_lines, record_infos) end
                 end
               else
                 let
                   val (msg, rest) = (Process_Result.err_lines res) |> chop error_detail
                   val _ = report_cpp_errors "cpp" msg
                   val cpp_err = "cpp failed on " ^ filename ^ "\nCommand: " ^ cmdline ^

                     (if null rest then "" else
                       ("\n(... " ^ string_of_int (length rest) ^
                        " more line" ^ plural (length rest) ^ ")"))
                 in (error cpp_err, []) end
             end)
         end
   end

val base_file_name = Path.file_name o Path.base o Path.explode

fun get_Csyntax src_path lines thy = let

  val _ = setup_feedback_thy thy

  val cpp_option =
      case Config.get_global thy cpp_path of
          "" => NONE
        | s => SOME (Path.explode s)
  val cpp_error_count = Config.get_global thy report_cpp_errors
  val (cpp_output, clang_record_infos) = do_cpp (Proof_Context.init_global thy) {error_detail = cpp_error_count, cpp_path = cpp_option} 
    {includes=C_Includes.get thy,src_path=src_path, lines=lines}

  val file_name = Path.file_name (Path.base src_path)
  val thy = C_Files.map_cpp_output file_name (K cpp_output) thy 
  val ctxt = Proof_Context.init_global thy
  
  val ((ast0, num_errors), actually_included) =
      StrictCParser.parse ctxt
        15
        src_path
        cpp_output
  val _ = if num_errors > 0 then error ("error(s) parsing file " ^ quote (Path.file_name src_path)) else ()
  val included = C_Files.get_current_files thy |> Symtab.keys |> remove (op = ) (C_Files.get_main thy)
    |> map base_file_name
  val unused = subtract (op =) actually_included included
  fun pretty_list xs = xs |> map Pretty.str |> Pretty.list "[" "]" |> Pretty.string_of

  val _ = if null unused then () else
     warning ("some included files where unused: " ^ pretty_list unused)
  val not_included  = subtract (op =) included actually_included
  val _ = if null not_included then () else
    warning ("please use command" ^ quote (fst @{command_keyword "include_C_file"}) ^
      " to include the following files: " ^ pretty_list not_included)
  val ast1 = ast0 
    |> SyntaxTransforms.nest_gotos ctxt 
    |> SyntaxTransforms.anonymous_empty_fields
    |> SyntaxTransforms.remove_anonstructs ctxt 
    |> SyntaxTransforms.remove_typedefs
    |> SyntaxTransforms.eval_static_builtins ctxt
in
  ((ast1, clang_record_infos), thy)
end

fun print_addressed_vars ctxt cse = let
  open ProgramAnalysis Feedback
  val globs = get_globals cse
  val _ = informStr ctxt (0, "There are "^Int.toString (length globs)^" globals: "^
                        commas_quote (map srcname globs))
  val addressed = get_global_addressed cse
  val addr_vars = map (MString.dest o fst) addressed
  val _ = informStr ctxt (0, "There are "^Int.toString (length addr_vars)^
                        " addressed variables: "^ commas_quote addr_vars)
in
  ()
end

structure MGraph = Graph(struct type key = MString.t val ord = inv_img_ord MString.dest string_ord end)

fun define_global_initializers msgpfx name_munger mungedb cse constant_globs lthy =
  let
    val inittab = ProgramAnalysis.get_globinits cse
    fun mname (_, info) =
          case !info of
            SOME (ty, Expr.MungedVar {munge, ...}) => SOME (munge, ty)
          | _ => NONE

    fun check (x, xs) =
      let

        val not_consts = filter_out (MSymTab.defined constant_globs o fst) xs
        val not_array = filter_out (CType.array_type o snd) not_consts
         (* assignment of non constant array may be ok as due to array decay maybe only the pointer is assigned which is constant *)
        val _ = null not_array orelse error ("define_global_initializers: initialisation of " ^
                  quote (@{make_string} x) ^ " not only depends on constant global variables: " ^ @{make_string} (map fst not_array))
      in
        (x, map fst xs)
      end

   (* In case of a pointer to an array we should do array-decay for field, and Expr.vars_expr should not make a dependency, but make an Addr around *)
    val deps = inittab |> MSymTab.dest |> map (apsnd (Expr.vars_expr {typ = false, addr = false, pre_op=true, post_op=true}))
      |> map (apsnd (map_filter mname))
      |> map (apsnd (sort_distinct (MString.ord o apply2 fst))) |> map check |> MSymTab.make

    val uninits = constant_globs |> MSymTab.keys  |> filter_out (MSymTab.defined deps) |> map (rpair [])

    val all_deps = MSymTab.dest deps @ uninits |> map (apfst (rpair ()))
    val all_ordered = MGraph.make all_deps |> MGraph.topological_order |> rev
    val inits = all_ordered
      |> filter (MSymTab.defined constant_globs)
      |> map (fn x => (x, the (MSymTab.lookup constant_globs x), MSymTab.lookup inittab x))

    val senv = ProgramAnalysis.get_senv cse
    fun define (gnm : MString.t, gty, rhs_opt) lthy =
      let
        val value =
            case  rhs_opt of
              NONE => ExpressionTranslation.zero_term lthy (ProgramAnalysis.get_senv cse) gty
            | SOME rhs => let
                fun error _ = (Feedback.errorStr' lthy (Absyn.eleft rhs, Absyn.eright rhs,
                                                  "Illegal form in initialisor for\
                                                  \ global");
                               raise Fail "Bad global initialisation")
                val fakeTB = TermsTypes.TB {var_updator = error, var_accessor = error,
                                            rcd_updator = error, rcd_accessor = error}
                fun varinfo s = stmt_translation.state_varlookup  "" s mungedb
                val ei = ExpressionTranslation.expr_term lthy cse fakeTB varinfo rhs
                val ei = case gty of
                           Absyn.Array _ => ei
                         | _ => ExpressionTranslation.typecast(lthy, gty, ei)
              in
                ExpressionTranslation.rval_of ei (Free("x", TermsTypes.bool))
                 (* the Free("x",bool) is arbitrary as the constant
                    expression should be ignoring the state argument *)
              end
        val _ = Feedback.informStr lthy (2,
                          msgpfx ^ " " ^ MString.dest gnm ^ " (of C type "^
                          Absyn.tyname gty ^") to have value "^
                          Syntax.string_of_term lthy value)
        val value = Thm.cterm_of lthy value |> Simplifier.rewrite lthy |> Thm.rhs_of |> Thm.term_of
        val T = fastype_of value
        val b = Binding.name (MString.dest (name_munger gnm))
      in
        lthy
        |> Local_Theory.begin_nested |> snd
        |> Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, @{attributes [global_const_defs]}), value))
        |> (fn ((_, (_, eq)), lthy) =>
           let
             val (eqs, attrs) = if TermsTypes.is_array_type T then
                         (Array_Selectors.array_selectors lthy {recursive_record_simpset=true} eq,
                         @{attributes [global_const_array_selectors, global_const_selectors]})
                       else
                         ([eq], @{attributes [global_const_non_array_selectors, global_const_selectors]})
           in
             lthy |>
             Local_Theory.note ((Binding.empty, attrs), eqs)
           end)
        |> snd
        |> Local_Theory.end_nested
      end
  in
    lthy |> fold define inits
  end

val use_anon_vars = Attrib.setup_config_bool \<^binding>\<open>use_anonymous_local_variables\<close> (K false)
val allow_underscore_idents = Attrib.setup_config_bool \<^binding>\<open>allow_underscore_idents\<close> (K false)

fun get_callees cse slist = let
  val {callees,...} = ProgramAnalysis.compute_callgraphs cse
  fun recurse acc worklist =
      case worklist of
          [] => acc
        | fnname :: rest =>
          if Binaryset.member(acc, fnname) then recurse acc rest
          else
            case Symtab.lookup callees fnname of
                NONE => recurse (Binaryset.add(acc, fnname)) rest
              | SOME set => recurse (Binaryset.add(acc, fnname))
                                    (Binaryset.listItems set @ rest)
in
  recurse (Binaryset.empty string_ord) slist
end

fun map_file_pos f ({src_path, lines, digest, pos}: Token.file) =
  ({src_path = src_path, lines = lines, digest = digest, pos = f pos}: Token.file)

fun include_C_file (files, main) thy =
  let
    val (files, thy) = files thy
    val file as {src_path,...}:Token.file = the_single files
    val thy = thy |> C_Files.map_file main (Path.implode src_path) (K (file, Position.thread_data ()))
  in
    thy
  end

fun install_C_file0 (files, options) thy = let
  val _ = setup_feedback_thy thy
  val (files, thy) = files thy
  val file as {src_path, lines, pos,...}:Token.file = the_single files

  val file_name = Path.file_name (Path.base src_path)
  val prog_name = Path.base src_path |> Path.drop_ext |> Path.file_name

  val thy = thy
    |> C_Files.map_main (K file_name)
    |> C_Files.map_file file_name file_name (K (file, Position.thread_data ()))


  val full_src_path = Path.append (Resources.master_directory thy) src_path
  val s = Path.file_name full_src_path
  val _ = not (Long_Name.is_qualified prog_name) orelse
            raise Fail ("Base of filename looks like qualified Isabelle ID: "^
                        prog_name)
  val _ = prog_name <> "" orelse
          raise Fail ("Filename (>'" ^ s ^
                      "'<) gives \"\" as locale name, which is illegal")

  val mstate_ty =
      case CParser_Options.get_machinety options of
        NONE => TermsTypes.nat
      | SOME s => Syntax.read_typ_global thy s
  val roots_opt = CParser_Options.get_roots options
  val gstate_ty =
      case CParser_Options.get_ghostty options of
        NONE => TermsTypes.unit
      | SOME s => Syntax.read_typ_global thy s
  val thy = Config.put_global HP_TermsTypes.current_C_filename s thy
  val thy = CalculateState.store_ghostty (s, gstate_ty) thy
  val anon_vars = Config.get_global thy use_anon_vars
  val uscore_idents = Config.get_global thy allow_underscore_idents



  val install_typs = the_default true (CParser_Options.get_c_types options)
  val install_defs = the_default true (CParser_Options.get_c_defs options)
  val prune_types = the_default true (CParser_Options.get_prune_types options)
  val memsafe = the_default false (CParser_Options.get_memsafe options)
  val skip_asm = the_default false (CParser_Options.get_skip_asm options)
  val ((ast, clang_record_infos), thy) = get_Csyntax src_path lines thy
  val lthy = Named_Target.init [] "" thy
  open ProgramAnalysis CalculateState Feedback
  val owners =
      (* non-null if there are any globals that have owned_by annotations *)
      let
        open StmtDecl RegionExtras
        fun getowner d =
            case d of
                Decl d =>
                (case node d of
                     VarDecl (_, _, _, _, attrs) => get_owned_by attrs
                   | _ => NONE)
              | _ => NONE
      in
        List.mapPartial getowner ast
      end
  val mifname = case Config.get lthy munge_info_fname of
                  "" => NONE
                | s => SOME (Path.explode s)
  val ((ast, init_stmts), cse) =
      process_decls lthy {anon_vars=anon_vars,owners = owners,
                     allow_underscore_idents = uscore_idents,
                     munge_info_fname = mifname, prog_name = prog_name}
                    ast
  val () = if Feedback.get_num_errors_val lthy > 0 then error ("error(s) occured in file " ^ quote file_name) else ()
  val () = export_mungedb cse
  val cse = cse 
    |> ProgramAnalysis.add_init_globals_fun init_stmts 
    |> ProgramAnalysis.map_clang_record_infos (K clang_record_infos)
  val lthy = lthy |> Local_Theory.background_theory (store_csenv (s, cse))

  val _ = print_addressed_vars lthy cse
  val ecenv = cse2ecenv lthy cse
  val lthy = define_enum_consts ecenv lthy
  val state = create_state cse
  val (rcdinfo, lthy) = mk_thy_types cse install_typs prune_types lthy
  val ast = SyntaxTransforms.remove_embedded_fncalls lthy cse ast
  val toTranslate = Option.map (get_callees cse) roots_opt
  val toTranslate_s =
      case toTranslate of
          NONE => "all functions"
        | SOME set => "functions " ^
                      String.concatWith ", " (Binaryset.listItems set) ^
                      " (derived from "^
                      String.concatWith ", " (the roots_opt) ^ ")"
  val _ =
      Feedback.informStr lthy (0, "Beginning function translation for " ^
                toTranslate_s)
  val toTranslateP =
      case toTranslate of
          NONE => (fn _ => true)
        | SOME set => (fn s => Binaryset.member(set,s))
  val (fninfo_cliques, callgraph, fun_ptr_clique) = HPInter.mk_fninfo lthy cse toTranslateP ast
  val callgraph_with_exit = ProgramAnalysis.compute_callgraphs_with_exit cse
  val cliques = map (map #fname) fninfo_cliques;
  val cse = cse |> map_cliques (K cliques)
  val proto_deps = get_prototype_dependencies (Proof_Context.theory_of lthy) s
  val lthy = lthy |> Local_Theory.background_theory 
    (map_csenv s (map_cliques (K cliques) #>
     map_fun_ptr_core_clique (K fun_ptr_clique) #> 
     map_final_callgraph (K callgraph) #>
     map_final_callgraph_with_exit (K callgraph_with_exit) #>
     (fn cse => map_variable_dependencies (K (ProgramAnalysis.variable_dependencies lthy proto_deps cse)) cse)))
  val _ = 
    if Config.get lthy do_check_embedded_function_calls then 
      ProgramAnalysis.check_embedded_fncall_exprs lthy (the (CalculateState.get_csenv (Proof_Context.theory_of lthy) s))
    else ()
  val fninfo = flat fninfo_cliques;
  val lthy = if not install_defs then
        lthy
        |> More_Local_Theory.in_theory (C_Installs.map (
          Symtab.map_default (s, {locale_names = [], options = options, prototype_dependencies = Symtab.empty}) 
            (map_options (K options))))
    else
    let
      val ((vdecls, globs, (globty, locty, styargs)), lthy) =
        lthy
        |> More_Local_Theory.in_theory_result (
          mk_thy_decls prog_name state {owners = owners, gstate_ty = gstate_ty, mstate_ty = mstate_ty,
            addressed_funs = get_all_addressed_funs cse,
            all_funs = map #fname fninfo})
      val elems = globs
      val loc_b = Binding.name (NameGeneration.globals_locale_name prog_name)
      fun ensure_scope prog_name scope =
        case scope of
         (prog_name'::_) => if prog_name = prog_name' then scope else [prog_name]
        | _ => [prog_name];

      val _ = Feedback.informStr lthy (0,
        "Create locale for globals: " ^ Binding.print loc_b)

      val globloc = NameGeneration.intern_globals_locale_name (Proof_Context.theory_of lthy) prog_name
      val lthy =
        lthy
        |> More_Local_Theory.in_theory (
            Named_Target.init [] globloc  
            #> Local_Theory.declaration {pervasive=false, syntax=true, pos = \<^here>} (fn _ =>
                  Hoare.set_default_state_kind (Hoare.Other NameGeneration.locals_stackN) #>
                  CLocals.scope_map (ensure_scope prog_name))
            #> Local_Theory.exit_global)

      val mungedb = mk_mungedb vdecls
      val lthy = More_Local_Theory.in_theory (CalculateState.store_mungedb (s, mungedb)) lthy
      val all_constant_globals = get_untouched_globals cse
      val lthy = lthy |> (
          define_global_initializers "Defining constant globals"
                                     NameGeneration.untouched_global_name
                                     mungedb
                                     cse
                                     all_constant_globals)
      val lthy =
          if Config.get lthy CalculateState.record_globinits then (
              let
                val globs0 = get_globals cse
                val globs_types = map (fn vi => (get_mname vi, get_vtype vi)) globs0
                val glob_table = MSymTab.make globs_types
              in
                lthy |> define_global_initializers
                  "Defining initializers for all globals "
                  NameGeneration.initial_value_name
                  mungedb
                  cse
                  glob_table
              end)
          else (Feedback.informStr lthy (0,
                    "Ignoring initialisations of modified globals (if any)");
                lthy)

      open TermsTypes

      val lthy = Local_Theory.background_theory (HPInter.define_state_spaces prog_name styargs globloc fninfo) lthy

      val translate_body = stmt_translation.translate_body (globty, locty, styargs)
                                            mungedb
                                            cse
                                            fninfo
                                            rcdinfo
                                            memsafe
                                            skip_asm

      val (specs, lthy) =
          HPInter.make_function_definitions cse
                                            styargs
                                            fninfo_cliques
                                            translate_body
                                            globloc
                                            globs
                                            prog_name
                                            lthy


      val lthy =
        lthy
        |> not (Symtab.is_empty (get_defined_functions cse)) ?
          More_Local_Theory.in_theory (Modifies_Proofs.prove_all_modifies_goals cse toTranslateP styargs prog_name cliques)
        |> More_Local_Theory.in_theory (
          C_Installs.map (Symtab.map_default (s, { locale_names = [globloc] @ specs, options = options, prototype_dependencies = Symtab.empty})
            (map_locale_names (K ([globloc] @ specs)) #> map_options (K options)) ))
    in
      lthy

    end
    val thy =  lthy |> Local_Theory.exit_global
    val _   = Feedback.informStr lthy (0, "install_C_file done")
in
  thy
end handle e as TYPE (s,tys,tms) =>
         (tracing (s ^ "\n" ^
                   Int.toString (length tms) ^ " term(s): " ^
                   String.concatWith
                       ", "
                       (map (Syntax.string_of_term @{context}) tms) ^ "\n" ^
                   Int.toString (length tys) ^ " type(s): "^
                   String.concatWith
                       ", "
                       (map (Syntax.string_of_typ @{context}) tys));
          raise e)

(* timing *)

val timing = Attrib.setup_config_bool \<^binding>\<open>cparser_timing\<close> (K true);
fun timeit_msg ctxt s x = if Config.get ctxt timing then (warning s; timeit x) else x ();
fun timing_msg ctxt s = if Config.get ctxt timing then warning s else ();


fun install_C_file args thy =
  timeit_msg (Proof_Context.init_global thy) "install C file" (fn () =>
    thy |> install_C_file0 args
        |> Config.put_global HP_TermsTypes.current_C_filename "")

fun install_C_file_expect_reject args thy =
  let
    val thy' = Config.put_global Feedback.expect_reject true thy
    val res = Exn.capture (install_C_file args) thy'
    val _ = if Exn.is_exn res then () else error ("expecting install_C_file to reject program and report error, but it succeeded")
  in thy end
 

fun install_C_types files thy = let
  open CalculateState ProgramAnalysis
  val (files, thy) = files thy
  val {src_path, lines, ...}:Token.file = the_single files
  val lthy = Named_Target.init [] "" thy
  val full_src_path = Path.append (Resources.master_directory thy) src_path

  val prog_name = Path.base src_path |> Path.split_ext |> fst |> Path.file_name

  val ((ast, clang_record_infos), thy) = get_Csyntax full_src_path lines thy
  val (_, cse) =
      process_decls lthy {prog_name = prog_name,
        anon_vars = Config.get_global thy use_anon_vars,
        allow_underscore_idents = Config.get lthy allow_underscore_idents,
        munge_info_fname = NONE,
        owners = []} ast
  val (_, lthy) = mk_thy_types cse true false lthy
in
  lthy |> Local_Theory.exit_global
end

fun gen_umm_types_file prune files outputfile thy = let
  open ProgramAnalysis
  val (files, thy) = files thy
  val {src_path, lines, ...}:Token.file = the_single files
  val lthy = Named_Target.init [] "" thy
  val full_src_path = Path.append (Resources.master_directory thy) src_path
  val prog_name = Path.base src_path |> Path.split_ext |> fst |> Path.file_name
  val ((ast, clang_record_infos), thy) = get_Csyntax full_src_path lines thy
  val (_, cse) =
      process_decls lthy {prog_name = prog_name,
        anon_vars = Config.get_global thy use_anon_vars,
        allow_underscore_idents = Config.get_global thy allow_underscore_idents,
        munge_info_fname = NONE,
        owners = []} ast
  val _ = CalculateState.gen_umm_types_file lthy prune cse outputfile
in
  lthy |> Local_Theory.exit_global
end


val memsafeN = "memsafe"
val typesN = "c_types"
val defsN = "c_defs"
val mtypN = "machinety"
val ghosttypN = "ghostty"
val rootsN = "roots"
val prunetypesN = "prune_types"
val skip_asmN = "skip_asm"

local
  structure P = Parse
  structure K = Keyword
  structure O = CParser_Options

  val opts = [
        (memsafeN   , Option_Scanner.bool_opt O.map_memsafe (SOME true)),
        (typesN     , Option_Scanner.bool_opt O.map_c_types (SOME true)),
        (defsN      , Option_Scanner.bool_opt O.map_c_defs (SOME true)),
        (prunetypesN, Option_Scanner.bool_opt O.map_prune_types (SOME true)),
        (mtypN      , Option_Scanner.string_opt O.map_machinety NONE),
        (ghosttypN  , Option_Scanner.string_opt O.map_ghostty NONE),
        (rootsN     , Option_Scanner.string_list_opt O.map_roots NONE),
        (skip_asmN  , Option_Scanner.bool_opt O.map_skip_asm (SOME true))
    ];

in

fun new_include s thy = C_Includes.map (fn sl => s::sl) thy

val _ = Outer_Syntax.command @{command_keyword "new_C_include_dir"}
                            "add a directory to the include path"
                            (P.embedded >> (Toplevel.theory o new_include))

fun file_inclusion install =
  Resources.provide_parse_files single -- (Option_Scanner.get_options O.default_options opts)
   >> (Toplevel.theory o install)

val _ =
    Outer_Syntax.command
     @{command_keyword "include_C_file"}
     "include a C file"
     (Resources.provide_parse_files single --
       (@{keyword "for"} |-- P.path)  >> (Toplevel.theory o include_C_file))

val _ =
    Outer_Syntax.command
      @{command_keyword "install_C_file"}
      "import a C file"
      (file_inclusion install_C_file)

val _ =
    Outer_Syntax.command
      @{command_keyword "install_C_file_expect_reject"}
      "import a C file, expect an error message and skip"
      (file_inclusion install_C_file_expect_reject)

val _ =
    Outer_Syntax.command
      @{command_keyword "install_C_types"}
      "install types from a C file"
      (Resources.provide_parse_files single >> (Toplevel.theory o install_C_types))

end

end; (* struct *)
