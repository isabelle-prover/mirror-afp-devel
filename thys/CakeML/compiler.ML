signature CAKEML_COMPILER = sig
  val compiler: unit -> Path.T
  val compile_ml: string -> Path.T
  val compile_ml_file: Path.T -> Path.T
  val compile_c_file: Path.T -> Path.T
  val compile_ffi: unit -> Path.T
  val link: Path.T list -> Path.T

  val eval: string -> string
  val eval_source: Input.source -> string

  val string_of_prog: Proof.context -> term -> string

  datatype mode = Literal | Prog
  val cakeml_cmd: Proof.context -> mode -> Input.source -> unit
end

structure CakeML_Compiler : CAKEML_COMPILER = struct

fun compiler () =
  let
    val platform = getenv_strict "ISABELLE_PLATFORM64"
    val paths = [getenv_strict "ISABELLE_CAKEML_HOME", "bin", platform, "cake"]
    val file = Path.appends (map Path.explode paths)
  in
    if File.exists file then
      file
    else
      error "CakeML: unsupported platform"
  end

fun basis_ffi () =
  Path.append (Path.explode (getenv_strict "ISABELLE_CAKEML_HOME")) (Path.basic "basis_ffi.c")

fun compile_ml_file source =
  let
    val id = serial_string ()
    val output = File.tmp_path (Path.basic ("cakeml_out" ^ id ^ ".S"))

    val bash_cake = File.bash_path (compiler ())
    val bash_source = File.bash_path source
    val {out, err, rc, ...} = Bash.process (bash_cake ^ " < " ^ bash_source)
    val _ = if err <> "" then warning err else ()
  in
    if rc <> 0 orelse err <> "" then
      error "CakeML: ML compilation failed"
    else
      (File.write output out; output)
  end

fun compile_ml source =
  let
    val id = serial_string ()
    val output = File.tmp_path (Path.basic ("cakeml_in" ^ id))
    val _ = File.write output source
  in compile_ml_file output end

fun compile_c_file source =
  let
    val id = serial_string ()
    val output = File.tmp_path (Path.basic ("c_out" ^ id ^ ".o"))

    val bash_cc = File.bash_path (Path.explode (getenv_strict "ISABELLE_CC"))
    val bash_source = File.bash_path source
    val bash_output = File.bash_path output
    val {out, err, rc, ...} = Bash.process (bash_cc ^ " -c -o " ^ bash_output ^ " " ^ bash_source)
    val _ = if err <> "" then warning err else ()
    val _ = writeln out
  in
    if rc <> 0 orelse err <> "" then
      error "CakeML: C compilation failed"
    else
      output
  end

fun compile_ffi () =
  compile_c_file (basis_ffi ())

fun link sources =
  let
    val id = serial_string ()
    val output = File.tmp_path (Path.basic ("bin" ^ id ^ ".out"))

    val bash_cc = File.bash_path (Path.explode (getenv_strict "ISABELLE_CC"))
    val bash_sources = Bash.strings (map File.standard_path sources)
    val bash_output = File.bash_path output
    val {out, err, rc, ...} = Bash.process (bash_cc ^ " -o " ^ bash_output ^ " " ^ bash_sources)
    val _ = if err <> "" then warning err else ()
    val _ = writeln out
  in
    if rc <> 0 orelse err <> "" then
      error "CakeML: linking failed"
    else
      output
  end

fun eval source =
  let
    val cake = compile_ml source
    val ffi = compile_ffi ()
    val bin = link [cake, ffi]
    val {out, err, rc, ...} = Bash.process (File.bash_path bin)
    val _ = if err <> "" then warning err else ()
  in
    if rc <> 0 orelse err <> "" then
      error "CakeML: evaluation failed"
    else
      out
  end

val eval_source =
  eval o Input.source_content

fun string_of_prog ctxt t =
  let
    val (_, raw_string) =
      Thm.cterm_of ctxt (@{const print_prog} $ t)
      |> Code_Simp.dynamic_conv ctxt
      |> Thm.prop_of
      |> Logic.dest_equals
  in HOLogic.dest_string raw_string end

datatype mode = Literal | Prog

val parse_mode =
  Args.parens (Parse.reserved "literal" >> K Literal ||
               Parse.reserved "prog" >> K Prog)

fun cakeml_cmd ctxt mode source =
  let
    val source =
      case mode of
        Literal => Input.source_content source
      | Prog =>
          Syntax.implode_input source
          |> Syntax.parse_term ctxt
          |> Type.constraint @{typ Ast.prog}
          |> Syntax.check_term ctxt
          |> string_of_prog ctxt
    val _ = tracing ("Evaluating: " ^ source)
    val output = eval source
  in writeln output end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>cakeml\<close> "evalute CakeML source"
    (parse_mode -- Parse.input Parse.text >> (fn (mode, src) =>
      Toplevel.keep (fn state => cakeml_cmd (Toplevel.context_of state) mode src)))

end