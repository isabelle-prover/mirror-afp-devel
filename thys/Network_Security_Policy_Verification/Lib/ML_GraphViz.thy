theory ML_GraphViz
imports ML_GraphViz_Config
begin


ML_val{*
  val _ = writeln ("using `"^Graphviz_Platform_Config.executable_pdf_viewer^"` as pdf viewer and `"^
                   Graphviz_Platform_Config.executable_dot^"` to render graphs.");
*}


ML {*
signature GRAPHVIZ =
sig
  val open_viewer: bool Unsynchronized.ref

  val default_tune_node_format: term -> string -> string

  (* edges is a term of type ('a \<times> 'a) list *)
  
  (* @{context} default_tune_node_format (edges_format \<times> edges)list*)
  val visualize_graph: Proof.context -> (term -> string -> string) -> term -> int

  (* @{context} default_tune_node_format (edges_format \<times> edges)list*)
  val visualize_graph_pretty: Proof.context -> (term -> string -> string) -> (string * term) list-> int

end

structure Graphviz: GRAPHVIZ =
struct

(*if set to false, graphviz will not be run and not pdf will be opened. Include ML_GraphViz_Disable.thy to run in batch mode.*)
val open_viewer = Unsynchronized.ref true

val default_tune_node_format = (fn _ => I)

fun write_to_tmpfile (t: string): Path.T = 
  let 
    val p = Isabelle_System.create_tmp_path "graphviz" "graph_tmp.dot"
    val p_str = File.shell_path p
  in
    writeln ("using tmpfile " ^ p_str); File.write p (t^"\n"); p
  end

fun evaluate_term ctxt edges = 
  case Code_Evaluation.dynamic_value ctxt edges of
    SOME x => x
  | NONE => error "ML_GraphViz: failed to evaluate edges"

local

  (* viz is graphiz command, e.g. dot
     viewer is a PDF viewer, e.g. xdg-open
     retuns return code of bash command.
     noticeable side effect: generated pdf file is not deleted (maybe still open in editor)*)
  fun paint_graph (viewer: string) (viz: string) (f: Path.T): int =
    if (Isabelle_System.bash ("which "^viz)) <> 0 then
      (*TODO: `which` on windows?*)
      error "ML_GraphViz: Graphviz command not found"
    else if (Isabelle_System.bash ("which "^viewer)) <> 0 then
      error "ML_GraphViz: viewer command not found"
    else
      let
        val file = (File.shell_path (Path.base f)) (*absolute path: (File.shell_path f)*)
        val filePDF = file^".pdf";
        val cmd = (viz^" -o "^filePDF^" -Tpdf "^file^" && "^viewer^" "^filePDF) (*^" && rm "^filePDF*)
      in
        (*First cd to the temp directory, then only call the commands with relative paths. 
          This is a Windows workaround if the Windows (not cygwin) version of graphviz is installed:
            It does not understand paths such as /tmp/isabelle/.., it wants C:\tmp\..
          Hence, we cd to the tmp directory and only use relative filenames henceforth.*)
        (writeln ("cding to "^(File.shell_path (Path.dir f))); File.cd (Path.dir f));
        (writeln ("executing: "^cmd); Isabelle_System.bash cmd; ());
        Isabelle_System.bash ("rm "^file) (*cleanup dot file, PDF file will still exist*)
        (*some pdf viewers do not like it if we delete the pdf file they are currently displaying*)
      end

  fun is_valid_char c =
    (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
    (c <= #"9" andalso c >= #"0")

  val sanitize_string =
    String.map (fn c => if is_valid_char c then c else #"_")

  fun format_dot_edges ctxt tune_node_format trm =
    let
      fun format_node t = t |> Syntax.pretty_term ctxt |> Pretty.string_of |> YXML.content_of |> tune_node_format t |> sanitize_string
      fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";\n"
    in
      writeln "TODO: name clashes?"; map format_dot_edge trm
    end

  fun apply_dot_header es =
    "digraph graphname {\n" ^ implode es ^ "}"
in
  fun visualize_graph_pretty ctxt tune_node_format Es : int =
    let 
      val evaluated_edges = map (fn (str, t) => (str, evaluate_term ctxt t)) Es
      val edge_to_string =
        HOLogic.dest_list #> map HOLogic.dest_prod #> format_dot_edges ctxt tune_node_format #> implode
      val formatted_edges = map (fn (str, t) => str ^ "\n" ^ edge_to_string t) evaluated_edges
    in
      if !open_viewer then (* only run the shell commands if not disabled by open_viewer *)
        (
          apply_dot_header formatted_edges
          |> write_to_tmpfile
          |> paint_graph Graphviz_Platform_Config.executable_pdf_viewer Graphviz_Platform_Config.executable_dot
        )
      else
        (writeln "visualization disabled (Graphviz.open_viewer)"; 0)
    end
  end

fun visualize_graph ctxt tune_node_format edges =
  visualize_graph_pretty ctxt tune_node_format [("", edges)]

end;
*}


end
