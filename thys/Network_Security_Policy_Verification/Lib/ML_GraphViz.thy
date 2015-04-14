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

  (*function to modify the printing of a node name*)
  val default_tune_node_format: term -> string -> string

  (* edges is a term of type ('a \<times> 'a) list *)
  
  (* @{context} default_tune_node_format (edges_format \<times> edges)list*)
  val visualize_graph: Proof.context -> (term -> string -> string) -> term -> int

  (* @{context} default_tune_node_format (edges_format \<times> edges)list graphviz_header*)
  val visualize_graph_pretty: Proof.context -> (term -> string -> string) -> (string * term) list -> string-> int

  (* helper function.
     @{context} tune_node_format node *)
  val node_to_string: Proof.context -> (term -> string -> string) ->  term -> string
  val term_to_string: Proof.context ->  term -> string;
  val term_to_string_safe: Proof.context ->  term -> string;
  val term_to_string_html: Proof.context ->  term -> string;
end

structure Graphviz: GRAPHVIZ =
struct

(*if set to false, graphviz will not be run and not pdf will be opened. Include ML_GraphViz_Disable.thy to run in batch mode.*)
val open_viewer = Unsynchronized.ref true

val default_tune_node_format: term -> string -> string = (fn _ => I)

fun write_to_tmpfile (t: string): Path.T = 
  let 
    val p = Isabelle_System.create_tmp_path "graphviz" "graph_tmp.dot"
    val p_str = File.shell_path p
  in
    writeln ("using tmpfile " ^ p_str); File.write p (t^"\n"); p
  end

fun evaluate_term (ctxt: Proof.context) edges = 
  case Code_Evaluation.dynamic_value ctxt edges of
    SOME x => x
  | NONE => error "ML_GraphViz: failed to evaluate term"


fun is_valid_char c =
  (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
  (c <= #"9" andalso c >= #"0")

val sanitize_string =
  String.map (fn c => if is_valid_char c then c else #"_")


fun term_to_string (ctxt: Proof.context) (t: term) : string = 
  (*n |> Syntax.pretty_term ctxt |> Pretty.string_of |> ATP_Util.unyxml*)
  let
    val ctxt' = Config.put show_markup false ctxt;
  in Print_Mode.setmp [] (Syntax.string_of_term ctxt') t
  end;


fun term_to_string_safe ctxt (n: term) : string = 
  let
    val str = term_to_string ctxt n
  in
    if sanitize_string str <> str then (warning ("String  "^str^" contains invalid characters!"); sanitize_string str)
     else str end;

local
  val sanitize_string_html =
    String.map (fn c => if (is_valid_char c orelse c = #" " orelse (c <= #"/" andalso c >= #"(")
                            orelse c = #"|" orelse c = #"=" orelse c = #"?" orelse c = #"!" orelse c = #"_"
                            orelse c = #"[" orelse c = #"}") then c else #"_")
in
  fun term_to_string_html ctxt (n: term) : string = 
    let
      val str = term_to_string ctxt n
    in
      if sanitize_string_html str <> str then (warning ("String  "^str^" contains invalid characters!"); sanitize_string_html str)
       else str end
end;

fun node_to_string ctxt (tune_node_format: term -> string -> string) (n: term) : string = 
  n |> term_to_string ctxt |> tune_node_format n
  handle Subscript => error ("Subscript Exception in node_to_string for string "^( Pretty.string_of (Syntax.pretty_term ctxt n)));

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

  fun format_dot_edges ctxt tune_node_format trm =
    let
      fun format_node t = let val str = node_to_string ctxt tune_node_format t in
                              if sanitize_string str <> str then
                                (warning ("Node "^str^" contains invalid characters!"); sanitize_string str)
                              else str
                            end;
      fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";\n"
    in
      map format_dot_edge trm
    end

  fun apply_dot_header header edges =
    "digraph graphname {\n#header\n" ^ header ^"\n#edges\n\n"^ implode edges ^ "}"
in
  fun visualize_graph_pretty ctxt tune_node_format Es (header:string): int =
    let 
      val evaluated_edges = map (fn (str, t) => (str, evaluate_term ctxt t)) Es
      val edge_to_string = HOLogic.dest_list #> map HOLogic.dest_prod #> format_dot_edges ctxt tune_node_format #> implode
      val formatted_edges = map (fn (str, t) => str ^ "\n" ^ edge_to_string t) evaluated_edges
    in
      if !open_viewer then (* only run the shell commands if not disabled by open_viewer *)
        (
          apply_dot_header header formatted_edges
          |> write_to_tmpfile
          |> paint_graph Graphviz_Platform_Config.executable_pdf_viewer Graphviz_Platform_Config.executable_dot
        )
      else
        (writeln "visualization disabled (Graphviz.open_viewer)"; 0)
    end
  end

fun visualize_graph ctxt tune_node_format edges =
  visualize_graph_pretty ctxt tune_node_format [("", edges)] "#TODO add header here"

end;
*}


end
