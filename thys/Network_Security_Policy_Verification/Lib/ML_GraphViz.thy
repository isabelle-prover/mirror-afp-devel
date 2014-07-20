theory ML_GraphViz
imports Main
begin

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
    val p_str = File.platform_path p
  in
    writeln ("using tmpfile " ^ p_str); File.write p (t^"\n"); p
  end

fun evaluate_term thy edges = 
  case Code_Evaluation.dynamic_value thy edges of
    SOME x => x
  | NONE => error "ML_GraphViz: failed to evaluate edges"

local

  (* viz is graphiz command, e.g. dot
     viewer is a PDF viewer, e.g. xdg-open
     retuns return code of bash command *)
  fun paint_graph (viewer: string) (viz: string) (f: Path.T): int =
    if (Isabelle_System.bash ("which "^viz)) <> 0 then
      error "ML_GraphViz: Graphviz command not found"
    else if (Isabelle_System.bash ("which "^viewer)) <> 0 then
      error "ML_GraphViz: viewer command not found"
    else
      let
        val file = (File.platform_path f)
        val filePDF = file^".pdf";
        val cmd = (viz^" -o "^filePDF^" -Tpdf "^file^" && "^viewer^" "^filePDF) (*^" && rm "^filePDF*)
      in
        (writeln ("executing: "^cmd); Isabelle_System.bash cmd; ());
        Isabelle_System.bash ("rm "^file) (*cleanup dot file, PDF file will still exist*)
      end

  fun is_valid_char c =
    (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
    (c <= #"9" andalso c >= #"0")

  val sanitize_string =
    String.map (fn c => if is_valid_char c then c else #"_")

  fun format_dot_edges tune_node_format trm =
    let
      fun format_node t = t |> Syntax.pretty_term @{context} |> Pretty.string_of |> ATP_Util.unyxml |> tune_node_format t |> sanitize_string
      fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";\n"
    in
      writeln "TODO: name clashes?"; map format_dot_edge trm
    end

  fun apply_dot_header es =
    "digraph graphname {\n" ^ implode es ^ "}"
in
  fun visualize_graph_pretty thy tune_node_format Es : int =
    let 
      val evaluated_edges = map (fn (str, t) => (str, evaluate_term thy t)) Es
      val edge_to_string = HOLogic.dest_list #> map HOLogic.dest_prod #> format_dot_edges tune_node_format #> implode
      val formatted_edges = map (fn (str, t) => str ^ "\n" ^ edge_to_string t) evaluated_edges
    in
      if !open_viewer then (* only run the shell commands if not disabled by open_viewer *)
        (apply_dot_header formatted_edges
        |> write_to_tmpfile
        |> paint_graph "xdg-open" "dot")
      else
        (writeln "visualization disabled (Graphviz.open_viewer)"; 0)
    end
  end

fun visualize_graph thy tune_node_format edges =
  visualize_graph_pretty thy tune_node_format [("", edges)]

end;
*}


end
