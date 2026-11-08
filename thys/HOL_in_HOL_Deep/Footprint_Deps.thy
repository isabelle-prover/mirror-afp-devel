theory Footprint_Deps
  imports Main_Results Footprint_Checks
begin

section \<open>Footprint audit, part two: choice in the model versus choice in the proof\<close>

text \<open>Theory \<open>Footprint_Checks\<close> records what the consistency argument does not use.  Two of
  its claims concern Hilbert choice, and this theory checks them mechanically rather than by
  inspection.

  \<^enum> \<^emph>\<open>No choice in the model.\<close>  The defining equations of the concrete model in theory
    \<open>Consistency\<close> --- the enumeration \<open>en\<close>, the domains \<open>cD\<close>, application \<open>cAp\<close>, abstraction
    \<open>cLm\<close>, the parameter interpretation \<open>cJv\<close> and the assignment \<open>cXi\<close> --- mention neither
    Isabelle's choice operator \<^const>\<open>Eps\<close> (\<open>SOME\<close>) nor definite description \<^const>\<open>The\<close>.

  \<^enum> \<^emph>\<open>Choice in the proof.\<close>  The transitive dependency closure of the consistency theorem,
    computed from the proof terms with \<^ML>\<open>Proofterm.fold_body_thms\<close>, does contain facts of
    theory \<open>Hilbert_Choice\<close>, among them the axiom \<open>someI\<close> itself.  They enter through the
    datatype package, through lemmas about fresh variable names in the syntax, through the
    evaluation of abstraction and quantification in the semantics, and through the soundness
    proof.  The footprint claim is therefore "no choice in the model", not "no choice in the
    proof": the latter is an inherited dependency on the meta-logic.

  Both checks fail the build if they fail; the second one also prints, for the record, every
  fact of this development in the closure that uses a \<open>Hilbert_Choice\<close> fact directly.\<close>

ML \<open>
  (* 1. No choice in the model: the defining equations are free of Eps and The. *)
  local
    val defs = @{thms en.simps cD_def cAp.simps cLm_def cJv_def cXi_def};
    fun mentions_choice t =
      Term.exists_Const (fn (c, _) => c = \<^const_name>\<open>Eps\<close> orelse c = \<^const_name>\<open>The\<close>) t;
    val bad = filter (mentions_choice o Thm.prop_of) defs;
  in
    val _ =
      if null bad then writeln "Footprint_Deps: the model's defining equations use neither SOME nor THE."
      else error ("Footprint_Deps: choice in a defining equation: " ^
                  commas (map (Thm.string_of_thm \<^context>) bad))
  end;

  (* 2. Choice in the proof: the dependency closure of the consistency theorem. *)
  local
    val thy = \<^theory>;
    fun closure thm =
      Proofterm.fold_body_thms
        (fn {thm_name = (name, _), ...} => fn acc => Symtab.update (name, ()) acc)
        [Thm.proof_body_of thm] Symtab.empty
      |> Symtab.keys;
    val deps = closure @{thm consistency};
    val choice_facts = filter (String.isPrefix "Hilbert_Choice.") deps;
    (* direct users of Hilbert_Choice facts among this development's own facts *)
    fun direct thm = Thm_Deps.thm_deps thy [thm] |> map (fn (_, (nm, i)) => (nm, i));
    fun get1 (nm, i) =
      SOME (Global_Theory.get_thm_name thy ((nm, i), Position.none)) handle ERROR _ => NONE;
    fun get (nm, i) =
      (case get1 (nm, i) of SOME th => SOME th | NONE => get1 ("HOL_in_HOL_Deep." ^ nm, i));
    val own_prefixes =
      ["Syntax.", "Semantics.", "Calculus.", "Soundness.", "Completeness.", "Consistency.",
       "NK_Infinity.", "Cantor.", "Main_Results."];
    fun is_own n = exists (fn p => String.isPrefix p n) own_prefixes;
    fun entry_points root =
      let
        fun loop [] _ acc = acc
          | loop ((nm, i) :: queue) seen acc =
              (case get (nm, i) of
                NONE => loop queue seen acc
              | SOME th =>
                  let
                    val ds = direct th;
                    val hits =
                      if is_own nm then filter (String.isPrefix "Hilbert_Choice." o fst) ds else [];
                    val acc' = if null hits then acc else insert (op =) nm acc;
                    val next = filter (fn (n, _) => is_own n andalso not (Symtab.defined seen n)) ds;
                    val seen' = fold (fn (n, _) => Symtab.update (n, ())) next seen;
                  in loop (queue @ next) seen' acc' end)
      in loop [(root, 0)] (Symtab.make [(root, ())]) [] end;
    val entries = entry_points "Main_Results.consistency" |> sort_distinct string_ord;
  in
    val _ =
      if member (op =) choice_facts "Hilbert_Choice.someI" then
        writeln ("Footprint_Deps: the consistency theorem depends on " ^
                 string_of_int (length deps) ^ " facts, " ^
                 string_of_int (length choice_facts) ^ " of them from Hilbert_Choice " ^
                 "(including someI); direct users of Hilbert_Choice facts in this development:\n  " ^
                 cat_lines (map (fn s => "  " ^ s) entries))
      else error "Footprint_Deps: expected Hilbert_Choice.someI in the closure of consistency"
  end;
\<close>

end
