theory Poly_Extract
  imports "More_More_MPoly_Type"
  keywords "poly_extract" :: thy_defn
begin

subsection \<open>Automatic generation of polynomials from Isabelle terms\<close>

ML\<open>
fun gen_def spec lthy =
  let
    val atts = [];
    val (((x, T), rhs), prove) = Local_Defs.derived_def lthy (fn _ => []) {conditional = true} spec;
    val _ = Name.reject_internal (x, []);
    val (b, mx) = (Binding.make (x, Position.none), NoSyn)
    val name = Thm.def_binding b;
    val ((lhs, (_, raw_th)), lthy2) = lthy
      |> Local_Theory.define_internal ((b, mx), ((Binding.suffix_name "_raw" name, []), rhs));
    val th = prove lthy2 raw_th;
    val lthy3 = lthy2 |> Spec_Rules.add name Spec_Rules.equational [lhs] [th];
    val ([(def_name, [th'])], lthy4) = lthy3
      |> Local_Theory.notes [((name, atts), [([th], [])])];
    val lthy5 = lthy4
      |> Code.declare_default_eqns [(th', true)];
    val lhs' = Morphism.term (Local_Theory.target_morphism lthy5) lhs;
    val _ =
      Proof_Display.print_consts true (Position.thread_data ()) lthy5
        (Frees.defined (Frees.build (Frees.add_frees lhs'))) [(x, T)];
  in ((lhs, (def_name, th')), lthy5) end;

fun gen_theorems (name, thms) lthy =
  let
    val kind = "lemma";
    val facts = [((Binding.make (name, Position.none), []), [(thms, [])])];
    val facts' = facts |> Attrib.partial_evaluation lthy;
    val (res, lthy') = lthy |> Local_Theory.notes_kind kind facts';
    val _ =
      Proof_Display.print_results
        {interactive = true, pos = Position.thread_data (), proof_state = false}
        lthy' ((kind, ""), res);
  in (res, lthy') end;

fun find_def (ctxt : Proof.context) s =
  let
    val thy = Proof_Context.theory_of ctxt;
    val axioms = (Theory.all_axioms_of thy |> map #2) @
      (Locale.get_locales thy |> maps (Locale.axioms_of thy) |> map Thm.full_prop_of)
  in
    case
      axioms
        |> List.mapPartial (fn axiom_statement =>
          case axiom_statement of
            Const ("Pure.eq", _) $ lhs $ rhs =>
              let
                val (lhs_fn, lhs_args) = strip_comb lhs;
              in
                if lhs_fn aconv s then SOME (lhs_args, rhs) else NONE
              end
          | _ => NONE
        )
    of
        def :: _ => def
      | [] => error ("Definition not found: " ^ @{make_string} s)
  end;

fun find_thm (ctxt : Proof.context) (name: string) : thm =
  case
    Proof_Context.get_fact ctxt (Facts.named name)
  of
      thm :: _ => thm
    | [] => error ("Theorem not found: " ^ name);
\<close>

ML\<open>
fun convert_num n =
  if n < 1 then
    raise Match
  else if n = 1 then
    Const ("Num.num.One", @{typ num})
  else if n mod 2 = 0 then
    Const ("Num.num.Bit0", @{typ "num \<Rightarrow> num"}) $ convert_num (n div 2)
  else
    Const ("Num.num.Bit1", @{typ "num \<Rightarrow> num"}) $ convert_num (n div 2);

fun convert_nat n =
  if n < 0 then
    raise Match
  else if n = 0 then
    Const ("Groups.zero_class.zero", @{typ nat})
  else if n = 1 then
    Const ("Groups.one_class.one", @{typ nat})
  else
    Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> nat"}) $ (convert_num n);

fun convert_nat_normal n =
  if n < 0 then
    raise Match
  else if n = 0 then
    Const ("Groups.zero_class.zero", @{typ nat})
  else
    Const ("Nat.Suc", @{typ "nat \<Rightarrow> nat"}) $ (convert_nat_normal (n - 1));

fun convert_list typ l =
  case l of
    [] => Const ("List.list.Nil", Type("List.list", [typ]))
  | s :: l' => Const ("List.list.Cons", typ --> Type("List.list", [typ]) --> Type("List.list", [typ])) $ s $ convert_list typ l';

fun dest_list l =
  case l of
    Const ("List.list.Nil", _) => []
  | Const ("List.list.Cons", _) $ s $ l' => s :: dest_list l'
  | _ => raise Match

fun get_deps input =
  let
    val (input_fn, input_args) = strip_comb input;
  in
    case (input_fn, input_args) of
      (Bound _, _) => []
    | (Const ("Num.num.One", _), _) => []
    | (Const ("Num.num.Bit0", _), _) => []
    | (Const ("Num.num.Bit1", _), _) => []
    | (Const ("Groups.zero_class.zero", _), _) => []
    | (Const ("Groups.one_class.one", _), _) => []
    | (Const ("Num.numeral_class.numeral", _), _) => []
    | (Const ("Nat.semiring_1_class.of_nat", _), _) => []
    | (Const ("Groups.plus_class.plus", _), [s, t]) => get_deps s @ get_deps t
    | (Const ("Groups.minus_class.minus", _), [s, t]) => get_deps s @ get_deps t
    | (Const ("Groups.uminus_class.uminus", _), [s]) => get_deps s
    | (Const ("Groups.times_class.times", _), [s, t]) => get_deps s @ get_deps t
    | (Const ("Power.power_class.power", _), [s, _]) => get_deps s
    | (Const ("Fun.comp", _), [Const("MPoly_Type.insertion", _), Const("Notation.nth0", _), _, _]) => []
    | (Const (dep, _), _) => [dep] @ (input_args |> filter (not o is_Free) |> maps get_deps)
    | _ => error ("Unknown term: " ^ (@{make_string} input))
  end;

fun make_mpoly var_count (input : term) : term =
  let
    val (input_fn, input_args) = strip_comb input;
  in
    case (input_fn, input_args) of
      (Bound i, []) =>
      Const ("MPoly_Type.Var", @{typ "nat \<Rightarrow> int mpoly"}) $ convert_nat (var_count - i - 1)
    | (Const ("Groups.zero_class.zero", _), []) =>
      Const ("Groups.zero_class.zero", @{typ "int mpoly"})
    | (Const ("Groups.one_class.one", _), []) =>
      Const ("Groups.one_class.one", @{typ "int mpoly"})
    | (Const ("Num.numeral_class.numeral", _), [s]) =>
      Const ("Num.numeral_class.numeral", @{typ "num => int mpoly"}) $ s
    | (Const ("Nat.semiring_1_class.of_nat", _), _) =>
      Const ("MPoly_Type.Const", @{typ "int \<Rightarrow> int mpoly"}) $ input
    | (Const ("Groups.plus_class.plus", _), [s, t]) =>
      Const ("Groups.plus_class.plus", @{typ "int mpoly \<Rightarrow> int mpoly \<Rightarrow> int mpoly"}) $ make_mpoly var_count s $ make_mpoly var_count t
    | (Const ("Groups.minus_class.minus", _), [s, t]) =>
      Const ("Groups.minus_class.minus", @{typ "int mpoly \<Rightarrow> int mpoly \<Rightarrow> int mpoly"}) $ make_mpoly var_count s $ make_mpoly var_count t
    | (Const ("Groups.uminus_class.uminus", _), [s]) =>
      Const ("Groups.uminus_class.uminus", @{typ "int mpoly \<Rightarrow> int mpoly"}) $ make_mpoly var_count s
    | (Const ("Groups.times_class.times", _), [s, t]) =>
      Const ("Groups.times_class.times", @{typ "int mpoly \<Rightarrow> int mpoly \<Rightarrow> int mpoly"}) $ make_mpoly var_count s $ make_mpoly var_count t
    | (Const ("Power.power_class.power", _), [s, t]) =>
      Const ("Power.power_class.power", @{typ "int mpoly \<Rightarrow> nat \<Rightarrow> int mpoly"}) $ make_mpoly var_count s $ t
    | (Const ("Fun.comp", _), [Const("MPoly_Type.insertion", _), Const("Notation.nth0", _), args, poly]) =>
      @{term "poly_subst_list :: _ \<Rightarrow> _ \<Rightarrow> int mpoly"} $
      (args |> dest_list |> map (make_mpoly var_count) |> convert_list @{typ "int mpoly"}) $
      poly
    | (Const(const_name, _), _) =>
      let
        val params = input_args |> filter is_Free;
        val param_types = params |> map fastype_of;
        val args = input_args |> filter (not o is_Free);
      in
        @{term "poly_subst_list :: _ \<Rightarrow> _ \<Rightarrow> int mpoly"} $
        (args |> map (make_mpoly var_count) |> convert_list @{typ "int mpoly"}) $
        (list_comb (
          Const (const_name ^ "_poly", param_types ---> @{typ "int mpoly"}),
          params
        ))
      end
    | _ => error ("Unknown term: " ^ (@{make_string} input))
  end

fun prove_nat_normal (ctxt : Proof.context) =
  List.tabulate (30, fn i =>
    let
      val statement =
        HOLogic.mk_Trueprop (HOLogic.mk_eq (
          convert_nat i,
          convert_nat_normal i
        ))
    in
      Goal.prove ctxt [] [] statement (fn {prems = _, context} =>
        Clasimp.auto_tac context
      )
    end
  ) |> tl

fun string_of_string_list (xs : string list) : string = 
  case xs of
    [] => "[]"
  | [x] => x
  | x::ys => x ^ ", " ^ string_of_string_list ys

fun string_of_terms (ctxt : Proof.context) (terms: term list): string = 
  string_of_string_list (map (Syntax.string_of_term ctxt) terms)

fun string_of_typs (ctxt : Proof.context) (typs: typ list): string = 
  string_of_string_list (map (Syntax.string_of_typ ctxt) typs)

fun print_strings (strings : string list) = 
  writeln (string_of_string_list strings)

fun print_terms (ctxt : Proof.context) (terms : term list) = 
  print_strings (map (Syntax.string_of_term ctxt) terms)

fun print_typs (ctxt : Proof.context) (typs : typ list) = 
  print_strings (map (Syntax.string_of_typ ctxt) typs)

\<close>


ML\<open>

fun make_thm_statement (converted_const: term) (input_const: term) 
  (input_def_params: term list) (var_count: int) : term =
  Const ("Pure.all", (@{typ "nat \<Rightarrow> int"} --> propT) --> propT) $ Abs (
    "fn",
    @{typ "nat \<Rightarrow> int"},
    HOLogic.mk_Trueprop (
      HOLogic.mk_eq (
        @{term "insertion :: _ \<Rightarrow> _ \<Rightarrow> int"} $ Bound 0 $ converted_const,
        list_comb (
          list_comb(Term.close_schematic_term input_const, input_def_params),
          List.tabulate (var_count, fn i => Bound 0 $ convert_nat i)
        )
      )
    )
  )

fun prove_correctness_theorem lthy' correct_thm_statement input_def converted_def dep_correct_thms = 
  Goal.prove lthy' [] [] correct_thm_statement (fn {prems = _, context} =>
    Local_Defs.unfold_tac context (prove_nat_normal lthy' @ [
      @{thm insertion_Const},
      @{thm insertion_Var},
      @{thm insertion_add},
      @{thm insertion_diff},
      @{thm insertion_neg},
      @{thm insertion_mult},
      @{thm insertion_pow},
      @{thm insertion_nth0},
      @{thm insertion_poly_subst},
      @{thm poly_subst_list_def},
      @{thm comp_def},
      (nth @{thms List.list.map} 0),
      (nth @{thms List.list.map} 1),
      @{thm nth0_Cons_0},
      @{thm nth0_Cons_Suc},
      input_def,
      converted_def
    ] @ dep_correct_thms) THEN Clasimp.auto_tac context
  );

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>poly_extract\<close>
    "extract terms as polynomials"
    (Parse.term >> (fn raw_input => fn lthy =>
      let
        val input = Syntax.read_term lthy raw_input;
        val (input_const : term, input_params : term list) = strip_comb input;

        val input_const_name = input_const |> dest_Const |> #1;
        val input_const_short_name = Binding.name_of (Binding.qualified_name input_const_name);

        val input_def : thm = find_thm lthy (input_const_name ^ "_def");
        val (input_def_params : term list, input_def_value : term) = find_def lthy input_const;

        val intparams = List.filter (fn term => let
          val termtype = fastype_of term
          in termtype = @{typ "int"}
        end) input_def_params

        val nonintparams = List.filter (fn term => let
          val termtype = fastype_of term
          in termtype <> @{typ "int"}
        end) input_def_params


        val input_def_value_with_closed_ints : term = fold lambda (rev intparams) input_def_value

        val full_substitution : (indexname * term) list = 
          ListPair.zip (map #1 (map dest_Var input_def_params), input_params)

        val substitution : (indexname * term) list =
          List.filter (fn (_, term) => 
            let 
              val termtype : typ = fastype_of term 
            in termtype <> @{typ "int"} end) 
          full_substitution

        val applied_input_def_value = subst_Vars substitution input_def_value_with_closed_ints;

        val (vars, input_def_value_content) = strip_abs applied_input_def_value;

        val deps = get_deps input_def_value_content;
        val dep_correct_thms = deps |> map (fn dep => find_thm lthy (dep ^ "_correct"));
        val var_count = vars |> length;

        val mpoly : term = make_mpoly var_count input_def_value_content;
        val ((mpoly_const, (mpoly_def_name, _)), lthy'') =
          lthy
          |> gen_def (Logic.mk_equals
                (Free (input_const_short_name ^ "_poly", @{typ "int mpoly"}), mpoly))

        val mpoly_fact : thm = find_thm lthy'' mpoly_def_name;

        val _ = writeln ("Generated definition: " ^ Syntax.string_of_term lthy mpoly)

        val correct_thm_statement : term = 
          make_thm_statement mpoly_const input_const nonintparams var_count

        val _ = writeln ("Proved correctness theorem: " ^ Syntax.string_of_term lthy correct_thm_statement)

        val correct_thm = prove_correctness_theorem lthy'' correct_thm_statement input_def mpoly_fact dep_correct_thms
        val (_, lthy''') =
          lthy'' |> gen_theorems (input_const_short_name ^ "_correct", [correct_thm]); 
        in lthy'''
end));
\<close>


end
