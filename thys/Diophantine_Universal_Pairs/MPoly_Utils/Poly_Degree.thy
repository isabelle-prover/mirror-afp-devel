theory Poly_Degree
  imports "More_More_MPoly_Type" Total_Degree_Env Poly_Extract
  keywords "poly_degree" :: thy_defn and "|"
begin

ML\<open>
(* intermediate representation of degree expressions *)
structure Degree_Expr = struct
  datatype expr =
    Const of int
  | Var   of string
  | Add   of expr * expr
  | Max   of expr * expr
  | Mul   of expr * expr
  | Term  of term (* New constructor for Isabelle terms *)

  fun c k        = Const k
  fun v name     = Var name
  fun add (x,y)  = Add (x,y)
  fun max (x,y)  = Max (x,y)
  fun mul (x,y)  = Mul (x,y)
  fun exp tm     = Term tm (* Constructor function for exponents *)

  (* convert expr into a HOL term of type nat *)
  fun to_hol expr =
    let
      fun numeral k = HOLogic.mk_number @{typ nat} k
      val plus  = Term.Const (@{const_name Groups.plus_class.plus}, @{typ "nat \<Rightarrow> nat \<Rightarrow> nat"})
      val times = Term.Const (@{const_name Groups.times_class.times}, @{typ "nat \<Rightarrow> nat \<Rightarrow> nat"})
      val maxc  = Term.Const (@{const_name Orderings.ord_class.max}, @{typ "nat \<Rightarrow> nat \<Rightarrow> nat"})
      fun conv (Const k)        = numeral k
        | conv (Var x)          = Free ("deg_" ^ x, @{typ nat})
        | conv (Add(a,b))       = plus $ conv a $ conv b
        | conv (Mul(a,b))       = times $ conv a $ conv b
        | conv (Max(a,b))       = maxc $ conv a $ conv b
        | conv (Term tm)        = tm
    in conv expr end

  (* simplify expr *)
  fun norm (Add (Const a, Const b)) = Const (a + b)
    | norm (Max (Const a, Const b)) = Const (Int.max (a, b))
    | norm (Mul (Const a, Const b)) = Const (a * b)
    | norm (Add (x, y)) = norm (Add (norm x, norm y))
    | norm (Max (x, y)) = norm (Max (norm x, norm y))
    | norm (Mul (x, y)) = norm (Mul (norm x, norm y))
    | norm e = e
end

fun to_sexpr_untyped (t: term) = 
  case t of
     f $ x => "(apply " ^ to_sexpr_untyped f ^ " " ^ to_sexpr_untyped x ^ ")"
   | Const (n, _) => "(const " ^ n ^  ")"
   | Free (n, _) => "(free " ^ n ^ ")"
   | Var (n, _) => "(var " ^  @{make_string} n ^ ")"
   | Bound n => "(bound " ^ @{make_string} n ^ ")"
   | Abs (n, _, e) => "(bound " ^ n ^ " " ^ to_sexpr_untyped e ^   ")"

(* recursively compute the degree expression of a term*)
fun compute_degree_expr ctxt deg_env deg_dict tm =
  let
    val (f, args) = Term.strip_comb tm

    fun schematic_to_free tm = case tm of
        Var ((name, _), @{typ "int mpoly"}) => Free (name, @{typ "int mpoly"})
        | a $ b => (schematic_to_free a) $ (schematic_to_free b)
        | x => x
    fun close exp = schematic_to_free exp

    fun dest_nat_numeral t =
      let val (_, k) = HOLogic.dest_number t in k end
  in
    case (f, args) of
      (* constants \<rightarrow> degree 0 *)
        (* handle MPoly constants *)
      (Const ("MPoly_Type.Const", _), _) =>
        Degree_Expr.c 0
        (* handle literal numerals *)
    | (Const (@{const_name Num.numeral_class.numeral}, _), _) =>
        Degree_Expr.c 0
    | (Const (@{const_name Groups.zero_class.zero}, _), _) =>
        Degree_Expr.c 0
    | (Const (@{const_name Groups.one_class.one}, _), _) =>
        Degree_Expr.c 0

      (* variables \<rightarrow> look up index and apply deg_env *)
    | (Const ("MPoly_Type.Var", _), [n]) =>
        let val i = dest_nat_numeral n in
          deg_env i (* default: Degree_Expr.c 1 *)
        end

      (* addition/subtraction \<rightarrow> max of degrees *)
    | (Const (@{const_name Groups.plus_class.plus}, _), [s, t]) =>
        Degree_Expr.max (compute_degree_expr ctxt deg_env deg_dict s,
                         compute_degree_expr ctxt deg_env deg_dict t)

    | (Const (@{const_name Groups.minus_class.minus}, _), [s, t]) =>
        Degree_Expr.max (compute_degree_expr ctxt deg_env deg_dict s,
                         compute_degree_expr ctxt deg_env deg_dict t)

      (* multiplication \<rightarrow> sum of degrees *)
    | (Const (@{const_name Groups.times_class.times}, _), [s, t]) =>
        Degree_Expr.add (compute_degree_expr ctxt deg_env deg_dict s,
                         compute_degree_expr ctxt deg_env deg_dict t)

      (* power \<rightarrow> multiply degree of base by exponent *)
    | (Const (@{const_name Power.power_class.power}, _), [base, exp]) =>
          let
            val d_base = compute_degree_expr ctxt deg_env deg_dict base
            val (f_exp, args_exp) = Term.strip_comb exp
            val d_exp =
              case (f_exp, args_exp) of
                (Const (@{const_name Num.numeral_class.numeral}, _), []) =>
                  Degree_Expr.c (dest_nat_numeral exp)
                | _ => Degree_Expr.exp (close exp)
          in
            Degree_Expr.mul (d_exp, d_base)
          end

      (* substitution \<rightarrow> deg_env updated for each substitution term *)
    | (Const ("Substitutions.poly_subst_list", _), [subs, body]) =>
        let
          val subst_terms = HOLogic.dest_list subs
          
          val subst_degrees = map (compute_degree_expr ctxt deg_env deg_dict) subst_terms
          
          fun new_env i =
            (List.nth (subst_degrees, i))
            handle Subscript => error
              "Referencing an ill-defined substitution! Given list has less elements than referred to."
        in
          compute_degree_expr ctxt new_env deg_dict body
        end
    
      (* dependent MPoly \<rightarrow> use dependency theorem or unfold definition *)
    | (Const (hd, _), _) =>
        let
             val closed_args = map close args
             val deg_opt = Symtab.lookup deg_dict hd
        in
          (case deg_opt of
           (* Case 1: fall back to a \<dots>_degree_correct dependency if one exists*)
           SOME deg_thm =>
               let
                  val rhs_term = (case Thm.prop_of deg_thm of
                     Const (@{const_name HOL.Trueprop}, _) $ (Const (@{const_name Orderings.less_eq}, _) $ _ $ r) => r     (* c \<le> rhs *)
                      | Const ("Pure.imp", _) $ _ $ (Const (@{const_name HOL.Trueprop}, _) $ (Const (@{const_name Orderings.less_eq}, _) $ _ $ r)) => r
                      | t => raise TERM ("poly_deg_simps is not an inequality", [t]))
                    |> Term.close_schematic_term
                  val full_rhs = Term.betapplys (rhs_term, closed_args) 
                in
                 Degree_Expr.exp full_rhs
               end
             (* Case 2: find and unfold the definition of the dependent MPoly*)
           | NONE =>
               let
                 val def_thm = Proof_Context.get_thm ctxt (hd ^ "_def")
                 val rhs_term = Thm.rhs_of def_thm |> Thm.term_of |> Term.close_schematic_term
                 val full_rhs = Term.betapplys (rhs_term, closed_args)
               in
                 compute_degree_expr ctxt deg_env deg_dict full_rhs
               end)
        end
      (* unrecognized \<rightarrow> error*)
    | (hd, _) => Degree_Expr.v (to_sexpr_untyped hd)
  end

(* generate theorem statement for poly_degree_correct *)
fun make_corr_thm_term (poly_term : term) (poly_degree_term : term) : term =
  let
    val T = fastype_of poly_term
    val total_degree_const = Const (@{const_name total_degree}, T --> @{typ nat})
    val lhs = total_degree_const $ poly_term
    val rhs = poly_degree_term
  in
    HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name "Orderings.less_eq"} (lhs, rhs))
  end

(* get definition theorems of dependent MPoly *)
fun get_deps ctxt exclude input =
  let
    val (hd, args) = strip_comb input

    fun get_def_term name =
      (case Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def")) of
        Const (@{const_name Pure.eq}, _) $ _ $ r => r     (* c \<equiv> rhs *)
        | Const (@{const_name HOL.eq},  _) $ _ $ r => r     (* c  = rhs *)
        | t => raise TERM ("poly_degree: not a definition", [t]))

    fun is_allowed s = not
                         (fold (fn a => fn b => a orelse b)
                          (map (fn r => String.isSubstring r s) exclude)
                          false)

    val args_deps = maps (get_deps ctxt exclude) args

    val hd_deps =
      case hd of
        Bound _ => []
        | Const ("Num.num.One", _) => []
        | Const ("Num.num.Bit0", _) => []
        | Const ("Num.num.Bit1", _) => []
        | Const ("Groups.zero_class.zero", _) => []
        | Const ("Groups.one_class.one", _) => []
        | Const ("Num.numeral_class.numeral", _) => []
        | Const ("Nat.semiring_1_class.of_nat", _) => []
        | Const (cname, T) =>
            if is_allowed cname andalso
               (T = @{typ "int mpoly"} orelse T = @{typ "int mpoly \<Rightarrow> int mpoly"})
            then
              cname :: get_deps ctxt exclude (get_def_term cname)
            else []
        | _ => []
  in
    hd_deps @ args_deps
  end

fun prove_total_degree_var_list context N =
  let 
    (* Returns the term for n in unary notation, i.e., Suc (Suc ... 0) *)
    fun mk_unary_nat 0 = Const (@{const_name Groups.zero_class.zero}, @{typ nat})
      | mk_unary_nat n = Const (@{const_name Nat.Suc}, @{typ "nat \<Rightarrow> nat"}) $ mk_unary_nat (n - 1);
    
    (* Generates a list of terms [0, Suc 0, ..., Suc ... (Suc 0)] up to limit-1 *)
    fun unary_nat_list limit = HOLogic.mk_list @{typ nat} (map mk_unary_nat (0 upto (limit - 1)))
                                |> Thm.cterm_of context

    val lists = (map unary_nat_list (0 upto N))
  in
    map (Simplifier.simplify context)
      (map (fn ls => Drule.infer_instantiate' context [SOME ls, NONE] @{thm total_degree_map_Var})
        lists)
  end

fun unfold_nth0 (context : Proof.context) = 
  Local_Defs.unfold_tac context ([@{thm nth0_Cons_0}, @{thm nth0_Cons_Suc}] @ prove_nat_normal context)

val PREPROCESSING_THMS : thm list = [
  @{thm Notation.Const_numeral[symmetric]},
  @{thm total_degree_env_id[symmetric]},
  @{thm nth0_Cons_0},
  @{thm nth0_Cons_Suc}]


val DEG_ENV_THMS : thm list = [
  @{thm le_trans[OF total_degree_env_Const_le]},
  @{thm le_trans[OF total_degree_env_Var_le]},
  @{thm total_degree_neg},
  @{thm le_trans[OF total_degree_env_add max.mono]},
  @{thm le_trans[OF total_degree_env_diff max.mono]},
  @{thm le_trans[OF total_degree_env_mult add_mono]},
  @{thm le_trans[OF total_degree_env_pow mult_le_mono2]},
  @{thm le_trans[OF total_degree_env_poly_subst_list]}]

(* prove correctness theorem *)
fun prove_corr_thm lthy' (corr_thm : term) def_deps deg_deps (auxthms : thm list) = 
   Goal.prove lthy' [] [] corr_thm
      (fn {context: Proof.context, prems = _: thm list} =>
        let
          val mk_le_trans2 = (fn th => th RSN (2, @{thm le_trans}))
          fun mk_env_mono th = @{thm total_degree_env_mono2} OF [th]
          val deg_rules  = map mk_env_mono deg_deps 

          val trans_auxiliary_theorems = map mk_le_trans2 auxthms
        in
          Local_Defs.unfold_tac context (def_deps @ PREPROCESSING_THMS) 
          THEN REPEAT (
            REPEAT_FIRST (resolve_tac context (
              deg_rules @ DEG_ENV_THMS @ [@{thm impI}]
            ))
            THEN unfold_nth0 context
          )
          THEN TRY (REPEAT_SOME (dresolve_tac context trans_auxiliary_theorems))
          THEN ((
            SOLVE (
              TRY (REPEAT_SOME (resolve_tac context [@{thm total_degree_env_mono3'}]))
              THEN ALLGOALS (simp_tac (context addsimps
                            (@{thms algebra_simps} @ prove_total_degree_var_list context 20)))
            )
          ) ORELSE ( 
            TRY (REPEAT_SOME (resolve_tac context [@{thm total_degree_env_mono3_bounded}]))
            THEN (auto_tac (context addsimps auxthms
              @ @{thms algebra_simps}
              @ prove_total_degree_var_list context 20
            ))
          ))
        end
        )

(* register the local_theory command *)
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>poly_degree\<close>
    "find the upper bound of the total degree of a multivariate polynomial and prove correctness"
    (Parse.name -- (Scan.option (\<^keyword>\<open>|\<close> |-- Parse.thms1)) >> (fn (raw_poly_str, args) => fn lthy : local_theory =>
      let
        (* read & typecheck term in this theory context *)
        val input_thms = case args of 
          NONE => []
        | SOME args => let
            val input_facts = map fst args
            val input_thms = List.concat (map (Proof_Context.get_fact lthy) input_facts)
            in
              input_thms
            end 

        val poly_tm = Syntax.read_term lthy raw_poly_str
        
        (* peel off the head constant to build names, extract body *)
        val (hd, _) = Term.strip_comb poly_tm
        val short =
            (case hd of
               Const (s, _) => Binding.name_of (Binding.qualified_name s)
             | Free  (s, _) => Binding.name_of (Binding.qualified_name s)
             | _            => error "poly_degree: expected a constant or free at head")
        val poly_def_thm = 
             (case Term.strip_comb poly_tm of
               (Const (cname, _), _) => Proof_Context.get_thm lthy (cname ^ "_def")
               | _ => raise TERM ("Could not locate a corresponding definition", []))
        val poly_body =
             (case Thm.prop_of poly_def_thm of
               Const (@{const_name Pure.eq}, _) $ _ $ r => r     (* c \<equiv> rhs *)
             | Const (@{const_name HOL.eq},  _) $ _ $ r => r     (* c  = rhs *)
             | t => raise TERM ("poly_degree: not a definition", [t]))

        fun fully_qualify_xstring ctxt xstr =
          let
            val const = Proof_Context.read_const {proper = false, strict = false} ctxt xstr
            val (qname, _) = Term.dest_Const const
          in
            qname
          end
        
        (* get dependent theorems *)
        val deg_dep_names = ["coding_variables.D_poly", "coding_variables.K_poly"] @
                        ["combined_variables.R_poly", "combined_variables.S_poly", "combined_variables.T_poly",
                         "combined_variables.A\<^sub>3_poly", "combined_variables.A\<^sub>2_poly", "combined_variables.A\<^sub>1_poly",
                         "combined_variables.X_poly", "combined_variables.Y_poly"]

        val f = try (fn n => Proof_Context.get_thm lthy (n ^ "_degree_correct"))
        val deg_dict_opt = fold (fn key => Symtab.update (key, f key)) deg_dep_names Symtab.empty
        
        val g = fully_qualify_xstring lthy
        val deg_dict_aux = Symtab.fold (fn (k, SOME v) => Symtab.update (g k, v) | (_, NONE) => I)
                            deg_dict_opt Symtab.empty

        fun u name =
          let val key = f name in
            if is_some key then Symtab.update (g name, the key) else I
          end

        (* for calculation *)
        val deg_dict = deg_dict_aux |> u "coding_variables.M_poly"
        val deg_thms = map #2 (Symtab.dest (deg_dict))
        
        (* for proving correctness *)
        val deg_thms_for_proof = (let val x = f "combined_variables.M_poly" in
                                    if is_some x then [the x] else [] end)
          @ map #2 (Symtab.dest deg_dict_aux)

        val disallowed_deps = "P\<^sub>1" :: "suitable_for_coding" :: Symtab.keys deg_dict

        val (_, poly_body_content) = strip_abs poly_body; (* if poly_body might be an Abs *)
        val deps = get_deps lthy disallowed_deps poly_body_content;
        val deps_unique = Library.distinct (op =) deps

        val _ = Pretty.writeln (Pretty.str_list "Definitions: " "" deps_unique);

        val def_deps_opt = (deps_unique) |> map (try (fn n => Proof_Context.get_thm lthy (n ^ "_def")))
        val def_deps = map the (List.filter is_some def_deps_opt)
        
        val _ = Pretty.writeln (Pretty.big_list "Dependency Theorems:"
                                (map (Thm.pretty_thm lthy) (def_deps @ deg_thms)));
        
        (* compute the symbolic degree AST & lower to a HOL term *)
        fun init_env (_: int) = Degree_Expr.Const 1
        val expr   = compute_degree_expr lthy init_env deg_dict poly_body
        val deg_tm = Degree_Expr.to_hol expr
        
        (* build and add the `_degree` definition *)
        val def_name  = short ^ "_degree"
        val def_const = Free (def_name, @{typ nat})
        val eqn       = Logic.mk_equals (def_const, deg_tm)        

        (* generate definition and correctness lemma for poly_degree *)
        val ((_, (_, def_thm)), lthy') = gen_def eqn lthy
        
        val corr_name = short ^ "_degree_correct"
        val corr_cterm = make_corr_thm_term poly_tm def_const
        (* val corr_cterm = make_corr_thm_term poly_tm deg_tm *)

        (* prove the correctness lemma *)
        val corr_thm = prove_corr_thm lthy' corr_cterm (poly_def_thm :: def_deps @ [def_thm]) deg_thms_for_proof input_thms
        val (_, lthy'') = lthy' |> gen_theorems (corr_name, [corr_thm]);
      in
        (* return the updated theory with definition and correctness theorem in context *)
        lthy''
      end));
\<close>


end
