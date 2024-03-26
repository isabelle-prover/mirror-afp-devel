
signature CODE_GO =
sig
  val target: string
end;

structure Code_Go : CODE_GO =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;

val target = "Go";

fun map_terms_bottom_up f (t as IConst _) = f t
  | map_terms_bottom_up f (t as IVar _) = f t
  | map_terms_bottom_up f (t1 `$ t2) = f
      (map_terms_bottom_up f t1 `$ map_terms_bottom_up f t2)
  | map_terms_bottom_up f ((v, ty) `|=> (t, rty)) = f
      ((v, ty) `|=> (map_terms_bottom_up f t, rty))
  | map_terms_bottom_up f (ICase { term = t, typ = ty, clauses = clauses, primitive = t0 }) = f
      (ICase { term = map_terms_bottom_up f t, typ = ty,
        clauses = (map o apply2) (map_terms_bottom_up f) clauses,
        primitive = map_terms_bottom_up f t0 });

fun range_of_head t =
  case fst (Code_Thingol.unfold_app t) of
    IConst {range, ...} => range

val print_go_string =
  let
    fun unicode i = "\\u" ^ align_right "0" 4 (Int.fmt StringCvt.HEX i)
    fun char "\"" = "\\\""
      | char "\\" = "\\\\"
      | char c =
         let val i = ord c
         in if i < 32 orelse i > 126
          then unicode i
          else if i >= 128
          then error "non-ASCII byte in Go string literal"
          else c
        end;
  in quote o translate_string char end;


fun block_enclose (prt1, prt2) prts = (* Pretty.block_enclose (prt1, prt2) prts*)
  Pretty.chunks [Pretty.block (Pretty.fbreaks ((Pretty.unbreakable prt1) :: prts)), Pretty.unbreakable prt2];

fun print_go_numeral num = "Bigint.MkInt(\"" ^ signed_string_of_int num ^ "\")";

val literals = Literals {
  literal_string = print_go_string,
  literal_numeral = print_go_numeral,
  literal_list = enum "," "[" "]",
  infix_cons = (6, "<no infix cons operator in  go>") (* TODO: this will go wrong if ever used *)
};



(* the subset of thingol we actually need for Go *)
datatype go_stmt = Fun of typscheme * ((iterm list * iterm) * (thm option * bool)) list
  | Datatype of vname list * ((string * vname list) * itype list) list
  | Class of (vname * ((class * class) list * (string * itype) list))
  | Datatypecons of string
  | Instance of { class: string, tyco: string, vs: (vname * sort) list,
        superinsts: (class * (itype * dict list) list) list,
        inst_params: ((string * (const * int)) * (thm * bool)) list,
        superinst_params: ((string * (const * int)) * (thm * bool)) list };

fun print_go_stmt gen_stringer undefineds infinite_types tyco_syntax const_syntax reserved
    args_num is_sum_type is_class_param is_constr (deresolve, deresolve_full) =
  let
    fun lookup_tyvar tyvars = lookup_var tyvars;
    fun intro_tyvars vs = intro_vars (map fst vs);
    val deresolve_const = deresolve o Constant;
    val deresolve_class = deresolve o Type_Class;
    val deresolve_classrel = deresolve o Class_Relation;
    val deresolve_inst = deresolve o Class_Instance;
    val deresolve_tyco = deresolve o Type_Constructor;
    val oneline = Pretty.unbreakable o semicolon;
    val block = Pretty.unbreakable o Pretty.block;
    val spaced = Pretty.unbreakable o concat;

    fun mk_dest_name name =  Long_Name.map_base_name (fn s => s^"_dest") name
    fun applify_constraints _ head [] = head
     | applify_constraints tyvars head vs = let
          val anys = (block o commas o map (str o lookup_tyvar tyvars)) vs
         in block [head, str "[", anys, Pretty.brk 1, str "any", str "]"] end

    fun print_go_typ tyvars (tyco `%% tys) = (case tyco_syntax tyco of
        NONE => apply_constraints tyvars ((str o deresolve_tyco) tyco) tys
      | SOME (_, print) => print (K (print_go_typ tyvars)) NOBR tys)
    | print_go_typ tyvars (ITyVar v) = (str o lookup_tyvar tyvars) v
    and apply_constraints tyvars head vs =
      gen_applify false "[" "]" (print_go_typ tyvars) NOBR head vs

    (* uncurried types of functions in type classes are special-cased here *)
    fun print_go_typ_uncurried_toplevel tyvars (typ as "fun" `%% _) = let
          val (args, rtyp) = Code_Thingol.unfold_fun typ
          val head = applify "(" ")" (print_go_typ tyvars) NOBR (str "func") args;
        in concat [head, print_go_typ tyvars rtyp] end
    | print_go_typ_uncurried_toplevel tyvars typ =
        block [str "func () ", print_go_typ tyvars typ]

    (* wrap a statement into an immediately called function to make it an expression *)
    fun wrap_into_lambda tyvars typ body =
      block_enclose
        (concat [str "func ()", print_go_typ tyvars typ, str "{"], str "}()") body
    fun wrap_in_return t = oneline [str "return", t]
    fun wrap_if true = wrap_in_return
      | wrap_if false = I

    fun print_func head body = block_enclose
      (block [str "func ", head, str " {"], str "}")
      [body];
    fun print_func_head tyvars vars const tvs extras params tys rty = let
      val args = params ~~ tys
      |> map (fn (param, ty) => let
         val name = case param of
           NONE => "_" | SOME n => lookup_var vars n;
         in Pretty.block [str name, Pretty.brk 1, print_go_typ tyvars ty] end)
      |> (curry op @ extras)
      |> enum "," "(" ")"
      val sym = case const of
        SOME name => (str o deresolve) name
      | NONE => str ""
      val func_head = concat (applify_constraints tyvars sym tvs :: [args, rty]);
      in func_head
    end;

    (* a definition of a datatype *)
    fun print_go_typedef tyco vs cos reserved = let
      val [p,m] = Name.invent (snd reserved) "p" 2
      val ctxt = Name.declare p (Name.declare m (snd reserved))
      val tyargs = map ITyVar vs
      val self = tyco `%% tyargs
      val tyvars = intro_tyvars (map (rpair []) vs) reserved;
      val allowed_infinite = List.exists (fn n => n = tyco) infinite_types

      fun print_constructor m type_name ((name,_), tys) = let
        val named_fields = Name.invent_names ctxt "A" tys
        val fields = named_fields
         |> map (fn (name, arg) => oneline [str name, print_go_typ tyvars arg])
        val head = applify_constraints tyvars (str name) vs
        val typ = apply_constraints tyvars (str name) tyargs
        val elim_body = if type_name = NONE
          then let
            val case_branch = block
              [str "return ", (Pretty.block o commas) (map (fn (field,_) => str (p^"."^field)) named_fields)]
          in (*Pretty.chunks
            [oneline [str ((if null named_fields then "_ = " else m^" := ")^p^".("), typ , str ")"]
            ,*) case_branch end
          else Pretty.block [oneline [str "return ", (Pretty.block o commas) (map (fn (field,_) => str (p^"."^field)) named_fields)]]
        val elim_name = mk_dest_name (case type_name of
            NONE => name
          | SOME name' => name')
        val eliminator = if null tys then str "" else print_func
          (applify "(" ")" I NOBR (Pretty.block [applify_constraints tyvars (str elim_name) vs, str ("("^p^" "), typ, str ")"])  (map (print_go_typ tyvars o snd) named_fields))
          elim_body
        val pretty = name ^ "(" ^ (fold (curry (op ^)) (map (K "%v") fields) "") ^ ")"
        val constr = oneline [block_enclose (concat [str "type", head, str "struct {"], str "}")
          fields]
        in (constr, eliminator) end
      in if not allowed_infinite andalso length cos = 1 then case cos of
        [((name,_),tys)] => let
          val name = deresolve_const name
          val tname = deresolve_tyco tyco
          val (constr, dest) = print_constructor m (SOME name) ((tname, []), tys)
        in Pretty.chunks [constr, dest] end
      else let
          val (constrs, destrs) = cos
            |> map (fn ((name,_),tys) => ((deresolve_const name, []),tys))
            |> map (print_constructor m NONE)
            |> split_list
          val names = map (fn ((name,_),_) => (str o deresolve_const) name) cos
          val comment = block (str "// sum type which can be " :: Pretty.commas names)
          val any = oneline [str "type", applify_constraints tyvars ((str o deresolve_tyco) tyco) vs, str "any"]
        in Pretty.chunks (comment :: any :: constrs @ destrs)  end
      end;


    fun print_classrels [] ps = Pretty.block ps
      | print_classrels rels ps = let
        val postfix = rels
          |> map (fn (self, super) => (Long_Name.base_name o deresolve_classrel) (self, super))
          |> rev
          |> String.concatWith "."
        in block (ps @ [str ".", str postfix]) end
    fun print_dict tyvars (Dict (classrels, x)) =
      print_classrels classrels (print_plain_dict tyvars x)
    and print_plain_dict tyvars (Dict_Const (inst, args)) = let
        val needs_mono = true (* not (length args = 0)*)
        val (typargs, dss) = split_list args
        val wrap = if needs_mono
          then fn head => apply_constraints tyvars head typargs
          else I
      in wrap ((str o deresolve_inst) inst)
         :: (if needs_mono then [((enum "," "(" ")") o map (print_dict tyvars) o flat) dss] else []) end
    | print_plain_dict tyvars (Dict_Var { var, index, length, ... }) =
      [str (if length = 1 then var ^ "_"
         else var ^ string_of_int (index + 1) ^ "_")]

    fun wrap_new_scope term =
      block_enclose (str "{", str "};") [term]

    fun type_of_primitive_pattern t =
      let
        val destructor = case fst (Code_Thingol.unfold_app t) of
          IConst const => const
        val extras = drop (args_num (#sym destructor)) (#dom destructor)
      in extras `--> (#range destructor)
      end

    fun print_app_expr const_syntax tyvars some_thm vars
        (app as ({ sym, dicts, dom, range, typargs, ... }, ts)) = let
        val k = length dom
        val l = args_num sym
      in if length ts = k then
        let
          val is_constr = is_constr sym
          val is_sum_type = is_sum_type sym
          val is_class_param = is_class_param sym
          val dict_args = map (print_dict tyvars) (flat dicts)
          val typ = case snd (Code_Thingol.unfold_fun range) of
            name `%% _ => name | ITyVar name => name
          val allowed_infinite = List.exists (fn n => n = typ) infinite_types
            andalso is_constr
          val _ = if is_class_param andalso not (length dict_args = 1)
            then warning "bug in print_app" else ()
          val applify' = if is_constr
            then gen_applify true "{" "}"
            else gen_applify true "(" ")"
          val (immediate, curried) = chop l ts
          val symbol = if is_constr
            then (if is_sum_type orelse allowed_infinite then sym else Type_Constructor typ)
            else sym
          val func_name = if is_class_param
            then Pretty.block [hd dict_args, str ".", (str o deresolve) symbol]
            else (str o deresolve) symbol
          fun wrap_type_args s = if is_sum_type orelse allowed_infinite
            then applify "(" ")" I APP (apply_constraints tyvars ((str o deresolve_tyco) typ) typargs) [s]
            else s
          fun wrap_type_conversion name =
            let
              val typargs = if is_constr
                (* these typargs are always the same set as the outer ones, but sometimes in different order *)
                then case range of _ `%% typargs => typargs | _ => []
                else typargs
            in if is_class_param then name
              else apply_constraints tyvars name typargs
            end
          val immediate_args = immediate
           |> map (print_go_expr const_syntax tyvars some_thm vars BR)
          val invocation = (if is_class_param orelse is_constr then immediate_args else dict_args @ immediate_args)
           |> applify' I APP (wrap_type_conversion func_name)
           |> wrap_type_args
          val curried_args = curried
           |> map (enclose "(" ")" o single o print_go_expr const_syntax tyvars some_thm vars NOBR)
          in invocation :: curried_args
        end
      else
       [print_go_expr const_syntax tyvars some_thm vars BR (Code_Thingol.saturated_application k app)]
      end
    and print_clause _ _ _ _ [] _ =
      raise Fail "there's a bug in the pattern-match translator"
    | print_clause tyvars some_thm vars p ((target, pattern) :: subps) term =
      let
        fun print_condition vars conds (constr, typargs, range, args) p q target body = let
          val destructor = (mk_dest_name o deresolve) constr
          val (tyco, typargs) = case snd (Code_Thingol.unfold_fun range) of
            a `%% typargs => (a, typargs)
          val is_boxed = is_sum_type constr orelse List.exists (fn n => n = tyco) infinite_types
          val names = map (fn (SOME n) => (str o lookup_var vars) n | NONE => str "_") args
          val any_names = exists is_some args
          val checks = conds
            |> map (fn (var,const) => concat [
                 str var,
                 str "==",
                 enclose "(" ")" [print_app false const_syntax tyvars some_thm vars NOBR (const, [])]
               ])
            |> separate (str "&&")
            |> concat
        in Pretty.chunks
           ((if is_boxed then [oneline [(block o commas) [str (if any_names then q else "_"), str p], str ":=", 
              applify ".(" ")" I NOBR (str target) [apply_constraints tyvars ((str o deresolve) constr) typargs]]]
            else [oneline [str "_ =", str target]])
          @ [(if is_boxed then block_enclose (spaced [str "if", str p, str "{"], str "}") else Pretty.chunks)
              ((if any_names then [oneline ((Pretty.block o commas) names :: [str ":=",  applify "(" ")" str NOBR (str destructor) [if is_boxed then q else target]])]
                else [])
               @ [(if null conds then Pretty.chunks else (block_enclose ((spaced [str "if", checks, str "{"]), str "}")))
                   [body]])])
        end
      in case pattern
        of IConst c =>
          let
            val checks = concat
              [str target, str "==", enclose "(" ")" [print_app false const_syntax tyvars some_thm vars NOBR (c, [])]]
            val body =  (if subps = []
              then print_go_term const_syntax tyvars some_thm vars NOBR term
              else print_clause tyvars some_thm vars p subps term)
          in block_enclose ((spaced [str "if", checks, str "{"]), str "}")
               [body]
          end
        | _ `$ _ => (case Code_Thingol.unfold_const_app pattern of
            NONE => raise Fail "bad application in pattern match"
          | SOME (constr, args) => let
            val ((arg_names, subpatterns, conds), vars') =
              fold_rev (fn term => fn ((ts, rs, cs), vars) => case term of
                  IConst c => let
                  val [name] = Name.invent (snd vars) "c" 1
                  in ((SOME name :: ts, rs,(name,c) :: cs), intro_vars [name] vars) end
                | IVar NONE => ((NONE :: ts, rs, cs), vars)
                | IVar (SOME v) => ((SOME v :: ts, rs, cs), intro_vars [v] vars)
                | _ `$ _ => let
                  val [name] = Name.invent (snd vars) "p" 1
                  in ((SOME name :: ts, (name, term) :: rs, cs), intro_vars [name] vars) end)
              args (([],[],[]), vars)
            val [q] = Name.invent (snd vars) "q" 1
            val vars = intro_vars [q] vars
            val wrapper = print_condition vars' conds (#sym constr, #typargs constr, #range constr, arg_names) p q target
            val subpatterns' = subpatterns @ subps
          in wrapper (if subpatterns' = []
            then print_go_term const_syntax tyvars some_thm vars' NOBR term
            else print_clause tyvars some_thm vars' p subpatterns' term)
          end)
        | IVar v => let
            val vars' = intro_vars (the_list v) vars
            val name_printed = case v of
              NONE => str "_" | SOME name => (str o lookup_var vars') name
            val binding = oneline [name_printed, str ":=", str target]
            val usage = case v of
                SOME _ => oneline [str "_ =", name_printed]
              | NONE => str ""
            val body = if subps = []
              then print_go_term const_syntax tyvars some_thm vars' NOBR term
              else print_clause tyvars some_thm vars' p subps term
          in
            Pretty.chunks [binding, body]
          end
        | _ => raise Fail "bad term in pattern"
      end
    and print_pattern_match is_stmt tyvars some_thm vars rtyp target clauses =
      let
        val [target_var] = Name.invent (snd vars) "target" 1
        val vars = intro_vars [target_var] vars
        val [p] = Name.invent (snd vars) "m" 1
        val vars = intro_vars [p] vars
        val target = print_go_expr const_syntax tyvars some_thm vars NOBR target
        val assignment = oneline [str target_var, str ":=", target]
        val body = assignment
           :: map (fn (pattern,term) =>
               wrap_new_scope (print_clause tyvars some_thm vars p [(target_var, pattern)] term))
           clauses @ [oneline [str "panic(\"match failed\")"]]
      in if is_stmt
        then Pretty.chunks body
        else wrap_into_lambda tyvars rtyp body
      end
    and print_app is_stmt const_syntax tyvars some_thm vars fxy (app as (const, args)) =
      if List.exists (fn name => #sym const = Constant name) undefineds then
         args
          (* the arguments may use otherwise-unused variables, so just print somewhere to make Go happy *)
          |> map (print_go_expr const_syntax tyvars some_thm vars fxy)
          |> map (fn p => oneline [ str "_ = ", p])
          |> curry (op @) [ str ("panic(\"encountered undefined function: \" + "^print_go_string (Code_Symbol.default_base (#sym const))^")") ]
          |> Pretty.chunks
       else wrap_if is_stmt (gen_print_app (print_app_expr const_syntax tyvars)
        (print_go_expr const_syntax tyvars) const_syntax some_thm vars fxy app)
    (* go has a distinction between expressions and statements which Thingol doesn't, so we just
       periodically have to wrap things into a lambda & return *)
    and print_go_term const_syntax tyvars some_thm vars fxy iterm =
        print_go_term_gen true const_syntax tyvars some_thm vars fxy iterm
    and print_go_expr const_syntax tyvars some_thm vars fxy t =
        print_go_term_gen false const_syntax tyvars some_thm vars fxy t
    and print_go_term_gen is_stmt const_syntax tyvars some_thm vars fxy t = case t of
      IConst (const as {sym,...}) => let
        in (print_app is_stmt const_syntax tyvars some_thm vars fxy (const, [])) end
    | t1 `$ t2 => (case Code_Thingol.unfold_const_app t of
         SOME app =>
          (print_app is_stmt const_syntax tyvars some_thm vars fxy app)
       | _ => wrap_if is_stmt
            (applify "(" ")" (print_go_expr const_syntax tyvars some_thm vars NOBR) fxy
                    (print_go_expr const_syntax tyvars some_thm vars BR t1) [t2]))
    | IVar NONE => raise Fail "can't return a variable with no name!"
    | IVar (SOME v) => wrap_if is_stmt (str (lookup_var vars v))
    | (params, tys) `|=> (t, rty) => let
        (* horrible workaround, please fix me upstream *)
        val rty = case t of
           ICase c => type_of_primitive_pattern (#primitive c)
           | _ => rty
        val vars' = intro_vars (map_filter I [params]) vars;
        val func_head = print_func_head tyvars vars' NONE [] [] [params] [tys] (print_go_typ tyvars rty)
        val body = print_go_term const_syntax tyvars some_thm vars' fxy t
      in wrap_if is_stmt (print_func func_head body) end
    | ICase { clauses = [], ... } => let
      val _ = warning "empty case statement; generating call to panic() ...";
      in str "panic(\"empty case\");" end
    (* this is a let-binding, represented as a case *)
    | ICase (cases as { clauses = [_], ...}) =>
      let
        val (binds, body) = Code_Thingol.unfold_let (ICase cases);
        val does_not_pattern_match = List.all (Code_Thingol.is_IVar o fst o fst) binds
      in if does_not_pattern_match then
        let
          fun print_call t vars =
            (print_go_expr const_syntax tyvars some_thm vars fxy t, vars);
          fun print_bind tyvars some_thm fxy p =
              gen_print_bind (print_go_expr const_syntax tyvars) some_thm fxy p
          fun print_assignment ((pat, _), t) vars = vars
            |> print_bind tyvars some_thm BR pat
            |>> (fn p => (oneline [p, str ":=",
                  fst (print_call t vars)]))
          fun print_left ((IVar NONE, _), t) =
            print_call t (* evaluate and discard the result; go does not allow declaring to blank *)
          | print_left ((pat as IVar (SOME _), ty), t) =
            print_assignment ((pat, ty), t)
          val (seps_ps, vars') =
            fold_map print_left binds vars;
          val term = print_go_term const_syntax tyvars some_thm vars' fxy body
        in if is_stmt then Pretty.chunks (seps_ps @ [term])
          else wrap_into_lambda tyvars (type_of_primitive_pattern (#primitive cases)) (seps_ps @ [term])
        end
      else
       print_pattern_match is_stmt tyvars some_thm vars
         (type_of_primitive_pattern (#primitive cases)) (#term cases) (#clauses cases)
      end
    | ICase cases => print_pattern_match is_stmt tyvars some_thm vars
         (type_of_primitive_pattern (#primitive cases)) (#term cases) (#clauses cases);

    fun print_dict_args tyvars vs =
      let
        fun print_single_arg length v (index, class) =
          let
            val name = if length = 1 then v^"_" else v ^ string_of_int (index + 1) ^ "_"
            val ty = apply_constraints tyvars ((str o deresolve_class) class) [ITyVar v]
          in concat [str name, ty] end
        fun print_single_dict (v, sort) = let
            val args = map_index (print_single_arg (length sort) v) sort
          in args end
      in (flat (map print_single_dict vs))
      end;


    fun print_go_func const_syntax reserved const vs ty [] =
          let
            val (tys, ty') = Code_Thingol.unfold_fun ty;
            val params = Name.invent (snd reserved) "a" (length tys);
            val tyvars = intro_tyvars vs reserved;
            val vars = intro_vars params tyvars;
        val dict_args = print_dict_args tyvars vs
        val head = print_func_head tyvars vars ((SOME o Constant) const) (map fst vs) dict_args (map SOME params) tys (print_go_typ tyvars ty');
        val _ = warning ("you appear to have defined a function "^const^" with no body; generating a call to panic() ...")
      in
        print_func head (oneline [str ("panic("^print_go_string const^")")])
      end
    | print_go_func const_syntax reserved const vs ty eqs =
      let
        val tycos = build (fold (fn ((ts, t), _) =>
          fold Code_Thingol.add_tyconames (t :: ts)) eqs);
        val tyvars = reserved
          |> intro_base_names
               (is_none o tyco_syntax) deresolve_tyco tycos
          |> intro_tyvars vs;
        val simple = case eqs
         of [((ts, _), _)] => forall Code_Thingol.is_IVar ts
          | _ => false;
        val vars1 = reserved
          |> intro_tyvars vs
          |> intro_base_names_for (is_none o const_syntax)
               deresolve (map (snd o fst) eqs);
        val params = if simple
          then (map (fn IVar x => x) o fst o fst o hd) eqs
          else map SOME (aux_params vars1 (map (fst o fst) eqs));
        val vars2 = intro_vars (map_filter I params) vars1;
        val (tys', ty') = Code_Thingol.unfold_fun_n (length params) ty;
        fun print_rhs is_stmt vars' ((_, t), (some_thm, _)) =
          print_go_term_gen is_stmt const_syntax tyvars some_thm vars' NOBR t;
        val [p] = Name.invent (snd vars2) "m" 1
        val vars3 = intro_vars [p] vars2
        fun print_fun_clause ((targets, t), (some_thm, _)) =
          let
            val used = Code_Thingol.add_varnames t []
            val vars' =
              intro_vars (build (fold Code_Thingol.add_varnames targets)) vars2;
            fun remove_unused (IVar (SOME name)) = IVar
                (if member (op =) used name then SOME name else NONE)
              | remove_unused t = t
            val clauses = params ~~ targets
              |> map (apsnd (map_terms_bottom_up remove_unused))
              |> filter (fn (_, IVar NONE) => false | _ => true)
              |> map_filter (fn (NONE, _) => NONE | (SOME v, t) => SOME (v,t))
            val clause = print_clause tyvars some_thm vars' p clauses t
          in
            wrap_new_scope clause
          end;
        val dict_args = print_dict_args tyvars vs
        val head = print_func_head tyvars vars3 ((SOME o Constant) const) (map fst vs) dict_args params tys' (print_go_typ tyvars ty');
      in (*if null params andalso null vs then
         print_var ((str o deresolve_const) const) (print_rhs false vars2 (hd eqs))
       else*)
       if simple then
          print_func head (print_rhs true vars2 (hd eqs))
        else
          print_func head (Pretty.chunks
            (map print_fun_clause eqs @ [oneline [str "panic(\"match failed\")"]]))
      end;
    fun print_typeclass tyvars sym ((target, (super, params))) =
      let
        val tyvars = intro_vars [target] tyvars
        val super_fields = super
          |> map (fn (self, super) => block [
               (str o Long_Name.base_name o deresolve_classrel) (self, super),
               Pretty.brk 1,
               apply_constraints tyvars ((str o deresolve_class) super) [ITyVar target]
             ])
        val fields = params
          |> map (fn (name,typ) => block [
               (str o deresolve_const) name, Pretty.brk 1,
               print_go_typ_uncurried_toplevel tyvars typ
             ])
          |> (curry op @) super_fields
        val head = applify_constraints tyvars ((str o deresolve_class) sym) [target]
      in block_enclose (concat [str "type", head, str "struct {"], str "}") fields
      end;
    fun print_instance tyvars (target, class) {vs, inst_params, superinsts, tyco, ...} =
      let
        val class_name = deresolve_class class
        val tyvars = intro_tyvars vs tyvars
        val tyargs = map fst vs
        val class_head = apply_constraints tyvars (str class_name) [tyco `%% (map ITyVar tyargs)]
        val sym = Class_Instance (target, class)
        val instance_name = deresolve_inst (target, class)
        val superinsts_fields = superinsts
          |> map (fn (super, dicts) => block [
              (str o Long_Name.base_name o deresolve_classrel) (class, super),
              str ":", Pretty.brk 1,
              print_dict tyvars (Dict ([], Dict_Const ((tyco, super), dicts))), str ","
            ])
         fun print_classparam_instance ((classparam, (const as { dom, ... }, dom_length)), (thm, _)) =
           let
             val aux_dom = Name.invent_names (snd reserved) "A" dom;
             val auxs = map fst aux_dom;
             val vars = intro_vars auxs tyvars;
             val (aux_dom1, aux_dom2) = chop dom_length aux_dom;
             fun abstract_using [] _ _ body = body
               | abstract_using aux_dom should_wrap rty body = let
                  val params = aux_dom
                   |> map (fn (aux, ty) =>
                       block [(str o lookup_var vars) aux, Pretty.brk 1, print_go_typ tyvars ty])
                  val head = print_func_head tyvars vars NONE [] params [] []
                       ((if should_wrap then print_go_typ_uncurried_toplevel else print_go_typ) tyvars rty)
                 in print_func head (wrap_if should_wrap body) end;
             val aux_abstract = if not (null aux_dom1) andalso not (null aux_dom2)
               then abstract_using aux_dom1 true (map snd aux_dom2 `--> #range const) o abstract_using aux_dom2 false (#range const)
               else abstract_using aux_dom1 false (#range const) o abstract_using aux_dom2 false (#range const)
             val wrap_in_func = if null aux_dom1 andalso null aux_dom2
               then print_func (print_func_head tyvars vars NONE [] [] [] [] (print_go_typ tyvars (#range const))) else I
             val wrap_aux = case (null aux_dom1, null aux_dom2) of
               (true, true) => print_func (print_func_head tyvars vars NONE [] [] [] [] (print_go_typ tyvars (#range const)))
             | (false, false) => abstract_using aux_dom1 true (map snd aux_dom2 `--> #range const) o abstract_using aux_dom2 false (#range const)
             | _ => abstract_using aux_dom1 false (#range const) o abstract_using aux_dom2 false (#range const)
           in block [
            (str o Long_Name.base_name o deresolve_const) classparam,
            str ":", Pretty.brk 1,
            (wrap_aux o wrap_in_return o print_app false const_syntax tyvars (SOME thm) vars NOBR)
              (const, map (IVar o SOME) auxs),
            str ","
           ] end;
      in let
          val body = block_enclose (concat [str "return", class_head, str "{"],str "}")
                      (superinsts_fields
                        @ map print_classparam_instance inst_params)
          val head = print_func_head tyvars reserved (SOME sym) tyargs (print_dict_args tyvars vs)
                   [] [] class_head
        in print_func head body end
      end;
    fun print_stmt (Constant const, (_, Fun ((vs, ty), raw_eqs))) =
       print_go_func const_syntax reserved const vs ty (filter (snd o snd) raw_eqs)
    | print_stmt (Type_Constructor tyco, (_, Datatype (vs, cos))) =
       print_go_typedef tyco vs cos reserved
    | print_stmt (Type_Class sym, (_, Class class)) =
       print_typeclass reserved sym class
    | print_stmt (Class_Instance sym, (_, Instance instance)) =
       print_instance reserved sym instance
    | print_stmt (_, _) = str "<unknown>" (*raise Fail "whatever this is, it's not yet supported";*)
  in print_stmt
  end;



fun variant_capitalize s ctxt =
  let
    val cs = Symbol.explode s;
    val s_lower = case cs of
      c :: cs => Symbol.to_ascii_upper c :: cs
  in ctxt
    |> Name.variant (implode s_lower)
  end;

fun go_program_of_program ctxt module_name reserved identifiers exports program =
  let
    val variant = variant_capitalize
    fun namify_module name_fragment ((nsp_class, nsp_object), nsp_common) =
      let
        val declare = Name.declare name_fragment;
      in (name_fragment, ((declare nsp_class, declare nsp_object), declare nsp_common)) end;
    fun namify_common base ((nsp_class, nsp_object), nsp_common) =
      let
        val (base', nsp_common') = variant base nsp_common
      in
        (base', ((Name.declare base' nsp_class, Name.declare base' nsp_object), nsp_common'))
      end;
    fun namify_stmt (Code_Thingol.Fun _) = namify_common
      | namify_stmt (Code_Thingol.Datatype _) = namify_common
      | namify_stmt (Code_Thingol.Datatypecons _) = namify_common
      | namify_stmt (Code_Thingol.Class _) = namify_common
      | namify_stmt (Code_Thingol.Classrel _) = namify_common
      | namify_stmt (Code_Thingol.Classparam _) = namify_common
      | namify_stmt (Code_Thingol.Classinst _) = namify_common;

    fun modify_stmt (_, (_, Code_Thingol.Fun (_, SOME _))) = NONE
      | modify_stmt (_, (export, Code_Thingol.Fun (x, _))) = SOME (export, Fun x)
      | modify_stmt (_, (export, Code_Thingol.Datatype x)) = SOME (export, Datatype x)
      | modify_stmt (_, (_, Code_Thingol.Datatypecons _)) = NONE
      | modify_stmt (Type_Class class, (export, Code_Thingol.Class x)) =
          SOME (export, Class x)
      | modify_stmt (_, (_, Code_Thingol.Classrel x)) = NONE
      | modify_stmt (_, (_, Code_Thingol.Classparam x)) = NONE
      | modify_stmt (_, (export, Code_Thingol.Classinst inst)) =
          SOME (export, Instance inst);
  in
    Code_Namespace.hierarchical_program ctxt
      { module_name = module_name, reserved = reserved, identifiers = identifiers,
        empty_nsp = ((reserved, reserved), reserved), namify_module = namify_module,
        namify_stmt = namify_stmt, cyclic_modules = false,
        class_transitive = true, class_relation_public = true, empty_data = (),
        memorize_data = K I, modify_stmts = map modify_stmt }
      exports program
  end;




fun serialize_go gen_stringer go_module undefineds infinite_types ctxt { module_name, reserved_syms,
     identifiers, includes, class_syntax, tyco_syntax, const_syntax } program exports =
  let
    (* build program *)
    val { deresolver, hierarchical_program = go_program } =
      go_program_of_program ctxt module_name (Name.make_context reserved_syms)
        identifiers exports program;

    val go_module = if go_module = "" then "isabelle/exported" else go_module;

    (* helper functions that need access to the entire program *)
    fun lookup_constr tyco constr = case Code_Symbol.Graph.get_node program (Type_Constructor tyco)
     of Code_Thingol.Datatype (_, constrs) =>
           (AList.lookup (op = o apsnd fst) constrs constr)
       | _ => NONE;
    fun is_sum_type sym = case Code_Symbol.Graph.get_node program sym of
     Code_Thingol.Datatypecons tyco => (case Code_Symbol.Graph.get_node program (Type_Constructor tyco)
     of Code_Thingol.Datatype (_, []) => false
      | Code_Thingol.Datatype (_, [_]) => false
      | Code_Thingol.Datatype _ => true
      | _ => false)
     | _ => false;

    fun is_class_param (sym as Constant const) = case Code_Symbol.Graph.get_node program sym
     of Code_Thingol.Classparam _ => true
        | _ => false
    fun classparams_of_class class = case Code_Symbol.Graph.get_node program (Type_Class class)
     of Code_Thingol.Class (_, (_, classparams)) => classparams;
    fun args_num (sym as Constant const) = case Code_Symbol.Graph.get_node program sym
     of Code_Thingol.Fun (((_, ty), []), _) =>
          (length o fst o Code_Thingol.unfold_fun) ty
      | Code_Thingol.Fun ((_, ((ts, _), _) :: _), _) => length ts
      | Code_Thingol.Datatypecons tyco => length (the (lookup_constr tyco const))
      | Code_Thingol.Classparam class =>
          (length o fst o Code_Thingol.unfold_fun o the o AList.lookup (op =)
            (classparams_of_class class)) const;
    (* print the go code *)
    fun print_stmt prefix_fragments b = ("", print_go_stmt gen_stringer undefineds infinite_types
      tyco_syntax const_syntax (make_vars reserved_syms) args_num is_sum_type is_class_param
      (Code_Thingol.is_constr program) (deresolver prefix_fragments, deresolver) b);

    fun get_imports module_name = Module module_name
      |> Code_Symbol.Graph.immediate_succs go_program
      |> map (fn (Module a) => a)
      |> (curry op @) (map fst includes)
      |> map (fn (a) => go_module ^ "/" ^ a)

    (* print modules *)
    fun print_module _ base _ ps = (base, Pretty.chunks2
      (str ("package " ^ base)
      :: block_enclose (str "import (", str ")")
          (map (str o print_go_string) (get_imports base))
      :: (map snd ps) ))


    (* serialization *)
    val p = Code_Namespace.print_hierarchical {
        print_module = print_module, print_stmt = print_stmt,
        lift_markup = K I } go_program
     |> curry (op @) includes
     |> map (apfst (fn a => [a, "exported.go"]))

    val is_single_module = length p = 1
  in (
    if is_single_module
      then Code_Target.Singleton ("go", snd (hd p))
      else Code_Target.Hierarchy ((["go.mod"], Pretty.chunks2 [
        concat [str "module",(str o print_go_string) go_module],
        str "go 1.18"
      ]) :: p),
    try (deresolver [])
  ) end;


val serializer : Code_Target.serializer =
  Code_Target.parse_args ((Scan.optional (Args.$$$ "go_module" |-- Args.name) ""
      -- Scan.optional (Args.$$$ "gen_stringer" >> K true) false
      -- Scan.optional (Args.$$$ "panic_on" |-- (Scan.repeat Parse.term)) []
      -- Scan.optional (Args.$$$ "infinite_type" |-- (Scan.repeat Parse.term)) [])
  >> (fn (((go_module, gen_stringer), undef_terms), infinite_types) => fn lthy => let
         val undefineds = map (fst o dest_Const o Syntax.read_term lthy) undef_terms
         val infinite_types = map (fst o dest_Type o Syntax.parse_typ lthy) infinite_types
       in serialize_go gen_stringer go_module undefineds infinite_types lthy end))


val _ = Theory.setup
  (Code_Target.add_language
    (target, { serializer = serializer, literals = literals,
      check = { env_var = "ISABELLE_GO",
        make_destination = fn p => p + Path.explode "export.go",
        make_command = fn p => "test -d export.go && cd export.go && $ISABELLE_GO build ./"^p^" || $ISABELLE_GO build ./export.go"},
      evaluation_args = []})
  #> Code_Target.set_printings (Type_Constructor ("fun",
    [(target, SOME (2, fn print_go_typ => fn fxy => fn [arg, rtyp] => let
        val head = applify "(" ")" (print_go_typ fxy) NOBR (str "func") [arg];
      in concat [head, print_go_typ fxy rtyp] end)
    )]))
  #> fold (Code_Target.add_reserved target) [
      "any", "break", "default", "func", "interface", "select", "case", "defer",
      "go", "map", "struct", "chan", "else", "goto", "package", "switch",
      "const", "fallthrough", "if", "range", "type", "continue", "for",
      "import", "return", "var"
    ]);


end; (*struct*)
