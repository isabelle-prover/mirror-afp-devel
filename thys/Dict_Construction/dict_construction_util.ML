infixr 5 ==>
infixr ===>
infix 1 CONTINUE_WITH CONTINUE_WITH_FW

structure Dict_Construction_Util = struct

(* general *)

fun symreltab_of_symtab tab =
  Symtab.map (K Symtab.dest) tab |>
    Symtab.dest |>
    maps (fn (k, kvs) => map (apfst (pair k)) kvs) |>
    Symreltab.make

fun split_list3 [] = ([], [], [])
  | split_list3 ((x, y, z) :: rest) =
      let val (xs, ys, zs) = split_list3 rest in
        (x :: xs, y :: ys, z :: zs)
      end

fun zip_symtabs f t1 t2 =
  let
    open Symtab
    val ord = fast_string_ord
    fun aux acc [] [] = acc
      | aux acc ((k1, x) :: xs) ((k2, y) :: ys) =
        (case ord (k1, k2) of
           EQUAL   => aux (update_new (k1, f x y) acc) xs ys
         | LESS    => raise UNDEF k1
         | GREATER => raise UNDEF k2)
      | aux _ ((k, _) :: _) [] =
          raise UNDEF k
      | aux _ [] ((k, _) :: _) =
          raise UNDEF k
  in aux empty (dest t1) (dest t2) end

fun cat_options [] = []
  | cat_options (SOME x :: xs) = x :: cat_options xs
  | cat_options (NONE :: xs) = cat_options xs

fun partition f xs = (filter f xs, filter_out f xs)

fun unappend (xs, _) = chop (length xs)

fun flat_right [] = []
  | flat_right ((x, ys) :: rest) = map (pair x) ys @ flat_right rest

(* logic *)

fun x ==> y = Logic.mk_implies (x, y)
val op ===> = Library.foldr op ==>

fun sortify_typ sort (Type (tyco, args)) = Type (tyco, map (sortify_typ sort) args)
  | sortify_typ sort (TFree (name, _)) = TFree (name, sort)
  | sortify_typ _ (TVar _) = error "TVar encountered"

fun sortify sort (Const (name, typ)) = Const (name, sortify_typ sort typ)
  | sortify sort (Free (name, typ)) = Free (name, sortify_typ sort typ)
  | sortify sort (t $ u) = sortify sort t $ sortify sort u
  | sortify sort (Abs (name, typ, term)) = Abs (name, sortify_typ sort typ, sortify sort term)
  | sortify _ (Bound n) = Bound n
  | sortify _ (Var _) = error "Var encountered"

val typify_typ = sortify_typ @{sort type}
val typify = sortify @{sort type}

fun all_frees (Free (name, typ)) = [(name, typ)]
  | all_frees (t $ u) = union (op =) (all_frees t) (all_frees u)
  | all_frees (Abs (_, _, t)) = all_frees t
  | all_frees _ = []

val all_frees' = map fst o all_frees

fun all_tfrees (TFree (name, sort)) = [(name, sort)]
  | all_tfrees (Type (_, ts)) = fold (union (op =)) (map all_tfrees ts) []
  | all_tfrees _ = []

(* printing *)

fun pretty_const ctxt const =
  Syntax.pretty_term ctxt (Const (const, Sign.the_const_type (Proof_Context.theory_of ctxt) const))

(* conversion/tactic *)

fun ANY tacs = fold (curry op APPEND) tacs no_tac
fun ANY' tacs n = fold (curry op APPEND) (map (fn t => t n) tacs) no_tac
fun TRY' tac n = TRY (tac n)

fun descend_fun_conv cv =
  cv else_conv (fn ct =>
    case Thm.term_of ct of
      _ $ _ => Conv.fun_conv (descend_fun_conv cv) ct
    | _ => Conv.no_conv ct)

fun lhs_conv cv =
  cv |> Conv.arg1_conv |> Conv.arg_conv

fun rhs_conv cv =
  cv |> Conv.arg_conv |> Conv.arg_conv

fun rewr_lhs_head_conv thm =
  safe_mk_meta_eq thm |> Conv.rewr_conv |> descend_fun_conv |> lhs_conv

fun rewr_rhs_head_conv thm =
  safe_mk_meta_eq thm |> Conv.rewr_conv |> descend_fun_conv |> rhs_conv

fun conv_result cv ct =
  Thm.prop_of (cv ct) |> Logic.dest_equals |> snd

fun changed_conv cv = fn ct =>
  let
    val res = cv ct
    val (lhs, rhs) = Thm.prop_of res |> Logic.dest_equals
  in
    if lhs aconv rhs then
      raise CTERM ("no conversion", [])
    else
      res
  end

fun multi_induct_tac rules insts arbitrary ctxt =
  let
    val insts' = map (map (SOME o pair NONE o rpair false)) insts
    val arbitrary' = map (map dest_Free) arbitrary
  in
    DETERM (Induct.induct_tac ctxt false insts' arbitrary' [] (SOME rules) [] 1)
  end

fun maybe_induct_tac (SOME rules) insts arbitrary = multi_induct_tac rules insts arbitrary
  | maybe_induct_tac NONE _ _ = K all_tac

fun (tac CONTINUE_WITH tacs) i st =
  st |> (tac i THEN (fn st' =>
    let
      val n' = Thm.nprems_of st'
      val n = Thm.nprems_of st
      fun aux [] _ = all_tac
        | aux (tac :: tacs) i = tac i THEN aux tacs (i - 1)
    in
      if n' - n + 1 <> length tacs then
        raise THM ("CONTINUE_WITH: unexpected number of emerging subgoals", 0, [st'])
      else
        aux (rev tacs) (i + n' - n) st'
    end))

fun (tac CONTINUE_WITH_FW tacs) i st =
  st |> (tac i THEN (fn st' =>
    let
      val n' = Thm.nprems_of st'
      val n = Thm.nprems_of st
      fun aux [] _ st = all_tac st
        | aux (tac :: tacs) i st = st |>
            (tac i THEN (fn st' =>
             aux tacs (i + 1 + Thm.nprems_of st' - Thm.nprems_of st) st'))
    in
      if n' - n + 1 <> length tacs then
        raise THM ("unexpected number of emerging subgoals", 0, [st'])
      else
        aux tacs i st'
    end))

fun SOLVED tac = tac THEN ALLGOALS (K no_tac)

(* theorem manipulation *)

fun contract ctxt thm =
  let
    val (((_, frees), [thm']), ctxt') = Variable.import true [thm] ctxt

    val prop = Thm.prop_of thm'
    val prems = Logic.strip_imp_prems prop
    val (lhs, rhs) =
      Logic.strip_imp_concl prop
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq

    fun used x =
      exists (exists_subterm (fn t => t = x)) prems

    val (f, xs) = strip_comb lhs
    val (g, ys) = strip_comb rhs

    fun loop [] ys = (0, (f, list_comb (g, rev ys)))
      | loop xs [] = (0, (list_comb (f, rev xs), g))
      | loop (x :: xs) (y :: ys) =
          if x = y andalso is_Free x andalso not (used x) then
            loop xs ys |> apfst (fn x => x + 1)
          else
            (0, (list_comb (f, rev (x :: xs)), list_comb (g, rev (y :: ys))))

    val (count, (lhs', rhs')) = loop (rev xs) (rev ys)

    val concl' = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs', rhs'))

    fun tac ctxt 0 = resolve_tac ctxt [thm] THEN_ALL_NEW (Method.assm_tac ctxt)
      | tac ctxt n = resolve_tac ctxt @{thms ext} THEN' tac ctxt (n - 1)

    val prop = prems ===> concl'
  in
    Goal.prove_future ctxt' [] [] prop (fn {context, ...} => HEADGOAL (tac context count))
    |> singleton (Variable.export ctxt' ctxt)
  end

(* theory *)

fun define_params_nosyn term =
  Specification.definition NONE [] [] ((Binding.empty, []), term)
  #>> snd #>> snd

fun note_thm binding thm =
  Local_Theory.note ((binding, []), [thm]) #>> snd #>> the_single

fun note_thms binding thms =
  Local_Theory.note ((binding, []), thms) #>> snd

end