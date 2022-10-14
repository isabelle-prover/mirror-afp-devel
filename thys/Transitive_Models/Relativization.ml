signature Relativization =
  sig
    structure Data: GENERIC_DATA
    val Rel_add: attribute
    val Rel_del: attribute
    val add_rel_const : Database.mode -> term -> term -> Data.T -> Data.T
    val add_constant : Database.mode -> string -> string -> Proof.context -> Proof.context
    val rem_constant : (term -> Data.T -> Data.T) -> string -> Proof.context -> Proof.context
    val db: Data.T
    val init_db : Data.T -> theory -> theory
    val get_db : Proof.context -> Data.T
    val relativ_fm: bool -> bool -> term -> Data.T -> (term * (term * term)) list * Proof.context * term list * bool -> term -> term * ((term * (term * term)) list * term list * term list * Proof.context)
    val relativ_tm: bool -> bool -> term option -> term -> Data.T -> (term * (term * term)) list * Proof.context -> term -> term * (term * (term * term)) list * Proof.context
    val read_new_const : Proof.context -> string -> term
    val relativ_tm_frm': bool -> bool -> term -> Data.T -> Proof.context -> term -> term option * term
    val relativize_def: bool -> bool -> bool -> bstring -> string -> Position.T -> Proof.context -> Proof.context
    val relativize_tm: bool -> bstring -> string -> Position.T -> Proof.context -> Proof.context
    val rel_closed_goal : string -> Position.T -> Proof.context -> Proof.state
    val iff_goal : string -> Position.T -> Proof.context -> Proof.state
    val univalent_goal : string -> Position.T -> Proof.context -> Proof.state
  end

structure Relativization : Relativization = struct

infix 6 &&&
val op &&& = Utils.&&&

infix 6 ***
val op *** = Utils.***

infix 6 @@
val op @@ = Utils.@@

infix 6 ---
val op --- = Utils.---

fun insert_abs2rel ((t, u), db) = ((t, u), Database.insert Database.abs2rel (t, t) db)

fun insert_rel2is ((t, u), db) = Database.insert Database.rel2is (t, u) db

(* relativization db of relation constructors *)
val db = [ (@{const relation}, @{const Relative.is_relation})
         , (@{const function}, @{const Relative.is_function})
         , (@{const mem}, @{const mem})
         , (@{const True}, @{const True})
         , (@{const False}, @{const False})
         , (@{const Memrel}, @{const membership})
         , (@{const trancl}, @{const tran_closure})
         , (@{const IFOL.eq(i)}, @{const IFOL.eq(i)})
         , (@{const Subset}, @{const Relative.subset})
         , (@{const quasinat}, @{const Relative.is_quasinat})
         , (@{const apply}, @{const Relative.fun_apply})
         , (@{const Upair}, @{const Relative.upair})
         ]
         |> List.foldr (insert_rel2is o insert_abs2rel) Database.empty
         |> Database.insert Database.abs2is (@{const Pi}, @{const is_funspace})

fun var_i v = Free (v, @{typ i})
fun var_io v = Free (v, @{typ "i \<Rightarrow> o"})
val const_name = #1 o dest_Const

val lookup_tm  = AList.lookup (op aconv)
val update_tm  =  AList.update (op aconv)
val join_tm = AList.join (op aconv) (K #1)

val conj_ = Utils.binop @{const "IFOL.conj"}

(* generic data *)
structure Data = Generic_Data
(
  type T = Database.db
  val empty = Database.empty (* Should we initialize this outside this file? *)
  val merge = Database.merge
);

fun init_db db = Context.theory_map (Data.put db)

fun get_db thy = Data.get (Context.Proof thy)

val read_const = Proof_Context.read_const {proper = true, strict = true}
val read_new_const = Proof_Context.read_term_pattern

fun add_rel_const mode c t = Database.insert mode (c, t)

fun get_consts thm =
  let val (c_rel, rhs) = Thm.concl_of thm |> Utils.dest_trueprop |>
                          Utils.dest_iff_tms |>> head_of
  in case try Utils.dest_eq_tms rhs of
       SOME tm => (c_rel, tm |> #2 |> head_of)
     | NONE => (c_rel, rhs |> Utils.dest_mem_tms |> #2 |> head_of)
  end

fun add_rule thm rs =
  let val (c_rel,c_abs) = get_consts thm
  (* in (add_rel_const Database.rel2is c_abs c_rel o add_rel_const Database.abs2rel c_abs c_abs) rs *)
  in (add_rel_const Database.abs2rel c_abs c_abs o add_rel_const Database.abs2is c_abs c_rel) rs
end

fun get_mode is_functional relationalising = if relationalising then Database.rel2is else if is_functional then Database.abs2rel else Database.abs2is

fun add_constant mode abs rel thy =
  let
    val c_abs = read_new_const thy abs
    val c_rel = read_new_const thy rel
    val db_map = Data.map (Database.insert mode (c_abs, c_rel))
    fun add_to_context ctxt' = Context.proof_map db_map ctxt'
    fun add_to_theory ctxt' = Local_Theory.raw_theory (Context.theory_map db_map) ctxt'
  in
    Local_Theory.target (add_to_theory o add_to_context) thy
 end

fun rem_constant rem_op c thy =
  let
    val c = read_new_const thy c
    val db_map = Data.map (rem_op c)
    fun add_to_context ctxt' = Context.proof_map db_map ctxt'
    fun add_to_theory ctxt' = Local_Theory.raw_theory (Context.theory_map db_map) ctxt'
  in
    Local_Theory.target (add_to_theory o add_to_context) thy
  end

val del_rel_const = Database.remove_abs

fun del_rule thm = del_rel_const (thm |> get_consts |> #2)

val Rel_add =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (add_rule (Thm.trim_context thm)) context);

val Rel_del =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (del_rule (Thm.trim_context thm)) context);

(* Conjunction of a list of terms *)
fun conjs [] = @{term IFOL.True}
  | conjs (fs as _ :: _) = foldr1 (uncurry conj_) fs

(* Produces a relativized existential quantification of the term t *)
fun rex p t (Free v) = @{const rex} $ p $ lambda (Free v) t
  | rex _ t (Bound _) = t
  | rex _ t tm = raise TERM ("rex shouldn't handle this.",[tm,t])

(* Constants that do not take the class predicate *)
val absolute_rels = [ @{const ZF_Base.mem}
                    , @{const IFOL.eq(i)}
                    , @{const Memrel}
                    , @{const True}
                    , @{const False}
                    ]

(* Creates the relational term corresponding to a term of type i. If the last
  argument is (SOME v) then that variable is not bound by an existential
  quantifier.
*)
fun close_rel_tm pred tm tm_var rs =
  let val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs
      val (vars, tms) = split_list (map #2 news) ||> (curry op @) (the_list tm)
      val vars = case tm_var of
        SOME w => filter (fn v => not (v = w)) vars
      | NONE => vars
  in fold (fn v => fn t => rex pred (incr_boundvars 1 t) v) vars (conjs tms)
  end

fun relativ_tms __ _ _ rs ctxt [] = ([], rs, ctxt)
  | relativ_tms is_functional relationalising pred rel_db rs ctxt (u :: us) =
      let val (w_u, rs_u, ctxt_u) = relativ_tm is_functional relationalising NONE pred rel_db (rs, ctxt) u
          val (w_us, rs_us, ctxt_us) = relativ_tms is_functional relationalising pred rel_db rs_u ctxt_u us
      in (w_u :: w_us, join_tm (rs_u , rs_us), ctxt_us)
      end
and
    (* The result of the relativization of a term is a triple consisting of
      a. the relativized term (it can be a free or a bound variable but also a Collect)
      b. a list of (term * (term, term)), taken as a map, which is used
         to reuse relativization of different occurrences of the same term. The
         first element is the original term, the second its relativized version,
         and the last one is the predicate corresponding to it.
      c. the resulting context of created variables.
    *)
    relativ_tm is_functional relationalising mv pred rel_db (rs,ctxt) tm =
      let
      (* relativization of a fully applied constant *)
      fun mk_rel_const mv c (args, after) abs_args ctxt =
        case Database.lookup (get_mode is_functional relationalising) c rel_db of
          SOME p =>
            let
              val args' = List.filter (not o member (op =) (Utils.frees p)) args
              val (v, ctxt1) =
                the_default
                  (Variable.variant_fixes [""] ctxt |>> var_i o hd)
                  (Utils.map_option (I &&& K ctxt) mv)
              val args' =
                (* FIXME: This special case for functional relativization of sigma should not be needed *)
                if c = @{const Sigma} andalso is_functional
                  then
                    let
                      val t = hd args'
                      val t' = Abs ("uu_", @{typ "i"}, (hd o tl) args' |> incr_boundvars 1)
                    in
                      [t, t']
                    end
                  else
                    args'
              val arg_list = if after then abs_args @ args' else args' @ abs_args
              val r_tm =
                if is_functional
                  then list_comb (p, if p = c then arg_list else pred :: arg_list)
                  else list_comb (p, if (not o null) args' andalso  hd args' = pred then arg_list @ [v] else pred :: arg_list @ [v])
            in
              if is_functional
                then (r_tm, r_tm, ctxt)
                else (v, r_tm, ctxt1)
            end
        | NONE => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)
      (* relativization of a partially applied constant *)
      fun relativ_app mv mctxt tm abs_args (Const c) (args, after) rs =
            let
              val (w_ts, rs_ts, ctxt_ts) = relativ_tms is_functional relationalising pred rel_db rs (the_default ctxt mctxt) args
              val (w_tm, r_tm, ctxt_tm) = mk_rel_const mv (Const c) (w_ts, after) abs_args ctxt_ts
              val rs_ts' = if is_functional then rs_ts else update_tm (tm, (w_tm, r_tm)) rs_ts
            in
              (w_tm, rs_ts', ctxt_tm)
            end
        | relativ_app _ _ _ _ t _ _ =
            raise TERM ("Tried to relativize an application with a non-constant in head position",[t])

      (* relativization of non dependent product and sum *)
      fun relativ_app_no_dep mv tm c t t' rs =
          if loose_bvar1 (t', 0)
            then
              raise TERM("A dependency was found when trying to relativize", [tm])
            else
              relativ_app mv NONE tm [] c ([t, incr_boundvars ~1 t'], false) rs

      fun relativ_replace mv t body after ctxt' =
        let
          val (v, b) = Utils.dest_abs body |>> var_i ||> after
          val (b', (rs', ctxt'')) =
            relativ_fm is_functional relationalising pred rel_db (rs, ctxt', single v, false) b |>> incr_boundvars 1 ||> #1 &&& #4
        in
          relativ_app mv (SOME ctxt'') tm [lambda v b'] @{const Replace} ([t], false) rs'
        end

      fun get_abs_body (Abs body) = body
        | get_abs_body t = raise TERM ("Term is not Abs", [t])

      fun go _ (Var _) = raise TERM ("Var: Is this possible?",[])
        | go mv (@{const Replace} $ t $ Abs body) = relativ_replace mv t body I ctxt
        (* It is easier to rewrite RepFun as Replace before relativizing,
           since { f(x) . x \<in> t } = { y . x \<in> t, y = f(x) } *)
        | go mv (@{const RepFun} $ t $ Abs body) =
            let
              val (y, ctxt') = Variable.variant_fixes [""] ctxt |>> var_i o hd
            in
              relativ_replace mv t body (lambda y o Utils.eq_ y o incr_boundvars 1) ctxt'
            end
        | go mv (@{const Collect} $ t $ pc) =
            let
              val (pc', (rs', ctxt')) = relativ_fm is_functional relationalising pred rel_db (rs,ctxt, [], false) pc ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [pc'] @{const Collect} ([t], false) rs'
            end
        | go mv (@{const Least} $ pc) =
            let
              val (pc', (rs', ctxt')) = relativ_fm is_functional relationalising pred rel_db (rs,ctxt, [], false) pc ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [pc'] @{const Least} ([], false) rs'
            end
        | go mv (@{const transrec} $ t $ Abs body) =
            let
              val (res, ctxt') = Variable.variant_fixes [if is_functional then "_aux" else ""] ctxt |>> var_i o hd
              val (x, b') = Utils.dest_abs body |>> var_i
              val (y, b) = get_abs_body b' |> Utils.dest_abs |>> var_i
              val p = Utils.eq_ res b |> lambda res
              val (p', (rs', ctxt'')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt', [x, y], true) p |>> incr_boundvars 3 ||> #1 &&& #4
              val p' = if is_functional then p' |> #2 o Utils.dest_eq_tms o #2 o Utils.dest_abs o get_abs_body else p'
            in
              relativ_app mv (SOME ctxt'') tm [p' |> lambda x o lambda y] @{const transrec} ([t], not is_functional) rs'
            end
        | go mv (tm as @{const Sigma} $ t $ Abs (_, _, t')) =
            relativ_app_no_dep mv tm @{const Sigma} t t' rs
        | go mv (tm as @{const Pi} $ t $ Abs (_, _, t')) =
            relativ_app_no_dep mv tm @{const Pi} t t' rs
        | go mv (tm as @{const bool_of_o} $ t) =
            let
              val (t', (rs', ctxt')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt, [], false) t ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [t'] @{const bool_of_o} ([], false) rs'
            end
        | go mv (tm as @{const If} $ b $ t $ t') =
            let
              val (br, (rs', ctxt')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt, [], false) b ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [br] @{const If} ([t,t'], true) rs'
            end
        | go mv (@{const The} $ pc) =
            let
              val (pc', (rs', ctxt')) = relativ_fm is_functional relationalising pred rel_db (rs,ctxt, [], false) pc ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [pc'] @{const The} ([], false) rs'
            end
        | go mv (@{const recursor} $ t $ Abs body $ t') =
            let
              val (res, ctxt') = Variable.variant_fixes [if is_functional then "_aux" else ""] ctxt |>> var_i o hd
              val (x, b') = Utils.dest_abs body |>> var_i
              val (y, b) = get_abs_body b' |> Utils.dest_abs |>> var_i
              val p = Utils.eq_ res b |> lambda res
              val (p', (rs', ctxt'')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt', [x, y], true) p |>> incr_boundvars 3 ||> #1 &&& #4
              val p' = if is_functional then p' |> #2 o Utils.dest_eq_tms o #2 o Utils.dest_abs o get_abs_body else p'
              val (tr, rs'', ctxt''') = relativ_tm is_functional relationalising NONE pred rel_db (rs', ctxt'') t
            in
              relativ_app mv (SOME ctxt''') tm [tr, p' |> lambda x o lambda y] @{const recursor} ([t'], true) rs''
            end
        | go mv (@{const wfrec} $ t1 $ t2 $ Abs body) =
            let
              val (res, ctxt') = Variable.variant_fixes [if is_functional then "_aux" else ""] ctxt |>> var_i o hd
              val (x, b') = Utils.dest_abs body |>> var_i
              val (y, b) = get_abs_body b' |> Utils.dest_abs |>> var_i
              val p = Utils.eq_ res b |> lambda res
              val (p', (rs', ctxt'')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt', [x, y], true) p |>> incr_boundvars 3 ||> #1 &&& #4
              val p' = if is_functional then p' |> #2 o Utils.dest_eq_tms o #2 o Utils.dest_abs o get_abs_body else p'
            in
              relativ_app mv (SOME ctxt'') tm [p' |> lambda x o lambda y] @{const wfrec} ([t1,t2], not is_functional) rs'
            end
        | go mv (@{const wfrec_on} $ t1 $ t2 $ t3 $ Abs body) =
            let
              val (res, ctxt') = Variable.variant_fixes [if is_functional then "_aux" else ""] ctxt |>> var_i o hd
              val (x, b') = Utils.dest_abs body |>> var_i
              val (y, b) = get_abs_body b' |> Utils.dest_abs |>> var_i
              val p = Utils.eq_ res b |> lambda res
              val (p', (rs', ctxt'')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt', [x, y], true) p |>> incr_boundvars 3 ||> #1 &&& #4
              val p' = if is_functional then p' |> #2 o Utils.dest_eq_tms o #2 o Utils.dest_abs o get_abs_body else p'
            in
              relativ_app mv (SOME ctxt'') tm [p' |> lambda x o lambda y] @{const wfrec_on} ([t1,t2,t3], not is_functional) rs'
            end
        | go mv (@{const Lambda} $ t $ Abs body) =
            let
              val (res, ctxt') = Variable.variant_fixes [if is_functional then "_aux" else ""] ctxt |>> var_i o hd
              val (x, b) = Utils.dest_abs body |>> var_i
              val p = Utils.eq_ res b |> lambda res
              val (p', (rs', ctxt'')) = relativ_fm is_functional relationalising pred rel_db (rs, ctxt', [x], true) p |>> incr_boundvars 2 ||> #1 &&& #4
              val p' = if is_functional then p' |> #2 o Utils.dest_eq_tms o #2 o Utils.dest_abs o get_abs_body else p'
              val (tr, rs'', ctxt''') = relativ_tm is_functional relationalising NONE pred rel_db (rs', ctxt'') t
            in
              relativ_app mv (SOME ctxt''') tm [tr, p' |> lambda x] @{const Lambda} ([], true) rs''
            end
        (* The following are the generic cases *)
        | go mv (tm as Const _) = relativ_app mv NONE tm [] tm ([], false) rs
        | go mv (tm as _ $ _) = (strip_comb tm ||> I &&& K false |> uncurry (relativ_app mv NONE tm [])) rs
        | go _ tm = if is_functional then (tm, rs, ctxt) else (tm, update_tm (tm,(tm,tm)) rs, ctxt)

      (* we first check if the term has been already relativized as a variable *)
      in case lookup_tm rs tm of
           NONE => go mv tm
         | SOME (w, _) => (w, rs, ctxt)
      end
and
  relativ_fm is_functional relationalising pred rel_db (rs, ctxt, vs, is_term) fm =
  let

  (* relativization of a fully applied constant *)
  fun relativ_app (ctxt, rs) c args = case Database.lookup (get_mode is_functional relationalising) c rel_db of
    SOME p =>
      let (* flag indicates whether the relativized constant is absolute or not. *)
        val flag = not (exists (curry op aconv c) absolute_rels orelse c = p)
        val (args, rs_ts, ctxt') = relativ_tms is_functional relationalising pred rel_db rs ctxt args
        (* TODO: Verify if next line takes care of locales' definitions *)
        val args' = List.filter (not o member (op =) (Utils.frees p)) args
        val args'' = if not (null args') andalso hd args' = pred then args' else pred :: args'
        val tm = list_comb (p, if flag then args'' else args')
        (* TODO: Verify if next line is necessary *)
        val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs_ts
        val (vars, tms) = split_list (map #2 news)
        (* val vars = filter (fn v => not (v = tm)) vars *) (* Verify if this line is necessary *)
       in (tm, (rs_ts, vars, tms, ctxt'))
       end
   | NONE   => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

  fun close_fm quantifier (f, (rs, vars, tms, ctxt)) =
    let
      fun contains_b0 t = loose_bvar1 (t, 0)

      fun contains_extra_var t = fold (fn v => fn acc => acc orelse fold_aterms (fn t => fn acc => t = v orelse acc) t false) vs false

      fun contains_b0_extra t = contains_b0 t orelse contains_extra_var t

      (* t1 $ v \<hookrightarrow> t2 iff v \<in> FV(t2) *)
      fun chained_frees (_ $ v) t2 = member (op =) (Utils.frees t2) v
        | chained_frees t _ = raise TERM ("Malformed term", [t])

      val tms_to_close = filter contains_b0_extra tms |> Utils.reachable chained_frees tms
      val tms_to_keep = map (incr_boundvars ~1) (tms --- tms_to_close)
      val vars_to_close = inter (op =) (map (List.last o #2 o strip_comb) tms_to_close) vars
      val vars_to_keep = vars --- vars_to_close
      val new_rs =
        rs
        |> filter (fn (k, (v, rel)) => not (contains_b0_extra k orelse contains_b0_extra v orelse contains_b0_extra rel))
        |> map (fn (k, (v, rel)) => (incr_boundvars ~1 k, (incr_boundvars ~1 v, incr_boundvars ~1 rel)))

      val f' =
        if not is_term andalso not quantifier andalso is_functional
          then pred $ Bound 0 :: (map (curry (op $) pred) vs) @ [f]
          else [f]
    in
      (fold (fn v => fn t => rex pred (incr_boundvars 1 t) v) vars_to_close (conjs (f' @ tms_to_close)),
       (new_rs, vars_to_keep, tms_to_keep, ctxt))
    end

  (* Handling of bounded quantifiers. *)
  fun bquant (ctxt, rs) quant conn dom pred =
    let val (v,pred') = Utils.dest_abs pred |>> var_i
    in
      go (ctxt, rs, false) (quant $ (lambda v o incr_boundvars 1) (conn $ (@{const mem} $ v $ dom) $ pred'))
    end
  and
  bind_go (ctxt, rs) const f f' =
    let
      val (r , (rs1, vars1, tms1, ctxt1)) = go (ctxt, rs, false) f
      val (r', (rs2, vars2, tms2, ctxt2)) = go (ctxt1, rs1, false) f'
    in
      (const $ r $ r', (rs2, vars1 @@ vars2, tms1 @@ tms2, ctxt2))
    end
  and
      relativ_eq_var (ctxt, rs) v t =
        let
          val (_, rs', ctxt') = relativ_tm is_functional relationalising (SOME v) pred rel_db (rs, ctxt) t
          val f = lookup_tm rs' t |> #2 o the
          val rs'' = filter (not o (curry (op =) t) o #1) rs'
          val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs''
          val (vars, tms) = split_list (map #2 news)
        in
          (f, (rs'', vars, tms, ctxt'))
        end
  and
      relativ_eq (ctxt, rs) t1 t2 =
        if is_functional orelse ((is_Free t1 orelse is_Bound t1) andalso (is_Free t2 orelse is_Bound t2)) then
          relativ_app (ctxt, rs) @{const IFOL.eq(i)} [t1, t2]
        else if is_Free t1 orelse is_Bound t1 then
          relativ_eq_var (ctxt, rs) t1 t2
        else if is_Free t2 orelse is_Bound t2 then
          relativ_eq_var (ctxt, rs) t2 t1
        else
          relativ_app (ctxt, rs) @{const IFOL.eq(i)} [t1, t2]
  and
      go (ctxt, rs, _         ) (@{const IFOL.conj} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.conj} f f'
    | go (ctxt, rs, _         ) (@{const IFOL.disj} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.disj} f f'
    | go (ctxt, rs, _         ) (@{const IFOL.Not} $ f) = go (ctxt, rs, false) f |>> ((curry op $) @{const IFOL.Not})
    | go (ctxt, rs, _         ) (@{const IFOL.iff} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.iff} f f'
    | go (ctxt, rs, _         ) (@{const IFOL.imp} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.imp} f f'
    | go (ctxt, rs, _         ) (@{const IFOL.All(i)} $ f) = go (ctxt, rs, true) f |>> ((curry op $) (@{const OrdQuant.rall} $ pred))
    | go (ctxt, rs, _         ) (@{const IFOL.Ex(i)} $ f) = go (ctxt, rs, true) f |>> ((curry op $) (@{const OrdQuant.rex} $ pred))
    | go (ctxt, rs, _         ) (@{const Bex} $ f $ Abs p) = bquant (ctxt, rs) @{const Ex(i)} @{const IFOL.conj} f p
    | go (ctxt, rs, _         ) (@{const Ball} $ f $ Abs p) = bquant (ctxt, rs) @{const All(i)} @{const IFOL.imp} f p
    | go (ctxt, rs, _         ) (@{const rall} $ _ $ p) = go (ctxt, rs, true) p |>> (curry op $) (@{const rall} $ pred)
    | go (ctxt, rs, _         ) (@{const rex} $ _ $ p) = go (ctxt, rs, true) p |>> (curry op $) (@{const rex} $ pred)
    | go (ctxt, rs, _         ) (@{const IFOL.eq(i)} $ t1 $ t2) = relativ_eq (ctxt, rs) t1 t2
    | go (ctxt, rs, _         ) (Const c) = relativ_app (ctxt, rs) (Const c) []
    | go (ctxt, rs, _         ) (tm as _ $ _) = strip_comb tm |> uncurry (relativ_app (ctxt, rs))
    | go (ctxt, rs, quantifier) (Abs (v, _, t)) =
      let
        val new_rs = map (fn (k, (v, rel)) => (incr_boundvars 1 k, (incr_boundvars 1 v, incr_boundvars 1 rel))) rs
      in
        go (ctxt, new_rs, false) t |> close_fm quantifier |>> lambda (var_i v)
      end
    | go _ t = raise TERM ("Relativization of formulas cannot handle this case.",[t])
  in
    go (ctxt, rs, false) fm
  end


fun relativ_tm_frm' is_functional relationalising cls_pred db ctxt tm =
  let
    fun get_bounds (l as Abs _) = op @@ (strip_abs l |>> map (op #1) ||> get_bounds)
      | get_bounds (t as _$_) = strip_comb t |> op :: |> map get_bounds |> flat
      | get_bounds _ = []

    val ty = fastype_of tm
    val initial_ctxt = fold Utils.add_to_context (get_bounds tm) ctxt
  in
    case ty of
        @{typ i} =>
          let
            val (w, rs, _) =  relativ_tm is_functional relationalising NONE cls_pred db ([], initial_ctxt) tm
          in
            if is_functional
              then (NONE, w)
              else (SOME w, close_rel_tm cls_pred NONE (SOME w) rs)
          end
      | @{typ o} =>
          let
            fun close_fm (f, (_, vars, tms, _)) =
              fold (fn  v => fn t => rex cls_pred (incr_boundvars 1 t) v) vars (conjs (f :: tms))
          in
            (NONE, relativ_fm is_functional relationalising cls_pred db ([], initial_ctxt, [], false) tm |> close_fm)
          end
      | ty' => raise TYPE ("We can relativize only terms of types i and o", [ty'], [tm])
  end

fun lname ctxt = Local_Theory.full_name ctxt o Binding.name

fun destroy_first_lambdas (Abs (body as (_, ty, _))) =
     Utils.dest_abs body ||> destroy_first_lambdas |> (#1 o #2) &&& ((fn v => Free (v, ty)) *** #2) ||> op ::
  | destroy_first_lambdas t = (t, [])

fun freeType (Free (_, ty)) = ty
  | freeType t = raise TERM ("freeType", [t])

fun relativize_def is_external is_functional relationalising def_name thm_ref pos lthy =
  let
    val ctxt = lthy
    val (vars,tm,ctxt1) = Utils.thm_concl_tm ctxt (thm_ref ^ "_def")
    val db' = Data.get (Context.Proof lthy)
    val (tm, lambdavars) = tm |> destroy_first_lambdas o #2 o Utils.dest_eq_tms' o Utils.dest_trueprop
    val ctxt1 = fold Utils.add_to_context (map Utils.freeName lambdavars) ctxt1
    val (cls_pred, ctxt1, vars, lambdavars) =
      if (not o null) vars andalso (#2 o #1 o hd) vars = @{typ "i \<Rightarrow> o"} then
        ((Thm.term_of o #2 o hd) vars, ctxt1, tl vars, lambdavars)
      else if null vars andalso (not o null) lambdavars andalso (freeType o hd) lambdavars = @{typ "i \<Rightarrow> o"} then
        (hd lambdavars, ctxt1, vars, tl lambdavars)
      else Variable.variant_fixes ["N"] ctxt1 |>> var_io o hd |> (fn (cls, ctxt) => (cls, ctxt, vars, lambdavars))
    val db' = db' |> Database.insert Database.abs2rel (cls_pred, cls_pred)
                     o Database.insert Database.rel2is (cls_pred, cls_pred)
    val (v,t) = relativ_tm_frm' is_functional relationalising cls_pred db' ctxt1 tm
    val t_vars = sort_strings (Term.add_free_names tm [])
    val vs' = List.filter (#1 #> #1 #> #1 #> Ord_List.member String.compare t_vars) vars
    val vs = cls_pred :: map (Thm.term_of o #2) vs' @ lambdavars @ the_list v
    val at = List.foldr (uncurry lambda) t vs
    val abs_const = read_const lthy (if is_external then thm_ref else lname lthy thm_ref)
    fun new_const ctxt' = read_new_const ctxt' def_name
    fun db_map ctxt' =
       Data.map (add_rel_const (get_mode is_functional relationalising) abs_const (new_const ctxt'))
    fun add_to_context ctxt' = Context.proof_map (db_map ctxt') ctxt'
    fun add_to_theory ctxt' = Local_Theory.raw_theory (Context.theory_map (db_map ctxt')) ctxt'
  in
    lthy
    |> Local_Theory.define ((Binding.name def_name, NoSyn), ((Binding.name (def_name ^ "_def"), []), at))
    |>> (#2 #> (fn (s,t) => (s,[t])))
    |> Utils.display "theorem" pos
    |> Local_Theory.target (add_to_theory o add_to_context)
  end

fun relativize_tm is_functional def_name term pos lthy =
  let
    val ctxt = lthy
    val (cls_pred, ctxt1) = Variable.variant_fixes ["N"] ctxt |>> var_io o hd
    val tm = Syntax.read_term ctxt1 term
    val db' = Data.get (Context.Proof lthy)
    val db' = db' |> Database.insert Database.abs2rel (cls_pred, cls_pred)
                     o Database.insert Database.rel2is (cls_pred, cls_pred)
    val vs' = Variable.add_frees ctxt1 tm []
    val ctxt2 = fold Utils.add_to_context (map #1 vs') ctxt1
    val (v,t) = relativ_tm_frm' is_functional false cls_pred db' ctxt2 tm
    val vs = cls_pred :: map Free vs' @ the_list v
    val at = List.foldr (uncurry lambda) t vs
  in
    lthy
    |> Local_Theory.define ((Binding.name def_name, NoSyn), ((Binding.name (def_name ^ "_def"), []), at))
    |>> (#2 #> (fn (s,t) => (s,[t])))
    |> Utils.display "theorem" pos
  end

val op $` = curry ((op $) o swap)
infix $`

fun is_free_i (Free (_, @{typ "i"})) = true
  | is_free_i _ = false

fun rel_closed_goal target pos lthy =
  let
    val (_, tm, _) = Utils.thm_concl_tm lthy (target ^ "_rel_def")
    val (def, tm) = tm |> Utils.dest_eq_tms'
    fun first_lambdas (Abs (body as (_, ty, _))) =
        if ty = @{typ "i"}
          then (op ::) (Utils.dest_abs body |>> Utils.var_i ||> first_lambdas)
          else Utils.dest_abs body |> first_lambdas o #2
      | first_lambdas _ = []
    val (def, vars) = Term.strip_comb def ||> filter is_free_i
    val vs = vars @ first_lambdas tm
    val class = Free ("M", @{typ "i \<Rightarrow> o"})
    val def = fold (op $`) (class :: vs) def
    val hyps = map (fn v => class $ v |> Utils.tp) vs
    val concl = class $ def
    val goal = Logic.list_implies (hyps, Utils.tp concl)
    val attribs = @{attributes [intro, simp]}
  in
    Proof.theorem NONE (fn thmss => Utils.display "theorem" pos
                                    o Local_Theory.note ((Binding.name (target ^ "_rel_closed"), attribs), hd thmss))
    [[(goal, [])]] lthy
  end

fun iff_goal target pos lthy =
  let
    val (_, tm, ctxt') = Utils.thm_concl_tm lthy (target ^ "_rel_def")
    val (_, is_def, ctxt) = Utils.thm_concl_tm ctxt' ("is_" ^ target ^ "_def")
    val is_def = is_def |> Utils.dest_eq_tms' |> #1 |> Term.strip_comb |> #1
    val (def, tm) = tm |> Utils.dest_eq_tms'
    fun first_lambdas (Abs (body as (_, ty, _))) =
        if ty = @{typ "i"}
          then (op ::) (Utils.dest_abs body |>> Utils.var_i ||> first_lambdas)
          else Utils.dest_abs body |> first_lambdas o #2
      | first_lambdas _ = []
    val (def, vars) = Term.strip_comb def ||> filter is_free_i
    val vs = vars @ first_lambdas tm
    val class = Free ("M", @{typ "i \<Rightarrow> o"})
    val def = fold (op $`) (class :: vs) def
    val ty = fastype_of def
    val res = if ty = @{typ "i"}
                then Variable.variant_fixes ["res"] ctxt |> SOME o Utils.var_i o hd o #1
                else NONE
    val is_def = fold (op $`) (class :: vs @ the_list res) is_def
    val hyps = map (fn v => class $ v |> Utils.tp) (vs @ the_list res)
    val concl = @{const "IFOL.iff"} $ is_def
              $ (if ty = @{typ "i"} then (@{const IFOL.eq(i)} $ the res $ def) else def)
    val goal = Logic.list_implies (hyps, Utils.tp concl)
  in
    Proof.theorem NONE (fn thmss => Utils.display "theorem" pos
                                    o Local_Theory.note ((Binding.name ("is_" ^ target ^ "_iff"), []), hd thmss))
    [[(goal, [])]] lthy
  end

fun univalent_goal target pos lthy =
  let
    val (_, tm, ctxt) = Utils.thm_concl_tm lthy ("is_" ^ target ^ "_def")
    val (def, tm) = tm |> Utils.dest_eq_tms'
    fun first_lambdas (Abs (body as (_, ty, _))) =
        if ty = @{typ "i"}
          then (op ::) (Utils.dest_abs body |>> Utils.var_i ||> first_lambdas)
          else Utils.dest_abs body |> first_lambdas o #2
      | first_lambdas _ = []
    val (def, vars) = Term.strip_comb def ||> filter is_free_i
    val vs = vars @ first_lambdas tm
    val n = length vs
    val vs = List.take (vs, n - 2)
    val class = Free ("M", @{typ "i \<Rightarrow> o"})
    val def = fold (op $`) (class :: vs) def
    val v = Variable.variant_fixes ["A"] ctxt |> Utils.var_i o hd o #1
    val hyps = map (fn v => class $ v |> Utils.tp) (v :: vs)
    val concl = @{const "Relative.univalent"} $ class $ v $ def
    val goal = Logic.list_implies (hyps, Utils.tp concl)
  in
    Proof.theorem NONE (fn thmss => Utils.display "theorem" pos
                                    o Local_Theory.note ((Binding.name ("univalent_is_" ^ target), []), hd thmss))
    [[(goal, [])]] lthy
  end

end

local
  val full_mode_parser =
       Scan.option (((Parse.$$$ "functional" |-- Parse.$$$ "relational") >> K Database.rel2is)
                    || (((Scan.option (Parse.$$$ "absolute")) |-- Parse.$$$ "functional") >> K Database.abs2rel)
                    || (((Scan.option (Parse.$$$ "absolute")) |-- Parse.$$$ "relational") >> K Database.abs2is))
       >> (fn mode => the_default Database.abs2is mode)

  val reldb_parser =
       Parse.position (full_mode_parser -- (Parse.string -- Parse.string));

  val singlemode_parser = (Parse.$$$ "absolute" >> K Database.remove_abs)
                       || (Parse.$$$ "functional" >> K Database.remove_rel)
                       || (Parse.$$$ "relational" >> K Database.remove_is)

  val reldb_rem_parser = Parse.position (singlemode_parser -- Parse.string)

  val mode_parser =
       Scan.option ((Parse.$$$ "relational" >> K false) || (Parse.$$$ "functional" >> K true))
       >> (fn mode => if is_none mode then false else the mode)

  val relativize_parser =
       Parse.position (mode_parser -- (Parse.string -- Parse.string) -- (Scan.optional (Parse.$$$ "external" >> K true) false));

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>reldb_add\<close> "ML setup for adding relativized/absolute pairs"
       (reldb_parser >> (fn ((mode, (abs_term,rel_term)),_) =>
          Relativization.add_constant mode abs_term rel_term))

  val _ =
   Outer_Syntax.local_theory \<^command_keyword>\<open>reldb_rem\<close> "ML setup for adding relativized/absolute pairs"
     (reldb_rem_parser >> (uncurry Relativization.rem_constant o #1))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>relativize\<close> "ML setup for relativizing definitions"
       (relativize_parser >> (fn (((is_functional, (bndg,thm)), is_external),pos) =>
          Relativization.relativize_def is_external is_functional false thm bndg pos))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>relativize_tm\<close> "ML setup for relativizing definitions"
       (relativize_parser >> (fn (((is_functional, (bndg,term)), _),pos) =>
          Relativization.relativize_tm is_functional term bndg pos))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>relationalize\<close> "ML setup for relativizing definitions"
       (relativize_parser >> (fn (((is_functional, (bndg,thm)), is_external),pos) =>
          Relativization.relativize_def is_external is_functional true thm bndg pos))

  val _ =
    Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>rel_closed\<close> "ML setup for rel_closed theorem"
      (Parse.position (Parse.$$$ "for" |-- Parse.string) >> (fn (target,pos) =>
        Relativization.rel_closed_goal target pos))

  val _ =
    Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>is_iff_rel\<close> "ML setup for rel_closed theorem"
      (Parse.position (Parse.$$$ "for" |-- Parse.string) >> (fn (target,pos) =>
        Relativization.iff_goal target pos))

  val _ =
    Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>univalent\<close> "ML setup for rel_closed theorem"
      (Parse.position (Parse.$$$ "for" |-- Parse.string) >> (fn (target,pos) =>
        Relativization.univalent_goal target pos))

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>Rel\<close> (Attrib.add_del Relativization.Rel_add Relativization.Rel_del)
      "declaration of relativization rule") ;
in
end
