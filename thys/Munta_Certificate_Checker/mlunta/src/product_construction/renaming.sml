signature RENAMING = sig
  val create_renaming_symtab:
      string list -> (string IndexDict.t * int Symtab.table)
  val create_renaming_inttab:
      int list -> (int IndexDict.t * int Inttab.table)


  val mk_varf: 'a Symtab.table -> string -> 'a Error.res
  val mk_clockf: 'a Symtab.table -> string -> 'a Error.res
  val mk_locf: 'a Inttab.table -> int -> 'a Error.res

  val update:
      ('a -> ('b list, 'c) Either.t) ->
      'a Syntax.update -> ('b list, 'c Syntax.update) Either.t

  val node:
      (int -> int Error.res) ->
      (string -> int Error.res) ->
      RewriteBexpsTypes.node ->
      RenamingTypes.node Error.res

  val edge:
      (string -> int Error.res) ->
      (int -> int Error.res) ->
      (string -> int Error.res) ->
      (string -> int Error.res) ->
      RewriteBexpsTypes.edge -> RenamingTypes.edge Error.res

  val automaton:
      (string -> int Error.res) ->
      (string -> int Error.res) ->
      (string -> int Error.res) ->
      (string -> int Error.res) ->
      RewriteBexpsTypes.automaton -> RenamingTypes.automaton Error.res

  val network: RewriteBexpsTypes.network -> RenamingTypes.network Error.res
end

structure Renaming : RENAMING = struct
open Either
open Error
open CompilationError
open NamingError
open RewriteBexpsTypes
open Syntax

fun add_zero_clock clocks = "0" :: clocks

fun create_renaming_map update empty =
    IndexDict.fromList
    #> ` (IndexDict.foldli
            (fn (ix,v, acc) => update (v, ix) acc) empty)
    #> swap

fun create_renaming_symtab xs =
    xs
    |> create_renaming_map Symtab.update Symtab.empty

val naming_err = naming #> comp_err #> single

fun mk_fun err dict = Symtab.lookup dict #> from_option err
fun mk_varf dict s = mk_fun (unknown_var s |> naming_err) dict s
fun mk_clockf dict s = mk_fun (unknown_clock s |> naming_err) dict s
fun mk_procf dict s = mk_fun (unknown_proc s |> naming_err) dict s
fun mk_namef dict s = mk_fun (unknown_loc s |> naming_err) dict s
fun mk_broadcastf dict s = mk_fun (unknown_label s |> naming_err) dict s

fun create_renaming_inttab xs =
    xs
    |> create_renaming_map Inttab.update Inttab.empty

fun mk_locf dict s =
    s
    |> Inttab.lookup dict
    |> from_option (unknown_id s |> naming_err)

fun rename_clock_pair f =
    Difference.check f (Difference.Single #> succeed)
                     (Difference.Diff #> succeed)

fun update f u =
    case u of
        Reset (x, i) => f x |> mapR (fn x' => (Reset (x', i))) |
        Copy (x, y) =>  (f x <|> f y) |> mapR (fn (x', y') => Copy (x', y')) |
        Shift (x, i) =>  f x |> mapR (fn x' => (Shift (x', i))) |
        Update (x, y, c) =>  (f x <|> f y) |> mapR (fn (x', y') => Update (x', y', c))

fun node loc_f clock_f ({id, invariant, name} : node) =
    (combine_map (Constraint.map_either clock_f) invariant
                 <|> loc_f id)
    |> mapR (fn (invar, id') =>
                {
                  id = id',
                  invariant = invar,
                  name = name
                }
                )

fun edge label_f loc_f clock_f var_f
         ({source, target, g_single, g_diag, g_data, label, clock_updates,
           var_updates}
          : edge) =
    let
      fun rename_dataguard f =
          combine_map (Guard.map_either (Constraint.map_either
                                             (rename_clock_pair f)))
      fun rename_guard f =
          combine_map (Constraint.map_either (rename_clock_pair f))
      val rename_g = rename_guard clock_f
      val rename_g_data = rename_dataguard var_f
      val rename_upd_c = combine_map (update clock_f)
      val rename_upd_v = combine_map (update var_f)
      val label_f' = get_label #> label_f

      fun updates clock_updates var_updates =
          rename_upd_c clock_updates <|> rename_upd_v var_updates

      fun guards g_single g_diag g_data =
          (rename_g g_single <|> rename_g g_diag ) <|> rename_g_data g_data

      fun locs source target = loc_f source <|> loc_f target

      fun mk_edge (((gs,upds), locs), label') =
          let
            val ((g_single, g_diag), g_data) = gs
            val (c_upd, v_upd) = upds
            val (src, dest) = locs
          in
            {
              source = src,
              target = dest,
              label = label',
              g_single = g_single,
              g_diag = g_diag,
              g_data = g_data,
              clock_updates = c_upd,
              var_updates = v_upd
            }
          end
    in
      guards g_single g_diag g_data
      <|> updates clock_updates var_updates
      <|> locs source target
      <|> label_f' label
      |> mapR mk_edge
    end

(* gets set of labels *)
fun set_labels (automata : (string * automaton) list) =
    let
      val e_to_label_str = #label #> Syntax.get_label
    in
      foldl
              (fn ((_, ta), tbl) =>
                  foldl (fn (e, tbl') =>
                                Symtab.insert_set (e_to_label_str e) tbl')
                                tbl (#edges_in ta @ #edges_out ta))
              (Symtab.make_set []) automata
    end

fun create_label_dicts (automata : (string * automaton) list) =
    automata
    |> set_labels
    |> Symtab.keys
    |> IndexDict.fromList
    |> ` (IndexDict.foldli
            (fn (ix,v, acc) => Symtab.update (v, ix) acc) Symtab.empty)
    |> swap

(* renaming fun for labels*)
fun mk_fun' err dict = Symtab.lookup dict #> from_option err
fun mk_labelf dict = mk_fun' (InternalError "This should never happen!" |> single) dict

fun mk_formf dict = mk_locf dict

fun automaton
        broadcast_f
        label_f
        clock_f
        var_f
        ({edges_in, edges_out, broadcast_in, broadcast_out,
          edges_internal, nodes, initial, committed} : automaton)
    =
    let
      val loc_ls = nodes |> List.map #id
      val (ix_dict, map_loc) = create_renaming_inttab loc_ls
      val loc_f = mk_locf map_loc
      val loc_name_ls = nodes |> List.map #name
      val (ix_name_dict, map_name_loc) = create_renaming_symtab loc_name_ls
      val name_f = mk_namef map_name_loc

      fun edges es = combine_map (edge label_f loc_f clock_f var_f) es
      fun broadcast es = combine_map (edge broadcast_f loc_f clock_f var_f) es
      fun edges_internalf es = combine_map
                                   (edge (K (succeed 0)) loc_f clock_f var_f) es

      fun nodesf V = combine_map (node loc_f clock_f) V
    in
      ((edges edges_in <|> edges edges_out)
           <|> edges_internalf edges_internal
           <|> (broadcast broadcast_in
           <|> broadcast broadcast_out))
      <|> (nodesf nodes <|> loc_f initial)
      <|> (combine_map loc_f committed)
      |> mapR (fn (((((in_es, out_es), internal), (broadcast_in, broadcast_out)),
                       (V, initial')), committed) =>
                  {
                    edges_in = in_es,
                    edges_out = out_es,
                    edges_internal = internal,
                    broadcast_in = broadcast_in,
                    broadcast_out = broadcast_out,
                    nodes = V,
                    initial = initial',
                    committed = Inttab.make_set committed,
                    loc_dict = ix_dict,
                    name_dict = ix_name_dict,
                    name_f = name_f
                  }
              )
    end

fun mk_form_f_tab automata =
    foldl (fn ((proc, ta), tab') =>
              Inttab.update (proc, RenamingTypes.get_namef ta) tab')
          Inttab.empty automata

fun re_formula proc_f' var_f form_f f =
    let
      open Formula
      val success_single =
          Difference.Single #> succeed
      val success_diff =
          Difference.Diff #> succeed
      fun rename_loc ta name =
          proc_f' ta
          >>= (fn p => form_f p
          >>= (fn f => f name
          |> mapR (pair p #> Loc)))

      fun rename_var_cond c =
          Constraint.map_either
              (Difference.check var_f
                                success_single
                                success_diff) c
          |> mapR Pred

      fun renaming f' =
              case f' of
              True => succeed True |
              Not e => renaming e |> mapR Not |
              And (l, r) => renaming l <|> renaming r
                            |> mapR And |
              Or (l, r) => renaming l <|> renaming r
                           |> mapR Or |
              Impl (l, r) => renaming l <|> renaming r
                             |> mapR Impl |
              Pred c => rename_var_cond c |
              Loc (ta, name) => rename_loc ta name
    in
      case f of
              Ex f => renaming f |> mapR Ex |
              Eg f => renaming f |> mapR Eg |
              Ax f => renaming f |> mapR Ax |
              Ag f => renaming f |> mapR Ag |
              Leadsto (p, q) => renaming p <|> renaming q |> mapR Leadsto
    end

(* Here finally the zero clock is introduced *)
fun network ({automata, clocks, vars, formula, broadcast_channels} : network) =
    let
      val (ix_str_clocks, str_ix_clocks) =
              create_renaming_symtab (add_zero_clock clocks)
      val clock_f = mk_clockf str_ix_clocks

      val (ix_str_vars, str_ix_vars) =
              create_renaming_symtab (List.map (#name) vars)
      val var_f = mk_varf str_ix_vars

      val (ix_str_procs, str_ix_procs) =
              create_renaming_symtab (map fst automata)
      val proc_f' = mk_procf str_ix_procs
      fun proc_f (s, ta) = proc_f' s |> mapR (rpair ta)

      val (ix_str_labels, str_ix_labels) =
              create_label_dicts automata
      val label_f = mk_labelf str_ix_labels
      val (ix_str_broadcast, str_ix_broadcast) =
          create_renaming_symtab broadcast_channels
      val broadcast_f =
          mk_broadcastf str_ix_broadcast
    in
          combine_map
              (fn (s, ta) =>
                      automaton broadcast_f label_f clock_f var_f ta
                      |> mapR (pair s)) automata
          |> bindR (combine_map proc_f)
          |> mapR (fn tas_pre => (tas_pre, mk_form_f_tab tas_pre |> mk_formf))
          |> bindR (fn (tas, form_f) => formula
                                        |> re_formula proc_f' var_f form_f
                                        |> mapR (pair tas))
          |> mapR (fn (tas, F) =>
                          {
                            clock_dict = ix_str_clocks,
                            var_dict = ix_str_vars,
                            label_dict = ix_str_labels,
                            var_bounds = List.map (fn v => (#lower v, #upper v))
                                                  vars
                                         |> IndexDict.fromList,
                            automata = tas,
                            ta_names = ix_str_procs,
                            broadcast_dict = ix_str_broadcast,
                            formula = F
                      })
    end
end
