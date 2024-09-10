(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory ML_Fun_Cache
  imports Pure
begin

text \<open>Extension of the basic cache in @{ML_structure "Cache"}:
\<^item> Include some statistics on cache hits / misses
\<^item> Retrieval of existing caches
\<^item> Support garbage collected caches (via weak references)
\<close>


text \<open>Combination of synchronized variables and weak references. 
Stored value might get garbage collected.
Note the difference in the signature (option value at some positions) compared to 
@{ML_structure Synchronized}.
\<close>

ML \<open>
signature SYNCHRONIZED_WEAK =
sig
  type 'a var
  val var: string -> 'a -> 'a var
  val value: 'a var -> 'a option
  val assign: 'a var -> 'a -> unit

  val timed_access: 'a var -> ('a option -> Time.time option) -> ('a option -> ('b * 'a) option) -> 'b option
  val guarded_access: 'a var -> ('a option -> ('b * 'a) option) -> 'b
  val change_result: 'a var -> ('a option -> 'b * 'a) -> 'b
  val change: 'a var -> ('a option -> 'a) -> unit

end;


structure Synchronized_Weak: SYNCHRONIZED_WEAK =
struct
  abstype 'a var = Weak_Var of ('a Unsynchronized.ref option Unsynchronized.ref) Synchronized.var
  with

(* basic operations on weak references *)

fun mk_weak x = Weak.weak (SOME (Unsynchronized.ref x))

fun get_val w = case !w of
      SOME r => SOME (!r)
    | NONE => NONE

fun map_val f w = f (get_val w)

(* the main interface *)

fun var name x = 
  Weak_Var (Synchronized.var name (mk_weak x))
 
fun value (Weak_Var x) = 
    get_val (Synchronized.value x)

fun assign (Weak_Var x) v = Synchronized.assign x (mk_weak v)

fun apply_access f w =
  case f (get_val w) of
     SOME (res, x) => SOME (res, mk_weak x)
   | NONE => NONE
 
fun timed_access (Weak_Var x) time_limit f = 
  Synchronized.timed_access x (map_val time_limit) (apply_access f)

fun guarded_access var f = the (timed_access var (fn _ => NONE) f);

(* unconditional change *)

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));
end
end
\<close>


ML \<open>

structure More_Binding = struct

\<comment>\<open>cf. @{ML Position.here}\<close>
fun here b =
  let
    val pos = Binding.pos_of b
    val text = Binding.print b
    val props = Position.properties_of pos;
    val (s1, s2) =
      (case (Position.line_of pos, Position.file_of pos) of
        (SOME i, NONE) => (" ", "(line " ^ Value.print_int i ^ ")")
      | (SOME i, SOME name) => (" ", "(line " ^ Value.print_int i ^ " of " ^ quote name ^ ")")
      | (NONE, SOME name) => (" ", "(file " ^ quote name ^ ")")
      | _ => if Position.is_reported pos then ("", "\092<^here>") else ("", ""));
  in
    Markup.markup (Markup.properties props Markup.position) (text ^ s1 ^ s2)
  end;

end

signature FUN_CACHE =
sig

  (* non garbage collected variant of cache *)
  val create: binding -> ('table -> string) -> 'table -> ('table -> 'key -> 'value lazy option) ->
    ('key * 'value lazy -> 'table -> 'table) -> ('key -> 'value) -> 'key -> 'value

  (* garbage collected variant of cache *)
  val create_gc: binding -> ('table -> string) -> 'table -> ('table -> 'key -> 'value lazy option) ->
    ('key * 'value lazy -> 'table -> 'table) -> ('key -> 'value) -> 'key -> 'value

  datatype 'content handler = Handler of {name: binding, hits: unit -> int, misses: unit -> int, 
          reset: unit -> unit, content: unit -> 'content, mk_string: 'content -> string}

  (* non garbage collected variant of cache *)
  val create_handler: binding -> ('table -> string) -> 'table -> ('table -> 'key -> 'value lazy option) ->
    ('key * 'value lazy -> 'table -> 'table) -> ('key -> 'value) -> (('key -> 'value) * 'table handler)

  (* garbage collected variant of cache *)
  val create_gc_handler: binding -> ('table -> string) -> 'table -> ('table -> 'key -> 'value lazy option) ->
    ('key * 'value lazy -> 'table -> 'table) -> ('key -> 'value) -> (('key -> 'value) * 'table handler)

  val get_handler: string -> string handler option
  val delete_handler: string -> unit
  val all_handlers: unit -> (string * string handler) list
  val cache_statistics: unit -> (binding * {hits: int, misses: int, content_size: int}) list

  val reset_cache: string -> unit
  val reset_all_caches: unit -> unit

  val get_info: 'content handler -> {name: binding, hits: int, misses: int, content: 'content, mk_string: 'content -> string}

  val dummy_handler : 'content ->  'content handler;

  val pretty_handler: 'content handler -> Pretty.T
  val string_of_handler: 'content handler -> string
end;

structure Fun_Cache: FUN_CACHE =
struct

datatype 'content handler = Handler of {name: binding, hits: unit -> int, misses: unit -> int, 
  reset: unit -> unit, content: unit -> 'content, mk_string: 'content -> string};

fun dummy_handler c = Handler {name = Binding.name "", hits = K 0, misses = K 0, reset = K (), content = K c, mk_string = K "()"};

val caches = Synchronized.var "caches" (Symtab.empty)

fun add_handler name handler = Synchronized.change caches (fn tab => 
  let
    val raw_name = Binding.name_of name
    val _ = if Symtab.defined tab raw_name then tracing ("overwriting cache: " ^ More_Binding.here name) else ()
  in Symtab.update (raw_name, handler) tab end)

fun cached_apply name lookup update f x (tab, hits, misses) =
      case lookup tab x of
        SOME y => (y, (tab, hits + 1, misses))
      | NONE =>
          let val y = Lazy.lazy_name name (fn () => f x)
          in (y, (update (x, y) tab, hits, misses + 1)) end

fun gen_apply cached_apply change_result cache =
  change_result cache cached_apply
  |> Lazy.force;

fun create_handler name mk_string empty lookup update f =
  let
    val raw_name = Binding.name_of name
    val empty_cache = (empty, 0, 0)
    val cache = Synchronized.var raw_name empty_cache;
    fun apply x = gen_apply (cached_apply raw_name lookup update f x) Synchronized.change_result cache 
     
    fun hits () = #2 (Synchronized.value cache)
    fun misses () = #3 (Synchronized.value cache)
    fun content () = #1 (Synchronized.value cache)
    fun string () = mk_string (#1 (Synchronized.value cache))
    fun reset () = Synchronized.change cache (K empty_cache)

    val handler = Handler {name = name, hits = hits, misses = misses, reset = reset, content = content, mk_string = mk_string}
    val handler' = Handler {name = name, hits = hits, misses = misses, reset = reset, content = string, mk_string = I}
    val _ = add_handler name handler'
  in (apply, handler) end;

fun create name mk_string empty lookup update f = fst (create_handler name mk_string empty lookup update f)

fun map_default_trace msg default f v =
  case v of SOME x => f x | NONE => (tracing msg; f default)

fun the_default_trace msg default v =
  case v of 
   SOME x => x
   | NONE => (tracing msg; default)

fun create_gc_handler name mk_string empty lookup update f =
  let
    val raw_name = Binding.name_of name
    val empty_cache = (empty, 0, 0)
    val cache = Synchronized_Weak.var raw_name empty_cache;
    val the_default = the_default_trace ("cache: " ^ More_Binding.here name ^ " was garbage collected")
    val map_default = map_default_trace ("cache: " ^ More_Binding.here name ^ " was garbage collected - starting with empty cache again.")

    fun apply x = gen_apply (map_default empty_cache (cached_apply raw_name lookup update f x)) Synchronized_Weak.change_result cache

    fun get cache = the_default empty_cache (Synchronized_Weak.value cache)
    fun hits () = #2 (get cache)
    fun misses () = #3 (get cache)
    fun content () = #1 (get cache)
    fun string () = mk_string (#1 (get cache))
    fun reset () = Synchronized_Weak.change cache (K empty_cache)

    val handler = Handler {name = name, hits = hits, misses = misses, reset = reset, content = content, mk_string = mk_string}
    val handler' = Handler {name = name, hits = hits, misses = misses, reset = reset, content = string, mk_string = I}
    val _ = add_handler name handler'
  in (apply, handler) end;

fun create_gc name mk_string empty lookup update f = fst (create_gc_handler name mk_string empty lookup update f)

fun get_handler name =
  Symtab.lookup (Synchronized.value caches) name

fun delete_handler name = Synchronized.change caches (Symtab.delete name) 

fun all_handlers () =
  Symtab.dest (Synchronized.value caches)

fun cache_statistics () =  all_handlers () |> 
   map (fn (_, Handler h) => 
     (#name h, {hits = #hits h (), misses = #misses h (), content_size = ML_Heap.obj_size (#content h ())}))

fun reset_cache name =
  case get_handler name of
    SOME (Handler h) => #reset h ()
  | NONE => warning ("reset_handler: no handler with name " ^ name)

fun reset_all_caches () =
  all_handlers () |> map (apsnd (fn Handler h => #reset h ())) |> K ()

fun get_info (Handler handler:'content handler) = 
  {name = #name handler, hits = (#hits handler) (), misses = (#misses handler) (), content = (#content handler) (), mk_string = #mk_string handler}

fun pretty_elem name value = Pretty.block (Pretty.breaks [Pretty.str name, Pretty.str "=", Pretty.str value])
fun pretty_info {name, content, hits, misses, mk_string, ...} =
  Pretty.list "{" "}" ( 
   [pretty_elem "name" (More_Binding.here name), 
    pretty_elem "hits" (string_of_int hits), 
    pretty_elem "misses" (string_of_int misses), 
    pretty_elem "content" (mk_string content)])

fun pretty_handler x = (pretty_info o get_info) x
fun string_of_info x = (Pretty.string_of o pretty_info) x
fun string_of_handler x = (string_of_info o get_info) x

val _ =
  ML_system_pp (fn depth => fn pretty => fn handler =>
    Pretty.to_ML (pretty_handler handler));

end;
\<close>

subsection \<open>Example\<close>

text \<open>Cache without garbage collection\<close>
ML_val \<open>
fun fib n =
  if n < 3 then 1
  else fib (n-1) + fib (n-2)

val (fib, handler) = Fun_Cache.create_handler 
  @{binding "fib"} 
  (fn n => @{make_string} n) (* as the type of n is fixed @{make_string} will pick a proper print function *) 
  Inttab.empty
  Inttab.lookup
  Inttab.update
  fib

val _ = tracing ("trace 1: " ^ Fun_Cache.string_of_handler handler)
val tests1 = map fib (1 upto 6)
val _ = (tracing "enforcing garbage collection"; ML_Heap.full_gc()); (* does not affect cache *)
val _ = tracing ("trace 2: " ^ Fun_Cache.string_of_handler handler)
val tests2 = map fib (1 upto 6)
val _ = tracing ("trace 3: " ^ Fun_Cache.string_of_handler handler)
\<close>

text \<open>Cache with garbage collection\<close>

ML_val \<open>
fun fib n =
  if n < 3 then 1
  else fib (n-1) + fib (n-2)

val (fib, handler) = Fun_Cache.create_gc_handler 
  @{binding "fib"} 
  (fn n => @{make_string} n) (* as the type of n is fixed @{make_string} will pick a proper print function *) 
  Inttab.empty
  Inttab.lookup
  Inttab.update
  fib

val _ = tracing ("trace 1: " ^ Fun_Cache.string_of_handler handler)
val tests1 = map fib (1 upto 6)
val _ = tracing ("trace 2: " ^ Fun_Cache.string_of_handler handler)
val _ = (tracing "enforcing garbage collection"; ML_Heap.full_gc()); (* should empty cache *)
val _ = tracing ("trace 3: " ^ Fun_Cache.string_of_handler handler)
val tests2 = map fib (1 upto 6)
val _ = tracing ("trace 4: " ^ Fun_Cache.string_of_handler handler)
val tests3 = map fib (1 upto 6)
val _ = tracing ("trace 5: " ^ Fun_Cache.string_of_handler handler)
\<close>

end