signature POSITIONAL_SYMBOL_TABLE =
sig
  type key
  type qualifier = string list
  type 'a symbol_table

  structure Keytab: TABLE
  exception DUP of (qualifier * key)
  exception SAME

  val empty: 'a symbol_table
  val is_empty: 'a symbol_table -> bool

  val dest: 'a symbol_table -> ((qualifier * key) * (int * 'a)) list
  val dest_scope: qualifier -> 'a symbol_table -> (key * (int * 'a)) list
  val dest_scope_positional: qualifier -> 'a symbol_table -> (int * (key * 'a)) list

  val lookup: 'a symbol_table -> qualifier -> key -> (int * 'a) option
  val lookup_positional: 'a symbol_table -> qualifier -> int -> (key * 'a) option

  val defined_scope: 'a symbol_table -> qualifier -> bool
  val get_scope: 'a symbol_table -> qualifier -> (int * 'a) Keytab.table
  val match: 'a symbol_table -> qualifier -> (key -> bool) -> (key * (int * 'a)) list

  val fold: (qualifier -> key -> int -> 'a -> 'b -> 'b) -> 'a symbol_table -> 'b -> 'b
  val fold_rev: (qualifier -> key -> int -> 'a -> 'b -> 'b) -> 'a symbol_table -> 'b -> 'b

  val update: qualifier -> key * 'a -> 'a symbol_table -> 'a symbol_table
  val update_new: qualifier -> key * 'a -> 'a symbol_table -> 'a symbol_table (*exception DUP*)
  val default: qualifier -> key * 'a -> 'a symbol_table -> 'a symbol_table
  val map_entry: qualifier -> key -> ('a -> 'a) (*exception SAME*) -> 'a symbol_table -> 'a symbol_table
  val map_default: qualifier -> key * 'a -> ('a -> 'a) -> 'a symbol_table -> 'a symbol_table

  val make: ((qualifier * key) * 'a) list -> 'a symbol_table (*exception DUP*)
  val add: ((qualifier * key) * 'a) list -> 'a symbol_table -> 'a symbol_table (*exception DUP*)
  val make_scope: qualifier -> (key * 'a) list -> 'a symbol_table (*exception DUP*)
  val add_scope: qualifier -> (key * 'a) list -> 'a symbol_table -> 'a symbol_table (*exception DUP*)

  val join: (qualifier -> key -> int -> 'a * 'a -> 'a) (*exception SAME*) ->
    'a symbol_table * 'a symbol_table -> 'a symbol_table (*exception DUP*)
  val merge: ('a * 'a -> bool) -> 'a symbol_table * 'a symbol_table -> 'a symbol_table  (*exception DUP*)

end

functor Positional_Symbol_Table(Key: KEY) : POSITIONAL_SYMBOL_TABLE =
struct

type qualifier = string list;
type key = Key.key;
structure Keytab = Table(Key);
type 'a keytab = 'a Keytab.table;

structure Scopetab = Table(type key = qualifier val ord = list_ord fast_string_ord);

datatype 'a scope = Scope of {entries: (int * 'a) Keytab.table, position: key Inttab.table, size: int}
fun rep_scope (Scope x) = x

type 'a symbol_table = 'a scope Scopetab.table;

exception DUP of (qualifier * key)
exception SAME

val empty = Scopetab.empty
val empty_scope = Scope {entries = Keytab.empty, position = Inttab.empty, size = 0}

val is_empty = Scopetab.is_empty;

fun lookup tab qualifier key = 
  Scopetab.lookup tab qualifier 
  |> Option.mapPartial (fn Scope {entries, ...} => 
       Keytab.lookup entries key)

fun defined_scope tab qualifier =
  Scopetab.defined tab qualifier

fun get_scope tab qualifier  = 
  case Scopetab.lookup tab qualifier of 
   SOME (Scope {entries, ...}) => entries
  | NONE => Keytab.empty

fun match tab qualifier P =
  Scopetab.lookup tab qualifier 
  |> Option.map (fn Scope {entries, ...} => 
       Keytab.dest entries |> filter (P o fst))
  |> these

fun lookup_positional tab qualifier pos = 
  Scopetab.lookup tab qualifier 
  |> Option.mapPartial (fn Scope {entries, position, ...} => 
       Inttab.lookup position pos 
  |> Option.mapPartial (fn key => Keytab.lookup entries key 
  |> Option.map (apfst (K key))))

fun modify_scope key f (Scope {entries, position, size}) =
   (case Keytab.lookup entries key of
           SOME (i, x) => Scope {entries = Keytab.update (key, (i, f (SOME x))) entries, 
                            position = position, size = size}
         | NONE => Scope {entries = Keytab.update (key, (size, f NONE)) entries, 
                     position = Inttab.update (size, key) position, size = size + 1}) 
 
fun modify qualifier key f tab =
  (case Scopetab.lookup tab qualifier of
     SOME scope => Scopetab.update (qualifier, modify_scope key f scope) tab
   | NONE => Scopetab.update_new (qualifier, modify_scope key f empty_scope) tab)

fun update qualifier (key, x) tab = modify qualifier key (fn _ => x) tab;
fun update_new qualifier (key, x) tab = modify qualifier key (fn NONE => x | SOME _ => raise DUP (qualifier, key)) tab;
fun default qualifier (key, x) tab = modify qualifier key (fn NONE => x | SOME _ => raise SAME) tab;
fun map_entry qualifier key f = modify qualifier key (fn NONE => raise SAME | SOME x => f x);
fun map_default qualifier (key, x) f = modify qualifier key (fn NONE => f x | SOME y => f y);
(* f qualifier key pos value b = b *)

fun fold_scope f (Scope {entries, ...}) =
 let
   fun g (key, (pos, value)) = f key pos value 
 in Keytab.fold g entries end;

fun fold_rev_scope f (Scope {entries, ...}) =
 let
   fun g (key, (pos, value)) = f key pos value 
 in Keytab.fold_rev g entries end;

fun fold_table f =
 let
   fun g (qualifier, scope) x = fold_scope (f qualifier) scope x      
 in Scopetab.fold g end;

fun fold_rev_table f =
 let
   fun g (qualifier, scope) x = fold_rev_scope (f qualifier) scope x      
 in Scopetab.fold_rev g end;

local
  fun xcons qualifier key pos value xs = ((qualifier, key), (pos, value)) :: xs
in
fun dest tab = fold_rev_table xcons tab [];
end

fun dest_scope qualifier tab =
  Scopetab.lookup tab qualifier |> the_list |> map (Keytab.dest o #entries o rep_scope) |> flat

fun dest_scope_positional qualifier =     
  dest_scope qualifier  
  #> map (fn (key, (pos, value)) => (pos, (key, value)))
  #> sort (int_ord o apply2 fst)

fun build (f: 'a symbol_table -> 'a symbol_table) = f empty;

local
  fun upd_new ((qualifier, key), x) = update_new qualifier (key, x)
in
fun make entries = build (fold upd_new entries);
fun add entries = fold upd_new entries

fun make_scope qualifier entries = build (fold (update_new qualifier) entries)
fun add_scope qualifier entries = fold (update_new qualifier) entries
end


fun join f (table1, table2) =
  let
    fun add qualifier key pos y tab = modify qualifier key (fn NONE => y | SOME x => f qualifier key pos (x, y)) tab;
  in
    if pointer_eq (table1, table2) then table1
    else if is_empty table1 then table2
    else fold_table add table2 table1
  end;

fun merge eq  = 
  join (fn qualifier => fn key => fn pos => fn xy => 
    if eq xy then fst xy else raise DUP (qualifier, key))
  

val fold = fold_table;
val fold_rev = fold_rev_table;

end