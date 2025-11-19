structure Location = struct
type hash = int
type key = (int Array.array * int Array.array)
type from = key
type to = Word8Vector.vector

fun hash (L, vars) =
    SimpleHash.int_arr' (L, 0w0)
    |> (curry SimpleHash.int_arr') vars
    |> Word.toIntX


fun cmp_callback (L, vars) (L', vars') f =
    case Array.collate int_ord (L, L') of
            EQUAL => Array.collate int_ord (vars, vars') |> f |
            x => f x

fun eq (L, L') = cmp_callback L L' (fn EQUAL => true
                                    | _ => false)
type from = key
type to = Word8Vector.vector
fun serialize_int_array arr acc =
    Array.foldr (fn (x, acc) => SerInt.serialize x :: acc) acc arr

fun serialize (l, r) =
    serialize_int_array r []
    |> serialize_int_array l
    |> Word8Vector.concat
end

signature NETWORK = sig
  type location
  type 'a state = location * 'a
  type info = {
    renaming : JsonP.json,
    processes : int,
    clocks : int,
    vars : int
  }
  type 'a system =
       {
             initial : 'a state,
             trans : 'a state -> 'a state list,
             invars_at: location -> ('a -> 'a),
             clock_dict: string IndexDict.t,
             var_dict: string IndexDict.t,
             label_dict: string IndexDict.t,
             var_bounds: (int * int) IndexDict.t,
             norm_k_G: int Array.array -> 'a -> 'a list,
             formula: (location -> bool) Formula.F,
             loc_dict: int IndexDict.t IndexDict.t,
             name_dict: string IndexDict.t IndexDict.t,
             ta_names : string IndexDict.t
       }
  val renaming_json: 'a system -> JsonP.json
  val discrete: 'a state -> location
  val zone: 'a state -> 'a
  val info: 'a system -> info
end

structure Network : NETWORK = struct
type location = Location.key
type 'a state = location * 'a

type 'a system =
     {
       initial : 'a state,
       trans : 'a state -> 'a state list,
       invars_at: location -> ('a -> 'a),
       clock_dict: string IndexDict.t,
       var_dict: string IndexDict.t,
       label_dict: string IndexDict.t,
       var_bounds: (int * int) IndexDict.t,
       norm_k_G: int Array.array -> 'a -> 'a list,
       formula: (location -> bool) Formula.F,
       loc_dict: int IndexDict.t IndexDict.t,
       name_dict: string IndexDict.t IndexDict.t,
       ta_names : string IndexDict.t
     }

type info = {
  renaming : JsonP.json,
  processes : int,
  clocks : int,
  vars : int
}

fun vars (net : 'a system) =
    net |> #var_dict |> IndexDict.size

fun clocks (net : 'a system) =
    net |> #clock_dict |> IndexDict.size

fun processes (net : 'a system) =
    net |> #ta_names |> IndexDict.size

val discrete = fst
val zone = snd

local open JsonP in
fun renaming_json ({clock_dict, var_dict, loc_dict, ta_names, ...}
                   : 'a system) =
    let
      fun dict_to_json ty =
          IndexDict.foldli
              (fn (new, k, tab) => Symtab.update (k, ty new) tab) Symtab.empty
          #> Object
      val dict_dict_to_json =
          IndexDict.foldli (fn (p, dict, tab) =>
                               Symtab.update
                                   (IndexDict.find p ta_names,
                                    dict_to_json VInt dict) tab)
      val processes = dict_dict_to_json Symtab.empty
                                        #> Object
      val loc_dict_str = IndexDict.map (IndexDict.map Int.toString) loc_dict
    in
        Symtab.empty
        |> Symtab.update ("clocks", dict_to_json VInt clock_dict)
        |> Symtab.update ("vars", dict_to_json VInt var_dict)
        |> Symtab.update ("processes", dict_to_json VInt ta_names)
        |> Symtab.update ("locations", processes loc_dict_str)
        |> Object
    end
end

fun info net =
    {
      renaming = renaming_json net,
      processes = processes net,
      clocks = clocks net,
      vars = vars net
    }
end
