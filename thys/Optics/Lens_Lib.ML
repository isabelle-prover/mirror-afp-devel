signature LENS_LIB =
sig
  (* Lens Constant Names *)
  val bij_lensN: string
  val vwb_lensN: string
  val sym_lensN: string
  val lens_indepN: string
  val lens_plusN: string
  val lens_quotientN: string
  val lens_compN: string
  val id_lensN: string
  val sublensN: string
  val lens_equivN: string

  val lens_defsN: string
  val indepsN: string
  val sublensesN: string
  val quotientsN: string
  val compositionsN: string
  val lens_suffix: string

  (* Lens terms *)

  val lensT: typ -> typ -> typ              (* Lens type *)
  val isLensT: typ -> bool                
  val astateT: typ                          (* Abstract state type *)
  val pairsWith: 'a list -> 'a list -> ('a * 'a) list
  val pairings: 'a list -> ('a * 'a) list   (* Calculate all pairings *)
  val mk_vwb_lens: term -> term             (* Make a very well-behaved lens term *)
  val mk_indep: term -> term -> term        (* Make an independence term *)
  val remove_lens_suffix: string -> string  (* Remove the suffix subscript v from a name *)
end

structure Lens_Lib : LENS_LIB =
struct

val bij_lensN = @{const_name bij_lens}
val vwb_lensN = @{const_name vwb_lens}
val sym_lensN = @{const_name sym_lens}
val lens_indepN = @{const_name lens_indep}
val lens_plusN = @{const_name lens_plus}
val lens_quotientN = @{const_name lens_quotient}
val lens_compN = @{const_name lens_comp}
val id_lensN = @{const_name id_lens}
val sublensN = @{const_name sublens}
val lens_equivN = @{const_name lens_equiv}

val lens_defsN = "lens_defs"
val indepsN = "indeps"
val sublensesN = "sublenses"
val quotientsN = "quotients"
val compositionsN = "compositions"

val lens_suffix = "\<^sub>v"

fun lensT a b = Type (@{type_name lens_ext}, [a, b, HOLogic.unitT])

fun isLensT (Type (n, _)) = (n = @{type_name lens_ext}) |
    isLensT _ = false

val astateT = (TFree ("'st", [@{class type}, @{class scene_space}]))

fun pairWith _ [] = []
  | pairWith x (y :: ys) = [(x, y), (y, x)] @ pairWith x ys;

fun pairsWith [] _ = []
  | pairsWith (x :: xs) ys = pairWith x ys @ pairsWith xs ys;

fun pairings [] = []
  | pairings (x :: xs) = pairWith x xs @ pairings xs;  

fun mk_vwb_lens t = HOLogic.mk_Trueprop (Syntax.const vwb_lensN $ t)

fun mk_indep x y = HOLogic.mk_Trueprop (Syntax.const lens_indepN $ x $ y)

fun remove_lens_suffix x = (if (String.isSuffix lens_suffix x) 
                   then String.substring (x, 0, (String.size x - String.size lens_suffix)) 
                   else x);

end
