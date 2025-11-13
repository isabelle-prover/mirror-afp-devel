\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generic Zippers Base Setup\<close>
theory ML_Gen_Zippers_Base
  imports
    Zippy_Base_Setup
    ML_IMap_Antiquotation
    Gen_ML_Typeclasses_Base
begin

text\<open>The ML code is parametrised by the number of zippers \<open>nzippers\<close>, the number of type parameters
of the underlying typeclasses \<open>'p1,...,'pn\<close>, and the number of additional type parameters for the
zipper \<open>'a1,...,'am\<close>. All parameters of the underlying typeclasses are also put into the zipper
type per default since zippers for search trees must be able to store moves in the zipper
themselves, i.e. a zipper takes type parameters \<open>'p1,...,'pn,'a1,...,'am\<close>.

Note: due to a performance problem in Poly/ML's type checker, instantiation functors need to be
carefully used (i.e. avoid deep type instantiation chains):
\<^url>\<open>https://github.com/polyml/polyml/issues/213\<close>\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: Zipper_Type_Args_Antiquotations
  functor_name: Args_Antiquotations
  id: \<open>"ZipperT"\<close>
  more_args: \<open>val init_args = {
    args = SOME ["'a1"],
    sep = SOME ", ",
    encl = SOME ("", ""),
    encl_arg = SOME ("", ""),
    start = SOME 0,
    stop = SOME NONE}\<close>\<close>
\<close>
local_setup \<open>Zipper_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set zipper type args antiquotation arguments")\<close>
setup \<open>Zipper_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>Zipper_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: All_Type_Args_Antiquotations
  functor_name: Args_Antiquotations
  id: \<open>"AllT"\<close>
  more_args: \<open>val init_args = {
    args = SOME ["'p1", "'a1"],
    sep = SOME ", ",
    encl = SOME ("(", ")"),
    encl_arg = SOME ("", ""),
    start = SOME 0,
    stop = SOME NONE}\<close>\<close>
\<close>
local_setup \<open>All_Type_Args_Antiquotations.setup_args_attribute
  (SOME "set all type args antiquotation arguments")\<close>
setup \<open>All_Type_Args_Antiquotations.setup_args_antiquotation\<close>
setup \<open>All_Type_Args_Antiquotations.setup_arg_antiquotation\<close>

(*functions to create type generic ML code*)
ML\<open>
structure ML_Gen =
struct
  open ML_Gen
  structure AllT = All_Type_Args_Antiquotations
  structure ZipperT = Zipper_Type_Args_Antiquotations
  fun nzippers () = ZipperT.nargs (Context.the_generic_context ())
  val nzippers' = nzippers #> string_of_int

  fun setup_zipper_args paraT_args zipperT_args =
    ParaT.map_args (K paraT_args)
    #> ZipperT.map_args (K zipperT_args)
    #> AllT.map_args (K (paraT_args @ zipperT_args))
    #> Standard_IMap_Antiquotation.map_stop (K (length zipperT_args))
  fun setup_zipper_args' (opt_ParaT_nargs, opt_ParaT_arg) (opt_nzippers, opt_zipperT_arg) context =
    let
      val ParaT_nargs = \<^if_none>\<open>ParaT.nargs context\<close> opt_ParaT_nargs
      val ParaT_arg = \<^if_none>\<open>string_of_int #> prefix "'p"\<close> opt_ParaT_arg
      val ParaT_args = map_range ParaT_arg ParaT_nargs
      val nzippers = \<^if_none>\<open>nzippers ()\<close> opt_nzippers
      val zipperT_arg = \<^if_none>\<open>string_of_int #> prefix "'a"\<close> opt_zipperT_arg
      val zipperT_args = map_range zipperT_arg nzippers
    in setup_zipper_args ParaT_args zipperT_args context end

  (*ML structure names may not begin with a digit; hence we add a "n" prefix for indexed names*)
  val nprefix = prefix "n"
  fun pfx_nzippers s = mk_name [nprefix (nzippers' ()), s]

  (*modular arithmetic for domain [1,...,nzippers]*)
  fun add_mod_nzippers i j = ((i + j - 1) mod nzippers ()) + 1
  fun add_mod_nzippers' i = add_mod_nzippers i #> string_of_int
  fun sub_mod_nzippers i j = ((i - j - 1) mod nzippers ()) + 1
  fun sub_mod_nzippers' i = sub_mod_nzippers i #> string_of_int
  val succ_mod_nzippers = add_mod_nzippers 1
  val succ_mod_nzippers' = add_mod_nzippers' 1
  fun pred_mod_nzippers i = sub_mod_nzippers i 1
  fun pred_mod_nzippers' i = sub_mod_nzippers' i 1

  fun sfx_T_nargs s = mk_name [s, ParaT_nargs' (), nzippers' ()]

  val pfx_sfx_nargs = pfx_nzippers #> sfx_T_nargs

  (*instantiate a zipper type*)
  fun sfx_inst s i = mk_name [s, string_of_int i]

  fun sfx_inst_T_nargs s = sfx_inst s #> sfx_T_nargs
  val pfx_sfx_inst_nargs = pfx_nzippers #> sfx_inst_T_nargs

  fun inst_zipperT instT i =
    let val ctxt = Context.the_local_context ()
    in
      nzippers ()
      |> map_range (fn j => if i = j + 1 then instT else ZipperT.mk_arg_code j ctxt)
      |> commas
    end
end
\<close>

end
