\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generic Zippers Setup\<close>
theory ML_Gen_Zippers_Setup
  imports
    ML_Gen_Zippers_Base
    ML_Lenses
begin

declare [[ParaT_args sep: ", " encl: "" ", " encl_arg: "" "" stop: ]]
declare [[ParaT_args sep: ", " encl: "" ", " encl_arg: "" "" stop: ]]
and [[ZipperT_args sep: ", " encl: "" "" encl_arg: "" "" stop: ]]
and [[AllT_args sep: ", " encl: "(" ")" encl_arg: "" "" stop: ]]
and [[imap start: 1]]
(*setup for 5-alternating zippers*)
setup\<open>Context.theory_map (ML_Gen.setup_zipper_args' (NONE, NONE) (SOME 5, NONE))\<close>

ML\<open>
  val sfx_ParaT_nargs = ML_Gen.sfx_ParaT_nargs
  val sfx_T_nargs = ML_Gen.sfx_T_nargs
  val sfx_inst_T_nargs = ML_Gen.sfx_inst_T_nargs
\<close>

end
