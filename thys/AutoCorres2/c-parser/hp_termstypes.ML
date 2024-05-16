(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature HP_TERMS_TYPES =
sig

  val StrictC_errortype_ty : typ  (* errors are from failed guards *)
  val c_exntype_ty : typ   (* exns are flow-control interrupts:
                                return, break and continue *)
  val strip_c_exntype : typ -> typ

  val c_exit_status_info: (string * typ * 'c CType.ctype)
  val c_Nonlocal : term
  val c_the_Nonlocal : term
  val mk_com_ty : typ list -> typ (* list of three elements *)
  val dest_com_ty: typ -> (typ * typ * typ)
  val gammaN : string
  val mk_gamma_ty : typ list -> typ
  val mk_gamma : Proof.context -> string -> term

  val div_0_error : term
  val shift_error : term
  val safety_error : term
  val c_guard_error : term
  val arraybound_error : term
  val signed_overflow_error : term
  val dont_reach_error : term
  val side_effect_error : term
  val ownership_error : term
  val unspecified_syntax_error1 : term
  val unspecified_syntax_error2 : string -> term


  val Continue_exn : term
  val Return_exn : term
  val Break_exn : term

  val list_mk_seq : term list -> term
  val mk_fun_ptr : Proof.context -> string (* program *) -> string (* function *) -> term
  val mk_VCGfn_name : Proof.context -> string -> term
  val mk_basic_t : typ list -> term
  val mk_call_t : typ list -> term
  val mk_exit_t : typ list -> term
  val mk_catch_t : typ list -> term
  val mk_cbreak : theory -> typ list -> typ -> term
  val mk_cgoto : theory -> typ list -> typ -> string -> term
  val mk_goto : typ list -> string -> term
  val mk_ccatchbrk : theory -> typ list -> typ -> term
  val mk_ccatchgoto : theory -> typ list -> typ -> string -> term
  val mk_ccatchreturn : theory -> typ list -> typ -> term
  val mk_cond_t : typ list -> term
  val mk_creturn : theory -> typ list -> typ -> term -> term -> term
  val mk_creturn_void : theory -> typ list -> typ -> term
  val mk_dyncall_t : typ list -> term list -> term
  val mk_empty_INV : typ -> term
  val mk_guard : term -> term -> term -> term
  val mk_skip_t : typ list -> term
  val mk_Spec : typ list * term -> term
  val mk_specAnno : term -> term -> term -> term
  val mk_switch : term * term -> term
  val mk_throw_t : typ list -> term
  val mk_while_t : typ list -> term

  val current_C_filename : string Config.T
  val get_program_name : Proof.context -> string

  datatype state_kind = State | Globals
  val globals_stack_heap_state_params: state_kind -> Proof.context ->  {htd: term, htd_upd: term, hmem: term, hmem_upd: term, S:term, G:term}
  val globals_stack_heap_raw_state_params: state_kind -> Proof.context ->  {hrs: term, hrs_upd: term, S:term, G:term}
  val S: Proof.context -> term
  val G: Proof.context -> term
  val known_function: Proof.context -> term
end

structure HP_TermsTypes : HP_TERMS_TYPES =
struct

open IsabelleTermsTypes

val StrictC_errortype_ty = @{typ "CProof.strictc_errortype"}
val c_exntype_ty = @{typ "exit_status CProof.c_exntype"}
fun strip_c_exntype \<^Type>\<open>c_exntype T\<close> = T
  | strip_c_exntype T = T
val c_Nonlocal = @{const Nonlocal(exit_status)}
val c_the_Nonlocal = @{const the_Nonlocal(exit_status)}
val c_exit_status_info = (NameGeneration.global_exn_var_name, c_exntype_ty, CType.Signed CType.Int)

fun mk_com_ty args = Type("Language.com", args)
val dest_com_ty = \<^Type_fn>\<open>com s p f => \<open>(s, p, f)\<close>\<close>

val gammaN = "\<Gamma>"
fun mk_gamma_ty (args as [_, p, _]) = p --> IsabelleTermsTypes.mk_option_ty (mk_com_ty args)

fun mk_gamma ctxt prog_name =
  Proof_Context.read_const {proper=true, strict=false} ctxt 
      (Long_Name.qualify prog_name gammaN)
 

fun mk_skip_t tyargs = Const("Language.com.Skip", mk_com_ty tyargs)

val Return_exn = @{const "CProof.c_exntype.Return"(exit_status)}
val Break_exn = @{const "CProof.c_exntype.Break"(exit_status)}
val Continue_exn = @{const "CProof.c_exntype.Continue"(exit_status)}

val current_C_filename = Attrib.setup_config_string \<^binding>\<open>current_C_filename\<close> (K "")

fun get_program_name ctxt =
  Config.get ctxt current_C_filename
  |> Path.explode |> Path.base |> Path.split_ext |> fst |> Path.file_name

fun mk_fun_ptr ctxt prog_name fname =
  let
    val fname = NameGeneration.fun_ptr_name fname
  in
    Proof_Context.read_const {proper=true, strict=false} ctxt 
      (Long_Name.qualify prog_name fname)
  end

fun mk_VCGfn_name ctxt fname =
    mk_fun_ptr ctxt (get_program_name ctxt) fname

fun mk_basic_t tyargs = let
  val statety = hd tyargs
in
  Const(@{const_name "Language.com.Basic"},
        (statety --> statety) --> mk_com_ty tyargs)
end
fun mk_call_t tyargs = let
  val sarg = hd tyargs
  val parg = List.nth (tyargs, 1)
  val sarg2 = sarg --> sarg
  val sarg3 = sarg --> sarg2
  val com_ty = mk_com_ty tyargs
  val s2_to_com = sarg --> (sarg --> com_ty)
in
  Const(@{const_name "call_exn"},
        sarg2 --> (parg --> (sarg3 --> sarg3 --> (s2_to_com --> com_ty))))
end

fun mk_inter T t1 t2 =
 let 
   val setT = HOLogic.mk_setT T
   val Const (c, _) = @{term "(\<inter>)"}
 in
   Const (c, setT --> setT --> setT) $ t1 $ t2
 end

fun intersects T ts =
  let
    val Const (UNIV, _) = @{term UNIV}
  in 
    case ts of 
      [] => Const (UNIV, HOLogic.mk_setT T)
    | (t::ts') =>  t |> fold (mk_inter T) ts'
  end

fun mk_dyncall_t tyargs grds = let
  val [sarg, parg, farg] = tyargs
  val s2p_arg = sarg --> parg
  val sarg2 = sarg --> sarg
  val sarg3 = sarg --> sarg2
  val com_ty = mk_com_ty tyargs
  val s2_to_com = sarg --> (sarg --> com_ty)
  val guard_ty = HOLogic.mk_setT sarg
  val grd = intersects sarg grds
in
  Const(@{const_name "dynCall_exn"},
        farg --> guard_ty --> sarg2 --> (s2p_arg --> (sarg3 --> sarg3 --> (s2_to_com --> com_ty)))) $ 
    @{term UndefinedFunction} $ grd
end

fun mk_exit_t tyargs = let
  val sarg = hd tyargs
  val com_ty = mk_com_ty tyargs

in
  Const(@{const_name "CLanguage.cexit"}, (sarg --> sarg) --> com_ty)
end


fun mk_while_t tyargs = let
  val statety = hd tyargs
  val stateset_ty = mk_set_type statety
  val state_squared_set_ty = mk_set_type (mk_prod_ty (statety, statety))
  val com = mk_com_ty tyargs
in
  Const(@{const_name "Language.whileAnno"},
        stateset_ty --> stateset_ty --> state_squared_set_ty  --> com --> com)
end
fun mk_seq_t tyargs = let
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "Language.com.Seq"}, comty --> (comty --> comty))
end
fun mk_cond_t tyargs = let
  val statety = hd tyargs
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "Language.com.Cond"},
        mk_set_type statety --> (comty --> (comty --> comty)))
end

fun mk_seq s1 s2 = let
  val ty1 = type_of s1
            handle TYPE (msg, tys, tms) =>
                   raise TYPE ("mk_seq: "^msg, tys, tms)
  val tyargs = case ty1 of
                 Type(_, args) => args
               | _ => raise TYPE ("mk_seq: unexpected type for statement",
                                  [ty1], [s1])
in
  mk_seq_t tyargs $ s1 $ s2
end

fun list_mk_seq stmts =
    case stmts of
      [] => error "list_mk_seq: empty list as argument"
    | s::rest => s |> fold (fn s' => fn acc => mk_seq acc s') rest

fun mk_throw_t tyargs =
    Const(@{const_name "Language.com.Throw"}, mk_com_ty tyargs)
fun mk_catch_t tyargs = let
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "Language.com.Catch"}, comty --> (comty --> comty))
end

fun mk_switch (guard, cases) = let
  val cases_ty = type_of cases
  val cty = dest_list_type cases_ty
  val (_, sty) = dest_prod_ty cty
in
  Const(@{const_name "Language.switch"},
        type_of guard --> cases_ty --> sty) $ guard $ cases
end

fun mk_global_exn_var_update (thy : theory) (statety : Term.typ) : Term.term = let
    val exnvar_ty = (c_exntype_ty --> c_exntype_ty) --> statety --> statety
    val exnvar_name = suffix Record.updateN NameGeneration.global_exn_var
in
    Const (Sign.intern_const thy exnvar_name, exnvar_ty)
end

fun mk_creturn (thy : theory)
               (tyargs : Term.typ list)
               (statety : Term.typ)
               (updf : Term.term)
               (v : Term.term) : Term.term = let
    val exnvar = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.creturn"},
           (type_of exnvar) --> (type_of updf) --> (type_of v) --> mk_com_ty tyargs
          ) $ exnvar $ updf $ v
end

fun mk_creturn_void (thy : theory)
                    (tyargs : Term.typ list)
                    (statety : Term.typ) = let
    val exnvar      = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.creturn_void"},
           type_of exnvar --> mk_com_ty tyargs) $ exnvar
end

fun mk_cbreak_const (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.cbreak"}, (type_of exnvar) --> mk_com_ty tyargs)
end

fun mk_cbreak (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
in
    mk_cbreak_const thy tyargs statety $ exnvar
end

fun mk_global_exn_var (thy : theory) (statety : Term.typ) : Term.term = let
    val exnvar_ty = statety --> c_exntype_ty
    val exnvar_name = NameGeneration.global_exn_var
in
    Const (Sign.intern_const thy exnvar_name, exnvar_ty)
end

fun mk_ccatchbrk (thy : theory)
                 (tyargs : Term.typ list)
                 (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var thy statety
in
    Const (@{const_name "CLanguage.ccatchbrk"}, (type_of exnvar) --> mk_com_ty tyargs) $ exnvar
end

fun mk_ccatchgoto (thy : theory) (tyargs : Term.typ list) (statety : Term.typ) label = 
  let
    val exnvar  = mk_global_exn_var thy statety
    val label' = Utils.encode_isa_string label
  in
    Const (@{const_name "CLanguage.ccatchgoto"}, @{typ string} --> (type_of exnvar) --> mk_com_ty tyargs) $ label' $ exnvar
  end

fun mk_cgoto_const (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.cgoto"}, @{typ string} --> (type_of exnvar) --> mk_com_ty tyargs)
end

fun mk_cgoto (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) label = let
    val exnvar  = mk_global_exn_var_update thy statety
    val label' = Utils.encode_isa_string label
in
    mk_cgoto_const thy tyargs statety $ label' $ exnvar
end

fun mk_goto (tyargs : Term.typ list) label = 
  let

    val label' = Utils.encode_isa_string label
  in
    Const (@{const_name "c_exntype.Goto"}, @{typ string} --> c_exntype_ty) $ label' 
  end

fun mk_ccatchreturn (thy : theory)
                 (tyargs : Term.typ list)
                 (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var thy statety
in
    Const (@{const_name "CLanguage.ccatchreturn"}, (type_of exnvar) --> mk_com_ty tyargs) $ exnvar
end

val div_0_error      = @{const "Div_0"}
val c_guard_error    = @{const "C_Guard"}
val safety_error     = @{const "MemorySafety"}
val shift_error      = @{const "ShiftError"}
val side_effect_error= @{const "SideEffects"}
val arraybound_error = @{const "ArrayBounds"}
val signed_overflow_error = @{const "SignedArithmetic"}
val dont_reach_error = @{const "DontReach"}
val unspecified_syntax_error = @{const "UnspecifiedSyntax"}
val ownership_error = @{const "OwnershipError"}

val unspecified_syntax_error1 = @{const "UnspecifiedSyntax"}
fun unspecified_syntax_error2 s = @{const "unspecified_syntax_error"}
    $ mk_string s

fun mk_guard_t tyargs =
    Const(@{const_name "Language.com.Guard"},
          List.last tyargs --> mk_set_type (hd tyargs) -->
          mk_com_ty tyargs --> mk_com_ty tyargs)

fun mk_guard gdset gdtype com = let
  val tyargs =
      case type_of com of
        Type(@{type_name "Language.com"}, args) => args
      | _ => raise Fail "mk_guard: command not of type \"Language.com\""
in
  mk_guard_t tyargs $ gdtype $ gdset $ com
end

fun mk_Spec(styargs, reln) =
    Const(@{const_name "Language.Spec"}, type_of reln --> mk_com_ty styargs) $
    reln


fun mk_specAnno pre body post = let
  val pre_type = type_of pre
  val (bty, stateset_ty) = dom_rng pre_type
  val bvar = case pre of
               Abs(nm, _, _) => nm
             | _ => raise Fail "mk_specAnno: pre not an abstraction"
  val body_type = type_of body
  val specAnno_ty =
      pre_type --> body_type --> pre_type --> pre_type -->
      #2 (dom_rng body_type)
in
  Const(@{const_name "Language.specAnno"}, specAnno_ty) $ pre $ body $ post $
       Abs(bvar, bty, Const("{}", stateset_ty))
end

fun mk_empty_INV ty = mk_collect_t ty $ Abs("x", ty, mk_arbitrary bool)

datatype state_kind = State | Globals

fun the_const ctxt n =
  let
    val consts = Proof_Context.consts_of ctxt;
    val name = the (Consts.get_const_name consts (Consts.intern consts n))
  in (name, Consts.the_const_type consts name) end

fun globals_stack_heap_state_params kind ctxt =
  let
    val S = the_const ctxt NameGeneration.stack_addrs
    val G = the_const ctxt NameGeneration.global_addrs
    val t_hrs = the_const ctxt NameGeneration.global_heap_var
    val t_hrs_upd = the_const ctxt (suffix Record.updateN NameGeneration.global_heap_var)
    val (htd, htd_upd, hmem, hmem_upd) = case kind of
          State => 
           (\<^infer_instantiate>\<open>t_hrs = \<open>Const t_hrs\<close> in 
             term (schematic) "\<lambda>s. hrs_htd (t_hrs (globals s))" \<close> ctxt,
       
            \<^infer_instantiate>\<open>t_hrs_update = \<open>Const t_hrs_upd\<close> in 
             term (schematic) "\<lambda>upd. globals_update (t_hrs_update (hrs_htd_update upd))" \<close> ctxt , 
            \<^infer_instantiate>\<open>t_hrs = \<open>Const t_hrs\<close> in 
             term (schematic) "\<lambda>s. (hrs_mem (t_hrs (globals s)))" \<close> ctxt,
            \<^infer_instantiate>\<open>t_hrs_update = \<open>Const t_hrs_upd\<close> in 
             term (schematic) "\<lambda>upd. (globals_update (t_hrs_update (hrs_mem_update upd)))"\<close> ctxt)     
         | Globals =>
          (\<^infer_instantiate>\<open>t_hrs = \<open>Const t_hrs\<close> in 
             term (schematic) "\<lambda>s. hrs_htd (t_hrs s)" \<close> ctxt,
       
            \<^infer_instantiate>\<open>t_hrs_update = \<open>Const t_hrs_upd\<close> in 
             term (schematic) "\<lambda>upd. (t_hrs_update (hrs_htd_update upd))" \<close> ctxt , 
            \<^infer_instantiate>\<open>t_hrs = \<open>Const t_hrs\<close> in 
             term (schematic) "\<lambda>s. (hrs_mem (t_hrs s))" \<close> ctxt,
            \<^infer_instantiate>\<open>t_hrs_update = \<open>Const t_hrs_upd\<close> in 
             term (schematic) "\<lambda>upd. (t_hrs_update (hrs_mem_update upd))"\<close> ctxt)     
  in
    {htd = htd, htd_upd = htd_upd, hmem = hmem, hmem_upd = hmem_upd, S = Const S, G = Const G}
  end

fun globals_stack_heap_raw_state_params kind ctxt =
  let
    val S = the_const ctxt NameGeneration.stack_addrs
    val G = the_const ctxt NameGeneration.global_addrs
    val t_hrs = the_const ctxt NameGeneration.global_heap_var
    val t_hrs_upd = the_const ctxt   
          (suffix Record.updateN NameGeneration.global_heap_var)
    val (hrs, hrs_upd) = case kind of
          State => 
           (\<^infer_instantiate>\<open>t_hrs = \<open>Const t_hrs\<close> in 
             term (schematic) "\<lambda>s. t_hrs (globals s)" \<close> ctxt,
       
            \<^infer_instantiate>\<open>t_hrs_update = \<open>Const t_hrs_upd\<close> in 
             term (schematic) "\<lambda>upd. globals_update (t_hrs_update upd)" \<close> ctxt)     
         | Globals =>
          (\<^infer_instantiate>\<open>t_hrs = \<open>Const t_hrs\<close> in 
             term (schematic) "t_hrs" \<close> ctxt,
       
            \<^infer_instantiate>\<open>t_hrs_update = \<open>Const t_hrs_upd\<close> in 
             term (schematic) "t_hrs_update" \<close> ctxt)     
  in
    {hrs = hrs, hrs_upd = hrs_upd, S = Const S, G = Const G}
  end

fun S ctxt = #S (globals_stack_heap_state_params State ctxt)
fun G ctxt = #G (globals_stack_heap_state_params State ctxt)

fun known_function ctxt = Const (the_const ctxt NameGeneration.known_function)
end
