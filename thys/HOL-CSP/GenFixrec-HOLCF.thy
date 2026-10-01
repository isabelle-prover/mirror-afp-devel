(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_Metric_Space - Seeing Processes as a Metric Space
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Example Instance of the Generic Fixrec Package with CPO's
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter \<open>An Example Instance of the Generic Fixrec-package: The HOLCF Language\<close>

theory  "GenFixrec-HOLCF"
  imports GenFixrec 
          "HOL-CSP" "HOLCF-Library.Int_Discrete"
          
begin

default_sort type  \<comment> \<open>no cpo default sorts are imposed on users of the instance\<close>


section\<open>Setup of the Language Instance\<close>

ML\<open>

structure HOLCF_instance =
struct

local open GenFixrec in
  

fun mk_cfun t1 t2 = Type(\<^type_name>\<open>Cfun.cfun\<close>,[t1,t2])
fun dest_cfun (Type(\<^type_name>\<open>Cfun.cfun\<close>,[t1,t2])) = (t1,t2)
   |dest_cfun _ = error"dest_cfun : illegal arg."


fun mk_cpo_fix [] E = 
        let val a_ty = (fst o dest_funT o fastype_of) E
            val a_a_ty = (mk_cfun a_ty a_ty)
            val F = Const (\<^const_name>\<open>cfun.Rep_cfun\<close>, (mk_cfun a_a_ty a_ty)-->(a_a_ty)-->a_ty) 
                      $ Const (\<^const_name>\<open>Fixrec.fix\<close>, mk_cfun a_a_ty a_ty) 
                      $ (Const (\<^const_name>\<open>cfun.Abs_cfun\<close>, (a_ty --> a_ty) -->  a_a_ty ) 
                         $ Abs ("X", a_ty, E $ Bound 0))
        in F end

(* returns the functional F of  fix\<cdot>(\<Lambda> X. F X); accepts also the \<beta>-normal 
   form  fix\<cdot>(\<Lambda> X. body)  (then F = \<lambda>X. body) as stored by definitions *)
fun dest_cpo_fix (Const (\<^const_name>\<open>cfun.Rep_cfun\<close>,_)
                  $ Const (\<^const_name>\<open>Fixrec.fix\<close>, _) 
                  $ (Const (\<^const_name>\<open>cfun.Abs_cfun\<close>, _) $ F)) = 
        (case F of Abs (_, _, E $ Bound 0) => if loose_bvar1 (E, 0) then F 
                                              else incr_boundvars ~1 E
                 | _ => F)
  | dest_cpo_fix t = raise TERM ("dest_cpo_fix : illegal pattern", [t])


fun set_context_fix ctxt = ctxt |> fold Splitter.add_split @{thms  prod.split}
                                |> fold Simplifier.add_simp [@{thm cont_fun},
                                                           @{thm prod_cont_iff}]

val aux = (Goal.prove_global @{theory} [] [] 
                         (@{prop \<open>s \<equiv> s' \<Longrightarrow> s' = t \<Longrightarrow> s = t\<close>}) 
                         (fn {context,...} =>auto_tac context))
val aux2 = (Goal.prove_global @{theory} [] [] 
                         (@{prop \<open>s = s' \<Longrightarrow> P s' = t \<Longrightarrow> P s = t\<close>}) 
                         (fn {context,...} =>auto_tac context))
val aux2' = meta_eq_to_obj_eq RS aux2

val add_prod_splits = fold Splitter.add_split @{thms prod.split};
fun metis_step ctxt defs = Metis_Tactic.metis_tac  
                                  [] "opaque_lifting" 
                                  ctxt (@{thms "prod.sel"} @ defs)


(* orig *)
fun prove_projection  defs unfold ctxt def = 
       EVERY [resolve0_tac [def RS aux] 1,
              resolve0_tac [unfold RS aux2] 1,
              auto_tac (add_prod_splits ctxt), 
              metis_step ctxt defs 1]

(* structural projection proof (core), heuristic proof as fallback (e.g. for \<Lambda>-redexes) *)
fun prove_projection  defs unfold ctxt def = 
       structural_projection_tac defs unfold ctxt def
       ORELSE
       EVERY [resolve0_tac [def RS aux2'] 1,
              resolve0_tac [unfold RS aux2] 1,
              auto_tac (add_prod_splits ctxt), 
              TRY (metis_step ctxt defs 1)]  (* auto may already solve the goal *)


val def_cont_fix_eq = @{thm "def_cont_fix_eq"}
val def_cont_fix_ind = @{thm def_cont_fix_ind}

fun add_case_prod_beta ctxt = Simplifier.add_simp @{thm case_prod_beta} ctxt (* case_prod_beta*)
fun add_cont_rwrts ctxt = ctxt |> Simplifier.add_simp @{thm prod_cont_iff} 
                               |> Simplifier.add_simp @{thm cont_fun}

local open HOLogic in

fun substitute_curried_pred ctxt vartab thm =
    let val frees = map (fn((s,t,_),_) => Free(Binding.name_of s,t)) vartab;
        val Var ((P, idx), ty') $ S = dest_Trueprop(Thm.concl_of thm);
        val prodT'= strip_tupleT (domain_type ty')
        val frees'= map (fn (Free(s,_),t) => Free(s,t)) (frees ~~ prodT') 
      
        val P' = list_comb (Var((P^"'",idx),prodT' ---> boolT), frees')
        val proJT' =  tupled_lambda (mk_tuple frees') P'
        val subst = Vars.make1(((P,idx),ty'), Thm.cterm_of ctxt proJT');
    in  thm |> Thm.instantiate(TVars.empty,subst) end

end

(* \<Lambda> x. E  resp.  \<Lambda>(x\<^sub>1,...,x\<^sub>n). E *)
fun cfun_lambda pat E = 
        let val T  = fastype_of pat
            val ET = fastype_of E
        in  Const (\<^const_name>\<open>cfun.Abs_cfun\<close>, (T --> ET) --> mk_cfun T ET) 
            $ HOLogic.tupled_lambda pat E 
        end

val holcf = {mk_fix = mk_cpo_fix,
             lambda'  = cfun_lambda,
             dest_fix = dest_cpo_fix,
             apply    = @{term \<open>Cfun.cfun.Rep_cfun\<close>}, (* inner application: c\<cdot>x *)
             shift_tac = fn {context,...} => EVERY[REPEAT(resolve0_tac [@{thm refl}] 1), 
                                                   DEPTH_SOLVE_1(auto_tac context)],
                         (* not yet implemented. shift_tac is place_holder code. *)
             fix_tac  = (fn {context,prems} => EVERY[resolve0_tac [hd prems RS def_cont_fix_eq] 1,
                                                     auto_tac (set_context_fix context)]),
             proj_tac = (fn {proj_def, projs, unfold} =>
                            fn {context,prems} => prove_projection projs unfold context proj_def),
             fixind_tac = (fn {eqns,varstab,projs,rec_def,unfold} =>
                            fn {context,prems} => ((rec_def RS def_cont_fix_ind)
                                                   |> substitute_curried_pred context varstab
                                                   |> Simplifier.asm_full_simplify (add_case_prod_beta context)
                                                   |> Simplifier.asm_full_simplify (add_cont_rwrts context)
                                                   |> Local_Defs.fold context projs
                                                   ))  
            } : language;

fun define_scott_space thy =  Context.Theory thy 
                               |> update_language (Binding.make("HOLCF",@{here})) holcf
                               |> Context.the_theory;
end
end (* struct *)
\<close>



setup \<open>HOLCF_instance.define_scott_space\<close>


end


