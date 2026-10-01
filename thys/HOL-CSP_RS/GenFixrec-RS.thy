(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_Metric_Space - Seeing Processes as a Metric Space
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       :Instantiation of the Generic Fixpoint Package with Restriction Spaces
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



chapter \<open>Instantiation of the Generic Fixrec Package for Restriction-Spaces\<close>

theory  "GenFixrec-RS"
  imports "HOL-CSP.GenFixrec"
          "HOL-CSP_RS"

begin

default_sort type  \<comment> \<open>no cpo default sorts are imposed on users of the instance\<close>


subsection\<open>Example setup\<close>


lemma def_constructive_fix_eq :
   \<open>f \<equiv> (\<upsilon> x. F x) \<Longrightarrow> constructive F \<Longrightarrow> f = F f\<close>
   by(simp, rule restriction_fix_eq,simp)

text \<open>Case distinctions on conditions not depending on the recursion variable (the rules of
\<^session>\<open>Restriction_Spaces\<close> state the condition as \<open>P x\<close>, which the simplifier cannot match):\<close>

lemma non_destructive_if [simp] :
  \<open>(b \<Longrightarrow> non_destructive f) 
   \<Longrightarrow> (\<not> b \<Longrightarrow> non_destructive g)
   \<Longrightarrow> non_destructive (\<lambda>x. if b then f x else g x)\<close>
  by (cases b) simp_all

lemma constructive_if [simp] :
  \<open>(b \<Longrightarrow> constructive f) 
   \<Longrightarrow> (\<not> b \<Longrightarrow> constructive g) 
   \<Longrightarrow> constructive (\<lambda>x. if b then f x else g x)\<close>
  by (cases b) simp_all


text \<open>The rules on the constructiveness of \<^const>\<open>Throw\<close>, in particular in its continuation
(@{thm [source] ThrowR_constructive}, @{thm [source] Throw_constructive_continuation}), are in
@{theory "HOL-CSP_RS.Throw_Non_Destructive"}; the constructiveness proofs of the RS instance use:\<close>

declare Throw_constructive_continuation [simp]


lemma def_restriction_fix_ind :
  "\<lbrakk>f \<equiv> \<upsilon> x. F x; constructive F; adm\<^sub>\<down> P; P x; \<And>x. P x \<Longrightarrow> P (F x)\<rbrakk> \<Longrightarrow> P f"
by (simp add: restriction_fix_ind)

ML\<open>
structure RS_instance =
struct

local open GenFixrec in

val E = @{term "restriction_fix"};
val a_ty = (snd o dest_funT o fastype_of) E;
fun mk_rs_fix [] E = let val a_ty = (fst o dest_funT o fastype_of) E
                   in Const (\<^const_name>\<open>complete_restriction_space_class.restriction_fix\<close>, 
                              (a_ty --> a_ty) --> a_ty) 
                      $ E
                   end

fun dest_rs_fix (Const (\<^const_name>\<open>complete_restriction_space_class.restriction_fix\<close>, t) $ E) = E

(* constructiveness proofs: the shift rules of HOL-CSP_RS are simp rules; case_prod_beta turns
   continuations with tuple patterns (e.g. of read prefixes) into terms they apply to *)
fun set_context_fix ctxt = ctxt |> fold Splitter.add_split @{thms  prod.split}
                                |> fold Simplifier.add_simp [@{thm case_prod_beta}]

val def_rs_fix_eq = @{thm "def_constructive_fix_eq"}

val aux = (Goal.prove_global @{theory} [] [] 
                         (@{prop \<open>s \<equiv> s' \<Longrightarrow> s' = t \<Longrightarrow> s = t\<close>}) 
                         (fn {context,...} =>auto_tac context))

val aux2 = (Goal.prove_global @{theory} [] []
                         (@{prop \<open>s = s' \<Longrightarrow> P s' = t \<Longrightarrow> P s = t\<close>}) 
                         (fn {context,...} =>auto_tac context))

val fst_conv = @{thm "fst_conv"}
val snd_conv = @{thm "snd_conv"}

val add_prod_splits = fold Splitter.add_split @{thms prod.split};
fun metis_step ctxt defs = Metis_Tactic.metis_tac [] "combs" 
                                                  ctxt  (fst_conv :: snd_conv :: defs)


val aux2' = meta_eq_to_obj_eq RS aux2

(* structural projection proof (core), heuristic proof as fallback;
   aux2' (instead of aux) also covers shifted equations  c x\<^sub>1 ... x\<^sub>n = E *)
fun prove_projection  defs unfold ctxt def =  
       structural_projection_tac defs unfold ctxt def
       ORELSE
       EVERY [resolve0_tac [def RS aux2'] 1,
              resolve0_tac [unfold RS aux2] 1,
              auto_tac (add_prod_splits ctxt), 
              TRY (metis_step ctxt defs 1)]  (* auto may already solve the goal *) 

local open HOLogic in

fun substitute_curried_pred ctxt vartab thm =
    let val frees = map (fn((s,t,_),_) => Free(Binding.name_of s,t)) vartab;
        val vars_proj = map (fn((s,t,_),_) => Var((Binding.name_of s,0),t)) vartab;
        val Var ((P, idx), ty') $ S = dest_Trueprop(Thm.concl_of thm);
        val prodT'= strip_tupleT (domain_type ty')
        val frees'= map (fn (Free(s,_),t) => Free(s,t)) (frees ~~ prodT') 
        val frees'' = map (fn (Free(s,_),t) => Var((s^"0",0),t)) (frees ~~ prodT') 
        val tuple_witness = HOLogic.mk_tuple frees''
      
        val P' = list_comb (Var((P^"'",idx),prodT' ---> boolT), frees')
        val proJT' =  tupled_lambda (mk_tuple frees') P'
        val subst = Vars.make2(((P,idx),ty'), Thm.cterm_of ctxt proJT')
                              ((("x",0),domain_type ty'), Thm.cterm_of ctxt tuple_witness); 
    in  thm |> Thm.instantiate(TVars.empty,subst) end

end

val def_restriction_fix_ind = @{thm def_restriction_fix_ind}

fun add_case_prod_beta ctxt = Simplifier.add_simp @{thm case_prod_beta} ctxt (* case_prod_beta*)

val rs =    {mk_fix    = mk_rs_fix,
             dest_fix  = dest_rs_fix,
             lambda'   = HOLogic.tupled_lambda, (* no inner application; never used *)
             apply     = Bound 0, (* dummy *)
             shift_tac = (fn {context,...} => all_tac), (* dummy *)
             fix_tac   = (fn {context,prems} => 
                               resolve0_tac [hd prems RS def_rs_fix_eq] 1
                               THEN (SOLVED' (asm_full_simp_tac (set_context_fix context)) 1
                                     ORELSE auto_tac (set_context_fix context))),
             proj_tac  = (fn {proj_def, projs, unfold} =>
                             fn {context,prems} => prove_projection projs unfold context proj_def),
             fixind_tac = (fn {eqns, varstab, projs, rec_def, unfold} =>
                               fn {context,prems} => ((rec_def RS def_restriction_fix_ind)
                                                      |> substitute_curried_pred context varstab
                                                      |> Simplifier.asm_full_simplify 
                                                                    (add_case_prod_beta context)
                                                      |> Local_Defs.fold context projs 
                                                      |> Simplifier.asm_full_simplify context
                                                      )) 
            } : language;

fun define_rs_space thy =  Context.Theory thy 
                               |> update_language (Binding.make("RS",@{here})) rs
                               |> Context.the_theory;
end (* local *)
end (* struct *)
\<close>

setup \<open>RS_instance.define_rs_space\<close>


end


