(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Laws for architectural operators
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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


structure Cspm_API : sig
    (* misc *)                                                        
    val dest_listT: typ -> typ                              
    val dest_multisetT: typ -> typ                          
    val mk_multisetT: typ -> typ
    val mk_mset: term -> term                               
    val dest_mset: term -> term                             

    (* HOL-CSP process core *)                                                        
    val is_processpT: typ -> bool                             
    val mk_processT: typ -> typ                           \<comment> \<open> classic SKIP\<close>
    val mk_processpT: typ -> typ -> typ                   \<comment> \<open> param. SKIP\<close>
    val dest_processT: typ -> typ                        
    val dest_processpT: typ -> typ * typ                 
    val mk_evT : typ -> typ                      
    val mk_evT_ : typ -> typ -> typ
    val dest_evT : typ -> typ
    val dest_evT_ : typ -> typ * typ
    val mk_ev : term -> term                             
    val mk_ev_ : typ -> term -> term                        
    val dest_ev: term -> term                            
    val mk_tick : typ -> term                            
    val mk_tick_ : typ -> term -> term                           
    val dest_tick: term -> term                          
                                                         
    (* HOL-CSP consts *)                                                    
    val mk_BOT: typ -> term                               \<comment> \<open> classic BOT\<close>
    val mk_BOT_: typ -> typ -> term                       \<comment> \<open> param. BOT\<close>
    val mk_Skip: typ -> term                              \<comment> \<open> classic Skip\<close>
    val mk_SKIP: typ -> typ -> term                       \<comment> \<open> param. SKIP\<close>
    val mk_STOP: typ -> term                              \<comment> \<open> classic STOP\<close>
    val mk_STOP_: typ -> typ -> term                      \<comment> \<open> param. STOP\<close>
                                                         
    (* HOL-CSP ops *)                                                    
    val mk_write: term -> term -> term                    \<comment> \<open> \<^term>\<open>a \<rightarrow> P\<close>\<close> 
    val mk_write_: term -> term -> term                   \<comment> \<open> \<^term>\<open>a \<rightarrow> P\<close>, param. tick\<close>
    val mk_Det: term -> term -> term                      \<comment> \<open> \<^term>\<open>P \<box> Q\<close>\<close>
    val mk_NDet: term -> term -> term                     \<comment> \<open> \<^term>\<open>P \<sqinter> Q\<close>\<close>
    val mk_Sync: term -> term -> term -> term             \<comment> \<open> \<^term>\<open>P \<lbrakk>A\<rbrakk> Q\<close>\<close>
    val mk_Inter: term -> term -> term                    \<comment> \<open> \<^term>\<open>P ||| Q\<close>\<close>
    val mk_Par: term -> term -> term                      \<comment> \<open> \<^term>\<open>P || Q\<close>\<close>
    val mk_Seq: term -> term -> term                      \<comment> \<open> \<^term>\<open>P \<^bold>; Q\<close>\<close>
    val mk_Hiding: term -> term -> term                   \<comment> \<open> \<^term>\<open>P \ A\<close>\<close>
    val mk_Renaming: term -> term -> term                 \<comment> \<open> \<^term>\<open>Renaming P f\<close>\<close>
                                                         
                                                         
    (* HOL-CSPM communication ops *)                                                    
    val mk_prefix: term -> term -> term                   \<comment> \<open> \<^term>\<open>\<box>x\<in>A \<rightarrow> P x\<close>\<close>
    val mk_Mndetprefix: term -> term -> term              \<comment> \<open> \<^term>\<open>\<sqinter>x\<in>A \<rightarrow> P x\<close>\<close>
    val mk_prefix_read: term -> term -> term -> term      \<comment> \<open> \<^term>\<open>c\<^bold>?x\<in>A \<rightarrow> P x\<close>\<close>
    val mk_prefix_read_: term -> term -> term -> term     \<comment> \<open> \<^term>\<open>c\<^bold>?x\<in>A \<rightarrow> P x\<close>, param. tick\<close>
    val mk_prefix_read_abs : term -> (string * typ) list 
                                  -> term -> term -> term \<comment> \<open> \<^term>\<open>c\<^bold>?(x,y,z)\<in>A \<rightarrow> P x y\<close>, p. tick\<close>
    val mk_ndet_write_set: term -> term -> term -> term   \<comment> \<open> \<^term>\<open>c\<^bold>!\<^bold>!x\<in>A \<rightarrow> P x\<close>\<close>
    val mk_ndet_write_set_: term -> term -> term -> term  \<comment> \<open> \<^term>\<open>c\<^bold>!\<^bold>!x\<in>A \<rightarrow> P x\<close>, param. tick\<close>
    val mk_ndet_write_set_abs: term -> (string * typ) list
                                    -> term -> term -> term   
                                                          \<comment> \<open> \<^term>\<open>c\<^bold>!\<^bold>!(x,y,z)\<in>A \<rightarrow> P x\<close>, p. tick\<close>
    val mk_ndet_write_pred: term -> term -> term -> term  \<comment> \<open> \<^term>\<open>c\<^bold>!\<^bold>!x \<^bold>| Pr x \<rightarrow> P x\<close>\<close>
    val mk_ndet_write_pred_abs: typ -> term
                                    -> (string * typ) list
                                    -> term -> term -> term   
                                                          \<comment> \<open> \<^term>\<open>c\<^bold>!\<^bold>!(x,y,z)\<^bold>|(x>5\<and>y=x+3) \<rightarrow> P x\<close>, 
                                                                    param. tick\<close>

    (* HOL-CSPM architectural ops *)                                                        
    val mk_MultiSync_: typ -> term -> term -> term -> term\<comment> \<open> \<^term>\<open> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>  idx \<in># M. P idx\<close>, p. tick\<close>
    val mk_MultiSync: term -> term -> term -> term        \<comment> \<open> \<^term>\<open> \<^bold>\<lbrakk>S\<^bold>\<rbrakk>  idx \<in># M. P idx\<close>\<close>
    val mk_MultiInter_: typ -> term -> term -> term       \<comment> \<open> \<^term>\<open> \<^bold>|\<^bold>|\<^bold>| idx \<in># M. P idx\<close>, p. tick\<close>
    val mk_MultiInter: term -> term -> term               \<comment> \<open> \<^term>\<open> \<^bold>|\<^bold>|\<^bold>| idx \<in># M. P idx\<close>\<close>
    val mk_MultiPar_: typ -> term -> term -> term         \<comment> \<open> \<^term>\<open> \<^bold>|\<^bold>|  idx \<in># M. P idx\<close>, p. tick\<close>
    val mk_MultiPar: term -> term -> term                 \<comment> \<open> \<^term>\<open> \<^bold>|\<^bold>|  idx \<in># M. P idx\<close>\<close>
    val mk_Interrupt: term -> term -> term                \<comment> \<open> \<^term>\<open>P \<triangle> Q\<close>\<close>
    val mk_Sliding: term -> term -> term                  \<comment> \<open> \<^term>\<open>P \<rhd> Q\<close>\<close>

end = struct

local open HOLogic in

(* why the heck is this missing in HOLogic ? *)
fun dest_listT  (Type (\<^type_name>\<open>List.list\<close>, [T])) = T
  | dest_listT T = raise TYPE ("dest_listT: list type expected", [T], []);
fun mk_multisetT ty = Type(\<^type_name>\<open>multiset\<close>,[ty])
fun dest_multisetT (Type(\<^type_name>\<open>multiset\<close>, [ty])) = ty 
  | dest_multisetT T = raise TYPE ("dest_multisetT: multiset type expected", [T], []);


(* the core *)
fun is_processpT (Type(\<^type_name>\<open>Process.process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[_,_])) = true
   |is_processpT _ = false

fun mk_processpT typarm tyres = Type(\<^type_name>\<open>Process.process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[typarm,tyres])
fun mk_processT typarm = Type(\<^type_name>\<open>Process.process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[typarm,unitT])

fun dest_processpT (Type(\<^type_name>\<open>Process.process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[ty,ty'])) = (ty,ty')
  | dest_processpT T = raise TYPE ("dest_processpT: skip-parametric process type expected", [T], []);

fun dest_processT (Type(\<^type_name>\<open>Process.process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[ty,Type(\<^type_name>\<open>unit\<close>,[])])) = ty
  | dest_processT T = raise TYPE ("dest_processT: non-skip-parametric process type expected", [T], []);

fun mk_evT_ ty ty' = Type(\<^type_name>\<open>Process.event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[ty,ty'])
fun mk_evT ty = mk_evT_ ty unitT

fun dest_evT (Type(\<^type_name>\<open>Process.event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[ty,ty'])) = ty
   |dest_evT T = raise TYPE ("dest_evT: event type expected", [T], []);

fun dest_evT_ (Type(\<^type_name>\<open>Process.event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,[ty,ty'])) = (ty,ty')
   |dest_evT_ T = raise TYPE ("dest_evT: event type expected", [T], []);

fun mk_ev_ ty_res S = let val ty = fastype_of S 
                      in (Const(\<^const_name>\<open>Process.ev\<close>,ty --> mk_evT_ ty ty_res) $ S) end
fun mk_ev S = mk_ev_ unitT S
fun dest_ev (Const(\<^const_name>\<open>Process.ev\<close>,_) $ S) = S
  | dest_ev T = raise TERM ("dest_ev: event-constructor expected", [T]);

fun mk_tick_ ty_ev S = let val ty_res = fastype_of S 
                       in Const(\<^const_name>\<open>Process.tick\<close>,ty_res --> mk_evT_ ty_ev ty_res) $ S end
fun mk_tick ty_ev = Const(\<^const_name>\<open>Process.tick\<close>,unitT --> mk_evT_ ty_ev unitT) $ unit
fun dest_tick (Const(\<^const_name>\<open>Process.tick\<close>,_) $ S) = S
  | dest_tick T = raise TERM ("dest_tick: tick-constructor expected", [T]);

fun mk_mset S = 
    let val ty = dest_listT(fastype_of S)
    in  Const(\<^const_name>\<open>Multiset.mset\<close>,listT ty --> mk_multisetT ty) $ S end
fun dest_mset (Const(\<^const_name>\<open>Multiset.mset\<close>,_) $ S) = S 
  | dest_mset T = raise TERM ("dest_mset: multiset list-constructor expected", [T]);

(* the CSP base *)
val _ = \<^term>\<open>SKIP t\<close>
fun mk_SKIP ty ty_res = Const(\<^const_name>\<open>SKIP\<close>, ty_res --> mk_processpT ty ty_res)
fun mk_Skip ty = Const(\<^const_name>\<open>SKIP\<close>, unitT --> mk_processT ty) $ unit  


val _ = \<^term>\<open>STOP\<close>
fun mk_STOP ty = Const(\<^const_name>\<open>STOP\<close>, mk_processT ty)
fun mk_STOP_ ty ty'= Const(\<^const_name>\<open>STOP\<close>, mk_processpT ty ty')

val _ = \<^term>\<open>bottom\<close>
fun mk_BOT ty = Const(\<^const_name>\<open>bottom\<close>, mk_processT ty)
fun mk_BOT_ ty ty' = Const(\<^const_name>\<open>bottom\<close>, mk_processpT ty ty')


val _ = \<^term>\<open>P \<box> Q\<close>
fun mk_Det P Q = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Det\<close>,ty --> ty --> ty) $ P $ Q end

val _ = \<^term>\<open>P \<sqinter> Q\<close>
fun mk_NDet P Q = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Ndet\<close>,ty --> ty --> ty) $ P $ Q end


val _ = \<^term>\<open>c\<^bold>?(x,y)\<in>A \<rightarrow> P x y\<close>
fun mk_prefix_read ch A P = 
    let val ty = fastype_of ch
        val ty_ev = domain_type ty
        val ty_ch = range_type ty
        val read_ty = [ty,HOLogic.mk_setT ty_ev, ty_ev --> mk_processT ty_ch] ---> mk_processT ty_ch
    in Const(\<^const_name>\<open>read\<close>, read_ty) $ ch $ A $ P end
val test0 = Thm.cterm_of @{context} 
                         (mk_prefix_read  (\<^const>\<open>Suc\<close>) 
                                          (mk_set natT [mk_nat 0]) 
                                          (Abs("x",natT,(mk_Skip natT))) )

fun mk_prefix_read_ ch A P = 
    let val ty = fastype_of ch
        val ty_ev = domain_type ty
        val tyP = fastype_of P
        val read_ty = [ty,HOLogic.mk_setT ty_ev, tyP] ---> (range_type tyP)
    in Const(\<^const_name>\<open>read\<close>, read_ty) $ ch $ A $ P end
val test0 = Thm.cterm_of @{context} 
                         (mk_prefix_read_  (\<^const>\<open>Suc\<close>) 
                                           (mk_set natT [mk_nat 0]) 
                                           (Abs("_",natT,mk_SKIP natT natT $ Bound 0)) )


val _ = \<^term>\<open>c\<^bold>?(x,y)\<in>A \<rightarrow> P x y\<close>
fun  mk_prefix_read_abs ch [] A P = error "mk_prefix_read_abs: empty arg list"
   | mk_prefix_read_abs ch L A P = mk_prefix_read_ ch A (tupled_lambda (mk_tuple (map Free L)) P) 
val test0 = Thm.cterm_of @{context} 
                         (mk_prefix_read_abs (\<^term>\<open>f:: nat\<times>bool \<Rightarrow> int\<close>) [("x",natT),("y",boolT)] 
                                             (\<^term>\<open>UNIV \<times> UNIV :: (nat\<times>bool)set\<close>) 
                                             (mk_SKIP intT natT $ (Free("x",natT))))

val _ = \<^term>\<open>c\<^bold>!\<^bold>!x\<in>A \<rightarrow> P x\<close>
fun mk_ndet_write_set ch A P = 
       let val ty = fastype_of ch
           val ty_ev = domain_type ty
           val ty_ch = range_type ty
           val read_ty = [ty,HOLogic.mk_setT ty_ev, ty_ev --> mk_processT ty_ch] ---> mk_processT ty_ch
       in  Const(\<^const_name>\<open>ndet_write\<close>, read_ty) $ ch $ A $ P end
val test0 = Thm.cterm_of @{context} 
                         (mk_ndet_write_set  (\<^const>\<open>Suc\<close>) 
                                             (mk_set natT [mk_nat 0]) 
                                             (Abs("x",natT,(mk_Skip natT))) )


val _ = \<^term>\<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P x\<close>
fun mk_ndet_write_set_ ch A P = 
    let val ty = fastype_of ch
        val ty_ev = domain_type ty
        val tyP = fastype_of P
        val write_ty = [ty,HOLogic.mk_setT ty_ev, tyP] ---> (range_type tyP)
    in Const(\<^const_name>\<open>ndet_write\<close>, write_ty) $ ch $  A $ P end
val test0 = Thm.cterm_of @{context} 
                         (mk_ndet_write_set_ (\<^const>\<open>Suc\<close>) 
                                             (mk_set natT [mk_nat 0]) 
                                             (Abs("_",natT,mk_SKIP natT natT $ Bound 0)) )

val _ = \<^term>\<open>c\<^bold>!\<^bold>!(x,y)\<in>A \<rightarrow> P x\<close>
fun  mk_ndet_write_set_abs ch [] A P = error "mk_ndet_write_set_abs: empty arg list"
   | mk_ndet_write_set_abs ch L A P = mk_ndet_write_set_ ch A (tupled_lambda (mk_tuple (map Free L)) P) 

val _ = \<^term>\<open>c\<^bold>!\<^bold>!y \<^bold>| (y > 5) \<rightarrow> P x\<close> 
fun mk_ndet_write_pred_ ty_res ch Pr P = 
    let val ty = fastype_of ch
        val ty_ev = domain_type ty
        val ty_ch = range_type ty
        val tyP = mk_processpT ty_ch ty_res
        val write_ty = [ty,HOLogic.mk_setT ty_ev, ty_ev --> tyP] ---> tyP
    in   Const(\<^const_name>\<open>ndet_write\<close>, write_ty) $ ch $ (Collect_const ty_ev $ Pr) $ P end
fun mk_ndet_write_pred ch Pr P = mk_ndet_write_pred_ unitT ch Pr P
val test0 = Thm.cterm_of @{context} 
                         (mk_ndet_write_pred (\<^const>\<open>Suc\<close>)  
                                             (Abs("x", natT,\<^term>\<open>True\<close>)) 
                                             (Abs("x",natT, mk_Skip natT )) )


val _ = \<^term>\<open>c\<^bold>!\<^bold>!(x,y) \<^bold>| (x=0 \<and> y > 5) \<rightarrow> P x\<close> 
fun  mk_ndet_write_pred_abs ty_res ch [] _ _ = error "mk_ndet_write_pred_abs: empty arg list"
   | mk_ndet_write_pred_abs ty_res ch L Pr P = mk_ndet_write_pred_ ty_res ch 
                                                   (tupled_lambda (mk_tuple (map Free L)) Pr)
                                                   (tupled_lambda (mk_tuple (map Free L)) P) 
val test0 = Thm.cterm_of @{context} 
                         (mk_ndet_write_pred_abs natT (\<^term>\<open>f:: nat\<times>bool \<Rightarrow> int\<close>) 
                                                 [("x",natT),("y",boolT)] 
                                                 (\<^term>\<open>y=True \<and> x > (5::nat)\<close>) 
                                                 ( mk_SKIP intT natT $ (Free("x",natT))))
val _ = \<^term>\<open>a \<rightarrow> P\<close>
fun mk_write ev P = 
       let val ty = fastype_of ev
       in Const(\<^const_name>\<open>write0\<close>, ty --> mk_processT ty --> mk_processT ty) $ ev $ P end
val test0 = Thm.cterm_of @{context} (mk_write  (mk_nat 0) (mk_Skip natT) )

fun mk_write_ ev P = 
       let val pty = fastype_of P
           val (ty_ev,_) = dest_processpT pty
       in  Const(\<^const_name>\<open>write0\<close>, ty_ev --> pty --> pty) $ ev $ P end
val test0 = Thm.cterm_of @{context} (mk_write_  (mk_nat 0) (mk_SKIP natT boolT $ @{term True}))

val _ = \<^term>\<open>\<box>(x,y)\<in>A \<rightarrow> P x\<close>
fun mk_prefix A P_fun = 
    let val ty = dest_setT(fastype_of A)
    in  Const (\<^const_name>\<open>Mprefix\<close>,mk_setT ty --> (ty --> mk_processT ty)) $ A $ P_fun end

val _ = \<^term>\<open>\<sqinter>x\<in>A \<rightarrow> P x\<close>
fun mk_Mndetprefix A P_fun = 
    let val ty = dest_setT(fastype_of A)
    in  Const (\<^const_name>\<open>Mndetprefix\<close>,mk_setT ty --> (ty --> mk_processT ty)) $ A $ P_fun end


val _ = \<^term>\<open>P \<^bold>; Q\<close>
fun mk_Seq P Q = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Seq\<close>,ty --> ty --> ty) $ P $ Q end

val _ = \<^term>\<open>P \ A\<close>
fun mk_Hiding P A = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Hiding.Hiding\<close>, ty --> mk_setT(dest_processT ty) --> ty) $ P $ A end
        
val _ = \<^term>\<open>P \<lbrakk>A\<rbrakk> Q\<close>
fun mk_Sync P A Q = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Sync\<close>, ty --> mk_setT(dest_processT ty) --> ty --> ty) $ P $ A $ Q end
val test = Thm.cterm_of @{context} (mk_Sync (mk_Skip natT) (mk_UNIV natT) (mk_Skip natT) )

val _ = \<^term>\<open>P || Q\<close>
fun mk_Par P Q = 
    let val ty = dest_processT(fastype_of P) 
    in mk_Sync P (Const(\<^const_name>\<open>Orderings.top_class.top\<close>, mk_setT ty)) Q end

val _ = \<^term>\<open>P ||| Q\<close>
fun mk_Inter P Q = 
    let val ty = dest_processT(fastype_of P) 
    in mk_Sync P (Const(\<^const_name>\<open>Orderings.bot_class.bot\<close>, mk_setT ty)) Q end

val _ = \<^term>\<open>P \<rhd> Q\<close>
fun mk_Sliding P Q = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Sliding\<close>,ty --> ty --> ty) $ P $ Q end

val _ = \<^term>\<open>P \<triangle> Q\<close>
fun mk_Interrupt P Q = 
    let val ty = fastype_of P 
    in  Const(\<^const_name>\<open>Interrupt\<close>,ty --> ty --> ty) $ P $ Q end

val _ = \<^term>\<open>Renaming.Renaming P f\<close>
fun mk_Renaming P f = 
    let val ty = fastype_of f 
        val ty_res = mk_processT(domain_type ty) --> ty --> mk_processT(range_type ty)
    in  Const(\<^const_name>\<open>Renaming.Renaming\<close>, ty_res) $ P $ f end

val _ = \<^term>\<open> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P p\<close> (* avoids typing P for efficiency reasons *)
fun mk_MultiSync_ ty_res S M P = 
    let val ty_S = fastype_of S
        val ty = dest_setT ty_S
        val ty_M = fastype_of M
        val ty' = dest_multisetT ty_M
        val ty'' = ty_S --> ty_M --> (ty' --> mk_processpT ty ty_res) --> mk_processpT ty ty_res
    in  Const(\<^const_name>\<open>MultiSync\<close>, ty'') $ S $ M $ P end
val test0 = Thm.cterm_of @{context} (mk_MultiSync_ boolT (mk_UNIV natT) 
                                    (\<^term>\<open>{#}::nat multiset\<close>) 
                                    (Abs("x", natT, (mk_SKIP natT boolT $ @{term True}))) )

fun mk_MultiSync S M P = mk_MultiSync_ unitT S M P
val test0 = Thm.cterm_of @{context} (mk_MultiSync (mk_UNIV natT) 
                                    (\<^term>\<open>{#}::nat multiset\<close>) 
                                    (\<^term>\<open>\<lambda>x::nat. Skip::nat process\<close>) ) 



val _ = \<^term>\<open> \<^bold>|\<^bold>| p \<in># M. P p\<close>
fun mk_MultiPar_ ty_res M P = 
    let val ty = dest_multisetT (fastype_of M) 
    in  mk_MultiSync_ ty_res (Const(\<^const_name>\<open>Orderings.top_class.top\<close>, mk_setT ty)) M P end
fun mk_MultiPar M P = mk_MultiPar_ unitT M P


val _ = \<^term>\<open> \<^bold>|\<^bold>|\<^bold>| p \<in># M. P x\<close>
fun mk_MultiInter_ ty_res M P = 
    let val ty = dest_multisetT (fastype_of M) 
    in  mk_MultiSync_ ty_res (Const(\<^const_name>\<open>Orderings.bot_class.bot\<close>, mk_setT ty)) M P end
fun mk_MultiInter M P = mk_MultiInter_ unitT M P

end (* open HOLogic *)
end
