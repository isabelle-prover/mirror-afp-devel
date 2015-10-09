(*****************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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
 ******************************************************************************)

section\<open>Toy Meta-Model aka. AST definition of Toy (II)\<close>

theory  Meta_Toy_extended
imports "../../../Init"
begin

subsection\<open>Type Definition\<close>

datatype internal_oid = Oid nat
datatype internal_oids = Oids nat (* start *)
                              nat (* oid for assoc (incremented from start) *)
                              nat (* oid for inh (incremented from start) *)

datatype toy_def_base = ToyDefInteger "string" (* integer digit *)
                      | ToyDefReal "string (* integer digit (left) *) \<times> string (* integer digit (right) *)"
                      | ToyDefString "string"

datatype toy_data_shallow = ShallB_term toy_def_base
                          | ShallB_str string (* binding *)
                          | ShallB_self internal_oid
                          | ShallB_list "toy_data_shallow list"

datatype 'a toy_list_attr = ToyAttrNoCast 'a (* inh, own *)
                          | ToyAttrCast
                              string (* cast from *)
                              "'a toy_list_attr" (* cast entity *)
                              'a (* inh, own *)

record toy_instance_single = Inst_name :: "string option" (* None: fresh name to be generated *)
                             Inst_ty :: "string option" (* type *)
                             Inst_attr :: "((  (string (* pre state *) \<times> string (* post state *)) option
                                               (* state used when toy_data_shallow is an object variable (for retrieving its oid) *)
                                             \<times> string (*name*)
                                             \<times> toy_data_shallow) list) (* inh and own *)
                                           toy_list_attr"

datatype toy_instance = ToyInstance "toy_instance_single list" (* mutual recursive *)

datatype toy_def_base_l = ToyDefBase "toy_def_base list"

datatype 'a toy_def_state_core = ToyDefCoreAdd toy_instance_single
                               | ToyDefCoreBinding 'a

datatype toy_def_state = ToyDefSt  string (* name *)
                                  "string (* name *) toy_def_state_core list"

datatype toy_def_pp_core = ToyDefPPCoreAdd "string (* name *) toy_def_state_core list"
                         | ToyDefPPCoreBinding string (* name *)

datatype toy_def_pre_post = ToyDefPP
                              "string option" (* None: fresh name to be generated *)
                              toy_def_pp_core (* pre *)
                              "toy_def_pp_core option" (* post *) (* None: same as pre *)

subsection\<open>Object ID Management\<close>

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Succ n2) (Succ n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Succ n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitAll = (\<lambda>Oids n1 _ _ \<Rightarrow> Oids n1 n1 n1)"
definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"

subsection\<open>Operations of Fold, Map, ..., on the Meta-Model\<close>

definition "toy_instance_single_empty = \<lparr> Inst_name = None, Inst_ty = None, Inst_attr = ToyAttrNoCast [] \<rparr>"

fun map_data_shallow_self where
   "map_data_shallow_self f e = (\<lambda> ShallB_self s \<Rightarrow> f s
                                 | ShallB_list l \<Rightarrow> ShallB_list (List.map (map_data_shallow_self f) l)
                                 | x \<Rightarrow> x) e"

fun map_list_attr where
   "map_list_attr f e = 
     (\<lambda> ToyAttrNoCast x \<Rightarrow> ToyAttrNoCast (f x)
      | ToyAttrCast c_from l_attr x \<Rightarrow> ToyAttrCast c_from (map_list_attr f l_attr) (f x)) e"

definition "map_instance_single f toyi = toyi \<lparr> Inst_attr := map_list_attr (L.map f) (Inst_attr toyi) \<rparr>"

fun fold_list_attr where
   "fold_list_attr cast_from f l_attr accu = (case l_attr of
        ToyAttrNoCast x \<Rightarrow> f cast_from x accu
      | ToyAttrCast c_from l_attr x \<Rightarrow> fold_list_attr (Some c_from) f l_attr (f cast_from x accu))"

definition "inst_ty0 toyi = (case Inst_ty toyi of Some ty \<Rightarrow> Some ty
                                                | None \<Rightarrow> (case Inst_attr toyi of ToyAttrCast ty _ _ \<Rightarrow> Some ty
                                                                                | _ \<Rightarrow> None))"
definition "inst_ty toyi = (case inst_ty0 toyi of Some ty \<Rightarrow> ty)"

definition "fold_instance_single f toyi = fold_list_attr (inst_ty0 toyi) (\<lambda> Some x \<Rightarrow> f x) (Inst_attr toyi)"
definition "fold_instance_single' f toyi = fold_list_attr (Inst_ty toyi) f (Inst_attr toyi)"

end
