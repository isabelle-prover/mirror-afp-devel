(***********************************************************************************
 * Copyright (c) 2021-2023 University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

structure Activation_Term:ACTIVATION_TERM = struct
  datatype mode = Single | MultiList | MultiMatrix
  open TensorFlow_Type
  fun term_of_activation_single Linear      = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Identity\<close>}
    | term_of_activation_single Softsign   = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.SoftSign\<close>}
    | term_of_activation_single Sign   = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Sign\<close>}
    | term_of_activation_single BinaryStep   = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.BinaryStep\<close>}
    | term_of_activation_single Sigmoid = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Sigmoid\<close>}
    | term_of_activation_single Swish = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Swish\<close>}
    | term_of_activation_single Tanh = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Tanh\<close>}
    | term_of_activation_single Relu = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.ReLU\<close>}
    | term_of_activation_single Gelu = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.GeLUapprox\<close>}
    | term_of_activation_single GRelu = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.GReLU\<close>}
    | term_of_activation_single Softplus = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Softplus\<close>}
    | term_of_activation_single Elu = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.ELU\<close>}
    | term_of_activation_single Selu = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.SELU\<close>}
    | term_of_activation_single Exponential = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Exp\<close>}
    | term_of_activation_single Hard_sigmoid = @{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.HardSigmoid\<close>}
    | term_of_activation_single Sigmoid_taylor = (@{Const \<open>Activation_Functions.activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e.Sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}$HOLogic.mk_nat 2)
    | term_of_activation_single Softmax = error "Activation fuction 'softmax' is not a single class activation function."
    | term_of_activation_single Softmax_taylor = error "Activation fuction 'softmax_taylor' is not a single class activation function."
  
  fun term_of_activation_multi Linear      = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mIdentity\<close>}
    | term_of_activation_multi Softsign   = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSoftSign\<close>}
    | term_of_activation_multi Sign   = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSign\<close>}
    | term_of_activation_multi BinaryStep   = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mBinaryStep\<close>}
    | term_of_activation_multi Sigmoid = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSigmoid\<close>}
    | term_of_activation_multi Swish = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSwish\<close>}
    | term_of_activation_multi Tanh = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mTanh\<close>}
    | term_of_activation_multi Relu = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mReLU\<close>}
    | term_of_activation_multi Gelu = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mGeLUapprox\<close>}
    | term_of_activation_multi GRelu = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mGReLU\<close>}
    | term_of_activation_multi Softplus = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSoftplus\<close>}
    | term_of_activation_multi Elu = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mELU\<close>}
    | term_of_activation_multi Selu = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSELU\<close>}
    | term_of_activation_multi Exponential = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mExp\<close>}
    | term_of_activation_multi Hard_sigmoid = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mHardSigmoid\<close>}
    | term_of_activation_multi Softmax = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSoftmax\<close>}
    | term_of_activation_multi Sigmoid_taylor = (@{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}$HOLogic.mk_nat 2)
    | term_of_activation_multi Softmax_taylor = @{Const \<open>Activation_Functions.activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i.mSoftmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}
                                                 $(HOLogic.mk_nat 2)


  fun term_of_activation_eqn_single Linear      = @{const \<open>Activation_Functions.identity\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Softsign   = @{const \<open>Activation_Functions.softsign\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Sign   = @{const \<open>Activation_Functions.sign\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single BinaryStep   = @{const \<open>Activation_Functions.binary_step\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Sigmoid = @{const \<open>Activation_Functions.sigmoid\<close>}
    | term_of_activation_eqn_single Swish = @{const \<open>Activation_Functions.swish\<close>}
    | term_of_activation_eqn_single Tanh = @{const \<open>Transcendental.tanh\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Relu = @{const \<open>Activation_Functions.relu\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Gelu = @{const \<open>Activation_Functions.gelu_approx\<close>}
    | term_of_activation_eqn_single GRelu = @{const \<open>Activation_Functions.generalized_relu\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Softplus = @{const \<open>Activation_Functions.softplus\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Elu = @{const \<open>Activation_Functions.elu\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Selu = @{const \<open>Activation_Functions.selu\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Exponential = @{const \<open>Transcendental.exp\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Hard_sigmoid = @{const \<open>Activation_Functions.hard_sigmoid\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Sigmoid_taylor = @{const \<open>Activation_Functions.sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>(\<open>real\<close>)}
    | term_of_activation_eqn_single Softmax = error "Activation fuction 'softmax' is not a single class activation function."
    | term_of_activation_eqn_single Softmax_taylor = error "Activation fuction 'softmax_taylor' is not a single class activation function."

  fun term_of_activation_eqn_multi_list Linear      = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.identity\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Softsign   = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.softsign\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Sign   = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.sign\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list BinaryStep   = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.binary_step\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Sigmoid = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.sigmoid\<close>})
    | term_of_activation_eqn_multi_list Swish = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.swish\<close>})
    | term_of_activation_eqn_multi_list Tanh = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Transcendental.tanh\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Relu = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.relu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Gelu = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.gelu_approx\<close>})
    | term_of_activation_eqn_multi_list GRelu = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.generalized_relu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Softplus = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.softplus\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Elu = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.elu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Selu = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.selu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Exponential = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Transcendental.exp\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Hard_sigmoid = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.hard_sigmoid\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Sigmoid_taylor = (@{const \<open>map\<close>(real,real)})$(@{const \<open>Activation_Functions.sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>(\<open>real\<close>)}$(HOLogic.mk_nat 2) )
    | term_of_activation_eqn_multi_list Softmax = (@{const \<open>Activation_Functions.softmax\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_list Softmax_taylor = (@{const \<open>Activation_Functions.softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>(\<open>real\<close>)}$HOLogic.mk_nat 2)

  fun term_of_activation_eqn_multi_matrix Linear      = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.identity\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Softsign   = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.softsign\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Sign   = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.sign\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix BinaryStep   = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.binary_step\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Sigmoid = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.sigmoid\<close>})
    | term_of_activation_eqn_multi_matrix Swish = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.swish\<close>})
    | term_of_activation_eqn_multi_matrix Tanh = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Transcendental.tanh\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Relu = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.relu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Gelu = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.gelu_approx\<close>})
    | term_of_activation_eqn_multi_matrix GRelu = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.generalized_relu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Softplus = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.softplus\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Elu = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.elu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Selu = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.selu\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Exponential = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Transcendental.exp\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Hard_sigmoid = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.hard_sigmoid\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Sigmoid_taylor = (@{const \<open>map_vec\<close>(real,real)})$(@{const \<open>Activation_Functions.sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>(\<open>real\<close>)}$(HOLogic.mk_nat 2) )
    | term_of_activation_eqn_multi_matrix Softmax = (@{const \<open>Activation_Functions.msoftmax\<close>(\<open>real\<close>)})
    | term_of_activation_eqn_multi_matrix Softmax_taylor = (@{const \<open>Activation_Functions.msoftmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>(\<open>real\<close>)}$HOLogic.mk_nat 2)


  fun add_function binding eqs lthy =
    let
  val cfg =
    Function_Common.FunctionConfig { sequential=true, default=NONE,
      domintros=true, partials=false}
      val eq_defs = map (fn eq => (((Binding.empty, []), eq), [], [])) eqs
      val ctx =
        Function_Fun.add_fun [(binding, NONE, NoSyn)]
          eq_defs
          cfg  lthy;
    in
       ctx      
    end

   val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq
   fun remdups (x::xs) = if NONE <> (List.find (fn x' => x'=x) xs) then remdups xs else x::(remdups xs)
     | remdups [] = []

      fun lemma_phi_ran mode defN phitab lthy = 
      let 
         fun get_local_thms n0 n1 = Proof_Context.get_thms lthy (Local_Theory.full_name lthy (Binding.qualify false defN (Binding.qualify_name false (Binding.name (n0))  n1) ))
        fun mk_ss ctx thms = put_simpset HOL_basic_ss ctx addsimps thms
        val phitab = remdups phitab
        val Phi = Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name defN) ("\<phi>_"^defN))
        val phi_const = case mode of 
                        Single => Const(Phi, @{typ \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e \<Rightarrow> (real \<Rightarrow> real) option\<close>})
                      | MultiList => Const(Phi, @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real list \<Rightarrow> real list) option\<close>})
                      | MultiMatrix => Const(Phi, @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real Matrix.vec \<Rightarrow> real Matrix.vec) option\<close>})
         val ran_const = case mode of 
                        Single => @{const "ran" (\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>, \<open>real \<Rightarrow> real\<close>)}
                      | MultiList => @{const "ran" (\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real list \<Rightarrow> real list\<close>)}
                      | MultiMatrix => @{const "ran" (\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real Matrix.vec \<Rightarrow> real Matrix.vec\<close>)}
         val lhs = ran_const$phi_const 
         val rhs =  case mode of 
                           Single => HOLogic.mk_set @{typ "real \<Rightarrow> real"} (map term_of_activation_eqn_single phitab)
                         | MultiList  => HOLogic.mk_set @{typ "real list \<Rightarrow> real list"} (map term_of_activation_eqn_multi_list phitab)
                         | MultiMatrix  => HOLogic.mk_set @{typ "real Matrix.vec\<Rightarrow> real Matrix.vec"} (map term_of_activation_eqn_multi_matrix phitab)
      in
         nn_tactics.prove_simple (Binding.qualify_name false (Binding.name defN) "\<phi>_ran")
                      (mk_Trueprop_eq (lhs,rhs))
    
                    (fn ctx =>  auto_tac (mk_ss ctx [@{thm "ran_def"},@{thm "ranI"}]) 
                           THEN eresolve_tac ctx (get_local_thms ("\<phi>_"^defN) "elims") 1  
                           THEN auto_tac (mk_ss ctx [@{thm "ran_def"},@{thm "ranI"}])
                           THEN ALLGOALS (Meson.meson_tac ctx ([@{thm "bot.extremum"}, @{thm "insert_subsetI"}, @{thm "ranI"}]@(get_local_thms ("\<phi>_"^defN) "simps")) )
                     )  lthy 
(*  
                   (fn s => Skip_Proof.cheat_tac lthy 1) lthy 
 *)     end 

  fun def_phi_tab mode defN phitab lthy = 
      let
        val phitab = remdups phitab
        val Phi = "\<phi>_"^defN 
        fun phi_tab_term Phi mode = case mode of 
                        Single => Free(Phi, @{typ \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e \<Rightarrow> (real \<Rightarrow> real) option\<close>})
                      | MultiList => Free(Phi, @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real list \<Rightarrow> real list) option\<close>})
                      | MultiMatrix => Free(Phi, @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real Matrix.vec \<Rightarrow> real Matrix.vec) option\<close>})

        fun mk_term phi = 
            let 
              val lhs =  case mode of 
                           Single => (phi_tab_term Phi mode)$(term_of_activation_single phi)
                         | MultiList => (phi_tab_term Phi mode)$(term_of_activation_multi phi)
                         | MultiMatrix => (phi_tab_term Phi mode)$(term_of_activation_multi phi)
              val rhs =  case mode of 
                           Single => @{const \<open>Some\<close>(\<open>real \<Rightarrow>real\<close>)}$(term_of_activation_eqn_single phi)
                         | MultiList  => @{const \<open>Some\<close>(\<open>real list \<Rightarrow>real list\<close>)}$(term_of_activation_eqn_multi_list phi)
                         | MultiMatrix  => @{const \<open>Some\<close>(\<open>real Matrix.vec \<Rightarrow>real Matrix.vec\<close>)}$(term_of_activation_eqn_multi_matrix phi)
            in
               mk_Trueprop_eq (lhs,rhs)
            end 
        val catch_all_lhs = case mode of 
                              Single =>  (Free(Phi, @{typ \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e \<Rightarrow> (real \<Rightarrow> real) option\<close>}))$(@{term \<open>(x::activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e)\<close>})
                            | MultiList =>   (Free(Phi, @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real list \<Rightarrow> real list) option\<close>}))$(@{term \<open>(x::activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i)\<close>})
                            | MultiMatrix =>   (Free(Phi, @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real Matrix.vec \<Rightarrow> real Matrix.vec) option\<close>}))$(@{term \<open>(x::activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i)\<close>})
        val catch_all_rhs = case mode of 
                              Single => @{term "None::(real \<Rightarrow> real) option"}
                            | MultiList   =>  @{term "None::(real list \<Rightarrow> real list) option"}
                            | MultiMatrix =>  @{term "None::(real Matrix.vec \<Rightarrow> real Matrix.vec) option"}
                                      
                                      
        val eqs =  (map mk_term phitab)@[mk_Trueprop_eq(catch_all_lhs, catch_all_rhs)]
      in
        (snd o Local_Theory.begin_nested) lthy
        |> add_function (Binding.qualify_name true (Binding.name defN) ("\<phi>_"^defN)) eqs 
        |> Local_Theory.end_nested
        |> (snd o Local_Theory.begin_nested)
        |> lemma_phi_ran mode defN phitab 
        |> Local_Theory.end_nested

      end 


end 
