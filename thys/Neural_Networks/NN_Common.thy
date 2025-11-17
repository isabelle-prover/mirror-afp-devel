(***********************************************************************************
 * Copyright (c) University of Exeter, UK
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

section\<open>Common Infrastructure\<close>
theory NN_Common
imports
  TensorFlow_Import
  Complex_Main
  "HOL-Decision_Procs.Approximation"
  "HOL-Eisbach.Eisbach"
keywords
    "import_data_file" :: thy_load
begin


text\<open>
  In this theory we define common infrastructure that is used by most formalizations of 
  neural networks. 
\<close>



subsection\<open>Utility Functions\<close>
ML\<open>
structure nn_common_utils = struct

   val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq
    fun define_lemmas name thm_names = Specification.theorems_cmd "" 
                                  [((name, []), map (fn n => (Facts.named n, [])) thm_names)] 
                                  [] false
    fun make_const_def (binding, trm) lthy = let
            val lthy' =  snd ( Local_Theory.begin_nested lthy )
            val arg = ((binding, NoSyn), ((Thm.def_binding binding,@{attributes [code]}), trm)) 
            val ((_, (_ , thm)), lthy'') = Local_Theory.define arg lthy'
        in
            (thm, Local_Theory.end_nested lthy'')
        end


end
\<close>

definition \<open>map_of_list =  map_of o  (List.enumerate 0)\<close>

subsection\<open>Data Import\<close>

ML\<open>
structure Data_Import = struct
  fun parseRealLines lines = 
        map ((map (Option.valOf o IEEEReal.fromString)) o (String.tokens Char.isSpace)) lines
        handle Option => (error "Invalid data error in parseRealData")
  fun term_of_RealList data =
      let
        fun term_of_real_list reals = HOLogic.mk_list (@{typ "real"}) (map (Nano_Json_Type.term_of_real false) reals)
      in
        HOLogic.mk_list (@{typ "real list"}) (map term_of_real_list data)
      end
  fun def_data name lines =
      let 
        val data_term = term_of_RealList (parseRealLines lines)
      in 
        Nano_Json_Parser_Isar.make_const_def (Binding.name name,data_term)
      end
end

val _ = Outer_Syntax.command \<^command_keyword>\<open>import_data_file\<close>
        "Import test or training data and bind it to a constant."
        ((Resources.parse_file -- \<^keyword>\<open>defining\<close> -- Parse.name) >>
         (fn ((get_file,_),name) =>
           Toplevel.theory (fn thy =>
           let
              val ({lines, ...}:Token.file) = get_file thy
              val lines' = List.filter (fn s => (s <> "")) lines
           in Named_Target.theory_map (snd o (Data_Import.def_data name lines')) thy end)))
\<close>


subsection\<open>Common Infrastructure for Proof Tactics\<close>
ML\<open>
  
  datatype nn_proof_mode = SKIP | SORRY | EVAL | NBE | SAFE
  val nn_proof_mode = Attrib.setup_config_string \<^binding>\<open>nn_proof_mode\<close> (K "nbe")
  fun get_nn_proof_mode ctxt =
    (case Config.get ctxt nn_proof_mode of
      "skip"  => SKIP
    | "sorry" => SORRY
    | "eval"  => EVAL
    | "nbe"   => NBE
    | "safe"  => SAFE
    | name => error ("Bad proof mode: " ^ quote name ^ " (\"skip\", \"sorry\", \"eval\", \"nbe\", or \"safe\" expected)"))
\<close>


ML\<open>
structure nn_tactics = struct
   fun prove_simple bname stmt tactic lthy = 
         let
           val stmt'  = Syntax.check_term lthy stmt
           val thm = Goal.prove lthy [] [] stmt' (fn {context, ...} => tactic context)
                     |> Goal.norm_result lthy
                     |> Goal.check_finished lthy
         in
           lthy |>
           snd o  Local_Theory.note ((bname, []), [thm])
         end
    
    fun prove_method_simple proof_mode method proof_state =
      let
         fun prove_it method proof_state = Seq.the_result "error in proof state" (Proof.refine method proof_state)
                                           |> Proof.global_done_proof 
      in 
        case proof_mode of
          SKIP => error "Error in proof_sate_simple, too late to skip."
        | SORRY => Proof.global_skip_proof true proof_state
        | _ => prove_it method proof_state
      end 

   fun normalize_tac ctxt = (CHANGED_PROP o
            (CONVERSION (Nbe.dynamic_conv ctxt)
              THEN_ALL_NEW (TRY o resolve_tac ctxt [TrueI])))

 fun eval_tac ctxt =
      let val conv = Code_Runtime.dynamic_holds_conv
      in
        CONVERSION (Conv.params_conv ~1 (Conv.concl_conv ~1 o conv) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end

   fun eval_or_normalize_tac lthy = 
        case get_nn_proof_mode lthy of
             SKIP  => error "Error: Too late to skip proofs."
           | SORRY => error "Error: Too late to sorry proofs."
           | EVAL  => eval_tac 
           | NBE   => normalize_tac 
           | SAFE  => Code_Simp.dynamic_tac 


end
\<close>

ML\<open>
  val nn_verbose = let
    val (nn_verbose_config, nn_verbose_setup) =
      Attrib.config_int (Binding.name "nn_verbose") (K 0)
  in
    Context.>>(Context.map_theory nn_verbose_setup);
    nn_verbose_config
  end

  structure nn_log = struct
    fun info _ prfx lthy str state = 
        let 
          val _ = if (0 < (Config.get lthy nn_verbose)) 
                  then warning (prfx^str) 
                  else () 
        in state end 
  end 
\<close>


text\<open>
  Finally, we lay out the foundations of our custom proof methods. For this, we
  utilize Eisbach~\<^cite>\<open>"matichuk.ea:eisbach:2016"\<close>.
\<close>



named_theorems nn_layer

method forced_approximation = 
  ((approximation 15 | approximation 30 | approximation 60 | approximation 120))


method predict_layer uses add =
   (simp only: nn_layer add)

lemmas [nn_layer] = list.map(2) foldl.simps if_False if_True if_cancel if_P if_not_P list.size
                    option.simps map.identity Let_def


end

