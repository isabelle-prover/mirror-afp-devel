(***********************************************************************************
 * Copyright (c) 2021-2022 University of Exeter, UK
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

structure TensorFlow_Json:TENSORFLOW_JSON  = struct 
  open Nano_Json_Type
  open Nano_Json_Query

  fun parseBinaryWeights file = let
                        fun readFloat32 istream = if BinIO.endOfStream istream
                              then []
                              else PackReal32Little.fromBytes(BinIO.inputN(istream, PackReal32Little.bytesPerElem))::(readFloat32 istream)
                        val readFloats = File_Stream.open_input (readFloat32)
                      in
                      readFloats file
                      handle IO.Io {name=n, cause=c,  ...} => (case c of OS.SysErr (n2,_) => (error (n2 ^ ": "^ n))
                                                                  | _ => (error "Unknown IO error in parseBinaryWeights"))
                      | Subscript => let val _ = error ("Binary weight file corrupt: "^(Path.implode file)) in [] end   
                     end

  fun updateWeightsManifest parent wm =
      let 
      fun getPath wm = (case wm of 
                           (ARRAY[OBJECT (("paths", ARRAY [STRING path])::_)]) 
                             => let 
                                  val p = Path.explode path
                                in 
                                  if (Path.is_absolute p) then p else Path.append parent p
                                end 
                        | _ => error ("Error in getPath:"^(Nano_Json_Serializer.serialize_json wm)))
      fun getWeightShapes wm =  (case nj_filter "weights" wm of 
                                  [(["weights"], ARRAY ws )] => ws
                                | _ =>  error "Error in getWeightShapes" )
      val weights = parseBinaryWeights (getPath wm) |> map Real32.toDecimal
      fun updateWeights (OBJECT [name, ("shape", shapeVal), _ ]) ws = 
          let
            fun tab (x,0) xs = [take x xs]
              | tab (x,1) xs = tab (x,0) xs 
              | tab (x,n) xs = [take x xs]@(tab (x, n-1) (drop x xs))

            val (shapeVal',ws') = let 
                                    fun conv x y = (map (fn x' => ARRAY (map (fn v => NUMBER (REAL v)) x')) 
                                                   (tab (x,y) ws), drop (x*y) ws)
                                  in
                                    case shapeVal of
                                      (ARRAY [NUMBER (INTEGER x), NUMBER (INTEGER y)]) => conv y x 
                                    | (ARRAY [NUMBER (INTEGER x)])                     => conv x 1
                                    | _ => error "Error in obtaining shape"
                                  end 
          in 
              (OBJECT [name, ("shape", ARRAY shapeVal')],ws')
          end
        | updateWeights _ _ = error "Error in parsing shapes"
      in 
          fold_map updateWeights (getWeightShapes wm) weights |> fst |> ARRAY
      end
  
  
  fun transform_json parent json = 
      let
          val wm = (nj_update (updateWeightsManifest parent) "weightsManifest" json)
      in
          wm
      end

  fun def_nn_json defN strT numT json lthy = 
      let 
        val thy = Proof_Context.theory_of lthy
        val verbose =  Config.get_global thy json_verbose
        val json_term = Nano_Json_Type.term_of_json verbose strT numT json
      in
        (Nano_Json_Parser_Isar.make_const_def (Binding.name(defN), json_term)) lthy
        |> snd
      end 
fun get_weights layer json = case nj_filterp_obj (["weightsManifest", "name"], SOME (STRING (layer^"/kernel"))) json of 
                             [(_, Nano_Json_Type.OBJECT weights)] => (case (List.filter (fn e => fst e = "shape") weights) of 
                                                                      [(_,w)] => SOME w
                                                                     | _ => NONE) 
                           | _ => NONE
fun get_bias layer json = case nj_filterp_obj (["weightsManifest", "name"], SOME (STRING (layer^"/bias"))) json of 
                             [(_, Nano_Json_Type.OBJECT weights)] => (case (List.filter (fn e => fst e = "shape") weights) of 
                                                                      [(_,w)] => SOME w
                                                                     | _ => NONE) 
                           | _ => NONE

fun get_layer json = case nj_filterp ["modelTopology", "model_config", "config", "layers"] json of
                       [(_,Nano_Json_Type.ARRAY v)] => SOME v
                     | _       => NONE

open TensorFlow_Type

fun convert_layer json layer_js = let
                         val name = case Option.mapPartial nj_string_of (nj_first_value_of "name" layer_js) of
                                         SOME s => s
                                       | NONE => error "Layer name not found."
                         val inputs = (case nj_first_value_of "batch_input_shape" layer_js of 
                                            SOME (ARRAY [NULL, NUMBER (INTEGER n)]) => SOME n
                                          | SOME _ => error "Batch input shape not supported."
                                          | NONE => NONE
                         )
                         val activation_opt = Option.mapPartial nj_string_of 
                                              (case nj_first_value_ofp ["config","activation","config","activation"]  layer_js of 
                                                 SOME j => SOME j
                                               | NONE => nj_first_value_of "activation" layer_js)
                         val activation =  (case activation_opt of 
                                               NONE => NONE
                                             | SOME "linear" => SOME Linear
                                             | SOME "softsign" => SOME Softsign
                                             | SOME "sign" => SOME Sign
                                             | SOME "binary_step" => SOME BinaryStep
                                             | SOME "sigmoid" => SOME Sigmoid                                         
                                             | SOME "swish" => SOME Swish
                                             | SOME "tanh" => SOME Tanh
                                             | SOME "gelu" => SOME Gelu
                                             | SOME "relu" => SOME Relu
                                             | SOME "softplus" => SOME Softplus
                                             | SOME "elu" => SOME Elu
                                             | SOME "selu" => SOME Selu
                                             | SOME "exponential" => SOME Exponential
                                             | SOME "hard_sigmoid" => SOME Hard_sigmoid
                                             | SOME "softmax" => SOME Softmax
                                             | SOME "softmax_taylor" => SOME Softmax_taylor
                                             | SOME "sigmoid_taylor" => SOME Sigmoid_taylor
                                             | SOME s => error ("Activation type not supported: "^s))

                         val layer_type = (case Option.mapPartial nj_string_of (nj_first_value_of "class_name" layer_js) of 
                                                NONE => error "Layer type not found."
                                              | SOME "InputLayer" => InputLayer 
                                              | SOME "Dense" => Dense 
                                              | SOME s => error ("Layer type not supported: "^s))
                         val units = if layer_type = InputLayer 
                                     then (case inputs of SOME i => i | NONE => error "Input layer without inputs.")
                                     else  (case Option.mapPartial nj_integer_of (nj_first_value_of "units" layer_js) of 
                                                 NONE => error "Units for internal layer not specified" 
                                               | SOME i => i)
                         fun conv_real_array (ARRAY a) = map (fn v => (case nj_real_of v of 
                                                               SOME r => r 
                                                             | NONE => error "Unkown format in real array conversion.")) a 
                           | conv_real_array _         = error "Unknown format in real array conversion."
                         val bias = (case get_bias name json of
                                          NONE => []  
                                        | SOME (ARRAY a) => map conv_real_array a |> List.concat
                                        | SOME _ => error "Bias format not supported.")
  
                         val weights = (case get_weights name json of
                                          NONE => []
                                        | SOME (ARRAY a) => map conv_real_array a
                                        | SOME _ => error "Weight format not supported.")   
                         in 
                           ({ name = name, units = units, activation = activation, 
                            layer_type=layer_type, bias = bias, weights=weights}):(IEEEReal.decimal_approx layer)
                        end 

  fun convert_layers json = case Option.mapPartial nj_string_of 
                               (nj_first_value_ofp ["modelTopology", "model_config", "class_name"] json) of 
                            SOME "Sequential" => (case get_layer json of 
                                                      SOME lj => let 
                                                                  val l = (map (convert_layer json) lj)
                                                                in  
                                                                  if l = [] then [] else 
                                                                  l@[{name="OUTPUT",
                                                                      units= #units (List.hd (rev l)),
                                                                      activation=NONE,
                                                                      layer_type=OutputLayer,
                                                                      bias=[],
                                                                      weights=[]}]
                                                                end 
                                                     | NONE => error "Layer configuration not found.")
                         |  SOME s => error ("Layer configuration not supported"^s)
                         |  NONE => error "Layer configuration not found."


end
