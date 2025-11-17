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

section\<open>Infrastructure for Importing TensorFlow Models\<close>

theory
    TensorFlow_Import 
imports 
  Complex_Main
  Nano_JSON.Nano_JSON_Main
keywords
      "import_TensorFlow" :: thy_decl
  and "as"::quasi_command 
begin

text\<open>
  In this theory, we implement the core infrastructure for importing models from 
  TensorFlow.js~\<^cite>\<open>"smilkov.ea:tensorflowjs:2019"\<close>. This common infrastructure provided a generic 
  parser for the JSON~\<^cite>\<open>"ecma:json:2017" and "ietf:rfc8259-json:2017"\<close> representation of 
  neural networks that can be exported from TensorFlow.js. Actually, TensorFlow.js~\<^cite>\<open>"smilkov.ea:tensorflowjs:2019"\<close> exports the structure of a neural network (and its configuration 
  used for training the neural network) as JSON file. The weights and biases are stored
  in a binary file to which the JSON file refers to (see \<^url>\<open>https://www.tensorflow.org/js/guide/save_load\<close> 
  and \<^url>\<open>https://github.com/tensorflow/tfjs/issues/386\<close> for more details). 

  This theory implements an infrastructure for importing this format, including the decoding 
  of the binary format storing the weights and biases, into Isabelle/HOL. At its core, the
  infrastructure provides a parser for the format used by TensorFlow.js and a mechanism 
  for hooking datatype packages into it that provide specific encodings into Isabelle/HOL.
  As a first example, this theory provides a datatype package that provides a JSON-like 
  encoding of neural networks (including their weights and biases) using Nano 
  JSON~\<^cite>\<open>"brucker:nano-json:2022"\<close>. The implementation used the JSON infrastructure 
  provided by the AFP entry Nano JSON~\<^cite>\<open>"brucker:nano-json:2022"\<close>. 
\<close>	

subsection\<open>Encoder\<close>

ML\<open>
signature TENSORFLOW_TYPE = sig
  datatype activationT = Linear | BinaryStep | Softsign | Sign | Sigmoid | Swish | Tanh | Relu | Gelu 
                       | GRelu | Softplus | Elu | Selu | Exponential | Hard_sigmoid 
                       | Softmax | Softmax_taylor | Sigmoid_taylor
    datatype layerT = Dense | InputLayer | OutputLayer
    type 'a layer = {
                       activation: activationT option, 
                       bias: 'a list, units: int, 
                       layer_type: layerT, 
                       name: string, 
                       weights: 'a list list
                    }
end
\<close>
ML_file\<open>Tools/TensorFlow_Type.ML\<close>

text\<open>
  The ML structure @{ML_structure  \<open>TensorFlow_Type:TENSORFLOW_TYPE\<close> } provides the core datatypes
  required for the TensorFlow.js import: 
  \<^item> @{ML_type \<open>TensorFlow_Type.activationT\<close>}: this datatype enumerates the currently supported
    activation functions (see~\autoref{tab:tensorflow-activation} for a mapping of their 
    names used by our formalization).
  \<^item> @{ML_type \<open>TensorFlow_Type.layerT\<close>}: This datatype enumerates the currently supported layer types 
    of TensorFlow. 
  \<^item> @{ML_type \<open>'a TensorFlow_Type.layer\<close>}: This record captures the properties of a layer that are 
    extracted from the JSON provided by TensorFlow.js.
\<close>

ML\<open>
signature TENSORFLOW_JSON = sig
  val transform_json: Path.T -> Nano_Json_Type.json -> Nano_Json_Type.json
  val def_nn_json:  bstring  -> typ -> typ -> Nano_Json_Type.json 
                   -> local_theory -> local_theory
  val convert_layers: Nano_Json_Type.json 
                      -> IEEEReal.decimal_approx TensorFlow_Type.layer list
end
\<close>
ML_file\<open>Tools/TensorFlow_Json.ML\<close>
text\<open>
  TensorFlow.js does export a neural network in a format consisting out of a JSON file and and a 
  binary file:
    \<^item> the JSON file stores the overall structure of the neural network and the configuration used for 
      training the neural network. Notably, the JSON file does neither contain the biases nor the weights.
    \<^item> a binary file containing the biases and weights. 
\<close>
text\<open>
  The ML structure @{ML_structure \<open>TensorFlow_Json:TENSORFLOW_JSON\<close> } provides, foremost, a function
  for parsing the JSON exported neural network in the format supported by TensorFlow. This 
  function, @{ML \<open>TensorFlow_Json.transform_json\<close>}, takes two arguments
    \<^item> the directory (path) of the TensorFlow.js export, i.e., the directory in which both the 
      JSON file and the binary file containing the biases and weights are stored.
    \<^item> the parsed JSON file (the actual JSON parsing is done using @{ML "Nano_Json_Parser.json_of_string"},
      which is provided by Nano JSON~\<^cite>\<open>"brucker:nano-json:2022"\<close>.
\<close>
text\<open>
  The function @{ML \<open>TensorFlow_Json.transform_json\<close>} parses the binary file containing the biases
  and weights and transforms the input JSON such that the resulting JSON representation includes
  the biases and weights. In more detail, the JSON file exported by TensorFlow.js stores the
  biases and weights as follows:
\begin{json}  
 "weightsManifest": [{
      "paths": [ "group1-shard1of1.bin" ],
      "weights": [
        {
          "name": "dense/kernel",
          "shape": [2, 1],
          "dtype": "float32"
        }, {
          "name": "dense/bias",
          "shape": [1],
          "dtype": "float32"
        }
      ]
  }]
\end{json}
  Instead of storing the biases and weights in the JSON file, the exported JSON only contains 
  the type information (here: \inlinejson|float32|) refers to an external file (here: 
  \inlinejson|group1-shard1of1.bin| that stores the actual value. In our example, this 
  external file has  a size of 12 bytes, storing three 32 Bit floating point numbers (encoding 
  as IEEE floating point using a Little Endian encoding. The order of the biases and weights
  corresponds to the order and shape of their references in the original JSON file. In our 
  example, the function @{ML \<open>TensorFlow_Json.transform_json\<close>} results in the following transformed
  \inlinejson{weightsManifest}:
\begin{json}
 "weightsManifest":[{
   "name":"dense/kernel",
   "shape":[
             [-0.47318925857543945E1],
             [-0.4610690593719482E1]
           ]
  }, 
  {
   "name":"dense/bias",
   "shape":[[0.22737088203430176E1]]
  }]
\end{json}

Moreover, the ML structure @{ML_structure  \<open>TensorFlow_Json:TENSORFLOW_JSON\<close> } also provides an 
ML for converting a (transformed) JSON representation into a more abstract representation based on 
a sequence of layers:  @{ML \<open>TensorFlow_Json.convert_layers\<close>}. This function uses the datatypes 
provided by @{ML_structure \<open>TensorFlow_Type:TENSORFLOW_TYPE\<close>}.

Finally, @{ML_structure  \<open>TensorFlow_Json:TENSORFLOW_JSON\<close> } provides  
@{ML \<open>TensorFlow_Json.def_nn_json\<close>}, which is a simple wrapper around the datatype package provided 
by Nano JSON generating a formal JSON representation of the neural network imported from TensorFlow.js
in HOL.
\<close>


ML\<open>
signature CONVERT_TENSORFLOW_SYMTAB = sig
  structure NN_Encoder_Data: THEORY_DATA
  eqtype targetT
  type nn_encoderT = bstring-> typ -> typ -> Nano_Json_Type.json -> local_theory -> local_theory
  val add_encoding: Symtab.key * nn_encoderT -> theory -> theory
  val assert_target: theory -> Symtab.key -> Symtab.key
  val lookup_nn_encoder: theory -> Symtab.key -> (targetT * nn_encoderT) option
end
\<close>
ML_file\<open>Tools/Convert_TensorFlow_Symtab.ML\<close>

text\<open>
  We use the mechanism of attaching a symtab to theories to provide a dynamic registration 
  mechanism for different datatype packages that encode the JSON representation in a formal 
  model. The  ML structure @{ML_structure  \<open>Convert_TensorFlow_Symtab:CONVERT_TENSORFLOW_SYMTAB\<close> }
  defines the type for encoder functions (i.e., @{ML_type \<open>Convert_TensorFlow_Symtab.nn_encoderT\<close>} and 
  it provides methods for adding a new encoding (@{ML \<open>Convert_TensorFlow_Symtab.add_encoding\<close>}, 
  checking if a encoder for a given target encoding exists (@{ML \<open>Convert_TensorFlow_Symtab.assert_target\<close>},
  and for the lookup of an encoder ((@{ML \<open>Convert_TensorFlow_Symtab.lookup_nn_encoder\<close>}). The 
  symtab is registered as follows:
\<close>
ML\<open>val _ = Theory.setup 
           (Convert_TensorFlow_Symtab.add_encoding 
               ("json", TensorFlow_Json.def_nn_json))
\<close>

ML\<open>
local
    fun import_and_define_nn defN tokenFile modeOption lthy =
        let
            val thy = Proof_Context.theory_of lthy

            val ({src_path, lines, ...}:Token.file) = tokenFile
            val path = if (Path.is_absolute src_path) 
                       then src_path 
                       else Path.append (Resources.master_directory thy) src_path
            val mode = case modeOption of 
                         SOME m => m 
                       | NONE   => "json"
            val encoder = let 
                            val _  = Convert_TensorFlow_Symtab.assert_target thy mode
                          in 
                            case Convert_TensorFlow_Symtab.lookup_nn_encoder thy mode
                              of NONE => error "Encoder not found" 
                               | SOME e => snd e     
                          end
            val strT = Nano_Json_Parser.stringT thy 
            val numT = Nano_Json_Parser.numT thy
            val tf_json = Nano_Json_Parser.json_of_string (String.concat lines)
            val json = TensorFlow_Json.transform_json (Path.dir path)  tf_json
        in 
          encoder defN strT numT json lthy
        end
    
in
val _ = Outer_Syntax.command \<^command_keyword>\<open>import_TensorFlow\<close> 
        "Import trained neural network from a TensorFlow.js JSON file."
        ((Parse.name -- \<^keyword>\<open>file\<close> -- Resources.parse_file -- Scan.option (\<^keyword>\<open>as\<close> |-- Parse.!!! (Parse.name))) >> 
         (fn (((name,_),get_file),mode_option) =>
           Toplevel.theory (fn thy => let val file = get_file thy;
           in Named_Target.theory_map (import_and_define_nn name file mode_option) thy end)
        ))
end
\<close>
                                                  
text\<open>
  Lastly, we bind our encoder to a new top-level command: @{command import_TensorFlow} and prepare
  its default configuration: \<close>
declare[[JSON_num_type = real, JSON_string_type = string, JSON_verbose = false]]


subsection\<open>Example Import\<close>

text\<open>
  In the following, we briefly demonstrate the use of the TensorFlow.js import.
\<close>

import_TensorFlow compass file "examples/compass/model/model.json" as json

JSON_export compass file nor_model_transformed

text\<open>
This generated the definition @{const \<open>compass\<close>} with the following definition:
@{thm [display] "compass_def"}
\<close>

end
