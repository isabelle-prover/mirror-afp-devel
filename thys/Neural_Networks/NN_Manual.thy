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

chapter\<open>Reference Manual (thy)\<close>

theory 
  NN_Manual
imports 
  NN_Main
begin
text\<open>\label{ch:manual}\<close>

section\<open>Importing Neural Networks and Data\<close>

paragraph\<open>@{command "import_data_file"}.\<close> 
text\<open> For importing test or training data, we provide the following command:
 \<^rail>\<open> @@{command "import_data_file"} data_filename 'defining' data_def \<close> 
where \emph{data-filename} is the path (file name) of the data file that should be read and  
\<^emph>\<open>data-def\<close> is the name the HOL definition representing the data 
is bound to. The data file should be a simple two-dimensional array of real numbers as, e.g., 
produced by NumPy's \<^cite>\<open>"harris.ea:array:2020"\<close> \<^verbatim>\<open>savetxt\<close> command: 
\begin{python}
import numpy as np
training_data = np.array([[0,0],[0,1],[1,0],[1,1]], "float32")
np.savetxt('training_data.out', training_data)
\end{python}
For further information, please see 
\<^url>\<open>https://numpy.org/doc/stable/reference/generated/numpy.savetxt.html\<close>. 
\<close>

paragraph\<open>@{command "import_TensorFlow"}.\<close> 
text\<open> For importing trained neural networks, we provide the following command:
 \<^rail>\<open> @@{command "import_TensorFlow"} name 'file' data_filename 'as' 
       ('json' | 'digraph' | 'digraph_single' | 'seq_layer')\<close> 
The input should be in JSON \<^cite>\<open>"ecma:json:2017"\<close> format with the weights stored
in a separate file. This format is used by TensorFlow.js~\<^cite>\<open>"smilkov.ea:tensorflowjs:2019"\<close>
and also supported by the corresponding Python module. For example:
\begin{python}
import tensorflowjs as tfjs
import numpy as np
import keras
from keras.models import Sequential 
from keras.layers import Dense

training_data = np.array([[0,0],[0,1],[1,0],[1,1]], "float32")
target_data = np.array([[1],[0],[0],[0]], "float32")

model = Sequential()
model.add(Dense(1, activation='hard_sigmoid'))
model.compile(loss='mean_squared_error', optimizer='adam', metrics=['binary_accuracy'])
model.fit(training_data, target_data, epochs=7500, verbose=0)

# safe trained model as JSON (with external file for weights)
tfjs.converters.save_keras_model(model, ".")
\end{python}
\<close>


paragraph\<open>Configuration.\<close> text \<open>We provide several configuration attributes:
\<^item> The attribute @{attribute "nn_proof_mode"} (default @{term "nbe"} configures if proofs during 
  the import of neural networks (i.e., @{command "import_TensorFlow"}) should
  \<^item> not generate any proofs (@{term "skip"} 
  \<^item> generate proofs axiomatically, without actually proving them (@{term "sorry"})
  \<^item> use code generation (i.e., the proof method @{method "eval"}) if possible (@{term "eval"})
  \<^item> use normalization by evaluation (i.e., the proof method @{method "normalization"}) if possible (@{term "nbe"})
  \<^item> avoid using the code generator (@{term "safe"})

  While, in many scenarios, the proof method @{method "eval"}  is much faster than  the
  alternative approaches, its safety relies on the configuration of the code generator. A more 
  detailed discussion can be found in Section 5 of \<^cite>\<open>"isabelle:codegen:2021"\<close>.
\<close>

section\<open>Proof Methods\<close>

text\<open>Currently, we provide two domain-specific proof methods: 
\<^item> The method @{method "predict_layer"} is, in its essence, a simplification using the 
  theorem set @{text "nn_layer"}, which is configured automatically by the import of 
  layer-based models.
\<^item> @{method "forced_approximation"} is a method mainly for debugging and experimentation 
  that repeats the application of the @{method "approximation"}. 
\<close>

end
