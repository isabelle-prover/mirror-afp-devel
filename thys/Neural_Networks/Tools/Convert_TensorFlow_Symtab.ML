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

structure Convert_TensorFlow_Symtab:CONVERT_TENSORFLOW_SYMTAB = struct
  type targetT=string 
  type nn_encoderT = bstring -> typ -> typ -> Nano_Json_Type.json -> local_theory -> local_theory
  type nn_encoder_tabT = (targetT * nn_encoderT) Symtab.table

  fun eq' (a, a') = (fst a) = (fst a')
  fun merge_trac_tab (tab,tab') = Symtab.merge eq' (tab,tab')
  structure NN_Encoder_Data = Theory_Data
  (
    type T = nn_encoder_tabT
    val empty  = Symtab.empty:nn_encoder_tabT
    fun merge(t1,t2)  = merge_trac_tab (t1, t2)
  );
  fun update  p thy = ((NN_Encoder_Data.map (fn tab => Symtab.update (fst p, p) tab) thy))
  fun lookup name thy = (Symtab.lookup (NN_Encoder_Data.get thy) name,thy)

  val exists_target = Symtab.defined o NN_Encoder_Data.get;
  val lookup_nn_encoder = Symtab.lookup o NN_Encoder_Data.get;
  
  fun assert_target thy target_name =
    if exists_target thy target_name
    then target_name
    else error ("Unknown encoding for TensorFlow models: " ^ quote target_name);
  
  fun allocate_target target_name encoder thy =
    let
      val _ = if exists_target thy target_name
        then error ("Attempt to overwrite existing encoding for TensorFlow modles: " ^ quote target_name)
        else ();
    in
      thy
      |> (NN_Encoder_Data.map o Symtab.update) (target_name, (target_name,encoder))
    end;
  
  fun add_encoding (target_name, encoder) =
    allocate_target target_name encoder
end 
