(***********************************************************************************
 * Copyright (c) 2019-2022 Achim D. Brucker
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

structure Nano_Json_Query:NANO_JSON_QUERY  = struct
open Nano_Json_Type


fun nj_string_of (STRING s) = SOME s
  | nj_string_of _          = NONE
fun nj_string_of' _ (STRING s) = s
  | nj_string_of' s _          = s

fun nj_integer_of (NUMBER (INTEGER i)) = SOME i
  | nj_integer_of _                    = NONE
fun nj_integer_of' _ (NUMBER (INTEGER i)) = i
  | nj_integer_of' i _                    = i

fun nj_real_of (NUMBER (REAL r)) = SOME r
  | nj_real_of _                 = NONE
fun nj_real_of' _ (NUMBER (REAL r)) = r
  | nj_real_of' r _                 = r

fun nj_bool_of (BOOL b) = SOME b
  | nj_bool_of _           = NONE
fun nj_bool_of' _ (BOOL b) = b
  | nj_bool_of' b _        = b


fun nj_filter key json =
    let 
        fun nj_filter' key (prfx, OBJECT json) =  ((map (fn  (k,v) => (prfx@[k],v)) (filter (fn (k,_) =>  key = k) json) )
                                                 @(List.concat (map (nj_filter' key) (map (fn (k,v) => (prfx@[k],v)) json)))) 
          | nj_filter' key (prfx, ARRAY json) = (List.concat (map (nj_filter' key) (map (fn v => (prfx,v)) json)))
          | nj_filter' _ (_, NUMBER _) = []
          | nj_filter' _ (_, STRING _) = []
          | nj_filter' _ (_, BOOL _) = []
          | nj_filter' _ (_,NULL) = []
    in 
        nj_filter' key ([],json)
    end

fun nj_filterp []  _    = []
  | nj_filterp key json = nj_filter (List.last key) json |> filter (fn e => fst e = key)


fun nj_first_value_of key json = case nj_filter key json of [] => NONE
                                    | (j::_) => SOME (snd j) 

fun nj_first_value_ofp key json = case nj_filterp key json of [] => NONE
                                    | (j::_) => SOME (snd j) 

fun  nj_filter_obj kv json = 
    let 
        fun nj_filter_obj' (key, value) (prfx, OBJECT json) =  if List.exists (fn e => key = fst e andalso (value = NONE orelse value = SOME (snd e))) json 
                                                      then [(prfx@[key],OBJECT json)] 
                                                      else (List.concat (map (nj_filter_obj' (key, value)) (map (fn (k,v) => (prfx@[k],v)) json))) 
          | nj_filter_obj' kv (prfx, ARRAY json) = (List.concat (map (nj_filter_obj' kv) (map (fn v => (prfx,v)) json)))
          | nj_filter_obj' _ (_, NUMBER _) = []
          | nj_filter_obj' _ (_, STRING _) = []
          | nj_filter_obj' _ (_, BOOL _) = []
          | nj_filter_obj' _ (_,NULL) = []
    in 
        nj_filter_obj' kv ([],json)
    end

fun nj_filterp_obj ([],_)  _    = []
  | nj_filterp_obj (key, value) json = nj_filter_obj (List.last key, value) json |> filter (fn e => fst e = key)


fun nj_update f key (OBJECT kjson) =  OBJECT (map (fn (k,json) => if k = key then (k, f json) else (k, nj_update f key json)) kjson)
  | nj_update f key (ARRAY json) = ARRAY (map (nj_update f key) json)
  | nj_update _ _ (NUMBER n) = NUMBER n
  | nj_update _ _ (STRING s) = STRING s
  | nj_update _ _ (BOOL b) = BOOL b
  | nj_update _ _ NULL = NULL

fun nj_updatep _ [] json = json 
  | nj_updatep f  (p::path) (OBJECT kjson) =  OBJECT (map (fn (k,json) => if [k] = (p::path) 
                                                                   then (k, f json) 
                                                                   else (k, nj_updatep f path json)) kjson)
  | nj_updatep f path (ARRAY json) = ARRAY (map (nj_updatep f path) json)
  | nj_updatep _ _ (NUMBER n) = NUMBER n
  | nj_updatep _ _ (STRING s) = STRING s
  | nj_updatep _ _ (BOOL b) = BOOL b
  | nj_updatep _ _ NULL = NULL

fun nj_convert f key (OBJECT json) =  List.concat ((map (fn (k,json) => if k = key then [f json] else nj_convert f key json)) json)
  | nj_convert f key (ARRAY json) = List.concat (map (nj_convert f key) json)
  | nj_convert f _ (NUMBER n) = [f (NUMBER n)]
  | nj_convert f _ (STRING s) = [f (STRING s)]
  | nj_convert f _ (BOOL b) = [f (BOOL b)]
  | nj_convert f _ NULL = [f NULL]

end
