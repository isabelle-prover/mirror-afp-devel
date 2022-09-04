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

structure Nano_Json_Type : NANO_JSON_TYPE = struct
    datatype NUMBER = INTEGER of int | REAL of IEEEReal.decimal_approx
    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of NUMBER
                  | STRING of string
                  | BOOL of bool
                  | NULL


    fun ieee_real_to_rat_approx verbose (rat:IEEEReal.decimal_approx) = let
           val _ = if verbose 
                   then warning ("Conversion of real numbers is not JSON compliant.") 
                   else ()
           fun pow (_, 0) = 1  
             | pow (x, n) = if n mod 2 = 0 then pow (x*x, n div 2)  
                                           else x * pow (x*x, n div 2); 
           fun rat_of_dec rat = let
                 val sign = #sign rat
                 val digits = #digits rat
                 val exp = #exp rat
                 fun numerator_of _ [] = 0
                   | numerator_of c (x::xs) = x*pow(10,c) + (numerator_of (c+1) xs)
                 val numerator_abs = numerator_of 0 (rev digits)
                 val denominator = pow(10, (List.length digits - exp))  
               in
                 (if sign then ~ numerator_abs else numerator_abs, denominator)
               end
        in
          case #class rat of      
             IEEEReal.ZERO      => (0,0)
           | IEEEReal.SUBNORMAL => rat_of_dec rat
           | IEEEReal.NORMAL    => rat_of_dec rat 
           | IEEEReal.INF => error "Real is INF, not yet supported."
           | IEEEReal.NAN => error "Real is NaN, not yet supported."
        end


    fun mk_funT typ = Type("fun", typ)

    fun divide_classC realT = Const(@{const_name Rings.divide_class.divide} , mk_funT [realT, mk_funT [realT, realT]])
    fun mk_divide realT t1 t2 = (divide_classC realT) $ t1 $ t2
    fun mk_real_num realT i = HOLogic.mk_number realT i
    fun mk_real realT (p,q) = if q = 1 then mk_real_num realT p 
                                       else if (p = 0 andalso q = 0) then mk_real_num realT 0  
                                            else mk_divide realT (mk_real_num realT p) (mk_real_num realT q)
    fun term_of_real verbose  r = (mk_real HOLogic.realT (ieee_real_to_rat_approx verbose r))

    fun dest_real (Const(@{const_name Rings.divide_class.divide} , _)$a$b) = 
                                      Real.toDecimal(Real.fromInt(HOLogic.dest_number a |> snd)
                                                       / Real.fromInt(HOLogic.dest_number b |> snd))
      | dest_real t = Real.toDecimal (Real.fromInt (HOLogic.dest_number t |> snd))

    fun json_real_of_term r   = (NUMBER (REAL (dest_real r)))

    fun json_int_of_term i    =   (NUMBER (INTEGER (snd (HOLogic.dest_number i)))) 
    fun json_string_of_term s = STRING (HOLogic.dest_string s)
    fun json_string_literal_of_term s = STRING (HOLogic.dest_literal s)

    fun mk_jsonT stringT numberT = Type(@{type_name "json"},[stringT, numberT])
    fun mk_json_object stringT numberT = Const(@{const_name OBJECT}, mk_funT [
        HOLogic.listT (HOLogic.mk_prodT (stringT, mk_jsonT stringT numberT)), mk_jsonT stringT numberT])

    fun mk_str (@{typ "string"}) s         = HOLogic.mk_string s
      | mk_str (@{typ "String.literal"}) s = HOLogic.mk_literal s
      | mk_str _ _ = error "String type not supported"

    fun mk_json_array stringT numberT = Const(@{const_name "ARRAY"}, mk_funT [HOLogic.listT (mk_jsonT stringT numberT), mk_jsonT stringT numberT])
    fun mk_json_number stringT numberT = Const(@{const_name "NUMBER"}, mk_funT [numberT, mk_jsonT stringT numberT])
    fun mk_json_string stringT numberT = Const(@{const_name "STRING"}, mk_funT [stringT, mk_jsonT stringT numberT])
    fun mk_json_bool stringT numberT = Const(@{const_name "BOOL"}, mk_funT [@{typ bool}, mk_jsonT stringT numberT])
    fun mk_json_null stringT numberT = Const(@{const_name "NULL"}, mk_jsonT stringT numberT)

    fun fix_tilde_sign s =  String.implode (map (fn #"~" => #"-" | c => c)
                                     (String.explode s))


    fun mk_number _  @{typ "int"} (INTEGER i)            = HOLogic.mk_number @{typ "int"} i
      | mk_number _  @{typ "nat"} (INTEGER i)            = if i >= 0 then HOLogic.mk_number @{typ "nat"} i
                                                                else error "mk_number: JSON contains negative number and target is nat."
      | mk_number _ @{typ "int"} (REAL r)             = error (String.concat["mk_number: JSON contains real number and target is nat or int: ", 
     IEEEReal.toString  r])
      | mk_number verbose (Type("Real.real",[])) (INTEGER i) = term_of_real verbose (Real.toDecimal (Real.fromInt i))
      | mk_number verbose (Type("Real.real",[])) (REAL r)    = term_of_real verbose r

      | mk_number _ @{typ "string"} n         = (case n of 
                                                 (INTEGER i) => Int.toString i |> fix_tilde_sign |> HOLogic.mk_string
                                               | (REAL r)    => IEEEReal.toString r |> fix_tilde_sign |> HOLogic.mk_string 
                                                 ) 
      | mk_number _ @{typ "String.literal"} n  = (case n of 
                                                 (INTEGER i) => HOLogic.mk_literal (Int.toString i |> fix_tilde_sign)
                                               | (REAL r)    => HOLogic.mk_literal (IEEEReal.toString r |> fix_tilde_sign) 
                                                 )

      | mk_number _ _ _ = error "mk_number: type not supported"

    fun dest_funT (Type ("fun", [d,_])) = d
      | dest_funT _                     = error "Unkown ERROR in dest_funT."

    fun json_of_number t n = case dest_funT t of 
                               (@{typ "int"}) => json_int_of_term n
                             | (@{typ "nat"}) => json_int_of_term n
                             | (Type("Real.real" , [])) => json_real_of_term n
                             | (@{typ "string"}) => json_string_of_term n
                             | (@{typ "String.literal"}) => json_string_literal_of_term n 
                             | (Type(x,_))  => error (String.concat["ERROR  in json_of_number: ", x] )
                             | _  => error "Unknown ERROR  in json_of_number."
                          
    fun json_of_string t s = 
                            case dest_funT t of 
                               (@{typ "string"}) => json_string_of_term s
                             | (@{typ "String.literal"}) => json_string_literal_of_term s 
                             | (Type(x,_))  => error (String.concat["ERROR  in json_of_string: ", x] )
                             | _  => error "Unknown ERROR  in json_of_string."

                                    
    fun term_of_json verbose strT numT (OBJECT l) = mk_json_object strT numT 
                                  $(HOLogic.mk_list ((HOLogic.mk_prodT (strT, mk_jsonT strT numT )))  
                                    (map (fn (s,j) => HOLogic.mk_tuple[mk_str strT s, term_of_json verbose strT numT j]) l))
      | term_of_json verbose strT numT (ARRAY l)  = mk_json_array strT numT 
                                  $(HOLogic.mk_list ( mk_jsonT strT numT) (map (term_of_json verbose  strT numT) l))
      | term_of_json verbose strT numT (NUMBER n) = (mk_json_number strT numT)$(mk_number verbose numT n)  
      | term_of_json _ strT numT (STRING s) = (mk_json_string strT numT)$(mk_str strT s)
      | term_of_json _  strT numT (BOOL v)   = (mk_json_bool strT numT)$(if v then @{const "True"} else @{const "False"}) 
      | term_of_json _  strT numT  (NULL)    = mk_json_null strT numT 

fun string_of_typ (Type (s, _))     = s
  | string_of_typ (TFree (s, _))    = s
  | string_of_typ (TVar ((s,_), _)) = s;

    fun json_of_term t = let
        fun dest_key_value [string, json] = ((HOLogic.dest_string string, json_of json)
                                            handle TERM _ => (HOLogic.dest_literal string, json_of json))
          | dest_key_value _              = error "dest_key_value: not a key-value pair." 
        and json_of (Const(@{const_name "OBJECT"}, _) $ l) = OBJECT (map (dest_key_value o HOLogic.strip_tuple) (HOLogic.dest_list l))
          | json_of (Const(@{const_name "ARRAY"}, _)  $ l) = ARRAY (map json_of (HOLogic.dest_list l))
          | json_of (Const(@{const_name "NUMBER"}, numT) $ n ) = json_of_number numT n 
          | json_of (Const(@{const_name "STRING"}, stringT) $ s) = json_of_string stringT s 
          | json_of (Const(@{const_name "BOOL"}, _) $ @{const "True"}) = BOOL true
          | json_of (Const(@{const_name "BOOL"}, _) $ @{const "False"}) = BOOL false
          | json_of (Const(@{const_name "NULL"}, _))  = NULL
          | json_of t = error (String.concat ["Term not supported in json_of_term: ", string_of_typ (type_of t)])



    in
        case type_of t of 
          Type("Nano_JSON.json",[_,_]) => json_of t 
          | _ => error (String.concat ["Term not of type json: ", string_of_typ (type_of t)])
    end
end
