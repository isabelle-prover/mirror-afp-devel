(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure MString :> sig
  eqtype t
  val mk : string -> t
  val dest : t -> string
  val destPP : t -> string
  val ord : t * t -> order
  val eq : t * t -> bool
end = struct
  type t = string
  fun mk s = s
  fun dest s = s
  fun destPP s = "MV(" ^ s ^ ")"
  val ord = string_ord
  val eq = (op =)
end

val _ = ML_system_pp (fn _ => fn _ => fn t => ML_Pretty.str (MString.destPP t));

structure MSymTab = Table(struct
  type key = MString.t
  val ord = MString.ord
end)

structure XMSymTab = Table (struct
  type key = MString.t * string option
  val ord = prod_ord MString.ord (option_ord fast_string_ord) 
end)

structure CNameTab = Table
  (struct type key = {varname : MString.t,
                      fnname : string option}
          fun ord ({varname = vn1, fnname = fn1},
                   {varname = vn2, fnname = fn2}) =
              prod_ord (option_ord string_ord) (MString.ord)
                           ((fn1, vn1), (fn2, vn2))
   end)

datatype variable_kind = Global | Local | Parameter of int


fun variable_kind_ord (Parameter i1, Parameter i2) = int_ord (i1, i2)
  | variable_kind_ord (Parameter _ , Global  ) = LESS
  | variable_kind_ord (Parameter _ , Local  ) = LESS
  | variable_kind_ord (Global      , Parameter _ ) = GREATER
  | variable_kind_ord (Global      , Global  ) = EQUAL
  | variable_kind_ord (Global      , Local  ) = LESS
  | variable_kind_ord (Local       , Parameter _ ) = GREATER
  | variable_kind_ord (Local       , Global  ) = GREATER
  | variable_kind_ord (Local       , Local  ) = EQUAL

fun is_global_variable (Global) = true
  | is_global_variable  _ = false
  
fun is_local (Local) = true
  | is_local _ = false

fun is_parameter (Parameter _) = true
  | is_parameter _ = false

  