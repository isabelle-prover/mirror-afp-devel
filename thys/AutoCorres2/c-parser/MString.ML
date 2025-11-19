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

datatype more_info = MungedVar of {munge : MString.t, owned_by : string option, fname : string option, init : bool, global: bool}
                   | EnumC
                   | FunctionName

fun map_init f {munge, owned_by, fname, init, global} = 
  {munge = munge, owned_by = owned_by, fname = fname, init= f init, global=global}

fun map_munged_var f (MungedVar x) = (MungedVar (f x))
  | map_munged_var _ x = x

fun dest_munged_var_info (MungedVar {fname=SOME n, ...}) = SOME n
  | dest_munged_var_info _ = NONE

fun get_init (MungedVar {init, ...} ) = SOME init
  | get_init _ = NONE 

fun munged_var_ord ({munge = m1, owned_by = o1, fname = f1, init = i1, global = g1}, 
     {munge = m2, owned_by = o2, fname = f2, init = i2, global = g2}) =
   (prod_ord MString.ord (prod_ord (option_ord string_ord) (prod_ord (option_ord string_ord) (prod_ord bool_ord bool_ord)))) 
     ((m1, (o1, (f1, (i1, g1)))), (m2, (o2, (f2, (i2, g2)))))

fun more_info_ord (x, y) = 
  case (x, y) of
     (FunctionName, FunctionName) => EQUAL
   | (EnumC, EnumC) => EQUAL
   | (MungedVar m1, MungedVar m2) => munged_var_ord (m1, m2)
   | (MungedVar _, _) => LESS
   | (EnumC, MungedVar _) => GREATER
   | (_, FunctionName) => LESS
   | (FunctionName, _) => GREATER
  