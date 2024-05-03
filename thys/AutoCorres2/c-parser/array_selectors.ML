(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature ARRAY_SELECTORS = sig
  val array_selectors: Proof.context -> {recursive_record_simpset: bool} -> thm -> thm list
  val dest_numeralT: typ -> int
  val mk_index: typ * typ -> term
end

structure Array_Selectors : ARRAY_SELECTORS = struct
local
  fun int_of [] = 0
    | int_of (b :: bs) = b + 2 * int_of bs;

  fun bin_of (Type (\<^type_name>\<open>num0\<close>, [])) = []
    | bin_of (Type (\<^type_name>\<open>num1\<close>, [])) = [1]
    | bin_of (Type (\<^type_name>\<open>bit0\<close>, [bs])) = 0 :: bin_of bs
    | bin_of (Type (\<^type_name>\<open>bit1\<close>, [bs])) = 1 :: bin_of bs
    | bin_of ty = raise TYPE ("dest_numeralT.bin_of", [ty], []);
in
fun dest_numeralT ty = bin_of ty |> int_of
end

fun mk_index (ty, ty_index) = \<^Const>\<open>Arrays.index ty ty_index\<close>

fun array_selectors ctxt {recursive_record_simpset} thm =
  let
    val (lhs, _) = Thm.cprop_of thm |> Thm.dest_equals
    val tys_array = case fastype_of (Thm.term_of lhs) of
      Type (@{type_name Arrays.array}, [ty, ty_index]) => (ty, ty_index)
      | _ => raise TERM ("array_selector: expexted array but got", [Thm.term_of lhs])
    val index = mk_index tys_array |> Thm.cterm_of ctxt
    val n = tys_array |> snd |> dest_numeralT
    val simpset = if recursive_record_simpset
      then merge_ss (HOL_ss, RecursiveRecordPackage.get_simpset (Proof_Context.theory_of ctxt))
      else HOL_ss
    val ctxt' = put_simpset simpset ctxt addsimps
      (Named_Theorems.get ctxt @{named_theorems array_selectors_simps})
    fun array_selector i =
      let
        val ct = Thm.apply (Thm.apply index lhs) i
      in (Conv.arg1_conv (Conv.rewr_conv thm)
          then_conv Simplifier.rewrite ctxt') ct
      end
    in
      0 upto (n - 1) |>
      maps (fn i => Thm.cterm_of ctxt (HOLogic.mk_number @{typ nat} i) ::
        (if i = 1 then [@{cterm "Suc 0"}] else [])) |>
      map array_selector
    end

local
val name_is_facts = Parse.and_list1 (Parse_Spec.opt_thm_name "is" -- Parse.thms1);
in
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>array_selectors\<close> "define array selector theorems"
    (Args.mode "no_recursive_record_simpset" -- name_is_facts >>
      (fn (no_rrs, name_facts) =>
        fold (fn ((binding, raw_atts), xthms) => fn lthy =>
          Local_Theory.note ((binding, map (Attrib.check_src lthy) raw_atts),
              Attrib.eval_thms lthy xthms |>
              maps (array_selectors lthy {recursive_record_simpset = not no_rrs})
            ) lthy |> snd) name_facts));
end

end