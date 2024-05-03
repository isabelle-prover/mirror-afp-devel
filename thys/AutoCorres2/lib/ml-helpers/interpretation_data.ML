(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
Generic data for locale interpretations. Added inside of a locale, accessible for
interpretations via morphism.
The minimalistic interpretation data would be the plain morphism so you can use it whenever
you need an instance (of a theorem, term, ...). However, it probably makes sense to already apply
the morphism to (parts) of your data to avoid re-evaluation of the morphism on each use.
*)


structure Raw_Data = Generic_Data (
  type T = Any.T Symreltab.table (* indexed by locale-name * <interpretation-qualifier>.<dataslot-name> *)
  val empty = Symreltab.empty
  val merge = Symreltab.merge (K true)
)



val get_raw_interpretation_data = Raw_Data.get; (* For exploration purposes only *)

signature INTERPRETATION_DATA_ARGS =
sig
  type T
  val name: string
end;

signature INTERPRETATION_DATA =
sig
  type T
  val add : T -> Morphism.morphism -> Context.generic -> Context.generic
  val get : string -> Proof.context -> T option  
end;

functor Interpretation_Data (Data: INTERPRETATION_DATA_ARGS): INTERPRETATION_DATA =
struct
type T = Data.T
val name = 
  let
    val thy_naming = Name_Space.naming_of (Context.Theory (Context.the_global_context ()))
  in Name_Space.full_name thy_naming (Binding.name (Data.name)) end

val locale_name = 
  case Context.the_local_context () |> Named_Target.locale_of  of
    SOME name => name
  | NONE => error ("Interpretation_Data functor must be invoced inside of a locale context")

exception Data of T;

fun inj x = Data x;
fun prj (Data x) = x;

fun add x phi context = 
  let
    val b = Morphism.binding phi (Binding.name name)
    val qualified_name = Binding.prefix_of b |> map fst 
      |> (fn prfx => name |> fold Long_Name.qualify prfx)
  in
    context |> Raw_Data.map (Symreltab.update_new  ((locale_name, qualified_name), inj x))
  end


fun get interpretation_qualifier ctxt = 
  let
    val tab = Raw_Data.get (Context.Proof ctxt)
    val key = (locale_name, Long_Name.qualify interpretation_qualifier name)
  in 
    Option.map prj (Symreltab.lookup tab key)
  end
end;

structure Raw_Data = struct end;