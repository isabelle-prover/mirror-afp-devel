(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

text_raw \<open>\part{C-Parser}\<close>

chapter "Theory Variants for Target Architectures via \<open>L4V_ARCH\<close>"

theory Target_Architecture
  imports Main
  keywords
    "if_architecture_by" :: "qed_global" % "proof" and
    "if_architecture_context" :: thy_decl_block

begin

ML \<open>
structure Target_Architecture =
struct

datatype arch = ARM | ARM64 | ARM_HYP | RISCV64 | X64

val ARM_N     = "ARM"
val ARM64_N   = "ARM64"
val ARM_HYP_N = "ARM_HYP"
val RISCV64_N = "RISCV64"
val X64_N     = "X64"
val architectures = [(ARM_N, (\<^here>, ARM)), (ARM64_N, (\<^here>, ARM64)), (ARM_HYP_N, (\<^here>, ARM_HYP)), 
        (RISCV64_N, (\<^here>, RISCV64)), (X64_N, (\<^here>, X64))]

val rev_architectures = map (fn (name, (_, arch)) => (arch, name)) architectures

val string_of = AList.lookup (op =) rev_architectures #> the 

fun check_architecture thy (name, pos) = 
  case AList.lookup (op =) architectures name of
    SOME (def_pos, arch) => 
       let
         val markup = Position.entity_markup "architecture_variant" (name, def_pos)
         val _ = 
          Context_Position.reports (Proof_Context.init_global thy) [(pos, markup), (pos, Markup.string)] 
       in arch end
  | NONE => error ("undefined architecture variant " ^ quote name ^ Position.here pos ^ "\n" ^ 
             " known variants: "  ^ @{make_string} (map #1 architectures))

  val active = the_default ARM (try (getenv_strict) "L4V_ARCH" |> 
        Option.map (fn n => check_architecture @{theory} (n, \<^here>)))

end
\<close>


ML \<open>
structure Target_Architecture =
struct
  open Target_Architecture

fun arch_parser msg p = (Parse.$$$ "(" |-- Parse.list (Parse.name_position)  --| Parse.$$$ ")") 
  :|--  (fn archs => 
  let
    val archs' = map (check_architecture @{theory}) archs
    val is_active = member (op =) archs' active
    val _ = if not is_active then writeln ("active architecture " ^ quote (string_of active)
                 ^ " not in " ^ @{make_string} (map string_of archs') ^ ": " ^ msg) else ()
  in
    p is_active
  end) 


fun is_active arch = (arch = active); 

fun add_path arch =
  if is_active arch then Sign.add_path (string_of arch) else Sign.mandatory_path (string_of arch)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>if_architecture_by\<close> "conditional terminal backward proof"
    (arch_parser "aborting proof (oops)" (fn is_active =>
      (Method.parse -- Scan.option Method.parse >> (fn (m1, m2) =>
       (Method.report m1;
        Option.map Method.report m2;
        (if is_active then 
           Isar_Cmd.terminal_proof (m1, m2) 
         else 
           Toplevel.forget_proof (* oops *)))))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>if_architecture_context\<close> "conditional context or experiment"
   (arch_parser "experiment only" (fn is_active =>
      (Scan.repeat Parse_Spec.context_element --| Parse.begin
        >> (fn elems =>
            if is_active then 
              Toplevel.begin_nested_target (Target_Context.context_begin_nested_cmd [] elems)
            else
              Toplevel.begin_main_target true (Experiment.experiment_cmd elems #> snd)))));

val _ = Theory.setup
  (ML_Antiquotation.conditional \<^binding>\<open>if_ARM\<close>   (fn _ => is_active ARM) #>
   ML_Antiquotation.conditional \<^binding>\<open>if_ARM64\<close> (fn _ => is_active ARM64) #>
   ML_Antiquotation.conditional \<^binding>\<open>if_ARM_HYP\<close> (fn _ => is_active ARM_HYP) #>
   ML_Antiquotation.conditional \<^binding>\<open>if_RISCV64\<close> (fn _ => is_active RISCV64) #>
   ML_Antiquotation.conditional \<^binding>\<open>if_X64\<close> (fn _ => is_active X64))

end
\<close>

end

chapter "Unified Memory Model (UMM)"