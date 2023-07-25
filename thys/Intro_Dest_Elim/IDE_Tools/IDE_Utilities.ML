(* Copyright 2021 (C) Mihails Milehins *)

signature IDE_UTILITIES =
sig
  val print_theorem: Proof.context -> string -> thm list -> unit
end;

structure IDE_Utilities : IDE_UTILITIES =
struct

fun print_theorem ctxt name thms = 
  Proof_Display.print_results 
    true
    (Position.thread_data ()) 
    ctxt 
    ((Thm.theoremK, ""), [(name, thms)]);

end;