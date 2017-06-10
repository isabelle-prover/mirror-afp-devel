theory Fofu_Impl_Base
imports 
  "../../Refine_Imperative_HOL/IICF/IICF"
  "../../Refine_Imperative_HOL/Sepref_ICF_Bindings"
  "~~/src/HOL/Library/Rewrite"
  Refine_Monadic_Syntax_Sugar
begin
  hide_type (open) List_Seg.node

  interpretation Refine_Monadic_Syntax .


      
(* TODO: Move, patch Imperative/HOL! 
  This patch makes Imperative/HOL array translation also work for index types other than IntInf.
  Note that the toInt-operations are required to raise an Overflow exception on overflow, such that
  creating an array of too big size is safe, and also indexing an array out of bounds will be 
  correctly caught.
*)
code_printing constant Array.new' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ (IntInf.toInt _,/ (_)))"
code_printing constant Array.make' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ (IntInf.toInt _,/ _ o IntInf.fromInt))"
code_printing constant Array.len' \<rightharpoonup> (SML) "(fn/ ()/ =>/ IntInf.fromInt (Array.length/ _))"
code_printing constant Array.nth' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ IntInf.toInt _))"
code_printing constant Array.upd' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ IntInf.toInt _,/ (_)))"
  
  
(*
  TODO: Patch that belongs to array_blit.thy. 
  Already in Lammich's local AFP copy!
*)  
code_printing code_module "array_blit" \<rightharpoonup> (SML)
  {*
  (* Locally patched version  *)
  fun array_blit src si dst di len = (
    src=dst andalso raise Fail ("array_blit: Same arrays");
    ArraySlice.copy {
      di = IntInf.toInt di,
      src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
      dst = dst})

  fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
  fun array_upd_oo f i x a () = 
    (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

  *}
  
  
end
