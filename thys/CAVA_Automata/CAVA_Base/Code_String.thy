(*
 * Code setup for native strings.
 * Author: René Neumann <rene.neumann@in.tum.de>
 *)
theory Code_String
imports
  "~~/src/HOL/Library/Code_Char"
  (*"~~/src/HOL/Library/List_lexord"*)
  "../../Collections/Refine_Dflt"      
begin

(* TODO: Move to Collections *)
instantiation String.literal :: hashable
begin
  definition hashcode_literal :: "String.literal \<Rightarrow> uint32" 
    where "hashcode_literal s = hashcode (String.explode s)"

  definition def_hashmap_size_literal 
    :: "String.literal itself \<Rightarrow> nat" where
    "def_hashmap_size_literal _ = 10"

  instance proof
  qed (simp_all only: def_hashmap_size_literal_def)
end

(* Append on literal strings -- allows for easier written exceptions *)

context 
  includes literal.lifting
begin

lift_definition literal_append 
  :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"  (infixr "@@" 65)
  is "op @" .

end

lifting_update literal.lifting
lifting_forget literal.lifting

code_printing
  constant literal_append \<rightharpoonup>
    (SML) infixr 5 "^"
    and (Haskell) infixr 5 "++"
    and (OCaml) infixr 5 "^"
end
