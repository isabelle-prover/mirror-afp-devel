subsection \<open>Renaming strings apart\<close>

theory Renaming2_String
  imports 
    Renaming2
    Lists_are_Infinite
begin

lift_definition string_rename :: "string renaming2" is "(Cons (CHR ''x''), Cons (CHR ''y''))" 
  by auto

end

  
