(*  Title:      Containers/Compatibility_Containers_Regular_Sets.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

section {* Compatibility with Regular-Sets *}

theory Compatibility_Containers_Regular_Sets imports
  Containers
  "../Regular-Sets/Regexp_Method"
begin

text {*
  Adaptation theory to make @{text regexp} work when @{theory Containers} are loaded.

  Warning: Each invocation of @{text regexp} takes longer than without @{theory Containers}
  because the code generator takes longer to generate the evaluation code for @{text regexp}.
*}

datatype_compat rexp
derive ceq rexp
derive ccompare rexp
derive (choose) set_impl rexp

notepad begin
fix r s :: "('a \<times> 'a) set"
have "(r \<union> s^+)^* = (r \<union> s)^*" by regexp
end

end

