theory Infinite_Variables
  imports Fresh_Identifiers.Fresh
begin

locale infinite_variables =
  fixes exists_nonground :: bool and variables :: "'v set"
  assumes
    "variables = UNIV" and
    infinite_variables: "exists_nonground \<Longrightarrow> infinite (UNIV :: 'v set)"

sublocale infinite \<subseteq> infinite_variables True "UNIV :: 'a set"
proof unfold_locales
  show "UNIV = UNIV" ..
next
  show "infinite (UNIV :: 'a set)"
    using infinite_UNIV .
qed

end
