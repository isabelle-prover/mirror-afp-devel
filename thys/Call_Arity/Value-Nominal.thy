theory "Value-Nominal"
imports Value "Nominal-Utils" "Nominal-HOLCF"
begin

text {* Values are pure, i.e. contain no variables. *}

instantiation Value :: pure
begin
  definition "p \<bullet> (v::Value) = v"
instance
  apply default
  apply (auto simp add: permute_Value_def)
  done
end

instance Value :: pcpo_pt
  by default (simp add: pure_permute_id)

end
