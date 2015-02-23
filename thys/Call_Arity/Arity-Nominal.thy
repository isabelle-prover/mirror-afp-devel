theory "Arity-Nominal"
imports Arity "Nominal-HOLCF"
begin

lemma join_eqvt[eqvt]: "\<pi> \<bullet> (x \<squnion> (y :: 'a :: {Finite_Join_cpo, cont_pt})) = (\<pi> \<bullet> x) \<squnion> (\<pi> \<bullet> y)"
  by (rule is_joinI[symmetric]) (auto simp add: perm_below_to_right)


instantiation Arity :: pure
begin
  definition "p \<bullet> (a::Arity) = a"
instance
  apply default
  apply (auto simp add: permute_Arity_def)
  done
end


instance Arity :: cont_pt by default (simp add: pure_permute_id)
instance Arity :: pure_cont_pt by default

end
