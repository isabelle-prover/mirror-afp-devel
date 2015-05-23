theory BoolProgs_LTL_Conv
imports
  "BoolProgs_Extras"
  "~~/src/HOL/Library/Mapping"
  "../../LTL_to_GBA/LTL"
begin

context begin interpretation LTL_Syntax .

fun b2l :: "bexp \<Rightarrow> nat ltlc" where
  "b2l TT = true\<^sub>c"
| "b2l FF = false\<^sub>c"
| "b2l (bexp.V v) = prop\<^sub>c(v)"
| "b2l (bexp.Not e) = not\<^sub>c (b2l e)"
| "b2l (And e1 e2) = b2l e1 and\<^sub>c b2l e2"
| "b2l (Or e1 e2) = b2l e1 or\<^sub>c b2l e2"

end

datatype
  propc = CProp String.literal | FProp "String.literal * integer"

context begin interpretation LTL_Syntax .

fun ltl_conv :: "const_map \<Rightarrow> fun_map \<Rightarrow> propc ltlc \<Rightarrow> (nat ltlc + String.literal)"
where
  "ltl_conv _ _ LTLcTrue = Inl LTLcTrue"
| "ltl_conv _ _ LTLcFalse = Inl LTLcFalse"
| "ltl_conv C _ (LTLcProp (CProp s)) = (case Mapping.lookup C s of
                                              Some c \<Rightarrow> Inl (b2l c)
                                             | None \<Rightarrow> Inr (STR ''Unknown constant: '' @@ s))"
| "ltl_conv _ M (LTLcProp (FProp (s, arg))) = (case Mapping.lookup M s of
                                                    Some f \<Rightarrow> (Inl \<circ> b2l \<circ> f \<circ> nat_of_integer) arg
                                                  | None \<Rightarrow> Inr (STR ''Unknown function: '' @@ s))"
| "ltl_conv C M (LTLcNeg x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (LTLcNeg l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (LTLcNext x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (LTLcNext l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (LTLcFinal x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (LTLcFinal l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (LTLcGlobal x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (LTLcGlobal l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (LTLcAnd x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (LTLcAnd l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (LTLcOr x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (LTLcOr l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (LTLcImplies x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (LTLcImplies l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (LTLcIff x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (LTLcIff l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (LTLcUntil x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (LTLcUntil l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (LTLcRelease x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (LTLcRelease l r) | Inr s \<Rightarrow> Inr s))"

end
end
