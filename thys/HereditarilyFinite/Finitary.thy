theory Finitary
imports Ordinal
begin

class finitary =
  fixes hf_of :: "'a \<Rightarrow> hf"
  assumes inj: "inj hf_of"
begin
  lemma hf_of_eq_iff [simp]: "hf_of x = hf_of y \<longleftrightarrow> x=y"
    using inj by (auto simp: inj_on_def)
end

instantiation unit :: finitary
begin
  definition hf_of_unit_def: "hf_of (u::unit) == 0"
  instance
    by intro_classes (auto simp: inj_on_def hf_of_unit_def)
end

instantiation bool :: finitary
begin
  definition hf_of_bool_def: "hf_of b == if b then 1 else 0"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_bool_def)
end

instantiation nat :: finitary
begin
  definition hf_of_nat_def: "hf_of == ord_of"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_nat_def)
end

instantiation int :: finitary
begin
  definition hf_of_int_def: 
    "hf_of i == if i\<ge>(0::int) then \<langle>0, hf_of (nat i)\<rangle> else \<langle>1, hf_of (nat (-i))\<rangle>"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_int_def)
end

instantiation nibble :: finitary
begin
  definition hf_of_nibble_def: 
    "hf_of x == hf_of (nat_of_nibble x)"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_nibble_def nat_of_nibble_eq_iff)
end

text{*Strings are char lists, and are not considered separately.*}
instantiation char :: finitary
begin
  definition hf_of_char_def: 
    "hf_of x == hf_of (nat_of_char x)"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_char_def nat_of_char_eq_iff)
end

instantiation prod :: (finitary,finitary) finitary
begin
  definition hf_of_prod_def: 
    "hf_of == \<lambda>(x,y). \<langle>hf_of x, hf_of y\<rangle>"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_prod_def)
end

instantiation sum :: (finitary,finitary) finitary
begin
  definition hf_of_sum_def: 
    "hf_of == case_sum (HF.Inl o hf_of) (HF.Inr o hf_of)"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_sum_def split: sum.split_asm)
end

instantiation option :: (finitary) finitary
begin
  definition hf_of_option_def: 
    "hf_of == case_option 0 (\<lambda>x. \<lbrace>hf_of x\<rbrace>)"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_option_def split: option.split_asm)
end

instantiation list :: (finitary) finitary
begin
  primrec hf_of_list where
    "hf_of_list Nil = 0"
  | "hf_of_list (x#xs) = \<langle>hf_of x, hf_of_list xs\<rangle>"
  lemma [simp]: fixes x :: "'a list" shows "hf_of x = hf_of y \<Longrightarrow> x = y"
    apply (induct x arbitrary: y, auto)
    apply (metis (mono_tags) hf_of_list.simps(2) hpair_nonzero neq_Nil_conv)
    apply (rename_tac y)
    apply (case_tac y, auto)
    done
  instance 
    by intro_classes (auto simp: inj_on_def)
end

end

