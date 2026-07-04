theory Xor_Inst
imports
  Xor
  Fixed_Length_Vector.Fixed_Length_Vector
begin

text \<open>More instances for @{locale abel_group_xor}\<close>

unbundle Fixed_Length_Vector.vec_syntax

text \<open>Sequences containing a base type that can be xor'd can itself also be xor'd, via element-wise xor\<close>
instantiation (*tag:important*) vec :: (abel_group_xor,index1) abel_group_xor begin

text \<open>XORing two vectors is defined as element-wise XOR\<close>
definition xor_vec :: "('a, 'b) vec \<Rightarrow>
                       ('a, 'b) vec \<Rightarrow>
                       ('a, 'b) vec" where
  "xor_vec a b \<equiv> map_vec (\<lambda>(a',b'). a' XOR b') (zip_vec a b)"

text \<open>The identity vector is a vector where every element is zero\<close>
definition "zero_vec \<equiv> replicate_vec 0 :: ('a,'b) vec"

instance proof
  fix a b c :: "('a, 'b) vec"
  show eq_iff: "a XOR b = 0 \<longleftrightarrow> a = b" unfolding xor_vec_def zero_vec_def
    by (metis (no_types, opaque_lifting) map_nth_vec replicate_nth_vec split_beta vec_cong
    abel_group_xor_class.eq_iff zip_vec_fst zip_vec_snd)
qed (simp_all add: xor_vec_def zero_vec_def ac_simps vec_cong)
end (* instance vec::xor *)

lemma nth_conv [simp]:
  shows "(a XOR b) $ i = a $ i XOR b $ i"
  unfolding xor_vec_def by simp

unbundle no Fixed_Length_Vector.vec_syntax
end (*theory*)