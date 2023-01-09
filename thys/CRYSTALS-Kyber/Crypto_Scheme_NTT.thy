theory Crypto_Scheme_NTT

imports Crypto_Scheme
        NTT_Scheme

begin

section \<open>Kyber Algorithm using NTT for Fast Multiplication\<close>

hide_type Matrix.vec

context kyber_ntt
begin


definition mult_ntt:: "'a qr \<Rightarrow> 'a qr \<Rightarrow> 'a qr" (infixl "*\<^bsub>ntt\<^esub>" 70) where
  "mult_ntt f g = inv_ntt_poly (ntt_poly f \<star> ntt_poly g)"

lemma mult_ntt:
  "f*g = f *\<^bsub>ntt\<^esub> g"
  unfolding mult_ntt_def using convolution_thm_ntt_poly by auto

definition scalar_prod_ntt:: 
  "('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> 'a qr" (infixl "\<bullet>\<^bsub>ntt\<^esub>" 70) where
  "scalar_prod_ntt v w = 
  (\<Sum>i\<in>(UNIV::'k set). (vec_nth v i) *\<^bsub>ntt\<^esub> (vec_nth w i))"

lemma scalar_prod_ntt:
  "scalar_product v w = scalar_prod_ntt v w"
  unfolding scalar_product_def scalar_prod_ntt_def using mult_ntt by auto

definition mat_vec_mult_ntt:: 
  "(('a qr, 'k) vec, 'k) vec \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec" (infixl "\<cdot>\<^bsub>ntt\<^esub>" 70) where
  "mat_vec_mult_ntt A v = vec_lambda (\<lambda>i. 
  (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) *\<^bsub>ntt\<^esub> (vec_nth v j)))"


lemma mat_vec_mult_ntt:
  "A *v v = mat_vec_mult_ntt A v"
  unfolding matrix_vector_mult_def mat_vec_mult_ntt_def using mult_ntt by auto

text \<open>Refined algorithm using NTT for multiplications\<close>

definition key_gen_ntt :: 
  "nat \<Rightarrow> (('a qr, 'k) vec, 'k) vec \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> 
   ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec" where 
  "key_gen_ntt dt A s e = compress_vec dt (A \<cdot>\<^bsub>ntt\<^esub> s + e)"

lemma key_gen_ntt:
  "key_gen_ntt dt A s e = key_gen dt A s e"
  unfolding key_gen_ntt_def key_gen_def mat_vec_mult_ntt by auto

definition encrypt_ntt :: 
  "('a qr, 'k) vec \<Rightarrow> (('a qr, 'k) vec, 'k) vec \<Rightarrow> 
   ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> ('a qr) \<Rightarrow> 
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a qr \<Rightarrow> 
   (('a qr, 'k) vec) * ('a qr)" where
  "encrypt_ntt t A r e1 e2 dt du dv m = 
  (compress_vec du ((transpose A) \<cdot>\<^bsub>ntt\<^esub> r + e1),  
   compress_poly dv ((decompress_vec dt t) \<bullet>\<^bsub>ntt\<^esub> r +
    e2 + to_module (round((real_of_int q)/2)) *\<^bsub>ntt\<^esub> m)) "

lemma encrypt_ntt:
  "encrypt_ntt t A r e1 e2 dt du dv m = encrypt t A r e1 e2 dt du dv m"
  unfolding encrypt_ntt_def encrypt_def mat_vec_mult_ntt scalar_prod_ntt mult_ntt by auto

definition decrypt_ntt :: 
  "('a qr, 'k) vec \<Rightarrow> ('a qr) \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> 
  nat \<Rightarrow> nat \<Rightarrow> 'a qr" where
  "decrypt_ntt u v s du dv = compress_poly 1 ((decompress_poly dv v) - 
  s \<bullet>\<^bsub>ntt\<^esub> (decompress_vec du u))"

lemma decrypt_ntt:
  "decrypt_ntt u v s du dv = decrypt u v s du dv"
  unfolding decrypt_ntt_def decrypt_def scalar_prod_ntt by auto

text \<open>$(1-\delta)$-correctness for the refined algorithm\<close>

lemma kyber_correct_ntt:
  fixes A s r e e1 e2 dt du dv ct cu cv t u v
  assumes 
      t_def:   "t = key_gen_ntt dt A s e"
  and u_v_def: "(u,v) = encrypt_ntt t A r e1 e2 dt du dv m"
  and ct_def:  "ct = compress_error_vec dt (A \<cdot>\<^bsub>ntt\<^esub> s + e)"
  and cu_def:  "cu = compress_error_vec du 
                ((transpose A) \<cdot>\<^bsub>ntt\<^esub> r + e1)"
  and cv_def:  "cv = compress_error_poly dv 
                ((decompress_vec dt t) \<bullet>\<^bsub>ntt\<^esub> r + e2 + 
                 to_module (round((real_of_int q)/2)) *\<^bsub>ntt\<^esub> m)"
  and delta:   "abs_infty_poly (e \<bullet>\<^bsub>ntt\<^esub> r + e2 + cv - 
                s \<bullet>\<^bsub>ntt\<^esub> e1 + ct \<bullet>\<^bsub>ntt\<^esub> r - 
                s \<bullet>\<^bsub>ntt\<^esub> cu) < round (real_of_int q / 4)"
  and m01:     "set ((coeffs \<circ> of_qr) m) \<subseteq> {0,1}"
  shows "decrypt_ntt u v s du dv = m"
using assms unfolding key_gen_ntt encrypt_ntt decrypt_ntt mat_vec_mult_ntt[symmetric] 
scalar_prod_ntt[symmetric] mult_ntt[symmetric] using kyber_correct by auto

end
end