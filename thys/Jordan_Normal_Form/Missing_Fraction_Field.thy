(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Fraction Field\<close>

text \<open>This theory provides an injective mapping from rings into the corresponding
  fraction field: \textit{embed-ff}.\<close>

theory Missing_Fraction_Field
imports 
  "~~/src/HOL/Library/Fraction_Field"
  "../Polynomial_Interpolation/Ring_Hom"
begin

context
  fixes ty :: "'a :: idom itself"
begin
definition embed_ff :: "'a \<Rightarrow> 'a fract" where
  "embed_ff x = Fract x 1"

lemma inj_embed_ff: "embed_ff x = embed_ff y \<Longrightarrow> x = y"
  unfolding embed_ff_def by (simp add: eq_fract)

lemma embed_ff: "inj_ring_hom embed_ff"
  by (unfold_locales, insert inj_embed_ff, unfold embed_ff_def Zero_fract_def One_fract_def, auto)
end

lemma embed_ff_1: "embed_ff 1 = 1" 
proof -
  interpret inj_ring_hom embed_ff by (rule embed_ff)
  show ?thesis by simp 
qed

lemma embed_ff_0: "embed_ff 0 = 0"
proof -
  interpret inj_ring_hom embed_ff by (rule embed_ff)
  show ?thesis by simp 
qed

end