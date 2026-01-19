section \<open>\<open>Aux_Sturm_Calculation\<close> -- Auxiliary theory for technical reasons.\<close>

theory Aux_Sturm_Calculation imports
  Sturm_Sequences.Sturm
begin

text \<open>We prove this fact in a separate theory because in \<open>Collision.thy\<close>,
  the @{method sturm} method fails with an internal error.\<close>
lemma sturm_calculation: \<open>12 * (r\<^sup>2+154)^3 - (10/3 * (r+2)^3 + 20)\<^sup>2 \<noteq> 0\<close> if \<open>r \<ge> 0\<close> for r :: real
  by sturm

end