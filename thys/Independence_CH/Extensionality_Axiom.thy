section\<open>The Axiom of Extensionality in $M[G]$\<close>

theory Extensionality_Axiom
  imports
    Names
begin

context forcing_data1
begin

lemma extensionality_in_MG : "extensionality(##(M[G]))"
  unfolding extensionality_def
proof(clarsimp)
  fix x y
  assume "x\<in>M[G]" "y\<in>M[G]" "(\<forall>w\<in>M[G] . w \<in> x \<longleftrightarrow> w \<in> y)"
  moreover from this
  have "z\<in>x \<longleftrightarrow> z\<in>M[G] \<and> z\<in>y" for z
    using transitivity_MG by auto
  moreover from calculation
  have "z\<in>M[G] \<and> z\<in>x \<longleftrightarrow> z\<in>y" for z
    using transitivity_MG by auto
  ultimately
  show "x=y"
    by auto
qed

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end