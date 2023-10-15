\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Relator\<close>
theory Transport_Compositions_Agree_Galois_Relator
  imports
    Transport_Compositions_Agree_Base
begin

context transport_comp_agree
begin

lemma left_Galois_le_comp_left_GaloisI:
  assumes in_codom_mono_r2: "([in_codom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  and r2_L2_self_if_in_codom: "\<And>z. in_codom (\<le>\<^bsub>R2\<^esub>) z \<Longrightarrow> r2 z \<le>\<^bsub>L2\<^esub> r2 z"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) \<le> ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
proof (rule le_relI)
  fix x z assume "x \<^bsub>L\<^esub>\<lessapprox> z"
  then have "x \<le>\<^bsub>L1\<^esub> r z" "in_codom (\<le>\<^bsub>R\<^esub>) z" by auto
  with \<open>x \<le>\<^bsub>L1\<^esub> r z\<close> in_codom_mono_r2 have "x \<^bsub>L1\<^esub>\<lessapprox> r2 z" by auto
  moreover from \<open>in_codom (\<le>\<^bsub>R2\<^esub>) z\<close> r2_L2_self_if_in_codom have "r2 z \<^bsub>L2\<^esub>\<lessapprox> z"
    by (intro g2.left_GaloisI) auto
  ultimately show "((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) x z" by blast
qed

lemma comp_left_Galois_le_left_GaloisI:
  assumes mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and R1_r2_if_in_codom: "\<And>y z. in_codom (\<le>\<^bsub>R2\<^esub>) z \<Longrightarrow> y \<le>\<^bsub>L2\<^esub> r2 z \<Longrightarrow> y \<le>\<^bsub>R1\<^esub> r2 z"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) \<le> (\<^bsub>L\<^esub>\<lessapprox>)"
proof (rule le_relI)
  fix x z assume "((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>)) x z"
  then obtain y where "x \<^bsub>L1\<^esub>\<lessapprox> y" "y \<^bsub>L2\<^esub>\<lessapprox> z" by blast
  then have "x \<le>\<^bsub>L1\<^esub> r1 y" "y \<le>\<^bsub>L2\<^esub> r2 z" "in_codom (\<le>\<^bsub>R\<^esub>) z" by auto
  with R1_r2_if_in_codom have "y \<le>\<^bsub>R1\<^esub> r2 z" by blast
  with mono_r1 have "r1 y \<le>\<^bsub>L1\<^esub> r z" by auto
  with \<open>x \<le>\<^bsub>L1\<^esub> r1 y\<close> \<open>in_codom (\<le>\<^bsub>R\<^esub>) z\<close> show "x \<^bsub>L\<^esub>\<lessapprox> z" using trans_L1 by blast
qed

corollary left_Galois_eq_comp_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>z. in_codom (\<le>\<^bsub>R2\<^esub>) z \<Longrightarrow> r2 z \<le>\<^bsub>L2\<^esub> r2 z"
  and "\<And>y z. in_codom (\<le>\<^bsub>R2\<^esub>) z \<Longrightarrow> y \<le>\<^bsub>L2\<^esub> r2 z \<Longrightarrow> y \<le>\<^bsub>R1\<^esub> r2 z"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms
  by (intro antisym left_Galois_le_comp_left_GaloisI comp_left_Galois_le_left_GaloisI
    dep_mono_wrt_predI)
  fastforce

corollary left_Galois_eq_comp_left_GaloisI':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "reflexive_on (in_codom (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "\<And>y z. in_codom (\<le>\<^bsub>R2\<^esub>) z \<Longrightarrow> y \<le>\<^bsub>L2\<^esub> r2 z \<Longrightarrow> y \<le>\<^bsub>R1\<^esub> r2 z"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_GaloisI) auto

corollary left_Galois_eq_comp_left_GaloisI'':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "reflexive_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "\<And>y z. in_codom (\<le>\<^bsub>R2\<^esub>) z \<Longrightarrow> y \<le>\<^bsub>L2\<^esub> r2 z \<Longrightarrow> y \<le>\<^bsub>R1\<^esub> r2 z"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_GaloisI) (auto 0 4)

end

context transport_comp_same
begin

lemma left_Galois_eq_comp_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) r2"
  and "reflexive_on (in_codom (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_GaloisI') auto

lemma left_Galois_eq_comp_left_GaloisI':
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_codom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) r2"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<circ>\<circ> (\<^bsub>L2\<^esub>\<lessapprox>))"
  using assms by (intro left_Galois_eq_comp_left_GaloisI'') auto

end


end