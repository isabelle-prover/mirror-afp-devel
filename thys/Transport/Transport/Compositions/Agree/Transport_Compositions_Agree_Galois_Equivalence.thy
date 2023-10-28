\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Equivalence\<close>
theory Transport_Compositions_Agree_Galois_Equivalence
  imports
    Transport_Compositions_Agree_Galois_Connection
begin

context transport_comp_agree
begin

interpretation flip : transport_comp_agree R2 L2 r2 l2 R1 L1 r1 l1 .

lemma galois_equivalenceI:
  assumes galois: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and mono_L1_L2_l1: "\<And>x y. x \<le>\<^bsub>L1\<^esub> y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> l1 y \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> l1 y"
  and mono_R2_R1_r2: "\<And>x y. x \<le>\<^bsub>R2\<^esub> y \<Longrightarrow> r2 x \<le>\<^bsub>L2\<^esub> r2 y \<Longrightarrow> r2 x \<le>\<^bsub>R1\<^esub> r2 y"
  and "([in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> [in_codom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap l1 r2 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap l1 r2 (\<le>\<^bsub>L2\<^esub>))"
  and mono_iff2: "([in_dom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow> [in_codom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap r2 l1 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap r2 l1 (\<le>\<^bsub>L2\<^esub>))"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from galois mono_L1_L2_l1 have "([in_codom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>L2\<^esub>)) l1"
    by (intro dep_mono_wrt_predI) blast
  moreover from galois mono_R2_R1_r2 have "([in_dom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>R1\<^esub>)) r2"
    by (intro dep_mono_wrt_predI) blast
  moreover from mono_iff2 have "([in_dom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow> [in_codom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap r2 l1 (\<le>\<^bsub>L2\<^esub>)) (rel_bimap r2 l1 (\<le>\<^bsub>R1\<^esub>))" by blast
  ultimately show ?thesis using assms
    by (intro galois_equivalenceI galois_connectionI flip.galois_propI) auto
qed

lemma galois_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) l1" "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) r2"
  and "([in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> [in_codom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap l1 r2 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap l1 r2 (\<le>\<^bsub>L2\<^esub>))"
  and "([in_dom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow> [in_codom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap r2 l1 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap r2 l1 (\<le>\<^bsub>L2\<^esub>))"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalenceI) auto

end

context transport_comp_same
begin

lemma galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>R1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (rule galois_equivalenceI) auto

end


end