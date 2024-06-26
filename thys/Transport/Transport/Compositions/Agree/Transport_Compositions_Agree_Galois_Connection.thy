\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Connection\<close>
theory Transport_Compositions_Agree_Galois_Connection
  imports
    Transport_Compositions_Agree_Monotone
    Transport_Compositions_Agree_Galois_Property
begin

context transport_comp_agree
begin

interpretation flip : transport_comp_agree R2 L2 r2 l2 R1 L1 r1 l1 .

lemma galois_connectionI:
  assumes galois: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and mono_L1_L2_l1: "\<And>x y. x \<le>\<^bsub>L1\<^esub> y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> l1 y \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> l1 y"
  and mono_R2_R1_r2: "\<And>x y. x \<le>\<^bsub>R2\<^esub> y \<Longrightarrow> r2 x \<le>\<^bsub>L2\<^esub> r2 y \<Longrightarrow> r2 x \<le>\<^bsub>R1\<^esub> r2 y"
  and "(in_dom (\<le>\<^bsub>L1\<^esub>) \<Rrightarrow> in_codom (\<le>\<^bsub>R2\<^esub>) \<Rrightarrow> (\<longleftrightarrow>)) (rel_bimap l1 r2 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap l1 r2 (\<le>\<^bsub>L2\<^esub>))"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from galois mono_L1_L2_l1 have "(in_dom (\<le>\<^bsub>L1\<^esub>) \<Rightarrow> in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
    by (intro mono_wrt_predI) (blast elim!: in_domE g1.galois_connectionE)
  moreover from galois mono_R2_R1_r2
    have "(in_codom (\<le>\<^bsub>R2\<^esub>) \<Rightarrow> in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
    by (intro mono_wrt_predI) (blast elim!: in_codomE g2.galois_connectionE)
  ultimately show ?thesis using assms
    by (intro galois_connectionI galois_propI mono_wrt_rel_leftI
      flip.mono_wrt_rel_leftI)
    auto
qed

lemma galois_connectionI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rightarrow> (\<le>\<^bsub>L2\<^esub>)) l1" "((\<le>\<^bsub>R2\<^esub>) \<Rightarrow> (\<le>\<^bsub>R1\<^esub>)) r2"
  and "(in_dom (\<le>\<^bsub>L1\<^esub>) \<Rrightarrow> in_codom (\<le>\<^bsub>R2\<^esub>) \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap l1 r2 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap l1 r2 (\<le>\<^bsub>L2\<^esub>))"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_connectionI) auto

end

context transport_comp_same
begin

corollary galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1" "((\<le>\<^bsub>R1\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (rule galois_connectionI) auto

end


end