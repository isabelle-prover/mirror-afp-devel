\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Property\<close>
theory Transport_Compositions_Agree_Galois_Property
  imports
    Transport_Compositions_Agree_Base
begin

context transport_comp_agree
begin

lemma galois_propI:
  assumes galois1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and galois2: "((\<le>\<^bsub>L2\<^esub>) \<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and mono_l1: "([in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>L2\<^esub>)) l1"
  and mono_r2: "([in_codom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  and agree: "([in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> [in_codom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow> (\<longleftrightarrow>))
    (rel_bimap l1 r2 (\<le>\<^bsub>R1\<^esub>)) (rel_bimap l1 r2 (\<le>\<^bsub>L2\<^esub>))"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
proof (rule galois_prop.galois_propI')
  fix x y assume "in_dom (\<le>\<^bsub>L\<^esub>) x" "in_codom (\<le>\<^bsub>R\<^esub>) y"
  with mono_r2 mono_l1 have "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)" "in_codom (\<le>\<^bsub>R1\<^esub>) (r2 y)" by auto
  have "x \<le>\<^bsub>L\<^esub> r y \<longleftrightarrow> x \<le>\<^bsub>L1\<^esub> r1 (r2 y)" by simp
  also from galois1 \<open>in_dom (\<le>\<^bsub>L1\<^esub>) x\<close> \<open>in_codom (\<le>\<^bsub>R1\<^esub>) (r2 y)\<close>
    have "... \<longleftrightarrow> l1 x \<le>\<^bsub>R1\<^esub> r2 y"
    by (rule g1.galois_prop_left_rel_right_iff_left_right_rel)
  also from agree \<open>in_dom (\<le>\<^bsub>L1\<^esub>) x\<close> \<open>in_codom (\<le>\<^bsub>R2\<^esub>) y\<close>
    have "... \<longleftrightarrow> l1 x \<le>\<^bsub>L2\<^esub> r2 y" by fastforce
  also from galois2 \<open>in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)\<close> \<open>in_codom (\<le>\<^bsub>R2\<^esub>) y\<close>
    have "... \<longleftrightarrow> l x \<le>\<^bsub>R2\<^esub> y"
    unfolding l_def
    by (simp add: g2.galois_prop_left_rel_right_iff_left_right_rel)
  finally show "x \<le>\<^bsub>L\<^esub> r y \<longleftrightarrow> l x \<le>\<^bsub>R\<^esub> y" .
qed

end

context transport_comp_same
begin

corollary galois_propI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R1\<^esub>) \<unlhd> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "([in_dom (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m in_dom (\<le>\<^bsub>R1\<^esub>)) l1"
  and "([in_codom (\<le>\<^bsub>R2\<^esub>)] \<Rrightarrow>\<^sub>m in_codom (\<le>\<^bsub>R1\<^esub>)) r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (rule galois_propI) auto

end


end