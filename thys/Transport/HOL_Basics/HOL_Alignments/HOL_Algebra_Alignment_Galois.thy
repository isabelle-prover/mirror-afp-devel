\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Definitions from HOL-Algebra\<close>
theory HOL_Algebra_Alignment_Galois
  imports
    "HOL-Algebra.Galois_Connection"
    HOL_Algebra_Alignment_Orders
    Galois
begin

named_theorems HOL_Algebra_galois_alignment

context galois_connection
begin

context
  fixes L R l r
  defines "L \<equiv> (\<sqsubseteq>\<^bsub>\<X>\<^esub>)\<restriction>\<^bsub>carrier \<X>\<^esub>\<upharpoonleft>\<^bsub>carrier \<X>\<^esub>" and "R \<equiv> (\<sqsubseteq>\<^bsub>\<Y>\<^esub>)\<restriction>\<^bsub>carrier \<Y>\<^esub>\<upharpoonleft>\<^bsub>carrier \<Y>\<^esub>"
    and "l \<equiv> \<pi>\<^sup>*" and "r \<equiv> \<pi>\<^sub>*"
  notes defs[simp] = L_def R_def l_def r_def and restrict_right_eq[simp]
    and restrict_leftI[intro!] restrict_leftE[elim!]
begin

interpretation galois L R l r .

lemma mono_wrt_rel_lower [HOL_Algebra_galois_alignment]: "(L \<Rrightarrow>\<^sub>m R) l"
  using lower_closed upper_closed by (fastforce intro: use_iso2[OF lower_iso])

lemma mono_wrt_rel_upper [HOL_Algebra_galois_alignment]: "(R \<Rrightarrow>\<^sub>m L) r"
  using lower_closed upper_closed by (fastforce intro: use_iso2[OF upper_iso])

lemma half_galois_prop_left [HOL_Algebra_galois_alignment]: "(L \<^sub>h\<unlhd> R) l r"
  using galois_property lower_closed by fastforce

lemma half_galois_prop_right [HOL_Algebra_galois_alignment]: "(L \<unlhd>\<^sub>h R) l r"
  using galois_property upper_closed by fastforce

lemma galois_prop [HOL_Algebra_galois_alignment]: "(L \<unlhd> R) l r"
  using half_galois_prop_left half_galois_prop_right by blast

lemma galois_connection [HOL_Algebra_galois_alignment]: "(L \<stileturn> R) l r"
  using mono_wrt_rel_lower mono_wrt_rel_upper galois_prop by blast

end
end

context galois_bijection
begin

context
  fixes L R l r
  defines "L \<equiv> (\<sqsubseteq>\<^bsub>\<X>\<^esub>)\<restriction>\<^bsub>carrier \<X>\<^esub>\<upharpoonleft>\<^bsub>carrier \<X>\<^esub>" and "R \<equiv> (\<sqsubseteq>\<^bsub>\<Y>\<^esub>)\<restriction>\<^bsub>carrier \<Y>\<^esub>\<upharpoonleft>\<^bsub>carrier \<Y>\<^esub>"
    and "l \<equiv> \<pi>\<^sup>*" and "r \<equiv> \<pi>\<^sub>*"
  notes defs[simp] = L_def R_def l_def r_def and restrict_right_eq[simp]
    and restrict_leftI[intro!] restrict_leftE[elim!] in_codom_restrict_leftE[elim!]
begin

interpretation galois R L r l .

lemma half_galois_prop_left_right_left [HOL_Algebra_galois_alignment]:
  "(R \<^sub>h\<unlhd> L) r l"
  using gal_bij_conn.right lower_inv_eq upper_closed upper_inv_eq
  by (intro half_galois_prop_leftI; elim left_GaloisE) (auto; metis)

lemma half_galois_prop_right_right_left [HOL_Algebra_galois_alignment]:
  "(R \<unlhd>\<^sub>h L) r l"
  using gal_bij_conn.left lower_closed lower_inv_eq upper_inv_eq
  by (intro half_galois_prop_rightI; elim Galois_rightE) (auto; metis)

lemma prop_right_right_left [HOL_Algebra_galois_alignment]: "(R \<unlhd> L) r l"
  using half_galois_prop_left_right_left half_galois_prop_right_right_left by blast

lemma galois_equivalence [HOL_Algebra_galois_alignment]: "(L \<equiv>\<^sub>G R) l r"
  using gal_bij_conn.galois_connection prop_right_right_left
  by (intro galois.galois_equivalenceI) auto

end
end


end