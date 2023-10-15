\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Monotonicity\<close>
theory Transport_Compositions_Generic_Monotone
  imports
    Transport_Compositions_Generic_Base
begin

context transport_comp
begin

lemma mono_wrt_rel_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and inflationary_unit2: "inflationary_on (in_codom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
proof (rule dep_mono_wrt_relI)
  fix x x' assume "x \<le>\<^bsub>L\<^esub> x'"
  then show "l x \<le>\<^bsub>R\<^esub> l x'"
  proof (rule right_rel_if_left_relI)
    fix y' assume "l1 x \<le>\<^bsub>L2\<^esub> y'"
    with \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close> show "l x \<le>\<^bsub>R2\<^esub> l2 y'" by auto
  next
    assume "in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x')"
    with inflationary_unit2 show "l1 x' \<le>\<^bsub>L2\<^esub> r2 (l x')" by auto
    from \<open>in_codom (\<le>\<^bsub>L2\<^esub>) (l1 x')\<close> \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close>
      show "in_codom (\<le>\<^bsub>R2\<^esub>) (l x')" by auto
  qed (insert assms, auto)
qed

lemma mono_wrt_rel_leftI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>L2\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and refl_L2: "reflexive_on (in_dom (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_dom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_dom (\<le>\<^bsub>L2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
proof (rule dep_mono_wrt_relI)
  fix x x' assume "x \<le>\<^bsub>L\<^esub> x'"
  then show "l x \<le>\<^bsub>R\<^esub> l x'"
  proof (rule right_rel_if_left_relI')
    fix y' assume "y' \<le>\<^bsub>L2\<^esub> l1 x'"
    moreover with \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close> have "l2 y' \<le>\<^bsub>R2\<^esub> l x'" by auto
    ultimately show "in_codom (\<le>\<^bsub>R2\<^esub>) (l x')" "y' \<le>\<^bsub>L2\<^esub> r2 (l x')"
      using \<open>((\<le>\<^bsub>L2\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R2\<^esub>)) l2 r2\<close> by auto
  next
    assume "in_dom (\<le>\<^bsub>L2\<^esub>) (l1 x)"
    with refl_L2 \<open>((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2\<close> show "l x \<le>\<^bsub>R2\<^esub> l2 (l1 x)" by auto
  qed (insert assms, auto)
qed

end


end