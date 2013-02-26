theory "Value-Meet"
  imports "HOLCF-Join"  "Denotational-Common"
begin

subsubsection {* The binary meet of two values *}

fixrec value_meet :: "Value \<rightarrow> Value \<rightarrow> Value"
  where "value_meet\<cdot>(Fn\<cdot>f)\<cdot>(Fn\<cdot>g) = Fn\<cdot>(\<Lambda> x. value_meet\<cdot>(f\<cdot>x)\<cdot>(g\<cdot>x))"

lemma[simp]: "value_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "value_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)

instance Value :: Finite_Meet_cpo
apply default
proof(rule exI, intro conjI strip)
  fix x y
  {
    fix t
    have "(t \<sqsubseteq> value_meet\<cdot>x\<cdot>y) = (t \<sqsubseteq> x \<and> t \<sqsubseteq> y)"
    proof (induct t rule:Value.take_induct)
      fix n
      show "(Value_take n\<cdot>t \<sqsubseteq> value_meet\<cdot>x\<cdot>y) = (Value_take n\<cdot>t \<sqsubseteq> x \<and> Value_take n\<cdot>t \<sqsubseteq> y)"
      proof (induct n arbitrary: t x y rule:nat_induct)
        case 0 thus ?case by auto
        next
        case (Suc n t x y) thus ?case
          apply -
          apply (cases t, simp)
          apply (cases x, simp)
          apply (cases y, simp)
          apply (fastforce simp add: cfun_below_iff)
          done
      qed
   qed auto
  } note * = this
  show "value_meet\<cdot>x\<cdot>y \<sqsubseteq> x" using * by auto
  show "value_meet\<cdot>x\<cdot>y \<sqsubseteq> y" using * by auto
  fix z
  assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
  thus "z \<sqsubseteq> value_meet\<cdot>x\<cdot>y" using * by auto
qed

instance Value :: Finite_Meet_bifinite_cpo by default


end
