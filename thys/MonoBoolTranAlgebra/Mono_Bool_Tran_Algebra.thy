header {* Algebra of Monotonic Boolean Transformers *}

theory  Mono_Bool_Tran_Algebra
imports Mono_Bool_Tran
begin

text{*
In this section we introduce the {\em algebra of monotonic boolean transformers}.
This is a bounded distributive lattice with a monoid operation, a
dual operator and an iteration operator. The standard model for this
algebra is the set of monotonic boolean transformers introduced
in the previous section. 
*}

class dual = 
  fixes dual::"'a \<Rightarrow> 'a" ("_ ^ o" [81] 80)

class omega = 
  fixes omega::"'a \<Rightarrow> 'a" ("_ ^ \<omega>" [81] 80)

class mbt_algebra = monoid_mult + dual + omega + distrib_lattice + top + bot +
  assumes
      dual_le: "(x \<le> y) = (y ^ o \<le> x ^ o)"
  and dual_dual [simp]: "(x ^ o) ^ o = x"
  and dual_comp: "(x * y) ^ o = x ^ o * y ^ o"
  and dual_one [simp]: "1 ^ o = 1"
  and top_comp [simp]: "\<top> * x = \<top>"
  and inf_comp: "(x \<sqinter> y) * z = (x * z) \<sqinter> (y * z)"
  and le_comp: "x \<le> y \<Longrightarrow> z * x \<le> z * y"
  and dual_neg: "(x * \<top>) \<sqinter> (x ^ o * \<bottom>) = \<bottom>"
  and omega_fix: "x ^ \<omega> = (x * (x ^ \<omega>)) \<sqinter> 1"
  and omega_least: "(x * z) \<sqinter> y \<le> z \<Longrightarrow> (x ^ \<omega>) * y \<le> z"
begin

lemma le_comp_right: "x \<le> y \<Longrightarrow> x * z \<le> y * z"
  apply (cut_tac x = x and y = y and z = z in inf_comp)
  apply (simp add: inf_absorb1)
  apply (subgoal_tac "x * z \<sqinter> (y * z) \<le> y * z")
  apply simp
  by (rule inf_le2)

subclass bounded_lattice
  proof qed

end

instantiation MonoTran :: (complete_boolean_algebra) mbt_algebra
begin

definition 
  dual_MonoTran_def: "x ^ o = Abs_MonoTran (dual_fun (Rep_MonoTran x))"

definition
  omega_MonoTran_def: "x ^ \<omega> = Abs_MonoTran (omega_fun (Rep_MonoTran x))"

instance proof
  fix x y :: "'a MonoTran" show "(x \<le> y) = (y ^ o \<le> x ^ o)"
    apply (simp add: dual_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
    apply (simp add: dual_fun_def le_fun_def compl_le_compl_iff)
    apply safe
    apply simp
    apply (drule_tac x = "-xa" in spec) 
    by simp
next
  fix x :: "'a MonoTran" show "(x ^ o) ^ o = x"
    apply (simp add: dual_MonoTran_def Abs_MonoTran_inverse)
    by (simp add: dual_fun_def Rep_MonoTran_inverse)
next
  fix x y :: "'a MonoTran" show "(x * y) ^ o = x ^ o * y ^ o"
    apply (simp add: dual_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse)
    apply (simp add: dual_fun_def)
    apply (subgoal_tac "(\<lambda>p . - Rep_MonoTran x (Rep_MonoTran y (- p))) = ((\<lambda>p . - Rep_MonoTran x (- p)) \<circ> (\<lambda>p . - Rep_MonoTran y (- p)))")
    apply simp_all
    by (simp add: fun_eq_iff)
next
  show "(1\<Colon>'a MonoTran) ^ o = 1"
    apply (simp add: dual_MonoTran_def one_MonoTran_def Abs_MonoTran_inverse)
    by (simp add: dual_fun_def id_def)

next
  fix x :: "'a MonoTran" show "\<top> * x = \<top>"
    apply (simp add: top_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse)
    by (simp add: top_fun_def o_def)
next
  fix x y z :: "'a MonoTran" show "(x \<sqinter> y) * z = (x * z) \<sqinter> (y * z)"
    apply (simp add: inf_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse)
    by (simp add: inf_fun_def o_def)
next
  fix x y z :: "'a MonoTran" assume A: "x \<le> y" from A show " z * x \<le> z * y"
    apply (simp add: less_eq_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse)
    apply (cut_tac x = z in Rep_MonoTran)
    by (simp add: le_fun_def MonoTran_def mono_def o_def)
next
  fix x :: "'a MonoTran" show "x * \<top> \<sqinter> (x ^ o * \<bottom>) = \<bottom>"
    apply (simp add: inf_MonoTran_def times_MonoTran_def top_MonoTran_def bot_MonoTran_def dual_MonoTran_def Abs_MonoTran_inverse)
    by (simp add: inf_fun_def bot_fun_def dual_fun_def o_def top_fun_def inf_compl_bot)

  fix x :: "'a MonoTran" show "x ^ \<omega> = x * x ^ \<omega> \<sqinter> 1"
    apply (simp add: omega_MonoTran_def times_MonoTran_def inf_MonoTran_def one_MonoTran_def Abs_MonoTran_inverse)
    apply (simp add: omega_fun_def Omega_fun_def)
    apply (subst lfp_unfold, simp_all)
    apply (cut_tac x = x in Rep_MonoTran)
    by (unfold Omega_fun_def [THEN sym], simp)
next
  fix x y z :: "'a MonoTran" assume A: "x * z \<sqinter> y \<le> z" from A show "x ^ \<omega> * y \<le> z"
    apply (simp add: omega_MonoTran_def times_MonoTran_def less_eq_MonoTran_def inf_MonoTran_def one_MonoTran_def Abs_MonoTran_inverse)
    apply (cut_tac f = "Rep_MonoTran x" and g = "Rep_MonoTran y" in lfp_omega)
    apply (cut_tac x = x in Rep_MonoTran)
    apply simp_all
    apply (simp add: lfp_def)
    apply (rule Inf_lower)
    by (simp add: Omega_fun_def)
    
qed

end

context mbt_algebra begin

lemma dual_top [simp]: "\<top> ^ o = \<bottom>"
  apply (rule antisym, simp_all)
  by (subst dual_le, simp)

lemma dual_bot [simp]: "\<bottom> ^ o = \<top>"
  apply (rule antisym, simp_all)
  by (subst dual_le, simp)

lemma dual_inf: "(x \<sqinter> y) ^ o = (x ^ o) \<squnion> (y ^ o)"
  apply (rule antisym, simp_all, safe)
  apply (subst dual_le, simp, safe)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp)
  by (subst dual_le, simp)

lemma dual_sup: "(x \<squnion> y) ^ o = (x ^ o) \<sqinter> (y ^ o)"
  apply (rule antisym, simp_all, safe)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp, safe)
  apply (subst dual_le, simp)
  by (subst dual_le, simp)

lemma sup_comp: "(x \<squnion> y) * z = (x * z) \<squnion> (y * z)"
  apply (subgoal_tac "((x ^ o \<sqinter> y ^ o) * z ^ o) ^ o = ((x ^ o * z ^ o) \<sqinter> (y ^ o * z ^ o)) ^ o")
  apply (simp add: dual_inf dual_comp)
  by (simp add: inf_comp)


lemma dual_eq: "x ^ o = y ^ o \<Longrightarrow> x = y"
  apply (subgoal_tac "(x ^ o) ^ o = (y ^ o) ^ o")
  apply (subst (asm) dual_dual)
  apply (subst (asm) dual_dual)
  by simp_all

lemma dual_neg_top [simp]: "(x ^ o * \<bottom>) \<squnion> (x * \<top>) = \<top>"
  apply (rule dual_eq)
  by(simp add: dual_sup dual_comp dual_neg)

 lemma bot_comp [simp]: "\<bottom> * x = \<bottom>"
   by (rule dual_eq, simp add: dual_comp)

lemma [simp]: "(x * \<top>) * y = x * \<top>" 
  by (simp add: mult_assoc)

lemma [simp]: "(x * \<bottom>) * y = x * \<bottom>" 
  by (simp add: mult_assoc)


lemma gt_one_comp: "1 \<le> x \<Longrightarrow> y \<le> x * y"
  by (cut_tac x = 1 and y = x and z = y in le_comp_right, simp_all)

end

sublocale mbt_algebra < conjunctive "inf" "inf" "times"
done
sublocale mbt_algebra < disjunctive "sup" "sup" "times"
done

context mbt_algebra begin
lemma dual_conjunctive: "x \<in> conjunctive \<Longrightarrow> x ^ o \<in> disjunctive"
  apply (simp add: conjunctive_def disjunctive_def)
  apply safe
  apply (rule dual_eq)
  by (simp add: dual_comp dual_sup)

lemma dual_disjunctive: "x \<in> disjunctive \<Longrightarrow> x ^ o \<in> conjunctive"
  apply (simp add: conjunctive_def disjunctive_def)
  apply safe
  apply (rule dual_eq)
  by (simp add: dual_comp dual_inf)

subsection{*Assertions*}

text{*
Usually, in Kleene algebra with tests or in other progrm algebras, tests or assertions
or assumptions are defined using an existential quantifier. An element of the algebra
is a test if it has a complement with respect to $\bot$ and $1$. In this formalization
assertions can be defined much simpler using the dual operator.
*}

definition
   "assertion = {x . x \<le> 1 \<and> (x * \<top>) \<sqinter> (x ^ o) = x}"

lemma assertion_prop: "x \<in> assertion \<Longrightarrow> (x * \<top>) \<sqinter> 1 = x"
  apply (simp add: assertion_def)
  apply safe
  apply (rule antisym)
  apply simp_all
  proof -
    assume [simp]: "x \<le> 1"
    assume A: "x * \<top> \<sqinter> x ^ o = x"
    have "x * \<top> \<sqinter> 1 \<le> x * \<top> \<sqinter> x ^ o"
      apply simp
      apply (rule_tac y = 1 in order_trans)
      apply simp
      apply (subst dual_le)
      by simp
    also have "\<dots> = x" by (cut_tac A, simp)
    finally show "x * \<top> \<sqinter> 1 \<le> x" .
  next
    assume A: "x * \<top> \<sqinter> x ^ o = x"
    have "x = x * \<top> \<sqinter> x ^ o" by (simp add: A)
    also have "\<dots> \<le> x * \<top>" by simp
    finally show "x \<le> x * \<top>" .
  qed

lemma dual_assertion_prop: "x \<in> assertion \<Longrightarrow> ((x ^ o) * \<bottom>) \<squnion> 1 = x ^ o"
  apply (rule dual_eq)
  by (simp add: dual_sup dual_comp assertion_prop)

lemma assertion_disjunctive: "x \<in> assertion \<Longrightarrow> x \<in> disjunctive"
  apply (simp add: disjunctive_def, safe)
  apply (drule assertion_prop)
  proof -
    assume A: "x * \<top> \<sqinter> 1 = x"
    fix y z::"'a"
    have "x * (y \<squnion> z) = (x * \<top> \<sqinter> 1) * (y \<squnion> z)" by (cut_tac  A, simp)
    also have "\<dots> = (x * \<top>) \<sqinter> (y \<squnion> z)" by (simp add: inf_comp)
    also have "\<dots> = ((x * \<top>) \<sqinter> y) \<squnion> ((x * \<top>) \<sqinter> z)" by (simp add: inf_sup_distrib)
    also have "\<dots> = (((x * \<top>) \<sqinter> 1) * y) \<squnion> (((x * \<top>) \<sqinter> 1) * z)" by (simp add: inf_comp)
    also have "\<dots> = x * y \<squnion> x * z" by (cut_tac  A, simp)
    finally show "x * (y \<squnion> z) = x * y \<squnion> x * z" .
  qed

lemma Abs_MonoTran_injective: "x \<in> MonoTran \<Longrightarrow> y \<in> MonoTran \<Longrightarrow> Abs_MonoTran x = Abs_MonoTran y \<Longrightarrow> x = y"
  apply (subgoal_tac "Rep_MonoTran (Abs_MonoTran x) = Rep_MonoTran (Abs_MonoTran y)")
  apply (subst (asm) Abs_MonoTran_inverse, simp)
  by (subst (asm) Abs_MonoTran_inverse, simp_all)
end

lemma mbta_MonoTran_disjunctive: "Rep_MonoTran ` disjunctive = Apply.disjunctive"
  apply safe
  apply (simp add: disjunctive_def Apply.disjunctive_def, safe)
  apply (simp add: sup_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse Rep_MonoTran_inverse)
    apply (drule_tac x = "Abs_MonoTran (\<lambda> u . y)" in spec)
    apply (drule_tac x = "Abs_MonoTran (\<lambda> u . z)" in spec)
    apply (simp add: Abs_MonoTran_inverse Rep_MonoTran_inverse)
    apply (cut_tac x = "Rep_MonoTran xa \<circ> (\<lambda>u\<Colon>'a. y) \<squnion> (\<lambda>u\<Colon>'a. z)" 
      and y = "((Rep_MonoTran xa \<circ> (\<lambda>u\<Colon>'a. y)) \<squnion> (Rep_MonoTran xa \<circ> (\<lambda>u\<Colon>'a. z)))" in Abs_MonoTran_injective)
    apply simp_all
    apply (simp add: fun_eq_iff sup_fun_def o_def)
    apply (simp add: image_def)
    apply (subgoal_tac "x \<in> MonoTran")
    apply (rule_tac x = "Abs_MonoTran x" in bexI)
    apply (simp add: Abs_MonoTran_inverse)
    apply (simp add: disjunctive_def sup_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse Rep_MonoTran_inverse)
    apply safe
    apply (rule_tac f = "Abs_MonoTran" in fun_eq)
    apply (simp add: Apply.disjunctive_def fun_eq_iff o_def sup_fun_def)
    by (subst MonoTran_def, simp)

lemma assertion_MonoTran: "assertion = Abs_MonoTran ` assertion_fun"
    apply (safe)
    apply (subst assertion_fun_disj_less_one)
    apply (simp add: image_def)
    apply (rule_tac x = "Rep_MonoTran x" in bexI)
    apply (simp add: Rep_MonoTran_inverse)
    apply safe
    apply (drule assertion_disjunctive)
    apply (unfold mbta_MonoTran_disjunctive [THEN sym], simp)
    apply (simp add: assertion_def less_eq_MonoTran_def one_MonoTran_def Abs_MonoTran_inverse)
    apply (simp add: assertion_def)
    by (simp_all add: inf_MonoTran_def less_eq_MonoTran_def 
      times_MonoTran_def dual_MonoTran_def top_MonoTran_def Abs_MonoTran_inverse one_MonoTran_def assertion_fun_dual)

context mbt_algebra begin
lemma assertion_conjunctive: "x \<in> assertion \<Longrightarrow> x \<in> conjunctive"
  apply (simp add: conjunctive_def, safe)
  apply (drule assertion_prop)
  proof -
    assume A: "x * \<top> \<sqinter> 1 = x"
    fix y z::"'a"
    have "x * (y \<sqinter> z) = (x * \<top> \<sqinter> 1) * (y \<sqinter> z)" by (cut_tac  A, simp)
    also have "\<dots> = (x * \<top>) \<sqinter> (y \<sqinter> z)" by (simp add: inf_comp)
    also have "\<dots> = ((x * \<top>) \<sqinter> y) \<sqinter> ((x * \<top>) \<sqinter> z)"
      apply (rule antisym, simp_all, safe)
      apply (rule_tac y = "y \<sqinter> z" in order_trans)
      apply (rule inf_le2)
      apply simp
      apply (rule_tac y = "y \<sqinter> z" in order_trans)
      apply (rule inf_le2)
      apply simp_all
      apply (simp add: inf_assoc)
      apply (rule_tac y = " x * \<top> \<sqinter> y" in order_trans)
      apply (rule inf_le1)
      apply simp
      apply (rule_tac y = " x * \<top> \<sqinter> z" in order_trans)
      apply (rule inf_le2)
      by simp
    also have "\<dots> = (((x * \<top>) \<sqinter> 1) * y) \<sqinter> (((x * \<top>) \<sqinter> 1) * z)" by (simp add: inf_comp)
    also have "\<dots> = (x * y) \<sqinter> (x * z)" by (cut_tac  A, simp)
    finally show "x * (y \<sqinter> z) = (x * y) \<sqinter> (x * z)" .
  qed

lemma dual_assertion_conjunctive: "x \<in> assertion \<Longrightarrow> x ^ o \<in> conjunctive"
  apply (drule assertion_disjunctive)
  by (rule dual_disjunctive, simp)

lemma dual_assertion_disjunct: "x \<in> assertion \<Longrightarrow> x ^ o \<in> disjunctive"
  apply (drule assertion_conjunctive)
  by (rule dual_conjunctive, simp)


lemma [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<sqinter> y \<le> x * y"
  apply (simp add: assertion_def, safe)
  proof -
  assume A: "x \<le> 1"
  assume B: "x * \<top> \<sqinter> x ^ o = x"
  assume C: "y \<le> 1"
  assume D: "y * \<top> \<sqinter> y ^ o = y"
  have "x \<sqinter> y = (x * \<top> \<sqinter> x ^ o) \<sqinter> (y * \<top> \<sqinter> y ^ o)" by (cut_tac B D, simp)
  also have "\<dots> \<le> (x * \<top>) \<sqinter> (((x^o) * (y * \<top>)) \<sqinter> ((x^o) * (y^o)))"
    apply (simp, safe)
      apply (rule_tac y = "x * \<top> \<sqinter> x ^ o" in order_trans)
      apply (rule inf_le1)
      apply simp
      apply (rule_tac y = "y * \<top>" in order_trans)
      apply (rule_tac y = "y * \<top> \<sqinter> y ^ o" in order_trans)
      apply (rule inf_le2)
      apply simp
      apply (rule gt_one_comp)
      apply (subst dual_le, simp add: A)
      apply (rule_tac y = "y ^ o" in order_trans)
      apply (rule_tac y = "y * \<top> \<sqinter> y ^ o" in order_trans)
      apply (rule inf_le2)
      apply simp
      apply (rule gt_one_comp)
      by (subst dual_le, simp add: A)
    also have "... = ((x * \<top>) \<sqinter> (x ^ o)) * ((y * \<top>) \<sqinter> (y ^ o))"
      apply (cut_tac x = x in dual_assertion_conjunctive)
      apply (cut_tac A, cut_tac B, simp add: assertion_def)
      by (simp add: inf_comp conjunctiveD)
    also have "... = x * y"
      by (cut_tac B, cut_tac D, simp)
    finally show "x \<sqinter> y \<le> x * y" .
  qed
    
lemma [simp]: "x \<in> assertion \<Longrightarrow> x * y \<le> y"
  by (unfold assertion_def, cut_tac x = x and y = 1 and z = y in le_comp_right, simp_all)


lemma [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x * y \<le> x"
  apply (subgoal_tac "x * y \<le> (x * \<top>) \<sqinter> (x ^ o)")
  apply (simp add: assertion_def) 
  apply (simp, safe)
  apply (rule le_comp, simp)
  apply (rule_tac y = 1 in order_trans)
  apply (rule_tac y = y in order_trans)
  apply simp
  apply (simp add: assertion_def)
  by (subst dual_le, simp add: assertion_def)

lemma assertion_inf_comp_eq: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<sqinter> y = x * y"
  by (rule antisym, simp_all)

lemma one_right_assertion [simp]: "x \<in> assertion \<Longrightarrow> x * 1 = x"
  apply (drule assertion_prop)
  proof -
    assume A: "x * \<top> \<sqinter> 1 = x"
    have "x * 1 = (x * \<top> \<sqinter> 1) * 1" by (simp add: A)
    also have "\<dots> = x * \<top> \<sqinter> 1" by (simp add: inf_comp)
    also have "\<dots> = x" by (simp add: A)
    finally show ?thesis .
  qed

lemma [simp]: "x \<in> assertion \<Longrightarrow> x \<squnion> 1 = 1"
  by (rule antisym, simp_all add: assertion_def)
  
lemma [simp]: "x \<in> assertion \<Longrightarrow> 1 \<squnion> x = 1"
  by (rule antisym, simp_all add: assertion_def)
  
lemma [simp]: "x \<in> assertion \<Longrightarrow> x \<sqinter> 1 = x"
  by (rule antisym, simp_all add: assertion_def)
  
lemma [simp]: "x \<in> assertion \<Longrightarrow> 1 \<sqinter> x = x"
  by (rule antisym, simp_all add: assertion_def)

lemma [simp]:  "x \<in> assertion \<Longrightarrow> x \<le> x * \<top>"
  by (cut_tac x = 1 and y = \<top> and z = x in le_comp, simp_all)

lemma [simp]: "x \<in> assertion \<Longrightarrow> x \<le> 1"
  by (simp add: assertion_def)

definition
  "neg_assert (x::'a) = (x ^ o * \<bottom>) \<sqinter> 1"
  

lemma sup_uminus[simp]: "x \<in> assertion \<Longrightarrow> x \<squnion> neg_assert x = 1"
  apply (simp add: neg_assert_def)
  apply (simp add: sup_inf_distrib)
  apply (rule antisym, simp_all)
  apply (unfold assertion_def)
  apply safe
  apply (subst dual_le)
  apply (simp add: dual_sup dual_comp)
  apply (subst inf_commute)
  by simp

lemma inf_uminus[simp]: "x \<in> assertion \<Longrightarrow> x \<sqinter> neg_assert x = \<bottom>"
  apply (simp add: neg_assert_def)
  apply (rule antisym, simp_all)
  apply (rule_tac y = "x \<sqinter> (x ^ o * \<bottom>)" in order_trans)
  apply simp
  apply (rule_tac y = "x ^ o * \<bottom> \<sqinter> 1" in order_trans)
  apply (rule inf_le2)
  apply simp
  apply (rule_tac y = "(x * \<top>)  \<sqinter> (x ^ o * \<bottom>)" in order_trans)
  apply simp
  apply (rule_tac y = x in order_trans)
  apply simp_all
  by (simp add: dual_neg)


lemma uminus_assertion[simp]: "x \<in> assertion \<Longrightarrow> neg_assert x \<in> assertion"
  apply (subst assertion_def)
  apply (simp add: neg_assert_def)
  apply (simp add: inf_comp dual_inf dual_comp inf_sup_distrib)
  apply (subst inf_commute)
  by (simp add: dual_neg)

lemma uminus_uminus [simp]: "x \<in> assertion \<Longrightarrow> neg_assert (neg_assert x) = x"
  apply (simp add: neg_assert_def)
  by (simp add: dual_inf dual_comp sup_comp assertion_prop)

lemma dual_comp_neg [simp]: "x ^ o * y \<squnion> (neg_assert x) * \<top> = x ^ o * y"
  apply (simp add: neg_assert_def inf_comp)
  apply (rule antisym, simp_all)
  by (rule le_comp, simp)


lemma [simp]: "(neg_assert x) ^ o * y \<squnion> x * \<top> = (neg_assert x) ^ o * y"
  apply (simp add: neg_assert_def inf_comp dual_inf dual_comp sup_comp)
  by (rule antisym, simp_all)

lemma [simp]: " x * \<top> \<squnion> (neg_assert x) ^ o * y= (neg_assert x) ^ o * y"
  by (simp add: neg_assert_def inf_comp dual_inf dual_comp sup_comp)

lemma inf_assertion [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<sqinter> y \<in> assertion"
  apply (subst assertion_def)
  apply safe
  apply (rule_tac y = x in order_trans)
  apply simp_all
  apply (simp add: assertion_inf_comp_eq)
  proof -
    assume A: "x \<in> assertion"
    assume B: "y \<in> assertion"
    have C: "(x * \<top>) \<sqinter> (x ^ o) = x"
      by (cut_tac A, unfold assertion_def, simp) 
    have D: "(y * \<top>) \<sqinter> (y ^ o) = y"
      by (cut_tac B, unfold assertion_def, simp)
    have "x * y = ((x * \<top>) \<sqinter> (x ^ o)) * ((y * \<top>) \<sqinter> (y ^ o))" by (simp add: C D)
    also have "\<dots> = x * \<top> \<sqinter> ((x ^ o) * ((y * \<top>) \<sqinter> (y ^ o)))" by (simp add: inf_comp)
    also have "\<dots> =  x * \<top> \<sqinter> ((x ^ o) * (y * \<top>)) \<sqinter> ((x ^ o) *(y ^ o))" 
      by (cut_tac A, cut_tac x = x in dual_assertion_conjunctive, simp_all add: conjunctiveD inf_assoc)
    also have "\<dots> = (((x * \<top>) \<sqinter> (x ^ o)) * (y * \<top>)) \<sqinter> ((x ^ o) *(y ^ o))"
      by (simp add: inf_comp)
    also have "\<dots> = (x * y * \<top>)  \<sqinter> ((x * y) ^ o)" by (simp add: C mult_assoc dual_comp)
    finally show "(x * y * \<top>)  \<sqinter> ((x * y) ^ o) = x * y" by simp
  qed

lemma comp_assertion [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x * y \<in> assertion"
  by (subst assertion_inf_comp_eq [THEN sym], simp_all)


lemma sup_assertion [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<squnion> y \<in> assertion"
  apply (subst assertion_def)
  apply safe
  apply (unfold assertion_def)
  apply simp
  apply safe
  proof -
    assume [simp]: "x \<le> 1"
    assume [simp]: "y \<le> 1"
    assume A: "x * \<top> \<sqinter> x ^ o = x"
    assume B: "y * \<top> \<sqinter> y ^ o = y"
    have "(y * \<top>) \<sqinter> (x ^ o) \<sqinter> (y ^ o) = (x ^ o) \<sqinter> (y * \<top>) \<sqinter> (y ^ o)" by (simp add: inf_commute)
    also have "\<dots> = (x ^ o) \<sqinter> ((y * \<top>) \<sqinter> (y ^ o))" by (simp add: inf_assoc)
    also have "\<dots> = (x ^ o) \<sqinter> y" by (simp add: B)
    also have "\<dots> = y"
      apply (rule antisym, simp_all)
      apply (rule_tac y = 1 in order_trans)
      apply simp
      by (subst dual_le, simp)
    finally have [simp]: "(y * \<top>) \<sqinter> (x ^ o) \<sqinter> (y ^ o) = y" .
    have "x * \<top> \<sqinter> (x ^ o) \<sqinter> (y ^ o) = x \<sqinter> (y ^ o)"  by (simp add: A)
    also have "\<dots> = x"
      apply (rule antisym, simp_all)
      apply (rule_tac y = 1 in order_trans)
      apply simp
      by (subst dual_le, simp)
    finally have [simp]: "x * \<top> \<sqinter> (x ^ o) \<sqinter> (y ^ o) = x" .
    have "(x \<squnion> y) * \<top> \<sqinter> (x \<squnion> y) ^ o = (x * \<top> \<squnion> y * \<top>) \<sqinter> ((x ^ o) \<sqinter> (y ^ o))" by (simp add: sup_comp dual_sup)
    also have "\<dots> = x \<squnion> y" by (simp add: inf_sup_distrib inf_assoc [THEN sym])
    finally show "(x \<squnion> y) * \<top> \<sqinter> (x \<squnion> y) ^ o = x \<squnion> y" .
  qed

lemma [simp]: "x \<in> assertion \<Longrightarrow> x * x = x"
  by (simp add: assertion_inf_comp_eq [THEN sym])

lemma [simp]: "x \<in> assertion \<Longrightarrow> (x ^ o) * (x ^ o) = x ^ o"
  apply (rule dual_eq)
  by (simp add: dual_comp assertion_inf_comp_eq [THEN sym])

lemma [simp]: "x \<in> assertion \<Longrightarrow> x * (x ^ o) = x"
  proof -
    assume A: "x \<in> assertion"
    have B: "x * \<top> \<sqinter> (x ^ o) = x" by (cut_tac A, unfold assertion_def, simp)
    have "x * x ^ o = (x * \<top> \<sqinter> (x ^ o)) * x ^ o" by (simp add: B)
    also have "\<dots> = x * \<top> \<sqinter> (x ^ o)" by (cut_tac A, simp add: inf_comp)
    also have "\<dots> = x" by (simp add: B)
    finally show ?thesis .
  qed

lemma [simp]: "x \<in> assertion \<Longrightarrow> (x ^ o) * x = x ^ o"
  apply (rule dual_eq)
  by (simp add: dual_comp)


lemma [simp]: "\<bottom> \<in> assertion"
  by (unfold assertion_def, simp)

lemma [simp]: "1 \<in> assertion"
  by (unfold assertion_def, simp)


subsection {*Weakest precondition of true*}

definition
  "wpt x = (x * \<top>) \<sqinter> 1"

lemma wpt_is_assertion [simp]: "wpt x \<in> assertion"
  apply (unfold wpt_def assertion_def, safe)
  apply simp
  apply (simp add: inf_comp dual_inf dual_comp inf_sup_distrib)
  apply (rule antisym)
  by (simp_all add: dual_neg)

lemma wpt_comp: "(wpt x) * x = x"
  apply (simp add: wpt_def inf_comp)
  apply (rule antisym, simp_all)
  by (cut_tac x = 1 and y = \<top> and z = x in le_comp, simp_all)

lemma wpt_comp_2: "wpt (x * y) = wpt (x * (wpt y))"
  by (simp add: wpt_def inf_comp mult_assoc)

lemma wpt_assertion [simp]: "x \<in> assertion \<Longrightarrow> wpt x = x"
  by (simp add: wpt_def assertion_prop)

lemma wpt_le_assertion: "x \<in> assertion \<Longrightarrow> x * y = y \<Longrightarrow> wpt y \<le> x"
  apply (simp add: wpt_def)
  proof -
    assume A: "x \<in> assertion"
    assume B: "x * y = y"
    have "y * \<top> \<sqinter> 1 = x * (y * \<top>) \<sqinter> 1" by (simp add: B mult_assoc [THEN sym])
    also have "\<dots> \<le> x * \<top> \<sqinter> 1" 
      apply simp
      apply (rule_tac y = "x * (y * \<top>)" in order_trans)
      apply simp_all
      by (rule le_comp, simp)
    also have "\<dots> = x" by (cut_tac A, simp add: assertion_prop)
    finally show "y * \<top> \<sqinter> 1 \<le> x" .
  qed

lemma wpt_choice: "wpt (x \<sqinter> y) = wpt x \<sqinter> wpt y"
  apply (simp add: wpt_def inf_comp)
  proof -
    have "x * \<top> \<sqinter> 1 \<sqinter> (y * \<top> \<sqinter> 1) = x * \<top> \<sqinter> ((y * \<top> \<sqinter> 1) \<sqinter> 1)" apply (subst inf_assoc) by (simp add: inf_commute)
    also have "... = x * \<top> \<sqinter> (y * \<top> \<sqinter> 1)" by (subst inf_assoc, simp)
    also have "... = (x * \<top>) \<sqinter> (y * \<top>) \<sqinter> 1" by (subst inf_assoc, simp)
    finally show "x * \<top> \<sqinter> (y * \<top>) \<sqinter> 1 = x * \<top> \<sqinter> 1 \<sqinter> (y * \<top> \<sqinter> 1)" by simp
  qed
end 

context lattice begin
lemma [simp]: "x \<le> y \<Longrightarrow> x \<sqinter> y = x"
  by (simp add: inf_absorb1)
end


context mbt_algebra begin

lemma wpt_dual_assertion_comp: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> wpt ((x ^ o) * y) = (neg_assert x) \<squnion> y"
  apply (simp add: wpt_def neg_assert_def)
  proof -
    assume A: "x \<in> assertion"
    assume B: "y \<in> assertion"
    have C: "((x ^ o) * \<bottom>) \<squnion> 1 = x ^ o"
      by (rule dual_assertion_prop, rule A)
    have "x ^ o * y * \<top> \<sqinter> 1 = (((x ^ o) * \<bottom>) \<squnion> 1) * y * \<top> \<sqinter> 1" by (simp add: C)
    also have "\<dots> = ((x ^ o) * \<bottom> \<squnion> (y * \<top>)) \<sqinter> 1" by (simp add: sup_comp)
    also have "\<dots> = (((x ^ o) * \<bottom>) \<sqinter> 1) \<squnion> ((y * \<top>) \<sqinter> 1)" by (simp add: inf_sup_distrib2)
    also have "\<dots> = (((x ^ o) * \<bottom>) \<sqinter> 1) \<squnion> y" by (cut_tac B, drule assertion_prop, simp)
    finally show "x ^ o * y * \<top> \<sqinter> 1 = (((x ^ o) * \<bottom>) \<sqinter> 1) \<squnion> y" .
  qed

lemma le_comp_left_right: "x \<le> y \<Longrightarrow> u \<le> v \<Longrightarrow> x * u \<le> y * v"
  apply (rule_tac y = "x * v" in order_trans)
  apply (rule le_comp, simp)
  by (rule le_comp_right, simp)

lemma wpt_dual_assertion: "x \<in> assertion \<Longrightarrow> wpt (x ^ o) = 1"
  apply (simp add: wpt_def)
  apply (rule antisym)
  apply simp_all
  apply (cut_tac x = 1 and y = "x ^ o" and u = 1 and v = \<top> in le_comp_left_right)
  apply simp_all
  apply (subst dual_le)
  by simp

lemma assertion_commute: "x \<in> assertion \<Longrightarrow> y \<in> conjunctive \<Longrightarrow> y * x = wpt(y * x) * y"
  apply (simp add: wpt_def)
  apply (simp add: inf_comp)
  apply (drule_tac x = y and y = "x * \<top>" and z = 1 in conjunctiveD)
  by (simp add: mult_assoc [THEN sym] assertion_prop)


lemma wpt_mono: "x \<le> y \<Longrightarrow> wpt x \<le> wpt y"
  apply (simp add: wpt_def)
  apply (rule_tac y = "x * \<top>" in order_trans, simp_all)
  by (rule le_comp_right, simp)

lemma "a \<in> conjunctive \<Longrightarrow> x * a \<le> a * y \<Longrightarrow> (x ^ \<omega>) * a \<le> a * (y ^ \<omega>)"
  apply (rule omega_least)
  apply (simp add: mult_assoc [THEN sym])
  apply (rule_tac y = "a * y * y ^ \<omega> \<sqinter> a" in order_trans)
  apply (simp)
  apply (rule_tac y = "x * a * y ^ \<omega>" in order_trans, simp_all)
  apply (rule le_comp_right, simp)
  apply (simp add: mult_assoc)
  apply (subst (2) omega_fix)
  by (simp add: conjunctiveD)

lemma [simp]: "x \<le> 1 \<Longrightarrow> y * x \<le> y"
  by (cut_tac x = x and y = 1 and z = y in le_comp, simp_all)

lemma [simp]: "x \<le> x * \<top>"
  by (cut_tac x = 1 and y = \<top> and z = x in le_comp, simp_all)

lemma [simp]: "x * \<bottom> \<le> x"
  by (cut_tac x = \<bottom> and y = 1 and z = x in le_comp, simp_all)

end

subsection{*Monotonic Boolean trasformers algebra with post condition statement*}

class post_mbt_algebra = mbt_algebra +
  fixes post :: "'a \<Rightarrow> 'a"
  assumes post_1: "(post x) * x * \<top> = \<top>"
  and post_2: "y * x * \<top> \<sqinter> (post x) \<le> y"

instantiation MonoTran :: (complete_boolean_algebra) post_mbt_algebra
begin
definition
  post_MonoTran_def: "post x = Abs_MonoTran (\<lambda> q . if (Rep_MonoTran x) \<top> \<le> q then \<top> else \<bottom>)"
instance proof
have op_p_MonoTran [simp]: "\<And>p::'a . op \<sqinter> p \<in> MonoTran"
   apply (simp add: MonoTran_def mono_def, safe)
   by (rule_tac y = x in order_trans, simp_all)
have [simp]: "\<And>p :: 'a .  (\<lambda>q . if p \<le> q then \<top> else \<bottom>) \<in> MonoTran"
   apply (simp add: MonoTran_def mono_def, safe)
   apply (subgoal_tac "p \<le> y", simp)
   by (rule_tac y = x in order_trans, simp_all)
  fix x :: "'a MonoTran" show "post x * x * \<top> = \<top>"
    apply (simp add: post_MonoTran_def times_MonoTran_def top_MonoTran_def 
      Abs_MonoTran_inverse Rep_MonoTran_inverse)
   by (simp add: fun_eq_iff top_fun_def o_def)
 
  fix x y :: "'a MonoTran" show "y * x * \<top> \<sqinter> post x \<le> y"
    apply (simp add: post_MonoTran_def times_MonoTran_def top_MonoTran_def Abs_MonoTran_inverse 
      Rep_MonoTran_inverse inf_MonoTran_def less_eq_MonoTran_def)
    apply (simp add: le_fun_def bot_fun_def inf_fun_def top_fun_def o_def)
    apply safe
    apply (rule_tac f = "Rep_MonoTran y" in monoD)
    apply (cut_tac x = y in  Rep_MonoTran)
    by (simp_all)
qed
   
end

subsection{*Complete monotonic Boolean transformers algebra*}

class complete_mbt_algebra = post_mbt_algebra + complete_distrib_lattice +
  assumes Inf_comp: "(Inf X) * z = (INF x : X . (x * z))"


instantiation MonoTran :: (complete_boolean_algebra) complete_mbt_algebra
begin

instance proof
  fix z :: "'a MonoTran" fix X show "Inf X * z = (INF x:X. x * z)"
    apply (simp add: INFI_def Inf_MonoTran_def times_MonoTran_def Inf_comp_fun Abs_MonoTran_inverse sup_Inf_distrib1)
    apply (subgoal_tac "{g\<Colon>'a \<Rightarrow> 'a. \<exists>m\<Colon>'a MonoTran\<in>X. g = Rep_MonoTran m \<circ> Rep_MonoTran z} = Rep_MonoTran ` (\<lambda>x\<Colon>'a MonoTran. Abs_MonoTran (Rep_MonoTran x \<circ> Rep_MonoTran z)) ` X")
    apply simp
    apply (simp add: image_def, safe)
    apply (rule_tac x = "Abs_MonoTran (Rep_MonoTran m \<circ> Rep_MonoTran z)" in exI)
    apply (simp_all add: Abs_MonoTran_inverse)
    by auto
qed
end

context complete_mbt_algebra begin
lemma dual_Inf: "(Inf X) ^ o = (SUP x: X . x ^ o)"
  apply (rule antisym)
  apply (simp_all add: SUPR_def)
  apply (subst dual_le, simp)
  apply (rule Inf_greatest)
  apply (subst dual_le, simp)
  apply (rule Sup_upper, simp)
  apply (rule Sup_least, safe)
  apply (subst dual_le, simp)
  by (rule Inf_lower, simp)

lemma dual_Sup: "(Sup X) ^ o = (INF x: X . x ^ o)"
  apply (rule antisym)
  apply (simp_all add: INFI_def)
  apply (rule Inf_greatest, safe)
  apply (subst dual_le, simp)
  apply (rule Sup_upper, simp)
  apply (subst dual_le, simp)
  apply (rule Sup_least)
  apply (subst dual_le, simp)
  by (rule Inf_lower, simp)

lemma INFI_comp: "(INFI A f) * z = (INF a : A . (f a) * z)"
  apply (simp add: INFI_def Inf_comp)
  apply (subgoal_tac "((\<lambda>x\<Colon>'a. x * z) ` f ` A) = ((\<lambda>a\<Colon>'b. f a * z) ` A)")
  by auto

lemma dual_INFI: "(INFI A f) ^ o = (SUP a : A . (f a) ^ o)"
  apply (simp add: INFI_def dual_Inf SUPR_def)
  apply (subgoal_tac "(dual ` f ` A) = ((\<lambda>a\<Colon>'b. f a ^ o) ` A)")
  by auto

lemma dual_SUPR: "(SUPR A f) ^ o = (INF a : A . (f a) ^ o)"
  apply (simp add: INFI_def dual_Sup SUPR_def)
  apply (subgoal_tac "(dual ` f ` A) = ((\<lambda>a\<Colon>'b. f a ^ o) ` A)")
  by auto

lemma Sup_comp: "(Sup X) * z = (SUP x : X . (x * z))"
  apply (rule dual_eq)
  by (simp add: dual_comp dual_Sup dual_SUPR INFI_comp)

lemma SUPR_comp: "(SUPR A f) * z = (SUP a : A . (f a) * z)"
  apply (simp add: SUPR_def Sup_comp)
  apply (subgoal_tac "((\<lambda>x\<Colon>'a. x * z) ` f ` A) = ((\<lambda>a\<Colon>'b. f a * z) ` A)")
  by auto


lemma Sup_assertion [simp]: "X \<subseteq> assertion \<Longrightarrow> Sup X \<in> assertion"
  apply (unfold assertion_def)
  apply safe
  apply (rule Sup_least)
  apply blast
  apply (simp add: Sup_comp dual_Sup SUPR_def inf_Sup_distrib2)
  apply (subgoal_tac "((\<lambda>y . y \<sqinter> INFI X dual) ` (\<lambda>x . x * \<top>) ` X) = X")
  apply simp
  proof -
    assume A: "X \<subseteq> {x. x \<le> 1 \<and> x * \<top> \<sqinter> x ^ o = x}"
    have B [simp]: "!! x . x \<in> X \<Longrightarrow>  x * \<top> \<sqinter> (INFI X dual) = x"
      proof -
        fix x
        assume C: "x \<in> X"
        have "x * \<top> \<sqinter> INFI X dual = x * \<top> \<sqinter> (x ^ o \<sqinter> INFI X dual)"
          apply (subgoal_tac "INFI X dual = (x ^ o \<sqinter> INFI X dual)", simp)
          apply (rule antisym, simp_all)
          by (unfold INFI_def, rule Inf_lower, cut_tac C, simp)
        also have "\<dots> = x \<sqinter> INFI X dual" by (unfold  inf_assoc [THEN sym], cut_tac A, cut_tac C, auto)
        also have "\<dots> = x"
          apply (rule antisym, simp_all)
          apply (simp add: INFI_def)
          apply (rule Inf_greatest, safe)
          apply (cut_tac A C)
          apply (rule_tac y = 1 in order_trans)
          apply auto[1]
          by (subst dual_le, auto)
        finally show "x * \<top> \<sqinter> INFI X dual = x" .
      qed
      show "(\<lambda>y. y \<sqinter> INFI X dual) ` (\<lambda>x . x * \<top>) ` X = X"
        by (unfold image_def, auto)
    qed

lemma Sup_range_assertion [simp]: "(!!w . p w \<in> assertion) \<Longrightarrow> Sup (range p) \<in> assertion"
  by (rule Sup_assertion, auto)

lemma Sup_less_assertion [simp]: "(!!w . p w \<in> assertion) \<Longrightarrow> Sup_less p w \<in> assertion"
  by (unfold Sup_less_def, rule Sup_assertion, auto)

theorem omega_lfp: 
  "x ^ \<omega> * y = lfp (\<lambda> z . (x * z) \<sqinter> y)"
  apply (rule antisym)
  apply (rule lfp_greatest)
  apply (drule omega_least, simp)
  apply (rule lfp_lowerbound)
  apply (subst (2) omega_fix)
  by (simp add: inf_comp mult_assoc)

end

end
