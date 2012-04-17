header {* Monotonic Boolean Transformers *}

theory  Mono_Bool_Tran
imports "../LatticeProperties/Complete_Lattice_Prop"
   "../LatticeProperties/Conj_Disj"
begin

text{*
The type of monotonic transformers is the type associated to the set of monotonic
functions from a partially ordered set (poset) to itself. The type of monotonic
transformers with the pointwise extended order is also a poset. 
The monotonic transformers with composition and identity 
form a monoid, and the monoid operation is compatible with the order.

Gradually we extend the algebraic structure of monotonic transformers to
lattices, and complete lattices. We also introduce a dual operator 
($(\mathsf{dual}\;f) p = - f (-p)$) on monotonic transformers over
a boolean algebra. However the monotonic transformers over a boolean
algebra are not closed to the pointwise extended negation operator.

Finally we introduce an iteration operator on monotonic transformers
over a complete lattice.
*}

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70)
  and sup (infixl "\<squnion>" 65)


typedef ('a::order) MonoTran = "{f::'a \<Rightarrow> 'a . mono f}"
  apply (rule_tac x = id in exI)
  by (simp add: mono_def)

lemma [simp]: "Rep_MonoTran x \<in> MonoTran"
  by (rule Rep_MonoTran)

instantiation MonoTran :: (order) order
begin

definition
  less_eq_MonoTran_def: "(x \<le> y) = (Rep_MonoTran x \<le> Rep_MonoTran y)"

definition
  less_MonoTran_def: "((x::'a MonoTran) < y) = (x \<le> y \<and> \<not> y \<le> x)"

instance proof
  fix x y :: "'a MonoTran" show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_MonoTran_def)
next
  fix x :: "'a MonoTran" show "x \<le> x"
    by (simp add: less_eq_MonoTran_def)
next
  fix x y z :: "'a MonoTran" assume A: "x \<le> y" assume B: "y \<le> z" from A B show "x \<le> z"
    by (simp add: less_eq_MonoTran_def)
next
  fix x y :: "'a MonoTran" assume A: "x \<le> y" assume B: "y \<le> x" from A B show "x = y"
    apply (simp add: less_eq_MonoTran_def)
    apply (subgoal_tac "Abs_MonoTran (Rep_MonoTran y) = Abs_MonoTran (Rep_MonoTran x)")
    apply (subst (asm) Rep_MonoTran_inverse, subst (asm) Rep_MonoTran_inverse, simp)
    by simp
qed
end

lemma [simp]: "(\<lambda> u . v) \<in> MonoTran"
  by (simp add: MonoTran_def mono_def)

lemma comp_MonoTran [simp]: "f \<in> MonoTran \<Longrightarrow> g \<in> MonoTran \<Longrightarrow> f o g \<in> MonoTran"
  by (simp add: MonoTran_def mono_def)

lemma [simp]: "id \<in> MonoTran"
  by (simp add: MonoTran_def mono_def)

instantiation MonoTran :: (order) monoid_mult
begin

definition
  one_MonoTran_def: "1 = Abs_MonoTran id"

definition
  times_MonoTran_def: "x * y = Abs_MonoTran (Rep_MonoTran x  o Rep_MonoTran y)"

instance proof
  fix a b c :: "'a MonoTran" show "a * b * c = a * (b * c)"
    by (simp add: times_MonoTran_def Abs_MonoTran_inverse o_assoc)
  next
  fix a :: "'a MonoTran" show "1 * a = a"
    by (simp add: one_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse Rep_MonoTran_inverse)
  next
  fix a :: "'a MonoTran" show "a * 1 = a"
    by (simp add: one_MonoTran_def times_MonoTran_def Abs_MonoTran_inverse Rep_MonoTran_inverse)
qed
end

lemma [simp]: "\<bottom> \<in> MonoTran"
  by (simp add: MonoTran_def mono_def bot_fun_def)


class order_bot = order + bot

instantiation MonoTran :: (order_bot) bot
begin

definition
  bot_MonoTran_def: "\<bottom> = Abs_MonoTran \<bottom>"

instance proof
  fix x :: "'a MonoTran" show "\<bottom> \<le> x"
    by (simp add: bot_MonoTran_def Abs_MonoTran_inverse less_eq_MonoTran_def)
qed
end

lemma [simp]: "\<top> \<in> MonoTran"
  by (simp add: MonoTran_def mono_def top_fun_def)

class order_top = order + top

instantiation MonoTran :: (order_top) top
begin

definition
  top_MonoTran_def: "\<top> = Abs_MonoTran \<top>"

instance proof
  fix x :: "'a MonoTran" show "x \<le> \<top>"
    by (simp add: top_MonoTran_def Abs_MonoTran_inverse less_eq_MonoTran_def)
qed
end

lemma inf_MonoTran [simp]: "f \<in> MonoTran \<Longrightarrow> g \<in> MonoTran \<Longrightarrow> f \<sqinter> g \<in> MonoTran"
  apply (simp add: MonoTran_def mono_def inf_fun_def)
  apply safe
  apply (rule_tac y = "f x" in order_trans)
  apply simp_all
  apply (rule_tac y = "g x" in order_trans)
  by simp_all

lemma sup_MonoTran [simp]: "f \<in> MonoTran \<Longrightarrow> g \<in> MonoTran \<Longrightarrow> f \<squnion> g \<in> MonoTran"
  apply (simp add: MonoTran_def mono_def sup_fun_def)
  apply safe
  apply (rule_tac y = "f y" in order_trans)
  apply simp_all
  apply (rule_tac y = "g y" in order_trans)
  by simp_all

text{*
The type of monotonic transformers on a lattice is also a lattice
*}

instantiation MonoTran :: (lattice) lattice
begin
definition
  inf_MonoTran_def: "x \<sqinter> y = Abs_MonoTran (Rep_MonoTran x \<sqinter> Rep_MonoTran y)"

definition
  sup_MonoTran_def: "x \<squnion> y = Abs_MonoTran (Rep_MonoTran x \<squnion> Rep_MonoTran y)"

instance proof
  fix x y :: "'a MonoTran" show "x \<sqinter> y \<le> x"
    by (simp add: inf_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse) 
  fix x y :: "'a MonoTran" show "x \<sqinter> y \<le> y"
    by (simp add: inf_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
  fix x y z :: "'a MonoTran" assume A: "x \<le> y" assume B: "x \<le> z" from A B show "x \<le> y \<sqinter> z"
    by (simp add: inf_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
next
  fix x y :: "'a MonoTran" show "x \<le> x \<squnion> y"
    by (simp add: sup_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse) 
  fix x y :: "'a MonoTran" show "y \<le> x \<squnion> y"
    by (simp add: sup_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
  fix x y z :: "'a MonoTran" assume A: "y \<le> x" assume B: "z \<le> x" from A B show "y \<squnion> z \<le> x"
    by (simp add: sup_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
qed

end

instantiation MonoTran :: (distrib_lattice) distrib_lattice
begin
instance proof
  fix x y z :: "'a MonoTran" show "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    by (simp add: sup_MonoTran_def inf_MonoTran_def sup_inf_distrib Abs_MonoTran_inverse)
qed

end

context complete_lattice begin
subclass order_top proof qed
end

context complete_lattice begin
subclass order_bot proof qed
end

lemma Sup_MonoTran [simp]: "X \<subseteq> MonoTran \<Longrightarrow> Sup X \<in> MonoTran"
  apply (simp add: MonoTran_def mono_def Sup_fun_def)
  apply safe
  apply (rule SUP_least)
  apply (rule_tac y = "f y" in order_trans) 
  apply blast
  by (rule SUP_upper, blast)


lemma Inf_MonoTran [simp]: "X \<subseteq> MonoTran \<Longrightarrow> Inf X \<in> MonoTran"
  apply (simp add: MonoTran_def mono_def Inf_fun_def)
  apply safe
  apply (rule INF_greatest)
  apply (rule_tac y = "f x" in order_trans) 
  apply (rule INF_lower, blast)
  by blast

lemma [simp]: "Rep_MonoTran ` A \<subseteq> MonoTran"
  apply (rule subsetI)
  apply (simp add: image_def, safe)
  by (rule Rep_MonoTran) 

instantiation MonoTran :: (complete_lattice) complete_lattice
begin

definition
  Sup_MonoTran_def: "Sup X = Abs_MonoTran (Sup (Rep_MonoTran`X))"

definition
  Inf_MonoTran_def: "Inf X = Abs_MonoTran (Inf (Rep_MonoTran`X))"

instance proof
  fix x :: "'a MonoTran" fix A assume A: "x \<in> A" from A show "Inf A \<le> x"
    apply (simp add: Inf_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
    by (rule Inf_lower, blast)
next
  fix z :: "'a MonoTran" fix A assume A: "\<And> x . x \<in> A \<Longrightarrow> z \<le> x" from A show "z \<le> Inf A"
    apply (simp add: Inf_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
    by (rule Inf_greatest, blast)
next
  fix x :: "'a MonoTran" fix A assume A: "x \<in> A" from A show "x \<le> Sup A"
    apply (simp add: Sup_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
    by (rule Sup_upper, blast)
next
  fix z :: "'a MonoTran" fix A assume A: "\<And> x . x \<in> A \<Longrightarrow> x \<le> z" from A show "Sup A \<le> z"
    apply (simp add: Sup_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse)
    by (rule Sup_least, blast)
next
qed
end

instantiation MonoTran :: (complete_distrib_lattice) complete_distrib_lattice
begin
instance proof
  fix x :: "'a MonoTran" fix Y :: "'a MonoTran set" show "x \<sqinter> Sup Y = (SUP y:Y. x \<sqinter> y)"
    apply (simp add: SUP_def Sup_MonoTran_def inf_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse inf_Sup)
    apply (simp add: image_def)
    apply (subgoal_tac "{y . \<exists>xa . (\<exists>x \<in> Y . xa = Rep_MonoTran x) \<and> y = Rep_MonoTran x \<sqinter> xa} 
       = {y . \<exists>xa . (\<exists>xb\<Colon>'a MonoTran\<in>Y. xa = Abs_MonoTran (Rep_MonoTran x \<sqinter> Rep_MonoTran xb)) \<and> y = Rep_MonoTran xa}")
    apply (simp, safe)
    apply (rule_tac x = "Abs_MonoTran (Rep_MonoTran x \<sqinter> Rep_MonoTran xb)" in exI)
    by (simp_all add: Abs_MonoTran_inverse, auto)
next
  fix x :: "'a MonoTran" fix Y show "x \<squnion> Inf Y = (INF y:Y. x \<squnion> y)"
    apply (simp add: INF_def Inf_MonoTran_def sup_MonoTran_def less_eq_MonoTran_def Abs_MonoTran_inverse sup_Inf)
    apply (simp add: image_def)
    apply (subgoal_tac "{y . \<exists>xa . (\<exists>x \<in> Y . xa = Rep_MonoTran x) \<and> y = Rep_MonoTran x \<squnion> xa} 
      = {y . \<exists>xa . (\<exists>xb \<in>Y. xa = Abs_MonoTran (Rep_MonoTran x \<squnion> Rep_MonoTran xb)) \<and> y = Rep_MonoTran xa}")
    apply (simp, safe)
    apply (rule_tac x = "Abs_MonoTran (Rep_MonoTran x \<squnion> Rep_MonoTran xb)" in exI)
    by (simp_all add: Abs_MonoTran_inverse, auto)
qed
end


definition
  "dual_fun (f::'a::boolean_algebra \<Rightarrow> 'a) = (\<lambda> p . - (f (- p)))"

lemma [simp]: "f \<in> MonoTran \<Longrightarrow> dual_fun f \<in> MonoTran"
  by (simp add: MonoTran_def dual_fun_def mono_def)

definition
  "Omega_fun f g = (\<lambda> h . (f o h) \<sqinter> g)"

definition 
  "omega_fun f = lfp (Omega_fun f id)"

definition
  "star_fun f = gfp (Omega_fun f id)"

lemma [simp]: "f \<in> MonoTran \<Longrightarrow> mono f"
  by (unfold MonoTran_def, simp)

lemma [simp]: "f \<in> MonoTran \<Longrightarrow> Omega_fun f g \<in> MonoTran"
  apply (simp add: Omega_fun_def mono_def MonoTran_def)
  apply safe
  apply (simp add: le_fun_def inf_fun_def id_def o_def)
  apply safe
  apply (rule_tac y = "f (x xa)" in order_trans)
  by simp_all

lemma [simp]: "f \<in> MonoTran \<Longrightarrow> omega_fun f \<in> MonoTran" 
  apply (unfold omega_fun_def MonoTran_def Omega_fun_def, simp)
  apply (rule lfp_mono)
  apply (simp add: mono_mono_def mono_def)
  apply safe
  apply (rule_tac y = "f \<circ> x" in order_trans)
  apply simp
  apply (simp add: le_fun_def inf_fun_def id_def o_def)
  apply (rule_tac y = "f (fa x)" in order_trans)
  apply simp_all
  apply (rule_tac y = "x" in order_trans)
  by simp_all

lemma [simp]: "f \<in> MonoTran \<Longrightarrow> star_fun f \<in> MonoTran" 
  apply (unfold star_fun_def MonoTran_def Omega_fun_def, simp)
  apply (rule gfp_mono)
  apply (simp add: mono_mono_def mono_def)
  apply safe
  apply (rule_tac y = "f \<circ> x" in order_trans)
  apply simp
  apply (simp add: le_fun_def inf_fun_def id_def o_def)
  apply (rule_tac y = "f (fa x)" in order_trans)
  apply simp_all
  apply (rule_tac y = "x" in order_trans)
  by simp_all

lemma Sup_comp_fun: "(Sup M) o f = Sup {g . \<exists> m \<in> M . g = m o f}"
  apply (simp add: fun_eq_iff Sup_fun_def o_def)
  apply safe
  apply (simp add: SUP_def image_def)
  apply (subgoal_tac "{y . \<exists>fa \<in> M . y = fa (f x)} = {y . \<exists>fa . (\<exists>m \<in> M . \<forall>x . fa x = m (f x)) \<and> y = fa x}")
  by auto

lemma Inf_comp_fun: "(Inf M) o f = Inf {g . \<exists> m \<in> M . g = m o f}"
  apply (simp add: fun_eq_iff Inf_fun_def o_def)
  apply safe
  apply (simp add: INF_def image_def)
  apply (subgoal_tac "{y . \<exists>fa \<in> M . y = fa (f x)} = {y . \<exists>fa . (\<exists>m \<in> M . \<forall>x\<Colon>'a. fa x = m (f x)) \<and> y = fa x}")
  by auto

lemma lfp_omega_lowerbound: "f \<in> MonoTran \<Longrightarrow> Omega_fun f g A \<le> A \<Longrightarrow> (omega_fun f) o g \<le> A"
  apply (simp add: omega_fun_def)
  apply (rule_tac P = "\<lambda> x . x \<circ> g \<le> A" and f = "Omega_fun f id" in lfp_ordinal_induct)
  apply simp_all
  apply (simp add: le_fun_def o_def inf_fun_def id_def Omega_fun_def)
  apply auto
  apply (rule_tac y = "f (A x) \<sqinter> g x" in order_trans)
  apply simp_all
  apply (rule_tac y = "f (S (g x))" in order_trans)
  apply simp_all
  apply (simp add: mono_def MonoTran_def)
  apply (unfold Sup_comp_fun)
  apply (rule Sup_least)
  by auto

lemma gfp_omega_upperbound: "f \<in> MonoTran \<Longrightarrow> A \<le> Omega_fun f g A \<Longrightarrow> A \<le> (star_fun f) o g"
  apply (simp add: star_fun_def)
  apply (rule_tac P = "\<lambda> x . A \<le> x \<circ> g" and f = "Omega_fun f id" in gfp_ordinal_induct)
  apply simp_all
  apply (simp add: le_fun_def o_def inf_fun_def id_def Omega_fun_def)
  apply auto
  apply (rule_tac y = "f (A x) \<sqinter> g x" in order_trans)
  apply simp_all
  apply (rule_tac y = "f (A x)" in order_trans)
  apply simp_all
  apply (simp add: mono_def MonoTran_def)
  apply (unfold Inf_comp_fun)
  apply (rule Inf_greatest)
  by auto

lemma lfp_omega_greatest: "(\<forall> u . Omega_fun f g u \<le> u \<longrightarrow> A \<le> u) \<Longrightarrow> A \<le> (omega_fun f) o g"
  apply (unfold omega_fun_def)
  apply (simp add: lfp_def)
  apply (unfold Inf_comp_fun)
  apply (rule Inf_greatest)
  apply simp
  apply safe
  apply (drule_tac x = "m o g" in spec)
  by (simp add: le_fun_def o_def inf_fun_def Omega_fun_def)

lemma gfp_star_least: "(\<forall> u . u \<le> Omega_fun f g u \<longrightarrow> u \<le> A) \<Longrightarrow> (star_fun f) o g \<le> A"
  apply (unfold star_fun_def)
  apply (simp add: gfp_def)
  apply (unfold Sup_comp_fun)
  apply (rule Sup_least)
  apply simp
  apply safe
  apply (drule_tac x = "m o g" in spec)
  by (simp add: le_fun_def o_def inf_fun_def Omega_fun_def)

lemma lfp_omega: "f \<in> MonoTran \<Longrightarrow> ((omega_fun f) o g) = lfp (Omega_fun f g)"
  apply (rule antisym)
  apply (rule lfp_omega_lowerbound)
  apply simp_all
  apply (simp add: lfp_def)
  apply (rule Inf_greatest)
  apply safe
  apply (rule_tac y = "Omega_fun f g x" in order_trans)
  apply simp_all
  apply (rule_tac f = " Omega_fun f g" in monoD)
  apply simp_all
  apply (rule Inf_lower)
  apply simp
  apply (rule lfp_omega_greatest)
  apply safe
  apply (simp add: lfp_def)
  apply (rule Inf_lower)
  by simp

lemma gfp_star: "f \<in> MonoTran \<Longrightarrow> ((star_fun f) o g) = gfp (Omega_fun f g)"
  apply (rule antisym)
  apply (rule gfp_star_least)
  apply safe
  apply (simp add: gfp_def)
  apply (rule Sup_upper, simp)
  apply (rule gfp_omega_upperbound)
  apply simp_all
  apply (simp add: gfp_def)
  apply (rule Sup_least)
  apply safe
  apply (rule_tac y = "Omega_fun f g x" in order_trans)
  apply simp_all
  apply (rule_tac f = " Omega_fun f g" in monoD)
  apply simp_all
  apply (rule Sup_upper)
  by simp

definition "assert_fun p q = (p \<sqinter> q :: 'a::semilattice_inf)"

lemma assert_fun_MonoTran [simp]: "(assert_fun p) \<in> MonoTran"
  apply (simp add: assert_fun_def MonoTran_def mono_def, safe)
  by (rule_tac y = x in order_trans, simp_all)

lemma assert_fun_le_id [simp]: "assert_fun p \<le> id"
  by (simp add: assert_fun_def id_def le_fun_def)

lemma assert_fun_disjunctive [simp]: "assert_fun (p::'a::distrib_lattice) \<in> Apply.disjunctive"
  by (simp add: assert_fun_def Apply.disjunctive_def inf_sup_distrib)
  
definition
  "assertion_fun = {x . \<exists> p . x = assert_fun p}"

lemma assert_cont:
  "(x :: 'a::boolean_algebra \<Rightarrow> 'a)  \<le> id \<Longrightarrow> x \<in> Apply.disjunctive \<Longrightarrow> x = assert_fun (x \<top>)"
  apply (rule antisym)
  apply (simp_all add: le_fun_def assert_fun_def, safe)
  apply (rule_tac f = x in  monoD, simp_all)
  apply (subgoal_tac "x top = sup (x xa) (x (-xa))")
  apply simp
  apply (subst inf_sup_distrib)
  apply simp
  apply (rule_tac y = "inf (- xa) xa" in order_trans)
  apply (simp del: compl_inf_bot)
  apply (rule_tac y = "x (- xa)" in order_trans)
  apply simp
  apply simp
  apply simp
  apply (cut_tac x = x and y = xa and z = "-xa" in Apply.disjunctiveD, simp)
  apply (subst (asm) sup_commute)
  apply (subst (asm) compl_sup_top)
  by simp

lemma assertion_fun_disj_less_one: "assertion_fun = Apply.disjunctive \<inter> {x::'a::boolean_algebra \<Rightarrow> 'a . x \<le> id}"
  apply safe
  apply (simp_all add: assertion_fun_def, auto)
  apply (rule_tac x = "x \<top>" in exI)
  by (rule assert_cont, simp_all)

lemma assert_fun_dual: "((assert_fun p) o \<top>) \<sqinter> (dual_fun (assert_fun p)) = assert_fun p"
  by (simp add: fun_eq_iff inf_fun_def dual_fun_def o_def assert_fun_def top_fun_def inf_sup_distrib inf_compl_bot)

lemma assertion_fun_dual: "x \<in> assertion_fun \<Longrightarrow> (x o \<top>) \<sqinter> (dual_fun x) = x"
  by (simp add: assertion_fun_def, safe, simp add: assert_fun_dual)

lemma assertion_fun_MonoTran [simp]: "x \<in> assertion_fun \<Longrightarrow> x \<in> MonoTran"
  by (unfold assertion_fun_def MonoTran_def, auto)

lemma assertion_fun_le_one [simp]: "x \<in> assertion_fun \<Longrightarrow> x \<le> id"
  by (unfold assertion_fun_def, auto)

end

