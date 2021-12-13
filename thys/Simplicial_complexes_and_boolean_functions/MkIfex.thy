
text\<open>
  Author: Julius Michaelis
\<close>

theory MkIfex
  imports "ROBDD.BDT"
begin

section\<open>Converting boolean functions to BDTs\<close>
text\<open>The following function builds an @{typ "'a ifex"}
  (a binary decision tree)
  from a boolean function and its list of variables
  (note that in this development we will be using
  boolean functions over sets of the natural numbers
  of the form @{term "{..<n::nat}"}).\<close>

fun mk_ifex :: "('a :: linorder) boolfunc \<Rightarrow> 'a list \<Rightarrow> 'a ifex" where
"mk_ifex f [] = (if f (const False) then Trueif else Falseif)" |
"mk_ifex f (v#vs) = ifex_ite
                      (IF v Trueif Falseif)
                      (mk_ifex (bf_restrict v True f) vs)
                      (mk_ifex (bf_restrict v False f) vs)"

text\<open>The result of @{term "mk_ifex"} is @{const ifex_ordered}
  and @{const ifex_minimal}.\<close>

lemma mk_ifex_ro: "ro_ifex (mk_ifex f vs)"
  by(induction vs arbitrary: f; fastforce
      intro: order_ifex_ite_invar minimal_ifex_ite_invar
      simp del: ifex_ite.simps)

text\<open>To prove that @{const mk_ifex} has correctly captured a boolean function @{term f},
we need know that all variables that @{term f} depends on were considered by @{const mk_ifex}.
In that regard, one troublesome aspect of @{type boolfunc} from @{theory "ROBDD.Bool_Func"} is that it is too general:
Boolean functions' assignments assign a Boolean value to any natural number,
and functions are not limited to ``reading'' only from a finite set of variables.
This for example allows for the boolean function that asks ``Is the assignment true in a finite number of variables:
@{term "\<lambda>as. finite {x. as x}"}.''
This function does not depend on any single variable, but on the set of all of them.
A definition that proved to work despite such subtleties is that
a function @{term f} only depends on the variables in set @{term x} iff
for any pair of assignments that agree in @{term x} (but are arbitrary otherwise),
the values of @{term f} agree:\<close>
definition "reads_inside_set f x \<equiv>
  (\<forall>assmt1 assmt2. (\<forall>p. p \<in> x \<longrightarrow> assmt1 p = assmt2 p) \<longrightarrow> f assmt1 = f assmt2)"

lemma reads_inside_set_subset: "reads_inside_set f a \<Longrightarrow> a \<subseteq> b \<Longrightarrow> reads_inside_set f b"
  unfolding reads_inside_set_def by blast

lemma reads_inside_set_restrict: "reads_inside_set f s \<Longrightarrow> reads_inside_set (bf_restrict i v f) (Set.remove i s)"
  unfolding reads_inside_set_def bf_restrict_def by force (* wow *)

lemma collect_upd_true: "Collect (x(y:= True)) = insert y (Collect x)" by auto
lemma collect_upd_false: "Collect (x(y:= False)) = Set.remove y (Collect x)" by auto metis

lemma reads_none: "reads_inside_set f {} \<Longrightarrow> f = bf_True \<or> f = bf_False"
  unfolding reads_inside_set_def by fast (* wow *)

lemma val_ifex_ite_subst: "\<lbrakk>ro_ifex i; ro_ifex t; ro_ifex e\<rbrakk> \<Longrightarrow> val_ifex (ifex_ite i t e) = bf_ite (val_ifex i) (val_ifex t) (val_ifex e)"
  using val_ifex_ite by blast

theorem
  val_ifex_mk_ifex_equal:
  "reads_inside_set f (set vs) \<Longrightarrow> val_ifex (mk_ifex f vs) assmt = f assmt"
proof(induction vs arbitrary: f assmt)
  case Nil
  then show ?case using reads_none by auto
next
  case (Cons v vs)
  have "reads_inside_set (bf_restrict v x f) (set vs)" for x
    using reads_inside_set_restrict[OF Cons.prems] reads_inside_set_subset by fastforce
  from Cons.IH[OF this] show ?case
    unfolding mk_ifex.simps val_ifex.simps bf_restrict_def
    by(subst val_ifex_ite_subst; simp add: bf_ite_def fun_upd_idem mk_ifex_ro)
qed

end
