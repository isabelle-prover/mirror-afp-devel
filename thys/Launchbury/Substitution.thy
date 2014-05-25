theory Substitution
imports Terms
begin

text {* Defining a substitution function on terms turned out to be slightly tricky. *}

fun subst_var :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" ("_[_::v=_]" [1000,100,100] 1000)
  where "x[y ::v= z] = (if x = y then z else x)"

(* Helper lemmas provided by Christian Urban *)

lemma Projl_permute:
  assumes a: "\<exists>y. f = Inl y"
  shows "(p \<bullet> (Sum_Type.Projl f)) = Sum_Type.Projl (p \<bullet> f)"
using a by auto

lemma Projr_permute:
  assumes a: "\<exists>y. f = Inr y"
  shows "(p \<bullet> (Sum_Type.Projr f)) = Sum_Type.Projr (p \<bullet> f)"
using a by auto

nominal_primrec  (default "sum_case (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)",
                  invariant "\<lambda> a r . (\<forall> as y z . ((a = Inr (as, y, z) \<and> atom ` domA as \<sharp>* (y, z)) \<longrightarrow> map (\<lambda>x . atom (fst x))  (Sum_Type.Projr r) = map (\<lambda>x . atom (fst x)) as))")
  subst :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_::=_]" [1000,100,100] 1000)
and
  subst_heap :: "heap \<Rightarrow> var \<Rightarrow> var \<Rightarrow> heap" ("_[_::h=_]" [1000,100,100] 1000)
where
  "(Var x)[y ::= z] = Var (x[y ::v= z])"
 |"(App e v)[y ::= z] = App (e[y ::= z]) (v[y ::v= z])"
 |"atom ` domA as \<sharp>* (y,z) \<Longrightarrow> (Let as body)[y ::= z] = Let (as[y ::h= z]) (body[y ::= z])" 
 |"atom x \<sharp> (y,z) \<Longrightarrow> (Lam [x].e)[y ::= z] = Lam [x].(e[y::=z])"
 |"[][y ::h= z] = []"
 |"((v,e)# as)[y ::h= z] = (v, e[y ::= z])# (as[y ::h= z])"
proof-

have eqvt_at_subst: "\<And> e y z . eqvt_at subst_subst_heap_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst a b c) (e, y, z)"
  apply(simp add: eqvt_at_def subst_def)
  apply(rule)
  apply(subst Projl_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_heap_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_heap_graph (Inl (e, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_heap_graph.cases)
  apply(assumption)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply(rule_tac x="Sum_Type.Projl x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply blast 
  apply(simp (no_asm) only: Projl.simps)
  apply (metis Inr_not_Inl)
  apply (metis Inr_not_Inl)
  apply(simp)
  apply(perm_simp)
  apply(simp)
done

have eqvt_at_subst_heap: "\<And> as y z . eqvt_at subst_subst_heap_sumC (Inr (as, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_heap a b c) (as, y, z)"
  apply(simp add: eqvt_at_def subst_heap_def)
  apply(rule)
  apply(subst Projr_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_heap_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_heap_graph (Inr (as, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_heap_graph.cases)
  apply(assumption)
  apply (metis (mono_tags) Inr_not_Inl)+
  apply(rule_tac x="Sum_Type.Projr x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply auto[1]
  apply(simp (no_asm) only: Projr.simps)
  
  apply(rule_tac x="Sum_Type.Projr x" in exI)
  apply(clarify)
  apply (rule the1_equality)
  apply auto[1]
  apply(simp (no_asm) only: Projr.simps)
  
  apply(simp)
  apply(perm_simp)
  apply(simp)
done

{
(* Equivariance of the graph *)
case goal1 thus ?case
  unfolding eqvt_def subst_subst_heap_graph_aux_def
  by simp

(* The invariant *)
next case goal2 thus ?case
  by (induct rule: subst_subst_heap_graph.induct)(auto simp add: exp_assn.bn_defs fresh_star_insert)

(* Exhaustiveness *)
next case (goal3 P x) show ?case
  proof(cases x)
  case (Inl a) thus P
    proof(cases a)
    case (fields a1 a2 a3)
    thus P using Inl goal3
      apply (rule_tac y ="a1" and c ="(a2, a3)" in exp_strong_exhaust)
      apply (auto simp add: fresh_star_def)
      apply metis
    done
  qed
  next
  case (Inr a) thus P
    proof (cases a)
    case (fields a1 a2 a3)
    thus P using Inr goal3
      by (metis heapToAssn.cases)
  qed
qed

next case (goal15 e y2 z2 as e2 y z as2) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (drule eqvt_at_subst_heap)+
  apply (simp only: meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff]
    meta_eq_to_obj_eq[OF subst_heap_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (auto simp add: Abs_fresh_iff)
  apply (drule_tac
    c = "(y, z)" and
    as = "(map (\<lambda>x. atom (fst x)) e)" and
    bs = "(map (\<lambda>x. atom (fst x)) e2)" and
    f = "\<lambda> a b c . [a]lst. (subst (fst b) y z, subst_heap (snd b) y z )" in Abs_lst_fcb2)
  apply (simp add: perm_supp_eq fresh_Pair fresh_star_def Abs_fresh_iff)
  apply (metis domA_def image_image image_set)
  apply (metis domA_def image_image image_set)
  apply (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  apply (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  apply (simp add: eqvt_at_def)
  done

next case (goal19 x2 y2 z2 e2 x y z e) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (simp only: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (simp add: eqvt_at_def)
  apply rule
  apply (erule_tac x = "(x2 \<leftrightarrow> c)" in allE)
  apply (erule_tac x = "(x \<leftrightarrow> c)" in allE)
  apply auto
  done
}
qed(auto)

termination (eqvt) by lexicographic_order

lemma shows
  True and bn_subst[simp]: "domA (subst_heap as y z) = domA as"
by(induct rule:subst_subst_heap.induct)
  (auto simp add: exp_assn.bn_defs fresh_star_insert)

lemma subst_noop[simp]:
shows "e[y ::= y] = e" and "as[y::h=y]= as"
by(induct e y y and as y y rule:subst_subst_heap.induct)
  (auto simp add:fresh_star_Pair exp_assn.bn_defs)

lemma subst_is_fresh[simp]:
assumes "atom y \<sharp> z"
shows
  "atom y \<sharp> e[y ::= z]"
and
 "atom ` domA as \<sharp>* y \<Longrightarrow> atom y \<sharp> as[y::h=z]"
using assms
by(induct e y z and as y z rule:subst_subst_heap.induct)
  (auto simp add:fresh_at_base fresh_star_Pair fresh_star_insert fresh_Nil fresh_Cons)

lemma
 subst_pres_fresh: "x \<sharp> e \<Longrightarrow> x \<sharp> z \<Longrightarrow> x \<sharp> e[y ::= z]"
and
 "x \<sharp> \<Gamma> \<Longrightarrow> x \<sharp> z \<Longrightarrow> x \<notin> atom ` domA \<Gamma> \<Longrightarrow> x \<sharp> (\<Gamma>[y ::h= z])"
by(induct e y z and \<Gamma> y z rule:subst_subst_heap.induct)
  (auto simp add:fresh_star_Pair exp_assn.bn_defs fresh_Cons)

lemma subst_fresh_noop: "atom x \<sharp> e \<Longrightarrow> e[x ::= y] = e"
  and subst_heap_fresh_noop: "atom x \<sharp> \<Gamma> \<Longrightarrow>  \<Gamma>[x ::h= y] = \<Gamma>"
by (nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_def fresh_Pair fresh_at_base fresh_Cons simp del: exp_assn.eq_iff)

lemma supp_subst: "supp (e[y::=x]) \<subseteq> (supp e - {atom y}) \<union> supp x"
proof-
  have "\<And> a. (a \<sharp> e \<or> a = atom y) \<Longrightarrow> a \<sharp> x \<Longrightarrow> a \<sharp> e[y::=x]"
    by (auto intro: subst_pres_fresh)
  thus ?thesis by (auto simp add: fresh_def)
qed

lemma fv_subst_subset: "fv (e[y ::= x]) \<subseteq> (fv e - {y}) \<union> {x}"
proof-
  have "fv (e[y ::= x]) = {v. atom v \<in> supp (e[y ::= x])}" unfolding fv_def..
  also have "\<dots> \<subseteq> {v. atom v \<in> ((supp e - {atom y}) \<union> supp x)}"
    using supp_subst by auto
  also have "\<dots> = (fv e - {y}) \<union> {x}"
    using supp_subst by (auto simp add: fv_def supp_at_base)
  finally show ?thesis.
qed

lemma fresh_star_at_base:
  fixes x :: "'a :: at_base"
  shows "S \<sharp>* x \<longleftrightarrow> atom x \<notin> S"
  by (metis fresh_at_base(2) fresh_star_def)

lemma subst_swap_same: "atom x \<sharp> e \<Longrightarrow>  (x \<leftrightarrow> y) \<bullet> e = e[y ::=x]"
  and "atom x \<sharp> \<Gamma> \<Longrightarrow> atom `domA \<Gamma> \<sharp>* y \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> \<Gamma> = \<Gamma>[y ::h= x]"
by(nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_Pair fresh_star_at_base fresh_Cons simp del: exp_assn.eq_iff)

lemma subst_subst_back: "atom x \<sharp> e \<Longrightarrow>  e[y::=x][x::=y] = e" 
  and "atom x \<sharp> \<Gamma> \<Longrightarrow> atom `domA \<Gamma> \<sharp>* y  \<Longrightarrow> \<Gamma>[y::h=x][x::h=y] = \<Gamma>"
by(nominal_induct  e and \<Gamma> avoiding: x y rule:exp_heap_strong_induct)
  (auto simp add: fresh_star_Pair fresh_star_at_base fresh_star_Cons fresh_Cons  exp_assn.bn_defs simp del: exp_assn.eq_iff)


end
