theory Terms
  imports Main  "./Nominal/Nominal/Nominal2" 
begin

subsubsection {* Variables (names) and expressions *}

text {*
The type of variables is abstract and provided by the Nominal package. All we know is that it is countable.
*}

atom_decl var

nominal_datatype exp =
  Var "var"
| App "exp" "var"
| Let as::"assn" body::"exp" binds "bn as" in "body" "as"
| Lam x::"var" body::"exp" binds x in body  ("Lam [_]. _" [100, 100] 100)
and assn =
  ANil | ACons "var" "exp" "assn" 
binder
  bn
where "bn ANil = []" | "bn (ACons x t as) = (atom x) # (bn as)"

notation (latex output) Terms.Var ("_")
notation (latex output) Terms.App ("_ _")
notation (latex output) Terms.Let ("\<^raw:\textrm{\textsf{let}}> _ \<^raw:\textrm{\textsf{in}}> _")
notation (latex output) Terms.Lam ("\<lambda>_. _")

abbreviation
  LetBe :: "var\<Rightarrow>exp\<Rightarrow>exp\<Rightarrow>exp" ("let _ be _ in _ " [100,100,100] 100)
where
  "let x be t1 in t2 \<equiv> Let (ACons x t1 ANil) t2"

type_synonym heap = "(var \<times> exp) list"

subsubsection {* Testing alpha equivalence *}
              
lemma alpha_test:
  shows "Lam [x]. (Var x) = Lam [y]. (Var y)"
  by (simp add: Abs1_eq_iff fresh_at_base)

lemma alpha_test2:
  shows "let x be (Var x) in (Var x) = let y be (Var y) in (Var y)"
  by (simp add: exp_assn.bn_defs Abs1_eq_iff fresh_Pair add: fresh_at_base)

lemma alpha_test3:
  shows "
    Let (ACons x (Var y) (ACons y (Var x) ANil)) (Var x)
    =
    Let (ACons y (Var x) (ACons x (Var y) ANil)) (Var y)" (is "Let ?la ?lb = _")
  apply (simp add: exp_assn.bn_defs Abs1_eq_iff fresh_Pair add:fresh_at_base)
  apply (simp add: Abs_swap2[of "atom x" "(?lb,?la)" "[atom x, atom y]" "atom y"])
done

subsubsection {* Substitution *}

fun subst_var :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" ("_[_::v=_]" [1000,100,100] 1000)
where "x[y ::v= z] = (if x = y then z else x)"

lemma subst_var_eqvts[eqvt]:
 fixes \<pi>::perm
 shows "\<pi> \<bullet> (subst_var x y z) = subst_var (\<pi> \<bullet> x) (\<pi> \<bullet> y) (\<pi> \<bullet> z)"
by auto

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
                  invariant "\<lambda> a r . (\<forall> as y z . ((a = Inr (as, y, z) \<and> set (bn as) \<sharp>* (y, z)) \<longrightarrow> bn (Sum_Type.Projr r) = bn as))")
  subst :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_::=_]" [1000,100,100] 1000)
and
  subst_assn :: "assn \<Rightarrow> var \<Rightarrow> var \<Rightarrow> assn" ("_[_::a=_]" [1000,100,100] 1000)
where
  "(Var x)[y ::= z] = (Var (x[y ::v= z]))"
 |"(App e v)[y ::= z] = (App (e[y ::= z]) (v[y ::v= z]))"
 |"(set (bn as)) \<sharp>* (y,z) \<Longrightarrow> (Let as body)[y ::= z] = Let (subst_assn as y z) (body[y ::= z])" 
 |"(atom x \<sharp> (y,z)) \<Longrightarrow> (Lam [x].e)[y ::= z] = Lam [x].(e[y::=z])"
 |"subst_assn ANil y z = ANil"
 |"subst_assn (ACons v e as) y z = ACons v (e[y ::= z]) (subst_assn as y z)"
proof-

have eqvt_at_subst: "\<And> e y z . eqvt_at subst_subst_assn_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst a b c) (e, y, z)"
  apply(simp add: eqvt_at_def subst_def)
  apply(rule)
  apply(subst Projl_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_assn_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_assn_graph (Inl (e, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_assn_graph.cases)
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

have eqvt_at_subst_assn: "\<And> as y z . eqvt_at subst_subst_assn_sumC (Inr (as, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_assn a b c) (as, y, z)"
  apply(simp add: eqvt_at_def subst_assn_def)
  apply(rule)
  apply(subst Projr_permute)
  apply(thin_tac "?X")+
  apply (simp add: subst_subst_assn_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (subst_subst_assn_graph (Inr (as, y, z)))")
  apply(simp)
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: subst_subst_assn_graph.cases)
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
  unfolding eqvt_def subst_subst_assn_graph_aux_def
  by simp

(* The invariant *)
next case goal2 thus ?case
  by (induct rule: subst_subst_assn_graph.induct)(auto simp add: exp_assn.bn_defs fresh_star_insert)

(* Exhaustiveness *)
next case (goal3 P x) show ?case
  proof(cases x)
  case (Inl a) thus P
    proof(cases a)
    case (fields a1 a2 a3)
    thus P using Inl goal3
      apply (rule_tac y ="a1" and c ="(a2, a3)" in exp_assn.strong_exhaust(1))
      apply (auto simp add: fresh_star_def)
      apply metis
    done
  qed
  next
  case (Inr a) thus P
    proof (cases a)
    case (fields a1 a2 a3)
    thus P using Inr goal3
      apply (rule_tac ya ="a1" in exp_assn.strong_exhaust(2))
      apply (auto)
      apply blast+
    done
  qed
qed

next case (goal15 e y2 z2 as e2 y z as2) thus ?case
  apply -
  apply (drule eqvt_at_subst)+
  apply (drule eqvt_at_subst_assn)+
  apply (simp only: meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff]
    meta_eq_to_obj_eq[OF subst_assn_def, symmetric, unfolded fun_eq_iff])
  (* No _sum any more at this point! *)
  apply (auto simp add: Abs_fresh_iff)
  apply (drule_tac
    c = "(y, z)" and
    as = "(bn e)" and
    bs = "(bn e2)" and
    f = "\<lambda> a b c . [a]lst. (subst (fst b) y z, subst_assn (snd b) y z )" in Abs_lst_fcb2)
  apply (simp add: perm_supp_eq fresh_Pair fresh_star_def Abs_fresh_iff)
  apply (simp)
  apply (simp)
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
  True and bn_subst[simp]: "set (bn as) \<sharp>* (y, z) \<Longrightarrow> bn (subst_assn as y z) = bn as"
by(induct rule:subst_subst_assn.induct)
  (auto simp add: exp_assn.bn_defs fresh_star_insert)


lemma subst_is_fresh[simp]:
assumes "atom y \<sharp> z"
shows
  "atom y \<sharp> e[y ::= z]"
and
 "set (bn as) \<sharp>* (y, z) \<Longrightarrow> atom y \<sharp> (subst_assn as y z)"
using assms
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)

lemma
 subst_pres_fresh: "(atom x \<sharp> e \<and> atom x \<sharp> z) --> atom x \<sharp> e[y ::= z]"
and
 "(atom x \<sharp> as \<and> atom x \<sharp> z \<and> atom x \<notin> set (bn as)) --> (atom x \<sharp> (subst_assn as y z))"
by(induct e y z and as y z rule:subst_subst_assn.induct)
  (auto simp add:fresh_at_base fresh_star_Pair exp_assn.bn_defs fresh_star_insert)

lemma let_binders_fresh[simp]: "set (bn as) \<sharp>* Terms.Let as body"
  by (metis Diff_iff exp_assn.supp(3) finite_supp fresh_finite_atom_set fresh_star_def fresh_star_set fresh_star_supp_conv supp_of_atom_list)

end
