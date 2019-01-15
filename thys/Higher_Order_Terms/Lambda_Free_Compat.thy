chapter \<open>Instantiation for \<open>\<lambda>\<close>-free terms according to Blanchette\<close>

theory Lambda_Free_Compat
imports Term_Class "Lambda_Free_RPOs.Lambda_Free_Term"
begin

text \<open>
  Blanchette et al.\ define a higher-order, lambda-free term language @{cite blanchette2016lambda}.
  To illustrate flexibility of the term algebra, I instantiate my class with their term type. The
  major issue is that Blanchette's terms are parameterized over the symbol and variable types, which
  cannot easily be supported by the classy approach, where those types are fixed to @{typ name}.
  As a workaround, I introduce a class that requires both symbol and variable types to be isomorphic
  to @{typ name}. Finally, I derive a matching operation for Blanchette's terms and prove that their
  substitution operation satisfies the class axioms.
\<close>

hide_const (open) Lambda_Free_Term.subst

class is_name =
  fixes of_name :: "name \<Rightarrow> 'a"
  assumes bij: "bij of_name"
begin

definition to_name :: "'a \<Rightarrow> name" where
"to_name = inv of_name"

lemma to_of_name[simp]: "to_name (of_name a) = a"
unfolding to_name_def using bij by (metis bij_inv_eq_iff)

lemma of_to_name[simp]: "of_name (to_name a) = a"
unfolding to_name_def using bij by (meson bij_inv_eq_iff)

lemma of_name_inj: "of_name name\<^sub>1 = of_name name\<^sub>2 \<Longrightarrow> name\<^sub>1 = name\<^sub>2"
using bij by (metis to_of_name)

end

instantiation name :: is_name begin

definition of_name_name :: "name \<Rightarrow> name" where
[code_unfold]: "of_name_name x = x"

instance by standard (auto simp: of_name_name_def bij_betw_def inj_on_def)

end

lemma [code_unfold]: "(to_name :: name \<Rightarrow> name) = id"
unfolding to_name_def of_name_name_def by auto

instantiation tm :: (is_name, is_name) "pre_term" begin

definition app_tm where
"app_tm = tm.App"

definition unapp_tm where
"unapp_tm t = (case t of App t u \<Rightarrow> Some (t, u) | _ \<Rightarrow> None)"

definition const_tm where
"const_tm n = Hd (Sym (of_name n))"

definition unconst_tm where
"unconst_tm t = (case t of Hd (Sym a) \<Rightarrow> Some (to_name a) | _ \<Rightarrow> None)"

definition free_tm where
"free_tm n = Hd (Var (of_name n))"

definition unfree_tm where
"unfree_tm t = (case t of Hd (Var a) \<Rightarrow> Some (to_name a) | _ \<Rightarrow> None)"

context
  includes fset.lifting
begin

lift_definition frees_tm :: "('a, 'b) tm \<Rightarrow> name fset" is "\<lambda>t. to_name ` vars t"
  by auto

lift_definition consts_tm :: "('a, 'b) tm \<Rightarrow> name fset" is "\<lambda>t. to_name ` syms t"
  by auto

end

lemma frees_tm[code, simp]:
  "frees (App f x) = frees f |\<union>| frees x"
  "frees (Hd h) = (case h of Sym _ \<Rightarrow> fempty | Var v \<Rightarrow> {| to_name v |})"
including fset.lifting
by (transfer; auto split: hd.splits)+

lemma consts_tm[code, simp]:
  "consts (App f x) = consts f |\<union>| consts x"
  "consts (Hd h) = (case h of Var _ \<Rightarrow> fempty | Sym v \<Rightarrow> {| to_name v |})"
including fset.lifting
by (transfer; auto split: hd.splits)+

definition subst_tm :: "('a, 'b) tm \<Rightarrow> (name, ('a, 'b) tm) fmap \<Rightarrow> ('a, 'b) tm" where
"subst_tm t env =
  Lambda_Free_Term.subst (fmlookup_default env (Hd \<circ> Var \<circ> of_name) \<circ> to_name) t"

lemma subst_tm[code, simp]:
  "subst (App t u) env = App (subst t env) (subst u env)"
  "subst (Hd h) env = (case h of
    Sym s \<Rightarrow> Hd (Sym s) |
    Var x \<Rightarrow> (case fmlookup env (to_name x) of
      Some t' \<Rightarrow> t'
    | None \<Rightarrow> Hd (Var x)))"
unfolding subst_tm_def
by (auto simp: fmlookup_default_def split: hd.splits option.splits)

instance proof (standard, goal_cases)
qed (auto
      simp: app_tm_def unapp_tm_def const_tm_def unconst_tm_def free_tm_def unfree_tm_def of_name_inj
      split: tm.splits hd.splits option.splits)

end

instantiation tm :: (is_name, is_name) "term" begin

definition abs_pred_tm :: "(('a, 'b) tm \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tm \<Rightarrow> bool" where
"abs_pred_tm P t \<longleftrightarrow> True"

instance proof (standard, goal_cases)
  case (1 P t)
  then show ?case
    proof (induction t)
      case (Hd h)
      then show ?case
        apply (cases h)
        apply (auto simp: free_tm_def const_tm_def)
        apply (metis of_to_name)+
        done
    qed (auto simp: app_tm_def)
qed (auto simp: abs_pred_tm_def)

end

lemma apps_list_comb: "apps f xs = list_comb f xs"
by (induction xs arbitrary: f) (auto simp: app_tm_def)

end