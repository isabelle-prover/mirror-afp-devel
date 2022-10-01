section \<open>Examples\<close>

(*<*)
theory Examples
imports Restrict_Frees_Impl
begin
(*>*)

global_interpretation extra_cp: simplification cp cpropagated
  defines RB = "simplification.rb_impl_det cp"
      and assemble = "simplification.assemble cp"
      and SPLIT = "simplification.split_impl_det cp"
  by standard (auto simp only: sat_cp fv_cp rrb_cp gen_Gen_cp cpropagated_cp cpropagated_cp_triv
    cpropagated_sub Let_def is_Bool_def fv.simps cp.simps cpropagated_simps nocp.simps cpropagated_nocp split: if_splits)

subsection \<open>Restricting Bounds in the "Suspicious Users" Query\<close>

context
  fixes b s p u :: nat and B P S
  defines "b \<equiv> 0"
    and "s \<equiv> Suc 0"
    and "p \<equiv> Suc (Suc 0)"
    and "u \<equiv> Suc (Suc (Suc 0))"
    and "B \<equiv> \<lambda>b. Pred ''B'' [Var b] :: (string, string) fmla"
    and "P \<equiv> \<lambda>b p. Pred ''P'' [Var b, Var p] :: (string, string) fmla"
    and "S \<equiv> \<lambda>p u s. Pred ''S'' [Var p, Var u, Var s] :: (string, string) fmla"
  notes cp.simps[simp del]
begin

definition Q_susp_user where
  "Q_susp_user = Conj (B b) (Exists s (Forall p (Impl (P b p) (S p u s))))"
definition Q_susp_user_rb :: "(string, string) fmla" where
  "Q_susp_user_rb = Conj (B b) (Disj (Exists s (Conj (Forall p (Impl (P b p) (S p u s))) (Exists p (S p u s)))) (Forall p (Neg (P b p))))"

lemma ex_rb_Q_susp_user: "the_res (RB Q_susp_user) = Q_susp_user_rb"
  by code_simp

end

subsection \<open>Splitting a Disjunction of Predicates\<close>

context
  fixes x y :: nat and B P
  defines "x \<equiv> 0"
    and "y \<equiv> 1"
    and "B \<equiv> \<lambda>b. Pred ''B'' [Var b] :: (string, string) fmla"
    and "P \<equiv> \<lambda>b p. Pred ''P'' [Var b, Var p] :: (string, string) fmla"
  notes cp.simps[simp del]
begin

definition Q_disj where
  "Q_disj = Disj (B x) (P x y)"
definition Q_disj_split_fin :: "(string, string) fmla" where
  "Q_disj_split_fin = Conj (Disj (B x) (P x y)) (P x y)"
definition Q_disj_split_inf :: "(string, string) fmla" where
  "Q_disj_split_inf = Exists x (B x)"

lemma ex_split_Q_disj: "the_res (SPLIT Q_disj) = (Q_disj_split_fin, Q_disj_split_inf)"
  by code_simp

end

subsection \<open>Splitting a Conjunction with an Equality\<close>

context
  fixes x u v :: nat and B
  defines "x \<equiv> 0"
    and "u \<equiv> 1"
    and "v \<equiv> 2"
    and "B \<equiv> \<lambda>b. Pred ''B'' [Var b] :: (string, string) fmla"
  notes cp.simps[simp del]
begin

definition Q_eq where
  "Q_eq = Conj (B x) (u \<approx> v)"
definition Q_eq_split_fin :: "(string, string) fmla" where
  "Q_eq_split_fin = Bool False"
definition Q_eq_split_inf :: "(string, string) fmla" where
  "Q_eq_split_inf = Exists x (B x)"

lemma ex_split_Q_eq: "the_res (SPLIT Q_eq) = (Q_eq_split_fin, Q_eq_split_inf)"
  by code_simp

end

subsection \<open>Splitting the "Suspicious Users" Query\<close>

context
  fixes b s p u :: nat and B P S
  defines "b \<equiv> 0"
    and "s \<equiv> Suc 0"
    and "p \<equiv> Suc (Suc 0)"
    and "u \<equiv> Suc (Suc (Suc 0))"
    and "B \<equiv> \<lambda>b. Pred ''B'' [Var b] :: (string, string) fmla"
    and "P \<equiv> \<lambda>b p. Pred ''P'' [Var b, Var p] :: (string, string) fmla"
    and "S \<equiv> \<lambda>p u s. Pred ''S'' [Var p, Var u, Var s] :: (string, string) fmla"
  notes cp.simps[simp del]
begin

definition "Q_susp_user_split_fin = Conj Q_susp_user_rb (Exists s (Exists p (S p u s)))"
definition "Q_susp_user_split_inf = Exists b (Conj (B b) (Forall p (Neg (P b p))))"

lemma ex_split_Q_susp_user: "the_res (SPLIT Q_susp_user) = (Q_susp_user_split_fin, Q_susp_user_split_inf)"
  by code_simp

end

(*<*)
end
(*>*)