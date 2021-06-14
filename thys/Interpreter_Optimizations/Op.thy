theory Op
  imports Main
begin

section \<open>n-ary operations\<close>

locale nary_operations =
  fixes
    \<OO>\<pp> :: "'op \<Rightarrow> 'a list \<Rightarrow> 'a" and
    \<AA>\<rr>\<ii>\<tt>\<yy> :: "'op \<Rightarrow> nat"
  assumes
    \<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>_domain: "length xs = \<AA>\<rr>\<ii>\<tt>\<yy> op \<Longrightarrow> \<exists>y. \<OO>\<pp> op xs = y"

(* locale nary_operations_inl =
  nary_operations "\<lambda>op args. fst (eval op args)" arity
  for
    eval :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn \<times> 'op option" and arity
begin

definition equiv_op where
  "equiv_op x y \<equiv> fst \<circ> eval x = fst \<circ> eval y"

lemma equivp_equiv_op[simp]: "equivp equiv_op"
proof (rule equivpI)
  show "reflp equiv_op"
    by (rule reflpI) (simp add: equiv_op_def)
next
  show "symp equiv_op"
    by (rule sympI) (simp add: equiv_op_def)
next
  show "transp equiv_op"
    by (rule transpI) (simp add: equiv_op_def)
qed

end *)

(* locale nary_operations0 =
  fixes
    eval :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn \<times> 'op option" and
    arity :: "'op \<Rightarrow> nat"
begin

definition equiv_op where
  "equiv_op x y \<equiv> fst \<circ> eval x = fst \<circ> eval y"

lemma equivp_equiv_op[simp]: "equivp equiv_op"
proof (rule equivpI)
  show "reflp equiv_op"
    by (rule reflpI) (simp add: equiv_op_def)
next
  show "symp equiv_op"
    by (rule sympI) (simp add: equiv_op_def)
next
  show "transp equiv_op"
    by (rule transpI) (simp add: equiv_op_def)
qed

end *)

end