(*  Title:       Termination of the Hydra Battle following Dershowitz and Moser
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2017
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Termination of the Hydra Battle Following Dershowitz and Moser\<close>

theory Hydra_Battle
imports Syntactic_Ordinal
begin

hide_const (open) Nil Cons

datatype lisp =
  Nil
| Cons (car: lisp) (cdr: lisp)
where
  "car Nil = Nil"
| "cdr Nil = Nil"

primrec hmset_of_lisp :: "lisp \<Rightarrow> hmultiset" where
  "hmset_of_lisp Nil = 0"
| "hmset_of_lisp (Cons l r) = HMSet {#hmset_of_lisp l#} + hmset_of_lisp r"

lemma hmset_of_lisp_left_less: "hmset_of_lisp l < hmset_of_lisp (Cons l r)"
  by (auto simp: mem_imp_less_HMSet intro: trans_less_add1_hmset)

lemma hmset_of_lisp_right_less: "hmset_of_lisp r < hmset_of_lisp (Cons l r)"
  by simp

primrec f :: "nat \<Rightarrow> lisp \<Rightarrow> lisp \<Rightarrow> lisp" where
  "f 0 y x = x"
| "f (Suc m) y x = Cons y (f m y x)"

lemma hmset_of_lisp_f:
  "hmset_of_lisp (f n y x) = HMSet (replicate_mset n (hmset_of_lisp y)) + hmset_of_lisp x"
  by (induct n) (auto simp: HMSet_plus[symmetric])

function d :: "nat \<Rightarrow> lisp \<Rightarrow> lisp" where
  "d n x =
   (if car x = Nil then cdr x
    else if car (car x) = Nil then f n (cdr (car x)) (cdr x)
    else Cons (d n (car x)) (cdr x))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, x). size x)", rule wf_measure, rename_tac n x, case_tac x, auto)

declare d.simps[simp del]

function h :: "nat \<Rightarrow> lisp \<Rightarrow> lisp" where
  "h n x = (if x = Nil then Nil else h (n + 1) (d n x))"
  by pat_completeness auto
termination
proof -
  let ?R = "inv_image {(m, n). m < n} (\<lambda>(n, x). hmset_of_lisp x)"

  show ?thesis
  proof (relation ?R)
    show "wf ?R"
      by (rule wf_inv_image) (rule wf)
  next
    fix n x
    assume x_cons: "x \<noteq> Nil"
    thus "((n + 1, d n x), n, x) \<in> ?R"
      unfolding inv_image_def mem_Collect_eq prod.case
    proof (induct x)
      case (Cons l r)
      note ihl = this(1)
      show ?case
      proof (subst d.simps, simp, intro conjI impI)
        assume l_cons: "l \<noteq> Nil"
        {
          assume "car l = Nil"
          show "hmset_of_lisp (f n (cdr l) r) < HMSet {#hmset_of_lisp l#} + hmset_of_lisp r"
            using l_cons by (cases l) (auto simp: hmset_of_lisp_f)
        }
        {
          show "hmset_of_lisp (d n l) < hmset_of_lisp l"
            by (rule ihl[OF l_cons])
        }
      qed
    qed simp
  qed
qed

declare h.simps[simp del]

end
