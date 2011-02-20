(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

(*<*)
theory Backtracking
imports HOLCF LList Nats WorkerWrapperNew
begin
(*>*)

section{* Wand/Vaillancourt Backtracking Monads *}

text{* This is the first-order part of the language considered by
\citet{WandVaillancourt:FIXME}. This is routine, following the same
recipe as \S\ref{sec:continuations}.

It is currently not easy to reason about higher-order languages in
HOLCF. *}

domain Expr
  = Const (lazy Nat)
  | Add (lazy Expr) (lazy Expr)
  | Disj (lazy Expr) (lazy Expr) | Fail

fixrec eval_body :: "(Expr \<rightarrow> Nat llist) \<rightarrow> (Expr \<rightarrow> Nat llist)"
where
  "eval_body\<cdot>r\<cdot>(Const\<cdot>n) = lsingleton\<cdot>n"
| "eval_body\<cdot>r\<cdot>(Add\<cdot>e1\<cdot>e2) = lconcat\<cdot>(lmap\<cdot>(\<Lambda> x. lconcat\<cdot>(lmap\<cdot>(\<Lambda> y. lsingleton\<cdot>(x + y))\<cdot>(r\<cdot>e2)))\<cdot>(r\<cdot>e1))"
| "eval_body\<cdot>r\<cdot>(Disj\<cdot>e1\<cdot>e2) = r\<cdot>e1 :++ r\<cdot>e2"
| "eval_body\<cdot>r\<cdot>Fail = lnil"

lemma eval_body_strict_e[simp]: "eval_body\<cdot>r\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

text{* The observation type is @{typ "Nat llist"}, which is a little
less obvious than Gill/Hutton's example. Also note @{text
"Observation"} is not unlifted and relifted, and that if we want this
to work in a strict setting, we need to thunkify @{text "Failure"},
which complicates reasoning. The ONE domain is a bit fiddly. *}

type_synonym Observation = "Nat llist"
type_synonym Failure = "Observation"
type_synonym Success = "Nat \<rightarrow> Failure \<rightarrow> Observation"
type_synonym K = "Success \<rightarrow> Failure \<rightarrow> Observation"

(* FIXME what is blah? *)

fixrec blah :: "Nat llist \<rightarrow> K"
where
  "blah\<cdot>lnil\<cdot>s\<cdot>f = f"
| "blah\<cdot>(x :@ xs)\<cdot>s\<cdot>f = s\<cdot>x\<cdot>(blah\<cdot>xs\<cdot>s\<cdot>f)"

lemma blah_strict[simp]: "blah\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

definition unwrap :: "(Expr \<rightarrow> Nat llist) \<rightarrow> (Expr \<rightarrow> K)"
where
  "unwrap \<equiv> \<Lambda> r e s f. blah\<cdot>(r\<cdot>e)\<cdot>s\<cdot>f"

lemma unwrap_strict[simp]: "unwrap\<cdot>\<bottom> = \<bottom>"
  unfolding unwrap_def by (rule ext_cfun)+ simp

lemma unwrap_strict2[simp]: "r\<cdot>\<bottom> = \<bottom> \<Longrightarrow> unwrap\<cdot>r\<cdot>\<bottom> = \<bottom>"
  unfolding unwrap_def by (rule ext_cfun)+ simp

definition
  wrap :: "(Expr \<rightarrow> K) \<rightarrow> (Expr \<rightarrow> Nat llist)" where
  "wrap \<equiv> \<Lambda> r e. r\<cdot>e\<cdot>(\<Lambda> x f. x :@ f)\<cdot>lnil"

lemma wrap_unwrap_id: "wrap oo unwrap = ID"
  unfolding wrap_def unwrap_def
  apply (rule ext_cfun)+
  apply (case_tac "x\<cdot>xa")
  apply (simp_all)
  apply (induct_tac llist)
  apply simp_all
  done

definition eval_work :: "Expr \<rightarrow> K"
where
  "eval_work \<equiv> fix\<cdot>(unwrap oo eval_body oo wrap)"

definition eval :: "Expr \<rightarrow> Nat llist"
where
  "eval \<equiv> wrap\<cdot>eval_work"

lemma "fix\<cdot>eval_body = eval"
  unfolding eval_def eval_work_def
  using worker_wrapper_id[OF wrap_unwrap_id]
  by simp

fixrec eval_body' :: "(Expr \<rightarrow> K) \<rightarrow> (Expr \<rightarrow> K)"
where
  "eval_body'\<cdot>r\<cdot>(Const\<cdot>n)\<cdot>s\<cdot>f = s\<cdot>n\<cdot>f"
| "eval_body'\<cdot>r\<cdot>(Add\<cdot>e1\<cdot>e2)\<cdot>s\<cdot>f = r\<cdot>e1\<cdot>(\<Lambda> x. r\<cdot>e2\<cdot>(\<Lambda> y. s\<cdot>(x + y)))\<cdot>f"
| "eval_body'\<cdot>r\<cdot>(Disj\<cdot>e1\<cdot>e2)\<cdot>s\<cdot>f = r\<cdot>e1\<cdot>s\<cdot>(r\<cdot>e2\<cdot>s\<cdot>f)"
| "eval_body'\<cdot>r\<cdot>Fail\<cdot>s\<cdot>f = f"

lemma eval_body'_strict[simp]: "eval_body'\<cdot>r\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma FIXME: "blah\<cdot>(xs :++ ys)\<cdot>s\<cdot>f = blah\<cdot>xs\<cdot>s\<cdot>(blah\<cdot>ys\<cdot>s\<cdot>f)"
  apply (induct xs)
  apply simp_all
  done

lemma FIXME2: "blah\<cdot>(lconcat\<cdot>(lmap\<cdot>g\<cdot>xs))\<cdot>s\<cdot>f = blah\<cdot>xs\<cdot>(\<Lambda> x. blah\<cdot>(g\<cdot>x)\<cdot>s)\<cdot>f"
  apply (induct xs)
     apply simp
    apply simp
   apply simp
  apply (simp add: FIXME)
  done

lemma eval_body_body':
  "unwrap oo eval_body oo wrap = eval_body' oo unwrap oo wrap"
  apply (rule ext_cfun)+
  apply (case_tac xa)
      apply simp
     apply (simp add: unwrap_def)
    apply (simp add: unwrap_def)
    apply (simp add: FIXME2 eta_cfun)
    apply (subgoal_tac "(\<Lambda> xa. blah\<cdot>(lconcat\<cdot>(lmap\<cdot>(\<Lambda> y. (xa + y) :@ lnil)\<cdot>(wrap\<cdot>x\<cdot>Expr2)))\<cdot>xb)
                      = (\<Lambda> xa. blah\<cdot>(wrap\<cdot>x\<cdot>Expr2)\<cdot>(\<Lambda> y. xb\<cdot>(xa + y)))")
     apply simp
    apply (rule ext_cfun)+
    apply (simp add: FIXME2)
    apply (subgoal_tac "(\<Lambda> x. blah\<cdot>((xd + x) :@ lnil)\<cdot>xb)
                      = (\<Lambda> y. xb\<cdot>(xd + y))")
     apply simp
    apply (rule ext_cfun)+
    apply simp
   apply (simp add: unwrap_def FIXME)
  apply (simp add: unwrap_def)
  done

lemma "wrap\<cdot>(fix\<cdot>eval_body') = fix\<cdot>eval_body"
  using worker_wrapper_new[OF wrap_unwrap_id unwrap_strict]
        eval_body_body'
  by simp

(*<*)
end
(*>*)
