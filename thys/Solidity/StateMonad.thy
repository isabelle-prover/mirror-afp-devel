theory StateMonad
imports Main "HOL-Library.Monad_Syntax"
begin

section "State Monad with Exceptions"

datatype ('n, 'e) result = Normal 'n | Exception 'e

type_synonym ('a, 'e, 's) state_monad = "'s \<Rightarrow> ('a \<times> 's, 'e) result"

lemma result_cases[cases type: result]:
  fixes x :: "('a \<times> 's, 'e) result"
  obtains (n) a s where "x = Normal (a, s)"
        | (e) e where "x = Exception e"
proof (cases x)
    case (Normal n)
    then show ?thesis
      by (metis n prod.swap_def swap_swap)
  next
    case (Exception e)
    then show ?thesis ..
qed

subsection \<open>Fundamental Definitions\<close>

fun
  return :: "'a \<Rightarrow> ('a, 'e, 's) state_monad" where
  "return a s = Normal (a, s)"

fun
  throw :: "'e \<Rightarrow> ('a, 'e, 's) state_monad" where
  "throw e s = Exception e"

fun
  bind :: "('a, 'e, 's) state_monad \<Rightarrow> ('a \<Rightarrow> ('b, 'e, 's) state_monad) \<Rightarrow>
           ('b, 'e, 's) state_monad" (infixl ">>=" 60)
  where
    "bind f g s = (case f s of
                      Normal (a, s') \<Rightarrow> g a s'
                    | Exception e \<Rightarrow> Exception e)"

adhoc_overloading Monad_Syntax.bind bind

lemma throw_left[simp]: "throw x \<bind> y = throw x" by auto

subsection \<open>The Monad Laws\<close>

text \<open>@{term return} is absorbed at the left of a @{term bind},
  applying the return value directly:\<close>
lemma return_bind [simp]: "(return x \<bind> f) = f x"
  by auto

text \<open>@{term return} is absorbed on the right of a @{term bind}\<close>
lemma bind_return [simp]: "(m \<bind> return) = m"
proof -
  have "\<forall>s. bind m return s = m s"
  proof
    fix s
    show "bind m return s = m s"
    proof (cases "m s" rule: result_cases)
      case (n a s)
      then show ?thesis by auto
    next
      case (e e)
      then show ?thesis by auto
    qed
  qed
  thus ?thesis by auto
qed

text \<open>@{term bind} is associative\<close>
lemma bind_assoc:
  fixes m :: "('a,'e,'s) state_monad"
  fixes f :: "'a \<Rightarrow> ('b,'e,'s) state_monad"
  fixes g :: "'b \<Rightarrow> ('c,'e,'s) state_monad"
  shows "(m \<bind> f) \<bind> g  =  m \<bind> (\<lambda>x. f x\<bind> g)"
proof
  fix s
  show "bind (bind m f) g s = bind m (\<lambda>x. bind (f x) g) s"
    by (cases "m s" rule: result_cases, simp+)
qed

subsection \<open>Basic Conguruence Rules\<close>

(*
  This lemma is needed for termination proofs.

  Function sub1 , for example, requires it.
*)
lemma monad_cong[fundef_cong]:
  fixes m1 m2 m3 m4
  assumes "m1 s = m2 s"
      and "\<And>v s'. m2 s = Normal (v, s') \<Longrightarrow> m3 v s' = m4 v s'"
    shows "(bind m1 m3) s = (bind m2 m4) s"
  apply(insert assms, cases "m1 s")
  apply (metis StateMonad.bind.simps old.prod.case result.simps(5))
  by (metis bind.elims result.simps(6))

(*
  Lemma bind_case_nat_cong is required if a bind operand is a case analysis over nat.

  Function sub2, for example, requires it.
*)
lemma bind_case_nat_cong [fundef_cong]:
  assumes "x = x'" and "\<And>a. x = Suc a \<Longrightarrow> f a h = f' a h"
  shows "(case x of Suc a \<Rightarrow> f a | 0 \<Rightarrow> g) h = (case x' of Suc a \<Rightarrow> f' a | 0 \<Rightarrow> g) h"
  by (metis assms(1) assms(2) old.nat.exhaust old.nat.simps(4) old.nat.simps(5))

lemma if_cong[fundef_cong]:
  assumes "b = b'"
    and "b' \<Longrightarrow> m1 s = m1' s"
    and "\<not> b' \<Longrightarrow> m2 s = m2' s"
  shows "(if b then m1 else m2) s = (if b' then m1' else m2') s"
  using assms(1) assms(2) assms(3) by auto

lemma bind_case_pair_cong [fundef_cong]:
  assumes "x = x'" and "\<And>a b. x = (a,b) \<Longrightarrow> f a b s = f' a b s"
  shows "(case x of (a,b) \<Rightarrow> f a b) s = (case x' of (a,b) \<Rightarrow> f' a b) s"
  by (simp add: assms(1) assms(2) prod.case_eq_if)

lemma bind_case_let_cong [fundef_cong]:
  assumes "M = N"
      and "(\<And>x. x = N \<Longrightarrow> f x s = g x s)"
    shows "(Let M f) s = (Let N g) s"
  by (simp add: assms(1) assms(2))

lemma bind_case_some_cong [fundef_cong]:
  assumes "x = x'" and "\<And>a. x = Some a \<Longrightarrow> f a s = f' a s" and "x = None \<Longrightarrow> g s = g' s"
  shows "(case x of Some a \<Rightarrow> f a | None \<Rightarrow> g) s = (case x' of Some a \<Rightarrow> f' a | None \<Rightarrow> g') s"
  by (simp add: assms(1) assms(2) assms(3) option.case_eq_if)

subsection \<open>Other functions\<close>

text \<open>
  The basic accessor functions of the state monad. \<open>get\<close> returns
  the current state as result, does not fail, and does not change the state.
  \<open>put s\<close> returns unit, changes the current state to \<open>s\<close> and does not fail.
\<close>
fun get :: "('s, 'e, 's) state_monad" where
  "get s = Normal (s, s)"

fun put :: "'s \<Rightarrow> (unit, 'e, 's) state_monad" where
  "put s _ = Normal ((), s)"

text \<open>Apply a function to the current state and return the result
without changing the state.\<close>
fun
  applyf :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a, 'e, 's) state_monad" where
 "applyf f = get \<bind> (\<lambda>s. return (f s))"

text \<open>Modify the current state using the function passed in.\<close>
fun
  modify :: "('s \<Rightarrow> 's) \<Rightarrow> (unit, 'e, 's) state_monad"
where "modify f = get \<bind> (\<lambda>s::'s. put (f s))"

text \<open>
  Perform a test on the current state, performing the left monad if
  the result is true or the right monad if the result is false.
\<close>
fun
  condition :: "('s \<Rightarrow> bool) \<Rightarrow> ('a, 'e, 's) state_monad \<Rightarrow> ('a, 'e, 's) state_monad \<Rightarrow> ('a, 'e, 's) state_monad"
where
  "condition P L R s = (if (P s) then (L s) else (R s))"

notation (output)
  condition  ("(condition (_)//  (_)//  (_))" [1000,1000,1000] 1000)

lemma condition_cong[fundef_cong]:
  assumes "b s = b' s"
    and "b' s \<Longrightarrow> m1 s = m1' s"
    and "\<And>s'. s' = s \<Longrightarrow> \<not> b' s' \<Longrightarrow> m2 s' = m2' s'"
  shows "(condition b m1 m2) s = (condition b' m1' m2') s"
  by (simp add: assms(1) assms(2) assms(3))

fun
  assert :: "'e \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('a, 'e, 's) state_monad \<Rightarrow> ('a, 'e, 's) state_monad" where
 "assert x t m = condition t (throw x) m"

notation (output)
  assert  ("(assert (_)//  (_)//  (_))" [1000,1000,1000] 1000)

lemma assert_cong[fundef_cong]:
  assumes "b s = b' s"
    and "\<not> b' s \<Longrightarrow> m s = m' s"
  shows "(assert x b m) s = (assert x b' m') s"
  by (simp add: assms(1) assms(2))

subsection \<open>Some basic examples\<close>

lemma "do {
        x \<leftarrow> return 1;
        return (2::nat);
        return x
       } =
       return 1 \<bind> (\<lambda>x. return (2::nat) \<bind> (\<lambda>_. (return x)))" ..

lemma "do {
        x \<leftarrow> return 1;
          return 2;
          return x
       } = return 1"
  by auto

fun sub1 :: "(unit, nat, nat) state_monad" where
    "sub1 0 = put 0 0"
  | "sub1 (Suc n) = (do {
                     x \<leftarrow> get;
                     put x;
                     sub1
                    }) n"

fun sub2 :: "(unit, nat, nat) state_monad" where
  "sub2 s =
     (do {
        n \<leftarrow> get;
        (case n of
          0 \<Rightarrow> put 0
        | Suc n' \<Rightarrow> (do {
                  put n';
                  sub2
                }))
     }) s"

fun sub3 :: "(unit, nat, nat) state_monad" where
  "sub3 s =
     condition (\<lambda>n. n=0)
       (return ())
       (do {
         n \<leftarrow> get;
         put (n - 1);
         sub3
        }) s"

fun sub4 :: "(unit, nat, nat) state_monad" where
  "sub4 s =
     assert (0) (\<lambda>n. n=0)
       (do {
         n \<leftarrow> get;
         put (n - 1);
         sub4
        }) s"

fun sub5 :: "(unit, nat, (nat*nat)) state_monad" where
  "sub5 s =
     assert (0) (\<lambda>n. fst n=0)
       (do {
         (n,m) \<leftarrow> get;
          put (n - 1,m);          
          sub5
        }) s"
end