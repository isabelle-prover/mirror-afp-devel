theory State_Monad
imports State "HOL-Library.Monad_Syntax" Utils
begin

section "state Monad with Exceptions"

datatype ('n, 'e) result =
  Normal (normal: 'n)
| Exception (ex: 'e)
| NT

lemma result_cases[cases type: result]:
  fixes x :: "('a \<times> 's, 'e \<times> 's) result"
  obtains (n) a s where "x = Normal (a, s)"
        | (e) e s where "x = Exception (e, s)"
        | (t) "x = NT"
proof (cases x)
  case (Normal n)
  then show ?thesis using n by force
next
  case (Exception e)
  then show ?thesis using e by force
next
  case NT
  then show ?thesis using t by simp
qed

typedef ('a, 'e, 's) state_monad = "UNIV::('s \<Rightarrow> ('a \<times> 's, 'e \<times> 's) result) set"
  morphisms execute create
  by simp

named_theorems execute_simps "simplification rules for execute"

lemma execute_Let [execute_simps]:
  "execute (let x = t in f x) = (let x = t in execute (f x))"
  by (simp add: Let_def)

subsection \<open>Code Generator Setup\<close>

code_datatype create

lemma execute_create[execute_simps, code]: "execute (create f) = f" using create_inverse by simp

declare execute_inverse[simp]

lemma execute_ext[intro]: "(\<And>x. (execute m1 x = execute m2 x)) \<Longrightarrow> m1 = m2" using HOL.ext
  by (metis execute_inverse)

subsection \<open>Fundamental Definitions\<close>

definition return :: "'a \<Rightarrow> ('a, 'e, 's) state_monad"
  where "return a = create (\<lambda>s. Normal (a, s))"

lemma execute_return [execute_simps]:
  "execute (return x) = Normal \<circ> Pair x"
  unfolding return_def by (auto simp add:execute_simps)

lemma execute_returnE:
  assumes "execute (return x) s = Normal (a, s')"
  shows "x = a" and "s = s'"
  using assms unfolding return_def execute_create by auto

definition throw :: "'e \<Rightarrow> ('a, 'e, 's) state_monad"
  where "throw e = create (\<lambda>s. Exception (e, s))"

lemma execute_throw [execute_simps]:
  "execute (throw x) s = Exception (x, s)"
  unfolding throw_def by (auto simp add:execute_simps)

definition bind :: "('a, 'e, 's) state_monad \<Rightarrow> ('a \<Rightarrow> ('b, 'e, 's) state_monad) \<Rightarrow> ('b, 'e, 's) state_monad" (infixl ">>=" 60)
where "bind f g = create (\<lambda>s. (case (execute f) s of
                      Normal (a, s') \<Rightarrow> execute (g a) s'
                    | Exception e \<Rightarrow> Exception e
                    | NT \<Rightarrow> NT))"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind

lemma execute_bind [execute_simps]:
  "execute f s = Normal (x, s') \<Longrightarrow> execute (f \<bind> g) s = execute (g x) s'"
  "execute f s = Exception e \<Longrightarrow> execute (f \<bind> g) s = Exception e"
  "execute f s = NT \<Longrightarrow> execute (f \<bind> g) s = NT"
  unfolding bind_def execute_create by simp_all

lemma execute_bind_normal_E:
  assumes "execute (f \<bind> g) s = Normal (a, s')"
  obtains (1) s'' x where "execute f s = Normal (x, s'')" and "execute (g x) s'' = Normal (a, s')"
  using assms unfolding bind_def execute_create apply (cases "execute f s") using that by auto

lemma execute_bind_exception_E:
  assumes "execute (f \<bind> g) s = Exception (x, s')"
  obtains (1) "execute f s = Exception (x, s')"
        | (2) a s'' where "execute f s = Normal (a,s'')" and "execute (g a) s'' = Exception (x,s')"
  using assms unfolding bind_def execute_create apply (cases "execute f s") using that by auto

(*
  This lemma is needed for termination proofs.
*)
lemma monad_cong[cong]:
  fixes m1 m2 m3 m4
  assumes "m1 = m2"
      and "\<And>s v s'. execute m2 s = Normal (v, s') \<Longrightarrow> execute (m3 v) s' = execute (m4 v) s'"
    shows "(bind m1 m3) = (bind m2 m4)"
  unfolding bind_def
proof -
  have "(\<lambda>s. case execute m1 s of Normal (a, xa) \<Rightarrow> execute (m3 a) xa | Exception x \<Rightarrow> Exception x | NT \<Rightarrow> NT) =
        (\<lambda>s. case execute m2 s of Normal (a, xa) \<Rightarrow> execute (m4 a) xa | Exception x \<Rightarrow> Exception x | NT \<Rightarrow> NT)"
  (is  "(\<lambda>s. ?L s) = (\<lambda>s. ?R s)")
  proof
    fix s
    show "?L s = ?R s"
      using assms by (cases "execute m1 s"; simp)
  qed
  then show "create (\<lambda>s. ?L s) = create (\<lambda>s. ?R s)" by simp
qed

lemma throw_left[simp]: "throw x \<bind> y = throw x" unfolding throw_def bind_def by (simp add: execute_simps)

subsection \<open>The Monad Laws\<close>

text \<open>@{term return} is absorbed at the left of a @{term bind},
  applying the return value directly:\<close>
lemma return_bind [simp]: "(return x \<bind> f) = f x"
unfolding return_def bind_def by (simp add: execute_simps)

text \<open>@{term return} is absorbed on the right of a @{term bind}\<close>
lemma bind_return [simp]: "(m \<bind> return) = m"
proof (rule execute_ext)
  fix s
  show "execute (m \<bind> return) s = execute m s"
  proof (cases "execute m s" rule: result_cases)
    case (n a s)
    then show ?thesis by (simp add: execute_simps)
  next
    case (e e)
    then show ?thesis by (simp add: execute_simps)
  next
    case t
    then show ?thesis by (simp add: execute_simps)
  qed
qed

text \<open>@{term bind} is associative\<close>
lemma bind_assoc:
  fixes m :: "('a,'e,'s) state_monad"
  fixes f :: "'a \<Rightarrow> ('b,'e,'s) state_monad"
  fixes g :: "'b \<Rightarrow> ('c,'e,'s) state_monad"
  shows "(m \<bind> f) \<bind> g  =  m \<bind> (\<lambda>x. f x\<bind> g)"
proof
  fix s
  show "execute (m \<bind> f \<bind> g) s = execute (m \<bind> (\<lambda>x. f x \<bind> g)) s"
  unfolding bind_def by (cases "execute m s" rule: result_cases; simp add: execute_simps)
qed

subsection \<open>Basic Conguruence Rules\<close>

(*
  Lemma bind_case_nat_cong is required if a bind operand is a case analysis over nat.
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

lemma bind_case_bool_cong [fundef_cong]:
  assumes "x = x'" and "x = True \<Longrightarrow> f s = f' s" and "x = False \<Longrightarrow> g s = g' s"
  shows "(case x of True \<Rightarrow> f | False \<Rightarrow> g) s = (case x' of True \<Rightarrow> f' | False \<Rightarrow> g') s"
  using assms(1) assms(2) assms(3) by auto

subsection \<open>Other functions\<close>

text \<open>
  The basic accessor functions of the state monad. \<open>get\<close> returns
  the current state as result, does not fail, and does not change the state.
  \<open>put s\<close> returns unit, changes the current state to \<open>s\<close> and does not fail.
\<close>
definition get :: "('s, 'e, 's) state_monad" where
  "get = create (\<lambda>s. Normal (s, s))"

lemma execute_get [execute_simps]:
  "execute get = (\<lambda>s. Normal (s, s))"
  unfolding get_def by (auto simp add:execute_simps)

definition put :: "'s \<Rightarrow> (unit, 'e, 's) state_monad" where
  "put s = create (K (Normal ((), s)))"

lemma execute_put [execute_simps]:
  "execute (put s) = K (Normal ((), s))"
  unfolding put_def by (auto simp add:execute_simps)

definition update :: "('s \<Rightarrow> 'a \<times> 's) \<Rightarrow> ('a, 'e, 's) state_monad" where
  "update f = create (\<lambda>s. Normal (f s))"

lemma execute_update [execute_simps]:
  "execute (update f) = (\<lambda>s. Normal (f s))"
  unfolding update_def by (auto simp add:execute_simps)

text \<open>Apply a function to the current state and return the result
without changing the state.\<close>
definition applyf :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a, 'e, 's) state_monad" where
 "applyf f = get \<bind> (\<lambda>s. return (f s))"

text \<open>Modify the current state using the function passed in.\<close>
definition modify :: "('s \<Rightarrow> 's) \<Rightarrow> (unit, 'e, 's) state_monad" where
"modify f = get \<bind> (\<lambda>s::'s. put (f s))"

lemma execute_modify [execute_simps]:
  "execute (modify f) s = Normal ((), f s)"
  unfolding modify_def by (auto simp add:execute_simps)

primrec mfold :: "('a,'e,'s) state_monad list \<Rightarrow> ('a list,'e,'s) state_monad"
  where
    "mfold [] = return []"
  | "mfold (m # ms) =
      do {
        x \<leftarrow> m;
        xs \<leftarrow> mfold ms;
        return (x # xs)
      }"

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

subsection \<open>Conditional Monad\<close>

fun cond_monad:: "('s \<Rightarrow> bool) \<Rightarrow> ('a, 'e, 's) state_monad \<Rightarrow> ('a, 'e, 's) state_monad \<Rightarrow> ('a, 'e, 's) state_monad" where
"cond_monad c mt mf = 
  do {
    s \<leftarrow> get;
    if (c s) then mt else mf
  }"

definition option :: "'e \<Rightarrow> ('s \<Rightarrow> 'a option) \<Rightarrow> ('a, 'e, 's) state_monad" where
 "option x f = create (\<lambda>s. (case f s of
    Some y \<Rightarrow> execute (return y) s
  | None \<Rightarrow> execute (throw x) s))"

lemma execute_option [execute_simps]:
  "\<And>y. f s = Some y \<Longrightarrow> execute (option e f) s = execute (return y) s"
  "f s = None \<Longrightarrow> execute (option e f) s = execute (throw e) s"
  unfolding option_def by (auto simp add:execute_simps)

definition assert :: "'e \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> (unit, 'e, 's) state_monad" where
 "assert x t = create (\<lambda>s. if (t s) then execute (return ()) s else execute (throw x) s)"

lemma execute_assert [execute_simps]:
  "t s \<Longrightarrow> execute (assert e t) s = execute (return ()) s"
  "\<not> t s \<Longrightarrow> execute (assert e t) s = execute (throw e) s"
  unfolding assert_def by (auto simp add:execute_simps)

subsection \<open>Setup for Partial Function Package\<close>

text \<open>
  We can make result into a pointed cpo:
  \<^item> The order is obtained by combinin function order with result order
  \<^item> The least element is NT
\<close>

definition effect :: "('a, 'b, 'c) state_monad \<Rightarrow> 'c \<Rightarrow> 'a \<times> 'c + 'b \<times> 'c \<Rightarrow> bool" where
  effect_def: "effect c h r \<longleftrightarrow> is_Normal (execute c h) \<and> r = Inl (normal (execute c h)) \<or> is_Exception (execute c h) \<and> r = Inr (ex (execute c h))"

lemma effectE:
  assumes "effect c h r"
  obtains (normal) "is_Normal (execute c h) \<and> r = Inl (normal (execute c h))"
  | (exception) "is_Exception (execute c h) \<and> r = Inr (ex (execute c h))"
  using assms unfolding effect_def by auto

abbreviation "empty_result \<equiv> create (\<lambda>s. NT)"
abbreviation "result_ord \<equiv> flat_ord NT"
abbreviation "result_lub \<equiv> flat_lub NT"

definition sm_ord :: "('a, 'e, 's) state_monad \<Rightarrow> ('a, 'e, 's) state_monad \<Rightarrow> bool" where
  "sm_ord = img_ord execute (fun_ord result_ord)"

definition sm_lub :: "('a, 'e, 's) state_monad set \<Rightarrow> ('a, 'e, 's) state_monad" where
  "sm_lub = img_lub execute create (fun_lub result_lub)"

lemma sm_lub_empty: "sm_lub {} = empty_result"
  by(simp add: sm_lub_def img_lub_def fun_lub_def flat_lub_def)

lemma sm_ordI:
  assumes "\<And>h. execute x h = NT \<or> execute x h = execute y h"
  shows "sm_ord x y"
  using assms unfolding sm_ord_def img_ord_def fun_ord_def flat_ord_def
  by blast

lemma sm_ordE:
  assumes "sm_ord x y"
  obtains "execute x h = NT" | "execute x h = execute y h"
  using assms unfolding sm_ord_def img_ord_def fun_ord_def flat_ord_def
  by atomize_elim blast

lemma sm_interpretation: "partial_function_definitions sm_ord sm_lub"
proof -
  have "partial_function_definitions (fun_ord result_ord) (fun_lub result_lub)"
    by (rule partial_function_lift) (rule flat_interpretation)
  then have "partial_function_definitions (img_ord execute (fun_ord result_ord))
      (img_lub execute create (fun_lub result_lub))"
    by (rule partial_function_image) (auto simp add: execute_simps)
  then show "partial_function_definitions sm_ord sm_lub"
    by (simp only: sm_ord_def sm_lub_def)
qed

interpretation sm: partial_function_definitions sm_ord sm_lub
  rewrites "sm_lub {} \<equiv> empty_result"
by (fact sm_interpretation)(simp add: sm_lub_empty)

named_theorems mono

declare sm.const_mono[mono]
declare Partial_Function.call_mono[mono]

text \<open>The success predicate requires a state monad sm starting in state s to terminate successfully in state s' with return value a.\<close>

definition success :: "('a, 'e, 's) state_monad \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool" where
  success_def: "success sm s s' a \<longleftrightarrow> execute sm s \<noteq> NT"

text \<open>We can show that every predicate P is admissible if we assume successful termination.\<close>
lemma sm_step_admissible: 
  "ccpo.admissible (fun_lub result_lub) (fun_ord result_ord) (\<lambda>xa. \<forall>h r. is_Normal (xa h) \<and> r = Inl (normal (xa h)) \<or> is_Exception (xa h) \<and> r = Inr (ex (xa h)) \<longrightarrow> P h r)"
proof (rule ccpo.admissibleI)
  fix A :: "('a \<Rightarrow> ('b, 'c) result) set"
  assume ch: "Complete_Partial_Order.chain (fun_ord result_ord) A"
    and IH: "\<forall>xa\<in>A. \<forall>h r. is_Normal (xa h) \<and> r = Inl (normal (xa h)) \<or> is_Exception (xa h) \<and> r = Inr (ex (xa h)) \<longrightarrow> P h r"
  from ch have ch': "\<And>x. Complete_Partial_Order.chain result_ord {y. \<exists>f\<in>A. y = f x}" by (rule chain_fun)
  show "\<forall>h r. is_Normal (fun_lub result_lub A h) \<and> r = Inl (normal (fun_lub result_lub A h)) \<or> is_Exception (fun_lub result_lub A h) \<and> r = Inr (ex (fun_lub result_lub A h)) \<longrightarrow> P h r"
  proof (intro allI impI)
    fix h r assume "is_Normal (fun_lub result_lub A h) \<and> r = Inl (normal (fun_lub result_lub A h)) \<or> is_Exception (fun_lub result_lub A h) \<and> r = Inr (ex (fun_lub result_lub A h))"
    then show "P h r"
    proof
      assume "is_Normal (fun_lub result_lub A h) \<and> r = Inl (normal (fun_lub result_lub A h))"
      with flat_lub_in_chain[OF ch'] this[unfolded fun_lub_def]
      show "P h r" using IH
        by (smt (verit) Collect_cong mem_Collect_eq result.case_eq_if result.disc_eq_case(3))
    next
      assume "is_Exception (fun_lub result_lub A h) \<and> r = Inr (ex (fun_lub result_lub A h))"
      with flat_lub_in_chain[OF ch'] this[unfolded fun_lub_def]
      show "P h r" using IH
        by (smt (verit) Collect_cong mem_Collect_eq result.case_eq_if result.disc_eq_case(3))
    qed
  qed
qed

lemma admissible_sm: 
  "sm.admissible (\<lambda>f. \<forall>x h r. effect (f x) h r \<longrightarrow> P x h r)"
proof (rule admissible_fun[OF sm_interpretation])
  fix x
  show "ccpo.admissible sm_lub sm_ord (\<lambda>a. \<forall>h r. effect a h r \<longrightarrow> P x h r)"
    unfolding sm_ord_def sm_lub_def
  proof (intro admissible_image partial_function_lift flat_interpretation)
    show "ccpo.admissible (fun_lub result_lub) (fun_ord result_ord) ((\<lambda>a. \<forall>h r. effect a h r \<longrightarrow> P x h r) \<circ> create)"
      unfolding comp_def effect_def execute_create
      by (rule sm_step_admissible)
  qed (auto simp add: execute_simps)
qed

text \<open>
  Now we can derive an induction rule for proving partial correctness properties.
  Note that this rule requires successful termination.
\<close>

lemma fixp_induct_sm:
  fixes F :: "'c \<Rightarrow> 'c" and
        U :: "'c \<Rightarrow> 'b \<Rightarrow> ('a, 'e, 's) state_monad" and
        C :: "('b \<Rightarrow> ('a, 'e, 's) state_monad) \<Rightarrow> 'c" and
        P :: "'b \<Rightarrow> 's \<Rightarrow> 'a \<times> 's + 'e \<times> 's \<Rightarrow> bool"
  assumes mono: "\<And>x. monotone (fun_ord sm_ord) sm_ord (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub sm_lub) (fun_ord sm_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x h r. (\<And>x h r. effect (U f x) h r \<Longrightarrow> P x h r) 
    \<Longrightarrow> effect (U (F f) x) h r \<Longrightarrow> P x h r"
  assumes defined: "effect (U f x) h r"
  shows "P x h r"
  using step defined sm.fixp_induct_uc[of U F C, OF mono eq inverse2 admissible_sm, of P]
  unfolding effect_def execute_create by blast

text \<open>We now need to setup the new sm mode for the partial function package.\<close>

declaration \<open>
  Partial_Function.init "sm"
    \<^term>\<open>sm.fixp_fun\<close>
    \<^term>\<open>sm.mono_body\<close>
    @{thm sm.fixp_rule_uc}
    @{thm sm.fixp_induct_uc}
    (SOME @{thm fixp_induct_sm})
\<close>

subsection \<open>Monotonicity Results\<close>

abbreviation "mono_sm \<equiv> monotone (fun_ord sm_ord) sm_ord"

lemma execute_bind_case:
  "execute (f \<bind> g) h = (case (execute f h) of
    Normal (x, h') \<Rightarrow> execute (g x) h' | Exception e \<Rightarrow> Exception e | NT \<Rightarrow> NT)"
  by (simp add: bind_def execute_simps)

lemma bind_mono [partial_function_mono,mono]:
  assumes mf: "mono_sm B" and mg: "\<And>y. mono_sm (\<lambda>f. C y f)"
  shows "mono_sm (\<lambda>f. B f \<bind> (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> ('b, 'c, 'd) state_monad" assume fg: "sm.le_fun f g"
  from mf
  have 1: "sm_ord (B f) (B g)" by (rule monotoneD) (rule fg)
  from mg
  have 2: "\<And>y'. sm_ord (C y' f) (C y' g)" by (rule monotoneD) (rule fg)

  have "sm_ord (B f \<bind> (\<lambda>y. C y f)) (B g \<bind> (\<lambda>y. C y f))" (is "sm_ord ?L ?R")
  proof (rule sm_ordI)
    fix h
    from 1 show "execute ?L h = NT \<or> execute ?L h = execute ?R h"
      by (rule sm_ordE[where h = h]) (auto simp: execute_bind_case)
  qed
  also
  have "sm_ord (B g \<bind> (\<lambda>y'. C y' f)) (B g \<bind> (\<lambda>y'. C y' g))" (is "sm_ord ?L ?R")
  proof (rule sm_ordI)
    fix h
    show "execute ?L h = NT \<or> execute ?L h = execute ?R h"
    proof (cases "execute (B g) h")
      case (n a s)
      then have "execute ?L h = execute (C a f) s" "execute ?R h = execute (C a g) s"
        by (auto simp: execute_bind_case)
      with 2[of a] show ?thesis by (auto elim: sm_ordE)
    next
      case (e e)
      then show ?thesis by (simp add: execute_bind_case)
    next
      case t
      then have "execute ?L h = NT" by (auto simp: execute_bind_case)
      thus ?thesis ..
    qed
  qed
  finally (sm.leq_trans)
  show "sm_ord (B f \<bind> (\<lambda>y. C y f)) (B g \<bind> (\<lambda>y'. C y' g))" .
qed

lemma throw_monad_mono[mono]: "mono_sm (\<lambda>_. throw e)"
  by (simp add: monotoneI sm_ordI)

lemma return_monad_mono[mono]: "mono_sm (\<lambda>_. return x)"
  by (simp add: monotoneI sm_ordI)

lemma option_monad_mono[mono]: "mono_sm (\<lambda>_. option E x)"
  by (simp add: monotoneI sm_ordI)

definition exc:: "('a, 'b, 'c) state_monad \<Rightarrow> ('a, 'b, 'c) state_monad"
  where "exc m \<equiv> create (\<lambda>s. case execute m s of Normal (v,s') \<Rightarrow> Normal (v, s')
                                               | Exception (e, s') \<Rightarrow> Exception (e, s)
                                               | NT \<Rightarrow> NT)"

lemma exc_mono[mono]:
  fixes m::"('b \<Rightarrow> ('c, 'e, 'f) state_monad) \<Rightarrow> ('x, 'y, 'z) state_monad"
  assumes mf: "mono_sm (\<lambda>call. (m call))"
  shows "mono_sm (\<lambda>call. (exc (m call)))"

proof (rule monotoneI)
  fix f g :: "'b \<Rightarrow> ('c, 'e, 'f) state_monad"
  assume fg: "sm.le_fun f g"
  then have 1: "sm_ord (m f) (m g)" using mf by (auto dest: monotoneD)
  show "sm_ord (exc (m f)) (exc (m g))"
  proof (rule sm_ordI)
    fix h
    show "execute (exc (m f)) h = NT \<or> execute (exc (m f)) h = execute (exc (m g)) h"
    proof (rule sm_ordE[OF 1, of h])
      assume "execute (m f) h = NT"
      then show "execute (exc (m f)) h = NT \<or> execute (exc (m f)) h = execute (exc (m g)) h" unfolding exc_def by (simp add:execute_simps)
    next
      assume "execute (m f) h = execute (m g) h"
      then show "execute (exc (m f)) h = NT \<or> execute (exc (m f)) h = execute (exc (m g)) h" unfolding exc_def by (simp add:execute_simps)
    qed
  qed
qed


end
