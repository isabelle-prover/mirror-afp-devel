theory StateMonad
imports Main "HOL-Library.Monad_Syntax" Utils Solidity_Symbex
begin

section "State Monad with Exceptions"

datatype ('n, 'e) result = Normal (normal: 'n) | Exception (exception: 'e)

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

fun return :: "'a \<Rightarrow> ('a, 'e, 's) state_monad"
where "return a s = Normal (a, s)"

fun throw :: "'e \<Rightarrow> ('a, 'e, 's) state_monad"
where "throw e s = Exception e"

fun bind :: "('a, 'e, 's) state_monad \<Rightarrow> ('a \<Rightarrow> ('b, 'e, 's) state_monad) \<Rightarrow> ('b, 'e, 's) state_monad" (infixl ">>=" 60)
where "bind f g s = (case f s of
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

fun
  assert :: "'e \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> (unit, 'e, 's) state_monad" where
 "assert x t = (\<lambda>s. if (t s) then return () s else throw x s)"

fun
  option :: "'e \<Rightarrow> ('s \<Rightarrow> 'a option) \<Rightarrow> ('a, 'e, 's) state_monad" where
 "option x f = (\<lambda>s. (case f s of
    Some y \<Rightarrow> return y s
  | None \<Rightarrow> throw x s))"

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

section "Hoare Logic"

named_theorems wprule

definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('a,'e,'s) state_monad \<Rightarrow> 
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 
             ('e \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (case f s of
                   Normal (r,s') \<Rightarrow> Q r s'
                 | Exception e \<Rightarrow> E e)"

lemma weaken:
  assumes "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
      and "\<forall>s. P s \<longrightarrow> Q s"
    shows "\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  using assms by (simp add: valid_def)

lemma strengthen:
  assumes "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
      and "\<forall>a s. Q a s \<longrightarrow> R a s"
    shows "\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding valid_def
proof(rule allI[OF impI])
  fix s
  assume "P s"
  show "case f s of Normal (r, s') \<Rightarrow> R r s' | Exception e \<Rightarrow> E e"
  proof (cases "f s")
    case (n a s')
    then show ?thesis using assms valid_def \<open>P s\<close>
      by (metis case_prod_conv result.simps(5))
  next
    case (e e)
    then show ?thesis using assms valid_def \<open>P s\<close>
      by (metis result.simps(6))
  qed
qed

definition wp
  where "wp f P E s \<equiv> (case f s of
                   Normal (r,s') \<Rightarrow> P r s'
                 | Exception e \<Rightarrow> E e)"

declare wp_def [solidity_symbex]

lemma wp_valid: assumes "\<And>s. P s \<Longrightarrow> (wp f Q E s)" shows "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def by (metis assms wp_def)

lemma valid_wp: assumes "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" shows "\<And>s. P s \<Longrightarrow> (wp f Q E s)"
  by (metis assms valid_def wp_def)

lemma put: "\<lbrace>\<lambda>s. P () x\<rbrace> put x \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  using valid_def by fastforce

lemma put':
  assumes "\<forall>s. P s \<longrightarrow> Q () x"
  shows "\<lbrace>\<lambda>s. P s\<rbrace> put x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  using assms weaken[OF put, of P Q x E] by blast

lemma wpput[wprule]: 
  assumes "P () x"
  shows "wp (put x) P E s"
  unfolding wp_def using assms by simp

lemma get: "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  using valid_def by fastforce

lemma get':
  assumes "\<forall>s. P s \<longrightarrow> Q s s"
  shows "\<lbrace>\<lambda>s. P s\<rbrace> get \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  using assms weaken[OF get] by blast

lemma wpget[wprule]: 
  assumes "P s s"
  shows "wp get P E s"
  unfolding wp_def using assms by simp

lemma return: "\<lbrace>\<lambda>s. P x s\<rbrace> return x \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  using valid_def by fastforce

lemma return':
  assumes "\<forall>s. P s \<longrightarrow> Q x s"
  shows "\<lbrace>\<lambda>s. P s\<rbrace> return x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  using assms weaken[OF return, of P Q x E] by blast

lemma wpreturn[wprule]: 
  assumes "P x s"
  shows "wp (return x) P E s"
  unfolding wp_def using assms by simp

lemma bind:
  assumes "\<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
      and "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>"
    shows "\<lbrace>A\<rbrace> f \<bind> g \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def
proof (rule allI[OF impI])
  fix s assume a: "A s"
  show "case (f \<bind> g) s of Normal (r, s') \<Rightarrow> C r s' | Exception e \<Rightarrow> E e"
  proof (cases "f s" rule:result_cases)
    case nf: (n a s')
    with assms(2) a have b: "B a s'" using valid_def[where ?f=f] by auto
    then show ?thesis
    proof (cases "g a s'" rule:result_cases)
      case ng: (n a' s'')
      with assms(1) b have c: "C a' s''" using valid_def[where ?f="g a"] by fastforce
      moreover from ng nf have "(f \<bind> g) s = Normal (a', s'')" by simp
      ultimately show ?thesis by simp
    next
      case eg: (e e)
      with assms(1) b have c: "E e" using valid_def[where ?f="g a"] by fastforce
      moreover from eg nf have "(f \<bind> g) s = Exception e" by simp
      ultimately show ?thesis by simp
    qed
  next
    case (e e)
    with a assms(2) have "E e" using valid_def[where ?f=f] by auto
    moreover from e have "(f \<bind> g) s = Exception e" by simp
    ultimately show ?thesis by simp
  qed
qed

lemma wpbind[wprule]:
  assumes "wp f (\<lambda>a. (wp (g a) P E)) E s"
  shows "wp (f \<bind> g) P E s"
proof (cases "f s" rule:result_cases)
  case nf: (n a s')
  then have **:"wp (g a) P E s'" using wp_def[of f "\<lambda>a. wp (g a) P E"] assms by simp
  show ?thesis
  proof (cases "g a s'" rule:result_cases)
    case ng: (n a' s'')
    then have "P a' s''" using wp_def[of "g a" P] ** by simp
    moreover from nf ng have "(f \<bind> g) s = Normal (a', s'')" by simp
    ultimately show ?thesis using wp_def by fastforce
  next
    case (e e)
    then have "E e" using wp_def[of "g a" P] ** by simp
    moreover from nf e have "(f \<bind> g) s = Exception e" by simp
    ultimately show ?thesis using wp_def by fastforce
  qed
next
  case (e e)
  then have "E e" using wp_def[of f "\<lambda>a. wp (g a) P E"] assms by simp
  moreover from e have "(f \<bind> g) s = Exception e" by simp
  ultimately show ?thesis using wp_def by fastforce
qed

lemma wpassert[wprule]:
  assumes "t s \<Longrightarrow> wp (return ()) P E s"
      and "\<not> t s \<Longrightarrow> wp (throw x) P E s"
    shows "wp (assert x t) P E s"
  using assms unfolding wp_def by simp

lemma throw:
  assumes "E x"
  shows "\<lbrace>P\<rbrace> throw x \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  using valid_def assms by fastforce

lemma wpthrow[wprule]:
  assumes "E x"
  shows "wp (throw x) P E s"
  unfolding wp_def using assms by simp

lemma applyf:
    "\<lbrace>\<lambda>s. P (f s) s\<rbrace> applyf f \<lbrace>\<lambda>a s. P a s\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: valid_def)

lemma applyf':
  assumes "\<forall>s. P s \<longrightarrow> Q (f s) s"
  shows "\<lbrace>\<lambda>s. P s\<rbrace> applyf f \<lbrace>\<lambda>a s. Q a s\<rbrace>,\<lbrace>E\<rbrace>"
  using assms weaken[OF applyf] by blast

lemma wpapplyf[wprule]:
  assumes "P (f s) s"
  shows "wp (applyf f) P E s"
  unfolding wp_def using assms by simp

lemma modify:
  "\<lbrace>\<lambda>s. P () (f s)\<rbrace> modify f \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>"
  apply simp
  apply (rule bind,rule allI)
  apply (rule put)
  apply (rule get)
  done

lemma modify':
  assumes "\<forall>s. P s \<longrightarrow> Q () (f s)"
  shows "\<lbrace>\<lambda>s. P s\<rbrace> modify f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  using assms weaken[OF modify, of P Q _ E] by blast

lemma wpmodify[wprule]:
  assumes "P () (f s)"
  shows "wp (modify f) P E s"
  unfolding wp_def using assms by simp

lemma wpcasenat[wprule]:
  assumes "(y=(0::nat) \<Longrightarrow> wp (f y) P E s)"
      and "\<And>x. y=Suc x \<Longrightarrow> wp (g x) P E s"
  shows "wp (case y::nat of 0 \<Rightarrow> f y | Suc x \<Rightarrow> g x) P E s"
  by (metis assms(1) assms(2) not0_implies_Suc old.nat.simps(4) old.nat.simps(5))

lemma wpif[wprule]:
  assumes "c \<Longrightarrow> wp f P E s"
      and "\<not>c \<Longrightarrow> wp g P E s"
  shows "wp (if c then f else g) P E s"
  using assms by simp

lemma wpsome[wprule]:
  assumes "\<And>y. x = Some y \<Longrightarrow> wp (f y) P E s"
      and "x = None \<Longrightarrow> wp g P E s"
  shows "wp (case x of Some y \<Rightarrow> f y | None \<Rightarrow> g) P E s"
  using assms unfolding wp_def by (simp split: option.split)

lemma wpoption[wprule]:
  assumes "\<And>y. f s = Some y \<Longrightarrow> wp (return y) P E s"
      and "f s = None \<Longrightarrow> wp (throw x) P E s"
  shows "wp (option x f) P E s"
  using assms unfolding wp_def by (auto split:option.split)

lemma wpprod[wprule]:
  assumes "\<And>x y. a = (x,y) \<Longrightarrow> wp (f x y) P E s"
  shows "wp (case a of (x, y) \<Rightarrow> f x y) P E s"
  using assms unfolding wp_def
  by (simp split: prod.split)

method wp = rule wprule; wp?
method wpvcg = rule wp_valid, wp

lemma "\<lbrace>\<lambda>s. s=5\<rbrace> do {
        put (5::nat);
        x \<leftarrow> get;
        return x
       } \<lbrace>\<lambda>a s. s=5\<rbrace>,\<lbrace>\<lambda>e. False\<rbrace>"
  by (wpvcg, simp)
end
