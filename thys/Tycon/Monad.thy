section {* Monad Class *}

theory Monad
imports Functor
begin

subsection {* Class definition *}

text {* In Haskell, class \emph{Monad} is defined as follows: *}

text_raw {*
\begin{verbatim}
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
\end{verbatim}
*}

text {* We formalize class @{text monad} in a manner similar to the
@{text functor} class: We fix monomorphic versions of the class
constants, replacing type variables with @{text udom}, and assume
monomorphic versions of the class axioms. *}

text {* Because the monad laws imply the composition rule for @{text
fmap}, we declare @{text prefunctor} as the superclass, and separately
prove a subclass relationship with @{text functor}. *}

class monad = prefunctor +
  fixes returnU :: "udom \<rightarrow> udom\<cdot>'a::tycon"
  fixes bindU :: "udom\<cdot>'a \<rightarrow> (udom \<rightarrow> udom\<cdot>'a) \<rightarrow> udom\<cdot>'a"
  assumes fmapU_eq_bindU:
    "\<And>f xs. fmapU\<cdot>f\<cdot>xs = bindU\<cdot>xs\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
  assumes bindU_returnU:
    "\<And>f x. bindU\<cdot>(returnU\<cdot>x)\<cdot>f = f\<cdot>x"
  assumes bindU_bindU:
    "\<And>xs f g. bindU\<cdot>(bindU\<cdot>xs\<cdot>f)\<cdot>g = bindU\<cdot>xs\<cdot>(\<Lambda> x. bindU\<cdot>(f\<cdot>x)\<cdot>g)"

instance monad \<subseteq> "functor"
proof
  fix f g :: "udom \<rightarrow> udom" and xs :: "udom\<cdot>'a"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
    by (simp add: fmapU_eq_bindU bindU_bindU bindU_returnU)
qed

text {* As with @{text fmap}, we define the polymorphic @{text return}
and @{text bind} by coercion from the monomorphic @{text returnU} and
@{text bindU}. *}

definition return :: "'a \<rightarrow> 'a\<cdot>'m::monad"
  where "return = coerce\<cdot>(returnU :: udom \<rightarrow> udom\<cdot>'m)"

definition bind :: "'a\<cdot>'m::monad \<rightarrow> ('a \<rightarrow> 'b\<cdot>'m) \<rightarrow> 'b\<cdot>'m"
  where "bind = coerce\<cdot>(bindU :: udom\<cdot>'m \<rightarrow> _)"

abbreviation bind_syn :: "'a\<cdot>'m::monad \<Rightarrow> ('a \<rightarrow> 'b\<cdot>'m) \<Rightarrow> 'b\<cdot>'m" (infixl "\<bind>" 55)
  where "m \<bind> f \<equiv> bind\<cdot>m\<cdot>f"

subsection {* Naturality of bind and return *}

text {* The three class axioms imply naturality properties of @{text
returnU} and @{text bindU}, i.e., that both commute with @{text
fmapU}. *}

lemma fmapU_returnU [coerce_simp]:
  "fmapU\<cdot>f\<cdot>(returnU\<cdot>x) = returnU\<cdot>(f\<cdot>x)"
by (simp add: fmapU_eq_bindU bindU_returnU)

lemma fmapU_bindU [coerce_simp]:
  "fmapU\<cdot>f\<cdot>(bindU\<cdot>m\<cdot>k) = bindU\<cdot>m\<cdot>(\<Lambda> x. fmapU\<cdot>f\<cdot>(k\<cdot>x))"
by (simp add: fmapU_eq_bindU bindU_bindU)

lemma bindU_fmapU:
  "bindU\<cdot>(fmapU\<cdot>f\<cdot>xs)\<cdot>k = bindU\<cdot>xs\<cdot>(\<Lambda> x. k\<cdot>(f\<cdot>x))"
by (simp add: fmapU_eq_bindU bindU_returnU bindU_bindU)

subsection {* Polymorphic versions of class assumptions *}

lemma monad_fmap:
  fixes xs :: "'a\<cdot>'m::monad" and f :: "'a \<rightarrow> 'b"
  shows "fmap\<cdot>f\<cdot>xs = xs \<bind> (\<Lambda> x. return\<cdot>(f\<cdot>x))"
unfolding bind_def return_def fmap_def
by (simp add: coerce_simp fmapU_eq_bindU bindU_returnU)

lemma monad_left_unit [simp]: "(return\<cdot>x \<bind> f) = (f\<cdot>x)"
unfolding bind_def return_def
by (simp add: coerce_simp bindU_returnU)

lemma bind_bind:
  fixes m :: "'a\<cdot>'m::monad"
  shows "((m \<bind> f) \<bind> g) = (m \<bind> (\<Lambda> x. f\<cdot>x \<bind> g))"
unfolding bind_def
by (simp add: coerce_simp bindU_bindU)

subsection {* Derived rules *}

text {* The following properties can be derived using only the
abstract monad laws. *}

lemma monad_right_unit [simp]: "(m \<bind> return) = m"
 apply (subgoal_tac "fmap\<cdot>ID\<cdot>m = m")
  apply (simp only: monad_fmap)
  apply (simp add: eta_cfun)
 apply simp
done

lemma fmap_return: "fmap\<cdot>f\<cdot>(return\<cdot>x) = return\<cdot>(f\<cdot>x)"
by (simp add: monad_fmap)

lemma fmap_bind: "fmap\<cdot>f\<cdot>(bind\<cdot>xs\<cdot>k) = bind\<cdot>xs\<cdot>(\<Lambda> x. fmap\<cdot>f\<cdot>(k\<cdot>x))"
by (simp add: monad_fmap bind_bind)

lemma bind_fmap: "bind\<cdot>(fmap\<cdot>f\<cdot>xs)\<cdot>k = bind\<cdot>xs\<cdot>(\<Lambda> x. k\<cdot>(f\<cdot>x))"
by (simp add: monad_fmap bind_bind)

text {* Bind is strict in its first argument, if its second argument
is a strict function. *}

lemma bind_strict:
  assumes "k\<cdot>\<bottom> = \<bottom>" shows "\<bottom> \<bind> k = \<bottom>"
proof -
  have "\<bottom> \<bind> k \<sqsubseteq> return\<cdot>\<bottom> \<bind> k"
    by (intro monofun_cfun below_refl minimal)
  thus "\<bottom> \<bind> k = \<bottom>"
    by (simp add: assms)
qed

lemma congruent_bind:
  "(\<forall>m. m \<bind> k1 = m \<bind> k2) = (k1 = k2)"
 apply (safe, rule cfun_eqI)
 apply (drule_tac x="return\<cdot>x" in spec, simp)
done

subsection {* Laws for join *}

definition join :: "('a\<cdot>'m)\<cdot>'m \<rightarrow> 'a\<cdot>'m::monad"
  where "join \<equiv> \<Lambda> m. m \<bind> (\<Lambda> x. x)"

lemma join_fmap_fmap: "join\<cdot>(fmap\<cdot>(fmap\<cdot>f)\<cdot>xss) = fmap\<cdot>f\<cdot>(join\<cdot>xss)"
by (simp add: join_def monad_fmap bind_bind)

lemma join_return: "join\<cdot>(return\<cdot>xs) = xs"
by (simp add: join_def)

lemma join_fmap_return: "join\<cdot>(fmap\<cdot>return\<cdot>xs) = xs"
by (simp add: join_def monad_fmap eta_cfun bind_bind)

lemma join_fmap_join: "join\<cdot>(fmap\<cdot>join\<cdot>xsss) = join\<cdot>(join\<cdot>xsss)"
by (simp add: join_def monad_fmap bind_bind)

lemma bind_def2: "m \<bind> k = join\<cdot>(fmap\<cdot>k\<cdot>m)"
by (simp add: join_def monad_fmap eta_cfun bind_bind)

subsection {* Equivalence of monad laws and fmap/join laws *}

lemma "(return\<cdot>x \<bind> f) = (f\<cdot>x)"
by (simp only: bind_def2 fmap_return join_return)

lemma "(m \<bind> return) = m"
by (simp only: bind_def2 join_fmap_return)

lemma "((m \<bind> f) \<bind> g) = (m \<bind> (\<Lambda> x. f\<cdot>x \<bind> g))"
 apply (simp only: bind_def2)
 apply (subgoal_tac "join\<cdot>(fmap\<cdot>g\<cdot>(join\<cdot>(fmap\<cdot>f\<cdot>m))) =
    join\<cdot>(fmap\<cdot>join\<cdot>(fmap\<cdot>(fmap\<cdot>g)\<cdot>(fmap\<cdot>f\<cdot>m)))")
  apply (simp add: fmap_fmap)
 apply (simp add: join_fmap_join join_fmap_fmap)
done

subsection {* Simplification of coercions *}

text {* We configure rewrite rules that push coercions inwards, and
reduce them to coercions on simpler types. *}

lemma coerce_return [coerce_simp]:
  "COERCE('a\<cdot>'m,'b\<cdot>'m::monad)\<cdot>(return\<cdot>x) = return\<cdot>(COERCE('a,'b)\<cdot>x)"
by (simp add: coerce_functor fmap_return)

lemma coerce_bind [coerce_simp]:
  fixes m :: "'a\<cdot>'m::monad" and k :: "'a \<rightarrow> 'b\<cdot>'m"
  shows "COERCE('b\<cdot>'m,'c\<cdot>'m)\<cdot>(m \<bind> k) = m \<bind> (\<Lambda> x. COERCE('b\<cdot>'m,'c\<cdot>'m)\<cdot>(k\<cdot>x))"
by (simp add: coerce_functor fmap_bind)

lemma bind_coerce [coerce_simp]:
  fixes m :: "'a\<cdot>'m::monad" and k :: "'b \<rightarrow> 'c\<cdot>'m"
  shows "COERCE('a\<cdot>'m,'b\<cdot>'m)\<cdot>m \<bind> k = m \<bind> (\<Lambda> x. k\<cdot>(COERCE('a,'b)\<cdot>x))"
by (simp add: coerce_functor bind_fmap)

end
