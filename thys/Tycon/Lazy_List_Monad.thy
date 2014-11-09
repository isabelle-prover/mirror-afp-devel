section {* Lazy list monad *}

theory Lazy_List_Monad
imports Monad_Zero_Plus
begin

text {* To illustrate the general process of defining a new type
constructor, we formalize the datatype of lazy lists. Below are the
Haskell datatype definition and class instances. *}

text_raw {*
\begin{verbatim}
data List a = Nil | Cons a (List a)

instance Functor List where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

instance Monad List where
  return x        = Cons x Nil
  Nil       >>= k = Nil
  Cons x xs >>= k = mplus (k x) (xs >>= k)

instance MonadZero List where
  mzero = Nil

instance MonadPlus List where
  mplus Nil         ys = ys
  mplus (Cons x xs) ys = Cons x (mplus xs ys)
\end{verbatim}
*}

subsection {* Type definition *}

text {* The first step is to register the datatype definition with
@{text tycondef}. *}

tycondef 'a\<cdot>llist = LNil | LCons (lazy "'a") (lazy "'a\<cdot>llist")

text {* The @{text tycondef} command generates lots of theorems
automatically, but there are a few more involving @{text coerce} and
@{text fmapU} that we still need to prove manually. These proofs could
be automated in a later version of @{text tycondef}. *}

lemma coerce_llist_abs [simp]: "coerce\<cdot>(llist_abs\<cdot>x) = llist_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: llist_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_llist)
done

lemma coerce_LNil [simp]: "coerce\<cdot>LNil = LNil"
unfolding LNil_def by simp

lemma coerce_LCons [simp]: "coerce\<cdot>(LCons\<cdot>x\<cdot>xs) = LCons\<cdot>(coerce\<cdot>x)\<cdot>(coerce\<cdot>xs)"
unfolding LCons_def by simp

lemma fmapU_llist_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>llist) = \<bottom>"
  "fmapU\<cdot>f\<cdot>LNil = LNil"
  "fmapU\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs) = LCons\<cdot>(f\<cdot>x)\<cdot>(fmapU\<cdot>f\<cdot>xs)"
unfolding fmapU_llist_def llist_map_def
apply (subst fix_eq, simp)
apply (subst fix_eq, simp add: LNil_def)
apply (subst fix_eq, simp add: LCons_def)
done

subsection {* Class instances *}

text {* The @{text tycondef} command defines @{text fmapU} for us and
proves a @{text prefunctor} class instance automatically. For the
@{text functor} instance we only need to prove the composition law,
which we can do by induction. *}

instance llist :: "functor"
proof
  fix f g and xs :: "udom\<cdot>llist"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
    by (induct xs rule: llist.induct) simp_all
qed

text {* For the other class instances, we need to provide definitions
for a few constants: @{text returnU}, @{text bindU} @{text zeroU}, and
@{text plusU}. We can use ordinary commands like @{text definition}
and @{text fixrec} for this purpose. Finally we prove the class
axioms, along with a few helper lemmas, using ordinary proof
procedures like induction. *}

instantiation llist :: monad_zero_plus
begin

fixrec plusU_llist :: "udom\<cdot>llist \<rightarrow> udom\<cdot>llist \<rightarrow> udom\<cdot>llist"
  where "plusU_llist\<cdot>LNil\<cdot>ys = ys"
  | "plusU_llist\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>ys = LCons\<cdot>x\<cdot>(plusU_llist\<cdot>xs\<cdot>ys)"

lemma plusU_llist_strict [simp]: "plusU\<cdot>\<bottom>\<cdot>ys = (\<bottom>::udom\<cdot>llist)"
by fixrec_simp

fixrec bindU_llist :: "udom\<cdot>llist \<rightarrow> (udom \<rightarrow> udom\<cdot>llist) \<rightarrow> udom\<cdot>llist"
  where "bindU_llist\<cdot>LNil\<cdot>k = LNil"
  | "bindU_llist\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>k = plusU\<cdot>(k\<cdot>x)\<cdot>(bindU_llist\<cdot>xs\<cdot>k)"

lemma bindU_llist_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>llist)"
by fixrec_simp

definition zeroU_llist_def:
  "zeroU = LNil"

definition returnU_llist_def:
  "returnU = (\<Lambda> x. LCons\<cdot>x\<cdot>LNil)"

lemma plusU_LNil_right: "plusU\<cdot>xs\<cdot>LNil = xs"
by (induct xs rule: llist.induct) simp_all

lemma plusU_llist_assoc:
  fixes xs ys zs :: "udom\<cdot>llist"
  shows "plusU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>zs = plusU\<cdot>xs\<cdot>(plusU\<cdot>ys\<cdot>zs)"
by (induct xs rule: llist.induct) simp_all

lemma bindU_plusU_llist:
  fixes xs ys :: "udom\<cdot>llist" shows
  "bindU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>f = plusU\<cdot>(bindU\<cdot>xs\<cdot>f)\<cdot>(bindU\<cdot>ys\<cdot>f)"
by (induct xs rule: llist.induct) (simp_all add: plusU_llist_assoc)

instance proof
  fix x :: "udom"
  fix f :: "udom \<rightarrow> udom"
  fix h k :: "udom \<rightarrow> udom\<cdot>llist"
  fix xs ys zs :: "udom\<cdot>llist"
  show "fmapU\<cdot>f\<cdot>xs = bindU\<cdot>xs\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct xs rule: llist.induct, simp_all add: returnU_llist_def)
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>k = k\<cdot>x"
    by (simp add: returnU_llist_def plusU_LNil_right)
  show "bindU\<cdot>(bindU\<cdot>xs\<cdot>h)\<cdot>k = bindU\<cdot>xs\<cdot>(\<Lambda> x. bindU\<cdot>(h\<cdot>x)\<cdot>k)"
    by (induct xs rule: llist.induct)
       (simp_all add: bindU_plusU_llist)
  show "bindU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>k = plusU\<cdot>(bindU\<cdot>xs\<cdot>k)\<cdot>(bindU\<cdot>ys\<cdot>k)"
    by (induct xs rule: llist.induct)
       (simp_all add: plusU_llist_assoc)
  show "plusU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>zs = plusU\<cdot>xs\<cdot>(plusU\<cdot>ys\<cdot>zs)"
    by (rule plusU_llist_assoc)
  show "bindU\<cdot>zeroU\<cdot>k = zeroU"
    by (simp add: zeroU_llist_def)
  show "fmapU\<cdot>f\<cdot>(plusU\<cdot>xs\<cdot>ys) = plusU\<cdot>(fmapU\<cdot>f\<cdot>xs)\<cdot>(fmapU\<cdot>f\<cdot>ys)"
    by (induct xs rule: llist.induct) simp_all
  show "fmapU\<cdot>f\<cdot>zeroU = (zeroU :: udom\<cdot>llist)"
    by (simp add: zeroU_llist_def)
  show "plusU\<cdot>zeroU\<cdot>xs = xs"
    by (simp add: zeroU_llist_def)
  show "plusU\<cdot>xs\<cdot>zeroU = xs"
    by (simp add: zeroU_llist_def plusU_LNil_right)
qed

end

subsection {* Transfer properties to polymorphic versions *}

text {* After proving the class instances, there is still one more
step: We must transfer all the list-specific lemmas about the
monomorphic constants (e.g., @{text fmapU} and @{text bindU}) to the
corresponding polymorphic constants (@{text fmap} and @{text bind}).
These lemmas primarily consist of the defining equations for each
constant. The polymorphic constants are defined using @{text coerce},
so the proofs proceed by unfolding the definitions and simplifying
with the @{text coerce_simp} rules. *}

lemma fmap_llist_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>llist) = \<bottom>"
  "fmap\<cdot>f\<cdot>LNil = LNil"
  "fmap\<cdot>f\<cdot>(LCons\<cdot>x\<cdot>xs) = LCons\<cdot>(f\<cdot>x)\<cdot>(fmap\<cdot>f\<cdot>xs)"
unfolding fmap_def by simp_all

lemma mplus_llist_simps [simp]:
  "mplus\<cdot>(\<bottom>::'a\<cdot>llist)\<cdot>ys = \<bottom>"
  "mplus\<cdot>LNil\<cdot>ys = ys"
  "mplus\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>ys = LCons\<cdot>x\<cdot>(mplus\<cdot>xs\<cdot>ys)"
unfolding mplus_def by simp_all

lemma bind_llist_simps [simp]:
  "bind\<cdot>(\<bottom>::'a\<cdot>llist)\<cdot>f = \<bottom>"
  "bind\<cdot>LNil\<cdot>f = LNil"
  "bind\<cdot>(LCons\<cdot>x\<cdot>xs)\<cdot>f = mplus\<cdot>(f\<cdot>x)\<cdot>(bind\<cdot>xs\<cdot>f)"
unfolding bind_def mplus_def
by (simp_all add: coerce_simp)

lemma return_llist_def:
  "return = (\<Lambda> x. LCons\<cdot>x\<cdot>LNil)"
unfolding return_def returnU_llist_def
by (simp add: coerce_simp)

lemma mzero_llist_def:
  "mzero = LNil"
unfolding mzero_def zeroU_llist_def
by simp

lemma join_llist_simps [simp]:
  "join\<cdot>(\<bottom>::'a\<cdot>llist\<cdot>llist) = \<bottom>"
  "join\<cdot>LNil = LNil"
  "join\<cdot>(LCons\<cdot>xs\<cdot>xss) = mplus\<cdot>xs\<cdot>(join\<cdot>xss)"
unfolding join_def by simp_all

end
