(*<*)
(* Author: Dmitriy Traytel *)

section {* A Codatatype of Formal Languages *}

theory Coinductive_Language
imports Main
begin

hide_const (open) Inter
(*>*)

section {* Introduction *}

text {*
We define formal languages as a codataype of infinite trees branching over the
alphabet @{typ 'a}. Each node in such a tree indicates whether the path to this
node constitutes a word inside or outside of the language.

*}

codatatype 'a language = Lang (\<oo>: bool) (\<dd>: "'a \<Rightarrow> 'a language")

text {* 
This codatatype is isormorphic to the set of lists representation of languages,
but caters for definitions by corecursion and proofs by coinduction.

Regular operations on languages are then defined by primitive corecursion.
A difficulty arises here, since the standard definitions of concatenation and
iteration from the coalgebraic literature are not primitively corecursive---they
require guardedness up-to union/concatenation. Without support for up-to corecursion,
these operation must be defined as a composition of primitive ones (and proved being
equal to the standard definitions). As an exercise in coinduction we also prove the
axioms of Kleene algebra for the defined regular operations.

Furthermore, a language for context-free grammars given by productions in Greibach
normal form and an initial nonterminal is constructed by primitive corecursion,
yielding an executable decision procedure for the word problem without further ado.
*}
(*<*)
(* custom coinduction theorem (getting rid of rel_fun) *)
declare language.coinduct_strong[unfolded rel_fun_def, simplified, case_names Lang, coinduct pred]
(*>*)

section {* Regular Languages *}

primcorec Zero :: "'a language" where
  "\<oo> Zero = False"
| "\<dd> Zero = (\<lambda>_. Zero)"

primcorec One :: "'a language" where
  "\<oo> One = True"
| "\<dd> One = (\<lambda>_. Zero)"

primcorec Atom :: "'a \<Rightarrow> 'a language" where
  "\<oo> (Atom a) = False"
| "\<dd> (Atom a) = (\<lambda>b. if a = b then One else Zero)"

primcorec Plus :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "\<oo> (Plus r s) = (\<oo> r \<or> \<oo> s)"
| "\<dd> (Plus r s) = (\<lambda>a. Plus (\<dd> r a) (\<dd> s a))"

theorem Plus_ZeroL[simp]: "Plus Zero r = r"
  by (coinduction arbitrary: r) simp

theorem Plus_ZeroR[simp]: "Plus r Zero = r"
  by (coinduction arbitrary: r) simp

theorem Plus_assoc: "Plus (Plus r s) t = Plus r (Plus s t)"
  by (coinduction arbitrary: r s t) auto

theorem Plus_comm: "Plus r s = Plus s r"
  by (coinduction arbitrary: r s) auto

lemma Plus_rotate: "Plus r (Plus s t) = Plus s (Plus r t)"
  using Plus_assoc Plus_comm by metis

theorem Plus_idem: "Plus r r = r"
  by (coinduction arbitrary: r) auto

lemma Plus_idem_assoc: "Plus r (Plus r s) = Plus r s"
  by (metis Plus_assoc Plus_idem)

lemmas Plus_ACI[simp] = Plus_rotate Plus_comm Plus_assoc Plus_idem_assoc Plus_idem

lemma Plus_OneL[simp]: "\<oo> r \<Longrightarrow> Plus One r = r"
  by (coinduction arbitrary: r) auto

lemma Plus_OneR[simp]: "\<oo> r \<Longrightarrow> Plus r One = r"
  by (coinduction arbitrary: r) auto

text {*
  Concatenation is not primitively corecursive---the corecursive call of its derivative is
  guarded by @{term Plus}. However, it can be defined as a composition of two primitively
  corecursive functions.
*}

primcorec TimesLR :: "'a language \<Rightarrow> 'a language \<Rightarrow> ('a \<times> bool) language" where
  "\<oo> (TimesLR r s) = (\<oo> r \<and> \<oo> s)"
| "\<dd> (TimesLR r s) = (\<lambda>(a, b). 
   if b then TimesLR (\<dd> r a) s else if \<oo> r then TimesLR (\<dd> s a) One else Zero)"

primcorec Times_Plus :: "('a \<times> bool) language \<Rightarrow> 'a language" where
  "\<oo> (Times_Plus r) = \<oo> r"
| "\<dd> (Times_Plus r) = (\<lambda>a. Times_Plus (Plus (\<dd> r (a, True)) (\<dd> r (a, False))))"

lemma TimesLR_ZeroL[simp]: "TimesLR Zero r = Zero"
  by (coinduction arbitrary: r) auto

lemma TimesLR_ZeroR[simp]: "TimesLR r Zero = Zero"
  by (coinduction arbitrary: r) (auto intro: exI[of _ Zero])

lemma TimesLR_PlusL[simp]: "TimesLR (Plus r s) t = Plus (TimesLR r t) (TimesLR s t)"
  by (coinduction arbitrary: r s t) auto

lemma TimesLR_PlusR[simp]: "TimesLR r (Plus s t) = Plus (TimesLR r s) (TimesLR r t)"
  by (coinduction arbitrary: r s t) auto

lemma Times_Plus_Zero[simp]: "Times_Plus Zero = Zero"
  by coinduction simp

lemma Times_Plus_Plus[simp]: "Times_Plus (Plus r s) = Plus (Times_Plus r) (Times_Plus s)"
proof (coinduction arbitrary: r s)
  case (Lang r s)
  then show ?case unfolding Times_Plus.sel Plus.sel
    by (intro conjI[OF refl]) (metis Plus_comm Plus_rotate) 
qed

lemma Times_Plus_TimesLR_One[simp]: "Times_Plus (TimesLR r One) = r"
  by (coinduction arbitrary: r) simp

lemma Times_Plus_TimesLR_PlusL[simp]:
  "Times_Plus (TimesLR (Plus r s) t) = Plus (Times_Plus (TimesLR r t)) (Times_Plus (TimesLR s t))"
  by (coinduction arbitrary: r s t) auto

lemma Times_Plus_TimesLR_PlusR[simp]:
  "Times_Plus (TimesLR r (Plus s t)) = Plus (Times_Plus (TimesLR r s)) (Times_Plus (TimesLR r t))"
  by (coinduction arbitrary: r s t) auto

definition Times :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "Times r s = Times_Plus (TimesLR r s)"

lemma \<oo>_Times[simp]:
  "\<oo> (Times r s) = (\<oo> r \<and> \<oo> s)"
  unfolding Times_def by simp

lemma \<dd>_Times[simp]:
  "\<dd> (Times r s) = (\<lambda>a. if \<oo> r then Plus (Times (\<dd> r a) s) (\<dd> s a) else Times (\<dd> r a) s)"
  unfolding Times_def by (rule ext, coinduction arbitrary: r s) auto

theorem Times_ZeroL[simp]: "Times Zero r = Zero"
  by coinduction simp

theorem Times_ZeroR[simp]: "Times r Zero = Zero"
  by (coinduction arbitrary: r) auto

theorem Times_OneL[simp]: "Times One r = r"
  by (coinduction arbitrary: r rule: language.coinduct_strong) (simp add: rel_fun_def)

theorem Times_OneR[simp]: "Times r One = r"
  by (coinduction arbitrary: r) simp



text {*
  Coinduction up-to @{term Plus}--congruence relaxes the coinduction hypothesis by requiring
  membership in the congruence closure of the bisimulation rather than in the bisimulation itself.
*}

inductive Plus_cong where
  Refl[intro]: "x = y \<Longrightarrow> Plus_cong R x y"
| Base[intro]: "R x y \<Longrightarrow> Plus_cong R x y"
| Sym: "Plus_cong R x y \<Longrightarrow> Plus_cong R y x"
| Trans[intro]: "Plus_cong R x y \<Longrightarrow> Plus_cong R y z \<Longrightarrow> Plus_cong R x z"
| Plus[intro]: "\<lbrakk>Plus_cong R x y; Plus_cong R x' y'\<rbrakk> \<Longrightarrow> Plus_cong R (Plus x x') (Plus y y')"

lemma language_coinduct_upto_Plus[unfolded rel_fun_def, simplified, case_names Lang, consumes 1]: 
  assumes R: "R L K" and hyp:
    "(\<And>L K. R L K \<Longrightarrow> \<oo> L = \<oo> K \<and> rel_fun op = (Plus_cong R) (\<dd> L) (\<dd> K))"
  shows "L = K"
proof (coinduct rule: language.coinduct[of "Plus_cong R"])
  fix L K assume "Plus_cong R L K"
  then show "\<oo> L = \<oo> K \<and> rel_fun op = (Plus_cong R) (\<dd> L) (\<dd> K)" using hyp
    by (induct rule: Plus_cong.induct) (auto simp: rel_fun_def intro: Sym)
qed (intro Base R)

theorem Times_PlusL[simp]: "Times (Plus r s) t = Plus (Times r t) (Times s t)"
  by (coinduction arbitrary: r s rule: language_coinduct_upto_Plus) auto

theorem Times_PlusR[simp]: "Times r (Plus s t) = Plus (Times r s) (Times r t)"
  by (coinduction arbitrary: r s rule: language_coinduct_upto_Plus) fastforce

theorem Times_assoc[simp]: "Times (Times r s) t = Times r (Times s t)"
  by (coinduction arbitrary: r s t rule: language_coinduct_upto_Plus) fastforce

text {*
  Similarly to @{term Times}, iteration is not primitively corecursive (guardedness by
  @{term Times} is required). We apply a similar trick to obtain its definition.
*}

primcorec StarLR :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "\<oo> (StarLR r s) = \<oo> r"
| "\<dd> (StarLR r s) = (\<lambda>a. StarLR (\<dd> (Times r (Plus One s)) a) s)"

lemma StarLR_Zero[simp]: "StarLR Zero r = Zero"
  by coinduction auto

lemma StarLR_Plus[simp]: "StarLR (Plus r s) t = Plus (StarLR r t) (StarLR s t)"
  by (coinduction arbitrary: r s) (auto simp del: Plus_ACI Times_PlusR)

lemma StarLR_Times_Plus_One[simp]: "StarLR (Times r (Plus One s)) s = StarLR r s"
proof (coinduction arbitrary: r s)
  case Lang
  { fix a
    def L \<equiv> "Plus (\<dd> r a) (Plus (Times (\<dd> r a) s) (\<dd> s a))"
    and R \<equiv> "Times (Plus (\<dd> r a) (Plus (Times (\<dd> r a) s) (\<dd> s a))) s"
    have "Plus L (Plus R (\<dd> s a)) = Plus (Plus L (\<dd> s a)) R" by (metis Plus_assoc Plus_comm)
    also have "Plus L (\<dd> s a) = L" unfolding L_def by simp
    finally have "Plus L (Plus R (\<dd> s a)) = Plus L R" .
  }
  then show ?case by (auto simp del: StarLR_Plus Plus_assoc Times_PlusL)
qed

lemma StarLR_Times: "StarLR (Times r s) t = Times r (StarLR s t)"
  by (coinduction arbitrary: r s t rule: language_coinduct_upto_Plus)
    (fastforce simp del: Plus_ACI Times_PlusR)

definition Star :: "'a language \<Rightarrow> 'a language" where
  "Star r = StarLR One r"

lemma \<oo>_Star[simp]: "\<oo> (Star r)"
  unfolding Star_def by simp

lemma \<dd>_Star[simp]: "\<dd> (Star r) = (\<lambda>a. Times (\<dd> r a) (Star r))"
  unfolding Star_def by (rule ext, coinduction arbitrary: r)
    (auto simp add: Star_def StarLR_Times[symmetric])

lemma Star_Zero[simp]: "Star Zero = One"
  by coinduction auto

lemma Star_One[simp]: "Star One = One"
  by coinduction auto

lemma Star_unfoldL: "Star r = Plus One (Times r (Star r))"
  by coinduction auto

primcorec Inter :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "\<oo> (Inter r s) = (\<oo> r \<and> \<oo> s)"
| "\<dd> (Inter r s) = (\<lambda>a. Inter (\<dd> r a) (\<dd> s a))"

primcorec Not :: "'a language \<Rightarrow> 'a language" where
  "\<oo> (Not r) = (\<not> \<oo> r)"
| "\<dd> (Not r) = (\<lambda>a. Not (\<dd> r a))"

primcorec Full :: "'a language" ("\<Sigma>\<^sup>*") where
  "\<oo> Full = True"
| "\<dd> Full = (\<lambda>_. Full)"

text {*
  Shuffle product is not primitively corecursive---the corecursive call of its derivative is
  guarded by @{term Plus}. However, it can be defined as a composition of two primitively
  corecursive functions.
*}

primcorec ShuffleLR :: "'a language \<Rightarrow> 'a language \<Rightarrow> ('a \<times> bool) language" where
  "\<oo> (ShuffleLR r s) = (\<oo> r \<and> \<oo> s)"
| "\<dd> (ShuffleLR r s) = (\<lambda>(a, b). if b then ShuffleLR (\<dd> r a) s else ShuffleLR r (\<dd> s a))"

primcorec Shuffle_Plus :: "('a \<times> bool) language \<Rightarrow> 'a language" where
  "\<oo> (Shuffle_Plus r) = \<oo> r"
| "\<dd> (Shuffle_Plus r) = (\<lambda>a. Shuffle_Plus (Plus (\<dd> r (a, True)) (\<dd> r (a, False))))"

lemma ShuffleLR_ZeroL[simp]: "ShuffleLR Zero r = Zero"
  by (coinduction arbitrary: r) auto

lemma ShuffleLR_ZeroR[simp]: "ShuffleLR r Zero = Zero"
  by (coinduction arbitrary: r) (auto intro: exI[of _ Zero])

lemma ShuffleLR_PlusL[simp]: "ShuffleLR (Plus r s) t = Plus (ShuffleLR r t) (ShuffleLR s t)"
  by (coinduction arbitrary: r s t) auto

lemma ShuffleLR_PlusR[simp]: "ShuffleLR r (Plus s t) = Plus (ShuffleLR r s) (ShuffleLR r t)"
  by (coinduction arbitrary: r s t) auto

lemma Shuffle_Plus_Zero[simp]: "Shuffle_Plus Zero = Zero"
  by coinduction simp

lemma Shuffle_Plus_Plus[simp]: "Shuffle_Plus (Plus r s) = Plus (Shuffle_Plus r) (Shuffle_Plus s)"
proof (coinduction arbitrary: r s)
  case (Lang r s)
  then show ?case unfolding Shuffle_Plus.sel Plus.sel
    by (intro conjI[OF refl]) (metis Plus_comm Plus_rotate) 
qed

lemma Shuffle_Plus_ShuffleLR_One[simp]: "Shuffle_Plus (ShuffleLR r One) = r"
  by (coinduction arbitrary: r) simp

lemma Shuffle_Plus_ShuffleLR_PlusL[simp]:
  "Shuffle_Plus (ShuffleLR (Plus r s) t) = Plus (Shuffle_Plus (ShuffleLR r t)) (Shuffle_Plus (ShuffleLR s t))"
  by (coinduction arbitrary: r s t) auto

lemma Shuffle_Plus_ShuffleLR_PlusR[simp]:
  "Shuffle_Plus (ShuffleLR r (Plus s t)) = Plus (Shuffle_Plus (ShuffleLR r s)) (Shuffle_Plus (ShuffleLR r t))"
  by (coinduction arbitrary: r s t) auto

definition Shuffle :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "Shuffle r s = Shuffle_Plus (ShuffleLR r s)"

lemma \<oo>_Shuffle[simp]:
  "\<oo> (Shuffle r s) = (\<oo> r \<and> \<oo> s)"
  unfolding Shuffle_def by simp

lemma \<dd>_Shuffle[simp]:
  "\<dd> (Shuffle r s) = (\<lambda>a. Plus (Shuffle (\<dd> r a) s) (Shuffle r (\<dd> s a)))"
  unfolding Shuffle_def by (rule ext, coinduction arbitrary: r s) auto

theorem Shuffle_ZeroL[simp]: "Shuffle Zero r = Zero"
  by (coinduction arbitrary: r rule: language_coinduct_upto_Plus) (auto 0 4)

theorem Shuffle_ZeroR[simp]: "Shuffle r Zero = Zero"
  by (coinduction arbitrary: r rule: language_coinduct_upto_Plus) (auto 0 4)

theorem Shuffle_OneL[simp]: "Shuffle One r = r"
  by (coinduction arbitrary: r) simp

theorem Shuffle_OneR[simp]: "Shuffle r One = r"
  by (coinduction arbitrary: r) simp

theorem Shuffle_PlusL[simp]: "Shuffle (Plus r s) t = Plus (Shuffle r t) (Shuffle s t)"
  by (coinduction arbitrary: r s t rule: language_coinduct_upto_Plus)
    (force intro!: Trans[OF Plus[OF Base Base] Refl])

theorem Shuffle_PlusR[simp]: "Shuffle r (Plus s t) = Plus (Shuffle r s) (Shuffle r t)"
  by (coinduction arbitrary: r s t rule: language_coinduct_upto_Plus)
    (force intro!: Trans[OF Plus[OF Base Base] Refl])

theorem Shuffle_assoc[simp]: "Shuffle (Shuffle r s) t = Shuffle r (Shuffle s t)"
  by (coinduction arbitrary: r s t rule: language_coinduct_upto_Plus) fastforce

text {*
  We generalize coinduction up-to @{term Plus} to coinduction up-to all previously defined concepts.
*}

inductive regular_cong where
  Refl[intro]: "x = y \<Longrightarrow> regular_cong R x y"
| Sym[intro]: "regular_cong R x y \<Longrightarrow> regular_cong R y x"
| Trans[intro]: "\<lbrakk>regular_cong R x y; regular_cong R y z\<rbrakk> \<Longrightarrow> regular_cong R x z"
| Base[intro]: "R x y \<Longrightarrow> regular_cong R x y"
| Plus[intro]: "\<lbrakk>regular_cong R x y; regular_cong R x' y'\<rbrakk> \<Longrightarrow>
    regular_cong R (Plus x x') (Plus y y')"
| Times[intro]: "\<lbrakk>regular_cong R x y; regular_cong R x' y'\<rbrakk> \<Longrightarrow>
    regular_cong R (Times x x') (Times y y')"
| Star[intro]: "\<lbrakk>regular_cong R x y\<rbrakk> \<Longrightarrow>
    regular_cong R (Star x) (Star y)"
| Inter[intro]: "\<lbrakk>regular_cong R x y; regular_cong R x' y'\<rbrakk> \<Longrightarrow>
    regular_cong R (Inter x x') (Inter y y')"
| Not[intro]: "\<lbrakk>regular_cong R x y\<rbrakk> \<Longrightarrow>
    regular_cong R (Not x) (Not y)"
| Shuffle[intro]: "\<lbrakk>regular_cong R x y; regular_cong R x' y'\<rbrakk> \<Longrightarrow>
    regular_cong R (Shuffle x x') (Shuffle y y')"

lemma language_coinduct_upto_regular[unfolded rel_fun_def, simplified, case_names Lang, consumes 1]: 
  assumes R: "R L K" and hyp:
    "(\<And>L K. R L K \<Longrightarrow> \<oo> L = \<oo> K \<and> rel_fun op = (regular_cong R) (\<dd> L) (\<dd> K))"
  shows "L = K"
proof (coinduct rule: language.coinduct[of "regular_cong R"])
  fix L K assume "regular_cong R L K"
  then show "\<oo> L = \<oo> K \<and> rel_fun op = (regular_cong R) (\<dd> L) (\<dd> K)" using hyp
    by (induct rule: regular_cong.induct) (auto simp: rel_fun_def Plus Times Shuffle)
qed (intro Base R)

lemma Star_unfoldR: "Star r = Plus One (Times (Star r) r)"
proof (coinduction arbitrary: r rule: language_coinduct_upto_regular)
  case Lang
  { fix a have "Plus (Times (\<dd> r a) (Times (Star r) r)) (\<dd> r a) = 
      Times (\<dd> r a) (Plus One (Times (Star r) r))" by simp
  }
  then show ?case by (auto simp del: Times_PlusR)
qed

lemma Star_Star[simp]: "Star (Star r) = Star r"
  by (subst Star_unfoldL, coinduction arbitrary: r rule: language_coinduct_upto_regular) auto

lemma Times_Star[simp]: "Times (Star r) (Star r) = Star r"
proof (coinduction arbitrary: r rule: language_coinduct_upto_regular)
  case Lang
  have *: "\<And>r s. Plus (Times r s) r = Times r (Plus s One)" by simp
  show ?case by (auto simp del: Times_PlusR Plus_ACI simp: Times_PlusR[symmetric] *)
qed

instantiation language :: (type) "{semiring_1, order}"
begin

lemma Zero_One[simp]: "Zero \<noteq> One"
  by (metis One.simps(1) Zero.simps(1))

definition "zero_language = Zero"
definition "one_language = One"
definition "plus_language = Plus"
definition "times_language = Times"

definition "less_eq_language r s = (Plus r s = s)"
definition "less_language r s = (Plus r s = s \<and> r \<noteq> s)"

lemmas language_defs = zero_language_def one_language_def plus_language_def times_language_def
  less_eq_language_def less_language_def

instance proof intro_classes
  fix x y z :: "'a language" assume "x \<le> y" "y \<le> z"
  then show "x \<le> z" unfolding language_defs by (metis Plus_assoc)
next
  fix x y z :: "'a language"
  show "x + y + z = x + (y + z)" unfolding language_defs by (rule Plus_assoc)
qed (auto simp: language_defs)

end

text {*
  We prove the missing axioms of Kleene Algebras about @{term Star}, as well as monotonicity
  properties and three standard interesting rules: bisimulation, sliding, and denesting.
*}

theorem le_StarL: "Plus One (Times r (Star r)) \<le> Star r"
  by (rule order_eq_refl[OF Star_unfoldL[symmetric]])

theorem le_StarR: "Plus One (Times (Star r) r) \<le> Star r"
  by (rule order_eq_refl[OF Star_unfoldR[symmetric]])

theorem ardenL: "Plus r (Times s x) \<le> x \<Longrightarrow> Times (Star s) r \<le> x"
unfolding language_defs
proof (coinduction arbitrary: r s x rule: language_coinduct_upto_regular)
  case Lang
  hence "\<oo> r \<Longrightarrow> \<oo> x" by (metis Plus.sel(1))
  moreover
  { fix a
    let ?R = "(\<lambda>L K. \<exists>r s.  L = Plus (Times (Star s) r) K \<and> Plus r (Plus (Times s K) K) = K)"
    have "regular_cong ?R (Plus x (Times (Star s) r)) x"
      using Lang[unfolded Plus_assoc] by (auto simp only: Plus_comm)
    hence "regular_cong ?R
      (Plus (Times (\<dd> s a) (Plus x (Times (Star s) r))) (Plus (\<dd> r a) (\<dd> x a)))
      (Plus (\<dd> r a) (Plus (Times (\<dd> s a) x) (\<dd> x a)))"
      by (auto simp del: Times_PlusR)
    also have "(Plus (Times (\<dd> s a) (Plus x (Times (Star s) r))) (Plus (\<dd> r a) (\<dd> x a))) = 
      (Plus (Times (\<dd> s a) (Times (Star s) r)) (Plus (\<dd> r a) (\<dd> x a)))"
      by (subst (3) Lang[symmetric]) auto
    finally have "regular_cong ?R
      (Plus (Times (\<dd> s a) (Times (Star s) r)) (Plus (\<dd> r a) (\<dd> x a)))
      (Plus (\<dd> r a) (Plus (Times (\<dd> s a) x) (\<dd> x a)))" .
  }
  ultimately show ?case by (subst (4) Lang[symmetric]) auto
qed

theorem ardenR: "Plus r (Times x s) \<le> x \<Longrightarrow> Times r (Star s) \<le> x"
unfolding language_defs
proof (coinduction arbitrary: r s x rule: language_coinduct_upto_regular)
  case Lang
  let ?R = "(\<lambda>L K. \<exists>r s. L = Plus (Times r (Star s)) K \<and> Plus r (Plus (Times K s) K) = K)"
  have "\<And>a. \<oo> x \<Longrightarrow> Plus (\<dd> s a) (\<dd> x a) = \<dd> x a"
    by (subst (1 2) Lang[symmetric]) auto
  then have *: "\<And>a. ?R (Plus (Times (\<dd> r a) (Star s)) (\<dd> x a)) (\<dd> x a)"
    by (subst Lang[symmetric]) (auto simp del: Plus_comm)
  moreover
  from Lang have "\<oo> r \<Longrightarrow> \<oo> x" by (metis Plus.sel(1))
  moreover
  { fix a assume "\<oo> x"
    have "regular_cong ?R (Plus (Times (\<dd> s a) (Star s)) (\<dd> x a)) (\<dd> x a)"
    proof (rule Base exI conjI[OF refl])+
      from `\<oo> x` show "Plus (\<dd> s a) (Plus (Times (\<dd> x a) s) (\<dd> x a)) = \<dd> x a"
        by (subst (1 3) Lang[symmetric]) auto
    qed
    from Plus[OF Base[of ?R, OF *[of a]] this] have "regular_cong ?R
      (Plus (Times (\<dd> r a) (Star s)) (Plus (Times (\<dd> s a) (Star s)) (\<dd> x a))) (\<dd> x a)" by auto
  }
  ultimately show ?case by auto
qed

lemma ge_One[simp]: "One \<le> r \<longleftrightarrow> \<oo> r"
  unfolding less_eq_language_def by (metis One.sel(1) Plus.sel(1) Plus_OneL)

lemma Plus_mono[intro]: "\<lbrakk>r1 \<le> s1; r2 \<le> s2\<rbrakk> \<Longrightarrow> Plus r1 r2 \<le> Plus s1 s2"
  unfolding less_eq_language_def by (metis Plus_assoc Plus_comm)

lemma Plus_upper: "\<lbrakk>r1 \<le> s; r2 \<le> s\<rbrakk> \<Longrightarrow> Plus r1 r2 \<le> s"
  by (metis Plus_mono Plus_idem)

lemma le_PlusL: "r \<le> Plus r s"
  by (metis Plus_idem_assoc less_eq_language_def)

lemma le_PlusR: "s \<le> Plus r s"
  by (metis Plus_comm Plus_idem_assoc less_eq_language_def)

lemma Times_mono[intro]: "\<lbrakk>r1 \<le> s1; r2 \<le> s2\<rbrakk> \<Longrightarrow> Times r1 r2 \<le> Times s1 s2"
proof (unfold less_eq_language_def)
  assume s1[symmetric]: "Plus r1 s1 = s1" and s2[symmetric]: "Plus r2 s2 = s2"
  have "Plus (Times r1 r2) (Times s1 s2) =
    Plus (Times r1 r2) (Plus (Times r1 r2) (Plus (Times s1 r2) (Plus (Times r1 s2) (Times s1 s2))))"
    by (subst s1, subst s2) auto
  also have "\<dots> = Plus (Times r1 r2) (Plus (Times s1 r2) (Plus (Times r1 s2) (Times s1 s2)))"
    by (metis Plus_idem Plus_assoc)
  also have "\<dots> = Times s1 s2" by (subst s1, subst s2) auto
  finally show "Plus (Times r1 r2) (Times s1 s2) = Times s1 s2" .
qed

lemma le_TimesL: "\<oo> s \<Longrightarrow> r \<le> Times r s"
  by (metis Plus_OneL Times_OneR Times_mono le_PlusL order_refl)

lemma le_TimesR: "\<oo> r \<Longrightarrow> s \<le> Times r s"
  by (metis Plus_OneR Times_OneL Times_mono le_PlusR order_refl)

lemma le_Star: "s \<le> Star s"
  by (subst Star_unfoldL, subst Star_unfoldL) (auto intro: order_trans[OF le_PlusL le_PlusR])

lemma Star_mono:
  assumes rs: "r \<le> s"
  shows "Star r \<le> Star s"
proof -
  have "Star r = Plus One (Times (Star r) r)" by (rule Star_unfoldR)
  also have "\<dots> \<le> Plus One (Times (Star r) s)" by (blast intro: rs)
  also have "Times (Star r) s \<le> Star s"
  proof (rule ardenL[OF Plus_upper[OF le_Star]])
    have "Times r (Star s) \<le> Times s (Star s)" by (blast intro: rs)
    also have "Times s (Star s) \<le> Plus One (Times s (Star s))" by (rule le_PlusR)
    finally show "Times r (Star s) \<le> Star s" by (subst (2) Star_unfoldL)
  qed
  finally show ?thesis by auto
qed

lemma Inter_mono: "\<lbrakk>r1 \<le> s1; r2 \<le> s2\<rbrakk> \<Longrightarrow> Inter r1 r2 \<le> Inter s1 s2"
unfolding less_eq_language_def proof (coinduction arbitrary: r1 r2 s1 s2)
  case Lang
  then have "\<oo> (Plus r1 s1) = \<oo> s1" "\<oo> (Plus r2 s2) = \<oo> s2"
        "\<forall>a. \<dd> (Plus r1 s1) a = \<dd> s1 a" "\<forall>a. \<dd> (Plus r2 s2) a = \<dd> s2 a" by simp_all
  then show ?case by fastforce
qed

lemma Not_antimono: "r \<le> s \<Longrightarrow> Not s \<le> Not r"
unfolding less_eq_language_def proof (coinduction arbitrary: r s)
  case Lang
  then have "\<oo> (Plus r s) = \<oo> s" "\<forall>a. \<dd> (Plus r s) a = \<dd> s a" by simp_all
  then show ?case by auto
qed

lemma Not_Plus[simp]: "Not (Plus r s) = Inter (Not r) (Not s)"
  by (coinduction arbitrary: r s) auto

lemma Not_Inter[simp]: "Not (Inter r s) = Plus (Not r) (Not s)"
  by (coinduction arbitrary: r s) auto

lemma Inter_assoc[simp]: "Inter (Inter r s) t = Inter r (Inter s t)"
  by (coinduction arbitrary: r s t) auto

lemma Inter_comm: "Inter r s = Inter s r"
  by (coinduction arbitrary: r s) auto

lemma Inter_idem[simp]: "Inter r r = r"
  by (coinduction arbitrary: r) auto

lemma Inter_ZeroL[simp]: "Inter Zero r = Zero"
  by (coinduction arbitrary: r) auto

lemma Inter_ZeroR[simp]: "Inter r Zero = Zero"
  by (coinduction arbitrary: r) auto

lemma Inter_FullL[simp]: "Inter Full r = r"
  by (coinduction arbitrary: r) auto

lemma Inter_FullR[simp]: "Inter r Full = r"
  by (coinduction arbitrary: r) auto

lemma Plus_FullL[simp]: "Plus Full r = Full"
  by (coinduction arbitrary: r) auto

lemma Plus_FullR[simp]: "Plus r Full = Full"
  by (coinduction arbitrary: r) auto

lemma Not_Not[simp]: "Not (Not r) = r"
  by (coinduction arbitrary: r) auto

lemma Not_Zero[simp]: "Not Zero = Full"
  by coinduction simp

lemma Not_Full[simp]: "Not Full = Zero"
  by coinduction simp

lemma bisimulation:
  assumes "Times r s = Times s t"
  shows "Times (Star r) s = Times s (Star t)"
proof (rule antisym[OF ardenL[OF Plus_upper[OF le_TimesL]] ardenR[OF Plus_upper[OF le_TimesR]]])
  have "Times r (Times s (Star t)) = Times s (Times t (Star t))" (is "?L = _")
    by (simp only: assms Times_assoc[symmetric])
  also have "\<dots> \<le> Times s (Star t)" (is "_ \<le> ?R")
    by (rule Times_mono[OF order_refl ord_le_eq_trans[OF le_PlusR Star_unfoldL[symmetric]]])
  finally show "?L \<le> ?R" .
next
  have "Times (Times (Star r) s) t = Times (Times (Star r) r) s" (is "?L = _")
    by (simp only: assms Times_assoc)
  also have "\<dots> \<le> Times (Star r) s" (is "_ \<le> ?R")
    by (rule Times_mono[OF ord_le_eq_trans[OF le_PlusR Star_unfoldR[symmetric]] order_refl])
  finally show "?L \<le> ?R" .
qed simp_all

lemma sliding: "Times (Star (Times r s)) r = Times r (Star (Times s r))"
proof (rule antisym[OF ardenL[OF Plus_upper[OF le_TimesL]] ardenR[OF Plus_upper[OF le_TimesR]]])
  have "Times (Times r s) (Times r (Star (Times s r))) =
    Times r (Times (Times s r) (Star (Times s r)))" (is "?L = _") by simp
  also have "\<dots> \<le> Times r (Star (Times s r))" (is "_ \<le> ?R")
    by (rule Times_mono[OF order_refl ord_le_eq_trans[OF le_PlusR Star_unfoldL[symmetric]]])
  finally show "?L \<le> ?R" .
next
  have "Times (Times (Star (Times r s)) r) (Times s r) =
    Times (Times (Star (Times r s)) (Times r s)) r" (is "?L = _") by simp
  also have "\<dots> \<le> Times (Star (Times r s)) r" (is "_ \<le> ?R")
    by (rule Times_mono[OF ord_le_eq_trans[OF le_PlusR Star_unfoldR[symmetric]] order_refl])
  finally show "?L \<le> ?R" .
qed simp_all

lemma denesting: "Star (Plus r s) = Times (Star r) (Star (Times s (Star r)))"
proof (rule antisym[OF _ ardenR[OF Plus_upper[OF Star_mono[OF le_PlusL]]]])
  have "Star (Plus r s) = Times (Star (Plus r s)) One" by simp
  also have "\<dots> \<le> Times (Star r) (Star (Times s (Star r)))"
  proof (rule ardenL[OF Plus_upper])
    show "Times (Plus r s) (Times (Star r) (Star (Times s (Star r)))) \<le>
      Times (Star r) (Star (Times s (Star r)))" (is "Times _ ?L \<le> ?R")
    proof (subst Times_PlusL, rule Plus_upper)
      show "Times s ?L \<le> ?R"
        by (subst (5) Star_unfoldL, rule order_trans[OF order_trans[OF _ le_PlusR] le_TimesR]) auto
    qed (subst (4) Times_Star[symmetric], auto simp del: Times_Star intro: le_Star)
  qed simp
  finally show "Star (Plus r s) \<le> Times (Star r) (Star (Times s (Star r)))" .
next
  have "Times (Star (Plus r s)) (Times s (Star r)) \<le> Times (Star (Plus r s)) (Star (Plus r s))"
    by (subst (4) Star_unfoldL, rule Times_mono[OF order_refl
      order_trans[OF Times_mono[OF le_PlusR Star_mono[OF le_PlusL]] le_PlusR]])
  also have "\<dots> = Star (Plus r s)" by simp
  finally show "Times (Star (Plus r s)) (Times s (Star r)) \<le> Star (Plus r s)" .
qed

text {*
It is useful to lift binary operators @{term Plus} and @{term Times}
to $n$-ary operators (that take a list as input).
*}

definition PLUS :: "'a language list \<Rightarrow> 'a language" where
  "PLUS xs \<equiv> foldr Plus xs Zero"

lemma \<oo>_foldr_Plus: "\<oo> (foldr Plus xs s) = (\<exists>x\<in>set (s # xs). \<oo> x)"
  by (induct xs arbitrary: s) auto

lemma \<dd>_foldr_Plus: "\<dd> (foldr Plus xs s) a = foldr Plus (map (\<lambda>r. \<dd> r a) xs) (\<dd> s a)"
  by (induct xs arbitrary: s) simp_all

lemma \<oo>_PLUS[simp]: "\<oo> (PLUS xs) = (\<exists>x\<in>set xs. \<oo> x)"
  unfolding PLUS_def \<oo>_foldr_Plus by simp

lemma \<dd>_PLUS[simp]: "\<dd> (PLUS xs) a = PLUS (map (\<lambda>r. \<dd> r a) xs)"
  unfolding PLUS_def \<dd>_foldr_Plus by simp

definition TIMES :: "'a language list \<Rightarrow> 'a language" where
  "TIMES xs \<equiv> foldr Times xs One"

lemma \<oo>_foldr_Times: "\<oo> (foldr Times xs s) = (\<forall>x\<in>set (s # xs). \<oo> x)"
  by (induct xs) (auto simp: PLUS_def)

primrec tails where
  "tails [] = [[]]"
| "tails (x # xs) = (x # xs) # tails xs"

lemma tails_snoc[simp]: "tails (xs @ [x]) = map (\<lambda>ys. ys @ [x]) (tails xs) @ [[]]"
  by (induct xs) auto

lemma length_tails[simp]: "length (tails xs) = Suc (length xs)"
  by (induct xs) auto

lemma \<dd>_foldr_Times: "\<dd> (foldr Times xs s) a =
  (let n = length (takeWhile \<oo> xs)
  in PLUS (map (\<lambda>zs. TIMES (\<dd> (hd zs) a # tl zs)) (take (Suc n) (tails (xs @ [s])))))"
  by (induct xs) (auto simp: TIMES_def PLUS_def Let_def foldr_map o_def)

lemma \<oo>_TIMES[simp]: "\<oo> (TIMES xs) = (\<forall>x\<in>set xs. \<oo> x)"
  unfolding TIMES_def \<oo>_foldr_Times by simp

lemma TIMES_snoc_One[simp]: "TIMES (xs @ [One]) = TIMES xs"
  by (induct xs) (auto simp: TIMES_def)

lemma \<dd>_TIMES[simp]: "\<dd> (TIMES xs) a = (let n = length (takeWhile \<oo> xs)
  in PLUS (map (\<lambda>zs. TIMES (\<dd> (hd zs) a # tl zs)) (take (Suc n) (tails (xs @ [One])))))"
  unfolding TIMES_def \<dd>_foldr_Times by simp

section {* Context Free Languages *}

text {*
A context-free grammar consists of a list of productions for every nonterminal
and an initial nonterminal. The productions are required to be in weak Greibach
normal form, i.e. each right hand side of a production must either be empty or
start with a terminal.
*}

locale cfg =
fixes init :: "'n::enum"
and   prod :: "'n \<Rightarrow> ('t + 'n) list list"
assumes weakGreibach: "\<forall>N. \<forall>rhs \<in> set (prod N). case rhs of (Inr N # _) \<Rightarrow> False | _ \<Rightarrow> True"

context
fixes init :: "'n::enum"
and   prod :: "'n \<Rightarrow> ('t + 'n) list list"
begin

private abbreviation "\<oo>\<^sub>n N \<equiv> ([] \<in> set (prod N))"
private fun \<oo>\<^sub>r where
  "\<oo>\<^sub>r [] = True"
| "\<oo>\<^sub>r (Inl _ # _) = False"
| "\<oo>\<^sub>r (Inr N # xs) = (\<oo>\<^sub>n N \<and> \<oo>\<^sub>r xs)"
private abbreviation "\<oo>\<^sub>P P \<equiv> fold (op \<or>) (map \<oo>\<^sub>r P) False"

private abbreviation "\<dd>\<^sub>n N a \<equiv>
  List.map_filter (\<lambda>xs.
    case xs of Inl b # xs \<Rightarrow> if a = b then Some xs else None | _ \<Rightarrow> None) (prod N)"
private fun \<dd>\<^sub>r where
  "\<dd>\<^sub>r [] a = []"
| "\<dd>\<^sub>r (Inl b # xs) a = (if a = b then [xs] else [])"
| "\<dd>\<^sub>r (Inr N # xs) a = map (\<lambda>ys. ys @ xs) (\<dd>\<^sub>n N a) @ (if \<oo>\<^sub>n N then \<dd>\<^sub>r xs a else [])"
private abbreviation "\<dd>\<^sub>P P a \<equiv> fold (op @) (map (\<lambda>r. \<dd>\<^sub>r r a) P) []"

primcorec subst :: "('t + 'n) list list \<Rightarrow> 't language" where
  "subst P = Lang (\<oo>\<^sub>P P) (\<lambda>x. subst (\<dd>\<^sub>P P x))"

end

abbreviation (in cfg) lang where
  "lang \<equiv> subst prod (prod init)"


section {* Word-theoretic Semantics of Languages *}

text {*
We show our @{type language} codatatype being isomorphic to the standard
language representation as a set of lists.
*}

primrec in_language :: "'a language \<Rightarrow> 'a list \<Rightarrow> bool" where
  "in_language L [] = \<oo> L"
| "in_language L (x # xs) = in_language (\<dd> L x) xs"

primcorec to_language :: "'a list set \<Rightarrow> 'a language" where
  "\<oo> (to_language L) = ([] \<in> L)"
| "\<dd> (to_language L) = (\<lambda>a. to_language {w. a # w \<in> L})"

lemma in_language_to_language[simp]: "Collect (in_language (to_language L)) = L"
proof (rule set_eqI, unfold mem_Collect_eq)
  fix w show "in_language (to_language L) w = (w \<in> L)" by (induct w arbitrary: L) auto
qed

lemma to_language_in_language[simp]: "to_language (Collect (in_language L)) = L"
  by (coinduction arbitrary: L) auto

lemma in_language_bij: "bij (Collect o in_language)"
proof (rule bijI', unfold o_apply, safe)
  fix L R :: "'a language" assume "Collect (in_language L) = Collect (in_language R)"
  then show "L = R" unfolding set_eq_iff mem_Collect_eq
    by (coinduction arbitrary: L R) (metis in_language.simps)
next
  fix L :: "'a list set"
  have "L = Collect (in_language (to_language L))" by simp
  then show "\<exists>K. L = Collect (in_language K)" by blast
qed

lemma to_language_bij: "bij to_language"
  by (rule o_bij[of "Collect o in_language"]) (simp_all add: fun_eq_iff)

(*<*)
hide_const (open) TimesLR Times_Plus StarLR subst

end
(*>*)
