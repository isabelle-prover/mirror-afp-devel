(*  Title:       A library for coinductive lists
    Author:      Andreas Lochbihler
                 lfilter by Larry Paulson
    Maintainer:  Andreas Lochbihler
*)
theory Coinductive_List_Lib imports
  Coinductive_List
  Coinductive_Nat
begin

section {* A library of functions on lazy lists *}

subsection {* Library function definitions *}

definition llist_corec2 :: "'a \<Rightarrow> ('a \<Rightarrow> (('b \<times> 'a) option + 'b llist)) \<Rightarrow> 'b llist"
where
  "llist_corec2 a f = 
   llist_corec (Inl a)
     (\<lambda>a. case a of Inl a' \<Rightarrow> case f a' of Inl opt \<Rightarrow> (case opt of None \<Rightarrow> None 
                                                       | Some (b, a'') \<Rightarrow> Some (b, Inl a''))
                                          | Inr xs \<Rightarrow> (case xs of LNil \<Rightarrow> None |
                                                           LCons b xs' \<Rightarrow> Some (b, Inr xs'))
                  | Inr xs \<Rightarrow> (case xs of LNil \<Rightarrow> None 
                                | LCons a xs' \<Rightarrow> Some (a, Inr xs')))"

inductive lfinite :: "'a llist \<Rightarrow> bool"
where
  lfinite_LNil:  "lfinite LNil"
| lfinite_LConsI: "lfinite xs \<Longrightarrow> lfinite (LCons x xs)"

primrec llist_of :: "'a list \<Rightarrow> 'a llist"
where
  "llist_of [] = LNil"
| "llist_of (x#xs) = LCons x (llist_of xs)"

definition list_of :: "'a llist \<Rightarrow> 'a list"
where [code del]: "list_of xs = (if lfinite xs then inv llist_of xs else undefined)"

definition llength :: "'a llist \<Rightarrow> inat"
where [code del]:
  "llength xs = inat_corec xs (\<lambda>xs. case xs of LNil \<Rightarrow> None
                                      | LCons x xs' \<Rightarrow> Some xs')"

definition ltake :: "inat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where [code del]:
  "ltake n xs = 
   llist_corec (n, xs) (\<lambda>(n, xs). case n of 0 \<Rightarrow> None
                                    | iSuc n' \<Rightarrow> (case xs of LNil \<Rightarrow> None
                                                    | LCons x xs' \<Rightarrow> Some (x, (n', xs'))))"

primrec ldropn :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "ldropn 0 xs = xs"
| "ldropn (Suc n) xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldropn n xs')"

declare ldropn.simps(2) [simp del]

primrec ldrop :: "inat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "ldrop (Fin n) xs = ldropn n xs"
| "ldrop \<infinity> xs = LNil"

primrec lnth :: "'a llist \<Rightarrow> nat \<Rightarrow> 'a"
where 
  "lnth xs 0 = (case xs of LNil \<Rightarrow> undefined (0 :: nat) | LCons x xs' \<Rightarrow> x)"
| "lnth xs (Suc n) = (case xs of LNil \<Rightarrow> undefined (Suc n) | LCons x xs' \<Rightarrow> lnth xs' n)"

declare lnth.simps [simp del]

definition lzip :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a \<times> 'b) llist"
where [code del]:
  "lzip xs ys =
   llist_corec (xs, ys)
      (\<lambda>(xs, ys). case xs of LNil \<Rightarrow> None 
                     | LCons x xs \<Rightarrow> case ys of LNil \<Rightarrow> None
                                        | LCons y ys \<Rightarrow> Some ((x, y), (xs, ys)))"

definition lset :: "'a llist \<Rightarrow> 'a set"
where [code del]: "lset xs = lnth xs ` {n. Fin n < llength xs}"

definition llist_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'b llist \<Rightarrow> bool"
where [code del]:
  "llist_all2 P xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>(x, y) \<in> lset (lzip xs ys). P x y)"

definition lhd :: "'a llist \<Rightarrow> 'a"
where [code del]: "lhd xs = (case xs of LNil \<Rightarrow> undefined | LCons x xs' \<Rightarrow> x)"

definition ltl :: "'a llist \<Rightarrow> 'a llist"
where [code del]: "ltl xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> xs')"

definition inf_llist :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a llist"
where [code del]: "inf_llist f = llist_corec f (\<lambda>f. Some (f 0, \<lambda>n. f (Suc n)))"

definition lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where [code del]: "lprefix xs ys \<equiv> \<exists>zs. lappend xs zs = ys"

definition lstrict_prefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where [code del]: "lstrict_prefix xs ys \<equiv> lprefix xs ys \<and> xs \<noteq> ys"

coinductive llexord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  llexord_LCons_eq: "llexord r xs ys \<Longrightarrow> llexord r (LCons x xs) (LCons x ys)"
| llexord_LCons_less: "r x y \<Longrightarrow> llexord r (LCons x xs) (LCons y ys)"
| llexord_LNil [simp, intro!]: "llexord r LNil ys"

text {* 
  The "filter" functional for coinductive lists --
  defined by a combination of induction and coinduction
*}

inductive_set findRel :: "('a => bool) => ('a llist * 'a llist) set"
  for p :: "'a => bool"
  where
    found:  "p x ==> (LCons x l, LCons x l) \<in> findRel p"
  | seek:   "[| ~p x;  (l,l') \<in> findRel p |] ==> (LCons x l, l') \<in> findRel p"

declare findRel.intros [intro]

definition find :: "['a => bool, 'a llist] => 'a llist" 
where
  "find p l = (SOME l'. (l,l'): findRel p | (l' = LNil & l ~: Domain(findRel p)))"

definition lfilter :: "['a => bool, 'a llist] => 'a llist" where
  "lfilter p l = llist_corec l (%l. case find p l of LNil => None
                                              | LCons y z => Some(y,z))"

definition lconcat :: "'a llist llist \<Rightarrow> 'a llist"
where [code del]:
  "lconcat xs =
   llist_corec (lfilter (\<lambda>xs. xs \<noteq> LNil) xs)
     (\<lambda>xs. case xs of LNil \<Rightarrow> None
             | LCons x xs' \<Rightarrow> Some (lhd x, if ltl x = LNil then xs' else LCons (ltl x) xs'))"

definition lsublist :: "'a llist \<Rightarrow> nat set \<Rightarrow> 'a llist"
where "lsublist xs A = lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (iterates Suc 0)))"

subsection {* Auxiliary lemmata *}

lemma funpow_Suc_conv [simp]: "(Suc ^^ n) m = m + n"
by(induct n arbitrary: m) simp_all

lemma min_iSuc_iSuc [simp]: "min (iSuc n) (iSuc m) = iSuc (min n m)"
by(simp add: min_def)

lemma inat_le_plus_same: "x \<le> (x :: inat) + y" "x \<le> y + x"
by(auto simp add: less_eq_inat_def plus_inat_def split: inat.split)

lemma llist_split_asm:
  "P (llist_case f g xs) =
  (\<not> (xs = LNil \<and> \<not> P f \<or> (\<exists>x xs'. xs = LCons x xs' \<and> \<not> P (g x xs'))))"
by(cases xs) simp_all

lemma llist_split:
  "P (llist_case f g xs) =
  ((xs = LNil \<longrightarrow> P f) \<and> (\<forall>x xs'. xs = LCons x xs' \<longrightarrow> P (g x xs')))"
by(cases xs) simp_all

lemmas llist_splits = llist_split llist_split_asm

lemma neq_LNil_conv: "xs \<noteq> LNil \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs')"
by(cases xs) auto

lemma lappend_eq_LNil_conv [simp]: 
  "lappend xs ys = LNil \<longleftrightarrow> xs = LNil \<and> ys = LNil"
by(cases xs, simp_all)

lemma lappend_snocL1_conv_LCons2: 
  "lappend (lappend xs (LCons y LNil)) ys = lappend xs (LCons y ys)"
by(simp add: lappend_assoc)

lemma lmap_eq_LNil_conv [simp]: "lmap f xs = LNil \<longleftrightarrow> xs = LNil"
by(cases xs) simp_all

lemma lmap_eq_LCons_conv:
  "lmap f xs = LCons y ys \<longleftrightarrow> 
  (\<exists>x xs'. xs = LCons x xs' \<and> y = f x \<and> ys = lmap f xs')"
by(cases xs)(auto)

lemma lmap_eq_LCons:
  "lmap f l = LCons x l'
  \<Longrightarrow> \<exists>y l''. x = f y \<and> l' = lmap f l'' \<and> l = LCons y l''"
unfolding lmap_eq_LCons_conv by auto

lemma iterates_neq_LNil [simp]: "iterates f x \<noteq> LNil"
by(subst iterates) simp

subsection {* Corecursion with termination: @{term "llist_corec2"} *}

lemma llist_corec2 [nitpick_simp]:
  "llist_corec2 a f = 
  (case f a of Inl opt \<Rightarrow> (case opt of None \<Rightarrow> LNil
                             | Some (b, a') \<Rightarrow> LCons b (llist_corec2 a' f))
             | Inr xs \<Rightarrow> xs)"
unfolding llist_corec2_def
apply(subst llist_corec)
 apply(auto split: sum.split option.split llist_split_asm)
apply(rule llist_fun_equalityI)
 apply(simp_all add: llist_corec)
done

subsection {* The subset of finite lazy lists @{term "lfinite"} *}

declare lfinite_LNil [iff]

lemma lfinite_LCons [simp]: "lfinite (LCons x xs) = lfinite xs"
by(auto elim: lfinite.cases intro: lfinite_LConsI)

lemma lfinite_code [code]:
  "lfinite LNil = True"
  "lfinite (LCons x xs) = lfinite xs"
by simp_all

lemma lfinite_lappend [simp]:
  "lfinite (lappend xs ys) \<longleftrightarrow> lfinite xs \<and> lfinite ys"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
  proof(induct zs\<equiv>"lappend xs ys" arbitrary: xs ys)
    case lfinite_LNil[symmetric]
    thus ?case by simp
  next
    case (lfinite_LConsI zs z)
    thus ?case by(cases xs)(cases ys, simp_all)
  qed
next
  assume ?rhs (is "?xs \<and> ?ys")
  then obtain ?xs ?ys ..
  thus ?lhs by induct simp_all
qed

lemma lappend_inf: "\<not> lfinite xs \<Longrightarrow> lappend xs ys = xs"
proof -
  assume "\<not> lfinite xs"
  hence "(lappend xs ys, xs) \<in> {(lappend xs ys, xs)| xs ys. \<not> lfinite xs}"
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where q: "q = (lappend xs ys, xs)"
      and xs: "\<not> lfinite xs" by blast
    from xs obtain x xs' where xs': "xs = LCons x xs'" "\<not> lfinite xs'"
      by(cases xs) auto
    with q have ?EqLCons by auto
    thus ?case ..
  qed
qed

lemma lfinite_lmap [simp]:
  "lfinite (lmap f xs) = lfinite xs"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
  proof(induct zs\<equiv>"lmap f xs" arbitrary: xs)
    case lfinite_LNil[symmetric]
    thus ?case by simp
  next
    case (lfinite_LConsI zs z)
    from `LCons z zs = lmap f xs`[symmetric]
    obtain x xs' where "xs = LCons x xs'" "z = f x" "zs = lmap f xs'"
      unfolding lmap_eq_LCons_conv by blast
    moreover from `zs = lmap f xs'` have "lfinite xs'"
      by(rule lfinite_LConsI)
    ultimately show ?case by simp
  qed
next
  assume ?rhs thus ?lhs
    by(induct) simp_all
qed

lemma lfinite_iterates [iff]: "\<not> lfinite (iterates f x)"
proof
  assume "lfinite (iterates f x)"
  thus False
  proof(induct zs\<equiv>"iterates f x" arbitrary: x)
    case lfinite_LNil[symmetric]
    thus ?case by(simp)
  next
    case (lfinite_LConsI zs z)
    have "iterates f x = LCons x (iterates f (f x))" by(rule iterates)
    with `LCons z zs = iterates f x` have "zs = iterates f (f x)" by simp
    thus False by(rule lfinite_LConsI)
  qed
qed

subsection {* Converting ordinary lists to lazy lists: @{term "llist_of"} *}

lemma lfinite_llist_of [simp]: "lfinite (llist_of xs)"
by(induct xs) auto

lemma lfinite_eq_range_llist_of: "lfinite xs \<longleftrightarrow> xs \<in> range llist_of"
proof
  assume "lfinite xs"
  thus "xs \<in> range llist_of"
    by(induct rule: lfinite.induct)(auto intro: llist_of.simps[symmetric])
next
  assume "xs \<in> range llist_of"
  thus "lfinite xs" by(auto intro: lfinite_llist_of)
qed

lemma lappend_llist_of_llist_of [simp]:
  "lappend (llist_of xs) (llist_of ys) = llist_of (xs @ ys)"
by(induct xs) simp_all

lemma lappend_llist_of_LCons: 
  "lappend (llist_of xs) (LCons y ys) = lappend (llist_of (xs @ [y])) ys"
by(induct xs) simp_all

lemma lmap_llist_of [simp]:
  "lmap f (llist_of xs) = llist_of (map f xs)"
by(induct xs) simp_all

lemma llist_of_inj [simp]: "llist_of xs = llist_of ys \<longleftrightarrow> xs = ys"
proof
  assume "llist_of xs = llist_of ys"
  thus "xs = ys"
  proof(induct xs arbitrary: ys)
    case Nil thus ?case by(cases ys) auto
  next
    case Cons thus ?case by(cases ys) auto
  qed
qed simp

subsection {* Converting finite lazy lists to ordinary lists: @{term "list_of"} *}

lemma list_of_llist_of [simp]: "list_of (llist_of xs) = xs"
by(fastsimp simp add: list_of_def intro: inv_f_f inj_onI)

lemma llist_of_list_of: "lfinite xs \<Longrightarrow> llist_of (list_of xs) = xs"
unfolding lfinite_eq_range_llist_of by auto

lemma list_of_LNil [simp, code]: "list_of LNil = []"
using list_of_llist_of[of "[]"] by simp

lemma list_of_LCons : "lfinite xs \<Longrightarrow> list_of (LCons x xs) = x # list_of xs"
proof(induct arbitrary: x rule: lfinite.induct)
  case lfinite_LNil
  show ?case using list_of_llist_of[of "[x]"] by simp
next
  case (lfinite_LConsI xs' x')
  from `list_of (LCons x' xs') = x' # list_of xs'` show ?case
    using list_of_llist_of[of "x # x' # list_of xs'"]
      llist_of_list_of[OF `lfinite xs'`] by simp
qed

lemma list_of_LCons_code [code]:
  "list_of (LCons x xs) = (if lfinite xs then x # list_of xs else undefined)"
by(auto simp add: list_of_LCons)(auto simp add: list_of_def)

subsection {* The length of a lazy list: @{term "llength"} *}

lemma [simp, code]:
  shows llength_LNil: "llength LNil = 0"
  and llength_LCons: "llength (LCons x xs) = iSuc (llength xs)"
by(simp_all add: llength_def inat_corec)

lemma llength_eq_0 [simp]: "llength xs = 0 \<longleftrightarrow> xs = LNil"
by(cases xs) simp_all

lemma llength_lmap [simp]: "llength (lmap f xs) = llength xs"
proof -
  have "(llength (lmap f xs), llength xs) \<in> 
        {(llength (lmap f xs), llength xs)|xs. True}" by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain xs where "m = llength (lmap f xs)" "n = llength xs" by auto
    thus ?case by(cases xs) auto
  qed
qed

lemma llength_lappend [simp]: "llength (lappend xs ys) = llength xs + llength ys"
proof -
  have "(llength (lappend xs ys), llength xs + llength ys) \<in>
        {(llength (lappend xs ys), llength xs + llength ys)|xs. True}" by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain xs
      where xs: "m = llength (lappend xs ys)" "n = llength xs + llength ys" by auto
    thus ?case
    proof(cases xs)
      case LNil
      with xs show ?thesis by(cases ys)(simp_all)
    next
      case (LCons x xs')
      with xs show ?thesis by(auto simp add: iSuc_plus)
    qed
  qed
qed

lemma llength_iterates [simp]: "llength (iterates f x) = Infty"
proof -
  def Infty' \<equiv> Infty
  hence "(llength (iterates f x), Infty) \<in>
         {(llength (iterates f x), Infty')|x. True}" by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain x where m: "m = llength (iterates f x)" and n: "n = Infty"
      unfolding Infty'_def by blast
    have "iterates f x = LCons x (iterates f (f x))" by(rule iterates)
    with m have "m = iSuc (llength (iterates f (f x)))" by simp
    moreover from n have "n = iSuc \<infinity>" by(simp add: iSuc_def)
    ultimately have ?iSuc unfolding Infty'_def using m by blast
    thus ?case ..
  qed
qed

lemma llength_llist_of [simp]:
  "llength (llist_of xs) = Fin (length xs)"
by(induct xs)(simp_all add: zero_inat_def iSuc_def)

lemma length_list_of:
  "lfinite xs \<Longrightarrow> Fin (length (list_of xs)) = llength xs"
apply(rule sym)
by(induct rule: lfinite.induct)(auto simp add: iSuc_Fin list_of_LCons zero_inat_def)

lemma llength_eq_Fin_lfiniteD: "llength xs = Fin n \<Longrightarrow> lfinite xs"
proof(induct n arbitrary: xs)
  case 0[folded zero_inat_def]
  thus ?case by simp
next
  case (Suc n)
  note len = `llength xs = Fin (Suc n)`
  then obtain x xs' where "xs = LCons x xs'"
    by(cases xs)(auto simp add: zero_inat_def)
  moreover with len have "llength xs' = Fin n"
    by(simp add: iSuc_def split: inat.split_asm)
  hence "lfinite xs'" by(rule Suc)
  ultimately show ?case by simp
qed

lemma lfinite_llength_Fin:
  assumes "lfinite xs"
  shows "\<exists>n. llength xs = Fin n"
using assms
by induct(auto simp add: iSuc_def zero_inat_def)

lemma lfinite_conv_llength_Fin:
  "lfinite xs \<longleftrightarrow> (\<exists>n. llength xs = Fin n)"
by(blast dest: llength_eq_Fin_lfiniteD lfinite_llength_Fin)

lemma not_lfinite_llength:
  fixes xs :: "'a llist"
  assumes nfin: "\<not> lfinite xs"
  shows "llength xs = Infty"
proof -
  from nfin have "(llength xs, Infty) \<in>
                 {(llength xs, Infty)|xs :: 'a llist. \<not> lfinite xs}" by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain xs :: "'a llist"
      where "m = llength xs" "n = Infty" "\<not> lfinite xs" by blast
    hence ?iSuc by(cases xs)(auto intro: sym iSuc_Infty)
    thus ?case ..
  qed
qed

subsection {* Taking and dropping from lazy lists: @{term "ltake"} and @{term "ldrop"} *}

lemma ltake_LNil [simp, code]: "ltake n LNil = LNil"
by(simp add: ltake_def llist_corec split: inat_cosplit)

lemma ltake_0 [simp]: "ltake 0 xs = LNil"
by(simp add: ltake_def llist_corec)

lemma ltake_iSuc_LCons [simp]: 
  "ltake (iSuc n) (LCons x xs) = LCons x (ltake n xs)"
by(simp add: ltake_def llist_corec)

lemma ltake_iSuc:
  "ltake (iSuc n) xs =
  (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> LCons x (ltake n xs'))"
by(cases xs) simp_all

lemma ltake_LCons [code]:
  "ltake n (LCons x xs) =
  (case n of 0 \<Rightarrow> LNil | iSuc n' \<Rightarrow> LCons x (ltake n' xs))"
by(cases n rule: inat_coexhaust) simp_all

lemma llength_ltake [simp]:
  fixes xs :: "'a llist"
  shows "llength (ltake n xs) = min n (llength xs)"
proof -
  have "(llength (ltake n xs), min n (llength xs)) \<in> 
       {(llength (ltake n xs), min n (llength xs))|n (xs :: 'a llist). True}" by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m m')
    then obtain xs :: "'a llist" and n where m: "m = llength (ltake n xs)"
      and m': "m' = min n (llength xs)" by blast
    show ?case
    proof(cases xs)
      case LNil with m m' have ?zero by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with m m' show ?thesis by(cases n rule: inat_coexhaust) auto
    qed
  qed
qed

lemma ltake_lmap [simp]: "ltake n (lmap f xs) = lmap f (ltake n xs)"
proof -
  have "(ltake n (lmap f xs), lmap f (ltake n xs)) \<in>
        {(ltake n (lmap f xs), lmap f (ltake n xs))|n xs. True}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain n xs
      where q: "q = (ltake n (lmap f xs), lmap f (ltake n xs))" by blast
    show ?case
    proof(cases xs)
      case LNil with q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with q show ?thesis by(cases n rule: inat_coexhaust) auto
    qed
  qed
qed

lemma ltake_ltake [simp]: "ltake n (ltake m xs) = ltake (min n m) xs"
proof -
  have "(ltake n (ltake m xs), ltake (min n m) xs) \<in>
        {(ltake n (ltake m xs), ltake (min n m) xs)|xs m n. True}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain m n xs
      where q: "q = (ltake n (ltake m xs), ltake (min n m) xs)" by blast
    show ?case
    proof(cases xs)
      case LNil with q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with q show ?thesis
	by(cases n rule: inat_coexhaust)
          (simp, cases m rule: inat_coexhaust, auto simp add: min_def)
    qed
  qed
qed

lemma ltake_all: 
  assumes len: "llength xs \<le> m"
  shows "ltake m xs = xs"
proof -
  from len have "(ltake m xs, xs) \<in> {(ltake m xs, xs)|m xs. llength xs \<le> m}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain m xs where q: "q = (ltake m xs, xs)"
      and len: "llength xs \<le> m" by blast
    show ?case
    proof(cases xs)
      case LNil with q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with len obtain m' where "m = iSuc m'" "llength xs' \<le> m'"
	by(cases m rule: inat_coexhaust) auto
      with LCons q have ?EqLCons by auto
      thus ?thesis ..
    qed
  qed
qed

lemma ltake_llist_of [simp]:
  "ltake (Fin n) (llist_of xs) = llist_of (take n xs)"
proof(induct n arbitrary: xs)
  case 0
  thus ?case unfolding zero_inat_def[symmetric]
    by(cases xs) simp_all
next
  case (Suc n)
  thus ?case unfolding iSuc_Fin[symmetric]
    by(cases xs) simp_all
qed


lemma lfinite_ltake [simp]:
  "lfinite (ltake n xs) \<longleftrightarrow> lfinite xs \<or> n < Infty"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
  proof(induct ys\<equiv>"ltake n xs" arbitrary: n xs)
    case lfinite_LNil
    thus ?case by(cases xs)(auto simp add: ltake_all)
  next
    case (lfinite_LConsI ys y)
    from `LCons y ys = ltake n xs` obtain n' x xs'
      where n: "n = iSuc n'" and xs: "xs = LCons x xs'"
      and ys: "ys = ltake n' xs'"
      by(cases xs, simp)(cases n rule: inat_coexhaust, auto)
    from ys have "lfinite xs' \<or> n' < \<infinity>" by(rule lfinite_LConsI)
    with n xs show ?case by(auto simp add: iSuc_def split: inat.split_asm)
  qed
next
  assume ?rhs (is "?xs \<or> ?n")
  thus ?lhs
  proof
    assume ?xs thus ?thesis
    proof(induct xs arbitrary: n)
      case (lfinite_LConsI xs x)
      thus ?case by(cases n rule: inat_coexhaust) auto
    qed simp
  next
    assume ?n
    then obtain n' where "n = Fin n'" by(cases n) auto
    moreover have "lfinite (ltake (Fin n') xs)"
      by(induct n' arbitrary: xs)
        (auto simp add: zero_inat_def[symmetric] iSuc_Fin[symmetric] ltake_iSuc
              split: llist_split)
    ultimately show ?thesis by simp
  qed
qed

lemma ltake_lappend1: 
  assumes "n \<le> llength xs"
  shows "ltake n (lappend xs ys) = ltake n xs"
proof -
  def zs \<equiv> "ltake n (lappend xs ys)"
  def us \<equiv> "ltake n xs"
  from zs_def us_def assms
  have "(zs, us) \<in> {(ltake n (lappend xs ys), ltake n xs)|xs n. n \<le> llength xs}" by auto
  thus "zs = us"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs n where q: "q = (ltake n (lappend xs ys), ltake n xs)"
      and n: "n \<le> llength xs" by auto
    show ?case
    proof(cases xs)
      case LNil with n show ?thesis unfolding q by simp
    next
      case (LCons x xs')
      with n show ?thesis unfolding q 
        by(cases n rule: inat_coexhaust) auto
    qed
  qed
qed

lemma take_list_of:
  assumes "lfinite xs"
  shows "take n (list_of xs) = list_of (ltake (Fin n) xs)"
using assms
by(induct arbitrary: n)
  (simp_all add: list_of_LCons take_Cons zero_inat_def[symmetric] iSuc_Fin[symmetric] 
            split: nat.split)

lemma ldropn_LNil [simp]: "ldropn n LNil = LNil"
by(cases n)(simp_all add: ldropn.simps)

lemma ldropn_LCons: 
  "ldropn n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | Suc n' \<Rightarrow> ldropn n' xs)"
by(cases n)(simp_all add: ldropn.simps)

lemma ldrop_LNil [simp]: "ldrop n LNil = LNil"
by(cases n)(simp_all add: ldropn.simps)

lemma ldropn_Suc_LCons [simp]: "ldropn (Suc n) (LCons x xs) = ldropn n xs"
by(simp add: ldropn_LCons)

lemma ldrop_0 [simp]: "ldrop 0 xs = xs"
by(simp add: zero_inat_def)

lemma ldrop_iSuc_LCons [simp]: "ldrop (iSuc n) (LCons x xs) = ldrop n xs"
by(simp add: iSuc_def ldropn.simps split: inat.split)

lemma ldrop_iSuc: 
  "ldrop (iSuc n) xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldrop n xs')"
by(cases xs) simp_all

lemma ldrop_LCons:
  "ldrop n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | iSuc n' \<Rightarrow> ldrop n' xs)"
by(cases n rule: inat_coexhaust) simp_all

lemma lfinite_ldropn [simp]: "lfinite (ldropn n xs) = lfinite xs"
by(induct n arbitrary: xs)(simp_all add: ldropn.simps split: llist_split)

lemma lfinite_ldrop [simp]:
  "lfinite (ldrop n xs) \<longleftrightarrow> lfinite xs \<or> n = Infty"
by(cases n) simp_all

lemma lappend_ltake_ldrop:
  "lappend (ltake n xs) (ldrop n xs) = xs"
proof -
  have "(lappend (ltake n xs) (ldrop n xs), xs) \<in>
        {(lappend (ltake n xs) (ldrop n xs), xs)|n xs. True}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain n xs
      where q: "q = (lappend (ltake n xs) (ldrop n xs), xs)" by blast
    show ?case
    proof(cases xs)
      case LNil with q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with q have ?EqLCons by(cases n rule: inat_coexhaust) auto
      thus ?thesis ..
    qed
  qed
qed

lemma ltake_is_lprefix [simp, intro]:
  "lprefix (ltake n xs) xs"
unfolding lprefix_def
by(rule exI)(rule lappend_ltake_ldrop)

lemma ldropn_all:
  "llength xs \<le> Fin m \<Longrightarrow> ldropn m xs = LNil"
proof(induct m arbitrary: xs)
  case (Suc m) thus ?case
    by(cases xs)(simp_all add: iSuc_Fin[symmetric])
qed(simp add: zero_inat_def[symmetric])

lemma ldrop_all:
  "llength xs \<le> m \<Longrightarrow> ldrop m xs = LNil"
by(cases m)(simp_all add: ldropn_all)

lemma ldropn_lmap [simp]: "ldropn n (lmap f xs) = lmap f (ldropn n xs)"
by(induct n arbitrary: xs)(simp_all add: ldropn.simps split: llist_split)

lemma ldrop_lmap [simp]: "ldrop n (lmap f xs) = lmap f (ldrop n xs)"
by(cases n)(simp_all)

lemma ldropn_ldropn [simp]: 
  "ldropn n (ldropn m xs) = ldropn (n + m) xs"
by(induct m arbitrary: xs)(auto simp add: ldropn.simps split: llist_split)

lemma ldrop_ldrop [simp]: 
  "ldrop n (ldrop m xs) = ldrop (n + m) xs"
by(cases n,cases m) simp_all

lemma ldropn_eq_LNil: "(ldropn n xs = LNil) = (llength xs \<le> Fin n)"
proof(induct n arbitrary: xs)
  case 0 thus ?case 
    by(cases xs)(simp_all add: iSuc_def split: inat.split)
next
  case Suc thus ?case
    by(cases xs)(simp_all add: iSuc_def split: inat.split)
qed

lemma ldrop_eq_LNil: "ldrop n xs = LNil \<longleftrightarrow> llength xs \<le> n"
by(cases n)(simp_all add: ldropn_eq_LNil)

lemma Fin_llength_ldropn:
  "Fin n \<le> llength xs \<Longrightarrow> Fin (n - m) \<le> llength (ldropn m xs)"
proof(induct m arbitrary: xs n)
  case 0 thus ?case by simp
next
  case (Suc m)
  note IH = `\<And>n xs. Fin n \<le> llength xs \<Longrightarrow> Fin (n - m) \<le> llength (ldropn m xs)`
  show ?case
  proof(cases xs)
    case LNil with `Fin n \<le> llength xs`
    show ?thesis by(simp add: zero_inat_def)
  next
    case (LCons x xs')
    show ?thesis
    proof(cases n)
      case 0
      thus ?thesis by(simp add: zero_inat_def[symmetric])
    next
      case (Suc n')
      with IH[of n' xs'] `Fin n \<le> llength xs` LCons show ?thesis
        by(auto simp add: iSuc_Fin[symmetric] ldropn.simps)
    qed
  qed
qed

lemma ldropn_iterates: "ldropn n (iterates f x) = iterates f ((f ^^ n) x)"
proof(induct n arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "ldropn (Suc n) (iterates f x) = ldropn n (iterates f (f x))"
    by(subst iterates)simp
  also have "\<dots> = iterates f ((f ^^ n) (f x))" by(rule Suc)
  also have "\<dots> = iterates f ((f ^^ Suc n) x)" by(simp only: funpow_Suc_tail_rec)
  finally show ?case .
qed

lemma ldropn_llist_of [simp]: "ldropn n (llist_of xs) = llist_of (drop n xs)"
proof(induct n arbitrary: xs)
  case Suc thus ?case by(cases xs) simp_all
qed simp

lemma ldrop_llist_of: "ldrop (Fin n) (llist_of xs) = llist_of (drop n xs)"
by simp


subsection {* Taking the $n$-th element of a lazy list: @{term "lnth" } *}

lemma lnth_LNil:
  "lnth LNil n = undefined n"
by(cases n)(simp_all add: lnth.simps)

lemma lnth_0 [simp]:
  "lnth (LCons x xs) 0 = x"
by(simp add: lnth.simps)

lemma lnth_Suc_LCons [simp]:
  "lnth (LCons x xs) (Suc n) = lnth xs n"
by(simp add: lnth.simps)

lemma lnth_LCons:
  "lnth (LCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> lnth xs n')"
by(cases n) simp_all

lemma lnth_lmap [simp]: 
  "Fin n < llength xs \<Longrightarrow> lnth (lmap f xs) n = f (lnth xs n)"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) simp_all
next
  case (Suc n)
  from `Fin (Suc n) < llength xs` obtain x xs'
    where xs: "xs = LCons x xs'" and len: "Fin n < llength xs'"
    by(cases xs)(auto simp add: Suc_ile_eq)
  from len have "lnth (lmap f xs') n = f (lnth xs' n)" by(rule Suc)
  with xs show ?case by simp
qed

lemma lnth_ldropn [simp]:
  "Fin (n + m) < llength xs \<Longrightarrow> lnth (ldropn n xs) m = lnth xs (m + n)"
proof(induct n arbitrary: xs)
  case (Suc n)
  from `Fin (Suc n + m) < llength xs`
  obtain x xs' where "xs = LCons x xs'" by(cases xs) auto
  moreover with `Fin (Suc n + m) < llength xs`
  have "Fin (n + m) < llength xs'" by(simp add: Suc_ile_eq)
  hence "lnth (ldropn n xs') m = lnth xs' (m + n)" by(rule Suc)
  ultimately show ?case by simp
qed simp

lemma lnth_iterates [simp]: "lnth (iterates f x) n = (f ^^ n) x"
proof(induct n arbitrary: x)
  case 0 thus ?case by(subst iterates) simp
next
  case (Suc n)
  hence "lnth (iterates f (f x)) n = (f ^^ n) (f x)" .
  also have "\<dots> = (f ^^ Suc n) x" by(simp only: funpow_Suc_tail_rec)
  finally show ?case by(subst iterates) simp
qed

lemma lnth_llist_of: "n < length xs \<Longrightarrow> lnth (llist_of xs) n = xs ! n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `Suc n < length xs` obtain x xs'
    where "xs = x # xs'" by(cases xs) auto
  moreover with `Suc n < length xs`
  have "n < length xs'" by simp
  hence "lnth (llist_of xs') n = xs' ! n" by(rule Suc)
  ultimately show ?case by simp
qed

lemma lnth_lappend1:
  "Fin n < llength xs \<Longrightarrow> lnth (lappend xs ys) n = lnth xs n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(auto simp add: zero_inat_def[symmetric] neq_LNil_conv)
next
  case (Suc n)
  from `Fin (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" and len: "Fin n < llength xs'"
    by(cases xs)(auto simp add: Suc_ile_eq)
  from len have "lnth (lappend xs' ys) n = lnth xs' n" by(rule Suc)
  thus ?case by simp
qed

lemma lnth_lappend_llist_of: 
  "lnth (lappend (llist_of xs) ys) n = 
  (if n < length xs then xs ! n else lnth ys (n - length xs))"
proof(induct xs arbitrary: n)
  case (Cons x xs) thus ?case by(cases n) auto
qed simp

lemma lnth_lappend2:
  "\<lbrakk> llength xs = Fin k; k \<le> n \<rbrakk> \<Longrightarrow> lnth (lappend xs ys) n = lnth ys (n - k)"
proof(induct n arbitrary: xs k)
  case 0 thus ?case by(simp add: zero_inat_def[symmetric])
next
  case (Suc n) thus ?case
    by(cases xs)(auto simp add: iSuc_def zero_inat_def split: inat.split_asm)
qed

lemma lnth_ltake:
  "Fin m < n \<Longrightarrow> lnth (ltake n xs) m = lnth xs m"
proof(induct m arbitrary: xs n)
  case 0 thus ?case
    by(cases n rule: inat_coexhaust)(auto, cases xs, auto)
next
  case (Suc m)
  from `Fin (Suc m) < n` obtain n' where "n = iSuc n'"
    by(cases n rule: inat_coexhaust) auto
  with `Fin (Suc m) < n` have "Fin m < n'" by(simp add: iSuc_Fin[symmetric])
  with Suc `n = iSuc n'` show ?case by(cases xs) auto
qed

lemma ldropn_Suc_conv_ldropn:
  "Fin n < llength xs \<Longrightarrow> LCons (lnth xs n) (ldropn (Suc n) xs) = ldropn n xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `Fin (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" by(cases xs) auto
  from `Fin (Suc n) < llength xs`
  have "Fin n < llength xs'" by(simp add: Suc_ile_eq)
  hence "LCons (lnth xs' n) (ldropn (Suc n) xs') = ldropn n xs'" by(rule Suc)
  thus ?case by simp
qed

subsection {* Zipping two lazy lists to a lazy list of pairs @{term "lzip" } *}

lemma lzip_simps [simp, code]:
  "lzip LNil ys = LNil"
  "lzip xs LNil = LNil"
  "lzip (LCons x xs) (LCons y ys) = LCons (x, y) (lzip xs ys)"
by(simp_all add: lzip_def llist_corec split: llist_split)

lemma lzip_eq_LNil_conv: "lzip xs ys = LNil \<longleftrightarrow> xs = LNil \<or> ys = LNil"
apply(cases xs, simp)
apply(cases ys, simp_all)
done

lemma lzip_eq_LCons_conv:
  "lzip xs ys = LCons z zs \<longleftrightarrow>
   (\<exists>x xs' y ys'. xs = LCons x xs' \<and> ys = LCons y ys' \<and> z = (x, y) \<and> zs = lzip xs' ys')"
apply(cases xs, simp)
apply(cases ys, auto)
done

lemma lzip_lappend: 
  assumes len: "llength xs = llength us"
  shows "lzip (lappend xs ys) (lappend us vs) = lappend (lzip xs us) (lzip ys vs)"
proof -
  have "(lzip (lappend xs ys) (lappend us vs), lappend (lzip xs us) (lzip ys vs)) \<in> 
       {(lzip (lappend xs ys) (lappend us vs), lappend (lzip xs us) (lzip ys vs)) 
        | xs ys us vs. llength xs = llength us}"
    using len by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys us vs
      where q: "q = (lzip (lappend xs ys) (lappend us vs),
                     lappend (lzip xs us) (lzip ys vs))"
      and len: "llength xs = llength us" by blast
    show ?case
    proof(cases xs)
      case LNil
      with len q show ?thesis by(cases "lzip ys vs") simp_all
    next
      case (LCons x xs')
      with len q have ?EqLCons by(cases us) auto
      thus ?thesis ..
    qed
  qed
qed

lemma llength_lzip: 
  fixes xs :: "'a llist" and ys :: "'b llist"
  shows "llength (lzip xs ys) = min (llength xs) (llength ys)"
proof -
  have "(llength (lzip xs ys), min (llength xs) (llength ys)) \<in> 
       {(llength (lzip xs ys), min (llength xs) (llength ys)) 
        | (xs :: 'a llist) (ys :: 'b llist). True}"
    by blast
  thus ?thesis
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain xs :: "'a llist" and ys :: "'b llist"
      where m: "m = llength (lzip xs ys)"
      and n: "n = min (llength xs) (llength ys)" by blast
    show ?case
    proof(cases "xs = LNil \<or> ys = LNil")
      case True
      with m n have ?zero by auto
      thus ?thesis ..
    next
      case False
      with m n have ?iSuc by(auto simp add: neq_LNil_conv) blast
      thus ?thesis ..
    qed
  qed
qed

lemma ltake_lzip: "ltake n (lzip xs ys) = lzip (ltake n xs) (ltake n ys)"
proof -
  have "(ltake n (lzip xs ys), lzip (ltake n xs) (ltake n ys)) \<in>
        {(ltake n (lzip xs ys), lzip (ltake n xs) (ltake n ys))|n xs ys. True}"
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain n xs ys
      where q: "q = (ltake n (lzip xs ys), lzip (ltake n xs) (ltake n ys))"
      by blast
    show ?case
    proof(cases "xs = LNil \<or> ys = LNil \<or> n = 0")
      case True
      with q have ?EqLNil by auto
      thus ?thesis ..
    next
      case False
      then obtain x xs' y ys' n'
	where "xs = LCons x xs'" "ys = LCons y ys'" "n = iSuc n'"
	by(auto simp add: neq_LNil_conv neq_zero_conv_iSuc) blast
      with q have ?EqLCons by auto
      thus ?thesis ..
    qed
  qed
qed

lemma ldropn_lzip [simp]:
  "ldropn n (lzip xs ys) = lzip (ldropn n xs) (ldropn n ys)"
by(induct n arbitrary: xs ys)(simp_all add: ldropn.simps split: llist_split)

lemma ldrop_lzip [simp]: "ldrop n (lzip xs ys) = lzip (ldrop n xs) (ldrop n ys)"
by(cases n) simp_all

lemma lzip_iterates:
  "lzip (iterates f x) (iterates g y) = iterates (\<lambda>(x, y). (f x, g y)) (x, y)"
proof -
  let ?f = "\<lambda>(x, y). (f x, g y)"
  have "(lzip (iterates f x) (iterates g y), iterates ?f (x, y)) \<in>
       {(lzip (iterates f x) (iterates g y), iterates ?f (x, y))|x y. True}"
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain x y
      where q: "q = (lzip (iterates f x) (iterates g y), iterates ?f (x, y))"
      by auto
    have ?EqLCons unfolding q by(subst (1 2 3) iterates) auto
    thus ?case ..
  qed
qed

lemma lzip_llist_of [simp]:
  "lzip (llist_of xs) (llist_of ys) = llist_of (zip xs ys)"
proof(induct xs arbitrary: ys)
  case (Cons x xs')
  thus ?case by(cases ys) simp_all
qed simp

lemma lnth_lzip:
  "\<lbrakk> Fin n < llength xs; Fin n < llength ys \<rbrakk>
  \<Longrightarrow> lnth (lzip xs ys) n = (lnth xs n, lnth ys n)"
proof(induct n arbitrary: xs ys)
  case 0
  then obtain x xs' y ys' where "xs = LCons x xs'" "ys = LCons y ys'"
    unfolding zero_inat_def[symmetric]
    by(cases xs, simp)(cases ys, auto)
  thus ?case by simp
next
  case (Suc n)
  from `Fin (Suc n) < llength xs` obtain x xs'
    where xs: "xs = LCons x xs'" by(cases xs) auto
  moreover from `Fin (Suc n) < llength ys` obtain y ys'
    where ys: "ys = LCons y ys'" by(cases ys) auto
  moreover from `Fin (Suc n) < llength xs` `Fin (Suc n) < llength ys` xs ys
  have "Fin n < llength xs'" "Fin n < llength ys'"
    by(auto simp add: iSuc_Fin[symmetric])
  hence "lnth (lzip xs' ys') n = (lnth xs' n, lnth ys' n)" by(rule Suc)
  ultimately show ?case by simp
qed


lemma lfinite_lzip [simp]:
  "lfinite (lzip xs ys) \<longleftrightarrow> lfinite xs \<or> lfinite ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
  proof(induct zs\<equiv>"lzip xs ys" arbitrary: xs ys)
    case lfinite_LNil[symmetric]
    thus ?case by(auto simp add: lzip_eq_LNil_conv)
  next
    case (lfinite_LConsI zs z)
    from `LCons z zs = lzip xs ys`[symmetric]
    obtain x xs' y ys' where "xs = LCons x xs'" "ys = LCons y ys'"
      "z = (x, y)" "zs = lzip xs' ys'"
      unfolding lzip_eq_LCons_conv by blast
    with `zs = lzip xs' ys' \<Longrightarrow> lfinite xs' \<or> lfinite ys'` show ?case by simp
  qed
next
  assume ?rhs (is "?xs \<or> ?ys")
  thus ?lhs
  proof
    assume ?xs
    thus ?thesis
    proof(induct arbitrary: ys)
      case (lfinite_LConsI xs x)
      thus ?case by(cases ys) simp_all
    qed simp
  next
    assume ?ys
    thus ?thesis
    proof(induct arbitrary: xs)
      case (lfinite_LConsI ys y)
      thus ?case by(cases xs) simp_all
    qed simp
  qed
qed

lemma lappend_eq_lappend_conv:
  assumes len: "llength xs = llength us"
  shows "lappend xs ys = lappend us vs \<longleftrightarrow>
         xs = us \<and> (lfinite xs \<longrightarrow> ys = vs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  thus ?lhs by(auto simp add: lappend_inf)
next
  assume eq: ?lhs
  show ?rhs
  proof(intro conjI impI)
    have "(xs, us) \<in> {(xs, us). llength xs = llength us \<and> lappend xs ys = lappend us vs}"
      using len eq by blast
    thus "xs = us"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain xs us where q: "q = (xs, us)"
	and len: "llength xs = llength us"
	and eq: "lappend xs ys = lappend us vs" by blast
      show ?case
      proof(cases xs)
	case LNil
	with len have "us = LNil" by simp
	with LNil q show ?thesis by simp
      next
	case (LCons x xs')
	with len obtain u us'
          where "us = LCons u us'" by(cases us)(auto)
	with LCons q len eq show ?thesis by simp
      qed
    qed
    assume "lfinite xs"
    then obtain xs' where "xs = llist_of xs'"
      by(auto simp add: lfinite_eq_range_llist_of)
    hence "(ys, vs) \<in> {(ys, vs). \<exists>xs'. lappend (llist_of xs') ys = lappend (llist_of xs') vs}"
      using eq `xs = us` by blast
    thus "ys = vs"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain ys vs xs' where q: "q = (ys, vs)"
	and eq: "lappend (llist_of xs') ys = lappend (llist_of xs') vs" by blast
      show ?case
      proof(cases ys)
	case LNil
	with eq have "vs = LNil"
	proof(cases vs)
	  case (LCons v vs')
	  with eq LNil have "llist_of xs' = lappend (llist_of (xs' @ [v])) vs'"
	    by(auto simp add: lappend_llist_of_LCons)
	  hence "llength (llist_of xs') = llength (lappend (llist_of (xs' @ [v])) vs')"
            by simp
	  hence "Fin (length xs') = Fin (Suc (length xs')) + llength vs'"
            by simp
	  hence False by(metis Suc_n_not_le_n inat_le_plus_same(1) inat_ord_code(1))
	  thus ?thesis ..
	qed simp
	with LNil q have ?EqLNil by simp
	thus ?thesis ..
      next
	case (LCons y ys')
	with eq obtain vs'
          where "vs = LCons y vs'" 
          and "lappend (llist_of (xs' @ [y])) ys' = lappend (llist_of (xs' @ [y])) vs'"
	proof(cases vs)
	  case LNil
	  with eq LCons have "llist_of xs' = lappend (llist_of (xs' @ [y])) ys'"
	    by(auto simp add: lappend_llist_of_LCons)
	  hence "llength (llist_of xs') = llength (lappend (llist_of (xs' @ [y])) ys')"
            by simp
	  hence "Fin (length xs') = Fin (Suc (length xs')) + llength ys'" by simp
	  hence False by(metis Suc_n_not_le_n inat_le_plus_same(1) inat_ord_code(1))
	  thus ?thesis ..
	next
	  case (LCons v vs')
	  have "y = lnth (lappend (llist_of (xs' @ [y])) ys') (length xs')"
	    by(simp add: lnth_lappend1 lnth_llist_of)
	  also from eq `ys = LCons y ys'` LCons
	  have "lappend (llist_of (xs' @ [y])) ys' = lappend (llist_of (xs' @ [v])) vs'"
	    by(auto simp add: lappend_llist_of_LCons)
	  also have "lnth \<dots> (length xs') = v"
            by(simp add: lnth_lappend1 lnth_llist_of)
	  finally show ?thesis using eq LCons `ys = LCons y ys'` that
	    by(auto simp add: lappend_llist_of_LCons)
	qed
	with LCons q show ?thesis by auto
      qed
    qed
  qed
qed

lemma lzip_eq_lappend_conv:
  assumes eq: "lzip xs ys = lappend us vs"
  shows "\<exists>xs' xs'' ys' ys''. xs = lappend xs' xs'' \<and> ys = lappend ys' ys'' \<and>
                             llength xs' = llength ys' \<and> us = lzip xs' ys' \<and>
                             vs = lzip xs'' ys''"
proof -
  let ?xs' = "ltake (llength us) xs"
  let ?xs'' = "ldrop (llength us) xs"
  let ?ys' = "ltake (llength us) ys"
  let ?ys'' = "ldrop (llength us) ys"

  from eq have "llength (lzip xs ys) = llength (lappend us vs)" by simp
  hence "min (llength xs) (llength ys) \<ge> llength us"
    by(auto simp add: llength_lzip inat_le_plus_same)
  hence len: "llength xs \<ge> llength us" "llength ys \<ge> llength us" by(auto)

  hence leneq: "llength ?xs' = llength ?ys'" by(simp add: min_def)
  have xs: "xs = lappend ?xs' ?xs''" and ys: "ys = lappend ?ys' ?ys''"
    by(simp_all add: lappend_ltake_ldrop)
  hence "lappend us vs = lzip (lappend ?xs' ?xs'') (lappend ?ys' ?ys'')"
    using eq by simp
  with len have "lappend us vs = lappend (lzip ?xs' ?ys') (lzip ?xs'' ?ys'')"
    by(simp add: lzip_lappend min_def)
  hence us: "us = lzip ?xs' ?ys'" 
    and vs: "lfinite us \<longrightarrow> vs = lzip ?xs'' ?ys''" using len
    by(simp_all add: llength_lzip min_def lappend_eq_lappend_conv)
  show ?thesis
  proof(cases "lfinite us")
    case True
    with leneq xs ys us vs len show ?thesis by fastsimp
  next
    case False
    let ?xs'' = "lmap fst vs"
    let ?ys'' = "lmap snd vs"
    from False have "lappend us vs = us" by(simp add: lappend_inf)
    moreover from False have "llength us = Infty"
      by(rule not_lfinite_llength)
    moreover with len
    have "llength xs = Infty" "llength ys = Infty" by auto
    moreover with `llength us = Infty`
    have "xs = ?xs'" "ys = ?ys'" by(simp_all add: ltake_all)
    from `llength us = Infty` len 
    have "\<not> lfinite ?xs'" "\<not> lfinite ?ys'"
      by(auto simp del: llength_ltake lfinite_ltake 
             simp add: ltake_all dest: lfinite_llength_Fin)
    with `xs = ?xs'` `ys = ?ys'`
    have "xs = lappend ?xs' ?xs''" "ys = lappend ?ys' ?ys''"
      by(simp_all add: lappend_inf)
    moreover have "vs = lzip ?xs'' ?ys''" 
      by(coinduct vs rule: llist_fun_equalityI) simp_all
    ultimately show ?thesis using eq by(fastsimp  simp add: ltake_all)
  qed
qed

lemma lzip_lmap [simp]:
  "lzip (lmap f xs) (lmap g ys) = lmap (\<lambda>(x, y). (f x, g y)) (lzip xs ys)"
proof -
  let ?f = "\<lambda>(x, y). (f x, g y)"
  have "(lzip (lmap f xs) (lmap g ys), lmap ?f (lzip xs ys)) \<in>
       {(lzip (lmap f xs) (lmap g ys), lmap ?f (lzip xs ys))|xs ys. True}" 
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys 
      where q: "q = (lzip (lmap f xs) (lmap g ys), lmap ?f (lzip xs ys))" 
      by blast
    show ?case unfolding q by(cases xs)(simp, cases ys, auto)
  qed
qed

lemma lzip_lmap1:
  "lzip (lmap f xs) ys = lmap (\<lambda>(x, y). (f x, y)) (lzip xs ys)"
by(subst (4) lmap_ident[symmetric])(simp only: lzip_lmap)

lemma lzip_lmap2: 
  "lzip xs (lmap f ys) = lmap (\<lambda>(x, y). (x, f y)) (lzip xs ys)"
by(subst (1) lmap_ident[symmetric])(simp only: lzip_lmap)

lemma lmap_fst_lzip_conv_ltake: 
  fixes ys :: "'b llist"
  shows "lmap fst (lzip xs ys) = ltake (min (llength xs) (llength ys)) xs"
proof -
  have "(lmap fst (lzip xs ys), ltake (min (llength xs) (llength ys)) xs) \<in>
       {(lmap fst (lzip xs ys), ltake (min (llength xs) (llength ys)) xs)
        | xs (ys :: 'b llist). True}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs and ys :: "'b llist"
      where q: "q = (lmap fst (lzip xs ys), ltake (min (llength xs) (llength ys)) xs)"
      by blast
    thus ?case by(cases xs)(simp, cases ys, auto)
  qed
qed

lemma lmap_snd_lzip_conv_ltake: 
  fixes xs :: "'a llist"
  shows "lmap snd (lzip xs ys) = ltake (min (llength xs) (llength ys)) ys"
proof -
  let ?l = "\<lambda>xs ys. min (llength xs) (llength ys)"
  have "(lmap snd (lzip xs ys), ltake (?l xs ys) ys) \<in>
       {(lmap snd (lzip xs ys), ltake (?l xs ys) ys) | (xs :: 'a llist) ys. True}"
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs :: "'a llist" and ys
      where q: "q = (lmap snd (lzip xs ys), ltake (?l xs ys) ys)" by blast
    thus ?case by(cases xs)(simp, cases ys, auto)
  qed
qed

lemma lzip_conv_lzip_ltake_min_llength:
  "lzip xs ys = 
  lzip (ltake (min (llength xs) (llength ys)) xs) 
       (ltake (min (llength xs) (llength ys)) ys)"
proof -
  let ?l = "\<lambda>xs ys. min (llength xs) (llength ys)"
  have "(lzip xs ys, lzip (ltake (?l xs ys) xs) (ltake (?l xs ys) ys)) \<in>
       {(lzip xs ys, lzip (ltake (?l xs ys) xs) (ltake (?l xs ys) ys))|xs ys. True}" 
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys
      where q: "q = (lzip xs ys, lzip (ltake (?l xs ys) xs) (ltake (?l xs ys) ys))"
      by blast
    show ?case unfolding q by(cases xs)(simp, cases ys, auto)
  qed
qed

subsection {* The set of elements in a lazy list: @{term "lset"} *}

lemma lset_LNil [simp]:
  "lset LNil = {}"
by(simp add: lset_def)

lemma lset_LCons [simp]:
  "lset (LCons x xs) = insert x (lset xs)"
proof -
  have "x \<in> lnth (LCons x xs) ` {n. Fin n \<le> llength xs}"
    by(rule image_eqI[where x=0])(simp_all add: zero_inat_def[symmetric])
  thus ?thesis
    by(auto simp add: lset_def Suc_ile_eq lnth_LCons split: nat.split)
qed

lemma lset_lmap [simp]: "lset (lmap f xs) = f ` lset xs"
apply(auto simp add: lset_def)
apply(rule_tac x=xb in image_eqI, auto)
done

lemma lset_lzip: 
  "lset (lzip xs ys) =
   {(lnth xs n, lnth ys n)|n. Fin n < min (llength xs) (llength ys)}"
apply(auto simp add: lset_def llength_lzip lnth_lzip)
apply(rule_tac x=n in image_eqI)
apply(auto simp add: lnth_lzip)
done

lemma lset_iterates:
  "lset (iterates f x) = {(f ^^ n) x|n. True}"
by(auto simp add: lset_def)

lemma lset_llist_of [simp]: "lset (llist_of xs) = set xs"
by(induct xs) simp_all

lemma split_llist:
  assumes "x \<in> lset xs"
  shows "\<exists>ys zs. xs = lappend ys (LCons x zs) \<and> lfinite ys"
proof -
  from `x \<in> lset xs` obtain n where x: "x = lnth xs n"
    and n: "Fin n < llength xs" unfolding lset_def by auto
  from n show ?thesis unfolding x
  proof(induct n arbitrary: xs)
    case 0
    then obtain x xs' where "xs = LCons x xs'" by(cases xs) auto
    hence "xs = lappend LNil (LCons (lnth xs 0) xs')" by simp
    thus ?case by blast
  next
    case (Suc n)
    note IH = `\<And>xs. Fin n < llength xs
               \<Longrightarrow> \<exists>ys zs. xs = lappend ys (LCons (lnth xs n) zs) \<and> lfinite ys`
    note len = `Fin (Suc n) < llength xs`
    then obtain x xs' where xs: "xs = LCons x xs'"
      by(cases xs) auto
    with len have "Fin n < llength xs'" by(simp add: Suc_ile_eq)
    from IH[OF this] obtain ys zs
      where "xs' = lappend ys (LCons (lnth xs' n) zs)" "lfinite ys" by blast
    with xs have "xs = lappend (LCons x ys) (LCons (lnth xs (Suc n)) zs)"
      and "lfinite (LCons x ys)" by simp_all
    thus ?case by blast
  qed
qed

lemma lset_lappend_lfinite [simp]:
  "lfinite xs \<Longrightarrow> lset (lappend xs ys) = lset xs \<union> lset ys"
by(induct rule: lfinite.induct) auto

lemma lset_lappend: "lset (lappend xs ys) \<subseteq> lset xs \<union> lset ys"
proof(cases "lfinite xs")
  case True
  thus ?thesis by(simp add: lset_lappend_lfinite)
next
  case False
  thus ?thesis by(auto simp add: lappend_inf) 
qed

lemma lfinite_imp_finite_lset:
  assumes "lfinite xs"
  shows "finite (lset xs)"
using assms
by induct auto

lemma lset_code [code]:
  "lset LNil y \<longleftrightarrow> False"
  "lset (LCons x xs) y \<longleftrightarrow> (x = y \<or> lset xs y)"
apply(simp_all)
 apply(simp only: empty_def Collect_def)
apply(auto simp only: insert_def Collect_def Un_def mem_def)
done

subsection {* @{term "llist_all2"} *}

lemma llist_all2_LNil_LNil [simp]: "llist_all2 P LNil LNil"
  by(simp add: llist_all2_def)

lemma llist_all2_LNil_LCons [simp]: "\<not> llist_all2 P LNil (LCons x xs)"
  by(simp add: llist_all2_def)

lemma llist_all2_LCons_LNil [simp]: "\<not> llist_all2 P (LCons x xs) LNil"
  by(simp add: llist_all2_def)

lemma llist_all2_LCons_LCons [simp]:
  "llist_all2 P (LCons x xs) (LCons y ys) \<longleftrightarrow> P x y \<and> llist_all2 P xs ys"
by(auto simp add: llist_all2_def)

lemma llist_all2_code [code]:
  "llist_all2 P LNil LNil = True"
  "llist_all2 P LNil (LCons y ys) = False"
  "llist_all2 P (LCons x xs) LNil = False"
  "llist_all2 P (LCons x xs) (LCons y ys) \<longleftrightarrow> P x y \<and> llist_all2 P xs ys"
by(simp_all)

lemma llist_all2_llist_of [simp]:
  "llist_all2 P (llist_of xs) (llist_of ys) = list_all2 P xs ys"
by(induct xs ys rule: list_induct2')(simp_all)

lemma llist_all2_llengthD:
  "llist_all2 P xs ys \<Longrightarrow> llength xs = llength ys"
by(simp add: llist_all2_def)

lemma llist_all2_all_lnthI:
  "\<lbrakk> llength xs = llength ys;
     \<And>n. Fin n < llength xs \<Longrightarrow> P (lnth xs n) (lnth ys n) \<rbrakk>
  \<Longrightarrow> llist_all2 P xs ys"
by(auto simp add: llist_all2_def lset_lzip)

lemma llist_all2_lnthD:
  "\<lbrakk> llist_all2 P xs ys; Fin n < llength xs \<rbrakk> \<Longrightarrow> P (lnth xs n) (lnth ys n)"
by(fastsimp simp add: llist_all2_def lset_lzip)

lemma llist_all2_lnthD2:
  "\<lbrakk> llist_all2 P xs ys; Fin n < llength ys \<rbrakk> \<Longrightarrow> P (lnth xs n) (lnth ys n)"
by(fastsimp simp add: llist_all2_def lset_lzip)

lemma llist_all2_conv_all_lnth:
  "llist_all2 P xs ys \<longleftrightarrow> 
   llength xs = llength ys \<and> 
   (\<forall>n. Fin n < llength ys \<longrightarrow> P (lnth xs n) (lnth ys n))"
by(auto dest: llist_all2_llengthD llist_all2_lnthD2 intro: llist_all2_all_lnthI)


subsection {* Head and tail: @{term "lhd"} and @{term "ltl"} *}

lemma lhd_LCons [simp, code]:
  "lhd (LCons x xs) = x"
by(simp add: lhd_def)

lemma lhd_lappend:
  "lhd (lappend xs ys) = (if xs = LNil then lhd ys else lhd xs)"
by(auto simp add: lhd_def neq_LNil_conv)

lemma lhd_conv_lnth:
  "xs \<noteq> LNil \<Longrightarrow> lhd xs = lnth xs 0"
by(auto simp add: lhd_def neq_LNil_conv)

lemma ltl_simps [simp, code]:
  shows ltl_LNil: "ltl LNil = LNil"
  and ltl_LCons: "ltl (LCons x xs) = xs"
by(simp_all add: ltl_def)

lemma lhd_LCons_ltl: "xs \<noteq> LNil \<Longrightarrow> LCons (lhd xs) (ltl xs) = xs"
by(auto simp add: neq_LNil_conv)

lemma lhd_iterates [simp]: "lhd (iterates f x) = x"
by(subst iterates) simp

lemma lhd_llist_of [simp]: "lhd (llist_of xs) = hd xs"
by(cases xs)(simp_all add: hd_def lhd_def)

lemma lhd_ldropn:
  "Fin n < llength xs \<Longrightarrow> lhd (ldropn n xs) = lnth xs n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `Fin (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" by(cases xs) auto
  from `Fin (Suc n) < llength xs`
  have "Fin n < llength xs'" by(simp add: Suc_ile_eq)
  hence "lhd (ldropn n xs') = lnth xs' n" by(rule Suc)
  thus ?case by simp
qed

lemma ldropn_Suc: "ldropn (Suc n) xs = ldropn n (ltl xs)"
by(simp add: ldropn.simps split: llist_split)

lemma ldrop_iSuc_ltl: "ldrop (iSuc n) xs = ldrop n (ltl xs)"
by(simp add: iSuc_def ldropn_Suc split: inat.split)

lemma llength_ltl: "llength (ltl xs) = llength xs - 1"
by(cases xs) simp_all

lemma ltake_ltl: "ltake n (ltl xs) = ltl (ltake (iSuc n) xs)"
by(cases xs) simp_all

lemma ltl_llist_of [simp]: "ltl (llist_of xs) = llist_of (tl xs)"
by(cases xs) simp_all

lemma ltl_lappend:
  "ltl (lappend xs ys) = 
   (case xs of LNil \<Rightarrow> ltl ys | LCons x xs' \<Rightarrow> lappend xs' ys)"
by(simp split: llist_split)

lemma ltl_ldropn: "ltl (ldropn n xs) = ldropn n (ltl xs)"
proof(induct n arbitrary: xs)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case
    by(cases xs)(simp_all del: ldropn.simps(2) add: ldropn_Suc)
qed

lemma ltl_ldrop: "ltl (ldrop n xs) = ldrop n (ltl xs)"
by(cases n)(simp_all add: ltl_ldropn)

lemma ltl_iterates [simp]: "ltl (iterates f x) = iterates f (f x)"
by(subst iterates) simp

lemma ltl_take: "ltl (ltake n xs) = ltake (n - 1) (ltl xs)"
apply(cases xs, simp_all)
apply(cases n rule: inat_coexhaust, simp_all)
done


subsection {* 
  The prefix ordering on lazy lists: 
  @{term "lprefix"} and @{term "lstrict_prefix"} 
*}

lemma lprefix_refl [intro, simp]: "lprefix xs xs"
by(auto simp add: lprefix_def intro: exI[where x=LNil])

lemma lprefix_LNIl [simp]: "lprefix xs LNil \<longleftrightarrow> xs = LNil"
by(auto simp add: lprefix_def)

lemma LNil_lprefix [simp, intro]: "lprefix LNil xs"
by(simp add: lprefix_def)

lemma lprefix_LCons_conv: 
  "lprefix xs (LCons y ys) \<longleftrightarrow> 
   xs = LNil \<or> (\<exists>xs'. xs = LCons y xs' \<and> lprefix xs' ys)"
by(cases xs)(auto simp add: lprefix_def)

lemma LCons_lprefix_LCons [simp]:
  "lprefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lprefix xs ys"
by(simp add: lprefix_LCons_conv)

lemma LCons_lprefix_conv:
  "lprefix (LCons x xs) ys \<longleftrightarrow> (\<exists>ys'. ys = LCons x ys' \<and> lprefix xs ys')"
by(cases ys)(auto)

lemma lprefix_antisym:
  assumes "lprefix xs ys" "lprefix ys xs"
  shows "xs = ys"
proof -
  have "(xs, ys) \<in> {(xs, ys)|xs ys. lprefix xs ys \<and> lprefix ys xs}"
    using assms by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where q: "q = (xs, ys)"
      and prefix: "lprefix xs ys" "lprefix ys xs" by blast
    show ?case
    proof(cases xs)
      case LNil
      with prefix have "ys = LNil" by simp
      with LNil q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with prefix obtain ys' 
        where "ys = LCons x ys'" 
        and "lprefix ys' xs'"
        and"lprefix xs' ys'"
	by(auto simp add: lprefix_LCons_conv)
      with LCons q have ?EqLCons by simp
      thus ?thesis ..
    qed
  qed
qed

lemma lprefix_trans [trans]:
  "\<lbrakk> lprefix xs ys; lprefix ys zs \<rbrakk> \<Longrightarrow> lprefix xs zs"
by(auto simp add: lprefix_def lappend_assoc)

lemma lprefix_code [code]:
  "lprefix LNil ys \<longleftrightarrow> True" 
  "lprefix (LCons x xs) LNil \<longleftrightarrow> False"
  "lprefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lprefix xs ys"
by simp_all

lemma lstrict_prefix_code [code, simp]:
  "lstrict_prefix LNil LNil \<longleftrightarrow> False"
  "lstrict_prefix LNil (LCons y ys) \<longleftrightarrow> True"
  "lstrict_prefix (LCons x xs) LNil \<longleftrightarrow> False"
  "lstrict_prefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lstrict_prefix xs ys"
by(auto simp add: lstrict_prefix_def)

lemma not_lfinite_lprefix_conv_eq:
  assumes nfin: "\<not> lfinite xs"
  shows "lprefix xs ys \<longleftrightarrow> xs = ys"
proof
  assume "lprefix xs ys" with nfin
  have "(xs, ys) \<in> {(xs, ys). lprefix xs ys \<and> \<not> lfinite xs}" by blast
  thus "xs = ys"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where "q = (xs, ys)" "lprefix xs ys" "\<not> lfinite xs" by blast
    hence ?EqLCons by(cases xs)(auto simp add: LCons_lprefix_conv)
    thus ?case ..
  qed
qed simp

lemma lmap_lprefix: "lprefix xs ys \<Longrightarrow> lprefix (lmap f xs) (lmap f ys)"
by(auto simp add: lprefix_def lmap_lappend_distrib)

lemma lprefix_llength_eq_imp_eq:
  assumes "lprefix xs ys" "llength xs = llength ys"
  shows "xs = ys"
proof -
  have "(xs, ys) \<in> {(xs, ys)|xs ys. lprefix xs ys \<and> llength xs = llength ys}"
    using assms by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where q: "q = (xs, ys)"
      and le: "lprefix xs ys" and len: "llength xs = llength ys" by blast
    show ?case
    proof(cases xs)
      case LNil
      with len have "ys = LNil" by simp
      with LNil q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with len obtain y ys' where "ys = LCons y ys'" by(cases ys) auto
      with q LCons len le have ?EqLCons by auto
      thus ?thesis ..
    qed
  qed
qed

lemma lprefix_llength_le:
  fixes xs ys :: "'a llist"
  assumes "lprefix xs ys"
  shows "llength xs \<le> llength ys"
proof -
  have "(llength xs, llength ys) \<in>
        {(llength xs, llength ys)|xs ys :: 'a llist. lprefix xs ys}" 
    using assms by blast
  thus ?thesis
  proof(coinduct rule: inat_leI)
    case (Leinat m n)
    then obtain xs ys :: "'a llist"
      where mn: "m = llength xs" "n = llength ys" "lprefix xs ys" by blast
    thus ?case
    proof(cases xs)
      case (LCons x xs')
      moreover with `lprefix xs ys` obtain ys'
	where "ys = LCons x ys'" "lprefix xs' ys'"
        by(auto simp add: LCons_lprefix_conv)
      moreover hence "n = llength ys' + Fin 1" using mn
	unfolding one_inat_def[symmetric] by(simp add: plus_1_iSuc)
      ultimately have ?iSuc using mn by auto
      thus ?thesis ..
    qed auto
  qed
qed

lemma lstrict_prefix_llength_less:
  assumes "lstrict_prefix xs ys"
  shows "llength xs < llength ys"
proof(rule ccontr)
  assume "\<not> llength xs < llength ys"
  moreover from `lstrict_prefix xs ys` have "lprefix xs ys" "xs \<noteq> ys"
    unfolding lstrict_prefix_def by simp_all
  from `lprefix xs ys` have "llength xs \<le> llength ys"
    by(rule lprefix_llength_le)
  ultimately have "llength xs = llength ys" by auto
  with `lprefix xs ys` have "xs = ys" 
    by(rule lprefix_llength_eq_imp_eq)
  with `xs \<noteq> ys` show False by contradiction
qed

lemma wfP_lstrict_prefix: "wfP lstrict_prefix"
proof(unfold wfP_def)
  have "wf {(x :: inat, y). x < y}"
    unfolding wf_def by(blast intro: less_induct)
  hence "wf (inv_image {(x, y). x < y} llength)" by(rule wf_inv_image)
  moreover have "{(xs, ys). lstrict_prefix xs ys} \<subseteq> inv_image {(x, y). x < y} llength"
    by(auto intro: lstrict_prefix_llength_less)
  ultimately show "wf {(xs, ys). lstrict_prefix xs ys}" by(rule wf_subset)
qed

lemma llist_less_induct[case_names less]:
  "(\<And>xs. (\<And>ys. lstrict_prefix ys xs \<Longrightarrow> P ys) \<Longrightarrow> P xs) \<Longrightarrow> P xs"
by(rule wfP_induct[OF wfP_lstrict_prefix]) blast

coinductive_set lprefix_llist :: "('a llist \<times> 'a llist) set"
where
  Le_LNil: "(LNil, xs) \<in> lprefix_llist"
| Le_LCons: "(xs, ys) \<in> lprefix_llist \<Longrightarrow> (LCons x xs, LCons x ys) \<in> lprefix_llist"

lemma lprefix_into_lprefix_llist:
  assumes "lprefix xs ys"
  shows "(xs, ys) \<in> lprefix_llist"
proof -
  from assms have "(xs, ys) \<in> {(xs, ys). lprefix xs ys}" by blast
  thus ?thesis
  proof(coinduct)
    case (lprefix_llist xs ys)
    hence pref: "lprefix xs ys" by simp
    show ?case
    proof(cases xs)
      case LNil hence ?Le_LNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      with pref obtain ys' where "ys = LCons x ys'" "lprefix xs' ys'"
	by(auto simp add: LCons_lprefix_conv)
      with LCons have ?Le_LCons by auto
      thus ?thesis ..
    qed
  qed
qed

lemma lprefix_llist_implies_ltake_lprefix:
  "(xs, ys) \<in> lprefix_llist \<Longrightarrow> lprefix (ltake (Fin n) xs) (ltake (Fin n) ys)"
proof(induct n arbitrary: xs ys)
  case 0 show ?case by(simp add: zero_inat_def[symmetric])
next
  case (Suc n)
  from `(xs, ys) \<in> lprefix_llist` show ?case
  proof cases
    case Le_LNil thus ?thesis by simp
  next
    case (Le_LCons xs' ys' x)
    from `(xs', ys') \<in> lprefix_llist`
    have "lprefix (ltake (Fin n) xs') (ltake (Fin n) ys')" by(rule Suc)
    with Le_LCons show ?thesis by(simp add: iSuc_Fin[symmetric])
  qed
qed

lemma ltake_Fin_eq_imp_eq:
  assumes "\<And>n. ltake (Fin n) xs = ltake (Fin n) ys"
  shows "xs = ys"
proof -
  have "(xs, ys) \<in> {(xs, ys)|xs ys. \<forall>n. ltake (Fin n) xs = ltake (Fin n) ys}"
    using assms by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where q: "q = (xs, ys)"
      and eq: "\<And>n. ltake (Fin n) xs = ltake (Fin n) ys" by blast
    show ?case
    proof(cases xs)
      case LNil
      with eq[of 1] have "ys = LNil"
	unfolding one_inat_def[symmetric] one_iSuc by(cases ys) simp_all
      with LNil q have ?EqLNil by simp
      thus ?thesis ..
    next
      case (LCons x xs')
      moreover with eq[of 1] obtain ys' where ys: "ys = LCons x ys'"
	unfolding one_inat_def[symmetric] one_iSuc by(cases ys) auto
      moreover have "\<forall>n. ltake (Fin n) xs' = ltake (Fin n) ys'"
      proof
	fix n from eq[of "Suc n"] ys LCons
	show "ltake (Fin n) xs' = ltake (Fin n) ys'"
	  unfolding iSuc_Fin[symmetric] by simp
      qed
      ultimately have ?EqLCons using q by auto
      thus ?thesis ..
    qed
  qed
qed

lemma ltake_Fin_lprefix_imp_lprefix:
  assumes le: "\<And>n. lprefix (ltake (Fin n) xs) (ltake (Fin n) ys)"
  shows "lprefix xs ys"
proof(cases "lfinite xs")
  case True
  then obtain n where n: "llength xs = Fin n" by(auto dest: lfinite_llength_Fin)
  have "xs = ltake (Fin n) xs" unfolding n[symmetric] by(simp add: ltake_all)
  also have "lprefix \<dots> (ltake (Fin n) ys)" by(rule le)
  also have "lprefix \<dots> ys" ..
  finally show ?thesis .
next
  case False
  hence [simp]: "llength xs = \<infinity>" by(rule not_lfinite_llength)
  { fix n
    from le[of n] obtain zs where "lappend (ltake (Fin n) xs) zs = ltake (Fin n) ys"
      unfolding lprefix_def by blast
    hence "llength (lappend (ltake (Fin n) xs) zs) = llength (ltake (Fin n) ys)"
      by simp
    hence n: "Fin n \<le> llength ys"
      by(cases "llength zs", cases "llength ys")
        (simp_all add: min_def split: split_if_asm)
    from le have "ltake (Fin n) xs = ltake (Fin n) ys"
      by(rule lprefix_llength_eq_imp_eq)(simp add: n min_def) }
  hence "xs = ys" by(rule ltake_Fin_eq_imp_eq)
  thus ?thesis by simp
qed

lemma lprefix_llist_imp_lprefix:
  "(xs, ys) \<in> lprefix_llist \<Longrightarrow> lprefix xs ys"
by(rule ltake_Fin_lprefix_imp_lprefix)(rule lprefix_llist_implies_ltake_lprefix)

lemma lprefix_llist_eq_lprefix:
  "(xs, ys) \<in> lprefix_llist \<longleftrightarrow> lprefix xs ys"
by(blast intro: lprefix_llist_imp_lprefix lprefix_into_lprefix_llist)

lemma lprefixI [consumes 1, case_names lprefix, 
                case_conclusion lprefix LeLNil LeLCons]:
  assumes major: "(xs, ys) \<in> X"
  and step [simplified mem_def]:
      "\<And>xs ys. (xs, ys) \<in> X 
       \<Longrightarrow> xs = LNil \<or> (\<exists>x xs' ys'. xs = LCons x xs' \<and> ys = LCons x ys' \<and> 
                                   ((xs', ys') \<in> X \<or> lprefix xs' ys'))"
  shows "lprefix xs ys"
proof -
  from major have "curry X xs ys" by(auto simp add: mem_def)
  thus ?thesis
    by(rule lprefix_llist.coinduct[unfolded lprefix_llist_eq_lprefix])
      (auto dest: step)
qed

lemma lprefix_lappend:
  "lprefix xs (lappend xs ys)"
proof -
  def zs \<equiv> "lappend xs ys"
  hence "(xs, zs) \<in> {(xs, zs). zs = lappend xs ys}" by blast
  thus "lprefix xs zs"
  proof(coinduct rule: lprefixI)
    case (lprefix xs zs)
    thus ?case by(cases xs) auto
  qed
qed

lemma lappend_lprefixE:
  assumes "lprefix (lappend xs ys) zs"
  obtains zs' where "zs = lappend xs zs'"
using assms unfolding lprefix_def by(auto simp add: lappend_assoc)

lemma lprefix_lfiniteD:
  "\<lbrakk> lprefix xs ys; lfinite ys \<rbrakk> \<Longrightarrow> lfinite xs"
unfolding lprefix_def by auto

lemma lprefix_lappendD:
  assumes "lprefix xs (lappend ys zs)"
  shows "lprefix xs ys \<or> lprefix ys xs"
proof(rule ccontr)
  assume "\<not> (lprefix xs ys \<or> lprefix ys xs)"
  hence "\<not> lprefix xs ys" "\<not> lprefix ys xs" by simp_all
  from `lprefix xs (lappend ys zs)` obtain xs' 
    where "lappend xs xs' = lappend ys zs"
    unfolding lprefix_def by auto
  hence eq: "lappend (ltake (llength ys) xs) (lappend (ldrop (llength ys) xs) xs') =
             lappend ys zs"
    unfolding lappend_assoc[symmetric] by(simp only: lappend_ltake_ldrop)
  moreover have "llength xs \<ge> llength ys"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "llength xs < llength ys" by simp
    hence "ltake (llength ys) xs = xs" by(simp add: ltake_all)
    hence "lappend xs (lappend (ldrop (llength ys) xs) xs') = 
           lappend (ltake (llength xs) ys) (lappend (ldrop (llength xs) ys) zs)"
      unfolding lappend_assoc[symmetric] lappend_ltake_ldrop
      using eq by(simp add: lappend_assoc)
    hence xs: "xs = ltake (llength xs) ys" using `llength xs < llength ys`
      by(subst (asm) lappend_eq_lappend_conv)(auto simp add: min_def)
    have "lprefix xs ys" by(subst xs) auto
    with `\<not> lprefix xs ys` show False by contradiction
  qed
  ultimately have ys: "ys = ltake (llength ys) xs"
    by(subst (asm) lappend_eq_lappend_conv)(simp_all add: min_def)
  have "lprefix ys xs" by(subst ys) auto
  with `\<not> lprefix ys xs` show False by contradiction
qed

lemma lstrict_prefix_lappend_conv:
  "lstrict_prefix xs (lappend xs ys) \<longleftrightarrow> lfinite xs \<and> ys \<noteq> LNil"
proof -
  { assume "lfinite xs" "xs = lappend xs ys"
    hence "ys = LNil" by induct auto }
  thus ?thesis
    by(auto simp add: lstrict_prefix_def lprefix_lappend lappend_inf 
            elim: contrapos_np)
qed


subsection {* Lexicographic order on lazy lists: @{term "llexord"} *}

lemma llexord_refl [simp, intro!]:
  "llexord r xs xs"
proof -
  def ys == xs
  hence "xs = ys" by simp
  thus "llexord r xs ys"
  proof(coinduct xs ys rule: llexord.coinduct)
    case (llexord xs ys)
    thus ?case by(cases xs) blast+
  qed
qed

lemma llexord_LCons_LCons [simp]:
  "llexord r (LCons x xs) (LCons y ys) \<longleftrightarrow> (x = y \<and> llexord r xs ys \<or> r x y)"
by(auto intro: llexord.intros elim: llexord.cases)

lemma llexord_LNil_right [simp]:
  "llexord r xs LNil \<longleftrightarrow> xs = LNil"
by(auto elim: llexord.cases intro: llexord.intros)

lemma llexord_LCons_left:
  "llexord r (LCons x xs) ys \<longleftrightarrow>
   (\<exists>y ys'. ys = LCons y ys' \<and> (x = y \<and> llexord r xs ys' \<or> r x y))"
by(cases ys)(auto elim: llexord.cases)

lemma lprefix_imp_llexord:
  assumes "lprefix xs ys"
  shows "llexord r xs ys"
using assms
proof(coinduct)
  case (llexord xs ys)
  thus ?case by(cases xs)(auto simp add: LCons_lprefix_conv)
qed

lemma llexord_empty:
  "llexord (\<lambda>x y. False) xs ys = lprefix xs ys"
proof
  assume "llexord (\<lambda>x y. False) xs ys"
  hence "(xs, ys) \<in> {(xs, ys). llexord (\<lambda>x y. False) xs ys}" by blast
  thus "lprefix xs ys" by(coinduct rule: lprefixI)(auto elim: llexord.cases)
qed(rule lprefix_imp_llexord)

lemma llexord_append_right:
  "llexord r xs (lappend xs ys)"
by(rule lprefix_imp_llexord)(auto simp add: lprefix_def)

lemma llexord_lappend_leftI:
  assumes "llexord r ys zs"
  shows "llexord r (lappend xs ys) (lappend xs zs)"
proof(cases "lfinite xs")
  case True thus ?thesis by induct (simp_all add: assms)
next
  case False thus ?thesis by(simp add: lappend_inf)
qed

lemma llexord_lappend_leftD:
  assumes "llexord r (lappend xs ys) (lappend xs zs)"
  and "lfinite xs"
  and "!!x. x \<in> lset xs \<Longrightarrow> \<not> r x x"
  shows "llexord r ys zs"
using `lfinite xs` `llexord r (lappend xs ys) (lappend xs zs)`
  `!!x. x \<in> lset xs \<Longrightarrow> \<not> r x x`
by(induct) simp_all

lemma llexord_lappend_left:
  "\<lbrakk> lfinite xs; !!x. x \<in> lset xs \<Longrightarrow> \<not> r x x \<rbrakk> 
  \<Longrightarrow> llexord r (lappend xs ys) (lappend xs zs) \<longleftrightarrow> llexord r ys zs"
by(blast intro: llexord_lappend_leftI llexord_lappend_leftD)

lemma antisym_llexord:
  assumes r: "antisymP r"
  and irrefl: "\<And>x. \<not> r x x"
  shows "antisymP (llexord r)"
proof(rule antisymI)
  fix xs ys
  assume "(xs, ys) \<in> {(xs, ys). llexord r xs ys}"
    and "(ys, xs) \<in> {(xs, ys). llexord r xs ys}"
  hence "(xs, ys) \<in> {(xs, ys). llexord r xs ys \<and> llexord r ys xs}" by auto
  thus "xs = ys"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where q: "q = (xs, ys)"
      and "llexord r xs ys" "llexord r ys xs" by blast
    from `llexord r xs ys` show ?case
    proof(cases)
      case (llexord_LCons_eq xs' ys' x)
      hence ?EqLCons unfolding q using `llexord r ys xs` irrefl[of x] by simp
      thus ?thesis ..
    next
      case (llexord_LCons_less x y xs' ys')
      with `llexord r ys xs` have "r y x" by auto
      with r `r x y` have "x = y" by(auto elim: antisymD)
      with irrefl[of x] `r x y` show ?thesis by auto
    next
      case llexord_LNil
      with `llexord r ys xs` have ?EqLNil unfolding q by simp
      thus ?thesis ..
    qed
  qed
qed

lemma llexord_antisym:
  "\<lbrakk> llexord r xs ys; llexord r ys xs; 
    !!a b. \<lbrakk> r a b; r b a \<rbrakk> \<Longrightarrow> False \<rbrakk> 
  \<Longrightarrow> xs = ys"
using antisymD[OF antisym_llexord, of r xs ys]
by(auto intro: antisymI)

lemma llexord_trans:
  assumes 1: "llexord r xs ys"
  and 2: "llexord r ys zs"
  and trans: "!!a b c. \<lbrakk> r a b; r b c \<rbrakk> \<Longrightarrow> r a c"
  shows "llexord r xs zs"
proof -
  from 1 2 have "\<exists>ys. llexord r xs ys \<and> llexord r ys zs" by blast
  thus ?thesis
  proof(coinduct)
    case (llexord xs zs)
    then obtain ys where "llexord r xs ys" "llexord r ys zs" by blast
    from `llexord r xs ys` show ?case
    proof(cases)
      case (llexord_LCons_eq xs' ys' x)
      from `ys = LCons x ys'` `llexord r ys zs` obtain z zs'
	where "zs = LCons z zs'" "x = z \<and> llexord r ys' zs' \<or> r x z"
	by(auto simp add: llexord_LCons_left)
      then show ?thesis using llexord_LCons_eq by(auto)
    next
      case (llexord_LCons_less x y xs' ys')
      from `ys = LCons y ys'` `llexord r ys zs` obtain z zs'
	where zs: "zs = LCons z zs'" "y = z \<and> llexord r ys' zs' \<or> r y z"
	by(auto simp add: llexord_LCons_left)
      from zs `r x y` have "r x z" by(auto intro: trans)
      with zs show ?thesis using llexord_LCons_less by auto
    qed simp
  qed
qed      

lemma trans_llexord:
  "transP r \<Longrightarrow> transP (llexord r)"
by(auto intro!: transI elim: llexord_trans dest: transD)
  
lemma llexord_linear:
  assumes linear: "!!x y. r x y \<or> x = y \<or> r y x"
  shows "llexord r xs ys \<or> llexord r ys xs"
proof(rule disjCI)
  assume "\<not> llexord r ys xs"
  thus "llexord r xs ys"
  proof(coinduct)
    case (llexord xs ys)
    show ?case
    proof(cases xs)
      case LNil thus ?thesis by simp
    next
      case (LCons x xs')
      with `\<not> llexord r ys xs` obtain y ys'
	where ys: "ys = LCons y ys'" "\<not> r y x" "y \<noteq> x \<or> \<not> llexord r ys' xs'"
	by(cases ys) auto
      with `\<not> r y x` linear[of x y] ys LCons show ?thesis by auto
    qed
  qed
qed

lemma llexord_code [code]:
  "llexord r LNil ys = True"
  "llexord r (LCons x xs) LNil = False"
  "llexord r (LCons x xs) (LCons y ys) = (r x y \<or> x = y \<and> llexord r xs ys)"
by auto

lemma llexord_conv:
 "llexord r xs ys \<longleftrightarrow> 
  xs = ys \<or>
  (\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and> ys = lappend zs (LCons y ys') \<and>
                  (xs' = LNil \<or> r (lhd xs') y))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  show ?rhs (is "_ \<or> ?prefix")
  proof(rule disjCI)
    assume "\<not> ?prefix"
    with `?lhs` 
    have "(xs, ys) \<in>
          {(xs, ys). llexord r xs ys \<and> 
                     (\<forall>zs xs' y ys'. lfinite zs \<longrightarrow> xs = lappend zs xs' \<longrightarrow>
                                     ys = lappend zs (LCons y ys') \<longrightarrow> 
                                     xs' \<noteq> LNil \<and> \<not> r (lhd xs') y)}"
      by auto
    thus "xs = ys"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain xs ys where q: "q = (xs, ys)"
	and "llexord r xs ys"
	and prefix: "\<And>zs xs' y ys'. \<lbrakk> lfinite zs; xs = lappend zs xs';
                                      ys = lappend zs (LCons y ys') \<rbrakk>
                                     \<Longrightarrow> xs' \<noteq> LNil \<and> \<not> r (lhd xs') y"
	by blast
      from `llexord r xs ys` show ?case
      proof(cases)
	case (llexord_LCons_eq xs' ys' x)
	{ fix zs xs'' y ys''
	  assume "lfinite zs" "xs' = lappend zs xs''" 
            and "ys' = lappend zs (LCons y ys'')"
	  hence "lfinite (LCons x zs)" "xs = lappend (LCons x zs) xs''"
            and "ys = lappend (LCons x zs) (LCons y ys'')"
	    using llexord_LCons_eq by simp_all
	  hence "xs'' \<noteq> LNil \<and> \<not> r (lhd xs'') y" by(rule prefix) }
	with llexord_LCons_eq show ?thesis unfolding q by auto
      next
	case (llexord_LCons_less x y xs' ys')
	with prefix[of LNil xs y ys'] show ?thesis by simp
      next
	case llexord_LNil
	have ?EqLNil
	proof(cases ys)
	  case LNil thus ?thesis unfolding q llexord_LNil by simp
	next
	  case (LCons y ys')
	  with prefix[of LNil xs y ys'] llexord_LNil
          show ?thesis by simp
	qed
	thus ?thesis ..
      qed
    qed
  qed
next
  assume ?rhs
  thus ?lhs
  proof(coinduct)
    case (llexord xs ys)
    show ?case
    proof(cases xs)
      case LNil thus ?thesis by simp
    next
      case (LCons x xs')
      with llexord obtain y ys' where "ys = LCons y ys'"
	by(cases ys)(auto dest: sym)
      show ?thesis
      proof(cases "x = y")
	case True
	from llexord show ?thesis
	proof
	  assume "xs = ys"
	  with True LCons `ys = LCons y ys'` show ?thesis by simp
	next
	  assume "\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and>
                                 ys = lappend zs (LCons y ys') \<and>
                                 (xs' = LNil \<or> r (lhd xs') y)"
	  then obtain zs xs' y' ys''
	    where "lfinite zs" "xs = lappend zs xs'"
            and "ys = lappend zs (LCons y' ys'')"
            and "xs' = LNil \<or> r (lhd xs') y'" by blast
	  with True LCons `ys = LCons y ys'`
          show ?thesis by(cases zs) auto
	qed
      next
	case False
	with LCons llexord `ys = LCons y ys'`
	have "r x y" by(fastsimp elim: lfinite.cases)
	with LCons `ys = LCons y ys'` show ?thesis by auto
      qed
    qed
  qed
qed

lemma llexord_conv_ltake_index:
  "llexord r xs ys \<longleftrightarrow>
   (llength xs \<le> llength ys \<and> ltake (llength xs) ys = xs) \<or>
   (\<exists>n. Fin n < min (llength xs) (llength ys) \<and> 
        ltake (Fin n) xs = ltake (Fin n) ys \<and> r (lnth xs n) (lnth ys n))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  thus ?rhs (is "?A \<or> ?B") unfolding llexord_conv
  proof
    assume "xs = ys" thus ?thesis by(simp add: ltake_all)
  next
    assume "\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and>
                           ys = lappend zs (LCons y ys') \<and>
                           (xs' = LNil \<or> r (lhd xs') y)"
    then obtain zs xs' y ys'
      where "lfinite zs" "xs' = LNil \<or> r (lhd xs') y"
      and [simp]: "xs = lappend zs xs'" "ys = lappend zs (LCons y ys')"
      by blast
    show ?thesis
    proof(cases xs')
      case LNil
      hence ?A by(auto intro: inat_le_plus_same simp add: ltake_lappend1 ltake_all)
      thus ?thesis ..
    next
      case LCons
      with `xs' = LNil \<or> r (lhd xs') y` have "r (lhd xs') y" by simp
      from `lfinite zs` obtain zs' where [simp]: "zs = llist_of zs'"
	unfolding lfinite_eq_range_llist_of by blast
      with LCons have "Fin (length zs') < min (llength xs) (llength ys)"
	by(auto simp add: less_inat_def iSuc_def split: inat.split)
      moreover have "ltake (Fin (length zs')) xs = ltake (Fin (length zs')) ys"
	by(simp add: ltake_lappend1)
      moreover have "r (lnth xs (length zs')) (lnth ys (length zs'))"
	using LCons `r (lhd xs') y`
        by(simp add: lappend_llist_of_LCons lnth_lappend1 lnth_llist_of)
      ultimately have ?B by blast
      thus ?thesis ..
    qed
  qed
next
  assume ?rhs (is "?A \<or> ?B")
  thus ?lhs
  proof
    assume ?A thus ?thesis
    proof(coinduct)
      case (llexord xs ys)
      thus ?case by(cases xs, simp)(cases ys, auto)
    qed
  next
    assume "?B"
    then obtain n where len: "Fin n < min (llength xs) (llength ys)"
      and takexs: "ltake (Fin n) xs = ltake (Fin n) ys"
      and r: "r (lnth xs n) (lnth ys n)" by blast
    have "xs = lappend (ltake (Fin n) xs) (ldrop (Fin n) xs)"
      by(simp only: lappend_ltake_ldrop)
    moreover from takexs len
    have "ys = lappend (ltake (Fin n) xs) (LCons (lnth ys n) (ldrop (Fin (Suc n)) ys))"
      by(simp add: ldropn_Suc_conv_ldropn)
        (simp only: lappend_ltake_ldrop ldrop.simps[symmetric])
    moreover from r len
    have "r (lhd (ldrop (Fin n) xs)) (lnth ys n)"
      by(simp add: lhd_ldropn)
    moreover have "lfinite (ltake (Fin n) xs)" by simp
    ultimately show ?thesis unfolding llexord_conv by blast
  qed
qed

lemma llist_of_eq_LNil_conv [simp]:
  "llist_of xs = LNil \<longleftrightarrow> xs = []"
by(cases xs) simp_all

lemma llist_of_eq_LCons_conv:
  "llist_of xs = LCons y ys \<longleftrightarrow> (\<exists>xs'. xs = y # xs' \<and> ys = llist_of xs')"
by(cases xs) auto

lemma llexord_llist_of:
  "llexord r (llist_of xs) (llist_of ys) \<longleftrightarrow> 
   xs = ys \<or> (xs, ys) \<in> lexord (\<lambda>(x, y). r x y)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  { fix zs xs' y ys'
    assume "lfinite zs" "llist_of xs = lappend zs xs'"
      and "llist_of ys = lappend zs (LCons y ys')"
      and "xs' = LNil \<or> r (lhd xs') y"
    from `lfinite zs` obtain zs' where [simp]: "zs = llist_of zs'"
      unfolding lfinite_eq_range_llist_of by blast
    have "lfinite (llist_of xs)" by simp
    hence "lfinite xs'" unfolding `llist_of xs = lappend zs xs'` by simp
    then obtain XS' where [simp]: "xs' = llist_of XS'"
      unfolding lfinite_eq_range_llist_of by blast
    from `llist_of xs = lappend zs xs'` have [simp]: "xs = zs' @ XS'" by simp
    have "lfinite (llist_of ys)" by simp
    hence "lfinite ys'" unfolding `llist_of ys = lappend zs (LCons y ys')` by simp
    then obtain YS' where [simp]: "ys' = llist_of YS'"
      unfolding lfinite_eq_range_llist_of by blast
    from `llist_of ys = lappend zs (LCons y ys')` have [simp]: "ys = zs' @ y # YS'"
      by(auto simp add: llist_of.simps(2)[symmetric] simp del: llist_of.simps(2))
    have "(\<exists>a ys'. ys = xs @ a # ys') \<or>
          (\<exists>zs a b. r a b \<and> (\<exists>xs'. xs = zs @ a # xs') \<and> (\<exists>ys'. ys = zs @ b # ys'))"
      (is "?A \<or> ?B")
    proof(cases xs')
      case LNil thus ?thesis by auto
    next
      case (LCons x xs'')
      with `xs' = LNil \<or> r (lhd xs') y`
      have "r (lhd xs') y" by(auto simp add: llist_of_eq_LCons_conv)
      with LCons have ?B by(auto simp add: llist_of_eq_LCons_conv) fastsimp
      thus ?thesis ..
    qed
    hence "(xs, ys) \<in> {(x, y). \<exists>a v. y = x @ a # v \<or>
                                    (\<exists>u a b v w. (a, b) \<in> (\<lambda>(x, y). r x y) \<and> 
                                                 x = u @ a # v \<and> y = u @ b # w)}"
      by(simp add: split_def)(simp add: mem_def) }
  with `?lhs` show ?rhs
    unfolding lexord_def llexord_conv llist_of_inj by blast
next
  assume "?rhs"
  thus ?lhs
  proof
    assume "xs = ys" thus ?thesis by simp
  next
    assume "(xs, ys) \<in> lexord (\<lambda>(x, y). r x y)"
    moreover def xs' == "llist_of xs"
    moreover def ys' == "llist_of ys"
    ultimately have "(xs', ys') \<in> 
                  {(llist_of xs, llist_of ys)
                   |xs ys. (xs, ys) \<in> lexord (\<lambda>(x, y). r x y)}"
      by blast
    thus "llexord r xs' ys'"
    proof(coinduct)
      case (llexord xs' ys')
      then obtain xs ys where [simp]: "xs' = llist_of xs" "ys' = llist_of ys"
	and "(xs, ys) \<in> lexord (\<lambda>(x, y). r x y)" by blast
      thus ?case by(cases xs, simp)(cases ys, auto, simp_all add: mem_def)
    qed
  qed
qed

subsection {* The filter functional on lazy lists: @{term "lfilter"} *}

text {* basic laws about @{text findRel} *}

inductive_cases findRel_LConsE [elim!]:
  "(LCons x l, l'') \<in> findRel p"

lemma findRel_functional:
  assumes "(l,l') \<in> findRel p"
  and "(l, l''): findRel p"
  shows "l'' = l'"
using assms by induct auto

lemma findRel_imp_LCons:
  "(l,l'): findRel p ==> \<exists>x l''. l' = LCons x l'' & p x"
by (erule findRel.induct, auto)

lemma findRel_LNil [elim!]:
  "(LNil,l): findRel p ==> R"
by (blast elim: findRel.cases)

lemma find_eq_LConsD: 
  assumes "find P ys = LCons x ys'"
  shows "(ys, LCons x ys') \<in> findRel P"
proof -
  have "(ys, find P ys) \<in> findRel P \<or> (find P ys = LNil \<and> ys \<notin> Domain (findRel P))"
    unfolding find_def by(rule someI_ex)(auto)
  with assms show ?thesis by auto
qed

lemma lmap_LCons_findRel:
  assumes "(lmap f l, LCons x l') \<in> findRel p"
  shows "\<exists>y l''. x = f y & l' = lmap f l'' & (l, LCons y l'') \<in> findRel(%x. p(f x))"
using assms
apply(induct lx\<equiv>"lmap f l" ly\<equiv>"LCons x l'" arbitrary: l)
apply simp_all
apply (blast dest!: lmap_eq_LCons[OF sym])+
done

lemma findRel_conj:
  assumes "(l,LCons x l'') \<in> findRel q"
  shows "p x \<Longrightarrow> (l,LCons x l'') \<in> findRel (%x. p x & q x)"
using assms by(induct l l'\<equiv>"LCons x l''" rule: findRel.induct) auto

lemma findRel_not_conj_Domain:
  assumes "(l,l'') \<in> findRel (%x. p x & q x)"
  and "(l, LCons x l') \<in> findRel q" "~ p x"
  shows "l' \<in> Domain (findRel (%x. p x & q x))"
using assms by induct auto

lemma findRel_conj2:
  assumes "(l,LCons x lx) \<in> findRel q"
  and "(lx,lz) \<in> findRel(%x. p x & q x)" "~ p x"
  shows "(l,lz) \<in> findRel (%x. p x & q x)"
using assms by(induct l lxx\<equiv>"LCons x lx") auto

lemma findRel_prefix:
  assumes "(xs, ys) \<in> findRel P"
  shows "\<exists>zs. xs = lappend zs ys \<and> lfinite zs \<and> (\<forall>z\<in>lset zs. \<not> P z)"
using assms
proof induct
  case (found x xs)
  have "LCons x xs = lappend LNil (LCons x xs)" by simp
  thus ?case by fastsimp
next
  case (seek x xs xs')
  from `\<exists>zs. xs = lappend zs xs' \<and> lfinite zs \<and> (\<forall>z\<in>lset zs. \<not> P z)` obtain zs
    where "xs = lappend zs xs'" "lfinite zs" "\<forall>z\<in>lset zs. \<not> P z" by blast
  with `\<not> P x` have "LCons x xs = lappend (LCons x zs) xs'"
    "\<forall>z\<in>lset (LCons x zs). \<not> P z" "lfinite (LCons x zs)" by auto
  thus ?case by blast
qed

text {* Properties of @{text "Domain (findRel p)"} *}

lemma LCons_Domain_findRel [simp]:
  "LCons x l \<in> Domain(findRel p) = (p x | l \<in> Domain(findRel p))"
by auto

lemma Domain_findRel_iff:
  "(l \<in> Domain (findRel p)) = (\<exists>x l'. (l, LCons x l') \<in> findRel p &  p x)" 
by (blast dest: findRel_imp_LCons) 

lemma Domain_findRel_mono:
  "[| !!x. p x ==> q x |] ==> Domain (findRel p) <= Domain (findRel q)"
apply clarify
apply (erule findRel.induct, blast+)
done

lemma findRel_lmap_Domain:
  assumes "(l,l') \<in> findRel (\<lambda>x. p (f x))"
  shows "lmap f l \<in> Domain (findRel p)"
using assms by induct auto

text {* @{text find}: basic equations *}

lemma find_LNil [simp]: "find p LNil = LNil"
by (unfold find_def, blast)

lemma findRel_imp_find [simp]: "(l,l') \<in> findRel p ==> find p l = l'"
unfolding find_def by (blast dest: findRel_functional)

lemma find_LCons_found: "p x ==> find p (LCons x l) = LCons x l"
by (blast intro: findRel_imp_find)

lemma diverge_find_LNil [simp]: "l ~: Domain(findRel p) ==> find p l = LNil"
by (unfold find_def, blast)

lemma find_LCons_seek: "~ (p x) ==> find p (LCons x l) = find p l"
by(cases "LCons x l \<in> Domain (findRel p) ")(fastsimp intro: findRel_imp_find)+

lemma find_LCons [simp]:
     "find p (LCons x l) = (if p x then LCons x l else find p l)"
by (simp add: find_LCons_seek find_LCons_found)

text {* @{text lfilter}: basic equations *}

lemma lfilter_LNil [simp]: "lfilter p LNil = LNil"
unfolding lfilter_def by(simp add: llist_corec)

lemma diverge_lfilter_LNil [simp]:
  "l ~: Domain(findRel p) ==> lfilter p l = LNil"
unfolding lfilter_def by(simp add: llist_corec)

lemma lfilter_LCons_found:
  "p x ==> lfilter p (LCons x l) = LCons x (lfilter p l)"
unfolding lfilter_def by(simp add: llist_corec)

lemma findRel_imp_lfilter [simp]:
  "(l, LCons x l') \<in> findRel p ==> lfilter p l = LCons x (lfilter p l')"
unfolding lfilter_def by(simp add: llist_corec)

lemma lfilter_LCons_seek: "~ (p x) ==> lfilter p (LCons x l) = lfilter p l"
unfolding lfilter_def by(simp add: llist_corec)

lemma lfilter_LCons [simp]:
  "lfilter p (LCons x l) =
  (if p x then LCons x (lfilter p l) else lfilter p l)"
by (simp add: lfilter_LCons_found lfilter_LCons_seek)

lemma lfilter_eq_LNil:
  "lfilter p l = LNil ==> l ~: Domain(findRel p)" 
by (auto iff: Domain_findRel_iff)

lemma lfilter_eq_LCons:
  "lfilter p l = LCons x l' \<Longrightarrow>
   \<exists>l''. l' = lfilter p l'' & (l, LCons x l'') \<in> findRel p"
unfolding lfilter_def
by(cases "l \<in> Domain (findRel p)")
  (auto iff: Domain_findRel_iff simp add: llist_corec)

lemma lfilter_cases:
  "lfilter p l = LNil |
   (\<exists>y l'. lfilter p l = LCons y (lfilter p l') & p y)"
by (cases "l \<in> Domain (findRel p) ") (auto iff: Domain_findRel_iff)

lemma lfilter_K_True: "lfilter (%x. True) l = l"
by (rule llist_fun_equalityI[where l=l], simp_all)

lemma lfilter_idem: "lfilter p (lfilter p l) = lfilter p l"
proof(coinduct l rule: llist_fun_equalityI)
  case LNil thus ?case by simp
next
  case (LCons x l)
  show ?case
  proof(cases "p x")
    case True hence ?EqLCons by auto thus ?thesis ..
  next
    case False thus ?thesis
      by(cases "lfilter p l")(auto dest: lfilter_eq_LCons findRel_imp_LCons)
  qed
qed

lemma findRel_lfilter_Domain_conj:
  assumes "(lfilter q l,ly) \<in> findRel p"
  shows "l \<in> Domain (findRel(%x. p x & q x))"
using assms
proof(induct lx\<equiv>"lfilter q l" ly arbitrary: l)
  case found thus ?case 
    by(auto dest!: sym[THEN lfilter_eq_LCons] intro: findRel_conj)
next
  case seek thus ?case
    by(fastsimp intro: findRel_conj2 dest: sym[THEN lfilter_eq_LCons])
qed

lemma findRel_conj_lfilter [rule_format]:
     "(l,LCons y l') \<in> findRel(%x. p x & q x)  
      ==> (lfilter q l, LCons y (lfilter q l')) \<in> findRel p"
by(induct l l''\<equiv>"LCons y l'" rule: findRel.induct) auto

lemma lfilter_conj_lemma:
 "(lfilter p (lfilter q l), lfilter (\<lambda>x. p x \<and> q x) l) = (LNil, LNil) \<or>
  (\<exists>l1 l2 a. (lfilter p (lfilter q l), lfilter (\<lambda>x. p x \<and> q x) l) = (LCons a l1, LCons a l2) \<and>
             ((l1, l2) \<in> {(lfilter p (lfilter q u), lfilter (\<lambda>x. p x \<and> q x) u) |u. True} \<or>
             l1 = l2))"
proof(cases "l \<in> Domain (findRel q)")
  case False
  hence "l \<notin> Domain (findRel (\<lambda>x. p x \<and> q x))"
    by (blast intro: rev_subsetD [OF _ Domain_findRel_mono])
  hence "(lfilter p (lfilter q l), lfilter (\<lambda>x. p x \<and> q x) l) = (LNil, LNil)" 
    using False by simp
  thus ?thesis ..
next
  case True
  then obtain x l' where l': "(l, LCons x l') \<in> findRel q" and qx: "q x"
    unfolding Domain_findRel_iff by blast
  show ?thesis
  proof(cases "p x")
    case True with l' show ?thesis
      by(auto simp add: findRel_conj [THEN findRel_imp_lfilter])
  next
    case False show ?thesis
    proof(cases "l' \<in> Domain (findRel (%x. p x & q x))")
      case False
      with `\<not> p x` l' have "l \<notin> Domain (findRel (%x. p x & q x))"
	by (blast intro: findRel_not_conj_Domain)
      moreover hence "lfilter q l ~: Domain (findRel p)"
	by(blast intro: findRel_lfilter_Domain_conj)
      ultimately show ?thesis by simp
    next
      case True
      then obtain x' l'' where l'': "(l', LCons x' l'') \<in> findRel (\<lambda>x. p x \<and> q x)" 
	and px: "p x'" and qx: "q x'" unfolding Domain_findRel_iff by blast
      from l'' have "(l, LCons x' l'') \<in> findRel (%x. p x & q x)"
	using l' `\<not> p x` by(blast intro: findRel_conj2)
      moreover from l'' have "(lfilter q l', LCons x' (lfilter q l'')) \<in> findRel p" 
	by(rule findRel_conj_lfilter)
      ultimately show ?thesis using l'' l' `\<not> p x` by auto
    qed
  qed
qed

lemma lfilter_lfilter: "lfilter p (lfilter q l) = lfilter (%x. p x & q x) l"
proof(coinduct l rule: llist_fun_equalityI)
  case LNil thus ?case by simp
next
  case (LCons x l)
  show ?case
  proof(cases "p x \<and> q x")
    case True hence ?EqLCons by auto
    thus ?thesis ..
  next
    case False
    have "(lfilter p (lfilter q l), lfilter (\<lambda>x. p x \<and> q x) l) = (LNil, LNil) \<or>
          (\<exists>l1 l2 a. (lfilter p (lfilter q l), lfilter (\<lambda>x. p x \<and> q x) l) = (LCons a l1, LCons a l2) \<and>
                     ((l1, l2) \<in> {(lfilter p (lfilter q u), lfilter (\<lambda>x. p x \<and> q x) u) |u. True} \<or>
                     l1 = l2))" by(rule lfilter_conj_lemma)
    thus ?thesis by auto
  qed
qed

lemmas lfilter_conj = lfilter_lfilter

lemma lfilter_lmap: "lfilter p (lmap f l) = lmap f (lfilter (p o f) l)"
proof(coinduct l rule: llist_fun_equalityI)
  case LNil thus ?case by simp
next
  case (LCons x l)
  show ?case
  proof(cases "p (f x)")
    case True thus ?thesis by auto
  next
    case False
    show ?thesis
    proof(cases "lmap f l \<in> Domain (findRel p)")
      case True
      then obtain x' l' where l': "(lmap f l, LCons x' l') \<in> (findRel p)"
        and px': "p x'" unfolding Domain_findRel_iff by blast
      with lmap_LCons_findRel[OF l'] False have ?EqLCons by fastsimp
      thus ?thesis ..
    next
      case False
      hence "l \<notin> Domain (findRel (\<lambda>x. p (f x)))"
	by (blast intro: findRel_lmap_Domain)
      thus ?thesis using `\<not> p (f x)` False by simp
    qed
  qed
qed

lemma lfilter_llist_of [simp]:
  "lfilter P (llist_of xs) = llist_of (filter P xs)"
by(induct xs) simp_all

lemma lfilter_lappend_lfinite [simp]:
  "lfinite xs \<Longrightarrow> lfilter P (lappend xs ys) = lappend (lfilter P xs) (lfilter P ys)"
by(induct rule: lfinite.induct) auto

lemma lfilter_code [code]:
  "lfilter P LNil = LNil"
  "lfilter P (LCons x xs) = (if P x then LCons x (lfilter P xs) else lfilter P xs)"
by simp_all

lemma lfilter_False:
  assumes "\<forall>x\<in>lset xs. \<not> P x"
  shows "lfilter P xs = LNil"
proof -
  have "xs \<notin> Domain (findRel P)"
  proof
    assume "xs \<in> Domain (findRel P)"
    then obtain ys where "(xs, ys) \<in> findRel P" by blast
    thus False using `\<forall>x\<in>lset xs. \<not> P x` by induct auto
  qed
  thus ?thesis by(rule diverge_lfilter_LNil)
qed

lemma lfilter_empty_conv: "lfilter P xs = LNil \<longleftrightarrow> (\<forall>x\<in>lset xs. \<not> P x)"
proof
  assume eq: "lfilter P xs = LNil"
  show "\<forall>x\<in>lset xs. \<not> P x"
  proof
    fix x
    assume "x \<in> lset xs"
    from split_llist[OF this] obtain ys zs
      where "xs = lappend ys (LCons x zs)" "lfinite ys" by blast
    with eq show "\<not> P x" by(simp split: split_if_asm)
  qed
qed(rule lfilter_False)

lemma lfilter_eq_LConsD:
  assumes "lfilter P ys = LCons x xs"
  shows "\<exists>us vs. ys = lappend us (LCons x vs) \<and> lfinite us \<and>
                      (\<forall>u\<in>lset us. \<not> P u) \<and> P x \<and> xs = lfilter P vs"
proof -
  from lfilter_eq_LCons[OF assms] obtain ys' 
    where xs: "xs = lfilter P ys'"
    and ys': "(ys, LCons x ys') \<in> findRel P" by blast
  from findRel_prefix[OF ys'] obtain us
    where "ys = lappend us (LCons x ys')"
    and "\<forall>u\<in>lset us. \<not> P u" "lfinite us" by blast
  moreover from assms lfilter_cases[of P ys] have "P x" by simp
  ultimately show ?thesis using xs by blast
qed

lemma lfilter_cong:
  assumes xsys: "xs = ys"
  and set: "\<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x"
  shows "lfilter P xs = lfilter Q ys"
proof -
  from set xsys
  have "(lfilter P xs, lfilter Q ys) \<in> 
       {(lfilter P ys, lfilter Q ys)|ys. \<forall>y \<in> lset ys. P y = Q y}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain ys where q: "q = (lfilter P ys, lfilter Q ys)"
      and set: "\<And>y. y \<in> lset ys \<Longrightarrow> P y = Q y" by blast
    show ?case
    proof(cases "lfilter P ys")
      case LNil
      with set have "lfilter Q ys = LNil" by(simp add: lfilter_empty_conv)
      with LNil have ?EqLNil unfolding q by simp
      thus ?thesis ..
    next
      case (LCons x xs)
      from lfilter_eq_LConsD[OF this] obtain us vs
	where ys: "ys = lappend us (LCons x vs)" "lfinite us"
	and us: "\<forall>u\<in>lset us. \<not> P u" and x: "P x" and xs: "xs = lfilter P vs" by blast
      from ys x set have "Q x" by auto
      moreover from us ys set have "\<forall>u\<in>lset us. \<not> Q u" by auto
      hence "lfilter Q us = LNil" by(rule lfilter_False)
      ultimately have "lfilter Q ys = LCons x (lfilter Q vs)"
	unfolding ys using `lfinite us` by simp
      moreover from ys set have "\<forall>v\<in>lset vs. P v = Q v" by auto
      ultimately have ?EqLCons using LCons xs unfolding q by auto
      thus ?thesis ..
    qed
  qed
qed

lemma lfilter_eq_lappend_lfiniteD:
  assumes "lfilter P xs = lappend ys zs" and "lfinite ys"
  shows "\<exists>us vs. xs = lappend us vs \<and> lfinite us \<and>
                      ys = lfilter P us \<and> zs = lfilter P vs"
using `lfinite ys` `lfilter P xs = lappend ys zs`
proof(induct arbitrary: xs zs)
  case lfinite_LNil
  hence "xs = lappend LNil xs" "LNil = lfilter P LNil" "zs = lfilter P xs"
    by simp_all
  thus ?case by blast
next
  case (lfinite_LConsI ys y)
  note IH = `\<And>xs zs. lfilter P xs = lappend ys zs \<Longrightarrow>
            \<exists>us vs. xs = lappend us vs \<and> lfinite us \<and>
                    ys = lfilter P us \<and> zs = lfilter P vs`
  from `lfilter P xs = lappend (LCons y ys) zs`
  have "lfilter P xs = LCons y (lappend ys zs)" by simp
  from lfilter_eq_LConsD[OF this] obtain us vs
    where xs: "xs = lappend us (LCons y vs)" "lfinite us" 
              "P y" "\<forall>u\<in>lset us. \<not> P u"
    and vs: "lfilter P vs = lappend ys zs" by auto
  from IH[OF vs] obtain us' vs' where "vs = lappend us' vs'" "lfinite us'"
    and "ys = lfilter P us'" "zs = lfilter P vs'" by blast
  with xs show ?case
    by(fastsimp simp add: lappend_snocL1_conv_LCons2[symmetric, where ys="lappend us' vs'"]
                          lappend_assoc[symmetric] lfilter_False)
qed

lemma llength_lfilter_ile:
  "llength (lfilter P xs) \<le> llength xs"
proof -
  have "(llength (lfilter P xs), llength xs) \<in>
        {(llength (lfilter P xs), llength xs)|xs. True}" by blast
  thus ?thesis
  proof(coinduct rule: inat_leI)
    case (Leinat m n)
    then obtain xs where m: "m = llength (lfilter P xs)"
      and n: "n = llength xs" by auto
    show ?case
    proof(cases "xs \<in> Domain (findRel P)")
      case False
      hence "find P xs = LNil" by simp
      with m have ?zero by(auto simp add: lfilter_def llist_corec)
      thus ?thesis ..
    next
      case True
      then obtain ys where "(xs, ys) \<in> findRel P" by auto
      moreover then obtain y ys' where "ys = LCons y ys'"
        by(auto dest!: findRel_imp_LCons)
      ultimately have "find P xs = LCons y ys'" by(simp)
      hence "(xs, LCons y ys') \<in> findRel P" by(rule find_eq_LConsD)
      hence "lfilter P xs = LCons y (lfilter P ys')" by simp
      moreover from lfilter_eq_LConsD[OF this]
      obtain us vs where xs: "xs = lappend us (LCons y vs)"
	and "lfilter P ys' = lfilter P vs" "P y" "lfinite us"
	and "\<And>u. u \<in> lset us \<Longrightarrow> \<not> P u" by blast
      ultimately have "m = iSuc (llength (lfilter P vs))" using m by simp
      moreover from `lfinite us` obtain k where "llength us = Fin k"
	by(auto dest: lfinite_llength_Fin)
      with xs n have "n = llength vs + Fin (Suc k)"
	by(auto simp add: iSuc_def add_ac one_inat_def split: inat.split)
      ultimately have ?iSuc by auto
      thus ?thesis ..
    qed
  qed
qed

lemma lfinite_lfilter [simp]:
  "lfinite (lfilter P xs) \<longleftrightarrow> 
   lfinite xs \<or> finite {n. Fin n < llength xs \<and> P (lnth xs n)}"
proof
  assume "lfinite (lfilter P xs)"
  { assume "\<not> lfinite xs"
    with `lfinite (lfilter P xs)`
    have "finite {n. Fin n < llength xs \<and> P (lnth xs n)}"
    proof(induct ys\<equiv>"lfilter P xs" arbitrary: xs)
      case lfinite_LNil
      from `LNil = lfilter P xs`[symmetric] `\<not> lfinite xs`
      have "\<forall>x\<in>lset xs. \<not> P x" by(auto simp add: lfilter_empty_conv)
      hence eq: "{n. Fin n < llength xs \<and> P (lnth xs n)} = {}" 
        by(auto simp add: lset_def)
      show ?case unfolding eq ..
    next
      case (lfinite_LConsI ys x)
      from lfilter_eq_LConsD[OF `LCons x ys = lfilter P xs`[symmetric]]
      obtain us vs where "xs = lappend us (LCons x vs)" "lfinite us"
	"\<forall>u\<in>lset us. \<not> P u" "P x" "ys = lfilter P vs" by blast
      from `lfinite us` obtain us' where "us = llist_of us'"
        unfolding lfinite_eq_range_llist_of by blast 
      def k \<equiv> "length us'"
      from `\<not> lfinite xs` `xs = lappend us (LCons x vs)` `lfinite us`
      have "\<not> lfinite vs" by simp
      with `ys = lfilter P vs`
      have "finite {n. Fin n < llength vs \<and> P (lnth vs n)}"
	by(rule lfinite_LConsI)
      hence "finite ((\<lambda>m. Suc (m + k)) ` {n. Fin n < llength vs \<and> P (lnth vs n)})"
        by(rule finite_imageI)
      moreover {
	have "{n. n \<le> k \<and> P (lnth xs n)} \<subseteq> {n. n \<le> k}" by auto
	moreover have "finite {n. n \<le> k}" by auto
	ultimately have "finite {n. n \<le> k \<and> P (lnth xs n)}" by(rule finite_subset) }
      ultimately have "finite ((\<lambda>m. Suc (m + k)) ` {n. Fin n < llength vs \<and> P (lnth vs n)} \<union>
                            {n. n \<le> k \<and> P (lnth xs n)})"
        by simp
      moreover
      have "(\<lambda>m. Suc (m + k)) ` {n. Fin n < llength vs \<and> P (lnth vs n)} \<union> 
            {n. n \<le> k \<and> P (lnth xs n)} =
            {n. Fin n < llength xs \<and> P (lnth xs n)}"
	unfolding k_def using `xs = lappend us (LCons x vs)` `us = llist_of us'`
	by(auto simp add: lnth_lappend_llist_of iSuc_def lnth_LCons split: inat.split)
          (force split: nat.splits)+
      ultimately show ?case by(simp)
    qed }
  thus "lfinite xs \<or> finite {n. Fin n < llength xs \<and> P (lnth xs n)}" by blast
next
  assume "lfinite xs \<or> finite {n. Fin n < llength xs \<and> P (lnth xs n)}"
  moreover {
    assume "lfinite xs"
    with llength_lfilter_ile[of P xs] have "lfinite (lfilter P xs)"
      by(auto simp add: lfinite_eq_range_llist_of)
  } moreover {
    assume nfin: "\<not> lfinite xs"
    hence len: "llength xs = Infty" by(rule not_lfinite_llength)
    assume fin: "finite {n. Fin n < llength xs \<and> P (lnth xs n)}"
    have "lfinite (lfilter P xs)"
    proof(cases "P = (\<lambda>x. True)")
      case True with fin len have False by simp
      thus ?thesis ..
    next
      case False
      hence "\<not> All P" unfolding All_def .
      then obtain a where "\<not> P a" by auto
      from fin len show ?thesis
      proof(induct A\<equiv>"{n. Fin n < llength xs \<and> P (lnth xs n)}"
                  arbitrary: xs rule: finite_induct)
	case empty
	hence "lfilter P xs = LNil"
          by(simp add: lfilter_empty_conv lset_def)
	thus ?case by simp
      next
	case (insert n A)
	note [simp] = `llength xs = \<infinity>`
	from `insert n A = {n. Fin n < llength xs \<and> P (lnth xs n)}` `n \<notin> A`
	have A: "A = {m. m \<noteq> n \<and> Fin m < llength xs \<and> P (lnth xs m)}" by auto
	let ?xs = "lappend (ltake (Fin n) xs) (LCons a (ldropn (Suc n) xs))"
	have xs: "xs = lappend (ltake (Fin n) xs) (ldrop (Fin n) xs)"
          by(simp only: lappend_ltake_ldrop)
	from `llength xs = \<infinity>` have "\<not> lfinite xs"
          by(auto dest: lfinite_llength_Fin)
	hence "\<not> lfinite (ldropn n xs)" by(subst xs) simp
	then obtain X XS where "ldropn n xs = LCons X XS"
          by(cases "ldropn n xs") auto
	moreover have "lnth (ldropn n xs) 0 = lnth xs n"
          using `llength xs = \<infinity>` by(simp del: lnth.simps(1))
	moreover have "ltl (ldropn n xs) = ldropn (Suc n) xs"
	  by(cases xs)(simp_all add: ltl_ldropn del: ldropn_LCons)
	ultimately have "ldropn n xs = LCons (lnth xs n) (ldropn (Suc n) xs)" by simp
	hence xs: "xs = lappend (ltake (Fin n) xs) (LCons (lnth xs n) (ldropn (Suc n) xs))"
          using xs by simp
	have "llength (ldropn (Suc n) xs) = \<infinity>"
	  by(rule not_lfinite_llength)(simp add: `\<not> lfinite xs`)
	hence [simp]: "llength ?xs = \<infinity>" using `llength xs = \<infinity>` xs by(simp)
	moreover {
	  fix m
	  { assume "m \<noteq> n"
	    have "lnth ?xs m = lnth xs m"
	    proof(cases "m < n")
	      case True thus ?thesis by(simp add: lnth_lappend1 lnth_ltake)
	    next
	      case False
	      with `m \<noteq> n` have "n < m" by(simp add: not_less_iff_gr_or_eq)
	      moreover then obtain k where "m - n = Suc k" by(cases "m - n") auto
	      moreover hence "Suc (k + n) = m" by auto
	      ultimately show ?thesis by(auto simp add: lnth_lappend2)
	    qed }
	  moreover from `insert n A = {n. Fin n < llength xs \<and> P (lnth xs n)}`
	  have "P (lnth xs n)" by auto
	  ultimately have "P (lnth xs m) \<longleftrightarrow> P (lnth ?xs m) \<or> m = n"
            by(cases "m = n") simp_all }
	hence "A = {n. Fin n < llength xs \<and> P (lnth ?xs n)}"
	  unfolding A using `\<not> P a` by(auto simp add: lnth_lappend2)
	hence "A = {n. Fin n < llength ?xs \<and> P (lnth ?xs n)}"
	  unfolding `llength ?xs = \<infinity>` `llength xs = \<infinity>` . 
	then have "lfinite (lfilter P ?xs)" using `llength ?xs = \<infinity>` by(rule insert)
	thus ?case by(subst xs)(simp split: split_if_asm)
      qed
    qed }
  ultimately show "lfinite (lfilter P xs)" by blast
qed

lemma lset_lfilter [simp]: "lset (lfilter P xs) = {x \<in> lset xs. P x}"
proof
  show "lset (lfilter P xs) \<subseteq> {x \<in> lset xs. P x}"
  proof
    fix x
    assume "x \<in> lset (lfilter P xs)"
    from split_llist[OF this] obtain ys zs
      where "lfilter P xs = lappend ys (LCons x zs)" "lfinite ys" by blast
    from lfilter_eq_lappend_lfiniteD[OF this] obtain us vs
      where "xs = lappend us vs" "ys = lfilter P us" "lfinite us"
      "lfilter P vs = LCons x zs" by auto
    thus "x \<in> {x \<in> lset xs. P x}" by(auto dest!: lfilter_eq_LConsD)
  qed
next
  show "{x \<in> lset xs. P x} \<subseteq> lset (lfilter P xs)"
  proof
    fix x
    assume "x \<in> {x \<in> lset xs. P x}"
    hence "x \<in> lset xs" "P x" by(auto)
    from split_llist[OF `x \<in> lset xs`] obtain ys zs
      where "xs = lappend ys (LCons x zs)" "lfinite ys" by blast
    with `P x` show "x \<in> lset (lfilter P xs)" by(simp add: lset_lappend)
  qed
qed


subsection {* Concatenating all lazy lists in a lazy list: @{term "lconcat"} *}

lemma lconcat_LNil [simp, code]: "lconcat LNil = LNil"
by(simp add: lconcat_def llist_corec)

lemma lconcat_LCons [simp, code]:
  "lconcat (LCons ys xss) = lappend ys (lconcat xss)"
proof(cases "ys = LNil")
  case True thus ?thesis by(simp add: lconcat_def)
next
  case False
  hence "(lconcat (LCons ys xss), lappend ys (lconcat xss)) \<in> 
        {(lconcat (LCons ys xss), lappend ys (lconcat xss))|ys. ys \<noteq> LNil}"
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain ys
      where q: "q = (lconcat (LCons ys xss), lappend ys (lconcat xss))"
      and "ys \<noteq> LNil" by blast
    then obtain y ys' where ys: "ys = LCons y ys'"
      by(auto simp add: neq_LNil_conv)
    have "lconcat (LCons (LCons y ys') xss) = LCons y (lconcat (LCons ys' xss))"
      by(auto simp add: lconcat_def llist_corec)
    moreover {
      assume "ys' = LNil"
      hence "lconcat (LCons ys' xss) = lappend ys' (lconcat xss)"
        by(simp add: lconcat_def) 
    } ultimately have ?EqLCons unfolding q ys
      by(cases "ys' = LNil") auto
    thus ?case ..
  qed
qed

lemma lconcat_llist_of:
  "lconcat (llist_of (map llist_of xs)) = llist_of (concat xs)"
by(induct xs) simp_all

lemma lconcat_eq_LNil: "lconcat xss = LNil \<longleftrightarrow> lset xss \<subseteq> {LNil}"
proof
  assume "lconcat xss = LNil"
  hence "lfilter (\<lambda>xs. xs \<noteq> LNil) xss = LNil"
    by(cases "lfilter (\<lambda>xs. xs \<noteq> LNil) xss = LNil")
      (auto simp add: lconcat_def llist_corec neq_LNil_conv split: option.split_asm)
  thus "lset xss \<subseteq> {LNil}" unfolding lfilter_empty_conv by auto
next
  assume "lset xss \<subseteq> {LNil}"
  hence "lfilter (\<lambda>xs. xs \<noteq> LNil) xss = LNil"
    unfolding lfilter_empty_conv by auto
  thus "lconcat xss = LNil" by(simp add: lconcat_def llist_corec)
qed

lemma lmap_lconcat:
  fixes xss :: "'a llist llist"
  shows "lmap f (lconcat xss) = lconcat (lmap (lmap f) xss)"
proof -
  { fix xss :: "'a llist llist"
    assume "LNil \<notin> lset xss"
    hence "(lmap f (lconcat xss), lconcat (lmap (lmap f) xss)) \<in>
          {(lmap f (lconcat xss), lconcat (lmap (lmap f) xss))|xss. LNil \<notin> lset xss}"
      by blast
    hence "lmap f (lconcat xss) = lconcat (lmap (lmap f) xss)"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain xss where q: "q = (lmap f (lconcat xss), lconcat (lmap (lmap f) xss))"
	and notLNil: "LNil \<notin> lset xss" by blast
      show ?case
      proof(cases xss)
	case LNil
	with q have ?EqLNil by simp
	thus ?thesis ..
      next
	case (LCons xs xss')
	with notLNil have "xs \<noteq> LNil" by auto
	then obtain x xs' where xs: "xs = LCons x xs'"
	  by(auto simp add: neq_LNil_conv)
	have ?EqLCons
	proof(cases "xs' = LNil")
	  case True
	  thus ?thesis using LCons q notLNil xs by fastsimp
	next
	  case False
	  thus ?thesis using LCons q notLNil xs
	    by(auto)(rule_tac x="LCons xs' xss'" in exI, simp)
	qed
	thus ?thesis ..
      qed
    qed }
  note eq = this
  have "lmap f (lconcat (lfilter (\<lambda>xs. xs \<noteq> LNil) xss)) =
         lconcat (lmap (lmap f) (lfilter (\<lambda>xs. xs \<noteq> LNil) xss))"
    by(rule eq) simp
  also have "lconcat (lfilter (\<lambda>xs. xs \<noteq> LNil) xss) = lconcat xss"
    unfolding lconcat_def lfilter_idem ..
  also have "lconcat (lmap (lmap f) (lfilter (\<lambda>xs. xs \<noteq> LNil) xss)) =
            lconcat (lmap (lmap f) xss)"
    unfolding lconcat_def lfilter_lmap lfilter_conj by(simp add: o_def)
  finally show ?thesis .
qed


subsection {* Sublist view of a lazy list: @{term "lsublist"} *}

lemma lsublist_empty [simp]: "lsublist xs {} = LNil"
by(auto simp add: lsublist_def split_def lfilter_empty_conv)

lemma lsublist_LNil [simp]: "lsublist LNil A = LNil"
by(simp add: lsublist_def)

lemma lsublist_LCons:
  "lsublist (LCons x xs) A = 
  (if 0 \<in> A then LCons x (lsublist xs {n. Suc n \<in> A}) else lsublist xs {n. Suc n \<in> A})"
proof -
  let ?it = "iterates Suc"
  let ?f = "\<lambda>(x, y). (x, Suc y)"
  { fix n
    have "(lzip xs (?it (Suc n)), lmap ?f (lzip xs (?it n))) \<in>
         {(lzip xs (?it (Suc n)), lmap ?f (lzip xs (?it n)))|xs n. True}" 
      by blast
    hence "lzip xs (?it (Suc n)) = lmap ?f (lzip xs (?it n))"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain n xs
	where q: "q = (lzip xs (?it (Suc n)), lmap ?f (lzip xs (?it n)))" 
        by blast
      show ?case
      proof(cases xs)
	case LNil hence ?EqLNil unfolding q by simp
	thus ?thesis ..
      next
	case LCons hence ?EqLCons unfolding q
	  by(subst (1 2) iterates) auto
	thus ?thesis ..
      qed
    qed
    hence "lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (?it (Suc n)))) =
           lmap fst (lfilter (\<lambda>(x, y). Suc y \<in> A) (lzip xs (?it n)))"
      by(simp add: lfilter_lmap lmap_compose[symmetric] o_def split_def 
              del: lmap_compose) }
  thus ?thesis
    by(auto simp add: lsublist_def)(subst iterates, simp)+
qed

lemma lset_lsublist:
  "lset (lsublist xs I) = {lnth xs i|i. Fin i<llength xs \<and> i \<in> I}"
apply(auto simp add: lsublist_def lset_lzip)
apply(rule_tac x="(lnth xs i, i)" in image_eqI)
apply auto
done

lemma lset_lsublist_subset: "lset (lsublist xs I) \<subseteq> lset xs"
by(auto simp add: lset_lsublist)(simp add: lset_def)

lemma lsublist_singleton [simp]:
  "lsublist (LCons x LNil) A = (if 0 : A then LCons x LNil else LNil)"
by (simp add: lsublist_LCons)

lemma lsublist_upt_eq_ltake [simp]:
  "lsublist xs {..<n} = ltake (Fin n) xs"
apply(rule sym)
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_inat_def[symmetric])
next
  case (Suc n)
  thus ?case 
    by(cases xs)(simp_all add: iSuc_Fin[symmetric] lsublist_LCons lessThan_def)
qed

lemma lsublist_llist_of [simp]:
  "lsublist (llist_of xs) A = llist_of (sublist xs A)"
by(induct xs arbitrary: A)(simp_all add: lsublist_LCons sublist_Cons)

lemma llength_lsublist_ile: "llength (lsublist xs A) \<le> llength xs"
proof -
  have "llength (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (iterates Suc 0))) \<le>
        llength (lzip xs (iterates Suc 0))"
    by(rule llength_lfilter_ile)
  thus ?thesis by(simp add: lsublist_def llength_lzip)
qed

lemma lsublist_lmap [simp]:
  "lsublist (lmap f xs) A = lmap f (lsublist xs A)"
by(simp add: lsublist_def lzip_lmap1 lmap_compose[symmetric]
             lfilter_lmap o_def split_def
        del: lmap_compose)

lemma lfilter_conv_lsublist: 
  "lfilter P xs = lsublist xs {n. Fin n < llength xs \<and> P (lnth xs n)}"
proof -
  have "lsublist xs {n. Fin n < llength xs \<and> P (lnth xs n)} =
        lmap fst (lfilter (\<lambda>(x, y). Fin y < llength xs \<and> P (lnth xs y)) 
                          (lzip xs (iterates Suc 0)))"
    by(simp add: lsublist_def)
  also have "\<forall>(x, y)\<in>lset (lzip xs (iterates Suc 0)). Fin y < llength xs \<and> x = lnth xs y"
    by(auto simp add: lset_lzip)
  hence "lfilter (\<lambda>(x, y). Fin y < llength xs \<and> P (lnth xs y)) (lzip xs (iterates Suc 0)) =
         lfilter (P \<circ> fst) (lzip xs (iterates Suc 0))"
    by -(rule lfilter_cong[OF refl], auto)
  also have "lmap fst (lfilter (P \<circ> fst) (lzip xs (iterates Suc 0))) =
            lfilter P (lmap fst (lzip xs (iterates Suc 0)))"
    unfolding lfilter_lmap ..
  also have "lmap fst (lzip xs (iterates Suc 0)) = xs"
    by(simp add: lmap_fst_lzip_conv_ltake ltake_all)
  finally show ?thesis ..
qed

lemma ltake_iterates_Suc:
  "ltake (Fin n) (iterates Suc m) = llist_of [m..<n + m]"
proof(induct n arbitrary: m)
  case 0 thus ?case by(simp add: zero_inat_def[symmetric])
next
  case (Suc n)
  have "ltake (Fin (Suc n)) (iterates Suc m) = 
        LCons m (ltake (Fin n) (iterates Suc (Suc m)))"
    by(subst iterates)(simp add: iSuc_Fin[symmetric])
  also note Suc
  also have "LCons m (llist_of [Suc m..<n + Suc m]) = llist_of [m..<Suc n+m]"
    unfolding llist_of.simps[symmetric]
    by(auto simp del: llist_of.simps simp add: upt_conv_Cons)
  finally show ?case .
qed

lemma lsublist_lappend_lfinite: 
  assumes len: "llength xs = Fin k"
  shows "lsublist (lappend xs ys) A = 
         lappend (lsublist xs A) (lsublist ys {n. n + k \<in> A})"
proof -
  let ?it = "iterates Suc"
  from assms have fin: "lfinite xs" by(rule llength_eq_Fin_lfiniteD)
  have "lsublist (lappend xs ys) A = 
    lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip (lappend xs ys) (?it 0)))"
    by(simp add: lsublist_def)
  also have "?it 0 = lappend (ltake (Fin k) (?it 0)) (ldrop (Fin k) (?it 0))"
    by(simp only: lappend_ltake_ldrop)
  also note lzip_lappend
  also note lfilter_lappend_lfinite
  also note lmap_lappend_distrib
  also have "lzip xs (ltake (Fin k) (?it 0)) = lzip xs (?it 0)"
    using len by(subst (1 2) lzip_conv_lzip_ltake_min_llength) simp
  also note lsublist_def[symmetric]
  also have "ldrop (Fin k) (?it 0) = ?it k"
    by(simp add: ldropn_iterates)
  also { fix n m
    have "(?it (n + m), lmap (\<lambda>n. n + m) (?it n)) \<in>
         {(?it (n + m), lmap (\<lambda>n. n + m) (?it n))|n. True}" by blast
    hence "?it (n + m) = lmap (\<lambda>n. n + m) (?it n)"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain n where q: "q = (?it (n + m), lmap (\<lambda>n. n + m) (?it n))" 
        by blast
      have ?EqLCons unfolding q by(subst (1 2) iterates) force
      thus ?case ..
    qed }
  from this[of 0 k] have "?it k = lmap (\<lambda>n. n + k) (?it 0)" by simp
  also note lzip_lmap2
  also note lfilter_lmap
  also note lmap_compose[symmetric]
  also have "fst \<circ> (\<lambda>(x, y). (x, y + k)) = fst" 
    by(simp add: o_def split_def)
  also have "(\<lambda>(x, y). y \<in> A) \<circ> (\<lambda>(x, y). (x, y + k)) = (\<lambda>(x, y). y \<in> {n. n + k \<in> A})"
    by(simp add: expand_fun_eq)
  also note lsublist_def[symmetric]
  finally show ?thesis using len by simp
qed

lemma lsublist_split:
  "lsublist xs A = 
   lappend (lsublist (ltake (Fin n) xs) A) (lsublist (ldropn n xs) {m. n + m \<in> A})"
proof(cases "Fin n \<le> llength xs")
  case False thus ?thesis by(auto simp add: ltake_all ldropn_all)
next
  case True
  have "xs = lappend (ltake (Fin n) xs) (ldrop (Fin n) xs)"
    by(simp only: lappend_ltake_ldrop)
  hence "xs = lappend (ltake (Fin n) xs) (ldropn n xs)" by simp
  hence "lsublist xs A = lsublist (lappend (ltake (Fin n) xs) (ldropn n xs)) A"
    by(simp)
  also note lsublist_lappend_lfinite[where k=n]
  finally show ?thesis using True by(simp add: min_def add_ac)
qed

lemma lsublist_cong:
  assumes xs: "xs = ys" and A: "\<And>n. Fin n < llength ys \<Longrightarrow> n \<in> A \<longleftrightarrow> n \<in> B"
  shows "lsublist xs A = lsublist ys B"
proof -
  have "lfilter (\<lambda>(x, y). y \<in> A) (lzip ys (iterates Suc 0)) = 
        lfilter (\<lambda>(x, y). y \<in> B) (lzip ys (iterates Suc 0))"
    by(rule lfilter_cong[OF refl])(auto simp add: lset_lzip A)
  thus ?thesis unfolding `xs = ys` lsublist_def by simp
qed

lemma lsublist_insert:
  assumes n: "Fin n < llength xs"
  shows "lsublist xs (insert n A) = 
         lappend (lsublist (ltake (Fin n) xs) A) (LCons (lnth xs n) 
                 (lsublist (ldropn (Suc n) xs) {m. Suc (n + m) \<in> A}))"
proof -
  have "lsublist xs (insert n A) = 
        lappend (lsublist (ltake (Fin n) xs) (insert n A)) 
                (lsublist (ldropn n xs) {m. n + m \<in> (insert n A)})"
    by(rule lsublist_split)
  also have "lsublist (ltake (Fin n) xs) (insert n A) = 
            lsublist (ltake (Fin n) xs) A"
    by(rule lsublist_cong[OF refl]) simp
  also { from n obtain X XS where "ldropn n xs = LCons X XS"
      by(cases "ldropn n xs")(auto simp add: ldropn_eq_LNil)
    moreover have "lnth (ldropn n xs) 0 = lnth xs n"
      using n by(simp del: lnth.simps(1))
    moreover have "ltl (ldropn n xs) = ldropn (Suc n) xs"
      by(cases xs)(simp_all add: ltl_ldropn del: ldropn_LCons)
    ultimately have "ldropn n xs = LCons (lnth xs n) (ldropn (Suc n) xs)" by simp
    hence "lsublist (ldropn n xs) {m. n + m \<in> insert n A} = 
           LCons (lnth xs n) (lsublist (ldropn (Suc n) xs) {m. Suc (n + m) \<in> A})"
      by(simp add: lsublist_LCons) }
  finally show ?thesis .
qed

lemma lfinite_lsublist [simp]:
  "lfinite (lsublist xs A) \<longleftrightarrow> lfinite xs \<or> finite A"
proof
  assume "lfinite (lsublist xs A)"
  hence "lfinite xs \<or> 
         finite {n. Fin n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)}"
    by(simp add: lsublist_def llength_lzip)
  also have "{n. Fin n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)} =
            {n. Fin n < llength xs \<and> n \<in> A}" by(auto simp add: lnth_lzip)
  finally show "lfinite xs \<or> finite A"
    by(auto simp add: not_lfinite_llength elim: contrapos_np)
next
  assume "lfinite xs \<or> finite A"
  moreover
  have "{n. Fin n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)} =
        {n. Fin n < llength xs \<and> n \<in> A}" by(auto simp add: lnth_lzip)
  ultimately show "lfinite (lsublist xs A)"
    by(auto simp add: lsublist_def llength_lzip)
qed



subsection {* 
  Alternative view on @{typ "'a llist"} as datatype 
  with constructors @{term "llist_of"} and @{term "inf_llist"}
*}

lemma inf_llist_rec [code]:
  "inf_llist f = LCons (f 0) (inf_llist (\<lambda>n. f (Suc n)))"
unfolding inf_llist_def
by(subst llist_corec) simp

lemma lfinite_inf_llist [iff]: "\<not> lfinite (inf_llist f)"
proof
  assume "lfinite (inf_llist f)"
  thus False
  proof(induct xs\<equiv>"inf_llist f" arbitrary: f rule: lfinite.induct)
    case lfinite_LNil
    with inf_llist_rec[of f] show ?case by simp
  next
    case (lfinite_LConsI xs x)
    from `LCons x xs = inf_llist f` inf_llist_rec[of f]
    have "xs = inf_llist (\<lambda>n. f (n + 1))" by simp
    thus ?case by(rule lfinite_LConsI)
  qed
qed

lemma inf_llist_neq_llist_of [simp]:
  "llist_of xs \<noteq> inf_llist f"
   "inf_llist f \<noteq> llist_of xs"
using lfinite_llist_of[of xs] lfinite_inf_llist[of f] by fastsimp+

lemma inf_llist_inj [simp]:
  "inf_llist f = inf_llist g \<longleftrightarrow> f = g"
proof
  assume eq: "inf_llist f = inf_llist g"
  show "f = g"
  proof(rule ext)
    fix n
    from eq show "f n = g n"
    proof(induct n arbitrary: f g)
      case 0
      with inf_llist_rec[of f] inf_llist_rec[of g] show ?case by simp
    next
      case (Suc n)
      from `inf_llist f = inf_llist g` inf_llist_rec[of f] inf_llist_rec[of g]
      have "inf_llist (\<lambda>n. f (Suc n)) = inf_llist (\<lambda>n. g (Suc n))" by simp_all
      thus ?case by(rule Suc)
    qed
  qed
qed simp

lemma inf_llist_lprefix [simp]: "lprefix (inf_llist f) xs \<longleftrightarrow> xs = inf_llist f"
by(auto simp add: not_lfinite_lprefix_conv_eq)

lemma llist_exhaust:
  obtains (llist_of) ys where "xs = llist_of ys"
       | (inf_llist) f where "xs = inf_llist f"
proof(cases "lfinite xs")
  case True
  then obtain ys where "xs = llist_of ys"
    unfolding lfinite_eq_range_llist_of by auto
  thus ?thesis by(rule that)
next
  case False
  hence "(xs, inf_llist (lnth xs)) \<in>
        {(xs, inf_llist (lnth xs))|xs. \<not> lfinite xs}" by blast
  hence "xs = inf_llist (lnth xs)"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs where q: "q = (xs, inf_llist (lnth xs))"
      and nfin: "\<not> lfinite xs" by blast
    from nfin obtain x xs' where xs: "xs = LCons x xs'" by(cases xs) auto
    moreover with nfin have nfin': "\<not> lfinite xs'" by simp
    ultimately show ?case using q inf_llist_rec[of "lnth xs"] by simp
  qed
  thus thesis by(rule that)
qed

subsection {* The infinite list constructor @{term "inf_llist"} *}

lemma llength_inf_llist [simp]:
  "llength (inf_llist f) = Infty"
by(rule not_lfinite_llength) auto

lemma lappend_inf_llist [simp]: "lappend (inf_llist f) xs = inf_llist f"
by(simp add: lappend_inf)

lemma lmap_inf_llist [simp]: 
  "lmap f (inf_llist g) = inf_llist (f o g)"
proof -
  have "(lmap f (inf_llist g), inf_llist (f o g)) \<in>
       {(lmap f (inf_llist g), inf_llist (f o g))|g. True}" by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain g where q: "q = (lmap f (inf_llist g), inf_llist (f o g))" by blast
    have ?EqLCons unfolding q by(subst (1 2) inf_llist_rec)(auto simp add: o_def)
    thus ?case ..
  qed
qed

lemma ltake_Fin_inf_llist [simp]:
  "ltake (Fin n) (inf_llist f) = llist_of (map f [0..<n])"
proof(induct n arbitrary: f)
  case 0 thus ?case by(simp add: zero_inat_def[symmetric])
next
  case (Suc n)
  have "ltake (Fin (Suc n)) (inf_llist f) =
        LCons (f 0) (ltake (Fin n) (inf_llist (\<lambda>n. f (Suc n))))"
    by(subst inf_llist_rec)(simp add: iSuc_Fin[symmetric])
  also note Suc[of "\<lambda>n. f (Suc n)"]
  also have "map (\<lambda>a. f (Suc a)) [0..<n] = map f [1..<Suc n]" by(induct n) auto
  also note llist_of.simps(2)[symmetric]
  also have "f 0 # map f [1..<Suc n] = map f [0..<Suc n]" by(simp add: upt_rec)
  finally show ?case .
qed

lemma ldropn_inf_llist [simp]:
  "ldropn n (inf_llist f) = inf_llist (\<lambda>m. f (m + n))"
proof(induct n arbitrary: f)
  case 0 thus ?case by simp
next
  case (Suc n)
  from Suc[of "\<lambda>n. f (Suc n)"] show ?case
    by(subst inf_llist_rec) simp
qed

lemma ldrop_Fin_inf_llist:
  "ldrop (Fin n) (inf_llist f) = inf_llist (\<lambda>m. f (m + n))"
by simp

lemma lzip_inf_llist_inf_llist [simp]:
  "lzip (inf_llist f) (inf_llist g) = inf_llist (\<lambda>n. (f n, g n))"
proof -
  have "(lzip (inf_llist f) (inf_llist g), inf_llist (\<lambda>n. (f n, g n))) \<in> 
       {(lzip (inf_llist f) (inf_llist g), inf_llist (\<lambda>n. (f n, g n)))|f g. True}"
    by blast
  thus ?thesis
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain f g
      where q: "q = (lzip (inf_llist f) (inf_llist g), inf_llist (\<lambda>n. (f n, g n)))"
      by blast
    have ?EqLCons unfolding q by(subst (1 2 3) inf_llist_rec) auto
    thus ?case ..
  qed
qed

lemma lzip_llist_of_inf_llist [simp]:
  "lzip (llist_of xs) (inf_llist f) = llist_of (zip xs (map f [0..<length xs]))"
proof(induct xs arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "map f [0..<length (x # xs)] = f 0 # map (\<lambda>n. f (Suc n)) [0..<length xs]"
    by(simp add: upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)
  with Cons[of "\<lambda>n. f (Suc n)"]
  show ?case by(subst inf_llist_rec)(simp)
qed

lemma lzip_inf_llist_llist_of [simp]:
  "lzip (inf_llist f) (llist_of xs) = llist_of (zip (map f [0..<length xs]) xs)"
proof(induct xs arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "map f [0..<length (x # xs)] = f 0 # map (\<lambda>n. f (Suc n)) [0..<length xs]"
    by(simp add: upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)
  with Cons[of "\<lambda>n. f (Suc n)"]
  show ?case by(subst inf_llist_rec)(simp)
qed

lemma lnth_inf_llist [simp]: "lnth (inf_llist f) n = f n"
proof(induct n arbitrary: f)
  case 0 thus ?case by(subst inf_llist_rec) simp
next
  case (Suc n)
  from Suc[of "\<lambda>n. f (Suc n)"] show ?case
    by(subst inf_llist_rec) simp
qed

lemma lset_inf_llist [simp]: "lset (inf_llist f) = range f"
by(auto simp add: lset_def)

lemma llist_all2_inf_llist [simp]:
  "llist_all2 P (inf_llist f) (inf_llist g) \<longleftrightarrow> (\<forall>n. P (f n) (g n))"
by(simp add: llist_all2_def)

lemma llist_all2_llist_of_inf_llist [simp]:
  "\<not> llist_all2 P (llist_of xs) (inf_llist f)"
by(simp add: llist_all2_def)

lemma llist_all2_inf_llist_llist_of [simp]:
  "\<not> llist_all2 P (inf_llist f) (llist_of xs)"
by(simp add: llist_all2_def)

lemma lhd_inf_llist [simp]: "lhd (inf_llist f) = f 0"
by(subst inf_llist_rec) simp

lemma ltl_inf_llist [simp]: "ltl (inf_llist f) = inf_llist (\<lambda>n. f (Suc n))"
by(subst inf_llist_rec)(simp)

end
