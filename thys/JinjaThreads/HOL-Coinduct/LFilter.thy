(*  Title:      Filter for lazy lists
    Author:     Lawrence C Paulson and Andreas Lochbihler
    Copyright   1997  University of Cambridge
*)

header {*The "filter" functional for coinductive lists
  --defined by a combination of induction and coinduction*}

theory LFilter imports Coinductive_List begin

inductive_set
  findRel	:: "('a => bool) => ('a llist * 'a llist)set"
  for p :: "'a => bool"
  where
    found:  "p x ==> (LCons x l, LCons x l) \<in> findRel p"
  | seek:   "[| ~p x;  (l,l') \<in> findRel p |] ==> (LCons x l, l') \<in> findRel p"

declare findRel.intros [intro]

definition
  find    :: "['a => bool, 'a llist] => 'a llist" where
  "find p l = (SOME l'. (l,l'): findRel p | (l' = LNil & l ~: Domain(findRel p)))"

definition
  lfilter :: "['a => bool, 'a llist] => 'a llist" where
  "lfilter p l = llist_corec l (%l. case find p l of
                                            LNil => None
                                          | LCons y z => Some(y,z))"


subsection {* @{text findRel}: basic laws *}

inductive_cases
  findRel_LConsE [elim!]: "(LCons x l, l'') \<in> findRel p"


lemma findRel_functional [rule_format]:
     "(l,l'): findRel p ==> (l,l''): findRel p --> l'' = l'"
by (erule findRel.induct, auto)

lemma findRel_imp_LCons [rule_format]:
     "(l,l'): findRel p ==> \<exists>x l''. l' = LCons x l'' & p x"
by (erule findRel.induct, auto)

lemma findRel_LNil [elim!]: "(LNil,l): findRel p ==> R"
by (blast elim: findRel.cases)


subsection {* Properties of @{text "Domain (findRel p)"} *}

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


subsection {* @{text find}: basic equations *}

lemma find_LNil [simp]: "find p LNil = LNil"
by (unfold find_def, blast)

lemma findRel_imp_find [simp]: "(l,l') \<in> findRel p ==> find p l = l'"
unfolding find_def by (blast dest: findRel_functional)

lemma find_LCons_found: "p x ==> find p (LCons x l) = LCons x l"
by (blast intro: findRel_imp_find)

lemma diverge_find_LNil [simp]: "l ~: Domain(findRel p) ==> find p l = LNil"
by (unfold find_def, blast)

lemma find_LCons_seek: "~ (p x) ==> find p (LCons x l) = find p l"
by (cases "LCons x l \<in> Domain (findRel p) ")(fastsimp intro: findRel_imp_find)+

lemma find_LCons [simp]:
     "find p (LCons x l) = (if p x then LCons x l else find p l)"
by (simp add: find_LCons_seek find_LCons_found)


subsection {* @{text lfilter}: basic equations *}

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

(* declare llistD_Fun_LNil_I [intro!] llistD_Fun_LCons_I [intro!] *)

lemma lfilter_eq_LNil: "lfilter p l = LNil ==> l ~: Domain(findRel p)" 
by (auto iff: Domain_findRel_iff)


lemma llist_split_asm: "P (llist_case f g xs) = (\<not> (xs = LNil \<and> \<not> P f \<or> (\<exists>x xs'. xs = LCons x xs' \<and> \<not> P (g x xs'))))"
by(cases xs) simp_all

lemma llist_split: "P (llist_case f g xs) = ((xs = LNil \<longrightarrow> P f) \<and> (\<forall>x xs'. xs = LCons x xs' \<longrightarrow> P (g x xs')))"
by(cases xs) simp_all

lemma lfilter_eq_LCons:
     "lfilter p l = LCons x l' \<Longrightarrow>
               (\<exists>l''. l' = lfilter p l'' & (l, LCons x l'') \<in> findRel p)"
unfolding lfilter_def
by(cases "l \<in> Domain (findRel p)")(auto iff: Domain_findRel_iff simp add: llist_corec)

lemma lfilter_cases: "lfilter p l = LNil  |   
          (\<exists>y l'. lfilter p l = LCons y (lfilter p l') & p y)"
by (cases "l \<in> Domain (findRel p) ") (auto iff: Domain_findRel_iff)

subsection {* @{text lfilter}: simple facts by coinduction *}

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

subsection {* Numerous lemmas required to prove @{text lfilter_conj} *}

lemma findRel_conj:
  assumes "(l,LCons x l'') \<in> findRel q"
  shows "p x \<Longrightarrow> (l,LCons x l'') \<in> findRel (%x. p x & q x)"
using assms by(induct l l'\<equiv>"LCons x l''" rule: findRel.induct) auto

lemma findRel_not_conj_Domain [rule_format]:
  assumes "(l,l'') \<in> findRel (%x. p x & q x)"
  shows "\<lbrakk> (l, LCons x l') \<in> findRel q; ~ p x \<rbrakk> \<Longrightarrow> l' \<in> Domain (findRel (%x. p x & q x))"
using assms by induct auto

lemma findRel_conj2 [rule_format]:
  assumes "(l,LCons x lx) \<in> findRel q"
  shows "\<lbrakk> (lx,lz) \<in> findRel(%x. p x & q x); ~ p x \<rbrakk>
         \<Longrightarrow> (l,lz) \<in> findRel (%x. p x & q x)"
using assms by(induct l lxx\<equiv>"LCons x lx") auto

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
  with False have "(lfilter p (lfilter q l), lfilter (\<lambda>x. p x \<and> q x) l) = (LNil, LNil)" by simp
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

lemma lfilter_conj: "lfilter p (lfilter q l) = lfilter (%x. p x & q x) l"
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

subsection {* Numerous lemmas required to prove ??:
     @{text "lfilter p (lmap f l) = lmap f (lfilter (%x. p(f x)) l)"}
 *}

lemma findRel_lmap_Domain:
  assumes "(l,l') \<in> findRel (\<lambda>x. p (f x))"
  shows "lmap f l \<in> Domain (findRel p)"
using assms by induct auto

lemma lmap_eq_LCons:
  "lmap f l = LCons x l' \<Longrightarrow> \<exists>y l''. x = f y & l' = lmap f l'' & l = LCons y l''"
unfolding lmap_def
by(cases l)(simp_all add: llist_corec)

lemma lmap_LCons_findRel:
  assumes "(lmap f l, LCons x l') \<in> findRel p"
  shows "\<exists>y l''. x = f y & l' = lmap f l'' & (l, LCons y l'') \<in> findRel(%x. p(f x))"
using assms
apply(induct lx\<equiv>"lmap f l" ly\<equiv>"LCons x l'" arbitrary: l)
apply simp_all
apply (blast dest!: lmap_eq_LCons[OF sym])+
done

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
      then obtain x' l' where l': "(lmap f l, LCons x' l') \<in> (findRel p)" and px': "p x'"
	unfolding Domain_findRel_iff by blast
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

end