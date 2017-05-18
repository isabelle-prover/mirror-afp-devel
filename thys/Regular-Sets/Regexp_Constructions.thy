(*
  File:     Regexp_Constructions.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>

  Some simple constructions on regular expressions to illustrate closure properties of regular
  languages: reversal, prefixes, suffixes, subwords ("fragments")
*)
section \<open>Basic constructions on regular expressions\<close>
theory Regexp_Constructions
imports
  Main
  "~~/src/HOL/Library/Sublist"
  "$AFP/Regular-Sets/Regular_Exp"
begin

subsection \<open>Reverse language\<close>

lemma rev_conc [simp]: "rev ` (A @@ B) = rev ` B @@ rev ` A"
  unfolding conc_def image_def by force

lemma rev_compower [simp]: "rev ` (A ^^ n) = (rev ` A) ^^ n"
  by (induction n) (simp_all add: conc_pow_comm)

lemma rev_star [simp]: "rev ` star A = star (rev ` A)"
  by (simp add: star_def image_UN)

  
text \<open>Suffix language\<close>

definition Suffixes :: "'a list set \<Rightarrow> 'a list set" where
  "Suffixes A = {w. \<exists>q. q @ w \<in> A}"

lemma Suffixes_altdef [code]: "Suffixes A = (\<Union>w\<in>A. set (suffixes w))"
  unfolding Suffixes_def set_suffixes_eq suffix_def by blast

lemma Nil_in_Suffixes_iff [simp]: "[] \<in> Suffixes A \<longleftrightarrow> A \<noteq> {}"
  by (auto simp: Suffixes_def)

lemma Suffixes_empty [simp]: "Suffixes {} = {}"
  by (auto simp: Suffixes_def)
    
lemma Suffixes_empty_iff [simp]: "Suffixes A = {} \<longleftrightarrow> A = {}"
  by (auto simp: Suffixes_altdef)
    
lemma Suffixes_singleton [simp]: "Suffixes {xs} = set (suffixes xs)"
  by (auto simp: Suffixes_altdef)
    
lemma Suffixes_insert: "Suffixes (insert xs A) = set (suffixes xs) \<union> Suffixes A"
  by (simp add: Suffixes_altdef)

lemma Suffixes_conc [simp]: "A \<noteq> {} \<Longrightarrow> Suffixes (A @@ B) = Suffixes B \<union> (Suffixes A @@ B)"
  unfolding Suffixes_altdef conc_def by (force simp: suffix_append)
    
lemma Suffixes_union [simp]: "Suffixes (A \<union> B) = Suffixes A \<union> Suffixes B"
  by (auto simp: Suffixes_def)
  
lemma Suffixes_UNION [simp]: "Suffixes (UNION A f) = UNION A (\<lambda>x. Suffixes (f x))"
  by (auto simp: Suffixes_def)

lemma Suffixes_compower: 
  assumes "A \<noteq> {}"
  shows   "Suffixes (A ^^ n) = insert [] (Suffixes A @@ (\<Union>k<n. A ^^ k))"
proof (induction n)
  case (Suc n)
  from Suc have "Suffixes (A ^^ Suc n) = 
                   insert [] (Suffixes A @@ ((\<Union>k<n. A ^^ k) \<union> A ^^ n))"
    by (simp_all add: assms conc_Un_distrib)
  also have "(\<Union>k<n. A ^^ k) \<union> A ^^ n = (\<Union>k\<in>insert n {..<n}. A ^^ k)"  by blast
  also have "insert n {..<n} = {..<Suc n}" by auto
  finally show ?case .
qed simp_all

lemma Suffixes_star [simp]: 
  assumes "A \<noteq> {}"
  shows   "Suffixes (star A) = Suffixes A @@ star A"
proof -
  have "star A = (\<Union>n. A ^^ n)" unfolding star_def ..
  also have "Suffixes \<dots> = (\<Union>x. Suffixes (A ^^ x))" by simp
  also have "\<dots> = (\<Union>n. insert [] (Suffixes A @@ (\<Union>k<n. A ^^ k)))"
    using assms by (subst Suffixes_compower) auto
  also have "\<dots> = insert [] (Suffixes A @@ (\<Union>n. (\<Union>k<n. A ^^ k)))"
    by (simp_all add: conc_UNION_distrib)
  also have "(\<Union>n. (\<Union>k<n. A ^^ k)) = (\<Union>n. A ^^ n)" by auto
  also have "\<dots> = star A" unfolding star_def ..
  also have "insert [] (Suffixes A @@ star A) = Suffixes A @@ star A" 
    using assms by auto
  finally show ?thesis .
qed
  
text \<open>Prefix language\<close>

definition Prefixes :: "'a list set \<Rightarrow> 'a list set" where
  "Prefixes A = {w. \<exists>q. w @ q \<in> A}"

lemma Prefixes_altdef [code]: "Prefixes A = (\<Union>w\<in>A. set (prefixes w))"
  unfolding Prefixes_def set_prefixes_eq prefix_def by blast

lemma Nil_in_Prefixes_iff [simp]: "[] \<in> Prefixes A \<longleftrightarrow> A \<noteq> {}"
  by (auto simp: Prefixes_def)

lemma Prefixes_empty [simp]: "Prefixes {} = {}"
  by (auto simp: Prefixes_def)
    
lemma Prefixes_empty_iff [simp]: "Prefixes A = {} \<longleftrightarrow> A = {}"
  by (auto simp: Prefixes_altdef)
    
lemma Prefixes_singleton [simp]: "Prefixes {xs} = set (prefixes xs)"
  by (auto simp: Prefixes_altdef)
    
lemma Prefixes_insert: "Prefixes (insert xs A) = set (prefixes xs) \<union> Prefixes A"
  by (simp add: Prefixes_altdef)

lemma Prefixes_conc [simp]: "B \<noteq> {} \<Longrightarrow> Prefixes (A @@ B) = Prefixes A \<union> (A @@ Prefixes B)"
  unfolding Prefixes_altdef conc_def by (force simp: prefix_append)
    
lemma Prefixes_union [simp]: "Prefixes (A \<union> B) = Prefixes A \<union> Prefixes B"
  by (auto simp: Prefixes_def)
  
lemma Prefixes_UNION [simp]: "Prefixes (UNION A f) = UNION A (\<lambda>x. Prefixes (f x))"
  by (auto simp: Prefixes_def)


lemma Prefixes_rev: "Prefixes (rev ` A) = rev ` Suffixes A"
  by (auto simp: Prefixes_altdef prefixes_rev Suffixes_altdef)

lemma Suffixes_rev: "Suffixes (rev ` A) = rev ` Prefixes A"
  by (auto simp: Prefixes_altdef suffixes_rev Suffixes_altdef)    


lemma Prefixes_compower:
  assumes "A \<noteq> {}"
  shows   "Prefixes (A ^^ n) = insert [] ((\<Union>k<n. A ^^ k) @@ Prefixes A)"
proof -
  have "A ^^ n = rev ` ((rev ` A) ^^ n)" by (simp add: image_image)
  also have "Prefixes \<dots> = insert [] ((\<Union>k<n. A ^^ k) @@ Prefixes A)"
    unfolding Prefixes_rev 
    by (subst Suffixes_compower) (simp_all add: image_UN image_image Suffixes_rev assms)
  finally show ?thesis .
qed

lemma Prefixes_star [simp]:
  assumes "A \<noteq> {}"
  shows   "Prefixes (star A) = star A @@ Prefixes A"
proof -
  have "star A = rev ` star (rev ` A)" by (simp add: image_image)
  also have "Prefixes \<dots> = star A @@ Prefixes A"
    unfolding Prefixes_rev
    by (subst Suffixes_star) (simp_all add: assms image_image Suffixes_rev)
  finally show ?thesis .
qed


subsection \<open>Sublists language\<close>

definition Sublists where "Sublists A = (\<Union>w\<in>A. set (sublists w))"

lemma Sublists_empty [simp]: "Sublists {} = {}"
  by (simp add: Sublists_def)

lemma Sublists_insert [simp]: "Sublists (insert xs A) = set (sublists xs) \<union> Sublists A"
  by (simp add: Sublists_def)
    
lemma Sublists_singleton [simp]: "Sublists {xs} = set (sublists xs)"
  by simp
    
lemma Sublists_Un [simp]: "Sublists (A \<union> B) = Sublists A \<union> Sublists B"
  by (simp add: Sublists_def)
    
lemma Sublists_UNION [simp]: "Sublists (UNION A f) = UNION A (\<lambda>x. Sublists (f x))"
  by (simp add: Sublists_def)
  
lemma Sublists_conc [simp]: "Sublists (A @@ B) = Sublists A @@ Sublists B"
proof safe
  fix xs assume "xs \<in> Sublists (A @@ B)"
  then obtain ys zs where *: "ys \<in> A" "zs \<in> B" "sublisteq xs (ys @ zs)" 
    by (auto simp: Sublists_def conc_def)
  from *(3) obtain xs1 xs2 where "xs = xs1 @ xs2" "sublisteq xs1 ys" "sublisteq xs2 zs"
    by (rule sublisteq_appendE)
  with *(1,2) show "xs \<in> Sublists A @@ Sublists B" by (auto simp: Sublists_def set_sublists_eq)
next
  fix xs assume "xs \<in> Sublists A @@ Sublists B"
  then obtain xs1 xs2 ys zs 
    where "xs = xs1 @ xs2" "sublisteq xs1 ys" "sublisteq xs2 zs" "ys \<in> A" "zs \<in> B"
    by (auto simp: conc_def Sublists_def)
  thus "xs \<in> Sublists (A @@ B)" by (force simp: Sublists_def conc_def intro: list_emb_append_mono)
qed

lemma Sublists_compower [simp]: "Sublists (A ^^ n) = Sublists A ^^ n"
  by (induction n) simp_all
    
lemma Sublists_star [simp]: "Sublists (star A) = star (Sublists A)"
  by (simp add: star_def)


subsection \<open>Various regular expression constructions\<close>
  
primrec rexp_rev where
  "rexp_rev Zero = Zero"
| "rexp_rev One = One"
| "rexp_rev (Atom x) = Atom x"
| "rexp_rev (Plus r s) = Plus (rexp_rev r) (rexp_rev s)"
| "rexp_rev (Times r s) = Times (rexp_rev s) (rexp_rev r)"
| "rexp_rev (Star r) = Star (rexp_rev r)"

lemma lang_rexp_rev [simp]: "lang (rexp_rev r) = rev ` lang r"
  by (induction r) (simp_all add: image_Un)  


primrec suffix_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "suffix_rexp Zero = Zero"
| "suffix_rexp One = One"
| "suffix_rexp (Atom a) = Plus (Atom a) One"
| "suffix_rexp (Plus r s) = Plus (suffix_rexp r) (suffix_rexp s)"
| "suffix_rexp (Times r s) =
    (if rexp_empty r then Zero else Plus (Times (suffix_rexp r) s) (suffix_rexp s))"
| "suffix_rexp (Star r) =
    (if rexp_empty r then One else Times (suffix_rexp r) (Star r))"

theorem lang_suffix_rexp [simp]:
  "lang (suffix_rexp r) = Suffixes (lang r)"
  by (induction r) (auto simp: rexp_empty_iff)


primrec prefix_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "prefix_rexp Zero = Zero"
| "prefix_rexp One = One"
| "prefix_rexp (Atom a) = Plus (Atom a) One"
| "prefix_rexp (Plus r s) = Plus (prefix_rexp r) (prefix_rexp s)"
| "prefix_rexp (Times r s) =
    (if rexp_empty s then Zero else Plus (Times r (prefix_rexp s)) (prefix_rexp r))"
| "prefix_rexp (Star r) =
    (if rexp_empty r then One else Times (Star r) (prefix_rexp r))"

theorem lang_prefix_rexp [simp]:
  "lang (prefix_rexp r) = Prefixes (lang r)"
  by (induction r) (auto simp: rexp_empty_iff)


primrec sublists_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "sublists_rexp Zero = Zero"
| "sublists_rexp One = One"
| "sublists_rexp (Atom x) = Plus (Atom x) One"
| "sublists_rexp (Plus r s) = Plus (sublists_rexp r) (sublists_rexp s)"
| "sublists_rexp (Times r s) = Times (sublists_rexp r) (sublists_rexp s)"
| "sublists_rexp (Star r) = Star (sublists_rexp r)"

lemma lang_sublists_rexp [simp]: "lang (sublists_rexp r) = Sublists (lang r)"
  by (induction r) auto 

end