(*  Title:      RSAPSS/Pigeonholeprinciple.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Pigeon hole principle"

theory Pigeonholeprinciple
imports Productdivides
begin

text {*
  This theory is a formal proof for the pigeon hole principle. The
  basic principle is, that if you have to put @{text "n + 1"} pigeons
  in n holes there is at least one hole with more than one pigeon.
*}

abbreviation (input) "alldistinct \<equiv> distinct"
abbreviation (input) mem (infixl "mem" 55) where "x mem xs \<equiv> x \<in> set xs"

primrec alllesseq :: "nat list \<Rightarrow> nat \<Rightarrow> bool"
where
  "alllesseq [] n = True"
| "alllesseq (x # xs) n = (x \<le> n \<and> alllesseq xs n)"

primrec allnonzero :: "nat list \<Rightarrow> bool"
where
  "allnonzero [] = True"
| "allnonzero (x # xs) = (x \<noteq> 0 \<and> allnonzero xs)"

primrec positives :: "nat \<Rightarrow> nat list"
where
  "positives 0 = []"
| "positives (Suc n) = Suc n # positives n"

primrec timeslist :: "nat list \<Rightarrow> nat"
where
  "timeslist [] = 1"
| "timeslist (x # xs) = x * timeslist xs"

primrec fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
| "fac (Suc n) = Suc n * fac n"

primrec del :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "del a [] = []"
| "del a (x # xs) = (if a \<noteq> x then x # del a xs else xs)" 

lemma length_del: "x mem xs \<Longrightarrow> length (del x xs) < length xs"
  by (induct xs) auto

function pigeonholeinduction
where
  "pigeonholeinduction [] = True"
| "pigeonholeinduction (x#xs) =
    (if ((length (x#xs)) mem xs)
     then (pigeonholeinduction (del (length (x#xs)) (x#xs)))
     else (pigeonholeinduction xs))"
by pat_completeness auto

termination by (relation "measure size") (auto simp add: length_del)

lemma old_pig_induct:
  fixes P
  assumes "P []"
    and "(\<And>(x\<Colon>nat) xs\<Colon>nat list.
    \<not> length (x # xs) mem xs \<longrightarrow> P xs \<Longrightarrow>
    length (x # xs) mem xs \<longrightarrow> P (del (length (x # xs)) (x # xs)) \<Longrightarrow>
    P (x # xs))"
  shows "P x"
  apply (rule pigeonholeinduction.induct)
  using assms apply auto
  done

definition
  perm :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "perm xs ys \<longleftrightarrow> sort xs = sort ys"

lemma allnonzerodelete: "allnonzero xs \<Longrightarrow> allnonzero (del x xs)"
  by (induct xs) auto

lemma notmemnotdelmem: "x \<noteq> a \<Longrightarrow> \<not> a mem xs \<Longrightarrow> \<not> a mem (del x xs)"
  by (induct xs) auto

lemma alldistinctdelete: "alldistinct xs \<Longrightarrow> alldistinct (del x xs)"
  apply (induct xs)
   apply auto
  apply (insert notmemnotdelmem)
  apply auto
  done

lemma pigeonholeprinciple_lemma2: "\<not> (Suc n) mem xs \<Longrightarrow> alllesseq xs (Suc n) \<Longrightarrow> alllesseq xs n"
  apply (atomize (full))
  apply (induct xs)
   apply auto
  done

lemma pigeonholeprinciple_lemma1:
    "alldistinct xs \<Longrightarrow> alllesseq xs (Suc n) \<Longrightarrow> alllesseq (del (Suc n) xs) n"
  apply (induct xs)
   apply auto
  apply (rule pigeonholeprinciple_lemma2)
   apply auto
  done

lemma anotinsort: "a \<noteq> x \<Longrightarrow> a mem b = a mem (insort x b)"
  by (induct b) auto

lemma ainsort: "a mem (insort a b)"
  by (induct b) auto

lemma memeqsort: "x mem xs = x mem (sort xs)"
  by (simp add: set_sort)

lemma permmember: "\<lbrakk>perm xs ys; x mem xs\<rbrakk> \<Longrightarrow> x mem ys"
  by (simp only: perm_def memeqsort [of x xs] memeqsort [of x ys])

lemma alllesseqdelete: "\<lbrakk>alldistinct (x#xs); alllesseq (x#xs) (length(x#xs))\<rbrakk>
    \<Longrightarrow> alllesseq (del (length(x#xs)) (x#xs)) (length (xs))"
  apply (insert pigeonholeprinciple_lemma1 [of "x#xs" "length xs"])
  apply simp
  done

lemma perminsert: "perm xs ys \<Longrightarrow> perm (a#xs) (a#ys)"
  by (simp add: perm_def)

lemma lengthdel2: "a mem xs \<Longrightarrow> length (del a (x#xs)) = length xs"
  by (induct xs) auto

lemma dellengthinalllesseq:
  "\<lbrakk>alldistinct (x#xs); alllesseq (x#xs) (length (x#xs)); length (x#xs) mem xs \<rbrakk>
  \<Longrightarrow> alllesseq (del (length (x#xs)) (x#xs))(length (del (length (x#xs)) (x#xs)))"
  apply (drule alllesseqdelete)
   apply simp
  apply (insert lengthdel2 [of "length (x#xs)" xs x])
  apply simp
  done

lemma lengthmem: "\<lbrakk>length (x#xs) mem (xs)\<rbrakk> \<Longrightarrow> length (x#xs) mem (x#xs)"
  by auto

lemma permSuclengthdel:
  "\<lbrakk>Suc (length xs) mem xs;
    perm (positives (length xs)) (x # del (Suc (length xs)) xs);
    x \<noteq> Suc (length xs)\<rbrakk> \<Longrightarrow>
  perm (Suc (length xs) # positives (length xs)) ((Suc (length xs))#(x # del (Suc (length xs)) xs))"
  apply (rule perminsert)
  apply simp
  done

lemma insortsym: "insort a (insort x xs) = insort x (insort a xs)"
  by (induct xs) auto

lemma insortsortdel: "x mem xs \<Longrightarrow> insort x (sort (del  x xs)) = (sort xs)"
  apply (induct xs)
   apply auto
  apply (subst insortsym)
  apply simp
  done

lemma permSuclengthdel2:
  "\<lbrakk>Suc (length xs) mem xs; x \<noteq> Suc (length xs);
    perm (Suc (length xs) # positives (length xs)) ((Suc (length xs))#(x # del (Suc (length xs)) xs))\<rbrakk>
  \<Longrightarrow> perm (Suc (length xs) # positives (length xs)) (x # xs)"
  apply (simp add: perm_def)
  apply (subst insortsym)
  apply (insert insortsortdel [of "Suc (length xs)" xs, symmetric])
  apply auto
  done

lemma dellengthinperm:
  "\<lbrakk> length (x # xs) mem (x#xs);
  perm (positives (length (del (length (x # xs)) (x # xs))))(del (length (x # xs)) (x # xs))\<rbrakk>
    \<Longrightarrow> perm (positives (length (x # xs))) (x # xs)"
  apply (cases "x = Suc (length xs)")
   apply simp
   apply (drule perminsert)
   apply simp
  apply (insert lengthdel2 [of "length (x # xs)" xs x])
  apply (simp del: perm_def positives.simps)
  apply (simp only: positives.simps)
  apply (frule permSuclengthdel)
    apply simp
   apply simp
  apply (rule permSuclengthdel2)
    apply simp_all
  done

lemma positiveseq: "positives (length xs) = rev ([1 ..< Suc(length xs)])"
  by (induct xs) auto

lemma memsetpositives:
  "\<lbrakk>perm (positives (length xs)) xs; 0 < x; x \<le> length xs\<rbrakk> \<Longrightarrow> x \<in> set (positives (length xs))"
  apply (subst positiveseq)
  apply (simp add:set_upt)
  apply auto
  done

lemmas seteqmem = List.member_def [symmetric]

lemma pigeonholeprinciple:
  "allnonzero xs \<Longrightarrow> alldistinct xs \<Longrightarrow> alllesseq xs (length xs) \<Longrightarrow> perm (positives (length xs)) xs"
  apply (atomize (full))
  apply (induct xs rule: old_pig_induct)
  apply (simp add: perm_def)
  apply safe
  apply (erule_tac P="allnonzero (del (length (x # xs)) (x # xs))" in notE)
  apply (rule allnonzerodelete)
  apply (simp)
  apply (erule_tac P="alldistinct (del (length (x # xs)) (x # xs))" in notE)
  apply (rule alldistinctdelete)
  apply (simp)
  apply (erule_tac P="alllesseq (del (length (x # xs)) (x # xs))(length (del (length (x # xs)) (x # xs)))" in notE)
  apply (rule dellengthinalllesseq)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (erule_tac P="perm (positives (length (x # xs))) (x # xs)" in notE)
  apply (drule lengthmem)  
  apply (drule dellengthinperm)
  apply (simp)+  
  apply (erule conjE)+
  apply (erule_tac P="alllesseq xs (length xs)" in notE)
  apply (erule pigeonholeprinciple_lemma2)
  apply (simp)+
  apply (erule conjE)+
  apply (case_tac "x=Suc(length xs)")
  apply (simp)
  apply (rule perminsert)
  apply (simp)
  apply (drule le_neq_implies_less)
  apply (simp add:less_Suc_eq_le)
  apply (erule_tac P="x mem xs" in notE)
  apply (simp add:seteqmem [symmetric])
  apply (frule memsetpositives)
  apply simp+
  apply (rule permmember)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (erule_tac P="allnonzero (del (length (x # xs)) (x # xs))" in notE, rule allnonzerodelete, simp)+
  apply (simp)
  apply (simp)
  apply (simp)
  apply (erule_tac P="alldistinct (del (length (x # xs)) (x # xs))" in notE, rule alldistinctdelete, simp)+
  apply (erule_tac P="alllesseq (del (length (x # xs)) (x # xs))(length (del (length (x # xs)) (x # xs)))" in notE)
  apply (case_tac "length (x#xs) mem xs")
  apply (erule dellengthinalllesseq, simp, simp)+
  apply (erule_tac P="alllesseq xs (length xs)" in notE)
  apply (rule pigeonholeprinciple_lemma2)
  apply (simp)+
  apply (case_tac "length (x#xs) mem (x#xs)")
  apply (frule dellengthinperm)
  apply (simp)+
  apply (case_tac "Suc (length xs) \<noteq> x")
  apply (simp)
  apply (erule conjE)+
  apply (erule_tac P="alllesseq xs (length xs)" in notE)
  apply (drule pigeonholeprinciple_lemma2)
  apply (simp)
  apply (simp)
  apply (erule conjE)+
  apply (simp)+
  apply (case_tac "Suc (length xs) = x")
  apply (drule perminsert)
  apply (simp)+
  apply (erule conjE)+
  apply (drule le_neq_implies_less)
  apply (simp add:less_Suc_eq_le)+
  apply (erule_tac P="x mem xs" in notE)
  apply (frule memsetpositives)
  apply simp+
  apply (rule permmember)
  apply (simp)+
  apply (case_tac "Suc (length xs) = x")
  apply (drule perminsert)
  apply (simp)+
  apply (erule conjE)+
  apply (drule le_neq_implies_less)
  apply (simp add:less_Suc_eq_le)+
  apply (erule_tac P="x mem xs" in notE)
  apply (frule memsetpositives)
  apply simp+
  apply (rule permmember)
  apply (simp)+
  done

lemma equaltimeslist: "\<lbrakk>sort xs = sort ys\<rbrakk> \<Longrightarrow> timeslist (sort xs) = timeslist (sort ys)"
  by auto

lemma timeslistmultkom: "timeslist (xs) * x = x * timeslist (xs)"
  by simp

lemma timeslistinsort: "timeslist (insort a xs) = timeslist (a#xs)" 
  by (induct xs) auto

lemma timeslisteq: "timeslist (sort xs) = timeslist xs"
  apply (induct xs)
   apply auto
  apply (simp add: timeslistmultkom [symmetric])
  apply (simp add:timeslistinsort)
  done

lemma permtimeslist: "perm xs ys \<Longrightarrow> timeslist xs = timeslist ys"
  apply (simp only:perm_def)
  apply (insert equaltimeslist [of xs ys])
  apply (simplesubst timeslisteq [symmetric])
  apply (simplesubst timeslisteq [of xs, symmetric])
  apply auto
  done

lemma timeslistpositives: "timeslist (positives n) = fac n"
  by (induct n) auto

lemma pdvdnot: fixes p::nat shows "\<lbrakk>prime p; \<not> p dvd x; \<not> p dvd y\<rbrakk> \<Longrightarrow> \<not> p dvd x*y"
by (metis prime_dvd_mult_eq_nat)

lemma lessdvdnot: "\<lbrakk>Suc (x::nat) < p\<rbrakk> \<Longrightarrow> \<not> p dvd Suc x"
  apply auto
  apply (frule mod_less)
  apply (frule dvd_imp_le)
  apply auto
  done

lemma pnotdvdall: "\<lbrakk>prime p; p dvd (Suc n)*(fac n); \<not> p dvd fac n; Suc n < p\<rbrakk> \<Longrightarrow> False"
by (metis lessdvdnot prime_dvd_mult_eq_nat)

lemma primefact: "prime p \<Longrightarrow> (n::nat) < p \<Longrightarrow> fac n mod p \<noteq> 0"
  apply (induct n)
   apply (simp add: prime_nat_def)
  apply (simp only: fac.simps dvd_eq_mod_eq_0 [symmetric])
  by (metis Suc_lessD pnotdvdall)

end
