(*  Title:      RSAPSS/Pigeonholeprinciple.thy
    ID:         $Id: Pigeonholeprinciple.thy,v 1.1 2005-05-10 16:13:46 nipkow Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Pigeon hole principle"

theory Pigeonholeprinciple
imports Productdivides
begin

text {* This theory is a formal proof for the pigeon hole principle. The
  basic principle is, that if you have to put n+1 pigeons in n holes there
  is at least one hole with more than one pigeon *}

consts
  alldistinct:: "nat list \<Rightarrow> bool"
  alllesseq:: "nat list \<Rightarrow> nat \<Rightarrow> bool"
  allnonzero:: "nat list \<Rightarrow> bool"
  positives:: "nat \<Rightarrow> nat list"
  timeslist:: "nat list \<Rightarrow> nat"
  fac:: "nat \<Rightarrow> nat"
  del:: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  pigeonholeinduction::" nat list \<Rightarrow> bool"
  insort:: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  sort:: "nat list \<Rightarrow> nat list"

primrec 
  "alldistinct [] = True"
  "alldistinct (x # xs) =  (\<not> x mem xs \<and> alldistinct xs)"

primrec
  "alllesseq [] n= True"
  "alllesseq (x # xs) n = (x \<le> n \<and> (alllesseq xs n))"

primrec
  "allnonzero [] = True"
  "allnonzero (x # xs) = (x \<noteq> 0 \<and> allnonzero xs)"

primrec
  "positives 0 = []"
  "positives (Suc n) = (Suc n)#(positives n)"

primrec
  "timeslist [] = 1"
  "timeslist (x#xs) = x * timeslist (xs)"

primrec
  "fac 0 = 1"
  "fac (Suc n) = Suc n * fac n"

primrec
  "del a [] = []"
  "del a (x#xs) = (if a \<noteq> x then x # (del a xs) else xs)" 

lemma length_del [rule_format]: "x mem xs \<longrightarrow> length (del x xs) < length xs"
  by (induct xs) auto

recdef pigeonholeinduction "measure length"
  "pigeonholeinduction [] = True"
  "pigeonholeinduction (x#xs) = (if ((length (x#xs)) mem xs) then (pigeonholeinduction (del (length (x#xs)) (x#xs))) else (pigeonholeinduction xs))"
  (hints recdef_simp: length_del)

primrec
  "insort x[] = [x]"
  "insort x (y#ys) = (if (x < y) then (x#y#ys) else y#(insort x ys))"

recdef sort "measure length"
  "sort [] = []"
  "sort (x#xs) = insort x (sort xs)"

constdefs perm:: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  "perm xs ys == (sort xs = sort ys)"

lemma allnonzerodelete[rule_format]: "(allnonzero xs) \<longrightarrow> allnonzero (del x xs)"
  apply (induct_tac xs)
  by (auto)

lemma notmemnotdelmem [rule_format]: "x \<noteq> a \<longrightarrow> \<not> a mem xs \<longrightarrow> \<not> a mem (del x xs)"
  apply (induct_tac xs)
  by (auto)

lemma alldistinctdelete[rule_format]: "(alldistinct xs) \<longrightarrow> alldistinct (del x xs)"
  apply (induct_tac xs)
  apply (auto)
  apply (insert notmemnotdelmem)
  by (auto)

lemma pigeonholeprinciple_lemma2[rule_format]: "\<not> (Suc n) mem xs \<longrightarrow> alllesseq xs (Suc n) \<longrightarrow> alllesseq xs n"
  apply (induct_tac xs)
  by (auto)

lemma pigeonholeprinciple_lemma1[rule_format]: "alldistinct xs \<longrightarrow> alllesseq xs (Suc n) \<longrightarrow> alllesseq (del (Suc n) xs) n"
  apply (induct_tac xs)
  apply (auto)
  apply (rule pigeonholeprinciple_lemma2)
  by (auto)

lemma anotinsort[rule_format]: "a \<noteq> x \<longrightarrow> (a mem b = a mem (insort x b))"
  apply (induct_tac b)
  by (auto)

lemma ainsort: "a mem (insort a b)"
  apply (induct_tac b)
  by (auto)

lemma memeqsort: "x mem xs = x mem (sort xs)"
  apply (induct_tac xs)
  apply (simp)+
  apply (case_tac "x=a")
  apply (simp add: ainsort)+
  by (rule anotinsort, simp)

lemma  permmember: "\<lbrakk>perm xs ys; x mem xs\<rbrakk> \<Longrightarrow> x mem ys"
  by (simp add:perm_def memeqsort [of x xs] memeqsort [of x ys])

lemma seteqmem: "x \<in> set xs = x mem xs"
  apply (induct_tac xs)
  by (auto)

lemma lengtheqSuc: "length (x#xs) = Suc (length xs)"
  by (auto)

lemma alllesseqdelete: "\<lbrakk>alldistinct (x#xs); alllesseq (x#xs) (length(x#xs))\<rbrakk> \<Longrightarrow> alllesseq (del (length(x#xs)) (x#xs)) (length (xs))"
  apply (insert pigeonholeprinciple_lemma1 [of "x#xs" "length xs" ])
  by (simp only: lengtheqSuc)

lemma perminsert: "perm xs ys \<Longrightarrow> perm (a#xs) (a#ys)"
  by (simp add: perm_def)

lemma lengthdel2 [rule_format]: "a  mem xs \<longrightarrow>length(del a (x#xs)) = length xs"
  apply (induct_tac xs)
  by (auto)

lemma dellengthinalllesseq: "\<lbrakk>alldistinct (x#xs); alllesseq (x#xs) (length (x#xs)); length (x#xs) mem xs \<rbrakk> \<Longrightarrow> alllesseq (del (length (x#xs)) (x#xs))(length (del (length (x#xs)) (x#xs)))"
  apply (drule alllesseqdelete)
  apply (simp)
  apply (insert lengthdel2 [of "length (x#xs)" xs x])
  by (simp)

lemma lengthmem: "\<lbrakk>length (x#xs) mem (xs)\<rbrakk> \<Longrightarrow> length (x#xs) mem (x#xs)"
  by (auto)

lemma permSuclengthdel: "\<lbrakk>Suc (length xs) mem xs; perm (positives (length xs)) (x # del (Suc (length xs)) xs); x \<noteq> Suc (length xs)\<rbrakk> \<Longrightarrow> perm (Suc (length xs) # positives (length xs)) ((Suc (length xs))#(x # del (Suc (length xs)) xs))"
  apply (rule perminsert)
  by (simp)

lemma insortsym: "insort a (insort x xs) = insort x (insort a xs)"
  apply (induct_tac xs)
  by (auto)

lemma insortsortdel[rule_format]: "x mem xs \<longrightarrow> insort x (sort (del  x xs)) = (sort xs)"
  apply (induct_tac xs)
  apply (auto)
  apply (subst insortsym)
  by (auto)

lemma permSuclengthdel2: "\<lbrakk>Suc (length xs) mem xs; x \<noteq> Suc (length xs); perm (Suc (length xs) # positives (length xs)) ((Suc (length xs))#(x # del (Suc (length xs)) xs))\<rbrakk> \<Longrightarrow>perm (Suc (length xs) # positives (length xs)) (x # xs)"
  apply (simp add: perm_def)
  apply (subst insortsym)
  apply (insert insortsortdel [of "Suc (length xs)" xs, THEN sym])
  by (auto)

lemma dellengthinperm: "\<lbrakk> length (x # xs) mem (x#xs); perm (positives (length (del (length (x # xs)) (x # xs))))(del (length (x # xs)) (x # xs))\<rbrakk> \<Longrightarrow> perm (positives (length (x # xs))) (x # xs)"
  apply (case_tac "x =Suc (length xs)")
  apply (simp)
  apply (drule perminsert)
  apply (simp)
  apply (insert lengthdel2 [of "length (x # xs)" "xs" "x"])
  apply (simp del:perm_def positives.simps)
  apply (simp only: positives.simps)
  apply (frule permSuclengthdel)
  apply (simp)
  apply (simp)
  apply (rule permSuclengthdel2)
  by (simp)+

lemma positiveseq: "positives (length xs) = rev ([1 .. length xs])"
  apply (induct_tac xs)
  by (auto)

lemma memsetpositives:"\<lbrakk>perm (positives (length xs)) xs; 0 < x; x \<le> length xs\<rbrakk> \<Longrightarrow> x \<in> set (positives (length xs))"
  apply (subst positiveseq)
  apply (simp add:set_upt)
  by (auto)

lemma pigeonholeprinciple[rule_format]: "allnonzero xs \<longrightarrow> alldistinct xs \<longrightarrow> alllesseq xs (length xs) \<longrightarrow> perm (positives (length xs)) xs"
  apply (induct_tac xs rule:pigeonholeinduction.induct)
  apply (simp add:perm_def)
  apply (safe)
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
  apply (simp add:seteqmem [THEN sym])
  apply (frule memsetpositives)
  apply (simp add:seteqmem)+
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
  apply (simp add:seteqmem [THEN sym])
  apply (frule memsetpositives)
  apply (simp add:seteqmem)+
  apply (rule permmember)
  apply (simp)+
  apply (case_tac "Suc (length xs) = x")
  apply (drule perminsert)
  apply (simp)+
  apply (erule conjE)+
  apply (drule le_neq_implies_less)
  apply (simp add:less_Suc_eq_le)+
  apply (erule_tac P="x mem xs" in notE)
  apply (simp add:seteqmem [THEN sym])
  apply (frule memsetpositives)
  apply (simp add:seteqmem)+
  apply (rule permmember)
  by (simp)+

lemma equaltimeslist: "\<lbrakk>sort xs = sort ys\<rbrakk> \<Longrightarrow> timeslist (sort xs) = timeslist (sort ys)"
  by (auto)

lemma timeslistmultkom: "timeslist (xs) * x = x * timeslist (xs)"
  by (simp)

lemma timeslistinsort: "timeslist (insort a xs) = timeslist (a#xs)" 
  apply (induct_tac xs)
  by (auto)

lemma timeslisteq: "timeslist (sort xs) = timeslist xs"
  apply (induct_tac xs)
  apply (auto)
  apply (simp add: timeslistmultkom [THEN sym])
  by (simp add:timeslistinsort)

lemma permtimeslist: "perm xs ys \<Longrightarrow> timeslist xs = timeslist ys"
  apply (simp only:perm_def)
  apply (insert equaltimeslist [of xs ys])
  apply (simplesubst timeslisteq [THEN sym])
  apply (simplesubst timeslisteq [of xs, THEN sym])
  by (auto)

lemma timeslistpositives: "timeslist (positives n) = fac n"
  apply (induct_tac n)
  by (auto)

lemma pdvdnot: "\<lbrakk>p \<in> prime; \<not> p dvd x; \<not> p dvd y\<rbrakk> \<Longrightarrow> \<not> p dvd x*y"
  apply (auto)
  apply (insert prime_dvd_mult [of p x y])
  by (simp)

lemma lessdvdnot: "\<lbrakk>Suc (x::nat) < p\<rbrakk> \<Longrightarrow> \<not> p dvd Suc x"
  apply (auto)
  apply (frule mod_less)
  apply (frule dvd_imp_le)
by (auto)

lemma pnotdvdall:"\<lbrakk>p \<in> prime; p dvd (Suc n)*(fac n); \<not> p dvd fac n; Suc n < p\<rbrakk> \<Longrightarrow> False"
  apply (insert lessdvdnot [of n p])
  apply (insert pdvdnot [of p "Suc n" "fac n"])
  by (auto)

lemma primefact[rule_format]: "p \<in> prime \<longrightarrow>  (n::nat) < p \<longrightarrow> (fac n mod p \<noteq> 0)"
  apply (induct_tac n rule:fac.induct)
  apply (simp add:prime_def)
  apply (simp only: fac.simps dvd_eq_mod_eq_0 [THEN sym] )
  apply (clarify)
  apply (drule mp)
  apply (simp)
  apply (insert lessdvdnot pdvdnot [of "p" "fac n" "Suc n"] pnotdvdall)
  by (auto)

end
