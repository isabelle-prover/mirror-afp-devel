(*  ID:         $Id: Vector.thy,v 1.2 2007-07-19 19:50:51 fhaftmann Exp $
    Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Vector *}

theory Vector
imports Main Efficient_Nat
begin

datatype 'a vector = Vector "'a list"

subsection {* Tabulation *}

constdefs
  tabulate' :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vector"
  "tabulate' p \<equiv> Vector (map (snd p) [0 ..< fst p])"
        (* map int [0..nat (fst p)])])*)
  tabulate :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vector"
  "tabulate n f \<equiv> tabulate' (n, f)"
  tabulate2 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a vector vector"
  "tabulate2 m n f \<equiv> tabulate m (\<lambda>i .tabulate n (f i))"
  tabulate3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
  (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a vector vector vector"
  "tabulate3 l m n f \<equiv> tabulate l (\<lambda>i. tabulate m (\<lambda>j .tabulate n (\<lambda>k. f i j k)))"


syntax 
 "_tabulate" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 'a vector"  ("(\<lbrakk>_. _ < _\<rbrakk>)") 
 "_tabulate2" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 
    pttrn \<Rightarrow> nat \<Rightarrow> 'a vector"
  ("(\<lbrakk>_. _ < _, _ < _\<rbrakk>)")
 "_tabulate3" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 
     pttrn \<Rightarrow> nat \<Rightarrow> 
     pttrn \<Rightarrow> nat \<Rightarrow> 'a vector"
  ("(\<lbrakk>_. _ < _, _ < _, _ < _ \<rbrakk>)")
translations 
  "\<lbrakk>f. x < n\<rbrakk>" == "tabulate n (\<lambda>x. f)"
  "\<lbrakk>f. x < m, y < n\<rbrakk>" == "tabulate2 m n (\<lambda>x y. f)"
  "\<lbrakk>f. x < l, y < m, z < n\<rbrakk>" == "tabulate3 l m n (\<lambda>x y z. f)"


subsection {* Access *}

constdefs 
 sub1 :: "'a vector \<times> nat \<Rightarrow> 'a"
 "sub1 p \<equiv> let (a, n) = p in case a of (Vector as) \<Rightarrow> as ! n"
 sub :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a" 
 "sub a n \<equiv> sub1 (a, n)"

syntax 
  "_sub" :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_\<rbrakk>)" [1000] 999) 
  "_sub2" :: "'a vector vector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_,_\<rbrakk>)" [1000] 999)
  "_sub3" :: "'a vector vector vector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" ("(_\<lbrakk>_,_,_\<rbrakk>)" [1000] 999) 

translations 
  "(a\<lbrakk>n\<rbrakk>)" == "sub a n"
  "(as\<lbrakk>m, n\<rbrakk>)" == "sub (sub as m) n"
  "(as\<lbrakk>l, m, n\<rbrakk>)" == "sub (sub (sub as l) m) n"


types_code
  vector  ("_ vector")

consts_code
  "tabulate'"  ("Vector.tabulate")
  "sub1"       ("Vector.sub")


text {* examples:  @{term "\<lbrakk>0. i < 5\<rbrakk>"}, @{term "\<lbrakk>i. i < 5, j < 3\<rbrakk>"}  *}

lemma sub_tabulate: "0 \<le> i ==> i < u ==>
 (tabulate u f)\<lbrakk>i\<rbrakk> = f i" 
  by (simp add: tabulate_def tabulate'_def sub_def sub1_def Let_def) 

lemma sub_tabulate3: "0 \<le> i ==> 0 \<le> j ==> 0 \<le> k ==> 
 i < l ==> j < m ==> k < n ==>
 (tabulate3 l m n f)\<lbrakk>i, j, k\<rbrakk> = f i j k"
  by (simp add: tabulate3_def tabulate_def tabulate'_def 
  sub_def sub1_def Let_def  Vector.inject 
  split: Vector.split)

end
