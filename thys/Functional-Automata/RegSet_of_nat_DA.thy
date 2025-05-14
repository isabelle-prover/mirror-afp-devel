(*  Author:     Tobias Nipkow
    Copyright   1998 TUM

To generate a regular expression, the alphabet must be finite.
regexp needs to be supplied with an 'a list for a unique order

add_Atom d i j r a = (if d a i = j then Union r (Atom a) else r)
atoms d i j as = foldl (add_Atom d i j) Empty as

regexp as d i j 0 = (if i=j then Union (Star Empty) (atoms d i j as)
                        else atoms d i j as
*)

section "From deterministic automata to regular sets"

theory RegSet_of_nat_DA
imports "Regular-Sets.Regular_Set" DA  "HOL-ex.Sketch_and_Explore" 
begin

type_synonym 'a nat_next = "'a \<Rightarrow> nat \<Rightarrow> nat"

abbreviation
  deltas :: "'a nat_next \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "deltas \<equiv> foldl2"

primrec trace :: "'a nat_next \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat list"  where
"trace d i [] = []" |
"trace d i (x#xs) = d x i # trace d (d x i) xs"

(* conversion a la Warshall *)

primrec regset :: "'a nat_next \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list set" where
"regset d i j 0 = (if i=j then insert [] {[a] | a. d a i = j}
                          else {[a] | a. d a i = j})" |
"regset d i j (Suc k) =
  regset d i j k \<union>
  (regset d i k k) @@ (star(regset d k k k)) @@ (regset d k j k)"

definition
 regset_of_DA :: "('a,nat)da \<Rightarrow> nat \<Rightarrow> 'a list set" where
"regset_of_DA A k = (\<Union>j\<in>{j. j<k \<and> fin A j}. regset (next A) (start A) j k)"

definition
 bounded :: "'a nat_next \<Rightarrow> nat \<Rightarrow> bool" where
"bounded d k = (\<forall>n. n < k \<longrightarrow> (\<forall>x. d x n < k))"

declare
  in_set_butlast_appendI[simp,intro] less_SucI[simp] image_eqI[simp]

(* Lists *)

lemma butlast_empty[iff]:
  "(butlast xs = []) = (case xs of [] \<Rightarrow> True | y#ys \<Rightarrow> ys=[])"
by (cases xs) simp_all

lemma in_set_butlast_concatI:
 "x \<in> set(butlast xs) \<Longrightarrow> xs \<in> set xss \<Longrightarrow> x \<in> set(butlast(concat xss))"
  by (metis concat.simps(2) concat_append in_set_butlast_appendI split_list_first)

(* Regular sets *)

(* The main lemma:
   how to decompose a trace into a prefix, a list of loops and a suffix.
*)
lemma decompose[rule_format]:
 "\<forall>i. k \<in> set(trace d i xs) \<longrightarrow> (\<exists>pref mids suf.
  xs = pref @ concat mids @ suf \<and>
  deltas d pref i = k \<and> (\<forall>n\<in>set(butlast(trace d i pref)). n \<noteq> k) \<and>
  (\<forall>mid\<in>set mids. (deltas d mid k = k) \<and>
                  (\<forall>n\<in>set(butlast(trace d k mid)). n \<noteq> k)) \<and>
  (\<forall>n\<in>set(butlast(trace d k suf)). n \<noteq> k))"
apply (induct "xs")
 apply (simp)
apply (rename_tac a as)
apply (intro strip)
apply (case_tac "d a i = k")
 apply (rule_tac x = "[a]" in exI)
 apply simp
 apply (case_tac "k \<in> set(trace d (d a i) as)")
  apply (erule allE)
  apply (erule impE)
   apply (assumption)
  apply (erule exE)+
  apply (rule_tac x = "pref#mids" in exI)
  apply (rule_tac x = "suf" in exI)
  apply simp
 apply (rule_tac x = "[]" in exI)
 apply (rule_tac x = "as" in exI)
 apply simp
 apply (blast dest: in_set_butlastD)
apply simp
apply (erule allE)
apply (erule impE)
 apply (assumption)
apply (erule exE)+
apply (rule_tac x = "a#pref" in exI)
apply (rule_tac x = "mids" in exI)
apply (rule_tac x = "suf" in exI)
apply simp
done

lemma length_trace[simp]: "\<And>i. length(trace d i xs) = length xs"
by (induct "xs") simp_all

lemma deltas_append[simp]:
  "\<And>i. deltas d (xs@ys) i = deltas d ys (deltas d xs i)"
by (induct "xs") simp_all

lemma trace_append[simp]:
  "\<And>i. trace d i (xs@ys) = trace d i xs @ trace d (deltas d xs i) ys"
by (induct "xs") simp_all

lemma trace_concat[simp]:
 "(\<forall>xs \<in> set xss. deltas d xs i = i) \<Longrightarrow>
  trace d i (concat xss) = concat (map (trace d i) xss)"
by (induct "xss") simp_all

lemma trace_is_Nil[simp]: "\<And>i. (trace d i xs = []) = (xs = [])"
by (case_tac "xs") simp_all

lemma trace_is_Cons_conv[simp]:
 "(trace d i xs = n#ns) =
  (case xs of [] \<Rightarrow> False | y#ys \<Rightarrow> n = d y i \<and> ns = trace d n ys)"
by (auto simp: split: list.splits)

lemma set_trace_conv:
 "\<And>i. set(trace d i xs) =
  (if xs=[] then {} else insert(deltas d xs i)(set(butlast(trace d i xs))))"
  by (induct "xs") (simp_all add: insert_commute)

lemma deltas_concat[simp]:
 "(\<forall>mid\<in>set mids. deltas d mid k = k) \<Longrightarrow> deltas d (concat mids) k = k"
by (induct mids) simp_all

lemma lem: "[| n < Suc k; n \<noteq> k |] ==> n < k"
by arith

lemma regset_spec:
  "xs \<in> regset d i j k \<longleftrightarrow>
   ((\<forall>n\<in>set(butlast(trace d i xs)). n < k) \<and> deltas d xs i = j)"
proof (induction k arbitrary: i j xs)
  case 0
  then show ?case by (force split: list.split)
next
  case (Suc k)
  show ?case
  proof
    assume xs: "xs \<in> regset d i j (Suc k)"
    have *: "\<And>ys. ys \<in> star (regset d k k k)
       \<Longrightarrow> (\<forall>m\<in>set (butlast (trace d k ys)). m < Suc k) \<and> deltas d ys k = k"
      by (erule star_induct; simp add: Suc set_trace_conv butlast_append ball_Un)
    show "(\<forall>n\<in>set (butlast (trace d i xs)). n < Suc k) \<and> deltas d xs i = j"
      using xs Suc 
      apply (simp add: conc_def)
      apply (elim disjE exE conjE; simp add: set_trace_conv butlast_append ball_Un * Suc)
      done
  next
    assume \<section>: "(\<forall>n\<in>set (butlast (trace d i xs)). n < Suc k) \<and> deltas d xs i = j"
    show "xs \<in> regset d i j (Suc k)"
    proof (cases "k \<in> set(butlast(trace d i xs))")
      case True
      then obtain pref mids suf 
        where xs: "pref @ concat mids @ suf = xs"
          and k: "deltas d pref i = k"
          and "\<forall>n\<in>set (butlast (trace d i pref)). n \<noteq> k"
          and 2: "\<And>mid. mid\<in>set mids \<Longrightarrow> 
                     deltas d mid k = k \<and> (\<forall>n\<in>set (butlast (trace d k mid)). n \<noteq> k)"
          and 3: "\<forall>n\<in>set (butlast (trace d k suf)). n \<noteq> k"
        by (auto dest!: in_set_butlastD decompose)
      then have 4: "\<forall>n\<in>set (butlast (trace d i pref)). n < k"
        by (metis "\<section>" in_set_butlast_appendI lem trace_append xs)
      have 1: "set mids \<subseteq> regset d (deltas d pref i) (deltas d pref i) (deltas d pref i)"
        using xs k 2 
        apply (clarsimp simp: subset_iff Suc)
        using \<section> by (force intro: lem in_set_butlast_concatI)
      have "\<exists>xs ys. concat mids @ suf = xs @ ys \<and> xs \<in> star (regset d k k k) \<and> ys \<in> regset d k j k"
        using \<section> 
        apply (simp add: Suc 4 k xs)
        using 1 2 3 concat_in_star
        by (metis deltas_append deltas_concat in_set_butlast_appendI k linorder_neqE_nat
            not_less_eq trace_append xs)
      with "4" Suc k xs
      show ?thesis
        by (fastforce simp add: conc_def)
    next
      case False
      with Suc \<section> show ?thesis
        by (auto simp add: conc_def less_Suc_eq)
    qed
  qed
qed

lemma trace_below:
 "bounded d k \<Longrightarrow> \<forall>i. i < k \<longrightarrow> (\<forall>n\<in>set(trace d i xs). n < k)"
  unfolding bounded_def
  by (induct "xs") force+

lemma regset_below:
 "\<lbrakk>bounded d k; i < k; j < k\<rbrakk> \<Longrightarrow> regset d i j k = {xs. deltas d xs i = j}"
  by (force simp add: regset_spec dest: trace_below in_set_butlastD)

lemma deltas_below:
 "\<And>i. bounded d k \<Longrightarrow> i < k \<Longrightarrow> deltas d w i < k"
  unfolding bounded_def
  by (induct w) force+

lemma regset_DA_equiv:
 "\<lbrakk>bounded (next A) k; start A < k; j < k\<rbrakk> \<Longrightarrow> (w \<in> regset_of_DA A k) = accepts A w"
  unfolding regset_of_DA_def
  by (simp cong: conj_cong add: regset_below deltas_below accepts_def delta_def)

end
