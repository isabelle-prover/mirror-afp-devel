(* Author: Tobias Nipkow (based on Hauke Brinkop's tree proofs) *)

subsection \<open>Okasaki's Pairing Heap (Modified)\<close>

theory Pairing_Heap_List2_Analysis
imports
  Pairing_Heap.Pairing_Heap_List2
  Amortized_Framework
  Priority_Queue_ops_merge
  Lemmas_log
  "HOL-Data_Structures.Define_Time_Function"
begin

text
\<open>Amortized analysis of a modified version of the pairing heaps defined by Okasaki \<^cite>\<open>"Okasaki"\<close>.
Simplified version of proof in the Nipkow and Brinkop paper.\<close>

fun lift_hp :: "'b \<Rightarrow> ('a hp \<Rightarrow> 'b) \<Rightarrow> 'a heap \<Rightarrow> 'b" where
"lift_hp c f None = c" |
"lift_hp c f (Some h) = f h"

consts sz :: "'a \<Rightarrow> nat"

overloading
size_hps \<equiv> "sz :: 'a hp list \<Rightarrow> nat"
size_hp \<equiv> "sz :: 'a hp \<Rightarrow> nat"
size_heap \<equiv> "sz :: 'a heap \<Rightarrow> nat"
begin

fun size_hps :: "'a hp list \<Rightarrow> nat" where
"size_hps(Hp x hsl # hsr) = size_hps hsl + size_hps hsr + 1" |
"size_hps [] = 0"

definition size_hp :: "'a hp \<Rightarrow> nat" where
[simp]: "size_hp h = sz(hps h) + 1"

definition size_heap :: "'a heap \<Rightarrow> nat" where
[simp]: "size_heap \<equiv> lift_hp 0 sz"

end

consts \<Phi> :: "'a \<Rightarrow> real"

overloading
\<Phi>_hps \<equiv> "\<Phi> :: 'a hp list \<Rightarrow> real"
\<Phi>_hp \<equiv> "\<Phi> :: 'a hp \<Rightarrow> real"
\<Phi>_heap \<equiv> "\<Phi> :: 'a heap \<Rightarrow> real"
begin

fun \<Phi>_hps :: "'a hp list \<Rightarrow> real" where
"\<Phi>_hps [] = 0" |
"\<Phi>_hps (Hp x hsl # hsr) = \<Phi>_hps hsl + \<Phi>_hps hsr + log 2 (sz hsl + sz hsr + 1)"

definition \<Phi>_hp :: "'a hp \<Rightarrow> real" where
[simp]: "\<Phi>_hp h = \<Phi> (hps h) + log 2 (sz(hps(h))+1)"

definition \<Phi>_heap :: "'a heap \<Rightarrow> real" where
[simp]: "\<Phi>_heap \<equiv> lift_hp 0 \<Phi>"

end

lemma \<Phi>_hps_ge0: "\<Phi> (hs::_ hp list) \<ge> 0"
by (induction hs rule: size_hps.induct) auto

declare algebra_simps[simp]

lemma sz_hps_Cons[simp]: "sz(h # hs) = sz (h::_ hp) + sz hs"
by(cases h) simp

lemma link2: "link (Hp x lx) h = (case h of (Hp y ly) \<Rightarrow> 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly)))"
by(simp split: hp.split)

lemma sz_hps_link: "sz(hps (link h1 h2)) = sz h1 + sz h2 - 1" 
by (induction rule: link.induct) simp_all

lemma pass\<^sub>1_size[simp]: "sz (pass\<^sub>1 hs) = sz hs" 
by (induction hs rule: pass\<^sub>1.induct) (simp_all add: sz_hps_link)

lemma pass\<^sub>2_None[simp]: "pass\<^sub>2 hs = None \<longleftrightarrow> hs = []"
by(cases hs) auto

lemma \<Delta>\<Phi>_insert:
  "\<Phi> (Pairing_Heap_List2.insert x h) - \<Phi> h \<le> log 2 (sz h + 1)"
by(cases h)(auto simp: link2 split: hp.split)

lemma \<Delta>\<Phi>_link: "\<Phi> (link h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2 * log 2 (sz h1 + sz h2)"
by (cases "(h1,h2)" rule: link.cases) (simp  add: add_increasing)
(* unused
lemma \<Phi>_Cons: "\<Phi> (h # hs) = \<Phi>(hps h) + \<Phi> hs + log 2 (sz(hps h) + sz hs + 1)"
by(cases h) simp

lemma \<Phi>_hps_link:
  "\<Phi> (hps(link h1 h2)) = \<Phi> (hps h1) + \<Phi> (hps h2) + log 2 (sz h1+sz h2-1)"
by (cases "(h1,h2)" rule: link.cases) (simp)

lemma \<Phi>_link:
  "\<Phi> (link h1 h2) = \<Phi> (hps h1) + \<Phi> (hps h2) + log 2 (sz h1+sz h2-1) + log 2 (sz h1+sz h2)"
by (cases "(h1,h2)" rule: link.cases) (simp)
*)
lemma \<Delta>\<Phi>_pass1: "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs  \<le> 2 * log 2 (sz hs + 1) - length hs + 2"
proof (induction hs rule: pass\<^sub>1.induct)
  case (3 h1 h2 hs)
  let ?h12s = "h1 # h2 # hs" let ?m = "sz hs"
  obtain x1 hs1 x2 hs2 where h12: "h1 = Hp x1 hs1" "h2 = Hp x2 hs2"
    using hp.exhaust_sel by blast
  let ?n1 = "sz hs1" let ?n2 = "sz hs2"
  have "\<Phi> (pass\<^sub>1 ?h12s) - \<Phi> ?h12s = \<Phi> (pass\<^sub>1 hs) + log 2 (?n1+?n2+1) - \<Phi> hs - log 2 (?n2+?m+1)" 
    by (simp add: h12)
  also have "\<dots> \<le> log 2 (?n1+?n2+1) - log 2 (?n2+?m+1) + 2 * log 2 (?m+1) - length hs + 2" 
    using 3 by (simp)
  also have "\<dots> \<le> 2 * log 2 (?n1+?n2+?m+2) - log 2 (?n2+?m+1) + log 2 (?m+1) - length hs" 
        using ld_sum_inequality [of "?n1+?n2+1" "?m+1"] by(simp)
  also have "\<dots> \<le> 2 * log 2 (?n1+?n2+?m+2) - length hs" by simp
  also have "\<dots> = 2 * log 2 (sz ?h12s) - length ?h12s + 2" using h12 by simp
  also have "\<dots> \<le> 2 * log 2 (sz ?h12s + 1) - length ?h12s + 2" using h12 by simp
  finally show ?case .
qed simp_all

lemma size_hps_pass2: "sz(pass\<^sub>2 hs) = sz hs"
apply(induction hs rule: pass\<^sub>2.induct)
apply(auto simp: sz_hps_link split: option.split)
done

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> [] \<Longrightarrow> \<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (sz hs)"
proof (induction hs)
  case IH: (Cons h1 hs')
  obtain x hs1 where [simp]: "h1 = Hp x hs1" by (metis hp.exhaust)
  show ?case
  proof (cases "hs' = []")
    case False
    then obtain h2 where [simp]: "pass\<^sub>2 hs' = Some h2" by fastforce
    then obtain y hs2 where [simp]: "h2 = Hp y hs2" by (metis hp.exhaust)
(* automatic: *)
    from False size_hps_pass2[of hs',symmetric] IH(1) have ?thesis
      by(simp add: add_mono)
(* explicit: *)
    let ?n1 = "sz hs1" let ?n2 = "sz hs2"
    have *: "\<Phi> (link h1 h2) = \<Phi> hs1 + \<Phi> hs2 + log 2 (?n1+?n2+1) + log 2 (?n1+?n2+2)"
      by simp
    have [simp]: "sz hs' = sz hs2 + 1" using size_hps_pass2[of hs'] by simp
    hence IH2: "\<Phi> (hs2) - \<Phi> hs' \<le> 0" using IH(1)[OF False] by simp
    have "\<Phi> (pass\<^sub>2 (h1 # hs')) - \<Phi> (h1 # hs') = \<Phi> (link h1 h2) - (\<Phi> hs1 + \<Phi> hs' + log 2 (?n1+sz hs'+1))"
      by simp
    also have "\<dots> = \<Phi> hs2 + log 2 (?n1+?n2+1) - \<Phi> hs'"
      using * by simp
    also have "\<dots> \<le> log 2 (?n1+?n2+1)"
      using IH2 by simp
    also have "\<dots> \<le> log 2 (sz(h1 # hs'))" by simp
    finally show ?thesis .
  qed simp
qed simp

corollary \<Delta>\<Phi>_pass2': "\<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (sz hs + 1)"
proof cases
  assume "hs = []" thus ?thesis by simp
next
  assume "hs \<noteq> []"
  hence "log 2 (sz hs) \<le> log 2 (sz hs + 1)" by (auto simp:  neq_Nil_conv)
  then show ?thesis using \<Delta>\<Phi>_pass2[OF \<open>hs \<noteq> []\<close>] by linarith
qed

lemma \<Delta>\<Phi>_del_min:
shows "\<Phi> (del_min (Some h)) - \<Phi> (Some h) 
  \<le> 2 * log 2 (sz(hps h) + 1) - length (hps h) + 2"
proof -
  obtain x hs where [simp]: "h = Hp x hs" by (meson hp.exhaust_sel)
  have "\<Phi> (del_min (Some h)) - \<Phi> (Some h) =
        \<Phi> (pass\<^sub>2 (pass\<^sub>1 hs)) - (log 2 (sz hs + 1) + \<Phi> hs)" by simp
  also have "\<dots> \<le> \<Phi> (pass\<^sub>1 hs) - \<Phi> hs"
    using \<Delta>\<Phi>_pass2'[of "pass\<^sub>1 hs"] by(simp)
  also have "\<dots> \<le> 2 * log 2 (sz hs + 1) - length hs + 2" by(rule \<Delta>\<Phi>_pass1)
  finally show ?thesis by simp
qed

time_fun link

lemma T_link_0[simp]: "T_link h1 h2 = 0"
by (cases "(h1,h2)" rule: T_link.cases) auto

time_fun pass\<^sub>1

time_fun pass\<^sub>2

time_fun del_min

time_fun Pairing_Heap_List2.insert

lemma T_insert_0[simp]: "T_insert a h = 0"
by (cases h) auto

time_fun merge

lemma T_merge_0[simp]: "T_merge h1 h2 = 0"
by (cases "(h1,h2)" rule: merge.cases) auto

lemma A_insert: "T_insert a ho + \<Phi>(Pairing_Heap_List2.insert a ho) - \<Phi> ho \<le> log 2 (sz ho + 1)"
using \<Delta>\<Phi>_insert by auto

lemma A_merge:
  "T_merge ho1 ho2 + \<Phi> (merge ho1 ho2) - \<Phi> ho1 - \<Phi> ho2 \<le> 2 * log 2 (sz ho1 + sz ho2 + 1)"
proof (cases "(ho1,ho2)" rule: merge.cases)
  case (3 h1 h2)
  then show ?thesis using \<Delta>\<Phi>_link[of "the ho1" "the ho2"] apply auto
    by (smt (verit, best) log_mono of_nat_0_le_iff)
qed auto

lemma A_del_min:
  "T_del_min ho + \<Phi> (del_min ho) - \<Phi> ho \<le> 2*log 2 (sz ho + 1) + 4"
proof (cases ho)
  case [simp]: (Some h)
  show ?thesis
  proof (cases h)
    case [simp]: (Hp x hs)
    have "T_pass\<^sub>2 (pass\<^sub>1 hs) + T_pass\<^sub>1 hs \<le> 2 + length hs"
      by (induct hs rule: T_pass\<^sub>1.induct) (auto split: option.split)
    hence  "T_del_min ho  \<le> \<dots>" by simp
    moreover
    have "\<Phi> (del_min ho) - \<Phi> ho \<le> 2*log 2 (sz ho) - length hs + 2"
      using  \<Delta>\<Phi>_del_min[of h] by (simp)
    moreover
    have "\<dots> \<le> 2*log 2 (sz ho + 1) - length hs + 2" by simp
    ultimately show ?thesis
      by linarith
  qed
qed simp


fun exec :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> 'a heap" where
"exec Empty [] = None" | 
"exec Del_min [h] = del_min h" |
"exec (Insert x) [h] = Pairing_Heap_List2.insert x h" |
"exec Merge [h1,h2] = merge h1 h2"

fun cost :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> nat" where
"cost Empty _ = 0" |
"cost Del_min [h] = T_del_min h" |
"cost (Insert a) [h] = T_insert a h" |
"cost Merge [h1,h2] = T_merge h1 h2"

fun U :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> real" where
"U Empty _ = 0" |
"U (Insert a) [h] = log 2 (sz h + 1)" |
"U Del_min [h] = 2*log 2 (sz h + 1) + 4" |
"U Merge [h1,h2] = 2*log 2 (sz h1 + sz h2 + 1)"

interpretation pairing: Amortized
where arity = arity and exec = exec and cost = cost and inv = "\<lambda>_. True"
and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (2 s) show ?case by (cases s) (auto simp: \<Phi>_hps_ge0)
next
  case (3 ss f) show ?case
  proof (cases f)
    case Empty with 3 show ?thesis by(auto)
  next
    case Insert
    thus ?thesis using Insert A_insert 3 by auto
  next
    case [simp]: Del_min
    then obtain ho where "ss = [ho]" using 3 by auto
    thus ?thesis using A_del_min by fastforce
  next
    case [simp]: Merge
    then obtain ho1 ho2 where "ss = [ho1, ho2]"
      using 3 by(auto simp: numeral_eq_Suc)
    thus ?thesis using A_merge by auto
  qed
qed simp

end
