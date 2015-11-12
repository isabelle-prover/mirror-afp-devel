(* Author: Tobias Nipkow *)

subsection {* Mixed Tree/List Representation *}

theory Pairing_Heap_List
imports
  Amor
  Priority_Queue_ops
  Lemmas_log
begin

text{* The Pairing Heap theory by Hauke Brinkop follows the original publication
\cite{FredmanSST86} and represents pairing heaps as binary trees, although conceptually
the type also involves lists and options. This theory makes these conceptual types explicit
while following Brinkop's proofs. As a consequence no invariants are necessary, but size
and potential functions need to be defined on multiple types. *}

datatype 'a hp = Hp 'a (hps: "'a hp list")

type_synonym 'a heap = "'a hp option"

fun lift_hp :: "'b \<Rightarrow> ('a hp \<Rightarrow> 'b) \<Rightarrow> 'a heap \<Rightarrow> 'b" where
"lift_hp c f None = c" |
"lift_hp c f (Some h) = f h"

fun merge :: "'a :: linorder hp \<Rightarrow> 'a hp \<Rightarrow> 'a hp" where
"merge (Hp x lx) (Hp y ly) = 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly))"

hide_const (open) insert

fun insert :: "'a \<Rightarrow> 'a :: linorder heap \<Rightarrow> 'a heap" where
"insert x None = Some(Hp x [])" |
"insert x (Some h) = Some(merge (Hp x []) h)"

fun pass\<^sub>1 :: "'a :: linorder hp list \<Rightarrow> 'a hp list" where
  "pass\<^sub>1 [] = []"
| "pass\<^sub>1 [h] = [h]" 
| "pass\<^sub>1 (h1#h2#hs) = merge h1 h2 # pass\<^sub>1 hs"

fun pass\<^sub>2 :: "'a :: linorder hp list \<Rightarrow> 'a heap" where
  "pass\<^sub>2 [] = None"
| "pass\<^sub>2 (h#hs) = Some(case pass\<^sub>2 hs of None \<Rightarrow> h | Some h' \<Rightarrow> merge h h')"

fun del_min :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "del_min None = None"
| "del_min (Some(Hp x hs)) = pass\<^sub>2 (pass\<^sub>1 hs)"

definition ld :: "nat \<Rightarrow> real" where
"ld x = (if x = 0 then 0 else log 2 x)"

lemma [simp]: "n \<noteq> 0 \<Longrightarrow> ld n = log 2 n"
by (simp add: ld_def)

fun szs :: "'a hp list \<Rightarrow> nat" where
"szs(Hp x hsl # hsr) = szs hsl + szs hsr + 1" |
"szs [] = 0"

definition sz :: "'a hp \<Rightarrow> nat" where
[simp]: "sz h = szs(hps h) + 1"

lemma sz_Hp[simp]: "sz(Hp x hs) = szs hs + 1"
by simp

fun \<phi> :: "'a hp list \<Rightarrow> real" where
"\<phi> [] = 0" |
"\<phi> (Hp x hsl # hsr) = \<phi> hsl + \<phi> hsr + log 2 (szs hsl + szs hsr + 1)"

definition \<Phi> :: "'a hp \<Rightarrow> real" where
[simp]: "\<Phi> h = \<phi> (hps h) + log 2 (szs(hps(h))+1)"

abbreviation \<Phi>o :: "'a heap \<Rightarrow> real" where
"\<Phi>o \<equiv> lift_hp 0 \<Phi>"

abbreviation szo :: "'a heap \<Rightarrow> nat" where
"szo \<equiv> lift_hp 0 sz"

lemma \<phi>_ge0: "\<phi> hs \<ge> 0"
by (induction hs rule: szs.induct) auto

declare algebra_simps[simp] of_nat_Suc[simp]

lemma szs_Cons[simp]: "szs(h # hs) = sz h + szs hs"
by(cases h) simp

lemma merge2: "merge (Hp x lx) h = (case h of (Hp y ly) \<Rightarrow> 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly)))"
by(simp split: hp.split)

lemma szs_merge: "szs(hps (merge h1 h2)) = sz h1 + sz h2 - 1" 
by (induction rule: merge.induct) simp_all

lemma pass\<^sub>1_size[simp]: "szs (pass\<^sub>1 hs) = szs hs" 
by (induct hs rule: pass\<^sub>1.induct) (simp_all add: szs_merge)

lemma pass\<^sub>2_None[simp]: "pass\<^sub>2 hs = None \<longleftrightarrow> hs = []"
by(cases hs) auto

lemma \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t: "\<Phi>o (insert x h) - \<Phi>o h \<le> log 2 (szo h + 1)"
by(induct h)(auto simp: merge2 split: hp.split)

lemma \<Delta>\<Phi>\<^sub>m\<^sub>e\<^sub>r\<^sub>g\<^sub>e: "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2 * log 2 (sz h1 + sz h2)"
by (induction h1 h2 rule: merge.induct) (simp  add: add_increasing)

fun sum_ub :: "'a hp list \<Rightarrow> real" where
  "sum_ub [] = 0"
| "sum_ub [Hp _ _] = 0"
| "sum_ub [Hp _ lx, Hp _ ly] = 2*log 2 (2 + szs lx + szs ly)" 
| "sum_ub (Hp _ lx # Hp _ ly # ry) = 2*log 2 (2 + szs lx + szs ly + szs ry) 
    - 2*log 2 (szs ry) - 2 + sum_ub ry"


lemma \<Delta>\<Phi>_pass1_sum_ub: "\<phi> (pass\<^sub>1 h) - \<phi> h  \<le> sum_ub h"
proof (induction h rule: sum_ub.induct)
  case (3 lx x ly y)
  have 0: "\<And>x y::real. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> x \<le> 2*y" by linarith
  show ?case by (simp add: add_increasing 0)
next
  case (4 x hsx y hsy z hsz)
  let ?ry = "z # hsz"
  let ?rx = "Hp y hsy # ?ry"
  let ?h = "Hp x hsx # ?rx"
  have "\<phi>(pass\<^sub>1 ?h) - \<phi> ?h  
    \<le> log 2 (1 + szs hsx + szs hsy) - log 2 (1 + szs hsy + szs ?ry) + sum_ub ?ry"
    using "4.IH" by simp
  also have "log 2 (1 + szs hsx + szs hsy) - log 2 (1 + szs hsy + szs ?ry) 
    \<le> 2*log 2 (szs ?h) - 2*log 2 (szs ?ry) - 2"
  proof -
    have "log 2 (1 + szs hsx + szs hsy) + log 2 (szs ?ry) - 2*log 2 (szs ?h) 
      = log 2 ((1 + szs hsx + szs hsy)/(szs ?h) ) + log 2 (szs ?ry / szs ?h)"
      by (simp add: log_divide)
    also have "\<dots> \<le> -2" 
    proof -
      have "2 + \<dots>
        \<le> 2*log 2 ((1 + szs hsx + szs hsy) / szs ?h +  szs ?ry / szs ?h)"  
        using ld_sum_inequality [of "(1 + szs hsx + szs hsy) / szs ?h" "(szs ?ry / szs ?h)"] by simp
      also have "\<dots> \<le> 0" by (simp add: field_simps log_divide add_pos_nonneg)
      finally show ?thesis by linarith
    qed 
    finally have "log 2 (1 + szs hsx + szs hsy) + log 2 (szs ?ry) + 2
      \<le>  2*log 2 (szs ?h)" by simp
    moreover have "log 2 (szs ?ry) \<le> log 2 (szs ?rx)" by simp
    ultimately have "log 2 (1 + szs hsx + szs hsy) - \<dots> 
      \<le>  2*log 2 (szs ?h) - 2*log 2 (szs ?ry) - 2" by linarith
    thus ?thesis by simp
  qed
  finally show ?case by (simp)
qed simp_all


lemma \<Delta>\<Phi>_pass1: "\<phi> (pass\<^sub>1 h) - \<phi> h \<le> 2*ld(szs h) - length h + 2"
proof - 
  have "sum_ub h \<le> 2*ld(szs h) - length h + 2" 
    by (induct h rule: sum_ub.induct) (simp_all add: ld_def)
  thus ?thesis using \<Delta>\<Phi>_pass1_sum_ub[of h] by linarith
qed

lemma szs_pass2: "pass\<^sub>2 hs = Some h \<Longrightarrow> szs hs = szs(hps h)+1"
apply(induction hs arbitrary: h rule: \<phi>.induct)
apply (auto simp: merge2 split: option.split hp.split)
done

lemma \<Delta>\<Phi>_pass2: "\<Phi>o (pass\<^sub>2 hs) - \<phi> hs \<le> ld (szs hs)"
proof (induction hs)
  case (Cons h hs)
  thus ?case
  proof -
    obtain x hs2 where [simp]: "h = Hp x hs2" by (metis hp.exhaust)
    show ?thesis
    proof (cases "pass\<^sub>2 hs")
      case [simp]: (Some h2)
      obtain y hs3 where [simp]: "h2 = Hp y hs3" by (metis hp.exhaust)
      from szs_pass2[OF Some] Cons show ?thesis by(auto simp: add_mono)
    qed simp
  qed
qed (simp add: ld_def)

lemma \<Delta>\<Phi>\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e\<^sub>M\<^sub>i\<^sub>n:  "\<Phi>o (del_min (Some h)) - \<Phi>o (Some h) 
  \<le> 3*ld(szs(hps h)) - length(hps h) + 2"
proof -
  let ?\<Delta>\<Phi>\<^sub>1 = "\<phi>(hps h) - \<Phi> h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>o(pass\<^sub>2(pass\<^sub>1 (hps h))) - \<phi> (hps h)"
  let ?\<Delta>\<Phi> = "\<Phi>o (del_min (Some h)) - \<Phi>o (Some h)"
  have "\<Phi>o(pass\<^sub>2(pass\<^sub>1(hps h))) - \<phi> (pass\<^sub>1(hps h)) \<le> ld (szs(hps h))" 
    using \<Delta>\<Phi>_pass2[of "pass\<^sub>1(hps h)"] by (metis pass\<^sub>1_size)
  moreover have "\<phi> (pass\<^sub>1 (hps h)) - \<phi> (hps h) \<le>  2*\<dots> - length (hps h) + 2"
    using \<Delta>\<Phi>_pass1 by blast
  moreover have "?\<Delta>\<Phi>\<^sub>1 \<le> 0" by (cases h) simp
  moreover have "?\<Delta>\<Phi> = ?\<Delta>\<Phi>\<^sub>1 + ?\<Delta>\<Phi>\<^sub>2" by (cases h) simp
  ultimately show ?thesis by linarith
qed

fun nxt :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "nxt Del_min h = del_min h"
| "nxt (Insert x) h = insert x h"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 :: "'a hp list \<Rightarrow> real" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 [] = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 [_] = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (_ # _ # hs) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 hs"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 :: "'a hp list \<Rightarrow> real" where
 "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 [] = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (_ # hs) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 hs"

fun t :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap \<Rightarrow> real" where
  "t Del_min None = 1"
| "t Del_min (Some(Hp x hs)) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 hs) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 hs"
| "t (Insert a) _ = 1"

fun U :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap \<Rightarrow> real" where
 "U (Insert a) h = log 2 (szo h + 1) + 1"
| "U Del_min h = 3*log 2 (szo h + 1) + 5"

interpretation pairing: amor where 
init = "None" and nxt = nxt and t = t and inv = "\<lambda>_. True" and \<Phi> = \<Phi>o and U = U
proof
  case goal3 show ?case by (cases s) (auto simp: \<phi>_ge0)
next
  case goal5 show ?case
  proof (cases f)
    case [simp]: (Insert x)
    have "\<Phi>o (insert x s) - \<Phi>o s \<le> log 2 (1 + szo s)" using \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t by auto
    thus ?thesis by simp
  next
    case [simp]: (Del_min)
    show ?thesis
    proof (cases s)
      case [simp]: (Some h)
        show ?thesis
        proof (cases h)
        case [simp]: (Hp x hs)
        have "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 hs) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 hs \<le> 2 + length hs"
          by (induct hs rule: pass\<^sub>1.induct) simp_all
        hence  "t f s \<le> 1 + \<dots>" by simp
        moreover have  "\<Phi>o (del_min s) - \<Phi>o s \<le> 3*ld(szs hs) - length hs + 2"
          using  \<Delta>\<Phi>\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e\<^sub>M\<^sub>i\<^sub>n[of h] by simp
        moreover have "ld(szs hs) \<le> ld (szo s + 1)" by (simp add: ld_def)
        ultimately show ?thesis by simp
      qed
    qed simp
  qed
qed simp_all

end