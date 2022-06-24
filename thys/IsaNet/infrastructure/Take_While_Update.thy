theory Take_While_Update imports Tools
begin

(******************************************************************************)
section \<open>Extending @{text "Take_While"} with an additional, mutable parameter\<close>
(******************************************************************************)

text\<open>This theory defines takeW, holds and extract similarly to the other @{text "Take_While"} theory, but removes 
the predecessor parameter and adds a parameter to P and an update function that is applied to this parameter.
In our formalization, the additional parameter is the uinfo field and the update function is the update
on uinfo fields.\<close>

locale TWu =
  fixes P :: "('b \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> bool)"
  fixes upd :: "('b \<Rightarrow> 'a \<Rightarrow> 'b)"
begin

subsection\<open>Definitions\<close>

text\<open>Apply @{text "upds"} on a sequence\<close>
abbreviation upds :: "'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
  "upds \<equiv> foldl upd"

fun upd_opt :: "('b \<Rightarrow> 'a option \<Rightarrow> 'b)" where
  "upd_opt info (Some hf) = upd info hf"
| "upd_opt info None = info"

text\<open>holds returns true iff every element of a list, together with its context, satisfies P.\<close>
fun holds :: "'b \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "holds info (x # y # ys) nxt \<longleftrightarrow> P info x (Some y) \<and> holds (upd info y) (y # ys) nxt"
| "holds info [x] nxt \<longleftrightarrow> P info x nxt"
| "holds info [] nxt \<longleftrightarrow> True"

text\<open>holds returns the longest prefix of a list for every element, together with its context, satisfies P.\<close>
function takeW :: "'b \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> 'a list" where
  "takeW _ [] _ = []"
| "P info x xo \<Longrightarrow> takeW info [x] xo = [x]"
| "\<not> P info x xo \<Longrightarrow> takeW info [x] xo = []"
| "P info x (Some y) \<Longrightarrow> takeW info (x # y # xs) xo = x # takeW (upd info y) (y # xs) xo"
| "\<not> P info x (Some y) \<Longrightarrow> takeW info (x # y # xs) xo = []"
apply auto
  by (metis remdups_adj.cases)
termination
  by lexicographic_order

text\<open>extract returns the last element of a list, or nxt if the list is empty.\<close>
fun "extract" :: "'b \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  "extract info (x # y # ys) nxt = (if P info x (Some y) then extract (upd info y) (y # ys) nxt else Some x)"
| "extract info [x] nxt = (if P info x nxt then nxt else (Some x))"
| "extract info [] nxt = nxt"


subsection\<open>Lemmas\<close>

text \<open>Lemmas packing singleton and at least two element cases into a single equation.\<close>

lemma takeW_singleton:
  "takeW info [x] xo = (if P info x xo then [x] else [])"
by (simp)

lemma takeW_two_or_more:
  "takeW info (x # y # zs) xo = (if P info x (Some y) then x # takeW (upd info y) (y # zs) xo else [])"
by (simp)


text \<open>Some lemmas for splitting the tail of the list argument.\<close>

text \<open>Splitting lemma formulated with if-then-else rather than case.\<close>

lemma takeW_split_tail:
  "takeW info (x # xs) nxt =
     (if xs = []
      then (if P info x nxt then [x] else [])
      else (if P info x (Some (hd xs)) then x # takeW (upd info (hd xs)) xs nxt else []))"
by (cases xs, auto)

lemma extract_split_tail:
  "extract info (x # xs) nxt =
     (case xs of
          [] \<Rightarrow> (if P info x nxt then nxt else (Some x))
        | (y # ys) \<Rightarrow> (if P info x (Some y) then extract (upd info y) (y # ys) nxt else Some x))"
by (cases xs, auto)

lemma holds_split_tail:
  "holds info (x # xs) nxt \<longleftrightarrow>
      (case xs of
          [] \<Rightarrow> P info x nxt
        | (y # ys) \<Rightarrow> P info x (Some y) \<and> holds (upd info y) (y # ys) nxt)"
by (cases xs, auto)

lemma holds_Cons_P:
  "holds info (x # xs) nxt \<Longrightarrow> \<exists>y . P info x y"
by (cases xs, auto)

lemma holds_Cons_holds:
  "holds info (x # xs) nxt \<Longrightarrow> holds (upd_opt info (head xs)) xs nxt"
by (cases xs, auto)

lemmas tail_splitting_lemmas =
  extract_split_tail holds_split_tail

text \<open>Interaction between @{term holds}, @{term takeWhile}, and @{term extract}.\<close>
declare if_split_asm [split]

lemma holds_takeW_extract: "holds info (takeW info xs nxt) (extract info xs nxt)"
apply(induction info xs nxt rule: takeW.induct)
apply auto
subgoal for info x y ys
  apply(cases "ys")
  apply(simp_all)
  done
done

text \<open>Interaction of @{term holds}, @{term takeWhile}, and @{term extract}
with @{term append}.\<close>

lemma holds_append:
  "holds info (xs @ ys) nxt =
   (case ys of [] \<Rightarrow> holds info xs nxt | x # _ \<Rightarrow> 
     holds info xs (Some x) \<and> 
     (case xs of [] \<Rightarrow> holds info ys nxt 
                | _ \<Rightarrow> holds (upds info (tl xs@[x])) ys nxt))"
  by(induction info xs nxt rule: takeW.induct)
    (auto split: list.split)

lemma upds_snoc: "upds uinfo (xs@[x]) = upd (upds uinfo xs) x" 
  by simp


lemma takeW_prefix:
  "prefix (takeW info l nxt) l"
by (induction info l nxt rule: takeW.induct) auto

lemma takeW_set: "t \<in> set (TWu.takeW P upd info l nxt) \<Longrightarrow> t \<in> set l"
by(auto intro: takeW_prefix elim: set_prefix)

lemma holds_implies_takeW_is_identity:
  "holds info l nxt \<Longrightarrow> takeW info l nxt = l"
by (induction info l nxt rule: takeW.induct) auto

(*even stronger...*)
lemma holds_takeW_is_identity[simp]:
  "takeW info l nxt = l \<longleftrightarrow> holds info l nxt"
  by (induction info l nxt rule: takeW.induct) auto


lemma takeW_takeW_extract:
  "takeW info (takeW info l nxt) (extract info l nxt)
 = takeW info l nxt"
using holds_takeW_extract holds_implies_takeW_is_identity
  by blast

(******************************************************************************)
subsubsection \<open>Holds unfolding\<close>
(******************************************************************************)
text \<open>This section contains various lemmas that show how one can deduce P info' x' nxt' for some of
        info' x' nxt' out of a list l, for which we know that holds info l nxt is true.\<close>

lemma holds_set_list: "\<lbrakk>holds info l nxt; x \<in> set l\<rbrakk> \<Longrightarrow> \<exists> p y . P p x y"
  apply(induction info l nxt rule: TWu.takeW.induct[where ?Pa="P"]) by auto

lemma holds_set_list_no_update: "\<lbrakk>holds info l nxt; x \<in> set l; \<And>a b. upd a b = a\<rbrakk> \<Longrightarrow> \<exists> y . P info x y"
  apply(induction info l nxt rule: TWu.takeW.induct[where ?Pa="P"]) by auto

lemma holds_unfold: "holds info l None \<Longrightarrow>
  l = [] \<or>
  (\<exists> x . l = [x] \<and> P info x None) \<or>
  (\<exists> x y ys . l = (x#y#ys) \<and> P info x (Some y) \<and> holds (upd info y) (y#ys) None)"
  by auto (meson holds.elims(2))

lemma holds_unfold_prexnxt': (*weakened!*)
  "\<lbrakk>holds info l nxt; l = (zs@(x1#x2#xs)); zs \<noteq> []\<rbrakk>
 \<Longrightarrow> P (upds info ((tl zs)@[x1])) x1 (Some x2)"
  apply(cases zs) apply simp
  apply(simp only: TWu.holds_append)
  by auto

lemma holds_suffix:
  "\<lbrakk>holds info l nxt; suffix l' l\<rbrakk> \<Longrightarrow> \<exists> info'. holds info' l' nxt"
  apply(cases l')
  by(auto simp add: suffix_def TWu.holds_append list.case_eq_if)

lemma holds_unfold_prelnil:
  "\<lbrakk>holds info l nxt; l = (zs@(x1#[])); zs \<noteq> []\<rbrakk>
 \<Longrightarrow> P (upds info ((tl zs)@[x1])) x1 nxt"
  apply(cases zs) 
   subgoal by simp
  by(simp only: TWu.holds_append) auto


(******************************************************************************)
subsubsection \<open>Update shifted\<close>
(******************************************************************************)
text\<open>Usually, the update has already been applied to the head of the list. Hence, when given a list
to apply updates to (and a successor, i.e., the first element that comes after the list), we remove 
the first element of the list and add the successor. We apply the updates on the resulting list.\<close>

fun upd_shifted :: "('b \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'b)" where
  "upd_shifted uinfo (x#xs) nxt = upds uinfo (xs@[nxt])"
| "upd_shifted uinfo [] nxt = uinfo"


text\<open>This lemma is useful when there is an intermediate hop field hf of interest.\<close>
lemma holds_intermediate:
  assumes "holds uinfo p nxt" "p = pre @ hf # post"
  shows "holds (upd_shifted uinfo pre hf) (hf # post) nxt"
using assms proof(induction pre arbitrary: p uinfo hf)
  case Nil
  then show ?case using assms by auto
next
  case induct_asm: (Cons a prev) 
  show ?case
  proof(cases prev)
    case Nil
    then have "holds (upd uinfo hf) (hf # post) nxt" 
      using induct_asm by simp
    then show ?thesis 
      using induct_asm Nil by auto
  next
    case cons_asm: (Cons b list)
    then have "holds (upd uinfo b) (b # list @ hf # post) nxt" 
      using induct_asm(2-3) by auto 
    then show ?thesis
      using induct_asm(1)
      by (simp add: cons_asm)
  qed
qed

lemma holds_intermediate_ex:
  assumes "holds uinfo hfs nxt" "hf \<in> set hfs"
  shows "\<exists>pre post . holds (upd_shifted uinfo pre hf) (hf # post) nxt \<and> hfs = pre @ hf # post"
  using assms holds_intermediate
  by (meson split_list) 


end

end