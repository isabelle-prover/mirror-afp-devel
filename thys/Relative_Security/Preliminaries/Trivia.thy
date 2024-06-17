section \<open>Trivia\<close>

text \<open> This theory contains some preliminary facts about lists and lazy-lists, including 
coinduction for filtermap. \<close>


theory Trivia
imports Main "HOL-Library.Sublist" More_LazyLists.LazyList_Filtermap
begin

subsection \<open>Facts about lists\<close>

lemma butlast_append2[simp]: "butlast (ys @ [y, y']) = (ys @ [y])"
  by (metis butlast_append butlast_snoc list.discI two_singl_Rcons)

(* *)

lemma less2_induct[case_names less]: 
assumes "(\<And>(x::nat) (a::nat). (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. b < a \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::nat,b::nat),(x,a)) . y < x \<or> y = x \<and> b < a}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . x < y}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed

lemma less2_induct'[case_names less]: 
assumes "(\<And>(x::'a::wellorder) (a::'w::wellorder). (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. b < a \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::'a::wellorder,b::'w::wellorder),(x,a)) . y < x \<or> y = x \<and> b < a}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . x < y}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed

lemma less2_induct''[consumes 1, case_names less]: 
assumes W: "wf (W::'w rel)" and 
"(\<And>(x::'a::wellorder) a. (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. (b,a) \<in> W \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::'a::wellorder,b::'w),(x,a)) . y < x \<or> y = x \<and> (b,a) \<in> W}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . (x,y) \<in> W}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 using W by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed

(* *)

lemma drop_Suc: "n < length xs \<Longrightarrow> drop n xs = Cons (nth xs n) (drop (Suc n) xs)" 
by (simp add: Cons_nth_drop_Suc)

lemma append_take_nth_drop: "n < length xs \<Longrightarrow>
  append (take n xs) (Cons (nth xs n) (drop (Suc n) xs)) = xs"
by (metis append_take_drop_id drop_Suc)   

lemmas list_all_nth = list_all_length

lemma list_all_hd:
  assumes \<open>list_all P xs\<close>
      and \<open>xs \<noteq> []\<close>
    shows \<open>P (hd xs)\<close>
  using assms by (metis list.collapse list_all_simps(1))

lemma measure_induct2[case_names IH]:
fixes meas :: "'a \<Rightarrow> 'b \<Rightarrow> nat"
assumes "\<And>x1 x2. (\<And>y1 y2. meas y1 y2 < meas x1 x2 \<Longrightarrow> S y1 y2) \<Longrightarrow> S x1 x2"
shows "S x1 x2"
proof-
  let ?m = "\<lambda> x1x2. meas (fst x1x2) (snd x1x2)" let ?S = "\<lambda> x1x2. S (fst x1x2) (snd x1x2)"
  have "?S (x1,x2)"
  apply(rule measure_induct[of ?m ?S])
  using assms by (metis fst_conv snd_conv)
  thus ?thesis by auto
qed

(* Notation for being a member in a list:  *)
abbreviation lmember ("(_/ \<in>\<in> _)" [50, 51] 50) where "x \<in>\<in> xs \<equiv> x \<in> set xs"

(* Mapping elements to lists followed by concatenation: *)
abbreviation  cmap :: "('b \<Rightarrow> 'a list) \<Rightarrow> 'b list \<Rightarrow> 'a list" where 
"cmap ff aal \<equiv> concat (map ff aal)"

lemma cmap_empty:
assumes "\<forall> x. x \<in>\<in> xl \<longrightarrow> ff x = []"
shows "cmap ff xl = []"
using assms by (induct xl) auto

lemma cmap_cong_empty:
assumes "\<forall> x. ff x = [] \<and> gg x = []"
shows "cmap ff xl = cmap gg yl"
using assms by (auto simp: cmap_empty)

lemma list_ex_cmap:
"list_ex P (cmap f xs) \<longleftrightarrow> (\<exists> x. x \<in>\<in> xs \<and> list_ex P (f x))"
by (induction xs) auto

lemma not_list_ex_filter:
assumes "\<not> list_ex P xs" shows "filter P xs = []"
using assms by (induct xs) auto

lemma cmap_filter_cong:
assumes "\<And> x u. x \<in>\<in> xs \<Longrightarrow> u \<in>\<in> ff x \<Longrightarrow> (q x \<longleftrightarrow> p u)"
and "\<And> x. x \<in>\<in> xs \<Longrightarrow> q x \<Longrightarrow> gg x = ff x"
shows "cmap ((filter p) o ff) xs = cmap gg (filter q xs)"
using assms by (induction xs) fastforce+

lemma cmap_cong:
  assumes "xs = ys" and "\<And>x. x \<in>\<in> xs \<Longrightarrow> ff x = gg x"
  shows "cmap ff xs = cmap gg ys"
  using assms by (induction xs arbitrary: ys) auto

lemma cmap_empty_singl_filter[simp]:
"cmap (\<lambda>x. if pred x then [x] else []) xl = filter pred xl"
  by (induct xl) auto

(* The non-None items in a list of options: *)
fun these :: "'a option list \<Rightarrow> 'a list" where
  "these [] = []"
| "these (None # xs) = these xs"
| "these (Some x # xs) = x # these xs"

lemma these_map_Some'[simp]: "these (map Some xs) = xs"
by (induct xs) auto

lemma these_map_Some[simp]: "these (map (Some o f) xs) = map f xs"
by (induct xs) auto

(* *)

(* Take-until and drop-until (variations of takeWhile and dropWhile *)

definition "takeUntil pred xs \<equiv> 
  append (takeWhile (\<lambda>x. \<not> pred x) xs) [hd (dropWhile (\<lambda>x. \<not> pred x) xs)]"

definition "dropUntil pred xs \<equiv> tl (dropWhile (\<lambda>x. \<not> pred x) xs)"

lemma append_takeUntil_dropUntil: 
"\<exists>x\<in>set xs. pred x \<Longrightarrow> append (takeUntil pred xs) (dropUntil pred xs) = xs"
by (simp add: dropUntil_def takeUntil_def) 

lemma takeUntil_not_Nil: 
assumes "\<exists>x\<in>set xs. pred x"  
shows "takeUntil pred xs \<noteq> []"
by (simp add: takeUntil_def) 

lemma takeUntil_ex_butlast: 
assumes "\<exists>x\<in>set xs. pred x" "y \<in> set (butlast (takeUntil pred xs))"
shows "\<not> pred y"
using assms unfolding takeUntil_def 
by (metis butlast_snoc set_takeWhileD) 

lemma takeUntil_last: 
assumes "\<exists>x\<in>set xs. pred x" 
shows "pred (last (takeUntil pred xs))"
using assms unfolding takeUntil_def 
by (metis dropWhile_eq_Nil_conv hd_dropWhile last_snoc) 

lemma takeUntil_last_butlast: 
assumes "\<exists>x\<in>set xs. pred x" 
shows "takeUntil pred xs = append (butlast (takeUntil pred xs)) [last (takeUntil pred xs)]"
by (simp add: assms takeUntil_not_Nil)


subsection \<open>Facts about lists\<close>

text \<open>The two-element datatype of turns will be used in the soundness proof for unwinding. \<close>

datatype turn = L | R

fun switch where "switch L = R" | "switch R = L"

(* We set "L < R". *)
instantiation turn :: wellorder 
begin 
  definition less_eq_turn :: "turn \<Rightarrow> turn \<Rightarrow> bool" where 
  "less_eq_turn trn trn' \<longleftrightarrow> trn = trn' \<or> trn' = R"
  definition less_turn :: "turn \<Rightarrow> turn \<Rightarrow> bool" where 
  "less_turn trn trn' \<longleftrightarrow> trn = L \<and> trn' = R"
  instance apply standard unfolding less_eq_turn_def less_turn_def  
  using switch.cases by auto 
end (* instantiation *)

declare less_eq_turn_def [simp] less_turn_def [simp]

(* A well-founded relation involving taking turns: *)

definition TWW :: "((turn \<times> enat \<times> enat) \<times> (turn \<times> enat \<times> enat)) set" where 
"TWW \<equiv> {((trn,wL,wR), (trn',wL',wR')) | trn wL wR trn' wL' wR' . 
  trn < trn' \<or> 
  trn = trn' \<and> (trn = L \<and> trn' = L \<and> wL < wL' \<or> trn = R \<and> trn' = R \<and> wR < wR')}"

lemma wf_TWW: "wf TWW"
proof-     
  define WL :: "((turn \<times> enat \<times> enat) \<times> (turn \<times> enat \<times> enat)) set" 
  where "WL \<equiv> {((trn,wL,wR), (trn',wL',wR')) | trn wL wR trn' wL' wR' . 
                  trn = L \<and> trn' = L \<and> wL < wL'}"
  have "WL \<subseteq> inv_image {(w,w') . w < w'} (\<lambda>(trn,wL,wR). wL)"
  unfolding WL_def inv_image_def by auto
  hence wfWL: "wf WL" using wf wf_inv_image wf_subset by blast

  define WR :: "((turn \<times> enat \<times> enat) \<times> (turn \<times> enat \<times> enat)) set" 
  where "WR \<equiv> {((trn,wL,wR), (trn',wL',wR')) | trn wL wR trn' wL' wR' . 
                  trn = R \<and> trn' = R \<and> wR < wR'}"
  have "WR \<subseteq> inv_image {(w,w') . w < w'} (\<lambda>(trn,wL,wR). wR)"
  unfolding WR_def inv_image_def by auto
  hence wfWR: "wf WR" using wf wf_inv_image wf_subset by blast

  have wfWW: "wf (WL \<union> WR)" apply(rule wf_Un) 
  using wfWL wfWR unfolding WL_def WR_def by auto
  define f where "f \<equiv> \<lambda>(trn::turn,wL::enat,wR::enat). (trn,(trn,wL,wR))"
  have TWW: "TWW = inv_image (lex_prod {(trn::turn,trn') . trn < trn'} (WL \<union> WR)) f"
  unfolding TWW_def WL_def WR_def inv_image_def f_def by auto

  show ?thesis  unfolding TWW  
  using wf wfWW by blast
qed




subsection \<open>Facts about filtermap on lazy lists \<close>

text \<open>Soem customization of the coinduction principles for 
filtermap equality -- to accommodate turns. \<close>

context TwoFuncPred
begin

lemmas sameFM_selectLNil = disjI1
lemmas sameFM_selectSingl = disjI2[OF disjI1]
lemmas sameFM_selectlappend = disjI2[OF disjI2[OF disjI1]] 
lemmas sameFM_selectlmap_lfilter = disjI2[OF disjI2[OF disjI2]]

coinductive sameFM1 :: "turn \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
LNil: 
"sameFM1 trn wL wR [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> sameFM1 trn wL wR [[a]] [[a']]"
|
lappend: 
"xs \<noteq> [] \<Longrightarrow> xs' \<noteq> [] \<Longrightarrow> 
 map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM1 trn' vL vR as as'
 \<Longrightarrow> sameFM1 trn wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayL: 
"vL < wL \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM1 L vL vR as as'
 \<Longrightarrow> sameFM1 L wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayR: 
"vR < wR \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM1 R vL vR as as'
 \<Longrightarrow> sameFM1 R wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
RL: 
"map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM1 L vL vR as as'
 \<Longrightarrow> sameFM1 R wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"

lemmas sameFM1_selectLNil = disjI1
lemmas sameFM1_selectSingl = disjI2[OF disjI1]
lemmas sameFM1_selectlappend = disjI2[OF disjI2[OF disjI1]]
lemmas sameFM1_selectDelayL = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas sameFM1_selectDelayR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI1]]]]
lemmas sameFM1_selectRL = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI2]]]]

(* *)
proposition sameFM1_lmap_lfilter: 
assumes "sameFM1 trn wL wR as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
proof-
  define P where "P \<equiv> \<lambda>(trn,wL,wR) as as'. sameFM1 trn wL wR as as'"
  show ?thesis 
  apply(rule lmap_lfilter_lappend_coind_wf[OF wf_TWW, of P "(trn,wL,wR)"])
    subgoal using assms unfolding P_def by simp
    subgoal for w lxs lxs' apply (cases w)
    unfolding P_def apply clarify apply (erule sameFM1.cases)
    by (fastforce elim: sameFM1.cases simp: TWW_def less_turn_def)+ .   
qed
 

(* *)

coinductive sameFM2 :: "turn \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
LNil: 
"sameFM2 trn wL wR [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> sameFM2 trn wL wR [[a]] [[a']]"
|
lappend: 
"xs \<noteq> [] \<Longrightarrow> xs' \<noteq> [] \<Longrightarrow> 
 map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM2 trn' vL vR as as'
 \<Longrightarrow> sameFM2 trn wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayL: 
"vL < wL \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM2 L vL vR as as'
 \<Longrightarrow> sameFM2 L wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayR: 
"vR < wR \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM2 R vL vR as as'
 \<Longrightarrow> sameFM2 R wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
LR: 
"map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM2 R vL vR as as'
 \<Longrightarrow> sameFM2 L wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"


lemmas sameFM2_selectLNil = disjI1
lemmas sameFM2_selectSingl = disjI2[OF disjI1]
lemmas sameFM2_selectlappend = disjI2[OF disjI2[OF disjI1]]
lemmas sameFM2_selectDelayL = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas sameFM2_selectDelayR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI1]]]]
lemmas sameFM2_selectLR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI2]]]]

lemma switch: "switch trn = (if trn = L then R else L)"
by(cases trn, auto)

lemma sameFM2_lmap_lfilter: 
assumes "sameFM2 trn wL wR as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
proof-
  define P where "P \<equiv> \<lambda>(trn,wR,wL) as as'. sameFM2 (switch trn) wL wR as as'"
  show ?thesis 
  apply(rule lmap_lfilter_lappend_coind_wf[OF wf_TWW, of P "(switch trn,wR,wL)"])
    subgoal using assms unfolding P_def 
      using switch switch.cases by auto   
    subgoal for w lxs lxs' apply (cases w) subgoal for trn wL wR 
    unfolding P_def apply clarify apply (erule sameFM2.cases)
      subgoal by fastforce 
      subgoal using sameFM.Singl sameFM_lmap_lfilter by auto
      subgoal by (smt (verit, best) case_prod_conv switch turn.exhaust)
      subgoal unfolding TWW_def less_turn_def  
        by simp (metis (full_types) switch.elims)
      subgoal unfolding TWW_def less_turn_def  
        by simp (metis (full_types) switch.elims)
      subgoal unfolding TWW_def less_turn_def  
        by simp (metis (full_types) switch.elims) . . .
qed

end (* context TwoFuncPred *)


subsection \<open>More locale infrastructure for list-filtermap 
and lazy-list-filtermap \<close>

(* This will be instantiated to the observation, action and secrecy operators 
that form relative security. Using a locale and then interpreting 
to all these definitions offers slightly better automation than 
using the predicate-and-function generic results, and allows for 
less writing than plugging in the predicate and functiin explicitly when 
invoking the results. 
*)

text \<open>Locale for applying filtermap to all-but-the-last elements of 
a list \<close>

(* "BL" stands for "butlast" *)

locale FiltermapBL =
  fixes pred and func and filtermapBL
  assumes FiltermapBL: "filtermapBL tr = filtermap pred func (butlast tr)"
begin

lemma map_filter: "filtermapBL tr = map func (filter pred (butlast tr))" 
  unfolding FiltermapBL filtermap_def ..

lemma simps[simp]:
"filtermapBL [] = []"  "\<not> pred s \<Longrightarrow> filtermapBL (s # tr) = filtermapBL tr"  
"pred s \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> filtermapBL (s # tr) = func s # filtermapBL tr"
"filtermapBL [s] = []"
unfolding FiltermapBL by auto

lemma iff_Nil[simp]: "filtermapBL (s # tr) = [] \<longleftrightarrow> (\<not> pred s \<or> tr = []) \<and> filtermapBL tr = []"
unfolding FiltermapBL by (cases "pred s", auto)

lemma Nil_iff: "[] = filtermapBL (s # tr) \<longleftrightarrow> (\<not> pred s \<or> tr = []) \<and> filtermapBL tr = []"
unfolding FiltermapBL by (cases "pred s", auto)

lemma Cons_unfold: "filtermapBL (s # tr) = (if pred s then (if tr = [] then [] else func s # filtermapBL tr) else filtermapBL tr)"
  by auto

lemma length: "length (filtermapBL tr) \<le> length tr" 
unfolding FiltermapBL  
by (metis diff_le_self dual_order.trans length_butlast length_filtermap)  

lemma length_Nil[simp]: "length tr \<le> Suc 0 \<Longrightarrow> filtermapBL tr = []"
unfolding FiltermapBL by (cases tr, auto)


lemma eq_Nil_iff:
  "filtermapBL tr = [] \<longleftrightarrow> never pred (butlast tr)"
  "[] = filtermapBL tr \<longleftrightarrow> never pred (butlast tr)"
by (metis FiltermapBL filtermap_Nil_never)+

lemma eq_Cons: 
assumes 1: "filtermapBL tr = Cons obs obsl'"
shows "\<exists>trv1 s tr'. tr = append trv1 (Cons s tr') \<and> never pred trv1 \<and> 
   pred s \<and> func s = obs \<and> filtermapBL tr' = obsl'"
proof-
  have "tr \<noteq> []" using 1 by auto
  note 1 = this 1 
  have "\<not> never pred (butlast tr)"  
    by (metis eq_Nil_iff(2) 1(2) list.distinct(1))   

  then obtain ii where ii: "ii < length (butlast tr) \<and> pred (nth (butlast tr) ii)"  
  unfolding list_all_nth by auto
  define i where "i = (LEAST ii. ii < length (butlast tr) \<and> pred (nth (butlast tr) ii))"
  have i: "i < length (butlast tr)" "pred (nth (butlast tr) i)"
  and min_i: "\<And>j. j < i \<Longrightarrow> \<not> pred (nth (butlast tr) j)"
  unfolding i_def  
  by (smt (verit, ccfv_SIG) LeastI_ex dual_order.strict_trans enat_ord_simps(2) ii not_less_Least)+
  hence isInt: "pred (nth tr i)" by (simp add: nth_butlast)

  have [simp]: "\<not> length tr \<le> Suc i" 
      using i(1) by auto

  show ?thesis 
  proof(rule exI[of _ "take i tr"], rule exI[of _ "nth tr i"], 
        rule exI[of _ "drop (Suc i) tr"],intro conjI)  
    show 2: "tr = take i tr @ tr ! i # drop (Suc i) tr" 
    apply(rule sym) apply(rule append_take_nth_drop)
    using i(1) by auto
    have "butlast tr = take i tr @ (butlast (tr ! i # drop (Suc i) tr))" 
    by (metis "2" butlast_append list.distinct(1))
    hence 22: "butlast tr = take i tr @ (tr ! i # butlast (drop (Suc i) tr))" by simp

    show 3: "never pred (take i tr)" 
    unfolding list_all_nth  
    by simp (metis i(1) min_i nth_butlast order_less_trans) 
    have 33: "map func (filter pred (take i tr)) = []"  
    by simp (metis "3" never_Nil_filter)
   
    show 4: "pred (nth tr i)" by fact
    show "func (nth tr i) = obs" 
    using 1 4 by(simp add: map_filter 22 33)
    show "filtermapBL (drop (Suc i) tr) = obsl'" 
    using 1 4 by(simp add: map_filter 22 33)  
  qed
qed

end (* context FiltermapBL *)


text \<open>Locale for applying filtermap to all-but-the-last elements of 
a lazy list. (If the lazy list is infinite, it is applied to all.) \<close>

locale LfiltermapBL =
  fixes pred and func and lfiltermapBL
  assumes LfiltermapBL: "lfiltermapBL tr = lfiltermap pred func (lbutlast tr)"
begin

lemma lmap_lfilter: "lfiltermapBL tr = lmap func (lfilter pred (lbutlast tr))" 
  unfolding LfiltermapBL lfiltermap_lmap_lfilter ..

lemma simps[simp]:
"lfiltermapBL [[]] = [[]]"  "\<not> pred s \<Longrightarrow> lfiltermapBL (s $ tr) = lfiltermapBL tr"  
"pred s \<Longrightarrow> tr \<noteq> [[]] \<Longrightarrow> lfiltermapBL (s $ tr) = func s $ lfiltermapBL tr"
"lfiltermapBL [[s]] = [[]]"
unfolding LfiltermapBL lfiltermap_def 
by auto (metis lbutlast_Cons lbutlast_LNil lbutlast_singl lfilter_LCons_seek)

lemma iff_Nil[simp]: "lfiltermapBL (s $ tr) = [[]] \<longleftrightarrow> (\<not> pred s \<or> tr = [[]]) \<and> lfiltermapBL tr = [[]]"
unfolding LfiltermapBL lfiltermap_def  
by (metis lbutlast_Cons lbutlast_LNil lbutlast_singl lfilter_LCons_found llist.distinct(1) lmap_eq_LNil lmap_lfilter simps(2))

lemma Nil_iff: "[[]] = lfiltermapBL (s $ tr) \<longleftrightarrow> (\<not> pred s \<or> tr = [[]]) \<and> lfiltermapBL tr = [[]]"
apply(subst iff_Nil[symmetric]) by metis

lemma Cons_unfold: "lfiltermapBL (s $ tr) = (if pred s then (if tr = [[]] then [[]] else func s $ lfiltermapBL tr) else lfiltermapBL tr)"
  by auto

lemma length: "llength (lfiltermapBL tr) \<le> llength tr" 
 unfolding LfiltermapBL lfiltermap_def  
by simp (metis dual_order.trans epred_conv_minus ile_eSuc lbutlast_LNil llength_LCons 
   llength_lbutlast llength_lfilter_ile llength_ltl llist.exhaust_sel)
 
lemma eq_LNil_iff: "lfiltermapBL tr = [[]] \<longleftrightarrow> lnever pred (lbutlast tr)"
by (metis lmap_lfilter lfiltermap_LNil_never lfiltermap_lmap_lfilter)

lemma eq_LCons_infinite: 
assumes 1: "llength tr = \<infinity>" "lfiltermapBL tr = LCons obs obsl'"
shows "\<exists>trv1 s tr'. tr = lappend (llist_of trv1) (LCons s tr') \<and> never pred trv1 \<and> 
   pred s \<and> func s = obs \<and> lfiltermapBL tr' = obsl'"
proof-
  have tr_bl: "lbutlast tr = tr"  
    by (meson assms(1) lbutlast_def llength_eq_infty_conv_lfinite)
  have "\<not> lnever pred tr"  
    by (metis assms(2) eq_LNil_iff llist.distinct(1) tr_bl)
    
  then obtain ii where ii: "ii < llength tr \<and> pred (lnth tr ii)"  
  unfolding llist_all_lnth by auto
  define i where "i = (LEAST ii. ii < llength tr \<and> pred (lnth tr ii))"
  have i: "i < llength tr" "pred (lnth tr i)"
  and min_i: "\<And>j. j < i \<Longrightarrow> \<not> pred (lnth tr j)"
  unfolding i_def  
  by (smt (verit, ccfv_SIG) LeastI_ex dual_order.strict_trans enat_ord_simps(2) ii not_less_Least)+
 
  have [simp]: "\<not> llength tr \<le> i" 
      using i(1) by auto

  show ?thesis 
  proof(rule exI[of _ "list_of (ltake i tr)"], rule exI[of _ "lnth tr i"], 
        rule exI[of _ "ldrop (Suc i) tr"], intro conjI)  
    show 2: "tr = lappend (llist_of (list_of (ltake (enat i) tr))) (lnth tr i $ ldrop (enat (Suc i)) tr)"
    apply simp apply(rule sym) apply(rule lappend_ltake_lnth_ldrop)
    using i(1) by auto
  
    show 3: "never pred (list_of (ltake (enat i) tr))" 
     unfolding list_all_nth apply simp 
     by (simp add: i(1) length_list_of_conv_the_enat lnth_ltake min_i)
  
    have 33: "lmap func (lfilter pred (ltake i tr)) = [[]]" apply simp  
    by (metis (no_types, lifting) enat_ord_simps(2) llength_ltake llist_all_lnth 
        lnever_LNil_lfilter lnth_ltake min_i min_less_iff_conj)

    have [simp]: "min (enat i) (llength tr) = enat i"  
      by (simp add: assms(1))

    have def2: "lfiltermapBL tr = lmap func (lfilter pred tr)"
    unfolding lmap_lfilter tr_bl ..
   
    show 4: "pred (lnth tr i)" by fact
    show "func (lnth tr i) = obs" 
    using 1(2) unfolding def2  apply(subst (asm) 2)
    using 4 apply simp unfolding lmap_lappend_distrib unfolding 33 by simp

    have ll: "llength (ldrop (enat (Suc i)) tr) = \<infinity>" 
      by (simp add: assms(1) ldrop_enat)
   
    show "lfiltermapBL (ldrop (Suc i) tr) = obsl'" 
    using 1(2) unfolding def2  apply(subst (asm) 2)
    using 4 apply simp unfolding lmap_lappend_distrib unfolding 33 apply simp  
    by (metis lmap_lfilter lbutlast_def ll llength_eq_infty_conv_lfinite)
  qed
qed 

lemma eq_LCons_finite: 
assumes 1: "llength tr < \<infinity>" "lfiltermapBL tr = LCons obs obsl'"
shows "\<exists>trv1 s tr'. tr = lappend (llist_of trv1) (LCons s tr') \<and> never pred trv1 \<and> 
   pred s \<and> func s = obs \<and> lfiltermapBL tr' = obsl'"
proof-
  obtain ttr where tr: "tr = llist_of ttr" using 1(1)  
    using enat_ord_simps(4) llist_cases by blast

  have [simp]: "ttr \<noteq> []" "tr \<noteq> [[]]"    
    using assms(2) tr by fastforce+
  
  define ddef where "ddef \<equiv> \<lambda> tr. (if tr = [] then [] else filtermap pred func (butlast tr))"
  have ii: "FiltermapBL pred func ddef" unfolding ddef_def FiltermapBL_def 
  by simp

  have lo: "llength obsl' < \<infinity>" 
    by (metis assms(1) assms(2) enat_ord_simps(4) leD length lfinite_code(2) llength_eq_infty_conv_lfinite)
  define oobsl' where "oobsl' \<equiv> list_of obsl'"

  have dd: "ddef ttr = Cons obs oobsl'"
  unfolding ddef_def oobsl'_def apply simp 
  using 1(2) using LfiltermapBL_axioms[unfolded LfiltermapBL_def, rule_format, of tr] 
  apply simp 
  by (metis lfinite_code(2) lfinite_lfiltermap_filtermap lfinite_llist_of list_of_LCons list_of_llist_of llist_of_butlast tr)

  obtain trv1 s tr' where 0: "ttr = trv1 @ s # tr' \<and> never pred trv1 \<and> pred s \<and> func s = obs \<and> ddef tr' = oobsl'"
  using FiltermapBL.eq_Cons[OF ii dd] by auto

  show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ s]) apply(rule exI[of _ "llist_of tr'"])
  using 0 1(1) lo  
  by simp (metis ddef_def LfiltermapBL lappend_llist_of_llist_of lfiltermap_llist_of_filtermap 
  llength_eq_enat_lfiniteD llist_of.simps(1) llist_of.simps(2) llist_of_butlast llist_of_list_of oobsl'_def simps(1) tr)
qed

lemma eq_LCons: 
assumes "lfiltermapBL tr = LCons obs obsl'"
shows "\<exists>trv1 s tr'. tr = lappend (llist_of trv1) (LCons s tr') \<and> never pred trv1 \<and> 
   pred s \<and> func s = obs \<and> lfiltermapBL tr' = obsl'"
using assms enat_ord_simps(4) eq_LCons_finite eq_LCons_infinite by blast


end (* context LfiltermapBL *)


end
