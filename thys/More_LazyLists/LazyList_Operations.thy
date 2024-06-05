section \<open>Some Operations on Lazy Lists\<close>

theory LazyList_Operations
imports "Coinductive.Coinductive_List" List_Filtermap
begin 


text \<open> This theory defines some operations for lazy lists, and proves their basic properties. \<close>

subsection \<open>Preliminaries\<close>

lemma enat_ls_minius_1: "enat i < j - 1 \<Longrightarrow> enat i < j"
by (metis co.enat.exhaust eSuc_minus_1 idiff_0 iless_Suc_eq less_imp_le)

(* Some notations: *)

abbreviation LNil_abbr ("[[]]") where "LNil_abbr \<equiv> LNil"

abbreviation LCons_abbr (infixr "$" 65) where "x $ xs \<equiv> LCons x xs"

abbreviation lnever :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" where "lnever U \<equiv> llist_all (\<lambda> a. \<not> U a)"
  
syntax
  \<comment> \<open>llist Enumeration\<close>
  "_llist" :: "args => 'a llist"    ("[[(_)]]")

translations
  "[[x, xs]]" == "x $ [[xs]]"
  "[[x]]" == "x $ [[]]"

(* Some simplification rules: *)
declare llist_of_eq_LNil_conv[simp]
declare lmap_eq_LNil[simp]
declare llength_ltl[simp]


subsection \<open>More properties of operators from the Coinductive library\<close>

lemma lnth_lconcat: 
assumes "i < llength (lconcat xss)"
shows "\<exists>j<llength xss. \<exists>k<llength (lnth xss j). lnth (lconcat xss) i = lnth (lnth xss j) k"
using assms lnth_lconcat_conv by blast

lemma lnth_0_lset:  "xs \<noteq> [[]] \<Longrightarrow> lnth xs 0 \<in> lset xs"
by (metis llist.set_sel(1) lnth_0_conv_lhd lnull_def)

lemma lconcat_eq_LNil_iff: "lconcat xss = [[]] \<longleftrightarrow> (\<forall>xs\<in>lset xss. xs = [[]])"
by (metis lnull_def lnull_lconcat mem_Collect_eq subset_eq)

lemma llast_last_llist_of: "lfinite xs \<Longrightarrow> llast xs = last (list_of xs)"
by (metis llast_llist_of llist_of_list_of)

lemma lappend_llist_of_inj: 
"length xs = length ys \<Longrightarrow> 
 lappend (llist_of xs) as = lappend (llist_of ys) bs \<longleftrightarrow> xs = ys \<and> as = bs"
apply(induct xs ys arbitrary: as bs rule: list_induct2) by auto

lemma llist_all_lnth: "llist_all P xs = (\<forall>n<llength xs. P (lnth xs n))"
by (metis in_lset_conv_lnth llist.pred_set)

lemma llist_eq_cong: 
assumes "llength xs = llength ys" "\<And>i. i < llength xs \<Longrightarrow> lnth xs i = lnth ys i"
shows "xs = ys"
proof-
  have "llength xs = llength ys \<and> (\<forall>i. i < llength xs \<longrightarrow> lnth xs i = lnth ys i)"
  using assms by auto 
  thus ?thesis apply(coinduct rule: llist.coinduct)  
  by simp (metis lhd_conv_lnth linorder_not_less llength_eq_0 lnth_beyond lnth_ltl)
qed

lemma llist_cases: "llength xs = \<infinity> \<or> (\<exists>ys. xs = llist_of ys)"
by (metis llist_of_list_of not_lfinite_llength)

lemma llist_all_lappend: "lfinite xs \<Longrightarrow> 
llist_all pred (lappend xs ys) \<longleftrightarrow> llist_all pred xs \<and> llist_all pred ys"
unfolding llist.pred_set by (auto simp add: in_lset_lappend_iff) 

lemma llist_all_lappend_llist_of: 
"llist_all pred (lappend (llist_of xs) ys) \<longleftrightarrow> list_all pred xs \<and> llist_all pred ys"
by (metis lfinite_llist_of list_all_iff llist.pred_set llist_all_lappend lset_llist_of)

lemma llist_all_conduct: 
"X xs \<Longrightarrow> 
(\<And>xs. X xs \<Longrightarrow> \<not> lnull xs \<Longrightarrow> P (lhd xs) \<and> (X (ltl xs) \<or> llist_all P (ltl xs))) \<Longrightarrow>
 llist_all P xs"
unfolding llist.pred_rel apply(coinduct rule: llist_all2_coinduct[of "\<lambda>xs ys. X xs \<and> xs = ys"])
by (auto simp: eq_onp_same_args)

lemma lfilter_lappend_llist_of:
"lfilter P (lappend (llist_of xs) ys) = lappend (llist_of (filter P xs)) (lfilter P ys)"
by simp

lemma ldrop_Suc: "n < llength xs \<Longrightarrow> ldrop (enat n) xs = LCons (lnth xs n) (ldrop (enat (Suc n)) xs)" 
apply(rule llist_eq_cong)
  subgoal apply(subst llength_ldrop) apply simp apply(subst llength_ldrop) 
  using llist_cases[of xs] by (auto simp: eSuc_enat) 
  subgoal for i apply(subst lnth_ldrop) 
    subgoal by (metis add.commute ldrop_eq_LNil ldrop_ldrop linorder_not_less)
    subgoal apply(subst lnth_LCons)  
      by (metis \<open>\<lbrakk>enat n < llength xs; enat i < llength (ldrop (enat n) xs)\<rbrakk> \<Longrightarrow> 
       enat n + enat i < llength xs\<close> ldrop_enat ldropn_Suc_conv_ldropn lnth_LCons lnth_ldrop) . . 
    
lemma lappend_ltake_lnth_ldrop: "n < llength xs \<Longrightarrow>
  lappend (ltake (enat n) xs) (LCons (lnth xs n) (ldrop (enat (Suc n)) xs)) = xs"
by (simp add: ldrop_enat ldropn_Suc_conv_ldropn) 

lemma ltake_eq_LNil: "ltake i tr = [[]] \<longleftrightarrow> i = 0 \<or> tr = [[]]" 
by (metis LNil_eq_ltake_iff)

lemma ex_llength_infty: 
"\<exists>a. llength a = \<infinity> \<and> lhd a = 0"
by (meson lhd_iterates llength_iterates)

lemma repeat_not_Nil[simp]: "repeat a \<noteq> [[]]" 
by (metis lfinite_LNil lfinite_iterates)


subsection \<open>A convenient adaptation of the lazy-list corecursor \<close>

(* "isn" stands for "is nil", "h" and "t" for "head" and "tail", "e" for "exist" and "ec" for exit condition".*)

definition ccorec_llist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b llist) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b llist"
where "ccorec_llist isn h ec e t \<equiv> 
    corec_llist isn (\<lambda>a. if ec a then lhd (e a) else h a) ec (\<lambda>a. case e a of b $ a' \<Rightarrow> a') t"

lemma llist_ccorec_LNil: "isn a \<Longrightarrow> ccorec_llist isn h ec e t a = [[]]"
unfolding ccorec_llist_def llist.corec(1) by auto

lemma llist_ccorec_LCons: 
"\<not> lnull (e a) \<Longrightarrow> \<not> isn a \<Longrightarrow> 
ccorec_llist isn h ec e t a = (if ec a then e a else h a $ ccorec_llist isn h ec e t (t a))"
unfolding ccorec_llist_def llist.corec(2)  
by (cases " e a", auto simp: lnull_def) 

(* Compare with the corresponding equation for the standard corecursor:
thm llist.corec(2)
Unlike that one, llist_ccorec_LCons does not enforce a guard at the top in the ``exit'' case. *)

lemmas llist_ccorec = llist_ccorec_LNil llist_ccorec_LCons


subsection \<open>Multi-step coinduction for llist equality \<close>

text \<open>In this principle, the coinductive step can consume any non-empty list, not 
just single elements. \<close>

proposition llist_lappend_coind: 
assumes P: "P lxs lxs'"
and lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lxs = lxs' \<or>  
   (\<exists>ys llxs llxs'. ys \<noteq> [] \<and> 
    lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys) llxs' \<and> 
    P llxs llxs')" 
shows "lxs = lxs'"
proof-
  have l1: "llength lxs \<le> llength lxs'"
  proof(cases "lfinite lxs'")
    case False thus ?thesis by (simp add: not_lfinite_llength)
  next
    case True
    then obtain xs' where lxs': "lxs' = llist_of xs'"
    by (metis llist_of_list_of)
    show ?thesis using P unfolding lxs' proof(induct xs' arbitrary: lxs rule: length_induct)
      case (1 xs' lxs)
      show ?case using lappend[OF 1(2)] apply(elim disjE exE conjE)
        subgoal by simp
        subgoal for ys llxs llxs' using 1(1)[rule_format, of "list_of llxs'" llxs] 
        by simp (metis length_append length_greater_0_conv less_add_same_cancel2 
        lfinite_lappend lfinite_llist_of list_of_lappend list_of_llist_of llength_llist_of llist_of_list_of) .
    qed
  qed
  (* *)
  have l2: "llength lxs' \<le> llength lxs"
  proof(cases "lfinite lxs")
    case False thus ?thesis by (simp add: not_lfinite_llength)
  next
    case True
    then obtain xs where lxs: "lxs = llist_of xs"
    by (metis llist_of_list_of)
    show ?thesis using P unfolding lxs proof(induct xs arbitrary: lxs' rule: length_induct)
      case (1 xs lxs')
      show ?case using lappend[OF 1(2)] apply(elim disjE exE conjE)
        subgoal by simp
        subgoal for ys llxs llxs' using 1(1)[rule_format, of "list_of llxs" llxs'] 
        by simp (metis length_append length_greater_0_conv less_add_same_cancel2 
        lfinite_lappend lfinite_llist_of list_of_lappend list_of_llist_of llength_llist_of llist_of_list_of) .
    qed
  qed

  from l1 l2 have l: "llength lxs = llength lxs'" by simp
  show ?thesis proof(rule llist_eq_cong)
    show "llength lxs = llength lxs'" by fact
  next
    fix i assume i: "enat i < llength lxs"
    
    show "lnth lxs i = lnth lxs' i"  
    using P l i proof(induct i arbitrary: lxs lxs' rule: less_induct)
      case (less i lxs lxs')
      show ?case using lappend[OF less(2)] proof(elim disjE exE conjE)
        fix ys llxs llxs'
        assume ys: "ys \<noteq> []" and P: " P llxs llxs'"
        and lxs: "lxs = lappend (llist_of ys) llxs"
        and lxs': "lxs' = lappend (llist_of ys) llxs'" 
      
        show "lnth lxs i = lnth lxs' i"
        proof(cases "i < length ys")
          case True
          hence "lnth lxs i = ys ! i" "lnth lxs' i = ys ! i" unfolding lxs lxs'  
          by (auto simp: lnth_lappend_llist_of)
          thus ?thesis by simp
        next
          case False
          then obtain j where i: "i = length ys + j" 
          using le_Suc_ex not_le_imp_less by blast
          hence j: "j < llength lxs" "j < llength lxs'"  
          by (metis dual_order.strict_trans enat_ord_simps(2) 
                    length_greater_0_conv less.prems(2,3) less_add_same_cancel2 ys)+
          hence 0: "lnth lxs i = lnth llxs j" "lnth lxs' i = lnth llxs' j" unfolding lxs lxs'  
          unfolding i by (auto simp: lnth_lappend_llist_of)
          show ?thesis unfolding 0 apply(rule less(1)[rule_format, of j llxs llxs'])
            subgoal by (simp add: i ys)
            subgoal by (simp add: P)
            subgoal using less.prems(2) lxs lxs' by auto
            subgoal by (metis enat_add_mono i less.prems(3) llength_lappend llength_llist_of lxs plus_enat_simps(1)) .
        qed
      qed auto
    qed
  qed 
qed


subsection \<open>Interval lazy lists\<close>

text \<open>The list of all naturals between a natural and an extended-natural\<close>

primcorec betw :: "nat \<Rightarrow> enat \<Rightarrow> nat llist" where 
"betw i n = (if i \<ge> n then LNil else i $ betw (Suc i) n)"

lemma betw_more_simps: 
"\<not> n \<le> i \<Longrightarrow> betw i n = i $ betw (Suc i) n"
using betw.ctr(2) enat_ord_simps(1) by blast

lemma lhd_betw: "i < n \<Longrightarrow> lhd (betw i n) = i"
by fastforce

lemma not_lfinite_betw_infty: "\<not> lfinite (betw i \<infinity>)"
proof-
  {fix js assume "lfinite js" "js = betw i \<infinity>" 
   hence False
   apply (induct arbitrary: i)
     subgoal by (metis betw.disc(2) enat_ord_code(5) llist.disc(1))
     subgoal by (metis betw.sel(2) enat_ord_code(5) llist.sel(3)) .
  }
  thus ?thesis by auto
qed

lemma llength_betw_infty[simp]: "llength (betw i \<infinity>) = \<infinity>"
using not_lfinite_betw_infty not_lfinite_llength by blast

lemma llength_betw: "llength (betw i n) = n - i"
apply(cases n)
  subgoal for nn apply simp apply(induct "nn-i" arbitrary: i, auto)
    apply (simp add: zero_enat_def)  
    by (metis betw.ctr(2) diff_Suc_1 diff_Suc_eq_diff_pred diff_commute 
    eSuc_enat enat_ord_simps(1) less_le_not_le llength_LCons zero_less_Suc zero_less_diff)
  subgoal by simp .

lemma lfinite_betw_not_infty: "n < \<infinity> \<Longrightarrow> lfinite (betw i n)"
using lfinite_conv_llength_enat llength_betw by fastforce

lemma lfinite_betw_enat: "lfinite (betw i (enat n))"
using lfinite_conv_llength_enat llength_betw by fastforce
  
lemma lnth_betw: "enat j < n - i \<Longrightarrow> lnth (betw i n) j = i + j"
apply(induct j arbitrary: i, auto)  
  apply (metis betw.ctr(1) betw.disc_iff(1) betw.simps(3) enat_0 llength_LNil 
       llength_betw lnth_0_conv_lhd zero_less_iff_neq_zero)
  by (metis Suc_ile_eq add_Suc betw.ctr(1) betw.ctr(2) betw.disc(2) betw.sel(2) iless_Suc_eq 
  llength_LCons llength_LNil llength_betw lnth_ltl not_less_zero)


subsection \<open>Function builders for lazy lists\<close>

text \<open>Building an llist from a function, more precisely from its values 
between 0 and a given extended natural n\<close>

definition "build n f \<equiv> lmap f (betw 0 n)"

lemma llength_build[simp]: "llength (build n f) = n" 
by (simp add: build_def llength_betw)

lemma lnth_build[simp]: "i < n \<Longrightarrow> lnth (build n f) i = f i" 
by (simp add: build_def llength_betw lnth_betw)

lemma build_lnth[simp]: "build (llength xs) (lnth xs) = xs"
by (metis (mono_tags, lifting) llength_build llist.rel_eq llist_all2_all_lnthI lnth_build)

lemma build_eq_LNil[simp]: "build n f = [[]] \<longleftrightarrow> n = 0"
  by (metis llength_build llength_eq_0 lnull_def)


subsection \<open>The butlast (reverse tail) operation\<close>

definition lbutlast :: "'a llist \<Rightarrow> 'a llist" where 
"lbutlast sl \<equiv> if lfinite sl then llist_of (butlast (list_of sl)) else sl"

lemma llength_lbutlast_lfinite[simp]: 
"sl \<noteq> [[]] \<Longrightarrow> lfinite sl \<Longrightarrow> llength (lbutlast sl) = llength sl - 1"
unfolding lbutlast_def  
by simp (metis One_nat_def idiff_enat_enat length_list_of one_enat_def)

lemma llength_lbutlast_not_lfinite[simp]: 
"\<not> lfinite sl \<Longrightarrow> llength (lbutlast sl) = \<infinity>"
unfolding lbutlast_def using not_lfinite_llength by auto

lemma lbutlast_LNil[simp]:
"lbutlast [[]] = [[]]"
unfolding lbutlast_def by auto

lemma lbutlast_singl[simp]:
"lbutlast [[s]] = [[]]"
unfolding lbutlast_def by auto

lemma lbutlast_lfinite[simp]:
"lfinite sl \<Longrightarrow> lbutlast sl = llist_of (butlast (list_of sl))"
unfolding lbutlast_def by auto

lemma lbutlast_Cons[simp]: "tr \<noteq> [[]] \<Longrightarrow> lbutlast (s $ tr) = s $ lbutlast tr"
unfolding lbutlast_def using llist_of_list_of by fastforce

lemma llist_of_butlast: "llist_of (butlast xs) = lbutlast (llist_of xs)"
by simp

lemma lprefix_lbutlast: "lprefix xs ys \<Longrightarrow> lprefix (lbutlast xs) (lbutlast ys)"
apply(cases "lfinite xs") 
  subgoal apply(cases "lfinite ys") 
    subgoal  
    by simp (smt (verit, ccfv_threshold) butlast_append lfinite_lappend list_of_lappend 
     lprefix_conv_lappend prefix_append prefix_order.eq_iff prefixeq_butlast)
    subgoal by (metis lbutlast_def llist_of_list_of lprefix_llist_of lprefix_trans prefixeq_butlast) .
  by (simp add: not_lfinite_lprefix_conv_eq)

lemma lbutlast_lappend: 
assumes "(ys::'a llist) \<noteq> [[]]" shows "lbutlast (lappend xs ys) = lappend xs (lbutlast ys)"
proof-
  {fix us vs :: "'a llist"
   assume "\<exists> xs ys. ys \<noteq> [[]] \<and> us = lbutlast (lappend xs ys) \<and> vs = lappend xs (lbutlast ys)"
   hence "us = vs"
   apply(coinduct rule: llist.coinduct)  
   by (smt (z3) eq_LConsD lappend.disc_iff(2) lappend_code(2) lappend_eq_LNil_iff lappend_lnull1 
     lappend_snocL1_conv_LCons2 lbutlast_Cons lbutlast_singl lhd_LCons lhd_LCons_ltl lnull_def 
     lnull_lprefix lprefix_code(2) ltl_simps(1) ltl_simps(2) not_lnull_conv)
  }
  thus ?thesis using assms by blast
qed

lemma lbutlast_llist_of: "lbutlast (llist_of xs) = llist_of (butlast xs)"
by auto

lemma butlast_list_of: "lfinite xs \<Longrightarrow> butlast (list_of xs) = list_of (lbutlast xs)"
by simp

lemma butlast_length_le1[simp]: "llength xs \<le> Suc 0 \<Longrightarrow> lbutlast xs = [[]]"
 by (metis One_nat_def antisym_conv2 enat_ile epred_1 epred_conv_minus 
iless_Suc_eq lbutlast_LNil le_zero_eq lfinite_conv_llength_enat llength_eq_0 
llength_lbutlast_lfinite lnull_def one_eSuc one_enat_def)

lemma llength_lbutlast[simp]: "llength (lbutlast tr) = llength tr - 1"
by (metis idiff_0 idiff_infinity lbutlast_LNil llength_LNil llength_lbutlast_lfinite 
     llength_lbutlast_not_lfinite not_lfinite_llength)

lemma lnth_lbutlast: "i < llength xs - 1 \<Longrightarrow> lnth (lbutlast xs) i = lnth xs i"
unfolding lbutlast_def   
by simp (metis enat_ord_simps(2) llength_lbutlast llength_llist_of llist_of_butlast 
   llist_of_list_of nth_butlast nth_list_of)


subsection \<open>Consecutive-elements sublists\<close>

definition "lsublist xs ys \<equiv> \<exists>us vs. lfinite us \<and> ys = lappend us (lappend xs vs)"

lemma lsublist_refl: "lsublist xs xs"  
  by (metis lappend_LNil2 lappend_code(1) lfinite_LNil lsublist_def)

lemma lsublist_trans:
  assumes "lsublist xs ys" and "lsublist ys zs" shows "lsublist xs zs"
using assms unfolding lsublist_def  
by (metis lappend_assoc lfinite_lappend)

lemma lnth_lconcat_lsublist: 
assumes xs: "xs = lconcat (lmap llist_of xss)" and "i < llength xss"
shows "lsublist (llist_of (lnth xss i)) xs"
unfolding lsublist_def 
apply(rule exI[of _ "lconcat (lmap llist_of (ltake i xss))"])
apply(rule exI[of _ "lconcat (lmap llist_of (ldrop (Suc i) xss))"])
apply simp   
by (metis (no_types, lifting) assms lappend_inf 
    lappend_ltake_ldrop lconcat_lappend lconcat_simps(2) ldrop_enat ldrop_lmap 
    ldropn_Suc_conv_ldropn linorder_neq_iff llength_lmap llength_ltake lmap_lappend_distrib 
    lnth_lmap min_def order_less_imp_le)

lemma lnth_lconcat_lsublist2: 
assumes xs: "xs = lconcat (lmap llist_of xss)" and "Suc i < llength xss"
shows "lsublist (llist_of (append (lnth xss i) (lnth xss (Suc i)))) xs"
proof -
  have llen_Suc: \<open>enat (Suc i) < llength xss\<close>
    by (simp add: assms(2))
  then have unfold_Suc_llist_of: \<open>llist_of (lnth xss (Suc i)) = lnth (lmap llist_of xss) (Suc i)\<close>
    by (rule lnth_lmap[symmetric])
  have ldropn_Suc_complex:\<open>(llist_of (lnth xss (Suc i)) $ ldrop (enat (Suc (Suc i))) (lmap llist_of xss)) = ldropn (Suc i) (lmap llist_of xss)\<close>
    unfolding unfold_Suc_llist_of
    unfolding ldrop_enat lconcat_simps(2)[symmetric]
    apply (rule ldropn_Suc_conv_ldropn)
    by (simp add: llen_Suc)

  have llen: \<open>enat i < llength xss\<close>
    using llen_Suc  Suc_ile_eq nless_le by auto
  then have unfold_llist_of: \<open>llist_of (lnth xss i) = lnth (lmap llist_of xss) i\<close>
    by (rule lnth_lmap[symmetric])
  have ldropn_complex:\<open>(llist_of (lnth xss i) $ ldropn (Suc i) (lmap llist_of xss)) = ldropn i (lmap llist_of xss)\<close>
    unfolding unfold_llist_of
    unfolding ldrop_enat lconcat_simps(2)[symmetric]
    apply (rule ldropn_Suc_conv_ldropn)
    by (simp add: llen)

  show ?thesis  
    unfolding lsublist_def
    apply(rule exI[of _ "lconcat (lmap llist_of (ltake i xss))"])
    apply(rule exI[of _ "lconcat (lmap llist_of (ldrop (Suc (Suc i)) xss))"]) 
    unfolding xs  
    by simp (metis enat.simps(3) enat_ord_simps(4) lappend_assoc 
      lappend_llist_of_llist_of lappend_ltake_enat_ldropn lconcat_LCons 
      lconcat_lappend ldrop_lmap ldropn_Suc_complex ldropn_complex 
      lfinite_ltake ltake_lmap)
 qed

lemma lnth_lconcat_lconcat_lsublist: 
assumes xs: "xs = lappend (lconcat (lmap llist_of xss)) ys" and "i < llength xss"
shows "lsublist (llist_of (lnth xss i)) xs"
by (metis assms lappend_assoc lnth_lconcat_lsublist lsublist_def xs)

lemma lnth_lconcat_lconcat_lsublist2: 
assumes xs: "xs = lappend (lconcat (lmap llist_of xss)) ys" and "Suc i < llength xss"
shows "lsublist (llist_of (append (lnth xss i) (lnth xss (Suc i)))) xs"
by (metis assms lappend_assoc lnth_lconcat_lsublist2 lsublist_def xs)

lemma su_lset_lconcat_llist_of: 
assumes "xs \<in> lset xss"
shows "set xs \<subseteq> lset (lconcat (lmap llist_of xss))"
using in_lset_lappend_iff
by (metis assms in_lset_conv_lnth lnth_lconcat_lsublist lset_llist_of lsublist_def subsetI)

lemma lsublist_lnth_lconcat: "i < llength tr1s \<Longrightarrow> lsublist (llist_of (lnth tr1s i)) (lconcat (lmap llist_of tr1s))"
by (meson lnth_lconcat_lsublist)

lemma lsublist_lset: 
"lsublist xs ys \<Longrightarrow> lset xs \<subseteq> lset ys"
by (metis in_lset_lappend_iff lsublist_def subsetI)

lemma lsublist_LNil: 
"lsublist xs ys \<Longrightarrow> ys = LNil \<Longrightarrow> xs = LNil"
by (metis LNil_eq_lappend_iff lsublist_def)


subsection \<open>Take-until and drop-until\<close>

(* "ltakeUntil pred xs" only makes sense when "\<not> pred" does not hold for all elements of xs; 
in that case, it returns the prefix of xs all the way up to and including the first element 
where pred holds.
*)

definition ltakeUntil :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a list" where 
"ltakeUntil pred xs \<equiv> 
 list_of (lappend (ltakeWhile (\<lambda>x. \<not> pred x) xs) [[lhd (ldropWhile (\<lambda>x. \<not> pred x) xs)]])"

(* "ldropUntil pred xs" only makes sense when "\<not> pred" does not hold for all elements of xs; 
in that case, it returns the suffix of xs starting from the position right after the first one 
where pred holds. 
*)

definition ldropUntil :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where 
"ldropUntil pred xs \<equiv> ltl (ldropWhile (\<lambda>x. \<not> pred x) xs)"

lemma lappend_ltakeUntil_ldropUntil: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> lappend (llist_of (ltakeUntil pred xs)) (ldropUntil pred xs) = xs"
by (simp add: lappend_snocL1_conv_LCons2 ldropUntil_def lfinite_ltakeWhile ltakeUntil_def)

lemma ltakeUntil_not_Nil: 
assumes "\<exists>x\<in>lset xs. pred x"  
shows "ltakeUntil pred xs \<noteq> []"
by (simp add: assms lfinite_ltakeWhile list_of_lappend ltakeUntil_def)

lemma ltakeUntil_ex_butlast: 
assumes "\<exists>x\<in>lset xs. pred x" "y \<in> set (butlast (ltakeUntil pred xs))"
shows "\<not> pred y"
using assms unfolding ltakeUntil_def 
by (metis (mono_tags, lifting) butlast_snoc lfinite_LConsI lfinite_LNil lfinite_ltakeWhile 
list_of_LCons list_of_LNil list_of_lappend llist_of_list_of lset_llist_of lset_ltakeWhileD) 

lemma ltakeUntil_never_butlast: 
assumes "\<exists>x\<in>lset xs. pred x" 
shows "never pred (butlast (ltakeUntil pred xs))"
using Ball_set assms ltakeUntil_ex_butlast by fastforce 

lemma ltakeUntil_last: 
assumes "\<exists>x\<in>lset xs. pred x" 
shows "pred (last (ltakeUntil pred xs))"
using assms unfolding ltakeUntil_def 
by (metis lfinite_LConsI lfinite_LNil lfinite_lappend lfinite_ltakeWhile lhd_ldropWhile 
 llast_lappend_LCons llast_llist_of llast_singleton llist_of_list_of)

lemma ltakeUntil_last_butlast: 
assumes "\<exists>x\<in>lset xs. pred x" 
shows "ltakeUntil pred xs = append (butlast (ltakeUntil pred xs)) [last (ltakeUntil pred xs)]"
by (simp add: assms ltakeUntil_not_Nil)

lemma ltakeUntil_LCons1[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred x \<Longrightarrow> ltakeUntil pred (LCons x xs) = x # ltakeUntil pred xs"
unfolding ltakeUntil_def 
by simp (metis lfinite_LConsI lfinite_LNil lfinite_lappend lfinite_ltakeWhile list_of_LCons)

lemma ldropUntil_LCons1[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred x \<Longrightarrow> 
  ldropUntil pred (LCons x xs) = ldropUntil pred xs"
by (simp add: ldropUntil_def)

lemma ltakeUntil_LCons2[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> pred x \<Longrightarrow> ltakeUntil pred (LCons x xs) = [x]"
unfolding ltakeUntil_def by auto

lemma ldropUntil_LCons2[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> pred x \<Longrightarrow> ldropUntil pred (LCons x xs) = xs"
unfolding ldropUntil_def by auto

lemma ltakeUntil_tl1[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred (lhd xs) \<Longrightarrow> ltakeUntil pred (ltl xs) = tl (ltakeUntil pred xs)"
by (smt (verit, ccfv_SIG) eq_LConsD list.sel(3) lset_cases ltakeUntil_LCons1)

lemma ldropUntil_tl1[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred (lhd xs) \<Longrightarrow> ldropUntil pred (ltl xs) = ldropUntil pred xs"
by (metis bex_empty ldropUntil_def ldropWhile_LCons llist.exhaust_sel llist.set(1))

lemma ltakeUntil_tl2[simp]: 
"xs \<noteq> [[]] \<Longrightarrow> pred (lhd xs) \<Longrightarrow> tl (ltakeUntil pred xs) = []"
by (metis lappend_code(1) lfinite_LNil list.sel(3) list_of_LCons list_of_LNil ltakeUntil_def ltakeWhile_eq_LNil_iff)

lemma ldropUntil_tl2[simp]: 
"xs \<noteq> [[]] \<Longrightarrow> pred (lhd xs) \<Longrightarrow> ldropUntil pred xs = ltl xs"
by (metis lappend_code(1) lappend_ltakeWhile_ldropWhile ldropUntil_def ltakeWhile_eq_LNil_iff)

lemma LCons_lfilter_ldropUntil: "y $ ys = lfilter pred xs \<Longrightarrow> ys = lfilter pred (ldropUntil pred xs)"
unfolding ldropUntil_def  
by (metis (mono_tags, lifting) comp_apply eq_LConsD ldropWhile_cong lfilter_eq_LCons)

lemma length_ltakeUntil_ge_0: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "length (ltakeUntil pred xs) > 0"
using ltakeUntil_not_Nil[OF assms] by auto

lemma length_ltakeUntil_eq_1: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "length (ltakeUntil pred xs) = Suc 0 \<longleftrightarrow> pred (lhd xs)"
proof-
  obtain x xss where xs: "xs = LCons x xss" 
  using assms by (cases xs, auto)
  hence x: "x = lhd xs" by auto
  show ?thesis unfolding xs 
  using ltakeUntil_LCons2[OF assms, of x] x 
  by (smt (verit, del_insts) assms diff_Suc_1 eq_LConsD lappend_ltakeUntil_ldropUntil 
  length_Suc_conv_rev length_butlast length_tl length_ltakeUntil_ge_0 list.size(3) lnth_0 
  lnth_lappend_llist_of ltakeUntil_last ltakeUntil_last_butlast ltakeUntil_tl2 nth_append_length xs)
qed

lemma length_ltakeUntil_Suc: 
assumes "\<exists>x\<in>lset xs. pred x" "\<not> pred (lhd xs)"
shows "length (ltakeUntil pred xs) = Suc (length (ltakeUntil pred (ltl xs)))"
proof-
  obtain x xss where xs: "xs = LCons x xss" 
  using assms by (cases xs, auto)
  hence x: "x = lhd xs" and xss: "xss = ltl xs" by auto
  hence 0: "\<exists>x\<in>lset xss. pred x"  
  by (metis assms(1) assms(2) insertE lset_LCons xs)
  show ?thesis unfolding xs 
  unfolding ltakeUntil_LCons1[OF 0 assms(2), unfolded x[symmetric]] by simp
qed


subsection \<open>Splitting a lazy list according to the points where a predicate is satisfied \<close>

(* If xs = [x_0,x_1,...] such that x_(j0), x_(j0), ... are all elements where pred holds,
then split xs = 
[
 [x_0,...,x_(j0)], 
 [x_(j0+1),...,x_(j1)], 
 ...
]

Note that, if the sequence x_(j0), x_(j0), ... is finite, i.e., after some point jk 
the predicate pred will be vacuosuly false, then the split stops there, i.e., does not 
include the elements after jk. Such a "split remaider" will be covered by the operator 
lsplitRemainder introduced further down. 
*)

primcorec lsplit :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a list llist" where 
"lsplit pred xs = 
 (if (\<exists>x\<in>lset xs. pred x)
    then LCons (ltakeUntil pred xs) (lsplit pred (ldropUntil pred xs))
    else [[]])"

declare lsplit.ctr[simp]

lemma infinite_split[simp]: 
"infinite {x \<in> lset xs. pred x} \<Longrightarrow> lsplit pred xs = LCons (ltakeUntil pred xs) (lsplit pred (ldropUntil pred xs))"
using lsplit.ctr(2) not_finite_existsD by force

lemma lconcat_lsplit_not_lfinite: 
"\<not> lfinite (lfilter pred xs) \<Longrightarrow> xs = lconcat (lmap llist_of (lsplit pred xs))"
apply(coinduction arbitrary: xs) apply safe
  subgoal by simp
  subgoal by simp (metis (full_types) image_subset_iff llist.set_sel(1) lnull_imp_lfinite lnull_lfilter 
  lnull_llist_of lsplit.simps(2) lsplit.simps(3) ltakeUntil_not_Nil mem_Collect_eq) 
  subgoal by (smt (verit) lappend_ltakeUntil_ldropUntil lhd_lappend lhd_lconcat llist.map_disc_iff 
   llist.map_sel(1) llist_of.simps(1) llist_of_inject 
   lnull_def lnull_imp_lfinite lnull_lfilter lsplit.simps(2) lsplit.simps(3) ltakeUntil_not_Nil)
  subgoal for xs apply(subgoal_tac "xs \<noteq> [[]]")
    subgoal apply(subgoal_tac "\<not> lfinite (lfilter pred (ltl xs)) \<and> (\<exists>x\<in>lset xs. pred x)") 
      subgoal apply(cases "pred (lhd xs)")  
        subgoal by simp (meson ltakeUntil_not_Nil) 
        subgoal apply(rule exI[of _ "ltl xs"], safe)
          subgoal apply(subst ltl_lconcat)
            subgoal by auto
            subgoal by (metis llist.map_sel(1) lnull_llist_of lsplit.disc(2) lsplit.simps(3) ltakeUntil_not_Nil)
            subgoal unfolding ltl_lmap  apply(subst lsplit.sel(2)) 
              subgoal by auto
              subgoal using ltakeUntil_tl1 ltl_lappend ltl_lconcat ltl_llist_of ltl_lmap ltl_simps(2)
              by (smt (verit) lconcat_LCons ldropUntil_tl1 lhd_LCons_ltl 
               llist.map_disc_iff llist.map_sel(1) lnull_imp_lfinite lnull_lfilter 
               lsplit.ctr(2) lsplit.disc_iff(2) lsplit.simps(3)) . . . .
      subgoal by (metis diverge_lfilter_LNil lfilter_LCons lfinite.simps lhd_LCons_ltl) .
    subgoal by auto . . 

lemma lfinite_lsplit: 
assumes "lfinite (lfilter pred xs)" 
shows "lfinite (lsplit pred xs)"
proof-
  {fix ys assume "lfinite ys"  "ys = lfilter pred xs"
   hence ?thesis proof(induct arbitrary: xs)
     case lfinite_LNil
     then show ?case by (metis lfilter_empty_conv lnull_imp_lfinite lsplit.disc(1))
   next
     case (lfinite_LConsI ys y xs)
     then show ?case apply(cases "\<exists>x\<in>lset xs. pred x")
       subgoal by simp (meson LCons_lfilter_ldropUntil)
       subgoal using lnull_imp_lfinite lsplit.disc(1) by blast .      
   qed 
  }
  thus ?thesis using assms by auto
qed
 
lemma lconcat_lsplit_lfinite: 
assumes "lfinite (lfilter pred xs)"
shows "\<exists>ys. xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) ys \<and> (\<forall>y\<in>lset ys. \<not> pred y)"
proof-
  {fix ys assume "lfinite ys"  "ys = lfilter pred xs"
   hence ?thesis proof(induct arbitrary: xs)
     case lfinite_LNil
     then show ?case 
     by (metis lappend_code(1) lconcat_LNil llist.disc(1) llist.simps(12) lnull_lfilter lsplit.ctr(1))
   next
     case (lfinite_LConsI ys y xs)
     then show ?case apply(cases "\<exists>x\<in>lset xs. pred x")
       subgoal by simp (smt (verit) LCons_lfilter_ldropUntil lappend_assoc lappend_ltakeUntil_ldropUntil)
       subgoal by simp .
   qed 
  }
  thus ?thesis using assms by auto
qed

lemma lconcat_lsplit: 
"\<exists>ys. xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) ys \<and> (\<forall>y\<in>lset ys. \<not> pred y)"
proof(cases "lfinite (lfilter pred xs)")
  case True
  show ?thesis using lconcat_lsplit_lfinite[OF True] .
next
  case False
  show ?thesis apply(rule exI[of _ LNil]) 
  using lconcat_lsplit_not_lfinite[OF False] by simp
qed

lemma lsublist_lsplit: 
assumes "i < llength (lsplit pred xs)"
shows "lsublist (llist_of (lnth (lsplit pred xs) i)) xs"
by (metis assms lconcat_lsplit lnth_lconcat_lconcat_lsublist)  

lemma lsublist_lsplit2: 
assumes "Suc i < llength (lsplit pred xs)"
shows "lsublist (llist_of (append (lnth (lsplit pred xs) i) (lnth (lsplit pred xs) (Suc i)))) xs"
by (metis assms lconcat_lsplit lnth_lconcat_lconcat_lsublist2) 

lemma lsplit_main: 
"llist_all (\<lambda>zs. zs \<noteq> [] \<and> list_all (\<lambda>z. \<not> pred z) (butlast zs) \<and> pred (last zs)) 
           (lsplit pred xs)"
proof-
  {fix ys assume "\<exists>xs. ys = (lsplit pred xs)"
   hence "llist_all (\<lambda>zs. zs \<noteq> [] \<and> list_all (\<lambda>z. \<not> pred z) (butlast zs) \<and> pred (last zs))  ys"
   apply(coinduct rule: llist_all_conduct[where X = "\<lambda>ys. \<exists>xs. ys = (lsplit pred xs)"]) 
   apply safe
     subgoal by simp (meson ltakeUntil_not_Nil)  
     subgoal by simp (metis ltakeUntil_never_butlast) 
     subgoal by simp (meson ltakeUntil_last)
     subgoal by auto .
  }
  thus ?thesis by auto
qed

lemma lsplit_main_lset:  
assumes "ys \<in> lset (lsplit pred xs)"
shows "ys \<noteq> [] \<and> 
       list_all (\<lambda>z. \<not> pred z) (butlast ys) \<and> 
       pred (last ys)" 
using assms lsplit_main[of pred] unfolding llist.pred_set by auto

lemma lsplit_main_lnth:  
assumes "i < llength (lsplit pred xs)"
shows "lnth (lsplit pred xs) i \<noteq> [] \<and> 
       list_all (\<lambda>z. \<not> pred z) (butlast (lnth (lsplit pred xs) i)) \<and> 
       pred (last (lnth (lsplit pred xs) i))" 
using assms lsplit_main[of pred] unfolding llist_all_lnth by auto

lemma hd_lhd_lsplit: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> hd (lhd (lsplit pred xs)) = lhd xs"
by (metis lappend_ltakeUntil_ldropUntil lhd_lappend lhd_llist_of lnull_llist_of lsplit.simps(3) ltakeUntil_not_Nil)

lemma lprefix_lsplit: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "lprefix (llist_of (lhd (lsplit pred xs))) xs"
by (metis assms lappend_ltakeUntil_ldropUntil lprefix_lappend lsplit.simps(3)) 

lemma lprefix_lsplit_lbutlast: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "lprefix (llist_of (butlast (lhd (lsplit pred xs)))) (lbutlast xs)"
using lprefix_lsplit[OF assms] unfolding llist_of_butlast 
using lprefix_lbutlast by blast

lemma set_lset_lsplit: 
assumes "ys \<in> lset (lsplit pred xs)"
shows "set ys \<subseteq> lset xs"
proof-
  have "set ys \<subseteq> lset (lconcat (lmap llist_of (lsplit pred xs)))" 
  using su_lset_lconcat_llist_of[OF assms ] .   
  also have "\<dots> \<subseteq> lset xs" 
  by (metis lconcat_lsplit lset_lappend1)
  finally show ?thesis .
qed

lemma set_lnth_lsplit: 
assumes "i < llength (lsplit pred xs)"  
shows "set (lnth (lsplit pred xs) i) \<subseteq> lset xs"
by (meson assms in_lset_conv_lnth set_lset_lsplit)


subsection \<open>The split remainder \<close>

definition "lsplitRemainder pred xs \<equiv> SOME ys. xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) ys \<and> (\<forall>y\<in>lset ys. \<not> pred y)"

lemma lsplitRemainder: 
"xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) (lsplitRemainder pred xs) \<and> 
(\<forall>y\<in>lset (lsplitRemainder pred xs). \<not> pred y)"
unfolding lsplitRemainder_def apply(rule someI_ex) using lconcat_lsplit .

lemmas lsplit_lsplitRemainder = lsplitRemainder[THEN conjunct1]
lemmas lset_lsplitRemainder = lsplitRemainder[THEN conjunct2, rule_format]


subsection \<open>The first index for which a predicate holds (if any) \<close> 

definition firstHolds where 
"firstHolds pred xs \<equiv> length (ltakeUntil pred xs) - 1"

lemma firstHolds_eq_0: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "firstHolds pred xs = 0 \<longleftrightarrow> pred (lhd xs)"
using assms unfolding firstHolds_def 
by (metis Suc_pred diff_Suc_1 length_ltakeUntil_eq_1 length_ltakeUntil_ge_0)

lemma firstHolds_eq_0': 
assumes "\<not> lnever pred xs"
shows "firstHolds pred xs = 0 \<longleftrightarrow> pred (lhd xs)"
apply(rule firstHolds_eq_0)
using assms by (simp add: llist.pred_set)

lemma firstHolds_Suc: 
assumes "\<exists>x\<in>lset xs. pred x" and "\<not> pred (lhd xs)"
shows "firstHolds pred xs = Suc (firstHolds pred (ltl xs))"
using assms unfolding firstHolds_def 
by (smt (verit, best) Suc_pred diff_Suc_1 length_greater_0_conv length_ltakeUntil_Suc 
   length_ltakeUntil_eq_1 list.size(3))

lemma firstHolds_Suc': 
assumes "\<not> lnever pred xs" and "\<not> pred (lhd xs)"
shows "firstHolds pred xs = Suc (firstHolds pred (ltl xs))"
apply(rule firstHolds_Suc) using assms by (auto simp: llist.pred_set)

lemma firstHolds_append: 
assumes "\<not> lnever pred xs" and "never pred ys"
shows "firstHolds pred (lappend (llist_of ys) xs) = length ys + firstHolds pred xs"
using assms by (induct ys) (auto simp add: llist_all_lappend_llist_of firstHolds_Suc') 


subsection \<open>The first index for which the list in a lazy-list of lists is non-empty\<close> 

definition firstNC where 
"firstNC xss \<equiv> firstHolds (\<lambda>xs. xs \<noteq> []) xss"

lemma firstNC_eq_0: 
assumes "\<exists>xs\<in>lset xss. xs \<noteq> []"
shows "firstNC xss = 0 \<longleftrightarrow> lhd xss \<noteq> []"
using assms unfolding firstNC_def 
by (simp add: firstHolds_eq_0)

lemma firstNC_Suc: 
assumes "\<exists>xs\<in>lset xss. xs \<noteq> []" and "lhd xss = []"
shows "firstNC xss = Suc (firstNC (ltl xss))"
using assms unfolding firstNC_def by (simp add: firstHolds_Suc) 

lemma firstNC_LCons_notNil: "xs \<noteq> [] \<Longrightarrow> firstNC (xs $ xss) = 0"
by (simp add: firstNC_eq_0)

lemma firstNC_LCons_Nil: 
"(\<exists>ys\<in>lset xss. ys \<noteq> []) \<Longrightarrow> xs = [] \<Longrightarrow> firstNC (xs $ xss) = Suc (firstNC xss)"
by (simp add: firstNC_Suc)


end 