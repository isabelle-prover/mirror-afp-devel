section \<open>Filtermap for Lazy Lists\<close>

theory LazyList_Filtermap
  imports LazyList_Operations List_Filtermap
begin

text \<open> This theory defines the filtermap operator for lazy lists, proves its basic properties, 
and proves a coinductive criterion for the euqlity of two filtermapped lazy lsits. \<close>


subsection \<open>Lazy lists filtermap\<close>

definition lfiltermap ::
"('trans \<Rightarrow> bool) \<Rightarrow> ('trans \<Rightarrow> 'a) \<Rightarrow> 'trans llist \<Rightarrow> 'a llist"
where
"lfiltermap pred func tr \<equiv> lmap func (lfilter pred tr)"

lemmas lfiltermap_lmap_lfilter = lfiltermap_def

lemma lfiltermap_lappend: "lfinite tr \<Longrightarrow> lfiltermap pred func (lappend tr tr1) = 
  lappend (lfiltermap pred func tr) (lfiltermap pred func tr1)"
unfolding lfiltermap_def by (simp add: lmap_lappend_distrib)

lemma lfiltermap_LNil_never: "lfiltermap pred func tr = [[]] \<longleftrightarrow> lnever pred tr"
by (simp add: lfilter_empty_conv lfiltermap_lmap_lfilter llist.pred_set)

lemma llength_lfiltermap: "llength (lfiltermap pred func tr) \<le> llength tr"
by (simp add: lfiltermap_lmap_lfilter llength_lfilter_ile)

lemma lfiltermap_llist_all[simp]: "lfinite tr \<Longrightarrow> lfiltermap pred func tr = lmap func tr \<longleftrightarrow> llist_all pred tr"
apply (induction "list_of tr" arbitrary: tr)
  subgoal using llist_of_list_of   
    by (metis lfiltermap_LNil_never llist.pred_inject(1) llist.simps(12) llist_of.simps(1) llist_of_list_of) 
  subgoal for a x tr apply(cases tr, auto)  
    apply (metis iless_Suc_eq length_list_of lfilter_LCons lfiltermap_lmap_lfilter 
    lfinite_LConsI linorder_not_less llength_LCons llength_lfiltermap llength_lmap)
    apply (metis Suc_ile_eq eSuc_enat length_list_of lfilter_LCons lfiltermap_lmap_lfilter linorder_not_less 
      llength_LCons llength_lfiltermap llength_lmap llist.sel(3) ltl_lmap)
    by (simp add: lfiltermap_lmap_lfilter) .

lemma lfilter_LNil_lnever: "[[]] = lfilter pred xs \<Longrightarrow> lnever pred xs"
by (metis lfiltermap_LNil_never lfiltermap_lmap_lfilter llist.simps(12))

lemma lnever_LNil_lfilter: "lnever pred xs \<longleftrightarrow> [[]] = lfilter pred xs"
by (metis lfilter_empty_conv llist.pred_set)

lemma lfilter_LNil_lnever': "lfilter pred xs = [[]] \<Longrightarrow> lnever pred xs"
by (metis lfiltermap_LNil_never lfiltermap_lmap_lfilter llist.simps(12))

lemma lnever_LNil_lfilter': "lnever pred xs \<longleftrightarrow> lfilter pred xs = [[]]"
by (metis lfilter_empty_conv llist.pred_set)

lemma lfiltermap_LCons2_eq:
     "lfiltermap pred func [[x, x']] = lfiltermap pred func [[y, y']]
  \<Longrightarrow> lfiltermap pred func (x $ x' $ zs) = lfiltermap pred func (y $ y' $ zs)"
by (metis lappend_code(1) lappend_code(2) lfiltermap_lappend lfinite_LCons lfinite_LNil)

lemma lfiltermap_LCons_cong:
   "lfiltermap pred func xs = lfiltermap pred func ys
\<Longrightarrow> lfiltermap pred func (x $ xs) = lfiltermap pred func (x $ ys)"
by (simp add: lfiltermap_lmap_lfilter)

lemma lfiltermap_LCons_eq:
   "lfiltermap pred func xs = lfiltermap pred func ys
\<Longrightarrow> pred x \<longleftrightarrow> pred y
\<Longrightarrow> pred x \<longrightarrow> func x = func y
\<Longrightarrow> lfiltermap pred func (x $ xs) = lfiltermap pred func (y $ ys)"
by (simp add: lfiltermap_lmap_lfilter)

lemma set_lfiltermap:
"lset (lfiltermap pred func xs) \<subseteq> {func x | x . x \<in> lset xs \<and> pred x}"
unfolding lfiltermap_def by auto

lemma lfinite_lfiltermap_filtermap: 
"lfinite xs \<Longrightarrow> lfiltermap pred func xs = llist_of (filtermap pred func (list_of xs))" 
by (induct rule: lfinite.induct, auto simp: lfiltermap_lmap_lfilter) 

lemma lfiltermap_llist_of_filtermap: 
"lfiltermap pred func(llist_of xs) = llist_of (filtermap pred func xs)"
by (simp add: lfinite_lfiltermap_filtermap)

lemma filtermap_butlast: "xs \<noteq> [] \<Longrightarrow>
    \<not> pred (last xs) \<Longrightarrow>
    filtermap pred func xs = filtermap pred func (butlast xs)"
by (metis append_butlast_last_id not_holds_filtermap_RCons)

lemma filtermap_butlast': 
"xs \<noteq> [] \<Longrightarrow> pred (last xs) \<Longrightarrow> 
 filtermap pred func xs = filtermap pred func (butlast xs) @ [func (last xs)]"
by (metis append_butlast_last_id holds_filtermap_RCons)

lemma lfinite_lfiltermap_butlast: "xs \<noteq> [[]] \<Longrightarrow> (lfinite xs \<Longrightarrow> \<not> pred (llast xs)) \<Longrightarrow> 
lfiltermap pred func xs = lfiltermap pred func (lbutlast xs)"
unfolding lbutlast_def 
by (metis (full_types) filtermap_butlast lfiltermap_llist_of_filtermap llast_last_llist_of 
llist_of.simps(1) llist_of_list_of)  

lemma last_filtermap: "xs \<noteq> [] \<Longrightarrow> pred (last xs) \<Longrightarrow> 
  filtermap pred func xs \<noteq> [] \<and> last (filtermap pred func xs) = func (last xs)"
by (metis holds_filtermap_RCons snoc_eq_iff_butlast)

(* *)

lemma filtermap_ltakeUntil[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> filtermap pred func (ltakeUntil pred xs) = [func (last (ltakeUntil pred xs))]"
unfolding filtermap_def  
by (smt (verit, del_insts) Cons_eq_map_conv append_butlast_last_id append_self_conv2 filter.simps(1) 
filter_eq_Cons_iff ltakeUntil_ex_butlast ltakeUntil_last ltakeUntil_not_Nil map_append)

lemma last_ltakeUntil_filtermap[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> func (last (ltakeUntil pred xs)) = lhd (lfiltermap pred func xs)"
unfolding lfiltermap_lmap_lfilter  
by simp (metis (no_types, lifting) ldropWhile_cong lfinite_LConsI lfinite_LNil lfinite_lappend 
lfinite_ltakeWhile llast_lappend_LCons llast_llist_of llast_singleton llist_of_list_of ltakeUntil_def)

lemma lfiltermap_lmap_filtermap_lsplit:
assumes "lfiltermap pred func xs = lfiltermap pred func ys"
shows "lmap (filtermap pred func) (lsplit pred xs) = lmap (filtermap pred func) (lsplit pred ys)"
using assms apply(coinduction arbitrary: xs ys) 
by simp (smt (verit, best) LCons_lfilter_ldropUntil lfiltermap_lmap_lfilter 
  llist.map_disc_iff lnull_lfilter ltl_lmap ltl_simps(2) not_lnull_conv)

lemma lfiltermap_lfinite_lsplit:
assumes "lfiltermap pred func xs = lfiltermap pred func ys"
shows "lfinite (lsplit pred xs) \<longleftrightarrow> lfinite (lsplit pred ys)" 
by (metis assms lfiltermap_lmap_filtermap_lsplit llength_eq_infty_conv_lfinite llength_lmap)

lemma lfiltermap_lsplitRemainder[simp]: "lfiltermap pred func (lsplitRemainder pred xs) = [[]]"
by (metis lfiltermap_LNil_never llist.pred_set lset_lsplitRemainder)

lemma lfiltermap_lconcat_lsplit: 
"lfiltermap pred func xs = 
 lfiltermap pred func (lconcat (lmap llist_of (lsplit pred xs)))"
apply(subst lsplit_lsplitRemainder[of xs pred])
apply(cases "lfinite (lconcat (lmap llist_of (lsplit pred xs)))")
  subgoal apply(subst lfiltermap_lappend) by auto
  subgoal apply(subst lappend_inf) by auto .

lemma lfilter_lconcat_lfinite': "(\<And>i. i < llength yss \<Longrightarrow> lfinite (lnth yss i)) 
\<Longrightarrow> lfilter pred (lconcat yss) = lconcat (lmap (lfilter pred) yss)" 
by (metis in_lset_conv_lnth lfilter_lconcat_lfinite)

lemma lfilter_lconcat_llist_of: 
"lfilter pred (lconcat (lmap llist_of yss)) = lconcat (lmap (lfilter pred) (lmap llist_of yss))" 
apply(rule lfilter_lconcat_lfinite) by auto

lemma lfiltermap_lconcat_lmap_llist_of: 
"lfiltermap pred func (lconcat (lmap llist_of yss)) = 
 lconcat (lmap (llist_of o filtermap pred func) yss)" 
unfolding lfiltermap_def lfilter_lconcat_llist_of 
unfolding lmap_lconcat filtermap_def 
by simp (smt (verit, best) in_lset_conv_lnth lfilter_llist_of 
 llength_lmap llist.map_comp llist.map_cong lmap_llist_of lnth_lmap)

lemma filtermap_noteq_imp_lsplit:
assumes len: "llength (lsplit pred xs) = llength (lsplit pred xs')"
and l: "lfiltermap pred func xs \<noteq> lfiltermap pred func xs'"
shows "\<exists>i0<llength (lsplit pred xs). 
   filtermap pred func (lnth (lsplit pred xs) i0) \<noteq> 
   filtermap pred func (lnth (lsplit pred xs') i0)"
proof-
  define yss where yss: "yss \<equiv> lsplit pred xs" 
  define yss' where yss': "yss' \<equiv> lsplit pred xs'" 
  define u where u: "u = lmap (llist_of o filtermap pred func) yss"
  define u' where u': "u' = lmap (llist_of o filtermap pred func) yss'"
  have "lfiltermap pred func (lconcat (lmap llist_of yss)) \<noteq> 
        lfiltermap pred func (lconcat (lmap llist_of yss'))" 
  using l[unfolded lfiltermap_lconcat_lsplit[of pred func xs]
                   lfiltermap_lconcat_lsplit[of pred func xs']]
  unfolding yss yss' .
  hence "lconcat u \<noteq> lconcat u'" 
  unfolding lfiltermap_lconcat_lmap_llist_of u u' .
  hence "u \<noteq> u'" by auto
  moreover have "llength u = llength u'"  
    by (simp add: u u' len yss yss')
  ultimately obtain i0 where 0: "i0 < llength u" "lnth u i0 \<noteq> lnth u' i0" 
  by (metis llist.rel_eq llist_all2_all_lnthI)

  show ?thesis unfolding yss[symmetric] yss'[symmetric] apply(rule exI[of _ i0])
  using 0 len unfolding u u'  
  by simp (metis lnth_lmap yss yss')
qed


subsection \<open>Coinductive criterion for filtermap equality\<close>

text \<open>We work in a locale that fixes two function-predicate pairs, 
for performing two instances of filtermap. We will give criteria for 
when the two filtermap applications to two lazy lists are equal. \<close>

locale TwoFuncPred = 
fixes pred :: "'a \<Rightarrow> bool" and pred' :: "'a' \<Rightarrow> bool" 
and func :: "'a \<Rightarrow> 'b" and func' :: "'a' \<Rightarrow> 'b"
begin

lemma LCons_eq_lmap_lfilter: 
assumes "LCons b bss = lmap func (lfilter pred as)" 
shows "\<exists>as1 a ass. 
   as = lappend (llist_of as1) (LCons a ass) \<and> 
   never pred as1 \<and> pred a \<and> func a = b \<and> 
   bss = lmap func (lfilter pred ass)"
proof-
  obtain a ass' where 1: "lfilter pred as = LCons a ass'" "b = func a" "bss = lmap func ass'"
  using assms by (metis lmap_eq_LCons_conv)
  obtain us vs where 2: "as = lappend us (a $ vs)" "lfinite us"
  "\<forall>u\<in>lset us. \<not> pred u" "pred a" "ass' = lfilter pred vs"
  using lfilter_eq_LConsD[OF 1(1)] by auto
  show ?thesis apply(rule exI[of _ "list_of us"]) apply(rule exI[of _ a]) apply(rule exI[of _ "vs"]) 
  using 1 2  
  by simp (metis Ball_set set_list_of) 
qed

lemma LCons_eq_lmap_lfilter': 
assumes "LCons b bss = lmap func' (lfilter pred' as)" 
shows "\<exists>as1 a ass. 
   as = lappend (llist_of as1) (LCons a ass) \<and> 
   never pred' as1 \<and> pred' a \<and> func' a = b \<and> 
   bss = lmap func' (lfilter pred' ass)"
proof-
  obtain a ass' where 1: "lfilter pred' as = LCons a ass'" "b = func' a" "bss = lmap func' ass'"
  using assms by (metis lmap_eq_LCons_conv)
  obtain us vs where 2: "as = lappend us (a $ vs)" "lfinite us"
  "\<forall>u\<in>lset us. \<not> pred' u" "pred' a" "ass' = lfilter pred' vs"
  using lfilter_eq_LConsD[OF 1(1)] by auto
  show ?thesis apply(rule exI[of _ "list_of us"]) apply(rule exI[of _ a]) apply(rule exI[of _ "vs"]) 
  using 1 2  
  by simp (metis Ball_set set_list_of) 
qed

lemma lmap_lfilter_lappend_lnever: 
assumes P: "P lxs lxs'"
and lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
shows "lnever pred lxs = lnever pred' lxs'"
proof safe
  assume ln: "lnever pred lxs"
  show "lnever pred' lxs'"
  unfolding llist_all_lnth using P ln apply (intro allI impI)
  subgoal for i proof(induct i arbitrary: lxs lxs' rule: less_induct)
    case (less i lxs lxs')
    show ?case using lappend[OF less(2)] proof(elim disjE exE conjE)
      fix ys llxs ys' llxs'
      assume yss': "ys \<noteq> []" "ys' \<noteq> []" "map func (filter pred ys) = map func' (filter pred' ys')"
      and lxs: "lxs = lappend (llist_of ys) llxs" and lxs': "lxs' = lappend (llist_of ys') llxs'" 
      and P: "P llxs llxs'" 
      have lnys: "never pred ys" and lnllxs: "lnever pred llxs" using `lnever pred lxs` unfolding lxs 
        by (auto simp add: list_all_iff llist.pred_set) 
      hence lnys': "never pred' ys'" using yss'(2)  
        by (metis Nil_is_map_conv never_Nil_filter yss'(3))
      show "\<not> pred' (lnth lxs' i)" 
      proof(cases "i < length ys'")
        case True note i = True
        hence 0: "lnth lxs' i = ys' ! i" unfolding lxs lxs'  
          by (auto simp: lnth_lappend_llist_of)
        show ?thesis using lnys' i unfolding 0 
          by (simp add: list_all_length)
      next
        case False note i = False
        then obtain j where i: "i = length ys' + j" 
        using le_Suc_ex not_le_imp_less by blast
        hence j: "j < llength llxs'" using `i < llength lxs'` unfolding lxs' 
        using enat_add_mono by fastforce 
        hence 0: "lnth lxs' i = lnth llxs' j" unfolding lxs lxs'  
        unfolding i  by (auto simp: lnth_lappend_llist_of)
        show ?thesis unfolding 0 apply(rule less(1)[rule_format, OF _ P])
        using j P yss' less.prems lnllxs unfolding i by auto 
      qed
    qed(metis less.prems(2) less.prems(3) llist_all_lnth lmap_eq_LNil lnever_LNil_lfilter')
  qed .
next
  assume ln': "lnever pred' lxs'"
  show "lnever pred lxs"
  unfolding llist_all_lnth using P ln' apply (intro allI impI)
  subgoal for i proof(induct i arbitrary: lxs lxs' rule: less_induct)
    case (less i lxs lxs')
    show ?case using lappend[OF less(2)] proof(elim disjE exE conjE)
      fix ys llxs ys' llxs'
      assume yss': "ys \<noteq> []" "ys' \<noteq> []" "map func (filter pred ys) = map func' (filter pred' ys')"
      and lxs: "lxs = lappend (llist_of ys) llxs" and lxs': "lxs' = lappend (llist_of ys') llxs'" 
      and P: "P llxs llxs'" 
      have lnys': "never pred' ys'" and lnllxs: "lnever pred' llxs'" using `lnever pred' lxs'` unfolding lxs' 
        by (auto simp add: list_all_iff llist.pred_set) 
      hence lnys: "never pred ys" using yss'(2)  
        by (metis Nil_is_map_conv never_Nil_filter yss'(3))
      show "\<not> pred (lnth lxs i)" 
      proof(cases "i < length ys")
        case True note i = True
        hence 0: "lnth lxs i = ys ! i" unfolding lxs lxs'  
          by (auto simp: lnth_lappend_llist_of)
        show ?thesis using lnys i unfolding 0  
          by (simp add: list_all_length)
      next
        case False note i = False
        then obtain j where i: "i = length ys + j" 
        using le_Suc_ex not_le_imp_less by blast
        hence j: "j < llength llxs" using `i < llength lxs` unfolding lxs
        using enat_add_mono by fastforce 
        hence 0: "lnth lxs i = lnth llxs j" unfolding lxs lxs'  
        unfolding i  by (auto simp: lnth_lappend_llist_of)
        show ?thesis unfolding 0 apply(rule less(1)[rule_format, OF _ P])
        using j P yss' less.prems lnllxs unfolding i by auto 
      qed
    qed(metis less.prems(2) less.prems(3) llist_all_lnth lmap_eq_LNil lnever_LNil_lfilter')
  qed .
qed

(* Key lemma: From the weaker assumption ys \<noteq> [] \<and> ys' \<noteq> [], 
move to the stronger one "map func (filter pred ys) \<noteq> []" 
(and also "map func (filter pred ys') \<noteq> []" since the two are assumed equal). 
*)
lemma lmap_lfilter_lappend_makeStronger: 
assumes lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
and P: "P lxs lxs'" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       map func (filter pred ys) \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')"
using P proof(induct "firstHolds pred lxs" arbitrary: lxs lxs' rule: less_induct)
  case (less lxs lxs')
  show ?case using lappend[OF less(2)] proof(elim disjE allE conjE exE)
    fix ys llxs ys' llxs'
    assume yss': "ys \<noteq> []" "ys' \<noteq> []" "map func (filter pred ys) = map func' (filter pred' ys')"
    and lxs: "lxs = lappend (llist_of ys) llxs" and lxs': "lxs' = lappend (llist_of ys') llxs'"
    and P: "P llxs llxs'"
    show ?thesis
    proof(cases "lnever pred lxs")
      case True note ln = True
      hence ln': "lnever pred' lxs'" 
      using lappend less.prems lmap_lfilter_lappend_lnever by blast
      show ?thesis apply(rule disjI1)
      using ln ln' by (simp add: lnever_LNil_lfilter')
    next
      case False note ln = False
      hence ln': "\<not> lnever pred' lxs'" 
      using lappend less.prems lmap_lfilter_lappend_lnever by blast
      have "\<not> never pred ys \<or> (never pred ys \<and> \<not> lnever pred llxs)" using ln unfolding lxs
      unfolding llist_all_lappend_llist_of by simp
      thus ?thesis proof(elim disjE conjE)
        assume ys: "\<not> never pred ys"
        show ?thesis apply(rule disjI2)
        apply(rule exI[of _ ys]) apply(rule exI[of _ llxs]) apply(rule exI[of _ ys']) apply(rule exI[of _ llxs'])
        using yss' lxs lxs' P ys by (auto simp:  never_Nil_filter)
      next
        assume ys: "never pred ys" and llxs: "\<not> lnever pred llxs"
        hence ys': "never pred' ys'" and llxs': "\<not> lnever pred' llxs'"      
        apply (metis Nil_is_map_conv never_Nil_filter yss'(3)) 
        using P lappend llxs lmap_lfilter_lappend_lnever by blast

        have firstHolds: "firstHolds pred llxs < firstHolds pred lxs"
        unfolding lxs firstHolds_append[OF llxs ys] using yss' by simp 
      
        show ?thesis proof(cases "lmap func (lfilter pred llxs) = lmap func' (lfilter pred' llxs')")
          case True
          hence "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
          unfolding lxs lxs' using ys ys' 
          by (simp add: lmap_lappend_distrib yss'(3))
          thus ?thesis by simp
        next
          case False
          then obtain yys lllxs yys' lllxs' where yyss': "map func (filter pred yys) \<noteq> []" 
          "map func (filter pred yys) = map func' (filter pred' yys')"
          and llxs: "llxs = lappend (llist_of yys) lllxs" and llxs': "llxs' = lappend (llist_of yys') lllxs'" 
          and "P lllxs lllxs'" using less(1)[OF firstHolds P] by blast
        
          show ?thesis apply(rule disjI2) 
          apply(rule exI[of _ "ys @ yys"]) apply(rule exI[of _ lllxs])
          apply(rule exI[of _ "ys' @ yys'"]) apply(rule exI[of _ lllxs'])
          apply(intro conjI)
            subgoal using yyss'(1) by simp
            subgoal apply simp unfolding yss'(3) yyss'(2) ..
            subgoal unfolding lxs llxs lappend_assoc lappend_llist_of_llist_of[symmetric] ..
            subgoal unfolding lxs' llxs' lappend_assoc lappend_llist_of_llist_of[symmetric] .. 
            subgoal by fact .   
        qed
      qed 
    qed
  qed simp
qed


(* The "raw" version of the criterion ensures coinductive progress via "ys \<noteq> [] \<and> ys' \<noteq> []". *)

proposition lmap_lfilter_lappend_coind: 
assumes P: "P lxs lxs'"
and lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
proof-
  have lappend: 
  "\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.               
       map func (filter pred ys) \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
  using lmap_lfilter_lappend_makeStronger[OF lappend] by auto
  show ?thesis apply(rule llist_lappend_coind[where P = "\<lambda>as as'. 
    \<exists>lxs lxs'. as = lmap func (lfilter pred lxs) \<and> 
               as' = lmap func' (lfilter pred' lxs') \<and> 
               P lxs lxs'"])
    subgoal using P by auto
    subgoal for lxs lxs' using lappend  
    by (smt (verit, ccfv_SIG) lfilter_lappend_llist_of list.map_disc_iff lmap_lappend_distrib lmap_llist_of) .
qed 


(* The criterion can be enhanced by plugging in descent via a well-founded relation 
as an alternative to "ys \<noteq> [] \<and> ys' \<noteq> []". *)

proposition lmap_lfilter_lappend_coind_wf: 
assumes W: "wf W" and P: "P w lxs lxs'"
and lappend: 
"\<And>w lxs lxs'. P w lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>v ys llxs ys' llxs'.        
       (ys \<noteq> [] \<and> ys' \<noteq> [] \<or> (v,w) \<in> W) \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v llxs llxs')" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
proof-
  define Q where "Q \<equiv> \<lambda> llxs llxs'. \<exists>w. P w llxs llxs'"
  have Q: "Q lxs lxs'" using P unfolding Q_def by auto
  {fix lxs lxs' assume "Q lxs lxs'"
   then obtain w where "P w lxs lxs'" using Q_def by auto
   hence "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
     (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       Q llxs llxs')" 
   proof(induct w arbitrary: lxs lxs' rule: wf_induct_rule[OF W])
     case (1 w lxs lxs')
     show ?case using lappend[OF 1(2)] apply(elim disjE)
       subgoal by simp
       subgoal proof(elim exE disjE conjE)
         fix v ys llxs ys' llxs' assume vw: "(v, w) \<in> W"
         and yss': "map func (filter pred ys) = map func' (filter pred' ys')"
         and lxs: "lxs = lappend (llist_of ys) llxs"
         and lxs': "lxs' = lappend (llist_of ys') llxs'"
         and P: "P v llxs llxs'"
         show ?thesis
         proof(cases "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')")
           case True
           thus ?thesis by simp
         next
           case False
           hence "lmap func (lfilter pred llxs) \<noteq> lmap func' (lfilter pred' llxs')"
           using yss' unfolding lxs lxs' by (auto simp: lmap_lappend_distrib)
           then obtain yys lllxs yys' lllxs' where yyss': "yys \<noteq> []" "yys' \<noteq> []"
           "map func (filter pred yys) = map func' (filter pred' yys')"
           and llxs: "llxs = lappend (llist_of yys) lllxs"
           and llxs': "llxs' = lappend (llist_of yys') lllxs'"
           and "Q lllxs lllxs'"using 1(1)[OF vw P] by auto
           show ?thesis apply(rule disjI2)
           apply(rule exI[of _ "ys @ yys"]) apply(rule exI[of _ lllxs])
           apply(rule exI[of _ "ys' @ yys'"]) apply(rule exI[of _ lllxs'])
           apply(intro conjI)
            subgoal using yyss'(1) by simp
            subgoal using yyss'(2) by simp
            subgoal apply simp unfolding yss' yyss' ..
            subgoal unfolding lxs llxs lappend_assoc lappend_llist_of_llist_of[symmetric] ..
            subgoal unfolding lxs' llxs' lappend_assoc lappend_llist_of_llist_of[symmetric] .. 
            subgoal by fact . 
       qed 
     qed (unfold Q_def,blast) .
   qed 
  } note lappend = this
  show ?thesis apply(rule lmap_lfilter_lappend_coind[of Q, OF Q lappend]) by auto
qed


(* And finally a version with well-founded descent separated for ys and ys': *)

proposition lmap_lfilter_lappend_coind_wf2: 
assumes W1: "wf (W1::'a1 rel)" and W2: "wf (W2::'a2 rel)" 
and P: "P w1 w2 lxs lxs'"
and lappend: 
"\<And>w1 w2 lxs lxs'. P w1 w2 lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>v1 v2 ys llxs ys' llxs'.        
       ((v1,w1) \<in> W1 \<or> ys \<noteq> []) \<and> ((v2,w2) \<in> W2 \<or> ys' \<noteq> []) \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v1 v2 llxs llxs')" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
proof-
  {fix w1 w2  lxs lxs' assume "P w1 w2 lxs lxs'" 
   hence "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
     (\<exists>v1 v2 ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> (ys' \<noteq> [] \<or> (v2,w2) \<in> trancl W2) \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v1 v2 llxs llxs')" 
   proof(induct w1 arbitrary: w2 lxs lxs' rule: wf_induct_rule[OF W1])
     case (1 w1 w2 lxs lxs')
     show ?case using lappend[OF 1(2)] apply(elim disjE)
       subgoal by simp 
       subgoal proof(elim exE conjE)
         fix v1 v2 ys llxs ys' llxs' assume vw1: "(v1, w1) \<in> W1 \<or> ys \<noteq> []"
         and vw2: "(v2, w2) \<in> W2 \<or> ys' \<noteq> []"
         and yss': "map func (filter pred ys) = map func' (filter pred' ys')"
         and lxs: "lxs = lappend (llist_of ys) llxs"
         and lxs': "lxs' = lappend (llist_of ys') llxs'"
         and P: "P v1 v2 llxs llxs'"
         show ?thesis 
         proof(cases "ys \<noteq> []")
           case True
           thus ?thesis using vw2 yss' lxs lxs' P by blast
         next
           case False note ys = False         
           hence vw1: "(v1, w1) \<in> W1" using vw1 by auto
           show ?thesis
           proof(cases "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')")
             case True
             thus ?thesis by simp
           next
             case False
             hence "lmap func (lfilter pred llxs) \<noteq> lmap func' (lfilter pred' llxs')"
             using yss' unfolding lxs lxs' by (auto simp: lmap_lappend_distrib)
             then obtain v1 vv2 yys lllxs yys' lllxs' where yyss': "yys \<noteq> []" "yys' \<noteq> [] \<or> (vv2,v2) \<in> trancl W2"
             "map func (filter pred yys) = map func' (filter pred' yys')"
             and llxs: "llxs = lappend (llist_of yys) lllxs"
             and llxs': "llxs' = lappend (llist_of yys') lllxs'"
             and "P v1 vv2 lllxs lllxs'"using 1(1)[OF vw1 P] by blast
             show ?thesis apply(rule disjI2)
             apply(rule exI[of _ v1]) apply(rule exI[of _ vv2])
             apply(rule exI[of _ "ys @ yys"]) apply(rule exI[of _ lllxs])
             apply(rule exI[of _ "ys' @ yys'"]) apply(rule exI[of _ lllxs'])
             apply(intro conjI)
               subgoal using yyss'(1) by simp
               subgoal using yyss'(2) vw2 by auto
               subgoal apply simp unfolding yss' yyss' ..
               subgoal unfolding lxs llxs lappend_assoc lappend_llist_of_llist_of[symmetric] ..
               subgoal unfolding lxs' llxs' lappend_assoc lappend_llist_of_llist_of[symmetric] .. 
               subgoal by fact . 
         qed 
       qed 
     qed . 
   qed
  } note lappend = this
  (* *)
  define Q where "Q \<equiv> \<lambda> w2 llxs llxs'. \<exists>w1. P w1 w2 llxs llxs'" 
  have W2p: "wf (W2\<^sup>+)"  
    using W2 wf_trancl by blast
  have Q: "Q w2 lxs lxs'" using P unfolding Q_def by auto
  show ?thesis apply(rule lmap_lfilter_lappend_coind_wf[OF W2p, of Q, OF Q])
  using lappend unfolding Q_def by meson
qed


subsection \<open> A concrete instantiation of the criterion\<close>

(* It uses the standard order on extended-naturals. 
``sameFM'' stands for "same filtermap (value)". 
*)

coinductive sameFM :: "enat \<Rightarrow> enat \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
LNil: 
"sameFM wL wR [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> sameFM wL wR [[a]] [[a']]"
|
lappend: 
"(xs \<noteq> [] \<or> vL < wL) \<Longrightarrow> (xs' \<noteq> [] \<or> vR < wR) \<Longrightarrow> 
 map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sameFM vL vR as as'
 \<Longrightarrow> sameFM wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
lmap_lfilter: 
"lmap func (lfilter pred as) = lmap func' (lfilter pred' as') \<Longrightarrow> 
 sameFM wL wR as as'"

proposition sameFM_lmap_lfilter: 
assumes "sameFM wL wR as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
apply(rule lmap_lfilter_lappend_coind_wf2[OF wf wf, of sameFM wL wR])
  subgoal using assms by simp
  subgoal apply (erule sameFM.cases)
  by simp_all blast .

end (* context TwoFuncPred *)


end
