theory BPlusTree_ImpRange
imports
  BPlusTree_Iter
  BPlusTree_Range
  BPlusTree_ImpSplit
begin

abbreviation "blist_leafs_assn k \<equiv> list_assn ((\<lambda> t (ti,r',z',lptrs). bplustree_assn_leafs k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn)"

context split\<^sub>i_tree
begin

lemma list_induct5 [consumes 4, case_names Nil Cons]:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> length zs = length ws \<Longrightarrow> length ws = length vs \<Longrightarrow>
   P [] [] [] [] [] \<Longrightarrow> (\<And>x xs y ys z zs w ws v vs. length xs = length ys \<Longrightarrow>
   length ys = length zs \<Longrightarrow> length zs = length ws \<Longrightarrow> length ws = length vs \<Longrightarrow> P xs ys zs ws vs \<Longrightarrow>
   P (x#xs) (y#ys) (z#zs) (w#ws) (v#vs)) \<Longrightarrow> P xs ys zs ws vs"
proof (induct xs arbitrary: ys zs ws vs)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs ws) then show ?case by ((cases ys, simp_all), (cases zs,simp_all), (cases ws, simp_all)) (cases vs, simp_all)
qed

declare butlast.simps[simp del] last.simps[simp del]
lemma blist_assn_extract_leafs: "
length ts = length tsi \<Longrightarrow>
length tsi = length rs \<Longrightarrow>
blist_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) rs)) (map snd tsi))
=
(\<exists>\<^sub>Aspl. blist_leafs_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip rs spl))) (map snd tsi)) * \<up>(length spl = length rs))"
proof(induction arbitrary: r rule: list_induct3)
  case Nil
  then show ?case
    apply(intro ent_iffI)
    by sep_auto+
next
  case (Cons x xs y ys z zs r)
  show ?case
    using Cons.hyps
    using Cons.hyps
  apply (sep_auto simp add: butlast_double_Cons last_double_Cons)
    supply R= Cons.IH[simplified, of z]
    thm R
    apply(subst R)
  proof(intro ent_iffI, goal_cases)
    case 1
    then show ?case
    apply(sep_auto eintros del: exI simp add: prod_assn_def bplustree_extract_leafs split!: prod.splits)
      subgoal for _ _ spl lptrs
      apply(inst_existentials "lptrs#spl")
        apply auto
        done
      done
  next
    case 2
    then show ?case
    apply(sep_auto eintros del: exI)
      subgoal for spl
      apply(cases spl)
        apply simp
        subgoal for hdspl tlspl
          apply(inst_existentials tlspl)
          apply (auto simp add: prod_assn_def bplustree_extract_leafs split!: prod.splits)
          done
        done
      done
    qed
  qed
declare butlast.simps[simp add] last.simps[simp add]

lemma blist_discard_leafs: 
  assumes 
"length ts = length tsi"
"length tsi = length rs"
"length spl = length rs"
shows
"blist_leafs_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip rs spl))) (map snd tsi)) \<Longrightarrow>\<^sub>A
blist_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) rs)) (map snd tsi))"
  apply (subst blist_assn_extract_leafs[OF assms(1,2)])
  using assms
  by sep_auto

declare butlast.simps[simp del] last.simps[simp del]
lemma split\<^sub>i_leafs_rule_help: 
"sorted_less (separators ts) \<Longrightarrow>
  length tsi = length rs \<Longrightarrow>
  tsi' = (zip (zip (map fst tsi) (zip (butlast (r#rs)) (butlast (rs@[z]))))) (map snd tsi) \<Longrightarrow>
 <is_pfa c tsi (a,n) 
  * blist_assn k ts tsi' > 
    split\<^sub>i (a,n) p 
  <\<lambda>i. \<exists>\<^sub>Aspl.
    is_pfa c tsi (a,n)
    * blist_leafs_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip (butlast (rs@[z])) spl))) (map snd tsi))
    * \<up>(split_relation ts (split ts p) i)
    * \<up>(length spl = length rs) >\<^sub>t" 
proof(rule hoare_triple_preI, goal_cases) 
  case 1
  have ***: "length tsi' = length rs"
    using 1 by auto
  then have *: "length ts = length tsi'"
    using 1 by (auto dest!: mod_starD list_assn_len)
  then have **: "length ts = length tsi"
    using 1 by (auto dest!: mod_starD list_assn_len)
  note R = split\<^sub>i_rule[of ts tsi rs "zip (zip (subtrees tsi) (zip (butlast (r # rs)) rs)) (separators tsi)" r]
  from 1 show ?thesis
    apply(vcg)
    using ** 1(2)
    apply(simp add: blist_assn_extract_leafs)
    find_theorems ex_assn entails
    apply(rule ent_ex_preI)
    subgoal for x spl
      apply(inst_ex_assn spl)
      apply sep_auto
      done
    done
qed
declare butlast.simps[simp add] last.simps[simp add]

lemma fr_refl_rot: "P \<Longrightarrow>\<^sub>A R \<Longrightarrow> F * P \<Longrightarrow>\<^sub>A F * R"
  using fr_refl[of P R F] by (simp add: mult.commute)

declare butlast.simps[simp del] last.simps[simp del]
lemma split\<^sub>i_leafs_rule[sep_heap_rules]: 
  assumes "sorted_less (separators ts)"
  and "length tsi = length rs"
  and "length spl = length rs"
  and "tsi' = zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip (butlast (rs@[z])) spl))) (map snd tsi)"
  shows "
 <is_pfa c tsi (a,n) 
  * blist_leafs_assn k ts tsi' > 
    split\<^sub>i (a,n) p 
  <\<lambda>i. \<exists>\<^sub>Aspl.
    is_pfa c tsi (a,n)
    * blist_leafs_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip (butlast (rs@[z])) spl))) (map snd tsi))
    * \<up>(split_relation ts (split ts p) i)
    * \<up>(length spl = length rs) >\<^sub>t" 
proof(rule hoare_triple_preI, goal_cases) 
  case 1
  have "length tsi' = length rs"
    using assms by auto
  then have *: "length ts = length tsi'"
    using 1 by (auto dest!: mod_starD list_assn_len)
  then have **: "length ts = length tsi"
    using 1 assms by (auto dest!: mod_starD list_assn_len)
  note R = split\<^sub>i_leafs_rule_help[
    OF assms(1,2),
    of "zip (zip (subtrees tsi) (zip (butlast (r # rs)) (butlast (rs @ [z])))) (separators tsi)" r
        z c a n k
  ]
  thm R
  note R' = fi_rule[OF R, of "is_pfa c tsi (a,n) * blist_leafs_assn k ts tsi'" "emp"]
  thm R'
  show ?case
    apply(vcg heap add: R')
    subgoal
      apply (simp add: assms)
      apply(rule fr_refl_rot)
      using blist_discard_leafs[OF ** assms(2,3)]
      apply auto
      done
    subgoal by sep_auto
    done
qed

end

(* Adding an actual range iterator based on the normal iterator
is trivial (just forward until we reach the first element \<ge> and stop
as soon as we have an element <)
We now try to implement a search for the first element of the range efficiently
 *)
subsection "The imperative split locale"


locale split\<^sub>i_range = abs_split_range: split_range split lrange_list + split\<^sub>i_tree split split\<^sub>i
  for split::
    "('a bplustree \<times> 'a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
    and lrange_list ::  "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a list"
    and split\<^sub>i :: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap" +
  fixes lrange_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfa_it Heap"
  assumes lrange_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ks (a',n')> 
    lrange_list\<^sub>i x (a',n') 
  <pfa_is_it c ks (a',n') (lrange_list x ks)>\<^sub>t"
begin

partial_function (heap) leaf_nodes_lrange\<^sub>i ::
  "'a btnode ref \<Rightarrow> 'a \<Rightarrow> 'a btnode ref option Heap"
  where
    "leaf_nodes_lrange\<^sub>i p x = do {
  node \<leftarrow> !p;
  (case node of
     Btleaf xs z \<Rightarrow> do {
        return (Some p)
      }
       |
     Btnode ts t \<Rightarrow> do {
       i \<leftarrow> split\<^sub>i ts x;
       tsl \<leftarrow> pfa_length ts;
       if i < tsl then do {
         s \<leftarrow> pfa_get ts i;
         let (sub,sep) = s in
           leaf_nodes_lrange\<^sub>i (the sub) x
       } else
           leaf_nodes_lrange\<^sub>i t x
    }
)}"


(* HT when expressed on list of leaves 
lemma leaf_nodes_lrange\<^sub>i_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn_leafs k t ti r z lptrs>
leaf_nodes_lrange\<^sub>i ti x
<\<lambda>p. (\<exists>\<^sub>A xs1 xs2 lptrs1 lptrs2 ps.
  trunk_assn k t ti r z lptrs *
  leaf_nodes_assn k xs1 r p lptrs1 *
  list_assn leaf_node xs2 (map bplustree.vals xs2) *
  list_assn (is_pfa (2 * k)) (map bplustree.vals xs2) ps *
  leafs_assn ps lptrs2 p z *
  \<up>(concat (map bplustree.vals xs2) = abs_split_range.leaf_nodes_lrange\<^sub>i t x) *
  \<up>(lptrs = lptrs1@lptrs2) *
  \<up>(leaf_nodes t = xs1@xs2)
)>\<^sub>t"
sorry
*)

lemma leaf_nodes_assn_split2:
"length xs = length xsi \<Longrightarrow>
  leaf_nodes_assn k (xs @ ys) r z (xsi @ ysi) = (\<exists>\<^sub>Al. leaf_nodes_assn k xs r l xsi * leaf_nodes_assn k ys l z ysi)"
proof(induction arbitrary: r rule: list_induct2)
  case (Nil r)
  then show ?case
    apply(cases r; cases ys)
    apply clarsimp_all
      subgoal
        apply(rule ent_iffI)
        by (sep_auto dest!: leaf_nodes_assn_impl_length)+
      subgoal
        apply(rule ent_iffI)
        by (sep_auto dest!: leaf_nodes_assn_impl_length)+
      subgoal
        apply(rule ent_iffI)
        by (sep_auto dest!: leaf_nodes_assn_impl_length)+
    subgoal for _ t _
      apply(cases t)
      subgoal
      apply clarsimp_all
          apply(rule ent_iffI)
          by (sep_auto dest!: leaf_nodes_assn_impl_length)+
        subgoal by clarsimp
        done
    done
next
  case (Cons x xs xi xsi r)
  show ?case
    apply(cases r; cases x)
    apply clarsimp_all
        apply(rule ent_iffI)
    subgoal for _ ts
      apply(subst Cons.IH)
      apply simp
      apply(rule ent_ex_preI)+
      subgoal for tsi fwd l
        apply(inst_ex_assn l tsi fwd)
        apply sep_auto
        done
      done
    subgoal for _ ts
      apply(subst Cons.IH)
      apply(simp)
      apply(rule ent_ex_preI)+
      subgoal for l tsi fwd
        apply(inst_ex_assn tsi fwd l)
        apply sep_auto
      done
    done
  done
qed

lemma eq_preI: "(\<forall>h. h \<Turnstile> P \<longrightarrow> Q = Q') \<Longrightarrow> P * Q = P * Q'"
  apply(intro ent_iffI)
  using entails_def mod_starD apply blast+
  done

lemma simp_map_temp: "(map (leaf_nodes \<circ> fst)) = map (\<lambda>a. (leaf_nodes (fst a)))"
  by (meson comp_apply)


declare last.simps[simp del] butlast.simps[simp del]
lemma blist_leafs_assn_split_help:
"   length tsi' = length rrs \<Longrightarrow>
    length rrs = length spl \<Longrightarrow>
    length spl = length ts \<Longrightarrow>
    (blist_leafs_assn k ts
      (zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl))) (separators tsi'))
      =
     list_assn ((\<lambda>t (ti, r', x, y). trunk_assn k t (the ti) r' x y) \<times>\<^sub>a id_assn) ts
      (zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl))) (separators tsi')) *
     leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) ts)) r (last (r#rrs)) (concat spl)
) "
proof(induction tsi' rrs spl ts arbitrary: r rule: list_induct4)
  case Nil
  then show ?case
    by (sep_auto simp add: last.simps butlast.simps)
next
  case (Cons x xs y ys z zs w ws r)
  show ?case
    using Cons.hyps Cons.prems
    apply(clarsimp simp add: butlast_double_Cons last_double_Cons)
    apply(clarsimp simp add: prod_assn_def split!: prod.splits)
        apply(simp add: bplustree_leaf_nodes_sep)
    apply(subst Cons.IH[of y])
    subgoal for sub sep
      apply(intro ent_iffI)
      subgoal
      apply(rule entails_preI)
    apply(subst leaf_nodes_assn_split2)
        subgoal by (auto dest!: mod_starD leaf_nodes_assn_impl_length)
        apply (simp add: simp_map_temp)
        apply(inst_ex_assn y)
        apply(sep_auto)
        done
      subgoal
      apply(rule entails_preI)
        apply(cases ws)
      proof(goal_cases)
        case 1
        then show ?thesis
          by (sep_auto simp add: last.simps)
      next
        case (2 _ a list)
        then show ?thesis
          apply(cases xs, simp)
          apply(cases ys, simp)
          apply(cases zs, simp)
          subgoal for x' xs' y'' ys'' z' zs'
          apply(clarsimp simp add: butlast_double_Cons last_double_Cons)
          apply(clarsimp simp add: prod_assn_def split!: prod.splits)
            subgoal for sub' sep'
            apply(subgoal_tac "y = Some (hd z')")
            prefer 2
            subgoal by (auto dest!: mod_starD trunk_assn_hd)
          apply sep_auto
    apply(subst leaf_nodes_assn_split[where yi="the y" and ysr="tl z'@concat zs'"])
        find_theorems trunk_assn length
        subgoal by (auto dest!: mod_starD trunk_assn_leafs_len_imp)
        apply(subgoal_tac "z' \<noteq> []")
        prefer 2
          subgoal by (auto dest!: mod_starD trunk_assn_leafs_len_imp simp add: leaf_nodes_not_empty)
          subgoal by simp
        apply (simp add: simp_map_temp)
        apply(sep_auto)
        done
      done
    done
    qed
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]

lemma blist_leafs_assn_split:
"   length tsi' = length rrs \<Longrightarrow>
    length rrs = length spl \<Longrightarrow>
    (blist_leafs_assn k ts
      (zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl))) (separators tsi'))
      =
     list_assn ((\<lambda>t (ti, r', x, y). trunk_assn k t (the ti) r' x y) \<times>\<^sub>a id_assn) ts
      (zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl))) (separators tsi')) *
     leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) ts)) r (last (r#rrs)) (concat spl)
) "
proof((intro ent_iffI; rule entails_preI), goal_cases)
  case 1
  then have "length spl = length ts" 
    by (auto dest!: list_assn_len)
  then show ?case 
    using blist_leafs_assn_split_help[OF 1(1,2)]
    by auto
next
  case 2
  then have "length spl = length ts" 
    by (auto dest!: mod_starD list_assn_len)
  then show ?case
    using blist_leafs_assn_split_help[OF 2(1,2)]
    by auto
qed

lemma split_list: "i < length ts \<Longrightarrow> ts ! i = x \<Longrightarrow> \<exists>ls rs. ts = ls@x#rs \<and> length ls = i"
  by (metis id_take_nth_drop length_take min_simps(2))

lemma take_butlast_Suc: "i < length xs \<Longrightarrow> take i (butlast xs) = butlast (take (Suc i) xs)"
  by (metis Suc_leI Suc_to_right take_butlast take_minus_one_conv_butlast)

lemma inbetween_aligned_imp_Laligned: "inbetween aligned l (ls@(sub,sep)#rs) t u \<Longrightarrow> Laligned sub sep"
  by (induction ls arbitrary: l) (auto simp add: aligned_imp_Laligned)

lemma Laligned_sub: "Laligned (Node (ls@(sub,sep)#rs) t) u \<Longrightarrow> Laligned sub sep"
  by (cases ls) (auto simp add: inbetween_aligned_imp_Laligned split!: prod.splits) 

(* much shorter when expressed on the nodes themselves *)
declare last.simps[simp del] butlast.simps[simp del]
lemma leaf_nodes_lrange\<^sub>i_rule:
  assumes "k > 0" "root_order k t" "Laligned t u"
  shows "<bplustree_assn_leafs k t ti r z lptrs >
leaf_nodes_lrange\<^sub>i ti x
<\<lambda>p. (\<exists>\<^sub>A lptrs xs1 lptrs1 lptrs2.
  trunk_assn k t ti r z lptrs *
  leaf_nodes_assn k xs1 r p lptrs1 *
  leaf_nodes_assn k (abs_split_range.leaf_nodes_lrange t x) p z lptrs2 *
  \<up>(lptrs = lptrs1@lptrs2) *
  \<up>(leaf_nodes t = xs1@(abs_split_range.leaf_nodes_lrange t x))
)
>\<^sub>t"
  using assms
proof(induction t x arbitrary: ti r z u lptrs rule: abs_split_range.leaf_nodes_lrange.induct)
  case (1 ks x)
  then show ?case
    apply(subst leaf_nodes_lrange\<^sub>i.simps)
    apply (sep_auto eintros del: exI)
    apply(inst_existentials "[ti]" "[]::'a bplustree list" "[]::'a btnode ref list" "[ti]")
    apply sep_auto+
    done
next
  case (2 ts t x ti r z u lptrs)
  then have "sorted_less (separators ts)"
    by (meson Laligned_sorted_separators sorted_wrt_append)
  obtain ls rs where split_pair: "split ts x = (ls,rs)"
    by (meson surj_pair)
  show ?case
  proof(cases rs)
    case Nil
    then show ?thesis
      using split_pair
    apply(subst leaf_nodes_lrange\<^sub>i.simps)
    apply simp
    apply(vcg)
    apply simp
    subgoal for tsi tii tsi' rrs spl
      apply(cases tsi)
      subgoal for tsia tsin
    supply R = split\<^sub>i_leafs_rule[of ts tsi' rrs "butlast spl" "(zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs (butlast spl))))
        (separators tsi'))" r z]
      thm R
    apply (vcg heap add: R)
      subgoal using \<open>sorted_less (separators ts)\<close> by linarith
      subgoal by simp
      subgoal by simp
      subgoal by (simp add: butlast.simps)
      apply simp
      apply(rule norm_pre_ex_rule)
      apply(rule hoare_triple_preI)
      apply(vcg)
(* discard wrong path *)
      subgoal by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
(* correct path *)
      subgoal for _ spl
      supply R = "2.IH"(1)[OF split_pair[symmetric] Nil, of u]
      thm R
      apply(vcg heap add: R)
      subgoal using "2.prems" by simp
      subgoal 
      using "2.prems"(2) assms(1) order_impl_root_order root_order.simps(2) by blast
      subgoal 
      using "2.prems"(3) Lalign_Llast by blast
    apply (sep_auto eintros del: exI)
    subgoal for y lptrs xs1 lptrs1 lptrs2
      apply(inst_existentials "concat (spl@[lptrs])" "concat (map (leaf_nodes \<circ> fst) ts) @ xs1" "(concat spl) @ lptrs1" lptrs2
            tsia tsin tii tsi' "(zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl)))
            (separators tsi'))" rrs "spl@[lptrs]")
      (*apply(inst_existentials "concat (spl@[lptrs])" "concat (map (leaf_nodes \<circ> fst) ts) @ xs1" "(concat (butlast spl)) @ lptrs1" lptrs2
                              tsia tsin tii tsi' "(zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs (butlast spl))))
            (separators tsi'))" rrs spl)*)
      subgoal
        by (auto)
      subgoal
        apply sep_auto
        apply(subst blist_leafs_assn_split)
        subgoal by simp
        subgoal 
          by (auto dest!: mod_starD list_assn_len)
        apply(rule entails_preI)
        apply(subst leaf_nodes_assn_split2)
        subgoal 
          by (auto dest!: mod_starD leaf_nodes_assn_impl_length)
        apply (sep_auto eintros del: exI)
        apply(inst_existentials "(last (r # rrs))")
        apply (sep_auto)
        done
      done
  done
    done
  done
  done
  next
    case (Cons subsep rrs)
    then obtain sub sep where subsep_split[simp]:"subsep = (sub,sep)"
      by (cases subsep)
    then show ?thesis
    apply(subst leaf_nodes_lrange\<^sub>i.simps)
    using split_pair Cons apply (simp split!: list.splits prod.splits)
    apply(vcg)
    apply simp
    subgoal for tsi tii tsi' rs' spl_first
      apply(cases tsi)
      subgoal for tsia tsin
    supply R = split\<^sub>i_leafs_rule[of ts tsi' rs' "butlast spl_first" "(zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' (butlast spl_first))))
        (separators tsi'))" r z]
      thm R
    apply (vcg heap add: R)
      subgoal using \<open>sorted_less (separators ts)\<close> by linarith
      subgoal by simp
      subgoal by simp
      subgoal by (simp add: butlast.simps)
      thm split_relation_alt
      apply simp
      apply(rule norm_pre_ex_rule)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
      apply(rule norm_pre_ex_rule)+
      apply(rule hoare_triple_preI)
      subgoal for spl lsi subsepi rsi
        apply(cases subsepi)
        subgoal for zz sepi
          apply(cases zz)
          subgoal for subi subp subfwd sublptrs
      apply(vcg)
(* correct path *)
      subgoal for _ _ suba sepa 
      apply(subgoal_tac "lsi = take (length ls) (zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
     (separators tsi'))")
      prefer 2
    subgoal proof (goal_cases)
      case 1
      have *: "length lsi = length ls"
        using 1 by (auto dest!: mod_starD list_assn_len)
      then have "take (length ls) (zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl))) (separators tsi')) = 
                  take (length ls) (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi)"
        using 1 by auto
      also have "\<dots> = lsi"
        using * by auto
      finally show ?case .. 
    qed
      apply(subgoal_tac "rsi = drop (length ls+1) (zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
     (separators tsi'))")
      prefer 2
    subgoal proof (goal_cases)
      case 1
      have *: "length lsi = length ls"
        using 1 by (auto dest!: mod_starD list_assn_len)
      then have "drop (length ls+1) (zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl))) (separators tsi')) = 
                  drop (length ls+1) (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi)"
        using 1 by auto
      also have "\<dots> = rsi"
        using * by auto
      finally show ?case .. 
    qed
      apply(subgoal_tac "subtrees tsi' = (take (length ls) (subtrees tsi'))@subi#(drop (length ls+1) (subtrees tsi'))")
    prefer 2
      subgoal proof (goal_cases)
        case 1
        have "length spl = length tsi'" "length tsi' = length rs'"
          using 1 by auto
        then have "subtrees tsi' = map fst (map fst ((zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
       (separators tsi'))))"
          by simp
        also have "\<dots> = map fst (map fst (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi))"
          using 1 by simp
        also have "\<dots> = map fst (map fst (lsi)) @ subi # map fst (map fst (rsi))"
          by auto
        also have "\<dots> = (take (length ls) (subtrees tsi')) @ subi # (drop (length ls +1) (subtrees tsi'))"
          using 1 by (auto simp add: take_map[symmetric] drop_map[symmetric])
        finally show ?case .
      qed
      apply(subgoal_tac "separators tsi' = (take (length ls) (separators tsi'))@sepi#(drop (length ls+1) (separators tsi'))")
    prefer 2
      subgoal proof (goal_cases)
        case 1
        have "length spl = length tsi'" "length tsi' = length rs'"
          using 1 by auto
        then have "separators tsi' = map snd ((zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
       (separators tsi')))"
          by simp
        also have "\<dots> = map snd (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi)"
          using 1 by simp
        also have "\<dots> = map snd (lsi) @ sepi # map snd (rsi)"
          by auto
        also have "\<dots> = (take (length ls) (separators tsi')) @ sepi # (drop (length ls +1) (separators tsi'))"
          using 1 by (auto simp add: take_map[symmetric] drop_map[symmetric])
        finally show ?case .
      qed
      apply(subgoal_tac "spl = (take (length ls) spl)@sublptrs#(drop (length ls+1) spl)")
        prefer 2
      subgoal proof (goal_cases)
        case 1
        have "length spl = length tsi'" "length tsi' = length rs'"
          using 1 by auto
        then have "spl = map snd (map snd (map snd (map fst ((zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
       (separators tsi'))))))"
          by simp
        also have "\<dots> = map snd (map snd (map snd (map fst (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi))))"
          using 1 by simp
        also have "\<dots> = map snd (map snd (map snd (map fst (lsi)))) @ sublptrs # map snd (map snd (map snd (map fst (rsi))))"
          by auto
        also have "\<dots> = (take (length ls) spl) @ sublptrs # (drop (length ls +1) spl)"
          using 1 by (auto simp add: take_map[symmetric] drop_map[symmetric])
        finally show ?case .
      qed
      apply(subgoal_tac "rs' = (take (length ls) rs')@subfwd#(drop (length ls+1) rs')")
        prefer 2
      subgoal proof (goal_cases)
        case 1
        have "length spl = length tsi'" "length tsi' = length rs'"
          using 1 by auto
        then have "rs' = map fst (map snd (map snd (map fst ((zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
       (separators tsi'))))))"
          by simp
        also have "\<dots> = map fst (map snd (map snd (map fst (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi))))"
          using 1 by simp
        also have "\<dots> = map fst (map snd (map snd (map fst (lsi)))) @ subfwd # map fst (map snd (map snd (map fst (rsi))))"
          by auto
        also have "\<dots> = (take (length ls) rs') @ subfwd # (drop (length ls +1) rs')"
          using 1 by (auto simp add: take_map[symmetric] drop_map[symmetric])
        finally show ?case .
      qed
      apply(subgoal_tac "butlast (r#rs') = (take (length ls) (butlast (r#rs')))@subp#(drop (length ls+1) (butlast (r#rs')))")
        prefer 2
      subgoal proof (goal_cases)
        case 1
        have "length spl = length tsi'" "length tsi' = length rs'"
          using 1 by auto
        then have "butlast (r#rs') = (map fst (map snd (map fst ((zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
       (separators tsi'))))))"
          by simp
        also have "\<dots> = map fst (map snd (map fst (lsi @ ((subi, subp, subfwd, sublptrs), sepi) # rsi)))"
          using 1 by simp
        also have "\<dots> = map fst (map snd (map fst (lsi))) @ subp # map fst (map snd (map fst (rsi)))"
          by auto
        also have "\<dots> = (take (length ls) (butlast (r#rs'))) @ subp # (drop (length ls +1) (butlast (r#rs')))"
          using 1 by (auto simp add: take_map[symmetric] drop_map[symmetric])
        finally show ?case .
      qed
          apply(subgoal_tac "subsepi = ((suba, subp, subfwd, sublptrs), sepa)", simp)
        prefer 2
    subgoal proof (goal_cases)
      case assms: 1
      have "subi = suba" "sepi = sepa"
      proof(goal_cases)
        case 1
        have "subtrees tsi' ! (length ls) = subi"
          by (metis append_take_drop_id assms(20) nth_via_drop same_append_eq)
        moreover have "subtrees tsi' ! (length ls) = suba"
          using assms by simp
        ultimately show ?case by simp
      next
        case 2
        have "separators tsi' ! (length ls) = sepi"
          by (metis append_take_drop_id assms(21) nth_via_drop same_append_eq)
        moreover have "separators tsi' ! (length ls) = sepa"
          using assms by simp
        ultimately show ?case by simp
      qed
      then show ?case
        using assms by auto
    qed
      supply R = "2.IH"(2)[OF split_pair[symmetric] Cons subsep_split[symmetric], of sep]
      thm R
      apply(vcg heap add: R)
      subgoal using "2.prems" by simp
      subgoal 
        using "2.prems"(2) assms(1)  root_order.simps(2)
        by (auto dest!: order_impl_root_order[of k sub, OF assms(1)])
      subgoal 
        using "2.prems"(3) split_pair Cons subsep_split Laligned_sub[of ls sub sep rrs]
        by simp
    apply (sep_auto eintros del: exI)
    subgoal for y lptrs xs1 lptrs1 lptrs2
      thm blist_leafs_assn_split
        apply(inst_existentials "concat ((take (length ls) spl)@lptrs#(drop (Suc (length ls)) spl)@[last spl_first])" "concat (map (leaf_nodes \<circ> fst) ls) @ xs1"
"concat (take (length ls) spl) @ lptrs1" "lptrs2 @ (concat (drop (Suc (length ls)) spl))@last spl_first"
tsia tsin tii tsi' "zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' (butlast ((take (length ls) spl)@lptrs#(drop (Suc (length ls)) spl)@[last spl_first])))))
         (separators tsi')" rs' "(take (length ls) spl)@lptrs#(drop (Suc (length ls)) spl)@[last spl_first]" "(take (length ls)
            (zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' spl)))
              (separators tsi')))" subi subp subfwd lptrs sepi "(drop (Suc (length ls))
            (zip (zip (subtrees tsi') (zip (butlast (r # rs')) (zip rs' ((take (length ls) spl)@lptrs#(drop (length ls+1) spl)))))
              (separators tsi')))")
      (*apply(inst_existentials "concat (spl@[lptrs])" "concat (map (leaf_nodes \<circ> fst) ts) @ xs1" "(concat (butlast spl)) @ lptrs1" lptrs2
                              tsia tsin tii tsi' "(zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs (butlast spl))))
            (separators tsi'))" rrs spl)*)
      subgoal
        find_theorems "butlast" "_@[_]"
        apply (auto)
      proof (goal_cases)
        case (1 a b)
        have *: "(take (length ls) spl @ (lptrs1 @ lptrs2) # drop (Suc (length ls)) spl @ [last spl_first])
 = ((take (length ls) spl @ (lptrs1 @ lptrs2) # drop (Suc (length ls)) spl) @ [last spl_first])"
          by auto
        have **: 
           "subtrees tsi' = take (length ls) (subtrees tsi') @ subi # drop (Suc (length ls)) (subtrees tsi')"
           "separators tsi' = take (length ls) (separators tsi') @ sepi # drop (Suc (length ls)) (separators tsi')"
           "spl = take (length ls) spl @ sublptrs # drop (Suc (length ls)) spl"
           "rs' = take (length ls) rs' @ subfwd # drop (Suc (length ls)) rs'"
           "butlast (r # rs') =
           take (length ls) (butlast (r # rs')) @
           subp # drop (Suc (length ls)) (butlast (r # rs'))"
          using 1 by simp_all
        have drop_sep_tsi': "drop (length ls) (separators tsi') = sepi#(drop (length ls+1) (separators tsi'))" 
        proof -
          have "take (length ls) (separators tsi') @ drop (length ls) (separators tsi') = take (length ls) (separators tsi')@sepi#(drop (length ls+1) (separators tsi'))" 
            using 1 by auto
          then show ?thesis
            by (meson same_append_eq)
        qed
        have drop_sub_tsi': "drop (length ls) (subtrees tsi') = subi#(drop (length ls+1) (subtrees tsi'))" 
        proof -
          have "take (length ls) (subtrees tsi') @ drop (length ls) (subtrees tsi') = take (length ls) (subtrees tsi')@subi#(drop (length ls+1) (subtrees tsi'))" 
            using 1 by auto
          then show ?thesis
            by (meson same_append_eq)
        qed
        have drop_rs': "drop (length ls) rs' = subfwd#(drop (length ls+1) rs')" 
        proof -
          have "take (length ls) rs' @ drop (length ls) rs' = take (length ls) rs'@subfwd#(drop (length ls+1) rs')" 
            using 1 by auto
          then show ?thesis
            by (meson same_append_eq)
        qed
        have drop_butlastrs': "drop (length ls) (butlast (r#rs')) = subp#(drop (length ls+1) (butlast (r#rs')))" 
        proof -
          have "take (length ls) (butlast (r#rs')) @ drop (length ls) (butlast (r#rs')) = take (length ls) (butlast (r#rs'))@subp#(drop (length ls+1) (butlast (r#rs')))" 
            using 1 by auto
          then show ?thesis
            by (meson same_append_eq)
        qed
        have "length tsi' = length rs'" "length spl = length rs'" "length ls \<le> length rs'" 
          using 1 by auto
        then show ?case 
          apply(subst *)
          apply(subst butlast_snoc)
          find_theorems "zip" "_@_"
          apply(subst(2) zip_append2)
          apply(subst(2) zip_append2)
          apply(subst(2) zip_append2)
          apply(subst zip_append1)
          find_theorems min "_ \<le> _"
          apply (simp add: min.absorb2)
          find_theorems "zip" "_#_"
          find_theorems zip take
          apply(simp add: take_zip)
          apply(subst drop_sep_tsi')
          apply(subst drop_sub_tsi')
          apply(subst drop_rs')
          apply(subst drop_butlastrs')
          apply(simp add: drop_zip min.absorb2)
          done
      qed
      subgoal
        find_theorems butlast take
        apply(simp add: take_zip drop_zip)
        apply(simp add: take_butlast_Suc)
        apply(subgoal_tac "drop (Suc (length ls)) (butlast (r # rs')) = butlast (subfwd#(drop (Suc (length ls)) rs'))") 
        apply (simp add: take_map drop_map)
        thm blist_leafs_assn_split
         supply R = blist_leafs_assn_split[of
                  "take (length ls) tsi'"
                  "take (length ls) rs'"
                  "take (length ls) spl"
                  k ls
                  ]
        thm R
        find_theorems map take
        apply(subst blist_leafs_assn_split)
        subgoal by simp
        subgoal 
          by (auto dest!: mod_starD list_assn_len)
        apply(subst blist_leafs_assn_split)
        subgoal by simp
        subgoal 
          by (auto dest!: mod_starD list_assn_len)
        apply(clarsimp)
        apply(rule entails_preI)
        apply(subst leaf_nodes_assn_split2)
        subgoal 
          by (auto dest!: mod_starD leaf_nodes_assn_impl_length)
        apply(subst leaf_nodes_assn_split2)
        subgoal 
          by (auto dest!: mod_starD leaf_nodes_assn_impl_length)
        apply(subst leaf_nodes_assn_split2)
        subgoal 
          by (auto dest!: mod_starD leaf_nodes_assn_impl_length)
        apply(subst bplustree_leaf_nodes_sep)+
        apply (sep_auto eintros del: exI)
        apply(inst_existentials subfwd "(last (subfwd # drop (Suc (length ls)) rs'))" "(last (r # take (length ls) rs'))")
        apply(subgoal_tac "last (subfwd # drop (Suc (length ls)) rs') = last (r#rs')")
        apply(subgoal_tac "(last (r # take (length ls) rs')) = subp")
        apply(simp add: last.simps)
        apply (solve_entails)
      proof(goal_cases)
        case (1 a b)
        then have *: "length ls < length rs'"
          by simp
        have "butlast (r # rs') =
    butlast (r # take (length ls) rs') @ subp # butlast (subfwd # drop (Suc (length ls)) rs')"
          using 1 by simp
        then have "take (length ls + 1) (butlast (r #rs')) = butlast (r # take (length ls) rs') @ [subp]"
          using * by simp
        then have "butlast (r # rs') ! (length ls) = subp"
          using * take_Suc_conv_app_nth[of "length ls" "butlast (r#rs')"]
          by simp
        then have obt:"(r # rs') ! (length ls) = subp"
          using nth_butlast[of "length ls" "r#rs'"] * by auto
        have **: "r#(take (length ls) rs') = take (length ls +1) (r#rs')"
          by simp
        show ?case
          apply (subst **)
          apply(subst last_take_nth_conv)
          using obt * by auto
      next
        case (2 a b)
        then have "rs' = take (length ls) rs' @ subfwd # drop (Suc (length ls)) rs'"
          by simp
        then have "r#rs' = (r#take (length ls) rs') @ subfwd # drop (Suc (length ls)) rs'"
          by simp
        then have "last(r#rs') = last((r#take (length ls) rs') @ subfwd # drop (Suc (length ls)) rs')"
          by simp
        also have "\<dots> = last(subfwd # drop (Suc (length ls)) rs')"
          thm last_append[of "r#take (length ls) rs'"]
          using last_append[of "r#take (length ls) rs'"]
          by simp
        finally show ?case ..
      next
        case 3
        have "drop (Suc (length ls)) (butlast (r # rs')) = butlast (drop (Suc (length ls)) (r#rs'))"
          by (auto simp add: butlast.simps butlast_drop)
        also have "\<dots> = butlast (drop (length ls) rs')"
          by simp
        also have "\<dots> = butlast (subfwd # drop (Suc (length ls)) rs')"
        proof -
            have *:"rs' = take (length ls) rs' @ subfwd # drop (Suc (length ls)) rs'"
              using 3 by simp
            have "length ls < length rs'"
              using 3 by simp
            then have "drop (length ls) rs' = subfwd # drop (Suc (length ls)) rs'"
              apply(subst *)
              by (simp add: min.absorb1 min.absorb2)
            then show ?thesis by simp
          qed
          finally show ?case .
      qed
        done
      done
  subgoal
    apply(rule hoare_triple_preI)
    subgoal by (auto simp add: split_relation_alt dest!:  mod_starD list_assn_len arg_cong[of _ _ length])[]
  done
  done
  done
  done
  done
  done
  done
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]

(*fun concat_leaf_nodes_lrange\<^sub>i where
  "concat_leaf_nodes_lrange\<^sub>i t x = (case leaf_nodes_lrange\<^sub>i t x of (Leaf ks)#list \<Rightarrow> lrange_list x ks @ (concat (map leaves list)))"
*)

definition concat_leaf_nodes_lrange\<^sub>i where
"concat_leaf_nodes_lrange\<^sub>i ti x = do {
  lp \<leftarrow> leaf_nodes_lrange\<^sub>i ti x;
  li \<leftarrow> !(the lp);
  case li of Btleaf xs nxt \<Rightarrow> do {
    arr_it \<leftarrow> lrange_list\<^sub>i x xs;
    fla_it \<leftarrow> leaf_values_adjust (nxt,None) arr_it;
    return fla_it
  }
}"

lemma sorted_less_leaf_nodes: "sorted_less (leaves t) \<Longrightarrow> (Leaf ks) \<in> set (leaf_nodes t) \<Longrightarrow> sorted_less ks"
proof(induction t arbitrary: ks rule: leaf_nodes.induct)
  case (1 xs)
  then show ?case by simp
next
  case I: (2 ts t)
  then have "(\<exists>x \<in> set ts. Leaf ks \<in> set (leaf_nodes (fst x))) \<or> Leaf ks \<in> set (leaf_nodes t)"
    by simp
  then show ?case 
  proof(standard, goal_cases)
    case 1
    then show ?case
      using I
      by (metis (no_types, lifting) in_set_conv_decomp list.simps(9) map_append sorted_leaves_subtrees)
  next
    case 2
    then show ?case
      using I
      by (meson sorted_leaves_induct_last)
  qed
qed

lemmas leaf_values_adjust_rule = leaf_values_iter.flatten_it_adjust_rule

lemma concat_leaf_nodes_lrange\<^sub>i_rule_help:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t u"
  shows "<bplustree_assn_leafs k t ti r None lptrs>
concat_leaf_nodes_lrange\<^sub>i ti x
<bplustree_iter k t ti r (abs_split_range.lrange t x)>\<^sub>t"
  apply(subst concat_leaf_nodes_lrange\<^sub>i_def)
  apply(vcg (ss) heap: leaf_nodes_lrange\<^sub>i_rule[of k t u])+
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  apply simp
  apply(rule norm_pre_ex_rule)+
  apply(rule hoare_triple_preI)
  apply(auto dest!: mod_starD)
proof(goal_cases)
  case (1 l xs1 lptrs1 lptrs2)
  obtain ks list where *[simp]: "abs_split_range.leaf_nodes_lrange t x = (Leaf ks)#list \<and> (Leaf ks) \<in> set (leaf_nodes t)"
    using abs_split_range.leaf_nodes_lrange_not_empty by blast
  then obtain r' lptrs2' where [simp]: "lptrs2 = r' # lptrs2'"
    using 1
    by (metis Suc_length_conv leaf_nodes_assn_impl_length)
  have sorted_less_ks: "sorted_less ks"
    using \<open>abs_split_range.leaf_nodes_lrange t x = Leaf ks # list \<and> Leaf ks \<in> set (leaf_nodes t)\<close> assms(3) sorted_less_leaf_nodes split\<^sub>i_range_axioms by blast
  then obtain pref where ks_split: "ks = pref @ lrange_list x ks"
  proof (goal_cases)
    case 1
    have "suffix (lrange_list x ks) ks"
      by (metis \<open>sorted_less ks\<close> abs_split_range.lrange_list_req lrange_suffix sorted_less_lrange)
    then have "\<exists>pref. ks = pref @ lrange_list x ks"
      by (meson suffixE)
    then show ?case
      using 1
      by blast
  qed
  show ?case
  proof(cases l)
    case None
    show ?thesis
      apply(rule hoare_triple_preI)
      using None by simp
  next
  case (Some a)
    then show ?thesis
      apply simp
      apply(rule norm_pre_ex_rule)+
      apply vcg
      apply simp
      subgoal for xsi fwd
        apply(cases xsi)
        apply simp
      thm lrange_list_rule
      using sorted_less_ks apply (vcg  heap: lrange_list_rule)
      apply(subst leaf_nodes_assn_flatten)+
      apply(simp)
      apply(rule norm_pre_ex_rule)+
      subgoal for ksia ksin it ps2 ps1
      supply R = fi_rule[
            OF leaf_values_adjust_rule,
            where F="list_assn leaf_node (leaf_nodes t) (leaf_lists t) *
                     trunk_assn k t ti r None (lptrs1 @ r' # lptrs2') *
                     true"]
        thm R
        supply R' = R[of _ k "map leaves xs1" ps1 "map leaves list" ps2 "(ksia,ksin)"
                         "lptrs1@r'#lptrs2'" r "(fwd,None)" pref "lrange_list x ks" it]
      thm R'
      apply(vcg heap: R')
      apply(subst leaf_iter_assn_def)
      apply simp
      subgoal
        apply(inst_ex_assn "ps1@[(ksia,ksin)]" "lptrs1@[r']" lptrs2')
        apply sep_auto
          subgoal
            apply(rule entails_preI)
            apply(subst leafs_assn_aux_append)
            subgoal by (auto dest!: mod_starD leafs_assn_impl_length)
            subgoal
              apply simp
              apply(inst_ex_assn "Some r'")
              subgoal using 1(1) ks_split by sep_auto
              done
        done
      done
      subgoal
        apply (sep_auto eintros del: exI simp add: bplustree_iter_def)
        apply(inst_existentials "lptrs1@lptrs2")
        apply(subgoal_tac "leaves t = (concat (map leaves xs1) @ pref @ lrange_list x ks @ concat (map leaves list))")
        apply(subgoal_tac "abs_split_range.lrange t x = (lrange_list x ks @ concat (map leaves list))")
        subgoal using 1(1) 1(2) ks_split by sep_auto
        subgoal by (metis \<open>abs_split_range.leaf_nodes_lrange t x = Leaf ks # list \<and> Leaf ks \<in> set (leaf_nodes t)\<close> abs_split_range.split_range_axioms split_range.leaf_nodes_lrange_pre_lrange)
        subgoal
          using concat_leaf_nodes_leaves[symmetric, of t] 1(1) ks_split
          by auto
        done
      done
    done
  done
  qed
qed

lemma concat_leaf_nodes_lrange\<^sub>i_rule:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t u"
  shows "<bplustree_assn k t ti r None>
concat_leaf_nodes_lrange\<^sub>i ti x
<bplustree_iter k t ti r (abs_split_range.lrange t x)>\<^sub>t"
  find_theorems bplustree_assn_leafs
  apply(simp add: bplustree_extract_leafs)
  using assms apply(sep_auto heap add: concat_leaf_nodes_lrange\<^sub>i_rule_help)
  done

end

context split\<^sub>i_list
begin

definition lrange_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfa_it Heap"
  where "lrange_list\<^sub>i x ks = do {
    i \<leftarrow> split\<^sub>i_list ks x;
    return (ks, i)
}"

lemma lrange_list\<^sub>i_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows
   "<is_pfa c ks (a',n')> 
    lrange_list\<^sub>i x (a',n') 
  <pfa_is_it c ks (a',n') (abs_split_list.lrange_split x ks)>\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then have "lrange_list x ks = rs"
    by (simp add: abs_split_list.lrange_filter_split assms)
  moreover have "ks = ls@rs"
    using abs_split_list.split_list_req(1) list_split by blast
  ultimately show ?thesis
      apply(subst lrange_list\<^sub>i_def)
      using assms list_split abs_split_list.lrange_split_req
      apply(sep_auto simp add: sorted_less_lrange pfa_is_it_def split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)
      done
qed
end

context split\<^sub>i_full
begin

sublocale split\<^sub>i_range split  split\<^sub>i_list.abs_split_list.lrange_split split\<^sub>i split\<^sub>i_list.lrange_list\<^sub>i
  using split\<^sub>i_list.abs_split_list.lrange_split_req split\<^sub>i_list.lrange_list\<^sub>i_rule
  apply unfold_locales 
  apply sep_auto +
  done

end



end