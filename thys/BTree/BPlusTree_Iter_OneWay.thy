theory BPlusTree_Iter_OneWay
  imports
    BPlusTree_Imp
    "HOL-Real_Asymp.Inst_Existentials"
    "Separation_Logic_Imperative_HOL.Imp_List_Spec"
    Flatten_Iter
    Partially_Filled_Array_Iter
begin


fun leaf_nodes_assn :: "nat \<Rightarrow> ('a::heap) bplustree list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "leaf_nodes_assn k ((Leaf xs)#lns) (Some r) z = 
 (\<exists>\<^sub>A xsi fwd.
      r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xs xsi
    * leaf_nodes_assn k lns fwd z
  )" | 
  "leaf_nodes_assn k [] r z = \<up>(r = z)" |
  "leaf_nodes_assn _ _ _ _ = false"


fun inner_nodes_assn :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "inner_nodes_assn k (Leaf xs) a r z = \<up>(r = Some a)" |
  "inner_nodes_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * inner_nodes_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). inner_nodes_assn k t (the ti) r' z') \<times>\<^sub>a id_assn) ts tsi''
    )"


lemma leaf_nodes_assn_aux_append:
   "leaf_nodes_assn k (xs@ys) r z = (\<exists>\<^sub>Al. leaf_nodes_assn k xs r l * leaf_nodes_assn k ys l z)"
  apply(induction k xs r z rule: leaf_nodes_assn.induct)
  apply(sep_auto intro!: ent_iffI)+
  done



declare last.simps[simp del] butlast.simps[simp del]
declare mult.left_assoc[simp add]
lemma bplustree_leaf_nodes_help:
  "bplustree_assn k t ti r z \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * inner_nodes_assn k t ti r z"
proof(induction arbitrary: r rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    by (sep_auto)
next
  case (2 k ts t a r z ra)
  show ?case
    apply(auto)
    apply(rule ent_ex_preI)+
  proof (goal_cases)
    case (1 tsi ti tsi' tsi'' rs)
    have *: "
        length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        set tsi's \<subseteq> set tsi' \<Longrightarrow>
        set rss \<subseteq> set rs \<Longrightarrow>
        set tss \<subseteq> set ts \<Longrightarrow>
       bplustree_assn k t ti (last (ra # rss)) z * 
       blist_assn k tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) \<Longrightarrow>\<^sub>A
       leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z * 
      inner_nodes_assn k t ti (last (ra#rss)) z *
       list_assn ((\<lambda> t (ti,r',z'). inner_nodes_assn k t (the ti) r' z') \<times>\<^sub>a id_assn) tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's))
"
      for rss tsi's tss
    proof (induct arbitrary: ra rule: list_induct3)
      case (Nil r)
      then show ?case
        apply sep_auto
        using 2(1)[of ti r "[]"]
      apply (simp add: last.simps butlast.simps)
      done
    next
      case (Cons subsepi tsi's subleaf rss subsep tss r)
      show ?case
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
        apply(subst prod_assn_def)
        apply(simp split!: prod.splits add: mult.left_assoc)
        apply(subst leaf_nodes_assn_aux_append)
        apply simp
        apply(inst_ex_assn subleaf)
      proof (goal_cases)
        case (1 sub sep)
        have "(sub,sep) \<in> set ts"
          using "1" Cons.prems(3) by force
        moreover have "set tsi's \<subseteq> set tsi' \<and> set rss \<subseteq> set rs \<and> set tss \<subseteq> set ts"
          by (meson Cons.prems set_subset_Cons subset_trans)
        moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
          by auto
        ultimately  show ?case
          using
           Cons(3)[of subleaf]
           "2.IH"(2)[of "(sub,sep)"
                "((fst subsepi, (temp1, subleaf)),temp2)" "[((fst subsepi, (temp1, subleaf)),temp2)]"
                "fst subsepi" "(temp1, subleaf)" temp1 subleaf r]
          apply auto
          thm mult.commute
          thm star_aci
          apply(subst mult.commute)
          thm mult.commute[where b="inner_nodes_assn k sub (the (fst subsepi)) r subleaf"]
          apply(subst mult.commute[where b="inner_nodes_assn k sub (the (fst subsepi)) r subleaf"])
          find_theorems "_ * _ = _ * _"
          apply(simp)
          thm ent_star_mono
          supply R=ent_star_mono[where
P="bplustree_assn k sub (the (fst subsepi)) r subleaf" and P'="inner_nodes_assn k sub (the (fst subsepi)) r subleaf *
 leaf_nodes_assn k (leaf_nodes sub) r subleaf"
and Q="bplustree_assn k t ti (last (subleaf # rss)) z *
    id_assn sep (snd subsepi) *
    blist_assn k tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) rss)) (separators tsi's))"
and Q'="leaf_nodes_assn k (concat (map (\<lambda>a. leaf_nodes (fst a)) tss) @ leaf_nodes t) subleaf
     z *
    inner_nodes_assn k t ti (last (subleaf # rss)) z *
    id_assn sep (snd subsepi) *
    list_assn ((\<lambda>t (ti, x, y). inner_nodes_assn k t (the ti) x y) \<times>\<^sub>a id_assn) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) rss)) (separators tsi's))"
          ,simplified]
          thm R
          apply(rule R)
          subgoal
            apply(subst mult.commute)
            by simp
          subgoal
            thm mult.commute
            apply(subst mult.commute[where b="id_assn _ _"], simp)+
            find_theorems "_ * _ = _* _"
            apply(subst mult.commute)
            supply R = ent_star_mono[where
              P="id_assn sep (snd subsepi)" and P'="id_assn sep (snd subsepi)"
and Q="bplustree_assn k t ti (last (subleaf # rss)) z *
    blist_assn k tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) rss))
       (separators tsi's))" and
Q'="leaf_nodes_assn k (concat (map (\<lambda>a. leaf_nodes (fst a)) tss) @ leaf_nodes t) subleaf
     z *
    inner_nodes_assn k t ti (last (subleaf # rss)) z *
    list_assn ((\<lambda>t (ti, x, y). inner_nodes_assn k t (the ti) x y) \<times>\<^sub>a id_assn) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) rss))
       (separators tsi's))"
, simplified]
            thm R
            apply(rule R)
            apply simp
            done
      done
      qed
    qed
    show ?case
      apply(rule entails_preI)
        using 1 apply (auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        apply(inst_ex_assn tsi ti tsi' tsi'' rs)
        by (smt (z3) assn_aci(10) assn_times_comm fr_refl mult.right_neutral pure_true)
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]
declare mult.left_assoc[simp del]

lemma bplustree_leaf_nodes:
  "bplustree_assn k t ti r z \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * inner_nodes_assn k t ti r z"
  using bplustree_leaf_nodes_help[of k t ti r z] by simp

fun leaf_node:: "('a::heap) bplustree \<Rightarrow> 'a list \<Rightarrow> assn" where
  "leaf_node (Leaf xs) xsi = \<up>(xs = xsi)" |
  "leaf_node _ _ = false"

fun leafs_assn :: "('a::heap) pfarray list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "leafs_assn (ln#lns) (Some r) z = 
 (\<exists>\<^sub>A fwd.
      r \<mapsto>\<^sub>r Btleaf ln fwd
    * leafs_assn lns fwd z
  )" | 
  "leafs_assn [] r z = \<up>(r = z)" |
  "leafs_assn _ _ _ = false"

lemma leafs_assn_aux_append:
   "leafs_assn (xs@ys) r z = (\<exists>\<^sub>Al. leafs_assn xs r l * leafs_assn ys l z)"
  apply(induction xs r z rule: leafs_assn.induct)
  apply(sep_auto intro!: ent_iffI)+
  done

lemma leaf_nodes_assn_split:
  "leaf_nodes_assn k ts r z = (\<exists>\<^sub>Aps. list_assn leaf_node ts (map bplustree.vals ts) * list_assn (is_pfa (2*k)) (map bplustree.vals ts) ps * leafs_assn ps r z)"
proof (induction ts arbitrary: r)
  case Nil
  then show ?case
  apply(intro ent_iffI)
    subgoal by sep_auto
    subgoal by sep_auto
    done
next
  case (Cons a xs)
  then show ?case
  proof(intro ent_iffI, goal_cases)
    case 1
    show ?case
      apply(cases r; cases a)
      apply simp_all
      find_theorems "\<exists>\<^sub>A_._ \<Longrightarrow>\<^sub>A_"
      apply(rule ent_ex_preI)+
      subgoal for aa x1 xsi fwd
      apply (subst "Cons.IH"[of fwd]) 
        apply simp
      apply(rule ent_ex_preI)+
        subgoal for ps
          apply(inst_ex_assn "xsi#ps")
          apply simp_all
          apply(inst_ex_assn fwd)
          apply (sep_auto)
          done
        done
      done
  next
    case 2
    have *: "list_assn leaf_node xs (map bplustree.vals xs) * list_assn (is_pfa (2 * k)) (map bplustree.vals xs) ps' * leafs_assn ps' r' z
          \<Longrightarrow>\<^sub>A leaf_nodes_assn k xs r' z" 
      for ps' r'
      using assn_eq_split(1)[OF sym[OF "Cons.IH"[of r']]]
             ent_ex_inst[where Q="leaf_nodes_assn k xs r' z" and y=ps']
      by blast
    show ?case
      apply(rule ent_ex_preI)+
      subgoal for ps
        apply(cases ps; cases r; cases a)
      apply simp_all
      apply(rule ent_ex_preI)+
        subgoal for aa list aaa x1 fwd
          apply(inst_ex_assn aa fwd)
          apply sep_auto
          using *[of list fwd]
          by (smt (z3) assn_aci(9) assn_times_comm fr_refl)
        done
      done
  qed
qed

lemma inst_same: "(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>\<^sub>A x. P x) = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma inst_same2: "(\<And>x. P = Q x) \<Longrightarrow> P = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma pure_eq_pre: "(P \<Longrightarrow> Q = R) \<Longrightarrow> (Q * \<up>P = R * \<up>P)"
  by fastforce

lemma bplustree_leaf_nodes_sep:
  "leaf_nodes_assn k (leaf_nodes t) r z * (leaf_nodes_assn k (leaf_nodes t) r z -* bplustree_assn k t ti r z) \<Longrightarrow>\<^sub>A bplustree_assn k t ti r z"
  by (simp add: ent_mp)

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_leaf_nodes_sep:
  "bplustree_assn k t ti r z = leaf_nodes_assn k (leaf_nodes t) r z * (leaf_nodes_assn k (leaf_nodes t) r z -* bplustree_assn k t ti r z)"
  oops

(* this doesn't hold, we need to know more about the remaining list,
specifically because inner_nodes_assn doesn't say anything about next pointers *)
lemma leaf_nodes_assn_split_spec: "leaf_nodes_assn k
        (leaf_nodes x @ ys) r z *
       inner_nodes_assn k x a r m =
      leaf_nodes_assn k (leaf_nodes x) r m * leaf_nodes_assn k ys m z *
       inner_nodes_assn k x a r m"
    oops



(* TODO find a statement that cleanly separates the heap *)
declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_leaf_nodes_sep:
  "bplustree_assn k t ti r z = leaf_nodes_assn k (leaf_nodes t) r z * inner_nodes_assn k t ti r z"
  oops
(*
proof(induction arbitrary: r rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    apply(intro ent_iffI)
    apply sep_auto+
    done
next
  case (2 k ts t a r z ra)
  show ?case
      apply simp
    apply(rule inst_same)+
    apply(rule pure_eq_pre)
    proof(goal_cases)
      case (1 tsi ti tsi' tsi'' rs)
      have *: "
          length tsi's = length rss \<Longrightarrow>
          length rss = length tss \<Longrightarrow>
          set tsi's \<subseteq> set tsi' \<Longrightarrow>
          set rss \<subseteq> set rs \<Longrightarrow>
          set tss \<subseteq> set ts \<Longrightarrow>
         bplustree_assn k t ti (last (ra # rss)) z * 
         blist_assn k tss
          (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) =
         leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z *
         list_assn ((\<lambda>t (ti, x, y). inner_nodes_assn k t (the ti) x y) \<times>\<^sub>a id_assn) tss
         (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) *
        inner_nodes_assn k t ti (last (ra#rss)) z"
        for rss tsi's tss
      proof (induct arbitrary: ra rule: list_induct3)
        case (Nil r)
        then show ?case
          apply sep_auto
          using 2(1)[of ti r]
          apply (simp add: last.simps)
          done
      next
        case (Cons subsepi tsi's subleaf rss subsep tss r)
        show ?case 
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
          apply(subst prod_assn_def)
        apply(simp split!: prod.splits add: mult.left_assoc)
        (*apply(subst leaf_nodes_assn_split_spec)*)
        proof(goal_cases)
          case (1 sub sep)
          moreover have p: "set tsi's \<subseteq> set tsi'"
               "set rss \<subseteq> set rs"
               "set tss \<subseteq> set ts"
            using Cons.prems by auto
          moreover have "(sub,sep) \<in> set ts"
            using "1" Cons.prems(3) by force
          moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
            by auto
          ultimately show ?case
            apply(inst_ex_assn subleaf)
            using "Cons.hyps"(3)[of subleaf, OF p]
            apply (auto simp add: algebra_simps)
            using "2.IH"(2)[of subsep "((fst subsepi, (temp1, subleaf)),temp2)" "[((fst subsepi, (temp1, subleaf)),temp2)]"
                "fst subsepi" "(temp1, subleaf)" temp1 subleaf r]
            apply auto
            using assn_times_assoc ent_refl by presburger
        qed
      qed
      show ?case
        apply(intro ent_iffI)
        subgoal
         apply(rule entails_preI)
          using 1
        apply(auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        apply (smt (z3) assn_aci(10) assn_times_comm entails_def)
        done
      subgoal
         apply(rule entails_preI)
        using 1
        apply(auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        apply (smt (z3) assn_aci(10) assn_times_comm entails_def)
        done
      done
    qed
  qed
declare last.simps[simp add] butlast.simps[simp add]
*)

subsection "Iterator"

partial_function (heap) first_leaf :: "('a::heap) btnode ref \<Rightarrow> 'a btnode ref option Heap"
  where
    "first_leaf p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ _ \<Rightarrow> do { return (Some p) } |
    Btnode tsi ti \<Rightarrow> do {
        s \<leftarrow> pfa_get tsi 0;
        let (sub,sep) = s in do { 
          first_leaf (the sub)
        }
  }
)}"

partial_function (heap) last_leaf :: "('a::heap) btnode ref \<Rightarrow> 'a btnode ref option Heap"
  where
    "last_leaf p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ z \<Rightarrow> do { return z } |
    Btnode tsi ti \<Rightarrow> do {
        last_leaf ti
  }
)}"

declare last.simps[simp del] butlast.simps[simp del]
lemma first_leaf_rule[sep_heap_rules]:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  first_leaf ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(u = r)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti z)
  case (Leaf x)
  then show ?case
    apply(subst first_leaf.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  then obtain sub sep tts where Cons: "ts = (sub,sep)#tts"
    apply(cases ts) by auto
  then show ?case 
    apply(subst first_leaf.simps)
    apply (sep_auto simp add: butlast.simps)
    subgoal for tsia tsil ti tsi' rs subi sepi
    apply(cases rs; cases tsi')
    apply simp_all
      subgoal for subleaf rrs _ ttsi'
        supply R = "Node.IH"(1)[of "(sub,sep)" sub "(the subi)" subleaf]
        thm R
    using  "Node.prems"(1)
    apply (sep_auto heap add: R)
    subgoal by (metis Node.prems(2) assms(1) bplustree.inject(2) bplustree.simps(4) Cons list.set_intros(1) order_impl_root_order root_order.elims(2) some_child_sub(1))
    apply (sep_auto eintros del: exI)
    apply(inst_existentials tsia tsil ti "(subi, sepi) # ttsi'" "((subi, (r, subleaf)),sepi)#(zip (zip (subtrees ttsi') (zip (butlast (subleaf # rrs)) rrs)) (separators ttsi'))" "subleaf # rrs")
    apply (sep_auto simp add: last.simps butlast.simps)+
    done
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]

declare last.simps[simp del] butlast.simps[simp del]
lemma last_leaf_rule[sep_heap_rules]:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  last_leaf ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(u = z)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti r)
  case (Leaf x)
  then show ?case
    apply(subst last_leaf.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  show ?case 
    apply(subst last_leaf.simps)
        supply R = "Node.IH"(2)
    apply (sep_auto heap add: R)
    subgoal using "Node.prems" by simp
    subgoal by (metis Node.prems(2) assms(1) bplustree.inject(2) bplustree.simps(4) Cons list.set_intros(1) order_impl_root_order root_order.elims(2) some_child_sub(1))
    apply (sep_auto eintros del: exI)
    subgoal for tsia tsil ti tsi' rs
    apply(inst_existentials tsia tsil ti "tsi'" " (zip (zip (subtrees tsi') (zip (butlast (r # rs)) rs)) (separators tsi'))" rs)
    apply (sep_auto simp add: last.simps butlast.simps)+
    done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]


definition tree_leaf_iter_init where
"tree_leaf_iter_init p = do {
  r \<leftarrow> first_leaf (the p);
  z \<leftarrow> last_leaf (the p);
  return  (r, z)
}"

lemma tree_leaf_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  tree_leaf_iter_init (Some ti)
  <\<lambda>(u,v). leaf_nodes_assn k (leaf_nodes t) u v * inner_nodes_assn k t ti r z * \<up>(u = r \<and> v = z)>\<^sub>t"
  using assms
  using bplustree_leaf_nodes_help[of k t ti r z]
  unfolding tree_leaf_iter_init_def
  apply (sep_auto)
  using ent_star_mono ent_true by blast


definition leaf_iter_next where
"leaf_iter_next = (\<lambda>(r,z). do {
  p \<leftarrow> !(the r);
  return (vals p, (fwd p, z))
})"

lemma leaf_iter_next_rule_help:
  "<leafs_assn (x#xs) r z>
      leaf_iter_next (r,z)
   <\<lambda>(p,(n,z')). leafs_assn [x] r n * leafs_assn xs n z' * \<up>(p = x) * \<up>(z=z')>"
  apply(subst leaf_iter_next_def)
  apply(cases r; cases x)
  apply(sep_auto)+
  done

definition leaf_iter_assn where "leaf_iter_assn xs r xs2 = (\<lambda>(n,z). 
  (\<exists>\<^sub>Axs1. \<up>(xs = xs1@xs2) * leafs_assn xs1 r n * leafs_assn xs2 n z * \<up>(z=None)))" 

lemma leaf_nodes_assn_imp_iter_assn: "leafs_assn xs r None \<Longrightarrow>\<^sub>A leaf_iter_assn xs r xs (r,None)"
  unfolding leaf_iter_assn_def
  by sep_auto

definition leaf_iter_init where
"leaf_iter_init p = do {
  return  (p, None)
}"

lemma leaf_iter_init_rule:
  shows "<leafs_assn xs r None>
  leaf_iter_init r
  <\<lambda>u. leaf_iter_assn xs r xs u>"
  unfolding leaf_iter_init_def
  using leaf_nodes_assn_imp_iter_assn
  by (sep_auto)

lemma leaf_iter_next_rule: "<leaf_iter_assn xs r (x#xs2) it>
leaf_iter_next it
<\<lambda>(p, it'). leaf_iter_assn xs r xs2 it' * \<up>(p = x)>"
  unfolding leaf_iter_assn_def
  apply(cases it)
  by (sep_auto heap add: leaf_iter_next_rule_help simp add: leafs_assn_aux_append)

definition leaf_iter_has_next where
"leaf_iter_has_next  = (\<lambda>(r,z). return (r \<noteq> z))"

(* TODO this so far only works for the whole tree (z = None)
for subintervals, we would need to show that the list of pointers is indeed distinct,
hence r = z can only occur at the end *)
lemma leaf_iter_has_next_rule:
  "<leaf_iter_assn xs r xs2 it> leaf_iter_has_next it <\<lambda>u. leaf_iter_assn xs r xs2 it * \<up>(u \<longleftrightarrow> xs2 \<noteq> [])>"
  unfolding leaf_iter_has_next_def
  apply(cases it)
  apply(sep_auto simp add: leaf_iter_assn_def split!: prod.splits dest!: mod_starD)
  subgoal for a
  apply(cases xs2; cases a)
    by auto
  done

(* copied from peter lammichs lseg_prec2 *)
declare mult.left_commute[simp add]
lemma leafs_assn_prec2: 
  "\<forall>l l'. (h\<Turnstile>
      (leafs_assn l p None * F1) \<and>\<^sub>A (leafs_assn l' p None * F2)) 
    \<longrightarrow> l=l'"
  apply (intro allI)
  subgoal for l l'
  proof (induct l arbitrary: p l' F1 F2)
    case Nil thus ?case
      apply simp_all
      apply (cases l')
      apply simp
      apply (cases p)
      apply auto
      done
  next
    case (Cons y l)
    from Cons.prems show ?case
      apply (cases p)
      apply simp
      apply (cases l')
      apply (auto) []
      apply (clarsimp)
      apply (rule)
      apply (drule_tac p=a in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      subgoal for a aa b list fwd fwda
        apply(subgoal_tac "fwd=fwda")
      using Cons.hyps[of fwd "a \<mapsto>\<^sub>r Btleaf y fwda * F1" list "a \<mapsto>\<^sub>r Btleaf (aa, b) fwd * F2", simplified]
       apply (simp add: mult.left_assoc mod_and_dist)
      apply (simp add: ab_semigroup_mult_class.mult.commute)
      apply (drule_tac p=a in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
    done
  qed
  done
declare mult.left_commute[simp del]

interpretation leaf_node_it: imp_list_iterate
    "\<lambda>x y. leafs_assn x y None"
    leaf_iter_assn
    leaf_iter_init
    leaf_iter_has_next
    leaf_iter_next
  apply(unfold_locales)
  subgoal 
    by (simp add: leafs_assn_prec2 precise_def)
  subgoal for l p 
    by (sep_auto heap add: leaf_iter_init_rule)
  subgoal for l' l p it
    thm leaf_iter_next_rule
    apply(cases l'; cases it)
    by (sep_auto heap add: leaf_iter_next_rule)+
  subgoal for l p l' it'
    thm leaf_iter_has_next_rule
    apply(cases it')
    apply(rule hoare_triple_preI)
    apply(sep_auto heap add: leaf_iter_has_next_rule)
    done
  subgoal for l p l' it
  unfolding leaf_iter_assn_def
  apply(cases it)
    apply simp_all
  apply(rule ent_ex_preI)
  by (sep_auto simp add: leafs_assn_aux_append)
  done

interpretation leaf_elements_iter: flatten_iter
  "\<lambda>x y. leafs_assn x y None" leaf_iter_assn leaf_iter_init leaf_iter_has_next leaf_iter_next
  "is_pfa (2*k)" "pfa_is_it (2*k)" pfa_it_init pfa_it_has_next pfa_it_next
  by (unfold_locales)

thm leaf_elements_iter.is_flatten_list.simps
thm leaf_elements_iter.is_flatten_it.simps
thm tree_leaf_iter_init_def
thm leaf_elements_iter.flatten_it_init_def
print_theorems

fun leaf_elements_iter_init :: "('a::heap) btnode ref \<Rightarrow> _" where
  "leaf_elements_iter_init ti = do {
        rz \<leftarrow> tree_leaf_iter_init (Some ti);
        it \<leftarrow> leaf_elements_iter.flatten_it_init (fst rz);
        return it
}"


(* NOTE: the other direction does not work, we are loosing information here
  workaround: introduce specialized is_flatten_list assumption, show that all operations
  preserve its correctness
*)
lemma leaf_nodes_imp_flatten_list:
  "leaf_nodes_assn k ts r None \<Longrightarrow>\<^sub>A
   list_assn leaf_node ts (map bplustree.vals ts) *
   leaf_elements_iter.is_flatten_list k (concat (map bplustree.vals ts)) r"
  apply(simp add: leaf_nodes_assn_split)
  apply(rule ent_ex_preI)+
  subgoal for ps
    apply(inst_ex_assn ps "map bplustree.vals ts")
    apply sep_auto
    done
  done

lemma concat_leaf_nodes_leaves: "(concat (map bplustree.vals (leaf_nodes t))) = leaves t"
  apply(induction t rule: leaf_nodes.induct)
  subgoal by auto
  subgoal for ts t
    apply(induction ts)
    subgoal by simp
    subgoal by auto
    done
  done

lemma leaf_elements_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r None>
leaf_elements_iter_init ti
<leaf_elements_iter.is_flatten_it k (leaves t) r (leaves t)>\<^sub>t"
  unfolding leaf_elements_iter_init.simps
  using assms 
  apply (sep_auto heap add:
      tree_leaf_iter_init_rule
  )
    supply R = Hoare_Triple.cons_pre_rule[OF leaf_nodes_imp_flatten_list[of k "leaf_nodes t" r],
        where Q="\<lambda>it. leaf_elements_iter.is_flatten_it k (leaves t) r (leaves t) it * true"
        and c="leaf_elements_iter.flatten_it_init r"]
    thm R
    apply(sep_auto heap add: R)
    subgoal
      apply(simp add: concat_leaf_nodes_leaves)
      apply sep_auto
        done
    subgoal by sep_auto
    done

end