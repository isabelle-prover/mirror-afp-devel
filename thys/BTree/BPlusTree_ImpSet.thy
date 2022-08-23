theory BPlusTree_ImpSet
  imports
    BPlusTree_Set
    BPlusTree_ImpSplit
    "HOL-Real_Asymp.Inst_Existentials"
begin

section "Imperative Set operations"

subsection "Auxiliary operations"


text "This locale extends the abstract split locale,
assuming that we are provided with an imperative program
that refines the abstract split function."


(* TODO separate into split_tree and split + split_list  *)
locale split\<^sub>i_set = abs_split_set: split_set split + split\<^sub>i_tree split split\<^sub>i
  for split::
    "('a bplustree \<times> 'a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
  and split\<^sub>i :: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap" +
  fixes isin_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> bool Heap"
    and ins_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
    and del_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
  assumes isin_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ks (a',n')> 
    isin_list\<^sub>i x (a',n') 
  <\<lambda>b. 
    is_pfa c ks (a',n')
    * \<up>(isin_list x ks = b)>\<^sub>t"
  and ins_list_rule [sep_heap_rules]:"sorted_less ks' \<Longrightarrow>
   <is_pfa c ks' (a',n')>
    ins_list\<^sub>i x (a',n') 
  <\<lambda>(a'',n'').  is_pfa (max c (length (insert_list x ks'))) (insert_list x ks') (a'',n'') >\<^sub>t"
  and del_list_rule [sep_heap_rules]:"sorted_less ks'' \<Longrightarrow>
   <is_pfa c ks'' (a',n')> 
    del_list\<^sub>i x (a',n') 
  <\<lambda>(a'',n''). is_pfa c (delete_list x ks'') (a'',n'') >\<^sub>t"
begin

subsection "Initialization"

definition empty\<^sub>i ::"nat \<Rightarrow> 'a btnode ref Heap"
  where "empty\<^sub>i k = do {
  empty_list \<leftarrow> pfa_empty (2*k);
  empty_leaf \<leftarrow> ref (Btleaf empty_list None);
  return empty_leaf
}"

lemma empty\<^sub>i_rule:
  shows "<emp>
  empty\<^sub>i k
  <\<lambda>r. bplustree_assn k (abs_split_set.empty_bplustree) r (Some r) None>"
  apply(subst empty\<^sub>i_def)
  apply(sep_auto simp add: abs_split_set.empty_bplustree_def)
  done

subsection "Membership"

(* TODO introduce imperative equivalents to searching/inserting/deleting in a list *)
partial_function (heap) isin\<^sub>i :: "'a btnode ref \<Rightarrow> 'a \<Rightarrow>  bool Heap"
  where
    "isin\<^sub>i p x = do {
  node \<leftarrow> !p;
  (case node of
     Btleaf xs _ \<Rightarrow> isin_list\<^sub>i x xs |
     Btnode ts t \<Rightarrow> do {
       i \<leftarrow> split\<^sub>i ts x;
       tsl \<leftarrow> pfa_length ts;
       if i < tsl then do {
         s \<leftarrow> pfa_get ts i;
         let (sub,sep) = s in
           isin\<^sub>i (the sub) x
       } else
           isin\<^sub>i t x
    }
)}"

lemma nth_zip_zip:
  assumes "length ys = length xs"
    and "length zs = length xs"
    and "zs1 @ ((suba', x), sepa') # zs2 =
    zip (zip ys xs) zs"
  shows "suba' = ys ! length zs1 \<and>
         sepa' = zs ! length zs1 \<and>
         x = xs ! length zs1"
proof -
  obtain suba'' x' sepa'' where "zip (zip ys xs) zs ! length zs1 = ((suba'', x'), sepa'')"
    by (metis surj_pair)
  moreover have "((suba'', x'), sepa'')  = ((suba', x), sepa')"
    by (metis calculation assms(3) nth_append_length)
  moreover have "length zs1 < length xs"
  proof - 
    have "length (zip (zip ys xs) zs) = length xs"
      by (simp add: assms(1,2))
    then have "length zs1 + 1 + length zs2 = length xs"
      by (metis assms(1,3) group_cancel.add1 length_Cons length_append plus_1_eq_Suc)
    then show ?thesis
    by (simp add: assms(1))
  qed
  ultimately show ?thesis
    using assms(1,2) by auto
qed


lemma  "k > 0 \<Longrightarrow> root_order k t \<Longrightarrow> sorted_less (inorder t) \<Longrightarrow> sorted_less (leaves t) \<Longrightarrow>
   <bplustree_assn k t ti r z>
     isin\<^sub>i ti x
   <\<lambda>y. bplustree_assn k t ti r z * \<up>(abs_split_set.isin t x = y)>\<^sub>t"
proof(induction t x arbitrary: ti r z rule: abs_split_set.isin.induct)
  case (1 x r z)
  then show ?case
    apply(subst isin\<^sub>i.simps)
    apply sep_auto
    done
next
  case (2 ts t x ti r z)
   obtain ls rs where list_split[simp]: "split ts x = (ls,rs)"
     by (cases "split ts x")
  moreover have ts_non_empty: "length ts > 0"
    using "2.prems"(2) root_order.simps(2) by blast
  moreover have "sorted_less (separators ts)"
    using "2.prems"(3) sorted_inorder_separators by blast
  ultimately show ?case
  proof (cases rs)
    (* NOTE: induction condition trivial here *)
    case [simp]: Nil
    show ?thesis
      apply(subst isin\<^sub>i.simps)
      using ts_non_empty  apply(sep_auto)
      subgoal  using \<open>sorted_less (separators ts)\<close> by blast
      apply simp
      apply sep_auto
        apply(rule hoare_triple_preI)
      apply (sep_auto)
      subgoal for a b ti tsi' rs x sub sep
        apply(auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
        done
      thm "2.IH"(1)[of ls "[]"]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      subgoal
        using "2.prems"(2) order_impl_root_order
        by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
      subgoal 
        using "2.prems"(3) sorted_inorder_induct_last
        by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
      subgoal using "2"(6) sorted_leaves_induct_last
        by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      done
  next
    case [simp]: (Cons h rrs)
    obtain sub sep where h_split[simp]: "h = (sub,sep)"
      by (cases h)
      then show ?thesis
        apply(simp split: list.splits prod.splits)
        apply(subst isin\<^sub>i.simps)
        using "2.prems" sorted_inorder_separators 
        apply(sep_auto)
          (* simplify towards induction step *)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
(* NOTE show that z = (suba, sepa)  -- adjusted since we now contain also current pointers and forward pointers *)
         apply(rule norm_pre_ex_rule)+
         apply(rule hoare_triple_preI)
        subgoal for tsi n ti tsi' pointers suba sepa zs1 z zs2
          apply(cases z)
          subgoal for subacomb sepa'
            apply(cases subacomb)
            subgoal for suba' subp subfwd
          apply(subgoal_tac "z = ((suba, subp, subfwd), sepa)", simp)
          thm "2.IH"(2)[of ls rs h rrs sub sep "(the suba')" subp subfwd]
          using 2(3,4,5,6) apply(sep_auto
              heap:"2.IH"(2)[of ls rs h rrs sub sep "the suba'" subp subfwd]
              simp add: sorted_wrt_append)
          using list_split Cons h_split apply simp_all
          subgoal 
            by (meson "2.prems"(1) order_impl_root_order)
          subgoal
            apply(rule impI)
            apply(inst_ex_assn "(tsi,n)" "ti" "tsi'" "(zs1 @ ((suba', subp, subfwd), sepa') # zs2)" "pointers" "zs1" "z" "zs2")
              (* proof that previous assumptions hold later *)
             apply sep_auto
            done
          subgoal
            (* prove subgoal_tac assumption *)
            using nth_zip_zip[of "subtrees tsi'" "zip (r # butlast pointers) pointers" "separators tsi'" zs1 suba' "(subp, subfwd)" sepa' zs2]
             apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
          done
        done
      done
    done
      (* eliminate last vacuous case *)
  apply(rule hoare_triple_preI)
  apply(auto simp add: split_relation_def dest!: mod_starD list_assn_len)[]
  done
  qed
qed

subsection "Insertion"


datatype 'c btupi = 
  T\<^sub>i "'c btnode ref" |
  Up\<^sub>i "'c btnode ref" "'c" "'c btnode ref"

fun btupi_assn where
  "btupi_assn k (abs_split_set.T\<^sub>i l) (T\<^sub>i li) r z =
   bplustree_assn k l li r z" |
(*TODO ai is not necessary not in the heap area of li *)
  "btupi_assn k (abs_split_set.Up\<^sub>i l a r) (Up\<^sub>i li ai ri) r' z' =
   (\<exists>\<^sub>A newr. bplustree_assn k l li r' newr * bplustree_assn k r ri newr z' * id_assn a ai)" |
  "btupi_assn _ _ _ _ _ = false"


(* TODO take in a pointer ot a btnode instead, only create one new node *)
definition node\<^sub>i :: "nat \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btupi Heap" where
  "node\<^sub>i k p \<equiv> do {
    pt \<leftarrow> !p;
    let a = kvs pt; ti = lst pt in do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      p := Btnode a' ti;
      return (T\<^sub>i p)
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: ('a btnode ref option \<times> 'a) pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a (i-1);
      b' \<leftarrow> pfa_drop a i b;
      a' \<leftarrow> pfa_shrink (i-1) a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      let (sub,sep) = m in do {
        p := Btnode a'' (the sub);
        r \<leftarrow> ref (Btnode b' ti);
        return (Up\<^sub>i p sep r)
      }
    }
  }
}"

definition Lnode\<^sub>i :: "nat \<Rightarrow> 'a btnode ref  \<Rightarrow> 'a btupi Heap" where
  "Lnode\<^sub>i k p \<equiv> do {
    pt \<leftarrow> !p;
    let a = vals pt; nxt = fwd pt in do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      p := Btleaf a' nxt;
      return (T\<^sub>i p)
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: 'a pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a (i-1);
      b' \<leftarrow> pfa_drop a i b;
      a' \<leftarrow> pfa_shrink i a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      r \<leftarrow> ref (Btleaf b' nxt);
      p := Btleaf a'' (Some r);
      return (Up\<^sub>i p m r)
    }
  }
}"

(* TODO Lnode\<^sub>i allocates a new node when invoked, do not invoke if array didn't grow *)
partial_function (heap) ins\<^sub>i :: "nat \<Rightarrow> 'a \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btupi Heap"
  where
    "ins\<^sub>i k x p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf ksi nxt \<Rightarrow> do {
      ksi' \<leftarrow> ins_list\<^sub>i x ksi; 
      p := Btleaf ksi' nxt;
      Lnode\<^sub>i k p
    } |
    Btnode tsi ti \<Rightarrow> do {
      i \<leftarrow> split\<^sub>i tsi x;
      tsl \<leftarrow> pfa_length tsi;
      if i < tsl then do {
        s \<leftarrow> pfa_get tsi i;
        let (sub,sep) = s in do {
          r \<leftarrow> ins\<^sub>i k x (the sub);
          case r of (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set tsi i (Some lp,sep);
            return (T\<^sub>i p)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            pfa_set tsi i (Some rp,sep);
            tsi' \<leftarrow> pfa_insert_grow tsi i (Some lp,x');
            p := Btnode tsi' ti;
            node\<^sub>i k p
          }
        }
      }
      else do {
        r \<leftarrow> ins\<^sub>i k x ti;
        case r of (T\<^sub>i lp) \<Rightarrow> do {
            p := (Btnode tsi lp);
            return (T\<^sub>i p)
        } | (Up\<^sub>i lp x' rp) \<Rightarrow> do { 
            tsi' \<leftarrow> pfa_append_grow' tsi (Some lp,x');
            p := Btnode tsi' rp;
            node\<^sub>i k p
        }
      }
  }
)}"


(*fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a bplustree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)" 

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a bplustree \<Rightarrow> 'a bplustree" where
  "insert k x t = tree\<^sub>i (ins k x t)"
*)

definition insert\<^sub>i :: "nat \<Rightarrow> 'a \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref Heap" where
  "insert\<^sub>i \<equiv> \<lambda>k x ti. do {
  ti' \<leftarrow> ins\<^sub>i k x ti;
  case ti' of
     T\<^sub>i sub \<Rightarrow> return sub |
     Up\<^sub>i l a r \<Rightarrow> do {
        kvs \<leftarrow> pfa_init (2*k) (Some l,a) 1;
        t' \<leftarrow> ref (Btnode kvs r);
        return t'
      }
}"


lemma take_butlast_prepend: "take n (butlast (r # pointers)) =
       butlast (r # take n pointers)"
  apply (cases "length pointers > n")
  by (simp_all add: butlast_take take_Cons' take_butlast)

lemma take_butlast_append: "take n (butlast (xs @ x # ys)) =
       take n (xs @ (butlast (x#ys)))"
  by (auto simp add: butlast_append)

lemma map_eq_nth_eq_diff:
  assumes A: "map f l = map g l'"
  and B: "i < length l"
  shows "f (l!i) = g (l'!i)"
proof -
  from A have "length l = length l'"
    by (metis length_map)
  thus ?thesis using A B
    apply (induct l l' arbitrary: i rule: list_induct2)
      apply (simp)
    subgoal for x xs y ys i
      apply(cases i)
      apply(simp add: nth_def)
      apply simp
      done
    done
qed

lemma "BPlusTree_Split.split_half ts = (ls,rs) \<Longrightarrow> length ls = Suc (length ts) div 2"
  by (metis Suc_eq_plus1 split_half_conc)

lemma take_half_less: "take (Suc (length ts) div 2) ts = ls @ [(sub, sep)] \<Longrightarrow> length ls < length ts"
proof -
  assume " take (Suc (length ts) div 2) ts = ls @ [(sub, sep)]"
  then have "ts \<noteq> []"
    by force
  then have "Suc (length ts) div 2 \<le> length ts"
    by linarith
  then have "length (take (Suc (length ts) div 2) ts) \<le> length ts" 
    by simp
  moreover have "length ls < length (take (Suc (length ts) div 2) ts)"
    by (simp add: \<open>take (Suc (length ts) div 2) ts = ls @ [(sub, sep)]\<close>)
  ultimately show "length ls < length ts"
    by linarith
qed

declare abs_split_set.node\<^sub>i.simps [simp add]
declare last.simps[simp del] butlast.simps[simp del]
lemma node\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r#pointers)) (butlast (pointers@[z])))) (map snd tsi')"
  shows "<p \<mapsto>\<^sub>r Btnode (a,n) ti * is_pfa c tsi' (a,n) * blist_assn k ts tsi'' * bplustree_assn k t ti (last (r#pointers)) z>
  node\<^sub>i k p
  <\<lambda>u. btupi_assn k (abs_split_set.node\<^sub>i k ts t) u r z>\<^sub>t"
proof (cases "length ts \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto)
    subgoal by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using assms(3,4) by (sep_auto)
    subgoal 
      apply(subgoal_tac "length ts = length tsi'")
    subgoal using True by (sep_auto)
    subgoal using True assms by (sep_auto dest!: mod_starD list_assn_len)
    done
  done
next
  case [simp]: False
  then obtain ls sub sep rs where      
    split_half_eq: "BPlusTree_Split.split_half ts = (ls@[(sub,sep)],rs)"
    using abs_split_set.node\<^sub>i_cases by blast
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply sep_auto
    subgoal by (sep_auto simp add:  split_relation_alt split_relation_length is_pfa_def dest!: mod_starD list_assn_len)
    subgoal using assms by (sep_auto dest!: mod_starD list_assn_len)
    subgoal
      apply(subgoal_tac "length ts = length tsi'")
      subgoal using False by (sep_auto dest!: mod_starD list_assn_len)
      subgoal using assms(3,4) by (sep_auto dest!: mod_starD list_assn_len)
      done
    apply sep_auto
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply sep_auto
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply simp
    apply(rule hoare_triple_preI)
    apply(vcg)
    apply(simp add: split_relation_alt)
    apply(rule impI)+
    subgoal for  _ _ rsia subi' sepi' rsin lsi _
      supply R = append_take_drop_id[of "(length ls)" ts,symmetric]
      thm R
      apply(subst R)
      supply R = Cons_nth_drop_Suc[of "length ls" ts, symmetric]
      thm R
      apply(subst R)
      subgoal
        by (meson take_half_less)
     supply R=list_assn_append_Cons_left[where xs="take (length ls) ts" and ys="drop (Suc (length ls)) ts" and x="ts ! (length ls)"]
      thm R
      apply(subst R)
      apply(auto)[]
      apply(rule ent_ex_preI)+
      apply(subst ent_pure_pre_iff; rule impI)
      apply (simp add: prod_assn_def split!: prod.splits)
      subgoal for tsi''l subi'' subir subinext sepi'' tsi''r sub' sep'
        (* instantiate right hand side *)
(* newr is the first leaf of the tree directly behind sub
  and (r#pointers) is the list of all first leafs of the tree in this node
   \<rightarrow> the pointer at position of sub in pointers
      or the pointer at position of sub+1 in (r#pointers)
*)
      (* Suc (length tsi') div 2 - Suc 0) = length ls *)
        apply(inst_ex_assn "subinext" "(rsia,rsin)" ti
        "drop (length ls+1) tsi'"
        "drop (length ls+1) tsi''"
        "drop (length ls+1) pointers"
        lsi
        "the subi'"
        "take (length ls) tsi'"
        "take (length ls) tsi''"
        "take (length ls) pointers"
      )
      apply (sep_auto)
      subgoal using assms(3) by linarith
      subgoal 
        using assms(3,4) by (auto dest!: mod_starD 
          simp add: take_map[symmetric] take_zip[symmetric] take_butlast_prepend[symmetric]
      )
         subgoal using assms(3,4) by (auto dest!: mod_starD      
          simp add: list_assn_prod_map id_assn_list_alt)
         subgoal 
           apply(subgoal_tac "length ls < length pointers")
           apply(subgoal_tac "subinext = pointers ! (length ls)")
           subgoal
        using assms(3,4) apply (auto 
          simp add: drop_map[symmetric] drop_zip[symmetric] drop_butlast[symmetric] Cons_nth_drop_Suc
      )[]
           supply R = drop_Suc_Cons[where n="length ls" and xs="butlast pointers" and x=r, symmetric]
           thm R
           apply(simp only: R drop_zip[symmetric])
           apply (simp add: last.simps butlast.simps)
           done
        subgoal apply(auto dest!: mod_starD list_assn_len)     
        proof (goal_cases)
        case 1
        have "length ls < length tsi''"
          using assms(3,4) "1" by auto
        moreover have "subinext = snd (snd (fst (tsi'' ! length ls)))"
          using 1 calculation by force
        ultimately have "subinext = map snd (map snd (map fst tsi'')) ! length ls"
          by auto
        then show ?case
          using assms(3,4) by auto
      qed
          subgoal  apply(auto dest!: mod_starD  list_assn_len)
        proof (goal_cases)
          case 1 
          then have "length ls  < length ts"
            by (simp)
          moreover have "length ts = length tsi''"
            by (simp add: 1)
          moreover have "\<dots> = length pointers"
            using assms(3,4) by auto
          ultimately show ?case by simp
        qed
      done
    apply(rule entails_preI)
      (* introduce some simplifying equalities *)
        apply(subgoal_tac "Suc (length tsi') div 2 = length ls + 1")
     prefer 2 subgoal 
        apply(auto dest!: mod_starD  list_assn_len)     
        proof (goal_cases)
          case 1
          have "length tsi' = length tsi''"
            using assms(3,4) by auto
          also have "\<dots> = length ts"
            by (simp add: 1)
          finally show ?case 
            using 1
            by (metis Suc_eq_plus1 abs_split_set.length_take_left div2_Suc_Suc length_append length_append_singleton numeral_2_eq_2)
        qed
    apply(subgoal_tac "length ts = length tsi''")
        prefer 2 subgoal using assms(3,4) by (auto dest!: mod_starD  list_assn_len)     
    apply(subgoal_tac "(sub', sep') = (sub, sep)")
        prefer 2 subgoal
        by (metis One_nat_def Suc_eq_plus1 Suc_length_conv abs_split_set.length_take_left length_0_conv length_append less_add_Suc1 nat_arith.suc1 nth_append_length nth_take)
      apply(subgoal_tac "length ls = length tsi''l")
        prefer 2 subgoal by (auto dest!: mod_starD list_assn_len)
    apply(subgoal_tac "(subi'', sepi'') = (subi', sepi')")
      prefer 2 subgoal
        using assms(3,4) apply (auto dest!: mod_starD list_assn_len)
      proof (goal_cases)
        case 1
        then have "tsi'' ! length tsi''l =  ((subi'', subir, subinext), sepi'')"
          by auto
        moreover have "length tsi''l < length tsi''"
          by (simp add: 1)
        moreover have "length tsi''l < length tsi'"
          using "1" assms(3) by linarith
        ultimately have
            "fst (fst (tsi'' ! length tsi''l)) = fst (tsi' ! length tsi''l)"
            "snd (tsi'' ! length tsi''l) = snd (tsi' ! length tsi''l)"
          using assms(4) by auto
        then show ?case
          by (simp add: "1" \<open>tsi'' ! length tsi''l = ((subi'', subir, subinext), sepi'')\<close>)
        case 2
        then show ?case
          by (metis \<open>snd (tsi'' ! length tsi''l) = snd (tsi' ! length tsi''l)\<close> \<open>tsi'' ! length tsi''l = ((subi'', subir, subinext), sepi'')\<close> snd_conv)
      qed
    apply(subgoal_tac "(last (r # take (length ls) pointers)) = subir")
      prefer 2 subgoal
        using assms(3) apply (auto dest!: mod_starD list_assn_len)
      proof (goal_cases)
        case 1
        have "length tsi''l < length tsi''"
          by (simp add: 1)
        then have "fst (snd (fst (tsi'' ! length tsi''l))) = subir"
          using 1 assms(4) by auto
        moreover have "map fst (map snd (map fst tsi'')) = butlast (r#pointers)"
          using assms(3,4) by auto
        moreover have "(last (r#take (length ls) pointers)) = butlast (r#pointers) ! (length tsi''l)"
          by (smt (z3) "1" One_nat_def Suc_eq_plus1 Suc_to_right abs_split_set.length_take_left append_butlast_last_id div_le_dividend le_add2 length_butlast length_ge_1_conv length_take lessI list.size(4) min_eq_arg(2) nth_append_length nth_take nz_le_conv_less take_Suc_Cons take_butlast_conv)
        ultimately show ?case
          using 1 apply auto
          by (metis (no_types, opaque_lifting) 1 length_map map_map nth_append_length)
      qed
    apply(subgoal_tac "(last (subinext # drop (Suc (length tsi''l)) pointers)) = last (r#pointers)")
       prefer 2 subgoal
        using assms(3) apply (auto dest!: mod_starD list_assn_len)
      proof (goal_cases)
        case 1
        have "length tsi''l < length tsi''"
          using 1 by auto
        moreover have "subinext = snd (snd (fst (tsi'' ! length tsi''l)))"
          using "1" calculation by force
        ultimately have "subinext = map snd (map snd (map fst tsi'')) ! length tsi''l"
          by auto
        then have "subinext = pointers ! length tsi''l" 
          using assms(3,4) by auto
        then have "(subinext # drop (Suc (length tsi''l)) pointers) = drop (length tsi''l) pointers"
          by (metis 1 Cons_nth_drop_Suc Suc_eq_plus1 Suc_to_right abs_split_set.length_take_left div_le_dividend le_add1 less_Suc_eq nz_le_conv_less take_all_iff zero_less_Suc)
        moreover have "last (drop (length tsi''l) pointers) = last pointers"
          using \<open>length tsi''l < length tsi''\<close>  1 by force
        ultimately show ?case
          by (auto simp add: last.simps butlast.simps)
      qed
    apply(subgoal_tac "take (length tsi''l) ts = ls")
      prefer 2 subgoal
        by (metis append.assoc append_eq_conv_conj append_take_drop_id)
    apply(subgoal_tac "drop (Suc (length tsi''l)) ts = rs")
      prefer 2 subgoal by (metis One_nat_def Suc_eq_plus1 Suc_length_conv append_eq_conv_conj append_take_drop_id length_0_conv length_append)
    subgoal by (sep_auto)
    done
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]
declare abs_split_set.node\<^sub>i.simps [simp del]

declare abs_split_set.Lnode\<^sub>i.simps [simp add]
lemma Lnode\<^sub>i_rule:
  assumes "k > 0 " "r = Some a" "2*k \<le> c" "c \<le> 4*k"
  shows "<a \<mapsto>\<^sub>r (Btleaf xsi z) * is_pfa c xs xsi>
  Lnode\<^sub>i k a
  <\<lambda>a. btupi_assn k (abs_split_set.Lnode\<^sub>i k xs) a r z>\<^sub>t"
proof (cases "length xs \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst Lnode\<^sub>i_def)
      apply(rule hoare_triple_preI; simp)
    using assms apply(sep_auto eintros del: exI heap add: pfa_shrink_cap_rule)
    subgoal for _ _ aaa ba
      apply(inst_existentials aaa ba z)
      apply simp_all
      done
    subgoal
      apply(rule hoare_triple_preI)
      using True apply (auto dest!: mod_starD list_assn_len)+
      done
    done
next
  case [simp]: False
  then obtain ls sep rs where
    split_half_eq: "BPlusTree_Split.split_half xs = (ls@[sep],rs)"
    using abs_split_set.Lnode\<^sub>i_cases by blast
  then show ?thesis
    apply(subst Lnode\<^sub>i_def)
    apply auto
    using assms apply (vcg heap add: pfa_shrink_cap_rule; simp)
      apply(rule hoare_triple_preI)
      apply (sep_auto heap add: pfa_drop_rule simp add: split_relation_alt
              dest!: mod_starD list_assn_len)

    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    apply(sep_auto)
    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    apply(sep_auto eintros del: exI)
    subgoal for  _ _ _ _ rsa rn lsa ln newr
        (* instantiate right hand side *)
      apply(inst_existentials "Some newr"
             rsa rn  z
             lsa ln "Some newr"
            )
        (* introduce equality between equality of split tsi/ts and original lists *)
      apply(simp_all add: pure_def)
      apply(sep_auto dest!: mod_starD)
      apply(subgoal_tac "Suc (length xs) div 2 = Suc (length ls)")
      apply(subgoal_tac "xs = take (Suc (length ls)) xs @  drop (Suc (length ls)) xs")
      subgoal 
        by (metis nth_append_length)
      subgoal by auto
      subgoal by auto
      subgoal by sep_auto
      done
    done
qed
declare abs_split_set.Lnode\<^sub>i.simps [simp del]

lemma Lnode\<^sub>i_rule_tree:
  assumes "k > 0"
  shows "<bplustree_assn k (Leaf xs) a r z>
  Lnode\<^sub>i k a
  <\<lambda>a. btupi_assn k (abs_split_set.Lnode\<^sub>i k xs) a r z>\<^sub>t"
    using assms by (sep_auto heap add: Lnode\<^sub>i_rule)

lemma node\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split_set.node\<^sub>i k ts t = abs_split_set.T\<^sub>i (Node ts t)"
  by (simp add: abs_split_set.node\<^sub>i.simps)

lemma Lnode\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split_set.Lnode\<^sub>i k ts = abs_split_set.T\<^sub>i (Leaf ts)"
  by (simp add: abs_split_set.Lnode\<^sub>i.simps)

lemma id_assn_emp[simp]: "id_assn a a = emp"
  by (simp add: pure_def)

lemma butlast2[simp]: "butlast (ts@[a,b]) = ts@[a]"
  by (induction ts) auto

lemma butlast3[simp]: "butlast (ts@[a,b,c]) = ts@[a,b]"
  by (induction ts) auto

lemma zip_append_last: "length as = length bs \<Longrightarrow> zip (as@[a]) (bs@[b]) = zip as bs @ [(a,b)]"
  by simp

lemma pointers_append: "zip (z#as) (as@[a]) = zip (butlast (z#as)) as @ [(last (z#as),a)]"
  by (metis (no_types, opaque_lifting) Suc_eq_plus1 append_butlast_last_id butlast_snoc length_Cons length_append_singleton length_butlast list.distinct(1) zip_append_last)

lemma node\<^sub>i_rule_app: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r'#pointers)) pointers)) (map snd tsi')"
  shows "
<  p \<mapsto>\<^sub>r Btnode (tsia,tsin) ri *
   is_pfa c (tsi' @ [(Some li, a)]) (tsia, tsin) *
   blist_assn k ts tsi'' *
   bplustree_assn k l li (last (r'#pointers)) lz *
   bplustree_assn k r ri lz rz> node\<^sub>i k p
 <\<lambda>u. btupi_assn k (abs_split_set.node\<^sub>i k (ts @ [(l, a)]) r) u r' rz>\<^sub>t"
proof -
(*[of k c "(tsi' @ [(Some li, b)])" _ _ "(ls @ [(l, a)])" r ri]*)
  note node\<^sub>i_rule[of k c "tsi'@[(Some li, a)]" "pointers@[lz]" "tsi''@[((Some li, last(r'#pointers), lz),a)]" r' rz p tsia tsin ri "ts@[(l,a)]" r, OF assms(1,2)]
  then show ?thesis
    using assms
    apply (auto simp add:
         list_assn_app_one pointers_append
         mult.left_assoc
    )
    done
qed

lemma norm_pre_ex_drule: "<\<exists>\<^sub>Ax. P x> c <Q> \<Longrightarrow> (\<And>x. <P x> c <Q>)"
proof (goal_cases)
  case 1
  then show ?case
    using Hoare_Triple.cons_pre_rule by blast
qed

(* setting up the simplifier for tsi'' in the other direction *)
lemma node\<^sub>i_rule_diff_simp: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "zip (zip (map fst tsi') (zip (butlast (r#pointers)) (butlast (pointers@[z])))) (map snd tsi') = tsi''"
  shows "<p \<mapsto>\<^sub>r Btnode (a,n) ti * is_pfa c tsi' (a,n) * blist_assn k ts tsi'' * bplustree_assn k t ti (last (r#pointers)) z>
  node\<^sub>i k p
  <\<lambda>u. btupi_assn k (abs_split_set.node\<^sub>i k ts t) u r z>\<^sub>t"
  using node\<^sub>i_rule assms by (auto simp del: butlast.simps last.simps)

lemma list_assn_aux_append_Cons2: 
  shows "length xs = length zsl \<Longrightarrow> list_assn R (xs@x#y#ys) (zsl@z1#z2#zsr) = (list_assn R xs zsl * R x z1 * R y z2 * list_assn R ys zsr)"
  by (sep_auto simp add: mult.assoc)

lemma pointer_zip_access: "length tsi' = length pointers \<Longrightarrow> i < length tsi' \<Longrightarrow>
  zip (zip (map fst tsi') (zip (butlast (r'#pointers)) (butlast (pointers@[z])))) (map snd tsi') ! i
= ((fst (tsi' ! i), (r'#pointers) ! i, pointers ! i), snd (tsi' ! i))"
  apply(auto)
  by (metis append_butlast_last_id butlast.simps(2) len_greater_imp_nonempty length_Cons length_append_singleton nth_butlast)

lemma pointer_zip'_access: "length tsi' = length pointers \<Longrightarrow> i < length tsi' \<Longrightarrow>
  zip (zip (map fst tsi') (zip (butlast (r'#pointers)) (butlast (pointers@[z])))) (map snd tsi') ! i
= ((fst (tsi' ! i), (r'#pointers) ! i, pointers ! i), snd (tsi' ! i))"
  apply(auto)
  by (metis One_nat_def nth_take take_Cons' take_butlast_conv)

lemma access_len_last: "(x#xs@ys) ! (length xs) = last (x#xs)"
  by (induction xs) auto


lemma node\<^sub>i_rule_ins2: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "pointers = lpointers@lz#rz#rpointers"
    and "length tsi'' = length pointers"
    and "length lpointers = length lsi'"
    and "length rpointers = length rsi'"
    and "length lsi'' = length ls"
    and "length lsi' = length ls"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r'#pointers)) (butlast (pointers@[z])))) (map snd tsi')"
    and "tsi' = (lsi' @ (Some li, a) # (Some ri,a') # rsi')" 
    and "lsi'' = take (length lsi') tsi''"
    and "rsi'' = drop (Suc (Suc (length lsi'))) tsi''"
    and "r'' = last (r'#lpointers)"
    and "z'' = last (r'#pointers)"
    and "length tsi' = length pointers"
  shows "
<  p \<mapsto>\<^sub>r Btnode (tsia,tsin) ti *
   is_pfa c (lsi' @ (Some li, a) # (Some ri,a') # rsi') (tsia, tsin) *
   blist_assn k ls lsi'' *
   bplustree_assn k l li r'' lz*
   bplustree_assn k r ri lz rz*
   blist_assn k rs rsi'' *
   bplustree_assn k t ti z'' z> node\<^sub>i k p 
<\<lambda>u. btupi_assn k (abs_split_set.node\<^sub>i k (ls @ (l, a) # (r,a') # rs) t) u r' z>\<^sub>t"
proof -
  have "
     tsi'' =
     lsi'' @ ((Some li, r'', lz), a) # ((Some ri, lz, rz), a') # rsi''"
  proof (goal_cases)
    case 1
    have "tsi'' = take (length lsi') tsi'' @ drop (length lsi') tsi''"
      by auto
    also have "\<dots> = take (length lsi') tsi'' @ tsi''!(length lsi') # drop (Suc (length lsi')) tsi''"
      by (simp add: Cons_nth_drop_Suc assms(3) assms(4) assms(5))
    also have "\<dots> = take (length lsi') tsi'' @ tsi''!(length lsi') # tsi''!(Suc (length lsi')) #drop (Suc (Suc (length lsi'))) tsi''"
      by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_eq_plus1 Suc_le_eq assms(3) assms(4) assms(5) diff_add_inverse2 diff_is_0_eq length_append list.size(4) nat.simps(3) nat_add_left_cancel_le not_less_eq_eq)
    also have "\<dots> = lsi'' @ tsi''!(length lsi') # tsi''!(Suc (length lsi')) # rsi''"
      using assms(11) assms(12) by force
    also have "\<dots> = lsi'' @ ((Some li, r'', lz), a) # ((Some ri, lz, rz), a') # rsi''"
    proof (auto, goal_cases)
      case 1
      have "pointers ! length lsi' = lz"
        by (metis assms(3) assms(5) list.sel(3) nth_append_length)
      moreover have "(r'#pointers) ! length lsi' = r''"
        using assms access_len_last[of r' lpointers]
        by (auto simp del: last.simps butlast.simps)
      moreover have " tsi'!(length lsi') = (Some li,a)"
        using assms(10) by auto
      moreover have "length lsi' < length tsi'"
        using \<open>take (length lsi') tsi'' @ tsi'' ! length lsi' # drop (Suc (length lsi')) tsi'' = take (length lsi') tsi'' @ tsi'' ! length lsi' # tsi'' ! Suc (length lsi') # drop (Suc (Suc (length lsi'))) tsi''\<close> assms(15) assms(4) same_append_eq by fastforce
      ultimately show ?case 
        using pointer_zip'_access[of tsi' "pointers" "length lsi'" r'] assms(15) assms(9)
        by (auto simp del: last.simps butlast.simps)
    next
      case 2
      have "pointers ! (Suc (length lsi')) = rz"
        by (metis Suc_eq_plus1 append_Nil assms(3) assms(5) list.sel(3) nth_Cons_Suc nth_append_length nth_append_length_plus)
      moreover have "(r'#pointers) ! (Suc (length lsi')) = lz"
        using assms(3,4,5,6,7,8) apply auto
        by (metis nth_append_length)
      moreover have " tsi'!(Suc (length lsi')) = (Some ri,a')"
        using assms(10)
        by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_le_eq append_eq_conv_conj assms(15) assms(4) drop_all drop_eq_ConsD list.inject list.simps(3) not_less_eq_eq)
      moreover have "Suc (length lsi') < length tsi'"
        by (simp add: assms(10))
      ultimately show ?case 
        using pointer_zip'_access[of tsi' pointers "Suc (length lsi')"] assms(15) assms(9)
        by (auto simp del: last.simps butlast.simps)
    qed
    finally show ?thesis .
  qed
  moreover note node\<^sub>i_rule_diff_simp[of k c 
    "(lsi' @ (Some li, a) # (Some ri,a') # rsi')" 
    "lpointers@lz#rz#rpointers" r' z
    "lsi''@((Some li, r'', lz), a)#((Some ri, lz, rz), a')#rsi''"
    p tsia tsin ti "ls@(l,a)#(r,a')#rs" t
]
  ultimately show ?thesis
    using assms(1,2,3,4,5,6,7,8,9,10,13,14)
    apply (auto simp add: mult.left_assoc list_assn_aux_append_Cons2 prod_assn_def
simp del: last.simps)
    done
qed

lemma upd_drop_prepend: "i < length xs \<Longrightarrow> drop i (list_update xs i a) = a#(drop (Suc i) xs)" 
  by (simp add: upd_conv_take_nth_drop)

lemma zip_update: "(zip xs ys)!i = (a,b) \<Longrightarrow> list_update (zip xs ys) i (c,b) = zip (list_update xs i c) ys"
  by (metis fst_conv list_update_beyond list_update_id not_le_imp_less nth_zip snd_conv update_zip)

lemma append_Cons_last: "last (xs@x#ys) = last (x#ys)"
  by (induction xs) auto
                                                                                            
declare last.simps[simp del] butlast.simps[simp del]
lemma ins\<^sub>i_rule:
  "k > 0 \<Longrightarrow>
  sorted_less (inorder t) \<Longrightarrow>
  sorted_less (leaves t) \<Longrightarrow>
  root_order k t \<Longrightarrow>
  <bplustree_assn k t ti r z>
  ins\<^sub>i k x ti
  <\<lambda>a. btupi_assn k (abs_split_set.ins k x t) a r z>\<^sub>t"
proof (induction k x t arbitrary: ti r z rule: abs_split_set.ins.induct)
  case (1 k x xs ti r z)
  then show ?case
    apply(subst ins\<^sub>i.simps)
    apply (sep_auto heap: Lnode\<^sub>i_rule)
    done
next
  case (2 k x ts t ti r' z)
  obtain ls rrs where list_split: "split ts x = (ls,rrs)"
    by (cases "split ts x")
  have [simp]: "sorted_less (separators ts)"
    using "2.prems" sorted_inorder_separators by simp
  have [simp]: "sorted_less (inorder t)"
    using "2.prems" sorted_inorder_induct_last by simp
  show ?case
  proof (cases rrs)
    case Nil
    then have split_rel_i: "split_relation ts (ls,[]) i \<Longrightarrow> i = length ts" for i
      by (simp add: split_relation_alt)
    show ?thesis
    proof (cases "abs_split_set.ins k x t")
      case (T\<^sub>i a)
      then show ?thesis
        apply(subst ins\<^sub>i.simps)
        using Nil 
        apply(simp)
        apply vcg
        apply(simp)
        apply vcg
        thm split\<^sub>i_rule
        apply sep_auto
          apply(rule hoare_triple_preI)
        using Nil split_rel_i list_split
        apply (sep_auto dest!: split_rel_i mod_starD)
        subgoal
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for tsil tsin tti tsi'
          thm "2.IH"(1)[of ls rrs tti]
          using "2.prems" sorted_leaves_induct_last
          using  Nil list_split T\<^sub>i abs_split_set.split_conc[OF list_split] order_impl_root_order 
          apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
            subgoal by sep_auto
            subgoal by sep_auto
            done
          done
        done
    next
      case (Up\<^sub>i l a r)
      then show ?thesis
        apply(subst ins\<^sub>i.simps)
        using Nil 
        apply(simp)
        apply vcg
        apply simp
        apply vcg
        apply sep_auto
          apply(rule hoare_triple_preI)
        using Nil list_split
        apply (sep_auto dest!: split_rel_i mod_starD)
        subgoal
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)                 
        subgoal
          using Nil list_split 
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for tsia tsin tti tsi' pointers _ _ _ _ _ _ _ _ _ _  i 
          thm "2.IH"(1)[of ls rrs tti "last (r'#pointers)" z]
          using "2.prems" sorted_leaves_induct_last
          using  Nil list_split Up\<^sub>i abs_split_set.split_conc[OF list_split] order_impl_root_order
          apply(sep_auto split!: list.splits 
              simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
            subgoal by sep_auto
            apply(rule hoare_triple_preI)
            thm node\<^sub>i_rule_app
            apply(sep_auto heap add: node\<^sub>i_rule_app)
            apply(sep_auto simp add: pure_def)
            done
          done
        done
    qed
  next
    case (Cons a rs)
    obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then have [simp]: "sorted_less (inorder sub)"
      by (metis "2"(4) abs_split_set.split_set(1) list_split local.Cons some_child_sub(1) sorted_inorder_subtrees)
    from Cons have split_rel_i: "ts = ls@a#rs \<and> i = length ls \<Longrightarrow> i < length ts" for i
      by (simp add: split_relation_alt)
    then show ?thesis
      proof (cases "abs_split_set.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split)
          apply(subst ins\<^sub>i.simps)
          apply vcg
           apply auto
          apply vcg
          subgoal by sep_auto
          apply simp
          (*this solves a subgoal*) apply simp
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          using list_split Cons abs_split_set.split_conc[of ts x ls rrs] 
          apply (simp add: list_assn_append_Cons_left)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply(simp add: split_relation_alt prod_assn_def split!: prod.splits)
              (* actual induction branch *)
          subgoal for tsia tsin tti tsi' pointers suba' sepa' lsi' suba subleaf subnext sepa rsi' _ _ sub' sep'
            apply(subgoal_tac "length ls = length lsi'")
          apply(subgoal_tac "(suba', sepa') = (suba, sepa)") 
          apply(subgoal_tac "(sub', sep') = (sub, sep)") 
          thm "2.IH"(2)[of ls rs a rrs sub sep "the suba" subleaf subnext]
             apply (sep_auto heap add: "2.IH"(2))
          subgoal using "2.prems" by metis
            subgoal using "2.prems" sorted_leaves_induct_subtree \<open>sorted_less (inorder sub)\<close>
              by (auto split!: btupi.splits) 
            subgoal 
              using "2.prems"(3) sorted_leaves_induct_subtree by blast
            subgoal using "2.prems"(1,4) order_impl_root_order[of k sub] by auto
            subgoal for up
              apply(cases up)
              subgoal for ai
               apply (sep_auto eintros del: exI)
                apply(inst_existentials tsia tsin tti "tsi'[length ls := (Some ai, sepa)]" "lsi'@((Some ai, subleaf, subnext),sepa)#rsi'" pointers)
                  apply (sep_auto simp add: prod_assn_def split!: prod.splits)
                  subgoal  (* necessary goal due to the difference between implementation and abstract code *)
                  proof (goal_cases)
                    case 1
                    then have *: "((suba, subleaf, subnext), sepa) = (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi')"
                      by (metis nth_append_length)
                    have **:"(zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi') = (((subtrees tsi')!(length lsi'), (butlast (r'#pointers))!(length lsi'), pointers!(length lsi')), (separators tsi')!(length lsi'))" 
                      using 1 by simp
                    have "lsi' @ ((Some ai, subleaf, subnext), sepa) # rsi' =
                          list_update (lsi' @ ((suba, subleaf, subnext), sepa) # rsi') (length lsi') ((Some ai, subleaf, subnext), sepa)"
                      by simp
                    also have "\<dots> = list_update (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')) (length lsi') ((Some ai, subleaf,subnext), sepa)" 
                      using 1 by simp
                    also have "\<dots> = zip (list_update (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (length lsi') (Some ai, subleaf, subnext)) (separators tsi')"
                      by (meson zip_update sym[OF *])
                    finally show ?case
                      using ** *
                      by (simp add: update_zip map_update)
                  qed
                  subgoal by sep_auto
                  done
              subgoal
                apply(rule hoare_triple_preI)
                using T\<^sub>i
                subgoal by (auto dest!: mod_starD)
                done
              done
            subgoal
              using a_split by fastforce
            subgoal
                  proof (goal_cases)
                    case 1
                    then have *: "((suba, subleaf, subnext), sepa) = (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi')"
                      by (metis nth_append_length)
                    have **:"(zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi') = (((subtrees tsi')!(length lsi'), (butlast (r'#pointers))!(length lsi'), pointers!(length lsi')), (separators tsi')!(length lsi'))" 
                      using 1 by simp
                    then show ?case
                      using ** * 1
                      by simp
                  qed
                  subgoal by (auto dest!: mod_starD list_assn_len)
                  done
                subgoal
                  apply(rule hoare_triple_preI)
                    using Cons split_relation_alt[of ts ls "a#rs"] list_split
                    by (auto dest!: list_assn_len mod_starD)
                  done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply(auto simp add: Cons list_split a_split)
          apply(subst ins\<^sub>i.simps)
          apply vcg
           apply auto
          apply vcg
          subgoal by sep_auto
          apply simp
          (*this solves a subgoal*) apply simp
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          using list_split Cons abs_split_set.split_conc[of ts x ls rrs] 
          apply (simp add: list_assn_append_Cons_left)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply(simp add: split_relation_alt prod_assn_def split!: prod.splits)
              (* actual induction branch *)
          subgoal for tsia tsin tti tsi' pointers suba' sepa' lsi' suba subleaf subnext sepa rsi' _ _ sub' sep'
          apply(subgoal_tac "length ls = length lsi'") 
          apply(subgoal_tac "(suba', sepa') = (suba, sepa)") 
          apply(subgoal_tac "(sub', sep') = (sub, sep)") 
          thm "2.IH"(2)[of ls rs a rrs sub sep "the suba" subleaf subnext]
             apply (sep_auto heap add: "2.IH"(2))
          subgoal using "2.prems" by metis
            subgoal using "2.prems" sorted_leaves_induct_subtree \<open>sorted_less (inorder sub)\<close>
              by (auto split!: btupi.splits) 
            subgoal 
              using "2.prems"(3) sorted_leaves_induct_subtree by blast
            subgoal using "2.prems"(1,4) order_impl_root_order[of k sub] by auto
            subgoal for up
              apply(cases up)
            subgoal by simp
            subgoal for li ai ri (* split case *)
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
              subgoal by (sep_auto simp add: is_pfa_def)
              subgoal for aa ba ac bc ae be ak bk al bl newr x xaa
                apply(simp split!: prod.splits)
              subgoal for tsia'
                supply R= node\<^sub>i_rule_ins2[where k=k and c="max (2*k) (Suc tsin)" and
                      lsi'="take (length lsi') tsi'" and li=li and ri=ri
                      and rsi'="drop (Suc (length lsi')) tsi'"
                      and lpointers="take (length lsi') pointers"
                      and rpointers="drop (Suc (length lsi')) pointers"
                      and pointers="take (length lsi') pointers @ newr # subnext # drop (Suc (length lsi')) pointers"
                      and z''="last (r'#pointers)"
                      and tsi'="take (length lsi') tsi' @ (Some li, ai) # (Some ri, sepa) # drop (Suc (length lsi')) tsi'"
                      and r'="r'" and z="z"
and tsi''="zip (zip (subtrees
           (take (length lsi') tsi' @
            (Some li, ai) # (Some ri, sepa) # drop (Suc (length lsi')) tsi'))
      (zip (butlast
             (r' #
              take (length lsi') pointers @ newr # subnext # drop (Suc (length lsi')) pointers))
        (butlast
          ((take (length lsi') pointers @ newr # subnext # drop (Suc (length lsi')) pointers) @
           [z]))))
 (separators
   (take (length lsi') tsi' @
    (Some li, ai) # (Some ri, sepa) # drop (Suc (length lsi')) tsi'))"
                    ]
                thm R
              apply (sep_auto simp add: upd_drop_prepend eintros del: exI heap: R split!: prod.splits)
                subgoal
                proof (goal_cases)
                  case 1
                  from sym[OF 1(8)] have "lsi' = take (length lsi') (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))"
                    by auto
                  then show ?case using 1
                    by (auto simp add: take_zip take_map take_butlast_prepend take_butlast_append)
                qed
                subgoal 
                proof (goal_cases)
                  case 1
                  let ?tsi''="zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')"
                  from sym[OF 1(8)] have "rsi' = drop (Suc (length lsi')) ?tsi''"
                    by auto
                  moreover have "pointers ! length lsi' = subnext" 
                  proof -
                    let ?i = "length lsi'"
                    have "?tsi'' ! ?i = ((fst (tsi'!?i), (r' # pointers) ! ?i, pointers ! ?i), snd (tsi' ! ?i))"
                      using pointer_zip_access 1 by fastforce
                    moreover have "?tsi'' ! ?i = ((suba, subleaf, subnext), sepa)"
                      by (metis "1" nth_append_length)
                    ultimately show ?thesis by simp
                  qed
                  ultimately show ?case using 1
                    by (auto simp add: drop_zip drop_map drop_butlast Cons_nth_drop_Suc)
                qed
              subgoal 
                proof (goal_cases)
                  case 1
                  let ?tsi''="zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')"
                  let ?i = "length lsi'"
                  show ?thesis
                  proof -
                    let ?i = "length lsi'"
                    have "?tsi'' ! ?i = ((fst (tsi'!?i), (r' # pointers) ! ?i, pointers ! ?i), snd (tsi' ! ?i))"
                      using pointer_zip_access 1 by fastforce
                    moreover have "?tsi'' ! ?i = ((suba, subleaf, subnext), sepa)"
                      by (metis "1" nth_append_length)
                    ultimately have "(r'#pointers) ! ?i = subleaf"
                      by simp
                    then show ?thesis
                      using sym[OF append_take_drop_id, of pointers "length lsi'"]
                      using access_len_last[of r' "take (length lsi') pointers" "drop (length lsi') pointers"]
                      using 1
                      by simp
                  qed
                qed
                subgoal
                proof (goal_cases)
                  case 1
                  let ?tsi''="zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')"
                  let ?i = "length lsi'"
                  have "pointers ! ?i = subnext" 
                  proof -
                    have "?tsi'' ! ?i = ((fst (tsi'!?i), (r' # pointers) ! ?i, pointers ! ?i), snd (tsi' ! ?i))"
                      using pointer_zip_access 1 by fastforce
                    moreover have "?tsi'' ! ?i = ((suba, subleaf, subnext), sepa)"
                      by (metis "1" nth_append_length)
                    ultimately show ?thesis by simp
                  qed
                  moreover have "drop (length lsi') pointers \<noteq> []"
                    using "1" by auto
                  moreover have "pointers \<noteq> []"
                    using "1" by auto
                  ultimately show ?case
                    apply(auto simp add: Cons_nth_drop_Suc  last.simps)
                    apply(auto simp add: last_conv_nth)
                    by (metis Suc_to_right le_SucE)
                qed
              subgoal by auto
              subgoal by (sep_auto simp add: pure_def)
              done
            done
          done
        done
            subgoal
              using a_split by fastforce
            subgoal
                  proof (goal_cases)
                    case 1
                    then have *: "((suba, subleaf, subnext), sepa) = (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi')"
                      by (metis nth_append_length)
                    have **:"(zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi') = (((subtrees tsi')!(length lsi'), (butlast (r'#pointers))!(length lsi'), pointers!(length lsi')), (separators tsi')!(length lsi'))" 
                      using 1 by simp
                    then show ?case
                      using ** * 1
                      by simp
                  qed
                  subgoal by (auto dest!: mod_starD list_assn_len)
                  done
                subgoal
                  apply(rule hoare_triple_preI)
                    using Cons split_relation_alt[of ts ls "a#rs"] list_split
                    by (auto dest!: list_assn_len mod_starD)
                  done
      qed
    qed
  qed
declare last.simps[simp add] butlast.simps[simp add]

text "The imperative insert refines the abstract insert."

lemma insert\<^sub>i_rule:
  assumes "k > 0" "sorted_less (inorder t)" "sorted_less (leaves t)" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  insert\<^sub>i k x ti
  <\<lambda>u. bplustree_assn k (abs_split_set.insert k x t) u r z>\<^sub>t"
proof(cases "abs_split_set.ins k x t")
  case (T\<^sub>i x1)
  then show ?thesis
  unfolding insert\<^sub>i_def
   using assms
    by (sep_auto split!: btupi.splits heap: ins\<^sub>i_rule)
next
  case (Up\<^sub>i x21 x22 x23)
  then show ?thesis
  unfolding insert\<^sub>i_def
  using assms
  apply (sep_auto eintros del: exI split!: btupi.splits heap: ins\<^sub>i_rule)
  subgoal for x21a x22a x23a newr a b xa
  apply(inst_existentials a b x23a "[(Some x21a, x22a)]" "[((Some x21a, r, newr),x22a)]" "[newr]")
    apply (auto simp add: prod_assn_def)
    apply (sep_auto)
    done
  done
qed

text "The \"pure\" resulting rule follows automatically."
lemma insert\<^sub>i_rule':
  shows "<bplustree_assn (Suc k) t ti r z * \<up>(abs_split_set.invar_leaves (Suc k) t \<and> sorted_less (leaves t))>
  insert\<^sub>i (Suc k) x ti
  <\<lambda>ri.\<exists>\<^sub>Au. bplustree_assn (Suc k) u ri r z * \<up>(abs_split_set.invar_leaves (Suc k) u \<and> sorted_less (leaves u) \<and> leaves u = (ins_list x (leaves t)))>\<^sub>t"
  using Laligned_sorted_inorder[of t top] sorted_wrt_append
  using abs_split_set.insert_bal[of t] abs_split_set.insert_order[of "Suc k" t]
  using abs_split_set.insert_Linorder_top[of "Suc k" t]
  by (sep_auto heap: insert\<^sub>i_rule simp add: sorted_ins_list)


subsection "Deletion"

text "The below definitions work for non-linked-leaf B-Plus-Trees
but not yet for linked-leaf trees"


(* rebalance middle tree gets a list of trees, an index pointing to
the position of sub/sep and a last tree *)

definition rebalance_middle_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder,order_top}) btnode ref option \<times> 'a) pfarray \<Rightarrow> nat \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_middle_tree \<equiv> \<lambda> k tsi i p_ti. ( do {
  ti \<leftarrow> !p_ti;
  case ti of
  Btleaf txsi n_p \<Rightarrow> do {
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      subi \<leftarrow> !(the r_sub);
      l_sub \<leftarrow> pfa_length (vals subi);
      l_txs \<leftarrow> pfa_length (txsi);
      if l_sub \<ge> k \<and> l_txs \<ge> k then do {
        return (Btnode tsi p_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if i+1 = l_tsi then do {
          mts' \<leftarrow> pfa_extend_grow (vals subi) (txsi);
          (the r_sub) := Btleaf mts' n_p;
          res_node\<^sub>i \<leftarrow> Lnode\<^sub>i k (the r_sub);
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_shrink i tsi;
              return (Btnode tsi' u)
            } |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (Some l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          rsub \<leftarrow> !(the r_rsub);
          mts' \<leftarrow> pfa_extend_grow (vals subi) (vals rsub);
          (the r_sub) := Btleaf mts' (fwd rsub);
          res_node\<^sub>i \<leftarrow> Lnode\<^sub>i k (the r_sub);
          case res_node\<^sub>i of
           T\<^sub>i u \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some u,rsep);
            tsi'' \<leftarrow> pfa_delete tsi' (i+1);
            return (Btnode tsi'' p_ti)
          } |
           Up\<^sub>i l a r \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some l,a);
            tsi'' \<leftarrow> pfa_set tsi' (i+1) (Some r,rsep);
            return (Btnode tsi'' p_ti)
          }
        }
  }} |
  Btnode ttsi tti \<Rightarrow> do {
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      subi \<leftarrow> !(the r_sub);
      l_sub \<leftarrow> pfa_length (kvs subi);
      l_tts \<leftarrow> pfa_length (ttsi);
      if l_sub \<ge> k \<and> l_tts \<ge> k then do {
        return (Btnode tsi p_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if i+1 = l_tsi then do {
          mts' \<leftarrow> pfa_append_extend_grow (kvs subi) (Some (lst subi),sep) (ttsi);
          (the r_sub) := Btnode mts' (lst ti);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k (the r_sub);
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_shrink i tsi;
              return (Btnode tsi' u)
            } |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (Some l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          rsub \<leftarrow> !(the r_rsub);
          mts' \<leftarrow> pfa_append_extend_grow (kvs subi) (Some (lst subi),sep) (kvs rsub);
          (the r_sub) := Btnode mts' (lst rsub);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k (the r_sub);
          case res_node\<^sub>i of
           T\<^sub>i u \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some u,rsep);
            tsi'' \<leftarrow> pfa_delete tsi' (i+1);
            return (Btnode tsi'' p_ti)
          } |
           Up\<^sub>i l a r \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some l,a);
            tsi'' \<leftarrow> pfa_set tsi' (i+1) (Some r,rsep);
            return (Btnode tsi'' p_ti)
          }
        }
  }
}}
)
"


definition rebalance_last_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder,order_top}) btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_last_tree \<equiv> \<lambda>k tsi ti. do {
   l_tsi \<leftarrow> pfa_length tsi;
   rebalance_middle_tree k tsi (l_tsi-1) ti
}"


subsection "Refinement of the abstract B-tree operations"


lemma P_imp_Q_implies_P: "P \<Longrightarrow> (Q \<longrightarrow> P)"
  by simp



lemma btupi_assn_T: "h \<Turnstile> btupi_assn k (abs_split_set.node\<^sub>i k ts t) (T\<^sub>i x) r z \<Longrightarrow> abs_split_set.node\<^sub>i k ts t = abs_split_set.T\<^sub>i (Node ts t)"
  apply(auto simp add: abs_split_set.node\<^sub>i.simps dest!: mod_starD split!: list.splits prod.splits)
  done

lemma btupi_assn_Up: "h \<Turnstile> btupi_assn k (abs_split_set.node\<^sub>i k ts t) (Up\<^sub>i l a r) r' z \<Longrightarrow>
  abs_split_set.node\<^sub>i k ts t = (
    case BPlusTree_Split.split_half ts of (ls,rs) \<Rightarrow> (
      case last ls of (sub,sep) \<Rightarrow>
        abs_split_set.Up\<^sub>i (Node (butlast ls) sub) sep (Node rs t)
  )
)"
  apply(auto simp add: abs_split_set.node\<^sub>i.simps split!: list.splits prod.splits)
  done

lemma Lbtupi_assn_T: "h \<Turnstile> btupi_assn k (abs_split_set.Lnode\<^sub>i k ts) (T\<^sub>i x) r z \<Longrightarrow> abs_split_set.Lnode\<^sub>i k ts = abs_split_set.T\<^sub>i (Leaf ts)"
  apply(cases "length ts \<le> 2*k")
  apply(auto simp add: abs_split_set.Lnode\<^sub>i.simps split!: list.splits prod.splits)
  done

lemma Lbtupi_assn_Up: "h \<Turnstile> btupi_assn k (abs_split_set.Lnode\<^sub>i k ts) (Up\<^sub>i l a r) r' z \<Longrightarrow>
  abs_split_set.Lnode\<^sub>i k ts = (
    case BPlusTree_Split.split_half ts of (ls,rs) \<Rightarrow> (
      case last ls of sep \<Rightarrow>
        abs_split_set.Up\<^sub>i (Leaf ls) sep (Leaf rs)
  )
)"
  apply(auto simp add: abs_split_set.Lnode\<^sub>i.simps split!: list.splits prod.splits)
  done

lemma second_last_access:"(xs@a#b#ys) ! Suc(length xs) = b"
  by (simp add: nth_via_drop)

lemma second_last_update:"(xs@a#b#ys)[Suc(length xs) := c] = (xs@a#c#ys)"
  by (metis append.assoc append_Cons empty_append_eq_id length_append_singleton list_update_length)

lemma clean_heap:"\<lbrakk>(a, b) \<Turnstile> P \<Longrightarrow> Q; (a, b) \<Turnstile> P\<rbrakk> \<Longrightarrow> Q"
  by auto



partial_function (heap) del ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder,order_top}) btnode ref \<Rightarrow> 'a btnode ref Heap"
  where
    "del k x tp = do {
  ti \<leftarrow> !tp;
  (case ti of Btleaf xs np \<Rightarrow> do { 
      xs' \<leftarrow> del_list\<^sub>i x xs;
      tp := (Btleaf xs' np);
      return tp
} |
   Btnode tsi tti \<Rightarrow> do {
   i \<leftarrow> split\<^sub>i tsi x;
   tsl \<leftarrow> pfa_length tsi;
   if i < tsl then do {
       (sub,sep) \<leftarrow> pfa_get tsi i;
       sub' \<leftarrow> del k x (the sub);
       kvs' \<leftarrow> pfa_set tsi i (Some sub',sep);
       node' \<leftarrow> rebalance_middle_tree k kvs' i tti;
       tp := node';
       return tp
   } else do {
       t' \<leftarrow> del k x tti;
       node' \<leftarrow> rebalance_last_tree k tsi t';
       tp := node';
       return tp
    }
  })
}"


end

context split\<^sub>i_list
begin

definition isin_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> bool Heap"
  where "isin_list\<^sub>i x ks = do {
    i \<leftarrow> split\<^sub>i_list ks x;
    xsl \<leftarrow> pfa_length ks;
    if i \<ge> xsl then return False
    else do {
      sep \<leftarrow> pfa_get ks i;
      return (sep = x)
  }
}"

lemma isin_list\<^sub>i_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows
   "<is_pfa c ks (a',n')> 
    isin_list\<^sub>i x (a',n') 
  <\<lambda>b. 
    is_pfa c ks (a',n')
    * \<up>(b = abs_split_list.isin_list x ks)>\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      apply(subst isin_list\<^sub>i_def)
      using assms list_split apply(sep_auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
      done
  next
  case (Cons a rrs)
  then show ?thesis
      apply(subst isin_list\<^sub>i_def)
      using list_split apply simp
      using assms list_split  apply(sep_auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)
      done
  qed
qed

definition ins_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
  where "ins_list\<^sub>i x ks = do {
    i \<leftarrow> split\<^sub>i_list ks x;
    xsl \<leftarrow> pfa_length ks;
    if i \<ge> xsl then
      pfa_append_grow ks x
    else do {
      sep \<leftarrow> pfa_get ks i;
      if sep = x then
        return ks
      else
        pfa_insert_grow ks i x 
  }
}"

lemma ins_list\<^sub>i_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows
   "<is_pfa c ks (a',n')> 
    ins_list\<^sub>i x (a',n') 
  <\<lambda>(a'',n''). is_pfa (max c (length (abs_split_list.insert_list x ks))) (abs_split_list.insert_list x ks) (a'',n'')
    >\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      apply(subst ins_list\<^sub>i_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      using list_split apply (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    subgoal
      apply(simp add: is_pfa_def)
        apply(rule ent_ex_preI)
      subgoal for l
        apply(rule ent_ex_postI[where x="l"])
      using assms list_split apply(sep_auto simp add: split_relation_alt pure_def dest!: mod_starD list_assn_len)
      done
    done
    subgoal
      apply(simp add: is_pfa_def)
        apply(rule ent_ex_preI)
      subgoal for l
        apply(rule ent_ex_postI[where x="l"])
      using assms list_split apply(sep_auto simp add: split_relation_alt pure_def dest!: mod_starD list_assn_len)
      done
    done
  done
  next
  case (Cons a rrs)
  then show ?thesis
  proof (cases "a = x")
    case True
    then show ?thesis
      apply(subst ins_list\<^sub>i_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      prefer 2
      subgoal by (metis (no_types, lifting) id_assn_list list_split local.Cons mod_starD split_relation_access)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
        apply(subgoal_tac "max c (Suc (length ls + length rrs)) = c")
      subgoal using assms list_split by (sep_auto simp add: split_relation_alt  dest!: mod_starD id_assn_list)
          subgoal
            apply(auto simp add: is_pfa_def)
            by (metis add_Suc_right length_Cons length_append length_take max.absorb1 min_eq_arg(2))
      done
  next
    case False
    then show ?thesis
      apply(subst ins_list\<^sub>i_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal by (metis (no_types, lifting) id_assn_list list_split local.Cons mod_starD split_relation_access)
      apply vcg
      subgoal by (auto simp add: is_pfa_def)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    subgoal for _ _ _ _
        apply(subgoal_tac "(Suc (Suc (length ls + length rrs))) = Suc n'")
        subgoal
      using assms list_split Cons by (sep_auto simp add: split_relation_alt dest!: mod_starD id_assn_list)
      subgoal
        apply(auto simp add: is_pfa_def)
        by (metis add_Suc_right length_Cons length_append length_take min_eq_arg(2))
      done
    done
qed
qed
qed

definition del_list\<^sub>i:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
  where "del_list\<^sub>i x ks = do {
    i \<leftarrow> split\<^sub>i_list ks x;
    xsl \<leftarrow> pfa_length ks;
    if i \<ge> xsl then
      return ks
    else do {
      sep \<leftarrow> pfa_get ks i;
      if sep = x then
        pfa_delete ks i
      else
        return ks
  }
}"

lemma del_list\<^sub>i_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows "<is_pfa c ks (a',n')> 
    del_list\<^sub>i x (a',n') 
  <\<lambda>(a'',n''). is_pfa c (abs_split_list.delete_list x ks) (a'',n'')>\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      apply(subst del_list\<^sub>i_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      using list_split apply (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      done
  next
  case (Cons a rrs)
  then show ?thesis
  proof (cases "a = x")
    case True
    then show ?thesis
      apply(subst del_list\<^sub>i_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons apply (auto simp add: split_relation_alt is_pfa_def split!: prod.splits list.splits dest!: mod_starD list_assn_len)
        by (metis add_Suc_right length_Cons length_append length_take less_add_Suc1 min_eq_arg(2))
      prefer 2
      subgoal  by (simp add: list_split local.Cons split_relation_access)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      done
  next
    case False
    then show ?thesis
      apply(subst del_list\<^sub>i_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt is_pfa_def split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      subgoal by (simp add: list_split local.Cons split_relation_access)
      apply vcg
      using list_split Cons apply (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    done
    qed
  qed
qed

end

context split\<^sub>i_full
begin

sublocale split\<^sub>i_set split\<^sub>i_list.abs_split_list.isin_list split\<^sub>i_list.abs_split_list.insert_list 
  split\<^sub>i_list.abs_split_list.delete_list split split\<^sub>i split\<^sub>i_list.isin_list\<^sub>i split\<^sub>i_list.ins_list\<^sub>i split\<^sub>i_list.del_list\<^sub>i
  using split\<^sub>i_list.abs_split_list.isin_list_set split\<^sub>i_list.abs_split_list.insert_list_set split\<^sub>i_list.abs_split_list.delete_list_set
  apply unfold_locales 
  apply sep_auto +
  done

end


end

