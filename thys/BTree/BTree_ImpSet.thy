theory BTree_ImpSet
  imports
    BTree_Imp
    BTree_Set
begin

section "Imperative Set operations"

subsection "Auxiliary operations"

definition "split_relation xs \<equiv>
   \<lambda>(as,bs) i. i \<le> length xs \<and> as = take i xs \<and> bs = drop i xs"

lemma split_relation_alt:
  "split_relation as (ls,rs) i = (as = ls@rs \<and> i = length ls)"
  by (auto simp add: split_relation_def)


lemma split_relation_length: "split_relation xs (ls,rs) (length xs) = (ls = xs \<and> rs = [])"
  by (simp add: split_relation_def)

(* auxiliary lemmas on assns *)
(* simp? not sure if it always makes things more easy *)
lemma list_assn_prod_map: "list_assn (A \<times>\<^sub>a B) xs ys = list_assn B (map snd xs) (map snd ys) * list_assn A (map fst xs) (map fst ys)"
  apply(induct "(A \<times>\<^sub>a B)" xs ys rule: list_assn.induct)
     apply(auto simp add: ab_semigroup_mult_class.mult.left_commute ent_star_mono star_aci(2) star_assoc)
  done

(* concrete *)
lemma id_assn_list: "h \<Turnstile> list_assn id_assn (xs::'a list) ys \<Longrightarrow> xs = ys"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done


lemma snd_map_help:
  "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
  "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto


lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  by auto

lemma split_relation_map: "split_relation as (ls,rs) i \<Longrightarrow> split_relation (map f as) (map f ls, map f rs) i"
  apply(induction as arbitrary: ls rs i)
   apply(auto simp add: split_relation_def take_map drop_Cons')
  apply(metis list.simps(9) take_map)
  done

lemma split_relation_access: "\<lbrakk>split_relation as (ls,rs) i; rs = r#rrs\<rbrakk> \<Longrightarrow> as!i = r"
  by (simp add: split_relation_alt)



lemma index_to_elem_all: "(\<forall>j<length xs. P (xs!j)) = (\<forall>x \<in> set xs. P x)"
  by (simp add: all_set_conv_nth)

lemma index_to_elem: "n < length xs \<Longrightarrow> (\<forall>j<n. P (xs!j)) = (\<forall>x \<in> set (take n xs). P x)"
  by (simp add: all_set_conv_nth)
    (* ----------------- *)

definition split_half :: "('a::heap \<times> 'b::{heap}) pfarray \<Rightarrow> nat Heap"
  where
    "split_half a \<equiv> do {
  l \<leftarrow> pfa_length a;
  return (l div 2)
}"

lemma split_half_rule[sep_heap_rules]: "<
    is_pfa c tsi a
  * list_assn R ts tsi>
    split_half a
  <\<lambda>i.
      is_pfa c tsi a
    * list_assn R ts tsi
    * \<up>(i = length ts div 2 \<and>  split_relation ts (BTree_Set.split_half ts) i)>"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done

subsection "The imperative split locale"

text "This locale extends the abstract split locale,
assuming that we are provided with an imperative program
that refines the abstract split function."


locale imp_split = abs_split: BTree_Set.split split
  for split::
    "('a btree \<times> 'a::{heap,default,linorder}) list \<Rightarrow> 'a
       \<Rightarrow> ('a btree \<times> 'a) list \<times> ('a btree \<times> 'a) list" +
  fixes imp_split:: "('a btnode ref option \<times> 'a::{heap,default,linorder}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes imp_split_rule [sep_heap_rules]:"sorted_less (separators ts) \<Longrightarrow>
   <is_pfa c tsi (a,n)
  * blist_assn k ts tsi>
    imp_split (a,n) p
  <\<lambda>i.
    is_pfa c tsi (a,n)
    * blist_assn k ts tsi
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"
begin

subsection "Membership"

partial_function (heap) isin :: "'a btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
  where
    "isin p x =
  (case p of
     None \<Rightarrow> return False |
     (Some a) \<Rightarrow> do {
       node \<leftarrow> !a;
       i \<leftarrow> imp_split (kvs node) x;
       tsl \<leftarrow> pfa_length (kvs node);
       if i < tsl then do {
         s \<leftarrow> pfa_get (kvs node) i;
         let (sub,sep) = s in
         if x = sep then
           return True
         else
           isin sub x
       } else
           isin (last node) x
    }
)"

subsection "Insertion"


datatype 'b btupi =
  T\<^sub>i "'b btnode ref option" |
  Up\<^sub>i "'b btnode ref option" "'b" "'b btnode ref option"

fun btupi_assn where
  "btupi_assn k (abs_split.T\<^sub>i l) (T\<^sub>i li) =
   btree_assn k l li" |
  "btupi_assn k (abs_split.Up\<^sub>i l a r) (Up\<^sub>i li ai ri) =
   btree_assn k l li * id_assn a ai * btree_assn k r ri" |
  "btupi_assn _ _ _ = false"



definition node\<^sub>i :: "nat \<Rightarrow> ('a btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btupi Heap" where
  "node\<^sub>i k a ti \<equiv> do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      l \<leftarrow> ref (Btnode a' ti);
      return (T\<^sub>i (Some l))
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: ('a btnode ref option \<times> 'a) pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a i;
      b' \<leftarrow> pfa_drop a (i+1) b;
      a' \<leftarrow> pfa_shrink i a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      let (sub,sep) = m in do {
        l \<leftarrow> ref (Btnode a'' sub);
        r \<leftarrow> ref (Btnode b' ti);
        return (Up\<^sub>i (Some l) sep (Some r))
      }
    }
}"


partial_function (heap) ins :: "nat \<Rightarrow> 'a \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btupi Heap"
  where
    "ins k x apo = (case apo of
  None \<Rightarrow>
    return (Up\<^sub>i None x None) |
  (Some ap) \<Rightarrow> do {
    a \<leftarrow> !ap;
    i \<leftarrow> imp_split (kvs a) x;
    tsl \<leftarrow> pfa_length (kvs a);
    if i < tsl then do {
      s \<leftarrow> pfa_get (kvs a) i;
      let (sub,sep) = s in
      if sep = x then
        return (T\<^sub>i apo)
      else do {
        r \<leftarrow> ins k x sub;
        case r of
          (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set (kvs a) i (lp,sep);
            return (T\<^sub>i apo)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            pfa_set (kvs a) i (rp,sep);
            if tsl < 2*k then do {
                kvs' \<leftarrow> pfa_insert (kvs a) i (lp,x');
                ap := (Btnode kvs' (last a));
                return (T\<^sub>i apo)
            } else do {
              kvs' \<leftarrow> pfa_insert_grow (kvs a) i (lp,x');
              node\<^sub>i k kvs' (last a)
            }
          }
        }
      }
    else do {
      r \<leftarrow> ins k x (last a);
      case r of
        (T\<^sub>i lp) \<Rightarrow> do {
          ap := (Btnode (kvs a) lp);
          return (T\<^sub>i apo)
        } |
        (Up\<^sub>i lp x' rp) \<Rightarrow>
          if tsl < 2*k then do {
            kvs' \<leftarrow> pfa_append (kvs a) (lp,x');
            ap := (Btnode kvs' rp);
            return (T\<^sub>i apo)
          } else do {
            kvs' \<leftarrow> pfa_append_grow' (kvs a) (lp,x');
            node\<^sub>i k kvs' rp
        }
    }
  }
)"


(*fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a btree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)"

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a btree" where
  "insert k x t = tree\<^sub>i (ins k x t)"
*)

definition insert :: "nat \<Rightarrow> ('a::{heap,default,linorder}) \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option Heap" where
  "insert \<equiv> \<lambda>k x ti. do {
  ti' \<leftarrow> ins k x ti;
  case ti' of
     T\<^sub>i sub \<Rightarrow> return sub |
     Up\<^sub>i l a r \<Rightarrow> do {
        kvs \<leftarrow> pfa_init (2*k) (l,a) 1;
        t' \<leftarrow> ref (Btnode kvs r);
        return (Some t')
      }
}"

subsection "Deletion"

(* rebalance middle tree gets a list of trees, an index pointing to
the position of sub/sep and a last tree *)
definition rebalance_middle_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder}) btnode ref option \<times> 'a) pfarray \<Rightarrow> nat \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_middle_tree \<equiv> \<lambda> k tsi i r_ti. (
  case r_ti of
  None \<Rightarrow> do {
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      case r_sub of None \<Rightarrow>  return (Btnode tsi r_ti)
  } |
  Some p_t \<Rightarrow> do {
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      case r_sub of (Some p_sub) \<Rightarrow>  do {
      ti \<leftarrow> !p_t;
      sub \<leftarrow> !p_sub;
      l_sub \<leftarrow> pfa_length (kvs sub);
      l_tts \<leftarrow> pfa_length (kvs ti);
      if l_sub \<ge> k \<and> l_tts \<ge> k then do {
        return (Btnode tsi r_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if i+1 = l_tsi then do {
          mts' \<leftarrow> pfa_append_extend_grow (kvs sub) (last sub,sep) (kvs ti);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last ti);
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_shrink i tsi;
              return (Btnode tsi' u)
            } |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          case r_rsub of Some p_rsub \<Rightarrow> do {
            rsub \<leftarrow> !p_rsub;
            mts' \<leftarrow> pfa_append_extend_grow (kvs sub) (last sub,sep) (kvs rsub);
            res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last rsub);
            case res_node\<^sub>i of
             T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (u,rsep);
              tsi'' \<leftarrow> pfa_delete tsi' (i+1);
              return (Btnode tsi'' r_ti)
            } |
             Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (l,a);
              tsi'' \<leftarrow> pfa_set tsi' (i+1) (r,rsep);
              return (Btnode tsi'' r_ti)
            }
          }
        }
      }
  }
})
"


definition rebalance_last_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder}) btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_last_tree \<equiv> \<lambda>k tsi ti. do {
   l_tsi \<leftarrow> pfa_length tsi;
   rebalance_middle_tree k tsi (l_tsi-1) ti
}"


subsection "Refinement of the abstract B-tree operations"

definition empty ::"('a::{default,heap,linorder}) btnode ref option Heap"
  where "empty = return None"


lemma P_imp_Q_implies_P: "P \<Longrightarrow> (Q \<longrightarrow> P)"
  by simp


lemma  "sorted_less (inorder t) \<Longrightarrow>
   <btree_assn k t ti>
     isin ti x
   <\<lambda>r. btree_assn k t ti * \<up>(abs_split.isin t x = r)>\<^sub>t"
proof(induction t x arbitrary: ti rule: abs_split.isin.induct)
  case (1 x)
  then show ?case
    apply(subst isin.simps)
    apply (cases ti)
     apply (auto simp add: return_cons_rule)
    done
next
  case (2 ts t x)
  then obtain ls rs where list_split[simp]: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then show ?case
  proof (cases rs)
    (* NOTE: induction condition trivial here *)
    case [simp]: Nil
    show ?thesis
      apply(subst isin.simps)
      apply(sep_auto)
      using "2.prems" sorted_inorder_separators apply blast
      apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      apply(rule hoare_triple_preI)
      apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      done
  next
    case [simp]: (Cons h rrs)
    obtain sub sep where h_split[simp]: "h = (sub,sep)"
      by (cases h)
    show ?thesis
    proof (cases "sep = x")
      (* NOTE: no induction required here, only vacuous counter cases generated *)
      case [simp]: True
      then show ?thesis
        apply(simp split: list.splits prod.splits)
        apply(subst isin.simps)
        using "2.prems" sorted_inorder_separators apply(sep_auto)
         apply(rule hoare_triple_preI)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
        done
    next
      case [simp]: False
      show ?thesis
        apply(simp split: list.splits prod.splits)
        apply safe
        using False apply simp
        apply(subst isin.simps)
        using "2.prems" sorted_inorder_separators
        apply(sep_auto)
          (*eliminate vacuous case*)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!:  mod_starD list_assn_len)[]
          (* simplify towards induction step *)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]

(* NOTE show that z = (suba, sepa) *)
         apply(rule norm_pre_ex_rule)+
         apply(rule hoare_triple_preI)
        subgoal for p tsi n ti xsi suba sepa zs1 z zs2 _
          apply(subgoal_tac "z = (suba, sepa)", simp)
          using 2(3) apply(sep_auto
              heap:"2.IH"(2)[of ls rs h rrs sub sep]
              simp add: sorted_wrt_append)
          using list_split Cons h_split apply simp_all
            (* proof that previous assumptions hold later *)
           apply(rule P_imp_Q_implies_P)
           apply(rule ent_ex_postI[where x="(tsi,n)"])
           apply(rule ent_ex_postI[where x="ti"])
           apply(rule ent_ex_postI[where x="(zs1 @ (suba, sepa) # zs2)"])
           apply(rule ent_ex_postI[where x="zs1"])
           apply(rule ent_ex_postI[where x="z"])
           apply(rule ent_ex_postI[where x="zs2"])
           apply sep_auto
            (* prove subgoal_tac assumption *)
          apply (metis (no_types, lifting) list_assn_aux_ineq_len list_assn_len nth_append_length star_false_left star_false_right)
          done
            (* eliminate last vacuous case *)
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: mod_starD list_assn_len)[]
        done
    qed
  qed
qed

declare abs_split.node\<^sub>i.simps [simp add]

lemma node\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
  shows "<is_pfa c tsi (a,n) * list_assn ((btree_assn k) \<times>\<^sub>a id_assn) ts tsi * btree_assn k t ti>
  node\<^sub>i k (a,n) ti
  <\<lambda>r. btupi_assn k (abs_split.node\<^sub>i k ts t) r >\<^sub>t"
proof (cases "length ts \<le> 2 * k")
  case [simp]: True
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
       apply(sep_auto simp add: is_pfa_def)[]
    using c_cap apply(sep_auto simp add: is_pfa_def)[]
     apply(sep_auto  dest!: mod_starD list_assn_len)[]
    using True apply(sep_auto dest!: mod_starD list_assn_len)
    done
next
  note max.absorb1 [simp del] max.absorb2 [simp del] max.absorb3 [simp del] max.absorb4 [simp del]
  note min.absorb1 [simp del] min.absorb2 [simp del] min.absorb3 [simp del] min.absorb4 [simp del]
  case [simp]: False
  then obtain ls sub sep rs where
    split_half_eq: "BTree_Set.split_half ts = (ls,(sub,sep)#rs)"
    using abs_split.node\<^sub>i_cases by blast
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
       apply(sep_auto simp add:  split_relation_alt split_relation_length is_pfa_def dest!: mod_starD list_assn_len)
    using False apply(sep_auto simp add: split_relation_alt )
    using False  apply(sep_auto simp add: is_pfa_def)[]
    apply(sep_auto)[]
      apply(sep_auto simp add: is_pfa_def split_relation_alt)[]
    using c_cap apply(sep_auto simp add: is_pfa_def)[]
     apply(sep_auto)[]
    using c_cap apply(sep_auto simp add: is_pfa_def)[]
    using c_cap apply(simp)
    apply(vcg)
    apply(simp)
    apply(rule impI)
    subgoal for  _ _ _ _ rsa subi ba rn lsi al ar _
      thm ent_ex_postI
      thm ent_ex_postI[where x="take (length tsi div 2) tsi"]
        (* instantiate right hand side *)
      apply(rule ent_ex_postI[where x="(rsa,rn)"])
      apply(rule ent_ex_postI[where x="ti"])
      apply(rule ent_ex_postI[where x="(drop (Suc (length tsi div 2)) tsi)"])
      apply(rule ent_ex_postI[where x="lsi"])
      apply(rule ent_ex_postI[where x="subi"])
      apply(rule ent_ex_postI[where x="take (length tsi div 2) tsi"])
        (* introduce equality between equality of split tsi/ts and original lists *)
      apply(simp add: split_relation_alt)
      apply(subgoal_tac "tsi =
            take (length tsi div 2) tsi @ (subi, ba) # drop (Suc (length tsi div 2)) tsi")
       apply(rule back_subst[where a="blist_assn k ts (take (length tsi div 2) tsi @ (subi, ba) # (drop (Suc (length tsi div 2)) tsi))" and b="blist_assn k ts tsi"])
        apply(rule back_subst[where a="blist_assn k (take (length tsi div 2) ts @ (sub, sep) # rs)" and b="blist_assn k ts"])
         apply(subst list_assn_aux_append_Cons)
          apply sep_auto
         apply sep_auto
        apply simp
       apply simp
      apply(rule back_subst[where a="tsi ! (length tsi div 2)" and b="(subi, ba)"])
       apply(rule id_take_nth_drop)
       apply simp
      apply simp
      done
    done
qed
declare abs_split.node\<^sub>i.simps [simp del]


lemma node\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split.node\<^sub>i k ts t = abs_split.T\<^sub>i (Node ts t)"
  by (simp add: abs_split.node\<^sub>i.simps)


lemma node\<^sub>i_rule_app: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1\<rbrakk> \<Longrightarrow>
<is_pfa c (tsi' @ [(li, ai)]) (aa, al) *
   blist_assn k ls tsi' *
   btree_assn k l li *
   id_assn a ai *
   btree_assn k r ri> node\<^sub>i k (aa, al) ri
 <btupi_assn k (abs_split.node\<^sub>i k (ls @ [(l, a)]) r)>\<^sub>t"
proof -
  note node\<^sub>i_rule[of k c "(tsi' @ [(li, ai)])" aa al "(ls @ [(l, a)])" r ri]
  moreover assume "2*k \<le> c" "c \<le> 4*k+1"
  ultimately show ?thesis
    by (simp add: mult.left_assoc)
qed

lemma node\<^sub>i_rule_ins2: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ (li, ai) # (ri,a'i) # rsi) (aa, al) *
   blist_assn k ls lsi *
   btree_assn k l li *
   id_assn a ai *
   btree_assn k r ri *
   id_assn a' a'i *
   blist_assn k rs rsi *
   btree_assn k t ti> node\<^sub>i k (aa, al)
          ti <btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # (r,a') # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (li, ai) # (ri,a'i) # rsi)" aa al "(ls @ (l, a) # (r,a') # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed

lemma ins_rule:
  "sorted_less (inorder t) \<Longrightarrow> <btree_assn k t ti>
  ins k x ti
  <\<lambda>r. btupi_assn k (abs_split.ins k x t) r>\<^sub>t"
proof (induction k x t arbitrary: ti rule: abs_split.ins.induct)
  case (1 k x)
  then show ?case
    apply(subst ins.simps)
    apply (sep_auto simp add: pure_app_eq)
    done
next
  case (2 k x ts t)
  obtain ls rrs where list_split: "split ts x = (ls,rrs)"
    by (cases "split ts x")
  have [simp]: "sorted_less (separators ts)"
    using "2.prems" sorted_inorder_separators by simp
  have [simp]: "sorted_less (inorder t)"
    using "2.prems" sorted_inorder_induct_last by simp
  show ?case
  proof (cases rrs)
    case Nil
    then show ?thesis
    proof (cases "abs_split.ins k x t")
      case (T\<^sub>i a)
      then show ?thesis
        apply(subst ins.simps)
        apply(sep_auto)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' i tsin' _ sub sep
          apply(rule hoare_triple_preI)
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi'
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split T\<^sub>i apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
             apply sep_auto
            apply sep_auto
            done
          done
        done
    next
      case (Up\<^sub>i l a r)
      then show ?thesis
        apply(subst ins.simps)
        apply(sep_auto)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' i tsin' _ sub sep
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' i tsin'
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split Up\<^sub>i apply(sep_auto split!: list.splits
              simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
             apply sep_auto
            apply(rule hoare_triple_preI)
            apply(sep_auto)
              apply(auto dest!: mod_starD simp add: is_pfa_def)[]
             apply (sep_auto)
            subgoal for li ai ri (* no split case *)
              apply(subgoal_tac "length (ls @ [(l,a)]) \<le> 2*k")
               apply(simp add: node\<^sub>i_no_split)
               apply(rule ent_ex_postI[where x="(tsil,Suc tsin)"])
               apply(rule ent_ex_postI[where x="ri"])
               apply(rule ent_ex_postI[where x="tsi' @ [(li, ai)]"])
               apply(sep_auto)
              apply (sep_auto dest!: mod_starD list_assn_len simp add: is_pfa_def)
              done
                (* split case*)
            apply(sep_auto heap add: node\<^sub>i_rule_app)
            done
          done
        done
    qed
  next
    case (Cons a rs)
    obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then have [simp]: "sorted_less (inorder sub)"
      using "2.prems" abs_split.split_axioms list_split Cons sorted_inorder_induct_subtree split_def
      by fastforce
    then show ?thesis
    proof(cases "x = sep")
      case True
      show ?thesis
        apply(subst ins.simps)
        apply(sep_auto)
        subgoal for p tsil tsin tti tsi j subi
          using Cons list_split a_split True
          by sep_auto
        subgoal for p tsil tsin tti tsi j _ _ subi sepi
          apply(rule hoare_triple_preI)
          using Cons list_split a_split True
          apply(subgoal_tac "sepi = sep")
           apply (sep_auto simp add: split_relation_alt)
          apply(sep_auto simp add: list_assn_prod_map dest!: mod_starD id_assn_list)
          by (metis length_map snd_conv snd_map_help(2) split_relation_access)
        subgoal for p tsil tsin tti tsi j
          apply(rule hoare_triple_preI)
          using Cons list_split
          by (sep_auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
        done
    next
      case False
      then show ?thesis
      proof (cases "abs_split.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins.simps)
          apply vcg
           apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
           apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
             apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply (cases a, simp)
            apply(subgoal_tac "subi = suba", simp)
            using list_split a_split T\<^sub>i False
             apply (vcg heap: 2)
               apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
             apply vcg
              apply simp
             apply vcg
             apply simp
            subgoal for a'i q r
              apply(rule impI)
              apply(simp add: list_assn_append_Cons_left)
              apply(rule ent_ex_postI[where x="(tsil,tsin)"])
              apply(rule ent_ex_postI[where x="ti"])
              apply(rule ent_ex_postI[where x="(zs1 @ (a'i, sepi) # zs2)"])
              apply(rule ent_ex_postI[where x="zs1"])
              apply(rule ent_ex_postI[where x="(a'i,sep)"])
              apply(rule ent_ex_postI[where x="zs2"])
              apply sep_auto
               apply (simp add: pure_app_eq)
              apply(sep_auto dest!:  mod_starD list_assn_len)[]
              done
            apply (metis list_assn_aux_ineq_len Pair_inject list_assn_len nth_append_length star_false_left star_false_right)
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins.simps)
          apply vcg
           apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
           apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
             apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply(subgoal_tac "subi = suba", simp)
            thm 2(2)[of ls rrs a rs sub sep]
            using list_split a_split Cons Up\<^sub>i False
             apply (sep_auto heap: 2(2))
             apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
              apply vcg
               apply simp
            subgoal for li wi ri u (* no split case *)
              apply (cases u,simp)
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
                apply (simp add: is_pfa_def)[]
                apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
               apply(simp add: is_pfa_def)
               apply (metis add_Suc_right length_Cons length_append length_take min.absorb2)
              apply(sep_auto split: prod.splits  dest!: mod_starD list_assn_len)[]
                (* no split case *)
              apply(subgoal_tac "length (ls @ [(l,w)]) \<le> 2*k")
               apply(simp add: node\<^sub>i_no_split)
               apply(rule ent_ex_postI[where x="(tsil,Suc tsin)"])
               apply(rule ent_ex_postI[where x="ti"])
               apply(rule ent_ex_postI[where x="(zs1 @ (li, wi) # (ri, sep) # zs2)"])
               apply(sep_auto dest!: mod_starD list_assn_len)
              apply (sep_auto dest!: mod_starD list_assn_len simp add: is_pfa_def)
              done
             apply vcg
              apply simp
            subgoal for x21 x22 x23 u (* split case *)
              apply (cases u,simp)
              thm pfa_insert_grow_rule[where ?l="((zs1 @ (suba, sepi) # zs2)[length ls := (x23, sepa)])"]
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
               apply (simp add: is_pfa_def)[]
               apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
              apply(auto split: prod.splits  dest!: mod_starD list_assn_len)[]

              apply (vcg heap: node\<^sub>i_rule_ins2)
                 apply simp
                apply simp
               apply simp
              apply sep_auto
              done
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      qed
    qed
  qed
qed

text "The imperative insert refines the abstract insert."

lemma insert_rule:
  assumes "k > 0" "sorted_less (inorder t)"
  shows "<btree_assn k t ti>
  insert k x ti
  <\<lambda>r. btree_assn k (abs_split.insert k x t) r>\<^sub>t"
  unfolding insert_def
  apply(cases "abs_split.ins k x t")
   apply(sep_auto split!: btupi.splits heap: ins_rule[OF assms(2)])
  using assms
  apply(vcg heap: ins_rule[OF assms(2)])
  apply(simp split!: btupi.splits)
  apply(vcg)
   apply auto[]
  apply vcg
  apply auto[]
  subgoal for l a r li ai ri tsa tsn ti
    apply(rule ent_ex_postI[where x="(tsa,tsn)"])
    apply(rule ent_ex_postI[where x="ri"])
    apply(rule ent_ex_postI[where x="[(li, ai)]"])
    apply sep_auto
    done
  done

text "The \"pure\" resulting rule follows automatically."
lemma insert_rule':
  shows "<btree_assn (Suc k) t ti * \<up>(abs_split.invar_inorder (Suc k) t \<and> sorted_less (inorder t))>
  insert (Suc k) x ti
  <\<lambda>ri.\<exists>\<^sub>Ar. btree_assn (Suc k) r ri * \<up>(abs_split.invar_inorder (Suc k) r \<and> sorted_less (inorder r) \<and> inorder r = (ins_list x (inorder t)))>\<^sub>t"
  using abs_split.insert_bal abs_split.insert_order abs_split.insert_inorder
  by (sep_auto heap: insert_rule simp add: sorted_ins_list)

lemma list_update_length2 [simp]:
  "(xs @ x # y # ys)[Suc (length xs) := z] = (xs @ x # z # ys)"
  by (induct xs, auto)


lemma node\<^sub>i_rule_ins: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ (li, ai) # rsi) (aa, al) *
   blist_assn k ls lsi *
   btree_assn k l li *
   id_assn a ai *
   blist_assn k rs rsi *
   btree_assn k t ti>
     node\<^sub>i k (aa, al) ti
 <btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (li, ai) # rsi)" aa al "(ls @ (l, a) # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed

lemma btupi_assn_T: "h \<Turnstile> btupi_assn k (abs_split.node\<^sub>i k ts t) (T\<^sub>i x) \<Longrightarrow> abs_split.node\<^sub>i k ts t = abs_split.T\<^sub>i (Node ts t)"
  apply(auto simp add: abs_split.node\<^sub>i.simps dest!: mod_starD split!: list.splits)
  done

lemma btupi_assn_Up: "h \<Turnstile> btupi_assn k (abs_split.node\<^sub>i k ts t) (Up\<^sub>i l a r) \<Longrightarrow>
  abs_split.node\<^sub>i k ts t = (
    case BTree_Set.split_half ts of (ls, (sub,sep)#rs) \<Rightarrow>
      abs_split.Up\<^sub>i (Node ls sub) sep (Node rs t))"
  apply(auto simp add: abs_split.node\<^sub>i.simps dest!: mod_starD split!: list.splits)
  done

lemma second_last_access:"(xs@a#b#ys) ! Suc(length xs) = b"
  by (simp add: nth_via_drop)

lemma pfa_assn_len:"h \<Turnstile> is_pfa k ls (a,n) \<Longrightarrow> n \<le> k \<and> length ls = n"
  by (auto simp add: is_pfa_def)

(*declare "impCE"[rule del]*)
lemma rebalance_middle_tree_rule:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "i = length ls"
  shows "<is_pfa (2*k) tsi (a,n) * blist_assn k (ls@(sub,sep)#rs) tsi * btree_assn k t ti>
  rebalance_middle_tree k (a,n) i ti
  <\<lambda>r. btnode_assn k (abs_split.rebalance_middle_tree k ls sub sep rs t) r >\<^sub>t"
  apply(simp add: list_assn_append_Cons_left)
  apply(rule norm_pre_ex_rule)+
proof(goal_cases)
  case (1 lsi z rsi)
  then show ?case
  proof(cases z)
    case z_split: (Pair subi sepi)
    then show ?thesis
    proof(cases sub)
      case sub_leaf[simp]: Leaf
      then have t_leaf[simp]: "t = Leaf" using assms
        by (cases t) auto
      show ?thesis
        apply (subst rebalance_middle_tree_def)
        apply (rule hoare_triple_preI)
        apply (vcg)
        using assms apply (auto dest!: mod_starD list_assn_len split!: option.splits)
        apply (vcg)
        apply (auto dest!: mod_starD list_assn_len split!: option.splits)
        apply (rule ent_ex_postI[where x=tsi])
        apply sep_auto
        done
    next
      case sub_node[simp]: (Node mts mt)
      then obtain tts tt where t_node[simp]: "t = Node tts tt" using assms
        by (cases t) auto
      then show ?thesis
      proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
        case True
        then show ?thesis
          apply(subst rebalance_middle_tree_def)
          apply(rule hoare_triple_preI)
          apply(sep_auto dest!: mod_starD)
          using assms apply (auto  dest!: list_assn_len)[]

          using assms apply(sep_auto  split!: prod.splits)
          using assms apply (auto simp del: height_btree.simps dest!: mod_starD list_assn_len)[]
          using z_split apply(auto)[]
          subgoal for _ _ _ _ _ _ _ _ tp tsia' tsin' _ _  _ _ _ _ _ _ _ _ tsia tsin tti ttsi sepi subp
            apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
            apply(vcg)
             apply(auto)[]
             apply(rule ent_ex_postI[where x="lsi@(Some subp, sepi)#rsi"])
             apply(rule ent_ex_postI[where x="(tsia, tsin)"])
             apply(rule ent_ex_postI[where x="tti"])
             apply(rule ent_ex_postI[where x=ttsi])
             apply(sep_auto)[]
            apply(rule hoare_triple_preI)
            using True apply(auto dest!: mod_starD list_assn_len)
            done
          done
      next
        case False
        then show ?thesis
        proof(cases rs)
          case Nil
          then show ?thesis
            apply(subst rebalance_middle_tree_def)
            apply(rule hoare_triple_preI)
            apply(sep_auto dest!: mod_starD)
            using assms apply (auto  dest!: list_assn_len)[]

             apply(sep_auto  split!: prod.splits)
            using assms apply (auto simp del: height_btree.simps dest!: mod_starD list_assn_len)[]
            using z_split apply(auto)[]
            subgoal for _ _ _ _ _ _ _ _ tp tsia' tsin' _ _  _ _ _ _ _ _ _ _ tsia tsin tti ttsi
              apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
              apply(vcg)
              using False apply(auto dest!: mod_starD list_assn_len)
              done
            apply(sep_auto dest!: mod_starD)
            using assms apply (auto dest!: list_assn_len)[]
            using assms apply (auto dest!: list_assn_len)[]
            apply(sep_auto)
            using assms apply (auto dest!: list_assn_len mod_starD)[]
            using assms apply (auto dest!: list_assn_len mod_starD)[]
              (* Issue: we do not know yet what  'subp is pointing at *)
            subgoal for _ _ _ _ _ _ tp tsia tsin tti ttsi _ _ _ _ _ _ _ _ tsia' tsin' tti' tsi' subi sepi subp
              apply(subgoal_tac "z = (subi, sepi)")
               prefer 2
               apply (metis assms(3) list_assn_len nth_append_length)
              apply simp
              apply(vcg)
              subgoal
                (* still the "IF" branch *)
                apply(rule entailsI)
                  (* solves impossible case*)
                using False apply (auto dest!: list_assn_len mod_starD)[]
                done
              apply (auto del: impCE)
              apply(thin_tac "_ \<Turnstile> _")+
              apply(rule hoare_triple_preI)
                (* for each possible combination of \<le> and \<not>\<le>, a subgoal is created *)
              apply(sep_auto heap add: node\<^sub>i_rule_ins dest!: mod_starD del: impCE)
                 apply (auto dest!: pfa_assn_len)[]
                apply (auto dest!: pfa_assn_len list_assn_len)[]
              subgoal
                apply(thin_tac "_ \<Turnstile> _")+
                apply(rule hoare_triple_preI)
                apply(sep_auto split!: btupi.splits del: impCE)
                 apply(auto dest!: btupi_assn_T mod_starD del: impCE)[]
                 apply(rule ent_ex_postI[where x="lsi"])
                 apply sep_auto
                apply (sep_auto del: impCE)
                apply(auto dest!: btupi_assn_Up mod_starD split!: list.splits del: impCE)[]
                subgoal for li ai ri
                  apply(rule ent_ex_postI[where x="lsi @ [(li, ai)]"])
                  apply sep_auto
                  done
                done
              apply (sep_auto del: impCE)
              using assms apply(auto dest!: pfa_assn_len list_assn_len mod_starD)[]
              using assms apply(auto dest!: pfa_assn_len list_assn_len mod_starD)[]
              done
            done
        next
          case (Cons rss rrs)
          then show ?thesis
            apply(subst rebalance_middle_tree_def)
            apply(rule hoare_triple_preI)
            apply(sep_auto dest!: mod_starD)
            using assms apply (auto  dest!: list_assn_len)[]

             apply(sep_auto  split!: prod.splits)
            using assms apply (auto simp del: height_btree.simps dest!: mod_starD list_assn_len)[]
             apply(auto)[]
            subgoal for _ _ _ _ _ _ _ _ tp tsia' tsin' _ _  _ _ _ _ _ _ _ _ tsia tsin tti ttsi
              apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
              apply(vcg)
              using False apply(auto dest!: mod_starD list_assn_len)
              done
            apply(sep_auto dest!: mod_starD del: impCE)
            using assms apply (auto dest!: list_assn_len)[]
            apply(sep_auto del: impCE)
            using assms apply (auto dest!: list_assn_len mod_starD)[]
              (* Issue: we do not know yet what  'xa' is pointing at *)
            subgoal for list_heap1 list_heap2 _ _ _ _ _ _ tp ttsia' ttsin' tti' ttsi' _ _ _ _ _ _ _ _ ttsia ttsin tti ttsi subi sepi subp
              apply(subgoal_tac "z = (subi, sepi)")
               prefer 2
               apply (metis assms(3) list_assn_len nth_append_length)
              apply simp
              apply(vcg)
              subgoal
                (* still the "IF" branch *)
                apply(rule entailsI)
                  (* solves impossible case*)
                using False apply (auto dest!: list_assn_len mod_starD)[]
                done
              apply simp
              subgoal for subtsi subti subts ti subi subtsl ttsl
                (* TODO different nodei rule here *)
                supply R = node\<^sub>i_rule_ins[where k=k and c="(max (2 * k) (Suc (_ + ttsin)))" and lsi=subts]
                thm R
                apply(cases subtsi)
                apply(sep_auto heap add: R pfa_append_extend_grow_rule dest!: mod_starD del: impCE)
                  (* all of these cases are vacuous *)
                using assms apply (auto dest!: list_assn_len pfa_assn_len)[]
                using assms apply (auto dest!: list_assn_len pfa_assn_len)[]
                using assms apply (auto dest!: list_assn_len pfa_assn_len)[]
                apply(sep_auto split!: btupi.splits del: impCE)
                using assms apply (auto dest!: list_assn_len pfa_assn_len)[]
                apply(thin_tac "_ \<Turnstile> _")+
                apply(rule hoare_triple_preI)
                apply (cases rsi)
                 apply(auto dest!: list_assn_len mod_starD)[]
                  (* TODO avoid creating subgoals here but still split the heap? do we need to do that anyways *)
                subgoal for subtsa subtsn mtsa mtsn mtt mtsi _ _ _ _ _ _ _ _ rsubsep _ rrsi rssi
                  (* ensuring that the tree to the right is not none *)
                  apply (cases rsubsep)
                  apply(subgoal_tac "rsubsep = rrsi")
                   prefer 2
                  using assms apply(auto dest!: list_assn_len mod_starD del: impCE simp add: second_last_access)[]
                  apply (simp add: prod_assn_def)
                  apply(cases rss)
                  apply simp
                  subgoal for rsubi rsepi rsub rsep
                    apply(subgoal_tac "height rsub \<noteq> 0")
                     prefer 2
                    using assms apply(auto)[]
                    apply(cases rsubi; cases rsub)
                       apply simp+
                      (* now we may proceed *)
                    apply (vcg (ss))
                    apply (vcg (ss))
                    apply (vcg (ss))
                     apply (vcg (ss))
                    apply (vcg (ss))
                    subgoal for rsubi rsubts rsubt rsubtsi' rsubti rsubtsi subnode
                      apply(cases "kvs subnode")
                      apply (vcg (ss))
                      apply (vcg (ss))
                      apply (vcg (ss))
                      apply (vcg (ss))
                       apply (vcg (ss))
                      subgoal for _ rsubtsn subtsmergedi
                        apply (cases subtsmergedi)
                        apply simp
                        apply (vcg (ss))
                        subgoal for subtsmergeda _
                          supply R = node\<^sub>i_rule_ins[where
                              k=k and
                              c="max (2*k) (Suc (subtsn + rsubtsn))" and
                              ls="mts" and
                              al="Suc (subtsn+rsubtsn)" and
                              aa=subtsmergeda and
                              ti=rsubti and
                              rsi=rsubtsi and
                              li=subti and a=sep and ai=sep
                              ]
                          thm R
                          apply(rule P_imp_Q_implies_P)
                          apply(auto del: impCE dest!: mod_starD list_assn_len)[]
                          apply(rule hoare_triple_preI)
                          apply(subgoal_tac "subtsn \<le> 2*k \<and> rsubtsn \<le> 2*k")
                           prefer 2
                           apply (auto simp add: is_pfa_def)[]
                          apply (sep_auto heap add: R del: impCE)
                          apply(sep_auto split!: btupi.splits del: impCE)
                          using assms apply(auto  dest!: mod_starD list_assn_len)[]
                           apply(sep_auto del: impCE)
                          using assms apply(auto  dest!: mod_starD list_assn_len pfa_assn_len del: impCE)[]
                           apply(thin_tac "_ \<Turnstile> _")+
                           apply(rule hoare_triple_preI)
                           apply (drule btupi_assn_T mod_starD | erule conjE exE)+
                           apply vcg
                           apply simp
                          subgoal for rsubtsi ai tsian
                            apply(cases tsian)
                            apply simp
                            apply(rule P_imp_Q_implies_P)
                            apply(rule ent_ex_postI[where x="lsi @ (ai, rsep) # rssi"])
                            apply(rule ent_ex_postI[where x="(ttsia, ttsin)"])
                            apply(rule ent_ex_postI[where x="tti"])
                            apply(rule ent_ex_postI[where x="ttsi"])
                            using assms apply (sep_auto dest!: list_assn_len)
                            done
                          subgoal for _ _ rsubp rsubtsa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  li ai ri
                            apply(sep_auto del: impCE)
                            using assms apply(auto dest!: list_assn_len)[]
                            apply(sep_auto del: impCE)
                            using assms apply(auto dest!: list_assn_len)[]
                            apply(thin_tac "_ \<Turnstile> _")+
                            apply(rule hoare_triple_preI)
                            apply (drule btupi_assn_Up mod_starD | erule conjE exE)+
                            apply vcg
                              (* generates two identical subgoals ? *)
                            apply(simp split!: list.split)
                             apply(rule ent_ex_postI[where x="(lsi @ (li, ai) # (ri, rsepi) # rssi)"])
                             apply(rule ent_ex_postI[where x="(ttsia, ttsin)"])
                             apply(rule ent_ex_postI[where x="tti"])
                             apply(rule ent_ex_postI[where x="ttsi"])
                            using assms apply (sep_auto dest!: list_assn_len)
                            apply(rule ent_ex_postI[where x="(lsi @ (li, ai) # (ri, rsepi) # rssi)"])
                            apply(rule ent_ex_postI[where x="(ttsia, ttsin)"])
                            apply(rule ent_ex_postI[where x="tti"])
                            apply(rule ent_ex_postI[where x="ttsi"])
                            using assms apply (sep_auto dest!: list_assn_len)
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            done
        qed
      qed
    qed
  qed
qed

lemma rebalance_last_tree_rule:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "<is_pfa (2*k) tsi tsia * blist_assn k ts tsi * btree_assn k t ti>
  rebalance_last_tree k tsia ti
  <\<lambda>r. btnode_assn k (abs_split.rebalance_last_tree k ts  t) r >\<^sub>t"
  apply(subst rebalance_last_tree_def)
  apply(rule hoare_triple_preI)
  using assms apply(auto dest!: mod_starD)
  apply(subgoal_tac "length tsi - Suc 0 = length list")
   prefer 2
   apply(auto dest!: list_assn_len)[]
  using assms apply(sep_auto)
  supply R = rebalance_middle_tree_rule[where
      ls="list" and
      rs="[]" and
      i="length tsi - 1", simplified]
  apply(cases tsia)
  using R by blast

partial_function (heap) split_max ::"nat \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> ('a btnode ref option \<times> 'a) Heap"
  where
    "split_max k r_t = (case r_t of Some p_t \<Rightarrow> do {
   t \<leftarrow> !p_t;
   (case (last t) of None \<Rightarrow> do {
      (sub,sep) \<leftarrow> pfa_last (kvs t);
      tsi' \<leftarrow> pfa_butlast (kvs t);
      p_t := Btnode tsi' sub;
      return (Some p_t, sep)
  } |
    Some x \<Rightarrow> do {
      (sub,sep) \<leftarrow> split_max k (Some x);
      p_t' \<leftarrow> rebalance_last_tree k (kvs t) sub;
      p_t := p_t';
      return (Some p_t, sep)
  })
})
"


declare  abs_split.split_max.simps [simp del] abs_split.rebalance_last_tree.simps [simp del] height_btree.simps [simp del]

lemma split_max_rule:
  assumes "abs_split.nonempty_lasttreebal t"
    and "t \<noteq> Leaf"
  shows "<btree_assn k t ti>
  split_max k ti
  <((btree_assn k) \<times>\<^sub>a id_assn) (abs_split.split_max k t)>\<^sub>t"
  using assms
proof(induction k t arbitrary: ti rule: abs_split.split_max.induct)
  case (2 Leaf)
  then show ?case by auto
next
  case (1 k ts tt)
  then show ?case
  proof(cases tt)
    case Leaf
    then show ?thesis
      apply(subst split_max.simps)
      apply (vcg)
      using assms apply auto[]
      apply (vcg (ss))
      apply simp
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
        apply(rule hoare_triple_preI)
        apply (vcg (ss))
      using 1 apply(auto dest!: mod_starD)[]
       apply (vcg (ss))
       apply (vcg (ss))
       apply (vcg (ss))
       apply (vcg (ss))
       apply (vcg (ss))
      subgoal for tp tsi tti tsi' tnode subsep sub sep
        apply(cases tsi)
        apply(rule hoare_triple_preI)
        apply (vcg)
        apply(auto simp add: prod_assn_def abs_split.split_max.simps split!: prod.splits)
        subgoal for tsia tsin _ _ tsin' lastsep lastsub
          apply(rule ent_ex_postI[where x="(tsia, tsin')"])
          apply(rule ent_ex_postI[where x="sub"])
          apply(rule ent_ex_postI[where x="(butlast tsi')"])
          using 1 apply (auto dest!: mod_starD simp add: list_assn_append_Cons_left)
          apply sep_auto
          done
        done
      apply(sep_auto)
      done
  next
    case (Node tts ttt)
    have IH_help: "abs_split.nonempty_lasttreebal tt \<Longrightarrow>
tt \<noteq> Leaf \<Longrightarrow>
<btree_assn k (Node tts ttt) (Some ttp)> split_max k (Some ttp) <(btree_assn k \<times>\<^sub>a id_assn) (abs_split.split_max k tt)>\<^sub>t"
      for ttp
      using "1.IH" Node by blast
    obtain butlasttts l_sub l_sep where ts_split:"tts = butlasttts@[(l_sub, l_sep)]"
      using 1 Node by auto
    from Node show ?thesis
      apply(subst split_max.simps)
      apply (vcg)
      using 1 apply auto[]
      apply (vcg (ss))
      apply simp
      apply (vcg (ss))
      apply (vcg (ss))
       apply (vcg (ss))
      apply (vcg (ss))
      apply (vcg (ss))
      apply (vcg (ss))
      apply (vcg (ss))
       apply (vcg (ss))
      using 1 apply(auto dest!: mod_starD)[]
      apply (vcg (ss))
      subgoal for tp tsi tti tsi' tnode ttp
        using "1.prems" apply (vcg heap add: IH_help)
          apply simp
         apply simp
        apply(subst prod_assn_def)
        apply(cases "abs_split.split_max k tt")
        apply (auto simp del: abs_split.split_max.simps abs_split.rebalance_last_tree.simps height_btree.simps)[]
        subgoal for ttsubi ttmaxi ttsub ttmax butlasttsi' lasttssubi butlastts lasttssub lasttssepi lasttssep
          apply(rule hoare_triple_preI)
          supply R = rebalance_last_tree_rule[where k=k and tsia=tsi and ti=ttsubi and t=ttsub and tsi=tsi' and ts=" (butlasttsi' @ [(lasttssubi, lasttssepi)])"
              and list=butlasttsi' and sub=lasttssubi and sep=lasttssepi]
          thm R
          using ts_split
            (*TODO weird post conditions... *)
          apply (sep_auto heap add: R
              simp del: abs_split.split_max.simps abs_split.rebalance_last_tree.simps height_btree.simps
              dest!: mod_starD)
            apply (metis abs_split.nonempty_lasttreebal.simps(2) abs_split.split_max_height btree.distinct(1))
           apply simp
          apply(rule hoare_triple_preI)
          apply (simp add: prod_assn_def)
          apply vcg
          apply(subst abs_split.split_max.simps)
          using "1.prems" apply(auto dest!: mod_starD split!: prod.splits btree.splits)
          subgoal for _ _ _ _ _ _ _ _ _ _ tp'
            apply(cases "abs_split.rebalance_last_tree k (butlasttsi' @ [(lasttssubi, lasttssepi)]) ttsub"; cases tp')
             apply auto
            apply(rule ent_ex_preI)
            subgoal for _ _ tsia' tsin' tt' _ tsi'
              apply(rule ent_ex_postI[where x="(tsia', tsin')"])
              apply(rule ent_ex_postI[where x="tt'"])
              apply(rule ent_ex_postI[where x="tsi'"])
              apply sep_auto
              done
            done
          done
        done
      done
  qed
qed

partial_function (heap) del ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> 'a btnode ref option Heap"
  where
    "del k x ti = (case ti of None \<Rightarrow> return None |
   Some p \<Rightarrow> do {
   node \<leftarrow> !p;
   i \<leftarrow> imp_split (kvs node) x;
   tsl \<leftarrow> pfa_length (kvs node);
   if i < tsl then do {
     (sub,sep) \<leftarrow> pfa_get (kvs node) i;
     if sep \<noteq> x then do {
       sub' \<leftarrow> del k x sub;
       kvs' \<leftarrow> pfa_set (kvs node) i (sub',sep);
       node' \<leftarrow> rebalance_middle_tree k kvs' i (last node);
       p := node';
       return (Some p)
      }
     else if sub = None then do{
       kvs' \<leftarrow> pfa_delete (kvs node) i;
       p := (Btnode kvs' (last node));
       return (Some p)
     }
     else do {
        sm \<leftarrow> split_max k sub;
        kvs' \<leftarrow> pfa_set (kvs node) i sm;
        node' \<leftarrow> rebalance_middle_tree k kvs' i (last node);
        p := node';
        return (Some p)
     }
   } else do {
       t' \<leftarrow> del k x (last node);
       node' \<leftarrow> rebalance_last_tree k (kvs node) t';
       p := node';
       return (Some p)
    }
})"

lemma rebalance_middle_tree_update_rule:
  assumes "height tt = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height tt | [] \<Rightarrow> True"
    and "i = length ls"
  shows "<is_pfa (2 * k) (zs1 @ (x', sep) # zs2) a * btree_assn k sub x' *
     blist_assn k ls zs1 *
     id_assn sep sep *
     blist_assn k rs zs2 *
     btree_assn k tt ti>
  rebalance_middle_tree k a i ti
   <btnode_assn k (abs_split.rebalance_middle_tree k ls sub sep rs tt)>\<^sub>t"
proof (cases a)
  case [simp]: (Pair a n)
  note R=rebalance_middle_tree_rule[of tt sub rs i ls k "zs1@(x', sep)#zs2" a n sep ti]
  show ?thesis
    apply(rule hoare_triple_preI)
    using R assms apply (sep_auto dest!: mod_starD list_assn_len simp add: prod_assn_def)
    using assn_times_assoc star_aci(3) by auto
qed

lemma del_rule:
  assumes "bal t" and "sorted (inorder t)" and "root_order k t" and "k > 0"
  shows "<btree_assn k t ti>
  del k x ti
  <btree_assn k (abs_split.del k x t)>\<^sub>t"
  using assms
proof (induction k x t arbitrary: ti rule: abs_split.del.induct)
  case (1 k x)
  then show ?case
    apply(subst del.simps)
    apply sep_auto
    done
next
  case (2 k x ts tt ti)
  obtain ls rs where split_ts[simp]: "split ts x = (ls, rs)"
    by (cases "split ts x")
  obtain tss lastts_sub lastts_sep where last_ts: "ts = tss@[(lastts_sub, lastts_sep)]"
    using "2.prems"  apply auto
    by (metis abs_split.isin.cases neq_Nil_rev_conv)
  show ?case
  proof(cases "rs")
    case Nil
    then show ?thesis
      apply(subst del.simps)
      apply sep_auto
      using "2.prems"(2) sorted_inorder_separators apply blast
      apply(rule hoare_triple_preI)
      apply (sep_auto)
      using Nil  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
      using Nil  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
      using Nil  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
      apply (sep_auto heap add: "2.IH"(1))
      using "2.prems" apply (auto dest!: mod_starD)[]
      using "2.prems" apply (auto dest!: mod_starD simp add: sorted_wrt_append)[]
      using "2.prems" order_impl_root_order apply (auto dest!: mod_starD)[]
      using "2.prems" apply (auto)[]
      subgoal for tp tsia tsin tti tsi i _ _ tti'
        apply(rule hoare_triple_preI)
        supply R = rebalance_last_tree_rule[where t="(abs_split.del k x tt)" and ti=tti' and ts=ts and sub=lastts_sub
            and list=tss and sep=lastts_sep]
        thm R
        using last_ts apply(sep_auto heap add: R)
        using "2.prems" abs_split.del_height[of k tt x] order_impl_root_order[of k tt] apply (auto dest!: mod_starD)[]
         apply simp
        apply(rule hoare_triple_preI)
        apply (sep_auto)
        apply(cases "abs_split.rebalance_last_tree k ts (abs_split.del k x tt)")
         apply(auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
        subgoal for tnode
          apply (cases tnode; sep_auto)
          done
        done
      done
  next
    case [simp]: (Cons rrs rss)
    then obtain sub sep where [simp]: "rrs = (sub, sep)"
      by (cases rrs)
    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" |
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof(cases)
      case sep_n_x
      then show ?thesis
        apply(subst del.simps)
        apply sep_auto
        using "2.prems"(2) sorted_inorder_separators apply blast
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
         apply(vcg (ss))
         apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
         apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply simp
         apply(vcg (ss))
         apply(vcg (ss))
         apply(vcg (ss))
        subgoal for tp tsi ti' tsi' tnode i tsi'l subsep subi sepi
          (* TODO this causes 4 subgoals *)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left;
              rule norm_pre_ex_rule; rule norm_pre_ex_rule; rule norm_pre_ex_rule;
              rule hoare_triple_preI;
              auto dest!: mod_starD)[]
             apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
          subgoal for lsi subi rsi
            apply(subgoal_tac "subi = None")
             prefer 2
             apply(auto dest!: list_assn_len)[]
            supply R = "2.IH"(2)[of ls rs rrs rss sub sep]
            thm R
            using split_ts apply(sep_auto heap add: R)
            using "2.prems" apply auto[]
               apply (metis "2.prems"(2) sorted_inorder_induct_subtree)
            using "2.prems" apply auto[]
              apply (meson "2.prems"(4) order_impl_root_order)
            using "2.prems"(4) apply fastforce
            apply(vcg (ss))
            apply(vcg (ss))
             apply(vcg (ss))
             apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
            apply(vcg (ss))
            apply(vcg (ss); simp)
            apply(cases tsi; simp)
            subgoal for subi' _ tsia' tsin'
              supply R = rebalance_middle_tree_update_rule
              thm R
                (* TODO create a new heap rule, in the node_i style *)
              apply(auto dest!: list_assn_len)[]
              apply(rule hoare_triple_preI)
              apply (sep_auto heap add: R dest!: mod_starD)
              using "2.prems" abs_split.del_height[of k sub x] order_impl_root_order[of k sub] apply (auto)[]
              using "2.prems" apply (auto split!: list.splits)[]
               apply auto[]
              apply sep_auto
              subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ tnode''
                apply (cases "(abs_split.rebalance_middle_tree k ls (abs_split.del k x sub) sepi rss tt)"; cases tnode'')
                 apply sep_auto
                apply sep_auto
                done
              done
            done
           apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
            (* copy pasta of "none" branch *)
          subgoal for subnode lsi subi rsi
            apply(subgoal_tac "subi = Some subnode")
             prefer 2
             apply(auto dest!: list_assn_len)[]
            supply R = "2.IH"(2)[of ls rs rrs rss sub sep]
            thm R
            using split_ts apply(sep_auto heap add: R)
            using "2.prems" apply auto[]
               apply (metis "2.prems"(2) sorted_inorder_induct_subtree)
            using "2.prems" apply auto[]
              apply (meson "2.prems"(4) order_impl_root_order)
            using "2.prems"(4) apply fastforce
            apply(vcg (ss))
            apply(vcg (ss))
             apply(vcg (ss))
             apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
            apply(vcg (ss))
            apply(vcg (ss); simp)
            apply(cases tsi; simp)
            subgoal for x' xab a n
              supply R = rebalance_middle_tree_update_rule
              thm R
                (* TODO create a new heap rule, in the node_i style *)
              apply(auto dest!: list_assn_len)[]
              apply(rule hoare_triple_preI)
              apply (sep_auto heap add: R dest!: mod_starD)
              using "2.prems" abs_split.del_height[of k sub x] order_impl_root_order[of k sub] apply (auto)[]
              using "2.prems" apply (auto split!: list.splits)[]
               apply auto[]
              apply sep_auto
              subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _  _  tnode'
                apply (cases "(abs_split.rebalance_middle_tree k ls (abs_split.del k x sub) sepi rss tt)"; cases tnode')
                 apply sep_auto
                apply sep_auto
                done
              done
            done
          done
        apply(rule hoare_triple_preI)
        using Cons  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
        done
    next
      case sep_x_Leaf
      then show ?thesis
        apply(subst del.simps)
        apply sep_auto
        using "2.prems"(2) sorted_inorder_separators apply blast
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
         apply(vcg (ss))
         apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
         apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply simp
         apply(vcg (ss))
         apply(vcg (ss))
         apply(vcg (ss))
        subgoal for tp tsi ti' tsi' tnode i tsi'l subsep subi sepi
          (* TODO this causes 4 subgoals *)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left;
              rule norm_pre_ex_rule; rule norm_pre_ex_rule; rule norm_pre_ex_rule;
              rule hoare_triple_preI;
              auto dest!: mod_starD)[]
            (* the correct subbranch *)
          subgoal for lsi subi rsi
            apply(cases tsi)
            apply (sep_auto)
             apply(auto simp add: is_pfa_def dest!: list_assn_len)[]
             apply (metis add_Suc_right le_imp_less_Suc length_append length_take less_add_Suc1 less_trans_Suc list.size(4) min.cobounded2 not_less_eq)
            apply vcg
            apply auto
            subgoal for tsin tsia
              apply(rule ent_ex_postI[where x="(tsia, tsin-1)"])
              apply(rule ent_ex_postI[where x="ti'"])
              apply(rule ent_ex_postI[where x="lsi@rsi"])
              apply (sep_auto dest!: list_assn_len)
              done
            done
            apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
           apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
          apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
          done
        apply(rule hoare_triple_preI)
        using Cons  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
        done
    next
      case sep_x_Node
      then show ?thesis
        apply(subst del.simps)
        apply sep_auto
        using "2.prems"(2) sorted_inorder_separators apply blast
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
         apply(vcg (ss))
         apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
         apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply simp
         apply(vcg (ss))
         apply(vcg (ss))
         apply(vcg (ss))
        subgoal for subts subt tp tsi ti tsi' tnode i tsi'l subsep subi sepi
          (* TODO this causes 4 subgoals *)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left;
              rule norm_pre_ex_rule; rule norm_pre_ex_rule; rule norm_pre_ex_rule;
              rule hoare_triple_preI;
              auto dest!: mod_starD)[]
             apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
            apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
            (* the correct sub branch *)
          subgoal for subnode lsi subi rsi
            apply(subgoal_tac "subi = Some subnode")
             apply (simp del: btree_assn.simps)
             supply R = split_max_rule[of "Node subts subt" k "Some subnode"]
            thm R
             apply(sep_auto heap add: R simp del: btree_assn.simps)
            using "2.prems" apply(auto dest!: list_assn_len mod_starD simp del: bal.simps order.simps)[]
            subgoal
            proof(goal_cases)
              case 1
              then have "order k (Node subts subt)"
                by blast
              moreover have "k > 0"
                by (simp add: "2.prems"(4))
              ultimately obtain sub_ls lsub lsep where sub_ts_split: "subts = sub_ls@[(lsub,lsep)]"
                by (metis abs_split.isin.cases le_0_eq list.size(3) order.simps(2) rev_exhaust zero_less_iff_neq_zero)
              from 1 have "bal (Node subts subt)"
                by auto
              then have "height lsub = height subt"
                by (simp add: sub_ts_split)
              then show ?thesis using sub_ts_split by blast
            qed
            using "2.prems" abs_split.order_bal_nonempty_lasttreebal[of k subt] order_impl_root_order[of k subt]
               apply(auto)[]
              apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
             apply vcg
              apply auto[]
             apply(cases "abs_split.split_max k (Node subts subt)"; simp)
            subgoal for split_res _ split_sub split_sep
              apply(cases split_res; simp)
              subgoal for split_subi split_sepi
                supply R = rebalance_middle_tree_update_rule[
                    of tt split_sub rss "length lsi" ls k lsi split_subi split_sep rsi tsi ti
                    ]
                thm R
                  (* id_assn split_sepi doesnt match yet... *)
                apply(auto simp add: prod_assn_def dest!: list_assn_len)
                apply (sep_auto)
                 apply(rule hoare_triple_preI)
                 apply(auto dest!: mod_starD)[]
                 apply (sep_auto heap add: R)
                using "2.prems" abs_split.split_max_height[of k sub] order_impl_root_order[of k sub]
                  abs_split.order_bal_nonempty_lasttreebal[of k sub] apply (auto)[]
                using "2.prems" abs_split.split_max_bal[of sub k] order_impl_root_order[of k sub]
                  apply (auto split!: list.splits)[]
                 apply auto[]
                apply(rule hoare_triple_preI)
                apply(auto dest!: mod_starD)[]
                subgoal for subtsi''a subtsi''n ti subtsi'' tnode'
                  apply(cases "(abs_split.rebalance_middle_tree k ls split_sub split_sep rss tt)"; cases "tnode'")
                   apply auto
                  apply sep_auto
                  done
                done
              done
            apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
            done
          apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
          done
        apply(rule hoare_triple_preI)
        using Cons  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
        done
    qed
  qed
qed

definition reduce_root ::"('a::{default,heap,linorder}) btnode ref option \<Rightarrow> 'a btnode ref option Heap"
  where
    "reduce_root ti = (case ti of
  None \<Rightarrow> return None |
  Some p_t \<Rightarrow> do {
    node \<leftarrow> !p_t;
    tsl \<leftarrow> pfa_length (kvs node);
    case tsl of 0 \<Rightarrow> return (last node) |
    _ \<Rightarrow> return ti
})"

lemma reduce_root_rule:
  "<btree_assn k t ti> reduce_root ti <btree_assn k (abs_split.reduce_root t)>\<^sub>t"
  apply(subst reduce_root_def)
  apply(cases t; cases ti)
     apply (sep_auto split!: nat.splits list.splits)+
  done

definition delete ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> 'a btnode ref option Heap"
  where
    "delete k x ti = do {
  ti' \<leftarrow> del k x ti;
  reduce_root ti'
}"

lemma delete_rule:
  assumes "bal t" and "root_order k t" and "k > 0" and "sorted (inorder t)"
  shows "<btree_assn k t ti> delete k x ti <btree_assn k (abs_split.delete k x t)>\<^sub>t"
  apply(subst delete_def)
  using assms apply (sep_auto heap add: del_rule reduce_root_rule)
  done

lemma empty_rule:
  shows "<emp>
  empty
  <\<lambda>r. btree_assn k (abs_split.empty_btree) r>"
  apply(subst empty_def)
  apply(sep_auto simp add: abs_split.empty_btree_def)
  done

end

end

