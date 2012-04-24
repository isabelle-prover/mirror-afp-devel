(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changelist since submission on 2009-11-26:

  2009-12-09: Ordered iterators, to_list produces sorted list


*)
header {* \isaheader{Map Implementation by Red-Black-Trees} *}
theory RBTMapImpl
imports 
  "../spec/MapSpec"
  "../common/RBT_add" 
  "../gen_algo/MapGA"
begin
text_raw {*\label{thy:RBTMapImpl}*}

(*@impl Map
  @type ('k::linorder,'v) rm 
  @abbrv rm,r
  Maps over linearly ordered keys implemented by red-black trees.
*)

type_synonym ('k,'v) rm = "('k,'v) RBT.rbt"

subsection "Definitions"
definition "rm_\<alpha> == RBT.lookup"
abbreviation (input) rm_invar where "rm_invar == \<lambda>_. True"
definition "rm_empty == (\<lambda>_::unit. RBT.empty)"
definition "rm_lookup k m == RBT.lookup m k"
definition "rm_update == RBT.insert"
definition "rm_update_dj == rm_update"
definition "rm_delete == RBT.delete"
definition rm_iterateoi where "rm_iterateoi r == RBT_add.rm_iterateoi (RBT.impl_of r)"
definition rm_reverse_iterateoi where "rm_reverse_iterateoi r == RBT_add.rm_reverse_iterateoi (RBT.impl_of r)"
definition "rm_iteratei == rm_iterateoi"

definition "rm_add == it_add rm_update rm_iteratei"
definition "rm_add_dj == rm_add"
definition "rm_isEmpty m == m=RBT.empty"
definition "rm_sel == iti_sel rm_iteratei"
definition "rm_sel' = iti_sel_no_map rm_iteratei"

definition "rm_to_list == it_map_to_list rm_reverse_iterateoi"
definition "list_to_rm == gen_list_to_map rm_empty rm_update"

definition "rm_min == iti_sel_no_map rm_iterateoi"
definition "rm_max == iti_sel_no_map rm_reverse_iterateoi"

subsection "Correctness"

lemmas rm_defs = 
  rm_\<alpha>_def
  rm_empty_def
  rm_lookup_def
  rm_update_def
  rm_update_dj_def
  rm_delete_def
  rm_iteratei_def
  rm_iterateoi_def
  rm_reverse_iterateoi_def
  rm_add_def
  rm_add_dj_def
  rm_isEmpty_def
  rm_sel_def
  rm_sel'_def
  rm_to_list_def
  list_to_rm_def
  rm_min_def
  rm_max_def

lemma rm_empty_impl: "map_empty rm_\<alpha> rm_invar rm_empty"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_lookup_impl: "map_lookup rm_\<alpha> rm_invar rm_lookup"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_update_impl: "map_update rm_\<alpha> rm_invar rm_update"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_update_dj_impl: "map_update_dj rm_\<alpha> rm_invar rm_update_dj"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_delete_impl: "map_delete rm_\<alpha> rm_invar rm_delete"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_\<alpha>_alist: "rm_invar m \<Longrightarrow> rm_\<alpha> m = Map.map_of (RBT.entries m)"
  by (simp add: rm_\<alpha>_def)

lemma rm_\<alpha>_finite[simp, intro!]: "finite (dom (rm_\<alpha> m))" 
  by (simp add: rm_\<alpha>_def)
  
lemma rm_is_finite_map: "finite_map rm_\<alpha> rm_invar" by (unfold_locales) auto

lemma map_to_set_lookup_entries: 
   "rbt_sorted t \<Longrightarrow> map_to_set (rbt_lookup t) = set (RBT_Impl.entries t)"
using RBT_Impl.map_of_entries[symmetric, of t]
by (simp add: distinct_entries map_to_set_map_of)

lemma rm_iterateoi_correct:
fixes t::"('k::linorder, 'v) RBT_Impl.rbt"
assumes is_sort: "rbt_sorted t"
defines "it \<equiv> RBT_add.rm_iterateoi::(('k, 'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v, '\<sigma>) set_iterator)"
shows "map_iterator_linord (it t) (rbt_lookup t)"
using is_sort
proof (induct t)
  case Empty
  show ?case unfolding it_def 
    by (simp add: rm_iterateoi_alt_def map_iterator_linord_emp_correct rbt_lookup_Empty)
next
  case (Branch c l k v r)
  note is_sort_t = Branch(3)

  from Branch(1) is_sort_t have l_it: "map_iterator_linord (it l) (rbt_lookup l)" by simp
  from Branch(2) is_sort_t have r_it: "map_iterator_linord (it r) (rbt_lookup r)" by simp
  note kv_it = map_iterator_linord_sng_correct[of k v]

  have kv_r_it : "set_iterator_map_linord
     (set_iterator_union (set_iterator_sng (k, v)) (it r))
     (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r))"
  proof (rule map_iterator_linord_union_correct [OF kv_it r_it])
    fix kv kv'
    assume pre: "kv \<in> map_to_set [k \<mapsto> v]" "kv' \<in> map_to_set (rbt_lookup r)"
    obtain k' v' where kv'_eq[simp]: "kv' = (k', v')" by (rule PairE)
 
    from pre is_sort_t show "fst kv < fst kv'" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      apply (metis entry_in_tree_keys rbt_greater_prop)
   done
  qed

  have l_kv_r_it : "set_iterator_map_linord (it (Branch c l k v r))
     (map_to_set (rbt_lookup l) \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r)))"
    unfolding it_def rm_iterateoi_alt_def
    unfolding it_def[symmetric]
  proof (rule map_iterator_linord_union_correct [OF l_it kv_r_it])
    fix kv1 kv2
    assume pre: "kv1 \<in> map_to_set (rbt_lookup l)" 
                "kv2 \<in> map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r)" 

    obtain k1 v1 where kv1_eq[simp]: "kv1 = (k1, v1)" by (rule PairE)
    obtain k2 v2 where kv2_eq[simp]: "kv2 = (k2, v2)" by (rule PairE)

    from pre is_sort_t show "fst kv1 < fst kv2" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      apply (metis entry_in_tree_keys rbt_greater_prop rbt_less_prop trt_trans')
    done
  qed
  
  from is_sort_t
  have map_eq: "map_to_set (rbt_lookup l) \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r)) =
        map_to_set (rbt_lookup (Branch c l k v r))" 
    by (simp add: set_eq_iff map_to_set_lookup_entries)

  from l_kv_r_it[unfolded map_eq]
  show ?case .
qed

lemma rm_iterateoi_impl: "map_iterateoi rm_\<alpha> rm_invar rm_iterateoi"
proof
  fix m:: "('a, 'b) rm"
  show "finite (dom (rm_\<alpha> m))" by simp
next
  fix m:: "('a, 'b) rm"
  show "map_iterator_linord (RBTMapImpl.rm_iterateoi m) (rm_\<alpha> m)"
    unfolding rm_\<alpha>_def RBTMapImpl.rm_iterateoi_def RBT.lookup_def
    by (rule rm_iterateoi_correct) (simp)
qed

lemma rm_reverse_iterateoi_correct:
fixes t::"('k::linorder, 'v) RBT_Impl.rbt"
assumes is_sort: "rbt_sorted t"
defines "it \<equiv> RBT_add.rm_reverse_iterateoi::(('k, 'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v, '\<sigma>) set_iterator)"
shows "map_iterator_rev_linord (it t) (rbt_lookup t)"
using is_sort
proof (induct t)
  case Empty
  show ?case unfolding it_def 
    by (simp add: rm_reverse_iterateoi_alt_def map_iterator_rev_linord_emp_correct rbt_lookup_Empty)
next
  case (Branch c l k v r)
  note is_sort_t = Branch(3)

  from Branch(1) is_sort_t have l_it: "map_iterator_rev_linord (it l) (rbt_lookup l)" by simp
  from Branch(2) is_sort_t have r_it: "map_iterator_rev_linord (it r) (rbt_lookup r)" by simp
  note kv_it = map_iterator_rev_linord_sng_correct[of k v]

  have kv_l_it : "set_iterator_map_rev_linord
     (set_iterator_union (set_iterator_sng (k, v)) (it l))
     (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l))"
  proof (rule map_iterator_rev_linord_union_correct [OF kv_it l_it])
    fix kv kv'
    assume pre: "kv \<in> map_to_set [k \<mapsto> v]" "kv' \<in> map_to_set (rbt_lookup l)"
    obtain k' v' where kv'_eq[simp]: "kv' = (k', v')" by (rule PairE)
 
    from pre is_sort_t show "fst kv > fst kv'" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      apply (metis entry_in_tree_keys rbt_less_prop)
   done
  qed

  have r_kv_l_it : "set_iterator_map_rev_linord (it (Branch c l k v r))
     (map_to_set (rbt_lookup r) \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l)))"
    unfolding it_def rm_reverse_iterateoi_alt_def
    unfolding it_def[symmetric]
  proof (rule map_iterator_rev_linord_union_correct [OF r_it kv_l_it])
    fix kv1 kv2
    assume pre: "kv1 \<in> map_to_set (rbt_lookup r)" 
                "kv2 \<in> map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l)" 

    obtain k1 v1 where kv1_eq[simp]: "kv1 = (k1, v1)" by (rule PairE)
    obtain k2 v2 where kv2_eq[simp]: "kv2 = (k2, v2)" by (rule PairE)

    from pre is_sort_t show "fst kv1 > fst kv2" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      apply (metis entry_in_tree_keys rbt_greater_prop rbt_less_prop trt_trans')
    done
  qed
  
  from is_sort_t
  have map_eq: "map_to_set (rbt_lookup r) \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l)) =
        map_to_set (rbt_lookup (Branch c l k v r))" 
    by (auto simp add: set_eq_iff map_to_set_lookup_entries)

  from r_kv_l_it[unfolded map_eq]
  show ?case .
qed

lemma rm_reverse_iterateoi_impl: "map_reverse_iterateoi rm_\<alpha> rm_invar rm_reverse_iterateoi"
proof
  fix m:: "('a, 'b) rm"
  show "finite (dom (rm_\<alpha> m))" by simp
next
  fix m:: "('a, 'b) rm"
  show "map_iterator_rev_linord (RBTMapImpl.rm_reverse_iterateoi m) (rm_\<alpha> m)"
    unfolding rm_\<alpha>_def RBTMapImpl.rm_reverse_iterateoi_def RBT.lookup_def
    by (rule rm_reverse_iterateoi_correct) (simp)
qed

lemmas rm_iteratei_impl = MapGA.iti_by_itoi[OF rm_iterateoi_impl, folded rm_iteratei_def]

lemmas rm_add_impl = 
  it_add_correct[OF rm_iteratei_impl rm_update_impl, folded rm_add_def]

lemmas rm_add_dj_impl =  
  map_add.add_dj_by_add[OF rm_add_impl, folded rm_add_dj_def]

lemma rm_isEmpty_impl: "map_isEmpty rm_\<alpha> rm_invar rm_isEmpty"
  apply (unfold_locales)
  apply (unfold rm_defs)
  apply (case_tac m)
  apply simp
  done

lemmas rm_sel_impl = iti_sel_correct[OF rm_iteratei_impl, folded rm_sel_def]
lemmas rm_sel'_impl = iti_sel'_correct[OF rm_iteratei_impl, folded rm_sel'_def]

lemmas rm_to_sorted_list_impl 
  = rito_map_to_sorted_list_correct[OF rm_reverse_iterateoi_impl, folded rm_to_list_def]

lemmas list_to_rm_impl
  = gen_list_to_map_correct[OF rm_empty_impl rm_update_impl, 
                            folded list_to_rm_def]

lemmas rm_min_impl = MapGA.itoi_min_correct[OF rm_iterateoi_impl, folded rm_min_def]
lemmas rm_max_impl = MapGA.ritoi_max_correct[OF rm_reverse_iterateoi_impl, folded rm_max_def]


interpretation rm: map_empty rm_\<alpha> rm_invar rm_empty 
  using rm_empty_impl .
interpretation rm: map_lookup rm_\<alpha> rm_invar rm_lookup 
  using rm_lookup_impl .
interpretation rm: map_update rm_\<alpha> rm_invar rm_update 
  using rm_update_impl .
interpretation rm: map_update_dj rm_\<alpha> rm_invar rm_update_dj 
  using rm_update_dj_impl .
interpretation rm: map_delete rm_\<alpha> rm_invar rm_delete 
  using rm_delete_impl .
interpretation rm: finite_map rm_\<alpha> rm_invar 
  using rm_is_finite_map .
interpretation rm: map_iteratei rm_\<alpha> rm_invar rm_iteratei
  using rm_iteratei_impl .
interpretation rm: map_iterateoi rm_\<alpha> rm_invar rm_iterateoi
  using rm_iterateoi_impl .
interpretation rm: map_reverse_iterateoi rm_\<alpha> rm_invar rm_reverse_iterateoi
  using rm_reverse_iterateoi_impl .
interpretation rm: map_add rm_\<alpha> rm_invar rm_add 
  using rm_add_impl .
interpretation rm: map_add_dj rm_\<alpha> rm_invar rm_add_dj 
  using rm_add_dj_impl .
interpretation rm: map_isEmpty rm_\<alpha> rm_invar rm_isEmpty 
  using rm_isEmpty_impl .
interpretation rm: map_sel rm_\<alpha> rm_invar rm_sel 
  using rm_sel_impl .
interpretation rm: map_sel' rm_\<alpha> rm_invar rm_sel' 
  using rm_sel'_impl .
interpretation rm: map_to_sorted_list rm_\<alpha> rm_invar rm_to_list 
  using rm_to_sorted_list_impl .
interpretation rm: list_to_map rm_\<alpha> rm_invar list_to_rm 
  using list_to_rm_impl . 

interpretation rm: map_min rm_\<alpha> rm_invar rm_min 
  using rm_min_impl .
interpretation rm: map_max rm_\<alpha> rm_invar rm_max 
  using rm_max_impl .

declare rm.finite[simp del, rule del]

lemmas rm_correct =
  rm.empty_correct
  rm.lookup_correct
  rm.update_correct
  rm.update_dj_correct
  rm.delete_correct
  rm.add_correct
  rm.add_dj_correct
  rm.isEmpty_correct
  rm.to_list_correct
  rm.to_map_correct

subsection "Code Generation"

export_code
  rm_empty
  rm_lookup
  rm_update
  rm_update_dj
  rm_delete
  rm_iteratei
  rm_iterateoi
  rm_reverse_iterateoi
  rm_add
  rm_add_dj
  rm_isEmpty
  rm_sel
  rm_sel'
  rm_to_list
  list_to_rm
  rm_min
  rm_max
  in SML
  module_name RBTMap
  file -

end

