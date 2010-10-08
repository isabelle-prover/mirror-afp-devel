header {* \isaheader{Record-based Map Interface: Implementation setup} *}
theory RecordMapImpl
imports 
  StdInst
begin

(*---------------------------------------------*)
subsection "Hash Maps"
  definition "hm_ops = \<lparr>
    map_op_\<alpha> = hm_\<alpha>, 
    map_op_invar = hm_invar, 
    map_op_empty = hm_empty, 
    map_op_lookup = hm_lookup, 
    map_op_update = hm_update, 
    map_op_update_dj = hm_update_dj, 
    map_op_delete = hm_delete, 
    map_op_add = hm_add, 
    map_op_add_dj = hm_add_dj, 
    map_op_isEmpty = hm_isEmpty, 
    map_op_ball = hm_ball, 
    map_op_sel = hm_sel', 
    map_op_to_list = hm_to_list, 
    map_op_to_map = list_to_hm
    \<rparr>"

  interpretation hmr!: StdMap hm_ops
    apply (rule StdMap.intro)
    apply (simp_all add: hm_ops_def)
    apply unfold_locales
    done

  lemma hm_ops_unfold[code_unfold]:
    "map_op_\<alpha> hm_ops = hm_\<alpha>"
    "map_op_invar hm_ops = hm_invar"
    "map_op_empty hm_ops = hm_empty"
    "map_op_lookup hm_ops = hm_lookup"
    "map_op_update hm_ops = hm_update"
    "map_op_update_dj hm_ops = hm_update_dj"
    "map_op_delete hm_ops = hm_delete"
    "map_op_add hm_ops = hm_add"
    "map_op_add_dj hm_ops = hm_add_dj"
    "map_op_isEmpty hm_ops = hm_isEmpty"
    "map_op_ball hm_ops = hm_ball"
    "map_op_sel hm_ops = hm_sel'"
    "map_op_to_list hm_ops = hm_to_list"
    "map_op_to_map hm_ops = list_to_hm"
    by (auto simp add: hm_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *}
  interpretation hmr!: map_iterate "(map_op_\<alpha> hm_ops)" "(map_op_invar hm_ops)" hm_iterate 
    using hm_iterate_impl[folded hm_ops_unfold] .

  interpretation hmr!: map_iteratei "(map_op_\<alpha> hm_ops)" "(map_op_invar hm_ops)" hm_iteratei 
    using hm_iteratei_impl[folded hm_ops_unfold] .




(*---------------------------------------------*)
subsection "RBT Maps"

  definition "rm_ops = \<lparr>
    map_op_\<alpha> = rm_\<alpha>, 
    map_op_invar = rm_invar, 
    map_op_empty = rm_empty, 
    map_op_lookup = rm_lookup, 
    map_op_update = rm_update, 
    map_op_update_dj = rm_update_dj, 
    map_op_delete = rm_delete, 
    map_op_add = rm_add, 
    map_op_add_dj = rm_add_dj, 
    map_op_isEmpty = rm_isEmpty, 
    map_op_ball = rm_ball, 
    map_op_sel = rm_sel', 
    map_op_to_list = rm_to_list, 
    map_op_to_map = list_to_rm,
    map_op_min = rm_min,
    map_op_max = rm_max
    \<rparr>"

  interpretation rmr!: StdMap rm_ops
    apply (rule StdMap.intro)
    apply (simp_all add: rm_ops_def)
    apply unfold_locales
    done

  interpretation rmr!: StdOMap rm_ops
    apply (rule StdOMap.intro)
    apply (rule StdMap.intro)
    apply (simp_all add: rm_ops_def)
    apply unfold_locales
    done

  lemma rm_ops_unfold[code_unfold]:
    "map_op_\<alpha> rm_ops = rm_\<alpha>"
    "map_op_invar rm_ops = rm_invar"
    "map_op_empty rm_ops = rm_empty"
    "map_op_lookup rm_ops = rm_lookup"
    "map_op_update rm_ops = rm_update"
    "map_op_update_dj rm_ops = rm_update_dj"
    "map_op_delete rm_ops = rm_delete"
    "map_op_add rm_ops = rm_add"
    "map_op_add_dj rm_ops = rm_add_dj"
    "map_op_isEmpty rm_ops = rm_isEmpty"
    "map_op_ball rm_ops = rm_ball"
    "map_op_sel rm_ops = rm_sel'"
    "map_op_to_list rm_ops = rm_to_list"
    "map_op_to_map rm_ops = list_to_rm"
    "map_op_min rm_ops = rm_min"
    "map_op_max rm_ops = rm_max"
    by (auto simp add: rm_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *}

  interpretation rmr!: map_iterate "(map_op_\<alpha> rm_ops)" "(map_op_invar rm_ops)" rm_iterate 
    unfolding rm_ops_unfold
    using rm_iterate_impl .

  interpretation rmr!: map_iteratei "(map_op_\<alpha> rm_ops)" "(map_op_invar rm_ops)" rm_iteratei 
    unfolding rm_ops_unfold
    using rm_iteratei_impl .

  interpretation rmr!: map_iterateo "(map_op_\<alpha> rm_ops)" "(map_op_invar rm_ops)" rm_iterateo 
    unfolding rm_ops_unfold
    using rm_iterateo_impl .

  interpretation rmr!: map_iterateoi "(map_op_\<alpha> rm_ops)" "(map_op_invar rm_ops)" rm_iterateoi 
    unfolding rm_ops_unfold
    using rm_iterateoi_impl .

  interpretation rmr!: map_reverse_iterateo "(map_op_\<alpha> rm_ops)" "(map_op_invar rm_ops)" rm_reverse_iterateo 
    unfolding rm_ops_unfold
    using rm_reverse_iterateo_impl .

  interpretation rmr!: map_reverse_iterateoi "(map_op_\<alpha> rm_ops)" "(map_op_invar rm_ops)" rm_reverse_iterateoi 
    unfolding rm_ops_unfold
    using rm_reverse_iterateoi_impl .



(*---------------------------------------------*)
subsection "List Maps"
  definition "lm_ops = \<lparr>
    map_op_\<alpha> = lm_\<alpha>, 
    map_op_invar = lm_invar, 
    map_op_empty = lm_empty, 
    map_op_lookup = lm_lookup, 
    map_op_update = lm_update, 
    map_op_update_dj = lm_update_dj, 
    map_op_delete = lm_delete, 
    map_op_add = lm_add, 
    map_op_add_dj = lm_add_dj, 
    map_op_isEmpty = lm_isEmpty, 
    map_op_ball = lm_ball, 
    map_op_sel = lm_sel', 
    map_op_to_list = lm_to_list, 
    map_op_to_map = list_to_lm
    \<rparr>"

  interpretation lmr!: StdMap lm_ops
    apply (rule StdMap.intro)
    apply (simp_all add: lm_ops_def)
    apply unfold_locales
    done

  lemma lm_ops_unfold[code_unfold]:
    "map_op_\<alpha> lm_ops = lm_\<alpha>"
    "map_op_invar lm_ops = lm_invar"
    "map_op_empty lm_ops = lm_empty"
    "map_op_lookup lm_ops = lm_lookup"
    "map_op_update lm_ops = lm_update"
    "map_op_update_dj lm_ops = lm_update_dj"
    "map_op_delete lm_ops = lm_delete"
    "map_op_add lm_ops = lm_add"
    "map_op_add_dj lm_ops = lm_add_dj"
    "map_op_isEmpty lm_ops = lm_isEmpty"
    "map_op_ball lm_ops = lm_ball"
    "map_op_sel lm_ops = lm_sel'"
    "map_op_to_list lm_ops = lm_to_list"
    "map_op_to_map lm_ops = list_to_lm"
    by (auto simp add: lm_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *}
  interpretation lmr!: map_iterate "(map_op_\<alpha> lm_ops)" "(map_op_invar lm_ops)" lm_iterate 
    using lm_iterate_impl[folded lm_ops_unfold] .

  interpretation lmr!: map_iteratei "(map_op_\<alpha> lm_ops)" "(map_op_invar lm_ops)" lm_iteratei 
    using lm_iteratei_impl[folded lm_ops_unfold] .

(*---------------------------------------------*)
subsection "Array Hash Maps"
  definition "ahm_ops = \<lparr>
    map_op_\<alpha> = ahm_\<alpha>, 
    map_op_invar = ahm_invar, 
    map_op_empty = ahm_empty, 
    map_op_lookup = ahm_lookup, 
    map_op_update = ahm_update, 
    map_op_update_dj = ahm_update_dj, 
    map_op_delete = ahm_delete, 
    map_op_add = ahm_add, 
    map_op_add_dj = ahm_add_dj, 
    map_op_isEmpty = ahm_isEmpty, 
    map_op_ball = ahm_ball, 
    map_op_sel = ahm_sel', 
    map_op_to_list = ahm_to_list, 
    map_op_to_map = list_to_ahm
    \<rparr>"

  interpretation ahmr!: StdMap ahm_ops
    apply (rule StdMap.intro)
    apply (simp_all add: ahm_ops_def)
    apply unfold_locales
    done

  lemma ahm_ops_unfold[code_unfold]:
    "map_op_\<alpha> ahm_ops = ahm_\<alpha>"
    "map_op_invar ahm_ops = ahm_invar"
    "map_op_empty ahm_ops = ahm_empty"
    "map_op_lookup ahm_ops = ahm_lookup"
    "map_op_update ahm_ops = ahm_update"
    "map_op_update_dj ahm_ops = ahm_update_dj"
    "map_op_delete ahm_ops = ahm_delete"
    "map_op_add ahm_ops = ahm_add"
    "map_op_add_dj ahm_ops = ahm_add_dj"
    "map_op_isEmpty ahm_ops = ahm_isEmpty"
    "map_op_ball ahm_ops = ahm_ball"
    "map_op_sel ahm_ops = ahm_sel'"
    "map_op_to_list ahm_ops = ahm_to_list"
    "map_op_to_map ahm_ops = list_to_ahm"
    by (auto simp add: ahm_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *}
  interpretation ahmr!: map_iterate "(map_op_\<alpha> ahm_ops)" "(map_op_invar ahm_ops)" ahm_iterate 
    using ahm_iterate_impl[folded ahm_ops_unfold] .

  interpretation ahmr!: map_iteratei "(map_op_\<alpha> ahm_ops)" "(map_op_invar ahm_ops)" ahm_iteratei 
    using ahm_iteratei_impl[folded ahm_ops_unfold] .

(*---------------------------------------------*)
(* TODO: Insert again when StdInst works with tries
subsection "Trie Maps"

  definition "tm_ops = \<lparr>
    map_op_\<alpha> = tm_\<alpha>, 
    map_op_invar = tm_invar, 
    map_op_empty = tm_empty, 
    map_op_lookup = tm_lookup, 
    map_op_update = tm_update, 
    map_op_update_dj = tm_update_dj, 
    map_op_delete = tm_delete, 
    map_op_add = tm_add, 
    map_op_add_dj = tm_add_dj, 
    map_op_isEmpty = tm_isEmpty, 
    map_op_ball = tm_ball, 
    map_op_sel = tm_sel', 
    map_op_to_list = tm_to_list, 
    map_op_to_map = list_to_tm
    \<rparr>"

  interpretation tmr!: StdMap tm_ops
    apply (rule StdMap.intro)
    apply (simp_all add: tm_ops_def)
    apply unfold_locales
    done

  lemma tm_ops_unfold[code_unfold]:
    "map_op_\<alpha> tm_ops = tm_\<alpha>"
    "map_op_invar tm_ops = tm_invar"
    "map_op_empty tm_ops = tm_empty"
    "map_op_lookup tm_ops = tm_lookup"
    "map_op_update tm_ops = tm_update"
    "map_op_update_dj tm_ops = tm_update_dj"
    "map_op_delete tm_ops = tm_delete"
    "map_op_add tm_ops = tm_add"
    "map_op_add_dj tm_ops = tm_add_dj"
    "map_op_isEmpty tm_ops = tm_isEmpty"
    "map_op_ball tm_ops = tm_ball"
    "map_op_sel tm_ops = tm_sel'"
    "map_op_to_list tm_ops = tm_to_list"
    "map_op_to_map tm_ops = list_to_tm"
    by (auto simp add: tm_ops_def)

  -- "Required to set up unfold_locales in contexts with additional iterators"
  interpretation tmr!: map_iterate "(map_op_\<alpha> tm_ops)" "(map_op_invar tm_ops)" tm_iterate 
    using tm_iterate_impl[folded tm_ops_unfold] .

  interpretation tmr!: map_iteratei "(map_op_\<alpha> tm_ops)" "(map_op_invar tm_ops)" tm_iteratei 
    using tm_iteratei_impl[folded tm_ops_unfold] .
*)
end
