(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Standard Instantiations *}
theory StdInst
imports 
  MapStdImpl SetStdImpl Fifo
  SetIndex Algos 
  SetGA MapGA

begin
text_raw {*\label{thy:StdInst}*}
(* We use a small ad-hoc hack to generate the actual instantiations from this file: *)

text {*
  This theory provides standard instantiations of some abstract algorithms
  for rb-trees, lists and hashsets/maps.
*}


(* TODO: A bit dirty: We partially instantiate the it_set_to_list_enqueue generic algorithm here.
  The other parameter (the set class) is instantiated below using the automatic instantiation *)
definition "it_set_to_fifo it == it_set_to_List_enq it fifo_empty fifo_enqueue"

lemmas it_set_to_fifo_correct = it_set_to_List_enq_correct[OF _ fifo_empty_impl fifo_enqueue_impl, folded it_set_to_fifo_def]

(*#implementations
  map ListMap_Invar lmi li
  map ListMap lm l
  map RBTMap rm r
  map HashMap hm h
  set ListSet_Invar lsi li
  set ListSet ls l
  set RBTSet rs r
  set HashSet hs h
  map ArrayHashMap ahm a
  set ArrayHashSet ahs a
*)
(*  map TrieMap tm t TODO: @Peter: Keine Kombination (trie, rbt) generieren *)
(*  set TrieSet ts t TODO: @Peter: Keine Kombination (trie, rbt) generieren *)



(*#patterns
 SetGA.it_copy@set_copy: (x:set)iterate (y:set)empty (y:set)ins \<Rightarrow> (x,y)copy
 SetGA.it_union@set_union: (x:set)iterate (y:set)ins \<Rightarrow> (x,y,y)union
 SetGA.it_union_dj@set_union_dj: (x:set)iterate (y:set)ins_dj \<Rightarrow> (x,y,y)union_dj
 SetGA.it_inter@set_inter: (x:set)iterate (y:set)memb (z:set)empty (z)ins_dj \<Rightarrow> (x,y,z)inter

 SetGA.ball_subset@set_subset: (x:set)ball (y:set)memb \<Rightarrow> (x,y)subset
 SetGA.subset_equal@set_equal: (x:set,y:set)subset (y,x)subset \<Rightarrow> (x,y)equal

 SetGA.it_image_filter@set_image_filter: (x:set)iterate (y:set)empty (y:set)ins \<Rightarrow> (x,y)image_filter
 SetGA.it_inj_image_filter@set_inj_image_filter: (x:set)iterate (y:set)empty (y:set)ins_dj \<Rightarrow> (x,y)inj_image_filter

 SetGA.iflt_image@set_image: (x:set,y:set)image_filter \<Rightarrow> (x,y)image
 SetGA.iflt_inj_image@set_inj_image: (x:set,y:set)inj_image_filter \<Rightarrow> (x,y)inj_image

 SetGA.it_Union_image@set_Union_image: (x:set)iterate (z:set)empty (y:set,z,z)union \<Rightarrow> (x,y,z)Union_image

 SetGA.sel_disjoint_witness@set_disjoint_witness: (x:set)sel (y:set)memb \<Rightarrow> (x,y)disjoint_witness
 SetGA.ball_disjoint@set_disjoint (x:set)ball (y:set)memb \<Rightarrow> (x,y)disjoint

 SetGA.image_filter_cp@!: (x:set)iterate (y:set)iterate (z:set)empty (z)ins \<Rightarrow> (x,y,z)image_filter_cp
 SetGA.inj_image_filter_cp@!: (x:set)iterate (y:set)iterate (z:set)empty (z)ins_dj \<Rightarrow> (x,y,z)inj_image_filter_cp
 SetGA.cart@!: (x:set)iterate (y:set)iterate (z:set)empty (z)ins_dj \<Rightarrow> (x,y,z)cart

 it_set_to_fifo@!: (x:set)iterate \<Rightarrow> (x)to_fifo

 map_to_nat@!: (x:set)iterate (y:map)empty (y:map)update \<Rightarrow> (x,y)map_to_nat
*)

(*#insert_generated*)


(*#explicit x:map y:set
definition "$s_idx_invar == idx_invar $x_\<alpha> $x_invar $y_\<alpha> $y_invar"
definition "$s_idx_lookup == idx_lookup $x_lookup $y_empty"
lemmas $s_idx_lookup_correct = idx_lookup_correct[OF $x_lookup_impl $y_empty_impl, folded $s_idx_invar_def $s_idx_lookup_def]
*)

(*#explicit x:map y:set z:set
definition "$s_idx_build == idx_build $x_empty $x_lookup $x_update   $y_empty $y_ins    $z_iterate"
lemmas $s_idx_build_correct = idx_build_correct[OF $x_empty_impl $x_lookup_impl $x_update_impl   $y_empty_impl $y_ins_impl   $z_iterate_impl,
  folded $!x$!y_idx_invar_def $s_idx_build_def]
*)

end
