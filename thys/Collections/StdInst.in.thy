(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Standard Instantiations *}
theory StdInst
imports MapStdImpl SetStdImpl HashMap HashSet Index Algos
begin
text_raw {*\label{thy:StdInst}*}
(* We use a small ad-hoc hack to generate the actual instantiations from this file: *)

text {*
  This theory provides standard instantiations of some abstract algorithms
  for rb-trees, lists and hashsets/maps.
*}


(*#implementations
  map ListMap lm l
  map RBTMap rm r
  map HashMap hm h
  set ListSet ls l
  set RBTSet rs r
  set HashSet hs h
*)

(*#patterns
 it_union@set_union: (x:set)iterate (y:set)ins \<Rightarrow> (x,y,y)union
 it_union_dj@set_union_dj: (x:set)iterate (y:set)ins_dj \<Rightarrow> (x,y,y)union_dj
 it_inter@set_inter: (x:set)iterate (y:set)memb (z:set)empty (z)ins_dj \<Rightarrow> (x,y,z)inter

 ball_subset@set_subset: (x:set)ball (y:set)memb \<Rightarrow> (x,y)subset
 subset_equal@set_equal: (x:set,y:set)subset (y,x)subset \<Rightarrow> (x,y)equal

 it_image_filter@set_image_filter: (x:set)iterate (y:set)empty (y:set)ins \<Rightarrow> (x,y)image_filter
 it_inj_image_filter@set_inj_image_filter: (x:set)iterate (y:set)empty (y:set)ins_dj \<Rightarrow> (x,y)inj_image_filter

 iflt_image@set_image: (x:set,y:set)image_filter \<Rightarrow> (x,y)image
 iflt_inj_image@set_inj_image: (x:set,y:set)inj_image_filter \<Rightarrow> (x,y)inj_image

 it_Union_image@set_Union_image: (x:set)iterate (z:set)empty (y:set,z,z)union \<Rightarrow> (x,y,z)Union_image

 sel_disjoint_witness@set_disjoint_witness: (x:set)sel (y:set)memb \<Rightarrow> (x,y)disjoint_witness
 ball_disjoint@set_disjoint (x:set)ball (y:set)memb \<Rightarrow> (x,y)disjoint

 image_filter_cp@!: (x:set)iterate (y:set)iterate (z:set)empty (z)ins \<Rightarrow> (x,y,z)image_filter_cp
 inj_image_filter_cp@!: (x:set)iterate (y:set)iterate (z:set)empty (z)ins_dj \<Rightarrow> (x,y,z)inj_image_filter_cp
 cart@!: (x:set)iterate (y:set)iterate (z:set)empty (z)ins_dj \<Rightarrow> (x,y,z)cart

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
