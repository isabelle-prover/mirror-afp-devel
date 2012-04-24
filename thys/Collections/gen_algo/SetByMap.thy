(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedMap, transfer of iterators to OrderedSet

*)
header {* \isaheader{Implementing Sets by Maps} *}
theory SetByMap
imports 
  "../spec/SetSpec"
  "../spec/MapSpec"
  "../common/Misc" 
  "../iterator/SetIteratorOperations" 
  "../iterator/SetIteratorGA"
begin
text_raw {*\label{thy:SetByMap}*}

text {*
  In this theory, we show how to implement sets
  by maps.
*}

subsection "Definitions"
definition s_\<alpha> :: "('s \<Rightarrow> 'u \<rightharpoonup> unit) \<Rightarrow> 's \<Rightarrow> 'u set" 
  where "s_\<alpha> \<alpha> m == dom (\<alpha> m)"
definition[code_unfold]: "s_empty empt = empt" 
definition[code_unfold]: "s_sng sng x = sng x ()" 
definition "s_memb lookup x s == lookup x s \<noteq> None"
definition[code_unfold]: "s_ins update x s == update x () s"
definition[code_unfold]: "s_ins_dj update_dj x s == update_dj x () s"
definition[code_unfold]: "s_delete delete == delete"
definition s_sel 
  :: "('s \<Rightarrow> ('u \<times> unit \<Rightarrow> 'r option) \<Rightarrow> 'r option) \<Rightarrow> 
      's \<Rightarrow> ('u \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "s_sel sel s f == sel s (\<lambda>(u, _). f u)"
declare s_sel_def[code_unfold]
definition[code_unfold]: "s_isEmpty isEmpty == isEmpty"
definition[code_unfold]: "s_isSng isSng == isSng"

definition s_iteratei :: "('s \<Rightarrow> (('k \<times> unit),'\<sigma>) set_iterator) \<Rightarrow> ('s \<Rightarrow> ('k, '\<sigma>) set_iterator)"
  where  "s_iteratei it s == map_iterator_dom (it s)"
lemma s_iteratei_code[code] :
  "s_iteratei it s c f = it s c (\<lambda>x. f (fst x))"
unfolding s_iteratei_def map_iterator_dom_def set_iterator_image_alt_def by simp

definition s_ball 
  :: "('s \<Rightarrow> ('u \<times> unit \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('u \<Rightarrow> bool) \<Rightarrow> bool" 
  where "s_ball ball s P == ball s (\<lambda>(u, _). P u)"
declare s_ball_def[code_unfold]

definition s_bexists
  :: "('s \<Rightarrow> ('u \<times> unit \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('u \<Rightarrow> bool) \<Rightarrow> bool" 
  where "s_bexists bexists s P == bexists s (\<lambda>(u,_). P u)"
declare s_bexists_def[code_unfold]

definition[code_unfold]: "s_size sz \<equiv> sz"
definition[code_unfold]: "s_size_abort size_abort \<equiv> size_abort"

definition[code_unfold]: "s_union add == add"
definition[code_unfold]: "s_union_dj add_dj = add_dj"

lemmas s_defs =
  s_\<alpha>_def
  s_empty_def
  s_sng_def
  s_memb_def
  s_ins_def
  s_ins_dj_def
  s_delete_def
  s_sel_def
  s_isEmpty_def
  s_isSng_def
  s_iteratei_def
  s_ball_def
  s_bexists_def
  s_size_def
  s_size_abort_def
  s_union_def
  s_union_dj_def

subsection "Correctness"

lemma s_empty_correct:         
  fixes empty                  
  assumes "map_empty \<alpha> invar empty"
  shows "set_empty (s_\<alpha> \<alpha>) invar (s_empty empty)"
proof -                                                        
  interpret map_empty \<alpha> invar empty by fact             
  show ?thesis                                                 
    by unfold_locales                                          
       (auto simp add: s_defs empty_correct)                   
qed                                                            

lemma s_sng_correct:         
  fixes sng
  assumes "map_sng \<alpha> invar sng"
  shows "set_sng (s_\<alpha> \<alpha>) invar (s_sng sng)"
proof -                                                        
  interpret map_sng \<alpha> invar sng by fact             
  show ?thesis                                                 
    by unfold_locales                                          
       (auto simp add: s_defs sng_correct)                   
qed                                                            

lemma s_memb_correct:
  fixes lookup         
  assumes "map_lookup \<alpha> invar lookup"
  shows "set_memb (s_\<alpha> \<alpha>) invar (s_memb lookup)"
proof -                                                  
  interpret map_lookup \<alpha> invar lookup by fact           
  show ?thesis                                           
    by unfold_locales                                    
       (auto simp add: s_defs lookup_correct)               
qed                                                      

lemma s_ins_correct:
  fixes ins         
  assumes "map_update \<alpha> invar update"
  shows "set_ins (s_\<alpha> \<alpha>) invar (s_ins update)"
proof -                                                  
  interpret map_update \<alpha> invar update by fact           
  show ?thesis                                           
    by unfold_locales                                    
       (auto simp add: s_defs update_correct)               
qed                                                      

lemma s_ins_dj_correct:
  fixes ins_dj         
  assumes "map_update_dj \<alpha> invar update_dj"
  shows "set_ins_dj (s_\<alpha> \<alpha>) invar (s_ins_dj update_dj)"
proof -                                                           
  interpret map_update_dj \<alpha> invar update_dj by fact              
  show ?thesis                                                    
    by unfold_locales                                             
       (auto simp add: s_defs update_dj_correct)                     
qed                                                               

lemma s_delete_correct:
  fixes delete         
  assumes "map_delete \<alpha> invar delete"
  shows "set_delete (s_\<alpha> \<alpha>) invar (s_delete delete)"
proof -                                                           
  interpret map_delete \<alpha> invar delete by fact              
  show ?thesis                                                    
    by unfold_locales                                             
       (auto simp add: s_defs delete_correct)                     
qed                                                               

lemma s_sel_correct:
  fixes sel         
  assumes sel_OK: "map_sel \<alpha> invar sel"
  shows "set_sel (s_\<alpha> \<alpha>) invar (s_sel sel)"
proof     
  fix s and f :: "'b \<Rightarrow> 'c option"
  assume invar_s: "invar s"                               

  {
    assume "\<forall>x\<in>s_\<alpha> \<alpha> s. f x = None"
    with map_sel.selI [OF sel_OK, OF invar_s, of "\<lambda>(u, _). f u"]
    show "s_sel sel s f = None" 
      by (simp add: Ball_def s_\<alpha>_def dom_def s_sel_def)
  }

  { fix x r Q
    assume "x \<in> s_\<alpha> \<alpha> s" "f x = Some r"
           "\<And>x r. s_sel sel s f = Some r \<Longrightarrow>
                  x \<in> s_\<alpha> \<alpha> s \<Longrightarrow> f x = Some r \<Longrightarrow> Q"
    with map_sel.selE [OF sel_OK, OF invar_s, of x "()" "\<lambda>(u, _). f u" r Q]
    show "Q" by (simp add: s_\<alpha>_def dom_def s_sel_def)
  }
qed


lemma s_isEmpty_correct:
  fixes isEmpty         
  assumes "map_isEmpty \<alpha> invar isEmpty"
  shows "set_isEmpty (s_\<alpha> \<alpha>) invar (s_isEmpty isEmpty)"
proof -                                                              
  interpret map_isEmpty \<alpha> invar isEmpty by fact               
  show ?thesis                                                       
    by unfold_locales                                                
       (auto simp add: s_defs isEmpty_correct)                       
qed                                                                  

lemma s_isSng_correct:
  fixes isSng
  assumes "map_isSng \<alpha> invar isSng"
  shows "set_isSng (s_\<alpha> \<alpha>) invar (s_isSng isSng)"
proof -                                                              
  interpret map_isSng \<alpha> invar isSng by fact               
  show ?thesis                                                       
    by unfold_locales 
       (auto simp add: s_defs isSng_correct dom_eq_singleton_conv)
qed                                                                  


lemma s_iteratei_correct:
  fixes iteratei         
  assumes map_it_OK: "map_iteratei \<alpha> invar iteratei"
  shows "set_iteratei (s_\<alpha> \<alpha>) invar (s_iteratei iteratei)"
proof 
  fix s
  assume invar_s: "invar s"
  
  from map_iteratei.iteratei_rule[OF map_it_OK,OF invar_s]
  have iti_s: "map_iterator (iteratei s) (\<alpha> s)" .

  from set_iterator_finite[OF iti_s] 
  show "finite (s_\<alpha> \<alpha> s)"
    unfolding s_\<alpha>_def finite_map_to_set .
 
  from map_iterator_dom_correct [OF iti_s]
  show "set_iterator (s_iteratei iteratei s) (s_\<alpha> \<alpha> s)"
    unfolding s_\<alpha>_def s_iteratei_def  .
qed


lemma s_iterateoi_correct:
  fixes iteratei         
  assumes map_it_OK: "map_iterateoi \<alpha> invar iteratei"
  shows "set_iterateoi (s_\<alpha> \<alpha>) invar (s_iteratei iteratei)"
proof 
  fix s
  assume invar_s: "invar s"
  
  from map_iterateoi.iterateoi_rule[OF map_it_OK,OF invar_s]
  have iti_s: "map_iterator_linord (iteratei s) (\<alpha> s)" .

  from set_iterator_genord.finite_S0[OF iti_s[unfolded set_iterator_map_linord_def]] 
  show "finite (s_\<alpha> \<alpha> s)"
    unfolding s_\<alpha>_def finite_map_to_set .
 
  from map_iterator_linord_dom_correct [OF iti_s]
  show "set_iterator_linord (s_iteratei iteratei s) (s_\<alpha> \<alpha> s)"
    unfolding s_\<alpha>_def s_iteratei_def  .
qed

lemma s_reverse_iterateoi_correct:
  fixes iteratei         
  assumes map_it_OK: "map_reverse_iterateoi \<alpha> invar iteratei"
  shows "set_reverse_iterateoi (s_\<alpha> \<alpha>) invar (s_iteratei iteratei)"
proof 
  fix s
  assume invar_s: "invar s"
  
  from map_reverse_iterateoi.reverse_iterateoi_rule[OF map_it_OK,OF invar_s]
  have iti_s: "map_iterator_rev_linord (iteratei s) (\<alpha> s)" .

  from set_iterator_genord.finite_S0[OF iti_s[unfolded set_iterator_map_rev_linord_def]] 
  show "finite (s_\<alpha> \<alpha> s)"
    unfolding s_\<alpha>_def finite_map_to_set .
 
  from map_iterator_rev_linord_dom_correct [OF iti_s]
  show "set_iterator_rev_linord (s_iteratei iteratei s) (s_\<alpha> \<alpha> s)"
    unfolding s_\<alpha>_def s_iteratei_def  .
qed

lemma s_ball_correct:
  fixes ball         
  assumes "map_ball \<alpha> invar ball"
  shows "set_ball (s_\<alpha> \<alpha>) invar (s_ball ball)"
proof -                                                     
  interpret map_ball \<alpha> invar ball by fact            
  show ?thesis                                              
    by unfold_locales                                       
       (auto simp add: s_defs ball_correct)                 
qed                                                         

lemma s_bexists_correct:
  fixes bexists         
  assumes "map_bexists \<alpha> invar bexists"
  shows "set_bexists (s_\<alpha> \<alpha>) invar (s_bexists bexists)"
proof -                                                     
  interpret map_bexists \<alpha> invar bexists by fact            
  show ?thesis                                              
    by unfold_locales                                       
       (auto simp add: s_defs bexists_correct)                 
qed

lemma s_size_correct:
  fixes size
  assumes "map_size \<alpha> invar size"
  shows "set_size (s_\<alpha> \<alpha>) invar (s_size size)"
proof -                                                     
  interpret map_size \<alpha> invar size by fact            
  show ?thesis                                              
    by unfold_locales                                       
       (auto simp add: s_defs size_correct)                 
qed

lemma s_size_abort_correct:
  fixes size_abort
  assumes "map_size_abort \<alpha> invar size_abort"
  shows "set_size_abort (s_\<alpha> \<alpha>) invar (s_size_abort size_abort)"
proof -                                                     
  interpret map_size_abort \<alpha> invar size_abort by fact            
  show ?thesis                                              
    by unfold_locales                                       
       (auto simp add: s_defs size_abort_correct)                 
qed

lemma s_union_correct:
  fixes add
  assumes "map_add \<alpha> invar add"
  shows "set_union (s_\<alpha> \<alpha>) invar (s_\<alpha> \<alpha>) invar (s_\<alpha> \<alpha>) invar (s_union add)"
proof -
  interpret map_add \<alpha> invar add by fact
  show ?thesis
    by unfold_locales
       (auto simp add: s_defs add_correct)
qed

lemma s_union_dj_correct:
  fixes add_dj
  assumes "map_add_dj \<alpha> invar add_dj"
  shows "set_union_dj (s_\<alpha> \<alpha>) invar (s_\<alpha> \<alpha>) invar (s_\<alpha> \<alpha>) invar (s_union_dj add_dj)"
proof -
  interpret map_add_dj \<alpha> invar add_dj by fact
  show ?thesis
    by unfold_locales
       (auto simp add: s_defs add_dj_correct)
qed

lemma finite_set_by_map:
  assumes BM: "finite_map \<alpha> invar"
  shows "finite_set (s_\<alpha> \<alpha>) invar"
proof -
  interpret finite_map \<alpha> invar by fact
  show ?thesis 
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def)
    apply simp
    done
qed

end
