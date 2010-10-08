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
imports OrderedSet OrderedMap "common/Misc"
begin
text_raw {*\label{thy:SetByMap}*}

text {*
  In this theory, we show how to implement sets
  by maps.
*}

subsection "Definitions"
definition s_\<alpha> :: "('s \<Rightarrow> 'u \<rightharpoonup> unit) \<Rightarrow> 's \<Rightarrow> 'u set" 
  where "s_\<alpha> \<alpha> m == dom (\<alpha> m)"
definition "s_empty empt = empt" 
definition "s_memb lookup x s == lookup x s \<noteq> None"
definition s_ins where "s_ins update x s == update x () s"
definition s_ins_dj where "s_ins_dj update_dj x s == update_dj x () s"
definition s_delete where "s_delete delete == delete"
definition s_sel 
  :: "('s \<Rightarrow> ('u \<Rightarrow> unit \<Rightarrow> 'r option) \<Rightarrow> 'r option) \<Rightarrow> 
      's \<Rightarrow> ('u \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "s_sel sel s f == sel s (\<lambda>u v. f u)"
definition "s_isEmpty isEmpty == isEmpty"

definition s_iterate :: "('s,'k,unit,'\<sigma>) map_iterator \<Rightarrow> ('s,'k,'\<sigma>) iterator"
  where  "s_iterate iterate f s \<sigma>0 == iterate (\<lambda>k v \<sigma>. f k \<sigma>) s \<sigma>0"
definition s_iteratei :: "('s,'k,unit,'\<sigma>) map_iteratori \<Rightarrow> ('s,'k,'\<sigma>) iteratori"
  where "s_iteratei iteratei c f s \<sigma>0 == iteratei c (\<lambda>k v \<sigma>. f k \<sigma>) s \<sigma>0"

definition s_iterateo 
  :: "('s,'k::linorder,unit,'\<sigma>) map_iterator \<Rightarrow> ('s,'k,'\<sigma>) iterator"
  where "s_iterateo iterate f s \<sigma>0 == iterate (\<lambda>k v \<sigma>. f k \<sigma>) s \<sigma>0"
definition s_iterateoi
  :: "('s,'k::linorder,unit,'\<sigma>) map_iteratori \<Rightarrow> ('s,'k,'\<sigma>) iteratori"
  where "s_iterateoi iteratei c f s \<sigma>0 == iteratei c (\<lambda>k v \<sigma>. f k \<sigma>) s \<sigma>0"

definition s_reverse_iterateo 
  :: "('s,'k::linorder,unit,'\<sigma>) map_iterator \<Rightarrow> ('s,'k,'\<sigma>) iterator"
  where "s_reverse_iterateo iterate f s \<sigma>0 == iterate (\<lambda>k v \<sigma>. f k \<sigma>) s \<sigma>0"
definition s_reverse_iterateoi 
  :: "('s,'k::linorder,unit,'\<sigma>) map_iteratori \<Rightarrow> ('s,'k,'\<sigma>) iteratori"
  where "s_reverse_iterateoi iteratei c f s \<sigma>0 == 
          iteratei c (\<lambda>k v \<sigma>. f k \<sigma>) s \<sigma>0"

definition s_ball 
  :: "('s \<Rightarrow> ('u \<Rightarrow> unit \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('u \<Rightarrow> bool) \<Rightarrow> bool" 
  where "s_ball ball s P == ball s (\<lambda>u v. P u)"
definition "s_union add == add"
definition "s_union_dj add_dj = add_dj"

lemmas s_defs =
  s_\<alpha>_def
  s_empty_def
  s_memb_def
  s_ins_def
  s_ins_dj_def
  s_delete_def
  s_sel_def
  s_isEmpty_def
  s_iterate_def
  s_iteratei_def
  s_iterateo_def
  s_iterateoi_def
  s_reverse_iterateo_def
  s_reverse_iterateoi_def
  s_ball_def
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
  assumes "map_sel \<alpha> invar sel"
  shows "set_sel (s_\<alpha> \<alpha>) invar (s_sel sel)"
proof -                                                  
  interpret map_sel \<alpha> invar sel by fact           
  show ?thesis                                           
    apply unfold_locales                                    
    apply (unfold s_\<alpha>_def s_sel_def dom_def)
    apply (auto simp add: selI elim: selE)
    done
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

lemma s_iterate_correct:
  fixes iterate         
  assumes "map_iterate \<alpha> invar iterate"
  shows "set_iterate (s_\<alpha> \<alpha>) invar (s_iterate iterate)"
proof -                                                              
  interpret map_iterate \<alpha> invar iterate by fact               
  show ?thesis
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def s_iterate_def)
    apply simp
    apply (rule iterate_rule)
    apply auto
    done
qed                                                                  

lemma s_iteratei_correct:
  fixes iteratei         
  assumes "map_iteratei \<alpha> invar iteratei"
  shows "set_iteratei (s_\<alpha> \<alpha>) invar (s_iteratei iteratei)"
proof -                                                                 
  interpret map_iteratei \<alpha> invar iteratei by fact                
  show ?thesis                                                          
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def s_iteratei_def)
    apply simp
    apply (rule iteratei_rule)
    apply auto
    done
qed                                                                     


lemma s_iterateo_correct:
  fixes iterate         
  assumes "map_iterateo \<alpha> invar iterate"
  shows "set_iterateo (s_\<alpha> \<alpha>) invar (s_iterateo iterate)"
proof -                                                              
  interpret map_iterateo \<alpha> invar iterate by fact               
  show ?thesis
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def s_iterateo_def)
    apply simp
    apply (rule iterateo_rule)
    apply auto
    done
qed                                                                  

lemma s_iterateoi_correct:
  fixes iteratei         
  assumes "map_iterateoi \<alpha> invar iteratei"
  shows "set_iterateoi (s_\<alpha> \<alpha>) invar (s_iterateoi iteratei)"
proof -                                                                 
  interpret map_iterateoi \<alpha> invar iteratei by fact                
  show ?thesis                                                          
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def s_iterateoi_def)
    apply simp
    apply (rule iterateoi_rule)
    apply auto
    done
qed                                                                     

lemma s_reverse_iterateo_correct:
  fixes iterate
  assumes "map_reverse_iterateo \<alpha> invar iterate"
  shows "set_reverse_iterateo (s_\<alpha> \<alpha>) invar (s_reverse_iterateo iterate)"
proof -                                                              
  interpret map_reverse_iterateo \<alpha> invar iterate by fact               
  show ?thesis
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def s_reverse_iterateo_def)
    apply simp
    apply (rule reverse_iterateo_rule)
    apply auto
    done
qed                                                                  

lemma s_reverse_iterateoi_correct:
  fixes iteratei         
  assumes "map_reverse_iterateoi \<alpha> invar iteratei"
  shows "set_reverse_iterateoi (s_\<alpha> \<alpha>) invar (s_reverse_iterateoi iteratei)"
proof -                                                                 
  interpret map_reverse_iterateoi \<alpha> invar iteratei by fact                
  show ?thesis                                                          
    apply (unfold_locales)
    apply (unfold s_\<alpha>_def s_reverse_iterateoi_def)
    apply simp
    apply (rule reverse_iterateoi_rule)
    apply auto
    done
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
