(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Set Implementation by List"
theory ListSetImpl
imports SetSpec SetGA "common/Misc"
begin
text_raw {*\label{thy:ListSetImpl}*}

text {*
  In this theory, sets are implemented by lists. Abbreviations: ls,l
*}


types
  'a ls = "'a list"

subsection "Definitions"

definition ls_\<alpha> :: "'a ls \<Rightarrow> 'a set" where "ls_\<alpha> == set"
definition ls_invar :: "'a ls \<Rightarrow> bool" where "ls_invar == distinct"
definition ls_empty :: "'a ls" where "ls_empty == []"
definition ls_memb :: "'a \<Rightarrow> 'a ls \<Rightarrow> bool" where "ls_memb == op mem"
definition ls_ins :: "'a \<Rightarrow> 'a ls \<Rightarrow> 'a ls" where "ls_ins x l == if x mem l then l else x#l"
definition ls_ins_dj :: "'a \<Rightarrow> 'a ls \<Rightarrow> 'a ls" where "ls_ins_dj x l == x#l"

(* Tail recursive version *)
fun ls_delete_aux where
  "ls_delete_aux x res [] = res" |
  "ls_delete_aux x res (a#l) = (if x=a then revg res l else ls_delete_aux x (a#res) l)"

definition ls_delete :: "'a \<Rightarrow> 'a ls \<Rightarrow> 'a ls" where "ls_delete x l == ls_delete_aux x [] l"

fun ls_iteratei :: "('a ls,'a,'\<sigma>) iteratori" where
  "ls_iteratei c f [] \<sigma> = \<sigma>" |
  "ls_iteratei c f (x#l) \<sigma> = (if c \<sigma> then ls_iteratei c f l (f x \<sigma>) else \<sigma>)"

definition ls_iterate :: "('a ls,'a,'\<sigma>) iterator" 
  where "ls_iterate == iti_iterate ls_iteratei"

definition ls_isEmpty :: "'a ls \<Rightarrow> bool" where "ls_isEmpty s == s=[]"

definition ls_union :: "'a ls \<Rightarrow> 'a ls \<Rightarrow> 'a ls" 
  where "ls_union == it_union ls_iterate ls_ins"
definition ls_inter :: "'a ls \<Rightarrow> 'a ls \<Rightarrow> 'a ls" 
  where "ls_inter == it_inter ls_iterate ls_memb ls_empty ls_ins_dj"
definition ls_union_dj :: "'a ls \<Rightarrow> 'a ls \<Rightarrow> 'a ls" 
  where "ls_union_dj s1 s2 == revg s1 s2" -- "Union of disjoint sets"

definition ls_image_filter 
  where "ls_image_filter == it_image_filter ls_iterate ls_empty ls_ins"

definition ls_inj_image_filter 
  where "ls_inj_image_filter == it_inj_image_filter ls_iterate ls_empty ls_ins_dj"

definition "ls_image == iflt_image ls_image_filter"
definition "ls_inj_image == iflt_inj_image ls_inj_image_filter"

definition ls_ball :: "'a ls \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "ls_ball l P == list_all P l"
definition ls_sel :: "'a ls \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "ls_sel == iti_sel ls_iteratei"

definition ls_to_list :: "'a ls \<Rightarrow> 'a list" where "ls_to_list == id"
definition list_to_ls :: "'a list \<Rightarrow> 'a ls" where "list_to_ls == remdups"

definition "ls_size == it_size ls_iterate"

subsection "Correctness"
lemmas ls_defs = 
  ls_\<alpha>_def
  ls_invar_def
  ls_empty_def
  ls_memb_def
  ls_ins_def
  ls_ins_dj_def
  ls_delete_def
  ls_iterate_def
  ls_isEmpty_def
  ls_union_def
  ls_inter_def
  ls_union_dj_def
  ls_image_filter_def
  ls_inj_image_filter_def
  ls_image_def
  ls_inj_image_def
  ls_ball_def
  ls_sel_def
  ls_to_list_def
  list_to_ls_def
  ls_size_def

lemma ls_empty_impl: "set_empty ls_\<alpha> ls_invar ls_empty"
  apply (unfold_locales)
  apply (auto simp add: ls_defs)
  done

lemma ls_memb_impl: "set_memb ls_\<alpha> ls_invar ls_memb"
  apply (unfold_locales)                                     
  apply (auto simp add: ls_defs mem_iff)                             
  done                                                       

lemma ls_ins_impl: "set_ins ls_\<alpha> ls_invar ls_ins"
  apply (unfold_locales)                                  
  apply (auto simp add: ls_defs mem_iff)                          
  done                                                    

lemma ls_ins_dj_impl: "set_ins_dj ls_\<alpha> ls_invar ls_ins_dj"
  apply (unfold_locales)                                           
  apply (auto simp add: ls_defs)                                   
  done                                                             

lemma ls_delete_aux_impl:
  "distinct (res@l) 
      \<Longrightarrow> distinct (ls_delete_aux x res l) 
          \<and> (set (ls_delete_aux x res l) = set res \<union> (set l - {x}))"
      by (induct l arbitrary: res) (auto)

lemma ls_delete_impl: "set_delete ls_\<alpha> ls_invar ls_delete"
  by (unfold_locales)
     (simp_all add: ls_defs ls_delete_aux_impl)

lemma ls_\<alpha>_finite[simp, intro!]: "finite (ls_\<alpha> l)"
  by (auto simp add: ls_defs)                                   

lemma ls_is_finite_set: "finite_set ls_\<alpha> ls_invar"
  apply (unfold_locales)                                           
  apply (auto simp add: ls_defs)                                   
  done                                                             

lemma ls_iteratei_impl: "set_iteratei ls_\<alpha> ls_invar ls_iteratei"
  apply (unfold_locales)
  apply (simp add: ls_defs)
proof -
  case (goal1 S I \<sigma> c f)
  {
    fix it
    assume 
      "it\<supseteq>ls_\<alpha> S"
      "I it \<sigma>"
      "\<forall>\<sigma> x it'. c \<sigma> \<and> x\<in>it' \<and> it' \<subseteq> it \<and> I it' \<sigma> \<longrightarrow> I (it' - {x}) (f x \<sigma>)"
    moreover note `ls_invar S` 
    ultimately have "I (it-ls_\<alpha> S) (ls_iteratei c f S \<sigma>) 
      \<or> (\<exists>it'\<subseteq>it. it'\<noteq>{} \<and> \<not>c (ls_iteratei c f S \<sigma>) \<and> I it' (ls_iteratei c f S \<sigma>))"
    proof (induct S arbitrary: it \<sigma>)
      case Nil thus ?case
        by (auto simp add: ls_defs)
    next
      case (Cons x S)
      show ?case proof (cases "c \<sigma>")
        case False with Cons.prems show ?thesis
          by auto
      next
        case True
        from Cons.prems(3)[rule_format, of \<sigma> x it] True Cons.prems(1-2) 
        have I': "I (it - {x}) (f x \<sigma>)" by (auto simp add: ls_defs)

        from Cons.prems(1) Cons.prems(4) have PP: "ls_\<alpha> S \<subseteq> it - {x}" "ls_invar S"
          by (auto simp add: ls_defs)

        from Cons.prems(3) have 
          IPRES': "\<forall>\<sigma> xa it'. 
                     c \<sigma> 
                     \<and> xa \<in> it' 
                     \<and> it' \<subseteq> it - {x} 
                     \<and> I it' \<sigma> 
                    \<longrightarrow> I (it' - {xa}) (f xa \<sigma>)"
          by auto

        from Cons.hyps[OF PP(1) I' IPRES' PP(2)] 
        have "I (it - {x} - ls_\<alpha> S) (ls_iteratei c f S (f x \<sigma>)) 
          \<or> (\<exists>it'. it' \<subseteq> it - {x} \<and> it' \<noteq> {} \<and> \<not> c (ls_iteratei c f S (f x \<sigma>)) \<and> I it' (ls_iteratei c f S (f x \<sigma>)))"
          (is "?C1 \<or> ?C2") .
        moreover {
          assume ?C1 hence ?thesis 
            by (auto simp add: ls_defs True set_diff_diff_left)
        } moreover {
          assume ?C2 
          then obtain it' where INT:
            "it'\<subseteq>it-{x}" 
            "it'\<noteq>{}" 
            "\<not>c (ls_iteratei c f S (f x \<sigma>))" 
            "I it' (ls_iteratei c f S (f x \<sigma>))"
            by blast

          hence ?thesis
            apply (rule_tac disjI2)
            apply (rule_tac x=it' in exI)
            apply (auto simp add: True)
            done
        } ultimately show ?thesis by blast
      qed
    qed
  } note R=this
  from R[OF subset_refl] goal1 show ?case by auto
qed

lemmas ls_iterate_impl = set_iteratei.iti_iterate_correct[OF ls_iteratei_impl, folded ls_iterate_def]

lemma ls_isEmpty_impl: "set_isEmpty ls_\<alpha> ls_invar ls_isEmpty"
  apply (unfold_locales)                                              
  apply (auto simp add: ls_defs)                                      
  done                                                                

lemmas ls_union_impl = it_union_correct[OF ls_iterate_impl ls_ins_impl, folded ls_union_def] 

lemmas ls_inter_impl = it_inter_correct[OF ls_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded ls_inter_def]

lemma ls_union_dj_impl: "set_union_dj ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_union_dj"
  apply (unfold_locales)                                                 
  apply (auto simp add: ls_defs)                                         
  done                                                                   

lemmas ls_image_filter_impl = it_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_impl, folded ls_image_filter_def]
lemmas ls_inj_image_filter_impl = it_inj_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ls_inj_image_filter_def]

lemmas ls_image_impl = iflt_image_correct[OF ls_image_filter_impl, folded ls_image_def]
lemmas ls_inj_image_impl = iflt_inj_image_correct[OF ls_inj_image_filter_impl, folded ls_inj_image_def]

lemma ls_ball_impl: "set_ball ls_\<alpha> ls_invar ls_ball"
  apply (unfold_locales)                                     
  apply (auto simp add: ls_defs list_all_iff)                             
  done                                                       

lemmas ls_sel_impl = iti_sel_correct[OF ls_iteratei_impl, folded ls_sel_def]

lemma ls_to_list_impl: "set_to_list ls_\<alpha> ls_invar ls_to_list"
  apply (unfold_locales)
  apply (auto simp add: ls_defs)
  done

lemma list_to_ls_impl: "list_to_set ls_\<alpha> ls_invar list_to_ls"
  apply (unfold_locales)
  apply (auto simp add: ls_defs)
  done

lemmas ls_size_impl = it_size_correct[OF ls_iterate_impl, folded ls_size_def]


interpretation ls: set_empty ls_\<alpha> ls_invar ls_empty using ls_empty_impl .
interpretation ls: set_memb ls_\<alpha> ls_invar ls_memb using ls_memb_impl .   
interpretation ls: set_ins ls_\<alpha> ls_invar ls_ins using ls_ins_impl .      
interpretation ls: set_ins_dj ls_\<alpha> ls_invar ls_ins_dj using ls_ins_dj_impl .
interpretation ls: set_delete ls_\<alpha> ls_invar ls_delete using ls_delete_impl .
interpretation ls: finite_set ls_\<alpha> ls_invar using ls_is_finite_set .
interpretation ls: set_iteratei ls_\<alpha> ls_invar ls_iteratei using ls_iteratei_impl .
interpretation ls: set_iterate ls_\<alpha> ls_invar ls_iterate using ls_iterate_impl .
interpretation ls: set_isEmpty ls_\<alpha> ls_invar ls_isEmpty using ls_isEmpty_impl .
interpretation ls: set_union ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_union using ls_union_impl .
interpretation ls: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_inter using ls_inter_impl .
interpretation ls: set_union_dj ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_union_dj using ls_union_dj_impl .
interpretation ls: set_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_image_filter using ls_image_filter_impl .
interpretation ls: set_inj_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_inj_image_filter using ls_inj_image_filter_impl .
interpretation ls: set_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_image using ls_image_impl .
interpretation ls: set_inj_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_inj_image using ls_inj_image_impl .
interpretation ls: set_ball ls_\<alpha> ls_invar ls_ball using ls_ball_impl .
interpretation ls: set_sel ls_\<alpha> ls_invar ls_sel using ls_sel_impl .
interpretation ls: set_to_list ls_\<alpha> ls_invar ls_to_list using ls_to_list_impl .
interpretation ls: list_to_set ls_\<alpha> ls_invar list_to_ls using list_to_ls_impl .
interpretation ls: set_size ls_\<alpha> ls_invar ls_size using ls_size_impl .

declare ls.finite[simp del, rule del]


lemmas ls_correct =
  ls.empty_correct                                                                                                 
  ls.memb_correct                                                                                                  
  ls.ins_correct                                                                                                   
  ls.ins_dj_correct
  ls.delete_correct
  ls.isEmpty_correct
  ls.union_correct
  ls.inter_correct
  ls.union_dj_correct
  ls.image_filter_correct
  ls.inj_image_filter_correct
  ls.image_correct
  ls.inj_image_correct
  ls.ball_correct
  ls.to_list_correct
  ls.to_set_correct
  ls.size_correct


subsection "Code Generation"

export_code
  ls_empty
  ls_memb
  ls_ins
  ls_ins_dj
  ls_delete_aux
  ls_delete
  ls_iteratei
  ls_iterate
  ls_isEmpty
  ls_union
  ls_inter
  ls_union_dj
  ls_image_filter
  ls_inj_image_filter
  ls_image
  ls_inj_image
  ls_ball
  ls_sel
  ls_to_list
  list_to_ls
  ls_size
  in SML
  module_name ListSet
  file -

end
