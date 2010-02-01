(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Map Implementation by Association Lists *}
theory ListMapImpl
imports Main MapSpec AssocList MapGA
begin
text_raw {*\label{thy:ListMapImpl}*}

text {*
  In this theory, we implement maps by lists of (key,value) pairs.

  This implementation uses the abbreviations: lm, l
 *}

types ('k,'v) lm = "('k\<times>'v) list"

subsection "Functions"

definition "lm_\<alpha> == Map.map_of"
definition "lm_invar m == distinct (List.map fst m)"
definition "lm_empty == []"
definition "lm_lookup k m == Map.map_of m k"
definition "lm_update == AssocList.update"
definition "lm_update_dj k v m == (k,v)#m"  
definition "lm_delete k m == AssocList.delete k m"
fun lm_iteratei :: "(('k,'v) lm,'k,'v,'\<sigma>) map_iteratori" where
  "lm_iteratei c f [] \<sigma> = \<sigma>" |
  "lm_iteratei c f ((k,v)#l) \<sigma> = 
    (if c \<sigma> then lm_iteratei c f l (f k v \<sigma>) else \<sigma>)"

definition "lm_iterate == iti_iterate lm_iteratei"
definition "lm_isEmpty m == m=[]"

definition "lm_add == it_add lm_update lm_iterate"
definition lm_add_dj :: "('k,'v) lm \<Rightarrow> ('k,'v) lm \<Rightarrow> ('k,'v) lm" 
  where "lm_add_dj m1 m2 == revg m1 m2" 

definition "lm_sel == iti_sel lm_iteratei"
definition "lm_ball == sel_ball lm_sel"
definition lm_to_list :: "('u,'v) lm \<Rightarrow> ('u\<times>'v) list"
  where "lm_to_list = id"
definition "list_to_lm == gen_list_to_map lm_empty lm_update"
definition list_to_lm_dj :: "('u\<times>'v) list \<Rightarrow> ('u,'v) lm"
  where "list_to_lm_dj == id"
definition "lm_sng == map_sng lm_empty lm_update"


subsection "Correctness"
lemmas lm_defs =
  lm_\<alpha>_def
  lm_invar_def
  lm_empty_def
  lm_lookup_def
  lm_update_def
  lm_update_dj_def
  lm_delete_def
  lm_isEmpty_def
  lm_add_def
  lm_add_dj_def
  lm_sel_def
  lm_ball_def
  lm_to_list_def
  list_to_lm_def
  list_to_lm_dj_def

lemma lm_empty_impl: 
  "map_empty lm_\<alpha> lm_invar lm_empty"
  apply (unfold_locales)
  apply (auto 
    simp add: lm_defs AssocList.update_conv' AssocList.distinct_update)
  done

interpretation lm: map_empty lm_\<alpha> lm_invar lm_empty using lm_empty_impl .

lemma lm_lookup_impl: 
  "map_lookup lm_\<alpha> lm_invar lm_lookup"
  apply (unfold_locales)
  apply (auto 
    simp add: lm_defs AssocList.update_conv' AssocList.distinct_update)
  done

interpretation lm: map_lookup lm_\<alpha> lm_invar lm_lookup using lm_lookup_impl .

lemma lm_update_impl: 
  "map_update lm_\<alpha> lm_invar lm_update"
  apply (unfold_locales)
  apply (auto 
    simp add: lm_defs AssocList.update_conv' AssocList.distinct_update)
  done

interpretation lm: map_update lm_\<alpha> lm_invar lm_update using lm_update_impl .

lemma lm_update_dj_impl: 
  "map_update_dj lm_\<alpha> lm_invar lm_update_dj"
  apply (unfold_locales)
  apply (auto simp add: lm_defs)
  done

interpretation lm: map_update_dj lm_\<alpha> lm_invar lm_update_dj using lm_update_dj_impl .

lemma lm_delete_impl: 
  "map_delete lm_\<alpha> lm_invar lm_delete"
  apply (unfold_locales)
  apply (auto simp add: lm_defs AssocList.update_conv' AssocList.distinct_update
                        AssocList.delete_conv' AssocList.distinct_delete)
  done

interpretation lm: map_delete lm_\<alpha> lm_invar lm_delete using lm_delete_impl .

lemma lm_isEmpty_impl: 
  "map_isEmpty lm_\<alpha> lm_invar lm_isEmpty"
  apply (unfold_locales)
  apply (unfold lm_defs)
  apply (case_tac m)
  apply auto
  done

interpretation lm: map_isEmpty lm_\<alpha> lm_invar lm_isEmpty using lm_isEmpty_impl .

lemma lm_iteratei_impl: 
  "map_iteratei lm_\<alpha> lm_invar lm_iteratei"
proof -
  show ?thesis
    apply (unfold_locales)
    apply (unfold lm_\<alpha>_def)
    apply simp
  proof -
    case goal1
    thus ?case proof (induct m arbitrary: \<sigma>0)
      case Nil thus ?case by simp
    next
      case (Cons p m)
      obtain k v where PFMT[simp]: "p=(k,v)" by (cases p) auto
      from Cons.prems(2) have I': "I (insert k (dom (Map.map_of m))) \<sigma>0"
        by (simp del: Map.map_of.simps add: dom_map_of_conv_image_fst)
      {
        assume C[simp]: "c \<sigma>0"
        have "lm_iteratei c f (p # m) \<sigma>0 = lm_iteratei c f m (f k v \<sigma>0)"
          by simp

        from Cons.prems(1) have INVN: "lm_invar m" 
          by (unfold lm_invar_def) auto
        from Cons.prems(1) have KNID: "k\<notin>dom (Map.map_of m)"
          by (unfold lm_invar_def)
             (simp add: dom_map_of_conv_image_fst)
        have IN: "I (dom (Map.map_of m)) (f k v \<sigma>0)" 
        proof -
          have "I (insert k (dom (Map.map_of m)) - {k}) (f k v \<sigma>0)"
            by (rule Cons.prems(3)[OF _ _ _ _ I', of k v])
               auto
          with KNID show ?thesis by auto
        qed
        have "I {} (lm_iteratei c f m (f k v \<sigma>0)) \<or> 
              (\<exists>it. it \<subseteq> dom (Map.map_of m) \<and> it \<noteq> {} \<and> 
                    \<not> c (lm_iteratei c f m (f k v \<sigma>0)) \<and> 
                    I it (lm_iteratei c f m (f k v \<sigma>0)))" 
          using KNID
          apply (rule_tac Cons.hyps[OF INVN IN])
          apply (rule Cons.prems(3))
          apply auto
          done
        hence ?case proof
          case goal1 thus ?case by simp
        next
          case goal2 then obtain it where 
            C: "it\<subseteq>dom (Map.map_of m)" "it \<noteq> {}" 
               "\<not> c (lm_iteratei c f m (f k v \<sigma>0))" 
               "I it (lm_iteratei c f m (f k v \<sigma>0))" 
            by blast
          hence "it \<subseteq> dom (Map.map_of (p # m))" "it \<noteq> {}" 
                "\<not> c (lm_iteratei c f (p # m) \<sigma>0)" 
                "I it (lm_iteratei c f (p # m) \<sigma>0)"
            by auto
          thus ?case by blast
        qed
      } moreover {
        assume C[simp]: "\<not> c \<sigma>0"
        have IF: "lm_iteratei c f (p # m) \<sigma>0 = \<sigma>0" by simp
        from Cons(3) have ?case
          apply (rule_tac disjI2)
          apply (rule_tac x="dom (Map.map_of (p # m))" in exI)
          apply (simp only: IF C)
          apply (intro conjI)
          apply blast
          apply auto
          done
      } ultimately show ?case by blast
    qed
  qed
qed

interpretation lm: map_iteratei lm_\<alpha> lm_invar lm_iteratei using lm_iteratei_impl .

lemma lm_is_finite_map: "finite_map lm_\<alpha> lm_invar" by unfold_locales auto
interpretation lm: finite_map lm_\<alpha> lm_invar using lm_is_finite_map .

lemmas lm_iterate_impl = lm.iti_iterate_correct[folded lm_iterate_def]
interpretation lm: map_iterate lm_\<alpha> lm_invar lm_iterate using lm_iterate_impl .

declare lm.finite[simp del, rule del]

lemma lm_finite[simp, intro!]: "finite (dom (lm_\<alpha> m))"
  by (auto simp add: lm_\<alpha>_def)

lemmas lm_add_impl = 
  it_add_correct[OF lm_iterate_impl lm_update_impl, folded lm_add_def]
interpretation lm: map_add lm_\<alpha> lm_invar lm_add using lm_add_impl .


lemma lm_add_dj_impl: 
  shows "map_add_dj lm_\<alpha> lm_invar lm_add_dj"
  apply (unfold_locales)
  apply (auto simp add: lm_defs)
  apply (blast intro: map_add_comm)
  apply (simp add: rev_map[symmetric])
  apply fastsimp
  done
  
interpretation lm: map_add_dj lm_\<alpha> lm_invar lm_add_dj using lm_add_dj_impl .

lemmas lm_sel_impl = iti_sel_correct[OF lm_iteratei_impl, folded lm_sel_def]
interpretation lm: map_sel lm_\<alpha> lm_invar lm_sel using lm_sel_impl .

lemmas lm_ball_impl = sel_ball_correct[OF lm_sel_impl, folded lm_ball_def]
interpretation lm: map_ball lm_\<alpha> lm_invar lm_ball using lm_ball_impl .

lemma lm_to_list_impl: "map_to_list lm_\<alpha> lm_invar lm_to_list"
  by (unfold_locales)
     (auto simp add: lm_defs)
interpretation lm: map_to_list lm_\<alpha> lm_invar lm_to_list using lm_to_list_impl .

lemmas list_to_lm_impl = 
  gen_list_to_map_correct[OF lm_empty_impl lm_update_impl, 
                          folded list_to_lm_def]

interpretation lm: list_to_map lm_\<alpha> lm_invar list_to_lm 
  using list_to_lm_impl .

lemma list_to_lm_dj_correct: 
  assumes [simp]: "distinct (map fst l)"
  shows "lm_\<alpha> (list_to_lm_dj l) = map_of l"
        "lm_invar (list_to_lm_dj l)"
  by (auto simp add: lm_defs)

lemma lm_to_list_to_lm[simp]: 
  "lm_invar m \<Longrightarrow> lm_\<alpha> (list_to_lm_dj (lm_to_list m)) = lm_\<alpha> m"
  by (simp add: lm.to_list_correct list_to_lm_dj_correct)

lemmas lm_sng_correct = map_sng_correct[OF lm_empty_impl lm_update_impl, folded lm_sng_def]

subsection "Code Generation"

fun lm_iterate_code :: "(('k,'v) lm,'k,'v,'\<sigma>) map_iterator" where
  "lm_iterate_code f [] \<sigma> = \<sigma>" |
  "lm_iterate_code f ((k,v)#l) \<sigma> = lm_iterate_code f l (f k v \<sigma>)"

lemma [code]: "lm_iterate = lm_iterate_code"
  apply (unfold lm_iterate_def iti_iterate_def)
proof (intro ext)
  fix f m \<sigma>0
  show "lm_iteratei (\<lambda>x. True) f m \<sigma>0 = lm_iterate_code f m \<sigma>0"
    apply (induct m arbitrary: \<sigma>0)
    apply auto
    done
qed

lemmas lm_correct = 
  lm.empty_correct
  lm.lookup_correct
  lm.update_correct
  lm.update_dj_correct
  lm.delete_correct
  lm.isEmpty_correct
  lm.add_correct
  lm.add_dj_correct
  lm.ball_correct
  lm.to_list_correct
  lm.to_map_correct
  list_to_lm_dj_correct
  lm_sng_correct

export_code
  lm_empty
  lm_lookup
  lm_update
  lm_update_dj
  lm_delete
  lm_isEmpty
  lm_iterate
  lm_iteratei
  lm_add
  lm_add_dj
  lm_sel
  lm_ball
  lm_to_list
  list_to_lm
  list_to_lm_dj
  lm_sng
  in SML
  module_name ListMap
  file -

end
