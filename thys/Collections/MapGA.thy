(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedMap, algorithms for iterators, min, max, to_sorted_list

*)

header {* \chapter{Generic algorithms} \label{ch:GA} \isaheader{Generic Algorithms for Maps} *}
theory MapGA
imports MapSpec OrderedMap "common/Misc"
begin
text_raw {*\label{thy:MapGA}*}

subsection {*Disjoint Update (by update)*}
lemma (in map_update) update_dj_by_update: 
  "map_update_dj \<alpha> invar update"
  apply (unfold_locales)
  apply (auto simp add: update_correct)
  done

subsection {*Disjoint Add (by add)*}
lemma (in map_add) add_dj_by_add: 
  "map_add_dj \<alpha> invar add"
  apply (unfold_locales)
  apply (auto simp add: add_correct)
  done

subsection {*Add (by iterate)*}
definition it_add 
  :: "('u \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s,'u,'v,'s) map_iterator \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" 
  where "it_add update iterate m1 m2 = iterate update m2 m1"

lemma it_add_correct:
  fixes \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  assumes "map_iterate \<alpha> invar iterate"
  assumes "map_update \<alpha> invar update"
  shows "map_add \<alpha> invar (it_add update iterate)"
proof -
  interpret map_update \<alpha> invar update by fact
  interpret map_iterate \<alpha> invar iterate by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold it_add_def)
    apply (rule_tac 
      I="\<lambda>it m. invar m \<and> \<alpha> m = \<alpha> m1 ++ (\<alpha> m2 |` (- it))" and 
      m=m2 and ?\<sigma>0.0=m1 and f=update  
      in iterate_rule_P)
    apply (auto simp add: update_correct)
    apply (auto simp add: map_add_upd[symmetric] restrict_map_upd map_upd_triv 
                simp del: map_add_upd restrict_fun_upd)
    apply (rule_tac 
      I="\<lambda>it m. invar m" and m=m2 and ?\<sigma>0.0=m1 and f=update  
      in iterate_rule_P)
    apply (auto simp add: update_correct)
    done
qed

subsection {*Disjoint Add (by iterate)*}
definition it_add_dj
  :: "('u \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s,'u,'v,'s) map_iterator \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" 
  where "it_add_dj update_dj iterate m1 m2 = iterate update_dj m2 m1"

lemma it_add_dj_correct:
  fixes \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  assumes "map_iterate \<alpha> invar iterate"
  assumes "map_update_dj \<alpha> invar update"
  shows "map_add_dj \<alpha> invar (it_add_dj update iterate)"
proof -
  interpret map_update_dj \<alpha> invar update by fact
  interpret map_iterate \<alpha> invar iterate by fact

  {
    fix m1 m2
    have "\<lbrakk>invar m1; invar m2; dom (\<alpha> m1) \<inter> dom (\<alpha> m2) = {}\<rbrakk> 
      \<Longrightarrow> \<alpha> (it_add_dj update iterate m1 m2) = \<alpha> m1 ++ \<alpha> m2 
          \<and> invar (it_add_dj update iterate m1 m2)"
      apply (unfold it_add_dj_def)
      apply (rule_tac 
        I="\<lambda>it m. invar m \<and> \<alpha> m = \<alpha> m1 ++ (\<alpha> m2 |` (- it))" and 
        m=m2 and ?\<sigma>0.0=m1 and f=update  
        in iterate_rule_P)
      apply (simp_all add: update_dj_correct)
      apply (subgoal_tac "k\<notin>dom (\<alpha> \<sigma>)")
      apply (auto simp add: update_dj_correct) [1]
      apply (auto 
        simp add: map_add_upd[symmetric] restrict_map_upd map_upd_triv 
        simp del: map_add_upd restrict_fun_upd) [1]
      apply fastsimp
      done
  } thus ?thesis
    by unfold_locales auto
qed

subsection {*Emptiness check (by iteratei)*}
definition iti_isEmpty 
  :: "('m,'k,'v,bool) map_iteratori \<Rightarrow> 'm \<Rightarrow> bool"
  where "iti_isEmpty iti m == iti id (\<lambda>k v res. False) m True"

lemma iti_isEmpty_correct:
  assumes "map_iteratei \<alpha> invar iti"
  shows "map_isEmpty \<alpha> invar (iti_isEmpty iti)"
proof -
  interpret map_iteratei \<alpha> invar iti by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold iti_isEmpty_def)
    apply (rule_tac I="\<lambda>it res. res \<longleftrightarrow> dom (\<alpha> m) - it = {}" in iteratei_rule_P)
    apply auto
    done
qed

subsection {* Iterators *}
subsubsection {*iterate (by iteratei)*}
definition iti_iterate
  :: "('m,'k,'v,'\<sigma>) map_iteratori \<Rightarrow> ('m,'k,'v,'\<sigma>) map_iterator"
  where "iti_iterate iti == iti (\<lambda>x. True)"

lemma (in map_iteratei) iti_iterate_correct: 
  "map_iterate \<alpha> invar (iti_iterate iteratei)"
  apply (unfold_locales)
  apply (unfold iti_iterate_def)
  apply (rule_tac I=I in iteratei_rule_P)
  apply auto
  done


subsubsection {*iteratei (by iterate)*}
  -- "Interruptible iterator by iterator (Inefficient)"
definition it_iteratei 
  :: "('m,'u,'v,bool \<times> '\<sigma>) map_iterator \<Rightarrow> ('m,'u,'v,'\<sigma>) map_iteratori" 
  where "it_iteratei iterate c f m \<sigma>0 == 
    snd (iterate (\<lambda>k v (flag,\<sigma>). 
                    if \<not>flag then (False,\<sigma>) 
                    else if (c \<sigma>) then (True,f k v \<sigma>) 
                    else (False,\<sigma>)) m (True,\<sigma>0)
        )"

lemma it_iteratei_correct:
  fixes empty
  assumes IT: "map_iterate \<alpha> invar iterate"
  shows "map_iteratei \<alpha> invar (it_iteratei iterate)"
proof -
  interpret map_iterate \<alpha> invar iterate using IT .
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_iteratei_def)
    apply (rule_tac 
      I="\<lambda>it (flag, \<sigma>). 
            (flag \<longrightarrow> I it \<sigma>) \<and> 
            (\<not>flag \<longrightarrow> (\<exists>it\<subseteq>dom (\<alpha> m). it\<noteq>{} \<and> \<not> c \<sigma> \<and> I it \<sigma>))" 
      in iterate_rule_P)
    apply simp
    apply simp
    apply (case_tac \<sigma>)
    apply (case_tac "c b")
    apply simp
    apply simp
    apply (case_tac a)
    apply simp
    apply (rule_tac x=it in exI)
    apply simp
    apply blast
    apply simp
    apply (case_tac \<sigma>)
    apply auto [1]
    done
qed

subsubsection {* Iteratei (by iterateoi) *}
lemma iti_by_itoi: 
  assumes "map_iterateoi \<alpha> invar it"
  shows "map_iteratei \<alpha> invar it"
proof -
  interpret map_iterateoi \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in iterateoi_rule_P)
    apply blast+
    done
qed

subsubsection {* Iterate (by iterateo) *}
lemma it_by_ito: 
  assumes "map_iterateo \<alpha> invar it"
  shows "map_iterate \<alpha> invar it"
proof -
  interpret map_iterateo \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in iterateo_rule_P)
    apply blast+
    done
qed

subsubsection {* Iteratei (by reverse\_iterateoi) *}
lemma iti_by_ritoi: 
  assumes "map_reverse_iterateoi \<alpha> invar it"
  shows "map_iteratei \<alpha> invar it"
proof -
  interpret map_reverse_iterateoi \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in reverse_iterateoi_rule_P)
    apply blast+
    done
qed

subsubsection {* Iterate (by reverse\_iterateo) *}
lemma it_by_rito: 
  assumes "map_reverse_iterateo \<alpha> invar it"
  shows "map_iterate \<alpha> invar it"
proof -
  interpret map_reverse_iterateo \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in reverse_iterateo_rule_P)
    apply blast+
    done
qed

subsubsection {* iterateo by iterateoi *}
definition itoi_iterateo
  :: "('m,'u,'v,'\<sigma>) map_iteratori \<Rightarrow> ('m,'u,'v,'\<sigma>) map_iterator"
  where
  "itoi_iterateo it == it (\<lambda>x. True)"

lemma (in map_iterateoi) itoi_iterateo_correct:
  shows "map_iterateo \<alpha> invar (itoi_iterateo iterateoi)"
  apply (unfold_locales)
  apply (unfold itoi_iterateo_def)
  apply (rule_tac I=I in iterateoi_rule_P)
  apply auto
  done

subsubsection {* reverse\_iterateo by reverse\_iterateoi *}
definition itoi_reverse_iterateo
  :: "('m,'u,'v,'\<sigma>) map_iteratori \<Rightarrow> ('m,'u,'v,'\<sigma>) map_iterator"
  where
  "itoi_reverse_iterateo it == it (\<lambda>x. True)"

lemma (in map_reverse_iterateoi) itoi_reverse_iterateo_correct:
  shows "map_reverse_iterateo \<alpha> invar (itoi_reverse_iterateo reverse_iterateoi)"
  apply (unfold_locales)
  apply (unfold itoi_reverse_iterateo_def)
  apply (rule_tac I=I in reverse_iterateoi_rule_P)
  apply auto
  done

subsection {*Selection (by iteratei)*}
definition iti_sel ::
  "('s,'k,'v,_) map_iteratori \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 'r option) \<rightharpoonup> 'r"
where "iti_sel iti m f == 
  iti (\<lambda>r. r=None) (\<lambda>k v res. f k v) m None
"

lemma iti_sel_correct:
  assumes "map_iteratei \<alpha> invar iti"
  shows "map_sel \<alpha> invar (iti_sel iti)"
proof -
  interpret map_iteratei \<alpha> invar iti by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold iti_sel_def)
    defer
    apply (rule_tac I="\<lambda>it res. res=None" in iteratei_rule_P)
    apply auto[5]
  proof -
    case goal1
    from goal1(1,2,3) have 
      "\<exists>k v r. iti (\<lambda>r. r=None) (\<lambda>k v res. f k v) m None = Some r 
        \<and> \<alpha> m k = Some v
        \<and> f k v = Some r"
      apply (rule_tac 
        I="\<lambda>it res. 
          case res of
            None \<Rightarrow> \<forall>k v. k\<notin>it \<and> \<alpha> m k = Some v \<longrightarrow> f k v = None |
            Some r \<Rightarrow> \<exists>k v. k\<notin>it \<and> \<alpha> m k = Some v \<and> f k v = Some r" 
        in iteratei_rule_P)
      apply (simp_all split: option.split option.split_asm)
      apply auto
      done
    thus ?case 
      apply (elim exE)
      apply (rule_tac goal1(4))
      apply auto
      done
  qed
qed

subsection {* Map-free selection by selection *}
definition sel_sel'
  :: "('s \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> _ option) \<Rightarrow> _ option) \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('k\<times>'v) option"
where "sel_sel' sel s P = sel s (\<lambda>k v. if P k v then Some (k,v) else None)"

lemma sel_sel'_correct: 
  assumes "map_sel \<alpha> invar sel"
  shows "map_sel' \<alpha> invar (sel_sel' sel)"
proof -
  interpret map_sel \<alpha> invar sel by fact

  show ?thesis
  proof
    case goal1 show ?case
      apply (rule selE[OF goal1(1,2), where f="(\<lambda>k v. if P k v then Some (k,v) else None)"])
      apply (simp add: goal1)
      apply (simp split: split_if_asm)
      apply (fold sel_sel'_def)
      apply (blast intro: goal1(4))
      done
  next
    case goal2 thus ?case
      apply (auto simp add: sel_sel'_def)
      apply (drule selI[where f="(\<lambda>k v. if P k v then Some (k,v) else None)"])
      apply auto
      done
  qed
qed

subsection {*Bounded Quantification (by sel)*}
definition sel_ball 
  :: "('s \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> unit option) \<rightharpoonup> unit) \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  where "sel_ball sel s P == sel s (\<lambda>k v. if \<not>P k v then Some () else None) = None"

lemma sel_ball_correct:
  assumes "map_sel \<alpha> invar sel"
  shows "map_ball \<alpha> invar (sel_ball sel)"
proof -
  interpret map_sel \<alpha> invar sel by fact
  
  show ?thesis
    apply unfold_locales
    apply (unfold sel_ball_def)
    apply (auto elim: sel_someE dest: sel_noneD split: split_if_asm)
    done
qed

subsection {*Map to List (by iterate)*}
definition it_map_to_list
  :: "('m,'u,'v,('u\<times>'v) list) map_iterator \<Rightarrow> 'm \<Rightarrow> ('u\<times>'v) list"
  where "it_map_to_list iterate m == iterate (\<lambda>u v res. (u,v)#res) m []"

lemma it_map_to_list_correct:
  assumes "map_iterate \<alpha> invar iterate"
  shows "map_to_list \<alpha> invar (it_map_to_list iterate)"
proof -
  interpret map_iterate \<alpha> invar iterate by fact
  show ?thesis
    apply unfold_locales
    apply (unfold it_map_to_list_def)
    apply (rule_tac I="\<lambda>it res. map_of res = \<alpha> m |` (-it)" in iterate_rule_P)
    apply (auto 
      simp add: restrict_map_def 
                not_None_eq[simplified eq_commute[of _ None]] 
      intro!: ext) [4]
    apply (rule_tac 
      I="\<lambda>it res. set (map fst res) \<inter> it = {} \<and> distinct (map fst res)" 
      in iterate_rule_P)
    apply auto
    done
qed

subsection {*List to Map*}

(* Tail recursive version *)
fun gen_list_to_map_aux
  :: "('k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> ('k\<times>'v) list \<Rightarrow> 'm"
  where
  "gen_list_to_map_aux upd accs [] = accs" |
  "gen_list_to_map_aux upd accs ((k,v)#l) = gen_list_to_map_aux upd (upd k v accs) l"

definition "gen_list_to_map empt upd l == gen_list_to_map_aux upd empt (rev l)"

lemma gen_list_to_map_correct:
  assumes "map_empty \<alpha> invar empt"
  assumes "map_update \<alpha> invar upd"
  shows "list_to_map \<alpha> invar (gen_list_to_map empt upd)"
proof -
  interpret map_empty \<alpha> invar empt by fact
  interpret map_update \<alpha> invar upd by fact

  { -- "Show a generalized lemma"
    fix l accs
    have "invar accs \<Longrightarrow> \<alpha> (gen_list_to_map_aux upd accs l) = \<alpha> accs ++ map_of (rev l)
          \<and> invar (gen_list_to_map_aux upd accs l)"
     apply (induct l arbitrary: accs)
     apply simp
     apply (case_tac a)
     apply (simp add: update_correct)
     done
  } thus ?thesis
    apply (unfold_locales)
    apply (unfold gen_list_to_map_def)
    apply (auto simp add: empty_correct)
    done
qed

subsection {* Singleton (by empty, update) *}
(* TODO: It might make sense to define a singleton function as locale *)
definition map_sng
  :: "'m \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'm"
  where "map_sng empt update k v == update k v empt"

lemma map_sng_correct:
  fixes empty
  assumes "map_empty \<alpha> invar empty"
  assumes "map_update \<alpha> invar update"
  shows "\<alpha> (map_sng empty update k v) = [k \<mapsto> v]" (is ?T1)
        "invar (map_sng empty update k v)" (is ?T2)
proof -
  interpret map_empty \<alpha> invar empty by fact
  interpret map_update \<alpha> invar update by fact

  show ?T1 ?T2
    by (simp_all add: update_correct empty_correct map_sng_def)
qed

subsection {* Min (by iterateoi) *}
definition itoi_min :: "('s,'k::linorder,'v,_) map_iteratori \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('k\<times>'v) option"
  where "itoi_min it m P ==
    it (\<lambda>x. x=None) (\<lambda>k v res. if P k v then Some (k,v) else None) m None
  "

(* TODO: Move to def of rel_of *)
lemma rel_of_empty[simp]: "rel_of Map.empty P = {}" 
  by (auto simp add: rel_of_def)


lemma itoi_min_correct:
  assumes "map_iterateoi \<alpha> invar it"
  shows "map_min \<alpha> invar (itoi_min it)"
proof -
  interpret map_iterateoi \<alpha> invar it by fact
  
  show ?thesis 
    apply (unfold_locales)
    apply (unfold itoi_min_def)
    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> rel_of (\<alpha> s |`(-it)) P = {} | 
        Some (k,v) \<Rightarrow> (k,v)\<in>rel_of (\<alpha> s) P 
                      \<and> (\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<le> k')"
      in iterateoi_rule_P)
    apply (auto 
      simp add: rel_of_def restrict_map_def 
      split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> rel_of (\<alpha> s |`(-it)) P = {} | 
        Some (k,v) \<Rightarrow> (k,v)\<in>rel_of (\<alpha> s) P 
                      \<and> (\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<le> k')"
      in iterateoi_rule_P)
    apply (auto 
      simp add: rel_of_def restrict_map_def 
      split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> rel_of (\<alpha> s |`(-it)) P = {} | 
        Some (k,v) \<Rightarrow> (k,v)\<in>rel_of (\<alpha> s) P 
                      \<and> (\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<le> k')"
      in iterateoi_rule_P)
    apply (auto 
      simp add: rel_of_def restrict_map_def 
      split: option.split_asm) [5]
    done
qed


subsection {* Max (by reverse\_iterateoi) *}
definition ritoi_max :: "('s,'k::linorder,'v,_) map_iteratori \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('k\<times>'v) option"
  where "ritoi_max it m P ==
    it (\<lambda>x. x=None) (\<lambda>k v res. if P k v then Some (k,v) else None) m None
  "

lemma ritoi_max_correct:
  assumes "map_reverse_iterateoi \<alpha> invar it"
  shows "map_max \<alpha> invar (ritoi_max it)"
proof -
  interpret map_reverse_iterateoi \<alpha> invar it by fact
  
  show ?thesis 
    apply (unfold_locales)
    apply (unfold ritoi_max_def)
    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> rel_of (\<alpha> s |`(-it)) P = {} | 
        Some (k,v) \<Rightarrow> (k,v)\<in>rel_of (\<alpha> s) P 
                      \<and> (\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<ge> k')"
      in reverse_iterateoi_rule_P)
    apply (auto 
      simp add: rel_of_def restrict_map_def 
      split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> rel_of (\<alpha> s |`(-it)) P = {} | 
        Some (k,v) \<Rightarrow> (k,v)\<in>rel_of (\<alpha> s) P 
                      \<and> (\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<ge> k')"
      in reverse_iterateoi_rule_P)
    apply (auto 
      simp add: rel_of_def restrict_map_def 
      split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> rel_of (\<alpha> s |`(-it)) P = {} | 
        Some (k,v) \<Rightarrow> (k,v)\<in>rel_of (\<alpha> s) P 
                      \<and> (\<forall>(k',v')\<in>rel_of (\<alpha> s) P. k \<ge> k')"
      in reverse_iterateoi_rule_P)
    apply (auto 
      simp add: rel_of_def restrict_map_def 
      split: option.split_asm) [5]

    done
qed


subsection {* Conversion to sorted list (by reverse\_iterateo) *}

definition rito_map_to_sorted_list
  :: "('m,'u,'v,('u\<times>'v) list) map_iterator \<Rightarrow> 'm \<Rightarrow> ('u\<times>'v) list"
  where "rito_map_to_sorted_list iterate m == iterate (\<lambda>u v res. (u,v)#res) m []"

lemma rito_map_to_sorted_list_correct:
  assumes "map_reverse_iterateo \<alpha> invar iterate"
  shows "map_to_sorted_list \<alpha> invar (rito_map_to_sorted_list iterate)"
proof -
  interpret map_reverse_iterateo \<alpha> invar iterate by fact
  show ?thesis
    apply unfold_locales
    apply (unfold rito_map_to_sorted_list_def)
    apply (rule_tac I="\<lambda>it res. map_of res = \<alpha> m |` (-it)" in reverse_iterateo_rule_P)
    apply (auto 
      simp add: restrict_map_def 
                not_None_eq[simplified eq_commute[of _ None]] 
      intro!: ext) [4]
    apply (rule_tac 
      I="\<lambda>it res. set (map fst res) \<inter> it = {} \<and> distinct (map fst res)" 
      in reverse_iterateo_rule_P)
    apply auto
    apply (rule_tac 
      I="\<lambda>it res. set (map fst res) = dom (\<alpha> m) - it \<and> sorted (map fst res)" 
      in reverse_iterateo_rule_P)
    apply (auto simp add: sorted_Cons)
    done
qed

end
