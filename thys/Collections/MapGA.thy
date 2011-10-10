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
      apply fastforce
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

definition sel_bexists
  :: "('s \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> unit option) \<rightharpoonup> unit) \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  where "sel_bexists sel s P == sel s (\<lambda>k v. if P k v then Some () else None) = Some ()"

lemma sel_bexists_correct:
  assumes "map_sel \<alpha> invar sel"
  shows "map_bexists \<alpha> invar (sel_bexists sel)"
proof -
  interpret map_sel \<alpha> invar sel by fact
  
  show ?thesis
    apply unfold_locales
    apply (unfold sel_bexists_def)
    apply auto
    apply (force elim!: sel_someE split: split_if_asm) []
    apply (erule_tac f="(\<lambda>k v. if P k v then Some () else None)" in selE)
    apply assumption
    apply simp
    apply simp
    done
qed

definition neg_ball_bexists
  :: "('s \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  where "neg_ball_bexists ball s P == \<not> (ball s (\<lambda>k v. \<not>(P k v)))"

lemma neg_ball_bexists_correct:
  fixes ball
  assumes "map_ball \<alpha> invar ball"
  shows "map_bexists \<alpha> invar (neg_ball_bexists ball)"
proof -
  interpret map_ball \<alpha> invar ball by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold neg_ball_bexists_def)
    apply (simp add: ball_correct)
  done
qed


subsection {* Size (by iterate)*}
definition it_size :: "('s,'k,'v,nat) map_iterator \<Rightarrow> 's \<Rightarrow> nat" 
  where "it_size iterate S == iterate (\<lambda>k v c. Suc c) S 0"

lemma it_size_correct:
  assumes A: "map_iterate \<alpha> invar iterate"
  shows "map_size \<alpha> invar (it_size iterate)"
proof -
  interpret map_iterate \<alpha> invar iterate by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (rule_tac I="\<lambda>it res. res = card (dom (\<alpha> s) - it)" in iterate_rule_P)
    apply auto
    apply (subgoal_tac "dom (\<alpha> s) - (it - {k}) = insert k (dom (\<alpha> s) - it)")
    apply auto
    done
qed

subsection {* Size with abort (by iterate) *}
definition iti_size_abort :: "('s,'k,'v,nat) map_iteratori \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> nat"
  where "iti_size_abort it m s == 
    (it (\<lambda>n. n < m) (\<lambda>k v n. Suc n) s 0)"

lemma iti_size_abort_correct:
  assumes S: "map_iteratei \<alpha> invar it"
  shows "map_size_abort \<alpha> invar (iti_size_abort it)"
proof - 
  interpret map_iteratei \<alpha> invar it by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold iti_size_abort_def)
  proof (rule_tac I="\<lambda>it res. res = min m (card (dom (\<alpha> s) - it))" in iteratei_rule_P)
    fix s m k v it \<sigma>
    assume "k\<in>it" and "it \<subseteq> dom (\<alpha> s)"
    hence "dom (\<alpha> s) - (it - {k}) = insert k (dom (\<alpha> s) - it)" by auto
    moreover assume "\<sigma><m" and "\<sigma> = min m (card (dom (\<alpha> s) - it))"
    moreover assume "invar s"
    ultimately show "Suc \<sigma> = min m (card (dom (\<alpha> s) - (it - {k})))"
      using `k\<in>it` 
      by auto
  next
    fix s m \<sigma> it
    assume [simp]: "invar s"
    assume "\<not>\<sigma><m" and [simp]: "\<sigma> = min m (card (dom (\<alpha> s) - it))"
    hence [simp]: "m \<le> (card (dom (\<alpha> s) - it))" by auto
    also have "\<dots> \<le> card (dom (\<alpha> s))"
      by (auto intro: card_mono)
    finally have "min m (card (dom (\<alpha> s))) = m"
      by auto
    thus "\<sigma> = min m (card (dom (\<alpha> s)))"
      by (auto simp: min_max.inf_absorb1)
  qed auto
qed

subsection {* Singleton check (by size-abort) *}
definition sza_isSng :: "(nat \<Rightarrow> 's \<Rightarrow> nat) \<Rightarrow> 's \<Rightarrow> bool"
  where "sza_isSng sza s == sza 2 s = 1"

lemma sza_isSng_correct:
  fixes \<alpha> :: "'s \<Rightarrow> 'k \<rightharpoonup> 'v"
  assumes S: "map_size_abort \<alpha> invar sza"
  shows "map_isSng \<alpha> invar (sza_isSng sza)"
proof -
  interpret map_size_abort \<alpha> invar sza
    by fact
  
  have "\<And>n::nat. min 2 n = 1 \<longleftrightarrow> n = 1" by auto
  thus ?thesis
    unfolding map_isSng_def sza_isSng_def
    by (simp add: size_abort_correct card_Suc_eq dom_eq_singleton_conv)
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
definition eu_sng
  :: "'m \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'm"
  where "eu_sng empt update k v == update k v empt"

lemma eu_sng_correct:
  fixes empty
  assumes "map_empty \<alpha> invar empty"
  assumes "map_update \<alpha> invar update"
  shows "map_sng \<alpha> invar (eu_sng empty update)"
proof -
  interpret map_empty \<alpha> invar empty by fact
  interpret map_update \<alpha> invar update by fact

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add: update_correct empty_correct eu_sng_def)
  done
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


subsection {* image restrict *}

definition it_map_image_filter ::
  "('s1,'u1,'v1,'s2) map_iterator \<Rightarrow> 's2 \<Rightarrow> ('u2 \<Rightarrow> 'v2 \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> ('u1 \<Rightarrow> 'v1 \<Rightarrow> ('u2 \<times> 'v2) option) \<Rightarrow> 's1 \<Rightarrow> 's2"
  where "it_map_image_filter map_it map_emp map_up_dj f m \<equiv>
         map_it (\<lambda>k v \<sigma>. case (f k v) of None \<Rightarrow> \<sigma> | Some (k', v') \<Rightarrow> (map_up_dj k' v' \<sigma>)) m map_emp"

lemma it_map_image_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'u1 \<rightharpoonup> 'v1"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'u2 \<rightharpoonup> 'v2" 
  assumes it: "map_iterate \<alpha>1 invar1 map_it"
  assumes emp: "map_empty \<alpha>2 invar2 map_emp"
  assumes up: "map_update_dj \<alpha>2 invar2 map_up_dj"
  shows "map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (it_map_image_filter map_it map_emp map_up_dj)"
proof -
  interpret it: map_iterate \<alpha>1 invar1 map_it using it .
  interpret emp: map_empty \<alpha>2 invar2 map_emp using emp .
  interpret up: map_update_dj \<alpha>2 invar2 map_up_dj using up .


  have "\<And>m f.
       \<lbrakk>invar1 m; transforms_to_unique_keys (\<alpha>1 m) f\<rbrakk>
       \<Longrightarrow> invar2 (it_map_image_filter map_it map_emp map_up_dj f m) \<and>
          (\<forall>k' v'. (\<alpha>2 (it_map_image_filter map_it map_emp map_up_dj f m) k' = Some v') =
                   (\<exists>k v. \<alpha>1 m k = Some v \<and> f k v = Some (k', v')))"
  proof -
    fix m :: 's1
    fix f :: "'u1 \<Rightarrow> 'v1 \<Rightarrow> ('u2 \<times> 'v2) option"
    assume invar_m : "invar1 m"
    assume tf_f : "transforms_to_unique_keys (\<alpha>1 m) f"
    let ?f' = "\<lambda>k v \<sigma>. case f k v of None \<Rightarrow> \<sigma> | Some (k', v') \<Rightarrow> map_up_dj k' v' \<sigma>"

    show "invar2 (it_map_image_filter map_it map_emp map_up_dj f m) \<and>
          (\<forall>k' v'. (\<alpha>2 (it_map_image_filter map_it map_emp map_up_dj f m) k' = Some v') =
                   (\<exists>k v. \<alpha>1 m k = Some v \<and> f k v = Some (k', v')))"
    unfolding it_map_image_filter_def
    proof (induct rule: it.iterate_rule_P [where I="\<lambda>d res. 
          invar2 res \<and>
          (\<forall>k' v'. (\<alpha>2 res k' = Some v') \<longleftrightarrow>  
                   (\<exists>k v. k \<notin> d \<and> \<alpha>1 m k = Some v \<and> f k v = Some (k', v')))"])

       case 1 thus ?case by (fact invar_m)
     next
       case 2 thus ?case by (auto simp add: emp.empty_correct domIff)
     next
       case 4 thus ?case by simp
     next
       case (3 k v d res)
       note k_in_d = 3(1)
       note m_k_eq = 3(2)
       note d_subset_dom = 3(3)
       note ind_hyp = 3(4)

       show "invar2 (?f' k v res) \<and>
             (\<forall>k' v'. (\<alpha>2 (?f' k v res) k' = Some v') \<longleftrightarrow>  
                      (\<exists>k'' v. k'' \<notin> d - {k} \<and> \<alpha>1 m k'' = Some v \<and> 
                               f k'' v = Some (k', v')))"
       proof (cases "f k v")
         case None thus ?thesis by (auto simp add: ind_hyp m_k_eq)
       next
         case (Some kv') note f_k_v_eq = this 
         then obtain k' v' where kv'_eq : "kv' = (k', v')" by (cases kv', blast)
         
         have "\<And>k2 v2 v2'.
                 \<lbrakk>\<alpha>1 m k2 = Some v2; 
                  f k2 v2 = Some (k', v2')\<rbrakk> \<Longrightarrow> k2 = k"
             by (metis f_k_v_eq [unfolded kv'_eq] m_k_eq tf_f[unfolded transforms_to_unique_keys_def])
         hence f_eq_k'_simp: "\<And>k2 v2 v2'.
                  (\<alpha>1 m k2 = Some v2 \<and> f k2 v2 = Some (k', v2') \<longleftrightarrow> (k2 = k  \<and> v2' = v' \<and> v2 = v))"
           by (metis Pair_eq f_k_v_eq [unfolded kv'_eq] m_k_eq Option.option.inject)

         have k'_nin_dom_res: "k' \<notin> dom (\<alpha>2 res)"
           by (simp add: domIff ind_hyp, metis k_in_d f_eq_k'_simp)

         from k'_nin_dom_res kv'_eq f_k_v_eq d_subset_dom show ?thesis 
            apply (simp add: up.update_dj_correct ind_hyp all_conj_distrib
                     f_eq_k'_simp)
            apply (auto)
            apply (auto simp add: f_k_v_eq kv'_eq m_k_eq)
         done
       qed
    qed
  qed

  thus ?thesis 
    apply (rule_tac map_image_filter.intro)
    apply auto
  done
qed


definition mif_map_value_image_filter :: 
  "(('u \<Rightarrow> 'v1 \<Rightarrow> ('u \<times> 'v2) option) \<Rightarrow> 's1 \<Rightarrow> 's2) \<Rightarrow>
    ('u \<Rightarrow> 'v1 \<Rightarrow> 'v2 option) \<Rightarrow> 's1 \<Rightarrow> 's2"
where
    "mif_map_value_image_filter mif f \<equiv>
     mif (\<lambda>k v. case (f k v) of Some v' \<Rightarrow> Some (k, v') | None \<Rightarrow> None)"


lemma mif_map_value_image_filter_correct :
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'u \<rightharpoonup> 'v1"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'u \<rightharpoonup> 'v2" 
shows "map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 mif \<Longrightarrow>
     map_value_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (mif_map_value_image_filter mif)"
proof -
  assume "map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 mif"
  then interpret map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 mif . 

  show "map_value_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (mif_map_value_image_filter mif)"
  proof (intro map_value_image_filter.intro conjI)
    fix m 
    fix f :: "'u \<Rightarrow> 'v1 \<Rightarrow> 'v2 option"
    assume invar: "invar1 m"

    let ?f = "\<lambda>k v. case (f k v) of Some v' \<Rightarrow> Some (k, v') | None \<Rightarrow> None"
    have unique_f: "transforms_to_unique_keys (\<alpha>1 m) ?f"
      unfolding transforms_to_unique_keys_def
      by (auto split: option.split)

    note correct' = map_image_filter_correct [OF invar unique_f, folded mif_map_value_image_filter_def]

    from correct' show "invar2 (mif_map_value_image_filter mif f m)"
      by simp

    have "\<And>k. \<alpha>2 (mif_map_value_image_filter mif f m) k = Option.bind (\<alpha>1 m k) (f k)"
    proof -
      fix k
      show "\<alpha>2 (mif_map_value_image_filter mif f m) k = Option.bind (\<alpha>1 m k) (f k)"
      using correct'
      apply (cases "Option.bind (\<alpha>1 m k) (f k)")
      apply (auto split: option.split)
      apply (case_tac "\<alpha>1 m k")
      apply (auto split: option.split)
      apply (metis option.inject)
      done
    qed
    thus "\<alpha>2 (mif_map_value_image_filter mif f m) = (\<lambda>k. Option.bind (\<alpha>1 m k) (f k))"
      by (simp add: fun_eq_iff)
  qed
qed

definition it_map_value_image_filter ::
  "('s1,'u,'v1,'s2) map_iterator \<Rightarrow> 's2 \<Rightarrow> ('u \<Rightarrow> 'v2 \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 
   ('u \<Rightarrow> 'v1 \<Rightarrow> 'v2 option) \<Rightarrow> 's1 \<Rightarrow> 's2" where
  "it_map_value_image_filter map_it map_emp map_up_dj f \<equiv>
   it_map_image_filter map_it map_emp map_up_dj
     (\<lambda>k v. case (f k v) of Some v' \<Rightarrow> Some (k, v') | None \<Rightarrow> None)"

lemma it_map_value_image_filter_alt_def :
  "it_map_value_image_filter map_it map_emp map_up_dj =
   mif_map_value_image_filter (it_map_image_filter map_it map_emp map_up_dj)"
apply (simp add: fun_eq_iff)
unfolding it_map_image_filter_def mif_map_value_image_filter_def
  it_map_value_image_filter_def
by fast

lemma it_map_value_image_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'u \<rightharpoonup> 'v1"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'u \<rightharpoonup> 'v2" 
  assumes it: "map_iterate \<alpha>1 invar1 map_it"
  assumes emp: "map_empty \<alpha>2 invar2 map_emp"
  assumes up: "map_update_dj \<alpha>2 invar2 map_up_dj"
  shows "map_value_image_filter \<alpha>1 invar1 \<alpha>2 invar2 
    (it_map_value_image_filter map_it map_emp map_up_dj)"
proof -
  note mif_OK = it_map_image_filter_correct [OF it emp up]
  note mif_map_value_image_filter_correct [OF mif_OK]
  thus ?thesis
    unfolding it_map_value_image_filter_alt_def
    by fast
qed


definition mif_map_restrict :: 
  "(('u \<Rightarrow> 'v \<Rightarrow> ('u \<times> 'v) option) \<Rightarrow> 's1 \<Rightarrow> 's2) \<Rightarrow>
   ('u \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2"
where
    "mif_map_restrict mif P \<equiv>
     mif (\<lambda>k v. if (P k v) then Some (k, v) else None)"

lemma mif_map_restrict_alt_def :
  "mif_map_restrict mif P =
   mif_map_value_image_filter mif (\<lambda>k v. if (P k v) then Some v else None)"
proof -
  have "(\<lambda>k v. if P k v then Some (k, v) else None) =
        (\<lambda>k v. case if P k v then Some v else None of None \<Rightarrow> None
               | Some v' \<Rightarrow> Some (k, v'))" 
    by (simp add: fun_eq_iff)
  thus ?thesis
    unfolding mif_map_restrict_def mif_map_value_image_filter_def
    by simp
qed

lemma mif_map_restrict_correct :
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'u \<rightharpoonup> 'v" 
shows "map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 mif \<Longrightarrow>
       map_restrict \<alpha>1 invar1 \<alpha>2 invar2 (mif_map_restrict mif)"
proof -
  assume "map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 mif"
  then interpret map_value_image_filter \<alpha>1 invar1 \<alpha>2 invar2 
                "mif_map_value_image_filter mif"
    by (rule mif_map_value_image_filter_correct) 

  show ?thesis
    unfolding mif_map_restrict_alt_def map_restrict_def
    apply (auto simp add: map_value_image_filter_correct fun_eq_iff
              restrict_map_def)
    apply (case_tac "\<alpha>1 m x")
    apply auto
  done
qed

definition it_map_restrict ::
  "('s1,'u,'v,'s2) map_iterator \<Rightarrow> 's2 \<Rightarrow> ('u \<Rightarrow> 'v \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 
   ('u \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2" where
  "it_map_restrict map_it map_emp map_up_dj P \<equiv>
   it_map_image_filter map_it map_emp map_up_dj
     (\<lambda>k v. if (P k v) then Some (k, v) else None)"

lemma it_map_restrict_alt_def :
  "it_map_restrict map_it map_emp map_up_dj =
   mif_map_restrict (it_map_image_filter map_it map_emp map_up_dj)"
apply (simp add: fun_eq_iff)
unfolding it_map_image_filter_def mif_map_restrict_def
  it_map_restrict_def
by fast

lemma it_map_restrict_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'u \<rightharpoonup> 'v"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'u \<rightharpoonup> 'v" 
  assumes it: "map_iterate \<alpha>1 invar1 map_it"
  assumes emp: "map_empty \<alpha>2 invar2 map_emp"
  assumes up: "map_update_dj \<alpha>2 invar2 map_up_dj"
  shows "map_restrict \<alpha>1 invar1 \<alpha>2 invar2 
    (it_map_restrict map_it map_emp map_up_dj)"
proof -
  note mif_OK = it_map_image_filter_correct [OF it emp up]
  note mif_map_restrict_correct [OF mif_OK]
  thus ?thesis
    unfolding it_map_restrict_alt_def
    by fast
qed

end
