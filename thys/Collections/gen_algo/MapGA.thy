(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedMap, algorithms for iterators, min, max, to_sorted_list

*)

header {* \isaheader{Generic Algorithms for Maps} *}
theory MapGA
imports 
  "../spec/MapSpec"
  "../common/Misc" 
  "../iterator/SetIteratorGA" 
  "../iterator/SetIteratorGACollections"
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

definition it_add where 
  "it_add update iti = (\<lambda>m1 m2. iterate_add_to_map m1 update (iti m2))"

lemma it_add_code[code]:
  "it_add update iti m1 m2 = iti m2 (\<lambda>_. True) (\<lambda>(x, y). update x y) m1"
unfolding it_add_def iterate_add_to_map_def by simp

lemma it_add_correct:
  fixes \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  assumes iti: "map_iteratei \<alpha> invar iti"
  assumes upd_OK: "map_update \<alpha> invar update"
  shows "map_add \<alpha> invar (it_add update iti)"
unfolding it_add_def
proof 
  fix m1 m2
  assume "invar m1" "invar m2"
  with map_iteratei.iteratei_rule[OF iti, of m2] 
  have iti_m2: "map_iterator (iti m2) (\<alpha> m2)" by simp

  from iterate_add_to_map_correct [OF upd_OK, OF `invar m1` iti_m2 ]
  show "\<alpha> (iterate_add_to_map m1 update (iti m2)) = \<alpha> m1 ++ \<alpha> m2"
       "invar (iterate_add_to_map m1 update (iti m2))"
    by simp_all
qed


subsection {*Disjoint Add (by iterate)*}
lemma it_add_dj_correct:
  fixes \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v"
  assumes iti: "map_iteratei \<alpha> invar iti"
  assumes upd_dj_OK: "map_update_dj \<alpha> invar update"
  shows "map_add_dj \<alpha> invar (it_add update iti)"
unfolding it_add_def
proof 
  fix m1 m2
  assume "invar m1" "invar m2" and dom_dj: "dom (\<alpha> m1) \<inter> dom (\<alpha> m2) = {}"
  with map_iteratei.iteratei_rule[OF iti, OF `invar m2`] 
  have iti_m2: "map_iterator (iti m2) (\<alpha> m2)" by simp

  from iterate_add_to_map_dj_correct [OF upd_dj_OK, OF `invar m1` iti_m2 ] dom_dj
  show "\<alpha> (iterate_add_to_map m1 update (iti m2)) = \<alpha> m1 ++ \<alpha> m2"
       "invar (iterate_add_to_map m1 update (iti m2))"
    by auto
qed

subsection {*Emptiness check (by iteratei)*}

definition iti_isEmpty where
  "iti_isEmpty iti = (\<lambda>m. iterate_is_empty (iti m))"

lemma iti_isEmpty[code] :
  "iti_isEmpty iti m = iti m (\<lambda>c. c) (\<lambda>_ _. False) True"
unfolding iti_isEmpty_def iterate_is_empty_def by simp

lemma iti_isEmpty_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_isEmpty \<alpha> invar (iti_isEmpty iti)"
unfolding iti_isEmpty_def
proof 
  fix m
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp

  from iterate_is_empty_correct[OF iti']
  show "iterate_is_empty (iti m) = (\<alpha> m = Map.empty)"
    by (simp add: map_to_set_empty_iff)
qed


subsection {* Iterators *}

subsubsection {* Iteratei (by iterateoi) *}
lemma iti_by_itoi: 
  assumes "map_iterateoi \<alpha> invar it"
  shows "map_iteratei \<alpha> invar it"
using assms
unfolding map_iterateoi_def map_iteratei_def map_iteratei_axioms_def
          map_iterateoi_axioms_def set_iterator_map_linord_def 
          finite_map_def ordered_finite_map_def
by (metis set_iterator_intro)

subsubsection {* Iteratei (by reverse\_iterateoi) *}
lemma iti_by_ritoi: 
  assumes "map_reverse_iterateoi \<alpha> invar it"
  shows "map_iteratei \<alpha> invar it"
using assms
unfolding map_reverse_iterateoi_def map_iteratei_def map_iteratei_axioms_def
          map_reverse_iterateoi_axioms_def set_iterator_map_rev_linord_def 
          finite_map_def ordered_finite_map_def
by (metis set_iterator_intro)


subsection {*Selection (by iteratei)*}

definition iti_sel where
  "iti_sel iti = (\<lambda>m f. iterate_sel (iti m) f)"

lemma iti_sel_code[code] :
  "iti_sel iti m f = iti m (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. f x) None"
unfolding iti_sel_def iterate_sel_def by simp

lemma iti_sel_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_sel \<alpha> invar (iti_sel iti)"
proof -
  { fix m f
    assume "invar m"
    with map_iteratei.iteratei_rule [OF iti, of m]
    have iti': "map_iterator (iti m) (\<alpha> m)" by simp
    note iterate_sel_genord_correct[OF iti'[unfolded set_iterator_def], of f]
  }
  thus ?thesis
    unfolding map_sel_def iti_sel_def
    apply (simp add: Bex_def Ball_def image_iff map_to_set_def)
    apply (metis option.exhaust)
  done
qed


subsection {* Map-free selection by selection *}

definition iti_sel_no_map where
  "iti_sel_no_map iti = (\<lambda>m P. iterate_sel_no_map (iti m) P)"

lemma iti_sel_no_map_code[code] :
  "iti_sel_no_map iti m P = iti m (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. if P x then Some x else None) None"
unfolding iti_sel_no_map_def iterate_sel_no_map_alt_def by simp

lemma iti_sel'_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_sel' \<alpha> invar (iti_sel_no_map iti)"
proof -
  { fix m P
    assume "invar m"
    with map_iteratei.iteratei_rule [OF iti, of m]
    have iti': "map_iterator (iti m) (\<alpha> m)" by simp
    note iterate_sel_no_map_correct[OF iti', of P]
  }
  thus ?thesis
    unfolding map_sel'_def iti_sel_no_map_def
    apply (simp add: Bex_def Ball_def image_iff map_to_set_def)
    apply clarify
    apply (metis option.exhaust PairE)
  done
qed

subsection {* Map-free selection by selection *}

definition sel_sel'
  :: "('s \<Rightarrow> ('k \<times> 'v \<Rightarrow> _ option) \<Rightarrow> _ option) \<Rightarrow> 's \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> ('k\<times>'v) option"
where "sel_sel' sel s P = sel s (\<lambda>kv. if P kv then Some kv else None)"

lemma sel_sel'_correct: 
  assumes "map_sel \<alpha> invar sel"
  shows "map_sel' \<alpha> invar (sel_sel' sel)"
proof -
  interpret map_sel \<alpha> invar sel by fact

  show ?thesis
  proof
    case goal1 show ?case
      apply (rule selE[OF goal1(1,2), where f="(\<lambda>kv. if P kv then Some kv else None)"])
      apply (simp add: goal1)
      apply (simp split: split_if_asm)
      apply (fold sel_sel'_def)
      apply (blast intro: goal1(4))
      done
  next
    case goal2 thus ?case
      apply (auto simp add: sel_sel'_def)
      apply (drule selI[where f="(\<lambda>kv. if P kv then Some kv else None)"])
      apply auto
      done
  qed
qed


subsection {*Bounded Quantification (by sel)*}
definition sel_ball 
  :: "('s \<Rightarrow> ('k \<times> 'v \<Rightarrow> unit option) \<rightharpoonup> unit) \<Rightarrow> 's \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  where "sel_ball sel s P == sel s (\<lambda>kv. if \<not>P kv then Some () else None) = None"

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
  :: "('s \<Rightarrow> ('k \<times> 'v \<Rightarrow> unit option) \<rightharpoonup> unit) \<Rightarrow> 's \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  where "sel_bexists sel s P == sel s (\<lambda>kv. if P kv then Some () else None) = Some ()"

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
    apply (erule_tac f="(\<lambda>kv. if P kv then Some () else None)" in selE)
    apply assumption
    apply simp
    apply simp
    done
qed

definition neg_ball_bexists
  :: "('s \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('k \<times> 'v \<Rightarrow> bool) \<Rightarrow> bool"
  where "neg_ball_bexists ball s P == \<not> (ball s (\<lambda>kv. \<not>(P kv)))"

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



subsection {*Bounded Quantification (by iterate)*}

definition iti_ball where
  "iti_ball iti = (\<lambda>m. iterate_ball (iti m))"

lemma iti_ball_code[code] :
  "iti_ball iti m P = iti m (\<lambda>c. c) (\<lambda>x \<sigma>. P x) True"
unfolding iti_ball_def iterate_ball_def[abs_def] id_def by simp

lemma iti_ball_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_ball \<alpha> invar (iti_ball iti)"
unfolding iti_ball_def
proof 
  fix m P
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp

  from iterate_ball_correct[OF iti', of P]
  show "iterate_ball (iti m) P = (\<forall>u v. \<alpha> m u = Some v \<longrightarrow> P (u, v))"
    by (simp add: map_to_set_def)
qed

definition iti_bexists where
  "iti_bexists iti = (\<lambda>m. iterate_bex (iti m))"

lemma iti_bexists_code[code] :
  "iti_bexists iti m P = iti m (\<lambda>c. \<not>c) (\<lambda>x \<sigma>. P x) False"
unfolding iti_bexists_def iterate_bex_def[abs_def] by simp

lemma iti_bexists_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_bexists \<alpha> invar (iti_bexists iti)"
unfolding iti_bexists_def
proof 
  fix m P
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp

  from iterate_bex_correct[OF iti', of P]
  show "iterate_bex (iti m) P = (\<exists>u v. \<alpha> m u = Some v \<and> P (u, v)) "
    by (simp add: map_to_set_def)
qed


subsection {* Size (by iterate)*}

definition it_size where
  "it_size iti = (\<lambda>m. iterate_size (iti m))"

lemma it_size_code[code] :
  "it_size iti m = iti m (\<lambda>_. True) (\<lambda>x n . Suc n) 0"
unfolding it_size_def iterate_size_def by simp

lemma it_size_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_size \<alpha> invar (it_size iti)"
unfolding it_size_def
proof 
  fix m
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp

  from iterate_size_correct [OF iti']
  show "finite (dom (\<alpha> m))"
       "iterate_size (iti m) = card (dom (\<alpha> m))"
    by (simp_all add: finite_map_to_set card_map_to_set) 
qed 

subsection {* Size with abort (by iterate) *}

definition iti_size_abort where
  "iti_size_abort iti = (\<lambda>n m. iterate_size_abort (iti m) n)"

lemma iti_size_abort_code[code] :
  "iti_size_abort iti n m = iti m (\<lambda>\<sigma>. \<sigma> < n) (\<lambda>x. Suc) 0"
unfolding iti_size_abort_def iterate_size_abort_def by simp

lemma iti_size_abort_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_size_abort \<alpha> invar (iti_size_abort iti)"
unfolding iti_size_abort_def
proof 
  fix m n
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp

  from iterate_size_abort_correct [OF iti']
  show "finite (dom (\<alpha> m))"
       "iterate_size_abort (iti m) n = min n (card (dom (\<alpha> m)))"
    by (simp_all add: finite_map_to_set card_map_to_set) 
qed 

subsection {* Singleton check (by size-abort) *}

definition sza_isSng where
  "sza_isSng iti = (\<lambda>m. iterate_is_sng (iti m))"

lemma sza_isSng_code[code] :
  "sza_isSng iti m = (iti m (\<lambda>\<sigma>. \<sigma> < 2) (\<lambda>x. Suc) 0 = 1)"
unfolding sza_isSng_def iterate_is_sng_def iterate_size_abort_def by simp

lemma sza_isSng_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_isSng \<alpha> invar (sza_isSng iti)"
unfolding sza_isSng_def
proof 
  fix m 
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp

  have "card (map_to_set (\<alpha> m)) = (Suc 0) \<longleftrightarrow> (\<exists>kv. map_to_set (\<alpha> m) = {kv})" by (simp add: card_Suc_eq)
  also have "\<dots> \<longleftrightarrow> (\<exists>kv. \<alpha> m = [fst kv \<mapsto> snd kv])" unfolding map_to_set_def
     apply (rule iff_exI)
     apply (simp add: set_eq_iff fun_eq_iff all_conj_distrib)
     apply auto
     apply (metis option.exhaust)
     apply (metis option.simps(1,2))
  done
  finally have "card (map_to_set (\<alpha> m)) = (Suc 0) \<longleftrightarrow> (\<exists>k v. \<alpha> m = [k \<mapsto> v])" by simp

  with iterate_is_sng_correct [OF iti']
  show "iterate_is_sng (iti m) = (\<exists>k v. \<alpha> m = [k \<mapsto> v])"
    by simp
qed 

subsection {*Map to List (by iterate)*}

definition it_map_to_list where
  "it_map_to_list iti = (\<lambda>m. iterate_to_list (iti m))"

lemma it_map_to_list_code[code] :
  "it_map_to_list iti m = iti m (\<lambda>_. True) op # []"
unfolding it_map_to_list_def iterate_to_list_def by simp

lemma it_map_to_list_correct:
  assumes iti: "map_iteratei \<alpha> invar iti"
  shows "map_to_list \<alpha> invar (it_map_to_list iti)"
unfolding it_map_to_list_def
proof 
  fix m
  assume "invar m"
  with map_iteratei.iteratei_rule[OF iti, of m] 
  have iti': "map_iterator (iti m) (\<alpha> m)" by simp
  let ?l = "iterate_to_list (iti m)"

  from iterate_to_list_correct [OF iti']
  have set_l_eq: "set ?l = map_to_set (\<alpha> m)" and dist_l: "distinct ?l" by simp_all

  from dist_l show dist_fst_l: "distinct (map fst ?l)"
    by (simp add: distinct_map set_l_eq map_to_set_def inj_on_def)
    
  from map_of_map_to_set[of ?l "\<alpha> m", OF dist_fst_l] set_l_eq
  show "map_of (iterate_to_list (iti m)) = \<alpha> m" by simp
qed


subsection {*List to Map*}

(* Tail recursive version *)
fun gen_list_to_map_aux
  :: "('k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> ('k\<times>'v) list \<Rightarrow> 'm"
  where
  "gen_list_to_map_aux upd accs [] = accs" |
  "gen_list_to_map_aux upd accs ((k,v)#l) = gen_list_to_map_aux upd (upd k v accs) l"

definition "gen_list_to_map empt upd l == gen_list_to_map_aux upd (empt ()) (rev l)"

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
  :: "(unit \<Rightarrow> 'm) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'm"
  where "eu_sng empt update k v == update k v (empt ())"

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

lemma itoi_min_correct:
  assumes iti: "map_iterateoi \<alpha> invar iti"
  shows "map_min \<alpha> invar (iti_sel_no_map iti)"
unfolding iti_sel_no_map_def
proof 
  fix m P

  assume "invar m"
  with map_iterateoi.iterateoi_rule [OF iti, of m]
  have iti': "map_iterator_linord (iti m) (\<alpha> m)" by simp
  note sel_correct = iterate_sel_no_map_map_linord_correct[OF iti', of P]
 
  { assume "rel_of (\<alpha> m) P \<noteq> {}"
    with sel_correct show "iterate_sel_no_map (iti m) P \<in> Some ` rel_of (\<alpha> m) P"
      by (auto simp add: image_iff rel_of_def)
  }

  { assume "rel_of (\<alpha> m) P = {}"        
     with sel_correct show "iterate_sel_no_map (iti m) P = None"
      by (auto simp add: image_iff rel_of_def)
  }

  { fix k v
    assume "(k, v) \<in> rel_of (\<alpha> m) P"
    with sel_correct show "fst (the (iterate_sel_no_map (iti m) P)) \<le> k"
      by (auto simp add: image_iff rel_of_def)
  }
qed

subsection {* Max (by reverse\_iterateoi) *}

lemma ritoi_max_correct:
  assumes iti: "map_reverse_iterateoi \<alpha> invar iti"
  shows "map_max \<alpha> invar (iti_sel_no_map iti)"
unfolding iti_sel_no_map_def
proof 
  fix m P

  assume "invar m"
  with map_reverse_iterateoi.reverse_iterateoi_rule [OF iti, of m]
  have iti': "map_iterator_rev_linord (iti m) (\<alpha> m)" by simp
  note sel_correct = iterate_sel_no_map_map_rev_linord_correct[OF iti', of P]
 
  { assume "rel_of (\<alpha> m) P \<noteq> {}"
    with sel_correct show "iterate_sel_no_map (iti m) P \<in> Some ` rel_of (\<alpha> m) P"
      by (auto simp add: image_iff rel_of_def)
  }

  { assume "rel_of (\<alpha> m) P = {}"        
     with sel_correct show "iterate_sel_no_map (iti m) P = None"
      by (auto simp add: image_iff rel_of_def)
  }

  { fix k v
    assume "(k, v) \<in> rel_of (\<alpha> m) P"
    with sel_correct show "k \<le> fst (the (iterate_sel_no_map (iti m) P))"
      by (auto simp add: image_iff rel_of_def)
  }
qed


subsection {* Conversion to sorted list (by reverse\_iterateo) *}

lemma rito_map_to_sorted_list_correct:
  assumes iti: "map_reverse_iterateoi \<alpha> invar iti"
  shows "map_to_sorted_list \<alpha> invar (it_map_to_list iti)"
unfolding it_map_to_list_def
proof 
  fix m
  assume "invar m"
  with map_reverse_iterateoi.reverse_iterateoi_rule[OF iti, of m] 
  have iti': "map_iterator_rev_linord (iti m) (\<alpha> m)" by simp
  let ?l = "iterate_to_list (iti m)"

  from iterate_to_list_map_rev_linord_correct [OF iti']
  show "sorted (map fst ?l)" 
       "distinct (map fst ?l)"
       "map_of (iterate_to_list (iti m)) = \<alpha> m" by simp_all
qed


subsection {* image restrict *}

definition it_map_image_filter ::
  "('s1 \<Rightarrow> ('u1 \<times> 'v1,'s2) set_iterator) \<Rightarrow> (unit \<Rightarrow> 's2) \<Rightarrow> ('u2 \<Rightarrow> 'v2 \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> ('u1 \<times> 'v1 \<Rightarrow> ('u2 \<times> 'v2) option) \<Rightarrow> 's1 \<Rightarrow> 's2"
  where "it_map_image_filter map_it map_emp map_up_dj f m \<equiv>
         iterate_to_map map_emp map_up_dj (set_iterator_image_filter f (map_it m))"

lemma it_map_image_filter_alt_def[code]:
  "it_map_image_filter map_it map_emp map_up_dj f m \<equiv>
   map_it m (\<lambda>_. True) (\<lambda>kv \<sigma>. case (f kv) of None \<Rightarrow> \<sigma> | Some (k', v') \<Rightarrow> (map_up_dj k' v' \<sigma>)) (map_emp ())"
unfolding it_map_image_filter_def iterate_to_map_alt_def set_iterator_image_filter_def prod_case_beta
by simp

lemma it_map_image_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'u1 \<rightharpoonup> 'v1"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'u2 \<rightharpoonup> 'v2" 
  assumes it: "map_iteratei \<alpha>1 invar1 map_it"
  assumes emp: "map_empty \<alpha>2 invar2 map_emp"
  assumes up: "map_update_dj \<alpha>2 invar2 map_up_dj"
  shows "map_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (it_map_image_filter map_it map_emp map_up_dj)"
proof 
  fix m k' v' and f :: "('u1 \<times> 'v1) \<Rightarrow> ('u2 \<times> 'v2) option"
  assume invar_m: "invar1 m" and
         unique_f: "transforms_to_unique_keys (\<alpha>1 m) f"

  from map_iteratei.iteratei_rule[OF it, OF invar_m] 
  have iti_m: "map_iterator (map_it m) (\<alpha>1 m)" by simp

  from unique_f have inj_on_f: "inj_on f (map_to_set (\<alpha>1 m) \<inter> dom f)"
    unfolding transforms_to_unique_keys_def inj_on_def Ball_def map_to_set_def
    by auto (metis option.inject)

  def vP \<equiv> "\<lambda>k v. \<exists>k' v'. \<alpha>1 m k' = Some v' \<and> f (k', v') = Some (k, v)"
  have vP_intro: "\<And>k v. (\<exists>k' v'. \<alpha>1 m k' = Some v' \<and> f (k', v') = Some (k, v)) \<longleftrightarrow> vP k v"
    unfolding vP_def by simp
  { fix k v
    have "Eps_Opt (vP k) = Some v \<longleftrightarrow> vP k v"
      using unique_f unfolding vP_def transforms_to_unique_keys_def 
      apply (rule_tac Eps_Opt_eq_Some)
      apply (metis Pair_eq option.inject)
    done
  } note Eps_vP_elim[simp] = this
  have map_intro: "{y. \<exists>x. x \<in> map_to_set (\<alpha>1 m) \<and> f x = Some y} = map_to_set (\<lambda>k. Eps_Opt (vP k))"
    by (simp add: map_to_set_def vP_intro set_eq_iff split: prod.splits)

  from set_iterator_image_filter_correct [OF iti_m, OF inj_on_f, unfolded map_intro] 
  have iti_filter: "map_iterator (set_iterator_image_filter f (map_it m))
        (\<lambda>k. Eps_Opt (vP k))" by auto

  from iterate_to_map_correct [OF up emp iti_filter]
  show "invar2 (it_map_image_filter map_it map_emp map_up_dj f m) \<and>
       (\<alpha>2 (it_map_image_filter map_it map_emp map_up_dj f m) k' = Some v') =
       (\<exists>k v. \<alpha>1 m k = Some v \<and> f (k, v) = Some (k', v'))"
    unfolding it_map_image_filter_def vP_def[symmetric]
    by (simp add: vP_intro)
qed


definition mif_map_value_image_filter :: 
  "(('u \<times> 'v1 \<Rightarrow> ('u \<times> 'v2) option) \<Rightarrow> 's1 \<Rightarrow> 's2) \<Rightarrow>
    ('u \<Rightarrow> 'v1 \<Rightarrow> 'v2 option) \<Rightarrow> 's1 \<Rightarrow> 's2"
where
    "mif_map_value_image_filter mif f \<equiv>
     mif (\<lambda>(k, v). case (f k v) of Some v' \<Rightarrow> Some (k, v') | None \<Rightarrow> None)"

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

    let ?f = "\<lambda>(k, v). case (f k v) of Some v' \<Rightarrow> Some (k, v') | None \<Rightarrow> None"
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
  "('s1 \<Rightarrow> ('u \<times> 'v1,'s2) set_iterator) \<Rightarrow> (unit \<Rightarrow> 's2) \<Rightarrow> ('u \<Rightarrow> 'v2 \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 
   ('u \<Rightarrow> 'v1 \<Rightarrow> 'v2 option) \<Rightarrow> 's1 \<Rightarrow> 's2" where
  "it_map_value_image_filter map_it map_emp map_up_dj f \<equiv>
   it_map_image_filter map_it map_emp map_up_dj
     (\<lambda>(k, v). case (f k v) of Some v' \<Rightarrow> Some (k, v') | None \<Rightarrow> None)"

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
  assumes it: "map_iteratei \<alpha>1 invar1 map_it"
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
  "(('u \<times> 'v \<Rightarrow> ('u \<times> 'v) option) \<Rightarrow> 's1 \<Rightarrow> 's2) \<Rightarrow>
   ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2"
where
    "mif_map_restrict mif P \<equiv>
     mif (\<lambda>(k, v). if (P (k, v)) then Some (k, v) else None)"

lemma mif_map_restrict_alt_def :
  "mif_map_restrict mif P =
   mif_map_value_image_filter mif (\<lambda>k v. if (P (k, v)) then Some v else None)"
proof -
  have "(\<lambda>k v. if P (k, v) then Some (k, v) else None) =
        (\<lambda>k v. case if P (k, v) then Some v else None of None \<Rightarrow> None
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
  "('s1 \<Rightarrow> ('u \<times> 'v,'s2) set_iterator) \<Rightarrow> (unit \<Rightarrow> 's2) \<Rightarrow> ('u \<Rightarrow> 'v \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 
   ('u \<times> 'v \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2" where
  "it_map_restrict map_it map_emp map_up_dj P \<equiv>
   it_map_image_filter map_it map_emp map_up_dj
     (\<lambda>(k, v). if (P (k, v)) then Some (k, v) else None)"

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
  assumes it: "map_iteratei \<alpha>1 invar1 map_it"
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
