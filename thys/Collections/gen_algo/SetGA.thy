(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedSet, algorithms for iterators, min, max, to_sorted_list

*)

header {* \isaheader{Generic Algorithms for Sets} *}
theory SetGA
imports 
  "../spec/SetSpec" 
  "../iterator/SetIteratorGA" 
  "../iterator/SetIteratorGACollections"
begin
text_raw {*\label{thy:SetGA}*}


subsection {* Singleton Set (by empty,insert)*}
definition ei_sng :: "(unit \<Rightarrow> 's) \<Rightarrow> ('x\<Rightarrow>'s\<Rightarrow>'s) \<Rightarrow> 'x \<Rightarrow> 's" where "ei_sng e i x = i x (e ())"
lemma ei_sng_correct: 
  assumes "set_empty \<alpha> invar e"
  assumes "set_ins \<alpha> invar i"
  shows "set_sng \<alpha> invar (ei_sng e i)"
proof -
  interpret set_empty \<alpha> invar e + set_ins \<alpha> invar i by fact+
  show ?thesis
    apply (unfold_locales)
    unfolding ei_sng_def
    by (auto simp: empty_correct ins_correct)
qed

subsection {*Disjoint Insert (by insert)*}
lemma (in set_ins) ins_dj_by_ins: 
  shows "set_ins_dj \<alpha> invar ins"
  by (unfold_locales)
     (simp_all add: ins_correct)

subsection {*Disjoint Union (by union)*}
lemma (in set_union) union_dj_by_union: 
  shows "set_union_dj \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 union"
  by (unfold_locales)
     (simp_all add: union_correct)

subsection {* Iterators *}

subsubsection {* Iteratei (by iterateoi) *}
lemma iti_by_itoi: 
  assumes "set_iterateoi \<alpha> invar it"
  shows "set_iteratei \<alpha> invar it"
proof -
  interpret set_iterateoi \<alpha> invar it by fact
  show ?thesis
  proof (unfold_locales)
    fix S
    assume "invar S"
    with iterateoi_rule[of S] have "set_iterator_linord (it S) (\<alpha> S)" .
    thus "set_iterator (it S) (\<alpha> S)"
      by (simp add: set_iterator_linord_def set_iterator_intro)
  qed
qed

subsubsection {* Iteratei (by reverse\_iterateoi) *}
lemma iti_by_ritoi: 
  assumes "set_reverse_iterateoi \<alpha> invar it"
  shows "set_iteratei \<alpha> invar it"
proof -
  interpret set_reverse_iterateoi \<alpha> invar it by fact
  show ?thesis
  proof (unfold_locales)
    fix S
    assume "invar S"
    with reverse_iterateoi_rule[of S] have "set_iterator_rev_linord (it S) (\<alpha> S)" .
    thus "set_iterator (it S) (\<alpha> S)"
      by (simp add: set_iterator_rev_linord_def set_iterator_intro)
  qed
qed


subsection {*Emptiness check (by iteratei)*}

definition iti_isEmpty where
  "iti_isEmpty iti = (\<lambda>s. (iterate_is_empty (iti s)))"

lemma iti_isEmpty_code[code] :
  "iti_isEmpty iti s = iti s (\<lambda>c. c) (\<lambda>_ _. False) True"
unfolding iti_isEmpty_def iterate_is_empty_def by simp

lemma iti_isEmpty_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_isEmpty \<alpha> invar (\<lambda>s. (iterate_is_empty (iti s)))"
proof 
  fix s
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have  iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  from iterate_is_empty_correct [OF iti_s]
  show "iterate_is_empty (iti s) = (\<alpha> s = {})" .
qed

subsection {*Bounded Quantification (by iteratei)*}

definition iti_ball where
  "iti_ball iti = (\<lambda>s. iterate_ball (iti s))"

lemma iti_ball_code[code] :
  "iti_ball iti s P = iti s (\<lambda>c. c) (\<lambda>x \<sigma>. P x) True"
unfolding iti_ball_def iterate_ball_def id_def
by simp

lemma iti_ball_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_ball \<alpha> invar (iti_ball iti)"
unfolding iti_ball_def
proof 
  fix s P
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  from iterate_ball_correct [OF iti_s, of P]
  show "iterate_ball (iti s) P = (\<forall>x\<in>\<alpha> s. P x)" .
qed

definition iti_bexists where
  "iti_bexists iti = (\<lambda>s. iterate_bex (iti s))"

lemma iti_bexists_code[code] :
  "iti_bexists iti s P = iti s (\<lambda>c. \<not>c) (\<lambda>x \<sigma>. P x) False"
unfolding iti_bexists_def iterate_bex_def 
by simp

lemma iti_bexists_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_bexists \<alpha> invar (iti_bexists iti)"
unfolding iti_bexists_def
proof 
  fix s P
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  from iterate_bex_correct [OF iti_s, of P]
  show "iterate_bex (iti s) P = (\<exists>x\<in>\<alpha> s. P x)" .
qed

definition neg_ball_bexists
  :: "('s \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "neg_ball_bexists ball s P == \<not> (ball s (\<lambda>x. \<not>(P x)))"

lemma neg_ball_bexists_correct:
  fixes ball
  assumes "set_ball \<alpha> invar ball"
  shows "set_bexists \<alpha> invar (neg_ball_bexists ball)"
proof -
  interpret set_ball \<alpha> invar ball by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold neg_ball_bexists_def)
    apply (simp add: ball_correct)
  done
qed

subsection {* Size (by iterate)*}

definition it_size where
  "it_size iti = (\<lambda>s. iterate_size (iti s))"

lemma it_size_code[code] :
  "it_size iti s = iti s (\<lambda>_. True) (\<lambda>x n . Suc n) 0"
unfolding it_size_def iterate_size_def by simp

lemma it_size_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_size \<alpha> invar (it_size iti)"
unfolding it_size_def
proof 
  fix s 
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  from iterate_size_correct [OF iti_s]
  show "iterate_size (iti s) = card (\<alpha> s)" "finite (\<alpha> s)" by simp_all
qed

subsection {* Size with abort (by iterate) *}

definition iti_size_abort where
  "iti_size_abort iti = (\<lambda>m s. iterate_size_abort (iti s) m)"

lemma iti_size_abort_code[code] :
  "iti_size_abort iti m s = iti s (\<lambda>\<sigma>. \<sigma> < m) (\<lambda>x. Suc) 0"
unfolding iti_size_abort_def iterate_size_abort_def by simp

lemma iti_size_abort_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_size_abort \<alpha> invar (iti_size_abort iti)"
unfolding iti_size_abort_def
proof 
  fix s n
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  from iterate_size_abort_correct [OF iti_s]
  show "iterate_size_abort (iti s) n = min n (card (\<alpha> s))" "finite (\<alpha> s)"
    by simp_all
qed

subsection {* Singleton check (by size-abort) *}

definition sza_isSng where
  "sza_isSng iti = (\<lambda>s. iterate_is_sng (iti s))"

lemma sza_isSng_code[code] :
  "sza_isSng iti s = (iti s (\<lambda>\<sigma>. \<sigma> < 2) (\<lambda>x. Suc) 0 = 1)"
unfolding sza_isSng_def iterate_is_sng_def iterate_size_abort_def
by simp

lemma sza_isSng_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_isSng \<alpha> invar (sza_isSng iti)"
unfolding sza_isSng_def
proof 
  fix s 
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  have "card (\<alpha> s) = (Suc 0) \<longleftrightarrow> (\<exists>e. \<alpha> s = {e})" by (simp add: card_Suc_eq)
  with iterate_is_sng_correct [OF iti_s]
  show "iterate_is_sng (iti s) = (\<exists>e. \<alpha> s = {e})"
    by simp
qed

subsection {*Copy (by iterate)*}

definition it_copy where
  "it_copy iti emp ins s = iterate_to_set emp ins (iti s)"

lemma it_copy_code[code] :
  "it_copy iti emp ins s = iti s (\<lambda>_. True) ins (emp ())"
unfolding it_copy_def iterate_to_set_alt_def by simp

lemma it_copy_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  fixes iteratei1 :: "'s1 \<Rightarrow> ('x,'s2) set_iterator"
  assumes iti: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes emp_OK: "set_empty \<alpha>2 invar2 empty2"
  assumes ins_dj_OK: "set_ins_dj \<alpha>2 invar2 ins2"
  shows "set_copy \<alpha>1 invar1 \<alpha>2 invar2 (it_copy iteratei1 empty2 ins2)"
unfolding it_copy_def[abs_def]
proof 
  fix s1
  assume "invar1 s1"
  with set_iteratei.iteratei_rule [OF iti, of s1]
  have iti_s: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  from iterate_to_set_correct[OF ins_dj_OK emp_OK iti_s] 
  show "\<alpha>2 (iterate_to_set empty2 ins2 (iteratei1 s1)) = \<alpha>1 s1"
       "invar2 (iterate_to_set empty2 ins2 (iteratei1 s1))" 
    by simp_all
qed

subsection {*Union (by iterate)*}

definition it_union where
  "it_union it ins \<equiv> (\<lambda>s1 s2. iterate_add_to_set s2 ins (it s1))"
lemma it_union_code[code] :
  "it_union it ins s1 s2 = it s1 (\<lambda>_. True) ins s2"
unfolding it_union_def iterate_add_to_set_def by simp

lemma it_union_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  assumes S1: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes S2: "set_ins \<alpha>2 invar2 ins2"
  shows "set_union \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>2 invar2 (it_union iteratei1 ins2)"
unfolding it_union_def
proof 
  fix s1 s2
  assume "invar1 s1"
  with set_iteratei.iteratei_rule [OF S1, of s1]
  have iti_s: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  assume "invar2 s2"
  with iterate_add_to_set_correct[OF S2 _ iti_s, of s2] 
  show "\<alpha>2 (iterate_add_to_set s2 ins2 (iteratei1 s1)) = \<alpha>1 s1 \<union> \<alpha>2 s2"
       "invar2 (iterate_add_to_set s2 ins2 (iteratei1 s1))" 
    by simp_all
qed


subsection {* Disjoint Union *}

definition [code_unfold]: "it_union_dj \<equiv> it_union"

lemma it_union_dj_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  assumes S1: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes S2: "set_ins_dj \<alpha>2 invar2 ins2"
  shows "set_union_dj \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>2 invar2 (it_union_dj iteratei1 ins2)"
unfolding it_union_def it_union_dj_def
proof 
  fix s1 s2
  assume "invar1 s1"
  with set_iteratei.iteratei_rule [OF S1, of s1]
  have iti_s: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  assume "invar2 s2" "\<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"
  with iterate_add_to_set_dj_correct[OF S2 _ iti_s, of s2] 
  show "\<alpha>2 (iterate_add_to_set s2 ins2 (iteratei1 s1)) = \<alpha>1 s1 \<union> \<alpha>2 s2"
       "invar2 (iterate_add_to_set s2 ins2 (iteratei1 s1))" 
    by simp_all
qed


subsection {* Diff (by iterator) *}

definition it_diff where
  "it_diff iteratei1 del2 \<equiv> (\<lambda>s2 s1. iterate_diff_set s2 del2 (iteratei1 s1))"

lemma it_diff_code[code]: 
  "it_diff it del s1 s2 = it s2 (\<lambda>_. True) del s1"
unfolding it_diff_def iterate_diff_set_def by simp

lemma it_diff_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  assumes S1: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes S2: "set_delete \<alpha>2 invar2 del2"
  shows "set_diff \<alpha>2 invar2 \<alpha>1 invar1 (it_diff iteratei1 del2)"
unfolding it_diff_def
proof 
  fix s1 s2
  assume "invar1 s1"
  with set_iteratei.iteratei_rule [OF S1, of s1]
  have iti_s: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  assume "invar2 s2" 
  with iterate_diff_correct[OF S2 _ iti_s, of s2] 
  show "\<alpha>2 (iterate_diff_set s2 del2 (iteratei1 s1)) = \<alpha>2 s2 - \<alpha>1 s1"
       "invar2 (iterate_diff_set s2 del2 (iteratei1 s1))" 
    by simp_all
qed


subsection {*Intersection (by iterator)*}

definition it_inter
  :: "('s1 \<Rightarrow> ('x,'s3) set_iterator) \<Rightarrow> 
      ('x \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> 
      (unit \<Rightarrow> 's3) \<Rightarrow> 
      ('x \<Rightarrow> 's3 \<Rightarrow> 's3) \<Rightarrow> 
      's1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  where
  "it_inter iteratei1 memb2 empt3 insrt3 s1 s2 \<equiv>
   iterate_to_set empt3 insrt3 (set_iterator_filter (\<lambda>x. memb2 x s2) (iteratei1 s1))"

lemma it_inter_code[code] :
  "it_inter iteratei1 memb2 empt3 insrt3 s1 s2 == 
              iteratei1 s1 (\<lambda>_. True) (\<lambda>x s. if memb2 x s2 then insrt3 x s else s) (empt3 ())"
   unfolding it_inter_def iterate_to_set_alt_def set_iterator_filter_alt_def by simp

lemma it_inter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  fixes \<alpha>3 :: "'s3 \<Rightarrow> 'x set"
  assumes it1: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes memb2: "set_memb \<alpha>2 invar2 memb2"
  assumes emp3: "set_empty \<alpha>3 invar3 empty3"
  assumes ins3: "set_ins_dj \<alpha>3 invar3 ins3"
  shows "set_inter \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 (it_inter iteratei1 memb2 empty3 ins3)"
proof 
  fix s1 s2
  assume "invar1 s1" "invar2 s2"

  from set_iteratei.iteratei_rule [OF it1, OF `invar1 s1`]
  have iti_s1: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  have "{x \<in> \<alpha>1 s1. memb2 x s2} = \<alpha>1 s1 \<inter> \<alpha>2 s2" using `invar2 s2` memb2
    unfolding set_memb_def by auto
  with set_iterator_filter_correct [OF iti_s1, of "\<lambda>x. memb2 x s2"]
  have iti_s12: "set_iterator (set_iterator_filter (\<lambda>x. memb2 x s2) (iteratei1 s1)) (\<alpha>1 s1 \<inter> \<alpha>2 s2)"
    by simp

  from iterate_to_set_correct[OF ins3 emp3 iti_s12]
  show "\<alpha>3 (it_inter iteratei1 memb2 empty3 ins3 s1 s2) = \<alpha>1 s1 \<inter> \<alpha>2 s2"
       "invar3 (it_inter iteratei1 memb2 empty3 ins3 s1 s2)"
    unfolding it_inter_def by simp_all
qed 
 

subsection {* Subset (by ball)*}
definition ball_subset ::
  "('s1 \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
  where "ball_subset ball1 mem2 s1 s2 == ball1 s1 (\<lambda>x. mem2 x s2)"

lemma ball_subset_correct:
  assumes "set_ball \<alpha>1 invar1 ball1"
  assumes "set_memb \<alpha>2 invar2 mem2"
  shows "set_subset \<alpha>1 invar1 \<alpha>2 invar2 (ball_subset ball1 mem2)"
proof -
  interpret s1: set_ball \<alpha>1 invar1 ball1 by fact
  interpret s2: set_memb \<alpha>2 invar2 mem2 by fact
  
  show ?thesis
    apply (unfold_locales)
    apply (unfold ball_subset_def)
    apply (auto simp add: s1.ball_correct s2.memb_correct)
    done
qed

subsection {* Equality Test (by subset) *}
definition subset_equal ::
  "('s1 \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> ('s2 \<Rightarrow> 's1 \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
  where "subset_equal ss1 ss2 s1 s2 == ss1 s1 s2 \<and> ss2 s2 s1"

lemma subset_equal_correct:
  assumes "set_subset \<alpha>1 invar1 \<alpha>2 invar2 ss1"
  assumes "set_subset \<alpha>2 invar2 \<alpha>1 invar1 ss2"
  shows "set_equal \<alpha>1 invar1 \<alpha>2 invar2 (subset_equal ss1 ss2)"
proof -
  interpret s1: set_subset \<alpha>1 invar1 \<alpha>2 invar2 ss1 by fact
  interpret s2: set_subset \<alpha>2 invar2 \<alpha>1 invar1 ss2 by fact

  show ?thesis
    apply unfold_locales
    apply (unfold subset_equal_def)
    apply (auto simp add: s1.subset_correct s2.subset_correct)
    done
qed

subsection {*Image-Filter (by iterate)*}

definition it_image_filter
  :: "('s1 \<Rightarrow> ('a,_) set_iterator) \<Rightarrow> (unit \<Rightarrow> 's2) \<Rightarrow> ('b \<Rightarrow> 's2 \<Rightarrow> 's2) 
      \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  where "it_image_filter iteratei1 empty2 ins2 f s == 
         iterate_to_set empty2 ins2 (set_iterator_image_filter f (iteratei1 s))"

lemma it_image_filter_code[code] :
  "it_image_filter iteratei1 empty2 ins2 f s == 
   iteratei1 s (\<lambda>_. True) (\<lambda>x res. case f x of Some v \<Rightarrow> ins2 v res | _ \<Rightarrow> res) (empty2 ())"
unfolding it_image_filter_def iterate_to_set_alt_def set_iterator_image_filter_def
by simp

lemma it_image_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x1 set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x2 set"
  assumes iti1: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes emp2: "set_empty \<alpha>2 invar2 empty2"
  assumes ins: "set_ins \<alpha>2 invar2 ins2"
  shows "set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (it_image_filter iteratei1 empty2 ins2)"
proof 
  fix s and f :: "'x1 \<Rightarrow> 'x2 option"
  assume "invar1 s" 
  from set_iteratei.iteratei_rule [OF iti1, OF `invar1 s`]
  have iti_s1: "set_iterator (iteratei1 s) (\<alpha>1 s)" by simp

  from iterate_image_filter_to_set_correct[OF ins emp2 iti_s1]
  show "\<alpha>2 (it_image_filter iteratei1 empty2 ins2 f s) =
        {b. \<exists>a\<in>\<alpha>1 s. f a = Some b}"
       "invar2 (it_image_filter iteratei1 empty2 ins2 f s)"
    unfolding it_image_filter_def by auto
qed


subsection {* Injective Image-Filter (by iterate)*}

definition [code_unfold] : "it_inj_image_filter = it_image_filter"

lemma it_inj_image_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x1 set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x2 set"
  assumes iti1: "set_iteratei \<alpha>1 invar1 iteratei1"
  assumes emp2: "set_empty \<alpha>2 invar2 empty2"
  assumes ins_dj2: "set_ins_dj \<alpha>2 invar2 ins2"
  shows "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 
            (it_inj_image_filter iteratei1 empty2 ins2)"
proof 
  fix s and f :: "'x1 \<Rightarrow> 'x2 option"
  assume "invar1 s" "inj_on f (\<alpha>1 s \<inter> dom f)"
  from set_iteratei.iteratei_rule [OF iti1, OF `invar1 s`]
  have iti_s1: "set_iterator (iteratei1 s) (\<alpha>1 s)" by simp

  from set_iterator_image_filter_correct [OF iti_s1, OF `inj_on f (\<alpha>1 s \<inter> dom f)`]
  have iti_s1_filter: "set_iterator (set_iterator_image_filter f (iteratei1 s))
     {y. \<exists>x. x \<in> \<alpha>1 s \<and> f x = Some y}"
    by simp

  from iterate_to_set_correct[OF ins_dj2 emp2, OF iti_s1_filter]
  show "\<alpha>2 (it_inj_image_filter iteratei1 empty2 ins2 f s) =
        {b. \<exists>a\<in>\<alpha>1 s. f a = Some b}"
       "invar2 (it_inj_image_filter iteratei1 empty2 ins2 f s)"
    unfolding it_inj_image_filter_def it_image_filter_def by auto
qed


subsection "Image (by image-filter)"
definition "iflt_image iflt f s == iflt (\<lambda>x. Some (f x)) s"

lemma iflt_image_correct:
  assumes "set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_image \<alpha>1 invar1 \<alpha>2 invar2 (iflt_image iflt)"
proof -
  interpret set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold iflt_image_def)
    apply (auto simp add: image_filter_correct)
    done
qed

subsection{* Injective Image-Filter (by image-filter)*}

definition [code_unfold]: "iflt_inj_image = iflt_image"

lemma iflt_inj_image_correct:
  assumes "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_inj_image \<alpha>1 invar1 \<alpha>2 invar2 (iflt_inj_image iflt)"
proof -
  interpret set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold iflt_image_def iflt_inj_image_def)
    apply (subst inj_image_filter_correct)
    apply (auto simp add: dom_const intro: inj_onI dest: inj_onD)
    apply (subst inj_image_filter_correct)
    apply (auto simp add: dom_const intro: inj_onI dest: inj_onD)
    done
qed


subsection{* Filter (by image-filter)*}
definition "iflt_filter iflt P s == iflt (\<lambda>x. if P x then Some x else None) s"

lemma iflt_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'a set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'a set"
  assumes "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_filter \<alpha>1 invar1 \<alpha>2 invar2 (iflt_filter iflt)"
proof (rule set_filter.intro)
  fix s P
  assume invar_s: "invar1 s"
  interpret S: set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact

  let ?f' = "\<lambda>x::'a. if P x then Some x else None"
  have inj_f': "inj_on ?f' (\<alpha>1 s \<inter> dom ?f')"
    by (simp add: inj_on_def Ball_def domIff)
  note correct' = S.inj_image_filter_correct [OF invar_s inj_f',
    folded iflt_filter_def]

  show "invar2 (iflt_filter iflt P s)"
       "\<alpha>2 (iflt_filter iflt P s) = {e \<in> \<alpha>1 s. P e}"
    by (auto simp add: correct')
qed


subsection {* union-list *}

definition fold_union_list where
  "fold_union_list emp un l =
  foldl (\<lambda>s s'. un s s') (emp ()) l"

lemma fold_union_list_correct :
  assumes emp_OK: "set_empty \<alpha> invar emp"
  assumes un_OK: "set_union \<alpha> invar \<alpha> invar \<alpha> invar un"
  shows "set_union_list \<alpha> invar \<alpha> invar (fold_union_list emp un)"
proof
  fix l
  note correct = set_empty.empty_correct[OF emp_OK]
                 set_union.union_correct[OF un_OK]

  assume "\<forall>s1\<in>set l. invar s1"
  hence aux: "\<And>s. invar s \<Longrightarrow>
         \<alpha> (foldl (\<lambda>s s'. un s s') s l) = \<Union>{\<alpha> s1 |s1. s1 \<in> set l} \<union> \<alpha> s \<and>
         invar (foldl (\<lambda>s s'. un s s') s l)"
    by (induct l) (auto simp add: correct)

  from aux [of "emp()"]
  show "\<alpha> (fold_union_list emp un l) = \<Union>{\<alpha> s1 |s1. s1 \<in> set l}"
       "invar (fold_union_list emp un l)"
    unfolding fold_union_list_def
    by (simp_all add: correct)
qed

function paired_union_list :: "_ \<Rightarrow> _ \<Rightarrow> 'a set list \<Rightarrow> 'a set list \<Rightarrow> 'a set" where
   "paired_union_list emp un [] [] = emp ()"
 | "paired_union_list emp un [] [s] = s"
 | "paired_union_list emp un (s1 # l1) [] = paired_union_list emp un [] (s1 # l1)"
 | "paired_union_list emp un (s1 # l1) [s2] = paired_union_list emp un [] (s2 # s1 # l1)"
 | "paired_union_list emp un l1 (s1 # s2 # l2) = 
    paired_union_list emp un ((un s1 s2) # l1) l2"
by pat_completeness simp_all
termination
by (relation "measure (\<lambda>(_, _, l1, l2). 3 * length l1 + 2 * length l2)") (simp_all)

lemma paired_union_list_correct :
  assumes emp_OK: "set_empty \<alpha> invar emp"
  assumes un_OK: "set_union \<alpha> invar \<alpha> invar \<alpha> invar un"
  shows "set_union_list \<alpha> invar \<alpha> invar (paired_union_list emp un [])"
proof
  fix l
  note correct = set_empty.empty_correct[OF emp_OK]
                 set_union.union_correct[OF un_OK]

  assume l_OK: "\<forall>s1\<in>set l. invar s1"
  { fix as
    from correct l_OK
    have "\<forall>s\<in>set as. invar s \<Longrightarrow>
         \<alpha> (paired_union_list emp un as l) = \<Union>{\<alpha> s1 |s1. s1 \<in> set (as @ l)} \<and>
         invar (paired_union_list emp un as l)" (is "_ \<Longrightarrow> ?P emp un as l")
    proof (induct emp un as l rule: paired_union_list.induct)
      case 1 thus ?case by simp
    next
      case 2 thus ?case by simp
    next
      case 3 thus ?case by simp
    next
      case 4 thus ?case by auto
    next
      case (5 emp un l1 s1 s2 l2) 
      from 5(1-7) have ind_hyp: "?P emp un ((un s1 s2)#l1) l2" by simp
      note l1_OK = 5(2)
      note emp_un_correct = 5(3-6)
      note s12_l2_OK = 5(7)

      from emp_un_correct s12_l2_OK have un_s12: "\<alpha> (un s1 s2) = \<alpha> s1 \<union> \<alpha> s2" by simp

      from un_s12
      show ?case by (simp add: ind_hyp) auto
    qed
  } note aux = this

  from aux[of "[]"]
  show "\<alpha> (paired_union_list emp un [] l) = \<Union>{\<alpha> s1 |s1. s1 \<in> set l}"
       "invar (paired_union_list emp un [] l)" by simp_all
qed


subsection {* Union of image of Set (by iterate) *}
definition it_Union_image
  :: "('s1 \<Rightarrow> ('x,_) set_iterator) \<Rightarrow> (unit \<Rightarrow> 's3) \<Rightarrow> ('s2 \<Rightarrow> 's3 \<Rightarrow> 's3) 
      \<Rightarrow> ('x \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's3"
where "it_Union_image iti1 em3 un233 f S == 
  iti1 S (\<lambda>_. True) (\<lambda>x res. un233 (f x) res) (em3 ())"

lemma it_Union_image_correct:
  assumes "set_iteratei \<alpha>1 invar1 iti1"
  assumes "set_empty \<alpha>3 invar3 em3"
  assumes "set_union \<alpha>2 invar2 \<alpha>3 invar3 \<alpha>3 invar3 un233"
  shows "set_Union_image \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 (it_Union_image iti1 em3 un233)"
proof -
  interpret set_iteratei \<alpha>1 invar1 iti1 by fact
  interpret set_empty \<alpha>3 invar3 em3 by fact
  interpret set_union \<alpha>2 invar2 \<alpha>3 invar3 \<alpha>3 invar3 un233 by fact
  
  {
    fix s f
    have "\<lbrakk>invar1 s; \<And>x. x \<in> \<alpha>1 s \<Longrightarrow> invar2 (f x)\<rbrakk> \<Longrightarrow> 
      \<alpha>3 (it_Union_image iti1 em3 un233 f s) = \<Union>\<alpha>2 ` f ` \<alpha>1 s 
      \<and> invar3 (it_Union_image iti1 em3 un233 f s)"
      apply (unfold it_Union_image_def)
      apply (rule_tac I="\<lambda>it res. invar3 res \<and> \<alpha>3 res = \<Union>\<alpha>2`f`(\<alpha>1 s - it)" in iterate_rule_P)
      apply (fastforce simp add: empty_correct union_correct)+
      done
  }
  thus ?thesis
    apply unfold_locales
    apply auto
    done
qed

subsection {* Disjointness Check with Witness (by sel)*}
definition "sel_disjoint_witness sel1 mem2 s1 s2 ==
  sel1 s1 (\<lambda>x. if mem2 x s2 then Some x else None)"

lemma sel_disjoint_witness_correct:
  assumes "set_sel \<alpha>1 invar1 sel1"
  assumes "set_memb \<alpha>2 invar2 mem2"
  shows "set_disjoint_witness \<alpha>1 invar1 \<alpha>2 invar2 (sel_disjoint_witness sel1 mem2)"
proof -
  interpret s1: set_sel \<alpha>1 invar1 sel1 by fact
  interpret s2: set_memb \<alpha>2 invar2 mem2 by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold sel_disjoint_witness_def)
    apply (auto dest: s1.sel_noneD 
                elim: s1.sel_someD  
                simp add: s2.memb_correct 
                split: split_if_asm)
    done
qed

subsection {* Disjointness Check (by ball) *}
definition "ball_disjoint ball1 memb2 s1 s2 == ball1 s1 (\<lambda>x. \<not> memb2 x s2)"

lemma ball_disjoint_correct:
  assumes "set_ball \<alpha>1 invar1 ball1"
  assumes "set_memb \<alpha>2 invar2 memb2"
  shows "set_disjoint \<alpha>1 invar1 \<alpha>2 invar2 (ball_disjoint ball1 memb2)"
proof -
  interpret s1: set_ball \<alpha>1 invar1 ball1 by fact
  interpret s2: set_memb \<alpha>2 invar2 memb2 by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold ball_disjoint_def)
    apply (auto simp add: s1.ball_correct s2.memb_correct)
    done
qed

subsection {* Selection (by iteratei) *}

definition iti_sel where
  "iti_sel iti = (\<lambda>s f. iterate_sel (iti s) f)"

lemma iti_sel_code[code]:
  "iti_sel iti s f = iti s (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. f x) None"
unfolding iti_sel_def iterate_sel_def by simp

lemma iti_sel_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_sel \<alpha> invar (iti_sel iti)"
unfolding set_sel_def iti_sel_def
using iterate_sel_genord_correct [OF set_iteratei.iteratei_rule [OF iti, unfolded set_iterator_def]]
apply (simp add: Bex_def) apply clarify
apply (metis option.exhaust)
done


subsection {* Map-free selection by selection *}
definition sel_sel'
  :: "('s \<Rightarrow> ('x \<Rightarrow> _ option) \<Rightarrow> _ option) \<Rightarrow> 's \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> 'x option"
where "sel_sel' sel s P = sel s (\<lambda>x. if P x then Some x else None)"

lemma sel_sel'_correct: 
  assumes "set_sel \<alpha> invar sel"
  shows "set_sel' \<alpha> invar (sel_sel' sel)"
proof -
  interpret set_sel \<alpha> invar sel by fact

  show ?thesis
  proof
    case goal1 show ?case
      apply (rule selE[OF goal1(1,2), where f="(\<lambda>x. if P x then Some x else None)"])
      apply (simp add: goal1)
      apply (simp split: split_if_asm)
      apply (fold sel_sel'_def)
      apply (blast intro: goal1(4))
      done
  next
    case goal2 thus ?case
      apply (auto simp add: sel_sel'_def)
      apply (drule selI[where f="(\<lambda>x. if P x then Some x else None)"])
      apply auto
      done
  qed
qed


subsection {* Map-free selection by iterate *}

definition iti_sel_no_map where
  "iti_sel_no_map iti = (\<lambda>s P. iterate_sel_no_map (iti s) P)"

lemma iti_sel_no_map_code[code]:
  "iti_sel_no_map iti s f = iti s (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. if f x then Some x else None) None"
unfolding iti_sel_no_map_def iterate_sel_no_map_alt_def by simp

lemma iti_sel'_correct: 
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_sel' \<alpha> invar (iti_sel_no_map iti)"
unfolding set_sel'_def iti_sel_no_map_def
using iterate_sel_no_map_correct [OF set_iteratei.iteratei_rule [OF iti]]
apply (simp add: Bex_def Ball_def)
apply (metis option.exhaust)
done
      
subsection {*Set to List (by iterate)*}

definition it_set_to_list where
  "it_set_to_list iti = (\<lambda>s. iterate_to_list (iti s))"

lemma it_set_to_list_code[code] :
  "it_set_to_list iti s = iti s (\<lambda>_. True) op# []"
unfolding it_set_to_list_def iterate_to_list_def by simp

lemma it_set_to_list_correct:
  assumes iti: "set_iteratei \<alpha> invar iti"
  shows "set_to_list \<alpha> invar (it_set_to_list iti)"
unfolding it_set_to_list_def
proof 
  fix s 
  assume "invar s"
  with set_iteratei.iteratei_rule [OF iti, of s]
  have iti_s: "set_iterator (iti s) (\<alpha> s)" by simp

  from iterate_to_list_correct [OF iti_s]
  show "set (iterate_to_list (iti s)) = \<alpha> s"
       "distinct (iterate_to_list (iti s))" by simp_all
qed

subsection {*List to Set*}
-- {* Tail recursive version *}
fun gen_list_to_set_aux
  :: "('x \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 'x list \<Rightarrow> 's"
  where
  "gen_list_to_set_aux ins accs [] = accs" |
  "gen_list_to_set_aux ins accs (x#l) = gen_list_to_set_aux ins (ins x accs) l"

definition "gen_list_to_set empt ins == gen_list_to_set_aux ins (empt ())"

lemma gen_list_to_set_correct:
  assumes "set_empty \<alpha> invar empt"
  assumes "set_ins \<alpha> invar ins"
  shows "list_to_set \<alpha> invar (gen_list_to_set empt ins)"
proof -
  interpret set_empty \<alpha> invar empt by fact
  interpret set_ins \<alpha> invar ins by fact

  { -- "Show a generalized lemma"
    fix l accs
    have "invar accs \<Longrightarrow> \<alpha> (gen_list_to_set_aux ins accs l) = set l \<union> \<alpha> accs 
          \<and> invar (gen_list_to_set_aux ins accs l)"
      by (induct l arbitrary: accs)
         (auto simp add: ins_correct)
  } thus ?thesis
    apply (unfold_locales)
    apply (unfold gen_list_to_set_def)
    apply (auto simp add: empty_correct)
    done
qed


subsection "More Generic Set Algorithms"
text {*
  These algorithms do not have a function specification in a locale, but
  their specification is done  ad-hoc in the correctness lemma.
*}

subsubsection "Image and Filter of Cartesian Product"

definition image_filter_cartesian_product 
  :: "('s1 \<Rightarrow> ('x,'s3) set_iterator) \<Rightarrow> 
      ('s2 \<Rightarrow> ('y,'s3) set_iterator) \<Rightarrow> 
      (unit \<Rightarrow> 's3) \<Rightarrow> ('z \<Rightarrow> 's3 \<Rightarrow> 's3) \<Rightarrow> 
      ('x \<times> 'y \<Rightarrow> 'z option) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  where
  "image_filter_cartesian_product iterate1 iterate2 empty3 insert3 f s1 s2 ==
   iterate_to_set empty3 insert3 (set_iterator_image_filter f (
     set_iterator_product (iterate1 s1) (\<lambda>_. iterate2 s2)))"

lemma image_filter_cartesian_product_code[code]:
  "image_filter_cartesian_product iterate1 iterate2 empty3 insert3 f s1 s2 ==
    iterate1 s1 (\<lambda>_. True) (\<lambda>x res.
      iterate2 s2 (\<lambda>_. True) (\<lambda>y res.
        case (f (x, y)) of 
          None \<Rightarrow> res
        | Some z \<Rightarrow> (insert3 z res)
      ) res
    ) (empty3 ())"
unfolding image_filter_cartesian_product_def iterate_to_set_alt_def
          set_iterator_image_filter_def set_iterator_product_def
by simp

lemma image_filter_cartesian_product_correct:
  assumes S: "set_iteratei \<alpha>1 invar1 iteratei1"
             "set_iteratei \<alpha>2 invar2 iteratei2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins \<alpha>3 invar3 ins3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  shows "\<alpha>3 (image_filter_cartesian_product iteratei1 iteratei2 empty3 ins3 f s1 s2) 
   = { z | x y z. f (x,y) = Some z \<and> x\<in>\<alpha>1 s1 \<and> y\<in>\<alpha>2 s2 }" (is ?T1)
  "invar3 (image_filter_cartesian_product iteratei1 iteratei2 empty3 ins3 f s1 s2)" (is ?T2)
proof -
  from set_iteratei.iteratei_rule [OF S(1), OF `invar1 s1`]
  have it_s1: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  from set_iteratei.iteratei_rule [OF S(2), OF `invar2 s2`]
  have it_s2: "set_iterator (iteratei2 s2) (\<alpha>2 s2)" by simp

  from set_iterator_product_correct [OF it_s1, OF it_s2]
  have it_s12: "set_iterator (set_iterator_product (iteratei1 s1) (\<lambda>_. iteratei2 s2))
                (\<alpha>1 s1 \<times> \<alpha>2 s2)" by simp

  from iterate_image_filter_to_set_correct[OF S(4) S(3) it_s12, of f]
  show ?T1 ?T2
    unfolding image_filter_cartesian_product_def by auto
qed


definition image_filter_cp where
  "image_filter_cp iterate1 iterate2 empty3 insert3 f P s1 s2 \<equiv>
   image_filter_cartesian_product iterate1 iterate2 empty3 insert3
     (\<lambda>xy. if P xy then Some (f xy) else None) s1 s2"

lemma image_filter_cp_correct:
  assumes S: "set_iteratei \<alpha>1 invar1 iterate1"
             "set_iteratei \<alpha>2 invar2 iterate2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins \<alpha>3 invar3 ins3"
  assumes I: "invar1 s1" "invar2 s2"
  shows 
  "\<alpha>3 (image_filter_cp iterate1 iterate2 empty3 ins3 f P s1 s2) 
   = { f (x, y) | x y. P (x, y) \<and> x\<in>\<alpha>1 s1 \<and> y\<in>\<alpha>2 s2 }" (is ?T1)
  "invar3 (image_filter_cp iterate1 iterate2 empty3 ins3 f P s1 s2)" (is ?T2)
proof -
  note image_filter_cartesian_product_correct [OF S, OF I]
  thus "?T1" "?T2"
    unfolding image_filter_cp_def
    by auto
qed


subsubsection "Injective Image and Filter of Cartesian Product"

definition[code_unfold]:
  "inj_image_filter_cartesian_product = image_filter_cartesian_product"

lemma inj_image_filter_cartesian_product_correct:
  assumes S: "set_iteratei \<alpha>1 invar1 iteratei1"
             "set_iteratei \<alpha>2 invar2 iteratei2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins_dj \<alpha>3 invar3 ins_dj3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  assumes INJ: "!!x y x' y' z. \<lbrakk> f (x, y) = Some z; f (x', y') = Some z \<rbrakk> \<Longrightarrow> x=x' \<and> y=y'"
  shows "\<alpha>3 (inj_image_filter_cartesian_product iteratei1 iteratei2 empty3 ins_dj3 f s1 s2) 
         = { z | x y z. f (x, y) = Some z \<and> x\<in>\<alpha>1 s1 \<and> y\<in>\<alpha>2 s2 }" (is ?T1)
  "invar3 (inj_image_filter_cartesian_product iteratei1 iteratei2 empty3 ins_dj3 f s1 s2)" (is ?T2)
proof -
  from set_iteratei.iteratei_rule [OF S(1), OF `invar1 s1`]
  have it_s1: "set_iterator (iteratei1 s1) (\<alpha>1 s1)" by simp

  from set_iteratei.iteratei_rule [OF S(2), OF `invar2 s2`]
  have it_s2: "set_iterator (iteratei2 s2) (\<alpha>2 s2)" by simp

  from set_iterator_product_correct [OF it_s1, OF it_s2]
  have it_s12: "set_iterator (set_iterator_product (iteratei1 s1) (\<lambda>_. iteratei2 s2))
                (\<alpha>1 s1 \<times> \<alpha>2 s2)" by simp

  from INJ have f_inj_on: "inj_on f (\<alpha>1 s1 \<times> \<alpha>2 s2 \<inter> dom f)" 
    unfolding inj_on_def dom_def by auto

  from iterate_inj_image_filter_to_set_correct[OF S(4) S(3) it_s12 f_inj_on]
  show ?T1 ?T2
    unfolding image_filter_cartesian_product_def inj_image_filter_cartesian_product_def 
  by auto
qed

subsubsection "Injective Image and Filter of Cartesian Product"

definition [code_unfold]: "inj_image_filter_cp = image_filter_cp"

lemma inj_image_filter_cp_correct:
  assumes S: "set_iteratei \<alpha>1 invar1 iterate1"
             "set_iteratei \<alpha>2 invar2 iterate2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins_dj \<alpha>3 invar3 ins_dj3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  assumes INJ: "!!x y x' y' z. \<lbrakk> P (x, y); P (x', y'); f (x, y) = f (x', y') \<rbrakk> \<Longrightarrow> x=x' \<and> y=y'"
  shows "\<alpha>3 (inj_image_filter_cp iterate1 iterate2 empty3 ins_dj3 f P s1 s2) 
         = { f (x, y) | x y. P (x, y) \<and> x\<in>\<alpha>1 s1 \<and> y\<in>\<alpha>2 s2 }" (is ?T1)
  "invar3 (inj_image_filter_cp iterate1 iterate2 empty3 ins_dj3 f P s1 s2)" (is ?T2)
proof -
  let ?f = "\<lambda>xy. if P xy then Some (f xy) else None"
  from INJ have INJ': 
    "!!x y x' y' z. \<lbrakk> ?f (x, y) = Some z; ?f (x', y') = Some z \<rbrakk> \<Longrightarrow> x=x' \<and> y=y'"
   by (auto simp add: split_if_eq1)

  note inj_image_filter_cartesian_product_correct [OF S, OF I,
    where f = ?f]
   
  with INJ' show "?T1" "?T2"
    unfolding image_filter_cp_def inj_image_filter_cp_def
              inj_image_filter_cartesian_product_def
    by auto
qed

subsubsection "Cartesian Product"
definition "cart it1 it2 empty3 ins3 s1 s2 == image_filter_cartesian_product it1 it2 empty3 ins3 (\<lambda>xy. Some xy) s1 s2"

lemma cart_code[code] :
"cart it1 it2 empty3 ins3 s1 s2 \<equiv>
 it1 s1 (\<lambda>_. True) (\<lambda>x. it2 s2 (\<lambda>_. True) (\<lambda>y res. ins3 (x,y) res)) (empty3 ())" 
 unfolding cart_def image_filter_cartesian_product_code
by simp

lemma cart_correct:
  assumes S: "set_iteratei \<alpha>1 invar1 iterate1"
             "set_iteratei \<alpha>2 invar2 iterate2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins_dj \<alpha>3 invar3 ins_dj3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  shows "\<alpha>3 (cart iterate1 iterate2 empty3 ins_dj3 s1 s2) 
         = \<alpha>1 s1 \<times> \<alpha>2 s2" (is ?T1)
  "invar3 (cart iterate1 iterate2 empty3 ins_dj3 s1 s2)" (is ?T2)
  apply -
  apply (unfold cart_def inj_image_filter_cartesian_product_def[symmetric])
  apply (subst inj_image_filter_cartesian_product_correct[OF S, OF I])
  apply auto
  apply (subst inj_image_filter_cartesian_product_correct[OF S, OF I])
  apply auto
  done


subsection {* Min (by iterateoi) *}

lemma itoi_min_correct: 
  assumes iti: "set_iterateoi \<alpha> invar iti"
  shows "set_min \<alpha> invar (iti_sel_no_map iti)"
unfolding set_min_def iti_sel_no_map_def
using iterate_sel_no_map_linord_correct [OF set_iterateoi.iterateoi_rule [OF iti]]
apply (simp add: Bex_def Ball_def image_iff)
apply (metis option.exhaust the.simps)
done

subsection {* Max (by reverse\_iterateoi) *}

lemma ritoi_max_correct: 
  assumes iti: "set_reverse_iterateoi \<alpha> invar iti"
  shows "set_max \<alpha> invar (iti_sel_no_map iti)"
unfolding set_max_def iti_sel_no_map_def
using iterate_sel_no_map_rev_linord_correct [OF set_reverse_iterateoi.reverse_iterateoi_rule [OF iti]]
apply (simp add: Bex_def Ball_def image_iff)
apply (metis option.exhaust the.simps)
done

subsection {*Conversion to sorted list (by reverse\_iterateo)*}

lemma rito_set_to_sorted_list_correct:
  assumes iti: "set_reverse_iterateoi \<alpha> invar iti"
  shows "set_to_sorted_list \<alpha> invar (it_set_to_list iti)"
unfolding it_set_to_list_def
proof 
  fix s 
  assume "invar s"
  with set_reverse_iterateoi.reverse_iterateoi_rule [OF iti, of s]
  have iti_s: "set_iterator_rev_linord (iti s) (\<alpha> s)" by simp

  from iterate_to_list_rev_linord_correct [OF iti_s]
  show "set (iterate_to_list (iti s)) = \<alpha> s"
       "sorted (iterate_to_list (iti s))"
       "distinct (iterate_to_list (iti s))" by simp_all
qed

end
