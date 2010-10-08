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
imports OrderedSet
begin
text_raw {*\label{thy:SetGA}*}



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
subsubsection {*Iteratei (by iterate)*}
  -- "Interruptible iterator by iterator (Inefficient)"
definition it_iteratei 
  :: "('m,'a,bool \<times> '\<sigma>) iterator \<Rightarrow> ('m,'a,'\<sigma>) iteratori" 
  where "it_iteratei iterate c f m \<sigma>0 == 
    snd (iterate (\<lambda>a (flag,\<sigma>). 
                    if \<not>flag then (False,\<sigma>) 
                    else if (c \<sigma>) then (True,f a \<sigma>) 
                    else (False,\<sigma>)) m (True,\<sigma>0)
        )"

lemma it_iteratei_correct:
  fixes empty
  assumes IT: "set_iterate \<alpha> invar iterate"
  shows "set_iteratei \<alpha> invar (it_iteratei iterate)"
proof -
  interpret set_iterate \<alpha> invar iterate by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_iteratei_def)
    apply (rule_tac 
      I="\<lambda>it (flag, \<sigma>). 
            (flag \<longrightarrow> I it \<sigma>) \<and> 
            (\<not>flag \<longrightarrow> (\<exists>it\<subseteq>(\<alpha> S). it\<noteq>{} \<and> \<not> c \<sigma> \<and> I it \<sigma>))" 
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

subsubsection {*iterate (by iteratei)*}
definition iti_iterate 
  :: "('s,'a,'\<sigma>) iteratori \<Rightarrow> ('s,'a,'\<sigma>) iterator"
  where "iti_iterate iti == iti (\<lambda>x. True)"

lemma (in set_iteratei) iti_iterate_correct:
  "set_iterate \<alpha> invar (iti_iterate iteratei)"
  apply (unfold_locales)
  apply (unfold iti_iterate_def)
  apply (rule_tac I="I" in iteratei_rule_P)
  apply auto
  done


subsubsection {* Iteratei (by iterateoi) *}
lemma iti_by_itoi: 
  assumes "set_iterateoi \<alpha> invar it"
  shows "set_iteratei \<alpha> invar it"
proof -
  interpret set_iterateoi \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in iterateoi_rule_P)
    apply blast+
    done
qed

subsubsection {* Iterate (by iterateo) *}
lemma it_by_ito: 
  assumes "set_iterateo \<alpha> invar it"
  shows "set_iterate \<alpha> invar it"
proof -
  interpret set_iterateo \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in iterateo_rule_P)
    apply blast+
    done
qed

subsubsection {* Iteratei (by reverse\_iterateoi) *}
lemma iti_by_ritoi: 
  assumes "set_reverse_iterateoi \<alpha> invar it"
  shows "set_iteratei \<alpha> invar it"
proof -
  interpret set_reverse_iterateoi \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in reverse_iterateoi_rule_P)
    apply blast+
    done
qed

subsubsection {* Iterate (by reverse\_iterateo) *}
lemma it_by_rito: 
  assumes "set_reverse_iterateo \<alpha> invar it"
  shows "set_iterate \<alpha> invar it"
proof -
  interpret set_reverse_iterateo \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (rule_tac I=I in reverse_iterateo_rule_P)
    apply blast+
    done
qed

subsubsection {* iterateo by iterateoi *}
definition itoi_iterateo
  :: "('m,'u,'\<sigma>) iteratori \<Rightarrow> ('m,'u,'\<sigma>) iterator"
  where
  "itoi_iterateo it == it (\<lambda>x. True)"

lemma (in set_iterateoi) itoi_iterateo_correct:
  shows "set_iterateo \<alpha> invar (itoi_iterateo iterateoi)"
  apply (unfold_locales)
  apply (unfold itoi_iterateo_def)
  apply (rule_tac I=I in iterateoi_rule_P)
  apply auto
  done

subsubsection {* reverse\_iterateo by reverse\_iterateoi *}
definition itoi_reverse_iterateo
  :: "('m,'u,'\<sigma>) iteratori \<Rightarrow> ('m,'u,'\<sigma>) iterator"
  where
  "itoi_reverse_iterateo it == it (\<lambda>x. True)"

lemma (in set_reverse_iterateoi) itoi_reverse_iterateo_correct:
  shows "set_reverse_iterateo \<alpha> invar (itoi_reverse_iterateo reverse_iterateoi)"
  apply (unfold_locales)
  apply (unfold itoi_reverse_iterateo_def)
  apply (rule_tac I=I in reverse_iterateoi_rule_P)
  apply auto
  done

subsection {*Emptiness check (by iteratei)*}

definition iti_isEmpty
  :: "('s,'a,bool) iteratori \<Rightarrow> 's \<Rightarrow> bool"
where "iti_isEmpty iti s == iti id (\<lambda>x res. False) s True"

lemma iti_isEmpty_correct:
  assumes "set_iteratei \<alpha> invar iti"
  shows "set_isEmpty \<alpha> invar (iti_isEmpty iti)"
proof -
  interpret set_iteratei \<alpha> invar iti by fact
  show ?thesis
    apply unfold_locales
    apply (unfold iti_isEmpty_def)
    apply (rule_tac I="\<lambda>it res. res \<longleftrightarrow> (\<alpha> s - it) = {}" in iteratei_rule_P)
    apply auto
    done
qed


subsection {*Bounded Quantification (by iteratei)*}
definition iti_ball
  :: "('s,'a,bool) iteratori \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "iti_ball it s P == it id (\<lambda>a r. P a) s True"


lemma iti_ball_correct:
  fixes ins
  assumes "set_iteratei \<alpha> invar iti"
  shows "set_ball \<alpha> invar (iti_ball iti)"
proof -
  interpret set_iteratei \<alpha> invar iti by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold iti_ball_def)
    apply (rule_tac 
      I="\<lambda>it res. res \<longleftrightarrow> (\<forall>x\<in>\<alpha> S - it. P x)" 
      in iteratei_rule_P)
    apply auto
    done
qed

subsection {* Size (by iterate)*}
definition it_size :: "('s,'x,nat) iterator \<Rightarrow> 's \<Rightarrow> nat" 
  where "it_size iterate S == iterate (\<lambda>x c. Suc c) S 0"

lemma it_size_correct:
  assumes A: "set_iterate \<alpha> invar iterate"
  shows "set_size \<alpha> invar (it_size iterate)"
proof -
  interpret set_iterate \<alpha> invar iterate by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (rule_tac I="\<lambda>it res. res = card (\<alpha> s - it)" in iterate_rule_P)
    apply auto
    apply (subgoal_tac "\<alpha> s - (it - {x}) = insert x (\<alpha> s - it)")
    apply auto
    done
qed

subsection {*Copy (by iterate)*}
definition it_copy
  :: "('s1,'x,_) iterator \<Rightarrow> 's2 \<Rightarrow> ('x \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's2"
where "it_copy iterate1 empty2 insert2 s1 == iterate1 insert2 s1 empty2"

lemma it_copy_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  assumes "set_iterate \<alpha>1 invar1 iterate1"
  assumes "set_empty \<alpha>2 invar2 empty2"
  assumes "set_ins \<alpha>2 invar2 ins2"
  shows "set_copy \<alpha>1 invar1 \<alpha>2 invar2 (it_copy iterate1 empty2 ins2)"
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
  interpret s2: set_empty \<alpha>2 invar2 empty2 by fact
  interpret s2: set_ins \<alpha>2 invar2 ins2 by fact

  show ?thesis
    apply unfold_locales
    apply (unfold it_copy_def)
    apply (rule_tac I="\<lambda>it \<sigma>. invar2 \<sigma> \<and> \<alpha>2 \<sigma> = \<alpha>1 s1 - it" in s1.iterate_rule_P, auto simp add: s2.ins_correct s2.empty_correct)+
    done
qed

subsection {*Union (by iterate)*}
  -- "Union by iterator. Append first set to second set. Result is of second set's type"
definition it_union 
  :: "('s1,'x,_) iterator \<Rightarrow> ('x \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's2"
  where "it_union iterate1 insrt2 s1 s2 == iterate1 (\<lambda>x s. insrt2 x s) s1 s2"

lemma it_union_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  assumes S1: "set_iterate \<alpha>1 invar1 iterate1"
  assumes S2: "set_ins \<alpha>2 invar2 ins2"
  shows "set_union \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>2 invar2 (it_union iterate1 ins2)"
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 using S1 .
  interpret s2: set_ins \<alpha>2 invar2 ins2 using S2 .

  show ?thesis
    apply unfold_locales
    apply (unfold it_union_def)
    apply (rule_tac 
      I="\<lambda>it res. invar2 res \<and> \<alpha>2 res = (\<alpha>1 s1 - it) \<union> \<alpha>2 s2" 
      in s1.iterate_rule_P, auto simp add: s2.ins_correct)+
    done
qed

subsection {* Disjoint Union *}
definition it_union_dj 
  :: "('s1,'x,_) iterator \<Rightarrow> ('x \<Rightarrow> 's2 \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's2"
  where "it_union_dj iterate1 ins_dj2 s1 s2 == iterate1 (\<lambda>x s. ins_dj2 x s) s1 s2"

lemma it_union_dj_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  assumes S1: "set_iterate \<alpha>1 invar1 iterate1"
  assumes S2: "set_ins_dj \<alpha>2 invar2 ins2"
  shows "set_union_dj \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>2 invar2 (it_union_dj iterate1 ins2)"
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 using S1 .
  interpret s2: set_ins_dj \<alpha>2 invar2 ins2 using S2 .

  {
    fix s1 s2
    have "\<lbrakk>invar1 s1; invar2 s2; \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}\<rbrakk> 
      \<Longrightarrow> \<alpha>2 (it_union_dj iterate1 ins2 s1 s2) = \<alpha>1 s1 \<union> \<alpha>2 s2 
          \<and> invar2 (it_union_dj iterate1 ins2 s1 s2)"
      apply (unfold it_union_dj_def)
      apply (rule_tac 
        I="\<lambda>it res. invar2 res \<and> \<alpha>2 res = (\<alpha>1 s1 - it) \<union> \<alpha>2 s2"
        in s1.iterate_rule_P)
      apply (simp_all add: s2.ins_dj_correct)
      apply (subgoal_tac "x\<notin>\<alpha>2 \<sigma>")
      apply (fastsimp simp add: s2.ins_dj_correct)
      apply blast
      done
  }
  thus ?thesis
    by unfold_locales auto
qed


subsection {*Intersection (by iterator)*}
definition it_inter
  :: "('s1,'x,'s3) iterator \<Rightarrow> 
      ('x \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> 
      's3 \<Rightarrow> 
      ('x \<Rightarrow> 's3 \<Rightarrow> 's3) \<Rightarrow> 
      's1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  where
  "it_inter iterate1 memb2 empt3 insrt3 s1 s2 == 
              iterate1 (\<lambda>x s. if memb2 x s2 then insrt3 x s else s) s1 empt3"


lemma it_inter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'x set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'x set"
  fixes \<alpha>3 :: "'s3 \<Rightarrow> 'x set"
  assumes "set_iterate \<alpha>1 invar1 iterate1"
  assumes "set_memb \<alpha>2 invar2 memb2"
  assumes "set_empty \<alpha>3 invar3 empty3"
  assumes "set_ins_dj \<alpha>3 invar3 ins3"
  shows "set_inter \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 (it_inter iterate1 memb2 empty3 ins3)"
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
  interpret s2: set_memb \<alpha>2 invar2 memb2 by fact
  interpret s3: set_empty \<alpha>3 invar3 empty3 by fact
  interpret s3: set_ins_dj \<alpha>3 invar3 ins3 by fact

  show ?thesis
    apply unfold_locales
    apply (unfold it_inter_def)
    apply (
      (rule_tac 
        I="\<lambda>it res. invar3 res \<and> \<alpha>3 res = (\<alpha>1 s1 - it) \<inter> \<alpha>2 s2"
        in s1.iterate_rule_P),
      (auto simp add: s2.memb_correct s3.empty_correct s3.ins_dj_correct))+
    done
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
  :: "('s1,'a,_) iterator \<Rightarrow> 's2 \<Rightarrow> ('b \<Rightarrow> 's2 \<Rightarrow> 's2) 
      \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  where "it_image_filter iterate1 empty2 ins2 f s == 
  iterate1 (\<lambda>x res. case f x of Some v \<Rightarrow> ins2 v res | _ \<Rightarrow> res) s empty2"

lemma it_image_filter_correct:
  assumes "set_iterate \<alpha>1 invar1 iterate1"
  assumes "set_empty \<alpha>2 invar2 empty2"
  assumes "set_ins \<alpha>2 invar2 ins2"
  shows "set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 
            (it_image_filter iterate1 empty2 ins2)"
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
  interpret s2: set_empty \<alpha>2 invar2 empty2 by fact
  interpret s2: set_ins \<alpha>2 invar2 ins2 by fact

  show ?thesis
	  apply (unfold_locales)
	  apply (unfold it_image_filter_def)
	  apply (rule_tac 
        I = "\<lambda>it res. invar2 res \<and> \<alpha>2 res = {b. \<exists>a\<in>\<alpha>1 s - it. f a = Some b}"
        in s1.iterate_rule_P)
	  apply (auto simp add: s2.empty_correct s2.ins_correct split: option.split)
	  apply (rule_tac I = "\<lambda>it res. invar2 res" in s1.iterate_rule_P)
	  apply (auto simp add: s2.empty_correct s2.ins_correct split: option.split)
	  done
qed

subsection {* Injective Image-Filter (by iterate)*}
definition it_inj_image_filter
  :: "('s1,'a,_) iterator \<Rightarrow> 's2 \<Rightarrow> ('b \<Rightarrow> 's2 \<Rightarrow> 's2) 
      \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  where "it_inj_image_filter iterate1 empty2 ins2 f s == 
  iterate1 (\<lambda>x res. case f x of Some v \<Rightarrow> ins2 v res | _ \<Rightarrow> res) s empty2"

lemma it_inj_image_filter_correct:
  assumes "set_iterate \<alpha>1 invar1 iterate1"
  assumes "set_empty \<alpha>2 invar2 empty2"
  assumes "set_ins_dj \<alpha>2 invar2 ins2"
  shows "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 
            (it_inj_image_filter iterate1 empty2 ins2)"
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
  interpret s2: set_empty \<alpha>2 invar2 empty2 by fact
  interpret s2: set_ins_dj \<alpha>2 invar2 ins2 by fact

  {
    fix s f
    have "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s \<inter> dom f)\<rbrakk> \<Longrightarrow> 
      \<alpha>2 (it_inj_image_filter iterate1 empty2 ins2 f s) 
        = {b. \<exists>a\<in>\<alpha>1 s. f a = Some b}
      \<and> invar2 (it_inj_image_filter iterate1 empty2 ins2 f s)"
      apply (unfold it_inj_image_filter_def)
      apply (rule_tac 
        I = "\<lambda>it res. invar2 res \<and> \<alpha>2 res = {b. \<exists>a\<in>\<alpha>1 s - it. f a = Some b}"
        in s1.iterate_rule_P)
      apply simp
      apply (simp add: s2.empty_correct s2.ins_dj_correct)
      apply (case_tac "f x")
      apply (fastsimp)
      apply simp
      apply (subgoal_tac "a\<notin>\<alpha>2 \<sigma>")
      apply (auto simp add: s2.ins_dj_correct) [1]
      apply auto [1]
      apply (drule_tac f=f and x=x and y=aa in inj_onD)
      apply auto [5]
      done
  } thus ?thesis
    apply (unfold_locales)
    apply auto
    done
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
definition "iflt_inj_image iflt f s == iflt (\<lambda>x. Some (f x)) s"

lemma iflt_inj_image_correct:
  assumes "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_inj_image \<alpha>1 invar1 \<alpha>2 invar2 (iflt_inj_image iflt)"
proof -
  interpret set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold iflt_inj_image_def)
    apply (subst inj_image_filter_correct)
    apply (auto simp add: dom_const intro: inj_onI dest: inj_onD)
    apply (subst inj_image_filter_correct)
    apply (auto simp add: dom_const intro: inj_onI dest: inj_onD)
    done
qed

subsection {* Union of image of Set (by iterate) *}
definition it_Union_image
  :: "('s1,'x,_) iterator \<Rightarrow> 's3 \<Rightarrow> ('s2 \<Rightarrow> 's3 \<Rightarrow> 's3) 
      \<Rightarrow> ('x \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's3"
where "it_Union_image it1 em3 un233 f S == 
  it1 (\<lambda>x res. un233 (f x) res) S em3"

lemma it_Union_image_correct:
  assumes "set_iterate \<alpha>1 invar1 it1"
  assumes "set_empty \<alpha>3 invar3 em3"
  assumes "set_union \<alpha>2 invar2 \<alpha>3 invar3 \<alpha>3 invar3 un233"
  shows "set_Union_image \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 (it_Union_image it1 em3 un233)"
proof -
  interpret set_iterate \<alpha>1 invar1 it1 by fact
  interpret set_empty \<alpha>3 invar3 em3 by fact
  interpret set_union \<alpha>2 invar2 \<alpha>3 invar3 \<alpha>3 invar3 un233 by fact
  
  {
    fix s f
    have "\<lbrakk>invar1 s; \<And>x. x \<in> \<alpha>1 s \<Longrightarrow> invar2 (f x)\<rbrakk> \<Longrightarrow> 
      \<alpha>3 (it_Union_image it1 em3 un233 f s) = \<Union>\<alpha>2 ` f ` \<alpha>1 s 
      \<and> invar3 (it_Union_image it1 em3 un233 f s)"
      apply (unfold it_Union_image_def)
      apply (rule_tac I="\<lambda>it res. invar3 res \<and> \<alpha>3 res = \<Union>\<alpha>2`f`(\<alpha>1 s - it)" in iterate_rule_P)
      apply (fastsimp simp add: empty_correct union_correct)+
      done
  }
  thus ?thesis
    apply unfold_locales
    apply auto
    done
qed

subsection {* Disjointness Check with Witness (by sel)*}
definition "sel_disjoint_witness sel1 mem2 s1 s2 ==
  sel1 s1 (\<lambda>x. if mem2 x s2 then Some x else None)
"

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
definition iti_sel ::
  "('s,'a,_) iteratori \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> 'r option) \<rightharpoonup> 'r"
where "iti_sel iti S f == 
  iti (\<lambda>r. r=None) (\<lambda>x res. f x) S None
"

lemma iti_sel_correct:
  assumes "set_iteratei \<alpha> invar iti"
  shows "set_sel \<alpha> invar (iti_sel iti)"
proof -
  interpret set_iteratei \<alpha> invar iti by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold iti_sel_def)
    defer
    apply (rule_tac I="\<lambda>it res. res=None" in iteratei_rule_P)
    apply auto[5]
  proof -
    case goal1
    from goal1(1,2,3) have 
      "\<exists>x r. iti (\<lambda>r. r=None) (\<lambda>x res. f x) s None = Some r 
        \<and> x\<in>\<alpha> s 
        \<and> f x = Some r"
      apply (rule_tac 
        I="\<lambda>it res. 
          case res of
            None \<Rightarrow> \<forall>x\<in>\<alpha> s - it. f x = None |
            Some r \<Rightarrow> \<exists>x\<in>\<alpha> s - it. f x = Some r" 
        in iteratei_rule_P)
      apply (simp_all split: option.split option.split_asm)
      apply blast+
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
      
subsection {*Set to List (by iterate)*}
definition it_set_to_list
  :: "('s,'x,_) iterator \<Rightarrow> 's \<Rightarrow> 'x list"
  where "it_set_to_list iterate s == iterate (\<lambda>x l. x#l) s []"

lemma it_set_to_list_correct:
  assumes "set_iterate \<alpha> invar iterate"
  shows "set_to_list \<alpha> invar (it_set_to_list iterate)"
proof -
  interpret set_iterate \<alpha> invar iterate by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_set_to_list_def)
    apply (rule_tac I="\<lambda>it res. set res = \<alpha> s - it" in iterate_rule_P)
    apply auto [4]
    apply (rule_tac I="\<lambda>it res. set res \<inter> it = {} \<and> distinct res" 
                    in iterate_rule_P)
    apply auto
    done
qed

subsection {*List to Set*}
-- {* Tail recursive version *}
fun gen_list_to_set_aux
  :: "('x \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 'x list \<Rightarrow> 's"
  where
  "gen_list_to_set_aux ins accs [] = accs" |
  "gen_list_to_set_aux ins accs (x#l) = gen_list_to_set_aux ins (ins x accs) l"

definition "gen_list_to_set empt ins == gen_list_to_set_aux ins empt"

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

definition image_filter_cp 
  :: "('s1,'x,'s3) iterator \<Rightarrow> 
      ('s2,'y,'s3) iterator \<Rightarrow> 
      's3 \<Rightarrow> ('z \<Rightarrow> 's3 \<Rightarrow> 's3) \<Rightarrow> 
      ('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  where
  "image_filter_cp iterate1 iterate2 empty3 insert3 f P s1 s2 ==
    iterate1 (\<lambda>x res.
      iterate2 (\<lambda>y res.
        if P x y then insert3 (f x y) res else res
      ) s2 res
    ) s1 empty3
  "

lemma image_filter_cp_correct:
  assumes S: "set_iterate \<alpha>1 invar1 iterate1"
             "set_iterate \<alpha>2 invar2 iterate2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins \<alpha>3 invar3 ins3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  shows 
  "\<alpha>3 (image_filter_cp iterate1 iterate2 empty3 ins3 f P s1 s2) 
   = { f x y | x y. P x y \<and> x\<in>\<alpha>1 s1 \<and> y\<in>\<alpha>2 s2 }" (is ?T1)
  "invar3 (image_filter_cp iterate1 iterate2 empty3 ins3 f P s1 s2)" (is ?T2)
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
  interpret s2: set_iterate \<alpha>2 invar2 iterate2 by fact
  interpret s3: set_empty \<alpha>3 invar3 empty3 by fact
  interpret s3: set_ins \<alpha>3 invar3 ins3 by fact

  have "?T1 \<and> ?T2"
    apply (unfold image_filter_cp_def)
    apply (rule_tac 
           I="\<lambda>it res. invar3 res \<and> 
                \<alpha>3 res = { f x y | x y. P x y \<and> x\<in>\<alpha>1 s1 - it \<and> y\<in>\<alpha>2 s2 }" 
           in s1.iterate_rule_P)
        -- "Invar"
      apply simp
        -- "Init"
      apply (simp add: s3.empty_correct)
	      -- "Step"
	    apply (rule_tac 
             I="\<lambda>it2 res2. invar3 res2 \<and> 
                \<alpha>3 res2 = { f x y | x y. P x y \<and> x\<in>\<alpha>1 s1 - it \<and> y\<in>\<alpha>2 s2 } 
                          \<union> { f x y | y. P x y \<and> y\<in>\<alpha>2 s2 - it2 }" 
             in s2.iterate_rule_P)
	        -- "Invar"
        apply simp
	        -- "Init"
        apply simp
	        -- "Step"
	      apply (auto simp add: s3.ins_correct) [1]
	        -- "Final"
	      apply auto [1]
	      -- "Final"
      apply simp
    done
  thus ?T1 ?T2 by auto
qed

subsubsection "Injective Image and Filter of Cartesian Product"
definition inj_image_filter_cp 
  :: "('s1,'x,'s3) iterator \<Rightarrow> 
      ('s2,'y,'s3) iterator \<Rightarrow> 
      's3 \<Rightarrow> ('z \<Rightarrow> 's3 \<Rightarrow> 's3) \<Rightarrow> 
      ('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> ('x \<Rightarrow> 'y \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  where
  "inj_image_filter_cp iterate1 iterate2 empty3 insert_dj3 f P s1 s2 ==
    iterate1 (\<lambda>x res.
      iterate2 (\<lambda>y res.
        if P x y then insert_dj3 (f x y) res else res
      ) s2 res
    ) s1 empty3
  "

lemma inj_image_filter_cp_correct:
  assumes S: "set_iterate \<alpha>1 invar1 iterate1"
             "set_iterate \<alpha>2 invar2 iterate2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins_dj \<alpha>3 invar3 ins_dj3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  assumes INJ: "!!x y x' y'. \<lbrakk> P x y; P x' y'; f x y = f x' y' \<rbrakk> \<Longrightarrow> x=x' \<and> y=y'"
  shows "\<alpha>3 (inj_image_filter_cp iterate1 iterate2 empty3 ins_dj3 f P s1 s2) 
         = { f x y | x y. P x y \<and> x\<in>\<alpha>1 s1 \<and> y\<in>\<alpha>2 s2 }" (is ?T1)
  "invar3 (inj_image_filter_cp iterate1 iterate2 empty3 ins_dj3 f P s1 s2)" (is ?T2)
proof -
  interpret s1: set_iterate \<alpha>1 invar1 iterate1 by fact
  interpret s2: set_iterate \<alpha>2 invar2 iterate2 by fact
  interpret s3: set_empty \<alpha>3 invar3 empty3 by fact
  interpret s3: set_ins_dj \<alpha>3 invar3 ins_dj3 by fact

  have "?T1 \<and> ?T2"
    apply (unfold inj_image_filter_cp_def)
    apply (rule_tac 
           I="\<lambda>it res. invar3 res \<and> 
                \<alpha>3 res = { f x y | x y. P x y \<and> x\<in>\<alpha>1 s1 - it \<and> y\<in>\<alpha>2 s2 }" 
      in s1.iterate_rule_P)
        -- "Invar"
      apply simp
	      -- "Init"
      apply (simp add: s3.empty_correct)
	      -- "Step"
	    apply (rule_tac 
             I="\<lambda>it2 res2. invar3 res2 \<and> 
                  \<alpha>3 res2 = { f x y | x y. P x y \<and> x\<in>\<alpha>1 s1 - it \<and> y\<in>\<alpha>2 s2 } 
                            \<union> { f x y | y. P x y \<and> y\<in>\<alpha>2 s2 - it2 }" 
        in s2.iterate_rule_P)
	        -- "Invar"
        apply simp
	        -- "Init"
        apply simp
	        -- "Step"
        apply (subgoal_tac "P x xa \<Longrightarrow> f x xa \<notin> \<alpha>3 \<sigma>'")
	      apply (auto simp add: s3.ins_dj_correct) [1]
        apply (auto dest: INJ) [1]
	        -- "Final"
	      apply auto [1]

        -- "Final"
      apply simp
    done
  thus ?T1 ?T2 by auto
qed

subsubsection "Cartesian Product"
definition "cart it1 it2 empty3 ins3 s1 s2 == inj_image_filter_cp it1 it2 empty3 ins3 (\<lambda>x y. (x,y)) (\<lambda>x y. True) s1 s2"

lemma cart_correct:
  assumes S: "set_iterate \<alpha>1 invar1 iterate1"
             "set_iterate \<alpha>2 invar2 iterate2"
             "set_empty \<alpha>3 invar3 empty3"
             "set_ins_dj \<alpha>3 invar3 ins_dj3"
  assumes I[simp, intro!]: "invar1 s1" "invar2 s2"
  shows "\<alpha>3 (cart iterate1 iterate2 empty3 ins_dj3 s1 s2) 
         = \<alpha>1 s1 \<times> \<alpha>2 s2" (is ?T1)
  "invar3 (cart iterate1 iterate2 empty3 ins_dj3 s1 s2)" (is ?T2)
  apply -
  apply (unfold cart_def)
  apply (subst inj_image_filter_cp_correct[OF S, OF I])
  apply simp_all
  apply (subst inj_image_filter_cp_correct[OF S, OF I])
  apply simp_all
  done

lemmas inj_image_filter_cp_correct[where f=Pair and P="\<lambda>x y. True", folded cart_def, simplified]



subsection {* Min (by iterateoi) *}
definition itoi_min :: "('s,'k::linorder,_) iteratori \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k) option"
  where "itoi_min it m P ==
    it (\<lambda>x. x=None) (\<lambda>k res. if P k then Some (k) else None) m None
  "

lemma itoi_min_correct:
  assumes "set_iterateoi \<alpha> invar it"
  shows "set_min \<alpha> invar (itoi_min it)"
proof -
  interpret set_iterateoi \<alpha> invar it by fact
  
  show ?thesis 
    apply (unfold_locales)
    apply (unfold itoi_min_def)
    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> { x\<in>\<alpha> s - it. P x } = {} | 
        Some x \<Rightarrow> x\<in>\<alpha> s \<and> P x 
                      \<and> (\<forall>x'\<in>\<alpha> s. P x' \<longrightarrow> x \<le> x')"
      in iterateoi_rule_P)
    apply (auto split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> { x\<in>\<alpha> s - it. P x } = {} | 
        Some x \<Rightarrow> x\<in>\<alpha> s \<and> P x 
                      \<and> (\<forall>x'\<in>\<alpha> s. P x' \<longrightarrow> x \<le> x')"
      in iterateoi_rule_P)
    apply (auto split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> { x\<in>\<alpha> s - it. P x } = {} | 
        Some x \<Rightarrow> x\<in>\<alpha> s \<and> P x 
                      \<and> (\<forall>x'\<in>\<alpha> s. P x' \<longrightarrow> x \<le> x')"
      in iterateoi_rule_P)
    apply (auto split: option.split_asm) [5]
    done
qed


subsection {* Max (by reverse\_iterateoi) *}
definition ritoi_max :: "('s,'k::linorder,_) iteratori \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k) option"
  where "ritoi_max it m P ==
    it (\<lambda>x. x=None) (\<lambda>k res. if P k then Some (k) else None) m None
  "

lemma ritoi_max_correct:
  assumes "set_reverse_iterateoi \<alpha> invar it"
  shows "set_max \<alpha> invar (ritoi_max it)"
proof -
  interpret set_reverse_iterateoi \<alpha> invar it by fact
  
  show ?thesis 
    apply (unfold_locales)
    apply (unfold ritoi_max_def)
    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> { x\<in> \<alpha> s - it. P x} = {} | 
        Some x \<Rightarrow> x\<in>\<alpha> s \<and> P x 
                      \<and> (\<forall>x'\<in>\<alpha> s. P x' \<longrightarrow> x \<ge> x')"
      in reverse_iterateoi_rule_P)
    apply (auto split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> { x\<in> \<alpha> s - it. P x} = {} | 
        Some x \<Rightarrow> x\<in>\<alpha> s \<and> P x 
                      \<and> (\<forall>x'\<in>\<alpha> s. P x' \<longrightarrow> x \<ge> x')"
      in reverse_iterateoi_rule_P)
    apply (auto split: option.split_asm) [5]

    apply (rule_tac 
      I="\<lambda>it res. 
      case res of 
        None \<Rightarrow> { x\<in> \<alpha> s - it. P x} = {} | 
        Some x \<Rightarrow> x\<in>\<alpha> s \<and> P x 
                      \<and> (\<forall>x'\<in>\<alpha> s. P x' \<longrightarrow> x \<ge> x')"
      in reverse_iterateoi_rule_P)
    apply (auto split: option.split_asm) [5]
    done
qed

subsection {*Conversion to sorted list (by reverse\_iterateo)*}

definition rito_set_to_sorted_list
  :: "('m,'u,('u) list) iterator \<Rightarrow> 'm \<Rightarrow> ('u) list"
  where "rito_set_to_sorted_list iterate m == iterate (\<lambda>u res. u#res) m []"

lemma rito_set_to_sorted_list_correct:
  assumes "set_reverse_iterateo \<alpha> invar iterate"
  shows "set_to_sorted_list \<alpha> invar (rito_set_to_sorted_list iterate)"
proof -
  interpret set_reverse_iterateo \<alpha> invar iterate by fact
  show ?thesis
    apply unfold_locales
    apply (unfold rito_set_to_sorted_list_def)
    apply (rule_tac I="\<lambda>it res. set res = \<alpha> s - it" in reverse_iterateo_rule_P)
    apply auto [4]
    apply (rule_tac 
      I="\<lambda>it res. set res \<inter> it = {} \<and> distinct res" 
      in reverse_iterateo_rule_P)
    apply auto
    apply (rule_tac 
      I="\<lambda>it res. set res = \<alpha> m - it \<and> sorted res" 
      in reverse_iterateo_rule_P)
    apply (auto simp add: sorted_Cons)
    done
qed

end
