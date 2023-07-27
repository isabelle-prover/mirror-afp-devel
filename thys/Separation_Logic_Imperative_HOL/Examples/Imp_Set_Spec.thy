section \<open>Interface for Sets\<close>
theory Imp_Set_Spec
imports "../Sep_Main"
begin
text \<open>
  This file specifies an abstract interface for set data structures. It can
  be implemented by concrete set data structures, as demonstrated in the 
  hash set example.
\<close>

locale imp_set =
  fixes is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  assumes precise: "precise is_set"

locale imp_set_empty = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes empty :: "'s Heap"
  assumes empty_rule[sep_heap_rules]: "<emp> empty <is_set {}>\<^sub>t"

locale imp_set_is_empty = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_empty :: "'s \<Rightarrow> bool Heap"
  assumes is_empty_rule[sep_heap_rules]: 
    "<is_set s p> is_empty p <\<lambda>r. is_set s p * \<up>(r \<longleftrightarrow> s={})>\<^sub>t"

locale imp_set_memb = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes memb :: "'a \<Rightarrow> 's \<Rightarrow> bool Heap"
  assumes memb_rule[sep_heap_rules]: 
    "<is_set s p> memb a p <\<lambda>r. is_set s p * \<up>(r \<longleftrightarrow> a \<in> s)>\<^sub>t"

locale imp_set_ins = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes ins_rule[sep_heap_rules]: 
    "<is_set s p> ins a p <is_set (Set.insert a s)>\<^sub>t"
    
locale imp_set_delete = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes delete :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes delete_rule[sep_heap_rules]: 
    "<is_set s p> delete a p <is_set (s - {a})>\<^sub>t"

locale imp_set_size = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes size :: "'s \<Rightarrow> nat Heap"
  assumes size_rule[sep_heap_rules]: 
    "<is_set s p> size p <\<lambda>r. is_set s p * \<up>(r = card s)>\<^sub>t"

locale imp_set_iterate = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_it :: "'a set \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'s \<Rightarrow> ('it) Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> ('a\<times>'it) Heap"
  assumes it_init_rule[sep_heap_rules]: 
    "<is_set s p> it_init p <is_it s p s>\<^sub>t"
  assumes it_next_rule[sep_heap_rules]: "s'\<noteq>{} \<Longrightarrow> 
    <is_it s p s' it> 
      it_next it 
    <\<lambda>(a,it'). is_it s p (s' - {a}) it' * \<up>(a \<in> s')>\<^sub>t"
  assumes it_has_next_rule[sep_heap_rules]: 
    "<is_it s p s' it> it_has_next it <\<lambda>r. is_it s p s' it * \<up>(r\<longleftrightarrow>s'\<noteq>{})>\<^sub>t"
  assumes quit_iteration:
    "is_it s p s' it \<Longrightarrow>\<^sub>A is_set s p * true"


locale imp_set_union = imp_set_iterate +
  fixes union :: "'s \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes union_rule[sep_heap_rules]: 
    "finite se \<Longrightarrow> <(is_set s p) * (is_set se q)> union p q <\<lambda>r.  
    \<exists>\<^sub>As'. is_set s' r * (is_set se q)* true *  \<up> (s' = s \<union> se)>"

(* TODO: Move Generic implementation*)

partial_function (heap) set_it_union
  where [code]: "set_it_union 
    it_has_next it_next set_ins it a = do {
      co \<leftarrow> it_has_next it;
      if co then do {
        (x,it') \<leftarrow> it_next it;
        insx <- set_ins x a;
        set_it_union it_has_next it_next set_ins it' (insx) 
      } else return a
    }"



lemma set_it_union_rule:
    assumes "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes "imp_set_ins is_set set_ins"
    assumes FIN: "finite it"
    shows "
    < is_it b q it iti * is_set a p> 
      set_it_union it_has_next it_next set_ins iti p 
    < \<lambda>r. \<exists>\<^sub>As'. is_set s' r *  is_set b q  * true * \<up> (s' = a \<union> it) >"
  proof -
    interpret imp_set_iterate is_set is_it it_init it_has_next it_next
        + imp_set_ins is_set set_ins
      by fact+

    from FIN show ?thesis
    proof (induction  arbitrary: a p iti rule: finite_psubset_induct)
      case (psubset it)
      show ?case
        apply (subst set_it_union.simps)
        using imp_set_iterate_axioms
        apply (sep_auto heap: psubset.IH)
        by (metis ent_refl_true ent_star_mono_true quit_iteration star_aci(2))
    qed
  qed


definition union_loop_ins  where 
"union_loop_ins it_init it_has_next it_next set_ins a b \<equiv> do { 
    it <- (it_init b);
    set_it_union it_has_next it_next set_ins it a
    }"



lemma set_union_rule:
    assumes IT: "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes INS: "imp_set_ins is_set set_ins"
    assumes finb: "finite b"
    shows "
    <is_set a p * is_set b q>
   union_loop_ins it_init  it_has_next it_next set_ins p q
    <\<lambda>r.  \<exists>\<^sub>As'. is_set s' r * true * is_set b q * \<up> (s' = a \<union> b)>"
  proof -
    interpret 
      imp_set_iterate is_set is_it it_init it_has_next it_next
        + imp_set_ins is_set set_ins
      by fact+

    note it_aux[sep_heap_rules] = set_it_union_rule[OF IT INS finb]
    show ?thesis
      unfolding union_loop_ins_def
       apply (sep_auto)
      done
  qed


end
