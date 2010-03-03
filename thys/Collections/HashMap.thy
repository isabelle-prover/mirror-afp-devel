(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Hash Maps"
theory HashMap
imports Main "common/Misc" ListMapImpl RBTMapImpl HashCode
begin
text_raw {*\label{thy:HashMap}*}

text {*
  This theory implements hashmaps. This uses the abbreviations hm,h.

  We use a red-black tree instead of an indexed array. This
  has the disadvantage of being more complex, however we need not bother
  about a fixed-size array and rehashing if the array becomes too full.

  The entries of the red-black tree are lists of (key,value) pairs.
*}

subsection {* Abstract Hashmap *}
text {*
  We first specify the behavior of our hashmap on the level of maps.
  We will then show that our implementation based on hashcode-map and bucket-map 
  is a correct implementation of this specification.
*}
types 
  ('k,'v) abs_hashmap = "hashcode \<rightharpoonup> ('k \<rightharpoonup> 'v)"

  -- "Map entry of map by function"
abbreviation map_entry where
  "map_entry k f m == m(k := f (m k))"


  -- "Invariant: Buckets only contain entries with the right hashcode and there are no empty buckets"
definition ahm_invar:: "('k::hashable,'v) abs_hashmap \<Rightarrow> bool" 
  where "ahm_invar m == 
    (\<forall>hc cm k. m hc = Some cm \<and> k\<in>dom cm \<longrightarrow> hashcode k = hc) \<and> 
    (\<forall>hc cm. m hc = Some cm \<longrightarrow> cm \<noteq> empty)"



  -- "Abstract a hashmap to the corresponding map"
definition ahm_\<alpha> where
  "ahm_\<alpha> m k == case m (hashcode k) of 
    None \<Rightarrow> None |
    Some cm \<Rightarrow> cm k"

  -- "Lookup an entry"
definition ahm_lookup :: "'k::hashable \<Rightarrow> ('k,'v) abs_hashmap \<Rightarrow> 'v option" 
  where "ahm_lookup k m == (ahm_\<alpha> m) k"

  -- "The empty hashmap"
definition ahm_empty :: "('k::hashable,'v) abs_hashmap" 
  where "ahm_empty = empty"

  -- "Update/insert an entry"
definition ahm_update where
  "ahm_update k v m ==
    case m (hashcode k) of
      None \<Rightarrow> m (hashcode k \<mapsto> [k \<mapsto> v]) |
      Some cm \<Rightarrow> m (hashcode k \<mapsto> cm (k \<mapsto> v))
  "

  -- "Delete an entry"
definition ahm_delete where 
  "ahm_delete k m == map_entry (hashcode k) 
    (\<lambda>v. case v of 
      None \<Rightarrow> None | 
      Some bm \<Rightarrow> (
        if bm |` (- {k}) = empty then
          None
        else
          Some ( bm |` (- {k}))
      )
    ) m
  "

definition ahm_isEmpty where
  "ahm_isEmpty m == m=Map.empty"

text {*
  Now follow correctness lemmas, that relate the hashmap operations to
  operations on the corresponding map. Those lemmas are named op\_correct, where
  op is the operation.
*}

lemma ahm_invarI: "\<lbrakk> 
  !!hc cm k. \<lbrakk>m hc = Some cm; k\<in>dom cm\<rbrakk> \<Longrightarrow> hashcode k = hc;
  !!hc cm. \<lbrakk> m hc = Some cm \<rbrakk> \<Longrightarrow> cm \<noteq> empty
  \<rbrakk> \<Longrightarrow> ahm_invar m"
  by (unfold ahm_invar_def) blast

lemma ahm_invarD: "\<lbrakk> ahm_invar m; m hc = Some cm; k\<in>dom cm \<rbrakk> \<Longrightarrow> hashcode k = hc"
  by (unfold ahm_invar_def) blast

lemma ahm_invarDne: "\<lbrakk> ahm_invar m; m hc = Some cm \<rbrakk> \<Longrightarrow> cm \<noteq> empty"
  by (unfold ahm_invar_def) blast

lemma ahm_invar_bucket_not_empty[simp]: 
  "ahm_invar m \<Longrightarrow> m hc \<noteq> Some Map.empty"
  by (auto dest: ahm_invarDne)

lemmas ahm_lookup_correct = ahm_lookup_def

lemma ahm_empty_correct: 
  "ahm_\<alpha> ahm_empty = empty"
  "ahm_invar ahm_empty"
  apply (rule ext)
  apply (unfold ahm_empty_def) 
  apply (auto simp add: ahm_\<alpha>_def intro: ahm_invarI split: option.split)
  done


lemma ahm_update_correct: 
  "ahm_\<alpha> (ahm_update k v m) = ahm_\<alpha> m (k \<mapsto> v)"
  "ahm_invar m \<Longrightarrow> ahm_invar (ahm_update k v m)"
  apply (rule ext)
  apply (unfold ahm_update_def)
  apply (auto simp add: ahm_\<alpha>_def split: option.split)
  apply (rule ahm_invarI)
  apply (auto dest: ahm_invarD ahm_invarDne split: split_if_asm)
  apply (rule ahm_invarI)
  apply (auto dest: ahm_invarD split: split_if_asm)
  apply (drule (1) ahm_invarD)
  apply auto
  done

lemma fun_upd_apply_ne: "x\<noteq>y \<Longrightarrow> (f(x:=v)) y = f y"
  by simp

lemma cancel_one_empty_simp: "m |` (-{k}) = Map.empty \<longleftrightarrow> dom m \<subseteq> {k}"
proof
  assume "m |` (- {k}) = Map.empty"
  hence "{} = dom (m |` (-{k}))" by auto
  also have "\<dots> = dom m - {k}" by auto
  finally show "dom m \<subseteq> {k}" by blast
next
  assume "dom m \<subseteq> {k}"
  hence "dom m - {k} = {}" by auto
  hence "dom (m |` (-{k})) = {}" by auto
  thus "m |` (-{k}) = Map.empty" by (simp only: dom_empty_simp)
qed
  
lemma ahm_delete_correct: 
  "ahm_\<alpha> (ahm_delete k m) = (ahm_\<alpha> m) |` (-{k})"
  "ahm_invar m \<Longrightarrow> ahm_invar (ahm_delete k m)"
  apply (rule ext)
  apply (unfold ahm_delete_def)
  apply (auto simp add: ahm_\<alpha>_def Let_def Map.restrict_map_def 
              split: option.split)[1]
  apply (drule_tac x=x in fun_cong)
  apply (auto)[1]
  apply (rule ahm_invarI)
  apply (auto split: split_if_asm option.split_asm dest: ahm_invarD)
  apply (drule (1) ahm_invarD)
  apply (auto simp add: restrict_map_def split: split_if_asm option.split_asm)
  done

lemma ahm_isEmpty_correct: "ahm_invar m \<Longrightarrow> ahm_isEmpty m \<longleftrightarrow> ahm_\<alpha> m = Map.empty"
proof
  assume "ahm_invar m" "ahm_isEmpty m"
  thus "ahm_\<alpha> m = Map.empty"
    by (auto simp add: ahm_isEmpty_def ahm_\<alpha>_def intro: ext)
next
  assume I: "ahm_invar m" 
    and E: "ahm_\<alpha> m = Map.empty"

  show "ahm_isEmpty m"
  proof (rule ccontr)
    assume "\<not>ahm_isEmpty m"
    then obtain hc bm where MHC: "m hc = Some bm"
      by (unfold ahm_isEmpty_def)
         (blast elim: nempty_dom dest: domD)
    from ahm_invarDne[OF I, OF MHC] obtain k v where
      BMK: "bm k = Some v"
      by (blast elim: nempty_dom dest: domD)
    from ahm_invarD[OF I, OF MHC] BMK have [simp]: "hashcode k = hc"
      by auto
    hence "ahm_\<alpha> m k = Some v"
      by (simp add: ahm_\<alpha>_def MHC BMK)
    with E show False by simp
  qed
qed
    
lemmas ahm_correct = ahm_empty_correct ahm_lookup_correct ahm_update_correct 
                     ahm_delete_correct ahm_isEmpty_correct

  -- "Bucket entries correspond to map entries"
lemma ahm_be_is_e:
  assumes I: "ahm_invar m"
  assumes A: "m hc = Some bm" "bm k = Some v"
  shows "ahm_\<alpha> m k = Some v"
  using A
  apply (auto simp add: ahm_\<alpha>_def split: option.split dest: ahm_invarD[OF I])
  apply (frule ahm_invarD[OF I, where k=k])
  apply auto
  done

  -- "Map entries correspond to bucket entries"
lemma ahm_e_is_be: "\<lbrakk>
  ahm_\<alpha> m k = Some v; 
  !!bm. \<lbrakk>m (hashcode k) = Some bm; bm k = Some v \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (unfold ahm_\<alpha>_def)
     (auto split: option.split_asm)

subsection {* Concrete Hashmap *}
text {*
  In this section, we define the concrete hashmap that is made from the 
  hashcode map and the bucket map.

  We then show the correctness of the operations w.r.t. the abstract hashmap, and
  thus, indirectly, w.r.t. the corresponding map.
*}

types
  ('k,'v) hm = "(hashcode, ('k,'v) lm) rm"

subsubsection "Operations"

  -- "Auxiliary function: Apply function to value of an entry"
definition rm_map_entry 
  :: "hashcode \<Rightarrow> ('v option \<Rightarrow> 'v option) \<Rightarrow> (hashcode, 'v) rm \<Rightarrow> (hashcode,'v) rm" 
  where 
  "rm_map_entry k f m ==
      case rm_lookup k m of
        None \<Rightarrow> (
          case f None of 
            None \<Rightarrow> m |
            Some v \<Rightarrow> rm_update k v m
        ) |
        Some v \<Rightarrow> (
          case f (Some v) of
            None \<Rightarrow> rm_delete k m |
            Some v' \<Rightarrow> rm_update k v' m
        )
    "

  -- "Empty hashmap"
definition "hm_empty == rm_empty"

  -- "Update/insert entry"
definition hm_update :: "'k::hashable \<Rightarrow> 'v \<Rightarrow> ('k,'v) hm \<Rightarrow> ('k,'v) hm"
  where 
  "hm_update k v m == 
     let hc = hashcode k in
       case rm_lookup hc m of
         None \<Rightarrow> rm_update hc (lm_sng k v) m |
         Some bm \<Rightarrow> rm_update hc (lm_update k v bm) m 
  " 

(* TODO: We could use an optimized version here, 
         utilizing disjoint update on bucket map *)
definition "hm_update_dj == hm_update"

  -- "Lookup value by key"
definition hm_lookup :: "'k::hashable \<Rightarrow> ('k,'v) hm \<Rightarrow> 'v option" where
  "hm_lookup k m ==
     case rm_lookup (hashcode k) m of
       None \<Rightarrow> None |
       Some lm \<Rightarrow> lm_lookup k lm
  "

  -- "Delete entry by key"
definition hm_delete :: "'k::hashable \<Rightarrow> ('k,'v) hm \<Rightarrow> ('k,'v) hm" where
  "hm_delete k m ==
     rm_map_entry (hashcode k) 
       (\<lambda>v. case v of 
         None \<Rightarrow> None | 
         Some lm \<Rightarrow> (
           let lm' = lm_delete k lm in
             if lm_isEmpty lm' then None else Some lm'
         )
       ) m
  "

  -- "Select arbitrary entry"
definition hm_sel 
  :: "('k::hashable,'v) hm \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "hm_sel m f == rm_sel m (\<lambda>hc lm. lm_sel lm f)"

  -- "Emptiness check"
definition "hm_isEmpty == rm_isEmpty"

  -- "Iterator"
definition "hm_iterate f m \<sigma>0 ==
  rm_iterate (\<lambda>hc lm \<sigma>. 
    lm_iterate f lm \<sigma>
  ) m \<sigma>0
"

  -- "Interruptible iterator"
definition "hm_iteratei c f m \<sigma>0 ==
  rm_iteratei c (\<lambda>hc lm \<sigma>. 
    lm_iteratei c f lm \<sigma>
  ) m \<sigma>0
"

subsubsection "Correctness w.r.t. Abstract HashMap"
text {*
  The following lemmas establish the correctness of the operations w.r.t. the 
  abstract hashmap.

  They have the naming scheme op\_correct', where op is the name of the 
  operation.
*}

  -- "Abstract concrete hashmap to abstract hashmap"
definition hm_\<alpha>' where "hm_\<alpha>' m == \<lambda>hc. case rm_\<alpha> m hc of
  None \<Rightarrow> None |
  Some lm \<Rightarrow> Some (lm_\<alpha> lm)"

  -- "Invariant for concrete hashmap: 
    The hashcode-map and bucket-maps satisfy their invariants and
    the invariant of the corresponding abstract hashmap is satisfied.
  "

definition "hm_invar m == 
  rm_invar m \<and> 
  (\<forall>hc lm. rm_\<alpha> m hc = Some lm \<longrightarrow> lm_invar lm) \<and> 
  (ahm_invar (hm_\<alpha>' m))"


lemma rm_map_entry_correct:
  "rm_invar m \<Longrightarrow> rm_\<alpha> (rm_map_entry k f m) = (rm_\<alpha> m)(k := f (rm_\<alpha> m k))"
  "rm_invar m \<Longrightarrow> rm_invar (rm_map_entry k f m)"
  apply (auto 
    simp add: rm_map_entry_def rm.delete_correct rm.lookup_correct rm.update_correct
    split: option.split)
  apply (auto simp add: Map.restrict_map_def fun_upd_def intro: ext)
  done


lemma hm_empty_correct': 
  "hm_\<alpha>' hm_empty = ahm_empty"
  "hm_invar hm_empty"
proof -
  show 1: "hm_\<alpha>' hm_empty = ahm_empty"
    apply (auto simp add: hm_\<alpha>'_def hm_empty_def ahm_empty_def)
    apply (auto simp add: hm_empty_def rm_correct)
    done
  show "hm_invar hm_empty"
    apply (unfold hm_invar_def)
    apply (auto simp add: hm_empty_def rm_correct ahm_empty_correct 
                          1[unfolded hm_empty_def])
    done
qed

lemma hm_lookup_correct': 
  "hm_invar m \<Longrightarrow> hm_lookup k m = ahm_lookup k (hm_\<alpha>' m)"
  apply (unfold hm_lookup_def hm_invar_def)
  apply (auto split: option.split 
              simp add: ahm_lookup_def ahm_\<alpha>_def hm_\<alpha>'_def 
                        rm_correct lm_correct)
  done

lemma hm_update_correct': 
  "hm_invar m \<Longrightarrow> hm_\<alpha>' (hm_update k v m) = ahm_update k v (hm_\<alpha>' m)"
  "hm_invar m \<Longrightarrow> hm_invar (hm_update k v m)"
proof -
  show 1: "hm_invar m \<Longrightarrow> hm_\<alpha>' (hm_update k v m) = ahm_update k v (hm_\<alpha>' m)"
    apply (unfold hm_invar_def)
    apply (rule ext)
    apply (auto simp add: hm_update_def ahm_update_def hm_\<alpha>'_def Let_def 
                          rm_correct lm_correct 
                split: option.split)
    done
  show "hm_invar m \<Longrightarrow> hm_invar (hm_update k v m)"
    apply (unfold hm_invar_def)
    apply (intro conjI)
    apply (auto simp add: hm_update_def Let_def rm_correct lm_correct 
                split: option.split option.split_asm split_if_asm) [2]
    apply (subst 1[unfolded hm_invar_def])
    apply simp
    apply (simp add: ahm_update_correct)
  done
qed

     
lemma hm_delete_correct':
  "hm_invar m \<Longrightarrow> hm_\<alpha>' (hm_delete k m) = ahm_delete k (hm_\<alpha>' m)"
  "hm_invar m \<Longrightarrow> hm_invar (hm_delete k m)"
proof -
  show 1: "hm_invar m \<Longrightarrow> hm_\<alpha>' (hm_delete k m) = ahm_delete k (hm_\<alpha>' m)"
    apply (unfold hm_invar_def)
    apply (rule ext)
    apply (auto simp add: hm_delete_def ahm_delete_def hm_\<alpha>'_def rm_map_entry_correct
                          rm_correct lm_correct Let_def 
                split: option.split option.split_asm) [1]
    done
  show "hm_invar m \<Longrightarrow> hm_invar (hm_delete k m)"
    apply (unfold hm_invar_def)
    apply (intro conjI)
    apply (auto simp add: hm_delete_def Let_def rm_correct lm_correct rm_map_entry_correct
                split: option.split option.split_asm split_if_asm) [2]
    apply (subst 1[unfolded hm_invar_def])
    apply simp
    apply (simp add: ahm_delete_correct)
    done
qed
  
lemmas hm_correct' = hm_empty_correct' hm_lookup_correct' hm_update_correct' 
                     hm_delete_correct'
lemmas hm_invars = hm_empty_correct'(2) hm_update_correct'(2) 
                   hm_delete_correct'(2)

subsubsection "Correctness w.r.t. Map"
text {* 
  The next lemmas establish the correctness of the hashmap operations w.r.t. the 
  associated map. This is achieved by chaining the correctness lemmas of the 
  concrete hashmap w.r.t. the abstract hashmap and the correctness lemmas of the
  abstract hashmap w.r.t. maps.
*}

  -- "Abstract concrete hashmap to map"
definition "hm_\<alpha> == ahm_\<alpha> \<circ> hm_\<alpha>'"


lemma hm_aux_correct_part:
  "hm_\<alpha> hm_empty = empty"
  "hm_invar m \<Longrightarrow> hm_lookup k m = hm_\<alpha> m k"
  "hm_invar m \<Longrightarrow> hm_\<alpha> (hm_update k v m) = (hm_\<alpha> m)(k\<mapsto>v)"
  "hm_invar m \<Longrightarrow> hm_\<alpha> (hm_delete k m) = (hm_\<alpha> m) |` (-{k})"
  by (auto simp add: hm_\<alpha>_def hm_correct' ahm_correct)

lemmas hm_aux_correct = hm_aux_correct_part hm_invars

subsection "Integration in Isabelle Collections Framework"
text {*
  In this section, we integrate hashmaps into the Isabelle Collections Framework.
*}

lemma hm_empty_impl: "map_empty hm_\<alpha> hm_invar hm_empty"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemma hm_lookup_impl: "map_lookup hm_\<alpha> hm_invar hm_lookup"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemma hm_update_impl: "map_update hm_\<alpha> hm_invar hm_update"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemmas hm_update_dj_impl 
  = map_update.update_dj_by_update[OF hm_update_impl, 
                                   folded hm_update_dj_def]

lemma hm_delete_impl: "map_delete hm_\<alpha> hm_invar hm_delete"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemma hm_finite[simp, intro!]:
  (* assumes A: "hm_invar m" *)
  shows "finite (dom (hm_\<alpha> m))"
proof -
  have SS: "dom (hm_\<alpha> m) \<subseteq> \<Union>{ dom (lm_\<alpha> lm) | lm hc. rm_\<alpha> m hc = Some lm }"
    apply auto
    apply (unfold hm_\<alpha>_def hm_\<alpha>'_def_raw ahm_\<alpha>_def_raw)
    apply (auto split: option.split_asm option.split)
    done
  show ?thesis
    apply (rule finite_subset[OF SS])
    apply rule
  proof -
    case goal1
    have "{ dom (lm_\<alpha> lm) | lm hc. rm_\<alpha> m hc = Some lm } 
          \<subseteq> (\<lambda>hc. dom (lm_\<alpha> (the (rm_\<alpha> m hc)) )) ` (dom (rm_\<alpha> m))" 
      (is "?S \<subseteq> _")
      by force
    moreover have "finite \<dots>"
      apply auto
      done
    ultimately show "finite ?S" by (blast intro: finite_subset)
  next
    case goal2
    thus ?case by auto
  qed
qed

lemma hm_is_finite_map: "finite_map hm_\<alpha> hm_invar"
  apply (unfold_locales)
  apply auto
  done

lemma hm_sel_impl: "map_sel hm_\<alpha> hm_invar hm_sel"
proof (rule map_sel_altI)
  case goal1
  hence I1[simp,intro!]: "rm_invar s" and IA: "ahm_invar (hm_\<alpha>' s)" 
    by (simp_all add: hm_invar_def)
  obtain hc lm where LME: "rm_\<alpha> s hc = Some lm" "lm_sel lm f = Some r" 
    by (erule rm.sel_someE[OF I1 goal1(2)[unfolded hm_sel_def]])
  with goal1(1) have I2[simp, intro!]: "lm_invar lm" 
    by (auto simp add: hm_invar_def)
  obtain k v where E: "lm_\<alpha> lm k = Some v" "f k v = Some r" 
    by (erule lm.sel_someE[OF I2 LME(2)])
  from LME have LMEA: "hm_\<alpha>' s hc = Some (lm_\<alpha> lm)" by (unfold hm_\<alpha>'_def) simp
  have HMA: "hm_\<alpha> s k = Some v"
    apply (unfold hm_\<alpha>_def)
    apply simp
    apply (rule ahm_be_is_e[OF IA, OF LMEA, OF E(1)])
    done
  from goal1(3)[OF HMA E(2)] show ?case .
next
  case goal2
  from goal2(1) have I1: "rm_invar s" by (unfold hm_invar_def) auto
  from goal2(3) have AE: "ahm_\<alpha> (hm_\<alpha>' s) u = Some v" by (unfold hm_\<alpha>_def) simp
  obtain lm where F1: "hm_\<alpha>' s (hashcode u) = Some lm" "lm u = Some v" 
    by (erule ahm_e_is_be[OF AE])
  from F1(1) obtain lmc where 
    F2: "rm_\<alpha> s (hashcode u) = Some lmc" "lm = lm_\<alpha> lmc" 
    by (auto simp add: hm_\<alpha>'_def split: option.split_asm)
  from goal2(1) F2(1) have I2: "lm_invar lmc" by (auto simp add: hm_invar_def)
  from F1(2) F2(2) have LMACU: "lm_\<alpha> lmc u = Some v" by simp
  from rm.sel_noneD[OF I1 goal2(2)[unfolded hm_sel_def], OF F2(1)] have 
    LMS: "lm_sel lmc f = None" .
  from lm.sel_noneD[OF I2 LMS LMACU] show ?case .
qed


lemma hm_isEmpty_impl: "map_isEmpty hm_\<alpha> hm_invar hm_isEmpty"
  apply (unfold_locales)
  thm ahm_isEmpty_correct[unfolded ahm_isEmpty_def, symmetric]
  apply (simp add: hm_isEmpty_def hm_invar_def rm.isEmpty_correct hm_\<alpha>_def
                   ahm_isEmpty_correct[unfolded ahm_isEmpty_def, symmetric])
  apply (auto simp add: hm_\<alpha>'_def intro!: ext)
  apply (drule_tac x=x in fun_cong)
  apply (auto split: option.split_asm)
  done

lemma hm_iterate_impl: 
  "map_iterate hm_\<alpha> hm_invar hm_iterate"
  apply (unfold_locales)
  apply simp
  apply (unfold hm_invar_def hm_iterate_def)
  apply clarify
proof (rule_tac I="\<lambda>it \<sigma>. I {k\<in>dom (hm_\<alpha> m). hashcode k \<in> it} \<sigma>" 
                in rm.iterate_rule_P)
  case goal1 -- "Invar" 
  thus ?case by simp
next
  case goal4 -- "Final"
  thus ?case by simp
next
  case goal2 -- "Init"
  have "{k \<in> dom (hm_\<alpha> m). hashcode k \<in> dom (rm_\<alpha> m)} = dom (hm_\<alpha> m)"
    by (auto simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
  with goal2(1) show ?case by simp
next
  case (goal3 m I \<sigma>0 f hc lm it \<sigma>) note G=this -- "Step" 
  show ?case
  proof (rule_tac 
      I="\<lambda>it2 \<sigma>. I ({k\<in>dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} 
                    \<union> {k\<in>dom (hm_\<alpha> m). hashcode k = hc \<and> k\<in>it2}) 
                   \<sigma>" 
      in lm.iterate_rule_P)
    case goal1 thus ?case using G by blast
  next
    case goal4 -- "Final"
    thus ?case by simp
  next
    case goal2 -- "Init"
    have "{k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} \<union> 
          {k \<in> dom (hm_\<alpha> m). hashcode k = hc \<and> k \<in> dom (lm_\<alpha> lm)}
         =
          {k \<in> dom (hm_\<alpha> m). hashcode k \<in> it}"
      using `hc\<in>it` `rm_\<alpha> m hc = Some lm`
      by (auto simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
    thus ?case using G by simp
  next
    case (goal3 k v it2 \<sigma>) note GG=this -- "Step"
    let ?it = "{k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} \<union>
                 {k \<in> dom (hm_\<alpha> m). hashcode k = hc \<and> k \<in> it2}"
    let ?it' = "({k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} \<union>
                 {ka \<in> dom (hm_\<alpha> m). hashcode ka = hc \<and> ka \<in> it2 - {k}})"
    have [simp]: "hashcode k = hc" 
      using G(7) GG(2) G(5)
      by (auto simp add: ahm_invar_def hm_\<alpha>'_def split: option.split_asm)
    hence I': "?it'=?it - {k}" by auto
    show ?case using G GG
      apply (simp only: I')
      apply (rule G(2)[of k ?it v \<sigma>])
      apply (auto simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
      done
  qed
qed



lemma hm_iteratei_impl: 
  "map_iteratei hm_\<alpha> hm_invar hm_iteratei"
  apply (unfold_locales)
  apply simp
  apply (unfold hm_invar_def hm_iteratei_def)
  apply (elim conjE)
proof (rule_tac I="\<lambda>it \<sigma>. 
    I {k\<in>dom (hm_\<alpha> m). hashcode k \<in> it} \<sigma> \<or> (\<exists>it'\<subseteq>dom (hm_\<alpha> m). it'\<noteq>{} \<and> \<not>c \<sigma> \<and> I it' \<sigma>)" 
                in rm.iteratei_rule_P)
  case goal1 -- "Invar" 
  thus ?case by simp
next
  case goal4 -- "Final"
  thus ?case by simp
next
  case goal5 -- "Interrupt"
  thus ?case
    apply (erule_tac disjE)
    apply (rule_tac disjI2)
    apply (rule_tac x="{k \<in> dom (hm_\<alpha> m). hashcode k \<in> it}" in exI)
    apply auto
  proof -
    case goal1
    hence "x\<in>dom (rm_\<alpha> m)" by auto
    then obtain bmc where "rm_\<alpha> m x = Some bmc" by auto
    then obtain bm where MBM: "hm_\<alpha>' m x = Some bm"
      by (simp add: hm_\<alpha>'_def)
    with goal1(5) have "bm\<noteq>Map.empty" by auto
    then obtain k v where BMK: "bm k = Some v" 
      by (blast elim: nempty_dom dest: domD)
    with ahm_invarD[OF goal1(5), OF MBM] have HCK: "hashcode k = x" by auto
    hence HMAK: "hm_\<alpha> m k = Some v" using MBM BMK
      by (simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def)
    show ?case using HMAK HCK `x\<in>it` by auto
  qed
next
  case goal2 -- "Init"
  have "{k \<in> dom (hm_\<alpha> m). hashcode k \<in> dom (rm_\<alpha> m)} = dom (hm_\<alpha> m)"
    by (auto simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
  with goal2(1) show ?case by simp
next
  case (goal3 m I \<sigma>0 c f hc lm it \<sigma>) note G=this -- "Step" 
  show ?case
  proof (rule_tac 
      I="\<lambda>it2 \<sigma>. I ({k\<in>dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} 
                    \<union> {k\<in>dom (hm_\<alpha> m). hashcode k = hc \<and> k\<in>it2}) 
                   \<sigma>" 
      in lm.iteratei_rule_P)
    case goal1 thus ?case using G by blast
  next
    case goal4 -- "Final"
    thus ?case by simp
  next
    case goal2 -- "Init"
    have "{k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} \<union> 
          {k \<in> dom (hm_\<alpha> m). hashcode k = hc \<and> k \<in> dom (lm_\<alpha> lm)}
         =
          {k \<in> dom (hm_\<alpha> m). hashcode k \<in> it}"
      using `hc\<in>it` `rm_\<alpha> m hc = Some lm`
      by (auto simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
    thus ?case using G by simp
  next
    case (goal3 k v it2 \<sigma>) note GG=this -- "Step"
    let ?it = "{k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} \<union>
                 {k \<in> dom (hm_\<alpha> m). hashcode k = hc \<and> k \<in> it2}"
    let ?it' = "({k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} \<union>
                 {ka \<in> dom (hm_\<alpha> m). hashcode ka = hc \<and> ka \<in> it2 - {k}})"
    have [simp]: "hashcode k = hc" 
      using GG(3) G(5,8)
      by (auto simp add: ahm_invar_def hm_\<alpha>'_def split: option.split_asm)
    hence I': "?it'=?it - {k}" by auto
    show ?case using G GG
      apply (simp only: I')
      apply (rule G(2)[of \<sigma> k ?it v])
      apply (auto simp add: hm_\<alpha>_def hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
      done
  next
    case (goal5 \<sigma>i ita)  -- "Interrupt"
    let ?it' = "({k \<in> dom (hm_\<alpha> m). hashcode k \<in> it - {hc}} 
                 \<union> {k \<in> dom (hm_\<alpha> m). hashcode k = hc \<and> k \<in> ita})"
    have 1: "?it' \<subseteq> dom (hm_\<alpha> m)"
      by auto
    from goal5 obtain k where KITA: "k\<in>ita" by auto
    with goal5 obtain v where AUX1: "lm_\<alpha> lm k = Some v" by auto
    from G(8) have AUX2: "hm_\<alpha>' m hc = Some (lm_\<alpha> lm)" by (simp add: hm_\<alpha>'_def)
    from ahm_invarD[OF G(5), OF AUX2] AUX1 have [simp]: "hashcode k = hc" by auto
    have "hm_\<alpha> m k = Some v"
      by (simp add: hm_\<alpha>_def ahm_\<alpha>_def AUX1 AUX2)
    with KITA have "k\<in>?it'" by auto
    hence 2: "?it' \<noteq> {}" by blast
    from goal5(3,4) 1 2 show ?case by blast
  qed
qed
    
thm it_add_def

definition "hm_add == it_add hm_update hm_iterate"
lemmas hm_add_impl = it_add_correct[OF hm_iterate_impl hm_update_impl, 
                                      folded hm_add_def]

definition "hm_add_dj == it_add_dj hm_update_dj hm_iterate"
lemmas hm_add_dj_impl = 
  it_add_dj_correct[OF hm_iterate_impl hm_update_dj_impl, 
                 folded hm_add_dj_def]

definition "hm_ball == sel_ball hm_sel"
lemmas hm_ball_impl = sel_ball_correct[OF hm_sel_impl, folded hm_ball_def]

definition "hm_to_list == it_map_to_list hm_iterate"
lemmas hm_to_list_impl = it_map_to_list_correct[OF hm_iterate_impl, 
                                                  folded hm_to_list_def]

definition "list_to_hm == gen_list_to_map hm_empty hm_update"
lemmas list_to_hm_impl = 
  gen_list_to_map_correct[OF hm_empty_impl hm_update_impl, 
                          folded list_to_hm_def]


interpretation hm: map_empty hm_\<alpha> hm_invar hm_empty using hm_empty_impl .
interpretation hm: map_lookup hm_\<alpha> hm_invar hm_lookup using hm_lookup_impl .
interpretation hm: map_update hm_\<alpha> hm_invar hm_update using hm_update_impl .
interpretation hm: map_update_dj hm_\<alpha> hm_invar hm_update_dj using hm_update_dj_impl .
interpretation hm: map_delete hm_\<alpha> hm_invar hm_delete using hm_delete_impl .
interpretation hm: finite_map hm_\<alpha> hm_invar using hm_is_finite_map .
interpretation hm: map_sel hm_\<alpha> hm_invar hm_sel using hm_sel_impl .
interpretation hm: map_isEmpty hm_\<alpha> hm_invar hm_isEmpty using hm_isEmpty_impl .
interpretation hm: map_iterate hm_\<alpha> hm_invar hm_iterate using hm_iterate_impl .
interpretation hm: map_iteratei hm_\<alpha> hm_invar hm_iteratei using hm_iteratei_impl .
interpretation hm: map_add hm_\<alpha> hm_invar hm_add using hm_add_impl .
interpretation hm: map_add_dj hm_\<alpha> hm_invar hm_add_dj using hm_add_dj_impl .
interpretation hm: map_ball hm_\<alpha> hm_invar hm_ball using hm_ball_impl .
interpretation hm: map_to_list hm_\<alpha> hm_invar hm_to_list using hm_to_list_impl .
interpretation hm: list_to_map hm_\<alpha> hm_invar list_to_hm using list_to_hm_impl .

declare hm.finite[simp del, rule del]

lemmas hm_correct =
  hm.empty_correct
  hm.lookup_correct
  hm.update_correct
  hm.update_dj_correct
  hm.delete_correct
  hm.add_correct
  hm.add_dj_correct
  hm.isEmpty_correct
  hm.ball_correct
  hm.to_list_correct
  hm.to_map_correct


subsection "Code Generation"

export_code 
  hm_empty
  hm_lookup
  hm_update
  hm_update_dj
  hm_delete
  hm_sel
  hm_isEmpty
  hm_iterate
  hm_iteratei
  hm_add
  hm_add_dj
  hm_ball
  hm_to_list
  list_to_hm
  in SML
  module_name HashMap
  file - (*"HashMap.ML"*)


end
