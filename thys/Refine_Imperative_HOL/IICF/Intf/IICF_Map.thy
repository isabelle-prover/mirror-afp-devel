section \<open>Map Interface\<close>
theory IICF_Map
imports "../../Sepref"
begin
  
subsection \<open>Parametricity for Maps\<close>
definition [to_relAPP]: "map_rel K V \<equiv> (K \<rightarrow> \<langle>V\<rangle>option_rel)
  \<inter> { (mi,m). dom mi \<subseteq> Domain K \<and> dom m \<subseteq> Range K }"
(*
definition [to_relAPP]: "map_rel K V \<equiv> (K \<rightarrow> \<langle>V\<rangle>option_rel)
  \<inter> { (mi,m). dom mi \<subseteq> Domain K \<and> dom m \<subseteq> Range K 
      \<and> ran mi \<subseteq> Domain V \<and> ran m \<subseteq> Range V }"
*)

lemma map_rel_Id[simp]: "\<langle>Id,Id\<rangle>map_rel = Id" 
  unfolding map_rel_def by auto

lemma map_rel_empty1_simp[simp]: 
  "(Map.empty,m)\<in>\<langle>K,V\<rangle>map_rel \<longleftrightarrow> m=Map.empty"
  apply (auto simp: map_rel_def)
  by (meson RangeE domIff option_rel_simp(1) subsetCE tagged_fun_relD_none)

lemma map_rel_empty2_simp[simp]: 
  "(m,Map.empty)\<in>\<langle>K,V\<rangle>map_rel \<longleftrightarrow> m=Map.empty"
  apply (auto simp: map_rel_def)
  by (meson Domain.cases domIff fun_relD2 option_rel_simp(2) subset_eq)

lemma map_rel_obtain1:
  assumes 1: "(m,n)\<in>\<langle>K,V\<rangle>map_rel"
  assumes 2: "n l = Some w"
  obtains k v where "m k = Some v" "(k,l)\<in>K" "(v,w)\<in>V"
  using 1 unfolding map_rel_def
proof clarsimp
  assume R: "(m, n) \<in> K \<rightarrow> \<langle>V\<rangle>option_rel"
  assume "dom n \<subseteq> Range K"
  with 2 obtain k where "(k,l)\<in>K" by auto
  moreover from fun_relD[OF R this] have "(m k, n l) \<in> \<langle>V\<rangle>option_rel" .
  with 2 obtain v where "m k = Some v" "(v,w)\<in>V" by (cases "m k"; auto)
  ultimately show thesis by - (rule that)
qed

lemma map_rel_obtain2:
  assumes 1: "(m,n)\<in>\<langle>K,V\<rangle>map_rel"
  assumes 2: "m k = Some v"
  obtains l w where "n l = Some w" "(k,l)\<in>K" "(v,w)\<in>V"
  using 1 unfolding map_rel_def
proof clarsimp
  assume R: "(m, n) \<in> K \<rightarrow> \<langle>V\<rangle>option_rel"
  assume "dom m \<subseteq> Domain K"
  with 2 obtain l where "(k,l)\<in>K" by auto
  moreover from fun_relD[OF R this] have "(m k, n l) \<in> \<langle>V\<rangle>option_rel" .
  with 2 obtain w where "n l = Some w" "(v,w)\<in>V" by (cases "n l"; auto)
  ultimately show thesis by - (rule that)
qed

lemma param_dom[param]: "(dom,dom)\<in>\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K\<rangle>set_rel"
  apply (rule fun_relI)
  unfolding map_rel_def set_rel_def dom_def
  apply (clarsimp; safe)
  subgoal proof -
    fix a :: "'a \<Rightarrow> 'b option" and a' :: "'c \<Rightarrow> 'd option" and x :: 'c and y :: 'd
    assume a1: "{a. \<exists>y. a' a = Some y} \<subseteq> Range K"
    assume a2: "a' x = Some y"
    assume a3: "(a, a') \<in> K \<rightarrow> \<langle>V\<rangle>option_rel"
    have "\<And>c. \<not> (\<exists>d. a' c = Some d) \<or> c \<in> Range K"
      using a1 by blast
    then have "\<exists>aa. (\<exists>b. a aa = Some b) \<and> (aa, x) \<in> K"
      using a3 a2 by (metis (no_types) RangeE fun_relD2 not_None_eq option_rel_simp(1))
    then show "x \<in> K `` {aa. \<exists>b. a aa = Some b}"
      by blast
  qed
  by (metis (no_types, hide_lams) fun_relD1 not_None_eq option_rel_simp(2))

subsection \<open>Interface Type\<close>

sepref_decl_intf ('k,'v) i_map is "'k \<rightharpoonup> 'v"

lemma [synth_rules]: "\<lbrakk>INTF_OF_REL K TYPE('k); INTF_OF_REL V TYPE('v)\<rbrakk> 
  \<Longrightarrow> INTF_OF_REL (\<langle>K,V\<rangle>map_rel) TYPE(('k,'v) i_map)" by simp

subsection \<open>Operations\<close>
  sepref_decl_op map_empty: "Map.empty" :: "\<langle>K,V\<rangle>map_rel" .
  
  sepref_decl_op map_is_empty: "op = Map.empty" :: "\<langle>K,V\<rangle>map_rel \<rightarrow> bool_rel"
    apply (rule fref_ncI)
    apply parametricity
    apply (rule fun_relI; auto)
    done

  sepref_decl_op map_update: "\<lambda>k v m. m(k\<mapsto>v)" :: "K \<rightarrow> V \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
    where "single_valued K" "single_valued (K\<inverse>)"
    apply (rule fref_ncI)
    apply parametricity
    unfolding map_rel_def
    apply (intro fun_relI)
    apply (elim IntE; rule IntI)
    apply (intro fun_relI)
    apply parametricity
    apply (simp add: pres_eq_iff_svb)
    apply auto
    done
    
  sepref_decl_op map_delete: "\<lambda>k m. fun_upd m k None" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
    where "single_valued K" "single_valued (K\<inverse>)"
    apply (rule fref_ncI)
    apply parametricity
    unfolding map_rel_def
    apply (intro fun_relI)
    apply (elim IntE; rule IntI)
    apply (intro fun_relI)
    apply parametricity
    apply (simp add: pres_eq_iff_svb)
    apply auto
    done

  sepref_decl_op map_lookup: "\<lambda>k (m::'k\<rightharpoonup>'v). m k" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>V\<rangle>option_rel"
    apply (rule fref_ncI)
    apply parametricity
    unfolding map_rel_def
    apply (intro fun_relI)
    apply (elim IntE)
    apply parametricity
    done
    
  lemma in_dom_alt: "k\<in>dom m \<longleftrightarrow> \<not>is_None (m k)" by (auto split: option.split)

  sepref_decl_op map_contains_key: "\<lambda>k m. k\<in>dom m" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> bool_rel"
    unfolding in_dom_alt
    apply (rule fref_ncI)
    apply parametricity
    unfolding map_rel_def
    apply (elim IntE)
    apply parametricity
    done

subsection \<open>Patterns\<close>

lemma pat_map_empty[pat_rules]: "\<lambda>\<^sub>2_. None \<equiv> op_map_empty" by simp

lemma pat_map_is_empty[pat_rules]: 
  "op =$m$(\<lambda>\<^sub>2_. None) \<equiv> op_map_is_empty$m" 
  "op =$(\<lambda>\<^sub>2_. None)$m \<equiv> op_map_is_empty$m" 
  "op =$(dom$m)${} \<equiv> op_map_is_empty$m"
  "op =${}$(dom$m) \<equiv> op_map_is_empty$m"
  unfolding atomize_eq
  by (auto dest: sym)

lemma pat_map_update[pat_rules]: 
  "fun_upd$m$k$(Some$v) \<equiv> op_map_update$'k$'v$'m"
  by simp
lemma pat_map_lookup[pat_rules]: "m$k \<equiv> op_map_lookup$'k$'m"
  by simp

lemma op_map_delete_pat[pat_rules]: 
  "op |` $ m $ (uminus $ (insert $ k $ {})) \<equiv> op_map_delete$'k$'m"
  "fun_upd$m$k$None \<equiv> op_map_delete$'k$'m"
  by simp_all

lemma op_map_contains_key[pat_rules]: 
  "op \<in> $ k $ (dom$m) \<equiv> op_map_contains_key$'k$'m"
  "Not$(op =$(m$k)$None) \<equiv> op_map_contains_key$'k$'m"
   by (auto intro!: eq_reflection)


subsection \<open>Parametricity\<close>

locale map_custom_empty = 
  fixes op_custom_empty :: "'k\<rightharpoonup>'v"
  assumes op_custom_empty_def: "op_custom_empty = op_map_empty"
begin
  sepref_register op_custom_empty :: "('kx,'vx) i_map"

  lemma fold_custom_empty:
    "Map.empty = op_custom_empty"
    "op_map_empty = op_custom_empty"
    "mop_map_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all
end

end
