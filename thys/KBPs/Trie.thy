(* Title: Implementation of a trie
   Author: Andreas Lochbihler < andreas dot lochbihler at kit dot edu >
   Author: Peter Gammie (gross simplification), 2010
*)


header "Trie"

theory Trie imports
  Main
  MapOps
  ODList
begin


(* From AssocList2 *)

text {* a more general update for assoc lists that uses the former value to compute the updated value *}

fun
  update_with :: "'val \<Rightarrow> 'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "update_with v k f [] = [(k, f v)]"
| "update_with v k f (p # ps) = (if (fst p = k) then (k, f (snd p)) # ps else p # update_with v k f ps)"

lemma map_of_update_with':
  "map_of (update_with v k f ps) k' = ((map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))) k'"
  by (induct ps) auto

lemma map_of_update_with:
  "map_of (update_with v k f ps) = (map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))"
  by (simp add: fun_eq_iff map_of_update_with')

text {* definitions for tries *}

datatype ('key, 'val) trie = Trie "'val option" "('key \<times> ('key, 'val) trie) list"

abbreviation
  trie_empty :: "('key, 'val) trie"
where
  "trie_empty \<equiv> Trie None []"

fun
  is_empty_trie :: "('key, 'val) trie \<Rightarrow> bool"
where
  "is_empty_trie (Trie vo ts) \<longleftrightarrow> vo = None \<and> ts = []"

lemma is_empty_trie_conv:
  "is_empty_trie ts \<longleftrightarrow> ts = trie_empty"
  by (cases ts) (simp)

fun trie_lookup :: "('key, 'val) trie \<Rightarrow> 'key list \<rightharpoonup> 'val"
where
  "trie_lookup (Trie vo _) [] = vo"
| "trie_lookup (Trie _ ts) (k#ks) = (case map_of ts k of None \<Rightarrow> None | Some t \<Rightarrow> trie_lookup t ks)"

fun
  trie_update_with :: "'key list \<Rightarrow> 'val \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where
  "trie_update_with []     v f (Trie vo ts) = Trie (Some (f (case vo of None \<Rightarrow> v | Some v' \<Rightarrow> v'))) ts"
| "trie_update_with (k#ks) v f (Trie vo ts) = Trie vo (update_with trie_empty k (trie_update_with ks v f) ts)"

abbreviation
  trie_update_with' :: "'k list \<Rightarrow> ('k, 'v) trie \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) trie"
where
  "trie_update_with' \<equiv> (\<lambda>k m v f. trie_update_with k v f m)"

definition
  trie_update :: "'key list \<Rightarrow> 'val \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where
  "trie_update k v t = trie_update_with k v (\<lambda>v'. v) t"

text {* @{term "trie_lookup"} *}

lemma trie_lookup_empty [simp]:
  "trie_lookup trie_empty ks = None"
  by (cases ks) (simp_all)

lemma trie_lookup_trie_update_with:
  "trie_lookup (trie_update_with ks v f t) ks'
 = (if ks = ks' then Some (f (case trie_lookup t ks of None \<Rightarrow> v | Some v' \<Rightarrow> v')) else trie_lookup t ks')"
proof(induct ks v f t arbitrary: ks' rule: trie_update_with.induct)
  case (1 v f vo ts ks')
  show ?case by (fastsimp simp add: neq_Nil_conv dest: not_sym)
next
  case (2 k ks v f vo ts ks')
  note IH = `\<And>t ks'. trie_lookup (trie_update_with ks v f t) ks' = (if ks = ks' then Some (f (case trie_lookup t ks of None \<Rightarrow> v | Some v' \<Rightarrow> v')) else trie_lookup t ks')`
  show ?case by(cases ks')(auto simp add: map_of_update_with IH split: option.split)
qed

lemma trie_lookup_trie_update:
  "trie_lookup (trie_update ks v t) ks' = (if ks = ks' then Some v else trie_lookup t ks')"
  unfolding trie_update_def by (simp add: trie_lookup_trie_update_with)

text{* @{term "MapOps"} *}

definition
  trie_MapOps :: "(('k, 'e) trie, 'k list, 'e) MapOps"
where
  "trie_MapOps \<equiv>
     \<lparr> MapOps.empty = trie_empty,
       lookup = trie_lookup,
       update = trie_update \<rparr>"

lemma trie_MapOps[intro, simp]:
  "inj_on \<alpha> { x . \<alpha> x \<in> d } \<Longrightarrow> MapOps \<alpha> d trie_MapOps"
  apply rule
  unfolding trie_MapOps_def
  apply (auto dest: inj_onD simp add: trie_lookup_trie_update)
  done

definition
  "trie_odlist_lookup = (\<lambda>M. trie_lookup M \<circ> toList)"

definition
  "trie_odlist_update = (\<lambda>k v. trie_update (toList k) v)"

definition
  trie_odlist_update_with :: "('k :: linorder) odlist \<Rightarrow> ('k, 'v) trie \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) trie"
where
  "trie_odlist_update_with = (\<lambda>k m v f. trie_update_with (toList k) v f m)"

definition
  trie_odlist_MapOps :: "(('k, 'e) trie, ('k ::linorder) odlist, 'e) MapOps"
where
  "trie_odlist_MapOps \<equiv>
     \<lparr> MapOps.empty = trie_empty,
       lookup = trie_odlist_lookup,
       update = trie_odlist_update \<rparr>"

lemma trie_odlist_MapOps[intro, simp]:
  "inj_on \<alpha> { x . \<alpha> x \<in> d } \<Longrightarrow> MapOps \<alpha> d trie_odlist_MapOps"
  apply rule
  unfolding trie_odlist_MapOps_def trie_odlist_lookup_def trie_odlist_update_def
  apply (auto dest: inj_onD simp add: trie_lookup_trie_update)
  done


end

