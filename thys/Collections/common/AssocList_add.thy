theory AssocList_add imports
  "~~/src/HOL/Library/AList_Impl"
begin

text {* @{term map_ran} with more general type - lemmas replicated from AList_Impl in HOL/Library *}

hide_const (open) map_ran

primrec
  map_ran :: "('key \<Rightarrow> 'val \<Rightarrow> 'val') \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val') list"
where
    "map_ran f [] = []"
  | "map_ran f (p#ps) = (fst p, f (fst p) (snd p)) # map_ran f ps"

subsection {* @{const map_ran} *}

lemma map_ran_conv: "map_of (map_ran f al) k = Option.map (f k) (map_of al k)"
  by (induct al) auto

lemma dom_map_ran: "fst ` set (map_ran f al) = fst ` set al"
  by (induct al) auto

lemma distinct_map_ran: "distinct (map fst al) \<Longrightarrow> distinct (map fst (map_ran f al))"
  by (induct al) (auto simp add: dom_map_ran)

lemma map_ran_filter: "map_ran f [(a, _)\<leftarrow>ps. fst p \<noteq> a] = [(a, _)\<leftarrow>map_ran f ps. fst p \<noteq> a]"
  by (induct ps) auto

lemma clearjunk_map_ran: "clearjunk (map_ran f al) = map_ran f (clearjunk al)"
by (induct al rule: clearjunk.induct) (simp_all add: delete_eq map_ran_filter)

text {* new lemmas and definitions *}

lemma map_ran_cong [fundef_cong]:
  "\<lbrakk> al = al'; \<And>k v. (k, v) \<in> set al \<Longrightarrow> f k v = g k v \<rbrakk> \<Longrightarrow> map_ran f al = map_ran g al'"
by clarify (induct al', auto)

lemma list_size_delete: "list_size f (delete a al) \<le> list_size f al"
by(induct al) simp_all

lemma list_size_clearjunk: "list_size f (clearjunk al) \<le> list_size f al"
by(induct al)(auto simp add: clearjunk_delete intro: le_trans[OF list_size_delete])

lemma set_delete_conv: "set (delete a al) = set al - ({a} \<times> UNIV)"
proof(induct al)
  case (Cons kv al)
  thus ?case by(cases kv) auto
qed simp

lemma set_clearjunk_subset: "set (clearjunk al) \<subseteq> set al"
by(induct al)(auto simp add: clearjunk_delete set_delete_conv)

lemma map_ran_conv_map:
  "map_ran f xs = map (\<lambda>(k, v). (k, f k v)) xs"
by(induct xs) auto

lemma card_dom_map_of: "distinct (map fst al) \<Longrightarrow> card (dom (map_of al)) = length al"
by(induct al)(auto simp add: card_insert_if finite_dom_map_of dom_map_of_conv_image_fst)

lemma map_of_map_inj_fst:
  assumes "inj f"
  shows "map_of (map (\<lambda>(k, v). (f k, v)) xs) (f x) = map_of xs x"
by(induct xs)(auto dest: injD[OF `inj f`])

lemma length_map_ran [simp]: "length (map_ran f xs) = length xs"
by(induct xs) simp_all

text {* a more general update for assoc lists that uses the former value to compute the updated value *}

primrec update_with :: "'val \<Rightarrow> 'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "update_with v k f [] = [(k, f v)]"
| "update_with v k f (p # ps) = (if (fst p = k) then (k, f (snd p)) # ps else p # update_with v k f ps)"

lemma map_of_update_with':
  "map_of (update_with v k f ps) k' = ((map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))) k'"
by(induct ps) auto

lemma map_of_update_with:
  "map_of (update_with v k f ps) = (map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))"
by(simp add: fun_eq_iff map_of_update_with')

lemma dom_update_with: "fst ` set (update_with v k f ps) = {k} \<union> fst ` set ps"
  by (induct ps) auto

lemma distinct_update_with [simp]:
  "distinct (map fst (update_with v k f ps)) = distinct (map fst ps)"
by(induct ps)(auto simp add: dom_update_with)

lemma length_update: 
  "length (update k v xs) = (if k \<in> fst ` set xs then length xs else Suc (length xs))"
by(induct xs) simp_all

lemma length_distinct: 
  "distinct (map fst xs) \<Longrightarrow> length (delete k xs) = (if k \<in> fst ` set xs then length xs - 1 else length xs)"
by(induct xs)(auto split: split_if_asm simp add: in_set_conv_nth)

end