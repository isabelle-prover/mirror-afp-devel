(*  Author:     Tobias Nipkow
*)

header "Trie (List Version)"

theory TrieList
imports Main
begin

subsection {* Association lists *}

primrec rem_alist :: "'key \<Rightarrow> ('key * 'val)list \<Rightarrow>  ('key * 'val)list" where
"rem_alist k [] = []" |
"rem_alist k (p#ps) = (if fst p = k then ps else p # rem_alist k ps)"

lemma rem_alist_id[simp]: "k \<notin> fst ` set al \<Longrightarrow> rem_alist k al = al"
by(induct al, auto)

lemma map_of_rem_distinct_alist: "distinct(map fst al) \<Longrightarrow>
  map_of(rem_alist k al) = (map_of al)(k := None)"
apply(induct al)
 apply simp
apply clarify
apply(rule ext)
apply auto
apply(erule ssubst)
apply simp
done

lemma map_of_rem_alist[simp]:
 "k' \<noteq> k \<Longrightarrow> map_of (rem_alist k al) k' = map_of al k'"
by(induct al, auto)


subsection {* Trie *}

datatype ('a,'v)trie = Trie  "'v list"  "('a * ('a,'v)trie)list"

primrec "values" :: "('a,'v)trie \<Rightarrow> 'v list" where
  "values(Trie vs al) = vs"

primrec alist :: "('a,'v)trie \<Rightarrow> ('a * ('a,'v)trie)list" where
  "alist(Trie vs al) = al"

primrec lookup_trie :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v list" where
"lookup_trie t [] = values t" |
"lookup_trie t (a#as) = (case map_of (alist t) a of
                      None \<Rightarrow> []
                    | Some at \<Rightarrow> lookup_trie at as)"

primrec update_trie :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> ('a,'v)trie" where
"update_trie t []     vs = Trie vs (alist t)" |
"update_trie t (a#as) vs =
   (let tt = (case map_of (alist t) a of
                None \<Rightarrow> Trie [] [] | Some at \<Rightarrow> at)
    in Trie (values t) ((a,update_trie tt as vs) # rem_alist a (alist t)))"

primrec insert_trie :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v      \<Rightarrow> ('a,'v)trie" where
"insert_trie t []     v = Trie (v # values t) (alist t)" |
"insert_trie t (a#as) vs =
   (let tt = (case map_of (alist t) a of
                None \<Rightarrow> Trie [] [] | Some at \<Rightarrow> at)
    in Trie (values t) ((a,insert_trie tt as vs) # rem_alist a (alist t)))"


lemma lookup_empty[simp]: "lookup_trie (Trie [] []) as = []"
by(case_tac as, simp_all)

theorem lookup_update_trie:
 "lookup_trie (update_trie t as vs) bs = (if as=bs then vs else lookup_trie t bs)"
apply(induct as arbitrary: t v bs)
 apply clarsimp
 apply(case_tac bs)
  apply simp
 apply simp
apply clarsimp
apply(case_tac bs)
 apply (auto simp add:Let_def split:option.split)
done

theorem insert_trie_conv:
 "insert_trie t as v = update_trie t as (v#lookup_trie t as)"
apply(induct as arbitrary: t)
apply (auto simp:Let_def split:option.split)
done

definition trie_of_list :: "('b \<Rightarrow> 'a list) \<Rightarrow> 'b list \<Rightarrow> ('a,'b)trie" where
"trie_of_list key = foldl (%t v. insert_trie t (key v) v) (Trie [] [])"

lemma in_set_lookup_trie_of_list:
 "v \<in> set(lookup_trie (trie_of_list key vs) (key v)) = (v \<in> set vs)"
proof -
  have "!!t.
 v \<in> set(lookup_trie (foldl (%t v. insert_trie t (key v) v) t vs) (key v)) =
 (v \<in> set vs \<union> set(lookup_trie t (key v)))"
    apply(induct vs)
     apply (simp add:trie_of_list_def)
    apply (simp add:trie_of_list_def)
    apply(simp add:insert_trie_conv lookup_update_trie)
    apply blast
    done
  thus ?thesis by(simp add:trie_of_list_def)
qed

lemma in_set_lookup_trie_of_listD:
assumes "v \<in> set(lookup_trie (trie_of_list f vs) xs)" shows "v \<in> set vs"
proof -
  have "!!t.
  v \<in> set(lookup_trie (foldl (%t v. insert_trie t (f v) v) t vs) xs) \<Longrightarrow>
  v \<in> set vs \<union> set(lookup_trie t xs)"
    apply(induct vs)
     apply (simp add:trie_of_list_def)
    apply (simp add:trie_of_list_def)
    apply(force simp:insert_trie_conv lookup_update_trie split:split_if_asm)
    done
  thus ?thesis using prems by(force simp add:trie_of_list_def)
qed

end