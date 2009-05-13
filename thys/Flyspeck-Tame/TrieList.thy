(*  ID:         $Id: TrieList.thy,v 1.2 2009-05-13 06:13:17 fhaftmann Exp $
    Author:     Tobias Nipkow
*)

header "Trie (List Version)"

theory TrieList
imports Main
begin

(* FIXME move alist to List *)

subsection {* Association lists *}

consts
 assoc :: "('key * 'val)list \<Rightarrow> 'key \<Rightarrow> 'val option"
 rem_alist :: "'key \<Rightarrow> ('key * 'val)list \<Rightarrow>  ('key * 'val)list"
 upd_alist :: "'key \<Rightarrow> 'val \<Rightarrow> ('key * 'val)list \<Rightarrow>  ('key * 'val)list"

primrec
"assoc [] x = None"
"assoc (p#ps) x = (let (a,b) = p in if a=x then Some b else assoc ps x)";
primrec
"rem_alist k [] = []"
"rem_alist k (p#ps) = (if fst p = k then ps else p # rem_alist k ps)"
primrec
"upd_alist k v [] = [(k,v)]"
"upd_alist k v (p#ps) = (if fst p = k then (k,v)#ps else p # upd_alist k v ps)"

lemma assoc_conv: "assoc al x = map_of al x"
by(induct al, auto)

lemma map_of_upd_alist: "map_of(upd_alist k v al) = (map_of al)(k \<mapsto> v)"
apply(induct al)
 apply simp
apply(rule ext)
apply auto
done

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

consts "values" :: "('a,'v)trie \<Rightarrow> 'v list"
       alist :: "('a,'v)trie \<Rightarrow> ('a * ('a,'v)trie)list"
primrec "values(Trie vs al) = vs"
primrec "alist(Trie vs al) = al"

consts
 lookup_trie :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v list"
 update_trie :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> ('a,'v)trie"
 insert_trie :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v      \<Rightarrow> ('a,'v)trie"

primrec
"lookup_trie t [] = values t"
"lookup_trie t (a#as) = (case assoc (alist t) a of
                      None \<Rightarrow> []
                    | Some at \<Rightarrow> lookup_trie at as)"
primrec
"update_trie t []     vs = Trie vs (alist t)"
"update_trie t (a#as) vs =
   (let tt = (case assoc (alist t) a of
                None \<Rightarrow> Trie [] [] | Some at \<Rightarrow> at)
    in Trie (values t) ((a,update_trie tt as vs) # rem_alist a (alist t)))"

primrec
"insert_trie t []     v = Trie (v # values t) (alist t)"
"insert_trie t (a#as) vs =
   (let tt = (case assoc (alist t) a of
                None \<Rightarrow> Trie [] [] | Some at \<Rightarrow> at)
    in Trie (values t) ((a,insert_trie tt as vs) # rem_alist a (alist t)))";


lemma lookup_empty[simp]: "lookup_trie (Trie [] []) as = []"
by(case_tac as, simp_all)

theorem lookup_update_trie: "!t v bs.
 lookup_trie (update_trie t as vs) bs = (if as=bs then vs else lookup_trie t bs)"
apply(induct as)
 apply clarsimp
 apply(case_tac bs)
  apply simp
 apply simp
apply clarsimp
apply(case_tac bs)
 apply (auto simp add:Let_def assoc_conv split:option.split)
done

theorem insert_trie_conv:
 "!!t. insert_trie t as v = update_trie t as (v#lookup_trie t as)"
apply(induct as)
apply (auto simp:Let_def assoc_conv split:option.split)
done

constdefs
 trie_of_list :: "('b \<Rightarrow> 'a list) \<Rightarrow> 'b list \<Rightarrow> ('a,'b)trie"
"trie_of_list key == foldl (%t v. insert_trie t (key v) v) (Trie [] [])"

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