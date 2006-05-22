(*  Title:      Trie
    ID:         $Id: Trie.thy,v 1.1 2006-05-22 09:54:04 nipkow Exp $
    Author:     Tobias Nipkow
*)

theory Trie
imports Main
begin

subsubsection {* Association lists *}

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


datatype ('a,'v)trie = Trie  "'v option"  "('a * ('a,'v)trie)list"

consts "value" :: "('a,'v)trie \<Rightarrow> 'v option"
       alist :: "('a,'v)trie \<Rightarrow> ('a * ('a,'v)trie)list"
primrec "value(Trie ov al) = ov"
primrec "alist(Trie ov al) = al"

consts
 lookup :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v option"
 update :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a,'v)trie"

primrec
"lookup t [] = value t"
"lookup t (a#as) = (case assoc (alist t) a of
                      None \<Rightarrow> None
                    | Some at \<Rightarrow> lookup at as)"
primrec
"update t []     v = Trie (Some v) (alist t)"
"update t (a#as) v =
   (let tt = (case assoc (alist t) a of
                None \<Rightarrow> Trie None [] | Some at \<Rightarrow> at)
    in Trie (value t) ((a,update tt as v) # rem_alist a (alist t)))";

lemma lookup_empty[simp]: "lookup (Trie None []) as = None"
by(case_tac as, simp_all)

theorem "\<And>t v bs.
 lookup (update t as v) bs = (if as=bs then Some v else lookup t bs)"
apply(induct as)
 apply simp
apply(case_tac[!] bs, auto simp:Let_def assoc_conv split:option.split)
done

consts dummy :: "'a \<Rightarrow> 'a"
consts_code dummy ("(writeln(string'_of'_int(_));0)")

end