(*  Author: Tobias Nipkow  *)

header "Tries (List Version)"

theory Tries
imports Maps
begin

subsection {* Association lists *}

primrec rem_alist :: "'key \<Rightarrow> ('key * 'val)list \<Rightarrow>  ('key * 'val)list" where
"rem_alist k [] = []" |
"rem_alist k (p#ps) = (if fst p = k then ps else p # rem_alist k ps)"

lemma rem_alist_id[simp]: "k \<notin> fst ` set al \<Longrightarrow> rem_alist k al = al"
by(induct al, auto)

lemma set_rem_alist:
  "distinct(map fst al) \<Longrightarrow> set (rem_alist a al) =
   (set al) - {(a,the(map_of al a))}"
apply(induct al)
 apply simp
apply simp
apply fastforce
done

lemma fst_set_rem_alist[simp]:
  "distinct(map fst al) \<Longrightarrow> fst ` set (rem_alist a al) = fst ` (set al) - {a}"
apply(induct al)
 apply simp
apply simp
apply blast
done
(*
lemma fst_set_rem_alist[simp]:
  "set (rem_alist a al) = (set al) - {(a,map_of al a)}"
apply(induct al)
 apply simp
apply simp
apply blast
done
*)
lemma distinct_map_fst_rem_alist[simp]:
  "distinct (map fst al) \<Longrightarrow> distinct (map fst (rem_alist a al))"
by(induct al) simp_all

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


subsection {* Tries *}

datatype ('a,'v)tries = Tries  "'v list"  "('a * ('a,'v)tries)list"

primrec "values" :: "('a,'v)tries \<Rightarrow> 'v list" where
  "values(Tries vs al) = vs"

primrec alist :: "('a,'v)tries \<Rightarrow> ('a * ('a,'v)tries)list" where
  "alist(Tries vs al) = al"

fun inv :: "('a,'v)tries \<Rightarrow> bool" where
"inv(Tries _ al) = (distinct(map fst al) & (\<forall>(a,t) \<in> set al. inv t))"

primrec lookup :: "('a,'v)tries \<Rightarrow> 'a list \<Rightarrow> 'v list" where
"lookup t [] = values t" |
"lookup t (a#as) = (case map_of (alist t) a of
                      None \<Rightarrow> []
                    | Some at \<Rightarrow> lookup at as)"

primrec update :: "('a,'v)tries \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> ('a,'v)tries" where
"update t []     vs = Tries vs (alist t)" |
"update t (a#as) vs =
   (let tt = (case map_of (alist t) a of
                None \<Rightarrow> Tries [] [] | Some at \<Rightarrow> at)
    in Tries (values t) ((a,update tt as vs) # rem_alist a (alist t)))"

primrec insert :: "('a,'v)tries \<Rightarrow> 'a list \<Rightarrow> 'v      \<Rightarrow> ('a,'v)tries" where
"insert t []     v = Tries (v # values t) (alist t)" |
"insert t (a#as) vs =
   (let tt = (case map_of (alist t) a of
                None \<Rightarrow> Tries [] [] | Some at \<Rightarrow> at)
    in Tries (values t) ((a,insert tt as vs) # rem_alist a (alist t)))"


lemma lookup_empty[simp]: "lookup (Tries [] []) as = []"
by(case_tac as, simp_all)

theorem lookup_update:
 "lookup (update t as vs) bs =
 (if as=bs then vs else lookup t bs)"
apply(induct as arbitrary: t v bs)
 apply clarsimp
 apply(case_tac bs)
  apply simp
 apply simp
apply clarsimp
apply(case_tac bs)
 apply (auto simp add:Let_def split:option.split)
done

theorem insert_conv:
 "insert t as v = update t as (v#lookup t as)"
apply(induct as arbitrary: t)
apply (auto simp:Let_def split:option.split)
done

lemma inv_insert: "inv t \<Longrightarrow> inv(insert t as v)"
apply(induct as arbitrary: t)
apply(case_tac t)
apply simp
apply(case_tac t)
apply simp
apply (auto simp:set_rem_alist split: option.split)
done

lemma inv_update: "inv t \<Longrightarrow> inv(update t as v)"
apply(induct as arbitrary: t)
apply(case_tac t)
apply simp
apply(case_tac t)
apply simp
apply (auto simp:set_rem_alist split: option.split)
done

definition trie_of_list :: "('b \<Rightarrow> 'a list) \<Rightarrow> 'b list \<Rightarrow> ('a,'b)tries" where
"trie_of_list key = foldl (%t v. insert t (key v) v) (Tries [] [])"

lemma inv_foldl_insert:
  "inv t \<Longrightarrow> inv (foldl (%t v. insert t (key v) v) t xs)"
apply(induct xs arbitrary: t)
apply(auto simp: inv_insert)
done

lemma inv_of_list: "inv (trie_of_list k xs)"
unfolding trie_of_list_def
apply(rule inv_foldl_insert)
apply simp
done

lemma in_set_lookup_of_list:
 "v \<in> set(lookup (trie_of_list key vs) (key v)) = (v \<in> set vs)"
proof -
  have "!!t.
 v \<in> set(lookup (foldl (%t v. insert t (key v) v) t vs) (key v)) =
 (v \<in> set vs \<union> set(lookup t (key v)))"
    apply(induct vs)
     apply (simp add:trie_of_list_def)
    apply (simp add:trie_of_list_def)
    apply(simp add:insert_conv lookup_update)
    apply blast
    done
  thus ?thesis by(simp add:trie_of_list_def)
qed

lemma in_set_lookup_of_listD:
assumes "v \<in> set(lookup (trie_of_list f vs) xs)" shows "v \<in> set vs"
proof -
  have "!!t.
  v \<in> set(lookup (foldl (%t v. insert t (f v) v) t vs) xs) \<Longrightarrow>
  v \<in> set vs \<union> set(lookup t xs)"
    apply(induct vs)
     apply (simp add:trie_of_list_def)
    apply (simp add:trie_of_list_def)
    apply(force simp:insert_conv lookup_update split:split_if_asm)
    done
  thus ?thesis using assms by(force simp add:trie_of_list_def)
qed

definition set_of :: "('a,'b)tries \<Rightarrow> 'b set" where
"set_of t = Union {gs. \<exists>a. gs = set(lookup t a)}"

lemma set_of_empty[simp]: "set_of (Tries [] []) = {}"
by(simp add: set_of_def)

lemma set_of_insert[simp]:
  "set_of (insert t a x) = Set.insert x (set_of t)"
by(auto simp: set_of_def insert_conv lookup_update)

lemma set_of_foldl_insert:
  "set_of (foldl (%t v. insert t (key v) v) t xs) =
   set xs Un set_of t"
by(induct xs arbitrary: t) auto

lemma set_of_of_list[simp]:
  "set_of(trie_of_list key xs) = set xs"
by(simp add: trie_of_list_def set_of_foldl_insert)

lemma in_set_lookup_set_ofD:
  "x\<in>set (lookup t a) \<Longrightarrow> x \<in> set_of t"
by(auto simp: set_of_def)

fun all :: "('v \<Rightarrow> bool) \<Rightarrow> ('a,'v)tries \<Rightarrow> bool" where
"all P (Tries vs al) =
 ((\<forall>v \<in> set vs. P v) \<and> (\<forall>(a,t) \<in> set al. all P t))"

interpretation map:
  maps "Tries [] []" update lookup inv
proof
  case goal1 show ?case by(rule ext) simp
next
  case goal2 show ?case by(rule ext) (simp add:lookup_update)
next
  case goal3 show ?case by(simp)
next
  case goal4 thus ?case by(simp add:inv_update)
qed

lemma set_of_conv: "set_of = maps.set_of lookup"
by(rule ext) (auto simp add: set_of_def map.set_of_def)

hide_const (open) inv lookup update insert set_of all

end