header {* \isaheader{The type of associative lists} *}
theory Assoc_List imports "~~/src/HOL/Library/AList_Impl" begin

subsection {* Additional operations for associative lists *}

fun iteratei_aux :: "('s \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 's \<Rightarrow> 's"
where
  "iteratei_aux c f [] \<sigma> = \<sigma>"
| "iteratei_aux c f ((k, v) # l) \<sigma> = 
    (if c \<sigma> then iteratei_aux c f l (f k v \<sigma>) else \<sigma>)"

primrec update_with_aux :: "'val \<Rightarrow> 'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "update_with_aux v k f [] = [(k, f v)]"
| "update_with_aux v k f (p # ps) = (if (fst p = k) then (k, f (snd p)) # ps else p # update_with_aux v k f ps)"

text {*
  Do not use @{term "AList_Impl.delete"} because this traverses all the list even if it has found the key.
  We do not have to keep going because we use the invariant that keys are distinct.
*}
fun delete_aux :: "'key \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "delete_aux k [] = []"
| "delete_aux k ((k', v) # xs) = (if k = k' then xs else (k', v) # delete_aux k xs)"

lemma iteratei_aux_correct:
  assumes "distinct (map fst m)"
  and "I (dom (map_of m)) \<sigma>0"
  and "\<And>k v it \<sigma>. \<lbrakk>c \<sigma>; k \<in> it; map_of m k = Some v; it \<subseteq> dom (map_of m); I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  shows "I {} (iteratei_aux c f m \<sigma>0) \<or>
         (\<exists>it\<subseteq>dom (map_of m). it \<noteq> {} \<and> \<not> c (iteratei_aux c f m \<sigma>0) \<and> I it (iteratei_aux c f m \<sigma>0))"
using assms
proof(induct m arbitrary: \<sigma>0)
  case Nil thus ?case by simp
next
  case (Cons p m)
  obtain k v where PFMT[simp]: "p = (k,v)" by (cases p) auto
  from Cons.prems(2) have I': "I (insert k (dom (map_of m))) \<sigma>0" 
    by(simp del: map_of.simps add: dom_map_of_conv_image_fst)
  show ?case
  proof(cases "c \<sigma>0")
    case True[simp]
    have "iteratei_aux c f (p # m) \<sigma>0 = iteratei_aux c f m (f k v \<sigma>0)"
      by simp

    from Cons.prems(1) have INVN: "distinct (map fst m)" by simp
    from Cons.prems(1) have KNID: "k \<notin> dom (map_of m)"
      by(simp add: dom_map_of_conv_image_fst)

    have "I (insert k (dom (Map.map_of m)) - {k}) (f k v \<sigma>0)"
      by (rule Cons.prems(3)[OF _ _ _ _ I', of k v]) auto
    with KNID have IN: "I (dom (Map.map_of m)) (f k v \<sigma>0)" by auto

    have "I {} (iteratei_aux c f m (f k v \<sigma>0)) \<or> 
          (\<exists>it. it \<subseteq> dom (map_of m) \<and> it \<noteq> {} \<and> \<not> c (iteratei_aux c f m (f k v \<sigma>0)) \<and> I it (iteratei_aux c f m (f k v \<sigma>0)))" 
      (is "?terminate \<or> ?interrupt")
      using INVN IN KNID
      by - (erule (1) Cons, rule Cons.prems(3), auto)
    thus ?thesis
    proof
      assume "?terminate" thus ?thesis by simp
    next
      assume "?interrupt"
      then obtain it where "it\<subseteq>dom (map_of m)" "it \<noteq> {}" 
        and "\<not> c (iteratei_aux c f m (f k v \<sigma>0))" 
        and "I it (iteratei_aux c f m (f k v \<sigma>0))" by blast
      hence "it \<subseteq> dom (map_of (p # m))" "it \<noteq> {}"
        and "\<not> c (iteratei_aux c f (p # m) \<sigma>0)" 
        and "I it (iteratei_aux c f (p # m) \<sigma>0)" by auto
      thus ?thesis by blast
    qed
  next
    case False[simp]
    have IF: "iteratei_aux c f (p # m) \<sigma>0 = \<sigma>0" by simp
    from Cons(3) show ?thesis
      by(simp del: fun_upd_apply add: exI[where x="dom (map_of (p # m))"])
  qed
qed

lemma iteratei_aux_interrupt:
  "\<not> c \<sigma> \<Longrightarrow> Assoc_List.iteratei_aux c f xs \<sigma> = \<sigma>"
by(cases xs) auto

lemma iteratei_cong [fundef_cong]:
  assumes "kvs = kvs'" "\<sigma> = \<sigma>'" "c = c'"
  and ff': "\<And>\<sigma> k v. \<lbrakk> (k, v) \<in> set kvs'; c' \<sigma> \<rbrakk> \<Longrightarrow> f k v \<sigma> = f' k v \<sigma>"
  shows "iteratei_aux c f kvs \<sigma> = iteratei_aux c' f' kvs' \<sigma>'"
unfolding assms using ff'
by(induct kvs' arbitrary: \<sigma>') auto

lemma map_of_update_with_aux':
  "map_of (update_with_aux v k f ps) k' = ((map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))) k'"
by(induct ps) auto

lemma map_of_update_with_aux:
  "map_of (update_with_aux v k f ps) = (map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))"
by(simp add: fun_eq_iff map_of_update_with_aux')

lemma dom_update_with_aux: "fst ` set (update_with_aux v k f ps) = {k} \<union> fst ` set ps"
  by (induct ps) auto

lemma distinct_update_with_aux [simp]:
  "distinct (map fst (update_with_aux v k f ps)) = distinct (map fst ps)"
by(induct ps)(auto simp add: dom_update_with_aux)

lemma set_update_with_aux:
  "distinct (map fst xs) 
  \<Longrightarrow> set (update_with_aux v k f xs) = (set xs - {k} \<times> UNIV \<union> {(k, f (case map_of xs k of None \<Rightarrow> v | Some v \<Rightarrow> v))})"
by(induct xs)(auto intro: rev_image_eqI)

lemma set_delete_aux: "distinct (map fst xs) \<Longrightarrow> set (delete_aux k xs) = set xs - {k} \<times> UNIV"
apply(induct xs)
apply simp_all
apply clarsimp
apply(fastforce intro: rev_image_eqI)
done

lemma dom_delete_aux: "distinct (map fst ps) \<Longrightarrow> fst ` set (delete_aux k ps) = fst ` set ps - {k}"
by(auto simp add: set_delete_aux)

lemma distinct_delete_aux [simp]:
  "distinct (map fst ps) \<Longrightarrow> distinct (map fst (delete_aux k ps))"
proof(induct ps)
  case Nil thus ?case by simp
next
  case (Cons a ps)
  obtain k' v where a: "a = (k', v)" by(cases a)
  show ?case
  proof(cases "k' = k")
    case True with Cons a show ?thesis by simp
  next
    case False
    with Cons a have "k' \<notin> fst ` set ps" "distinct (map fst ps)" by simp_all
    with False a have "k' \<notin> fst ` set (delete_aux k ps)"
      by(auto dest!: dom_delete_aux[where k=k])
    with Cons a show ?thesis by simp
  qed
qed


lemma map_of_delete_aux':
  "distinct (map fst xs) \<Longrightarrow> map_of (delete_aux k xs) = (map_of xs)(k := None)"
by(induct xs)(fastforce intro: ext simp add: map_of_eq_None_iff fun_upd_twist)+

lemma map_of_delete_aux:
  "distinct (map fst xs) \<Longrightarrow> map_of (delete_aux k xs) k' = ((map_of xs)(k := None)) k'"
by(simp add: map_of_delete_aux')

lemma delete_aux_eq_Nil_conv: "delete_aux k ts = [] \<longleftrightarrow> ts = [] \<or> (\<exists>v. ts = [(k, v)])"
by(cases ts)(auto split: split_if_asm)

subsection {* Type @{text "('a, 'b) assoc_list" } *}

typedef (open) ('k, 'v) assoc_list = "{xs :: ('k \<times> 'v) list. distinct (map fst xs)}"
morphisms impl_of Assoc_List
by(rule exI[where x="[]"]) simp

lemma assoc_list_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
by(simp add: impl_of_inject)

lemma expand_assoc_list_eq: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
by(simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of al))"
using impl_of[of al] by simp

lemma Assoc_List_impl_of [code abstype]: "Assoc_List (impl_of al) = al"
by(rule impl_of_inverse)

subsection {* Primitive operations *}

definition empty :: "('k, 'v) assoc_list"
where [code del]: "empty = Assoc_List []"

definition lookup :: "('k, 'v) assoc_list \<Rightarrow> 'k \<Rightarrow> 'v option"
where [code]: "lookup al = map_of (impl_of al)" 

definition update_with :: "'v \<Rightarrow> 'k \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) assoc_list \<Rightarrow> ('k, 'v) assoc_list"
where [code del]: "update_with v k f al = Assoc_List (update_with_aux v k f (impl_of al))"

definition delete :: "'k \<Rightarrow> ('k, 'v) assoc_list \<Rightarrow> ('k, 'v) assoc_list"
where [code del]: "delete k al = Assoc_List (delete_aux k (impl_of al))"

definition iteratei :: "('s \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('k, 'v) assoc_list \<Rightarrow> 's \<Rightarrow> 's" 
where [code]: "iteratei c f al = iteratei_aux c f (impl_of al)"

lemma impl_of_empty [code abstract]: "impl_of empty = []"
by(simp add: empty_def Assoc_List_inverse)

lemma impl_of_update_with [code abstract]:
  "impl_of (update_with v k f al) = update_with_aux v k f (impl_of al)"
by(simp add: update_with_def Assoc_List_inverse)

lemma impl_of_delete [code abstract]:
  "impl_of (delete k al) = delete_aux k (impl_of al)"
by(simp add: delete_def Assoc_List_inverse)

subsection {* Abstract operation properties *}

lemma lookup_empty [simp]: "lookup empty k = None"
by(simp add: empty_def lookup_def Assoc_List_inverse)

lemma lookup_empty': "lookup empty = Map.empty"
by(rule ext) simp

lemma lookup_update_with [simp]: 
  "lookup (update_with v k f al) = (lookup al)(k \<mapsto> case lookup al k of None \<Rightarrow> f v | Some v \<Rightarrow> f v)"
by(simp add: lookup_def update_with_def Assoc_List_inverse map_of_update_with_aux)

lemma lookup_delete [simp]: "lookup (delete k al) = (lookup al)(k := None)"
by(simp add: lookup_def delete_def Assoc_List_inverse distinct_delete map_of_delete_aux')

lemma finite_dom_lookup [simp, intro!]: "finite (dom (lookup m))"
by(simp add: lookup_def finite_dom_map_of)

lemma iteratei_correct:
  assumes "I (dom (lookup m)) \<sigma>0"
  and "\<And>k v it \<sigma>. \<lbrakk>c \<sigma>; k \<in> it; lookup m k = Some v; it \<subseteq> dom (lookup m); I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  shows "I {} (iteratei c f m \<sigma>0) \<or>
         (\<exists>it\<subseteq>dom (lookup m). it \<noteq> {} \<and> \<not> c (iteratei c f m \<sigma>0) \<and> I it (iteratei c f m \<sigma>0))"
using impl_of_distinct assms
unfolding iteratei_def lookup_def
by(rule iteratei_aux_correct)

subsection {* Derived operations *}

definition update :: "'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) assoc_list \<Rightarrow> ('key, 'val) assoc_list"
where "update k v = update_with v k (\<lambda>_. v)"

definition set :: "('key, 'val) assoc_list \<Rightarrow> ('key \<times> 'val) set"
where "set al = List.set (impl_of al)"


lemma lookup_update [simp]: "lookup (update k v al) = (lookup al)(k \<mapsto> v)"
by(simp add: update_def split: option.split)

lemma set_empty [simp]: "set empty = {}"
by(simp add: set_def empty_def Assoc_List_inverse)

lemma set_update_with:
  "set (update_with v k f al) = 
  (set al - {k} \<times> UNIV \<union> {(k, f (case lookup al k of None \<Rightarrow> v | Some v \<Rightarrow> v))})"
by(simp add: set_def update_with_def Assoc_List_inverse set_update_with_aux lookup_def)

lemma set_update: "set (update k v al) = (set al - {k} \<times> UNIV \<union> {(k, v)})"
by(simp add: update_def set_update_with)

lemma set_delete: "set (delete k al) = set al - {k} \<times> UNIV"
by(simp add: set_def delete_def Assoc_List_inverse set_delete_aux)

subsection {* Type classes *}

instantiation assoc_list :: (equal, equal) equal begin

definition "equal_class.equal (al :: ('a, 'b) assoc_list) al' == impl_of al = impl_of al'"

instance
proof
qed (simp add: equal_assoc_list_def impl_of_inject)

end

instantiation assoc_list :: (type, type) size begin

definition "size (al :: ('a, 'b) assoc_list) = length (impl_of al)"

instance ..
end

hide_const (open) impl_of empty lookup update_with set update delete iteratei iteratei_aux



end
