(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Implementation of a trie with explicit invariants} *}
theory Trie_Impl imports
  "common/Assoc_List"
begin

subsection {* Type definition and primitive operations *}

datatype ('key, 'val) trie = Trie "'val option" "('key \<times> ('key, 'val) trie) list"

lemma trie_induct [case_names Trie, induct type]:
  "(\<And>vo kvs. (\<And>k t. (k, t) \<in> set kvs \<Longrightarrow> P t) \<Longrightarrow> P (Trie vo kvs)) \<Longrightarrow> P t"
apply(induction_schema)
  apply pat_completeness
 apply(lexicographic_order)
done

definition empty :: "('key, 'val) trie"
where "empty = Trie None []"

fun lookup :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> 'val option"
where
  "lookup (Trie vo _) [] = vo"
| "lookup (Trie _ ts) (k#ks) = (case map_of ts k of None \<Rightarrow> None | Some t \<Rightarrow> lookup t ks)"

fun update :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> 'val \<Rightarrow> ('key, 'val) trie"
where
  "update (Trie vo ts) [] v = Trie (Some v) ts"
| "update (Trie vo ts) (k#ks) v = Trie vo (Assoc_List.update_with_aux (Trie None []) k (\<lambda>t. update t ks v) ts)"

primrec isEmpty :: "('key, 'val) trie \<Rightarrow> bool"
where "isEmpty (Trie vo ts) \<longleftrightarrow> vo = None \<and> ts = []"

fun delete :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> ('key, 'val) trie"
where
  "delete (Trie vo ts) [] = Trie None ts"
| "delete (Trie vo ts) (k#ks) =
   (case map_of ts k of None \<Rightarrow> Trie vo ts
                    | Some t \<Rightarrow> let t' = delete t ks 
                                in if isEmpty t'
                                   then Trie vo (Assoc_List.delete_aux k ts)
                                   else Trie vo (AList.update k t' ts))"

fun trie_invar :: "('key, 'val) trie \<Rightarrow> bool"
where "trie_invar (Trie vo kts) = (distinct (map fst kts) \<and> (\<forall>(k, t) \<in> set kts. \<not> isEmpty t \<and> trie_invar t))"

fun iteratei_postfixed :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('key list \<Rightarrow> 'val \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('key, 'val) trie \<Rightarrow> '\<sigma> \<Rightarrow> 'key list \<Rightarrow> '\<sigma>"
where
  "iteratei_postfixed c f (Trie vo ts) \<sigma> ks =
   (if c \<sigma> 
    then Assoc_List.iteratei_aux c (\<lambda>k t \<sigma>. iteratei_postfixed c f t \<sigma> (k # ks)) ts
                                 (case vo of None \<Rightarrow> \<sigma> | Some v \<Rightarrow> f ks v \<sigma>) 
    else \<sigma>)"

definition iteratei :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('key list \<Rightarrow> 'val \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('key, 'val) trie \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where
  "iteratei c f t \<sigma> = iteratei_postfixed c f t \<sigma> []"

subsection {* The empty trie *}

lemma trie_invar_empty [simp, intro!]: "trie_invar empty"
by(simp add: empty_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
proof
  fix ks show "lookup empty ks = Map.empty ks"
    by(cases ks)(auto simp add: empty_def)
qed

lemma lookup_empty' [simp]:
  "lookup (Trie None []) ks = None"
by(simp add: lookup_empty[unfolded empty_def])

subsection {* Emptyness check *}

lemma isEmpty_conv:
  "isEmpty ts \<longleftrightarrow> ts = Trie None []"
by(cases ts)(simp)

lemma update_not_empty: "\<not> isEmpty (update t ks v)"
apply(cases t)
apply(rename_tac kvs)
apply(cases ks)
apply(case_tac [2] kvs)
apply auto
done

lemma isEmpty_lookup_empty:
  "trie_invar t \<Longrightarrow> isEmpty t \<longleftrightarrow> lookup t = Map.empty"
proof(induct t)
  case (Trie vo kvs)
  thus ?case
    apply(cases kvs)
    apply(auto simp add: fun_eq_iff elim: allE[where x="[]"])
    apply(erule meta_allE)+
    apply(erule meta_impE)
    apply(rule disjI1)
    apply(fastforce intro: exI[where x="a # b", standard])+
    done
qed

subsection {* Trie update *}

lemma lookup_update:
  "lookup (update t ks v) ks' = (if ks = ks' then Some v else lookup t ks')"
proof(induct t ks v arbitrary: ks' rule: update.induct)
  case (1 vo ts v)
  show ?case by(fastforce simp add: neq_Nil_conv dest: not_sym)
next
  case (2 vo ts k ks v)
  note IH = `\<And>t ks'. lookup (update t ks v) ks' = (if ks = ks' then Some v else lookup t ks')`
  show ?case by(cases ks')(auto simp add: map_of_update_with_aux IH split: option.split)
qed

lemma lookup_update':
  "lookup (update t ks v) = (lookup t)(ks \<mapsto> v)"
by(rule ext)(simp add: lookup_update)


lemma trie_invar_update: "trie_invar t \<Longrightarrow> trie_invar (update t ks v)"
by(induct t ks v rule: update.induct)(auto simp add: set_update_with_aux update_not_empty split: option.splits)
 
subsection {* Trie removal *}

lemma delete_eq_empty_lookup_other_fail:
  "\<lbrakk> delete t ks = Trie None []; ks' \<noteq> ks \<rbrakk> \<Longrightarrow> lookup t ks' = None"
proof(induct t ks arbitrary: ks' rule: delete.induct)
  case (1 vo ts)
  thus ?case by(auto simp add: neq_Nil_conv)
next
  case (2 vo ts k ks)
  note IH = `\<And>t ks'. \<lbrakk>map_of ts k = Some t; delete t ks = Trie None []; ks' \<noteq> ks\<rbrakk>
           \<Longrightarrow> lookup t ks' = None`
  note ks' = `ks' \<noteq> k # ks`
  note empty = `delete (Trie vo ts) (k # ks) = Trie None []`
  show ?case
  proof(cases "map_of ts k")
    case (Some t)
    from Some empty show ?thesis
    proof(cases ks')
      case (Cons k' ks'')
      with Some empty ks' show ?thesis
      proof(cases "k' = k")
        case False
        from Some Cons empty have "delete_aux k ts = []"
          by(clarsimp simp add: Let_def split: split_if_asm)
        with False have "map_of ts k' = None"
          by(cases "map_of ts k'")(auto dest: map_of_is_SomeD simp add: delete_aux_eq_Nil_conv)
        thus ?thesis using False Some Cons empty by simp
      next
        case True
        with Some empty ks' Cons show ?thesis
          by(clarsimp simp add: IH Let_def isEmpty_conv split: split_if_asm)
      qed
    qed(simp add: Let_def split: split_if_asm)
  next
    case None thus ?thesis using empty by simp
  qed
qed

lemma lookup_delete:
  "trie_invar t \<Longrightarrow> lookup (delete t ks) ks' = (if ks = ks' then None else lookup t ks')"
proof(induct t ks arbitrary: ks' rule: delete.induct)
  case (1 vo ts)
  show ?case by(fastforce dest: not_sym simp add: neq_Nil_conv)
next
  case (2 vo ts k ks)
  note IH = `\<And>t ks'. \<lbrakk> map_of ts k = Some t; trie_invar t \<rbrakk>
           \<Longrightarrow> lookup (delete t ks) ks' = (if ks = ks' then None else lookup t ks')`
  note invar = `trie_invar (Trie vo ts)`
  show ?case
  proof(cases ks')
    case Nil thus ?thesis
      by(simp split: option.split add: Let_def)
  next
    case (Cons k' ks'')[simp]
    show ?thesis
    proof(cases "k' = k")
      case False thus ?thesis using invar
        by(auto simp add: Let_def update_conv' map_of_delete_aux split: option.split)
    next
      case True[simp]
      show ?thesis
      proof(cases "map_of ts k")
        case None thus ?thesis by simp
      next
        case (Some t)
        thus ?thesis 
        proof(cases "isEmpty (delete t ks)")
          case True
          with Some invar show ?thesis
            by(auto simp add: map_of_delete_aux isEmpty_conv dest: delete_eq_empty_lookup_other_fail)
        next
          case False
          thus ?thesis using Some IH[of t ks''] invar by(auto simp add: update_conv')
        qed
      qed
    qed
  qed
qed

lemma lookup_delete':
  "trie_invar t \<Longrightarrow> lookup (delete t ks) = (lookup t)(ks := None)"
by(rule ext)(simp add: lookup_delete)

lemma trie_invar_delete:
  "trie_invar t \<Longrightarrow> trie_invar (delete t ks)"
proof(induct t ks rule: delete.induct)
  case (1 vo ts)
  thus ?case by simp
next
  case (2 vo ts k ks)
  note invar = `trie_invar (Trie vo ts)`
  show ?case
  proof(cases "map_of ts k")
    case None
    thus ?thesis using invar by simp
  next
    case (Some t)
    with invar have "trie_invar t" by auto
    with Some have "trie_invar (delete t ks)" by(rule 2)
    from invar Some have distinct: "distinct (map fst ts)" "\<not> isEmpty t" by auto
    show ?thesis
    proof(cases "isEmpty (delete t ks)")
      case True
      { fix k' t'
        assume k't': "(k', t') \<in> set (delete_aux k ts)"
        with distinct have "map_of (delete_aux k ts) k' = Some t'" by simp
        hence "map_of ts k' = Some t'" using distinct
          by(auto simp del: map_of_eq_Some_iff simp add: map_of_delete_aux split: split_if_asm)
        with invar  have "\<not> isEmpty t' \<and> trie_invar t'" by auto }
      with invar have "trie_invar (Trie vo (delete_aux k ts))" by auto
      thus ?thesis using True Some by(simp)
    next
      case False
      { fix k' t'
        assume k't':"(k', t') \<in> set (AList.update k (delete t ks) ts)"
        hence "map_of (AList.update k (delete t ks) ts) k' = Some t'"
          using invar by(auto simp add: distinct_update)
        hence eq: "((map_of ts)(k \<mapsto> delete t ks)) k' = Some t'" unfolding update_conv .
        have "\<not> isEmpty t' \<and> trie_invar t'"
        proof(cases "k' = k")
          case True
          with eq have "t' = delete t ks" by simp
          with `trie_invar (delete t ks)` False
          show ?thesis by simp
        next
          case False
          with eq distinct have "(k', t') \<in> set ts" by simp
          with invar show ?thesis by auto
        qed }
      thus ?thesis using Some invar False by(auto simp add: distinct_update)
    qed
  qed
qed

subsection {* Domain of a trie *}

lemma dom_lookup: 
  "dom (lookup (Trie vo kts)) = 
  (\<Union>k\<in>dom (map_of kts). Cons k ` dom (lookup (the (map_of kts k)))) \<union>
  (if vo = None then {} else {[]})"
unfolding dom_def
apply(rule sym)
apply(safe)
  apply simp
 apply(clarsimp simp add: split_if_asm)
apply(case_tac x)
apply(auto split: option.split_asm)
done

lemma finite_dom_trie_lookup:
  "finite (dom (lookup t))"
proof(induct t)
  case (Trie vo kts)
  have "finite (\<Union>k\<in>dom (map_of kts). Cons k ` dom (lookup (the (map_of kts k))))"
  proof(rule finite_UN_I)
    show "finite (dom (map_of kts))" by(rule finite_dom_map_of)
  next
    fix k
    assume "k \<in> dom (map_of kts)"
    then obtain v where "(k, v) \<in> set kts" "map_of kts k = Some v" by(auto dest: map_of_SomeD)
    hence "finite (dom (lookup (the (map_of kts k))))" by simp(rule Trie)
    thus "finite (Cons k ` dom (lookup (the (map_of kts k))))" by(rule finite_imageI)
  qed
  thus ?case by(simp add: dom_lookup)
qed

lemma dom_lookup_empty_conv: "trie_invar t \<Longrightarrow> dom (lookup t) = {} \<longleftrightarrow> isEmpty t"
proof(induct t)
  case (Trie vo kvs)
  show ?case
  proof
    assume dom: "dom (lookup (Trie vo kvs)) = {}"
    have "vo = None"
    proof(cases vo)
      case (Some v)
      hence "[] \<in> dom (lookup (Trie vo kvs))" by auto
      with dom have False by simp
      thus ?thesis ..
    qed
    moreover have "kvs = []"
    proof(cases kvs)
      case (Cons kt kvs')
      with `trie_invar (Trie vo kvs)`
      have "\<not> isEmpty (snd kt)" "trie_invar (snd kt)" by auto
      from Cons have "(fst kt, snd kt) \<in> set kvs" by simp
      hence "dom (lookup (snd kt)) = {} \<longleftrightarrow> isEmpty (snd kt)"
        using `trie_invar (snd kt)` by(rule Trie)
      with `\<not> isEmpty (snd kt)` have "dom (lookup (snd kt)) \<noteq> {}" by simp
      with dom Cons have False by(auto simp add: dom_lookup)
      thus ?thesis ..
    qed
    ultimately show "isEmpty (Trie vo kvs)" by simp
  next
    assume "isEmpty (Trie vo kvs)"
    thus "dom (lookup (Trie vo kvs)) = {}"
      by(simp add: lookup_empty[unfolded empty_def])
  qed
qed

subsection {* Interuptible iterator *}

lemma iteratei_postfixed_induct[case_names iteratei_postfixed]:
  fixes c :: "'\<sigma> \<Rightarrow> bool" and f :: "'key list \<Rightarrow> 'val \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  and P :: "('key, 'val) trie \<Rightarrow> '\<sigma> \<Rightarrow> 'key list \<Rightarrow> bool"
  assumes IH: "\<And>vo ts \<sigma> ks. (\<And>\<sigma>' k v. \<lbrakk>c \<sigma>; (k, v) \<in> set ts; c \<sigma>'\<rbrakk> \<Longrightarrow> P v \<sigma>' (k # ks)) \<Longrightarrow> P (Trie vo ts) \<sigma> ks"
  shows "P t \<sigma> ks"
apply(rule iteratei_postfixed.induct[where P="\<lambda>c' f' t \<sigma> ks. c = c' \<longrightarrow> f = f' \<longrightarrow> P t \<sigma> ks", rule_format])
apply(rule IH)
apply blast+
done

lemma iteratei_postfixed_interrupt:
  "\<not> c \<sigma> \<Longrightarrow> iteratei_postfixed c f t \<sigma> ks = \<sigma>"
by(cases t) simp


lemma iteratei_postfixed_correct:
  fixes f :: "'key list \<Rightarrow> 'val \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  assumes invar: "trie_invar t"
  and I: "I ((\<lambda>ks. rev ks @ ks0) ` dom (lookup t)) \<sigma>0"
  and step: "\<And>ks v it \<sigma>. \<lbrakk> c \<sigma>; ks @ ks0 \<in> it; lookup t (rev ks) = Some v;
                           it \<subseteq> (\<lambda>ks. rev ks @ ks0) ` dom (lookup t); I it \<sigma> \<rbrakk>
             \<Longrightarrow> I (it - {ks @ ks0}) (f (ks @ ks0) v \<sigma>)"
  shows "I {} (iteratei_postfixed c f t \<sigma>0 ks0) \<or> 
        (\<exists>it. it \<subseteq> (\<lambda>ks. rev ks @ ks0) ` dom (lookup t) \<and> it \<noteq> {} \<and> \<not> (c (iteratei_postfixed c f t \<sigma>0 ks0)) \<and>
              I it (iteratei_postfixed c f t \<sigma>0 ks0))"
proof -
  def ipres \<equiv> "\<lambda>t d ks0.
               \<forall>\<sigma> ks v it. c \<sigma> \<longrightarrow> ks @ ks0 \<in> it \<longrightarrow> lookup t (rev ks) = Some v 
                           \<longrightarrow> it \<subseteq> d \<longrightarrow> I it \<sigma> \<longrightarrow> I (it - {ks @ ks0}) (f (ks @ ks0) v \<sigma>)"

  { fix \<sigma> it d
    assume "I it \<sigma>" "ipres t d ks0" "it \<subseteq> d"
      and "(\<lambda>ks. rev ks @ ks0) ` dom (lookup t) \<subseteq> it"
    with invar
    have "I (it - (\<lambda>ks. rev ks @ ks0) ` dom (lookup t)) (iteratei_postfixed c f t \<sigma> ks0) \<or>
         (\<exists>it' \<subseteq> d. it' \<noteq> {} \<and> \<not> c (iteratei_postfixed c f t \<sigma> ks0) \<and> I it' (iteratei_postfixed c f t \<sigma> ks0))"
    proof(induct t \<sigma> ks0 arbitrary: it d taking: c rule: iteratei_postfixed_induct)
      case (iteratei_postfixed vo ts \<sigma> ks0)
      have invar: "trie_invar (Trie vo ts)"
        and I: "I it \<sigma>"
        and it_subset: "it \<subseteq> d"
        and it_supset: "(\<lambda>ks. rev ks @ ks0) ` dom (lookup (Trie vo ts)) \<subseteq> it"
        and IH: "\<And>\<sigma>' k v it d. \<lbrakk> c \<sigma>; (k, v) \<in> set ts; c \<sigma>'; trie_invar v; I it \<sigma>'; ipres v d (k # ks0);
                                 it \<subseteq> d; (\<lambda>ks. rev ks @ k # ks0) ` dom (lookup v) \<subseteq> it\<rbrakk>
                 \<Longrightarrow> I (it - (\<lambda>ks. rev ks @ k # ks0) ` dom (lookup v)) (iteratei_postfixed c f v \<sigma>' (k # ks0)) \<or>
                    (\<exists>it' \<subseteq> d. it' \<noteq> {} \<and> \<not> c (iteratei_postfixed c f v \<sigma>' (k # ks0)) \<and>
                               I it' (iteratei_postfixed c f v \<sigma>' (k # ks0)))"
        by fact+
      note ipres = `ipres (Trie vo ts) d ks0`[unfolded ipres_def, rule_format]
      show ?case
      proof(cases "c \<sigma>")
        case False thus ?thesis
        proof(cases "it = {}")
          case True
          with it_supset have "dom (lookup (Trie vo ts)) = {}" by auto
          thus ?thesis using True `I it \<sigma>` False by(auto)
        next
          case False
          with `\<not> c \<sigma>` it_subset `I it \<sigma>` show ?thesis by auto
        qed
      next
        case True
        note c\<sigma> = this
        
        show ?thesis
        proof(cases "vo = None \<or> c (f ks0 (the vo) \<sigma>)")
          case False
          then obtain v where vo: "vo = Some v" "\<not> c (f ks0 v \<sigma>)" by auto
          hence "ks0 \<in> it" using it_supset by(simp add: dom_lookup)
          show ?thesis
          proof(cases "dom (lookup (Trie vo ts)) = {[]}")
            case True
            thus ?thesis using `c \<sigma>` vo `ks0 \<in> it` `it \<subseteq> d` `I it \<sigma>`
              by(auto simp add: iteratei_aux_interrupt intro: ipres[where ks="[]", unfolded vo, simplified])
          next
            case False
            hence "it - {ks0} \<noteq> {}" using it_supset vo by auto
            moreover have "it - {ks0} \<subseteq> d" using `it \<subseteq> d` by auto
            ultimately show ?thesis using vo True `ks0 \<in> it` `it \<subseteq> d` `I it \<sigma>`
              by(auto simp add: iteratei_aux_interrupt intro: ipres[where ks="[]", unfolded vo, simplified])
          qed
        next
          case True
          def \<sigma> == "case vo of None \<Rightarrow> \<sigma> | Some v \<Rightarrow> f ks0 v \<sigma>"
          def it == "case vo of None \<Rightarrow> it | Some v \<Rightarrow> it - {ks0}"
          obtain "c \<sigma>" "I it \<sigma>" "it \<subseteq> d"
            and it_supset: "(\<lambda>ks. rev ks @ ks0) ` dom (lookup (Trie None ts)) \<subseteq> it"
          proof(cases vo)
            case None[simp]
            from I c\<sigma> it_subset it_supset show ?thesis
              by(fastforce simp add: it_def \<sigma>_def intro!: that)
          next
            case (Some v)
            with True have "c \<sigma>" by(simp add: \<sigma>_def)
            moreover from Some True c\<sigma> it_supset it_subset I 
            have "I it \<sigma>" unfolding it_def \<sigma>_def
              by(auto intro: ipres[where ks="[]", unfolded Some, simplified] image_eqI[where x="[]"] simp add: dom_lookup)
            moreover from it_subset Some have "it \<subseteq> d" by(auto simp add: it_def)
            moreover from it_supset Some have "(\<lambda>ks. rev ks @ ks0) ` dom (lookup (Trie None ts)) \<subseteq> it"
              by(auto simp add: it_def dom_lookup intro!: domI rev_image_eqI)
            ultimately show thesis by(rule that)
          qed
          
          let ?f = "\<lambda>k t \<sigma>. iteratei_postfixed c f t \<sigma> (k # ks0)"
          let ?it'' = "\<lambda>it'. it - ((\<lambda>ks. rev ks @ ks0) ` (\<Union>k\<in>(dom (map_of ts) - it'). op # k ` dom (lookup (the (map_of ts k)))))"
          let ?I = "\<lambda>it' \<sigma>'. I it' \<sigma>' \<or> (\<exists>it'\<subseteq>d. it' \<noteq> {} \<and> \<not> c \<sigma>' \<and> I it' \<sigma>')"
          let ?\<sigma>' = "Assoc_List.iteratei_aux c ?f ts \<sigma>"
          
          from invar have "distinct (map fst ts)" by simp
          moreover from `I it \<sigma>` have "?I (?it'' (dom (map_of ts))) \<sigma>" by simp
          ultimately
          have IH': "?I (?it'' {}) ?\<sigma>' \<or> (\<exists>it\<subseteq>dom (map_of ts). it \<noteq> {} \<and> \<not> c ?\<sigma>' \<and> ?I (?it'' it) ?\<sigma>')"
          proof(rule iteratei_aux_correct)
            fix k t it' \<sigma>'
            assume "c \<sigma>'" "k \<in> it'" 
              and kt: "map_of ts k = Some t" 
              and "it' \<subseteq> dom (map_of ts)"
              and "?I (?it'' it') \<sigma>'"
            from `?I (?it'' it') \<sigma>'`
            show "?I (?it'' (it' - {k})) (?f k t \<sigma>')"
            proof
              assume "\<exists>it'\<subseteq>d. it' \<noteq> {} \<and> \<not> c \<sigma>' \<and> I it' \<sigma>'"
              then obtain it' where "it' \<subseteq> d" "it' \<noteq> {}" "\<not> c \<sigma>'" "I it' \<sigma>'" by blast
              thus ?thesis unfolding iteratei_postfixed_interrupt[of c \<sigma>', OF `\<not> c \<sigma>'`] by blast
            next
              assume "I (?it'' it') \<sigma>'"
              note c\<sigma>
              moreover from kt have "(k, t) \<in> set ts" by(rule map_of_SomeD)
              moreover note `c \<sigma>'`
              moreover with kt invar have "trie_invar t" by auto
              moreover note `I (?it'' it') \<sigma>'`
              moreover have "ipres t d (k # ks0)" unfolding ipres_def
              proof(intro strip)
                fix \<sigma>' ks' v' it'
                assume "c \<sigma>'" and "ks' @ k # ks0 \<in> it'" and "lookup t (rev ks') = Some v'"
                  and it': "it' \<subseteq> d" and "I it' \<sigma>'"
                
                note `c \<sigma>'`
                moreover from `ks' @ k # ks0 \<in> it'` have "(ks' @ [k]) @ ks0 \<in> it'" by simp
                moreover from Cons `lookup t (rev ks') = Some v'` kt
                have "lookup (Trie vo ts) (rev (ks' @ [k])) = Some v'" by simp
                ultimately have "I (it' - {(ks' @ [k]) @ ks0}) (f ((ks' @ [k]) @ ks0) v' \<sigma>')"
                  using `it' \<subseteq> d` `I it' \<sigma>'` by(rule ipres)
                thus "I (it' - {ks' @ k # ks0}) (f (ks' @ k # ks0) v' \<sigma>')" by simp
              qed
              moreover have "?it'' it' \<subseteq> d" using `it \<subseteq> d` by auto
              moreover from it_supset have "(\<lambda>ks. rev ks @ k # ks0) ` dom (lookup t) \<subseteq> ?it'' it'"
                using kt `k \<in> it'` by(fastforce intro!: rev_image_eqI simp add: dom_lookup)
              ultimately 
              have "I (?it'' it' - (\<lambda>ks. rev ks @ k # ks0) ` dom (lookup t)) (iteratei_postfixed c f t \<sigma>' (k # ks0)) \<or>
                    (\<exists>it''\<subseteq> d. it'' \<noteq> {} \<and> \<not> c (iteratei_postfixed c f t \<sigma>' (k # ks0)) \<and>
                                      I it'' (iteratei_postfixed c f t \<sigma>' (k # ks0)))"
                (is "?terminate \<or> ?interrupt") by(rule IH)
              thus ?thesis
              proof
                assume "?terminate"
                also have "?it'' it' - (\<lambda>ks. rev ks @ k # ks0) ` dom (lookup t) = ?it'' (it' - {k})"
                  (is "?lhs = ?rhs")
                proof(intro equalityI subsetI)
                  fix x
                  assume "x \<in> ?lhs"
                  thus "x \<in> ?rhs" using kt by(auto)
                next
                  fix x
                  assume "x \<in> ?rhs"
                  thus "x \<in> ?lhs" using kt
                    by auto(fastforce intro: image_eqI[where x="Cons a b", standard, where a=k])
                qed
                finally show ?thesis ..
              next
                assume "?interrupt"
                thus ?thesis by blast
              qed
            qed
          qed
          hence "I (it - (\<lambda>ks. rev ks @ ks0) ` (\<Union>k\<in>dom (map_of ts). op # k ` dom (lookup (the (map_of ts k))))) ?\<sigma>' \<or>
                (\<exists>it'\<subseteq>d. it' \<noteq> {} \<and> \<not> c ?\<sigma>' \<and> I it' ?\<sigma>')"
          proof
            assume "?I (?it'' {}) ?\<sigma>'"
            thus ?thesis by simp
          next
            assume "\<exists>it\<subseteq>dom (map_of ts). it \<noteq> {} \<and> \<not> c ?\<sigma>' \<and> ?I (?it'' it) ?\<sigma>'"
            then obtain it' where "it' \<subseteq> dom (map_of ts)"
              and "it' \<noteq> {}" and "\<not> c ?\<sigma>'" and "?I (?it'' it') ?\<sigma>'" by blast
            from `?I (?it'' it') ?\<sigma>'` have "\<exists>it'\<subseteq>d. it' \<noteq> {} \<and> \<not> c ?\<sigma>' \<and> I it' ?\<sigma>'"
            proof
              assume "I (?it'' it') ?\<sigma>'"
              moreover from `it' \<noteq> {}` `it' \<subseteq> dom (map_of ts)`
              obtain k' t' where "k' \<in> it'" "map_of ts k' = Some t'" by(fastforce)
              with invar have "\<not> isEmpty t'" "trie_invar t'" by auto
              from `\<not> isEmpty t'` have "dom (lookup t') \<noteq> {}"
                unfolding dom_lookup_empty_conv[OF `trie_invar t'`] .
              then obtain ks' where "ks' \<in> dom (lookup t')" by(auto simp del: dom_eq_empty_conv)
              with `k' \<in> it'` `map_of ts k' = Some t'` `it' \<subseteq> dom (map_of ts)` it_supset
              have "?it'' it' \<noteq> {}"
                by(fastforce simp add: dom_lookup dest: subsetD[where c="rev (k' # ks') @ ks0"] intro: image_eqI[where x="k' # ks'"] bexI[where x=k'])
              moreover from `it \<subseteq> d` have "?it'' it' \<subseteq> d" by auto
              ultimately show ?thesis using `\<not> c ?\<sigma>'` by(blast)
            qed
            thus ?thesis ..
          qed
          thus ?thesis
          proof
            assume "\<exists>it'\<subseteq>d. it' \<noteq> {} \<and> \<not> c ?\<sigma>' \<and> I it' ?\<sigma>'"
            then obtain it' where "it' \<subseteq> d" "it' \<noteq> {}" "\<not> c ?\<sigma>'" "I it' ?\<sigma>'" by blast
            thus ?thesis using True c\<sigma> unfolding it_def \<sigma>_def
              by(auto simp add: iteratei_postfixed_interrupt)
          next
            assume "I (it - (\<lambda>ks. rev ks @ ks0) ` (\<Union>k\<in>dom (map_of ts). op # k ` dom (lookup (the (map_of ts k))))) ?\<sigma>'"
            thus ?thesis using True c\<sigma> unfolding it_def \<sigma>_def
              by(auto simp add: dom_lookup Diff_insert2[symmetric] del: disjCI)
          qed
        qed
      qed
    qed }
  note A = this
  have "ipres t ((\<lambda>ks. rev ks @ ks0) ` dom (lookup t)) ks0"
    unfolding ipres_def by(auto intro: step)
  from A[OF I this subset_refl subset_refl]
  show ?thesis by simp
qed

lemma trie_iteratei_correct:
  assumes invar: "trie_invar t"
  and I: "I (rev ` dom (lookup t)) \<sigma>0"
  and step: "\<And>k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; lookup t (rev k) = Some v; it \<subseteq> rev ` (dom (lookup t)); I it \<sigma> \<rbrakk>
             \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  shows "I {} (iteratei c f t \<sigma>0) \<or> 
        (\<exists>it. it \<subseteq> rev ` dom (lookup t) \<and> it \<noteq> {} \<and> \<not> (c (iteratei c f t \<sigma>0)) \<and> I it (iteratei c f t \<sigma>0))"
proof -
  note invar
  moreover from I have "I ((\<lambda>ks. rev ks @ []) ` dom (lookup t)) \<sigma>0" by simp
  ultimately have "I {} (iteratei_postfixed c f t \<sigma>0 []) \<or>
               (\<exists>it\<subseteq>(\<lambda>ks. rev ks @ []) ` dom (lookup t). it \<noteq> {} \<and> \<not> c (iteratei_postfixed c f t \<sigma>0 []) \<and>
                   I it (iteratei_postfixed c f t \<sigma>0 []))"
    by(rule iteratei_postfixed_correct)(auto intro: step)
  thus ?thesis by(simp add: iteratei_def)
qed

hide_const (open) empty isEmpty iteratei lookup update delete
hide_type (open) trie

end