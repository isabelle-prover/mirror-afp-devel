(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Map Implementation by Red-Black-Trees*}
theory RBTMapImpl
imports Main MapSpec More_List RBT_Impl MapGA
begin
text_raw {*\label{thy:RBTMapImpl}*}


text {*
  The abbreviations used by this implementation are rm,r.
*}

types ('k,'v) rm = "('k,'v) RBT_Impl.rbt"

subsection "Definitions"
definition "rm_\<alpha> == RBT_Impl.lookup"
definition "rm_invar == RBT_Impl.is_rbt"
definition "rm_empty == RBT_Impl.Empty"
definition "rm_lookup k m == RBT_Impl.lookup m k"
definition "rm_update == RBT_Impl.insert"
definition "rm_update_dj == rm_update"
definition "rm_delete == RBT_Impl.delete"
definition "rm_iterate == RBT_Impl.fold"

(* TODO: The iterator could be defined as in-order traversal. Then we could
  show that iteration is always done in ascending order of keys.*)
(* TODO: In case of interrupt, the interrupt condition may get evaluated 
  twice on the same state: If the iteration interrupts in the right subtree,
  it will be continued in the left subtree to immediately interrupt again.
*)
fun rm_iteratei 
  :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('k,'v) rm \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  where
  "rm_iteratei c f RBT_Impl.Empty \<sigma> = \<sigma>" |
  "rm_iteratei c f (RBT_Impl.Branch col l k v r) \<sigma> = (
    if (c \<sigma>) then
      rm_iteratei c f l (rm_iteratei c f r (f k v \<sigma>))
    else 
      \<sigma>
  )"

definition "rm_add == it_add rm_update rm_iterate"
definition "rm_add_dj == rm_add"
definition "rm_isEmpty m == m=RBT_Impl.Empty"
definition "rm_sel == iti_sel rm_iteratei"

definition "rm_ball == sel_ball rm_sel"
definition "rm_to_list == it_map_to_list rm_iterate"
definition "list_to_rm == gen_list_to_map rm_empty rm_update"

definition "rm_sng == map_sng rm_empty rm_update"

subsection "Correctness"

lemmas rm_defs = 
  rm_\<alpha>_def
  rm_invar_def
  rm_empty_def
  rm_lookup_def
  rm_update_def
  rm_update_dj_def
  rm_delete_def
  rm_iterate_def
  rm_add_def
  rm_add_dj_def
  rm_isEmpty_def
  rm_sel_def
  rm_ball_def
  rm_to_list_def
  list_to_rm_def


lemma rm_empty_impl: "map_empty rm_\<alpha> rm_invar rm_empty"
  by (unfold_locales, unfold rm_defs)
     (simp_all add: RBT_Impl.lookup_Empty RBT_Impl.lookup_insert RBT_Impl.insert_is_rbt)

lemma rm_lookup_impl: "map_lookup rm_\<alpha> rm_invar rm_lookup"
  by (unfold_locales, unfold rm_defs)
     (simp_all add: RBT_Impl.lookup_Empty RBT_Impl.lookup_insert RBT_Impl.insert_is_rbt)

lemma rm_update_impl: "map_update rm_\<alpha> rm_invar rm_update"
  by (unfold_locales, unfold rm_defs)
     (simp_all add: RBT_Impl.lookup_Empty RBT_Impl.lookup_insert RBT_Impl.insert_is_rbt)

lemma rm_update_dj_impl: "map_update_dj rm_\<alpha> rm_invar rm_update_dj"
  by (unfold_locales, unfold rm_defs)
     (simp_all add: RBT_Impl.lookup_Empty RBT_Impl.lookup_insert RBT_Impl.insert_is_rbt)

lemma rm_delete_impl: "map_delete rm_\<alpha> rm_invar rm_delete"
  by (unfold_locales, unfold rm_defs)
     (simp_all add: RBT_Impl.lookup_Empty RBT_Impl.lookup_insert RBT_Impl.insert_is_rbt
       RBT_Impl.lookup_delete)

lemma rm_iterate_alt: 
  "rm_iterate f t \<sigma> = foldl (\<lambda>x (k, v). f k v x) \<sigma> (RBT_Impl.entries t)"
  by (simp add: rm_iterate_def RBT_Impl.fold_def foldl_fold prod_case_split split_def)

lemma rm_\<alpha>_alist: "rm_invar m \<Longrightarrow> rm_\<alpha> m = Map.map_of (RBT_Impl.entries m)"
  by (unfold rm_\<alpha>_def rm_invar_def)
     (simp add: map_of_entries)

lemma rm_\<alpha>_finite[simp, intro!]: "finite (dom (rm_\<alpha> m))" 
  by (simp add: rm_\<alpha>_def)
  
lemma rm_is_finite_map: "finite_map rm_\<alpha> rm_invar" by (unfold_locales) auto


lemma rm_iterate_impl: 
  "map_iterate rm_\<alpha> rm_invar rm_iterate"
  apply (unfold_locales)
  apply (unfold rm_iterate_alt)
  apply simp
  apply (simp only: rm_\<alpha>_alist dom_map_of_conv_image_fst)
proof -
  case goal1 thus ?case 
  proof (rule_tac 
      distinct_foldl_invar[of "RBT_Impl.entries m" "\<lambda>S \<sigma>. I (fst ` S) \<sigma>" 
                              \<sigma>0 "\<lambda>\<sigma> (k,v). f k v \<sigma>", 
                           simplified]
    )
    assume A: 
      "rm_invar m" 
      "I (fst ` set (RBT_Impl.entries m)) \<sigma>0"
      "\<And>k it v \<sigma>.
         \<lbrakk>k \<in> it; Map.map_of (RBT_Impl.entries m) k = Some v;
          it \<subseteq> fst ` set (RBT_Impl.entries m); I it \<sigma>\<rbrakk>
         \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"

    from A(1) have ST: "RBT_Impl.sorted m" by (simp add: rm_invar_def)
    with distinct_entries have "distinct (List.map fst (RBT_Impl.entries m))" .
    thus DAL: "distinct (RBT_Impl.entries m)" by (rule distinct_map)
    from A(2) show "I (fst ` set (RBT_Impl.entries m)) \<sigma>0" .
    
    fix x it \<sigma>
    assume B: "x \<in> it" "it \<subseteq> set (RBT_Impl.entries m)" "I (fst ` it) \<sigma>"

    have 
      ALD: "!!k v v'. \<lbrakk>(k,v)\<in>set (RBT_Impl.entries m); (k,v')\<in>set (RBT_Impl.entries m)\<rbrakk> \<Longrightarrow> v=v'" 
      using distinct_map_eq[OF distinct_entries[OF ST]]
      by auto
    hence ALD': "!!k v v'. \<lbrakk>(k,v)\<in>it; (k,v')\<in>it\<rbrakk> \<Longrightarrow> v=v'" using B(2) by blast

    obtain k v where [simp]: "x=(k,v)" by force
    have "I (fst ` it - {k}) (f k v \<sigma>)" proof (rule A(3))
      from B(1) show "k\<in>fst ` it" by force
      show "Map.map_of (RBT_Impl.entries m) k = Some v" using B(1,2)
        apply (rule_tac ccontr)
        apply (case_tac "Map.map_of (RBT_Impl.entries m) k")
        apply auto
        apply (subgoal_tac "(k,v)\<in>set (RBT_Impl.entries m)")
        apply (drule split_list)
        apply force
        apply blast
        apply (subgoal_tac "(k,a)\<in>set (RBT_Impl.entries m)")
        apply (blast dest: ALD)
        apply (auto dest: map_of_SomeD)
        done
      from B(2) show "fst ` it \<subseteq> fst ` set (RBT_Impl.entries m)" by auto
      from B(3) show "I (fst ` it) \<sigma>" .
    qed
    moreover have "fst ` (it - {(k, v)}) = fst ` it - {k}" using ALD' B(1)
      by auto
    ultimately show "I (fst ` (it - {x})) ((\<lambda>(k, v). f k v \<sigma>) x)" by simp
  qed
qed


lemma rm_iteratei_impl: "map_iteratei rm_\<alpha> rm_invar rm_iteratei"
  apply unfold_locales
  apply simp
proof -
  case (goal1 m I \<sigma> c f)

  txt {* We define a shortcut for the invariant preservation property, 
    parameterized by the map and the overall set of keys *}
  def ipres == "\<lambda>m d. \<forall>\<sigma> k v it. 
      ( c \<sigma> 
        \<and> k \<in> it \<and> RBT_Impl.lookup m k = Some v 
        \<and> it \<subseteq> d \<and> I it \<sigma> 
      ) \<longrightarrow> I (it - {k}) (f k v \<sigma>)"

  txt {*
    If the condition does not hold,
    the iteration will do nothing.
    *}
  have [simp]: "!!\<sigma> m. \<not>c \<sigma> \<Longrightarrow> rm_iteratei c f m \<sigma> = \<sigma>"
    by (case_tac m)
        simp_all

  {
    txt {*
      First, we show an auxiliary lemma that allows us to 
      split up the invariant preservation property to subtrees
      *}
    fix col l k' v' r d
    assume A:
      "RBT_Impl.sorted (RBT_Impl.Branch col l k' v' r)"
      "ipres (RBT_Impl.Branch col l k' v' r) d"

    from A(1) have ST: "l |\<guillemotleft> k'" "k' \<guillemotleft>| r" "RBT_Impl.sorted l" "RBT_Impl.sorted r" 
      by simp_all

    have L: "ipres l d"
      apply (unfold ipres_def)
      apply auto
    proof -
      fix \<sigma> k v it
      assume P:
        "c \<sigma>" 
        "k\<in>it" 
        "RBT_Impl.lookup l k = Some v" 
        "it \<subseteq> d" 
        "I it \<sigma>"

      from P(3) have "k\<in>set (RBT_Impl.keys l)"
        by (auto simp add: lookup_keys [symmetric] ST(3))
      with ST(1) tree_less_prop have "k < k'" by auto
      with P(3) have "RBT_Impl.lookup (RBT_Impl.Branch col l k' v' r) k = Some v"
        by (simp)
      thus "I (it - {k}) (f k v \<sigma>)"
        using P(1,2,4,5) A(2)
        apply (unfold ipres_def)
        apply blast
        done
    qed

    have R: "ipres r d"
      apply (unfold ipres_def)
      apply auto
    proof -
      fix \<sigma> k v it
      assume P:
        "c \<sigma>" 
        "k\<in>it" 
        "RBT_Impl.lookup r k = Some v" 
        "it \<subseteq> d" 
        "I it \<sigma>"

      from P(3) have "k\<in>set (RBT_Impl.keys r)" 
        by (auto simp add: lookup_keys[symmetric] ST(4))
      with ST(2) tree_greater_prop have "k' < k" by auto
      with P(3) have "RBT_Impl.lookup (RBT_Impl.Branch col l k' v' r) k = Some v"
        by auto
      thus "I (it - {k}) (f k v \<sigma>)"
        using P(1,2,4,5) A(2)
        apply (unfold ipres_def)
        apply blast
        done
    qed
        
    note L R
  } note ipres_split = this


  txt {* Next, we show a generalized goal, that fixes the domain of the 
    original map to @{text d}, and works for any set @{text it} of remaining
    keys, that is @{text \<supseteq>} the domain of the current map and @{text "\<subseteq> d"}.
    This generalization is required to get the induction through.
    *}
  have G: "!!it d. \<lbrakk>
    rm_invar m;
    I it \<sigma>;
    ipres m d;
    it \<supseteq> dom (rm_\<alpha> m);
    it \<subseteq> d
    \<rbrakk> \<Longrightarrow> I (it - dom (rm_\<alpha> m)) (rm_iteratei c f m \<sigma>) 
          \<or> (\<exists>it'\<subseteq>it. 
               it' \<noteq> {} 
               \<and> \<not> c (rm_iteratei c f m \<sigma>)  
               \<and> I it' (rm_iteratei c f m \<sigma>))"
    apply (unfold rm_\<alpha>_def rm_invar_def)
    apply (drule is_rbt_sorted)
  proof (induct m arbitrary: it \<sigma>)
    case Empty thus ?case by (simp add: lookup_Empty)
  next
    case (Branch col m1 a b m2)
    {
      assume C: "\<not>c \<sigma>"
      txt {* If the condition does not hold initially, the 
        iterator will return the original state, and
        we are in the second case (interrupt) of our proposition: *}
      from Branch.prems(3) have "it\<noteq>{}" by auto
      with C have ?case
        apply (simp del: RBT_Impl.lookup.simps)
        apply (rule_tac disjI2)
        apply (rule_tac x=it in exI)
        apply (simp add: Branch.prems(1))
        done
    } moreover {
      assume C: "c \<sigma>"
      txt {*
        If the condition holds, we can apply the first step. Due to the
        invariant preservation rule, the invariant holds for the resulting state.
        *}
      have I': "I (it - {a}) (f a b \<sigma>)" using Branch.prems
        apply (rule_tac Branch.prems(2)[unfolded ipres_def, rule_format])
        apply (auto simp add: C)
        done
      txt {* The invariant preservation rule also holds for the left and 
        right subtree *}
      note IPR = ipres_split[OF Branch.prems(5,2)]

      txt {* Also the sorted tree properties can be transferred to the subtrees*}
      from Branch.prems(5) have ST: "m1 |\<guillemotleft> a" "a \<guillemotleft>| m2" "RBT_Impl.sorted m1" "RBT_Impl.sorted m2"
        by simp_all

      txt {* As @{term a} is the key of the original tree, the subtrees, 
        in particular the right one, does not contain @{term a}. 
        With @{thm Branch.prems(3)} we thus get:
        *}
      from Branch.prems(3,5) have DSS: "dom (RBT_Impl.lookup m2) \<subseteq> it - {a}"
        apply (simp only: lookup_keys ST)
        apply (auto simp add: tree_greater_prop tree_less_prop)
        done
      txt {* Also, with @{thm Branch.prems(4)}, we get: *}
      from Branch.prems(4) have IMAS: "it - {a} \<subseteq> d" by auto
      
      txt {* Now we can apply the induction hypothesis for the right subtree: *}
      from Branch.hyps(2)[OF I' IPR(2) DSS IMAS ST(4)] have 
        "I (it - {a} - dom (RBT_Impl.lookup m2)) (rm_iteratei c f m2 (f a b \<sigma>)) 
         \<or> (\<exists>it'. it' \<subseteq> it - {a} \<and> it' \<noteq> {} 
              \<and> \<not> c (rm_iteratei c f m2 (f a b \<sigma>)) 
              \<and> I it' (rm_iteratei c f m2 (f a b \<sigma>)))" (is "?C1 \<or> ?C2") .
      moreover {
        txt {*
          Case: The iterator interrupted in the right subtree:
          *}
        assume ?C2
        then obtain it' where 
          "it'\<subseteq>it-{a}" 
          "it'\<noteq>{}" 
          "\<not>c (rm_iteratei c f m2 (f a b \<sigma>))" 
          "I it' (rm_iteratei c f m2 (f a b \<sigma>))"
          by auto
        hence ?case using C
          apply (rule_tac disjI2)
          apply (rule_tac x=it' in exI)
          apply auto
          done
      } moreover {
        txt {*
          Case: The iterator completely finished the right subtree:
          *}
        assume C1: ?C1
        txt {*
          In this case, we continue to iterate over the left subtree.
          We first show the prerequisites of the induction hypothesis for
          the left subtree:
          *}

        from Branch.prems(3,5) have 
          DSS: "dom (RBT_Impl.lookup m1) \<subseteq> it - {a} - dom (RBT_Impl.lookup m2)"
          apply (simp only: lookup_keys ST)
          apply (force simp add: tree_greater_prop tree_less_prop)
          done

        from Branch.prems(4) have IMAS: "it - {a} - dom (RBT_Impl.lookup m2) \<subseteq> d" by auto

        txt {* Finally, we can apply the induction hypothesis on the iteration over
          the left subtree, and get two cases: Ordinary termination or interrupt.*}
        from Branch.hyps(1)[OF C1 IPR(1) DSS IMAS ST(3)] have
          "I (it - {a} - dom (RBT_Impl.lookup m2) - dom (RBT_Impl.lookup m1)) 
             (rm_iteratei c f m1 (rm_iteratei c f m2 (f a b \<sigma>))) 
          \<or> (\<exists>it'. 
               it' \<subseteq> it - {a} - dom (RBT_Impl.lookup m2) 
               \<and> it' \<noteq> {} 
               \<and> \<not> c (rm_iteratei c f m1 (rm_iteratei c f m2 (f a b \<sigma>))) 
               \<and> I it' (rm_iteratei c f m1 (rm_iteratei c f m2 (f a b \<sigma>))))"
          .
        txt {* From these, it's straightforward to show the goal: *}
        hence ?case using C
          apply (simp only: dom_lookup_Branch [OF Branch.prems(5)])
          apply (simp add: Diff_insert2[symmetric] set_diff_diff_left)
          apply (simp only: Un_commute)
          apply (erule disjE)
          apply auto
          done
      } ultimately have ?case by blast
    } ultimately show ?case by blast
  qed
  txt {* Finally, we derive the original goal from the generalized one.*}
  from goal1(3) have IPR: "ipres m (dom (rm_\<alpha> m))"
    by (unfold ipres_def rm_\<alpha>_def) auto
  from G[OF goal1(1,2) IPR] show ?case by auto
qed

lemmas rm_add_impl = 
  it_add_correct[OF rm_iterate_impl rm_update_impl, folded rm_add_def]

lemmas rm_add_dj_impl =  
  map_add.add_dj_by_add[OF rm_add_impl, folded rm_add_dj_def]

lemma rm_isEmpty_impl: "map_isEmpty rm_\<alpha> rm_invar rm_isEmpty"
  apply (unfold_locales)
  apply (unfold rm_defs)
  apply (case_tac m)
  apply (fastsimp intro: ext)
  apply (auto simp add: map_of_entries [OF is_rbt_sorted, symmetric])
  done

lemmas rm_sel_impl = iti_sel_correct[OF rm_iteratei_impl, folded rm_sel_def]

lemmas rm_ball_impl = sel_ball_correct[OF rm_sel_impl, folded rm_ball_def]

lemmas rm_to_list_impl 
  = it_map_to_list_correct[OF rm_iterate_impl, folded rm_to_list_def]

lemmas list_to_rm_impl
  = gen_list_to_map_correct[OF rm_empty_impl rm_update_impl, 
                            folded list_to_rm_def]

lemmas rm_sng_correct 
  = map_sng_correct[OF rm_empty_impl rm_update_impl, folded rm_sng_def]

interpretation rm: map_empty rm_\<alpha> rm_invar rm_empty 
  using rm_empty_impl .
interpretation rm: map_lookup rm_\<alpha> rm_invar rm_lookup 
  using rm_lookup_impl .
interpretation rm: map_update rm_\<alpha> rm_invar rm_update 
  using rm_update_impl .
interpretation rm: map_update_dj rm_\<alpha> rm_invar rm_update_dj 
  using rm_update_dj_impl .
interpretation rm: map_delete rm_\<alpha> rm_invar rm_delete 
  using rm_delete_impl .
interpretation rm: finite_map rm_\<alpha> rm_invar 
  using rm_is_finite_map .
interpretation rm: map_iterate rm_\<alpha> rm_invar rm_iterate 
  using rm_iterate_impl .
interpretation rm: map_iteratei rm_\<alpha> rm_invar rm_iteratei
  using rm_iteratei_impl .
interpretation rm: map_add rm_\<alpha> rm_invar rm_add 
  using rm_add_impl .
interpretation rm: map_add_dj rm_\<alpha> rm_invar rm_add_dj 
  using rm_add_dj_impl .
interpretation rm: map_isEmpty rm_\<alpha> rm_invar rm_isEmpty 
  using rm_isEmpty_impl .
interpretation rm: map_sel rm_\<alpha> rm_invar rm_sel 
  using rm_sel_impl .
interpretation rm: map_ball rm_\<alpha> rm_invar rm_ball 
  using rm_ball_impl .
interpretation rm: map_to_list rm_\<alpha> rm_invar rm_to_list 
  using rm_to_list_impl .
interpretation rm: list_to_map rm_\<alpha> rm_invar list_to_rm 
  using list_to_rm_impl . 

declare rm.finite[simp del, rule del]
thm rm_\<alpha>_finite 


lemmas rm_correct =
  rm.empty_correct
  rm.lookup_correct
  rm.update_correct
  rm.update_dj_correct
  rm.delete_correct
  rm.add_correct
  rm.add_dj_correct
  rm.isEmpty_correct
  rm.ball_correct
  rm.to_list_correct
  rm.to_map_correct
  rm_sng_correct

subsection "Code Generation"

export_code
  rm_empty
  rm_lookup
  rm_update
  rm_update_dj
  rm_delete
  rm_iterate
  rm_iteratei
  rm_add
  rm_add_dj
  rm_isEmpty
  rm_sel
  rm_ball
  rm_to_list
  list_to_rm
  rm_sng
  in SML
  module_name RBTMap
  file -

end
