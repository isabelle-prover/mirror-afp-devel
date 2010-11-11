(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changelist since submission on 2009-11-26:

  2009-12-09: Ordered iterators, to_list produces sorted list


*)
header {* \isaheader{Map Implementation by Red-Black-Trees} *}
theory RBTMapImpl
imports OrderedMap More_List "common/RBT_add" MapGA 
begin
text_raw {*\label{thy:RBTMapImpl}*}


text {*
  The abbreviations used by this implementation are rm,r.
*}

types ('k,'v) rm = "('k,'v) RBT.rbt"

subsection "Definitions"
definition "rm_\<alpha> == RBT.lookup"
abbreviation (input) rm_invar where "rm_invar == \<lambda>_. True"
definition "rm_empty == RBT.empty"
definition "rm_lookup k m == RBT.lookup m k"
definition "rm_update == RBT.insert"
definition "rm_update_dj == rm_update"
definition "rm_delete == RBT.delete"
definition rm_iterateoi where "rm_iterateoi c f r == RBT_add.rm_iterateoi c f (RBT.impl_of r)"
definition rm_reverse_iterateoi where "rm_reverse_iterateoi c f r == RBT_add.rm_reverse_iterateoi c f (RBT.impl_of r)"
definition "rm_iterateo == itoi_iterateo rm_iterateoi"
definition "rm_reverse_iterateo == itoi_reverse_iterateo rm_reverse_iterateoi"
definition "rm_iteratei == rm_iterateoi"
definition "rm_iterate == rm_iterateo"

definition "rm_add == it_add rm_update rm_iterate"
definition "rm_add_dj == rm_add"
definition "rm_isEmpty m == m=RBT.empty"
definition "rm_sel == iti_sel rm_iteratei"
definition "rm_sel' = sel_sel' rm_sel"

definition "rm_ball == sel_ball rm_sel"
definition "rm_to_list == rito_map_to_sorted_list rm_reverse_iterateo"
definition "list_to_rm == gen_list_to_map rm_empty rm_update"

definition "rm_sng == map_sng rm_empty rm_update"

definition "rm_min == MapGA.itoi_min rm_iterateoi"

definition "rm_max == MapGA.ritoi_max rm_reverse_iterateoi"

subsection "Correctness"

lemmas rm_defs = 
  rm_\<alpha>_def
  rm_empty_def
  rm_lookup_def
  rm_update_def
  rm_update_dj_def
  rm_delete_def
  rm_iterate_def
  rm_iteratei_def
  rm_iterateo_def
  rm_iterateoi_def
  rm_reverse_iterateo_def
  rm_reverse_iterateoi_def
  rm_add_def
  rm_add_dj_def
  rm_isEmpty_def
  rm_sel_def
  rm_sel'_def
  rm_ball_def
  rm_to_list_def
  list_to_rm_def
  rm_min_def
  rm_max_def

lemma rm_empty_impl: "map_empty rm_\<alpha> rm_invar rm_empty"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_lookup_impl: "map_lookup rm_\<alpha> rm_invar rm_lookup"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_update_impl: "map_update rm_\<alpha> rm_invar rm_update"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_update_dj_impl: "map_update_dj rm_\<alpha> rm_invar rm_update_dj"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

lemma rm_delete_impl: "map_delete rm_\<alpha> rm_invar rm_delete"
  by (unfold_locales, unfold rm_defs)
     (simp_all)

(* Discontinued, as iterators are no longer implemented by fold. *)
(*lemma rm_iterate_alt: 
  "rm_iterate f t \<sigma> = foldl (\<lambda>x (k, v). f k v x) \<sigma> (alist_of t)"
  by (simp add: rm_iterate_def fold_alist_fold)
*)

lemma rm_\<alpha>_alist: "rm_invar m \<Longrightarrow> rm_\<alpha> m = Map.map_of (RBT.entries m)"
  by (simp add: rm_\<alpha>_def)


lemma rm_\<alpha>_finite[simp, intro!]: "finite (dom (rm_\<alpha> m))" 
  by (simp add: rm_\<alpha>_def)
  
lemma rm_is_finite_map: "finite_map rm_\<alpha> rm_invar" by (unfold_locales) auto

lemma rm_iterateoi_impl_aux: "map_iterateoi RBT_Impl.lookup RBT_Impl.is_rbt RBT_add.rm_iterateoi"
proof
  fix m
  show "finite (dom (RBT_Impl.lookup m))" by simp
next
  fix m :: "('a, 'b) RBT_Impl.rbt" and I :: "'a set \<Rightarrow> 'c \<Rightarrow> bool" and \<sigma> c f
  assume inv: "is_rbt m"
    and I0: "I (dom (RBT_Impl.lookup m)) \<sigma>"
    and step: "\<And>k v it \<sigma>.
               \<lbrakk> c \<sigma>; k \<in> it; \<forall>j\<in>it. k \<le> j; RBT_Impl.lookup m k = Some v; it \<subseteq> dom (RBT_Impl.lookup m); I it \<sigma> \<rbrakk>
               \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"

  txt {* We define a shortcut for the invariant preservation property, 
    parameterized by the map and the overall set of keys *}
  def ipres == "\<lambda>m d. \<forall>\<sigma> k v it. 
      c \<sigma> \<longrightarrow> k \<in> it \<longrightarrow> (\<forall>j\<in>it. k\<le>j) \<longrightarrow> RBT_Impl.lookup m k = Some v \<longrightarrow> it \<subseteq> d \<longrightarrow> I it \<sigma> 
      \<longrightarrow> I (it - {k}) (f k v \<sigma>)"

  {
    txt {*
      First, we show an auxiliary lemma that allows us to 
      split up the invariant preservation property to subtrees
      *}
    fix col l k' v' r d
    assume A:
      "RBT_Impl.sorted (Branch col l k' v' r)"
      "ipres (Branch col l k' v' r) d"

    from A(1) have ST: "l |\<guillemotleft> k'" "k' \<guillemotleft>| r" "RBT_Impl.sorted l" "RBT_Impl.sorted r" 
      by simp_all

    have L: "ipres l d" unfolding ipres_def
    proof(intro strip)
      fix \<sigma> k v it
      assume P:
        "c \<sigma>" 
        "k\<in>it" 
        "RBT_Impl.lookup l k = Some v" 
        "it \<subseteq> d" 
        "I it \<sigma>"
        "\<forall>j\<in>it. k\<le>j"

      from P(3) have "k\<in>set (RBT_Impl.keys l)" 
        by (auto simp add: lookup_keys[symmetric] ST(3))
      with ST(1) tree_less_prop have "k < k'" by auto
      with P(3) have "RBT_Impl.lookup (Branch col l k' v' r) k = Some v"
        by (simp)
      thus "I (it - {k}) (f k v \<sigma>)"
        using P(1,2,4,5,6) A(2)
        by (unfold ipres_def) blast
    qed

    have R: "ipres r d" unfolding ipres_def
    proof(intro strip)
      fix \<sigma> k v it
      assume P:
        "c \<sigma>" 
        "k\<in>it" 
        "RBT_Impl.lookup r k = Some v" 
        "it \<subseteq> d" 
        "I it \<sigma>"
        "\<forall>j\<in>it. k\<le>j"

      from P(3) have "k\<in>set (RBT_Impl.keys r)" 
        by (auto simp add: lookup_keys[symmetric] ST(4))
      with ST(2) tree_greater_prop have "k' < k" by auto
      with P(3) have "RBT_Impl.lookup (Branch col l k' v' r) k = Some v"
        by auto
      thus "I (it - {k}) (f k v \<sigma>)"
        using P(1,2,4,5,6) A(2)
        by(unfold ipres_def) blast
    qed
        
    note L R
  } note ipres_split = this


  txt {* Next, we show a generalized goal, that fixes the domain of the 
    original map to @{text d}, and works for any set @{text it} of remaining
    keys, that is @{text \<supseteq>} the domain of the current map and @{text "\<subseteq> d"}.
    This generalization is required to get the induction through.
    *}

  { fix it d
    assume is_rbt: "RBT_Impl.is_rbt m"
      and rest: "I it \<sigma>" "ipres m d" "it \<supseteq> dom (RBT_Impl.lookup m)"
      "\<forall>k\<in>dom (RBT_Impl.lookup m). \<forall>k'\<in>it-dom (RBT_Impl.lookup m). k\<le>k'"
      "it \<subseteq> d"
    from is_rbt have "RBT_Impl.sorted m" by(rule is_rbt_sorted)
    with rest
    have "I (it - dom (RBT_Impl.lookup m)) (RBT_add.rm_iterateoi c f m \<sigma>) 
          \<or> (\<exists>it'\<subseteq>it. it' \<noteq> {} \<and> \<not> c (RBT_add.rm_iterateoi c f m \<sigma>) \<and> I it' (RBT_add.rm_iterateoi c f m \<sigma>))"
    proof (induct m arbitrary: it \<sigma>)
      case Empty thus ?case by (simp)
    next
      case (Branch col m1 a b m2)
      show ?case
      proof(cases "c \<sigma>")
        case False
        txt {* If the condition does not hold initially, the 
          iterator will return the original state, and
          we are in the second case (interrupt) of our proposition: *}
        from Branch.prems(3) have "it\<noteq>{}" by auto
        with False show ?thesis
          by(simp del: RBT_Impl.lookup.simps add: exI[where x=it] Branch.prems(1))
      next
        case True
        note C = this
      
        txt {* If the condition holds, we descend into the left subtree. *}

        txt {* The invariant preservation rule also holds for the left and 
          right subtree *}
        note IPR = ipres_split[OF Branch.prems(6,2)]

        txt {* Also the sorted tree properties can be transferred to the subtrees*}
        from Branch.prems(6) have ST: "m1 |\<guillemotleft> a" "a \<guillemotleft>| m2" "RBT_Impl.sorted m1" "RBT_Impl.sorted m2"
          by simp_all
        
        txt {* As @{term a} is the key of the original tree, the subtrees, 
          in particular the left one, does not contain @{term a}. 
          With @{thm Branch.prems(3)} we thus get:
          *}
        from Branch.prems(3,6) have DSS: "dom (RBT_Impl.lookup m1) \<subseteq> it"
          apply (simp only: lookup_keys ST)
          apply (auto simp add: tree_greater_prop tree_less_prop)
          done

        txt {* As the whole tree's domain is minimal in the remaining elements, the left subtree is also minimal *}
        from Branch.prems(3,4,6) have 
          MIN: "\<forall>k\<in>dom (RBT_Impl.lookup m1). \<forall>k'\<in>it - dom (RBT_Impl.lookup m1). k \<le> k'"
          apply (simp only: lookup_keys ST)
          apply (intro ballI)
        proof -
          fix k k'
          assume A: 
            "set (RBT_Impl.keys (Branch col m1 a b m2)) \<subseteq> it" 
            "\<forall>k\<in>set (RBT_Impl.keys (Branch col m1 a b m2)). 
               \<forall>k'\<in>it - set (RBT_Impl.keys (Branch col m1 a b m2)). k \<le> k'" 
            "RBT_Impl.sorted (Branch col m1 a b m2)" 
            "k \<in> set (RBT_Impl.keys m1)" 
            "k' \<in> it - set (RBT_Impl.keys m1)"
          {
            assume C: "k'\<in>set (RBT_Impl.keys m2)"
            with A(3,4) have "k\<le>k'" 
              by (force simp add: tree_greater_prop tree_less_prop)
          } moreover {
            assume C: "k'=a"
            with A(3,4) have "k\<le>k'" 
              by (force simp add: tree_greater_prop tree_less_prop)
          } moreover {
            assume C: "k'\<in> it - set (RBT_Impl.keys (Branch col m1 a b m2))"
            with A(2,4) have "k\<le>k'" by auto
          } ultimately show "k\<le>k'" using A(4,5) by auto
        qed
        
        txt {* Now we can apply the induction hypothesis for the left subtree: *}

        from Branch.prems(1) IPR(1) DSS MIN Branch.prems(5) ST(3)
        have
          "I (it - dom (RBT_Impl.lookup m1)) (RBT_add.rm_iterateoi c f m1 \<sigma>) 
           \<or> (\<exists>it'. it' \<subseteq> it \<and> it' \<noteq> {} \<and> \<not> c (RBT_add.rm_iterateoi c f m1 \<sigma>) \<and> I it' (RBT_add.rm_iterateoi c f m1 \<sigma>))"
          (is "?C1 \<or> ?C2")
          by(rule Branch)
        thus ?thesis
        proof
          txt {* Case: The iterator interrupted in the left subtree: *}
          assume ?C2
          then obtain it' 
            where "it'\<subseteq>it" "it'\<noteq>{}" "\<not>c (RBT_add.rm_iterateoi c f m1 \<sigma>)" "I it' (RBT_add.rm_iterateoi c f m1 \<sigma>)"
            by auto
          thus ?thesis using C by auto
        next
          txt {* Case: The iterator completely finished the left subtree: *}
          assume C1: ?C1
          let ?\<sigma>' = "(RBT_add.rm_iterateoi c f m1 \<sigma>)"
          let ?it' = "(it - dom (RBT_Impl.lookup m1))"
          txt {* In this case, we have to check whether the condition still holds *}
          show ?thesis 
          proof (cases "c ?\<sigma>'")
            case False 
            txt {* The iterator will interrupt right here *}
            from Branch.prems(3,6) have ITGM1: "\<not> it \<subseteq> dom (RBT_Impl.lookup m1)"
              apply (simp only: lookup_keys ST)
              apply (auto simp add: tree_greater_prop tree_less_prop)
              done
            thus ?thesis using False C C1 by(auto intro!: exI[where x="?it'"])
          next
            case True
            txt {* The iterator will continue with the current node's single-step and the right subtree *}

            txt {* The root node is the smallest remaining element *}
            have AMIN: "\<forall>k\<in>?it'. a\<le>k" 
            proof (intro ballI)
              fix k
              assume A: "k\<in>it - dom (RBT_Impl.lookup m1)"
              show "a \<le> k"
              proof(cases "k \<in> dom (RBT_Impl.lookup (Branch col m1 a b m2))")
                case False
                with A Branch.prems(4)[rule_format, of a k] show "a\<le>k" by force
              next
                case True 
                with A have "k\<in>set (RBT_Impl.keys m2) \<or> a=k"
                  apply (simp only: lookup_keys ST Branch.prems(6))
                  apply auto
                  done
                with ST show "a\<le>k" by (auto simp add: tree_greater_prop)
              qed
            qed

            txt {* The invariant is preserved over the single-step with the root-node's data *}
            from True have I': "I (?it' - {a}) (f a b ?\<sigma>')" using Branch.prems
              apply (rule_tac Branch.prems(2)[unfolded ipres_def, rule_format])
              apply (auto simp add: C C1 AMIN)
              done
          
            have RMIN: "\<forall>k\<in>dom (RBT_Impl.lookup m2). 
                    \<forall>a\<in>it - dom (RBT_Impl.lookup m1) - {a} - dom (RBT_Impl.lookup m2). 
                      k \<le> a"
              using Branch.prems(4)
              apply (simp only: lookup_keys ST Branch.prems(6))
              apply auto
              done

            from Branch.prems(3,6) have 
              DSS: "dom (RBT_Impl.lookup m2) \<subseteq> ?it' - {a}"
              apply (simp only: lookup_keys ST)
              apply (force simp add: tree_greater_prop tree_less_prop)
              done

            from Branch.prems(5) have IMAS: "?it' - {a} \<subseteq> d" by auto

            txt {* Finally, we can apply the induction hypothesis on the iteration over
              the left subtree, and get two cases: Ordinary termination or interrupt.*}

            from I' IPR(2) DSS RMIN IMAS ST(4) have
              "I (?it' - {a} - dom (RBT_Impl.lookup m2)) (RBT_add.rm_iterateoi c f m2 (f a b ?\<sigma>')) \<or>
              (\<exists>it'. it' \<subseteq> ?it' - {a} \<and> it' \<noteq> {} \<and> \<not> c (RBT_add.rm_iterateoi c f m2 (f a b ?\<sigma>')) \<and>
                     I it' (RBT_add.rm_iterateoi c f m2 (f a b ?\<sigma>')))"
              by(rule Branch)

            thus ?thesis using C True
              apply (simp only: dom_lookup_Branch[OF Branch.prems(6)])
              apply (simp add: Diff_insert2[symmetric] set_diff_diff_left)
              apply auto
              done
          qed
        qed
      qed
    qed }
  note G = this

  txt {* Finally, we derive the original goal from the generalized one.*}
  from step have IPR: "ipres m (dom (RBT_Impl.lookup m))"
    by (unfold ipres_def) auto
  from G[OF inv I0 IPR]
  show "I {} (RBT_add.rm_iterateoi c f m \<sigma>) \<or>
        (\<exists>it\<subseteq>dom (RBT_Impl.lookup m). it \<noteq> {} \<and> \<not> c (RBT_add.rm_iterateoi c f m \<sigma>) \<and> I it (RBT_add.rm_iterateoi c f m \<sigma>))"
    by auto
qed

lemma rm_iterateoi_impl: "map_iterateoi rm_\<alpha> rm_invar rm_iterateoi"
proof
  fix m
  show "finite (dom (rm_\<alpha> m))" by simp
next
  fix m :: "('a, 'b) rm" and I :: "'a set \<Rightarrow> 'c \<Rightarrow> bool" and \<sigma>0 c f
  assume "I (dom (rm_\<alpha> m)) \<sigma>0"
    and "\<And>k v it \<sigma>. \<lbrakk>c \<sigma>; k \<in> it; \<forall>j\<in>it. k \<le> j; rm_\<alpha> m k = Some v; it \<subseteq> dom (rm_\<alpha> m); I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  with is_rbt_impl_of
  show "I {} (rm_iterateoi c f m \<sigma>0) \<or>
        (\<exists>it\<subseteq>dom (rm_\<alpha> m). it \<noteq> {} \<and> \<not> c (rm_iterateoi c f m \<sigma>0) \<and> I it (rm_iterateoi c f m \<sigma>0))"
    unfolding rm_\<alpha>_def RBT.lookup_def rm_iterateoi_def
    by(rule map_iterateoi.iterateoi_rule[OF rm_iterateoi_impl_aux])
qed

lemma rm_reverse_iterateoi_impl_aux: "map_reverse_iterateoi RBT_Impl.lookup is_rbt RBT_add.rm_reverse_iterateoi"
proof
  fix m
  show "finite (dom (RBT_Impl.lookup m))" by simp
next
  fix m :: "('a, 'b) RBT_Impl.rbt" and I :: "'a set \<Rightarrow> 'c \<Rightarrow> bool" and \<sigma> c f
  assume inv: "is_rbt m"
    and I0: "I (dom (RBT_Impl.lookup m)) \<sigma>"
    and step: "\<And>k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; \<forall>j\<in>it. j \<le> k; RBT_Impl.lookup m k = Some v; it \<subseteq> dom (RBT_Impl.lookup m); I it \<sigma> \<rbrakk>
               \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"

  txt {* We define a shortcut for the invariant preservation property, 
    parameterized by the map and the overall set of keys *}
  def ipres == "\<lambda>m d. \<forall>\<sigma> k v it. 
      c \<sigma> \<longrightarrow> k \<in> it \<longrightarrow> (\<forall>j\<in>it. k\<ge>j) \<longrightarrow> RBT_Impl.lookup m k = Some v \<longrightarrow> it \<subseteq> d \<longrightarrow> I it \<sigma> \<longrightarrow> I (it - {k}) (f k v \<sigma>)"

  {
    txt {*
      First, we show an auxiliary lemma that allows us to 
      split up the invariant preservation property to subtrees
      *}
    fix col l k' v' r d
    assume A:
      "RBT_Impl.sorted (Branch col l k' v' r)"
      "ipres (Branch col l k' v' r) d"

    from A(1) have ST: "l |\<guillemotleft> k'" "k' \<guillemotleft>| r" "RBT_Impl.sorted l" "RBT_Impl.sorted r" 
      by simp_all

    have L: "ipres l d" unfolding ipres_def
    proof(intro strip)
      fix \<sigma> k v it
      assume P:
        "c \<sigma>" 
        "k\<in>it" 
        "RBT_Impl.lookup l k = Some v" 
        "it \<subseteq> d" 
        "I it \<sigma>"
        "\<forall>j\<in>it. k\<ge>j"

      from P(3) have "k\<in>set (RBT_Impl.keys l)" 
        by (auto simp add: lookup_keys[symmetric] ST(3))
      with ST(1) tree_less_prop have "k < k'" by auto
      with P(3) have "RBT_Impl.lookup (Branch col l k' v' r) k = Some v"
        by (simp)
      thus "I (it - {k}) (f k v \<sigma>)"
        using P(1,2,4,5,6) A(2) unfolding ipres_def by blast
    qed

    have R: "ipres r d" unfolding ipres_def
    proof(intro strip)
      fix \<sigma> k v it
      assume P:
        "c \<sigma>" 
        "k\<in>it" 
        "RBT_Impl.lookup r k = Some v" 
        "it \<subseteq> d" 
        "I it \<sigma>"
        "\<forall>j\<in>it. k\<ge>j"

      from P(3) have "k\<in>set (RBT_Impl.keys r)" 
        by (auto simp add: lookup_keys[symmetric] ST(4))
      with ST(2) tree_greater_prop have "k' < k" by auto
      with P(3) have "RBT_Impl.lookup (Branch col l k' v' r) k = Some v"
        by auto
      thus "I (it - {k}) (f k v \<sigma>)"
        using P(1,2,4,5,6) A(2) unfolding ipres_def by blast
    qed
        
    note L R
  } note ipres_split = this

  txt {* Next, we show a generalized goal, that fixes the domain of the 
    original map to @{text d}, and works for any set @{text it} of remaining
    keys, that is @{text \<supseteq>} the domain of the current map and @{text "\<subseteq> d"}.
    This generalization is required to get the induction through.
    *}
  { fix it d
    assume is_rbt: "is_rbt m"
      and rest: "I it \<sigma>" "ipres m d" "it \<supseteq> dom (RBT_Impl.lookup m)" "\<forall>k\<in>dom (RBT_Impl.lookup m). \<forall>k'\<in>it-dom (RBT_Impl.lookup m). k\<ge>k'" "it \<subseteq> d"
    from is_rbt have "RBT_Impl.sorted m" by(rule is_rbt_sorted)
    with rest 
    have "I (it - dom (RBT_Impl.lookup m)) (RBT_add.rm_reverse_iterateoi c f m \<sigma>) 
          \<or> (\<exists>it'\<subseteq>it. it' \<noteq> {} \<and> \<not> c (RBT_add.rm_reverse_iterateoi c f m \<sigma>)  
               \<and> I it' (RBT_add.rm_reverse_iterateoi c f m \<sigma>))"
    proof (induct m arbitrary: it \<sigma>)
      case Empty thus ?case by (simp)
    next
      case (Branch col m1 a b m2)
      show ?case
      proof(cases "c \<sigma>")
        case False
        txt {* If the condition does not hold initially, the 
          iterator will return the original state, and
          we are in the second case (interrupt) of our proposition: *}
        from Branch.prems(3) have "it\<noteq>{}" by auto
        with False show ?thesis
          by (simp del: RBT_Impl.lookup.simps add: exI[where x=it] Branch.prems(1))
      next
        case True
        note C = this

        txt {* If the condition holds, we descend into the right subtree *}

        txt {* The invariant preservation rule also holds for the left and 
          right subtree *}
        note IPR = ipres_split[OF Branch.prems(6,2)]

        txt {* Also the sorted tree properties can be transferred to the subtrees*}
        from Branch.prems(6) have ST: "m1 |\<guillemotleft> a" "a \<guillemotleft>| m2" "RBT_Impl.sorted m1" "RBT_Impl.sorted m2"
          by simp_all

        txt {* As @{term a} is the key of the original tree, the subtrees, 
          in particular the right one, does not contain @{term a}. 
          With @{thm Branch.prems(3)} we thus get:
          *}
        from Branch.prems(3,6) have DSS: "dom (RBT_Impl.lookup m2) \<subseteq> it"
          apply (simp only: lookup_keys ST)
          apply (auto simp add: tree_greater_prop tree_less_prop)
          done

        txt {* As the whole tree's domain is maximal in the remaining elements, the right subtree is also maximal *}
        from Branch.prems(3,4,6) have 
          MIN: "\<forall>k\<in>dom (RBT_Impl.lookup m2). \<forall>k'\<in>it - dom (RBT_Impl.lookup m2). k \<ge> k'"
          apply (simp only: lookup_keys ST)
          apply (intro ballI)
        proof -
          fix k k'
          assume A: 
            "set (RBT_Impl.keys (Branch col m1 a b m2)) \<subseteq> it" 
            "\<forall>k\<in>set (RBT_Impl.keys (Branch col m1 a b m2)). 
            \<forall>k'\<in>it - set (RBT_Impl.keys (Branch col m1 a b m2)). k \<ge> k'" 
            "RBT_Impl.sorted (Branch col m1 a b m2)" 
            "k \<in> set (RBT_Impl.keys m2)" 
            "k' \<in> it - set (RBT_Impl.keys m2)"
          {
            assume C: "k'\<in>set (RBT_Impl.keys m1)"
            with A(3,4) have "k\<ge>k'" 
              by (force simp add: tree_greater_prop tree_less_prop)
          } moreover {
            assume C: "k'=a"
            with A(3,4) have "k\<ge>k'" 
              by (force simp add: tree_greater_prop tree_less_prop)
          } moreover {
            assume C: "k'\<in> it - set (RBT_Impl.keys (Branch col m1 a b m2))"
            with A(2,4) have "k\<ge>k'" by auto
          } ultimately show "k\<ge>k'" using A(4,5) by auto
        qed
        
        txt {* Now we can apply the induction hypothesis for the right subtree: *}
        from Branch.prems(1) IPR(2) DSS MIN Branch.prems(5) ST(4)
        have
          "I (it - dom (RBT_Impl.lookup m2)) (RBT_add.rm_reverse_iterateoi c f m2 \<sigma>) 
          \<or> (\<exists>it'. it' \<subseteq> it \<and> it' \<noteq> {} 
                 \<and> \<not> c (RBT_add.rm_reverse_iterateoi c f m2 \<sigma>) 
                 \<and> I it' (RBT_add.rm_reverse_iterateoi c f m2 \<sigma>))"
          (is "?C1 \<or> ?C2")
          by(rule Branch)
        thus ?thesis
        proof
          txt {* Case: The iterator interrupted in the right subtree: *}
          assume ?C2
          then obtain it' where 
            "it'\<subseteq>it" 
            "it'\<noteq>{}" 
            "\<not>c (RBT_add.rm_reverse_iterateoi c f m2 \<sigma>)" 
            "I it' (RBT_add.rm_reverse_iterateoi c f m2 \<sigma>)"
            by auto
          thus ?thesis using C by(auto)
        next
          txt {* Case: The iterator completely finished the right subtree: *}
          assume C1: ?C1
          let ?\<sigma>' = "(RBT_add.rm_reverse_iterateoi c f m2 \<sigma>)"
          let ?it' = "(it - dom (RBT_Impl.lookup m2))"
          txt {* In this case, we have to check whether the condition still holds *}
          show ?thesis
          proof (cases "c ?\<sigma>'")
            case False 
            txt {* The iterator will interrupt right here *}
            from Branch.prems(3,6) have ITGM1: "\<not> it \<subseteq> dom (RBT_Impl.lookup m2)"
              apply (simp only: lookup_keys ST)
              apply (auto simp add: tree_greater_prop tree_less_prop)
              done
            thus ?thesis using False C C1 by(auto intro!: exI[where x="?it'"])
          next
            case True
            txt {* The iterator will continue with the current node's single-step and the left subtree *}

            txt {* The root node is the largest remaining element *}
            have AMIN: "\<forall>k\<in>?it'. a\<ge>k" 
            proof (intro ballI)
              fix k
              assume A: "k\<in>it - dom (RBT_Impl.lookup m2)"
              show "a \<ge> k"
              proof(cases "k\<in>dom (RBT_Impl.lookup (Branch col m1 a b m2))")
                case False
                with A Branch.prems(4)[rule_format, of a k] show "a\<ge>k" by force
              next
                case True
                with A have "k\<in>set (RBT_Impl.keys m1) \<or> a=k"
                  apply (simp only: lookup_keys ST Branch.prems(6))
                  apply auto
                  done
                with ST show "a\<ge>k" by (auto simp add: tree_greater_prop tree_less_prop)
              qed
            qed

            txt {* The invariant is preserved over the single-step with the root-node's data *}
            from True have I': "I (?it' - {a}) (f a b ?\<sigma>')" using Branch.prems
              apply (rule_tac Branch.prems(2)[unfolded ipres_def, rule_format])
              apply (simp_all only: C1)
              apply (auto simp add: C AMIN)
              done
          
            have RMIN: "\<forall>k\<in>dom (RBT_Impl.lookup m1). 
                    \<forall>a\<in>it - dom (RBT_Impl.lookup m2) - {a} - dom (RBT_Impl.lookup m1). 
                      k \<ge> a"
              using Branch.prems(4)
              apply (simp only: lookup_keys ST Branch.prems(6))
              apply auto
              done

            from Branch.prems(3,6) have 
              DSS: "dom (RBT_Impl.lookup m1) \<subseteq> ?it' - {a}"
              apply (simp only: lookup_keys ST)
              apply (force simp add: tree_greater_prop tree_less_prop)
              done

            from Branch.prems(5) have IMAS: "?it' - {a} \<subseteq> d" by auto

            txt {* Finally, we can apply the induction hypothesis on the iteration over
              the left subtree, and get two cases: Ordinary termination or interrupt.*}
            from Branch.hyps(1)[OF I' IPR(1) DSS RMIN IMAS ST(3)] have
              "I (?it' - {a} - dom (RBT_Impl.lookup m1)) (RBT_add.rm_reverse_iterateoi c f m1 (f a b ?\<sigma>')) \<or>
              (\<exists>it'. it' \<subseteq> ?it' - {a} \<and> it' \<noteq> {} \<and> \<not> c (RBT_add.rm_reverse_iterateoi c f m1 (f a b ?\<sigma>')) \<and> I it' (RBT_add.rm_reverse_iterateoi c f m1 (f a b ?\<sigma>')))"
              .

            thus ?thesis using C True
              apply (simp only: dom_lookup_Branch[OF Branch.prems(6)])
              apply (simp add: Diff_insert2[symmetric] set_diff_diff_left Un_commute)
              apply auto
              done
          qed
        qed
      qed
    qed }
  note G = this

  txt {* Finally, we derive the original goal from the generalized one.*}
  from step have IPR: "ipres m (dom (RBT_Impl.lookup m))"
    by (unfold ipres_def) auto
  from G[OF inv I0 IPR]
  show "I {} (RBT_add.rm_reverse_iterateoi c f m \<sigma>) \<or>
        (\<exists>it \<subseteq> dom (RBT_Impl.lookup m). it \<noteq> {} \<and> \<not> c (RBT_add.rm_reverse_iterateoi c f m \<sigma>) \<and>
             I it (RBT_add.rm_reverse_iterateoi c f m \<sigma>))"
    by auto
qed

lemma rm_reverse_iterateoi_impl: "map_reverse_iterateoi rm_\<alpha> rm_invar rm_reverse_iterateoi"
proof
  fix m
  show "finite (dom (rm_\<alpha> m))" by simp
next
  fix m :: "('a, 'b) rm" and I :: "'a set \<Rightarrow> 'c \<Rightarrow> bool" and \<sigma>0 c f
  assume "I (dom (rm_\<alpha> m)) \<sigma>0"
    and "\<And>k v it \<sigma>. \<lbrakk>c \<sigma>; k \<in> it; \<forall>j\<in>it. j \<le> k; rm_\<alpha> m k = Some v; it \<subseteq> dom (rm_\<alpha> m); I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  with is_rbt_impl_of
  show "I {} (rm_reverse_iterateoi c f m \<sigma>0) \<or>
        (\<exists>it\<subseteq>dom (rm_\<alpha> m). it \<noteq> {} \<and> \<not> c (rm_reverse_iterateoi c f m \<sigma>0) \<and> I it (rm_reverse_iterateoi c f m \<sigma>0))"
    unfolding rm_\<alpha>_def RBT.lookup_def rm_reverse_iterateoi_def
    by(rule map_reverse_iterateoi.reverse_iterateoi_rule[OF rm_reverse_iterateoi_impl_aux])
qed

lemmas rm_iterateo_impl = 
  map_iterateoi.itoi_iterateo_correct[OF rm_iterateoi_impl, 
                                         folded rm_iterateo_def]
lemmas rm_reverse_iterateo_impl = 
  map_reverse_iterateoi.itoi_reverse_iterateo_correct[OF 
    rm_reverse_iterateoi_impl, folded rm_reverse_iterateo_def]

lemmas rm_iteratei_impl =
  MapGA.iti_by_itoi[OF rm_iterateoi_impl, folded rm_iteratei_def]

lemmas rm_iterate_impl =
  MapGA.it_by_ito[OF rm_iterateo_impl, folded rm_iterate_def]

lemmas rm_add_impl = 
  it_add_correct[OF rm_iterate_impl rm_update_impl, folded rm_add_def]

lemmas rm_add_dj_impl =  
  map_add.add_dj_by_add[OF rm_add_impl, folded rm_add_dj_def]

lemma rm_isEmpty_impl: "map_isEmpty rm_\<alpha> rm_invar rm_isEmpty"
  apply (unfold_locales)
  apply (unfold rm_defs)
  apply (case_tac m)
  apply simp
  done

lemmas rm_sel_impl = iti_sel_correct[OF rm_iteratei_impl, folded rm_sel_def]
lemmas rm_sel'_impl = sel_sel'_correct[OF rm_sel_impl, folded rm_sel'_def]

lemmas rm_ball_impl = sel_ball_correct[OF rm_sel_impl, folded rm_ball_def]

lemmas rm_to_sorted_list_impl 
  = rito_map_to_sorted_list_correct[OF rm_reverse_iterateo_impl, folded rm_to_list_def]

lemmas list_to_rm_impl
  = gen_list_to_map_correct[OF rm_empty_impl rm_update_impl, 
                            folded list_to_rm_def]

lemmas rm_sng_correct 
  = map_sng_correct[OF rm_empty_impl rm_update_impl, folded rm_sng_def]

lemmas rm_min_impl = MapGA.itoi_min_correct[OF rm_iterateoi_impl, folded rm_min_def]
lemmas rm_max_impl = MapGA.ritoi_max_correct[OF rm_reverse_iterateoi_impl, folded rm_max_def]


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
interpretation rm: map_iterateoi rm_\<alpha> rm_invar rm_iterateoi
  using rm_iterateoi_impl .
interpretation rm: map_reverse_iterateoi rm_\<alpha> rm_invar rm_reverse_iterateoi
  using rm_reverse_iterateoi_impl .
interpretation rm: map_iterateo rm_\<alpha> rm_invar rm_iterateo
  using rm_iterateo_impl .
interpretation rm: map_reverse_iterateo rm_\<alpha> rm_invar rm_reverse_iterateo
  using rm_reverse_iterateo_impl .
interpretation rm: map_add rm_\<alpha> rm_invar rm_add 
  using rm_add_impl .
interpretation rm: map_add_dj rm_\<alpha> rm_invar rm_add_dj 
  using rm_add_dj_impl .
interpretation rm: map_isEmpty rm_\<alpha> rm_invar rm_isEmpty 
  using rm_isEmpty_impl .
interpretation rm: map_sel rm_\<alpha> rm_invar rm_sel 
  using rm_sel_impl .
interpretation rm: map_sel' rm_\<alpha> rm_invar rm_sel' 
  using rm_sel'_impl .
interpretation rm: map_ball rm_\<alpha> rm_invar rm_ball 
  using rm_ball_impl .
interpretation rm: map_to_sorted_list rm_\<alpha> rm_invar rm_to_list 
  using rm_to_sorted_list_impl .
interpretation rm: list_to_map rm_\<alpha> rm_invar list_to_rm 
  using list_to_rm_impl . 

interpretation rm: map_min rm_\<alpha> rm_invar rm_min 
  using rm_min_impl .
interpretation rm: map_max rm_\<alpha> rm_invar rm_max 
  using rm_max_impl .

declare rm.finite[simp del, rule del]

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
  rm_iterateoi
  rm_reverse_iterateoi
  rm_iterateo
  rm_reverse_iterateo
  rm_add
  rm_add_dj
  rm_isEmpty
  rm_sel
  rm_sel'
  rm_ball
  rm_to_list
  list_to_rm
  rm_sng
  rm_min
  rm_max
  in SML
  module_name RBTMap
  file -

end

