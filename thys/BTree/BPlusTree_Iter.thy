theory BPlusTree_Iter
  imports
    BPlusTree_Imp
    "HOL-Real_Asymp.Inst_Existentials"
    "Separation_Logic_Imperative_HOL.Imp_List_Spec"
    Flatten_Iter_Spec
    Partially_Filled_Array_Iter
    Subst_Mod_Mult_AC
begin


(* TODO use list_zip? \<rightarrow> not well defined return type *)

fun bplustree_assn_leafs :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref list \<Rightarrow> assn" where
  "bplustree_assn_leafs k (Leaf xs) a r z leafptrs = 
 (\<exists>\<^sub>A xsi fwd.
      a \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xs xsi
    * \<up>(fwd = z)
    * \<up>(r = Some a)
    * \<up>(leafptrs = [a])
  )" |
  "bplustree_assn_leafs k (Node ts t) a r z leafptrs = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs split.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn_leafs k t ti (last (r#rs)) (last (rs@[z])) (last split)
    * is_pfa (2*k) tsi' tsi
    * \<up>(concat split = leafptrs)
    * \<up>(length tsi' = length rs)
    * \<up>(length split = length rs + 1)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (zip (butlast (rs@[z])) (butlast split)))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z',lptrs). bplustree_assn_leafs k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn) ts tsi''
    )"

(*fun make_list_list where "make_list_list xs = [xs]"

lemma make_list_list_concat: "concat (make_list_list ys) = ys"
  by auto

lemma ex_concat: "\<exists>xs. concat xs = ys"
  using make_list_list_concat by blast*)

lemma inst_same: "(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>\<^sub>A x. P x) = (\<exists>\<^sub>A x. Q x)"
  by simp


lemma reorder_ex: 
  "\<And>z. (\<exists>\<^sub>Aa b c d e f g. z a b c d e f g) = (\<exists>\<^sub>Ab c d e f a g. z a b c d e f g)"
  "\<And>z. (\<exists>\<^sub>Aa b . z a b) = (\<exists>\<^sub>Ab a. z a b)"
  "\<And>z. (\<exists>\<^sub>Aa b c d. z a b c d) = (\<exists>\<^sub>Ab c a d. z a b c d)"
  apply(intro ent_iffI; sep_auto)+
  done

lemma inst_same2: "(\<And>x. P = Q x) \<Longrightarrow> P = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma pure_eq_pre:
 "(P \<Longrightarrow> Q = R) \<Longrightarrow> (Q * \<up>P = R * \<up>P)"
  by fastforce


lemma otf_lem_comm_ex:
"\<And>a b c d e f g. (\<exists>\<^sub>A x. a * b x * c * d x * e x * f x * g x) = a * c * (\<exists>\<^sub>A x.  b x * d x * e x * f x * g x)"
"\<And>a b c d e. (\<exists>\<^sub>Aaa x. a * b x * c * d aa * e aa) = (a * c * (\<exists>\<^sub>A aa x. b x * d aa * e aa))"
"\<And>b d e. (\<exists>\<^sub>A aa x. b x * d aa * e aa) = (\<exists>\<^sub>A x. b x) * (\<exists>\<^sub>A aa. d aa * e aa)"
  by (auto simp add: algebra_simps)

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_extract_leafs:
 "bplustree_assn k t ti r z = (\<exists>\<^sub>Aleafptrs. bplustree_assn_leafs k t ti r z leafptrs)"
proof(induction arbitrary: r rule: bplustree_assn.induct )
  case (1 k xs a r z)
  then show ?case
  (*apply auto*)
    apply (rule ent_iffI)
    subgoal
      apply(inst_ex_assn "[a]")
      apply sep_auto
      done
    subgoal
      apply(rule ent_ex_preI)
      apply clarsimp
      apply(rule ent_ex_preI)+
      subgoal for x xsi fwd
      apply(inst_ex_assn xsi fwd)
        apply simp
        done
      done
    done
next
  case Istep: (2 k ts t a r z)
  show ?case
    apply(simp (no_asm))
    thm bplustree_assn_leafs.simps(2)
    apply(subst reorder_ex(1))
    apply(intro inst_same)
    thm reorder_ex(2)
    apply(subst reorder_ex(2))
    apply(subst reorder_ex(3))
    apply(rule inst_same)
(* pre-massage term for an explicit treatment. ignore inductive assumptions in simp s.t.
bplustree of the last tree does not get simplified away immediately *)
  proof(goal_cases)
    case (1 tsi ti tsi' rs)
    have *: "
        length tsi's = length tss \<Longrightarrow>
        length tss = length rss \<Longrightarrow>
        set tsi's \<subseteq> set tsi' \<Longrightarrow>
        set rss \<subseteq> set rs \<Longrightarrow>
        set tss \<subseteq> set ts \<Longrightarrow>
       blist_assn k tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) =
       (\<exists>\<^sub>Asplit. list_assn ((\<lambda> t (ti,r',z',lptrs). bplustree_assn_leafs k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn) tss 
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss split))) (separators tsi's)) *
        \<up>(length split = length rss))"
      for rss tsi's tss ra
    proof (induct arbitrary: ra rule: list_induct3)
      case Nil
      then show ?case
        apply sep_auto
        apply(subst ex_one_point_gen[where v="[]"])
        apply simp_all
        done
    next
    case (Cons subsepi tsi's subsep tss subleaf rss r)
      then show ?case 
        apply (auto simp add: butlast_double_Cons last_double_Cons)
        apply(auto simp add: prod_assn_def split: prod.splits)
      proof(goal_cases)
        case (1 sub sep)
        then have *: "bplustree_assn k sub (the (fst subsepi)) r subleaf = (\<exists>\<^sub>As. bplustree_assn_leafs k sub (the (fst subsepi)) r subleaf s)"
        proof -
          have "subsep \<in> set ts"
            by (simp add: "1"(10) "1"(8))
          moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
            by auto
          ultimately  show ?thesis
            using Istep(2)[of "(sub,sep)" "((fst subsepi, temp1, subleaf), temp2)" "[((fst subsepi, temp1, subleaf), temp2)]" "fst subsepi" "(temp1, subleaf)" temp1 subleaf r]
            using 1
            by simp
        qed
        show ?case
          apply (simp add: * 1(3)[of subleaf])
          apply(intro ent_iffI)
          subgoal
            apply(intro ent_ex_preI)
            subgoal for split x
            apply(inst_ex_assn "x#split")
              apply simp
              done
            done
          subgoal
            apply(intro ent_ex_preI)
            subgoal for split
              apply(cases split)
              apply simp
            subgoal for hdsplit tlsplit
            apply(inst_ex_assn "tlsplit" "hdsplit")
              apply (auto)
            done
          done
        done
      done
     qed
  qed
  have **: "bplustree_assn k t ti (last (r # rs)) z = (\<exists>\<^sub>Alsplit. bplustree_assn_leafs k t ti (last (r # rs)) z lsplit)" 
    using Istep(1)[of ti "last(r #rs)" "[]"]
    by (auto simp add: last.simps)
  show ?case
(* apply IH to last tree *)
    apply(subst **)
    apply(simp add: inst_same[OF bplustree_assn_leafs.simps(2)])
  proof(intro ent_iffI, goal_cases)
    case _: (1)
    show ?case
(* apply IH to list via rule just shown *)
    apply(rule entails_preI)
      apply(intro ent_ex_preI)
      apply(clarsimp dest!: mod_starD list_assn_len)
      apply (subst *[of tsi' ts rs])
    apply simp_all
(* show that the remainder is equivalent *)
      apply(intro ent_ex_preI)
    apply(rule entails_preI)
      apply(clarsimp dest!: mod_starD list_assn_len)
      subgoal for lsplit _ _ _ _ _ _ _ split
        find_theorems "\<exists>\<^sub>A_._"
      apply(inst_ex_assn "concat (split@[lsplit])" "zip (zip (subtrees tsi') (zip (butlast (r # rs)) (zip rs (butlast (split@[lsplit])))))
           (separators tsi')"  "split@[lsplit]")
        apply (sep_auto simp add: last.simps butlast.simps)
      done
    done
  next
  case _: (2)
  show ?case
(* apply IH to list via rule just shown (other direction) *)
    apply(rule entails_preI)
      apply(rule ent_ex_preI)
      apply(rule ent_ex_preI)
      apply(clarsimp dest!: mod_starD list_assn_len)
  apply(subst merge_pure_star[symmetric] mult.left_assoc)+
  apply(subst otf_lem_comm_ex)+
  apply(rule ent_star_mono)
  subgoal by sep_auto
proof(goal_cases) 
  case (1 c aa d ae bd af be ag bf)
  have **: "(\<exists>\<^sub>Ax. bplustree_assn_leafs k t ti (last (r # rs)) z (last x) *
              list_assn
               ((\<lambda>t (ti, r', x, y). bplustree_assn_leafs k t (the ti) r' x y) \<times>\<^sub>a id_assn)
               ts aa *
              \<up> (concat x = c) *
              \<up> (length x = Suc (length rs)) *
              \<up> (aa =
                 zip (zip (subtrees tsi') (zip (butlast (r # rs)) (zip rs (butlast x))))
                  (separators tsi'))) \<Longrightarrow>\<^sub>A ((\<exists>\<^sub>Asplit. list_assn ((\<lambda>t (ti, r', x, y). bplustree_assn_leafs k t (the ti) r' x y) \<times>\<^sub>a id_assn) ts (zip (zip (subtrees tsi') (zip (butlast (r # rs)) (zip rs split))) (separators tsi')) *
                  \<up> (length split = length rs)) * (\<exists>\<^sub>Alsplit. bplustree_assn_leafs k t ti (last (r # rs)) z lsplit) 
)"
    using 1 by sep_auto
  from ** show ?case
    apply(rule ent_trans)
    apply(subst mult.commute[of "ex_assn (bplustree_assn_leafs k t ti (last (r # rs)) z)"])
  apply(rule ent_star_mono)
    prefer 2
    subgoal by sep_auto
        subgoal
          apply(subst *[of tsi' ts rs r, symmetric])
          apply(simp_all add: 1)
          apply sep_auto
          done
        done
    qed
  qed
qed
qed
declare last.simps[simp add] butlast.simps[simp add]

(* even without the existential quantifier, we get our general assertion, used in insertion etc back*)
lemma bplustree_discard_leafs:
 "bplustree_assn_leafs k t ti r z leafptrs \<Longrightarrow>\<^sub>A bplustree_assn k t ti r z"
  by (simp add: bplustree_extract_leafs)


fun leaf_nodes_assn :: "nat \<Rightarrow> ('a::heap) bplustree list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref list \<Rightarrow> assn" where
  "leaf_nodes_assn k ((Leaf xs)#lns) (Some r) z (r'#lptrs) = 
 (\<exists>\<^sub>A xsi fwd.
      r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xs xsi
    * leaf_nodes_assn k lns fwd z lptrs
    * \<up>(r = r')
  )" | 
  "leaf_nodes_assn k [] r z [] = \<up>(r = z)" |
  "leaf_nodes_assn _ _ _ _ _ = false"


fun trunk_assn :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref list \<Rightarrow> assn" where
  "trunk_assn k (Leaf xs) a r z lptrs = \<up>(r = Some a \<and> lptrs = [a])" |
  "trunk_assn k (Node ts t) a r z lptrs = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs split.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * trunk_assn k t ti (last (r#rs)) (last (rs@[z])) (last split)
    * is_pfa (2*k) tsi' tsi
    * \<up>(concat split = lptrs)
    * \<up>(length tsi' = length rs)
    * \<up>(length split = length rs + 1)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (zip (butlast (rs@[z])) (butlast split)))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z',lptrs). trunk_assn k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn) ts tsi''
    )"

lemma leaf_nodes_assn_split:
"length xs = length xsi \<Longrightarrow> ysi = (yi#ysr) \<Longrightarrow>
  leaf_nodes_assn k (xs @ ys) r z (xsi @ ysi) = leaf_nodes_assn k xs r (Some yi) xsi * leaf_nodes_assn k ys (Some yi) z ysi"
proof(induction arbitrary: r rule: list_induct2)
  case (Nil r)
  then show ?case
    apply(cases r; cases ys)
    apply clarsimp_all
    subgoal for _ t _
    apply(cases t)
    apply clarsimp
      apply(intro inst_same)
      apply(rule pure_eq_pre)
      apply clarsimp_all
      done
    done
next
  case (Cons x xs xi xsi r)
  show ?case
    apply(cases r; cases x)
    apply clarsimp_all
      apply(intro inst_same)
      apply(rule pure_eq_pre)
      subgoal for a x1 xsi' fwd
      using Cons.IH[of fwd, OF Cons.prems]
      apply (clarsimp simp add: mult.assoc)
      done
    done
qed

lemma "length xs \<noteq> length xsi \<Longrightarrow> leaf_nodes_assn k xs r z xsi = false"
  by (induction rule: leaf_nodes_assn.induct) auto

lemma imp_eq_pure: "(\<forall>h. h \<Turnstile> P \<longrightarrow> Q) = (P = P * \<up>(Q))"
  apply(intro iffI)
  subgoal using ent_iffI by force
  subgoal by (metis mod_pure_star_dist)
  done

lemma imp_imp_pure: "(\<And>h. h \<Turnstile> P \<Longrightarrow> Q) \<Longrightarrow> (P = P * \<up>(Q))"
  using imp_eq_pure by blast

thm concat_append
lemma concat_append_butlast: "xs \<noteq> [] \<Longrightarrow> concat (butlast xs) @ last xs = concat xs"
  apply(induction xs)
  apply auto
  done

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_assn_leafs_len_imp: "h \<Turnstile> bplustree_assn_leafs k t a r z leafptrs \<Longrightarrow> length leafptrs = length (leaf_nodes t)"  
proof(induction k t a r z leafptrs arbitrary: h rule: bplustree_assn_leafs.induct)
  case (1 k xs a r z leafptrs)
  then show ?case
    by(clarsimp)
next
  case (2 k ts t a r z leafptrs h)
  from "2.prems" show ?case
    apply(sep_auto)
  proof(goal_cases)
    case (1 tsia tsin ti tsi' rs split)
    have *: "
length tss = length splits \<Longrightarrow>
length splits = length tsi's \<Longrightarrow>
length tsi's = length rss \<Longrightarrow>
set tss \<subseteq> set ts \<Longrightarrow> 
set tsi's \<subseteq> set tsi' \<Longrightarrow> 
set rss \<subseteq> set rs \<Longrightarrow> 
h \<Turnstile> list_assn
        ((\<lambda>t (ti, r', x, y). bplustree_assn_leafs k t (the ti) r' x y) \<times>\<^sub>a id_assn) tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss splits))) (separators tsi's))
\<Longrightarrow> (length (concat splits)) = length (concat (map (leaf_nodes \<circ> fst) tss))" for h tss tsi's splits rss ra
    proof(induction arbitrary: ra h rule: list_induct4)
      case Nil
      then show ?case
        by sep_auto
    next
      case (Cons x xs y ys z zs w ws)
      from Cons.prems show ?case
        apply (auto simp add: butlast_double_Cons last_double_Cons)
        apply(auto simp add: prod_assn_def split: prod.splits)
        apply(auto dest!: mod_starD)
      using Cons.IH
        apply(auto)
      using "2.IH"(2)
      apply sep_auto
      by (meson list.set_intros(1))
    qed
    have **: "length ts = length rs" "split \<noteq> []"
      using 1 by (auto dest!: mod_starD list_assn_len)
    from 1 show ?case
      apply(auto dest!: mod_starD)
      apply(subst concat_append_butlast[symmetric])
      subgoal using ** by sep_auto
      subgoal for h1 h2 h3 h4 h5 h6 h7 h8
      using *[of ts "butlast split" tsi' rs r "(h1,h2)"] "2.IH"(1)[of ti rs split "(h7,h8)"]
      using **
      by sep_auto
    done
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]

lemma bplustree_assn_leafs_len_aux: "bplustree_assn_leafs k t a r z leafptrs = bplustree_assn_leafs k t a r z leafptrs * \<up>(length leafptrs = length (leaf_nodes t))"  
  by (meson bplustree_assn_leafs_len_imp imp_imp_pure)

declare last.simps[simp del] butlast.simps[simp del]
lemma trunk_assn_leafs_len_imp: "h \<Turnstile> trunk_assn k t a r z leafptrs \<Longrightarrow> length leafptrs = length (leaf_nodes t)"  
(* same procedure as for bplustree_nodes_assn_leaf *)
proof(induction k t a r z leafptrs arbitrary: h rule: trunk_assn.induct)
  case (1 k xs a r z leafptrs)
  then show ?case
    by(clarsimp)
next
  case (2 k ts t a r z leafptrs h)
  from "2.prems" show ?case
    apply(sep_auto)
  proof(goal_cases)
    case (1 tsia tsin ti tsi' rs split)
    have *: "
length tss = length splits \<Longrightarrow>
length splits = length tsi's \<Longrightarrow>
length tsi's = length rss \<Longrightarrow>
set tss \<subseteq> set ts \<Longrightarrow> 
set tsi's \<subseteq> set tsi' \<Longrightarrow> 
set rss \<subseteq> set rs \<Longrightarrow> 
h \<Turnstile> list_assn
        ((\<lambda>t (ti, r', x, y). trunk_assn k t (the ti) r' x y) \<times>\<^sub>a id_assn) tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss splits))) (separators tsi's))
\<Longrightarrow> (length (concat splits)) = length (concat (map (leaf_nodes \<circ> fst) tss))" for h tss tsi's splits rss ra
    proof(induction arbitrary: ra h rule: list_induct4)
      case Nil
      then show ?case
        by sep_auto
    next
      case (Cons x xs y ys z zs w ws)
      from Cons.prems show ?case
        apply (auto simp add: butlast_double_Cons last_double_Cons)
        apply(auto simp add: prod_assn_def split: prod.splits)
        apply(auto dest!: mod_starD)
      using Cons.IH
        apply(auto)
      using "2.IH"(2)
      apply sep_auto
      by (meson list.set_intros(1))
    qed
    have **: "length ts = length rs" "split \<noteq> []"
      using 1 by (auto dest!: mod_starD list_assn_len)
    from 1 show ?case
      apply(auto dest!: mod_starD)
      apply(subst concat_append_butlast[symmetric])
      subgoal using ** by sep_auto
      subgoal for h1 h2 h3 h4 h5 h6 h7 h8
      using *[of ts "butlast split" tsi' rs r "(h1,h2)"] "2.IH"(1)[of ti rs split "(h7,h8)"]
      using **
      by sep_auto
    done
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]

lemma trunk_assn_leafs_len_aux: "trunk_assn k t a r z leafptrs = trunk_assn k t a r z leafptrs * \<up>(length leafptrs = length (leaf_nodes t))"  
  by (meson trunk_assn_leafs_len_imp imp_imp_pure)

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_assn_leafs_not_empty_aux: "bplustree_assn_leafs k t a r z leafptrs = bplustree_assn_leafs k t a r z leafptrs * \<up>(leafptrs \<noteq> [])"
  apply(intro ent_iffI)
  subgoal 
    apply(subst bplustree_assn_leafs_len_aux)
    using leaf_nodes_not_empty
    apply sep_auto
  done
  subgoal by sep_auto
  done

lemma trunk_assn_not_empty_aux: "trunk_assn k t a r z leafptrs = trunk_assn k t a r z leafptrs * \<up>(leafptrs \<noteq> [])"
  apply(intro ent_iffI)
  subgoal 
    apply(subst trunk_assn_leafs_len_aux)
    using leaf_nodes_not_empty
    apply sep_auto
  done
  subgoal by sep_auto
  done
declare last.simps[simp add] butlast.simps[simp add]

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_assn_leafs_hd:
  "h \<Turnstile> bplustree_assn_leafs k t a r z leafptrs \<Longrightarrow> r = Some (hd leafptrs)"  
proof(induction k t a r z leafptrs arbitrary: h rule: bplustree_assn_leafs.induct)
  case (1 k xs a r z leafptrs)
  then show ?case
    by(clarsimp)
next
  case (2 k ts t a r z leafptrs h)
  from "2.prems" show ?case
    apply(sep_auto dest!: mod_starD)
  proof(goal_cases)
    case (1 a b ti tsi' rs split ab bb ad bd ae be af bf)
    have  "length ts = length rs"
      using 1 by (auto dest!: list_assn_len)
    then show ?case
    proof(cases ts)
      case Nil
      then have "length split = 1" "rs = []"
        using "1"(4) \<open>length ts = length rs\<close> by auto
      then have *: "split = [last split]"
        by (metis append_butlast_last_id list.distinct(1) list_decomp_1 list_se_match(4))
      then have "concat split = last split"
        apply(subst *)
        unfolding concat.simps 
        by simp
      then show ?thesis
        using 1
        using "2.IH"(1)[of ti rs split "(af,bf)"] 
        using \<open>rs = []\<close>
        by (auto simp add: last.simps)
    next
      case (Cons a list)
      then obtain ra rss ss1 ss2 splits tss tsi's  where *:
        "rs = ra#rss"
        "split = ss1 # ss2 # splits"
        "tsi' = tss # tsi's"
        by (metis (no_types, lifting) "1"(3) "1"(4) Suc_length_conv \<open>length ts = length rs\<close>)
      obtain h1 h2 where first_subtree: "(h1, h2) \<Turnstile> bplustree_assn_leafs k (fst a) (the (fst tss)) r ra ss1"
        using 1 
        apply (auto simp add: butlast_double_Cons last_double_Cons * Cons)
        apply (auto simp add: prod_assn_def split: prod.splits )
        apply(auto dest!: mod_starD)
        done
      then have "ss1 \<noteq> []"
        using bplustree_assn_leafs_not_empty_aux[of k "(fst a)" "(the (fst tss))" r ra ss1] 
        by auto
      then have "hd (concat split) = hd ss1"
        by (simp add: "*"(2))
      then show ?thesis 
        using first_subtree
        apply auto
        by (metis "2.IH"(2) fst_conv list.set_intros(1) local.Cons)
    qed
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]

lemma bplustree_assn_leafs_hd_aux:
  "bplustree_assn_leafs k t a r z leafptrs = bplustree_assn_leafs k t a r z leafptrs * \<up>(r = Some (hd leafptrs))"  
  by (meson bplustree_assn_leafs_hd imp_imp_pure)

declare last.simps[simp del] butlast.simps[simp del]
lemma trunk_assn_hd:
  "h \<Turnstile> trunk_assn k t a r z leafptrs \<Longrightarrow> r = Some (hd leafptrs)"  
proof(induction k t a r z leafptrs arbitrary: h rule: trunk_assn.induct)
  case (1 k xs a r z leafptrs)
  then show ?case
    by(clarsimp)
next
  case (2 k ts t a r z leafptrs h)
  from "2.prems" show ?case
    apply(sep_auto dest!: mod_starD)
  proof(goal_cases)
    case (1 a b ti tsi' rs split ab bb ad bd ae be af bf)
    have  "length ts = length rs"
      using 1 by (auto dest!: list_assn_len)
    then show ?case
    proof(cases ts)
      case Nil
      then have "length split = 1" "rs = []"
        using "1"(4) \<open>length ts = length rs\<close> by auto
      then have *: "split = [last split]"
        by (metis append_butlast_last_id list.distinct(1) list_decomp_1 list_se_match(4))
      then have "concat split = last split"
        apply(subst *)
        unfolding concat.simps 
        by simp
      then show ?thesis
        using 1
        using "2.IH"(1)[of ti rs split "(af,bf)"] 
        using \<open>rs = []\<close>
        by (auto simp add: last.simps)
    next
      case (Cons a list)
      then obtain ra rss ss1 ss2 splits tss tsi's  where *:
        "rs = ra#rss"
        "split = ss1 # ss2 # splits"
        "tsi' = tss # tsi's"
        by (metis (no_types, lifting) "1"(3) "1"(4) Suc_length_conv \<open>length ts = length rs\<close>)
      obtain h1 h2 where first_subtree: "(h1, h2) \<Turnstile> trunk_assn k (fst a) (the (fst tss)) r ra ss1"
        using 1 
        apply (auto simp add: butlast_double_Cons last_double_Cons * Cons)
        apply (auto simp add: prod_assn_def split: prod.splits )
        apply(auto dest!: mod_starD)
        done
      then have "ss1 \<noteq> []"
        using trunk_assn_not_empty_aux[of k "(fst a)" "(the (fst tss))" r ra ss1] 
        by auto
      then have "hd (concat split) = hd ss1"
        by (simp add: "*"(2))
      then show ?thesis 
        using first_subtree
        apply auto
        by (metis "2.IH"(2) fst_conv list.set_intros(1) local.Cons)
    qed
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]

lemma trunk_assn_hd_aux:
  "trunk_assn k t a r z leafptrs = trunk_assn k t a r z leafptrs * \<up>(r = Some (hd leafptrs))"  
  by (simp add: imp_imp_pure trunk_assn_hd)

declare last.simps[simp del] butlast.simps[simp del]
lemma subleaf_at_head_of_concat_inner: "length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        length tss = length splits \<Longrightarrow>
list_assn ((\<lambda>t (ti, x, xa, y). trunk_assn k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    trunk_assn k t ti (last (subleaf # rss)) z ss
= 
list_assn ((\<lambda>t (ti, x, xa, y). trunk_assn k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    trunk_assn k t ti (last (subleaf # rss)) z ss * \<up>(Some (hd (concat splits@ss)) = subleaf)"
  apply(cases splits)
  subgoal
    apply (sep_auto simp add: last.simps)
    apply (metis (mono_tags, opaque_lifting) trunk_assn_hd_aux pure_assn_eq_conv)
    done
  subgoal
  apply(cases tss; cases rss; cases tsi's)
  apply simp_all
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
  apply(intro ent_iffI)
    subgoal
      apply(subst trunk_assn_hd_aux)
      apply(subst trunk_assn_not_empty_aux)
      apply sep_auto
      done
    subgoal by sep_auto
    done
  done

lemma subleaf_at_head_of_concat_bplustree: "length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        length tss = length splits \<Longrightarrow>
list_assn ((\<lambda>t (ti, x, xa, y). bplustree_assn_leafs k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    bplustree_assn_leafs k t ti (last (subleaf # rss)) z ss
= 
list_assn ((\<lambda>t (ti, x, xa, y). bplustree_assn_leafs k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    bplustree_assn_leafs k t ti (last (subleaf # rss)) z ss * \<up>(Some (hd (concat splits@ss)) = subleaf)"
  apply(cases splits)
  subgoal
    apply (sep_auto simp add: last.simps)
    apply (metis (mono_tags, opaque_lifting) bplustree_assn_leafs_hd_aux pure_assn_eq_conv)
    done
  subgoal
  apply(cases tss; cases rss; cases tsi's)
  apply simp_all
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
  apply(intro ent_iffI)
    subgoal
      apply(subst bplustree_assn_leafs_hd_aux)
      apply(subst bplustree_assn_leafs_not_empty_aux)
      apply sep_auto
      done
    subgoal by sep_auto
    done
  done
declare last.simps[simp add] butlast.simps[simp add]


declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_leaf_nodes_sep:
  "bplustree_assn_leafs k t ti r z lptrs = leaf_nodes_assn k (leaf_nodes t) r z lptrs * trunk_assn k t ti r z lptrs"
proof(induction arbitrary: r rule: bplustree_assn_leafs.induct)
  case (1 k xs a r z)
  then show ?case
    apply(intro ent_iffI)
    apply sep_auto+
    done
next
  case (2 k ts t a r z lptrs ra)
  show ?case
      apply simp
    apply(intro inst_same)
    apply (clarsimp simp add: mult.left_assoc)
    apply(intro pure_eq_pre)
    apply(clarsimp)
    proof(goal_cases)
      case (1 tsia tsin ti tsi' rs split)
      have *: "
          length tsi's = length rss \<Longrightarrow>
          length rss = length tss \<Longrightarrow>
          length tss = length splits \<Longrightarrow>
          set tsi's \<subseteq> set tsi' \<Longrightarrow>
          set rss \<subseteq> set rs \<Longrightarrow>
          set tss \<subseteq> set ts \<Longrightarrow>
          set splits \<subseteq> set split \<Longrightarrow>
         bplustree_assn_leafs k t ti (last (ra # rss)) z (last split)* 
         list_assn ((\<lambda>t (ti, x, y, s). bplustree_assn_leafs k t (the ti) x y s) \<times>\<^sub>a id_assn) tss
         (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss splits))) (separators tsi's)) =
         leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z (concat splits @ last split) *
         list_assn ((\<lambda>t (ti, x, y, s). trunk_assn k t (the ti) x y s) \<times>\<^sub>a id_assn) tss
         (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss splits))) (separators tsi's)) *
        trunk_assn k t ti (last (ra#rss)) z (last split)"
        for rss tsi's tss splits
      proof (induct arbitrary: ra rule: list_induct4)
        case (Nil r)
        then show ?case
          apply(clarsimp)
          using 2(1)[of ti r "[]" "split"]
          apply (simp add: last.simps)
          done
      next
        case (Cons subsepi tsi's subleaf rss subsep tss fsplit splits r)
        show ?case 
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
          apply(subst prod_assn_def)+
        apply(simp split!: prod.splits add: mult.left_assoc)
          subgoal for sub sep
(* extract fact that length of leaf nodes of subleaf matches leaf_nodes_assn_split req *)
          apply(subst bplustree_assn_leafs_len_aux[of k sub])
          apply(subst trunk_assn_leafs_len_aux[of k sub])
            apply sep_auto
            apply(intro pure_eq_pre)
(* extract fact that the remaining list is not empty *)
          apply(subst bplustree_assn_leafs_not_empty_aux[of k t])
          apply(subst trunk_assn_not_empty_aux[of k t])
            apply sep_auto
            apply(intro pure_eq_pre)
          supply R = leaf_nodes_assn_split[of "leaf_nodes sub" fsplit
                                        "concat splits @ last split" "hd (concat splits @ last split)" "tl (concat splits @ last split)"]
          thm R
        apply(subst R)
          subgoal by simp
          subgoal by simp
          (* show that r = hd fsplit *)
          apply(subst bplustree_assn_leafs_hd_aux[of k sub])
          apply(subst trunk_assn_hd_aux[of k sub])
            apply sep_auto
            apply(intro pure_eq_pre)
(* refactor multiplication s.t. we can apply the lemma about two mult. factors with an OTF lemma *)
          supply R = subleaf_at_head_of_concat_inner[of tsi's rss tss splits k id_assn subleaf t ti z "last split"]
          thm R
          apply (subst_mod_mult_ac R)
          subgoal using Cons by simp
          subgoal using Cons by simp
          subgoal using Cons by simp
          apply(simp add: mult.left_assoc)?
(* refactor multiplication s.t. we can apply the lemma about two mult. factors with an OTF lemma *)
          supply R=subleaf_at_head_of_concat_bplustree[of tsi's rss tss splits k id_assn subleaf t ti z "last split"]
          thm R
          apply (subst_mod_mult_ac R)
          subgoal using Cons by simp
          subgoal using Cons by simp
          subgoal using Cons by simp
          apply(simp add: mult.left_assoc)?
            apply(intro pure_eq_pre)
        proof(goal_cases)
          case 1
          moreover have p: "set tsi's \<subseteq> set tsi'"
               "set rss \<subseteq> set rs"
               "set tss \<subseteq> set ts"
               "set splits \<subseteq> set split"
            using Cons.prems by auto
          moreover have "(sub,sep) \<in> set ts"
            using "1" Cons.prems(3) by force
          moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf, fsplit), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf, fsplit), temp2)]"
            by auto
          ultimately show ?case
            apply(inst_ex_assn subleaf)
            using "Cons.hyps"(4)[of subleaf, OF p, simplified]
            apply (auto simp add: algebra_simps)
            using "2.IH"(2)[of subsep "((fst subsepi, temp1, subleaf, fsplit),temp2)" "[((fst subsepi, temp1, subleaf, fsplit),temp2)]"
                "fst subsepi" "(temp1, subleaf, fsplit)" temp1 "(subleaf, fsplit)" subleaf fsplit r, simplified]
            apply auto
            using assn_times_assoc ent_refl by presburger
        qed
        done
    qed
      show ?case
        apply(intro ent_iffI)
        subgoal
         apply(rule entails_preI)
          using 1
        apply(auto dest!: mod_starD list_assn_len)
          apply(subst_mod_mult_ac *[of tsi' rs ts "butlast split", simplified])
          subgoal by auto
          subgoal by auto
          subgoal by auto
          subgoal by (meson in_set_butlastD subset_code(1))
          subgoal
          apply(subgoal_tac "concat (butlast split) @ (last split) = concat split") 
            prefer 2
              subgoal
                apply(subst concat_append_butlast)
                apply auto
                done
              subgoal by sep_auto
              done
            done
      subgoal
         apply(rule entails_preI)
        using 1
        apply(auto dest!: mod_starD list_assn_len)
          apply(subgoal_tac "concat split = concat (butlast split) @ (last split)") 
            prefer 2
              subgoal
                apply(subst concat_append_butlast)
                apply auto
                done
              apply simp
              apply(subst_mod_mult_ac *[of tsi' rs ts "butlast split", simplified, symmetric])
          subgoal by auto
          subgoal by auto
          subgoal by auto
          subgoal by (meson in_set_butlastD subset_code(1))
          subgoal by sep_auto
        done
      done
    qed
  qed
declare last.simps[simp add] butlast.simps[simp add]


fun leaf_node:: "('a::heap) bplustree \<Rightarrow> 'a list \<Rightarrow> assn" where
  "leaf_node (Leaf xs) xsi = \<up>(xs = xsi)" |
  "leaf_node _ _ = false"

fun leafs_assn :: "('a::heap) pfarray list \<Rightarrow> 'a btnode ref list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "leafs_assn (ln#lns) (r'#lptrs) (Some r) z = 
 (\<exists>\<^sub>A fwd.
      r \<mapsto>\<^sub>r Btleaf ln fwd
    * leafs_assn lns lptrs fwd z
    * \<up>(r' = r)
  )" | 
  "leafs_assn [] [] r z = \<up>(r = z)" |
  "leafs_assn _ _ _ _ = false"

lemma leafs_assn_aux_append:
   "length xs = length xsi \<Longrightarrow> leafs_assn (xs@ys) (xsi@ysi) r z = (\<exists>\<^sub>Al. leafs_assn xs xsi r l * leafs_assn ys ysi l z)"
  apply(induction xs xsi r z rule: leafs_assn.induct)
  apply(sep_auto intro!: ent_iffI)+
  done

abbreviation "leaf_lists \<equiv> \<lambda>t. map leaves (leaf_nodes t)"  

lemma leaf_nodes_assn_flatten_help:
  "length ts = length lptrs \<Longrightarrow> leaf_nodes_assn k ts r z lptrs = (\<exists>\<^sub>Aps. list_assn leaf_node ts (map leaves ts) * list_assn (is_pfa (2*k)) (map leaves ts) ps * leafs_assn ps lptrs r z)"
proof (induction ts lptrs arbitrary: r rule: list_induct2)
  case Nil
  then show ?case
  apply(intro ent_iffI)
    subgoal by sep_auto
    subgoal by sep_auto
    done
next
  case (Cons a xs r' lptrs r)
  then show ?case
  proof(intro ent_iffI, goal_cases)
    case 1
    show ?case
      apply(cases r; cases a)
      apply simp_all
      find_theorems "\<exists>\<^sub>A_._ \<Longrightarrow>\<^sub>A_"
      apply(rule ent_ex_preI)+
      subgoal for aa x1 xsi fwd
      apply (subst "Cons.IH"[of fwd]) 
        apply simp
      apply(rule ent_ex_preI)+
        subgoal for ps
          apply(inst_ex_assn "xsi#ps")
          apply simp_all
          apply(inst_ex_assn fwd)
          apply (sep_auto)
          done
        done
      done
  next
    case 2
    have *: "list_assn leaf_node xs (map leaves xs) * list_assn (is_pfa (2 * k)) (map leaves xs) ps' * leafs_assn ps' lptrs r'' z 
          \<Longrightarrow>\<^sub>A leaf_nodes_assn k xs r'' z lptrs" 
      for ps' r''
      using assn_eq_split(1)[OF sym[OF "Cons.IH"[of r'']]]
             ent_ex_inst[where Q="leaf_nodes_assn k xs r'' z lptrs" and y=ps']
      by blast
    show ?case
      apply(rule ent_ex_preI)+
      subgoal for ps
        apply(cases ps; cases r; cases a)
      apply simp_all
      apply(rule ent_ex_preI)+
        subgoal for aa list aaa x1 fwd
          apply(inst_ex_assn aa fwd)
          apply sep_auto
          using *[of list fwd]
          by (smt (z3) assn_aci(9) assn_times_comm fr_refl)
        done
      done
  qed
qed

lemma leaf_nodes_assn_impl_length: "h \<Turnstile> leaf_nodes_assn k xs r z lptrs \<Longrightarrow> length xs = length lptrs" 
  apply(induction xs arbitrary: h r lptrs)
  subgoal for h r lptrs
    apply(cases r; cases lptrs)
    apply sep_auto+
    done
  subgoal for a xs h r lptrs
    apply(cases r; cases lptrs; cases a)
    apply (sep_auto dest: mod_starD)+
    done
  done

lemma leafs_assn_impl_length: "h \<Turnstile> leafs_assn xs lptrs r z \<Longrightarrow> length xs = length lptrs" 
  apply(induction xs arbitrary: h r lptrs)
  subgoal for h r lptrs
    apply(cases r; cases lptrs)
    apply sep_auto+
    done
  subgoal for a xs h r lptrs
    apply(cases r; cases lptrs)
    apply (sep_auto dest: mod_starD)+
    done
  done

lemma leaf_nodes_assn_flatten:
  "leaf_nodes_assn k ts r z lptrs = (\<exists>\<^sub>Aps. list_assn leaf_node ts (map leaves ts) * list_assn (is_pfa (2*k)) (map leaves ts) ps * leafs_assn ps lptrs r z)"
proof(intro ent_iffI, goal_cases)
  case 1
  then show ?case
  apply(rule entails_preI)
  apply (subst leaf_nodes_assn_flatten_help)
    subgoal by (sep_auto dest!: mod_starD leaf_nodes_assn_impl_length)
    subgoal by sep_auto
    done
next
  case 2
  then show ?case
  apply(rule entails_preI)
  apply (subst leaf_nodes_assn_flatten_help)
    subgoal by (sep_auto dest!: mod_starD leafs_assn_impl_length list_assn_len)
    subgoal by sep_auto
    done
qed


subsection "Iterator"


partial_function (heap) first_leaf :: "('a::heap) btnode ref \<Rightarrow> 'a btnode ref option Heap"
  where
    "first_leaf p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ _ \<Rightarrow> do { return (Some p) } |
    Btnode tsi ti \<Rightarrow> do {
        s \<leftarrow> pfa_get tsi 0;
        let (sub,sep) = s in do { 
          first_leaf (the sub)
        }
  }
)}"

partial_function (heap) last_leaf :: "('a::heap) btnode ref \<Rightarrow> 'a btnode ref option Heap"
  where
    "last_leaf p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ z \<Rightarrow> do { return z } |
    Btnode tsi ti \<Rightarrow> do {
        last_leaf ti
  }
)}"

declare last.simps[simp del] butlast.simps[simp del]
lemma first_leaf_rule[sep_heap_rules]:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  first_leaf ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(u = r)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti z)
  case (Leaf x)
  then show ?case
    apply(subst first_leaf.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  then obtain sub sep tts where Cons: "ts = (sub,sep)#tts"
    apply(cases ts) by auto
  then show ?case 
    apply(subst first_leaf.simps)
    apply (sep_auto simp add: butlast.simps)
    subgoal for tsia tsil ti tsi' rs subi sepi
    apply(cases rs; cases tsi')
    apply simp_all
      subgoal for subleaf rrs _ ttsi'
        supply R = "Node.IH"(1)[of "(sub,sep)" sub "(the subi)" subleaf]
        thm R
    using  "Node.prems"(1)
    apply (sep_auto heap add: R)
    subgoal by (metis Node.prems(2) assms(1) bplustree.inject(2) bplustree.simps(4) Cons list.set_intros(1) order_impl_root_order root_order.elims(2) some_child_sub(1))
    apply (sep_auto eintros del: exI)
    apply(inst_existentials tsia tsil ti "(subi, sepi) # ttsi'" "((subi, (r, subleaf)),sepi)#(zip (zip (subtrees ttsi') (zip (butlast (subleaf # rrs)) rrs)) (separators ttsi'))" "subleaf # rrs")
    apply (sep_auto simp add: last.simps butlast.simps)+
    done
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]

declare last.simps[simp del] butlast.simps[simp del]
lemma last_leaf_rule[sep_heap_rules]:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  last_leaf ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(u = z)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti r)
  case (Leaf x)
  then show ?case
    apply(subst last_leaf.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  show ?case 
    apply(subst last_leaf.simps)
        supply R = "Node.IH"(2)
    apply (sep_auto heap add: R)
    subgoal using "Node.prems" by simp
    subgoal by (metis Node.prems(2) assms(1) bplustree.inject(2) bplustree.simps(4) Cons list.set_intros(1) order_impl_root_order root_order.elims(2) some_child_sub(1))
    apply (sep_auto eintros del: exI)
    subgoal for tsia tsil ti tsi' rs
    apply(inst_existentials tsia tsil ti "tsi'" " (zip (zip (subtrees tsi') (zip (butlast (r # rs)) rs)) (separators tsi'))" rs)
    apply (sep_auto simp add: last.simps butlast.simps)+
    done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]


definition tree_leaf_iter_init where
"tree_leaf_iter_init p = do {
  r \<leftarrow> first_leaf (the p);
  z \<leftarrow> last_leaf (the p);
  return  (r, z)
}"

lemma tree_leaf_iter_init_rule_help:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  tree_leaf_iter_init (Some ti)
  <\<lambda>(u,v). bplustree_assn k t ti r z * \<up>(u = r \<and> v = z)>\<^sub>t"
  using assms
  unfolding tree_leaf_iter_init_def
  by (sep_auto)

lemma tree_leaf_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  tree_leaf_iter_init (Some ti)
  <\<lambda>(u,v). \<exists>\<^sub>A lptrs. leaf_nodes_assn k (leaf_nodes t) r z lptrs * trunk_assn k t ti r z lptrs * \<up>(u = r \<and> v = z)>\<^sub>t"
  using assms
  apply(vcg heap add: tree_leaf_iter_init_rule_help)
  by (simp add: bplustree_extract_leafs bplustree_leaf_nodes_sep)

lemma tree_leaf_iter_init_rule_alt:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  tree_leaf_iter_init (Some ti)
  <\<lambda>(u,v). \<exists>\<^sub>A lptrs ps. list_assn leaf_node (leaf_nodes t) (map leaves (leaf_nodes t)) * list_assn (is_pfa (2*k)) (map leaves (leaf_nodes t)) ps * leafs_assn ps lptrs r z * trunk_assn k t ti r z lptrs * \<up>(u = r \<and> v = z)>\<^sub>t"
  using assms
  apply(vcg heap add: tree_leaf_iter_init_rule)
  apply(sep_auto simp add: leaf_nodes_assn_flatten)
  done

(* TODO derive version that yields leaf_iter_assn *)


definition leaf_iter_next where
"leaf_iter_next = (\<lambda>(r,z). do {
  p \<leftarrow> !(the r);
  return (vals p, (fwd p, z))
})"

lemma leaf_iter_next_rule_help:
  "<leafs_assn (x#xs) (l#lptrs) r z>
      leaf_iter_next (r,z)
   <\<lambda>(p,(n,z')). leafs_assn [x] [l] r n * leafs_assn xs lptrs n z' * \<up>(p = x) * \<up>(z=z')>"
  apply(subst leaf_iter_next_def)
  apply(cases r; cases x)
  apply(sep_auto)+
  done

definition leaf_iter_assn where "leaf_iter_assn xs lptrs r xs2 = (\<lambda>(n,z). 
  (\<exists>\<^sub>Axs1 lptrs1 lptrs2. \<up>(xs = xs1@xs2) * \<up>(lptrs = lptrs1@lptrs2) * leafs_assn xs1 lptrs1 r n * leafs_assn xs2 lptrs2 n z * \<up>(z=None)))" 

lemma leaf_nodes_assn_imp_iter_assn:
  "leafs_assn xs lptrs r None \<Longrightarrow>\<^sub>A leaf_iter_assn xs lptrs r xs (r,None)"
  unfolding leaf_iter_assn_def
  by sep_auto

definition leaf_iter_init where
"leaf_iter_init p = do {
  return  (p, None)
}"

lemma leaf_iter_init_rule:
  shows "<leafs_assn xs lptrs r None>
  leaf_iter_init r
  <\<lambda>u. leaf_iter_assn xs lptrs r xs u>"
  unfolding leaf_iter_init_def
  using leaf_nodes_assn_imp_iter_assn
  by (sep_auto)


lemma leaf_iter_next_rule: "<leaf_iter_assn xs lptrs r (x#xs2) it>
leaf_iter_next it
<\<lambda>(p, it'). leaf_iter_assn xs lptrs r xs2 it' * \<up>(p = x)>"
  unfolding leaf_iter_assn_def
  apply(clarsimp split: prod.splits)
  apply(intro norm_pre_ex_rule)
  subgoal for n z xs1 lptrs1 lptrs2
    apply(rule hoare_triple_preI)
  apply(clarsimp dest!: mod_starD leafs_assn_impl_length)
    apply(cases lptrs2; clarsimp)
    subgoal for l llptrs2
   apply (sep_auto heap add: leaf_iter_next_rule_help eintros del: exI)
      apply(inst_existentials "xs1@[x]" "lptrs1@[l]" llptrs2)
      subgoal by sep_auto
      subgoal by (sep_auto simp add: leafs_assn_aux_append)
      done
    done
  done

definition leaf_iter_has_next where
"leaf_iter_has_next  = (\<lambda>(r,z). return (r \<noteq> z))"

(* TODO this so far only works for the whole tree (z = None)
for subintervals, we would need to show that the list of pointers is indeed distinct,
hence r = z can only occur at the end *)
lemma leaf_iter_has_next_rule:
  "<leaf_iter_assn xs lptrs r xs2 it> leaf_iter_has_next it <\<lambda>u. leaf_iter_assn xs lptrs r xs2 it * \<up>(u \<longleftrightarrow> xs2 \<noteq> [])>"
  unfolding leaf_iter_has_next_def leaf_iter_assn_def
  apply(cases it; simp)
  apply(intro norm_pre_ex_rule)
  apply(rule hoare_triple_preI)
  apply(clarsimp dest!: mod_starD leafs_assn_impl_length)
  apply(sep_auto split!: prod.splits dest!: mod_starD)
  by (metis leafs_assn.simps list.exhaust mod_false option.exhaust)

(* copied from peter lammichs lseg_prec2, don't ask what happens in the induction step
(or ask peter lammich) *)
declare mult.left_commute[simp add]
lemma leafs_assn_prec2: 
  "\<forall>l l'. (h\<Turnstile>
      (leafs_assn l lptrs p None * F1) \<and>\<^sub>A (leafs_assn l' lptrs p None * F2)) 
    \<longrightarrow> l=l'"
  apply (intro allI)
  subgoal for l l'
  proof (induct l arbitrary: lptrs p l' F1 F2)
    case Nil thus ?case
      apply (cases l')
      apply simp
      apply (cases p)
      apply (auto simp add: mod_and_dist dest!: mod_starD leafs_assn_impl_length)
      done
  next
    case (Cons y l)
    from Cons.prems show ?case
      apply (cases p)
      apply simp
      apply (cases l')
      subgoal by (auto simp add: mod_and_dist dest!: mod_starD leafs_assn_impl_length)[]
      apply(cases lptrs)
      subgoal by (auto simp add: mod_and_dist dest!: mod_starD leafs_assn_impl_length)[]
      apply (rule)
      apply clarsimp
      apply(subgoal_tac "y = (aa, b) \<and> fwd = fwda", simp)
      using Cons.hyps apply (erule prec_frame')
      apply frame_inference
      apply frame_inference
      apply (drule_tac p=a in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
  qed
  done
declare mult.left_commute[simp del]

interpretation leaf_node_it: imp_list_iterate
    "\<lambda>x y. leafs_assn x lptrs y None"
    "\<lambda>x y. leaf_iter_assn x lptrs y"
    leaf_iter_init
    leaf_iter_has_next
    leaf_iter_next
  apply(unfold_locales)
  subgoal 
    by (simp add: leafs_assn_prec2 precise_def)
  subgoal for l p 
    by (sep_auto heap add: leaf_iter_init_rule)
  subgoal for l' l p it
    thm leaf_iter_next_rule
    apply(cases l'; cases it)
    by (sep_auto heap add: leaf_iter_next_rule)+
  subgoal for l p l' it'
    thm leaf_iter_has_next_rule
    apply(cases it')
    apply(rule hoare_triple_preI)
    apply(sep_auto heap add: leaf_iter_has_next_rule)
    done
  subgoal for l p l' it
  unfolding leaf_iter_assn_def
  apply(cases it)
    apply simp_all
  apply(intro ent_ex_preI)
  apply(rule entails_preI)
  apply(clarsimp dest!: mod_starD leafs_assn_impl_length)
  by (sep_auto simp add: leafs_assn_aux_append)
  done

global_interpretation leaf_values_iter: flatten_iter
  "\<lambda>x y. leafs_assn x lptrs y None" "\<lambda>x y. leaf_iter_assn x lptrs y"
  leaf_iter_init leaf_iter_has_next leaf_iter_next
  "is_pfa (2*k)" "pfa_is_it (2*k)" pfa_it_init pfa_it_has_next pfa_it_next
  defines leaf_values_adjust = leaf_values_iter.flatten_it_adjust
      and leaf_values_init = leaf_values_iter.flatten_it_init
      and leaf_values_next = leaf_values_iter.flatten_it_next
      and leaf_values_has_next = leaf_values_iter.flatten_it_has_next
  by (unfold_locales)

thm leaf_values_iter.is_flatten_list.simps
thm leaf_values_iter.is_flatten_it.simps
thm leaf_values_init_def
thm leaf_values_iter.flatten_it_init_def
print_theorems

fun bplustree_iter_init :: "('a::heap) btnode ref \<Rightarrow> _" where
  "bplustree_iter_init ti = do {
        rz \<leftarrow> tree_leaf_iter_init (Some ti);
        it \<leftarrow> leaf_values_init (fst rz);
        return it
}"


lemma leaf_nodes_imp_flatten_list:
  "leaf_nodes_assn k ts r None lptrs \<Longrightarrow>\<^sub>A
   list_assn leaf_node ts (map leaves ts) *
   leaf_values_iter.is_flatten_list lptrs k (map leaves ts) (concat (map leaves ts)) r"
  apply(simp add: leaf_nodes_assn_flatten)
  apply(intro ent_ex_preI)
  subgoal for ps
    apply(inst_ex_assn ps "map leaves ts")
    apply sep_auto
    done
  done

lemma leaf_nodes_imp_flatten_list_back:
   "list_assn leaf_node ts (map leaves ts) *
leaf_values_iter.is_flatten_list lptrs k (map leaves ts) (concat (map leaves ts)) r \<Longrightarrow>\<^sub>A
  leaf_nodes_assn k ts r None lptrs"
  apply(simp add: leaf_nodes_assn_flatten)
  apply(intro ent_ex_preI)
  subgoal for ps
    apply(inst_ex_assn ps "map leaves ts")
    apply sep_auto
    done
  done

lemma leaf_nodes_flatten_list: "leaf_nodes_assn k ts r None lptrs =
   list_assn leaf_node ts (map leaves ts) *
   leaf_values_iter.is_flatten_list lptrs k (map leaves ts) (concat (map leaves ts)) r"
  apply(intro ent_iffI)
  subgoal by (rule leaf_nodes_imp_flatten_list)
  subgoal by (rule leaf_nodes_imp_flatten_list_back)
  done

definition "bplustree_iter_list k t ti r = (\<exists>\<^sub>A lptrs.
  leaf_values_iter.is_flatten_list lptrs k (map leaves (leaf_nodes t)) (leaves t) r *
  list_assn leaf_node (leaf_nodes t) (map leaves (leaf_nodes t)) *
  trunk_assn k t ti r None lptrs)"

lemma bplustree_iff_leaf_view: "bplustree_assn k t ti r None = bplustree_iter_list k t ti r"
  unfolding bplustree_iter_list_def
  apply(simp add:
        bplustree_extract_leafs
        bplustree_leaf_nodes_sep
        leaf_nodes_flatten_list
        concat_leaf_nodes_leaves
  )
  apply (auto simp add: algebra_simps)
  done

definition "bplustree_iter k t ti r vs it = (\<exists>\<^sub>A fringe.
  leaf_values_iter.is_flatten_it fringe k (map leaves (leaf_nodes t)) (leaves t) r vs it *
  list_assn leaf_node (leaf_nodes t) (map leaves (leaf_nodes t)) *
  trunk_assn k t ti r None fringe)"

(* Now finally, we can hide away that we extracted anything
and just provide the user with some pretty definitions *)

lemma bplustree_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r None>
bplustree_iter_init ti
<\<lambda>it. bplustree_iter k t ti r (leaves t) it>\<^sub>t"
  unfolding bplustree_iter_init.simps
  unfolding bplustree_iter_def
  using assms 
  apply (sep_auto heap add: tree_leaf_iter_init_rule)
  apply(subst leaf_nodes_flatten_list)
  apply(vcg heap add: leaf_values_iter.flatten_it_init_rule)
  subgoal for lptrs
    apply(inst_ex_assn lptrs)
    apply(sep_auto simp add: concat_leaf_nodes_leaves)
  done
  done

(* using is_flatten_it we can now iterate through elements in the leafs *)

abbreviation "bplustree_iter_next \<equiv> leaf_values_next" 

lemma bplustree_iter_next_rule: "vs \<noteq> [] \<Longrightarrow>
    <bplustree_iter k t ti r vs it>
  bplustree_iter_next it
  <\<lambda>(a, it'). bplustree_iter k t ti r (tl vs) it' * \<up> (a = hd vs)>\<^sub>t"
  unfolding bplustree_iter_def
  apply(sep_auto heap add: leaf_values_iter.flatten_it_next_rule)
  done

abbreviation "bplustree_iter_has_next \<equiv> leaf_values_has_next" 

lemma bplustree_iter_has_next_rule: "
    <bplustree_iter k t ti r vs it>
  bplustree_iter_has_next it
  <\<lambda>r'. bplustree_iter k t ti r vs it * \<up> (r' = (vs \<noteq> []))>\<^sub>t"
  unfolding bplustree_iter_def
  apply(sep_auto heap add: leaf_values_iter.flatten_it_has_next_rule)
  done

lemma bplustree_iter_quit: 
"bplustree_iter k t ti r vs it \<Longrightarrow>\<^sub>A bplustree_assn k t ti r None * true"
  unfolding bplustree_iter_def
  apply(rule ent_ex_preI)
  subgoal for lptrs
  apply(rule ent_frame_fwd[OF leaf_values_iter.flatten_quit_iteration, where F="list_assn leaf_node (leaf_nodes t) (leaf_lists t) *
    trunk_assn k t ti r None lptrs"])
  apply solve_entails
  apply(simp add:
        bplustree_extract_leafs
        bplustree_leaf_nodes_sep
        leaf_nodes_flatten_list
        concat_leaf_nodes_leaves
  )
  apply(rule ent_ex_preI)
  subgoal for lsi'
  apply(inst_ex_assn lptrs lsi')
  apply sep_auto
    done
  done
  done

declare first_leaf.simps[code]
declare last_leaf.simps[code]
(* declare leaf_values_iter.flatten_it_adjust.simps[code] *)
(* Code exports can be found with in ImpSplitCE *)
end