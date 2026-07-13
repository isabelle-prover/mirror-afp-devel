(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsection "Descending Unicycles Criterion"
theory Descending_Unicycles_Criterion
  imports "../Sloped_Graphs"
          "../Buchi_Preliminaries"
begin

(* 1. THE FLAT CYCLE CRITERION *)

context Graph
begin

(*It must satisfy cycleG, and the internal nodes must be unique. 
     We use 'butlast' because the first and last nodes are identical in cycleG. *)
definition basicCycle :: "'node list \<Rightarrow> bool" where
 "basicCycle c \<equiv> cycleG c \<and> distinct (butlast c)"

lemmas basicCycle_defs = basicCycle_def[unfolded cycleG_def]

lemma basicCycleI:"pathG c \<Longrightarrow> hd c = last c \<Longrightarrow> distinct (butlast c) \<Longrightarrow> basicCycle c"
  unfolding basicCycle_def cycleG_def by auto

lemma basicCycle_path_drop: "basicCycle c \<Longrightarrow> j < length (butlast c) \<Longrightarrow> pathG (drop j c)"
  using cycleG_path_drop unfolding basicCycle_def by auto


lemma basicCycle_not_nil:"basicCycle c \<Longrightarrow> c \<noteq>[]" unfolding basicCycle_def cycleG_def by auto
lemma basicCycle_ge2:"basicCycle c \<Longrightarrow> length c \<ge> 2" unfolding basicCycle_def cycleG_def using path_length_ge2 by auto

lemma cycle_elim:"\<not>(\<exists>c. basicCycle c \<and> set c = V') \<Longrightarrow> (\<forall>c. basicCycle c \<longrightarrow> set c \<noteq> V' \<Longrightarrow> P) \<Longrightarrow> P" by auto


lemma basicCycle_set_eq:"basicCycle c \<Longrightarrow> set c = set (butlast c)"
apply(standard)
  unfolding basicCycle_def cycleG_def
  using path_length_ge2[of c] 
  apply (metis append_butlast_last_id basicCycleI
      basicCycle_not_nil cycle_Cons hd_append2 hd_in_set
      list.simps(3) not_path_singl self_append_conv2
      set_ConsD sset_cycle stream.set_intros(2)
      subset_code(1))
  by (meson in_set_butlastD subset_code(1))

(*Any cycle necessarily has a basic cycle within*)
lemma cycleG_contains_basicCycle:
  assumes "cycleG ndl"
  shows "\<exists>c. basicCycle c \<and> set c \<subseteq> set ndl"
using assms proof (induct "length ndl" arbitrary: ndl rule: less_induct)
  case less
  note cycle = less(2)
  then have ndl_ne:"ndl \<noteq> []" "length ndl \<ge> 2" unfolding cycleG_def using path_length_ge2 by auto
  then show ?case 
  proof(cases "distinct (butlast ndl)")
    case True
    then show ?thesis unfolding basicCycle_def using cycle by auto
  next
    case False
    (*If not distinct, find the first repeated node to extract a smaller cycle*)
    then obtain xs y ys zs where split: "butlast ndl = xs @ y # ys @ y # zs" using not_distinct_decomp by fastforce

    let ?c' = "y # ys @ [y]"

    have pathG_butlast:"pathG (butlast ndl)" using cycle[unfolded cycleG_def] False pathG.cases by fastforce
    hence "pathG ?c'" unfolding split 
      using path_appendR[of xs "y # ys @ y # zs"] path_appendL[of "y # ys @ [y]"] by auto

    hence "cycleG ?c'" unfolding cycleG_def by auto

    also have "length ?c' < length ndl"   using split length_butlast[of ndl] ndl_ne by auto

    moreover have "set ?c' \<subseteq> set ndl" by(rule subsetI, rule in_set_butlastD, unfold split, auto) 

    ultimately show ?thesis using less(1)[of ?c'] by auto
  qed
qed

lemma basicCycle_rotate1:
"basicCycle (ndl @ [nd,nd']) \<Longrightarrow> basicCycle (nd # ndl @ [nd])" 
unfolding basicCycle_defs path_iff_set_nth apply safe
  subgoal by auto
  subgoal by auto
  subgoal for i apply (cases i) 
    subgoal by simp (metis append.assoc append.left_neutral append_Cons length_append_singleton 
      lessI list.sel(1) neq_Nil_conv nth_Cons_0 nth_append_length)
    subgoal by simp (metis Suc_lessI less_SucI nth_append nth_append_length) . 
  subgoal by simp
  by (simp add: butlast_append)

lemma basicCycle_rotate:
assumes "basicCycle (ndl1 @ ndl2 @ [nd'])" "ndl2 \<noteq> []" 
shows "basicCycle (ndl2 @ ndl1 @ [hd ndl2])" 
using assms proof(induction ndl2 arbitrary: ndl1 nd' rule: rev_induct) 
  case Nil thus ?case by auto
next 
  case (snoc nd2 ndl2 ndl1 nd')
  show ?case
  proof(cases "ndl2 = []")
    case True 
    show ?thesis unfolding True apply simp
    apply(rule basicCycle_rotate1) using snoc True by auto
  next
    case False   
    hence 1: "ndl2 @ nd2 # ndl1 @ [hd ndl2] = hd ndl2 # (tl ndl2 @ nd2 # ndl1) @ [hd ndl2]" by auto
    have 2: "(tl ndl2 @ nd2 # ndl1) @ [hd ndl2, hd (tl ndl2 @ [nd2])] = 
             (tl ndl2 @ [nd2]) @ (ndl1 @ [hd ndl2]) @ [hd (tl ndl2 @ [nd2])]"
    by auto
    show ?thesis using False apply simp unfolding append_Cons[symmetric]
    apply(rule snoc.IH[where nd' = nd2])
      subgoal unfolding append_Cons unfolding append_assoc[symmetric] apply(rule basicCycle_rotate1)
      using snoc by auto 
      subgoal by auto . 
  qed
qed

lemma basicCycle_rotate_butlast: 
assumes "basicCycle (ndl1 @ nd # ndl2)" "ndl1 \<noteq> []" "ndl2 \<noteq> []"
shows "basicCycle (nd # butlast ndl2 @ ndl1 @ [nd])" 
using assms basicCycle_rotate[where nd' = "last (nd # ndl2)"  
    and ?ndl2.0 = "butlast (nd # ndl2)" and ?ndl1.0 = ndl1] using assms by simp


lemma basicCycle_rotate_set: 
assumes "basicCycle ndl" "nd \<in> set ndl"
shows "\<exists>ndl'. set ndl' = set ndl \<and> basicCycle ndl' \<and> hd ndl' = nd \<and> last ndl' = nd \<and> length ndl' = length ndl"
proof(cases "hd ndl = nd \<or> last ndl = nd")
  case True thus ?thesis apply(intro exI[of _ ndl])
  using assms unfolding basicCycle_defs by auto
next
  case False then obtain ndl1 ndl2 where ndl: "ndl = ndl1 @ nd # ndl2" "ndl1 \<noteq> []" "ndl2 \<noteq> []"
  by (metis assms(2) hd_append last_ConsL last_append list.sel(1) list.simps(3) split_list)
  thus ?thesis using basicCycle_rotate_butlast[OF assms(1)[unfolded ndl(1)] ndl(2,3)] 
  apply(intro exI[of _ "nd # butlast ndl2 @ ndl1 @ [nd]"]) using assms ndl
  apply safe
    subgoal using in_set_butlastD by force
    subgoal by (smt Un_iff append_butlast_last_id hd_append2 hd_conv_nth in_set_conv_nth insert_iff 
      last.simps last_appendR length_greater_0_conv list.set(2) basicCycle_defs set_append)
    by auto 
qed

(*If there is an alternative edge within a basic cycle that's not in list order, 
  then we can construct a smaller cycle*)
lemma basicCycle_smaller_alt:
  assumes "basicCycle c"
  assumes "i < length c - 1"
  assumes "edge (c ! i) v" "v \<in> set (butlast c)"
  assumes assm:"v \<noteq> c ! Suc i"
  shows "\<exists>c_alt. basicCycle c_alt \<and> set c_alt \<subseteq> set c \<and> v \<in> set c_alt \<and> (c!i) \<in> set c_alt \<and> (c!Suc i) \<notin> set c_alt"
proof -
  from assms(1) have pG: "pathG c" and dist: "distinct (butlast c)" and cyc: "cycleG c"
    unfolding basicCycle_def using cycleG_def by auto

  hence c_Suc_in:"c ! Suc i \<in> set (butlast c)" using assms basicCycle_set_eq[OF assms(1)] 
    by (metis diff_Suc_1 diff_less_Suc in_set_conv_nth less_trans_Suc
        not_less_less_Suc_eq)
  have hd_eq:"hd (butlast c) = hd c"  by (metis append_butlast_last_id assms(4) hd_append2 list.set(1) set_nemp not_path_Nil pG)

  (**Find the index j of the target node v in the cycle**)
  obtain j where j: "j < length c - 1" "v = c ! j" "j \<noteq> Suc i"
    using assms(4) length_butlast[of c] by (metis assm in_set_conv_nth nth_butlast)
  
  (*Case 1: The edge forms a smaller 'shortcut' cycle*)
  (*Construct a new path p' from v back to c!i using the original cycle segments*)
  (*... and close it with the edge (c!i) v.*)
  
  (*Since unicyclesGraph is assumed, any basicCycle c' connected to c must have set c' = set c.\<close>
    However, a shortcut cycle strictly uses a subset of nodes if the graph is basic.*)

    show ?thesis proof(cases "j \<le> i")
    case True
                                                          
    define c_alt where c_alt:"c_alt = map ((!) (butlast c)) [j..<Suc i] @ [c!j]"
    hence c_alt': "c_alt = drop j (take (Suc i) (butlast c)) @ [c!j]" 
      using map_nth_upt_drop_take_conv[of "Suc i" "butlast c" j]
      using assms(2) by auto

    hence c_eq:"c = take j c @ drop j (take (Suc i) (butlast c)) @ drop (Suc i) c" 
      by (metis All_less_Suc True add_diff_cancel_left' add_increasing append_take_drop_id assms(2) diff_Suc_1'
          drop_take_drop_unsplit le_simps(2) less_diff_conv less_eqE nat_geq_1_eq_neqz nat_in_between_eq(2) plus_1_eq_Suc
          semiring_norm(174) take_butlast)

    have c_alt_dist:"distinct (butlast c_alt)"
      unfolding c_alt'
      using distinct_drop[of _ j, OF distinct_take[OF dist, of "Suc i"]] by auto 
    
    from c_alt have last:"c ! i = last (butlast c_alt)" 
      apply (simp add: True) 
      by (metis assms(2) butlast.simps(2) butlast_append last_snoc length_butlast
          list.distinct(1) nth_butlast)


    also have first:"hd c_alt = c ! j" "v \<in> set c_alt" 
      unfolding c_alt apply (simp_all add: hd_append hd_drop_conv_nth j True)
      by (metis True butlast_conv_take hd_map hd_upt j(1) le_0_eq nat_less_le nth_take
          upt_eq_Nil_conv)

    hence "c_alt \<noteq> []" by fastforce
    then have "c ! j \<in> set (butlast c_alt)"  using first c_alt True 
      by (simp,metis butlast_snoc c_alt hd_append2 hd_in_set list.discI list_se_match(2) not_Cons_self2)


    hence ci_in:"c ! i \<in> set (butlast c_alt)" apply-by(unfold last,rule last_in_set, fastforce) 

    have c_alt_path:"pathG c_alt"
    proof(cases "i = j")
      case True
      then show ?thesis
        unfolding c_alt apply (simp split:if_splits add: take_Suc hd_drop_conv_nth)
        using assms(3) j(1,2) pG pathG.intros(1) path_nth_'node by (simp add: nth_butlast)
    next
      case False
      hence "j<i" using True by auto
      thus ?thesis
        apply-apply(unfold c_alt,rule pathG.Step)
        subgoal using assms(1,4) basicCycle_set_eq j(2) pG path_set by auto
        subgoal using assms(1)[unfolded basicCycle_defs]
                       c_alt[symmetric, unfolded c_alt'] c_eq True apply simp
                apply(rule path_appendM[of "take j c" "drop j (take (Suc i) (butlast c))" "drop (Suc i) c"], simp)
          by (metis Suc_leI Suc_mono length_append_singleton length_map length_upt numerals(2) zero_less_diff)
        using last by (metis assms(3) butlast_snoc c_alt j(2))        
    qed

    moreover have "basicCycle c_alt"
      using calculation c_alt
            
      unfolding basicCycle_defs
      apply(intro conjI)
      subgoal using c_alt_path by auto
      subgoal using first by auto
      subgoal using c_alt_dist by auto  .

    moreover have "c ! Suc i \<notin> set c_alt"
    proof(cases "Suc i = length (butlast c)")
      case True
      hence c_Suc:"c ! Suc i = c ! 0"
        using assms(1)[unfolded basicCycle_defs] 
        by (metis append_butlast_last_id cyc cycleG_not_nil
            hd_conv_nth nth_append_length)


      hence j_gr:"j > 0" using j assm[unfolded c_Suc] bot_nat_0.not_eq_extremum by blast
      show ?thesis
        unfolding c_alt c_Suc apply (simp add: True, intro conjI)
        subgoal using assm[unfolded c_Suc] j(2) c_Suc by (metis)
        subgoal using j_gr  dist unfolding distinct_conv_nth[of "butlast c"]  apply-apply(elim allE[of _ 0], erule impE)
          subgoal using True by linarith
          subgoal using distinct_outside_index[of j, OF _ _ dist] 
                  by (metis One_nat_def True length_butlast nth_butlast zero_less_Suc) . .
    next
      case False
      hence "Suc i < length (butlast c)" using assms(2) by fastforce
      then show ?thesis
        unfolding c_alt apply (simp add: True, intro conjI)
        subgoal using nth_butlast[of i c, unfolded length_butlast, OF assms(2)]
                      dist distinct_conv_nth[of "butlast c"] 
          by (metis assms(2) length_butlast n_not_Suc_n nth_butlast)
        subgoal using j dist distinct_conv_nth[of "butlast c"] assm by fastforce
        subgoal using dist unfolding distinct_conv_nth[of "butlast c"]  apply-apply(elim allE[of _ "Suc i"], erule impE)
          subgoal by auto
          subgoal using distinct_outside_index'[OF dist] by blast . .
    qed

    ultimately show ?thesis
      apply-apply(rule exI[of _ c_alt], simp, intro conjI)
      subgoal using c_alt_dist unfolding c_alt' by (metis assms(1) basicCycle_set_eq in_set_dropD in_set_takeD snoc_eq_iff_butlast'
            subset_code(1))
      subgoal using j first(2) by blast 
      subgoal by (metis ci_in in_set_butlastD) .
  next
    case False
    hence False':"j > Suc i" using j by auto
    define c_alt where c_alt:"c_alt = (drop j (butlast c)) @ (take (Suc i) (butlast c)) @ [c!j]"

    hence butlast_alt:"butlast c_alt = (drop j (butlast c)) @ (take (Suc i) (butlast c))" by (simp add: butlast_append)
    from c_alt have last:"last (take (Suc i) (butlast c)) = c ! i" 
      using last_take_nth_conv assms(2) bot_nat_0.extremum_strict diff_Suc_1 diff_le_self 
      by (metis (no_types, lifting) butlast_conv_take length_butlast nth_take le_trans lessI less_eq_Suc_le )

    hence first:"hd c_alt = c ! j"  unfolding c_alt 
      by (metis butlast_conv_take drop_eq_Nil2 hd_append hd_drop_conv_nth j(1) length_butlast nth_take
          verit_comp_simplify1(3))
    hence hd_last:"hd c_alt = last c_alt" by (simp add: c_alt)


    have vin:"v \<in> set c_alt" unfolding j c_alt by auto
    have cin:"c ! i \<in> set c_alt" unfolding c_alt using last 
      by (metis Misc.last_in_set Zero_not_Suc assms(4) butlast_snoc gr0_conv_Suc in_set_butlast_appendI length_0_conv
          length_pos_if_in_set take_eq_Nil2)

    have set_incls:"set (drop j (butlast c))  \<subseteq> set c" "c!j \<in> set c" "set (take (Suc i) (butlast c)) \<subseteq> set c"
      apply (simp add: assms(1) basicCycle_set_eq set_drop_subset)
      apply (metis assms(4) in_set_butlastD j(2))
      by (meson in_set_butlastD in_set_takeD subset_code(1))
    hence set_in_alt:"set c_alt \<subseteq> set c" unfolding c_alt by auto

    have c_alt_path:"pathG c_alt"
      unfolding c_alt 
      apply(cases "length c > 2")  
      subgoal apply(rule path_append_hd)
        subgoal using basicCycle_path_drop[OF assms(1) j(1)[unfolded length_butlast[symmetric]]]
                      assms(1)[unfolded basicCycle_defs] 
          by (simp,metis assms(4) hd_append2 length_greater_0_conv length_pos_if_in_set list.size(3) take_eq_Nil
      zero_less_Suc append_take_drop_id basicCycleI basicCycle_not_nil distinct_drop drop_butlast hd_Nil_eq_last last_appendR
              snoc_eq_iff_butlast)
        subgoal apply(cases i, simp add: take_Suc hd_eq)
          subgoal apply(intro conjI)
            subgoal by (metis assms(4) list.set(1) memb_imp_not_empty)
            apply(rule pathG.Base)
            subgoal using path_set[OF pG] set_incls by force
            subgoal using assms j by (simp add: hd_conv_nth) .
          apply(rule pathG.Step)
          subgoal using pG path_iff_set_nth set_incls(2) by auto
          subgoal apply(rule path_appendL[of "take (Suc i) (butlast c)" "drop (Suc i) (butlast c)"])
            subgoal by (simp add: pG pathG_butlast) 
            subgoal by fastforce . 
          subgoal unfolding last using assms j by (simp add: hd_conv_nth) . . 
      (*length c = 2*)
      subgoal using False' apply(cases i, simp_all add: take_Suc) 
        subgoal using assms(2)[unfolded basicCycle_defs]  j(1) by force
        subgoal using j(1) by auto . .

    have c_alt_dist:"distinct (butlast c_alt)"
      using distinct_wrap_around[OF dist False'] unfolding butlast_alt by auto 

    have cS_notin:"c ! Suc i \<notin> set c_alt"
    proof(cases "Suc i = length (butlast c)")
      case True
      show ?thesis using j(1) True False by auto
    next
      case False
      hence succ:"Suc i < length (butlast c)" using assms(2) by fastforce
      then show ?thesis
        unfolding c_alt apply (simp add: False, intro conjI)
        subgoal using nth_butlast[of i c, unfolded length_butlast, OF assms(2)]
                      dist distinct_conv_nth[of "butlast c"] 
          using assm j(2) by fastforce
        subgoal  using False' atLeastLessThan_empty atLeastLessThan_empty_iff2 
                      dist nth_butlast nth_eq_iff_index_eq succ  in_set_drop_conv_nth by metis
        subgoal by (metis Cons_nth_drop_Suc append_take_drop_id dist distinct_take not_distinct_conv_prefix nth_butlast) .
    qed

    note all = set_in_alt vin cin cS_notin c_alt_dist c_alt_path hd_last

    show ?thesis unfolding basicCycle_defs  using all by auto
  qed
qed

(*Any strongly connected subgraph must have a basic cycle*)
lemma scsg_has_basicCycle:"V' \<noteq> {} \<Longrightarrow> scsg V' E' \<Longrightarrow> \<exists>c. basicCycle c \<and> set c \<subseteq> V'"
  unfolding scsg_def Graph.scg_def Graph.pathCon_def set_nemp
  apply(clarsimp)
  subgoal for v
    using Graph.cycleG_def[of V' E', symmetric]
                          cycleG_contains_basicCycle[of ] 
      by (metis Graph.path_set basic_trans_rules(23)
          cycle_subgr) . 


(*Any strongly connected subgraph must have a basic cycle from a given node within the graph*)
lemma scsg_node_in_basic_cycle:
  assumes "v \<in> V'"
  assumes "scsg V' E'"
  shows "\<exists>c. basicCycle c \<and> v \<in> set c \<and> set c \<subseteq> V'"
proof -
  (* 1. Strong connectivity implies a path from v back to v *)
  have pathConn:"Graph.pathCon V' E' v v" using scsg_paths[OF assms(2)] assms(1) by auto

  then obtain p where p:"Graph.pathG V' E' p" "hd p = v" "last p = v" "length p > 1"
    unfolding Graph.pathCon_def using Graph.not_path_Nil path_length_ge2 
    by (metis Graph.path_length_ge2 Suc_1 Suc_to_right
        not_numeral_le_zero nz_le_conv_less
        verit_comp_simplify1(3))

  hence cycFrom:"Graph.cycleFrom V' E' v p" unfolding Graph.cycleFrom_def Graph.cycleG_def by auto


  (* 2. Define the set of all such cycles containing v *)
  let ?Cycles = "{p. Graph.cycleFrom V' E' v p}"

  let ?min_len = "Least (\<lambda>p. p \<in> length ` ?Cycles)"
  (* 3. Pick the shortest cycle in that set *)
  from cycFrom have cyc_nemp: "?Cycles \<noteq> {}" by blast
  then have len_nemp: "length ` ?Cycles \<noteq> {}"  by auto

  then obtain p_min where
    pmin_mem: "p_min \<in> ?Cycles" and
    pmin_len: "length p_min = ?min_len"
    using cyc_nemp LeastI_ex  unfolding image_iff
    by (smt (verit, best) equals0I)

  hence p_min_least:"\<forall>p'. p' \<in> ?Cycles \<longrightarrow> length p_min \<le> length p'"  by (simp add: Least_le)
  also have p_min_cyc:"Graph.cycleG V' E' p_min"
    using pmin_mem unfolding Graph.cycleFrom_def 
    by (metis Graph.scsg.elims(2) assms(2) cycle_subgr
        mem_Collect_eq)

  have p_min_cycF:"cycleG p_min"
    using pmin_mem unfolding Graph.cycleFrom_def 
    by (metis Graph.scsg.elims(2) assms(2) cycle_subgr
        mem_Collect_eq)


   have v_in_pmin:"v \<in> set p_min" 
    using pmin_mem unfolding Graph.cycleFrom_def 
    by (metis (lifting) Graph.cycleG_def Graph.not_path_Nil
        list.set_sel(1) mem_Collect_eq)

  hence v_in_pmin:"v \<in> set (butlast p_min)" using p_min_cyc[unfolded Graph.cycleG_def] 
    by (smt (verit, ccfv_threshold) Graph.cycleFrom_def Graph.not_path_Nil
        Graph.pathG.simps butlast.simps(2) butlast_snoc hd_append2 list.sel(1)
        list.set_intros(1) list.set_sel(1) mem_Collect_eq pmin_mem split_list_first)

  have v_loc: "hd p_min = v" "last p_min = v" using pmin_mem unfolding Graph.cycleFrom_def Graph.cycleG_def by auto



  (* 4. The shortest cycle must be distinct (basic) *)
  have "basicCycle p_min"
  proof (rule ccontr)
    assume "\<not> basicCycle p_min"
    hence "\<not> distinct (butlast p_min)" unfolding basicCycle_def using p_min_cycF by auto
    then obtain xs y ys zs where split: "butlast p_min = xs @ y # ys @ y # zs"
      using not_distinct_decomp by fastforce 

    let ?c' = "y # ys @ [y]"

    have pathG_butlast:"Graph.pathG V' E' (butlast p_min)" using p_min_cyc[unfolded Graph.cycleG_def] split Graph.pathG.cases by fastforce 
    hence "Graph.pathG V' E' ?c'" unfolding split using Graph.path_appendR[of V' E' xs "y # ys @ y # zs"] Graph.path_appendL[of V' E' "y # ys @ [y]"] by auto

    (* If p_min is not distinct, you could construct a shorter cycle.
       Either v is in the sub-loop, it contradicts p_min being shortest.
       OR If v is in the 'xs' or 'zs' part, you can snip out the y-y loop to get 
       a shorter v-v cycle. *)
    hence cyc_c':"Graph.cycleG V' E' ?c'" unfolding Graph.cycleG_def by auto


    have cyc_l:"Graph.cycleG V' E' (xs @ y # zs @ [v])"
      unfolding Graph.cycleG_def
      using v_loc split
      using p_min_cyc[unfolded Graph.cycleG_def] 
      using append_butlast_last_id[of p_min, OF Graph.cycleG_not_nil[OF p_min_cyc], symmetric]
      apply-apply(rule conjI)
      subgoal apply(cases xs)
        subgoal apply(cases zs) 
          subgoal using Graph.path_appendR[of V' E' "y # ys" "[y, v]"] by auto
          subgoal for a ls using Graph.path_appendR[of V' E' "y # ys" "y # a # ls @ [v]"] by auto .
        subgoal for x' xs' apply(cases zs) 
          subgoal using Graph.path_append_hd[of V' E' "v # xs'" "[y, v]"]                     
                        Graph.path_appendR[of V' E' "x' # xs' @ y # ys" "[y, v]"]
                        Graph.path_appendL[of V' E' "x' # xs' @ [y]" "ys @ [y, v]"] by auto
          subgoal for z' zs' apply simp
            apply(rule Graph.path_append_hd[of V' E' "v # xs' @ [y]" "z' # zs' @ [v]", 
                                 OF _ Graph.path_appendR[of V' E' "x' # xs' @ y # ys @ [y]" "z' # zs' @ [v]"],
                                 unfolded list_unf]) 
              using Graph.path_appendM[of V' E' "x' # xs' @ y # ys" "[y,z']" " zs' @ [v]"]
              using Graph.path_appendL[of V' E' "x' # xs' @ [y]" "ys @ y # z' # zs' @ [v]"] 
              using Graph.path_append_hd[of V' E' "v # xs'" "[y, z']"] by auto . .
        by (metis Nil_is_append_conv hd_append last.simps last_append list.distinct(1)
            list.sel(1))

      have length_smaller:"length ?c' < length p_min" 
                          "length (xs @ y # zs @ [v]) < length p_min"
        using append_butlast_last_id[of p_min, OF cycleG_not_nil[OF p_min_cycF], unfolded split v_loc] 
        by auto

    have "v \<in> set ?c' \<or> v \<in> set (xs @ y # zs @ [v])" using  v_in_pmin[unfolded split] by auto

    thus "HOL.False"
      apply-apply(elim disjE)
      subgoal apply(drule Graph.cycle_rotate_set[OF cyc_c', of v], clarify)
        subgoal for ndl' using p_min_least 
          apply-apply(elim allE[of _ ndl'] impE, simp add: Graph.cycleFrom_def)
          using length_smaller by auto .
      subgoal apply(drule Graph.cycle_rotate_set[OF cyc_l, of v], clarify)
        subgoal for ndl' using p_min_least 
          apply-apply(elim allE[of _ ndl'] impE, simp add: Graph.cycleFrom_def)
          using length_smaller by auto . .
  qed

  with \<open>p_min \<in> ?Cycles\<close> show ?thesis 
    apply-apply(rule exI[of _ p_min], intro conjI, simp)
    apply (metis Graph.cycleFrom_def basicCycle_not_nil
        hd_in_set mem_Collect_eq)
    by (meson Graph.cycleFrom_def Graph.cycleG_def
        Graph.path_set mem_Collect_eq)
qed


(********)

(* There exists a path starting in cycle c1 and ending in cycle c2 *)
definition connectedCycles :: "'node list \<Rightarrow> 'node list \<Rightarrow> bool" where
 "connectedCycles c1 c2 \<equiv> (\<exists>p. pathG p \<and> hd p \<in> set c1 \<and> last p \<in> set c2)"

lemma connectedCyclesE:"connectedCycles c1 c2 \<Longrightarrow> (\<And>p. pathG p \<Longrightarrow>
         hd p \<in> set c1 \<Longrightarrow> last p \<in> set c2 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding connectedCycles_def by auto


(* Main Definition *)
definition unicyclesGraph :: bool where
  "unicyclesGraph \<equiv> 
    \<forall>c c'. basicCycle c \<and> basicCycle c' \<longrightarrow> 
      (connectedCycles c c' \<and> connectedCycles c' c) \<longrightarrow> set c = set c'"

lemma unicyclesGraphI:"(\<And>c c'.
       connectedCycles c c' \<Longrightarrow>
       basicCycle c \<Longrightarrow>
       basicCycle c' \<Longrightarrow>
       connectedCycles c' c \<Longrightarrow> set c = set c') \<Longrightarrow> unicyclesGraph"
  unfolding unicyclesGraph_def by auto

lemma unicyclesGraphI':"(\<And>c c' p.
       pathG p \<Longrightarrow>
       hd p \<in> set c \<Longrightarrow>
       last p \<in> set c' \<Longrightarrow>
       basicCycle c \<Longrightarrow>
       basicCycle c' \<Longrightarrow>
       connectedCycles c' c \<Longrightarrow> set c = set c') \<Longrightarrow> unicyclesGraph"
  unfolding unicyclesGraph_def connectedCycles_def by auto

lemma basicCycle_unique_successor:
  assumes "unicyclesGraph"
  assumes "basicCycle c"
  assumes "i < length c - 1"
  assumes "edge (c ! i) v" "v \<in> set (butlast c)"
  shows "v = c ! (Suc i)"
proof (rule ccontr)
  assume assm:"v \<noteq> c ! Suc i"
  
  from assms(2) have pG: "pathG c" and dist: "distinct (butlast c)" and cyc: "cycleG c"
    unfolding basicCycle_def using cycleG_def by auto

  hence c_Suc_in:"c ! Suc i \<in> set (butlast c)" using assms basicCycle_set_eq[OF assms(2)] 
    by (metis diff_Suc_1 diff_less_Suc in_set_conv_nth less_trans_Suc
        not_less_less_Suc_eq)
  have hd_eq:"hd (butlast c) = hd c"  by (metis append_butlast_last_id assms(5) hd_append2 list.set(1) memb_imp_not_empty not_path_Nil pG)

  (*There must be a strictly smaller cycle which uses v*)
  obtain c_alt where alt: "basicCycle c_alt" "set c_alt \<subseteq> set c" 
                          "v \<in> set c_alt" "(c!i) \<in> set c_alt" 
                          "(c!Suc i) \<notin> set c_alt" using basicCycle_smaller_alt[OF assms(2-) assm] by blast
  
  (*Because c and c_alt share nodes (like v), they are connectedCycles.*)
  have "connectedCycles c c_alt" "connectedCycles c_alt c"
    unfolding connectedCycles_def 
    using alt assms(2) \<open>v \<in> set c_alt\<close> assms(5) 
    by (metis alt(1,2) basicCycle_def basicCycle_defs cycleG_not_nil list.set_sel(1)
        subset_code(1) basicCycle_set_eq)+

  (*By the unicyclesGraph property, their sets must be equal.*) 
  with assms(1) alt(1) assms(2) have "set c_alt = set c" unfolding unicyclesGraph_def by blast

  (*if v \<noteq> c ! (Suc i), c_alt is a proper subset of c, contradiction.*)
  thus "HOL.False" using \<open>v \<noteq> c ! Suc i\<close> using alt 
    by (metis One_nat_def Suc_diff_Suc Suc_mono assms(3) cyc cycleG_not_nil
        length_greater_0_conv minus_nat.diff_0 nth_mem)
qed


(*In a unicycles graph, the strongly connected subgraphs are exactly the (uni)cycles.*)
lemma scsg_in_unicycles_is_basicCycle:
assumes "unicyclesGraph"
        "V' \<noteq> {}"
        "scsg V' E'"
      shows "\<exists>c. basicCycle c \<and> set c = V'"
proof (rule ccontr, erule cycle_elim)
  assume notFull:"\<forall>c. basicCycle c \<longrightarrow> set c \<noteq> V'"
  obtain c1 where cycle1: "basicCycle c1" "set c1 \<subseteq> V'" using scsg_has_basicCycle[OF assms(2,3)] by auto
  
  then obtain c' where c':"c' \<in> set c1" using basicCycle_not_nil by blast

  from cycle1 obtain v where v:"v \<in> V'" "v \<notin> set c1" using notFull by auto

  then obtain c2 where cycle2:"basicCycle c2" "v \<in> set c2" "set c2 \<subseteq> V'"
    using scsg_node_in_basic_cycle[OF v(1) assms(3)] by blast

  then have cycles_neq:"set c1 \<noteq> set c2"  using v(2) by auto

  note basicCycles = cycle1(1) cycle2(1)

  have cc1:"connectedCycles c1 c2" 
    unfolding connectedCycles_def 
    using scsg_paths[OF assms(3), simplified]
    apply-apply(erule allE[of _ c'], elim allE[of _ v] impE)
    subgoal using c' cycle1(2) v(1) by blast
    subgoal unfolding Graph.pathCon_def  using Graph.scsg_def assms(3) c' cycle2(2) path_subgr by blast .


  have cc2:"connectedCycles c2 c1" 
    unfolding connectedCycles_def 
    using scsg_paths[OF assms(3), simplified]
    apply-apply(erule allE[of _ v], elim allE[of _ c'] impE)
    subgoal using c' cycle1(2) v(1) by blast
    subgoal unfolding Graph.pathCon_def  using Graph.scsg_def assms(3) c' cycle2(2) path_subgr by blast .


  note connectedCycles = cc1 cc2

  show "HOL.False"
    using assms(1)[unfolded unicyclesGraph_def] basicCycles cc1 cc2
    apply-by(erule allE[of _ c1], elim allE[of _ c2] impE conjE, auto simp: cycles_neq)
qed


(*Consequently, the "limit" of an ipath is not just any SCSG, but the unique cycle it reaches:*)
lemma unicycle_limit_is_basic_cycle:
  assumes "unicyclesGraph"
  assumes "finite Node"
  assumes "ipath \<pi>"
  shows "\<exists>c. basicCycle c \<and> limitS \<pi> = set (butlast c)"
  using scsg_in_unicycles_is_basicCycle[OF assms(1) limitS_ne[OF assms(2,3)] scsg_limit[OF assms(2,3)]]
        basicCycle_set_eq by auto

(*Likewise the cycle order preserves the relation (limitR)*)
lemma limitS_limitR_edges:
  assumes "unicyclesGraph"
  assumes "finite Node"
  assumes "ipath \<pi>"
  assumes "limitS \<pi> = set (butlast c)"
  assumes "basicCycle c"
  shows "\<forall>i < length c - 1. (limitR \<pi>) (c ! i) (c ! Suc i)"
proof (rule allI, rule impI)
  fix i assume assm:"i < length c - 1"
  let ?u = "c ! i"
  let ?v = "c ! Suc i"

  (* 1. ?u is visited infinitely often *)
  have u_in_lim:"?u \<in> limitS \<pi>" using assms(4) by (metis assm length_butlast nth_butlast nth_mem)
  
  (* 2. In a unicycles graph, the only way to leave ?u and stay in 
        the limitS is via the edge (?u, ?v) *)
  have edge_dist:"\<forall>v'. edge ?u v' \<and> v' \<in> limitS \<pi> \<longrightarrow> v' = ?v"
    using basicCycle_unique_successor[OF assms(1,5) assm, unfolded assms(4)[symmetric] ] by auto

  obtain i' where ipaths:"Graph.ipath (limitS \<pi>) (limitR \<pi>) (sdrop i' \<pi>)"
    using ipath_sdrop_limit[OF assms(2,3)] by blast

  (*path eventually stays in limit*)
  hence n':"\<forall>n\<ge>i'. \<pi> !! n \<in> limitS \<pi>" unfolding Graph.ipath_iff_snth sdrop_snth by (metis less_eqE)

  (*so it will visit u*)
  then obtain n where n: "n \<ge> i'" "?u = \<pi> !! n"
    using limitS_infinite_visits[OF u_in_lim, of i'] by auto

  have lim:"\<pi> !! (Suc n) \<in> limitS \<pi>" 
    using n' n(1) le_Suc_eq by blast

  (*The next step must be v*)
  have edge: "edge (\<pi> !! n) (\<pi> !! (Suc n))" 
    using assms(3) unfolding ipath_def by (simp add: alw_holds2_iff_snth)

  hence edge':"edge ?u (\<pi> !! (Suc n))" using n(2) by simp

  hence eq:"?v = \<pi> !! (Suc n)" using edge_dist lim by auto

  show "(limitR \<pi>) ?u ?v"
    using n(1) ipaths[unfolded Graph.ipath_iff_snth]
    unfolding eq n(2) sdrop_snth  apply-by(erule allE[of _ "n-i'"], simp)

qed

(*Thus for a unicyles graph we eventually reach the limit of the graph
  Which is a basic cycle infinitely repeating*)
lemma unicycle_lasso:
  assumes "unicyclesGraph"
  assumes "finite Node"
  assumes "ipath \<pi>"
  shows "\<exists>v u. \<pi> = v @- srepeat u \<and> basicCycle (u @ [hd u])"
proof-
  (* 1. Obtain the SCSG of the limit set *)
  have "scsg (limitS \<pi>) (limitR \<pi>)" using scsg_limit[OF assms(2,3)] .

  (* 2. From unicycles graph then the limit is a basic cycle*)
  then obtain c where c_prop:"basicCycle c" "set (butlast c) = limitS \<pi>"
    using unicycle_limit_is_basic_cycle[OF assms] by blast

  also obtain i where final_ipath:"Graph.ipath (set (butlast c)) (limitR \<pi>) (sdrop i \<pi>)" 
    using ipath_sdrop_limit[OF assms(2,3)] calculation by auto

  hence hd_in:"shd (sdrop i \<pi>) \<in> set c" using basicCycle_set_eq[OF c_prop(1)] Graph.sset_ipath by blast

  (*Rotate the basic cycle to find the entry point of the ipath*)
  obtain c' where c'_prop:"basicCycle c'" "set c' = set c" "hd c' = shd (sdrop i \<pi>)"
                          "last c' = shd (sdrop i \<pi>)" "length c' = length c" 
    using basicCycle_rotate_set[OF c_prop(1), of "shd (sdrop i \<pi>)", OF hd_in] by blast

  hence lim_c':"limitS \<pi> = set (butlast c')" 
    using c_prop unfolding basicCycle_def 
    using Graph.basicCycle_set_eq c'_prop(1) c_prop(1)
    by blast

    have "\<And>n. (sdrop i \<pi>) !! n = (butlast c') ! (n mod length (butlast c'))"
    subgoal for n proof (induct n rule: nat_less_induct)
      fix n
      assume IH: "\<forall>m < n. (sdrop i \<pi>) !! m = (butlast c') ! (m mod length (butlast c'))"
      show "(sdrop i \<pi>) !! n = (butlast c') ! (n mod length (butlast c'))"
      proof (cases n)
        case 0
        then show ?thesis using c'_prop 
          by (metis List.set_empty assms(2,3) basicCycle_set_eq c_prop(2) hd_conv_nth
              length_greater_0_conv limitS_ne mod_less nth_butlast snth.simps(1))
      next
        case (Suc k)
        have c'_eq:"butlast c' ! (n mod length (butlast c')) =c' ! Suc (k mod length (butlast c'))"
          by (metis Graph.basicCycle_set_eq Suc c'_prop(1,3,4) hd_conv_nth last_conv_nth
              length_butlast length_greater_0_conv list.size(3) mod_Suc mod_less_divisor
              nth_butlast set_empty2)
        also have k_le:"k mod length (butlast c') < length c' - 1" using Suc length_butlast
          by (metis Graph.ipath_iff_snth c_prop(2) final_ipath length_butlast
              length_pos_if_in_set lim_c' mod_less_divisor numeral_nat(7))

        (* 1. From IH, (sdrop i \<pi>) !! k is in the cycle *)
        have drop_in:"(sdrop i \<pi>) !! n \<in> set (butlast c')" 
          by (metis Graph.ipath_iff_snth c_prop(2) final_ipath lim_c' sdrop_snth)

        then have sdrop_eq:"(sdrop i \<pi>) !! k = (butlast c') ! (k mod length (butlast c'))"
          using IH Suc by auto

        (* 2. The edge ((sdrop i \<pi>) !! k, (sdrop i \<pi>) !! Suc k) is in limitR *)
        then have "(limitR \<pi>) ((sdrop i \<pi>) !! k) ((sdrop i \<pi>) !! Suc k)"
          using final_ipath  Graph.ipath_iff_snth by blast

        (* 3. In a unicycles graph, the only edge from (butlast c') ! k 
              staying in the SCSG is to (butlast c') ! (Suc k) *)
        moreover have "(limitR \<pi>) ((butlast c') ! (k mod length (butlast c')))
                                  ((butlast c') ! (Suc k mod length (butlast c')))"
          using limitS_limitR_edges[OF assms(1,2,3) lim_c' c'_prop(1)] 
          by (metis Suc calculation(1) k_le length_butlast nth_butlast)

        ultimately show ?thesis unfolding c'_eq
          apply-apply(rule basicCycle_unique_successor[OF assms(1) c'_prop(1), 
                      of "(k mod length (butlast c'))" "(sdrop i \<pi> !! n)"])
          subgoal by (metis assms(2,3) length_butlast length_greater_0_conv lim_c' limitS_ne list.set(1) mod_less_divisor)
          subgoal using limitR_R[OF assms(3)] sdrop_eq by (metis Suc k_le length_butlast nth_butlast)
          subgoal using drop_in by auto .
      qed
    qed .

    hence cyc_repeat: "srepeat (butlast c') = sdrop i \<pi>"
      by (metis Graph.basicCycle_set_eq c'_prop(1,2) hd_in list.set(1) set_nemp
          snth_equalityI srepeat_snth)

  (* 4. Relate limitS to the srepeat structure *)
  (* Since the path is infinite and the graph is finite, 
     it must eventually enter and stay in limitS \<pi>. *)
  show ?thesis apply(rule exI[of _ "stake i \<pi>"], intro exI[of _ "butlast c'"] conjI)
    subgoal unfolding cyc_repeat by simp
    subgoal using basicCycle_ge2[OF c'_prop(1)] c'_prop(1)[unfolded basicCycle_defs] 
      by (simp add: c'_prop(1) hd_butlast le_simps(3) numeral_2_eq_2) .
qed


end

context Sloped_Graph
begin

(*This is the descending graph *)
definition "cycleDescends ndl \<equiv> (\<exists>n Pl. n \<noteq> 0 \<and> wfLabL (repeat n (butlast ndl) @ [last ndl]) Pl \<and> 
                                         descentPath (repeat n (butlast ndl) @ [last ndl]) Pl \<and> hd Pl = last Pl)"

lemma cycle_descentIPathS_imp_cycleDescends: 
assumes ndl: "cycleG ndl" and d: "descentIpathS (srepeat (butlast ndl)) Ps" 
shows "cycleDescends ndl"
  using cycle_descentIPathS_srepeat_imp_descentPath_repeat[OF assms]
  by (auto simp: cycleDescends_def)


lemma cycle_descentIPath_imp_cycleDescends: 
assumes ndl: "cycleG ndl" and d: "descentIpath (srepeat (butlast ndl)) Ps" 
shows "cycleDescends ndl"
  using srepeat_cycle_descentIpath_imp_descentIpath[OF assms]
        cycle_descentIPathS_imp_cycleDescends[OF assms(1)] by auto

lemma cycleDescends_imp_descentIPathS:
assumes ndl: "cycleG ndl" and desc: "cycleDescends ndl"
shows "\<exists>Ps. descentIpathS (srepeat (butlast ndl)) Ps"
  using assms(2)[unfolded cycleDescends_def]
  apply-apply(clarify)
  using cycle_descentPath_repeat_imp_descentIPathS_srepeat[OF assms(1)] by auto

definition SimplyDescendingGraph :: bool where  "SimplyDescendingGraph \<equiv> \<forall>ndl. basicCycle ndl \<longrightarrow> cycleDescends ndl" 

lemma SimplyDescendingGraphD: "SimplyDescendingGraph \<Longrightarrow> basicCycle c \<Longrightarrow> cycleDescends c"
  unfolding SimplyDescendingGraph_def by auto

lemma SimplyDescendingGraphI:"(\<And>c. ipath (srepeat (butlast c)) \<Longrightarrow> basicCycle c \<Longrightarrow> cycleDescends c) \<Longrightarrow> SimplyDescendingGraph"
  unfolding SimplyDescendingGraph_def basicCycle_def
  by (simp add: cycle_srepeat_ipath)


lemma SimplyDescendingGraphI':"(\<And>c. basicCycle c \<Longrightarrow> cycleDescends c) \<Longrightarrow> SimplyDescendingGraph"
  unfolding SimplyDescendingGraph_def basicCycle_def by auto

lemma allCyclesDescendI:"(\<And>c. ipath (srepeat (butlast c)) \<Longrightarrow> basicCycle c \<Longrightarrow> (\<exists>n Pl.
               n \<noteq> 0 \<and>
               wfLabL
                (repeat n (butlast c) @ [last c])
                Pl \<and>
               descentPath
                (repeat n (butlast c) @ [last c])
                Pl \<and>
               hd Pl = last Pl)) \<Longrightarrow> SimplyDescendingGraph"
  unfolding SimplyDescendingGraph_def cycleDescends_def
  using basicCycle_def
  by (simp add: cycle_srepeat_ipath)

  
proposition InfiniteDescent_implies_SimplyDescendingGraph: 
"InfiniteDescent \<Longrightarrow> SimplyDescendingGraph"
  unfolding SimplyDescendingGraph_def InfiniteDescent_def 
  using cycle_srepeat_ipath cycle_descentIPath_imp_cycleDescends basicCycle_def by blast


proposition SimplyDescendingUnicyclesGraph_implies_InfiniteDescent:
  assumes "unicyclesGraph"
  shows "SimplyDescendingGraph \<Longrightarrow> InfiniteDescent"
proof(rule InfiniteDescentI)
  fix nds
  assume SDG: "SimplyDescendingGraph" and
         ipath:"ipath nds"

  obtain v u where nds:"nds = v @- srepeat u" and cyc:"basicCycle (u @ [hd u])"
    using unicycle_lasso[OF assms Node_finite ipath] by auto

  then obtain Ps where descentS:"descentIpathS (srepeat u) Ps"
    using SDG[unfolded SimplyDescendingGraph_def]
    apply-apply(elim allE[of _ "u @ [hd u]"] impE exE conjE, assumption)
    using cycleDescends_imp_descentIPathS[of "u @ [hd u]"] basicCycle_def  by auto

  hence descent:"descentIpath (srepeat u) Ps" using descentIpathS_imp_descentIpath by auto

  then obtain Ps' where Ps':"descentIpath (v @- srepeat u) Ps'"
    using descentIpath_sdrop_any[of "length v", of "v @- srepeat u" Ps] 
    unfolding sdrop_shift_length' by auto

  thus "\<exists>Ps. descentIpath nds Ps" unfolding nds by auto
qed

theorem DescendingUnicyclesCriterion:
  assumes "unicyclesGraph"
  shows "InfiniteDescent \<longleftrightarrow> SimplyDescendingGraph"
  using InfiniteDescent_implies_SimplyDescendingGraph
        SimplyDescendingUnicyclesGraph_implies_InfiniteDescent[OF assms]
  by auto


end

end 
