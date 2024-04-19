(*<*)
theory Monitor
  imports Checker_Code
begin
(*>*)

section \<open>Unverified Explanation-Producing Monitoring Algorithm\<close>

fun merge_part2_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d set \<times> 'a) list \<Rightarrow> ('d set \<times> 'b) list \<Rightarrow> ('d set \<times> 'c) list" where
  "merge_part2_raw f [] _ = []"  
| "merge_part2_raw f ((P1, v1) # part1) part2 = 
    (let part12 = List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some(P1 \<inter> P2, f v1 v2) else None) part2 in
     let part2not1 = List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some(P2 - P1, v2) else None) part2 in
     part12 @ (merge_part2_raw f part1 part2not1))"

fun merge_part3_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'e) \<Rightarrow> ('d set \<times> 'a) list \<Rightarrow> ('d set \<times> 'b) list \<Rightarrow> ('d set \<times> 'c) list \<Rightarrow> ('d set \<times> 'e) list" where
  "merge_part3_raw f [] _ _ = []" 
| "merge_part3_raw f _ [] _ = []" 
| "merge_part3_raw f _ _ [] = []"
| "merge_part3_raw f part1 part2 part3 = merge_part2_raw (\<lambda>pt3 f'. f' pt3) part3 (merge_part2_raw f part1 part2)"

lemma partition_on_empty_iff: 
  "partition_on X \<P> \<Longrightarrow> \<P> = {} \<longleftrightarrow> X = {}"
  "partition_on X \<P> \<Longrightarrow> \<P> \<noteq> {} \<longleftrightarrow> X \<noteq> {}"
  by (auto simp: partition_on_def)

lemma wf_part_list_filter_inter: 
  defines "inP1 P1 f v1 part2 
    \<equiv> List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some(P1 \<inter> P2, f v1 v2) else None) part2"
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "partition_on X (set (map fst part2))"
  shows "partition_on P1 (set (map fst (inP1 P1 f v1 part2)))"
    and "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst (part2)) \<Longrightarrow>
    distinct (map fst (inP1 P1 f v1 part2))"
proof (rule partition_onI)
  show "\<Union> (set (map fst (inP1 P1 f v1 part2))) = P1"
  proof -
    have "\<exists>P2. (P1 \<inter> P2 \<noteq> {} \<longrightarrow> (\<exists>v2. (P2, v2) \<in> set part2) \<and> x \<in> P2) \<and> P1 \<inter> P2 \<noteq> {}"
      if "\<Union> (fst ` set part2) = P1 \<union> \<Union> (fst ` set part1)" and "x \<in> P1" for x
      using that by (metis (no_types, lifting) Int_iff UN_iff Un_Int_eq(3) empty_iff prod.collapse)
    with partition_onD1[OF assms(2)] partition_onD1[OF assms(3)] show ?thesis
      by (auto simp: map_filter_def inP1_def split: if_splits)
  qed
  show "\<And>A1 A2. A1 \<in> set (map fst (inP1 P1 f v1 part2)) \<Longrightarrow>
    A2 \<in> set (map fst (inP1 P1 f v1 part2)) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(2)] partition_onD2[OF assms(3)]
    by (force simp: disjnt_iff map_filter_def disjoint_def inP1_def split: if_splits)
  show "{} \<notin> set (map fst (inP1 P1 f v1 part2))" 
    using assms
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst part2) \<Longrightarrow>
    distinct (map fst (inP1 P1 f v1 part2))"
    using partition_onD2[OF assms(3), unfolded disjoint_def, simplified, rule_format]
    by (clarsimp simp: inP1_def map_filter_def distinct_map inj_on_def Ball_def) blast
qed

lemma wf_part_list_filter_minus: 
  defines "notinP2 P1 f v1 part2 
    \<equiv> List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some(P2 - P1, v2) else None) part2"
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "partition_on X (set (map fst part2))"
  shows "partition_on (X - P1) (set (map fst (notinP2 P1 f v1 part2)))"
    and "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst (part2)) \<Longrightarrow>
      distinct (map fst (notinP2 P1 f v1 part2))"
proof (rule partition_onI)
  show "\<Union> (set (map fst (notinP2 P1 f v1 part2))) = X - P1"
  proof -
    have "\<exists>P2. ((\<exists>x\<in>P2. x \<notin> P1) \<longrightarrow> (\<exists>v2. (P2, v2) \<in> set part2)) \<and> (\<exists>x\<in>P2. x \<notin> P1) \<and> x \<in> P2"
      if "\<Union> (fst ` set part2) = P1 \<union> \<Union> (fst ` set part1)" "x \<notin> P1" "(P1', v1) \<in> set part1" "x \<in> P1'" for x P1' v1
      using that by (metis (no_types, lifting) UN_iff Un_iff fst_conv prod.collapse)
    with partition_onD1[OF assms(2)] partition_onD1[OF assms(3)] show ?thesis
      by (auto simp: map_filter_def subset_eq split_beta notinP2_def split: if_splits)
  qed
  show "\<And>A1 A2. A1 \<in> set (map fst (notinP2 P1 f v1 part2)) \<Longrightarrow>
    A2 \<in> set (map fst (notinP2 P1 f v1 part2)) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(3)]
    by (auto simp: disjnt_def map_filter_def disjoint_def notinP2_def Ball_def Bex_def image_iff split: if_splits)
  show "{} \<notin> set (map fst (notinP2 P1 f v1 part2))" 
    using assms
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst part2) \<Longrightarrow>
    distinct (map fst ((notinP2 P1 f v1 part2)))"
    using partition_onD2[OF assms(3), unfolded disjoint_def]
    by (clarsimp simp: notinP2_def map_filter_def distinct_map inj_on_def Ball_def Bex_def image_iff) blast
qed

lemma wf_part_list_tail: 
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "distinct (map fst ((P1, v1) # part1))"
  shows "partition_on (X - P1) (set (map fst part1))"
    and "distinct (map fst part1)"
proof (rule partition_onI)
  show "\<Union> (set (map fst part1)) = X - P1"
    using partition_onD1[OF assms(1)] partition_onD2[OF assms(1)] assms(2)
    by (auto simp: disjoint_def image_iff)
  show "\<And>A1 A2. A1 \<in> set (map fst part1) \<Longrightarrow> A2 \<in> set (map fst part1) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(1)]
    by (clarsimp simp: disjnt_def disjoint_def)
      (smt (verit, ccfv_SIG) Diff_disjoint Int_Diff Int_commute fst_conv)
  show "{} \<notin> set (map fst part1)" 
    using partition_onD3[OF assms(1)]
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst (part1))"
    using assms(2)
    by auto
qed

lemma partition_on_append: "partition_on X (set xs) \<Longrightarrow> partition_on Y (set ys) \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow>
  partition_on (X \<union> Y) (set (xs @ ys))"
  by (auto simp: partition_on_def intro!: disjoint_union)

lemma wf_part_list_merge_part2_raw: 
  "partition_on X (set (map fst part1)) \<and> distinct (map fst part1) \<Longrightarrow>
   partition_on X (set (map fst part2)) \<and> distinct (map fst part2) \<Longrightarrow>
   partition_on X (set (map fst (merge_part2_raw f part1 part2))) 
    \<and> distinct (map fst (merge_part2_raw f part1 part2))"
proof(induct f part1 part2 arbitrary: X rule: merge_part2_raw.induct)
  case (2 f P1 v1 part1 part2)
  let ?inP1 = "List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some (P1 \<inter> P2, f v1 v2) else None) part2"
    and ?notinP1 = "List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some (P2 - P1, v2) else None) part2"
  have "P1 \<union> X = X"
    using "2.prems"
    by (auto simp: partition_on_def)
  have wf_part1: "partition_on (X - P1) (set (map fst part1))"
    "distinct (map fst part1)"
    using wf_part_list_tail "2.prems" by auto
  moreover have wf_notinP1: "partition_on (X - P1) (set (map fst ?notinP1))" 
    "distinct (map fst (?notinP1))"
    using wf_part_list_filter_minus[OF 2(2)[THEN conjunct1]] 
      "2.prems" by auto
  ultimately have IH: "partition_on (X - P1) (set (map fst (merge_part2_raw f part1 (?notinP1))))"
    "distinct (map fst (merge_part2_raw f part1 (?notinP1)))"
    using "2.hyps"[OF refl refl] by auto
  moreover have wf_inP1: "partition_on P1 (set (map fst ?inP1))" "distinct (map fst ?inP1)"
    using wf_part_list_filter_inter[OF 2(2)[THEN conjunct1]]
      "2.prems" by auto
  moreover have "(fst ` set ?inP1) \<inter> (fst ` set (merge_part2_raw f part1 (?notinP1))) = {}"
    using IH(1)[THEN partition_onD1]
    by (fastforce simp: map_filter_def split: prod.splits if_splits)
  ultimately show ?case 
    using partition_on_append[OF wf_inP1(1) IH(1)] \<open>P1 \<union> X = X\<close> wf_inP1(2) IH(2)
    by simp
qed simp

lemma wf_part_list_merge_part3_raw: 
  "partition_on X (set (map fst part1)) \<and> distinct (map fst part1) \<Longrightarrow>
   partition_on X (set (map fst part2)) \<and> distinct (map fst part2) \<Longrightarrow>
   partition_on X (set (map fst part3)) \<and> distinct (map fst part3) \<Longrightarrow>
   partition_on X (set (map fst (merge_part3_raw f part1 part2 part3))) 
    \<and> distinct (map fst (merge_part3_raw f part1 part2 part3))"
proof(induct f part1 part2 part3 arbitrary: X rule: merge_part3_raw.induct)
  case (4 f v va vb vc vd ve)
  have "partition_on X (set (map fst (v # va))) \<and> distinct (map fst (vb # vc))"
    using 4 by blast
  moreover have "partition_on X (set (map fst (vb # vc))) \<and> distinct (map fst (vb # vc))"
    using 4 by blast
  ultimately have "partition_on X (set (map fst (merge_part2_raw f (v # va) (vb # vc)))) 
  \<and> distinct (map fst (merge_part2_raw f (v # va) (vb # vc)))"
    using wf_part_list_merge_part2_raw[of X "(v # va)" "(vb # vc)" f] 4
    by fastforce
  moreover have "partition_on X (set (map fst (vd # ve))) \<and> distinct (map fst (vd # ve))"
    using 4 by blast
  ultimately show ?case 
    using wf_part_list_merge_part2_raw[of X "(vd # ve)" "(merge_part2_raw f (v # va) (vb # vc))" "(\<lambda>pt3 f'. f' pt3)"]
    by simp
qed auto

lift_definition merge_part2 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part" is merge_part2_raw
  by (rule wf_part_list_merge_part2_raw)

lift_definition merge_part3 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part" is merge_part3_raw
  by (rule wf_part_list_merge_part3_raw)

definition proof_app :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof" (infixl "\<oplus>" 65) where
  "p \<oplus> q = (case (p, q) of
   (Inl (SHistorically i li sps), Inl q) \<Rightarrow> Inl (SHistorically (i+1) li (sps @ [q]))
 | (Inl (SAlways i hi sps), Inl q) \<Rightarrow> Inl (SAlways (i-1) hi (q # sps))
 | (Inl (SSince sp2 sp1s), Inl q) \<Rightarrow> Inl (SSince sp2 (sp1s @ [q]))
 | (Inl (SUntil sp1s sp2), Inl q) \<Rightarrow> Inl (SUntil (q # sp1s) sp2)
 | (Inr (VSince i vp1 vp2s), Inr q) \<Rightarrow> Inr (VSince (i+1) vp1 (vp2s @ [q]))
 | (Inr (VOnce i li vps), Inr q) \<Rightarrow> Inr (VOnce (i+1) li (vps @ [q]))
 | (Inr (VEventually i hi vps), Inr q) \<Rightarrow> Inr (VEventually (i-1) hi (q # vps))
 | (Inr (VSinceInf i li vp2s), Inr q) \<Rightarrow> Inr (VSinceInf (i+1) li (vp2s @ [q]))
 | (Inr (VUntil i vp2s vp1), Inr q) \<Rightarrow> Inr (VUntil (i-1) (q # vp2s) vp1)
 | (Inr (VUntilInf i hi vp2s), Inr q) \<Rightarrow> Inr (VUntilInf (i-1) hi (q # vp2s)))"

definition proof_incr :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof" where
  "proof_incr p = (case p of
   Inl (SOnce i sp) \<Rightarrow> Inl (SOnce (i+1) sp)
 | Inl (SEventually i sp) \<Rightarrow> Inl (SEventually (i-1) sp)
 | Inl (SHistorically i li sps) \<Rightarrow> Inl (SHistorically (i+1) li sps)
 | Inl (SAlways i hi sps) \<Rightarrow> Inl (SAlways (i-1) hi sps)
 | Inr (VSince i vp1 vp2s) \<Rightarrow> Inr (VSince (i+1) vp1 vp2s)
 | Inr (VOnce i li vps) \<Rightarrow> Inr (VOnce (i+1) li vps)
 | Inr (VEventually i hi vps) \<Rightarrow> Inr (VEventually (i-1) hi vps)
 | Inr (VHistorically i vp) \<Rightarrow> Inr (VHistorically (i+1) vp)
 | Inr (VAlways i vp) \<Rightarrow> Inr (VAlways (i-1) vp)
 | Inr (VSinceInf i li vp2s) \<Rightarrow> Inr (VSinceInf (i+1) li vp2s)
 | Inr (VUntil i vp2s vp1) \<Rightarrow> Inr (VUntil (i-1) vp2s vp1)
 | Inr (VUntilInf i hi vp2s) \<Rightarrow> Inr (VUntilInf (i-1) hi vp2s))"

definition min_list_wrt :: "(('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> bool) \<Rightarrow> ('n, 'd) proof list \<Rightarrow> ('n, 'd) proof" where
  "min_list_wrt r xs = hd [x \<leftarrow> xs. \<forall>y \<in> set xs. r x y]"

definition do_neg :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_neg p = (case p of
  Inl sp \<Rightarrow> [Inr (VNeg sp)]
| Inr vp \<Rightarrow> [Inl (SNeg vp)])"

definition do_or :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_or p1 p2 = (case (p1, p2) of
  (Inl sp1, Inl sp2) \<Rightarrow> [Inl (SOrL sp1), Inl (SOrR sp2)]
| (Inl sp1, Inr _  ) \<Rightarrow> [Inl (SOrL sp1)]
| (Inr _  , Inl sp2) \<Rightarrow> [Inl (SOrR sp2)]
| (Inr vp1, Inr vp2) \<Rightarrow> [Inr (VOr vp1 vp2)])"

definition do_and :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_and p1 p2 = (case (p1, p2) of
  (Inl sp1, Inl sp2) \<Rightarrow> [Inl (SAnd sp1 sp2)]
| (Inl _  , Inr vp2) \<Rightarrow> [Inr (VAndR vp2)]
| (Inr vp1, Inl _  ) \<Rightarrow> [Inr (VAndL vp1)]
| (Inr vp1, Inr vp2) \<Rightarrow> [Inr (VAndL vp1), Inr (VAndR vp2)])"

definition do_imp :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_imp p1 p2 = (case (p1, p2) of
  (Inl _  , Inl sp2) \<Rightarrow> [Inl (SImpR sp2)]
| (Inl sp1, Inr vp2) \<Rightarrow> [Inr (VImp sp1 vp2)]
| (Inr vp1, Inl sp2) \<Rightarrow> [Inl (SImpL vp1), Inl (SImpR sp2)]
| (Inr vp1, Inr _  ) \<Rightarrow> [Inl (SImpL vp1)])"

definition do_iff :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_iff p1 p2 = (case (p1, p2) of
  (Inl sp1, Inl sp2) \<Rightarrow> [Inl (SIffSS sp1 sp2)]
| (Inl sp1, Inr vp2) \<Rightarrow> [Inr (VIffSV sp1 vp2)]
| (Inr vp1, Inl sp2) \<Rightarrow> [Inr (VIffVS vp1 sp2)]
| (Inr vp1, Inr vp2) \<Rightarrow> [Inl (SIffVV vp1 vp2)])"

definition do_exists :: "'n \<Rightarrow> ('n, 'd::{default,linorder}) proof + ('d, ('n, 'd) proof) part \<Rightarrow> ('n, 'd) proof list" where
  "do_exists x p_part = (case p_part of
  Inl p \<Rightarrow> (case p of
    Inl sp \<Rightarrow> [Inl (SExists x default sp)]
  | Inr vp \<Rightarrow> [Inr (VExists x (trivial_part vp))])
| Inr part \<Rightarrow> (if (\<exists>x\<in>Vals part. isl x) then 
                map (\<lambda>(D,p). map_sum (SExists x (Min D)) id p) (filter (\<lambda>(_, p). isl p) (subsvals part))
              else
                [Inr (VExists x (map_part projr part))]))"

definition do_forall :: "'n \<Rightarrow> ('n, 'd::{default,linorder}) proof + ('d, ('n, 'd) proof) part \<Rightarrow> ('n, 'd) proof list" where
  "do_forall x p_part = (case p_part of
  Inl p \<Rightarrow> (case p of
    Inl sp \<Rightarrow> [Inl (SForall x (trivial_part sp))]
  | Inr vp \<Rightarrow> [Inr (VForall x default vp)])
| Inr part \<Rightarrow> (if (\<forall>x\<in>Vals part. isl x) then 
                [Inl (SForall x (map_part projl part))]
              else 
                map (\<lambda>(D,p). map_sum id (VForall x (Min D)) p) (filter (\<lambda>(_, p). \<not>isl p) (subsvals part))))"

definition do_prev :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_prev i I t p = (case (p, t < left I) of
  (Inl _ , True) \<Rightarrow> [Inr (VPrevOutL i)]
| (Inl sp, False) \<Rightarrow> (if mem t I then [Inl (SPrev sp)] else [Inr (VPrevOutR i)])
| (Inr vp, True) \<Rightarrow> [Inr (VPrev vp), Inr (VPrevOutL i)]
| (Inr vp, False) \<Rightarrow> (if mem t I then [Inr (VPrev vp)] else [Inr (VPrev vp), Inr (VPrevOutR i)]))"

definition do_next :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_next i I t p = (case (p, t < left I) of
  (Inl _ , True) \<Rightarrow> [Inr (VNextOutL i)]
| (Inl sp, False) \<Rightarrow> (if mem t I then [Inl (SNext sp)] else [Inr (VNextOutR i)])
| (Inr vp, True) \<Rightarrow> [Inr (VNext vp), Inr (VNextOutL i)]
| (Inr vp, False) \<Rightarrow> (if mem t I then [Inr (VNext vp)] else [Inr (VNext vp), Inr (VNextOutR i)]))"

definition do_once_base :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_once_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr vp', True) \<Rightarrow> [Inr (VOnce i i [vp'])]
| ( _ , False) \<Rightarrow> [Inr (VOnce i i [])])"

definition do_once :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_once i a p p' = (case (p, a = 0, p') of
  (Inl sp, True,  Inr _ ) \<Rightarrow> [Inl (SOnce i sp)]
| (Inl sp, True,  Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp'), Inl (SOnce i sp)]
| (Inl _ , False, Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp')]
| (Inl _ , False, Inr (VOnce _ li vps')) \<Rightarrow> [Inr (VOnce i li vps')]
| (Inr _ , True,  Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr vp, True,  Inr vp') \<Rightarrow> [(Inr vp') \<oplus> (Inr vp)]
| (Inr _ , False, Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr _ , False, Inr (VOnce _ li vps')) \<Rightarrow> [Inr (VOnce i li vps')])"

definition do_eventually_base :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_eventually_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SEventually i sp')]
| (Inr vp', True) \<Rightarrow> [Inr (VEventually i i [vp'])]
| ( _ , False) \<Rightarrow> [Inr (VEventually i i [])])"

definition do_eventually :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_eventually i a p p' = (case (p, a = 0, p') of
  (Inl sp, True,  Inr _ ) \<Rightarrow> [Inl (SEventually i sp)]
| (Inl sp, True,  Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp'), Inl (SEventually i sp)]
| (Inl _ , False, Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp')]
| (Inl _ , False, Inr (VEventually _ hi vps')) \<Rightarrow> [Inr (VEventually i hi vps')]
| (Inr _ , True,  Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp')]
| (Inr vp, True,  Inr vp') \<Rightarrow> [(Inr vp') \<oplus> (Inr vp)]
| (Inr _ , False, Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp')]
| (Inr _ , False, Inr (VEventually _ hi vps')) \<Rightarrow> [Inr (VEventually i hi vps')])"

definition do_historically_base :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_historically_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SHistorically i i [sp'])]
| (Inr vp', True) \<Rightarrow> [Inr (VHistorically i vp')]
| ( _ , False) \<Rightarrow> [Inl (SHistorically i i [])])"

definition do_historically :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_historically i a p p' = (case (p, a = 0, p') of
  (Inl _ , True,  Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp')]
| (Inl sp, True,  Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp)]
| (Inl _ , False, Inl (SHistorically _ li sps')) \<Rightarrow> [Inl (SHistorically i li sps')]
| (Inl _ , False, Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp')]
| (Inr vp, True,  Inl _ ) \<Rightarrow> [Inr (VHistorically i vp)]
| (Inr vp, True,  Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp), Inr (VHistorically i vp')]
| (Inr _ , False, Inl (SHistorically _ li sps')) \<Rightarrow> [Inl (SHistorically i li sps')]
| (Inr _ , False, Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp')])"

definition do_always_base :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_always_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SAlways i i [sp'])]
| (Inr vp', True) \<Rightarrow> [Inr (VAlways i vp')]
| ( _ , False) \<Rightarrow> [Inl (SAlways i i [])])"

definition do_always :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_always i a p p' = (case (p, a = 0, p') of
  (Inl _ , True,  Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')]
| (Inl sp, True,  Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp)]
| (Inl _ , False, Inl (SAlways _ hi sps')) \<Rightarrow> [Inl (SAlways i hi sps')]
| (Inl _ , False, Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')]
| (Inr vp, True,  Inl _ ) \<Rightarrow> [Inr (VAlways i vp)]
| (Inr vp, True,  Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp), Inr (VAlways i vp')]
| (Inr _ , False, Inl (SAlways _ hi sps')) \<Rightarrow> [Inl (SAlways i hi sps')]
| (Inr _ , False, Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')])"

definition do_since_base :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_since_base i a p1 p2 = (case (p1, p2, a = 0) of
  ( _ , Inl sp2, True) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inl _ , _ , False) \<Rightarrow> [Inr (VSinceInf i i [])]
| (Inl _ , Inr vp2, True) \<Rightarrow> [Inr (VSinceInf i i [vp2])]
| (Inr vp1, _ , False) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSinceInf i i [])]
| (Inr vp1, Inr sp2, True) \<Rightarrow> [Inr (VSince i vp1 [sp2]), Inr (VSinceInf i i [sp2])])"

definition do_since :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_since i a p1 p2 p' = (case (p1, p2, a = 0, p') of 
  (Inl sp1, Inr _ , True, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1)]
| (Inl sp1, _ , False, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1)]
| (Inl sp1, Inl sp2, True, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1), Inl (SSince sp2 [])]
| (Inl _ , Inr vp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VSinceInf _ li vp2s')) \<Rightarrow> [Inr (VSinceInf i li vp2s')]
| (Inl _ , Inr vp2, True, Inr (VSince _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VSince _ vp1' vp2s')) \<Rightarrow> [Inr (VSince i vp1' vp2s')]
| (Inr vp1, Inr vp2, True, Inl _ ) \<Rightarrow> [Inr (VSince i vp1 [vp2])]
| (Inr vp1, _ , False, Inl _ ) \<Rightarrow> [Inr (VSince i vp1 [])]
| (Inr _ , Inl sp2, True, Inl _ ) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inr vp1, Inr vp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [Inr (VSince i vp1 [vp2]), p' \<oplus> (Inr vp2)]
| (Inr vp1, _, False, Inr (VSinceInf _ li vp2s')) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSinceInf i li vp2s')]
| ( _ , Inl sp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inr vp1, Inr vp2, True, Inr (VSince _ _ _ )) \<Rightarrow> [Inr (VSince i vp1 [vp2]), p' \<oplus> (Inr vp2)]
| (Inr vp1, _ , False, Inr (VSince _ vp1' vp2s')) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSince i vp1' vp2s')]
| ( _ , Inl vp2, True, Inr (VSince _ _ _ )) \<Rightarrow> [Inl (SSince vp2 [])])"

definition do_until_base :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_until_base i a p1 p2 = (case (p1, p2, a = 0) of
  ( _ , Inl sp2, True) \<Rightarrow> [Inl (SUntil [] sp2)]
| (Inl sp1, _ , False) \<Rightarrow> [Inr (VUntilInf i i [])]
| (Inl sp1, Inr vp2, True) \<Rightarrow> [Inr (VUntilInf i i [vp2])]
| (Inr vp1, _ , False) \<Rightarrow> [Inr (VUntil i [] vp1), Inr (VUntilInf i i [])]
| (Inr vp1, Inr vp2, True) \<Rightarrow> [Inr (VUntil i [vp2] vp1), Inr (VUntilInf i i [vp2])])"

definition do_until :: "nat \<Rightarrow> nat \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof list" where
  "do_until i a p1 p2 p' = (case (p1, p2, a = 0, p') of
  (Inl sp1, Inr _ , True, Inl (SUntil _ _ )) \<Rightarrow> [p' \<oplus> (Inl sp1)]
| (Inl sp1, _ , False, Inl (SUntil _ _ )) \<Rightarrow> [p' \<oplus> (Inl sp1)]
| (Inl sp1, Inl sp2, True, Inl (SUntil _ _ )) \<Rightarrow> [p' \<oplus> (Inl sp1), Inl (SUntil [] sp2)]
| (Inl _ , Inr vp2, True, Inr (VUntilInf _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VUntilInf _ hi vp2s')) \<Rightarrow> [Inr (VUntilInf i hi vp2s')]
| (Inl _ , Inr vp2, True, Inr (VUntil _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VUntil _ vp2s' vp1')) \<Rightarrow> [Inr (VUntil i vp2s' vp1')]
| (Inr vp1, Inr vp2, True, Inl (SUntil _ _ )) \<Rightarrow> [Inr (VUntil i [vp2] vp1)]
| (Inr vp1, _ , False, Inl (SUntil _ _ )) \<Rightarrow> [Inr (VUntil i [] vp1)]
| (Inr vp1, Inl sp2, True, Inl (SUntil _ _ )) \<Rightarrow> [Inl (SUntil [] sp2)]
| (Inr vp1, Inr vp2, True, Inr (VUntilInf _ _ _ )) \<Rightarrow> [Inr (VUntil i [vp2] vp1), p' \<oplus> (Inr vp2)]
| (Inr vp1, _ , False, Inr (VUntilInf _ hi vp2s')) \<Rightarrow> [Inr (VUntil i [] vp1), Inr (VUntilInf i hi vp2s')]
| ( _ , Inl sp2, True, Inr (VUntilInf _ hi vp2s')) \<Rightarrow> [Inl (SUntil [] sp2)]
| (Inr vp1, Inr vp2, True, Inr (VUntil _ _ _ )) \<Rightarrow> [Inr (VUntil i [vp2] vp1), p' \<oplus> (Inr vp2)]
| (Inr vp1, _ , False, Inr (VUntil _ vp2s' vp1')) \<Rightarrow> [Inr (VUntil i [] vp1), Inr (VUntil i vp2s' vp1')]
| ( _ , Inl sp2, True, Inr (VUntil _ _ _ )) \<Rightarrow> [Inl (SUntil [] sp2)])"

fun match :: "('n, 'd) Formula.trm list \<Rightarrow> 'd list \<Rightarrow> ('n \<rightharpoonup> 'd) option" where
  "match [] [] = Some Map.empty"
| "match (Formula.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (Formula.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

fun pdt_of :: "nat \<Rightarrow> 'n \<Rightarrow> ('n, 'd :: linorder) Formula.trm list \<Rightarrow> 'n list \<Rightarrow> ('n \<rightharpoonup> 'd) list \<Rightarrow> ('n, 'd) expl" where
  "pdt_of i r ts [] V = (if List.null V then Leaf (Inr (VPred i r ts)) else Leaf (Inl (SPred i r ts)))"
| "pdt_of i r ts (x # vs) V =
     (let ds = remdups (List.map_filter (\<lambda>v. v x) V);
          part = tabulate ds (\<lambda>d. pdt_of i r ts vs (filter (\<lambda>v. v x = Some d) V)) (pdt_of i r ts vs [])
     in Node x part)"

fun "apply_pdt1" :: "'n list \<Rightarrow> (('n, 'd) proof \<Rightarrow> ('n, 'd) proof) \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl" where
  "apply_pdt1 vs f (Leaf pt) = Leaf (f pt)"
| "apply_pdt1 (z # vs) f (Node x part) =
  (if x = z then
     Node x (map_part (\<lambda>expl. apply_pdt1 vs f expl) part)
   else
     apply_pdt1 vs f (Node x part))"
| "apply_pdt1 [] _ (Node _ _) = undefined"

fun "apply_pdt2" :: "'n list \<Rightarrow> (('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof) \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl" where
  "apply_pdt2 vs f (Leaf pt1) (Leaf pt2) = Leaf (f pt1 pt2)"
| "apply_pdt2 vs f (Leaf pt1) (Node x part2) = Node x (map_part (apply_pdt1 vs (f pt1)) part2)"
| "apply_pdt2 vs f (Node x part1) (Leaf pt2) = Node x (map_part (apply_pdt1 vs (\<lambda>pt1. f pt1 pt2)) part1)"
| "apply_pdt2 (z # vs) f (Node x part1) (Node y part2) =
    (if x = z \<and> y = z then
       Node z (merge_part2 (apply_pdt2 vs f) part1 part2)
     else if x = z then
       Node x (map_part (\<lambda>expl1. apply_pdt2 vs f expl1 (Node y part2)) part1)
     else if y = z then
       Node y (map_part (\<lambda>expl2. apply_pdt2 vs f (Node x part1) expl2) part2)
     else
       apply_pdt2 vs f (Node x part1) (Node y part2))"
| "apply_pdt2 [] _ (Node _ _) (Node _ _) = undefined"

fun "apply_pdt3" :: "'n list \<Rightarrow> (('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> ('n, 'd) proof) \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl" where
  "apply_pdt3 vs f (Leaf pt1) (Leaf pt2) (Leaf pt3) = Leaf (f pt1 pt2 pt3)"
| "apply_pdt3 vs f (Leaf pt1) (Leaf pt2) (Node x part3) = Node x (map_part (apply_pdt2 vs (f pt1) (Leaf pt2)) part3)" 
| "apply_pdt3 vs f (Leaf pt1) (Node x part2) (Leaf pt3) = Node x (map_part (apply_pdt2 vs (\<lambda>pt2. f pt1 pt2) (Leaf pt3)) part2)"
| "apply_pdt3 vs f (Node x part1) (Leaf pt2) (Leaf pt3) = Node x (map_part (apply_pdt2 vs (\<lambda>pt1. f pt1 pt2) (Leaf pt3)) part1)"
| "apply_pdt3 (w # vs) f (Leaf pt1) (Node y part2) (Node z part3) = 
  (if y = w \<and> z = w then
     Node w (merge_part2 (apply_pdt2 vs (f pt1)) part2 part3)
   else if y = w then
     Node y (map_part (\<lambda>expl2. apply_pdt2 vs (f pt1) expl2 (Node z part3)) part2)
   else if z = w then
     Node z (map_part (\<lambda>expl3. apply_pdt2 vs (f pt1) (Node y part2) expl3) part3)
   else
     apply_pdt3 vs f (Leaf pt1) (Node y part2) (Node z part3))"
| "apply_pdt3 (w # vs) f (Node x part1) (Node y part2) (Leaf pt3) = 
  (if x = w \<and> y = w then
     Node w (merge_part2 (apply_pdt2 vs (\<lambda>pt1 pt2. f pt1 pt2 pt3)) part1 part2)
   else if x = w then
     Node x (map_part (\<lambda>expl1. apply_pdt2 vs (\<lambda>pt1 pt2. f pt1 pt2 pt3) expl1 (Node y part2)) part1)
   else if y = w then
     Node y (map_part (\<lambda>expl2. apply_pdt2 vs (\<lambda>pt1 pt2. f pt1 pt2 pt3) (Node x part1) expl2) part2)
   else
     apply_pdt3 vs f (Node x part1) (Node y part2) (Leaf pt3))"
| "apply_pdt3 (w # vs) f (Node x part1) (Leaf pt2) (Node z part3) = 
  (if x = w \<and> z = w then
     Node w (merge_part2 (apply_pdt2 vs (\<lambda>pt1. f pt1 pt2)) part1 part3)
   else if x = w then
     Node x (map_part (\<lambda>expl1. apply_pdt2 vs (\<lambda>pt1. f pt1 pt2) expl1 (Node z part3)) part1)
   else if z = w then
     Node z (map_part (\<lambda>expl3. apply_pdt2 vs (\<lambda>pt1. f pt1 pt2) (Node x part1) expl3) part3)
   else
     apply_pdt3 vs f (Node x part1) (Leaf pt2) (Node z part3))"
| "apply_pdt3 (w # vs) f (Node x part1) (Node y part2) (Node z part3) = 
  (if x = w \<and> y = w \<and> z = w then
     Node z (merge_part3 (apply_pdt3 vs f) part1 part2 part3)
   else if x = w \<and> y = w then
     Node w (merge_part2 (apply_pdt3 vs (\<lambda>pt3 pt1 pt2. f pt1 pt2 pt3) (Node z part3)) part1 part2)
   else if x = w \<and> z = w then
     Node w (merge_part2 (apply_pdt3 vs (\<lambda>pt2 pt1 pt3. f pt1 pt2 pt3) (Node y part2)) part1 part3)
   else if y = w \<and> z = w then
     Node w (merge_part2 (apply_pdt3 vs (\<lambda>pt1. f pt1) (Node x part1)) part2 part3)
   else if x = w then
     Node x (map_part (\<lambda>expl1. apply_pdt3 vs f expl1 (Node y part2) (Node z part3)) part1)
   else if y = w then
     Node y (map_part (\<lambda>expl2. apply_pdt3 vs f (Node x part1) expl2 (Node z part3)) part2)
   else if z = w then
     Node z (map_part (\<lambda>expl3. apply_pdt3 vs f (Node x part1) (Node y part2) expl3) part3)
   else 
     apply_pdt3 vs f (Node x part1) (Node y part2) (Node z part3))"
| "apply_pdt3 [] _ _ _ _ = undefined"

fun "hide_pdt" :: "'n list \<Rightarrow> (('n, 'd) proof + ('d, ('n, 'd) proof) part \<Rightarrow> ('n, 'd) proof) \<Rightarrow> ('n, 'd) expl \<Rightarrow> ('n, 'd) expl" where
  "hide_pdt vs f (Leaf pt) = Leaf (f (Inl pt))"
| "hide_pdt [x] f (Node y part) = Leaf (f (Inr (map_part unleaf part)))"
| "hide_pdt (x # xs) f (Node y part) = 
  (if x = y then
     Node y (map_part (hide_pdt xs f) part)
   else
     hide_pdt xs f (Node y part))"
| "hide_pdt [] _ _ = undefined"

context 
  fixes \<sigma> :: "('n, 'd :: {default, linorder}) trace" and
  cmp :: "('n, 'd) proof \<Rightarrow> ('n, 'd) proof \<Rightarrow> bool"
begin

function (sequential) eval :: "'n list \<Rightarrow> nat \<Rightarrow> ('n, 'd) Formula.formula \<Rightarrow> ('n, 'd) expl" where
  "eval vs i Formula.TT = Leaf (Inl (STT i))"
| "eval vs i Formula.FF = Leaf (Inr (VFF i))"
| "eval vs i (Eq_Const x c) = Node x (tabulate [c] (\<lambda>c. Leaf (Inl (SEq_Const i x c))) (Leaf (Inr (VEq_Const i x c))))"
| "eval vs i (Formula.Pred r ts) = 
  (pdt_of i r ts (filter (\<lambda>x. x \<in> Formula.fv (Formula.Pred r ts)) vs) (List.map_filter (match ts) (sorted_list_of_set (snd ` {rd \<in> \<Gamma> \<sigma> i. fst rd = r}))))"
| "eval vs i (Formula.Neg \<phi>) = apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_neg p)) (eval vs i \<phi>)"
| "eval vs i (Formula.Or \<phi> \<psi>) = apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_or p1 p2)) (eval vs i \<phi>) (eval vs i \<psi>)"
| "eval vs i (Formula.And \<phi> \<psi>) = apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_and p1 p2)) (eval vs i \<phi>) (eval vs i \<psi>)"
| "eval vs i (Formula.Imp \<phi> \<psi>) = apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_imp p1 p2)) (eval vs i \<phi>) (eval vs i \<psi>)"
| "eval vs i (Formula.Iff \<phi> \<psi>) = apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_iff p1 p2)) (eval vs i \<phi>) (eval vs i \<psi>)"
| "eval vs i (Formula.Exists x \<phi>) = hide_pdt (vs @ [x]) (\<lambda>p. min_list_wrt cmp (do_exists x p)) (eval (vs @ [x]) i \<phi>)"
| "eval vs i (Formula.Forall x \<phi>) = hide_pdt (vs @ [x]) (\<lambda>p. min_list_wrt cmp (do_forall x p)) (eval (vs @ [x]) i \<phi>)"
| "eval vs i (Formula.Prev I \<phi>) = (if i = 0 then Leaf (Inr VPrevZ) 
                                   else apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_prev i I (\<Delta> \<sigma> i) p)) (eval vs (i-1) \<phi>))"
| "eval vs i (Formula.Next I \<phi>) = apply_pdt1 vs (\<lambda>l. min_list_wrt cmp (do_next i I (\<Delta> \<sigma> (i+1)) l)) (eval vs (i+1) \<phi>)"
| "eval vs i (Formula.Once I \<phi>) = 
  (if \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I then Leaf (Inr (VOnceOut i)) 
   else (let expl = eval vs i \<phi> in
        (if i = 0 then 
           apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_once_base 0 0 p)) expl
         else (if right I \<ge> enat (\<Delta> \<sigma> i) then
                 apply_pdt2 vs (\<lambda>p p'. min_list_wrt cmp (do_once i (left I) p p')) expl
                            (eval vs (i-1) (Formula.Once (subtract (\<Delta> \<sigma> i) I) \<phi>))
               else apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_once_base i (left I) p)) expl))))"
| "eval vs i (Formula.Historically I \<phi>) = 
  (if \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I then Leaf (Inl (SHistoricallyOut i)) 
   else (let expl = eval vs i \<phi> in
        (if i = 0 then 
           apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_historically_base 0 0 p)) expl
         else (if right I \<ge> enat (\<Delta> \<sigma> i) then
                 apply_pdt2 vs (\<lambda>p p'. min_list_wrt cmp (do_historically i (left I) p p')) expl
                            (eval vs (i-1) (Formula.Historically (subtract (\<Delta> \<sigma> i) I) \<phi>))
               else apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_historically_base i (left I) p)) expl))))"
| "eval vs i (Formula.Eventually I \<phi>) = 
  (let expl = eval vs i \<phi> in
  (if right I = \<infinity> then undefined 
   else (if right I \<ge> enat (\<Delta> \<sigma> (i+1)) then
           apply_pdt2 vs (\<lambda>p p'. min_list_wrt cmp (do_eventually i (left I) p p')) expl
                            (eval vs (i+1) (Formula.Eventually (subtract (\<Delta> \<sigma> (i+1)) I) \<phi>))
         else apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_eventually_base i (left I) p)) expl)))"
| "eval vs i (Formula.Always I \<phi>) = 
  (let expl = eval vs i \<phi> in
  (if right I = \<infinity> then undefined 
   else (if right I \<ge> enat (\<Delta> \<sigma> (i+1)) then
           apply_pdt2 vs (\<lambda>p p'. min_list_wrt cmp (do_always i (left I) p p')) expl
                            (eval vs (i+1) (Formula.Always (subtract (\<Delta> \<sigma> (i+1)) I) \<phi>))
         else apply_pdt1 vs (\<lambda>p. min_list_wrt cmp (do_always_base i (left I) p)) expl)))"
| "eval vs i (Formula.Since \<phi> I \<psi>) = 
  (if \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I then Leaf (Inr (VSinceOut i)) 
   else (let expl1 = eval vs i \<phi> in
         let expl2 = eval vs i \<psi> in
         (if i = 0 then 
            apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_since_base 0 0 p1 p2)) expl1 expl2
          else (if right I \<ge> enat (\<Delta> \<sigma> i) then
                  apply_pdt3 vs (\<lambda>p1 p2 p'. min_list_wrt cmp (do_since i (left I) p1 p2 p')) expl1 expl2
                             (eval vs (i-1) (Formula.Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))
                else apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_since_base i (left I) p1 p2)) expl1 expl2))))"
| "eval vs i (Formula.Until \<phi> I \<psi>) = 
  (let expl1 = eval vs i \<phi> in
   let expl2 = eval vs i \<psi> in
   (if right I = \<infinity> then undefined 
    else (if right I \<ge> enat (\<Delta> \<sigma> (i+1)) then
            apply_pdt3 vs (\<lambda>p1 p2 p'. min_list_wrt cmp (do_until i (left I) p1 p2 p')) expl1 expl2
                             (eval vs (i+1) (Formula.Until \<phi> (subtract (\<Delta> \<sigma> (i+1)) I) \<psi>))
          else apply_pdt2 vs (\<lambda>p1 p2. min_list_wrt cmp (do_until_base i (left I) p1 p2)) expl1 expl2)))"
  by pat_completeness auto

fun dist where
  "dist i (Formula.Once _ _) = i"
| "dist i (Formula.Historically _ _) = i"
| "dist i (Formula.Eventually I _) = LTP \<sigma> (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> (\<tau> \<sigma> i + b)) - i"
| "dist i (Formula.Always I _) = LTP \<sigma> (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> (\<tau> \<sigma> i + b)) - i"
| "dist i (Formula.Since _ _ _) = i"
| "dist i (Formula.Until _ I _) = LTP \<sigma> (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> (\<tau> \<sigma> i + b)) - i"
| "dist _ _ = undefined"

lemma i_less_LTP: "\<tau> \<sigma> (Suc i) \<le> b + \<tau> \<sigma> i \<Longrightarrow> i < LTP \<sigma> (b + \<tau> \<sigma> i)"
  by (metis Suc_le_lessD i_le_LTPi_add le_iff_add)

termination eval
  by (relation "measures [\<lambda>(_, _, \<phi>). size \<phi>, \<lambda>(_, i, \<phi>). dist i \<phi>]")
    (auto simp: add.commute le_diff_conv i_less_LTP intro!: diff_less_mono2)

end

end