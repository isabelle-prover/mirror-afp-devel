(**                Algebra3  
                                  author Hidetsune Kobayashi
                                  Department of Mathematics
                                  Nihon University
                                  hikoba@math.cst.nihon-u.ac.jp
                                  May 3, 2004.

 chapter 3.  Group Theory. Focused on Jordan Hoelder theorem (continued)
   section 6.  (continued)
   section 7.  homomorphism
   section 8.  gkernel, kernel of a group homomorphism
   section 9.  image, image of a group homomorphism
   section 10. incuded homomorphisms
   section 11. Homomorphism therems
   section 12. isomorphisms
   section 13. Zassenhaus
   section 14. an automorphism group
   section 15. chain of groups I
   section 16. existence of reduced chain 
   section 17. existence of reduced chain and composition series"
   section 18. chain of groups II
   section 19. Jordan Hoelder theorem
   section 20. abelian groups
  **)

theory Algebra3 = Algebra2:

section "6. (continued)"

lemma ZassenhausTr2: "\<lbrakk> group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; H1 \<lhd> grp G H\<rbrakk> 
           \<Longrightarrow> H1 \<bullet>\<^sub>G (H \<inter> K) = (H \<inter> K) \<bullet>\<^sub>G H1 "
apply (subgoal_tac "K \<lhd> grp G K")
apply (simp add: ZassenhausTr1 [of "G" "H" "H1" "K" "K"])
apply (simp add: special_nsubg_G [of "G" "K"])
done

lemma ZassenhausTr2_1: "\<lbrakk> group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; H1 \<lhd> grp G H\<rbrakk>
  \<Longrightarrow> H1 \<bullet>\<^sub>G (H \<inter> K) \<guillemotleft> G"
apply (frule ZassenhausTr2 [of "G" "H" "H1" "K"], assumption+)
apply (frule inter_subgs [of "G" "H" "K"], assumption+)
apply (simp add:subgsubg)
done

lemma ZassenhausTr2_2: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> H1 \<bullet>\<^sub>G H \<inter> K1 \<subseteq>  H1 \<bullet>\<^sub>G H \<inter> K"  
apply (rule settOpTr1_2  [of "G" "H1" "H \<inter> K" "H1" "H \<inter> K1"], assumption+)
 apply (simp add:subg_subset)
 apply (rule subg_subset, assumption+)
 apply (simp add:inter_subgs) apply simp
apply (rule subsetI)
 apply simp
 apply (frule subggrp [of "G" "K"], assumption+)
 apply (frule subg_subset [of "grp G K" "K1"])
 apply (simp add:nmlSubgTr0)
 apply (erule conjE)
 apply (simp add:grp_def subsetD)
done

lemma ZassenhausTr2_3:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; H1 \<lhd> grp G H\<rbrakk> \<Longrightarrow> H1 \<subseteq> H"
apply (frule subggrp [of "G" "H"], assumption+)
apply (frule nmlSubgTr0 [of "grp G H" "H1"], assumption+)
apply (frule subg_subset [of "grp G H" "H1"], assumption+) 
apply (simp add:grp_def)
done

lemma ZassenhausTr2_4:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; H1 \<lhd> grp G H; h \<in> H; h1 \<in> H1\<rbrakk>
 \<Longrightarrow> h \<cdot>\<^sub>G h1 \<cdot>\<^sub>G h\<inverse>\<^sup>G \<in> H1" 
apply (frule subggrp [of "G" "H"], assumption+)
apply (frule_tac a = h and h = h1 in NSubgPr1_1 [of "grp G H" "H1"], 
                                                          assumption+)
 apply (simp add:grp_def) apply assumption+
apply (simp add:grp_def)
done

lemma ZassenhausTr2_5: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K; a\<in> H1; b \<in> H \<inter> K1; c \<in> H1\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G b \<cdot>\<^sub>G c \<in> H1 \<bullet>\<^sub>G (H \<inter> K1)"
apply (frule ZassenhausTr1 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule settOpTr1[of "G" "H1" "H \<inter> K1" "a" "b"], assumption+)
 apply (simp add:inter_subgs) apply assumption+
 apply (subgoal_tac "a \<cdot>\<^sub>G b \<in> H \<inter> K1 \<bullet>\<^sub>G H1") 
 apply (thin_tac "H1 \<bullet>\<^sub>G H \<inter> K1 = H \<inter> K1 \<bullet>\<^sub>G H1") prefer 2
 apply simp
 apply (thin_tac "a \<cdot>\<^sub>G b \<in> H1 \<bullet>\<^sub>G H \<inter> K1")
 apply (simp add:settOp_def [of "G" "H \<inter> K1" "H1"])
apply auto apply (frule sym) apply (thin_tac "x \<cdot>\<^sub>G y =  a \<cdot>\<^sub>G b")
 apply simp
 apply (subst tOp_assoc, assumption)
 apply (simp add:subg_subset1)+
 apply (thin_tac "a \<cdot>\<^sub>G b =  x \<cdot>\<^sub>G y")
apply (frule ZassenhausTr1 [of "G" "H" "H1" "K" "K1"], assumption+)
 apply simp
 apply (thin_tac "H1 \<bullet>\<^sub>G H \<inter> K1 = H \<inter> K1 \<bullet>\<^sub>G H1")
 apply (simp add:settOp_def)
 apply (frule_tac ?h1.0 = y and ?h2.0 = c in subg_tOp_closed [of "G" "H1"],
          assumption+)
 apply auto
done

lemma ZassenhausTr2_6: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K; u \<in> carrier G;  u \<in> carrier G;  v \<in> carrier G;  x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow>  
u \<cdot>\<^sub>G v \<cdot>\<^sub>G ( x \<cdot>\<^sub>G y) \<cdot>\<^sub>G ( v\<inverse>\<^sup>G \<cdot>\<^sub>G u\<inverse>\<^sup>G) = u \<cdot>\<^sub>G v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G \<cdot>\<^sub>G (  v \<cdot>\<^sub>G y \<cdot>\<^sub>G v\<inverse>\<^sup>G) \<cdot>\<^sub>G u\<inverse>\<^sup>G  "
apply (subst tOp_assoc [of "G" "u \<cdot>\<^sub>G v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G" "v \<cdot>\<^sub>G y \<cdot>\<^sub>G v\<inverse>\<^sup>G" " u\<inverse>\<^sup>G "], 
assumption+ )
apply simp+
apply (subst tOp_assoc [of "G" "u \<cdot>\<^sub>G v \<cdot>\<^sub>G x" " v\<inverse>\<^sup>G" "v \<cdot>\<^sub>G y \<cdot>\<^sub>G v\<inverse>\<^sup>G \<cdot>\<^sub>G u\<inverse>\<^sup>G"],
 assumption+)
apply simp+
apply (subst tOp_assocTr41 [of "G" "v" "y" "v\<inverse>\<^sup>G" "u\<inverse>\<^sup>G"], assumption+)
apply simp+
apply (subst tOp_assoc [of "G" "v\<inverse>\<^sup>G" "v \<cdot>\<^sub>G y" " v\<inverse>\<^sup>G \<cdot>\<^sub>G u\<inverse>\<^sup>G", THEN sym], 
 assumption+)
 apply simp+
apply (subst tOp_assoc [of "G" "v\<inverse>\<^sup>G" "v" "y", THEN sym], assumption+) 
 apply simp+
 apply (simp add:iOp_l_inv)
apply (subst tOp_assoc [of "G" "u \<cdot>\<^sub>G v" "x" "y \<cdot>\<^sub>G ( v\<inverse>\<^sup>G \<cdot>\<^sub>G u\<inverse>\<^sup>G)"], 
  assumption+)
 apply simp+
apply (subst tOp_assoc [of "G" "x" "y" "v\<inverse>\<^sup>G \<cdot>\<^sub>G u\<inverse>\<^sup>G", THEN sym], assumption+)
 apply simp+
apply (rule tOp_assoc [of "G" "u \<cdot>\<^sub>G v" " x \<cdot>\<^sub>G y" "v\<inverse>\<^sup>G \<cdot>\<^sub>G u\<inverse>\<^sup>G"], assumption+)
 apply simp+
done

lemma ZassenhausTr2_7: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K; a \<in> carrier G; x \<in> carrier G;  y \<in> carrier G\<rbrakk> \<Longrightarrow> 
  a \<cdot>\<^sub>G ( x \<cdot>\<^sub>G y) \<cdot>\<^sub>G a\<inverse>\<^sup>G =    a \<cdot>\<^sub>G x \<cdot>\<^sub>G a\<inverse>\<^sup>G \<cdot>\<^sub>G (  a \<cdot>\<^sub>G y \<cdot>\<^sub>G a\<inverse>\<^sup>G)"
apply (subst tOp_assocTr43 [of "G" " a \<cdot>\<^sub>G x" " a\<inverse>\<^sup>G" "a \<cdot>\<^sub>G y" "a\<inverse>\<^sup>G"], 
        assumption+)
apply simp+
apply (subst tOp_assocTr42, assumption+) apply simp+
apply (subst tOp_assoc [of "G" " a\<inverse>\<^sup>G" "a" "y", THEN sym], assumption+)
apply simp+
apply (simp add:iOp_l_inv)
apply (rule tOp_assocTr42[THEN sym], assumption+)
apply simp
done

lemma ZassenhausTr3: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow>  (H1 \<bullet>\<^sub>G (H \<inter> K1)) \<lhd>  grp G (H1 \<bullet>\<^sub>G (H \<inter> K))"
apply (frule ZassenhausTr2_1 [of "G" "H" "H1" "K"], assumption+)
apply (frule ZassenhausTr2_1 [of "G" "H" "H1" "K1"], assumption+)

apply (frule ZassenhausTr2_2 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule subg_in_subg [of "G" "H1 \<bullet>\<^sub>G (H \<inter> K1)" "H1 \<bullet>\<^sub>G (H \<inter> K)"], 
                                                               assumption+)
apply (rule nmlSubg2)
 apply (simp add:subggrp)
 apply assumption+
apply (rule ballI)+
 apply (subgoal_tac "carrier (grp G (H1 \<bullet>\<^sub>G H \<inter> K)) = H1 \<bullet>\<^sub>G H \<inter> K")
 apply simp
apply (simp add:grp_def) apply (fold grp_def)
prefer 2 apply (simp add:grp_def)
 apply (subgoal_tac "\<exists>u\<in>H1. \<exists>v\<in>(H \<inter> K). u \<cdot>\<^sub>G v = a")
 prefer 2 apply (simp add:settOp_def)
 apply (subgoal_tac "\<exists>x\<in>H1. \<exists>y\<in>(H \<inter> K1). x \<cdot>\<^sub>G y = h")
 prefer 2 apply (simp add:settOp_def)
apply auto
 apply (subst invofab, assumption+)
 apply (simp add:subg_subset1)+
apply (subst ZassenhausTr2_6[of "G" "H" "H1" "K" "K1"], assumption+)
 apply (simp add:subg_subset1)+
apply (subgoal_tac "u \<cdot>\<^sub>G v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G \<in> H1")
apply (subgoal_tac "v \<cdot>\<^sub>G y \<cdot>\<^sub>G v\<inverse>\<^sup>G \<in> H \<inter> K1")
apply (rule_tac  a = "u \<cdot>\<^sub>G v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G" and b = " v \<cdot>\<^sub>G y \<cdot>\<^sub>G v\<inverse>\<^sup>G" and c = "u\<inverse>\<^sup>G" in  ZassenhausTr2_5 [of "G" "H" "H1" "K1" "K1"], assumption+)
 apply (simp add:special_nsubg_G)
 apply (simp add:subg_tOp_closed [of "G" "H1"])
 apply assumption
 apply (simp add:subg_iOp_closed)
apply simp
 apply (rule conjI)
 apply (rule subg_tOp_closed, assumption+)+
 apply (simp add:subg_iOp_closed)
 apply (frule subggrp [of "G" "K"], assumption+)
 apply (frule_tac a = v and h = y in NSubgPr1_1 [of "grp G K" "K1"],
                                                           assumption+)
 apply (simp add:grp_def)
 apply assumption  apply (simp add:grp_def) 
apply (subgoal_tac "u \<cdot>\<^sub>G v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G = u \<cdot>\<^sub>G (v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G)")
 apply simp
apply (rule_tac ?h1.0 = u and ?h2.0 = "v \<cdot>\<^sub>G x \<cdot>\<^sub>G v\<inverse>\<^sup>G" in 
                      subg_tOp_closed [of "G" "H1"], assumption+)
 apply (frule subggrp [of "G" "H"], assumption+)
 apply (frule_tac a = v and h = x in NSubgPr1_1 [of "grp G H" "H1"],
                                                           assumption+)
 apply (simp add:grp_def) apply assumption
 apply (simp add:grp_def)
apply (subst  tOp_assocTr45, assumption+)
 apply (simp add:subg_subset1)+
apply (rule tOp_bothl, assumption+)
 apply (rule tOp_closed, assumption+)+
 apply (simp add:subg_subset1)+
apply (subst tOp_assoc, assumption+)
 apply (simp add:subg_subset1)+
done

lemma ZassenhausTr3_2:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> H1 \<bullet>\<^sub>G (H \<inter> K1) \<bullet>\<^sub>G (H \<inter> K) \<guillemotleft> G" 
apply (frule settOpTr5 [of "G" "H1" "H \<inter> K1" "H \<inter> K"], assumption+)
 apply (simp add:inter_subgs)+
 apply (frule NinHNTr0_2 [of "G" "H \<inter> K1" "H \<inter> K"])
  apply (simp add:inter_subgs)+ 
  apply (frule  ZassenhausTr2_3 [of "G" "K" "K1"])
    apply auto
apply (simp add:ZassenhausTr2_1)
done

lemma ZassenhausTr3_3:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> (H1 \<inter> K) \<bullet>\<^sub>G (H \<inter> K1) = (K1 \<inter> H) \<bullet>\<^sub>G (K \<inter> H1)"
apply auto
 apply (simp add:settOp_def)
 apply auto
 apply (subgoal_tac "xa \<cdot>\<^sub>G y \<cdot>\<^sub>G xa\<inverse>\<^sup>G \<cdot>\<^sub>G xa = xa \<cdot>\<^sub>G y")
 apply (subgoal_tac "xa \<cdot>\<^sub>G y \<cdot>\<^sub>G xa\<inverse>\<^sup>G \<in> K1 \<inter> H")
 apply (subgoal_tac "xa \<in> K \<inter> H1")
apply blast apply simp
 apply (thin_tac "xa \<cdot>\<^sub>G y \<cdot>\<^sub>G xa\<inverse>\<^sup>G \<cdot>\<^sub>G xa =  xa \<cdot>\<^sub>G y")
 apply simp
 apply (rule conjI) 
 apply (frule subggrp [of "G" "K"], assumption+)
 apply (frule_tac a = xa and h = y in NSubgPr1_1 [of "grp G K" "K1"],
                                                           assumption+)
 apply (simp add:grp_def)
 apply assumption
 apply (simp add:grp_def)
 apply (rule subg_tOp_closed, assumption+)+
 apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+)
 apply (simp add:subsetD) apply assumption
 apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+)
 apply (frule_tac c = xa in subsetD [of "H1" "H"], assumption+)
 apply (simp add:subg_iOp_closed)
apply (subst tOp_assocTr43[THEN sym], assumption+)
 apply (simp add:subg_subset1)+
 apply (subst iOp_l_inv, assumption+)
 apply (simp add:subg_subset1)+
 apply (subst r_one, assumption+)
 apply (rule tOp_closed, assumption+)
 apply (simp add:subg_subset1)+
apply (simp add:settOp_def)
 apply auto
 apply (subgoal_tac "xa \<cdot>\<^sub>G y \<cdot>\<^sub>G xa\<inverse>\<^sup>G \<cdot>\<^sub>G xa = xa \<cdot>\<^sub>G y")
 apply (subgoal_tac "xa \<cdot>\<^sub>G y \<cdot>\<^sub>G xa\<inverse>\<^sup>G \<in> H1 \<inter> K")
 apply (subgoal_tac "xa \<in> H \<inter> K1")
apply blast apply simp
 apply (thin_tac "xa \<cdot>\<^sub>G y \<cdot>\<^sub>G xa\<inverse>\<^sup>G \<cdot>\<^sub>G xa =  xa \<cdot>\<^sub>G y")
 apply simp
 apply (rule conjI) 
 apply (frule subggrp [of "G" "H"], assumption+)
 apply (frule_tac a = xa and h = y in NSubgPr1_1 [of "grp G H" "H1"],
                                                           assumption+)
 apply (simp add:grp_def)
 apply assumption
 apply (simp add:grp_def)
 apply (rule subg_tOp_closed, assumption+)+
 apply (frule ZassenhausTr2_3 [of "G" "K" "K1"], assumption+)
 apply (simp add:subsetD) apply assumption
 apply (frule ZassenhausTr2_3 [of "G" "K" "K1"], assumption+)
 apply (frule_tac c = xa in subsetD [of "K1" "K"], assumption+)
 apply (simp add:subg_iOp_closed)
apply (subst tOp_assocTr43[THEN sym], assumption+)
 apply (simp add:subg_subset1)+
 apply (subst iOp_l_inv, assumption+)
 apply (simp add:subg_subset1)+
 apply (subst r_one, assumption+)
 apply (rule tOp_closed, assumption+)
 apply (simp add:subg_subset1)+
done


lemma ZassenhausTr3_4:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K; g \<in> H \<inter> K; h \<in> H \<inter> K1 \<rbrakk> \<Longrightarrow> g \<cdot>\<^sub>G h \<cdot>\<^sub>G g\<inverse>\<^sup>G \<in> H \<inter> K1"
apply (subgoal_tac "g \<cdot>\<^sub>G h \<cdot>\<^sub>G g\<inverse>\<^sup>G \<in> H") apply simp
apply (rule ZassenhausTr2_4 [of "G" "K" "K1" _], assumption+)
 apply simp+
apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+)
apply (rule subg_tOp_closed, assumption+)+
 apply (simp add:subg_subset1 subsetD)+
 apply (simp add:subsetD subg_iOp_closed)
done

lemma ZassenhausTr3_5:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; 
H1 \<lhd> (grp G H); K1 \<lhd> (grp G K)\<rbrakk> \<Longrightarrow> (H1 \<inter> K) \<bullet>\<^sub>G (H \<inter> K1) \<lhd> (grp G (H \<inter> K))"
apply (frule ZassenhausTr3 [of "G" "H \<inter> K" "H1 \<inter> K" "K \<inter> H" "H \<inter> K1"])
      apply (simp add:inter_subgs)+
  prefer 3
  apply (frule ZassenhausTr2_3 [of "G" "K" "K1"], assumption+)
  apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+) 
  apply (subgoal_tac "H \<inter> K \<inter> (H \<inter> K1) = H \<inter> K1")
   apply (subgoal_tac "H \<inter> K \<inter> (K \<inter> H) = H \<inter> K") apply simp
    apply (frule NinHNTr0_2 [of "G" "H1 \<inter> K" "H \<inter> K"])
       apply (simp add:inter_subgs)+
     apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], auto)
 apply (rule nmlSubg2)
   apply (rule subggrp, assumption+)
   apply (simp add:inter_subgs)
  apply (rule subg_in_subg, assumption+)
    apply (simp add:inter_subgs)+
  apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], auto)
  apply (simp add:grp_def) apply (fold grp_def)
  apply (frule subggrp [of "G" "H"], assumption+)
  apply (frule_tac a = a and h = h in NSubgPr1_1 [of "grp G H" "H1"],
                                                           assumption+)
    apply (simp add:grp_def)
   apply assumption
  apply (simp add:grp_def)
 apply (simp add:grp_def)
 apply (rule subg_tOp_closed, assumption+)+
   apply (simp add:subg_iOp_closed)
  apply (frule subggrp [of "G" "K \<inter> H"])
   apply (simp add:inter_subgs)
  apply (simp add:grp_def)
 apply (clarsimp simp add:grp_def)
 apply (fold grp_def)
 apply (simp add:subg_iOp_closed)
apply (rule nmlSubg2)
  apply (rule subggrp, assumption+)
  apply (simp add:inter_subgs)
 apply (rule subg_in_subg, assumption+)
   apply (simp add:inter_subgs)+
 apply (frule ZassenhausTr2_3 [of "G" "K" "K1"], auto)
 apply (simp add:grp_def) apply (fold grp_def)
 apply (erule conjE)+
 apply (rule subg_tOp_closed, assumption+)+
 apply (simp add:subg_iOp_closed)
apply (frule subggrp [of "G" "K"], assumption+)
apply (frule_tac a = a and h = h in NSubgPr1_1 [of "grp G K" "K1"],
                                                           assumption+)
  apply (simp add:grp_def)
 apply assumption+
apply (simp add:grp_def)
done

lemma ZassenhausTr4: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow>  (H1 \<bullet>\<^sub>G (H \<inter> K1)) \<bullet>\<^sub>G (H1 \<bullet>\<^sub>G (H \<inter> K)) = H1 \<bullet>\<^sub>G (H \<inter> K)"
apply (frule ZassenhausTr2 [of "G" "H" "H1" "K"], assumption+)        
apply (frule ZassenhausTr2 [of "G" "H" "H1" "K1"], assumption+) 
apply (frule ZassenhausTr1_1 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule ZassenhausTr2_1 [of "G" "H" "H1" "K"], assumption+)
apply (frule ZassenhausTr2_2 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (rule NinHNTr0_2 [of "G" "H1 \<bullet>\<^sub>G H \<inter> K1" "H1 \<bullet>\<^sub>G H \<inter> K"], assumption+)
done

lemma ZassenhausTr4_0: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow>  H1 \<bullet>\<^sub>G (H \<inter> K) = (H1 \<bullet>\<^sub>G (H \<inter> K1)) \<bullet>\<^sub>G (H \<inter> K)"
apply (frule inter_subgs [of "G" "H" "K1"], assumption+) 
apply (frule inter_subgs [of "G" "H" "K"], assumption+)
apply (subst settOpTr5 [of "G" "H1" "H \<inter> K1" "H \<inter> K"], assumption+)
apply (frule subggrp [of "G" "K"], assumption+)
apply (frule nmlSubgTr0 [of "grp G K" "K1"], assumption+)
apply (frule subg_subset [of "grp G K" "K1"], assumption+)
apply (simp add:grp_carrier [of "G" "K"])
apply (subgoal_tac "H \<inter> K1 \<subseteq> H \<inter> K")
apply (subst NinHNTr0_2 [of "G" "H \<inter> K1" "H \<inter> K"], assumption+)
apply auto
done

lemma ZassenhausTr4_1:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<lhd> (grp G H); H \<inter> K \<guillemotleft> (grp G H)\<rbrakk>
                           \<Longrightarrow> H1 \<lhd> (grp G (H1 \<bullet>\<^sub>G (H \<inter> K)))" 
apply (frule subggrp [of "G" "H"], assumption+)
apply (frule nmlSubgTr0 [of "grp G H" "H1"], assumption+)
apply (frule subg_of_subg [of "G" "H" "H \<inter> K"], assumption+) 
apply (frule subg_of_subg[of "G" "H" "H1"], assumption+)
apply (frule nnsubg_1 [of "grp G H" "H \<inter> K" "H1"], assumption+)
apply (frule settOpinherited [of "G" "H" "H1" "H \<inter> K"], assumption+) 
apply (rule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+)
 apply (simp add:Int_lower1) apply simp
  apply (thin_tac "H1 \<bullet>\<^sub>(grp G H) H \<inter> K = H1 \<bullet>\<^sub>G H \<inter> K")
 apply (frule ZassenhausTr2_1 [of "G" "H" "H1" "H \<inter> K"], assumption+) 
 apply (subgoal_tac "H \<inter> (H \<inter> K) = H \<inter> K") apply simp
  apply (thin_tac "H \<inter> (H \<inter> K) = H \<inter> K")
 apply (frule subg_inc_settOp [of "G" "H" "H1" "H \<inter> K"], assumption+)
  apply (rule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+)
  apply (simp add:Int_lower1)
 apply (frule grp_inherited [of "G" "H1 \<bullet>\<^sub>G H \<inter> K" "H"], assumption+)
 apply simp
apply auto
done

section "7. homomorphism"

lemma gHom: "\<lbrakk> group F; group G; f \<in> gHom F G ; x \<in> carrier F; 
           y \<in> carrier F\<rbrakk>  \<Longrightarrow> f (tOp F x y) = tOp G (f x) (f y)"
apply (simp add: gHom_def)
done

(* we have to check the composition of two ghom's *) 
lemma gHomcomp: "\<lbrakk> group F; group G; group H; f \<in> gHom F G; g \<in> gHom G H \<rbrakk>
    \<Longrightarrow> g \<circ>\<^sub>F f \<in> gHom F H"
apply (simp add:gHom_def)
 apply (erule conjE)+
apply (simp add:cmpghom_def composition)
apply (rule ballI)+
 apply (simp add:compose_def)
 apply (frule_tac x = x in funcset_mem [of "f" "carrier F" "carrier G"],
                                              assumption+) 
apply (frule_tac x = y in funcset_mem [of "f" "carrier F" "carrier G"],
                                              assumption+) 
apply auto
done

lemma gHom_comp_gsurjec: "\<lbrakk> group F; group G; group H; gsurjec\<^sub>F\<^sub>,\<^sub>G f; 
  gsurjec\<^sub>G\<^sub>,\<^sub>H g \<rbrakk>  \<Longrightarrow> gsurjec\<^sub>F\<^sub>,\<^sub>H (g \<circ>\<^sub>F f)"
apply (simp add:gsurjec_def)
apply (simp add:gHomcomp)

apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "f \<in> gHom F G \<and> surj_to f (carrier F) (carrier G)")
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "g \<in> gHom G H \<and> surj_to g (carrier G) (carrier H)")
apply (simp add:gHom_def)
 apply (erule conjE)+
 apply (thin_tac "(\<forall>x\<in>carrier F. \<forall>y\<in>carrier F. f ( x \<cdot>\<^sub>F y) =  (f x) \<cdot>\<^sub>G (f y))")
 apply (thin_tac "(\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. g ( x \<cdot>\<^sub>G y) =  (g x) \<cdot>\<^sub>H (g y))")
apply (simp add:cmpghom_def)
apply (rule compose_surj, assumption+)
done

lemma gHom_comp_ginjec: "\<lbrakk> group F; group G; group H; ginjec\<^sub>F\<^sub>,\<^sub>G f; 
  ginjec\<^sub>G\<^sub>,\<^sub>H g \<rbrakk>  \<Longrightarrow> ginjec\<^sub>F\<^sub>,\<^sub>H (g \<circ>\<^sub>F f)"
apply (simp add:ginjec_def)
apply (simp add:gHomcomp)

apply (erule conjE)+
apply (simp add:gHom_def) apply (erule conjE)+
apply (thin_tac "(\<forall>x\<in>carrier F. \<forall>y\<in>carrier F. f ( x \<cdot>\<^sub>F y) =  (f x) \<cdot>\<^sub>G (f y))")
apply (thin_tac "(\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. g ( x \<cdot>\<^sub>G y) =  (g x) \<cdot>\<^sub>H (g y))")
apply (simp add:cmpghom_def)
apply (simp add:comp_inj)
done

lemma ghom_unit_unit:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
                                                   f (1\<^sub>F) = 1\<^sub>G"
apply (frule ex_one [of "F"])
apply (frule gHom [of "F" "G" "f" "1\<^sub>F" "1\<^sub>F"], assumption+)
 apply (frule l_one [of "F" "1\<^sub>F"], assumption+)
 apply simp
 apply (simp add:gHom_def)  apply (erule conjE)+
 apply (thin_tac "\<forall>x\<in>carrier F. \<forall>y\<in>carrier F. f ( x \<cdot>\<^sub>F y) =  f x \<cdot>\<^sub>G (f y)")
 apply (frule_tac x = "1\<^sub>F" in funcset_mem [of "f" "carrier F" "carrier G"],
                                    assumption+)
 apply (thin_tac "f \<in> carrier F \<rightarrow> carrier G")
apply (frule sym)
apply (rule r_oneUnique [of "G" "f (1\<^sub>F)" "f (1\<^sub>F)"], assumption+)
done

lemma ghom_inv_inv: "\<lbrakk> group F; group G; f \<in> gHom F G ; x \<in> carrier F\<rbrakk> \<Longrightarrow>
   f (iOp F x) = iOp G (f x)"
apply (frule gHom [of "F" "G" "f" "iOp F x" "x"], assumption+)
apply simp+
apply (simp add:iOp_l_inv)
apply (frule ghom_unit_unit [of "F" "G" "f"], assumption+)
 apply simp
apply (simp add:gHom_def) apply (erule conjE)+
apply (frule funcset_mem [of "f" "carrier F" "carrier G" "x"], assumption+)
apply (frule iOp_closed [of "F" "x"], assumption+)
apply (frule funcset_mem [of "f" "carrier F" "carrier G" "x\<inverse>\<^sup>F"], assumption+)
apply (simp add:inv1_unique)
done

lemma ghomTr3: "\<lbrakk> group F; group G; f \<in> gHom F G ; x \<in> carrier F;
  y \<in> carrier F; f (x \<cdot>\<^sub>F y\<inverse>\<^sup>F) = 1\<^sub>G \<rbrakk> \<Longrightarrow> f x = f y"

apply (frule  gHom [of "F" "G" "f" "x \<cdot>\<^sub>F y\<inverse>\<^sup>F" "y"], assumption+)
apply simp+
apply (frule gHom [of "F" "G" "f" "x \<cdot>\<^sub>F y\<inverse>\<^sup>F" "y", THEN sym], assumption+)
apply (rule tOp_closed, assumption+)
 apply simp apply assumption
apply simp
 apply (frule iOp_closed [of "F" "y"], assumption+)
apply (simp add:tOp_assoc)
 apply (simp add:iOp_l_inv r_one)
apply (simp add:gHom_def) apply (erule conjE)+
apply (frule funcset_mem [of "f" "carrier F" "carrier G" "y"], assumption+)
apply simp
done

lemma ghomTr4:"\<lbrakk> group F; group G; f \<in> gHom F G; K \<guillemotleft> G \<rbrakk> \<Longrightarrow> 
   (Invim F G f K) \<guillemotleft> F"    
apply (simp add: subgroup_def [of "F" _])
apply (rule conjI)
apply (simp add:Invim_def)
 apply (rule subsetI) apply (simp add:CollectI)
apply (rule conjI)
apply (rule ballI)+
 apply (simp add:Invim_def)
 apply (simp add:gHom)
 apply (rule subg_tOp_closed, assumption+)
 apply simp+
apply (rule conjI)
apply (rule ballI)
 apply (simp add:Invim_def)
 apply (simp add:ghom_inv_inv)
 apply (rule subg_iOp_closed, assumption+)
 apply simp
(** 1\<^sub>F \<in> Invim F G f K **)
apply (simp add:Invim_def)
apply (simp add:ex_one ghom_unit_unit)
apply (simp add:one_in_subg)
done
 
lemma IdTr0: "group F \<Longrightarrow> idmap (carrier F) \<in> gHom F F"
apply (simp add:gHom_def)
apply (simp add:idmap_def extensional_def)
apply (simp add:Pi_def)
done

syntax 
  "@IDMAP"::"('a, 'more) GroupType_scheme \<Rightarrow> ('a \<Rightarrow> 'a)"
                ("(I\<^sub>_)" [999]1000)

  "@INVFUN"::"[('a, 'm1) GroupType_scheme, ('b, 'm) GroupType_scheme, 'a \<Rightarrow> 'b]
              \<Rightarrow> ('b \<Rightarrow> 'a)" ("(3Ifn _ _ _)" [88,88,89]88)
translations
   "I\<^sub>F" == "idmap (carrier F)"
   "Ifn F G f" == "invfun (carrier F) (carrier G) f"

lemma IdTr1:"\<lbrakk> group F; x \<in> carrier F\<rbrakk> \<Longrightarrow> (I\<^sub>F) x = x"
apply (simp add:idmap_def)
done

lemma IdTr2: "group F \<Longrightarrow> gbijec\<^sub>F\<^sub>,\<^sub>F (I\<^sub>F)"
apply (simp add:gbijec_def)
apply (rule conjI)
 (* gsurjec *)
  apply (simp add:gsurjec_def)
      apply (rule conjI)
        apply (simp add:IdTr0)
        apply (simp add:surj_to_def)
      apply (simp add:image_def idmap_def)
  (* ginjec *)
  apply (simp add:ginjec_def)
     apply (simp add:IdTr0)
     apply (simp add:inj_on_def idmap_def)
done

section "8. gkernel"

lemma gkernTr1: "\<lbrakk> group F; group G; f \<in> gHom F G; x \<in> gker\<^sub>F\<^sub>,\<^sub>G f\<rbrakk> \<Longrightarrow>                    x \<in> carrier F"
apply (simp add: gkernel_def)
done 

lemma gkernTr2: "\<lbrakk> group F; group G; f \<in> gHom F G ; 
x \<in> gker\<^sub>F\<^sub>,\<^sub>G f ; y \<in> gker\<^sub>F\<^sub>,\<^sub>G f \<rbrakk>   \<Longrightarrow> (tOp F x y) \<in> gker\<^sub>F\<^sub>,\<^sub>G f"
apply (simp add:gkernel_def)
apply (simp add:gHom)
apply (simp add:ex_one)
done

lemma gkernTr3:"\<lbrakk>group F; group G; f \<in> gHom F G ; x \<in> gker\<^sub>F\<^sub>,\<^sub>G f\<rbrakk> \<Longrightarrow> (iOp F x) \<in>  gker\<^sub>F\<^sub>,\<^sub>G f"
apply (simp add:gkernel_def)
(* thm ghom_inv_inv [of "F" "G" "f" "x"] *)
apply (simp add:ghom_inv_inv [of "F" "G" "f" "x"])
apply (simp add:inv_one)
done

lemma gkernTr6: "\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> (1\<^sub>F) \<in> gker\<^sub>F\<^sub>,\<^sub>G f"
apply (simp add:gkernel_def)   
apply (simp add:ex_one ghom_unit_unit [of "F" "G" "f" ])
done

lemma gkernTr7: "\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> gker\<^sub>F\<^sub>,\<^sub>G f \<guillemotleft> F"
apply (simp add: subgroup_def)
(* thm kernTr2 [of "F" "G" "f" _] *)
apply (simp add:gkernTr2 [of "F" "G" "f" _])
apply (rule conjI)
apply (rule subsetI)
apply (simp add:gkernTr1)

(* thm kernTr3 [of "F" "G" "f" _] *)
apply (rule conjI)
apply (rule ballI)
apply (simp add:gkernTr3 [of "F" "G" "f" _])
apply (simp add: gkernTr6 [of "F" "G" "f" ])
done

lemma gkern:"\<lbrakk> group F; group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>  gker\<^sub>F\<^sub>,\<^sub>G f \<lhd> F"
apply (rule nmlSubg2, assumption+)
apply (simp add:gkernTr7)
apply (rule ballI)+
apply (simp add:gkernel_def)
apply (subst gHom [of "F" "G" "f" _], assumption+)
apply simp+
apply (subst  gHom [of "F" "G" "f" _], assumption+)
apply simp
apply (erule conjE)
 apply (subgoal_tac "f \<in> carrier F \<rightarrow> carrier G")
apply (frule funcset_mem [of "f" "carrier F" "carrier G" ], assumption+)
apply (simp add:r_one)
apply (simp add:ghom_inv_inv iOp_r_inv)
 apply (simp add:gHom_def)
done

lemma gkern1:"\<lbrakk> group F; Ugp E; f \<in> gHom F E \<rbrakk> \<Longrightarrow>  gker\<^sub>F\<^sub>,\<^sub>E f = carrier F"
apply (rule equalityI)
 apply (rule subsetI)
 apply (rule gkernTr1 [of "F" "E" "f" _], assumption+)
 apply (simp add:Ugp_def)
 apply simp+
apply (rule subsetI)
 apply (simp add:gkernel_def)
 apply (simp add:Ugp_def gHom_def) apply (erule conjE)+
apply (subgoal_tac "f x \<in> {1\<^sub>E}")
 apply simp
apply (rule funcset_mem, assumption+)
done

lemma gkern2:"\<lbrakk> group F; group G; f \<in> gHom F G; ginjec\<^sub>F\<^sub>,\<^sub>G f \<rbrakk> \<Longrightarrow>
     gker\<^sub>F\<^sub>,\<^sub>G f = {1\<^sub>F}"
apply (simp add:ginjec_def)
apply (rule equalityI)
  apply (rule subsetI)
apply (simp add:gkernel_def)
apply (frule ghom_unit_unit [of "F" "G"], assumption+)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> carrier F \<and> f x = 1\<^sub>G")
apply (subgoal_tac "f x = f (1\<^sub>F)")
 apply (thin_tac "f (1\<^sub>F) = 1\<^sub>G")
 apply (thin_tac "f x = 1\<^sub>G")
 apply (subgoal_tac "1\<^sub>F \<in> carrier F")
apply (simp add:inj_on_def)
 apply (simp add:ex_one)
 apply simp
apply (simp add:gkernel_def ex_one ghom_unit_unit)
done

lemma gkernTr9:"\<lbrakk> group F; group G; f \<in> gHom F G; a \<in> carrier F; 
b \<in> carrier F; r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) a = r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) b \<rbrakk> \<Longrightarrow>f a = f b"
(* thm r_cosEqVar1 [of "F" "ker f (F \<rightharpoonup> G) " "a" "b"] *)
apply (frule gkernTr7[of "F" "G" "f"], assumption+)
apply (frule r_cosEqVar1 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" "b" "a"], assumption+)
apply (rule sym, assumption+)
apply (simp add:gkernel_def)
 apply (fold gkernel_def)
 apply (thin_tac "r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) a = r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) b")
 apply (thin_tac "gker\<^sub>F\<^sub>,\<^sub>G f  \<guillemotleft> F")
apply (rule ghomTr3 [of "F" "G" "f" _], assumption+)
done 

lemma gkernTr10:"\<lbrakk> group F; group G; f \<in> gHom F G ; a \<in> carrier F;
b \<in> carrier F; f a = f b \<rbrakk> \<Longrightarrow> r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) a =  
    r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) b "
apply (subgoal_tac "a \<cdot>\<^sub>F b\<inverse>\<^sup>F \<in> (gker\<^sub>F\<^sub>,\<^sub>G f)")
apply (rule r_cosEq, assumption+)
apply (simp add:gkernTr7)
apply simp+
apply (subgoal_tac "b \<cdot>\<^sub>F a\<inverse>\<^sup>F = (a \<cdot>\<^sub>F b\<inverse>\<^sup>F)\<inverse>\<^sup>F")
 apply simp
 apply (rule subg_iOp_closed, assumption+)
 apply (simp add:gkernTr7)
 apply assumption
 apply (subst invofab, assumption+)
 apply simp
 apply (simp add:iOp_invinv)
(** a \<cdot>\<^sub>F b\<inverse>\<^sup>F \<in> ker\<^sub>F\<^sub>,\<^sub>Gf **)
apply (simp add:gkernel_def)
apply (simp add: gHom [of "F" "G" "f" "a" "iOp F b"])
apply (simp add:ghom_inv_inv [of "F" "G" "f" "b"])
apply (subgoal_tac "f b \<in> carrier G")
apply (simp add:iOp_r_inv)
apply (subgoal_tac "f \<in> carrier F \<rightarrow> carrier G")
apply (simp add:funcset_mem)
apply (simp add:gHom_def)
done

lemma gkernTr11:"\<lbrakk> group F; group G; f \<in> gHom F G ; a \<in> carrier F \<rbrakk> \<Longrightarrow> 
        (Invim F G f {f a}) = r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) a"
apply (rule equalityI) (** Invim F G f {f a} \<subseteq> ker\<^sub>F\<^sub>,\<^sub>Gf \<^sub>F a **)
apply (rule subsetI)
apply (simp add:Invim_def)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> carrier F \<and> f x = f a")
apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
apply (frule_tac a = x in gkernTr10 [of "F" "G" "f" _ "a"], assumption+)
apply (frule_tac a = x in aInR_cos [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+)
 apply simp
(**  ker\<^sub>F\<^sub>,\<^sub>Gf \<^sub>F a \<subseteq> Invim F G f {f a} **)
apply (rule subsetI)
apply (simp add:r_coset_def Invim_def)
apply auto
apply (simp add:gkernel_def)

apply (simp add:gkernel_def) apply (erule conjE)
apply (simp add:gHom)
apply (simp add:gHom_def) apply (erule conjE)+
apply (simp add:funcset_mem)
done

lemma gHomcompTr3: "\<lbrakk> group F; group G; group H; gbijec\<^sub>F\<^sub>,\<^sub>G f;  gbijec\<^sub>G\<^sub>,\<^sub>H g \<rbrakk>
    \<Longrightarrow> gbijec\<^sub>F\<^sub>,\<^sub>H (g \<circ>\<^sub>F f)"
apply (simp add:gbijec_def)
apply (simp add:gHom_comp_gsurjec gHom_comp_ginjec)
done

lemma gHomcompTr4:"\<lbrakk> group G; gbijec\<^sub>G\<^sub>,\<^sub>G f;  gbijec\<^sub>G\<^sub>,\<^sub>G g\<rbrakk>
    \<Longrightarrow> gbijec\<^sub>G\<^sub>,\<^sub>G (g \<circ>\<^sub>G f) "
apply (simp add:gHomcompTr3)
done

lemma lunithom:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> (I\<^sub>G) \<circ>\<^sub>F f = f"
apply (simp add:cmpghom_def)
apply (subgoal_tac "f \<in> extensional (carrier F)")
apply (subgoal_tac "compose (carrier F) (I\<^sub>G) f \<in> extensional (carrier F)")
apply (rule extensionalityI, assumption+)
apply (simp add:compose_def)
apply (simp add:idmap_def) 
apply (simp add:gHom_def) apply (erule conjE)+ 
apply (simp add:funcset_mem)
apply (simp add:compose_def extensional_def)
apply (simp add:gHom_def)
done

lemma runithom:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> f \<circ>\<^sub>F (I\<^sub>F) = f"
apply (simp add:cmpghom_def)
apply (subgoal_tac "compose (carrier F) f I\<^sub>F \<in> extensional (carrier F)")
apply (subgoal_tac "f \<in> extensional (carrier F)")
apply (rule extensionalityI, assumption+)
apply (simp add:compose_def idmap_def)
apply (simp add:gHom_def extensional_def)
apply (simp add:compose_def extensional_def)
done


section "9. Image"

lemma invhom:"\<lbrakk> group F; group G; gbijec\<^sub>F\<^sub>,\<^sub>G f \<rbrakk> \<Longrightarrow> (Ifn F G f) \<in> gHom G F"
apply (simp add:gHom_def) 
apply (rule conjI)
 (** Ifn F G f \<in> carrier G \<rightarrow> carrier F **) 
apply (simp add:invfun_def restrict_def extensional_def)
apply (rule conjI)
apply (rule inv_func)
 apply (simp add:gbijec_def gsurjec_def gHom_def)
 apply (simp add:gbijec_def gsurjec_def ginjec_def)+

apply (rule ballI)+ apply (erule conjE)+
 apply (simp add:gHom_def) apply (erule conjE)+
apply (frule_tac f = f and A = "carrier F" and B = "carrier G" in inv_func,
                                  assumption+)
apply (frule_tac a = x and b = y in tOp_closed [of "G"], assumption+)
apply (frule_tac  x = " x \<cdot>\<^sub>G y" in funcset_mem [of "Ifn F G f" "carrier G" 
"carrier F"], assumption+)
apply (frule_tac  x = x in funcset_mem [of "Ifn F G f" "carrier G" 
"carrier F"], assumption+)
apply (frule_tac  x = y in funcset_mem [of "Ifn F G f" "carrier G" 
"carrier F"], assumption+)
apply (frule_tac a = "(Ifn F G f) x" and b = "(Ifn F G f) y" in 
   tOp_closed [of "F"], assumption+)
apply (subgoal_tac "f ((Ifn F G f) ( x \<cdot>\<^sub>G y)) = f (((Ifn F G f) x) \<cdot>\<^sub>F ((Ifn F G f) y))")
apply (simp add:inj_on_def)
apply (simp add:gHom)
apply (simp add:invfun_r)
done

lemma invhom_gbijec:"\<lbrakk> group F; group G; gbijec\<^sub>F\<^sub>,\<^sub>G f \<rbrakk> \<Longrightarrow> gbijec\<^sub>G\<^sub>,\<^sub>F (Ifn F G f)"
apply (frule invhom [of "F" "G" "f"], assumption+)
apply (simp add:gbijec_def)
apply (rule conjI)
(* gsurjec *)
apply (simp add:gsurjec_def ginjec_def) apply (erule conjE)+
apply (simp add:gHom_def) apply (erule conjE)+
 apply (simp add:invfun_surj)
 apply (simp add:gHom_def)
 apply (erule conjE)+
(* ginjec *)
apply (simp add:gsurjec_def ginjec_def)
 apply (erule conjE)+ apply (simp add:gHom_def) apply (erule conjE)+
apply (rule invfun_inj, assumption+)
done

lemma linvhom:"\<lbrakk> group F; group G; gbijec\<^sub>F\<^sub>,\<^sub>G f \<rbrakk> \<Longrightarrow> (Ifn F G f) \<circ>\<^sub>F f = (I\<^sub>F)"  
apply (simp add:gbijec_def gsurjec_def ginjec_def)
apply (erule conjE)+
 apply (simp add:cmpghom_def)
apply (subgoal_tac "compose (carrier F) (Ifn F G f) f \<in> extensional (carrier F)")
apply (subgoal_tac "I\<^sub>F \<in> extensional (carrier F)")
apply (rule extensionalityI, assumption+)
apply (simp add:compose_def idmap_def)
apply (simp add:gHom_def)  apply (erule conjE)+
apply (rule invfun_l [of "f" "carrier F" "carrier G" _], assumption+)
apply (simp add:idmap_def extensional_def)
apply (simp add:compose_def extensional_def)
done
  
lemma imgTr5:"\<lbrakk> group F; group G; f \<in> gHom F G; u \<in> f`(carrier F);
v \<in> f`(carrier F) \<rbrakk> \<Longrightarrow> u \<cdot>\<^sub>G v \<in> f`(carrier F)" 
apply (simp add:image_def)
apply auto
apply (subst gHom [of "F" "G" "f", THEN sym], assumption+)
apply (frule_tac a = x and b = xa in tOp_closed [of "F"], assumption+)
apply auto
done

lemma imgTr6:"\<lbrakk> group F; group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> one G \<in> f`(carrier F)"
apply (simp add:image_def)
apply (frule ghom_unit_unit [of "F" "G" "f"], assumption+)
apply (frule ex_one [of "F"])
apply (frule ghom_unit_unit [of "F" "G" "f", THEN sym], assumption+)
apply auto
done

lemma imgTr7:"\<lbrakk> group F; group G; f \<in> gHom F G; u \<in> f`(carrier F)\<rbrakk>
  \<Longrightarrow> iOp G u  \<in> f`(carrier F)"
apply (simp add:image_def)
apply auto
apply (frule_tac x1 = x in ghom_inv_inv [of "F" "G" "f", THEN sym], assumption+)
apply auto
done

lemma imgTr8:"\<lbrakk> group F; group G; f \<in> gHom F G;  H \<guillemotleft> F; u \<in> f` H; 
  v \<in> f` H \<rbrakk> \<Longrightarrow> tOp G u v \<in> f` H" 
apply (simp add:image_def)
apply auto
apply (subst gHom [of "F" "G" "f" _, THEN sym], assumption+)
 apply (simp add:subg_subset1)+ (*thm subg_tOp_closed [of "F" "H"] *)
 apply (frule_tac ?h1.0 = x and ?h2.0 = xa in subg_tOp_closed [of "F" "H"],
                        assumption+)
 apply auto
done

lemma imgTr9:"\<lbrakk> group F; group G; f \<in> gHom F G;  H \<guillemotleft> F; u \<in> f` H\<rbrakk> 
             \<Longrightarrow> iOp G u \<in> f` H" 
apply (simp add:image_def)
apply auto 
apply (frule_tac x = x in subg_iOp_closed [of "F" "H"], assumption+)
apply (frule_tac x1 = x in  ghom_inv_inv [THEN sym, of "F" "G" "f"], assumption+)
apply (simp add:subg_subset1)
apply auto
done

lemma imgTr10:"\<lbrakk> group F; group G; f \<in> gHom F G; H \<guillemotleft> F\<rbrakk> \<Longrightarrow> one G \<in> f`H"
apply (simp add:image_def)
apply (frule subg_one_closed [of "F" "H"], assumption+)
apply (frule ghom_unit_unit [of "F" "G" "f", THEN sym], assumption+)
apply auto
done

lemma imgTr11:"\<lbrakk> group F; group G; f \<in> gHom F G;  H \<guillemotleft> F\<rbrakk> \<Longrightarrow> (f` H) \<guillemotleft> G"
apply (simp add:subgroup_def [of "G" "f` H"])
apply (rule conjI)
apply (subgoal_tac "f \<in> carrier F \<rightarrow> carrier G")
apply (rule image_sub, assumption+)
 apply (simp add:subgroup_def)
 apply (simp add:gHom_def)
apply (rule conjI)
apply (rule ballI)+ 
 apply (frule_tac ?h1.0 = x and ?h2.0 = y in subg_tOp_closed [of "F" "H"],
                                                   assumption+)
 apply (frule_tac h = x in subg_subset1 [of "F" "H"], assumption+)
 apply (frule_tac h = y in subg_subset1 [of "F" "H"], assumption+)
 apply (subst  gHom [THEN sym, of "F" "G" "f"], assumption+)
 apply (simp add:image_def) apply auto
 apply (frule_tac h = x in subg_subset1 [of "F" "H"], assumption+)
 apply (frule_tac x1 = x in  ghom_inv_inv [THEN sym, of "F" "G" "f"], 
                                                            assumption+)  
 apply simp
 apply (frule_tac x = x in subg_iOp_closed [of "F" "H"], assumption+)
 apply (simp add:image_def) apply auto
apply (frule ghom_unit_unit [of "F" "G" "f", THEN sym], assumption+)
 apply (frule subg_one_closed [of "F" "H"], assumption+)
 apply (simp add:image_def)
 apply auto
done

lemma subgimg:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk>
                          \<Longrightarrow> f`(carrier F) \<guillemotleft> G"  
apply (frule special_subg_G [of "F"])
apply (simp add:imgTr11)
done

lemma img:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> group (img\<^sub>F\<^sub>,\<^sub>G f )"
apply (frule subgimg [of "F" "G" "f"], assumption+)
apply (simp add:img_hom_def subggrp)
done

lemma homtoimg:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> f \<in> gHom F (img\<^sub>F\<^sub>,\<^sub>G f)"
apply (simp add:gHom_def img_hom_def grp_def)
apply (erule conjE)+
 apply (simp add:Pi_def restrict_def)
done

lemma gkertoimg:"\<lbrakk> group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
                                       gker\<^sub>F\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f) f = gker\<^sub>F\<^sub>,\<^sub>G f" 
apply (simp add:gkernel_def)
apply (subgoal_tac "one (img\<^sub>F\<^sub>,\<^sub>G f) = one G")
 apply simp
 apply (simp add:img_hom_def grp_def)
done

lemma Pj_im_subg:"\<lbrakk>group G; H \<guillemotleft> G; K \<lhd> G; K \<subseteq> H\<rbrakk> \<Longrightarrow> 
                         Pj G K ` H = carrier (grp G H / K)"
apply (simp add:qgrp_def [of "grp G H" "K"])
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:image_def)
 apply (auto del:subsetI)
 apply (frule nmlSubgTr0 [of "G" "K"], assumption+)
 apply (frule_tac h = xa in subg_subset1 [of "G" "H"], assumption+)
 apply (simp add:Pj_mem set_r_cos_def)
 apply (subst r_coset_in_subg, assumption+)
 apply (simp add:grp_carrier) apply blast
apply (rule subsetI)
 apply (simp add:set_r_cos_def)
 apply (auto del:equalityI)
 apply (simp add:grp_carrier)
 apply (subst r_coset_in_subg [THEN sym, of "G" "H" "K"], assumption+)
 apply (frule nmlSubgTr0 [of "G" "K"], assumption+)
apply (simp add:image_def)
apply (frule_tac nmlSubgTr0 [of "G" "K"], assumption+)
apply (frule_tac h = a in subg_subset1 [of "G" "H"], assumption+)
apply (frule_tac x1 = a in Pj_mem [THEN sym, of "G" "K"], assumption+)
apply blast
done

lemma subg_Qsubg:"\<lbrakk>group G; H \<guillemotleft> G; K \<lhd> G; K \<subseteq> H\<rbrakk> \<Longrightarrow> 
                       carrier ((grp G H) / K) \<guillemotleft> (G / K)"
apply (frule Pjhom1 [of "G" "K"], assumption+)
apply (frule nsubg_in_subg [of "G" "K" "H"], assumption+)
apply (frule Qgrp [of "G" "K"], assumption+)
apply (frule imgTr11 [of "G" "G / K" "Pj G K" "H"], assumption+)
apply (frule Pj_im_subg [of "G" "H" "K"], assumption+)
apply simp
done

section "10 incuded homomorphisms"

lemma inducedhomTr: "\<lbrakk> group F; group G; f \<in> gHom F G; 
  S \<in> set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f); s1 \<in> S; s2 \<in> S \<rbrakk> \<Longrightarrow> f s1 = f s2"
apply (simp only:set_r_cos_def)
apply (simp add:CollectI)
apply auto 
apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
apply (frule_tac a = a in r_cosTr0 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" _ "s1"], assumption+)
apply (frule_tac a = a in r_cosTr0 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" _ "s2"], assumption+)
apply (frule_tac a1 = a in r_cosEqVar2 [THEN sym, of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" _ "s1"], 
                                                            assumption+)
apply (frule_tac a = a in r_cosEqVar2 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" _ "s2"], 
                                                            assumption+)
apply simp
apply (rule gkernTr9 [of "F" "G" "f" "s1" "s2"], assumption+)
done

constdefs
 ind_hom :: "[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme, 
                ('a  \<Rightarrow> 'b)] \<Rightarrow> ('a set  \<Rightarrow> 'b )"
     "ind_hom F G f == \<lambda>X\<in> (set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f)). f ( \<some> x. x \<in> X)"

syntax 
 "@IND_HOM"::"['a \<Rightarrow> 'b, ('a, 'm) GroupType_scheme, ('b, 'm1) GroupType_scheme]
 \<Rightarrow>  ('a set  \<Rightarrow> 'b )" ("(3_\<dieresis>\<^sub>_\<^sub>,\<^sub>_)" [82,82,83]82)  

translations
    "f\<dieresis>\<^sub>F\<^sub>,\<^sub>G " == "ind_hom F G f"

lemma ind_hom_someTr:"\<lbrakk>group F; group G; f\<in>gHom F G; 
X \<in> set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f)\<rbrakk> \<Longrightarrow> f (SOME xa. xa \<in> X) \<in> f `(carrier F)"
apply (simp add:set_r_cos_def)
apply auto
apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
apply (rule someI2_ex)
apply (frule_tac a = a in aInR_cos [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+) 
apply auto
apply (frule_tac a = a and x = x in r_cosTr0 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+)
apply (simp add:gHom_def) 
done

lemma ind_hom_someTr1:"\<lbrakk>group F; group G; f\<in>gHom F G; a\<in> carrier F\<rbrakk> \<Longrightarrow> 
     f (SOME xa. xa \<in> r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) a) = f a"
apply (rule someI2_ex)
 apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
 apply (frule aInR_cos [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" "a"], assumption+)
 apply blast
 apply (simp add:gkernTr11 [THEN sym])
 apply (simp add:Invim_def)
done

lemma inducedHOMTr0:"\<lbrakk> group F; group G; f \<in> gHom F G; a \<in> carrier F \<rbrakk> \<Longrightarrow>
     (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) (r_coset F (gker\<^sub>F\<^sub>,\<^sub>G f) a) = f a"
apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
apply (frule r_cosTr0_1 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f" "a"], assumption+)
apply (simp add:ind_hom_def)
apply (simp add:ind_hom_someTr1)
done

lemma inducedHOMTr0_1:"\<lbrakk> group F; group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>
    (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) \<in>  set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f) \<rightarrow> carrier G" 
apply (simp add:Pi_def restrict_def ind_hom_def)
 apply (rule allI) apply (rule impI)
 apply (frule_tac X = x in ind_hom_someTr [of "F" "G" "f"], assumption+)
 apply (simp add:gHom_def) apply (erule conjE)+
 apply (thin_tac "\<forall>x\<in>carrier F. \<forall>y\<in>carrier F. f ( x \<cdot>\<^sub>F y) =  f x \<cdot>\<^sub>G (f y)")
apply (frule image_sub [of "f" "carrier F" "carrier G" "carrier F"])
 apply simp
apply (simp add:subsetD)
done

lemma inducedHOMTr0_2:"\<lbrakk> group F; group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>
    (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) \<in>  set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f) \<rightarrow> f` (carrier F)"
apply (frule inducedHOMTr0_1 [of "F" "G" "f"], assumption+)
apply (simp add:Pi_def restrict_def)
apply (rule allI) apply (rule impI)
 apply (simp add:set_r_cos_def)
 apply auto
 apply (simp add: inducedHOMTr0)
done

lemma inducedHom: "\<lbrakk>group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> 
     (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) \<in> gHom (F/(gker\<^sub>F\<^sub>,\<^sub>G f)) G"
apply (simp add: gHom_def [of "F/(gker\<^sub>F\<^sub>,\<^sub>G f)" "G"])
apply (rule conjI)
apply (simp add:ind_hom_def extensional_def)
 apply (rule allI) apply (rule impI)
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f", THEN sym])
 apply simp apply (simp add:qgrp_def)
apply (rule conjI) apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI) 
apply (frule inducedHOMTr0_1 [of "F" "G" "f"], assumption+)
apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f", THEN sym])
apply (simp add:funcset_mem)
apply (rule ballI)+ 
apply (simp add:set_r_cos_def)
apply (auto del:equalityI) 
apply (subst costOpwelldef [THEN sym], assumption+)
 apply (rule gkern, assumption+)
apply (simp add:inducedHOMTr0)
apply (simp add:gHom)
done

lemma ind_hom_ginjec: "\<lbrakk>group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> 
            ginjec\<^sub>(F/(gker\<^sub>F\<^sub>,\<^sub>G f))\<^sub>,\<^sub>G (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G)"
apply (simp add:ginjec_def)
apply (simp add:inducedHom)
apply (simp add:inj_on_def)
apply (rule ballI)+
apply (simp add:qgrp_def)
apply (simp add:set_r_cos_def)
apply (rule impI)
apply auto 
apply (simp add:inducedHOMTr0) (* simp add:inducedHOMTr0 kernTr11[THEN sym] ??*)
apply (simp add: gkernTr11[THEN sym])
apply (simp add:inducedHOMTr0)
apply (simp add: gkernTr11[THEN sym])
done

lemma inducedhomgsurjec:"\<lbrakk>group F; group G; gsurjec\<^sub>F\<^sub>,\<^sub>G f\<rbrakk> \<Longrightarrow>
                                  gsurjec\<^sub>(F/(gker\<^sub>F\<^sub>,\<^sub>G f))\<^sub>,\<^sub>G (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G)"
apply (simp add:gsurjec_def)
apply (simp add:inducedHom)
 apply (erule conjE)
 apply (subgoal_tac "f \<in> carrier F \<rightarrow> carrier G") 
 apply (rule surj_to_test)
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"])
 apply simp 
apply (simp add:inducedHOMTr0_1)
prefer 2 apply (simp add:gHom_def)
 apply (rule ballI)+
 apply (simp add:surj_to_def image_def)
 apply (frule sym) apply (thin_tac "{y. \<exists>x\<in>carrier F. y = f x} = carrier G")
 apply simp
 apply (thin_tac "f \<in> carrier F \<rightarrow> {y. \<exists>x\<in>carrier F. y = f x}")
 apply (thin_tac "carrier G = {y. \<exists>x\<in>carrier F. y = f x}")
apply auto
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"])
 apply simp
 apply (thin_tac "carrier (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) = set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f)") 
 apply (frule_tac a = x in inducedHOMTr0 [of "F" "G" "f"], assumption+)
apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
apply (frule_tac  a = x in  r_cosTr0_1 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+)
 apply blast
done

lemma homomtr: "\<lbrakk>group F; group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> 
   (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) \<in> gHom (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) (img\<^sub>F\<^sub>,\<^sub>G f)"
apply (simp add:gHom_def [of "F/(gker\<^sub>F\<^sub>,\<^sub>G f)" _])
apply (rule conjI)
apply (simp add:ind_hom_def extensional_def)
 apply (rule allI) apply (rule impI)
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f", THEN sym])
  apply simp 
apply (rule conjI)
 apply (frule inducedHOMTr0_1 [of "F" "G" "f"], assumption+)
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"])
 apply simp
apply (simp add:img_hom_def grp_def) 
apply (simp add:inducedHOMTr0_2) 
apply (rule ballI)+
 apply (simp add:img_hom_def grp_def)
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"]) apply simp
 apply (thin_tac "carrier (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) = set_r_cos F ((gker\<^sub>F\<^sub>,\<^sub>G f))")
 apply (simp add:qgrp_def)
apply (simp add:set_r_cos_def)
 apply (auto del:equalityI)
 apply (frule gkern [of "F" "G" "f"], assumption+)
 apply (subst costOpwelldef [THEN sym, of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+)
apply (simp add:inducedHOMTr0)
 apply (simp add:gHom)
done

lemma homom2img: "\<lbrakk>group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> 
   (f\<dieresis>\<^sub>F\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f)) \<in> gHom (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) (img\<^sub>F\<^sub>,\<^sub>G f)"
apply (simp add:gHom_def [of "F/(gker\<^sub>F\<^sub>,\<^sub>G f)" _])
apply (frule gkertoimg [of "F" "G" "f"], assumption+)
apply (rule conjI)
apply (simp add:qgrp_def)
apply (subgoal_tac "carrier (img\<^sub>F\<^sub>,\<^sub>G f) = f `(carrier F)") 
apply (simp add:ind_hom_def extensional_def) 
apply (simp add:img_hom_def grp_def) 
apply (rule conjI)
apply (simp add:Pi_def restrict_def)
apply (rule allI) apply (rule impI)
apply (subgoal_tac "carrier (img\<^sub>F\<^sub>,\<^sub>G f) = f `(carrier F)") 
apply simp
apply (frule inducedHOMTr0_2 [of "F" "img\<^sub>F\<^sub>,\<^sub>G f" "f"])
 apply (simp add:img) apply (simp add:homtoimg)
 apply simp
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"]) apply simp
 apply (simp add:funcset_mem)
apply (simp add:qgrp_def)
apply (simp add:img_hom_def grp_def)

apply (rule ballI)+ 
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"]) apply simp
 apply (thin_tac "carrier (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) = set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f)")
 apply (frule homtoimg [of "F" "G" "f"], assumption+)
apply (simp add:set_r_cos_def)
apply (auto del:equalityI)
apply (frule img [of "F" "G" "f"], assumption+)
apply (frule_tac a = a in inducedHOMTr0 [of "F" "img\<^sub>F\<^sub>,\<^sub>G f" "f"], assumption+)
apply (frule_tac a = aa in inducedHOMTr0 [of "F" "img\<^sub>F\<^sub>,\<^sub>G f" "f"], assumption+)
 apply simp
 apply (simp add:qgrp_def)
 apply (frule gkern [of "F" "G" "f"], assumption+)
 apply (subst costOpwelldef [THEN sym, of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+)
apply (frule_tac a = a and b = aa in tOp_closed [of "F"], assumption+)
apply (frule_tac a = " a \<cdot>\<^sub>F aa" in inducedHOMTr0 [of "F" "img\<^sub>F\<^sub>,\<^sub>G f" "f"], 
                                              assumption+)
 apply simp
 apply (thin_tac "f \<in> gHom F G")
 apply (simp add:gHom)
done

lemma homom2img1:"\<lbrakk>group F; group G; f \<in> gHom F G; X \<in> set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f)\<rbrakk>
 \<Longrightarrow> (f\<dieresis>\<^sub>F\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f)) X = (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) X"
apply (frule gkertoimg [of "F" "G" "f"], assumption+)
apply (simp add:ind_hom_def)
done

subsection "11 Homomorphism therems"

constdefs
  iota :: "('a, 'm) GroupType_scheme \<Rightarrow> ('a \<Rightarrow> 'a)"  
(* used exclusively as an inclusion map *)
          ("(\<iota>\<^sub>_)" [1000]999) 
   "\<iota>\<^sub>F == \<lambda>x\<in>(carrier F). x"

lemma iotahomTr0:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G; h \<in> H \<rbrakk> \<Longrightarrow> (\<iota>\<^sub>(grp G H)) h = h"
apply (subgoal_tac "h \<in> carrier (grp G H)")  
apply (simp add:iota_def)
apply (simp add:grp_def)
done
     
lemma iotahom:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> 
                \<iota>\<^sub>(grp G H) \<in> gHom (grp G H) (grp G (H \<bullet>\<^sub>G N))" 
apply (simp add:gHom_def)
apply (rule conjI)
 apply (simp add:iota_def extensional_def)
apply (rule conjI)
apply (simp add:Pi_def restrict_def iota_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:grp_def)
 apply (frule nmlSubgTr0, assumption+)
 apply (frule settOpTr7 [of "G" "H" "N"], assumption+)
 apply (rule subsetD [of "H" "H \<bullet>\<^sub>G N"], assumption+)
apply (rule ballI)+
 apply (frule settOpTr7 [of "G" "H" "N"], assumption+)
 apply (simp add:nmlSubgTr0)
 apply (simp add:iota_def)
 apply (simp add:grp_def)
 apply (frule_tac ?h1.0 = x and ?h2.0 = y in subg_tOp_closed [of "G" "H"],
                                                  assumption+)
apply simp
done

lemma iotaTr0: "\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> 
                    ginjec\<^sub>(grp G H)\<^sub>,\<^sub>(grp G (H \<bullet>\<^sub>G N)) (\<iota>\<^sub>(grp G H))"
apply (simp add:ginjec_def)
apply (simp add:iotahom)
apply (simp add:inj_on_def iota_def grp_def)
done

theorem homomthm1: "\<lbrakk>group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
  gbijec\<^sub>(F/(gker\<^sub>F\<^sub>,\<^sub>G f))\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f) (f\<dieresis>\<^sub>F\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f))"
apply (frule homom2img [of "F" "G" "f"], assumption+)
apply (simp add:gbijec_def)
apply (frule homtoimg [of "F" "G" "f"], assumption+)
apply (rule conjI)
 (** gsurjec **)
 apply (simp add:gsurjec_def)
 apply (frule Qgrp_carrierTr [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"])
 apply simp
 apply (thin_tac "carrier (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) = set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f)")
 apply (subgoal_tac "f\<dieresis>\<^sub>F\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f) \<in> set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f) \<rightarrow> 
                                                    carrier (img\<^sub>F\<^sub>,\<^sub>G f)")
 apply (rule surj_to_test, assumption+)
apply (rule ballI)
 apply (subgoal_tac "carrier (img\<^sub>F\<^sub>,\<^sub>G f) = f `(carrier F)")
 apply simp
 apply (thin_tac "carrier (img\<^sub>F\<^sub>,\<^sub>G f) = f ` carrier F")
 apply (thin_tac "f\<dieresis>\<^sub>F\<^sub>,\<^sub>(img\<^sub>F\<^sub>,\<^sub>G f) \<in> set_r_cos F (gker\<^sub>F\<^sub>,\<^sub>G f ) \<rightarrow> f ` carrier F")
 apply (simp add:image_def)
apply (auto del:equalityI)
 apply (frule  gkernTr7 [of "F" "G" "f"], assumption+)
 apply (frule_tac a = x in r_cosTr0_1 [of "F" "gker\<^sub>F\<^sub>,\<^sub>G f"], assumption+)
 apply (frule img[of "F" "G" "f"], assumption+)
 apply (frule_tac a = x in inducedHOMTr0 [of "F" "img\<^sub>F\<^sub>,\<^sub>G f" "f"], assumption+)
 apply (frule gkertoimg [of "F" "G" "f"], assumption+)  apply simp
 apply (auto del:equalityI)
apply (simp add:img_hom_def grp_def)
apply (simp add:gHom_def [of "F / (gker\<^sub>F\<^sub>,\<^sub>G f)" _])
 apply (erule conjE)+ apply (simp add:qgrp_def)
 (** gsurjec done **)
(** ginjec **)
apply (frule ind_hom_ginjec[of "F" "G" "f"], assumption+)
 apply (simp add:ginjec_def) 
 apply (frule conj_2)
  apply (thin_tac "f\<dieresis>\<^sub>F\<^sub>,\<^sub>G \<in> gHom (F / (gker\<^sub>F\<^sub>,\<^sub>G f)) G \<and>
       inj_on (f\<dieresis>\<^sub>F\<^sub>,\<^sub>G) (carrier (F / (gker\<^sub>F\<^sub>,\<^sub>G f)))")
 apply (simp add:inj_on_def)
apply (rule ballI)+ apply (rule impI) 
apply (simp add:qgrp_def) apply (fold qgrp_def)
apply (simp add:homom2img1) 
done

lemma isomTr0 [simp]:"group F \<Longrightarrow> F \<cong> F"
apply (frule IdTr2 [of "F"])
 apply (simp add:isomorphism_def)
 apply auto
done

lemma isomTr1:"\<lbrakk>group F; group G; F \<cong>  G \<rbrakk> \<Longrightarrow> G \<cong> F"
apply (simp add:isomorphism_def)
apply auto
apply (frule_tac f = f in invhom_gbijec [of "F" "G"], assumption+)
apply auto
done
 
lemma isomTr2:"\<lbrakk>group F; group G; group H; F \<cong> G; G \<cong> H \<rbrakk> \<Longrightarrow> F \<cong> H"
apply (simp add:isomorphism_def)
apply auto
apply (simp add:gbijec_def)
 apply (erule conjE)+
apply (frule gHom_comp_gsurjec [of "F" "G" "H" _ _], assumption+)
apply (frule gHom_comp_ginjec [of "F" "G" "H" _ _], assumption+)
apply auto
done
 
lemma gisom1: "\<lbrakk>group F; group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
     (F/ (gker\<^sub>F\<^sub>,\<^sub>G f)) \<cong> (img\<^sub>F\<^sub>,\<^sub>G f)"
apply (simp add:isomorphism_def)
apply (frule homomthm1 [of "F" "G" "f"], assumption+)
apply auto
done

lemma homomth2Tr0: "\<lbrakk>group F; group G; f \<in> gHom F G; N \<lhd> G \<rbrakk> \<Longrightarrow>   
                           (Invim F G f N) \<lhd> F "
apply (rule nmlSubg2, assumption+)
 apply (rule ghomTr4, assumption+)
 apply (simp add:nmlSubgTr0)
apply (rule ballI)+
 apply (simp add:Invim_def)
 apply (simp add:gHom)
 apply (simp add:ghom_inv_inv)
 apply (subgoal_tac "f a \<in> carrier G")
apply (simp add:NSubgPr1_1)
 apply (subgoal_tac "f \<in> carrier F \<rightarrow> carrier G")
 apply (simp add:funcset_mem)
 apply (simp add:gHom_def)
done

lemma QgrpUnit_1:"\<lbrakk> group G; Ugp E; H \<lhd> G; (G / H) \<cong> E \<rbrakk> \<Longrightarrow> carrier G = H"
apply (simp add:isomorphism_def)
apply (auto del:equalityI)
 apply (simp add:gbijec_def)
apply (erule conjE)
  apply (simp add:gsurjec_def)
 apply (erule conjE)
 apply (simp add:ginjec_def)
 apply (frule Qgrp [of "G" "H"], assumption+)
 apply (simp add:Ugp_def) apply (erule conjE)
 apply (frule_tac f = f in ghom_unit_unit [of "G / H" "E"], assumption+)
 apply (simp add:Qgrp_one)
apply (frule Qgrp_carrierTr [of "G" "H"]) apply simp
 apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
 apply (frule subg_subset [of "G" "H"], assumption+)
apply (rule equalityI)
 prefer 2 apply assumption
 apply (rule subsetI)
 apply (frule_tac a = x in r_cosTr0_1 [of "G" "H"], assumption+)
 apply (frule ex_Qgrp_one [of "G" "H"], assumption+)
apply (simp add:gHom_def) apply (erule conjE)+
 apply (frule_tac f = f in funcset_mem [of _ "set_r_cos G H" "{1\<^sub>E}"], 
                                               assumption+)
 apply simp
  apply (thin_tac "\<forall>x\<in>set_r_cos G H.
                \<forall>y\<in>set_r_cos G H. f ( x \<cdot>\<^sub>(G / H) y) =  f x \<cdot>\<^sub>E (f y)")
 apply (simp add:inj_on_def) apply (rotate_tac -1)
 apply (frule sym) apply (thin_tac "f (H\<^sub>G x) = 1\<^sub>E") apply simp
  apply(thin_tac "1\<^sub>E = f (H\<^sub>G x)")
  apply (thin_tac "surj_to f (set_r_cos G H) {f (H\<^sub>G x)}")
  apply (thin_tac "carrier E = {f (H\<^sub>G x)}")
  apply (thin_tac "carrier (G / H) = set_r_cos G H")
  apply (thin_tac "f \<in> extensional (set_r_cos G H)")
  apply (thin_tac "f \<in> set_r_cos G H \<rightarrow> {f (H\<^sub>G x)}")
apply (subgoal_tac "H = H\<^sub>G x")
  apply (thin_tac "\<forall>x\<in>set_r_cos G H. \<forall>y\<in>set_r_cos G H. f x = f y \<longrightarrow> x = y")
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "H = H\<^sub>G x")
 apply (frule_tac  a = x in aInR_cos [of "G" "H"], assumption+) 
 apply simp
apply auto
done
    
lemma QgrpUnit_2:"\<lbrakk>group G; Ugp E; H \<lhd> G; carrier G = H \<rbrakk> \<Longrightarrow> (G/H) \<cong> E"
apply (frule Qgrp [of "G" "H"], assumption+)
apply (subgoal_tac "carrier (G/H) = {one (G/H)}") 
 apply (subgoal_tac "Ugp (G/H)")
  apply (simp add:unitGroups_isom)
 apply (simp add:Ugp_def)
 apply (frule Qgrp_carrierTr [of "G" "H"])
 apply simp
 apply (subst Qgrp_one, assumption+)
 apply (frule ex_Qgrp_one [of "G" "H"], assumption+)
apply (rule  equalityI)   
prefer 2  apply simp
 apply (rule subsetI) apply (simp add:set_r_cos_def)
 apply (subgoal_tac "\<forall>a\<in>H. x =  H\<^sub>G a \<longrightarrow> x = H") apply blast 
                     (* auto makes a complicated situation a little *) 
 apply (thin_tac "\<exists>a\<in>H. x = H\<^sub>G a")
apply (rule ballI) apply (rule impI)
 apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
 apply (frule_tac x = a in r_cosUnit1_1 [of "G" "H"], assumption+)
apply auto
done

lemma QgrpUnit_3:"\<lbrakk> group G; Ugp E; H \<guillemotleft> G; H1 \<guillemotleft> G; H1 \<lhd> (grp G H);
 ((grp G H) / H1) \<cong> E \<rbrakk> \<Longrightarrow> H = H1"
apply (frule subggrp [of "G" "H"], assumption+)
apply (frule QgrpUnit_1 [of "grp G H" "E" "H1"], assumption+)
apply (simp add:grp_carrier)
done

lemma QgrpUnit_4:"\<lbrakk> group G; Ugp E; H \<guillemotleft> G; H1 \<guillemotleft> G; H1 \<lhd> (grp G H);
\<not> ((grp G H) / H1) \<cong> E \<rbrakk> \<Longrightarrow> H \<noteq> H1"
apply (frule subggrp [of "G" "H"], assumption+)
apply (rule contrapos_pp, simp) apply simp
apply (frule QgrpUnit_2 [of "grp G H1" "E" "H1"], assumption+)
apply (simp add:grp_carrier)
apply simp
done

constdefs
  Qmp :: "[('a, 'm) GroupType_scheme, 'a set, 'a set] \<Rightarrow> ('a set \<Rightarrow> 'a set)"
   "Qmp G H N == \<lambda>X\<in> set_r_cos G H. {z. \<exists> x \<in> X. \<exists> y \<in> N. (y \<cdot>\<^sub>G x = z)}"
  
syntax
   "@QP" :: "['a GroupType, 'a set, 'a set] \<Rightarrow> ('a set \<Rightarrow> 'a set)"
               ("(3Qp\<^sub>_\<^sub>'/'\<^sub>_\<^sub>,\<^sub>_)" [82,82,83]82)
translations
   "Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N" == "Qmp G H N"

 (* "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow>
           Qmp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N  \<in> gHom (G / H) (G / N)"  *)

  (* show Qmp G H N is a welldefined map from G/H to G/N. step1 *)
 

lemma QmpTr0: "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N ; a \<in> carrier G\<rbrakk> \<Longrightarrow>
        Qmp G H N (r_coset G H a) = (r_coset G N a)"
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule_tac a = a in r_cosTr0_1 [of "G" "H"], assumption+)
apply (simp add:Qmp_def)
apply auto   
apply (simp add:r_coset_def)
apply (auto del:equalityI)
apply (frule nmlSubgTr0 [of "G" "N"], assumption+)
apply (frule_tac h = y in subg_subset1 [of "G" "N"], assumption+)
apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
apply (subst tOp_assoc [THEN sym], assumption+)
apply (frule_tac c = h in subsetD [of "H" "N"], assumption+)
apply (frule_tac ?h1.0 = y and ?h2.0 = h in subg_tOp_closed [of "G" "N"],
                 assumption+)
apply auto
apply (frule aInR_cos [of "G" "H" "a"]) apply (simp add:nmlSubgTr0)
apply assumption
apply (subgoal_tac "\<exists>n\<in>N. n \<cdot>\<^sub>G a = x") prefer 2 apply (simp add:r_coset_def)
apply auto
done

  (* show Qmp G H N is a welldefined map from G/H to G/N. step2 *)
lemma QmpTr1:"\<lbrakk>group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N; a \<in> carrier G; b \<in> carrier G; (r_coset G H a) = (r_coset G H b)\<rbrakk> \<Longrightarrow> (r_coset G N a) = (r_coset G N b)"
apply (frule_tac nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule_tac nmlSubgTr0 [of "G" "N"], assumption+)
apply (frule  r_cosEqVar1 [of "G" "H" "a" "b"], assumption+)
apply (frule subsetD [of "H" "N" "b \<cdot>\<^sub>G a\<inverse>\<^sup>G"], assumption+)
apply (rule  r_cosEq, assumption+)
done
   
lemma QmpTr2:"\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N ; X \<in> carrier (G/H)\<rbrakk> \<Longrightarrow>
        (Qmp G H N) X \<in> carrier (G/N)" 
apply (simp add:qgrp_def)
apply (simp add:set_r_cos_def)
apply auto
 apply (frule_tac a = a in QmpTr0 [of "G" "H" "N"], assumption+)
apply auto
done

lemma QmpTr2_1:"\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow> 
      Qmp G H N \<in> carrier (G/H) \<rightarrow> carrier (G/N)"
apply (simp add:Pi_def restrict_def)
apply (auto del:equalityI)
apply (simp add:QmpTr2 [of "G" "H" "N" _])
done

lemma QmpTr3:"\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N ; 
X \<in> carrier (G/H); Y \<in> carrier (G/H)\<rbrakk> \<Longrightarrow> 
  (Qmp G H N) (costOp G H X Y) = costOp G N ((Qmp G H N) X) ((Qmp G H N) Y)" 
apply (simp add:qgrp_def)
apply (simp add:set_r_cos_def)
apply (auto del:equalityI)
apply (subst costOpwelldef [THEN sym], assumption+)
apply (frule_tac  a = a and b = aa in tOp_closed [of "G"], assumption+)
apply (simp add:QmpTr0)
apply (subst costOpwelldef [THEN sym], assumption+)
apply simp
done
     
lemma QmpTr4: "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N; a \<in> N \<rbrakk> \<Longrightarrow>
             r_coset (grp G N) H a = r_coset G H a"
apply (frule nsubg_in_subg [of "G" "H" "N"], assumption+)
apply (simp add:nmlSubgTr0)
apply assumption
apply (simp add:r_coset_def)
apply (simp add:grp_def)
done

lemma QmpTr5: "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N; X \<in> carrier (G/H);
      Y \<in> carrier (G/H) \<rbrakk> \<Longrightarrow> (Qmp G H N) ( X \<cdot>\<^sub>(G / H) Y) =
              ((Qmp G H N) X) \<cdot>\<^sub>(G / N) ((Qmp G H N) Y)"
apply (frule QmpTr2_1 [of "G" "H" "N"], assumption+)
apply (frule QmpTr3 [of "G" "H" "N" "X" "Y"], assumption+)
apply (simp add:qgrp_def)
done

lemma QmpTr: "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow>
               (Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N) \<in> gHom (G / H) (G / N)"
apply (simp add:gHom_def)
apply (rule conjI)  
 apply (simp add:Qmp_def extensional_def)
apply (rule allI) 
apply (rule impI) 
apply (frule Qgrp_carrierTr [of "G" "H"])
 apply simp
 apply (simp add:qgrp_def)
apply (rule conjI)
apply (frule Qgrp_carrierTr [THEN sym, of "G" "H"])
apply (frule Qgrp_carrierTr [THEN sym, of "G" "N"]) 
apply (simp add:QmpTr2_1 [of "G" "H" "N"])      
apply (rule ballI)+
apply (frule Qgrp_carrierTr [THEN sym, of "G" "H"]) 
apply simp
apply (rule QmpTr3, assumption+) 
done
     
lemma Qmpgsurjec: "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow>
               gsurjec\<^sub>(G / H)\<^sub>,\<^sub>(G / N) (Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N)"  
apply (frule QmpTr [of "G" "H" "N"], assumption+) 
apply (simp add:gsurjec_def)
 apply (simp add:qgrp_def) 
 apply (fold qgrp_def)
apply (rule surj_to_test)
apply (frule Qgrp_carrierTr [of "G" "H"])
apply (frule Qgrp_carrierTr [of "G" "N"])  
 apply (simp add:gHom_def)
apply (rule ballI)
apply (simp add:set_r_cos_def [of "G" "N"])
apply (auto del:equalityI)
apply (frule_tac a = a in QmpTr0 [of "G" "H" "N"], assumption+)
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule_tac a = a in r_cosTr0_1 [of "G" "H"], assumption+)
apply (auto del:equalityI)
done

lemma gkerQmp: "\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow>
               gker\<^sub>(G / H)\<^sub>,\<^sub>(G / N) (Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N) = carrier ((grp G N)/H)"   
apply (simp add:gkernel_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI) apply (erule conjE)
 apply (simp add:qgrp_def)
  apply (simp add:set_r_cos_def)
 apply (auto del:equalityI)
 apply (simp add:QmpTr0)
 apply (frule nmlSubgTr0 [of "G" "N"], assumption+)
 apply (frule_tac a = a in aInR_cos [of "G" "N"], assumption+)
 apply simp
apply (simp add:grp_def) apply (fold grp_def)
 apply (frule_tac a1 = a in QmpTr4 [THEN sym, of "G" "H" "N"], assumption+) 
apply (auto del:equalityI)
apply (simp add:qgrp_def)
apply (simp add:set_r_cos_def)
apply (auto del:equalityI)
apply (simp add:grp_def) apply (fold grp_def)
apply (simp add:QmpTr4)
apply (frule nmlSubgTr0 [of "G" "N"], assumption+)
apply (frule subg_subset1, assumption+)
apply (auto del:equalityI)

apply (simp add:qgrp_def)
apply (simp add:set_r_cos_def)
apply (auto del:equalityI)
apply (simp add:grp_def) apply (fold grp_def)
apply (simp add:QmpTr4)
apply (frule nmlSubgTr0 [of "G" "N"], assumption+)
apply (frule_tac h = a in subg_subset1, assumption+)
apply (simp add:QmpTr0)
apply (simp add:r_cosUnit1_1 [of "G" "N"])
done

theorem homom2:"\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow>
      gbijec\<^sub>((G/H)/(carrier ((grp G N)/H)))\<^sub>,\<^sub>(G/N) ((Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N)\<dieresis>\<^sub>(G/H)\<^sub>,\<^sub>(G/N))"
apply (frule QmpTr [of "G" "H" "N"], assumption+)
apply (simp add:gbijec_def)
apply (rule conjI)
apply (frule Qgrp [of "G" "H"], assumption+)
apply (frule Qgrp [of "G" "N"], assumption+)
apply (frule inducedHom [of "G/H" "G/N" " Qmp G H N"], assumption+)
(** show  surj_to (Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N\<dieresis>\<^sub>(G / H)\<^sub>,\<^sub>(G / N))
        (carrier (G / H / carrier (grp G N / H))) (carrier (G / N)) *)
apply (frule Qmpgsurjec [of "G" "H" "N"], assumption+)
apply (frule inducedhomgsurjec [of "G/H" "G/N" "Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N"], assumption+)
apply (frule inducedhomgsurjec [of "G/H" "G/N" "Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N"], assumption+)
apply (simp add:gkerQmp [of "G" "H" "N"])
(** show ginjec\<^sub>(G / H / carrier (grp G N / H))\<^sub>,\<^sub>(G / N)
          (Qp\<^sub>G\<^sub>/\<^sub>H\<^sub>,\<^sub>N\<dieresis>\<^sub>(G / H)\<^sub>,\<^sub>(G / N))  **)
apply (frule QmpTr [of "G" "H" "N"], assumption+)
apply (frule Qgrp [of "G" "H"], assumption+)
apply (frule Qgrp [of "G" "N"], assumption+)
apply (frule ind_hom_ginjec [of "G/H" "G/N" "Qmp G H N"], assumption+)
apply (simp add:gkerQmp [of "G" "H" "N"])
done

section "12. Isomorphims"

theorem isom2:"\<lbrakk> group G; H \<lhd> G; N \<lhd> G; H \<subseteq> N \<rbrakk> \<Longrightarrow>
     ((G/H)/(carrier ((grp G N)/H))) \<cong>  (G/N)"
apply (frule homom2 [of "G" "H" "N"], assumption+)
 apply (simp add:isomorphism_def)
 apply blast
done

theorem homom3: "\<lbrakk> group F; group G; N \<lhd> G; gsurjec\<^sub>F\<^sub>,\<^sub>G f; 
 N1 = (Invim F G f) N \<rbrakk> \<Longrightarrow> (F/N1) \<cong> (G/N)"
apply (frule Pj_gsurjec [of "G" "N"], assumption+)
apply (frule Qgrp [of "G" "N"], assumption+)
apply (frule gHom_comp_gsurjec [of "F" "G" "G / N" "f" "Pj G N"], assumption+)
apply (frule inducedhomgsurjec [of "F" "G / N" "(Pj G N) \<circ>\<^sub>F f"], assumption+)
apply (frule ind_hom_ginjec [of "F" "G / N" "(Pj G N) \<circ>\<^sub>F f"], assumption+) 
 apply (simp add:gsurjec_def [of "F" "G / N" "(Pj G N) \<circ>\<^sub>F f"])
apply (subgoal_tac "gker\<^sub>F\<^sub>,\<^sub>(G / N) (Pj G N \<circ>\<^sub>F f) = N1")
apply (frule sym) apply (thin_tac "N1 = Invim F G f N")
 apply (simp add:isomorphism_def) apply (simp add:gbijec_def)
 apply (auto del:equalityI)
 
 apply (thin_tac "gsurjec\<^sub>F\<^sub>,\<^sub>(G / N) (Pj G N \<circ>\<^sub>F f)")
 apply (thin_tac "gsurjec\<^sub>G\<^sub>,\<^sub>(G / N) (Pj G N)")
 apply (thin_tac "gsurjec\<^sub>(F / gker\<^sub>F\<^sub>,\<^sub>(G / N)(Pj G N \<circ>\<^sub>F f) )\<^sub>,\<^sub>(G / N)
          (Pj G N \<circ>\<^sub>F f\<dieresis>\<^sub>F\<^sub>,\<^sub>(G / N))")
 apply (thin_tac "ginjec\<^sub>(F / gker\<^sub>F\<^sub>,\<^sub>(G / N)(Pj G N \<circ>\<^sub>F f) )\<^sub>,\<^sub>(G / N)
          (Pj G N \<circ>\<^sub>F f\<dieresis>\<^sub>F\<^sub>,\<^sub>(G / N))")

apply (simp add:gkernel_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
apply (simp add:cmpghom_def composition)
apply (simp add:gsurjec_def) apply (erule conjE)
apply (simp add:gHom_def) apply (erule conjE)+
apply (frule_tac x = x in funcset_mem [of "f" "carrier F" "carrier G"],
                                              assumption+)
apply (frule  Pj_mem, assumption+)
apply (simp add:compose_def Qgrp_one)
 apply (simp add:Invim_def)
 apply (rule r_coset_fixed, assumption+) 
 apply (simp add:nmlSubgTr0) 
 apply (simp add:funcset_mem)
 apply assumption

 apply (rule subsetI)
 apply (simp add:Invim_def)
 apply (erule conjE)
 apply (simp add:cmpghom_def composition compose_def)
 apply (frule nmlSubgTr0 [of "G" "N"], assumption+)
 apply (frule subg_subset1, assumption+)
 apply (simp add:Pj_mem Qgrp_one) 
 apply (frule_tac x = "f x" in r_cosUnit1_1 [of "G" "N"], assumption+)
done

lemma homom3Tr1:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> H \<inter> N =  
gker\<^sub>(grp G H)\<^sub>,\<^sub>((grp G (H \<bullet>\<^sub>G N))/N)  ((Pj (grp G (H \<bullet>\<^sub>G N)) N) \<circ>\<^sub>(grp G H) (\<iota>\<^sub>(grp G H)))"  
apply (simp add:gkernel_def)
apply (frule nmlSubgTr0, assumption+)
apply (simp add:grp_carrier[of "G" "H"])
apply (frule subgns, assumption+) 
apply (frule nnsubg, assumption+)
 apply (frule subggrp [of "G" "H \<bullet>\<^sub>G N"], assumption+)
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (simp add: Qgrp_one [of "grp G (H \<bullet>\<^sub>G N)" "N"])
 apply (simp add:cmpghom_def compose_def)
 apply (frule grp_carrier [of "G" "H"], assumption+) apply simp
 apply (simp add:iota_def)
 apply (subst Pj_mem [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
 apply (frule NinHNTr0_1, assumption+) apply (erule conjE)
 apply (subst grp_carrier [of "G" "H \<bullet>\<^sub>G N"], assumption+) 
 apply (simp add:subsetD)
 apply (erule conjE)
 apply (rule  r_cosUnit1_1 [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+) 
 apply (simp add:nmlSubgTr0) apply assumption

apply (simp add: Qgrp_one [of "grp G (H \<bullet>\<^sub>G N)" "N"] del:Int_subset_iff)
 apply (rule subsetI)
 apply (simp add:CollectI) apply (erule conjE)
 apply (simp add:cmpghom_def compose_def)
 apply (frule grp_carrier [of "G" "H"], assumption+) apply simp
 apply (simp add:iota_def)
 apply (frule grp_carrier [of "G" "H \<bullet>\<^sub>G N"], assumption+)
 apply (frule settOpTr7 [of "G" "H" "N"], assumption+)
 apply (frule_tac c = x in subsetD [of "H" "H \<bullet>\<^sub>G N"], assumption+)
 apply (frule Pj_mem [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
 apply simp apply simp
 apply (rule r_coset_fixed [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
  apply (simp add:nmlSubgTr0)
  apply simp
  apply assumption
done

section "13. Zassenhaus"

text{* we show H \<rightarrow> H N/N is gsurjective *}

lemma homom3Tr2:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow>  
gsurjec\<^sub>(grp G H)\<^sub>,\<^sub>((grp G (H \<bullet>\<^sub>G N))/N) ((Pj (grp G (H \<bullet>\<^sub>G N)) N) \<circ>\<^sub>(grp G H)
 (\<iota>\<^sub>(grp G H)))"
 apply (frule iotahom, assumption+)
 apply (frule subgns1 [of "G" "H" "N"], assumption+)
 apply (frule nnsubg [of "G" "H" "N"], assumption+)
 apply (frule Pj_gsurjec [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
 apply (simp add:gsurjec_def [of "grp G H" _  _])
  apply (simp add:gsurjec_def)
 apply (frule subggrp [of "G" "H"], assumption+)
 apply (frule gHomcomp [of "grp G H" "grp G (H \<bullet>\<^sub>G N)" "(grp G (H \<bullet>\<^sub>G N) / N)"
  "\<iota>\<^sub>(grp G H)" "Pj (grp G (H \<bullet>\<^sub>G N)) N"], assumption+)
 apply (simp add:Qgrp)
 apply simp+
apply (simp add:gHom_def [of "grp G H" "(grp G (H \<bullet>\<^sub>G N) / N)"])
 apply (erule conjE)+
 apply (thin_tac " \<forall>x\<in>carrier (grp G H).
          \<forall>y\<in>carrier (grp G H).
             (Pj (grp G (H \<bullet>\<^sub>G N)) N \<circ>\<^sub>(grp G H) \<iota>\<^sub>(grp G H)) ( x \<cdot>\<^sub>(grp G H) y) =
              ((Pj (grp G (H \<bullet>\<^sub>G N)) N \<circ>\<^sub>(grp G H) \<iota>\<^sub>(grp G H)) x)
                \<cdot>\<^sub>(grp G (H \<bullet>\<^sub>G N) / N)
                ((Pj (grp G (H \<bullet>\<^sub>G N)) N \<circ>\<^sub>(grp G H) \<iota>\<^sub>(grp G H)) y)")
 apply (rule surj_to_test [of "Pj (grp G (H \<bullet>\<^sub>G N)) N \<circ>\<^sub>(grp G H) \<iota>\<^sub>(grp G H)" 
 "carrier (grp G H)" "carrier (grp G (H \<bullet>\<^sub>G N) / N)"], assumption+)
 apply (rule ballI)
 apply (simp add:Qgrp_carrierTr [of "grp G (H \<bullet>\<^sub>G N)" "N"])
 apply (thin_tac " surj_to (Pj (grp G (H \<bullet>\<^sub>G N)) N) (carrier (grp G (H \<bullet>\<^sub>G N)))
            (set_r_cos (grp G (H \<bullet>\<^sub>G N)) N)")
 apply (thin_tac " Pj (grp G (H \<bullet>\<^sub>G N)) N
           \<in> gHom (grp G (H \<bullet>\<^sub>G N)) (grp G (H \<bullet>\<^sub>G N) / N)")
 apply (thin_tac "Pj (grp G (H \<bullet>\<^sub>G N)) N \<circ>\<^sub>(grp G H) \<iota>\<^sub>(grp G H)
           \<in> extensional (carrier (grp G H))")
 apply (thin_tac "Pj (grp G (H \<bullet>\<^sub>G N)) N \<circ>\<^sub>(grp G H) \<iota>\<^sub>(grp G H)
           \<in> carrier (grp G H) \<rightarrow> set_r_cos (grp G (H \<bullet>\<^sub>G N)) N")
 apply (thin_tac "\<iota>\<^sub>(grp G H) \<in> gHom (grp G H) (grp G (H \<bullet>\<^sub>G N))")
 apply (simp add:set_r_cos_def)
apply (auto del:equalityI)
 apply (frule grp_carrier [of "G" "H \<bullet>\<^sub>G N"])
  apply (simp add:subgns)

apply simp
 apply (thin_tac "carrier (grp G (H \<bullet>\<^sub>G N)) = H \<bullet>\<^sub>G N")
 apply (subgoal_tac "\<exists>x\<in>H. \<exists>y\<in>N.  x \<cdot>\<^sub>G y = a")
 apply (auto del:equalityI)
 apply (simp add:cmpghom_def iota_def compose_def)
 prefer 2 apply (simp add:settOp_def)
 apply (frule nmlSubgTr0 [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
 apply (frule nmlSubgTr0 [of "G" "N"], assumption+)
 apply (frule settOpTr7 [of "G" "H" "N"], assumption+)
 apply (frule subsetD [of "H" "H \<bullet>\<^sub>G N"], assumption+)
 apply (frule subgns [of "G" "H" "N"], assumption+)
 apply (frule grp_carrier [of "G" "H \<bullet>\<^sub>G N"], assumption+)
 apply (frule_tac a = x and b = " x \<cdot>\<^sub>G y" in r_cosEq [of "grp G (H \<bullet>\<^sub>G N)" "N"],
                                                assumption+)
 apply simp+
apply (simp add:grp_def) apply (fold grp_def)
apply (rule NSubgPr1_1 [of "G" "N"], assumption+)
 apply (simp add:subg_subset1)
 apply simp
 apply (frule grp_carrier [of "G" "H"], assumption+) apply simp
 apply (frule_tac x = x in Pj_mem [of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
 apply simp
apply (auto del:equalityI)
done

lemma homom4Tr1:"\<lbrakk> group G; N \<lhd> G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow>  group ((grp G (H \<bullet>\<^sub>G N)) / N)" 
apply (frule subgns1[of "G" "H" "N"], assumption+)
apply (frule nnsubg [of "G" "H" "N"], assumption+)
 apply (simp add:Qgrp)
done

theorem homom4: "\<lbrakk>group G; N \<lhd> G; H \<guillemotleft> G\<rbrakk> \<Longrightarrow>gbijec\<^sub>((grp G H)/(H \<inter> N))\<^sub>,\<^sub>((grp G (H \<bullet>\<^sub>G N)) / N) (((Pj (grp G (H \<bullet>\<^sub>G N)) N) \<circ>\<^sub>(grp G H) (\<iota>\<^sub>(grp G H)))\<dieresis>\<^sub>(grp G H)\<^sub>,\<^sub>((grp G (H \<bullet>\<^sub>G N)) / N))"
            
apply (frule homom3Tr2 [of "G" "H" "N"], assumption+)
apply (frule subgns1, assumption+)
apply (frule homom4Tr1[of "G" "N" "H"], assumption+)
apply (frule subggrp [of "G" "H"], assumption+)
apply (frule ind_hom_ginjec [of "grp G H" "(grp G (H \<bullet>\<^sub>G N)/N)" "(Pj (grp G (H \<bullet>\<^sub>G N)) N) \<circ>\<^sub>(grp G H) (\<iota>\<^sub>(grp G H))"], assumption+) 
 apply (simp add:gsurjec_def)
apply (frule inducedhomgsurjec [of "grp G H" "(grp G (H \<bullet>\<^sub>G N))/N" "(Pj (grp G (H \<bullet>\<^sub>G N)) N) \<circ>\<^sub>(grp G H) (\<iota>\<^sub>(grp G H))"], assumption+)
 apply (frule homom3Tr1[of "G" "H" "N"], assumption+)
 apply simp
apply (simp add:gbijec_def)   
done

lemma homom4_2: "\<lbrakk> group G; N \<lhd> G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> group ((grp G H) / (H \<inter> N))" 
 apply (subgoal_tac "(H \<inter> N) \<lhd> grp G H")
 apply (rule Qgrp)
 apply (simp add:subggrp) apply assumption+
apply (rule nmlSubg2 [of "grp G H" "H \<inter> N"])
apply (simp add:subggrp)
 apply (rule subg_in_subg, assumption+)
 apply (rule inter_subgs, assumption+) apply (simp add:nmlSubgTr0)
 apply assumption+ apply (rule subsetI) apply simp
apply (rule ballI)+
apply (simp add:grp_def) apply (erule conjE)
 apply (frule_tac x = a in subg_iOp_closed [of "G" "H"], assumption+)
 apply (frule_tac ?h1.0 = a and ?h2.0 = h in subg_tOp_closed [of "G" "H"],
                                              assumption+)
apply (rule conjI)
 apply (rule subg_tOp_closed [of "G" "H"], assumption+)+
 apply (rule NSubgPr1_1 [of "G" "N"], assumption+)
  apply (simp add:subg_subset1) apply assumption+
done

lemma  isom4: "\<lbrakk> group G; N \<lhd> G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow>
                 ((grp G H)/(H \<inter> N)) \<cong>  ((grp G (N \<bullet>\<^sub>G H)) / N)"
apply (frule homom4 [of "G" "N" "H"], assumption+)
apply (frule subgnsubg [of "G" "H" "N"], assumption+)
 apply simp
 apply (simp add:isomorphism_def)
 apply auto
done

lemma ZassenhausTr5: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow>   ((grp G (H \<inter> K))/((H1 \<inter> K) \<bullet>\<^sub>G (H \<inter> K1))) \<cong> 
       ((grp G (H1 \<bullet>\<^sub>G (H \<inter> K)))/(H1 \<bullet>\<^sub>G (H \<inter> K1)))"
(* show H1 (H \<inter> K)/H1 (H \<inter> K1) = H1 (H \<inter> K1) (H \<inter> K) / H1 (H \<inter> K1) *)
apply (subst ZassenhausTr4_0 [of "G" "H" "H1" "K" "K1"], assumption+)
 (* At first apply isom4 in the group grp G (H1 \<bullet>\<^sub>G H \<inter> K) *)
   (* thm isom4 [of "grp G (H1 \<bullet>\<^sub>G H \<inter> K)" "H1 \<bullet>\<^sub>G H \<inter> K1" "H \<inter> K"] *)
apply (frule ZassenhausTr2_1 [of "G" "H" "H1" "K"], assumption+)
apply (frule subggrp [of "G" "H1 \<bullet>\<^sub>G H \<inter> K"], assumption+)
apply (frule ZassenhausTr3 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule inter_subgs [of "G" "H" "K"], assumption+)
apply (frule settOpTr7_1 [of "G" "H1" "H \<inter> K"], assumption+)
apply (frule isom4 [of "grp G (H1 \<bullet>\<^sub>G H \<inter> K)" "H1 \<bullet>\<^sub>G H \<inter> K1" "H \<inter> K"], 
                                                             assumption+)
apply (frule settOpTr7_1 [of "G" "H1" "H \<inter> K"], assumption+)
 apply (rule subg_in_subg, assumption+)
 apply (frule grp_inherited [of "G" "H \<inter> K" "H1 \<bullet>\<^sub>G H \<inter> K"], assumption+)
 apply simp
 apply (frule ZassenhausTr4_0 [THEN sym, of "G" "H" "H1" "K" "K1"], assumption+)
 apply simp
 apply (frule nmlSubgTr0 [of "grp G (H1 \<bullet>\<^sub>G H \<inter> K)" "H1 \<bullet>\<^sub>G H \<inter> K1"], 
                              assumption+)
 apply (frule subg_subset [of "grp G (H1 \<bullet>\<^sub>G H \<inter> K)" "H1 \<bullet>\<^sub>G H \<inter> K1"], 
                              assumption+)  
 apply (simp add:grp_carrier [of "G" "H1 \<bullet>\<^sub>G H \<inter> K"])
 apply (frule subg_of_subg [of "G" "H1 \<bullet>\<^sub>G H \<inter> K" "H1 \<bullet>\<^sub>G H \<inter> K1"], 
                                                        assumption+)
 apply (simp add: settOpinherited [of "G" "H1 \<bullet>\<^sub>G H \<inter> K" 
                                    "H1 \<bullet>\<^sub>G H \<inter> K1" "H \<inter> K"])
 apply (frule special_subg_G [of "grp G (H1 \<bullet>\<^sub>G H \<inter> K)"])
 apply (simp add:grp_carrier)
 apply (frule grp_inherited [of "G" "H1 \<bullet>\<^sub>G H \<inter> K" "H1 \<bullet>\<^sub>G H \<inter> K"], 
                                                         assumption+)
 apply simp apply simp
apply (subgoal_tac "(H \<inter> K \<inter> (H1 \<bullet>\<^sub>G H \<inter> K1)) =  H1 \<inter> K \<bullet>\<^sub>G H \<inter> K1")
 apply simp

apply (thin_tac "(grp G (H \<inter> K) / (H \<inter> K \<inter> (H1 \<bullet>\<^sub>G (H \<inter> K1)))) \<cong>
       (grp G (H1 \<bullet>\<^sub>G (H \<inter> K)) / (H1 \<bullet>\<^sub>G (H \<inter> K1)))") 
apply (thin_tac "grp (grp G (H1 \<bullet>\<^sub>G H \<inter> K)) (H \<inter> K) = grp G (H \<inter> K)")
apply (thin_tac "H1 \<bullet>\<^sub>G H \<inter> K1 \<bullet>\<^sub>G H \<inter> K = H1 \<bullet>\<^sub>G H \<inter> K")
apply (thin_tac "grp (grp G (H1 \<bullet>\<^sub>G H \<inter> K)) (H1 \<bullet>\<^sub>G H \<inter> K) 
                                         = grp G (H1 \<bullet>\<^sub>G H \<inter> K)")
apply (frule settOpTr6_1 [of "G" "H1" "H \<inter> K1" "H \<inter> K"], assumption+) 
 apply (simp add:inter_subgs del:Int_subset_iff)+
 apply (frule ZassenhausTr2_3 [of "G" "K" "K1"], assumption+)
 apply (rule subsetI) apply simp
 apply (simp add:subsetD)
 apply (simp add:Int_assoc [THEN sym, of "H1" "H" "K"])
 apply (frule ZassenhausTr2_3 [of "G" "H" "H1"], assumption+)
 apply (simp add:Int_absorb2 [of "H1" "H"])
apply (simp add:Int_commute [of "H1 \<bullet>\<^sub>G H \<inter> K1" "H \<inter> K"])
done

lemma ZassenhausTr5_1: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow>   ((grp G (K \<inter> H))/((K1 \<inter> H) \<bullet>\<^sub>G (K \<inter> H1))) \<cong> 
       ((grp G (K1 \<bullet>\<^sub>G (K \<inter> H)))/(K1 \<bullet>\<^sub>G (K \<inter> H1)))"
(* thm ZassenhausTr5 [of "G" "K" "K1" "H" "H1"] *)
apply (simp add:ZassenhausTr5 [of "G" "K" "K1" "H" "H1"]) 
done

lemma ZassenhausTr5_2: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow>  ((grp G (H \<inter> K))/((H1 \<inter> K) \<bullet>\<^sub>G (H \<inter> K1))) = 
                       ((grp G (K \<inter> H))/((K1 \<inter> H) \<bullet>\<^sub>G (K \<inter> H1)))"

apply (subgoal_tac "H1 \<inter> K \<bullet>\<^sub>G H \<inter> K1 = K1 \<inter> H \<bullet>\<^sub>G K \<inter> H1")
  prefer 2
(* thm ZassenhausTr3_3 *)
apply (simp add:ZassenhausTr3_3)
apply simp  
  apply (simp add:Int_commute)
done

lemma ZassenhausTr6_1:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> group  (grp G (H \<inter> K) / (H1 \<inter> K \<bullet>\<^sub>G H \<inter> K1))"
apply (frule inter_subgs [of "G" "H" "K"], assumption+)
apply (frule subggrp [of "G" "H \<inter> K"], assumption+)
 apply (frule ZassenhausTr3_5 [of "G" "H" "H1" "K" "K1"], assumption+)
 apply (rule Qgrp, assumption+)
done

lemma ZassenhausTr6_2:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> group (grp G (H1 \<bullet>\<^sub>G H \<inter> K) / (H1 \<bullet>\<^sub>G H \<inter> K1))"
apply (frule ZassenhausTr2_1 [of "G" "H" "H1" "K"], assumption+)
 apply (frule subggrp [of "G" "H1 \<bullet>\<^sub>G H \<inter> K"], assumption+)
 apply (frule ZassenhausTr3 [of "G" "H" "H1" "K" "K1"], assumption+)
 apply (simp add:Qgrp)
done

lemma ZassenhausTr6_3:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> group (grp G (K1 \<bullet>\<^sub>G K \<inter> H) / (K1 \<bullet>\<^sub>G K \<inter> H1))"
apply (frule ZassenhausTr2_1 [of "G" "K" "K1" "H"], assumption+)
 apply (frule subggrp [of "G" "K1 \<bullet>\<^sub>G K \<inter> H"], assumption+)
 apply (frule ZassenhausTr3 [of "G" "K" "K1" "H" "H1"], assumption+)
 apply (simp add:Qgrp)
done

theorem Zassenhaus: "\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G; H1 \<lhd> grp G H; 
K1 \<lhd> grp G K\<rbrakk>
\<Longrightarrow> ((grp G (H1 \<bullet>\<^sub>G (H \<inter> K)))/ (H1 \<bullet>\<^sub>G (H \<inter> K1))) \<cong> 
       ((grp G (K1 \<bullet>\<^sub>G (K \<inter> H)))/(K1 \<bullet>\<^sub>G (K \<inter> H1)))"
apply (frule ZassenhausTr5 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule ZassenhausTr6_1 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule ZassenhausTr6_2 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule ZassenhausTr6_3 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule isomTr1 [of "(grp G (H \<inter> K) / (H1 \<inter> K \<bullet>\<^sub>G H \<inter> K1))" "grp G (H1 \<bullet>\<^sub>G H \<inter> K) / (H1 \<bullet>\<^sub>G H \<inter> K1)"], assumption+) 
apply (thin_tac "(grp G (H \<inter> K) / (H1 \<inter> K \<bullet>\<^sub>G (H \<inter> K1))) \<cong>
       (grp G (H1 \<bullet>\<^sub>G (H \<inter> K)) / (H1 \<bullet>\<^sub>G (H \<inter> K1)))")
apply (rule isomTr2 [of "(grp G (H1 \<bullet>\<^sub>G H \<inter> K) / (H1 \<bullet>\<^sub>G H \<inter> K1))" "(grp G (H \<inter> K) / (H1 \<inter> K \<bullet>\<^sub>G H \<inter> K1))" "(grp G (K1 \<bullet>\<^sub>G K \<inter> H) / (K1 \<bullet>\<^sub>G K \<inter> H1))"], 
 assumption+)
apply (thin_tac "(grp G (H1 \<bullet>\<^sub>G (H \<inter> K)) / (H1 \<bullet>\<^sub>G (H \<inter> K1))) \<cong>
       (grp G (H \<inter> K) / (H1 \<inter> K \<bullet>\<^sub>G (H \<inter> K1)))")
apply (frule ZassenhausTr5 [of "G" "K" "K1" "H" "H1"], assumption+)
apply (frule ZassenhausTr3_3 [THEN sym, of "G" "H" "H1" "K" "K1"], assumption+)
apply simp
apply (simp add:Int_commute [of "K" "H"])
done

section "14. An automorphism groups"

constdefs
   automg :: "'a GroupType \<Rightarrow> 
      \<lparr> carrier :: ('a \<Rightarrow> 'a) set, tOp :: ['a \<Rightarrow> 'a,'a \<Rightarrow> 'a] \<Rightarrow> ('a \<Rightarrow> 'a),
     iOp :: ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a), one :: ('a \<Rightarrow> 'a)\<rparr>"
 
      "automg G  ==  \<lparr> carrier = {f. gbijec\<^sub>G\<^sub>,\<^sub>G f}, tOp = \<lambda>g\<in>{f. gbijec\<^sub>G\<^sub>,\<^sub>G f}. \<lambda>f\<in>{f. gbijec\<^sub>G\<^sub>,\<^sub>G f}. ( g \<circ>\<^sub>G f), iOp = \<lambda>f\<in>{f. gbijec\<^sub>G\<^sub>,\<^sub>G f}. (Ifn G G f), one = I\<^sub>G \<rparr>" 

lemma automgroupTr1:"\<lbrakk> group G; gbijec\<^sub>G\<^sub>,\<^sub>G f; gbijec\<^sub>G\<^sub>,\<^sub>G g; gbijec\<^sub>G\<^sub>,\<^sub>G h\<rbrakk> \<Longrightarrow>
    (h \<circ>\<^sub>G g) \<circ>\<^sub>G f =  h \<circ>\<^sub>G (g \<circ>\<^sub>G f)" 
apply (simp add:cmpghom_def)
apply (subgoal_tac "f \<in> carrier G \<rightarrow> carrier G")
apply (subgoal_tac "g \<in> carrier G \<rightarrow> carrier G")
apply (subgoal_tac "h \<in> carrier G \<rightarrow> carrier G")
apply (simp add:compose_assoc)
apply (simp add:gbijec_def ginjec_def gHom_def)+
done

lemma automgroup:"group G  \<Longrightarrow> group (automg G)"
apply (unfold group_def [of "automg G"])      
apply (rule conjI)  apply (simp add:automg_def)   
 apply (simp add:Pi_def) apply (rule allI) 
apply (rule impI) apply (rule allI) apply (rule impI)
 apply (simp add: gHomcompTr3)
apply (rule conjI)
 apply (simp add:automg_def)
 apply (simp add:Pi_def iOp_def)
 apply (rule allI) apply (rule impI)
  apply (simp add:invhom_gbijec)
apply (rule conjI)
 apply (simp add:automg_def)
 apply (simp add:IdTr2)
apply (rule ballI)+
apply (rule conjI)
 apply (simp add:automg_def)
 apply (rule conjI)
 apply (rule impI)
 apply (rule lunithom, assumption+)
 apply (simp add:gbijec_def ginjec_def)
 apply (subgoal_tac "gbijec\<^sub>G\<^sub>,\<^sub>G I\<^sub>G") apply simp
apply (simp add:IdTr2)
apply (rule conjI)
 apply (simp add:automg_def)
 apply (rule conjI) apply (rule impI)
 apply (rule linvhom, assumption+)
apply (rule impI)
 apply (subgoal_tac "gbijec\<^sub>G\<^sub>,\<^sub>G (Ifn G G x)")
 apply simp apply (thin_tac "\<not> gbijec\<^sub>G\<^sub>,\<^sub>G (Ifn G G x)")
apply (simp add: invhom_gbijec) 
apply (subgoal_tac "gbijec\<^sub>G\<^sub>,\<^sub>G (x \<circ>\<^sub>G y)")
apply (subgoal_tac "gbijec\<^sub>G\<^sub>,\<^sub>G (y \<circ>\<^sub>G z)")
apply (simp add:automg_def)
apply (simp add:automgroupTr1)
apply (simp add:automg_def)
apply (simp add:gHomcompTr3)
apply (simp add:automg_def)
apply (simp add:gHomcompTr3)
done

section "15. chain of groups I" 

constdefs
  d_gchain:: "[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
    "d_gchain G n g  == if n=0 then g 0 \<guillemotleft> G else (\<forall>l\<in>Nset n. (g l) \<guillemotleft> G) \<and> (\<forall>l\<in> Nset (n - Suc 0).  g (Suc l) \<subseteq> g l )" 
           (**  g 0 \<supseteq> \<dots> \<supseteq> g n  **)

 D_gchain:: "[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "D_gchain G n g== if n = 0 then g 0 \<guillemotleft> G else d_gchain G n g \<and> 
     (\<forall>i \<in> Nset (n - 1).  g (Suc i) \<subset> g i)"
           (**  g 0 \<supset> \<dots> \<supset> g n **) 

 td_gchain::"[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "td_gchain G n g == if n=0 then g 0 = carrier G \<and> g 0 = {one G} else d_gchain G n g \<and> g 0 = carrier G \<and> g n = {one G}"
           (**  g 0 \<supseteq> \<dots> \<supseteq> g n with g 0 = carrier G and g n = {e}  **)

 tD_gchain::"[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "tD_gchain G n g == if n=0 then g 0 = carrier G \<and> g 0 = {one G} else D_gchain G n g \<and> (g 0 = carrier G) \<and> (g n = {one G})" 
           (**  g 0 \<supset> \<dots> \<supset> g n with g 0 = carrier G and g n = {e}  **)

 w_cmpser::"[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "w_cmpser G n g == if n = 0 then d_gchain G n g else d_gchain G n g \<and>  
   (\<forall>i\<in>Nset (n - 1). g (Suc i) \<lhd> grp G (g i))" 
           (**  g 0 \<rhd> \<dots> \<rhd> g n ** with g i \<supseteq> g (Suc i) **) 


 W_cmpser::"[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "W_cmpser G n g == if n = 0 then d_gchain G n g else D_gchain G n g \<and> 
 (\<forall>i\<in>Nset (n - 1). g (Suc i) \<lhd> grp G (g i))" 
           (**  g 0 \<rhd> \<dots> \<rhd> g n  with g i \<supset> g (Suc i) **) 

 tw_cmpser::"[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "tw_cmpser G n g == if n = 0 then td_gchain G n g else td_gchain G n g \<and> 
 (\<forall>i\<in>Nset (n - 1). g (Suc i) \<lhd> grp G (g i))" 
           (**  g 0 \<rhd> \<dots> \<rhd> g n with g 0 = carrier G and g n = {e}  **) 

 tW_cmpser::"[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool"
 "tW_cmpser G n g == if n = 0 then td_gchain G n g else tD_gchain G n g \<and> 
 (\<forall>i\<in>Nset (n - 1). g (Suc i) \<lhd> grp G (g i))"
  (* g 0 \<rhd> \<dots> \<rhd> g n with g 0 = carrier G, g n = {e} and g (Suc i) \<subset> g i*) 

  Qw_cmpser::"[('a, 'more) GroupType_scheme, nat \<Rightarrow> 'a set] \<Rightarrow> 
                                (nat \<Rightarrow> ('a set) GroupType)" 
  "Qw_cmpser G f i == ((grp G (f i)) / (f (Suc i)))" 

 (* f 0 \<rhd> \<dots> \<rhd> f (n+1), Qw_cmpser G n f is (f 0)/(f 1),\<dots>,f n/f (n+1) *)

constdefs
 red_chn:: "[('a, 'more) GroupType_scheme, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> 
                                                      (nat \<Rightarrow> 'a set)"   
     "red_chn G n f == SOME g. g \<in> {h. tW_cmpser G (card (f ` (Nset n))
      - 1) h \<and> (h `(Nset (card (f`(Nset n)) - 1)) = f `(Nset n))}"
    (* for tw_cmpser G f n, red_chn G f n is tW_cmpser  *)    

    chain_cutout :: "[nat, (nat \<Rightarrow> 'a set) ]
                                \<Rightarrow> (nat \<Rightarrow> 'a set)"
     "chain_cutout i f  == \<lambda>j. f (slide i j)"

lemma d_gchainTr0:"\<lbrakk> group G; 0< n; d_gchain G n f; k \<in> Nset (n - 1) \<rbrakk>
                        \<Longrightarrow> f (Suc k) \<subseteq> f k"
apply (simp add:d_gchain_def)
done

lemma d_gchain_pre:"\<lbrakk>group G; d_gchain G (Suc n) f\<rbrakk> \<Longrightarrow> d_gchain G n f"
apply (simp add:d_gchain_def)
 apply (case_tac "n = 0") apply (rotate_tac -1) 
 apply (erule conjE) apply (simp add:Nset_def) 
apply (erule conjE) apply simp
 apply (subgoal_tac "\<forall>l. l\<in>Nset n \<longrightarrow> l\<in> Nset (Suc n)")
 apply simp
 apply (subgoal_tac "\<forall>l. l\<in>Nset (n - 1) \<longrightarrow> l \<in> Nset (Suc n - Suc 0)")
 apply simp
apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def)
 apply (subgoal_tac "n - Suc 0 < n")
 apply (frule_tac i = l in le_less_trans [of _ "n - Suc 0" "n"], assumption+)
 apply (simp add:less_imp_le)
 apply simp
 apply (simp add:Nset_def)
done

lemma d_gchainTr1:"group G \<Longrightarrow> 0 < n \<longrightarrow> (\<forall>f. d_gchain G n f \<longrightarrow> (\<forall>i\<in>Nset n. \<forall>j\<in>Nset n. i < j \<longrightarrow> f j \<subseteq> f i))"
apply (induct_tac n)
 apply (rule impI) apply simp 
(** n **)
apply (rule impI)
apply (rule allI) apply (rule impI)
apply (rule ballI)+ apply (rule impI)
(** case n = 0 **)
apply (case_tac "n = 0") apply simp
 apply (simp add:Nset_def)
 apply (case_tac "j = 0") apply simp
 apply (frule le_imp_less_or_eq) apply (thin_tac "j \<le> Suc 0") 
 apply simp 
 apply (simp add:d_gchain_def) apply (erule conjE)
 apply (simp add:Nset_def)
  apply (rule contrapos_pp) apply simp+
(** case 0 < n **) 
 (** case j = n **)
apply (case_tac "j = Suc n")
 apply simp
 apply (frule_tac m = i and n = "Suc n" in Suc_leI)
 apply simp
  apply (case_tac "i = n") apply (thin_tac "i \<le> n")
  apply (thin_tac "\<forall>f. d_gchain G n f \<longrightarrow> (\<forall>i\<in>Nset n. \<forall>j\<in>Nset n. i < j \<longrightarrow> f j \<subseteq> f i)")
  apply (simp add:d_gchain_def) apply (erule conjE)
  apply (simp add:Nset_def)
apply (frule le_imp_less_or_eq) apply simp
 apply (frule_tac i = i and j = n and k = "Suc n" in le_less_trans)
 apply simp
 apply (frule_tac x = i and n = n in mem_of_Nset)
 apply (frule_tac m = i and n = n in noteq_le_less, assumption+)
 apply (frule_tac n = "Suc n" and f = f and k = n in d_gchainTr0 [of "G"])
 apply simp apply assumption apply (simp add:Nset_def)
 apply (subgoal_tac "n \<le> n")
 apply (subgoal_tac "f (Suc n) \<subseteq> f i") apply simp
 apply (frule_tac x = n and n = n in mem_of_Nset) 
 apply (thin_tac "n \<le> n")
 apply (frule_tac n = n and f = f in d_gchain_pre [of "G"], assumption+)
 apply (thin_tac "d_gchain G (Suc n) f")
 apply blast apply simp

apply (frule Nset_pre, assumption+)
 apply (thin_tac "j \<noteq> Suc n") apply (thin_tac "j \<in> Nset (Suc n)")
 apply (frule_tac n = n and f = f in d_gchain_pre [of "G"], assumption+)
 apply (thin_tac "d_gchain G (Suc n) f")
apply (subgoal_tac "f j \<subseteq> f i")  apply simp
 apply (thin_tac "\<not> f j \<subseteq> f i")
 apply (subgoal_tac "i \<in> Nset n") 
 apply blast
 apply (thin_tac " \<forall>f. d_gchain G n f \<longrightarrow> (\<forall>i\<in>Nset n. \<forall>j\<in>Nset n. i < j \<longrightarrow> f j \<subseteq> f i)")
 apply (simp add:Nset_def)
done

lemma d_gchainTr2:"\<lbrakk>group G; 0 < n; d_gchain G n f; i\<in>Nset n; j \<in> Nset n; 
 i \<le> j \<rbrakk> \<Longrightarrow> f j \<subseteq> f i"
apply (case_tac "i = j")
 apply simp
apply (frule le_imp_less_or_eq) apply simp
apply (simp add:d_gchainTr1)
done

lemma im_d_gchainTr1:"\<lbrakk>group G; d_gchain G n f; f i \<in> (f ` (Nset n)) - {f 0}\<rbrakk>
  \<Longrightarrow> f (LEAST j. f j \<in> (f ` (Nset n)) - {f 0}) \<in> (f ` (Nset n) - {f 0})"
apply (rule LeastI)
apply simp
done

lemma im_d_gchainTr1_0:"\<lbrakk>group G; d_gchain G n f; f i \<in> (f ` (Nset n)) - {f 0}\<rbrakk>
  \<Longrightarrow> 0 < (LEAST j. f j \<in> (f ` (Nset n)) - {f 0})"
apply (frule im_d_gchainTr1 [of "G" "n" "f"], assumption+)
apply (rule contrapos_pp) apply simp
apply simp
done 

lemma im_d_gchainTr1_1:"\<lbrakk>group G; d_gchain G n f; \<exists> i. f i \<in> (f ` (Nset n)) - {f 0}\<rbrakk>  \<Longrightarrow> f (LEAST j. f j \<in> ((f ` (Nset n)) - {f 0})) \<in> ((f`(Nset n)) - {f 0})"
apply (subgoal_tac "\<forall>i. f i \<in> f ` Nset n - {f 0} \<longrightarrow>  f (LEAST j. f j \<in> f ` Nset n - {f 0}) \<in> f ` Nset n - {f 0}")
apply blast
 apply (thin_tac "\<exists>i. f i \<in> f ` Nset n - {f 0}")
 apply (rule allI) apply (rule impI)
apply (rule im_d_gchainTr1 [of "G" "n" "f" _], assumption+)
done

lemma im_d_gchainsTr1_2:"\<lbrakk>group G; d_gchain G n f; i \<in> Nset n; f i \<in> f `(Nset n) - {f 0}\<rbrakk>  \<Longrightarrow> (LEAST j. f j \<in> (f `(Nset n) - {f 0})) \<le> i"
apply (rule Least_le)
apply (subgoal_tac "f i \<in> f ` Nset i")
 apply simp
 apply (simp add:image_def)
 apply (subgoal_tac "i \<in> Nset i") apply blast
 apply (simp add:Nset_def)
done

lemma im_d_gchainsTr1_3:"\<lbrakk>group G; d_gchain G n f;
 \<exists>i\<in>(Nset n). f i \<in> f`(Nset n) - {f 0}; k < (LEAST j. f j \<in> (f`(Nset n) - {f 0}))\<rbrakk> \<Longrightarrow> f k = f 0"
apply (auto del:equalityI) 
apply (frule_tac i = i in im_d_gchainsTr1_2 [of "G" "n" "f" _ ], assumption+)
apply (simp add:image_def)
apply (auto del:equalityI)
apply (rule contrapos_pp) apply simp+
 apply (subgoal_tac "k \<in> Nset n")
 apply (subgoal_tac "f k \<in> f ` Nset n - {f 0}")
 apply (frule im_d_gchainsTr1_2 [of "G" "n" "f" "k"], assumption+)
apply simp
 apply (simp add:image_def)
  apply (auto del:equalityI)
apply (simp add:Nset_def)
done

lemma im_gdchainsTr1_4:"\<lbrakk>group G; d_gchain G n f; \<exists>v\<in>f `(Nset n). v \<notin> {f 0}; 
i < (LEAST j. f j \<in> (f `(Nset n)) \<and> f j \<noteq> f 0) \<rbrakk> \<Longrightarrow> f i = f 0"
apply (frule im_d_gchainsTr1_3 [of "G" "n" "f" "i"], assumption+) 
 apply simp
 apply simp
apply (rule im_d_gchainsTr1_3, assumption+)
 apply simp
 apply simp
done

lemma im_d_gchainsTr1_5:"\<lbrakk>group G; 0 < n; d_gchain G n f; i \<in> Nset n; f i \<in> (f ` (Nset n) - {f 0}); (LEAST j. f j \<in> (f `(Nset n) - {f 0})) = j \<rbrakk> \<Longrightarrow> 
     f `(Nset (j - (Suc 0))) = {f 0}"
apply (frule im_d_gchainTr1_0 [of "G" "n" "f" "i"], assumption+)
apply (subst image_def)
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI)
apply (auto del:equalityI)
apply (subgoal_tac "xa < (LEAST j. f j \<in> f ` Nset n \<and> f j \<noteq> f 0)")
apply (rule  im_d_gchainsTr1_3, assumption+)
 apply blast
 apply simp
 apply (simp add:Nset_def)
 apply (rule le_less_trans, assumption+) apply simp
apply (subgoal_tac "0 \<in> Nset ((LEAST j. f j \<in> f ` Nset n \<and> f j \<noteq> f 0) - Suc 0)")
apply (auto del:equalityI)
apply (simp add:Nset_def)
done

lemma im_d_gchains1:"\<lbrakk>group G; 0 < n; d_gchain G n f; i \<in> Nset n; f i \<in> (f ` (Nset n) - {f 0}); (LEAST j. f j \<in> (f `(Nset n) - {f 0})) = j \<rbrakk> \<Longrightarrow> f `(Nset n) = {f 0} \<union> {f i |i. j \<le> i \<and> i \<le> n}"
apply (frule im_d_gchainTr1_0 [of "G" "n" "f" "i"], assumption+)
apply (frule im_d_gchainsTr1_2 [of "G" "n" "f" "i"], assumption+)
apply (frule Nset_nset_1 [of "n" "j - Suc 0"])
 apply simp 
 apply (simp add:Nset_def)
 apply (frule le_trans [of "j" "i" "n"], assumption+)
 apply (frule less_pre_n [of "j"])
 apply (rule less_le_trans, assumption+)
apply (subgoal_tac "\<forall>l\<in>Nset n. f l \<in> {H. H \<guillemotleft> G}")
prefer 2
 apply (thin_tac "Nset n = Nset (j - Suc 0) \<union> nset (Suc (j - Suc 0)) n")
 apply (simp add:d_gchain_def)
 apply (frule_tac im_set_un1 [of "Nset n" "f" _ "Nset (j - Suc 0)" 
                        "nset (Suc (j - Suc 0)) n"], assumption+)
 apply (thin_tac "\<forall>l\<in>Nset n. f l \<in> {H. H \<guillemotleft> G}")
apply (subgoal_tac "f ` Nset (j - Suc 0) = {f 0}")
apply (subgoal_tac "f ` nset (Suc (j - Suc 0)) n = {f i |i. j \<le> i \<and> i \<le> n}")
apply simp
 apply (thin_tac "Nset n = Nset (j - Suc 0) \<union> nset (Suc (j - Suc 0)) n")
 apply (thin_tac "f ` (Nset (j - Suc 0) \<union> nset (Suc (j - Suc 0)) n) =
       f ` Nset (j - Suc 0) \<union> f ` nset (Suc (j - Suc 0)) n")
 apply (thin_tac "f ` Nset (j - Suc 0) = {f 0}")
 apply (simp add:nset_def image_def) apply blast
 apply (frule sym) 
  apply (thin_tac "(LEAST j. f j \<in> f ` Nset n - {f 0}) = j")
  apply (thin_tac "Nset n = Nset (j - Suc 0) \<union> nset (Suc (j - Suc 0)) n")
  apply (thin_tac "f ` (Nset (j - Suc 0) \<union> nset (Suc (j - Suc 0)) n) =
       f ` Nset (j - Suc 0) \<union> f ` nset (Suc (j - Suc 0)) n")
 apply simp
apply (simp add:im_d_gchainsTr1_5)
done

lemma im_d_gchains1_1:"\<lbrakk>group G; d_gchain G n f; f n \<noteq> f 0\<rbrakk>  \<Longrightarrow> f `(Nset n) = {f 0} \<union> {f i |i. (LEAST j. f j \<in> (f `(Nset n) - {f 0})) \<le> i \<and> i \<le> n}"
apply (case_tac "n = 0") apply simp
apply simp 
apply (subgoal_tac "f n \<in> f ` Nset n - {f 0}")
apply (frule im_d_gchains1 [of "G" "n" "f" "n" "(LEAST j. f j \<in> f ` Nset n - {f 0})"], assumption+) 
 apply (simp add:Nset_def)
 apply simp+
 apply (simp add:image_def Nset_def)
 apply auto
done

lemma d_gchains_leastTr:"\<lbrakk>group G; d_gchain G n f; f n \<noteq> f 0\<rbrakk>  \<Longrightarrow>  (LEAST j. f j \<in> (f `(Nset n) - {f 0})) \<in> Nset n \<and> f  (LEAST j. f j \<in> (f `(Nset n) - {f 0})) \<noteq> f 0"
apply (frule im_d_gchainsTr1_2 [of "G" "n" "f" "n"], assumption+)
 apply (simp add:Nset_def)
 apply simp 
 apply (simp add:image_def Nset_def)
 apply blast
apply (subgoal_tac "f n \<in> f ` Nset n - {f 0}")
apply (frule im_d_gchainTr1, assumption+)
  apply (simp add:Nset_def) apply (simp add:image_def)
 apply (thin_tac "(LEAST j. (\<exists>x\<in>Nset n. f j = f x) \<and> f j \<noteq> f 0) \<le> n")
 apply (simp add:Nset_def)
 apply (auto del:equalityI)
done 

lemma im_d_gchainTr2:"\<lbrakk> group G; d_gchain G n f; j \<in> Nset n; f j \<noteq> f 0\<rbrakk> \<Longrightarrow>
                                 \<forall>i\<in>Nset n. f 0 = f i \<longrightarrow> \<not> j \<le> i"
apply (rule ballI) apply (rule impI)
apply (rule contrapos_pp) apply simp+
apply (case_tac "j = i") apply simp
apply (frule_tac j = i in d_gchainTr2 [of "G" "n" "f" "j" ])
apply (simp add:Nset_def)
apply assumption+
apply (frule d_gchainTr2 [of "G" "n" "f" "0" "j"])
 apply (simp add:Nset_def)+  
done

lemma D_gchain_pre:"\<lbrakk>group G; D_gchain G (Suc n) f\<rbrakk> \<Longrightarrow> D_gchain G n f"
apply (simp add:D_gchain_def) apply (erule conjE)
apply (case_tac "n = 0") apply (rotate_tac -1)
 apply simp apply (insert lessI [of "0::nat"])
 apply (simp add:Nset_def)
 apply (simp add:d_gchain_def) apply (simp add:Nset_def)
apply (simp add:Nset_def)
 apply (frule d_gchain_pre [of "G" "n"], assumption+)
 apply simp 
apply (rule allI) apply (rule impI)
 apply (frule less_pre_n [of "n"])
 apply (frule_tac i = i in le_less_trans [of _ "n - (Suc 0)" "n"], assumption+)
 apply (simp add:less_imp_le)
done

lemma D_gchain0:"\<lbrakk>group G; D_gchain G n f; i \<in> Nset n; j \<in> Nset n; i < j\<rbrakk> \<Longrightarrow> f j \<subset> f i"
apply (case_tac "n = 0") 
 apply (simp add:Nset_def) apply simp
 apply (simp add:D_gchain_def) apply (erule conjE)
 apply (frule d_gchainTr2 [of "G" "n" "f" "i" "j"], assumption+)
 apply (simp add:less_imp_le)
 apply (frule Suc_leI [of "i" "j"])
apply (case_tac "j = Suc i")
 apply (thin_tac "i \<in> Nset n")
 apply (frule_tac i = i and j = j and k = n in less_le_trans)
 apply (simp add:Nset_def)
 apply simp 
 apply (simp add:Nset_def)
 apply (frule less_le_diff [of "i" "n"])
 apply blast
apply (frule_tac i = i and j = j and k = n in less_le_trans)
 apply (thin_tac "\<forall>i\<in>Nset (n - Suc 0). f (Suc i) \<subset> f i")
 apply (simp add:Nset_def)
 apply (frule less_le_diff [of "i" "n"])
apply (simp add:Nset_def) 
 apply (subgoal_tac "f (Suc i) \<subset> f i")
 apply (thin_tac "\<forall>i. i \<le> n - Suc 0 \<longrightarrow> f (Suc i) \<subset> f i") 
 apply (frule d_gchainTr2 [of "G" "n" "f" "Suc i" "j"])
 apply (frule_tac le_trans [of "Suc i" "j" "n"], assumption+) 
 apply simp apply assumption
 apply (frule le_trans [of "Suc i" "j" "n"], assumption+)  
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply assumption
apply (rule subset_psubset_trans [of "f j" "f (Suc i)" "f i"], assumption+)
 apply blast
done

lemma D_gchain1:"\<lbrakk>group G; D_gchain G n f\<rbrakk> \<Longrightarrow> inj_on f (Nset n)"
apply (case_tac "n = 0")
 apply (simp add:inj_on_def Nset_def)
apply simp (** case 0 < n **)
apply (simp add:inj_on_def)
 apply (rule ballI)+
 apply (rule impI)
 apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "x < y \<or> x = y \<or> y < x")
 prefer 2 apply (rule less_linear) apply simp
 apply (thin_tac "x \<noteq> y")
 apply (case_tac "x < y")
 apply (frule_tac i = x and j = y in D_gchain0 [of "G" "n" "f"], assumption+)
 apply simp
apply simp
 apply (frule_tac i = y and j = x in D_gchain0 [of "G" "n" "f"], assumption+)
 apply simp
done

lemma card_im_D_gchain:"\<lbrakk> 0 < n; group G; D_gchain G n f\<rbrakk> 
                                   \<Longrightarrow> card (f `(Nset n)) = Suc n"
apply (insert finite_Nset [of "n"])
apply (frule D_gchain1 [of "G" "n"], assumption+)
apply (subst card_image, assumption+)
apply (simp add:card_Nset)
done

lemma w_cmpser_gr:"\<lbrakk>group G; 0 < r; w_cmpser G r f; i \<in> Nset r\<rbrakk> \<Longrightarrow>
                                                              f i \<guillemotleft> G"
apply (simp add:w_cmpser_def) apply (erule conjE)
apply (simp add:d_gchain_def)
done

lemma w_cmpser_ns:"\<lbrakk>group G; 0 < r; w_cmpser G r f; i \<in> Nset (r - 1)\<rbrakk> \<Longrightarrow>
             f (Suc i) \<lhd> grp G (f i)"
apply (simp add:w_cmpser_def)
done

lemma w_cmpser_pre:"\<lbrakk>group G; w_cmpser G (Suc n) f\<rbrakk> \<Longrightarrow> w_cmpser G n f"
apply (simp add:w_cmpser_def)
 apply (erule conjE)
 apply (case_tac "n = 0") apply (rotate_tac -1) apply simp
 apply (rule d_gchain_pre [of "G" "0" "f"], assumption+)
apply simp
 apply (frule d_gchain_pre [of "G" "n" "f"], assumption+)
 apply simp
apply (subgoal_tac "\<forall>l. l \<in> Nset (n - Suc 0) \<longrightarrow> l \<in> Nset n")
 apply simp
apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
 apply (frule_tac i = l in le_less_trans [of _ "n - Suc 0" "n"])
 apply simp
 apply (simp add:less_imp_le)
done

lemma W_cmpser_pre:"\<lbrakk>group G; W_cmpser G (Suc n) f\<rbrakk> \<Longrightarrow> W_cmpser G n f"
apply (simp add:W_cmpser_def)
 apply (erule conjE)
 apply (case_tac "n = 0") apply simp
 apply (simp add:D_gchain_def) apply (erule conjE)
 apply (rule d_gchain_pre, assumption+) apply simp
apply (frule D_gchain_pre, assumption+) apply simp
 apply (subgoal_tac "\<forall>l. l\<in>Nset (n - 1) \<longrightarrow> l \<in> Nset n")
 apply simp
apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
 apply (frule_tac i = l in le_less_trans [of _ "n - Suc 0" "n"])
 apply simp
 apply (simp add:less_imp_le)
done

lemma td_gchain_n:"\<lbrakk>group G; td_gchain G n f; carrier G \<noteq> {one G}\<rbrakk> \<Longrightarrow>
              0 < n"
apply (simp add:td_gchain_def)
apply (rule contrapos_pp) apply simp+
apply (erule conjE) apply simp
done

section "16. Existence of reduced chain" 

lemma jointgd_tool1:" 0 < i \<Longrightarrow> 0 \<le> i - Suc 0"
apply (frule Suc_leI [of "0" "i"])
 apply simp
done

lemma jointgd_tool2:" 0 < i \<Longrightarrow> i = Suc (i - Suc 0)"
apply (simp add:Suc_pred [THEN sym])
done

lemma jointgd_tool3:"\<lbrakk>0 < i;  i \<in> Nset m \<rbrakk> \<Longrightarrow> i - Suc 0 \<in> Nset (m - Suc 0)"
apply (simp add:Nset_def)
  apply (rule  diff_le_mono [of _ "m" "Suc 0"], assumption+)
done

lemma jointgd_tool4:"n < i \<Longrightarrow> i - n = Suc( i - Suc n)"
apply (frule less_diff_pos [of "n" "i"])
apply (subst less_diff_Suc [of "n" "i"], assumption+)
apply (rule Suc_pred [THEN sym, of "i - n"], assumption+)
done

lemma D_gchain_is_d_gchain:"\<lbrakk>group G; D_gchain G n f\<rbrakk> \<Longrightarrow> d_gchain G n f"
apply (simp add:D_gchain_def)
 apply (case_tac "n = 0") apply (rotate_tac -1) 
 apply (simp add:d_gchain_def) apply (rotate_tac -1)
 apply simp
done

lemma joint_d_gchains:"\<lbrakk> group G; d_gchain G n f; d_gchain G m g; 
  g 0 \<subseteq> f n \<rbrakk> \<Longrightarrow>  d_gchain G (Suc (n + m)) (jointfun n f m g)" 
apply (case_tac "n = 0")
 apply (case_tac "m = 0")
 apply (simp add:d_gchain_def [of "G" "Suc (n + m)" _])
 apply (simp add:jointfun_def sliden_def d_gchain_def) 
apply (rule conjI)
 apply (rule ballI) apply (rule impI) apply (simp add:Nset_def)
 apply (rule ballI) apply (rule impI)
 apply (simp add:Nset_def)
apply simp
 apply (simp add:d_gchain_def [of "G" _ "jointfun 0 f m g"])
 apply (rule conjI)
 apply (rule ballI)
 apply (simp add:jointfun_def d_gchain_def)
 apply (rule impI) apply (erule conjE)+
 apply (simp add:sliden_def) 
apply (subgoal_tac "l - Suc 0 \<in> Nset m") apply (rotate_tac -1)
 apply simp
 apply (simp add:Nset_def)
 apply (thin_tac "0 < m")
 apply (frule_tac m = 0 and n = l in Suc_leI)
 apply (frule diff_le_mono [of _ "Suc m" "Suc 0"]) apply simp+
apply (rule ballI)
 apply (simp add:jointfun_def)
 apply (case_tac "l = 0") 
 apply simp apply (simp add:sliden_def psubset_imp_subset)
 apply simp apply (rotate_tac -3)
 apply (simp add:d_gchain_def [of _ _ "g"])
 apply (erule conjE)
 apply (simp add:sliden_def)
 apply (simp add:Nset_def) 
apply (frule_tac  m = l and n = m and l = "Suc 0" in diff_le_mono)
 apply (frule_tac t = l in  Suc_pred [THEN sym])
 apply (thin_tac "\<forall>l. l \<le> m \<longrightarrow> g l \<guillemotleft> G")
 apply (subgoal_tac "g (Suc (l - (Suc 0))) \<subseteq> g (l - (Suc 0))") 
 apply simp
apply blast
apply simp

apply (simp add:d_gchain_def [of "G" "Suc (n + m)" _])
apply (rule conjI)
 apply (rule ballI)
 apply (case_tac "m = 0") apply simp
 apply (simp add:jointfun_def)
 apply (simp add:Nset_def)
  apply (case_tac "l \<le> n") apply simp
  apply (simp add:d_gchain_def [of _ "n" _]) 
  apply (simp add:Nset_def)
  apply simp 
  apply (rotate_tac -1) 
apply (subgoal_tac "l = Suc n") apply (simp add:sliden_def)
 apply (simp add:d_gchain_def [of _ "0" _])
 apply (auto del:subsetI)
 
apply (case_tac "l \<le> n")
 apply (simp add:d_gchain_def [of _ "n" _] jointfun_def Nset_def)
 apply (simp add:le_def)
 apply (frule_tac m = n and n = l in Suc_leI)
 apply (simp add:jointfun_def Nset_def)
 apply (frule_tac m = l and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
 apply (simp add:sliden_def)
 apply (simp add:d_gchain_def [of _ "m" _] Nset_def)

(** jointfun n f m g (Suc l) \<subseteq> jointfun n f m g l **) 
apply (simp add:jointfun_def)
 apply (simp add:Nset_def)
 apply (case_tac "l \<le> (n - Suc 0)")
 apply (subgoal_tac "Suc l \<le> n")
 apply (simp add:jointfun_def) apply (rotate_tac 4)
 apply (simp add:d_gchain_def [of _ "n"]) 
  apply (simp add:Nset_def) 
  apply (subgoal_tac "Suc l \<le> Suc (n - Suc 0)") apply simp
  apply (simp del:Suc_pred)
 apply (simp add:le_def [of _ "n - Suc 0"])
 apply (frule_tac m = "n - Suc 0" and n = l in Suc_leI)
 apply simp
apply (rule conjI)
 apply (rule impI)
 apply (simp add:sliden_def)
apply (rule impI)
 apply (frule_tac m = l and n = "n + m" and l = "Suc n" in diff_le_mono)
 apply (simp add:sliden_def d_gchain_def [of _ "m" _] Nset_def)
 apply (subgoal_tac "g (Suc (l - Suc n)) \<subseteq> g (l - Suc n)")
 apply (simp add:jointgd_tool4)
 apply blast
done

lemma joint_D_gchains:"\<lbrakk> group G; D_gchain G n f; D_gchain G m g; 
  g 0 \<subset> f n \<rbrakk> \<Longrightarrow>  D_gchain G (Suc (n + m)) (jointfun n f m g)" 
apply (simp add:D_gchain_def [of "G" "Suc (n + m)" _])
apply (subgoal_tac "d_gchain G n f")
apply (subgoal_tac "d_gchain G m g")
apply (frule joint_d_gchains [of "G" "n" "f" "m" "g"], assumption+)
 apply (simp add:psubset_imp_subset) apply simp
prefer 2
 apply (simp add:D_gchain_def [of _ "m" _])
 apply (case_tac "m = 0") apply (rotate_tac -1) apply (simp add:d_gchain_def)
 apply (rotate_tac -1) apply simp
prefer 2
 apply (simp add:D_gchain_def [of _ "n" _])
 apply (case_tac "n = 0") apply (rotate_tac -1) apply (simp add:d_gchain_def)
 apply (rotate_tac -1) apply simp

apply (rule ballI)
 apply (case_tac "n = 0") apply simp
 apply (simp add:jointfun_def)
  apply (case_tac "i = 0") 
  apply simp
  apply (simp add:sliden_def)
 apply simp
  apply (thin_tac "d_gchain G (Suc m)
            (\<lambda>i. if i = 0 then f i else g (sliden (Suc 0) i))")
  apply (simp add:Nset_def)
  apply (frule_tac j = i in less_le_trans [of "0" _ "m"], assumption+)
apply (rotate_tac -1)
  apply (simp add:D_gchain_def [of _ _ "g"] sliden_def Nset_def) 
  apply (frule_tac m = i in diff_le_mono [of _ "m" "Suc 0"])
  apply (subgoal_tac "g (Suc (i - Suc 0)) \<subset> g (i - Suc 0)")
  apply simp apply (rotate_tac -1) apply (simp del:Suc_pred)
apply simp
 apply (case_tac "i \<le> n - (Suc 0)")
 apply (frule_tac x = i in mem_of_Nset [of _ "n - (Suc 0)"])
 apply (simp add:Suc_le_mono [THEN sym, of _ "n - Suc 0"])
 apply (thin_tac "d_gchain G (Suc (n + m)) (jointfun n f m g)")
 apply (simp add:jointfun_def)
 apply (simp add:D_gchain_def [of "G" "n" _])
apply (simp add:le_def [of _ "n - Suc 0"]) 
 apply (frule_tac n = i in Suc_leI [of "n - Suc 0"]) apply simp
 apply (case_tac "i = n")
  apply simp
  apply (simp add:jointfun_def sliden_def)
apply (frule not_sym) apply (thin_tac "i \<noteq> n")
 apply (frule_tac m = n and n = i in noteq_le_less, assumption+) 
 apply (frule_tac m = n and n = i in Suc_leI)
 apply (case_tac "m = 0")
 apply (simp add:D_gchain_def [of _ "m"])
 apply (simp add:Nset_def)
 apply simp
 apply (simp add:D_gchain_def [of _ "m" ]) 
 apply (simp add:Nset_def)
 apply (frule_tac m = i and n = "n + m" and l = "Suc n" in diff_le_mono)
 apply (simp add:jointfun_def Nset_def sliden_def)
 apply (thin_tac "d_gchain G (Suc (n + m))
            (\<lambda>i. if i \<le> n then f i else g (sliden (Suc n) i))")
 apply (subgoal_tac "g (Suc (i - Suc n)) \<subset> g (i - Suc n)")
 apply (subgoal_tac "n < Suc n")
 apply (frule_tac k = i in less_le_trans [of "n" "Suc n" _], assumption+)
 apply (simp add:jointgd_tool4) apply simp
apply blast
done
 
lemma w_cmpser_is_d_gchain:"\<lbrakk>group G; w_cmpser G n f\<rbrakk> \<Longrightarrow> d_gchain G n f"
apply (simp add:w_cmpser_def)
 apply (case_tac "n=0") apply (rotate_tac -1) apply simp
 apply (rotate_tac -1) apply simp
done

lemma joint_w_cmpser:"\<lbrakk>group G; w_cmpser G n f; w_cmpser G m g; g 0 \<lhd> grp G (f n)\<rbrakk> \<Longrightarrow> w_cmpser G (Suc (n + m)) (jointfun n f m g)"
apply (simp add:w_cmpser_def [of _ "Suc (n + m)" _])
apply (rule conjI)
 apply (frule w_cmpser_is_d_gchain, assumption+)
 apply (thin_tac "w_cmpser G n f")
 apply (frule w_cmpser_is_d_gchain, assumption+)
 apply (thin_tac "w_cmpser G m g")
 apply (rule joint_d_gchains, assumption+)
apply (simp add:d_gchain_def [of _ "n" ])
 apply (case_tac "n = 0") apply simp
 apply (frule subggrp [of "G" "f 0"], assumption+)
 apply (frule nml_subg_subset, assumption+)
 apply (simp add:grp_carrier) apply simp
 apply (subgoal_tac "f n \<guillemotleft> G")
 apply (frule subggrp [of "G" "f n"], assumption+)
 apply (frule nml_subg_subset, assumption+)
 apply (simp add:grp_carrier) apply (simp add:Nset_def)
apply (rule ballI)
 apply (case_tac "n = 0") apply simp
 apply (simp add:jointfun_def)
  apply (case_tac "i = 0")
  apply simp apply (simp add:sliden_def)
 apply simp
 apply (simp add:w_cmpser_def [of _ "m" "g"])
 apply (case_tac "m = 0") apply (simp add:sliden_def)
 apply (simp add:Nset_def)
apply simp apply (erule conjE)
 apply (simp add:Nset_def sliden_def)
 apply (frule_tac i = 0 and j = i and k = m in less_le_trans, assumption+) 
 apply (subgoal_tac "g (Suc (i - Suc 0)) \<lhd> grp G (g (i - Suc 0))")
 apply (thin_tac "\<forall>i. i \<le> m - Suc 0 \<longrightarrow> g (Suc i) \<lhd> grp G (g i)")
 apply simp 
 apply (frule_tac m = i and n = m and l = "Suc 0" in diff_le_mono)
 apply (simp del:Suc_pred)
apply simp
 apply (case_tac "i \<le> n - Suc 0") 
 apply (frule less_pre_n [of "n"])
 apply (frule_tac i = i in le_less_trans[of _ "n - Suc 0" "n"], assumption+) 
 apply (simp add:Nset_def jointfun_def w_cmpser_def [of _ "n"])
apply (simp add:le_def [of _ "n - Suc 0"])
 apply (frule_tac n = i in Suc_leI [of "n - Suc 0" _])
 apply simp
 apply (case_tac "n = i")
 apply (frule sym) apply (thin_tac "n = i")
 apply simp
 apply (simp add:jointfun_def Nset_def sliden_def)
 apply (frule_tac m = n and n = i in noteq_le_less, assumption+)
 apply (frule_tac m = n and n = i in Suc_leI)
 apply (simp add:Nset_def jointfun_def)
 apply (frule_tac m = i and n = "n + m" and l = "Suc n" in diff_le_mono)
 apply simp
 apply (simp add:sliden_def w_cmpser_def [of _ "m" _])
 apply (erule conjE)
 apply (subgoal_tac "g (Suc (i - Suc n)) \<lhd>  grp G (g (i - Suc n))")
 apply (simp add:jointgd_tool4)
 apply (simp add:Nset_def)
done

lemma W_cmpser_is_D_gchain:"\<lbrakk>group G; W_cmpser G n f\<rbrakk> \<Longrightarrow> D_gchain G n f"
apply (simp add:W_cmpser_def)
 apply (case_tac "n = 0") apply (rotate_tac -1) apply simp
 apply (simp add:D_gchain_def d_gchain_def)
 apply (rotate_tac -1) apply simp
done

lemma W_cmpser_is_w_cmpser:"\<lbrakk>group G; W_cmpser G n f\<rbrakk> \<Longrightarrow> w_cmpser G n f"
apply (simp add:W_cmpser_def)
apply (case_tac "n = 0") apply (rotate_tac -1)
 apply simp
 apply (simp add:w_cmpser_def)
 apply (rotate_tac -1)
apply simp apply (erule conjE)
 apply (frule D_gchain_is_d_gchain, assumption+)
 apply (simp add:w_cmpser_def)
done

lemma tw_cmpser_is_w_cmpser:"\<lbrakk>group G; tw_cmpser G n f\<rbrakk> \<Longrightarrow> w_cmpser G n f"
apply (simp add:tw_cmpser_def)
 apply (case_tac "n = 0")
 apply (rotate_tac -1) apply simp
 apply (simp add:td_gchain_def w_cmpser_def) 
 apply (simp add:d_gchain_def) apply (simp add:special_subg_G)
apply (rotate_tac -1) apply simp
 apply (erule conjE) apply (simp add:td_gchain_def)
 apply (erule conjE)+
apply (simp add:w_cmpser_def)
done

lemma tW_cmpser_is_W_cmpser:"\<lbrakk>group G; tW_cmpser G n f\<rbrakk> \<Longrightarrow> W_cmpser G n f"
apply (simp add:tW_cmpser_def)
apply (case_tac "n = 0") apply (rotate_tac -1)
 apply simp
 apply (simp add:td_gchain_def)
 apply (simp add:W_cmpser_def d_gchain_def) apply (simp add:special_subg_G)
apply (rotate_tac -1) apply simp
apply (erule conjE)
 apply (simp add:tD_gchain_def)
 apply (erule conjE)+
 apply (simp add:W_cmpser_def)
done

lemma joint_W_cmpser:"\<lbrakk>group G; W_cmpser G n f; W_cmpser G m g; g 0 \<lhd> grp G (f n); g 0 \<subset> f n\<rbrakk> \<Longrightarrow> W_cmpser G (Suc (n + m)) (jointfun n f m g)"
apply (simp add:W_cmpser_def [of _ "Suc (n + m)" _])
 apply (frule W_cmpser_is_D_gchain [of "G" "n" "f"], assumption+)
 apply (frule W_cmpser_is_D_gchain [of "G" "m" "g"], assumption+)
 apply (simp add:joint_D_gchains)
apply (frule W_cmpser_is_w_cmpser [of _ "n" _], assumption+)
apply (frule W_cmpser_is_w_cmpser [of _ "m" _], assumption+)
 apply (frule joint_w_cmpser [of "G" "n" "f" "m" "g"], assumption+)
 apply (simp add:w_cmpser_def [of _ "Suc (n + m)" _])
done

lemma joint_d_gchain_n0:"\<lbrakk> group G; d_gchain G n f; d_gchain G 0 g;
 g 0 \<subseteq> f n \<rbrakk> \<Longrightarrow>  d_gchain G (Suc n) (jointfun n f 0 g)"
apply (frule joint_d_gchains [of "G" "n" "f" "0" "g"], assumption+)
apply simp
done

lemma joint_D_gchain_n0:"\<lbrakk> group G; D_gchain G n f; D_gchain G 0 g; 
  g 0 \<subset> f n \<rbrakk> \<Longrightarrow>  D_gchain G (Suc n) (jointfun n f 0 g)" 
apply (frule joint_D_gchains [of "G" "n" "f" "0" "g"], assumption+)
apply simp
done

lemma joint_w_cmpser_n0:"\<lbrakk>group G; w_cmpser G n f; w_cmpser G 0 g; 
  g 0 \<lhd> grp G (f n) \<rbrakk> \<Longrightarrow>  w_cmpser G (Suc n) (jointfun n f 0 g)" 
apply (frule joint_w_cmpser [of "G" "n" "f" "0" "g"], assumption+)
apply simp
done

lemma joint_W_cmpser_n0:"\<lbrakk>group G; W_cmpser G n f; W_cmpser G 0 g; 
  g 0 \<lhd> grp G (f n); g 0 \<subset> f n \<rbrakk> \<Longrightarrow>  W_cmpser G (Suc n) (jointfun n f 0 g)" 
apply (frule joint_W_cmpser [of "G" "n" "f" "0" "g"], assumption+)
apply simp
done

constdefs
 simple_group :: "'a GroupType \<Rightarrow> bool"
    "simple_group G == group G \<and> {N. N \<guillemotleft> G} = {carrier G, {one G}}"

 compseries:: "[('a, 'more) GroupType_scheme , nat, nat \<Rightarrow> 'a set] \<Rightarrow> bool"
   "compseries G n f == tW_cmpser G n f \<and> (if n = 0 then f 0 = {one G} else 
  (\<forall> i \<in> Nset (n - 1). (simple_group ((grp G (f i))/(f (Suc i))))))"

 length_twcmpser:: "[('a, 'more) GroupType_scheme, nat, nat \<Rightarrow> 'a set] \<Rightarrow> nat"
   "length_twcmpser G n f == card (f `(Nset n)) - Suc 0" 


lemma compseriesTr0:"\<lbrakk> group G; compseries G n f; i \<in> Nset n\<rbrakk> \<Longrightarrow>
        f i \<guillemotleft> G"
apply (simp add:compseries_def) 
 apply (frule conj_1)
 apply (thin_tac "tW_cmpser G n f \<and>
       (if n = 0 then f 0 = {1\<^sub>G}
        else \<forall>i\<in>Nset (n - 1). simple_group (grp G (f i) / f (Suc i)))")
 apply (frule tW_cmpser_is_W_cmpser, assumption+)
 apply (frule W_cmpser_is_w_cmpser, assumption+)
 apply (frule w_cmpser_is_d_gchain, assumption+)
apply (simp add:d_gchain_def)
 apply (case_tac "n = 0") apply simp
 apply (simp add:Nset_def)
 apply simp
done

lemma compseriesTr1:"\<lbrakk> group G; compseries G n f\<rbrakk> \<Longrightarrow> tW_cmpser G n f"
apply (simp add:compseries_def)
done

lemma compseriesTr2:"\<lbrakk> group G; compseries G n f\<rbrakk> \<Longrightarrow> f 0 = carrier G"
apply (frule compseriesTr1, assumption+)
apply (simp add:tW_cmpser_def)
apply (case_tac "n = 0")
 apply (simp add:td_gchain_def)
apply simp
apply (erule conjE) apply (simp add:tD_gchain_def)
done

lemma compseriesTr3:"\<lbrakk> group G; compseries G n f\<rbrakk> \<Longrightarrow> f n = {1\<^sub>G}"
apply (frule compseriesTr1, assumption+)
apply (simp add:tW_cmpser_def)
apply (case_tac "n = 0")
apply (simp add:td_gchain_def)
apply (auto del:equalityI)
apply (simp add:tD_gchain_def)
done

lemma compseriesTr4:"\<lbrakk>group G; compseries G n f\<rbrakk> \<Longrightarrow> w_cmpser G n f"
apply (frule compseriesTr1, assumption+)
apply (frule tW_cmpser_is_W_cmpser, assumption+)
apply (frule W_cmpser_is_w_cmpser, assumption+)
done

lemma im_jointfun1Tr1:"\<lbrakk>group G;  \<forall>l\<in>Nset n. f l \<guillemotleft> G \<rbrakk> \<Longrightarrow>
                               f \<in> Nset n \<rightarrow> Collect (subgroup G)"
apply (simp add:Pi_def)
done

lemma im_jointfun1:"\<lbrakk>group G;  \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset m. g l \<guillemotleft> G\<rbrakk> \<Longrightarrow> 
 (jointfun n f m g) `(Nset (Suc (n + m))) = f `(Nset n) \<union> g `(Nset m)"
apply (frule im_jointfun1Tr1 [of "G" "n" "f"], assumption+)
apply (frule im_jointfun1Tr1 [of "G" "m" "g"], assumption+)
apply (rule im_jointfun [of "f" "n" "Collect (subgroup G)" "g" "m" "Collect (subgroup G)"], assumption+)
done

lemma Nset_Suc_im:"\<lbrakk>group G; \<forall>l\<in>Nset (Suc n). f l \<guillemotleft> G \<rbrakk> \<Longrightarrow>insert (f (Suc n)) (f ` Nset n) = f ` Nset (Suc n)"
apply (rule equalityI)
 apply (rule subsetI)
  apply (simp add:image_def)       apply (simp add:Nset_def)
  apply (case_tac "x = f (Suc n)") apply blast
  apply simp                    apply (subgoal_tac "\<forall>l. l \<le> n \<longrightarrow> l \<le> Suc n")
  apply blast                      apply simp
 apply (rule subsetI)              apply (simp add:image_def)
  apply (subgoal_tac "\<forall>xa\<in>Nset (Suc n). x = f xa \<longrightarrow> (x = f (Suc n) \<or> (\<exists>xa\<in>Nset n. x = f xa))")                  apply blast 
  apply (thin_tac "\<exists>xa\<in>Nset (Suc n). x = f xa")
 apply (rule ballI)                apply (rule impI)
 apply (case_tac "xa = Suc n")     apply simp
 apply (frule Nset_pre, assumption+)
 apply blast
done

constdefs
  NfuncPair_neq_at::"[nat \<Rightarrow> 'a set, nat \<Rightarrow> 'a set, nat] \<Rightarrow> bool"
    "NfuncPair_neq_at f g i == (f i \<noteq>  g i)" 

lemma LeastTr0:"\<lbrakk> (i::nat) < (LEAST l. P (l))\<rbrakk> \<Longrightarrow> \<not> P (i)"
apply (rule not_less_Least)
apply simp
done

lemma funeq_LeastTr1:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; 
  (l :: nat) < (LEAST k. (NfuncPair_neq_at f g k)) \<rbrakk> \<Longrightarrow> f l = g l"
apply (subgoal_tac "\<not> (NfuncPair_neq_at f g l)")
apply (simp add:NfuncPair_neq_at_def)
apply (rule  LeastTr0 [of "l" "NfuncPair_neq_at f g"])
apply assumption
done

lemma funeq_LeastTr1_1:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; 
  (l :: nat) < (LEAST k. (f k \<noteq>  g k)) \<rbrakk> \<Longrightarrow> f l = g l"
apply (subgoal_tac "\<not> (NfuncPair_neq_at f g l)")
apply (simp add:NfuncPair_neq_at_def)
apply (rule  LeastTr0 [of "l" "NfuncPair_neq_at f g"])
apply (simp add:NfuncPair_neq_at_def)
done

lemma Nfunc_LeastTr2_1:"\<lbrakk>group G; i \<in> Nset n;\<forall>l\<in>Nset n. f l \<guillemotleft> G; 
\<forall>l\<in>Nset n. g l \<guillemotleft> G; NfuncPair_neq_at f g i \<rbrakk> \<Longrightarrow> NfuncPair_neq_at f g (LEAST k. (NfuncPair_neq_at f g k))" 
apply (simp add: LeastI [of "NfuncPair_neq_at f g" "i"])
done

lemma Nfunc_LeastTr2_2:"\<lbrakk>group G; i \<in> Nset n;\<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; NfuncPair_neq_at f g i \<rbrakk> \<Longrightarrow> (LEAST k. (NfuncPair_neq_at f g k)) \<le> i" 
apply (simp add: Least_le [of "NfuncPair_neq_at f g" "i"])
done

lemma Nfunc_LeastTr2_2_1:"\<lbrakk>group G; i \<in> Nset n;\<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; f i \<noteq> g i\<rbrakk> \<Longrightarrow> (LEAST k. (f k \<noteq>  g k)) \<le> i"
apply (subgoal_tac "NfuncPair_neq_at f g i") 
apply (frule Nfunc_LeastTr2_2 [of "G" "i" "n" "f" "g"], assumption+)
apply (simp add:NfuncPair_neq_at_def)+
done

lemma Nfunc_LeastTr2_3:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; i \<in> Nset n; f i \<noteq> g i\<rbrakk>  \<Longrightarrow>  f (LEAST k. (f k \<noteq>  g k)) \<noteq> g (LEAST k. (f k \<noteq>  g k))" 
apply (frule  Nfunc_LeastTr2_1 [of "G" "i" "n" "f" "g"], assumption+)
apply (simp add:NfuncPair_neq_at_def)+
done

lemma  Nfunc_LeastTr2_4:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; i \<in> Nset n; f i \<noteq> g i\<rbrakk> \<Longrightarrow>(LEAST k. (f k \<noteq>  g k)) \<in> Nset n" 
apply (frule_tac i = i in Nfunc_LeastTr2_2 [of "G" _ "n" "f" "g"], 
                                      assumption+)
apply (simp add:NfuncPair_neq_at_def)
apply (simp add:Nset_def)
apply (frule le_trans [of "(LEAST k. NfuncPair_neq_at f g k)" "i" "n"],
                                  assumption+)
apply (simp add:NfuncPair_neq_at_def)
done

lemma Nfunc_LeastTr2_5:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; \<exists>i\<in> Nset n. (f i \<noteq> g i)\<rbrakk>  \<Longrightarrow>  f (LEAST k. (f k \<noteq>  g k)) \<noteq> g (LEAST k. (f k \<noteq>  g k))"
apply (auto del:equalityI)
apply (simp add:Nfunc_LeastTr2_3)
done

lemma Nfunc_LeastTr2_6:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; \<exists>i\<in> Nset n. (f i \<noteq> g i)\<rbrakk>  \<Longrightarrow> (LEAST k. (f k \<noteq>  g k)) \<in> Nset n"
apply (auto del:equalityI)
apply (rule Nfunc_LeastTr2_4, assumption+)
done

lemma Nfunc_Least_sym:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; \<exists>i\<in> Nset n. (f i \<noteq> g i)\<rbrakk> \<Longrightarrow> (LEAST k. (f k \<noteq>  g k)) = (LEAST k. (g k \<noteq> f k))"
apply (auto del:equalityI)
 apply (frule_tac i = i in Nfunc_LeastTr2_4 [of "G" "n" "f" "g"], 
                                assumption+)
 apply (frule_tac i = i in Nfunc_LeastTr2_3 [of "G" "n" "f" "g" _], 
                                   assumption+) 
 apply (rotate_tac -1) apply (frule_tac not_sym)
  apply (thin_tac "f (LEAST k. f k \<noteq> g k) \<noteq> g (LEAST k. f k \<noteq> g k)")
 apply (frule_tac i = "(LEAST k. f k \<noteq> g k)" in 
           Nfunc_LeastTr2_2_1 [of "G" _ "n" "g" "f"], assumption+)
apply (frule not_sym) 
  apply (thin_tac "f i \<noteq> g i")
  apply (thin_tac "(LEAST k. f k \<noteq> g k) \<in> Nset n")
  apply (thin_tac "g (LEAST k. f k \<noteq> g k) \<noteq> f (LEAST k. f k \<noteq> g k)")
  apply (frule_tac i = i in Nfunc_LeastTr2_4 [of "G" "n" "g" "f"], 
                                assumption+)
 apply (frule_tac i = i in Nfunc_LeastTr2_3 [of "G" "n" "g" "f" _], 
                                   assumption+) 
 apply (rotate_tac -1) apply (frule_tac not_sym)
  apply (thin_tac "g (LEAST k. g k \<noteq> f k) \<noteq> f (LEAST k. g k \<noteq> f k)")
 apply (frule_tac i = "(LEAST k. g k \<noteq> f k)" in 
           Nfunc_LeastTr2_2_1 [of "G" _ "n" "f" "g"], assumption+)
apply (rule le_anti_sym, assumption+)
done

lemma Nfunc_iNJTr:"\<lbrakk>group G; \<forall>l\<in>Nset n. g l \<guillemotleft> G;  inj_on g (Nset n);i \<in> Nset n; j \<in> Nset n; i < j \<rbrakk> \<Longrightarrow> g i \<noteq> g j"
apply (unfold inj_on_def)
apply auto
done

lemma Nfunc_LeastTr2_7:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; inj_on g (Nset n); \<exists>i \<in> Nset n. (f i \<noteq> g i); f k = g (LEAST k.(f k\<noteq>g k))\<rbrakk> \<Longrightarrow>(LEAST k.(f k \<noteq> g k)) < k"
apply (rule contrapos_pp) 
apply simp+ 
apply (subgoal_tac "k \<le> (LEAST k. f k \<noteq> g k)")
  apply (thin_tac "\<not> (LEAST k.(f k\<noteq>g k)) < k")
apply (frule le_imp_less_or_eq)
 apply (thin_tac "k \<le> (LEAST k. f k \<noteq> g k)")
apply (case_tac "k = (LEAST k. f k \<noteq> g k)")
 apply simp 
 apply (frule  Nfunc_LeastTr2_5 [of "G" "n" "f" "g"], assumption+)
 apply simp 
apply (frule funeq_LeastTr1_1 [of "G" "n" "f" "g" "k"], assumption+)
 apply simp
apply (frule Nfunc_LeastTr2_6 [of "G" "n" "f" "g"], assumption+)
apply (subgoal_tac "k \<in> Nset n") apply (rotate_tac -5)
 apply simp
 apply (simp add:inj_on_def) apply blast
 apply (simp add:Nset_def less_le_trans [of "k" "(LEAST k. f k \<noteq> g k)" "n"] less_imp_le)
apply (simp add:le_def)
done

lemma Nfunc_LeastTr2_8:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; \<forall>l\<in>Nset n. g l \<guillemotleft> G; inj_on g (Nset n); \<exists>i\<in>Nset n. f i \<noteq> g i; f `(Nset n) = g `(Nset n)\<rbrakk> \<Longrightarrow> \<exists> k \<in>(nset (Suc (LEAST i. (f i \<noteq> g i))) n). f k = g (LEAST i. (f i \<noteq>  g i))"
apply (frule_tac Nfunc_LeastTr2_6 [of "G" "n" "f" "g"], assumption+)
apply (subgoal_tac "\<forall>l\<in>Nset n. g l \<in> Collect (subgroup G)")
 apply (thin_tac "\<forall>l\<in>Nset n. g l \<guillemotleft> G")
 apply (frule mem_in_image1 [of "Nset n" "g" "Collect (subgroup G)" 
                                  "LEAST k. f k \<noteq> g k"], assumption+)
 apply (frule sym) apply (thin_tac "f ` Nset n = g ` Nset n")
 apply simp
 apply (thin_tac "g ` Nset n = f ` Nset n")
 apply (simp add:image_def)
apply (auto del:equalityI)
 apply (subgoal_tac "x \<in> nset (Suc (LEAST i. f i \<noteq> g i)) n")
 apply blast
 apply (rule contrapos_pp, simp+)
 apply (frule Nfunc_LeastTr2_5 [of "G" "n" "f" "g"], assumption+)
 apply blast
 apply (simp add:Nset_def nset_def)
 apply (simp add:le_def [of "Suc (LEAST i. f i \<noteq> g i)" _])
 apply (frule_tac m = x in Suc_leI [of _ "Suc (LEAST i. f i \<noteq> g i)"])
 apply simp
apply (case_tac "x = (LEAST i. f i \<noteq> g i)")
 apply simp
 apply (frule_tac m = x in noteq_le_less [of _ "(LEAST i. f i \<noteq> g i)"],
                                               assumption+)
 apply (frule_tac l = x in funeq_LeastTr1_1 [of "G" "n" "f" "g"])
 apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:Nset_def) apply assumption+
 apply simp
 apply (insert inj_onTr1 [of "g" "{i. i \<le> n}" _ "(LEAST i. f i \<noteq> g i)"])
 apply (simp add:Nset_def)
done

lemma Nfunc_LeastTr2_9:"\<lbrakk>group G; \<forall>l\<in>Nset n. f l \<guillemotleft> G; inj_on f (Nset n); \<forall>l\<in>Nset n. g l \<guillemotleft> G; inj_on g (Nset n); \<exists>i\<in>Nset n. f i \<noteq> g i; f `(Nset n) = g `(Nset n); k \<in> Nset n; f k = g (LEAST i. (f i \<noteq> g i))\<rbrakk> \<Longrightarrow> (LEAST i. (f i \<noteq>  g i)) < k"
apply (frule Nfunc_LeastTr2_8 [of "G" "n" "f" "g"], assumption+)
apply (auto del:equalityI) 
apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "f ka = g (LEAST i. f i \<noteq> g i)")
 apply simp
 apply (subgoal_tac "\<forall>l\<in>Nset n. f l \<in> Collect (subgroup  G)")
  apply (thin_tac "\<forall>l\<in>Nset n. f l \<guillemotleft> G")
  apply (subgoal_tac "\<forall>l\<in>Nset n. g l \<in> Collect (subgroup  G)")
  apply (thin_tac "\<forall>l\<in>Nset n. g l \<guillemotleft> G")
 apply (frule_tac y = ka in inj_onTr1 [of "f" "Nset n" "k" ], assumption+) 
 apply (simp add:Nset_def nset_def)
 apply assumption
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "k = ka")
 apply (simp add:nset_def) apply (erule conjE)
 apply (insert  n_less_Suc [of "(LEAST i. f i \<noteq> g i)"])
apply (rule_tac less_le_trans [of "(LEAST i. f i \<noteq> g i)" 
      "Suc (LEAST i. f i \<noteq> g i)" "k"], assumption+)
 apply simp+
done

lemma ex_redchainTr1:"\<lbrakk>group G; d_gchain G n f; D_gchain G (card (f ` Nset n) - Suc 0) g; g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n\<rbrakk> \<Longrightarrow> g (card (f ` Nset n) - Suc 0) = f n"
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "f n \<in> g ` Nset (card (f ` Nset n) - Suc 0)")
 prefer 2 
 apply (frule sym)
 apply (thin_tac "g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
 apply (subgoal_tac "f n \<in> f ` (Nset n)") apply simp
 apply (thin_tac "f ` Nset n = g ` Nset (card (f ` Nset n) - Suc 0)")
 apply (simp add:image_def) apply (simp add:Nset_def) apply blast
 apply (frule sym) 
  apply (thin_tac " g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
apply (simp add:image_def [of "g"])
 apply (auto del:equalityI) apply (fold image_def)
 apply (frule sym) 
apply (thin_tac "f ` Nset n = g ` Nset (card (f ` Nset n) - Suc 0)")
apply (subgoal_tac "g (card (f ` Nset n) - Suc 0) \<in> 
                          g ` Nset (card (f ` Nset n) - Suc 0)")
 apply simp
 apply (thin_tac "g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
prefer 2 apply (thin_tac "g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
 apply (simp add:image_def Nset_def)
 apply blast
apply (simp add:image_def [of "f"])
 apply (auto del:equalityI)
 apply (fold image_def)
apply (simp add:Nset_def)
apply (case_tac "x = card (f ` {i. i \<le> n}) - Suc 0")
 apply simp
 apply (frule_tac m = x in noteq_le_less 
                   [of _ "card (f ` {i. i \<le> n}) - Suc 0"], assumption+)
 apply (frule_tac i = x in  D_gchain0 [of "G" "card (f ` {i. i \<le> n}) - Suc 0" "g" _ "card (f ` {i. i \<le> n}) - Suc 0"], assumption+)
 apply (simp add:Nset_def)
 apply (simp add:Nset_def)
 apply assumption
apply (frule_tac sym) apply (thin_tac "f n = g x")
 apply simp
apply (case_tac "n = 0") apply simp apply simp
apply (frule_tac i = xa in d_gchainTr2 [of "G" "n" "f" _ "n"], assumption+)
apply (simp add:Nset_def)+
done

lemma ex_redchainTr1_1:"\<lbrakk>group G; d_gchain G n f; D_gchain G (card (f ` Nset n) - Suc 0) g; g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n\<rbrakk> \<Longrightarrow> g 0 = f 0"
apply (case_tac "card (f ` Nset n) - Suc 0 = 0")
 apply simp
 apply (subgoal_tac "f 0 \<in> g ` Nset 0") 
 apply (thin_tac "g ` Nset 0 = f ` Nset n")
 apply (simp add:image_def Nset_def)
 apply simp apply (simp add:Nset_def image_def) apply blast
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "f 0 \<in> g ` Nset (card (f ` Nset n) - Suc 0)")
 prefer 2 
 apply (frule sym)
 apply (thin_tac "g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
 apply (subgoal_tac "f 0 \<in> f ` (Nset n)") apply simp
 apply (thin_tac "f ` Nset n = g ` Nset (card (f ` Nset n) - Suc 0)")
 apply (simp add:image_def) apply (simp add:Nset_def) apply blast
 apply (frule sym) 
  apply (thin_tac " g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
apply (simp add:image_def [of "g"])
 apply (auto del:equalityI) apply (fold image_def)
 apply (frule sym) 
apply (thin_tac "f ` Nset n = g ` Nset (card (f ` Nset n) - Suc 0)")
apply (subgoal_tac "g 0 \<in> g ` Nset (card (f ` Nset n) - Suc 0)")
 apply simp
 apply (thin_tac "g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
prefer 2 apply (thin_tac "g ` Nset (card (f ` Nset n) - Suc 0) = f ` Nset n")
 apply (simp add:image_def Nset_def)
 apply blast
apply (simp add:image_def [of "f"])
 apply (auto del:equalityI)
 apply (fold image_def)
 apply (simp add:le_def [of "card (f ` (Nset n))" "Suc 0"]) 
 apply (frule less_diff_pos [of "Suc 0" "card (f ` (Nset n))"])
apply (case_tac "x = 0")
 apply simp+
 apply (frule_tac j = x in D_gchain0 [of "G" "card (f ` Nset n) - Suc 0" "g" "0"], assumption+)
 apply (simp add:Nset_def) apply assumption+
 apply (subgoal_tac "f xa \<subseteq> f 0")
 apply (frule_tac t = "f xa" in sym [of "g 0"])
 apply (thin_tac "g 0 = f xa") apply simp 
 apply (insert finite_Nset [of "0"])
 apply (frule card_image_le [of "Nset 0" "f"])
 apply (simp add:card_Nset [of "0"])
apply (case_tac "n = 0") apply simp+
 apply (frule_tac j = xa in  d_gchainTr2 [of "G" "n" "f" "0" _], assumption+) 
 apply (simp add:Nset_def)
 apply (simp add:Nset_def)
 apply simp
 apply (auto del:equalityI)
done

lemma ex_redchainTr2:"\<lbrakk>group G; d_gchain G (Suc n) f \<rbrakk>
               \<Longrightarrow> D_gchain G 0 (constmap (Nset 0) {f (Suc n)})"
apply (simp add:D_gchain_def constmap_def)
apply (simp add:Nset_def)
apply (simp add:d_gchain_def Nset_def)
done

lemma ex_redchainTr3:"\<lbrakk>group G; d_gchain G (Suc n) f; f n \<noteq> f (Suc n)\<rbrakk> \<Longrightarrow>
   f ` (Nset (Suc n)) = insert (f (Suc n)) (f ` (Nset n))"
apply (insert Nset_un [of "n"])
apply simp
done

lemma ex_redchainTr4:"\<lbrakk>group G; d_gchain G (Suc n) f; f n \<noteq> f (Suc n)\<rbrakk> \<Longrightarrow>
  card (f ` (Nset (Suc n))) = Suc (card (f ` (Nset n)))"
apply (frule ex_redchainTr3 [of "G" "n" "f"], assumption+)
apply simp
apply (rule card_insert_disjoint)
apply (simp add:finite_Nset)
apply (rule contrapos_pp, simp+) 
 apply (thin_tac " f ` Nset (Suc n) = insert (f (Suc n)) (f ` Nset n)")
 apply (simp add:image_def) apply (auto del:equalityI)
apply (simp add:Nset_def)
apply (case_tac "n = 0") apply simp apply simp
apply (frule d_gchain_pre, assumption+)
apply (frule_tac i = x in d_gchainTr2 [of "G" "n" "f" _ "n"], assumption+)
 apply (simp add:Nset_def)+
apply (frule d_gchainTr2 [of "G" "Suc n" "f" "n" "Suc n"])
 apply (simp add:Nset_def)+ 
done

lemma ex_redchainTr5:"\<lbrakk>group G; d_gchain G n f\<rbrakk> \<Longrightarrow> 0 < card (f ` (Nset n))"
apply (insert finite_Nset[of "n"])
apply (frule finite_imageI [of "Nset n" "f"])  
apply (subgoal_tac "{f 0} \<subseteq> f ` (Nset n)")
apply (frule card_mono [of "f ` Nset n" "{f 0}"], assumption+)
apply (simp add:card1)
apply (simp add:image_def) apply (simp add:Nset_def)
apply auto
done

lemma ex_redchainTr6:"group G \<Longrightarrow> \<forall>f. d_gchain G n f \<longrightarrow> (\<exists>g. D_gchain G ((card (f `(Nset n))) - 1) g \<and> (g ` (Nset ((card (f `(Nset n))) - 1)) = f `(Nset n)))"
apply (induct_tac n)
apply (rule allI) apply (rule impI)
 apply (subgoal_tac "f `(Nset 0) = {f 0}") apply simp
   apply (simp add:D_gchain_def Nset_def d_gchain_def)
   apply blast
   apply (simp add:image_def Nset_def) 
(** n **)
apply (rule allI) apply (rule impI)  
apply (case_tac "f (Suc n) = f n")
 apply (subgoal_tac "f `(Nset (Suc n)) = f `(Nset n)") 
 apply simp
 apply (frule_tac n = n and f = f in d_gchain_pre [of "G"], assumption+)
  apply (rotate_tac -1)
  apply simp
   apply (thin_tac "\<forall>f. d_gchain G n f \<longrightarrow> (\<exists>g. D_gchain G (card (f ` Nset n) - 1) g \<and> g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)")
   apply (subgoal_tac "Nset (Suc n) = Nset n \<union> {Suc n}")
   apply simp
   apply (subgoal_tac "f n \<in> f ` Nset n") 
 apply blast
  apply (simp add:image_def) 
  apply (thin_tac "Nset (Suc n) = insert (Suc n) (Nset n)")
  apply (simp add:Nset_def) apply blast
 apply (simp add:Nset_un)
 apply (frule_tac n = n and f = f in d_gchain_pre [of "G"], assumption+)
 apply (rotate_tac -1)
  apply (subgoal_tac "(\<exists>g. D_gchain G (card (f ` Nset n) - 1) g \<and>
                      g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)")
  prefer 2 apply simp
  apply (thin_tac "\<forall>f. d_gchain G n f \<longrightarrow>
                 (\<exists>g. D_gchain G (card (f ` Nset n) - 1) g \<and>
                      g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)")
 apply (auto del:equalityI)
 apply (frule_tac n = "Suc n" and f = f and i = n and j = "Suc n" in 
                               d_gchainTr2 [of "G"]) 
  apply simp apply assumption apply (simp add:Nset_def)
  apply (simp add:Nset_def) apply (simp add:less_imp_le)
  apply (frule_tac A = "f (Suc n)" and B = "f n" in psubsetI, assumption+)
  apply (thin_tac "f (Suc n) \<subseteq> f n")
  apply (frule_tac n = n and f = f and g = g in ex_redchainTr1, assumption+)
 apply (rotate_tac -1) apply (frule sym)
  apply (thin_tac "g (card (f ` Nset n) - Suc 0) = f n") apply simp
 apply (frule_tac n = n and f = f in ex_redchainTr2 [of "G"], assumption+)
 apply (frule_tac n = "(card (f ` Nset n) - Suc 0)" and f = g and g = "constmap (Nset 0) {f (Suc n)}" in joint_D_gchain_n0 [of "G"], assumption+)
 apply (simp add:constmap_def Nset_def)
 apply (rotate_tac -3) apply (frule sym)
  apply (thin_tac "f n = g (card (f ` Nset n) - Suc 0)") apply simp
apply (subgoal_tac "Suc (card (f ` Nset n) - Suc 0) = card (f ` Nset (Suc n)) - Suc 0") apply simp
apply (subgoal_tac "(jointfun (card (f ` Nset n) - Suc 0) g 0
             (constmap (Nset 0) {f (Suc n)})) `  Nset (card (f ` Nset (Suc n)) - Suc 0) = f ` Nset (Suc n)")
apply blast
 apply (thin_tac "d_gchain G n f")
 apply (thin_tac "g (card (f ` Nset n) - Suc 0) = f n")
 apply (rotate_tac -1) 
 apply (frule sym)
 apply (thin_tac "Suc (card (f ` Nset n) - Suc 0) = card (f ` Nset (Suc n)) - Suc 0") apply simp
 apply (thin_tac " card (f ` Nset (Suc n)) - Suc 0 = Suc (card (f ` Nset n) - Suc 0)")
 apply (frule_tac n = "(card (f ` Nset n) - Suc 0)" and f = g and m = 0 and g = "(constmap (Nset 0) {f (Suc n)})" in im_jointfun1 [of "G"])
 apply (thin_tac " D_gchain G (Suc (card (f ` Nset n) - Suc 0))
           (jointfun (card (f ` Nset n) - Suc 0) g 0
             (constmap (Nset 0) {f (Suc n)}))")
 apply (simp add:D_gchain_def)
  apply (case_tac " card (f ` Nset n) \<le> Suc 0") apply simp
  apply (simp add:Nset_def)
 apply simp apply (erule conjE)
 apply (simp add:d_gchain_def)
 apply (simp add:D_gchain_def [of _ "0" ] constmap_def)
 apply (simp add:Nset_def)
 apply (subgoal_tac "constmap (Nset 0) {f (Suc n)} ` Nset 0 = {f (Suc n)}")
 apply simp
apply (frule_tac n1 = n and f1 = f in ex_redchainTr3 [THEN sym, of "G"],
                                            assumption+)
 apply (rule not_sym, assumption)
 apply assumption+
 apply (simp add:constmap_def Nset_def)
apply (frule not_sym) apply (thin_tac "f (Suc n) \<noteq> f n")
apply (subst ex_redchainTr4, assumption+)
apply (frule_tac n = n and f = f in ex_redchainTr5 [of "G"], assumption+)
apply simp
done

lemma ex_redchain:"\<lbrakk>group G; d_gchain G n f\<rbrakk> \<Longrightarrow>(\<exists>g. D_gchain G (card (f ` Nset n) - 1) g \<and> g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)"
apply (frule ex_redchainTr6 [of "G" "n"])
apply simp
done

lemma const_W_cmpser:"\<lbrakk>group G; d_gchain G (Suc n) f\<rbrakk> \<Longrightarrow>
                            W_cmpser G 0 (constmap (Nset 0) {f (Suc n)})"
apply (simp add:W_cmpser_def d_gchain_def constmap_def)
apply (simp add:Nset_def)
done
        
lemma ex_W_cmpserTr0m:"group G \<Longrightarrow> \<forall>f. w_cmpser G m f \<longrightarrow>  (\<exists>g. (W_cmpser G ((card (f `(Nset m))) - 1)) g \<and> (g `(Nset ((card (f `(Nset m))) - 1)) = f `(Nset m)))"
apply (induct_tac m)
(********* induct_step m = 0 ***************)
apply (rule allI) apply (rule impI)
 apply (subgoal_tac "card (f `(Nset 0)) = Suc 0")
   apply simp
   apply (simp add:w_cmpser_def W_cmpser_def)
 apply (simp add:Nset_def)
  apply blast
 apply (simp add:Nset_def)
(********** induct_step  m ****************)
apply (rule allI) apply (rule impI)  
 apply (case_tac "f (Suc n) = f n")
  apply (subgoal_tac "f `(Nset (Suc n)) = f `(Nset n)") 
apply (frule w_cmpser_pre, assumption+) apply (rotate_tac -1)
 apply simp
 apply (thin_tac "\<forall>f. w_cmpser G n f \<longrightarrow> (\<exists>g. W_cmpser G 
 (card (f ` Nset n) - 1) g \<and> g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)")
 apply (subgoal_tac "Nset (Suc n) = (Nset n) \<union> {Suc n}") 
 apply simp
 apply (simp add:Nset_def)
 apply (simp add:Nset_un)
 apply (frule w_cmpser_pre, assumption+)
 apply (subgoal_tac "(\<exists>g. W_cmpser G (card (f ` Nset n) - 1) g \<and>
                      g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)")
 prefer 2 apply simp
 apply (thin_tac "\<forall>f. w_cmpser G n f \<longrightarrow> (\<exists>g. W_cmpser G (card (f ` Nset n) - 1) g \<and> g ` Nset (card (f ` Nset n) - 1) = f ` Nset n)")
 apply (auto del:equalityI)
 apply (frule_tac f = g in W_cmpser_is_D_gchain [of "G"], assumption+)
 apply (frule_tac n = "Suc n" and f = f in w_cmpser_is_d_gchain [of "G"],
                                    assumption+)
 apply (frule d_gchain_pre, assumption+)
 apply (frule_tac n = n and f = f and g = g in ex_redchainTr1 [of "G"],
                                      assumption+)
 apply (thin_tac "w_cmpser G n f")
 apply (simp add:w_cmpser_def [of "G"])
 apply (subgoal_tac "f (Suc n) \<lhd> grp G (f n)") prefer 2
  apply (simp add:Nset_def)
  apply (thin_tac "\<forall>i\<in>Nset n. f (Suc i) \<lhd> grp G (f i)")
 apply (frule_tac n = "Suc n" and f = f and i = n and j = "Suc n" in 
                                          d_gchainTr2 [of "G"]) 
  apply simp apply assumption apply (simp add:Nset_def)
  apply (simp add:Nset_def) apply simp
  apply (frule_tac A = "f (Suc n)" and B = "f n" in psubsetI, assumption+)
 apply (frule_tac n = "(card (f ` Nset n)) - Suc 0" and f = g and g = "constmap (Nset 0) {f (Suc n)}" in joint_W_cmpser_n0 [of "G"], assumption+)
 apply (frule_tac n = n and f = f and g = g in ex_redchainTr1 [of "G"], 
                                                    assumption+)
 apply (rule const_W_cmpser, assumption+)
 apply (simp add:constmap_def Nset_def)
 apply (simp add:constmap_def Nset_def)
 apply (frule_tac n = n and f = f in ex_redchainTr4 [of "G"], assumption+)
 apply (rule not_sym, assumption) apply simp
 apply (thin_tac "card (f ` Nset (Suc n)) = Suc (card (f ` Nset n))")
 apply (frule_tac n = n and f = f in ex_redchainTr5 [of "G"], assumption+)
 apply simp
apply (subgoal_tac "(jointfun (card (f ` Nset n) - Suc 0) g 0 (constmap (Nset 0) {f (Suc n)})) ` Nset (card (f ` Nset n)) = f ` Nset (Suc n)")
apply blast
 apply (frule D_gchain_is_d_gchain, assumption+)
 apply (thin_tac "D_gchain G (card (f ` Nset n) - Suc 0) g")
 apply (thin_tac "g (card (f ` Nset n) - Suc 0) = f n")
 apply (thin_tac "f (Suc n) \<subseteq> f n") apply (thin_tac "f (Suc n) \<subset> f n")
 apply (thin_tac "d_gchain G n f")
 apply (thin_tac "f (Suc n) \<lhd> grp G (f n)")
 apply (thin_tac "W_cmpser G (card (f ` Nset n)) (jointfun (card (f ` Nset n) - Suc 0) g 0 (constmap (Nset 0) {f (Suc n)}))") 
 apply (frule_tac n = "(card (f ` Nset n) - Suc 0)" and f = g and m = 0 
 and g = "(constmap (Nset 0) {f (Suc n)})" in im_jointfun1 [of "G"])
 apply (simp add:d_gchain_def)
 apply (case_tac "card (f ` Nset n) \<le> Suc 0") apply simp
 apply (frule W_cmpser_is_w_cmpser, assumption+)
 apply (frule w_cmpser_is_d_gchain, assumption+) 
 apply (simp add:d_gchain_def Nset_def) apply simp
 apply (simp add:constmap_def d_gchain_def Nset_def)
 apply simp
 apply (subst im_of_constmap) 
 apply (frule not_sym) apply (thin_tac "f (Suc n) \<noteq> f n")
apply (frule_tac n1 = n and f1 = f in ex_redchainTr3[THEN sym, of "G"],
                                                         assumption+)
apply simp
done

lemma ex_W_cmpser:"\<lbrakk> group G; w_cmpser G m f \<rbrakk> \<Longrightarrow>\<exists>g. W_cmpser G (card (f ` Nset m) - 1) g \<and>  g ` Nset (card (f ` Nset m) - 1) = f ` Nset m"
apply (frule ex_W_cmpserTr0m [of "G" "m" ])
apply simp
done

section "17. Existence of reduced chain and composition series"

lemma ex_W_cmpserTr3m1:"\<lbrakk>group G; tw_cmpser G m f; W_cmpser G ((card (f ` (Nset m))) - 1) g; g `(Nset ((card (f `(Nset m))) - 1)) = f `(Nset m)\<rbrakk> \<Longrightarrow> tW_cmpser G ((card (f ` (Nset m))) - 1) g"
apply (frule_tac tw_cmpser_is_w_cmpser [of "G" "m" "f"], assumption+)
apply (frule_tac w_cmpser_is_d_gchain [of "G" "m" "f"], assumption+)
apply (frule_tac W_cmpser_is_D_gchain [of "G" "(card (f ` Nset m) - 1)" "g"],
                                                          assumption+)
apply (frule ex_redchainTr1 [of "G" "m" "f" "g"], assumption+)
 apply simp+
apply (frule_tac ex_redchainTr1_1 [of "G" "m" "f" "g"], assumption+)
 apply (simp add:tW_cmpser_def tw_cmpser_def)
 apply (case_tac "m = 0") apply simp
 apply (insert finite_Nset [of "0"])
 apply (frule card_image_le [of "Nset 0" "f"])
 apply (simp add:card_Nset [of "0"])
 apply (simp add:td_gchain_def) 
 apply blast
apply simp apply (erule conjE)+
 apply (case_tac "card (f ` Nset m) \<le> Suc 0") apply simp
 apply (simp add:td_gchain_def) apply blast
 apply simp
 apply (simp add:W_cmpser_def [of _ _ "g"])
 apply (thin_tac "\<forall>i\<in>Nset (card (f ` Nset m) - Suc (Suc 0)). g (Suc i) \<lhd> grp G (g i)")
 apply (simp add:tD_gchain_def td_gchain_def [of _ "m" "f"])
done

lemma ex_W_cmpserTr3m:"\<lbrakk>group G; tw_cmpser G m f\<rbrakk> \<Longrightarrow> \<exists>g. tW_cmpser G ((card (f ` (Nset m))) - 1) g \<and> g `(Nset ((card (f `(Nset m))) - 1)) = f `(Nset m)"
apply (frule tw_cmpser_is_w_cmpser[of "G" "m" "f"], assumption+)
apply (frule ex_W_cmpser [of "G" "m" "f"], assumption+)
apply (auto del:equalityI)
apply (frule_tac g = g in ex_W_cmpserTr3m1 [of "G" "m" "f"], assumption+) 
apply simp+
apply (auto del:equalityI)
done

constdefs 
  red_ch_cd::"[('a, 'more) GroupType_scheme, nat \<Rightarrow> 'a set, nat, nat \<Rightarrow> 'a set ] \<Rightarrow> bool"
    "red_ch_cd G f m g == tW_cmpser G (card (f `(Nset m)) - 1) g \<and> (g `(Nset (card (f `(Nset m)) - 1)) = f` (Nset m))"
 
 red_chain::"[('a, 'more) GroupType_scheme, nat, nat \<Rightarrow> 'a set] \<Rightarrow>
                                                     (nat \<Rightarrow> 'a set)"
  "red_chain G m f == (SOME g. g \<in> {h. red_ch_cd G f m h})"

lemma red_chainTr0m1_1:"\<lbrakk>group G; tw_cmpser G m f \<rbrakk> \<Longrightarrow> 
       (SOME g. g \<in> {h. red_ch_cd G f m h}) \<in> {h. red_ch_cd G f m h}"
apply (subgoal_tac "{h. red_ch_cd G f m h} \<noteq> {}")  
apply (rule nonempty_some [of "{h. red_ch_cd G f m h}"], assumption+)
apply (frule ex_W_cmpserTr3m [of "G" "m" "f"], assumption+)
 apply simp
 apply (simp add:red_ch_cd_def)
done

lemma red_chain_m:"\<lbrakk>group G; tw_cmpser G m f\<rbrakk> \<Longrightarrow> tW_cmpser G (card (f `(Nset m)) - 1) (red_chain G m f) \<and> (red_chain G m f) `(Nset (card (f `(Nset m)) - 1)) = f `(Nset m)"
apply (frule red_chainTr0m1_1 [of "G" "m" "f"], assumption+)
apply (subgoal_tac "(SOME g. g \<in> {h. red_ch_cd G f m h}) = red_chain G m f")
 apply (simp add:CollectI red_ch_cd_def)
 apply (simp add:CollectI red_chain_def)
done

section "18. Chain of groups II"

constdefs  
 Gchain :: "[nat, nat \<Rightarrow> (('a set), 'more) GroupType_scheme] \<Rightarrow> bool"
 "Gchain n g == \<forall>l\<in>Nset n. group (g l)"  

 isom_Gchains::"[nat, nat \<Rightarrow> nat, nat \<Rightarrow> (('a set), 'more) GroupType_scheme, nat \<Rightarrow> (('a set), 'more) GroupType_scheme]  \<Rightarrow> bool"
 "isom_Gchains n f g h == \<forall>i\<in>Nset n. (g i) \<cong> (h (f i))"
(* g, h are sequences of groups and f is gbijection of Nset to Nset *)

 Gch_bridge::"[nat, nat \<Rightarrow> (('a set), 'more) GroupType_scheme, nat \<Rightarrow> (('a set), 'more) GroupType_scheme, nat \<Rightarrow> nat]  \<Rightarrow> bool"
 "Gch_bridge n g h f == (\<forall>l\<in>Nset n. f l \<in> Nset n) \<and> inj_on f (Nset n) \<and> isom_Gchains n f g h" 

lemma Gchain_pre:"Gchain (Suc n) g \<Longrightarrow> Gchain n g"    
apply (simp add:Gchain_def Nset_def)
done

lemma isom_unit:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G; H = {one G}\<rbrakk>
  \<Longrightarrow> grp G H \<cong> grp G K \<longrightarrow> K = {one G}"
apply (simp add:isomorphism_def)
apply (rule impI)
apply (auto del:equalityI)
 apply (simp add:gbijec_def)
 apply (erule conjE)
 apply (simp add:gsurjec_def ginjec_def)
 apply (erule conjE)
apply (simp add:grp_carrier)
apply (simp add:surj_to_def)
apply (subgoal_tac "finite {f (1\<^sub>G)}") prefer 2 apply (rule finite1)
apply simp
apply (frule subg_one_closed [of "G" "K"], assumption+)
apply (subgoal_tac "{1\<^sub>G} \<subseteq> K") prefer 2 apply simp
apply (frule card_seteq, assumption+)
apply (subgoal_tac "card {f (1\<^sub>G)} = Suc 0") 
 apply simp apply (thin_tac "{f (1\<^sub>G)} = K") apply (simp add:card1)
apply (rule sym, assumption)
done

lemma isom_gch_unitsTr4:"\<lbrakk> group F; group G; Ugp E; F \<cong> G; F \<cong> E \<rbrakk> \<Longrightarrow>
      G \<cong> E"
apply (simp add:Ugp_def)
apply (erule conjE)
apply (frule isomTr1 [of "F" "G"], assumption+)
apply (rule isomTr2 [of "G" "F" "E"], assumption+)
done 

lemma isom_gch_cmp:"\<lbrakk>Gchain n g; Gchain n h; f1 \<in> Nset n \<rightarrow> Nset n; f2 \<in> Nset n \<rightarrow> Nset n; isom_Gchains n (cmp f2 f1) g h\<rbrakk> \<Longrightarrow> isom_Gchains n f1 g (cmp h f2)"
apply (simp add:isom_Gchains_def)
apply (simp add:cmp_def)
done

lemma isom_gch_transp:"\<lbrakk>Gchain n f; i \<in> Nset n; j \<in> Nset n; i < j\<rbrakk> \<Longrightarrow> 
                 isom_Gchains n (transpos i j) f (cmp  f (transpos i j))"
apply (rule isom_gch_cmp [of "n" "f" _ "transpos i j" "transpos i j"],
                                                                 assumption+)
 apply (rule transpos_hom, assumption+) apply simp
 apply (rule transpos_hom, assumption+) apply simp
apply (simp add:isom_Gchains_def)
apply (rule ballI) apply (simp add:Nset_def)
apply (frule less_le_trans [of "i" "j" "n"], assumption+)
apply (frule less_imp_le [of "i" "n"])
apply (frule_tac k = ia in cmp_transpos1 [of "i" "n" "j"], assumption+)
 apply simp apply (simp add:Nset_def)
apply simp
apply (simp add:Gchain_def)
apply (rule isomTr0)
apply (simp add:Nset_def)
done

lemma isom_gch_units_transpTr0:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<in> Nset n; j \<in> Nset n; i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow> {i. i \<in> Nset n \<and> g i \<cong> E} - {i, j} ={i. i \<in> Nset n \<and> h i \<cong> E} - {i, j}"
apply (simp add:isom_Gchains_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (erule conjE)+
 apply (frule_tac x = x in transpos_id_1 [of "i" "n" "j"], assumption+)
 apply simp apply assumption+
apply (subgoal_tac "g x \<cong> h (transpos i j x)")
 apply (thin_tac "\<forall>ia\<in>Nset n. g ia \<cong> h (transpos i j ia)")
 apply simp
apply (subgoal_tac "group (g x)")
apply (subgoal_tac "group (h x)")
apply (simp add:Ugp_def) apply (erule conjE)
apply (frule_tac F = "g x" and G = "h x" in isomTr1, assumption+)
apply (rule_tac F = "h x" and G = "g x" and H = E in isomTr2, assumption+)
apply (simp add:Gchain_def)
apply (simp add:Gchain_def)
 apply (thin_tac "transpos i j x = x")
 apply simp
apply (rule subsetI) apply (simp add:CollectI)
 apply (erule conjE)+
 apply (frule_tac x = x in transpos_id_1 [of "i" "n" "j"], assumption+)
 apply simp apply assumption+
apply (subgoal_tac "g x \<cong> h (transpos i j x)")
 apply (thin_tac "\<forall>ia\<in>Nset n. g ia \<cong> h (transpos i j ia)")
 apply simp
apply (subgoal_tac "group (g x)")
apply (subgoal_tac "group (h x)")
apply (simp add:Ugp_def) apply (erule conjE)
apply (rule_tac F = "g x" and G = "h x" and H = E in isomTr2, assumption+)
apply (simp add:Gchain_def)
apply (simp add:Gchain_def)
 apply (thin_tac "transpos i j x = x")
 apply simp
done

lemma isom_gch_units_transpTr1:"\<lbrakk>Ugp E; Gchain n g; i \<in> Nset n; j \<in> Nset n; g j \<cong> E; i \<noteq> j\<rbrakk> \<Longrightarrow> insert j ({i. i \<in> Nset n \<and> g i \<cong> E} - {i, j}) = {i. i \<in> Nset n \<and> g i \<cong> E} - {i}"
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply blast
apply (rule subsetI) apply (simp add:CollectI)
done

lemma isom_gch_units_transpTr2:"\<lbrakk>Ugp E; Gchain n g; i \<in> Nset n; j \<in> Nset n; i < j; g i \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset n \<and> g i \<cong> E} = insert i ({i. i \<in> Nset n \<and> g i \<cong> E} - {i})"
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
apply (rule subsetI) apply (simp add:CollectI)
 apply blast
done

lemma isom_gch_units_transpTr3:"\<lbrakk>Ugp E; Gchain n g; i \<in> Nset n\<rbrakk>
                         \<Longrightarrow> finite ({i. i \<in> Nset n \<and> g i \<cong> E} - {i})"
apply (insert finite_Nset [of "n"])
apply (subgoal_tac "({i. i \<in> Nset n \<and> g i \<cong> E} - {i}) \<subseteq> Nset n")
apply (rule finite_subset, assumption+)
apply (rule subsetI)
apply (simp add:CollectI)
done

lemma isom_gch_units_transpTr4:"\<lbrakk>Ugp E; Gchain n g; i \<in> Nset n\<rbrakk>
                         \<Longrightarrow> finite ({i. i \<in> Nset n \<and> g i \<cong> E} - {i, j})"
apply (insert finite_Nset [of "n"])
apply (subgoal_tac "({i. i \<in> Nset n \<and> g i \<cong> E} - {i, j}) \<subseteq> Nset n")
apply (rule finite_subset, assumption+)
apply (rule subsetI)
apply (simp add:CollectI)
done

lemma isom_gch_units_transpTr5_1:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<in> Nset n; j \<in> Nset n; i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow> g i \<cong> h j"
apply (simp add:isom_Gchains_def)
apply (subgoal_tac "g i \<cong> h (transpos i j i)")
apply (simp add:transpos_ij_1 [of "i" "n" "j"])
apply simp
done

lemma isom_gch_units_transpTr5_2:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<in> Nset n; j \<in> Nset n; i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow> g j  \<cong> h i"
apply (simp add:isom_Gchains_def)
apply (subgoal_tac "g j \<cong> h (transpos i j j)")
apply (simp add:transpos_ij_2 [of "i" "n" "j"]) 
apply simp
done

lemma isom_gch_units_transpTr6:"\<lbrakk>Gchain n g; i \<in> Nset n\<rbrakk> \<Longrightarrow> group (g i)"
apply (simp add:Gchain_def)
done

lemma isom_gch_units_transpTr7:"\<lbrakk>Ugp E;i \<in> Nset n; j \<in> Nset n; g j \<cong> h i; group (h i); group (g j); \<not> g j \<cong> E\<rbrakk> \<Longrightarrow>  \<not> h i \<cong> E"
apply (rule contrapos_pp, simp+)
apply (frule isomTr2 [of "g j" "h i" "E"], assumption+)
apply (simp add:Ugp_def)
apply assumption+
apply simp
done

lemma isom_gch_units_transpTr8_1:"\<lbrakk>Ugp E; Gchain n g; i \<in> Nset n; j \<in> Nset n; g i \<cong> E; \<not> g j \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset n \<and> g i \<cong> E} = {i. i \<in> Nset n \<and> g i \<cong> E} - { j }"
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI)
apply (rule subsetI) apply (simp add:CollectI)
done

lemma isom_gch_units_transpTr8_2:"\<lbrakk>Ugp E; Gchain n g; i \<in> Nset n; j \<in> Nset n; \<not> g i \<cong> E; \<not> g j \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset n \<and> g i \<cong> E} = {i. i \<in> Nset n \<and> g i \<cong> E} - {i, j }"
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI)
apply (rule subsetI) apply (simp add:CollectI)
done


lemma isom_gch_units_transp:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<in> Nset n; j \<in> Nset n; i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow>  card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and> h i \<cong> E}" 
apply (frule isom_gch_units_transpTr0 [of "E" "n" "g" "h" "i" "j"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "g" "i"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "h" "i"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "g" "j"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "h" "j"], assumption+)
apply (unfold Ugp_def) apply (frule conj_1) apply (fold Ugp_def)
apply (frule isom_gch_units_transpTr5_1 [of "E" "n" "g" "h" "i" "j"], 
                                                          assumption+)
apply (frule isom_gch_units_transpTr5_2 [of "E" "n" "g" "h" "i" "j"], 
                                                          assumption+)
apply (case_tac "g i \<cong> E")
 apply (case_tac "g j \<cong> E")  (** g i \<cong> E and g j \<cong> E **)
 apply (subst isom_gch_units_transpTr2 [of "E" "n" "g" "i" "j"], assumption+)
 apply (subst isom_gch_units_transpTr2 [of "E" "n" "h" "i" "j"], assumption+) 
 apply (rule isom_gch_unitsTr4 [of "g j" "h i" "E"], assumption+)
 apply (subst card_insert_disjoint) 
 apply (rule isom_gch_units_transpTr3, assumption+)
 apply simp
 apply (subst card_insert_disjoint)
 apply (rule isom_gch_units_transpTr3, assumption+)
 apply simp
 apply (subst isom_gch_units_transpTr1[THEN sym, of "E" "n" "g" "i" "j"], assumption+) apply simp
apply (subst isom_gch_units_transpTr1[THEN sym, of "E" "n" "h" "i" "j"], assumption+)
 apply (rule isom_gch_unitsTr4 [of "g i" "h j" "E"], assumption+)
apply simp 
apply simp
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "g" "i" "j"], assumption+)
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "h" "j" "i"], assumption+)
 apply (rule isom_gch_unitsTr4 [of "g i" "h j" "E"], assumption+)
 apply (rule isom_gch_units_transpTr7 [of "E" "i" "n" "j" "g" "h"], 
                                                        assumption+)
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "g" "j" "i"], assumption+) apply simp
 apply (subst card_insert_disjoint)
 apply (rule isom_gch_units_transpTr4, assumption+)
 apply simp
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "h" "i" "j"],
                                                                assumption+)
 apply (rule isom_gch_unitsTr4 [of "g i" "h j" "E"], assumption+)
 apply simp
 apply (subst card_insert_disjoint)
  apply (rule isom_gch_units_transpTr4, assumption+)
  apply simp
  apply (insert Nset_2 [of "j" "i"])
  apply simp
apply (case_tac "g j \<cong> E")
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "g" "j" "i"], assumption+)
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "h" "i" "j"], assumption+)
 apply (rule isom_gch_unitsTr4 [of "g j" "h i" "E"], assumption+)
 apply (rule isom_gch_units_transpTr7 [of "E" "j" "n" "i" "g" "h"], assumption+)
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "g" "i" "j"],
                                                              assumption+)
 apply simp
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "h" "j" "i"],
                                                              assumption+)
 apply (rule isom_gch_unitsTr4 [of "g j" "h i" "E"], assumption+)
 apply simp apply simp
 apply (subst card_insert_disjoint)
  apply (rule isom_gch_units_transpTr4, assumption+)
  apply simp
 apply (subst card_insert_disjoint)
  apply (rule isom_gch_units_transpTr4, assumption+)
  apply simp  apply simp
 apply (subst isom_gch_units_transpTr8_2 [of "E" "n" "g" "i" "j"], assumption+)
 apply (subst isom_gch_units_transpTr8_2 [of "E" "n" "h" "i" "j"], assumption+)
 apply (rule isom_gch_units_transpTr7[of "E" "i" "n" "j" "g" "h"], assumption+)
 apply (rule isom_gch_units_transpTr7[of "E" "j" "n" "i" "g" "h"], assumption+)
apply simp
done

lemma TR_isom_gch_units:"\<lbrakk>Ugp E; Gchain n f; i \<in> Nset n; j \<in> Nset n; i < j\<rbrakk> \<Longrightarrow>  card {k. k \<in> Nset n \<and> f k \<cong> E} = card {k. k \<in> Nset n \<and> (cmp f (transpos i j)) k \<cong> E}" 
apply (frule isom_gch_transp [of "n" "f" "i" "j"], assumption+)
apply (subgoal_tac "Gchain n (cmp f (transpos i j))")
 apply (rule isom_gch_units_transp [of "E" "n" "f" _ "i" "j"], assumption+)
 apply (simp add:Gchain_def)
 apply (rule ballI)
 apply (simp add:cmp_def)
apply (frule_tac l = l in transpos_mem [of "i" "n" "j"], assumption+)
 apply simp 
 apply (rotate_tac -1)
 apply simp 
 apply (auto del:equalityI)
done

lemma TR_isom_gch_units_1:"\<lbrakk>Ugp E; Gchain n f; i \<in> Nset n; j \<in> Nset n; i < j\<rbrakk> \<Longrightarrow>  card {k. k \<in> Nset n \<and> f k \<cong> E} = card {k. k \<in> Nset n \<and> f (transpos i j k) \<cong> E}" 
apply (frule TR_isom_gch_units [of "E" "n" "f" "i" "j"], assumption+)
 apply (simp add:cmp_def)
done

lemma isom_tgch_unitsTr0_1:"\<lbrakk>Ugp E; Gchain (Suc n) g; g (Suc n) \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset (Suc n) \<and> g i \<cong> E} = insert (Suc n) {i. i \<in> Nset n \<and> g i \<cong> E}"
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:CollectI Nset_def)
 apply (case_tac "x = Suc n") apply simp
 apply (erule conjE) apply simp 
apply (rule subsetI)
 apply (simp add:CollectI)
apply (simp add:Nset_def)
 apply auto
done

lemma isom_tgch_unitsTr0_2:"Ugp E  \<Longrightarrow> finite ({i. i \<in> Nset n \<and> g i \<cong> E})"
apply (insert finite_Nset [of "n"])
apply (subgoal_tac "{i. i \<in> Nset n \<and> g i \<cong> E} \<subseteq> Nset n")
apply (rule finite_subset, assumption+)
apply (rule subsetI)
apply (simp add:CollectI)
done

lemma isom_tgch_unitsTr0_3:"\<lbrakk>Ugp E; Gchain (Suc n) g; \<not> g (Suc n) \<cong> E\<rbrakk>
      \<Longrightarrow> {i. i \<in> Nset (Suc n) \<and> g i \<cong> E} = {i. i \<in> Nset n \<and> g i \<cong> E}"
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI)
apply (case_tac "x = Suc n") apply simp apply (erule conjE)
 apply (frule Nset_pre, assumption+)  
apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
apply (simp add:Nset_def)
done

lemma isom_tgch_unitsTr0:"\<lbrakk>Ugp E; card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and> h i \<cong> E}; Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f; f (Suc n) = Suc n\<rbrakk> \<Longrightarrow> card {i. i \<in> Nset (Suc n) \<and> g i \<cong> E} = card {i. i \<in> Nset (Suc n) \<and> h i \<cong> E}"
apply (erule conjE)+
apply (frule isom_gch_units_transpTr6 [of "Suc n" "g" "Suc n"])
apply (simp add:Nset_def)
apply (frule isom_gch_units_transpTr6 [of "Suc n" "h" "Suc n"])
apply (simp add:Nset_def)
 apply (case_tac "g (Suc n) \<cong> E")
 apply (subst isom_tgch_unitsTr0_1 [of "E" "n" "g"], assumption+)
 apply (subst isom_tgch_unitsTr0_1 [of "E" "n" "h"], assumption+) 
 apply (frule isom_gch_unitsTr4 [of "g (Suc n)" "h (Suc n)" "E"], assumption+)
apply (simp add:Gch_bridge_def) apply (frule conj_2)
apply (fold Gch_bridge_def) apply (frule conj_2)
apply (simp add:isom_Gchains_def) apply (erule conjE)
apply (simp add:Nset_def) 
 apply (thin_tac "card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and> h i \<cong> E}")
 apply (frule sym) apply (thin_tac "f (Suc n) = Suc n")
 apply auto
apply (subst card_insert_disjoint) 
 apply (simp add:isom_tgch_unitsTr0_2 [of "E" "n" "h"])
 apply (simp add:Nset_def)
apply (simp add:Gch_bridge_def) apply (frule conj_2)
 apply (fold Gch_bridge_def) apply (frule conj_2)
 apply (thin_tac "inj_on f (Nset (Suc n)) \<and> isom_Gchains (Suc n) f g h")
apply (subgoal_tac "group (h (f (Suc n)))")
apply (frule isom_gch_unitsTr4 [of "g (Suc n)" "h (f (Suc n))" "E"], 
                                                  assumption+)
 apply (thin_tac "f (Suc n) = Suc n")
apply (simp add:isom_Gchains_def Nset_def) apply assumption
apply simp
apply (subst card_insert_disjoint)
apply (simp add:isom_tgch_unitsTr0_2) apply (simp add:Nset_def)
apply simp
apply simp 
apply (subst isom_tgch_unitsTr0_3 [of "E" "n" "g"], assumption+) 
apply (subst isom_tgch_unitsTr0_3 [of "E" "n" "h"], assumption+)
apply (subgoal_tac "g (Suc n) \<cong> h (f (Suc n))") apply simp
apply (frule isom_gch_units_transpTr7 [of "E" "Suc n" "Suc n" "Suc n" "g" "h"])
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply assumption+
apply (thin_tac "f (Suc n) = Suc n")
 apply (simp add:Gch_bridge_def) apply (erule conjE)+
 apply (simp add:isom_Gchains_def) apply (simp add:Nset_def)
apply simp
done

lemma isom_gch_unitsTr1_1:" \<lbrakk>Ugp E; Gchain (Suc n) g \<and>  Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f; f (Suc n) = Suc n\<rbrakk> \<Longrightarrow> 
 Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f"
apply (erule conjE)+
apply (frule Gchain_pre [of "n" "g"])
apply (frule Gchain_pre [of "n" "h"])
apply simp
apply (simp add:Gch_bridge_def) apply (erule conjE)+
apply (rule conjI)
apply (rule Nset_injTr2, assumption+)
apply (rule conjI)
apply (rule Nset_injTr1, assumption+)
apply (simp add:isom_Gchains_def Nset_def)
done

lemma isom_gch_unitsTr1_2:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; \<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n); inj_on f (Nset (Suc n)) \<rbrakk> \<Longrightarrow> (cmp (transpos (f (Suc n)) (Suc n)) f) (Suc n) = Suc n"
apply (simp add:cmp_def)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f"  "Nset (Suc n)" ], assumption+)
apply (rule transpos_ij_1, assumption+)  apply (simp add:Nset_def)
done

lemma isom_gch_unitsTr1_3:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; \<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n); inj_on f (Nset (Suc n)) \<rbrakk> \<Longrightarrow> 
      inj_on (cmp (transpos (f (Suc n)) (Suc n)) f) (Nset (Suc n))"
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule funcset_mem1 [of "Nset (Suc n)" "f" "Nset (Suc n)" "Suc n"],
                                                   assumption+)
apply (frule transpos_hom [of "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply (frule transpos_inj [of "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply (subgoal_tac "f \<in> Nset (Suc n) \<rightarrow> Nset (Suc n)")
apply (frule cmp_inj_1 [of "f" "Nset (Suc n)" "Nset (Suc n)" "transpos (f (Suc n)) (Suc n)" "Nset (Suc n)"], assumption+)
apply (simp add:Pi_def)
apply (simp add:Nset_def)
done

lemma isom_gch_unitsTr1_4:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; \<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n); inj_on f (Nset (Suc n)) \<rbrakk> \<Longrightarrow> 
      inj_on (cmp (transpos (f (Suc n)) (Suc n)) f) (Nset n)"
apply (frule isom_gch_unitsTr1_3 [of "E" "f" "n"], assumption+)
apply (frule isom_gch_unitsTr1_2 [of "E" "f" "n"], assumption+)
apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). cmp (transpos (f (Suc n)) (Suc n)) f l \<in> Nset (Suc n)")
apply (frule Nset_injTr1 [of "n" "(cmp (transpos (f (Suc n)) (Suc n)) f)"],
                                           assumption+)
apply (rule ballI)
apply (simp add:cmp_def) 
apply (frule_tac x = l in funcset_mem1 [of "Nset (Suc n)" "f" 
        "Nset (Suc n)" ], assumption+)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" 
        "Nset (Suc n)" ], assumption+)
apply (rule_tac l = "f l" in transpos_mem [of 
                          "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply (simp add:Nset_def)
done 

lemma isom_gch_unitsTr1_5:"\<lbrakk>Ugp E; Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f; f (Suc n) \<noteq> Suc n \<rbrakk> \<Longrightarrow> Gchain n g \<and> Gchain n (cmp h (transpos (f (Suc n)) (Suc n))) \<and> Gch_bridge n g (cmp h (transpos (f (Suc n)) (Suc n))) (cmp (transpos (f (Suc n)) (Suc n)) f)"
apply (erule conjE)+ 
apply (simp add:Gchain_pre [of "n" "g"])
apply (rule conjI)
apply (simp add:Gchain_def) apply (rule ballI)
apply (simp add:Gch_bridge_def) apply (frule conj_1)
apply (fold Gch_bridge_def)
apply (frule Nsetn_sub_mem)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" "Nset (Suc n)"], assumption+) 
apply (frule_tac l = l in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply (simp add:cmp_def)
apply (simp add:Nset_def)
apply (simp add:Gch_bridge_def)
apply (erule conjE)+
apply (rule conjI)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" 
               "Nset (Suc n)"], assumption+)
apply (frule Nset_pre [of "f (Suc n)" "n"], assumption+)
apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). (cmp (transpos (f (Suc n)) (Suc n)) f) l \<in> Nset (Suc n)")
apply (frule isom_gch_unitsTr1_2 [of "E" "f" "n"], assumption+)
apply (frule isom_gch_unitsTr1_3 [of "E" "f" "n"], assumption+)
apply (frule Nset_injTr2 [of "n""cmp (transpos (f (Suc n)) (Suc n)) f"],
                                                   assumption+)
apply (rule ballI)
apply (simp add:cmp_def)
apply (frule_tac x = l in funcset_mem1 [of "Nset (Suc n)" 
                              "f" "Nset (Suc n)"], assumption+)
apply (frule Nsetn_sub_mem [of "f (Suc n)" "n"]) 
apply (rule_tac l = "f l" in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply (simp add:Nset_def)
apply (simp add:isom_gch_unitsTr1_4)
apply (simp add:isom_Gchains_def[of "n"])
apply (rule ballI)
apply (simp add:cmp_def)
apply (frule_tac l = i in  Nsetn_sub_mem [of _ "n"])
apply (frule_tac x = i in funcset_mem1 [of "Nset (Suc n)" "f" "Nset (Suc n)"], assumption+)
apply (subgoal_tac "(Suc n) \<in> Nset (Suc n)")
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" "Nset (Suc n)"], assumption+)
apply (frule Nset_le [of "f (Suc n)" "Suc n"])
apply (frule Nset_le [of "Suc n" "Suc n"])
apply (frule_tac k = "f i" in cmp_transpos1 [of "f (Suc n)" "Suc n" "Suc n"], assumption+) apply (simp add:cmp_def)
apply (thin_tac "transpos (f (Suc n)) (Suc n) (transpos (f (Suc n)) (Suc n) (f i)) = f i")
apply (simp add:isom_Gchains_def)
apply (simp add:Nset_def)
done

lemma isom_gch_unitsTr1_6:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f\<rbrakk>  \<Longrightarrow> Gchain (Suc n) g \<and>
 Gchain (Suc n) (cmp h (transpos (f (Suc n)) (Suc n))) \<and>
          Gch_bridge (Suc n) g (cmp h (transpos (f (Suc n)) (Suc n)))
           (cmp (transpos (f (Suc n)) (Suc n)) f)"
apply (erule conjE)+
apply simp
apply (simp add:Gch_bridge_def) apply (frule conj_1)
apply (frule conj_2) apply (fold Gch_bridge_def) apply (erule conjE)
apply (rule conjI)
apply (thin_tac "Gchain (Suc n) g")
apply (simp add:Gchain_def) apply (rule ballI)
apply (simp add:cmp_def)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" "Nset (Suc n)"], assumption+) 
apply (frule_tac l = l in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply blast apply (simp add:Nset_def)
apply (simp add:Gch_bridge_def)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (rule conjI)
apply (rule ballI)
apply (simp add:cmp_def)
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" 
               "Nset (Suc n)"], assumption+)
apply (frule_tac x = l in funcset_mem1 [of "Nset (Suc n)" "f" 
               "Nset (Suc n)"], assumption+)
apply (rule_tac l = "f l" in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"], assumption+)
apply (rule conjI)
apply (rule isom_gch_unitsTr1_3 [of "E" "f" "n"], assumption+)
apply (simp add:isom_Gchains_def) apply (rule ballI)
apply (simp add:cmp_def)
apply (frule_tac x = "Suc n" in funcset_mem1 [of "Nset (Suc n)" "f" 
               "Nset (Suc n)"], assumption+)
apply (frule Nset_le [of "f (Suc n)" "Suc n"])
apply (frule Nset_le [of "Suc n" "Suc n"])
apply (frule_tac k = "f i" in cmp_transpos1 [of "f (Suc n)" "Suc n" "Suc n"], assumption+) 
apply simp
apply (simp add:cmp_def)
apply (simp add:Nset_def)
done

lemma isom_gch_unitsTr1_7_0:"\<lbrakk>Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n)\<rbrakk>
 \<Longrightarrow> Gchain (Suc n) (cmp h (transpos k (Suc n)))"
apply (simp add:Gchain_def)
apply (rule ballI)
apply (simp add:cmp_def) 
apply (insert n_in_Nsetn [of "Suc n"])
apply (frule_tac l = l in transpos_mem [of "k" "Suc n" "Suc n"], assumption+)
apply auto
done

lemma isom_gch_unitsTr1_7_1:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n)\<rbrakk> \<Longrightarrow>{i. i \<in> Nset (Suc n) \<and> cmp h (transpos k (Suc n)) i \<cong> E} - {k , Suc n} = {i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k , Suc n}"
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply auto
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac x = x in transpos_id_1 [of "k" "Suc n" "Suc n"], assumption+)
apply (simp add:cmp_def) apply (simp add:Nset_def)
apply (simp add:cmp_def)
apply (frule_tac x = x in transpos_id_1 [of "k" "Suc n" "Suc n"], assumption+)
apply simp
apply (simp add:Nset_def)
done

lemma isom_gch_unitsTr1_7_2:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n);  h (Suc n) \<cong> E\<rbrakk> \<Longrightarrow>  cmp h (transpos k (Suc n)) k \<cong> E"
apply (simp add:cmp_def)
apply (subst transpos_ij_1 [of "k" "Suc n" "Suc n"], assumption+)
apply (simp add:Nset_def) apply assumption+
done

lemma isom_gch_unitsTr1_7_3:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); h k \<cong> E\<rbrakk> \<Longrightarrow> cmp h (transpos k (Suc n)) (Suc n) \<cong> E"
apply (simp add:cmp_def)
apply (subst transpos_ij_2 [of "k" "Suc n" "Suc n"], assumption+)
apply (simp add:Nset_def) apply (assumption+)
done

lemma isom_gch_unitsTr1_7_4:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); \<not> h (Suc n) \<cong> E\<rbrakk> \<Longrightarrow> \<not>  cmp h (transpos k (Suc n)) k \<cong> E"
apply (rule contrapos_pp, simp+)
apply (simp add:cmp_def)
apply (insert n_in_Nsetn [of "Suc n"])
apply (simp add: transpos_ij_1 [of "k" "Suc n" "Suc n"])
done

lemma isom_gch_unitsTr1_7_5:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); \<not> h k \<cong> E\<rbrakk> \<Longrightarrow> \<not>  cmp h (transpos k (Suc n)) (Suc n) \<cong> E"
apply (rule contrapos_pp, simp+)
apply (simp add:cmp_def)
apply (insert n_in_Nsetn [of "Suc n"])
apply (simp add:transpos_ij_2 [of "k" "Suc n" "Suc n"])
done

lemma isom_gch_unitsTr1_7_6:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); h (Suc n) \<cong> E; h k \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset (Suc n) \<and>  h i \<cong> E} = insert k (insert (Suc n) ({i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n}))" 
apply auto
apply (simp add:n_in_Nsetn)
done

lemma isom_gch_unitsTr1_7_7:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); h (Suc n) \<cong> E; \<not> h k \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset (Suc n) \<and>  h i \<cong> E} = insert (Suc n) ({i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n})" 
apply auto
apply (simp add:n_in_Nsetn)
done

lemma isom_gch_unitsTr1_7_8:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); \<not> h (Suc n) \<cong> E;  h k \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset (Suc n) \<and>  h i \<cong> E} = insert k ({i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n})"
apply auto
done

lemma isom_gch_unitsTr1_7_9:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n); \<not> h (Suc n) \<cong> E; \<not> h k \<cong> E\<rbrakk> \<Longrightarrow> {i. i \<in> Nset (Suc n) \<and>  h i \<cong> E} = {i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n}" 
apply auto
done

lemma isom_gch_unitsTr1_7:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<in> Nset (Suc n)\<rbrakk> \<Longrightarrow> card {i. i \<in> Nset (Suc n) \<and> cmp h (transpos k (Suc n)) i \<cong> E} =  card {i. i \<in> Nset (Suc n) \<and> h i \<cong> E}"
apply (frule isom_gch_unitsTr1_7_1 [of "E" "n" "h" "k"], assumption+)
apply (case_tac "h (Suc n) \<cong> E")
 apply (case_tac "h k \<cong> E")
 apply (subst isom_gch_unitsTr1_7_6 [of "E" "n" "h" "k"], assumption+)
 apply (frule isom_gch_unitsTr1_7_2 [of "E" "n" "h" "k"], assumption+)
 apply (frule isom_gch_unitsTr1_7_3 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_6 [of "E" "n" "cmp h (transpos k (Suc n))" "k"], assumption+)
apply (subst card_insert_disjoint) 
apply (subgoal_tac "(insert (Suc n) ({i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n})) \<subseteq> Nset (Suc n)")
apply (insert finite_Nset[of "Suc n"])
apply (rule finite_subset, assumption+)
apply (rule subsetI) apply (simp add:CollectI)
apply (simp add:Nset_def) apply blast
apply simp
apply (subst card_insert_disjoint)
 apply (subgoal_tac "({i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n}) \<subseteq> 
                                   Nset (Suc n)")
 apply (rule finite_subset, assumption+)
 apply (rule subsetI) apply (simp add:CollectI) apply simp
apply (subst card_insert_disjoint)
 apply (subgoal_tac "(insert (Suc n) ({i. i \<in> Nset (Suc n) \<and> cmp h (transpos k (Suc n)) i \<cong> E} - {k, Suc n})) \<subseteq> Nset (Suc n)")
 apply (rule finite_subset, assumption+)
 apply (rule subsetI) apply (simp add:CollectI) 
 apply (case_tac "x = Suc n") apply (simp add:Nset_def)
  apply (simp add:Nset_def)
apply simp
apply simp
apply (subst card_insert_disjoint)
 apply (subgoal_tac "({i. i \<in> Nset (Suc n) \<and> h i \<cong> E} - {k, Suc n}) \<subseteq> 
                                                            Nset (Suc n)")
 apply (rule finite_subset, assumption+)
 apply (rule subsetI) apply (simp add:CollectI) apply simp apply simp
apply (subst isom_gch_unitsTr1_7_7 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_5 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_2 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_8 [of "E" "n" "cmp h (transpos k (Suc n))" 
                                                     "k"], assumption+)
apply (subst card_insert_disjoint)
apply (rule isom_gch_units_transpTr4, assumption+) apply simp
apply (subst card_insert_disjoint)
apply (rule isom_gch_units_transpTr4, assumption+) apply simp apply simp
apply (case_tac "h k \<cong> E")
apply (subst isom_gch_unitsTr1_7_8 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_3 [of "E" "n" "h" "k"], assumption+) 
apply (frule isom_gch_unitsTr1_7_4 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_7 [of "E" "n" "cmp h (transpos k (Suc n))" 
                                                     "k"], assumption+)
apply (subst card_insert_disjoint)
apply (rule isom_gch_units_transpTr4, assumption+) apply simp
apply (subst card_insert_disjoint)
apply (rule isom_gch_units_transpTr4, assumption+) apply simp apply simp
apply (subst isom_gch_unitsTr1_7_9 [of "E" "n" "h" "k"], assumption+)
apply (frule_tac isom_gch_unitsTr1_7_4 [of "E" "n" "h" "k"], assumption+)
apply (frule_tac isom_gch_unitsTr1_7_5 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_9 [of "E" "n" " cmp h (transpos k (Suc n))" "k"], assumption+) apply simp
done

lemma isom_gch_unitsTr1:"Ugp E \<Longrightarrow> \<forall>g. \<forall>h. \<forall>f. Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f \<longrightarrow>  card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and> h i \<cong> E}"
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (rule card_eq)
 apply (simp add:Gch_bridge_def)
 apply (erule conjE)+
 apply (simp add:isom_Gchains_def Nset_def)
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
 apply simp
 apply (simp add:Gchain_def Nset_def)
apply (rule_tac F = "g 0" and G = "h 0" in isom_gch_unitsTr4 [of _ _ "E"],
                                                  assumption+)
apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
 apply simp
apply (simp add:Gchain_def Nset_def)
apply (frule_tac F = "g 0" and G = "h 0" in isomTr1, assumption+)
apply (rule_tac F = "h 0" and G = "g 0" in isom_gch_unitsTr4 [of _ _ "E"],
                                                  assumption+)
(***** n ******)
 apply (rule allI)+  apply (rule impI)
 (** n ** case f (Suc n) = Suc n **)
 apply (case_tac "f (Suc n) = Suc n") 
 apply (subgoal_tac "card {i. i \<in> Nset n \<and> g i \<cong> E} =
             card {i. i \<in> Nset n \<and> h i \<cong> E}")
 apply (thin_tac " \<forall>g h f.
             Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f \<longrightarrow>
             card {i. i \<in> Nset n \<and> g i \<cong> E} =
             card {i. i \<in> Nset n \<and> h i \<cong> E}")
apply (rule isom_tgch_unitsTr0, assumption+)
 apply (frule_tac n = n and g = g and h = h and f = f in 
            isom_gch_unitsTr1_1 [of "E"], assumption+)
 apply (rotate_tac -1) 
 apply (thin_tac "Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f")
 apply blast
  (**** n **** f (Suc n) \<noteq> Suc n ***) 
 apply (frule_tac n = n and g = g and h = h and f = f in isom_gch_unitsTr1_5 [of "E"], assumption+) 
apply (subgoal_tac "card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and>  (cmp h (transpos (f (Suc n)) (Suc n))) i \<cong> E}")
prefer 2 apply blast
 apply (thin_tac "\<forall>g h f.
             Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f \<longrightarrow>
             card {i. i \<in> Nset n \<and> g i \<cong> E} =
             card {i. i \<in> Nset n \<and> h i \<cong> E}")
 apply (thin_tac "Gchain n g \<and>
          Gchain n (cmp h (transpos (f (Suc n)) (Suc n))) \<and>
          Gch_bridge n g (cmp h (transpos (f (Suc n)) (Suc n)))
           (cmp (transpos (f (Suc n)) (Suc n)) f)")
apply (subgoal_tac "cmp (transpos (f (Suc n)) (Suc n)) f (Suc n) = Suc n")
apply (frule_tac n = n and g = g and h = "cmp h (transpos (f (Suc n)) (Suc n))" and f = "cmp (transpos (f (Suc n)) (Suc n)) f"  in  isom_tgch_unitsTr0 [of "E"], assumption+)
apply (rule isom_gch_unitsTr1_6, assumption+)
 apply (thin_tac "card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and> cmp h (transpos (f (Suc n)) (Suc n)) i \<cong> E}")
prefer 2 
 apply (erule conjE)+
 apply (simp add:Gch_bridge_def) apply (erule conjE)+
 apply (rule isom_gch_unitsTr1_2, assumption+)
apply simp
apply (erule conjE)+
apply (rule isom_gch_unitsTr1_7, assumption+)
apply (simp add:Gch_bridge_def)
 apply (frule conj_1) apply (fold Gch_bridge_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply auto
 apply (simp add:Nset_def)
done
 
lemma isom_gch_units:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; Gch_bridge n g h f\<rbrakk> \<Longrightarrow>  card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and> h i \<cong> E}"
apply (simp add:isom_gch_unitsTr1)
done

lemma isom_gch_units_1:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; \<exists>f. Gch_bridge n g h f\<rbrakk> \<Longrightarrow>  card {i. i \<in> Nset n \<and> g i \<cong> E} = card {i. i \<in> Nset n \<and> h i \<cong> E}"
apply (auto del:equalityI)
apply (simp add:isom_gch_units)
done

section "19. Jordan Hoelder theorem"

subsection "rfn_tools. tools to treat refinement of a cmpser, rtos"

lemma rfn_tool1:"\<lbrakk> 0 < (r::nat); (k::nat) = i * r + j; j < r \<rbrakk> 
                                                  \<Longrightarrow> (k div r) = i"  
proof -
 assume p1: "0 < r" and p2: "k = i * r + j" and p3: "j < r"
 from p1 and p2 have q1: "(j + i * r) div r = i + j div r" 
 apply (simp add:div_mult_self1 [of "r" "j" "i" ]) done
 from p1 and p3 have q2: "j div r = 0"
  apply (simp add:div_if) done
 from q1 and q2 have q3:"(j + i * r) div r = i"
  apply simp done
 from q3 have q4: "(i * r + j) div r = i" apply (simp add:add_commute)
  done
 from p2 and q4 show ?thesis
  apply simp 
 done
qed

lemma rfn_tool1_1:"\<lbrakk> 0 < (r::nat); j < r \<rbrakk> 
                             \<Longrightarrow> (i * r + j) div r = i"
apply (rule rfn_tool1 [of "r" "i * r + j" "i" "j"], assumption+)  
apply simp+
done

lemma rfn_tool2:"(a::nat) < s \<Longrightarrow> a \<le> s - Suc 0"
 apply (rule less_le_diff) apply simp+
done

lemma rfn_tool3:"(0::nat) \<le> m \<Longrightarrow> (m + n) - n = m"
apply auto
done

lemma rfn_tool11:"\<lbrakk>0 < b; (a::nat) \<le> b - Suc 0\<rbrakk> \<Longrightarrow> a < b"
 apply (frule le_less_trans [of "a" "b - Suc 0" "b"])
 apply simp+
done

lemma  rfn_tool12:"\<lbrakk>0 < (s::nat); (i::nat) mod s = s - 1 \<rbrakk> \<Longrightarrow>
                     Suc (i div s) = (Suc i) div s "
proof -
 assume p1:"0 < s" and p2:"i mod s = s - 1"
 have q1:"i div s * s + i mod s = i"
   apply (insert mod_div_equality [of "i" "s"]) 
   apply simp done
 have q2:"Suc (i div s * s + i mod s) = i div s * s + Suc (i mod s)"
  apply (insert add_Suc_right [THEN sym, of "i div s * s" "i mod s"])
  apply assumption done
 from p1 and p2 and q2 have q3:"Suc (i div s * s + i mod s) = i div s * s + s"
  apply simp done
 from q3 have q4:"Suc (i div s * s + i mod s) = Suc (i div s) * s "
  apply simp done
 from p1 and q1 and q4 show ?thesis  
 apply auto
 done
qed

lemma  rfn_tool12_1:"\<lbrakk>0 < (s::nat); (l::nat) mod s < s - 1 \<rbrakk> \<Longrightarrow>
                     Suc (l mod s) = (Suc l) mod s "
apply (insert mod_div_equality [of "l" "s"])
apply (insert add_Suc_right [THEN sym, of "l div s * s" "l mod s"])
apply (insert mod_mult_self1  [of "Suc (l mod s)" "l div s" "s"])
apply (frule Suc_mono [of "l mod s" "s - 1"]) apply simp
done

lemma  rfn_tool12_2:"\<lbrakk>0 < (s::nat); (i::nat) mod s = s - Suc 0\<rbrakk> \<Longrightarrow>
                                               (Suc i) mod s = 0" 
apply (insert mod_div_equality [THEN sym, of "i" "s"])
apply (insert add_Suc_right [THEN sym, of "i div s * s" "i mod s"])
apply auto
done

lemma rfn_tool13:"\<lbrakk> (0::nat) < r; a = b \<rbrakk> \<Longrightarrow> a mod r = b mod r"
apply simp
done

lemma rfn_tool13_1:"\<lbrakk> (0::nat) < r; a = b \<rbrakk> \<Longrightarrow> a div r = b div r"
apply simp
done

lemma div_Tr1:"\<lbrakk> (0::nat) < r; 0 < s; l \<le> s * r\<rbrakk> \<Longrightarrow> l div s \<le> r"
 apply (frule_tac m = l and n = "s * r" and k = s in div_le_mono)
 apply simp
done

lemma div_Tr2:"\<lbrakk>(0::nat) < r; 0 < s; l < s * r\<rbrakk> \<Longrightarrow> l div s \<le> r - Suc 0"
apply (rule contrapos_pp, simp+)
apply (simp add:le_def [of "l div s" "r - Suc 0"])
apply (frule Suc_leI [of "r - Suc 0" "l div s"])
apply simp
apply (frule less_imp_le [of "l" "s * r"])
apply (frule div_le_mono [of "l" "s * r" "s"]) apply simp
apply (insert mod_div_equality [THEN sym, of "l" "s"])
apply simp apply (simp add:mult_commute [of "r" "s"])
done

lemma div_Tr3_1:"\<lbrakk>(0::nat) < r; 0 < s; l mod s = s - 1\<rbrakk> \<Longrightarrow>  Suc l div s = Suc (l div s)"
apply (frule rfn_tool12 [of "s" "l"], assumption+)
 apply (rotate_tac -1) apply simp
done

lemma div_Tr3_2:"\<lbrakk>(0::nat) < r; 0 < s; l mod s < s - 1\<rbrakk> \<Longrightarrow> l div s = Suc l div s"
apply (frule Suc_mono [of "l mod s" "s - 1"]) apply simp
apply (insert mod_div_equality [of "l" "s"])
apply (insert add_Suc_right [THEN sym, of "l div s * s" "l mod s"])
apply (subgoal_tac "0 < s")
apply (frule rfn_tool13_1 [of "s" "Suc (l div s * s + l mod s)" "l div s * s + Suc (l mod s)"], assumption+)
apply (frule div_mult_self1 [of "s" "Suc (l mod s)" "l div s"])
apply (subgoal_tac "Suc (l mod s) div s = 0") apply simp
apply (simp add: div_if [of "s" "Suc (l mod s)"])
apply simp
done

constdefs 
 rtos::"[nat, nat] \<Rightarrow> (nat \<Rightarrow> nat)"
  "rtos r s i == if i < r * s then (i mod s) * r + i div s else r * s"
 
lemma rtos_hom0:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<in> Nset (r * s - Suc 0)\<rbrakk> \<Longrightarrow>
   i div s < r" 
apply (frule div_Tr2 [of "r" "s" "i"], assumption+)
apply (simp add:Nset_def)
apply (simp add:mult_commute [of "r" "s"])
apply (rule le_less_trans, assumption+) apply simp 
apply (rule le_less_trans, assumption+) apply simp
done

lemma rtos_hom1:"\<lbrakk>(0::nat) < r; 0 < s; l \<in> Nset (r * s - Suc 0)\<rbrakk> \<Longrightarrow> 
 (rtos r s) l \<in> Nset (s * r - Suc 0)"
apply (simp add:rtos_def)
apply (frule Nset_le [of "l" "r * s - Suc 0"])
apply (frule le_less_trans [of "l" "r * s - Suc 0" "r * s"])
 apply simp
 apply simp 
apply (frule mod_less_divisor [of "s" "l"])
 apply (frule less_le_diff [of "l mod s" "s"])
 apply (frule_tac i = "l mod s" and j = "s - Suc 0" and k = r and l = r in mult_le_mono) apply simp
 apply (frule_tac i = "l mod s * r" and j = "(s - Suc 0) * r" and k = "l div s" and l = "r - Suc 0" in add_le_mono)
 apply (rule div_Tr2, assumption+) apply (simp add:mult_commute)
 apply (simp add:Nset_def) apply (simp add:diff_mult_distrib)
done

lemma rtos_hom2:"\<lbrakk>(0::nat) < r; (0::nat) < s; l \<in> Nset (r * s - Suc 0)\<rbrakk> \<Longrightarrow> 
 rtos r s l \<in> Nset (r * s - Suc 0)"
apply (insert  rtos_hom1 [of "r" "s"]) apply simp
apply (simp add:mult_commute)
done

lemma rtos_hom3:"\<lbrakk>(0::nat) < r; 0 < s; i \<in> Nset (r * s - Suc 0) \<rbrakk> \<Longrightarrow>
  (rtos r s i div r) = i mod s"
apply (simp add:rtos_def)
 apply (frule Nset_le [of "i" "r * s - Suc 0"])
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"])
 apply simp apply simp
apply (subst add_commute)
 apply (frule div_mult_self1 [of "r" "i div s" "i mod s"])
 apply (frule div_Tr2 [of "r" "s" "i"], assumption+) 
 apply (simp add:mult_commute)
apply (frule le_less_trans [of "i div s" "r - Suc 0" "r"])
 apply simp
 apply (simp add:div_if [of "r" "i div s"])
done

lemma rtos_hom3_1:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<in> Nset (r * s - Suc 0) \<rbrakk> \<Longrightarrow>
  (rtos r s i mod  r) = i div s"
apply (simp add:rtos_def)
apply (simp add:Nset_def)
apply (simp add:rfn_tool11 [of "r * s" "i"])
 apply (frule rtos_hom0 [of "r" "s" "i"], assumption+)
 apply (simp add:mem_of_Nset)
 apply (subst add_commute)
 apply (subst mod_mult_self1 [of "i div s" "i mod s" "r"])
apply (subst mod_less, assumption+) apply simp 
done

lemma rtos_hom5:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<in> Nset (r *s - Suc 0); 
i div s = r - Suc 0 \<rbrakk> \<Longrightarrow> Suc (rtos r s i) div r = Suc (i mod s)"
apply (frule Nset_le [of "i" "r * s - Suc 0"])
apply (subgoal_tac "0 < r * s")
apply (frule rfn_tool11 [of "r * s" "i"], assumption+)
apply (simp add:rtos_def) apply (simp add:div_add_self2)
apply simp
done

lemma rtos_hom7:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<in> Nset (r * s - Suc 0); 
i div s = r - Suc 0 \<rbrakk> \<Longrightarrow> Suc (rtos r s i) mod r = 0"
apply (frule rtos_hom0 [of "r" "s" "i"], assumption+)
apply (simp add: rtos_def) 
apply (frule Nset_le [of "i" "r * s - Suc 0"])
apply (subgoal_tac "0 < r * s")
apply (simp add:rfn_tool11 [of "r * s" "i"])
apply simp
done

lemma rtos_inj:"\<lbrakk> (0::nat) < r; (0::nat) < s \<rbrakk> \<Longrightarrow> 
                   inj_on (rtos r s) (Nset (r * s - Suc 0))"
apply (simp add:inj_on_def) 
apply (rule ballI)+ apply (rule impI) 
apply (frule_tac x = x in Nset_le [of _ "r * s - Suc 0"])
apply (frule_tac x = y in Nset_le [of _ "r * s - Suc 0"])
apply (subgoal_tac "0 < r * s") 
 apply (frule_tac a = x in rfn_tool11 [of "r * s"], assumption+)
 apply (frule_tac a = y in rfn_tool11 [of "r * s"], assumption+)
 apply (subgoal_tac "x mod s = y mod s")
 apply (thin_tac "x \<le> r * s - Suc 0") apply (thin_tac " y \<le> r * s - Suc 0")
apply (simp add:rtos_def)
apply (subgoal_tac "x div s * s + x mod s = x") apply simp
 apply (rule mod_div_equality)
 apply (frule_tac i = x in rtos_hom0 [of "r" "s" _], assumption+)
 apply (frule_tac i = y in rtos_hom0 [of "r" "s" _], assumption+) 
 apply (thin_tac "x \<le> r * s - Suc 0")
 apply (thin_tac "y \<le> r * s - Suc 0")
apply (simp add:rtos_def) 
 apply (subgoal_tac "0 < r") 
 apply (frule_tac a = "x mod s * r + x div s" and  b = "y mod s * r + y div s" in rfn_tool13_1 [of "r"])
 apply assumption 
 apply (thin_tac "x mod s * r + x div s = y mod s * r + y div s")
 apply (frule_tac j = "x div s" and i = "x mod s" in rfn_tool1_1 [of "r"],
                                          assumption+)
  apply (frule_tac j = "y div s" and i = "y mod s" in rfn_tool1_1 [of "r"],
                                          assumption+)
 apply simp
apply simp+
done


lemma rtos_rs_Tr1:"\<lbrakk>(0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow> rtos r s (r * s) = r * s"
apply (simp add:rtos_def)
done

lemma rtos_rs_Tr2:"\<lbrakk>(0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow> \<forall>l\<in>Nset (r * s). rtos r s l \<in> Nset (r * s)"
apply (rule ballI)
 apply (case_tac "l = r * s") apply (simp add:rtos_rs_Tr1 Nset_def)
 apply (simp add:Nset_def) apply (frule le_imp_less_or_eq) 
 apply (thin_tac "l \<le> r * s") apply simp
 apply (subgoal_tac "0 < r * s")
 apply (frule_tac  r = r and s = s and l = l in rtos_hom2, assumption+)
 apply (simp add:Nset_def) apply (rule less_le_diff)
 apply simp 
apply (frule Nset_le)
 apply (frule_tac i = "rtos r s l" in le_less_trans [of _ "r * s - Suc 0" "r * s"]) apply simp
 apply (simp add:less_imp_le)
apply simp
done
    
lemma rtos_rs_Tr3:"\<lbrakk>(0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow> inj_on (rtos r s) (Nset (r * s))"
apply (frule rtos_inj [of "r" "s"], assumption+)
apply (simp add:inj_on_def [of _ "Nset (r * s)"])
 apply (rule ballI)+ apply (rule impI)
 apply (case_tac "x = r * s") apply simp
 apply (rule contrapos_pp, simp+)apply (frule not_sym)
 apply (thin_tac "r * s \<noteq> y")
 apply (frule_tac x = y in Nset_le [of _ "r * s"])
 apply (frule_tac m = y in noteq_le_less [of _ "r * s"], assumption+)
 apply (frule_tac x = y in less_le_diff [of _ "r * s"])
 apply (frule_tac x = y in mem_of_Nset [of _ "r * s - Suc 0"]) 
 apply (frule_tac l = y in rtos_hom2 [of "r" "s"], assumption+)
apply (frule sym) apply (thin_tac "rtos r s (r * s) = rtos r s y")
apply (simp add:rtos_rs_Tr1)
 apply (frule Nset_le [of "r * s" "r * s - Suc 0"])
 apply (subgoal_tac "0 < r * s")
 apply (frule le_less_trans [of "r * s" "r * s - Suc 0" "r * s"])
 apply simp apply simp apply simp
apply (frule_tac x = x and n = "r * s" in Nset_le)
apply (case_tac "y = r * s") apply simp
 apply (frule_tac m = x and n = "r * s" in noteq_le_less, assumption+)
  apply (frule_tac x = x in less_le_diff [of _ "r * s"])
 apply (frule_tac x = x in mem_of_Nset [of _ "r * s - Suc 0"]) 
 apply (frule_tac l = x in rtos_hom2 [of "r" "s"], assumption+)
 apply simp
 apply (simp add:rtos_rs_Tr1)
 apply (frule Nset_le [of "r * s" "r * s - Suc 0"])
 apply (subgoal_tac "0 < r * s")
 apply (frule le_less_trans [of "r * s" "r * s - Suc 0" "r * s"])
 apply simp apply simp apply simp
apply (frule_tac x = x and n = "r * s" in Nset_le)
apply (frule_tac x = y and n = "r * s" in Nset_le)
 apply (frule_tac m = x in noteq_le_less [of _ "r * s"], assumption+)
 apply (frule_tac m = y in noteq_le_less [of _ "r * s"], assumption+)
 apply (frule_tac x = x in less_le_diff [of _ "r * s"])
 apply (frule_tac x = y in less_le_diff [of _ "r * s"])
 apply (frule_tac x = x in mem_of_Nset [of _ "r * s - Suc 0"])
 apply (frule_tac x = y in mem_of_Nset [of _ "r * s - Suc 0"])
 apply (simp add:inj_on_def)
done


lemma Qw_cmpser:"\<lbrakk>group G; w_cmpser G (Suc n) f \<rbrakk> \<Longrightarrow> 
                               Gchain n (Qw_cmpser G f)"
apply (simp add:Gchain_def)
apply (rule ballI)
 apply (simp  add:Qw_cmpser_def)
 apply (simp add:w_cmpser_def)
 apply (erule conjE)
 apply (simp add:d_gchain_def) apply (erule conjE)
 apply (subgoal_tac "group (grp G (f l))")
 apply (subgoal_tac "f (Suc l) \<lhd> grp G (f l)")
 apply (simp add:Qgrp)
 apply simp+
apply (rule subggrp, assumption+)
 apply (simp add:Nset_def)
done

constdefs
 wcsr_rfns::"[('a, 'm) GroupType_scheme, nat, nat \<Rightarrow> 'a set, nat] \<Rightarrow> 
                                 (nat \<Rightarrow> 'a set) set"
  "wcsr_rfns G r f s  == {h. tw_cmpser G (s * r) h \<and> 
                                 (\<forall>i \<in> (Nset r). h (i * s) = f i)}"
      (** where f \<in> tw_cmpser G r **)
  (**  0-+-+-2-+-+-4-+-+-6  h 
      f 0   f 1   f 2   f 3  **)

 trivial_rfn::"[('a, 'm) GroupType_scheme, nat, nat \<Rightarrow> 'a set, nat] \<Rightarrow> 
                                                          (nat \<Rightarrow> 'a set)"
   "trivial_rfn G r f s k == if k < (s * r) then f (k div s) else f r"

lemma rfn_tool8:"\<lbrakk>group G;compseries G r f; 0 < r\<rbrakk> \<Longrightarrow> d_gchain G r f" 
apply (simp add:compseries_def tW_cmpser_def) 
apply (erule conjE)+
apply (simp add:tD_gchain_def) apply (erule conjE)+
apply (simp add:D_gchain_is_d_gchain)
done

lemma rfn_tool16:"\<lbrakk>group G; 0 < r; 0 < s;i \<in> Nset (s * r - Suc 0); f (i div s) \<guillemotleft> G; f (Suc (i div s)) \<lhd> grp G (f (i div s)); f (i div s) \<inter> g (s - Suc 0) \<guillemotleft> grp G (f (i div s))\<rbrakk>  \<Longrightarrow> f (Suc (i div s)) \<lhd> grp G ((f (Suc (i div s)) \<bullet>\<^sub>G (f (i div s) \<inter> g (s - Suc 0))))"
apply (rule ZassenhausTr4_1 [of "G" "f (i div s)" "f (Suc (i div s))" "g (s - Suc 0)"], assumption+)
done

text{* Show existence of the trivial refinement. This is not necessary
to prove JHS *}

lemma rfn_tool30:"\<lbrakk>0 < r; 0 < s; l div s * s + s < s * r\<rbrakk> 
                \<Longrightarrow> Suc (l div s) < r"
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "r \<le> Suc (l div s)") 
apply (thin_tac "\<not> Suc (l div s) < r")
apply (subgoal_tac "s * r \<le> Suc (l div s) * s") 
apply (simp add: add_commute)
 apply (thin_tac "l div s * s + s < s * r")
 apply (insert mult_commute [of "s" "r"])
 apply (insert mult_le_mono [of "r" "Suc (l div s)" "s" "s"]) 
 apply simp
 apply (simp add:mult_commute)+
done

lemma simple_grouptr0:"\<lbrakk> group G; H \<guillemotleft> G; K \<lhd> G; K \<subseteq> H; simple_group (G / K)\<rbrakk>
  \<Longrightarrow> H = carrier G \<or> H = K" 
apply (simp add:simple_group_def)
apply (erule conjE)
apply (frule subg_Qsubg [of "G" "H" "K"], assumption+)
apply (subgoal_tac "carrier ((grp G H) / K) \<in> {N. N \<guillemotleft> G / K}")
prefer 2
 apply (thin_tac "{N. N \<guillemotleft> G / K} = {carrier (G / K), {1\<^sub>(G / K)}}")
 apply simp
apply simp
apply (thin_tac "{N. N \<guillemotleft> G / K} = {carrier (G / K), {1\<^sub>(G / K)}}")
apply (thin_tac "carrier (grp G H / K) \<guillemotleft> G / K")
apply (simp add:Pj_im_subg [THEN sym, of "G" "H" "K"])
apply (frule Pj_gsurjec [of "G" "K"], assumption+)
apply (simp add:gsurjec_def) apply (erule conjE)
apply (simp add:surj_to_def) apply (rotate_tac -1)
apply (frule sym) apply (thin_tac "Pj G K ` carrier G = carrier (G / K)")
apply simp
apply (thin_tac "carrier (G / K) = Pj G K ` carrier G")
apply (simp add:gHom_def) apply (erule conjE)+
 apply (thin_tac "Pj G K \<in> extensional (carrier G)")
 apply (thin_tac "\<forall>x\<in>carrier G.
          \<forall>y\<in>carrier G. Pj G K ( x \<cdot>\<^sub>G y) =  Pj G K x \<cdot>\<^sub>(G / K) (Pj G K y)")
apply (case_tac "Pj G K ` H = Pj G K ` carrier G")
apply (thin_tac " Pj G K ` H = Pj G K ` carrier G \<or> Pj G K ` H = {1\<^sub>(G / K)}")
apply (subgoal_tac "H = carrier G") apply simp
prefer 2 apply simp apply (subgoal_tac "H = K") apply simp
apply (thin_tac "{1\<^sub>(G / K)} \<noteq> Pj G K ` carrier G")
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:qgrp_def) apply (fold qgrp_def)
 apply (frule_tac  x = x in Pj_mem [of "G" "K"], assumption+)
 apply (simp add:subg_subset1)
 apply (frule_tac x = x in  elem_in_image2 [of "Pj G K" "carrier G" 
 "set_r_cos G K" "H"])
 apply (simp add:subg_subset) apply assumption
 apply simp
 apply (frule nmlSubgTr0 [of "G" "K"], assumption+)
 apply (rule r_coset_fixed, assumption+) 
 apply (simp add:subg_subset1) apply assumption+
apply (rule equalityI)
 apply (simp add:subg_subset)
 apply (rule subsetI)
 apply (frule_tac a = x in  mem_in_image [of "Pj G K" "carrier G" "carrier (G / K)"], assumption+)
 apply (frule sym) apply (thin_tac "Pj G K ` H = Pj G K ` carrier G")
 apply simp apply (thin_tac "Pj G K ` carrier G = Pj G K ` H")
 apply (thin_tac "Pj G K \<in> carrier G \<rightarrow> carrier (G / K)")
 apply (simp add:image_def)
 apply (auto del:equalityI)
 apply (frule_tac h = xa in subg_subset1 [of "G" "H"], assumption+)
 apply (simp add:Pj_mem)
 apply (frule nmlSubgTr0[of "G" "K"], assumption+)
 apply (frule_tac a = x in aInR_cos [of "G" "K"], assumption+)
 apply simp
 apply (thin_tac "K\<^sub>G x = K\<^sub>G xa")
apply (simp add:r_coset_def)
apply auto
 apply (frule_tac c = h in subsetD [of "K" "H"], assumption+)
 apply (simp add:subg_tOp_closed)
done

lemma compser_simple:"\<lbrakk>0 < n; group G; compseries G n f; i \<in> Nset (n - 1)\<rbrakk>
       \<Longrightarrow> simple_group ((grp G (f i)) / f (Suc i))"
apply (simp add:compseries_def)
done

lemma compser_nsubg:"\<lbrakk>0 < n; group G; compseries G n f; i \<in> Nset (n - 1)\<rbrakk>
          \<Longrightarrow> f (Suc i) \<lhd> grp G (f i)"
apply (simp add:compseries_def tW_cmpser_def)
done

lemma compseriesTr5:"\<lbrakk>0 < n; group G; compseries G n f; i \<in> Nset (n - Suc 0)\<rbrakk>
          \<Longrightarrow> (f (Suc i)) \<subseteq>  (f i)"
apply (frule compser_nsubg, assumption+) apply simp+
apply (frule compseriesTr0 [of "G" "n" "f" "i"], assumption+)
apply (simp add:Nset_def) 
apply (frule le_less_trans [of "i" "n - Suc 0" "n"]) apply simp
apply (simp add:less_imp_le)
apply (frule subggrp [of "G" "f i"], assumption+)
apply (frule nsubg_subset [of "grp G (f i)" "f (Suc i)"], assumption+)
apply (simp add:grp_carrier)
done

lemma refine_cmpserTr0:"\<lbrakk>0 < n; group G; compseries G n f; i \<in> Nset (n - 1);
 H \<guillemotleft> G;  f (Suc i) \<subseteq> H \<and> H \<subseteq> f i\<rbrakk> \<Longrightarrow> H = f (Suc i) \<or> H = f i"
apply (frule compseriesTr0 [of "G" "n" "f" "i"], assumption+)
 apply (simp add:Nset_def)
 apply (frule le_less_trans [of "i" "n - Suc 0" "n"]) apply simp
 apply (simp add:less_imp_le)
 apply (frule subggrp [of "G" "f i"], assumption+) 
 apply (erule conjE)
 apply (frule compser_nsubg [of "n" "G" "f" "i"], assumption+)
 apply (frule subg_in_subg [of "G" "H" "f i"], assumption+)
 apply (frule simple_grouptr0 [of "grp G (f i)" "H" "f (Suc i)"], assumption+)
 apply (simp add:compser_simple)
 apply (simp add:grp_carrier)
apply (auto del:equalityI)
done

lemma div_Tr4:"\<lbrakk> (0::nat) < r; 0 < s; j < s * r \<rbrakk> \<Longrightarrow> j div s * s + s \<le> r * s"
apply (frule div_Tr2 [of "r" "s" "j"], assumption+)
apply (frule mult_le_mono [of "j div s" "r - Suc 0" "s" "s"])
 apply simp
 apply (frule add_le_mono [of "j div s * s" "(r - Suc 0) * s" "s" "s"])
 apply simp
 apply (thin_tac "j div s * s \<le> (r - Suc 0) * s")
 apply (subgoal_tac "(r - Suc 0) * s + s = r * s") apply simp
apply (simp add:diff_mult_distrib)
done

lemma compseries_is_tW_cmpser:"\<lbrakk>0 < r; group G; compseries G r f\<rbrakk> \<Longrightarrow>
        tW_cmpser G r f"
apply (simp add:compseries_def)
done

lemma compseries_is_td_gchain:"\<lbrakk>0 < r; group G; compseries G r f\<rbrakk> \<Longrightarrow>
        td_gchain G r f"
apply (frule compseries_is_tW_cmpser, assumption+)
apply (simp add:tW_cmpser_def) apply (erule conjE)
apply (thin_tac "\<forall>i\<in>Nset (r - Suc 0). f (Suc i) \<lhd> grp G (f i)")
apply (simp add:tD_gchain_def) apply (erule conjE)
apply (frule D_gchain_is_d_gchain, assumption+)
apply (simp add:td_gchain_def)
done

lemma compseries_is_D_gchain:"\<lbrakk>0 < r; group G; compseries G r f\<rbrakk> \<Longrightarrow>
             D_gchain G r f"
apply (frule compseriesTr1, assumption+)
apply (frule tW_cmpser_is_W_cmpser, assumption+)
apply (frule W_cmpser_is_D_gchain, assumption+)
done

lemma divTr5:"\<lbrakk>0< r; 0 < s; l < (r * s)\<rbrakk>  \<Longrightarrow> l div s * s \<le> l \<and> l  \<le> (Suc (l div s)) * s"
apply (insert mod_div_equality [THEN sym, of "l" "s"])
apply (rule conjI)
apply (insert le_add1 [of "l div s * s" "l mod s"])
apply simp
apply (frule mod_less_divisor [of "s" "l"])
 apply (frule less_imp_le [of "l mod s" "s"]) 
 apply (insert self_le [of "l div s * s"])
 apply (frule add_le_mono [of "l div s * s" "l div s * s" "l mod s" "s"])
 apply assumption+
apply (thin_tac "l div s * s \<le> l div s * s + l mod s")
apply (thin_tac "l div s * s \<le> l div s * s")
apply simp
done  

lemma rfn_compseries_iMTr1:"\<lbrakk>0 < r; 0 < s; group G; compseries G r f; 
h \<in> wcsr_rfns G r f s\<rbrakk> \<Longrightarrow>  f ` (Nset r) \<subseteq>  h ` (Nset (s * r))"
apply (simp add:wcsr_rfns_def) apply (rule subsetI)
apply (simp add:image_def)
apply (auto del:equalityI)
apply (frule_tac x = xa and n = r in Nset_le) 
apply (frule_tac i = xa in mult_le_mono [of _ "r" "s" "s"])
apply simp
apply (frule_tac x = "xa * s" and n = "r * s" in mem_of_Nset)
apply (simp add:mult_commute [of "r" "s"])
apply blast
done

lemma rfn_compseries_iMTr2:"\<lbrakk>0 < r; 0 < s; xa < s * r \<rbrakk> \<Longrightarrow>
         xa div s * s \<le> r * s \<and> Suc (xa div s) * s \<le> r * s"
apply (frule div_Tr1 [of "r" "s" "xa"], assumption+)
 apply (simp add:less_imp_le)
apply (rule conjI)
 apply (simp add:mult_le_mono [of "xa div s" "r" "s" "s"])
apply (thin_tac "xa div s \<le> r")
apply (frule div_Tr2[of "r" "s" "xa"], assumption+)
 apply (thin_tac "xa < s * r")
 apply (frule le_less_trans [of "xa div s" "r - Suc 0" "r"])
 apply simp 
 apply (frule Suc_leI [of "xa div s" "r"])
 apply (rule mult_le_mono [of "Suc (xa div s)" "r" "s" "s"], assumption+)
apply simp
done

lemma rfn_compseries_iMTr3:"\<lbrakk>0 < r; 0 < s; group G; compseries G r f; j \<in> Nset r; \<forall>i\<in>Nset r. h (i * s) = f i\<rbrakk> \<Longrightarrow>  h (j * s) = f j"
apply blast
done

lemma rfn_compseries_iM:"\<lbrakk>0< r; 0 < s; group G; compseries G r f; h \<in> wcsr_rfns G r f s\<rbrakk>  \<Longrightarrow> card (h `(Nset (s * r))) = r + 1"
apply (frule compseries_is_D_gchain, assumption+)
apply (frule D_gchain1, assumption+)
apply (subgoal_tac "h ` Nset (s * r) = f ` (Nset r)") apply simp
apply (subst card_image) 
  apply assumption
 apply (simp add:card_Nset)
apply (rule equalityI)
prefer 2 apply (rule rfn_compseries_iMTr1, assumption+)
apply (rule subsetI)
 apply (simp add:image_def)
 apply (auto del:equalityI)

apply (frule_tac x = xa and n = "s * r" in Nset_le)
apply (case_tac "xa = s * r") apply simp 
apply (simp add:wcsr_rfns_def) apply (erule conjE)
 apply (subgoal_tac "h (r * s) = f r")

apply (subst mult_commute [of "s" "r"])
apply (insert self_le [of "r"])
 apply (frule mem_of_Nset [of "r" "r"]) apply blast
 apply (frule mem_of_Nset [of "r" "r"]) apply blast   
apply (simp add:wcsr_rfns_def) apply (erule conjE)
apply (frule tw_cmpser_is_w_cmpser, assumption+)
apply (frule w_cmpser_is_d_gchain, assumption+)
apply (frule_tac m = xa and n = "s * r" in noteq_le_less, assumption+)
 apply (frule_tac l = xa in div_Tr1 [of "r" "s"], assumption+)
 apply (frule_tac x = "xa div s" in mem_of_Nset [of _ "r"])
 apply (frule_tac l = xa in div_Tr2[of "r" "s"], assumption+)
 apply (frule_tac i = "xa div s" in le_less_trans [of _ "r - Suc 0" "r"])
 apply simp
 apply (frule_tac m = "xa div s" in Suc_leI [of _ "r"])
 apply (frule_tac x = "Suc (xa div s)" in mem_of_Nset [of _ "r"])
 apply (thin_tac "xa \<le> s * r") apply (thin_tac "xa \<noteq> s * r")
 apply (frule_tac l = xa in divTr5 [of "r" "s"], assumption+)
 apply (simp add:mult_commute)
 apply (frule_tac xa = xa in rfn_compseries_iMTr2 [of "r" "s"], assumption+)
 apply (rotate_tac -1)
 apply (erule conjE)
 apply (frule_tac x = "xa div s * s" in mem_of_Nset [of _ "r * s"])
 apply (frule_tac x = "Suc (xa div s) * s" in mem_of_Nset [of _ "r * s"])
 apply (thin_tac "xa div s * s \<le> r * s")
 apply (thin_tac "Suc (xa div s) * s \<le> r * s")
 apply (erule conjE)
apply (frule_tac i = "xa div s * s" and j = xa in d_gchainTr2 [of "G" "r* s" "h"]) 
apply (simp add:wcsr_rfns_def)
 apply (simp add:mult_commute) apply assumption apply (simp add:mult_commute)
 apply assumption
 apply (thin_tac " inj_on f (Nset r)") 
 apply (thin_tac "xa div s \<le> r - Suc 0")
 apply (thin_tac "xa div s < r") apply (thin_tac "xa div s \<le> r")
apply (frule_tac i = xa and j = "Suc (xa div s) * s" in 
               d_gchainTr2 [of "G" "r* s" "h"])
 apply simp apply (simp add:mult_commute) apply (simp add:mult_commute)
 apply assumption+
 apply (frule_tac j = "xa div s" in rfn_compseries_iMTr3 
                          [of "r" "s" "G" "f"], assumption+)
 apply (frule_tac j = "Suc (xa div s)" in rfn_compseries_iMTr3 
                          [of "r" "s" "G" "f"], assumption+)
 apply simp
 apply (subgoal_tac "0 < r")
 apply (frule_tac i = "xa div s" and H = "h xa" in refine_cmpserTr0 [of "r" "G" "f"], assumption+)
 apply (simp add:Nset_def)
 apply (subgoal_tac "0 < r")
 apply (rule div_Tr2 [of "r" "s"], assumption+)
 apply simp
 apply (simp add:d_gchain_def Nset_def)
 apply simp
prefer 2 apply simp
 apply (case_tac "h xa = f (Suc (xa div s))")
 apply blast
 apply blast
done

lemma rfn_tool25:"\<lbrakk> (0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow> 0 < r * s"
apply simp
done

constdefs
 cmp_rfn::"[('a, 'm) GroupType_scheme, nat, nat \<Rightarrow> 'a set, nat, nat \<Rightarrow> 'a set] \<Rightarrow> (nat \<Rightarrow> 'a set)"
  "cmp_rfn G r f s g  == \<lambda>i. (if i < s * r then  f (Suc (i div s)) \<bullet>\<^sub>G (f (i div s) \<inter> g (i mod s)) else {one G})"

 (** refinement of compseries G r f by a compseries G s g **) 

lemma cmp_rfn0:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g; 
 i \<in> Nset (r - 1); j \<in> Nset (s - 1)\<rbrakk> \<Longrightarrow> f (Suc i) \<bullet>\<^sub>G ((f i ) \<inter> (g j)) \<guillemotleft> G"
apply (frule compser_nsubg, assumption+)
apply (frule compseriesTr0 [of "G" "r" "f" "i"], assumption+)
apply (simp add:Nset_def) 
apply (frule le_less_trans [of "i" "r - Suc 0" "r"]) apply simp
apply (simp add:less_imp_le)
apply (frule compseriesTr0 [of "G" "s" "g" "j"], assumption+)
apply (simp add:Nset_def) 
apply (frule le_less_trans [of "j" "s - Suc 0" "s"]) apply simp
apply (simp add:less_imp_le)
apply (frule compser_nsubg [of "s" "G" "g" "j"], assumption+)
apply (rule_tac G = G and H = "f i" and ?H1.0 = "f (Suc i)" and K = "g j" and ?K1.0 = "g j" in ZassenhausTr1_1, assumption+)
apply (simp add:Nset_def)
apply (frule le_less_trans [of "i" "r - Suc 0" "r"]) apply simp
apply (frule_tac Suc_leI [of "i" "r"])
apply (rule compseriesTr0 [of "G" "r" "f" "Suc i"], assumption+)
 apply (simp add:Nset_def)
 apply assumption+
apply (simp add:special_nsubg_G)
done

lemma cmp_rfn1:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
  \<Longrightarrow> f (Suc 0) \<bullet>\<^sub>G ((f 0 ) \<inter> (g 0)) = carrier G"
apply (frule compseriesTr2 [of "G" "r" "f"], assumption+)
apply (frule compseriesTr2 [of "G" "s" "g"], assumption+)
apply (frule compseriesTr0 [of _ _ "f" "Suc 0"], assumption+)
apply (simp add:Nset_def)
apply simp
apply (rule NinHNTr0_2 [of "G" "f (Suc 0)" "carrier G"], assumption+)
apply (simp add:special_subg_G)
apply (frule compseriesTr0 [of "G" "r" "f" "Suc 0"], assumption+) 
apply (simp add:Nset_def)
apply (simp add:subg_subset)
done

lemma cmp_rfn2:"\<lbrakk>0 < r; 0 < s; group G; compseries G r f; compseries G s g;
           l \<in> Nset (s * r)\<rbrakk>  \<Longrightarrow> cmp_rfn G r f s g l \<guillemotleft> G"
 apply (simp add:cmp_rfn_def)
 apply (case_tac "l < s * r")
 apply simp
 apply (frule_tac i = "l div s" and j = "l mod s" in cmp_rfn0 [of "G" "r" "s"],
                                                 assumption+)
 apply (simp add:Nset_def)
 apply (simp add:div_Tr2)
 apply (frule_tac m = l in mod_less_divisor [of "s"])
 apply (frule_tac x = "l mod s" and n = s in less_le_diff)
 apply (simp add:Nset_def) apply assumption 
apply simp
 apply (simp add:special_subg_e)
done

lemma cmp_rfn3:"\<lbrakk>0 < r; 0 < s; group G; compseries G r f; compseries G s g\<rbrakk>
 \<Longrightarrow> cmp_rfn G r f s g 0 = carrier G \<and> cmp_rfn G r f s g (s * r) = {1\<^sub>G}"
apply (rule conjI) 
 apply (simp add:cmp_rfn_def)
 apply (rule cmp_rfn1 [of "G" "r" "s" "f" "g"], assumption+)
 apply (simp add:cmp_rfn_def)
done
 
lemma rfn_tool20:"\<lbrakk>(0::nat) < m; a = b * m + c; c < m \<rbrakk> \<Longrightarrow>  a mod m = c"
apply (simp add:add_commute)
done

lemma Suci_mod_s_2:"\<lbrakk>0 < r; 0 < s;i \<le> r * s - Suc 0; i mod s < s - Suc 0\<rbrakk>
        \<Longrightarrow> Suc i mod s = Suc (i mod s)"
apply (insert mod_div_equality [of "i" "s", THEN sym])
apply (subgoal_tac "Suc i = i div s * s + Suc (i mod s)")
apply (subgoal_tac "Suc i mod s  = (i div s * s + Suc (i mod s)) mod s")
 apply (subgoal_tac "Suc (i mod s) < s")
 apply (frule_tac m = s and a = "Suc i" and b = "i div s" and c = "Suc (i mod s)" in rfn_tool20, assumption+)
 apply (subgoal_tac "Suc (i mod s) < Suc (s - Suc 0)")  apply simp
 apply (simp del:Suc_pred)
 apply simp+
done

lemma inter_subgs_Tr1:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g; i < r * s\<rbrakk>  \<Longrightarrow> f (i div s) \<inter> g (s - Suc 0) \<guillemotleft> G"
 apply (rule inter_subgs, assumption+)
 apply (rule compseriesTr0, assumption+)  
 apply (frule less_imp_le [of "i" "r * s"])
 apply (frule div_Tr1 [of "r" "s" "i"], assumption+) 
 apply (simp add:mult_commute) apply (simp add:Nset_def)
 apply (rule compseriesTr0, assumption+) apply (simp add:Nset_def)
done

lemma JHS_Tr0_2:"\<lbrakk>0 < r; 0 < s; group G; compseries G r f; compseries G s g\<rbrakk>
\<Longrightarrow> \<forall>i\<in>Nset (s * r - Suc 0). cmp_rfn G r f s g (Suc i) \<lhd> grp G (cmp_rfn G r f s g i)"
apply (frule compseriesTr4 [of "G" "r" "f"], assumption+)
apply (frule compseriesTr4 [of "G" "s" "g"], assumption+)
apply (rule ballI)
apply (frule_tac x = i in Nset_le [of _  "s * r - Suc 0"])
 apply (frule rfn_tool25 [of "s" "r"], assumption+) 
 apply (frule_tac a = i in  rfn_tool11 [of "s * r"], assumption+) 
 apply (frule_tac l = i in div_Tr1 [of "r" "s"], assumption+)
 apply (simp add:less_imp_le)
 apply (frule_tac x = "i div s" in mem_of_Nset [of _ "r"])
 apply (thin_tac "i div s \<le> r") apply (thin_tac "i \<le> s * r - Suc 0")  
 apply (frule_tac l = i in div_Tr2 [of "r" "s"], assumption+)
 apply (frule_tac x = "i div s" in mem_of_Nset [of _ "r - Suc 0"])
 apply (frule_tac a = "i div s" in rfn_tool11 [of "r"], assumption+)
 apply (frule_tac m = "i div s" in Suc_leI [of _ "r"])
 apply (frule_tac x = "Suc (i div s)" in mem_of_Nset [of _ "r"])
 apply (thin_tac "i div s < r") apply (thin_tac "Suc (i div s) \<le> r")
apply (simp add:cmp_rfn_def)
 apply (case_tac "Suc i < s * r")
 apply simp
  apply (case_tac "i mod s = s - 1") 
  apply (frule_tac l = i in div_Tr3_1 [of "r" "s"], assumption+)
  apply simp
  apply (frule_tac l = "Suc i" in div_Tr2 [of "r" "s"], assumption+)
  apply (frule_tac x = "Suc i div s" in mem_of_Nset [of _ "r - Suc 0"])
  apply (frule_tac a = "Suc i div s" in  rfn_tool11 [of "r"], assumption+) 
  apply (frule_tac x = "Suc i div s" in less_mem_of_Nset [of _ "r"])
  apply (frule_tac m = "Suc i div s" in Suc_leI [of _ "r"])
  apply (frule_tac x = "Suc (Suc i div s)" in mem_of_Nset [of _ "r"])
  apply (frule w_cmpser_is_d_gchain [of "G" "r" "f"], assumption+) 
  apply (frule_tac rfn_tool12_2 [of "s"], assumption+)
  apply (thin_tac "i div s \<in> Nset (r - Suc 0)")
  apply (thin_tac "i div s \<le> r - Suc 0")
  apply (thin_tac "i mod s = s - Suc 0")
  apply (thin_tac "Suc i < s * r")
  apply (thin_tac "Suc i div s \<le> r - Suc 0")
  apply (thin_tac "Suc i div s < r")
  apply (thin_tac "Suc (Suc i div s) \<le> r")
  apply simp
  apply (frule_tac i = "i div s" and j = "Suc (i div s)" in 
                       d_gchainTr2 [of "G" "r" "f"], assumption+)
  apply (simp add:less_imp_le)
  apply (frule_tac i = "Suc (i div s)" and j = "Suc (Suc (i div s))" in 
                       d_gchainTr2 [of "G" "r" "f"], assumption+)
  apply (simp add:less_imp_le)
  apply (thin_tac "Suc i div s = Suc (i div s)")
  apply (thin_tac "Suc i mod s = 0")
 apply (frule_tac i = "i div s" in compseriesTr0 [of "G" "r" "f"], assumption+)
 apply (frule_tac i = "Suc (i div s)" in compseriesTr0 [of "G" "r" "f"], 
                                                               assumption+)
 apply (frule_tac i = "Suc (Suc (i div s))" in compseriesTr0 [of "G" "r" "f"], 
                                                               assumption+)
 apply (subst compseriesTr2 [of "G" "s" "g"], assumption+)
 apply (frule_tac H = "f (i div s)" in subg_subset [of "G"], assumption+)
 apply (frule_tac H = "f (Suc (i div s))" in subg_subset [of "G"], assumption+)
 apply (frule_tac A = "f (Suc (i div s))" in Int_absorb2 [of _ "carrier G"]) 
 apply simp
 apply (thin_tac "f (Suc (i div s)) \<inter> carrier G = f (Suc (i div s))")
 apply (frule_tac H = "f (Suc (Suc (i div s)))" and K = "f (Suc (i div s))" in   NinHNTr0_2 [of "G" ], assumption+) apply simp 
 apply (thin_tac "f (Suc (Suc (i div s))) \<bullet>\<^sub>G (f (Suc (i div s))) = f (Suc (i div s))")
apply (rule rfn_tool16 [of "G" "r" "s" _], assumption+)
apply (rule compser_nsubg, assumption+)
 apply (frule_tac x = "Suc (i div s)" in Nset_le [of _ "r"])
 apply (frule_tac m = "Suc (i div s)" and n = r in diff_le_mono [of _ _ "Suc 0"]) apply (thin_tac "Suc (i div s) \<le> r") apply simp
 apply (rule mem_of_Nset, assumption+) 
 apply (rule_tac  H = "f (i div s) \<inter> g (s - Suc 0)" and K = "f (i div s)" in subg_in_subg [of "G"]) 
 apply assumption
 apply (rule inter_subgs_Tr1, assumption+)
 apply (frule_tac x = i in Nset_le [of _ "s * r - Suc 0"])
 apply (frule rfn_tool25 [of "s" "r"], assumption+)
 apply (frule_tac a = i in rfn_tool11 [of "s * r"], assumption+)
 apply (simp add:mult_commute) apply assumption
 apply (rule subsetI) apply simp
 apply (frule_tac m = i in mod_less_divisor [of "s"])
 apply (frule_tac x = "i mod s" in less_le_diff [of _ "s"])
 apply simp 
 apply (frule_tac m = "i mod s" in noteq_le_less [of _ "s - Suc 0"], assumption+) apply (thin_tac "i mod s \<noteq> s - Suc 0")
 apply (thin_tac "i mod s \<le> s - Suc 0")
 apply (frule_tac k = "i mod s" in nat_pos2 [of _ "s"])
 apply (frule_tac l1 = i in div_Tr3_2 [THEN sym, of "r" "s"], assumption+) 
 apply simp apply simp 
 apply (frule_tac i = i in Suci_mod_s_2 [of "r" "s"], assumption+)
 apply (simp add:Nset_le mult_commute) apply assumption apply simp
 apply (frule_tac i = "i mod s" in compser_nsubg [of "s" "G" "g"], assumption+)
 apply (simp add:mem_of_Nset)
 apply (frule_tac i = "Suc (i div s)" in compseriesTr0 [of "G" "r" "f"], assumption+)
 apply (frule_tac m = "i mod s" in Suc_mono [of _ "s - Suc 0"]) 
 apply (simp only:Suc_pred)
 apply (frule_tac x = "Suc (i mod s)" in less_mem_of_Nset [of _ "s"])
apply (frule_tac i = "Suc (i mod s)" in compseriesTr0 [of "G" "s" "g"], assumption+)
apply (rule_tac H = "f (i div s)" and ?H1.0 = "f (Suc (i div s))" and 
K = "g (i mod s)" and ?K1.0 = "g (Suc (i mod s))" in ZassenhausTr3 [of "G"],
                                                 assumption+)
apply (frule_tac i = "i div s" in compseriesTr0 [of "G" "r" "f"], assumption+)
apply (frule_tac i = "i mod s" in compseriesTr0 [of "G" "s" "g"], assumption+)
 apply (frule_tac a = "i mod s" in rfn_tool11 [of "s"])
 apply (rule less_imp_le, assumption+) 
 apply (rule less_mem_of_Nset, assumption+)
 apply (rule_tac i = "i div s" in compser_nsubg [of "r" "G" "f"], assumption+)
 apply simp  apply assumption
apply simp
 apply (frule_tac i = "i div s" in compser_nsubg [of "r" "G" "f"], assumption+) apply simp
 apply (frule_tac i = "i div s" and j = "i mod s" in  cmp_rfn0 [of "G" "r" "s" "f" "g"], assumption+) apply simp
 apply (frule_tac m = i in mod_less_divisor [of "s"])
 apply (frule_tac x = "i mod s" in less_le_diff [of _ "s"])
 apply (simp add:mem_of_Nset)
 apply (rule special_nsubg_e, assumption+)
done

lemma cmp_rfn4:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; 
compseries G s g; l \<in> Nset (s * r - Suc 0)\<rbrakk>
  \<Longrightarrow> cmp_rfn G r f s g (Suc l) \<subseteq> cmp_rfn G r f s g l"
apply (frule JHS_Tr0_2 [of "r" "s" "G" "f" "g"], assumption+)
apply (subgoal_tac "cmp_rfn G r f s g (Suc l) \<lhd> grp G (cmp_rfn G r f s g l)")
prefer 2 apply simp
apply (thin_tac " \<forall>i\<in>Nset (s * r - Suc 0).
          cmp_rfn G r f s g (Suc i) \<lhd> grp G (cmp_rfn G r f s g i)")
apply (frule cmp_rfn2 [of "r" "s" "G" "f" "g" "l"], assumption+)
apply (simp add:Nset_def)
apply (frule le_less_trans [of "l" "s * r - Suc 0" "s* r"]) apply simp
apply (simp add:less_imp_le)
apply (frule subggrp [of "G" "cmp_rfn G r f s g l"], assumption+)
apply (frule nsubg_subset [of "grp G (cmp_rfn G r f s g l)"  ], assumption+) 
apply (simp add: grp_carrier)
done

lemma cmp_rfn5:"\<lbrakk>0 < r; 0 < s; group G; compseries G r f; compseries G s g\<rbrakk>
    \<Longrightarrow> \<forall>i\<in>Nset r. cmp_rfn G r f s g (i * s) = f i"
apply (rule ballI)
apply (simp add:cmp_rfn_def)
apply (simp add:Nset_def) 
apply (case_tac "i < r") apply simp
apply (frule_tac m = i in less_imp_le [of _ "r"])
apply (frule_tac x = i in mem_of_Nset[of _ "r"])
apply (frule_tac i = i in compseriesTr0 [of "G" "r" "f"], assumption+)
apply (thin_tac "i \<le> r") 
apply (frule_tac m = i in Suc_leI [of _ "r"])
apply (frule_tac i = "Suc i" in compseriesTr0 [of "G" "r" "f"], assumption+)
apply (simp add:mem_of_Nset)
apply (subst compseriesTr2 [of "G" "s" "g"], assumption+) 
apply (frule_tac H = "f i" in subg_subset [of "G"], assumption+) 
apply (subst Int_absorb2, assumption+) apply (frule rfn_tool8, assumption+)
apply simp
apply (subgoal_tac "0 < r") prefer 2 apply simp
apply (frule_tac i = i and j = "Suc i" in d_gchainTr2 [of "G" "r" "f"], assumption+)
 apply (simp add:mem_of_Nset) apply simp
 apply (rule_tac K = "f i" and H = "f (Suc i)" in NinHNTr0_2 [of "G"], assumption+)
apply simp apply (frule compseries_is_td_gchain, assumption+)
apply (simp add:td_gchain_def)
done

lemma JHS_Tr0:"\<lbrakk>(0::nat) < r; 0 < s;  group G; compseries G r f; compseries G s g\<rbrakk> \<Longrightarrow> cmp_rfn G r f s g \<in> wcsr_rfns G r f s"
apply (simp add:wcsr_rfns_def)
apply (frule cmp_rfn5 [of "r" "s" "G" "f" "g"], assumption+) apply simp
apply (thin_tac "\<forall>i\<in>Nset r. cmp_rfn G r f s g (i * s) = f i")
apply (simp add:tw_cmpser_def) apply (rule conjI)
prefer 2 apply (rule  JHS_Tr0_2 [of "r" "s" "G" "f" "g"], assumption+)
apply (simp add:td_gchain_def) apply (rule conjI)
prefer 2
apply (rule cmp_rfn3, assumption+) apply (simp add:d_gchain_def)
apply (rule conjI) apply (rule ballI) apply (rule cmp_rfn2, assumption+)
apply (rule ballI) apply (rule cmp_rfn4, assumption+)
done

lemma rfn_tool17:"(a::nat) = b \<Longrightarrow> a - c = b - c"
apply simp
done

lemma isom4b:"\<lbrakk>group G; N \<lhd> G; H \<guillemotleft> G\<rbrakk> \<Longrightarrow> 
                    (grp G (N \<bullet>\<^sub>G H) / N) \<cong> (grp G H / (H \<inter> N))"
apply (frule isom4 [of "G" "N" "H"], assumption+)
apply (rule isomTr1)
 apply (simp add:homom4_2) 
 apply (frule  subgnsubg [of "G" "H" "N", THEN sym], assumption+)  apply simp 
apply (rule homom4Tr1, assumption+)
done

lemma Suc_rtos_div_r_1:"\<lbrakk> 0 < r; 0 < s; i \<le> r * s - Suc 0; 
Suc (rtos r s i) < r * s; i mod s = s - Suc 0; i div s < r - Suc 0\<rbrakk> \<Longrightarrow>
         Suc (rtos r s i) div r = i mod s"
apply (simp add:rtos_def) 
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
apply simp
apply (subgoal_tac "Suc ((s - Suc 0) * r + i div s) div r = ((s - Suc 0) * r + Suc (i div s)) div r") apply (simp del:add_Suc add_Suc_right)
apply (rule rfn_tool1_1, assumption+)
apply (subgoal_tac "Suc (i div s) < Suc (r - Suc 0)")
apply simp apply (simp del:Suc_pred) apply simp
done

lemma Suc_rtos_mod_r_1:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; Suc (rtos r s i) < r * s; i mod s = s - Suc 0; i  div s < r - Suc 0\<rbrakk>
         \<Longrightarrow> Suc (rtos r s i) mod r = Suc (i div s)"
apply (simp add:rtos_def)
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
 apply simp
 apply (subgoal_tac "Suc ((s - Suc 0) * r + i div s) mod r =
   ((s - Suc 0) * r + Suc (i div s)) mod r")
  apply (simp del:add_Suc add_Suc_right)
  apply (subgoal_tac "Suc (i div s) < r")
 apply (subst rfn_tool20 [of "r" _ "(s - Suc 0)" "Suc (i div s)"], assumption+)
 apply simp apply assumption apply simp
 apply (subgoal_tac "Suc (i div s) < Suc (r - Suc 0)") apply simp
 apply (simp del:Suc_pred) apply simp
done

lemma i_div_s_less:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; Suc (rtos r s i) < r * s;
i mod s = s - Suc 0; Suc i < s * r \<rbrakk>  \<Longrightarrow> i div s < r - Suc 0"
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"])
 apply simp
apply (frule_tac  r = r and s = s and l = i in div_Tr2, assumption+)
 apply (simp add:mult_commute)
apply (rule contrapos_pp)
 apply simp
apply (simp add:rtos_def)
apply (subgoal_tac "(s - Suc 0) * r + r = r * s")
 apply simp
apply (thin_tac "(s - Suc 0) * r + r < r * s")
apply (simp add:mult_commute)
apply (simp add:diff_mult_distrib2)
done

lemma rtos_mod_r_1:"\<lbrakk> 0 < r; 0 < s; i \<le> r * s - Suc 0; rtos r s i < r * s;
  i mod s = s - Suc 0 \<rbrakk>  \<Longrightarrow> rtos r s i mod r = i div s"
apply (simp add:rtos_def)
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
 apply simp
 apply (rule rfn_tool20, assumption+) apply simp
 apply (frule_tac r = r and s = s and l = i in div_Tr2, assumption+)
 apply (rule le_less_trans, assumption+) apply (simp add:mult_commute)
 apply (rule le_less_trans, assumption+) apply simp
done

lemma Suc_i_mod_s_0_1:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i mod s = s - Suc 0\<rbrakk>
        \<Longrightarrow> Suc i mod s = 0"
apply (insert mod_div_equality [of "i" "s", THEN sym])
apply simp
 apply (thin_tac "i mod s = s - Suc 0")
apply (subgoal_tac "Suc i mod s = Suc (i div s * s + s - Suc 0) mod s")
 apply (thin_tac "i = i div s * s + s - Suc 0") apply (simp del:add_Suc)
 apply (subgoal_tac "Suc (i div s * s + s - Suc 0) mod s = (i div s * s + s) mod s") 
 apply (simp del:add_Suc)
 apply (subgoal_tac "Suc (i div s * s + s - Suc 0) = i div s * s + s")
 apply (simp del:add_Suc)
apply (rule Suc_pred [of "i div s * s + s"]) apply simp
done

(* same as div_Tr3_2 *)
lemma Suci_div_s_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i mod s < s - Suc 0\<rbrakk>
         \<Longrightarrow> Suc i div s = i div s"
apply (rule div_Tr3_2 [THEN sym], assumption+)
 apply simp
done

lemma rtos_i_mod_r_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0\<rbrakk> \<Longrightarrow> rtos r s i mod r = i div s"
apply (simp add:rtos_def)
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
apply simp
apply (frule_tac  r = r and s = s and l = i in div_Tr2, assumption+)
 apply (simp add:mult_commute)
apply (subgoal_tac "i div s < r") 
 apply (rule rfn_tool20, assumption+)  apply simp       
 apply assumption
 apply (rule le_less_trans, assumption+) apply simp
done

lemma Suc_rtos_i_mod_r_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i div s = r - Suc 0\<rbrakk> \<Longrightarrow> Suc (rtos r s i) mod r = 0"
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
apply (simp add:rtos_def)
done

lemma Suc_rtos_i_mod_r_3:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i div s < r - Suc 0\<rbrakk> \<Longrightarrow> Suc (rtos r s i) mod r = Suc (i div s)"
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
apply (simp add:rtos_def)
apply (subgoal_tac "Suc (i mod s * r + i div s) mod r = 
                    (i mod s * r + Suc (i div s)) mod r")
apply (simp del:add_Suc add_Suc_right)
 apply (thin_tac "Suc (i mod s * r + i div s) mod r =
       (i mod s * r + Suc (i div s)) mod r")
 apply (subgoal_tac "Suc (i div s) < r")
apply (rule rfn_tool20, assumption+)  apply simp apply assumption+
apply (subgoal_tac "Suc (i div s) < Suc (r - Suc 0)") apply simp
apply (simp del:Suc_pred) apply simp
done

lemma Suc_rtos_div_r_3:"\<lbrakk>0 < r; 0 < s; i mod s < s - Suc 0; i \<le> r * s - Suc 0; 
Suc (rtos r s i) < r * s; i div s < r - Suc 0\<rbrakk> \<Longrightarrow> 
               Suc (rtos r s i) div r = i mod s"
apply (simp add:rtos_def) 
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
apply simp
apply (subgoal_tac "Suc (i mod s * r + i div s) div r = 
                       (i mod s * r + Suc (i div s)) div r") 
apply (simp del:add_Suc add_Suc_right)
 apply (thin_tac "Suc (i mod s * r + i div s) div r = 
                       (i mod s * r + Suc (i div s)) div r") 
 apply (subgoal_tac "Suc (i div s) < Suc (r - Suc 0)")
 apply (rule rfn_tool1_1, assumption+) apply simp
 apply (simp del:Suc_pred) apply simp 
done

lemma r_s_div_s:"\<lbrakk>0 < r; 0 < s \<rbrakk> \<Longrightarrow> (r * s - Suc 0) div s = r - Suc 0"
apply (frule rfn_tool1_1 [of "s" "s - Suc 0" "r - Suc 0"]) 
 apply simp
apply (subgoal_tac "((r - Suc 0) * s + (s - Suc 0)) div s 
                     = (r * s - Suc 0) div s")  apply simp
apply (subgoal_tac "((r - Suc 0) * s + (s - Suc 0)) = (r * s - Suc 0)")
apply simp  apply (simp add:diff_mult_distrib)
done
 
lemma r_s_mod_s:"\<lbrakk>0 < r; 0 < s \<rbrakk> \<Longrightarrow> (r * s - Suc 0) mod s = s - Suc 0"
apply (frule rfn_tool20 [of "s" "(r - Suc 0) * s + (s - Suc 0)" "r - Suc 0" "s - Suc 0"]) apply simp apply simp
apply (subgoal_tac "((r - Suc 0) * s + (s - Suc 0)) mod s = 
                                     (r * s - Suc 0) mod s")
apply simp
apply (subgoal_tac "(r - Suc 0) * s + (s - Suc 0) = r * s - Suc 0")
apply simp  apply (simp add:diff_mult_distrib)
done

lemma rtos_r_s:"\<lbrakk>0 < r; 0 < s\<rbrakk> \<Longrightarrow> rtos r s (r * s - Suc 0) = r * s - Suc 0"
apply (simp add:rtos_def)
apply (frule r_s_div_s [of "r" "s"], assumption+)
apply (frule r_s_mod_s [of "r" "s"], assumption+)
apply simp apply (simp add:diff_mult_distrib) apply (simp add:mult_commute)
done

lemma rtos_rs_1:"\<lbrakk> 0 < r; 0 < s; rtos r s i < r * s; \<not> Suc (rtos r s i) < r * s\<rbrakk> \<Longrightarrow> rtos r s i = r * s - Suc 0"
apply (frule rfn_tool25 [of "r" "s"], assumption+)
apply (frule less_le_diff [of "rtos r s i" "r * s"])
apply (subgoal_tac "r * s \<le> Suc (rtos r s i)")
apply (subgoal_tac "Suc (r * s - Suc 0) \<le> Suc (rtos r s i)")
apply (subgoal_tac "r * s - Suc 0 \<le> rtos r s i") apply simp
apply (simp del:Suc_pred) apply simp apply (simp add:le_def) 
done

lemma rtos_rs_i_rs:"\<lbrakk> 0 < r; 0 < s; i \<le> r * s - Suc 0; 
rtos r s i = r * s - Suc 0\<rbrakk> \<Longrightarrow>  i = r * s - Suc 0" 
apply (frule mem_of_Nset [of "i" "r * s - Suc 0"])     
apply (frule rtos_r_s [of "r" "s"], assumption+)
apply (subgoal_tac "rtos r s i = rtos r s (r * s - Suc 0)")
 apply (thin_tac "rtos r s i = r * s - Suc 0") 
 apply (thin_tac "rtos r s (r * s - Suc 0) = r * s - Suc 0")
apply (frule rtos_inj [of "r" "s"], assumption+)
apply (simp add:inj_on_def Nset_def)
 apply (subgoal_tac "r * s - Suc 0 = rtos r s (r * s - Suc 0)")
 apply (thin_tac "rtos r s (r * s - Suc 0) = r * s - Suc 0")
 apply simp
apply (rule sym, assumption)
done

lemma JHS_Tr1_1:"\<lbrakk> group G; 0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
\<Longrightarrow>  f (Suc ((r * s - Suc 0) div s)) \<bullet>\<^sub>G (f ((r * s - Suc 0) div s) \<inter> g ((r * s - Suc 0) mod s)) = f (r - Suc 0) \<inter> g (s - Suc 0)"
apply (frule r_s_div_s [of "r" "s"], assumption+)
apply (frule r_s_mod_s [of "r" "s"], assumption+)
apply simp 
apply (subst compseriesTr3 [of "G" "r" "f"], assumption+)
apply (frule compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule compseriesTr0 [of "G" "s" "g" "s - Suc 0"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule inter_subgs [of "G" "f (r - (Suc 0))" "g (s - Suc 0)"], 
                                                          assumption+)
apply (rule settOp_one_l, assumption+)
done

lemma JHS_Tr1_2:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
 k < r - Suc 0\<rbrakk> \<Longrightarrow> ((grp G (f (Suc k) \<bullet>\<^sub>G (f k \<inter> g (s - Suc 0)))) / 
                               (f (Suc (Suc k)) \<bullet>\<^sub>G (f (Suc k) \<inter> g 0))) \<cong>
               ((grp G (g s \<bullet>\<^sub>G (g (s - Suc 0) \<inter> f k))) /
                          (g s \<bullet>\<^sub>G (g (s - Suc 0) \<inter> f (Suc k))))"
apply (frule compseriesTr0 [of "G" "r" "f" "k"], assumption+)
apply (frule less_trans [of "k" "r - Suc 0" "r"]) apply simp
apply (simp add:mem_of_Nset) 
apply (frule Suc_leI [of "k" "r - Suc 0"]) 
apply (frule le_less_trans [of "Suc k" "r - Suc 0" "r"]) apply simp
apply (frule compseriesTr0 [of "G" "r" "f" "Suc k"], assumption+)
apply (rule less_mem_of_Nset, assumption+)
 apply (thin_tac "Suc k \<le> r - Suc 0")
 apply (frule Suc_leI[of "Suc k" "r"])
apply (frule compseriesTr0 [of "G" "r" "f" "Suc (Suc k)"], assumption+)
apply (rule mem_of_Nset, assumption+)
apply (frule compseriesTr0 [of "G" "s" "g" "s - Suc 0"], assumption+)
apply (simp add:Nset_def less_imp_le)
apply (subst compseriesTr2 [of "G" "s" "g"], assumption+)
apply (subst compseriesTr3 [of "G" "s" "g"], assumption+)
apply (subst Int_absorb2 [of "f (Suc k)" "carrier G"])
 apply (rule subg_subset, assumption+)
 apply (subst NinHNTr0_2 [of "G" "f (Suc (Suc k))" "f (Suc k)"], assumption+)
 apply (rule compseriesTr5 [of "r" "G" "f" "Suc k"], assumption+)
 apply (frule Suc_leI [of "k" "r - Suc 0"])
 apply (rule mem_of_Nset, assumption+)
apply (subst settOp_one_l [of "G" "g (s - Suc 0) \<inter> f k"], assumption+)
 apply (simp add:inter_subgs)
apply (subst settOp_one_l [of "G" "g (s - Suc 0) \<inter> f (Suc k)"], assumption+)
 apply (simp add:inter_subgs)
apply (frule subggrp [of "G" "f k"], assumption+) 
apply (frule compser_nsubg [of "r" "G" "f" "k"], assumption+)
apply (simp add:less_mem_of_Nset [of "k" "r - Suc 0"])
apply (frule isom4b [of "grp G (f k)" "f (Suc k)" "f k \<inter> g (s - Suc 0)"], 
                                                          assumption+)
apply (rule subg_in_subg, assumption+)
 apply (rule inter_subgs, assumption+)
 apply (simp add:Int_lower1)
 apply (frule compseriesTr5 [of "r" "G" "f" "k"], assumption+)
 apply (rule less_mem_of_Nset, assumption+)
 apply (frule settOpinherited [of "G" "f k" "f (Suc k)" "f k \<inter> g (s - Suc 0)"], assumption+)
 apply (simp add:Int_lower1) apply simp 
  apply (thin_tac " f (Suc k) \<bullet>\<^sub>(grp G (f k)) (f k \<inter> g (s - Suc 0)) =
       f (Suc k) \<bullet>\<^sub>G (f k \<inter> g (s - Suc 0))")
  apply (frule Suc_pos [of "Suc k" "r"])
 apply (frule cmp_rfn0 [of "G" "r" "s" "f" "g" "k" "s - Suc 0"], assumption+) 
 apply (simp add:less_mem_of_Nset)
 apply (simp add:Nset_def)
 apply (frule subg_inc_settOp [of "G" "f k" "f (Suc k)" "f k \<inter> g (s - Suc 0)"], assumption+) apply (simp add:Int_lower1)
 apply (simp add:grp_inherited [of "G" "f (Suc k) \<bullet>\<^sub>G (f k \<inter> g (s - Suc 0))" "f k"])
  apply (frule inter_subgs [of "G" "f k" "g (s - Suc 0)"], assumption+)
apply (frule grp_inherited [of "G" "f k \<inter> g (s - Suc 0)" "f k"], assumption+)
apply (rule Int_lower1) apply simp
 apply (thin_tac "grp (grp G (f k)) (f k \<inter> g (s - Suc 0)) =
       grp G (f k \<inter> g (s - Suc 0))")
 apply (thin_tac "f (Suc k) \<bullet>\<^sub>G (f k \<inter> g (s - Suc 0)) \<subseteq> f k")
 apply (thin_tac "f (Suc k) \<bullet>\<^sub>G (f k \<inter> g (s - Suc 0)) \<guillemotleft> G")
 apply (simp add:Int_assoc [of "f k" "g (s - Suc 0)" "f (Suc k)"])
 apply (simp add:Int_commute [of "g (s - Suc 0)" "f (Suc k)"])
 apply (simp add:Int_assoc [of "f k" "f (Suc k)" "g (s - Suc 0)", THEN sym])
 apply (simp add:Int_absorb1[of "f (Suc k)" "f k"])
apply (simp add:Int_commute)
done

lemma JHS_Tr1_3:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
       i \<le> s * r - Suc 0; Suc (rtos r s i) < s * r; Suc i < s * r;
       i mod s < s - Suc 0; Suc i div s \<le> r - Suc 0; i div s = r - Suc 0\<rbrakk>
    \<Longrightarrow> group (grp G (f r \<bullet>\<^sub>G (f (r - Suc 0) \<inter> g (i mod s))) /
        (f r \<bullet>\<^sub>G (f (r - Suc 0) \<inter> g (Suc (i mod s)))))"
apply (subgoal_tac "i div s \<le> r - Suc 0")
apply (frule mem_of_Nset [of "i div s" "r - Suc 0"]) prefer 2 apply simp
 apply (thin_tac "i div s \<le> r - Suc 0")
apply (frule less_mem_of_Nset [of "i mod s" "s - Suc 0"])
apply (frule compser_nsubg [of "r" "G" "f" "i div s"], assumption+)
 apply simp
apply (frule compser_nsubg [of "s" "G" "g" "i mod s"], assumption+)
 apply simp
 apply (frule  compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply (simp add:Nset_def)
 apply (frule  compseriesTr0 [of "G" "r" "f" "r"], assumption+)
 apply (simp add:Nset_def)
 apply (frule  compseriesTr0 [of "G" "s" "g" "i mod s"], assumption+)
 apply (simp add:Nset_def) apply (simp add:less_imp_le)
 apply (frule  compseriesTr0 [of "G" "s" "g" "Suc (i mod s)"], assumption+)
 apply (frule Suc_mono [of "i mod s" "s - (Suc 0)"]) 
 apply (simp add:less_mem_of_Nset)
 apply simp
apply (frule cmp_rfn0 [of "G" "r" "s" "f" "g" "i div s" "i mod s"], assumption+) apply (simp add:mem_of_Nset)+
apply (frule  ZassenhausTr3 [of "G" "f (r - Suc 0)" "f r" "g (i mod s)" "g (Suc (i mod s))"], assumption+)
apply (frule subggrp [of "G" "f r \<bullet>\<^sub>G (f (r - Suc 0) \<inter> g (i mod s))"], 
                                                              assumption+)
apply (rule Qgrp, assumption+)
done

lemma JHS_Tr1_4:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
       i \<le> s * r - Suc 0; Suc (rtos r s i) < s * r; Suc i < s * r;
       i mod s < s - Suc 0; Suc i div s \<le> r - Suc 0; i div s = r - Suc 0\<rbrakk> \<Longrightarrow> 
      group (grp G (g (Suc (i mod s)) \<bullet>\<^sub>G (g (i mod s) \<inter> f (r - Suc 0))) /
       (g (Suc (Suc (i mod s))) \<bullet>\<^sub>G (g (Suc (i mod s)) \<inter> f 0)))"
apply (subst compseriesTr2 [of "G" "r" "f"], assumption+)
apply (frule compseriesTr0 [of "G" "s" "g" "Suc (i mod s)"], assumption+)
apply (frule Suc_mono [of "i mod s" "s - Suc 0"]) apply simp
 apply (rule less_mem_of_Nset, assumption+)
apply (frule subg_subset [of "G" "g (Suc (i mod s))"], assumption+)
apply (subst Int_absorb2, assumption+)
apply (frule Suc_mono [of "i mod s" "s - Suc 0"])
apply (frule less_mem_of_Nset [of "i mod s" "s - Suc 0"])
 apply simp
apply (frule Suc_leI [of "Suc (i mod s)" "s"])
apply (frule compseriesTr0 [of "G" "s" "g" "Suc (Suc (i mod s))"], assumption+)
 apply (rule mem_of_Nset, assumption+)
 apply (frule less_le_diff [of "Suc (i mod s)" "s"])
 apply (frule Suc_pos [of "Suc (i mod s)" "s"])
 apply (frule compseriesTr5 [of "s" "G" "g" "Suc (i mod s)"], assumption+)
 apply (rule mem_of_Nset, assumption+)
 apply (subst NinHNTr0_2 [of "G" "g (Suc (Suc (i mod s)))"
                                        "g (Suc (i mod s))"], assumption+)
apply (frule compseriesTr0 [of "G" "s" "g" "i mod s"], assumption+)
 apply (frule mod_less_divisor [of "s" "i"])
 apply (rule less_mem_of_Nset, assumption+)
 apply (frule cmp_rfn0 [of "G" "s" "r" "g" "f" "i mod s" "r - Suc 0"], assumption+)
 apply simp apply (simp add:mem_of_Nset)
 apply (frule  compser_nsubg [of "s" "G" "g" "i mod s"], assumption+)
 apply simp
apply (frule ZassenhausTr4_1 [of "G" "g (i mod s)" "g (Suc (i mod s))" "f (r - Suc 0)"], assumption+)
 apply (rule subg_in_subg, assumption+)
 apply (rule inter_subgs, assumption+)
 apply (rule compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply (simp add:Nset_def) apply assumption
 apply (rule Int_lower1)
apply (rule Qgrp)
 apply (rule subggrp, assumption+)
done

lemma JHS_Tr1_5:"\<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
 i \<le> s * r - Suc 0; Suc (rtos r s i) < s * r; Suc i < s * r;
       i mod s < s - Suc 0; i div s < r - Suc 0\<rbrakk>
    \<Longrightarrow> (grp G (f (Suc (i div s)) \<bullet>\<^sub>G (f (i div s) \<inter> g (i mod s))) /
        (f (Suc (i div s)) \<bullet>\<^sub>G (f (i div s) \<inter> g (Suc (i mod s))))) \<cong>
       (grp G (g (Suc (i mod s)) \<bullet>\<^sub>G (g (i mod s) \<inter> f (i div s))) /
       (g (Suc (Suc (rtos r s i) div r)) \<bullet>\<^sub>G
           (g (Suc (rtos r s i) div r) \<inter> f (Suc (rtos r s i) mod r))))"

apply (frule compseriesTr0 [of "G" "s" "g" "i mod s"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule compseriesTr0 [of "G" "s" "g" "Suc (i mod s)"], assumption+)
apply (frule Suc_mono [of "i mod s" "s - Suc 0"]) apply simp
 apply (rule less_mem_of_Nset, assumption+)
apply (frule compseriesTr0 [of "G" "r" "f" "i div s"], assumption+)
 apply (frule less_trans [of "i div s" "r - Suc 0" "r"]) apply simp
 apply (rule less_mem_of_Nset, assumption+)
apply (frule compseriesTr0 [of "G" "r" "f" "Suc (i div s)"], assumption+)
 apply (frule Suc_mono [of "i div s" "r - Suc 0"]) 
 apply (simp add:less_mem_of_Nset)
 apply (frule compser_nsubg [of "r" "G" "f" "i div s"], assumption+)
 apply (simp add:less_mem_of_Nset)
 apply (frule compser_nsubg [of "s" "G" "g" "i mod s"], assumption+)
 apply (simp add:mem_of_Nset)
apply (subst Suc_rtos_i_mod_r_3 [of "r" "s" "i"], assumption+)
 apply (simp add:mult_commute) apply assumption
 apply (subst Suc_rtos_div_r_3 [of "r" "s" "i" ], assumption+)
 apply (simp add:mult_commute)+ 
apply (rule Zassenhaus [of "G" "f (i div s)" "f (Suc (i div s))" "g (i mod s)"
 "g (Suc (i mod s))"], assumption+)
done

lemma JHS_Tr1_6:" \<lbrakk>group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
 i \<le> r * s - Suc 0; Suc (rtos r s i) < r * s\<rbrakk> \<Longrightarrow>
  ((grp G (cmp_rfn G r f s g i)) / (cmp_rfn G r f s g (Suc i))) \<cong>
  ((grp G (g (Suc (rtos r s i div r)) \<bullet>\<^sub>G
                (g (rtos r s i div r) \<inter> f (rtos r s i mod r)))) /
        (g (Suc (Suc (rtos r s i) div r)) \<bullet>\<^sub>G
              ( g (Suc (rtos r s i) div r) \<inter> f (Suc (rtos r s i) mod r))))"
apply (simp add:cmp_rfn_def)
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) apply simp
 apply (simp add:mult_commute [of "r" "s"])
 apply (frule Suc_leI [of "i" "s * r"]) apply (thin_tac "i < s * r")
apply (case_tac "\<not> Suc i < s * r") apply simp
 apply (frule rfn_tool17 [of "Suc i" "s * r" "Suc 0"])
 apply (thin_tac " Suc i = s * r")
 apply simp
 apply (frule rtos_r_s [of "r" "s"], assumption+)
 apply (simp add:mult_commute [of "r" "s"])  (* !! ??? *)
apply simp
apply (frule mod_less_divisor [of "s" "i"])
apply (frule less_le_diff [of "i mod s" "s"]) apply (thin_tac "i mod s < s")
 apply (case_tac "i mod s = s - Suc 0")
 apply (frule_tac div_Tr2 [of "r" "s" "Suc i"], assumption+) apply simp
 apply (subst div_Tr3_1 [of "r" "s" "i"], assumption+) apply simp
 apply (subst rtos_hom3 [of "r" "s" "i"], assumption+) apply (rule mem_of_Nset)
 apply (simp add:mult_commute)
 apply (subst rtos_hom3_1 [of "r" "s" "i"], assumption+) apply (rule mem_of_Nset) apply (simp add:mult_commute)
apply (frule div_Tr3_1 [of "r" "s" "i"], assumption+) apply simp
 apply simp apply (thin_tac "Suc i div s = Suc (i div s)")
 apply (insert n_less_Suc [of "i div s"])
 apply (frule less_le_trans [of "i div s" "Suc (i div s)" "r - Suc 0"], 
                                                             assumption+)
 apply (subst Suc_rtos_div_r_1 [of "r" "s" "i"], assumption+) 
 apply (simp add:mult_commute) apply (simp add:mult_commute)+
 apply (subst Suc_rtos_mod_r_1 [of "r" "s" "i"], assumption+)
 apply (subst Suc_i_mod_s_0_1 [of "r" "s" "i"], assumption+) 
 apply (rule JHS_Tr1_2 [of "G" "r" "s" "f" "g" "i div s"], assumption+)
apply (frule noteq_le_less [of "i mod s" "s - Suc 0"], assumption+)
 apply (thin_tac "i mod s \<le> s - Suc 0")
 apply (thin_tac "i mod s \<noteq> s - Suc 0")
 apply (frule div_Tr2 [of "r" "s" "Suc i"], assumption+) apply simp
 apply (subst div_Tr3_2 [THEN sym, of "r" "s" "i"], assumption+)
 apply simp
 apply (subst rfn_tool12_1 [THEN sym, of "s" "i"], assumption+)
 apply simp
 apply (subst rtos_hom3 [of "r" "s" "i"], assumption+)
 apply (rule mem_of_Nset) apply (simp add:mult_commute)
 apply (subst rtos_hom3_1 [of "r" "s" "i"], assumption+)
 apply (rule mem_of_Nset) apply (simp add:mult_commute)
apply (case_tac "i div s = r - Suc 0")
apply (subst rtos_hom5 [of "r" "s" "i"], assumption+)
 apply (rule mem_of_Nset) apply (simp add:mult_commute)
 apply assumption
 apply (subst rtos_hom7 [of "r" "s" "i"], assumption+)
 apply (rule mem_of_Nset) apply (simp add:mult_commute)
 apply assumption apply simp
apply (frule JHS_Tr1_3 [of "G" "r" "s" "f" "g" "i"], assumption+)
 apply simp apply assumption+
apply (frule JHS_Tr1_4 [of "G" "r" "s" "f" "g" "i"], assumption+)
 apply simp apply assumption+
apply (rule isomTr1, assumption+)
apply (rule JHS_Tr1_2 [of "G" "s" "r" "g" "f" "i mod s"], assumption+)
apply (frule div_Tr2 [of "r" "s" "i"], assumption+)
 apply (rule le_less_trans [of "i" "s * r - Suc 0" "s * r"], assumption+)
 apply simp
apply (frule noteq_le_less [of "i div s" "r - Suc 0"], assumption+) 
apply (rule JHS_Tr1_5, assumption+)
apply simp apply assumption+
done

lemma JHS_Tr1:"\<lbrakk> group G; 0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
\<Longrightarrow> isom_Gchains (r * s - 1) (rtos r s) (Qw_cmpser G (cmp_rfn G r f s g)) (Qw_cmpser G (cmp_rfn G s g r f))"
apply (simp add:isom_Gchains_def)
 apply (rule ballI) 
 apply (simp add:Nset_def)
 apply (frule rfn_tool25 [of "r" "s"], assumption+)
 apply (frule_tac b = "r * s" and a = i in rfn_tool11, assumption+)
apply (simp add:Qw_cmpser_def)
 apply (simp only:cmp_rfn_def [of "G" "s" "g"]) 
 apply (frule_tac l = i in rtos_hom1 [of "r" "s"], assumption+)
 apply (rule mem_of_Nset, assumption+)
 apply (simp add:Nset_def)
 apply (frule_tac i = "rtos r s i" and j = "s * r - Suc 0" and k = "s * r" in
          le_less_trans) apply simp
 apply (simp add:mult_commute [of "s" "r"])
apply (case_tac "Suc (rtos r s i) < r * s") apply simp
prefer 2 apply simp
 apply (frule_tac i = i in rtos_rs_1 [of "r" "s"], assumption+) 
 apply (frule_tac i = i in rtos_rs_i_rs [of "r" "s"], assumption+)
 apply (rule less_le_diff, assumption+)
 apply (simp add:cmp_rfn_def)
 apply (simp add:mult_commute)
apply (subst JHS_Tr1_1 [of "G" "r" "s" "f" "g"], assumption+)
apply (frule JHS_Tr1_1 [of "G" "s" "r" "g" "f"], assumption+)
 apply (simp add:mult_commute [of "r" "s"])
 apply (simp add:Int_commute) 
apply (frule compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule compseriesTr0 [of "G" "s" "g" "s - Suc 0"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule inter_subgs [of "G" "f (r - (Suc 0))" "g (s - Suc 0)"], 
                                                          assumption+)
apply (frule special_subg_e [of "G"])
apply (frule special_nsubg_e [of "G" "f (r - Suc 0) \<inter> g (s - Suc 0)"], 
                                                        assumption+)
apply (frule subggrp [of "G" "f (r - Suc 0) \<inter> g (s - Suc 0)"], assumption+)
apply (frule Qgrp [of "grp G (f (r - Suc 0) \<inter> g (s - Suc 0))" "{1\<^sub>G}"])
 apply assumption+
 apply simp 
apply (rule JHS_Tr1_6, assumption+)
done
 
lemma abc_SucTr0:"\<lbrakk>(0::nat) < a; c \<le> b; a - Suc 0 = b - c\<rbrakk> \<Longrightarrow> a = (Suc b) - c"
apply (subgoal_tac "Suc 0 \<le> a")
apply (frule le_add_diff_inverse2 [of "Suc 0" "a", THEN sym])
apply auto apply (rule Suc_diff_le[THEN sym], assumption+)
done

lemma length_wcmpser0_0:"\<lbrakk>group G; Ugp E; w_cmpser G (Suc 0) f\<rbrakk> 
  \<Longrightarrow> f ` (Nset (Suc 0)) = {f 0, f (Suc 0)}"
apply (simp add:Nset_def)
apply (subst Nset_1) apply auto
done

lemma length_wcmpser0_1:"\<lbrakk>group G; Ugp E; w_cmpser G (Suc n) f; i \<in> Nset n;
 (Qw_cmpser G f) i \<cong> E\<rbrakk> \<Longrightarrow> f i = f (Suc i)"
apply (subgoal_tac "0 < Suc n")
apply (frule w_cmpser_gr [of "G" "Suc n" "f" "i"], assumption+) 
 apply (simp add:Nset_def) prefer 2 apply simp
apply (frule w_cmpser_gr [of "G" "Suc n" "f" "Suc i"], assumption+) 
apply (simp add:Nset_def)
apply (frule w_cmpser_ns [of "G" "Suc n" "f" "i"], assumption+) apply simp
apply (simp add:Qw_cmpser_def)
apply (rule QgrpUnit_3 [of "G" "E" "f i" "f (Suc i)"], assumption+)
done

lemma length_wcmpser0_2:"\<lbrakk>group G; Ugp E; w_cmpser G (Suc n) f; i \<in> Nset n;
 \<not> (Qw_cmpser G f) i \<cong> E\<rbrakk> \<Longrightarrow> f i \<noteq> f (Suc i)"       
apply (subgoal_tac "0 < Suc n")
apply (frule w_cmpser_gr [of "G" "Suc n" "f" "i"], assumption+) 
 apply (simp add:Nset_def) prefer 2 apply simp
apply (frule w_cmpser_gr [of "G" "Suc n" "f" "Suc i"], assumption+) 
apply (simp add:Nset_def)
apply (frule w_cmpser_ns [of "G" "Suc n" "f" "i"], assumption+) apply simp
apply (simp add:Qw_cmpser_def)
apply (rule QgrpUnit_4 [of "G" "E" "f i" "f (Suc i)"], assumption+)
done

lemma length_wcmpser0_3:"\<lbrakk>group G; Ugp E; w_cmpser G (Suc (Suc n)) f;
  f (Suc n) \<noteq> f (Suc (Suc n))\<rbrakk> \<Longrightarrow> f (Suc (Suc n)) \<notin> f ` Nset (Suc n)"
apply (frule w_cmpser_is_d_gchain, assumption+)
apply (thin_tac "w_cmpser G (Suc (Suc n)) f")
apply (rule contrapos_pp, simp+)
apply (frule d_gchainTr2 [of "G" "Suc ((Suc n))" "f" "Suc n" "Suc (Suc n)"])
apply simp apply assumption+ apply (simp add:Nset_def) apply (simp add:Nset_def)
apply simp
apply (frule psubsetI [of "f (Suc (Suc n))" "f (Suc n)"])
apply (rule not_sym, assumption+) 
apply (thin_tac "f (Suc (Suc n)) \<subseteq> f (Suc n)")
apply (simp add:image_def Nset_def)
apply (subgoal_tac "\<forall>x. x \<le> Suc n \<and> f (Suc (Suc n)) = f x \<longrightarrow> False")
apply blast
apply (rule allI) apply (rule impI) apply (erule conjE)
apply (subgoal_tac "0 < Suc (Suc n)") prefer 2 apply simp
apply (frule_tac f = f and i = x in d_gchainTr2 [of "G" "Suc ((Suc n))" 
                              _ _ "Suc (Suc n)"], assumption+)
 apply (simp add:Nset_def) 
 apply (simp add:Nset_def)
 apply simp
apply (frule_tac f = f and i = x in d_gchainTr2 [of "G" "Suc (Suc n)" 
                              _ _ "Suc n"], assumption+)
apply (simp add:Nset_def)
apply (simp add:Nset_def)
apply assumption
apply (frule sym) apply (thin_tac "f (Suc (Suc n)) = f x")
apply simp
done

lemma length_wcmpser0_4:"\<lbrakk>group G; Ugp E; w_cmpser G (Suc 0) f\<rbrakk> \<Longrightarrow>
  card (f ` Nset (Suc 0)) - 1 =
           Suc 0 - card {i. i \<in> Nset 0 \<and> Qw_cmpser G f i \<cong> E}"
apply (subst length_wcmpser0_0, assumption+)
apply (case_tac "Qw_cmpser G f 0 \<cong> E")
 apply (frule_tac n = 0 and f = f and i = 0 in length_wcmpser0_1 [of "G" "E"], assumption+) apply (simp add:Nset_def) apply assumption apply simp
 apply (simp add:Nset_def)
 apply (subgoal_tac "{i. i = 0 \<and> Qw_cmpser G f i \<cong> E} = {0}")
 apply simp
 apply (rule equalityI)
  apply (rule subsetI) apply (simp add:CollectI)
  apply (rule subsetI) apply (simp add:CollectI)
 apply (frule_tac f = f and i = 0 in length_wcmpser0_2 [of "G" "E" "0"], 
                                                        assumption+)
  apply (simp add:Nset_def) apply assumption
 apply (subgoal_tac "finite {f (Suc 0)}") prefer 2 apply (simp add:finite1)
 apply (subgoal_tac "f 0 \<notin> {f (Suc 0)}")
 apply (simp add: card_insert_disjoint [of "{f (Suc 0)}" "f 0"])
 prefer 2 apply simp  apply (simp add:Nset_def) 
 apply (subgoal_tac "card {i. i = 0 \<and> Qw_cmpser G f i \<cong> E} = 0")
 apply simp
 apply (subgoal_tac "{i. i = 0 \<and> Qw_cmpser G f i \<cong> E} = {}")
 apply (frule_tac A = "{i. i = 0 \<and> Qw_cmpser G f i \<cong> E}" and B = "{}" in card_eq) 
 apply simp  apply (rule equalityI)  apply (rule subsetI) 
apply (simp add:CollectI) apply (erule conjE)
 apply simp  apply simp
done

lemma length_wcmpser0_5:" \<lbrakk>group G; Ugp E; w_cmpser G (Suc (Suc n)) f; 
w_cmpser G (Suc n) f; card (f ` Nset (Suc n)) - 1 =  Suc n - 
card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}; Qw_cmpser G f (Suc n) \<cong> E\<rbrakk> \<Longrightarrow>
 card (f ` Nset (Suc (Suc n))) - 1 =
             Suc (Suc n) - card {i. i \<in> Nset (Suc n) \<and> Qw_cmpser G f i \<cong> E}"
apply (frule_tac n = "Suc n" and f = f and i = "Suc n" in 
                            length_wcmpser0_1 [of "G" "E"], assumption+)
 apply (simp add:Nset_def) apply assumption
apply (subgoal_tac "f ` Nset (Suc (Suc n)) = f ` Nset (Suc n)")
 apply simp
prefer 2  apply (rule equalityI) 
 apply (simp add:image_def)
 apply (auto del:equalityI)
 apply (case_tac "xa = Suc (Suc n)")  apply simp 
 apply (thin_tac " xa = Suc (Suc n)") apply (rotate_tac -2)
 apply (frule sym) apply (thin_tac "f (Suc n) = f (Suc (Suc n))")
 apply simp apply (thin_tac "f (Suc (Suc n)) = f (Suc n)")
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply blast
  apply (simp add:Nset_def) 
 apply (frule_tac x = xa and n = "Suc n" in Nset_pre, assumption+)
 apply blast 
 apply (simp add:Nset_def)
apply (subgoal_tac "{i. i \<in> Nset (Suc n) \<and> Qw_cmpser G f i \<cong> E} =
              insert (Suc n) {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
apply simp
apply (subgoal_tac "(Suc n) \<notin> {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
apply (subgoal_tac "finite {i. i \<in> Nset n \<and> Qw_cmpser G  f i \<cong> E}")
apply (subst card_insert_disjoint)
 apply assumption+ apply simp
apply (subgoal_tac "finite (Nset n)") prefer 2 apply (simp add:finite_Nset)
apply (subgoal_tac "{i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E} \<subseteq> Nset n")
apply (rule finite_subset, assumption+)
apply (rule subsetI) apply (simp add:CollectI)
apply (simp add:Nset_def) 
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI) 
 apply (thin_tac "card (f ` Nset (Suc n)) - Suc 0 =
          Suc n - card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 apply (thin_tac "f ` Nset (Suc (Suc n)) = f ` Nset (Suc n)")
 apply (erule conjE) apply (simp add:Nset_def)
 apply (case_tac "x = Suc n") apply simp 
 apply (frule_tac m = x and n = "Suc n" in noteq_le_less, assumption+)
 apply (frule_tac x = x and n = "Suc n" in less_le_diff) apply simp
 apply (rule subsetI) 
 apply (thin_tac "card (f ` Nset (Suc n)) - Suc 0 =
          Suc n - card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 apply (thin_tac "f ` Nset (Suc (Suc n)) = f ` Nset (Suc n)")
 apply (simp add:Nset_def)
 apply (case_tac "x = Suc n") apply simp apply simp
 apply (erule conjE) apply simp 
done


lemma length_wcmpser0_6:"\<lbrakk>group G; w_cmpser G (Suc (Suc n)) f\<rbrakk> \<Longrightarrow> 
                                          0 < card (f ` Nset (Suc n))"
apply (insert finite_Nset [of "Suc n"])
apply (frule finite_imageI [of "Nset (Suc n)" "f"])
apply (subgoal_tac "{f 0} \<subseteq> f ` ( Nset (Suc n))")
apply (frule card_mono [of "f ` (Nset (Suc n))" "{f 0}"], assumption+)
apply (simp add:card1 [of "f 0"])
apply (rule subsetI) apply (simp add:image_def)
apply (subgoal_tac "0 \<in> Nset (Suc n)") apply blast
apply (simp add:Nset_def)
done

lemma length_wcmpser0_7:"\<lbrakk>group G; w_cmpser G (Suc (Suc n)) f\<rbrakk> \<Longrightarrow>
                     card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E} \<le> Suc n"
apply (insert finite_Nset [of "n"])
apply (subgoal_tac "{i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E} \<subseteq> Nset n")
apply (frule card_mono [of "Nset n" "{i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}"])
 apply assumption  apply (simp add:card_Nset)
apply (rule subsetI) apply (simp add:CollectI)
done


lemma length_wcmpser0:"\<lbrakk>group G; Ugp E\<rbrakk> \<Longrightarrow>\<forall>f. w_cmpser G (Suc n) f \<longrightarrow>  
card (f ` (Nset (Suc n))) - 1 = (Suc  n) - (card {i. i \<in> Nset n \<and> 
                                      ((Qw_cmpser G f) i \<cong> E)})"
apply (induct_tac n)  
 (*** n = 0 ***)
apply (rule allI) apply (rule impI)  
apply (rule length_wcmpser0_4, assumption+)
  (**** n ****)
 apply (rule allI) apply (rule impI)
 apply (frule_tac n = "Suc n" and f = f in w_cmpser_pre [of "G"], assumption+)
 apply (subgoal_tac "card (f ` Nset (Suc n)) - 1 =
                 Suc n - card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 prefer 2 apply simp
 apply (thin_tac " \<forall>f. w_cmpser G (Suc n) f \<longrightarrow>
                 card (f ` Nset (Suc n)) - 1 =
                 Suc n - card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
apply (case_tac "Qw_cmpser G f (Suc n) \<cong> E")  
apply (rule length_wcmpser0_5, assumption+)
apply (frule_tac n = "Suc n" and f = f and i = "Suc n" in 
                            length_wcmpser0_2 [of "G" "E"], assumption+)
 apply (simp add:Nset_def) apply assumption
 apply (subgoal_tac "f ` Nset (Suc (Suc n)) = 
                       insert (f (Suc (Suc n))) (f ` (Nset (Suc n)))")
 apply simp apply (thin_tac "f ` Nset (Suc (Suc n)) =
             insert (f (Suc (Suc n))) (f ` Nset (Suc n))")
 apply (subgoal_tac "finite (f ` (Nset (Suc n)))")
 apply (subgoal_tac "f (Suc (Suc n)) \<notin> f ` (Nset (Suc n))")
 apply (subst card_insert_disjoint, assumption) 
 apply assumption
 prefer 2  apply (rule length_wcmpser0_3, assumption+)
 prefer 2
  apply (subgoal_tac "finite (Nset (Suc n))")
  apply (rule finite_imageI, assumption+) apply (simp add:finite_Nset)
 prefer 2 
 apply (thin_tac " \<not> Qw_cmpser G f (Suc n) \<cong> E")
 apply (thin_tac " w_cmpser G (Suc n) f")
 apply (thin_tac "f (Suc n) \<noteq> f (Suc (Suc n))")
 apply (subgoal_tac "Nset (Suc (Suc n)) = Nset (Suc n) \<union> {Suc (Suc n)}")
 prefer 2 apply (rule_tac n = "Suc n" in Nset_un) apply simp
 apply (subgoal_tac "card {i. i \<in> Nset (Suc n) \<and> Qw_cmpser G f i \<cong> E} =
                        card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 apply simp 
 apply (thin_tac " card {i. i \<in> Nset (Suc n) \<and> Qw_cmpser G f i \<cong> E} =
             card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 apply (thin_tac "\<not> Qw_cmpser G f (Suc n) \<cong> E")
 apply (thin_tac "f (Suc n) \<noteq> f (Suc (Suc n))") 
 apply (thin_tac "finite (f ` Nset (Suc n))")
 apply (thin_tac "f (Suc (Suc n)) \<notin> f ` Nset (Suc n)")
 apply (frule_tac n = n and f = f in length_wcmpser0_6 [of "G"], assumption+)
 apply (frule_tac n = n and f = f in length_wcmpser0_7 [of "G"], assumption+)
 apply (rule abc_SucTr0, assumption+)
apply (rule card_eq)
 apply (thin_tac "card (f ` Nset (Suc n)) - Suc 0 =
             Suc n - card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 apply (thin_tac "f (Suc n) \<noteq> f (Suc (Suc n))")
 apply (thin_tac "f (Suc (Suc n)) \<notin> f ` Nset (Suc n)")
 apply (subst Nset_un)  apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
 apply (case_tac "x = Suc n") apply simp apply simp
 apply (rule subsetI) apply (simp add:CollectI)
done


lemma length_of_twcmpser:"\<lbrakk>group G; Ugp E; tw_cmpser G (Suc n) f \<rbrakk> \<Longrightarrow> 
length_twcmpser G (Suc n) f = (Suc  n) - (card {i. i \<in> Nset n \<and> ((Qw_cmpser G f) i \<cong> E)})"
apply (unfold length_twcmpser_def)
apply (insert length_wcmpser0 [of "G" "E" "n"])
apply (subgoal_tac "w_cmpser G (Suc n) f") apply (rotate_tac -1)
apply simp  apply simp 
 apply (thin_tac "\<forall>f. w_cmpser G (Suc n) f \<longrightarrow>
           card (f ` Nset (Suc n)) - Suc 0 =
           Suc n - card {i. i \<in> Nset n \<and> Qw_cmpser G f i \<cong> E}")
 apply (simp add:tw_cmpser_def w_cmpser_def) apply (erule conjE)
 apply (thin_tac "\<forall>i\<in>Nset n. f (Suc i) \<lhd> grp G (f i)")
 apply (simp add:td_gchain_def)
done 

lemma JHS_1:"\<lbrakk>group G; Ugp E; compseries G r f; compseries G s g; 0 < r; 0 < s \<rbrakk> \<Longrightarrow> r =  r * s - card {i. i \<in> Nset (r * s - Suc 0) \<and>
            Qw_cmpser G (cmp_rfn G r f s g) i \<cong> E}"
apply (frule_tac r = r and s = s and G = G and f = f and g = g in JHS_Tr0, assumption+)
apply (simp add:wcsr_rfns_def) apply (erule conjE)
apply (frule_tac length_of_twcmpser [of "G" "E" "r * s - Suc 0" "cmp_rfn G r f s g"], assumption+) apply (simp add:mult_commute)
apply (simp add:length_twcmpser_def)
apply (frule rfn_compseries_iM [of "r" "s" "G" "f" "cmp_rfn G r f s g"], assumption+) apply (rule JHS_Tr0 [of "r" "s" "G" "f" "g"], assumption+)
apply (simp add:mult_commute [of "s" "r"])
done

lemma J_H_S:"\<lbrakk>group G; Ugp E; compseries G r f; compseries G s g; 0 < r; 0 < s \<rbrakk>  \<Longrightarrow> r = s"
apply (frule JHS_1 [of "G" "E" "r" "f" "s" "g"], assumption+)
apply (frule JHS_1 [of "G" "E" "s" "g" "r" "f"], assumption+)
apply (frule JHS_Tr1 [of "G" "r" "s" "f" "g"], assumption+)
apply (frule JHS_Tr0 [of "r" "s" "G" "f" "g"], assumption+)
apply (frule JHS_Tr0 [of "s" "r" "G" "g" "f"], assumption+)
 apply (simp add:wcsr_rfns_def) apply (erule conjE)+
 apply (frule tw_cmpser_is_w_cmpser [of "G" "s * r" "cmp_rfn G r f s g"],
                                                        assumption+)
 apply (frule Qw_cmpser [of "G" "s * r - Suc 0" "cmp_rfn G r f s g"]) 
 apply (simp add:rfn_tool25 [of "s" "r"])
 apply (frule tw_cmpser_is_w_cmpser [of "G" "r * s" "cmp_rfn G s g r f"],
                                                        assumption+)
 apply (frule Qw_cmpser [of "G" "r * s - Suc 0" "cmp_rfn G s g r f"]) 
 apply (simp add:rfn_tool25 [of "r" "s"])
 apply (simp add:mult_commute [of "s" "r"])
apply (frule isom_gch_units [of "E" "r * s - Suc 0" 
 "Qw_cmpser G (cmp_rfn G r f s g)" "Qw_cmpser G (cmp_rfn G s g r f)" 
                                               "rtos r s"], assumption+)
prefer 2 apply simp
apply (simp add:Gch_bridge_def)
apply (rule conjI) apply (rule ballI) 
 apply (frule_tac l = l in rtos_hom1 [of "r" "s"], assumption+)
 apply (simp add:mult_commute [of "s" "r"])
apply (rule rtos_inj, assumption+)
done

section "20. Abelian groups"

record 'a AgroupType = "'a Base" + 
  pOp      :: "['a, 'a ] \<Rightarrow> 'a" 
  mOp      :: "'a  \<Rightarrow> 'a"
  zero     :: "'a"

constdefs
 agroup :: "('a, 'more) AgroupType_scheme  \<Rightarrow> bool"
  "agroup G  ==  (pOp G): carrier G \<rightarrow> carrier G \<rightarrow> carrier G \<and> 
  (mOp G) \<in> carrier G \<rightarrow> carrier G \<and> (zero G) \<in>  carrier G  \<and> 
  (\<forall> x \<in> carrier G. \<forall> y \<in> carrier G. \<forall> z \<in> carrier G.
  (pOp G (zero G) x = x)  \<and> (pOp G (mOp G x) x  = zero G) \<and>  
  (pOp G (pOp G x y) z = pOp G (x) (pOp G y z)) \<and>
  (pOp G x y = pOp G y x))"

 b_ag::"('a, 'more) AgroupType_scheme \<Rightarrow>
   \<lparr>carrier:: 'a set, tOp:: ['a, 'a] \<Rightarrow> 'a , iOp:: 'a \<Rightarrow> 'a, one:: 'a \<rparr>"
   "b_ag G == \<lparr>carrier = carrier G, tOp = pOp G, iOp = mOp G,
    one = zero G \<rparr>"

 asubgroup :: "[('a, 'more) AgroupType_scheme, 'a set] \<Rightarrow> bool"
     "asubgroup G H == H \<guillemotleft> (b_ag G)"

constdefs
 ansubgroup :: "[('a, 'more) AgroupType_scheme, 'a set] \<Rightarrow> bool"
     "ansubgroup G N == N \<lhd> (b_ag G)"

constdefs
 aqgrp :: "[('a, 'more) AgroupType_scheme, 'a set] \<Rightarrow> 
         \<lparr> carrier :: 'a set set, pOp :: ['a  set, 'a set] \<Rightarrow> 'a set,
           mOp :: 'a set \<Rightarrow> 'a set, zero :: 'a set \<rparr>"
 
      "aqgrp G H  ==  \<lparr> carrier = set_r_cos (b_ag G) H, 
       pOp = \<lambda>X. \<lambda>Y. (costOp (b_ag G) H X Y), 
	 mOp = \<lambda>X. (cosiOp (b_ag G) H X), zero = H \<rparr>" 

syntax (xsymbols)
  "@ASubG"  :: "['a set, ('a, 'more) AgroupType_scheme] => bool" 
            (infixl "<+" 58)

translations
  "H <+ G" == "asubgroup G H"

syntax 
  "@ABOP1" :: "['a, ('a, 'more) AgroupType_scheme, 'a] \<Rightarrow> 'a" 
                ("(3 _/ +\<^sub>_/ _)" [62,62,63]62)
  "@AIOP1" :: "[('a, 'more) AgroupType_scheme, 'a] \<Rightarrow> 'a" ("(-\<^sub>_/ _)" [64,65]64)
  "@AUNIT1" :: "('a, 'more) AgroupType_scheme \<Rightarrow> 'a" ("'0\<^sub>_" [74]73) 
  
translations
  "x +\<^sub>G y" == "pOp G x y"
  "-\<^sub>G x" == "mOp G x"
  "0\<^sub>G" == "zero G"

lemma ag_carrier_carrier:"agroup G \<Longrightarrow> carrier (b_ag G) = carrier G"
apply (simp add:b_ag_def)
done

lemma ag_pOp_closed:"\<lbrakk>agroup G; x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> 
   pOp G x y \<in> carrier G"
apply (subgoal_tac "pOp G \<in> carrier G \<rightarrow> carrier G \<rightarrow> carrier G")
 apply (subgoal_tac "pOp G x \<in> carrier G \<rightarrow> carrier G")
 apply (thin_tac "pOp G \<in> carrier G \<rightarrow> carrier G \<rightarrow> carrier G")
 apply (simp add:funcset_mem)+  apply (simp add:agroup_def) 
done

lemma ag_mOp_closed:"\<lbrakk>agroup G; x \<in> carrier G\<rbrakk> \<Longrightarrow>  -\<^sub>G x  \<in> carrier G"
apply (subgoal_tac "mOp G \<in> carrier G \<rightarrow> carrier G")
apply (simp add:funcset_mem) apply (simp add:agroup_def)
done

lemma asubg_subset:"\<lbrakk> agroup G; H <+ G \<rbrakk> \<Longrightarrow> H \<subseteq> carrier G"
apply (simp add:asubgroup_def)
apply (subgoal_tac "H \<subseteq> carrier (b_ag G)") prefer 2 
 apply (simp add: subgroup_def  [of "b_ag G" "H"])
 apply (simp add:b_ag_def)
done

lemma ag_pOp_commute:"\<lbrakk> agroup G; x \<in> carrier G; y \<in> carrier G\<rbrakk>  \<Longrightarrow> 
 pOp G x y = pOp G y x"  
apply (simp add:agroup_def)
done

lemma b_ag_group:"agroup G \<Longrightarrow> group (b_ag G)"
apply (unfold group_def)
 apply (simp add:b_ag_def)
apply (simp add:agroup_def)
apply (rule impI) apply (rule ballI) apply (erule conjE)+
apply (subgoal_tac "x +\<^sub>G 0\<^sub>G =  0\<^sub>G +\<^sub>G x")
apply (subgoal_tac "0\<^sub>G +\<^sub>G x = x")
 apply (thin_tac "\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<forall>z\<in>carrier G.  0\<^sub>G +\<^sub>G x = x \<and>
       -\<^sub>G x +\<^sub>G x = 0\<^sub>G \<and> x +\<^sub>G y +\<^sub>G z =  x +\<^sub>G ( y +\<^sub>G z) \<and>  x +\<^sub>G y =  y +\<^sub>G x")
 apply simp  apply blast  apply blast
done

lemma agop_gop:"agroup G  \<Longrightarrow>  tOp (b_ag G) = pOp G"
 apply (simp add:b_ag_def)
done

lemma agiop_giop:"agroup G \<Longrightarrow> iOp (b_ag G) = mOp G"
apply (simp add:b_ag_def)
done

lemma agunit_gone:"agroup G \<Longrightarrow> one (b_ag G) = 0\<^sub>G"
apply (simp add:b_ag_def)
done

lemma ag_pOp_add_r:"\<lbrakk> agroup G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
 a = b \<rbrakk>  \<Longrightarrow> a +\<^sub>G c =  b +\<^sub>G c" 
apply simp
done

lemma ag_add_commute:"\<lbrakk>agroup G; a \<in> carrier G; b \<in> carrier G \<rbrakk> \<Longrightarrow>
                                                  a +\<^sub>G b = b +\<^sub>G a"
apply (simp add:agroup_def)
done

lemma ag_pOp_add_l:"\<lbrakk> agroup G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
 a = b \<rbrakk>  \<Longrightarrow> c +\<^sub>G a =  c +\<^sub>G b" 
apply simp
done

lemma asubg_pOp_closed:"\<lbrakk> agroup G; asubgroup G H; x \<in> H; y \<in> H\<rbrakk>
                           \<Longrightarrow> pOp G x y \<in> H"
apply (simp add:asubgroup_def)
 apply (frule b_ag_group [of "G"])
 apply (frule subg_tOp_closed [of "b_ag G" "H" "x" "y"], assumption+)
apply (frule agop_gop [of "G"]) apply simp
done

lemma asubg_mOp_closed:"\<lbrakk> agroup G; asubgroup G H; x \<in> H\<rbrakk> \<Longrightarrow> mOp G x \<in> H"
apply (simp add:asubgroup_def)
apply (subgoal_tac "carrier G = carrier (b_ag G)") 
 apply (subgoal_tac "mOp G = iOp (b_ag G)") apply simp
 apply (rule subg_iOp_closed)
 apply (simp add:b_ag_group)
 apply assumption+ apply (thin_tac "carrier G = carrier (b_ag G)")
 apply (simp add:b_ag_def)+
done

lemma asubg_subset1:"\<lbrakk> agroup G; asubgroup G H; x \<in> H\<rbrakk> \<Longrightarrow> x \<in> carrier G"
apply (simp add:asubgroup_def)
apply (insert subg_subset1 [of "b_ag G" "H" "x"])
 apply (simp add:b_ag_group) apply (simp add:b_ag_def) 
done

lemma asubg_inc_zero:"\<lbrakk> agroup G; asubgroup G H\<rbrakk> \<Longrightarrow> 0\<^sub>G \<in> H"
apply (simp add:asubgroup_def)
apply (insert one_in_subg [of "b_ag G" "H"])
apply (simp add:b_ag_group) apply (simp add:b_ag_def)
done

lemma ag_inc_zero:"agroup G \<Longrightarrow> 0\<^sub>G \<in> carrier G"
apply (simp add:agroup_def)
done

lemma ag_l_zero:"\<lbrakk> agroup G; x \<in> carrier G \<rbrakk> \<Longrightarrow> 0\<^sub>G +\<^sub>G x = x"
apply (unfold agroup_def) apply blast
done
 
lemma ag_r_zero:"\<lbrakk> agroup G; x \<in> carrier G \<rbrakk> \<Longrightarrow> x +\<^sub>G 0\<^sub>G = x"
apply (subgoal_tac "x +\<^sub>G 0\<^sub>G = 0\<^sub>G +\<^sub>G x")
apply simp apply (rule  ag_l_zero, assumption+)
apply (rule ag_pOp_commute, assumption+) apply (simp add:ag_inc_zero)
done

lemma ag_l_inv1:"\<lbrakk> agroup G; x \<in> carrier G \<rbrakk> \<Longrightarrow> -\<^sub>G x +\<^sub>G x = 0\<^sub>G"
apply (simp add:agroup_def)
done

lemma ag_r_inv1:"\<lbrakk> agroup G; x \<in> carrier G \<rbrakk> \<Longrightarrow> x +\<^sub>G (-\<^sub>G x) = 0\<^sub>G"
apply (frule ag_mOp_closed [of "G" "x"], assumption+)
apply (subgoal_tac "x +\<^sub>G -\<^sub>G x = -\<^sub>G x +\<^sub>G x") apply simp
apply (rule ag_l_inv1, assumption+) 
apply (rule ag_pOp_commute [of "G" "x" "-\<^sub>G x"], assumption+)
done

lemma ag_pOp_assoc:"\<lbrakk> agroup G; x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk> \<Longrightarrow> (x +\<^sub>G y) +\<^sub>G z = x +\<^sub>G (y +\<^sub>G z)"   
apply (simp add:agroup_def)
done

lemma ag_p_inv:"\<lbrakk>agroup G; x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow>
           -\<^sub>G (x +\<^sub>G y) = -\<^sub>G x +\<^sub>G (-\<^sub>G y)"
apply (subgoal_tac "x +\<^sub>G y +\<^sub>G ( -\<^sub>G (x +\<^sub>G y)) = 0\<^sub>G")
apply (subgoal_tac "-\<^sub>G x +\<^sub>G (x +\<^sub>G y +\<^sub>G -\<^sub>G ( x +\<^sub>G y)) = -\<^sub>G x +\<^sub>G 0\<^sub>G")
 apply (frule ag_mOp_closed [of "G" "x"], assumption+)
 apply (frule ag_pOp_closed [of "G" "x" "y"], assumption+)
 apply (frule ag_mOp_closed [of "G" "x +\<^sub>G y"], assumption+)
 apply (thin_tac "x +\<^sub>G y +\<^sub>G -\<^sub>G ( x +\<^sub>G y) = 0\<^sub>G")
 apply (simp add:ag_pOp_assoc [THEN sym, of "G" "-\<^sub>G x" "x +\<^sub>G y" "-\<^sub>G ( x +\<^sub>G y)"])
 apply (simp add:ag_pOp_assoc [THEN sym, of "G" "-\<^sub>G x" "x" "y"]) 
 apply (simp add:ag_l_inv1) apply (simp add:ag_l_zero)
 apply (simp add:ag_r_zero)
 apply (simp add:ag_pOp_commute [of "G" "y" "-\<^sub>G ( x +\<^sub>G y)"])
 apply (subgoal_tac "-\<^sub>G ( x +\<^sub>G y) +\<^sub>G y +\<^sub>G (-\<^sub>G y) = -\<^sub>G x +\<^sub>G (-\<^sub>G y)")
 apply (thin_tac "-\<^sub>G ( x +\<^sub>G y) +\<^sub>G y = -\<^sub>G x")
 apply (frule ag_mOp_closed [of "G" "y"], assumption+) 
 apply (simp add:ag_pOp_assoc [of "G" "-\<^sub>G ( x +\<^sub>G y)" "y" "-\<^sub>G y"])
 apply (simp add:ag_r_inv1) apply (simp add:ag_r_zero)
apply simp apply (simp add:ag_r_inv1)
apply (frule ag_pOp_closed [of "G" "x" "y"], assumption+)
apply (simp add:ag_r_inv1)
done

lemma pOp_assocTr41:"\<lbrakk>agroup G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
 d \<in> carrier G\<rbrakk> \<Longrightarrow> a +\<^sub>G b +\<^sub>G c +\<^sub>G d = a +\<^sub>G b +\<^sub>G (c +\<^sub>G d)"  
apply (subgoal_tac "carrier G = carrier (b_ag G)")
apply (frule_tac agop_gop [of "G", THEN sym])
 apply simp  apply (rule tOp_assocTr41)
 apply (simp add:b_ag_group)
 apply simp+  apply (simp add:b_ag_def)
done

lemma pOp_assocTr42:"\<lbrakk>agroup G; a \<in> carrier G; b \<in> carrier G;
 c \<in> carrier G; d \<in> carrier G\<rbrakk> \<Longrightarrow> a +\<^sub>G b +\<^sub>G c +\<^sub>G d = a +\<^sub>G (b +\<^sub>G c) +\<^sub>G d" 
apply (subgoal_tac "carrier G = carrier (b_ag G)")
apply (frule_tac agop_gop [of "G", THEN sym])
 apply simp
 apply (rule tOp_assocTr42)
 apply (simp add:b_ag_group)
 apply simp+  apply (simp add:b_ag_def)
done

lemma pOp_assocTr43:"\<lbrakk>agroup G; a \<in> carrier G; b \<in> carrier G;
 c \<in> carrier G; d \<in> carrier G\<rbrakk> \<Longrightarrow> a +\<^sub>G b +\<^sub>G (c +\<^sub>G d) = a +\<^sub>G (b +\<^sub>G c) +\<^sub>G d" 
apply (simp add:pOp_assocTr41 [THEN sym])
apply (simp add:pOp_assocTr42)
done

lemma gEQAddcross:
  "\<lbrakk> agroup G; l1 \<in> carrier G; l2 \<in> carrier G;
     r1 \<in> carrier G; r1 \<in> carrier G; l1 = r2; l2 = r1 \<rbrakk>
	\<Longrightarrow> l1 +\<^sub>G l2 = r1 +\<^sub>G  r2";
  apply (simp add:ag_pOp_commute)
  done

lemma ag_eq_sol1:"\<lbrakk> agroup G; a \<in> carrier G; x\<in> carrier G; b\<in> carrier G;
 a +\<^sub>G x = b\<rbrakk> \<Longrightarrow> x = (-\<^sub>G a) +\<^sub>G b"
apply (insert solOfEq1[of "b_ag G" "a" "b" "x"])
apply (simp add:b_ag_group) apply (simp add:b_ag_def)
done

lemma ag_eq_sol2:"\<lbrakk> agroup G; a \<in> carrier G; x\<in> carrier G; b\<in> carrier G;
 x +\<^sub>G a = b\<rbrakk> \<Longrightarrow> x = b +\<^sub>G (-\<^sub>G a)"
apply (insert  solOfEq2[of "b_ag G" "a" "b" "x"])
apply (simp add:b_ag_group) apply (simp add:b_ag_def) 
done

lemma ag_minus_0_eq_0:"agroup G \<Longrightarrow> -\<^sub>G (0\<^sub>G) = 0\<^sub>G"
apply (frule ag_inc_zero)
apply (frule  ag_r_zero [of "G" "0\<^sub>G"])
apply (frule ag_mOp_closed [of "G" "0\<^sub>G"], assumption+)
apply (frule ag_eq_sol2 [of "G" "0\<^sub>G" "0\<^sub>G" "0\<^sub>G"], assumption+)
apply (thin_tac " 0\<^sub>G +\<^sub>G 0\<^sub>G = 0\<^sub>G")
apply (frule ag_mOp_closed [of "G" "0\<^sub>G"], assumption+)
apply (simp add:ag_l_zero)
done

lemma ag_add4_rel:"\<lbrakk>agroup G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
 d \<in> carrier G \<rbrakk> \<Longrightarrow> a +\<^sub>G b +\<^sub>G (c +\<^sub>G d) =  a +\<^sub>G c +\<^sub>G (b +\<^sub>G d)"
apply (subst ag_pOp_assoc) apply assumption+ apply (simp add:ag_pOp_closed)
apply (subgoal_tac "c +\<^sub>G (b +\<^sub>G d) = c +\<^sub>G b +\<^sub>G d") apply simp
apply (subgoal_tac "c +\<^sub>G b = b +\<^sub>G c") apply simp
apply (subgoal_tac "b +\<^sub>G c +\<^sub>G d = b +\<^sub>G (c +\<^sub>G d)")  apply simp
apply (subst ag_pOp_assoc [THEN sym]) apply assumption+ 
apply (simp add:ag_pOp_closed) apply simp
apply (simp add: ag_pOp_assoc) apply (simp add:ag_pOp_commute)
apply (simp add:ag_pOp_assoc [THEN sym])
done

lemma ag_inv_inv:"\<lbrakk> agroup G; x \<in> carrier G \<rbrakk> \<Longrightarrow> -\<^sub>G (-\<^sub>G x) = x"
apply (insert iOp_invinv [of "b_ag G" "x"])
apply (frule b_ag_group)
apply (subgoal_tac "carrier (b_ag G) = carrier G") apply simp
apply (subgoal_tac "iOp (b_ag G) = mOp G") apply simp
apply (simp add:b_ag_def)+
done

lemma ag_inv_zero:"agroup G \<Longrightarrow> -\<^sub>G 0\<^sub>G = 0\<^sub>G"
apply (insert inv_one[of "b_ag G"])
apply (simp add: b_ag_group) apply (simp add:b_ag_def)
done

end
