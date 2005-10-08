(**       Algebra5
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            hikoba@math.cst.nihon-u.ac.jp
                            May 3, 2004.

  chapter 4.  Ring theory (continued)
    section 6.   operation of ideals (continued)
    section 7.   direct product1, general case
    section 8.   Chinese remainder theorem
    section 9.   addition of finite elements of a ring and ideal_multiplication
    section 10.  extension and contraction

  chapter 5. Modules
    section 1.   Basic properties of Modules
    section 2.   injective hom, surjective hom, bijective hom and iverse hom
   **)

theory Algebra5
imports Algebra4
begin

constdefs
 coprime_ideals::"[('a, 'm) RingType_scheme, 'a set, 'a set] \<Rightarrow> bool"
  "coprime_ideals R A B == A \<^bold>+\<^sub>R B = carrier R"

lemma coprime_int_prod:"\<lbrakk> ring R; ideal R A; ideal R B; coprime_ideals R A B\<rbrakk>
       \<Longrightarrow>   A \<inter> B = A \<diamondsuit>\<^sub>R B"
apply (simp add:coprime_ideals_def)
apply (rule equalityI)
 prefer 2
 (**  A \<diamondsuit>\<^sub>R B \<subseteq> A \<inter> B **)
apply (rule subsetI)
 apply (simp add:ideal_prod_def)
 apply (subgoal_tac "{x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> A") apply simp
 apply (subgoal_tac "{x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> B") apply simp
 apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>i\<in>A. \<forall>j\<in>B. xa =  i \<cdot>\<^sub>R j \<longrightarrow> xa \<in> B")
 apply blast apply (thin_tac "\<exists>i\<in>A. \<exists>j\<in>B. xa =  i \<cdot>\<^sub>R j")
 apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (frule ideal_subset, assumption+)
apply (simp add:ideal_ring_multiple)
 apply (thin_tac"\<forall>xa. ideal R xa \<and>{x. \<exists>i\<in>A. \<exists>j\<in>B. x = i \<cdot>\<^sub>R j}\<subseteq>xa \<longrightarrow> x \<in> xa")
 apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>i\<in>A. \<forall>j\<in>B. xa =  i \<cdot>\<^sub>R j \<longrightarrow> xa \<in> A")
 apply blast apply (thin_tac " \<exists>i\<in>A. \<exists>j\<in>B. xa =  i \<cdot>\<^sub>R j")
 apply (rule ballI) apply (rule ballI) apply (rule impI) apply (rotate_tac 2)
apply (frule ideal_subset, assumption+)
 apply (simp add:ideal_ring_multiple1)
 (**  A \<inter> B \<subseteq> A \<diamondsuit>\<^sub>R B **)
apply (subgoal_tac "carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = A \<inter> B")
apply (subgoal_tac "carrier R =  A \<^bold>+\<^sub>R B")
 apply (thin_tac "A \<^bold>+\<^sub>R B = carrier R")
apply (subgoal_tac "carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = (A \<inter> B) \<diamondsuit>\<^sub>R A \<^bold>+\<^sub>R (A \<inter> B) \<diamondsuit>\<^sub>R B")
apply (subgoal_tac " (A \<inter> B) \<diamondsuit>\<^sub>R A \<^bold>+\<^sub>R (A \<inter> B) \<diamondsuit>\<^sub>R B \<subseteq> A \<diamondsuit>\<^sub>R B")
apply simp
apply (subgoal_tac "(A \<inter> B) \<diamondsuit>\<^sub>R A \<subseteq> A \<diamondsuit>\<^sub>R B")
apply (subgoal_tac "(A \<inter> B) \<diamondsuit>\<^sub>R B \<subseteq> A \<diamondsuit>\<^sub>R B")
apply (rule sum_ideals_cont, assumption+)
 apply (rule ideal_prod_ideal, assumption+)
 apply (rule int_ideal, assumption)
 apply assumption+
apply (rule ideal_prod_ideal, assumption+)
 apply (simp add:int_ideal) apply assumption
 apply (simp add:ideal_prod_ideal)
 apply (rule subsetI)
 apply (thin_tac " carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = A \<inter> B")
 apply (thin_tac "carrier R = A \<^bold>+\<^sub>R B")
 apply (thin_tac "carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = (A \<inter> B) \<diamondsuit>\<^sub>R A \<^bold>+\<^sub>R (A \<inter> B) \<diamondsuit>\<^sub>R B")
 apply (simp add:subsetD)
 apply (thin_tac " carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = A \<inter> B")
 apply (thin_tac "carrier R = A \<^bold>+\<^sub>R B")
 apply (thin_tac "carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = (A \<inter> B) \<diamondsuit>\<^sub>R A \<^bold>+\<^sub>R (A \<inter> B) \<diamondsuit>\<^sub>R B")
 apply assumption
 apply (thin_tac " carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = A \<inter> B")
 apply (thin_tac "carrier R = A \<^bold>+\<^sub>R B")
 apply (thin_tac "carrier R \<diamondsuit>\<^sub>R (A \<inter> B)=(A \<inter> B) \<diamondsuit>\<^sub>R A \<^bold>+\<^sub>R (A \<inter> B) \<diamondsuit>\<^sub>R B")

(** (A \<inter> B) \<diamondsuit>\<^sub>R B \<subseteq> A \<diamondsuit>\<^sub>R B **)
apply (rule subsetI)  apply (thin_tac "(A \<inter> B) \<diamondsuit>\<^sub>R A \<subseteq> A \<diamondsuit>\<^sub>R B")
 apply (simp add:ideal_prod_def)
 apply (rule allI) apply (rule impI) apply blast

 apply (thin_tac " carrier R \<diamondsuit>\<^sub>R (A \<inter> B) = A \<inter> B")
 apply (thin_tac "carrier R = A \<^bold>+\<^sub>R B")
 apply (thin_tac "carrier R \<diamondsuit>\<^sub>R (A \<inter> B)=(A \<inter> B) \<diamondsuit>\<^sub>R A \<^bold>+\<^sub>R (A \<inter> B) \<diamondsuit>\<^sub>R B")
 apply (simp add:ideal_prod_def) apply (rule subsetI)
prefer 2
 apply simp
 apply (subgoal_tac " A \<inter> B =  (A \<inter> B) \<diamondsuit>\<^sub>R (A \<^bold>+\<^sub>R B)")
 apply (subgoal_tac "ideal R (A \<inter> B)")
  apply (frule ideal_distrib [of "R" "A \<inter> B"  "A" "B"], assumption+)
 apply simp apply (simp add:int_ideal)
 apply (subgoal_tac "ideal R  (A \<^bold>+\<^sub>R B)")
 apply (subgoal_tac "ideal R (A \<inter> B)")
 apply (subgoal_tac " (A \<^bold>+\<^sub>R B) \<diamondsuit>\<^sub>R (A \<inter> B) =  (A \<inter> B) \<diamondsuit>\<^sub>R (A \<^bold>+\<^sub>R B)")
 apply blast
 apply (rule prod_commute, assumption+)
 apply (simp add:int_ideal)
 apply (simp add:sum_ideals)

prefer 2
 apply (rule sym, assumption+)

prefer 2
 apply (rule id_coprimeTr0, assumption+)
 apply (simp add:int_ideal)

apply auto
 apply (rename_tac X)
 apply (subgoal_tac "{x. \<exists>i\<in>A \<inter> B. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j} \<subseteq> X")
 apply blast
 apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>A \<inter> B. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j} \<subseteq>
  xa \<longrightarrow> x \<in> xa")
apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>i\<in>A \<inter> B. \<forall>j\<in>A. xa =  i \<cdot>\<^sub>R j \<longrightarrow> xa \<in> X")
 apply blast apply (thin_tac "\<exists>i\<in>A \<inter> B. \<exists>j\<in>A. xa =  i \<cdot>\<^sub>R j")
 apply (rule ballI) apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "i \<in> B")
 apply (frule ideal_subset, assumption+) apply (rotate_tac 2)
 apply (frule ideal_subset, assumption+)
 apply (subgoal_tac "xa = j \<cdot>\<^sub>R i") apply (thin_tac "xa =  i \<cdot>\<^sub>R j")
 apply (subgoal_tac "xa \<in> {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j}")
 apply (rule subsetD, assumption+)
 apply simp apply blast
 apply (simp add:ring_tOp_commute)
 apply blast
done

lemma coprime_elems:"\<lbrakk>ring R; ideal R A; ideal R B; coprime_ideals R A B\<rbrakk> \<Longrightarrow>
 \<exists>a\<in>A. \<exists>b\<in>B. a +\<^sub>R b = 1\<^sub>R"
apply (simp add:coprime_ideals_def asettOp_def settOp_def)
apply (subgoal_tac "1\<^sub>R \<in> {z. \<exists>x\<in>A. \<exists>y\<in>B.  GroupType.tOp (b_ag R) x y = z}")
 apply (thin_tac "{z. \<exists>x\<in>A. \<exists>y\<in>B. GroupType.tOp (b_ag R) x y = z} = carrier R")
 apply (simp add:CollectI)
 apply (frule ring_is_ag [of "R"])
 apply (frule agop_gop[of "R"])
apply simp
apply (simp add:b_ag_def)
apply (simp add:ring_one)
done


lemma coprime_elemsTr:"\<lbrakk>ring R; ideal R A; ideal R B; a\<in>A; b\<in>B; a +\<^sub>R b = 1\<^sub>R\<rbrakk>
               \<Longrightarrow> pj R A b = 1\<^sub>(qring R A) \<and> pj R B a = 1\<^sub>(qring R B)"
apply (frule pj_Hom [of "R" "A"], assumption+)
apply (subgoal_tac "ring (qring R A)")
apply (subgoal_tac "ring (qring R B)")
apply (rule conjI)
apply (subgoal_tac "pj R A b = pj R A (a +\<^sub>R b)")
apply simp
apply (rule rHom_one[of "R" "qring R A" "pj R A"], assumption+)
apply (subst ringhom1 [of "R" "qring R A" _ _ "pj R A"] , assumption+)
 apply (simp add:ideal_subset)+
apply (subgoal_tac "pj R A a = 0\<^sub>(qring R A)")
apply simp
apply (subst ag_l_zero)
 apply (simp add:ring_def)
 apply (rule rHom_mem, assumption+)
 apply (simp add:ideal_subset)
 apply simp
apply (subst pj_mem, assumption+)
 apply (simp add: ideal_subset)
 apply (subst ar_coset_same4, assumption+)
 apply (simp add:ideal_subset)
 apply assumption
 apply (simp add:qring_def)

apply (frule pj_Hom [of "R" "B"], assumption+)
apply (subgoal_tac "pj R B a = pj R B (a +\<^sub>R b)")
apply simp
apply (rule rHom_one[of "R" "qring R B" "pj R B"], assumption+)
 apply (thin_tac "a +\<^sub>R b = 1\<^sub>R")
 apply (simplesubst ringhom1 [of "R" "qring R B" _], assumption+)
 apply (simp add:ideal_subset)+
 apply (simp add:pj_Hom)
apply (subgoal_tac "pj R B b = 0\<^sub>(qring R B)")
apply simp
apply (subst ag_r_zero)
 apply (simp add:ring_def)
 apply (frule pj_Hom [of "R" "B"], assumption+)
 apply (rule rHom_mem, assumption+)
 apply (simp add:ideal_subset)
 apply simp
apply (subst pj_mem, assumption+)
 apply (simp add: ideal_subset)
 apply (subst ar_coset_same4, assumption+)
 apply (simp add:ideal_subset)
 apply assumption
 apply (simp add:qring_def)
apply (simp add:qring_ring)+
done

lemma partition_of_unity:"\<lbrakk>ring R; ideal R A; a\<in>A; b\<in> carrier R; a +\<^sub>R b = 1\<^sub>R;
 u \<in> carrier R; v \<in> carrier R\<rbrakk> \<Longrightarrow> pj R A (a \<cdot>\<^sub>R v +\<^sub>R b \<cdot>\<^sub>R u ) = pj R A u"
apply (frule pj_Hom [of "R" "A"], assumption+)
apply (frule ideal_subset [of "R" "A" "a"], assumption+)
apply (frule ring_is_ag)
apply (subgoal_tac "ring (qring R A)")
apply (subgoal_tac "a \<cdot>\<^sub>R v \<in> carrier R")
apply (subgoal_tac "b \<cdot>\<^sub>R u \<in> carrier R")
apply (simp add: ringhom1 [of "R" "qring R A" _ _ "pj R A"])
apply (subgoal_tac "pj R A (a \<cdot>\<^sub>R v) = 0\<^sub>(qring R A)")
apply simp
apply (subst ag_l_zero)
 apply (simp add:ring_def)
 apply (simp add:rHom_mem)
 apply (subgoal_tac "pj R A ( b \<cdot>\<^sub>R u) = (pj R A b) \<cdot>\<^sub>(qring R A) (pj R A u)")
 apply simp
 apply (subgoal_tac "pj R A b = 1\<^sub>(qring R A)")
 apply simp
 apply (rule ring_l_one, assumption+)
 apply (simp add:rHom_mem)
apply (subgoal_tac "pj R A b = pj R A (a +\<^sub>R b)")
 apply simp
 apply (simp add:rHom_one) apply (thin_tac "a +\<^sub>R b = 1\<^sub>R")
 apply (simp add:ringhom1)
 apply (subgoal_tac "pj R A a = 0\<^sub>(qring R A)")
 apply simp
 apply (rule ag_l_zero [of "qring R A" "pj R A b", THEN sym])
  apply (simp add:ring_def)
  apply (simp add:rHom_mem)
  apply (subst pj_mem, assumption+)
  apply (simp add:ar_coset_same4)
  apply (simp add:qring_def)
 apply (simp add:rHom_tOp)
 apply (subgoal_tac "pj R A (a \<cdot>\<^sub>R v) = (a \<cdot>\<^sub>R v) \<uplus>\<^sub>R A")
 apply simp
 apply (subgoal_tac "a \<cdot>\<^sub>R v \<in> A")
 apply (simp add:ar_coset_same4)
 apply (simp add:qring_def)
 apply (simp add:ideal_ring_multiple1)
 apply (simp add:pj_mem)
apply (simp add:ring_tOp_closed)
apply (simp add:ring_tOp_closed)
apply (simp add:qring_ring)
done

lemma coprimes_commute:"\<lbrakk> ring R; ideal R A; ideal R B; coprime_ideals R A B \<rbrakk>
 \<Longrightarrow> coprime_ideals R B A"
apply (simp add:coprime_ideals_def)
apply (simp add:sum_ideals_commute)
done


lemma coprime_surjTr:"\<lbrakk>ring R; ideal R A; ideal R B; coprime_ideals R A B; X \<in> carrier (qring R A); Y \<in> carrier (qring R B) \<rbrakk> \<Longrightarrow> \<exists>r\<in>carrier R. pj R A r = X \<and> pj R B r = Y"
apply (frule qring_ring [of "R" "A"], assumption+)
apply (frule qring_ring [of "R" "B"], assumption+)
apply (frule coprime_elems [of "R" "A" "B"], assumption+)
apply (subgoal_tac "\<forall>a\<in>A. \<forall>b\<in>B.  a +\<^sub>R b = 1\<^sub>R \<longrightarrow> (\<exists>r\<in>carrier R. pj R A r = X \<and> pj R B r = Y )")
apply blast
 apply (thin_tac "\<exists>a\<in>A. \<exists>b\<in>B.  a +\<^sub>R b = 1\<^sub>R")
 apply (rule ballI)+
 apply (rule impI)
apply (simp add:qring_carrier [of "R" "A"])
apply (simp add:qring_carrier [of "R" "B"])
apply (subgoal_tac "\<forall>u\<in>carrier R. \<forall>v\<in>carrier R. u \<uplus>\<^sub>R A = X \<and> v \<uplus>\<^sub>R B = Y  \<longrightarrow> (\<exists>r\<in>carrier R. pj R A r = X \<and> pj R B r = Y)")
apply blast
 apply (thin_tac "\<exists>a\<in>carrier R. a \<uplus>\<^sub>R A = X")
 apply (thin_tac "\<exists>a\<in>carrier R. a \<uplus>\<^sub>R B = Y")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)
apply (subgoal_tac "pj R A (b \<cdot>\<^sub>R u +\<^sub>R (a \<cdot>\<^sub>R v)) = X \<and> pj R B (b \<cdot>\<^sub>R u +\<^sub>R (a \<cdot>\<^sub>R v)) = Y")
apply (subgoal_tac "b \<cdot>\<^sub>R u +\<^sub>R  a \<cdot>\<^sub>R v \<in> carrier R")
apply blast
 apply (frule ring_is_ag)
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:ideal_subset)
 apply assumption
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:ideal_subset)
 apply assumption
apply (rule conjI)
apply (frule pj_Hom [of "R" "A"], assumption+)
 apply (frule_tac h = a in ideal_subset [of "R" "A"], assumption+)
 apply (frule_tac h = b in ideal_subset [of "R" "B"], assumption+)
 apply (frule_tac x = b and y = u in ring_tOp_closed, assumption+)
 apply (frule_tac x = a and y = v in ring_tOp_closed, assumption+)
apply (subgoal_tac "pj R A \<in> aHom R (R /\<^sub>r A)")
 apply (subst aHom_add [of "R" "R /\<^sub>r A" "pj R A"])
  apply (simp add:ring_is_ag [of "R"])
  apply (simp add:qring_ring ring_is_ag) apply assumption+
 apply (subst rHom_tOp [of "R" "R /\<^sub>r A" _ _ "pj R A"], assumption+)
 apply (subst rHom_tOp [of "R" "R /\<^sub>r A" _ _ "pj R A"], assumption+)
 apply (subgoal_tac "pj R A (a +\<^sub>R b) = pj R A (1\<^sub>R)")
 apply (frule ring_is_ag [of "R"])
 apply (frule ring_is_ag [of "R /\<^sub>r A"])
 apply (frule_tac a = a and b = b in aHom_add [of "R" "R /\<^sub>r A" "pj R A"],
                                                      assumption+)
 apply simp
 apply (subgoal_tac "pj R A a = 0\<^sub>(R /\<^sub>r A)")
 apply simp
 apply (subst ring_times_0_x, assumption+) apply (simp add:pj_mem)
 apply (subst qring_carrier, assumption+) apply (simp add:CollectI)
 apply blast
 apply (subst ag_r_zero, assumption+)
 apply (rule ring_tOp_closed, assumption+)
  apply (simp add:rHom_mem)+
 apply (frule_tac x = "pj R A b" in ag_l_zero [of"R /\<^sub>r A"])
 apply (simp add:rHom_mem)
 apply simp apply (rotate_tac -3) apply (frule sym)
 apply (thin_tac "pj R A (1\<^sub>R) = pj R A b") apply simp
 apply (subst rHom_one [of "R" "R /\<^sub>r A" "pj R A"], assumption+)
 apply (subst ring_l_one, assumption+) apply (simp add:pj_mem)
 apply (rotate_tac 13) apply (frule sym) apply (thin_tac "u \<uplus>\<^sub>R A = X")
 apply simp apply (subst qring_carrier, assumption+)  apply (simp add:CollectI)
 apply blast
 apply (simp add:pj_mem)
 apply (frule_tac x = a in pj_mem[of "R" "A"], assumption+)
 apply simp
 apply (frule_tac a = a in ar_coset_same4 [of "R" "A"], assumption+)
 apply (simp add:qring_def) apply simp apply (simp add:rHom_def)
apply (frule pj_Hom [of "R" "B"], assumption+)
 apply (frule_tac h = a in ideal_subset [of "R" "A"], assumption+)
 apply (frule_tac h = b in ideal_subset [of "R" "B"], assumption+)
 apply (frule_tac x = b and y = u in ring_tOp_closed, assumption+)
 apply (frule_tac x = a and y = v in ring_tOp_closed, assumption+)
apply (subgoal_tac "pj R B \<in> aHom R (R /\<^sub>r B)")
 apply (subst aHom_add [of "R" "R /\<^sub>r B" "pj R B"])
  apply (simp add:ring_is_ag [of "R"])
  apply (simp add:qring_ring ring_is_ag) apply assumption+
 apply (subst rHom_tOp [of "R" "R /\<^sub>r B" _ _ "pj R B"], assumption+)
 apply (subst rHom_tOp [of "R" "R /\<^sub>r B" _ _ "pj R B"], assumption+)
 apply (subgoal_tac "pj R B (a +\<^sub>R b) = pj R B (1\<^sub>R)")
 apply (frule ring_is_ag [of "R"])
 apply (frule ring_is_ag [of "R /\<^sub>r B"])
 apply (frule_tac a = a and b = b in aHom_add [of "R" "R /\<^sub>r B" "pj R B"],
                                                      assumption+)
 apply simp
 apply (subgoal_tac "pj R B b = 0\<^sub>(R /\<^sub>r B)")
 apply simp
 apply (subst ring_times_0_x, assumption+) apply (simp add:pj_mem)
 apply (subst qring_carrier, assumption+) apply (simp add:CollectI)
 apply blast
 apply (subst ag_l_zero, assumption+)
 apply (rule ring_tOp_closed, assumption+)
  apply (simp add:rHom_mem)+
 apply (frule_tac x = "pj R B a" in ag_r_zero [of"R /\<^sub>r B"])
 apply (simp add:rHom_mem)
 apply simp apply (rotate_tac -3) apply (frule sym)
 apply (thin_tac "pj R B (1\<^sub>R) = pj R B a") apply simp
 apply (subst rHom_one [of "R" "R /\<^sub>r B" "pj R B"], assumption+)
 apply (subst ring_l_one, assumption+) apply (simp add:pj_mem)
 apply (rotate_tac 14) apply (frule sym) apply (thin_tac "v \<uplus>\<^sub>R B = Y")
 apply simp apply (subst qring_carrier, assumption+)  apply (simp add:CollectI)
 apply blast
 apply (simp add:pj_mem)
 apply (frule_tac x = b in pj_mem[of "R" "B"], assumption+)
 apply simp
 apply (frule_tac a = b in ar_coset_same4 [of "R" "B"], assumption+)
 apply (simp add:qring_def) apply simp apply (simp add:rHom_def)
done

lemma coprime_n_idealsTr0:"\<lbrakk> ring R; ideal R A; ideal R B; ideal R C;
coprime_ideals R A C; coprime_ideals R B C \<rbrakk> \<Longrightarrow> coprime_ideals R (A \<diamondsuit>\<^sub>R B) C"
apply (simp add: coprime_ideals_def [of "R" "A" "C"])
apply (simp add: coprime_ideals_def [of "R" "B" "C"])
apply (subgoal_tac "\<exists>a\<in>A. \<exists>c1\<in>C. a +\<^sub>R c1 = 1\<^sub>R")
apply (subgoal_tac "\<exists>b\<in>B. \<exists>c2\<in>C. b +\<^sub>R c2 = 1\<^sub>R")
 apply (subgoal_tac "\<forall>a\<in>A. \<forall>c1\<in>C.\<forall>b\<in>B. \<forall>c2\<in>C. a +\<^sub>R c1 = 1\<^sub>R \<and> b +\<^sub>R c2 = 1\<^sub>R
   \<longrightarrow>coprime_ideals R (A \<diamondsuit>\<^sub>R B) C")
 apply blast
  apply (thin_tac "\<exists>a\<in>A. \<exists>c1\<in>C.  a +\<^sub>R c1 = 1\<^sub>R")
  apply (thin_tac "\<exists>b\<in>B. \<exists>c2\<in>C.  b +\<^sub>R c2 = 1\<^sub>R")
apply (rule ballI)+
 apply (rule impI)
 apply (erule conjE)
 apply (simp add:coprime_ideals_def)
apply (rule ideal_inc_one, assumption+)
 apply (rule sum_ideals, assumption+)
 apply (rule ideal_prod_ideal, assumption+)
 apply (subgoal_tac "( a +\<^sub>R c1) \<cdot>\<^sub>R ( b +\<^sub>R c2) = 1\<^sub>R")
 apply (subgoal_tac "( a +\<^sub>R c1) \<cdot>\<^sub>R ( b +\<^sub>R c2) \<in>  A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R C")
 apply simp
apply (subst  ring_distrib3, assumption+)
 apply (simp add:ideal_subset)+
 apply (subgoal_tac "ideal R (A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R C)")
 apply (rule ideal_pOp_closed, assumption+)
 apply (rule ideal_pOp_closed, assumption+)
 apply (rule ideal_pOp_closed, assumption+)
apply (frule sum_ideals_la1 [of "R" "A \<diamondsuit>\<^sub>R B" "C"])
 apply (simp add:ideal_prod_ideal)
 apply assumption
 apply (subgoal_tac "a \<cdot>\<^sub>R b \<in> A \<diamondsuit>\<^sub>R B")
 apply (rule subsetD, assumption+)
 apply (simp add:ideal_prod_def)
apply blast
apply (frule sum_ideals_la2 [of "R" "A \<diamondsuit>\<^sub>R B" "C"])
 apply (simp add:ideal_prod_ideal)
 apply assumption
apply (subgoal_tac "a \<in> carrier R") apply (thin_tac "c1 \<in> C")
apply (frule ideal_ring_multiple [of "R" "C" _], assumption+)
 apply (rule subsetD, assumption+)
 apply (simp add:ideal_subset)
apply (subgoal_tac "b \<in> carrier R")
apply (frule ideal_ring_multiple1 [of "R" "C" _], assumption+)
apply (frule sum_ideals_la2 [of "R" "A \<diamondsuit>\<^sub>R B" "C"])
 apply (simp add:ideal_prod_ideal)
 apply assumption
apply (rule subsetD, assumption+)
 apply (simp add:ideal_subset)
apply (frule sum_ideals_la2 [of "R" "A \<diamondsuit>\<^sub>R B" "C"])
 apply (simp add:ideal_prod_ideal)
 apply assumption
apply (subgoal_tac "c2 \<in> carrier R")
apply (frule ideal_ring_multiple1 [of "R" "C" _], assumption+)
 apply (rule subsetD, assumption+)
 apply (simp add:ideal_subset)
apply (rule sum_ideals, assumption+)
 apply (simp add:ideal_prod_ideal)
 apply assumption
apply simp
apply (rule ring_r_one, assumption+)
apply (simp add:ring_def)
 apply (simp add:asettOp_def)
 apply (simp add:settOp_def)
apply (subgoal_tac "1\<^sub>R \<in> {z. \<exists>x\<in>B. \<exists>y\<in>C.  GroupType.tOp (b_ag R) x y = z}")
 apply (thin_tac "{z. \<exists>x\<in>A. \<exists>y\<in>C. GroupType.tOp (b_ag R) x y = z} = carrier R")
 apply (thin_tac "{z. \<exists>x\<in>B. \<exists>y\<in>C. GroupType.tOp (b_ag R) x y = z} = carrier R")
 apply (simp add:CollectI) apply (simp add:b_ag_def)
apply simp
 apply (simp add:ring_def)
 apply (thin_tac "B \<^bold>+\<^sub>R C = carrier R")
apply (simp add:asettOp_def settOp_def)
apply (subgoal_tac "1\<^sub>R \<in> {z. \<exists>x\<in>A. \<exists>y\<in>C.  GroupType.tOp (b_ag R) x y = z}")
 apply (thin_tac " {z. \<exists>x\<in>A. \<exists>y\<in>C. GroupType.tOp (b_ag R) x y = z} = carrier R")
 apply (simp add:CollectI b_ag_def)
apply simp
 apply (simp add:ring_def)
done

lemma coprime_n_idealsTr1:"\<lbrakk>ring R; ideal R C \<rbrakk> \<Longrightarrow>
 (\<forall>k\<in>Nset n. ideal R (J k)) \<and> (\<forall>i\<in>Nset n.  coprime_ideals R (J i) C) \<longrightarrow>  coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) C"
apply (induct_tac n)
apply (rule impI)
apply (erule conjE)
 apply (simp add:Nset_def)

apply (rule impI)
apply (erule conjE)
apply (subgoal_tac "coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) C")
apply simp
apply (subgoal_tac "coprime_ideals R (J (Suc n)) C")
apply (rule coprime_n_idealsTr0, assumption+)
apply (subgoal_tac "\<forall>k\<in>Nset n. ideal R (J k)")
apply (simp add: n_prod_ideal)
 apply (rule ballI) apply (subgoal_tac "k \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def)
 apply assumption+
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def)
apply (subgoal_tac "\<forall>k\<in>Nset n. k \<in> Nset (Suc n)")
apply blast
apply (rule ballI)
apply (simp add:Nset_def)
done

lemma coprime_n_idealsTr2:"\<lbrakk>ring R; ideal R C; (\<forall>k\<in>Nset n. ideal R (J k)); (\<forall>i\<in>Nset n. coprime_ideals R (J i) C) \<rbrakk> \<Longrightarrow> coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) C"
apply (simp add:coprime_n_idealsTr1)
done

lemma coprime_n_idealsTr3:"ring R \<Longrightarrow> (\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> (\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)) \<longrightarrow>  coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) (J (Suc n))"
apply (induct_tac n)
apply (rule impI)
apply (erule conjE)
 apply (subgoal_tac " (i\<Pi>\<^sub>R\<^sub>,\<^sub>0 J) = (J 0)")
 apply simp
apply (subgoal_tac "0 \<in> Nset (Suc 0)")
apply (subgoal_tac "Suc 0 \<in> Nset (Suc 0)") apply (rotate_tac -2)
apply simp apply (simp add:Nset_def) apply (simp add:Nset_def)
apply simp

apply (rule impI)
apply (erule conjE)+
 apply (subgoal_tac "\<forall>k\<in>Nset (Suc n). ideal R (J k)")
 apply (subgoal_tac "\<forall>i\<in>Nset (Suc n).
                     coprime_ideals R (J i) (J (Suc (Suc n)))")
 apply (subgoal_tac "ideal R (J (Suc (Suc n)))")
 apply (rule coprime_n_idealsTr2, assumption+)
 apply (simp add:Nset_def)
 apply (rule ballI)
 apply (subgoal_tac "i \<in> Nset (Suc (Suc n))")
 apply (subgoal_tac "Suc (Suc n) \<in> Nset (Suc (Suc n))")
 apply (rotate_tac -2)
  apply (thin_tac "(\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> (\<forall>i\<in>Nset (Suc n).
  \<forall>j\<in>Nset (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)) \<longrightarrow>
             coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) (J (Suc n))")
  apply (thin_tac "\<forall>k\<in>Nset (Suc (Suc n)). ideal R (J k)")
  apply (thin_tac "\<forall>k\<in>Nset (Suc n). ideal R (J k)")
 apply (subgoal_tac "i \<noteq> Suc (Suc n)")
 apply simp
 apply (simp add:Nset_def)+
done

lemma coprime_n_idealsTr4:"\<lbrakk>ring R; (\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> (\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk> \<Longrightarrow>
   coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) (J (Suc n))"
apply (simp add:coprime_n_idealsTr3)
done


section "7. direct product1, general case"


constdefs
  prod_tOp::"['i set,  'i \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow>
    ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow>  ('i \<Rightarrow> 'a)"
  "prod_tOp I A  == \<lambda>f\<in>carr_prodag I A. \<lambda>g\<in>carr_prodag I A.
                           \<lambda>x\<in>I. (f x) \<cdot>\<^sub>(A x) (g x)"
  (** Let x \<in> I, then A x is a ring, {A x | x \<in> I} is a set of rings. **)

  prod_one::"['i set,  'i  \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a)"
  "prod_one I A == \<lambda>x\<in>I. 1\<^sub>(A x)"
  (** 1\<^sub>(A x) is the unit of a ring A x. **)

constdefs
 prodrg :: "['i set, 'i \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a) RingType"
 "prodrg I A == \<lparr>carrier = carr_prodag I A, pOp = prod_pOp I A, mOp =
  prod_mOp I A, zero = prod_zero I A, tOp = prod_tOp I A,
  one = prod_one I A \<rparr>"
 (** I is the index set **)
syntax
  "@PRODRING" :: "['i set, 'i \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow>
               ('i \<Rightarrow> 'a ) RingType"  ("(r\<Pi>\<^sub>_/ _)" [72,73]72)
translations
  "r\<Pi>\<^sub>I A" == "prodrg I A"

constdefs
 augm_func::"[nat, nat \<Rightarrow> 'a,'a set, nat, nat \<Rightarrow> 'a, 'a set] \<Rightarrow> nat \<Rightarrow> 'a"
  "augm_func n f A m g B == \<lambda>i\<in>Nset (n + m). if i \<le> n then f i else
    if (Suc n) \<le> i \<and> i \<le> n + m then g ((sliden (Suc n)) i) else arbitrary"
 (* Remark. g is a function of Nset (m - 1) \<rightarrow> B *)

 ag_setfunc::"[nat, nat \<Rightarrow> ('a, 'more) RingType_scheme, nat,
nat \<Rightarrow> ('a, 'more)  RingType_scheme] \<Rightarrow> (nat \<Rightarrow> 'a) set \<Rightarrow> (nat \<Rightarrow> 'a) set
 \<Rightarrow> (nat  \<Rightarrow> 'a) set"
"ag_setfunc n B1 m B2 X Y
 == {f. \<exists>g. \<exists>h. (g\<in>X) \<and> (h\<in>Y) \<and> (f = (augm_func n g (Un_carrier (Nset n) B1)
    m h (Un_carrier (Nset (m - 1)) B2)))}"
 (* Later we consider X = ac_Prod_Rg (Nset n) B1 and Y = ac_Prod_Rg (Nset (m - 1)) B2 *)


consts
 ac_fProd_Rg::"[nat, nat \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow>
                 (nat \<Rightarrow> 'a) set"

primrec
 fprod_0: "ac_fProd_Rg 0 B = carr_prodag (Nset 0) B"
 frpod_n: "ac_fProd_Rg (Suc n) B = ag_setfunc n B (Suc 0) (compose (Nset 0)
 B (slide (Suc n))) (carr_prodag (Nset n) B) (carr_prodag (Nset 0) (compose (Nset 0) B (slide (Suc n))))"

constdefs
 prodB1 :: "[('a, 'm) RingType_scheme, ('a, 'm) RingType_scheme] \<Rightarrow>
                 (nat \<Rightarrow> ('a, 'm) RingType_scheme)"
  "prodB1 R S == \<lambda>k. if k=0 then R else if k=Suc 0 then S else
                 arbitrary"

 Prod2Rg :: "[('a, 'm) RingType_scheme, ('a, 'm) RingType_scheme]
              \<Rightarrow> (nat \<Rightarrow> 'a) RingType" (infixl "\<Oplus>~" 80)
  "A1 \<Oplus>~ A2 == prodrg (Nset (Suc 0)) (prodB1 A1 A2)"

text {* Don't try (Prod_ring (Nset n) B) \<Oplus>~ (B (Suc n)) *}

lemma prod_tOp_func:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
    prod_tOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A \<rightarrow> carr_prodag I A"
apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (subst carr_prodag_def) apply (simp add:CollectI)
apply (rule conjI)
 apply (simp add:prod_tOp_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:Un_carrier_def)
apply (subgoal_tac "prod_tOp I A a b x \<in> carrier (A x)")
 apply blast
 apply (simp add:prod_tOp_def)
 apply (rule ring_tOp_closed)
  apply simp
  apply (simp add:carr_prodag_def)
  apply (simp add:carr_prodag_def)
 apply (rule ballI)
 apply (simp add:prod_tOp_def)
 apply (rule ring_tOp_closed)
 apply simp apply (simp add:carr_prodag_def)+
done

lemma prod_tOp_mem:"\<lbrakk>\<forall>k\<in>I. ring (A k); X \<in> carr_prodag I A;
 Y \<in> carr_prodag I A\<rbrakk> \<Longrightarrow> prod_tOp I A X Y \<in> carr_prodag I A"
apply (frule prod_tOp_func)
apply (subgoal_tac "prod_tOp I A X \<in> carr_prodag I A \<rightarrow> carr_prodag I A")
apply (thin_tac "prod_tOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A
                                 \<rightarrow> carr_prodag I A")
apply (simp add: funcset_mem)
apply (simp add: funcset_mem)
done

lemma prod_one_func:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
                           prod_one I A \<in> carr_prodag I A"
apply (simp add:prod_one_def carr_prodag_def)
apply (rule conjI)
apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Un_carrier_def)
 apply (subgoal_tac "1\<^sub>(A x) \<in> carrier (A x)")
 apply blast
 apply (rule ring_one) apply simp
apply (rule ballI)
 apply (rule ring_one) apply simp
done


lemma prodrg_ring:"\<forall>k\<in>I. ring (A k) \<Longrightarrow> ring (prodrg I A)"
apply (subst ring_def)
 apply (rule conjI)
 apply (subgoal_tac "\<forall>k\<in>I. agroup (A k)")
 apply (frule prodag_agroup [of "I" "A"])
 apply (subst agroup_def)
 apply (subgoal_tac "carrier (r\<Pi>\<^sub>I A) = carrier (a\<Pi>\<^sub>I A)") apply simp
 apply (subgoal_tac "pOp (r\<Pi>\<^sub>I A) =  pOp (a\<Pi>\<^sub>I A)")  apply simp
 apply (subgoal_tac "mOp (r\<Pi>\<^sub>I A) =  mOp (a\<Pi>\<^sub>I A)")  apply simp
 apply (subgoal_tac "zero (r\<Pi>\<^sub>I A) = zero (a\<Pi>\<^sub>I A)") apply simp
 apply (simp add:agroup_def) apply (fold agroup_def)
apply (rule impI) apply (rule ballI) apply (simp add:ag_r_zero)
 apply (simp add:prodag_def prodrg_def)
 apply (simp add:prodag_def prodrg_def)
 apply (simp add:prodag_def prodrg_def)
 apply (simp add:prodag_def prodrg_def)
apply (rule ballI)
 apply (rule ring_is_ag) apply simp
 apply (rule conjI)
  apply (simp add:prodrg_def)
  apply (simp add:prod_tOp_func)
 apply (rule conjI)
  apply (simp add:prodrg_def prod_one_func)
apply (rule ballI)+
 apply (simp add:prodrg_def)
apply (subgoal_tac "\<forall>k\<in>I. agroup (A k)") prefer 2 apply (rule ballI)
 apply (rule ring_is_ag) apply simp
apply (rule conjI)
 apply (frule prod_one_func[of "I" "A"])
 apply (frule_tac X = "prod_one I A" and Y = x in prod_tOp_mem, assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (rule ballI) apply (simp add:prod_one_def)
 apply (simp add:prod_tOp_def)
 apply (rule ring_l_one) apply simp apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (frule_tac X = y and Y = z in prod_pOp_mem, assumption+)
 apply (frule_tac X = x and Y = "prod_pOp I A y z" in prod_tOp_mem,
                                                        assumption+)
 apply (frule_tac X = x and Y = y in prod_tOp_mem, assumption+)
 apply (frule_tac X = x and Y = z in prod_tOp_mem, assumption+)
 apply (frule_tac X = "(prod_tOp I A x y)" and Y = "(prod_tOp I A x z)" in prod_pOp_mem, assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (rule ballI)
 apply (simp add:prod_pOp_def prod_tOp_def)
 apply (rule ring_distrib1) apply simp apply (simp add:carr_prodag_def)
 apply (simp add:carr_prodag_def) apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (frule_tac X = x and Y = y in prod_tOp_mem, assumption+)
 apply (frule_tac X = "prod_tOp I A x y" and Y = z in prod_tOp_mem,
                                                              assumption+)
 apply (frule_tac X = y and Y = z in prod_tOp_mem, assumption+)
 apply (frule_tac X = x and Y = "prod_tOp I A y z" in prod_tOp_mem,
                                                            assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (rule ballI) apply (simp add:prod_tOp_def)
 apply (rule ring_tOp_assoc) apply simp
  apply (simp add:carr_prodag_def)
  apply (simp add:carr_prodag_def)
  apply (simp add:carr_prodag_def)
apply (frule_tac X = x and Y = y in prod_tOp_mem, assumption+)
 apply (frule_tac X = y and Y = x in prod_tOp_mem, assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (rule ballI) apply (simp add:prod_tOp_def)
 apply (rule ring_tOp_commute) apply simp
 apply (simp add:carr_prodag_def)+
done

lemma prodrg_carrier:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
         carrier (prodrg I A) = carr_prodag I A"
apply (simp add:prodrg_def)
done

lemma prodrg_elem_extensional:"\<lbrakk>\<forall>k\<in>I. ring (A k); f \<in> carrier (prodrg I A)\<rbrakk> \<Longrightarrow>
         f \<in> extensional I"
apply (simp add:prodrg_carrier)
apply (simp add:carr_prodag_def)
done

lemma prodrg_pOp:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
                  pOp (prodrg I A) = prod_pOp I A"
apply (simp add:prodrg_def)
done

lemma prodrg_mOp:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
                  mOp (prodrg I A) = prod_mOp I A"
apply (simp add:prodrg_def)
done

lemma prodrg_zero:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
                  zero (prodrg I A) = prod_zero I A"
apply (simp add:prodrg_def)
done

lemma prodrg_tOp:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
                  tOp (prodrg I A) = prod_tOp I A"
apply (simp add:prodrg_def)
done

lemma prodrg_one:"\<forall>k\<in>I. ring (A k) \<Longrightarrow>
                  one (prodrg I A) = prod_one I A"
apply (simp add:prodrg_def)
done


lemma prodrg_sameTr5:"\<lbrakk>\<forall>k\<in>I. ring (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_tOp I A = prod_tOp I B"
apply (frule prod_tOp_func)
apply (subgoal_tac "carr_prodag I A = carr_prodag I B") apply simp
apply (frule prod_tOp_func [of "I" "B"])
 apply (rule funcset_eq [of _ "carr_prodag I B" _])
 apply (simp add:prod_tOp_def extensional_def)
 apply (simp add:prod_tOp_def extensional_def)
apply (rule ballI)
 apply (frule_tac x = x in funcset_mem [of "prod_tOp I A" "carr_prodag I B"
 "carr_prodag I B \<rightarrow> carr_prodag I B"], assumption+)
 apply (frule_tac x = x in funcset_mem [of "prod_tOp I B" "carr_prodag I B"
 "carr_prodag I B \<rightarrow> carr_prodag I B"], assumption+)
 apply (thin_tac " prod_tOp I A
           \<in> carr_prodag I B \<rightarrow> carr_prodag I B \<rightarrow> carr_prodag I B")
 apply (thin_tac "prod_tOp I B
           \<in> carr_prodag I B \<rightarrow> carr_prodag I B \<rightarrow> carr_prodag I B")
 apply (rule funcset_eq [of _ "carr_prodag I B"])
 apply (simp add:prod_tOp_def extensional_def)
 apply (simp add:prod_tOp_def extensional_def)
apply (rule ballI)
 apply (frule_tac f = "prod_tOp I A x" and A = "carr_prodag I B" and
         x = xa in funcset_mem, assumption+)
 apply (frule_tac f = "prod_tOp I B x" and A = "carr_prodag I B" and
         x = xa in funcset_mem, assumption+)
 apply (subgoal_tac "\<forall>k\<in>I. agroup (B k)")
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule ballI) apply (simp add:prod_tOp_def) apply (rule ballI)
 apply (rule ring_is_ag) apply simp
apply (subgoal_tac "\<forall>k\<in>I. agroup (A k)")
 apply (simp add:prodag_sameTr1)
 apply (rule ballI)  apply (rule ring_is_ag) apply simp
done

lemma prodrg_sameTr6:"\<lbrakk>\<forall>k\<in>I. ring (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_one I A = prod_one I B"
apply (frule prod_one_func [of "I" "A"])
apply simp
apply (subgoal_tac "\<forall>k\<in>I. agroup (A k)")
apply (frule prod_one_func [of "I" "B"])
apply (frule prodag_sameTr1[of "I" "A" "B"], assumption+) apply simp
apply (rule carr_prodag_mem_eq, assumption+)
apply (rule ballI)
apply (simp add:prod_one_def)
apply (rule ballI) apply (rule ring_is_ag) apply simp
done

lemma prodrg_same:"\<lbrakk>\<forall>k\<in>I. ring (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prodrg I A = prodrg I B"
apply (subgoal_tac "\<forall>k\<in>I. agroup (A k)")
apply (frule prodag_sameTr1, assumption+)
apply (frule prodag_sameTr2, assumption+)
apply (frule prodag_sameTr3, assumption+)
apply (frule prodag_sameTr4, assumption+)
apply (frule prodrg_sameTr5, assumption+)
apply (frule prodrg_sameTr6, assumption+)
apply (simp add:prodrg_def)
apply (rule ballI) apply (rule ring_is_ag) apply simp
done

lemma project_rhom:"\<lbrakk>\<forall>k\<in>I. ring (A k); j \<in> I\<rbrakk> \<Longrightarrow>
                         PRoject I A j \<in> rHom ( prodrg I A) (A j)"
apply (simp add:rHom_def)
 apply (subgoal_tac "\<forall>k\<in>I. agroup (A k)")
 apply (frule project_aHom [of "I" "A" "j"], assumption+)
 apply (rule conjI)
 apply (subst aHom_def)
 apply (simp add:prodrg_def)
 apply (simp add:aHom_def) apply (simp add:prodag_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule prodrg_ring [of "I" "A"])
 apply (frule_tac x = x and y = y in ring_tOp_closed [of "r\<Pi>\<^sub>I A"],
                                                         assumption+)
 apply (simp add:prodrg_carrier)
 apply (simp add:PRoject_def)
 apply (simp add:prodrg_def) apply (fold prodrg_def)
 apply (simp add:prod_tOp_def)
apply (frule prodrg_ring [of "I" "A"])
apply (frule ring_one[of "r\<Pi>\<^sub>I A"])
 apply (simp add:prodrg_carrier)
 apply (simp add:PRoject_def) apply (simp add:prodrg_def)
 apply (fold prodrg_def) apply (simp add:prod_one_def)
apply (rule ballI)
 apply (rule ring_is_ag) apply simp
done

lemma augm_funcTr:"\<lbrakk>\<forall>k\<in>Nset (Suc n). ring (B k); f \<in> carr_prodag (Nset (Suc n)) B\<rbrakk> \<Longrightarrow> f = augm_func n (restrict f (Nset n)) (Un_carrier (Nset n) B) (Suc 0)  (\<lambda>x\<in>Nset 0. f (x + Suc n)) (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n))))"
apply (subgoal_tac "\<forall>k\<in>Nset (Suc n). agroup (B k)")
apply (rule carr_prodag_mem_eq [of "Nset (Suc n)" "B" "f" "augm_func n (restrict f (Nset n)) (Un_carrier (Nset n) B) (Suc 0) (\<lambda>x\<in>Nset 0. f (x + Suc n)) (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n))))"], assumption+)
apply (simp add:augm_func_def)
 apply (simp add:carr_prodag_def)
 apply (rule conjI) apply (simp add:Pi_def[of "Nset (Suc n)"])
 apply (rule allI) apply (rule conjI) apply (rule impI)
 apply (simp add:Nset_def)
 apply (rule impI) apply (rule conjI) apply (rule impI)
 apply (simp add:sliden_def) apply (simp add:Nset_def)
 apply (rule impI) apply (simp add:Nset_def sliden_def)
apply (rule ballI) apply (simp add:Nset_def) apply (rule impI)
 apply (subgoal_tac "i = Suc n") apply (simp add:sliden_def) apply simp
apply (rule ballI)
 apply (simp add:augm_func_def) apply (simp add:Nset_def sliden_def)
 apply (rule impI)
 apply (subgoal_tac "l = Suc n") apply simp apply simp
 apply (rule ballI) apply (rule ring_is_ag) apply simp
done

lemma A_to_prodag_mem:"\<lbrakk>ring A; \<forall>k\<in>I. ring (B k);  \<forall>k\<in>I. (S k) \<in>
 rHom A (B k); x \<in> carrier A \<rbrakk> \<Longrightarrow> A_to_prodag A I S B x \<in> carr_prodag I B"
apply (simp add:carr_prodag_def)
apply (rule conjI)
apply (simp add:A_to_prodag_def extensional_def)
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add: A_to_prodag_def)
 apply (subgoal_tac "(S xa) \<in> rHom A (B xa)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. S k \<in> rHom A (B k)")
 apply (frule_tac f = "S xa" and A = A and R = "B xa" in rHom_mem, assumption+)
 apply (simp add:Un_carrier_def) apply blast
apply (rule ballI)
apply (subgoal_tac "(S i) \<in> rHom A (B i)") prefer 2 apply simp
apply (frule_tac f = "S i" and A = A and R = "B i" in rHom_mem, assumption+)
apply (simp add:A_to_prodag_def)
done

lemma A_to_prodag_rHom:"\<lbrakk>ring A; \<forall>k\<in>I. ring (B k); \<forall>k\<in>I. (S k) \<in>
 rHom A (B k) \<rbrakk>  \<Longrightarrow> A_to_prodag A I S B \<in> rHom A (r\<Pi>\<^sub>I B)"
apply (simp add:rHom_def [of "A" "r\<Pi>\<^sub>I B"])
apply (rule conjI)
 apply (subst aHom_def)
 apply (simp add:CollectI)
 apply (simp add:prodrg_carrier)
 apply (subgoal_tac "\<forall>k\<in>I. agroup (B k)")
 apply (subgoal_tac "\<forall>k\<in>I. S k \<in> aHom A (B k)")
 apply (frule ring_is_ag)
 apply (frule A_to_prodag_aHom [of "A" "I" "B" "S"], assumption+)
 apply (rule conjI)
 apply (simp add:aHom_def prodag_def)
 apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule ballI)+
 apply (subst aHom_add [of "A" "a\<Pi>\<^sub>I B" "A_to_prodag A I S B"], assumption+)
 apply (simp add:prodag_agroup) apply assumption+
 apply (simp add:prodag_pOp prodrg_pOp)
apply (rule ballI) apply (subgoal_tac "S k \<in> rHom A (B k)")
 prefer 2 apply simp apply (simp add:rHom_def)
 apply (rule ballI) apply (rule ring_is_ag) apply simp
apply (rule conjI)
 apply (rule ballI)+
 apply (frule_tac x = x and y = y in ring_tOp_closed [of "A"], assumption+)
 apply (frule_tac x = "x \<cdot>\<^sub>A y" in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                    assumption+)
 apply (frule_tac x = x in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                    assumption+)
 apply (frule_tac x = y in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                    assumption+)
 apply (frule prodrg_ring [of "I" "B"])
 apply (frule_tac x = "A_to_prodag A I S B x" and
  y = "A_to_prodag A I S B y" in ring_tOp_closed [of "r\<Pi>\<^sub>I B"])
 apply (simp add:prodrg_carrier)+
 apply (subgoal_tac "\<forall>k\<in>I. agroup (B k)")
 apply (rule carr_prodag_mem_eq [of "I" "B"], assumption+)
 apply (rule ballI)
 apply (simp add:A_to_prodag_def)
 apply (simp add:prodrg_def) apply (fold prodrg_def)
 apply (simp add:prod_tOp_def)
 apply (subgoal_tac "ring (B l)") prefer 2 apply simp
 apply (subgoal_tac "S l \<in> rHom A (B l)")
 apply (simp add:rHom_tOp) apply simp
apply (rule ballI)
 apply (rule ring_is_ag) apply simp
apply (frule ring_one)
 apply (frule A_to_prodag_mem [of "A" "I" "B" "S" "1\<^sub>A"], assumption+)
 apply (frule prodrg_ring [of "I" "B"])
 apply (frule ring_one [of "r\<Pi>\<^sub>I B"])
 apply (simp add:prodrg_carrier)
 apply (rule carr_prodag_mem_eq [of "I" "B"])
 apply (rule ballI) apply (rule ring_is_ag) apply simp
 apply (simp add:A_to_prodag_mem) apply assumption
apply (rule ballI)
 apply (simp add:A_to_prodag_def)
 apply (simp add:prodrg_def) apply (fold prodrg_def)
 apply (simp add:prod_one_def)
 apply (subgoal_tac "S l \<in> rHom A (B l)")
 apply (rule rHom_one, assumption+) apply simp
 apply simp apply simp
done

lemma ac_fProd_ProdTr1:"\<lbrakk>\<forall>k\<in>Nset (Suc n). ring (B k)\<rbrakk> \<Longrightarrow>
 ag_setfunc n B (Suc 0) (compose (Nset 0) B (slide (Suc n))) (carr_prodag (Nset n) B) (carr_prodag (Nset 0) (compose (Nset 0) B (slide (Suc n)))) \<subseteq>  carr_prodag (Nset (Suc n)) B"
apply (rule subsetI)
apply (simp add:ag_setfunc_def)
apply (subgoal_tac " \<forall>g. g \<in> carr_prodag (Nset n) B \<and>
 (\<exists>h. h \<in> carr_prodag (Nset 0) (compose (Nset 0) B (slide (Suc n))) \<and>
 x = augm_func n g (Un_carrier (Nset n) B) (Suc 0) h (Un_carrier (Nset 0)
 (compose (Nset 0) B (slide (Suc n))))) \<longrightarrow>  x \<in> carr_prodag (Nset (Suc n)) B")
apply blast
apply (thin_tac "\<exists>g. g \<in> carr_prodag (Nset n) B \<and>
 (\<exists>h. h \<in> carr_prodag (Nset 0) (compose (Nset 0) B (slide (Suc n))) \<and>
 x = augm_func n g (Un_carrier (Nset n) B) (Suc 0) h (Un_carrier (Nset 0)
 (compose (Nset 0) B (slide (Suc n)))))")
apply (rule allI) apply (rule impI) apply (erule conjE)
apply (subgoal_tac "\<forall>h. h \<in> carr_prodag (Nset 0) (compose (Nset 0) B (slide (Suc n))) \<and> x =  augm_func n g (Un_carrier (Nset n) B) (Suc 0) h (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n)))) \<longrightarrow>  x \<in> carr_prodag (Nset (Suc n)) B") apply blast
apply (thin_tac  "\<exists>h. h \<in> carr_prodag (Nset 0) (compose (Nset 0) B (slide (Suc n))) \<and> x =  augm_func n g (Un_carrier (Nset n) B) (Suc 0) h (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n))))")
apply (rule allI) apply (rule impI)
apply (simp add:carr_prodag_def [of "Nset (Suc n)" "B"])
apply (rule conjI) apply (erule conjE)
 apply (thin_tac "x =
          augm_func n g (Un_carrier (Nset n) B) (Suc 0) h
           (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n))))")
 apply (simp add:augm_func_def)
apply (rule conjI) apply (erule conjE)
 apply (thin_tac "x =
          augm_func n g (Un_carrier (Nset n) B) (Suc 0) h
           (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n))))")
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:augm_func_def)
 apply (simp add:Nset_def)
 apply (case_tac "x \<le> n")
 apply simp apply (fold Nset_def) apply (simp add:carr_prodag_def)
 apply (erule conjE)+ apply (frule_tac x = x in mem_of_Nset [of _ "n"])
 apply (frule_tac f = g and x = x in funcset_mem[of _ "Nset n" "Un_carrier (Nset n) B"], assumption+)
 apply (thin_tac "g \<in> Nset n \<rightarrow> Un_carrier (Nset n) B")
 apply (thin_tac "h \<in> {0} \<rightarrow> Un_carrier {0} (compose {0} B (slide (Suc n)))")
 apply (simp add:Un_carrier_def)
 apply (subgoal_tac "\<forall>l. l \<in> Nset n \<longrightarrow> l \<in> Nset (Suc n)")
 apply blast apply (simp add:Nset_def)
 apply simp
 apply (subgoal_tac "x = Suc n") apply (thin_tac "x \<le> Suc n")
 apply (thin_tac "\<not> x \<le> n") apply simp
 apply (thin_tac "\<forall>k. k \<le> Suc n \<longrightarrow> ring (B k)")
 apply (thin_tac "g \<in> carr_prodag (Nset n) B")
 apply (simp add:sliden_def)
 apply (simp add:carr_prodag_def Un_carrier_def) apply (erule conjE)+
 apply (simp add:compose_def slide_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply blast
 apply (simp add:Nset_def) apply simp
apply (erule conjE)+
 apply (thin_tac "x =
          augm_func n g (Un_carrier (Nset n) B) (Suc 0) h
           (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc n))))")
 apply (rule ballI)
 apply (simp add:augm_func_def) apply (simp add:Nset_def)
 apply (case_tac "i \<le> n") apply simp
 apply (simp add:carr_prodag_def [of "{i. i \<le> n}" _])
 apply simp apply (thin_tac "g \<in> carr_prodag {i. i \<le> n} B")
 apply (subgoal_tac "i = Suc n") apply simp prefer 2 apply simp
 apply (simp add:carr_prodag_def compose_def slide_def sliden_def)
done

lemma ac_fProd_Prod:"\<forall>k\<in>Nset n. ring (B k) \<Longrightarrow>
                      ac_fProd_Rg n B = carr_prodag (Nset n) B"
apply (case_tac "n = 0")
 apply simp
 apply (subgoal_tac "\<exists>m. n = Suc m")
 apply (subgoal_tac "\<forall>m. n = Suc m \<longrightarrow> ac_fProd_Rg n B = carr_prodag (Nset n) B")
 apply blast apply (thin_tac "\<exists>m. n = Suc m")
 apply (rule allI) apply (rule impI) apply simp apply (thin_tac "n = Suc m")
 apply (rule equalityI)
 apply (simp add:ac_fProd_ProdTr1)
 apply (rule subsetI)
 apply (rename_tac m f)
apply (frule augm_funcTr, assumption+)
 apply (simp add:ag_setfunc_def)
 apply (subgoal_tac "(restrict f (Nset m)) \<in> carr_prodag (Nset m) B")
 apply (subgoal_tac "(\<lambda>x\<in>Nset 0. f (Suc (x + m))) \<in>  carr_prodag (Nset 0)
                           (compose (Nset 0) B (slide (Suc m)))")

 apply blast
 apply (thin_tac "f =  augm_func m (restrict f (Nset m)) (Un_carrier (Nset m) B) (Suc 0) (\<lambda>x\<in>Nset 0. f (Suc (x + m))) (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc m))))")
 apply (simp add:Nset_def carr_prodag_def)
 apply (rule conjI)
 apply (simp add:Pi_def restrict_def)
 apply (simp add:Un_carrier_def compose_def slide_def)
 apply (simp add:compose_def slide_def)

 apply (thin_tac "f = augm_func m (restrict f (Nset m)) (Un_carrier (Nset m) B)
              (Suc 0) (\<lambda>x\<in>Nset 0. f (Suc (x + m)))
              (Un_carrier (Nset 0) (compose (Nset 0) B (slide (Suc m))))")
apply (subgoal_tac "Nset m \<subseteq> Nset (Suc m)")
 apply (simp add:carr_prodag_def)
 apply (rule conjI)
 apply (simp add:Un_carrier_def subsetD)
 apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "x \<in> Nset (Suc m)")
 apply (rotate_tac -1) apply blast apply (simp add:Nset_def)
 apply (rule ballI) apply (subgoal_tac "i \<in> Nset (Suc m)")
 apply (rotate_tac -1)
 apply (simp add:subsetD) apply (simp add:subsetD)
apply (rule subsetI) apply (simp add:Nset_def CollectI)
apply (subgoal_tac "n = Suc (n - Suc 0)")
apply blast
apply simp
done

text{* A direct product of a finite number of rings defined with
 ac_fProd_Rg is equal to that defined by using carr_prodag. *}

constdefs
 fprodrg::"[nat, nat \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow>
  \<lparr>carrier:: (nat \<Rightarrow> 'a) set, pOp::[(nat \<Rightarrow> 'a), (nat \<Rightarrow> 'a)]
   \<Rightarrow> (nat \<Rightarrow> 'a), mOp:: (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a), zero::(nat \<Rightarrow> 'a),
   tOp :: [(nat \<Rightarrow> 'a), (nat \<Rightarrow> 'a)] \<Rightarrow> (nat \<Rightarrow> 'a), one :: (nat \<Rightarrow> 'a) \<rparr>"

  "fprodrg n B == \<lparr> carrier = ac_fProd_Rg n B,
 pOp = \<lambda>f. \<lambda>g. prod_pOp (Nset n) B f g, mOp = \<lambda>f. prod_mOp (Nset n) B f,
 zero = prod_zero (Nset n) B, tOp =  \<lambda>f. \<lambda>g. prod_tOp (Nset n) B f g,
 one = prod_one (Nset n) B \<rparr>"

 fPRoject::"[nat, nat \<Rightarrow> ('a, 'more) RingType_scheme, nat]
                   \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  "fPRoject n B x == \<lambda>f\<in>ac_fProd_Rg n B. f x"

syntax
  "@FPRODRING" :: "[nat, nat \<Rightarrow> ('a, 'more) RingType_scheme] \<Rightarrow>
               (nat \<Rightarrow> 'a) set"  ("(fr\<Pi>\<^sub>_/ _)" [72,73]72)
translations
  "fr\<Pi>\<^sub>n B" == "fprodrg n B"

lemma fprodrg_ring:"\<forall>k\<in>Nset n. ring (B k) \<Longrightarrow> ring (fprodrg n B)"
apply (simp add:fprodrg_def)
apply (frule ac_fProd_Prod)
apply simp
 apply (fold prodrg_def)
apply (simp add:prodrg_ring)
done


section "8. Chinese remainder theorem"

lemma Chinese_remTr1:"\<lbrakk>ring A; \<forall>k\<in>Nset n. ideal A (J k);
 \<forall>k\<in>Nset n. B k = qring A (J k); \<forall>k\<in>Nset n. S k = pj A (J k) \<rbrakk> \<Longrightarrow>
   ker\<^sub>A\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset n) B) (A_to_prodag A (Nset n) S B) = \<Inter> {I. \<exists>k\<in>Nset n. I = (J k)}"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def)
 apply (rule allI) apply (rule impI)
 apply (rename_tac a K)  apply (erule conjE)
 apply (simp add:prodrg_def) apply (simp add:A_to_prodag_def prod_one_def)
 apply (subgoal_tac "\<forall>k\<in>Nset n. K = J k \<longrightarrow> a \<in> K") apply blast
 apply (thin_tac "\<exists>k\<in>Nset n. K = J k") apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "(\<lambda>k\<in>Nset n. S k a) k = (\<lambda>x\<in>Nset n. 0\<^sub>B x) k")
 apply (thin_tac "(\<lambda>k\<in>Nset n. S k a) = prod_zero (Nset n) B")
 apply simp  apply (frule_tac I = "J k" in qring_zero [of "A"])
 apply simp
 apply (frule_tac I = "J k" and x = a in pj_mem [of "A"]) apply simp
 apply assumption apply simp
 apply (frule_tac I = "J k" and a = a in a_in_ar_coset [of "A"])
 apply simp apply assumption apply simp
 apply (simp add:prod_zero_def)
apply (rule subsetI)
 apply (simp add:CollectI ker_def)
 apply (subgoal_tac "0 \<in> Nset n") prefer 2 apply (simp add:Nset_def)
 apply (subgoal_tac "x \<in> J 0")  prefer 2 apply blast
 apply (subgoal_tac "ideal A (J 0)") prefer 2 apply simp
 apply (frule_tac h = x in ideal_subset [of "A" "J 0"], assumption+)
 apply simp
 apply (thin_tac "0 \<in> Nset n") apply (thin_tac "x \<in> J 0")
 apply (simp add:A_to_prodag_def prodrg_def)
 apply (simp add:prod_zero_def)
apply (rule funcset_eq [of _ "Nset n"])
 apply (simp add:extensional_def restrict_def)+
 apply (rule ballI) apply (simp add:qring_zero)
 apply (subgoal_tac "ideal A (J xa)")
 apply (subst pj_mem [of "A"], assumption+)
 apply (frule_tac I = "J xa" and a = x in a_in_ar_coset [of "A"]) apply simp
 apply assumption
 apply (rule_tac a = x and I = "J xa" in Qring_fix1 [of "A"], assumption+)
 apply blast apply simp
done

lemma coprime_prod_int2Tr:"ring R \<Longrightarrow> ((\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> (\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j)))) \<longrightarrow> (\<Inter> {I. \<exists>k\<in>Nset (Suc n). I = (J k)} = ideal_n_prod R (Suc n) J)"
apply (induct_tac n)
apply (rule impI)
 apply (erule conjE) apply (unfold Nset_def)
 apply (simp add:Nset_1) apply (erule conjE)+
 apply (subst coprime_int_prod [THEN sym, of "R" "J 0" "J (Suc 0)"],
                                                           assumption+)
 apply blast
(** n **)
apply (rule impI)
 apply (subgoal_tac "\<Inter>{I. \<exists>k\<in>Nset (Suc (Suc n)). I = J k} =
              (\<Inter>{I. \<exists>k\<in>Nset (Suc n). I = J k}) \<inter> (J (Suc (Suc n)))")
 apply (subgoal_tac "\<Inter>{I. \<exists>k\<in>Nset (Suc n). I = J k} = (i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J)")
(* apply (simp del:ideal_n_prodSn)*)
 apply (fold Nset_def)
 apply (frule_tac n = "Suc n" and J = J in coprime_n_idealsTr4 [of "R"],
                                                      assumption+)
  apply (simp del:ideal_n_prodSn)
 apply (subst coprime_int_prod, assumption+)
 apply (rule n_prod_ideal, assumption+)
 apply (rule ballI)
 apply (simp add:Nset_def)
apply (erule conjE)
 apply (thin_tac "(\<forall>i\<in>Nset (Suc (Suc n)).  \<forall>j\<in>Nset (Suc (Suc n)).
                  i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j))")
 apply (simp add:Nset_def)
 apply assumption
 apply simp

 apply (thin_tac "\<Inter>{I. \<exists>k\<in>Nset (Suc (Suc n)). I = J k} =
           \<Inter>{I. \<exists>k\<in>Nset (Suc n). I = J k} \<inter> J (Suc (Suc n))")
 apply (subgoal_tac "(\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and>
  (\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j))")
 apply (rotate_tac -1)
 apply (simp del:ideal_n_prodSn)
apply (subgoal_tac "\<forall>k\<in>Nset (Suc n). k \<in> Nset (Suc (Suc n))")
 apply blast
apply (simp add:Nset_def)
 apply (thin_tac " (\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> (\<forall>i\<in>Nset (Suc n).
         \<forall>j\<in>Nset (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)) \<longrightarrow>
           \<Inter>{I. \<exists>k\<in>Nset (Suc n). I = J k} = i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J")
 apply (thin_tac "(\<forall>k\<in>Nset (Suc (Suc n)). ideal R (J k)) \<and>
   (\<forall>i\<in>Nset (Suc (Suc n)). \<forall>j\<in>Nset (Suc (Suc n)).
        i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j))")
apply (subgoal_tac "Nset (Suc (Suc n)) = Nset (Suc n) \<union> {(Suc (Suc n))}")
apply blast
apply (simp add:Nset_Suc)
done

lemma coprime_prod_int2:"\<lbrakk>ring R; \<forall>k\<in>Nset (Suc n). ideal R (J k);
 \<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk>
 \<Longrightarrow> (\<Inter> {I. \<exists>k\<in>Nset (Suc n). I = (J k)} = ideal_n_prod R (Suc n) J)"
apply (simp add:coprime_prod_int2Tr)
done

lemma coprime_2_n:"\<lbrakk>ring R; ideal R A; ideal R B\<rbrakk> \<Longrightarrow>
 (qring R A) \<Oplus>~ (qring R B) = r\<Pi>\<^sub>(Nset (Suc 0)) (prodB1 (qring R A) (qring R B))"
apply (simp add: Prod2Rg_def)
done

text{* In this and following lemmata, ideals A and B are of type ('a, 'more) RingType_scheme. Don't try (r\<Pi>\<^sub>(Nset n) B) \<Oplus>~ B (Suc n) *}

lemma A_to_prodag2_hom:" \<lbrakk>ring R; ideal R A; ideal R B; S 0 = pj R A; S (Suc 0) = pj R B\<rbrakk>  \<Longrightarrow> A_to_prodag R (Nset (Suc 0))  S (prodB1 (qring R A) (qring R B)) \<in> rHom R (qring R A \<Oplus>~ qring R B)"
apply (frule coprime_2_n [of "R" "A" "B"], assumption+)
apply simp
apply (rule A_to_prodag_rHom, assumption+)
apply (rule ballI)
apply (case_tac "k = 0")
apply (simp add:prodB1_def)
apply (simp add:qring_ring)
apply (simp add:Nset_def)
apply (subgoal_tac "Suc 0 \<le> k") apply (thin_tac "0 < k")
apply (subgoal_tac "k = Suc 0") apply (thin_tac "k \<le> Suc 0")
 apply (thin_tac "Suc 0 \<le> k")
apply simp apply (simp add:prodB1_def)
apply (simp add:qring_ring) apply simp apply simp
apply (rule ballI)
apply (case_tac "k = Suc 0")
 apply (simp add:prodB1_def)
 apply (simp add:pj_Hom)
 apply (simp add:Nset_def)
 apply (subgoal_tac "k = 0")
 apply simp apply (simp add:prodB1_def)
 apply (simp add:pj_Hom)
 apply (frule le_imp_less_or_eq)
 apply simp
done

lemma A2coprime_rsurjecTr:"\<lbrakk>ring R; ideal R A; ideal R B; S 0 = pj R A; S (Suc 0) = pj R B\<rbrakk> \<Longrightarrow> (carrier (qring R A \<Oplus>~ qring R B)) = carr_prodag (Nset (Suc 0)) (prodB1 (qring R A) (qring R B))"
apply (simp add:Prod2Rg_def prodrg_def)
done

lemma A2coprime_rsurjec:"\<lbrakk>ring R; ideal R A; ideal R B; S 0 = pj R A; S (Suc 0) = pj R B; coprime_ideals R A B\<rbrakk> \<Longrightarrow> surjec\<^sub>R\<^sub>,\<^sub>((qring R A) \<Oplus>~ (qring R B)) (A_to_prodag R (Nset (Suc 0)) S (prodB1 (qring R A) (qring R B)))"
apply (simp add:surjec_def)
apply (rule conjI)
apply (frule A_to_prodag2_hom [of "R" "A" "B" "S"], assumption+)
apply (simp add:rHom_def)

apply (subgoal_tac "(A_to_prodag R (Nset (Suc 0)) S (prodB1 (qring R A) (qring R B))) \<in> (carrier R) \<rightarrow> (carrier (qring R A \<Oplus>~ qring R B))")
apply (simp add:A2coprime_rsurjecTr)
apply (simp add:surj_to_def image_def)
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>xa\<in>carrier R. x = A_to_prodag R (Nset (Suc 0)) S (prodB1 (qring R A) (qring R B)) xa \<longrightarrow> x \<in> carr_prodag (Nset (Suc 0)) (prodB1 (qring R A) (qring R B))")
 apply blast
 apply (thin_tac "\<exists>xa\<in>carrier R.
    x = A_to_prodag R (Nset (Suc 0)) S (prodB1 (qring R A) (qring R B)) xa")
 apply (rule ballI)
 apply (rule impI)
 apply simp
 apply (simp add:funcset_mem)

apply (rule subsetI)
apply (simp add:CollectI)
apply (subgoal_tac "x 0 \<in> carrier (qring R A)")
apply (subgoal_tac "x (Suc 0) \<in> carrier (qring R B)")
apply (subgoal_tac "\<exists>r\<in>carrier R. pj R A r = x 0 \<and> pj R B r = x (Suc 0)")
apply (subgoal_tac "\<forall>r\<in>carrier R. pj R A r = x 0 \<and> pj R B r = x (Suc 0) \<longrightarrow>
      x = A_to_prodag R (Nset (Suc 0)) S (prodB1 (qring R A) (qring R B)) r")
apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. pj R A r = x 0 \<and> pj R B r = x (Suc 0)")
 apply (rule ballI)
 apply (rule impI)
 apply (erule conjE)
apply (rule carr_prodag_mem_eq [of "Nset (Suc 0)" "prodB1 (qring R A) (qring R B)" _ _])
apply (rule ballI)
 apply (case_tac "k = 0")
 apply (simp add:prodB1_def)
 apply (frule qring_ring[of "R" "A"], assumption+) apply (simp add:ring_is_ag)
 apply (subgoal_tac "k = Suc 0")
 apply (simp add:prodB1_def)
 apply (frule qring_ring[of "R" "B"], assumption+) apply (simp add:ring_is_ag)
 apply (simp add:Nset_def)
 apply assumption
 apply (simp add:funcset_mem)
apply (rule ballI)
apply (case_tac "l = 0")
 apply (simp add:A_to_prodag_def prodB1_def)
 apply (subgoal_tac "l = Suc 0")
 apply (simp add:A_to_prodag_def prodB1_def)
 apply (simp add:Nset_def)
apply (simp add:coprime_surjTr)
 apply (thin_tac " A_to_prodag R (Nset (Suc 0)) S (prodB1 (R /\<^sub>r A) (R /\<^sub>r B))
           \<in> carrier R \<rightarrow>
             carr_prodag (Nset (Suc 0)) (prodB1 (R /\<^sub>r A) (R /\<^sub>r B))")
 apply (simp add:carr_prodag_def) apply (erule conjE)+
 apply (subgoal_tac "Suc 0 \<in> Nset (Suc 0)") prefer 2 apply (simp add:Nset_def)
 apply (subgoal_tac "x (Suc 0) \<in> carrier (prodB1 (qring R A) (qring R B) ( Suc 0))")  prefer 2 apply simp
 apply (simp add:prodB1_def)
 apply (simp add:carr_prodag_def) apply (erule conjE)+
apply (subgoal_tac "x 0 \<in> carrier (prodB1 (qring R A) (qring R B) 0)")
 prefer 2 apply (subgoal_tac "0 \<in> Nset (Suc 0)") apply simp
 apply (simp add:Nset_def)
 apply (simp add:prodB1_def)
apply (frule A_to_prodag2_hom [of "R" "A" "B" "S" ], assumption+)
apply (simp add:rHom_def aHom_def b_ag_def)
done

lemma prod2_n_Tr1:"\<lbrakk>ring R; \<forall>k\<in>Nset (Suc 0). ideal R (J k); \<forall>k\<in>Nset (Suc 0). B k = qring R (J k); \<forall>k\<in>Nset (Suc 0). S k = pj R (J k) \<rbrakk>  \<Longrightarrow> A_to_prodag R (Nset (Suc 0)) S (prodB1 (qring R (J 0)) (qring R (J (Suc 0)))) = A_to_prodag R (Nset (Suc 0)) S B"
apply (subgoal_tac "\<forall>k\<in>Nset (Suc 0). (prodB1 (qring R (J 0)) (qring R (J (Suc 0)))) k = B k")
apply (simp add:A_to_prodag_def)
apply (rule ballI)
 apply (case_tac "k = 0")
 apply simp
 apply (simp add:prodB1_def)
 apply (subgoal_tac "k = Suc 0")
apply simp
 apply (simp add:prodB1_def)
apply (simp add:Nset_def)
done

lemma Chinese_remTr2:"ring R \<Longrightarrow>  (\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> (\<forall>k\<in>Nset (Suc n). B k = qring R (J k)) \<and> (\<forall>k\<in>Nset (Suc n). S k = pj R (J k)) \<and> (\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))) \<longrightarrow> surjec\<^sub>R\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc n)) B) (A_to_prodag R (Nset (Suc n)) S B)"
apply (induct_tac n)
(* case n = 0, i.e. two coprime_ideals *)  (** use coprime_surjTr **)
apply (rule impI) apply (erule conjE)+
 apply (frule  A_to_prodag_rHom [of "R" "Nset (Suc 0)" "B" "S"])
 apply (rule ballI)
 apply (simp add:qring_ring)
 apply (simp add:pj_Hom)
 apply (simp add:surjec_def)
 apply (subgoal_tac "A_to_prodag R (Nset (Suc 0)) S B
                 \<in> carrier R \<rightarrow> carrier (r\<Pi>\<^sub>(Nset (Suc 0)) B)")
 prefer 2 apply (simp add:rHom_def aHom_def)
 apply (rule conjI)
 apply (simp add:rHom_def)
 apply (rule surj_to_test, assumption+)
 apply (rule ballI) apply (unfold Nset_def)
 apply (simp add:Nset_1) apply (erule conjE)+
 apply (frule coprime_elems [of "R" "J 0" "J (Suc 0)"], assumption+)
 apply (rename_tac f)
apply (subgoal_tac "\<forall>a\<in>J 0. \<forall>b\<in>J (Suc 0).  a +\<^sub>R b = 1\<^sub>R \<longrightarrow> (\<exists>a\<in>carrier R. A_to_prodag R {0, Suc 0} S B a = f)")
 apply blast
  apply (thin_tac "\<exists>a\<in>J 0. \<exists>b\<in>J (Suc 0).  a +\<^sub>R b = 1\<^sub>R")
 apply (rule ballI)+ apply (rule impI)
 apply (subgoal_tac "carrier (r\<Pi>\<^sub>{0, Suc 0} B) = carr_prodag {0, Suc 0} B")
 apply simp prefer 2 apply (rule prodrg_carrier) apply (rule ballI)
 apply simp apply (case_tac "k = 0") apply simp apply (simp add:qring_ring)
 apply (simp add:qring_ring)
 apply (subgoal_tac "f 0 \<in> carrier (qring R (J 0))")
 apply (subgoal_tac "f (Suc 0) \<in> carrier (qring R (J (Suc 0)))")
 apply (frule coprime_surjTr [of "R" "J 0" "J (Suc 0)" _], assumption+)
  apply (thin_tac "coprime_ideals R (J 0) (J (Suc 0))")
  apply (thin_tac "coprime_ideals R (J (Suc 0)) (J 0)")
  apply (thin_tac "carrier (r\<Pi>\<^sub>{0, Suc 0} B) = carr_prodag {0, Suc 0} B")
  apply (thin_tac " A_to_prodag R {0, Suc 0} S B \<in> carrier R \<rightarrow> carr_prodag {0, Suc 0} B")
  apply (thin_tac "a \<in> J 0") apply (thin_tac "b \<in> J (Suc 0)")
  apply (thin_tac " a +\<^sub>R b = 1\<^sub>R")
 apply (subgoal_tac "\<forall>r\<in>carrier R. pj R (J 0) r = f 0 \<and> pj R (J (Suc 0)) r = f (Suc 0) \<longrightarrow> (\<exists>a\<in>carrier R. A_to_prodag R {0, Suc 0} S B a = f)")
 apply blast
  apply (thin_tac "\<exists>r\<in>carrier R. pj R (J 0) r = f 0 \<and> pj R (J (Suc 0)) r = f (Suc 0)")
  apply (rule ballI)
  apply (rule impI)
  apply (erule conjE)
 apply (subgoal_tac "A_to_prodag R {0, Suc 0} S B r = f")
 apply blast
 apply (rule carr_prodag_mem_eq [of "{0, Suc 0}" "B"])
 apply (rule ballI) apply (case_tac "k = 0") apply simp
 apply (simp add:qring_ring ring_is_ag)
 apply (simp add:CollectI) apply (simp add:qring_ring ring_is_ag)
 apply (frule_tac a = r in rHom_mem [of "A_to_prodag R {0, Suc 0} S B" "R" "r\<Pi>\<^sub>{0, Suc 0} B"], assumption+) apply (simp add:prodrg_def)
 apply assumption
 apply (rule ballI)
 apply (case_tac "l = 0") apply simp apply (simp add:A_to_prodag_def)
 apply (simp add:CollectI) apply (simp add:A_to_prodag_def)
 apply (simp add:carr_prodag_def)
 apply (simp add:carr_prodag_def)
(**** n ****)
apply (fold Nset_def)
apply (rule impI)
 apply (erule conjE)+
 apply (subgoal_tac "\<forall>l. l\<in>Nset (Suc n) \<longrightarrow> l\<in>Nset (Suc (Suc n))")
 prefer 2 apply (simp add:Nset_def)
apply (subgoal_tac "\<forall>k\<in>{i. i \<le> Suc (Suc n)}. ring (B k)")
apply (frule_tac I = "{i. i \<le> Suc (Suc n)}"  in A_to_prodag_rHom [of "R" _ "B" "S"])
 apply assumption
 apply (rule ballI)
  apply (subgoal_tac "S k = pj R (J k)") prefer 2 apply (simp add:Nset_def)
  apply (subgoal_tac "B k = R /\<^sub>r J k") prefer 2 apply (simp add:Nset_def)
  apply simp
  apply (rule pj_Hom, assumption+) apply (simp add:Nset_def)
 apply (subgoal_tac "ideal R (i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J)")
 apply (subgoal_tac "ideal R (J (Suc (Suc n)))")
 apply (subgoal_tac "coprime_ideals R  (i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J) (J (Suc (Suc n)))")
 apply (subgoal_tac "surjec\<^sub>R\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc n)) B) (A_to_prodag R (Nset (Suc n)) S B)") prefer 2 apply blast
  apply (thin_tac "\<forall>i\<in>Nset (Suc (Suc n)).  \<forall>j\<in>Nset (Suc (Suc n)).
                   i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)")
   apply (thin_tac "(\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and>
           (\<forall>k\<in>Nset (Suc n). B k = R /\<^sub>r J k) \<and>
           (\<forall>k\<in>Nset (Suc n). S k = pj R (J k)) \<and>
           (\<forall>i\<in>Nset (Suc n).
               \<forall>j\<in>Nset (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)) \<longrightarrow>
           surjec\<^sub>R\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc n)) B) (A_to_prodag R (Nset (Suc n)) S B)")
 prefer 2  apply (rule coprime_n_idealsTr4, assumption+)
   apply simp
 prefer 2 apply (simp add:Nset_def)
 prefer 2 apply (rule n_prod_ideal, assumption+) apply (rule ballI)
  apply (simp add:Nset_def)
 prefer 2 apply (rule ballI) apply (subgoal_tac "B k =  R /\<^sub>r J k")
 prefer 2 apply (simp add:Nset_def) apply simp
 apply (rule qring_ring, assumption+) apply (simp add:Nset_def)
 apply (frule_tac A = "i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J" and B = "J (Suc (Suc n))" in
        coprime_elems [of "R"], assumption+)
apply (subgoal_tac "\<forall>a\<in>i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J. \<forall>b\<in>J (Suc (Suc n)).  a +\<^sub>R b = 1\<^sub>R  \<longrightarrow>
surjec\<^sub>R\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc (Suc n))) B) (A_to_prodag R (Nset (Suc (Suc n))) S B)")
apply blast
 apply (thin_tac "\<exists>a\<in>i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J. \<exists>b\<in>J (Suc (Suc n)).  a +\<^sub>R b = 1\<^sub>R")
apply (rule ballI)+ apply (rule impI)
 apply (thin_tac " coprime_ideals R (i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J) (J (Suc (Suc n)))")
apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). a \<in> (J l)")
prefer 2 apply (rule ele_n_prod, assumption+) apply (simp add:Nset_def)
 apply simp
 apply (simp add:surjec_def)
 apply (rule conjI) apply (simp add:Nset_def)
 apply (simp add:rHom_def)
 apply (rule surj_to_test) apply (erule conjE)
 apply (thin_tac "A_to_prodag R (Nset (Suc n)) S B \<in> aHom R (r\<Pi>\<^sub>(Nset (Suc n)) B)")
 apply (simp add:Nset_def) apply (simp add:rHom_def aHom_def)
 apply (rule ballI)
apply (rename_tac n a b f) apply (erule conjE)
 apply (subgoal_tac "A_to_prodag R (Nset (Suc n)) S B \<in> carrier R \<rightarrow>
                                   (carrier (r\<Pi>\<^sub>(Nset (Suc n)) B))")
 prefer 2 apply (simp add:Nset_def) apply (simp add:rHom_def aHom_def)
 apply (subgoal_tac "restrict f (Nset (Suc n)) \<in> carrier (r\<Pi>\<^sub>(Nset (Suc n)) B)")
 apply (subgoal_tac "\<exists>u\<in>carrier R. A_to_prodag R (Nset (Suc n)) S B u =
                            restrict f (Nset (Suc n))")
 prefer 2 apply (simp add:surj_to_def) apply (simp add:image_def)
 apply (frule sym)
 apply (subgoal_tac "restrict f (Nset (Suc n)) \<in> {y. \<exists>x\<in>carrier R. y = A_to_prodag R (Nset (Suc n)) S B x}") prefer 2 apply simp
 apply (thin_tac "{y. \<exists>x\<in>carrier R. y = A_to_prodag R (Nset (Suc n)) S B x} =
          carrier (r\<Pi>\<^sub>(Nset (Suc n)) B)")
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>x\<in>carrier R.
             restrict f (Nset (Suc n)) = A_to_prodag R (Nset (Suc n)) S B x
 \<longrightarrow>(\<exists>u\<in>carrier R.
             A_to_prodag R (Nset (Suc n)) S B u = restrict f (Nset (Suc n)))")
 apply blast
 apply (thin_tac "\<exists>x\<in>carrier R.
             restrict f (Nset (Suc n)) = A_to_prodag R (Nset (Suc n)) S B x")
 apply (rule ballI) apply (rule impI)
 apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "restrict f (Nset (Suc n)) = A_to_prodag R (Nset (Suc n)) S B x")
 apply blast
 apply (subgoal_tac "\<exists>v\<in>carrier R. pj R (J (Suc (Suc n))) v = f (Suc (Suc n))")
 apply (thin_tac "surj_to (A_to_prodag R (Nset (Suc n)) S B) (carrier R)
           (carrier (r\<Pi>\<^sub>(Nset (Suc n)) B))")
apply (subgoal_tac "\<forall>u\<in>carrier R. \<forall>v\<in>carrier R.  A_to_prodag R (Nset (Suc n)) S B u = restrict f (Nset (Suc n)) \<and> pj R (J (Suc (Suc n))) v = f (Suc (Suc n)) \<longrightarrow> (\<exists>a\<in>carrier R. A_to_prodag R (Nset (Suc (Suc n))) S B a = f)")
apply blast
 apply (thin_tac "\<exists>u\<in>carrier R.
             A_to_prodag R (Nset (Suc n)) S B u = restrict f (Nset (Suc n))")
 apply (thin_tac "\<exists>v\<in>carrier R. pj R (J (Suc (Suc n))) v = f (Suc (Suc n))")
apply (rule ballI)+ apply (rule impI)
 apply (erule conjE)
 prefer 2 apply (simp add:Nset_def)
 apply (simp add:prodrg_carrier carr_prodag_def)
 apply (subgoal_tac "f (Suc (Suc n)) \<in> carrier (R /\<^sub>r J (Suc (Suc n)))")
 apply (simp add:qring_carrier)
  apply (thin_tac "\<forall>k. k \<le> Suc (Suc n) \<longrightarrow> B k = R /\<^sub>r J k")
  apply (thin_tac "\<forall>k. k \<le> Suc (Suc n) \<longrightarrow> S k = pj R (J k)")
  apply (thin_tac "\<forall>k. k \<le> Suc (Suc n) \<longrightarrow> ring (R /\<^sub>r J k)")
  apply (thin_tac "A_to_prodag R {i. i \<le> Suc (Suc n)} S B
          \<in> rHom R (r\<Pi>\<^sub>{i. i \<le> Suc (Suc n)} B)")
 apply (subgoal_tac "\<exists>a\<in>carrier R. a \<uplus>\<^sub>R (J (Suc (Suc n))) = f (Suc (Suc n))")
 prefer 2 apply simp
 apply (thin_tac "f \<in> extensional {i. i \<le> Suc (Suc n)} \<and>
          f \<in> {i. i \<le> Suc (Suc n)} \<rightarrow> Un_carrier {i. i \<le> Suc (Suc n)} B \<and>
          (\<forall>i. i \<le> Suc (Suc n) \<longrightarrow> (\<exists>a\<in>carrier R. a \<uplus>\<^sub>R (J i) = f i))")
  apply (thin_tac " A_to_prodag R {i. i \<le> Suc n} S B
          \<in> carrier R \<rightarrow>
            {f. f \<in> extensional {i. i \<le> Suc n} \<and>
                f \<in> {i. i \<le> Suc n} \<rightarrow> Un_carrier {i. i \<le> Suc n} B \<and>
                (\<forall>i. i \<le> Suc n \<longrightarrow> (\<exists>a\<in>carrier R. a \<uplus>\<^sub>R (J i) = f i))}")
  apply (thin_tac "\<exists>u\<in>carrier R.
             A_to_prodag R {i. i \<le> Suc n} S B u = restrict f {i. i \<le> Suc n}")
  apply (subgoal_tac "\<forall>a\<in>carrier R. a \<uplus>\<^sub>R (J (Suc (Suc n))) = f (Suc (Suc n))
   \<longrightarrow> (\<exists>v\<in>carrier R. pj R (J (Suc (Suc n))) v = f (Suc (Suc n)))")
  apply blast
  apply (thin_tac "\<exists>a\<in>carrier R. a \<uplus>\<^sub>R (J (Suc (Suc n))) = f (Suc (Suc n))")
  apply (rule ballI) apply (rule impI)
  apply (frule_tac x = aa and I = "J (Suc (Suc n))" in pj_mem [of "R"])
  apply simp apply assumption+ apply simp
  apply blast apply simp
apply (subgoal_tac "A_to_prodag R (Nset (Suc (Suc n))) S B (b \<cdot>\<^sub>R u +\<^sub>R a \<cdot>\<^sub>R v)
                               = f")
apply (subgoal_tac " b \<cdot>\<^sub>R u +\<^sub>R  a \<cdot>\<^sub>R v \<in> carrier R")
apply (simp add:Nset_def)
 apply blast
 apply (frule ring_is_ag [of "R"])
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule_tac I ="J (Suc (Suc n))" in ideal_subset [of "R" ], assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ideal_subset [of "R" ], assumption+)
 apply (rule_tac I = "Nset (Suc (Suc n))" and A = B in carr_prodag_mem_eq )
 apply (rule ballI) apply (rule ring_is_ag)
 apply (simp add:Nset_def)
 apply (subgoal_tac "b \<cdot>\<^sub>R u +\<^sub>R  a \<cdot>\<^sub>R v \<in> carrier R")
 apply (simp add:Nset_def)
 apply (frule_tac f = "A_to_prodag R {i. i \<le> Suc (Suc n)} S B" and
 a = " b \<cdot>\<^sub>R u +\<^sub>R  a \<cdot>\<^sub>R v" in rHom_mem [of  _ "R"], assumption+)
 apply (simp add:prodrg_def)
  apply (frule ring_is_ag [of "R"])
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule_tac I ="J (Suc (Suc n))" in ideal_subset [of "R" ], assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ideal_subset [of "R" ], assumption+)
 apply (simp add:prodrg_carrier Nset_def)
apply (subgoal_tac "b \<cdot>\<^sub>R u +\<^sub>R  a \<cdot>\<^sub>R v \<in> carrier R")
prefer 2
 apply (frule ring_is_ag)
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rotate_tac 8)
apply (rule ideal_subset, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ideal_subset, assumption+)
apply (rule ballI)
apply (case_tac "l \<in> Nset (Suc n)")
 apply (subgoal_tac "a \<in> J l")
 apply (subgoal_tac "ideal R (J l)")
 apply (fold Nset_def)
 apply (thin_tac "\<forall>k\<in>Nset (Suc (Suc n)). B k = R /\<^sub>r J k")
 apply (thin_tac "\<forall>l\<in>Nset (Suc n). a \<in> J l")
 apply (thin_tac "A_to_prodag R (Nset (Suc (Suc n))) S B
          \<in> rHom R (r\<Pi>\<^sub>(Nset (Suc (Suc n))) B)")
 apply (thin_tac "A_to_prodag R (Nset (Suc n)) S B \<in> aHom R (r\<Pi>\<^sub>(Nset (Suc n)) B)")
 apply (thin_tac "A_to_prodag R (Nset (Suc n)) S B
          \<in> carrier R \<rightarrow> carrier (r\<Pi>\<^sub>(Nset (Suc n)) B)")
prefer 2  apply (simp add:Nset_def)
prefer 2  apply (simp add:Nset_def)
 apply (simp add:A_to_prodag_def)
 apply (subgoal_tac "S l = pj R (J l)") prefer 2 apply (simp add:Nset_def)
 apply simp
 apply (subgoal_tac "ideal R (J l)") prefer 2 apply (simp add:Nset_def)
 apply (subgoal_tac "ideal R (J (Suc (Suc n)))") prefer 2
  apply (simp add:Nset_def)
 apply (frule_tac A = "J l" and a = a and b = b and u = u and v = v in
  partition_of_unity [of "R"],  assumption+)
 apply (simp add:ideal_subset) apply assumption+
 apply (subgoal_tac "a \<cdot>\<^sub>R v \<in> carrier R")
 apply (subgoal_tac "b \<cdot>\<^sub>R u \<in> carrier R") apply (frule ring_is_ag)
 apply (subst ag_pOp_commute, assumption+) apply simp
 prefer 2 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:ideal_subset) apply assumption
 prefer 2 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:ideal_subset) apply assumption
 apply (subgoal_tac "(\<lambda>k\<in>Nset (Suc n). S k u) l = restrict f (Nset (Suc n)) l")  prefer 2 apply simp
 apply (thin_tac "ideal R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<diamondsuit>\<^sub>R (J (Suc n)))")
 apply (thin_tac "f \<in> carrier (r\<Pi>\<^sub>(Nset (Suc (Suc n))) B)")
 apply (thin_tac "restrict f (Nset (Suc n)) \<in> carrier (r\<Pi>\<^sub>(Nset (Suc n)) B)")
 apply (thin_tac "(\<lambda>k\<in>Nset (Suc n). S k u) = restrict f (Nset (Suc n))")
 apply (thin_tac "b \<cdot>\<^sub>R u +\<^sub>R  a \<cdot>\<^sub>R v \<in> carrier R")
 apply (thin_tac "pj R (J l) (  a \<cdot>\<^sub>R v +\<^sub>R  b \<cdot>\<^sub>R u) = pj R (J l) u")
 apply simp
 apply (subgoal_tac "l = Suc (Suc n)") prefer 2 apply (simp add:Nset_def)
 apply simp
 apply (thin_tac "A_to_prodag R (Nset (Suc n)) S B u = restrict f (Nset (Suc n))")
  apply (frule_tac A = "J (Suc (Suc n))" and a = b and b = a and u = v and v = u in  partition_of_unity [of "R"]) apply simp apply assumption
 apply (rule ideal_subset, assumption+)
 apply (subgoal_tac "a \<in> carrier R") apply (subgoal_tac "b \<in> carrier R")
 apply (frule ring_is_ag)
 apply (simp add:ag_pOp_commute)
 apply (subgoal_tac "ideal R (J (Suc (Suc n)))")
 prefer 2 apply (simp add:Nset_def)
 apply (thin_tac "\<forall>k\<in>Nset (Suc (Suc n)). ideal R (J k)")
 apply (simp add:ideal_subset) apply (rule ideal_subset, assumption+)
 apply simp
 apply (simp add:A_to_prodag_def)
apply (simplesubst prodrg_def) apply simp
 apply (simp add:carr_prodag_def)
 apply (simp add:extensional_def)
 apply (simp add:prodrg_def) apply (fold prodrg_def)
 apply (simp add:carr_prodag_def) apply (erule conjE)
 apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (subst Un_carrier_def) apply (simp add:CollectI)
 apply (subgoal_tac "f x \<in> carrier (R /\<^sub>r J x)")
 apply blast apply (simp add:Nset_def)
done


lemma Chinese_remTr3:"\<lbrakk>ring R; (\<forall>k\<in>Nset (Suc n). ideal R (J k)); \<forall>k\<in>Nset (Suc n). B k = qring R (J k); \<forall>k\<in>Nset (Suc n). S k = pj R (J k); \<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk> \<Longrightarrow> surjec\<^sub>R\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc n)) B) (A_to_prodag R (Nset (Suc n)) S B)"
apply (simp add:Chinese_remTr2 [of "R" "n" "J" "B" "S"])
done

lemma imset:"\<lbrakk>ring R; \<forall>k\<in>Nset (Suc n). ideal R (J k)\<rbrakk>
\<Longrightarrow> {I. \<exists>k\<in>Nset (Suc n). I = J k} = {J k| k. k \<in> Nset (Suc n)}"
apply blast
done

theorem Chinese_remThm:"\<lbrakk>ring R; (\<forall>k\<in>Nset (Suc n). ideal R (J k)); \<forall>k\<in>Nset (Suc n). B k = qring R (J k); \<forall>k\<in>Nset (Suc n). S k = pj R (J k); \<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk> \<Longrightarrow> bijec\<^sub>(qring R (\<Inter> {J k | k. k\<in>Nset (Suc n)}))\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc n)) B) ((A_to_prodag R (Nset (Suc n)) S B)\<degree>\<^sub>R\<^sub>,\<^sub>(r\<Pi>\<^sub>(Nset (Suc n)) B))"
apply (frule Chinese_remTr3, assumption+)
apply (subgoal_tac "ring (r\<Pi>\<^sub>(Nset (Suc n)) B)")
apply (frule surjec_ind_bijec [of "R" "(r\<Pi>\<^sub>(Nset (Suc n)) B)"
                   "A_to_prodag R (Nset (Suc n)) S B"], assumption+)
apply (rule A_to_prodag_rHom, assumption+)
 apply (rule ballI)
 apply (subgoal_tac "B k = R /\<^sub>r J k") prefer 2 apply (simp add:Nset_def)
 apply simp apply (rule qring_ring, assumption+) apply (simp add:Nset_def)
 apply (rule ballI) apply (subgoal_tac "S k = pj R (J k)")
 apply (subgoal_tac "B k = R /\<^sub>r J k") apply simp
 apply (rule pj_Hom, assumption+) apply (simp add:Nset_def) apply simp
 apply simp apply simp
apply (simp add:Chinese_remTr1 [of "R" "Suc n" "J" "B" "S"])
apply (simp add:imset)
apply (rule prodrg_ring [of "Nset (Suc n)"])
apply (simp add:qring_ring)
done

lemma prod_primeTr2:"\<lbrakk>ring R; ideal R A \<rbrakk> \<Longrightarrow> (\<forall>k\<in>Nset (Suc n). prime_ideal R (P k)) \<and> (\<forall>l\<in>Nset (Suc n). \<not> (A \<subseteq> P l)) \<and> (\<forall>k\<in>Nset (Suc n). \<forall>l\<in>Nset (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l)) \<longrightarrow> (\<forall>i\<in> Nset (Suc n). (nprod0 R (ppa R P A i) n \<in> A \<and> (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and> (nprod0 R (ppa R P A i) n \<notin> P i)))"
apply (induct_tac n)
 apply (rule impI)
 apply (rule ballI)
 apply simp
 apply (erule conjE)+
 apply (frule prod_primeTr1 [of "R" "0" "P" "A" _], assumption+)
 apply (rule conjI) apply (subgoal_tac "0 \<in> Nset 0")
  apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (rule conjI)
 apply (rule ballI)
 apply (subgoal_tac "0 \<in> Nset 0")
apply (simp add:Nset_1)
apply (case_tac "i = 0")
 apply (subgoal_tac "l = Suc 0")
 apply simp apply (simp add:Nset_def) apply (simp add:skip_def)
 apply (erule conjE)+
 apply (simp add:NSet_def) apply (simp add:Nset_def) apply (erule conjE)
 apply simp
 apply (frule_tac n = i in Suc_leI [of "0"]) apply (thin_tac "0 < i")
 apply (frule_tac x = i and n = "Suc 0" in Nset_le)
 apply (frule_tac m = i and n = "Suc 0" in le_anti_sym, assumption+)
 apply (thin_tac "Suc 0 \<le> i") apply (thin_tac "i \<le> Suc 0")
 apply simp
apply (frule skip_im_Tr3 [of "0" "0"])
 apply (simp add:Nset_def Nset_1)
 apply simp apply (simp add:Nset_def)
 apply (simp add:Nset_def)
(** n **)
  apply (rule impI)  (** show induction assumption is OK. **)
  apply (subgoal_tac "(\<forall>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n \<in> A \<and>
  (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and> nprod0 R (ppa R P A i) n \<notin> P i)")
  prefer 2
  apply (subgoal_tac "\<forall>l. l\<in>Nset (Suc n) \<longrightarrow> l\<in>Nset (Suc (Suc n))")
  apply blast
  apply (simp add:Nset_def)
  apply (thin_tac "(\<forall>k\<in>Nset (Suc n). prime_ideal R (P k)) \<and>
  (\<forall>l\<in>Nset (Suc n). \<not> A \<subseteq> P l) \<and> (\<forall>k\<in>Nset (Suc n). \<forall>l\<in>Nset (Suc n). k = l \<or>
   \<not> P k \<subseteq> P l) \<longrightarrow> (\<forall>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n \<in> A \<and>
  (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and> nprod0 R
  (ppa R P A i) n \<notin> P i)")
                    (* induction assumption OK *)
apply (rule ballI)
 apply (erule conjE)+
 apply (case_tac "i \<in> Nset (Suc n)")   (** case i \<in> Nset (Suc n) **)
 apply (subgoal_tac "nprod0 R (ppa R P A i) n \<in> A \<and>
 (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and> nprod0 R
 (ppa R P A i) n \<notin> P i")
 prefer 2 apply (rotate_tac -1) apply blast
  apply (thin_tac "\<forall>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n \<in> A \<and>
                (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and>
                nprod0 R (ppa R P A i) n \<notin> P i")
 apply (rule conjI)
 apply simp
 apply (rule ideal_ring_multiple, assumption+)
  apply simp
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
  apply (thin_tac "nprod0 R (ppa R P A i) n \<in> A \<and>
             (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and>
             nprod0 R (ppa R P A i) n \<notin> P i")
  apply (thin_tac "i \<in> Nset (Suc n)")
  apply (simp add: ppa_mem) apply (simp add:Nset_def)
apply (erule conjE)
 apply (rule conjI)
 apply (rule ballI)
 apply (frule skip_fun_im)
  apply (subgoal_tac "l \<in>  skip i ` Nset (Suc n)")
   prefer 2  apply (simp add:skip_fun_im)
  apply (thin_tac "skip i ` Nset (Suc n) = Nset (Suc (Suc n)) - {i}")
 apply (subgoal_tac "prime_ideal R (P l)")
  prefer 2 apply (simp add:Nset_def)
  apply (thin_tac "l \<in> Nset (Suc (Suc n)) - {i}")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>Nset (Suc n). l = skip i x \<longrightarrow> ppa R P A i (Suc n) \<cdot>\<^sub>R (nprod0 R (ppa R P A i) n) \<in> P l")
 apply blast apply (thin_tac "\<exists>x\<in>Nset (Suc n). l = skip i x")
 apply (rule ballI) apply (rule impI) apply simp
 apply (thin_tac "l = skip i x") apply simp
 apply (rename_tac n i h)
 apply (frule prod_primeTr1, assumption+)
apply (case_tac "h = Suc n")
 apply simp
 apply (subgoal_tac "ideal R (P (skip i (Suc n)))")
 prefer 2  apply (simp add:prime_ideal_def)
 apply (rule ideal_ring_multiple1, assumption+)
 apply (simp add:Nset_def)
  apply (subgoal_tac "\<forall>l\<in>Nset n. ppa R P A i l \<in> carrier R")
 apply (simp add:nprod_mem)
  apply (rule ballI) apply (subgoal_tac "l \<in> Nset (Suc n)")
  apply (simp add:ideal_subset) apply (simp add:Nset_def)
 apply (subgoal_tac "h \<in> Nset n")  (** case_tac ** h \<noteq> Suc n **)
  apply (thin_tac "h \<noteq> Suc n")
  apply (subgoal_tac "(skip i h) \<in> Nset (Suc n) - {i}")
  prefer 2
   apply (subgoal_tac "skip i \<in> NSet \<rightarrow> NSet")
   apply (subgoal_tac "Nset n \<subseteq> NSet")
   apply (subgoal_tac "skip i h \<in> skip i ` (Nset n)")
   prefer 2 apply (simp add:mem_in_image) apply (simp add:skip_fun_im)
   apply (simp add:Nset_def NSet_def) apply (simp add:Pi_def)
   apply (rule allI) apply (rule impI) apply (simp add:NSet_def)
 apply (subgoal_tac "ideal R (P (skip i h))")
 apply (rule ideal_ring_multiple, assumption+)
  apply blast
  apply (simp add:Nset_def ideal_subset)
  apply (subgoal_tac "prime_ideal R (P (skip i h))")
  apply (simp add:prime_ideal_def)
  apply (simp add:Nset_def)
   apply (simp add:Nset_def)
 apply (erule conjE)
  apply (thin_tac "\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l")
 apply simp
  apply (thin_tac " nprod0 R (ppa R P A i) n \<in> A")
  apply (frule  prod_primeTr1, assumption+)
  apply (subgoal_tac "ppa R P A i (Suc n) \<notin> P i")
  apply (subgoal_tac "ppa R P A i (Suc n) \<in> carrier R")
  apply (subgoal_tac "nprod0 R (ppa R P A i) n \<in> carrier R")
   apply (thin_tac "\<forall>l\<in>Nset (Suc (Suc n)). \<not> A \<subseteq> P l")
   apply (thin_tac "\<forall>k\<in>Nset (Suc (Suc n)).
                \<forall>l\<in>Nset (Suc (Suc n)). k = l \<or> \<not> P k \<subseteq> P l")
   apply (thin_tac "\<forall>l\<in>Nset (Suc n).
                ppa R P A i l \<in> A \<and>
                ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i")
   apply (subgoal_tac "prime_ideal R (P i)")
    apply (thin_tac "\<forall>k\<in>Nset (Suc (Suc n)). prime_ideal R (P k)")
    apply (thin_tac "ideal R A")
 apply (rule contrapos_pp) apply simp+
 apply (simp add:prime_ideal_def)
  apply (erule conjE)+
  apply (subgoal_tac "ppa R P A i (Suc n) \<in> P i \<or>
                             nprod0 R (ppa R P A i) n \<in> P i")
  apply blast
   apply (thin_tac "nprod0 R (ppa R P A i) n \<notin> P i")
   apply (thin_tac "ppa R P A i (Suc n) \<notin> P i")
  apply simp apply simp
  apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). ppa R P A i l \<in> carrier R")
  apply (simp add:nprod_mem)
  apply (simp add:ideal_subset)
  apply (simp add:Nset_def ideal_subset)
  apply (simp add:Nset_def)
apply (subgoal_tac "i = Suc (Suc n)")
(*** case i \<notin> Nset (Suc n), i.e. i = Suc (Suc n) **)
prefer 2
 apply (thin_tac "\<forall>i\<in>Nset (Suc n).
                nprod0 R (ppa R P A i) n \<in> A \<and>
                (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and>
                nprod0 R (ppa R P A i) n \<notin> P i")
 apply (thin_tac "\<forall>k\<in>Nset (Suc (Suc n)). prime_ideal R (P k)")
 apply (thin_tac "\<forall>l\<in>Nset (Suc (Suc n)). \<not> A \<subseteq> P l")
 apply (thin_tac " \<forall>k\<in>Nset (Suc (Suc n)).
                \<forall>l\<in>Nset (Suc (Suc n)). k = l \<or> \<not> P k \<subseteq> P l")
 apply (simp add:Nset_def)
  apply (thin_tac "i \<in> Nset (Suc (Suc n))")
  apply (thin_tac "i \<notin> Nset (Suc n)")
  apply (thin_tac "\<forall>i\<in>Nset (Suc n).
                nprod0 R (ppa R P A i) n \<in> A \<and>
                (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and>
                nprod0 R (ppa R P A i) n \<notin> P i")

 apply (subgoal_tac "Suc (Suc n) \<in> Nset (Suc (Suc n))")
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule prod_primeTr1, assumption+)
 prefer 2 apply (simp add:Nset_def)
 prefer 2 apply (simp add:Nset_def)
apply (rule conjI)
 apply simp
 apply (rule ideal_ring_multiple1, assumption+)
 apply (subgoal_tac "Suc (Suc n) \<in> Nset (Suc (Suc n))")
 apply simp apply (simp add:Nset_def)
 apply (frule ppa_mem, assumption+)
 apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). ppa R P A (Suc (Suc n)) l \<in> carrier R")
 apply (simp add:nprod_mem)
 apply (rule ballI)
 apply (subgoal_tac "Suc (Suc n) \<in> Nset (Suc (Suc n))")
 apply (simp add:ppa_mem) apply (simp add:Nset_def)
apply (rule conjI)
 apply (rule ballI)
 apply simp
 (** case induction above is not available **)
apply (subgoal_tac "l \<in> Nset (Suc n)")
 apply (case_tac "l = Suc n")
 apply simp
 apply (subgoal_tac "ideal R (P (Suc n))")
 apply (rule ideal_ring_multiple1, assumption+)
 apply (subgoal_tac "ppa R P A (Suc (Suc n)) (Suc n) \<in> P (skip (Suc (Suc n)) (Suc n))")
 apply (simp add:skip_id)
 apply (simp add:Nset_def)
 apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). ppa R P A (Suc (Suc n)) l \<in> carrier R")
 apply (rule nprod_mem, assumption+)
  apply simp
 apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). ppa R P A (Suc (Suc n)) l \<in> A")
  apply (simp add:ideal_subset) apply simp
  apply (subgoal_tac "prime_ideal R (P (Suc n))")
  apply (simp add:prime_ideal_def)
  apply (simp add:Nset_def)
(* show l \<le> n *)
apply (thin_tac "l \<in> Nset (Suc (Suc n)) \<and> l \<noteq> Suc (Suc n)")
apply (subgoal_tac "l \<in> Nset n")
 apply (subgoal_tac "ideal R (P l)")
 apply (rule ideal_ring_multiple, assumption+)
 apply (rule ideal_nprod_inc, assumption+)
 apply (rule ballI)
  apply (subgoal_tac "ppa R P A (Suc (Suc n)) ia \<in> A")
  apply (simp add:ideal_subset)
  apply (simp add:Nset_def)
  apply (subgoal_tac "ppa R P A (Suc (Suc n)) l \<in> P (skip (Suc (Suc n)) l)")
  apply (subgoal_tac "skip (Suc (Suc n)) l = l") apply (rotate_tac -1)
 apply simp
 apply blast
 apply (simp add:Nset_def skip_id) apply simp
 apply (simp add:ideal_subset)
 apply (simp add:Nset_def prime_ideal_def)
  apply (thin_tac "\<forall>l\<in>Nset (Suc n).
             ppa R P A (Suc (Suc n)) l \<in> A \<and>
             ppa R P A (Suc (Suc n)) l \<in> P (skip (Suc (Suc n)) l) \<and>
             ppa R P A (Suc (Suc n)) l \<notin> P (Suc (Suc n))")
  apply (thin_tac "Suc n \<in> Nset (Suc n)")
 apply (rule Nset_pre, assumption+)
  apply (erule conjE)
  apply (rule Nset_pre, assumption+)

apply (simp del:nprod0_suc)
 apply (rule prime_nprod_exc, assumption+)
 apply (simp add:Nset_def)
 apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). ppa R P A (Suc (Suc n)) l \<in> A")
 apply (simp add:ideal_subset)
 apply simp
apply simp
done

lemma prod_prime:"\<lbrakk>ring R; ideal R A; \<forall>k\<in>Nset (Suc n). prime_ideal R (P k);
\<forall>l\<in>Nset (Suc n). \<not> (A \<subseteq> P l); \<forall>k\<in>Nset (Suc n). \<forall>l\<in>Nset (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l)\<rbrakk> \<Longrightarrow> \<forall>i\<in> Nset (Suc n). (nprod0 R (ppa R P A i) n \<in> A \<and> (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and> (nprod0 R (ppa R P A i) n \<notin> P i))"
apply (frule  prod_primeTr2 [of "R" "A" "n" "P"], assumption+)
apply simp
done

lemma skip_im1:"\<lbrakk>i \<in> Nset (Suc n); P \<in> Nset (Suc n) \<rightarrow> {X. prime_ideal R X}\<rbrakk> \<Longrightarrow> compose (Nset n) P (skip i) ` Nset n = P ` (Nset (Suc n) - {i})"
 apply (subgoal_tac "compose (Nset n) P (skip i) =
                              compose (Nset n) P (restrict (skip i) (Nset n))")
 apply simp
 apply (subgoal_tac "restrict (skip i) (Nset n) \<in> Nset n \<rightarrow> Nset (Suc n)")
 apply (simp add:setim_cmpfn)
 apply (subgoal_tac "restrict (skip i) (Nset n) ` Nset n = Nset (Suc n) - {i}")
  apply simp
 apply (subgoal_tac "restrict (skip i) (Nset n) ` Nset n = (skip i) ` Nset n")
 apply simp
 apply (simp add:skip_fun_im)
  apply (rule equalityI)
  apply (rule subsetI)
   apply (simp add:image_def CollectI)
  apply (rule subsetI)
   apply (simp add:image_def CollectI)
 apply (simp add:Pi_def restrict_def)
 apply (simp add:skip_mem)
  apply (simp add:expand_fun_eq)
 apply (rule allI)
 apply (simp add:compose_def)
done

lemma mutch_aux1:"\<lbrakk>ring R; ideal R A; P \<in> Nset (Suc n) \<rightarrow> Collect (prime_ideal R); i \<in> Nset (Suc n)\<rbrakk> \<Longrightarrow> compose (Nset n) P (skip i) \<in> Nset n \<rightarrow> Collect (prime_ideal R)"
apply (subgoal_tac "compose (Nset n) P (restrict (skip i) (Nset n)) \<in>
  Nset n \<rightarrow> Collect (prime_ideal R)")
apply (subgoal_tac "compose (Nset n) P (restrict (skip i) (Nset n)) =
                          compose (Nset n) P (skip i)")
 apply simp
apply (simp add: expand_fun_eq)
 apply (rule allI)
 apply (simp add:compose_def)
 apply (subgoal_tac "restrict (skip i) (Nset n) \<in> Nset n \<rightarrow> Nset (Suc n)")
 apply (simp add:composition)
apply (thin_tac "P \<in> Nset (Suc n) \<rightarrow> Collect (prime_ideal R)")
apply (simp add:Pi_def restrict_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:skip_mem)
done

lemma prime_ideal_cont1Tr:"\<lbrakk>ring R; ideal R A\<rbrakk>  \<Longrightarrow> \<forall>P. ((P \<in> Nset n \<rightarrow> {X. prime_ideal R X}) \<and> (A \<subseteq> \<Union> P ` (Nset n))) \<longrightarrow> (\<exists>i\<in>Nset n. A \<subseteq> (P i))"
apply (induct_tac n)
 apply (rule allI) apply (rule impI)
 apply (erule conjE)
 apply (simp add:Nset_def)
(** n **)
apply (rule allI) apply (rule impI)
 apply (erule conjE)+
apply (case_tac "\<exists>i\<in>Nset (Suc n). \<exists>j\<in>Nset (Suc n). (i \<noteq> j \<and> P i \<subseteq> P j)")
apply auto
apply (subgoal_tac "A \<subseteq> \<Union> (compose (Nset n) P (skip i)) ` (Nset n)")
apply (frule mutch_aux1, assumption+)
 apply (subgoal_tac "\<exists>k\<in> Nset n. A \<subseteq> (compose (Nset n) P (skip i)) k")
 apply (subgoal_tac "\<forall>k\<in>Nset n. A \<subseteq> compose (Nset n) P (skip i) k \<longrightarrow>
                                     (\<exists>i\<in>Nset (Suc n). A \<subseteq> P i)")
  apply (thin_tac " \<forall>P. P \<in> Nset n \<rightarrow> Collect (prime_ideal R) \<and> A \<subseteq> UNION (Nset n) P \<longrightarrow> (\<exists>i\<in>Nset n. A \<subseteq> P i)")
  apply (thin_tac " P \<in> Nset (Suc n) \<rightarrow> Collect (prime_ideal R)")
  apply (thin_tac " A \<subseteq> \<Union>compose (Nset n) P (skip i) ` Nset n")
  apply (thin_tac "compose (Nset n) P (skip i) \<in> Nset n \<rightarrow> Collect (prime_ideal R)")
 apply blast apply (thin_tac "\<exists>k\<in>Nset n. A \<subseteq> compose (Nset n) P (skip i) k")
 apply (rule ballI) apply (rule impI)
 apply (simp add:compose_def)
 apply (subgoal_tac "skip i k \<in> Nset (Suc n)")
 apply blast
apply (simp add:skip_mem)
 apply (thin_tac "P \<in> Nset (Suc n) \<rightarrow> Collect (prime_ideal R)")
 apply (thin_tac "A \<subseteq> UNION (Nset (Suc n)) P")
 apply (thin_tac "i \<in> Nset (Suc n)") apply (thin_tac "j \<in> Nset (Suc n)")
 apply (thin_tac " i \<noteq> j") apply (thin_tac " P i \<subseteq> P j") apply (rotate_tac -1)
 apply blast
apply (simp add:Pi_def compose_def)

apply (subgoal_tac "UNION (Nset (Suc n)) P \<subseteq> (\<Union>x\<in>Nset n. P (skip i x))")
 apply (rule subset_trans [of "A" _ _], assumption+)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (thin_tac "\<forall>P. (\<forall>x. x \<in> Nset n \<longrightarrow> prime_ideal R (P x)) \<and>
              A \<subseteq> (\<Union>x\<in>Nset n. P x) \<longrightarrow>
              (\<exists>i\<in>Nset n. A \<subseteq> P i)")
 apply (thin_tac "\<forall>x. x \<in> Nset (Suc n) \<longrightarrow> prime_ideal R (P x)")
 apply (thin_tac "A \<subseteq> UNION (Nset (Suc n)) P")
 apply (subgoal_tac "\<forall>xa\<in>Nset (Suc n). x \<in> P xa \<longrightarrow> (\<exists>xa\<in>Nset n. x \<in> P (skip i xa))")
 apply blast apply (thin_tac "\<exists>xa\<in>Nset (Suc n). x \<in> P xa")
 apply (rule ballI)
 apply (rule impI)
 apply (subgoal_tac "skip i ` (Nset n) = Nset (Suc n) - {i}")
apply (case_tac "xa = i")
 apply (subgoal_tac "x \<in> P j")
 apply (subgoal_tac "j \<in> skip i ` Nset n")
 apply (thin_tac "skip i ` Nset n = Nset (Suc n) - {i}")
 apply (simp add:image_def)
 apply (rename_tac n P i j a l)
 apply (subgoal_tac "\<forall>x\<in>Nset n. j = skip i x \<longrightarrow> (\<exists>xa\<in>Nset n. a \<in> P (skip i xa))")
 apply blast apply (thin_tac "\<exists>x\<in>Nset n. j = skip i x")
 apply (rule ballI) apply (rule impI)
  apply simp
  apply blast
 apply simp apply simp
 apply (simp add:subsetD)
apply (rename_tac n P i j a l)
 apply (subgoal_tac "l \<in> skip i ` (Nset n)")
  apply (thin_tac "skip i ` Nset n = Nset (Suc n) - {i}")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>Nset n. l = skip i x \<longrightarrow> ( \<exists>xa\<in>Nset n. a \<in> P (skip i xa))")
 apply blast apply (thin_tac "\<exists>x\<in>Nset n. l = skip i x")
 apply (rule ballI) apply (rule impI)
 apply simp
 apply blast
apply simp
 apply (simp add:skip_fun_im)
(** last_step induction assumption is not abailable **)
apply (rule contrapos_pp)
 apply simp+
 apply (thin_tac "\<forall>P. P \<in> Nset n \<rightarrow> Collect (prime_ideal R) \<and>
                 A \<subseteq> UNION (Nset n) P \<longrightarrow> (\<exists>i\<in>Nset n. A \<subseteq> P i)")
 apply (subgoal_tac "\<forall>k\<in>Nset (Suc n). prime_ideal R (P k)")
 apply (thin_tac " P \<in> Nset (Suc n) \<rightarrow> Collect (prime_ideal R)")
 apply (frule prod_prime [of "R" "A" _ _], assumption+)
 prefer 2  apply (rule ballI)
 apply (frule funcset_mem, assumption+)
 apply simp
apply (subgoal_tac "nsum0 R (\<lambda>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n) (Suc n) \<in> A \<and>  nsum0 R (\<lambda>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n) (Suc n) \<notin>  UNION (Nset (Suc n)) P")
 apply (erule conjE)
 apply (subgoal_tac "nsum0 R (\<lambda>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n) (Suc n)
  \<in> UNION (Nset (Suc n)) P") apply simp
 apply (thin_tac " nsum0 R (\<lambda>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n) (Suc n)
             \<notin> UNION (Nset (Suc n)) P")
 apply (rule subsetD, assumption+)
apply (rule conjI)
 apply (thin_tac "A \<subseteq> UNION (Nset (Suc n)) P")
 apply (thin_tac "\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). i = j \<or> \<not> P i \<subseteq> P j")
 apply (thin_tac "\<forall>i\<in>Nset (Suc n). \<not> A \<subseteq> P i")
 apply (thin_tac "\<forall>k\<in>Nset (Suc n). prime_ideal R (P k)")
 apply (subgoal_tac "\<forall>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n \<in> A")
 prefer 2 apply blast
  apply (thin_tac "\<forall>i\<in>Nset (Suc n).
                nprod0 R (ppa R P A i) n \<in> A \<and>
                (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and>
                nprod0 R (ppa R P A i) n \<notin> P i")
  apply (rule nsum_ideal_inc, assumption+)
 apply simp
 apply (simp del:nsum0_suc)  (** final step **)
 apply (rule ballI)
 apply (subgoal_tac "ideal R (P x)")
 prefer 2 apply (subgoal_tac "prime_ideal R (P x)")
  apply (simp add:prime_ideal_def) apply simp
 apply (subgoal_tac "\<forall>i\<in>Nset (Suc n). (nprod0 R (ppa R P A i) n) \<in> carrier R")
 apply (subgoal_tac "\<forall>i\<in>Nset (Suc n)-{x}. (nprod0 R (ppa R P A i) n \<in> (P x))")
 apply (subgoal_tac "nprod0 R (ppa R P A x) n \<notin> (P x)")
 apply (rule nsum_ideal_exc, assumption+)
  apply simp
  apply (subgoal_tac "(\<forall>l\<in>Nset (Suc n) - {x}.
                 (\<lambda>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n) l \<in> P x) \<and>
             (\<lambda>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n) x \<notin> P x")
  apply (thin_tac "\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). i = j \<or> \<not> P i \<subseteq> P j")
  apply (thin_tac "\<forall>i\<in>Nset (Suc n). \<not> A \<subseteq> P i")
  apply (thin_tac "\<forall>k\<in>Nset (Suc n). prime_ideal R (P k)")
  apply (thin_tac "\<forall>i\<in>Nset (Suc n).
             nprod0 R (ppa R P A i) n \<in> A \<and>
             (\<forall>l\<in>Nset (Suc n) - {i}. nprod0 R (ppa R P A i) n \<in> P l) \<and>
             nprod0 R (ppa R P A i) n \<notin> P i")
  apply (thin_tac "\<forall>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n \<in> carrier R")
  apply (thin_tac "\<forall>i\<in>Nset (Suc n) - {x}. nprod0 R (ppa R P A i) n \<in> P x")
  apply (thin_tac "nprod0 R (ppa R P A x) n \<notin> P x")
  apply blast
apply (rule conjI)
  apply (rule ballI)
  apply simp
apply simp
 apply simp
 apply (thin_tac " A \<subseteq> UNION (Nset (Suc n)) P")
 apply (thin_tac "\<forall>i\<in>Nset (Suc n). \<forall>j\<in>Nset (Suc n). i = j \<or> \<not> P i \<subseteq> P j")
 apply (thin_tac "\<forall>i\<in>Nset (Suc n). \<not> A \<subseteq> P i")
 apply (thin_tac "\<forall>k\<in>Nset (Suc n). prime_ideal R (P k)")
 apply (thin_tac "\<forall>i\<in>Nset (Suc n). nprod0 R (ppa R P A i) n \<in> carrier R")
apply (rotate_tac -2)
 apply blast
apply (rule ballI)
 apply (simp add:ideal_subset)
done

lemma prime_ideal_cont1:"\<lbrakk>ring R; ideal R A; \<forall>i\<in>Nset n. prime_ideal R (P i);
A \<subseteq> \<Union> {X. (\<exists>i \<in> Nset n. X = (P i))} \<rbrakk> \<Longrightarrow> \<exists>i\<in>Nset n. A \<subseteq> (P i)"
apply (subgoal_tac "(\<lambda>i\<in>Nset n. (P i)) \<in> (Nset n) \<rightarrow> {X. prime_ideal R X}")
apply (subgoal_tac "A \<subseteq> \<Union> (\<lambda>i\<in>Nset n. (P i)) ` (Nset n)")
apply (subgoal_tac "\<exists>i\<in>Nset n. A \<subseteq> (restrict P (Nset n)) i")
apply (subgoal_tac "\<forall>i\<in>Nset n. A \<subseteq> restrict P (Nset n) i \<longrightarrow> (\<exists>i\<in>Nset n. A \<subseteq> P i)") apply blast
apply (thin_tac "\<exists>i\<in>Nset n. A \<subseteq> restrict P (Nset n) i")
 apply (rule ballI)
 apply (rule impI)
 apply (subgoal_tac "restrict P (Nset n) i = P i")
 apply blast
apply (simp add:restrict_def)
 apply (thin_tac "\<forall>i\<in>Nset n. prime_ideal R (P i)")
 apply (thin_tac "A \<subseteq> \<Union>{X. \<exists>i\<in>Nset n. X = P i}")
apply (subgoal_tac "\<forall>P. P \<in> Nset n \<rightarrow> Collect (prime_ideal R) \<and> A \<subseteq> \<Union>P ` Nset n \<longrightarrow> (\<exists>i\<in>Nset n. A \<subseteq> P i)")
apply blast
 apply (simp add:prime_ideal_cont1Tr [of "R" "A"])
apply (subgoal_tac "{X. \<exists>i\<in>Nset n. X = P i} = restrict P (Nset n) ` Nset n")
 apply simp
apply (rule equalityI)
 apply (rule subsetI)
 apply (rename_tac Y)
 apply (simp add:CollectI)
 apply (simp add:image_def)
 apply (rule subsetI) apply (rename_tac Y)
 apply (simp add:image_def CollectI)
apply (simp add:Pi_def)
done

lemma prod_n_ideal_contTr0:"ring R \<Longrightarrow> (\<forall>l\<in>Nset n. ideal R (J l)) \<longrightarrow>
 i\<Pi>\<^sub>R\<^sub>,\<^sub>n J  \<subseteq>  \<Inter>{X. (\<exists>k\<in>Nset n. X = (J k))}"
apply (induct_tac n)
 apply (simp add:Nset_def)
 apply (rule impI)
apply (subgoal_tac "\<Inter>{X. \<exists>k\<in>Nset (Suc n). X = J k} =
                           (\<Inter>{X. \<exists>k\<in>Nset n. X = J k}) \<inter> (J (Suc n))")
 apply (simp del:Int_subset_iff)
 apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<diamondsuit>\<^sub>R (J (Suc n)) \<subseteq> i\<Pi>\<^sub>R\<^sub>,\<^sub>n J")
 apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<diamondsuit>\<^sub>R (J (Suc n)) \<subseteq> J (Suc n)")
apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<diamondsuit>\<^sub>R (J (Suc n)) \<subseteq> (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) \<inter> (J (Suc n))")
apply (rule subsetI)
 apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<subseteq> \<Inter>{X. \<exists>k\<in>Nset n. X = J k}")
 apply (subgoal_tac "x \<in> i\<Pi>\<^sub>R\<^sub>,\<^sub>n J")
 apply (subgoal_tac "x \<in> J (Suc n)")
 apply (subgoal_tac "x \<in>  \<Inter>{X. \<exists>k\<in>Nset n. X = J k}")
 apply simp
 apply (rule subsetD, assumption+)
 apply (rule subsetD, assumption+)
 apply (rule subsetD, assumption+)
 apply (simp add:Nset_def)
 apply (rule subsetI)
  apply (subgoal_tac "x \<in> i\<Pi>\<^sub>R\<^sub>,\<^sub>n J")
  apply (subgoal_tac "x \<in> J (Suc n)")
 apply simp
 apply (rule subsetD, assumption+)
 apply (rule subsetD, assumption+)
 apply (rule ideal_prod_la2, assumption+)
 apply (simp add:Nset_def n_prod_ideal)
 apply (simp add:Nset_def)
 apply (rule ideal_prod_la1, assumption+)
 apply (simp add:Nset_def n_prod_ideal)
 apply (simp add:Nset_def)
  apply (thin_tac "(\<forall>l\<in>Nset n. ideal R (J l)) \<longrightarrow>
                         i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<subseteq> \<Inter>{X. \<exists>k\<in>Nset n. X = J k}")
apply (rule equalityI)
 apply (rule subsetI)
  apply (simp add:Nset_def)
 apply (rule conjI)
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "\<forall>k. k \<le> n \<and> xa = (J k) \<longrightarrow> x \<in> xa")
 apply blast apply (thin_tac "\<exists>k. k \<le> n \<and> xa = J k")
apply (rule allI) apply (rule impI) apply (erule conjE)
 apply simp
 apply (subgoal_tac "k \<le> Suc n")
apply blast apply simp
apply blast
 apply (rule subsetI)
 apply (simp add:Nset_def)
apply (rule allI) apply (rule impI)
 apply (subgoal_tac "\<forall>k. k \<le> Suc n \<and> xa = (J k) \<longrightarrow> x \<in> xa")
 apply blast apply (thin_tac "\<exists>k. k \<le> Suc n \<and> xa = J k")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (erule conjE)
 apply simp
 apply (case_tac "k = Suc n") apply simp
apply (subgoal_tac "k \<le> n") apply (thin_tac "k \<noteq> Suc n")
 apply (thin_tac " k \<le> Suc n")
 apply (thin_tac "x \<in> J (Suc n)")
 apply blast
apply (thin_tac "\<forall>l. l \<le> Suc n \<longrightarrow> ideal R (J l)")
apply (thin_tac "\<forall>xa. (\<exists>k. k \<le> n \<and> xa = J k) \<longrightarrow> x \<in> xa")
apply (frule le_imp_less_or_eq) apply (thin_tac " k \<le> Suc n")
apply simp
done

lemma prod_n_ideal_contTr:"\<lbrakk>ring R; \<forall>l\<in>Nset n. ideal R (J l)\<rbrakk> \<Longrightarrow>
 i\<Pi>\<^sub>R\<^sub>,\<^sub>n J  \<subseteq>  \<Inter>{X. (\<exists>k\<in>Nset n. X = (J k))}"
apply (simp add:prod_n_ideal_contTr0)
done

lemma prod_n_ideal_cont2:"\<lbrakk>ring R; \<forall>l\<in>Nset n. ideal R (J l); prime_ideal R P;
 \<Inter>{X. (\<exists>k\<in>Nset n. X = (J k))} \<subseteq> P \<rbrakk> \<Longrightarrow> \<exists>l\<in>Nset n. (J l) \<subseteq> P"
apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<subseteq> P")
 apply (simp add:ideal_n_prod_prime)
 apply (rule subsetI)
 apply (frule prod_n_ideal_contTr, assumption+)
 apply (subgoal_tac "x \<in> \<Inter>{X. \<exists>k\<in>Nset n. X = J k}")
 apply (rule subsetD, assumption+)
 apply (rule subsetD, assumption+)
done

lemma prod_n_ideal_cont3:"\<lbrakk>ring R; \<forall>l\<in>Nset n. ideal R (J l); prime_ideal R P;
 \<Inter>{X. (\<exists>k\<in>Nset n. X = (J k))} = P \<rbrakk> \<Longrightarrow> \<exists>l\<in>Nset n. (J l) = P"
apply (subgoal_tac "\<exists>l\<in>Nset n. (J l) \<subseteq> P")
 apply (subgoal_tac "\<forall>l\<in>Nset n. J l \<subseteq> P \<longrightarrow> (\<exists>l\<in>Nset n. J l = P)")
 apply blast apply (thin_tac "\<exists>l\<in>Nset n. J l \<subseteq> P")
 apply (rule ballI)
 apply (rule impI)
 apply (subgoal_tac "J l = P")
 apply blast
apply (rule equalityI, assumption+)
 apply (rule subsetI)
 apply (subgoal_tac "P = \<Inter>{X. \<exists>k\<in>Nset n. X = J k}")
 apply (thin_tac "\<Inter>{X. \<exists>k\<in>Nset n. X = J k} = P")
 apply simp
 apply blast
apply (rule sym, assumption)
apply (rule prod_n_ideal_cont2, assumption+)
apply simp
done

constdefs
 ideal_quotient::"[('a, 'b) RingType_scheme, 'a set, 'a set] \<Rightarrow> 'a set"
 "ideal_quotient R A B == {x| x. x \<in> carrier R \<and> (\<forall>b\<in>B. x \<cdot>\<^sub>R b \<in> A)}"

syntax
 "@IDEALQT"::"['a set, ('a, 'b) RingType_scheme, 'a set] \<Rightarrow> 'a set"
    ("(3_/ \<dagger>\<^sub>_/ _)" [82,82,83]82)

translations
 "A \<dagger>\<^sub>R B" =="ideal_quotient R A B"


lemma ideal_quotient_is_ideal:
  "\<lbrakk>ring R; ideal R A; ideal R B\<rbrakk> \<Longrightarrow> ideal R (ideal_quotient R A B)"
apply (rule ideal_condition, assumption+)
 apply (rule subsetI)
 apply (simp add:ideal_quotient_def CollectI)
 apply (simp add:ideal_quotient_def)
 apply (frule ring_zero [of "R"])
 apply (subgoal_tac "\<forall>b\<in>B. 0\<^sub>R \<cdot>\<^sub>R b \<in> A")
 apply blast
 apply (rule ballI)
 apply (frule_tac x = b in ring_times_0_x [of "R"])
 apply (simp add:ideal_subset) apply simp
 apply (simp add:ideal_zero)
apply (rule ballI)+
 apply (simp add:ideal_quotient_def) apply (erule conjE)+
 apply (rule conjI)
 apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:whole_ideal) apply assumption+
 apply (frule ring_is_ag)
 apply (simp add:ag_mOp_closed)
apply (rule ballI)
apply (subst ring_distrib2, assumption+)
 apply (simp add:ideal_subset) apply assumption
 apply (frule ring_is_ag) apply (simp add: ag_mOp_closed)
 apply (frule_tac a1 = y and b1 = b in ring_inv1_1 [THEN sym, of "R"],
                                                             assumption+)
 apply (simp add:ideal_subset) apply simp
 apply (rule ideal_pOp_closed, assumption+) apply simp
 apply (rule ideal_inv1_closed, assumption+) apply simp
apply (rule ballI)+
 apply (simp add:ideal_quotient_def)
 apply (rule conjI)
  apply (erule conjE)
  apply (simp add:ring_tOp_closed)
 apply (erule conjE)
apply (rule ballI)
 apply (subst ring_tOp_assoc, assumption+) apply (simp add:ideal_subset)
 apply (simp add:ideal_ring_multiple [of "R" "A"])
done

section "9. Addition of finite elements of a ring and ideal_multiplication"
text{* We consider sum in an abelian group *}

lemma func_pre:"f \<in> Nset (Suc n) \<rightarrow> A \<Longrightarrow> f \<in> Nset n \<rightarrow> A"
apply (simp add:Pi_def)
apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
done

lemma cmp_inj:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; inj_on f A; inj_on g B \<rbrakk> \<Longrightarrow>
         inj_on (cmp g f) A"
apply (simp add:inj_on_def [of "cmp g f"])
apply (rule ballI)+
apply (simp add:cmp_def) apply (rule impI)
apply (subgoal_tac "f x = f y")
apply (simp add:inj_on_def [of "f"])
apply (frule_tac x = x in funcset_mem [of "f" "A" "B"], assumption+)
apply (frule_tac x = y in funcset_mem [of "f" "A" "B"], assumption+)
apply (simp add:inj_on_def [of "g"])
done

lemma cmp_assoc:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; h \<in> C \<rightarrow> D; x \<in> A\<rbrakk> \<Longrightarrow>
                          (cmp h (cmp g f)) x  = (cmp (cmp h g) f) x"
apply (simp add:cmp_def)
done

lemma cmp_transpos:"\<lbrakk> i \<in> Nset n; i \<noteq> n; a \<in> Nset (Suc n)\<rbrakk> \<Longrightarrow>
  (cmp (transpos i n) (cmp (transpos n (Suc n)) (transpos i n))) a =
               transpos i (Suc n) a"
apply (case_tac "a = Suc n") apply simp
apply (subgoal_tac "transpos i n (Suc n) = Suc n")
apply (simp add:cmp_def)
apply (subgoal_tac "transpos n (Suc n) (Suc n) = n")
apply simp
apply (subgoal_tac "transpos i n n = i")
apply (subgoal_tac "transpos i (Suc n) (Suc n) = i")
apply simp
apply (simp add:transpos_def) apply (simp add:NSet_def)
apply (simp add:transpos_def) apply (simp add:NSet_def)
apply (simp add:transpos_def) apply (simp add:NSet_def)
apply (simp add:transpos_def) apply (simp add:NSet_def)
apply (frule Nset_le [of "i" "n"])
apply (frule le_less_trans [of "i" "n" "Suc n"]) apply simp
apply simp
apply (case_tac "a = n") apply (simp add:cmp_def)
apply (subgoal_tac "transpos i n n = i") apply simp
apply (subgoal_tac "transpos n (Suc n) i = i") apply simp
apply (subgoal_tac "transpos i n i = n") apply simp
apply (subgoal_tac "transpos i (Suc n) n = n") apply simp
apply (simp add:transpos_def NSet_def)+
 apply (simp add:Nset_def)
apply (simp add:transpos_def NSet_def)
apply (case_tac "a = i") apply (simp add:cmp_def)
apply (subgoal_tac "transpos i n i = n") apply simp
apply (subgoal_tac "transpos i (Suc n) i = Suc n") apply simp
apply (subgoal_tac "transpos n (Suc n) n = Suc n") apply simp
apply (subgoal_tac "transpos i n (Suc n) = Suc n") apply simp
apply (simp add:transpos_def NSet_def)
apply (simp add:transpos_def NSet_def)
apply (simp add:transpos_def NSet_def)
apply (simp add:transpos_def NSet_def)
apply (simp add:cmp_def)
apply (simp add:transpos_def NSet_def)
done

lemma eSum_memTr:"agroup R \<Longrightarrow>  f \<in> Nset n \<rightarrow> carrier R  \<longrightarrow>
                          (\<forall>i\<in>Nset n. eSum R f i \<in> carrier R)"
apply (induct_tac n)
 apply (rule impI)
 apply (rule ballI) apply (simp add:Nset_def)
 apply (rule funcset_mem, assumption+) apply (simp add:Nset_def)
apply (rule impI) apply (rule ballI)
 apply (case_tac "i \<le> n") apply (subgoal_tac "f \<in> Nset n \<rightarrow> carrier R")
 apply simp apply (frule_tac x = i and n = n in mem_of_Nset)
 apply simp
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (subgoal_tac "x \<in> Nset (Suc n)") apply simp apply (simp add:Nset_def)
apply (simp add:le_def)
apply (frule_tac m = n and n = i in Suc_leI)
apply (frule Nset_le)
apply (frule_tac m = i and n = "Suc n" in le_anti_sym, assumption+)
 apply simp
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> carrier R")
 apply (rule ag_pOp_closed, assumption+)
 apply (subgoal_tac "n \<in> Nset n")
 apply simp apply (simp add:Nset_def) apply (simp add:funcset_mem)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def)
done

lemma eSum_mem1Tr:"\<lbrakk>agroup R; J <+ R \<rbrakk> \<Longrightarrow>
                     f \<in> Nset n \<rightarrow> J  \<longrightarrow> eSum R f n \<in> J"
apply (induct_tac n)
 apply (rule impI)
 apply (simp add:Nset_def)
 apply (rule funcset_mem, assumption+) apply simp
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (rule asubg_pOp_closed, assumption+)
 apply (thin_tac "f \<in> Nset n \<rightarrow> J")
 apply (simp add:Nset_def funcset_mem)
done

lemma eSum_mem:"\<lbrakk>agroup R; f \<in> Nset n \<rightarrow> carrier R; i \<in> Nset n\<rbrakk> \<Longrightarrow>
                eSum R f i \<in> carrier R"
apply (simp add:eSum_memTr)
done

lemma eSum_mem1:"\<lbrakk>agroup R; J <+ R ; f \<in> Nset n \<rightarrow> J\<rbrakk> \<Longrightarrow> eSum R f n \<in> J"
apply (simp add:eSum_mem1Tr)
done

lemma eSum_eqTr:"agroup R \<Longrightarrow> f \<in> Nset n \<rightarrow> carrier R \<and> g \<in> Nset n \<rightarrow> carrier R \<and> ( \<forall>l\<in>Nset n. f l = g l) \<longrightarrow> eSum R f n = eSum R g n"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+ apply (simp add:Nset_def)
apply (rule impI) apply (erule conjE)+
apply (subgoal_tac "\<forall>l. l \<in> Nset n \<longrightarrow> l \<in> Nset (Suc n)")
prefer 2 apply (simp add:Nset_def) apply simp
apply (subgoal_tac "eSum R f n = eSum R g n")
apply (subgoal_tac "f (Suc n) = g (Suc n)") apply simp
 apply (simp add:Nset_def)
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> carrier R \<and> g \<in> Nset n \<rightarrow> carrier R")
 apply simp
apply (thin_tac "f \<in> Nset n \<rightarrow> carrier R \<and> g \<in> Nset n \<rightarrow> carrier R \<longrightarrow>
           eSum R f n = eSum R g n")
apply (thin_tac "\<forall>l\<in>Nset (Suc n). f l = g l")
apply (rule conjI)
apply (simp add:Pi_def)+
done

lemma eSum_eq:"\<lbrakk>agroup R; f \<in> Nset n \<rightarrow> carrier R; g \<in> Nset n \<rightarrow> carrier R;
 \<forall>l\<in>Nset n. f l = g l\<rbrakk> \<Longrightarrow> eSum R f n = eSum R g n"
apply (simp add:eSum_eqTr)
done

lemma eSum_eq_i:"\<lbrakk>agroup R; f \<in> Nset n \<rightarrow> carrier R; g \<in> Nset n \<rightarrow> carrier R;
 i \<in> Nset n;  \<forall>l\<in>Nset i. f l = g l\<rbrakk> \<Longrightarrow> eSum R f i = eSum R g i"
apply (subgoal_tac "\<forall>l. l \<in> Nset i \<longrightarrow> l \<in> Nset n")
apply (subgoal_tac "f \<in> Nset i \<rightarrow> carrier R")
apply (subgoal_tac "g \<in> Nset i \<rightarrow> carrier R")
apply (rule eSum_eq, assumption+)
apply (simp add:Pi_def)+
apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
done

lemma eSum_cmp_eq:"\<lbrakk>agroup R; f \<in> Nset n \<rightarrow> carrier R; h1 \<in> Nset n \<rightarrow> Nset n;
 h2 \<in> Nset n \<rightarrow> Nset n; i \<in> Nset n\<rbrakk> \<Longrightarrow>
 eSum R (cmp f (cmp h2 h1)) i = eSum R (cmp (cmp f h2) h1) i"
apply (rule eSum_eq_i [of "R" "cmp f (cmp h2 h1)" "n" "cmp (cmp f h2) h1" "i"],
                                                           assumption+)
apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
apply (simp add:cmp_def)
apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
apply (simp add:cmp_def) apply assumption
apply (rule ballI)
apply (simp add:cmp_def)
done

lemma eSum_cmp_eq_transpos:"\<lbrakk>agroup R; f \<in> Nset (Suc n) \<rightarrow> carrier R; i \<in> Nset n;i \<noteq> n \<rbrakk> \<Longrightarrow>
 eSum R (cmp f (cmp (transpos i n) (cmp (transpos n (Suc n)) (transpos i n))))
 (Suc n) = eSum R (cmp f (transpos i (Suc n))) (Suc n)"
apply (rule eSum_eq [of "R" "cmp f (cmp (transpos i n) (cmp (transpos n (Suc n)) (transpos i n)))" "Suc n" "cmp f (transpos i (Suc n))"], assumption+)
apply (rule cmp_fun [of _ "Nset (Suc n)" "Nset (Suc n)" _ "carrier R"])
apply (rule cmp_fun [of _ "Nset (Suc n)" "Nset (Suc n)" _ "Nset (Suc n)"])+
apply (rule transpos_hom)
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply simp
apply (rule transpos_hom)
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply simp
apply (rule transpos_hom)
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply simp
apply assumption
apply (rule cmp_fun [of _ "Nset (Suc n)" "Nset (Suc n)" _ "carrier R"])
apply (rule transpos_hom)
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (frule Nset_le [of "i" "n"])
 apply (frule le_less_trans [of "i" "n" "Suc n"]) apply simp apply simp
 apply assumption
apply (rule ballI)
 apply (simp add:cmp_def)
 apply (frule_tac a = l in cmp_transpos [of "i" "n"], assumption+)
 apply (simp add:cmp_def)
done

lemma transpos_Tr_n1:"Suc (Suc 0) \<le> n \<Longrightarrow>
                           transpos (n - Suc 0) n n = n - Suc 0"
apply (simp add:transpos_def)
apply (rule conjI) apply (rule impI) apply (simp add:NSet_def)
apply (rule impI) apply (rule impI) apply (simp add:NSet_def)
done

lemma transpos_Tr_n2:"Suc (Suc 0) \<le> n \<Longrightarrow>
               transpos (n - (Suc 0)) n (n - (Suc 0)) = n"
apply (simp add:transpos_def)
apply (simp add:NSet_def)
done

lemma additionTr0:"\<lbrakk>agroup R; 0 < n; f \<in> Nset n \<rightarrow> carrier R\<rbrakk>
 \<Longrightarrow> eSum R (cmp f (transpos (n - 1) n)) n = eSum R f n"
apply (case_tac "n \<le> 1")
 apply simp
 apply (frule Suc_leI [of "0" "n"])
 apply (frule le_anti_sym [of "n" "Suc 0"], assumption+) apply simp
 apply (simp add:cmp_def)
 apply (subgoal_tac "0 \<in> Nset (Suc 0)")
 apply (subgoal_tac "Suc 0 \<in> Nset (Suc 0)")
 apply (subst transpos_ij_1, assumption+) apply simp
 apply (subst transpos_ij_2, assumption+) apply simp
 apply (rule ag_pOp_commute, assumption+)
 apply (simp add:funcset_mem)+ apply (simp add:Nset_def)
  apply (simp add:Nset_def)
apply (simp add:le_def)
apply (frule_tac Suc_leI [of "Suc 0" "n"])
apply (subgoal_tac "0 < n")
apply (simplesubst jointgd_tool2 [of "n"], assumption+)
apply (simp del:Suc_pred) apply simp
prefer 2 apply simp
apply (subgoal_tac "0 < n - Suc 0")
apply (simplesubst jointgd_tool2 [of "n - Suc 0"], assumption+)
apply (simp del:Suc_pred)
prefer 2 apply simp
apply (subgoal_tac "eSum R (cmp f (transpos (Suc (n - Suc (Suc 0))) n))
          (n - Suc (Suc 0)) = eSum R f (n - Suc (Suc 0))")
apply simp
 apply (thin_tac " eSum R (cmp f (transpos (Suc (n - Suc (Suc 0))) n))
        (n - Suc (Suc 0)) = eSum R f (n - Suc (Suc 0))")
 apply (simp add:cmp_def)
 apply (subgoal_tac "transpos (Suc (n - Suc (Suc 0))) n (Suc (n - Suc (Suc 0)))
                        = n") apply simp
 apply (thin_tac "transpos (Suc (n - Suc (Suc 0))) n (Suc (n - Suc (Suc 0))) = n")
 apply (subgoal_tac "transpos (Suc (n - Suc (Suc 0))) n n = Suc (n - Suc (Suc 0))") apply simp
 apply (thin_tac "transpos (Suc (n - Suc (Suc 0))) n n = Suc (n - Suc (Suc 0))")
 apply (subgoal_tac "Suc (n - Suc(Suc 0)) = n - Suc 0")
 apply simp
apply (subgoal_tac "eSum R f (n - Suc (Suc 0)) \<in> carrier R")
apply (subgoal_tac "f (n - Suc 0) \<in> carrier R")
apply (subgoal_tac "f n \<in> carrier R")
apply (subst ag_pOp_assoc, assumption+)
apply (subst ag_pOp_assoc, assumption+)
apply (simp add:ag_pOp_commute)
apply (rule funcset_mem, assumption+) apply (simp add:Nset_def)
apply (rule funcset_mem, assumption+) apply (simp add:Nset_def)
apply (rule  eSum_mem, assumption+) apply (simp add:Nset_def)
 apply (simp add:Suc_Suc_Tr)+
 apply (simp add:transpos_Tr_n1)
 apply (simp add:Suc_Suc_Tr)
 apply (simp add:transpos_Tr_n2)
apply (simp add:Suc_Suc_Tr)
apply (subgoal_tac "\<forall>l\<in>Nset (n - (Suc (Suc 0))).  (cmp f (transpos (n - Suc 0) n)) l = f l")
apply (rule eSum_eq_i [of "R" "cmp f (transpos (n - Suc 0) n)"
                                      "n" "f" "n - Suc (Suc 0)"], assumption+)
apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:cmp_def)
 apply (subgoal_tac "n - Suc 0 \<in> Nset n")
 apply (subgoal_tac "n \<in> Nset n")
 apply (frule_tac l = x in transpos_mem [of "n - Suc 0" "n" "n"], assumption+)
 apply (frule Suc_pos [of "Suc 0" "n"])
 apply (simplesubst Suc_pred [THEN sym, of "n"], assumption)
 apply (simp del:Suc_pred) apply assumption+
 apply simp apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply assumption apply (simp add:Nset_def) apply simp
apply (rule ballI)
 apply (simp add:cmp_def)
 apply (subst transpos_id [of "n - Suc 0" "n" "n"])
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (frule Suc_pos [of "Suc 0" "n"])
 apply (simplesubst Suc_pred [THEN sym, of "n"], assumption)
 apply (simp del:Suc_pred)
 apply (simp add:Nset_Suc_Suc) apply simp
done

lemma additionTr1:"\<lbrakk>agroup R; \<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
 h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
 eSum R (cmp f h) (Suc n) = eSum R f (Suc n); f \<in> Nset (Suc (Suc n)) \<rightarrow> carrier R; h \<in> Nset (Suc (Suc n)) \<rightarrow> Nset (Suc (Suc n)); inj_on h (Nset (Suc (Suc n))); h (Suc (Suc n)) = Suc (Suc n)\<rbrakk>
        \<Longrightarrow> eSum R (cmp f h) (Suc (Suc n)) = eSum R f (Suc (Suc n))"
apply (subgoal_tac "f \<in> Nset (Suc n) \<rightarrow> carrier R")
apply (subgoal_tac "h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n)")
apply (subgoal_tac "inj_on h (Nset (Suc n))")
apply (subgoal_tac "eSum R (cmp f h) (Suc n) = eSum R f (Suc n)")
apply (thin_tac "\<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
       h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
       eSum R (cmp f h) (Suc n) = eSum R f (Suc n)")
prefer 2 apply simp
apply simp
 apply (thin_tac "eSum R (cmp f h) n +\<^sub>R (cmp f h (Suc n)) =  eSum R f n +\<^sub>R (f (Suc n))")
 apply (simp add:cmp_def)
 apply (thin_tac "\<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
       h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
       eSum R (cmp f h) (Suc n) = eSum R f (Suc n)")
 apply (frule Nset_injTr0 [of "h" "Suc n"], assumption+) apply simp
 apply (frule Nset_injTr0 [of "h" "Suc n"], assumption+) apply simp
apply (thin_tac "\<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
       h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
       eSum R (cmp f h) (Suc n) = eSum R f (Suc n)")
apply (thin_tac "h \<in> Nset (Suc (Suc n)) \<rightarrow> Nset (Suc (Suc n))")
apply (simp add:Pi_def [of "Nset (Suc n)"])
apply (rule allI) apply (rule impI)
apply (subgoal_tac "x \<in> Nset (Suc (Suc n))") apply (simp add:funcset_mem)
apply (simp add:Nset_def)
done

lemma additionTr1_1:"\<lbrakk>agroup R; \<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
 h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
 eSum R (cmp f h) (Suc n) = eSum R f (Suc n); f \<in> Nset (Suc (Suc n)) \<rightarrow> carrier R; i \<in> Nset n\<rbrakk> \<Longrightarrow> eSum R (cmp f (transpos i (Suc n))) (Suc (Suc n)) = eSum R f (Suc (Suc n))"
apply (rule additionTr1 [of "R" "n" "f" "transpos i (Suc n)"], assumption+)
apply (rule transpos_hom [of "i" "Suc (Suc n)" "Suc n"])
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (frule Nset_le [of "i" "n"])
 apply (frule le_less_trans [of "i" "n" "Suc n"]) apply simp apply simp
 apply (rule transpos_inj [of "i" "Suc (Suc n)" "Suc n"])
  apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (frule Nset_le [of "i" "n"])
 apply (frule le_less_trans [of "i" "n" "Suc n"]) apply simp apply simp
apply (simp add:transpos_def NSet_def)
 apply (frule Nset_le [of "i" "n"])
 apply (frule le_less_trans [of "i" "n" "Suc (Suc n)"]) apply simp apply simp
done

lemma additionTr1_2:"\<lbrakk>agroup R; \<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
 h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
 eSum R (cmp f h) (Suc n) = eSum R f (Suc n); f \<in> Nset (Suc (Suc n)) \<rightarrow> carrier R; i \<in> Nset (Suc n)\<rbrakk> \<Longrightarrow> eSum R (cmp f (transpos i (Suc (Suc n)))) (Suc (Suc n)) = eSum R f (Suc (Suc n))"
apply (case_tac "i = Suc n")
 apply (simp del:eSum_Suc)
apply (subgoal_tac "0 < Suc (Suc n)")
apply (frule additionTr0 [of "R" "Suc (Suc n)" "f"], assumption+)
apply simp apply simp
apply (frule Nset_pre [of "i" "n"], assumption+)
apply (subst eSum_cmp_eq_transpos [THEN sym, of "R" "f"
                                         "Suc n" "i"], assumption+)
apply (subst eSum_cmp_eq [of "R" "f" "Suc (Suc n)"  "cmp (transpos (Suc n) (Suc(Suc n))) (transpos i (Suc n))" "transpos i (Suc n)" "Suc (Suc n)"], assumption+)
apply (rule cmp_fun [of _ "Nset (Suc (Suc n))" "Nset (Suc (Suc n))" _ "Nset (Suc (Suc n))"])
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply assumption
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply simp
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply assumption apply (simp add:Nset_def)
apply (subst eSum_cmp_eq [of "R" "cmp f (transpos i (Suc n))" "Suc (Suc n)"  "(transpos i (Suc n))" "transpos (Suc n) (Suc (Suc n))" "Suc (Suc n)"], assumption+)
apply (rule cmp_fun [of _ "Nset (Suc (Suc n))"
                       "Nset (Suc (Suc n))" "f" "carrier R"])
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply assumption+
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply assumption
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply simp apply (simp add:Nset_def)
apply (subst additionTr1_1 [of "R" "n" "cmp (cmp f (transpos i (Suc n)))
               (transpos (Suc n) (Suc (Suc n)))" "i"], assumption+)
apply (rule  cmp_fun [of _ "Nset (Suc (Suc n))"
                       "Nset (Suc (Suc n))" _ "carrier R"])
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply simp
apply (rule cmp_fun [of _ "Nset (Suc (Suc n))"
                       "Nset (Suc (Suc n))" "f" "carrier R"])
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply assumption+
apply (subgoal_tac "0 < Suc (Suc n)")
apply (frule additionTr0 [of "R" "Suc (Suc n)" "cmp f (transpos i (Suc n))"],
                                                     assumption+)
apply (rule cmp_fun [of _ "Nset (Suc (Suc n))"
                       "Nset (Suc (Suc n))" "f" "carrier R"])
apply (rule transpos_hom) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply assumption+
apply (simp del:eSum_Suc)
apply (thin_tac "eSum R (cmp (cmp f (transpos i (Suc n))) (transpos (Suc n) (Suc (Suc n)))) (Suc (Suc n)) = eSum R (cmp f (transpos i (Suc n))) (Suc (Suc n))")
apply (rule additionTr1_1, assumption+)
apply simp
done

lemma additionTr2:"agroup R \<Longrightarrow> \<forall>f. \<forall>h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
 h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow> eSum R (cmp f h) (Suc n) = eSum R f (Suc n)"
apply (induct_tac n)
 apply (rule allI)+
 apply (rule impI) apply (erule conjE)+
 apply (simp add:cmp_def)
 apply (case_tac "h 0 = 0")
  apply (subgoal_tac "h (Suc 0) = Suc 0") apply simp
  apply (thin_tac "f \<in> Nset (Suc 0) \<rightarrow> carrier R")
  apply (simp add:Nset_def) apply (simp add:Nset_1)
  apply (subgoal_tac "Suc 0 \<in> {0, Suc 0}")
  apply (frule_tac f = h in funcset_mem [of _ "{0, Suc 0}"
                              "{0, Suc 0}" "Suc 0"], assumption+)
  apply (simp add:CollectI)
  apply (case_tac "h (Suc 0) = Suc 0") apply simp apply simp
  apply (simp add:inj_on_def)
  apply (simp add:Nset_def) apply (simp add:Nset_1)
  apply (subgoal_tac "0 \<in> {0, Suc 0}") prefer 2 apply simp
  apply (frule_tac f = h in funcset_mem [of _ "{0, Suc 0}" "{0, Suc 0}" "0"], assumption+)
  apply simp apply (subgoal_tac "h (Suc 0) = 0") apply simp
  apply (rule ag_pOp_commute, assumption+)
  apply (rule funcset_mem, assumption+) apply simp
  apply (rule funcset_mem, assumption+) apply simp
  apply (subgoal_tac "Suc 0 \<in> {0, Suc 0}")
  apply (frule_tac f = h in funcset_mem, assumption+) apply (simp add:CollectI)
  apply (case_tac "h (Suc 0) = 0") apply simp apply fastsimp
  apply simp
(************* n *****************)
apply (rule allI)+
apply (rule impI) apply (erule conjE)+
apply (case_tac "h (Suc (Suc n)) = Suc (Suc n)")
apply (rule additionTr1, assumption+)
apply (frule_tac f = h and n = "Suc (Suc n)" in inj_surj, assumption+)
 apply (subgoal_tac "Suc (Suc n) \<in> h ` Nset (Suc (Suc n))")
 apply (thin_tac "h ` Nset (Suc (Suc n)) = Nset (Suc (Suc n))")
 apply (simp del:eSum_Suc add:image_def)
 apply (subgoal_tac "\<forall>x\<in>Nset (Suc (Suc n)). Suc (Suc n) = h x \<longrightarrow>
               eSum R (cmp f h) (Suc (Suc n)) = eSum R f (Suc (Suc n))")
 apply blast apply (thin_tac "\<exists>x\<in>Nset (Suc (Suc n)). Suc (Suc n) = h x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "(cmp h (transpos x (Suc (Suc n)))) (Suc (Suc n)) =
              Suc (Suc n)")
 prefer 2 apply (subgoal_tac "transpos x (Suc (Suc n)) (Suc (Suc n)) = x")
 apply simp apply (simp add:cmp_def)
  apply (thin_tac "\<forall>f h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
                h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
                eSum R (cmp f h) (Suc n) = eSum R f (Suc n)")
  apply (rotate_tac -1) apply (frule sym) apply (thin_tac "Suc (Suc n) = h x")
  apply (subgoal_tac "h x \<noteq> h (Suc (Suc n))")
 apply (frule_tac f = h and A = "Nset (Suc (Suc n))" and x = x and y = "Suc (Suc n)" in inj_onTr2, assumption+)
  apply (simp add:Nset_def) apply assumption+
  apply (simp add:transpos_def) apply (simp add:NSet_def)
  apply simp
prefer 2 apply simp apply (simp add:Nset_def)
 apply (subgoal_tac "cmp h (transpos x (Suc (Suc n))) \<in> Nset (Suc (Suc n)) \<rightarrow>
                       Nset (Suc (Suc n))")
 apply (subgoal_tac "inj_on (cmp h (transpos x (Suc (Suc n)))) (Nset (Suc (Suc n)))")
 apply (subgoal_tac "eSum R (cmp f (cmp h (transpos x (Suc (Suc n))))) (Suc (Suc n)) = eSum R f (Suc (Suc n))")
prefer 2
  apply (rule additionTr1, assumption+)
  apply (frule_tac s = "Suc (Suc n)" and t = "h x" in sym)
  apply (thin_tac "Suc (Suc n) = h x") apply (rotate_tac -2)
  apply (frule sym)
  apply (thin_tac "eSum R (cmp f (cmp h (transpos x (Suc (Suc n)))))
  (Suc (Suc n)) = eSum R f (Suc (Suc n))") apply (simp del:eSum_Suc)
  apply (thin_tac "eSum R f (Suc (Suc n)) =
          eSum R (cmp f (cmp h (transpos x (Suc (Suc n))))) (Suc (Suc n))")
  apply (frule_tac f = f and n = "Suc (Suc n)" and ?h1.0 = "transpos x (Suc (Suc n))" and ?h2.0 = h and i = "Suc (Suc n)" in eSum_cmp_eq [of "R"], assumption+)
  apply (rule transpos_hom, assumption+) apply (simp add:Nset_def)
  apply (thin_tac "\<forall>f h. f \<in> Nset (Suc n) \<rightarrow> carrier R \<and>
                h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n) \<and> inj_on h (Nset (Suc n)) \<longrightarrow>
                eSum R (cmp f h) (Suc n) = eSum R f (Suc n)")
  apply (rule contrapos_pp, simp+) apply (simp add:Nset_def)
apply (simp del:eSum_Suc)
 apply (thin_tac "eSum R (cmp f (cmp h (transpos x (Suc (Suc n))))) (Suc
 (Suc n)) = eSum R (cmp (cmp f h) (transpos x (Suc (Suc n)))) (Suc (Suc n))")
  apply (rule_tac n1 = n and f1 = "cmp f h" and i1 = x in additionTr1_2 [THEN sym, of "R"], assumption+)
  apply (rule_tac f = h and A = "Nset (Suc (Suc n))" and
  B = "Nset (Suc (Suc n))" and g = f in  cmp_fun, assumption+)
  apply (subgoal_tac "x \<noteq> Suc (Suc n)") apply (rule Nset_pre, assumption+)
  apply (rule contrapos_pp, simp) apply simp
  apply (frule_tac s = "Suc (Suc n)" and t = "h x" in sym)
  apply (thin_tac "Suc (Suc n) = h x")
  apply (frule_tac i = x and n = "Suc (Suc n)" and j = "Suc (Suc n)" in transpos_inj) apply (simp add:Nset_def) apply (rule contrapos_pp)
  apply simp apply simp
  apply (subgoal_tac "transpos x (Suc (Suc n)) \<in> Nset (Suc (Suc n)) \<rightarrow>
                                                   Nset (Suc (Suc n))")
  apply (rule_tac f = "transpos x (Suc (Suc n))" and A = "Nset (Suc (Suc n))"
  and B = "Nset (Suc (Suc n))" and g = h and C = "Nset (Suc (Suc n))" in cmp_inj, assumption+)
  apply (rule transpos_hom) apply simp apply (simp add:Nset_def)
  apply (rule contrapos_pp) apply simp apply simp
  apply (subgoal_tac "transpos x (Suc (Suc n)) \<in> Nset (Suc (Suc n)) \<rightarrow>
                                                   Nset (Suc (Suc n))")
  apply (rule cmp_fun, assumption+)
  apply (rule transpos_hom) apply simp apply (simp add:Nset_def)
  apply (rule contrapos_pp, simp+)
done

lemma addition2:"\<lbrakk>agroup R; f \<in> Nset (Suc n) \<rightarrow> carrier R;
 h \<in> Nset (Suc n) \<rightarrow> Nset (Suc n); inj_on h (Nset (Suc n))\<rbrakk> \<Longrightarrow>
  eSum R (cmp f h) (Suc n) = eSum R f (Suc n)"
apply (simp del:eSum_Suc add:additionTr2)
done

lemma addition21:"\<lbrakk>agroup R; f \<in> Nset n \<rightarrow> carrier R;
 h \<in> Nset n \<rightarrow> Nset n; inj_on h (Nset n)\<rbrakk> \<Longrightarrow>
  eSum R (cmp f h) n = eSum R f n"
apply (case_tac "n = 0")
 apply simp
 apply (subgoal_tac "h 0 = 0") apply (simp add:cmp_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule_tac f = h and A = "Nset 0" and B = "Nset 0" in funcset_mem, assumption+) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply simp
 apply (frule_tac R = R and f = f and n = "n - Suc 0" and h = h in addition2)
 apply simp+
done


lemma addition3:"\<lbrakk>agroup R; f \<in> Nset (Suc n) \<rightarrow> carrier R; j \<in> Nset (Suc n);
j \<noteq> Suc n\<rbrakk> \<Longrightarrow> eSum R f (Suc n) = eSum R (cmp f (transpos j (Suc n))) (Suc n)"
apply (rule addition2 [THEN sym,of "R" "f" "n" "transpos j (Suc n)"], assumption+)
apply (simp add:transpos_hom n_in_Nsetn)
apply (simp add:transpos_inj n_in_Nsetn)
done


lemma eSum_splitTr:"agroup R \<Longrightarrow> f \<in> Nset (Suc (n + m)) \<rightarrow> carrier R \<longrightarrow>
   eSum R f (Suc (n + m)) = eSum R f n +\<^sub>R (eSum R (cmp f (slide (Suc n))) m)"
apply (induct_tac m)
apply (rule impI) apply (simp add:slide_def cmp_def)
apply (rule impI)
apply (subgoal_tac "f \<in> Nset (Suc (n + na)) \<rightarrow> carrier R")
apply (simp del:eSum_Suc) apply simp
apply (subgoal_tac "f (Suc (Suc (n + na))) = (cmp f (slide (Suc n))) (Suc na)")
apply simp
apply (rule ag_pOp_assoc, assumption+)
apply (rule eSum_mem, assumption+)
 apply (simp add:Nset_def)
 apply (subgoal_tac "(cmp f (slide (Suc n))) \<in> Nset na \<rightarrow> carrier R")
 apply (rule eSum_mem, assumption+) apply (simp add:Nset_def)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:cmp_def slide_def)
 apply (frule Nset_le)
 apply (subgoal_tac "n \<le> n")
 apply (frule_tac i = n and j = n and k = x and l = na in add_le_mono)
 apply assumption
 apply (frule_tac i = "n + x" and j = "n + na" and k = "Suc (n + na)" in
                                                 le_less_trans)
 apply simp
 apply (frule_tac m = "n + x" and n = "Suc (n + na)" in Suc_leI)
 apply (frule_tac x = "Suc (n + x)" and n = "Suc (n + na)" in mem_of_Nset)
 apply simp apply simp
 apply (subgoal_tac "Suc (Suc (n + na)) \<in> Nset (Suc (Suc (n + na)))")
 apply (frule_tac A = "Nset (Suc (Suc (n + na)))" and B = "carrier R" and
 x = "Suc (Suc (n + na))" in funcset_mem [of "f"], assumption+)
 apply (frule_tac s = "f (Suc (Suc (n + na)))" and t = " cmp f (slide (Suc n)) (Suc na)" in sym) apply simp apply (simp add:Nset_def)
 apply (thin_tac "eSum R f (n + na) +\<^sub>R (f (Suc (n + na))) =
             eSum R f n +\<^sub>R (eSum R (cmp f (slide (Suc n))) na)")
 apply (simp add:cmp_def slide_def)
 apply (thin_tac "f \<in> Nset (Suc (n + na)) \<rightarrow> carrier R \<longrightarrow>
 eSum R f (Suc (n + na)) = eSum R f n +\<^sub>R (eSum R (cmp f (slide (Suc n))) na)")
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def)
done

lemma eSum_split:"\<lbrakk>agroup R; f \<in> Nset (Suc (n + m)) \<rightarrow> carrier R \<rbrakk> \<Longrightarrow>
   eSum R f (Suc (n + m)) = eSum R f n +\<^sub>R (eSum R (cmp f (slide (Suc n))) m)"  apply (simp del:eSum_Suc add:eSum_splitTr)
done

lemma ag_minus_apb:"\<lbrakk>agroup G; a \<in>carrier G; b \<in> carrier G \<rbrakk> \<Longrightarrow>
                         -\<^sub>G (a +\<^sub>G b) = -\<^sub>G a +\<^sub>G (-\<^sub>G b)"
apply (frule ag_l_inv1 [of "G" "a +\<^sub>G b"])
 apply (simp add:ag_pOp_closed)
apply (subgoal_tac "-\<^sub>G ( a +\<^sub>G b) +\<^sub>G ( a +\<^sub>G b) +\<^sub>G (-\<^sub>G b) = 0\<^sub>G +\<^sub>G (-\<^sub>G b)")
 prefer 2 apply simp
 apply (thin_tac "-\<^sub>G ( a +\<^sub>G b) +\<^sub>G ( a +\<^sub>G b) = 0\<^sub>G")
 apply (frule ag_mOp_closed [of "G" "b"], assumption+)
 apply (simp add:ag_l_zero)
 apply (frule ag_pOp_closed [of "G" "a" "b"], assumption+)
 apply (frule ag_mOp_closed [of "G" "a +\<^sub>G b"], assumption+)
 apply (simp add:ag_pOp_assoc)
 apply (simp add:ag_r_inv1)
 apply (simp add:ag_r_zero)
 apply (frule ag_mOp_closed [of "G" "a"], assumption+)
apply (subgoal_tac "-\<^sub>G ( a +\<^sub>G b) +\<^sub>G a +\<^sub>G (-\<^sub>G a) = -\<^sub>G b +\<^sub>G (-\<^sub>G a)")
 prefer 2 apply simp
 apply (thin_tac "-\<^sub>G ( a +\<^sub>G b) +\<^sub>G a = -\<^sub>G b")
 apply (simp add:ag_pOp_assoc [of "G" "-\<^sub>G ( a +\<^sub>G b)" "a" "-\<^sub>G a"])
 apply (simp add:ag_r_inv1)
 apply (simp add:ag_r_zero)
apply (simp add:ag_pOp_commute)
done

lemma eSum_minusTr:"agroup G \<Longrightarrow> f \<in> Nset n \<rightarrow> carrier G \<longrightarrow>
                    -\<^sub>G (eSum G f n) = eSum G (\<lambda>x\<in>Nset n. -\<^sub>G (f x)) n"
apply (induct_tac n)
 apply (rule impI)
 apply (simp add:Nset_def)
apply (rule impI)
 apply (frule func_pre)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply simp
 apply (subst ag_minus_apb, assumption+)
 apply (frule_tac n = n and i = n in eSum_mem [of "G" "f"], assumption+)
 apply (simp add:Nset_def) apply assumption
 apply (simp add:funcset_mem)
 apply (subgoal_tac "e\<Sigma> G (\<lambda>u. if u \<in> Nset (Suc n) then -\<^sub>G (f u) else arbitrary) n = e\<Sigma> G (\<lambda>u. if u \<in> Nset n then -\<^sub>G (f u) else arbitrary) n")
 apply simp
 apply (rule_tac n = n and f = "\<lambda>u. if u \<in> Nset (Suc n) then -\<^sub>G (f u) else arbitrary" and g = "\<lambda>u. if u \<in> Nset n then -\<^sub>G (f u) else arbitrary" in eSum_eq_i [of "G"], assumption+)
 apply (thin_tac "-\<^sub>G e\<Sigma> G f n =
           e\<Sigma> G (\<lambda>u. if u \<in> Nset n then -\<^sub>G (f u) else arbitrary) n")
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> carrier G")
 apply (simp add:Pi_def) apply (rule allI)
 apply (rule conjI) apply (rule impI) apply (rule impI)
 apply (rule ag_mOp_closed, assumption+) apply simp
 apply (rule impI)+
 apply (subgoal_tac "x \<in> Nset (Suc n)") apply simp
 apply (thin_tac "x \<notin> Nset (Suc n)") apply (simp add:Nset_def)
 apply (thin_tac "-\<^sub>G e\<Sigma> G f n =
           e\<Sigma> G (\<lambda>u. if u \<in> Nset n then -\<^sub>G (f u) else arbitrary) n")
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> carrier G")
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (rule ag_mOp_closed, assumption+)
 apply simp apply (simp add:Nset_def)
apply (rule ballI)
 apply (subgoal_tac "l \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def)+
done

lemma eSum_minus:"\<lbrakk>agroup G; f \<in> Nset n \<rightarrow> carrier G \<rbrakk> \<Longrightarrow>
                    -\<^sub>G (eSum G f n) = eSum G (\<lambda>x\<in>Nset n. -\<^sub>G (f x)) n"
apply (simp add:eSum_minusTr)
done

lemma ring_eSum_zeroTr:"agroup G \<Longrightarrow>  f \<in> Nset n \<rightarrow> carrier G \<and> (\<forall>j\<in>Nset n. f j = 0\<^sub>G) \<longrightarrow> eSum G f n = 0\<^sub>G"
apply (induct_tac n)
apply (rule impI) apply (erule conjE)+ apply simp
 apply (simp add:Nset_def)
apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "e\<Sigma> G f n = 0\<^sub>G") prefer 2
 apply (frule func_pre [of "f"])
 apply (subgoal_tac "\<forall>j. j \<in> Nset n \<longrightarrow> j \<in> Nset (Suc n)")
apply simp apply (simp add:Nset_def)
 apply simp apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply simp
 apply (frule ag_inc_zero [of "G"])
apply (simp add:ag_l_zero) apply (simp add:Nset_def)
done

lemma ring_eSum_zero:"\<lbrakk>agroup G; f \<in> Nset n \<rightarrow> carrier G; \<forall>j\<in>Nset n. f j = 0\<^sub>G \<rbrakk> \<Longrightarrow>  e\<Sigma> G f n = 0\<^sub>G"
apply (simp add:ring_eSum_zeroTr)
done

lemma ag_eSum_1_nonzeroTr:"agroup G \<Longrightarrow> \<forall>f. (f \<in> Nset n \<rightarrow> carrier G \<and> l \<in> Nset n \<and> (\<forall>j\<in>(Nset n - {l}). f j = 0\<^sub>G)) \<longrightarrow> eSum G f n = f l"
apply (induct_tac n)
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (simp add:Nset_def)
apply (rule allI)
 apply (rule impI) apply (erule conjE)+
 apply (frule_tac f = f and n = n and A = "carrier G" in func_pre)
 apply (case_tac "l = Suc n")
 apply simp apply (thin_tac "l = Suc n")
 apply (thin_tac "\<forall>f. f \<in> Nset n \<rightarrow> carrier G \<and> Suc n \<in> Nset n \<and> (\<forall>j\<in>Nset n - {Suc n}. f j = 0\<^sub>G) \<longrightarrow>  e\<Sigma> G f n = f (Suc n)")
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> {0\<^sub>G}")
 apply (frule_tac  G = G and f = f and n = n in ring_eSum_zero, assumption+)
 apply (rule ballI)
 apply (frule_tac f = f and A = "Nset n" and B = "{0\<^sub>G}" in funcset_mem, assumption+) apply simp
 apply (frule_tac f = f and A = "Nset (Suc n)" and B = "carrier G" and x = "Suc n" in funcset_mem, assumption+)
 apply (simp add:ag_l_zero)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "Nset (Suc n) - {Suc n} = Nset n") apply simp
 apply (rule equalityI) apply (rule subsetI) apply (simp add:Nset_def)
 apply (rule subsetI) apply (simp add:Nset_def)
 apply (subgoal_tac "l \<in> Nset n") apply (subgoal_tac " \<forall>j\<in>Nset n - {l}. f j = 0\<^sub>G")
 apply simp
 apply (subgoal_tac "f (Suc n) = 0\<^sub>G")
 apply simp
 apply (frule_tac f = f and A = "Nset (Suc n)" and B = "carrier G" and x = l in funcset_mem, assumption+)
 apply (simp add:ag_r_zero) apply (simp add:Nset_def)
apply (rule ballI)
 apply (subgoal_tac "j \<in> Nset (Suc n) - {l}") prefer 2 apply simp
 apply (simp add:Nset_def)
 apply simp
apply (thin_tac "\<forall>f. f \<in> Nset n \<rightarrow> carrier G \<and> l \<in> Nset n \<and> (\<forall>j\<in>Nset n - {l}. f j = 0\<^sub>G) \<longrightarrow>  e\<Sigma> G f n = f l")
 apply (thin_tac "\<forall>j\<in>Nset (Suc n) - {l}. f j = 0\<^sub>G")
 apply (simp add:Nset_def)
done

lemma ag_eSum_1_nonzero:"\<lbrakk>agroup G; f \<in> Nset n \<rightarrow> carrier G; l \<in> Nset n; \<forall>j\<in>(Nset n - {l}). f j = 0\<^sub>G\<rbrakk> \<Longrightarrow> eSum G f n = f l"
apply (simp add:ag_eSum_1_nonzeroTr)
done

constdefs
 set_mult::"[('a, 'c) RingType_scheme, 'a set, 'a set] \<Rightarrow> 'a set"
 "set_mult R A B == {z. \<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = z}"

 sum_mult::"[('a, 'c) RingType_scheme, 'a set, 'a set] \<Rightarrow> 'a set"
  "sum_mult R A B == {x. \<exists>n. \<exists>f \<in> Nset n \<rightarrow> set_mult R A B. eSum R f n = x}"

 zero_fini::"[('a, 'c) RingType_scheme, 'a set, 'a set] \<Rightarrow> (nat \<Rightarrow> 'a)"
     "zero_fini R A B i == 0\<^sub>R \<cdot>\<^sub>R (0\<^sub>R)"

lemma sum_mult_Tr1:"\<lbrakk>ring R; A \<subseteq> carrier R; B \<subseteq> carrier R\<rbrakk> \<Longrightarrow>
               f \<in> Nset n \<rightarrow> set_mult R A B \<longrightarrow> eSum R f n \<in> carrier R"
apply (frule ring_is_ag)
apply (induct_tac n)
 apply (rule impI) apply (simp add:Nset_def)
 apply (subgoal_tac "(0::nat) \<in> {0}")
 apply (frule funcset_mem [of "f" "{0}" "set_mult R A B" "0"], assumption+)
 apply (simp add:set_mult_def)
 apply (thin_tac "f \<in> {0} \<rightarrow> {z. \<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = z}")
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f 0 \<longrightarrow> f 0 \<in> carrier R")
 apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f 0")
 apply (rule ballI)+ apply (rule impI)
 apply (frule sym) apply (thin_tac "x \<cdot>\<^sub>R y = f 0") apply simp
 apply (frule  subsetD [of "A" "carrier R"], assumption+)
 apply (frule  subsetD [of "B" "carrier R"], assumption+)
 apply (simp add:ring_tOp_closed) apply simp
apply (rule impI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") prefer 2 apply (simp add:Nset_def)
 apply (frule_tac A = "Nset (Suc n)" and x = "Suc n" in
             funcset_mem [of "f" _ "set_mult R A B"], assumption+)
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
 apply simp
 apply (rule ag_pOp_closed, assumption+)
 apply (thin_tac "eSum R f n \<in> carrier R")
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> set_mult R A B")
 apply (thin_tac "Suc n \<in> Nset (Suc n)")
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f (Suc n) \<longrightarrow>
                                      f (Suc n) \<in> carrier R")
 apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f (Suc n)")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "x \<cdot>\<^sub>R y = f (Suc n)") apply simp
 apply (frule subsetD [of "A" "carrier R"], assumption+)
 apply (frule subsetD [of "B" "carrier R"], assumption+)
 apply (simp add:ring_tOp_closed)
apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def)
done

lemma sum_mult_mem:"\<lbrakk>ring R; A \<subseteq> carrier R; B \<subseteq> carrier R;
   f \<in> Nset n \<rightarrow> set_mult R A B\<rbrakk>  \<Longrightarrow> eSum R f n \<in> carrier R"
apply (frule ring_is_ag)
apply (simp add:sum_mult_Tr1)
done

lemma times_mem_sum_mult:"\<lbrakk>ring R; A \<subseteq> carrier R; B \<subseteq> carrier R; a \<in> A; b \<in> B \<rbrakk>
                       \<Longrightarrow>  a \<cdot>\<^sub>R b \<in> sum_mult R A B"
apply (simp add:sum_mult_def)
apply (subgoal_tac "(\<lambda>i\<in>Nset 0. a \<cdot>\<^sub>R b) \<in> Nset 0 \<rightarrow> set_mult R A B")
apply (subgoal_tac "eSum R (\<lambda>i\<in>Nset 0. a \<cdot>\<^sub>R b) 0 = a \<cdot>\<^sub>R b")
apply blast
 apply (simp add:Nset_def)
 apply (simp add:Pi_def) apply (rule impI)
 apply (simp add:set_mult_def) apply blast
done

lemma minus_mem_sum_multTr1:"\<lbrakk>agroup R; a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
  -\<^sub>R (a +\<^sub>R b) = -\<^sub>R a +\<^sub>R (-\<^sub>R b)"
apply (simp add:ag_minus_apb)
done

lemma mem_minus_sum_multTr2:"\<lbrakk>ring R; A \<subseteq> carrier R; B \<subseteq> carrier R;
     f \<in> Nset n \<rightarrow> set_mult R A B; i \<in> Nset n\<rbrakk> \<Longrightarrow> f i \<in> carrier R"
apply (frule funcset_mem, assumption+)
apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
apply (simp add:set_mult_def)
apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f i \<longrightarrow> f i \<in> carrier R")
apply blast
apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f i")
apply (rule ballI)+
apply (rule impI) apply (frule sym) apply simp
apply (frule subsetD [of "A" "carrier R"], assumption+)
apply (frule subsetD [of "B" "carrier R"], assumption+)
apply (simp add:ring_tOp_closed)
done

lemma carrier_inc_set_mult:"\<lbrakk>ring R; A \<subseteq> carrier R; B \<subseteq> carrier R\<rbrakk> \<Longrightarrow>
                                    set_mult R A B \<subseteq> carrier R"
apply (frule ring_is_ag)
apply (rule subsetI)
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>xa\<in>A. \<forall>y\<in>B.  xa \<cdot>\<^sub>R y = x \<longrightarrow> x \<in> carrier R")
 apply blast apply (thin_tac "\<exists>xa\<in>A. \<exists>y\<in>B.  xa \<cdot>\<^sub>R y = x")
 apply (rule ballI)+ apply (rule impI)
 apply (frule subsetD [of "A"], assumption+)
 apply (frule subsetD [of "B"], assumption+)
 apply (frule sym) apply simp
 apply (simp add:ring_tOp_closed)
done

lemma eSum_jointfun:"\<lbrakk>agroup G; f \<in> Nset n \<rightarrow> carrier G; g \<in> Nset m \<rightarrow> carrier G\<rbrakk>  \<Longrightarrow> e\<Sigma> G (jointfun n f m g) (Suc (n + m)) =  e\<Sigma> G f n +\<^sub>G (e\<Sigma> G g m)"
 apply (subst eSum_split, assumption+)
 apply (frule_tac f = f and n = n and A = "carrier G" and g = g and m = m
 and B = "carrier G" in jointfun_hom, assumption+)
 apply simp
 apply (subgoal_tac "eSum G (jointfun n f m g) n = eSum G f n")
apply (subgoal_tac "eSum G (cmp (jointfun n f m g) (slide (Suc n))) m =
                               eSum G g m")
apply simp
 apply (thin_tac "eSum G (jointfun n f m g) n = eSum G f n")
 apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:cmp_def jointfun_def slide_def sliden_def)
 apply (simp add:funcset_mem) apply assumption
 apply (rule ballI) apply (simp add:cmp_def jointfun_def slide_def sliden_def)
 apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<le> n")
 apply (simp add:jointfun_def)  apply (simp add:funcset_mem)
 apply (simp add:Nset_def) apply assumption
 apply (rule ballI) apply (subgoal_tac "l \<le> n")
 apply (simp add:jointfun_def) apply (simp add:Nset_def)
done

lemma sum_mult_pOp_closed:"\<lbrakk>ring R; A \<subseteq> carrier R; B \<subseteq> carrier R;
  a \<in> sum_mult R A B;  b \<in> sum_mult R A B \<rbrakk> \<Longrightarrow> a +\<^sub>R b \<in> sum_mult R A B"
apply (frule ring_is_ag)
apply (simp add:sum_mult_def)
 apply auto
 apply (rename_tac n f m g)
 apply (frule_tac f = f and n = n and A = "set_mult R A B" and g = g and m = m
 and B = "set_mult R A B" in jointfun_hom, assumption+)
 apply simp
 apply (subgoal_tac "eSum R (jointfun n f m g) (Suc (n + m)) = eSum R f n +\<^sub>R (eSum R g m)")
 apply blast
 apply (thin_tac "jointfun n f m g \<in> Nset (Suc (n + m)) \<rightarrow> set_mult R A B")
 apply (subst eSum_split, assumption+)
 apply (frule_tac f = f and n = n and A = "set_mult R A B" and g = g and m = m
 and B = "set_mult R A B" in jointfun_hom, assumption+)
 apply simp
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
 apply (thin_tac "g \<in> Nset m \<rightarrow> set_mult R A B")
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (subgoal_tac "jointfun n f m g x \<in> set_mult R A B")
 apply (frule carrier_inc_set_mult[of "R" "A" "B"], assumption+)
 apply (simp add:subsetD) apply simp
apply (subgoal_tac "eSum R (jointfun n f m g) n = eSum R f n")
apply (subgoal_tac "eSum R (cmp (jointfun n f m g) (slide (Suc n))) m =
                               eSum R g m")
apply simp
 apply (thin_tac "eSum R (jointfun n f m g) n = eSum R f n")
 apply (rule eSum_eq, assumption+)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:cmp_def jointfun_def slide_def sliden_def)
 apply (frule carrier_inc_set_mult[of "R" "A" "B"], assumption+)
 apply (simp add:subsetD)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (frule carrier_inc_set_mult[of "R" "A" "B"], assumption+)
 apply (simp add:subsetD)
 apply (rule ballI)
 apply (simp add:jointfun_def cmp_def slide_def sliden_def)
apply (rule eSum_eq, assumption+)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:jointfun_def Nset_def)
 apply (frule carrier_inc_set_mult[of "R" "A" "B"], assumption+)
 apply (simp add:subsetD)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (frule carrier_inc_set_mult[of "R" "A" "B"], assumption+)
 apply (simp add:subsetD)
apply (rule ballI)
 apply (simp add:jointfun_def Nset_def)
done

lemma mem_minus_sum_multTr4:"\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B\<rbrakk> \<Longrightarrow>
    f \<in> Nset n \<rightarrow> set_mult R A B \<longrightarrow> -\<^sub>R (eSum R f n) \<in> sum_mult R A B "
apply (frule ring_is_ag)
apply (induct_tac n)
 apply (rule impI)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule funcset_mem, assumption+)
 apply (thin_tac "f \<in> Nset 0 \<rightarrow> set_mult R A B")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f 0 \<longrightarrow>
                                         (-\<^sub>R (f 0) \<in> sum_mult R A B)")
 apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f 0")
 apply (rule ballI)+ apply (rule impI) apply (frule sym) apply simp
 apply (subst ring_inv1_2, assumption+)
 apply (simp add:subsetD)
 apply (simp add:ideal_subset)
 apply (frule_tac x = y in ideal_inv1_closed [of "R" "B"], assumption+)
 apply (subgoal_tac "(\<lambda>i\<in>Nset 0. x \<cdot>\<^sub>R (-\<^sub>R y)) \<in> Nset 0 \<rightarrow> set_mult R A B")
 apply (subgoal_tac "eSum R (\<lambda>i\<in>Nset 0.   x \<cdot>\<^sub>R (-\<^sub>R y)) 0 =  x \<cdot>\<^sub>R (-\<^sub>R y)")
 apply (simp del:eSum_0 add:sum_mult_def)
 apply blast
 apply simp apply (simp add:Pi_def) apply (rule impI)
 apply (simp add:set_mult_def) apply blast apply (simp add:Nset_def)
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (frule_tac n = n in sum_mult_mem [of "R" "A" "B" "f"], assumption+)
 apply (rule subsetI) apply (simp add:ideal_subset) apply assumption
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
  apply (frule_tac n = "Suc n" and i = "Suc n" in
          mem_minus_sum_multTr2 [of "R" "A" "B"], assumption+)
  apply (rule subsetI) apply (rule ideal_subset, assumption+)
 apply (subst minus_mem_sum_multTr1, assumption+)
 apply (rule sum_mult_pOp_closed, assumption+)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
 apply (frule_tac f = f and A = "Nset (Suc n)" and B = "set_mult R A B"
   and x = "Suc n" in funcset_mem, assumption+)
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> set_mult R A B")
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f (Suc n) \<longrightarrow>
                             -\<^sub>R (f (Suc n)) \<in> sum_mult R A B")
 apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f (Suc n)")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "x \<cdot>\<^sub>R y = f (Suc n)") apply simp
 apply (subst ring_inv1_2, assumption+)
 apply (simp add:subsetD)
 apply (simp add:ideal_subset)
apply (rule times_mem_sum_mult, assumption+)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
 apply (simp add:ideal_inv1_closed)
 apply (simp add:Nset_def)
done

lemma sum_mult_iOp_closed:"\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B;
 a \<in> sum_mult R A B \<rbrakk> \<Longrightarrow> -\<^sub>R a \<in> sum_mult R A B"
apply (subgoal_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R A B. eSum R f n = a")
prefer 2 apply (simp add:sum_mult_def)
apply auto
apply (simp add:mem_minus_sum_multTr4)
done

lemma sum_mult_ring_multiplicationTr:
 "\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B; r \<in> carrier R\<rbrakk> \<Longrightarrow>
    f \<in> Nset n \<rightarrow> set_mult R A B \<longrightarrow> r \<cdot>\<^sub>R (eSum R f n) \<in> sum_mult R A B "
apply (frule ring_is_ag)
apply (induct_tac n)
 apply (rule impI) apply simp
 apply (subgoal_tac "0 \<in> Nset 0") apply (frule funcset_mem, assumption+)
 apply (thin_tac "f \<in> Nset 0 \<rightarrow> set_mult R A B")
 apply(simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B. x \<cdot>\<^sub>R y = f 0 \<longrightarrow> r \<cdot>\<^sub>R (f 0) \<in> sum_mult R A B") apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f 0")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "x \<cdot>\<^sub>R y = f 0") apply simp
 apply (frule subsetD [of "A"], assumption+)
 apply (frule ideal_subset [of _ "B"], assumption+)
 apply (frule_tac x = r and y = "x \<cdot>\<^sub>R y" in ring_tOp_commute [of "R"], assumption+)
 apply (simp add:ring_tOp_closed) apply simp
 apply (subst ring_tOp_assoc, assumption+)
 apply (thin_tac "r \<cdot>\<^sub>R ( x \<cdot>\<^sub>R y) =   x \<cdot>\<^sub>R y \<cdot>\<^sub>R r")
 apply (frule_tac x = y and y = r in ring_tOp_commute, assumption+)
 apply simp
 apply (frule_tac x = y and r = r in ideal_ring_multiple [of "R" "B"], assumption+)
 apply (rule times_mem_sum_mult, assumption+)
 apply (rule subsetI) apply (simp add:ideal_subset) apply assumption+
apply (simp add:Nset_def)
apply (rule impI)
 apply (frule_tac f = f and n = n and A = "set_mult R A B" in func_pre)
 apply simp
 apply (frule_tac R = R and f = f and n = n and i = n in eSum_mem)
 apply (frule carrier_inc_set_mult [of "R" "A" "B"], assumption+)
 apply (rule subsetI) apply (simp add:ideal_subset)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:subsetD) apply (simp add:Nset_def)
 apply (frule_tac A = "Nset (Suc n)" and B = "set_mult R A B" and x = "Suc n"
  in funcset_mem [of "f"]) apply (simp add:Nset_def)
 apply (frule carrier_inc_set_mult [of "R" "A" "B"], assumption+)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
 apply (frule_tac c = "f (Suc n)" in subsetD [of "set_mult R A B" "carrier R"],
                                       assumption+)
 apply (subst  ring_distrib1, assumption+)
 apply (rule sum_mult_pOp_closed, assumption+)
  apply (thin_tac "r \<cdot>\<^sub>R (eSum R f n) \<in> sum_mult R A B")
  apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> set_mult R A B")
  apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
  apply (thin_tac "set_mult R A B \<subseteq> carrier R")
  apply (thin_tac "f (Suc n) \<in> carrier R")
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f (Suc n) \<longrightarrow>
                             r \<cdot>\<^sub>R (f (Suc n)) \<in> sum_mult R A B")
 apply blast
 apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f (Suc n)")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "x \<cdot>\<^sub>R y = f (Suc n)") apply simp
 apply (frule subsetD [of "A"], assumption+)
 apply (frule ideal_subset [of _ "B"], assumption+)
 apply (frule_tac x = r and y = "x \<cdot>\<^sub>R y" in ring_tOp_commute [of "R"], assumption+) apply simp
 apply (subst ring_tOp_assoc, assumption+)
 apply (thin_tac "r \<cdot>\<^sub>R ( x \<cdot>\<^sub>R y) =   x \<cdot>\<^sub>R y \<cdot>\<^sub>R r")
 apply (frule_tac x = y and y = r in ring_tOp_commute, assumption+)
 apply simp
 apply (frule_tac x = y and r = r in ideal_ring_multiple [of "R" "B"], assumption+)
 apply (rule times_mem_sum_mult, assumption+)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
done

lemma sum_mult_ring_multiplication:"\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B;
 r \<in> carrier R; a \<in> sum_mult R A B\<rbrakk>  \<Longrightarrow> r \<cdot>\<^sub>R a \<in> sum_mult R A B"
apply (frule ring_is_ag)
apply (subgoal_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R A B. eSum R f n = a")
prefer 2 apply (simp add:sum_mult_def)
apply auto
apply (simp add:sum_mult_ring_multiplicationTr)
done

lemma ideal_sum_mult:"\<lbrakk>ring R; A \<subseteq> carrier R; A \<noteq> {}; ideal R B \<rbrakk> \<Longrightarrow>
    ideal R (sum_mult R A B)"
apply (simp add:ideal_def [of _ "sum_mult R A B"])
apply (frule ring_is_ag)
apply (rule conjI)
apply (rule asubg_test, assumption+)
apply (rule subsetI)
apply (simp add:sum_mult_def)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> set_mult R A B. eSum R f n = x
  \<longrightarrow> x \<in> carrier R") apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R A B. eSum R f n = x")
 apply (rule allI) apply (rule ballI) apply (rule impI)
 apply (frule sym) apply simp
 apply (subgoal_tac "B \<subseteq> carrier R")
 prefer 2 apply (rule subsetI) apply (rule ideal_subset, assumption+)
 apply (simp add:sum_mult_mem)
 apply (subgoal_tac "\<exists>a. a \<in> A") prefer 2 apply blast
 apply (subgoal_tac "\<forall>a. a \<in> A \<longrightarrow> sum_mult R A B \<noteq> {}")
 apply blast apply (thin_tac "\<exists>a. a \<in> A") apply (rule allI) apply (rule impI)
 apply (subgoal_tac "(\<lambda>i\<in>Nset 0. a \<cdot>\<^sub>R (0\<^sub>R)) \<in> Nset 0 \<rightarrow> set_mult R A B")
 apply (subgoal_tac "eSum R (\<lambda>i\<in>Nset 0. a \<cdot>\<^sub>R (0\<^sub>R)) 0 = a \<cdot>\<^sub>R (0\<^sub>R)")
 apply (simp add:sum_mult_def) apply blast
 apply (simp add:Nset_def)
 apply (simp add:Pi_def) apply (rule impI)
 apply (frule ideal_zero [of "R" "B"], assumption+)
 apply (simp add:set_mult_def)
 apply blast
apply (rule ballI)+
 apply (frule_tac a = b in sum_mult_iOp_closed [of "R" "A" "B"],
                                                                assumption+)
 apply (subgoal_tac "B \<subseteq> carrier R")
 apply (simp add:sum_mult_pOp_closed)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
apply (rule ballI)+
 apply (subgoal_tac "B \<subseteq> carrier R")
 apply (simp add:sum_mult_ring_multiplication)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
done

lemma ideal_inc_set_multTr:"\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B; ideal R C;
 set_mult R A B \<subseteq> C \<rbrakk> \<Longrightarrow> f \<in> Nset n \<rightarrow> set_mult R A B \<longrightarrow> eSum R f n \<in> C"
apply (induct_tac n)
 apply (rule impI) apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule funcset_mem, assumption+)
 apply (thin_tac "f \<in> Nset 0 \<rightarrow> set_mult R A B") apply (thin_tac "0 \<in> Nset 0")
 apply (simp add:set_mult_def) apply (fold set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A. \<forall>y\<in>B.  x \<cdot>\<^sub>R y = f 0 \<longrightarrow> f 0 \<in> C")
 apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>R y = f 0")
 apply (rule ballI)+ apply (rule impI) apply (frule sym) apply simp
 apply (subgoal_tac "x \<cdot>\<^sub>R y \<in> set_mult R A B") apply (simp add:subsetD)
 apply (simp add:set_mult_def) apply blast apply (simp add:Nset_def)
apply (rule impI)
 apply (frule_tac n = n in func_pre [of "f" _ "set_mult R A B"])
 apply simp
 apply (rule ideal_pOp_closed, assumption+)
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule funcset_mem, assumption+)
 apply (simp add:subsetD) apply (simp add:Nset_def)
done

lemma ideal_inc_set_mult:"\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B; ideal R C;
                           set_mult R A B \<subseteq> C \<rbrakk> \<Longrightarrow> sum_mult R A B \<subseteq> C"
apply (rule subsetI)
apply (subgoal_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R A B. eSum R f n = x")
prefer 2 apply (simp add:sum_mult_def)
apply auto
apply (simp add:ideal_inc_set_multTr)
done

lemma sum_mult_inc_set_mult:"\<lbrakk>ring R; A \<subseteq> carrier R; ideal R B\<rbrakk> \<Longrightarrow>
                           set_mult R A B \<subseteq>  sum_mult R A B"
apply (rule subsetI)
 apply (simp add:set_mult_def)
 apply auto
apply (rule times_mem_sum_mult, assumption+)
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
done

lemma AB_inc_sum_mult:"\<lbrakk>ring R; ideal R A; ideal R B\<rbrakk> \<Longrightarrow>
                                     sum_mult R A B \<subseteq> A \<inter> B"
apply (subgoal_tac "A \<subseteq> carrier R")
apply (subgoal_tac "B \<subseteq> carrier R")
apply (frule ideal_inc_set_mult [of "R" "A" "B" "A"], assumption+)
apply (rule subsetI)
prefer 2
apply (frule ideal_inc_set_mult [of "R" "A" "B" "B"], assumption+)
prefer 2 apply (rule subsetI) apply (simp add:subsetD)
apply (rule subsetI)
apply (simp add:set_mult_def)
apply auto
apply (frule ideal_subset [of _ "A"], assumption+)
apply (simp add:ideal_ring_multiple)
apply (simp add:set_mult_def)
apply auto
apply (frule ideal_subset [of _ "B"], assumption+)
apply (subst ring_tOp_commute, assumption+)
apply (simp add:ideal_subset) apply assumption
apply (simp add:ideal_ring_multiple)
apply (simp add:ideal_subset)+
done

lemma sum_mult_is_ideal_prod:"\<lbrakk>ring R; ideal R A; ideal R B\<rbrakk> \<Longrightarrow>
                                  sum_mult R A B =  A \<diamondsuit>\<^sub>R B"
apply (rule equalityI)
 apply (frule ideal_prod_ideal [of "R" "A" "B"], assumption+)
 apply (rule ideal_inc_set_mult, assumption+)
 apply (rule subsetI)
 apply (simp add:set_mult_def ideal_prod_def)
 apply (auto del:subsetI) apply (simp add:ideal_subset)
 apply (rule subsetI)
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>xa\<in>A. \<forall>y\<in>B.  xa \<cdot>\<^sub>R y = x \<longrightarrow> x \<in> A \<diamondsuit>\<^sub>R B")
 apply blast apply (thin_tac "\<exists>xa\<in>A. \<exists>y\<in>B.  xa \<cdot>\<^sub>R y = x")
 apply (rule ballI)+ apply (rule impI) apply (frule sym) apply simp
 apply (thin_tac "x =  xa \<cdot>\<^sub>R y")
apply (simp add:ideal_prod_def)
 apply (rule allI)
 apply (rename_tac xa y X) apply (rule impI) apply (erule conjE)
 apply blast
apply (subgoal_tac "A \<subseteq> carrier R")
apply (subgoal_tac "A \<noteq> {}")
apply (frule ideal_sum_mult [of "R" "A" "B"], assumption+)
 apply (simp add:ideal_prod_def)
 apply (subgoal_tac "sum_mult R A B \<in>
              {K. ideal R K \<and> {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> K}")
 apply (rule subsetI) apply (simp add:Int_def)
 apply (simp add:CollectI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>i\<in>A. \<forall>j\<in>B. x =  i \<cdot>\<^sub>R j \<longrightarrow> x \<in> sum_mult R A B")
 apply blast apply (thin_tac "\<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "i \<cdot>\<^sub>R j = x") apply simp
 apply (rule times_mem_sum_mult, assumption+)
 apply (rule subsetI) apply (rule ideal_subset[of _ "B"], assumption+)
 apply (frule ideal_zero [of _ "A"], assumption+) apply blast
 apply (rule subsetI) apply (rule ideal_subset, assumption+)
done

lemma ideal_quotient_idealTr:"\<lbrakk>ring R; ideal R A; ideal R B; ideal R C; x \<in> carrier R;\<forall>c\<in>C. x \<cdot>\<^sub>R c \<in> ideal_quotient R A B\<rbrakk> \<Longrightarrow> f\<in>Nset n \<rightarrow> set_mult R B C \<longrightarrow>
 x \<cdot>\<^sub>R (eSum R f n) \<in> A"
apply (frule ideal_subset1 [of "R" "A"], assumption+)
apply (frule ideal_subset1 [of "R" "B"], assumption+)
apply (induct_tac n)
 apply (rule impI) apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule funcset_mem, assumption+)
 apply (thin_tac "f \<in> Nset 0 \<rightarrow> set_mult R B C")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>u\<in>B. \<forall>v\<in>C.  u \<cdot>\<^sub>R v = f 0 \<longrightarrow> x \<cdot>\<^sub>R (f 0) \<in> A")
 apply blast apply (thin_tac "\<exists>x\<in>B. \<exists>y\<in>C.  x \<cdot>\<^sub>R y = f 0")
 apply (rule ballI)+ apply (rule impI) apply (frule sym) apply simp
 apply (thin_tac "f 0 = u \<cdot>\<^sub>R v")
 apply (frule ideal_subset [of _ "B"], assumption+)
 apply (frule ideal_subset [of _ "C"], assumption+)
 apply (frule_tac y = "u \<cdot>\<^sub>R v" in  ring_tOp_commute [of "R" "x"], assumption+)
 apply (rule ring_tOp_closed, assumption+) apply simp
 apply (thin_tac "x \<cdot>\<^sub>R ( u \<cdot>\<^sub>R v) =   u \<cdot>\<^sub>R v \<cdot>\<^sub>R x")
 apply (subst ring_tOp_assoc, assumption+)
 apply (frule_tac x = v in ring_tOp_commute [of "R" _ "x"], assumption+)
 apply simp
 apply (frule_tac x = u and y = "x \<cdot>\<^sub>R v" in ring_tOp_commute, assumption)
 apply (rule ring_tOp_closed, assumption+) apply simp
 apply (subgoal_tac "x \<cdot>\<^sub>R v \<in> ideal_quotient R A B")
 apply (thin_tac "\<forall>c\<in>C.  x \<cdot>\<^sub>R c \<in> ideal_quotient R A B")
 apply (simp add:ideal_quotient_def)
 apply simp apply (simp add:Nset_def)
(****** n ********)
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (frule ring_is_ag)
 apply (frule_tac  n = n and i = n in eSum_mem [of "R" "f"])
 apply (frule carrier_inc_set_mult [of "R" "B" "C"], assumption+)
 apply (simp add:Pi_def) apply (rule ideal_subset1, assumption+)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:subsetD) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule funcset_mem, assumption+)
 apply (frule carrier_inc_set_mult [of "R" "B" "C"], assumption+)
 apply (simp add:ideal_subset1)
 apply (frule_tac A = "set_mult R B C" and B = "carrier R" and c = "f (Suc n)"
             in subsetD, assumption+)
 apply (subst ring_distrib1, assumption+)
apply (rule ideal_pOp_closed, assumption+)
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> set_mult R B C")
 apply (thin_tac "x \<cdot>\<^sub>R (eSum R f n) \<in> A")
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R B C")
 apply (thin_tac "eSum R f n \<in> carrier R")
 apply (thin_tac "set_mult R B C \<subseteq> carrier R")
 apply (thin_tac "f (Suc n) \<in> carrier R")
apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>u\<in>B. \<forall>v\<in>C. u \<cdot>\<^sub>R v = f (Suc n) \<longrightarrow> x \<cdot>\<^sub>R (f (Suc n)) \<in> A")
 apply blast apply (thin_tac "\<exists>x\<in>B. \<exists>y\<in>C.  x \<cdot>\<^sub>R y = f (Suc n)")
 apply (rule ballI)+ apply (rule impI) apply (frule sym) apply simp
 apply (frule ideal_subset [of _ "B"], assumption+)
 apply (frule ideal_subset [of _ "C"], assumption+)
 apply (thin_tac "f (Suc n) = u \<cdot>\<^sub>R v")
 apply (frule_tac y = "u \<cdot>\<^sub>R v" in  ring_tOp_commute [of "R" "x"], assumption+)
 apply (rule ring_tOp_closed, assumption+) apply simp
 apply (thin_tac "x \<cdot>\<^sub>R ( u \<cdot>\<^sub>R v) =   u \<cdot>\<^sub>R v \<cdot>\<^sub>R x")
 apply (subst ring_tOp_assoc, assumption+)
 apply (frule_tac x = v in ring_tOp_commute [of "R" _ "x"], assumption+)
 apply simp
 apply (frule_tac x = u and y = "x \<cdot>\<^sub>R v" in ring_tOp_commute, assumption)
 apply (rule ring_tOp_closed, assumption+) apply simp
 apply (subgoal_tac "x \<cdot>\<^sub>R v \<in> ideal_quotient R A B")
 apply (thin_tac "\<forall>c\<in>C.  x \<cdot>\<^sub>R c \<in> ideal_quotient R A B")
 apply (simp add:ideal_quotient_def)
 apply simp apply (simp add:Nset_def)
done


lemma ideal_quotient_ideal:"\<lbrakk>ring R; ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
    ideal_quotient R (ideal_quotient R A B) C = ideal_quotient R A (B \<diamondsuit>\<^sub>R C)"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ideal_quotient_def [of _ _ "C"])
 apply (erule conjE)
 apply (simp add:ideal_quotient_def [of _ _ "B \<diamondsuit>\<^sub>R C"])
 apply (rule ballI)
apply (simp add:sum_mult_is_ideal_prod [THEN sym])
 apply (simp add:sum_mult_def)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> set_mult R B C. eSum R f n = b \<longrightarrow>
                                       x \<cdot>\<^sub>R b \<in> A")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R B C. eSum R f n = b")
 apply (rule allI) apply (rule ballI) apply (rule impI)
 apply (rename_tac x c n f)
 apply (frule sym) apply simp
apply (simp add:ideal_quotient_idealTr)
apply (rule subsetI)
 apply (simp add:sum_mult_is_ideal_prod [THEN sym])
 apply (simp add:ideal_quotient_def)
 apply (erule conjE)
 apply (rule ballI)
 apply (rename_tac x c)
 apply (frule ideal_subset [of _ "C"], assumption+)
 apply (simp add:ring_tOp_closed)
apply (rule ballI)
apply (rename_tac x v u)
 apply (frule ideal_subset [of _ "B"], assumption+)
 apply (subst ring_tOp_assoc, assumption+)
 apply (frule_tac x = v and y = u in ring_tOp_commute, assumption+)
 apply simp apply (thin_tac "v \<cdot>\<^sub>R u =  u \<cdot>\<^sub>R v")
 apply (subgoal_tac "u \<cdot>\<^sub>R v \<in> sum_mult R B C") apply simp
 apply (frule ideal_subset1 [of "R" "B"], assumption+)
 apply (frule ideal_subset1 [of "R" "C"], assumption+)
 apply (simp add:times_mem_sum_mult)
done

lemma ideal_prod_assocTr:"\<lbrakk>ring R; ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
  \<forall>f. f \<in> Nset n \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C \<longrightarrow>  (e\<Sigma> R f n) \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)"
apply (subgoal_tac "\<forall>x\<in>(A \<diamondsuit>\<^sub>R B). \<forall>y\<in>C. x \<cdot>\<^sub>R y \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)")
apply (induct_tac n)
  apply (rule allI) apply (rule impI)
  apply (frule_tac f = f and A = "Nset 0" and B = "set_mult R (A \<diamondsuit>\<^sub>R B) C" and
   x = 0 in funcset_mem) apply (simp add:Nset_def)
  apply (thin_tac "f \<in> Nset 0 \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C")
  apply (simp add:set_mult_def)
  apply (subgoal_tac "\<forall>x\<in>A \<diamondsuit>\<^sub>R B. \<forall>y\<in>C. RingType.tOp R x y = f 0 \<longrightarrow>
                                              f 0 \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)")
  apply blast apply (thin_tac "\<exists>x\<in>A \<diamondsuit>\<^sub>R B. \<exists>y\<in>C. RingType.tOp R x y = f 0")
  apply (rule ballI)+ apply (rule impI) apply (frule sym)
  apply (thin_tac "RingType.tOp R x y = f 0")
  apply simp
apply (rule allI) apply (rule impI)
 apply (frule_tac f = f and n = n and A = "set_mult R (A \<diamondsuit>\<^sub>R B) C" in func_pre)
 apply (subgoal_tac "e\<Sigma> R f n \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)") prefer 2 apply simp
 apply (thin_tac "\<forall>f. f \<in> Nset n \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C \<longrightarrow>
                 e\<Sigma> R f n \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)")
 apply simp
  apply (frule ideal_prod_ideal[of "R" "B" "C"], assumption+)
  apply (frule ideal_prod_ideal[of "R" "A" "B \<diamondsuit>\<^sub>R C"], assumption+)
  apply (rule ideal_pOp_closed[of "R" "A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)"], assumption+)
 apply (frule_tac f = f and A = "Nset (Suc n)" and B = "set_mult R (A \<diamondsuit>\<^sub>R B) C" and x = "Suc n" in funcset_mem) apply (simp add:Nset_def)
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C")
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>A \<diamondsuit>\<^sub>R B. \<forall>y\<in>C. RingType.tOp R x y = f (Suc n) \<longrightarrow>
            f (Suc n) \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)") apply blast
  apply (thin_tac "\<exists>x\<in>A \<diamondsuit>\<^sub>R B. \<exists>y\<in>C. RingType.tOp R x y = f (Suc n)")
  apply (rule ballI)+ apply (rule impI) apply (frule sym)
  apply (thin_tac "RingType.tOp R x y = f (Suc n)") apply simp
apply (rule ballI)+
  apply (frule ideal_prod_ideal[of "R" "B" "C"], assumption+)
  apply (frule ideal_prod_ideal[of "R" "A" "B \<diamondsuit>\<^sub>R C"], assumption+)
 apply (subst sum_mult_is_ideal_prod[THEN sym, of "R" "A" "B \<diamondsuit>\<^sub>R C"], assumption+)
 apply (simp add: sum_mult_is_ideal_prod[THEN sym, of "R" "A" "B"])
 apply (thin_tac "ideal R (A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C))")
 apply (simp add:sum_mult_def[of "R" "A" "B"])
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> set_mult R A B. e\<Sigma> R f n = x \<longrightarrow>
           RingType.tOp R x y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)")
 apply blast apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R A B. e\<Sigma> R f n = x")
 apply (rule allI) apply (rule ballI) apply (rule impI)
 apply (frule sym) apply (thin_tac "e\<Sigma> R f n = x") apply simp
 apply (thin_tac "x = e\<Sigma> R f n")
apply (subgoal_tac "\<forall>g. g\<in>Nset n \<rightarrow> set_mult R A B \<longrightarrow> RingType.tOp R (e\<Sigma> R g n) y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)") apply blast
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R A B")
 apply (induct_tac n)
  apply (rule allI)  apply (rule impI)
 apply (frule_tac f = g and A = "Nset 0" and B = "set_mult R A B" and x = "0" in funcset_mem) apply (simp add:Nset_def)
 apply (thin_tac "g \<in> Nset 0 \<rightarrow> set_mult R A B")
 apply (simp add:set_mult_def[of "R" "A" "B"])
 apply (subgoal_tac "\<forall>x1\<in>A. \<forall>y1\<in>B. RingType.tOp R x1 y1 = g 0 \<longrightarrow> RingType.tOp R (g 0) y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)") apply blast
  apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B. RingType.tOp R x y = g 0")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "RingType.tOp R x1 y1 = g 0") apply simp
 apply (frule_tac h = x1 in ideal_subset[of "R" "A"], assumption+)
 apply (frule_tac h = y1 in ideal_subset[of "R" "B"], assumption+)
 apply (frule_tac h = y in ideal_subset[of "R" "C"], assumption+)
 apply (simp add:ring_tOp_assoc)
 apply (subgoal_tac "x1 \<cdot>\<^sub>R (y1 \<cdot>\<^sub>R y) \<in> set_mult R A (B \<diamondsuit>\<^sub>R C)")
 apply (frule ideal_subset1[of "R" "A"], assumption+)
 apply (frule sum_mult_inc_set_mult[of "R" "A" "(B \<diamondsuit>\<^sub>R C)"], assumption+)
 apply (rule subsetD, assumption+)
 apply (subgoal_tac "(RingType.tOp R y1 y) \<in> (B \<diamondsuit>\<^sub>R C)")
 apply (simp add:set_mult_def) apply blast
 apply (subgoal_tac " RingType.tOp R y1 y \<in> set_mult R B C")
 apply (frule sum_mult_inc_set_mult[of "R" "B" "C"])
  apply (simp add:ideal_subset1) apply assumption+
  apply (subgoal_tac "RingType.tOp R y1 y \<in> set_mult R B C")
   apply (subst sum_mult_is_ideal_prod[THEN sym, of "R" "B" "C"], assumption+)
   apply (simp add:subsetD)
  apply assumption apply (simp add:set_mult_def) apply blast
apply (rule allI) apply (rule impI)
  apply (frule_tac f = g and n = na and A = "set_mult R A B" in func_pre)
  apply (subgoal_tac "RingType.tOp R (e\<Sigma> R g na) y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)")
  prefer 2 apply simp
  apply (thin_tac "\<forall>g. g \<in> Nset na \<rightarrow> set_mult R A B \<longrightarrow>
              RingType.tOp R (e\<Sigma> R g na) y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)")
 apply simp
apply (frule ideal_subset1[of "R" "A"], assumption+)
 apply (frule ideal_subset1[of "R" "B"], assumption+)
 apply (frule carrier_inc_set_mult [of "R" "A" "B"], assumption+)
 apply (subgoal_tac "g \<in> Nset (Suc na) \<rightarrow> carrier R")
 apply (frule_tac f = g and n = na and A = "carrier R" in func_pre)
 apply (frule ring_is_ag[of "R"])
 apply (frule_tac f = g and n = na and i = na in eSum_mem[of "R"], assumption+) apply (simp add:Nset_def)
apply (frule_tac f = g and A = "Nset (Suc na)" and B = "carrier R" and x = "Suc na" in funcset_mem) apply (simp add:Nset_def)
 apply (frule_tac h = y in ideal_subset[of "R" "C"], assumption+)
 apply (simp add:ring_distrib2)
 apply (rule sum_mult_pOp_closed, assumption+)
 apply (simp add:ideal_subset1)
 apply simp
 apply (frule_tac f = g and A = "Nset (Suc na)" and B = "set_mult R A B" and x = "Suc na" in funcset_mem) apply (simp add:Nset_def)
 apply (thin_tac "g \<in> Nset na \<rightarrow> set_mult R A B")
 apply (thin_tac "set_mult R A B \<subseteq> carrier R")
 apply (thin_tac "g (Suc na) \<in> carrier R")
 apply (thin_tac "RingType.tOp R (e\<Sigma> R g na) y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)")
 apply (thin_tac "e\<Sigma> R g na \<in> carrier R")
 apply (thin_tac "g \<in> Nset (Suc na) \<rightarrow> set_mult R A B")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x1\<in>A. \<forall>y1\<in>B. RingType.tOp R x1 y1 = g (Suc na) \<longrightarrow>
                      RingType.tOp R (g (Suc na)) y \<in> sum_mult R A (B \<diamondsuit>\<^sub>R C)")  apply blast apply (thin_tac "\<exists>x\<in>A. \<exists>y\<in>B. RingType.tOp R x y = g (Suc na)")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "RingType.tOp R x1 y1 = g (Suc na)") apply simp
 apply (frule_tac h = x1 in ideal_subset[of "R" "A"], assumption+)
 apply (frule_tac h = y1 in ideal_subset[of "R" "B"], assumption+)
 apply (frule_tac h = y in ideal_subset[of "R" "C"], assumption+)
 apply (simp add:ring_tOp_assoc)
 apply (frule sum_mult_inc_set_mult[of "R" "A" "B \<diamondsuit>\<^sub>R C"], assumption+)
 apply (rule subsetD, assumption+)
 apply (thin_tac "set_mult R A (B \<diamondsuit>\<^sub>R C) \<subseteq> sum_mult R A (B \<diamondsuit>\<^sub>R C)")
 apply (subgoal_tac "RingType.tOp R y1 y \<in> (B \<diamondsuit>\<^sub>R C)")
 apply (simp add:set_mult_def) apply blast
 apply (subst sum_mult_is_ideal_prod[THEN sym, of "R" "B" "C"], assumption+)
 apply (frule sum_mult_inc_set_mult[of "R" "B" "C"], assumption+)
 apply (subgoal_tac " RingType.tOp R y1 y \<in> set_mult R B C ")
 apply (rule subsetD, assumption+) apply (simp add:set_mult_def)
 apply blast
apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:funcset_mem subsetD)
done

lemma ideal_prod_assoc:"\<lbrakk>ring R; ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
            A \<diamondsuit>\<^sub>R B \<diamondsuit>\<^sub>R C = A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)"
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule ideal_prod_ideal[of "R" "A" "B"], assumption+)
 apply (frule sum_mult_is_ideal_prod[of "R" "A \<diamondsuit>\<^sub>R B" "C"], assumption+)
 apply (frule sym) apply (thin_tac "sum_mult R (A \<diamondsuit>\<^sub>R B) C = A \<diamondsuit>\<^sub>R B \<diamondsuit>\<^sub>R C")
 apply simp apply (thin_tac "A \<diamondsuit>\<^sub>R B \<diamondsuit>\<^sub>R C = sum_mult R (A \<diamondsuit>\<^sub>R B) C")
 apply (thin_tac "ideal R (A \<diamondsuit>\<^sub>R B)")
 apply (frule ideal_prod_ideal[of "R" "B" "C"], assumption+)
  apply (simp add:sum_mult_def)
  apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C. e\<Sigma> R f n = x
  \<longrightarrow> x \<in> A \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R C)")
  apply blast apply (thin_tac " \<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>R B) C. e\<Sigma> R f n = x")
 apply (rule allI) apply (rule ballI) apply (rule impI)
 apply (frule sym) apply (thin_tac "e\<Sigma> R f n = x") apply simp
 apply (simp add:ideal_prod_assocTr)
apply (rule subsetI)
 apply (frule ideal_prod_ideal[of "R" "B" "C"], assumption+)
 apply (simp add:prod_commute [of "R" "A" "B \<diamondsuit>\<^sub>R C"])
 apply (frule ideal_prod_ideal[of "R" "A" "B"], assumption+)
 apply (simp add:prod_commute[of "R" "A \<diamondsuit>\<^sub>R B" "C"])
 apply (simp add:prod_commute[of "R" "A" "B"])
 apply (simp add:prod_commute[of "R" "B" "C"])
 apply (frule ideal_prod_ideal[of "R" "C" "B"], assumption+)
 apply (frule sum_mult_is_ideal_prod[of "R" "C \<diamondsuit>\<^sub>R B" "A"], assumption+)
 apply (frule sym) apply (thin_tac "sum_mult R (C \<diamondsuit>\<^sub>R B) A = C \<diamondsuit>\<^sub>R B \<diamondsuit>\<^sub>R A")
 apply simp apply (thin_tac "C \<diamondsuit>\<^sub>R B \<diamondsuit>\<^sub>R A = sum_mult R (C \<diamondsuit>\<^sub>R B) A")
 apply (thin_tac "ideal R (C \<diamondsuit>\<^sub>R B)")
 apply (frule ideal_prod_ideal[of "R" "B" "A"], assumption+)
  apply (simp add:sum_mult_def)
  apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> set_mult R (C \<diamondsuit>\<^sub>R B) A. e\<Sigma> R f n = x
  \<longrightarrow> x \<in> C \<diamondsuit>\<^sub>R (B \<diamondsuit>\<^sub>R A)")
  apply blast apply (thin_tac " \<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R (C \<diamondsuit>\<^sub>R B) A. e\<Sigma> R f n = x")
 apply (rule allI) apply (rule ballI) apply (rule impI)
 apply (frule sym) apply (thin_tac "e\<Sigma> R f n = x") apply simp
 apply (simp add:ideal_prod_assocTr)
done

lemma prod_principal_ideal:"\<lbrakk>ring R; a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
 (Rxa R a) \<diamondsuit>\<^sub>R (Rxa R b) = Rxa R (a \<cdot>\<^sub>R b)"
apply (frule principal_ideal[of "R" "a"], assumption+)
apply (frule principal_ideal[of "R" "b"], assumption+)
apply (subst sum_mult_is_ideal_prod[THEN sym, of "R" "Rxa R a" "Rxa R b"], assumption+)
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:sum_mult_def)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b). e\<Sigma> R f n = x \<longrightarrow> x \<in> R \<diamondsuit> RingType.tOp R a b") apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b). e\<Sigma> R f n = x")
 apply (rule allI) apply (rule ballI) apply (rule impI)
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "e\<Sigma> R f n = x")
 apply simp apply (thin_tac "x = e\<Sigma> R f n")
 apply (subgoal_tac "\<forall>f. f \<in> Nset n \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b) \<longrightarrow> e\<Sigma> R f n \<in> R \<diamondsuit> RingType.tOp R a b") apply blast
 apply (thin_tac "f \<in> Nset n \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)")
 apply (induct_tac n)
 apply (rule allI) apply (rule impI)
 apply (frule_tac f = fa and A = "Nset 0" and B = "set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b) " and x = 0 in funcset_mem) apply (simp add:Nset_def)
 apply (thin_tac "fa \<in> Nset 0 \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>R \<diamondsuit> a. \<forall>y\<in>R \<diamondsuit> b. RingType.tOp R x y = fa 0 \<longrightarrow>
                          fa 0 \<in> R \<diamondsuit> RingType.tOp R a b")
 apply blast apply (thin_tac "\<exists>x\<in>R \<diamondsuit> a. \<exists>y\<in>R \<diamondsuit> b. RingType.tOp R x y = fa 0")
 apply (rule ballI)+ apply (rule impI) apply (rotate_tac -1)
 apply (frule sym) apply (thin_tac "RingType.tOp R x y = fa 0")
 apply simp apply (thin_tac "fa 0 = RingType.tOp R x y")
 apply (thin_tac "ideal R (R \<diamondsuit> a)") apply (thin_tac "ideal R (R \<diamondsuit> b)")
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r1\<in>carrier R. \<forall>r2 \<in> carrier R. x = r1 \<cdot>\<^sub>R a \<and> y = r2 \<cdot>\<^sub>R b  \<longrightarrow> (\<exists>r\<in>carrier R.
                RingType.tOp R x y = RingType.tOp R r (RingType.tOp R a b))")
 apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. x = RingType.tOp R r a")
 apply (thin_tac "\<exists>r\<in>carrier R. y = RingType.tOp R r b")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (frule_tac x = r2 and y = b in ring_tOp_closed, assumption+)
 apply (frule_tac x = r1 and y = a and z = "r2 \<cdot>\<^sub>R b" in ring_tOp_assoc,
                                     assumption+)
 apply simp
 apply (thin_tac "RingType.tOp R (RingType.tOp R r1 a) (RingType.tOp R r2 b) =
          RingType.tOp R r1 (RingType.tOp R a (RingType.tOp R r2 b))")
 apply (frule_tac x1 = a and y1 = r2 and z1 = b in ring_tOp_assoc[THEN sym],
            assumption+) apply simp
 apply (thin_tac " RingType.tOp R a (RingType.tOp R r2 b) =
          RingType.tOp R (RingType.tOp R a r2) b")
 apply (frule_tac x = a and y = r2 in ring_tOp_commute, assumption+)
 apply simp apply (thin_tac "RingType.tOp R a r2 = RingType.tOp R r2 a")
 apply (frule_tac x = r2 and y = a and z = b in ring_tOp_assoc, assumption+)
 apply simp
 apply (thin_tac "RingType.tOp R (RingType.tOp R r2 a) b =
          RingType.tOp R r2 (RingType.tOp R a b)")
 apply (frule ring_tOp_closed[of "R" "a" "b"], assumption+)
 apply (frule_tac x1 = r1 and y1 = r2 and z1 = "a \<cdot>\<^sub>R b" in ring_tOp_assoc[THEN sym], assumption+) apply simp
 apply (thin_tac " RingType.tOp R r1 (RingType.tOp R r2 (RingType.tOp R a b)) =
          RingType.tOp R (RingType.tOp R r1 r2) (RingType.tOp R a b)")
 apply (frule_tac x = r1 and y = r2 in ring_tOp_closed[of "R"], assumption+)
 apply blast
 apply (rule allI) apply (rule impI)
apply (frule_tac f = fa and n = na and A = "set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)" in func_pre)
 apply (subgoal_tac "e\<Sigma> R fa na \<in> R \<diamondsuit> RingType.tOp R a b")
 prefer 2 apply simp
 apply (thin_tac "\<forall>f. f \<in> Nset na \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b) \<longrightarrow>
              e\<Sigma> R f na \<in> R \<diamondsuit> RingType.tOp R a b")
 apply simp
 apply (frule ring_tOp_closed[of "R" "a" "b"], assumption+)
 apply (frule principal_ideal[of "R" "a \<cdot>\<^sub>R b"], assumption+)
 apply (rule ideal_pOp_closed, assumption+)
 apply (frule_tac f = fa and A = "Nset (Suc na)" and B = "set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b) " and x = "Suc na" in funcset_mem) apply (simp add:Nset_def)
 apply (thin_tac "ideal R (R \<diamondsuit> a)")
 apply (thin_tac "ideal R (R \<diamondsuit> b)")
 apply (thin_tac "fa \<in> Nset (Suc na) \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)")
 apply (thin_tac "fa \<in> Nset na \<rightarrow> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)")
 apply (thin_tac "e\<Sigma> R fa na \<in> R \<diamondsuit> RingType.tOp R a b")
 apply (thin_tac "ideal R (R \<diamondsuit> RingType.tOp R a b)")
 apply (simp add:set_mult_def)
 apply (subgoal_tac "\<forall>x\<in>R \<diamondsuit> a. \<forall>y\<in>R \<diamondsuit> b. RingType.tOp R x y = fa (Suc na)
    \<longrightarrow> fa (Suc na) \<in> R \<diamondsuit> RingType.tOp R a b") apply blast
 apply (thin_tac "\<exists>x\<in>R \<diamondsuit> a. \<exists>y\<in>R \<diamondsuit> b. RingType.tOp R x y = fa (Suc na)")
 apply (rule ballI)+ apply (rule impI) apply (frule sym)
 apply (thin_tac "RingType.tOp R x y = fa (Suc na)") apply simp
 apply (thin_tac "fa (Suc na) = RingType.tOp R x y")
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r1\<in>carrier R. \<forall>r2 \<in> carrier R. x = r1 \<cdot>\<^sub>R a \<and> y = r2 \<cdot>\<^sub>R b  \<longrightarrow> (\<exists>r\<in>carrier R.
                RingType.tOp R x y = RingType.tOp R r (RingType.tOp R a b))")
 apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. x = RingType.tOp R r a")
 apply (thin_tac "\<exists>r\<in>carrier R. y = RingType.tOp R r b")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (frule_tac x = r2 and y = b in ring_tOp_closed, assumption+)
 apply (frule_tac x = r1 and y = a and z = "r2 \<cdot>\<^sub>R b" in ring_tOp_assoc,
                                     assumption+)
 apply simp
 apply (thin_tac "RingType.tOp R (RingType.tOp R r1 a) (RingType.tOp R r2 b) =
          RingType.tOp R r1 (RingType.tOp R a (RingType.tOp R r2 b))")
 apply (frule_tac x1 = a and y1 = r2 and z1 = b in ring_tOp_assoc[THEN sym],
            assumption+) apply simp
 apply (thin_tac " RingType.tOp R a (RingType.tOp R r2 b) =
          RingType.tOp R (RingType.tOp R a r2) b")
 apply (frule_tac x = a and y = r2 in ring_tOp_commute, assumption+)
 apply simp apply (thin_tac "RingType.tOp R a r2 = RingType.tOp R r2 a")
 apply (frule_tac x = r2 and y = a and z = b in ring_tOp_assoc, assumption+)
 apply simp
 apply (thin_tac "RingType.tOp R (RingType.tOp R r2 a) b =
          RingType.tOp R r2 (RingType.tOp R a b)")
 apply (frule ring_tOp_closed[of "R" "a" "b"], assumption+)
 apply (frule_tac x1 = r1 and y1 = r2 and z1 = "a \<cdot>\<^sub>R b" in ring_tOp_assoc[THEN sym], assumption+) apply simp
 apply (thin_tac " RingType.tOp R r1 (RingType.tOp R r2 (RingType.tOp R a b)) =
          RingType.tOp R (RingType.tOp R r1 r2) (RingType.tOp R a b)")
 apply (frule_tac x = r1 and y = r2 in ring_tOp_closed[of "R"], assumption+)
 apply blast
 apply (rule subsetI)
 apply (simp add:Rxa_def [of "R" "a \<cdot>\<^sub>R b"])
 apply (subgoal_tac "\<forall>r\<in>carrier R. x = RingType.tOp R r (RingType.tOp R a b)
        \<longrightarrow> x \<in> sum_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)") apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. x = RingType.tOp R r (RingType.tOp R a b)")
 apply (rule ballI) apply (rule impI)
 apply (frule ideal_subset1[of "R" "R \<diamondsuit> a"], assumption+)
 apply (frule sum_mult_inc_set_mult[of "R" "R \<diamondsuit> a" "R \<diamondsuit> b"], assumption+)
 apply (subgoal_tac "x \<in> set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)")
 apply (rule subsetD, assumption+)
 apply (thin_tac "set_mult R (R \<diamondsuit> a) (R \<diamondsuit> b) \<subseteq> sum_mult R (R \<diamondsuit> a) (R \<diamondsuit> b)")
 apply simp apply (thin_tac "x = RingType.tOp R r (RingType.tOp R a b)")
 apply (simp add:set_mult_def) apply (simp add:ring_tOp_assoc[THEN sym])
 apply (subgoal_tac "RingType.tOp R r a \<in> R \<diamondsuit> a")
 apply (subgoal_tac "b \<in> R \<diamondsuit> b") apply blast
 apply (simp add:a_in_principal)
 apply (simp add:Rxa_def) apply blast
done

lemma principal_ideal_n_pow: "\<lbrakk>ring R; a \<in> carrier R; I = Rxa R a\<rbrakk> \<Longrightarrow>
                                  I \<^sup>\<diamondsuit>\<^sup>R \<^sup>n  = Rxa R (a^\<^sup>R\<^sup> \<^sup>n)"
apply (induct_tac n)
 apply simp
 apply (frule a_in_principal[of "R" "1\<^sub>R"])
 apply (simp add:ring_one)
 apply (rule ideal_inc_one[THEN sym, of "R" "R \<diamondsuit> RingType.one R"], assumption+)
 apply (rule principal_ideal[of "R" "1\<^sub>R"], assumption+)
 apply (simp add:ring_one) apply assumption
apply simp apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "R \<diamondsuit> a \<^sup>\<diamondsuit>\<^sup>R \<^sup>n = R \<diamondsuit> (a^\<^sup>R\<^sup> \<^sup>n)")
 apply (frule_tac b = "a^\<^sup>R\<^sup> \<^sup>n" in prod_principal_ideal[of "R" "a"], assumption+)
 apply (simp add:npClose) apply simp
done

lemma integral_domain_ring:"integral_domain R \<Longrightarrow> ring R"
apply (simp add:integral_domain_def)
done

lemma a_notin_n_pow1: "\<lbrakk>integral_domain R; a \<in> carrier R; \<not> unit R a; a \<noteq> 0\<^sub>R;
 0 < n\<rbrakk> \<Longrightarrow> a \<notin> (Rxa R a) \<^sup>\<diamondsuit>\<^sup>R \<^sup>(Suc n)"
apply (rule contrapos_pp)
 apply (simp del:ipSuc) apply (simp del:ipSuc)
 apply (frule integral_domain_ring[of "R"])
 apply (frule principal_ideal[of "R" "a"], assumption+)
 apply (frule principal_ideal_n_pow[of "R" "a" "R \<diamondsuit> a" "Suc n"], assumption+)
 apply simp apply (simp del:ipSuc)
 apply (thin_tac "R \<diamondsuit> a \<^sup>\<diamondsuit>\<^sup>R \<^sup>Suc n = R \<diamondsuit> RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n)")
 apply (thin_tac "ideal R (R \<diamondsuit> a)")
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. a = RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n)) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. a = RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (rule ballI) apply (rule impI)
apply (frule npClose[of "R" "a" "n"], assumption+)
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (simp add:ring_tOp_commute[of "R" _ "a"])
 apply (simp add:ring_tOp_assoc)
 apply (frule ring_r_one[THEN sym, of "R" "a"], assumption+)
 apply (subgoal_tac "a \<cdot>\<^sub>R (1\<^sub>R) = a \<cdot>\<^sub>R (r \<cdot>\<^sub>R (a^\<^sup>R\<^sup> \<^sup>n))") prefer 2 apply simp
 apply (thin_tac "a = RingType.tOp R a (RingType.tOp R r (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (frule_tac b = "r \<cdot>\<^sub>R (a^\<^sup>R\<^sup> \<^sup>n)" in idom_mult_cancel_l[of "R" "1\<^sub>R" _ "a"])
 apply (simp add:ring_one) apply (simp add:ring_tOp_closed)
 apply assumption+
 apply (thin_tac "RingType.tOp R a (RingType.one R) =
         RingType.tOp R a (RingType.tOp R r (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (thin_tac "a = RingType.tOp R a (RingType.one R)")
 apply (subgoal_tac "1\<^sub>R = r \<cdot>\<^sub>R (a^\<^sup>R\<^sup> \<^sup>(Suc (n - Suc 0)))") prefer 2
 apply (simp del:ipSuc)
 apply (thin_tac "RingType.one R = RingType.tOp R r (a^\<^sup>R\<^sup> \<^sup>n)")
 apply (simp del:Suc_pred)
 apply (frule npClose[of "R" "a" "n - Suc 0"], assumption+)
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (simp add:ring_tOp_commute[of "R" _ "a"])
 apply (simp add:ring_tOp_assoc)
 apply (frule_tac x = r in ring_tOp_closed[of "R" _ "a^\<^sup>R\<^sup> \<^sup>(n - Suc 0)"],
                                                 assumption+)
 apply (simp add:unit_def)
 apply blast
done

lemma a_notin_n_pow2: "\<lbrakk>integral_domain R; a \<in> carrier R; \<not> unit R a; a \<noteq> 0\<^sub>R;
 0 < n\<rbrakk> \<Longrightarrow> a^\<^sup>R\<^sup> \<^sup>n \<notin> (Rxa R a) \<^sup>\<diamondsuit>\<^sup>R \<^sup>(Suc n)"
apply (rule contrapos_pp)
 apply (simp del:ipSuc) apply (simp del:ipSuc)
 apply (frule integral_domain_ring[of "R"])
 apply (frule principal_ideal[of "R" "a"], assumption+)
 apply (frule principal_ideal_n_pow[of "R" "a" "R \<diamondsuit> a" "Suc n"], assumption+)
 apply simp apply (simp del:ipSuc)
 apply (thin_tac "R \<diamondsuit> a \<^sup>\<diamondsuit>\<^sup>R \<^sup>Suc n = R \<diamondsuit> RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n)")
 apply (thin_tac "ideal R (R \<diamondsuit> a)")
apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. a^\<^sup>R\<^sup> \<^sup>n = RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n)) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. a^\<^sup>R\<^sup> \<^sup>n = RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (rule ballI) apply (rule impI)
 apply (frule idom_potent_nonzero[of "R" "a" "n"], assumption+)
 apply (frule npClose[of "R" "a" "n"], assumption+)
 apply (frule ring_l_one[THEN sym, of "R" "a^\<^sup>R\<^sup> \<^sup>n "], assumption+)
 apply (subgoal_tac "RingType.tOp R (RingType.one R) (a^\<^sup>R\<^sup> \<^sup>n) =
                          RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))")
 prefer 2 apply simp
 apply (thin_tac "a^\<^sup>R\<^sup> \<^sup>n = RingType.tOp R (RingType.one R) (a^\<^sup>R\<^sup> \<^sup>n)")
 apply (thin_tac "a^\<^sup>R\<^sup> \<^sup>n = RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (frule_tac b = "r \<cdot>\<^sub>R a" in idom_mult_cancel_r[of "R" "1\<^sub>R" _ "a^\<^sup>R\<^sup> \<^sup>n"])
 apply (simp add:ring_one) apply (simp add:ring_tOp_closed)
 apply assumption+
 apply (thin_tac "RingType.tOp R (RingType.one R) (a^\<^sup>R\<^sup> \<^sup>n) =
         RingType.tOp R (RingType.tOp R r a) (a^\<^sup>R\<^sup> \<^sup>n)")
 apply (frule sym) apply (thin_tac "RingType.one R = RingType.tOp R r a")
 apply (frule_tac x = r in ring_tOp_commute[of "R" _ "a"], assumption+)
 apply simp apply (thin_tac "RingType.tOp R r a = RingType.one R")
 apply (simp add:unit_def)
done

lemma n_pow_not_prime: "\<lbrakk>integral_domain R; a \<in> carrier R; a \<noteq> 0\<^sub>R;  0 < n\<rbrakk>
            \<Longrightarrow>   \<not> prime_ideal R ((Rxa R a) \<^sup>\<diamondsuit>\<^sup>R \<^sup>(Suc n))"
apply (case_tac "n = 0")
 apply simp
apply (case_tac "unit R a")
 apply (simp del:ipSuc add:prime_ideal_def) apply (rule impI)
 apply (frule idom_is_ring[of "R"])
 apply (frule principal_ideal[of "R" "a"], assumption+)
 apply (frule principal_ideal_n_pow[of "R" "a" "R \<diamondsuit> a" "Suc n"], assumption+)
 apply simp apply (simp del:npow_suc)
 apply (simp del:npow_suc add:idom_potent_unit [of "R" "a" "Suc n"])
 apply (thin_tac "R \<diamondsuit> a \<diamondsuit>\<^sub>R R \<diamondsuit> a \<^sup>\<diamondsuit>\<^sup>R \<^sup>n = R \<diamondsuit> (a^\<^sup>R\<^sup> \<^sup>Suc n)")
 apply (frule npClose[of "R" "a" "Suc n"], assumption+)
 apply (frule a_in_principal[of "R" "a^\<^sup>R\<^sup> \<^sup>(Suc n)"], assumption+)
 apply (simp add: ideal_inc_unit)
 apply (frule a_notin_n_pow1[of "R" "a" "n"], assumption+)
 apply (frule a_notin_n_pow2[of "R" "a" "n"], assumption+)
apply (frule idom_is_ring[of "R"])
 apply (frule npClose[of "R" "a" "n"], assumption+)
 apply (frule principal_ideal[of "R" "a"], assumption+)
 apply (frule principal_ideal_n_pow[of "R" "a" "R \<diamondsuit> a" "Suc n"], assumption+)
 apply simp apply (simp del:ipSuc npow_suc)
 apply (thin_tac "R \<diamondsuit> a \<^sup>\<diamondsuit>\<^sup>R \<^sup>Suc n = R \<diamondsuit> (a^\<^sup>R\<^sup> \<^sup>Suc n)")
 apply (subst prime_ideal_def)
 apply (simp del:npow_suc) apply (rule impI)
 apply (subgoal_tac "a \<cdot>\<^sub>R (a^\<^sup>R\<^sup> \<^sup>n) \<in> R \<diamondsuit> (a^\<^sup>R\<^sup> \<^sup>Suc n)")
 apply blast
apply simp
 apply (simp add:Rxa_def)
 apply (thin_tac "ideal R {x. \<exists>r\<in>carrier R. x = RingType.tOp R r a}")
 apply (thin_tac "ideal R
      {x. \<exists>r\<in>carrier R. x = RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))}")
 apply (thin_tac "\<forall>r\<in>carrier R. a^\<^sup>R\<^sup> \<^sup>n \<noteq> RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (thin_tac "\<forall>r\<in>carrier R. a \<noteq> RingType.tOp R r (RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>n))")
 apply (frule ring_one[of "R"])
 apply (frule ring_tOp_closed[of "R" "a" "a^\<^sup>R\<^sup> \<^sup>n"], assumption+)
 apply (frule ring_l_one[THEN sym, of "R" "a \<cdot>\<^sub>R (a^\<^sup>R\<^sup> \<^sup>n)"], assumption+)
 apply blast
done

section "10. extension and contraction"

constdefs
 i_contract::"['a \<Rightarrow> 'b, ('a, 'm1) RingType_scheme, ('b, 'm2) RingType_scheme,
  'b set]  \<Rightarrow> 'a set"
   "i_contract f A R J == invim f (carrier A) J"

 i_extension::"['a \<Rightarrow> 'b, ('a, 'm1) RingType_scheme, ('b, 'm2) RingType_scheme,
           'a set] \<Rightarrow> 'b set"
 "i_extension f A R I == sum_mult R (f ` I) (carrier R)"

lemma i_contract_ideal:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal R J \<rbrakk> \<Longrightarrow>
                                          ideal A (i_contract f A R J)"
apply (simp add:i_contract_def)
apply (rule ideal_condition, assumption+)
 apply (simp add:invim_def) apply (rule subsetI)
 apply (simp add:CollectI)
apply (simp add:invim_def)
 apply (frule rHom_0_0 [of "A" "R" "f"], assumption+)
 apply (frule ring_zero [of "A"])
 apply (frule ring_zero [of "R"])
 apply (frule ideal_zero [of "R" "J"], assumption+)
 apply (subgoal_tac "f (0\<^sub>A) \<in> J") apply blast apply simp
apply (rule ballI)+
 apply (simp add:invim_def)
 apply (erule conjE)+
 apply (frule ring_is_ag)
 apply (frule_tac x = y in ag_mOp_closed [of "A"], assumption+)
 apply (frule_tac x = x and y = "-\<^sub>A y" in ag_pOp_closed, assumption+)
 apply simp
 apply (subst ringhom1[of "A" "R"], assumption+)
 apply (frule_tac x = y and f = f in  rHom_inv_inv [of "A" "R"],
                                                           assumption+)
 apply simp
 apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:ideal_inv1_closed)
apply (rule ballI)+
 apply (simp add:invim_def)
 apply (erule conjE)+
 apply (simp add:ring_tOp_closed)
 apply (subst rHom_tOp [of "A" "R"], assumption+)
 apply (frule_tac a = r in rHom_mem [of "f" "A" "R"], assumption+)
 apply (simp add:ideal_ring_multiple)
done

lemma i_contract_mono:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal R J1; ideal R J2;
 J1 \<subseteq> J2 \<rbrakk> \<Longrightarrow> i_contract f A R J1 \<subseteq> i_contract f A R J2"
apply (rule subsetI)
apply (simp add:i_contract_def invim_def) apply (erule conjE)
apply (rule subsetD, assumption+)
done

lemma i_contract_prime:"\<lbrakk>ring A; ring R; f \<in> rHom A R; prime_ideal R P\<rbrakk> \<Longrightarrow>
                            prime_ideal A (i_contract f A R P)"
apply (simp add:prime_ideal_def) apply (erule conjE)+
 apply (simp add:i_contract_ideal)
 apply (rule conjI)
 apply (rule contrapos_pp, simp+)
 apply (simp add:i_contract_def invim_def) apply (erule conjE)
 apply (simp add:rHom_one)
apply (rule ballI)+
 apply (frule_tac a = x in rHom_mem[of "f" "A" "R"], assumption+)
 apply (frule_tac a = y in rHom_mem[of "f" "A" "R"], assumption+)
 apply (rule impI)
 apply (simp add:i_contract_def invim_def) apply (erule conjE)
 apply (simp add:rHom_tOp)
done

lemma i_extension_ideal:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal A I \<rbrakk> \<Longrightarrow>
                            ideal R (i_extension f A R I)"
apply (simp add:i_extension_def)
apply (rule ideal_sum_mult [of "R" "f ` I" "carrier R"], assumption+)
apply (rule subsetI)
apply (simp add:image_def)
apply (subgoal_tac "\<forall>xa\<in>I. x = f xa \<longrightarrow> x \<in> carrier R")
 apply blast apply (thin_tac "\<exists>xa\<in>I. x = f xa")
 apply (rule ballI) apply (rule impI) apply simp
 apply (frule ideal_subset, assumption+)
 apply (simp add:rHom_mem)
apply (frule ideal_zero, assumption+) apply simp
 apply blast
 apply (simp add:whole_ideal)
done

lemma i_extension_mono:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal A I1; ideal A I2;
 I1 \<subseteq> I2 \<rbrakk> \<Longrightarrow> (i_extension f A R I1) \<subseteq> (i_extension f A R I2)"
apply (frule i_extension_ideal [of "A" "R" "f" "I2"], assumption+)
apply (subgoal_tac "(i_extension f A R I2) <+ R")
prefer 2 apply (simp add:ideal_def)
apply (simp add:i_extension_def)
apply (rule subsetI)
apply (simp add:sum_mult_def [of "R" "f ` I1" "carrier R"])
apply auto
apply (subgoal_tac "set_mult R (f ` I1) (carrier R) \<subseteq>
                                   set_mult R (f ` I2) (carrier R)")
apply (frule extend_fun [of _ _ "set_mult R (f ` I1) (carrier R)"
                            "set_mult R (f ` I2) (carrier R)"], assumption+)
apply (frule ring_is_ag [of "R"])
apply (rule eSum_mem1, assumption+)
apply (frule sum_mult_inc_set_mult [of "R" "f ` I2" "carrier R"])
 apply (thin_tac "fa \<in> Nset n \<rightarrow> set_mult R (f ` I1) (carrier R)")
 apply (thin_tac "set_mult R (f ` I1) (carrier R) \<subseteq> set_mult R (f ` I2) (carrier R)")
 apply (thin_tac "fa \<in> Nset n \<rightarrow> set_mult R (f ` I2) (carrier R)")
 apply (thin_tac "ideal R (sum_mult R (f ` I2) (carrier R))")
 apply (rule subsetI) apply (simp add:image_def)
prefer 2 apply (simp add:whole_ideal)
 apply (subgoal_tac "\<forall>xa\<in>I2. x = f xa \<longrightarrow> x \<in> carrier R")
 apply blast apply (thin_tac "\<exists>xa\<in>I2. x = f xa") apply (rule ballI)
 apply (rule impI) apply simp
 apply (frule ideal_subset [of _ "I2"], assumption+)
 apply (simp add:rHom_mem)
 apply (rule extend_fun [of _ _ "set_mult R (f ` I2) (carrier R)"
                 "sum_mult R (f ` I2) (carrier R)"], assumption+)
apply (rule subsetI)
 apply (simp add:set_mult_def)
 apply auto
done

lemma e_c_inc_self:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal A I \<rbrakk> \<Longrightarrow>
              I \<subseteq> i_contract f A R (i_extension f A R I)"
apply (rule subsetI)
 apply (simp add:i_contract_def i_extension_def)
 apply (simp add:invim_def)
 apply (simp add:ideal_subset)
 apply (frule ring_one [of "R"])
 apply (frule ideal_subset, assumption+)
 apply (subgoal_tac "f x \<in> f ` I")
 apply (frule_tac a = x in rHom_mem [of "f" "A" "R"], assumption+)
 apply (subst ring_r_one [of "R", THEN sym], assumption+)
 apply (rule_tac a = "f x" in times_mem_sum_mult [of "R" "f ` I" "carrier R" _ "1\<^sub>R"], assumption+)
 apply (rule subsetI)
 apply (thin_tac " f x \<in> f ` I")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>I. xa = f x \<longrightarrow> xa \<in> carrier R")
 apply blast apply (thin_tac "\<exists>x\<in>I. xa = f x")
 apply (rule ballI) apply (rule impI) apply simp
 apply (thin_tac "x \<in> I") apply (frule ideal_subset, assumption+)
 apply (thin_tac "x \<in> carrier A") apply (rule rHom_mem, assumption+)
 apply simp apply assumption+
 apply (simp add:image_def)
 apply blast
done

lemma c_e_incd_self:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal R J \<rbrakk> \<Longrightarrow>
                           i_extension f A R (i_contract f A R J) \<subseteq> J"
apply (rule subsetI)
 apply (simp add:i_extension_def)
 apply (simp add:sum_mult_def)
 apply auto
 apply (frule ring_is_ag [of "R"])
 apply (subgoal_tac "J <+ R") prefer 2 apply (simp add:ideal_def)
 apply (rule eSum_mem1, assumption+)
 apply (subgoal_tac "set_mult R (f ` i_contract f A R J) (carrier R) \<subseteq> J")
 apply (rule extend_fun, assumption+)
 apply (thin_tac "fa \<in> Nset n \<rightarrow> set_mult R (f ` i_contract f A R J) (carrier R)")
 apply (simp add:set_mult_def)
 apply (rule subsetI) apply (simp add:CollectI)
 apply auto
 apply (simp add:i_contract_def invim_def)
 apply (erule conjE)
 apply (frule rHom_mem, assumption+)
 apply (subst ring_tOp_commute, assumption+)
apply (simp add:ideal_ring_multiple)
done

lemma c_e_c_eq_c:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal R J \<rbrakk> \<Longrightarrow>
  i_contract f A R (i_extension f A R (i_contract f A R J))
                                          = i_contract f A R J"
apply (frule i_contract_ideal [of "A" "R" "f" "J"], assumption+)
apply (frule e_c_inc_self [of "A" "R" "f" "i_contract f A R J"], assumption+)
apply (frule c_e_incd_self [of "A" "R" "f" "J"], assumption+)
apply (frule i_contract_mono [of "A" "R" "f"
         "i_extension f A R (i_contract f A R J)" "J"], assumption+)
apply (rule i_extension_ideal, assumption+)
apply (rule equalityI, assumption+)
done

lemma e_c_e_eq_e:"\<lbrakk>ring A; ring R; f \<in> rHom A R; ideal A I \<rbrakk> \<Longrightarrow>
  i_extension f A R (i_contract f A R (i_extension f A R I))
                                          = i_extension f A R I"
apply (frule i_extension_ideal [of "A" "R" "f" "I"], assumption+)
apply (frule c_e_incd_self [of "A" "R" "f" "i_extension f A R I"], assumption+)
apply (rule equalityI, assumption+)
 apply (thin_tac "i_extension f A R (i_contract f A R (i_extension f A R I))
       \<subseteq> i_extension f A R I")
apply (frule e_c_inc_self [of "A" "R" "f" "I"], assumption+)
apply (rule i_extension_mono [of "A" "R" "f" "I"
               "i_contract f A R (i_extension f A R I)"], assumption+)
apply (rule i_contract_ideal, assumption+)
done

chapter "5. Modules"

section "1. Basic properties of Modules"

record ('a, 'b) ModuleType = "'a AgroupType" +
  sprod  :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"

constdefs
 Module ::"[('b, 'more) RingType_scheme, ('a, 'b, 'more1) ModuleType_scheme] \<Rightarrow> bool" (infixl "module" 100)
 "Module R M  == ring R \<and> agroup M \<and>
     sprod M \<in> carrier R \<rightarrow> carrier M \<rightarrow> carrier M \<and>
  (\<forall>a \<in> carrier R. \<forall>b\<in> carrier R. \<forall>m\<in>carrier M. \<forall>n\<in>carrier M.
   sprod M (tOp R a b) m = sprod M a (sprod M b m) \<and>
   sprod M (pOp R a b) m = pOp M (sprod M a m) (sprod M b m) \<and>
   sprod M a (pOp M m n) = pOp M (sprod M a m) (sprod M a n) \<and>
   sprod M (1\<^sub>R) m = m)"

submodule :: "[('b, 'more) RingType_scheme, ('a, 'b, 'more1) ModuleType_scheme,
 'a set] \<Rightarrow> bool"
 "submodule R M H == H \<subseteq> carrier M \<and> H <+ M \<and> (\<forall>a\<in>carrier R. \<forall>m\<in>H.
  sprod M a m \<in> H)"

constdefs
mdl :: "[('a, 'b, 'more1) ModuleType_scheme, 'a set] \<Rightarrow> ('a, 'b) ModuleType"
 "mdl M H == \<lparr>carrier = H, pOp = pOp M, mOp = mOp M, zero = zero M,
    sprod = sprod M\<rparr>"

syntax
  "@SPROD" :: "['b, ('a, 'b, 'more1) ModuleType_scheme] \<Rightarrow> 'a \<Rightarrow> 'a"
              ("(3 _/ \<star>\<^sub>_/ _)" [68,68,69]68 )

translations
  "a \<star>\<^sub>M m" == "sprod M a m"

lemma module_is_ag:"\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow> agroup M"
apply (simp add:Module_def)
done

lemma module_inc_zero:"\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow> 0\<^sub>M \<in> carrier M"
apply (frule module_is_ag, assumption+)
apply (simp add:ag_inc_zero)
done

lemma submodule_subset1:"\<lbrakk>ring R; R module M; submodule R M H; h \<in> H \<rbrakk> \<Longrightarrow>
                            h \<in> carrier M"
apply (simp add:submodule_def)
apply (erule conjE)+
apply (simp add:subsetD)
done

lemma submodule_inc_0:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                                           0\<^sub>M \<in> H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (simp add:submodule_def) apply (erule conjE)+
apply (rule asubg_inc_zero, assumption+)
done

lemma sprod_one:"\<lbrakk>ring R; R module M; m \<in> carrier M\<rbrakk> \<Longrightarrow>
           (1\<^sub>R) \<star>\<^sub>M m = m"
apply (frule ring_one)
apply (simp add:Module_def)
done

lemma sprod_mem:"\<lbrakk>ring R; R module M; a \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow>
           a \<star>\<^sub>M m \<in> carrier M"
apply (simp add:Module_def)
apply (erule conjE)+
apply (simp add:bivar_fun_mem)
done

lemma submodule_sprod_closed:"\<lbrakk>ring R; R module M; submodule R M H;
 a \<in> carrier R; h \<in> H\<rbrakk> \<Longrightarrow>  a \<star>\<^sub>M h \<in> H"
apply (simp add:submodule_def)
done

lemma sprod_assoc:"\<lbrakk>ring R; R module  M; a \<in> carrier R; b \<in> carrier R;
 m \<in> carrier M\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>R b \<star>\<^sub>M m =  a \<star>\<^sub>M ( b \<star>\<^sub>M m)"
apply (simp add:Module_def)
done

lemma one_module_id:"\<lbrakk> ring R; R module M; m \<in> carrier M \<rbrakk> \<Longrightarrow>
            sprod M (1\<^sub>R) m = m"
apply (frule ring_one)
apply (simp add:Module_def)
done

lemma sprod_distrib1:"\<lbrakk>ring R; R module M; a \<in> carrier R; b \<in> carrier R;
 m \<in> carrier M\<rbrakk> \<Longrightarrow> ( a +\<^sub>R b) \<star>\<^sub>M m =   a \<star>\<^sub>M m +\<^sub>M  b \<star>\<^sub>M m"
apply (simp add:Module_def)
done

lemma sprod_distrib2:"\<lbrakk>ring R; R module M; a \<in> carrier R; m \<in> carrier M;
 n \<in> carrier M\<rbrakk> \<Longrightarrow> a \<star>\<^sub>M ( m +\<^sub>M n) = a \<star>\<^sub>M m +\<^sub>M  a \<star>\<^sub>M n"
apply (simp add:Module_def)
done

lemma sprod_0_m:"\<lbrakk>ring R; R module M; m \<in> carrier M\<rbrakk> \<Longrightarrow> 0\<^sub>R \<star>\<^sub>M m = 0\<^sub>M"
apply (frule ring_is_ag)
apply (frule ag_inc_zero [of "R"])
apply (frule sprod_distrib1 [of "R" "M" "0\<^sub>R" "0\<^sub>R" "m"], assumption+)
apply (frule sprod_mem [of "R" "M" "0\<^sub>R" "m"], assumption+)
apply (simp add:ag_l_zero) apply (frule sym)
apply (thin_tac "0\<^sub>R \<star>\<^sub>M m = 0\<^sub>R \<star>\<^sub>M m +\<^sub>M  0\<^sub>R \<star>\<^sub>M m")
apply (frule module_is_ag [of "R" "M"], assumption)
apply (thin_tac "agroup R") apply (frule ag_eq_sol1 [of "M" "0\<^sub>R \<star>\<^sub>M m" "0\<^sub>R \<star>\<^sub>M m" "0\<^sub>R \<star>\<^sub>M m"], assumption+)
apply (simp add:ag_l_inv1)
done

lemma sprod_a_0:"\<lbrakk>ring R; R module M; a \<in> carrier R\<rbrakk> \<Longrightarrow> a \<star>\<^sub>M (0\<^sub>M) = 0\<^sub>M"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule ag_inc_zero [of "M"])
apply (frule sprod_distrib2 [of "R" "M" "a" "0\<^sub>M" "0\<^sub>M"], assumption+)
apply (frule sprod_mem [of "R" "M" "a" "0\<^sub>M"], assumption+)
apply (simp add:ag_l_zero) apply (frule sym)
apply (thin_tac "a \<star>\<^sub>M 0\<^sub>M = a \<star>\<^sub>M 0\<^sub>M +\<^sub>M  (a \<star>\<^sub>M 0\<^sub>M)")
apply (frule ag_eq_sol1 [of "M" "a \<star>\<^sub>M (0\<^sub>M)" "a \<star>\<^sub>M (0\<^sub>M)" "a \<star>\<^sub>M (0\<^sub>M)"], assumption+)
apply (simp add:ag_l_inv1)
done

lemma sprod_minus_am:"\<lbrakk>ring R; R module M; a \<in> carrier R; m \<in> carrier M\<rbrakk>
   \<Longrightarrow> -\<^sub>M (a \<star>\<^sub>M m) = a \<star>\<^sub>M (-\<^sub>M m)"
apply (frule module_is_ag, assumption+)
apply (frule ag_mOp_closed [of "M" "m"], assumption+)
apply (frule sprod_distrib2 [of "R" "M" "a" "m" "-\<^sub>M m"], assumption+)
apply (simp add:ag_r_inv1)
apply (simp add:sprod_a_0) apply (frule sym)
 apply (thin_tac "0\<^sub>M =   a \<star>\<^sub>M m +\<^sub>M  a \<star>\<^sub>M (-\<^sub>M m)")
 apply (frule sprod_mem [of "R" "M" "a" "m"], assumption+)
 apply (frule sprod_mem [of "R" "M" "a" "-\<^sub>M m"], assumption+)
 apply (frule ag_eq_sol1 [of "M" "a \<star>\<^sub>M m" "a \<star>\<^sub>M (-\<^sub>M m)" "0\<^sub>M"], assumption+)
 apply (simp add:ag_inc_zero) apply assumption
 apply (frule ag_mOp_closed [of "M" "a \<star>\<^sub>M m"], assumption+)
 apply (thin_tac "a \<star>\<^sub>M m +\<^sub>M  a \<star>\<^sub>M (-\<^sub>M m) = 0\<^sub>M")
 apply (simp add:ag_r_zero)
done

lemma sprod_minus_am1:"\<lbrakk>ring R; R module M; a \<in> carrier R; m \<in> carrier M\<rbrakk>
   \<Longrightarrow> -\<^sub>M (a \<star>\<^sub>M m) = (-\<^sub>R a) \<star>\<^sub>M m"
apply (frule ring_is_ag)
apply (frule ag_mOp_closed [of "R" "a"], assumption+)
apply (frule module_is_ag, assumption+)
apply (frule sprod_distrib1 [of "R" "M" "a" "-\<^sub>R a" "m"], assumption+)
apply (simp add:ag_r_inv1 [of "R"])
apply (simp add:sprod_0_m) apply (frule sym)
 apply (thin_tac "0\<^sub>M =   a \<star>\<^sub>M m +\<^sub>M  (-\<^sub>R a) \<star>\<^sub>M m")
 apply (frule sprod_mem [of "R" "M" "a" "m"], assumption+)
 apply (frule sprod_mem [of "R" "M" "-\<^sub>R a" "m"], assumption+)
 apply (frule ag_eq_sol1 [of "M" "a \<star>\<^sub>M m" "(-\<^sub>R a) \<star>\<^sub>M m" "0\<^sub>M"], assumption+)
 apply (simp add:ag_inc_zero [of "M"]) apply assumption
 apply (frule ag_mOp_closed [of "M" "a \<star>\<^sub>M m"], assumption+)
 apply (thin_tac "a \<star>\<^sub>M m +\<^sub>M (-\<^sub>R a) \<star>\<^sub>M m = 0\<^sub>M")
 apply (simp add:ag_r_zero)
done

lemma submodule_0:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> submodule R M {0\<^sub>M}"
apply (simp add:submodule_def)
apply (frule module_is_ag, assumption+)
apply (simp add:ag_inc_zero)
apply (rule conjI)
 apply (simp add:asubgroup_def)
 apply (subgoal_tac "0\<^sub>M = GroupType.one (b_ag M)")
 apply (frule b_ag_group)
 apply (simp add:special_subg_e)
apply (simp add:b_ag_def)
apply (rule ballI)
apply (simp add:sprod_a_0)
done

lemma submodule_whole:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> submodule R M (carrier M)"
apply (simp add:submodule_def)
apply (frule module_is_ag, assumption+)
apply (rule conjI)
 apply (simp add:asubgroup_def)
 apply (frule b_ag_group)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:special_subg_G)
apply (rule ballI)
apply (simp add:sprod_mem)
done

lemma submodule_pOp_closed:"\<lbrakk>ring R; R module M; submodule R M H; h \<in> H;
 k \<in> H \<rbrakk> \<Longrightarrow> h +\<^sub>M k \<in> H"
apply (simp add:submodule_def)
apply (erule conjE)+
apply (thin_tac "\<forall>a\<in>carrier R. \<forall>m\<in>H.  a \<star>\<^sub>M m \<in> H")
apply (simp add:asubgroup_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (simp add:agop_gop [THEN sym])
apply (frule b_ag_group)
apply (simp add:subg_tOp_closed)
done

lemma submodule_mOp_closed:"\<lbrakk>ring R; R module M; submodule R M H; h \<in> H \<rbrakk>
 \<Longrightarrow> -\<^sub>M h \<in> H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (simp add:submodule_def) apply (erule conjE)+
apply (rule asubg_mOp_closed, assumption+)
done

constdefs
 mHom :: "[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
                    ('c, 'b, 'm2) ModuleType_scheme] \<Rightarrow>  ('a \<Rightarrow> 'c) set"
        (*  ("(3HOM\<^sub>_/ _/ _)" [90, 90, 91]90 ) *)

 "mHom R M N == {f. f \<in> aHom M N \<and>
             (\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. f (a \<star>\<^sub>M m) = a \<star>\<^sub>N (f m))}"

 mimg ::"[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
  ('c, 'b, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'c] \<Rightarrow>  ('c, 'b) ModuleType"
                 ("(4mimg\<^sub>_ \<^sub>_\<^sub>,\<^sub>_/ _)" [88,88,88,89]88)
 "mimg\<^sub>R \<^sub>M\<^sub>,\<^sub>N f == mdl N (f ` (carrier M))"

 mzeromap::"[('a, 'b, 'm1) ModuleType_scheme, ('c, 'b, 'm2) ModuleType_scheme]
                              \<Rightarrow> ('a \<Rightarrow> 'c)"
  "mzeromap M N == \<lambda>x\<in>carrier M. 0\<^sub>N"

lemma mHom_test:"\<lbrakk>ring R;R module M; R module N; f \<in> carrier M \<rightarrow> carrier N \<and> f \<in> extensional (carrier M) \<and> (\<forall>m\<in>carrier M. \<forall>n\<in>carrier M. f (m +\<^sub>M n) = f m +\<^sub>N (f n)) \<and> (\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. f (a \<star>\<^sub>M m) = a \<star>\<^sub>N (f m))\<rbrakk> \<Longrightarrow>
  f \<in> mHom R M N"
apply (simp add:mHom_def)
apply (simp add:aHom_def)
done

lemma mHom_mem:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N; m \<in> carrier M\<rbrakk>
 \<Longrightarrow> f m \<in> carrier N"
apply (simp add:mHom_def aHom_def) apply (erule conjE)+
apply (simp add:funcset_mem)
done

lemma mHom_add:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N; m \<in> carrier M;n \<in> carrier M\<rbrakk> \<Longrightarrow> f (m +\<^sub>M n) = f m +\<^sub>N (f n)"
apply (simp add:mHom_def) apply (erule conjE)+
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:aHom_add)
done

lemma mHom_0:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                   f (0\<^sub>M) = 0\<^sub>N"
apply (simp add:mHom_def) apply (erule conjE)+
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:aHom_0_0)
done

lemma mHom_inv:"\<lbrakk>ring R; R module M; R module N; m \<in> carrier M; f \<in> mHom R M N\<rbrakk> \<Longrightarrow> f (-\<^sub>M m) = -\<^sub>N (f m)"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:mHom_def) apply (erule conjE)+
apply (rule aHom_inv_inv, assumption+)
done

lemma mHom_lin:"\<lbrakk>ring R; R module M; R module N; m \<in> carrier M; f \<in> mHom R M N;
 a \<in> carrier R\<rbrakk> \<Longrightarrow> f (a \<star>\<^sub>M m) = a \<star>\<^sub>N (f m)"
apply (simp add:mHom_def)
done

lemma mker_inc_one:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N \<rbrakk> \<Longrightarrow>
                           0\<^sub>M \<in> (ker\<^sub>M\<^sub>,\<^sub>N f)"
apply (simp add:ker_def)
apply (simp add:module_inc_zero)
apply (simp add:mHom_0)
done

lemma mHom_eq_ker:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N; a\<in>carrier M; b\<in> carrier M; a +\<^sub>M (-\<^sub>M b) \<in> ker\<^sub>M\<^sub>,\<^sub>N f\<rbrakk> \<Longrightarrow> f a = f b"
apply (simp add:ker_def) apply (erule conjE)
apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (frule ag_mOp_closed [of "M" "b"], assumption+)
apply (simp add:mHom_add)
apply (simp add:mHom_inv) apply (thin_tac "agroup M")
apply (frule mHom_mem [of "R" "M" "N" "f" "a"], assumption+)
apply (frule mHom_mem [of "R" "M" "N" "f" "b"], assumption+)
apply (frule module_is_ag[of "R" "N"], assumption+)
 apply (frule ag_mOp_closed [of "N" "f b"], assumption+)
 apply (subgoal_tac "f a +\<^sub>N (-\<^sub>N (f b)) +\<^sub>N (f b) = 0\<^sub>N +\<^sub>N (f b)")
 prefer 2 apply simp
 apply (thin_tac "f a +\<^sub>N (-\<^sub>N (f b)) = 0\<^sub>N")
 apply (simp add:ag_pOp_assoc)
 apply (simp add:ag_l_inv1) apply (simp add:ag_r_zero)
 apply (simp add:ag_l_zero)
done

lemma mker_submodule:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
         submodule R M (ker\<^sub>M\<^sub>,\<^sub>N f  )"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:submodule_def)
 apply (rule conjI)
 apply (rule subsetI) apply (simp add:ker_def)
 apply (rule conjI)
 apply (simp add:mHom_def) apply (erule conjE)+
 apply (simp add:ker_subg)
apply (rule ballI)+
 apply (simp add:ker_def) apply (erule conjE)
 apply (simp add:sprod_mem)
 apply (subst mHom_lin [of "R" "M" "N" _ "f"], assumption+)
 apply simp
 apply (simp add:sprod_a_0)
done

lemma mker_mzeromap:"\<lbrakk>ring R; R module M; R module N\<rbrakk> \<Longrightarrow>
                         ker\<^sub>M\<^sub>,\<^sub>N (mzeromap M N) = carrier M"
apply (simp add:ker_def mzeromap_def)
done

lemma mdl_carrier:"\<lbrakk>ring R; R module M;submodule R M H\<rbrakk> \<Longrightarrow>
                                            carrier (mdl M H) = H"
apply (simp add:mdl_def)
done

lemma mdl_is_ag:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                                             agroup (mdl M H)"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (simp add:agroup_def [of "mdl M H"])
apply (simp add:mdl_def)
apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:submodule_def)
 apply (erule conjE)+
 apply (simp add:asubg_pOp_closed)
apply (rule conjI)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:asubg_mOp_closed)
apply (rule conjI)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:asubg_inc_zero)
apply (rule ballI)+
 apply (subgoal_tac "\<forall>y. y \<in> H \<longrightarrow> y \<in> carrier M")
 apply (simp add:agroup_def) apply (erule conjE)+
 apply blast
apply (rule allI) apply (rule impI) apply (simp add:submodule_def)
 apply (erule conjE)+ apply (simp add:subsetD)
done

lemma mdl_is_module:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow> R module (mdl M H)"
apply (simp add:Module_def [of "R" "mdl M H"])
apply (simp add:mdl_is_ag [of "R" "M" "H"])
 apply (simp add:mdl_def)
apply (rule conjI)
apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:submodule_def)
apply (subgoal_tac "\<forall>h. h \<in> H \<longrightarrow> h \<in> carrier M")
apply (simp add:Module_def) apply (erule conjE)+
 apply (rule impI) apply blast
apply (rule allI) apply (rule impI)
 apply (simp add:submodule_def)
 apply (erule conjE)+
 apply (simp add:subsetD)
done

lemma img_set_submodule:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
         submodule R N (f ` (carrier M))"
apply (simp add:submodule_def)
apply (rule conjI)
 apply (rule subsetI)
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>carrier M. x = f xa \<longrightarrow> x \<in> carrier N") apply blast
 apply (thin_tac "\<exists>xa\<in>carrier M. x = f xa")
 apply (rule ballI) apply (rule impI) apply simp
 apply (simp add:mHom_mem)
apply (rule conjI)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (rule asubg_test, assumption+)
 apply (rule subsetI) apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>carrier M. x = f xa \<longrightarrow> x \<in> carrier N")
 apply blast apply (thin_tac "\<exists>xa\<in>carrier M. x = f xa")
 apply (rule ballI) apply (rule impI) apply simp apply (simp add:mHom_mem)
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule ag_inc_zero [of "M"])
 apply (subgoal_tac "f (0\<^sub>M) \<in> f ` (carrier M)") apply blast
 apply (simp add:image_def) apply blast
apply (rule ballI)+
 apply (simp add:image_def)
 apply auto
 apply (subst mHom_inv [THEN sym, of "R" "M" "N" _ "f"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = xa in ag_mOp_closed [of "M"], assumption+)
 apply (simp add: mHom_add [THEN sym, of "R" "M" "N" "f"])
 apply (frule_tac x = x and y = "-\<^sub>M xa" in ag_pOp_closed [of "M"],
                                                         assumption+)
 apply blast
 apply (frule_tac m1 = m and a1 = a in mHom_lin [THEN sym,
                             of "R" "M" "N" _ "f"], assumption+)
 apply simp
 apply (thin_tac "a \<star>\<^sub>N (f m) = f ( a \<star>\<^sub>M m)")
 apply (frule_tac a = a and m = m in sprod_mem [of "R" "M"], assumption+)
 apply (simp add:image_def)
apply blast
done

lemma mimg_module:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
        R module (mimg R M N f)"
apply (simp add:mimg_def)
apply (rule mdl_is_module [of "R" "N" "f ` (carrier M)"], assumption+)
apply (simp add:img_set_submodule)
done

constdefs
 tOp_mHom :: "[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
  ('c, 'b, 'm2) ModuleType_scheme] \<Rightarrow>  ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)"
 "tOp_mHom R M N f g == \<lambda>x \<in> carrier M. (f x +\<^sub>N (g x))"

 iOp_mHom :: "[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
  ('c, 'b, 'm2) ModuleType_scheme] \<Rightarrow>  ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)"
 "iOp_mHom R M N f  == \<lambda>x \<in> carrier M. (-\<^sub>N (f x))"

 sprod_mHom ::"[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
  ('c, 'b, 'm2) ModuleType_scheme] \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)"
 "sprod_mHom R M N a f  == \<lambda>x \<in> carrier M. a \<star>\<^sub>N (f x)"

 HOM :: "[('b, 'more) RingType_scheme, ('a, 'b, 'more1) ModuleType_scheme,
   ('c, 'b, 'more2) ModuleType_scheme] \<Rightarrow> ('a \<Rightarrow> 'c, 'b) ModuleType"
                                       ("(3HOM\<^sub>_/ _/ _)" [90, 90, 91]90 )

 "HOM\<^sub>R M N == \<lparr>carrier = mHom R M N, pOp = tOp_mHom R M N,
  mOp = iOp_mHom R M N, zero = mzeromap M N,  sprod =sprod_mHom R M N \<rparr>"

lemma tOp_mHom_closed:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
 g \<in> mHom R M N\<rbrakk> \<Longrightarrow> tOp_mHom R M N f g \<in> mHom R M N"
 apply (rule mHom_test, assumption+)
 apply (rule conjI)
 apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:tOp_mHom_def)
 apply (frule_tac f = f and m = x in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule_tac f = g and m = x in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_pOp_closed)
apply (rule conjI)
 apply (simp add:tOp_mHom_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:tOp_mHom_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = m and y = n in ag_pOp_closed [of "M"], assumption+)
 apply simp
apply (frule_tac f = f and m = m in mHom_mem [of "R" "M" "N"], assumption+)
apply (frule_tac f = f and m = n in mHom_mem [of "R" "M" "N"], assumption+)
apply (frule_tac f = g and m = m in mHom_mem [of "R" "M" "N"], assumption+)
apply (frule_tac f = g and m = n in mHom_mem [of "R" "M" "N"], assumption+)
apply (frule_tac f = f and m = m and n = n in mHom_add [of "R" "M" "N"],
                                                   assumption+)
apply (frule_tac f = g and m = m and n = n in mHom_add [of "R" "M" "N"],
                                                   assumption+)
apply simp
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simplesubst pOp_assocTr43[of "N"], assumption+)
apply (frule_tac x = "g m" and y = "f n" in ag_pOp_commute [of "N"],
                                                              assumption+)
apply simp
apply (subst pOp_assocTr43[of "N"], assumption+) apply simp
apply (rule ballI)+
apply (simp add:tOp_mHom_def)
apply (frule_tac a = a and m = m in sprod_mem [of "R" "M"], assumption+)
apply simp
apply (frule_tac f = f and m = m in mHom_mem [of "R" "M" "N"],
                                                             assumption+)
apply (frule_tac f = g and m = m in mHom_mem [of "R" "M" "N"],
                                                             assumption+)
apply (frule_tac a = a and m = "f m" and n = "g m" in
                                  sprod_distrib2 [of "R" "N"], assumption+)
apply simp
apply (simp add:mHom_lin)
done

lemma iOp_mHom_closed:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk>
        \<Longrightarrow> iOp_mHom R M N f \<in> mHom R M N"
apply (rule mHom_test, assumption+)
 apply (rule conjI) apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI) apply (simp add:iOp_mHom_def)
 apply (frule_tac f = f and m = x in mHom_mem [of "R" "M" "N"],
                                                             assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_mOp_closed)
 apply (rule conjI)
apply (simp add:iOp_mHom_def restrict_def extensional_def)
apply (rule conjI) apply (rule ballI)+
 apply (simp add:iOp_mHom_def)
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (frule_tac x = m and y = n in ag_pOp_closed [of "M"], assumption+)
 apply simp
 apply (frule_tac f = f and m = m and n = n in mHom_add [of "R" "M" "N"],
                                                              assumption+)
 apply simp
 apply (frule_tac f = f and m = m in mHom_mem [of "R" "M" "N"],
                                                             assumption+)
 apply (frule_tac f = f and m = n in mHom_mem [of "R" "M" "N"],
                                                             assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:ag_minus_apb)
apply (rule ballI)+
apply (simp add:iOp_mHom_def)
apply (simp add:sprod_mem)
 apply (frule_tac m = m and f = f and a = a in mHom_lin [of "R" "M" "N"],
                                                   assumption+)
 apply simp
 apply (frule_tac f = f and m = m in mHom_mem [of "R" "M" "N"],
                                                             assumption+)
 apply (simp add:sprod_minus_am)
done

lemma mHom_ex_one:"\<lbrakk>ring R; R module M; R module N\<rbrakk> \<Longrightarrow>
                                     mzeromap M N \<in> mHom R M N "
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI) apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mzeromap_def) apply (simp add:module_inc_zero)
 apply (simp add:mzeromap_def extensional_def)
 apply (rule ballI)+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed [of "M"], assumption+)
 apply simp
 apply (frule ag_inc_zero [of "N"])
 apply (simp add:ag_l_zero)
apply (rule ballI)+
 apply (simp add:mzeromap_def)
 apply (simp add:sprod_mem)
 apply (simp add:sprod_a_0)
done

lemma mHom_eq:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
  g \<in> mHom R M N; \<forall>m\<in>carrier M. f m = g m \<rbrakk> \<Longrightarrow> f = g"
apply (simp add:mHom_def aHom_def)
 apply (erule conjE)+
 apply (rule funcset_eq, assumption+)
done

lemma mHom_l_one:"\<lbrakk>ring R; R module M; R module N; x \<in> mHom R M N\<rbrakk>
       \<Longrightarrow> tOp_mHom R M N (mzeromap M N) x = x"
apply (frule mHom_ex_one [of "R" "M" "N"], assumption+)
apply (frule tOp_mHom_closed [of "R" "M" "N" "mzeromap M N" "x"], assumption+)
apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:tOp_mHom_def) apply (simp add:mzeromap_def)
 apply (frule_tac f = x and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_l_zero)
done

lemma mHom_l_inv:" \<lbrakk>ring R; R module M; R module N; x \<in> mHom R M N\<rbrakk>
       \<Longrightarrow> tOp_mHom R M N (iOp_mHom R M N x) x = mzeromap M N"
apply (frule mHom_ex_one [of "R" "M" "N"], assumption+)
apply (frule_tac f = x in iOp_mHom_closed [of "R" "M" "N"], assumption+)
apply (frule_tac f = "iOp_mHom R M N x" and g = x in tOp_mHom_closed [of "R" "M" "N"], assumption+)
apply (frule mHom_ex_one [of "R" "M" "N"], assumption+)
apply (rule mHom_eq, assumption+) apply (rule ballI)
 apply (simp add:tOp_mHom_def)
 apply (simp add:iOp_mHom_def) apply (simp add:mzeromap_def)
 apply (frule_tac f = x and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_l_inv1)
done

lemma mHom_tOp_assoc:" \<lbrakk>ring R; R module M; R module N; x \<in> mHom R M N;
 y \<in> mHom R M N; z \<in> mHom R M N\<rbrakk> \<Longrightarrow> tOp_mHom R M N (tOp_mHom R M N x y) z =
          tOp_mHom R M N x (tOp_mHom R M N y z)"
apply (frule_tac f = x and g = y in tOp_mHom_closed [of "R" "M" "N"],
                                              assumption+)
 apply (frule_tac f = "tOp_mHom R M N x y" and g = z in
                      tOp_mHom_closed [of "R" "M" "N"], assumption+)
 apply (frule_tac f = y and g = z in tOp_mHom_closed [of "R" "M" "N"],
                                              assumption+)
 apply (frule_tac f = x and g = "tOp_mHom R M N y z" in
                      tOp_mHom_closed [of "R" "M" "N"], assumption+)
 apply (rule mHom_eq, assumption+) apply (rule ballI)
 apply (thin_tac "tOp_mHom R M N x y \<in> mHom R M N")
 apply (thin_tac "tOp_mHom R M N (tOp_mHom R M N x y) z \<in> mHom R M N")
 apply (thin_tac "tOp_mHom R M N y z \<in> mHom R M N")
 apply (thin_tac "tOp_mHom R M N x (tOp_mHom R M N y z) \<in> mHom R M N")
 apply (simp add:tOp_mHom_def)
 apply (frule_tac f = x and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule_tac f = y and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule_tac f = z and m = m in mHom_mem [of "R" "M" "N"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_pOp_assoc)
done

lemma mHom_tOp_commute:"\<lbrakk>ring R; R module M; R module N; x \<in> mHom R M N;
 y \<in> mHom R M N\<rbrakk> \<Longrightarrow> tOp_mHom R M N x y = tOp_mHom R M N y x"
apply (frule_tac f = x and g = y in tOp_mHom_closed [of "R" "M" "N"],
                                              assumption+)
apply (frule_tac f = y and g = x in tOp_mHom_closed [of "R" "M" "N"],
                                              assumption+)
apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (thin_tac "tOp_mHom R M N x y \<in> mHom R M N")
 apply (thin_tac "tOp_mHom R M N y x \<in> mHom R M N")
 apply (simp add:tOp_mHom_def)
 apply (frule_tac f = x and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule_tac f = y and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_pOp_commute)
done

lemma HOM_is_ag:"\<lbrakk>ring R; R module M; R module N\<rbrakk> \<Longrightarrow> agroup (HOM\<^sub>R M N)"
apply (simp add:agroup_def)
apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (simp add:tOp_mHom_closed)
apply (rule conjI)
 apply (simp add:HOM_def)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:iOp_mHom_closed)
apply (rule conjI)
 apply (simp add:HOM_def)
apply (simp add:mHom_ex_one)
apply (rule ballI)+
 apply (simp add:HOM_def)
apply (frule mHom_ex_one [of "R" "M" "N"], assumption+)
apply (simp add:mHom_l_one)
apply (simp add:mHom_l_inv)
apply (simp add:mHom_tOp_assoc)
apply (simp add:mHom_tOp_commute)
done

lemma sprod_mHom_closed:"\<lbrakk>ring R; R module M; R module N; a \<in> carrier R;
 f \<in> mHom R M N\<rbrakk> \<Longrightarrow> sprod_mHom R M N a f \<in> mHom R M N"
apply (rule mHom_test, assumption+)
apply (rule conjI)
 apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI) apply (simp add:sprod_mHom_def)
 apply (frule_tac f = f and m = x in mHom_mem [of "R" "M" "N"], assumption+)
 apply (simp add:sprod_mem [of "R" "N" "a"])
apply (rule conjI)
apply (simp add:sprod_mHom_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = m and y = n in ag_pOp_closed [of "M"], assumption+)
 apply (simp add:sprod_mHom_def)
apply (subst mHom_add [of "R" "M" "N" "f"], assumption+)
 apply (frule_tac f = f and m = m in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule_tac f = f and m = n in mHom_mem [of "R" "M" "N"], assumption+)
 apply (simp add:sprod_distrib2)
apply (rule ballI)+
 apply (simp add:sprod_mHom_def)
 apply (frule_tac a = aa and m = m in sprod_mem [of "R" "M"], assumption+)
 apply simp
 apply (frule_tac m = m and f = f and a = aa in  mHom_lin [of "R" "M" "N"],
                                                                assumption+)
 apply simp
apply (frule_tac f = f and m = m in mHom_mem [of "R" "M" "N"], assumption+)
apply (subst sprod_assoc [THEN sym, of "R" "N"], assumption+)
apply (subst sprod_assoc [THEN sym, of "R" "N"], assumption+)
apply (simp add:ring_tOp_commute)
done

lemma HOM_is_module:"\<lbrakk>ring R; R module M; R module N\<rbrakk> \<Longrightarrow> R module (HOM\<^sub>R M N)"
apply (simp add:Module_def [of "R" "HOM\<^sub>R M N"])
apply (simp add:HOM_is_ag)
apply (rule conjI)
 apply (simp add:HOM_def)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:sprod_mHom_closed)
apply (rule ballI)+ apply (simp add:HOM_def)
apply (frule_tac x = a and y = b in ring_tOp_closed [of "R"], assumption+)
apply (frule_tac a = "a \<cdot>\<^sub>R b" and f = m in sprod_mHom_closed [of "R" "M" "N"],
                                                  assumption+)
apply (frule_tac a = b and f = m in sprod_mHom_closed [of "R" "M" "N"],
                                                  assumption+)
apply (frule_tac a = a and f = "sprod_mHom R M N b m" in
                        sprod_mHom_closed [of "R" "M" "N"], assumption+)
apply (rule conjI)
 apply (rule mHom_eq, assumption+) apply (rule ballI)
 apply (simp add:sprod_mHom_def)
 apply (frule_tac f = m and m = ma in mHom_mem [of "R" "M" "N"], assumption+)
 apply (simp add:sprod_assoc)
 apply (thin_tac "a \<cdot>\<^sub>R b \<in> carrier R")
 apply (thin_tac "sprod_mHom R M N ( a \<cdot>\<^sub>R b) m \<in> mHom R M N")
 apply (thin_tac "sprod_mHom R M N a (sprod_mHom R M N b m) \<in> mHom R M N")
apply (frule ring_is_ag)
 apply (frule_tac x = a and y = b in ag_pOp_closed, assumption+)

 apply (frule_tac a = "a +\<^sub>R b" and f = m in sprod_mHom_closed [of "R" "M" "N"],
                                                  assumption+)
 apply (frule_tac a = a and f = m in sprod_mHom_closed [of "R" "M" "N"],
                                                   assumption+)
 apply (rule conjI)
 apply (rule mHom_eq, assumption+)
 apply (simp add:tOp_mHom_closed)
 apply (rule ballI)
 apply (simp add:sprod_mHom_def tOp_mHom_def)
apply (frule_tac f = m and m = ma in mHom_mem [of "R" "M" "N"], assumption+)
 apply (simp add:sprod_distrib1)
apply (rule conjI)
 apply (rule mHom_eq, assumption+)
 apply (rule sprod_mHom_closed, assumption+)
 apply (rule tOp_mHom_closed, assumption+)
 apply (rule tOp_mHom_closed, assumption+)
 apply (rule sprod_mHom_closed, assumption+)
 apply (rule ballI)
 apply (simp add:sprod_mHom_def tOp_mHom_def)
 apply (frule_tac f = m and m = ma in mHom_mem [of "R" "M" "N"], assumption+)
 apply (frule_tac f = n and m = ma in mHom_mem [of "R" "M" "N"], assumption+)
 apply (simp add:sprod_distrib2)
apply (rule mHom_eq, assumption+)
 apply (rule sprod_mHom_closed, assumption+)
 apply (simp add:ring_one) apply assumption+
 apply (rule ballI)
 apply (simp add:sprod_mHom_def)
 apply (frule_tac f = m and m = ma in mHom_mem [of "R" "M" "N"], assumption+)
apply (simp add:one_module_id)
done

section "2. injective hom, surjective hom, bijective hom and iverse hom"

constdefs
 invmfun :: "[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
              ('c, 'b, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'c] \<Rightarrow> 'c \<Rightarrow> 'a"
 "invmfun R M N (f :: 'a \<Rightarrow> 'c) ==
                    \<lambda>y\<in>(carrier N). \<some> x. (x \<in> (carrier M) \<and> f x = y)"

 misomorphic :: "[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
              ('c, 'b, 'm2) ModuleType_scheme] \<Rightarrow> bool"
 "misomorphic R M N == \<exists>f. f \<in> mHom R M N \<and> bijec\<^sub>M\<^sub>,\<^sub>N f"

 mId :: "('a, 'b, 'm1) ModuleType_scheme \<Rightarrow> 'a \<Rightarrow> 'a"   ("(mId\<^sub>_/ )" [89]88)
 "mId\<^sub>M  == \<lambda>m\<in>carrier M. m"

 mcompose::"[('a, 'r, 'm1) ModuleType_scheme, 'b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow>
                                                                 'a \<Rightarrow> 'c"
 "mcompose M g f == compose (carrier M) g f"

syntax
 "@MISOM" ::"[('a, 'b, 'm1) ModuleType_scheme, ('b, 'm) RingType_scheme,
              ('c, 'b, 'm2) ModuleType_scheme] \<Rightarrow> bool"
             ("(3_ \<cong>\<^sub>_ _)" [82,82,83]82)
translations
 "M \<cong>\<^sub>R N" == "misomorphic R M N"

lemma minjec_inj:"\<lbrakk>ring R; R module M; R module N; injec\<^sub>M\<^sub>,\<^sub>N f\<rbrakk> \<Longrightarrow>
                            inj_on f (carrier M)"
apply (simp add:inj_on_def) apply (rule ballI)+ apply (rule impI)
apply (subgoal_tac "f (x +\<^sub>M (-\<^sub>M y)) = 0\<^sub>N")
apply (simp add:injec_def) apply (erule conjE)
apply (subgoal_tac "x +\<^sub>M (-\<^sub>M y) \<in> ker\<^sub>M\<^sub>,\<^sub>N f") apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = y in ag_mOp_closed [of "M"], assumption+)
 apply (subgoal_tac "x +\<^sub>M -\<^sub>M y +\<^sub>M y = 0\<^sub>M +\<^sub>M y") prefer 2 apply simp
 apply (frule_tac x = x and y = "-\<^sub>M y" and z = y in ag_pOp_assoc [of "M"],
                                                         assumption+)
 apply (simp add:ag_l_inv1) apply (simp add:ag_r_zero ag_l_zero)
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:ker_def)
 apply (frule_tac x = y in ag_mOp_closed [of "M"], assumption+)
 apply (frule_tac x = x and y = "-\<^sub>M y" in ag_pOp_closed [of "M"],
                                                         assumption+)
 apply blast
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule_tac x = y in ag_mOp_closed [of "M"], assumption+)
 apply (simp add:injec_def) apply (erule conjE)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:aHom_add)
 apply (subst aHom_inv_inv [of "M" "N" "f"], assumption+)
 apply (rule ag_r_inv1, assumption+)
 apply (simp add:aHom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
done

lemma invmfun_l_inv:"\<lbrakk>ring R; R module M; R module N; bijec\<^sub>M\<^sub>,\<^sub>N f;
      m \<in> carrier M\<rbrakk> \<Longrightarrow> (invmfun R M N f) (f m) = m"
apply (simp add:bijec_def) apply (erule conjE)
apply (frule minjec_inj [of "R" "M" "N" "f"], assumption+)
apply (simp add:surjec_def) apply (erule conjE) apply (simp add:aHom_def)
apply (frule conj_1)
apply (thin_tac "f \<in> carrier M \<rightarrow> carrier N \<and>
       f \<in> extensional (carrier M) \<and>
       (\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f ( a +\<^sub>M b) =  f a +\<^sub>N (f b))")
apply (frule invfun_l [of "f" "carrier M" "carrier N" "m"], assumption+)
 apply (simp add:surj_to_def)
apply (simp add:invfun_def invmfun_def)
done

lemma invmfun_mHom:"\<lbrakk>ring R; R module M; R module N; bijec\<^sub>M\<^sub>,\<^sub>N f;
                 f \<in> mHom R M N \<rbrakk> \<Longrightarrow> invmfun R M N f \<in> mHom R N M"
apply (frule minjec_inj [of "R" "M" "N" "f"], assumption+)
apply (simp add:bijec_def)
apply (subgoal_tac "surjec\<^sub>M\<^sub>,\<^sub>N f") prefer 2 apply (simp add:bijec_def)
apply (rule mHom_test, assumption+)
apply (rule conjI)
 apply (simp add:surjec_def) apply (erule conjE)
 apply (simp add:aHom_def) apply (frule conj_1)
 apply (thin_tac "f \<in> carrier M \<rightarrow> carrier N \<and> f \<in> extensional (carrier M) \<and>
       (\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f ( a +\<^sub>M b) =  f a +\<^sub>N (f b))")
 apply (frule inv_func [of "f" "carrier M" "carrier N"], assumption+)
 apply (simp add:invmfun_def invfun_def)
apply (rule conjI)
 apply (simp add:invmfun_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:surjec_def)
 apply (erule conjE) apply (simp add:surj_to_def)
 apply (subgoal_tac "m \<in> f ` carrier M")
 apply (subgoal_tac "n \<in> f ` carrier M")
 prefer 2 apply simp prefer 2 apply simp
 apply (thin_tac "f ` carrier M = carrier N") apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier M. \<forall>y\<in>carrier M. m = f x \<and> n = f y \<longrightarrow>
 invmfun R M N f ( m +\<^sub>N n) = invmfun R M N f m +\<^sub>M (invmfun R M N f n)")
 apply blast apply (thin_tac "\<exists>x\<in>carrier M. m = f x")
 apply (thin_tac "\<exists>x\<in>carrier M. n = f x")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (frule_tac m1 = x and n1 = y in mHom_add [THEN sym, of "R" "M" "N" "f"],
                                                             assumption+)
 apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = x and y = y in ag_pOp_closed [of "M"], assumption+)
 apply (simp add:invmfun_l_inv)
apply (rule ballI)+
 apply (simp add:surjec_def)
 apply (erule conjE)
 apply (subgoal_tac "m \<in> f ` (carrier M)") prefer 2
 apply (simp add:surj_to_def)
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier M. m = f x \<longrightarrow>
                     invmfun R M N f ( a \<star>\<^sub>N m) =  a \<star>\<^sub>M (invmfun R M N f m)")
 apply blast apply (thin_tac "\<exists>x\<in>carrier M. m = f x")
apply (rule ballI) apply (rule impI) apply simp
apply (frule_tac m1 = x and a1 = a in mHom_lin [THEN sym, of "R" "M" "N" _ "f"], assumption+) apply simp
 apply (frule_tac a = a and m = x in sprod_mem [of "R" "M"], assumption+)
 apply (simp add:invmfun_l_inv)
done

lemma mHom_compos:"\<lbrakk>ring R; R module L; R module M; R module N;
 f \<in> mHom R L M; g \<in> mHom R M N \<rbrakk> \<Longrightarrow> compos L g f \<in> mHom R L N"
apply (simp add:mHom_def [of "R" "L" "N"])
apply (frule module_is_ag [of "R" "L"], assumption+)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (rule conjI) apply (simp add:mHom_def) apply (erule conjE)+
 apply (simp add:aHom_compos)
apply (rule ballI)+
apply (simp add:compos_def compose_def)
 apply (simp add:sprod_mem)
 apply (subst mHom_lin[of "R" "L" "M" _ "f"], assumption+)
 apply (subst mHom_lin [of "R" "M" "N" _ "g"], assumption+)
 apply (simp add:mHom_def) apply (erule conjE)+
 apply (simp add:aHom_mem) apply assumption+
 apply simp
done

lemma mcompos_inj_inj:"\<lbrakk>ring R; R module L; R module M; R module N;
f \<in> mHom R L M; g \<in> mHom R M N; injec\<^sub>L\<^sub>,\<^sub>M f; injec\<^sub>M\<^sub>,\<^sub>N g \<rbrakk> \<Longrightarrow> injec\<^sub>L\<^sub>,\<^sub>N (compos L g f)"
apply (frule module_is_ag [of "R" "L"], assumption+)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:injec_def [of "L" "N"])
apply (rule conjI)
 apply (simp add:injec_def) apply (erule conjE)+
 apply (simp add:aHom_compos)
apply (simp add:ker_def)
 apply (simp add:compos_def compose_def)
 apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (erule conjE) apply simp
 apply (simp add:injec_def [of _ _ "g"])
 apply (erule conjE) apply (simp add:ker_def)
 apply (subgoal_tac "f x \<in> {a. a \<in> carrier M \<and> g a = 0\<^sub>N}")
 apply simp
 apply (simp add:injec_def [of _ _ "f"])
 apply (erule conjE) apply (subgoal_tac "x \<in> ker\<^sub>L\<^sub>,\<^sub>M f")
 apply simp apply (thin_tac "ker\<^sub>L\<^sub>,\<^sub>M f = {0\<^sub>L}")
 apply (simp add:ker_def)
 apply (thin_tac "{a. a \<in> carrier M \<and> g a = 0\<^sub>N} = {0\<^sub>M}")
 apply (simp add:CollectI) apply (simp add:mHom_mem)
apply (rule subsetI) apply (simp add:CollectI)
 apply (frule module_inc_zero [of "R" "L"], assumption+) apply simp
 apply (simp add:mHom_0)
done

lemma mcompos_surj_surj:"\<lbrakk>ring R; R module L; R module M; R module N;
surjec\<^sub>L\<^sub>,\<^sub>M f; surjec\<^sub>M\<^sub>,\<^sub>N g; f \<in> mHom R L M; g \<in> mHom R M N \<rbrakk> \<Longrightarrow>
                                        surjec\<^sub>L\<^sub>,\<^sub>N (compos L g f)"
apply (frule module_is_ag [of "R" "L"], assumption+)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply (simp add:surjec_def [of "L" "N"])
apply (rule conjI)
 apply (simp add:mHom_def) apply (erule conjE)+
 apply (rule aHom_compos, assumption+)
apply (rule surj_to_test)
 apply (frule mHom_compos [of "R" "L" "M" "N" "f" "g"], assumption+)
 apply (simp add:mHom_def aHom_def)
apply (rule ballI)
 apply (simp add: compos_def compose_def)
 apply (simp add:surjec_def [of _ _ "g"])
 apply (erule conjE) apply (simp add:surj_to_def)
 apply (subgoal_tac "b \<in> g ` carrier M")
 apply (thin_tac "g ` carrier M = carrier N") apply (thin_tac "b \<in> carrier N")
 apply (simp add:image_def)
 apply auto
  apply (simp add:surjec_def [of _ _ "f"])
 apply (erule conjE) apply (simp add:surj_to_def)
 apply (subgoal_tac "x \<in> f ` carrier L")
 apply (thin_tac "f ` carrier L = carrier M") apply (simp add:image_def)
apply auto
done

lemma mId_mHom:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> mId\<^sub>M \<in> mHom R M M"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mId_def)
apply (simp add:mId_def extensional_def)
apply (rule ballI)+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:ag_pOp_closed)
apply (rule ballI)+
 apply (simp add:mId_def)
 apply (simp add:sprod_mem)
done

lemma mHom_mId_bijec:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N; g \<in> mHom R N M; compose (carrier M) g f = mId\<^sub>M; compose (carrier N) f g = mId\<^sub>N\<rbrakk> \<Longrightarrow>
 bijec\<^sub>M\<^sub>,\<^sub>N f"
apply (simp add:bijec_def)
apply (rule conjI)
apply (simp add:injec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (simp add:ker_def)
 apply (rule equalityI)
 apply (rule subsetI) apply simp
 apply (subgoal_tac "(compose (carrier M) g f) x = (mId\<^sub>M) x")
 prefer 2 apply simp
 apply (thin_tac "compose (carrier M) g f = mId\<^sub>M")
 apply (erule conjE)
 apply (simp add:compose_def mId_def)
 apply (simp add:mHom_0)
 apply (rule subsetI) apply (simp add:ker_def)
 apply (simp add:module_inc_zero) apply (simp add:mHom_0)
apply (thin_tac "compose (carrier M) g f = mId\<^sub>M")
 apply (simp add:surjec_def)
 apply (rule conjI) apply (simp add:mHom_def)
 apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
 apply (rule ballI)
 apply (subgoal_tac "(compose (carrier N) f g) b = (mId\<^sub>N) b")
 prefer 2 apply simp
 apply (thin_tac "compose (carrier N) f g = mId\<^sub>N")
 apply (simp add:compose_def mId_def)
 apply (frule_tac m = b in mHom_mem [of "R" "N" "M" "g"], assumption+)
 apply blast
done

constdefs
 sup_sharp::"[('r, 'n) RingType_scheme, ('b, 'r, 'm1) ModuleType_scheme,
 ('c, 'r, 'm2) ModuleType_scheme, ('a, 'r, 'm) ModuleType_scheme, 'b \<Rightarrow> 'c]
 \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'a)"
 "sup_sharp R M N L u == \<lambda>f\<in>mHom R N L. compos M f u"

 sub_sharp::"[('r, 'n) RingType_scheme, ('a, 'r, 'm) ModuleType_scheme,
 ('b, 'r, 'm1) ModuleType_scheme, ('c, 'r, 'm2) ModuleType_scheme, 'b \<Rightarrow> 'c]
 \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
 "sub_sharp R L M N u == \<lambda>f\<in>mHom R L M. compos L u f"

       (*  L
          f| u
           M \<rightarrow> N,  f \<rightarrow> u o f   *)

lemma sup_sharp_homTr:"\<lbrakk>ring R; R module M; R module N; R module L;
 u \<in> mHom R M N; f \<in> mHom R N L \<rbrakk> \<Longrightarrow> sup_sharp R M N L u f \<in> mHom R M L"
apply (simp add:sup_sharp_def)
apply (simp add:mHom_compos)
done

lemma sup_sharp_hom:"\<lbrakk>ring R; R module M; R module N; R module L;
 u \<in> mHom R M N \<rbrakk> \<Longrightarrow> sup_sharp R M N L u \<in> mHom R (HOM\<^sub>R N L) (HOM\<^sub>R M L)"
apply (simp add:mHom_def [of "R" "HOM\<^sub>R N L"])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:HOM_def)
 apply (simp add:sup_sharp_def)
 apply (simp add:mHom_compos)
apply (rule conjI)
 apply (simp add:sup_sharp_def extensional_def)
 apply (rule allI) apply (rule impI) apply (simp add:HOM_def)
apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac f = a and g = b in tOp_mHom_closed [of "R" "N" "L"],
                                                              assumption+)
 apply (frule_tac f = a in sup_sharp_homTr [of "R" "M" "N" "L" "u"],
                                                              assumption+)
 apply (frule_tac f = b in sup_sharp_homTr [of "R" "M" "N" "L" "u"],
                                                              assumption+)
  apply (frule_tac f = "sup_sharp R M N L u a" and
  g = "sup_sharp R M N L u b" in tOp_mHom_closed [of "R" "M" "L"],
                                                              assumption+)
 apply (frule_tac f = "tOp_mHom R N L a b" in sup_sharp_homTr [of "R" "M" "N" "L" "u"], assumption+)
 apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:sup_sharp_def tOp_mHom_def compose_def compos_def)
 apply (simp add:mHom_mem)
apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac a = a and f = m in sprod_mHom_closed [of "R" "N" "L"],
                                                                assumption+)
 apply (frule_tac f = "sprod_mHom R N L a m" in
                        sup_sharp_homTr [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac f = m in
                        sup_sharp_homTr [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac a = a and f = "sup_sharp R M N L u m" in sprod_mHom_closed [of "R" "M" "L"], assumption+)
 apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:sprod_mHom_def sup_sharp_def compose_def compos_def)
apply (simp add:mHom_mem)
done

lemma sub_sharp_homTr:"\<lbrakk>ring R; R module M; R module N; R module L;
 u \<in> mHom R M N; f \<in> mHom R L M\<rbrakk> \<Longrightarrow> sub_sharp R L M N u f \<in> mHom R L N"
apply (simp add:sub_sharp_def)
apply (simp add:mHom_compos)
done

lemma sub_sharp_hom:"\<lbrakk>ring R; R module M; R module N; R module L;
 u \<in> mHom R M N\<rbrakk> \<Longrightarrow> sub_sharp R L M N u \<in> mHom R (HOM\<^sub>R L M) (HOM\<^sub>R L N)"
apply (simp add:mHom_def [of _ "HOM\<^sub>R L M"])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:HOM_def)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:sub_sharp_def) apply (simp add:mHom_compos)
apply (rule conjI)
 apply (simp add:sub_sharp_def extensional_def)
 apply (simp add:HOM_def)
apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac f = a and g = b in tOp_mHom_closed [of "R" "L" "M"],
                                                              assumption+)
 apply (frule_tac f = "tOp_mHom R L M a b" in sub_sharp_homTr
                                 [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac f = b in sub_sharp_homTr
                                 [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac f = a in sub_sharp_homTr
                                 [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac f = "sub_sharp R L M N u a" and
  g = "sub_sharp R L M N u b" in tOp_mHom_closed [of "R" "L" "N"],
                                                              assumption+)
apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:tOp_mHom_def sub_sharp_def mcompose_def compose_def)
 apply (simp add:compos_def compose_def)
 apply (rule mHom_add [of "R" "M"], assumption+)
 apply (simp add:mHom_mem)
 apply (simp add:mHom_mem)
apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac a = a and f = m in sprod_mHom_closed [of "R" "L" "M"],
                                                         assumption+)
 apply (frule_tac f = "sprod_mHom R L M a m" in sub_sharp_homTr
                                 [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac f = m in sub_sharp_homTr
                                 [of "R" "M" "N" "L" "u"], assumption+)
 apply (frule_tac a = a and f = "sub_sharp R L M N u m" in
                       sprod_mHom_closed [of "R" "L" "N"], assumption+)
apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:sprod_mHom_def sub_sharp_def mcompose_def compose_def)
 apply (frule_tac  f = m and m = ma in mHom_mem [of "R" "L" "M"], assumption+)
apply (simp add:compos_def compose_def)
apply (simp add:mHom_lin)
done

lemma mId_bijec:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> bijec\<^sub>M\<^sub>,\<^sub>M (mId\<^sub>M)"
apply (simp add:bijec_def)
apply (frule mId_mHom [of "R" "M"], assumption+)
apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule conjI) apply (simp add:mHom_def)
 apply (simp add:ker_def) apply (simp add:mId_def)
 apply (rule equalityI) apply (rule subsetI) apply (simp add:CollectI)
 apply (rule subsetI) apply (simp add:CollectI)
  apply (simp add:module_inc_zero)
apply (simp add:surjec_def)
 apply (simp add:mHom_def)
 apply (thin_tac "mId\<^sub>M  \<in> aHom M M \<and>
       (\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. (mId\<^sub>M ) ( a \<star>\<^sub>M m) =  a \<star>\<^sub>M ((mId\<^sub>M ) m))")
 apply (rule surj_to_test)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mId_def)
 apply (rule ballI)
 apply (simp add:mId_def)
done

lemma invmfun_bijec:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
  bijec\<^sub>M\<^sub>,\<^sub>N f\<rbrakk> \<Longrightarrow>  bijec\<^sub>N\<^sub>,\<^sub>M (invmfun R M N f)"
apply (frule invmfun_mHom [of "R" "M" "N" "f"], assumption+)
apply (simp add:bijec_def [of "N" "M"])
apply (rule conjI)
apply (simp add:injec_def)
 apply (simp add:mHom_def [of "R" "N" "M"]) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier R.
       \<forall>m\<in>carrier N. invmfun R M N f ( a \<star>\<^sub>N m) = a \<star>\<^sub>M (invmfun R M N f m)")
 apply (rule equalityI) apply (rule subsetI) apply (simp add:ker_def CollectI)
 apply (erule conjE)
 apply (subgoal_tac "surjec\<^sub>M\<^sub>,\<^sub>N f") prefer 2 apply (simp add:bijec_def)
 apply (simp add:surjec_def) apply (erule conjE)+ apply (simp add:surj_to_def)
 apply (subgoal_tac "x \<in> f ` carrier M") prefer 2 apply simp
 apply (thin_tac "f ` carrier M = carrier N") apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>carrier M. x = f xa \<longrightarrow> x = 0\<^sub>N")
 apply blast apply (thin_tac "\<exists>xa\<in>carrier M. x = f xa")
 apply (rule ballI) apply (rule impI)
 apply simp
 apply (simp add:invmfun_l_inv) apply (simp add:mHom_0)
 apply (rule subsetI) apply simp
 apply (simp add:ker_def) apply (simp add:module_inc_zero)
 apply (subst mHom_0 [THEN sym, of "R" "M" "N" "f"], assumption+)
 apply (subst invmfun_l_inv, assumption+) apply (simp add:module_inc_zero)
 apply simp
apply (simp add:surjec_def)
 apply (rule conjI) apply (simp add:mHom_def)
 apply (rule surj_to_test)
 apply (simp add:mHom_def [of "R" "N" "M"] aHom_def)
 apply (rule ballI)
 apply (frule_tac m = b in mHom_mem [of "R" "M" "N" "f"], assumption+)
 apply (frule_tac m = b in invmfun_l_inv [of "R" "M" "N" "f"], assumption+)
 apply blast
done

lemma misom_self:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> M \<cong>\<^sub>R M"
apply (frule_tac mId_bijec [of "R" "M"], assumption+)
apply (frule mId_mHom [of "R" "M"], assumption+)
apply (simp add:misomorphic_def)
apply auto
done

lemma misom_sym:"\<lbrakk>ring R; R module M; R module N; M \<cong>\<^sub>R N \<rbrakk> \<Longrightarrow> N \<cong>\<^sub>R M"
apply (simp add:misomorphic_def [of "R" "M" "N"])
apply auto
apply (frule_tac f = f in invmfun_mHom [of "R" "M" "N"], assumption+)
apply (frule_tac f = f in invmfun_bijec [of "R" "M" "N"], assumption+)
apply (simp add:misomorphic_def)
apply auto
done

lemma misom_trans:"\<lbrakk>ring R; R module L; R module M; R module N; L \<cong>\<^sub>R M;
M \<cong>\<^sub>R N\<rbrakk> \<Longrightarrow> L \<cong>\<^sub>R N"
apply (simp add:misomorphic_def)
apply (subgoal_tac "\<forall>f. \<forall>g. f \<in> mHom R L M \<and> bijec\<^sub>L\<^sub>,\<^sub>M f \<and> g \<in> mHom R M N \<and>
 bijec\<^sub>M\<^sub>,\<^sub>N g \<longrightarrow> (\<exists>f. f \<in> mHom R L N \<and> bijec\<^sub>L\<^sub>,\<^sub>N f)")
apply blast
 apply (thin_tac "\<exists>f. f \<in> mHom R L M \<and> bijec\<^sub>L\<^sub>,\<^sub>M f")
 apply (thin_tac "\<exists>f. f \<in> mHom R M N \<and> bijec\<^sub>M\<^sub>,\<^sub>N f")
 apply (rule allI)+
 apply (rule impI) apply (erule conjE)+
apply (subgoal_tac  "bijec\<^sub>L\<^sub>,\<^sub>N (compos L g f)")
apply (subgoal_tac "(compos L g f) \<in> mHom R L N")
 apply blast
 apply (simp add:bijec_def ) apply (erule conjE)+
apply (simp add:mHom_compos)
apply (simp add:bijec_def) apply (erule conjE)+
apply (simp add:mcompos_inj_inj)
apply (simp add:mcompos_surj_surj)
done

constdefs
 mr_coset :: "['a, ('a, 'b, 'more) ModuleType_scheme, 'a set] \<Rightarrow> 'a set"
     "mr_coset a M H == a \<uplus>\<^sub>M H"

constdefs
 set_mr_cos:: "[('a, 'b, 'more) ModuleType_scheme, 'a set] \<Rightarrow> 'a set set"
  "set_mr_cos M H == {X. \<exists>a\<in>carrier M. X = a \<uplus>\<^sub>M H}"

constdefs
 mr_cos_sprod ::"[('a, 'b, 'more) ModuleType_scheme, 'a set] \<Rightarrow>
                                              'b \<Rightarrow> 'a set \<Rightarrow> 'a set"
 "mr_cos_sprod M H a X == {z. \<exists>x\<in>X. \<exists>h\<in>H. z = h +\<^sub>M (a \<star>\<^sub>M x)}"

constdefs
 mr_cospOp ::"[('a, 'b, 'more) ModuleType_scheme, 'a set] \<Rightarrow>
                                               'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
 "mr_cospOp M H ==  \<lambda>X. \<lambda>Y. costOp (b_ag M) H X Y"

 mr_cosmOp ::"[('a, 'b, 'more) ModuleType_scheme, 'a set] \<Rightarrow>
                                                  'a set \<Rightarrow> 'a set"
 "mr_cosmOp M H == \<lambda>X. cosiOp (b_ag M) H X"

constdefs
 qmodule :: "[('a, 'r, 'more) ModuleType_scheme, 'a set] \<Rightarrow>
                 ('a set, 'r) ModuleType"
 "qmodule M H == \<lparr> carrier = set_mr_cos M H, pOp = mr_cospOp M H,
  mOp = mr_cosmOp M H, zero = H, sprod = mr_cos_sprod M H\<rparr>"

 sub_mr_set_cos:: "[('a, 'r, 'more) ModuleType_scheme, 'a set, 'a set] \<Rightarrow>
                            'a set set"
 "sub_mr_set_cos M H N == {X. \<exists>n\<in>N. X = n \<uplus>\<^sub>M H}"
 (* N/H, where N is a submodule *)

syntax
  "@QMODULE" :: "[('a, 'r, 'more) ModuleType_scheme, 'a set] \<Rightarrow>
                 ('a set, 'r) ModuleType"
              (infixl "'/'\<^sub>m" 200)
syntax
  "@SUBMRSET" ::"['a set, ('a, 'r, 'more) ModuleType_scheme, 'a set] \<Rightarrow>
                            'a set set"
             ("(3_/ \<^sub>s'/'\<^sub>_/ _)" [82,82,83]82)
translations
  "M /\<^sub>m H" == "qmodule M H"
  "N \<^sub>s/\<^sub>M H" == "sub_mr_set_cos M H N"

lemma qmodule_carr:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
            carrier (qmodule M H) = set_mr_cos M H"
apply (simp add:qmodule_def)
done

lemma set_mr_cos_mem:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                        m \<uplus>\<^sub>M H \<in> set_mr_cos M H"
apply (simp add:set_mr_cos_def)
apply blast
done


lemma m_in_mr_coset:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
             m \<in> m \<uplus>\<^sub>M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule b_ag_group)
apply (simp add:ar_coset_def)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:asubgroup_def)
apply (rule aInR_cos [of "b_ag M" "H" "m"], assumption+)
done

lemma mr_cos_h_stable:"\<lbrakk>ring R; R module M; submodule R M H; h \<in> H\<rbrakk> \<Longrightarrow>
                                                           H = h \<uplus>\<^sub>M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule b_ag_group [of "M"])
apply (simp add:ar_coset_def)
apply (rule r_cosUnit1_1 [THEN sym], assumption+)
apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:asubgroup_def) apply assumption
done

lemma mr_cos_h_stable1:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M;
h \<in> H\<rbrakk> \<Longrightarrow> (m +\<^sub>M h) \<uplus>\<^sub>M H = m \<uplus>\<^sub>M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (subst ag_pOp_commute [of "M"], assumption+)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:subsetD)
apply (frule b_ag_group [of "M"])
apply (simp add:ar_coset_def)
apply (simp add:agop_gop [THEN sym])
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:asubgroup_def)
apply (rule r_coset_fixed1 [THEN sym, of "b_ag M" "H" "m" "h"], assumption+)
done

lemma x_in_mr_coset:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M;
           x \<in> m \<uplus>\<^sub>M H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. m +\<^sub>M h = x"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (subgoal_tac "\<exists>h\<in>H. h +\<^sub>M m = x")
 apply (subgoal_tac "\<forall>h\<in>H. h +\<^sub>M m = x \<longrightarrow> (\<exists>h\<in>H.  m +\<^sub>M h = x)")
 apply blast apply (thin_tac "\<exists>h\<in>H.  h +\<^sub>M m = x")
 apply (rule ballI) apply (rule impI)
 apply (frule submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (simp add:ag_pOp_commute [of "M" _ "m"])
apply blast
apply (simp add:ar_coset_def)
apply (frule b_ag_group)
apply (simp add:agop_gop [THEN sym])
apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:asubgroup_def)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:r_cosTool2)
done

lemma mr_cos_sprodTr:"\<lbrakk>ring R; R module M; submodule R M H; a \<in> carrier R;
 m \<in> carrier M\<rbrakk> \<Longrightarrow>
 mr_cos_sprod M H a (m \<uplus>\<^sub>M H) = (a \<star>\<^sub>M m) \<uplus>\<^sub>M H"
apply (simp add:mr_cos_sprod_def)
apply (simp add:ar_coset_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule b_ag_group)
apply (simp add:submodule_def) apply (erule conjE)+
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>xa\<in>H\<^sub>(b_ag M) m. \<forall>h\<in>H. x = h +\<^sub>M  a \<star>\<^sub>M xa \<longrightarrow>
                            x \<in> H\<^sub>(b_ag M) ( a \<star>\<^sub>M m)")
 apply blast
 apply (thin_tac "\<exists>xa\<in>H\<^sub>(b_ag M) m. \<exists>h\<in>H. x =  h +\<^sub>M  a \<star>\<^sub>M xa")
 apply (rule ballI)+ apply (rule impI)
 apply (frule_tac x = xa in r_cosTool2 [of "b_ag M" "H" "m"])
 apply (simp add:asubgroup_def)
 apply (simp add:ag_carrier_carrier) apply assumption
 apply (subgoal_tac "\<forall>h\<in>H. GroupType.tOp (b_ag M) h m = xa \<longrightarrow> x \<in> H\<^sub>(b_ag M) ( a \<star>\<^sub>M m)")
 apply blast apply (thin_tac "\<exists>h\<in>H.  GroupType.tOp (b_ag M) h m = xa")
 apply (rule ballI) apply (rule impI)
 apply (simp add:agop_gop) apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "ha +\<^sub>M m = xa") apply simp
 apply (frule_tac c = ha in subsetD [of "H" "carrier M"], assumption+)
 apply (frule_tac m = ha and n = m in sprod_distrib2 [of "R" "M" "a"],
                                                             assumption+)
 apply simp
 apply (thin_tac "a \<star>\<^sub>M ( ha +\<^sub>M m) = a \<star>\<^sub>M ha +\<^sub>M  a \<star>\<^sub>M m")
 apply (frule_tac m = ha in sprod_mem [of "R" "M" "a"], assumption+)
 apply (frule_tac m = m in sprod_mem [of "R" "M" "a"], assumption+)
 apply (frule_tac c = h in subsetD [of "H" "carrier M"], assumption+)
 apply (subst ag_pOp_assoc [THEN sym], assumption+)
 apply (subgoal_tac "a \<star>\<^sub>M ha \<in> H") prefer 2 apply simp
 apply (frule_tac h = h and k = "a \<star>\<^sub>M ha" in
                    submodule_pOp_closed [of "R" "M" "H"], assumption+)
apply (simp add:submodule_def) apply assumption+
 apply (simp add:agop_gop [THEN sym])
 apply (simp add:asubgroup_def)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (frule_tac a = "a \<star>\<^sub>M m" and h = "GroupType.tOp (b_ag M) h (a \<star>\<^sub>M ha)"
  in  r_coset_fixed1 [of "b_ag M" "H"], assumption+)
 apply simp
 apply (simp add:aInR_cos)
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (simp add:asubgroup_def)
 apply (frule_tac m = m in sprod_mem [of "R" "M" "a"], assumption+)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (frule_tac x = x in r_cosTool2 [of "b_ag M" "H" "a \<star>\<^sub>M m"], assumption+)
 apply (simp add:agop_gop [THEN sym])
 apply (frule_tac aInR_cos [of "b_ag M" "H" "m"], assumption+)
apply blast
done

lemma mr_cos_sprod_mem:"\<lbrakk>ring R; R module M; submodule R M H;
 a \<in> carrier R; X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow> mr_cos_sprod M H a X \<in> set_mr_cos M H"
apply (subgoal_tac "\<exists>a\<in>carrier M. X = (a \<uplus>\<^sub>M H)")
prefer 2  apply (simp add:set_mr_cos_def)
apply auto apply (rename_tac m)
 apply (subst mr_cos_sprodTr, assumption+)
 apply (frule_tac m = m in sprod_mem [of "R" "M" "a"], assumption+)
apply (simp add:set_mr_cos_def)
apply blast
done

lemma mr_cos_sprod_assoc:"\<lbrakk>ring R; R module M; submodule R M H; a \<in> carrier R;
 b \<in> carrier R; X \<in> set_mr_cos M H \<rbrakk> \<Longrightarrow> mr_cos_sprod  M H (a \<cdot>\<^sub>R b) X =
                           mr_cos_sprod M H a (mr_cos_sprod M H b X)"
apply (subgoal_tac "\<exists>a\<in>carrier M. X = (a \<uplus>\<^sub>M H)")
prefer 2 apply (simp add:set_mr_cos_def)
apply (subgoal_tac "\<forall>m\<in>carrier M. X = m \<uplus>\<^sub>M H \<longrightarrow>
 mr_cos_sprod M H (a \<cdot>\<^sub>R b) X = mr_cos_sprod M H a (mr_cos_sprod M H b X)")
apply blast apply (thin_tac "\<exists>a\<in>carrier M. X = a \<uplus>\<^sub>M H")
apply (rule ballI) apply (rule impI) apply simp
 apply (frule_tac m = m in sprod_mem [of "R" "M" "b"], assumption+)
 apply (frule ring_tOp_closed [of "R" "a" "b"], assumption+)
 apply (subst mr_cos_sprodTr, assumption+)+
 apply (simp add: sprod_assoc [of "R" "M" "a" "b"])
done

lemma mr_cos_sprod_one:"\<lbrakk>ring R; R module M; submodule R M H;
 X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow> mr_cos_sprod M H (1\<^sub>R) X = X"
apply (subgoal_tac "\<exists>a\<in>carrier M. X = (a \<uplus>\<^sub>M H)")
prefer 2  apply (simp add:set_mr_cos_def)apply (subgoal_tac "\<forall>m\<in>carrier M. X = m \<uplus>\<^sub>M H \<longrightarrow>  mr_cos_sprod M H  (1\<^sub>R) X = X")
apply blast apply (thin_tac "\<exists>a\<in>carrier M. X = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI) apply simp
 apply (frule ring_one[of "R"])
 apply (subst mr_cos_sprodTr, assumption+)
 apply (simp add:one_module_id)
done

lemma mr_cospOpTr:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M;
 n \<in> carrier M\<rbrakk> \<Longrightarrow> mr_cospOp M H (m \<uplus>\<^sub>M H) (n \<uplus>\<^sub>M H) = (m +\<^sub>M n) \<uplus>\<^sub>M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule b_ag_group)
apply (simp add:mr_cospOp_def mr_coset_def agop_gop [THEN sym])
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:submodule_def) apply (erule conjE)+
apply (frule asubg_nsubg, assumption+) apply (simp add:ar_coset_def)
apply (rule costOpwelldef [THEN sym, of "b_ag M" "H" "m" "n"], assumption+)
done

lemma mr_cos_sprod_distrib1:"\<lbrakk>ring R; R module M; submodule R M H;
 a \<in> carrier R; b \<in> carrier R;  X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow>
 mr_cos_sprod M H (a +\<^sub>R b) X =
           mr_cospOp M H (mr_cos_sprod M H a X) (mr_cos_sprod M H b X)"
apply (subgoal_tac "\<exists>m\<in>carrier M. X = (m \<uplus>\<^sub>M H)")
prefer 2 apply (simp add:set_mr_cos_def)
apply (subgoal_tac "\<forall>m\<in>carrier M. X = m \<uplus>\<^sub>M H \<longrightarrow> mr_cos_sprod M H ( a +\<^sub>R b) X = mr_cospOp M H (mr_cos_sprod M H a X) (mr_cos_sprod M H b X)")
apply blast apply (thin_tac "\<exists>m\<in>carrier M. X = m \<uplus>\<^sub>M H")
apply (rule ballI) apply (rule impI)
 apply simp
 apply (frule ring_is_ag)
 apply (frule ag_pOp_closed [of "R" "a" "b"], assumption+)
apply (subst mr_cos_sprodTr [of "R" "M" "H"], assumption+)+
apply (subst mr_cospOpTr, assumption+)
 apply (simp add:sprod_mem)
 apply (simp add:sprod_mem)
 apply (simp add:sprod_distrib1)
done

lemma mr_cos_sprod_distrib2:"\<lbrakk>ring R; R module M; submodule R M H;
 a \<in> carrier R; X \<in> set_mr_cos M H; Y \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow>
 mr_cos_sprod M H a (mr_cospOp M H X Y) =
           mr_cospOp M H (mr_cos_sprod M H a X) (mr_cos_sprod M H a Y)"
apply (subgoal_tac "\<exists>m\<in>carrier M. X = (m \<uplus>\<^sub>M H)")
 prefer 2 apply (simp add:set_mr_cos_def)
apply (subgoal_tac "\<exists>n\<in>carrier M. Y = (n \<uplus>\<^sub>M H)")
 prefer 2 apply (simp add:set_mr_cos_def)
apply (subgoal_tac "\<forall>m\<in>carrier M. \<forall>n\<in>carrier M. X = m \<uplus>\<^sub>M H \<and> Y = n \<uplus>\<^sub>M H \<longrightarrow>
 mr_cos_sprod M H a (mr_cospOp M H X Y) =
       mr_cospOp M H (mr_cos_sprod M H a X) (mr_cos_sprod M H a Y)")
apply blast
 apply (thin_tac "\<exists>m\<in>carrier M. X = m \<uplus>\<^sub>M H")
 apply (thin_tac "\<exists>n\<in>carrier M. Y = n \<uplus>\<^sub>M H")
apply (simp add: mr_cospOpTr sprod_mem mr_cos_sprodTr module_is_ag ag_pOp_closed sprod_distrib2)
done

lemma mr_cosmOpTr:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                mr_cosmOp M H (m \<uplus>\<^sub>M H) = (-\<^sub>M m) \<uplus>\<^sub>M H"
apply (simp add:ar_coset_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule b_ag_group)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:agiop_giop [THEN sym])
apply (simp add:mr_cosmOp_def)
apply (rule cosiOpwelldef, assumption+)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule asubg_nsubg [of "M" "H"], assumption+)
done

lemma mr_cos_oneTr:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
               H =  (0\<^sub>M) \<uplus>\<^sub>M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule ag_inc_zero [of "M"])
 apply (simp add:ar_coset_def)
 apply (frule b_ag_group)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (subgoal_tac "0\<^sub>M = GroupType.one (b_ag M)") apply simp
 apply (rule r_cosUnit1 [THEN sym, of "b_ag M" "H"], assumption+)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:asubgroup_def)
 apply (simp add:b_ag_def)
done

lemma mr_cos_oneTr1:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                            mr_cospOp M H H (m \<uplus>\<^sub>M H) = m \<uplus>\<^sub>M H"
apply (subgoal_tac "mr_cospOp M H (0\<^sub>M \<uplus>\<^sub>M H) (m \<uplus>\<^sub>M H) = m \<uplus>\<^sub>M H")
apply (simp add:mr_cos_oneTr [THEN sym, of "R" "M" "H"])
apply (subst mr_cospOpTr, assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_inc_zero, assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_l_zero [of "M" "m"], assumption+)
apply simp
done

lemma qmodule_is_ag:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                          agroup (M /\<^sub>m H)"
apply (simp add:agroup_def)
apply (simp add:qmodule_def)
apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (rename_tac X Y)
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. X = a \<uplus>\<^sub>M H \<and> Y = b \<uplus>\<^sub>M H
  \<longrightarrow> (\<exists>a\<in>carrier M. mr_cospOp M H X Y = a \<uplus>\<^sub>M H)")
 apply blast apply (thin_tac "\<exists>a\<in>carrier M. X = a \<uplus>\<^sub>M H")
 apply (thin_tac "\<exists>a\<in>carrier M. Y = a \<uplus>\<^sub>M H")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed [of "M"], assumption+)
 apply (simp add: mr_cospOpTr)
 apply blast
apply (rule conjI)
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. x = a \<uplus>\<^sub>M H \<longrightarrow>
                        (\<exists>a\<in>carrier M. mr_cosmOp M H x = a \<uplus>\<^sub>M H)")
 apply blast
 apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI)
 apply (simp add: mr_cosmOpTr)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = a in ag_mOp_closed [of "M"], assumption+)
 apply blast
apply (rule conjI)
 apply (simp add:set_mr_cos_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule ag_inc_zero [of "M"])
 apply (frule mr_cos_oneTr [of "R" "M" "H"], assumption+)
 apply blast
apply (rule ballI)+
 apply (simp add:set_mr_cos_def)
 apply (rule conjI)
 apply (subgoal_tac "\<forall>a\<in>carrier M.  x = a \<uplus>\<^sub>M H \<longrightarrow>
                                 mr_cospOp M H H x = x")
 apply blast
   apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M H")
   apply (thin_tac "\<exists>b\<in>carrier M. y = b \<uplus>\<^sub>M H")
   apply (thin_tac "\<exists>c\<in>carrier M. z = c \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI) apply simp
 apply (simp add:mr_cos_oneTr1)
 apply (subgoal_tac "\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. \<forall>c\<in>carrier M.
   x = a \<uplus>\<^sub>M H \<and>  y = b \<uplus>\<^sub>M H \<and>  z = c \<uplus>\<^sub>M H \<longrightarrow>
          mr_cospOp M H (mr_cosmOp M H x) x = H \<and>
          mr_cospOp M H (mr_cospOp M H x y) z =
          mr_cospOp M H x (mr_cospOp M H y z) \<and>
          mr_cospOp M H x y = mr_cospOp M H y x")
 apply blast
  apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M H")
  apply (thin_tac "\<exists>b\<in>carrier M. y = b \<uplus>\<^sub>M H")
  apply (thin_tac "\<exists>c\<in>carrier M. z = c \<uplus>\<^sub>M H")
apply (rule ballI)+
 apply (rule impI) apply simp
apply (simp add:mr_cospOpTr)
apply (simp add:mr_cosmOpTr)
apply (thin_tac "x = a \<uplus>\<^sub>M H \<and> y = b \<uplus>\<^sub>M H \<and> z = c \<uplus>\<^sub>M H")
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule_tac x = a in ag_mOp_closed [of "M"], assumption+)
apply (frule_tac x = a and y = b in ag_pOp_closed [of "M"], assumption+)
apply (frule_tac x = b and y = c in ag_pOp_closed [of "M"], assumption+)
apply (simp add:mr_cospOpTr)
apply (simp add:ag_l_inv1)
apply (simp add:mr_cos_oneTr [THEN sym])
apply (simp add:ag_pOp_assoc)
apply (simp add:ag_pOp_commute)
done

lemma qmodule_module:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                                                   R module (M /\<^sub>m H)"
apply (simp add:Module_def [of "R" "M /\<^sub>m H"])
apply (simp add:qmodule_is_ag)
apply (simp add:qmodule_def)
apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:mr_cos_sprod_mem)
apply (rule ballI)+
apply (simp add:mr_cos_sprod_assoc)
apply (simp add:mr_cos_sprod_distrib1)
apply (simp add:mr_cos_sprod_distrib2)
apply (simp add:mr_cos_sprod_one)
done

end
