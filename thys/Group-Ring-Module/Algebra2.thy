(**                Algebra2  
                                  author Hidetsune Kobayashi
                                  Department of Mathematics
                                  Nihon University
                                  hikoba@math.cst.nihon-u.ac.jp
                                  May 3, 2004.

 chapter 2.  ordered set (continued)
   section 4.   ordered_set2.  preliminary lemmas for Zorn's lemma 
   section 5.   Zorn's lemma

 chapter 3.  Group Theory. Focused on Jordan Hoelder theorem
   section 1.    definition of a group 
   section 2.    non_commutative groups
   section 3.    properties of cosets
   section 4.    normal subgroups and quotient groups
   section 5.    setproducts
   section 6.    preliminary lemmas for Zassenhaus
**)

theory Algebra2 = Algebra1:

section "4. ordered_set2. Lemmas to prove Zorn's lemma "
 
lemma ord_adjunction:"\<lbrakk>ordered_set D; X \<subseteq> carrier D; a \<in> carrier D; 
\<forall>x\<in>X. x \<le>\<^sub>D a\<rbrakk> \<Longrightarrow> ordered_set (Iod D (X \<union> {a}))"
apply (subst ordered_set_def)
apply (rule conjI)
 apply (rule subsetI)
 apply simp apply (simp add:Iod_def) apply (erule conjE)+
apply (unfold Iod_def)
 apply auto
 apply (simp add:ordered_set_def)
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+)apply (simp add:ordered_set_def) 
 apply (simp add:ordered_set_def) apply (erule conjE)+
 apply blast
 apply (simp add:ordered_set_def) apply (erule conjE)+
 apply blast
 apply (simp add:ordered_set_def) apply (erule conjE)+
 apply blast
 apply (simp add:ordered_set_def) 
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
 apply (frule_tac A = X and B = "carrier D" and c = c in subsetD, assumption+)
 apply (unfold ordered_set_def) apply (erule conjE)+
 apply blast apply (erule conjE)+ 
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+)
 apply (frule_tac A = X and B = "carrier D" and c = c in subsetD, assumption+)
 apply blast
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+)
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
 apply (erule conjE)+ apply blast
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+)
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
 apply (erule conjE)+ apply blast
 apply simp apply (erule conjE)+ apply blast
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
 apply (erule conjE)+ apply blast
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
 apply (erule conjE)+ apply blast
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+) apply (erule conjE)+ apply blast
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+) 
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
apply (erule conjE)+ apply blast
 apply (frule_tac A = X and B = "carrier D" and c = aa in subsetD, assumption+) 
 apply (frule_tac A = X and B = "carrier D" and c = b in subsetD, assumption+)
apply (erule conjE)+ apply blast
done

lemma well_ord_adjunction:"\<lbrakk>ordered_set D; X \<subseteq> carrier D; a \<in> carrier D; \<forall>x\<in>X. x \<le>\<^sub>D a; well_ordered_set (Iod D X)\<rbrakk> \<Longrightarrow> well_ordered_set (Iod D (X \<union> {a}))"
apply (subst well_ordered_set_def)
apply (rule conjI)
 apply (simp add:tordered_set_def) 
 apply (frule_tac D = D and X = X and a = a in ord_adjunction, assumption+)
 apply simp
apply (rule ballI)+
apply (case_tac "aa \<in> X") apply (subgoal_tac "aa \<in> carrier (Iod D X)")
  prefer 2 apply (simp add:Iod_def)
 apply (case_tac "b \<in> X") apply (subgoal_tac "b \<in> carrier (Iod D X)")
  prefer 2 apply (simp add:Iod_def)
 apply (subgoal_tac "tordered_set (Iod D X)")
  prefer 2 apply (simp add:well_ordered_set_def)
  apply (simp add:tordered_set_def)
  apply (subgoal_tac "aa \<le>\<^sub>(Iod D X) b \<or>  b \<le>\<^sub>(Iod D X) aa") prefer 2 apply simp
 apply (simp add:Iod_def)
 apply (subgoal_tac "b = a") prefer 2 apply (simp add:Iod_def)
 apply simp apply (simp add:Iod_def)
apply (subgoal_tac "aa = a") prefer 2 apply (simp add:Iod_def)
 apply simp
 apply (case_tac "b \<in> X")
 apply (simp add:Iod_def)
 apply (subgoal_tac "b = a") apply simp apply (simp add:Iod_def ordering_axiom1)apply (simp add:Iod_def)
apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (case_tac "Xa \<inter> X = {}")
 apply (subgoal_tac "Xa = {a}") apply simp
 apply (subgoal_tac "minimum_elem (Iod D (insert a X)) {a} a") apply blast
 apply (subst minimum_elem_def) apply simp apply (simp add:Iod_def ordering_axiom1)
 apply (thin_tac "well_ordered_set (Iod D X)")
 apply (simp add:Iod_def)
 apply (rule equalityI) apply (rule subsetI) apply simp
prefer 3
 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "Xa \<inter> X \<subseteq> carrier (Iod D X)")
 apply (subgoal_tac "\<exists>x. minimum_elem (Iod D X) (Xa \<inter> X) x")
 prefer 2 apply simp 
  apply (thin_tac "tordered_set (Iod D X) \<and> (\<forall>Xa. Xa \<subseteq> carrier (Iod D X) \<and> Xa \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem (Iod D X) Xa x))")
  apply (subgoal_tac "\<forall>x. minimum_elem (Iod D X) (Xa \<inter> X) x \<longrightarrow> ( \<exists>x. minimum_elem (Iod D (insert a X)) Xa x)") apply blast
  apply (thin_tac "\<exists>x. minimum_elem (Iod D X) (Xa \<inter> X) x")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "minimum_elem (Iod D (insert a X)) Xa x")
 apply blast 
 apply (simp add:minimum_elem_def) apply (rule ballI)
 apply (erule conjE)+
apply (case_tac "xa \<in> X") apply (subgoal_tac "xa \<in> Xa \<inter> X")
 apply (subgoal_tac "\<forall>z \<in> Xa \<inter> X. x \<le>\<^sub>(Iod D X) xa") prefer 2 apply simp
 apply (thin_tac "Ball (Xa \<inter> X) (ordering (Iod D X) x)")
 apply (simp add:Iod_def) apply blast
 apply simp
 apply (subgoal_tac "xa = a") apply (simp add:Iod_def)
 apply (simp add:Iod_def) apply (frule_tac A = Xa and B = "insert a X" and c = xa in subsetD, assumption+) apply blast
 apply (rule subsetI) apply (simp add:Iod_def)
apply (frule_tac A = Xa and B = "insert a X" and c = x in subsetD, assumption+) apply blast
apply simp apply (rule contrapos_pp, simp+)
 apply blast
done
 
section "5. Zorn's lemma"

constdefs
 Chain :: "['a OrderedSet, 'a set] \<Rightarrow> bool"
 "Chain D C == C \<subseteq> carrier D \<and> tordered_set (Iod D C)" 
 upper_bound :: "['a OrderedSet, 'a set, 'a] \<Rightarrow> bool"
   ("(3ub/ _/ _/ _)" [100,100,101]100)
 "ub D S b == b \<in> (carrier D) \<and> (\<forall>s\<in>S.  s \<le>\<^sub>D b)" 

 inductive_set:: "'a OrderedSet \<Rightarrow> bool"
 "inductive_set D == ordered_set D \<and> (\<forall>C. Chain D C \<longrightarrow> (\<exists>b. ub D C b))"

 maximal_element::"['a OrderedSet, 'a] \<Rightarrow> bool"
         ("(maximal\<^sub>_/ _)" [100, 101]100)
 "maximal\<^sub>D m == \<forall>b\<in>carrier D. m \<le>\<^sub>D b \<longrightarrow> m = b"

 upper_bounds::"['a OrderedSet, 'a set] \<Rightarrow> 'a set"
 "upper_bounds D H == {x. ub D H x}"

 Sup::"['a OrderedSet, 'a set] \<Rightarrow> 'a"
 "Sup D X == THE x. minimum_elem D (upper_bounds D X) x"

 S_inductive_set::"'a OrderedSet \<Rightarrow> bool"
 "S_inductive_set D == ordered_set D \<and> (\<forall>C. Chain D C \<longrightarrow> (\<exists>x\<in>carrier D. minimum_elem D (upper_bounds D C) x))"

lemma tordered_Chain:"\<lbrakk>ordered_set D; X \<subseteq> carrier D; tordered_set (Iod D X)\<rbrakk>
 \<Longrightarrow> Chain D X"
apply (simp add:Chain_def tordered_set_def) 
done

lemma Sup:"\<lbrakk>ordered_set D; X \<subseteq> carrier D; minimum_elem D (upper_bounds D X) a\<rbrakk> \<Longrightarrow> Sup D X = a"
apply (subst Sup_def)
apply (subgoal_tac "\<forall>y. y \<in> upper_bounds D X \<and> (\<forall>x\<in>upper_bounds D X. y \<le>\<^sub>D x) \<longrightarrow> y = a")
apply (rule the_equality, assumption+)
 apply (simp add:minimum_elem_def)
 apply (rule allI) apply (rule impI)
 apply (erule conjE)+ 
 apply (simp add:minimum_elem_def) apply (erule conjE)+
 apply (subgoal_tac "a \<le>\<^sub>D y") prefer 2 apply (thin_tac "\<forall>x\<in>upper_bounds D X.  y \<le>\<^sub>D x") apply simp
 apply (subgoal_tac "y \<le>\<^sub>D a") prefer 2 apply simp
 apply (rule ordering_axiom2, assumption+)
 apply (simp add:upper_bounds_def upper_bound_def)
 apply (simp add:upper_bounds_def upper_bound_def)
 apply assumption+
done 

lemma S_inductive_sup:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
                             minimum_elem D (upper_bounds D X) (Sup D X)"
 apply (simp add:S_inductive_set_def)
 apply (subgoal_tac "\<exists>x\<in>carrier D. minimum_elem D (upper_bounds D X) x")
 prefer 2 apply simp apply (erule conjE)
 apply (thin_tac "\<forall>C. Chain D C \<longrightarrow>
           (\<exists>x\<in>carrier D. minimum_elem D (upper_bounds D C) x)")
 apply auto
 apply (subgoal_tac "\<forall>y. minimum_elem D (upper_bounds D X) y \<longrightarrow> y = x")
 apply (frule_tac a = x and P = "minimum_elem D (upper_bounds D X)" in theI)
 apply blast
apply (thin_tac "\<forall>y. minimum_elem D (upper_bounds D X) y \<longrightarrow> y = x")
 apply (simp add:Sup_def)
apply (rule allI) apply (rule impI)
 apply (subgoal_tac "X \<subseteq> carrier D")
 apply (frule_tac D = D and X = X and a = x in Sup, assumption+)
 apply (frule_tac D = D and X = X and a = y in Sup, assumption+)
 apply blast
apply (simp add:Chain_def)
done

lemma S_inductive_sup_mem:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
                             Sup D X \<in> carrier D"
apply (frule_tac D = D and X = X in S_inductive_sup)
apply simp
apply (simp add:minimum_elem_def) apply (erule conjE)+
apply (simp add:upper_bounds_def) apply (simp add:upper_bound_def)
done

lemma S_inductive_sup_bound:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
                                        \<forall>x\<in>X. x \<le>\<^sub>D (Sup D X)"
apply (frule_tac D = D and X = X in S_inductive_sup, assumption+) 
apply (rule ballI)
apply (simp add:minimum_elem_def) apply (erule conjE)
 apply (thin_tac "\<forall>x\<in>upper_bounds D X.  Sup D X \<le>\<^sub>D x")
 apply (simp add:upper_bounds_def upper_bound_def) 
done

lemma S_inductive_ordered:"S_inductive_set D \<Longrightarrow> ordered_set D"
apply (simp add:S_inductive_set_def)
done

constdefs
 Wa :: "['a OrderedSet, 'a set, 'a \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
 "Wa S W g a == W \<subseteq> carrier S \<and> well_ordered_set (Iod S W) \<and> a \<in> W \<and> (\<forall>x\<in>W. a \<le>\<^sub>S x) \<and> (\<forall>x\<in>W. (if (ExPre (Iod S W) x) then  g (Pre (Iod S W) x) = x else
 (if a \<noteq> x then Sup S (segment (Iod S W) x) = x else a = a)))" 

constdefs
 WWa :: "['a OrderedSet, 'a \<Rightarrow> 'a, 'a] \<Rightarrow> 'a set set"
 "WWa S g a == {W. Wa S W g a}"
 
lemma BNTr1:"\<lbrakk>ordered_set D; a \<in> carrier D\<rbrakk> \<Longrightarrow> well_ordered_set (Iod D {a})"
apply (simp add:well_ordered_set_def tordered_set_def)
apply (rule conjI)
 apply (simp add:ordered_set_Iod)
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:Iod_def)
 apply (simp add:ordering_axiom1)
apply (rule allI)
apply (rule impI)
 apply (erule conjE)
apply (subgoal_tac "X = {a}") apply simp
 apply (subgoal_tac "minimum_elem (Iod D {a}) {a} a")
 apply blast
apply (simp add:minimum_elem_def) apply (simp add:Iod_def)
 apply (simp add:ordering_axiom1)
apply (simp add:Iod_def)
apply (frule_tac A = X in nonempty_ex)
apply (subgoal_tac "\<forall>y. y \<in> X \<longrightarrow> X = {a}")
apply blast
apply (rule allI)
 apply (rule impI)
 apply (thin_tac "\<exists>x. x \<in> X")
 apply (frule_tac A = X and B = "{a}" and c = y in subsetD, assumption+)
apply (rule equalityI, assumption+)
 apply (rule subsetI)
 apply simp
done
 
lemma BNTr2:"\<lbrakk>ordered_set D;  f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> {a} \<in> WWa D f a"
apply (simp add:WWa_def Wa_def)
apply (subgoal_tac "\<not> ExPre (Iod D {a}) a") apply simp
 apply (simp add:ordering_axiom1)
 apply (simp add:BNTr1)
 apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
apply (rule contrapos_pp, simp+)
 apply (frule_tac D = D and a = a in BNTr1, assumption+) 
 apply (frule_tac S = "Iod D {a}" and a = a in Pre_element)
 apply (simp add:Iod_def) apply assumption
apply (erule conjE)+
 apply (simp add:Iod_def ord_neq_def)
done
     
lemma BNTr3:"\<lbrakk>ordered_set D;  f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); W \<in> WWa D f a\<rbrakk> \<Longrightarrow> minimum_elem (Iod D W) W a"
apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
apply (subst minimum_elem_def)
apply (simp add:Iod_def)
 apply (simp add:WWa_def Wa_def)
done

constdefs
 eqisom :: "['a OrderedSet, 'a OrderedSet, 'a \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
  "eqisom S T f a == a = f a" 

lemma BNTr4_1:"\<lbrakk>ordered_set D;  f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; b \<in> W2;  ord_isom (Iod D W1) (Iod D (segment (Iod D W2) b)) g\<rbrakk> \<Longrightarrow> \<forall>x\<in>W1. g x = x" 
 apply (subgoal_tac "well_ordered_set (Iod D W1)") 
  prefer 2 apply (simp add:WWa_def Wa_def)
  apply (subgoal_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  prefer 2 
  apply (frule_tac D = D and f = f and a = a and W = W1 in BNTr3, assumption+)
  apply (simp add:Iod_def)
 apply (subgoal_tac "g a = a")
 prefer 2 
(**---- g a = a ---**) 
 apply (subgoal_tac "well_ordered_set (Iod D W2)")
  prefer 2 apply (simp add:WWa_def Wa_def)
  apply (frule_tac S = "Iod D W2" and a = b in segment_well_ordered_set)
  apply (simp add:Iod_def)
  apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp
  apply (thin_tac "Iod (Iod D W2) (segment (Iod D W2) b) =
             Iod D (segment (Iod D W2) b)")
  apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D (segment (Iod D W2) b)" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = a in ord_isom_mem, assumption+) 
 apply (simp add:Iod_def WWa_def Wa_def)
 apply (simp add:WWa_def Wa_def) apply (erule conjE)+
 apply (thin_tac "\<forall>x\<in>W1.
                if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
                else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x
                     else a = a")
 apply (thin_tac "\<forall>x\<in>W2.
                if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
                else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x
                     else a = a")
 apply (subgoal_tac "g a \<in> W2") prefer 2 apply (simp add:Iod_def segment_def)
 apply (subgoal_tac "a \<le>\<^sub>D (g a)") prefer 2 apply simp 
  apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
  apply (subgoal_tac "a \<in> carrier (Iod D (segment (Iod D W2) b))") 
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and b = a in ord_isom_surj, assumption+)
 apply (subgoal_tac "\<forall>aa\<in>carrier (Iod D W1). a = g aa \<longrightarrow> g a = a")
 apply blast apply (thin_tac "\<exists>aa\<in>carrier (Iod D W1). a = g aa")
 apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "aa \<in> W1") prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac " a \<le>\<^sub>D aa") prefer 2 apply (thin_tac "a = g aa") 
  apply simp
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = a and b = aa in ord_isom1_2, assumption+)
  apply (simp add:Iod_def) apply assumption apply (simp add:Iod_def)
  apply (subgoal_tac "g a \<le>\<^sub>D a") apply (rule ordering_axiom2, assumption+)
  apply (rule_tac A = W2 and B = "carrier D" and c = "g a" in subsetD, assumption+)
  apply (simp add:Iod_def segment_def)
   apply (thin_tac "ord_isom (Iod D W1) (Iod D (segment (Iod D W2) b)) g")
   apply (thin_tac "well_ordered_set (Iod D W1)")
   apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
   apply (thin_tac "well_ordered_set (Iod D W2)")
   apply (thin_tac "well_ordered_set (Iod D (segment (Iod D W2) b))")
   apply (thin_tac "ordered_set (Iod D W1)")
   apply (thin_tac "ordered_set (Iod D (segment (Iod D W2) b))")
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply (erule conjE)+ apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (frule_tac c = b in subsetD [of "W2" "carrier D"], assumption+)
  apply (frule_tac c = "g a" in subsetD [of "W2" "carrier D"], assumption+)
  apply (frule_tac a = a and b = "g a" and c = b in ordering_axiom3 [of "D"],
                     assumption+) apply simp
  apply (rule contrapos_pp, simp+)
  apply (frule_tac a = "g b" and b = b in ordering_axiom2, assumption+)
  apply simp  (*** --- g a = a --- done ***)
 apply (rule Iod_sub_sub, assumption+) apply (rule subsetI) 
  apply (simp add:Iod_def segment_def) apply (simp add:WWa_def Wa_def)
apply (rule ballI)
 apply (frule_tac S = "Iod D W1" and ?s0.0 = a and P = "eqisom (Iod D W1) (Iod D (segment (Iod D W2) b)) g" in transfinite_induction)
 apply assumption
 apply (simp add:eqisom_def)
 prefer 2
  apply (subgoal_tac "x \<in> carrier (Iod D W1)")
  apply (subgoal_tac "eqisom (Iod D W1) (Iod D (segment (Iod D W2) b)) g x")
  prefer 2 apply simp apply (simp add:eqisom_def)
  apply (subgoal_tac "x = g x") 
  apply (thin_tac "\<forall>x\<in>carrier (Iod D W1). eqisom (Iod D W1) (Iod D (segment (Iod D W2) b)) g x")
  apply (simp add:WWa_def Wa_def) apply (erule conjE)+
  apply (thin_tac "\<forall>x\<in>W1.
             if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x else a = a")
  apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
  apply (frule_tac S = "Iod D W2" and a = b in segment_well_ordered_set)  
   apply (simp add:Iod_def)
  apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp  
  apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D (segment (Iod D W2) b)" in well_ordered_set_is_ordered_set)   
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = x in ord_isom_mem, assumption+) 
  apply (simp add:Iod_def segment_def)
   apply (simp add:Iod_def)
  apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:Iod_def segment_def)
  apply (simp add:WWa_def Wa_def)
 apply (simp add:Iod_def eqisom_def)
(**--- transfinite main part ---**)
apply (rule ballI)
 apply (rule impI)
apply (simp add:WWa_def Wa_def)
 apply (erule conjE)+
 apply (subgoal_tac "t \<in> W1")
  prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac "if ExPre (Iod D W1) t then f (Pre (Iod D W1) t) = t
             else if a \<noteq> t then Sup D (segment (Iod D W1) t) = t else a = a")
  prefer 2 apply simp
  apply (thin_tac "\<forall>x\<in>W1. if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x else a = a")
 (** case --- " ExPre (Iod D W1) t " --- **)
apply (case_tac "ExPre (Iod D W1) t")
 apply simp
 apply (frule_tac S = "Iod D W2" and a = b in segment_well_ordered_set)
  apply (simp add:Iod_def) 
  apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp prefer 2 apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:segment_def) apply (erule conjE)+
  apply (simp add:Iod_def) apply (simp add:WWa_def Wa_def)
 apply (frule_tac S = "Iod D W1" and T = "Iod D (segment (Iod D W2) b)" and a = t and f = g in ord_isom_Pre1, assumption+)  
 apply (frule_tac S = "Iod D W2" and a = b and b = "g t" in Pre_segment)
  apply (simp add:Iod_def)
  apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D (segment (Iod D W2) b)" in well_ordered_set_is_ordered_set)  
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = t in ord_isom_mem, assumption+)
  apply (simp add:Iod_def) apply simp
  apply (erule conjE)+
 apply (frule_tac S = "Iod D W1" and a = t in Pre_element, assumption+)
 apply (erule conjE)+
 apply (subgoal_tac " Pre (Iod D W1) t \<in> segment (Iod D W1) t")
  prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "eqisom (Iod D W1) (Iod D (segment (Iod D W2) b)) g (Pre (Iod D W1) t)") prefer 2 apply simp
 apply (simp add:eqisom_def)
 apply (subgoal_tac "g t \<in> W2") 
  apply (rotate_tac -6) apply (frule sym) 
  apply (thin_tac "Pre (Iod D W2) (g t) = Pre (Iod D (segment (Iod D W2) b)) (g t)")
 apply (subgoal_tac "if ExPre (Iod D W2) (g t) then f (Pre (Iod D W2) (g t)) = (g t) else if a \<noteq> (g t) then Sup D (segment (Iod D W2) (g t)) = (g t) else a = a") prefer 2 apply simp
 apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
 apply simp
 apply (frule_tac S = "Iod D W1" and T = "Iod D (segment (Iod D W2) b)" and a = t and f = g in ord_isom_Pre2, assumption+)
 apply simp
  apply (thin_tac " \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
  apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
  apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
  apply (thin_tac "\<forall>x\<in>W1.  a \<le>\<^sub>D x")
  apply (thin_tac "f (Pre (Iod D W1) t) = t")
  apply (thin_tac " ExPre (Iod D W1) t")
  apply (thin_tac "well_ordered_set (Iod D W2)")
  apply (thin_tac "Iod (Iod D W2) (segment (Iod D W2) b) =
          Iod D (segment (Iod D W2) b)")
  apply (thin_tac "ExPre (Iod D W2) (g t)")
  apply (thin_tac "Pre (Iod D W2) (g t) = Pre (Iod D (segment (Iod D W2) b)) (g t)")
  apply (thin_tac "ExPre (Iod D (segment (Iod D W2) b)) (g t)")
  apply (thin_tac "Pre (Iod D W1) t \<in> carrier (Iod D W1)")
  apply (thin_tac "Pre (Iod D W1) t <\<^sub>(Iod D W1) t")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D W1).
              Pre (Iod D W1) t <\<^sub>(Iod D W1) y \<longrightarrow> \<not>  y <\<^sub>(Iod D W1) t")
  apply (thin_tac "Pre (Iod D W1) t \<in> segment (Iod D W1) t")
 apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D (segment (Iod D W2) b)" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g in ord_isom_mem, assumption+)
 apply (simp add:Iod_def segment_def) (*** case "ExPre (Iod D W1) t" done ---*)
(** --- case " \<not> ExPre (Iod D W1) t " --- **)
apply (case_tac "a = t") 
 apply (simp add:eqisom_def)
apply (subgoal_tac "Sup D (segment (Iod D W1) t ) = t") prefer 2 apply simp
 apply (thin_tac "if ExPre (Iod D W1) t then f (Pre (Iod D W1) t) = t
          else if a \<noteq> t then Sup D (segment (Iod D W1) t) = t else a = a")
 apply (simp add:eqisom_def)
 apply (frule_tac S = "Iod D W2" and a = b in segment_well_ordered_set)
 apply (simp add:Iod_def) 
 apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp prefer 2 apply (rule Iod_sub_sub, assumption+)
 apply (rule subsetI) apply (simp add:Iod_def segment_def)
 apply assumption+
 apply (subgoal_tac "a \<noteq> g t") prefer 2 apply (rule contrapos_pp, simp+)
  apply (subgoal_tac "g a = g t") prefer 2 apply simp
  apply (subgoal_tac "a = t") apply simp
   apply (simp add:ord_isom_def) apply (erule conjE)+
   apply (simp add:bij_to_def) apply (erule conjE)+
   apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
   apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) (g t)")
   apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
   apply (thin_tac "\<forall>x\<in>W1.  g t \<le>\<^sub>D x")
   apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
   apply (thin_tac "\<forall>a\<in>carrier (Iod D W1). \<forall>ba\<in>carrier (Iod D W1).
          a <\<^sub>(Iod D W1) ba =  g a <\<^sub>(Iod D (segment (Iod D W2) b)) (g ba)")
   apply (thin_tac "surj_to g (carrier (Iod D W1))
           (carrier (Iod D (segment (Iod D W2) b)))")
   apply (rotate_tac -4) apply (frule sym) apply (thin_tac "a = g t")
   apply simp
   apply (subgoal_tac "g a = g t")
  apply (frule_tac f = g and A = "carrier (Iod D W1)" and x = a and y = t in
    injective)
   apply (simp add:Iod_def) apply assumption+ apply blast
   apply simp
 apply (subgoal_tac "\<not> ExPre (Iod D W2) (g t)")
  (**-- g t \<in> W2 -- *)
  apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D (segment (Iod D W2) b)" in well_ordered_set_is_ordered_set)
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = t in  ord_isom_mem, assumption+)
  apply (subgoal_tac "g t \<in> W2") prefer 2 apply (simp add:Iod_def segment_def)
  apply (subgoal_tac "if ExPre (Iod D W2) (g t) then f (Pre (Iod D W2) (g t)) = (g t) else if a \<noteq> (g t) then Sup D (segment (Iod D W2) (g t)) = (g t) else a = a") prefer 2 apply simp
  apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
  apply simp
  apply (subgoal_tac "segment (Iod D W2) (g t) = segment (Iod D W1) t")
  apply simp
apply (rule equalityI)
 apply (rule subsetI)
  apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  apply (thin_tac "well_ordered_set (Iod D W2)")
  apply (thin_tac "\<not> ExPre (Iod D W1) t")
  apply (thin_tac " Sup D (segment (Iod D W1) t) = t")
  apply (thin_tac "well_ordered_set (Iod D (segment (Iod D W2) b))")
  apply (thin_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)")
  apply (thin_tac "well_ordered_set (Iod D W1)")
  apply (subgoal_tac "xa \<in> carrier (Iod D (segment (Iod D W2) b))")
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and b = xa in ord_isom_surj, assumption+)
  apply (subgoal_tac "\<forall>w\<in>carrier (Iod D W1). xa = g w \<longrightarrow> xa \<in> segment (Iod D W1) t") apply blast apply (thin_tac "\<exists>a\<in>carrier (Iod D W1). xa = g a")
  apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "g w <\<^sub>D (g t)") 
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = w and b = t in ord_isom2_1, assumption+)
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply (subgoal_tac "w \<in> segment (Iod D W1) t")
  apply (subgoal_tac "w = g w") prefer 2 apply simp
  apply (simp add:segment_def) apply (simp add:segment_def)
  apply (simp add:Iod_def segment_def ord_neq_def)
   apply (thin_tac "ord_isom (Iod D W1) (Iod D (segment (Iod D W2) b)) g")
   apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
   apply (thin_tac "t \<in> carrier (Iod D W1)")
   apply (thin_tac "\<not> ExPre (Iod D W2) (g t)")
   apply (thin_tac "ordered_set (Iod D (segment (Iod D W2) b))")
   apply (thin_tac "Sup D (segment (Iod D W2) (g t)) = g t")
   apply (thin_tac "ordered_set (Iod D W1)")
  apply (simp add:segment_def Iod_def ord_neq_def)
  apply (erule conjE)+
  apply (frule_tac c = xa in subsetD [of "W2" "carrier D"], assumption+)
  apply (frule_tac c = b in subsetD [of "W2" "carrier D"], assumption+)
  apply (frule_tac c = "g t" in subsetD [of "W2" "carrier D"], assumption+)
  apply (frule_tac a = xa and b = "g t" and c = b in ordering_axiom3 [of "D"],
            assumption+) apply simp
  apply (rule contrapos_pp, simp+)
  apply (frule_tac a = b and b = "g t" in ordering_axiom2 [of "D"], assumption+) apply simp
apply (rule subsetI)
 apply (subgoal_tac "xa = g xa") prefer 2 apply simp
 apply (subgoal_tac "xa <\<^sub>(Iod D W1) t")
 apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = xa and b = t in ord_isom1_1, assumption+)
  apply (simp add:segment_def) apply assumption
  apply (simp add:segment_def)
  apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (thin_tac "well_ordered_set (Iod D W1)")
  apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
  apply (thin_tac "well_ordered_set (Iod D W2)")
  apply (thin_tac "\<forall>x\<in>W1.  a \<le>\<^sub>D x")
  apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
  apply (thin_tac "\<not> ExPre (Iod D W1) t")
  apply (thin_tac "Sup D (segment (Iod D W1) t) = t")
  apply (thin_tac "well_ordered_set (Iod D (segment (Iod D W2) b))")
  apply (thin_tac "Iod (Iod D W2) (segment (Iod D W2) b) =
          Iod D (segment (Iod D W2) b)")
  apply (thin_tac "f \<in> carrier D \<rightarrow> carrier D")
  apply (rotate_tac -3) apply (frule sym) apply (thin_tac "xa = g xa")
  apply simp
  apply (thin_tac "Sup D (segment (Iod D W2) (g t)) = g t")
  apply (thin_tac "g t \<in> carrier (Iod D (segment (Iod D W2) b))")
  apply (subgoal_tac "xa \<in> carrier (Iod D W1)")
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = xa in ord_isom_mem, assumption+) 
  apply (thin_tac " ord_isom (Iod D W1) (Iod D (segment (Iod D W2) b)) g")
  apply (thin_tac "t \<in> carrier (Iod D W1)")
  apply (thin_tac "xa <\<^sub>(Iod D W1) t")
  apply (thin_tac "\<not> ExPre (Iod D W2) (g t)")
  apply (thin_tac "ordered_set (Iod D W1)")
  apply (thin_tac "ordered_set (Iod D (segment (Iod D W2) b))")
  apply (thin_tac " xa \<in> segment (Iod D W1) t")
  apply (thin_tac "xa \<in> carrier (Iod D W1)")
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply (simp add:segment_def)
  apply (simp add:segment_def)
apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "f \<in> carrier D \<rightarrow> carrier D")
 apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
 apply (thin_tac "\<forall>x\<in>W1.  a \<le>\<^sub>D x")
 apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
 apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
 apply (thin_tac "Iod (Iod D W2) (segment (Iod D W2) b) =
          Iod D (segment (Iod D W2) b)")
 apply (thin_tac "Sup D (segment (Iod D W1) t) = t")
 apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D (segment (Iod D W2) b)" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g in ord_isom_sym, assumption+)
 apply (rule contrapos_pp, simp+) 
 apply (frule_tac S = "Iod D (segment (Iod D W2) b)" and T = "Iod D W1" and a = "g t" and f = "(invfun (carrier (Iod D W1)) (carrier (Iod D (segment (Iod D W2) b))) g)" in ord_isom_Pre1, assumption+)
 apply (simp add:ord_isom_mem)  
 apply (subgoal_tac "b \<in> carrier (Iod D W2)")
 apply (frule_tac S = "Iod D W2" and a = b and b = "g t" in Pre2segment, assumption+)
 apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = t in ord_isom_mem, assumption+)
 apply (simp add:Iod_def segment_def)
  apply (frule_tac D = "Iod D W1" and E = "Iod D (segment (Iod D W2) b)" and f = g and a = t in ord_isom_mem, assumption+)
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply assumption
 apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp
 apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:Iod_def segment_def)
 apply assumption+
 apply (simp add:Iod_def) apply assumption
apply (subgoal_tac "invfun (carrier (Iod D W1))
             (carrier (Iod D (segment (Iod D W2) b))) g (g t) = t")
 apply simp
 apply (rule invfun_l)
  apply (simp add:ord_isom_def)
  apply (simp add:ord_isom_def bij_to_def)
  apply (simp add:ord_isom_def bij_to_def)
 apply assumption
done

lemma BNTr4:"\<lbrakk>ordered_set D;  f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; \<exists>b\<in>W2. ord_equiv (Iod D W1) (Iod D (segment (Iod D W2) b))\<rbrakk> \<Longrightarrow> W1 \<subseteq> W2 " 
apply (rule subsetI)
 apply auto
 apply (simp add:ord_equiv_def)
 apply auto
 apply (subgoal_tac "ordered_set (Iod D W1)")
 apply (subgoal_tac "ordered_set (Iod D (segment (Iod D W2) b))")
 apply (subgoal_tac "x \<in> carrier (Iod D W1)") 
apply (frule_tac D = "Iod D W1" and E = "(Iod D (segment (Iod D W2) b))" and f = fa and a = x in ord_isom_mem, assumption+)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = W1 and ?W2.0 = W2 and b = b and g = fa in BNTr4_1, assumption+)
 apply simp apply (thin_tac "\<forall>x\<in>W1. fa x = x")
 apply (simp add:Iod_def segment_def) apply (simp add:Iod_def)
 apply (subgoal_tac "well_ordered_set (Iod D W2)")
 apply (frule_tac S = "Iod D W2" and a = b in segment_well_ordered_set)
  apply (simp add:Iod_def)
  apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp 
  apply (thin_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)")
  apply (simp add:well_ordered_set_is_ordered_set)
  apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:Iod_def segment_def)
  apply (simp add:WWa_def Wa_def)
  apply (simp add:WWa_def Wa_def)
apply (simp add:WWa_def Wa_def) apply (erule conjE)+
 apply (simp add:well_ordered_set_is_ordered_set)
done

lemma BNTr5:"\<lbrakk>ordered_set D;  f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; ord_equiv (Iod D W1) (Iod D W2)\<rbrakk> \<Longrightarrow> W1 \<subseteq> W2 " 
apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>g. ord_isom (Iod D W1) (Iod D W2) g \<longrightarrow> W1 \<subseteq> W2")  apply blast
 apply (thin_tac "\<exists>f. ord_isom (Iod D W1) (Iod D W2) f")
 apply (rule allI) apply (rule impI) 
 apply (subgoal_tac "well_ordered_set (Iod D W1)") 
  prefer 2 apply (simp add:WWa_def Wa_def)
  apply (subgoal_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  prefer 2 
  apply (frule_tac D = D and f = f and a = a and W = W1 in BNTr3, assumption+)
  apply (simp add:Iod_def)
 apply (subgoal_tac "g a = a")
 prefer 2 
(**---- g a = a ---**) 
 apply (subgoal_tac "well_ordered_set (Iod D W2)")
  prefer 2 apply (simp add:WWa_def Wa_def)
  apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = a in ord_isom_mem, assumption+) 
 apply (simp add:Iod_def WWa_def Wa_def)
 apply (simp add:WWa_def Wa_def) apply (erule conjE)+
 apply (thin_tac "\<forall>x\<in>W1.
                if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
                else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x
                     else a = a")
 apply (thin_tac "\<forall>x\<in>W2.
                if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
                else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x
                     else a = a")
 apply (subgoal_tac "g a \<in> W2") prefer 2 apply (simp add:Iod_def segment_def)
 apply (subgoal_tac "a \<le>\<^sub>D (g a)") prefer 2 apply simp 
  apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
  apply (subgoal_tac "a \<in> carrier (Iod D W2)") 
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and b = a in ord_isom_surj, assumption+)
 apply (subgoal_tac "\<forall>aa\<in>carrier (Iod D W1). a = g aa \<longrightarrow> g a = a")
 apply blast apply (thin_tac "\<exists>aa\<in>carrier (Iod D W1). a = g aa")
 apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "aa \<in> W1") prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac " a \<le>\<^sub>D aa") prefer 2 apply (thin_tac "a = g aa") 
  apply simp
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = a and b = aa in ord_isom1_2, assumption+)
  apply (simp add:Iod_def) apply assumption apply (simp add:Iod_def)
  apply (subgoal_tac "g a \<le>\<^sub>D a") apply (rule ordering_axiom2, assumption+)
  apply (rule_tac A = W2 and B = "carrier D" and c = "g a" in subsetD, assumption+)
  apply (simp add:Iod_def) apply (simp add:Iod_def)
    (*** --- g a = a --- done ***)
(*--- W1 \<subseteq> W2 ---*)
apply (rule subsetI)
 apply (frule_tac S = "Iod D W1" and ?s0.0 = a and P = "eqisom (Iod D W1) (Iod D W2) g" in transfinite_induction)
 apply assumption
 apply (simp add:eqisom_def)
 prefer 2
  apply (subgoal_tac "x \<in> carrier (Iod D W1)")
  apply (subgoal_tac "eqisom (Iod D W1) (Iod D W2) g x")
  prefer 2 apply simp apply (simp add:eqisom_def)
  apply (subgoal_tac "x = g x") apply (thin_tac "\<forall>x\<in>carrier (Iod D W1). x = g x")
 apply (subgoal_tac "well_ordered_set (Iod D W2)") 
 prefer 2 apply (simp add:WWa_def Wa_def)
 apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set) 
 apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = x in ord_isom_mem, assumption+)
 apply (simp add:Iod_def) apply simp apply (simp add:Iod_def)
(**--- transfinite main part ---**)
apply (rule ballI)
 apply (rule impI)
apply (simp add:WWa_def Wa_def)
 apply (erule conjE)+
 apply (subgoal_tac "t \<in> W1")
  prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac "if ExPre (Iod D W1) t then f (Pre (Iod D W1) t) = t
             else if a \<noteq> t then Sup D (segment (Iod D W1) t) = t else a = a")
  prefer 2 apply simp
  apply (thin_tac "\<forall>x\<in>W1. if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x else a = a")
 (** case --- " ExPre (Iod D W1) t " --- **)
apply (case_tac "ExPre (Iod D W1) t")
 apply (frule_tac S = "Iod D W1" and T = "Iod D W2" and a = t and f = g in ord_isom_Pre1, assumption+)  
 apply (frule_tac S = "Iod D W1" and a = t in Pre_element, assumption+)
 apply (erule conjE)+
 apply (subgoal_tac " Pre (Iod D W1) t \<in> segment (Iod D W1) t")
  prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "eqisom (Iod D W1) (Iod D W2) g (Pre (Iod D W1) t)") prefer 2 apply simp
 apply (simp add:eqisom_def)
 apply (subgoal_tac "g t \<in> W2") 
 apply (subgoal_tac "if ExPre (Iod D W2) (g t) then f (Pre (Iod D W2) (g t)) = (g t) else if a \<noteq> (g t) then Sup D (segment (Iod D W2) (g t)) = (g t) else a = a") prefer 2 apply simp
 apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
 apply simp
 apply (frule_tac S = "Iod D W1" and T = "Iod D W2" and a = t and f = g in ord_isom_Pre2, assumption+)
 apply simp
  apply (thin_tac " \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
  apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
  apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
  apply (thin_tac "\<forall>x\<in>W1.  a \<le>\<^sub>D x")
  apply (thin_tac "f (Pre (Iod D W1) t) = t")
  apply (thin_tac " ExPre (Iod D W1) t")
  apply (thin_tac "ExPre (Iod D W2) (g t)")
  apply (thin_tac "Pre (Iod D W1) t \<in> carrier (Iod D W1)")
  apply (thin_tac "Pre (Iod D W1) t <\<^sub>(Iod D W1) t")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D W1).
              Pre (Iod D W1) t <\<^sub>(Iod D W1) y \<longrightarrow> \<not>  y <\<^sub>(Iod D W1) t")
  apply (thin_tac "Pre (Iod D W1) t \<in> segment (Iod D W1) t")
 apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g in ord_isom_mem, assumption+)
 apply (simp add:Iod_def segment_def) (*** case "ExPre (Iod D W1) t" done ---*)
(** --- case " \<not> ExPre (Iod D W1) t " --- **)
apply (case_tac "a = t") 
 apply (simp add:eqisom_def)
apply (subgoal_tac "Sup D (segment (Iod D W1) t ) = t") prefer 2 apply simp
 apply (thin_tac "if ExPre (Iod D W1) t then f (Pre (Iod D W1) t) = t
          else if a \<noteq> t then Sup D (segment (Iod D W1) t) = t else a = a")
 apply (simp add:eqisom_def)
 apply (subgoal_tac "a \<noteq> g t") prefer 2 apply (rule contrapos_pp, simp+)
  apply (subgoal_tac "g a = g t") prefer 2 apply simp
  apply (subgoal_tac "a = t") apply simp
   apply (simp add:ord_isom_def) apply (erule conjE)+
   apply (simp add:bij_to_def) apply (erule conjE)+
   apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
   apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) (g t)")
   apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
   apply (thin_tac "\<forall>x\<in>W1.  g t \<le>\<^sub>D x")
   apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
   apply (thin_tac "\<forall>a\<in>carrier (Iod D W1). \<forall>ba\<in>carrier (Iod D W1).
          a <\<^sub>(Iod D W1) ba =  g a <\<^sub>(Iod D W2) (g ba)")
   apply (thin_tac "surj_to g (carrier (Iod D W1))
           (carrier (Iod D W2))")
   apply (rotate_tac -4) apply (frule sym) apply (thin_tac "a = g t")
   apply simp
   apply (subgoal_tac "g a = g t")
  apply (frule_tac f = g and A = "carrier (Iod D W1)" and x = a and y = t in
    injective)
   apply (simp add:Iod_def) apply assumption+ apply blast
   apply simp
 apply (subgoal_tac "\<not> ExPre (Iod D W2) (g t)")
  (**-- g t \<in> W2 -- *)
  apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = t in  ord_isom_mem, assumption+)
  apply (subgoal_tac "g t \<in> W2") prefer 2 apply (simp add:Iod_def segment_def)
  apply (subgoal_tac "if ExPre (Iod D W2) (g t) then f (Pre (Iod D W2) (g t)) = (g t) else if a \<noteq> (g t) then Sup D (segment (Iod D W2) (g t)) = (g t) else a = a") prefer 2 apply simp
  apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
  apply simp
  apply (subgoal_tac "segment (Iod D W2) (g t) = segment (Iod D W1) t")
  apply simp
apply (rule equalityI)
 apply (rule subsetI)
  apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  apply (thin_tac "well_ordered_set (Iod D W2)")
  apply (thin_tac "\<not> ExPre (Iod D W1) t")
  apply (thin_tac " Sup D (segment (Iod D W1) t) = t")
  apply (thin_tac "well_ordered_set (Iod D W1)")
  apply (subgoal_tac "xa \<in> carrier (Iod D W2)")
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and b = xa in ord_isom_surj, assumption+)
  apply (subgoal_tac "\<forall>w\<in>carrier (Iod D W1). xa = g w \<longrightarrow> xa \<in> segment (Iod D W1) t") apply blast apply (thin_tac "\<exists>a\<in>carrier (Iod D W1). xa = g a")
  apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "g w <\<^sub>D (g t)") 
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = w and b = t in ord_isom2_1, assumption+)
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply (subgoal_tac "w \<in> segment (Iod D W1) t")
  apply (subgoal_tac "w = g w") prefer 2 apply simp
  apply (simp add:segment_def) apply (simp add:segment_def)
  apply (simp add:Iod_def segment_def ord_neq_def)
   apply (thin_tac "ord_isom (Iod D W1) (Iod D W2) g")
   apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
   apply (thin_tac "t \<in> carrier (Iod D W1)")
   apply (thin_tac "\<not> ExPre (Iod D W2) (g t)")
   apply (thin_tac "ordered_set (Iod D W2)")
   apply (thin_tac "Sup D (segment (Iod D W2) (g t)) = g t")
   apply (thin_tac "ordered_set (Iod D W1)")
  apply (simp add:segment_def Iod_def ord_neq_def)
apply (rule subsetI)
 apply (subgoal_tac "xa = g xa") prefer 2 apply simp
 apply (subgoal_tac "xa <\<^sub>(Iod D W1) t")
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = xa and b = t in ord_isom1_1, assumption+)
  apply (simp add:segment_def) apply assumption
  apply (simp add:segment_def)
  apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (thin_tac "well_ordered_set (Iod D W1)")
  apply (thin_tac "minimum_elem (Iod D W1) (carrier (Iod D W1)) a")
  apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
  apply (thin_tac "well_ordered_set (Iod D W2)")
  apply (thin_tac "\<forall>x\<in>W1.  a \<le>\<^sub>D x")
  apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
  apply (thin_tac "\<not> ExPre (Iod D W1) t")
  apply (thin_tac "Sup D (segment (Iod D W1) t) = t")
  apply (thin_tac "f \<in> carrier D \<rightarrow> carrier D")
  apply (rotate_tac -3) apply (frule sym) apply (thin_tac "xa = g xa")
  apply simp
  apply (thin_tac "Sup D (segment (Iod D W2) (g t)) = g t")
  apply (thin_tac "g t \<in> carrier (Iod D W2)")
  apply (subgoal_tac "xa \<in> carrier (Iod D W1)")
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = xa in ord_isom_mem, assumption+) 
  apply (thin_tac " ord_isom (Iod D W1) (Iod D W2) g")
  apply (thin_tac "t \<in> carrier (Iod D W1)")
  apply (thin_tac "xa <\<^sub>(Iod D W1) t")
  apply (thin_tac "\<not> ExPre (Iod D W2) (g t)")
  apply (thin_tac "ordered_set (Iod D W1)")
  apply (thin_tac "ordered_set (Iod D W2)")
  apply (thin_tac " xa \<in> segment (Iod D W1) t")
  apply (thin_tac "xa \<in> carrier (Iod D W1)")
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply (simp add:segment_def)
  apply (simp add:segment_def)
apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "f \<in> carrier D \<rightarrow> carrier D")
 apply (thin_tac "\<forall>u\<in>segment (Iod D W1) t. u = g u")
 apply (thin_tac "\<forall>x\<in>W1.  a \<le>\<^sub>D x")
 apply (thin_tac "\<forall>x\<in>W2.  a \<le>\<^sub>D x")
 apply (thin_tac "\<forall>x\<in>W2.
             if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
             else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
 apply (thin_tac "Sup D (segment (Iod D W1) t) = t")
 apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g in ord_isom_sym, assumption+)
 apply (rule contrapos_pp, simp+) 
 apply (frule_tac S = "Iod D W2" and T = "Iod D W1" and a = "g t" and f = "(invfun (carrier (Iod D W1)) (carrier (Iod D W2)) g)" in ord_isom_Pre1, assumption+)
 apply (simp add:ord_isom_mem) apply assumption apply assumption
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = t in ord_isom_mem, assumption+)
  apply (frule_tac D = "Iod D W1" and E = "Iod D W2" and f = g and a = t in ord_isom_mem, assumption+)
apply (subgoal_tac "invfun (carrier (Iod D W1))
             (carrier (Iod D W2)) g (g t) = t")
 apply simp
 apply (rule invfun_l)
  apply (simp add:ord_isom_def)
  apply (simp add:ord_isom_def bij_to_def)
  apply (simp add:ord_isom_def bij_to_def)
 apply assumption
done

lemma BNTr6:"\<lbrakk>ordered_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
\<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; W1 \<subset> W2\<rbrakk> \<Longrightarrow> (\<exists>b\<in>carrier (Iod D W2). ord_equiv (Iod D W1) (Iod D (segment (Iod D W2) b)))"
apply (subgoal_tac "well_ordered_set (Iod D W1)") 
 apply (subgoal_tac "well_ordered_set (Iod D W2)")
 apply (frule_tac S = "Iod D W1" and T = "Iod D W2" in well_ord_compare, assumption+)
prefer 2 apply (simp add:WWa_def Wa_def)
prefer 2 apply (simp add:WWa_def Wa_def)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>b\<in>carrier (Iod D W2). Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp
 apply (thin_tac "\<forall>b\<in>carrier (Iod D W2). Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)")
 apply (thin_tac "\<forall>b\<in>carrier (Iod D W2).
          \<not> ord_equiv (Iod D W1) (Iod D (segment (Iod D W2) b))")
 apply (case_tac "ord_equiv (Iod D W1) (Iod D W2)")
 apply (frule_tac S = "Iod D W1" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" in ord_equiv_sym, assumption+) 
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = W2 and ?W2.0 = W1 in  BNTr5, assumption+)
 apply (rule_tac A = W1 and B = W2 in subset_contr, assumption+) 
apply simp
 apply (subgoal_tac "\<forall>a\<in>carrier (Iod D W1). ord_equiv (Iod (Iod D W1) (segment (Iod D W1) a)) (Iod D W2) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>a\<in>carrier (Iod D W1).
          ord_equiv (Iod (Iod D W1) (segment (Iod D W1) a)) (Iod D W2)")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac S = "Iod D W1" and a = aa in segment_well_ordered_set)
  apply (simp add:WWa_def Wa_def)
 apply (subgoal_tac "Iod (Iod D W1) (segment (Iod D W1) aa) = Iod D (segment (Iod D W1) aa)") apply simp
 apply (thin_tac "Iod (Iod D W1) (segment (Iod D W1) aa) =
            Iod D (segment (Iod D W1) aa)")
 apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D (segment (Iod D W1) aa)" in well_ordered_set_is_ordered_set) 
 apply (frule_tac D = "Iod D (segment (Iod D W1) aa)" and E = "Iod D W2" in ord_equiv_sym, assumption+)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = W2 and ?W2.0 = W1 in  BNTr4, assumption+) apply (subgoal_tac "aa \<in> W1") apply blast
  apply (simp add:Iod_def)
 apply (rule_tac A = W1 and B = W2 in subset_contr, assumption+)
 apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:segment_def) apply (simp add:Iod_def)
  apply (simp add:WWa_def Wa_def)
apply (rule ballI)
 apply (rule Iod_sub_sub, assumption+)
 apply (rule subsetI) apply (simp add:segment_def) apply (simp add:Iod_def)
apply (simp add:WWa_def Wa_def)
done

lemma BNTr7:"\<lbrakk>ordered_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
\<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a\<rbrakk> \<Longrightarrow> W1 \<subseteq> W2 \<or> W2 \<subseteq> W1"
apply (subgoal_tac "well_ordered_set (Iod D W1)") 
 apply (subgoal_tac "well_ordered_set (Iod D W2)")
 apply (frule_tac S = "Iod D W1" and T = "Iod D W2" in well_ord_compare, assumption+)
prefer 2 apply (simp add:WWa_def Wa_def)
prefer 2 apply (simp add:WWa_def Wa_def)
apply (case_tac "\<exists>a\<in>carrier (Iod D W1).
           ord_equiv (Iod (Iod D W1) (segment (Iod D W1) a)) (Iod D W2)")
apply (frule_tac D = D and f = f and a = a and ?W1.0 = W2 and ?W2.0 = W1 in BNTr4, assumption+)
 apply (thin_tac "(\<exists>a\<in>carrier (Iod D W1).
  ord_equiv (Iod (Iod D W1) (segment (Iod D W1) a)) (Iod D W2)) \<or>
  ord_equiv (Iod D W1) (Iod D W2) \<or> (\<exists>b\<in>carrier (Iod D W2).
           ord_equiv (Iod D W1) (Iod (Iod D W2) (segment (Iod D W2) b)))")
  apply (subgoal_tac "\<forall>c\<in>carrier (Iod D W1).
  ord_equiv (Iod (Iod D W1) (segment (Iod D W1) c)) (Iod D W2) \<longrightarrow> (\<exists>b\<in>W1. ord_equiv (Iod D W2) (Iod D (segment (Iod D W1) b)))") apply blast
  apply (thin_tac "\<exists>a\<in>carrier (Iod D W1).
          ord_equiv (Iod (Iod D W1) (segment (Iod D W1) a)) (Iod D W2)")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "Iod (Iod D W1) (segment (Iod D W1) c) = Iod D (segment (Iod D W1) c)") apply simp
 apply (frule_tac S = "Iod D W2" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D W1" and a = c in segment_well_ordered_set)
  apply assumption apply simp
 apply (frule_tac S = "Iod D (segment (Iod D W1) c)" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D (segment (Iod D W1) c)" and E = "Iod D W2" in ord_equiv_sym, assumption+) apply (subgoal_tac "c \<in> W1") apply blast
 apply (simp add:Iod_def)
 apply (rule Iod_sub_sub, assumption+) apply (rule subsetI) 
  apply (simp add:segment_def) apply (erule conjE)+ apply (simp add:Iod_def)
 apply (simp add:WWa_def Wa_def) apply simp
apply simp
apply (case_tac "ord_equiv (Iod D W1) (Iod D W2)")
 apply (simp add:BNTr5) apply simp 
 apply (frule BNTr4 [of "D" "f" "a" "W1" "W2"], assumption+)
 apply auto
 apply (subgoal_tac "b \<in> W2")
 apply (subgoal_tac "Iod (Iod D W2) (segment (Iod D W2) b) = Iod D (segment (Iod D W2) b)") apply simp
 apply blast
 apply (rule Iod_sub_sub, assumption+) apply (rule subsetI) 
  apply (simp add:segment_def) apply (simp add:Iod_def)
apply (simp add:WWa_def Wa_def)
apply (simp add:Iod_def)
done
 
lemma BNTr8:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> \<Union> (WWa D f a) \<in> (WWa D f a)"
apply (simp add:WWa_def)
apply (subgoal_tac "\<Union>{W. Wa D W f a} \<subseteq> carrier D")
 apply (subst Wa_def)
apply (rule conjI)
 apply assumption
 prefer 2
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (subgoal_tac "\<forall>xa. Wa D xa f a \<and> x \<in> xa \<longrightarrow> x \<in> carrier D")
 apply blast apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (rule allI) apply (rule impI) apply (simp add:Wa_def) 
 apply (erule conjE)+  apply (simp add:subsetD)
apply (subgoal_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
 apply (rule conjI)
 apply assumption
 prefer 2
 apply (simp add:well_ordered_set_def)
 apply (rule conjI)
 apply (simp add:tordered_set_def)
 apply (rule conjI)
 apply (rule ordered_set_Iod)
  apply (simp add:S_inductive_set_def) apply assumption
  apply (rule ballI)+
  apply (simp add:Iod_def CollectI)
 apply (subgoal_tac "\<forall>X Y. Wa D X f a \<and> aa \<in> X \<and> Wa D Y f a \<and> b \<in> Y \<longrightarrow>
             aa \<le>\<^sub>D b \<or>  b \<le>\<^sub>D aa")
 apply blast apply (thin_tac "\<exists>x. Wa D x f a \<and> aa \<in> x") 
  apply (thin_tac "\<exists>x. Wa D x f a \<and> b \<in> x") apply (rule allI)+
  apply (rule impI) apply (erule conjE)+
  apply (subgoal_tac "ordered_set D") prefer 2 apply (simp add:S_inductive_set_def)
  apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y in BNTr7, assumption+)
  apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (case_tac "X \<subseteq> Y")
  apply (frule_tac A = X and B = Y and c = aa in subsetD, assumption+)
  apply (subgoal_tac "well_ordered_set (Iod D Y)") prefer 2 apply (simp add:Wa_def)
  apply (simp add:well_ordered_set_def) apply (erule conjE)
  apply (thin_tac "\<forall>X. X \<subseteq> carrier (Iod D Y) \<and> X \<noteq> {} \<longrightarrow>
              Ex (minimum_elem (Iod D Y) X)")
  apply (simp add:tordered_set_def) apply (erule conjE)+
  apply (subgoal_tac "aa \<in> carrier (Iod D Y)")
  apply (subgoal_tac "b \<in> carrier (Iod D Y)")
  apply (subgoal_tac "aa \<le>\<^sub>(Iod D Y) b \<or> b \<le>\<^sub>(Iod D Y) aa")
   prefer 2 apply simp
  apply (simp add:Iod_def) apply (simp add:Iod_def) apply (simp add:Iod_def)
 apply simp
  apply (frule_tac A = Y and B = X and c = b in subsetD, assumption+)
  apply (subgoal_tac "well_ordered_set (Iod D X)") prefer 2 apply (simp add:Wa_def)
  apply (simp add:well_ordered_set_def) apply (erule conjE)
  apply (thin_tac "\<forall>Xa. Xa \<subseteq> carrier (Iod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (Iod D X) Xa x)")
  apply (simp add:tordered_set_def) apply (erule conjE)+
  apply (subgoal_tac "aa \<in> carrier (Iod D X)")
  apply (subgoal_tac "b \<in> carrier (Iod D X)")
  apply (subgoal_tac "aa \<le>\<^sub>(Iod D X) b \<or>  b \<le>\<^sub>(Iod D X) aa")
  prefer 2 apply simp apply (simp add:Iod_def)
  apply (simp add:Iod_def) apply (simp add:Iod_def)
apply (rule allI)
 apply (rule impI) apply (erule conjE)+
 apply (frule_tac A = X in nonempty_ex)
 apply (subgoal_tac "\<forall>z. z \<in> X \<longrightarrow> (\<exists>x. minimum_elem (Iod D (\<Union>{W. Wa D W f a})) X x)") apply blast apply (thin_tac "\<exists>x. x \<in> X")
 apply (rule allI) apply (rule impI)
 apply (frule_tac A = X and B = "carrier (Iod D (\<Union>{W. Wa D W f a}))" and c = z in subsetD, assumption+)
 apply (subgoal_tac "z \<in> \<Union>{W. Wa D W f a}") prefer 2 apply (simp add:Iod_def)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>Z. Wa D Z f a \<and> z \<in> Z \<longrightarrow> (\<exists>x. minimum_elem (Iod D (\<Union>{W. Wa D W f a})) X x)") apply blast apply (thin_tac "\<exists>x. Wa D x f a \<and> z \<in> x")
 apply (rule allI) apply (rule impI) apply (erule conjE)
apply (case_tac "minimum_elem (Iod D (\<Union>{W. Wa D W f a})) X z")
 apply blast
 apply (subgoal_tac "segment (Iod D X) z \<subseteq> carrier (Iod D Z)")
 apply (subgoal_tac "segment (Iod D X) z \<noteq> {}")
 apply (subgoal_tac "well_ordered_set (Iod D Z)") prefer 2 apply (simp add:Wa_def)
 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "\<exists>x. minimum_elem (Iod D Z) (segment (Iod D X) z) x")
 prefer 2 apply simp apply (thin_tac "tordered_set (Iod D Z) \<and> (\<forall>X. X \<subseteq> carrier (Iod D Z) \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem (Iod D Z) X x))")
 apply (subgoal_tac "\<forall>x. minimum_elem (Iod D Z) (segment (Iod D X) z) x \<longrightarrow>
 (\<exists>x. minimum_elem (Iod D (\<Union>{W. Wa D W f a})) X x)") apply blast
 apply (thin_tac "\<exists>x. minimum_elem (Iod D Z) (segment (Iod D X) z) x")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "minimum_elem (Iod D (\<Union>{W. Wa D W f a})) X x")
 apply blast
apply (simp add: minimum_elem_def) apply (erule conjE)+
 apply (rule conjI)
 apply (simp add:Iod_def segment_def) apply (rule ballI)
 apply (case_tac "xa \<in> segment (Iod D X) z")
  apply (subgoal_tac " x \<le>\<^sub>(Iod D Z) xa") prefer 2 apply simp
  apply (thin_tac "\<forall>xa\<in>segment (Iod D X) z.  x \<le>\<^sub>(Iod D Z) xa")
 apply (simp add:Iod_def)
 apply (thin_tac "z \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
 apply (thin_tac "segment (Iod D X) z \<subseteq> carrier (Iod D Z)")
 apply (thin_tac "segment (Iod D X) z \<noteq> {}")
 apply (thin_tac "\<forall>xa\<in>segment (Iod D X) z.  x \<le>\<^sub>(Iod D Z) xa")
 apply (thin_tac "\<exists>x\<in>X. \<not>  z \<le>\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
 apply (subgoal_tac "\<not> xa <\<^sub>(Iod D X) z") prefer 2 apply (simp add:segment_def)
  apply (rule contrapos_pp, simp+) apply (simp add:Iod_def)
  apply (thin_tac "xa \<notin> segment (Iod D X) z")
  apply (subgoal_tac "z \<le>\<^sub>D xa")
  apply (simp add:Iod_def segment_def ord_neq_def)
  apply (erule conjE)+
  apply (subgoal_tac "ordered_set D")
 apply (rule_tac a = x and b = z and c = xa in ordering_axiom3 [of "D"], assumption+)
 apply (frule_tac A = X and B = "\<Union>{W. Wa D W f a}" and C = "carrier D" in subset_trans, assumption+) apply (simp add:subsetD)
 apply (subgoal_tac "Z \<subseteq> \<Union>{W. Wa D W f a}")
 apply (frule_tac A = Z and B = "\<Union>{W. Wa D W f a}" and C = "carrier D" in subset_trans, assumption+) apply (simp add:subsetD)
 apply (subgoal_tac "Z \<in> {W. Wa D W f a}") apply (thin_tac "Wa D Z f a")
 apply blast apply simp
 apply (frule_tac A = X and B = "\<Union>{W. Wa D W f a}" and C = "carrier D" in subset_trans, assumption+) apply (simp add:subsetD) apply assumption+
 apply (simp add:S_inductive_set_def)
 apply (frule_tac A = X and B = "carrier (Iod D (\<Union>{W. Wa D W f a}))" and 
  c = xa in subsetD, assumption+)
 apply (subgoal_tac "\<exists>Y\<in>{W. Wa D W f a}. xa \<in> Y") 
 prefer 2 apply (simp add:Iod_def) apply simp
  apply (subgoal_tac "\<forall>Y. Wa D Y f a \<and> xa \<in> Y \<longrightarrow> z \<le>\<^sub>D xa")
  apply blast apply (thin_tac "\<exists>x. Wa D x f a \<and> xa \<in> x")
  apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "ordered_set D") 
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = Z and ?W2.0 = Y in BNTr7, assumption+)
 apply (simp add:WWa_def) apply (simp add:WWa_def) 
 apply (case_tac "Z \<subseteq> Y")
  apply (frule_tac A = Z and B = Y and c = z in subsetD, assumption+)
  apply (subgoal_tac "\<not> xa <\<^sub>(Iod D Y) z")
 apply (subgoal_tac "tordered_set (Iod D Y)") 
  apply (subgoal_tac "z \<in> carrier (Iod D Y)")
  apply (subgoal_tac "xa \<in> carrier (Iod D Y)")
 apply (frule_tac D = "Iod D Y" and a = xa and b = z in tordering_not2, assumption+)
 apply (simp add:Iod_def)
 apply (simp add:Iod_def) apply (simp add:Iod_def) 
  apply (subgoal_tac "well_ordered_set (Iod D Y)")
   apply (simp add:well_ordered_set_def)
  apply (simp add:Wa_def)
 apply (simp add:Iod_def ord_neq_def)
apply simp
 apply (frule_tac A = Y and B = Z and c = xa in subsetD, assumption+)
  apply (subgoal_tac "\<not> xa <\<^sub>(Iod D Z) z")
 apply (subgoal_tac "tordered_set (Iod D Z)") 
  apply (subgoal_tac "z \<in> carrier (Iod D Z)")
  apply (subgoal_tac "xa \<in> carrier (Iod D Z)")
 apply (frule_tac D = "Iod D Z" and a = xa and b = z in tordering_not2, assumption+)
 apply (simp add:Iod_def)
 apply (simp add:Iod_def) apply (simp add:Iod_def) 
  apply (subgoal_tac "well_ordered_set (Iod D Z)")
   apply (simp add:well_ordered_set_def)
  apply (simp add:Wa_def)
 apply (simp add:Iod_def ord_neq_def) 
 apply (simp add:S_inductive_set_def)
 apply (simp add:minimum_elem_def)
 apply (subgoal_tac "\<forall>x\<in>X. \<not>  z \<le>\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x \<longrightarrow> segment (Iod D X) z \<noteq> {}") apply blast apply (thin_tac "\<exists>x\<in>X. \<not>  z \<le>\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
 apply (rule ballI) apply (rule impI)
  apply (thin_tac "segment (Iod D X) z \<subseteq> carrier (Iod D Z)")
 apply (frule_tac A = X and B = "carrier (Iod D (\<Union>{W. Wa D W f a}))" and c = x in subsetD, assumption+)
 apply (subgoal_tac "\<exists>Y\<in>{W. Wa D W f a}. x \<in> Y") prefer 2 apply (simp add:Iod_def)
 apply (subgoal_tac "\<forall>Y\<in>{W. Wa D W f a}. x \<in> Y \<longrightarrow> segment (Iod D X) z \<noteq> {}")
 apply blast apply (thin_tac "\<exists>Y\<in>{W. Wa D W f a}. x \<in> Y")
 apply (rule ballI) apply (rule impI) apply simp
 apply (subgoal_tac "ordered_set D") 
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = Z and ?W2.0 = Y in BNTr7, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (case_tac "Z \<subseteq> Y")
 apply (frule_tac A = Z and B = Y and c = z in subsetD, assumption+)
 apply (subgoal_tac "\<not> z \<le>\<^sub>(Iod D Y) x")
 apply (subgoal_tac "tordered_set (Iod D Y)")
 apply (subgoal_tac "z \<in> carrier (Iod D Y)")
 apply (subgoal_tac "x \<in> carrier (Iod D Y)")
 apply (frule_tac D = "Iod D Y" and a = z and b = x in tordering_not, assumption+)
 apply (simp add:segment_def)
  apply (subgoal_tac "x \<in> carrier (Iod D X)")
  apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (simp add:Iod_def ord_neq_def)
  apply blast
  apply (simp add:Iod_def) apply (simp add:Iod_def) apply (simp add:Iod_def)
  apply (subgoal_tac "well_ordered_set (Iod D Y)") apply (simp add:well_ordered_set_def)
 apply (simp add:Wa_def)
 apply (simp add:Iod_def) apply simp
 
 apply (frule_tac A = Y and B = Z and c = x in subsetD, assumption+)
 apply (subgoal_tac "\<not> z \<le>\<^sub>(Iod D Z) x")
 apply (subgoal_tac "tordered_set (Iod D Z)")
 apply (subgoal_tac "z \<in> carrier (Iod D Z)")
 apply (subgoal_tac "x \<in> carrier (Iod D Z)")
 apply (frule_tac D = "Iod D Z" and a = z and b = x in tordering_not, assumption+)
 apply (simp add:segment_def)
  apply (subgoal_tac "x \<in> carrier (Iod D X)")
  apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (simp add:Iod_def ord_neq_def)
  apply blast
  apply (simp add:Iod_def) apply (simp add:Iod_def) apply (simp add:Iod_def)
  apply (subgoal_tac "well_ordered_set (Iod D Z)") apply (simp add:well_ordered_set_def)
 apply (simp add:Wa_def)
 apply (simp add:Iod_def) apply (simp add:S_inductive_set_def)
(**-- segment (Iod D X) z \<subseteq> carrier (Iod D Z) ---**)
 apply (rule subsetI)
  apply (simp add:segment_def)
  apply (erule conjE)
  apply (subgoal_tac "\<exists>Y\<in>{W. Wa D W f a}. x \<in> Y")
  apply (subgoal_tac "\<forall>Y\<in>{W. Wa D W f a}. x \<in> Y \<longrightarrow> x \<in> carrier (Iod D Z)")
  apply blast apply (thin_tac "\<exists>Y\<in>{W. Wa D W f a}. x \<in> Y")
 apply (rule ballI) apply (rule impI) apply simp
 apply (subgoal_tac "ordered_set D") prefer 2 apply (simp add:S_inductive_set_def)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = Y and ?W2.0 = Z in  
  BNTr7, assumption+)    
 apply (simp add:WWa_def Wa_def) apply (simp add:WWa_def Wa_def)
 apply (case_tac "Y \<subseteq> Z")
 apply (frule_tac A = Y and B = Z and c = x in subsetD, assumption+)
 apply (simp add:Iod_def) apply simp
 apply (subgoal_tac "Z \<subset> Y") prefer 2 apply (simp add:subset_def)
 apply blast apply (thin_tac "Z \<subseteq> Y") apply (thin_tac "\<not> Y \<subseteq> Z")
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = Z and ?W2.0 = Y in BNTr6, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply assumption
 apply (subgoal_tac "\<forall>b\<in>carrier (Iod D Y). ord_equiv (Iod D Z) (Iod D (segment (Iod D Y) b)) \<longrightarrow>  x \<in> carrier (Iod D Z)")
 apply blast apply (thin_tac "\<exists>b\<in>carrier (Iod D Y).
             ord_equiv (Iod D Z) (Iod D (segment (Iod D Y) b))")
 apply (rule ballI) apply (rule impI) apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>f. ord_isom (Iod D Z) (Iod D (segment (Iod D Y) b)) f \<longrightarrow> x \<in> carrier (Iod D Z)") apply blast
  apply (thin_tac "\<exists>f. ord_isom (Iod D Z) (Iod D (segment (Iod D Y) b)) f")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "well_ordered_set (Iod D Z)")
 apply (subgoal_tac "well_ordered_set (Iod D (segment (Iod D Y) b))")
 apply (subgoal_tac "z \<in> carrier (Iod D Z)") 
 apply (frule_tac S = "Iod D Z" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod D (segment (Iod D Y) b)" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod D Z" and E = "Iod D (segment (Iod D Y) b)" and f = fa and a = z in ord_isom_mem, assumption+)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = Z and ?W2.0 = Y and b = b and g = fa in BNTr4_1, assumption+)
 apply (simp add:WWa_def Wa_def) apply (simp add:WWa_def Wa_def) 
 apply (simp add:Iod_def) apply assumption apply simp 
 apply (subgoal_tac "z <\<^sub>(Iod D Y) b") prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "x \<in> carrier (Iod D (segment (Iod D Y) b))")
 apply (frule_tac D = "Iod D Z" and E = "Iod D (segment (Iod D Y) b)" and f = fa and b = x in ord_isom_surj, assumption+)
 apply (subgoal_tac "carrier (Iod D Z) = Z") apply simp apply (simp add:Iod_def)
 apply (subgoal_tac "x <\<^sub>(Iod D Y) b")
 apply (simp add:Iod_def segment_def)
 apply (subgoal_tac "Y \<subseteq> carrier D") apply (frule_tac A = Y and B = "carrier D" and c = x in subsetD, assumption+)
 apply (subgoal_tac "Z \<subseteq> carrier D") apply (frule_tac A = Z and B = "carrier D" and c = z in subsetD, assumption+)
 apply (subgoal_tac "b \<in> Y") prefer 2 apply (simp add:Iod_def)
 apply (subgoal_tac "x <\<^sub>(Iod D Y) z") prefer 2 apply (simp add:Iod_def ord_neq_def)
 apply (subgoal_tac "ordered_set (Iod D Y)") 
 apply (frule_tac D = "Iod D Y" and a = x and b = z and c = b in ord_neq_trans)
 apply (simp add:Iod_def)
 apply (frule_tac A = Z and B = Y in psubset_imp_subset)
 apply (frule_tac A = Z and B = Y and c = z in subsetD, assumption+)
 apply (simp add:Iod_def)
 apply (frule_tac A = Z and B = Y in psubset_imp_subset)
 apply (frule_tac A = Z and B = Y and c = z in subsetD, assumption+)
 apply (simp add:Wa_def well_ordered_set_is_ordered_set)
 apply (simp add:Wa_def) apply (simp add:Wa_def)
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "well_ordered_set (Iod D Y)")
 apply (frule_tac S = "Iod D Y" and a = b in segment_well_ordered_set)
  apply assumption
  apply (subgoal_tac "Iod (Iod D Y) (segment (Iod D Y) b) = Iod D (segment (Iod D Y) b)") apply simp
  apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:Iod_def segment_def)
 apply (simp add:WWa_def Wa_def) apply (simp add:WWa_def Wa_def)
 apply (simp add:WWa_def Wa_def)
 apply (subgoal_tac "x \<in> X")
 apply (frule_tac A = X and B = "carrier (Iod D (\<Union>{W. Wa D W f a}))" and c = x in subsetD) apply (simp add:Iod_def)
 apply (simp add:Iod_def) apply (simp add:Iod_def)
apply (rule conjI)
 apply (subgoal_tac "ordered_set D")
 apply (frule_tac D = D and f = f and a = a in BNTr2, assumption+) 
 apply simp apply (simp add:WWa_def)
 apply blast apply (simp add:S_inductive_set_def)
apply (rule conjI)
 apply (rule ballI) apply simp apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (subgoal_tac "\<forall>xa. Wa D xa f a \<and> x \<in> xa \<longrightarrow> a \<le>\<^sub>D x")
 apply blast apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (simp add:Wa_def)
apply (rule ballI)
 apply (case_tac "ExPre (Iod D (\<Union>{W. Wa D W f a})) x")
 apply simp
 apply (subgoal_tac "\<forall>xa. Wa D xa f a \<and> x \<in> xa \<longrightarrow> f (Pre (Iod D (\<Union>{W. Wa D W f a})) x) = x") apply blast
 apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (rename_tac x X)
 apply (subgoal_tac "ExPre (Iod D X) x")
 apply (subgoal_tac "(Pre (Iod D (\<Union>{W. Wa D W f a})) x) = Pre (Iod D X) x")
 apply simp apply (simp add:Wa_def)

 apply (rule_tac S = "Iod D (\<Union>{W. Wa D W f a})" and a = x and ?a1.0 = "Pre (Iod D X) x" in UniquePre, assumption+)
 apply (subst Iod_def) apply simp apply blast
 apply assumption+
 apply (subgoal_tac "well_ordered_set (Iod D X)") prefer 2 apply (simp add:Wa_def)
 apply (frule_tac S = "Iod D X" and a = x in Pre_element)
 apply (simp add:Iod_def) apply assumption
 apply (erule conjE)+
 apply (rule conjI) apply (subgoal_tac "carrier (Iod D X) = X") apply simp
 apply (subgoal_tac "carrier (Iod D (\<Union>{W. Wa D W f a})) = \<Union>{W. Wa D W f a}")
 apply simp apply blast
apply (simp add:Iod_def) apply (simp add:Iod_def)
 apply (rule conjI) apply (simp add:Iod_def ord_neq_def)
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>z\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
 Pre (Iod D X) x <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) z \<and> z <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x \<longrightarrow> False") apply (thin_tac "\<forall>y\<in>carrier (Iod D X).
                 Pre (Iod D X) x <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
 apply blast
 apply (thin_tac "\<exists>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
 Pre (Iod D X) x <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<and> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "\<exists>Z\<in>{W. Wa D W f a}. z \<in> Z") prefer 2 
 apply (simp add:Iod_def) apply simp
 apply (subgoal_tac "\<forall>Z. Wa D Z f a \<and> z \<in> Z \<longrightarrow> False") apply blast
  apply (thin_tac "\<exists>x. Wa D x f a \<and> z \<in> x") apply (rule allI) apply (rule impI)apply (erule conjE)+
apply (subgoal_tac "ordered_set D")
apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Z in BNTr7, assumption+)
 apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (case_tac "Z \<subseteq> X")
 apply (subgoal_tac "z \<in> carrier (Iod D X)")
 apply (subgoal_tac "Pre (Iod D X) x <\<^sub>(Iod D X) z \<longrightarrow> \<not>  z <\<^sub>(Iod D X) x")
 prefer 2 apply simp
 apply (subgoal_tac "Pre (Iod D X) x <\<^sub>(Iod D X) z")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D X).
              Pre (Iod D X) x <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
 apply simp
 apply (simp add:Iod_def ord_neq_def)
 apply (simp add:Iod_def ord_neq_def)
 apply (frule_tac A = Z and B = X and c = z in subsetD, assumption+)
  apply (simp add:Iod_def) apply simp
  apply (subgoal_tac "X \<subset> Z") prefer 2 apply blast
  apply (thin_tac "X \<subseteq> Z") apply (thin_tac "\<not> Z \<subseteq> X")
 apply (subgoal_tac "ordered_set D") prefer 2 apply (simp add:S_inductive_set_def) 
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Z in BNTr6, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def) 
  apply assumption
 apply (subgoal_tac "\<forall>b\<in>carrier (Iod D Z). ord_equiv (Iod D X) (Iod D (segment (Iod D Z) b)) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>b\<in>carrier (Iod D Z).
             ord_equiv (Iod D X) (Iod D (segment (Iod D Z) b))")
 apply (rule ballI) apply (rule impI)
 apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>h. ord_isom (Iod D X) (Iod D (segment (Iod D Z) b)) h \<longrightarrow>
  False") apply blast
 apply (thin_tac "Ex (ord_isom (Iod D X) (Iod D (segment (Iod D Z) b)))")
 apply (rule allI) apply (rule impI)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Z and b = b and g = h in BNTr4_1, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (simp add:Iod_def) apply assumption
 apply (subgoal_tac "x \<in> carrier (Iod D X)") prefer 2 apply (simp add:Iod_def)
 apply (subgoal_tac "ordered_set (Iod D X)")
 apply (subgoal_tac "ordered_set (Iod D (segment (Iod D Z) b))")
 apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Z) b)" and f = h and a = x in ord_isom_mem, assumption+)
 apply simp
 apply (subgoal_tac "z \<in> carrier (Iod D X)")
 apply (subgoal_tac "Pre (Iod D X) x <\<^sub>(Iod D X) z \<longrightarrow> \<not> z <\<^sub>(Iod D X) x")
 prefer 2 apply simp
 apply (subgoal_tac "Pre (Iod D X) x <\<^sub>(Iod D X) z")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D X).
              Pre (Iod D X) x <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
 apply simp
 apply (simp add:Iod_def ord_neq_def)
  apply (thin_tac "\<forall>y\<in>carrier (Iod D X).
              Pre (Iod D X) x <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
  apply (thin_tac "Pre (Iod D X) x <\<^sub>(Iod D X) z \<longrightarrow> \<not>  z <\<^sub>(Iod D X) x")
  apply (thin_tac "\<forall>x\<in>X. h x = x")
 apply (simp add:Iod_def ord_neq_def)
 apply (subgoal_tac "x <\<^sub>D b") prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "z <\<^sub>D x") prefer 2 apply (simp add:Iod_def ord_neq_def)
  apply (subgoal_tac "z \<in> carrier (Iod D (segment (Iod D Z) b))")
  apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Z) b)" and f = h and b = z in ord_isom_surj, assumption+)
  apply (subgoal_tac "\<forall>aa\<in>carrier (Iod D X). z = h aa \<longrightarrow> z \<in> carrier (Iod D X)") apply blast apply (thin_tac "\<exists>a\<in>carrier (Iod D X). z = h a")
  apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "aa \<in> X") apply simp apply (simp add:Iod_def)
  apply (frule_tac A = X and B = Z in psubset_imp_subset)
 apply (frule_tac A = X and B = Z and c = x in subsetD, assumption+)
  apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
  apply (thin_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
  apply (thin_tac "ExPre (Iod D (\<Union>{W. Wa D W f a})) x")
  apply (thin_tac "ExPre (Iod D X) x")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D X). Pre (Iod D X) x <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
 apply (subgoal_tac "z <\<^sub>D b")
 apply (simp add:Iod_def segment_def ord_neq_def) 
  apply (subgoal_tac "z \<in> carrier D")
  apply (subgoal_tac "x \<in> carrier D")
  apply (subgoal_tac "b \<in> carrier D")
 apply (frule_tac a = z and b = x and c = b in ord_neq_trans [of "D"], assumption+)
 apply (subgoal_tac "Z \<subseteq> carrier D")
 apply (subgoal_tac "b \<in> Z")
 apply (rule_tac A = Z and B = "carrier D" and c = b in subsetD, assumption+)
  apply (simp add:Iod_def) apply (simp add:Wa_def)
 apply (frule_tac A = X and B = Z and c = x in subsetD, assumption+)
 apply (subgoal_tac "Z \<subseteq> carrier D") apply (simp add:subsetD) 
 apply (simp add:Wa_def)
 apply (subgoal_tac "Z \<subseteq> carrier D") apply (rule_tac A = Z and B = "carrier D" and c = z in subsetD) apply (simp add:Wa_def) apply assumption
 apply (simp add:Wa_def)
 apply (subgoal_tac "well_ordered_set (Iod D Z)")
 apply (frule_tac S = "Iod D Z" and a = b in segment_well_ordered_set)
  apply assumption
  apply (frule_tac S = "Iod (Iod D Z) (segment (Iod D Z) b)" in well_ordered_set_is_ordered_set)
  apply (subgoal_tac "Iod (Iod D Z) (segment (Iod D Z) b) = Iod D (segment (Iod D Z) b)") apply simp
 apply (rule Iod_sub_sub, assumption+) apply (rule subsetI) apply (simp add:segment_def Iod_def) apply (simp add:Wa_def) apply (simp add:Wa_def)
 apply (simp add:well_ordered_set_is_ordered_set) apply (simp add:S_inductive_set_def) 
(**------ ExPre --------**)  
apply (unfold ExPre_def)
apply (subgoal_tac "\<forall>xa. xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a})) \<and>
 xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x \<and> \<not> (\<exists>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})). xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<and> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x) \<longrightarrow>
 (\<exists>xa. xa \<in> carrier (Iod D X) \<and> xa <\<^sub>(Iod D X) x \<and> \<not> (\<exists>y\<in>carrier (Iod D X).  xa <\<^sub>(Iod D X) y \<and>  y <\<^sub>(Iod D X) x))") apply blast
apply (thin_tac "\<exists>xa. xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a})) \<and>
 xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x \<and> \<not> (\<exists>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})). xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<and> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x)")
apply (rule allI) apply (rule impI) apply (erule conjE)+
apply (subgoal_tac "\<exists>Z\<in>{W. Wa D W f a}. xa \<in> Z") 
 prefer 2 apply (simp add:Iod_def) apply simp
 apply (subgoal_tac "\<forall>Z. Wa D Z f a \<and> xa \<in> Z \<longrightarrow> (\<exists>xa. xa \<in> carrier (Iod D X) \<and> xa <\<^sub>(Iod D X) x \<and> (\<forall>y\<in>carrier (Iod D X). xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x))") apply blast apply (thin_tac "\<exists>x. Wa D x f a \<and> xa \<in> x")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "ordered_set D")
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Z in BNTr7, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (case_tac "Z \<subseteq> X")
 apply (frule_tac A = Z and B = X and c = xa in subsetD, assumption+)
 apply (subgoal_tac "xa <\<^sub>(Iod D X) x")
 apply (subgoal_tac "\<forall>y\<in>carrier (Iod D X). xa <\<^sub>(Iod D X) y \<longrightarrow> \<not> y <\<^sub>(Iod D X) x")
 apply (subgoal_tac "xa \<in> carrier (Iod D X)") apply blast
 apply (simp add:Iod_def)
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "y \<in>carrier (Iod D (\<Union>{W. Wa D W f a}))")
 apply (subgoal_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow>
             \<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x") prefer 2 apply simp
  apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
  xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply (subgoal_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y") apply simp
 apply (simp add:Iod_def ord_neq_def)
  apply (thin_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply (simp add:Iod_def ord_neq_def)
   apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
   apply (thin_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
   apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
    xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
   apply (thin_tac "xa <\<^sub>(Iod D X) x")
   apply (thin_tac "xa <\<^sub>(Iod D X) y")
   apply (thin_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
   apply (thin_tac "xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
  apply (simp add:Iod_def CollectI) apply blast
  apply (simp add:Iod_def ord_neq_def) apply simp
  apply (subgoal_tac "X \<subset> Z") prefer 2 apply blast
   apply (thin_tac "X \<subseteq> Z") apply (thin_tac "\<not> Z \<subseteq> X")
  apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Z in
  BNTr6, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
   apply assumption
  apply (subgoal_tac "\<forall>b\<in>carrier (Iod D Z). ord_equiv (Iod D X) 
  (Iod D (segment (Iod D Z) b)) \<longrightarrow> (\<exists>xa. xa \<in> carrier (Iod D X) \<and>
  xa <\<^sub>(Iod D X) x \<and> (\<forall>y\<in>carrier (Iod D X).  xa <\<^sub>(Iod D X) y \<longrightarrow> \<not> y <\<^sub>(Iod D X) x))") apply blast
  apply (thin_tac " \<exists>b\<in>carrier (Iod D Z).
             ord_equiv (Iod D X) (Iod D (segment (Iod D Z) b))")
  apply (rule ballI) apply (rule impI)
  apply (simp add:ord_equiv_def)
  apply (subgoal_tac "\<forall>h. ord_isom (Iod D X) (Iod D (segment (Iod D Z) b)) h \<longrightarrow> (\<exists>xa. xa \<in> carrier (Iod D X) \<and> xa <\<^sub>(Iod D X) x \<and> (\<forall>y\<in>carrier (Iod D X).  xa <\<^sub>(Iod D X) y \<longrightarrow> \<not> y <\<^sub>(Iod D X) x))") apply blast
  apply (thin_tac "\<exists>f. ord_isom (Iod D X) (Iod D (segment (Iod D Z) b)) f")
  apply (rule allI) apply (rule impI)
  apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Z and b = b and g = h in BNTr4_1, assumption+) apply (simp add:WWa_def)
  apply (simp add:WWa_def) apply (simp add:Iod_def) apply assumption
  prefer 2 apply (simp add:S_inductive_set_def)
  apply (subgoal_tac "ordered_set (Iod D X)")
  apply (subgoal_tac "ordered_set (Iod D (segment (Iod D Z) b))")
  apply (subgoal_tac "x \<in> carrier (Iod D X)") prefer 2 apply (simp add:Iod_def)
  apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Z) b)" and f = h and a = x in ord_isom_mem, assumption+) apply simp
  apply (subgoal_tac "xa \<in> carrier (Iod D X)")
  apply (subgoal_tac "xa <\<^sub>(Iod D X) x")
  apply (subgoal_tac "\<forall>y\<in>carrier (Iod D X).  xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x") apply blast
  apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "y \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
  apply (subgoal_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow>
             \<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
 prefer 2 apply simp
  apply (subgoal_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
   xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply simp
  apply (simp add:Iod_def ord_neq_def) apply (simp add:Iod_def ord_neq_def)
  apply (thin_tac "\<forall>x\<in>carrier D. x \<le>\<^sub>D (f x)")
  apply (thin_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
  apply (thin_tac "xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
  xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply (thin_tac "xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply (subgoal_tac "X \<subseteq> \<Union>{W. Wa D W f a}")
  apply (subgoal_tac "y \<in> X") prefer 2 apply (simp add:Iod_def)
  apply (frule_tac A = X and B = "\<Union>{W. Wa D W f a}" and c = y in subsetD, assumption+)
  apply (simp add:Iod_def)
  apply (rule subsetI) apply simp apply blast
   apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
   xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply (simp add:Iod_def ord_neq_def)
apply (thin_tac " well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
 apply (thin_tac "xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
  xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
 apply (subgoal_tac "xa \<in> carrier (Iod D (segment (Iod D Z) b))")  
 apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Z) b)" and f = h and b = xa in ord_isom_surj, assumption+)
 apply (subgoal_tac "\<forall>aa\<in>carrier (Iod D X). xa = h aa \<longrightarrow> xa \<in> carrier (Iod D X)") apply blast apply (thin_tac "\<exists>a\<in>carrier (Iod D X). xa = h a")
 apply (rule ballI) apply (rule impI) apply (subgoal_tac "aa \<in> X") 
 apply simp apply (simp add:Iod_def)
 apply (subgoal_tac "xa <\<^sub>(Iod D Z) b")
  apply (simp add:Iod_def segment_def ord_neq_def)
 apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "ord_isom (Iod D X) (Iod D (segment (Iod D Z) b)) h")
 apply (thin_tac "ordered_set (Iod D X)")
 apply (thin_tac "ordered_set (Iod D (segment (Iod D Z) b))")
 apply (thin_tac "x \<in> carrier (Iod D X)")
 apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
  apply (subgoal_tac "xa \<in> carrier D")
  apply (subgoal_tac "x \<in> carrier D")
  apply (subgoal_tac "b \<in> carrier D")
 apply (frule_tac a = xa and b = x and c = b in ordering_axiom3, assumption+)
 apply simp apply (rule contrapos_pp, simp+)
 apply (frule_tac a = x and b = b in ordering_axiom2, assumption+) apply simp
 apply (simp add:Wa_def) apply (erule conjE)+ apply (simp add:subsetD)
 apply (simp add:Wa_def) apply (erule conjE)+ apply (simp add:subsetD)
 apply (simp add:Wa_def) apply (erule conjE)+ apply (simp add:subsetD)
  apply (thin_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})).
   xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x")
  apply (subgoal_tac "well_ordered_set (Iod D Z)")
  apply (frule_tac S = "Iod D Z" and a = b in segment_well_ordered_set, assumption+)
  apply (subgoal_tac "Iod (Iod D Z) (segment (Iod D Z) b) = Iod D (segment (Iod D Z) b)") apply simp apply (simp add:well_ordered_set_is_ordered_set)
  apply (rule Iod_sub_sub, assumption+)
  apply (rule subsetI) apply (simp add:Iod_def segment_def)
  apply (simp add:Wa_def) apply (simp add:Wa_def) apply (simp add:Wa_def well_ordered_set_is_ordered_set)
 apply (fold ExPre_def)
 apply simp apply (rule impI)
apply (subgoal_tac "\<forall>X. Wa D X f a \<and> x \<in> X \<longrightarrow> Sup D (segment (Iod D (\<Union>{W. Wa D W f a})) x) = x") apply blast apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (rule allI) apply (rule impI)
 apply (erule conjE)+
apply (subgoal_tac "segment (Iod D (\<Union>{W. Wa D W f a})) x = segment (Iod D X) x") apply simp
apply (subgoal_tac "\<not>  ExPre (Iod D X) x")
 apply (simp add:Wa_def)
apply (rule contrapos_pp, simp+)
 apply (thin_tac "segment (Iod D (\<Union>{W. Wa D W f a})) x = segment (Iod D X) x")
 apply (subgoal_tac "ExPre (Iod D (\<Union>{W. Wa D W f a})) x") apply simp
 apply (thin_tac "\<not> ExPre (Iod D (\<Union>{W. Wa D W f a})) x")
 apply (simp add: ExPre_def)
 apply (subgoal_tac "\<forall>xa.  xa \<in> carrier (Iod D X) \<and> xa <\<^sub>(Iod D X) x \<and>  (\<forall>y\<in>carrier (Iod D X). xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x) \<longrightarrow>(\<exists>xa. xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a})) \<and> xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x \<and> (\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})). xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x))") apply blast
 apply (thin_tac "\<exists>xa.  xa \<in> carrier (Iod D X) \<and> xa <\<^sub>(Iod D X) x \<and> (\<forall>y\<in>carrier (Iod D X). xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x)")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "xa \<in> carrier (Iod D (\<Union>{W. Wa D W f a})) \<and>  xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x \<and> (\<forall>y\<in>carrier (Iod D (\<Union>{W. Wa D W f a})). xa <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y \<longrightarrow> \<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x)")
 apply blast
apply (rule conjI)  
 apply (subgoal_tac "X \<subseteq> \<Union>{W. Wa D W f a}")
 apply (subgoal_tac "xa \<in> X") prefer 2  apply (simp add:Iod_def)
 apply (frule_tac A = X and B = "\<Union>{W. Wa D W f a}" and c = xa in subsetD, assumption+)
 apply (simp add:Iod_def)
 apply (rule subsetI) apply simp apply blast
 apply (rule conjI)
  apply (simp add:Iod_def ord_neq_def)
 apply (rule ballI) apply (rule impI)
(**-- overup trick --**)
 apply (subgoal_tac "\<exists>Y\<in>{W. Wa D W f a}. y \<in> Y")
 apply (subgoal_tac "\<forall>Y\<in>{W. Wa D W f a}. y \<in> Y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x") apply blast apply (thin_tac "\<exists>Y\<in>{W. Wa D W f a}. y \<in> Y")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "ordered_set D")
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y in BNTr7, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (case_tac "Y \<subseteq> X")
 apply (frule_tac A = Y and B = X and c = y in subsetD, assumption+)
 apply (subgoal_tac "y \<in> carrier (Iod D X)") prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac "xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x") 
  prefer 2 apply simp apply (thin_tac "\<forall>y\<in>carrier (Iod D X).  xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
  apply (subgoal_tac "xa <\<^sub>(Iod D X) y") apply simp
  apply (simp add:Iod_def ord_neq_def) apply (simp add:Iod_def ord_neq_def)
 (*-- overup -- X \<subseteq> Y \<or> Y \<subseteq> X; \<not> Y \<subseteq> X -- *)
apply simp apply (subgoal_tac "X \<subset> Y") apply (thin_tac "X \<subseteq> Y") apply (thin_tac "\<not> Y \<subseteq> X")
 apply (subgoal_tac "ordered_set D")
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y in BNTr6, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply assumption+
 apply (subgoal_tac "\<forall>b\<in>carrier (Iod D Y). ord_equiv (Iod D X) (Iod D (segment (Iod D Y) b)) \<longrightarrow> (\<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x)")
 apply blast 
  apply (thin_tac "\<exists>b\<in>carrier (Iod D Y). ord_equiv (Iod D X) (Iod D (segment (Iod D Y) b))")
 apply (rule ballI) apply (rule impI) apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>h. ord_isom (Iod D X) (Iod D (segment (Iod D Y) b)) h \<longrightarrow> (\<not> y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x)") apply blast
 apply (thin_tac "Ex (ord_isom (Iod D X) (Iod D (segment (Iod D Y) b)))")
 apply (rule allI) apply (rule impI)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y and
 b = b and g = h in BNTr4_1, assumption+)
  apply (simp add:WWa_def) apply (simp add:WWa_def) apply (simp add:Iod_def)
  apply assumption
  apply (thin_tac "y \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
 apply (case_tac "y <\<^sub>(Iod D Y) b")
  apply (subgoal_tac "ordered_set (Iod D X)")
  apply (subgoal_tac "ordered_set (Iod D (segment (Iod D Y) b))")
  apply (subgoal_tac "y \<in> carrier (Iod D (segment (Iod D Y) b))")
  apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Y) b)" and f = h and b = y in ord_isom_surj, assumption+)
  apply (subgoal_tac "\<forall>aa\<in>carrier (Iod D X). y = h aa \<longrightarrow> (\<not>  y <\<^sub>(Iod D (\<Union>{W. Wa D W f a})) x)") apply blast apply (thin_tac "\<exists>a\<in>carrier (Iod D X). y = h a")
  apply (rule ballI) apply (rule impI) apply (subgoal_tac "aa \<in> X")
  apply simp apply (rotate_tac -2) apply (frule sym) apply (thin_tac "y = aa")
  apply simp apply (subgoal_tac "xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
  prefer 2 apply simp apply (subgoal_tac "xa <\<^sub>(Iod D X) y")
  apply (thin_tac "\<forall>y\<in>carrier (Iod D X).  xa <\<^sub>(Iod D X) y \<longrightarrow> \<not>  y <\<^sub>(Iod D X) x")
 apply simp apply (simp add:Iod_def ord_neq_def)
 apply (simp add:Iod_def ord_neq_def)  apply (simp add:Iod_def)
 apply (simp add:Iod_def segment_def)
 apply (subgoal_tac "well_ordered_set (Iod D Y)")
 apply (frule_tac S = "Iod D Y" and a = b in segment_well_ordered_set, assumption+)
  apply (subgoal_tac "Iod (Iod D Y) (segment (Iod D Y) b) = Iod D (segment (Iod D Y) b)") apply simp apply (simp add:well_ordered_set_is_ordered_set)
  apply (rule Iod_sub_sub, assumption+) apply (rule subsetI)
   apply (simp add:Iod_def segment_def ord_neq_def)
  apply (simp add:WWa_def Wa_def) apply (simp add:Wa_def)
  apply (subgoal_tac "well_ordered_set (Iod D X)") apply (simp add:well_ordered_set_is_ordered_set) apply (simp add:Wa_def)
 apply (subgoal_tac "well_ordered_set (Iod D Y)") prefer 2 apply (simp add:Wa_def)
 apply (subgoal_tac "tordered_set (Iod D Y)") prefer 2 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "y \<in> carrier (Iod D Y)") prefer 2 apply (simp add:Iod_def)
 prefer 2 apply (simp add:S_inductive_set_def)
 prefer 2 apply blast
 prefer 2 apply (simp add:S_inductive_set_def)
 prefer 2 apply (simp add:Iod_def)
 apply (subgoal_tac "b \<in> carrier (Iod D Y)")
 apply (frule_tac D = "Iod D Y" and a = y and b = b in tordering_not2, assumption+)
 apply (subgoal_tac "x \<in> carrier (Iod D X)") prefer 2 apply (simp add:Iod_def)
  prefer 2 apply (simp add:Iod_def) 
 apply (subgoal_tac "ordered_set (Iod D X)")
 apply (subgoal_tac "ordered_set (Iod D (segment (Iod D Y) b))")
 apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Y) b)" and f = h and a = x in ord_isom_mem, assumption+) apply simp
 apply (subgoal_tac "x \<le>\<^sub>(Iod D (\<Union>{W. Wa D W f a})) b")
 apply (subgoal_tac "b \<le>\<^sub>(Iod D (\<Union>{W. Wa D W f a})) y")
 apply (frule_tac S = "Iod D (\<Union>{W. Wa D W f a})" in well_ordered_set_is_ordered_set)
 apply (subgoal_tac "x \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
 apply (subgoal_tac "b \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))") 
 apply (subgoal_tac "y \<in> carrier (Iod D (\<Union>{W. Wa D W f a}))")
 apply (frule_tac a = x and b = b and c = y in ordering_axiom3 [of "Iod D (\<Union>{W. Wa D W f a})"], assumption+)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "tordered_set (Iod D (\<Union>{W. Wa D W f a}))") 
 prefer 2 apply (simp add:well_ordered_set_def)
 apply (frule_tac D = "Iod D (\<Union>{W. Wa D W f a})" and a = y and b = x in tordering_not1, assumption+) apply simp
 apply (simp add:Iod_def) apply blast
 apply (simp add:Iod_def) apply blast
 apply (simp add:Iod_def) apply blast
 apply (simp add:Iod_def ord_neq_def)
 apply (simp add:Iod_def ord_neq_def segment_def)
apply (subgoal_tac "well_ordered_set (Iod D Y)")
 apply (frule_tac S = "Iod D Y" and a = b in segment_well_ordered_set, assumption+)
  apply (subgoal_tac "Iod (Iod D Y) (segment (Iod D Y) b) = Iod D (segment (Iod D Y) b)") apply simp apply (simp add:well_ordered_set_is_ordered_set)
  apply (rule Iod_sub_sub, assumption+) apply (rule subsetI)
  apply (simp add:Iod_def segment_def) apply (simp add:Wa_def)
  apply (simp add:Wa_def) apply (simp add:Wa_def well_ordered_set_is_ordered_set)
(*** overup done ***)
 apply (thin_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
 apply (thin_tac "\<not> ExPre (Iod D (\<Union>{W. Wa D W f a})) x")
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply (subgoal_tac "\<forall>Y. Wa D Y f a \<and> xa \<in> Y \<longrightarrow> xa \<in> X")
 apply blast apply (thin_tac "\<exists>x. Wa D x f a \<and> xa \<in> x")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 (**--- overup again ---**) 
 apply (subgoal_tac "ordered_set D") prefer 2 apply (simp add:S_inductive_set_def)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y in BNTr7, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply (case_tac "Y \<subseteq> X")
 apply (rule_tac A = Y and B = X and c = xa in subsetD, assumption+)
 (**-- overup X \<subseteq> Y \<or> Y \<subseteq> X; \<not> Y \<subseteq> X ---*)
apply simp apply (subgoal_tac "X \<subset> Y") apply (thin_tac "X \<subseteq> Y") apply (thin_tac "\<not> Y \<subseteq> X") prefer 2 apply blast
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y in BNTr6, assumption+) apply (simp add:WWa_def) apply (simp add:WWa_def)
 apply assumption+
 apply (subgoal_tac "\<forall>b\<in>carrier (Iod D Y). ord_equiv (Iod D X) (Iod D (segment (Iod D Y) b)) \<longrightarrow> xa \<in> X")
 apply blast 
  apply (thin_tac "\<exists>b\<in>carrier (Iod D Y). ord_equiv (Iod D X) (Iod D (segment (Iod D Y) b))")
 apply (rule ballI) apply (rule impI) apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>h. ord_isom (Iod D X) (Iod D (segment (Iod D Y) b)) h \<longrightarrow> xa \<in> X") apply blast
 apply (thin_tac "Ex (ord_isom (Iod D X) (Iod D (segment (Iod D Y) b)))")
 apply (rule allI) apply (rule impI)
 apply (frule_tac D = D and f = f and a = a and ?W1.0 = X and ?W2.0 = Y and
 b = b and g = h in BNTr4_1, assumption+)
  apply (simp add:WWa_def) apply (simp add:WWa_def) apply (simp add:Iod_def)
  apply assumption
  apply (subgoal_tac "ordered_set (Iod D X)")
  apply (subgoal_tac "ordered_set (Iod D (segment (Iod D Y) b))")
  apply (subgoal_tac "x \<in> carrier (Iod D X)")
  apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Y) b)" and f = h and a = x in ord_isom_mem, assumption+) apply simp
  apply (subgoal_tac "x <\<^sub>D b") prefer 2 apply (simp add:Iod_def segment_def ord_neq_def) 
  apply (frule_tac A = X and B = Y in psubset_imp_subset)
  apply (frule_tac A = X and B = Y and c = x in subsetD, assumption+)
  apply (subgoal_tac "xa \<in> carrier D") 
  apply (subgoal_tac "x \<in> carrier D")
  apply (subgoal_tac "b \<in> carrier D")
  apply (subgoal_tac "xa <\<^sub>D x") prefer 2 apply (simp add:ord_neq_def)
  apply (frule_tac a = xa and b = x and c = b in ord_neq_trans, assumption+)
  apply (subgoal_tac "xa \<in> carrier (Iod D (segment (Iod D Y) b))")
  prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
  apply (frule_tac D = "Iod D X" and E = "Iod D (segment (Iod D Y) b)" and f = h and b = xa in ord_isom_surj, assumption+)
  apply (subgoal_tac "\<forall>aa\<in>carrier (Iod D X). xa = h aa \<longrightarrow> xa \<in> X") apply blast apply (thin_tac "\<exists>a\<in>carrier (Iod D X). xa = h a")
  apply (rule ballI) apply (rule impI) apply (subgoal_tac "aa \<in> X")
  apply simp apply (subgoal_tac "aa \<in> X") apply simp apply (simp add:Iod_def)
  apply (simp add:Iod_def) apply blast
  apply (simp add:Iod_def) apply blast   apply (simp add:Iod_def) apply blast
  apply (simp add:Iod_def)
  apply (subgoal_tac "well_ordered_set (Iod D Y)") prefer 2 apply (simp add:Wa_def)
  apply (frule_tac S = "Iod D Y" and a = b in segment_well_ordered_set, assumption+)
  apply (subgoal_tac "Iod (Iod D Y) (segment (Iod D Y) b) = Iod D (segment (Iod D Y) b)") apply simp apply (simp add:well_ordered_set_is_ordered_set)
  apply (rule Iod_sub_sub, assumption+) apply (rule subsetI) apply (simp add:Iod_def segment_def) apply (simp add:Wa_def) apply (simp add:Wa_def well_ordered_set_is_ordered_set)
apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
 apply blast
done

lemma BNTr8_1:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> Chain D (\<Union>WWa D f a)"
apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
apply (simp add:WWa_def)
 apply (subgoal_tac "well_ordered_set (Iod D (\<Union>{W. Wa D W f a}))")
 prefer 2 apply (simp add:Wa_def)
 apply (subgoal_tac "tordered_set (Iod D (\<Union>{W. Wa D W f a}))")
 apply (subgoal_tac "(\<Union>{W. Wa D W f a}) \<subseteq> carrier D") 
 prefer 2 apply (simp add:Wa_def) 
apply (frule S_inductive_ordered [of "D"])
apply (rule_tac D = D and X = "\<Union>{W. Wa D W f a}" in tordered_Chain, assumption+)
apply (simp add:well_ordered_set_def)
done

lemma BNTr8_2:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)\<rbrakk>  \<Longrightarrow> a \<in> \<Union>WWa D f a"
apply (simp add:WWa_def)
 apply (frule S_inductive_ordered [of "D"])
 apply (frule_tac D = D and f = f and a = a in BNTr2, assumption+)
 apply (simp add:WWa_def)
 apply (subgoal_tac "a \<in> {a}")
 apply blast apply simp
done

lemma BNTr8_3:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); \<exists>xa. Wa D xa f a \<and> x \<in> xa\<rbrakk> \<Longrightarrow> x \<in> \<Union>WWa D f a"
apply (subgoal_tac "\<forall>xa. Wa D xa f a \<and> x \<in> xa \<longrightarrow> x \<in> \<Union>WWa D f a")  
apply blast apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
apply (rule allI) apply (rule impI) apply (simp add:WWa_def) apply blast
done

lemma BNTr8_4:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); \<exists>xa. Wa D xa f a \<and> x \<in> xa\<rbrakk> \<Longrightarrow> x \<in> carrier D"
apply auto
 apply (simp add:Wa_def) apply (erule conjE) apply (simp add:subsetD)
done

lemma BNTr8_4_1:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); x \<in> \<Union>WWa D f a \<rbrakk> \<Longrightarrow> x \<in> carrier D" 
apply (simp add:WWa_def)
apply (rule BNTr8_4, assumption+)
done

lemma BNTr8_5:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); b \<in> carrier D; \<forall>z\<in>(\<Union>WWa D f a). z \<le>\<^sub>D b; x \<in> (\<Union>WWa D f a) \<rbrakk> \<Longrightarrow> ExPre (Iod D (insert b (\<Union>WWa D f a))) x \<longrightarrow>  ExPre (Iod D (\<Union>WWa D f a)) x" apply (rule impI)
apply (simp add:ExPre_def)
apply (subgoal_tac "\<forall>xa. xa \<in> carrier (Iod D (insert b (\<Union>WWa D f a))) \<and>  xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x \<and> (\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))). xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x) \<longrightarrow> (\<exists>xa. xa \<in> carrier (Iod D (\<Union>WWa D f a)) \<and>  xa <\<^sub>(Iod D (\<Union>WWa D f a)) x \<and> (\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)). xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x))") apply blast
apply (thin_tac "\<exists>xa. xa \<in> carrier (Iod D (insert b (\<Union>WWa D f a))) \<and>  xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x \<and> (\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))). xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x)")
apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "xa \<in> carrier (Iod D (\<Union>WWa D f a)) \<and>  xa <\<^sub>(Iod D (\<Union>WWa D f a)) x \<and> (\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)). xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x)") apply blast
apply (rule conjI)
 apply (subgoal_tac "\<forall>X\<in>WWa D f a. x \<in> X \<longrightarrow> xa \<in> carrier (Iod D (\<Union>WWa D f a))") apply blast apply (thin_tac "\<exists>X\<in>WWa D f a. x \<in> X")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "x  \<le>\<^sub>D b") prefer 2 apply blast
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D b")
 apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))).   xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x")
 apply (simp add:Iod_def ord_neq_def) 
 apply (case_tac "xa = b") apply (erule conjE)+ apply simp
 apply (frule S_inductive_ordered [of "D"])
 apply (frule_tac a = x and b = b in ordering_axiom2[of "D"])
 apply (subgoal_tac "X \<subseteq> carrier D") apply (simp add:subsetD)
 apply (simp add:WWa_def Wa_def) apply assumption+
 apply simp apply simp
apply (rule conjI)
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))).  xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x")
 apply (simp add:Iod_def ord_neq_def)
apply (rule ballI)
 apply (subgoal_tac "y \<in> carrier (Iod D (insert b (\<Union>WWa D f a)))")
 prefer 2 apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))).
 xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x") apply (simp add:Iod_def)
 apply (subgoal_tac "xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x") prefer 2 apply simp
 apply (simp add:Iod_def ord_neq_def)
done

lemma BNTr8_6:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); b \<in> carrier D; \<forall>z\<in>(\<Union>WWa D f a). z \<le>\<^sub>D b; x \<in> (\<Union>WWa D f a) \<rbrakk> \<Longrightarrow> ExPre (Iod D (\<Union>WWa D f a)) x \<longrightarrow> ExPre (Iod D (insert b (\<Union>WWa D f a))) x"
apply (rule impI)
apply (simp add:ExPre_def)
apply (subgoal_tac "\<forall>xa. xa \<in> carrier (Iod D (\<Union>WWa D f a)) \<and>  xa <\<^sub>(Iod D (\<Union>WWa D f a)) x \<and> (\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)).  xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x) \<longrightarrow> (\<exists>xa. xa \<in> carrier (Iod D (insert b (\<Union>WWa D f a))) \<and> xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x \<and> (\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))). xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x))") apply blast
apply (thin_tac "\<exists>xa. xa \<in> carrier (Iod D (\<Union>WWa D f a)) \<and>  xa <\<^sub>(Iod D (\<Union>WWa D f a)) x \<and> (\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)). xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x)")
apply (rule allI)
 apply (rule impI)
 apply (erule conjE)+
 apply (subgoal_tac "xa \<in> carrier (Iod D (insert b (\<Union>WWa D f a))) \<and>
 xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x \<and> (\<forall>y\<in>carrier (Iod D (insert b (\<Union>WWa D f a))).  xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) x)")
 apply blast
 apply (rule conjI) apply (simp add:Iod_def)
 apply (rule conjI) apply (simp add:Iod_def ord_neq_def)
apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "y \<in> (insert b (\<Union>WWa D f a))") 
 prefer 2 apply (simp add:Iod_def)
 apply simp
 apply (case_tac "y = b")
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 apply (frule_tac S_inductive_ordered [of "D"])
 apply (subgoal_tac "(\<Union>WWa D f a) \<subseteq> carrier D")
 apply (frule_tac D = D and X = "\<Union>WWa D f a" and a = b in well_ord_adjunction,
                            assumption+)
 apply (rule ballI) apply simp apply assumption
 apply simp
 apply (subgoal_tac "x \<in> carrier (Iod D (insert b (\<Union>WWa D f a)))")
 apply (subgoal_tac "tordered_set (Iod D (insert b (\<Union>WWa D f a)))")
 prefer 2 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "x \<le>\<^sub>(Iod D (insert b (\<Union>WWa D f a))) b")
 apply (frule_tac D = "Iod D (insert b (\<Union>WWa D f a))" and a = x and b = b in 
 tordering_not3, assumption+) 
 apply (thin_tac "xa \<in> carrier (Iod D (\<Union>WWa D f a))")
 apply (thin_tac "xa <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)).
    xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) b")
 apply (thin_tac "well_ordered_set (Iod D (insert b (\<Union>WWa D f a)))")
 apply (subgoal_tac "\<forall>X\<in>WWa D f a. x \<in> X \<longrightarrow> x \<le>\<^sub>(Iod D (insert b (\<Union>WWa D f a))) b")
 apply blast apply (thin_tac "\<exists>X\<in>WWa D f a. x \<in> X")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "x \<le>\<^sub>D b") prefer 2 apply blast apply (simp add:Iod_def)
 apply (simp add:Iod_def) 
 apply (rule subsetI) apply simp apply (subgoal_tac "\<forall>x\<in>WWa D f a. xb \<in> x \<longrightarrow>
 xb \<in> carrier D") apply blast apply (thin_tac "\<exists>x\<in>WWa D f a. xb \<in> x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "xba \<subseteq> carrier D") apply (simp add:subsetD)
 apply (simp add:WWa_def Wa_def)
apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D b")
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)).
              xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "xa \<in> carrier (Iod D (\<Union>WWa D f a))")
 apply (thin_tac "xa <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y")
apply (simp add:WWa_def) apply (simp add:Wa_def)
apply simp
 apply (subgoal_tac "y \<in> insert b (\<Union>WWa D f a)") 
 prefer 2 apply (simp add:Iod_def) apply simp
 apply (subgoal_tac "y \<in> carrier (Iod D (\<Union>WWa D f a))")
 apply (subgoal_tac "xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x") prefer 2 apply simp
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)).
              xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (subgoal_tac "xa <\<^sub>(Iod D (\<Union>WWa D f a)) y")
 prefer 2 apply (simp add:Iod_def ord_neq_def) apply simp
 apply (simp add:Iod_def ord_neq_def)
apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D b")
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)).
     xa <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "xa <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "xa <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) y")
 apply (thin_tac "y \<in> carrier (Iod D (insert b (\<Union>WWa D f a)))")
 apply (simp add:Iod_def)
done

lemma BNTr8_7:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); b \<in> carrier D; \<forall>z\<in>(\<Union>WWa D f a). z \<le>\<^sub>D b; x \<in> (\<Union>WWa D f a); ExPre (Iod D (insert b (\<Union>WWa D f a))) x\<rbrakk> \<Longrightarrow> Pre (Iod D (insert b (\<Union>WWa D f a))) x = Pre (Iod  D (\<Union>WWa D f a)) x"
apply (frule_tac D = D and f = f and a = a and b = b in BNTr8_5, assumption+)
apply simp
(** well_ordered **)
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2 apply (simp add:WWa_def Wa_def)
 apply (frule S_inductive_ordered [of "D"])
 apply (frule_tac D = D and X = "(\<Union>WWa D f a)" and a = b in well_ord_adjunction)
 apply (rule subsetI) apply (simp add:WWa_def) 
 apply (rule BNTr8_4, assumption+) apply blast apply assumption 
(** well_ordered ---- done **)
apply simp
apply (subgoal_tac "x \<in> carrier (Iod D (insert b (\<Union>WWa D f a)))")
apply (frule_tac S = "Iod D (insert b (\<Union>WWa D f a))" and a = x and ?a1.0 = "Pre (Iod D (\<Union>WWa D f a)) x" in UniquePre, assumption+)
 apply (subgoal_tac "x \<in> carrier (Iod D (\<Union>WWa D f a))")
 apply (frule_tac S = "Iod D (\<Union>WWa D f a)" and a = x in Pre_element, assumption+)
 apply (erule conjE)
 apply (rule conjI) apply (simp add:Iod_def)
 apply (rule conjI) apply (erule conjE)+ apply (simp add:Iod_def ord_neq_def)
 apply simp
 apply (rule ballI) apply (rule impI)
 apply (case_tac "y = b") apply simp
 apply (subgoal_tac "x \<le>\<^sub>D b") 
 apply (subgoal_tac "tordered_set (Iod D (insert b (\<Union>WWa D f a)))")
 prefer 2 apply (simp add:well_ordered_set_def)
 apply (rule_tac D = "Iod D (insert b (\<Union>WWa D f a))" and a = x and b = b in tordering_not3, assumption+) apply (simp add:Iod_def)
  apply (thin_tac "ExPre (Iod D (insert b (\<Union>WWa D f a))) x")
  apply (thin_tac "ExPre (Iod D (\<Union>WWa D f a)) x")
  apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
  apply (thin_tac "well_ordered_set (Iod D (insert b (\<Union>WWa D f a)))")
  apply (thin_tac "Pre (Iod D (\<Union>WWa D f a)) x <\<^sub>(Iod D (\<Union>WWa D f a)) x \<and>
  (\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)).  Pre (Iod D (\<Union>WWa D f a)) x <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x)")
  apply (thin_tac "x \<in> carrier (Iod D (insert b (\<Union>WWa D f a)))")
  apply (thin_tac "Pre (Iod D (\<Union>WWa D f a)) x \<in> carrier (Iod D (\<Union>WWa D f a))")
  apply (thin_tac "b \<in> carrier (Iod D (insert b (\<Union>WWa D f a)))")
  apply (thin_tac "Pre (Iod D (\<Union>WWa D f a)) x <\<^sub>(Iod D (insert b (\<Union>WWa D f a))) b")
  apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (subgoal_tac "\<forall>X\<in>WWa D f a. x \<in> X \<longrightarrow> x \<le>\<^sub>D b") apply blast
 apply (thin_tac "\<exists>X\<in>WWa D f a. x \<in> X") apply (rule ballI) apply (rule impI)
 apply blast
 apply (subgoal_tac "y \<in> carrier (Iod D (\<Union>WWa D f a))") 
 prefer 2 apply (simp add:Iod_def) apply (erule conjE)+
 apply (subgoal_tac "Pre (Iod D (\<Union>WWa D f a)) x <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow>
              \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 prefer 2 apply simp
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (\<Union>WWa D f a)). Pre (Iod D (\<Union>WWa D f a)) x <\<^sub>(Iod D (\<Union>WWa D f a)) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (\<Union>WWa D f a)) x")
 apply (subgoal_tac "Pre (Iod D (\<Union>WWa D f a)) x <\<^sub>(Iod D (\<Union>WWa D f a)) y")
 apply simp apply (simp add:Iod_def ord_neq_def)
 apply (simp add:Iod_def ord_neq_def)
 apply (simp add:Iod_def) apply assumption
apply (simp add:Iod_def)
done

lemma BNTr8_8:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x); b \<in> carrier D; \<forall>z\<in>(\<Union>WWa D f a). z \<le>\<^sub>D b; x \<in> (\<Union>WWa D f a); ExPre (Iod D (\<Union>WWa D f a)) x\<rbrakk> \<Longrightarrow> Pre (Iod  D (\<Union>WWa D f a)) x = Pre (Iod D (insert b (\<Union>WWa D f a))) x"
apply (frule_tac D = D and f = f and a = a and b = b and x = x in BNTr8_6,
                                  assumption+) apply simp
apply (rule_tac D1 = D and f1 = f and a1 = a and b1 = b and x1 = x in BNTr8_7 [THEN sym], assumption+) apply blast apply blast apply assumption
done

lemma BNTr8_9:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x); X \<in> WWa D f a\<rbrakk> \<Longrightarrow> X \<subseteq> \<Union>WWa D f a"
apply (rule subsetI) apply (simp add:WWa_def)
apply blast
done

lemma BNTr9:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
\<forall>x\<in>carrier D. x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> (\<Union>WWa D f a) \<union> {Sup D (\<Union>WWa D f a)} \<in> WWa D f a"
apply (frule S_inductive_ordered [of "D"])
apply (frule_tac D = D and f = f and a = a in BNTr8_1, assumption+) 
apply (subst WWa_def) apply simp
 apply (subst Wa_def)
apply (rule conjI)
(*** insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}) \<subseteq> carrier D ***)
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (unfold WWa_def)  apply simp
 apply (rule conjI) 
 apply (simp add:S_inductive_sup_mem)
 apply (rule subsetI) apply simp
 apply (rule_tac D = D and f = f and a = a and x = x in BNTr8_4, assumption+)
 (** done **)
apply (rule conjI)
(** well_ordered_set
        (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) **)
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2 apply (simp add:WWa_def Wa_def)
 apply (frule_tac D = D and X = "(\<Union>WWa D f a)" and a = "Sup D (\<Union>{W. Wa D W f a})" in well_ord_adjunction) apply (simp add:WWa_def)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 prefer 2 apply (simp add:WWa_def) apply (simp add:Wa_def)
 apply (frule_tac D = D and X = "\<Union>{W. Wa D W f a}" in S_inductive_sup_mem, assumption+)
  apply (rule ballI)
  apply (frule_tac D = D and X = "(\<Union>{W. Wa D W f a})" in S_inductive_sup_bound, assumption+)  apply (simp add:WWa_def)
  apply simp apply (simp add:WWa_def) (** done **)
apply (rule conjI)
 apply (frule_tac D = D and f = f and a = a in BNTr8_2, assumption+)
 apply (simp add:WWa_def)
apply (rule conjI)
 apply (rule ballI)
 apply (case_tac "x = (Sup D (\<Union>{W. Wa D W f a}))") 
 apply (frule_tac D = D and X = "(\<Union>{W. Wa D W f a})" in S_inductive_sup_bound, assumption+) 
apply (frule_tac D = D and f = f and a = a in BNTr8_2, assumption+)
 apply (unfold WWa_def) apply blast
apply simp
 apply (subgoal_tac "\<forall>X. Wa D X f a \<and> x \<in> X \<longrightarrow>  a \<le>\<^sub>D x") apply blast
 apply (thin_tac " \<exists>xa. Wa D xa f a \<and> x \<in> xa") apply (rule allI)
 apply (rule impI) apply (erule conjE) apply (simp add:Wa_def)
apply (rule ballI)
 apply (case_tac "ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x") apply simp 
prefer 2 apply simp
(** \<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x *)
 apply (rule impI) 
 apply (case_tac "x = Sup D (\<Union>{W. Wa D W f a})")
 apply (case_tac "x \<in> \<Union>{W. Wa D W f a}")
 apply (frule sym) apply (thin_tac "x = Sup D (\<Union>{W. Wa D W f a})")
 apply simp apply (thin_tac "Sup D (\<Union>{W. Wa D W f a}) = x")
 apply (subgoal_tac "insert x (\<Union>{W. Wa D W f a}) =\<Union>{W. Wa D W f a}")  
 prefer 2  apply (subgoal_tac "\<forall>X. Wa D X f a \<and> x \<in> X \<longrightarrow> insert x (\<Union>{W. Wa D W f a}) = \<Union>{W. Wa D W f a}") apply blast apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa") apply (rule allI) apply (rule impI)
 apply (thin_tac " \<not> ExPre (Iod D (insert x (\<Union>{W. Wa D W f a}))) x")
 apply (rule equalityI)
  apply (rule subsetI) apply simp apply blast
  apply (rule subsetI) apply simp 
apply simp apply (thin_tac "insert x (\<Union>{W. Wa D W f a}) = \<Union>{W. Wa D W f a}")
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (simp add:WWa_def)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (subgoal_tac "x \<in> \<Union>WWa D f a")
 apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (simp add:Wa_def) apply (erule conjE)+
 apply (subgoal_tac "\<forall>X\<in>WWa D f a. x \<in> X \<longrightarrow> (Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x)") apply blast apply (thin_tac "\<exists>X\<in>WWa D f a. x \<in> X")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "\<forall>x\<in>X. if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x  then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x  else a = a") prefer 2 apply simp
 apply (thin_tac "\<forall>y\<in>WWa D f a.  \<forall>x\<in>y. if ExPre (Iod D (\<Union>WWa D f a)) x
  then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a")
 apply (subgoal_tac "if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x else if a \<noteq> x  then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a") prefer 2 apply simp
 apply (thin_tac "\<forall>x\<in>X. if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a") apply simp
 apply (rule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (simp add:WWa_def)
(** \<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x
   done **)
(* \<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x *)
apply (subgoal_tac "segment (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x = \<Union>{W. Wa D W f a}")
 apply simp
 apply (rule equalityI)
 apply (rule subsetI)
  apply (thin_tac "x = Sup D (\<Union>{W. Wa D W f a}) \<or> (\<exists>xa. Wa D xa f a \<and> x \<in> xa)")
  apply (thin_tac "\<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x")
 apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
 apply simp
 apply (rule subsetI)
 apply (thin_tac "\<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x")
 apply (thin_tac "x = Sup D (\<Union>{W. Wa D W f a}) \<or> (\<exists>xa. Wa D xa f a \<and> x \<in> xa)")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "\<forall>Y. Wa D Y f a \<and> xa \<in> Y \<longrightarrow> (xa \<le>\<^sub>D (Sup D (\<Union>{W. Wa D W f a})) \<and> xa \<noteq> (Sup D (\<Union>{W. Wa D W f a})))") apply blast
 apply (thin_tac "\<exists>x. Wa D x f a \<and> xa \<in> x")
 apply (rule allI) apply (rule impI) 
 apply (frule_tac D = D and X = "\<Union>{W. Wa D W f a}" in S_inductive_sup_bound,
                                   assumption+)
 apply (subgoal_tac "xa \<in> \<Union>{W. Wa D W f a}")
 apply (subgoal_tac "xa \<le>\<^sub>D (Sup D (\<Union>{W. Wa D W f a}))")
 prefer 2 apply blast
  apply (thin_tac "\<forall>x\<in>\<Union>{W. Wa D W f a}.  x \<le>\<^sub>D (Sup D (\<Union>{W. Wa D W f a}))")
  apply simp
  apply (rule contrapos_pp, simp+) apply blast 
 apply (thin_tac "\<forall>x\<in>\<Union>{W. Wa D W f a}.  x \<le>\<^sub>D (Sup D (\<Union>{W. Wa D W f a}))")
 apply simp apply blast
apply simp
 apply (subgoal_tac "segment (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x = segment (Iod D (\<Union>{W. Wa D W f a})) x") 
 apply simp
 apply (subgoal_tac "\<not> ExPre (Iod D (\<Union>{W. Wa D W f a})) x")
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (simp add:WWa_def)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp 
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
apply (simp only:Wa_def) apply (erule conjE)+ 
 apply (subgoal_tac "if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x
  else a = a") prefer 2 apply blast
 apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a. if ExPre (Iod D (\<Union>WWa D f a)) x  then f (Pre (Iod D (\<Union>WWa D f a)) x) = x else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a")
 apply simp
 apply (simp add:WWa_def)
(*-- \<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x
        \<Longrightarrow> \<not> ExPre (Iod D (\<Union>{W. Wa D W f a})) x --*)
apply (thin_tac "segment (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x = segment (Iod D (\<Union>{W. Wa D W f a})) x")
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (frule_tac D = D and f = f and a = a and b = "Sup D (\<Union>WWa D f a)" and x = x in BNTr8_6, assumption+)
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem, assumption+)
 apply (rule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+) apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") 
 apply (simp add:WWa_def) apply simp apply (simp add:WWa_def)
 (** done **)
(*** segment (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a})))
            x =  segment (Iod D (\<Union>{W. Wa D W f a})) x ***)
apply (thin_tac "\<not> ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x")
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
 apply (case_tac "xa = Sup D (\<Union>{W. Wa D W f a})")
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (frule_tac D = D and X = "\<Union>{W. Wa D W f a}" in S_inductive_sup_bound, assumption+)
 apply (subgoal_tac "x \<le>\<^sub>D (Sup D (\<Union>{W. Wa D W f a}))") prefer 2 apply blast
 apply (frule sym) apply (thin_tac "xa = Sup D (\<Union>{W. Wa D W f a})")
 apply simp
 apply (subgoal_tac "x \<in> carrier D")
 apply (subgoal_tac "xa \<in> carrier D")
 apply (frule_tac D = D in S_inductive_ordered)
 apply (frule_tac a = xa and b = x in ordering_axiom2 [of "D"], assumption+)
 apply simp
 apply (frule_tac D = D and X = "\<Union>{W. Wa D W f a}" in S_inductive_sup_mem,
  assumption+) apply simp
 apply (rule_tac D = D and f = f and a = a and x = x in BNTr8_4, assumption+)
 apply simp
 apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def)
(**--  ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x
 = f (Pre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x) =  x --**)
apply (case_tac "x = Sup D (\<Union>{W. Wa D W f a})")
 apply (case_tac "x \<notin> \<Union>{W. Wa D W f a}")
 prefer 2 apply simp 
 apply (subgoal_tac "\<forall>X. Wa D X f a \<and>  Sup D (\<Union>{W. Wa D W f a}) \<in> X \<longrightarrow>
  f (Pre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a})))
    (Sup D (\<Union>{W. Wa D W f a}))) =  Sup D (\<Union>{W. Wa D W f a})")
 apply blast apply (thin_tac "\<exists>x. Wa D x f a \<and> Sup D (\<Union>{W. Wa D W f a}) \<in> x") apply (rule allI) apply (rule impI) 
 apply (frule sym) apply (thin_tac "x = Sup D (\<Union>{W. Wa D W f a})") apply simp
 apply (thin_tac "Sup D (\<Union>{W. Wa D W f a}) = x")
 apply (subgoal_tac "insert x (\<Union>{W. Wa D W f a}) = \<Union>{W. Wa D W f a}")
 prefer 2 apply (rule_tac equalityI)
  apply (rule subsetI) apply simp apply blast apply (rule subsetI) apply simp
  apply simp
  apply (thin_tac "insert x (\<Union>{W. Wa D W f a}) = \<Union>{W. Wa D W f a}")
  apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
  apply (simp add:WWa_def)
  apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
  apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (subgoal_tac "x \<in> (\<Union>WWa D f a)")
 apply (simp only:Wa_def) 
 apply simp apply (subst WWa_def) apply blast apply (simp add:WWa_def)
(*** case  x = Sup D (\<Union>{W. Wa D W f a}); x \<notin> \<Union>{W. Wa D W f a} ***)
   (** if ExPre the Pre is the Sup **)
 (**-- preparation for  Pre_element --*)
 apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2  apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
  apply (thin_tac "x = Sup D (\<Union>{W. Wa D W f a}) \<or> (\<exists>xa. Wa D xa f a \<and> x \<in> xa)")
  apply (thin_tac "ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x")
 apply (simp add:WWa_def) apply (simp add:Wa_def) 
 (*************)
 apply (frule_tac D = D and X = "(\<Union>WWa D f a)" and a = "Sup D (\<Union>{W. Wa D W f a})" in well_ord_adjunction)
  apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
  apply (simp add:WWa_def) apply (simp add:Chain_def)
 apply (frule_tac D = D and X = "\<Union>{W. Wa D W f a}" in S_inductive_sup_mem, assumption+)
 apply (frule_tac D = D and X = "\<Union>{W. Wa D W f a}" in S_inductive_sup_bound, assumption+) apply (simp add:WWa_def) apply simp (*preparation done*)
 apply (frule sym) apply (thin_tac "x = Sup D (\<Union>{W. Wa D W f a})") apply simp
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")  prefer 2 apply (simp add:WWa_def) 
apply simp
 apply (subgoal_tac "x \<in> carrier (Iod D (insert (Sup D (\<Union>WWa D f a)) (\<Union>WWa D f a)))") prefer 2 apply (simp add:Iod_def)
 apply (frule_tac S = "Iod D (insert x (\<Union>WWa D f a))" and a = x in Pre_element) apply simp apply assumption  (**  ============o----------o
                                              Pre        Sup   ***)
  apply (erule conjE)+
  apply simp 
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound)
  apply assumption 
  apply (subgoal_tac "\<forall>z\<in>\<Union>WWa D f a. z \<le>\<^sub>D (Pre (Iod D (insert x (\<Union>WWa D f a))) x)") prefer 2
  apply (rule ballI)
  apply (subgoal_tac "Pre (Iod D (insert x (\<Union>WWa D f a))) x <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) z \<longrightarrow>  \<not>  z <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
   prefer 2 
   apply (subgoal_tac "z \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))") 
   apply blast
   apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a.  x \<le>\<^sub>D (Sup D (\<Union>WWa D f a))")
   apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))). Pre (Iod D (insert x (\<Union>WWa D f a))) x <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
   apply (simp add:Iod_def)
  apply (rule contrapos_pp, simp+)
  apply (subgoal_tac "z \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
   prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac "tordered_set (Iod D (insert x (\<Union>WWa D f a)))")
  apply (frule_tac D = "Iod D (insert x (\<Union>WWa D f a))" and a = z and b = "Pre (Iod D (insert x (\<Union>WWa D f a))) x" in  tordering_not, assumption+)
   apply (simp add:Iod_def)
   apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))).  Pre (Iod D (insert x (\<Union>WWa D f a))) x <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<longrightarrow> \<not>  y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x") apply simp
   apply (subgoal_tac "x \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))") 
    prefer 2 apply (simp add:Iod_def)
   apply (frule_tac D = "Iod D (insert x (\<Union>WWa D f a))" and a = z and b = x in  tordering_not2, assumption+)
   apply (subgoal_tac "x \<le>\<^sub>D  z") prefer 2 apply (simp add:Iod_def)
 apply simp
 apply (frule_tac a = x and b = z in ordering_axiom2 [of "D"])
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem, assumption+) apply simp 
   apply (thin_tac "ExPre (Iod D (insert x (\<Union>WWa D f a))) x")
   apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
   apply (thin_tac "Chain D (\<Union>WWa D f a)")
   apply (thin_tac "well_ordered_set (Iod D (insert x (\<Union>WWa D f a)))")
   apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
   apply (thin_tac " Pre (Iod D (insert x (\<Union>WWa D f a))) x
          \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
 apply (simp add:WWa_def)
 apply (rule_tac D = D and f = f and a = a and x = z in BNTr8_4, assumption+)
  apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+)
  apply (frule_tac D = D and f = f and a = a and x = z in BNTr8_3, assumption+)
  apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
  apply (simp add:WWa_def)
  apply (subgoal_tac "z \<le>\<^sub>D (Sup D (\<Union>WWa D f a))")
   apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a.  x \<le>\<^sub>D (Sup D (\<Union>WWa D f a))") apply simp
  apply blast
  apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
   apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)") 
   apply (thin_tac "ExPre (Iod D (insert z (\<Union>WWa D f a))) z")
   apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
   apply (thin_tac "well_ordered_set (Iod D (insert z (\<Union>WWa D f a)))")
   apply (thin_tac " Pre (Iod D (insert z (\<Union>WWa D f a))) z
             \<in> carrier (Iod D (insert z (\<Union>WWa D f a)))")
   apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>x\<in>y.  x \<le>\<^sub>D z")
   apply (thin_tac " \<not>  z <\<^sub>(Iod D (insert z (\<Union>WWa D f a))) z")
  apply (simp add:WWa_def) apply blast
apply (simp add:well_ordered_set_def) 
(**-- pre is upper_bound ---*)
apply simp  
apply (subgoal_tac "Pre (Iod D (insert x (\<Union>WWa D f a))) x \<in> upper_bounds D (\<Union>WWa D f a)") 
 prefer 2 apply (simp add:upper_bounds_def upper_bound_def)
  apply (subgoal_tac "carrier (Iod D (insert x (\<Union>WWa D f a))) \<subseteq> carrier D")
  apply (simp add:subsetD)
  apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))).
  Pre (Iod D (insert x (\<Union>WWa D f a))) x <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y   \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
  apply (thin_tac "\<forall>xa. Wa D xa f a \<longrightarrow> x \<notin> xa")
  apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
  apply (thin_tac "well_ordered_set (Iod D (insert x (\<Union>WWa D f a)))")
  apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
  apply (thin_tac "Pre (Iod D (insert x (\<Union>WWa D f a))) x
           \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
  apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>xa\<in>y.  xa \<le>\<^sub>D x")
  apply (thin_tac " Pre (Iod D (insert x (\<Union>WWa D f a))) x
              <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
  apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D (Pre (Iod D (insert x (\<Union>WWa D f a))) x)")
 apply (rule subsetI) apply (thin_tac "x \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
  apply (thin_tac " ExPre (Iod D (insert x (\<Union>WWa D f a))) x")
 apply (simp add:Iod_def)
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem, assumption+) apply simp
 apply (case_tac "xa = x") apply simp apply simp
 apply (subgoal_tac "\<forall>Z\<in>WWa D f a. xa \<in> Z \<longrightarrow> xa \<in> carrier D") apply blast
 apply (thin_tac "Bex (WWa D f a) (op \<in> xa)")
 apply (rule ballI) apply (rule impI) apply (simp add:WWa_def)
 apply (subgoal_tac "Z \<subseteq> carrier D") apply (simp add:subsetD)
 apply (simp add:Wa_def)
apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (thin_tac "\<forall>xa. Wa D xa f a \<longrightarrow> x \<notin> xa")
 apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (thin_tac "x \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
 apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))).
  Pre (Iod D (insert x (\<Union>WWa D f a))) x  <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<longrightarrow>  \<not>  y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>xa\<in>y.  xa \<le>\<^sub>D x")
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D (Pre (Iod D (insert x (\<Union>WWa D f a))) x)") apply (rename_tac x0)
 apply (thin_tac "ExPre (Iod D (insert x0 (\<Union>WWa D f a))) x0")
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup)
  apply assumption+ apply simp apply (thin_tac "Sup D (\<Union>WWa D f a) = x0")
 apply (simp add:minimum_elem_def) apply (erule conjE)
 apply (subgoal_tac "x0 \<le>\<^sub>D (Pre (Iod D (insert x0 (\<Union>WWa D f a))) x0)")
 prefer 2 apply blast apply (thin_tac "\<forall>x\<in>upper_bounds D (\<Union>WWa D f a).  x0 \<le>\<^sub>D x")
apply (subgoal_tac "tordered_set (Iod D (insert x0 (\<Union>WWa D f a)))")
 prefer 2 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "x0 \<in> carrier (Iod D (insert x0 (\<Union>WWa D f a)))")
 apply (frule_tac D = "Iod D (insert x0 (\<Union>WWa D f a))" and a = "Pre (Iod D (insert x0 (\<Union>WWa D f a))) x0" and b = x0 in tordering_not1, assumption+)
 apply (simp add:Iod_def)
 apply (simp add:Iod_def)
(** ExPre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a}))) x 
  \<Longrightarrow>  f (Pre (Iod D (insert (Sup D (\<Union>{W. Wa D W f a})) (\<Union>{W. Wa D W f a})))
   x) =  x **)
apply simp
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (frule_tac D = D and f = f and a = a and b = "Sup D (\<Union>WWa D f a)" and x = x  in BNTr8_5, assumption+)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
apply (thin_tac "x \<noteq> Sup D (\<Union>WWa D f a)")
 apply (rule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem, assumption+) apply (simp add:WWa_def)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+) apply blast apply (simp add:WWa_def) apply assumption
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (simp add:WWa_def)
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
apply (subgoal_tac "ExPre (Iod D (\<Union>{W. Wa D W f a})) x")
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (frule_tac D = D and f = f and a = a and b = "Sup D (\<Union>WWa D f a)" and x = x in BNTr8_7, assumption+)
 apply (rule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem, assumption+) 
 apply (rule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+)  apply simp
 apply assumption apply simp
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (simp add:WWa_def)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
  prefer 2 apply (simp add:WWa_def) 
  apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
  apply (thin_tac "Pre (Iod D (insert (Sup D (\<Union>WWa D f a)) (\<Union>WWa D f a))) x =
           Pre (Iod D (\<Union>WWa D f a)) x") 
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
  apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
  apply (unfold Wa_def) apply (erule conjE)+ apply (fold Wa_def)
apply (case_tac "a \<noteq> x")
 apply (subgoal_tac "if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x
 else a = a")
 apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a. if ExPre (Iod D (\<Union>WWa D f a)) x
  then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a")
 prefer 2 apply blast apply simp
 apply simp 
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "a = x")
 apply simp
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>x\<in>y. if ExPre (Iod D (\<Union>WWa D f a)) x
  then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x  then 
  Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x  else a = a")
 apply (subgoal_tac "a \<in> carrier (Iod D (\<Union>WWa D f a))")
 apply (frule_tac S = "Iod D (\<Union>WWa D f a)" and a = a in  Pre_element, assumption+)
 apply (erule conjE)+
 apply (thin_tac "\<not> (\<exists>y\<in>carrier (Iod D (\<Union>WWa D f a)).  Pre (Iod D (\<Union>WWa D f a)) a <\<^sub>(Iod D (\<Union>WWa D f a)) y \<and>  y <\<^sub>(Iod D (\<Union>WWa D f a)) a)")
 apply (subgoal_tac "tordered_set (Iod D (\<Union>WWa D f a))")
 apply (frule_tac D = "Iod D (\<Union>WWa D f a)" and a = "Pre (Iod D (\<Union>WWa D f a)) a" and b = a in tordering_not1, assumption+)
 apply (thin_tac "Pre (Iod D (\<Union>WWa D f a)) a <\<^sub>(Iod D (\<Union>WWa D f a)) a")
 apply (subgoal_tac "Pre (Iod D (\<Union>WWa D f a)) a \<in> \<Union>WWa D f a")
 prefer 2 apply (simp add:Iod_def)
 apply (subgoal_tac "a \<le>\<^sub>D (Pre (Iod D (\<Union>WWa D f a)) a)")
 apply (simp add:Iod_def)
  apply (thin_tac "\<Union>WWa D f a \<subseteq> carrier D")
  apply (thin_tac "Pre (Iod D (\<Union>WWa D f a)) a \<in> carrier (Iod D (\<Union>WWa D f a))")
  apply (thin_tac "\<not>  a \<le>\<^sub>(Iod D (\<Union>WWa D f a)) (Pre (Iod D (\<Union>WWa D f a)) a)")   apply blast apply (simp add:well_ordered_set_def)
    apply (thin_tac "ExPre (Iod D (insert (Sup D (\<Union>WWa D f a)) (\<Union>WWa D f a))) a")
   apply (thin_tac "ExPre (Iod D (\<Union>WWa D f a)) a")
   apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
   apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>x\<in>y.  a \<le>\<^sub>D x")
   apply (thin_tac "Chain D (\<Union>WWa D f a)") apply (thin_tac "a \<noteq> Sup D (\<Union>WWa D f a)") 
  apply (simp add:WWa_def Iod_def) apply (simp add:WWa_def) apply assumption
 apply (simp add:WWa_def)
done

lemma BNTr10:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;  \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> (Sup D (\<Union>WWa D f a)) \<in> (\<Union>WWa D f a)"
apply (frule_tac D = D and f = f and a = a in BNTr9, assumption+) 
apply (subgoal_tac "\<Union>WWa D f a \<union> {Sup D (\<Union>WWa D f a)} \<subseteq> \<Union>WWa D f a")
apply (subgoal_tac "(Sup D (\<Union>WWa D f a)) \<in> \<Union>WWa D f a \<union> {Sup D (\<Union>WWa D f a)}")
apply (simp add:subsetD)
 apply simp
apply auto
done

lemma BNTr11:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;  \<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> f (Sup D (\<Union>WWa D f a)) = (Sup D (\<Union>WWa D f a))"
apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2
  apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
  apply (simp add:WWa_def) apply (simp add:Wa_def)
apply (subgoal_tac "Chain D (\<Union>WWa D f a)")
apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem, assumption+)
apply (subgoal_tac "Sup D (\<Union>WWa D f a) \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 prefer 2 apply simp
apply (case_tac "Sup D (\<Union>WWa D f a) = (f (Sup D (\<Union>WWa D f a)))")
 apply (rule sym, assumption+)
prefer 2 
(**-- Chain D (\<Union>WWa D f a) --**) 
 apply (subgoal_tac "tordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2 apply (simp add:well_ordered_set_def) 
 apply (subgoal_tac "(\<Union>WWa D f a) \<subseteq> carrier D")
 apply (frule S_inductive_ordered [of "D"])
apply (rule tordered_Chain, assumption+)
 apply (rule subsetI) apply (rule BNTr8_4_1, assumption+)
 (** Chain D (\<Union>WWa D f a) done **)
apply (subgoal_tac "well_ordered_set (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 prefer 2
 apply (frule S_inductive_ordered [of "D"])
 apply (subgoal_tac "\<Union>WWa D f a \<subseteq> carrier D") prefer 2 apply (rule subsetI)
 apply (rule BNTr8_4_1, assumption+)
 apply (frule_tac D = D and X = "\<Union>WWa D f a" and a = "f (Sup D (\<Union>WWa D f a))" in  well_ord_adjunction, assumption+)
 apply (simp add:funcset_mem)
 apply (rule ballI)
 apply (rule_tac a = x and b = "Sup D (\<Union>WWa D f a)" and c = "f (Sup D (\<Union>WWa D f a))" in ordering_axiom3[of "D"], assumption+)
 apply (rule BNTr8_4_1, assumption+) apply (simp add:funcset_mem)
 apply (simp add:S_inductive_sup_bound, assumption+) apply simp
(** well_ordered_set (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) 
     done **)
(**-- starting step 1 --**)
apply (subgoal_tac "(\<Union>WWa D f a) \<union> {f (Sup D (\<Union>WWa D f a))} \<in> WWa D f a")
 apply (subgoal_tac "\<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))} \<subseteq> (\<Union>WWa D f a)")
 apply (subgoal_tac "(f (Sup D (\<Union>WWa D f a))) \<in> \<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))}") prefer 2 apply simp
 apply (frule_tac A = "\<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))}" and B = "\<Union>WWa D f a" and c = "f (Sup D (\<Union>WWa D f a))" in subsetD, assumption+)
 apply (thin_tac "\<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))} \<in> WWa D f a")
 apply (thin_tac "\<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))} \<subseteq> \<Union>WWa D f a")
 apply (thin_tac "f (Sup D (\<Union>WWa D f a)) \<in> \<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))}")
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+)
 apply (subgoal_tac " f (Sup D (\<Union>WWa D f a)) \<le>\<^sub>D (Sup D (\<Union>WWa D f a))")
 prefer 2 apply blast
 apply (frule S_inductive_ordered [of "D"]) 
(**-- well_ordered (Iod D (\<Union>WWa D f a)), again --**)
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2 apply (simp add:WWa_def Wa_def)
 (* well_ordered done *) 
(**-- f (Sup D (\<Union>WWa D f a)) \<le>\<^sub>D Sup D (\<Union>WWa D f a contradicts  Sup D (\<Union>WWa D f a) <\<^sub>D f (Sup D (\<Union>WWa D f a)) --**)
 apply (subgoal_tac "\<Union>WWa D f a \<subseteq> carrier D")
 prefer 2 apply (rule subsetI)
 apply (rule_tac x = x in BNTr8_4_1, assumption+) 
 apply (subgoal_tac "f (Sup D (\<Union>WWa D f a)) \<le>\<^sub>D (Sup D (\<Union>WWa D f a))")
 prefer 2 apply simp apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a.  x \<le>\<^sub>D (Sup D (\<Union>WWa D f a))")
 apply (frule_tac D = D and f = f and a = a and x = "f (Sup D (\<Union>WWa D f a))" in BNTr8_4_1, assumption+)
 apply (frule_tac a = "Sup D (\<Union>WWa D f a)" and b = "f (Sup D (\<Union>WWa D f a))" in ordering_axiom2 [of "D"], assumption+) apply simp
apply (frule_tac D = D and f = f and a = a and X = "\<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))}" in BNTr8_9, assumption+) 
 (** step 1, done **)
(**-- step 2, show \<Union>WWa D f a \<union> {f (Sup D (\<Union>WWa D f a))} \<in> WWa D f a --**)
apply (subst WWa_def) apply simp
apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 prefer 2 apply (simp add:WWa_def)
apply (subst Wa_def)
 apply (rule conjI)
 apply (rule subsetI) apply simp
 apply (case_tac "x = f (Sup D (\<Union>WWa D f a))") apply simp
 apply (simp add:funcset_mem) apply simp
  apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
  apply (thin_tac "Chain D (\<Union>WWa D f a)")
  apply (thin_tac "Sup D (\<Union>WWa D f a) \<in> carrier D")
  apply (thin_tac "well_ordered_set
            (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 apply (subgoal_tac "\<forall>X\<in>WWa D f a. x \<in> X \<longrightarrow> x \<in> carrier D")
  apply blast apply (thin_tac "Bex (WWa D f a) (op \<in> x)")
  apply (rule ballI) apply (rule impI) apply (subgoal_tac "X \<subseteq> carrier D")
  apply (simp add:subsetD) apply (simp add:WWa_def Wa_def)
 apply (rule conjI) apply simp
 apply (rule conjI) apply simp apply (frule S_inductive_ordered [of "D"]) 
 apply (frule_tac D = D and f = f and a = a in BNTr2, assumption+)
 apply (subgoal_tac "a \<in> {a}") apply blast apply simp
apply (rule conjI)
 apply (rule ballI)
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (unfold WWa_def) apply simp apply (fold WWa_def)
 apply (unfold Wa_def) apply (erule conjE)+ apply (fold Wa_def)
 apply (case_tac "x = f (Sup D (\<Union>WWa D f a))") (*
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+) *)
 apply (frule_tac D = D and f = f and a = a in BNTr10, assumption+)
 apply (subgoal_tac "a \<le>\<^sub>D (Sup D (\<Union>WWa D f a))") prefer 2 apply blast
 apply (subgoal_tac "Sup D (\<Union>WWa D f a) \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 prefer 2 apply blast apply simp
 apply (frule S_inductive_ordered [of "D"])
 apply (rule_tac a = a and b = "Sup D (\<Union>WWa D f a)" and c = "f (Sup D (\<Union>WWa D f a))" in ordering_axiom3[of "D"], assumption+) apply (simp add:funcset_mem)
 apply assumption apply simp
 apply simp
  apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
  apply (thin_tac "\<Union>WWa D f a \<subseteq> carrier D")
  apply (thin_tac "\<exists>x\<in>WWa D f a. a \<in> x")
  apply (thin_tac "\<forall>y\<in>WWa D f a.  \<forall>x\<in>y. if ExPre (Iod D (\<Union>WWa D f a)) x
  then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x  then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x  else a = a")
 apply (subgoal_tac "\<forall>X. Wa D X f a \<and> x \<in> X \<longrightarrow>  a \<le>\<^sub>D x") apply blast
 apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa") apply (rule allI) 
 apply (rule impI) apply (erule conjE) apply (unfold Wa_def) 
 apply (erule conjE)+ apply simp
apply (rule ballI) 
(** \<forall>z\<in>(\<Union>WWa D f a). z \<le>\<^sub>D f (Sup D (\<Union>WWa D f a)) **)
 apply (subgoal_tac "\<forall>z\<in>(\<Union>WWa D f a). z \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 prefer 2  apply (rule ballI)
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+)
 apply (subgoal_tac "z \<le>\<^sub>D (Sup D (\<Union>WWa D f a))") prefer 2 apply blast
 apply (frule_tac D = D and f = f and a = a and x = z in BNTr8_4_1, assumption+)
 apply (subgoal_tac "Sup D (\<Union>WWa D f a) \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 prefer 2 apply blast apply (thin_tac "\<forall>x\<in>carrier D.  x \<le>\<^sub>D (f x)")
 apply (frule S_inductive_ordered [of "D"])
 apply (rule_tac a = z and b = "Sup D (\<Union>WWa D f a)" and c = "f (Sup D (\<Union>WWa D f a))" in ordering_axiom3 [of "D"], assumption+)
 apply (simp add:funcset_mem) apply assumption+
 (** done **)
 apply (case_tac "ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x") apply simp
 prefer 2 apply simp
apply (rule impI)
 apply (unfold ExPre_def)
 apply (case_tac "x = f (Sup D (\<Union>WWa D f a))") apply simp 
 apply (subgoal_tac "Sup D (\<Union>WWa D f a)  \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 prefer 2 apply blast
 apply (subgoal_tac "Sup D (\<Union>WWa D f a) <\<^sub>(Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) (f (Sup D (\<Union>WWa D f a)))")
 prefer 2 apply (simp add:Iod_def ord_neq_def)
 apply (subgoal_tac "f (Sup D (\<Union>WWa D f a)) = x") prefer 2 apply (rule sym)
 apply assumption
 apply (thin_tac "x = f (Sup D (\<Union>WWa D f a))") apply simp
 apply (subgoal_tac "(Sup D (\<Union>WWa D f a)) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x \<longrightarrow> (Sup D (\<Union>WWa D f a)) \<in> carrier (Iod D (insert x (\<Union>WWa D f a))) \<longrightarrow>      (\<exists>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))). (Sup D (\<Union>WWa D f a)) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<and> y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x)")
 prefer 2 apply simp
 apply (thin_tac "\<forall>xa.  xa <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x \<longrightarrow> xa \<in> carrier (Iod D (insert x (\<Union>WWa D f a))) \<longrightarrow>  (\<exists>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))).  xa <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<and>  y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x)")
 apply (subgoal_tac "Sup D (\<Union>WWa D f a) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
 apply simp
 prefer 2 apply (simp add:Iod_def ord_neq_def)
 apply (subgoal_tac " Sup D (\<Union>WWa D f a) \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
 prefer 2  apply (frule_tac D = D and f = f and a = a in BNTr10, assumption+)
 apply (simp add:Iod_def) apply simp
apply (subgoal_tac "\<forall>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))).  Sup D (\<Union>WWa D f a) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<and> y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x \<longrightarrow> Sup D (segment (Iod D (insert x (\<Union>WWa D f a))) x) = x")
 apply blast
 apply (thin_tac "\<exists>y\<in>carrier (Iod D (insert x (\<Union>WWa D f a))).  Sup D (\<Union>WWa D f a) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y \<and> y <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "y \<noteq> x") prefer 2 apply (simp add:Iod_def ord_neq_def)
 apply (subgoal_tac "y \<in> insert x (\<Union>WWa D f a)") 
  prefer 2 apply (simp add:Iod_def) apply simp
  apply (erule conjE)
  apply (subgoal_tac "\<forall>X\<in>WWa D f a. y \<in> X \<longrightarrow> Sup D (segment (Iod D (insert x (\<Union>WWa D f a))) x) = x") apply blast apply (thin_tac "Bex (WWa D f a) (op \<in> y)") apply (rule ballI) apply (rule impI)
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, assumption+)
 apply (subgoal_tac "y \<in> \<Union>WWa D f a") prefer 2 apply simp apply blast
 apply (subgoal_tac "y \<le>\<^sub>D (Sup D (\<Union>WWa D f a))") prefer 2 apply blast
 apply (subgoal_tac "Sup D (\<Union>WWa D f a) \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
 apply (subgoal_tac "tordered_set (Iod D (insert x (\<Union>WWa D f a)))")
 apply (frule_tac D = "Iod D (insert x (\<Union>WWa D f a))" and a = "Sup D (\<Union>WWa D f a)" and b = y in tordering_not1, assumption+)
  apply (thin_tac "Sup D (\<Union>WWa D f a) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) x")
  apply (thin_tac "well_ordered_set (Iod D (insert x (\<Union>WWa D f a)))")
  apply (thin_tac "Sup D (\<Union>WWa D f a) <\<^sub>(Iod D (insert x (\<Union>WWa D f a))) y")
  apply (thin_tac "Sup D (\<Union>WWa D f a) \<in> carrier (Iod D (insert x (\<Union>WWa D f a)))")
 apply (simp add:Iod_def) apply (simp add:well_ordered_set_def)
 apply assumption
 (** case x = f (Sup D (\<Union>WWa D f a)) done **)
apply (fold ExPre_def) apply simp
 apply (subgoal_tac "\<not> ExPre (Iod D (\<Union>WWa D f a)) x")
 prefer 2 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>z\<in>\<Union>WWa D f a. z \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 prefer 2 apply blast apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+) 
 apply (simp add:WWa_def)
 apply (subgoal_tac "\<not> ExPre (Iod D (\<Union>WWa D f a)) x")
  prefer 2 
  apply (subgoal_tac "ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x") 
  apply (thin_tac "\<exists>xa\<in>WWa D f a. x \<in> xa") apply simp
 apply (thin_tac "\<not> ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x")
 apply (frule_tac D = D and f = f and a = a and b = "f (Sup D (\<Union>WWa D f a))" and x = x in BNTr8_6, assumption+) apply (simp add:funcset_mem)
 apply assumption+ apply simp apply simp
(**-- segment (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x 
                                   = segment (Iod D (\<Union>WWa D f a)) x --**)
apply (subgoal_tac "segment (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x = segment (Iod D (\<Union>WWa D f a)) x") apply simp
 apply (thin_tac "segment (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x = segment (Iod D (\<Union>WWa D f a)) x")
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (thin_tac "well_ordered_set
            (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 apply (thin_tac "\<not> ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x")
 apply (thin_tac "Sup D (\<Union>WWa D f a) \<noteq> f (Sup D (\<Union>WWa D f a))")
 apply (simp add:WWa_def)
 apply (subgoal_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a") apply simp
 apply (thin_tac "\<Union>{W. Wa D W f a} = \<Union>WWa D f a")
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (unfold Wa_def) apply (erule conjE)+ apply (fold Wa_def)
 apply (subgoal_tac "if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x
 else a = a") prefer 2 apply blast
 apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a. if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a")
 apply simp
apply (simp add:WWa_def)
 apply (thin_tac "\<not> ExPre (Iod D (\<Union>WWa D f a)) x")
 apply (thin_tac "\<not> ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x")
 apply (thin_tac "well_ordered_set
            (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 apply (thin_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 apply (rule equalityI)  (*******)
 apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply (case_tac "xa = f (Sup D (\<Union>WWa D f a))")
 apply (subgoal_tac "\<forall>X\<in>WWa D f a. x \<in> X \<longrightarrow> Bex (WWa D f a) (op \<in> xa)")
 apply blast apply (thin_tac "\<exists>xa\<in>WWa D f a. x \<in> xa")
 apply (rule ballI) apply (rule impI) 
 apply (subgoal_tac "x \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))") prefer 2 apply blast
 apply (subgoal_tac "xa \<in> carrier D")
 apply (subgoal_tac "x \<in> carrier D")
 apply (frule S_inductive_ordered [of "D"])
 apply (frule_tac a = xa and b = x and c = "f (Sup D (\<Union>WWa D f a))" in 
 ordering_axiom3 [of "D"], assumption+) apply (simp add:funcset_mem)
 apply assumption+
 apply (subgoal_tac "xa \<noteq> f (Sup D (\<Union>WWa D f a))") apply simp
 apply (rule contrapos_pp, simp+)
  apply (thin_tac "f (Sup D (\<Union>WWa D f a)) \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 apply (subgoal_tac "x \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))") prefer 2 apply blast
 apply (frule_tac a = x and b = "f (Sup D (\<Union>WWa D f a))" in ordering_axiom2 [of "D"], assumption+) apply simp
 apply (subgoal_tac "X \<subseteq> carrier D") apply (simp add:subsetD)
 apply (simp add:WWa_def Wa_def) apply simp
 apply (simp add:funcset_mem) apply simp
apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def)
(**-- ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x \<longrightarrow>
  f (Pre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x) =  x --**)apply (case_tac "x = f (Sup D (\<Union>WWa D f a))")        
 apply (subgoal_tac "Pre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x = Sup D (\<Union>WWa D f a)") apply simp
 apply (rule_tac S = "Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))" and a = x and ?a1.0 = "Sup D (\<Union>WWa D f a)" in UniquePre, assumption+)
 apply (simp add:Iod_def) apply assumption
apply (rule conjI)
 apply (frule_tac D = D and f = f and a = a in BNTr10, assumption+)
 apply (simp add:Iod_def)
apply (rule conjI)
 apply (simp add:Iod_def ord_neq_def)
 apply simp
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "y \<in> insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)")
 prefer 2 apply (simp add:Iod_def) apply simp
 apply (case_tac "y = f (Sup D (\<Union>WWa D f a))") 
 apply (simp add:Iod_def ord_neq_def) apply simp 
 apply (thin_tac "y \<in> carrier
                  (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 apply (thin_tac "ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) 
 (\<Union>WWa D f a))) (f (Sup D (\<Union>WWa D f a)))")
 apply (subgoal_tac "y \<le>\<^sub>D (Sup D (\<Union>WWa D f a))")
 apply (subgoal_tac "y \<in> carrier (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 apply (subgoal_tac "(Sup D (\<Union>WWa D f a)) \<in> carrier (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
 apply (subgoal_tac "tordered_set (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))") 
 apply (frule_tac D = "Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))"  and a = "Sup D (\<Union>WWa D f a)" and b = y in tordering_not1, assumption+)
 apply (simp add:Iod_def) apply (simp add:well_ordered_set_def)
 apply (frule_tac D = D and f = f and a = a in BNTr10, assumption+)
 apply (simp add:Iod_def) apply (simp add:Iod_def) 
 apply (subgoal_tac "\<exists>Y\<in>WWa D f a. y \<in> Y") prefer 2 apply blast
 apply (thin_tac "Bex (WWa D f a) (op \<in> y)") 
 apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_bound, 
            assumption+) 
 apply (frule_tac D = D and f = f and a = a and x = y in BNTr8_3, assumption+)
 apply (simp add:WWa_def) apply blast
apply simp 
 apply (frule_tac D = D and f = f and a = a and b = "f (Sup D (\<Union>WWa D f a))" and x = x in BNTr8_7, assumption+)
 apply (simp add:funcset_mem)
 apply simp
 apply (subgoal_tac "\<exists>X\<in>WWa D f a. x \<in> X") prefer 2 apply simp
 apply (rule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (simp add:WWa_def) apply assumption apply simp
 apply (thin_tac " Pre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x = Pre (Iod D (\<Union>WWa D f a)) x")
 apply (frule_tac D = D and f = f and a = a and b = "f (Sup D (\<Union>WWa D f a))" and x = x in BNTr8_5, assumption+)
 apply (simp add:funcset_mem)
 apply simp
 apply (subgoal_tac "\<exists>X\<in>WWa D f a. x \<in> X") prefer 2 apply simp
 apply (rule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+)
 apply (simp add:WWa_def) 
 apply simp
  apply (thin_tac "well_ordered_set
            (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a)))")
  apply (thin_tac "\<forall>y\<in>WWa D f a. \<forall>z\<in>y.  z \<le>\<^sub>D (f (Sup D (\<Union>WWa D f a)))")
  apply (thin_tac "ExPre (Iod D (insert (f (Sup D (\<Union>WWa D f a))) (\<Union>WWa D f a))) x")
 apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
 apply (unfold WWa_def) apply simp apply (fold WWa_def)
 apply (frule_tac D = D and f = f and a = a and x = x in BNTr8_3, assumption+) 
 apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (unfold Wa_def) apply (erule conjE)+
 apply (subgoal_tac "if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x  else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x
 else a = a") prefer 2 apply blast
 apply (thin_tac "\<forall>x\<in>\<Union>WWa D f a. if ExPre (Iod D (\<Union>WWa D f a)) x then f (Pre (Iod D (\<Union>WWa D f a)) x) = x else if a \<noteq> x then Sup D (segment (Iod D (\<Union>WWa D f a)) x) = x else a = a") apply simp
done

lemma Bourbaki_Nakayama:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<le>\<^sub>D (f x)\<rbrakk> \<Longrightarrow> \<exists>x0\<in>carrier D. f x0 = x0"
apply (frule_tac D = D and f = f and a = a in BNTr11, assumption+)
apply (frule_tac D = D and f = f and a = a in BNTr8, assumption+)
apply (subgoal_tac "well_ordered_set (Iod D (\<Union>WWa D f a))")
 prefer 2 apply (simp add:WWa_def Wa_def)
 apply (subgoal_tac "tordered_set (Iod D (\<Union>WWa D f a))")
 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "(\<Union>WWa D f a) \<subseteq> carrier D")
 prefer 2 apply (rule subsetI) apply (simp add:WWa_def)
 apply (subgoal_tac "\<forall>X. Wa D X f a \<and> x \<in> X \<longrightarrow> x \<in> carrier D")
 apply blast apply (thin_tac "\<exists>xa. Wa D xa f a \<and> x \<in> xa")
 apply (rule allI) apply (rule impI) apply (erule conjE)
apply (subgoal_tac "X \<subseteq> carrier D") apply (simp add:subsetD)
 apply (simp add:Wa_def)
 apply (thin_tac "\<forall>X. X \<subseteq> carrier (Iod D (\<Union>WWa D f a)) \<and> X \<noteq> {} \<longrightarrow>
           Ex (minimum_elem (Iod D (\<Union>WWa D f a)) X)")
 apply (frule S_inductive_ordered [of "D"])
 apply (frule_tac D = D and X = "(\<Union>WWa D f a)" in tordered_Chain, assumption+)
 apply (frule_tac D = D and X = "\<Union>WWa D f a" in S_inductive_sup_mem)
 apply assumption apply blast
apply (simp add:well_ordered_set_def)
done

constdefs
 maxl_fun::"'a OrderedSet \<Rightarrow> 'a \<Rightarrow> 'a"
 "maxl_fun S == \<lambda>x\<in>carrier S. if \<exists>y. y\<in>(upper_bounds S {x}) \<and> y \<noteq> x then
  SOME z. z \<in> (upper_bounds S {x}) \<and> z \<noteq> x else x"

lemma maxl_fun_func:"ordered_set D \<Longrightarrow> maxl_fun D \<in> carrier D \<rightarrow> carrier D"
apply (rule univar_func_test)
apply (rule ballI)
 apply (simp add:maxl_fun_def) apply (rule impI)
 apply (subgoal_tac "(SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<in> upper_bounds D {x} \<and> (SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<noteq> x") 
 prefer 2 apply (rule someI2_ex, assumption+) 
apply (erule conjE)+
apply (simp add:upper_bounds_def upper_bound_def)
done

lemma maxl_fun_maxl:"\<lbrakk>ordered_set D; x \<in> carrier D; maxl_fun D x = x \<rbrakk>
\<Longrightarrow> maximal\<^sub>D x"
apply (simp add:maximal_element_def)
apply (rule ballI) apply (rule impI)
apply (simp add:maxl_fun_def)
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "\<exists>y. y \<in> upper_bounds D {x} \<and> y \<noteq> x") apply simp
apply (subgoal_tac "(SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<in> upper_bounds D {x} \<and> (SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<noteq> x")
prefer 2 apply (rule someI2_ex, assumption+) 
apply (erule conjE) apply simp
apply (thin_tac "(if \<exists>y. y \<in> upper_bounds D {x} \<and> y \<noteq> x then SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x else x) =  x")
apply (subgoal_tac "b \<in> upper_bounds D {x}") prefer 2 
 apply (simp add:upper_bounds_def upper_bound_def)
apply (frule not_sym) apply (thin_tac "x \<noteq> b")
apply blast
done

lemma maxl_fun_asc:"ordered_set D \<Longrightarrow> \<forall>x\<in>carrier D. x \<le>\<^sub>D (maxl_fun D x)"
apply (rule ballI)
apply (simp add:maxl_fun_def)
 apply (rule conjI)
 apply (rule impI)  
 apply (subgoal_tac "(SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<in> upper_bounds D {x} \<and> (SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<noteq> x") 
 prefer 2 apply (rule someI2_ex, assumption+) apply (erule conjE)
 apply (simp add:upper_bounds_def upper_bound_def)
apply (rule impI)
apply (simp add:ordering_axiom1 [of "D"])
done
   
lemma S_inductive_maxl:"\<lbrakk>S_inductive_set D; carrier D \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m. m \<in>carrier D \<and> maximal\<^sub>D m"
apply (frule nonempty_ex [of "carrier D"])
 apply (subgoal_tac "\<forall>a. a \<in> carrier D \<longrightarrow> (\<exists>m. m \<in> carrier D \<and> maximal\<^sub>D m)")
 apply blast apply (thin_tac "\<exists>x. x \<in> carrier D")
apply (rule allI) apply (rule impI)
apply (frule S_inductive_ordered [of "D"])
apply (frule maxl_fun_asc [of "D"])
apply (frule maxl_fun_func [of "D"]) 
apply (frule_tac D = D and f = "maxl_fun D" and a = a in BNTr11, assumption+)
 apply (subgoal_tac "Chain D  (\<Union>WWa D (maxl_fun D) a)")
 apply (frule_tac D = D and X = "\<Union>WWa D (maxl_fun D) a" in S_inductive_sup_mem,  assumption+)
 apply (frule_tac D = D and x = "Sup D (\<Union>WWa D (maxl_fun D) a)" in maxl_fun_maxl,
 assumption+) apply blast
apply (rule_tac D = D and f = "maxl_fun D" and a = a in BNTr8_1, assumption+)
done

constdefs
 Chains :: "'a OrderedSet \<Rightarrow> ('a set) set"
 "Chains D == {C. Chain D C}"


 family_tordered::"'a OrderedSet \<Rightarrow> ('a set) OrderedSet"
  ("(fto _)" [999]1000)
 "fto D == \<lparr>carrier = Chains D , ord_rel = {Z. Z \<in> (Chains D) \<times> (Chains D) \<and> (fst Z) \<subseteq> (snd Z)}, ordering = \<lambda>a\<in>(Chains D). \<lambda>b\<in>(Chains D). a \<subseteq> b\<rparr>"

lemma fto_ordered:"ordered_set D \<Longrightarrow> ordered_set (fto D)"
apply (subst ordered_set_def)
 apply (simp add:family_tordered_def)
 apply auto
done

lemma fto_Chains:"\<lbrakk>ordered_set D; Chain (fto D) CC\<rbrakk> \<Longrightarrow> Chain D (\<Union> CC)"
apply (subgoal_tac "\<Union>CC \<subseteq> carrier D")  
apply (subst Chain_def) apply simp
prefer 2
 apply (rule subsetI)
 apply (simp add:Chain_def) apply (erule conjE) apply (thin_tac "tordered_set (Iod (fto D) CC)")
 apply (subgoal_tac "\<forall>X\<in>CC. x \<in> X \<longrightarrow> x \<in> carrier D")
  apply blast apply (thin_tac "\<exists>X\<in>CC. x \<in> X")
 apply (rule ballI) apply (rule impI) 
 apply (frule_tac A = CC and B = "carrier (fto D)" and c = X in subsetD, assumption+) apply (thin_tac "CC \<subseteq> carrier fto D")
 apply (simp add:family_tordered_def Chains_def Chain_def) apply (erule conjE)
 apply (simp add:subsetD)
(** tordered **)
apply (simp add:tordered_set_def)
 apply (simp add:ordered_set_Iod)
apply (rule ballI)+
 apply (simp add:Iod_def)
 apply (subgoal_tac "\<forall>X1\<in>CC. \<forall>X2\<in>CC. a \<in> X1 \<and> b \<in> X2 \<longrightarrow> a \<le>\<^sub>D b \<or>  b \<le>\<^sub>D a")
 apply blast apply (thin_tac "\<exists>X\<in>CC. a \<in> X") apply (thin_tac "\<exists>X\<in>CC. b \<in> X")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply (simp add:Chain_def) apply (erule conjE)
 apply (simp add:tordered_set_def) apply (erule conjE)+
  apply (subgoal_tac "X1 \<in> carrier (Iod (fto D) CC)")
  apply (subgoal_tac "X2 \<in> carrier (Iod (fto D) CC)")  
  apply (subgoal_tac "X1 \<le>\<^sub>(Iod (fto D) CC) X2 \<or>  X2 \<le>\<^sub>(Iod (fto D) CC) X1")
  prefer 2 apply simp
  apply (thin_tac "\<forall>a\<in>carrier (Iod (fto D) CC). \<forall>b\<in>carrier (Iod (fto D) CC).
                 a \<le>\<^sub>(Iod (fto D) CC) b \<or>  b \<le>\<^sub>(Iod (fto D) CC) a")
  apply (subgoal_tac "X1 \<in> Chains D") apply (subgoal_tac "X2 \<in> Chains D")
  apply (simp add:Iod_def family_tordered_def)
  apply (thin_tac " ordered_set \<lparr>carrier = CC, ord_rel = {x. x \<in> Chains D \<times> Chains D \<and>  fst x \<subseteq> snd x \<and> fst x \<in> CC \<and> snd x \<in> CC},  ordering = \<lambda>a\<in>Chains D. restrict (op \<subseteq> a) (Chains D)\<rparr>")
 prefer 2 apply (frule_tac A = CC and B = "carrier (fto D)" and c = X2 in
              subsetD, assumption+)
          apply (simp add:Iod_def family_tordered_def)
 prefer 2 apply (frule_tac A = CC and B = "carrier (fto D)" and c = X1 in
              subsetD, assumption+)
          apply (simp add:Iod_def family_tordered_def)
 prefer 2 apply (simp add:Iod_def)
 prefer 2 apply (simp add:Iod_def)
apply (case_tac "X1 \<subseteq> X2")
 apply (frule_tac A = X1 and B = X2 and c = a in subsetD, assumption+)
  apply (thin_tac "X1 \<in> Chains D") apply (thin_tac "CC \<subseteq> Chains D")
  apply (simp add:Chains_def Chain_def tordered_set_def) apply (erule conjE)+
  apply (simp add:Iod_def)
 apply simp
 apply (frule_tac A = X2 and B = X1 and c = b in subsetD, assumption+)
  apply (thin_tac "X2 \<in> Chains D") apply (thin_tac "CC \<subseteq> Chains D")
  apply (simp add:Chains_def Chain_def tordered_set_def) apply (erule conjE)+
  apply (simp add:Iod_def)
done

lemma fto_S_inductive:"ordered_set D \<Longrightarrow> S_inductive_set (fto D)"
apply (simp add:S_inductive_set_def)
 apply (simp add:fto_ordered)
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "minimum_elem (fto D) (upper_bounds (fto D) C) (\<Union>C)")  
 apply (subgoal_tac "(\<Union>C) \<in> carrier (fto D)") apply blast
 apply (thin_tac "minimum_elem (fto D) (upper_bounds (fto D) C) (\<Union>C)")
 apply (frule_tac D = D and CC = C in fto_Chains, assumption+)
 apply (subst family_tordered_def) apply simp apply (simp add:Chains_def)
(** \<Union>C is minimum_elem of the upper_bounds **)
apply (simp add:minimum_elem_def) 
 apply (rule conjI)
 apply (simp add:upper_bounds_def upper_bound_def)
 apply (rule conjI)
 apply (subst family_tordered_def) apply (simp add:Chains_def)
 apply (rule_tac D = D and CC = C in fto_Chains, assumption+)
 apply (subgoal_tac "\<forall>z. z\<in>C \<longrightarrow> z \<in>  Chains D")
 apply (frule_tac D = D and CC = C in fto_Chains, assumption+)
 apply (subgoal_tac "\<Union>C \<in> Chains D")
 apply (subst family_tordered_def) apply (simp add:Iod_def)
 apply (rule ballI) apply (rule subsetI) apply simp apply blast
 apply (simp add:Chains_def)
apply (rule allI) apply (rule impI)
 apply (simp add:Chain_def [of "fto D"]) apply (erule conjE)+
 apply (frule_tac A = C and B = "carrier (fto D)" and c = z in subsetD, assumption+)
 apply (simp add:family_tordered_def Iod_def)
apply (rule ballI)
 apply (simp add:upper_bounds_def upper_bound_def) apply (erule conjE)
 apply (subgoal_tac "\<forall>z. z\<in>C \<longrightarrow> z \<in>  Chains D")
 apply (subgoal_tac "\<Union>C \<in> Chains D")
 apply (simp add:family_tordered_def Iod_def)
prefer 2 apply (simp add:Chains_def) 
 apply (rule_tac D = D and CC = C in fto_Chains, assumption+) 
 apply (thin_tac "Chain \<lparr>carrier = Chains D, ord_rel = {Z. Z \<in> Chains D \<times> Chains D \<and> fst Z \<subseteq> snd Z},  ordering = \<lambda>a\<in>Chains D. restrict (op \<subseteq> a) (Chains D)\<rparr>
              C")
 apply (thin_tac "\<forall>z. z \<in> C \<longrightarrow> z \<in> Chains D")
 apply (rule subsetI) apply simp
 apply (subgoal_tac "\<forall>X\<in>C. xa \<in> X \<longrightarrow> xa \<in> x") apply blast
 apply (thin_tac "\<exists>X\<in>C. xa \<in> X") apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "X \<subseteq> x") prefer 2 apply simp
 apply (rule_tac A = X and B = x and c = xa in subsetD, assumption+)
apply (rule allI) apply (rule impI)
 apply (thin_tac "\<forall>s\<in>C.  s \<le>\<^sub>(fto D) x")
 apply (simp add:Chain_def) apply (thin_tac "x \<in> carrier (fto D)")
 apply (erule conjE)
 apply (frule_tac A = C and B = "carrier (fto D)" and c = z in subsetD, assumption+)
  apply (thin_tac "tordered_set (Iod (fto D) C)")
 apply (simp add:family_tordered_def Iod_def)
done 

lemma Hausdorff_ac:"\<lbrakk>ordered_set D; C \<in> carrier (fto D)\<rbrakk> \<Longrightarrow> \<exists>M\<in>carrier (fto D). C \<subseteq> M \<and> maximal\<^sub>(fto D) M"
apply (subgoal_tac "S_inductive_set (Iod (fto D) {S. S \<in> (carrier (fto D)) \<and>
 C \<subseteq> S})")
prefer 2 
  apply (simp add:S_inductive_set_def)
  apply (rule conjI)
  apply (frule fto_ordered [of "D"])
  apply (rule ordered_set_Iod, assumption+)
  apply (rule subsetI) apply simp  
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "Chain (fto D) Ca")
 prefer 2 
  apply (subst Chain_def)
  apply (rule conjI)
  apply (simp add:Chain_def) apply (erule conjE)
  apply (thin_tac "tordered_set (Iod (Iod (fto D) {S. S \<in> carrier (fto D) \<and> 
                                                              C \<subseteq> S}) Ca)")
  apply (simp add:Iod_def)
  apply (rule subsetI) apply (frule_tac A = Ca and B = "{S. S \<in> carrier fto D \<and> C \<subseteq> S}" and c = x in subsetD, assumption+) apply simp
  apply (simp add:Chain_def) apply (erule conjE)
 apply (subgoal_tac "Iod (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) Ca =
    Iod (fto D) Ca") apply simp 
  apply (rule Iod_sub_sub)
   apply (simp add:fto_ordered) apply (simp add:Iod_def)
   apply (rule subsetI) apply simp
(*** case Ca = {} ***)
  apply (case_tac "Ca = {}")
  apply (subgoal_tac "C \<in> carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})")
  apply (subgoal_tac "minimum_elem (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) (upper_bounds (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})  Ca) C")
  apply blast
  apply (simp add:minimum_elem_def)
  apply (simp add:upper_bounds_def upper_bound_def) 
  apply (rule ballI)
   apply (thin_tac "Chain (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) {}")
  apply (simp add:Iod_def) apply (erule conjE)
  apply (subgoal_tac "x \<in> Chains D") apply (subgoal_tac "C \<in> Chains D")
  apply (simp add:family_tordered_def) apply (simp add:family_tordered_def)
  apply (simp add:family_tordered_def)
  apply (thin_tac "Chain (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) Ca")
 apply (simp add:Iod_def)
(** case Ca \<noteq> {} ***) 
  apply (frule fto_S_inductive[of "D"])
   apply (simp add:S_inductive_set_def) apply (erule conjE)
   apply (subgoal_tac "\<exists>x\<in>carrier fto D. minimum_elem (fto D) (upper_bounds (fto D) Ca) x") prefer 2 apply simp
  apply (thin_tac "\<forall>C. Chain (fto D) C \<longrightarrow> (\<exists>x\<in>carrier (fto D). minimum_elem (fto D) (upper_bounds (fto D) C) x)")
  apply (subgoal_tac "\<forall>x0\<in>carrier (fto D). minimum_elem (fto D) (upper_bounds (fto D) Ca) x0 \<longrightarrow> (\<exists>x\<in>carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}). minimum_elem (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) (upper_bounds (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) Ca) x)")
  apply blast
  apply (thin_tac "\<exists>x\<in>carrier (fto D). minimum_elem (fto D) (upper_bounds (fto D) Ca) x")
  apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "x0\<in>carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})")
  apply (subgoal_tac "minimum_elem (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) (upper_bounds (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) Ca) x0")
  apply blast
  apply (simp add:minimum_elem_def) apply (erule conjE)+
  apply (rule conjI)
   apply (thin_tac "\<forall>x\<in>upper_bounds (fto D) Ca.  x0 \<le>\<^sub>(fto D) x")
  apply (simp add:upper_bounds_def upper_bound_def) apply (simp add:Iod_def)
  apply (rule ballI)
  apply (simp add:upper_bounds_def upper_bound_def)
  apply (simp add:Iod_def)
  apply (simp add:minimum_elem_def) apply (erule conjE)
   apply (thin_tac "\<forall>x\<in>upper_bounds (fto D) Ca.  x0 \<le>\<^sub>(fto D)  x")
   apply (simp add:upper_bounds_def upper_bound_def)  
  apply (frule_tac A = Ca in nonempty_ex) apply (thin_tac "Ca \<noteq> {}")
   apply (subgoal_tac "\<forall>Z. Z \<in> Ca \<longrightarrow> x0 \<in> carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})") apply blast apply (thin_tac "\<exists>x. x \<in> Ca")
   apply (rule allI) apply (rule impI)
  apply (subgoal_tac "Z \<le>\<^sub>(fto D) x0") prefer 2 apply simp
  apply (thin_tac "\<forall>s\<in>Ca.  s \<le>\<^sub>(fto D) x0")
  apply (thin_tac "Chain (fto D) Ca")
  apply (simp add:Chain_def) apply (erule conjE)+
   apply (thin_tac "tordered_set
           (Iod (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) Ca)")
   apply (frule_tac A = Ca and B = "carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})" and c = Z in subsetD, assumption+)
   apply (thin_tac "Ca \<subseteq> carrier (Iod (fto D) {S. S \<in> carrier fto D  \<and> C \<subseteq> S})")
  apply (simp add:Iod_def) apply (erule conjE)
  apply (subgoal_tac "C \<in> Chains D") apply (subgoal_tac "x0 \<in> Chains D")
  apply (thin_tac "ordered_set (fto D)")
  apply (simp add:family_tordered_def) 
  apply (thin_tac "ordered_set (fto D)") apply (thin_tac "Z \<le>\<^sub>(fto D) x0")
  apply (simp add:family_tordered_def)  apply (simp add:family_tordered_def)
apply (subgoal_tac "C \<in> carrier (Iod (fto D) {S. S \<in> carrier fto D  \<and> C \<subseteq> S})")
 apply (subgoal_tac "carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) \<noteq> {}") prefer 2 apply blast
 apply (frule_tac D = "Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}" in S_inductive_maxl, assumption+)
 apply (subgoal_tac "\<forall>m. m \<in> carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) \<and> maximal\<^sub>(Iod (fto D) {S. S \<in> carrier fto D  \<and> C \<subseteq> S}) m \<longrightarrow> (\<exists>M\<in>carrier (fto D). C \<subseteq> M \<and> maximal\<^sub>(fto D) M)")  apply blast
 apply (thin_tac "\<exists>m. m \<in> carrier (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S}) \<and> maximal\<^sub>(Iod (fto D) {S. S \<in> carrier fto D  \<and> C \<subseteq> S}) m") 
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "m \<in> carrier (fto D)")
 apply (subgoal_tac "C \<subseteq> m \<and> maximal\<^sub>(fto D) m") apply blast
apply (erule conjE)+
 apply (thin_tac "S_inductive_set (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})")
 apply (simp add:maximal_element_def)
 apply (simp add:Iod_def)
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "m \<in> Chains D") apply (subgoal_tac "b \<in> Chains D")
 apply (simp add:family_tordered_def)
 apply (frule_tac A = C and B = m and C = b in subset_trans, assumption+)
 apply blast apply (simp add:family_tordered_def) 
 apply (simp add:family_tordered_def) 
apply (erule conjE)+
 apply (simp add:Iod_def)
apply (thin_tac "S_inductive_set (Iod (fto D) {S. S \<in> carrier (fto D) \<and> C \<subseteq> S})")
apply (simp add:Iod_def)
done

lemma g_Zorn_lemma1:"\<lbrakk>inductive_set D; Chain D C \<rbrakk> \<Longrightarrow> \<exists>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D C"
apply (subgoal_tac "C \<in> carrier (fto D)")  
 prefer 2 apply (simp add:family_tordered_def Chains_def) 
apply (subgoal_tac "ordered_set D") prefer 2 apply (simp add:inductive_set_def)
apply (frule_tac D = D and C = C in Hausdorff_ac, assumption+) 
apply (subgoal_tac "\<forall>M\<in>carrier (fto D). C \<subseteq> M \<and> maximal\<^sub>(fto D) M \<longrightarrow>
       (\<exists>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D C)") apply blast
 apply (thin_tac "\<exists>M\<in>carrier (fto D). C \<subseteq> M \<and> maximal\<^sub>(fto D) M")
 apply (rule ballI)
 apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "Chain D M") prefer 2 apply (simp add:family_tordered_def Chains_def)
 apply (subgoal_tac "upper_bounds D M \<noteq> {}")
 prefer 2 apply (simp add:inductive_set_def)
 apply (subgoal_tac "Ex (upper_bound D M)") prefer 2 apply simp 
  apply (thin_tac "\<forall>C. Chain D C \<longrightarrow> Ex (upper_bound D C)")
  apply (subgoal_tac "\<forall>t. upper_bound D M t \<longrightarrow> upper_bounds D M \<noteq> {}")
  apply blast apply (thin_tac "Ex (upper_bound D M)")
  apply (rule allI) apply (rule impI)
  apply (subst upper_bounds_def) apply simp apply blast
 apply (frule_tac A = "upper_bounds D M" in nonempty_ex)
 apply (subgoal_tac "\<forall>x. x \<in> upper_bounds D M \<longrightarrow> (\<exists>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D C)") apply blast apply (thin_tac "\<exists>x. x \<in> upper_bounds D M")
 apply (rule allI) apply (rule impI) apply (thin_tac "upper_bounds D M \<noteq> {}")
 apply (subgoal_tac "maximal\<^sub>D x \<and> x \<in> upper_bounds D C")
 apply blast
apply (rule conjI)
 apply (subst maximal_element_def) apply (rule ballI) apply (rule impI)
(** adjunct Chain **)
apply (subgoal_tac "Chain D (M \<union> {b})")
 apply (simp add:maximal_element_def)
 apply (subgoal_tac "(insert b M) \<in> carrier (fto D)") 
  prefer 2 apply (simp add:family_tordered_def) apply (simp add:Chains_def)
 apply (subgoal_tac "M \<le>\<^sub>(fto D) (insert b M) \<longrightarrow> M = (insert b M)")
  prefer 2 apply simp apply (thin_tac "\<forall>b\<in>carrier (fto D).  M \<le>\<^sub>(fto D) b \<longrightarrow> M = b")
 apply (subgoal_tac "M \<le>\<^sub>(fto D) (insert b M)") apply simp
 apply (subgoal_tac "b \<in> M") prefer 2 apply blast
 apply (simp add:upper_bounds_def upper_bound_def)
 apply (erule conjE) apply (subgoal_tac "b \<le>\<^sub>D x") prefer 2 apply simp
 apply (thin_tac "\<forall>s\<in>M. s \<le>\<^sub>D x")
 apply (rule_tac a = x and b = b in ordering_axiom2 [of "D"], assumption+)
 apply (subgoal_tac "M \<in> Chains D") apply (subgoal_tac "(insert b M) \<in> Chains D")
 apply (simp add:family_tordered_def)
 apply (rule subsetI) apply simp
 apply (simp add:Chains_def) apply (simp add:Chains_def)
 (** Chain D (M \<union> {b}) **)
 apply (thin_tac "M \<in> carrier fto D") apply (thin_tac "maximal\<^sub>(fto D) M")
 apply (simp add:Chain_def) apply (erule conjE)+
 apply (subst tordered_set_def) apply (rule conjI)
 apply (rule ordered_set_Iod, assumption+)
 apply (rule subsetI) apply simp 
  apply (case_tac "xa = b") apply simp apply simp apply (simp add:subsetD)
 apply (rule ballI)+
 apply (case_tac "a = b")
  apply (case_tac "ba = b") apply simp
  apply (simp add:Iod_def ordering_axiom1[of "D"]) 
  apply (subgoal_tac "ba \<in> M") prefer 2 apply (simp add:Iod_def)
  apply (subgoal_tac "ba \<le>\<^sub>D b") apply (simp add:Iod_def)
  apply (simp add:upper_bounds_def upper_bound_def) apply (erule conjE)+
  apply (subgoal_tac "ba \<le>\<^sub>D x") prefer 2 apply simp
  apply (rule_tac a = ba and b = x and c = b in ordering_axiom3 [of "D"], assumption+)
  apply (simp add:subsetD) apply assumption+
 apply (case_tac "ba = b")
  apply (subgoal_tac "a \<in> M") prefer 2 apply (simp add:Iod_def) apply simp
  apply (subgoal_tac "a \<le>\<^sub>D b") apply (simp add:Iod_def)
  apply (simp add:upper_bounds_def upper_bound_def) apply (erule conjE)+
  apply (subgoal_tac "a \<le>\<^sub>D x") prefer 2 apply simp
  apply (rule_tac a = a and b = x and c = b in ordering_axiom3 [of "D"], assumption+)
  apply (simp add:subsetD) apply assumption+
  apply (subgoal_tac "a \<in> carrier (Iod D M)")
  apply (subgoal_tac "ba \<in> carrier (Iod D M)")  
  apply (thin_tac "tordered_set (Iod D C)") apply (simp add:tordered_set_def)
  apply (erule conjE)
  apply (subgoal_tac "a \<le>\<^sub>(Iod D M) ba \<or>  ba \<le>\<^sub>(Iod D M) a")
   prefer 2 apply simp
   apply (thin_tac "\<forall>a\<in>carrier (Iod D M). \<forall>b\<in>carrier (Iod D M).  
                        a \<le>\<^sub>(Iod D M) b \<or>  b \<le>\<^sub>(Iod D M) a")
   apply (simp add:Iod_def)
   apply (simp add:Iod_def) apply (simp add:Iod_def)
apply (simp add:upper_bounds_def upper_bound_def)
 apply (erule conjE)
 apply (rule ballI)
 apply (frule_tac A = C and B = M and c = s in subsetD, assumption+)
 apply simp
done

lemma g_Zorn_lemma2:"\<lbrakk>inductive_set D; a \<in> carrier D \<rbrakk> \<Longrightarrow> \<exists>m\<in>carrier D. maximal\<^sub>D m \<and> a \<le>\<^sub>D m"
apply (subgoal_tac "ordered_set D") prefer 2 apply (simp add:inductive_set_def)
apply (frule BNTr1 [of "D" "a"], assumption+)
apply (subgoal_tac "{a} \<subseteq> carrier D") prefer 2 apply simp
apply (frule_tac D = D and X = "{a}" in tordered_Chain, assumption+)
 apply (simp add:well_ordered_set_def)
 apply (frule_tac D = D and C = "{a}" in g_Zorn_lemma1, assumption+)
 apply (subgoal_tac "\<forall>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D {a} \<longrightarrow>
  (\<exists>m\<in>carrier D. maximal\<^sub>D m \<and>  a \<le>\<^sub>D m)") apply blast
 apply (thin_tac "\<exists>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D {a}")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (simp add:upper_bounds_def upper_bound_def) apply (erule conjE)
apply blast
done

lemma g_Zorn_lemma3:"inductive_set D \<Longrightarrow> \<exists>m\<in>carrier D. maximal\<^sub>D m"
apply (subgoal_tac "Chain D {}")
 prefer 2 apply (simp add:Chain_def) apply (simp add:tordered_set_def)
 apply (rule conjI)
 apply (simp add:ordered_set_def)
 apply auto apply (simp add:Iod_def)+
apply (frule_tac D = D and C = "{}" in g_Zorn_lemma1, assumption+) 
 apply (subgoal_tac "\<forall>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D {} \<longrightarrow>
  (\<exists>m\<in>carrier D. maximal\<^sub>D m)") apply blast
 apply (thin_tac "\<exists>m. maximal\<^sub>D m \<and> m \<in> upper_bounds D {}")
 apply (rule allI)
 apply (rule impI) apply (erule conjE)
 apply (simp add:upper_bounds_def upper_bound_def) 
 apply blast
done

chapter "3. Group Theory. Focused on Jordan Hoelder theorem"
    

section "1. Definition of a Group"

record 'a GroupType = "'a Base" + 
  tOp      :: "['a, 'a ] \<Rightarrow> 'a" 
  iOp      :: "'a  \<Rightarrow>  'a"
  one     :: "'a"  

constdefs
 group :: "('a, 'more) GroupType_scheme  \<Rightarrow> bool"
     "group G  == (tOp G): carrier G \<rightarrow> carrier G \<rightarrow> carrier G \<and> 
	          (iOp G) \<in> carrier G \<rightarrow> carrier G \<and>  
                  (one G) \<in>  carrier G  \<and> 
                (\<forall> x \<in> carrier G. \<forall> y \<in> carrier G. \<forall> z \<in> carrier G.
                       (tOp G (one G) x = x)  \<and>  
                       (tOp G (iOp G x) x  = one G)  \<and>  
                       (tOp G (tOp G x y) z =
			tOp G (x) (tOp G y z)))"  

 subgroup :: "[('a, 'more) GroupType_scheme, 'a set] \<Rightarrow> bool"
  "subgroup G H == (H \<subseteq> carrier G) \<and> (\<forall>x \<in> H. \<forall>y \<in> H. (tOp G x y \<in> H)) \<and>
       (\<forall>x \<in> H. (iOp G x \<in> H)) \<and> ((one G) \<in> H) "

syntax
  "@SG" :: "['a set, ('a, 'more) GroupType_scheme] => bool" ("_ \<guillemotleft> _" [61,60]60)

translations
  "H \<guillemotleft> G" == "subgroup G H"

constdefs

   r_coset  :: "[('a, 'more) GroupType_scheme, 'a set, 'a] \<Rightarrow> 'a set"
      "r_coset G H a == {b. \<exists> h \<in> H. (tOp G) h a = b}"

   l_coset  ::  "[('a, 'more) GroupType_scheme, 'a, 'a set] \<Rightarrow> 'a set"
      "l_coset G a H  == {b. \<exists> h \<in> H. tOp G a h = b}" 

syntax
  "@R_COS" :: "['a set, ('a, 'more) GroupType_scheme, 'a] \<Rightarrow> 'a set"
        ("(3_\<^sub>_/ _)" [82,83,82]82)
  "@L_COS" :: "['a, 'a set, ('a, 'more) GroupType_scheme] \<Rightarrow> 'a set"
         ("(3_/ _\<^sub>_)" [82,82,83]82)
translations
   "H\<^sub>G a" == "r_coset G H a"
   "a H\<^sub>G" == "l_coset G a H"

constdefs
   nsubgroup  :: "('a, 'more) GroupType_scheme \<Rightarrow> 'a set \<Rightarrow> bool"
      "nsubgroup G H  == (group G) \<and> (subgroup G H) \<and>   
          (\<forall>x \<in> carrier G. r_coset G H x = l_coset G x H)" 

syntax (xsymbols)
  "@NS"  :: "['a set, ('a, 'more) GroupType_scheme] => bool"
                 ("(_ \<lhd> _)" [60,61]60)

translations
  "N \<lhd> G" == " nsubgroup G N"
constdefs
   set_r_cos :: "[('a, 'more) GroupType_scheme, 'a set] 
                                  \<Rightarrow> 'a set set"
      "set_r_cos G H == { C. \<exists> a \<in> carrier G. C = r_coset G H a}"

   cosiOp :: "[('a, 'more) GroupType_scheme, 'a set]  \<Rightarrow> 'a set \<Rightarrow> 'a set"
   "cosiOp G H ==\<lambda>X\<in>set_r_cos G H. {z. \<exists> x \<in> X . \<exists> h \<in> H. (tOp G h (iOp G  x) = z)}"      
 
   costOp :: "[('a, 'more) GroupType_scheme, 'a set] 
                            \<Rightarrow> (['a set, 'a set] \<Rightarrow> 'a set)" 
    
    "costOp G H == \<lambda>X\<in>set_r_cos G H. \<lambda>Y\<in>set_r_cos G H. 
                          {z. \<exists> x \<in> X. \<exists> y \<in> Y. tOp G x y = z}" 
constdefs

 qgrp :: "[('a, 'more) GroupType_scheme, 'a set] \<Rightarrow> 
         \<lparr> carrier :: 'a set set, tOp :: ['a set, 'a set] \<Rightarrow> 'a set,
           iOp :: 'a set \<Rightarrow> 'a set, one :: 'a set \<rparr>"
 
   "qgrp G H  ==  \<lparr> carrier = set_r_cos G H, 
       tOp = \<lambda>X. \<lambda>Y. (costOp G H X Y), 
	  iOp = \<lambda>X. (cosiOp G H X), one = H \<rparr>" 

constdefs
   Pj :: "[('a, 'more) GroupType_scheme, 'a set] \<Rightarrow>  ( 'a => 'a set)" 
      "Pj G H == \<lambda>x \<in> carrier G. r_coset G H x"        

 syntax 
  "@QGRP" :: "([('a, 'more) GroupType_scheme, 'a set] => ('a set) GroupType)"
              (infixl "'/'" 200)  
  "@BOP1" :: "['a, ('a, 'more) GroupType_scheme, 'a] \<Rightarrow> 'a" 
                                 ("(3_/ \<cdot>\<^sub>_/ _)" [70,70,71]70)
  "@IOP1" :: "['a, ('a, 'more) GroupType_scheme] \<Rightarrow> 'a" ("(_\<inverse>\<^sup>_)" [72,73]72)
  "@ONE"  :: "('a, 'more) GroupType_scheme \<Rightarrow> 'a"
                        ("('1\<^sub>_ )" [75]74)
translations
  "x \<cdot>\<^sub>G y" == "tOp G x y"
  "G / H" == "qgrp G H"
  "x\<inverse>\<^sup>G" == "iOp G x"
  "1\<^sub>G"  == "one G"

constdefs
  gHom ::"[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme]
                                   \<Rightarrow> ('a  \<Rightarrow> 'b) set"
  "gHom F G =={f. (f \<in> extensional (carrier F) \<and> f \<in> carrier F \<rightarrow> carrier G) \<and>   
            (\<forall>x \<in> carrier F. \<forall>y \<in> carrier F.  
                f (tOp F x y) = tOp G (f x) (f y))}"
 
  gkernel :: "[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme, 
                      'a \<Rightarrow> 'b]  \<Rightarrow> 'a set"  
     "gkernel F G f == {x. (x \<in> carrier F) \<and> (f x = one G)}"

  Invim::"[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme, 
     'a \<Rightarrow> 'b, 'b set]  \<Rightarrow> 'a set"  
     "Invim F G f K == {x. (x \<in> carrier F) \<and> (f x \<in> K)}"

syntax 
 "@GKER"::"[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme,
    'a \<Rightarrow> 'b ] \<Rightarrow> 'a set" ("(3gker\<^sub>_\<^sub>,\<^sub>_/_ )" [88,88,89]88)

translations
     "gker\<^sub>F\<^sub>,\<^sub>G f" == "gkernel F G f"

constdefs
  gsurjec :: "[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme, 
             'a \<Rightarrow> 'b] \<Rightarrow> bool"  ("(3gsurjec\<^sub>_\<^sub>,\<^sub>_/ _)" [88,88,89]88)
  "gsurjec\<^sub>F\<^sub>,\<^sub>G f  == (f \<in> gHom F G) \<and> (surj_to f (carrier F) (carrier G))" 


  ginjec ::  "[('a, 'more) GroupType_scheme, ('b, 'more1) GroupType_scheme, 
             'a \<Rightarrow> 'b]  \<Rightarrow> bool"    ("(3ginjec\<^sub>_\<^sub>,\<^sub>_/ _)" [88,88,89]88) 
     "ginjec\<^sub>F\<^sub>,\<^sub>G f == (f \<in> gHom F G) \<and>  (inj_on f (carrier F))"

  gbijec :: "[('a, 'm) GroupType_scheme, ('b, 'm1) GroupType_scheme, 'a \<Rightarrow> 'b]
             \<Rightarrow> bool"       ("(3gbijec\<^sub>_\<^sub>,\<^sub>_/ _)" [88,88,89]88)
      "gbijec\<^sub>F\<^sub>,\<^sub>G f  ==  (gsurjec\<^sub>F\<^sub>,\<^sub>G f) \<and> (ginjec\<^sub>F\<^sub>,\<^sub>G f)"

constdefs
  Ugp :: "('a, 'm) GroupType_scheme \<Rightarrow> bool"
  "Ugp E == group E \<and> carrier E = {1\<^sub>E}"



constdefs
  isomorphism:: "[('a, 'm) GroupType_scheme, ('b, 'm1) GroupType_scheme]
                         \<Rightarrow> bool"   (infixr "\<cong>" 100)
   "F \<cong> G == \<exists>f. (gbijec\<^sub>F\<^sub>,\<^sub>G f)"
constdefs
  consthom::"[('a, 'm) GroupType_scheme, ('b, 'm1) GroupType_scheme] 
                           \<Rightarrow> ('a \<Rightarrow> 'b)"
   "consthom F G == \<lambda>x\<in>carrier F. (1\<^sub>G)" 

constdefs
 cmpghom:: "[('a, 'm) GroupType_scheme, 'b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c"
 "cmpghom F g f == compose (carrier F) g f"  

syntax
   "@GCOMP" :: "['b \<Rightarrow> 'c, ('a, 'm) GroupType_scheme, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c"
   ("(3_ \<circ>\<^sub>_ _)" [88, 88, 89]88)
translations
"g \<circ>\<^sub>F f"=="cmpghom F g f"

lemma ex_one: " group G \<Longrightarrow> 1\<^sub>G \<in> carrier G" 
apply (simp only: group_def)
done

lemma tOp_closed [simp]: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G \<rbrakk> 
       \<Longrightarrow> a \<cdot>\<^sub>G b \<in> carrier G "
proof -
 assume p1:"group G" and p2:"a \<in> carrier G" and p3:"b \<in> carrier G"
 from p1 have q1:"tOp G \<in> carrier G \<rightarrow> carrier G \<rightarrow> carrier G"
  by  (simp add:group_def)  
 from p1 and p2 and p3 and q1 show ?thesis
  apply (simp add:bivar_fun_mem)
 done 
qed

lemma iOp_closed [simp] : "\<lbrakk> group G ; a \<in> carrier G \<rbrakk> 
        \<Longrightarrow> a\<inverse>\<^sup>G \<in> carrier G"
proof -
 assume p1:"group G" and p2:"a \<in> carrier G"
 from p1 have q1:"iOp G : carrier G \<rightarrow> carrier G"
  by (simp add:group_def)
 from p1 and p2 and q1 show ?thesis
  apply (simp add: funcset_mem)
 done
qed

lemma subg_subset: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> H \<subseteq> carrier G"
apply (simp add: subgroup_def)
done

lemma subg_subset1:"\<lbrakk> group G; H \<guillemotleft> G; h \<in> H \<rbrakk> \<Longrightarrow> h \<in> carrier G"
apply (frule subg_subset [of "G" "H"], assumption+)
apply (simp only:subsetD)
done

lemma tOp_closed_subr:"\<lbrakk> group G; H \<guillemotleft> G; x \<in> carrier G; h \<in> H \<rbrakk> \<Longrightarrow>
      x \<cdot>\<^sub>G h \<in> carrier G"
apply (frule subg_subset1 [of "G" "H" "h"], assumption+)
apply simp
done

lemma tOp_closed_subl:"\<lbrakk> group G; H \<guillemotleft> G; x \<in> carrier G; h \<in> H \<rbrakk> \<Longrightarrow>
        h \<cdot>\<^sub>G x \<in> carrier G"
apply (frule subg_subset1 [of "G" "H" "h"], assumption+)
apply simp
done

lemma subg_tOp_closed: "\<lbrakk> group G; H \<guillemotleft> G ; h1 \<in> H; h2 \<in> H \<rbrakk> 
     \<Longrightarrow> h1 \<cdot>\<^sub>G h2 \<in> H" 
apply (simp add:subgroup_def)
done

lemma subg_one_closed: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> 
     \<Longrightarrow> 1\<^sub>G  \<in> H" 
apply (simp add: subgroup_def)
done

lemma nsubg_subg: "\<lbrakk> group G; H \<lhd>  G \<rbrakk> \<Longrightarrow> H \<guillemotleft> G"
apply (simp add: nsubgroup_def)
done

lemma nsubg_subset:"\<lbrakk> group G; H \<lhd>  G \<rbrakk> \<Longrightarrow> H \<subseteq> carrier G"
apply (frule nsubg_subg, assumption)
apply (simp add:subg_subset)
done

lemma nsubg_lr_cos_eq:"\<lbrakk>group G; H \<lhd> G; a\<in>carrier G\<rbrakk> \<Longrightarrow>
        l_coset G a H = r_coset G H a"
apply (simp add: nsubgroup_def)
done

lemma subg_iOp_closed: "\<lbrakk> group G; H \<guillemotleft> G; x \<in> H \<rbrakk> \<Longrightarrow> iOp G x \<in> H"
apply (simp add: subgroup_def)
done

lemma subg_iOptOp_closed: "\<lbrakk>group G; H \<guillemotleft> G; a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> H"
apply (rule subg_tOp_closed, assumption+)
apply (simp add:subg_iOp_closed)
apply assumption
done

lemma subg_tOpiOp_closed: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> H ; b \<in> H \<rbrakk> \<Longrightarrow>
    a \<cdot>\<^sub>G b\<inverse>\<^sup>G\<in> H"
apply (simp add:subgroup_def)
done

constdefs
  subg_gen :: "[('a, 'more) GroupType_scheme, 'a set] \<Rightarrow> 'a set"
    "subg_gen G A == \<Inter> {H. ((H \<guillemotleft> G) \<and> (A \<subseteq> H))}" 

lemma smallest_subg_gen: "\<lbrakk> group G; A \<subseteq> carrier G; H \<guillemotleft> G; A \<subseteq> H \<rbrakk> \<Longrightarrow>
       subg_gen G A \<subseteq> H"
apply (simp add:subg_gen_def)
apply auto
done

lemma special_subg_G: "group G \<Longrightarrow> (carrier G) \<guillemotleft> G"
apply (simp add:subgroup_def)
apply (simp add:group_def)
done

lemma subg_generated: "\<lbrakk> group G; A \<subseteq> carrier G \<rbrakk> \<Longrightarrow> subg_gen G A \<guillemotleft> G"
apply (simp add:subgroup_def)
apply (rule conjI)
 apply (rule subsetI) apply (simp add:subg_gen_def)
 apply (frule special_subg_G)
 apply blast

apply (rule conjI)
apply (rule ballI)+
apply (simp add:subg_gen_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:subg_tOp_closed)
apply (rule conjI)
 apply (rule ballI)
 apply (simp add:subg_gen_def) apply (rule allI) apply (rule impI)
 apply (simp add:subg_iOp_closed)
 apply (simp add:subg_gen_def) apply (rule allI) apply (rule impI)
 apply (simp add:subg_one_closed)
done

lemma inter_subgs: "\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G \<rbrakk> \<Longrightarrow> (H \<inter> K) \<guillemotleft> G"
apply (simp add:subgroup_def)
apply auto
done

section "2. non_commutative Groups" 
  
lemma tOp_tr0: "group G \<Longrightarrow> iOp G \<in> carrier G \<rightarrow> carrier G \<and> 
  tOp G \<in> carrier G \<rightarrow> carrier G \<rightarrow> carrier G"
apply (simp add:group_def)
done

lemma iOptOp_closed: "\<lbrakk>group G; a \<in> carrier G ; b \<in> carrier G\<rbrakk> \<Longrightarrow>
       a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> carrier G "
apply (rule tOp_closed, assumption)
apply simp+
done  

lemma l_one [simp]: "\<lbrakk> group G; a \<in> carrier G \<rbrakk> 
                               \<Longrightarrow> (1\<^sub>G) \<cdot>\<^sub>G a = a"
apply  (simp only:group_def)
done

lemma l_onei: "\<lbrakk>group G; a \<in> carrier G\<rbrakk> \<Longrightarrow> (1\<^sub>G) \<cdot>\<^sub>G a\<inverse>\<^sup>G = a\<inverse>\<^sup>G"
apply (rule l_one)
apply (assumption)
apply simp 
done

(* left inverse *)
lemma iOp_l_inv : "\<lbrakk> group G; a \<in> carrier G \<rbrakk> \<Longrightarrow>  a\<inverse>\<^sup>G \<cdot>\<^sub>G a = 1\<^sub>G"
apply (simp only: group_def)
done

lemma l_invTr1:  "\<lbrakk> group G; a \<in> carrier G \<rbrakk> \<Longrightarrow> (a\<inverse>\<^sup>G)\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G = 1\<^sub>G"
apply (rule iOp_l_inv)
apply (assumption) apply simp
done

lemma tOp_assoc: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk>
   \<Longrightarrow> (a \<cdot>\<^sub>G b) \<cdot>\<^sub>G c = a \<cdot>\<^sub>G (b \<cdot>\<^sub>G c)"  
apply (simp only:group_def)
done


lemma tOp_bothl: "\<lbrakk> group G; x \<in> carrier G; y \<in> carrier G; a \<in> carrier G;
  x = y \<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G x = a \<cdot>\<^sub>G y"
apply simp
done

lemma tOp_bothr: "\<lbrakk> group G; x \<in> carrier G; y \<in> carrier G; a \<in> carrier G;
  x = y \<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>G a  = y \<cdot>\<^sub>G a"
apply simp
done

lemma bothl_eq: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G; y \<in> carrier G;
   a \<cdot>\<^sub>G x = a \<cdot>\<^sub>G y \<rbrakk> \<Longrightarrow> x = y "
apply (subgoal_tac "x = tOp G (iOp G a) (tOp G a x)")
apply (simp add:tOp_assoc [THEN sym])
apply (simp add:iOp_l_inv) apply (thin_tac " a \<cdot>\<^sub>G x =  a \<cdot>\<^sub>G y")
apply (simp add:tOp_assoc [THEN sym] iOp_l_inv)
done

lemma invboth1_eq: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G; 
  y \<in> carrier G; a\<inverse>\<^sup>G \<cdot>\<^sub>G x = a\<inverse>\<^sup>G \<cdot>\<^sub>G y \<rbrakk>
   \<Longrightarrow> x = y "
apply (rule bothl_eq [of "G" "iOp G a" "x" "y"], assumption+)
apply simp+
done
                                        
lemma tOp_assocTr41: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; c \<in> 
 carrier G; d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G b \<cdot>\<^sub>G c \<cdot>\<^sub>G d = a \<cdot>\<^sub>G b \<cdot>\<^sub>G (c \<cdot>\<^sub>G d)"
apply (rule trans)
apply (rule tOp_assoc, assumption+)
apply simp+
done

lemma tOp_assocTr42: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; c \<in> 
 carrier G; d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G b \<cdot>\<^sub>G c \<cdot>\<^sub>G d = a \<cdot>\<^sub>G (b \<cdot>\<^sub>G c) \<cdot>\<^sub>G d"
apply (rule tOp_bothr, assumption+)
apply simp+
apply (simp add:tOp_assoc)
done

lemma tOp_assocTr43: "\<lbrakk>group G; a\<in>carrier G; b\<in>carrier G; c\<in>carrier G; 
 d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G b \<cdot>\<^sub>G (c \<cdot>\<^sub>G d) = a \<cdot>\<^sub>G b \<cdot>\<^sub>G c \<cdot>\<^sub>G d"
apply (simp add:tOp_assocTr41 [THEN sym] tOp_assocTr42)
done

lemma iOp_r_inv: "\<lbrakk> group G; a \<in> carrier G \<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G a\<inverse>\<^sup>G = 1\<^sub>G"
apply (frule l_one [of "G" "a \<cdot>\<^sub>G a\<inverse>\<^sup>G"])
 apply (rule tOp_closed, assumption+)
  apply simp
apply (frule l_invTr1, assumption)
 apply (rotate_tac -1) apply (frule sym)
apply simp apply (thin_tac "1\<^sub>G =  a\<inverse>\<^sup>G\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G")
apply (simp add:tOp_assocTr43)
 apply (frule sym) apply (thin_tac "a\<inverse>\<^sup>G\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G \<cdot>\<^sub>G a \<cdot>\<^sub>G a\<inverse>\<^sup>G =  a \<cdot>\<^sub>G a\<inverse>\<^sup>G")
apply simp
apply (subst tOp_assocTr42, assumption+) apply simp+
apply (subst iOp_l_inv, assumption+) apply simp
apply (subst iOp_l_inv, assumption+) 
apply (subst tOp_assoc, assumption+) apply simp+
apply (simp add:ex_one) apply simp+
apply (subst iOp_l_inv, assumption+)
apply simp+
done


lemma tOp_assocTr44: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; 
c \<in> carrier G; d \<in> carrier G \<rbrakk> \<Longrightarrow> (a\<inverse>\<^sup>G) \<cdot>\<^sub>G b \<cdot>\<^sub>G ((c\<inverse>\<^sup>G) \<cdot>\<^sub>G d) = 
       a\<inverse>\<^sup>G \<cdot>\<^sub>G ((b \<cdot>\<^sub>G (c\<inverse>\<^sup>G)) \<cdot>\<^sub>G d)"  
 apply (subst tOp_assoc [of "G" "a\<inverse>\<^sup>G" "b" "c\<inverse>\<^sup>G \<cdot>\<^sub>G d"], assumption+)
  apply simp apply assumption
  apply (rule tOp_closed, assumption+)
  apply simp apply assumption
 apply (simp add:tOp_assoc [THEN sym])
done

lemma tOp_assocTr45:  "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G; 
d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G b \<cdot>\<^sub>G c \<cdot>\<^sub>G d = a \<cdot>\<^sub>G (b \<cdot>\<^sub>G (c \<cdot>\<^sub>G d))"
apply (subst tOp_assoc, assumption+)+
 apply simp+
 apply (simp add:tOp_assoc)
done
 
lemma r_one: "\<lbrakk> group G; a \<in> carrier G \<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G (1\<^sub>G) = a"
apply (subst iOp_l_inv [THEN sym])
apply (assumption)+
apply (subst tOp_assoc [THEN sym], assumption+)
apply simp_all
apply (simp add:iOp_r_inv)+
done

lemma one_unique:" \<lbrakk> group G; a \<in> carrier G; x \<in> carrier G;
  x \<cdot>\<^sub>G a = x \<rbrakk> \<Longrightarrow>  a = 1\<^sub>G "

apply (rule bothl_eq[of "G" "x"], assumption+)
apply (simp only:group_def)
apply (subst r_one, assumption+)
done

lemma inv_one:"group G \<Longrightarrow> (1\<^sub>G)\<inverse>\<^sup>G = 1\<^sub>G "
apply (frule iOp_l_inv [of "G" "1\<^sub>G"], simp add:ex_one)
apply (frule ex_one [of "G"])
apply (frule iOp_closed [of "G" "1\<^sub>G"], assumption+)
apply (frule r_one [of "G" "(1\<^sub>G)\<inverse>\<^sup>G"], assumption+)
apply auto
done

lemma special_subg_e: "group G \<Longrightarrow> {1\<^sub>G} \<guillemotleft> G"
apply (simp add:subgroup_def)
apply (simp add:ex_one inv_one)
done

lemma iOp_invTr1: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G;
   a = x\<inverse>\<^sup>G \<rbrakk> \<Longrightarrow> x = a\<inverse>\<^sup>G"
apply (rule bothl_eq [of "G" "a" _], assumption+)
apply (simp add: iOp_r_inv iOp_l_inv)+
done

lemma iOp_invTr2: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G;
    x \<cdot>\<^sub>G a = x \<cdot>\<^sub>G x\<inverse>\<^sup>G \<rbrakk> \<Longrightarrow>  x = a\<inverse>\<^sup>G "
apply (rule iOp_invTr1, assumption+)
apply (rule bothl_eq [of "G" "x" "a" "iOp G x"], assumption+)
apply simp+
done

lemma inv1_unique: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G;
 x \<cdot>\<^sub>G a = 1\<^sub>G \<rbrakk> \<Longrightarrow> x = a\<inverse>\<^sup>G"
apply (rule iOp_invTr2, assumption+) 
apply (simp only: iOp_r_inv)
done
 
lemma r_oneUnique: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G; 
              a \<cdot>\<^sub>G x = a \<rbrakk>  \<Longrightarrow> x = 1\<^sub>G"
apply (rule bothl_eq, assumption+)
apply (simp only:group_def)
apply (simp add: r_one)
done

lemma r_invUnique: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G;
 a \<cdot>\<^sub>G x = 1\<^sub>G \<rbrakk> \<Longrightarrow> x = a\<inverse>\<^sup>G"
apply (rule bothl_eq, assumption+)
apply simp
apply (simp add: iOp_r_inv)
done

lemma iOp_invinv: "\<lbrakk> group G; a \<in> carrier G \<rbrakk> \<Longrightarrow> (a\<inverse>\<^sup>G)\<inverse>\<^sup>G = a"
apply (subgoal_tac "(a\<inverse>\<^sup>G)\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G \<cdot>\<^sub>G a = a")
apply (simp add:tOp_assoc) apply (simp add:iOp_l_inv) 
apply (simp add:r_one)
apply (subst iOp_l_inv, assumption+, simp+)+
done

lemma invofab: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G \<rbrakk> \<Longrightarrow>
   (a \<cdot>\<^sub>G b)\<inverse>\<^sup>G = b\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G "

apply (rule bothl_eq [of "G" "tOp G a b" "iOp G (tOp G a b)" 
 "tOp G (iOp G b) (iOp G a)"], assumption+, simp+)
apply (subst iOp_r_inv [of "G" "tOp G a b"], assumption+, simp)
apply (subst tOp_assocTr43, assumption+, simp+)
apply (subst tOp_assocTr42, assumption+, simp+)
apply (simp add:iOp_r_inv r_one)
done

lemma solOfEq1: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; x \<in> carrier G;
 a \<cdot>\<^sub>G x = b \<rbrakk> \<Longrightarrow> x = a\<inverse>\<^sup>G \<cdot>\<^sub>G b"
apply (rule bothl_eq[of "G" _ _ _], assumption+)
apply simp+
apply (simp add:tOp_assoc[THEN sym] iOp_r_inv)
done

lemma solOfEq2: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; x \<in> carrier G;
 x \<cdot>\<^sub>G a = b \<rbrakk> \<Longrightarrow> x = b \<cdot>\<^sub>G a\<inverse>\<^sup>G "

apply (insert tOp_bothr[of "G" " tOp G x a" "b" "iOp G a"] )
apply (insert tOp_assoc [of "G" "x" "a" "iOp G a"])
apply (simp add:iOp_r_inv r_one)
done

lemma tOp_in_subg:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> carrier G;
  x \<cdot>\<^sub>G a \<in> H \<rbrakk> \<Longrightarrow> \<exists> h \<in> H. (h \<cdot>\<^sub>G a\<inverse>\<^sup>G = x)" 
apply (subgoal_tac "tOp G (tOp G x a) (iOp G a) = x") 
apply auto
apply (simp add:tOp_assoc iOp_r_inv r_one)
done  

lemma rone_in_subg: "\<lbrakk>group G; H \<guillemotleft> G; h \<in> H\<rbrakk> \<Longrightarrow> h \<cdot>\<^sub>G (1\<^sub>G) = h"
apply (frule subg_subset [of "G" "H"], assumption)
apply (frule subsetD, assumption+)
apply (simp add:r_one)
done

lemma lone_in_subg: "\<lbrakk>group G; H \<guillemotleft> G; h \<in> H\<rbrakk> \<Longrightarrow> (1\<^sub>G) \<cdot>\<^sub>G h = h"
apply (frule subg_subset [of "G" "H"], assumption+)
apply (frule subsetD, assumption+)
apply simp
done

lemma both_invr: "\<lbrakk> group G; a \<in> carrier G; x \<in> carrier G; y \<in> carrier G;
   x \<cdot>\<^sub>G a = y \<cdot>\<^sub>G a \<rbrakk> \<Longrightarrow> x = y "
apply (subgoal_tac  "x \<cdot>\<^sub>G a \<cdot>\<^sub>G a\<inverse>\<^sup>G =  y \<cdot>\<^sub>G a \<cdot>\<^sub>G a\<inverse>\<^sup>G")
 apply (thin_tac "x \<cdot>\<^sub>G a =  y \<cdot>\<^sub>G a") 
 apply (simp add:tOp_assoc iOp_r_inv r_one)
apply simp
done

lemma eqTr1: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; 
                  a \<cdot>\<^sub>G b\<inverse>\<^sup>G = 1\<^sub>G \<rbrakk> \<Longrightarrow> a = b"
apply (subgoal_tac "tOp G (tOp G a (iOp G b)) b = a")
apply (rotate_tac 4) apply simp apply (thin_tac "a \<cdot>\<^sub>G b\<inverse>\<^sup>G = 1\<^sub>G")
apply (rotate_tac 3)
apply (frule l_one, assumption+) apply simp
apply (subst tOp_assoc, assumption+)
apply simp+
apply (simp add:iOp_l_inv r_one)  
done

lemma eqTr2: "\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; 
                  a\<inverse>\<^sup>G \<cdot>\<^sub>G b = 1\<^sub>G \<rbrakk> \<Longrightarrow> a = b"
apply (subgoal_tac "tOp G a (tOp G (iOp G a) b) = b")
apply (simp add:tOp_assoc [THEN sym])
apply (simp add:r_one)
 apply (thin_tac "a\<inverse>\<^sup>G \<cdot>\<^sub>G b = 1\<^sub>G")
apply (simp add:tOp_assoc [THEN sym])
apply (simp add:iOp_r_inv)
done

lemma one_in_subg: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> 1\<^sub>G \<in> H"
apply (simp only:subgroup_def)
done

lemma subg_l_inv: "\<lbrakk> group G; H \<guillemotleft> G; x \<in> H \<rbrakk> \<Longrightarrow> x\<inverse>\<^sup>G \<cdot>\<^sub>G x = 1\<^sub>G"
apply (frule subg_subset1, assumption+)
apply (simp add:iOp_l_inv)
done

lemma subg_l_one: "\<lbrakk> group G; H \<guillemotleft> G; x \<in> H \<rbrakk> \<Longrightarrow> (1\<^sub>G) \<cdot>\<^sub>G x = x"
apply (frule subg_subset1, assumption+)
apply simp
done

lemma subg_tOp_assoc: "\<lbrakk> group G; H \<guillemotleft> G; x \<in> H; y \<in> H; z \<in> H\<rbrakk> \<Longrightarrow>
  x \<cdot>\<^sub>G (y \<cdot>\<^sub>G z) = (x \<cdot>\<^sub>G y) \<cdot>\<^sub>G z" 
apply (frule subg_subset1 [of "G" "H" "x"], assumption+)
apply (frule subg_subset1 [of "G" "H" "y"], assumption+)
apply (frule subg_subset1 [of "G" "H" "z"], assumption+)
apply (simp add:tOp_assoc [THEN sym])
done

lemma subg_condTr1:"\<lbrakk>group G; H \<subseteq> carrier G; H \<noteq> {};
   \<forall>a. \<forall>b. a \<in> H \<and> b\<in> H \<longrightarrow>  a \<cdot>\<^sub>G b\<inverse>\<^sup>G\<in> H\<rbrakk> \<Longrightarrow> 1\<^sub>G \<in> H"
apply (frule  nonempty_ex [of "H"])
apply (subgoal_tac "\<forall>a. a\<in>H \<longrightarrow> 1\<^sub>G \<in> H")
apply blast apply (thin_tac "\<exists>a. a \<in> H")
apply (rule allI) apply (rule impI)
apply (subgoal_tac "a \<cdot>\<^sub>G a\<inverse>\<^sup>G \<in> H")
apply (frule_tac c = a in subsetD [of "H" "carrier G"], assumption)
 apply (simp add:iOp_r_inv)
 apply blast
done

lemma subg_condTr2:"\<lbrakk>group G; H \<subseteq> carrier G; a \<in> H;
   \<forall>a. \<forall>b. a \<in> H \<and> b\<in> H \<longrightarrow>  a \<cdot>\<^sub>G b\<inverse>\<^sup>G\<in> H\<rbrakk> \<Longrightarrow> a\<inverse>\<^sup>G \<in> H"
apply (frule subg_condTr1, assumption+)
 apply blast
 apply assumption
apply (subgoal_tac "1\<^sub>G \<cdot>\<^sub>G a\<inverse>\<^sup>G \<in> H")
 apply (thin_tac "\<forall>a b. a \<in> H \<and> b \<in> H \<longrightarrow>  a \<cdot>\<^sub>G b\<inverse>\<^sup>G \<in> H")
 apply (frule subsetD [of "H" "carrier G" "a"], assumption+)
 apply (frule iOp_closed [of "G" "a"], assumption+)
 apply simp
apply auto
done

lemma subg_condition:"\<lbrakk>group G; H \<subseteq> carrier G; H \<noteq> {};
   \<forall>a. \<forall>b. a \<in> H \<and> b\<in> H \<longrightarrow>  a \<cdot>\<^sub>G b\<inverse>\<^sup>G\<in> H\<rbrakk> \<Longrightarrow> H \<guillemotleft> G"
apply (simp add:subgroup_def)
apply (simp add:subg_condTr1)
apply (rule conjI)
apply (rule ballI)+

apply (frule_tac  a = y in subg_condTr2 [of "G" "H"], assumption+)
apply (subgoal_tac "x \<cdot>\<^sub>G (y\<inverse>\<^sup>G)\<inverse>\<^sup>G \<in> H")
apply (frule_tac c = y in subsetD [of "H" "carrier G"], assumption+)
apply (simp add:iOp_invinv)
apply blast
apply (rule ballI)
apply (simp add:subg_condTr2)
done


constdefs
  grp :: "[('a, 'more) GroupType_scheme, 'a set ] \<Rightarrow> 'a GroupType"
  "grp G H == \<lparr> carrier = H, tOp = tOp G, iOp = iOp G, one = 1\<^sub>G \<rparr>"
  (* grp G H is a group ismorpic to the subgroup H *)

constdefs
   img_hom :: "[('a, 'm) GroupType_scheme, ('b, 'm1) GroupType_scheme, 
     'a  \<Rightarrow> 'b] \<Rightarrow> 'b GroupType"
   "img_hom F G f == grp G (f`(carrier F))"
  
syntax
   "@IMGHOM" :: "[('a, 'm) GroupType_scheme, ('b, 'm1) GroupType_scheme, 
        'a \<Rightarrow> 'b ] \<Rightarrow> 'b GroupType"    ("(3img\<^sub>_\<^sub>,\<^sub>_/ _)" [88,88,89]88)
translations
     "img\<^sub>F\<^sub>,\<^sub>G f" == "img_hom F G f"

lemma subggrp: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> group (grp G H)" 
apply (unfold  group_def [of "grp G H"])
 apply (simp add:grp_def)
 apply (simp add:subg_tOp_closed bivar_func_test) 
 apply (simp add:subg_iOp_closed univar_func_test)  
apply (unfold subgroup_def) apply simp
apply (fold subgroup_def)
apply (rule ballI)+
apply (simp add:subg_subset1 [of "G" "H" _])
apply (frule_tac h = x in  subg_subset1 [of "G" "H" _], assumption+)
apply (frule_tac h = y in  subg_subset1 [of "G" "H" _], assumption+)
apply (frule_tac h = z in  subg_subset1 [of "G" "H" _], assumption+)
apply (simp add:tOp_assoc)
apply (simp add:iOp_l_inv)
done

lemma grp_carrier:"\<lbrakk>group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> carrier (grp G H) = H" 
apply (simp add:grp_def)
done

lemma subg_in_subg:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G; H \<subseteq> K \<rbrakk> \<Longrightarrow> H \<guillemotleft> grp G K"
apply (simp add:subgroup_def [of "grp G K" "H"])
apply (rule conjI) apply (simp add:grp_def)
 apply (simp add:grp_def)
 apply (simp add:subg_tOp_closed)
 apply (simp add:subg_iOp_closed)
 apply (simp add:subgroup_def)
done


lemma subg_subset_in_subg: "\<lbrakk> group G; K \<guillemotleft> G; H \<guillemotleft> grp G K \<rbrakk> \<Longrightarrow> H \<subseteq> K"
apply (frule subggrp [of "G" "K"], assumption)
apply (frule subg_subset [of "grp G K" "H"], assumption+)
apply (simp add:grp_def)
done

lemma consthom_ghom:"\<lbrakk> group F; group G \<rbrakk> \<Longrightarrow> consthom F G \<in> gHom F G"
apply (unfold gHom_def)
apply (simp add:CollectI) apply (simp add:consthom_def)
apply (simp add:Pi_def ex_one)
done

lemma unitGroups_isom:"\<lbrakk> Ugp E1; Ugp E2 \<rbrakk> \<Longrightarrow> E1 \<cong> E2"
apply (unfold isomorphism_def)
apply (subgoal_tac "gbijec\<^sub>E1\<^sub>,\<^sub>E2 (consthom E1 E2)")
  apply blast
apply (simp add:Ugp_def) apply (erule conjE)+
apply (frule consthom_ghom [of "E1" "E2"], assumption+)
apply (simp add:gbijec_def)
apply (rule conjI)
 apply (simp add:gsurjec_def surj_to_def consthom_def)
 apply (simp add:ginjec_def inj_on_def consthom_def)
done

lemma subg_tOp_inherited:"\<lbrakk>group G; L \<guillemotleft> G; a \<in> L; b \<in> L\<rbrakk>  \<Longrightarrow>  
  tOp (grp G L) a b = tOp G a b"
apply (simp add:grp_def)
done

lemma subg_of_subg:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> grp G H \<rbrakk> \<Longrightarrow> K \<guillemotleft> G"
apply (simp add:subgroup_def [of "G" "K"])
 apply (rule conjI)
 apply (frule subg_subset [of "G" "H"], assumption+)
 apply (frule subggrp [of "G" "H"], assumption+)
 apply (frule subg_subset [of "grp G H" "K"], assumption)
 apply (simp add:grp_def subset_trans[of "K" "H" "carrier G"])
apply (rule conjI)
 apply (rule ballI)+
 apply (subgoal_tac "x \<cdot>\<^sub>(grp G H) y \<in> K")
 apply (simp add:grp_def)
 apply (rule subg_tOp_closed) 
  apply (simp add:subggrp) apply assumption+
 apply (frule subggrp [of "G" "H"], assumption+)
apply (rule conjI)
 apply (rule ballI)
 apply (frule_tac x = x in subg_iOp_closed [of "grp G H" "K"], assumption+)
 apply (simp add:grp_def)
 apply (frule_tac subg_one_closed [of "grp G H"], assumption+)
 apply (simp add:grp_def)
done

lemma grp_inherited: "\<lbrakk> group G; K \<guillemotleft> G; L \<guillemotleft> G; K \<subseteq> L \<rbrakk> \<Longrightarrow>
         grp (grp G L) K = grp G K" 
apply (simp add:grp_def)
done

section "3. Properties of cosets"

(* left cosets *)

lemma l_cosTr0: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> l_coset G a H \<rbrakk>
  \<Longrightarrow> x \<in> carrier G"
apply (simp add: l_coset_def subgroup_def)
apply auto
done

lemma a_in_l_cos:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
          a \<in> l_coset G a H"
apply (simp add: l_coset_def)
apply (rule bexI [of _ "1\<^sub>G"])
apply (subst r_one, assumption+, simp)
apply (simp add:subg_one_closed)
done

lemma l_cosTr1 :"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
         x \<in> l_coset G a H; l_coset G a H = l_coset G b H \<rbrakk> \<Longrightarrow>
           x \<in> l_coset G b H "
apply simp
done

lemma l_cosEqTr:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
 l_coset G a H = l_coset G b H \<rbrakk> \<Longrightarrow> a \<in> l_coset G b H "
apply (rule l_cosTr1, assumption+)
 apply (thin_tac "a H\<^sub>G = b H\<^sub>G")
apply (simp add:a_in_l_cos)
apply assumption
done   


lemma l_cosTr2: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G; 
  a \<in> l_coset G b H \<rbrakk>  \<Longrightarrow> b\<inverse>\<^sup>G \<cdot>\<^sub>G a \<in> H "
apply (simp only: l_coset_def)
apply (simp add: bexI)
apply auto 
apply (subst tOp_assoc [THEN sym], assumption+)
apply simp
apply assumption+                  
apply (rule subg_subset1, assumption+)
apply (simp add:iOp_l_inv subg_l_one)
done


lemma l_cos_belong: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> carrier G;
  a\<inverse>\<^sup>G \<cdot>\<^sub>G x \<in> H \<rbrakk> \<Longrightarrow> x \<in> l_coset G a H";
apply (simp only: l_coset_def)
apply (simp)
apply (rule bexI)
apply (simp_all)
apply (subst tOp_assoc [THEN sym], assumption+)
 apply simp+
apply (simp add:iOp_r_inv)
done

lemma l_cosTr3: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
      l_coset G a H \<subseteq> carrier G"
apply (simp add: l_coset_def subgroup_def)
apply auto
done

lemma l_cosTr4: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
 x \<in> carrier G\<rbrakk> \<Longrightarrow> (a\<inverse>\<^sup>G \<cdot>\<^sub>G b)\<inverse>\<^sup>G \<cdot>\<^sub>G (a\<inverse>\<^sup>G \<cdot>\<^sub>G x)  = b\<inverse>\<^sup>G \<cdot>\<^sub>G x"
apply (subst invofab [of "G" "iOp G a" "b"], assumption+)
apply simp+
apply (subst tOp_assocTr43, assumption+)
apply simp+
apply (subst tOp_assocTr42, assumption+)
apply simp+
apply (subst iOp_l_inv [of "G" "iOp G a"], assumption+)
apply simp
apply (simp add:r_one)
done

lemma  l_cosTr5: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
  tOp G (iOp G a) b \<in> H ; x \<in> l_coset G a H \<rbrakk> \<Longrightarrow> 
   (b\<inverse>\<^sup>G \<cdot>\<^sub>G x) \<in> H"
apply (frule l_cosTr0, assumption+)
apply (frule l_cosTr2 [of "G" "H" "x" "a" ], assumption+)
apply (frule subg_iOp_closed [of "G" "H" " a\<inverse>\<^sup>G \<cdot>\<^sub>G b"], assumption+)
apply (frule invofab [of "G" "a\<inverse>\<^sup>G" "b"]) apply simp+
apply (frule subg_tOp_closed [of "G" "H" "b\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G\<inverse>\<^sup>G" "a\<inverse>\<^sup>G \<cdot>\<^sub>G x"], 
               assumption+)
 apply (thin_tac "a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> H")  apply (thin_tac "a\<inverse>\<^sup>G \<cdot>\<^sub>G x \<in> H")
 apply (thin_tac "b\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G\<inverse>\<^sup>G \<in> H")
 apply (thin_tac "( a\<inverse>\<^sup>G \<cdot>\<^sub>G b)\<inverse>\<^sup>G =  b\<inverse>\<^sup>G \<cdot>\<^sub>G a\<inverse>\<^sup>G\<inverse>\<^sup>G")
apply (frule iOp_closed [of "G" "a"], assumption+)
apply (frule iOp_closed [of "G" "a\<inverse>\<^sup>G"], assumption+)
apply (simp add:tOp_assocTr43)
apply (frule iOp_closed [of "G" "a"], assumption+)
apply (frule iOp_closed [of "G" "a\<inverse>\<^sup>G"], assumption+)
apply (simp add:tOp_assocTr42)
apply (simp add:iOp_l_inv)
apply (simp add:r_one)
done

lemma l_cosTr6: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> H ; x \<in> l_coset G a H \<rbrakk> \<Longrightarrow> 
   x \<in> l_coset G b H"
apply (frule l_cosTr5 [of "G" "H" "a" "b" "x"], assumption+)
apply (frule l_cos_belong [of "G" "H" "b" "x"], assumption+)
apply auto
apply (frule l_cosTr0 [of "G" "H" "a" "x"], assumption+)
done

lemma l_cosUnit1: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow>
        l_coset G (1\<^sub>G) H = H"
apply auto
apply (simp add:l_coset_def)
apply auto
apply (simp add:subg_l_one)
apply (simp add:l_coset_def)
apply (simp add:subg_l_one)
done

lemma l_cosUnit1_1:"\<lbrakk>group G; H \<guillemotleft> G; h \<in> H\<rbrakk> \<Longrightarrow> l_coset G h H = H"
apply auto
apply (simp add:l_coset_def) apply auto
apply (simp add:subg_tOp_closed)
apply (rule l_cos_belong, assumption+)
 apply (simp add:subg_subset1)+
 apply (rule subg_tOp_closed, assumption+)
 apply (simp add:subg_iOp_closed)
 apply simp
done

lemma l_cosTr7: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> H \<rbrakk> \<Longrightarrow> l_coset G a H \<subseteq>  l_coset G b H"
apply (rule subsetI)
apply (simp add:l_cosTr6 [of "G" "H" "a" "b" _])
done

lemma l_cosTr8: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; h \<in> H \<rbrakk> \<Longrightarrow>
    tOp G a h \<in> l_coset G a H"
apply (simp add:l_coset_def)
apply blast
done

lemma l_cosTool1: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> H \<rbrakk> \<Longrightarrow> b\<inverse>\<^sup>G \<cdot>\<^sub>G  a \<in> H "
apply (frule subg_iOp_closed [of "G" "H" "a\<inverse>\<^sup>G \<cdot>\<^sub>G b"], assumption+)
 apply (simp add:invofab iOp_invinv)
done

theorem l_cosEq: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   a\<inverse>\<^sup>G \<cdot>\<^sub>G  b \<in> H \<rbrakk> \<Longrightarrow> l_coset G a H = l_coset G b H";
apply (rule equalityI)
apply (rule l_cosTr7 [of "G" "H" "a" "b"], assumption+)
apply (frule l_cosTool1 [of "G" "H" "a" "b"], assumption+)
apply (rule l_cosTr7 [of "G" "H" "b" "a"], assumption+)
done

lemma l_cosEqVar1: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
 l_coset G a H = l_coset G b H \<rbrakk> \<Longrightarrow>  tOp G (iOp G a) b \<in> H" 
apply (frule l_cosEqTr [of "G" "H" "b" "a"], assumption+)
apply (rule sym, simp)
apply (rule l_cosTr2 [of "G" "H" "b" "a"], assumption+)
done

lemma r_cosTr0: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> r_coset G H a \<rbrakk>
  \<Longrightarrow> x \<in> carrier G"
apply (simp add: r_coset_def subgroup_def)
apply auto
done

lemma r_cosTr0_1:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                         r_coset G H a \<in> set_r_cos G H"
apply (simp add:set_r_cos_def)
apply auto
done

lemma r_cosTr0_2:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G \<rbrakk>
    \<Longrightarrow> r_coset G H (tOp G a b) \<in> set_r_cos G H"
apply (simp add:r_cosTr0_1 [of "G" "H" "tOp G a b"])
done

lemma aInR_cos:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
          a \<in> r_coset G H a"
apply (simp add: r_coset_def)
apply (rule bexI [of _ "1\<^sub>G"])
apply (simp)
apply (simp add:subgroup_def)
done

lemma r_cosTr1 :"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
         x \<in> r_coset G H a; r_coset G H a = r_coset G H b \<rbrakk> \<Longrightarrow>
           x \<in> r_coset G H b "
apply simp
done

lemma r_cosEqTr:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
 r_coset G H a = r_coset G H b \<rbrakk> \<Longrightarrow> a \<in> r_coset G H b "
apply (rule r_cosTr1, assumption+)
apply (rule aInR_cos, assumption+)
done 

lemma r_cosTr2: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G; 
  a \<in> r_coset G H b \<rbrakk>  \<Longrightarrow> tOp G a (iOp G b) \<in> H "
apply (simp only: r_coset_def) apply (simp add:CollectI)
apply auto
apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
apply (subst tOp_assoc, assumption+) apply simp
apply (simp add:iOp_r_inv r_one)
done

lemma r_cosTr2_1: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G;
    b \<in> r_coset G H a \<rbrakk> \<Longrightarrow> tOp G b (iOp G a) \<in> H"
apply (frule r_cosTr0 [of "G" "H" "a" "b"], assumption+)
apply (rule r_cosTr2 [of "G" "H" "b" "a"], assumption+)
done

lemma r_cosTr2_2: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G;
     b \<in> r_coset G H (iOp G a)\<rbrakk> \<Longrightarrow> tOp G b a \<in> H"

apply (insert  r_cosTr2_1 [of "G" "H" "iOp G a" _])
apply (simp add:iOp_invinv)
done

lemma r_cos_belong: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> carrier G;
  tOp G x (iOp G a)  \<in> H \<rbrakk> \<Longrightarrow> x \<in> r_coset G H a";
apply (subgoal_tac "\<exists>h\<in>H. x = h \<cdot>\<^sub>G a")
apply (simp add:r_coset_def) apply blast
apply (frule  tOp_in_subg [of "G" "H" "iOp G a" "x"], assumption+)
 apply simp+
apply (simp add:iOp_invinv) apply blast
done

lemma r_cosTr3: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
      r_coset G H a \<subseteq> carrier G"
apply (simp add: r_coset_def subgroup_def)
apply auto
done

lemma r_cosTr4: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
 x \<in> carrier G\<rbrakk> \<Longrightarrow>
 tOp G (tOp G x (iOp G a)) (iOp G (tOp G b (iOp G a))) 
 = tOp G x (iOp G b) "
apply (subst invofab [of "G" "b" "iOp G a"])
apply assumption+
apply simp+
apply (subst tOp_assocTr43, assumption+)
 apply simp+
 apply (frule iOp_closed [of "G" "a"], assumption+)
 apply (subst tOp_assocTr42, assumption+) apply simp+
apply (simp add:iOp_r_inv r_one)
done  

lemma  r_cosTr5: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
  tOp G b (iOp G a) \<in> H ; x \<in> r_coset G H a \<rbrakk> \<Longrightarrow> 
   (tOp G x (iOp G b)) \<in> H"
apply (simp add:r_coset_def) 
apply auto
apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
apply (subst tOp_assoc, assumption+)
apply simp
apply (frule subg_iOp_closed [of "G" "H" "b \<cdot>\<^sub>G a\<inverse>\<^sup>G"], assumption+)
apply (simp add:invofab iOp_invinv)
apply (simp add:subg_tOp_closed)
done

lemma r_cosTr6: "\<lbrakk>group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   tOp G b (iOp G a) \<in> H ; x \<in> r_coset G H a\<rbrakk> \<Longrightarrow> 
   x \<in> r_coset G H b"
apply (frule  r_cosTr5 [of "G" "H" "a" "b" "x"], assumption+)
apply (rule r_cos_belong [of "G" "H" "b" "x"], assumption+) 
apply (rule r_cosTr0, assumption+)
done

lemma r_cosUnit1: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> r_coset G H (1\<^sub>G) = H"
apply auto
apply (simp only:r_coset_def) apply (simp add:CollectI)
apply auto
 apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
 apply (simp add:r_one)

apply (simp add:r_coset_def)
apply (subgoal_tac "x \<cdot>\<^sub>G (1\<^sub>G) = x")
apply blast
apply (frule subg_subset1, assumption+)
apply (simp add:r_one)
done

lemma r_cosUnit1_1: "\<lbrakk> group G; H \<guillemotleft> G; x \<in> H \<rbrakk> \<Longrightarrow> r_coset G H x = H"
apply auto
 apply (simp add:r_coset_def) apply auto
 apply (simp add:subg_tOp_closed)
apply (simp add:r_coset_def)
apply (subgoal_tac "(xa \<cdot>\<^sub>G x\<inverse>\<^sup>G) \<cdot>\<^sub>G x = xa")
apply (subgoal_tac "xa \<cdot>\<^sub>G x\<inverse>\<^sup>G \<in> H")
apply blast
apply (rule subg_tOp_closed, assumption+) 
apply (simp add:subg_iOp_closed)
apply (frule_tac h = x in subg_subset1 [of "G" "H"], assumption+)
apply (frule_tac h = xa in subg_subset1 [of "G" "H"], assumption+)
 apply (subst tOp_assoc, assumption+) apply simp+
 apply (subst iOp_l_inv, assumption+)
 apply (simp add:r_one)
done

lemma r_cosTr7: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   tOp G b (iOp G a) \<in> H \<rbrakk> \<Longrightarrow> r_coset G H a  \<subseteq>  r_coset G H b "
apply (rule subsetI)
apply (simp add:r_cosTr6[of "G" "H" "a" "b"])
done 

lemma r_cosTool1: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
   tOp G b (iOp G a) \<in> H \<rbrakk> \<Longrightarrow> tOp G a (iOp G b)  \<in> H "
apply (frule subg_iOp_closed [of "G" "H" "b \<cdot>\<^sub>G a\<inverse>\<^sup>G"], assumption+)
 apply (simp add:invofab iOp_invinv)
done

lemma r_cosTool2: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; 
   x \<in> r_coset G H a \<rbrakk> \<Longrightarrow> \<exists> h \<in> H. (tOp G h a = x)"
apply (simp add:r_coset_def)
done

theorem r_cosEq: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
  tOp G b (iOp G a) \<in> H \<rbrakk> \<Longrightarrow> r_coset G H a  = r_coset G H b ";
apply auto
apply (frule r_cosTr7 [of "G" "H" "a" "b"], assumption+)
 apply (simp add:subsetD)
apply (frule subg_iOp_closed [of "G" "H" "b \<cdot>\<^sub>G a\<inverse>\<^sup>G"], assumption+)
 apply (thin_tac "b \<cdot>\<^sub>G a\<inverse>\<^sup>G \<in> H")
apply (simp add:invofab iOp_invinv)
apply (frule r_cosTr7 [of "G" "H" "b" "a"], assumption+)
apply (simp add:subsetD)
done

lemma r_cosEqVar1:"\<lbrakk>group G; H \<guillemotleft> G; a \<in> carrier G; b \<in> carrier G;
 r_coset G H a = r_coset G H b\<rbrakk> \<Longrightarrow>  tOp G b (iOp G a) \<in> H" 
apply (frule r_cosEqTr [of "G" "H" "b" "a"], assumption+)
apply (rule sym, assumption+)
apply (frule r_cosTr2 [of "G" "H" "b" "a"], assumption+)
done  

lemma r_cosEqVar2:"\<lbrakk>group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> r_coset G H a\<rbrakk>
          \<Longrightarrow>  r_coset G H a = r_coset G H x"
apply (frule r_cosTr2 [of "G" "H" "x" "a"], assumption+)
apply (rule r_cosTr0, assumption+)
apply (rule r_cosEq [of "G" "H" "a" "x"], assumption+)
apply (rule r_cosTr0, assumption+)
done

lemma r_cosEqVar3: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G;
 b \<in> carrier G; (r_coset G H a) \<inter> (r_coset G H b) \<noteq> {} \<rbrakk> \<Longrightarrow> 
         r_coset G H a = r_coset G H b "
apply (frule nonempty_int [of "r_coset G H a" "r_coset G H b"])
apply (erule exE)
apply simp
apply (erule conjE)
apply (frule  r_cosEqVar2 [of "G" "H" "a" _], assumption+)
 apply simp+
apply (frule r_cosEqVar2 [of "G" "H" "b" _], assumption+)
apply simp
done

lemma r_cosTr8: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; h \<in> H;
     x \<in> r_coset G H a \<rbrakk> \<Longrightarrow> tOp G h x \<in> r_coset G H a"

apply (frule r_cosEqVar2 [of "G" "H" "a" "x"], assumption+)
apply simp
apply (simp add:r_coset_def)
apply auto
done

lemma r_cosTr9: "\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; h \<in> H;
   iOp G x \<in> r_coset G H a \<rbrakk> \<Longrightarrow> tOp G h (iOp G x) \<in> r_coset G H a"

apply (insert r_cosTr8 [of "G" "H" "a" "h" "iOp G x"])
apply simp
done

lemma r_cosTr10:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; x \<in> r_coset G H a;
y \<in> r_coset G H a \<rbrakk> \<Longrightarrow> tOp G x (iOp G y) \<in> H" 
apply (simp add:r_coset_def)
apply auto
apply (subst invofab, assumption+)
apply (simp add:subg_subset1) apply assumption
 apply (frule iOp_closed [of "G" "a"], assumption+)
 apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
 apply (frule_tac h = ha in subg_subset1 [of "G" "H"], assumption+)
 apply (frule_tac a = ha in iOp_closed [of "G"], assumption+)
apply (subst tOp_assocTr43, assumption+)
apply (subst tOp_assocTr42, assumption+)
apply (simp add:iOp_r_inv) apply (simp add:r_one)
apply (simp add:subg_iOp_closed subg_tOp_closed)
done


lemma PrSubg4_2:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G;
   x \<in> r_coset G H (iOp G a) \<rbrakk> \<Longrightarrow> 
       x \<in> {z. \<exists> v \<in> r_coset G H a. \<exists> h \<in> H. (tOp G h (iOp G v) = z)}"

apply (simp add:CollectI)
apply (frule r_cosTool2 [of "G" "H" "a\<inverse>\<^sup>G" "x"], assumption+)
 apply simp apply assumption
 apply (frule aInR_cos [of "G" "H" "a"], assumption+)
 apply auto
done

lemma r_coset_fixed:"\<lbrakk> group G; H \<guillemotleft> G; a \<in> carrier G; r_coset G H a = H \<rbrakk>
   \<Longrightarrow> a \<in> H"
apply (frule aInR_cos [of "G" "H" "a"], assumption+)
apply simp
done

lemma r_coset_fixed1:"\<lbrakk>group G; H \<guillemotleft> G; a \<in> carrier G; h \<in> H \<rbrakk> \<Longrightarrow>
                                 r_coset G H a = r_coset G H (h \<cdot>\<^sub>G a)"
apply (frule r_cosEq [of "G" "H" "a" "h \<cdot>\<^sub>G a"], assumption+)
apply (frule subg_subset1, assumption+)
apply simp apply (frule subg_subset1, assumption+)
apply (frule iOp_closed [of "G" "a"], assumption+)
apply (subst tOp_assoc, assumption+)
apply (simp add:iOp_r_inv r_one)
apply simp
done

lemma subg_r_cos:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> G; H \<subseteq> K; x \<in> K\<rbrakk> \<Longrightarrow>
          r_coset (grp G K) H x = r_coset G H x"
apply (simp add:r_coset_def)
apply (simp add:grp_def)
done

lemma subg_l_cos:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> G; H \<subseteq> K; x \<in> K\<rbrakk> \<Longrightarrow>
          l_coset (grp G K) x H  = l_coset G x H "
apply (simp add:l_coset_def)
apply (simp add:grp_def)
done

section "4. Normal subgroups and Quotient groups"

lemma nmlSubgTr0: "\<lbrakk> group G; H \<lhd> G \<rbrakk> \<Longrightarrow> H \<guillemotleft> G"
apply (simp add:nsubgroup_def)
done

lemma nmlSubgTr1: "\<lbrakk> group G; H \<guillemotleft> G; b \<in> carrier G; h \<in> H;
  \<forall> a \<in> carrier G. \<forall> h \<in> H. ((a \<cdot>\<^sub>G h) \<cdot>\<^sub>G a\<inverse>\<^sup>G) \<in> H\<rbrakk> \<Longrightarrow>  
                                 b \<cdot>\<^sub>G h \<cdot>\<^sub>G b\<inverse>\<^sup>G  \<in> H"
apply auto
done

lemma nmlSubgTr2: "\<lbrakk> group G; H \<guillemotleft> G; b \<in> carrier G; h \<in> H;  
 \<forall>a\<in>carrier G. \<forall> h \<in> H. (a \<cdot>\<^sub>G h) \<cdot>\<^sub>G a\<inverse>\<^sup>G  \<in> H\<rbrakk> \<Longrightarrow>  b\<inverse>\<^sup>G \<cdot>\<^sub>G h \<cdot>\<^sub>G b \<in> H"
apply (insert nmlSubgTr1 [of "G" "H" "b\<inverse>\<^sup>G"])
apply (simp add:iOp_invinv)
done

lemma nmlSubgTr3:"\<lbrakk> group G; H \<lhd>  G; h \<in> H \<rbrakk> \<Longrightarrow> h \<in> carrier G"
apply (insert nmlSubgTr0 [of "G" "H"])
apply simp
apply (simp add:subg_subset1)
done

lemma nml_subg_subset:"\<lbrakk> group G; N \<lhd>  G \<rbrakk> \<Longrightarrow> N \<subseteq>  carrier G"
apply (frule nmlSubgTr0, assumption+)
 apply (simp add:subg_subset)
done

lemma NSubgLREq:"\<lbrakk> group G; H \<lhd> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
        l_coset G a H = r_coset G H a"
apply (simp add: nsubgroup_def)
done

lemma nmlSubg1: "\<lbrakk>group G; H \<guillemotleft> G; \<forall>a\<in> carrier G. \<forall>h\<in>H. (a \<cdot>\<^sub>G h) \<cdot>\<^sub>G a\<inverse>\<^sup>G  \<in> H;
b \<in> carrier G \<rbrakk> \<Longrightarrow> r_coset G H b =  l_coset G b H"
apply auto 
 (* x \<in> r_coset G H b \<Longrightarrow> x \<in> l_coset G b H  *)
  apply (frule_tac x = x in r_cosTr0 [of "G" "H" "b" _], assumption+) 

  (* from x \<in> r_coset G H b we get x \<cdot>\<^sub>G b\<inverse>\<^sup>G \<in> H *)

  apply (frule_tac a = x in r_cosTr2 [of "G" "H" _ "b"], assumption+)
  apply (frule_tac h = "x \<cdot>\<^sub>G b\<inverse>\<^sup>G" in nmlSubgTr2 [of "G" "H" "b"], assumption+)
   apply (simp add: tOp_assoc [of "G" " b\<inverse>\<^sup>G" _  "b"])
   apply (simp add: tOp_assoc [of "G" _ "b\<inverse>\<^sup>G" "b"])
   apply (simp add: iOp_l_inv)
   apply (simp add:r_one)
  apply (simp add:l_cos_belong)

(* We prove l_coset G b H \<subseteq> r_coset G H b *)
  apply (frule_tac x = x in l_cosTr0 [of "G" "H" "b"], assumption+)
  apply (simp add:l_coset_def) 
  apply auto
  apply (rule_tac x = "b \<cdot>\<^sub>G h" in r_cos_belong [of "G" "H" "b" _], assumption+)
  apply simp
done

lemma nmlSubg2: "\<lbrakk> group G; H \<guillemotleft> G; \<forall> a \<in> carrier G. 
\<forall> h \<in> H. (a \<cdot>\<^sub>G h) \<cdot>\<^sub>G a\<inverse>\<^sup>G  \<in> H \<rbrakk> \<Longrightarrow> H \<lhd> G" 

apply (simp add:nsubgroup_def)
apply (simp add:nmlSubg1 [of "G" "H"])
done

lemma special_nsubg_e:"\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> {1\<^sub>G} \<lhd> grp G H"
apply (simp add:nsubgroup_def)
apply (simp add:subggrp)
apply (rule conjI)
apply (rule subg_in_subg [of "G" "{1\<^sub>G}" "H"], assumption+)
 apply (simp add:special_subg_e) apply assumption+
 apply (simp add:subg_one_closed)

apply (rule ballI)
apply (simp add:l_coset_def r_coset_def)
apply (simp add:grp_def)
apply (frule subg_subset1, assumption+)
apply (simp add:r_one)
done

lemma special_nsubg_G:"\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> H \<lhd> grp G H" 
apply (frule subggrp, assumption+)
apply (simp add:nsubgroup_def)
apply (rule conjI)
apply (rule  subg_in_subg [of "G" "H" "H"], assumption+)
 apply simp
apply (rule ballI)
apply (subst subg_r_cos, assumption+)  apply simp
 apply (simp add:grp_def)
apply (subst subg_l_cos, assumption+) apply simp
 apply (simp add:grp_def)
 apply (subst r_cosUnit1_1, assumption+)
 apply (simp add:grp_def)
 apply (subst l_cosUnit1_1, assumption+)
 apply (simp add:grp_def) apply simp
done


lemma NSubgTr0: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G; b \<in> carrier G;
 b \<in> r_coset G H a \<rbrakk> \<Longrightarrow>  ((a \<cdot>\<^sub>G b\<inverse>\<^sup>G) \<in> H) \<and> (a\<inverse>\<^sup>G \<cdot>\<^sub>G b \<in> H)"
apply (frule nmlSubgTr0, assumption+)
apply (frule r_cosTr2 [of "G" "H" "b" "a"], assumption+)
apply (frule subg_iOp_closed [of "G" "H" "b \<cdot>\<^sub>G a\<inverse>\<^sup>G"], assumption+)
apply (simp add: invofab iOp_invinv)
apply (simp add: NSubgLREq [of "G" "H" "a", THEN sym])
apply (frule l_cosTr2 [of "G" "H" "b" "a"], assumption+)
done


lemma NSubgTr1: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G; b \<in> carrier G;
 b \<cdot>\<^sub>G a\<inverse>\<^sup>G \<in> H \<rbrakk> \<Longrightarrow> b\<inverse>\<^sup>G \<cdot>\<^sub>G a \<in> H"
apply (frule nmlSubgTr0, assumption+)
apply (frule r_cos_belong [of "G" "H" "a" "b"], assumption+)
apply (simp add: NSubgLREq [of "G" "H" "a", THEN sym])
apply (frule l_cosTr2 [of "G" "H" "b" "a"], assumption+)
apply (frule subg_iOp_closed[of "G" "H" "a\<inverse>\<^sup>G \<cdot>\<^sub>G b"], assumption+)
apply (simp add:invofab iOp_invinv)
done      

lemma NSubgTr2:"\<lbrakk> group G; a \<in> carrier G; b \<in> carrier G; 
                            a1 \<in> carrier G; b1 \<in> carrier G \<rbrakk>
 \<Longrightarrow> tOp G (tOp G a b) (iOp G (tOp G a1 b1)) = 
 tOp G a (tOp G (tOp G  (tOp G b (iOp G b1)) (tOp G (iOp G a1) a)) (iOp G a))"
apply (simp add: invofab)
apply (subst tOp_assoc, assumption+)
 apply (rule tOp_closed, assumption+)
 apply simp
 apply (rule tOp_closed, assumption+)
 apply simp+
apply (subgoal_tac "a1\<inverse>\<^sup>G \<cdot>\<^sub>G a \<cdot>\<^sub>G a\<inverse>\<^sup>G = a1\<inverse>\<^sup>G") apply simp
apply (subst tOp_assoc, assumption+)
 apply simp+
apply (subgoal_tac "a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G ( b1\<inverse>\<^sup>G \<cdot>\<^sub>G a1\<inverse>\<^sup>G)) = a \<cdot>\<^sub>G  b \<cdot>\<^sub>G ( b1\<inverse>\<^sup>G \<cdot>\<^sub>G a1\<inverse>\<^sup>G)")
apply simp
apply (simp add:tOp_assoc[THEN sym])
apply (simp add:tOp_assoc)
apply (simp add:iOp_r_inv)
apply (simp add:r_one)
done

lemma NSubgPr1: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G ; h \<in> H \<rbrakk> \<Longrightarrow>
          tOp G a (tOp G h (iOp G a)) \<in> H"
apply (frule nmlSubgTr0, assumption+)
apply (frule l_cosTr8 [of "G" "H" "a" "h"], assumption+)
apply (simp add:NSubgLREq [of "G" "H" "a"])
apply (subst tOp_assoc [THEN sym], assumption+)
 apply (simp add:subg_subset1) apply simp
 apply (rule r_cosTr2 [of "G" "H" "a \<cdot>\<^sub>G h" "a"], assumption+)
 apply (rule tOp_closed, assumption+) 
 apply (simp add:subg_subset1) apply assumption+
done
    
lemma NSubgPr1_1: "\<lbrakk>group G; H \<lhd> G; a \<in> carrier G ; h \<in> H\<rbrakk> \<Longrightarrow> 
          (a \<cdot>\<^sub>G h) \<cdot>\<^sub>G a\<inverse>\<^sup>G \<in> H"
apply (frule NSubgPr1 [of "G" "H" "a" "h"], assumption+)
apply (subst tOp_assoc, assumption+)
 apply (frule nmlSubgTr0, assumption+)
 apply (simp add:subg_subset1)
 apply simp
 apply assumption
done

lemma NSubgPr2:"\<lbrakk> group G; H \<lhd> G; a \<in> carrier G ; h \<in> H \<rbrakk> \<Longrightarrow>
                 a\<inverse>\<^sup>G \<cdot>\<^sub>G (h \<cdot>\<^sub>G a) \<in> H"
apply (frule iOp_closed [of "G" "a"], assumption+)
apply (frule NSubgPr1 [of "G" "H" "a\<inverse>\<^sup>G" "h"], assumption+)
apply (simp add:iOp_invinv)
done

lemma NSubgPr2_1:"\<lbrakk> group G; H \<lhd> G; a \<in> carrier G ; h \<in> H \<rbrakk> \<Longrightarrow>
                 a\<inverse>\<^sup>G \<cdot>\<^sub>G  h \<cdot>\<^sub>G a \<in> H"
apply (frule NSubgPr2, assumption+)
apply (frule iOp_closed [of "G" "a"], assumption+)
apply (subst tOp_assoc, assumption+)
apply (frule nmlSubgTr0, assumption+)
apply (rule subg_subset1, assumption+)
done

lemma NSubgTr3: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G; b \<in> carrier G; 
a1 \<in> carrier G; b1 \<in> carrier G; tOp G a (iOp G a1) \<in> H; 
 tOp G b (iOp G b1) \<in> H \<rbrakk> 
       \<Longrightarrow> tOp G (tOp G a b) (iOp G (tOp G a1 b1)) \<in> H"

apply (frule  NSubgTr2 [of "G" "a" "b" "a1" "b1"], assumption+)
apply (frule NSubgTr1 [of "G" "H" "a1" "a"], assumption+)

apply (frule subg_iOp_closed [of "G" "H" "tOp G (iOp G a) a1"])
 apply (simp add:nmlSubgTr0)
 apply assumption+
apply (simp add: invofab iOp_invinv)
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule subg_tOp_closed [of "G" "H" "tOp G b (iOp G b1)" 
                                        "tOp G (iOp G a1) a"], assumption+)
apply (frule  NSubgPr1 [of "G" "H" "a" "tOp G (tOp G b (iOp G b1)) (tOp G (iOp G a1) a)"], assumption+)
done

lemma nsubg_in_subg:"\<lbrakk>group G; H \<lhd> G; N \<guillemotleft> G; H \<subseteq> N\<rbrakk> \<Longrightarrow> H \<lhd> grp G N"
apply (frule subggrp [of "G" "N"], assumption+)
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule subg_in_subg [of "G" "H" "N"], assumption+)
apply (rule nmlSubg2, assumption+)
apply (rule ballI)+
apply (simp add:grp_def) apply (fold grp_def)
apply (frule_tac h = a in subg_subset1 [of "G" "N"], assumption+)
apply (simp add: NSubgPr1_1 [of "G" "H"]) 
done

lemma NSubgTr4: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G; 
 x \<in> r_coset G H a \<rbrakk> \<Longrightarrow> iOp G x \<in> r_coset G H (iOp G a)"

apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule r_cosTr2 [of "G" "H" "x" "a"], assumption+)
apply (rule r_cosTr0, assumption+)
apply (frule NSubgTr1 [of "G" "H" "a" "x"], assumption+)
apply (rule r_cosTr0, assumption+)
 apply (thin_tac "x \<cdot>\<^sub>G a\<inverse>\<^sup>G \<in> H")
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule r_cos_belong [of "G" "H" "iOp G a" "iOp G x"], assumption+)
 apply simp+
 apply (frule r_cosTr0, assumption+) apply simp
 apply (simp add:iOp_invinv)
apply assumption
done

lemma ctOpTr1:"\<lbrakk> group G; H \<lhd> G; a \<in> carrier G; b \<in> carrier G; 
a1 \<in> carrier G; b1 \<in> carrier G; r_coset G H a = r_coset G H a1;
r_coset G H b = r_coset G H b1 \<rbrakk> \<Longrightarrow> 
 r_coset G H (tOp G a b) = r_coset G H (tOp G a1 b1)"
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule r_cosEqVar1 [of "G" "H" "a1" "a"], assumption+)
 apply (rule sym, assumption+)
apply (frule r_cosEqVar1 [of "G" "H" "b1" "b"], assumption+)
 apply (rule sym, assumption+)
apply (frule subg_iOp_closed [of "G" "H" "tOp G a (iOp G a1)"], assumption+)
apply (simp add:invofab iOp_invinv)
apply (frule NSubgTr2 [of "G" "a" "b" "a1" "b1"], assumption+)
apply (frule NSubgTr1 [of "G" "H" "a" "a1"], assumption+)
apply (frule subg_tOp_closed [of "G" "H" "tOp G b (iOp G b1)" "tOp G (iOp G a1) a"], assumption+)
apply (insert  NSubgPr1 [of "G" "H" "a" " tOp G (tOp G b (iOp G b1)) (tOp G (iOp G a1) a)"] )
apply simp
apply (subgoal_tac "tOp G (tOp G a b) (iOp G (tOp G a1 b1)) \<in> H" )
prefer 2
apply simp
apply (insert  r_cosEq [of "G" "H" "tOp G a1 b1" "tOp G a b" ])
apply simp
done 

lemma ctOpTr2:" \<lbrakk> group G; H \<lhd> G; a \<in> carrier G; a1 \<in> carrier G;
  r_coset G H a = r_coset G H a1 \<rbrakk> \<Longrightarrow> 
             r_coset G H (iOp G a) = r_coset G H (iOp G a1) " 
apply (frule nmlSubgTr0, assumption+)
apply (frule r_cosEqVar1 [of "G" "H" "a" "a1"], assumption+)

apply (frule NSubgTr1 [of "G" "H" "a" "a1"], assumption+)

apply (frule  r_cosEq [of "G" "H" "iOp G a1" "iOp G a"], assumption+)
apply simp+
apply (simp add: iOp_invinv)
apply (frule subg_iOp_closed [of "G" "H" "tOp G a1 (iOp G a)"], assumption+)
apply (simp add: iOp_invinv invofab)
apply (simp add: NSubgTr1 [of "G" "H" "a1" "a"])
apply (rule sym, assumption+)
done


lemma cosiOpwelldefTr1: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
   cosiOp G H (r_coset G H a) \<subseteq>  r_coset G H (iOp G a)"  

apply (frule  nmlSubgTr0 [of "G" "H"], assumption+)  
apply (rule subsetI)
apply (frule iOp_closed [of "G" "a"], assumption+)
apply (subst NSubgLREq[THEN sym], assumption+)
apply (simp only:cosiOp_def) 
 apply (simp add:CollectI)
 apply (frule r_cosTr0_1 [of "G" "H" "a"], assumption+)
 apply simp 
apply auto
 apply (thin_tac "H\<^sub>G a \<in> set_r_cos G H")
 apply (simp add:r_coset_def [of "G" "H" "a"])
 apply auto
apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+) 
apply (frule_tac h = ha in subg_subset1 [of "G" "H"], assumption+)
apply (simp add:invofab)
apply (rule l_cos_belong, assumption+)
 apply simp
 apply (rule tOp_closed, assumption+)+ apply simp+
 apply (frule iOp_closed [of "G" "a"], assumption+)
 apply (frule iOp_closed [of "G" "a\<inverse>\<^sup>G"], assumption+)
 apply (subst tOp_assocTr45 [THEN sym], assumption+)
  apply simp
 apply (rule subg_tOp_closed [of "G" "H"], assumption+)
 apply (simp add:NSubgPr2_1 [of "G" "H" "a\<inverse>\<^sup>G" _])
 apply (simp add:subg_iOp_closed)
done

lemma cosiOpwelldefTr2: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
       r_coset G H (iOp G a) \<subseteq>  cosiOp G H (r_coset G H a)"
apply (rule subsetI)
 apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
 apply (frule r_cosTr0_1 [of "G" "H" "a"], assumption+)
apply (simp add: cosiOp_def) 
 apply (thin_tac "H\<^sub>G a \<in> set_r_cos G H")
 apply (frule iOp_closed [of "G" "a"], assumption+)
 apply (simp add:r_coset_def [of "G" "H" "a\<inverse>\<^sup>G"]) apply auto
 apply (frule aInR_cos [of "G" "H" "a"])
 apply (simp add:nmlSubgTr0) apply assumption
apply auto
done
 
lemma cosiOpwelldef: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G \<rbrakk> \<Longrightarrow>
    cosiOp G H (r_coset G H a) = r_coset G H (iOp G a)"  
 apply (rule equalityI)
 apply (simp add: cosiOpwelldefTr1 [of "G" "H" "a"])
 apply (simp add: cosiOpwelldefTr2 [of "G" "H" "a"])
done

lemma costOpwelldefTr1: "\<lbrakk>group G; H \<lhd> G; a \<in> carrier G; 
b \<in> carrier G; x \<in> r_coset G H a; y \<in> r_coset G H b\<rbrakk>
           \<Longrightarrow> tOp G x y \<in> r_coset G H (tOp G a b)"
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule r_cosTr0 [of "G" "H" "a" "x"], assumption+)
apply (frule r_cosTr0 [of "G" "H" "b" "y"], assumption+)
apply (frule r_cosEqVar2 [of "G" "H" "a" "x"], assumption+)
apply (frule r_cosEqVar2 [of "G" "H" "b" "y"], assumption+)
 apply (thin_tac "x \<in> r_coset G H a")
 apply (thin_tac "y \<in> r_coset G H b")

apply (frule ctOpTr1 [THEN sym, of "G" "H" "a" "b" "x" "y"], assumption+)
apply (frule aInR_cos [of "G" "H" "tOp G x y"], assumption+)
apply auto
done

lemma costOpwelldefTr2: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G;
b \<in> carrier G \<rbrakk> 
 \<Longrightarrow> costOp G H (r_coset G H a) (r_coset G H b) \<subseteq>  r_coset G H (tOp G a b)"
apply (insert nmlSubgTr0 [of "G" "H"])
apply (simp add: costOp_def)
apply (frule r_cosTr0_1 [of "G" "H" "b"], assumption+)
apply (frule r_cosTr0_1 [of "G" "H" "a"], assumption+)
apply auto
apply (simp add: costOpwelldefTr1 [of "G" "H" "a" "b" _])
done

lemma costOpwelldefTr4:"\<lbrakk> group G; H \<lhd> G; a \<in> carrier G;
b \<in> carrier G; x \<in> r_coset G H (tOp G a b) \<rbrakk> \<Longrightarrow>
   x \<in> costOp G H (r_coset G H a) (r_coset G H b) " 
(*
thm r_cosTool2 [of "G" "H" "tOp G a b" "x"]
*)
apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (frule r_cosTr0 [of "G" "H" "tOp G a b" "x"], assumption+)
apply auto 
apply (frule r_cosTool2 [of "G" "H" "a \<cdot>\<^sub>G b" "x"], assumption+)
apply auto
 apply (thin_tac "h \<cdot>\<^sub>G ( a \<cdot>\<^sub>G b) \<in> H\<^sub>G ( a \<cdot>\<^sub>G b)")
 apply (thin_tac "h \<cdot>\<^sub>G ( a \<cdot>\<^sub>G b) \<in> carrier G")
apply (simp add:costOp_def)
apply (frule r_cosTr0_1 [of "G" "H" "b"], assumption+)
apply (frule r_cosTr0_1 [of "G" "H" "a"], assumption+)
 apply auto
 apply (frule aInR_cos [of "G" "H" "a"], assumption+)
 apply (frule_tac h = h in r_cosTr8 [of "G" "H" "a" _ "a"], assumption+)
 apply (frule aInR_cos [of "G" "H" "b"], assumption+)
 apply (frule subg_subset1, assumption+)
 apply (frule_tac a1 = h in tOp_assoc [of "G" _ "a" "b", THEN sym], 
                                       assumption+)
apply auto
done

lemma costOpwelldefTr5: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G;
b \<in> carrier G \<rbrakk> 
 \<Longrightarrow> r_coset G H (tOp G a b) \<subseteq> costOp G H (r_coset G H a) (r_coset G H b)"
apply (rule subsetI) 
apply (frule costOpwelldefTr4 [of "G" "H" "a" "b" _], assumption+)
done

lemma costOpwelldef: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G;
b \<in> carrier G \<rbrakk> 
 \<Longrightarrow> r_coset G H (tOp G a b) = costOp G H (r_coset G H a) (r_coset G H b)"
apply (rule equalityI)
apply (simp add:costOpwelldefTr5)
apply (simp add:costOpwelldefTr2)
done           

lemma qgrpUnit: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G\<rbrakk> \<Longrightarrow>
    costOp G H H (r_coset G H a) = r_coset G H a" 

apply (frule nmlSubgTr0 [of "G" "H"], assumption+)
apply (subgoal_tac "costOp G H H (r_coset G H a) = 
       costOp G H (r_coset G H (1\<^sub>G)) (r_coset G H a)" )
apply simp
apply (subst costOpwelldef [THEN sym, of "G" "H" "1\<^sub>G" "a"], assumption+)
apply (simp add:ex_one) apply assumption apply simp
apply (insert r_cosUnit1[of "G" "H"])
apply simp
done

lemma qgrpUnitTr:"\<lbrakk>group G; H \<lhd> G\<rbrakk>
  \<Longrightarrow> \<forall>x \<in> set_r_cos G H. costOp G H H x = x" 
apply (simp only: set_r_cos_def)
apply (simp add:qgrpUnit)+
apply (insert qgrpUnit [of "G" "H" _])
apply auto
done

lemma qgrpInv: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G\<rbrakk> \<Longrightarrow>
    costOp G H (cosiOp G H (r_coset G H a))  (r_coset G H a) = H"

apply (insert cosiOpwelldef [of "G" "H" "a"])
apply simp+

apply (simp add:costOpwelldef [THEN sym, of "G" "H" "iOp G a" "a"])
apply (simp add:iOp_l_inv r_one)

apply (insert nmlSubgTr0 [of "G" "H"])
apply simp
apply (simp add:r_cosUnit1)
done  

lemma qgrpInvTr:"\<lbrakk> group G; H \<lhd> G \<rbrakk>
  \<Longrightarrow> \<forall> x \<in> set_r_cos G H. costOp G H (cosiOp G H x) x = H "
apply (simp only:set_r_cos_def)   
apply (insert qgrpInv [of "G" "H" _])
apply auto
done

lemma qgrpAssBop: "\<lbrakk> group G; H \<lhd> G; a \<in> carrier G; b \<in> carrier G;
c \<in> carrier G \<rbrakk> \<Longrightarrow> costOp G H (r_coset G H a) 
     (costOp G H (r_coset G H b) (r_coset G H c)) = 
costOp G H (costOp G H (r_coset G H a) (r_coset G H b)) (r_coset G H c)"

apply (simp add:costOpwelldef [THEN sym])
apply (simp add:tOp_assoc)
done

lemma qgrpAssBopTr: "\<lbrakk> group G; H \<lhd> G \<rbrakk> \<Longrightarrow>
\<forall>X\<in>set_r_cos G H. \<forall>Y\<in>set_r_cos G H. \<forall>Z\<in>set_r_cos G H. costOp G H X 
   (costOp G H Y Z) = costOp G H (costOp G H X Y) Z"
apply (simp only:set_r_cos_def)
apply (insert qgrpAssBop [of "G" "H" _])
apply  auto
done

lemma Qgrp_bOp: "\<lbrakk> group G; H \<lhd> G \<rbrakk> \<Longrightarrow> 
  costOp G H : set_r_cos G H \<rightarrow> set_r_cos G H \<rightarrow> set_r_cos G H"
(* later we have to clean up the following proof *)
apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:set_r_cos_def) apply auto
 apply (subst costOpwelldef[THEN sym], assumption+)
 apply (frule_tac a = aa and b = ab in tOp_closed [of "G"], assumption+)
apply auto
done

lemma Qgrp_iOp: "\<lbrakk>group G; H \<lhd> G \<rbrakk> \<Longrightarrow>
      cosiOp G H : set_r_cos G H \<rightarrow> set_r_cos G H"

apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:set_r_cos_def)
 apply auto
apply (frule_tac a = a in cosiOpwelldef [of "G" "H"], assumption+)
 apply simp
 apply (frule_tac a = a in iOp_closed [of "G"], assumption+)
apply auto
done

lemma ex_Qgrp_one: "\<lbrakk> group G; H \<lhd> G \<rbrakk> \<Longrightarrow>  H \<in> set_r_cos G H"
apply (simp add:set_r_cos_def)
apply (insert nmlSubgTr0 [of "G" "H"])
apply auto

apply (insert r_cosUnit1[of "G" "H" ])
apply simp

apply (frule ex_one [of "G"])
apply blast
done

theorem Qgrp:"\<lbrakk> group G; H \<lhd> G \<rbrakk> \<Longrightarrow>  group (qgrp G H)"
apply (simp add:qgrp_def)
apply (frule  Qgrp_bOp [of "G" "H"], assumption+)
apply (frule  Qgrp_iOp [of "G" "H"], assumption+)
apply (frule  ex_Qgrp_one [of "G" "H"], assumption+)
apply (frule  qgrpInvTr [of "G" "H" ], assumption+)
apply (frule  qgrpAssBopTr [of "G" "H"], assumption+)
apply (frule  qgrpUnitTr [of "G" "H" ], assumption+)
apply (simp only:group_def)
apply simp
done

lemma Qgrp_one:"\<lbrakk>group G; H \<lhd> G \<rbrakk> \<Longrightarrow> one (G / H) = H"
apply (simp add:qgrp_def)
done

lemma Qgrp_carrierTr:"group G \<Longrightarrow> carrier (G / (N::'a set)) = set_r_cos G N" 
apply (simp add:qgrp_def)
done    (** only a trick *)

lemma grp_qgrp:"\<lbrakk>group G; N \<lhd> G\<rbrakk> \<Longrightarrow> grp (G/N) (carrier (G/N)) = G/N"
apply (simp add:grp_def qgrp_def)
done

lemma Pjhom0: "\<lbrakk> group G; H \<lhd> G; x \<in> carrier G; y \<in> carrier G \<rbrakk>
  \<Longrightarrow> Pj G H ( tOp G x y) = tOp (qgrp G H) (Pj G H x) (Pj G H y)"
apply (simp add:Pj_def)
apply (simp add:qgrp_def) apply (simp add:costOpwelldef)
done

lemma Pjhom1:"\<lbrakk> group G; N \<lhd> G \<rbrakk> \<Longrightarrow> (Pj G N) \<in> gHom G (G / N)"
apply (simp add:gHom_def)
apply (rule conjI)
apply (simp add:restrict_def Pj_def)
apply (simp add:extensional_def)
apply (rule conjI) apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
apply (simp add:qgrp_def set_r_cos_def) apply (simp add:Pj_def)
apply blast
apply (rule ballI)+
apply (simp add:Pjhom0)
done

lemma Pj_mem:"\<lbrakk> group G; N \<lhd> G; x \<in> carrier G \<rbrakk> \<Longrightarrow> 
                              (Pj G N) x = r_coset G N x"
apply (simp add:Pj_def)
done

lemma Pj_gsurjec: "\<lbrakk> group G; N \<lhd> G \<rbrakk> \<Longrightarrow> gsurjec G (G/N) (Pj G N)"
apply (simp add:gsurjec_def)
apply (simp add:Pjhom1)
apply (simp add:surj_to_def)
apply (rule equalityI)
apply (frule Pjhom1, assumption+) apply (simp add:gHom_def)
 apply (erule conjE)+
 apply (rule image_sub [of "Pj G N" "carrier G" "carrier (G / N)" 
  "carrier G"], assumption+) apply simp
apply (rule subsetI) apply (simp add:qgrp_def set_r_cos_def)
apply (simp add:Pj_def image_def)
done

lemma l_coset_in_subg:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> G; K \<subseteq> H; a \<in> H \<rbrakk>  \<Longrightarrow> 
            l_coset G a K = l_coset (grp G H) a K"
apply (simp add:l_coset_def)
apply (simp add:grp_def)
done

lemma r_coset_in_subg:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> G; K \<subseteq> H; a \<in> H \<rbrakk>  \<Longrightarrow> K\<^sub>G a = K\<^sub>(grp G H) a"
apply (simp add:r_coset_def)
apply (simp add:grp_def)
done


section "5. Setproducts"
       
constdefs
  commutators:: "('a, 'more) GroupType_scheme \<Rightarrow> 'a set"
     "commutators G == {z. \<exists> a\<in> (carrier G). \<exists>b \<in> (carrier G). 
       ((a \<cdot>\<^sub>G b) \<cdot>\<^sub>G a\<inverse>\<^sup>G) \<cdot>\<^sub>G b\<inverse>\<^sup>G  = z}" 

lemma commutator: "\<lbrakk> group G; H \<guillemotleft> G; (commutators G) \<subseteq> H  \<rbrakk> \<Longrightarrow> 
         H \<lhd> G "
apply (rule nmlSubg2 [of "G" "H" ], assumption+)
apply (rule ballI)+
 apply (frule subg_subset1, assumption+)
apply (subgoal_tac "a \<cdot>\<^sub>G h \<cdot>\<^sub>G a\<inverse>\<^sup>G \<cdot>\<^sub>G h\<inverse>\<^sup>G \<in> H") prefer 2 
 apply (simp add:commutators_def)
 apply (rule subsetD, assumption+) apply (simp add:CollectI)
 apply blast 
apply (frule_tac ?h1.0 ="a \<cdot>\<^sub>G h \<cdot>\<^sub>G a\<inverse>\<^sup>G \<cdot>\<^sub>G h\<inverse>\<^sup>G" and ?h2.0 = h in 
         subg_tOp_closed [of "G" "H"], assumption+)
apply (frule_tac a = a in  iOp_closed [of "G"], assumption+)
apply (frule_tac a = h in  iOp_closed [of "G"], assumption+)
(* thm tOp_assoc [of "G", THEN sym] *)
apply (frule_tac a1 = "a \<cdot>\<^sub>G h \<cdot>\<^sub>G a\<inverse>\<^sup>G" and b1 = "h\<inverse>\<^sup>G" and c1 = h in 
       tOp_assoc [of "G", THEN sym]) 
 apply (rule tOp_closed, assumption+)+
 apply (simp add:iOp_l_inv r_one)
done

constdefs
 settOp :: "[('a, 'more) GroupType_scheme, 'a set, 'a set] \<Rightarrow> 'a set "
  "settOp G H K == {z. \<exists>x \<in> H. \<exists>y \<in> K. (x \<cdot>\<^sub>G y = z)}"

syntax 
  "@SBOP1" :: "['a set, ('a, 'more) GroupType_scheme, 'a set] \<Rightarrow> 'a set"
            ("(3_/ \<bullet>\<^sub>_/ _)" [66,66,67]66)
translations
  "H \<bullet>\<^sub>G K" == "settOp G H K"

lemma settOpinherited:"\<lbrakk> group G; L \<guillemotleft> G; H \<subseteq> L; K \<subseteq> L \<rbrakk> 
        \<Longrightarrow> settOp (grp G L) H K =  H \<bullet>\<^sub>G K "
apply (simp add:settOp_def) 
apply (simp add:grp_def)
done

lemma settOp_one_l:"\<lbrakk> group G; K \<guillemotleft> G \<rbrakk> \<Longrightarrow> {1\<^sub>G} \<bullet>\<^sub>G K = K"
apply (simp add:settOp_def)
apply auto
 apply (frule subg_subset1, assumption+) apply simp
 apply (subgoal_tac "\<forall>y\<in>K. 1\<^sub>G \<cdot>\<^sub>G y = y") 
apply auto
 apply (frule_tac h = y in subg_subset1 [of "G" "K"], assumption+)
 apply simp
done

lemma settOp_one_r:"\<lbrakk>group G; K \<guillemotleft> G\<rbrakk> \<Longrightarrow> K \<bullet>\<^sub>G {1\<^sub>G} = K"
apply (simp add:settOp_def)
apply auto
 apply (frule subg_subset1, assumption+) apply (simp add:r_one) 
apply (subgoal_tac "\<forall>k\<in>K. k \<cdot>\<^sub>G (1\<^sub>G) = k") apply auto
apply (frule_tac h = k in subg_subset1 [of "G" "K"], assumption+)
apply (simp add:r_one)
done

lemma settOpTr0:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G\<rbrakk> \<Longrightarrow>  H \<bullet>\<^sub>G K \<subseteq> carrier G "
apply (simp add:settOp_def)
apply (rule subsetI) apply (simp add:CollectI)
apply auto
apply (frule_tac h = xa in subg_subset1 [of "G" "H"], assumption+)
apply (frule_tac h = y in subg_subset1 [of "G" "K"], assumption+)
apply simp
done

lemma subg_inc_settOp:"\<lbrakk> group G; L \<guillemotleft> G; H \<subseteq> L; K \<subseteq> L\<rbrakk> \<Longrightarrow>  H \<bullet>\<^sub>G K \<subseteq> L "
apply (rule subsetI)
apply (simp add:settOp_def)
apply auto
apply (frule_tac c = xa in subsetD [of "H" "L"], assumption+)
apply (frule_tac c = y in subsetD [of "K" "L"], assumption+)
apply (simp add:subg_tOp_closed)
done

lemma settOpTr0_s:"\<lbrakk> group G; H \<subseteq> (carrier G); K \<subseteq> (carrier G)\<rbrakk> 
                         \<Longrightarrow>  H \<bullet>\<^sub>G K \<subseteq> carrier G "
apply (rule subsetI)
apply (simp add:settOp_def CollectI)
apply auto
apply (subgoal_tac "xa \<in> carrier G")
apply (subgoal_tac "y \<in> carrier G")
apply simp
apply (simp add:subsetD)+
done

lemma settOpTr1:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G; a \<in> H; b \<in> K \<rbrakk> \<Longrightarrow> 
    a \<cdot>\<^sub>G b \<in> H \<bullet>\<^sub>G K "
apply (simp add:settOp_def)
apply auto
done

lemma settOpTr1_s:"\<lbrakk> group G; H \<subseteq> carrier G; K \<subseteq> carrier G; 
a \<in> H; b \<in> K \<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>G b \<in> H \<bullet>\<^sub>G K "
apply (simp add:settOp_def)
apply auto
done

lemma  settOpTr1_1:"\<lbrakk> group G; H \<subseteq> carrier G; K \<subseteq> carrier G; 
                      u \<in> H \<bullet>\<^sub>G K \<rbrakk> \<Longrightarrow>  \<exists>a \<in> H. \<exists>b \<in> K. (a \<cdot>\<^sub>G b = u)"
apply (simp add:settOp_def)
done

lemma settOpTr1_2:"\<lbrakk> group G; H \<subseteq> carrier G; K \<subseteq> carrier G; 
         H1 \<subseteq> H; K1 \<subseteq> K \<rbrakk> \<Longrightarrow>  H1 \<bullet>\<^sub>G K1 \<subseteq> H \<bullet>\<^sub>G K "
apply (rule subsetI)
apply (simp add:settOp_def) apply blast
done

lemma settOpTr2:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G\<rbrakk> \<Longrightarrow>  1\<^sub>G \<in> H \<bullet>\<^sub>G K "
apply (frule subg_one_closed [of "G" "H"], assumption+)
apply (frule subg_one_closed [of "G" "K"], assumption+)
apply (simp add:settOp_def)
apply (frule ex_one [of "G"])
apply (frule l_one [of "G" "1\<^sub>G"], assumption+)
apply blast
done

lemma settOpTr3:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G;  K \<bullet>\<^sub>G H = H \<bullet>\<^sub>G K;
  u \<in> H \<bullet>\<^sub>G K;  v \<in>  H \<bullet>\<^sub>G K \<rbrakk> \<Longrightarrow>  u \<cdot>\<^sub>G v \<in> H \<bullet>\<^sub>G K "
apply (frule subg_subset [of "G" "H"], assumption+)
apply (frule subg_subset [of "G" "K"], assumption+)
apply (subgoal_tac "u \<in>  K \<bullet>\<^sub>G H")
apply (frule settOpTr1_1 [of "G" "K" "H" "u"], assumption+)
apply auto apply (thin_tac " a \<cdot>\<^sub>G b \<in> H \<bullet>\<^sub>G K") 
apply (subgoal_tac "\<exists>h\<in>H. \<exists>k\<in>K. h \<cdot>\<^sub>G k = v")
prefer 2 apply (simp add:settOp_def) apply auto
 apply (frule_tac h = a in subg_subset1 [of "G" "K"], assumption+)
 apply (frule_tac h = k in subg_subset1 [of "G" "K"], assumption+)
 apply (frule_tac h = b in subg_subset1 [of "G" "H"], assumption+)
 apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
apply (subst tOp_assocTr43, assumption+)
apply (subst tOp_assocTr42, assumption+)
apply (subgoal_tac "a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h) \<in>  K \<bullet>\<^sub>G H") apply simp
apply (subgoal_tac "\<exists>h1\<in>H. \<exists>k1\<in>K. h1 \<cdot>\<^sub>G k1 = a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h)")
 prefer 2 apply (simp add:settOp_def)
apply (subgoal_tac "\<forall>h1\<in>H. \<forall>k1\<in>K.  h1 \<cdot>\<^sub>G k1 =  a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h) \<longrightarrow> 
          (a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h) \<cdot>\<^sub>G k \<in> H \<bullet>\<^sub>G K)") apply blast
apply (thin_tac "\<exists>h1\<in>H. \<exists>k1\<in>K.  h1 \<cdot>\<^sub>G k1 =  a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h)")
apply (rule ballI)+ apply (rule impI) apply (rotate_tac -1)
apply (frule sym) apply (thin_tac "h1 \<cdot>\<^sub>G k1 =  a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h)")
apply simp
 apply (thin_tac "a \<in> carrier G")
 apply (thin_tac "b \<in> carrier G")
 apply (thin_tac "h \<in> carrier G")
 apply (thin_tac "a \<cdot>\<^sub>G ( b \<cdot>\<^sub>G h) =  h1 \<cdot>\<^sub>G k1")
 apply (thin_tac "h1 \<cdot>\<^sub>G k1 \<in> H \<bullet>\<^sub>G K")
apply (frule_tac h = k1 in subg_subset1 [of "G" "K"], assumption+)
apply (frule_tac h = h1 in subg_subset1 [of "G" "H"], assumption+)
apply (subst tOp_assoc, assumption+)
apply (frule_tac ?h1.0 = k1 and ?h2.0 = k in subg_tOp_closed [of "G" "K"],
                               assumption+)
apply (simp add:settOp_def) apply blast
apply (frule_tac ?h1.0 = b and ?h2.0 = h in subg_tOp_closed [of "G" "H"],
                               assumption+)
apply (simp add:settOp_def) apply blast
done

lemma settOpTr4:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G; H \<bullet>\<^sub>G K =  K \<bullet>\<^sub>G H;
 u \<in>  H \<bullet>\<^sub>G K\<rbrakk> \<Longrightarrow>  u\<inverse>\<^sup>G \<in> H \<bullet>\<^sub>G K "
apply (subgoal_tac "\<exists>h\<in>H. \<exists>k\<in>K. h \<cdot>\<^sub>G k = u") prefer 2
 apply (thin_tac "H \<bullet>\<^sub>G K = K \<bullet>\<^sub>G H")
 apply (simp add:settOp_def) (** apply auto is too slow. From here **) 
apply (subgoal_tac "\<forall>h\<in>H. \<forall>k\<in>K.  h \<cdot>\<^sub>G k = u \<longrightarrow> u\<inverse>\<^sup>G \<in> H \<bullet>\<^sub>G K")
apply blast apply (thin_tac "\<exists>h\<in>H. \<exists>k\<in>K.  h \<cdot>\<^sub>G k = u")
apply (rule ballI)+ apply (rule impI) (** to here.  **)
apply (frule sym [of _ "u"]) apply (thin_tac "h \<cdot>\<^sub>G k = u")
apply simp
apply (frule_tac h = h in subg_subset1 [of "G" "H"], assumption+)
apply (frule_tac h = k in subg_subset1 [of "G" "K"], assumption+)
apply (simp add:invofab)
apply (frule sym) apply (thin_tac "H \<bullet>\<^sub>G K = K \<bullet>\<^sub>G H")
 apply (thin_tac "h \<cdot>\<^sub>G k \<in> K \<bullet>\<^sub>G H")
 apply (thin_tac "K \<bullet>\<^sub>G H = H \<bullet>\<^sub>G K")
apply (frule_tac x = h in subg_iOp_closed [of "G" "H"], assumption+)
apply (frule_tac x = k in subg_iOp_closed [of "G" "K"], assumption+)
apply (simp add:settOp_def) apply auto
done

lemma settOpTr5:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G; L \<guillemotleft> G \<rbrakk> \<Longrightarrow>
         (H \<bullet>\<^sub>G K) \<bullet>\<^sub>G L =  H \<bullet>\<^sub>G (K \<bullet>\<^sub>G L)"
apply (simp add:settOp_def [of "G" "H \<bullet>\<^sub>G K" "L"])
apply (simp add:settOp_def [of "G" "H" "K \<bullet>\<^sub>G L"])
apply auto
apply (simp add:settOp_def [of "G" "H" "K"])
apply auto
apply (frule_tac h = x in subg_subset1 [of "G" "H"], assumption+) 
apply (frule_tac h = ya in subg_subset1 [of "G" "K"], assumption+) 
apply (frule_tac h = y in subg_subset1 [of "G" "L"], assumption+) 
apply (frule_tac  a = x and b = ya and c = y in tOp_assoc [of "G"], 
                    assumption+) apply simp
apply (subgoal_tac "ya \<cdot>\<^sub>G y \<in> K \<bullet>\<^sub>G L")  apply blast
 apply (thin_tac "x \<cdot>\<^sub>G ya \<cdot>\<^sub>G y =  x \<cdot>\<^sub>G ( ya \<cdot>\<^sub>G y)")
 apply (simp add:settOp_def) apply blast
apply (simp add:settOp_def [of "G" "K" "L"])
 apply auto
apply (frule_tac h = xa in subg_subset1 [of "G" "H"], assumption+) 
apply (frule_tac h = x in subg_subset1 [of "G" "K"], assumption+) 
apply (frule_tac h = ya in subg_subset1 [of "G" "L"], assumption+)
apply (frule_tac  a1 = xa and b1 = x and c1 = ya in 
                            tOp_assoc [of "G", THEN sym], assumption+)
apply simp
 apply (thin_tac "xa \<cdot>\<^sub>G ( x \<cdot>\<^sub>G ya) =   xa \<cdot>\<^sub>G x \<cdot>\<^sub>G ya")
 apply (subgoal_tac "xa \<cdot>\<^sub>G x \<in> H \<bullet>\<^sub>G K")
 apply blast
apply (simp  add:settOp_def) apply blast
done

lemma settOpTr6: "\<lbrakk> group G; H1 \<guillemotleft> G; H2 \<guillemotleft> G; K \<guillemotleft> G; H1 \<subseteq> K \<rbrakk> \<Longrightarrow>
      ( H1 \<bullet>\<^sub>G H2) \<inter> K = H1 \<bullet>\<^sub>G (H2 \<inter> K) " 
apply auto
apply (simp add:settOp_def [of "G" "H1" "H2"]) apply auto
apply (frule_tac  c = xa in subsetD [of "H1" "K"], assumption+)
apply (frule_tac x = xa in subg_iOp_closed [of "G" "K"], assumption+)
apply (frule_tac  ?h1.0 = "xa\<inverse>\<^sup>G" and ?h2.0 = "xa \<cdot>\<^sub>G y" in 
              subg_tOp_closed [of "G" "K"], assumption+)
apply (frule_tac h = xa in subg_subset1 [of "G" "K"], assumption+) 
apply (frule_tac h = "xa\<inverse>\<^sup>G" in subg_subset1 [of "G" "K"], assumption+) 
apply (frule_tac h = y in subg_subset1 [of "G" "H2"], assumption+)
apply (simp add:tOp_assoc [THEN sym])
apply (simp add:iOp_l_inv)
 apply (simp add:settOp_def)
 apply auto
apply (simp add:settOp_def) apply auto
apply (simp add:settOp_def) apply auto
apply (frule_tac  c = xa in subsetD [of "H1" "K"], assumption+)
apply (simp add:subg_tOp_closed)
done

lemma settOpTr6_1: "\<lbrakk> group G; H1 \<guillemotleft> G; H2 \<guillemotleft> G; K \<guillemotleft> G; H2 \<subseteq> K \<rbrakk> \<Longrightarrow>
      ( H1 \<bullet>\<^sub>G H2) \<inter> K = (H1 \<inter> K) \<bullet>\<^sub>G H2 " 
apply auto
apply (simp add:settOp_def [of "G" "H1" "H2"])
apply auto
apply (frule_tac  c = y in subsetD [of "H2" "K"], assumption+)
apply (frule_tac x = y in subg_iOp_closed [of "G" "K"], assumption+)
apply (frule_tac  ?h1.0 = "xa \<cdot>\<^sub>G y" and ?h2.0 = "y\<inverse>\<^sup>G" in 
              subg_tOp_closed [of "G" "K"], assumption+)
apply (frule_tac h = xa in subg_subset1 [of "G" "H1"], assumption+) 
apply (frule_tac h = y in subg_subset1 [of "G" "K"], assumption+) 
apply (frule_tac h = "y\<inverse>\<^sup>G" in subg_subset1 [of "G" "K"], assumption+) 
apply (simp add:tOp_assoc iOp_r_inv r_one)
apply (simp add:settOp_def) apply auto
apply (simp add:settOp_def) apply auto
apply (simp add:settOp_def) apply auto
apply (frule_tac  c = y in subsetD [of "H2" "K"], assumption+)
apply (simp add:subg_tOp_closed)
done

lemma settOpTr7: "\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G \<rbrakk> \<Longrightarrow> H \<subseteq> H \<bullet>\<^sub>G K"
apply (simp add:settOp_def)
apply (rule subsetI)
apply (frule subg_one_closed [of "G" "K"], assumption+)
apply (simp add:CollectI)
apply (frule_tac h = x in subg_subset1 [of "G" "H"], assumption+) 
 apply (frule_tac a = x in r_one [of "G"], assumption+)
 apply blast
done

lemma settOpTr7_1: "\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G \<rbrakk> \<Longrightarrow> K \<subseteq> H \<bullet>\<^sub>G K"
apply (rule subsetI)
 apply (simp add:settOp_def)
 apply (frule_tac h = x in subg_subset1 [of "G" "K"], assumption+)
 apply (frule_tac a = x in l_one [of "G"], assumption+)
 apply (frule subg_one_closed [of "G" "H"], assumption+)
apply blast
done

lemma settOpTr8: "\<lbrakk> group G; H \<guillemotleft> G \<rbrakk> \<Longrightarrow> H = H \<bullet>\<^sub>G H"
apply (rule equalityI)
apply (simp add:settOpTr7)
apply (rule subsetI)
apply (simp add:settOp_def) apply auto
apply (simp add:subg_tOp_closed)
done

section "6. preliminary lemmas for Zassenhaus"

lemma ZassenhausTr0: "\<lbrakk> group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G;
   H1 \<lhd> grp G H; K1 \<lhd> grp G K \<rbrakk> \<Longrightarrow> (H \<inter> K1) \<lhd> grp G (H \<inter> K)"
apply (frule inter_subgs [of "G" "H" "K"], assumption+)
apply (frule inter_subgs [of "G" "H" "K1"], assumption+)
apply (subgoal_tac "H \<inter> K1 \<subseteq> H \<inter> K")
apply (frule subg_in_subg [of "G" "H \<inter> K1" "H \<inter> K"], assumption+)
apply (rule nmlSubg2 [of "grp G (H \<inter> K)" "H \<inter> K1"])
 apply (simp add:subggrp)+ 
 apply (rule ballI)+
 apply (simp add:grp_def) apply (fold grp_def)
apply (rule conjI)
 apply (erule conjE)+
 apply (rule subg_tOp_closed, assumption+)+
 apply (simp add:subg_iOp_closed)
 apply (erule conjE)+ 
apply (frule subggrp [of "G" "K"], assumption+)
 apply (frule_tac a = a and h = h in NSubgPr1_1 [of "grp G K" "K1"], 
                                       assumption+)
 apply (simp add:grp_def) apply assumption apply (simp add:grp_def)
apply (frule subggrp [of "G" "K"], assumption+)
 apply (frule nmlSubgTr0 [of "grp G K" "K1"], assumption+)
 apply (frule subg_subset [of "grp G K" "K1"], assumption+)
apply (rule subsetI)
 apply (simp add:grp_def subsetD)
done
 
    
lemma subgsubg:"\<lbrakk> group G; H \<guillemotleft> G; K \<guillemotleft> G; H \<bullet>\<^sub>G K =  K \<bullet>\<^sub>G H \<rbrakk> \<Longrightarrow> H \<bullet>\<^sub>G K \<guillemotleft> G"
apply (frule settOpTr0 [of "G" "H" "K"], assumption+)
apply (frule settOpTr2 [of "G" "H" "K"], assumption+) 
apply (unfold subgroup_def [of "G" "H \<bullet>\<^sub>G K"]) apply simp
apply (rule conjI)
apply (rule ballI)+
apply (rule settOpTr3, assumption+)

apply (rule ballI)
apply (rule settOpTr4 [of "G" "K" "H" _], assumption+)
 apply (rule sym, assumption+)
done

lemma l_coset_sub:"\<lbrakk>group G; H \<guillemotleft> G; N \<guillemotleft> G; a \<in> H\<rbrakk> \<Longrightarrow> l_coset G a N \<subseteq> H \<bullet>\<^sub>G N"
apply (rule subsetI)
 apply (simp add:l_coset_def settOp_def)
 apply auto
done

lemma r_coset_sub:"\<lbrakk>group G; H \<guillemotleft> G; N \<guillemotleft> G; a \<in> H\<rbrakk> \<Longrightarrow> r_coset G N a \<subseteq> N \<bullet>\<^sub>G H"
apply (rule subsetI)
 apply (simp add:r_coset_def settOp_def)
 apply auto
done

lemma subgnsubg:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> H \<bullet>\<^sub>G N = N \<bullet>\<^sub>G H "
apply auto
 apply (simp add:settOp_def [of "G" "H" "N"])
 apply auto
 apply (subgoal_tac "xa \<cdot>\<^sub>G y \<in> l_coset G xa N")
 apply (frule_tac h = xa in subg_subset1 [of "G" "H"], assumption+)
 apply (frule_tac a = xa in NSubgLREq [of "G" "N"], assumption+)
 apply simp apply (thin_tac "xa N\<^sub>G = N\<^sub>G xa")
 apply (simp add:r_coset_def) apply auto apply (frule sym)
 apply (thin_tac "h \<cdot>\<^sub>G xa =  xa \<cdot>\<^sub>G y") apply simp
 apply (thin_tac "xa \<cdot>\<^sub>G y =  h \<cdot>\<^sub>G xa")
apply (simp add:settOp_def) 
 apply auto
 apply (simp add:l_coset_def) apply auto

apply (simp add:settOp_def [of "G" "N" "H"]) 
apply auto
 apply (subgoal_tac "xa \<cdot>\<^sub>G y \<in> r_coset G N y")
 apply (frule_tac h = y in subg_subset1 [of "G" "H"], assumption+)
 apply (frule_tac a1 = y in NSubgLREq [THEN sym, of "G" "N"], assumption+)
 apply simp
 apply (thin_tac "N\<^sub>G y = y N\<^sub>G")
apply (simp add:l_coset_def) apply auto
apply (frule sym) apply (thin_tac "y \<cdot>\<^sub>G h =  xa \<cdot>\<^sub>G y") 
apply simp apply (thin_tac "xa \<cdot>\<^sub>G y =  y \<cdot>\<^sub>G h")
 apply (simp add:settOp_def) apply auto
apply (simp add:r_coset_def) apply auto 
done

lemma subgns:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> H \<bullet>\<^sub>G N  \<guillemotleft> G "

apply (insert subgnsubg [of "G" "H" "N"])
apply simp

apply (rule subgsubg [of "G" "N" "H"])
apply assumption
apply (simp add:nmlSubgTr0)
apply assumption
apply auto
done

lemma subgnS:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> N \<bullet>\<^sub>G H  \<guillemotleft> G "
apply (frule subgns, assumption+)
apply (frule subgnsubg, assumption+)
apply simp
done

lemma subgns1:"\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> group (grp G (H \<bullet>\<^sub>G N))"

apply (insert subgns [of "G" "H" "N"])
apply simp
apply (simp add:subggrp)
done

lemma NinHNTr0:"\<lbrakk>group G; H \<guillemotleft> G; N \<guillemotleft> G \<rbrakk> \<Longrightarrow> N \<subseteq>  H \<bullet>\<^sub>G N" 
apply (simp add:settOp_def) 
apply (rule subsetI)
apply (frule subg_one_closed, assumption+)
apply (simp add:CollectI)
apply (frule_tac h = x in subg_subset1 [of "G" "N"], assumption+)
apply (frule_tac a = x in l_one [of "G"], assumption+)
apply blast
done

lemma HinHK:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> G \<rbrakk> \<Longrightarrow> H \<subseteq>  H \<bullet>\<^sub>G K" 
apply (rule subsetI)
apply (frule subg_one_closed [of "G" "K"], assumption+)
apply (simp add:settOp_def) 
apply (frule_tac h = x in subg_subset1 [of "G" "H"], assumption+)
apply (frule_tac a = x in r_one, assumption+) 
apply auto
done

lemma NinHNTr2:"\<lbrakk>group G; H \<guillemotleft> G; N \<lhd> G\<rbrakk> \<Longrightarrow> N \<guillemotleft>  grp G (H \<bullet>\<^sub>G N)"
apply (frule nmlSubgTr0, assumption+) 
apply (frule NinHNTr0 [of "G" "H" "N"], assumption+)
apply (frule subgns, assumption+)  
apply (simp add:subg_in_subg)
done

lemma NinHNTr0_1:"\<lbrakk>group G; H \<guillemotleft> G; N \<lhd>  G \<rbrakk> \<Longrightarrow> N \<subseteq>  H \<bullet>\<^sub>G N"
apply (frule NinHNTr2 [of "G" "H" "N"], assumption+) 
apply (simp add:grp_def)
apply (simp add:subgroup_def)
done

lemma NinHNTr0_2:"\<lbrakk>group G; H \<guillemotleft> G; K \<guillemotleft> G; H \<subseteq> K\<rbrakk> \<Longrightarrow>  H \<bullet>\<^sub>G K = K"
apply (simp add:settOp_def)
apply auto
apply (frule_tac c = xa in subsetD [of "H" "K"], assumption+)
apply (simp add:subg_tOp_closed)
apply (frule subg_one_closed [of "G" "H"], assumption+)
apply (frule_tac h = x in subg_subset1 [of "G" "K"], assumption+)
apply (frule_tac a = x in l_one [of "G"], assumption+)
apply blast
done
  
lemma nnsubg1:"\<lbrakk>group G; H \<guillemotleft> G; N \<lhd> G; N \<subseteq> H\<rbrakk> \<Longrightarrow> N \<lhd> grp G H"
apply (frule nmlSubgTr0, assumption+)
apply (simp add:nsubgroup_def [of "grp G H" "N"])
apply (simp add:subggrp)
apply (simp add:subg_in_subg)
apply (rule ballI)
apply (subst l_coset_in_subg[THEN sym], assumption+)
 apply (simp add:grp_def)
apply (subst r_coset_in_subg[THEN sym], assumption+)
 apply (simp add:grp_def)
 apply (simp add:grp_def)
 apply (frule_tac h = x in subg_subset1 [of "G" "H"], assumption+)
apply (simp add:nsubgroup_def)
done

lemma nnsubg: "\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> N \<lhd> grp G (H \<bullet>\<^sub>G N)"
apply (frule subgns1, assumption+)
apply (frule NinHNTr2 [of "G" "H" "N"], assumption+)
apply (frule subgns [of "G" "H" "N"], assumption+)
apply (rule nnsubg1 [of "G" "H \<bullet>\<^sub>G N" "N"], assumption+)
apply (frule subg_subset[of "grp G (H \<bullet>\<^sub>G N)" "N"], assumption+)
apply (simp add:grp_def)
done 

lemma nnsubg_1: "\<lbrakk> group G; H \<guillemotleft> G; N \<lhd> G \<rbrakk> \<Longrightarrow> N \<lhd> grp G (N \<bullet>\<^sub>G H)"
apply (frule nnsubg, assumption+)
apply (frule subgnsubg, assumption+)
apply simp
done

lemma ZassenhausTr1:"\<lbrakk>group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G;
   H1 \<lhd> grp G H; K1 \<lhd> grp G K\<rbrakk> \<Longrightarrow> H1 \<bullet>\<^sub>G (H \<inter> K1) = (H \<inter> K1) \<bullet>\<^sub>G H1"
apply auto
 apply (simp add:settOp_def [of "G" "H1" "H \<inter> K1"])
 apply auto
 apply (frule_tac a = y in r_coset_sub [of "G" "H \<inter> K1" "H1"])
 apply (simp add:inter_subgs) apply simp+
 apply (frule subggrp [of "G" "H"], assumption+)
 apply (frule_tac a = y in NSubgLREq [of "grp G H" "H1"], assumption+)
 apply (simp add:grp_def)
 apply (frule subg_subset [of "grp G H" "H1"])
  apply (simp add:nmlSubgTr0)
  apply (frule_tac a1 = y in l_coset_in_subg [THEN sym, of "G" "H" "H1"],
                                    assumption+) 
  apply (simp add:grp_def) apply assumption
  apply simp
 apply (frule_tac a1 = y in r_coset_in_subg [THEN sym, of "G" "H" "H1"],
                                    assumption+) 
  apply (simp add:grp_def) apply assumption
  apply simp      
apply (frule_tac a = y and h = xa and x = y in r_cosTr8 [of "G" "H1"], assumption+)
 apply (simp add:subg_subset1) apply assumption+
 apply (thin_tac "l_coset G y H1 = r_coset G H1 y")
 apply (subst r_coset_def) apply (simp add:CollectI) 
 apply (frule subg_one_closed [of "G" "H1"], assumption+)
 apply (frule_tac h = y in subg_subset1 [of "G" "H"], assumption+)
 apply (frule_tac a = y in l_one [of "G"], assumption+) apply blast
 apply (frule sym) apply (thin_tac "y H1\<^sub>G = H1\<^sub>G y") apply simp
 apply (frule_tac a = y in l_coset_sub [of "G" "H \<inter> K1" "H1"]) 
 apply (simp add:inter_subgs) apply simp+
 apply (rule subsetD, assumption+) 

 apply (simp add:settOp_def [of "G" "H \<inter> K1" "H1"])
 apply auto
 apply (frule_tac a = xa in l_coset_sub [of "G" "H \<inter> K1" "H1"])
 apply (simp add:inter_subgs) apply simp+
 apply (frule subggrp [of "G" "H"], assumption+)
 apply (frule_tac a = xa in NSubgLREq [of "grp G H" "H1"], assumption+)
 apply (simp add:grp_def)
 apply (frule subg_subset [of "grp G H" "H1"])
  apply (simp add:nmlSubgTr0)
  apply (frule_tac a = xa in l_coset_in_subg [of "G" "H" "H1"], assumption+) 
  apply (simp add:grp_def) apply assumption
  apply simp
 apply (frule_tac a1 = xa in l_coset_in_subg [THEN sym, of "G" "H" "H1"],
                                    assumption+) 
  apply (simp add:grp_def) apply assumption
  apply simp      
apply (frule_tac a = xa and h = y in l_cosTr8 [of "G" "H1"], assumption+)
 apply (simp add:subg_subset1) apply assumption+
 apply (thin_tac "l_coset G xa H1 = r_coset (grp G H) H1 xa")
 apply (frule_tac a = xa in l_coset_sub [of "G" "H \<inter> K1" "H1"]) 
 apply (simp add:inter_subgs) apply assumption+ apply simp
  apply (frule_tac a1 = xa in l_coset_in_subg [THEN sym, of "G" "H" "H1"],
                                    assumption+) 
  apply (simp add:grp_def) apply assumption
  apply simp
 apply (frule_tac a1 = xa in r_coset_in_subg [THEN sym, of "G" "H" "H1"],
                                    assumption+) 
  apply (simp add:grp_def) apply assumption
  apply simp
 apply (frule_tac a = xa in r_coset_sub [of "G" "H \<inter> K1" "H1"]) 
 apply (simp add:inter_subgs) apply simp+
 apply (rule subsetD, assumption+) 
done

lemma ZassenhausTr1_1: "\<lbrakk> group G; H \<guillemotleft> G; H1 \<guillemotleft> G; K \<guillemotleft> G; K1 \<guillemotleft> G;
   H1 \<lhd> grp G H; K1 \<lhd> grp G K \<rbrakk> \<Longrightarrow> H1 \<bullet>\<^sub>G (H \<inter> K1) \<guillemotleft> G "
apply (frule ZassenhausTr1 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule inter_subgs [of "G" "H" "K1"], assumption+)
apply (simp add:subgsubg)
done

end
