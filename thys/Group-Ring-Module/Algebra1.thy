(**            Algebra1  
                               author Hidetsune Kobayashi
                               Department of Mathematics
                               Nihon University
                               hikoba@math.cst.nihon-u.ac.jp
                               May 3, 2004.

 chapter 1. preliminaries.
   section 1.   natural number and Integers
   section 2.   sets
   section 3.   functions
   section 4.   Nsets, set of natural numbers
   section 3'.  Lower bounded set of integers
   section 5.   cardinality of sets 
 chapter 2. Ordered Set
   section 1.   Basic Concepts of Ordered Sets
   section 2.   Pre, (predecessors)
   section 3.   transfinite induction  **)
  
theory Algebra1 = Main + FuncSet:

chapter "0. Preliminaries"

(* Some of the lemmas of this section are proved in src/HOL/Integ
   of Isabelle version 2003. *) 

section "1. Natural number and Integers"

lemma add_both:"(a::nat) = b \<Longrightarrow> a + c = b + c"
 apply simp
done

lemma add_bothl:"a = b \<Longrightarrow> c + a = c + b"
apply simp
done

lemma diff_Suc:"(n::nat) \<le> m \<Longrightarrow> m - n + Suc 0 = Suc m - n"
 apply auto
 apply (rule Suc_diff_le [THEN sym], assumption+)
done

lemma less_convert:"\<lbrakk> a = b; c < b \<rbrakk> \<Longrightarrow> c < a"
apply auto
done

lemma diff_Suc_pos:"0 < a - Suc 0 \<Longrightarrow>  0 < a"
apply simp
done  

lemma minus_SucSuc:"a - Suc (Suc 0) = a - Suc 0 - Suc 0" 
apply simp
done

lemma Suc_Suc_Tr:"Suc (Suc 0) \<le> n \<Longrightarrow> Suc (n - Suc (Suc 0)) = n - Suc 0"
apply (simp add:Suc_diff_le [THEN sym, of "Suc (Suc 0)" "n"])
done

lemma Suc_Suc_less:"Suc 0 < a \<Longrightarrow> Suc (a - Suc (Suc 0)) < a"
apply (subst minus_SucSuc)
apply (subgoal_tac "0 < a - Suc 0")
apply (subst Suc_pred, assumption+) 
apply simp+
done

lemma non_zero_int:" (n::int) \<noteq> 0 \<Longrightarrow> 0 < n \<or> n < 0"
apply (subgoal_tac "n < 0 \<or> n = 0 \<or> 0 < n") apply simp
apply (thin_tac "n \<noteq> 0") apply blast
apply (rule zless_linear)
done

lemma not_zle:"(\<not> (n::int) \<le> m) =  (m < n)"
apply auto
done

lemma not_zless:"(\<not> (n::int) < m) = (m \<le> n)"
apply auto
done

lemma zle_imp_zless_or_eq:"(n::int) \<le> m \<Longrightarrow> n < m \<or> n = m"
apply (subgoal_tac "n < m \<or> n = m \<or> m < n")
apply (simp add:not_zless[THEN sym])
apply (rule zless_linear[of "n" "m"])
done

lemma zminus_zadd_cancel:" - z + (z + w) = (w::int)"
apply simp
done

lemma int_neq_iff:"((w::int) \<noteq> z) = (w < z) \<or> (z < w)"
apply auto
done

lemma zless_imp_zle:"(z::int) < z' \<Longrightarrow> z \<le> z'"
apply simp
done 

lemma zdiff:"z - (w::int) = z + (- w)"
apply simp
done
 
lemma int_mult_mono:"\<lbrakk> i < j; (0::int) < k \<rbrakk> \<Longrightarrow> k * i < k * j"
apply (frule zmult_zless_mono2_lemma [of "i" "j" "nat k"])
apply simp apply simp
done

lemma int_mult_le:"\<lbrakk>i \<le> j; (0::int) \<le> k\<rbrakk> \<Longrightarrow> k * i \<le> k * j"
apply (simp add:order_le_less)
 apply (case_tac "i < j")
  apply (case_tac "0 < k") 
  apply (simp add:order_le_less) apply (simp add:int_mult_mono)
 apply (simp add:order_le_less) apply simp
done

lemma int_mult_le1:"\<lbrakk>i \<le> j; (0::int) \<le> k\<rbrakk> \<Longrightarrow> i * k \<le> j * k"
apply (simp add:zmult_commute[of _ "k"])
apply (simp add:int_mult_le)
done

lemma zmult_zminus_right:"(w::int) * (- z) = - (w * z)"
apply (insert zadd_zmult_distrib2[of "w" "z" "-z"]) 
apply simp
done

lemma zmult_zle_mono1_neg:"\<lbrakk>(i::int) \<le> j; k \<le> 0\<rbrakk> \<Longrightarrow> j * k \<le> i * k"
apply (subgoal_tac "0 \<le> - k") prefer 2 apply simp
apply (frule int_mult_le [of "i" "j" "- k"], assumption+)
apply (simp add:zmult_commute)
done 

lemma zle:"((z::int) \<le> w) = (\<not> (w < z))" 
apply auto
done

lemma zmult_pos_mono:"\<lbrakk> (0::int) < w; w * z \<le> w * z'\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (rule contrapos_pp, simp+) 
apply (subgoal_tac "\<not> (z < z' \<or> z = z')") prefer 2 apply simp
 apply (thin_tac "\<not> z \<le> z'") apply simp
apply (subgoal_tac "z < z' \<or> z = z' \<or> z' < z") apply simp
prefer 2 apply (thin_tac "\<not> z < z' \<and> z \<noteq> z'") apply (simp add:zless_linear)
apply (frule int_mult_mono[of "z'" "z" "w"], assumption+)
apply (simp add:zle)
done

lemma zmult_pos_mono_r:"\<lbrakk> (0::int) < w; z * w \<le> z' * w\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (simp add:zmult_commute)
apply (rule zmult_pos_mono, assumption+)
done

lemma zadd_zle_mono:"\<lbrakk>w' \<le> w; z' \<le> (z::int)\<rbrakk> \<Longrightarrow> w' + z' \<le> w + z" 
apply simp
done

lemma zmult_neg:"\<lbrakk>i < (0::int); j < 0\<rbrakk> \<Longrightarrow> 0 < i * j"
apply (insert zmult_zle_mono1_neg[of "i" "0" "j"])
 apply (simp add:zle_imp_zless_or_eq)
 apply (frule zle_imp_zless_or_eq[of "0" "i * j"])
 apply (case_tac "0 = i * j") apply simp
 apply (thin_tac "0 \<le> i * j") 
 apply simp
done

lemma mult_pos_iff:"\<lbrakk>(0::int) < i; 0 \<le> i * j \<rbrakk> \<Longrightarrow> 0 \<le> j" 
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "j < 0 \<or> j = 0 \<or> 0 < j")
 apply (simp add:order_le_less)
 apply (frule int_mult_mono[of "j" "0" "i"], assumption+)  apply simp
 apply (simp add:zless_linear)
done

lemma zmult_eq:"\<lbrakk>(0::int) < w; z = z'\<rbrakk> \<Longrightarrow> w * z = w * z'"
apply simp
done

lemma int_nat_minus:"0 < (n::int) \<Longrightarrow> nat (n - 1) = (nat n) - 1"
apply (subgoal_tac "0 \<le> (1::int)")
apply (subgoal_tac "1 \<le> n") 
apply (frule_tac z' = 1 and z = n in nat_diff_distrib)
 apply (frule_tac w1 = 0 and z1 = n in add1_zle_eq [THEN sym])
 apply (subgoal_tac "nat (1::int) = (1::nat)") apply simp
 apply simp 
 apply (subgoal_tac "0 + 1 \<le> n") apply simp 
 apply (simp add:add1_zle_eq[THEN sym, of "0" "n"])
 apply simp
done

lemma int_nat_add:"\<lbrakk>0 < (n::int); 0 < (m::int)\<rbrakk> \<Longrightarrow> (nat (n - 1)) + (nat (m - 1)) + (Suc 0) = nat (n + m - 1)"
apply (subgoal_tac "nat (n - 1) + (nat (m - 1)) = (nat n - 1) + (nat m - 1)")
prefer 2 apply (simp add:int_nat_minus)
apply (simp del:add_Suc_right)
 apply (subst add_assoc)
 apply simp
 apply (thin_tac "nat (n - (1\<Colon>int)) + nat (m - (1\<Colon>int)) =
       nat n - Suc (0\<Colon>nat) + (nat m - Suc (0\<Colon>nat))")
 apply (simp add:int_nat_minus)
 apply (simp add:nat_add_distrib)
 apply (subgoal_tac "Suc 0 \<le> nat n")
 apply (simp add:diff_add_assoc2[THEN sym, of "0" "nat n" "nat m"])
 apply (subgoal_tac "0 < nat n") apply (thin_tac "0 < n") 
 prefer 2 apply simp apply (thin_tac "0 < m")
 apply (simp add:Suc_leI)
done

lemma int_equation:"(x::int) = y + z \<Longrightarrow> x - y = z"
apply simp
done

lemma int_pos_mult_monor:"\<lbrakk> 0 < (n::int); 0 \<le> n * m \<rbrakk> \<Longrightarrow> 0 \<le> m" 
 apply (rule mult_pos_iff, assumption+)
done

lemma int_pos_mult_monol:"\<lbrakk> 0 < (m::int); 0 \<le> n * m \<rbrakk> \<Longrightarrow> 0 \<le> n" 
 apply (rule int_pos_mult_monor, assumption+)
 apply (simp add:zmult_commute)
done

lemma zmult_eq:"\<lbrakk>(0::int) < w; z = z'\<rbrakk> \<Longrightarrow> w * z = w * z'"
apply simp
done 

lemma zmult_eq_r:"\<lbrakk>(0::int) < w; w * z = w * z'\<rbrakk> \<Longrightarrow> z = z'"
apply simp
done 

lemma zdiv_positive:"\<lbrakk>(0::int) \<le> a; 0 < b\<rbrakk> \<Longrightarrow> 0 \<le> a div b"
apply (frule_tac a = 0 and a' = a and b = b in zdiv_mono1, assumption+)
apply simp
done 

lemma zmult_pos_mono:"\<lbrakk> (0::int) < w; w * z \<le> w * z'\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (rule contrapos_pp, simp+) 
apply (subgoal_tac "\<not> (z < z' \<or> z = z')") prefer 2 apply simp
 apply (thin_tac "\<not> z \<le> z'") apply simp
apply (subgoal_tac "z < z' \<or> z = z' \<or> z' < z") apply simp
prefer 2 apply (thin_tac "\<not> z < z' \<and> z \<noteq> z'") apply (simp add:zless_linear)
apply (frule int_mult_mono[of "z'" "z" "w"], assumption+)
apply (simp add:zle)
done 

section "2. Sets"

(* Preliminary properties of the set are proved here. Some of them are 
 already proved by L. Paulson and others. *)

lemma inEx:"x \<in> A \<Longrightarrow> \<exists>y\<in>A. y = x"
apply simp
done

lemma nonempty_ex:"A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A"
 apply blast
done

lemma ex_nonempty:"\<exists>x. x \<in> A \<Longrightarrow> A \<noteq> {}"
 apply blast
done

lemma nonempty: "x \<in> A \<Longrightarrow> A \<noteq> {}"
 apply blast
done

lemma sets_not_eq:"\<lbrakk>A \<noteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> \<exists>a\<in>A. a \<notin> B"
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "A \<subseteq> B")
apply (frule equalityI[of "A" "B"], assumption+)
apply simp
apply (rule subsetI) apply simp
done

lemma nonempty_int: "A \<inter> B \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A \<inter> B "
 apply (rule nonempty_ex [of "A \<inter> B"], assumption+)
done

lemma elem_some:"x \<in> A \<Longrightarrow> \<exists>y\<in>A. x = y"
 apply simp
done

lemma eq_elem_in: "\<lbrakk> a \<in> A; a = b \<rbrakk> \<Longrightarrow> b \<in> A"
 apply simp
done

lemma eq_set_inc: "\<lbrakk> a \<in> A; A = B \<rbrakk> \<Longrightarrow> a \<in> B"
 apply simp
done

lemma int_subsets: "\<lbrakk> A1 \<subseteq> A; B1 \<subseteq> B \<rbrakk> \<Longrightarrow> A1 \<inter> B1 \<subseteq> A \<inter> B"
apply (rule subsetI)
 apply (simp add:subsetD)
done

lemma sub_Un1:"B \<subseteq>  B \<union> C" 
apply (rule subsetI)
 apply simp
done

lemma sub_Un2:"C \<subseteq>  B \<union> C" 
apply (rule subsetI)
 apply simp
done

lemma subset_contr:"\<lbrakk> A \<subset> B; B \<subseteq> A \<rbrakk> \<Longrightarrow> False"
apply (simp add:psubset_def)
 apply blast
done

lemma psubset_contr:"\<lbrakk> A \<subset> B; B \<subset> A \<rbrakk> \<Longrightarrow> False"
apply (simp add:psubset_def)
 apply blast
done

lemma not_subseteq:" \<not> A \<subseteq> B \<Longrightarrow> \<exists>a \<in> A. a \<notin> B" 
apply (simp add:subset_def)
done

lemma in_un1:"\<lbrakk> x \<in> A \<union> B; x \<notin> B \<rbrakk> \<Longrightarrow> x \<in> A"
apply simp
done

lemma in_un2:"\<lbrakk> x \<in> A \<union> B; x \<notin> A \<rbrakk> \<Longrightarrow> x \<in> B"
apply simp
done

lemma diff_disj:"x \<notin> A \<Longrightarrow> A - {x} = A" 
apply auto
done

lemma nonempty_some:"A \<noteq> {} \<Longrightarrow> (SOME x. x \<in> A) \<in> A" 
apply (frule nonempty_ex[of "A"])
apply (subst someI2_ex, simp+)
done

subsection "a short notes for proof steps" 

lemma conj_1:"P \<and> Q \<Longrightarrow> P"
 apply simp
done

lemma conj_2:"P \<and> Q \<Longrightarrow> Q"
apply simp
done

section "3. Functions"

constdefs
   cmp::"['b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> ('a \<Rightarrow> 'c)"
   "cmp g f == \<lambda>x. g (f x)"

   idmap :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a)"   
    "idmap A == \<lambda>x\<in>A. x" 

   constmap::"['a set, 'b set] \<Rightarrow> ('a \<Rightarrow>'b)"
   "constmap A B == \<lambda>x\<in>A. SOME y. y \<in> B" 

   invfun :: "['a set, 'b set, 'a \<Rightarrow> 'b] \<Rightarrow> ('b \<Rightarrow> 'a)"     
    "invfun A B (f :: 'a \<Rightarrow> 'b) == \<lambda>y\<in>B. \<some> x. (x \<in> A \<and> f x = y)"

lemma eq_fun:"\<lbrakk> f \<in> A \<rightarrow> B; f = g \<rbrakk> \<Longrightarrow> g \<in> A \<rightarrow> B"
 apply simp
done

lemma cmp_fun:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C \<rbrakk> \<Longrightarrow> cmp g f \<in> A \<rightarrow> C"
apply (simp add:Pi_def)
apply (rule allI) apply (rule impI)
apply (simp add:cmp_def)
done

lemma restrict_fun_eq:"\<forall>x\<in>A. f x = g x \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
 apply (simp add:expand_fun_eq)
done

lemma funcset_mem: "\<lbrakk>f \<in> A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
apply (simp add: Pi_def)
done

lemma funcset_mem1:"\<lbrakk>\<forall>l\<in>A. f l \<in> B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
apply simp
done

lemma restrict_in_funcset: "\<forall>x\<in> A. f x \<in> B \<Longrightarrow> 
                                     (\<lambda>x\<in>A. f x)\<in> A \<rightarrow> B"
apply (simp add:Pi_def restrict_def)
done

lemma funcset_eq:"\<lbrakk> f \<in> extensional A; g \<in> extensional A; \<forall>x\<in>A. f x = g x \<rbrakk> \<Longrightarrow>  f = g"
apply (simp add:extensionalityI)
done

lemma restriction_of_domain:"\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> 
  restrict f A1 \<in> A1 \<rightarrow> B"
apply (simp add:Pi_def [of "A1" _])
 apply (rule allI) apply (rule impI)
 apply (frule subsetD, assumption+)
 apply (simp add:funcset_mem)
done

lemma restrict_restrict:"\<lbrakk> restrict f A \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow>
      restrict (restrict f A) A1 = restrict f A1"
apply (rule funcset_eq[of _ "A1"])
 apply (simp add:restrict_def extensional_def)
 apply (simp add:restrict_def extensional_def)
apply (rule ballI) apply simp
 apply (simp add:subsetD)
done
 
lemma restr_restr_eq:"\<lbrakk> restrict f A \<in> A \<rightarrow> B; restrict f A = restrict g A;
A1 \<subseteq> A \<rbrakk> \<Longrightarrow> restrict f A1 = restrict g A1"
 apply (subst restrict_restrict[THEN sym, of "f" "A" "B" "A1"], assumption+)
 apply (simp add:restrict_restrict[THEN sym, of "g" "A" "B" "A1"])
done

lemma funcTr:"\<lbrakk> f \<in> A \<rightarrow> B; g \<in> A \<rightarrow> B; f = g; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
apply simp
done 

lemma funcTr1:"\<lbrakk>f = g; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
apply simp
done

lemma restrictfun_im:"\<lbrakk> (restrict f A) \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow>
       (restrict f A) ` A1 = f ` A1"
apply (subgoal_tac "\<forall>x\<in>A1. x \<in> A")
apply (simp add:image_def)
apply (rule ballI) apply (simp add:subsetD)
done

lemma mem_in_image:"\<lbrakk> f \<in> A \<rightarrow> B; a \<in> A\<rbrakk> \<Longrightarrow> f a \<in> f ` A "
apply (simp add:image_def)
 apply blast
done

lemma mem_in_image1:"\<lbrakk> \<forall>l\<in>A. f l \<in> B; a \<in> A\<rbrakk> \<Longrightarrow> f a \<in> f ` A "
apply simp
done

lemma elem_in_image2: "\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A; x \<in> A1\<rbrakk> \<Longrightarrow> f x \<in> f` A1"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"A1 \<subseteq> A" and p3:"x \<in> A1"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:image_def)
 apply auto
 done
qed

lemma funcs_nonempty:"\<lbrakk> A \<noteq> {}; B \<noteq> {} \<rbrakk> \<Longrightarrow> (A \<rightarrow> B) \<noteq> {}"
apply (subgoal_tac "constmap A B \<in> A \<rightarrow> B") apply (simp add:nonempty)
apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:constmap_def)
 apply (frule nonempty_ex[of "B"])
 apply (rule someI2_ex) apply assumption+
done

lemma idmap_funcs: "idmap A \<in> A \<rightarrow> A"
proof -
 show ?thesis
 apply (simp add:Pi_def restrict_def idmap_def)
 done
qed

lemma l_idmap_comp: "\<lbrakk>f \<in> extensional A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> compose A (idmap B) f = f"
proof -
 assume p1: "f \<in> extensional A" and p2: "f \<in> A \<rightarrow> B"
 have q1:"\<forall>x. compose A (idmap B) f x = f x"
  proof -
  from p1 and p2 show ?thesis
  apply (simp add:compose_def)
  apply (rule allI)
  apply (rule conjI)
  apply (rule impI) 
  apply (simp add:idmap_def) apply (simp add:funcset_mem)
  apply (simp add:extensional_def)
  done
  qed
 from q1 show ?thesis
 apply (simp add:ext)
 done
qed
 
lemma r_idmap_comp: "\<lbrakk>f \<in> extensional A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> compose A f (idmap A) = f"
proof -
 assume p1: "f \<in> extensional A" and p2: "f \<in> A \<rightarrow> B"
 have al:"\<forall>x. compose A f (idmap A) x = f x"
  proof -
  from p1 and p2 show ?thesis
  apply (simp add:idmap_def compose_def extensional_def)
  done
  qed
 from al show ?thesis
 apply (simp add:ext)
 done
qed
 
lemma extend_fun: "\<lbrakk> f \<in> A \<rightarrow> B; B \<subseteq> B1 \<rbrakk> \<Longrightarrow> f \<in> A \<rightarrow> B1"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"B \<subseteq> B1"
 from p1 and p2 show ?thesis
 apply (simp add:Pi_def restrict_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:subsetD)
 done
qed 

lemma restrict_fun: "\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> restrict f A1 \<in> A1 \<rightarrow> B"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"A1 \<subseteq> A"
 from p1 and p2 show ?thesis 
 apply (simp add:Pi_def restrict_def)
 apply (rule allI) apply (rule impI) 
 apply (simp add:subsetD)
 done
qed
 
lemma set_of_hom: "\<forall>x \<in> A. f x \<in> B \<Longrightarrow> restrict f A \<in> A \<rightarrow> B"
proof -
 assume p1:"\<forall>x\<in>A. f x \<in> B"
 from p1 show ?thesis
 apply (simp add:Pi_def restrict_def)
 done
qed

lemma composition : "\<lbrakk> f \<in> A \<rightarrow>  B; g \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> (compose A g f) \<in> A \<rightarrow>  C"
proof -
 assume p1:"f \<in> A \<rightarrow>  B" and p2:"g \<in> B \<rightarrow> C"
 from p1 and p2 show ?thesis
 apply (simp add:Pi_def restrict_def compose_def)
 done  
qed

lemma comp_assoc:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; h \<in> C \<rightarrow> D \<rbrakk> \<Longrightarrow>
     compose A h (compose A g f) = compose A (compose B h g) f" 
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"g \<in> B \<rightarrow> C" and p3:" h \<in> C \<rightarrow> D"  
 have al:"\<forall>x.  compose A h (compose A g f) x = compose A (compose B h g) f x"
 proof -
  from p1 and p2 and p3 show ?thesis
  apply (simp add:compose_def funcset_mem)
  done
  qed
 from al show ?thesis
 apply (simp add:ext)
 done
qed

lemma restrictfun_inj: "\<lbrakk> inj_on f A; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> inj_on (restrict f A1) A1"
proof -
 assume p1:"inj_on f A" and p2:"A1 \<subseteq> A"
 from p1 and p2 show ?thesis
 apply (simp add:inj_on_def) 
 apply auto
 done
qed

lemma injective:"\<lbrakk> inj_on f A; x \<in> A; y \<in> A; x \<noteq> y \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
proof -
 assume p1:"inj_on f A" and p2:"x \<in> A" and p3:"y \<in> A" and p4:"x \<noteq> y"
 from p1 and p2 and p3 and p4 show ?thesis
 apply auto
 apply (simp add:inj_on_def)
 done
qed

lemma bivar_fun: "\<lbrakk> f \<in> A \<rightarrow> (B \<rightarrow> C); a \<in> A \<rbrakk> \<Longrightarrow> f a \<in> B \<rightarrow> C"
proof -
 assume p1:"f \<in> A \<rightarrow> B \<rightarrow> C" and p2:"a \<in> A"
 from p1 and p2 show ?thesis
 apply (simp add:funcset_mem)
 done
qed

lemma bivar_fun_mem: "\<lbrakk> f \<in> A \<rightarrow> (B \<rightarrow> C); a \<in> A; b \<in> B \<rbrakk> \<Longrightarrow> f a b \<in> C"
proof -
 assume p1:" f \<in> A \<rightarrow> (B \<rightarrow> C)" and p2:"a \<in> A" and p3:" b \<in> B"
  have q1:"f a \<in> B \<rightarrow> C"
  apply (rule funcset_mem, assumption+) done
 from q1 and p3 show ?thesis
 apply (simp add:funcset_mem)
 done
qed

lemma bivar_func_test:"\<forall>a\<in>A. \<forall>b\<in>B. f a b \<in> C \<Longrightarrow> f \<in> A \<rightarrow> B \<rightarrow> C"
apply (simp add:Pi_def)
done

lemma bivar_func_eq:"\<lbrakk>\<forall>a\<in>A. \<forall>b\<in>B. f a b = g a b \<rbrakk> \<Longrightarrow>
                         (\<lambda>x\<in>A. \<lambda>y\<in>B. f x y) =  (\<lambda>x\<in>A. \<lambda>y\<in>B. g x y)"
apply (subgoal_tac "\<forall>x\<in>A. (\<lambda>y\<in>B. f x y) = (\<lambda>y\<in>B. g x y)")
apply (rule funcset_eq [of _ "A"]) 
 apply (simp add:extensional_def restrict_def)
 apply (simp add:extensional_def restrict_def)
 apply (rule ballI)
 apply simp
apply (rule ballI)
 apply (rule funcset_eq [of _ "B"]) 
 apply (simp add:restrict_def extensional_def)
 apply (simp add:restrict_def extensional_def)
apply (rule ballI) apply simp
done
 
lemma univar_func_test: "\<forall>x \<in> A. f x \<in> B \<Longrightarrow> f \<in> A \<rightarrow> B"
proof -
  assume p1:"\<forall>x \<in> A. f x \<in> B"
  from prems show ?thesis
 apply (simp add:Pi_def)
 done
qed

lemma set_image: "\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A; A2 \<subseteq> A \<rbrakk> \<Longrightarrow> 
            f`(A1 \<inter> A2) \<subseteq> (f` A1) \<inter> (f` A2)"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"A1 \<subseteq> A" and p3:"A2 \<subseteq> A"
 from p1 and p2 and p3 show ?thesis
 apply (simp add: image_def) 
 apply auto
 done
qed

lemma image_sub: "\<lbrakk>f \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> (f`A1) \<subseteq> B"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"A1 \<subseteq> A"
 from p1 and p2 show ?thesis
 apply (simp add:image_def)
 apply auto 
 apply (frule subsetD, assumption+)
 apply (simp add:funcset_mem)
 done
qed

lemma im_set_mono: "\<lbrakk>f \<in>A \<rightarrow> B; A1 \<subseteq> A2; A2 \<subseteq> A \<rbrakk> \<Longrightarrow> (f ` A1) \<subseteq> (f ` A2)"
proof -
 assume p1:"f \<in>A \<rightarrow> B" and p2:"A1 \<subseteq> A2" and p3:"A2 \<subseteq> A"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:image_def)
 apply auto
 done
qed

lemma im_set_un:"\<lbrakk> f\<in>A \<rightarrow> B; A1 \<subseteq> A; A2 \<subseteq> A \<rbrakk> \<Longrightarrow> 
             f`(A1 \<union> A2) = (f`A1) \<union> (f`A2)"
proof -
 assume p1:"f\<in>A \<rightarrow> B" and p2:"A1 \<subseteq> A" and p3:"A2 \<subseteq> A"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:image_def)
 apply auto
 done
qed

lemma im_set_un1:"\<lbrakk>\<forall>l\<in>A. f l \<in> B; A = A1 \<union> A2\<rbrakk> \<Longrightarrow> 
                                f `(A1 \<union> A2) = f `(A1) \<union> f `(A2)" 
proof -
 assume p1:"\<forall>l\<in>A. f l \<in> B" and p2:"A = A1 \<union> A2"
 from p1 and p2 have q1:"f `(A1 \<union> A2) \<subseteq> f `(A1) \<union> f `(A2)"
  apply (simp add:image_def) apply (rule subsetI) apply (simp add:CollectI)
  apply blast done
 from p1 and p2 have q2:"f `(A1) \<union> f `(A2) \<subseteq> f `(A1 \<union> A2)"
  apply (simp add:image_def) apply (rule subsetI) apply (simp add:CollectI)
  apply blast done
 from q1 and q2 show ?thesis
 apply (rule equalityI)
 done
qed

constdefs
 invim::"['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> 'a set"
  "invim f A B == {x. x\<in>A \<and> f x \<in> B}"

lemma invim: "\<lbrakk> f:A \<rightarrow> B; B1 \<subseteq> B \<rbrakk> \<Longrightarrow> invim f A B1 \<subseteq> A"
proof -
 assume p1:"f:A \<rightarrow> B" and p2:"B1 \<subseteq> B"
 from p1 and p2 show ?thesis
 apply (simp add:invim_def)
 apply auto
 done
qed

lemma setim_cmpfn: "\<lbrakk> f:A \<rightarrow> B; g:B \<rightarrow> C; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> 
               (compose A g f)` A1 = g`(f` A1)"
proof -
 assume p1:"f:A \<rightarrow> B" and p2:"g:B \<rightarrow> C" and p3:"A1 \<subseteq> A"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:image_def compose_def)
 apply auto
 done
qed

constdefs
 surj_to ::"['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"
  "surj_to f A B == f`A = B"

lemma surj_to_test:"\<lbrakk> f \<in> A \<rightarrow> B; \<forall>b\<in>B. \<exists>a\<in>A. f a = b \<rbrakk> \<Longrightarrow>
                                                  surj_to f A B" 
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"\<forall>b\<in>B. \<exists>a\<in>A. f a = b"
 from p1 and p2 show ?thesis
 apply (simp add:surj_to_def image_def)
 apply auto
 apply (simp add:funcset_mem)
 done
qed

lemma surj_to_el:"\<lbrakk> f \<in> A \<rightarrow> B; surj_to f A B \<rbrakk> \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. f a = b"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"surj_to f A B"
 from p1 and p2 show ?thesis
 apply (simp add:surj_to_def image_def)
 apply auto
 done
qed

lemma surj_to_el1:"\<lbrakk> f \<in> A \<rightarrow> B; surj_to f A B; b\<in>B\<rbrakk> \<Longrightarrow> \<exists>a\<in>A. f a = b"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"surj_to f A B" and p3:" b\<in>B"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:surj_to_el)
 done
qed

lemma compose_surj: "\<lbrakk>f:A \<rightarrow> B; surj_to f A B; g : B \<rightarrow> C; surj_to g B C \<rbrakk> 
                         \<Longrightarrow> surj_to (compose A g f) A C " 
proof -
 assume p1:"f:A \<rightarrow> B" and p2:"surj_to f A B" and p3:"g : B \<rightarrow> C" and
  p4:"surj_to g B C"
 from p1 and p2 and p3 and p4 show ?thesis
 apply (simp add:surj_to_def compose_def image_def)
 apply auto 
 done
qed

lemma cmp_surj: "\<lbrakk>f:A \<rightarrow> B; surj_to f A B; g : B \<rightarrow> C; surj_to g B C \<rbrakk> 
                         \<Longrightarrow> surj_to (cmp g f) A C " 
apply (rule surj_to_test)
apply (simp add:cmp_fun) 
apply (rule ballI)
apply (simp add:surj_to_def [of "g"]) apply (frule sym) 
 apply (thin_tac "g ` B = C")  apply simp apply (simp add:image_def)
 apply (simp add:cmp_def)
 apply auto
apply (simp add:surj_to_def) apply (frule sym)  
 apply (thin_tac " f ` A = B") apply (simp add:image_def)
 apply auto
done

lemma inj_onTr0:"\<lbrakk> f \<in> A \<rightarrow> B; x \<in> A; y \<in> A; inj_on f A; f x = f y\<rbrakk> \<Longrightarrow> x = y"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"x \<in> A" and p3:"y \<in> A" and p4:"inj_on f A" 
 and p5:"f x = f y"
 from p1 and p2 and p3 and p4 and p5 show ?thesis
 apply (simp add:inj_on_def)
 done
qed

lemma inj_onTr1:"\<lbrakk>inj_on f A; x \<in> A; y \<in> A; f x = f y\<rbrakk>  \<Longrightarrow> x = y"
apply (simp add:inj_on_def)
done

lemma inj_onTr2:"\<lbrakk>inj_on f A; x \<in> A; y \<in> A; f x \<noteq> f y\<rbrakk>  \<Longrightarrow> x \<noteq> y"
apply (rule contrapos_pp, simp+)
done  (* premis inj_on can be changed to some condition indicating f to be
         a function *)


lemma comp_inj: "\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; g \<in> B \<rightarrow> C; inj_on g B \<rbrakk> 
              \<Longrightarrow> inj_on (compose A g f) A "
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"inj_on f A" and p3:"g \<in> B \<rightarrow> C" and 
 p4:"inj_on g B"
 from p1 and p2 and p3 and p4 show ?thesis
 apply (simp add:inj_on_def [of "compose A g f"])
 apply (rule ballI)+ apply (rule impI)
 apply (rule inj_onTr0 [of "f" "A" "B"], assumption+)
 apply (frule funcset_mem [of "f" "A" "B" _], assumption+)
 apply (rotate_tac -3)
 apply (frule funcset_mem [of "f" "A" "B" _], assumption+)
 apply (rule inj_onTr0 [of "g" "B" "C" _], assumption+)
 apply (simp add:compose_def)
 done
qed

lemma cmp_inj_1: "\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; g \<in> B \<rightarrow> C; inj_on g B \<rbrakk> 
              \<Longrightarrow> inj_on (cmp g f) A "
apply (simp add:inj_on_def [of "cmp g f"])
apply (rule ballI)+ apply (rule impI)
apply (simp add:cmp_def)
apply (frule_tac x = x in funcset_mem [of "f" "A" "B"], assumption+)
apply (frule_tac x = y in funcset_mem [of "f" "A" "B"], assumption+)
apply (frule_tac x = "f x" and y = "f y" in inj_onTr1 [of "g" "B"],
                       assumption+)
apply (rule_tac x = x and y = y in inj_onTr1 [of "f" "A"], assumption+)
done

lemma cmp_inj_2: "\<lbrakk>\<forall>l\<in>A. f l \<in> B; inj_on f A; \<forall>k\<in>B. g k \<in> C; inj_on g B \<rbrakk> 
              \<Longrightarrow> inj_on (cmp g f) A "
apply (simp add:inj_on_def [of "cmp g f"])
apply (rule ballI)+ apply (rule impI)
apply (simp add:cmp_def)
apply (frule_tac x = x in funcset_mem1 [of "A" "f" "B"], assumption+)
apply (frule_tac x = y in funcset_mem1 [of "A" "f" "B"], assumption+)
apply (frule_tac x = "f x" and y = "f y" in inj_onTr1 [of "g" "B"],
                       assumption+)
apply (rule_tac x = x and y = y in inj_onTr1 [of "f" "A"], assumption+)
done

lemma invfun_mem:"\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B; b \<in> B \<rbrakk> 
                      \<Longrightarrow>  (invfun A B f) b \<in> A"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"inj_on f A" and p3:"surj_to f A B" and p4:"b \<in> B"
 from p1 and p2 and p3 and p4 show ?thesis
 apply (simp add:invfun_def)
 apply (simp add:surj_to_def image_def) apply (frule sym)
 apply (thin_tac "{y. \<exists>x\<in>A. y = f x} = B") apply simp
 apply (thin_tac "B = {y. \<exists>x\<in>A. y = f x}") apply auto
 apply (rule someI2_ex)
 apply blast apply simp
 done
qed

lemma inv_func:"\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow>  (invfun A B f) \<in> B \<rightarrow> A"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"inj_on f A" and p3:"surj_to f A B"
 from p1 and p2 and p3 show ?thesis 
 apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
 apply (rule invfun_mem) apply (rule funcsetI)
 apply simp+
 done
qed


lemma invfun_r:"\<lbrakk> f\<in>A \<rightarrow> B; inj_on f A; surj_to f A B; b \<in> B \<rbrakk> 
                      \<Longrightarrow> f ((invfun A B f) b) = b"
proof -
 assume p1:"f\<in>A \<rightarrow> B" and p2:"inj_on f A" and p3:"surj_to f A B" and p4:"b \<in> B"
 from p1 and p2 and p3 and p4 show ?thesis
 apply (simp add:invfun_def)
 apply (rule someI2_ex)
 apply (simp add:surj_to_def image_def)
 apply auto
 done
qed

lemma invfun_l:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B; a \<in> A\<rbrakk> 
                      \<Longrightarrow> (invfun A B f) (f a) = a"
apply (simp add:invfun_def Pi_def restrict_def)
apply (rule someI2_ex) apply auto
apply (simp add:inj_on_def)
done

lemma invfun_inj:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow>  inj_on (invfun A B f) B"
proof -
 assume p1:"f \<in> A \<rightarrow> B" and p2:"inj_on f A" and p3:"surj_to f A B"   
 from p1 and p2 and p3 show ?thesis
 apply (simp add:inj_on_def [of "invfun A B f" "B"] )
 apply auto
 apply (frule_tac b = y in invfun_r [of "f" "A" "B"], assumption+)
 apply (frule_tac b = x in invfun_r [of "f" "A" "B"], assumption+)
 apply simp
 done
qed
     
lemma invfun_surj:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow>  surj_to (invfun A B f) B A "
apply (simp add:surj_to_def [of "invfun A B f" "B" "A"] image_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply auto
apply (simp add:invfun_mem)
apply (frule funcset_mem [of "f" "A" "B"], assumption+)
 apply (frule_tac t = x in invfun_l [of "f" "A" "B", THEN sym], assumption+)
 apply auto
done

constdefs
  bij_to :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"
   "bij_to f A B  == (surj_to f A B) \<and> (inj_on f A)"

lemma bij_invfun:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B\<rbrakk> \<Longrightarrow>
                              bij_to (invfun A B f) B A"
apply (simp add:bij_to_def)
apply (simp add:invfun_inj invfun_surj)
done

lemma l_inv_invfun:"\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow> compose A (invfun A B f) f = idmap A"
apply (rule ext) 
 apply (simp add:compose_def idmap_def)
apply (rule impI)
apply (simp add:invfun_l)
done

section "4.Nsets"

 (* NSet is the set of natural numbers, and "Nset n" is the set of 
natural numbers from 0 through n  *)

constdefs
   NSet :: "nat set"
    "NSet == {i. 0 \<le> i}"

   Nset :: "nat \<Rightarrow> (nat) set"
   "Nset n == {i. i \<le> n }"
   
   nset:: "[nat, nat] \<Rightarrow> (nat) set"
    "nset i j == {k. i \<le> k \<and> k \<le> j}"

   slide :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    "slide i j == i + j"
   sliden :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    "sliden i j == j - i"

  jointfun :: "[nat, nat \<Rightarrow> 'a, nat, nat \<Rightarrow> 'a] \<Rightarrow> (nat \<Rightarrow> 'a)"
   "(jointfun n f m g) ==\<lambda> i. if i \<le> n then f i else  g ((sliden (Suc n)) i)"


   skip::"nat \<Rightarrow> (nat \<Rightarrow> nat)"
    "skip i  == \<lambda>x\<in>NSet. (if i = 0 then Suc x else 
                  (if x \<in> Nset (i - Suc 0) then x  else Suc x))" 

lemma nat_pos:"0 \<le> (l::nat)"
apply simp
done

lemma Suc_pos:"Suc k \<le> r \<Longrightarrow> 0 < r"
apply simp
done

lemma nat_pos2:"(k::nat) < r \<Longrightarrow> 0 < r"
apply simp
done

lemma eq_le_not:"\<lbrakk>(a::nat) \<le> b; \<not> a < b \<rbrakk> \<Longrightarrow> a = b"
apply auto
done

lemma im_of_constmap:"(constmap (Nset 0) {a}) ` (Nset 0) = {a}" 
apply (simp add:constmap_def Nset_def)
done

lemma noteq_le_less:"\<lbrakk> m \<le> (n::nat); m \<noteq> n \<rbrakk> \<Longrightarrow> m < n"
apply auto
done

lemma self_le:"(n::nat) \<le> n"
apply simp
done

lemma n_less_Suc:"(n::nat) < Suc n"
apply simp
done

lemma less_diff_pos:"i < (n::nat) \<Longrightarrow> 0 < n - i"
apply auto
done

lemma less_diff_Suc:"i < (n::nat) \<Longrightarrow> n - (Suc i) = (n - i) - (Suc 0)"
apply auto
done

lemma less_Suc_le1:"x < n \<Longrightarrow> Suc x \<le> n"
apply simp
done

lemma Suc_less_le:"x < Suc n \<Longrightarrow> x \<le> n"
apply auto
done

lemma less_le_diff:"x < n \<Longrightarrow> x \<le> n - Suc 0"
apply (frule_tac x = x and n = n in less_Suc_le1)
apply (frule diff_le_mono [of "Suc x" "n" "Suc 0"])
apply simp
done

lemma less_pre_n:"0 < n \<Longrightarrow> n - Suc 0 < n"
apply simp
done

lemma Nset_1:"{i. i \<le> Suc 0} = {0, Suc 0}"
proof -
 show ?thesis
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (frule le_imp_less_or_eq)
 apply (thin_tac "x \<le> Suc 0")
 apply (case_tac "x < Suc 0")
  apply simp
  apply (simp add:le_def)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (case_tac "x = 0") apply simp
 apply blast
 done
qed

lemma Nset_2:"{i, j} = {j, i}"
apply auto
done

lemma Nset_nonempty:"Nset n \<noteq> {}"
apply (subgoal_tac "0 \<in> Nset n")
apply (simp add:nonempty)
apply (simp add:Nset_def)
done

lemma Nset_le:"x \<in> Nset n \<Longrightarrow> x \<le> n"
apply (simp add:Nset_def)
done

lemma n_in_Nsetn:"n \<in> Nset n"
apply (simp add:Nset_def)
done

lemma Nset_pre:"\<lbrakk> x \<in> Nset (Suc n); x \<noteq> Suc n \<rbrakk> \<Longrightarrow> x \<in> Nset n"
apply (simp add:Nset_def)
done

lemma mem_of_Nset:"x \<le> (n::nat) \<Longrightarrow> x \<in> Nset n"
apply (simp add:Nset_def)
done

lemma less_mem_of_Nset:"x < (n::nat) \<Longrightarrow> x \<in> Nset n"
apply (frule less_imp_le [of "x" "n"])
apply (rule mem_of_Nset, assumption+)
done

lemma Nset_nset:"Nset (Suc (n + m)) = Nset n \<union> nset (Suc n) (Suc (n + m))"
proof -
 have q1:" n \<le> Suc (n + m)" apply simp done
 have q2:"Nset (Suc (n + m)) \<subseteq> Nset n \<union> nset (Suc n) (Suc (n + m))"
  apply (simp add:Nset_def nset_def)
  apply (rule subsetI) apply (simp add:CollectI)
  apply (case_tac "x \<le> n") apply simp apply simp done
 from q1 have q3:"Nset n \<union> nset (Suc n) (Suc (n + m)) \<subseteq> Nset (Suc (n + m))"
  apply (simp add:Nset_def nset_def)
  apply (rule subsetI) apply (simp add:CollectI)
  apply (case_tac "x \<le> n") apply simp apply simp done
from q2 and q3 show ?thesis
 apply (rule equalityI)
 done
qed

lemma Nset_nset_1:"\<lbrakk>0 < n; i < n\<rbrakk> \<Longrightarrow> Nset n = Nset i \<union> nset (Suc i) n"
apply auto
 apply (simp add:Nset_def nset_def)
 apply (simp add:Nset_def)
 apply (simp add:Nset_def nset_def)
done

lemma skip_mem:"l \<in> Nset n \<Longrightarrow> (skip i l) \<in> Nset (Suc n)"
apply (case_tac "i = 0")
 apply (simp add:skip_def)
 apply (simp add:Nset_def NSet_def)+
apply (simp add:skip_def) 
apply (simp add:NSet_def)
done

lemma skip_im_Tr0:"x \<in> Nset n \<Longrightarrow> skip 0 x = Suc x"
apply (simp add:skip_def NSet_def)
done

lemma skip_im_Tr0_1:"0 < y \<Longrightarrow> skip 0 (y - Suc 0) = y"
apply (simp add:skip_def NSet_def)
done

lemma skip_im_Tr1:"\<lbrakk> i \<in> Nset (Suc n); 0 < i; x \<le> i - Suc 0 \<rbrakk> \<Longrightarrow>
      skip i x = x"
 apply (simp add:skip_def Nset_def NSet_def)
done

lemma skip_im_Tr2:"\<lbrakk> 0 < i; i \<in> Nset (Suc n); i \<le> x\<rbrakk> \<Longrightarrow>
      skip i x = Suc x"
proof -
 assume p1:" 0 < i" and p2:"i \<in> Nset (Suc n)" and p3:"i \<le> x"
 have q1:"i - Suc 0 < i" 
 proof -
 from p1 show ?thesis apply simp done
 qed
 from p1 and p2 and p3 and q1 show ?thesis
 apply (simp add:skip_def Nset_def NSet_def)
 done
qed

lemma skip_im_Tr3:"x \<in> Nset n \<Longrightarrow> skip (Suc n) x = x"
apply (simp add:skip_def Nset_def NSet_def)
done

lemma skip_im_Tr4:"\<lbrakk>x \<le> Suc n; 0 < x\<rbrakk> \<Longrightarrow> x - Suc 0 \<le> n"
 apply (simp add:Suc_le_mono [of "x - Suc 0" "n", THEN sym])
done
   
lemma skip_fun_im:"i \<in> Nset (Suc n) \<Longrightarrow> (skip i) `(Nset n) = (Nset (Suc n) - {i})"
proof -
 assume p1:"i \<in> Nset (Suc n)"
 have q1:"skip i ` Nset n \<subseteq> Nset (Suc n) - {i}" 
 apply (rule subsetI)
 apply (simp add:skip_def image_def)
 apply (case_tac "i = 0")
 apply auto
 apply (simp add:Nset_def)
 apply (simp add:NSet_def)+
 apply (simp add:Nset_def)
 apply (simp add:NSet_def)
 apply (simp add:Nset_def)
 apply (simp add:NSet_def)
 apply (simp add:NSet_def Nset_def)
 apply (case_tac "xa \<le> i - Suc 0")  
 apply simp 
 apply (frule diff_Suc_less [of "i" "0"])
 apply (simp add:le_def)
 apply (rotate_tac -1) apply simp
 apply auto done
 have q2:"Nset (Suc n) - {i} \<subseteq>  skip i ` Nset n"
 proof -
  from p1 show ?thesis
  apply (simp add:image_def)
  apply (rule subsetI) apply (simp add:CollectI)
  apply (erule conjE)
  apply (case_tac "i = 0") apply simp
  apply (frule_tac t = x in skip_im_Tr0_1 [THEN sym])
  apply (simp add:Nset_def)
  apply (frule_tac  x = x and n = n in skip_im_Tr4, assumption+) 
  apply blast
  apply simp
  apply (case_tac "x \<le> i - Suc 0")
  apply (frule_tac i1 = i and n1 = n and t = x in skip_im_Tr1[THEN sym], 
   assumption+)
  apply (case_tac "i = Suc n")
  apply (simp add:Nset_def)
  apply (frule le_imp_less_or_eq) apply (thin_tac "x \<le> Suc n") apply simp
  apply (frule Suc_less_le)
  apply blast
  apply (simp add:Nset_def) 
  apply (frule le_imp_less_or_eq) apply (thin_tac "i \<le> Suc n") apply simp
  apply (frule_tac i = x in le_less_trans [of _ "i - Suc 0" "i"])
  apply simp
  apply (frule_tac i = x in less_trans [of _ "i" "Suc n"], assumption+)
  apply (frule_tac x = x and n = n in Suc_less_le)
  apply blast
  apply (simp add:le_def)
  apply (frule_tac  x = "i - Suc 0" and n = x in less_Suc_le1)
  apply simp
  apply (frule not_sym) apply (thin_tac "x \<noteq> i")
  apply (frule le_imp_less_or_eq) apply (thin_tac "i \<le> x")
  apply simp
  apply (frule less_trans [of "0" "i" _]) apply simp
  apply (frule_tac n = x and x = i in less_le_diff)
  apply (frule_tac i1 = i and n1 = n and x1 = "x - Suc 0" in 
               skip_im_Tr2[THEN sym],  assumption+)
  apply simp
  apply (simp add:Nset_def)
  apply (frule_tac m = x and n = "Suc n" and l = "Suc 0" in diff_le_mono)
  apply simp
  apply blast
  done
  qed
 from q1 and q2 show ?thesis
 apply (rule equalityI)
done
qed
 

lemma skip_id:"l < i \<Longrightarrow> skip i l = l"
proof -
 assume p1:"l < i" 
 have q1:"0 \<le> l" apply simp done
 have q2:"0 < i" 
 proof -
  from q1 and p1 show ?thesis
  apply (rule le_less_trans) 
  done
  qed
 from p1 and q2 show ?thesis
 apply (unfold skip_def)
 apply (frule_tac  n = i and x = l in less_le_diff)
 apply (thin_tac "l < i")
 apply (simp add:Nset_def NSet_def)
 done
qed

lemma le_imp_add_int:" i \<le> j \<Longrightarrow> \<exists> k \<in> NSet. j = i + k"
proof -
 assume p1:"i \<le> j"
 have q1: "j = j + 0" apply simp done
 from p1 and q1 show ?thesis
 apply (case_tac "i = j")
 apply (simp add:Nset_def) apply (simp add:NSet_def)
 apply (frule le_imp_less_or_eq) apply (thin_tac "i \<le> j")
 apply simp
 apply (insert less_imp_add_positive [of "i" "j"])
 apply auto
(* thm less_imp_le [of "0" _] *)
 apply (simp add:NSet_def)
 done
qed

lemma jointfun_hom0:"\<lbrakk> f \<in> Nset n \<rightarrow> A; g \<in> Nset m \<rightarrow> B \<rbrakk> \<Longrightarrow> 
        (jointfun n f m g) \<in> Nset (Suc (n + m)) \<rightarrow>  A \<union> B"
apply (simp add: Pi_def [of "Nset (Suc (n + m))"])
apply (rule allI) apply (rule impI)
apply (simp add:jointfun_def)
apply (rule conjI)
apply (rule impI) apply (simp add:Nset_def funcset_mem)
apply (rule impI) apply (simp add:le_def) 
apply (frule_tac x = n and n = x in less_Suc_le1)
 apply (thin_tac "n < x")
 apply (simp add:Nset_def)
 apply (frule_tac m = x and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
 apply simp
 apply (simp add:sliden_def funcset_mem)
done

lemma slide_hom:"i \<le> j \<Longrightarrow> (slide i) \<in> Nset (j - i) \<rightarrow> nset i j"
apply (simp add:Pi_def restrict_def)
apply (rule allI) apply (rule impI)
   apply (simp add:Nset_def)
   apply (simp add:slide_def)
apply (simp add:nset_def)
   apply (frule add_le_mono1 [of  _ "j - i" "i"])
apply simp
done

lemma slide_mem:"\<lbrakk> i \<le> j; l \<in> Nset (j - i)\<rbrakk> \<Longrightarrow> slide i l \<in> nset i j"
apply (frule slide_hom)
apply (rule funcset_mem, assumption+)
done


lemma slide_hom_1:"(slide i) \<in> NSet \<rightarrow> NSet"
apply (simp add:Pi_def restrict_def)
apply (rule allI) apply (rule impI)
apply (simp add:NSet_def)
done

lemma slide_iM:"(slide i) ` NSet = {k. i \<le> k}"
apply (simp add:image_def slide_def)
apply (rule equalityI)
 apply (rule subsetI) 
 apply (simp add:NSet_def)   
 apply auto
 apply (rule le_imp_add_int)
 apply assumption
done


lemma jointfun_hom:"\<lbrakk> f \<in> Nset n \<rightarrow> A; g \<in> Nset m \<rightarrow> B \<rbrakk> \<Longrightarrow> 
                   (jointfun n f m g) \<in> Nset (Suc (n + m)) \<rightarrow> A \<union> B"
proof -
 assume p1:"f \<in> Nset n \<rightarrow> A" and p2:"g \<in> Nset m \<rightarrow> B"
 from p1 and p2 show ?thesis
  apply (simp add:Pi_def restrict_def jointfun_def)
  apply (rule allI) 
  apply (rule conjI)
  apply (rule impI) apply (rule impI)
  apply (simp add:Nset_def)
  apply (rule impI)+
  apply (simp add:le_def) apply (simp add:Nset_def) 
  apply (frule_tac x = n and n = x in less_Suc_le1)
  apply (frule_tac m = x and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
  apply simp
  apply (simp add:sliden_def)
 done
qed

lemma im_jointfunTr1:"(jointfun n f m g) ` (Nset n) = f ` (Nset n)"
proof -
  have q1:"(jointfun n f m g) ` (Nset n) \<subseteq>  f ` (Nset n)" 
  apply (simp add:image_def) apply (rule subsetI) apply (simp add:CollectI)
  apply auto
  apply (simp add:jointfun_def Nset_def)
  apply blast done
  have q2:"f ` (Nset n) \<subseteq> (jointfun n f m g) ` (Nset n)"
  apply (simp add:image_def) apply (rule subsetI) apply (simp add:CollectI)
  apply auto
  apply (simp add:Nset_def jointfun_def)
  apply blast
  done
 from q1 and q2 show ?thesis
 apply (rule equalityI)
 done
qed
 
lemma im_jointfunTr2:"(jointfun n f m g) ` (nset (Suc n) (Suc (n + m))) = g ` (Nset m)"
proof -
 have q1:"(jointfun n f m g) ` (nset (Suc n) (Suc (n + m))) \<subseteq>  g ` (Nset m)"
  apply (simp add:image_def)
  apply (rule subsetI) apply (simp add:CollectI)
  apply (simp add:nset_def Nset_def) apply auto
  apply (frule_tac m = xa and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
  apply simp
  apply (simp add:jointfun_def sliden_def)
  apply blast done
  have q2:"g ` (Nset m) \<subseteq> (jointfun n f m g) ` (nset (Suc n) (Suc (n + m)))"
  apply (simp add:image_def) apply (rule subsetI) 
  apply (simp add:CollectI) 
  apply (subgoal_tac "\<forall>xa\<in>Nset m. x = g xa \<longrightarrow> ( \<exists>xa\<in>nset (Suc n) (Suc (n + m)). x = jointfun n f m g xa)")
  apply blast apply (thin_tac "\<exists>xa\<in>Nset m. x = g xa")
  apply (rule ballI) apply (rule impI)
  apply (rename_tac x y) 
  apply (subgoal_tac "Suc n \<le> Suc (n + m)") prefer 2 apply simp
  apply (subgoal_tac "y \<in> Nset (Suc (n + m) - (Suc n))") prefer 2 apply simp
  apply (frule_tac l = y in slide_mem [of "Suc n" "Suc (n + m)"], assumption+)
  apply (thin_tac "Suc n \<le> Suc (n + m)")
  apply (thin_tac "y \<in> Nset (Suc (n + m) - (Suc n))")
  apply (subgoal_tac "x = jointfun n f m g (slide (Suc n) y)")
  apply blast
  
  apply (simp add:nset_def) apply (erule conjE)
  apply (simp add:jointfun_def sliden_def slide_def)
  done
  from q1 and q2 show ?thesis
  apply (rule equalityI)
 done
qed
   
lemma im_jointfun:"\<lbrakk>f\<in>Nset n \<rightarrow> A; g \<in> Nset m \<rightarrow> B\<rbrakk> \<Longrightarrow> (jointfun n f m g) `(Nset (Suc (n + m))) = f `(Nset n) \<union> g `(Nset m)"
proof -
 assume p1:"f \<in> Nset n \<rightarrow> A" and p2:"g \<in> Nset m \<rightarrow>  B"
 have q1:"Nset (Suc (n + m)) = Nset n \<union> nset (Suc n) (Suc (n + m))"
  apply (rule Nset_nset [of "n" "m"]) done
 from p1 and p2 have q2:"\<forall>l\<in>Nset (Suc (n + m)). (jointfun n f m g) l \<in> A \<union> B" 
  apply auto
  apply (case_tac "l \<le> n")
   apply (simp add:jointfun_def) apply (simp add:Nset_def funcset_mem)
 apply (simp add:le_def)
  apply (frule_tac x = n and n = l in less_Suc_le1) apply (thin_tac "n < l")
  apply (simp add:jointfun_def sliden_def)
  apply (simp add:Nset_def)
  apply (frule_tac m = l and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
  apply simp 
  apply (frule_tac x = "l - Suc n" in funcset_mem [of "g" "{i. i \<le> m}"])
  apply simp apply simp done 
 from p1 and p2 and q2 and q1 show ?thesis 
 apply simp
 apply (insert im_set_un1 [of "Nset (Suc (n + m))" "jointfun n f m g" "A \<union> B" 
 "Nset n" "nset (Suc n) (Suc (n + m))"])

 apply (simp add:im_jointfunTr1 im_jointfunTr2) 
 done
qed

lemma jointfun_surj:"\<lbrakk>f\<in>Nset n \<rightarrow> A; surj_to f (Nset n) A; g \<in> Nset m \<rightarrow> B; surj_to g (Nset m) B\<rbrakk> \<Longrightarrow> 
 surj_to (jointfun n f m g) (Nset (Suc (n + m))) (A \<union> B)"
proof -
 assume p1:"f\<in>Nset n \<rightarrow> A" and p2:"surj_to f (Nset n) A" and 
 p3:"g \<in> Nset m \<rightarrow> B" and p4:"surj_to g (Nset m) B"       
 from p1 and p2 and p3 and p4 show ?thesis
 apply (simp add:surj_to_def [of "jointfun n f m g"])
 apply (simp add:im_jointfun)
 apply (simp add:surj_to_def)
 done
qed

lemma Nset_un:"Nset (Suc n) = Nset n \<union> {Suc n}"
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:CollectI Nset_def) 
 apply auto
apply (simp add:Nset_def)+
done

lemma Nsetn_sub: "Nset n \<subseteq> Nset (Suc n)"
apply (rule subsetI)
apply (simp add:Nset_def)
done

lemma Nset_pre_sub:"(0::nat) < k \<Longrightarrow> Nset (k - Suc 0) \<subseteq> Nset k"
apply (rule subsetI)
apply (simp add:Nset_def)
apply (frule_tac i = x and j = "k - Suc 0" and k = k in le_less_trans)
 apply simp
 apply (simp add:less_imp_le)
done

lemma Nset_pre_un:"(0::nat) < k \<Longrightarrow> Nset k = Nset (k - Suc 0) \<union> {k}"
apply (insert Nset_un [of "k - Suc 0"])
apply simp
done

lemma Nsetn_sub_mem:" l \<in> Nset n \<Longrightarrow> l \<in> Nset (Suc n)"
apply (simp add:Nset_def)
done

lemma Nset_Suc:"Nset (Suc n) = insert (Suc n) (Nset n)"
apply (rule equalityI)
apply (rule subsetI)
apply (simp add:Nset_def)
apply auto
apply (simp add:Nset_def)+
done

lemma Nset_Suc_Suc:"Suc (Suc 0) \<le> n \<Longrightarrow>
        Nset (n - Suc (Suc 0)) = Nset n - {n - Suc 0, n}" 
apply (insert Nset_un [of "n - (Suc 0)"])
apply (insert Nset_un [of "n - Suc (Suc 0)"])
apply (subgoal_tac "Nset (Suc (n - Suc (Suc 0))) = Nset (n - Suc 0)")
apply simp
 apply (thin_tac "Nset n =
       insert n (insert (Suc (n - Suc (Suc 0))) (Nset (n - Suc (Suc 0))))")
 apply (thin_tac " Nset (n - Suc 0) =
       insert (Suc (n - Suc (Suc 0))) (Nset (n - Suc (Suc 0)))")
 apply (thin_tac "Nset (Suc (n - Suc (Suc 0))) =
       insert (Suc (n - Suc (Suc 0))) (Nset (n - Suc (Suc 0)))")
apply (simp add:Suc_Suc_Tr)
prefer 2 apply (simp add:Suc_Suc_Tr)
apply (rule equalityI)
prefer 2 apply (rule subsetI) apply simp
apply (rule subsetI) 
 apply (simp add:Nset_def)
 apply (rule conjI)
 apply (frule_tac i = x in add_le_mono [of _ "n - Suc (Suc 0)" "Suc 0" "Suc 0"]) apply simp
 apply (thin_tac "x \<le> n - Suc (Suc 0)")
 apply (simp del:add_Suc_right)
 apply (frule_tac i = x in add_le_mono [of _ "n - Suc (Suc 0)" "Suc (Suc 0)" 
 "Suc (Suc 0)"]) apply simp
 apply (thin_tac "x \<le> n - Suc (Suc 0)")
 apply (simp del:add_Suc_right)
done

lemma finite_Nset:"finite (Nset n)"
apply (induct_tac n)
 apply (simp add:Nset_def) 
 apply (subst Nset_Suc) 
 apply (simp add:InsertI)
done

section "3'. Lower bounded set of integers"

(* In this section. I prove that a lower bounded set of integers
  has the minimal element *)

constdefs
 Zset ::"int set"
 "Zset == {x. \<exists>(n::int). x = n}"

constdefs
 Zleast ::"int set \<Rightarrow> int"
 "Zleast A == THE a. (a \<in> A \<and> (\<forall>x\<in>A. a \<le> x))"

 LB::"[int set, int] \<Rightarrow> bool"
 "LB A n == \<forall>a\<in>A. n \<le> a"

lemma zle_linear1:"(m::int) < n \<or> n \<le> m"
apply (subgoal_tac "m < n \<or> n = m \<or> n < m")
apply (case_tac "m < n") apply simp apply simp
apply (subgoal_tac "m < n \<or> m = n \<or> n < m") 
apply blast
apply (simp add:zless_linear)
done

consts
 dec_seq::"[int set, int, nat] \<Rightarrow> int"

primrec
 dec_seq_0   : "dec_seq A a 0 = a"
 dec_seq_Suc : "dec_seq A a (Suc n) = (SOME b. ((b \<in> A) \<and> b < (dec_seq A a n)))"

lemma dec_seq_mem:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                        (dec_seq A a n) \<in> A"
apply (induct_tac n)
 apply simp apply simp  apply (simp add:not_zle)
apply (subgoal_tac "\<exists>x\<in>A. x < (dec_seq A a n)") prefer 2 apply blast
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. x < m)")
 apply (rule someI2_ex) apply blast
apply simp
done

lemma dec_seqn:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                       (dec_seq A a (Suc n)) < (dec_seq A a n)"
apply simp
 apply (frule dec_seq_mem [of "a" "A" "n"], assumption+)
 apply simp
 apply (simp add:not_zle)
 apply (subgoal_tac "\<exists>x\<in>A. x < (dec_seq A a n)") prefer 2 apply simp
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. x < m)")
apply (rule someI2_ex) apply blast
 apply simp
done

lemma dec_seqn1:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                       (dec_seq A a (Suc n)) \<le> (dec_seq A a n) - 1"
apply (frule dec_seqn [of "a" "A" "n"], assumption+)
 apply simp
done

lemma lbs_ex_ZleastTr:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                        (dec_seq A a n) \<le> (a - int(n))"
apply (induct_tac n)
 apply simp
apply (frule_tac n = n in dec_seqn1[of "a" "A"], assumption+)
 apply (subgoal_tac "dec_seq A a n - 1 \<le> a - (int n) - 1") prefer 2 
   apply simp apply (thin_tac "dec_seq A a n \<le> a - int n")
 apply (frule_tac i = "dec_seq A a (Suc n)" and j = "dec_seq A a n - 1" and
 k = "a - int n - 1" in zle_trans, assumption+)
 apply (thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))")
 apply (thin_tac "dec_seq A a (Suc n) \<le> dec_seq A a n - 1")
 apply (thin_tac "dec_seq A a n - 1 \<le> a - int n - 1")
apply (subgoal_tac "a - int n - 1 = a - int (Suc n)") apply simp
 apply (thin_tac "dec_seq A a (Suc n) \<le> a - int n - 1")
apply simp
done

lemma big_int_less:"a - int(nat(abs(a) + abs(N) + 1)) < N"
apply (simp add:zabs_def)
done

lemma lbs_ex_Zleast:"\<lbrakk>A \<noteq> {}; A \<subseteq> Zset; LB A n\<rbrakk> \<Longrightarrow> \<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x)"
apply (frule nonempty_ex[of "A"])
 apply (thin_tac "A \<noteq> {}")
 apply (subgoal_tac "\<forall>a. a \<in> A \<longrightarrow> (\<exists>!m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))")
 apply blast apply (thin_tac "\<exists>x. x \<in> A")
 apply (rule allI) apply (rule impI)
apply (rule ex_ex1I)
prefer 2
 apply (thin_tac "LB A n") apply (erule conjE)+
 apply (subgoal_tac "m \<le> y") prefer 2 apply simp
 apply (subgoal_tac "y \<le> m") prefer 2 apply simp
 apply (thin_tac "\<forall>x\<in>A. m \<le> x") apply (thin_tac "\<forall>x\<in>A. y \<le> x")
 apply simp
apply (rule contrapos_pp) apply simp 
 apply (frule_tac a = a and A = A and n = "nat(abs(a) + abs(n) + 1)" in lbs_ex_ZleastTr, assumption+)
 apply (subgoal_tac "a - int(nat(abs(a) + abs(n) + 1)) < n")
 prefer 2 apply (rule big_int_less)
 apply (frule_tac x = "dec_seq A a (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))" and y = "a - int (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))" and z = n in order_le_less_trans, assumption+)
 apply (frule_tac a = a and n = "nat (\<bar>a\<bar> + \<bar>n\<bar> + 1)" in dec_seq_mem [of _ "A"], assumption+)
 apply (thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))")
 apply (thin_tac "dec_seq A a (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))
           \<le> a - int (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))")
 apply (thin_tac "a - int (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1)) < n")
apply (simp add:LB_def)
 apply (subgoal_tac "n \<le> dec_seq A a (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))")
 apply (thin_tac "\<forall>a\<in>A. n \<le> a") apply (simp add:not_zle)
 apply blast
done 

lemma Zleast:"\<lbrakk>A \<noteq> {}; A \<subseteq> Zset; LB A n\<rbrakk> \<Longrightarrow> Zleast A \<in> A \<and>
               (\<forall>x\<in>A. (Zleast A) \<le> x)"
apply (frule lbs_ex_Zleast [of "A" "n"], assumption+)
 apply (simp add:Zleast_def)
 apply (rule theI')
 apply simp
done

section "5. cardinality of sets"

text {* cardinality is defined for the finite sets only *}

lemma card_eq:"A = B \<Longrightarrow> card A = card B"
proof -
 assume p1:"A = B"
 from p1 show ?thesis
 apply simp
 done
qed

lemma card0:"card {} = 0"
apply simp
done

lemma card_nonzero:"\<lbrakk>finite A; card A \<noteq> 0\<rbrakk> \<Longrightarrow> A \<noteq> {}"
apply (rule contrapos_pp, simp+)
done

lemma finite1:"finite {a}"
apply simp
done

lemma card1:"card {a} = 1"
apply simp
done

lemma nonempty_card_pos:"\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> 0 < card A"
apply (frule nonempty_ex [of "A"])
apply (subgoal_tac "\<forall>x. x \<in> A \<longrightarrow> 0 < card A")
apply blast apply (thin_tac "\<exists>x. x \<in> A")
apply (rule allI) apply (rule impI)
apply (subgoal_tac "{x} \<subseteq> A") 
apply (frule_tac B = A and A = "{x}" in card_mono, assumption+)
apply (simp add:card1)
apply simp
done
 

lemma card1_tr0:"\<lbrakk> finite A; card A = Suc 0; a \<in> A \<rbrakk> \<Longrightarrow> {a} = A"
proof -
 assume p1:" finite A" and p2:" card A = Suc 0" and p3:" a \<in> A"
 from p3 have q1: "{a} \<subseteq> A" apply simp done
 have q2:"card {a} = Suc 0" apply (simp add:card1) done
 from p2 and q2 have q3:"card A \<le> card {a}" apply simp done
  
 from p1 and q1 and q3 show ?thesis
 apply (rule card_seteq [of "A" "{a}"])
 done
qed

lemma card1_tr1:"(constmap (Nset 0) {x}) \<in> (Nset 0) \<rightarrow> {x} \<and>
                       surj_to (constmap (Nset 0) {x}) (Nset 0) {x}"
proof -
 show ?thesis
 apply (rule conjI)
 apply (simp add:constmap_def Nset_def Pi_def)
 apply (simp add:surj_to_def image_def Nset_def constmap_def)
 done
qed

lemma card1_Tr2:"\<lbrakk>finite A; card A = Suc 0\<rbrakk> \<Longrightarrow> 
                  \<exists>f. f \<in> Nset 0 \<rightarrow> A \<and> surj_to f (Nset 0) A"
proof -
 assume p1:"finite A" and p2:"card A = Suc 0"
 from p2 have q1:"card A \<noteq> 0" apply simp done
 from p1 and q1 have q2: "A \<noteq> {}"  apply (rule card_nonzero) done
 from q2 have q3: "\<exists>x. x \<in> A" apply (simp add:nonempty_ex) done
 from p1 and p2 and q3 have 
  q4:"(constmap (Nset 0) A) \<in> (Nset 0) \<rightarrow> A \<and> 
                       surj_to (constmap (Nset 0) A) (Nset 0) A"
  apply auto
  apply (frule_tac t = A and a1 = x in card1_tr0 [THEN sym], assumption+)
  apply simp  apply (simp add:card1_tr1)
  apply (frule_tac t = A and a1 = x in card1_tr0 [THEN sym], assumption+)
  apply simp  apply (simp add:card1_tr1) done
 from q4 show ?thesis
  apply auto
  done
qed
 
lemma card2:"\<lbrakk> finite A; a \<in> A; b \<in> A; a \<noteq> b \<rbrakk> \<Longrightarrow> Suc (Suc 0) \<le> card A"
proof -
  assume fin: "finite A" and a: "a \<in> A" and b: "b \<in> A" and ab:
"a \<noteq> b"
  have card_is_2: "card {a, b} = Suc (Suc 0)"
  proof -
    have "card {a} = 1" apply (simp add: card1) done
    have ba: "b \<notin> {a}" apply simp apply (rule not_sym) apply assumption done
    have card: "card (insert b {a}) = Suc (card {a})"
      apply (rule card_insert_disjoint)
      apply simp
      apply (rule ba) done
    from card and ab show ?thesis apply simp done
  qed
  from a and b have subset: "{a, b} \<subseteq> A" apply simp done
  from fin and subset have card_subset: "card {a, b} \<le> card A"
    apply (rule card_mono [of "A" "{a, b}"]) done
  from card_subset and card_is_2 show ?thesis apply simp done
qed

lemma card_Nset_Tr0:"Suc n \<notin> Nset n"
proof -
 show ?thesis
 apply (simp add:Nset_def) done
qed

lemma card_Nset_Tr1:"card (Nset n) = Suc n \<Longrightarrow> 
         card (insert (Suc n) (Nset n)) = Suc (Suc n)"
proof -
 assume p1:"card (Nset n) = Suc n"
 have q1:"finite (Nset n)" apply (simp add:finite_Nset) done
 have q2:"Suc n \<notin> Nset n" apply (simp add:card_Nset_Tr0) done
 from p1 and q1 and q2 show ?thesis
 apply (subst card_insert_disjoint)
 apply simp+
 done
qed

lemma card_Nset:" card (Nset n) = Suc n"
proof -
 show ?thesis
 apply (induct_tac n)
 apply (simp add:Nset_def)
 (* thm card_insert_disjoint *)
 apply (subst Nset_Suc)
 apply (simp add:card_Nset_Tr1)
 done
qed

lemma Nset2_prep1:"\<lbrakk>finite A; card A = Suc (Suc n) \<rbrakk> \<Longrightarrow> \<exists>x. x\<in>A" 
proof -
 assume p1:"finite A" and p2:"card A = Suc (Suc n)"
 from p2 have q1:"card A \<noteq> 0" apply simp done
 from q1 have q2:"A \<noteq> {}"  apply auto done
 from q2 show ?thesis apply auto
 done
qed

lemma ex_least_set:"\<lbrakk>A = {H. finite H \<and> P H}; H \<in> A\<rbrakk> \<Longrightarrow> \<exists>K \<in> A. (LEAST j. j \<in> (card ` A)) =  card K" 
(* proof by L. C. Paulson *)
apply (simp add:image_def)
apply (rule LeastI)
apply (rule_tac x = "H" in exI)
apply simp
done


lemma Nset2_prep2:"x \<in> A \<Longrightarrow> A - {x} \<union> {x} = A"
 apply auto
 done

lemma Nset2_finiteTr:"\<forall>A. (finite A \<and>(card A = Suc n) \<longrightarrow> (\<exists>f. f \<in> (Nset n) \<rightarrow> A \<and> surj_to f (Nset n) A))"
proof -
 show ?thesis
 apply (induct_tac n)
  apply (rule allI)  apply (rule impI) apply (erule conjE)
  apply (simp add:card1_Tr2)
  (* n *) 
 apply (rule allI) apply (rule impI)
  apply (erule conjE)
  apply (frule Nset2_prep1, assumption+)
  apply auto
  apply (frule_tac A = A and x = x in card_Diff_singleton, assumption+)
  apply simp 
  apply (frule_tac B = A and Ba = "{x}" in finite_Diff)
  apply (frule_tac  P = "finite (A - {x})" and Q = "card (A - {x}) = Suc n" in conjI, assumption+)
  apply (subgoal_tac "\<exists>f. f \<in> Nset n \<rightarrow> (A - {x}) \<and>surj_to f (Nset n) (A - {x})")
 prefer 2 apply (thin_tac "finite A") apply (thin_tac "card A = Suc (Suc n)")
  apply blast
  apply (thin_tac "\<forall>A. finite A \<and> card A = Suc n \<longrightarrow> (\<exists>f. f \<in> Nset n \<rightarrow> A \<and>surj_to f (Nset n) A)")
  apply auto
  apply (subgoal_tac "constmap (Nset 0) {x} \<in> Nset 0 \<rightarrow> {x} \<and>
                          surj_to (constmap (Nset 0) {x}) (Nset 0) {x}")
 prefer 2 apply (simp add:card1_tr1) apply (erule conjE)
  apply (frule_tac f = f and n = n and A = "A - {x}" and g = "constmap (Nset 0) {x}" 
 and m = 0 and B = "{x}" in jointfun_surj, assumption+)
  apply (frule_tac f = f and n = n and A = "A - {x}" and g = "constmap (Nset 0) {x}"
 and m = 0 and B = "{x}" in jointfun_hom0, assumption+) 
  apply (frule_tac x = x and A = A in Nset2_prep2) apply simp
  apply blast
 done
qed

lemma Nset2_finite:"\<lbrakk> finite A; card A = Suc n\<rbrakk> \<Longrightarrow>
                       \<exists>f. f \<in> Nset n \<rightarrow> A \<and> surj_to f (Nset n) A "
 apply (simp add:Nset2_finiteTr)
done

lemma Nset2finite_inj_tr0:"j \<in> Nset n \<Longrightarrow> card (Nset n - {j}) = n"
apply (insert finite_Nset [of "n"])
apply (subst card_Diff_singleton [of "Nset n" "j"], assumption+)
apply (subst card_Nset[of "n"]) apply simp
done

lemma Nset2finite_inj_tr1:"\<lbrakk> i \<in> Nset n; j \<in> Nset n; f i = f j; i \<noteq> j \<rbrakk> \<Longrightarrow> f ` (Nset n - {j}) = f ` (Nset n)"
apply (simp add:image_def)
 apply (rule equalityI) apply (rule subsetI) apply (simp add:CollectI)
 apply auto
 apply (case_tac "xa = j") apply (frule sym) apply (thin_tac "f i = f j")
 apply simp apply auto
done

lemma Nset2finite_inj:"\<lbrakk> finite A; card A = Suc n; surj_to f (Nset n) A \<rbrakk> \<Longrightarrow> 
        inj_on f (Nset n)"
apply (rule contrapos_pp)
 apply simp+
 apply (simp add:inj_on_def)
 apply auto
 apply (rename_tac i j)
 apply (frule_tac i = i and n = n and j = j and f = f in Nset2finite_inj_tr1, 
                                                           assumption+) 
 apply (subgoal_tac "f ` (Nset n - {j}) = f ` (Nset n)")
 apply (insert finite_Nset [of "n"])
 apply (frule_tac Ba = "{j}" in finite_Diff [of "Nset n" ])
 apply (frule_tac A = "Nset n - {j}" and f = f in card_image_le)
 apply simp
 apply (simp add:surj_to_def)
 apply (frule_tac j = j and n = n in Nset2finite_inj_tr0)
 apply simp
 apply (simp add:Nset2finite_inj_tr1)
done

lemma slide_surj:"i < j \<Longrightarrow> surj_to (slide i) (Nset (j - i)) (nset i j)"
proof -
 assume p1:"i < j"
 from p1 show ?thesis
  apply (simp add:surj_to_def image_def)
  apply auto
  apply (simp add:slide_def nset_def)
  apply (simp add:Nset_def)
  apply (frule_tac m = i and n = j in less_imp_le)
  apply (thin_tac "i < j")
  apply (frule add_le_mono [of _ "j - i" "i" "i"])
  apply simp+
 apply (simp add:nset_def Nset_def slide_def)
  apply (erule conjE)
  apply (frule_tac m = x and n = j and l = i in diff_le_mono)
  apply (subgoal_tac "x = slide i (x - i)") 
  apply auto
 apply (simp add:slide_def)
 done
qed

lemma slide_inj:"i < j \<Longrightarrow> inj_on (slide i) (Nset (j - i))"
apply (simp add:inj_on_def)
apply auto
apply (simp add:slide_def)
done

lemma card_nset:"i < (j :: nat) \<Longrightarrow> card (nset i j) = Suc (j - i)"

apply (insert finite_Nset [of "j - i"])
apply (frule slide_inj [of "i" "j"])
apply (frule card_image [of "Nset (j - i)" "slide i"], assumption+)
apply (simp add:card_Nset) 
apply (frule slide_surj [of "i" "j"]) 
apply (simp add:surj_to_def)
done

lemma sliden_hom:"\<lbrakk> i < j\<rbrakk> \<Longrightarrow> (sliden i) \<in> nset i j \<rightarrow>  Nset (j - i)"
apply (simp add:Pi_def)
apply (rule allI) apply (rule impI)
apply (simp add:sliden_def Nset_def)
apply (simp add:nset_def)
 apply (erule conjE)
 apply (simp add:diff_le_mono)
done

lemma slide_sliden:"(sliden i) (slide i k) = k"
apply (simp add:sliden_def slide_def)
done

lemma sliden_surj:"i < j \<Longrightarrow>  surj_to (sliden i) (nset i j) (Nset (j - i))"
proof -
 assume p1:"i < j"
 from p1 have q1:"sliden i \<in> (nset i j) \<rightarrow> Nset (j - i)"
  apply (simp add:sliden_hom) done
 from p1 and q1  have q2:"\<forall>b\<in>Nset (j - i). \<exists>a\<in>(nset i j). 
 sliden i a = b" 
 apply auto
 apply (subst slide_sliden [of "i", THEN sym])
 apply (insert slide_mem [of "i" "j"]) apply simp
 apply auto
 done
 from p1 and q1 and q2 show ?thesis 
 apply (simp add: surj_to_test [of "sliden i" "nset i j" "Nset (j - i)"])
 done
qed
 
lemma sliden_inj: "i < j \<Longrightarrow>  inj_on (sliden i) (nset i j)"
proof -
 assume p1:"i < j"
 from p1 show ?thesis
 apply (simp add:inj_on_def)
 apply (rule ballI)+
 apply (rule impI)
 apply (simp add:sliden_def)
 apply (simp add:nset_def)
 apply (erule conjE)+ 
 apply (subgoal_tac "(x - i = y - i) = (x = y)")
 apply blast
 apply (rule eq_diff_iff, assumption+)
 done
qed

constdefs
 transpos :: "[nat, nat] \<Rightarrow> (nat \<Rightarrow> nat)"
 "transpos i j  == \<lambda> k\<in>NSet. if k = i then j else if k = j then i else k" 

lemma transpos_id:"\<lbrakk> i \<in> Nset n; j \<in> Nset n; i \<noteq> j ; x \<in> Nset n - {i, j} \<rbrakk>
  \<Longrightarrow> transpos i j x = x"
proof -
 assume p1:"i \<in> Nset n" and p2:"j \<in> Nset n" and p3:" i \<noteq> j" and 
 p4:"x \<in> Nset n - {i, j}"
 from p1 and p2 and p3 and p4 show ?thesis
  apply (simp add:transpos_def)
  apply (subgoal_tac "x \<in> NSet")
  apply simp
  apply (simp add:NSet_def)
 done
qed

lemma transpos_id_1:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j; x \<in> Nset n;
 x \<noteq> i; x \<noteq> j \<rbrakk> \<Longrightarrow> transpos i j x = x" 
proof -
 assume p1:"i \<in> Nset n" and p2:"j \<in> Nset n" and p3:"i \<noteq> j" and p4:"x \<in> Nset n" and p5:"x \<noteq> i" and p6:"x \<noteq> j"
 from p1 and p2 and p3 and p4 and p5 and p6 show ?thesis
 apply (simp add:transpos_def NSet_def)
done
qed

lemma transpos_id_2:"\<lbrakk>i \<le>  n; j \<le> n; i \<noteq> j; x \<le> n;
 x \<noteq> i; x \<noteq> j \<rbrakk> \<Longrightarrow> transpos i j x = x" 
proof -
 assume p1:"i \<le>  n" and p2:"j \<le> n" and p3:"i \<noteq> j" and p4:"x \<le> n" and p5:" x \<noteq> i" and p6:"x \<noteq> j"
 from p1 and p2 and p4 have q1:"i \<in> Nset n \<and> j \<in> Nset n \<and> x \<in> Nset n"
  apply (simp add:Nset_def)  done
 from q1 and p3 and p5 and p6 show ?thesis
 apply auto
 apply (simp add:transpos_id_1)
 done
qed

lemma transpos_ij_1:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j \<rbrakk> \<Longrightarrow>
                        transpos i j i = j"
apply (simp add:transpos_def NSet_def)
done

lemma transpos_ij_2:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j \<rbrakk> \<Longrightarrow>
                        transpos i j j = i"
apply (simp add:transpos_def NSet_def)
done


lemma transpos_hom:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j\<rbrakk> \<Longrightarrow> 
                          (transpos i j)  \<in> Nset n \<rightarrow> Nset n" 
apply (simp add:Pi_def)
apply (rule allI)  apply (rule impI)
apply (case_tac "x = i")
 apply (simp add:transpos_def NSet_def)
 apply (case_tac "x = j")
 apply (simp add:transpos_def NSet_def)
 apply (subst transpos_id, assumption+)
 apply simp
apply assumption
done

lemma transpos_mem:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j; l \<in> Nset n\<rbrakk> \<Longrightarrow> 
                           transpos i j  l \<in> Nset n"
apply (frule transpos_hom [of "i" "n" "j"], assumption+)
apply (rule funcset_mem, assumption+)
done

lemma transpos_mem1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; l \<le> n\<rbrakk> \<Longrightarrow> 
                           transpos i j  l \<le>  n"
proof -
 assume p1:"i \<le> n" and p2:"j \<le> n" and p3:"i \<noteq> j" and p4:"l \<le> n"
 from p1 and p2 and p3 and p4 have q1: "i \<in> Nset n \<and> j \<in> Nset n \<and> l \<in> Nset n"
 apply (simp add:Nset_def) done
 from q1 and p3 show ?thesis
 apply auto
 apply (frule transpos_mem [of "i" "n" "j" "l"], assumption+)
 apply (simp add:Nset_def)
done
qed

lemma transpos_inj:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j\<rbrakk> 
                          \<Longrightarrow> inj_on (transpos i j) (Nset n)"
proof -
 assume p1:"i \<in> Nset n" and p2:"j \<in> Nset n" and p3:"i \<noteq> j"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:inj_on_def)
  apply (rule ballI)+
  apply (rule impI)
  apply (case_tac "x = i") 
  apply (case_tac "y = j")
  apply (simp add:transpos_def NSet_def) 
 
  apply (simp add:transpos_ij_1)
  apply (rule contrapos_pp, simp+)
  apply (frule_tac x = y in transpos_id [of "i" "n" "j"], assumption+)
  apply simp+

  apply (case_tac "x = j") apply simp
  apply (simp add:transpos_ij_2)
  apply (rule contrapos_pp, simp+)
  apply (frule_tac x = y in transpos_id [of "i" "n" "j"], assumption+)
  apply simp
  apply (rule contrapos_pp, simp+)
  apply (simp add:transpos_ij_1)

  apply simp
  apply (simp add:transpos_ij_1)
  apply (simp add:transpos_id_1) 

  apply (thin_tac "x = transpos i j y")
  apply (case_tac "y = i") apply (simp add:transpos_ij_1)
  apply (case_tac "y = j") apply (simp add:transpos_ij_2)
 
  apply (simp add:transpos_id_1)
 done
qed

lemma transpos_surjec:"\<lbrakk>i \<in> Nset n; j \<in> Nset n; i \<noteq> j\<rbrakk> 
                          \<Longrightarrow> surj_to (transpos i j) (Nset n) (Nset n)"
proof -
 assume p1:"i \<in> Nset n" and p2:"j \<in> Nset n" and p3:"i \<noteq> j"
 have q1:"finite (Nset n)" apply (simp add:finite_Nset) done
 from p1 and p2 and p3 and q1 show ?thesis
 apply (simp add:surj_to_def)
 apply (frule transpos_hom [of "i" "n" "j"], assumption+)
 apply (frule image_sub [of "transpos i j" "Nset n" "Nset n" "Nset n"])
 apply simp
 apply (frule transpos_inj [of "i" "n" "j"], assumption+)
 apply (frule card_image [of "Nset n" "transpos i j"], assumption+)
 apply (simp add:card_seteq)
 done
qed

lemma comp_transpos:"\<lbrakk> i \<le> n; j \<le> n; i \<noteq> j \<rbrakk> \<Longrightarrow> \<forall>k \<in> (Nset n). (compose (Nset n) (transpos i j) (transpos i j)) k = k"
proof -
 assume p1:"i \<le> n" and p2:"j \<le> n" and p3:"i \<noteq> j"
 from p1 and p2 and p3 show ?thesis
  apply (simp add:compose_def)
  apply (rule ballI)
  apply (case_tac "k = i") apply simp
  apply (subst transpos_ij_1, assumption+) 
  apply (simp add:Nset_def)+
  apply (rule transpos_ij_2) apply (simp add:Nset_def)+
  apply (case_tac "k = j") apply simp
  apply (subst transpos_ij_2) apply (simp add:Nset_def)+
  apply (rule transpos_ij_1) apply (simp add:Nset_def)+
  apply (subst transpos_id_1) apply (simp add:Nset_def)+
  apply (simp add:transpos_mem1)
  apply (simp add:transpos_id_2)+
 done
qed
 
lemma comp_transpos_1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; k \<in> Nset n\<rbrakk> \<Longrightarrow>
                           (transpos i j) ((transpos i j) k) = k"
apply (frule comp_transpos [of "i" "n" "j"], assumption+)
 apply (simp add:compose_def)
done

lemma cmp_transpos1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; k \<in> Nset n\<rbrakk> \<Longrightarrow> (cmp (transpos i j) (transpos i j)) k = k"
apply (simp add:cmp_def)
apply (simp add:comp_transpos_1)
done

lemma im_Nset_Suc:"insert (f (Suc n)) (f ` (Nset n)) = f ` (Nset (Suc n))"
apply (subgoal_tac "\<forall>j. j \<in> Nset n \<longrightarrow> j \<in> Nset (Suc n)")
apply (simp add:image_def)
 apply auto apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply blast
 apply (simp add:Nset_def) apply (subgoal_tac "xa \<noteq> Suc n") 
 apply (frule_tac x = xa and n = n in Nset_pre, assumption+)
 apply blast
apply (rule contrapos_pp, simp+)
apply (simp add:Nset_def)
done


lemma Nset_injTr0:"\<lbrakk> f \<in> Nset (Suc n) \<rightarrow> Nset (Suc n); inj_on f (Nset (Suc n)); f (Suc n) = Suc n \<rbrakk> \<Longrightarrow> f \<in> Nset n \<rightarrow> Nset n \<and> inj_on f (Nset n)"
proof -
 assume p1:"f \<in> Nset (Suc n) \<rightarrow> Nset (Suc n)" and p2:"inj_on f (Nset (Suc n))"
 and p3:"f (Suc n) = Suc n"
 have q1:"\<forall>l\<in>Nset n. l \<in> Nset (Suc n)" apply (simp add:Nset_def) done
 from p1 and p2 and p3 and q1 have q2:"f \<in> Nset n \<rightarrow> Nset n"
  apply (simp add:Pi_def)
  apply (rule allI) apply (rule impI)
  apply (subgoal_tac "f x \<in> Nset (Suc n)") prefer 2 apply blast
 apply (subgoal_tac "f x \<noteq> f (Suc n)")
 apply (rule Nset_pre, assumption+)apply simp
 apply (thin_tac "\<forall>x. x \<in> Nset (Suc n) \<longrightarrow> f x \<in> Nset (Suc n)")
 apply (thin_tac "f x \<in> Nset (Suc n)")
 apply (rule contrapos_pp, simp+) 
 apply (simp add:inj_on_def)
 apply (subgoal_tac "x = Suc n")
  apply (simp add:Nset_def)

 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "f x = Suc n")
 apply (subgoal_tac "f (Suc n) = f x") prefer 2 apply simp
 apply (thin_tac "f (Suc n) = Suc n") apply (thin_tac "Suc n = f x")
 apply (simp add:Nset_def) done

 from p1 and p2 and p3 and q1 and q2 show ?thesis
 apply simp
 apply (simp add:inj_on_def [of "f" "Nset n"])
 apply (rule ballI)+ apply (rule impI)
 apply (simp add:inj_on_def)
 done
qed
 
lemma inj_surj:"\<lbrakk>f \<in> Nset n \<rightarrow> Nset n; inj_on f (Nset n)\<rbrakk> \<Longrightarrow>
    f ` (Nset n) = Nset n"
proof -
 assume p1:"f \<in> Nset n \<rightarrow> Nset n" and p2:"inj_on f (Nset n)"
 from p1 and p2 have q1: "0 < Suc 0" apply simp done
 from p1 and p2 and q1 show ?thesis
 apply simp
 apply (frule image_sub [of "f" "Nset n" "Nset n" "Nset n"])
 apply simp+
 apply (insert finite_Nset [of "n"])
 apply (frule card_image [of "Nset n" "f"], assumption+)
 apply (simp add:card_seteq)
 done
qed

lemma Nset_pre_mem:"\<lbrakk> f: Nset (Suc n) \<rightarrow> Nset (Suc n); inj_on f (Nset (Suc n)); f (Suc n) = Suc n; k \<in> Nset n \<rbrakk> \<Longrightarrow> f k \<in> Nset n"
proof -
 assume p1:"f: Nset (Suc n) \<rightarrow> Nset (Suc n)" and p2:"inj_on f (Nset (Suc n))"
  and p3:"f (Suc n) = Suc n" and p4:" k \<in> Nset n" 
 have q1: "\<forall>l. l \<in> Nset n \<longrightarrow> l \<in> Nset (Suc n)" apply (simp add:Nset_def) done
 from p1 and p2 and p3 and p4 have q2: "f k \<noteq> Suc n"
 apply (simp add:inj_on_def)
 apply (subgoal_tac "k \<in> Nset (Suc n)") prefer 2 apply (simp add:Nset_def)
 apply (frule funcset_mem [of "f" "Nset (Suc n)" "Nset (Suc n)"], assumption+)
 apply (simp add:Nset_def)
 apply (rule contrapos_pp) apply simp+
 apply (subgoal_tac "f (Suc n) = f k")
 apply (subgoal_tac "Suc n = k")
 apply (simp add:Nset_def) apply (thin_tac " f (Suc n) = Suc n")
  apply (thin_tac "f k = Suc n")
 apply (simp add:inj_on_def) 
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (subgoal_tac "k \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def) apply (simp add:Nset_def)
 done
 from p1 and p2 and p2 and p3 and p4 and q1 and q2 show ?thesis
 apply simp
 apply (subgoal_tac "f k \<in> Nset (Suc n)") apply (rule Nset_pre, assumption+)
 apply (simp add:funcset_mem)
done
qed

lemma Nset_injTr1:"\<lbrakk> \<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n); inj_on f (Nset (Suc n)); f (Suc n) = Suc n \<rbrakk> \<Longrightarrow> inj_on f (Nset n)"
proof -
 assume p1:"\<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n)" and p2:"inj_on f (Nset (Suc n))" and p3:"f (Suc n) = Suc n"
 from p1 and p2 and p3 show ?thesis
 apply (simp add:inj_on_def)
  apply (rule ballI)+
  apply (rule impI)  
  apply (frule_tac l = x and n = n in  Nsetn_sub_mem) 
  apply (thin_tac "x \<in> Nset n")
  apply (frule_tac l = y and n = n in Nsetn_sub_mem)
  apply (thin_tac "y \<in> Nset n")
  apply blast
 done
qed

lemma Nset_injTr2:"\<lbrakk>\<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n); inj_on f (Nset (Suc n)); f (Suc n) = Suc n \<rbrakk> \<Longrightarrow> \<forall>l\<in>Nset n. f l \<in> Nset n"
apply (rule ballI)
apply (rule contrapos_pp, simp+)
apply (frule Nsetn_sub_mem)
apply (subgoal_tac "f l = f (Suc n)")
apply (frule_tac x = l in inj_onTr1 [of "f" "Nset (Suc n)" _ "Suc n"], 
                                                  assumption+)
 apply (simp add:Nset_def) apply assumption
apply (simp add:Nset_def) apply simp
apply (subgoal_tac "f l \<in> Nset (Suc n)")
 apply (thin_tac "\<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n)") 
 apply (thin_tac "inj_on f (Nset (Suc n))")
 apply (thin_tac "l \<in> Nset n") apply (thin_tac "l \<in> Nset (Suc n)")
apply (simp add:Nset_def)
apply (simp add:Nset_def)
done

lemma TR_inj_inj:"\<lbrakk>\<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n); inj_on f (Nset (Suc n));
i \<in> Nset (Suc n); j \<in> Nset (Suc n); i < j \<rbrakk> \<Longrightarrow> inj_on (compose (Nset (Suc n)) (transpos i j) f) (Nset (Suc n))"
proof -
 assume p1:"\<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n)" and p2:"inj_on f (Nset (Suc n))" and p3:"i \<in> Nset (Suc n)" and p4:"j \<in> Nset (Suc n)" and p5:"i < j"
 from p1 and p2 and p3 and p4 and p5 show ?thesis
  apply (unfold inj_on_def)
   apply (rule ballI)+ apply (rule impI)
   apply (subgoal_tac "f x = f y") apply (rotate_tac -1)
   apply (thin_tac "\<forall>l\<in>Nset (Suc n). f l \<in> Nset (Suc n)")
   apply simp
   apply (thin_tac "\<forall>x\<in>Nset (Suc n). \<forall>y\<in>Nset (Suc n). f x = f y \<longrightarrow> x = y")
   apply (frule_tac i = i and n = "Suc n" and j = j in transpos_inj, assumption+) apply simp
   apply (simp add:inj_on_def)
   apply (subgoal_tac "f x \<in> Nset (Suc n)")
   apply (subgoal_tac "f y \<in> Nset (Suc n)") 
   apply (simp add:compose_def)
   apply (simp add:Nset_def)+
  done
 qed

lemma enumeration:"\<lbrakk> f \<in> Nset n \<rightarrow> Nset m; inj_on f (Nset n) \<rbrakk> \<Longrightarrow> n \<le> m"
proof -
 assume p1:"f \<in> Nset n \<rightarrow> Nset m" and p2:"inj_on f (Nset n)" 
  from p1 have q1:"f ` (Nset n) \<subseteq> Nset m"
   apply (simp add:image_sub) done
  have q2:"finite (Nset n)" apply (simp add:finite_Nset) done
  have q3:"finite (Nset m)" apply (simp add:finite_Nset) done
  from p2 and q2 have q4: "card (f ` (Nset n)) = Suc n"
   apply (simp add: card_image [of "Nset n" "f"] card_Nset) done
  from q1 and q3 have q5:"card (f ` (Nset n)) \<le> card (Nset m)"
   apply (simp add:card_mono) done
 from q4 and q5 show ?thesis
  apply (simp add:card_Nset)
 done
qed
 
lemma enumerate_1:"\<lbrakk> f \<in> Nset n \<rightarrow> A; g \<in> Nset m \<rightarrow> A; inj_on f (Nset n); 
inj_on g (Nset m); f `(Nset n) = A; g ` (Nset m) = A \<rbrakk> \<Longrightarrow> n = m" 
proof -
 assume p1:"f \<in> Nset n \<rightarrow> A" and p2:"g \<in> Nset m \<rightarrow> A" and 
 p3:"inj_on f (Nset n)" and p4:"inj_on g (Nset m)" and p5:" f `(Nset n) = A" 
 and p6:"g ` (Nset m) = A"
 from p5 have q1:"card (f ` (Nset n)) = card A" apply (rule card_eq) done
 have q2:"finite (Nset n)" apply (simp add:finite_Nset) done
 from p3 and q2 have q3: "card (f ` (Nset n)) = card (Nset n)"
  apply (simp add:card_image) done
 from q1 and q3 have q4:"card A = card (Nset n)" apply auto done
 
 from p6 have q5:"card (g ` (Nset m)) = card A" apply (rule card_eq) done
 have q6:"finite (Nset m)" apply (simp add:finite_Nset) done
 from p4 and q6 have q7: "card (g ` (Nset m)) = card (Nset m)"
  apply (simp add:card_image) done
 from q5 and q7 have q8:"card A = card (Nset m)" apply auto done 

 from q4 and q8 show ?thesis
 apply (simp add:card_Nset)
 done
qed

constdefs
  ninv::"[nat, (nat \<Rightarrow> nat)] \<Rightarrow> (nat \<Rightarrow> nat)"
   "ninv n f == \<lambda>y\<in>Nset n. \<some> x. (x \<in> (Nset n) \<and>  y = f x)"


lemma ninv_hom:"\<lbrakk>f \<in> (Nset n) \<rightarrow> (Nset n); inj_on f (Nset n)\<rbrakk> \<Longrightarrow>
                        ninv n f \<in> (Nset n) \<rightarrow> (Nset n)"
proof -
 assume p1:"f \<in> (Nset n) \<rightarrow> (Nset n)" and p2:"inj_on f (Nset n)"
  from p1 and p2 have q1:"f ` Nset n = Nset n"
   apply (simp add:inj_surj) done
  
  from p1 and p2 and q1 show ?thesis
   apply (simp add:Pi_def ninv_def) 
   apply (rule allI) apply (rule impI) 
   apply (subgoal_tac "x \<in> f ` (Nset n)")
   apply (thin_tac "f ` Nset n = Nset n")
   apply (simp add:image_def CollectI)
   apply (rule someI2_ex)
   apply auto 
  done
qed

lemma ninv_r_inv:"\<lbrakk>f \<in> (Nset n) \<rightarrow> (Nset n); inj_on f (Nset n); b \<in> Nset n\<rbrakk> 
 \<Longrightarrow>  f (ninv n f b) = b "
proof -
 assume p1:"f \<in> (Nset n) \<rightarrow> (Nset n)" and p2:"inj_on f (Nset n)" and
               p3:" b \<in> Nset n"
 from p1 and p2 and p3 show ?thesis
  apply (simp add:ninv_def)
  apply (frule inj_surj, assumption+)
  apply (subgoal_tac "b \<in> f `(Nset n)") 
   apply (thin_tac "f ` Nset n = Nset n") 
  apply (simp add:image_def CollectI) 
  apply (rule someI2_ex) apply blast
  apply (subgoal_tac "b = f x") apply simp+
 done
qed

lemma ninv_inj:"\<lbrakk>f \<in> (Nset n) \<rightarrow> (Nset n); inj_on f (Nset n)\<rbrakk> \<Longrightarrow>
                                inj_on  (ninv n f) (Nset n)"
proof -
 assume p1:"f \<in> (Nset n) \<rightarrow> (Nset n)" and p2:"inj_on f (Nset n)"
 from p1 and p2 show ?thesis
  apply (simp add:inj_on_def [of "ninv n f" "Nset n"])
  apply (rule ballI)+ apply (rule impI)
  apply (subgoal_tac "f (ninv n f x) = f (ninv n f y)")
  apply (thin_tac "ninv n f x = ninv n f y")
  apply (subgoal_tac "f (ninv n f y) = y") apply simp
  apply (thin_tac "f (ninv n f y) = y")
  apply (subgoal_tac "f (ninv n f x) = x")  apply simp
  apply (rule ninv_r_inv, assumption+)+
  apply simp
 done
qed

chapter "1. Ordered Set"

(* In this chapter, I prove Zorn's lemma in general form. *)

section "1. Basic Concepts of Ordered Sets"

record 'a Base =
  carrier :: "'a set"

record 'a OrderedSet = "'a Base" + 
 ord_rel  :: "('a  * 'a) set"
 ordering  :: "['a, 'a] \<Rightarrow> bool" 

constdefs
 ordered_set :: "('a, 'mo) OrderedSet_scheme \<Rightarrow> bool"
 "ordered_set D == (ord_rel D) \<subseteq> (carrier D) \<times> (carrier D) \<and> (\<forall>a \<in> (carrier D). (a, a) \<in> (ord_rel D)) \<and>  (\<forall>a \<in> (carrier D). \<forall>b \<in> (carrier D). (a, b) \<in> (ord_rel D) \<and> (b, a) \<in> (ord_rel D)  \<longrightarrow> a = b) \<and> (\<forall>a \<in> (carrier D). \<forall>b\<in>(carrier D). \<forall>c\<in>(carrier D). (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D) \<and> (\<forall>a \<in> carrier D. \<forall>b \<in> carrier D. ordering D a b = ((a, b) \<in> ord_rel D))" 

ord_neq :: "[('a, 'mo) OrderedSet_scheme, 'a, 'a] \<Rightarrow> bool"
"ord_neq D a b == ordering D a b \<and> a \<noteq> b"
 
Iod :: "[('a, 'mo) OrderedSet_scheme, 'a set] \<Rightarrow> 'a OrderedSet"
"Iod D T == \<lparr>carrier = T, ord_rel = {x. x \<in> ord_rel D \<and> (fst x) \<in> T \<and> (snd x) \<in> T}, ordering = ordering D\<rparr>" 
    
syntax
 "@ORDERING"::"['a, ('a, 'mo) OrderedSet_scheme, 'a] \<Rightarrow> bool"
   ("(3_/ '\<le>\<^sub>_/ _)" [60,61,60]60)

 "@ORDNEQ"::"['a, ('a, 'mo) OrderedSet_scheme, 'a] \<Rightarrow> bool"
   ("(3/ _/ '<\<^sub>_/ _)" [60,61,60]60)
 

translations
 "a <\<^sub>D b" == "ord_neq D a b"
 "a \<le>\<^sub>D b" == "ordering D a b"

lemma Iod_self:"ordered_set T \<Longrightarrow> T = Iod T (carrier T)"
apply (rule equality)
 apply (simp add:Iod_def)+
 apply (subgoal_tac "ord_rel T \<subseteq> (carrier T) \<times> (carrier T)") 
prefer 2 apply (simp add:ordered_set_def)
 apply auto
apply (simp add:Iod_def)
done

lemma ordering_axiom1:"\<lbrakk>ordered_set D; a \<in> carrier D\<rbrakk> \<Longrightarrow> a \<le>\<^sub>D a"
apply (simp add:ordered_set_def)
done

lemma ordering_axiom2:"\<lbrakk>ordered_set D; a \<in> carrier D; b \<in> carrier D; a \<le>\<^sub>D b; b \<le>\<^sub>D a \<rbrakk> \<Longrightarrow> a = b"
apply (unfold ordered_set_def) apply (erule conjE)+
apply (subgoal_tac "(a, b) \<in> ord_rel D")
 prefer 2 
 apply (thin_tac "\<forall>a\<in>carrier D.
          \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply simp
apply (subgoal_tac "(b, a) \<in> ord_rel D")
 prefer 2 
 apply (thin_tac "\<forall>a\<in>carrier D.
          \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply simp
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D.  a \<le>\<^sub>D b = ((a, b) \<in> ord_rel D)") apply simp
done

lemma ordering_axiom3:"\<lbrakk>ordered_set D; a \<in> carrier D; b \<in> carrier D; c \<in> carrier D; a \<le>\<^sub>D b; b \<le>\<^sub>D c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>D c"
apply (unfold ordered_set_def)
 apply (erule conjE)+
 apply (subgoal_tac "(a, b) \<in> ord_rel D")
 apply (subgoal_tac "(b, c) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (subgoal_tac "(a, c) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow>  (a, c) \<in> ord_rel D") 
 apply (thin_tac "(a, b) \<in> ord_rel D") apply (thin_tac "(b, c) \<in> ord_rel D")
 apply (subgoal_tac "a \<le>\<^sub>D c = ((a, c) \<in> ord_rel D)")
 apply simp apply simp
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D.  a \<le>\<^sub>D b = ((a, b) \<in> ord_rel D)")
 apply blast
 apply (thin_tac "\<forall>a\<in>carrier D.
          \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply simp
 apply (thin_tac "\<forall>a\<in>carrier D.
          \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply simp 
done

lemma ord_neq_trans:"\<lbrakk>ordered_set D; a \<in> carrier D; b \<in> carrier D; c \<in> carrier D; a <\<^sub>D b; b <\<^sub>D c \<rbrakk> \<Longrightarrow> a <\<^sub>D c"
apply (simp add:ord_neq_def)
 apply (erule conjE)+
 apply (frule_tac a = a and b = b and c = c in ordering_axiom3, assumption+)
 apply simp
 apply (rule contrapos_pp, simp+)
apply (frule_tac a = c and b = b in ordering_axiom2, assumption+)
apply simp
done
 
constdefs
 tordered_set::"('a, 'mo) OrderedSet_scheme \<Rightarrow> bool"
 "tordered_set D == ordered_set D \<and> (\<forall>a\<in>(carrier D). \<forall>b\<in>(carrier D). a \<le>\<^sub>D b \<or> b \<le>\<^sub>D a)"

lemma tordering_not:"\<lbrakk>tordered_set D; a \<in> carrier D; b \<in> carrier D; \<not> a \<le>\<^sub>D b\<rbrakk> \<Longrightarrow>   b <\<^sub>D a" 
apply (case_tac "a = b") apply simp
 apply (subgoal_tac "ordered_set D")
 apply (frule ordering_axiom1 [of "D" "b"], assumption+) apply simp
 apply (simp add:tordered_set_def)
apply (simp add:tordered_set_def) apply (erule conjE)
apply (subgoal_tac "b \<le>\<^sub>D a") prefer 2 apply blast
apply (simp add:ord_neq_def) apply (rule not_sym, assumption+)
done

lemma tordering_not1:"\<lbrakk>tordered_set D; a \<in> carrier D; b \<in> carrier D; a <\<^sub>D b \<rbrakk> \<Longrightarrow>
 \<not> b \<le>\<^sub>D a"
apply (rule contrapos_pp, simp+) apply (simp add:ord_neq_def)
apply (erule conjE)+ 
 apply (simp add: tordered_set_def) apply (erule conjE)
apply (frule_tac ordering_axiom2 [of "D" "a" "b"], assumption+) 
apply blast
done

lemma tordering_not2:"\<lbrakk>tordered_set D; a \<in> carrier D; b \<in> carrier D; \<not> a <\<^sub>D b\<rbrakk>  \<Longrightarrow>  b \<le>\<^sub>D a"
apply (rule contrapos_pp, assumption+)
apply (frule_tac D = D and a = b and b = a in tordering_not, assumption+)
apply simp
done

lemma tordering_not3:"\<lbrakk>tordered_set D; a \<in> carrier D; b \<in> carrier D;  a \<le>\<^sub>D b\<rbrakk>  \<Longrightarrow> \<not>  b <\<^sub>D a"
apply (rule contrapos_pp, simp+)
apply (frule_tac D = D and a = b and b = a in tordering_not1, assumption+)
apply simp
done

constdefs
 ordered_set_Pow::"'a set \<Rightarrow> ('a set) OrderedSet"
  ("(po  _ )" [999]1000)
 "po A == \<lparr>carrier = Pow A, ord_rel = {Z. Z \<in> (Pow A) \<times> (Pow A) \<and> (fst Z) \<subseteq> (snd Z)}, ordering = \<lambda>a\<in>(Pow A). \<lambda>b\<in>(Pow A). a \<subseteq> b\<rparr>"

lemma ordered_Pow:"ordered_set (po A )"
apply (simp add:ordered_set_Pow_def)
apply (simp add:ordered_set_def) 
apply (rule conjI)
 apply (rule subsetI)
 apply simp
apply (rule conjI)
 apply (rule ballI) apply (simp add:Pow_def)
 apply (rule conjI)
 apply (rule ballI)+ apply (rule impI) 
 apply (erule conjE)+ apply (rule equalityI, assumption+)
apply (rule conjI)
 apply (rule ballI)+ apply (rule impI)
 apply (erule conjE)+ 
 apply (rule_tac A = a and B = b and C = c in subset_trans, assumption+)
apply (rule ballI)
 apply (simp add:Pow_def)
done

constdefs
ordered_set_fs::"['a set, 'b set] \<Rightarrow> ('a set * ('a \<Rightarrow> 'b)) OrderedSet"
"ordered_set_fs A B == \<lparr>carrier = {Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1 \<and> Z = (A1, f)}, ord_rel = {Y. Y \<in> ({Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1 \<and> Z = (A1, f)}) \<times> ({Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1 \<and> Z = (A1, f)}) \<and> fst (fst Y) \<subseteq> fst (snd Y) \<and> (\<forall>a\<in> (fst (fst Y)). (snd (fst Y)) a = (snd (snd Y)) a)}, ordering = \<lambda>u\<in>{Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1 \<and> Z = (A1, f)}. \<lambda>v\<in>{Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1 \<and> Z = (A1, f)}. ((fst u) \<subseteq> (fst v) \<and> (\<forall>a\<in>(fst u). (snd u) a = (snd v) a)) \<rparr>" 

(* order (A1, f1) < (A2, f2), where A1, A2 subsets of A and f1, f2 functions
 of A1 to B, A2 to B respectively. *)

lemma ordered_fs:"ordered_set (ordered_set_fs A B)"
apply (simp add:ordered_set_fs_def)
apply (simp add:ordered_set_def)
apply (rule conjI)
 apply (rule subsetI)
 apply simp
apply (rule conjI)
 apply (rule allI)+ apply (rule impI) apply (rule allI)+ apply (rule impI)
 apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "a = aa") apply simp 
 apply (rule_tac s = ba and A1 = aa and t = b in funcset_eq[THEN sym], assumption+)
 apply (rule equalityI, assumption+)
 apply (rule allI)+ apply (rule impI) 
 apply (rule allI)+ apply (rule impI) 
 apply (rule allI)+ apply (rule impI) apply (rule impI)
 apply (erule conjE)+ 
apply (subgoal_tac "a \<subseteq> ab") apply simp
 apply (rule ballI) apply blast
 apply (rule_tac A = a and B = aa and C = ab in subset_trans, assumption+)
done

lemma ordered_set_Iod:"\<lbrakk>ordered_set D; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow> ordered_set (Iod D T)"
apply (subst ordered_set_def)
 apply (rule conjI)
 apply (simp add:Iod_def)
 apply (rule subsetI) apply simp apply (erule conjE)+
 apply auto
apply (simp add:Iod_def)
 apply (simp add:ordered_set_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
        (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D.  a \<le>\<^sub>D b = ((a, b) \<in> ord_rel D)")
 apply (thin_tac "\<forall>a\<in>carrier D.
              \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply blast
apply (simp add:Iod_def)
 apply (simp add:ordered_set_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier D. (a, a) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply blast
apply (simp add:Iod_def) apply (simp add:ordered_set_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. (a, a) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D.  a \<le>\<^sub>D b = ((a, b) \<in> ord_rel D)")
 apply blast
apply (simp add:Iod_def)
 apply (simp add:ordered_set_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D.
 (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
 apply blast
apply (simp add:Iod_def) apply (simp add:ordered_set_def)
 apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier D. (a, a) \<in> ord_rel D")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, a) \<in> ord_rel D \<longrightarrow> a = b")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. \<forall>c\<in>carrier D. (a, b) \<in> ord_rel D \<and> (b, c) \<in> ord_rel D \<longrightarrow> (a, c) \<in> ord_rel D")
apply blast
done

lemma Iod_sub_sub:"\<lbrakk>ordered_set D; S \<subseteq> T; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow>
  Iod (Iod D T) S = Iod D S"
apply (simp add:Iod_def)
apply auto
done

constdefs
 ord_inj :: "[('a, 'mo) OrderedSet_scheme, ('b, 'mo) OrderedSet_scheme,  'a \<Rightarrow> 'b] \<Rightarrow> bool"
 "ord_inj D E f == f \<in> extensional (carrier D) \<and> f \<in> (carrier D) \<rightarrow> (carrier E) \<and> (inj_on f (carrier D)) \<and> (\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a <\<^sub>D b) = ((f a) <\<^sub>E (f b)))"

 ord_isom :: "[('a, 'mo) OrderedSet_scheme, ('b, 'mo) OrderedSet_scheme, 'a \<Rightarrow> 'b] \<Rightarrow> bool"
 "ord_isom D E f == f \<in> extensional (carrier D) \<and> f \<in> (carrier D) \<rightarrow> (carrier E) \<and> (bij_to f (carrier D) (carrier E)) \<and> (\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a <\<^sub>D b) = ((f a) <\<^sub>E (f b)))"

lemma ord_isom_mem:"\<lbrakk>ordered_set D; ordered_set E; ord_isom D E f; a \<in> carrier D\<rbrakk> \<Longrightarrow> (f a) \<in> carrier E"
apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
done

lemma ord_isom_surj:"\<lbrakk>ordered_set D; ordered_set E; ord_isom D E f; b \<in> carrier E\<rbrakk> \<Longrightarrow> \<exists>a\<in>carrier D. b = f a"
apply (simp add:ord_isom_def) apply (erule conjE)+
apply (simp add:bij_to_def) apply (erule conjE)+
 apply (simp add:surj_to_def image_def)
 apply (frule sym) apply (thin_tac "{y. \<exists>x\<in>carrier D. y = f x} = carrier E")
 apply simp
done

lemma ord_isom1_1:"\<lbrakk> ordered_set D; ordered_set E; ord_isom D E f; a \<in> carrier D; b \<in> carrier D; a <\<^sub>D b \<rbrakk> \<Longrightarrow> (f a) <\<^sub>E (f b)"
apply (unfold ord_isom_def) apply (erule conjE)+
 apply blast
done

lemma ord_isom1_2:"\<lbrakk> ordered_set D; ordered_set E; ord_isom D E f; a \<in> carrier D; b \<in> carrier D; a \<le>\<^sub>D b \<rbrakk> \<Longrightarrow> (f a) \<le>\<^sub>E (f b)"
apply (case_tac "a = b") apply (simp) apply (rule ordering_axiom1, assumption+)
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply (subgoal_tac "a <\<^sub>D b") prefer 2 apply (simp add:ord_neq_def)
apply (frule ord_isom1_1 [of "D" "E" "f" "a" "b"], assumption+)
apply (simp add:ord_neq_def)
done

lemma ord_isom2_1:"\<lbrakk> ordered_set D; ordered_set E; ord_isom D E f; a \<in> carrier D; b \<in> carrier D; (f a) <\<^sub>E (f b)\<rbrakk> \<Longrightarrow>  a <\<^sub>D b"
apply (unfold ord_isom_def) apply (erule conjE)+
 apply blast
done

lemma ord_isom2_2:"\<lbrakk> ordered_set D; ordered_set E; ord_isom D E f; a \<in> carrier D; b \<in> carrier D; (f a) \<le>\<^sub>E (f b)\<rbrakk> \<Longrightarrow>  a \<le>\<^sub>D b"
apply (case_tac "f a \<noteq> (f b)") 
apply (subgoal_tac "f a <\<^sub>E (f b)")
 apply (frule_tac ord_isom2_1 [of "D" "E" "f" "a" "b"], assumption+)
 apply (simp add:ord_neq_def)
 apply (simp add:ord_neq_def)
apply simp 
 apply (subgoal_tac "inj_on f (carrier D)")
 apply (simp add:inj_on_def)
 apply (subgoal_tac "a = b") prefer 2 apply simp
apply (simp add:ordering_axiom1) 
apply (simp add:ord_isom_def bij_to_def) 
done

lemma ord_isom_sym:"\<lbrakk>ordered_set D; ordered_set E; ord_isom D E f\<rbrakk> \<Longrightarrow>
 ord_isom E D (invfun (carrier D) (carrier E) f)"
apply (subst ord_isom_def)
apply (rule conjI)
 apply (simp add:invfun_def extensional_def)
 apply (rule conjI)
 apply (rule inv_func)
 apply (simp add:ord_isom_def) apply (simp add:ord_isom_def bij_to_def) 
 apply (simp add:ord_isom_def bij_to_def) 
apply (rule conjI)
 apply (rule bij_invfun) apply (simp add:ord_isom_def)+
 apply (rule ballI)+ 
 apply (simp add:bij_to_def) apply (erule conjE)+
 apply (subgoal_tac "f ` (carrier D) = carrier E") 
 prefer 2 apply (simp add:surj_to_def)
 apply (subgoal_tac "a \<in> f ` carrier D")
 apply (subgoal_tac "b \<in> f ` carrier D")
 apply (thin_tac " f ` carrier D = carrier E") apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier D. \<forall>y\<in>carrier D. a = f x \<and> b = f y \<longrightarrow> a <\<^sub>E b = invfun (carrier D) (carrier E) f a <\<^sub>D (invfun (carrier D) (carrier E) f b)")
 apply blast apply (thin_tac "\<exists>x\<in>carrier D. a = f x")
 apply (thin_tac "\<exists>x\<in>carrier D. b = f x") apply (rule ballI)+ 
 apply (rule impI) apply (erule conjE) apply simp
 apply (subst invfun_l, assumption+)+
 apply (subgoal_tac "x <\<^sub>D y = (f x) <\<^sub>E (f y)") prefer 2 apply simp
apply (rule sym, assumption+)
 apply simp apply simp
done

lemma ord_isom_trans:"\<lbrakk> ordered_set D; ordered_set E; ordered_set F; ord_isom D E f; ord_isom E F g \<rbrakk> \<Longrightarrow>  ord_isom D F (compose (carrier D) g f)"
apply (simp add:ord_isom_def)
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:compose_def)
 apply (erule conjE)+ apply (simp add:funcset_mem)+
apply (rule conjI)
 apply (simp add:bij_to_def) apply (erule conjE)+
 apply (simp add:compose_surj) apply (simp add:comp_inj)
apply (rule ballI)+ apply (erule conjE)+
apply (frule_tac f = f and A = "carrier D" and B = "carrier E" and x = a
         in funcset_mem, assumption+)
apply (frule_tac f = f and A = "carrier D" and B = "carrier E" and x = b
         in funcset_mem, assumption+)
apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D.  a <\<^sub>D b =  f a <\<^sub>E (f b)")
apply (simp add:compose_def)
done

constdefs
 ord_equiv :: "[('a, 'mo) OrderedSet_scheme, ('b, 'mo) OrderedSet_scheme]  \<Rightarrow> bool"
 "ord_equiv D E == \<exists>f. ord_isom D E f"

lemma ord_equiv_reflex:"ordered_set D \<Longrightarrow> ord_equiv D D"
apply (simp add:ord_equiv_def)
apply (subgoal_tac "ord_isom D D (idmap (carrier D))")
 apply blast
 apply (simp add:ord_isom_def)
 apply (simp add:idmap_funcs)
apply (rule conjI)
 apply (simp add:idmap_def extensional_def)
 apply (rule conjI)
 apply (simp add:bij_to_def)
 apply (rule conjI)
 apply (simp add:surj_to_def) apply (simp add:image_def)
 apply (simp add:idmap_def)
 apply (simp add:inj_on_def) apply (rule ballI)+
 apply (simp add:idmap_def)
apply (simp add:idmap_def)
done

lemma ord_equiv_sym:"\<lbrakk>ordered_set D; ordered_set E; ord_equiv D E \<rbrakk> \<Longrightarrow>
 ord_equiv E D"
apply (simp add:ord_equiv_def)
apply (subgoal_tac "\<forall>g. ord_isom D E g \<longrightarrow> (\<exists>f. ord_isom E D f)")
 apply blast apply (thin_tac "\<exists>f. ord_isom D E f")
 apply (rule allI) apply (rule impI)
apply (frule_tac D = D and E = E and f = g in ord_isom_sym, assumption+)
 apply blast
done

lemma ord_equiv_trans:"\<lbrakk>ordered_set D; ordered_set E; ordered_set F; ord_equiv D E; ord_equiv E F\<rbrakk> \<Longrightarrow>  ord_equiv D F"
apply (simp add:ord_equiv_def)
apply (subgoal_tac "\<forall>f g. ord_isom D E f \<and> ord_isom E F g \<longrightarrow> (\<exists>f. ord_isom D F f)") apply blast apply (thin_tac "\<exists>f. ord_isom D E f")
 apply (thin_tac "\<exists>f. ord_isom E F f") apply (rule allI)+ apply (rule impI)
 apply (erule conjE)
 apply (frule_tac f = f and g = g in ord_isom_trans [of "D" "E" "F"], assumption+)
apply blast
done

constdefs
 minimum_elem::"[('a, 'mo) OrderedSet_scheme, 'a set, 'a] \<Rightarrow> bool"
 "minimum_elem D X a == a \<in> X \<and> (\<forall>x\<in>X. a \<le>\<^sub>D x)"  

 well_ordered_set::"('a, 'mo) OrderedSet_scheme \<Rightarrow> bool"
 "well_ordered_set D == tordered_set D \<and> (\<forall>X. X \<subseteq> (carrier D) \<and> X \<noteq> {} \<longrightarrow>
  (\<exists>x. minimum_elem D X x))"

lemma well_ordered_set_is_ordered_set:"well_ordered_set S \<Longrightarrow> ordered_set S"
apply (simp add:well_ordered_set_def tordered_set_def)
done

lemma pre_minimum:"\<lbrakk>well_ordered_set D; T \<subseteq> carrier D; minimum_elem D T t; 
s \<in> carrier D; s <\<^sub>D t \<rbrakk> \<Longrightarrow> \<not> s \<in> T"
apply (rule contrapos_pp, simp+)
 apply (simp add:minimum_elem_def) apply (erule conjE)+
 apply (simp add:ord_neq_def) apply (erule conjE)
 apply (subgoal_tac "t \<le>\<^sub>D s") prefer 2 apply simp
 apply (frule well_ordered_set_is_ordered_set [of "D"])
 apply (frule ordering_axiom2 [of "D" "s" "t"], assumption+)
 apply (simp add:subsetD) apply assumption+
apply simp
done

lemma well_ordered_to_subset:"\<lbrakk>well_ordered_set (S::'a OrderedSet); T \<subseteq> carrier S; ord_isom S (Iod S T) f\<rbrakk> \<Longrightarrow> \<forall>a. a \<in> carrier S \<longrightarrow> a \<le>\<^sub>S (f a)"  
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "\<exists>b. minimum_elem S {c. c \<in> carrier S \<and> \<not> c \<le>\<^sub>S (f c)} b")
apply (subgoal_tac "\<forall>b. minimum_elem S {c. c \<in> carrier S \<and> \<not> c \<le>\<^sub>S (f c)} b \<longrightarrow> False") apply blast apply (thin_tac "\<exists>b. minimum_elem S {c. c \<in> carrier S \<and> \<not>  c \<le>\<^sub>S (f c)} b")
apply (rule allI) apply (rule impI)
 apply (thin_tac "\<exists>a. a \<in> carrier S \<and> \<not>  a \<le>\<^sub>S (f a)")
prefer 2 apply (simp add:well_ordered_set_def) apply (erule conjE)+
 apply (subgoal_tac "{c. c \<in> carrier S \<and> \<not>  c \<le>\<^sub>S (f c)} \<subseteq> carrier S \<and> {c. c \<in> carrier S \<and> \<not>  c \<le>\<^sub>S (f c)} \<noteq> {}") apply blast
 apply (rule conjI)
 apply (rule subsetI) apply simp
 apply blast 
 apply (subgoal_tac "b \<in> {c. c \<in> carrier S \<and> \<not>  c \<le>\<^sub>S (f c)}")
 prefer 2 apply (simp add:minimum_elem_def)
 apply simp apply (erule conjE)
 apply (simp add:well_ordered_set_def) apply (erule conjE)+
  apply (thin_tac "\<forall>X. X \<subseteq> carrier S \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem S X x)")
  apply (subgoal_tac "f b \<in> carrier S")
 apply (frule_tac a = b and b = "f b" in tordering_not [of "S"], assumption+)
 apply (subgoal_tac "\<not>  (f b) \<le>\<^sub>S (f (f b))")
 apply (simp add:minimum_elem_def) 
 apply (subgoal_tac "ordered_set S") prefer 2 apply (simp add:tordered_set_def)
apply (rule tordering_not1, assumption+)
 apply (simp add:ord_isom_def Iod_def) apply (erule conjE)+
 apply (simp add:funcset_mem subsetD) apply assumption
 apply (frule_tac a = "f b" and b = b in ord_isom1_1 [of "S" "Iod S T" "f"])
 apply (simp add:ordered_set_Iod) apply assumption+
 apply (simp add:Iod_def ord_neq_def)  
apply (simp add:ord_isom_def Iod_def) apply (erule conjE)+
 apply (simp add:funcset_mem subsetD)
done

lemma ordered_ord_equiv_well_ordered:"\<lbrakk>well_ordered_set S; ordered_set T; ord_isom S T f\<rbrakk> \<Longrightarrow> well_ordered_set T"
apply (subst well_ordered_set_def)
apply (rule conjI)
apply (subst tordered_set_def)
 apply simp
 apply (rule ballI)+
 apply (subgoal_tac "surj_to f (carrier S) (carrier T)")
 apply (simp add:surj_to_def)
 apply (subgoal_tac "a \<in> f ` carrier S")
 apply (subgoal_tac "b \<in> f ` carrier S")
 apply (thin_tac "f ` carrier S = carrier T")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier S. \<forall>y\<in>carrier S. a = f x \<and> b = f y \<longrightarrow> a \<le>\<^sub>T b \<or>  b \<le>\<^sub>T a")
 apply blast apply (thin_tac "\<exists>x\<in>carrier S. a = f x") apply (thin_tac "\<exists>x\<in>carrier S. b = f x")
 apply (rule ballI)+ apply (rule impI)
 apply (erule conjE)+
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (erule conjE)+
 apply (thin_tac "\<forall>X. X \<subseteq> carrier S \<and> X \<noteq> {} \<longrightarrow> Ex (minimum_elem S X)")
 apply (subgoal_tac "x \<le>\<^sub>S y \<or>  y \<le>\<^sub>S x") prefer 2 apply simp
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a")
 apply (case_tac "x \<le>\<^sub>S y") apply (simp add:ord_isom1_2)
 apply (simp add:ord_isom1_2) apply simp+
 apply (simp add:ord_isom_def bij_to_def)
apply (rule allI)
 apply (rule impI)
 apply (erule conjE)
 apply (subgoal_tac "invim f (carrier S) X \<noteq> {}")
 apply (subgoal_tac "invim f (carrier S) X \<subseteq> carrier S")
 apply (subgoal_tac "\<exists>a. minimum_elem S (invim f (carrier S) X) a")
 apply (subgoal_tac "\<forall>a. minimum_elem S (invim f (carrier S) X) a \<longrightarrow>
 (\<exists>x. minimum_elem T X x)") apply blast
 apply (thin_tac "\<exists>a. minimum_elem S (invim f (carrier S) X) a")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "minimum_elem T X (f a)") apply blast
apply (subst minimum_elem_def)
 apply (rule conjI)
 apply (simp add:minimum_elem_def) apply (erule conjE)
 apply (simp add:invim_def)
 apply (rule ballI)
 apply (simp add:minimum_elem_def) apply (erule conjE)+
 apply (subgoal_tac "bij_to f (carrier S) (carrier T)")
 apply (simp add:bij_to_def) apply (erule conjE)+
 apply (frule_tac A = X and B = "carrier T" and c = x in subsetD, assumption+)
 apply (simp add:surj_to_def) apply (subgoal_tac "x \<in> f ` (carrier S)")
 apply (thin_tac "f ` carrier S = carrier T")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>carrier S. x = f xa \<longrightarrow> f a \<le>\<^sub>T x")
 apply blast apply (thin_tac "\<exists>xa\<in>carrier S. x = f xa")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "a \<le>\<^sub>S xa") apply (subgoal_tac "a \<in> carrier S")
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (simp add:ord_isom1_2)
 apply (simp add:invim_def)
 apply (subgoal_tac "xa \<in> invim f (carrier S) X")
 apply simp
 apply (subst invim_def) apply simp apply (simp add:subsetD)
apply (simp add:ord_isom_def)
 apply (simp add:well_ordered_set_def)
 apply (rule subsetI)
 apply (simp add:invim_def)
apply (frule_tac A = X in nonempty_ex) apply (thin_tac "X \<noteq> {}")
 apply (subgoal_tac "\<forall>x. x \<in> X \<longrightarrow> invim f (carrier S) X \<noteq> {}")
 apply blast apply (thin_tac "\<exists>x. x \<in> X")
apply (rule allI) apply (rule impI)
 apply (subgoal_tac "surj_to f (carrier S) (carrier T)")
 apply (simp add:surj_to_def)
 apply (subgoal_tac "x \<in> f ` (carrier S)")
 apply (thin_tac "f ` carrier S = carrier T") apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>carrier S. x = f xa \<longrightarrow> (invim f (carrier S) X \<noteq> {})") apply blast apply (thin_tac "\<exists>xa\<in>carrier S. x = f xa")
 apply (rule ballI) apply (rule impI)
 apply (simp add:invim_def) apply blast
 apply (simp add:subsetD)
apply (simp add:ord_isom_def bij_to_def)
done

lemma ord_isom_self_id:"\<lbrakk>well_ordered_set (S::'a OrderedSet); ord_isom S S f\<rbrakk> \<Longrightarrow> f = idmap (carrier S)" 
apply (subgoal_tac "ordered_set S") 
prefer 2 apply (simp add:well_ordered_set_def tordered_set_def) 
apply (frule ord_isom_sym [of "S" "S" "f"], assumption+)
apply (subgoal_tac "f \<in> carrier S \<rightarrow> carrier S")
 prefer 2 apply (simp add:ord_isom_def)
 apply (subgoal_tac "idmap (carrier S) \<in> (carrier S) \<rightarrow> (carrier S)")
 prefer 2 apply (simp add:idmap_funcs)
 apply (subgoal_tac "f \<in> extensional (carrier S)") 
 apply (rule funcset_eq, assumption+)
 apply (simp add:idmap_def)
 apply (rule ballI) apply (simp add:idmap_def)
 apply (frule well_ordered_to_subset [of "S" "carrier S" "f"])
 apply simp
 apply (simp add:ord_isom_def) apply (simp add:Iod_def ord_neq_def) 
 apply (subgoal_tac "x \<le>\<^sub>S (f x)")  prefer 2 apply blast
 apply (thin_tac "\<forall>a. a \<in> carrier S \<longrightarrow>  a \<le>\<^sub>S (f a)")
 apply (frule well_ordered_to_subset [of "S" "carrier S" "invfun (carrier S) (carrier S) f"])
 apply simp
 apply (simp add:ord_isom_def Iod_def ord_neq_def)
 apply (subgoal_tac "x \<le>\<^sub>S (invfun (carrier S) (carrier S) f x)")
 prefer 2 apply blast
 apply (thin_tac "\<forall>a. a \<in> carrier S \<longrightarrow>  a \<le>\<^sub>S (invfun (carrier S) (carrier S) f a)") 
 apply (frule_tac x = x in funcset_mem [of "f" "carrier S" "carrier S"], assumption+)
 apply (subgoal_tac "inj_on f (carrier S) \<and> surj_to f (carrier S) (carrier S)")
 apply (erule conjE)+
 apply (frule_tac b = x in invfun_mem [of "f" "carrier S" "carrier S"], assumption+)
 apply (subgoal_tac "f x \<le>\<^sub>S (f (invfun (carrier S) (carrier S) f x))")
 apply (simp add:invfun_r)
 apply (rule_tac a = "f x" and b = x in ordering_axiom2 [of "S"], assumption+) 
 apply (rule_tac a = x and b = "(invfun (carrier S) (carrier S) f x)" in ord_isom1_2 [of "S" "S" "f"], assumption+)
 apply (simp add:ord_isom_def bij_to_def)
apply (simp add:ord_isom_def)
done

lemma wellord_isom_unique:"\<lbrakk>well_ordered_set (S :: 'a OrderedSet); well_ordered_set (T :: 'a OrderedSet); ord_isom S T f; ord_isom S T g\<rbrakk> \<Longrightarrow> f = g"
apply (subgoal_tac "ordered_set S")
apply (subgoal_tac "ordered_set T")
apply (frule ord_isom_sym[of "S" "T" "g"], assumption+)
apply (frule ord_isom_trans [of "S" "T" "S" "f" "invfun (carrier S) (carrier T) g"], assumption+)
apply (frule ord_isom_self_id [of "S" "compose (carrier S) (invfun (carrier S) (carrier T) g) f"], assumption+)
 apply (thin_tac "ord_isom T S (invfun (carrier S) (carrier T) g)")
 apply (simp add:compose_def)
prefer 2 apply (simp add:well_ordered_set_def tordered_set_def)
prefer 2 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (subgoal_tac "f \<in> extensional (carrier S) \<and> f \<in> carrier S \<rightarrow> carrier T")
 apply (subgoal_tac "g \<in> extensional (carrier S) \<and> g \<in> carrier S \<rightarrow> carrier T")
prefer 2 apply (simp add:ord_isom_def)
prefer 2 apply (simp add:ord_isom_def) apply (erule conjE)+
apply (rule funcset_eq, assumption+)
 apply (rule ballI)
 apply (subgoal_tac "((\<lambda>x\<in>carrier S. invfun (carrier S) (carrier T) g (f x))) x = idmap (carrier S) x") prefer 2 apply simp
 apply (thin_tac "(\<lambda>x\<in>carrier S. invfun (carrier S) (carrier T) g (f x)) =
           idmap (carrier S)")
 apply simp
 apply (frule_tac x = x in funcset_mem [of "f" "carrier S" "carrier T"], assumption+) 
 apply (simp add:idmap_def)
 apply (subgoal_tac "g (invfun (carrier S) (carrier T) g (f x)) = g x")
 prefer 2 apply simp
 apply (thin_tac "invfun (carrier S) (carrier T) g (f x) = x")
 apply (subgoal_tac "inj_on g (carrier S) \<and> surj_to g (carrier S) (carrier T)")
 apply (erule conjE)
 apply (simp add:invfun_r)
apply (simp add:ord_isom_def [of "S" "T" "g"] bij_to_def)
done
 
constdefs
 segment :: "[('a, 'mo) OrderedSet_scheme, 'a] \<Rightarrow> 'a set"
 "segment S a == {x.  x <\<^sub>S a \<and> x \<in> carrier S}"   
   (* used in wellordered set *)

lemma segment_inc:"\<lbrakk> ordered_set D; a \<in> carrier D; b \<in> carrier D; a <\<^sub>D b \<rbrakk> \<Longrightarrow> a \<in> segment D b" 
apply (simp add:segment_def)
done

lemma ord_isom_segment_segment:"\<lbrakk>well_ordered_set S; well_ordered_set T; ord_isom S T f; a \<in> carrier S \<rbrakk> \<Longrightarrow> ord_equiv (Iod S (segment S a)) (Iod T (segment T (f a)))" 
apply (subgoal_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (f a))) (\<lambda>x\<in>carrier (Iod S (segment S a)). f x)")
apply (subst ord_equiv_def) apply blast
apply (subst ord_isom_def)
 apply (rule conjI)
 apply (simp add:restrict_def extensional_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Iod_def) apply (simp add:segment_def)
 apply (erule conjE) apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply (rule conjI)
 apply (simp add:bij_to_def)
 apply (rule conjI)
 apply (rule surj_to_test)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Iod_def)
 apply (simp add:segment_def) 
 apply (erule conjE)
 apply (subgoal_tac "f x \<in> carrier T") apply simp
 apply (simp add:ord_isom_def) apply (simp add:ord_isom_def) 
 apply (erule conjE)+ apply (simp add:funcset_mem)
apply (rule ballI)
 apply (simp add:Iod_def)
 apply (simp add:segment_def)
 apply (subgoal_tac "surj_to f (carrier S) (carrier T)")
 apply (simp add:surj_to_def) apply (erule conjE)
 apply (subgoal_tac "b \<in> f ` (carrier S)") prefer 2 apply simp
 apply (thin_tac " f ` carrier S = carrier T")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier S. b = f x \<longrightarrow> (\<exists>aa.  aa <\<^sub>S a \<and> aa \<in> carrier S \<and> f aa = b)") apply blast apply (thin_tac "\<exists>x\<in>carrier S. b = f x")
 apply (rule ballI) apply (rule impI) apply simp
 apply (subgoal_tac "ordered_set S") apply (subgoal_tac "ordered_set T")
 apply (frule_tac a = x and b = a in ord_isom2_1 [of "S" "T" "f"], assumption+)
 apply blast
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (simp add:ord_isom_def bij_to_def)
 apply (subgoal_tac "\<forall>x. x \<in> carrier (Iod S (segment S a)) \<longrightarrow> x \<in> carrier S")
 apply (simp add:ord_isom_def bij_to_def inj_on_def)
apply (rule allI) apply (rule impI) apply (simp add:Iod_def segment_def)
apply (rule ballI)+
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply auto
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (rule ord_isom1_2 [of "S" "T" "f"], assumption+) 
 apply (simp add:ord_isom_def bij_to_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a <\<^sub>S b =  f a <\<^sub>T (f b)")
 apply (simp add:inj_on_def)
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (rule ord_isom2_2 [of "S" "T" "f"], assumption+)
done

lemma ord_isom_induced:"\<lbrakk>well_ordered_set S; well_ordered_set T; ord_isom S T f; S1 \<subseteq> carrier S \<rbrakk> \<Longrightarrow> ord_isom (Iod S S1) (Iod T (f ` S1)) (\<lambda>x\<in>S1. f x)"
 apply (subst ord_isom_def)
 apply (rule conjI)
 apply (simp add:Iod_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:Iod_def)
apply (rule conjI)
 apply (unfold bij_to_def)
 apply (rule conjI) 
  apply (simp add:surj_to_def Iod_def)
 apply (simp add:ord_isom_def bij_to_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a <\<^sub>S b =  f a <\<^sub>T (f b)")
 apply (subgoal_tac "\<forall>x. x \<in> S1 \<longrightarrow> x \<in> carrier S")
  apply (simp add:inj_on_def Iod_def)
  apply (simp add:subsetD)
apply (rule ballI)+
 apply (simp add:Iod_def ord_neq_def)
 apply auto
 apply (rule_tac a = a and b = b in ord_isom1_2 [of "S" "T" "f"])
 apply (simp add:well_ordered_set_is_ordered_set)+
 apply (simp add:subsetD)+
 apply (simp add:ord_isom_def bij_to_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a <\<^sub>S b =  f a <\<^sub>T (f b)")
 apply (frule_tac c = a in subsetD [of "S1" "carrier S"], assumption+)
 apply (frule_tac c = b in subsetD [of "S1" "carrier S"], assumption+)
 apply (simp add:inj_on_def)
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (frule well_ordered_set_is_ordered_set [of "T"])
apply (frule_tac c = a in subsetD [of "S1" "carrier S"], assumption+)
apply (frule_tac c = b in subsetD [of "S1" "carrier S"], assumption+)
apply (rule_tac a = a and b = b in ord_isom2_2 [of "S" "T" "f"], assumption+)
done

lemma ord_equiv_induced:"\<lbrakk>well_ordered_set S; well_ordered_set T; ord_isom S T f; S1 \<subseteq> carrier S \<rbrakk> \<Longrightarrow> ord_equiv (Iod S S1) (Iod T (f ` S1))"
apply (simp add:ord_equiv_def)
apply (frule ord_isom_induced [of "S" "T" "f" "S1"], assumption+)
 apply blast
done

lemma ord_isom_induced_by_inj:"\<lbrakk>well_ordered_set S; well_ordered_set T; ord_inj S T f\<rbrakk> \<Longrightarrow> ord_isom S (Iod T (f ` carrier S)) (\<lambda>x\<in>carrier S. f x)"
 apply (simp add:ord_inj_def ord_isom_def)
 apply (erule conjE)+
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Iod_def)
apply (rule conjI)
 apply (simp add:bij_to_def)
 apply (simp add:surj_to_def)
 apply (simp add:Iod_def)
apply (rule ballI)+
 apply (simp add:Iod_def ord_neq_def)
done

lemma ord_equiv_induced_by_inj:"\<lbrakk>well_ordered_set S; well_ordered_set T; ord_inj S T f\<rbrakk> \<Longrightarrow> ord_equiv S (Iod T (f ` carrier S)) "
apply (simp add:ord_equiv_def)
apply (frule ord_isom_induced_by_inj [of "S" "T" "f"], assumption+)
apply blast
done

lemma segment_min_empty:"\<lbrakk>well_ordered_set S; minimum_elem S (carrier S) a \<rbrakk> \<Longrightarrow> segment S a = {}"
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "\<exists>b. b \<in> segment S a") prefer 2 apply blast
 apply (subgoal_tac "\<forall>b. b \<in> segment S a \<longrightarrow> False")
 apply blast apply (thin_tac "\<exists>b. b \<in> segment S a")
 apply (rule allI) apply (rule impI)
 apply (simp add:segment_def) apply (erule conjE)+
 apply (subgoal_tac "\<forall>x.  x <\<^sub>S a \<and> x \<in> carrier S \<longrightarrow> False")
 apply blast apply (thin_tac "\<exists>x.  x <\<^sub>S a \<and> x \<in> carrier S") 
 apply (rule allI) apply (rule impI) apply (erule conjE)+
apply (simp add:minimum_elem_def) 
 apply (subgoal_tac "a \<le>\<^sub>S b") prefer 2 apply simp
 apply (simp add:ord_neq_def) apply (erule conjE)
 apply (subgoal_tac "a \<le>\<^sub>S b") prefer 2 apply simp
 apply (subgoal_tac "ordered_set S")
 apply (frule_tac a = a and b = b in ordering_axiom2[of "S"], assumption+) 
 apply simp apply simp 
apply (simp add:well_ordered_set_def tordered_set_def)
done

lemma segment_empty_min:"\<lbrakk>well_ordered_set S; a \<in> carrier S; segment S a = {} \<rbrakk> \<Longrightarrow> minimum_elem S (carrier S) a"
apply (simp add:minimum_elem_def)
apply (rule ballI)
 apply (simp add:segment_def)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "tordered_set S")
 apply (frule_tac a = a and b = x in tordering_not [of "S"], assumption+)
 apply (thin_tac " \<not>  a \<le>\<^sub>S x")
 apply (subgoal_tac "x \<notin> carrier S")
 apply blast apply simp
apply (simp add:well_ordered_set_def)
done

lemma wellordered_ord_segment1_1:"\<lbrakk>well_ordered_set S; a \<in> carrier S; b \<in> carrier S; a \<le>\<^sub>S b \<rbrakk> \<Longrightarrow> segment (Iod S (segment S b)) a = segment S a"
apply (rule equalityI)
 apply (rule subsetI) 
 apply (simp add:segment_def Iod_def ord_neq_def)
apply (rule subsetI)
 apply (simp add:segment_def Iod_def ord_neq_def) apply (erule conjE)+
 apply (subgoal_tac "ordered_set S")
 apply (frule_tac a = x and b = a and c = b in ordering_axiom3 [of "S"], assumption+) apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule ordering_axiom2[of "S" "a" "b"], assumption+)
 apply simp
apply (simp add:well_ordered_set_def tordered_set_def)
done

lemma wellordered_ord_segment1_2:"\<lbrakk>well_ordered_set S; a \<in> carrier S; b \<in> carrier S; segment (Iod S (segment S b)) a = segment S a\<rbrakk> \<Longrightarrow> a \<le>\<^sub>S b"
apply (simp add:segment_def Iod_def ord_neq_def)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "tordered_set S")
 apply (frule tordering_not[of "S" "a" "b"], assumption+)
 apply (thin_tac "\<not>  a \<le>\<^sub>S b")
 apply (subgoal_tac "b \<in> {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and>  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S}") 
 apply (thin_tac "{x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and>  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S} =
       {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}")
 apply simp apply (simp add:ord_neq_def)
apply (simp add:well_ordered_set_def)
done

lemma wellordered_segment_segment2_1:"\<lbrakk>well_ordered_set S; b \<in> carrier S; a \<in> carrier S; segment (Iod S (segment S b)) a = segment S a\<rbrakk> \<Longrightarrow> (segment S a) \<subseteq>  (segment S b)" 
apply (rule subsetI)
 apply (simp add:segment_def Iod_def ord_neq_def)
 apply (erule conjE)+
 apply (subgoal_tac "x \<in> {x. x \<noteq> a \<and>  x <\<^sub>S a \<and> x \<noteq> b \<and>  x <\<^sub>S b \<and> x \<in> carrier S}") 
 apply (thin_tac " {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and>  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S} =
           {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}")
 apply simp apply (erule conjE)+ apply (simp add:ord_neq_def)
apply (frule sym)
 apply (thin_tac "{x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and>  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S} =
           {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}")
apply (subgoal_tac "x \<in> {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}")
apply (simp add:ord_neq_def)
apply (thin_tac "{x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S} =
           {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and>  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S}")
apply simp
done

lemma wellordered_segment_segment2_2:"\<lbrakk>well_ordered_set S; b \<in> carrier S; a \<in> carrier S; (segment S a) \<subseteq>  (segment S b)\<rbrakk> \<Longrightarrow> segment (Iod S (segment S b)) a = segment S a" 
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:segment_def Iod_def ord_neq_def)
apply (rule subsetI)
 apply (simp add:segment_def Iod_def ord_neq_def)
 apply (subgoal_tac "x \<in> {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}")
 apply (frule_tac A = "{x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}" and B = "{x.  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S}" and c = x in subsetD, assumption+)
 apply (thin_tac "x \<in> {x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}")
 apply simp
apply simp
done

constdefs
 SS :: "('a, 'mo) OrderedSet_scheme \<Rightarrow> 'a set OrderedSet"
 "SS S == \<lparr>carrier = {X. \<exists>a\<in>carrier S. X = segment S a}, ord_rel = {XX. XX \<in> {X. \<exists>a\<in>carrier S. X = segment S a} \<times> {X. \<exists>a\<in>carrier S. X = segment S a} \<and> ((fst XX) \<subseteq> (snd XX))}, ordering = \<lambda>X. \<lambda>Y. X \<subseteq> Y\<rparr>"

constdefs
 segmap::"('a, 'mo) OrderedSet_scheme \<Rightarrow> 'a \<Rightarrow> 'a set"
 "segmap S == \<lambda>x\<in>(carrier S). (segment S x)"

lemma ord_isom_segmap:"well_ordered_set S \<Longrightarrow> ord_isom S (SS S) (segmap S)"
apply (simp add:ord_isom_def)
apply (rule conjI)
 apply (simp add:segmap_def extensional_def)
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:SS_def) apply (simp add:segmap_def)
 apply blast
apply (rule conjI)
 apply (simp add:bij_to_def)
 apply (rule conjI)
 apply (rule surj_to_test)
 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:segmap_def SS_def) apply blast
 apply (rule ballI) apply (simp add:SS_def segmap_def)
 apply blast
 apply (simp add:inj_on_def) apply (rule ballI)+
 apply (rule impI) apply (simp add:segmap_def)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "tordered_set S")
 apply (simp add:tordered_set_def) apply (erule conjE)
 apply (subgoal_tac "x \<le>\<^sub>S y \<or>  y \<le>\<^sub>S x")
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a")
 apply (case_tac "x \<le>\<^sub>S y")
 apply (subgoal_tac "x <\<^sub>S y") prefer 2 apply (simp add:ord_neq_def)
 apply (subgoal_tac "x \<in> segment S x")
 apply (thin_tac "segment S x = segment S y")
 apply (simp add:segment_def ord_neq_def) 
 apply simp apply (thin_tac "segment S x = segment S y")
 apply (simp add:segment_def) 
apply simp
 apply (subgoal_tac "tordered_set S") 
 apply (frule_tac a = x and b = y in tordering_not[of "S"], assumption+)
 apply (subgoal_tac "y \<in> segment S x")
 apply (simp add:segment_def ord_neq_def)
 apply (thin_tac "segment S x = segment S y")
 apply (simp add:segment_def) apply (simp add:well_ordered_set_def)
 apply simp 
 apply (simp add:well_ordered_set_def)
apply (rule ballI)+ 
 apply (simp add:segmap_def SS_def ord_neq_def)
 apply auto
 apply (simp add:segment_def) apply (erule conjE)
 apply (simp add:ord_neq_def) apply (erule conjE)+
 apply (subgoal_tac "ordered_set S")
 apply (frule_tac a = x and b = a and c = b in ordering_axiom3 [of "S"],
     assumption+) apply simp 
 apply (rule contrapos_pp, simp+)
 apply (frule_tac a = a and b = b in ordering_axiom2 [of "S"], assumption+)
 apply simp 
apply (simp add:well_ordered_set_def tordered_set_def)
apply (subgoal_tac "a <\<^sub>S b")
 apply (subgoal_tac "a \<in> segment S a")
 apply (thin_tac "segment S a = segment S b")
 apply (simp add:segment_def ord_neq_def)
 apply simp
 apply (simp add:segment_def)
 apply (simp add:ord_neq_def) 
 apply (subgoal_tac "segment S a \<subset> segment S b")
 prefer 2 apply (simp add:psubset_def)
 apply blast
apply (thin_tac "segment S a \<subseteq> segment S b")
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "tordered_set S")
 apply (frule_tac a = a and b = b in tordering_not[of "S"], assumption+)
 apply (subgoal_tac "b \<in> segment S a")
 apply (frule_tac A = "segment S a" and B = "segment S b" in psubset_imp_subset)
 apply (frule_tac A = "segment S a" and B = "segment S b" and c = b in subsetD, assumption+)
 apply (simp add:segment_def ord_neq_def)
 apply (simp add:segment_def)
apply (simp add:well_ordered_set_def)
done

lemma not_ordequiv_segment:"\<lbrakk>well_ordered_set S; a \<in> carrier S\<rbrakk> \<Longrightarrow>
 \<not> ord_equiv S (Iod S (segment S a))"
apply (rule contrapos_pp, simp+)
 apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>f. ord_isom S (Iod S (segment S a)) f \<longrightarrow> False")
 apply blast apply (thin_tac "\<exists>f. ord_isom S (Iod S (segment S a)) f")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "f \<in> carrier S \<rightarrow> carrier (Iod S (segment S a))") 
 apply (frule_tac f = f and A = " carrier S" and B = "carrier (Iod S (segment S a))" and x = a in funcset_mem, assumption+)
 apply (thin_tac "f \<in> carrier S \<rightarrow> carrier (Iod S (segment S a))")
 apply (subgoal_tac "(segment S a) \<subseteq> carrier S")
 apply (frule_tac f = f in well_ordered_to_subset [of "S" "segment S a"], assumption+)
 apply (subgoal_tac "a \<le>\<^sub>S (f a)")
 apply (thin_tac "\<forall>a. a \<in> carrier S \<longrightarrow>  a \<le>\<^sub>S (f a)")
 apply (thin_tac "ord_isom S (Iod S (segment S a)) f")
 apply (simp add:Iod_def) apply (thin_tac "segment S a \<subseteq> carrier S")
 apply (simp add:segment_def)
 apply (erule conjE) apply (simp add:ord_neq_def)
 apply (erule conjE)
 apply (subgoal_tac "ordered_set S")
 apply (frule_tac a = "f a" and b = a in ordering_axiom2, assumption+)
 apply simp apply (simp add:well_ordered_set_def tordered_set_def)
 apply simp
 apply (rule subsetI) 
  apply (thin_tac "ord_isom S (Iod S (segment S a)) f")
  apply (thin_tac "f a \<in> carrier (Iod S (segment S a))")
 apply (simp add:segment_def)
 apply (simp add:ord_isom_def)
done

lemma subset_well_ordered:"\<lbrakk>well_ordered_set S; T \<subseteq> carrier S \<rbrakk> \<Longrightarrow>
  well_ordered_set (Iod S T)"
apply (subst well_ordered_set_def)
 apply (rule conjI)
 apply (simp add:tordered_set_def)
 apply (rule conjI)
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (erule conjE)+
 apply (rule ordered_set_Iod [of "S" "T"], assumption+)
apply (rule ballI)+
 apply (simp add:Iod_def)
 apply (frule_tac c = a in subsetD [of "T" "carrier S"], assumption+)
 apply (frule_tac c = b in subsetD [of "T" "carrier S"], assumption+)
 apply (simp add:well_ordered_set_def tordered_set_def)
apply (simp add:Iod_def minimum_elem_def)
 apply (subgoal_tac "\<forall>Y. Y \<subseteq> T \<longrightarrow> Y \<subseteq> carrier S")
 apply (simp add:well_ordered_set_def minimum_elem_def)
apply (rule allI) apply (rule impI)
 apply (rule subset_trans[of _ "T" "carrier S"], assumption+)
done

lemma segment_well_ordered_set:"\<lbrakk>well_ordered_set S; a \<in> carrier S \<rbrakk> \<Longrightarrow>
 well_ordered_set (Iod S (segment S a))"
apply (rule subset_well_ordered [of "S" "segment S a"], assumption+)
 apply (rule subsetI)
 apply (simp add:segment_def)
done

lemma segment_unique1:"\<lbrakk>well_ordered_set S; a \<in> carrier S; b \<in> carrier S;
a <\<^sub>S b\<rbrakk> \<Longrightarrow> \<not> ord_equiv (Iod S (segment S b)) (Iod S (segment S a)) "
apply (frule segment_well_ordered_set [of "S" "b"], assumption+)
 apply (subgoal_tac "a \<in> carrier (Iod S (segment S b))")
 apply (frule not_ordequiv_segment [of "Iod S (segment S b)" "a"], assumption+)
 apply (subgoal_tac "(Iod (Iod S (segment S b)) (segment (Iod S (segment S b)) a))  = (Iod S (segment S a))") apply simp
prefer 2 apply (simp add:Iod_def segment_def)
apply (thin_tac "\<not> ord_equiv (Iod S (segment S b))
          (Iod (Iod S (segment S b)) (segment (Iod S (segment S b)) a))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "a \<in> carrier (Iod S (segment S b))")
apply (simp add:ord_neq_def) apply (erule conjE)
 apply (frule wellordered_ord_segment1_1 [of "S" "a" "b"], assumption+)
 apply simp
 apply (thin_tac "segment (Iod S (segment S b)) a = segment S a")
 apply (rule Iod_sub_sub [of "S" "segment S a" "segment S b"])
 apply (simp add:well_ordered_set_def tordered_set_def)
apply (rule subsetI)
 apply (simp add:segment_def) apply (erule conjE) 
 apply (subgoal_tac "a <\<^sub>S b") 
 apply (rule_tac a = x and b = a and c = b in ord_neq_trans [of "S"])
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply assumption+ apply (simp add:ord_neq_def)
apply (rule subsetI)
 apply (simp add:segment_def)
done
 
lemma segment_unique:"\<lbrakk>well_ordered_set S; a \<in> carrier S; b \<in> carrier S;
ord_equiv (Iod S (segment S a)) (Iod S (segment S b)) \<rbrakk> \<Longrightarrow> a = b"
 apply (subgoal_tac "ordered_set (Iod S (segment S a))")
 apply (subgoal_tac "ordered_set (Iod S (segment S b))")
apply (subgoal_tac "ordered_set S") 
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "a \<le>\<^sub>S b \<or> b \<le>\<^sub>S a")
apply (case_tac "a \<le>\<^sub>S b")
 apply (frule segment_unique1 [of "S" "a" "b"], assumption+)
 apply (simp add:ord_neq_def)
 apply (frule ord_equiv_sym [of "Iod S (segment S a)" "Iod S (segment S b)"],
           assumption+) apply simp
 apply simp apply (subgoal_tac "b <\<^sub>S a")
 apply (frule segment_unique1 [of "S" "b" "a"], assumption+)
 apply simp
 apply (simp add:ord_neq_def) apply (rule not_sym, assumption+)
apply (simp add:well_ordered_set_def tordered_set_def)
apply (simp add:well_ordered_set_def tordered_set_def)
 apply (rule ordered_set_Iod)
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (rule subsetI) apply (simp add:segment_def)
 apply (rule ordered_set_Iod)
 apply (simp add:well_ordered_set_def tordered_set_def)
 apply (rule subsetI) apply (simp add:segment_def)
done

lemma segmentTr:"\<lbrakk>well_ordered_set S; T \<subseteq> carrier S; \<forall>b \<in> T. (\<forall>x.  (x <\<^sub>S b \<and> x \<in> (carrier S) \<longrightarrow> x \<in> T))\<rbrakk> \<Longrightarrow> (T = carrier S) \<or> (\<exists>a. a \<in> (carrier S) \<and> T = segment S a)"
apply (case_tac "(carrier S) - T = {}")
 apply (subgoal_tac "T = carrier S") apply simp
 apply blast
apply (unfold well_ordered_set_def) apply (erule conjE)+
 apply (subgoal_tac "\<exists>x. minimum_elem S (carrier S - T) x")
 apply (thin_tac "\<forall>X. X \<subseteq> carrier S \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem S X x)")
 apply (thin_tac "carrier S - T \<noteq> {}")
 apply (subgoal_tac "T \<noteq> carrier S") apply simp
 apply (thin_tac "T \<noteq> carrier S")
 apply (subgoal_tac "\<forall>x. minimum_elem S (carrier S - T) x \<longrightarrow> (\<exists>a. a \<in> carrier S \<and> T = segment S a)")
 apply blast apply (thin_tac "\<exists>x. minimum_elem S (carrier S - T) x")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "x \<in> carrier S \<and> T = segment S x")
 apply blast
 apply (rule conjI) apply (unfold minimum_elem_def) apply (erule conjE)
 apply (thin_tac "\<forall>xa\<in>carrier S - T.  x \<le>\<^sub>S xa")
 apply blast
 apply (rule equalityI)
 apply (rule subsetI) apply (erule conjE)
 apply (subgoal_tac "xa \<noteq> x")
 apply (subgoal_tac "xa \<le>\<^sub>S x \<or> x \<le>\<^sub>S xa")
 prefer 2 apply (thin_tac "\<forall>b\<in>T. \<forall>x.  x <\<^sub>S b \<and> x \<in> carrier S \<longrightarrow> x \<in> T")
 apply (thin_tac "\<forall>xa\<in>carrier S - T.  x \<le>\<^sub>S xa")
apply (simp add:tordered_set_def) apply (erule conjE)+
 apply (frule_tac A = T and B = "carrier S" and c = xa in subsetD, assumption+)
 apply simp
 apply (rename_tac y v) 
 apply (case_tac "v <\<^sub>S y") apply (unfold tordered_set_def)
 apply (erule conjE)+
 apply (rule_tac a = v and b = y in segment_inc [of "S"], assumption+)
 apply (rule subsetD, assumption+) apply blast apply assumption
 apply (unfold ord_neq_def) 
 apply (subgoal_tac "y \<in> T")
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. ( x \<le>\<^sub>S b \<and> x \<noteq> b) \<and> x \<in> carrier S \<longrightarrow> x \<in> T")
 apply (thin_tac " ordered_set S \<and> (\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a)")
 apply (thin_tac "\<forall>x\<in>carrier S - T.  y \<le>\<^sub>S x")
 apply blast
 apply (subgoal_tac "(y \<le>\<^sub>S v \<and> y \<noteq> v) \<and> y \<in> carrier S")
 apply (thin_tac "ordered_set S \<and> (\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a)")
 apply (thin_tac "\<forall>x\<in>carrier S - T.  y \<le>\<^sub>S x")
 apply blast
 apply (rule conjI)
 apply (rule conjI) 
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. ( x \<le>\<^sub>S b \<and> x \<noteq> b) \<and> x \<in> carrier S \<longrightarrow> x \<in> T")
 apply (thin_tac "ordered_set S \<and>
             (\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a)")
 apply (thin_tac "\<forall>x\<in>carrier S - T.  y \<le>\<^sub>S x")
 apply simp apply (rule not_sym, assumption+)
 apply blast apply blast
prefer 2 apply blast
prefer 2 
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. ( x \<le>\<^sub>S b \<and> x \<noteq> b) \<and> x \<in> carrier S \<longrightarrow> x \<in> T") 
 apply (thin_tac "ordered_set S \<and> (\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a)")
 apply (subgoal_tac "carrier S - T \<subseteq> carrier S")
 apply blast 
 apply (rule subsetI)
 apply (thin_tac "\<forall>X. X \<subseteq> carrier S \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>xa\<in>X.  x \<le>\<^sub>S xa))") apply simp
 apply (rule subsetI) 
apply (rename_tac x y) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a")
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. ( x \<le>\<^sub>S b \<and> x \<noteq> b) \<and> x \<in> carrier S \<longrightarrow> x \<in> T")
 apply (rule contrapos_pp, simp+)
 apply (simp add:segment_def)
 apply (subgoal_tac "y \<in> carrier S - T")
 apply (subgoal_tac "x \<le>\<^sub>S y")
 apply (thin_tac "\<forall>xa\<in>carrier S - T.  x \<le>\<^sub>S xa")
 apply (erule conjE)+ apply (unfold ord_neq_def) apply (erule conjE)
 apply (frule_tac a = y and b = x in ordering_axiom2, assumption+)
 apply simp
 apply simp
apply (thin_tac "\<forall>xa\<in>carrier S - T.  x \<le>\<^sub>S xa")
 apply (erule conjE)+
 apply blast
done

constdefs
 Twell :: "[('a, 'mo) OrderedSet_scheme, ('b, 'mo) OrderedSet_scheme] \<Rightarrow> 'a \<Rightarrow> 'b"
 "Twell S T  == \<lambda>a\<in> carrier S. SOME x. x\<in>carrier T \<and> ord_equiv (Iod S (segment S a)) (Iod T (segment T x))"

lemma Twell_func:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T. ord_equiv (Iod S (segment S a)) (Iod T (segment T b))\<rbrakk> \<Longrightarrow>
Twell S T \<in> carrier S \<rightarrow> carrier T" 
apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:Twell_def)
 apply (rule someI2_ex) apply blast apply simp
done

lemma Twell_equiv:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T. ord_equiv (Iod S (segment S a)) (Iod T (segment T b)); x \<in> carrier S \<rbrakk> \<Longrightarrow>  ord_equiv (Iod S (segment S x)) (Iod T (segment T ((Twell S T) x)))"
apply (subgoal_tac "\<exists>b \<in> carrier T.  ord_equiv (Iod S (segment S x)) (Iod T (segment T b))") prefer 2 apply simp
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
              ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
apply (simp add:Twell_def)
apply (rule someI2_ex)
 apply blast apply simp
done

lemma Twell_inj:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))\<rbrakk> \<Longrightarrow>
inj_on (Twell S T)  (carrier S)" 
 apply (simp add:inj_on_def)
 apply (rule ballI)+ apply (rule impI) 
 apply (frule_tac x = x in Twell_equiv [of "S" "T"], assumption+)
 apply (frule_tac x = y in Twell_equiv [of "S" "T"], assumption+) apply simp
 apply (subgoal_tac "ord_equiv (Iod S (segment S x)) (Iod S (segment S y))")
 apply (simp add:segment_unique)
apply (subgoal_tac "ordered_set (Iod S (segment S x))")
 apply (subgoal_tac "ordered_set (Iod S (segment S y))")
 apply (subgoal_tac "ordered_set (Iod T (segment T (Twell S T y)))")
 apply (frule_tac D = "Iod S (segment S y)" and E = "Iod T (segment T (Twell S T y))" in ord_equiv_sym, assumption+) 
 apply (thin_tac "ord_equiv (Iod S (segment S y)) (Iod T (segment T (Twell S T y)))")
 apply (rule_tac D = "Iod S (segment S x)" and E = "Iod T (segment T (Twell S T y))" and F = "Iod S (segment S y)" in ord_equiv_trans, assumption+)
 apply (rule ordered_set_Iod)
  apply (simp add:well_ordered_set_def tordered_set_def)
  apply (rule subsetI) apply (simp add:segment_def)
 apply (rule ordered_set_Iod)
  apply (simp add:well_ordered_set_def tordered_set_def)
  apply (rule subsetI) apply (simp add:segment_def)
 apply (rule ordered_set_Iod)
  apply (simp add:well_ordered_set_def tordered_set_def)
  apply (rule subsetI) apply (simp add:segment_def)
done

lemma Twell_ord_inj:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))\<rbrakk> \<Longrightarrow>
ord_inj S T (Twell S T)" 
apply (simp add:ord_inj_def)
 apply (rule conjI)
 apply (simp add:Twell_def extensional_def)
 apply (simp add:Twell_func)
apply (rule conjI)
 apply (simp add:Twell_inj)
apply (rule ballI)+
apply auto 
 apply (frule Twell_func [of "S" "T"], assumption+)
 apply (frule_tac x = b in Twell_equiv [of "S" "T"], assumption+)
 apply (frule_tac x = a in Twell_equiv [of "S" "T"], assumption+)
 apply (subgoal_tac "\<exists>f. ord_isom (Iod S (segment S b))
                  (Iod T (segment T (Twell S T b))) f") 
 prefer 2 apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>f. ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b))) f \<longrightarrow> Twell S T a <\<^sub>T (Twell S T b)") 
 apply blast apply (thin_tac "\<exists>f. ord_isom (Iod S (segment S b))
                  (Iod T (segment T (Twell S T b))) f")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "a \<in> carrier (Iod S (segment S b))") 
 apply (subgoal_tac "f a \<in> carrier (Iod T (segment T (Twell S T b)))")
 prefer 2 apply (simp add:ord_isom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
 apply (frule_tac S = S and a = b in segment_well_ordered_set, assumption+)
 apply (frule_tac S = "Iod S (segment S b)" and T = "Iod T (segment T (Twell S T b))" and f = f in ord_isom_segment_segment)
 apply (rule_tac S = T and a = "Twell S T b" in segment_well_ordered_set, assumption+) apply (simp add:funcset_mem) apply assumption apply simp
 apply (subgoal_tac "a \<le>\<^sub>S b")
 apply (frule_tac a = a and b = b in wellordered_ord_segment1_1 [of "S"],
 assumption+) apply simp
 apply (thin_tac "segment (Iod S (segment S b)) a = segment S a")
 apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (subgoal_tac "segment S a \<subseteq> segment S b")
 apply (frule_tac S = "segment S a" and T = "segment S b" in Iod_sub_sub [of "S"], assumption+) 
 apply (rule subsetI)
 apply (simp add:segment_def) apply simp
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac " Iod (Iod S (segment S b)) (segment S a) = Iod S (segment S a)")
 apply (subgoal_tac "(segment (Iod T (segment T (Twell S T b))) (f a)) \<subseteq> segment T (Twell S T b)")
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (frule_tac S = "segment (Iod T (segment T (Twell S T b))) (f a)" and T = "segment T (Twell S T b)" in Iod_sub_sub) apply assumption+
 apply (rule subsetI)  apply (simp add:segment_def)
  apply simp
  apply (thin_tac "Iod (Iod T (segment T (Twell S T b))) (segment (Iod T (segment T (Twell S T b))) (f a)) = Iod T (segment (Iod T (segment T (Twell S T b))) (f a))")
 apply (subgoal_tac "(segment (Iod T (segment T (Twell S T b))) (f a)) = 
  segment T (f a)") apply simp
 apply (thin_tac "segment (Iod T (segment T (Twell S T b))) (f a) = segment T (f a)")
 apply (subgoal_tac " ord_equiv (Iod T (segment T (Twell S T a))) (Iod T (segment T (f a)))")
 apply (subgoal_tac "f a \<in> carrier T")
 prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "Twell S T a \<in> carrier T")
 prefer 2 apply (simp add:funcset_mem)
 apply (frule_tac  a = "Twell S T a" and b = "f a" in segment_unique [of "T"],
          assumption+)
 apply simp
 apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b))) f")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (f a)))")
 apply (thin_tac " ord_equiv (Iod T (segment T (f a))) (Iod T (segment T (f a)))")
 apply (thin_tac "segment T (f a) \<subseteq> segment T (Twell S T b)")
 apply (thin_tac "segment S a \<subseteq> segment S b")
 apply (thin_tac "a \<in> carrier (Iod S (segment S b))")
 apply (simp add:Iod_def segment_def)
apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (thin_tac " ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b))) f")
 apply (frule_tac a = a in segment_well_ordered_set [of "S"], assumption+)
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (frule_tac x = a in funcset_mem [of "Twell S T" "carrier S" "carrier T"], assumption+)
 apply (frule_tac a = "Twell S T a"  in segment_well_ordered_set [of "T"], assumption+)
 apply (frule_tac S = "Iod S (segment S a)" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod T (segment T (Twell S T a))" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod S (segment S a)" and E = "Iod T (segment T (Twell S T a))" in ord_equiv_sym, assumption+) 
 apply (rule_tac D = "Iod T (segment T (Twell S T a))" and E = "Iod S (segment S a)" and F = "Iod T (segment T (f a))" in ord_equiv_trans, assumption+)
 apply (rule well_ordered_set_is_ordered_set)
 apply (rule segment_well_ordered_set, assumption+)
  apply (simp add:Iod_def segment_def) apply assumption+
apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))  f")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a))
           (Iod T (segment (Iod T (segment T (Twell S T b))) (f a)))")
 apply (thin_tac "segment (Iod T (segment T (Twell S T b))) (f a)
          \<subseteq> segment T (Twell S T b)")
 apply (thin_tac "a \<in> carrier (Iod S (segment S b))")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule equalityI)
 apply (rule subsetI)
 apply simp
 apply (rule subsetI) apply simp
 apply (thin_tac "{x.  x \<le>\<^sub>S a \<and> x \<noteq> a \<and> x \<in> carrier S}
          \<subseteq> {x.  x \<le>\<^sub>S b \<and> x \<noteq> b \<and> x \<in> carrier S}")
 apply (erule conjE)+
 apply (frule_tac a = x and b = "f a" and c = "Twell S T b" in ordering_axiom3 [of "T"], assumption+)
 apply (simp add:funcset_mem) apply assumption+ apply simp
 apply (rule contrapos_pp, simp+) 
 apply (frule_tac a = "Twell S T b" and b = "f a" in ordering_axiom2 [of "T"],
             assumption+) apply simp
 apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac " ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b))) f")
 apply (thin_tac "a \<in> carrier (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod (Iod T (segment T (Twell S T b))) (segment (Iod T (segment T (Twell S T b))) (f a)))")
 apply (thin_tac "segment S a \<subseteq> segment S b")
 apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (thin_tac " \<forall>a\<in>carrier S.  \<exists>b \<in> carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b))) f")
 apply (thin_tac "f a \<in> carrier (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "a \<in> carrier (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac " ord_equiv (Iod (Iod S (segment S b)) (segment S a))
           (Iod (Iod T (segment T (Twell S T b)))
             (segment (Iod T (segment T (Twell S T b))) (f a)))")
 apply (rule subsetI)
 apply (simp add:segment_def) apply (erule conjE)
 apply (rule ord_neq_trans, assumption+)
 apply (simp add:ord_neq_def)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ord_isom (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))  f")
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (frule_tac x = b in Twell_equiv [of "S" "T"], assumption+)
 apply (frule_tac x = a in Twell_equiv [of "S" "T"], assumption+)
 apply (frule_tac a = b in segment_well_ordered_set [of "S"], assumption+)
 apply (frule_tac S = "Iod S (segment S b)" in well_ordered_set_is_ordered_set)
 apply (subgoal_tac "Twell S T b \<in> carrier T")
 apply (frule_tac a = "Twell S T b" in segment_well_ordered_set [of "T"], assumption+)
 apply (frule_tac D = "Iod S (segment S b)" and E = "Iod T (segment T (Twell S T b))" in ord_equiv_sym)  
 apply (simp add:well_ordered_set_is_ordered_set) apply assumption
 apply (thin_tac "ord_equiv (Iod S (segment S b)) (Iod T (segment T (Twell S T b)))")
 apply (subgoal_tac "\<exists>g. ord_isom (Iod T (segment T (Twell S T b))) (Iod S (segment S b)) g")
 prefer 2 apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>g. ord_isom (Iod T (segment T (Twell S T b))) (Iod S (segment S b)) g \<longrightarrow> a <\<^sub>S b")
 apply blast apply (thin_tac "\<exists>g. ord_isom (Iod T (segment T (Twell S T b)))
                  (Iod S (segment S b)) g")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "Twell S T a \<in> carrier (Iod T (segment T (Twell S T b)))")
  apply (frule_tac S = "Iod T (segment T (Twell S T b))" and T = "Iod S (segment S b)" and f = g and a = "Twell S T a" in ord_isom_segment_segment, assumption+)
 apply (subgoal_tac "Iod (Iod T (segment T (Twell S T b))) (segment (Iod T (segment T (Twell S T b))) (Twell S T a)) = Iod T (segment T (Twell S T a))") 
 apply simp
 apply (subgoal_tac "Iod (Iod S (segment S b)) (segment (Iod S (segment S b)) (g (Twell S T a))) = Iod S (segment S (g (Twell S T a)))")
 apply simp
 apply (thin_tac "Iod (Iod S (segment S b)) (segment (Iod S (segment S b)) (g (Twell S T a))) = Iod S (segment S (g (Twell S T a)))")
 apply (thin_tac "Iod (Iod T (segment T (Twell S T b))) (segment (Iod T (segment T (Twell S T b))) (Twell S T a)) = Iod T (segment T (Twell S T a))")
 apply (subgoal_tac " g (Twell S T a) = a") 
 apply (subgoal_tac "g (Twell S T a) <\<^sub>S b") apply simp
 apply (thin_tac "g (Twell S T a) = a")
 apply (subgoal_tac "g (Twell S T a) \<in> carrier (Iod S (segment S b))")
 apply (thin_tac "\<forall>a\<in>carrier S.  \<exists>b \<in> carrier T. 
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "ordered_set (Iod S (segment S b))")
 apply (thin_tac "Twell S T b \<in> carrier T")
 apply (thin_tac " ord_equiv (Iod T (segment T (Twell S T b))) (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_isom (Iod T (segment T (Twell S T b))) (Iod S (segment S b)) g")
 apply (thin_tac "Twell S T a \<in> carrier (Iod T (segment T (Twell S T b)))")
 apply (thin_tac " ord_equiv (Iod T (segment T (Twell S T a)))
           (Iod S (segment S (g (Twell S T a))))")
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "ordered_set (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod T (segment T (Twell S T b))) (Iod S (segment S b))")
 apply (thin_tac " ord_equiv (Iod T (segment T (Twell S T a))) (Iod S (segment S (g (Twell S T a))))")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod T (segment T (Twell S T b))) (Iod S (segment S b))")
 apply (thin_tac "ordered_set (Iod S (segment S b))")
 apply (frule_tac a = "Twell S T a" in segment_well_ordered_set [of "T"])
 apply (simp add:Iod_def segment_def)
 apply (frule_tac S = "Iod T (segment T (Twell S T a))" in well_ordered_set_is_ordered_set)
 apply (frule_tac a = a in segment_well_ordered_set [of "S"], assumption+)
 apply (frule_tac S = "Iod S (segment S a)" in well_ordered_set_is_ordered_set)
 apply (subgoal_tac "g (Twell S T a) \<in> carrier S")
 apply (frule_tac a = "g (Twell S T a)" in segment_well_ordered_set [of "S"], assumption+)
 apply (frule_tac S = "Iod S (segment S (g (Twell S T a)))" in well_ordered_set_is_ordered_set)
apply (frule_tac D = "Iod S (segment S a)" and E = "Iod T (segment T (Twell S T a))" and F = "Iod S (segment S (g (Twell S T a)))" in ord_equiv_trans, assumption+)
 apply (subgoal_tac "a = g (Twell S T a)") apply (rule sym, assumption+)
 apply (rule segment_unique, assumption+)
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (frule_tac f = g and A = "carrier (Iod T (segment T (Twell S T b)))" and B = "carrier (Iod S (segment S b))" and x = "Twell S T a" in funcset_mem, assumption+) 
apply (thin_tac "\<forall>a\<in>carrier (Iod T (segment T (Twell S T b))).
             \<forall>ba\<in>carrier (Iod T (segment T (Twell S T b))).
 a <\<^sub>(Iod T (segment T (Twell S T b))) ba = g a <\<^sub>(Iod S (segment S b)) (g ba)")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "ordered_set (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod T (segment T (Twell S T b))) (Iod S (segment S b))")
 apply (thin_tac "ord_equiv (Iod T (segment T (Twell S T a)))
 (Iod (Iod S (segment S b)) (segment (Iod S (segment S b)) (g (Twell S T a))))")
 apply (thin_tac "Iod (Iod T (segment T (Twell S T b)))
           (segment (Iod T (segment T (Twell S T b))) (Twell S T a)) =
          Iod T (segment T (Twell S T a))")
 apply (subgoal_tac "g (Twell S T a) \<in> segment S b")
 apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (subgoal_tac "segment S (g (Twell S T a)) \<subseteq> segment S b")  
 apply (subgoal_tac "segment (Iod S (segment S b)) (g (Twell S T a)) = 
                 segment S (g (Twell S T a))")
 apply simp
 apply (frule_tac S = "segment S (g (Twell S T a))" and T = "segment S b" in Iod_sub_sub [of "S"], assumption+) 
 apply (rule subsetI) apply (simp add:segment_def)  apply assumption
apply (thin_tac "ord_isom (Iod T (segment T (Twell S T b))) (Iod S (segment S b)) g")
 apply (rule equalityI)
 apply (rule subsetI)
  apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule subsetI)
  apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
  apply (frule_tac a = x and b = "g (Twell S T a)" and c = b in ordering_axiom3
 [of "S"], assumption+) apply simp 
 apply (rule contrapos_pp, simp+) 
  apply (frule_tac a = b and b = "g (Twell S T a)" in ordering_axiom2 
 [of "S"], assumption+) apply simp   
apply (rule subsetI)
 apply (simp add:segment_def) apply (erule conjE)+
 apply (rule_tac a = x and b = "g (Twell S T a)" and c = b in ord_neq_trans [of "S"], assumption+) 
apply (simp add:ord_isom_def) apply (erule conjE)+ 
 apply (thin_tac "\<forall>a\<in>carrier (Iod T (segment T (Twell S T b))).
 \<forall>ba\<in>carrier (Iod T (segment T (Twell S T b))). a <\<^sub>(Iod T (segment T (Twell S T b))) ba =  g a <\<^sub>(Iod S (segment S b)) (g ba)")
 apply (frule_tac f = g and A = "carrier (Iod T (segment T (Twell S T b)))" and B = " carrier (Iod S (segment S b))" and x = "Twell S T a" in funcset_mem, assumption+)
 apply (simp add:Iod_def)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod T (segment T (Twell S T b))) (Iod S (segment S b))")
 apply (thin_tac "ord_equiv
           (Iod (Iod T (segment T (Twell S T b)))
             (segment (Iod T (segment T (Twell S T b))) (Twell S T a)))
           (Iod (Iod S (segment S b))
             (segment (Iod S (segment S b)) (g (Twell S T a))))")
 apply (thin_tac " ord_isom (Iod T (segment T (Twell S T b))) (Iod S (segment S b)) g")
 apply (subgoal_tac "segment (Iod T (segment T (Twell S T b))) (Twell S T a) =
     segment T (Twell S T a)") apply simp
 apply (thin_tac "segment (Iod T (segment T (Twell S T b))) (Twell S T a) =
             segment T (Twell S T a)")
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (subgoal_tac "segment T (Twell S T a) \<subseteq> segment T (Twell S T b)")
 apply (rule_tac S = "segment T (Twell S T a)" and T = "segment T (Twell S T b)" in Iod_sub_sub [of "T"], assumption+)
apply (rule subsetI)
 apply (simp add:segment_def)
apply (thin_tac "ordered_set (Iod S (segment S b))")
apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule subsetI) apply simp apply (erule conjE)+
 apply (frule_tac a = x and b = "Twell S T a" and c = "Twell S T b" in ordering_axiom3 [of "T"], assumption+) apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac a = "Twell S T a" and b = "Twell S T b" in ordering_axiom2 [of "T"], assumption+) apply simp
apply (thin_tac "ordered_set (Iod S (segment S b))")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule equalityI) 
 apply (rule subsetI) apply simp
 apply (rule subsetI) apply simp apply (erule conjE)+
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (frule_tac a = x and b = "Twell S T a" and c = "Twell S T b" in ordering_axiom3 [of "T"], assumption+) apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac a = "Twell S T a" and b = "Twell S T b" in ordering_axiom2 [of "T"], assumption+) apply simp
apply (frule Twell_func [of "S" "T"], assumption+)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_equiv (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ordered_set (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod S (segment S b))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T b)))")
 apply (thin_tac "ord_equiv (Iod T (segment T (Twell S T b))) (Iod S (segment S b))")
 apply (thin_tac "ord_isom (Iod T (segment T (Twell S T b))) (Iod S (segment S b)) g")
 apply (frule_tac f = "Twell S T" and A = "carrier S" and B = "carrier T" and
 x = a in funcset_mem, assumption+)
 apply (thin_tac "Twell S T \<in> carrier S \<rightarrow> carrier T")
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (frule Twell_func [of "S" "T"], assumption+)
 apply (simp add:funcset_mem)
done

lemma ord_isom_induced_by_Twell:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))\<rbrakk> \<Longrightarrow> ord_isom  S (Iod T ((Twell S T) ` (carrier S))) (restrict (Twell S T) (carrier S))"
apply (frule Twell_ord_inj [of "S" "T"], assumption+)
apply (simp add:ord_isom_induced_by_inj [of "S" "T" "Twell S T"])
done

lemma ord_isom_Twell_segment:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b)); a\<in>carrier S\<rbrakk> \<Longrightarrow> ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) (restrict (Twell S T) (segment S a))"
apply (frule Twell_equiv [of "S" "T" "a"], assumption+)
 apply (frule Twell_ord_inj [of "S" "T"], assumption+)
 apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>f. ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f \<longrightarrow> ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))  (restrict (Twell S T) (segment S a))")
 apply blast
 apply (thin_tac "\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (rule allI) apply (rule impI)
apply (subst ord_isom_def)
 apply (rule conjI)
 apply (simp add:Iod_def extensional_def)
apply (rule conjI)
 apply (simp add:ord_inj_def) apply (erule conjE)+
 apply (rule univar_func_test) apply (rule ballI)
 apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (simp add:Iod_def)
 apply (simp add:segment_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply (rule conjI)
 apply (simp add:bij_to_def)
 apply (rule conjI)
 apply (rule surj_to_test)
 apply (rule univar_func_test) apply (rule ballI)
 apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (simp add:Iod_def)
 apply (simp add:segment_def) apply (erule conjE) apply (simp add:ord_inj_def)
 apply (erule conjE)+ apply (simp add:funcset_mem)
apply (rule ballI)
 apply (subgoal_tac "\<exists>x\<in>carrier (Iod S (segment S a)). b = f x")
 apply (subgoal_tac "\<forall>x\<in>carrier (Iod S (segment S a)). b = f x \<longrightarrow> (\<exists>aa\<in>carrier (Iod S (segment S a)). (if aa \<in> segment S a then Twell S T aa else arbitrary) = b)") apply blast apply (thin_tac "\<exists>x\<in>carrier (Iod S (segment S a)). b = f x") apply (rule ballI) apply (rule impI) 
 apply (subgoal_tac "ord_equiv (Iod T (segment T (Twell S T x))) (Iod T (segment T b))")
 apply (frule_tac a = "Twell S T x" and b = b in segment_unique [of "T" ])
 apply (simp add:ord_inj_def) apply (erule conjE)+
 apply (subgoal_tac "x \<in> carrier S") apply (simp add:funcset_mem)
 apply (simp add:Iod_def segment_def) apply (simp add:Iod_def segment_def)
 apply assumption
 apply (subgoal_tac "(if x \<in> segment S a then Twell S T x else arbitrary)  = b") apply blast
 apply simp apply (simp add:Iod_def)
 apply (frule segment_well_ordered_set [of "S" "a"], assumption+)
 apply (subgoal_tac "Twell S T a \<in> carrier T")
 apply (frule segment_well_ordered_set [of "T" "Twell S T a"], assumption+)
 apply (frule_tac f = f and a = x in ord_isom_segment_segment [of "Iod S (segment S a)" "Iod T (segment T (Twell S T a))"], assumption+) apply simp
 apply (subgoal_tac "segment (Iod S (segment S a)) x = segment S x")
 prefer 2 apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))  f") 
 apply (thin_tac " well_ordered_set (Iod S (segment S a))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ord_equiv (Iod (Iod S (segment S a)) (segment (Iod S (segment S a)) x)) (Iod (Iod T (segment T (Twell S T a))) (segment (Iod T (segment T (Twell S T a))) (f x)))")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule equalityI)
 apply (rule subsetI) apply simp
 apply (rule subsetI) apply simp apply (erule conjE)+
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (frule_tac a = xa and b = x and c = a in ordering_axiom3 [of "S"], assumption+) apply simp apply (rule contrapos_pp, simp+)
 apply (frule_tac a = x and b = a in ordering_axiom2 [of "S"], assumption+)
 apply simp
apply simp
 apply (subgoal_tac "segment (Iod T (segment T (Twell S T a))) (f x) = 
   segment T (f x)") apply simp
 apply (subgoal_tac "segment S x \<subseteq> segment S a")
 apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (frule_tac  S = "segment S x" in Iod_sub_sub [of "S" _  "segment S a"], assumption+)
 apply (rule subsetI) 
 apply (simp add:segment_def) apply simp
 apply (thin_tac "segment S x \<subseteq> segment S a")
 apply (subgoal_tac "segment T (f x) \<subseteq> segment T (Twell S T a)")
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (frule_tac S = "segment T (f x)" in Iod_sub_sub [of "T" _ "segment T (Twell S T a)"], assumption+)
 apply (rule subsetI) 
 apply (simp add:segment_def) apply simp
  apply (thin_tac "segment (Iod S (segment S a)) x = segment S x")
  apply (thin_tac "segment (Iod T (segment T (Twell S T a))) (f x) = segment T (f x)")
  apply (thin_tac "Iod (Iod S (segment S a)) (segment S x) = Iod S (segment S x)")
  apply (thin_tac "Iod (Iod T (segment T (Twell S T a))) (segment T (f x)) =
          Iod T (segment T (f x))")
  apply (thin_tac "segment T (f x) \<subseteq> segment T (Twell S T a)")
  apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
  apply (thin_tac "well_ordered_set (Iod S (segment S a))")
  apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T a)))")
 apply (frule_tac x = x in Twell_equiv [of "S" "T"], assumption+)
 apply (simp add:ord_equiv_def)
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (frule_tac a = x in segment_well_ordered_set [of "S"])
 apply (simp add:Iod_def segment_def)
 apply (frule_tac a = "f x" in segment_well_ordered_set [of "T"])
 apply (simp add:Iod_def segment_def)
 apply (frule_tac a = "Twell S T  x" in segment_well_ordered_set [of "T"])
 apply (simp add:ord_inj_def) apply (erule conjE)+
 apply (subgoal_tac "x \<in> carrier S") apply (simp add:funcset_mem)
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (frule_tac S = "Iod S (segment S x)" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod T (segment T (f x))" in well_ordered_set_is_ordered_set)
 apply (frule_tac S = "Iod T (segment T (Twell S T x))" in well_ordered_set_is_ordered_set)
 apply (frule_tac  D = "Iod S (segment S x)" and E = "Iod T (segment T (Twell S T x))"  in ord_equiv_sym, assumption+) 
 apply (thin_tac "ord_equiv (Iod S (segment S x)) (Iod T (segment T (Twell S T x))) ")
 apply (frule_tac D = "Iod T (segment T (Twell S T x))" and E = "Iod S (segment S x)" and F = "Iod T (segment T (f x))" in ord_equiv_trans, assumption+)
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
       (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b)) f)")
 apply (thin_tac "x \<in> carrier (Iod S (segment S a))")
 apply (thin_tac "well_ordered_set (Iod S (segment S a))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ord_equiv (Iod S (segment S x)) (Iod (Iod T (segment T (Twell S T a))) (segment T (f x)))")
 apply (thin_tac "segment (Iod S (segment S a)) x = segment S x")
 apply (thin_tac "Iod (Iod S (segment S a)) (segment S x) = Iod S (segment S x)")
 apply (thin_tac "segment (Iod T (segment T (Twell S T a))) (f x) = segment T (f x)")
 apply (thin_tac " ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (rule subsetI)
 apply (simp add:segment_def Iod_def ord_neq_def)
 apply (erule conjE)+
 apply (rule conjI)
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (rule_tac a = xa and b = "f x" and c = "Twell S T a" in ordering_axiom3 [of "T"], assumption+)
 apply (rule contrapos_pp, simp+)
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (subgoal_tac "Twell S T a \<in> carrier T")
 apply (frule_tac a = "f x" and b = "Twell S T a" in ordering_axiom2 [of "T"], assumption+) apply simp
 apply assumption
 apply (rule subsetI)
 apply (thin_tac "\<forall>a\<in>carrier S.  \<exists>b \<in> carrier T.  (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b))  f)")
 apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a)))  f")
 apply (thin_tac "well_ordered_set (Iod S (segment S a))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T a)))")
 apply (thin_tac " ord_equiv (Iod (Iod S (segment S a)) (segment S x))
           (Iod (Iod T (segment T (Twell S T a))) (segment T (f x)))")
 apply (thin_tac "segment (Iod S (segment S a)) x = segment S x")
 apply (thin_tac "segment (Iod T (segment T (Twell S T a))) (f x) = segment T (f x)")
 apply (thin_tac "f x \<in> carrier (Iod T (segment T (Twell S T a)))")
apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
 apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (frule_tac a = xa and b = x and c = a in ordering_axiom3 [of "S"], assumption+) apply simp apply (rule contrapos_pp, simp+)
 apply (frule_tac a = x and b = a in ordering_axiom2 [of "S"], assumption+) apply simp 
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.  (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b)) f)")
 apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (thin_tac "x \<in> carrier (Iod S (segment S a))")
 apply (thin_tac "well_ordered_set (Iod S (segment S a))")
 apply (thin_tac "well_ordered_set (Iod T (segment T (Twell S T a)))")
 apply (thin_tac "ord_equiv (Iod (Iod S (segment S a)) (segment S x))
           (Iod (Iod T (segment T (Twell S T a)))
             (segment (Iod T (segment T (Twell S T a))) (f x)))")
 apply (thin_tac "segment (Iod S (segment S a)) x = segment S x")
 apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply (rule conjI)
 apply (subgoal_tac "Twell S T a \<in> carrier T")
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (frule_tac a = xa and b = "f x" and c = "Twell S T a" in ordering_axiom3 [of "T"], assumption+)
 apply (rule contrapos_pp, simp+)
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (frule_tac a = "f x" and b = "Twell S T a" in ordering_axiom2 [of "T"], assumption+) apply simp
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.  (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b)) f)")
 apply (simp add:ord_inj_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.  (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b)) f)")
 apply (simp add:ord_isom_def bij_to_def)
 apply (erule conjE)+
 apply (thin_tac "\<forall>aa\<in>carrier (Iod S (segment S a)).
 \<forall>b\<in>carrier (Iod S (segment S a)).  aa <\<^sub>(Iod S (segment S a)) b =
                    f aa <\<^sub>(Iod T (segment T (Twell S T a))) (f b)")
 apply (thin_tac "inj_on f (carrier (Iod S (segment S a)))")
 apply (simp add:surj_to_def image_def)
 apply (subgoal_tac "b \<in> {y. \<exists>x\<in>carrier (Iod S (segment S a)). y = f x}")
 prefer 2 apply simp
 apply (thin_tac "{y. \<exists>x\<in>carrier (Iod S (segment S a)). y = f x} =
             carrier (Iod T (segment T (Twell S T a)))")
 apply simp
 apply (thin_tac " \<forall>a\<in>carrier S. \<exists>b \<in> carrier T. 
      (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b))  f)")
 apply (simp add:ord_inj_def)
 apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a <\<^sub>S b =  Twell S T a <\<^sub>T (Twell S T b)")
 apply (subgoal_tac "\<forall>y. y \<in> segment S a \<longrightarrow> y \<in> carrier S")
 apply (subgoal_tac "carrier (Iod S (segment S a)) = segment S a")
 apply simp
 apply (simp add:inj_on_def)
 apply (thin_tac "\<forall>y. y \<in> segment S a \<longrightarrow> y \<in> carrier S")
 apply (simp add:Iod_def)
 apply (rule allI) apply (rule impI) apply (simp add:segment_def)
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
       (\<exists>f. ord_isom (Iod S (segment S a)) (Iod T (segment T b)) f)")
 apply (rule ballI)+
 apply auto 
apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply (subgoal_tac "aa <\<^sub>S b")
 apply (simp add:ord_inj_def)
 apply (simp add:ord_neq_def) apply (simp add:ord_neq_def)
apply (thin_tac "ord_isom (Iod S (segment S a)) (Iod T (segment T (Twell S T a))) f")
 apply (simp add:ord_inj_def) apply (erule conjE)+
 apply (subgoal_tac "b \<in> carrier S") apply (rename_tac x y)
 apply (subgoal_tac "x <\<^sub>S y = Twell S T x <\<^sub>T (Twell S T y)")
 prefer 2  apply (subgoal_tac "x \<in> carrier S") apply simp
 apply (simp add:Iod_def segment_def)
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a <\<^sub>S b =  Twell S T a <\<^sub>T (Twell S T b)")
 apply (frule sym) apply (thin_tac "x <\<^sub>S y =  Twell S T x <\<^sub>T (Twell S T y)")
 apply (subgoal_tac "Twell S T x <\<^sub>T (Twell S T y)")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (thin_tac "Twell S T x <\<^sub>T (Twell S T y) =  x <\<^sub>S y")
 apply (simp add:Iod_def ord_neq_def)
 apply (simp add:segment_def)
 apply (simp add:Iod_def)
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (simp add:Iod_def)+
done

lemma well_ord_compare1:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))\<rbrakk> \<Longrightarrow> (ord_equiv S T) \<or> (\<exists>c\<in>carrier T. ord_equiv S (Iod T (segment T c)))"
apply (frule Twell_ord_inj [of "S" "T"], assumption+)
apply (frule ord_isom_induced_by_Twell [of "S" "T"], assumption+)
apply (case_tac "(Twell S T) ` (carrier S) = carrier T")
 apply simp
 apply (subgoal_tac "Iod T (carrier T) = T") apply simp
 apply (simp add:ord_equiv_def) apply blast
apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
              ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_isom S (Iod T (carrier T)) (restrict (Twell S T) (carrier S))")
 apply (frule well_ordered_set_is_ordered_set [of "T"]) 
 apply (simp add:Iod_self[THEN sym])
 apply (frule segmentTr [of "T" "(Twell S T) ` (carrier S)"])
 apply (thin_tac "\<forall>a\<in>carrier S.  \<exists>b \<in> carrier T.
              ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (simp add:ord_inj_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a <\<^sub>S b =  Twell S T a <\<^sub>T (Twell S T b)")
 apply (rule image_sub[of "Twell S T" "carrier S" "carrier T" "carrier S"], assumption+) apply simp
 apply (rule ballI) apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (frule well_ordered_set_is_ordered_set [of "T"])
 apply (subgoal_tac "Twell S T \<in> carrier S \<rightarrow> carrier T")
 apply (subgoal_tac "\<exists>a\<in>carrier S. b = Twell S T a")
 prefer 2 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>a\<in>carrier S. b = Twell S T a \<longrightarrow> x \<in> Twell S T ` carrier S") apply blast apply (thin_tac "\<exists>a\<in>carrier S. b = Twell S T a")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac x = a in Twell_equiv [of "S" "T"], assumption+)
 apply (frule sym) apply (thin_tac "b = Twell S T a") apply simp 
 apply (frule_tac a = a in ord_isom_Twell_segment [of "S" "T"], assumption+)
 apply simp
 apply (subgoal_tac "x \<in> carrier (Iod T (segment T b))")
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "ord_isom S (Iod T (Twell S T ` carrier S))
           (restrict (Twell S T) (carrier S))")
 apply (simp add:ord_isom_def bij_to_def) apply (erule conjE)+
 apply (thin_tac "\<forall>aa\<in>carrier (Iod S (segment S a)).
 \<forall>ba\<in>carrier (Iod S (segment S a)). aa <\<^sub>(Iod S (segment S a)) ba =
 (if aa \<in> segment S a then Twell S T aa else arbitrary) <\<^sub>(Iod T (segment T b))
                   (if ba \<in> segment S a then Twell S T ba else arbitrary)")
 apply (simp add:surj_to_def)
 apply (subgoal_tac "x \<in> restrict (Twell S T) (segment S a) `
          carrier (Iod S (segment S a))")
 prefer 2 apply simp
  apply (thin_tac "restrict (Twell S T) (segment S a) `
          carrier (Iod S (segment S a)) = carrier (Iod T (segment T b))")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>carrier (Iod S (segment S a)).
 x = (if xa \<in> segment S a then Twell S T xa else arbitrary) \<longrightarrow> (\<exists>xa\<in>carrier S. x = Twell S T xa)") apply blast
 apply (thin_tac "\<exists>xa\<in>carrier (Iod S (segment S a)).
             x = (if xa \<in> segment S a then Twell S T xa else arbitrary)")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "carrier (Iod S (segment S a)) = segment S a")
 apply simp apply (subgoal_tac "xa \<in> carrier S")
 apply blast apply (simp add:segment_def)
 apply (simp add:Iod_def)
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
                 ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (simp add:ord_inj_def) apply simp
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b \<in> carrier T.
              ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
apply (subgoal_tac "\<forall>a.  a \<in> carrier T \<and> Twell S T ` carrier S = segment T a
 \<longrightarrow> (ord_equiv S T \<or> (\<exists>c\<in>carrier T. ord_equiv S (Iod T (segment T c))))")
 apply blast apply (thin_tac "\<exists>a. a \<in> carrier T \<and> Twell S T ` carrier S = segment T a")
 apply (rule allI)
 apply (rule impI) apply (erule conjE)+ apply simp
 apply (simp add:ord_equiv_def)
apply blast
done

lemma well_ord_compare2:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<exists>a\<in>carrier S. \<forall>b\<in>carrier T. \<not> ord_equiv (Iod S (segment S a)) (Iod T (segment T b))\<rbrakk> \<Longrightarrow> \<exists>c\<in>carrier S. ord_equiv (Iod S (segment S c))  T"
apply (subgoal_tac "{x. x \<in> carrier S \<and> (\<forall>b \<in> carrier T. \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} \<noteq> {}") 
prefer 2 apply blast
 apply (thin_tac "\<exists>a\<in>carrier S. \<forall>b\<in>carrier T.
             \<not> ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (subgoal_tac "\<exists>d. minimum_elem S {x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
               \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} d")
 apply (subgoal_tac "\<forall>d. minimum_elem S {x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
  \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} d \<longrightarrow> (\<exists>c\<in>carrier S. ord_equiv (Iod S (segment S c)) T)") apply blast
 apply (thin_tac "\<exists>d. minimum_elem S {x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
               \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} d")
 apply (thin_tac " {x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
  \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} \<noteq> {}")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "\<forall>x\<in>carrier (Iod S (segment S d)). \<exists>y\<in>carrier T.
        ord_equiv (Iod (Iod S (segment S d)) (segment (Iod S (segment S d)) x))
                   (Iod T (segment T y))")
 apply (frule_tac a = d in segment_well_ordered_set [of "S" ])
 apply (simp add:minimum_elem_def)
apply (frule_tac S = "Iod S (segment S d)" in  well_ord_compare1 [of _ "T"], assumption+)
 apply (simp add:minimum_elem_def) apply (erule conjE)+
 apply (thin_tac "\<forall>b\<in>carrier T.
              \<not> ord_equiv (Iod S (segment S d)) (Iod T (segment T b))")
 apply (thin_tac "\<forall>x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T. \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b))) \<longrightarrow>   d \<le>\<^sub>S x")
 apply (thin_tac "\<forall>x\<in>carrier (Iod S (segment S d)). \<exists>y\<in>carrier T.
  ord_equiv (Iod (Iod S (segment S d)) (segment (Iod S (segment S d)) x))
                  (Iod T (segment T y))")
 apply blast
 apply (subgoal_tac "d \<in> carrier S") prefer 2 apply (simp add:minimum_elem_def) 
apply (rule ballI)
 apply (subgoal_tac "x <\<^sub>S d")
 apply (frule_tac t = d and s = x in pre_minimum [of "S" "{x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T. \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))}"])
 apply (rule subsetI) apply simp apply assumption
 apply (simp add:Iod_def segment_def) apply assumption
apply (thin_tac "minimum_elem S {x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
 \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))}  d")
 apply simp 
 apply (subgoal_tac "Iod (Iod S (segment S d)) (segment (Iod S (segment S d)) x) = Iod S (segment S x)") apply simp
 apply (subgoal_tac "x \<in> carrier S") apply blast
apply (simp add:Iod_def segment_def)
 apply (thin_tac "x \<in> carrier S \<longrightarrow>  (\<exists>b\<in>carrier T.
                 ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))")
 apply (subgoal_tac "segment (Iod S (segment S d)) x = segment S x")
 apply simp
 apply (subgoal_tac "segment S x \<subseteq> segment S d")
 apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (frule_tac S = "segment S x" and T = "segment S d" in Iod_sub_sub [of "S"], assumption+) apply (rule subsetI) apply (simp add:segment_def)
 apply assumption
 apply (rule subsetI) apply (simp add:segment_def)
 apply (erule conjE)+ apply (subgoal_tac "x \<in> carrier S")
 apply (frule well_ordered_set_is_ordered_set [of "S"])
apply (rule_tac a = xa and b = x and c = d in ord_neq_trans [of "S"], assumption+)
 apply (simp add:Iod_def)
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule equalityI)
 apply (rule subsetI) apply simp
 apply (rule subsetI) apply simp apply (erule conjE)+
apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (frule_tac a = xa and b = x and c = d in ordering_axiom3 [of "S"], assumption+) apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac a = x and b = d in ordering_axiom2 [of "S"], assumption+)
 apply simp
apply (thin_tac " minimum_elem S {x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
  \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} d")
 apply (simp add:Iod_def segment_def ord_neq_def)
apply (unfold well_ordered_set_def [of "S"])
 apply (subgoal_tac "{x. x \<in> carrier S \<and> (\<forall>b\<in>carrier T.
  \<not> ord_equiv (Iod S (segment S x)) (Iod T (segment T b)))} \<subseteq> carrier S") 
 apply blast
 apply(rule subsetI)
 apply simp
done

lemma well_ord_equiv:"\<lbrakk>well_ordered_set (S::'a OrderedSet); well_ordered_set (T::'b OrderedSet); \<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b));  \<forall>c\<in>carrier T. \<exists>d\<in>carrier S.  ord_equiv (Iod T (segment T c)) (Iod S (segment S d))\<rbrakk> \<Longrightarrow> ord_equiv S T"
apply (frule well_ord_compare1 [of "S" "T"], assumption+)
apply (case_tac "ord_equiv S T") apply simp apply simp
apply (subgoal_tac "\<forall>c\<in>carrier T. ord_equiv S (Iod T (segment T c)) \<longrightarrow>
        False") apply blast
 apply (thin_tac "\<exists>c\<in>carrier T. ord_equiv S (Iod T (segment T c))")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "\<exists>d\<in>carrier S.
                 ord_equiv (Iod T (segment T c)) (Iod S (segment S d))")
 prefer 2 apply simp
 apply (subgoal_tac "\<forall>d\<in>carrier S. ord_equiv (Iod T (segment T c)) (Iod S (segment S d)) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>d\<in>carrier S. ord_equiv (Iod T (segment T c)) (Iod S (segment S d))")
 apply (rule ballI)
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b\<in>carrier T.
                   ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (thin_tac "\<forall>c\<in>carrier T.  \<exists>d\<in>carrier S.
                   ord_equiv (Iod T (segment T c)) (Iod S (segment S d))")
 apply (rule impI)
apply (frule_tac S = S and a = d in segment_well_ordered_set, assumption+)
apply (frule_tac S = T and a = c in segment_well_ordered_set, assumption+)
apply (frule_tac S = "Iod S (segment S d)" in well_ordered_set_is_ordered_set)
apply (frule_tac S = "Iod T (segment T c)" in well_ordered_set_is_ordered_set)
apply (frule_tac S = S in well_ordered_set_is_ordered_set)
apply (frule_tac D = "S" and E = "Iod T (segment T c)" and F = "Iod S (segment S d)" in ord_equiv_trans, assumption+) 
apply (frule_tac a = d in not_ordequiv_segment [of "S"], assumption+)
apply simp
done

lemma well_ord_equiv1:"\<lbrakk>well_ordered_set (S::'a OrderedSet); well_ordered_set (T::'b OrderedSet); \<not> ord_equiv S T\<rbrakk> \<Longrightarrow> \<not> ((\<forall>a\<in>carrier S. \<exists>b\<in>carrier T.  ord_equiv (Iod S (segment S a)) (Iod T (segment T b))) \<and> (\<forall>c\<in>carrier T. \<exists>d\<in>carrier S.  ord_equiv (Iod T (segment T c)) (Iod S (segment S d))))"
apply (rule contrapos_pp, simp+) apply (erule conjE)
apply (frule well_ord_equiv [of "S" "T"], assumption+)
apply simp
done

lemma well_ord_compare:"\<lbrakk>well_ordered_set (S::'a OrderedSet); well_ordered_set (T::'b OrderedSet) \<rbrakk> \<Longrightarrow>
 (\<exists>a\<in>carrier S. ord_equiv (Iod S (segment S a)) T) \<or> ord_equiv S T \<or> 
 (\<exists>b\<in>carrier T. ord_equiv S (Iod T (segment T b)))" 
apply (case_tac "ord_equiv S T") apply simp
 apply (frule well_ord_equiv1 [of "S" "T"], assumption+)
 apply simp
 apply (case_tac "\<exists>a\<in>carrier S.  \<forall>b\<in>carrier T.
              \<not> ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (frule well_ord_compare2 [of "S" "T"], assumption+)
 apply blast apply simp
 apply (frule  well_ord_compare2 [of "T" "S"], assumption+)
apply (thin_tac "\<exists>c\<in>carrier T.  \<forall>d\<in>carrier S.
             \<not> ord_equiv (Iod T (segment T c)) (Iod S (segment S d))")
 apply (thin_tac "\<forall>a\<in>carrier S. \<exists>b\<in>carrier T.
             ord_equiv (Iod S (segment S a)) (Iod T (segment T b))")
 apply (subgoal_tac "\<forall>c\<in>carrier T. ord_equiv (Iod T (segment T c)) S \<longrightarrow>  ((\<exists>a\<in>carrier S. ord_equiv (Iod S (segment S a)) T) \<or> (\<exists>b\<in>carrier T. ord_equiv S (Iod T (segment T b))))")
 apply blast
 apply (thin_tac "\<exists>c\<in>carrier T. ord_equiv (Iod T (segment T c)) S")
 apply (rule ballI) apply (rule impI)
apply (frule_tac S = T and a = c in segment_well_ordered_set, assumption+)
apply (frule_tac S = "Iod T (segment T c)" in well_ordered_set_is_ordered_set)
apply (frule_tac D = "Iod T (segment T c)" and E = S in ord_equiv_sym)
 apply (simp add:well_ordered_set_is_ordered_set [of "S"])
 apply assumption
 apply blast
done

lemma well_ord_compareTr1:"\<lbrakk>well_ordered_set (S::'a OrderedSet); well_ordered_set (T::'b OrderedSet); \<exists>a\<in>carrier S. ord_equiv (Iod S (segment S a)) T; ord_equiv S T \<rbrakk> \<Longrightarrow> False"
apply auto
apply (frule_tac a = a in segment_well_ordered_set [of "S"], assumption+)
apply (frule_tac S = S in well_ordered_set_is_ordered_set)
apply (frule_tac S = T in well_ordered_set_is_ordered_set)
apply (frule_tac S = "Iod S (segment S a)" in well_ordered_set_is_ordered_set)
apply (frule_tac D = "Iod S (segment S a)" and E = T in ord_equiv_sym)
 apply assumption+
apply (frule_tac D = S and E = T and F = "Iod S (segment S a)" in ord_equiv_trans, assumption+)
 apply (frule_tac a = a in not_ordequiv_segment [of "S"], assumption+)
apply simp
done

lemma well_ordered_compareTr2:"\<lbrakk>well_ordered_set (S::'a OrderedSet); well_ordered_set (T::'b OrderedSet);ord_equiv S T; \<exists>b\<in>carrier T. ord_equiv S (Iod T (segment T b)) \<rbrakk> \<Longrightarrow> False"
apply auto
apply (frule_tac a = b in segment_well_ordered_set [of "T"], assumption+)
apply (frule_tac S = S in well_ordered_set_is_ordered_set)
apply (frule_tac S = T in well_ordered_set_is_ordered_set)
apply (frule_tac S = "Iod T (segment T b)" in well_ordered_set_is_ordered_set)
apply (frule_tac D = S and E = T in ord_equiv_sym, assumption+)
apply (frule_tac D = T and E = S and F = "Iod T (segment T b)" in ord_equiv_trans, assumption+)
 apply (frule_tac a = b in not_ordequiv_segment [of "T"], assumption+)
apply simp
done

lemma well_ordered_compareTr3:"\<lbrakk>well_ordered_set S; well_ordered_set T; \<exists>b\<in>carrier T. ord_equiv S (Iod T (segment T b)); \<exists>a\<in>carrier S. ord_equiv (Iod S (segment S a)) T \<rbrakk> \<Longrightarrow> False"  
apply (subgoal_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier T. ord_equiv (Iod S (segment S a)) T \<and> ord_equiv S (Iod T (segment T b)) \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>b\<in>carrier T. ord_equiv S (Iod T (segment T b))")
 apply (thin_tac "\<exists>a\<in>carrier S. ord_equiv (Iod S (segment S a)) T")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)
apply (frule_tac a = a in segment_well_ordered_set [of "S"], assumption+)
apply (frule_tac a = b in segment_well_ordered_set [of "T"], assumption+)
apply (frule_tac S = S in well_ordered_set_is_ordered_set)
apply (frule_tac S = "Iod S (segment S a)" in well_ordered_set_is_ordered_set)
apply (frule_tac S = T in well_ordered_set_is_ordered_set)
apply (frule_tac D = "Iod S (segment S a)" and E = T in ord_equiv_sym, assumption+)
 apply (thin_tac "ord_equiv (Iod S (segment S a)) T")
 apply (simp add:ord_equiv_def)
apply (subgoal_tac "\<forall>f g.  ord_isom S (Iod T (segment T b)) f \<and> ord_isom T (Iod S (segment S a)) g \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>f. ord_isom S (Iod T (segment T b)) f")
 apply (thin_tac "\<exists>f. ord_isom T (Iod S (segment S a)) f")
apply (rule allI)+ apply (rule impI) apply (erule conjE)+ (** koko **)
 apply (frule_tac S = T and T = "Iod S (segment S a)" and f = g and  ?S1.0 = "segment T b" in ord_isom_induced)  
 apply (simp add:segment_well_ordered_set) apply assumption
 apply (rule subsetI) apply (simp add:segment_def)
 apply (frule_tac S = "Iod T (segment T b)" in well_ordered_set_is_ordered_set)
 apply (frule_tac E = "Iod T (segment T b)" and F = "Iod (Iod S (segment S a)) (g ` segment T b)" and f = f and g = "restrict g (segment T b)" in ord_isom_trans [of "S"], assumption+)
 apply (subgoal_tac " g ` (segment T b) \<subseteq> carrier (Iod S (segment S a))")
 apply (frule_tac S = "Iod S (segment S a)" and T = "g ` (segment T b)" in subset_well_ordered, assumption+)
 apply (simp add:well_ordered_set_is_ordered_set)
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac f = g and A = "carrier T" and B = "segment S a" and ?A1.0 =
 "segment T b" in image_sub)
 apply (rule subsetI) apply (simp add:segment_def) apply assumption
 apply assumption
 apply simp 
 apply (subgoal_tac "(g ` (segment T b)) \<subseteq> (segment S a)") 
 apply (frule_tac S = "g ` (segment T b)" and T = "segment S a" in Iod_sub_sub [of "S" ], assumption+)
 apply (rule subsetI) apply (simp add:segment_def) apply simp
 apply (thin_tac "Iod (Iod S (segment S a)) (g ` segment T b) =
          Iod S (g ` segment T b)")
 apply (subgoal_tac " g ` segment T b \<subseteq> carrier S")
 apply (frule_tac T = "g ` (segment T b)" and f = "(compose (carrier S) (restrict g (segment T b)) f)" in well_ordered_to_subset [of "S"], assumption+)
 apply (subgoal_tac "a \<le>\<^sub>S ((compose (carrier S) (restrict g (segment T b)) f) a)") prefer 2 apply simp
 apply (thin_tac "\<forall>a. a \<in> carrier S \<longrightarrow>
               a \<le>\<^sub>S (compose (carrier S) (restrict g (segment T b)) f a)")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (thin_tac "restrict g (segment T b)
          \<in> extensional (carrier (Iod T (segment T b)))")
 apply (thin_tac " bij_to (compose (carrier S) (restrict g (segment T b)) f)
           (carrier S) (carrier (Iod S (g ` segment T b)))")
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>ba\<in>carrier S.
 f a <\<^sub>(Iod T (segment T b)) (f ba) = compose (carrier S) (restrict g (segment T b)) f a <\<^sub>(Iod S (g ` segment T b)) (compose (carrier S) (restrict g (segment T b)) f ba)")
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>ba\<in>carrier S.  a <\<^sub>S ba =
 (compose (carrier S) (restrict g (segment T b)) f) a <\<^sub>(Iod S (g ` segment T b)) ((compose (carrier S) (restrict g (segment T b)) f) ba)")
 apply (thin_tac "\<forall>aa\<in>carrier T. \<forall>b\<in>carrier T.  aa <\<^sub>T b =  g aa <\<^sub>(Iod S (segment S a)) (g b)")
 apply (thin_tac "bij_to (restrict g (segment T b)) (carrier (Iod T (segment T b))) (carrier (Iod S (g ` segment T b)))")
 apply (thin_tac "\<forall>a\<in>carrier (Iod T (segment T b)). \<forall>ba\<in>carrier (Iod T (segment T b)). a <\<^sub>(Iod T (segment T b)) ba = (if a \<in> segment T b then g a else arbitrary) <\<^sub>(Iod S (g ` segment T b)) (if ba \<in> segment T b then g ba else arbitrary)")
 apply (thin_tac "bij_to f (carrier S) (carrier (Iod T (segment T b)))")
 apply (thin_tac "bij_to g (carrier T) (carrier (Iod S (segment S a)))")
 apply (thin_tac "f \<in> extensional (carrier S)")
 apply (thin_tac "g \<in> extensional (carrier T)")
 apply (thin_tac "g ` segment T b \<subseteq> carrier S")
 apply (thin_tac "restrict g (segment T b) \<in> carrier (Iod T (segment T b)) \<rightarrow>
            carrier (Iod S (g ` segment T b))")
 apply (frule_tac f = "compose (carrier S) (restrict g (segment T b)) f" and A = "carrier S" and B = "carrier (Iod S (g ` segment T b))" and x = a in funcset_mem, assumption+)
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac A = "g ` segment T b" and B = "segment S a" and c = "(compose (carrier S) (restrict g (segment T b)) f) a" in subsetD, assumption+)
 apply (thin_tac "compose (carrier S) (restrict g (segment T b)) f a
          \<in> g ` segment T b")
 apply (thin_tac " compose (carrier S) (restrict g (segment T b)) f
          \<in> carrier S \<rightarrow> g ` segment T b")
 apply (simp add:compose_def funcset_mem)
 apply (thin_tac "well_ordered_set (Iod S (segment S a))")
 apply (thin_tac "ordered_set (Iod S (segment S a))")
 apply (thin_tac "f \<in> carrier S \<rightarrow> segment T b")
 apply (thin_tac "well_ordered_set (Iod T (segment T b))")
 apply (thin_tac "ordered_set (Iod T (segment T b))")
 apply (simp add:segment_def) apply (erule conjE)+ apply (simp add:ord_neq_def)
 apply (erule conjE)+ 
 apply (frule_tac a = "g (f a)" and b = a in ordering_axiom2 [of "S"], assumption+) 
 apply simp
 apply (rule_tac A = "g ` segment T b" and B = " segment S a" and C = " carrier S" in subset_trans, assumption+)
 apply (rule subsetI) apply (simp add:segment_def)
 apply (simp add:ord_isom_def [of "T"]) apply (erule conjE)+
 apply (thin_tac "\<forall>aa\<in>carrier T.
             \<forall>b\<in>carrier T.  aa <\<^sub>T b =  g aa <\<^sub>(Iod S (segment S a)) (g b)")
 apply (thin_tac "well_ordered_set (Iod T (segment T b))")
 apply (thin_tac "ord_isom (Iod T (segment T b)) (Iod (Iod S (segment S a)) (g ` segment T b))  (restrict g (segment T b))")
 apply (thin_tac "ord_isom S (Iod (Iod S (segment S a)) (g ` segment T b))
           (compose (carrier S) (restrict g (segment T b)) f)")

 apply (thin_tac "ord_isom S (Iod T (segment T b)) f")
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (rule_tac f = g and A = "carrier T" and B = "segment S a" and
 ?A1.0 = "segment T b" in image_sub, assumption+)
 apply (rule subsetI) apply (simp add:segment_def)
done
lemma subset_equiv_segment:"\<lbrakk>well_ordered_set D; S \<subseteq> carrier D\<rbrakk> \<Longrightarrow> ord_equiv D (Iod D S) \<or> (\<exists>a\<in>carrier D. ord_equiv (Iod D S) (Iod D (segment D a)))"
apply (frule subset_well_ordered [of "D" "S"], assumption+)
 apply (frule well_ord_compare [of "D" "Iod D S"], assumption+)
 apply (case_tac "ord_equiv D (Iod D S)")
  apply simp apply simp
  apply (case_tac "\<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) (Iod D S)")
  apply (subgoal_tac "\<forall>a\<in>carrier D. ord_equiv (Iod D (segment D a)) (Iod D S)
 \<longrightarrow> (\<exists>a\<in>carrier D. ord_equiv (Iod D S) (Iod D (segment D a)))")
  apply blast
  apply (thin_tac "\<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) (Iod D S)")
  apply (rule ballI) apply (rule impI)
  apply (frule_tac S = D and a = a in segment_well_ordered_set, assumption+)
  apply (frule_tac S = "Iod D (segment D a)" in well_ordered_set_is_ordered_set)
  apply (frule_tac S = "Iod D S" in well_ordered_set_is_ordered_set) 
  apply (frule_tac D = "Iod D (segment D a)" and E = "Iod D S" in ord_equiv_sym) apply assumption+
  apply blast apply simp
 apply (subgoal_tac "\<forall>b\<in>carrier (Iod D S). ord_equiv D (Iod (Iod D S) (segment (Iod D S) b)) \<longrightarrow> (\<exists>a\<in>carrier D. ord_equiv (Iod D S) (Iod D (segment D a)))")
 apply blast
 apply (thin_tac "\<exists>b\<in>carrier (Iod D S).
          ord_equiv D (Iod (Iod D S) (segment (Iod D S) b))")
 apply (rule ballI) apply (rule impI)
apply (subgoal_tac "\<exists>f. ord_isom  D (Iod (Iod D S) (segment (Iod D S) b)) f")
 prefer 2 apply (simp add:ord_equiv_def)
 apply (subgoal_tac "\<forall>f. ord_isom D (Iod (Iod D S) (segment (Iod D S) b)) f \<longrightarrow> (\<exists>a\<in>carrier D. ord_equiv (Iod D S) (Iod D (segment D a)))")
 apply blast apply (rule allI) apply (rule impI)
 apply (thin_tac "\<exists>f. ord_isom D (Iod (Iod D S) (segment (Iod D S) b)) f")
 apply (thin_tac "ord_equiv D (Iod (Iod D S) (segment (Iod D S) b))")
 apply (frule well_ordered_set_is_ordered_set [of "D"])
 apply (subgoal_tac "segment (Iod D S) b \<subseteq> S")
 apply (frule_tac S = "segment (Iod D S) b" in  Iod_sub_sub [of "D" _  "S"], assumption+) apply simp
 apply (thin_tac "Iod (Iod D S) (segment (Iod D S) b) = Iod D (segment (Iod D S) b)")
 apply (frule_tac T = "segment (Iod D S) b" and f = f in  well_ordered_to_subset [of "D"])
 apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
 apply (rule_tac c = x and A = S and B = "carrier D" in subsetD, assumption+)
 apply (subgoal_tac "b \<le>\<^sub>D (f b)") prefer 2 apply (subgoal_tac "b \<in> S")
 apply (frule_tac c = b and A = S and B = "carrier D" in subsetD, assumption+)
 apply simp apply (simp add:Iod_def)
 apply (thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow>  a \<le>\<^sub>D (f a)")
 apply (subgoal_tac "f b <\<^sub>D b")
 apply (simp add:ord_neq_def) apply (erule conjE)+
 apply (subgoal_tac "f b \<in> carrier D")
 apply (frule_tac a = "f b" and b = b in ordering_axiom2, assumption+)
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (simp add:subsetD) apply assumption+ apply simp
apply (thin_tac "\<forall>a\<in>carrier D. \<not> ord_equiv (Iod D (segment D a)) (Iod D S)")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac c = b in subsetD [of "S" "carrier D"], assumption+)
 apply (frule_tac f = f and A = "carrier D" and B = "segment (Iod D S) b" and x = b in funcset_mem, assumption+)
 apply (simp add:subsetD)+
apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (thin_tac " \<forall>a\<in>carrier D. \<forall>ba\<in>carrier D.
          a <\<^sub>D ba =  f a <\<^sub>(Iod D (segment (Iod D S) b)) (f ba)")
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac c = b in subsetD [of "S" "carrier D"], assumption+)
 apply (frule_tac f = f and A = "carrier D" and B = "segment (Iod D S) b" and x = b in funcset_mem, assumption+)
 apply (simp add:segment_def) apply (fold segment_def) apply (erule conjE)+
 apply (simp add:Iod_def ord_neq_def)
apply (rule subsetI)
 apply (simp add:Iod_def segment_def ord_neq_def)
done

constdefs
 ordinal_number :: "'a OrderedSet \<Rightarrow> ('a OrderedSet) set"
 "ordinal_number D == {X. well_ordered_set X \<and> ord_equiv X D}"

constdefs
 ODnums :: "('a OrderedSet) set set"
 "ODnums == {X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}"

 ODord :: "[('a OrderedSet) set, ('a OrderedSet) set] \<Rightarrow> bool"
 "ODord X Y == \<exists>x \<in> X. \<exists>y \<in> Y. (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c)))"

 ODord_eq::"[('a OrderedSet) set, ('a OrderedSet) set] \<Rightarrow> bool"
 "ODord_eq X Y == X = Y \<or> ODord X Y"

 ODrel :: "((('a OrderedSet) set) * (('a OrderedSet) set)) set"
 "ODrel == {Z. Z \<in> ODnums \<times> ODnums \<and> ODord_eq (fst Z) (snd Z)}" 

 ODnods :: "(('a OrderedSet) set) OrderedSet"
 "ODnods == \<lparr>carrier = ODnums, ord_rel = ODrel, ordering = ODord_eq \<rparr>"
 

lemma ODord_eq_ref:"\<lbrakk> X \<in> ODnums; Y \<in> ODnums; ODord_eq X Y; ODord_eq Y X \<rbrakk> \<Longrightarrow>
               X = Y"
apply (simp add:ODnums_def)
apply (subgoal_tac "\<forall>D E. well_ordered_set D \<and> X = ordinal_number D \<and> well_ordered_set E \<and> Y = ordinal_number E \<longrightarrow> X = Y")
 apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> X = ordinal_number D") 
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> Y = ordinal_number D")
apply (rule allI)+
 apply (rule impI) apply (erule conjE)+
 apply (simp add:ODord_eq_def ODord_def)
 apply (simp add:ordinal_number_def)
 apply (case_tac "{X. well_ordered_set X \<and> ord_equiv X D} = {X. well_ordered_set X \<and> ord_equiv X E}")
 apply simp apply simp
 apply (frule not_sym) apply (thin_tac "{X. well_ordered_set X \<and> ord_equiv X D} \<noteq> {X. well_ordered_set X \<and> ord_equiv X E}") apply simp
 apply (thin_tac "{X. well_ordered_set X \<and> ord_equiv X E} \<noteq>
             {X. well_ordered_set X \<and> ord_equiv X D}")
 apply (subgoal_tac "\<forall>u v. well_ordered_set u \<and> ord_equiv u D \<and> (\<exists>y. well_ordered_set y \<and> ord_equiv y E \<and> (\<exists>c\<in>carrier y. ord_equiv u (Iod y (segment y c)))) \<and> well_ordered_set v \<and> ord_equiv v E \<and> (\<exists>y. well_ordered_set y \<and>
 ord_equiv y D \<and> (\<exists>c\<in>carrier y. ord_equiv v (Iod y (segment y c)))) \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>x. well_ordered_set x \<and> ord_equiv x D \<and> (\<exists>y. well_ordered_set y \<and> ord_equiv y E \<and> (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))))")
 apply (thin_tac "\<exists>x. well_ordered_set x \<and> ord_equiv x E \<and> (\<exists>y. well_ordered_set y \<and> ord_equiv y D \<and> (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))))")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply auto
apply (rename_tac D E d e y ya c ca)
apply (frule_tac S = D in well_ordered_set_is_ordered_set)
apply (frule_tac S = E in well_ordered_set_is_ordered_set)
apply (frule_tac S = d in well_ordered_set_is_ordered_set)
apply (frule_tac S = e in well_ordered_set_is_ordered_set)
apply (frule_tac S = y in well_ordered_set_is_ordered_set) 
apply (frule_tac S = ya in well_ordered_set_is_ordered_set) 
 apply (frule_tac D = d and E = D in ord_equiv_sym, assumption+)
 apply (frule_tac D = e and E = E in ord_equiv_sym, assumption+)
 apply (thin_tac "ord_equiv d D") apply (thin_tac "ord_equiv e E")
apply (frule_tac D = D and E = d and F = "Iod y (segment y c)" in ord_equiv_trans, assumption+) 
apply (frule_tac S = y and a = c in segment_well_ordered_set, assumption+)
 apply (simp add:well_ordered_set_is_ordered_set) apply assumption+
apply (frule_tac D = E and E = e and F = "Iod ya (segment ya ca)" in ord_equiv_trans, assumption+)
apply (frule_tac S = ya and a = ca in segment_well_ordered_set, assumption+)
 apply (simp add:well_ordered_set_is_ordered_set) apply assumption+
apply (simp add:ord_equiv_def)
apply (subgoal_tac "\<forall>f g h i j k. ord_isom D d f \<and> ord_isom E e g \<and> ord_isom y E h \<and> ord_isom d (Iod y (segment y c)) i \<and> ord_isom ya D j \<and> ord_isom e (Iod ya (segment ya ca)) k \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>f. ord_isom y E f")
 apply (thin_tac "\<exists>f. ord_isom E e f")
 apply (thin_tac "\<exists>f. ord_isom d (Iod y (segment y c)) f")
 apply (thin_tac "\<exists>f. ord_isom ya D f")
 apply (thin_tac "\<exists>f. ord_isom e (Iod ya (segment ya ca)) f")
 apply (thin_tac "\<exists>f. ord_isom D d f")
apply (rule allI)+ apply (rule impI) apply (erule conjE)+
apply (frule_tac S = y and T = E and f = h and a = c in ord_isom_segment_segment, assumption+)
apply (frule_tac S = ya and T = D and f = j and a = ca in ord_isom_segment_segment, assumption+)
 apply (fold ord_equiv_def)
 apply (frule_tac D = D and E = "Iod y (segment y c)" and F = "Iod E (segment E (h c))" in ord_equiv_trans)
 apply (frule_tac S = y and a = c in segment_well_ordered_set, assumption+) 
 apply (simp add:well_ordered_set_is_ordered_set)
 apply (subgoal_tac "h c \<in> carrier E")
 apply (frule_tac S = E and a = "h c" in segment_well_ordered_set, assumption+) apply (simp add:well_ordered_set_is_ordered_set)
 apply (thin_tac "ord_isom D d f")
 apply (thin_tac "ord_isom E e g")
 apply (thin_tac "ord_isom d (Iod y (segment y c)) i")
 apply (thin_tac "ord_isom ya D j")
 apply (thin_tac "ord_isom e (Iod ya (segment ya ca)) k")
 apply (thin_tac "ord_equiv D (Iod y (segment y c))")
 apply (thin_tac "ord_equiv E (Iod ya (segment ya ca))")
 apply (thin_tac "ord_equiv (Iod y (segment y c)) (Iod E (segment E (h c)))")
 apply (thin_tac "ord_equiv (Iod ya (segment ya ca)) (Iod D (segment D (j ca)))")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem) apply assumption+
 apply (subgoal_tac "h c \<in> carrier E")
 apply (rule_tac S = D and T = E in well_ordered_compareTr3, assumption+)
 apply blast
 apply (frule_tac S = ya and a = ca in segment_well_ordered_set, assumption+)
 apply (frule_tac S = "Iod ya (segment ya ca)" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = E and E = "Iod ya (segment ya ca)" in ord_equiv_sym, assumption+) apply (thin_tac "ord_equiv E (Iod ya (segment ya ca))")
 apply (subgoal_tac "j ca \<in> carrier D")
 apply (frule_tac S = D and a = "j ca" in segment_well_ordered_set, assumption+)
 apply (frule_tac S = "Iod D (segment D (j ca))" in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod ya (segment ya ca)" and E = "Iod D (segment D (j ca))" in ord_equiv_sym, assumption+)
 apply (frule_tac D = "Iod D (segment D (j ca))" and E = "Iod ya (segment ya ca)" and F = E in ord_equiv_trans, assumption+)
 apply blast
 apply (thin_tac "ord_isom D d f")
 apply (thin_tac "ord_isom E e g")
 apply (thin_tac "ord_isom y E h")
 apply (thin_tac "ord_isom d (Iod y (segment y c)) i")
 apply (thin_tac "ord_isom e (Iod ya (segment ya ca)) k")
 apply (thin_tac "well_ordered_set (Iod ya (segment ya ca))")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
 apply (thin_tac "ord_isom D d f")
 apply (thin_tac "ord_isom E e g")
 apply (thin_tac "ord_isom d (Iod y (segment y c)) i")
 apply (thin_tac "ord_isom ya D j")
 apply (thin_tac "ord_isom e (Iod ya (segment ya ca)) k")
 apply (thin_tac "ord_equiv (Iod y (segment y c)) (Iod E (segment E (h c)))")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
done

lemma well_ordered_set_sym:"\<lbrakk>well_ordered_set S; well_ordered_set T; ord_equiv S T \<rbrakk> \<Longrightarrow> ord_equiv T S"
apply (frule_tac well_ordered_set_is_ordered_set [of "S"])
apply (frule_tac well_ordered_set_is_ordered_set [of "T"])
apply (rule ord_equiv_sym [of "S" "T"], assumption+)
done

lemma well_ordered_set_trans:"\<lbrakk>well_ordered_set S; well_ordered_set T; well_ordered_set U; ord_equiv S T; ord_equiv T U\<rbrakk> \<Longrightarrow> ord_equiv S U" 
apply (frule_tac well_ordered_set_is_ordered_set [of "S"])
apply (frule_tac well_ordered_set_is_ordered_set [of "T"])
apply (frule_tac well_ordered_set_is_ordered_set [of "U"])
apply (rule ord_equiv_trans [of "S" "T" "U"], assumption+)
done

lemma ODord_eq_trans:"\<lbrakk> X \<in> ODnums; Y \<in> ODnums; Z \<in> ODnums; ODord_eq X Y; ODord_eq Y Z \<rbrakk> \<Longrightarrow> ODord_eq X Z"
apply (simp add:ODord_eq_def)
apply (case_tac "X = Y")
 apply simp
 apply (case_tac "Y = Z")
 apply simp
apply simp
 apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>D E F. well_ordered_set D \<and> X = ordinal_number D \<and>
 well_ordered_set E \<and> Y = ordinal_number E \<and> well_ordered_set F \<and> Z = ordinal_number F \<longrightarrow> X = Z \<or> ODord X Z")
 apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> X = ordinal_number D")
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> Y = ordinal_number D")
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> Z = ordinal_number D")
apply (rule allI)+
 apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def ODord_def) apply (fold ordinal_number_def)
apply (subgoal_tac "\<exists>c\<in>carrier F. ord_equiv D (Iod F (segment F c))")
 apply (subgoal_tac "ord_equiv D D")
 apply (subgoal_tac "ord_equiv F F")
 apply blast
 apply (frule_tac S = F in well_ordered_set_is_ordered_set)
 apply (simp add:ord_equiv_reflex)
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (simp add:ord_equiv_reflex)
 apply (subgoal_tac "\<forall>u v. (well_ordered_set u \<and> ord_equiv u D \<and> (\<exists>y. well_ordered_set y \<and> ord_equiv y E \<and> (\<exists>c\<in>carrier y. ord_equiv u (Iod y (segment y c))))) \<and> (well_ordered_set v \<and> ord_equiv v E \<and> (\<exists>y. well_ordered_set y \<and> ord_equiv y F \<and> (\<exists>c\<in>carrier y. ord_equiv v (Iod y (segment y c))))) \<longrightarrow>
 (\<exists>c\<in>carrier F. ord_equiv D (Iod F (segment F c)))")
 apply blast
 apply (thin_tac "\<exists>x. well_ordered_set x \<and>  ord_equiv x D \<and>
  (\<exists>y. well_ordered_set y \<and> ord_equiv y E \<and>
                 (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))))")
 apply (thin_tac "\<exists>x. well_ordered_set x \<and> ord_equiv x E \<and>
  (\<exists>y. well_ordered_set y \<and> ord_equiv y F \<and>
                 (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))))")
apply (rule allI)+ apply (rule impI)
 apply (erule conjE)+ 
 apply (subgoal_tac "\<forall>e f. (well_ordered_set e \<and> ord_equiv e E \<and> (\<exists>c\<in>carrier e. ord_equiv u (Iod e (segment e c)))) \<and> (well_ordered_set f \<and> ord_equiv f F \<and> (\<exists>c\<in>carrier f. ord_equiv v (Iod f (segment f c)))) \<longrightarrow> (\<exists>c\<in>carrier F. ord_equiv D (Iod F (segment F c)))")
 apply blast
 apply (thin_tac "\<exists>y. well_ordered_set y \<and> ord_equiv y E \<and>
              (\<exists>c\<in>carrier y. ord_equiv u (Iod y (segment y c)))")
 apply (thin_tac "\<exists>y. well_ordered_set y \<and> ord_equiv y F \<and>
              (\<exists>c\<in>carrier y. ord_equiv v (Iod y (segment y c)))")
apply (rule allI)+ apply (rule impI) apply (erule conjE)+
apply (subgoal_tac "\<forall>ce\<in>carrier e. \<forall>cf\<in>carrier f.  (ord_equiv u (Iod e (segment e ce))) \<and> (ord_equiv v (Iod f (segment f cf))) \<longrightarrow> (\<exists>c\<in>carrier F. ord_equiv D (Iod F (segment F c)))")
apply blast
apply (thin_tac "\<exists>c\<in>carrier e. ord_equiv u (Iod e (segment e c))")
apply (thin_tac "\<exists>c\<in>carrier f. ord_equiv v (Iod f (segment f c))")
apply (rule ballI)+ apply (rule impI) apply (erule conjE) 
 apply (subgoal_tac "\<exists>h. ord_isom e E h")
 apply (subgoal_tac "\<exists>k. ord_isom f F k")
 apply (subgoal_tac "\<forall>h k. ord_isom e E h \<and> ord_isom f F k \<longrightarrow>
 (\<exists>c\<in>carrier F. ord_equiv D (Iod F (segment F c)))")
 apply blast
 apply (thin_tac "\<exists>h. ord_isom e E h")
 apply (thin_tac "\<exists>k. ord_isom f F k")
apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (frule_tac S = e and T = E and f = h and a = ce in ord_isom_segment_segment, assumption+)
 apply (subgoal_tac "h ce \<in> carrier E")
 apply (frule_tac S = u and T = D in well_ordered_set_sym, assumption+)
 apply (thin_tac "ord_equiv u D")
 apply (frule_tac S = D and T = u and U = "Iod e (segment e ce)" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_well_ordered_set) apply assumption+
 apply (frule_tac S = e and a = ce in segment_well_ordered_set, assumption+)
 apply (frule_tac S = D and T = "Iod e (segment e ce)" and U = "Iod E (segment E (h ce))" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_well_ordered_set) apply assumption+
 apply (frule_tac S = v and T = E in well_ordered_set_sym, assumption+)
 apply (frule_tac S = E and T = v and U = "Iod f (segment f cf)" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_well_ordered_set) apply assumption+
 apply (frule_tac S = f and T = F and f = k and a = cf in ord_isom_segment_segment, assumption+) 
 apply (subgoal_tac "k cf \<in> carrier F")
 apply (frule_tac S = f and a = cf in segment_well_ordered_set, assumption+)
 apply (frule_tac S = E and T = "Iod f (segment f cf)" and U = "Iod F (segment F (k cf))" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_well_ordered_set) apply assumption+
 apply (thin_tac "X = ordinal_number D")
 apply (thin_tac "Y = ordinal_number E")
 apply (thin_tac " Z = ordinal_number F")
 apply (thin_tac "well_ordered_set u")
 apply (thin_tac "well_ordered_set v")
 apply (thin_tac "ord_equiv v E")
 apply (thin_tac "well_ordered_set e")
 apply (thin_tac "well_ordered_set f")
 apply (thin_tac "ord_equiv u (Iod e (segment e ce))")
 apply (thin_tac "ord_equiv v (Iod f (segment f cf))")
 apply (thin_tac "ord_isom f F k")
 apply (thin_tac "ord_equiv (Iod e (segment e ce)) (Iod E (segment E (h ce)))")
 apply (thin_tac "ord_equiv D u")
 apply (thin_tac "ord_equiv D (Iod e (segment e ce))")
 apply (thin_tac "well_ordered_set (Iod e (segment e ce))")
 apply (thin_tac "ord_equiv E v")
 apply (thin_tac "ord_equiv E (Iod f (segment f cf))")
 apply (thin_tac "ord_equiv (Iod f (segment f cf)) (Iod F (segment F (k cf)))")
 apply (thin_tac "well_ordered_set (Iod f (segment f cf))")
 apply (thin_tac "ord_equiv e E")  apply (thin_tac "ord_equiv f F")
 apply (thin_tac "ce \<in> carrier e") apply (thin_tac "ord_isom e E h")
 apply (thin_tac "cf \<in> carrier f") apply simp 
apply (unfold ord_equiv_def)
 apply (subgoal_tac "\<forall>f g. ord_isom D (Iod E (segment E (h ce))) f \<and> ord_isom E (Iod F (segment F (k cf))) g \<longrightarrow> (\<exists>c\<in>carrier F. \<exists>f. ord_isom D (Iod F (segment F c)) f)") apply blast
 apply (thin_tac "\<exists>f. ord_isom D (Iod E (segment E (h ce))) f")
 apply (thin_tac "\<exists>f. ord_isom E (Iod F (segment F (k cf))) f")
apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (fold ord_equiv_def)
 apply (frule_tac S = F and a = "k cf" in segment_well_ordered_set, assumption+)
 apply (frule_tac S = E and T = "Iod F (segment F (k cf))" and f = g and a = "h ce" in ord_isom_segment_segment, assumption+) 
 apply (subgoal_tac "segment F (g (h ce)) \<subseteq> segment F (k cf)")
 apply (frule_tac S = F in well_ordered_set_is_ordered_set)
 apply (frule_tac D = F and S = "segment F (g (h ce))" and T = "segment F (k cf)" in Iod_sub_sub, assumption+) 
 apply (rule subsetI) apply (simp add:segment_def) 
 apply (subgoal_tac "segment (Iod F (segment F (k cf))) (g (h ce)) = segment F (g (h ce))") apply simp
 apply (thin_tac "segment (Iod F (segment F (k cf))) (g (h ce)) =
          segment F (g (h ce))")
 apply (thin_tac "Iod (Iod F (segment F (k cf))) (segment F (g (h ce))) =
          Iod F (segment F (g (h ce)))")
 apply (subgoal_tac "ord_equiv D (Iod E (segment E (h ce)))")
 apply (subgoal_tac "ord_equiv (Iod E (segment E (h ce))) (Iod F (segment F (g (h ce))))")
 apply (frule_tac S = E and a = "h ce" in segment_well_ordered_set, assumption+)
 apply (frule_tac S = D and T = "Iod E (segment E (h ce))" and U = "Iod F (segment F (g (h ce)))" in well_ordered_set_trans, assumption+)
 apply (subgoal_tac "g (h ce) \<in> carrier F")
 apply (simp add:segment_well_ordered_set)
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac f = g and A = "carrier E" and B = "segment F (k cf)" and x = "h ce" in funcset_mem, assumption+) apply (simp add:segment_def)
 apply assumption+
 apply (subgoal_tac "g (h ce) \<in> carrier F")
 apply blast 
 apply (thin_tac "ord_isom D (Iod E (segment E (h ce))) f")
 apply (thin_tac "well_ordered_set (Iod F (segment F (k cf)))")
 apply (thin_tac " ord_equiv (Iod E (segment E (h ce))) (Iod F (segment F (g (h ce))))")
 apply (thin_tac "segment F (g (h ce)) \<subseteq> segment F (k cf)")
 apply (thin_tac "ord_equiv D (Iod E (segment E (h ce)))")
 apply (thin_tac "ord_equiv (Iod E (segment E (h ce)))
           (Iod F (segment F (g (h ce))))")
 apply (thin_tac "ord_equiv D (Iod F (segment F (g (h ce))))")
 apply (thin_tac "well_ordered_set (Iod E (segment E (h ce)))")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier E. \<forall>b\<in>carrier E.  a <\<^sub>E b =  g a <\<^sub>(Iod F (segment F (k cf))) (g b)")
 apply (thin_tac "bij_to g (carrier E) (carrier (Iod F (segment F (k cf))))")
 apply (simp add:Iod_def)
 apply (frule_tac f = g and A = "carrier E" and B = "segment F (k cf)" and x = "h ce" in funcset_mem, assumption+) apply (simp add:segment_def)
 apply assumption+
 apply (subst ord_equiv_def) apply blast
apply (rule equalityI)
 apply (rule subsetI)  apply (simp add:Iod_def segment_def ord_neq_def) 
 apply (rule subsetI) apply (subst Iod_def) apply (subst segment_def)
 apply simp apply (simp add:ord_neq_def)
 apply (simp add:ord_isom_def)  apply (erule conjE)+
 apply (thin_tac " ord_equiv (Iod E (segment E (h ce))) (Iod (Iod F (segment F (k cf))) (segment (Iod F (segment F (k cf))) (g (h ce))))")
 apply (thin_tac "g \<in> extensional (carrier E)")
 apply (thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D.  a <\<^sub>D b =  f a <\<^sub>(Iod E (segment E (h ce))) (f b)")
 apply (thin_tac "\<forall>a\<in>carrier E. \<forall>b\<in>carrier E.  a <\<^sub>E b =  g a <\<^sub>(Iod F (segment F (k cf))) (g b)")
 apply (thin_tac "bij_to f (carrier D) (carrier (Iod E (segment E (h ce))))")
 apply (thin_tac "bij_to g (carrier E) (carrier (Iod F (segment F (k cf))))")
 apply (thin_tac "f \<in> carrier D \<rightarrow> carrier (Iod E (segment E (h ce)))")
 apply (thin_tac "Iod (Iod F (segment F (k cf))) (segment F (g (h ce))) =
          Iod F (segment F (g (h ce)))")
 apply (frule_tac A = "segment F (g (h ce))" and B = "segment F (k cf)" and c = x in subsetD, assumption+) apply simp apply (thin_tac "x \<in> segment F (k cf)")
 apply (thin_tac "g \<in> carrier E \<rightarrow> carrier (Iod F (segment F (k cf)))")
 apply (thin_tac "segment F (g (h ce)) \<subseteq> segment F (k cf)")
 apply (simp add:segment_def) apply (erule conjE)+
 apply (simp add:ord_neq_def)
apply (thin_tac "ord_isom D (Iod E (segment E (h ce))) f")
 apply (thin_tac "well_ordered_set (Iod F (segment F (k cf)))")
 apply (thin_tac "ord_equiv (Iod E (segment E (h ce)))  (Iod (Iod F (segment F (k cf))) (segment (Iod F (segment F (k cf))) (g (h ce))))")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac f = g and A = "carrier E" and B = "segment F (k cf)" and x = "h ce" in funcset_mem, assumption+)
 apply (thin_tac "\<forall>a\<in>carrier E. \<forall>b\<in>carrier E.  a <\<^sub>E b =  g a <\<^sub>(Iod F (segment F (k cf))) (g b)") 
 apply (rule subsetI)  apply (simp add:segment_def) apply (erule conjE)+
 apply (frule_tac S = F in well_ordered_set_is_ordered_set)
 apply (frule_tac a = x and b = "g (h ce)" and c = "k cf" in ord_neq_trans,
 assumption+)  
apply (thin_tac "ord_isom e E h")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply (thin_tac "ord_isom f F k")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
apply assumption+
done

lemma ordinal_numberTr1:" X \<in> carrier ODnods \<Longrightarrow> \<exists>D. well_ordered_set D \<and> 
 D \<in> X"
apply (simp add:ODnods_def)
apply (simp add:ODnums_def) 
apply (subgoal_tac "\<forall>D. well_ordered_set D \<and> X = ordinal_number D \<longrightarrow>
 (\<exists>D. well_ordered_set D \<and> D \<in> X)")
 apply blast apply (thin_tac "\<exists>D. well_ordered_set D \<and> X = ordinal_number D")
 apply (rule allI) apply (rule impI)
 apply (erule conjE)
 apply (simp add:ordinal_number_def)
 apply (thin_tac "X = {X. well_ordered_set X \<and> ord_equiv X D}")
apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac D = D in ord_equiv_reflex)
 apply blast
done

lemma ordinal_numberTr2:"\<lbrakk>well_ordered_set D; x = ordinal_number D\<rbrakk> \<Longrightarrow>
            D \<in> x"
apply (simp add:ordinal_number_def)
apply (rule ord_equiv_reflex) 
apply (simp add:well_ordered_set_is_ordered_set)
done

lemma ordinal_numberTr3:"\<lbrakk>well_ordered_set D; well_ordered_set F; ord_equiv D F; x = ordinal_number D\<rbrakk> \<Longrightarrow> x = ordinal_number F"
 apply (simp add:ordinal_number_def)
 apply (thin_tac "x = {X. well_ordered_set X \<and> ord_equiv X D}")
 apply (rule equalityI)
 apply (rule subsetI) apply simp apply (erule conjE)
 apply (rule_tac S = x and T = D and U = F in well_ordered_set_trans, assumption+)
 apply (rule subsetI) apply simp apply (erule conjE)
 apply (frule well_ordered_set_sym [of "D" "F"], assumption+)
 apply (rule_tac S = x and T = F and U = D in well_ordered_set_trans, assumption+)
done

lemma ordinal_number_ord:"\<lbrakk> X \<in> carrier ODnods; Y \<in> carrier ODnods\<rbrakk> \<Longrightarrow>
 ODord X Y \<or> X = Y \<or> ODord Y X"
apply (simp add:ODord_def)
 apply (frule ordinal_numberTr1 [of "X"])
 apply (frule ordinal_numberTr1 [of "Y"])
apply (subgoal_tac "\<forall>D E. well_ordered_set D \<and> D \<in> X \<and> well_ordered_set E \<and> E \<in> Y \<longrightarrow> (\<exists>x\<in>X. \<exists>y\<in>Y. \<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))) \<or>  X = Y \<or> (\<exists>x\<in>Y. \<exists>y\<in>X. \<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c)))")
 apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> D \<in> X")
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> D \<in> Y")
apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (frule_tac S = D and T = E in well_ord_compare, assumption+)
 apply (case_tac "\<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E")
 apply (subgoal_tac "(\<exists>x\<in>Y. \<exists>y\<in>X. \<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c)))") apply simp
 apply (thin_tac "(\<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E) \<or> ord_equiv D E \<or> (\<exists>b\<in>carrier E. ord_equiv D (Iod E (segment E b)))")
 apply (subgoal_tac "\<forall>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E \<longrightarrow>
 (\<exists>x\<in>Y. \<exists>y\<in>X. \<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c)))")
 apply blast apply (thin_tac "\<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E")
 apply (rule ballI)  apply (rule impI)
 apply (subgoal_tac "ord_equiv E (Iod D (segment D a))")
 apply blast
 apply (rule ord_equiv_sym)
  apply (simp add:segment_well_ordered_set well_ordered_set_is_ordered_set)
  apply (simp add:well_ordered_set_is_ordered_set)
  apply assumption
apply simp
 apply (case_tac "ord_equiv D E")
 apply (subgoal_tac "X = Y") apply simp
 apply (thin_tac "ord_equiv D E \<or> (\<exists>b\<in>carrier E. ord_equiv D (Iod E (segment E b)))")
 apply (thin_tac "\<forall>a\<in>carrier D. \<not> ord_equiv (Iod D (segment D a)) E")
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ODnods_def) apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>F G. well_ordered_set F \<and> X = ordinal_number F \<and> 
 well_ordered_set G \<and> Y = ordinal_number G \<longrightarrow> x \<in> Y")
 apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> X = ordinal_number D")
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> Y = ordinal_number D")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def) apply (erule conjE)+
 apply (thin_tac "X = {X. well_ordered_set X \<and> ord_equiv X F}")
 apply (thin_tac "Y = {X. well_ordered_set X \<and> ord_equiv X G}")
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac S = E in well_ordered_set_is_ordered_set)
 apply (frule_tac S = F in well_ordered_set_is_ordered_set)
 apply (frule_tac S = G in well_ordered_set_is_ordered_set)
 apply (frule_tac S = x in well_ordered_set_is_ordered_set)
 apply (frule_tac D = D and E = F in ord_equiv_sym, assumption+)
 apply (frule_tac D = x and E = F and F = D in ord_equiv_trans, assumption+)
 apply (frule_tac D = x and E = D and F = E in ord_equiv_trans, assumption+)
 apply (rule_tac D = x and E = E and F = G in ord_equiv_trans, assumption+) 
 apply (rule subsetI)
 apply (simp add:ODnods_def) apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>F G. well_ordered_set F \<and> X = ordinal_number F \<and> 
 well_ordered_set G \<and> Y = ordinal_number G \<longrightarrow> x \<in> X")
 apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> X = ordinal_number D")
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> Y = ordinal_number D")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def) apply (erule conjE)+
 apply (thin_tac "X = {X. well_ordered_set X \<and> ord_equiv X F}")
 apply (thin_tac "Y = {X. well_ordered_set X \<and> ord_equiv X G}")
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac S = E in well_ordered_set_is_ordered_set)
 apply (frule_tac S = F in well_ordered_set_is_ordered_set)
 apply (frule_tac S = G in well_ordered_set_is_ordered_set)
 apply (frule_tac S = x in well_ordered_set_is_ordered_set)
 apply (frule_tac D = E and E = G in ord_equiv_sym, assumption+)
 apply (frule_tac D = D and E = E in ord_equiv_sym, assumption+)
 apply (frule_tac D = x and E = G and F = E in ord_equiv_trans, assumption+)
 apply (frule_tac D = x and E = E and F = D in ord_equiv_trans, assumption+)
 apply (rule_tac D = x and E = D and F = F in ord_equiv_trans, assumption+) 
apply simp
 apply blast
done

lemma ODnum_subTr:"\<lbrakk>well_ordered_set D; x = ordinal_number D; y \<in>ODnums; ODord y x; Y \<in> y\<rbrakk> \<Longrightarrow> \<exists>c\<in>carrier D. ord_equiv Y (Iod D (segment D c))"
apply (simp add:ordinal_number_def)
apply (simp add:ODord_def)
apply (subgoal_tac "\<forall>u\<in>y. \<forall>v. well_ordered_set v \<and> ord_equiv v D \<and> (\<exists>c\<in>carrier v. ord_equiv u (Iod v (segment v c))) \<longrightarrow> (\<exists>c\<in>carrier D. ord_equiv Y (Iod D (segment D c))
)") apply blast 
 apply (thin_tac " \<exists>x\<in>y. \<exists>y. well_ordered_set y \<and>  ord_equiv y D \<and>
                 (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))) ")
 apply (rule ballI) apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "\<forall>c\<in>carrier v. ord_equiv u (Iod v (segment v c)) \<longrightarrow>
  (\<exists>c\<in>carrier D. ord_equiv Y (Iod D (segment D c)))")
 apply blast apply (thin_tac "\<exists>c\<in>carrier v. ord_equiv u (Iod v (segment v c))")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "ord_equiv Y u")
apply (simp add:ord_equiv_def [of _ "D"])
 apply (subgoal_tac "\<forall>f. ord_isom v D f \<longrightarrow> (\<exists>c\<in>carrier D. ord_equiv Y (Iod D (segment D c)))")
 apply blast apply (thin_tac "\<exists>f. ord_isom v D f")
 apply (rule allI) apply (rule impI)
 apply (frule_tac S = v and T = D and f = f and a = c in ord_isom_segment_segment, assumption+)
apply (frule_tac S = v and a = c in segment_well_ordered_set, assumption+)
 apply (subgoal_tac "well_ordered_set u")
 apply (frule_tac S = u and T = "Iod v (segment v c)" and U = "Iod D (segment D (f c))" in well_ordered_set_trans, assumption+)
apply (rule segment_well_ordered_set, assumption+)
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem) apply assumption+
apply (subgoal_tac "well_ordered_set Y")
 apply (frule_tac S = Y and T = u and U = "Iod D (segment D (f c))" in well_ordered_set_trans, assumption+)
 apply (rule segment_well_ordered_set, assumption+)
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem) apply assumption+ 
apply (subgoal_tac "f c \<in> carrier D")
 apply blast
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (simp add:funcset_mem) 
apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>E. well_ordered_set E \<and> y = ordinal_number E \<longrightarrow>
 well_ordered_set Y") apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def)
apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>E. well_ordered_set E \<and> y = ordinal_number E \<longrightarrow>
 well_ordered_set u") apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def)
apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>E. well_ordered_set E \<and> y = ordinal_number E \<longrightarrow>
 ord_equiv Y u") apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def)
 apply (erule conjE)+
apply (frule_tac S = u and T = E in well_ordered_set_sym, assumption+)
 apply (frule_tac S = Y and T = E and U = u in well_ordered_set_trans, assumption+)
done 

lemma ODnum_segment_uniqueTr:"\<lbrakk>well_ordered_set D; y \<in> ODnums; Y \<in> y; Y1 \<in> y; c \<in> carrier D; c1 \<in> carrier D; ord_equiv Y (Iod D (segment D c)); ord_equiv Y1 (Iod D (segment D c1))\<rbrakk> \<Longrightarrow> c = c1" 
apply (simp add:ODnums_def)
apply (subgoal_tac "\<forall>D. well_ordered_set D \<and> y = ordinal_number D \<longrightarrow> c = c1")
apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (simp add:ordinal_number_def)
 apply (erule conjE)+ apply (thin_tac "y = {X. well_ordered_set X \<and> ord_equiv X Da}")
 apply (frule segment_well_ordered_set [of "D" "c"], assumption+)
 apply (frule segment_well_ordered_set [of "D" "c1"], assumption+)
apply (frule_tac S = Y1 and T = Da in well_ordered_set_sym, assumption+)
apply (frule well_ordered_set_sym [of "Y" "Iod D (segment D c)"], assumption+)
 apply (frule_tac S = Y and T = Da and U = Y1 in well_ordered_set_trans, 
                      assumption+)
 apply (frule_tac S = "Iod D (segment D c)" and T = Y and U = Y1 in well_ordered_set_trans, assumption+) 
 apply (frule_tac S = "Iod D (segment D c)" and T = Y1 and U = "Iod D (segment D c1)" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_unique)
done

lemma ODnum_segmentTr:"\<lbrakk>well_ordered_set D; x = ordinal_number D; y \<in>ODnums; ODord y x\<rbrakk> \<Longrightarrow> \<exists>c. c\<in>carrier D \<and> (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c)))"
apply (subgoal_tac "\<exists>Z. Z\<in>y") prefer 2 apply (simp add:ODnums_def)
apply (subgoal_tac "\<forall>E. well_ordered_set E \<and> y = ordinal_number E \<longrightarrow> (\<exists>Z. Z \<in> y)") apply blast apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (simp add:ordinal_number_def)
 apply (subgoal_tac "ord_equiv E E") apply blast
apply (frule_tac S = E in well_ordered_set_is_ordered_set)
 apply (rule ord_equiv_reflex, assumption+)
 apply (subgoal_tac "\<forall>Z. Z \<in> y \<longrightarrow> (\<exists>c\<in>carrier D. \<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c)))") apply blast apply (thin_tac "\<exists>Z. Z \<in> y")
 apply (rule allI) apply (rule impI)
 apply (frule_tac Y = Z in ODnum_subTr [of "D" "x" "y"], assumption+)
 apply (subgoal_tac "\<forall>d\<in>carrier D. ord_equiv Z (Iod D (segment D d)) \<longrightarrow>
 (\<exists>c\<in>carrier D. \<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c)))")
 apply blast apply (thin_tac "\<exists>c\<in>carrier D. ord_equiv Z (Iod D (segment D c))")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D d))")
 apply blast
apply (rule ballI)
 apply (simp add:ODnums_def) apply auto
 apply (simp add:ordinal_number_def) apply (erule conjE)+
 apply (frule_tac S = Z and T = Da in well_ordered_set_sym, assumption+)
 apply (frule_tac S = Y and T = Da and U = Z in well_ordered_set_trans, assumption+)
 apply (rule_tac S = Y and T = Z and U = "Iod D (segment D d)" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_well_ordered_set) apply assumption+
done

lemma ODnum_segmentTr1:"\<lbrakk>well_ordered_set D; x = ordinal_number D; y \<in> ODnums; ODord y x\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> carrier D \<and> (y = ordinal_number (Iod D (segment D c)))"
apply (simp add:ODnums_def) 
apply (subgoal_tac "\<forall>F. well_ordered_set F \<and> y = ordinal_number F \<longrightarrow> (\<exists>c. c \<in> carrier D \<and> y = ordinal_number (Iod D (segment D c)))")
apply blast apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule ODnum_segmentTr [of "D" "x" "y"], assumption+)
 apply (simp add:ODnums_def) apply blast apply simp
 apply (subgoal_tac "\<forall>c. c \<in>carrier D \<and> (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c))) \<longrightarrow> (\<exists>c. c \<in> carrier D \<and> y = ordinal_number (Iod D (segment D c)))")
 apply blast
 apply (thin_tac "\<exists>c. c \<in> carrier D \<and> (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c)))")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac D = F and x = y in ordinal_numberTr2, assumption+) 
 apply (subgoal_tac "ord_equiv F (Iod D (segment D c))")
 prefer 2 apply simp apply (thin_tac "\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c))")
 apply (subgoal_tac "y = ordinal_number (Iod D (segment D c))")
 apply blast apply (thin_tac " x = ordinal_number D")
 apply (frule sym) apply (thin_tac "ordinal_number F = y")
 apply simp apply (thin_tac " y = ordinal_number F")
 apply (subst ordinal_number_def) apply (subst ordinal_number_def)
apply (frule_tac S = D and a = c in segment_well_ordered_set, assumption+)
apply (rule equalityI)
 apply (rule subsetI) apply simp apply (erule conjE)
 apply (rule_tac S = x and T = F and U = "Iod D (segment D c)" in well_ordered_set_trans, assumption+)
 apply (rule subsetI) apply simp apply (erule conjE)
apply (frule_tac S = F and T = "(Iod D (segment D c))" in well_ordered_set_sym)
 apply assumption+
apply (rule_tac S = x and T = "Iod D (segment D c)" and U = F in well_ordered_set_trans, assumption+)
done

constdefs
 ODNmap :: "'a OrderedSet \<Rightarrow> ('a OrderedSet) set \<Rightarrow> 'a"
 "ODNmap D y == SOME z. (z \<in> carrier D \<and> (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D z))))" 
 
lemma ODNmapTr:"\<lbrakk>well_ordered_set D; x = ordinal_number D; y \<in> ODnums; ODord y x\<rbrakk> \<Longrightarrow> ODNmap D y \<in> carrier D \<and> (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D (ODNmap D y))))" 
apply (frule ODnum_segmentTr [of "D" "x" "y"], assumption+)
apply (simp add:ODNmap_def)
apply (rule someI2_ex, assumption+)
done 

lemma ODNmapTr1:"\<lbrakk>well_ordered_set D; x = ordinal_number D; y \<in> ODnums; ODord y x\<rbrakk> \<Longrightarrow> y = ordinal_number (Iod D (segment D (ODNmap D y)))"
apply (frule ODNmapTr [of "D" "x" "y"], assumption+)  apply (erule conjE)
 apply (frule ODnum_segmentTr1 [of "D" "x" "y"], assumption+)
 apply (subgoal_tac "\<forall>c\<in>carrier D. y = ordinal_number (Iod D (segment D c))
 \<longrightarrow> y = ordinal_number (Iod D (segment D (ODNmap D y)))") apply blast
 apply (thin_tac "\<exists>c. c\<in>carrier D \<and> y = ordinal_number (Iod D (segment D c))")
 apply (rule ballI) apply (rule impI) 
apply (frule_tac S = D and a = c in segment_well_ordered_set, assumption+)
 apply (frule_tac D = "Iod D (segment D c)" and x = y in ordinal_numberTr2,
            assumption+)
 apply (subgoal_tac "ord_equiv (Iod D (segment D c)) (Iod D (segment D (ODNmap D y)))") prefer 2 apply simp 
 apply (rule_tac D = "Iod D (segment D c)" and F = "Iod D (segment D (ODNmap D y))" in ordinal_numberTr3, assumption+)
 apply (simp add:segment_well_ordered_set)
 apply assumption+
done

lemma ODNmap_self:"\<lbrakk>well_ordered_set D; c \<in> carrier D; a = ordinal_number (Iod D (segment D c))\<rbrakk> \<Longrightarrow> ODNmap D a = c"
apply (simp add:ODNmap_def)
apply (subgoal_tac "\<exists>d. d \<in> carrier D \<and> (\<forall>Y\<in>ordinal_number (Iod D (segment D c)). ord_equiv Y (Iod D (segment D d)))")
apply (rule someI2_ex)
 apply simp
apply (thin_tac "\<exists>d. d \<in> carrier D \<and> (\<forall>Y\<in>ordinal_number (Iod D (segment D c)). ord_equiv Y (Iod D (segment D d)))")
 apply (erule conjE)
 apply (frule_tac S = D and a = c in segment_well_ordered_set, assumption+)
 apply (frule_tac D = "Iod D (segment D c)" and x = a in ordinal_numberTr2,
  assumption+)
 apply (subgoal_tac "ord_equiv (Iod D (segment D c)) (Iod D (segment D x))")
 apply (thin_tac "\<forall>Y\<in>ordinal_number (Iod D (segment D c)). ord_equiv Y (Iod D (segment D x))")
 apply (rule segment_unique, assumption+)
 apply (frule_tac S = D and a = x in segment_well_ordered_set, assumption+) 
 apply (rule well_ordered_set_sym, assumption+)
 apply simp
apply (subgoal_tac "\<forall>Y\<in>ordinal_number (Iod D (segment D c)).
               ord_equiv Y (Iod D (segment D c))")
 apply blast
apply (rule ballI)
 apply (thin_tac "a = ordinal_number (Iod D (segment D c))")
 apply (simp add:ordinal_number_def)
done

lemma ODnum_lessTr:"\<lbrakk>well_ordered_set D; c \<in> carrier D; a = ordinal_number (Iod D (segment D c)); d \<in> carrier D; b = ordinal_number (Iod D (segment D d)); ODord a b\<rbrakk> \<Longrightarrow>  ODNmap D a <\<^sub>D (ODNmap D b)"
apply (frule ODNmap_self [of "D" "c" "a"], assumption+)
apply (frule ODNmap_self [of "D" "d" "b"], assumption+)
apply simp
 apply (thin_tac "a = ordinal_number (Iod D (segment D c))")
 apply (thin_tac "b = ordinal_number (Iod D (segment D d))")
 apply (thin_tac "ODNmap D (ordinal_number (Iod D (segment D c))) = c")
 apply (thin_tac "ODNmap D (ordinal_number (Iod D (segment D d))) = d")
apply (simp add:ODord_def) 
apply (frule segment_well_ordered_set [of "D" "c"], assumption+)
apply (frule segment_well_ordered_set [of "D" "d"], assumption+) 
apply (subgoal_tac "\<forall>x\<in>ordinal_number (Iod D (segment D c)). \<forall>y\<in>ordinal_number (Iod D (segment D d)). \<forall>z\<in>carrier y. ord_equiv x (Iod y (segment y z)) \<longrightarrow>
  c <\<^sub>D d")
 apply blast
 apply (thin_tac "\<exists>x\<in>ordinal_number (Iod D (segment D c)). \<exists>y\<in>ordinal_number (Iod D (segment D d)). \<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))")
 apply (rule ballI)+ apply (rule impI)
 apply (rename_tac X Y z)
 apply (subgoal_tac "ord_equiv X (Iod D (segment D c))")
 apply (subgoal_tac "ord_equiv Y (Iod D (segment D d))")
apply (subgoal_tac "\<exists>f. ord_isom Y (Iod D (segment D d)) f")
 apply (subgoal_tac "\<forall>f. ord_isom Y (Iod D (segment D d)) f \<longrightarrow>  c <\<^sub>D d") 
 apply blast apply (thin_tac "\<exists>f. ord_isom Y (Iod D (segment D d)) f")
 apply (rule allI) apply (rule impI)
 apply (frule segment_well_ordered_set [of "D" "d"], assumption+)
 apply (subgoal_tac "well_ordered_set Y")
 apply (frule_tac S = Y and T = "Iod D (segment D d)" and f = f in ord_isom_segment_segment, assumption+)
 apply (simp add:ord_isom_def)
 apply (erule conjE)+ 
 apply (frule_tac f = f and A = "carrier Y" and B = "carrier (Iod D (segment D d))" and x = z in funcset_mem, assumption+)
 apply (thin_tac "f \<in> extensional (carrier Y)")
 apply (thin_tac "f \<in> carrier Y \<rightarrow> carrier (Iod D (segment D d))")
 apply (thin_tac "bij_to f (carrier Y) (carrier (Iod D (segment D d)))")
 apply (thin_tac "\<forall>a\<in>carrier Y. \<forall>b\<in>carrier Y.  a <\<^sub>Y b =  f a <\<^sub>(Iod D (segment D d)) (f b)")
 apply (subgoal_tac "segment D (f z) \<subseteq> segment D d")
 apply (frule well_ordered_set_is_ordered_set [of "D"])  
 apply (frule_tac D = D and S = "segment D (f z)" and T = "segment D d" in Iod_sub_sub, assumption+)
 apply (rule subsetI) apply (simp add:segment_def) 
 apply (subgoal_tac "segment (Iod D (segment D d)) (f z) = segment D (f z)")
 apply simp
 apply (thin_tac "segment D (f z) \<subseteq> segment D d")
 apply (thin_tac "Iod (Iod D (segment D d)) (segment D (f z)) =
          Iod D (segment D (f z))")
 apply (thin_tac "segment (Iod D (segment D d)) (f z) = segment D (f z)")
 apply (frule segment_well_ordered_set [of "D" "c"], assumption+)
 apply (subgoal_tac "well_ordered_set X")
 apply (frule_tac S = X and T = "Iod D (segment D c)" in well_ordered_set_sym,
            assumption+)
 apply (subgoal_tac "well_ordered_set Y")
 apply (frule_tac S = "Iod D (segment D c)" and T = X and U = "Iod Y (segment Y z)" in well_ordered_set_trans, assumption+)
 apply (simp add:segment_well_ordered_set)
 apply (simp add:ordinal_number_def) apply assumption+
 apply (frule_tac S = Y and a = z in segment_well_ordered_set, assumption+)
 apply (frule_tac S = "Iod D (segment D c)" and T = "Iod Y (segment Y z)" and U = "Iod D (segment D (f z))" in well_ordered_set_trans, assumption+)
 apply (rule segment_well_ordered_set, assumption+)
  apply (simp add:Iod_def segment_def) apply assumption+
 apply (subgoal_tac "ordinal_number (Iod D (segment D c)) = ordinal_number (Iod D (segment D (f z)))")
 apply simp
 apply (frule_tac D = D and c = c and a = "ordinal_number (Iod D (segment D c))" in ODNmap_self, assumption+) apply simp apply simp
 apply (subgoal_tac "f z \<in> carrier D")
 apply (frule_tac D = D and c = "f z" and a = "ordinal_number (Iod D (segment D (f z)))" in ODNmap_self, assumption+) apply simp apply (rotate_tac -3)
 apply (frule sym) apply (thin_tac "ODNmap D (ordinal_number (Iod D (segment D (f z)))) = c")
 apply simp
 apply (thin_tac "ODNmap D (ordinal_number (Iod D (segment D (f z)))) = f z")
 apply (thin_tac "X \<in> ordinal_number (Iod D (segment D (f z)))")
 apply (thin_tac "Y \<in> ordinal_number (Iod D (segment D d))")
 apply (thin_tac "z \<in> carrier Y")
 apply (thin_tac "ord_equiv X (Iod Y (segment Y z))")
 apply (thin_tac "ord_equiv X (Iod D (segment D (f z)))")
 apply (thin_tac "ord_equiv Y (Iod D (segment D d))")
 apply (thin_tac "well_ordered_set (Iod D (segment D d))")
 apply (thin_tac "ord_equiv (Iod Y (segment Y z)) (Iod D (segment D (f z)))")
 apply (thin_tac "well_ordered_set (Iod D (segment D (f z)))")
 apply (thin_tac "ord_equiv (Iod D (segment D (f z))) X")
 apply (thin_tac "well_ordered_set (Iod Y (segment Y z))")
 apply (thin_tac "ord_equiv (Iod D (segment D (f z))) (Iod Y (segment Y z))")
 apply (thin_tac "ord_equiv (Iod D (segment D (f z))) (Iod D (segment D (f z)))")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (simp add:Iod_def segment_def)
 apply (frule_tac S = D and a = "f z" in segment_well_ordered_set)
 apply (simp add:Iod_def segment_def)
apply (frule_tac F = "Iod D (segment D (f z))" and x = "ordinal_number (Iod D (segment D c))" in ordinal_numberTr3 [of "Iod D (segment D c)"], assumption+)
 apply simp+
 apply (simp add:ordinal_number_def)
 apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule subsetI)
 apply (thin_tac "well_ordered_set (Iod D (segment D c))")
 apply (thin_tac "X \<in> ordinal_number (Iod D (segment D c))")
 apply (thin_tac "Y \<in> ordinal_number (Iod D (segment D d))")
 apply (thin_tac "ord_equiv X (Iod Y (segment Y z))")
 apply (thin_tac "ord_equiv X (Iod D (segment D c))")
 apply (thin_tac "ord_equiv Y (Iod D (segment D d))")
 apply (thin_tac "well_ordered_set (Iod D (segment D d))")
 apply (thin_tac "ord_equiv (Iod Y (segment Y z)) (Iod (Iod D (segment D d))
             (segment (Iod D (segment D d)) (f z)))")
 apply (thin_tac "segment D (f z) \<subseteq> segment D d")
 apply (thin_tac "Iod (Iod D (segment D d)) (segment D (f z)) =
          Iod D (segment D (f z))")
apply (simp add:Iod_def segment_def ord_neq_def) apply (erule conjE)+
 apply (frule_tac D = D and a = x and b = "f z" and c = d in ordering_axiom3,
              assumption+) apply simp apply (rule contrapos_pp, simp+)
 apply (frule_tac D = D and a = "f z" and b = d in ordering_axiom2, assumption+) apply simp
apply (thin_tac "well_ordered_set (Iod D (segment D c))")
 apply (thin_tac "X \<in> ordinal_number (Iod D (segment D c))")
 apply (thin_tac "Y \<in> ordinal_number (Iod D (segment D d))")
 apply (thin_tac "ord_equiv X (Iod Y (segment Y z))")
 apply (thin_tac "ord_equiv X (Iod D (segment D c))")
 apply (thin_tac "ord_equiv Y (Iod D (segment D d))")
 apply (thin_tac "well_ordered_set (Iod D (segment D d))")
 apply (thin_tac "ord_equiv (Iod Y (segment Y z)) (Iod (Iod D (segment D d))
             (segment (Iod D (segment D d)) (f z)))")
 apply (rule subsetI) apply (simp add:segment_def Iod_def ord_neq_def)
 apply (erule conjE)+
 apply (frule well_ordered_set_is_ordered_set [of "D"])
 apply (frule_tac a = x and b = "f z" and c = d in ordering_axiom3, assumption+) apply simp apply (rule contrapos_pp, simp+)
 apply (frule_tac a = "f z" and b = d in ordering_axiom2, assumption+)
 apply simp
 apply (simp add:ordinal_number_def)
 apply (simp add:ord_equiv_def)
apply (thin_tac "well_ordered_set (Iod D (segment D c))")
apply (thin_tac "X \<in> ordinal_number (Iod D (segment D c))")
 apply (thin_tac "ord_equiv X (Iod Y (segment Y z))")
 apply (thin_tac "ord_equiv X (Iod D (segment D c))")
 apply (simp add:ordinal_number_def)
apply (simp add:ordinal_number_def)
done

lemma ODnum_subTr1:"\<lbrakk>well_ordered_set D; x = ordinal_number D\<rbrakk>  \<Longrightarrow> ord_equiv (Iod ODnods {y. y \<in>ODnums \<and> ODord y x}) D"
apply (subst ord_equiv_def)
apply (subgoal_tac "ord_isom (Iod ODnods {y. y \<in> ODnums \<and> ODord y x}) D (\<lambda>x\<in>(carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y x})). (ODNmap D x))") 
 apply blast
 apply (simp add:ord_isom_def)
 apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:Iod_def) apply (erule conjE)
 apply (frule_tac D = D and x = x and y = xa in ODNmapTr, assumption+)
 apply simp apply simp
apply (rule conjI)
 apply (simp add:bij_to_def)
 apply (rule conjI)
 apply (rule surj_to_test)
 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:Iod_def) apply (erule conjE)
 apply (frule_tac D = D and x = x and y = xa in ODNmapTr, assumption+)
 apply simp apply simp
 apply (rule ballI)
 apply (frule_tac a = b in segment_well_ordered_set [of "D"], assumption+)
 apply (subgoal_tac "ordinal_number (Iod D (segment D b)) \<in> carrier  (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)})")
 apply (subgoal_tac "restrict (ODNmap D) (carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)})) (ordinal_number (Iod D (segment D b))) = b")
 apply blast
apply (simp add:Iod_def) apply (fold Iod_def) apply (erule conjE)
 apply (frule_tac y = "ordinal_number (Iod D (segment D b))" in ODNmapTr [of "D" "x"], assumption+)
 apply simp apply (erule conjE)+
 apply (subgoal_tac "(Iod D (segment D b)) \<in> ordinal_number (Iod D (segment D b))")
 apply (subgoal_tac "ord_equiv (Iod D (segment D b)) (Iod D (segment D 
  (ODNmap D (ordinal_number (Iod D (segment D b))))))")
 prefer 2 apply simp
 apply (thin_tac "\<forall>Y\<in>ordinal_number (Iod D (segment D b)). ord_equiv Y
  (Iod D (segment D (ODNmap D (ordinal_number (Iod D (segment D b))))))")
 apply (frule_tac a = b in segment_well_ordered_set [of "D"], assumption+)
 apply (frule_tac a = "ODNmap D (ordinal_number (Iod D (segment D b)))" in segment_well_ordered_set [of "D"], assumption+) 
 apply (frule_tac a = b and b = "ODNmap D (ordinal_number (Iod D (segment D b)))" in segment_unique [of "D"], assumption+)
 apply (rule sym, assumption+) 
 apply (thin_tac "\<forall>Y\<in>ordinal_number (Iod D (segment D b)). ord_equiv Y
 (Iod D (segment D (ODNmap D (ordinal_number (Iod D (segment D b))))))")
 apply (subst ordinal_number_def) apply simp
 apply (frule_tac S = "Iod D (segment D b)" in well_ordered_set_is_ordered_set)
 apply (simp add:ord_equiv_reflex)
 apply (subst ordinal_number_def) apply (simp add:Iod_def) apply (fold Iod_def)
 apply (rule conjI) apply (simp add:ODnums_def)
 apply (simp add:ordinal_number_def) apply blast
 apply (subst ODord_def)
 apply (subgoal_tac "(Iod D (segment D b)) \<in> ordinal_number (Iod D (segment D b))")
 apply (subgoal_tac "D \<in> {X. well_ordered_set X \<and> ord_equiv X D}")
 apply (subgoal_tac "ord_equiv (Iod D (segment D b)) (Iod D (segment D b))")
 apply blast
 apply (rule ord_equiv_reflex)
 apply (simp add:well_ordered_set_is_ordered_set)
 apply simp
 apply (rule ord_equiv_reflex) apply (simp add:well_ordered_set_is_ordered_set)
 apply (simp add:ordinal_number_def)
 apply (rule ord_equiv_reflex)
 apply (simp add:well_ordered_set_is_ordered_set)
apply (simp add:inj_on_def)
 apply (rule ballI)+
 apply (simp add:Iod_def) apply (erule conjE)+
 apply (rule impI) 
 apply (frule_tac D = D and x = x and y = xa in ODNmapTr1, assumption+)
  apply simp
 apply (frule_tac D = D and x = x and y = y in ODNmapTr1, assumption+)
  apply simp apply simp
apply (rule ballI)+
 apply (simp add:Iod_def ODnods_def ord_neq_def) apply (erule conjE)+
apply (subgoal_tac "ODord a b = ODNmap D a <\<^sub>D (ODNmap D b)")
 apply (simp add:ODord_eq_def ord_neq_def) apply blast
apply (frule_tac D = D and x = x and y = a in ODnum_segmentTr1, assumption+)
 apply simp
 apply (frule_tac D = D and x = x and y = b in ODnum_segmentTr1, assumption+)
 apply simp
 apply (subgoal_tac "\<forall>c d. c \<in> carrier D \<and> a = ordinal_number (Iod D (segment D c)) \<and> d \<in> carrier D \<and> b = ordinal_number (Iod D (segment D d)) \<longrightarrow>
 ODord a b =  ODNmap D a <\<^sub>D (ODNmap D b)")
 apply blast
 apply (thin_tac "\<exists>c. c \<in> carrier D \<and> b = ordinal_number (Iod D (segment D c))")
 apply (thin_tac "\<exists>c. c \<in> carrier D \<and> a = ordinal_number (Iod D (segment D c))")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
apply (case_tac "ODord a b")
 apply (frule_tac c = c and a = a and d = d and b = b in ODnum_lessTr [of "D"],
       assumption+) apply simp 
 apply (subgoal_tac "a \<in> carrier ODnods")
 apply (subgoal_tac "b \<in> carrier ODnods")
apply (frule_tac X = a and Y = b in ordinal_number_ord, assumption+)
 prefer 2 apply (simp add:ODnods_def)
 prefer 2 apply (simp add:ODnods_def)
apply (subgoal_tac "a = b \<or> ODord b a")
 apply (subgoal_tac "\<not> ODNmap D a <\<^sub>D (ODNmap D b)")
 apply simp
 apply (thin_tac "\<not> ODord a b")
 apply (thin_tac "ODord a b \<or> a = b \<or> ODord b a")
apply (subst ord_neq_def) apply simp
 apply (simp add:ODNmap_self)
 apply (subgoal_tac "c = d \<or> d <\<^sub>D c")
 apply (case_tac "c = d") apply (rule impI) apply simp
 apply (rule impI)
 apply (subgoal_tac "d <\<^sub>D c")
 apply (subgoal_tac "tordered_set D")
 apply (frule_tac D = D and a = d and b = c in tordering_not1, assumption+)
 apply simp
  apply (simp add:well_ordered_set_def)
  apply (simp add:ord_neq_def)
apply (case_tac "ordinal_number (Iod D (segment D c)) = ordinal_number (Iod D (segment D d))")
 apply (subgoal_tac "ODNmap D (ordinal_number (Iod D (segment D c))) = ODNmap D (ordinal_number (Iod D (segment D d)))")
 apply (thin_tac "ordinal_number (Iod D (segment D c)) =
          ordinal_number (Iod D (segment D d))")
 apply (simp add:ODNmap_self) apply simp apply simp
 apply (thin_tac "ordinal_number (Iod D (segment D c)) \<noteq>
          ordinal_number (Iod D (segment D d))")
 apply (frule_tac c = d and a = "ordinal_number (Iod D (segment D d))" and d = c and b = "ordinal_number (Iod D (segment D c))" in ODnum_lessTr [of "D"],
 assumption+) apply simp apply assumption+ apply simp apply assumption
 apply (simp add:ODNmap_self)
 apply simp
done

lemma ODnods_ordered:"ordered_set ODnods"
apply (simp add:ordered_set_def)
 apply (simp add:ODnods_def)
apply (rule conjI)
 apply (simp add:ODrel_def)
 apply (rule subsetI)  apply simp
apply (rule conjI)
 apply (rule ballI) apply (simp add:ODrel_def) apply (simp add:ODord_eq_def)
apply (rule conjI)
 apply (rule ballI)+ apply (rule impI)
 apply (simp add:ODrel_def) apply (erule conjE)
 apply (simp add:ODord_eq_def)
 apply (case_tac "a = b") apply simp apply simp
 apply (frule not_sym) apply simp
apply (subgoal_tac "\<exists>D. well_ordered_set D \<and> a = ordinal_number D")
 prefer 2 apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>D. well_ordered_set D \<and> a = ordinal_number D \<longrightarrow>
  False") apply blast
  apply (thin_tac "\<exists>D. well_ordered_set D \<and> a = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac D = D and x = a and y = b in ODnum_segmentTr1, assumption+)
 apply (subgoal_tac "\<forall>c. c \<in> carrier D \<and> b = ordinal_number (Iod D (segment D c)) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>c. c \<in> carrier D \<and> b = ordinal_number (Iod D (segment D c))")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac S = D and a = c in segment_well_ordered_set, assumption+)
 apply (frule_tac D = "Iod D (segment D c)" and x = b and y = a in ODnum_segmentTr1, assumption+)
 apply (subgoal_tac "\<forall>ca.  ca \<in> carrier (Iod D (segment D c)) \<and> a = ordinal_number (Iod (Iod D (segment D c)) (segment (Iod D (segment D c)) ca)) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>ca.  ca \<in> carrier (Iod D (segment D c)) \<and> a = ordinal_number (Iod (Iod D (segment D c)) (segment (Iod D (segment D c)) ca))") 
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "Iod (Iod D (segment D c)) (segment (Iod D (segment D c)) ca ) = Iod D (segment D ca)") apply simp
 apply (thin_tac "Iod (Iod D (segment D c)) (segment (Iod D (segment D c)) ca) = Iod D (segment D ca)")
 apply (subgoal_tac "D \<in> ordinal_number (Iod D (segment D ca))")
 apply (thin_tac "ordinal_number (Iod D (segment D ca)) = ordinal_number D")
 prefer 2 
 apply (frule_tac D = D and x = a in ordinal_numberTr2, assumption+)
 apply simp
  apply (thin_tac "ordinal_number (Iod D (segment D c)) \<in> ODnums")
  apply (thin_tac "ODord (ordinal_number D) (ordinal_number (Iod D (segment D c)))")
  apply (thin_tac "ODord (ordinal_number (Iod D (segment D c))) (ordinal_number D)")
  apply (thin_tac "ordinal_number D \<noteq> ordinal_number (Iod D (segment D c))")
  apply (thin_tac "ordinal_number (Iod D (segment D c)) \<noteq> ordinal_number D")
  apply (thin_tac "ordinal_number D \<in> ODnums")
  apply (thin_tac " b = ordinal_number (Iod D (segment D c))")
  apply (thin_tac "well_ordered_set (Iod D (segment D c))")
 apply (subgoal_tac "ca \<in> carrier D") apply (thin_tac " ca \<in> carrier (Iod D (segment D c))")
  apply (thin_tac "a = ordinal_number D")
 apply (simp add:ordinal_number_def)
 apply (frule_tac S = D and a = ca in not_ordequiv_segment, assumption+) 
 apply simp 
 apply (simp add:Iod_def segment_def)
 apply (thin_tac "a = ordinal_number (Iod (Iod D (segment D c)) (segment (Iod D (segment D c)) ca))")
  apply (thin_tac "b = ordinal_number (Iod D (segment D c))")
  apply (thin_tac "well_ordered_set (Iod D (segment D c))")
 apply (subgoal_tac "segment (Iod D (segment D c)) ca = segment D ca")
 apply simp apply (thin_tac "segment (Iod D (segment D c)) ca = segment D ca")
 apply (subgoal_tac "segment D ca \<subseteq> segment D c")
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac D = D and S = "segment D ca" and T = "segment D c" in Iod_sub_sub, assumption+)
 apply (rule subsetI) apply (simp add:segment_def) apply simp
 apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac D = D and a = x and b = ca and c = c in ordering_axiom3,
                                  assumption+) apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac D = D and a = c and b = ca in ordering_axiom2, assumption+) 
 apply simp
 apply (rule equalityI)
  apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
  apply (rule subsetI) apply (simp add:Iod_def segment_def ord_neq_def)
  apply (erule conjE)+
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac D = D and a = x and b = ca and c = c in ordering_axiom3, assumption+) apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac D = D and a = c and b = ca in ordering_axiom2, assumption+) apply simp
apply (rule conjI)
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply (simp add:ODrel_def)
 apply (frule_tac X = a and Y = b and Z = c in ODord_eq_trans, assumption+)
apply (rule ballI)+
 apply (simp add:ODrel_def)
done

lemma ODnum_less_not_eq:"\<lbrakk> x \<in> ODnums; y \<in> ODnums; ODord x y \<rbrakk> \<Longrightarrow> x \<noteq> y"
apply (subgoal_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 prefer 2 apply (simp add:ODnums_def)
 apply (subgoal_tac "\<forall>D. well_ordered_set D \<and> y = ordinal_number D \<longrightarrow>
               x \<noteq> y") apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> y = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac D = D and x = y and y = x in ODnum_segmentTr1, assumption+) 
 apply (subgoal_tac "\<forall>c. c \<in> carrier D \<and> x = ordinal_number (Iod D (segment D c)) \<longrightarrow> x \<noteq> y") apply blast
 apply (thin_tac "\<exists>c. c \<in> carrier D \<and> x = ordinal_number (Iod D (segment D c))")
 apply (rule allI) apply (rule impI) apply (erule conjE)
apply (rule contrapos_pp, simp+)
 apply (thin_tac "y = ordinal_number D")
 apply (frule_tac D = D and x = x in ordinal_numberTr2, assumption+) 
 apply (subgoal_tac "D \<in> ordinal_number (Iod D (segment D c))")
 apply (thin_tac "ordinal_number (Iod D (segment D c)) = ordinal_number D")
 apply (thin_tac "D \<in> x")
 apply (simp add:ordinal_number_def)
 apply (frule_tac S = D and a = c in not_ordequiv_segment, assumption+)
 apply simp
apply simp
done

lemma ODnum_sub_well_ordered:"S \<subseteq> ODnums \<Longrightarrow> well_ordered_set (Iod ODnods S)"
apply (simp add:well_ordered_set_def)
apply (rule conjI)
 apply (simp add:tordered_set_def)
 apply (rule conjI)
 apply (subgoal_tac "ordered_set ODnods") 
 prefer 2 apply (simp add:ODnods_ordered)
 apply (rule ordered_set_Iod, assumption+) 
 apply (simp add:ODnods_def)
 (* ------------------- *)
 apply (rule ballI)+ apply (simp add:Iod_def) 
 apply (simp add:ODnods_def)
 apply (simp add:ODord_eq_def)
 apply (frule_tac A = S and B = ODnums and c = a in subsetD, assumption+)
 apply (frule_tac A = S and B = ODnums and c = b in subsetD, assumption+) 
 apply (subgoal_tac "a \<in> carrier ODnods") 
 apply (subgoal_tac "b \<in> carrier ODnods")
 apply (frule_tac X = a and Y = b in ordinal_number_ord, assumption+)
 apply blast
 apply (simp add:ODnods_def) apply (simp add:ODnods_def)
 (* ------------------ *)
apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac A = X in nonempty_ex)
 apply (subgoal_tac "\<forall>x. x \<in> X \<longrightarrow> (\<exists>x. minimum_elem (Iod ODnods S) X x)") apply blast apply (thin_tac "\<exists>x. x \<in> X")
 apply (rule allI) apply (rule impI)
apply (case_tac "minimum_elem (Iod ODnods S) X x")
 apply blast
 apply (subgoal_tac "segment (Iod (Iod ODnods S) X) x \<noteq> {}")
 apply (subgoal_tac "segment (Iod (Iod ODnods S) X) x = segment (Iod ODnods X) x") 
 apply simp
 prefer 2  apply (rule equalityI)
  apply (rule subsetI) apply (simp add:segment_def Iod_def ODnods_def ord_neq_def)
  apply (rule subsetI)
  apply (simp add:segment_def Iod_def ODnods_def ord_neq_def)
 apply (thin_tac " segment (Iod (Iod ODnods S) X) x = segment (Iod ODnods X) x")
 apply (subgoal_tac "\<exists>y. minimum_elem (Iod ODnods S) X y")
 apply simp
 apply (subgoal_tac "carrier (Iod ODnods S) = S") apply simp
 prefer 2 apply (simp add:Iod_def)
 apply (thin_tac "carrier (Iod ODnods S) = S")
 apply (frule_tac A = X and B = S and c = x in subsetD, assumption+)
 apply (frule_tac A = S and B = ODnums and c = x in subsetD, assumption+)
 apply (simp add:ODnums_def) 
 apply (subgoal_tac "\<forall>D. well_ordered_set D \<and> x = ordinal_number D \<longrightarrow> (\<exists>y. minimum_elem (Iod ODnods S) X y)")
 apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> x = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)
prefer 2 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "minimum_elem (Iod ODnods S) X x") apply simp
 apply (thin_tac "\<not> minimum_elem (Iod ODnods S) X x")
 apply (simp add:minimum_elem_def) apply (rule ballI)
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "x \<in> carrier ODnods")
 apply (subgoal_tac "xa \<in> carrier ODnods")
 apply (frule_tac X = x and Y = xa in ordinal_number_ord, assumption+)
 apply (simp add:ODnods_def)
 apply (rename_tac X u v)
 apply (case_tac "ODord u v") apply (simp add:ODord_eq_def)
 apply (case_tac "u = v")  apply (simp add:ODord_eq_def)
 apply simp
 apply (subgoal_tac "ODord_eq v u") prefer 2 apply (simp add:ODord_eq_def)
 apply (subgoal_tac "v = u \<or> v \<notin> X") prefer 2 
 apply (thin_tac "\<not> ODord u v") apply (thin_tac "u \<noteq> v") 
 apply (thin_tac "v \<in> X") apply simp apply blast
 apply (thin_tac "\<forall>xa.  xa \<le>\<^sub>ODnods x \<longrightarrow> xa = x \<or> xa \<notin> X")
 apply (frule_tac A = X and B = S and c = xa in subsetD, assumption+)
 apply (frule_tac A = S and B = ODnums and c = xa in subsetD, assumption+)
 apply (simp add:ODnods_def)
 apply (frule_tac A = X and B = S and c = x in subsetD, assumption+)
 apply (frule_tac A = S and B = ODnums and c = x in subsetD, assumption+)
 apply (simp add:ODnods_def)
(* ---------------------- *)
 apply (frule_tac D = D and x = x in ODnum_subTr1, assumption+)
 apply (unfold ord_equiv_def)
 apply (subgoal_tac "\<forall>f. ord_isom (Iod ODnods {y. y \<in> ODnums \<and> ODord y x}) D f
 \<longrightarrow> (\<exists>y. minimum_elem (Iod ODnods S) X y)")
 apply blast
 apply (thin_tac "\<exists>f. ord_isom (Iod ODnods {y. y \<in> ODnums \<and> ODord y x}) D f")
 apply (rule allI) apply (rule impI)
apply (subgoal_tac "segment (Iod ODnods X) x \<subseteq> carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y x})")
 apply (subgoal_tac "\<exists>y0. minimum_elem D (f ` (segment (Iod ODnods X) x)) y0")
 apply (subgoal_tac "\<forall>y0. minimum_elem D (f ` segment (Iod ODnods X) x) y0 \<longrightarrow>
 (\<exists>y. minimum_elem (Iod ODnods S) X y)") apply blast
 apply (thin_tac " \<exists>y0. minimum_elem D (f ` segment (Iod ODnods X) x) y0")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "\<exists>x0\<in>segment (Iod ODnods X) x. f x0 = y0")
 apply (subgoal_tac "\<forall>x0\<in>segment (Iod ODnods X) x. f x0 = y0 \<longrightarrow> (\<exists>y. minimum_elem (Iod ODnods S) X y)") apply blast apply (thin_tac "\<exists>x0\<in>segment (Iod ODnods X) x. f x0 = y0")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "minimum_elem (Iod ODnods S) X x0")
 apply blast
apply (subst minimum_elem_def) apply simp 
 apply (subgoal_tac "x0 \<in> X") apply simp
 prefer 2  apply (simp add:Iod_def segment_def)
 apply (rule ballI)
 apply (subst Iod_def) apply (simp add:ord_neq_def) apply (subst ODnods_def)
 apply (simp add:ord_neq_def) 
 apply (frule_tac A = X and B = S and c = xa in subsetD, assumption+)
 apply (frule_tac A = S and B = "{X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}" and c = xa in subsetD, assumption+)
 apply (subgoal_tac "\<exists>F. well_ordered_set F \<and> xa = ordinal_number F")
 prefer 2 apply (simp add:ordinal_number_def ord_equiv_def)
 apply (subgoal_tac "\<forall>F. well_ordered_set F \<and> xa = ordinal_number F \<longrightarrow>
 ODord_eq x0 xa") apply blast apply (thin_tac "\<exists>F. well_ordered_set F \<and> xa = ordinal_number F")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "x \<in> carrier ODnods")
 apply (subgoal_tac "xa \<in> carrier ODnods")
 prefer 2 apply (simp add:ODnods_def ODnums_def) 
 apply (frule_tac X = x and Y = xa in ordinal_number_ord, assumption+)
 apply (subgoal_tac "ordinal_number D = x") apply (thin_tac "x = ordinal_number D")
 apply (subgoal_tac "ordinal_number F = xa") 
  apply (thin_tac "xa = ordinal_number F")
 apply simp
 apply (case_tac "ODord x xa \<or> x = xa")
 apply (subgoal_tac "ODord_eq x xa")
 apply (subgoal_tac "x0 \<in> ODnums")
 apply (subgoal_tac "x \<in> ODnums")
 apply (subgoal_tac "xa \<in> ODnums")
 apply (subgoal_tac "ODord_eq x0 x")
 apply (frule_tac X = x0 and Y = x and Z = xa in ODord_eq_trans, assumption+)
 apply (simp add:segment_def Iod_def ord_neq_def ODnods_def)
  apply (thin_tac " segment (Iod ODnods X) x
          \<subseteq> carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y x})")
  apply (thin_tac "\<exists>D. well_ordered_set D \<and> xa = ordinal_number D")
  apply (thin_tac "segment (Iod ODnods X) x \<noteq> {}")
 apply (simp add:ODnods_def)
 apply (simp add:ODnums_def) apply blast
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> xa = ordinal_number D")
 apply (subgoal_tac "x0 \<in> X")
 apply (frule_tac A = X and B = S and c = x0 in subsetD, assumption+)
 apply (frule_tac A = S and B = "{X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}" and c = x0 in subsetD, assumption+)
 apply (simp add:ODnums_def)
 apply (simp add:Iod_def segment_def)
 apply (simp add:ODord_eq_def) apply blast 
apply simp
 apply (thin_tac "\<exists>D. well_ordered_set D \<and> xa = ordinal_number D")
 apply (thin_tac "\<not> ODord x xa \<and> x \<noteq> xa")
 apply (subgoal_tac "xa \<in> segment (Iod ODnods X) x")
 apply (simp add:minimum_elem_def) apply (erule conjE)
 apply (rename_tac X u D f y0 x0 xa F)
 apply (subgoal_tac "y0 \<le>\<^sub>D (f xa)") prefer 2 apply simp
 apply (thin_tac "\<forall>x\<in>segment (Iod ODnods X) u.  y0 \<le>\<^sub>D (f x)")
 apply (subgoal_tac "y0 = f x0") apply (thin_tac "f x0 = y0")
 apply simp apply (thin_tac "y0 = f x0")
apply (subgoal_tac "ordered_set ODnods") 
 prefer 2 apply (simp add: ODnods_ordered)
 apply (subgoal_tac "{y. y \<in> ODnums \<and> ODord y u} \<subseteq> carrier ODnods")
 apply (frule_tac D = ODnods and T = "{y. y \<in> ODnums \<and> ODord y u}" in ordered_set_Iod, assumption+) 
 apply (frule_tac S = D in well_ordered_set_is_ordered_set)
 apply (frule_tac D = "Iod ODnods {y. y \<in> ODnums \<and> ODord y u}" and E = D and f = f and a = x0 and b = xa in ord_isom2_2, assumption+)
 apply (thin_tac "\<exists>x\<in>X. \<not>  u \<le>\<^sub>(Iod ODnods S) x")
 apply (thin_tac "segment (Iod ODnods X) u \<noteq> {}")
 apply (thin_tac "ord_isom (Iod ODnods {y. y \<in> ODnums \<and> ODord y u}) D f")
 apply (thin_tac "segment (Iod ODnods X) u
          \<subseteq> carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y u})")
 apply (thin_tac "ordered_set (Iod ODnods {y. y \<in> ODnums \<and> ODord y u})")
 apply (simp add:Iod_def segment_def ord_neq_def) 
 apply (frule_tac A = X and B = S and c = x0 in subsetD, assumption+)
 apply (frule_tac A = S and B = "{X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}" and c = x0 in subsetD, assumption+)
 apply simp
 apply (subgoal_tac "\<forall>G. well_ordered_set G \<and> x0 = ordinal_number G \<longrightarrow>
  x0 \<in> ODnums \<and> ODord x0 u") apply blast
  apply (thin_tac "\<exists>D. well_ordered_set D \<and> x0 = ordinal_number D")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (simp add:ODnods_def ODord_eq_def)
 apply (simp add:ODnums_def) apply blast
 apply (thin_tac "\<exists>x\<in>X. \<not>  u \<le>\<^sub>(Iod ODnods S) x")
 apply (thin_tac "segment (Iod ODnods X) u \<noteq> {}")
 apply (thin_tac "ord_isom (Iod ODnods {y. y \<in> ODnums \<and> ODord y u}) D f")
 apply (thin_tac "segment (Iod ODnods X) u
          \<subseteq> carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y u})")
 apply (thin_tac "ordered_set (Iod ODnods {y. y \<in> ODnums \<and> ODord y u})")
 apply (simp add:Iod_def) apply (fold Iod_def)
 apply (frule_tac A = S and B = "{X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}" and c = xa in subsetD, assumption+)
 apply (simp add:ODnums_def) apply assumption
 apply (simp add:Iod_def) apply (fold Iod_def) apply (simp add:ODnods_def)
 (* ----------------- *)
apply (rule subsetI) apply (simp add:ODnods_def)
apply (rule sym, assumption+) 
apply (simp add:Iod_def segment_def) apply (fold Iod_def)
 apply (simp add:Iod_def ODnods_def ord_neq_def)
 apply (simp add:ODord_eq_def)
 apply (rule_tac x = xa and y = x in ODnum_less_not_eq, assumption+)
apply (rule sym, assumption+) apply (rule sym, assumption+)
 apply (simp add:ODnods_def ODnums_def)
 apply blast
apply (simp add:minimum_elem_def) apply (erule conjE)
 apply (thin_tac "\<forall>x\<in>segment (Iod ODnods X) (ordinal_number D).  y0 \<le>\<^sub>D (f x)")
 apply (simp add:image_def) apply blast
 apply (frule_tac A = "segment (Iod ODnods X) x" in nonempty_ex)
 apply (subgoal_tac "\<forall>xa. xa \<in> segment (Iod ODnods X) x \<longrightarrow> (\<exists>y0. minimum_elem D (f ` segment (Iod ODnods X) x) y0)")
 apply blast apply (thin_tac "\<exists>xa. xa \<in> segment (Iod ODnods X) x")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "f ` (segment (Iod ODnods X) x) \<noteq> {}")
 apply (thin_tac "segment (Iod ODnods X) x \<noteq> {}")
 apply (thin_tac "segment (Iod ODnods X) x
          \<subseteq> carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y x})")
 apply (subgoal_tac "f ` (segment (Iod ODnods X) x) \<subseteq> carrier D")
 apply (thin_tac "S \<subseteq> {X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}")
 apply (thin_tac "\<not> minimum_elem (Iod ODnods S) X x")
 apply (thin_tac "x = ordinal_number D")
 apply (simp add:well_ordered_set_def)
(* ------------------- *)
apply (thin_tac "\<not> minimum_elem (Iod ODnods S) X x")
 apply (thin_tac "xa \<in> segment (Iod ODnods X) x")
 apply (simp add:ord_isom_def) apply (erule conjE)+
 apply (thin_tac "f \<in> extensional (carrier
                 (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)}))")
 apply (thin_tac "bij_to f (carrier
 (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)})) (carrier D)")
 apply (thin_tac "\<forall>a\<in>carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)}).  \<forall>b\<in>carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)}).  a <\<^sub>(Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)}) b = f a <\<^sub>D (f b)")
 apply (subgoal_tac "segment (Iod ODnods X) (ordinal_number D) \<subseteq>  carrier
               (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)})")
 apply (frule_tac f = f and A = " carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y (ordinal_number D)})" and B = "carrier D" and ?A1.0 = "segment (Iod ODnods X) (ordinal_number D)" in image_sub, assumption+)
 apply (rule subsetI)
 apply (subgoal_tac "ordinal_number D = x") 
  apply (thin_tac "x = ordinal_number D") apply simp
  apply (thin_tac " f \<in> carrier (Iod ODnods {y. y \<in> ODnums \<and> ODord y x}) \<rightarrow>
              carrier D")
 apply (simp add:Iod_def segment_def ord_neq_def) apply (simp add:ODnums_def)
 apply (simp add:ODnods_def) apply (erule conjE)+
 apply (simp add:ODord_eq_def)
 apply (thin_tac "\<exists>xa. (xa = x \<or> ODord xa x) \<and> xa \<noteq> x \<and> xa \<in> X")
 apply (thin_tac "ordinal_number D = x")
 apply (frule_tac A = X and B = S and c = xa in subsetD, assumption+)
 apply (frule_tac A = S and B = "{X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}" and c = xa in subsetD, assumption+)
 apply simp apply (rule sym, assumption+)
 apply (simp add:ord_isom_def)
(* ----------------------- *)
apply (rule subsetI)
 apply (frule sym)  apply (thin_tac "x = ordinal_number D")
 apply (subgoal_tac "xa \<in> X")
 apply (frule_tac A = X and B = S and c = xa in subsetD, assumption+)
 apply (frule_tac A = S and B = "{X. \<exists>D. well_ordered_set D \<and> X = ordinal_number D}" and c = xa in subsetD, assumption+)
 apply simp
 apply (simp add:segment_def Iod_def ord_neq_def)
 apply (simp add:ODnums_def)
 apply (simp add:ODnods_def ODord_eq_def)
 apply blast
apply (simp add:Iod_def segment_def)
done

section "2. Pre"    (* pre elements *)

constdefs
  ExPre :: "['a OrderedSet, 'a] \<Rightarrow> bool"
  "ExPre S a == \<exists>x. (x \<in> carrier S \<and> x <\<^sub>S a \<and> \<not> (\<exists>y\<in>carrier S. (x <\<^sub>S y \<and> y <\<^sub>S a)))" 
  Pre :: "['a OrderedSet, 'a] \<Rightarrow> 'a" 
  "Pre S a == SOME x. (x \<in> carrier S \<and> x <\<^sub>S a \<and> \<not> (\<exists>y\<in>carrier S. (x <\<^sub>S y \<and> y <\<^sub>S a)))"

lemma UniquePre:"\<lbrakk>well_ordered_set S; a \<in> carrier S; ExPre S a;
 a1 \<in> carrier S \<and> a1 <\<^sub>S a \<and> \<not> (\<exists>y\<in>carrier S. (a1 <\<^sub>S y \<and> y <\<^sub>S a)) \<rbrakk> \<Longrightarrow>
 Pre S a = a1"
apply (simp add:ExPre_def)
apply (subst Pre_def)
apply (rule someI2_ex) apply blast
apply (erule conjE)+
 apply (rename_tac z)
 apply (thin_tac "\<exists>x. x \<in> carrier S \<and> x <\<^sub>S a \<and> (\<forall>y\<in>carrier S.  x <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S a)")
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "tordered_set S") prefer 2 apply (simp add:well_ordered_set_def)
 apply (simp add:tordered_set_def) apply (erule conjE)
 apply (subgoal_tac "z \<le>\<^sub>S a1 \<or>  a1 \<le>\<^sub>S z") prefer 2 apply simp
 apply (case_tac "z \<le>\<^sub>S a1")
  apply (subgoal_tac  "z <\<^sub>S a1") prefer 2 apply (simp add:ord_neq_def)
  apply (subgoal_tac "\<not> a1 <\<^sub>S a") prefer 2 apply simp
  apply (thin_tac "\<forall>y\<in>carrier S.  z <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S a")
  apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a")
  apply simp 
apply simp apply (frule not_sym) apply (thin_tac "z \<noteq> a1")
 apply (subgoal_tac "a1 <\<^sub>S z") prefer 2 apply (simp add:ord_neq_def)
 apply (thin_tac "\<forall>a\<in>carrier S. \<forall>b\<in>carrier S.  a \<le>\<^sub>S b \<or>  b \<le>\<^sub>S a")
 apply (thin_tac "\<forall>y\<in>carrier S.  z <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S a")
 apply (subgoal_tac "\<not> z <\<^sub>S a") prefer 2 apply simp
 apply simp
done

lemma Pre_element:"\<lbrakk>well_ordered_set S; a \<in> carrier S; ExPre S a\<rbrakk> \<Longrightarrow> Pre S a \<in> carrier S \<and> (Pre S a) <\<^sub>S a \<and> \<not> (\<exists>y\<in>carrier S. ((Pre S a) <\<^sub>S y \<and> y <\<^sub>S a))"
apply (simp add:ExPre_def)
apply (subst Pre_def)
apply (rule someI2_ex)
apply simp+
done

lemma Pre_segment:"\<lbrakk>well_ordered_set S; a \<in> carrier S; b \<in> segment S a; ExPre (Iod S (segment S a)) b\<rbrakk> \<Longrightarrow> ExPre S b \<and> Pre S b = Pre (Iod S (segment S a)) b"
apply (subgoal_tac "ExPre S b")
 prefer 2 
 apply (simp add:ExPre_def)
 apply auto
 apply (subgoal_tac "x <\<^sub>S b") prefer 2 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (subgoal_tac "x \<in> carrier S") prefer 2 apply (simp add:Iod_def segment_def)
 apply (subgoal_tac "\<forall>y\<in>carrier S.  x <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S b")
 apply blast
 apply (rule ballI) apply (rule impI)
 apply (case_tac "y \<in> carrier (Iod S (segment S a))")
 apply (subgoal_tac " x <\<^sub>(Iod S (segment S a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod S (segment S a)) b") prefer 2 apply simp
 apply (subgoal_tac "x <\<^sub>(Iod S (segment S a)) y") prefer 2 apply simp
 apply (thin_tac "\<forall>y\<in>carrier (Iod S (segment S a)).
                 x <\<^sub>(Iod S (segment S a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod S (segment S a)) b")
 apply (simp add:Iod_def ord_neq_def)
 apply (subgoal_tac "\<not>  y <\<^sub>(Iod S (segment S a)) b") prefer 2 apply simp
 apply (simp add:Iod_def ord_neq_def)
apply (thin_tac "\<forall>y\<in>carrier (Iod S (segment S a)).
       x <\<^sub>(Iod S (segment S a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod S (segment S a)) b")
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (rule impI) apply (erule conjE)+
 apply (case_tac "y \<le>\<^sub>S a") apply simp
  apply (frule_tac S = S in well_ordered_set_is_ordered_set)
  apply (frule_tac a = a and b = b in ordering_axiom2, assumption+)
 apply (subgoal_tac "tordered_set S")
 apply (frule_tac D = S and a = y and b = a in tordering_not, assumption+)
 apply (subgoal_tac "a \<le>\<^sub>S y") prefer 2 apply (simp add:ord_neq_def)
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (frule_tac a = b and b = a and c = y in ordering_axiom3 [of "S"], assumption+)
 apply (rule ordering_axiom2 [of "S"], assumption+)
 apply (simp add:well_ordered_set_def)
 apply (subgoal_tac "b \<in> carrier S")
apply (frule_tac S = S and a = b and ?a1.0 = "Pre (Iod S (segment S a)) b" in  UniquePre, assumption+)
prefer 3 apply (simp add:segment_def)
prefer 2 apply simp 
 apply (frule_tac S = S and a = a in segment_well_ordered_set, assumption+)
 apply (subgoal_tac "b \<in> carrier (Iod S (segment S a))")
 apply (frule_tac S = "Iod S (segment S a)" and a = b in Pre_element, assumption+)
 apply (erule conjE)+
apply (rule conjI)
 apply (simp add:Iod_def segment_def)
apply (rule conjI)
 apply (simp add:Iod_def segment_def ord_neq_def) 
prefer 2
 apply (simp add:Iod_def)
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>z\<in>carrier S. Pre (Iod S (segment S a)) b <\<^sub>S z \<and>  z <\<^sub>S b
 \<longrightarrow> False") apply blast
  apply (thin_tac "\<exists>y\<in>carrier S.  Pre (Iod S (segment S a)) b <\<^sub>S y \<and>  y <\<^sub>S b")
  apply (rule ballI)
  apply (rule impI)
 apply (case_tac "z \<in> carrier (Iod S (segment S a))")
  apply (subgoal_tac "Pre (Iod S (segment S a)) b <\<^sub>(Iod S (segment S a)) z \<longrightarrow>
              \<not>  z <\<^sub>(Iod S (segment S a)) b") prefer 2 apply simp
  apply (thin_tac "\<forall>y\<in>carrier (Iod S (segment S a)).  Pre (Iod S (segment S a)) b <\<^sub>(Iod S (segment S a)) y \<longrightarrow>  \<not>  y <\<^sub>(Iod S (segment S a)) b")
  apply (subgoal_tac " Pre (Iod S (segment S a)) b <\<^sub>(Iod S (segment S a)) z")
  apply simp
  apply (subgoal_tac "\<not> z <\<^sub>S b") apply (erule conjE)+ apply simp
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
  apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
(**----- b <\<^sub>S z ----- **)
 apply (thin_tac "\<forall>y\<in>carrier (Iod S (segment S a)). Pre (Iod S (segment S a)) b <\<^sub>(Iod S (segment S a)) y \<longrightarrow> \<not>  y <\<^sub>(Iod S (segment S a)) b")
 apply (thin_tac "ExPre (Iod S (segment S a)) b")
 apply (thin_tac "Pre (Iod S (segment S a)) b \<in> carrier (Iod S (segment S a))")
 apply (thin_tac " well_ordered_set (Iod S (segment S a))")
 apply (thin_tac "Pre (Iod S (segment S a)) b <\<^sub>S z")
 apply (thin_tac "Pre (Iod S (segment S a)) b <\<^sub>(Iod S (segment S a)) b")
 apply (thin_tac "b \<in> carrier (Iod S (segment S a))")
apply (simp add:Iod_def segment_def ord_neq_def)
 apply (erule conjE)+
 apply (case_tac "z \<le>\<^sub>S a") apply simp
 apply (frule well_ordered_set_is_ordered_set [of "S"])
 apply (frule_tac a = a and b = b in ordering_axiom2 [of "S"], assumption+)
 apply simp
 apply (frule well_ordered_set_is_ordered_set [of "S"]) 
 apply (frule_tac a = z and b = b and c = a in ordering_axiom3[of "S"], assumption+)
apply simp
done

lemma Pre2segment:"\<lbrakk>well_ordered_set S; a \<in> carrier S; b \<in> carrier S; b <\<^sub>S a; ExPre S b\<rbrakk> \<Longrightarrow> ExPre (Iod S (segment S a)) b"
apply (simp add:ExPre_def)
 apply (simp add:Iod_def segment_def ord_neq_def)
 apply auto
 apply (frule_tac S = S in well_ordered_set_is_ordered_set)
 apply (frule_tac a = x and b = b and c = a in ordering_axiom3, assumption+)
 apply (subgoal_tac "x \<noteq> a")
 apply (subgoal_tac "\<forall>y.  y \<le>\<^sub>S a \<and> y \<noteq> a \<and> y \<in> carrier S \<longrightarrow>
                     x \<le>\<^sub>S y \<and> x \<noteq> y \<longrightarrow>  y \<le>\<^sub>S b \<longrightarrow> y = b")
 apply blast
 apply (rule allI) apply (rule impI) apply (rule impI) apply (rule impI)
 apply (erule conjE)+ apply blast
  apply (thin_tac "\<forall>y\<in>carrier S.  x \<le>\<^sub>S y \<and> x \<noteq> y \<longrightarrow>  y \<le>\<^sub>S b \<longrightarrow> y = b")
 apply (rule contrapos_pp, simp+) 
 apply (frule_tac b = a and a = b in ordering_axiom2, assumption+)
 apply simp
done

lemma ord_isom_Pre1:"\<lbrakk>well_ordered_set S; well_ordered_set T; a \<in> carrier S; ExPre S a; ord_isom S T f\<rbrakk> \<Longrightarrow> ExPre T (f a)"
apply (simp add:ExPre_def) 
apply (subgoal_tac "\<forall>z. (z \<in> carrier S \<and>  z <\<^sub>S a \<and> (\<forall>y\<in>carrier S.  z <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S a)) \<longrightarrow> (\<exists>x. x \<in> carrier T \<and> x <\<^sub>T (f a) \<and> (\<forall>y\<in>carrier T.  x <\<^sub>T y \<longrightarrow> \<not>  y <\<^sub>T (f a)))")
 apply blast
 apply (thin_tac "\<exists>x. x \<in> carrier S \<and>  x <\<^sub>S a \<and> (\<forall>y\<in>carrier S.  x <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S a)")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "(f z) \<in> carrier T \<and> (f z) <\<^sub>T (f a) \<and> (\<forall>y\<in>carrier T.  (f z) <\<^sub>T y \<longrightarrow> \<not>  y <\<^sub>T (f a))")
 apply blast
apply (rule conjI)  
 apply (frule_tac S = S in well_ordered_set_is_ordered_set)
 apply (frule_tac S = T in well_ordered_set_is_ordered_set)
 apply (simp add:ord_isom_mem)
apply (frule_tac S = S in well_ordered_set_is_ordered_set)
 apply (frule_tac S = T in well_ordered_set_is_ordered_set)
 apply (rule conjI)
 apply (simp add:ord_isom1_1)
apply (rule ballI) apply (rule impI) 
 apply (frule_tac D = S and E = T and f = f and b = y in ord_isom_surj, assumption+) 
 apply (subgoal_tac "\<forall>u\<in>carrier S. y = f u \<longrightarrow>  \<not>  y <\<^sub>T (f a)")
 apply blast apply (thin_tac "\<exists>a\<in>carrier S. y = f a")
 apply (rule ballI) apply (rule impI)
 apply simp
 apply (subgoal_tac "\<not>  u <\<^sub>S a")
prefer 2 
 apply (frule_tac a = z and b = u in ord_isom2_1 [of "S" "T" "f"], assumption+)
 apply simp
apply (thin_tac "\<forall>y\<in>carrier S.  z <\<^sub>S y \<longrightarrow> \<not>  y <\<^sub>S a") 
 apply (rule contrapos_pp, simp+)
 apply (frule_tac a = u and b = a in ord_isom2_1 [of "S" "T" "f"], assumption+)
apply simp
done

lemma ord_isom_Pre2:"\<lbrakk>well_ordered_set S; well_ordered_set T; a \<in> carrier S; ExPre S a; ord_isom S T f\<rbrakk> \<Longrightarrow> f (Pre S a) = Pre T (f a)" 
apply (frule_tac S = S and T = T and a = a and f = f in ord_isom_Pre1, assumption+)
 apply (frule_tac S = S and a = a in Pre_element, assumption+)
 apply (frule_tac S = T and a = "f a" in Pre_element)
 apply (frule_tac S = S in well_ordered_set_is_ordered_set)
 apply (frule_tac S = T in well_ordered_set_is_ordered_set)
 apply (rule ord_isom_mem [of "S" "T" "f"], assumption+)
 apply (rule_tac S1 = T and a1 = "f a" and t = "f (Pre S a)" in UniquePre [THEN sym], assumption+)
 apply (frule_tac S = S in well_ordered_set_is_ordered_set)
 apply (frule_tac S = T in well_ordered_set_is_ordered_set)
 apply (simp add:ord_isom_mem) apply assumption
apply (erule conjE)+
 apply (frule_tac S = S in well_ordered_set_is_ordered_set)
 apply (frule_tac S = T in well_ordered_set_is_ordered_set) 
 apply (rule conjI)
 apply (simp add:ord_isom_mem)
apply (rule conjI)
 apply (simp add:ord_isom1_1)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>z\<in>carrier T. f (Pre S a) <\<^sub>T z \<and> z <\<^sub>T (f a) \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>y\<in>carrier T.  f (Pre S a) <\<^sub>T y \<and>  y <\<^sub>T (f a)")
 apply (rule ballI)
 apply (rule impI)
 apply (erule conjE)
 apply (frule_tac b = z in ord_isom_surj [of "S" "T" "f"], assumption+)
 apply (subgoal_tac "\<forall>d\<in>carrier S. z = f d \<longrightarrow> False") 
 apply blast apply (thin_tac "\<exists>a\<in>carrier S. z = f a")
apply (rule ballI) apply (rule impI) apply simp
 apply (frule_tac a = "Pre S a" and b = d in ord_isom2_1 [of "S" "T" "f"], assumption+)
 apply (frule_tac a = d and b = a in ord_isom2_1 [of "S" "T" "f"], assumption+)
 apply (subgoal_tac "\<not> d <\<^sub>S a") apply blast
apply simp
done

section "3. transfinite induction"

lemma transfinite_induction:"\<lbrakk>well_ordered_set S; minimum_elem S (carrier S) s0; P s0; \<forall>t\<in>carrier S. ((\<forall>u\<in> segment S t. P u) \<longrightarrow> P t)\<rbrakk> \<Longrightarrow> \<forall>x\<in>carrier S. P x" 
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "{y. y \<in> carrier S \<and> \<not> P y} \<noteq> {}")
 prefer 2 
 apply (subgoal_tac "\<forall>x\<in>carrier S. \<not> P x \<longrightarrow>  {y. y \<in> carrier S \<and> \<not> P y} \<noteq> {}") apply blast
 apply (thin_tac "\<exists>x\<in>carrier S. \<not> P x")
 apply (rule ballI) apply (rule impI) 
 apply (rule_tac x = x and A = "{y. y \<in> carrier S \<and> \<not> P y}" in nonempty)
 apply simp
apply (subgoal_tac "\<exists>y0. minimum_elem S {y. y \<in> carrier S \<and> \<not> P y} y0")
apply (subgoal_tac "\<forall>y0. minimum_elem S {y. y \<in> carrier S \<and> \<not> P y} y0 \<longrightarrow>
                    False")
 apply blast apply (thin_tac " \<exists>y0. minimum_elem S {y. y \<in> carrier S \<and> \<not> P y} y0")
 apply (rule allI) apply (rule impI)
prefer 2 apply (subgoal_tac "{y. y \<in> carrier S \<and> \<not> P y} \<subseteq> carrier S")
 apply (simp add:well_ordered_set_def)
 apply (rule subsetI) apply simp
 apply (thin_tac "\<exists>x\<in>carrier S. \<not> P x")
 apply (thin_tac "{y. y \<in> carrier S \<and> \<not> P y} \<noteq> {}")
 apply (subgoal_tac "\<forall>x\<in>segment S y0. P x")
apply (subgoal_tac "y0 \<in> carrier S")
 apply (subgoal_tac "(\<forall>u\<in>segment S t. P u) \<longrightarrow> P y0") prefer 2 apply simp
 apply (subgoal_tac "P y0") prefer 2 apply simp
 apply (thin_tac "\<forall>t\<in>carrier S. (\<forall>u\<in>segment S t. P u) \<longrightarrow> P t") 
 apply (thin_tac "\<forall>x\<in>segment S y0. P x")
 apply (thin_tac "(\<forall>u\<in>segment S t. P u) \<longrightarrow> P y0")
 apply (simp add:minimum_elem_def)
 apply (simp add:minimum_elem_def)
apply (rule ballI)
 apply (thin_tac "\<forall>t\<in>carrier S. (\<forall>u\<in>segment S t. P u) \<longrightarrow> P t")
 apply (thin_tac "minimum_elem S (carrier S) s0")
 apply (simp add:minimum_elem_def) apply (erule conjE)+
 apply (simp add:segment_def) apply (erule conjE)
 apply (subgoal_tac "\<not> y0 \<le>\<^sub>S x") apply blast
apply (thin_tac "\<forall>x. x \<in> carrier S \<and> \<not> P x \<longrightarrow>  y0 \<le>\<^sub>S x")
apply (simp add:well_ordered_set_def) apply (erule conjE)
 apply (thin_tac "\<forall>X. X \<subseteq> carrier S \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem S X x)")
 apply (simp add:tordering_not1)
done

end
