(* 
Title: Lifting 2-Catoids to Powerset 2-Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Lifting 2-Catoids to powerset 2-quantales\<close>

theory Two_Catoid_Lifting
  imports Two_Catoid Two_Quantale Catoids.Catoid_Lifting 

begin

instantiation set :: (local_two_catoid) two_quantale

begin

definition dom\<^sub>0_set :: "'a set \<Rightarrow> 'a set" where
 "dom\<^sub>0 X = Src\<^sub>0 X"

definition cod\<^sub>0_set :: "'a set \<Rightarrow> 'a set" where
  "cod\<^sub>0 X = Tgt\<^sub>0 X"

definition comp0_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X \<cdot>\<^sub>0 Y = X *\<^sub>0 Y" 

definition id0_set :: "'a set"
  where "1\<^sub>0 = s0fix"

definition dom\<^sub>1_set :: "'a set \<Rightarrow> 'a set" where
  "dom\<^sub>1 X = Src\<^sub>1 X"

definition cod\<^sub>1_set :: "'a set \<Rightarrow> 'a set" where
  "cod\<^sub>1 X = Tgt\<^sub>1 X"

definition comp1_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X \<cdot>\<^sub>1 Y = X *\<^sub>1 Y" 

definition id1_set :: "'a set" where
  "1\<^sub>1 = t1fix"

instance
  apply intro_classes
  unfolding comp0_set_def dom\<^sub>0_set_def cod\<^sub>0_set_def id0_set_def comp1_set_def dom\<^sub>1_set_def cod\<^sub>1_set_def id1_set_def
                      apply (simp add: msg0.conv_assoc)
  using stmm0.stopp.stopp.conv_uns apply blast
                      apply (metis stmm0.stopp.stopp.conv_unt stmm0.stopp.stopp.st_fix_set)
                      apply (smt (verit, ccfv_SIG) Collect_cong image_def stmm0.stopp.conv_distr)
                      apply (smt (z3) Collect_cong image_def multimagma.conv_distr)
                      apply simp+
                      apply (simp add: image_Un)
  using stmm0.stopp.stopp.Tgt_subid stmm0.stopp.stopp.st_fix_set apply blast
                      apply force
                      apply simp+
                      apply (simp add: image_Un)
  using stmm0.stopp.stopp.Src_subid apply blast
                      apply force
                      apply simp+
                      apply (simp add: msg1.conv_assoc)
                      apply (metis stmm1.stopp.stopp.conv_uns stmm1.stopp.stopp.st_fix_set)
  using stmm1.stopp.stopp.conv_unt apply blast
                     apply (smt (verit, best) Collect_cong image_def multimagma.conv_distl)
                    apply (smt (verit) Collect_cong image_def multimagma.conv_distr)
                   apply simp+
                 apply (simp add: image_Un)
  using stmm1.stopp.stopp.Tgt_subid apply blast
               apply simp+
            apply (simp add: image_Un)
           apply force
          apply simp+
       apply (simp add: interchange_lifting)
      apply (simp add: Src1_hom)
     apply (simp add: Tgt1_hom)
  using Src0_hom apply blast
   apply (simp add: Tgt0_hom)
  by simp

end

end










 







 







