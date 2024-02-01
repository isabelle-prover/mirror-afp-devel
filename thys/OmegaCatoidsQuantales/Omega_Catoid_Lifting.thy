(* 
Title: Lifting Omega-Catoids to Powerset Omega-Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Lifting $\omega$-catoids to powerset $\omega$-quantales\<close>

theory Omega_Catoid_Lifting
  imports Omega_Catoid Omega_Quantale

begin

instantiation set :: (local_omega_catoid) omega_quantale

begin

definition do_set :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set" where
 "do i X = Srci i X"

definition cd_set :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "cd i X = Tgti i X"

definition icomp_set :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X \<cdot>\<^bsub>i\<^esub> Y = X \<star>\<^bsub>i\<^esub> Y" 

definition un_set :: "nat \<Rightarrow> 'a set" where 
  "un i = srcfix i"

instance
  apply intro_classes
  unfolding icomp_set_def do_set_def cd_set_def un_set_def iconv_prop
                      apply (simp add: ims.conv_assoc)
  using stimm.stopp.stopp.conv_uns apply blast
                    apply (metis stimm.stopp.stopp.conv_unt stimm.stopp.stopp.st_fix_set)
                   apply (simp add: ims.conv_distl)
                  apply (simp add: multimagma.conv_distr)
                 apply force+
     apply (metis iconv_prop interchange_lift)
    apply (metis iconv_prop omega_st_multimagma_class.Srcj_hom)
   apply (metis iconv_prop omega_st_multimagma_class.Tgtj_hom)
  by (simp add: olropp.TjTi)

end

end










 







 







