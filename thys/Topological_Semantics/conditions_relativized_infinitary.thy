theory conditions_relativized_infinitary
  imports conditions_relativized conditions_negative_infinitary
begin   

subsection \<open>Infinitary Relativized Conditions\<close>

text\<open>We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.\<close>

definition iADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDIr")
  where "iADDIr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<^bold>=\<^sup>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)"
definition iADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDIr\<^sup>a")
  where "iADDIr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<^bold>\<le>\<^sup>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" 
definition iADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDIr\<^sup>b")
  where "iADDIr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le>\<^sup>U \<phi>(\<^bold>\<Or>S))" 

definition inADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inADDIr")
  where "inADDIr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<^bold>=\<^sup>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)"
definition inADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inADDIr\<^sup>a")
  where "inADDIr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le>\<^sup>U \<phi>(\<^bold>\<Or>S))"  
definition inADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inADDIr\<^sup>b")
  where "inADDIr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<^bold>\<le>\<^sup>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)" 

declare iADDIr_def[cond] iADDIr_a_def[cond] iADDIr_b_def[cond]
        inADDIr_def[cond] inADDIr_a_def[cond] inADDIr_b_def[cond]

definition iMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULTr")
  where "iMULTr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<^bold>=\<^sub>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)"
definition iMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULTr\<^sup>a")
  where "iMULTr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<^bold>\<le>\<^sub>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)"
definition iMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULTr\<^sup>b")
  where "iMULTr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le>\<^sub>U \<phi>(\<^bold>\<And>S))"

definition inMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inMULTr")
  where "inMULTr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<^bold>=\<^sub>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)"
definition inMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inMULTr\<^sup>a")
  where "inMULTr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<^bold>\<le>\<^sub>U \<phi>(\<^bold>\<And>S))"
definition inMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inMULTr\<^sup>b")
  where "inMULTr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<^bold>\<le>\<^sub>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)"

declare iMULTr_def[cond] iMULTr_a_def[cond] iMULTr_b_def[cond]
        inMULTr_def[cond] inMULTr_a_def[cond] inMULTr_b_def[cond]

lemma iADDIr_char: "iADDIr \<phi> = (iADDIr\<^sup>a \<phi> \<and> iADDIr\<^sup>b \<phi>)" unfolding cond setequ_char setequ_out_char subset_out_char by (meson setequ_char)
lemma iMULTr_char: "iMULTr \<phi> = (iMULTr\<^sup>a \<phi> \<and> iMULTr\<^sup>b \<phi>)" unfolding cond setequ_char setequ_in_char subset_in_char by (meson setequ_char)

lemma inADDIr_char: "inADDIr \<phi> = (inADDIr\<^sup>a \<phi> \<and> inADDIr\<^sup>b \<phi>)" unfolding cond setequ_char setequ_out_char subset_out_char by (meson setequ_char)
lemma inMULTr_char: "inMULTr \<phi> = (inMULTr\<^sup>a \<phi> \<and> inMULTr\<^sup>b \<phi>)" unfolding cond setequ_char setequ_in_char subset_in_char by (meson setequ_char)


text\<open>Dual interrelations.\<close>
lemma iADDIr_dual1: "iADDIr\<^sup>a \<phi> = iMULTr\<^sup>b \<phi>\<^sup>d" unfolding cond by (smt (z3) BA_cmpl_equ BA_cp BA_deMorgan2 dual_invol iDM_a iDM_b im_prop1 op_dual_def setequ_ext subset_in_char subset_out_char)
lemma iADDIr_dual2: "iADDIr\<^sup>b \<phi> = iMULTr\<^sup>a \<phi>\<^sup>d" unfolding cond by (smt (z3) BA_cmpl_equ BA_cp BA_deMorgan2 dual_invol iDM_a iDM_b im_prop1 op_dual_def setequ_ext subset_in_char subset_out_char)
lemma iADDIr_dual:  "iADDIr \<phi> = iMULTr \<phi>\<^sup>d" using iADDIr_char iADDIr_dual1 iADDIr_dual2 iMULTr_char by blast

lemma inADDIr_dual1: "inADDIr\<^sup>a \<phi> = inMULTr\<^sup>b \<phi>\<^sup>d" unfolding cond by (smt (z3) BA_cmpl_equ compl_def dual_invol iDM_a iDM_b im_prop3 op_dual_def setequ_ext subset_in_def subset_in_out)
lemma inADDIr_dual2: "inADDIr\<^sup>b \<phi> = inMULTr\<^sup>a \<phi>\<^sup>d" unfolding cond by (smt (z3) BA_cmpl_equ compl_def dual_invol iDM_a iDM_b im_prop3 op_dual_def setequ_ext subset_in_def subset_in_out)
lemma inADDIr_dual:  "inADDIr \<phi> = inMULTr \<phi>\<^sup>d" using inADDIr_char inADDIr_dual1 inADDIr_dual2 inMULTr_char by blast

text\<open>Complement interrelations.\<close>
lemma iADDIr_a_cmpl: "iADDIr\<^sup>a \<phi> = inADDIr\<^sup>a \<phi>\<^sup>-" unfolding cond by (smt (z3) compl_def dualcompl_invol iDM_b im_prop2 setequ_ext subset_out_def svfun_compl_def)
lemma iADDIr_b_cmpl: "iADDIr\<^sup>b \<phi> = inADDIr\<^sup>b \<phi>\<^sup>-" unfolding cond by (smt (z3) compl_def iDM_b im_prop2 setequ_ext sfun_compl_invol subset_out_def svfun_compl_def)
lemma iADDIr_cmpl: "iADDIr \<phi> = inADDIr \<phi>\<^sup>-" by (simp add: iADDIr_a_cmpl iADDIr_b_cmpl iADDIr_char inADDIr_char)

lemma iMULTr_a_cmpl: "iMULTr\<^sup>a \<phi> = inMULTr\<^sup>a \<phi>\<^sup>-" unfolding cond by (smt (z3) compl_def iDM_b im_prop2 setequ_ext subset_in_def svfun_compl_def)
lemma iMULTr_b_cmpl: "iMULTr\<^sup>b \<phi> = inMULTr\<^sup>b \<phi>\<^sup>-" unfolding cond by (smt (z3) compl_def dualcompl_invol iDM_a im_prop2 setequ_ext subset_in_def svfun_compl_def)
lemma iMULTr_cmpl: "MULTr \<phi> = nMULTr \<phi>\<^sup>-" by (simp add: MULTr_a_cmpl MULTr_b_cmpl MULTr_char nMULTr_char)

text\<open>Fixed-point interrelations.\<close>
lemma iADDIr_a_fpc: "iADDIr\<^sup>a \<phi> = iADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>-" unfolding cond subset_out_def image_def ofp_fixpoint_compl_def supremum_def sdiff_def by (smt (verit))
lemma iADDIr_a_fp: "iADDIr\<^sup>a \<phi> = inADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p" by (metis iADDIr_a_cmpl iADDIr_a_fpc sfun_compl_invol)
lemma iADDIr_b_fpc: "iADDIr\<^sup>b \<phi> = iADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>-" unfolding cond subset_out_def image_def ofp_fixpoint_compl_def supremum_def sdiff_def by (smt (verit))
lemma iADDIr_b_fp: "iADDIr\<^sup>b \<phi> = inADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p" by (metis iADDIr_b_cmpl iADDIr_b_fpc sfun_compl_invol)

lemma iMULTr_a_fp: "iMULTr\<^sup>a \<phi> = iMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_def image_def by (smt (z3) dimpl_def infimum_def ofp_invol op_fixpoint_def)
lemma iMULTr_a_fpc: "iMULTr\<^sup>a \<phi> = inMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>-" using iMULTr_a_cmpl iMULTr_a_fp by blast
lemma iMULTr_b_fp: "iMULTr\<^sup>b \<phi> = iMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_def image_def dimpl_def infimum_def op_fixpoint_def by (smt (verit))
lemma iMULTr_b_fpc: "iMULTr\<^sup>b \<phi> = inMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>-" using iMULTr_b_cmpl iMULTr_b_fp by blast

end
