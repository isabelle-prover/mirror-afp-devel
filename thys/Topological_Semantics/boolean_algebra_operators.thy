theory boolean_algebra_operators
  imports boolean_algebra
begin

subsection \<open>Operations on set-valued functions\<close>

text\<open>Functions with sets in their codomain will be called here 'set-valued functions'.
  We conveniently define some (2nd-order) Boolean operations on them.\<close>

text\<open>The 'meet' and 'join' of two set-valued functions.\<close>
definition svfun_meet::"('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>)" (infixr "\<^bold>\<and>\<^sup>:" 62) 
  where "\<phi> \<^bold>\<and>\<^sup>: \<psi> \<equiv> \<lambda>x. (\<phi> x) \<^bold>\<and> (\<psi> x)"
definition svfun_join::"('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>)" (infixr "\<^bold>\<or>\<^sup>:" 61) 
  where "\<phi> \<^bold>\<or>\<^sup>: \<psi> \<equiv> \<lambda>x. (\<phi> x) \<^bold>\<or> (\<psi> x)"
text\<open>Analogously, we can define an 'implication' and a 'complement'.\<close>
definition svfun_impl::"('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>)" (infixr "\<^bold>\<rightarrow>\<^sup>:" 61) 
  where "\<psi> \<^bold>\<rightarrow>\<^sup>: \<phi> \<equiv> \<lambda>x. (\<psi> x) \<^bold>\<rightarrow> (\<phi> x)"
definition svfun_compl::"('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>-)") 
  where "\<phi>\<^sup>- \<equiv> \<lambda>x. \<^bold>\<midarrow>(\<phi> x)"
text\<open>There are two natural 0-ary connectives (aka. constants). \<close>
definition svfun_top::"'a \<Rightarrow> 'w \<sigma>" ("\<^bold>\<top>\<^sup>:") 
  where "\<^bold>\<top>\<^sup>: \<equiv> \<lambda>x. \<^bold>\<top>"
definition svfun_bot::"'a \<Rightarrow> 'w \<sigma>" ("\<^bold>\<bottom>\<^sup>:") 
  where "\<^bold>\<bottom>\<^sup>: \<equiv> \<lambda>x. \<^bold>\<bottom>"

named_theorems conn2 (*to group together definitions for 2nd-order algebraic connectives*)
declare svfun_meet_def[conn2] svfun_join_def[conn2] svfun_impl_def[conn2]
        svfun_compl_def[conn2] svfun_top_def[conn2] svfun_bot_def[conn2]

text\<open>And, of course, set-valued functions are naturally ordered in the expected way:\<close>
definition svfun_sub::"('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" (infixr "\<^bold>\<le>\<^sup>:" 55) 
  where "\<psi> \<^bold>\<le>\<^sup>: \<phi> \<equiv> \<forall>x. (\<psi> x) \<^bold>\<le> (\<phi> x)"
definition svfun_equ::"('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('a \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" (infixr "\<^bold>=\<^sup>:" 55) 
  where "\<psi> \<^bold>=\<^sup>: \<phi> \<equiv> \<forall>x. (\<psi> x) \<^bold>= (\<phi> x)"

named_theorems order2 (*to group together definitions for 2nd-order algebraic connectives*)
declare svfun_sub_def[order2] svfun_equ_def[order2]

text\<open>These (trivial) lemmas are intended to help automated tools.\<close>
lemma svfun_sub_char: "(\<psi> \<^bold>\<le>\<^sup>: \<phi>) = (\<psi> \<^bold>\<rightarrow>\<^sup>: \<phi> \<^bold>=\<^sup>: \<^bold>\<top>\<^sup>:)" by (simp add: BA_impl svfun_equ_def svfun_impl_def svfun_sub_def svfun_top_def)
lemma svfun_equ_char: "(\<psi> \<^bold>=\<^sup>: \<phi>) = (\<psi> \<^bold>\<le>\<^sup>: \<phi> \<and> \<phi> \<^bold>\<le>\<^sup>: \<psi>)" unfolding order2 setequ_char by blast
lemma svfun_equ_ext: "(\<psi> \<^bold>=\<^sup>: \<phi>) = (\<psi> = \<phi>)" by (meson ext setequ_ext svfun_equ_def)

text\<open>Clearly, set-valued functions form a Boolean algebra. We can prove some interesting relationships:\<close>
lemma svfun_compl_char: "\<phi>\<^sup>- = (\<phi> \<^bold>\<rightarrow>\<^sup>: \<^bold>\<bottom>\<^sup>:)" unfolding conn conn2 by simp
lemma svfun_impl_char1: "(\<psi> \<^bold>\<rightarrow>\<^sup>: \<phi>) = (\<psi>\<^sup>- \<^bold>\<or>\<^sup>: \<phi>)" unfolding conn conn2 by simp
lemma svfun_impl_char2: "(\<psi> \<^bold>\<rightarrow>\<^sup>: \<phi>) = (\<psi> \<^bold>\<and>\<^sup>: (\<phi>\<^sup>-))\<^sup>-" unfolding conn conn2 by simp
lemma svfun_deMorgan1: "(\<psi> \<^bold>\<and>\<^sup>: \<phi>)\<^sup>- = (\<psi>\<^sup>-) \<^bold>\<or>\<^sup>: (\<phi>\<^sup>-)" unfolding conn conn2 by simp
lemma svfun_deMorgan2: "(\<psi> \<^bold>\<or>\<^sup>: \<phi>)\<^sup>- = (\<psi>\<^sup>-) \<^bold>\<and>\<^sup>: (\<phi>\<^sup>-)" unfolding conn conn2 by simp


subsection \<open>Operators and their transformations\<close>

text\<open>Dual to set-valued functions we can have set-domain functions. For them we can define the 'dual-complement'.\<close>
definition sdfun_dcompl::"('w \<sigma> \<Rightarrow> 'a) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'a)" ("(_\<^sup>d\<^sup>-)") 
  where "\<phi>\<^sup>d\<^sup>- \<equiv> \<lambda>X. \<phi>(\<^bold>\<midarrow>X)"
lemma sdfun_dcompl_char: "\<phi>\<^sup>d\<^sup>- = (\<lambda>X. \<exists>Y. (\<phi> Y) \<and> (X = \<^bold>\<midarrow>Y))" by (metis BA_dn setequ_ext sdfun_dcompl_def)

text\<open>Operators are a particularly important kind of functions. They are both set-valued and set-domain.
Thus our algebra of operators inherits the connectives defined above plus the ones below. \<close>

text\<open>We conveniently define the 'dual' of an operator.\<close>
definition op_dual::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"

text\<open>The following two 0-ary connectives (i.e. operator 'constants') exist already (but somehow implicitly).
  We just make them explicit by introducing some convenient notation.\<close>
definition id_op::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>e") 
  where "\<^bold>e \<equiv> \<lambda>X. X" (*introduces notation to refer to 'identity' operator*)
definition compl_op::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>n") 
  where "\<^bold>n \<equiv> \<lambda>X. \<^bold>\<midarrow>X" (*to refer to 'complement' operator*)

declare sdfun_dcompl_def[conn2] op_dual_def[conn2] id_op_def[conn2] compl_op_def[conn2]

text\<open>We now prove some lemmas (some of them might help provers in their hard work).\<close>
lemma dual_compl_char1: "\<phi>\<^sup>d\<^sup>- = (\<phi>\<^sup>d)\<^sup>-" unfolding conn2 conn order by simp
lemma dual_compl_char2: "\<phi>\<^sup>d\<^sup>- = (\<phi>\<^sup>-)\<^sup>d" unfolding conn2 conn order by simp
lemma sfun_compl_invol: "\<phi>\<^sup>-\<^sup>- = \<phi>" unfolding conn2 conn order by simp
lemma dual_invol: "\<phi>\<^sup>d\<^sup>d = \<phi>" unfolding conn2 conn order by simp
lemma dualcompl_invol: "(\<phi>\<^sup>d\<^sup>-)\<^sup>d\<^sup>- = \<phi>" unfolding conn2 conn order by simp

lemma op_prop1: "\<^bold>e\<^sup>d = \<^bold>e" unfolding conn2 conn by simp
lemma op_prop2: "\<^bold>n\<^sup>d = \<^bold>n" unfolding conn2 conn by simp
lemma op_prop3: "\<^bold>e\<^sup>- = \<^bold>n" unfolding conn2 conn by simp
lemma op_prop4: "(\<phi> \<^bold>\<or>\<^sup>: \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<^bold>\<and>\<^sup>: (\<psi>\<^sup>d)" unfolding conn2 conn by simp
lemma op_prop5: "(\<phi> \<^bold>\<or>\<^sup>: \<psi>)\<^sup>- = (\<phi>\<^sup>-) \<^bold>\<and>\<^sup>: (\<psi>\<^sup>-)" unfolding conn2 conn by simp
lemma op_prop6: "(\<phi> \<^bold>\<and>\<^sup>: \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<^bold>\<or>\<^sup>: (\<psi>\<^sup>d)" unfolding conn2 conn by simp
lemma op_prop7: "(\<phi> \<^bold>\<and>\<^sup>: \<psi>)\<^sup>- = (\<phi>\<^sup>-) \<^bold>\<or>\<^sup>: (\<psi>\<^sup>-)" unfolding conn2 conn by simp
lemma op_prop8: "\<^bold>\<top>\<^sup>: = \<^bold>n \<^bold>\<or>\<^sup>: \<^bold>e" unfolding conn2 conn by simp
lemma op_prop9: "\<^bold>\<bottom>\<^sup>: = \<^bold>n \<^bold>\<and>\<^sup>: \<^bold>e" unfolding conn2 conn by simp

text\<open>The notion of a fixed-point is fundamental. We speak of sets being fixed-points of operators.
We define a function that given an operator returns the set of all its fixed-points.\<close>
definition fixpoints::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma>)\<sigma>" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. (\<phi> X) \<^bold>= X"
text\<open>We can in fact 'operationalize' the function above, thus obtaining a 'fixed-point operation'.\<close>
definition op_fixpoint::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>f\<^sup>p)")
  where "\<phi>\<^sup>f\<^sup>p \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

declare fixpoints_def[conn2] op_fixpoint_def[conn2]

text\<open>Interestingly, the fixed-point operation (or transformation) is definable in terms of the others.\<close>
lemma op_fixpoint_char: "\<phi>\<^sup>f\<^sup>p = (\<phi> \<^bold>\<and>\<^sup>: \<^bold>e) \<^bold>\<or>\<^sup>: (\<phi>\<^sup>- \<^bold>\<and>\<^sup>: \<^bold>n)" unfolding conn2 order conn by blast

text\<open>Given an operator @{text "\<phi>"} the fixed-points of it's dual is the set of complements of @{text "\<phi>'s"} fixed-points.\<close>
lemma fp_dual: "fp \<phi>\<^sup>d = (fp \<phi>)\<^sup>d\<^sup>-" unfolding order conn conn2 by blast
text\<open>The fixed-points of @{text "\<phi>'s"} complement is the set of complements of the fixed-points of @{text "\<phi>'s"} dual-complement.\<close>
lemma fp_compl: "fp \<phi>\<^sup>- = (fp (\<phi>\<^sup>d\<^sup>-))\<^sup>d\<^sup>-" by (simp add: dual_compl_char2 dualcompl_invol fp_dual)
text\<open>The fixed-points of @{text "\<phi>'s"} dual-complement is the set of complements of the fixed-points of @{text "\<phi>'s"} complement.\<close>
lemma fp_dcompl: "fp (\<phi>\<^sup>d\<^sup>-) = (fp \<phi>\<^sup>-)\<^sup>d\<^sup>-" by (simp add: dualcompl_invol fp_compl)

text\<open>The fixed-points function and the fixed-point operation are essentially related.\<close>
lemma fp_rel: "fp \<phi> A \<longleftrightarrow> (\<phi>\<^sup>f\<^sup>p A) \<^bold>= \<^bold>\<top>" unfolding conn2 order conn by simp
lemma fp_d_rel:  "fp \<phi>\<^sup>d A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>= \<^bold>\<top>" unfolding conn2 order conn by blast
lemma fp_c_rel: "fp \<phi>\<^sup>- A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p A \<^bold>= \<^bold>\<bottom>" unfolding conn2 order conn by blast
lemma fp_dc_rel: "fp (\<phi>\<^sup>d\<^sup>-) A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>= \<^bold>\<bottom>" unfolding conn2 order conn by simp

text\<open>The fixed-point operation is involutive.\<close>
lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p = \<phi>" unfolding conn2 order conn by blast
text\<open>And commutes the dual with the dual-complement operations.\<close>
lemma ofp_comm_dc1: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>d\<^sup>-" unfolding conn2 order conn by blast
lemma ofp_comm_dc2:"(\<phi>\<^sup>d\<^sup>-)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>d" unfolding conn2 order conn by simp

text\<open>The fixed-point operation commutes with the complement.\<close>
lemma ofp_comm_compl: "(\<phi>\<^sup>-)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>-" unfolding conn2 order conn by blast
text\<open>The above motivates the following alternative definition for a 'complemented-fixed-point' operation.\<close>
lemma ofp_fixpoint_compl_def: "\<phi>\<^sup>f\<^sup>p\<^sup>- = (\<lambda>X. (\<phi> X) \<^bold>\<triangle> X)" unfolding conn2 conn by simp
text\<open>Analogously, the 'complemented fixed-point' operation is also definable in terms of the others.\<close>
lemma op_fixpoint_compl_char: "\<phi>\<^sup>f\<^sup>p\<^sup>- = (\<phi> \<^bold>\<or>\<^sup>: \<^bold>e) \<^bold>\<and>\<^sup>: (\<phi>\<^sup>- \<^bold>\<or>\<^sup>: \<^bold>n)" unfolding conn2 conn by blast

text\<open>In fact, function composition can be seen as an additional binary connective for operators.
  We show below some interesting relationships that hold. \<close>
lemma op_prop10: "\<phi> = (\<^bold>e \<circ> \<phi>)" unfolding conn2 fun_comp_def by simp
lemma op_prop11: "\<phi> = (\<phi> \<circ> \<^bold>e)" unfolding conn2 fun_comp_def by simp
lemma op_prop12: "\<^bold>e = (\<^bold>n \<circ> \<^bold>n)" unfolding conn2 conn fun_comp_def by simp
lemma op_prop13: "\<phi>\<^sup>- = (\<^bold>n \<circ> \<phi>)" unfolding conn2 fun_comp_def by simp
lemma op_prop14: "\<phi>\<^sup>d\<^sup>- = (\<phi> \<circ> \<^bold>n)" unfolding conn2 fun_comp_def by simp
lemma op_prop15: "\<phi>\<^sup>d = (\<^bold>n \<circ> \<phi> \<circ> \<^bold>n)" unfolding conn2 fun_comp_def by simp

text\<open>There are also some useful properties regarding the images of operators.\<close>
lemma im_prop1: "\<lbrakk>\<phi> D\<rbrakk>\<^sup>d\<^sup>-  = \<lbrakk>\<phi>\<^sup>d D\<^sup>d\<^sup>-\<rbrakk>" unfolding image_def op_dual_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop2: "\<lbrakk>\<phi>\<^sup>- D\<rbrakk>\<^sup>d\<^sup>- = \<lbrakk>\<phi> D\<rbrakk>" unfolding image_def svfun_compl_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop3: "\<lbrakk>\<phi>\<^sup>d D\<rbrakk>\<^sup>d\<^sup>- = \<lbrakk>\<phi> D\<^sup>d\<^sup>-\<rbrakk>" unfolding image_def op_dual_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop4: "\<lbrakk>\<phi>\<^sup>d\<^sup>- D\<rbrakk>\<^sup>d\<^sup>- = \<lbrakk>\<phi>\<^sup>d D\<rbrakk>" unfolding image_def op_dual_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop5: "\<lbrakk>\<phi>\<^sup>- D\<^sup>d\<^sup>-\<rbrakk>  = \<lbrakk>\<phi>\<^sup>d\<^sup>- D\<rbrakk>\<^sup>d\<^sup>-" unfolding image_def svfun_compl_def sdfun_dcompl_def by (metis (no_types, opaque_lifting) BA_dn setequ_ext)
lemma im_prop6: "\<lbrakk>\<phi>\<^sup>d\<^sup>- D\<^sup>d\<^sup>-\<rbrakk>  = \<lbrakk>\<phi> D\<rbrakk>" unfolding image_def sdfun_dcompl_def by (metis BA_dn setequ_ext)


text\<open>Observe that all results obtained by assuming fixed-point predicates extend to their associated operators.\<close>
lemma "\<phi>\<^sup>f\<^sup>p(A) \<^bold>\<and> \<Gamma>(A) \<^bold>\<le> \<Delta>(A) \<longrightarrow> (fp \<phi>)(A) \<longrightarrow> \<Gamma>(A) \<^bold>\<le> \<Delta>(A)"
  by (simp add: fp_rel meet_def setequ_ext subset_def top_def)
lemma "\<phi>\<^sup>f\<^sup>p(A) \<^bold>\<and> \<phi>\<^sup>f\<^sup>p(B) \<^bold>\<and> (\<Gamma> A B) \<^bold>\<le> (\<Delta> A B) \<longrightarrow> (fp \<phi>)(A) \<and> (fp \<phi>)(B) \<longrightarrow> (\<Gamma> A B) \<^bold>\<le> (\<Delta> A B)"
  by (simp add: fp_rel meet_def setequ_ext subset_def top_def)

end
