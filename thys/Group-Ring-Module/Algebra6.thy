(**        Algebra6
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            hikoba at math.cst.nihon-u.ac.jp
                            May 3, 2004.

   chapter 5. Modules
    section 3.   a module over two rings
    section 4.   eSum and Generators
     subsection 4-1. sum up coefficients
     subsection 4-2. free generators
   **)

theory Algebra6
imports Algebra5
begin


constdefs
 indmhom :: "[('b, 'm) RingType_scheme, ('a, 'b, 'm1) ModuleType_scheme,
   ('c, 'b, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'c] \<Rightarrow>  'a set \<Rightarrow> 'c"

 "indmhom R M N f == \<lambda>X\<in> (set_mr_cos M (ker\<^sub>M\<^sub>,\<^sub>N f)). f ( \<some> x. x \<in> X)"

syntax
 "@INDMHOM"::"['a \<Rightarrow> 'b, ('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, ('b, 'r, 'm2) ModuleType_scheme]  \<Rightarrow>  ('a set  \<Rightarrow> 'b )"
  ("(4_\<^sup>\<flat>\<^sub>_ \<^sub>_\<^sub>,\<^sub>_)" [92,92,92,93]92)

translations
    "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N" == "indmhom R M N f"


lemma indmhom_someTr:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
X \<in> set_mr_cos M (ker\<^sub>M\<^sub>,\<^sub>N f)\<rbrakk> \<Longrightarrow> f (SOME xa. xa \<in> X) \<in> f `(carrier M)"
apply (simp add:set_mr_cos_def)
apply auto
apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:asubgroup_def)
 apply (thin_tac "\<forall>a\<in>carrier R. \<forall>m\<in>ker\<^sub>M\<^sub>,\<^sub>N f.  a \<star>\<^sub>M m \<in> ker\<^sub>M\<^sub>,\<^sub>N f")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule b_ag_group)
apply (rule someI2_ex)
 apply (simp add:ar_coset_def)
apply (frule_tac a = a in aInR_cos [of "b_ag M" "ker\<^sub>M\<^sub>,\<^sub>N f"], assumption+)
apply (simp add:ag_carrier_carrier [THEN sym])
apply auto
apply (simp add:ar_coset_def)
apply (frule_tac a = a and x = x in r_cosTr0 [of "b_ag M" "ker\<^sub>M\<^sub>,\<^sub>N f"],
                                                 assumption+)
apply (simp add:ag_carrier_carrier) apply assumption
apply (simp add:ag_carrier_carrier) (* ? *)
done

lemma indmhom_someTr1:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
 m \<in> carrier M\<rbrakk> \<Longrightarrow>  f (SOME xa. xa \<in> (ar_coset m M (ker\<^sub>M\<^sub>,\<^sub>N f))) = f m"
apply (rule someI2_ex)
 apply (frule_tac m_in_mr_coset[of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f" "m"], assumption+)
 apply (rule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply blast
apply (frule_tac x = x in x_in_mr_coset [of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f" "m"],
                                                              assumption+)
apply (rule mker_submodule [of "R" "M" "N" "f"], assumption+)
apply auto
apply (thin_tac "m +\<^sub>M h \<in> m \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f")
apply (simp add:ker_def) apply (erule conjE)
apply (subst mHom_add[of "R" "M" "N" "f" "m"], assumption+)
apply (frule module_is_ag [of "R" "N"], assumption+)
apply simp
apply (frule mHom_mem [of "R" "M" "N" "f" "m"], assumption+)
apply (simp add:ag_r_zero)
done

lemma indmhom_someTr2:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N; submodule R M H; m \<in> carrier M; H \<subseteq> ker\<^sub>M\<^sub>,\<^sub>N f \<rbrakk> \<Longrightarrow>  f (SOME xa. xa \<in> m \<uplus>\<^sub>M H) = f m"
apply (rule someI2_ex)
 apply (frule_tac m_in_mr_coset[of "R" "M" "H" "m"], assumption+)
 apply blast
apply (frule_tac x = x in x_in_mr_coset [of "R" "M" "H" "m"], assumption+)
 apply (subgoal_tac "\<forall>h\<in>H. m +\<^sub>M h = x \<longrightarrow> f x = f m") apply blast
 apply (thin_tac "\<exists>h\<in>H.  m +\<^sub>M h = x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "h \<in> carrier M") apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "m +\<^sub>M h = x") apply simp
 apply (subst mHom_add[of "R" "M" "N" "f" "m"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (frule mHom_mem [of "R" "M" "N" "f" "m"], assumption+)
 apply (frule_tac A = H and B = "ker\<^sub>M\<^sub>,\<^sub>N f" and c = h in subsetD, assumption+)
 apply (simp add:ker_def)
apply (simp add:ag_r_zero) apply (simp add:ker_def)
 apply (frule_tac A = H and B = "{a. a \<in> carrier M \<and> f a = 0\<^sub>N}" and c = h in
 subsetD, assumption+) apply simp
done

lemma indmhomTr1:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
m \<in> carrier M\<rbrakk> \<Longrightarrow> (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) (m \<uplus>\<^sub>M (ker\<^sub>M\<^sub>,\<^sub>N f)) = f m"
apply (simp add:indmhom_def)
apply (subgoal_tac "m \<uplus>\<^sub>M (ker\<^sub>M\<^sub>,\<^sub>N f) \<in> set_mr_cos M (ker\<^sub>M\<^sub>,\<^sub>N f)")
apply simp
apply (rule indmhom_someTr1, assumption+)
apply (rule set_mr_cos_mem, assumption+)
apply (rule mker_submodule, assumption+)
done

lemma indmhomTr2:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk>
      \<Longrightarrow> (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) \<in> set_mr_cos M (ker\<^sub>M\<^sub>,\<^sub>N f) \<rightarrow> carrier N"
apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:set_mr_cos_def)
 apply auto
 apply (frule_tac m = a in indmhomTr1 [of "R" "M" "N" "f"], assumption+)
 apply (simp add:mHom_mem)
done

lemma indmhom:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk>
      \<Longrightarrow> (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) \<in> mHom R (M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)) N"
apply (simp add:mHom_def [of "R" "M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)" "N"])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (simp add:qmodule_carr)
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. x = a \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f \<longrightarrow>
                                      (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) x \<in> carrier N")
 apply blast apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f")
 apply (rule ballI) apply (rule impI)
 apply simp apply (simp add:indmhomTr1 mHom_mem)
apply (rule conjI)
 apply (simp add:indmhom_def extensional_def)
 apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (simp add:qmodule_carr)
apply (rule ballI)+
 apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (simp add:qmodule_carr)
 apply (subst qmodule_def) apply simp
 apply (simp add:set_mr_cos_def)
  apply (subgoal_tac "\<forall>m\<in>carrier M. \<forall>n\<in>carrier M. a = m \<uplus>\<^sub>M (ker\<^sub>M\<^sub>,\<^sub>N f) \<and>
 b = n \<uplus>\<^sub>M (ker\<^sub>M\<^sub>,\<^sub>N f) \<longrightarrow> ((f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) (mr_cospOp M (ker\<^sub>M\<^sub>,\<^sub>N f) a b) =
              (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) a +\<^sub>N ((f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N) b))")
 apply blast
 apply (thin_tac "\<exists>aa\<in>carrier M. a = aa \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f")
 apply (thin_tac "\<exists>a\<in>carrier M. b = a \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f")
 apply (rule ballI)+ apply (rule impI) apply simp
 apply (thin_tac "a = m \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f \<and> b = n \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f")
 apply (subst mr_cospOpTr [of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f"], assumption+)
apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = m and y = n in ag_pOp_closed [of "M"], assumption+)
 apply (subst indmhomTr1, assumption+)+
 apply (simp add:mHom_add)
apply (rule ballI)+
 apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (simp add:qmodule_carr) apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply auto
 apply (subst mr_cos_sprodTr, assumption+)
apply (rename_tac a m)
 apply (frule_tac a = a and m = m in sprod_mem [of "R" "M"], assumption+)
  apply (subst indmhomTr1, assumption+)+
 apply (simp add:mHom_lin)
done

lemma indmhom_injec:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
       injec\<^sub>(M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f))\<^sub>,\<^sub>N (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N)"
apply (simp add:injec_def)
apply (frule indmhom [of "R" "M" "N" "f"], assumption+)
apply (rule conjI)
apply (simp add:mHom_def)
apply (simp add:ker_def [of  _ _ "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N"])
apply (simp add:qmodule_def) apply (fold qmodule_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. x = a \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f \<longrightarrow> x = ker\<^sub>M\<^sub>,\<^sub>N f")
 apply blast
 apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M ker\<^sub>M\<^sub>,\<^sub>N f")
 apply (rule ballI) apply (rule impI)
 apply simp
 apply (simp add:indmhomTr1)
 apply (subgoal_tac "a \<in> ker\<^sub>M\<^sub>,\<^sub>N f")
apply (rule_tac h1 = a in mr_cos_h_stable [THEN sym, of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f"],
                                                    assumption+)
 apply (simp add:mker_submodule) apply assumption
 apply (simp add:ker_def)
apply (rule subsetI) apply (simp add:CollectI)
 apply (rule conjI)
 apply (simp add:set_mr_cos_def)
 apply (frule mr_cos_oneTr [of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f"], assumption+)
 apply (simp add:mker_submodule)
 apply (frule module_inc_zero [of "R" "M"], assumption+)
 apply blast
apply (subst mr_cos_oneTr [of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f"], assumption+)
 apply (simp add:mker_submodule)
 apply (subst indmhomTr1, assumption+)
 apply (simp add:module_inc_zero)
 apply (simp add:mHom_0)
done

lemma indmhom_surjec1:"\<lbrakk>ring R; R module M; R module N; surjec\<^sub>M\<^sub>,\<^sub>N f;
 f \<in> mHom R M N\<rbrakk> \<Longrightarrow>  surjec\<^sub>(M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f))\<^sub>,\<^sub>N (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N)"
apply (simp add:surjec_def)
 apply (frule indmhom [of "R" "M" "N" "f"], assumption+)
 apply (rule conjI)
 apply (simp add:mHom_def)
apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
apply (rule ballI)
 apply (erule conjE)
 apply (subgoal_tac "b \<in> f ` (carrier M)")
 apply (simp add:image_def)
 prefer 2 apply (simp add:surj_to_def)
apply auto
 apply (frule_tac m = x in indmhomTr1 [of "R" "M" "N" "f"], assumption+)
 apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (simp add:qmodule_carr)
 apply (frule_tac m = x in set_mr_cos_mem [of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f"], assumption+)
apply auto
done

lemma module_homTr:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                           f \<in> mHom R M (mimg\<^sub>R \<^sub>M\<^sub>,\<^sub>N f)"
apply (subst mHom_def) apply (simp add:CollectI)
 apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:mimg_def mdl_def)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:image_def) apply blast
apply (rule conjI)
 apply (simp add:mHom_def aHom_def extensional_def)
apply (rule ballI)+
 apply (simp add:mimg_def mdl_def)
 apply (simp add:mHom_add)
apply (rule ballI)+
 apply (simp add:mimg_def mdl_def)
 apply (simp add:mHom_lin)
done

lemma module_homTr1:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
   (mimg\<^sub>R \<^sub>(M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f))\<^sub>,\<^sub>N (f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N )) = mimg\<^sub>R \<^sub>M\<^sub>,\<^sub>N f"
apply (simp add:mimg_def mdl_def)
apply (simp add:qmodule_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def set_mr_cos_def)
 apply auto
 apply (subst indmhomTr1, assumption+) apply blast
apply (simp add:image_def set_mr_cos_def)
 apply (frule_tac m1 = xa in indmhomTr1 [THEN sym, of "R" "M" "N" "f"],
                                                     assumption+)
 apply auto
done

lemma module_Homth_1:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                     M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f) \<cong>\<^sub>R mimg\<^sub>R \<^sub>M\<^sub>,\<^sub>N f"
apply (simp add:misomorphic_def)
apply (subgoal_tac "bijec\<^sub>(M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f))\<^sub>,\<^sub>(mimg\<^sub>R \<^sub>M\<^sub>,\<^sub>N f)
                                              (indmhom R M N f)")
 apply (subgoal_tac "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N \<in> mHom R (M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)) (mimg\<^sub>R \<^sub>M\<^sub>,\<^sub>N f)")
 apply auto
 apply (frule indmhom [of "R" "M" "N" "f"], assumption+)
 apply (subgoal_tac "R module (M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f))")
 apply (frule module_homTr [of "R" "M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)" "N" "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N"], assumption+)
 apply (simp add:module_homTr1)
 apply (rule qmodule_module, assumption+)
 apply (simp add:mker_submodule)
apply (frule indmhom [of "R" "M" "N" "f"], assumption+)
 apply (subgoal_tac "R module (M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f))")
 apply (frule module_homTr [of "R" "M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)" "N" "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N"], assumption+)
 apply (simp add:module_homTr1)
 apply (thin_tac "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N \<in> mHom R (M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)) N")
apply (simp add:bijec_def)
 apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (frule indmhom_injec [of "R" "M" "N" "f"], assumption+)
 apply (simp add:injec_def)
 apply (simp add:ker_def) apply (simp add:mimg_def mdl_def)
 apply (simp add:surjec_def)
 apply (rule conjI) apply (simp add:mHom_def)
 apply (frule mker_submodule [of "R" "M" "N" "f"], assumption+)
 apply (simp add:qmodule_carr)
 apply (simp add:mimg_def mdl_def) apply (fold mdl_def)
 apply (rule surj_to_test)
 apply (thin_tac "f \<in> mHom R M N")
 apply (simp add:mHom_def aHom_def) apply (frule conj_1)
 apply (simp add:qmodule_carr mdl_def)
prefer 2  apply (rule qmodule_module, assumption+)
 apply (simp add:mker_submodule)
 apply (rule ballI)
 apply (thin_tac "f\<^sup>\<flat>\<^sub>R \<^sub>M\<^sub>,\<^sub>N \<in> mHom R (M /\<^sub>m (ker\<^sub>M\<^sub>,\<^sub>N f)) (mdl N (f ` carrier M))")
 apply (simp add:image_def) apply auto
 apply (frule_tac m = x in indmhomTr1 [of "R" "M" "N" "f"], assumption+)
 apply (frule_tac m = x in set_mr_cos_mem [of "R" "M" "ker\<^sub>M\<^sub>,\<^sub>N f"], assumption+)
 apply auto
done

constdefs
 mpj :: "[('a, 'r, 'm) ModuleType_scheme, 'a set] \<Rightarrow>  ('a => 'a set)"
      "mpj M H == \<lambda>x\<in>carrier M. x \<uplus>\<^sub>M H"

lemma mpj_mHom:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                                mpj M H \<in> mHom R M (M /\<^sub>m H)"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mpj_def qmodule_carr)
 apply (simp add:set_mr_cos_mem)
apply (rule conjI)
 apply (simp add:mpj_def extensional_def)
apply (rule ballI)+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed [of "M"], assumption+)
 apply (simp add:mpj_def)
 apply (simp add:qmodule_def)
 apply (subst mr_cospOpTr, assumption+) apply simp
apply (rule ballI)+
 apply (simp add:mpj_def qmodule_def)
 apply (simp add:sprod_mem)
 apply (simp add:mr_cos_sprodTr)
done

lemma mpj_mem:"\<lbrakk>ring R; R module M; submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                                mpj M H m \<in> carrier (M /\<^sub>m H)"
apply (frule mpj_mHom[of "R" "M" "H"], assumption+)
apply (rule mHom_mem [of "R" "M" "M /\<^sub>m H" "mpj M H" "m"], assumption+)
 apply (simp add:qmodule_module) apply assumption+
done

lemma mpj_surjec:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                                   surjec\<^sub>M\<^sub>,\<^sub>(M /\<^sub>m H) (mpj M H)"
apply (simp add:surjec_def)
apply (frule mpj_mHom [of "R" "M" "H"])
apply assumption+
apply (simp add:mHom_def) apply (erule conjE)
 apply (thin_tac "\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. mpj M H ( a \<star>\<^sub>M m) =  a \<star>\<^sub>(M /\<^sub>m H) (mpj M H m)")
 apply (rule surj_to_test)
 apply (simp add:aHom_def)
apply (rule ballI)
 apply (thin_tac "mpj M H \<in> aHom M (M /\<^sub>m H)")
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
apply (subgoal_tac "\<forall>a\<in>carrier M. b = a \<uplus>\<^sub>M H \<longrightarrow> (\<exists>a\<in>carrier M. mpj M H a = b)")
apply blast apply (thin_tac "\<exists>a\<in>carrier M. b = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI) apply simp
 apply (simp add:mpj_def) apply blast
done

lemma mpj_0:"\<lbrakk>ring R; R module M; submodule R M H; h \<in> H\<rbrakk> \<Longrightarrow>
                                 mpj M H h  = 0\<^sub>(M /\<^sub>m H)"
apply (simp add:mpj_def)
apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:subsetD)
 apply (simp add:qmodule_def)
 apply (frule_tac m = h in m_in_mr_coset [of "R" "M" "H"], assumption+)
 apply (simp add:submodule_def)
 apply (simp add:subsetD)
 apply (rule mr_cos_h_stable[THEN sym], assumption+)
 apply (simp add:submodule_def)
apply assumption
done

lemma mker_of_mpj:"\<lbrakk>ring R; R module M; submodule R M H\<rbrakk> \<Longrightarrow>
                                 ker\<^sub>M\<^sub>,\<^sub>(M /\<^sub>m H) (mpj M H) = H"
apply (simp add:ker_def)
apply (simp add:mpj_def)
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI)
 apply (erule conjE) apply simp
 apply (simp add:qmodule_def)
 apply (frule_tac m = x in m_in_mr_coset [of "R" "M" "H"], assumption+)
 apply simp
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (rule conjI) apply (rule impI)
 apply (simp add:qmodule_def)
 apply (rule mr_cos_h_stable[THEN sym], assumption+)
 apply (simp add:submodule_def) apply assumption
 apply (simp add:subsetD)
done

lemma indmhom1:"\<lbrakk>ring R; R module M; submodule R M H; R module N; f \<in> mHom R M N;  H \<subseteq> ker\<^sub>M\<^sub>,\<^sub>N f\<rbrakk> \<Longrightarrow> \<exists>!g. g \<in> (mHom R (M /\<^sub>m H) N) \<and> (compose (carrier M) g (mpj M H)) = f"
apply (rule ex_ex1I)
prefer 2
apply (rename_tac g h)
 apply (erule conjE)+
 apply (frule qmodule_module[of "R" "M" "H"], assumption+)
 apply (rule_tac f = g and g = h in mHom_eq[of "R" "M /\<^sub>m H" "N"], assumption+)
 apply (rule ballI)
 apply (simp add:qmodule_def) apply (fold qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. m = a \<uplus>\<^sub>M H \<longrightarrow> g m = h m") apply blast
 apply (thin_tac "\<exists>a\<in>carrier M. m = a \<uplus>\<^sub>M H") apply (rule ballI)
 apply (rule impI)
 apply (subgoal_tac "mpj M H a = a \<uplus>\<^sub>M H") prefer 2 apply (simp add:mpj_def)
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "mpj M H a = a \<uplus>\<^sub>M H")
 apply simp
 apply (subgoal_tac "compose (carrier M) g (mpj M H) a = f a")
 prefer 2 apply simp apply (thin_tac "compose (carrier M) g (mpj M H) = f")
 apply (subgoal_tac "compose (carrier M) h (mpj M H) a = f a")
 prefer 2 apply simp apply (thin_tac "compose (carrier M) h (mpj M H) = f")
 apply (simp add:compose_def)
apply (subgoal_tac "(\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)) \<in> mHom R  (M /\<^sub>m H) N \<and> compose (carrier M) (\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)) (mpj M H) = f")
 apply blast
 apply (rule conjI)
apply (rule mHom_test, assumption+)
 apply (simp add:qmodule_module) apply assumption+
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:qmodule_def) apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. x =  a \<uplus>\<^sub>M H \<longrightarrow> f (SOME xa. xa \<in> x) \<in> carrier N") apply blast apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI) apply simp
 apply (simp add:indmhom_someTr2) apply (simp add:mHom_mem)
apply (rule conjI)
 apply (simp add:qmodule_def)
apply (rule conjI) apply (rule ballI)+
 apply (simp add:qmodule_def)
 apply (subgoal_tac "mr_cospOp M H m n \<in> set_mr_cos M H")
 apply (simp add:set_mr_cos_def) apply (thin_tac "\<exists>a\<in>carrier M. mr_cospOp M H m n = a \<uplus>\<^sub>M H")
 apply (subgoal_tac "\<forall>a\<in>carrier M. \<forall>b\<in>carrier M.  m = a \<uplus>\<^sub>M H \<and> n = b \<uplus>\<^sub>M H \<longrightarrow> f (SOME x. x \<in> mr_cospOp M H m n) = f (SOME x. x \<in> m) +\<^sub>N (f (SOME x. x \<in> n))")  apply blast apply (thin_tac "\<exists>a\<in>carrier M. m = a \<uplus>\<^sub>M H")
 apply (thin_tac "\<exists>a\<in>carrier M. n = a \<uplus>\<^sub>M H") apply (rule ballI)+
 apply (rule impI) apply (erule conjE) apply simp
 apply (simp add:mr_cospOpTr [of "R" "M" "H"])
 apply (simp add:indmhom_someTr2)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed[of "M"], assumption+)
 apply (simp add:indmhom_someTr2) apply (simp add:mHom_add)
apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. \<forall>b\<in>carrier M.  m = a \<uplus>\<^sub>M H \<and> n = b \<uplus>\<^sub>M H \<longrightarrow> (\<exists>a\<in>carrier M. mr_cospOp M H m n = a \<uplus>\<^sub>M H)") apply blast
 apply (thin_tac "\<exists>a\<in>carrier M. m = a \<uplus>\<^sub>M H") apply (thin_tac "\<exists>a\<in>carrier M. n = a \<uplus>\<^sub>M H") apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp apply (simp add:mr_cospOpTr [of "R" "M" "H"])
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed[of "M"], assumption+)
 apply blast
apply (rule ballI)+
 apply (simp add:qmodule_def)
 apply (frule_tac a = a and X = m in mr_cos_sprod_mem [of "R" "M" "H"], assumption+) apply simp
 apply (subgoal_tac "\<exists>a\<in>carrier M. m = a \<uplus>\<^sub>M H")
 prefer 2 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>n\<in>carrier M. m = n \<uplus>\<^sub>M H \<longrightarrow> f (SOME x. x \<in> mr_cos_sprod M H a m) =  a \<star>\<^sub>N (f (SOME x. x \<in> m))")
 apply blast apply (thin_tac "\<exists>a\<in>carrier M. m = a \<uplus>\<^sub>M H") apply (rule ballI)
 apply (rule impI) apply simp
 apply (simp add:mr_cos_sprodTr)
 apply (frule_tac a = a and m = n in sprod_mem[of "R" "M"], assumption+)
 apply (simp add:indmhom_someTr2)
 apply (simp add:mHom_lin)
apply (subgoal_tac "f \<in> carrier M \<rightarrow> carrier N \<and> f \<in> extensional (carrier M)")
 prefer 2 apply (simp add:mHom_def aHom_def) apply (erule conjE)
 apply (subgoal_tac "compose (carrier M) (\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)) (mpj M H) \<in> carrier M \<rightarrow> carrier N")
 apply (rule_tac f = "compose (carrier M) (\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)) (mpj M H)" and A = "carrier M" and g = f in funcset_eq)
 apply (simp add:compose_def restrict_def extensional_def) apply assumption
apply (rule ballI) apply (simp add:compose_def)
 apply (subgoal_tac "mpj M H x \<in> set_mr_cos M H") apply simp
 prefer 2 apply (simp add:mpj_def set_mr_cos_def) apply blast
 apply (simp add:set_mr_cos_def)
apply (subgoal_tac "\<forall>a\<in>carrier M. mpj M H x = a \<uplus>\<^sub>M H \<longrightarrow> f (SOME xa. xa \<in> mpj M H x) = f x") apply blast apply (thin_tac "\<exists>a\<in>carrier M. mpj M H x = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI) apply simp
 apply (frule_tac m = a in indmhom_someTr2[of "R" "M" "N" "f" "H"], assumption+) apply simp apply (thin_tac "f (SOME xa. xa \<in> a \<uplus>\<^sub>M H) = f a")
 apply (thin_tac "(\<lambda>x\<in>carrier M. if \<exists>a\<in>carrier M. mpj M H x = a \<uplus>\<^sub>M H then f (SOME xa. xa \<in> mpj M H x) else arbitrary) \<in> carrier M \<rightarrow> carrier N")
 apply (simp add:mpj_def)
 apply (frule_tac m = x in m_in_mr_coset[of "R" "M" "H"], assumption+)
 apply simp apply (thin_tac "x \<uplus>\<^sub>M H = a \<uplus>\<^sub>M H")
 apply (frule_tac m = a and x = x in x_in_mr_coset[of "R" "M" "H"], assumption+)
 apply (subgoal_tac "\<forall>h\<in>H. a +\<^sub>M h = x \<longrightarrow> f a = f x") apply blast
 apply (thin_tac "\<exists>h\<in>H.  a +\<^sub>M h = x") apply (rule ballI) apply (rule impI)
 apply (frule sym) apply (thin_tac "a +\<^sub>M h = x") apply simp
 apply (subgoal_tac "h \<in> carrier M")
 apply (simp add:mHom_add) apply (frule_tac A = H and B = " ker\<^sub>M\<^sub>,\<^sub>N f" and c = h in subsetD, assumption+) apply (simp add:ker_def)
 apply (frule_tac m = a in mHom_mem[of "R" "M" "N" "f"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+) apply (simp add:ag_r_zero)
 apply (frule_tac A = H and B = "ker\<^sub>M\<^sub>,\<^sub>N f" and c = h in subsetD, assumption+)
 apply (simp add:ker_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:compose_def) apply (subgoal_tac "mpj M H x \<in> set_mr_cos M H")
 apply simp apply (simp add:mpj_def)
 apply (simp add:indmhom_someTr2[of "R" "M" "N" "f" "H"]) apply (simp add:funcset_mem)
apply (simp add:mpj_def set_mr_cos_def)  apply blast
done

constdefs
  mQmp :: "[('a, 'r, 'm) ModuleType_scheme, 'a set, 'a set] \<Rightarrow>
                                                   ('a set \<Rightarrow> 'a set)"
 "mQmp M H N == \<lambda>X\<in> set_mr_cos M H. {z. \<exists> x \<in> X. \<exists> y \<in> N. (y +\<^sub>M x = z)}"
             (* H \<subseteq> N *)
syntax
   "@MQP" :: "[('a, 'b) ModuleType, 'a set, 'a set] \<Rightarrow> ('a set \<Rightarrow> 'a set)"
               ("(3Mqp\<^sub>_\<^sub>'/'\<^sub>_\<^sub>,\<^sub>_)" [82,82,83]82)
translations
   "Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N" == "mQmp M H N"

 (* "\<lbrakk> R Module M; H \<subseteq> N \<rbrakk> \<Longrightarrow> Mqp\<^sub>M \<^sub>/\<^sub>m \<^sub>H\<^sub>,\<^sub>N  \<in> rHom (M /\<^sub>m H) (M /\<^sub>m N)"  *)

lemma mQmpTr0: "\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N;
 m \<in> carrier M\<rbrakk> \<Longrightarrow>  mQmp M H N (m \<uplus>\<^sub>M H) = m \<uplus>\<^sub>M N"
apply (frule set_mr_cos_mem [of "R" "M" "H" "m"], assumption+)
apply (simp add:mQmp_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>xa\<in>m \<uplus>\<^sub>M H. \<forall>y\<in>N.  y +\<^sub>M xa = x \<longrightarrow> x \<in> m \<uplus>\<^sub>M N")
 apply blast apply (thin_tac "\<exists>xa\<in>m \<uplus>\<^sub>M H. \<exists>y\<in>N.  y +\<^sub>M xa = x")
 apply (rule ballI)+ apply (rule impI)
 apply (frule_tac x = xa in  x_in_mr_coset [of "R" "M" "H" "m"], assumption+)
 apply (subgoal_tac "\<forall>h\<in>H.  m +\<^sub>M h = xa \<longrightarrow> x \<in> m \<uplus>\<^sub>M N")
 apply blast apply (thin_tac "\<exists>h\<in>H.  m +\<^sub>M h = xa")
 apply (rule ballI) apply (rule impI) apply (frule sym)
 apply (thin_tac "y +\<^sub>M xa = x") apply simp apply (thin_tac "x =  y +\<^sub>M xa")
 apply (frule sym) apply (thin_tac "m +\<^sub>M h = xa")
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_pOp_commute, assumption+)
 apply (simp add:submodule_def [of "R" "M" "N"]) apply (erule conjE)+
 apply (rule subsetD, assumption+) apply simp
 apply (rule_tac x = m and y = h in ag_pOp_closed [of "M"], assumption+)
 apply (simp add:submodule_def [of "R" "M" "H"]) apply (erule conjE)+
 apply (rule subsetD, assumption+) apply simp
 apply (subst ag_pOp_assoc, assumption+)
 apply (simp add:submodule_def [of "R" "M" "H"]) apply (erule conjE)+
 apply (simp add:subsetD)
 apply (simp add:submodule_def [of "R" "M" "N"]) apply (erule conjE)+
 apply (simp add:subsetD)
apply (simp add:submodule_def [of "R" "M" "N"]) apply (erule conjE)+
apply (frule_tac c = h in subsetD [of "H" "N"], assumption+)
apply (frule_tac x = h and y = y in asubg_pOp_closed [of "M" "N"],
                                                          assumption+)
apply (frule_tac h = "h +\<^sub>M y" in mr_cos_h_stable1 [of "R" "M" "N" "m"],
                                                            assumption+)
apply (simp add:submodule_def) apply assumption+
 apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "(m +\<^sub>M ( h +\<^sub>M y)) \<uplus>\<^sub>M N = m \<uplus>\<^sub>M N")
 apply simp
 apply (rule m_in_mr_coset [of "R" "M" "N"], assumption+)
 apply (simp add:submodule_def)
 apply (rule ag_pOp_closed, assumption+)
 apply (simp add:subsetD)
apply (rule subsetI)
 apply (simp add:mr_coset_def)
 apply (subgoal_tac "N\<^sub>(b_ag M) m = m \<uplus>\<^sub>M N")
 apply (subgoal_tac "H\<^sub>(b_ag M) m = m \<uplus>\<^sub>M H")
 apply (thin_tac " N\<^sub>(b_ag M) m = m \<uplus>\<^sub>M N")
 apply (thin_tac " H\<^sub>(b_ag M) m = m \<uplus>\<^sub>M H")
prefer 2 apply (simp only:ar_coset_def [of "m" "M" "H"])
prefer 2 apply (simp only:ar_coset_def [of "m" "M" "N"])
 apply (frule_tac x = x in x_in_mr_coset [of "R" "M" "N" "m"], assumption+)
 apply (frule m_in_mr_coset [of "R" "M" "H" "m"], assumption+)
 apply auto
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_pOp_commute [of M m], assumption+)
 apply (simp add:submodule_def [of _ _ "N"])
 apply auto
done

  (* show mQmp M H N is a welldefined map from M/H to M/N. step2 *)
lemma mQmpTr1:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N;
 m \<in> carrier M; n \<in> carrier M; m \<uplus>\<^sub>M H = n \<uplus>\<^sub>M H\<rbrakk> \<Longrightarrow>  m \<uplus>\<^sub>M N = n \<uplus>\<^sub>M N"
apply (frule_tac m_in_mr_coset [of "R" "M" "H" "m"], assumption+)
apply simp
apply (frule_tac x_in_mr_coset [of "R" "M" "H" "n" "m"], assumption+)
apply (auto del:equalityI)
apply (frule_tac c = h in subsetD [of "H" "N"], assumption+)
apply (rule mr_cos_h_stable1[of "R" "M" "N" "n"], assumption+)
done

lemma mQmpTr2:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N ; X \<in> carrier (M /\<^sub>m H)\<rbrakk> \<Longrightarrow> (mQmp M H N) X \<in> carrier (M /\<^sub>m N)"
apply (simp add:qmodule_def)
apply (simp add:set_mr_cos_def)
apply auto
 apply (frule_tac m = a in mQmpTr0 [of "R" "M" "H" "N"], assumption+)
apply auto
done

lemma mQmpTr2_1:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N \<rbrakk>
 \<Longrightarrow> mQmp M H N \<in> carrier (M /\<^sub>m H) \<rightarrow> carrier (M /\<^sub>m N)"
apply (simp add:Pi_def)
apply (auto del:equalityI)
apply (simp add:mQmpTr2 [of "R" "M" "H" "N" _])
done

lemma mQmpTr3:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N ;
X \<in> carrier (M /\<^sub>m H); Y \<in> carrier (M /\<^sub>m H)\<rbrakk> \<Longrightarrow> (mQmp M H N) (mr_cospOp M H X Y) = mr_cospOp M N ((mQmp M H N) X) ((mQmp M H N) Y)"
apply (simp add:qmodule_def)
apply (simp add:set_mr_cos_def)
apply (auto del:equalityI)
apply (subst mr_cospOpTr, assumption+)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule_tac x = a and y = aa in ag_pOp_closed, assumption+)
apply (subst mQmpTr0, assumption+)+
apply (subst mr_cospOpTr, assumption+)
apply simp
done

lemma mQmpTr4:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N;
 a \<in> N\<rbrakk> \<Longrightarrow> mr_coset a (mdl M N) H = mr_coset a M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule b_ag_group)
apply (simp add:submodule_def) apply (erule conjE)+
apply (frule asubg_nsubg [of "M" "H"], assumption+)
apply (frule asubg_nsubg [of "M" "N"], assumption+)
apply (simp add:mr_coset_def ar_coset_def)
apply (simp add:asubgroup_def)
apply (frule nsubg_in_subg [of "b_ag M" "H" "N"], assumption+)
apply (simp add:nmlSubgTr0) apply (simp add:r_coset_def)
apply (simp add:mdl_def b_ag_def)
done

lemma mQmp_mHom: "\<lbrakk>ring R; R module M; submodule R M H; submodule R M N;
H \<subseteq> N\<rbrakk> \<Longrightarrow> (Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N) \<in> mHom R (M /\<^sub>m H) (M /\<^sub>m N)"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (simp add:mQmpTr2_1)
apply (rule conjI)
 apply (simp add:mQmp_def extensional_def qmodule_def)
 apply (rule ballI)+
 apply (frule_tac X1 = a and Y1 = b in mQmpTr3 [THEN sym, of "R" "M" "H" "N"],
                                               assumption+)
 apply (simp add:qmodule_def)
apply (rule ballI)+
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>n\<in>carrier M. m = n \<uplus>\<^sub>M H \<longrightarrow> ((Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N) (mr_cos_sprod M H a m) = mr_cos_sprod M N a ((Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N) m))")
 apply blast apply (thin_tac "\<exists>a\<in>carrier M. m = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI) apply simp
 apply (subst mr_cos_sprodTr, assumption+)
 apply (frule_tac a = a and m = n in sprod_mem [of "R" "M"], assumption+)
 apply (simp add:mQmpTr0)
 apply (subst mr_cos_sprodTr, assumption+)
apply simp
done

lemma Mqp_surjec: "\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow> surjec\<^sub>(M /\<^sub>m H)\<^sub>,\<^sub>(M /\<^sub>m N) (Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N)"
apply (simp add:surjec_def)
 apply (frule mQmp_mHom [of "R" "M" "H" "N"], assumption+)
 apply (rule conjI)
 apply (simp add:mHom_def)
apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
 apply (rule ballI)
 apply (thin_tac "Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N \<in> mHom R (M /\<^sub>m H) (M /\<^sub>m N)")
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply auto
 apply (frule_tac m = a in mQmpTr0 [of "R" "M" "H" "N"], assumption+)
 apply auto
done

lemma kerQmp: "\<lbrakk>ring R; R module M; submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk>
 \<Longrightarrow> ker\<^sub>(M /\<^sub>m H)\<^sub>,\<^sub>(M /\<^sub>m N) (Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N) = carrier ((mdl M N) /\<^sub>m H)"
apply (simp add:ker_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI) apply (erule conjE)
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def [of "mdl M N" "H"])
 apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>b\<in>carrier M. x = b \<uplus>\<^sub>M H \<longrightarrow> ( \<exists>a\<in>carrier (mdl M N). x = a \<uplus>\<^sub>(mdl M N) H)")
 apply blast
 apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M H")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac m = b in mQmpTr0 [of "R" "M" "H" "N"], assumption+)
 apply simp
 apply (frule_tac m = b in m_in_mr_coset [of "R" "M" "N"], assumption+)
 apply (subgoal_tac "carrier (mdl M N) = N") prefer 2 apply (simp add:mdl_def)
 apply simp
 apply (frule mQmpTr4 [THEN sym, of "R" "M" "H" "N"], assumption+)
 apply (simp add:mr_coset_def)
 apply blast
apply (rule subsetI)
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def [of "mdl M N" "H"])
 apply (subgoal_tac "\<forall>a\<in>carrier (mdl M N). x = a \<uplus>\<^sub>(mdl M N) H \<longrightarrow>
                        x \<in> set_mr_cos M H \<and> (Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N) x = N")
 apply blast
 apply (thin_tac "\<exists>a\<in>carrier (mdl M N). x = a \<uplus>\<^sub>(mdl M N) H")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac a = a in mQmpTr4 [of "R" "M" "H" "N"], assumption+)
 apply (simp add:mdl_def) apply (simp add:mr_coset_def)
 apply (thin_tac "a \<uplus>\<^sub>(mdl M N) H = a \<uplus>\<^sub>M H")
 apply (simp add:mdl_def)
 apply (subgoal_tac "a \<in> carrier M")
 apply (simp add:set_mr_cos_mem) apply (simp add:mQmpTr0)
 apply (simp add:mr_cos_h_stable [THEN sym])
apply (simp add:submodule_def [of _ _ "N"]) apply (erule conjE)+
 apply (simp add:subsetD)
done

lemma misom2Tr:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N;
           H \<subseteq> N\<rbrakk> \<Longrightarrow> (M /\<^sub>m H) /\<^sub>m (carrier ((mdl M N) /\<^sub>m H)) \<cong>\<^sub>R (M /\<^sub>m N)"
apply (frule mQmp_mHom [of "R" "M" "H" "N"], assumption+)
apply (frule qmodule_module [of "R" "M" "H"], assumption+)
apply (frule qmodule_module [of "R" "M" "N"], assumption+)
apply (frule indmhom [of "R" "M /\<^sub>m H" "M /\<^sub>m N" "Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N"], assumption+)
apply (simp add:kerQmp)
apply (subgoal_tac "bijec\<^sub>((M /\<^sub>m H) /\<^sub>m (carrier((mdl M N) /\<^sub>m H)))\<^sub>,\<^sub>(M /\<^sub>m N)
 (indmhom R (M /\<^sub>m H) (M /\<^sub>m N) (mQmp M H N))")
apply (simp add:misomorphic_def) apply blast
apply (simp add:bijec_def)
apply (rule conjI)
 apply (simp add:kerQmp [THEN sym])
 apply (rule indmhom_injec [of "R" "M /\<^sub>m H" "M /\<^sub>m N" "Mqp\<^sub>M\<^sub>/\<^sub>H\<^sub>,\<^sub>N"], assumption+)
apply (frule Mqp_surjec [of "R" "M" "H" "N"], assumption+)
 apply (simp add:kerQmp [THEN sym])
 apply (rule indmhom_surjec1, assumption+)
done

lemma eq_class_of_Submodule:"\<lbrakk>ring R; R module M; submodule R M H;
            submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow> carrier ((mdl M N) /\<^sub>m H) = N \<^sub>s/\<^sub>M H"
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def) apply auto
 apply (frule_tac a = a in mQmpTr4 [of "R" "M" "H" "N"], assumption+)
 apply (simp add:mdl_def) apply (simp add:mr_coset_def)
 apply (simp add:sub_mr_set_cos_def)
 apply (simp add:mdl_def)
 apply auto
apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply (simp add:sub_mr_set_cos_def)
 apply auto
 apply (frule_tac a1 = n in mQmpTr4[THEN sym, of "R" "M" "H" "N"], assumption+)
 apply (simp add:mr_coset_def)
 apply (subgoal_tac "carrier (mdl M N) = N")  apply simp
 apply (auto del:equalityI)
apply (simp add:mdl_def)
done

theorem misom2:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M N;
           H \<subseteq> N\<rbrakk> \<Longrightarrow> (M /\<^sub>m H) /\<^sub>m (N \<^sub>s/\<^sub>M H) \<cong>\<^sub>R (M /\<^sub>m N)"
apply (frule misom2Tr [of "R" "M" "H" "N"], assumption+)
apply (simp add:eq_class_of_Submodule)
done

consts
  natm ::  "('a, 'm) AgroupType_scheme  => nat \<Rightarrow> 'a  => 'a"

primrec
 natm_0:  "natm M 0 x = 0\<^sub>M"
 natm_Suc:  "natm M (Suc n) x = (natm M n x) +\<^sub>M x"

constdefs
 finitesum_base::"[('a, 'r, 'm) ModuleType_scheme, 'b set, 'b \<Rightarrow> 'a set]
                      \<Rightarrow> 'a set "
   "finitesum_base M I f == \<Union>{f i | i. i \<in> I}"

constdefs
finitesum ::"[('a, 'r, 'm) ModuleType_scheme, 'b set, 'b \<Rightarrow> 'a set]
                      \<Rightarrow> 'a set "
"finitesum M I f == {x. \<exists>n. \<exists>g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and>                                                          x =  eSum M g n}"


lemma finitesumbase_sub_carrier:"\<lbrakk>ring R; R module M;
 f \<in> I \<rightarrow> {X. submodule R M X}\<rbrakk> \<Longrightarrow> finitesum_base M I f \<subseteq> carrier M"
apply (simp add:finitesum_base_def)
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> x \<in> xa \<longrightarrow> x \<in> carrier M")
 apply blast
 apply (thin_tac "\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> x \<in> xa")
 apply (rule allI)
 apply (rule impI)
 apply (erule conjE)+
 apply auto
 apply (frule_tac x = i in funcset_mem [of "f" "I" "Collect (submodule R M)"],
                                                              assumption+)
 apply (thin_tac "f \<in> I \<rightarrow> Collect (submodule R M)")
 apply (simp add:CollectI)
 apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:subsetD)
done

lemma finitesum_ex_one:"\<lbrakk>ring R; R module M; f \<in> I \<rightarrow> {X. submodule R M X};
I \<noteq> {}\<rbrakk>  \<Longrightarrow> 0\<^sub>M \<in> finitesum M I f"
apply (simp add:finitesum_def)
apply (subgoal_tac "\<exists>i. i \<in> I") prefer 2 apply blast
apply (subgoal_tac "\<forall>i. i\<in>I \<longrightarrow> (\<exists>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> 0\<^sub>M = e\<Sigma> M g n)")
apply blast apply (thin_tac "\<exists>i. i \<in> I")
apply (rule allI) apply (rule impI)
apply (subgoal_tac "(\<lambda>x\<in>Nset 0. 0\<^sub>M) \<in> Nset 0 \<rightarrow> finitesum_base M I f \<and>
          0\<^sub>M = e\<Sigma> M (\<lambda>x\<in>Nset 0. 0\<^sub>M) 0")
apply blast
apply (rule conjI)
apply (rule univar_func_test)
apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:finitesum_base_def)
 apply (frule_tac x = i in funcset_mem [of "f" "I" "{X. submodule R M X}"],
                                                  assumption+)
 apply (simp add:CollectI) apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule_tac H = "f i" in asubg_inc_zero [of "M"], assumption+)
 apply blast
apply (simp add:Nset_def)
done

lemma finitesum_iOp_closed:"\<lbrakk>ring R; R module M; f \<in> I \<rightarrow> {X. submodule R M X}; I \<noteq> {}; a \<in> finitesum M I f\<rbrakk> \<Longrightarrow> -\<^sub>M a \<in> finitesum M I f"
apply (simp add:finitesum_def)
apply (subgoal_tac "\<forall>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> a = e\<Sigma> M g n
    \<longrightarrow> (\<exists>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> -\<^sub>M a = e\<Sigma> M g n)")
apply blast
 apply (thin_tac "\<exists>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> a = e\<Sigma> M g n")
 apply (rule allI)+ apply (rule impI)
 apply (erule conjE) apply simp apply (thin_tac "a = e\<Sigma> M g n")
 apply (frule module_is_ag [of "R" "M"], assumption+)
  apply (frule finitesumbase_sub_carrier [of "R" "M" "f" "I"], assumption+)
  apply (frule_tac f = g and A = "Nset n" and B = "finitesum_base M I f"
          and ?B1.0 = "carrier M" in extend_fun, assumption+)
apply (simp add: eSum_minus [of M])
 apply (subgoal_tac "(\<lambda>x\<in>Nset n. -\<^sub>M (g x)) \<in> Nset n \<rightarrow> finitesum_base M I f")
 apply blast
apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (frule_tac f = g and A = "Nset n" and B = "finitesum_base M I f" and
   x = x in funcset_mem, assumption+)
 apply (simp add:finitesum_base_def)
 apply (subgoal_tac "\<forall>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> g x \<in> xa \<longrightarrow>
                        (\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> -\<^sub>M (g x) \<in> xa)")
 apply blast
 apply (thin_tac "\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> g x \<in> xa")
 apply (rule allI) apply (rule impI)
 apply (erule conjE)
 apply (subgoal_tac "\<forall>i. xa = f i \<and> i \<in> I \<longrightarrow> (\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I)
                           \<and> -\<^sub>M (g x) \<in> xa)")
 apply blast apply (thin_tac "\<exists>i. xa = f i \<and> i \<in> I")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac f = f and A = I and B = "{X. submodule R M X}" and
  x = i in funcset_mem, assumption+) apply (simp add:CollectI)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (thin_tac "f \<in> I \<rightarrow> {X. submodule R M X}")
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule_tac H = "f i" and x = "g x" in asubg_mOp_closed [of "M"],
                                                                  assumption+)
 apply blast
done

lemma finitesum_tOp_closed:
 "\<lbrakk>ring R; R module M; f \<in> I \<rightarrow> {X. submodule R M X}; a \<in> finitesum M I f;
 b \<in> finitesum M I f\<rbrakk>  \<Longrightarrow>  a +\<^sub>M b \<in> finitesum M I f"
apply (simp add:finitesum_def)
apply auto
apply (subgoal_tac "jointfun n g na ga \<in> Nset (Suc (n + na)) \<rightarrow> finitesum_base M I f")
apply (subgoal_tac "e\<Sigma> M g n +\<^sub>M (e\<Sigma> M ga na) = e\<Sigma> M (jointfun n g na ga) (Suc (n + na))")
apply (simp del:eSum_Suc)
apply blast
 apply (frule finitesumbase_sub_carrier [of "R" "M" "f" "I"], assumption+)
 apply (frule_tac f = g and A = "Nset n" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)
 apply (thin_tac "g \<in> Nset n \<rightarrow> finitesum_base M I f")
 apply (frule_tac f = ga and A = "Nset na" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)
 apply (thin_tac "ga \<in> Nset na \<rightarrow> finitesum_base M I f")
 apply (frule_tac f = "jointfun n g na ga" and A = "Nset (Suc (n + na))" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)
 apply (thin_tac "jointfun n g na ga \<in> Nset (Suc (n + na)) \<rightarrow> finitesum_base M I f")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst eSum_split, assumption+)
 apply (subgoal_tac "e\<Sigma> M g n = e\<Sigma> M (jointfun n g na ga) n") apply simp
 apply (subgoal_tac "e\<Sigma> M ga na = e\<Sigma> M (cmp (jointfun n g na ga) (slide (Suc n))) na") apply simp
apply (thin_tac "jointfun n g na ga \<in> Nset (Suc (n + na)) \<rightarrow> carrier M")
apply (thin_tac "e\<Sigma> M g n = e\<Sigma> M (jointfun n g na ga) n")
apply (simp add:cmp_def jointfun_def slide_def sliden_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (rule eSum_eq, assumption+)
apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<in> Nset (Suc (n + na))") apply (simp add:funcset_mem)
 apply (simp add:Nset_def)
 apply (rule ballI) apply (simp add:Nset_def jointfun_def)
 apply (frule_tac f = g and n = n and A = "finitesum_base M I f" and
  g = ga and m = na and B = "finitesum_base M I f" in jointfun_hom, assumption+)
 apply simp
done

lemma finitesum_sprodTr:"\<lbrakk>ring R; R module M; f \<in> I \<rightarrow> {X. submodule R M X};
I \<noteq> {}; r \<in> carrier R\<rbrakk>  \<Longrightarrow> g \<in>Nset n \<rightarrow> (finitesum_base M I f)
              \<longrightarrow> r \<star>\<^sub>M (eSum M g n) =  eSum M (\<lambda>x. r \<star>\<^sub>M (g x)) n"
apply (induct_tac n)
 apply (rule impI)
 apply (simp add:Nset_def)
apply (rule impI)
apply (frule func_pre) apply simp
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule finitesumbase_sub_carrier [of "R" "M" "f" "I"], assumption+)
 apply (frule_tac f = g and A = "Nset (Suc n)" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)
 apply (thin_tac "g \<in> Nset (Suc n) \<rightarrow> finitesum_base M I f")
 apply (thin_tac "g \<in> Nset n \<rightarrow> finitesum_base M I f")
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule func_pre)
 apply (frule_tac n = n and i = n in eSum_mem [of "M" "g"], assumption+)
 apply (simp add:Nset_def)
 apply (frule_tac x = "Suc n" in funcset_mem [of "g" _ "carrier M"],
                                                           assumption+)
 apply (subst sprod_distrib2, assumption+)
 apply (simp del:eSum_Suc)
apply (simp add:Nset_def)
done

lemma finitesum_sprod:"\<lbrakk>ring R; R module M; f \<in> I \<rightarrow> {X. submodule R M X};
I \<noteq> {}; r \<in> carrier R; g \<in>Nset n \<rightarrow> (finitesum_base M I f) \<rbrakk> \<Longrightarrow>
                       r \<star>\<^sub>M (eSum M g n) =  eSum M (\<lambda>x. r \<star>\<^sub>M (g x)) n"
apply (simp add:finitesum_sprodTr)
done

lemma finitesum_subModule:"\<lbrakk>ring R; R module M; f \<in> I \<rightarrow> {X. submodule R M X};
I \<noteq> {}\<rbrakk>  \<Longrightarrow> submodule R M (finitesum M I f)"
apply (simp add:submodule_def [of _ _ "(finitesum M I f)"])
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (rule conjI)
 apply (simp add:finitesum_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (auto del:equalityI)
 apply (frule finitesumbase_sub_carrier [of "R" "M" "f" "I"], assumption+)
apply (frule_tac f = g and A = "Nset n" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)
 apply (rule_tac n = n and i = n in eSum_mem [of "M"], assumption+)
 apply (simp add:Nset_def)
 apply (rule asubg_test, assumption+)
 apply (rule subsetI)
 apply (simp add:finitesum_def)
 apply (subgoal_tac "\<forall>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> x = e\<Sigma> M g n
  \<longrightarrow> x \<in> carrier M")
 apply blast
 apply (thin_tac "\<exists>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> x = e\<Sigma> M g n")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (frule finitesumbase_sub_carrier [of "R" "M" "f" "I"], assumption+)
 apply (frule_tac f = g and A = "Nset n" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)  apply simp
 apply (rule_tac n = n and i = n in eSum_mem [of "M"], assumption+)
 apply (simp add:Nset_def)
apply (frule finitesum_ex_one [of "R" "M" "f" "I"], assumption+)
apply (rule nonempty [of "0\<^sub>M" "finitesum M I f"], assumption+)
apply (rule ballI)+
 apply (rule finitesum_tOp_closed, assumption+)
 apply (rule finitesum_iOp_closed, assumption+)
apply (simp add:finitesum_def)
 apply (subgoal_tac "\<forall>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> m = e\<Sigma> M g n
  \<longrightarrow> (\<exists>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and>  a \<star>\<^sub>M m = e\<Sigma> M g n)")
 apply blast
 apply (thin_tac "\<exists>n g. g \<in> Nset n \<rightarrow> finitesum_base M I f \<and> m = e\<Sigma> M g n")
 apply (rule allI)+
 apply (rule impI) apply (erule conjE)
apply (simp add: finitesum_sprod)
 apply (subgoal_tac "(\<lambda>x.  a \<star>\<^sub>M (g x)) \<in> Nset n \<rightarrow> finitesum_base M I f")
 apply blast
apply (rule univar_func_test)
 apply (rule ballI)
 apply (frule_tac x = x in funcset_mem [of _ _ "finitesum_base M I f"],
                                                       assumption+)
 apply (simp add:finitesum_base_def)
 apply (subgoal_tac "\<forall>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> g x \<in> xa \<longrightarrow>
  (\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and>  a \<star>\<^sub>M (g x) \<in> xa)")
 apply blast
 apply (thin_tac "\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and> g x \<in> xa")
 apply (rule allI) apply (rule impI)
 apply (erule conjE)
apply (subgoal_tac "\<forall>i. xa = f i \<and> i \<in> I \<longrightarrow> (\<exists>xa. (\<exists>i. xa = f i \<and> i \<in> I) \<and>  a \<star>\<^sub>M (g x) \<in> xa)") apply blast
 apply (thin_tac "\<exists>i. xa = f i \<and> i \<in> I")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (frule_tac x = i in funcset_mem [of "f" "I"], assumption+)
 apply (simp add:CollectI) apply (simp add:submodule_def) apply (erule conjE)+
 apply (subgoal_tac "a \<star>\<^sub>M (g x) \<in> f i")
 apply blast
 apply simp
done

constdefs
 sSum ::"[('a, 'r, 'm1) ModuleType_scheme, 'a set, 'a set] \<Rightarrow> 'a set"
 "sSum M H1 H2 == {x. \<exists>h1\<in>H1. \<exists>h2\<in>H2. x = h1 +\<^sub>M h2}"

syntax
 "@SSUM":: "['a set, ('a, 'r, 'm1) ModuleType_scheme, 'a set] \<Rightarrow> 'a set"
             ("(3_/ \<plusminus>\<^sub>_/ _)" [60,60,61]60)

translations
 "H1 \<plusminus>\<^sub>M H2" == "sSum M H1 H2"

lemma sSum_cont_H:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                     H \<subseteq>  H \<plusminus>\<^sub>M K"
apply (rule subsetI)
apply (simp add:sSum_def)
apply (frule submodule_inc_0 [of "R" "M" "K"], assumption+)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (frule_tac t = x in ag_r_zero [THEN sym, of "M"])
apply (rule submodule_subset1, assumption+)
apply blast
done

lemma sSum_commute:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                       H \<plusminus>\<^sub>M K =  K \<plusminus>\<^sub>M H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (rule equalityI)
apply (rule subsetI) apply (simp add:sSum_def)
apply auto
apply (frule_tac h = h1 in submodule_subset1 [of "R" "M" "H"], assumption+)
apply (frule_tac h = h2 in submodule_subset1 [of "R" "M" "K"], assumption+)
apply (simplesubst ag_pOp_commute, assumption+)
apply blast
apply (simp add:sSum_def)
apply auto
apply (frule_tac h = h1 in submodule_subset1 [of "R" "M" "K"], assumption+)
apply (frule_tac h = h2 in submodule_subset1 [of "R" "M" "H"], assumption+)
apply (simplesubst ag_pOp_commute, assumption+)
apply blast
done

lemma Sum_of_SubmodulesTr:"\<lbrakk>ring R; R module M; submodule R M H1; submodule R M H2\<rbrakk> \<Longrightarrow>  g \<in> Nset n \<rightarrow> H1 \<union> H2 \<longrightarrow> e\<Sigma> M g n \<in> H1 \<plusminus>\<^sub>M H2"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (induct_tac n)
 apply (rule impI)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule funcset_mem [of "g" "Nset 0" "H1 \<union> H2" "0"], assumption+)
 apply (simp add:sSum_def)
 apply (case_tac "g 0 \<in> H1")
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule_tac c = "g 0" in subsetD [of "H1" "carrier M"], assumption+)
 apply (frule ag_r_zero [THEN sym, of "M" "g 0"], assumption+)
 apply (frule asubg_inc_zero [of "M" "H2"], assumption+)
 apply blast apply simp
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule_tac c = "g 0" in subsetD [of "H2" "carrier M"], assumption+)
 apply (frule ag_l_zero [THEN sym, of "M" "g 0"], assumption+)
 apply (frule asubg_inc_zero [of "M" "H1"], assumption+)
 apply blast apply (simp add:Nset_def)
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (simp add:sSum_def)
 apply auto apply (thin_tac "g \<in> Nset n \<rightarrow> H1 \<union> H2")
 apply (frule_tac f = g and A = "Nset (Suc n)" and x = "Suc n" in
                        funcset_mem)
 apply (simp add:Nset_def)
 apply simp
 apply (case_tac "g (Suc n) \<in> H1")
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule_tac c = h1 in subsetD [of "H1" "carrier M"], assumption+)
 apply (frule_tac c = "g (Suc n)" in subsetD [of "H1" "carrier M"],
                                                           assumption+)
 apply (frule_tac c = h2 in subsetD [of "H2" "carrier M"], assumption+)
 apply (simp add: ag_pOp_assoc)
 apply (frule_tac x = h2 and y = "g (Suc n)" in ag_pOp_commute [of "M"],
                                                           assumption+)
 apply (simp add: ag_pOp_assoc [symmetric])
 apply (frule_tac x = h1 and y = "g (Suc n)" in asubg_pOp_closed [of "M" "H1"], assumption+)
 apply blast apply simp
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (frule_tac c = h1 in subsetD [of "H1" "carrier M"], assumption+)
 apply (frule_tac c = h2 in subsetD [of "H2" "carrier M"], assumption+)
 apply (frule_tac c = "g (Suc n)" in subsetD [of "H2" "carrier M"],
                                                           assumption+)
 apply (simp add: ag_pOp_assoc)
 apply (frule_tac x = h2 and y = "g (Suc n)" in asubg_pOp_closed [of "M" "H2"], assumption+)
 apply blast
done

lemma sSum_two_Submodules:"\<lbrakk>ring R; R module M; submodule R M H1;
                         submodule R M H2\<rbrakk> \<Longrightarrow> submodule R M (H1 \<plusminus>\<^sub>M H2)"
apply (subgoal_tac "H1 \<plusminus>\<^sub>M H2 = finitesum M (Nset (Suc 0)) (\<lambda>x. (if x = 0 then H1 else if x = (Suc 0) then H2 else arbitrary))")
apply simp
apply (rule finitesum_subModule, assumption+)
apply (thin_tac "H1 \<plusminus>\<^sub>M H2 = finitesum M (Nset (Suc 0))
        (\<lambda>x. if x = 0 then H1 else if x = Suc 0 then H2 else arbitrary)")
apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:Nset_def)
apply (simp add:Nset_def) apply (subgoal_tac "0 \<le> Suc 0") apply blast
apply simp
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:sSum_def finitesum_def)
 apply (auto del:subsetI)
apply (subgoal_tac "(\<lambda>x. if x = 0 then h1 else if x = (Suc 0) then h2 else
       arbitrary) \<in> Nset (Suc 0) \<rightarrow> finitesum_base M (Nset (Suc 0))
 (\<lambda>x. if x = 0 then H1 else if x = Suc 0 then H2 else arbitrary) \<and>
  h1 +\<^sub>M h2 = e\<Sigma> M (\<lambda>x. if x = 0 then h1 else if x = (Suc 0) then h2 else
       arbitrary) (Suc 0)")
apply blast
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "x = 0") apply simp
 apply (simp add:finitesum_base_def)
 apply blast
apply (subgoal_tac "x = Suc 0") apply (simp add:finitesum_base_def)
 apply blast
 apply (simp add:Nset_def)
apply simp
apply (simp add:finitesum_def) apply (rule subsetI)
 apply (simp add:CollectI)
 apply auto
 apply (simp add:finitesum_base_def)
 apply (subgoal_tac "\<Union>{if i = 0 then H1 else if i = Suc 0 then H2 else
 arbitrary | i. i \<in> Nset (Suc 0)} = H1 \<union> H2")
 apply (simp add:Sum_of_SubmodulesTr)
apply (thin_tac "g \<in> Nset n \<rightarrow> \<Union>{if i = 0 then H1
            else if i = Suc 0 then H2 else arbitrary | i. i \<in> Nset (Suc 0)}")
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>xa. (\<exists>i. xa = (if i = 0 then H1
   else if i = Suc 0 then H2 else arbitrary) \<and> i \<in> Nset (Suc 0)) \<and> x \<in> xa \<longrightarrow>
    x \<in> H1 \<or> x \<in> H2")
 apply blast
 apply (thin_tac "\<exists>xa. (\<exists>i. xa = (if i = 0 then H1
   else if i = Suc 0 then H2 else arbitrary) \<and> i \<in> Nset (Suc 0)) \<and> x \<in> xa")
 apply (rule allI)
 apply (rule impI)
 apply (erule conjE)+
 apply (subgoal_tac "\<forall>i. xa =
  (if i = 0 then H1 else if i = Suc 0 then H2 else arbitrary) \<and>
  i \<in> Nset (Suc 0) \<longrightarrow> x \<in> H1 \<or> x \<in> H2") apply blast
 apply (thin_tac "\<exists>i. xa =
              (if i = 0 then H1 else if i = Suc 0 then H2 else arbitrary) \<and>
              i \<in> Nset (Suc 0)")
 apply (rule allI) apply (rule impI)
 apply (erule conjE)+
 apply (case_tac "i = Suc 0") apply simp apply (frule Nset_pre, assumption+)
 apply (simp add:Nset_def)
apply (rule subsetI)
 apply (simp add:CollectI Nset_def)
 apply blast
done

constdefs
 iotam::"[('a, 'r, 'm) ModuleType_scheme, 'a set, 'a set] \<Rightarrow> ('a \<Rightarrow> 'a)"
      ("(3\<iota>m\<^sub>_ \<^sub>_\<^sub>,\<^sub>_)" [82, 82, 83]82)
 "\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K == \<lambda>x\<in>H. (x +\<^sub>M (0\<^sub>M))"  (** later we define miota. This is not
 equal to iotam **)

lemma iotam_mHom:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk>
                           \<Longrightarrow> \<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K \<in> mHom R (mdl M H) (mdl M (H \<plusminus>\<^sub>M K))"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (simp add:mdl_def)
 apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:iotam_def sSum_def)
 apply (frule submodule_inc_0 [of "R" "M" "K"], assumption+)
 apply blast
apply (rule conjI)
 apply (simp add:iotam_def extensional_def mdl_def)
apply (rule ballI)+
 apply (simp add:mdl_def iotam_def)
 apply (frule_tac h = a and k = b in submodule_pOp_closed [of "R" "M" "H"],
                                                      assumption+)
 apply simp
 apply (frule_tac h = a in submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (frule_tac h = b in submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (frule_tac h = "a +\<^sub>M b" in submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:ag_r_zero)
apply (rule ballI)+
 apply (simp add:mdl_def iotam_def)
 apply (simp add:submodule_sprod_closed)
 apply (frule_tac a = a and h = m in submodule_sprod_closed [of "R" "M" "H"],
                                                        assumption+)
 apply (frule_tac h = m in submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_r_zero, assumption+)
 apply (frule_tac h = "a \<star>\<^sub>M m" in submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (subst ag_r_zero, assumption+)
 apply simp
done

lemma mhomom3Tr:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                         submodule R (mdl M (H \<plusminus>\<^sub>M K)) K"
apply (subst submodule_def)
apply (rule conjI)
 apply (simp add:mdl_def)
 apply (subst sSum_commute, assumption+)
 apply (simp add:sSum_cont_H)
apply (rule conjI)
 apply (rule asubg_test)
 apply (frule sSum_two_Submodules [of "R" "M" "H" "K"], assumption+)
 apply (frule mdl_is_module [of "R" "M" "(H \<plusminus>\<^sub>M K)"], assumption+)
 apply (rule module_is_ag, assumption+)
apply (simp add:mdl_def)
 apply (subst sSum_commute, assumption+)
  apply (simp add:sSum_cont_H)
 apply (frule submodule_inc_0 [of "R" "M" "K"], assumption+)
 apply (simp add:nonempty)
apply (rule ballI)+
 apply (simp add:mdl_def)
 apply (rule submodule_pOp_closed, assumption+)
 apply (rule submodule_mOp_closed, assumption+)
apply (rule ballI)+
 apply (simp add:mdl_def)
 apply (simp add:submodule_sprod_closed)
done

lemma mhomom3Tr0:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk>
     \<Longrightarrow> compos (mdl M H) (mpj (mdl M (H \<plusminus>\<^sub>M K)) K) (\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K)
        \<in> mHom R (mdl M H) (mdl M (H \<plusminus>\<^sub>M K) /\<^sub>m K)"
apply (frule mdl_is_module [of "R" "M" "H"], assumption+)
apply (frule mhomom3Tr[of "R" "M" "H" "K"], assumption+)
apply (frule mdl_is_module [of "R" "M" "H \<plusminus>\<^sub>M K"], assumption+)
apply (frule sSum_two_Submodules [of "R" "M" "H" "K"], assumption+)
apply (frule iotam_mHom [of "R" "M" "H" "K"], assumption+)
apply (frule mpj_mHom [of "R" "mdl M (H \<plusminus>\<^sub>M K)" "K"], assumption+)
apply (rule mHom_compos [of "R" "mdl M H" "mdl M (H \<plusminus>\<^sub>M K)"], assumption+)
apply (simp add:qmodule_module) apply assumption
apply (simp add:mpj_mHom)
done

lemma mhomom3Tr1:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
  surjec\<^sub>(mdl M H)\<^sub>,\<^sub>((mdl M (H \<plusminus>\<^sub>M K)) /\<^sub>m K)
    (compos (mdl M H) (mpj (mdl M (H \<plusminus>\<^sub>M K)) K) (\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K))"
apply (simp add:surjec_def)
apply (frule mhomom3Tr0 [of "R" "M" "H" "K"], assumption+)
apply (rule conjI)
apply (simp add:mHom_def)
apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
apply (rule ballI)
 apply (simp add:compos_def compose_def)
 apply (thin_tac "(\<lambda>x\<in>carrier (mdl M H). mpj (mdl M (H \<plusminus>\<^sub>M K)) K ((\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K) x))
           \<in> mHom R (mdl M H) (mdl M (H \<plusminus>\<^sub>M K) /\<^sub>m K)")
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply auto
 apply (simp add:mdl_def) apply (fold mdl_def)
 apply (subgoal_tac "\<exists>h\<in>H. \<exists>k\<in>K. a = h +\<^sub>M k")
 apply (subgoal_tac "\<forall>h\<in>H. \<forall>k\<in>K. a = h +\<^sub>M k \<longrightarrow> (\<exists>aa\<in>H.
              mpj (mdl M (H \<plusminus>\<^sub>M K)) K ((\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K) aa) = a \<uplus>\<^sub>(mdl M (H \<plusminus>\<^sub>M K)) K)")
 apply blast apply (thin_tac "\<exists>h\<in>H. \<exists>k\<in>K. a =  h +\<^sub>M k")
 apply (rule ballI)+ apply (rule impI) apply simp
 apply (subgoal_tac "(h +\<^sub>M k) \<uplus>\<^sub>(mdl M (H \<plusminus>\<^sub>M K)) K = h \<uplus>\<^sub>(mdl M (H \<plusminus>\<^sub>M K)) K")
 apply simp
 apply (simp add:iotam_def)
 apply (simp add:mpj_def)
 apply (subgoal_tac "\<forall>k. k\<in>H \<longrightarrow> k +\<^sub>M 0\<^sub>M \<in> carrier (mdl M ((H \<plusminus>\<^sub>M K)))")
 apply simp
 apply (subgoal_tac "\<forall>k. k\<in>H \<longrightarrow> k +\<^sub>M 0\<^sub>M = k") apply simp
 apply blast
 apply (rule allI) apply (rule impI)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_r_zero, assumption+) apply (simp add:submodule_def)
 apply (erule conjE)+ apply (simp add:subsetD)
 apply (rule allI) apply (rule impI) apply (simp add:mdl_def)
 apply (fold mdl_def) apply (simp add:sSum_def)
 apply (frule submodule_inc_0 [of "R" "M" "K"], assumption+)
 apply blast
 apply (subgoal_tac "R module mdl M (H \<plusminus>\<^sub>M K)")
 apply (frule_tac m = h and h = k in mr_cos_h_stable1 [of "R" "mdl M (H \<plusminus>\<^sub>M K)" "K"], assumption+)
 apply (simp add:mhomom3Tr)
 apply (simp add:mdl_def) apply (fold mdl_def)
 apply (frule sSum_cont_H [of "R" "M" "H" "K"], assumption+)
 apply (simp add:subsetD) apply assumption
 apply (simp add:mdl_def)
apply (frule sSum_two_Submodules [of "R" "M" "H" "K"], assumption+)
 apply (simp add: mdl_is_module)
 apply (simp add:sSum_def)
done

lemma mhomom3Tr2:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
  ker\<^sub>(mdl M H)\<^sub>,\<^sub>((mdl M (H \<plusminus>\<^sub>M K)) /\<^sub>m K)
    (compos (mdl M H) (mpj (mdl M (H \<plusminus>\<^sub>M K)) K) (\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K)) = H \<inter> K"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def) apply (erule conjE)
 apply (simp add:qmodule_def)
 apply (simp add:mdl_carrier)
 apply (simp add:compos_def compose_def mdl_def iotam_def)
 apply (fold mdl_def)
apply (subgoal_tac "x +\<^sub>M 0\<^sub>M \<in> carrier (mdl M (H \<plusminus>\<^sub>M K))")
apply (simp add:iotam_def mpj_def)
apply (frule sSum_two_Submodules[of "R" "M" "H" "K"], assumption+)
apply (frule mdl_is_module [of "R" "M" "H \<plusminus>\<^sub>M K"], assumption+)
apply (frule_tac m = "x +\<^sub>M 0\<^sub>M" in m_in_mr_coset [of "R" "mdl M (H \<plusminus>\<^sub>M K)" "K"],
                          assumption+)
 apply (simp add:mhomom3Tr)
 apply (simp add:mdl_carrier [of "R" "M" "H \<plusminus>\<^sub>M K"])
 apply simp
 apply (frule_tac h = x in submodule_subset1 [of "R" "M" "H"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:ag_r_zero)
 apply (frule mdl_is_module [of "R" "M" "H \<plusminus>\<^sub>M K"], assumption+)
 apply (simp add:sSum_two_Submodules[of "R" "M" "H" "K"])
 apply (simp add:mdl_def) apply (fold mdl_def)
 apply (frule submodule_inc_0 [of "R" "M" "K"], assumption+)
 apply (simp add:sSum_def) apply blast
apply (rule subsetI)
 apply (simp add:ker_def)
 apply (simp add:mdl_carrier)
 apply (simp add:qmodule_def)
 apply (simp add:compos_def compose_def)
 apply (subst mdl_carrier, assumption+) apply simp
 apply (erule conjE)+
apply (simp add:iotam_def mpj_def)
 apply (frule sSum_two_Submodules[of "R" "M" "H" "K"], assumption+)
 apply (simp add: mdl_carrier)
 apply (subgoal_tac "x +\<^sub>M 0\<^sub>M \<in> H \<plusminus>\<^sub>M K") apply simp
 apply (frule mdl_is_module [of "R" "M" "H \<plusminus>\<^sub>M K"], assumption+)
 apply (subgoal_tac "x +\<^sub>M 0\<^sub>M = x") apply simp
 apply (frule_tac h1 = x in mr_cos_h_stable [THEN sym, of "R" "mdl M (H \<plusminus>\<^sub>M K)"
  "K"], assumption+)
 apply (simp add:mhomom3Tr) apply assumption+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_r_zero, assumption+)
 apply (simp add:submodule_def[of "R" "M" "H"]) apply (erule conjE)+
 apply (simp add:subsetD) apply simp
 apply (frule_tac submodule_inc_0 [of "R" "M" "K"], assumption+)
apply (simp add:sSum_def) apply blast
done

lemma mhomom_3:"\<lbrakk>ring R; R module M; submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                 (mdl M H) /\<^sub>m (H \<inter> K) \<cong>\<^sub>R (mdl M (H \<plusminus>\<^sub>M K)) /\<^sub>m K"
apply (frule sSum_two_Submodules [of "R" "M" "H" "K"], assumption+)
 apply (frule mdl_is_module [of "R" "M" "H"], assumption+)
 apply (frule mdl_is_module [of "R" "M" "K"], assumption+)
 apply (frule mdl_is_module [of "R" "M" "H \<plusminus>\<^sub>M K"], assumption+)
 apply (frule mhomom3Tr [of "R" "M" "H" "K"], assumption+)
 apply (frule qmodule_module [of "R" "mdl M (H \<plusminus>\<^sub>M K)" "K"], assumption+)
apply (simp add:misomorphic_def)
apply (frule mhomom3Tr [of "R" "M" "H" "K"], assumption+)
apply (frule qmodule_module [of "R" "mdl M (H \<plusminus>\<^sub>M K)" "K"], assumption+)
apply (frule mhomom3Tr0 [of "R" "M" "H" "K"], assumption+)
apply (frule indmhom [of "R" "mdl M H" "mdl M (H \<plusminus>\<^sub>M K) /\<^sub>m K" "compos (mdl M H) (mpj (mdl M (H \<plusminus>\<^sub>M K)) K) (\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K)"], assumption+)
apply (subgoal_tac "bijec\<^sub>((mdl M H) /\<^sub>m (H \<inter> K))\<^sub>,\<^sub>((mdl M (H \<plusminus>\<^sub>M K)) /\<^sub>m K) (indmhom R (mdl M H) ((mdl M (H \<plusminus>\<^sub>M K)) /\<^sub>m K) (compos (mdl M H) (mpj (mdl M (H \<plusminus>\<^sub>M K)) K) (\<iota>m\<^sub>M \<^sub>H\<^sub>,\<^sub>K)))")
apply (simp add:mhomom3Tr2[THEN sym])
apply blast
apply (simp add:bijec_def)
 apply (simp add:mhomom3Tr2[THEN sym])
apply (rule conjI)
 apply (rule indmhom_injec, assumption+)
 apply (rule indmhom_surjec1, assumption+)
 apply (simp add: mhomom3Tr1)
 apply assumption
done

constdefs
linear_combination::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, nat] \<Rightarrow> (nat \<Rightarrow> 'r) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
 "linear_combination R M n s m == eSum M (\<lambda>j. (s j) \<star>\<^sub>M (m j)) n"

linear_span::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, 'r set, 'a set] \<Rightarrow> 'a set"
 "linear_span R M A H == if H = {} then {0\<^sub>M} else {x. \<exists>n. \<exists>f \<in> Nset n \<rightarrow> H.
 \<exists>s\<in>Nset n \<rightarrow> A.  x = linear_combination R M n s f}"

coefficient::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,
nat, nat \<Rightarrow> 'r, nat \<Rightarrow> 'a] \<Rightarrow> nat \<Rightarrow> 'r"

"coefficient R M n s m j == s j"

body::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,
nat, nat \<Rightarrow> 'r, nat \<Rightarrow> 'a] \<Rightarrow> nat \<Rightarrow> 'a"

"body R M n s m j == m j"

lemma linear_comb_eqTr:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow> s \<in> Nset n \<rightarrow> carrier R \<and> f \<in> Nset n \<rightarrow> H \<and> g \<in> Nset n \<rightarrow> H \<and> (\<forall>j\<in>Nset n. f j = g j) \<longrightarrow>
linear_combination R M n s f = linear_combination R M n s g"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+ apply (simp add:linear_combination_def)
 apply (simp add:Nset_def)
apply (rule impI) apply (erule conjE)+
apply (subgoal_tac "\<forall>j. j \<in> Nset n \<longrightarrow> j \<in> Nset (Suc n)")
 apply (frule_tac f = s in func_pre)
 apply (frule_tac f = f in func_pre)
 apply (frule_tac f = g in func_pre)
apply (subgoal_tac "linear_combination R M n s f = linear_combination R M n s g") prefer 2 apply simp
 apply (thin_tac "s \<in> Nset n \<rightarrow> carrier R \<and> f \<in> Nset n \<rightarrow> H \<and> g \<in> Nset n \<rightarrow> H \<and> (\<forall>j\<in>Nset n. f j = g j) \<longrightarrow> linear_combination R M n s f = linear_combination R M n s g")
 apply (thin_tac "\<forall>j. j \<in> Nset n \<longrightarrow> j \<in> Nset (Suc n)")
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "f (Suc n) = g (Suc n)") apply simp
 apply (simp add:Nset_def)+
done

lemma linear_comb_eq:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; s \<in> Nset n \<rightarrow> carrier R; f \<in> Nset n \<rightarrow> H; g \<in> Nset n \<rightarrow> H; \<forall>j\<in>Nset n. f j = g j\<rbrakk> \<Longrightarrow>
linear_combination R M n s f = linear_combination R M n s g"
apply (simp add:linear_comb_eqTr)
done

lemma linear_comb0_1Tr:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
 s \<in> Nset n \<rightarrow> {0\<^sub>R} \<and>  m \<in> Nset n \<rightarrow> H \<longrightarrow> linear_combination R M n s m = 0\<^sub>M"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (subgoal_tac "s 0 = 0\<^sub>R") apply simp
 apply (rule sprod_0_m, assumption+)
 apply (simp add:funcset_mem subsetD)
 apply (frule funcset_mem [of "s" "Nset 0" "{0\<^sub>R}" "0"], assumption+)
 apply simp apply (simp add:Nset_def)
apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "{0\<^sub>R}"])
 apply (frule func_pre [of _ _ "H"])
 apply (subgoal_tac "linear_combination R M n s m = 0\<^sub>M")
 apply (thin_tac  "s \<in> Nset n \<rightarrow> {0\<^sub>R} \<and> m \<in> Nset n \<rightarrow> H \<longrightarrow>
           linear_combination R M n s m = 0\<^sub>M")
 prefer 2 apply simp
 apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_l_zero, assumption+)
 apply (rule sprod_mem, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac A = "Nset (Suc n)" and x = "Suc n" in funcset_mem [of "s" _ "{0\<^sub>R}" _], assumption+) apply simp apply (simp add:ring_zero)
 apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac A = "Nset (Suc n)" and x = "Suc n" in funcset_mem [of "s" _ "{0\<^sub>R}" _], assumption+) apply simp
 apply (rule sprod_0_m, assumption+)
 apply (simp add:funcset_mem subsetD)
 apply (simp add:Nset_def)
done

lemma linear_comb0_1:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; s \<in> Nset n \<rightarrow> {0\<^sub>R}; m \<in> Nset n \<rightarrow> H \<rbrakk> \<Longrightarrow> linear_combination R M n s m = 0\<^sub>M"
apply (simp add:linear_comb0_1Tr)
done

lemma linear_comb0_2Tr:"\<lbrakk>ring R; R module M; ideal R A\<rbrakk> \<Longrightarrow>
 s \<in> Nset n \<rightarrow> A \<and>  m \<in> Nset n \<rightarrow> {0\<^sub>M} \<longrightarrow> linear_combination R M n s m = 0\<^sub>M"
apply (induct_tac n )
 apply (rule impI) apply (erule conjE)
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule funcset_mem [of "m" "Nset 0" "{0\<^sub>M}" "0"], assumption+)
 apply simp
 apply (rule sprod_a_0, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:Nset_def)
apply (rule impI)
 apply (erule conjE)+
 apply (frule func_pre [of "s"])
 apply (frule func_pre [of "m"])
 apply (subgoal_tac "linear_combination R M n s m = 0\<^sub>M")
 prefer 2 apply simp
 apply (thin_tac " s \<in> Nset n \<rightarrow> A \<and> m \<in> Nset n \<rightarrow> {0\<^sub>M} \<longrightarrow>
           linear_combination R M n s m = 0\<^sub>M")
 apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (subst ag_l_zero, assumption+)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
apply (frule_tac A = "Nset (Suc n)" and x = "Suc n" in funcset_mem [of "m" _ "{0\<^sub>M}" ], assumption+)
 apply simp apply (simp add:module_inc_zero)
 apply (frule_tac A = "Nset (Suc n)" and x = "Suc n" in funcset_mem [of "m" _ "{0\<^sub>M}" ], assumption+) apply simp
 apply (rule sprod_a_0, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:Nset_def)
done

lemma linear_comb0_2:"\<lbrakk>ring R; R module M; ideal R A;  s \<in> Nset n \<rightarrow> A;
m \<in> Nset n \<rightarrow> {0\<^sub>M} \<rbrakk> \<Longrightarrow>  linear_combination R M n s m = 0\<^sub>M"
apply (simp add:linear_comb0_2Tr)
done

lemma liear_comb_memTr:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
 \<forall>s. \<forall>m. s \<in> Nset n \<rightarrow> A \<and> m \<in> Nset n \<rightarrow> H \<longrightarrow> linear_combination R M n s m \<in> carrier M"
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (simp add:linear_combination_def Nset_def)
 apply (rule sprod_mem [of "R" "M"], assumption+)
 apply (subgoal_tac "(0::nat) \<in> {0}")
 apply (simp add:funcset_mem ideal_subset subsetD) apply simp
 apply (simp add:funcset_mem ideal_subset subsetD)
apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"])
 apply (frule func_pre [of _ _ "H"])
 apply (subgoal_tac "linear_combination R M n s m \<in> carrier M")
 prefer 2 apply simp
 apply (thin_tac "\<forall>s m. s \<in> Nset n \<rightarrow> A \<and> m \<in> Nset n \<rightarrow> H \<longrightarrow>
                linear_combination R M n s m \<in> carrier M")
apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_pOp_closed, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset subsetD)
 apply (simp add:funcset_mem subsetD)
 apply (simp add:Nset_def)
done

lemma linear_combination_mem:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M;
 s \<in> Nset n \<rightarrow> A; m \<in> Nset n \<rightarrow> H\<rbrakk> \<Longrightarrow> linear_combination R M n s m \<in> carrier M"
apply (simp add:liear_comb_memTr)
done

lemma elem_linear_span:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M; a \<in> A;
 h \<in> H\<rbrakk> \<Longrightarrow> a \<star>\<^sub>M h \<in> linear_span R M A H"
apply (simp add:linear_span_def)
 apply (simp add:nonempty)
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "(\<lambda>k\<in>Nset 0. a) \<in> Nset 0 \<rightarrow> A")
 apply (subgoal_tac "(\<lambda>k\<in>Nset 0. h) \<in> Nset 0 \<rightarrow> H")
 apply (subgoal_tac "a \<star>\<^sub>M h =
         e\<Sigma> M (\<lambda>j. (\<lambda>k\<in>Nset 0. a) j \<star>\<^sub>M ((\<lambda>k\<in>Nset 0. h) j)) 0")
 apply blast
 apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
done

lemma elem_linear_span1:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow> H \<subseteq> linear_span R M (carrier R) H"
apply (rule subsetI)
apply (frule_tac R = R and M = M and A = "carrier R" and H = H and a = "1\<^sub>R" and h = x in elem_linear_span, assumption+)
 apply (simp add:whole_ideal)
 apply assumption+
 apply (simp add:ring_one)
 apply assumption+
 apply (frule_tac A = H and B = "carrier M" and c = x in subsetD, assumption+)
 apply (simp add:sprod_one)
done

lemma linear_span_inc_0:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M\<rbrakk>
  \<Longrightarrow> 0\<^sub>M \<in> linear_span R M A H"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (subgoal_tac "\<exists>h. h \<in> H") prefer 2 apply blast
 apply (subgoal_tac "\<forall>h. h \<in> H \<longrightarrow>  0\<^sub>M \<in> linear_span R M A H")
 apply blast apply (thin_tac "\<exists>h. h \<in> H")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "(\<lambda>j\<in>Nset 0. 0\<^sub>R) \<in> Nset 0 \<rightarrow> A")
 apply (subgoal_tac "(\<lambda>j\<in>Nset 0. h) \<in> Nset 0 \<rightarrow> H")
 apply (subgoal_tac "0\<^sub>M = linear_combination R M 0 (\<lambda>j\<in>Nset 0. 0\<^sub>R) (\<lambda>j\<in>Nset 0. h)")
 apply (simp add:linear_span_def) apply blast
apply (simp add:linear_combination_def Nset_def)
 apply (rule sprod_0_m[THEN sym], assumption+) apply (simp add:subsetD)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:ideal_zero)
done

lemma linear_span_iOp_closedTr1:"\<lbrakk>ring R; ideal R A; s \<in> Nset n \<rightarrow> A\<rbrakk>
    \<Longrightarrow> (\<lambda>x\<in>Nset n. -\<^sub>R (s x)) \<in> Nset n \<rightarrow> A"
apply (rule univar_func_test) apply (rule ballI)
 apply simp
 apply (rule ideal_inv1_closed, assumption+)
 apply (simp add:funcset_mem)
done

lemma linear_span_iOp_closedTr2:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M; f \<in> Nset n \<rightarrow> H; s \<in> Nset n \<rightarrow> A\<rbrakk>  \<Longrightarrow> -\<^sub>M (linear_combination R M n s f) = linear_combination R M n (\<lambda>x\<in>Nset n. -\<^sub>R (s x)) f"
apply (subgoal_tac "H \<noteq> {}") prefer 2
 apply (subgoal_tac "0 \<in> Nset n")
 apply (frule_tac f = f and A = "Nset n" and B = H and x = 0 in funcset_mem,
                                       assumption+)
 apply (simp add:nonempty) apply (simp add:Nset_def)
apply (frule_tac R = R and A = A and s = s in linear_span_iOp_closedTr1, assumption+)
apply (subgoal_tac "-\<^sub>M (linear_combination R M n s f) = linear_combination R M n (\<lambda>x\<in>Nset n. -\<^sub>R (s x)) f")
apply blast
 apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst eSum_minus, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem[of "R" "M"], assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (rule ag_mOp_closed, assumption+)
 apply (rule sprod_mem[of "R" "M"], assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (rule sprod_mem, assumption+)
 apply (frule ring_is_ag)
 apply (rule ag_mOp_closed [of "R"], assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
apply (rule ballI)
 apply simp
 apply (rule sprod_minus_am1, assumption+)
 apply (rule funcset_mem ideal_subset, assumption+)
 apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
done


lemma linear_span_iOp_closed:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M;
 a \<in> linear_span R M A H\<rbrakk> \<Longrightarrow> -\<^sub>M a \<in> linear_span R M A H"
apply (case_tac "H = {}")
apply (simp add:linear_span_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (simp add:ag_minus_0_eq_0)
apply (simp add:linear_span_def)
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A. a = linear_combination R M n s f \<longrightarrow>(\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A. -\<^sub>M a = linear_combination R M n s f)")
apply blast
apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A. a = linear_combination R M n s f")
apply(rule allI) apply (rule ballI)+ apply (rule impI) apply simp
apply (frule_tac R = R and A = A and s = s and n = n in linear_span_iOp_closedTr1,
             assumption+)
apply (frule_tac R = R and M = M and A = A and H = H and f = f and s = s in linear_span_iOp_closedTr2, assumption+)
apply blast
done

lemma linear_span_tOp_closed:
 "\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M; a \<in> linear_span R M A H;
  b \<in> linear_span R M A H\<rbrakk> \<Longrightarrow> a +\<^sub>M b \<in> linear_span R M A H"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (frule module_is_ag, assumption+)
 apply (frule ag_inc_zero)
 apply (simp add:ag_r_zero)
apply (simp add:linear_span_def)
apply (subgoal_tac "\<forall>i j. \<forall>f \<in> Nset i \<rightarrow> H. \<forall>s\<in>Nset i \<rightarrow> A. \<forall>g\<in> Nset j \<rightarrow>  H. \<forall>t\<in>Nset j \<rightarrow> A.  a = linear_combination R M i s f \<and>  b = linear_combination R M j t g \<longrightarrow> (\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A.  a +\<^sub>M b = linear_combination R M n s f)")
apply blast
apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A.
                                  a = linear_combination R M n s f")
apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A.
                                  b = linear_combination R M n s f")
apply (rule allI)+ apply (rule ballI)+ apply (rule impI)
apply (erule conjE) apply simp
 apply (thin_tac "a = linear_combination R M i s f")
 apply (thin_tac "b = linear_combination R M j t g")
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "jointfun i f j g \<in> Nset (Suc (i + j)) \<rightarrow> H")
 apply (subgoal_tac "jointfun i s j t \<in> Nset (Suc (i + j)) \<rightarrow> A")
apply (subgoal_tac "e\<Sigma> M (\<lambda>k.  s k \<star>\<^sub>M (f k)) i +\<^sub>M (e\<Sigma> M (\<lambda>l.  t l \<star>\<^sub>M (g l)) j)
 = e\<Sigma> M (\<lambda>u. (jointfun i s j t) u \<star>\<^sub>M ((jointfun i f j g) u)) (Suc (i + j))")
apply (simp del:eSum_Suc)
apply (thin_tac "e\<Sigma> M (\<lambda>k. (s k) \<star>\<^sub>M (f k)) i +\<^sub>M (e\<Sigma> M (\<lambda>l. (t l) \<star>\<^sub>M (g l)) j )
 = e\<Sigma> M (\<lambda>u. (jointfun i s j t u) \<star>\<^sub>M (jointfun i f j g u)) (Suc (i + j))")
apply blast
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst eSum_split, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>k.  s k \<star>\<^sub>M (f k)) i =
            e\<Sigma> M (\<lambda>u.  jointfun i s j t u \<star>\<^sub>M (jointfun i f j g u)) i")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>l.  t l \<star>\<^sub>M (g l)) j =  e\<Sigma> M (cmp
 (\<lambda>u. jointfun i s j t u \<star>\<^sub>M (jointfun i f j g u)) (slide (Suc i))) j")
 apply simp
apply (thin_tac "e\<Sigma> M (\<lambda>k.  s k \<star>\<^sub>M (f k)) i =
            e\<Sigma> M (\<lambda>u.  jointfun i s j t u \<star>\<^sub>M (jointfun i f j g u)) i")
apply (simp add:cmp_def jointfun_def slide_def sliden_def)
apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:jointfun_def Nset_def)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (rule ballI)
 apply (simp add:jointfun_def Nset_def)
 apply (frule_tac f = s and n = i and A = A and g = t and m = j and B = A in jointfun_hom, assumption+) apply simp
 apply (frule_tac f = f and n = i and A = H and g = g and m = j and B = H in jointfun_hom, assumption+) apply simp
done

lemma linear_span_sprodTr:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M;
 r \<in> carrier R; H \<noteq> {}\<rbrakk>  \<Longrightarrow> s \<in> Nset n \<rightarrow> A \<and> g \<in> Nset n \<rightarrow>  H
  \<longrightarrow> r \<star>\<^sub>M (eSum M (\<lambda>k. (s k) \<star>\<^sub>M (g k))  n) =
                                   eSum M (\<lambda>k. r \<star>\<^sub>M ((s k) \<star>\<^sub>M (g k))) n"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+  apply (simp add:Nset_def)
apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"]) apply (frule func_pre [of _ _ "H"])
 apply (subgoal_tac "r \<star>\<^sub>M (e\<Sigma> M (\<lambda>k.  s k \<star>\<^sub>M (g k)) n) =
           e\<Sigma> M (\<lambda>k.  r \<star>\<^sub>M ( s k \<star>\<^sub>M (g k))) n")
 prefer 2 apply simp
 apply (thin_tac "s \<in> Nset n \<rightarrow> A \<and> g \<in> Nset n \<rightarrow> H \<longrightarrow>
 r \<star>\<^sub>M (e\<Sigma> M (\<lambda>k.  s k \<star>\<^sub>M (g k)) n) = e\<Sigma> M (\<lambda>k.  r \<star>\<^sub>M ( s k \<star>\<^sub>M (g k))) n")
 apply simp
 apply (subst sprod_distrib2, assumption+)
 apply (frule_tac s = s and m = g and n = n in linear_combination_mem[of "R" "M" "A" "H"]
, assumption+)
 apply (simp add:linear_combination_def)
 apply (rule sprod_mem, assumption+)+
  apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (simp add:Nset_def funcset_mem subsetD)
 apply simp
done


lemma linear_span_sprod:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M;
 r \<in> carrier R; s \<in> Nset n \<rightarrow> A;  g \<in> Nset n \<rightarrow>  H \<rbrakk> \<Longrightarrow>
r \<star>\<^sub>M (eSum M (\<lambda>k. (s k) \<star>\<^sub>M (g k)) n) =  eSum M (\<lambda>k. r \<star>\<^sub>M ((s k) \<star>\<^sub>M (g k))) n"
apply (case_tac "H \<noteq> {}")
 apply (simp add:linear_span_sprodTr)
 apply (subgoal_tac "0 \<in> Nset n") prefer 2 apply (simp add:Nset_def)
 apply (simp add:Pi_def)
done

lemma linear_span_sprod_closed:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M;
 r \<in> carrier R; x \<in> linear_span R M A H\<rbrakk> \<Longrightarrow> r \<star>\<^sub>M x \<in> linear_span R M A H"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (simp add:sprod_a_0)
apply (simp add:linear_span_def)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f \<longrightarrow> (\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A.  r \<star>\<^sub>M x = linear_combination R M n s f )")
 apply blast
 apply (rule allI)
 apply (rule ballI)+ apply (rule impI) apply simp
 apply (thin_tac "x = linear_combination R M n s f")
 apply (simp add:linear_combination_def)
 apply (simp add: linear_span_sprod)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>k.  r \<star>\<^sub>M ( s k \<star>\<^sub>M (f k))) n =
                        e\<Sigma> M (\<lambda>k. (r \<cdot>\<^sub>R  (s k)) \<star>\<^sub>M (f k)) n")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>k.  r \<star>\<^sub>M ( s k \<star>\<^sub>M (f k))) n
                        = e\<Sigma> M (\<lambda>k.  r \<cdot>\<^sub>R (s k) \<star>\<^sub>M (f k)) n")
 apply (subgoal_tac "(\<lambda>k\<in>Nset n. (r \<cdot>\<^sub>R (s k))) \<in> Nset n \<rightarrow> A")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>k. r \<cdot>\<^sub>R (s k) \<star>\<^sub>M (f k)) n =
                      e\<Sigma> M (\<lambda>j. (\<lambda>k\<in>Nset n.  r \<cdot>\<^sub>R (s k)) j \<star>\<^sub>M (f j)) n")
 apply blast
apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI)
 apply simp
 apply (rule sprod_mem, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
apply (rule ballI) apply simp
apply (rule univar_func_test)
 apply (rule ballI)
 apply simp
 apply (simp add:funcset_mem ideal_ring_multiple)
apply (rule eSum_eq)
 apply (simp add:module_is_ag)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (rule sprod_mem, assumption+)+
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (rule sprod_mem, assumption+)+
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
apply (rule ballI)
 apply (rule sprod_assoc [THEN sym], assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
done

lemma linear_span_subModule:"\<lbrakk>ring R; R module M; ideal R A; H \<subseteq> carrier M\<rbrakk>  \<Longrightarrow> submodule R M (linear_span R M A H)"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (simp add:submodule_0)
apply (simp add:submodule_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (rule conjI)
 apply (simp add:linear_span_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f \<longrightarrow> (x \<in> carrier M)")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_mem)
apply (rule conjI)
 apply (rule asubg_test) apply (simp add:module_is_ag)
 apply (rule subsetI) apply (simp add:linear_span_def)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f \<longrightarrow> (x \<in> carrier M)")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_mem)
 apply (frule linear_span_inc_0, assumption+) apply (simp add:nonempty)
 apply (rule ballI)+
 apply (rule linear_span_tOp_closed, assumption+)
 apply (rule linear_span_iOp_closed, assumption+)
apply (rule ballI)+
 apply (simp add:linear_span_sprod_closed)
done

constdefs
 smodule_ideal_coeff::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,
       'r set] \<Rightarrow> 'a set"
 "smodule_ideal_coeff R M A == linear_span R M A (carrier M)"

syntax
 "@SMLIDEALCOEFF" ::"['r set, ('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme] \<Rightarrow> 'a set" ("(3_/ \<odot>\<^sub>_/ _)" [64,64,65]64)

translations
 "A \<odot>\<^sub>R M" == "smodule_ideal_coeff R M A"

lemma smodule_ideal_coeff_is_Submodule:"\<lbrakk>ring R; R module M; ideal R A \<rbrakk> \<Longrightarrow>
           submodule R M (A \<odot>\<^sub>R M)"
apply (simp add:smodule_ideal_coeff_def)
apply (simp add:linear_span_subModule)
done

constdefs
 quotient_of_submodules::"[('r, 'm) RingType_scheme,
 ('a, 'r, 'm1) ModuleType_scheme, 'a set, 'a set] \<Rightarrow> 'r set"
 "quotient_of_submodules R M N P == {x | x. x\<in>carrier R \<and>
                                    (linear_span R M (Rxa R x)  P) \<subseteq> N}"

 Annihilator::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme]
  \<Rightarrow> 'r set" ("(Ann\<^sub>_ _)" [82,83]82)
 "Ann\<^sub>R M == quotient_of_submodules R M {0\<^sub>M} (carrier M)"

syntax
 "@QOFSUBMDS" :: "['a set, ('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, 'a set] \<Rightarrow> 'r set" ("(4_/ \<^sub>_\<ddagger>\<^sub>_/ _)" [82,82,82,83]82)

translations
 "N \<^sub>R\<ddagger>\<^sub>M P" == "quotient_of_submodules R M N P"

lemma quotient_of_submodules_inc_0Tr0:
 "\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow> f \<in> Nset n \<rightarrow> {0\<^sub>M} \<longrightarrow> e\<Sigma> M f n = 0\<^sub>M"
apply (frule module_is_ag, assumption+)
apply (frule ag_inc_zero [of "M"])
apply (induct_tac n)
apply (rule impI)
 apply (simp add:Nset_def)
 apply (frule funcset_mem [of "f" "{0}" "{0\<^sub>M}" "0"]) apply simp
 apply simp
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule funcset_mem, assumption+) apply simp
 apply (frule module_is_ag, assumption+)
apply (simp add:ag_l_zero)
apply (simp add:Nset_def)
done

lemma eSum_zero:
 "\<lbrakk>ring R; R module M; f \<in> Nset n \<rightarrow> {0\<^sub>M}\<rbrakk> \<Longrightarrow> e\<Sigma> M f n = 0\<^sub>M"
apply (simp add:quotient_of_submodules_inc_0Tr0)
done

lemma quotient_of_submodules_inc_0:
  "\<lbrakk>ring R; R module M; submodule R M P; submodule R M Q\<rbrakk> \<Longrightarrow> 0\<^sub>R \<in> (P \<^sub>R\<ddagger>\<^sub>M Q)"
apply (simp add:quotient_of_submodules_def)
apply (frule ring_is_ag)
apply (simp add:ag_inc_zero [of "R"])
apply (subgoal_tac "R \<diamondsuit> (0\<^sub>R) = {0\<^sub>R}") apply simp
apply (simp add:linear_span_def)
 apply (subgoal_tac "Q \<noteq> {}")
 apply simp
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> Q. \<forall>s\<in>Nset n \<rightarrow> {0\<^sub>R}.
 x = linear_combination R M n s f \<longrightarrow> x \<in> P")
 apply blast apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> Q. \<exists>s\<in>Nset n \<rightarrow> {0\<^sub>R}.
                                     x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+
 apply (rule impI)
 apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:submodule_def[of "R" "M" "P"])
 apply (erule conjE)+
 apply (rule eSum_mem1 [of "M" "P"], assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "s xa = 0\<^sub>R") apply simp
 apply (subst sprod_0_m, assumption+)
 apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:funcset_mem subsetD)
 apply (rule submodule_inc_0 [of "R" "M" "P"], assumption+)
 apply (simp add:submodule_def)
 apply (frule_tac f = s and A = "Nset n" and B = "{0\<^sub>R}" and x = xa
 in funcset_mem) apply simp+
 apply (frule submodule_inc_0[of "R" "M" "Q"], assumption+)
 apply (simp add:nonempty)
apply (rule equalityI)
 apply (rule subsetI)
  apply (simp add:Rxa_def CollectI)
  apply (auto del:subsetI)
  apply (simp add:ring_times_x_0)
apply (simp add:Rxa_def)
  apply (frule ring_is_ag)
  apply (frule ag_inc_zero)
  apply (frule ring_times_x_0 [THEN sym, of "R" "0\<^sub>R"], assumption+)
  apply blast
done

lemma quotient_of_submodules_is_ideal:
 "\<lbrakk>ring R; R module M; submodule R M P; submodule R M Q\<rbrakk> \<Longrightarrow> ideal R (P \<^sub>R\<ddagger>\<^sub>M Q)"
apply (frule quotient_of_submodules_inc_0 [of "R" "M" "P" "Q"], assumption+)
apply (rule ideal_condition, assumption+)
apply (simp add:quotient_of_submodules_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
apply (simp add:nonempty) apply (thin_tac "0\<^sub>R \<in> P \<^sub>R\<ddagger>\<^sub>M Q")
 apply (rule ballI)+
 apply (simp add:quotient_of_submodules_def)
apply (erule conjE)+
 apply (rule conjI)
 apply (frule ring_is_ag)
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ag_mOp_closed, assumption+)
apply (subst linear_span_def)
 apply (subgoal_tac "Q \<noteq> {}") apply simp
 prefer 2 apply (frule submodule_inc_0 [of "R" "M" "Q"], assumption+)
  apply (simp add:nonempty)
 apply (rule subsetI)
  apply (simp add:CollectI)
  apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> Q. \<forall>s\<in>Nset n \<rightarrow> R \<diamondsuit> ( x +\<^sub>R -\<^sub>R y).
   xa = linear_combination R M n s f  \<longrightarrow> xa \<in> P")
  apply blast
  apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> Q. \<exists>s\<in>Nset n \<rightarrow> R \<diamondsuit> ( x +\<^sub>R -\<^sub>R y).
                    xa = linear_combination R M n s f")
  apply (rule allI) apply (rule ballI)+ apply (rule impI)
  apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "P <+ M")
 apply (rule eSum_mem1, assumption+)
  apply (rule univar_func_test) apply (rule ballI)
  apply (frule_tac f = s and A = "Nset n" and B = "R \<diamondsuit> ( x +\<^sub>R -\<^sub>R y)" and
    x = xb in funcset_mem, assumption+)
  apply (simp add:Rxa_def) apply (fold Rxa_def)
  apply (subgoal_tac "\<forall>r\<in>carrier R. s xb =  r \<cdot>\<^sub>R ( x +\<^sub>R (-\<^sub>R y)) \<longrightarrow>
              s xb \<star>\<^sub>M (f xb) \<in> P")
  apply blast apply (thin_tac "\<exists>r\<in>carrier R. s xb =  r \<cdot>\<^sub>R ( x +\<^sub>R -\<^sub>R y)")
  apply (rule ballI) apply (rule impI) apply simp
  apply (subst ring_distrib1, assumption+)
apply (frule ring_is_ag)
 apply (rule ag_mOp_closed, assumption+)
 apply (subst sprod_distrib1, assumption+)
 apply (simp add:ring_tOp_closed)
 apply (rule ring_tOp_closed, assumption+)
 apply (frule ring_is_ag)  apply (rule ag_mOp_closed, assumption+)
 apply (subgoal_tac "Q \<subseteq> carrier M") prefer 2 apply (simp add:submodule_def)
 apply (simp add:funcset_mem subsetD)
 apply (rule submodule_pOp_closed, assumption+)
 apply (frule_tac f = f and A = "Nset n" and B = Q and x = xb in
                                            funcset_mem, assumption+)
 apply (frule_tac A = "R \<diamondsuit> x" and a = "r \<cdot>\<^sub>R x" and h = "f xb" in
          elem_linear_span [of "R" "M" _ "Q"], assumption+)
 apply (simp add:principal_ideal)
 apply (rule subsetI)
 apply (simp add:submodule_subset1)
 apply (simp add:Rxa_def) apply blast apply assumption
 apply (rule subsetD, assumption+)
 apply (frule_tac A = "R \<diamondsuit> y" and a = "r \<cdot>\<^sub>R (-\<^sub>R y)" and h = "f xb" in
          elem_linear_span [of "R" "M" _ "Q"], assumption+)
 apply (simp add:principal_ideal)
 apply (rule subsetI)
 apply (simp add:submodule_subset1)
 apply (subst ring_inv1_2 [THEN sym], assumption+)
 apply (rule ideal_inv1_closed, assumption+)
 apply (simp add:principal_ideal) apply (simp add:Rxa_def) apply blast
 apply (simp add:funcset_mem) apply (simp add:subsetD)
 apply (simp add:submodule_def [of "R" "M" "P"])
apply (rule ballI)+
 apply (simp add:quotient_of_submodules_def)
 apply (erule conjE)+
 apply (rule conjI)
 apply (simp add:ring_tOp_closed)
 apply (subst linear_span_def)
 apply (frule submodule_inc_0 [of "R" "M" "Q"], assumption+)
 apply (simp add:nonempty)
 apply (rule subsetI) apply (simp add:CollectI)
 apply auto
 apply (subgoal_tac "linear_combination R M n s f \<in> linear_span R M (R \<diamondsuit> x) Q")
 apply (thin_tac "linear_span R M (R \<diamondsuit> (0\<^sub>R)) Q \<subseteq> P")
 apply (rule subsetD, assumption+)
 apply (subgoal_tac "s \<in> Nset n \<rightarrow> R \<diamondsuit> x")
 apply (simp add:linear_span_def linear_combination_def)
 apply (simp add:nonempty) apply blast
apply (rule univar_func_test) apply (rule ballI)
  apply (frule_tac f = s and A = "Nset n" and B = "R \<diamondsuit> ( r \<cdot>\<^sub>R x)" and x = xa in
           funcset_mem, assumption+)
 apply (thin_tac "linear_span R M (R \<diamondsuit> (0\<^sub>R)) Q \<subseteq> P")
 apply (thin_tac "linear_span R M (R \<diamondsuit> x) Q \<subseteq> P")
 apply (thin_tac "s \<in> Nset n \<rightarrow> R \<diamondsuit> ( r \<cdot>\<^sub>R x)")
 apply (simp add:Rxa_def)
 apply auto
apply (simp add: ring_tOp_assoc [THEN sym])
 apply (frule_tac x = ra and y = r in ring_tOp_closed [of "R"], assumption+)
 apply blast
done

lemma Ann_is_ideal:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> ideal R (Ann\<^sub>R M)"
apply (simp add:Annihilator_def)
apply (rule quotient_of_submodules_is_ideal, assumption+)
apply (simp add:submodule_0)
apply (simp add:submodule_whole)
done

lemma linmap_im_of_lincombTr:"\<lbrakk>ring R; ideal R A; R module M; R module N; f \<in> mHom R M N; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>  s \<in> Nset n \<rightarrow> A \<and> g \<in> Nset n \<rightarrow> H \<longrightarrow>
 f (linear_combination R M n s g) = linear_combination R N n s (cmp f g)"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)
 apply (simp add:linear_combination_def)
 apply (frule_tac m = "g 0" and f = f and a = "s 0" in mHom_lin [of "R" "M" "N"], assumption+)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:funcset_mem subsetD) apply (simp add:n_in_Nsetn)
 apply assumption
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:funcset_mem ideal_subset) apply (simp add:n_in_Nsetn)
 apply (simp add:cmp_def)
apply (rule impI) apply (erule conjE)
 apply (frule_tac f = s in func_pre) apply (frule_tac f = g in func_pre)
 apply (subgoal_tac "f (linear_combination R M n s g) =
           linear_combination R N n s (cmp f g)")
 prefer 2 apply simp
 apply (simp add:linear_combination_def)
 apply (subst mHom_add[of "R" "M" "N" "f"], assumption+)
 apply (rule_tac R = M and f = "(\<lambda>j. s j \<star>\<^sub>M (g j))" and n = n and i = n in eSum_mem) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI) apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD) apply (simp add:n_in_Nsetn)
 apply (rule sprod_mem, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem ideal_subset) apply (simp add:n_in_Nsetn)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem subsetD) apply (simp add:n_in_Nsetn)
apply simp
 apply (subgoal_tac "f ( s (Suc n) \<star>\<^sub>M (g (Suc n))) = (s (Suc n)) \<star>\<^sub>N ((cmp f g) (Suc n))")  apply simp
 apply (frule_tac m = "g (Suc n)" and f = f and a = "s (Suc n)" in mHom_lin [of "R" "M" "N"], assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem subsetD) apply (simp add:n_in_Nsetn)
 apply assumption
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem ideal_subset) apply (simp add:n_in_Nsetn)
 apply (simp add:cmp_def)
done

lemma linmap_im_lincomb:"\<lbrakk>ring R; ideal R A; R module M; R module N; f \<in> mHom R M N; H \<subseteq> carrier M; s \<in> Nset n \<rightarrow> A; g \<in> Nset n \<rightarrow> H \<rbrakk> \<Longrightarrow>
  f (linear_combination R M n s g) = linear_combination R N n s (cmp f g)"
apply (simp add:linmap_im_of_lincombTr)
done

lemma linmap_im_linspan:"\<lbrakk>ring R; ideal R A; R module M; R module N; f \<in> mHom R M N; H \<subseteq> carrier M; s \<in> Nset n \<rightarrow> A; g \<in> Nset n \<rightarrow> H \<rbrakk> \<Longrightarrow>
            f (linear_combination R M n s g) \<in> linear_span R N A (f ` H)"
 apply (subgoal_tac "linear_combination R M n s g \<in> linear_span R M A H")
 apply (simp add:linear_span_def)
 apply (case_tac "H = {}") apply simp apply (simp add:mHom_0)
apply simp
 apply (thin_tac "\<exists>na. \<exists>f\<in>Nset na \<rightarrow> H. \<exists>sa\<in>Nset na \<rightarrow> A.
   linear_combination R M n s g = linear_combination R M na sa f")
 apply (simp add: linmap_im_lincomb [of "R" "A" "M" "N" "f" "H" "s" "n" "g"])
 apply (subgoal_tac "(cmp f g) \<in> Nset n \<rightarrow> f ` H")
 apply blast
apply (rule univar_func_test) apply (rule ballI) apply (simp add:cmp_def)
 apply (frule_tac f = g and A = "Nset n" and B = H and x = x in funcset_mem,
         assumption+) apply (simp add:image_def) apply blast
apply (simp add:linear_combination_def linear_span_def)
 apply (subgoal_tac "0 \<in> Nset n") prefer 2 apply (simp add:Nset_def)
 apply (frule_tac f = g and A = "Nset n" and B = H and x = 0 in funcset_mem,
                  assumption+)
 apply (simp add:nonempty)
 apply blast
done

lemma linmap_im_linspan1:"\<lbrakk>ring R; ideal R A; R module M; R module N; f \<in> mHom R M N; H \<subseteq> carrier M; h \<in> linear_span R M A H\<rbrakk> \<Longrightarrow>
                              f h \<in> linear_span R N A (f ` H)"
apply (simp add:linear_span_def [of "R" "M"])
 apply (case_tac "H = {}") apply (simp add:linear_span_def)
 apply (simp add:mHom_0) apply simp
apply (subgoal_tac "\<forall>n. \<forall>g\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A.
 h = linear_combination R M n s g \<longrightarrow> f h \<in> linear_span R N A (f ` H)")
apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> A. h = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linmap_im_linspan)
done

section "3. a module over two rings"

record ('a, 'r1, 'r2) bModuleType = "'a AgroupType" +
  sprodl  :: "'r1 \<Rightarrow> 'a \<Rightarrow> 'a"
  sprodr  :: "'r2 \<Rightarrow> 'a \<Rightarrow> 'a"

constdefs
 bModule ::"[('r1, 'm1) RingType_scheme, ('r2, 'm2) RingType_scheme, ('a, 'r1, 'r2, 'more) bModuleType_scheme] \<Rightarrow> bool"
            ("(3_/ _/ bModule/ _)" [82,82,83]82)
 "R S bModule M  == ring R \<and> ring S \<and>  agroup M  \<and>
   sprodl M \<in> carrier R \<rightarrow> carrier M \<rightarrow> carrier M \<and>
  (\<forall>a \<in> carrier R. \<forall>b\<in> carrier R. \<forall>m\<in>carrier M. \<forall>n\<in>carrier M.
      sprodl M (tOp R a b) m = sprodl M a (sprodl M b m) \<and>
   sprodl M (pOp R a b) m = pOp M (sprodl M a m) (sprodl M b m) \<and>
   sprodl M a (pOp M m n) = pOp M (sprodl M a m) (sprodl M a n) \<and>
   sprodl M (1\<^sub>R) m = m) \<and>
   sprodr M \<in> carrier S \<rightarrow> carrier M \<rightarrow> carrier M \<and>
  (\<forall>a \<in> carrier S. \<forall>b\<in> carrier S. \<forall>m\<in>carrier M. \<forall>n\<in>carrier M.
      sprodr M (tOp S a b) m = sprodr M a (sprodr M b m) \<and>
   sprodr M (pOp S a b) m = pOp M (sprodr M a m) (sprodr M b m) \<and>
   sprodr M a (pOp M m n) = pOp M (sprodr M a m) (sprodr M a n) \<and>
   sprodr M (1\<^sub>S) m = m)"

constdefs
  lModule::"('a, 'r1, 'r2, 'more) bModuleType_scheme \<Rightarrow> ('a, 'r1) ModuleType"
       ("(_\<^sub>l)" [1000]999)
  "M\<^sub>l == \<lparr>carrier = carrier M, pOp = pOp M, mOp = mOp M,
    zero = zero M, sprod = sprodl M \<rparr>"

constdefs
  rModule::"('a, 'r1, 'r2, 'more) bModuleType_scheme \<Rightarrow> ('a, 'r2) ModuleType"
        ("(_\<^sub>r)" [1000]999)
  "M\<^sub>r == \<lparr>carrier = carrier M, pOp = pOp M, mOp = mOp M,
    zero = zero M, sprod = sprodr M \<rparr>"

lemma bmodule_is_ag:"\<lbrakk>ring R; ring S; R S bModule M\<rbrakk> \<Longrightarrow> agroup M"
apply (simp add:bModule_def)
done

lemma bModule_is_lModule:"\<lbrakk>ring R; ring S; R S bModule M\<rbrakk> \<Longrightarrow> R module M\<^sub>l"
apply (subgoal_tac "agroup \<lparr>carrier = carrier M, pOp = pOp M,
 mOp = mOp M, zero = 0\<^sub>M, sprod = sprodl M\<rparr>")
apply (simp add:bModule_def lModule_def Module_def)
apply (frule bmodule_is_ag [of "R" "S" "M"], assumption+)
apply (simp add:agroup_def) apply (fold agroup_def)
apply (rule impI) apply (rule ballI)
apply (simp add:ag_r_zero)
done

lemma bModule_is_rModule:"\<lbrakk>ring R; ring S; R S bModule M\<rbrakk> \<Longrightarrow> S module M\<^sub>r"
apply (subgoal_tac "agroup \<lparr>carrier = carrier M, pOp = pOp M,
 mOp = mOp M, zero = 0\<^sub>M, sprod = sprodr M\<rparr>")
apply (simp add:bModule_def rModule_def Module_def)
apply (frule bmodule_is_ag [of "R" "S" "M"], assumption+)
apply (simp add:agroup_def) apply (fold agroup_def)
apply (rule impI) apply (rule ballI)
apply (simp add:ag_r_zero)
done

lemma sprodr_welldefTr1:"\<lbrakk>ring R; R module M; ideal R A; A \<subseteq> Ann\<^sub>R M; a \<in> A;
 m \<in> carrier M\<rbrakk>  \<Longrightarrow> a \<star>\<^sub>M m = 0\<^sub>M "
apply (simp add:Annihilator_def quotient_of_submodules_def)
apply (frule subsetD, assumption+)
 apply (simp add:CollectI) apply (erule conjE)
 apply (frule_tac a = a and A = "R \<diamondsuit> a" in elem_linear_span [of "R" "M" _ "carrier M" _ "m"], assumption+)
 apply (simp add:principal_ideal) apply simp apply (simp add:a_in_principal)
 apply assumption
 apply (frule subsetD [of "linear_span R M (R \<diamondsuit> a) (carrier M)" "{0\<^sub>M}"
 "a \<star>\<^sub>M m"], assumption+) apply simp
done

lemma sprodr_welldefTr2:"\<lbrakk>ring R; R module M; ideal R A; A \<subseteq> Ann\<^sub>R M;
a \<in> carrier R; x \<in> a \<uplus>\<^sub>R A; m \<in> carrier M\<rbrakk>  \<Longrightarrow> a \<star>\<^sub>M m = x \<star>\<^sub>M m"
apply (frule mem_ar_coset1 [of "R" "A" "a" "x"], assumption+)
apply auto
apply (subst sprod_distrib1, assumption+)
 apply (simp add:ideal_subset)
 apply assumption+
apply (simp add:sprodr_welldefTr1)
apply (frule sprod_mem [of "R" "M" "a" "m"], assumption+)
apply (frule module_is_ag, assumption+)
apply (simp add:ag_l_zero)
done

constdefs
 cos_sprodr::"[('r, 'm) RingType_scheme, 'r set, ('a, 'r, 'm1) ModuleType_scheme] \<Rightarrow> 'r set \<Rightarrow> 'a \<Rightarrow> 'a"
  "cos_sprodr R A M == \<lambda>X. \<lambda>m. (SOME x. x \<in> X) \<star>\<^sub>M m"

lemma cos_sprodr_welldef:"\<lbrakk>ring R; R module M; ideal R A; A \<subseteq> Ann\<^sub>R M;
X \<in> set_ar_cos R A; a \<in> carrier R; X = a \<uplus>\<^sub>R A; m \<in> carrier M\<rbrakk>  \<Longrightarrow>
 cos_sprodr R A M X m = a \<star>\<^sub>M m"
apply (simp add:set_ar_cos_def)
apply (subgoal_tac "\<forall>aa\<in>carrier R. a \<uplus>\<^sub>R A = aa \<uplus>\<^sub>R A \<longrightarrow>
                           cos_sprodr R A M (a \<uplus>\<^sub>R A) m =  a \<star>\<^sub>M m")
apply blast
 apply (thin_tac "\<exists>aa\<in>carrier R. a \<uplus>\<^sub>R A = aa \<uplus>\<^sub>R A")
 apply (rule ballI) apply (rule impI)
 apply (frule a_in_ar_coset [of "R" "A" "a"], assumption+)
 apply (thin_tac "a \<uplus>\<^sub>R A = aa \<uplus>\<^sub>R A")
 apply (simp add:cos_sprodr_def)
 apply (rule sprodr_welldefTr2[THEN sym], assumption+) prefer 2 apply simp
apply (rule someI2_ex) apply blast apply assumption
done

constdefs
 r_qr_bmod::"[('r, 'm) RingType_scheme, 'r set, ('a, 'r, 'm1) ModuleType_scheme] \<Rightarrow> ('a, 'r, 'r set) bModuleType"
 "r_qr_bmod R A M == \<lparr>carrier = carrier M, pOp = pOp M, mOp = mOp M,
  zero = zero M, sprodl = sprod M, sprodr = cos_sprodr R A M \<rparr>"
 (* Remark. A should be an ideal contained in Ann\<^sub>R M. *)
syntax
 "@RQBMOD" :: "[('a, 'r, 'm1) ModuleType_scheme, ('r, 'm) RingType_scheme,
  'r set] \<Rightarrow>  ('a, 'r, 'r set) bModuleType" ("(3_\<^sub>_\<^sub>'/'\<^sub>_)" [84,84,85]84)
translations
 "M\<^sub>R\<^sub>/\<^sub>A" == "r_qr_bmod R A M"

lemma r_qr_Mmodule:"\<lbrakk>ring R; R module M; A \<subseteq> Ann\<^sub>R M; ideal R A\<rbrakk> \<Longrightarrow> R (R /\<^sub>r A) bModule M\<^sub>R\<^sub>/\<^sub>A"
apply (simp add:bModule_def)
apply (simp add:r_qr_bmod_def)
apply (simp add:qring_ring)
apply (subgoal_tac " agroup
        \<lparr>carrier = carrier M, pOp = pOp M, mOp = mOp M, zero = 0\<^sub>M,
           sprodl = sprod M, sprodr = cos_sprodr R A M\<rparr>") apply simp
prefer 2 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:agroup_def) apply (fold agroup_def)
 apply (rule impI) apply (rule ballI) apply (simp add:ag_r_zero)
 apply (thin_tac " agroup
        \<lparr>carrier = carrier M, pOp = pOp M, mOp = mOp M, zero = 0\<^sub>M,
           sprodl = sprod M, sprodr = cos_sprodr R A M\<rparr>")
apply (rule conjI)
apply (simp add:Module_def)
apply (rule conjI)
apply (simp add:Module_def)
apply (rule conjI) apply (simp add:qring_def)
 apply (subgoal_tac "set_r_cos (b_ag R) A = set_ar_cos R A") apply simp
 apply (rule bivar_func_test) apply (rule ballI)+
 apply (thin_tac "set_r_cos (b_ag R) A = set_ar_cos R A")
 apply (simp add:set_ar_cos_def)
 apply (subgoal_tac "\<forall>aa\<in>carrier R. a = aa \<uplus>\<^sub>R A \<longrightarrow>
                             cos_sprodr R A M a b \<in> carrier M")
 apply blast apply (thin_tac "\<exists>aa\<in>carrier R. a = aa \<uplus>\<^sub>R A")
 apply (rule ballI) apply (rule impI) apply simp
 apply (rename_tac X m a)
 apply (frule_tac X = "a \<uplus>\<^sub>R A" and a = a and m = m in
               cos_sprodr_welldef[of "R" "M" "A"], assumption+)
 apply (simp add:set_ar_cos_def) apply blast
 apply assumption apply simp apply assumption apply simp
 apply (simp add:sprod_mem)
 apply (simp add:set_ar_cos_def)
 apply (frule ring_is_ag)
 apply (frule b_ag_group)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:ar_coset_def set_r_cos_def)
apply (rule ballI)+
 apply (frule ring_is_ag)
 apply (frule b_ag_group)
 apply (simp add:qring_def)
apply (subgoal_tac "set_r_cos (b_ag R) A = set_ar_cos R A") apply simp
apply (rename_tac X Y m n)
 apply (subgoal_tac "\<exists>x\<in>carrier R. X = x \<uplus>\<^sub>R A")
 apply (subgoal_tac "\<exists>y\<in>carrier R. Y = y \<uplus>\<^sub>R A")
 apply (subgoal_tac "\<forall>x \<in> carrier R. \<forall>y\<in> carrier R. X = x \<uplus>\<^sub>R A \<and> Y = y \<uplus>\<^sub>R A
  \<longrightarrow>     cos_sprodr R A M (rcostOp R A X Y) m =
          cos_sprodr R A M X (cos_sprodr R A M Y m) \<and>
          cos_sprodr R A M (costOp (b_ag R) A X Y) m =
          cos_sprodr R A M X m +\<^sub>M (cos_sprodr R A M Y m) \<and>
          cos_sprodr R A M X ( m +\<^sub>M n) =
          cos_sprodr R A M X m +\<^sub>M (cos_sprodr R A M X n) \<and>
          cos_sprodr R A M (1\<^sub>R \<uplus>\<^sub>R A) m = m")
 apply blast
 apply (thin_tac "\<exists>x\<in>carrier R. X = x \<uplus>\<^sub>R A")
 apply (thin_tac "\<exists>y\<in>carrier R. Y = y \<uplus>\<^sub>R A")
 apply (rule ballI)+
 apply (rule impI) apply (erule conjE) apply simp
 apply (subst rcostOp, assumption+)
 apply (frule_tac x = x and y = y in ring_tOp_closed, assumption+)
 apply (simp add:cos_sprodr_welldef)
apply (subgoal_tac "costOp (b_ag R) A (x \<uplus>\<^sub>R A) (y \<uplus>\<^sub>R A) = (x +\<^sub>R y) \<uplus>\<^sub>R A")
 apply simp
prefer 3 apply (simp add:set_ar_cos_def)
prefer 3 apply (simp add:set_ar_cos_def)
prefer 3 apply (simp add:set_ar_cos_def)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:set_r_cos_def ar_coset_def)
prefer 2
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:ar_coset_def) apply (simp add:agop_gop [THEN sym])
 apply (rule  costOpwelldef [THEN sym], assumption+)
 apply (simp add:ideal_def) apply (erule conjE)
 apply (simp add:asubg_nsubg) apply assumption+
apply (frule_tac x = x and y = y in ag_pOp_closed[of "R"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption)
 apply (frule_tac x = m and y = n in ag_pOp_closed [of "M"], assumption+)
 apply (frule_tac a = y and m = m in sprod_mem [of "R" "M"], assumption+)
 apply (frule ring_one [of "R"])
 apply (simp add:cos_sprodr_welldef)
 apply (frule_tac X = "x \<cdot>\<^sub>R y \<uplus>\<^sub>R A" and a = "x \<cdot>\<^sub>R y" and m = m in
                        cos_sprodr_welldef [of "R" "M" "A"], assumption+)
 apply (simp add:set_ar_cos_def) apply blast apply assumption apply simp
 apply assumption apply simp
 apply (simp add:sprod_assoc)
 apply (frule ring_one [of "R"])
 apply (frule_tac X = "(x +\<^sub>R y) \<uplus>\<^sub>R A" and a = "(x +\<^sub>R y)" and m = m in
                        cos_sprodr_welldef [of "R" "M" "A"], assumption+)
 apply (simp add:set_ar_cos_def) apply blast
 apply simp+
 apply (simp add:sprod_distrib1)
 apply (simp add:sprod_distrib2)
apply (frule_tac X = "1\<^sub>R \<uplus>\<^sub>R A" and a = "1\<^sub>R" and m = m in
                        cos_sprodr_welldef [of "R" "M" "A"], assumption+)
 apply (simp add:set_ar_cos_def) apply blast apply assumption apply simp+
 apply (simp add:sprod_one)
done

constdefs
 faithful::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme]
                             \<Rightarrow> bool"
  "faithful R M == Ann\<^sub>R M = {0\<^sub>R}"

section "4. eSum and Generators"

constdefs
 generator ::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,
               'a set] \<Rightarrow> bool"
 "generator R M H == H \<subseteq> carrier M \<and>
                      linear_span R M (carrier R) H = carrier M"

 finite_generator::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,
               'a set] \<Rightarrow> bool"
 "finite_generator R M H == finite H \<and> generator R M H"

 fGOver :: "[('a, 'r, 'm1) ModuleType_scheme, ('r, 'm)
 RingType_scheme]  \<Rightarrow>  bool" (*(infixl 70)*)
 "fGOver M R ==  \<exists>H. finite_generator R M H"

syntax
 "@FGENOVER"::"[('a, 'r, 'm1) ModuleType_scheme, ('r, 'm)
 RingType_scheme]  \<Rightarrow>  bool" (infixl "fgover" 70)

translations
 "M fgover R" == "fGOver M R"

lemma h_in_linear_span:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; h \<in> H\<rbrakk> \<Longrightarrow>
                                   h \<in> linear_span R M (carrier R) H"
apply (subst sprod_one [THEN sym, of "R" "M" "h"], assumption+)
 apply (simp add:subsetD)
 apply (frule ring_one)
 apply (rule elem_linear_span [of "R" "M" "carrier R" "H" "1\<^sub>R" "h"],
                                              assumption+)
 apply (simp add:whole_ideal) apply assumption+
done

lemma generator_sub_carrier:"\<lbrakk>ring R; R module M; generator R M H\<rbrakk> \<Longrightarrow>
                                              H \<subseteq> carrier M"
apply (simp add:generator_def)
done

lemma lin_span_sub_carrier:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
            linear_span R M A H \<subseteq> carrier M"
apply (rule subsetI)
 apply (simp add:linear_span_def)
 apply (case_tac "H = {}") apply simp
 apply (simp add:module_inc_zero)
apply simp
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A.
 x = linear_combination R M n s f \<longrightarrow> x \<in> carrier M")
apply blast apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
apply (rule allI) apply (rule ballI)+ apply (rule impI)
apply (simp add:linear_combination_def)
apply (rule_tac R = M and n = n and i = n in eSum_mem)
 apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (simp add:n_in_Nsetn)
done

lemma lin_span_lin_span:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M\<rbrakk>\<Longrightarrow>
                        linear_span R M A H \<subseteq> linear_span R M (carrier R) H"
apply (rule subsetI)
 apply (simp add:linear_span_def)
 apply (case_tac "H = {}") apply simp apply simp
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A.
 x = linear_combination R M n s f \<longrightarrow> (\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f)")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_def)
 apply (frule ideal_subset1 [of "R" "A"], assumption+)
apply (frule_tac  f = s in extend_fun, assumption+)
 apply blast
done

lemma lin_span_closedTr:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M\<rbrakk>\<Longrightarrow>  \<forall>s. \<forall>f. s\<in>Nset n \<rightarrow> A \<and> f\<in> Nset n \<rightarrow> linear_span R M A H \<longrightarrow>(eSum M (\<lambda>j. s j \<star>\<^sub>M (f j)) n \<in> linear_span R M A H)"
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply simp
 apply (erule conjE) apply (subgoal_tac "0 \<in> Nset 0")
 apply (rule submodule_sprod_closed, assumption+)
 apply (rule linear_span_subModule, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"])
 apply (frule func_pre [of _ _ "linear_span R M A H"])
 apply simp
 apply (rule submodule_pOp_closed, assumption+)
 apply (rule linear_span_subModule, assumption+)
 apply simp
apply (rule linear_span_sprod_closed, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac f = s and A = "Nset (Suc n)" and B = A and x = "Suc n" in
 funcset_mem, assumption+)  apply (simp add:ideal_subset)
 apply (simp add:Nset_def)
 apply (simp add:Nset_def funcset_mem)
done

lemma lin_span_closed:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M;
 s \<in> Nset n \<rightarrow> A;  f \<in> Nset n \<rightarrow> linear_span R M A H \<rbrakk> \<Longrightarrow>
 linear_combination R M n s f \<in> linear_span R M A H"
apply (simp add:linear_combination_def)
apply (simp add:lin_span_closedTr)
done

lemma lin_span_closed1:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M;
 s \<in> Nset n \<rightarrow> carrier R;  f \<in> Nset n \<rightarrow> linear_span R M (carrier R) H \<rbrakk> \<Longrightarrow>
 e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n \<in> linear_span R M (carrier R) H"
apply (frule whole_ideal [of "R"])
apply (simp add:lin_span_closedTr)
done

lemma lin_span_closed2Tr:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
 s \<in> Nset n \<rightarrow> A \<and> f \<in> Nset n \<rightarrow> linear_span R M (carrier R) H \<longrightarrow>
 linear_combination R M n s f \<in> linear_span R M A H"
apply (induct_tac n)
apply (rule impI) apply (erule conjE)+
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule_tac f = f and A = "Nset 0" and B = "{0\<^sub>M}" and x = 0 in
          funcset_mem, assumption+)
 apply simp
 apply (rule sprod_a_0, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:Nset_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule_tac f = f and A = "Nset 0" and B = "linear_span R M (carrier R) H" and x = 0 in funcset_mem, assumption+)
 apply (simp add:linear_combination_def)
 apply (thin_tac "f \<in> Nset 0 \<rightarrow> linear_span R M (carrier R) H")
 apply (simp add:linear_span_def [of _ _ "carrier R"])
 apply (subgoal_tac "\<forall>n. \<forall>fa\<in>Nset n \<rightarrow> H. \<forall>t\<in>Nset n \<rightarrow> carrier R.
 f 0 = linear_combination R M n t fa \<longrightarrow> s 0 \<star>\<^sub>M (f 0) \<in> linear_span R M A H")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>fa\<in>Nset n \<rightarrow> H.
              \<exists>s\<in>Nset n \<rightarrow> carrier R. f 0 = linear_combination R M n s fa")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_def)
 apply (frule_tac f = s and A = "Nset 0" and B = A and x = 0 in funcset_mem, assumption+)
 apply (subst linear_span_sprod [of "R" "M" "carrier R" "H"], assumption+)
 apply (simp add:whole_ideal) apply assumption
 apply (simp add:ideal_subset) apply assumption+
apply (subgoal_tac "e\<Sigma> M (\<lambda>k. s 0 \<star>\<^sub>M ( t k \<star>\<^sub>M (fa k))) n =
               e\<Sigma> M (\<lambda>k.  (s 0 \<cdot>\<^sub>R (t k)) \<star>\<^sub>M (fa k)) n")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>k. s 0 \<star>\<^sub>M (t k \<star>\<^sub>M (fa k))) n =
          e\<Sigma> M (\<lambda>k.  (s 0 \<cdot>\<^sub>R (t k)) \<star>\<^sub>M (fa k)) n")
 apply (simp add:linear_span_def)
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "(\<lambda>l\<in>Nset n. (s 0 \<cdot>\<^sub>R (t l))) \<in> Nset n \<rightarrow> A")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>k. (s 0 \<cdot>\<^sub>R (t k)) \<star>\<^sub>M (fa k)) n =
       e\<Sigma> M (\<lambda>k. (\<lambda>l\<in>Nset n.  (s 0 \<cdot>\<^sub>R (t l))) k \<star>\<^sub>M (fa k)) n")
 apply blast
apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (rule sprod_mem, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
apply (rule ballI)
 apply simp
apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (frule_tac r = "t x" in ideal_ring_multiple[of "R" "A" "s 0"],
                                                            assumption+)
 apply (simp add:funcset_mem)
 apply (subst ring_tOp_commute, assumption+)
 apply (simp add:ideal_subset) apply (simp add:funcset_mem)
 apply assumption
apply (rule eSum_eq)
 apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)+
 apply (simp add:ideal_subset)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:ideal_subset) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
apply (rule ballI)
 apply (rule sprod_assoc [THEN sym], assumption+)
 apply (simp add:ideal_subset) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
 apply (rule impI) apply (erule conjE)+
 apply (frule func_pre [of _ _ "A"])
 apply (frule func_pre [of _ _ "linear_span R M (carrier R) H"])
 apply (subgoal_tac "linear_combination R M n s f \<in> linear_span R M A H")
 apply (thin_tac "s \<in> Nset n \<rightarrow> A \<and> f \<in> Nset n \<rightarrow>
 linear_span R M (carrier R) H \<longrightarrow> linear_combination R M n s f \<in> linear_span R M A H")
 apply (simp add:linear_combination_def)
 apply (rule linear_span_tOp_closed, assumption+)
prefer 2 apply simp
 apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac  f = f and A = "Nset (Suc n)" and B = "{0\<^sub>M}" and x = "Suc n" in funcset_mem, assumption+) apply simp
 apply (rule sprod_a_0, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:Nset_def)
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
apply (frule_tac  f = f and A = "Nset (Suc n)" and B = "linear_span R M (carrier R) H" and x = "Suc n" in funcset_mem, assumption+)
 apply (thin_tac "f \<in> Nset (Suc n) \<rightarrow> linear_span R M (carrier R) H")
 apply (thin_tac "f \<in> Nset n \<rightarrow> linear_span R M (carrier R) H")
 apply (thin_tac " e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n \<in> linear_span R M A H")
prefer 2 apply (simp add:Nset_def)
apply (simp add:linear_span_def [of "R" "M" "carrier R"])
 apply (subgoal_tac "\<forall>na. \<forall>fa\<in>Nset na \<rightarrow> H. \<forall>t\<in>Nset na \<rightarrow> carrier R.
 f (Suc n) = linear_combination R M na t fa \<longrightarrow> (s (Suc n) \<star>\<^sub>M (f (Suc n)) \<in> linear_span R M A H)")  apply blast
 apply (thin_tac "\<exists>na. \<exists>fa\<in>Nset na \<rightarrow> H. \<exists>s\<in>Nset na \<rightarrow> carrier R.
                      f (Suc n) = linear_combination R M na s fa")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_def linear_span_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add: linear_span_sprod [of "R" "M" "carrier R" "H"] whole_ideal funcset_mem ideal_subset)
 apply (subgoal_tac "(\<lambda>l\<in>Nset na. (s (Suc n)) \<cdot>\<^sub>R (t l)) \<in> Nset na \<rightarrow> A")
 apply (subgoal_tac " e\<Sigma> M (\<lambda>k. s (Suc n) \<star>\<^sub>M ( t k \<star>\<^sub>M (fa k))) na =
  e\<Sigma> M (\<lambda>j. (\<lambda>l\<in>Nset na. (s (Suc n)) \<cdot>\<^sub>R (t l)) j  \<star>\<^sub>M (fa j)) na")
 apply blast
apply (rule eSum_eq)
 apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)+
 apply (simp add:funcset_mem ideal_subset)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (rule sprod_mem, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem) apply (simp add:funcset_mem subsetD)
apply (rule ballI)
 apply simp
 apply (rule sprod_assoc [THEN sym], assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (rule_tac x = "s (Suc n)" and r = "t x" in
                   ideal_ring_multiple1 [of "R" "A"], assumption+)
 apply (simp add:funcset_mem)
 apply (simp add:funcset_mem)
apply (simp add:Nset_def)
done

lemma lin_span_closed2:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M;
 s \<in> Nset n \<rightarrow> A ; f \<in> Nset n \<rightarrow> linear_span R M (carrier R) H \<rbrakk> \<Longrightarrow>
   linear_combination R M n s f \<in> linear_span R M A H"
apply (simp add:lin_span_closed2Tr)
done

lemma lin_span_closed3:"\<lbrakk>ring R; R module M; ideal R A; generator R M H;
A \<odot>\<^sub>R M = carrier M \<rbrakk> \<Longrightarrow> linear_span R M A H = carrier M"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:linear_span_def)
apply (case_tac "H = {}") apply simp apply (simp add:module_inc_zero)
 apply simp
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H.
   \<forall>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f \<longrightarrow> x \<in> carrier M")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply simp
 apply (rule_tac s = s and m = f in linear_combination_mem [of "R" "M" "A" "H"], assumption+)
 apply (simp add:generator_def) apply assumption+
apply (rule subsetI)
 apply (simp add:generator_def)
 apply (erule conjE)
 apply (case_tac "H = {}") apply simp apply (simp add:linear_span_def)
apply (simp add:smodule_ideal_coeff_def)
 apply (subgoal_tac "x \<in> linear_span R M A (carrier M)") prefer 2 apply simp
 apply (thin_tac "linear_span R M A (carrier M) = carrier M")
 apply (frule sym) apply (thin_tac "linear_span R M (carrier R) H = carrier M")
 apply simp
 apply (subgoal_tac "H \<subseteq> carrier M")
 apply (thin_tac "carrier M = linear_span R M (carrier R) H")
 apply (thin_tac "H \<subseteq> linear_span R M (carrier R) H")
 apply (frule linear_span_inc_0 [of "R" "M" "carrier R" "H"], assumption+)
 apply (simp add:whole_ideal) apply assumption+
apply (frule nonempty [of "0\<^sub>M" "linear_span R M (carrier R) H"])
apply (simp add:linear_span_def [of _ _ _ "linear_span R M (carrier R) H"])
prefer 2  apply simp
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> linear_span R M (carrier R) H.
 \<forall>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f \<longrightarrow> x \<in> linear_span R M A H")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> linear_span R M (carrier R) H.
                  \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+
 apply (rule impI)
apply simp
apply (simp add:lin_span_closed2)
done

lemma generator_generator:"\<lbrakk>ring R; R module M; generator R M H;
H1 \<subseteq> carrier M; H \<subseteq> linear_span R M (carrier R) H1 \<rbrakk>  \<Longrightarrow>  generator R M H1"
apply (subst generator_def)
 apply (frule generator_sub_carrier [of "R" "M" "H"], assumption+)
 apply simp
apply (rule equalityI)
 apply (rule subsetI)
 apply (thin_tac "H \<subseteq> linear_span R M (carrier R) H1")
 apply (simp add:linear_span_def)
 apply (case_tac "H1 = {}") apply simp
 apply (rule module_inc_zero, assumption+) apply simp
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H1. \<forall>s\<in>Nset n \<rightarrow> carrier R.
 x = linear_combination R M n s f \<longrightarrow> x \<in> carrier M")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H1.
                  \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply simp apply (thin_tac "x = linear_combination R M n s f")
 apply (simp add:linear_combination_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule_tac R = M and f = "\<lambda>j.  s j \<star>\<^sub>M (f j)" and n = n and i = n in
  eSum_mem, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem) apply (simp add:funcset_mem subsetD)
 apply (simp add:Nset_def)
 apply (rule subsetI)
 apply (simp add:generator_def)
 apply (subgoal_tac "x \<in> linear_span R M (carrier R) H")
 apply (thin_tac "linear_span R M (carrier R) H = carrier M")
 apply (simp add:linear_span_def [of "R" "M" _ "H"])
 apply (case_tac "H = {}") apply simp apply (rule linear_span_inc_0, assumption+) apply (simp add:whole_ideal) apply assumption+ apply simp
 prefer 2 apply simp
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f  \<longrightarrow> x \<in> linear_span R M (carrier R) H1")
 apply blast
 apply (thin_tac " \<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                  \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_def)
 apply (rule_tac s = s and n = n and f = f in lin_span_closed1 [of "R" "M" "H1"], assumption+)
apply (rule extend_fun, assumption+)
done

lemma generator_generator_decTr:"\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow>
f \<in> Nset n \<rightarrow> carrier M \<and> generator R M (f ` Nset n) \<and> (\<forall>i\<in>nset (Suc 0) n. f i \<in> linear_span R M (carrier R) (f ` Nset (i - Suc 0))) \<longrightarrow> linear_span R M (carrier R) {f 0} = carrier M"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "f ` Nset 0 = {f 0}") apply simp
 apply (thin_tac " \<forall>i\<in>nset (Suc 0) 0.
          f i \<in> linear_span R M (carrier R) (f ` Nset (i - Suc 0))")
 apply (thin_tac "f ` Nset 0 = {f 0}")
 apply (simp add:generator_def)
 apply (simp add:Nset_def)
apply (rule impI)
 apply (erule conjE)+
 apply (frule func_pre [of _ _ "carrier M"])
 apply (subgoal_tac "f (Suc n) \<in> linear_span R M (carrier R) (f ` (Nset n))")
 apply (subgoal_tac "generator R M (f ` Nset n)")
 apply (subgoal_tac "\<forall>i\<in>nset (Suc 0) n.
               f i \<in> linear_span R M (carrier R) (f ` Nset (i - Suc 0))")
 apply blast
 apply (thin_tac " f \<in> Nset n \<rightarrow> carrier M \<and>
           generator R M (f ` Nset n) \<and>
           (\<forall>i\<in>nset (Suc 0) n.
               f i \<in> linear_span R M (carrier R) (f ` Nset (i - Suc 0))) \<longrightarrow>
           linear_span R M (carrier R) {f 0} = carrier M")
 apply (rule ballI)
 apply (subgoal_tac "i \<in> nset (Suc 0) (Suc n)") apply simp
 apply (simp add:nset_def)
 apply (frule_tac H = "f ` (Nset (Suc n))" and ?H1.0 = "f ` (Nset n)"in generator_generator [of "R" "M"], assumption+)
 apply (rule_tac f = f and A = "Nset n" and B = "carrier M" and ?A1.0 = "Nset n" in image_sub, assumption+) apply simp
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (rule subsetI) apply (simp add:Nset_def)
 apply (rule subsetI) apply (simp add:Nset_def)
 apply (rule subsetI) apply simp
 apply (case_tac "x = f (Suc n)") apply simp apply simp
 apply (rule h_in_linear_span, assumption+)
 apply (rule_tac f = f and A = "Nset n" and B = "carrier M" and ?A1.0 = "Nset n" in image_sub, assumption+) apply simp apply assumption+
 apply (thin_tac " f \<in> Nset n \<rightarrow> carrier M \<and> generator R M (f ` Nset n) \<and>
 (\<forall>i\<in>nset (Suc 0) n. f i \<in> linear_span R M (carrier R) (f ` Nset (i - Suc 0))) \<longrightarrow>  linear_span R M (carrier R) {f 0} = carrier M")
 apply (subgoal_tac "Suc n \<in> nset (Suc 0) (Suc n)")
 apply (subgoal_tac "f (Suc n) \<in> linear_span R M (carrier R)
        (f ` Nset (Suc n - Suc 0))") apply simp
 apply blast
 apply (simp add:nset_def)
done

lemma generator_generator_dec:"\<lbrakk>ring R; R module M; f \<in> Nset n \<rightarrow> carrier M;
 generator R M (f ` Nset n); (\<forall>i\<in>nset (Suc 0) n. f i \<in> linear_span R M (carrier R) (f ` Nset (i - Suc 0))) \<rbrakk> \<Longrightarrow> linear_span R M (carrier R) {f 0} = carrier M"
apply (simp add:generator_generator_decTr [of "R" "M" "f" "n"])
done

lemma surjec_generator:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
 surjec\<^sub>M\<^sub>,\<^sub>N f; generator R M H\<rbrakk> \<Longrightarrow> generator R N (f ` H)"
apply (simp add:generator_def) apply (erule conjE)
 apply (simp add:surjec_def) apply (erule conjE)+
 apply (simp add:aHom_def) apply (erule conjE)+
 apply (simp add:image_sub [of "f" "carrier M" "carrier N" "H"])
apply (frule lin_span_sub_carrier [of "R" "carrier R" "N" "f ` H"])
 apply (simp add:whole_ideal) apply assumption
 apply (simp add:image_sub [of "f" "carrier M" "carrier N" "H"])
apply (rule equalityI, assumption+)
 apply (rule subsetI)
 apply (simp add:surj_to_def)
 apply (subgoal_tac "x \<in> f ` carrier M") prefer 2 apply simp
 apply (thin_tac "f ` carrier M = carrier N")
 apply (simp add:image_def)
 apply (thin_tac "\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f ( a +\<^sub>M b) =  f a +\<^sub>N (f b)")
apply (subgoal_tac "\<forall>xa\<in>carrier M. x = f xa \<longrightarrow>
          x \<in> linear_span R N (carrier R) {y. \<exists>x\<in>H. y = f x}")
 apply blast apply (thin_tac "\<exists>xa\<in>carrier M. x = f xa")
 apply (rule ballI) apply (rule impI) apply (fold image_def)
 apply (subgoal_tac "xa \<in> linear_span R M (carrier R) H")
 prefer 2 apply simp
 apply (thin_tac "linear_span R M (carrier R) H = carrier M")
 apply (thin_tac "f \<in> extensional (carrier M)")
 apply (simp add:linear_span_def [of "R" "M"])
apply (case_tac "H = {}") apply (simp add:linear_span_def)
 apply (simp add:mHom_0) apply simp
 apply auto
 apply (subgoal_tac "f (linear_combination R M n s fa) \<in> linear_span R N (carrier R) (f ` H)") apply simp
 apply (thin_tac "f (linear_combination R M n s fa) \<notin> linear_span R N (carrier R) (f ` H)")
 apply (rule linmap_im_linspan, assumption+ )
 apply (rule whole_ideal, assumption+)
done

lemma surjec_finitely_gen:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
       surjec\<^sub>M\<^sub>,\<^sub>N f; M fgover R\<rbrakk>  \<Longrightarrow> N fgover R"
apply (simp add:fGOver_def)
 apply (subgoal_tac "\<forall>H. finite_generator R M H \<longrightarrow> (\<exists>H. finite_generator R N H)") apply blast apply (thin_tac "\<exists>H. finite_generator R M H")
 apply (rule allI) apply (rule impI)
 apply (simp add:finite_generator_def [of "R" "M"]) apply (erule conjE)
 apply (frule_tac H = H in surjec_generator[of "R" "M" "N" "f"], assumption+)
apply (simp add:finite_generator_def [of "R" "N"])
 apply (frule_tac F = H and h = f in finite_imageI)
 apply blast
done



 subsection "4-1. sum up coefficients "
 text{* Symbolic calculation. *}

lemma similar_termTr:"\<lbrakk>ring R; ideal R A; R module M; a \<in> A\<rbrakk> \<Longrightarrow>
 \<forall>s. \<forall>f. s\<in>Nset n \<rightarrow> A \<and> f\<in> Nset n \<rightarrow> carrier M \<and> m \<in> f ` (Nset n) \<longrightarrow>(\<exists>t\<in>Nset n \<rightarrow> A. eSum M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M a \<star>\<^sub>M m = eSum M (\<lambda>j. t j \<star>\<^sub>M (f j)) n )"
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (simp add:Nset_def)
 apply (subgoal_tac "(0::nat) \<in> {0}")
 apply (frule_tac a = "s 0" and b = a and m = "f 0" in sprod_distrib1 [of "R" "M"], assumption+)
  apply (simp add:funcset_mem) apply (simp add:funcset_mem ideal_subset)
  apply (simp add:ideal_subset)
  apply (simp add:funcset_mem) apply (rotate_tac -1)
  apply (frule sym) apply (thin_tac "(s 0 +\<^sub>R a) \<star>\<^sub>M (f 0) = s 0 \<star>\<^sub>M (f 0) +\<^sub>M  a \<star>\<^sub>M (f 0)")
   apply (subgoal_tac "(\<lambda>k\<in>Nset 0. (s 0 +\<^sub>R a)) \<in> {0} \<rightarrow> A")
   apply (subgoal_tac "s 0 \<star>\<^sub>M (f 0) +\<^sub>M  a \<star>\<^sub>M (f 0)
                          = ((\<lambda>k\<in>Nset 0.  s 0 +\<^sub>R a) 0) \<star>\<^sub>M (f 0)")
   apply (thin_tac " s 0 \<star>\<^sub>M (f 0) +\<^sub>M  a \<star>\<^sub>M (f 0) =  ( s 0 +\<^sub>R a) \<star>\<^sub>M (f 0)")
  apply blast
  apply (simp add:Nset_def)
  apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
  apply (rule ideal_pOp_closed, assumption+)
  apply (subgoal_tac "(0::nat) \<in> {0}")
  apply (simp add:funcset_mem) apply simp apply assumption apply simp
(** n **)
apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (simp del:eSum_Suc add:image_def)
 apply (subgoal_tac "\<forall>x\<in>Nset (Suc n). m = f x \<longrightarrow> (\<exists>t\<in>Nset (Suc n) \<rightarrow>
 A. e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) (Suc n) +\<^sub>M  a \<star>\<^sub>M m =
             e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (f j)) (Suc n))")
 apply (thin_tac "\<forall>s f. s \<in> Nset n \<rightarrow> A \<and> f \<in> Nset n \<rightarrow> carrier M \<and>
 (\<exists>x\<in>Nset n. m = f x) \<longrightarrow> (\<exists>t\<in>Nset n \<rightarrow>  A.
   e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n +\<^sub>M  a \<star>\<^sub>M m =   e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (f j)) n)")
 apply blast
 apply (thin_tac "\<exists>x\<in>Nset (Suc n). m = f x")
 apply (rule ballI) apply (rule impI)
 apply (case_tac "x = Suc n")  (***** case x = Suc n ********)
 apply (thin_tac "\<forall>s f. s \<in> Nset n \<rightarrow> A \<and> f \<in> Nset n \<rightarrow> carrier M \<and>
 (\<exists>x\<in>Nset n. m = f x) \<longrightarrow>  (\<exists>t\<in>Nset n \<rightarrow> A.
  e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n +\<^sub>M  a \<star>\<^sub>M m = e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (f j)) n)")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "(\<lambda>j. s j \<star>\<^sub>M (f j)) \<in> Nset n \<rightarrow> carrier M")
 apply (frule_tac n = n and i = n and f = "\<lambda>j. s j \<star>\<^sub>M (f j)" in
                                               eSum_mem [of "M"], assumption+)
 apply (simp add:Nset_def) apply simp
 apply (frule_tac a = "s (Suc n)" and m = "f (Suc n)" in sprod_mem [of "R" "M"], assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
 apply (frule_tac a = a and m = "f (Suc n)" in sprod_mem [of "R" "M"], assumption+) apply (simp add:ideal_subset) apply (simp add:funcset_mem)
 apply (frule_tac a = "s (Suc n)" and b = a and m = "f (Suc n)" in
       sprod_distrib1 [of "R" "M"], assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:ideal_subset)
 apply (simp add:funcset_mem)
 apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "(s (Suc n) +\<^sub>R a) \<star>\<^sub>M (f (Suc n)) =
          s (Suc n) \<star>\<^sub>M (f (Suc n)) +\<^sub>M  a \<star>\<^sub>M (f (Suc n))")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_pOp_assoc, assumption+) apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n \<in> carrier M")
 apply (thin_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) \<in> carrier M")
 apply (thin_tac "a \<star>\<^sub>M (f (Suc n)) \<in> carrier M")
 apply (thin_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) +\<^sub>M  a \<star>\<^sub>M (f (Suc n)) =
           ( s (Suc n) +\<^sub>R a) \<star>\<^sub>M (f (Suc n))")
 apply (subgoal_tac "jointfun n s 0 (\<lambda>l.  ( s (Suc n) +\<^sub>R a))
  \<in> Nset (Suc n) \<rightarrow> A")
 apply (subgoal_tac "
e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n +\<^sub>M  ( s (Suc n) +\<^sub>R a) \<star>\<^sub>M (f (Suc n)) =
eSum M (\<lambda>k. (jointfun n s 0 (\<lambda>l.  ( s (Suc n) +\<^sub>R a))) k \<star>\<^sub>M (f k)) (Suc n)")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M  ((s (Suc n) +\<^sub>R a) \<star>\<^sub>M (f (Suc n))) =  e\<Sigma> M (\<lambda>k. (jointfun n s 0 (\<lambda>l.  s (Suc n) +\<^sub>R a)) k \<star>\<^sub>M (f k)) n +\<^sub>M
         ((jointfun n s 0 (\<lambda>l.  s (Suc n) +\<^sub>R a)) (Suc n) \<star>\<^sub>M (f (Suc n)))")
 apply blast
 apply (simp add:jointfun_def Nset_def)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n =
    e\<Sigma> M (\<lambda>k.  (if k \<le> n then s k else  s (Suc n) +\<^sub>R a) \<star>\<^sub>M (f k)) n ")
 apply simp
apply (rule eSum_eq, assumption+)  apply (rule univar_func_test)
 apply (rule ballI)  apply (rule sprod_mem, assumption+)
 apply (simp add:Nset_def funcset_mem ideal_subset) apply (simp add:Nset_def funcset_mem)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (rule sprod_mem, assumption+)  apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (simp add:Nset_def funcset_mem)
 apply (rule ballI) apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def jointfun_def)
 apply (case_tac "xa \<le> n") apply simp apply (simp add:funcset_mem)
 apply simp
 apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:funcset_mem) apply assumption
apply (rule univar_func_test)
 apply (rule ballI) apply (rule sprod_mem, assumption+)
 apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (simp add:Nset_def funcset_mem)
 apply (frule Nset_pre, assumption+)
 apply (frule func_pre [of _ _ "A"])
 apply (frule func_pre [of _ _ "carrier M"])
 apply (subgoal_tac "\<exists>x\<in>Nset n. m = f x") prefer 2 apply blast
apply (subgoal_tac "\<exists>t\<in>Nset n \<rightarrow> A.
  e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M  a \<star>\<^sub>M m = e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (f j)) n")
prefer 2 apply simp apply (thin_tac "\<exists>x\<in>Nset n. m = f x")
apply (thin_tac "\<forall>s f. s \<in> Nset n \<rightarrow> A \<and> f \<in> Nset n \<rightarrow> carrier M \<and> (\<exists>x\<in>Nset n. m = f x) \<longrightarrow> (\<exists>t\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M (a \<star>\<^sub>M m) = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (f j)) n)")
apply auto
apply (frule_tac s = s and n = n and m = f in linear_combination_mem [of "R" "M" "A" "carrier M"], assumption+)
 apply simp apply assumption+
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) \<in> carrier M")
 apply (subgoal_tac "a \<star>\<^sub>M (f x) \<in> carrier M")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_pOp_assoc, assumption+)
 apply (frule_tac x = "s (Suc n) \<star>\<^sub>M (f (Suc n))" and y = "a \<star>\<^sub>M (f x)" in
 ag_pOp_commute [of "M"], assumption+) apply simp
 apply (subst ag_pOp_assoc [THEN sym], assumption+)
 apply (thin_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) +\<^sub>M  a \<star>\<^sub>M (f x) =
            a \<star>\<^sub>M (f x) +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n)))")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M  a \<star>\<^sub>M (f x)
                       = e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (f j)) n")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n \<in> carrier M")
 apply (thin_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) \<in> carrier M")
 apply (thin_tac "a \<star>\<^sub>M (f x) \<in> carrier M")
 apply (subgoal_tac "jointfun n t 0 (\<lambda>j. s (Suc n)) \<in> Nset (Suc n) \<rightarrow> A")
apply (subgoal_tac "e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (f j)) n +\<^sub>M (s (Suc n) \<star>\<^sub>M (f (Suc n))) =
 e\<Sigma> M (\<lambda>j. (jointfun n t 0 (\<lambda>j. s (Suc n))) j \<star>\<^sub>M (f j)) n +\<^sub>M
    ((jointfun n t 0 (\<lambda>j. s (Suc n))) (Suc n) \<star>\<^sub>M (f (Suc n)))")
apply simp
apply blast
 apply (simp add:Nset_def jointfun_def)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (f j)) n =
  e\<Sigma> M (\<lambda>j.  (if j \<le> n then t j else s (Suc n)) \<star>\<^sub>M (f j)) n") apply simp
apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (simp add:Nset_def funcset_mem)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def funcset_mem)
 apply (rule sprod_mem, assumption+) apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (simp add:Nset_def funcset_mem)
 apply (rule ballI) apply (simp add:Nset_def)
 apply (subgoal_tac "(\<lambda>j. s (Suc n)) \<in> Nset 0 \<rightarrow> A")
 apply (frule_tac f = t and n = n and A = A and g = "\<lambda>j. s (Suc n)"
 and m = 0 and B = A in jointfun_hom, assumption+)
 apply simp
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (rule sprod_mem, assumption+) apply (simp add:ideal_subset)
apply (simp add:Nset_def funcset_mem)
apply (rule sprod_mem, assumption+)
 apply (simp add:Nset_def funcset_mem ideal_subset)
 apply (simp add:Nset_def funcset_mem)
done

lemma similar_term1:"\<lbrakk>ring R; ideal R A; R module M; a \<in> A;s\<in>Nset n \<rightarrow> A; f\<in> Nset n \<rightarrow> carrier M; m \<in> f ` (Nset n) \<rbrakk> \<Longrightarrow>
\<exists>t\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M  a \<star>\<^sub>M m =
             e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (f j)) n"
apply (simp add:similar_termTr)
done

lemma same_togetherTr:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M \<rbrakk> \<Longrightarrow> \<forall>s. \<forall>f. s\<in>Nset n \<rightarrow> A \<and> f\<in> Nset n \<rightarrow> H \<longrightarrow> (\<exists>t \<in> Nset (card (f ` (Nset n)) - Suc 0) \<rightarrow> A. \<exists>g\<in> Nset (card (f ` (Nset n)) - Suc 0) \<rightarrow> f ` (Nset n). surj_to g (Nset (card (f ` (Nset n)) - Suc 0)) (f ` (Nset n)) \<and>  eSum M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = eSum M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` (Nset n)) - Suc 0))"
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (simp add:Nset_def)
 apply (subgoal_tac "f \<in> {0::nat} \<rightarrow> {f 0}")
 apply (subgoal_tac "surj_to f {0::nat} {f 0}")
 apply blast
 apply (simp add:surj_to_def)
 apply (rule univar_func_test) apply (rule ballI) apply simp
apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"])
 apply (frule func_pre [of _ _ "H"])
apply (subgoal_tac "\<exists>t\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> A.
\<exists>g\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> f ` Nset n.  surj_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n)\<and> e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n = e\<Sigma> M (\<lambda>k.  t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0)")
 prefer 2 apply simp
 apply (thin_tac "\<forall>s f. s \<in> Nset n \<rightarrow> A \<and> f \<in> Nset n \<rightarrow> H \<longrightarrow>
 (\<exists>t\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> A.
\<exists>g\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> f ` Nset n. surj_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n) \<and> e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =
     e\<Sigma> M (\<lambda>k.  t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0))")
apply (subgoal_tac "\<forall>t\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> A.
\<forall>g\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> f ` Nset n. surj_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n) \<and> e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0) \<longrightarrow> (\<exists>t\<in>Nset (card (f ` Nset (Suc n)) - (Suc 0)) \<rightarrow> A. \<exists>g\<in>Nset (card (f ` Nset (Suc n)) - (Suc 0)) \<rightarrow> f ` Nset (Suc n). surj_to g (Nset (card (f ` Nset (Suc n)) - Suc 0)) (f ` Nset (Suc n))  \<and> e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) (Suc n) =
   e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset (Suc n)) - (Suc 0)))")
apply blast
 apply (thin_tac "\<exists>t\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> A.
\<exists>g\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> f ` Nset n. surj_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n) \<and> e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0)")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n =
          e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0)")
 apply (case_tac "f (Suc n) \<in> g ` (Nset (card (f ` Nset n) - Suc 0))")
  apply (subgoal_tac "f ` (Nset (Suc n)) = f ` (Nset n)") apply simp
 apply (frule_tac a = "s (Suc n)" and s = t and n = "card (f ` Nset n) - Suc 0" and f = g and m = "f (Suc n)" in similar_term1 [of "R" "A" "M"], assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply assumption
 apply (frule_tac f = f and A = "Nset n" and ?A1.0 = "Nset n" in
  image_sub) apply simp
 apply (rule extend_fun, assumption+)
 apply (rule subset_trans, assumption+)
 apply (subgoal_tac "\<forall>ta\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> A.  e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (g j)) (card (f ` Nset n) - (Suc 0)) +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n))) = e\<Sigma> M (\<lambda>j.  ta j \<star>\<^sub>M (g j)) (card (f ` Nset n) - (Suc 0)) \<longrightarrow> (\<exists>ta\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> A.  \<exists>ga\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> f ` Nset n. surj_to ga (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n) \<and> e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - (Suc 0)) +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n))) = e\<Sigma> M (\<lambda>k. ta k \<star>\<^sub>M (ga k)) (card (f ` Nset n) - (Suc 0)))")
 apply (thin_tac "f ` Nset (Suc n) = f ` Nset n")
 apply (thin_tac "f (Suc n) \<in> g ` Nset (card (f ` Nset n) - Suc 0)")
 apply (thin_tac "surj_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n)")
 apply (thin_tac "g \<in> Nset (card (f ` Nset n) - Suc 0) \<rightarrow> f ` Nset n")
 apply (thin_tac "t \<in> Nset (card (f ` Nset n) - Suc 0) \<rightarrow> A")
 apply blast
 apply (thin_tac "\<exists>ta\<in>Nset (card (f ` Nset n) - (Suc 0)) \<rightarrow> A.  e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (g j)) (card (f ` Nset n) - (Suc 0)) +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n))) = e\<Sigma> M (\<lambda>j.  ta j \<star>\<^sub>M (g j)) (card (f ` Nset n) - (Suc 0))")
 apply (rule ballI) apply (rule impI) apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (g j)) (card (f ` Nset n) - Suc 0) +\<^sub>M
 (s (Suc n) \<star>\<^sub>M (f (Suc n))) =
          e\<Sigma> M (\<lambda>j. ta j \<star>\<^sub>M (g j)) (card (f ` Nset n) - Suc 0)")
 apply blast
apply (rule equalityI)
 apply (subst Nset_un)
 apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub) apply (rule subsetI) apply (simp add:Nset_def)
apply (frule_tac f = g and A = "Nset (card (f ` Nset n) - Suc 0)" and ?A1.0 = "Nset (card (f ` Nset n) - Suc 0)" in image_sub) apply simp
 apply (simp add:subsetD)
 apply (subgoal_tac "Nset n \<subseteq> Nset (Suc n)")
 apply (rule_tac f = f and A = "Nset (Suc n)" and B = H and
 ?A1.0 = "Nset n" and ?A2.0 = "Nset (Suc n)" in im_set_mono, assumption+)
 apply simp apply (simp add:Nsetn_sub)
 apply (simp add:surj_to_def)
 apply (subgoal_tac "jointfun (card (f ` Nset n) - Suc 0) t 0 (\<lambda>l\<in>Nset 0. s (Suc n)) \<in> Nset (card (f ` Nset (Suc n)) - Suc 0) \<rightarrow> A")
 apply (subgoal_tac "jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n)) \<in> Nset (card (f ` Nset (Suc n)) - Suc 0) \<rightarrow> f ` (Nset (Suc n))")
 apply (subgoal_tac "(jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n))) ` (Nset (card (f ` Nset (Suc n)) - Suc 0)) = f ` Nset (Suc n)")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0) +\<^sub>M
 (s (Suc n) \<star>\<^sub>M (f (Suc n))) = e\<Sigma> M (\<lambda>k. (jointfun (card (f ` Nset n) - Suc 0) t 0 (\<lambda>l\<in>Nset 0. s (Suc n))) k \<star>\<^sub>M (((jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n)))) k)) (card (f ` Nset (Suc n)) - Suc 0)")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0) +\<^sub>M
 (s (Suc n) \<star>\<^sub>M (f (Suc n))) = e\<Sigma> M (\<lambda>k. (jointfun (card (f ` Nset n) - Suc 0) t 0 (\<lambda>l\<in>Nset 0. s (Suc n))) k \<star>\<^sub>M (((jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n)))) k)) (card (f ` Nset (Suc n)) - Suc 0)")
 apply blast
 apply (subgoal_tac "card (f ` Nset (Suc n)) - Suc 0 = Suc (card (f ` Nset n) - Suc 0)") apply simp
 apply (subgoal_tac "(jointfun (card (f ` Nset n) - Suc 0) t 0
 (\<lambda>l\<in>Nset 0. s (Suc n))) (Suc (card (f ` Nset n) - Suc 0)) \<star>\<^sub>M ((jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n)))
  (Suc (card (f ` Nset n) - Suc 0))) =  s (Suc n) \<star>\<^sub>M (f (Suc n))")
 prefer 2 apply (simp add:jointfun_def slide_def sliden_def)
 apply (simp add:Nset_def) apply simp
 apply (thin_tac "(jointfun (card (f ` Nset n) - Suc 0) t 0
 (\<lambda>l\<in>Nset 0. s (Suc n))) (Suc (card (f ` Nset n) - Suc 0)) \<star>\<^sub>M ((jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n)))
  (Suc (card (f ` Nset n) - Suc 0))) =  s (Suc n) \<star>\<^sub>M (f (Suc n))")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0)
 = e\<Sigma> M (\<lambda>k. (jointfun (card (f ` Nset n) - Suc 0) t 0 (\<lambda>l\<in>Nset 0. s (Suc n)))
 k \<star>\<^sub>M ((jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n))) k)) (card (f ` Nset n) - Suc 0)") apply simp
 apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (frule_tac f = f and A = "Nset n" and B = H and
          ?A1.0 = "Nset n" in image_sub) apply simp
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<le> card (f ` Nset n) - Suc 0")
 apply (simp add:jointfun_def)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (frule_tac f = f and A = "Nset n" and B = H and
          ?A1.0 = "Nset n" in image_sub) apply simp
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
apply (rule ballI)
 apply (subgoal_tac "l \<le> card (f ` Nset n) - Suc 0")
 apply (simp add:jointfun_def) apply (simp add:Nset_def)
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub) apply (rule subsetI) apply (simp add:Nset_def)
 apply simp apply (subst card_insert_disjoint)
 apply (rule finite_imageI) apply (simp add:finite_Nset) apply assumption
 apply (subgoal_tac "0 < card (f ` Nset n)") apply simp
 apply (rule  nonempty_card_pos)
  apply (rule finite_imageI) apply (simp add:finite_Nset)
  apply (subgoal_tac "f 0 \<in> f ` Nset n") apply (simp add:nonempty)
  apply (subgoal_tac "0 \<in> Nset n") apply (simp add:nonempty)
  apply (simp add:Nset_def) apply (subgoal_tac "0 \<in> Nset n")
  apply (simp add:mem_in_image) apply (simp add:Nset_def)
 apply (subgoal_tac "(\<lambda>l\<in>Nset 0. f (Suc n)) \<in> Nset 0 \<rightarrow> {f (Suc n)}")
 apply (frule_tac f = g and n = "card (f ` Nset n) - Suc 0" and A = "f ` Nset n" and g = "\<lambda>l\<in>Nset 0. f (Suc n)" and m = 0 and B = "{f (Suc n)}" in im_jointfun, assumption+)
 apply simp apply (subgoal_tac "Nset (Suc (card (f ` Nset n) - Suc 0)) =
 Nset (card (f ` Nset (Suc n)) - Suc 0)") apply simp
 apply (subgoal_tac "(\<lambda>l\<in>Nset 0. f (Suc n)) ` Nset 0 = {f (Suc n)}")
 apply simp apply (subst Nset_un)
 apply (subst im_set_un, assumption+)  apply (simp add:Nsetn_sub)
 apply (rule subsetI) apply (simp add:Nset_def) apply simp
 apply (simp add:image_def) apply (rule equalityI) apply (rule subsetI)
 apply (simp add:CollectI) apply (rule subsetI) apply (simp add:CollectI)
 apply (simp add:Nset_def)
apply (thin_tac "jointfun (card (f ` Nset n) - Suc 0) t 0 (\<lambda>l\<in>Nset 0. s (Suc n)) \<in> Nset (card (f ` Nset (Suc n)) - Suc 0) \<rightarrow> A")
 apply (thin_tac "jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0. f (Suc n)) \<in> Nset (card (f ` Nset (Suc n)) - Suc 0) \<rightarrow> f ` Nset (Suc n)")
 apply (thin_tac "jointfun (card (f ` Nset n) - Suc 0) g 0 (\<lambda>l\<in>Nset 0.
 f (Suc n)) ` Nset (Suc (card (f ` Nset n) - Suc 0)) =
          f ` Nset n \<union> (\<lambda>l. f (Suc n)) ` Nset 0")
 apply (subgoal_tac "Suc (card (f ` Nset n) - Suc 0) = card (f ` Nset (Suc n)) - Suc 0") apply simp
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub)  apply (rule subsetI) apply (simp add:Nset_def)
 apply simp apply (subst card_insert_disjoint) apply (rule finite_imageI)
 apply (simp add:finite_Nset) apply assumption
 apply (subgoal_tac "0 < card (f ` Nset n)") apply simp
 apply (rule  nonempty_card_pos) apply (rule finite_imageI)
 apply (simp add:finite_Nset) apply (subgoal_tac "f 0 \<in> f ` Nset n")
 apply (simp add:nonempty) apply (subgoal_tac "0 \<in> Nset n")
 apply (simp add:nonempty) apply (simp add:Nset_def)
 apply (subgoal_tac "0 \<in> Nset n") apply (simp add:mem_in_image)
 apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
apply (frule_tac f = g and n = "card (f ` Nset n) - Suc 0" and
 A = "f ` Nset n" and g = "\<lambda>l\<in>Nset 0. f (Suc n)" and m = 0 and B = "{f (Suc n)}" in  jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply simp
 apply (subgoal_tac  "Nset (Suc (card (f ` Nset n) - Suc 0)) =
 Nset (card (f ` Nset (Suc n)) - Suc 0)") apply simp
 apply (subgoal_tac "insert (f (Suc n)) (f ` Nset n) = f ` (Nset (Suc n))")
 apply simp
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub) apply (rule subsetI) apply (simp add:Nset_def)
 apply simp
apply (subgoal_tac "Suc (card (f ` Nset n) - Suc 0) = card (f ` Nset (Suc n)) - Suc 0") apply simp
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub)  apply (rule subsetI) apply (simp add:Nset_def)
 apply simp apply (subst card_insert_disjoint) apply (rule finite_imageI)
 apply (simp add:finite_Nset) apply assumption
 apply (subgoal_tac "0 < card (f ` Nset n)") apply simp
 apply (rule  nonempty_card_pos) apply (rule finite_imageI)
 apply (simp add:finite_Nset) apply (subgoal_tac "f 0 \<in> f ` Nset n")
 apply (simp add:nonempty) apply (subgoal_tac "0 \<in> Nset n")
 apply (simp add:nonempty) apply (simp add:Nset_def)
 apply (subgoal_tac "0 \<in> Nset n") apply (simp add:mem_in_image)
 apply (simp add:Nset_def)
apply (frule_tac f = t and n = "card (f ` Nset n) - Suc 0" and
 A = A and g = "\<lambda>l\<in>Nset 0. s (Suc n)" and m = 0 and B = A in jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:funcset_mem) apply simp
 apply (subgoal_tac  "Nset (Suc (card (f ` Nset n) - Suc 0)) =
 Nset (card (f ` Nset (Suc n)) - Suc 0)") apply simp
apply (subgoal_tac "Suc (card (f ` Nset n) - Suc 0) = card (f ` Nset (Suc n)) - Suc 0") apply simp
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub)  apply (rule subsetI) apply (simp add:Nset_def)
 apply simp apply (subst card_insert_disjoint) apply (rule finite_imageI)
 apply (simp add:finite_Nset) apply assumption
 apply (subgoal_tac "0 < card (f ` Nset n)") apply simp
 apply (rule  nonempty_card_pos) apply (rule finite_imageI)
 apply (simp add:finite_Nset) apply (subgoal_tac "f 0 \<in> f ` Nset n")
 apply (simp add:nonempty) apply (subgoal_tac "0 \<in> Nset n")
 apply (simp add:nonempty) apply (simp add:Nset_def)
 apply (subgoal_tac "0 \<in> Nset n") apply (simp add:mem_in_image)
 apply (simp add:Nset_def)
done

 (* H shall be a generator *)
lemma same_together:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M; s \<in> Nset n \<rightarrow> A; f \<in>  Nset n \<rightarrow> H\<rbrakk> \<Longrightarrow> \<exists>t \<in> Nset (card (f ` (Nset n)) - Suc 0) \<rightarrow> A. \<exists>g\<in> Nset (card (f ` (Nset n)) - Suc 0) \<rightarrow> f ` (Nset n). surj_to g (Nset (card (f ` (Nset n)) - Suc 0)) (f ` (Nset n)) \<and>  eSum M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = eSum M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` (Nset n)) - Suc 0)"
apply (simp add:same_togetherTr)
done

lemma one_last:"\<lbrakk>ring R; ideal R A; R module M; H \<subseteq> carrier M; s \<in> Nset (Suc n) \<rightarrow> A; f \<in> Nset (Suc n) \<rightarrow> H; bij_to f (Nset (Suc n)) H; j \<in> Nset (Suc n); j \<noteq> (Suc n)\<rbrakk> \<Longrightarrow> \<exists>t\<in> Nset (Suc n) \<rightarrow> A. \<exists>g\<in> Nset (Suc n) \<rightarrow> H.  eSum M (\<lambda>k. s k \<star>\<^sub>M (f k)) (Suc n) = eSum M (\<lambda>k. t k \<star>\<^sub>M (g k)) (Suc n) \<and> g (Suc n) = f j \<and> t (Suc n) = s j \<and> bij_to g (Nset (Suc n)) H"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (subgoal_tac "(\<lambda>k.  s k \<star>\<^sub>M (f k)) \<in> Nset (Suc n) \<rightarrow> carrier M")
apply (subgoal_tac "transpos j (Suc n) \<in> Nset (Suc n) \<rightarrow> Nset (Suc n)")
apply (subgoal_tac "inj_on (transpos j (Suc n)) (Nset (Suc n))")
apply (frule_tac f1 = "\<lambda>k.  s k \<star>\<^sub>M (f k)" and n1 = n and h1 = "transpos j (Suc n)" in addition2 [THEN sym, of "M"], assumption+)
apply (simp del:eSum_Suc)
prefer 2 apply (rule transpos_inj, assumption+) apply (simp add:Nset_def)
 apply assumption+
prefer 2 apply (rule transpos_hom, assumption+) apply (simp add:Nset_def)
 apply assumption+
prefer 2  apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem subsetD)
 apply (subgoal_tac "cmp s (transpos j (Suc n)) \<in> Nset (Suc n) \<rightarrow> A")
 apply (subgoal_tac "cmp f (transpos j (Suc n)) \<in> Nset (Suc n) \<rightarrow> H")
 apply (subgoal_tac "e\<Sigma> M (cmp (\<lambda>k. s k \<star>\<^sub>M (f k)) (transpos j (Suc n))) (Suc n) =e\<Sigma> M (\<lambda>k. (cmp s (transpos j (Suc n))) k \<star>\<^sub>M ((cmp f (transpos j (Suc n))) k)) (Suc n)")
 apply (simp del:eSum_Suc)
 apply (subgoal_tac "bij_to (cmp f (transpos j (Suc n))) (Nset (Suc n)) H")
 apply (subgoal_tac "(cmp f (transpos j (Suc n))) (Suc n) = f j")
 apply (subgoal_tac "(cmp s (transpos j (Suc n))) (Suc n) = s j")
 apply blast
 apply (simp add:cmp_def)
 apply (subst transpos_ij_2, assumption+) apply (simp add:Nset_def)
 apply assumption apply simp
 apply (simp add:cmp_def)
 apply (subst transpos_ij_2, assumption+) apply (simp add:Nset_def)
 apply assumption apply simp
prefer 2
apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule_tac f = "transpos j (Suc n)" and A = "Nset (Suc n)" and
 B = "Nset (Suc n)" and g = "\<lambda>k. s k \<star>\<^sub>M (f k)" in cmp_fun, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:cmp_def)
 apply (frule_tac x = x in funcset_mem [of "transpos j (Suc n)"
 "Nset (Suc n)" "Nset (Suc n)"], assumption+)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem subsetD)
apply (rule ballI)
 apply (simp add:cmp_def)
prefer 2  apply (simp add:cmp_fun)
prefer 2 apply (simp add:cmp_fun)
 apply (thin_tac "e\<Sigma> M (\<lambda>k. s k \<star>\<^sub>M (f k)) (Suc n) = e\<Sigma> M (\<lambda>k. (cmp s (transpos j (Suc n))) k \<star>\<^sub>M ((cmp f (transpos j (Suc n)) k))) (Suc n)")
 apply (thin_tac " e\<Sigma> M (cmp (\<lambda>k. s k \<star>\<^sub>M (f k)) (transpos j (Suc n))) (Suc n) = e\<Sigma> M (\<lambda>k. (cmp s (transpos j (Suc n))) k \<star>\<^sub>M ((cmp f (transpos j (Suc n)) k))) (Suc n)")
 apply (simp add:bij_to_def)
 apply (simp add:cmp_inj)
 apply (rule cmp_surj, assumption+)
 apply (rule transpos_surjec, assumption+) apply (simp add:Nset_def)
 apply assumption+ apply simp
done

lemma finite_lin_spanTr1:"\<lbrakk>ring R; R module M; ideal R A; z \<in> carrier M\<rbrakk> \<Longrightarrow>
h \<in> Nset n \<rightarrow> {z} \<and> t \<in> Nset n \<rightarrow> A  \<longrightarrow> (\<exists>s\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n =  s 0 \<star>\<^sub>M z)"
apply (induct_tac n)
 apply (rule impI)
 apply (erule conjE)+ apply (simp add:Nset_def)
 apply (subgoal_tac "(0::nat) \<in> {0}")
 apply (frule_tac f = h and A = "{0}" and B = "{z}" and x = 0 in funcset_mem)
 apply assumption apply simp apply blast apply simp
apply (rule impI) apply (erule conjE)+
 apply (frule func_pre [of _ _ "{z}"])
 apply (frule func_pre [of _ _ "A"])
apply (subgoal_tac "\<exists>s\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n =  s 0 \<star>\<^sub>M z")
 prefer 2 apply simp
 apply (subgoal_tac "\<forall>r\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n = r 0 \<star>\<^sub>M z \<longrightarrow>
  (\<exists>s\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) (Suc n) = s 0 \<star>\<^sub>M z)")
 apply blast apply (thin_tac "\<exists>s\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n =  s 0 \<star>\<^sub>M z")
 apply (rule ballI) apply (rule impI) apply simp
 apply (frule_tac f = h and A = "Nset (Suc n)" and B = "{z}" and x = "Suc n" in funcset_mem) apply (simp add:Nset_def) apply simp
 apply (subst sprod_distrib1 [THEN sym], assumption+)
 apply (subgoal_tac "0 \<in> Nset 0") apply (simp add:funcset_mem ideal_subset)
 apply (simp add:Nset_def) apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem ideal_subset) apply (simp add:Nset_def)
 apply assumption
apply (subgoal_tac "(\<lambda>l\<in>Nset 0. (r 0 +\<^sub>R (t (Suc n)))) \<in> Nset 0 \<rightarrow> A")
apply (subgoal_tac "( r 0 +\<^sub>R (t (Suc n))) \<star>\<^sub>M z = (\<lambda>l\<in>Nset 0. (r 0 +\<^sub>R (t (Suc n)))) 0 \<star>\<^sub>M z") apply blast
 apply (subgoal_tac "0 \<in> Nset 0")
 apply simp apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (rule ideal_pOp_closed, assumption+)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
done

lemma single_span:"\<lbrakk>ring R; R module M; ideal R A; z \<in> carrier M;
h \<in> Nset n \<rightarrow> {z}; t \<in> Nset n \<rightarrow> A\<rbrakk> \<Longrightarrow> \<exists>s\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n =  s 0 \<star>\<^sub>M z"
apply (simp add:finite_lin_spanTr1)
done

lemma finite_lin_spanTr2:"\<lbrakk>ring R; R module M; ideal R A; \<forall>m. (\<exists>na. \<exists>f\<in>Nset na \<rightarrow> h ` Nset n. \<exists>s\<in>Nset na \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na) \<longrightarrow> (\<exists>s\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) n); h \<in> Nset (Suc n) \<rightarrow> carrier M; f \<in> Nset na \<rightarrow> h ` Nset n; s \<in> Nset na \<rightarrow> A; m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na \<rbrakk> \<Longrightarrow> \<exists>sa\<in>Nset (Suc n) \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (h j)) n +\<^sub>M  (sa (Suc n) \<star>\<^sub>M (h (Suc n)))"
 apply (subgoal_tac "\<exists>l\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j.  l j \<star>\<^sub>M (h j)) n")
 prefer 2
 apply (thin_tac "h \<in> Nset (Suc n) \<rightarrow> carrier M")
 apply blast
 apply (thin_tac " \<forall>m. (\<exists>na. \<exists>f\<in>Nset na \<rightarrow> h ` Nset n.
  \<exists>s\<in>Nset na \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na) \<longrightarrow>
              (\<exists>s\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (h j)) n)")
 apply (subgoal_tac "\<forall>l\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n \<longrightarrow> (\<exists>sa\<in>Nset (Suc n) \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (h j)) n +\<^sub>M  (sa (Suc n) \<star>\<^sub>M (h (Suc n))))")
 apply blast
 apply (thin_tac "\<exists>l\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n")
 apply (rule ballI) apply (rule impI)
 apply (frule sym) apply (thin_tac "m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na")
 apply simp
 apply (thin_tac "m = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n")
 apply (subgoal_tac "jointfun n l 0 (\<lambda>x\<in>Nset 0. (0\<^sub>R)) \<in> Nset (Suc n) \<rightarrow> A")
 apply (subgoal_tac " e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n =
  e\<Sigma> M (\<lambda>j. (jointfun n l 0 (\<lambda>x\<in>Nset 0. (0\<^sub>R))) j \<star>\<^sub>M (h j)) n +\<^sub>M  ((jointfun n l 0 (\<lambda>x\<in>Nset 0. (0\<^sub>R))) (Suc n)) \<star>\<^sub>M (h (Suc n))")
 apply blast
 apply (subgoal_tac "jointfun n l 0 (\<lambda>x\<in>Nset 0. 0\<^sub>R) (Suc n) \<star>\<^sub>M (h (Suc n)) =
  0\<^sub>M") apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. jointfun n l 0 (\<lambda>x\<in>Nset 0. 0\<^sub>R) j \<star>\<^sub>M (h j)) n =
 e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n ") apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_r_zero, assumption+)
 apply (subgoal_tac "(\<lambda>j. l j \<star>\<^sub>M (h j)) \<in> Nset n \<rightarrow> carrier M")
 apply (rule eSum_mem, assumption+) apply (simp add:n_in_Nsetn)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (frule func_pre [of "h" _ "carrier M"])
 apply (simp add:funcset_mem) apply simp
 apply (rule eSum_eq)
 apply (rule module_is_ag [of "R" "M"], assumption+)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (frule_tac x = x and n = n in Nset_le)
 apply (insert Nset_nonempty[of "0"])
 apply (simp add:jointfun_def)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (frule func_pre [of "h" _ "carrier M"])
 apply (simp add:funcset_mem)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (frule func_pre [of "h" _ "carrier M"])
 apply (simp add:funcset_mem)
apply (rule ballI)
 apply (frule_tac x = la and n = n in Nset_le)
 apply (simp add:jointfun_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:jointfun_def sliden_def slide_def)
 apply (rule sprod_0_m, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:n_in_Nsetn)+
apply (frule_tac f = l and n = n and A = A and g = "\<lambda>x\<in>Nset 0. 0\<^sub>R" and m = 0
      and B = A in jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:ideal_zero) apply simp
done (** koko **)

constdefs
 coeff_at_k::"[('r, 'm) RingType_scheme, 'r, nat] \<Rightarrow> (nat \<Rightarrow> 'r)"
 "coeff_at_k R a k  == \<lambda>j. if j = k then a else (0\<^sub>R)"

lemma card_Nset_im:"\<lbrakk>f \<in> Nset n \<rightarrow> A\<rbrakk> \<Longrightarrow> Suc 0 \<le> card (f ` Nset n)"
apply (subgoal_tac "0 < card (f ` Nset n)")
apply simp
apply (rule nonempty_card_pos)
apply (rule finite_imageI) apply (simp add:finite_Nset)
apply (subgoal_tac "f 0 \<in> f ` Nset n") apply (rule nonempty, assumption+)
apply (rule mem_in_image, assumption+) apply (simp add:Nset_def)
done

lemma eSum_changeTr1:"\<lbrakk>ring R; R module M; ideal R A; t \<in> Nset (card (f ` Nset na) - Suc 0) \<rightarrow> A; g \<in> Nset (card (f ` Nset na) - Suc 0) \<rightarrow> f ` Nset na; Suc 0 < card (f ` Nset na); g x = h (Suc n); x = Suc n; card (f ` Nset na) - Suc 0 =  Suc (card (f ` Nset na) - Suc 0 - Suc 0)\<rbrakk>  \<Longrightarrow> e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset na) - Suc 0) =  e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset na) - Suc 0 - Suc 0) +\<^sub>M  (t (Suc (card (f ` Nset na) - Suc 0 - Suc 0)) \<star>\<^sub>M (g ( Suc (card (f ` Nset na) - Suc 0 - Suc 0))))"
apply simp
done

constdefs
 zeroi::"[('r, 'm) RingType_scheme] \<Rightarrow> nat \<Rightarrow> 'r"
 "zeroi R == \<lambda>j. 0\<^sub>R"

lemma prep_arrTr1:"\<lbrakk>ring R; R module M; ideal R A; h \<in> Nset (Suc n) \<rightarrow> carrier M; f\<in>Nset na \<rightarrow> h ` Nset (Suc n); s\<in>Nset na \<rightarrow> A; m = linear_combination R M na s f\<rbrakk> \<Longrightarrow> \<exists>l\<in>Nset (Suc n). (\<exists>s\<in>Nset l \<rightarrow> A. \<exists>g\<in> Nset l \<rightarrow> h ` Nset (Suc n). m = linear_combination R M l s g \<and> bij_to g (Nset l) (f ` Nset na))"
apply (frule_tac s = s and n = na and f = f in  same_together[of "R" "A" "M" " h ` Nset (Suc n)"], assumption+)
 apply (simp add:image_sub) apply assumption+
apply auto
 apply (simp add:linear_combination_def)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na =
          e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset na) - Suc 0)")
apply (subgoal_tac "(card (f ` Nset na) - Suc 0) \<in> Nset (Suc n)")
 apply (subgoal_tac "g \<in> Nset (card (f ` Nset na) - Suc 0) \<rightarrow> h ` Nset (Suc n)")
 apply (subgoal_tac "bij_to g (Nset (card (f ` Nset na) - Suc 0)) (f ` Nset na)")
 apply blast
 prefer 2
  apply (frule_tac f = f and A = "Nset na" and B = "h ` Nset (Suc n)" and
        ?A1.0 = "Nset na" in image_sub) apply simp
  apply (rule extend_fun, assumption+)
 apply (frule_tac f = f and A = "Nset na" and B = "h ` Nset (Suc n)" and
        ?A1.0 = "Nset na" in image_sub) apply simp
 apply (simp add:bij_to_def)
apply (rule_tac A = "f ` Nset na" and n = "card (f ` Nset na) - Suc 0" and f = g in Nset2finite_inj)
 apply (rule finite_imageI) apply (simp add:finite_Nset)
 apply (frule_tac f = f and n = na and A = "h ` Nset (Suc n)" in card_Nset_im)
 apply simp apply assumption
apply (subgoal_tac "finite (h ` Nset (Suc n))")
apply (frule_tac f = f and A = "Nset na" and B = "h ` Nset (Suc n)" and
        ?A1.0 = "Nset na" in image_sub) apply simp
 apply (frule_tac B = "h ` Nset (Suc n)" and A = "f ` Nset na" in card_mono,
                                     assumption+)
 apply (insert finite_Nset [of "Suc n"])
 apply (frule card_image_le [of "Nset (Suc n)" "h"])
 apply (frule_tac i = "card (f ` Nset na)" and j = "card (h ` Nset (Suc n))"
 and k = "card (Nset (Suc n))" in le_trans, assumption+)
 apply (simp add:card_Nset[of "Suc n"])
 apply (frule_tac i = "card (f ` Nset na)" and j = "card (h ` Nset (Suc n))"
 and k = "Suc (Suc n)" in le_trans, assumption+)
 apply (frule_tac m = "card (f ` Nset na)" and n = "Suc (Suc n)" and l = "Suc 0" in diff_le_mono)
 apply (simp add:Nset_def)
apply (rule finite_imageI) apply (simp add:finite_Nset)
done

lemma finite_lin_spanTr3:"\<lbrakk>ring R; R module M; ideal R A\<rbrakk> \<Longrightarrow> h\<in>Nset n \<rightarrow> carrier M \<longrightarrow> (\<forall>na. \<forall>s \<in> Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> (h ` (Nset n)). (\<exists>t \<in> Nset n \<rightarrow> A. linear_combination R M na s f = linear_combination R M n t h))"
apply (induct_tac n)
 apply (rule impI) apply (rule allI) apply (rule ballI)+
 apply (insert Nset_nonempty [of "0"])
 apply (simp add:linear_combination_def)
 apply (frule_tac z = "h 0" and h = f and t = s in
          single_span [of "R" "M" "A"], assumption+)
 apply (insert n_in_Nsetn [of "0"])
 apply (rule funcset_mem, assumption+)
 apply (simp add:Nset_def image_def) apply assumption
 apply (subgoal_tac "\<forall>sa\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = sa 0 \<star>\<^sub>M (h 0) \<longrightarrow> (\<exists>t. t \<in> Nset 0 \<rightarrow> A \<and> e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = (t 0) \<star>\<^sub>M (h 0))")
 apply blast apply (thin_tac "\<exists>sa\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = sa 0 \<star>\<^sub>M (h 0)")
 apply (rule ballI) apply (rule impI) apply simp
 apply blast
(********** n = 0 done ***********)
apply (rule impI)  apply (rule allI) apply (rule ballI)+
 apply (frule func_pre) apply simp
 apply (case_tac "h (Suc n) \<notin>  f ` Nset na")
  apply (subgoal_tac "f \<in> Nset na \<rightarrow> h ` Nset n")
  apply (subgoal_tac "\<exists>t\<in>Nset n \<rightarrow> A. linear_combination R M na s f = linear_combination R M n t h")
  prefer 2 apply simp
  apply (subgoal_tac "\<forall>t\<in>Nset n \<rightarrow> A. linear_combination R M na s f = linear_combination R M n t h \<longrightarrow> (\<exists>t\<in>Nset (Suc n) \<rightarrow> A. linear_combination R M na s f = linear_combination R M (Suc n) t h)")
  apply blast
  apply (thin_tac "\<exists>t\<in>Nset n \<rightarrow> A. linear_combination R M na s f = linear_combination R M n t h")
  apply (rule ballI) apply (rule impI)
  apply simp
 apply (thin_tac "linear_combination R M na s f = linear_combination R M n t h")
apply (simp add:linear_combination_def)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n = e\<Sigma> M (\<lambda>j. (jointfun n t 0 (zeroi R)) j \<star>\<^sub>M (h j)) (Suc n)") apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n = e\<Sigma> M (\<lambda>j. jointfun n t 0 (zeroi R) j \<star>\<^sub>M (h j)) n +\<^sub>M  (jointfun n t 0 (zeroi R) (Suc n) \<star>\<^sub>M (h (Suc n)))")
 apply (subgoal_tac "jointfun n t 0 (zeroi R) \<in> Nset (Suc n) \<rightarrow> A")
 apply blast
apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "x \<le> n") apply (simp add:jointfun_def)
 apply (simp add:funcset_mem Nset_def) apply (simp add:Nset_def)
 apply (simp add:jointfun_def slide_def sliden_def)
 apply (simp add:zeroi_def) apply (simp add:ideal_zero)
 apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. jointfun n t 0 (zeroi R) j \<star>\<^sub>M (h j)) n =  e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n ") apply simp
 apply (subgoal_tac "jointfun n t 0 (zeroi R) (Suc n) \<star>\<^sub>M (h (Suc n)) = 0\<^sub>M")
 apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_r_zero [THEN sym, of "M"], assumption+)
 apply (rule_tac n = n and i = n in  eSum_mem, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem) apply (simp add:n_in_Nsetn)
 apply (simp add:jointfun_def slide_def sliden_def zeroi_def)
 apply (rule sprod_0_m, assumption+) apply (rule funcset_mem, assumption+)
 apply (simp add:n_in_Nsetn)
apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test)
 apply (rule ballI) apply (frule Nset_le)
 apply (simp add:jointfun_def) apply (simp add:Nset_def) apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
 apply (rule univar_func_test)
 apply (rule ballI) apply (frule Nset_le)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
apply (rule ballI) apply (frule Nset_le)
 apply (simp add:jointfun_def Nset_def)
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = f and A = "Nset na" and B = "h ` Nset (Suc n)" and
       x = x in funcset_mem, assumption+)
 apply (subgoal_tac "h ` Nset (Suc n) = h ` (Nset n) \<union> {h (Suc n)}")
 apply simp apply (subgoal_tac "f x \<noteq> h (Suc n)") apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac f = f and A = "Nset na" and a = x in mem_in_image,
          assumption+) apply simp
 apply (subst Nset_un) apply (subst im_set_un, assumption+)
 apply (simp add:Nsetn_sub) apply (rule subsetI) apply (simp add:n_in_Nsetn)
 apply simp apply simp
(*** case h (Suc n) \<notin>  f ` (Nset na) done ***)
apply (frule_tac h = h and n = n and m = "linear_combination R M na s f" in prep_arrTr1 [of "R" "M" "A"], assumption+) apply simp
apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). \<forall>sa\<in>Nset l \<rightarrow> A. \<forall>g\<in>Nset l \<rightarrow> h ` Nset (Suc n). linear_combination R M na s f = linear_combination R M l sa g \<and> bij_to g (Nset l) (f ` Nset na) \<longrightarrow>
 (\<exists>t\<in>Nset (Suc n) \<rightarrow> A. linear_combination R M na s f = linear_combination R M (Suc n) t h)")
 apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
\<exists>t\<in>Nset n \<rightarrow> A. linear_combination R M na s f = linear_combination R M n t h")
 apply blast
 apply (thin_tac "\<exists>l\<in>Nset (Suc n). \<exists>sa\<in>Nset l \<rightarrow> A. \<exists>g\<in>Nset l \<rightarrow> h ` Nset (Suc n). linear_combination R M na s f = linear_combination R M l sa g \<and>
                   bij_to g (Nset l) (f ` Nset na)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (thin_tac "linear_combination R M na s f = linear_combination R M l sa g")
 apply (subgoal_tac "inj_on g (Nset l)")  prefer 2 apply (simp add:bij_to_def)
 apply (subgoal_tac "surj_to g (Nset l) (f ` Nset na)") prefer 2
   apply (simp add:bij_to_def)
 apply (simp add:surj_to_def) apply (frule sym)
 apply (thin_tac "g ` Nset l = f ` Nset na") apply simp
 apply (subgoal_tac "\<exists>x\<in>Nset l. h (Suc n) = g x")
 prefer 2 apply (simp add:image_def)
apply (subgoal_tac "\<forall>x\<in>Nset l. h (Suc n) = g x \<longrightarrow> (\<exists>t\<in>Nset (Suc n) \<rightarrow> A.
 linear_combination R M l sa g = linear_combination R M (Suc n) t h)")
 apply blast apply (thin_tac "\<exists>x\<in>Nset l. h (Suc n) = g x")
 apply (rule ballI) apply (rule impI)
 apply (simp add:linear_combination_def)
apply (case_tac "l = 0") apply simp
 apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
  \<exists>t\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n")
 apply (subgoal_tac "jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. (sa 0)) \<in>
   Nset (Suc n) \<rightarrow> A")
 apply (subgoal_tac "(\<lambda>k\<in>Nset (Suc n). (g x)) \<in> Nset n \<rightarrow> carrier M")
 apply (subgoal_tac "sa 0 \<star>\<^sub>M (g 0) =  e\<Sigma> M (\<lambda>j. (jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. sa 0)) j \<star>\<^sub>M (h j)) (Suc n)") apply simp
 apply (thin_tac "sa 0 \<star>\<^sub>M (g 0) = e\<Sigma> M (\<lambda>j. (jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. (sa 0))) j \<star>\<^sub>M (h j)) n +\<^sub>M ((jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. sa 0)) (Suc n) \<star>\<^sub>M (g x))")
 apply (thin_tac "h \<in> Nset n \<rightarrow> carrier M")
 apply blast
 apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. (jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. sa 0)) j \<star>\<^sub>M (h j)) n = 0\<^sub>M") apply simp
 apply (subgoal_tac "(jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. sa 0)) (Suc n) \<star>\<^sub>M (g x)  = sa 0 \<star>\<^sub>M (g 0)")  apply simp apply (frule module_is_ag, assumption+)
 apply (rule ag_l_zero [THEN sym], assumption+)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (subgoal_tac "g \<in> Nset 0 \<rightarrow> carrier M") apply (simp add:funcset_mem)
 apply (frule_tac f = h and A = "Nset (Suc n)" and B = "carrier M" and
  ?A1.0 = "Nset (Suc n)" in image_sub) apply simp
 apply (rule extend_fun, assumption+)
 apply (subgoal_tac "x = 0") apply (simp add:jointfun_def slide_def sliden_def NSet_def) apply (simp add:Nset_def)
 apply (frule_tac f = "jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. sa 0)" in func_pre)
 apply (frule_tac s = "jointfun n (zeroi R) 0 (\<lambda>k\<in>Nset 0. sa 0)" and n = n and m = h in linear_comb0_1 [of "R" "M" "carrier M"], assumption+)
 apply simp
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def jointfun_def zeroi_def)
 apply assumption+
 apply (simp add:linear_combination_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "xa \<in> Nset (Suc n)") apply simp
apply (frule_tac f = h and A = "Nset (Suc n)" and B = "carrier M" and
  ?A1.0 = "Nset (Suc n)" in image_sub) apply simp
 apply (frule_tac f = g and A = "Nset 0" and B = "h ` Nset (Suc n)" and
       ?B1.0 = "carrier M" in extend_fun, assumption+)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "xa = Suc n")
 apply (simp add:jointfun_def slide_def sliden_def)
 apply (simp add:funcset_mem) apply (rotate_tac -2)  apply (frule Nset_pre, assumption+)
 apply (simp add:Nset_def jointfun_def zeroi_def)
 apply (simp add:ideal_zero)
apply (case_tac "x = l")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) l =
            e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (Suc (l - Suc 0))")
 apply (simp del:Suc_pred)
 apply (thin_tac " e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) l =
  e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (l - Suc 0) +\<^sub>M (sa (Suc (l - Suc 0)) \<star>\<^sub>M (g (Suc (l - Suc 0))))") apply simp apply (rotate_tac -3) apply (frule sym)
 apply (thin_tac "h (Suc n) = g l") apply simp
 apply (subgoal_tac "sa \<in> Nset (Suc (l - Suc 0)) \<rightarrow> A")
 apply (frule_tac f = sa in func_pre)
 apply (subgoal_tac "g \<in> Nset (l - Suc 0) \<rightarrow> h ` Nset n")
 apply (subgoal_tac "\<exists>w\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (l - Suc 0) =
                        e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n")
 prefer 2 apply simp
apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
 \<exists>t\<in>Nset n \<rightarrow> A.  e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n")
 apply (subgoal_tac "\<forall>w\<in>Nset n \<rightarrow> A.  e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (l - Suc 0) = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n \<longrightarrow> (\<exists>t\<in>Nset (Suc n) \<rightarrow> A.  e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (l - Suc 0) +\<^sub>M  (sa l \<star>\<^sub>M (h (Suc n))) = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n +\<^sub>M  (t (Suc n) \<star>\<^sub>M (h (Suc n))))")
 apply (thin_tac "g \<in> Nset (l - Suc 0) \<rightarrow> h ` Nset n")
 apply (thin_tac "sa \<in> Nset (l - Suc 0) \<rightarrow> A")
 apply (thin_tac "sa \<in> Nset (Suc (l - Suc 0)) \<rightarrow> A")
 apply (thin_tac "g l = h (Suc n)")
 apply (thin_tac "l \<in> Nset l") apply (thin_tac "f ` Nset na = g ` Nset l")
 apply (thin_tac " h \<in> Nset (Suc n) \<rightarrow> carrier M")
 apply (thin_tac "s \<in> Nset na \<rightarrow> A")
 apply (thin_tac "f \<in> Nset na \<rightarrow> h ` Nset (Suc n)")
 apply (thin_tac "h \<in> Nset n \<rightarrow> carrier M")
 apply (thin_tac "l \<in> Nset (Suc n)")
 apply (thin_tac " bij_to g (Nset l) (g ` Nset l)")
 apply (thin_tac "inj_on g (Nset l)")
 apply (thin_tac "sa \<in> Nset l \<rightarrow> A") apply (thin_tac "g \<in> Nset l \<rightarrow> h ` Nset (Suc n)")
 apply blast
 apply (thin_tac "\<exists>w\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (l - Suc 0) = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n") apply (rule ballI) apply (rule impI)
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (l - Suc 0) = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n")
prefer 3 apply simp
prefer 2
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = g and A = "Nset l" and B = "h ` Nset (Suc n)" and
 ?A1.0 = "Nset l" in image_sub) apply simp
 apply (subgoal_tac "xa \<in> Nset l")
 apply (frule_tac x = xa and n = "l - Suc 0" in Nset_le)
 apply (frule_tac i = xa and j = "l - Suc 0" and k = l in le_less_trans)
 apply simp
 apply (subgoal_tac "xa \<noteq> l") prefer 2 apply simp
 apply (frule_tac f = g and A = "Nset l" and x = xa and y = l in injective,
                                     assumption+) apply simp
 apply (frule_tac f = g and A = "Nset l" and B = "h ` Nset (Suc n)" and x = xa
         in funcset_mem, assumption+)
 apply (simp add:Nset_un) apply (simp add:Nset_def)
 apply (frule_tac i = xa and j = "l - Suc 0" and k = l in le_less_trans)
 apply simp
 apply (simp add:less_imp_le)
 prefer 2  apply (simp del:eSum_Suc)
apply (subgoal_tac "jointfun n w 0 (\<lambda>k\<in>Nset 0. (sa l)) \<in> Nset (Suc n) \<rightarrow> A")
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n +\<^sub>M  (sa l \<star>\<^sub>M (h (Suc n))) =
 e\<Sigma> M (\<lambda>j. (jointfun n w 0 (\<lambda>k\<in>Nset 0. (sa l))) j \<star>\<^sub>M (h j)) (Suc n)")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n +\<^sub>M (sa l \<star>\<^sub>M (h (Suc n))) =
  e\<Sigma> M (\<lambda>j. (jointfun n w 0 (\<lambda>k\<in>Nset 0. sa l)) j \<star>\<^sub>M (h j)) n +\<^sub>M
   ((jointfun n w 0 (\<lambda>k\<in>Nset 0. sa l)) (Suc n) \<star>\<^sub>M (h (Suc n)))")
 apply (thin_tac "h \<in> Nset (Suc n) \<rightarrow> carrier M")
 apply (thin_tac "s \<in> Nset na \<rightarrow> A")
 apply (thin_tac "f \<in> Nset na \<rightarrow> h ` Nset (Suc n)")
 apply (thin_tac "h \<in> Nset n \<rightarrow> carrier M")
 apply (thin_tac "g \<in> Nset l \<rightarrow> h ` Nset (Suc n)")
 apply (thin_tac "bij_to g (Nset l) (g ` Nset l)")
 apply (thin_tac "f ` Nset na = g ` Nset l")
 apply (thin_tac "g \<in> Nset (l - Suc 0) \<rightarrow> h ` Nset n")
 apply blast apply simp
 apply (subgoal_tac "(jointfun n w 0 (\<lambda>k\<in>Nset 0. sa l)) (Suc n) \<star>\<^sub>M (h (Suc n))
 =  (sa l) \<star>\<^sub>M (h (Suc n))") apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. (jointfun n w 0 (\<lambda>k\<in>Nset 0. sa l)) j \<star>\<^sub>M (h j)) n = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n") apply simp
 apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def jointfun_def) apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def jointfun_def) apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem)
apply (rule ballI)
 apply (simp add:Nset_def jointfun_def)
 apply (simp add:jointfun_def slide_def sliden_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "xa = Suc n")
 apply (simp add:jointfun_def slide_def sliden_def)
 apply (simp add:funcset_mem) apply (rotate_tac -2) apply (frule Nset_pre, assumption+)
 apply (simp add:Nset_def jointfun_def) apply (simp add:funcset_mem)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) l =
           e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (Suc (l - Suc 0))")
 apply (simp del:eSum_Suc Suc_pred)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) l =
           e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (Suc (l - Suc 0))")
 prefer 2 apply simp
 apply (frule_tac H = "g ` Nset l" and s = sa and n = "l - Suc 0" and
 f = g and j = x in one_last [of "R" "A" "M"], assumption+)
 apply (frule_tac f = h and A = "Nset (Suc n)" and B = "carrier M" and
  ?A1.0 = "Nset (Suc n)" in image_sub) apply simp
 apply (rotate_tac -6) apply (frule sym) apply (thin_tac "f ` Nset na = g ` Nset l") apply simp
 apply (frule_tac f = h and A = "Nset (Suc n)" and B = "carrier M" and
  ?A1.0 = "Nset (Suc n)" in image_sub) apply simp
 apply (frule_tac f = f and A = "Nset na" and B = "h ` Nset (Suc n)" and
  ?A1.0 = "Nset na" in image_sub) apply simp
 apply (rule subset_trans, assumption+)
 apply simp apply simp
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:mem_in_image)
 apply simp apply simp apply simp
apply (subgoal_tac "\<forall>t\<in>Nset (Suc (l - Suc 0)) \<rightarrow> A. \<forall>ga\<in>Nset (Suc (l - Suc 0)) \<rightarrow> g ` Nset l. e\<Sigma> M (\<lambda>k. sa k \<star>\<^sub>M (g k)) (Suc (l - Suc 0)) =
 e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (ga k)) (Suc (l - Suc 0)) \<and> ga (Suc (l - Suc 0)) = g x \<and>
 t (Suc (l - Suc 0)) = sa x \<and> bij_to ga (Nset (Suc (l - Suc 0))) (g ` Nset l) \<longrightarrow> (\<exists>t\<in>Nset (Suc n) \<rightarrow> A. e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (g j)) (Suc (l - Suc 0)) =
              e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n +\<^sub>M  (t (Suc n) \<star>\<^sub>M (g x)))")
 apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
 \<exists>t\<in>Nset n \<rightarrow> A.  e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n")
 apply (thin_tac "Nset 0 \<noteq> {}")
 apply (thin_tac "0 \<in> Nset 0")
 apply (thin_tac "h \<in> Nset (Suc n) \<rightarrow> carrier M")
 apply (thin_tac "s \<in> Nset na \<rightarrow> A")
 apply (thin_tac "f \<in> Nset na \<rightarrow> h ` Nset (Suc n)")
 apply (thin_tac "h \<in> Nset n \<rightarrow> carrier M")
 apply (thin_tac "l \<in> Nset (Suc n)")
 apply (thin_tac "sa \<in> Nset l \<rightarrow> A")
 apply (thin_tac "g \<in> Nset l \<rightarrow> h ` Nset (Suc n)")
 apply (thin_tac "inj_on g (Nset l)")
 apply (thin_tac "f ` Nset na = g ` Nset l")
 apply (thin_tac "x \<in> Nset l")
 apply (thin_tac "h (Suc n) = g x")
 apply (thin_tac "x \<noteq> l")
apply blast
 apply (thin_tac "\<exists>t\<in>Nset (Suc (l - Suc 0)) \<rightarrow> A. \<exists>ga\<in>Nset (Suc (l - Suc 0)) \<rightarrow> g ` Nset l. e\<Sigma> M (\<lambda>k. sa k \<star>\<^sub>M (g k)) (Suc (l - Suc 0)) =
 e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (ga k)) (Suc (l - Suc 0)) \<and> ga (Suc (l - Suc 0)) = g x \<and>    t (Suc (l - Suc 0)) = sa x \<and> bij_to ga (Nset (Suc (l - Suc 0))) (g ` Nset l)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)+
 apply (simp del:Suc_pred)
 apply (thin_tac "e\<Sigma> M (\<lambda>k. sa k \<star>\<^sub>M (g k)) (l - Suc 0) +\<^sub>M (sa (Suc (l - Suc 0)) \<star>\<^sub>M (g (Suc (l - Suc 0)))) = e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (ga k)) (l - Suc 0) +\<^sub>M (sa x \<star>\<^sub>M (g x))")
 apply (frule_tac f = t in func_pre)
 apply (frule_tac f = ga in func_pre)
 apply (subgoal_tac "ga \<in> Nset (l - Suc 0) \<rightarrow> h ` Nset n")
 apply (subgoal_tac "\<exists>w\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (ga j)) (l - Suc 0) =
                        e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n")
 prefer 2
  apply (thin_tac "f \<in> Nset na \<rightarrow> h ` Nset (Suc n)")
  apply (thin_tac "ga (Suc (l - Suc 0)) = g x")
  apply (thin_tac "t (Suc (l - Suc 0)) = sa x")
  apply (thin_tac "t \<in> Nset (Suc (l - Suc 0)) \<rightarrow> A")
  apply (thin_tac "f ` Nset na = g ` Nset l")
  apply (thin_tac "x \<in> Nset l")
  apply (thin_tac "h (Suc n) = g x")
  apply (thin_tac "g \<in> Nset l \<rightarrow> h ` Nset (Suc n)")
  apply (thin_tac "inj_on g (Nset l)")
  apply simp
apply (subgoal_tac "\<forall>w\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (ga j)) (l - Suc 0) = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n \<longrightarrow> (\<exists>ta\<in>Nset (Suc n) \<rightarrow> A. e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (ga j)) (l - Suc 0) +\<^sub>M  (sa x \<star>\<^sub>M (g x)) = e\<Sigma> M (\<lambda>j. ta j \<star>\<^sub>M (h j)) n +\<^sub>M (ta (Suc n) \<star>\<^sub>M (g x)))")
  apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
  \<exists>t\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n")
  apply (thin_tac "ga (Suc (l - Suc 0)) = g x")
  apply (thin_tac "t (Suc (l - Suc 0)) = sa x")
  apply (thin_tac "ga \<in> Nset (l - Suc 0) \<rightarrow> h ` Nset n")
  apply (thin_tac " h (Suc n) = g x")
  apply (thin_tac "t \<in> Nset (Suc (l - Suc 0)) \<rightarrow> A")
apply blast apply (thin_tac "\<exists>w\<in>Nset n \<rightarrow> A.
   e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (ga j)) (l - Suc 0) = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n")
 apply (rule ballI) apply (rule impI) apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (ga j)) (l - Suc 0) = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n")
 apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
  \<exists>t\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n")
 apply (rotate_tac -12)
 apply (frule sym) apply (thin_tac "h (Suc n) = g x")
 apply simp
apply (subgoal_tac "jointfun n w 0 (\<lambda>k\<in>Nset 0. (sa x)) \<in> Nset (Suc n) \<rightarrow> A")
apply (subgoal_tac "e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n +\<^sub>M  (sa x \<star>\<^sub>M (h (Suc n))) =
 e\<Sigma> M (\<lambda>j. (jointfun n w 0 (\<lambda>k\<in>Nset 0. (sa x))) j \<star>\<^sub>M (h j)) (Suc n)")
(* kore o lemma ni shite oku to yoi. *)
apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n +\<^sub>M  (sa x \<star>\<^sub>M (h (Suc n))) =
  e\<Sigma> M (\<lambda>j. (jointfun n w 0 (\<lambda>k\<in>Nset 0. sa x)) j \<star>\<^sub>M (h j)) n +\<^sub>M
     ((jointfun n w 0 (\<lambda>k\<in>Nset 0. sa x)) (Suc n) \<star>\<^sub>M (h (Suc n)))")
 apply blast apply simp
 apply (subgoal_tac "(jointfun n w 0 (\<lambda>k\<in>Nset 0. sa x)) (Suc n) \<star>\<^sub>M (h (Suc n))
 = sa x \<star>\<^sub>M (h (Suc n))") apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. (jointfun n w 0 (\<lambda>k\<in>Nset 0. sa x)) j \<star>\<^sub>M (h j)) n  = e\<Sigma> M (\<lambda>j. w j \<star>\<^sub>M (h j)) n") apply simp
 apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def jointfun_def)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
apply (rule ballI)
 apply (simp add:Nset_def jointfun_def)
 apply (simp add:jointfun_def slide_def sliden_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "xa = Suc n")
 apply (simp add:jointfun_def slide_def sliden_def)
 apply (simp add:funcset_mem) apply (rotate_tac -2)
  apply (frule Nset_pre, assumption+)
  apply (simp add:Nset_def jointfun_def) apply (simp add:funcset_mem)
apply (thin_tac "\<forall>na. \<forall>s\<in>Nset na \<rightarrow> A. \<forall>f\<in>Nset na \<rightarrow> h ` Nset n.
 \<exists>t\<in>Nset n \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) na =  e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (h j)) n")
 apply simp
 apply (rotate_tac -10) apply (frule sym) apply (thin_tac "h (Suc n) = g x")
 apply simp
 apply (thin_tac "t \<in> Nset l \<rightarrow> A")
 apply (thin_tac "t l = sa x")
 apply (thin_tac "t \<in> Nset (l - Suc 0) \<rightarrow> A")
 apply (thin_tac "ga \<in> Nset (l - Suc 0) \<rightarrow> g ` Nset l")
 apply (thin_tac "s \<in> Nset na \<rightarrow> A")
 apply (thin_tac "sa \<in> Nset l \<rightarrow> A")
 apply (thin_tac " x \<in> Nset l") apply (thin_tac "g x = h (Suc n)")
apply (frule_tac f = f and A = "Nset na" and B = "h ` Nset (Suc n)"
  and ?A1.0 = "Nset na" in image_sub) apply simp
apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "xa \<in> Nset l")
  apply (frule_tac f = ga and A = "Nset l" and B = "g ` Nset l" and x = xa in
          funcset_mem) apply assumption+
 apply (thin_tac "xa \<in> Nset l")
 apply (frule_tac x = xa in Nset_le)
apply (subgoal_tac "xa \<noteq> l")
 prefer 2 apply (frule_tac i = xa and j = "l - Suc 0" and k = l in le_less_trans) apply simp apply simp apply (simp add:bij_to_def) apply (erule conjE)
 apply (frule_tac f = ga and A = "Nset l" and x = xa and y = l in injective)
 apply (simp add:Nset_def)
 apply (frule_tac i = xa and j = "l - Suc 0" and k = l in le_less_trans) apply simp apply (simp add:less_imp_le) apply (simp add:n_in_Nsetn)
 apply assumption apply simp
 apply (frule_tac A = "g ` Nset l" and B = " h ` Nset (Suc n)" and c = "ga xa"  in subsetD, assumption+)
 apply (simp add:Nset_un)
 apply (simp add:Nset_def)
apply (frule_tac i = xa and j = "l - Suc 0" and k = l in le_less_trans)
apply simp apply (simp add:less_imp_le)
done

lemma finite_lin_span:"\<lbrakk>ring R; R module M; ideal R A;  h \<in> Nset n \<rightarrow> carrier M; s \<in> Nset na \<rightarrow> A; f\<in>Nset na \<rightarrow> h ` Nset n\<rbrakk> \<Longrightarrow> \<exists>t\<in>Nset n \<rightarrow> A.
              linear_combination R M na s f = linear_combination R M n t h"
apply (simp add:finite_lin_spanTr3)
done

 subsection "4-2. free generators"
constdefs
 free_generator::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, 'a set] \<Rightarrow> bool"
 "free_generator R M H == generator R M H \<and> (\<forall>n. (\<forall>s f. (s \<in> Nset n \<rightarrow> carrier R \<and> f \<in> Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and> linear_combination R M n s f = 0\<^sub>M) \<longrightarrow> s \<in> Nset n \<rightarrow> {0\<^sub>R}))"

lemma free_generator_nonzero:"\<lbrakk>\<not> (zeroring R); ring R; R module M; free_generator R M H; h \<in> H\<rbrakk> \<Longrightarrow> h \<noteq> 0\<^sub>M"
apply (rule contrapos_pp, simp+)
 apply (simp add:free_generator_def) apply (erule conjE)+
 apply (subgoal_tac "(\<lambda>t. 1\<^sub>R) \<in> Nset 0 \<rightarrow> carrier R")
 apply (subgoal_tac "(\<lambda>t. 0\<^sub>M) \<in> Nset 0 \<rightarrow> H \<and> inj_on (\<lambda>t. 0\<^sub>M) (Nset 0) \<and>
 linear_combination R M 0 (\<lambda>t. 1\<^sub>R) (\<lambda>t. 0\<^sub>M) = 0\<^sub>M")
 apply (subgoal_tac "(\<lambda>t. 1\<^sub>R) \<in> Nset 0 \<rightarrow> {0\<^sub>R}") prefer 2 apply blast
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule_tac f = "\<lambda>t. 1\<^sub>R" and A = "Nset 0" and B = "{0\<^sub>R}" and x = 0 in
 funcset_mem, assumption+) apply simp
 apply (frule Zero_ring1 [of "R"], assumption+) apply simp
apply (simp add:Nset_def)
 apply (thin_tac "\<forall>n s. s \<in> Nset n \<rightarrow> carrier R \<and> (\<exists>f. f \<in> Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and> linear_combination R M n s f = 0\<^sub>M) \<longrightarrow> s \<in> Nset n \<rightarrow> {0\<^sub>R}")
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (rule conjI)
 apply (simp add:inj_on_def) apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:linear_combination_def)
 apply (rule sprod_a_0, assumption+)
 apply (simp add:ring_one)
apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:ring_one)
done

lemma unique_expression1:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; free_generator R M H;
s \<in> Nset n \<rightarrow> carrier R; m \<in> Nset n \<rightarrow> H; inj_on m (Nset n); linear_combination R M n s m = 0\<^sub>M\<rbrakk> \<Longrightarrow> \<forall>j\<in>Nset n. s j = 0\<^sub>R"
apply (rule ballI)
apply (simp add:free_generator_def) apply (erule conjE)+
apply (subgoal_tac "s \<in> Nset n \<rightarrow> {0\<^sub>R}")
 apply (frule_tac f = s and A = "Nset n" and B = "{0\<^sub>R}" and x = j in funcset_mem, assumption+) apply simp
apply blast
done

lemma unique_expression2:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; f\<in>Nset n \<rightarrow> H; s \<in> Nset n \<rightarrow> carrier R\<rbrakk> \<Longrightarrow> \<exists>m g t. g \<in> (Nset m \<rightarrow> H) \<and> bij_to g (Nset m) (f ` (Nset n)) \<and> t \<in> (Nset m \<rightarrow> carrier R) \<and> linear_combination R M n s f = linear_combination R M m t g"
apply (frule whole_ideal [of "R"])
apply (frule_tac R = R and A = "carrier R" and M = M and H = H and s = s and f = f in same_together, assumption+)
apply (subgoal_tac "\<forall>t\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> carrier R.
 \<forall>g\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> f ` Nset n.  surj_to g
 (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n) \<and> e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n
  = e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0) \<longrightarrow> (\<exists>m g t.
  g \<in> Nset m \<rightarrow> H \<and> bij_to g (Nset m) (f ` Nset n) \<and>  t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M n s f = linear_combination R M m t g)")
 apply blast
 apply (thin_tac "\<exists>t\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> carrier R.  \<exists>g\<in>Nset (card (f ` Nset n) - Suc 0) \<rightarrow> f ` Nset n.  surj_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` Nset n) \<and>  e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = e\<Sigma> M (\<lambda>k. t k \<star>\<^sub>M (g k)) (card (f ` Nset n) - Suc 0)")
apply (rule ballI)+  apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac " g \<in> Nset (card (f ` Nset n) - Suc 0) \<rightarrow> H")
 apply (subgoal_tac "bij_to g (Nset (card (f ` Nset n) - Suc 0)) (f ` (Nset n))")
 apply (simp add:linear_combination_def) apply blast
prefer 2
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "Nset n \<subseteq> (Nset n)")
 apply (frule_tac f = f and A = "Nset n" and ?A1.0 = "Nset n" and B = H in
 image_sub, assumption+) apply (thin_tac "Nset n \<subseteq> (Nset n)")
 apply (simp add:funcset_mem subsetD) apply simp
 apply (insert finite_Nset [of "n"])
 apply (subgoal_tac "finite (f` (Nset n))") prefer 2 apply simp
apply (subst bij_to_def) apply (simp del:finite_imageI)
apply (rule_tac A = "f ` (Nset n)" and n = "card (f ` Nset n) - Suc 0" and f = g in Nset2finite_inj, assumption+)
 apply (subgoal_tac "0 < card (f ` (Nset n))") apply simp
 apply (subgoal_tac "{f 0} \<subseteq> f ` (Nset n)")
 apply (frule_tac B = "f ` (Nset n)" and A = "{f 0}" in card_mono)
 apply assumption
 apply (subgoal_tac "card {f 0} = 1") prefer 2 apply (simp add:card1)
 apply simp
 apply (rule subsetI) apply simp
 apply (subgoal_tac "0 \<in> Nset n") apply (simp add:funcset_mem)
 apply (simp add:Nset_def) apply assumption
done

lemma unique_expression3_1:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; f\<in>Nset (Suc n) \<rightarrow> H; s \<in> Nset (Suc n) \<rightarrow> carrier R; j \<in> Nset (Suc n); (f j) \<notin> f ` (Nset (Suc n) - {j}); j = Suc n\<rbrakk> \<Longrightarrow> \<exists>g m t. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) s f = linear_combination R M m t g \<and> t m = s j"
apply (subgoal_tac "linear_combination R M (Suc n) s f = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) (Suc n)") apply simp
apply (frule_tac f = f and n = n and A = H in func_pre)
apply (frule_tac f = s and n = n and A = "carrier R" in func_pre)
apply (frule_tac R = R and M = M and H = H and f = f and s = s and n = n in unique_expression2, assumption+)
apply auto
prefer 2  apply (simp add:linear_combination_def)
apply (subgoal_tac "jointfun m g 0 (\<lambda>j. (f (Suc n))) \<in> Nset (Suc m) \<rightarrow> H")
apply (subgoal_tac "inj_on (jointfun m g 0 (\<lambda>j. (f (Suc n)))) (Nset (Suc m))")
apply (subgoal_tac "jointfun m t 0 (\<lambda>j. (s (Suc n))) \<in> Nset (Suc m) \<rightarrow> carrier R")
apply (subgoal_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n)))=
 linear_combination R M (Suc m) (jointfun m t 0 (\<lambda>j. (s (Suc n)))) (jointfun m g 0 (\<lambda>j. (f (Suc n))))")
apply (subgoal_tac "(jointfun m t 0 (\<lambda>j. (s (Suc n)))) (Suc m) = s (Suc n)")
apply blast
apply (simp add:jointfun_def) apply (simp add:linear_combination_def)
apply (subgoal_tac "e\<Sigma> M (\<lambda>j. (t j) \<star>\<^sub>M (g j)) m = e\<Sigma> M (\<lambda>j. jointfun m t 0 (\<lambda>j. s (Suc n)) j \<star>\<^sub>M (jointfun m g 0 (\<lambda>j. f (Suc n)) j)) m")
apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) = (jointfun m t 0 (\<lambda>j. s (Suc n)) (Suc m)) \<star>\<^sub>M (jointfun m g 0 (\<lambda>j. f (Suc n)) (Suc m))") apply simp
 apply (thin_tac "jointfun m g 0 (\<lambda>j. f (Suc n)) \<in> Nset (Suc m) \<rightarrow> H")
 apply (thin_tac "inj_on (jointfun m g 0 (\<lambda>j. f (Suc n))) (Nset (Suc m))")
 apply (thin_tac "e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (f j)) n = e\<Sigma> M (\<lambda>j.  t j \<star>\<^sub>M (g j)) m")
 apply (thin_tac "jointfun m t 0 (\<lambda>j. s (Suc n)) \<in> Nset (Suc m) \<rightarrow> carrier R")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (g j)) m = e\<Sigma> M (\<lambda>j. jointfun m t 0 (\<lambda>j. s (Suc n)) j \<star>\<^sub>M (jointfun m g 0 (\<lambda>j. f (Suc n)) j)) m")
 apply (simp add:jointfun_def)
apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (subgoal_tac "(\<lambda>j.  t j \<star>\<^sub>M (g j)) \<in> Nset m \<rightarrow> carrier M")
 apply (subgoal_tac "(\<lambda>j. (jointfun m t 0 (\<lambda>j. s (Suc n)) j) \<star>\<^sub>M ((jointfun m g 0 (\<lambda>j. f (Suc n))) j)) \<in> Nset m \<rightarrow> carrier M")
 apply (frule_tac R = M and f = "\<lambda>j.  t j \<star>\<^sub>M (g j)" and n = m and g = "\<lambda>j. (jointfun m t 0 (\<lambda>j. s (Suc n)) j) \<star>\<^sub>M ((jointfun m g 0 (\<lambda>j. f (Suc n))) j)" in eSum_eq, assumption+)
 apply (rule ballI)
 apply (thin_tac "jointfun m g 0 (\<lambda>j. f (Suc n)) \<in> Nset (Suc m) \<rightarrow> H")
 apply (thin_tac "inj_on (jointfun m g 0 (\<lambda>j. f (Suc n))) (Nset (Suc m))")
 apply (thin_tac "jointfun m t 0 (\<lambda>j. s (Suc n)) \<in> Nset (Suc m) \<rightarrow> carrier R")
 apply (thin_tac "(\<lambda>j. (jointfun m t 0 (\<lambda>j. s (Suc n)) j) \<star>\<^sub>M (jointfun m g 0 (\<lambda>j. f (Suc n)) j)) \<in> Nset m \<rightarrow> carrier M")
 apply (subgoal_tac "l \<le> m") prefer 2 apply (simp add:Nset_def)
 apply (simp add:jointfun_def) apply assumption
apply (rule univar_func_test)
 apply (rule ballI) apply (subgoal_tac "x \<le> m") prefer 2 apply (simp add:Nset_def)
 apply (simp add:jointfun_def)
 apply (rule_tac R = R and M = M and a = "t x" and m = "g x" in sprod_mem,
  assumption+) apply (simp add:funcset_mem) apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule_tac R = R and M = M and a = "t x" and m = "g x" in sprod_mem,
  assumption+) apply (simp add:funcset_mem) apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "x = Suc m")
  apply (simp add:jointfun_def) apply (simp add:funcset_mem)
  apply (subgoal_tac "x \<le> m") apply (subgoal_tac "x \<in> Nset m")
  apply (simp add:jointfun_def) apply (simp add:funcset_mem)
  apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (thin_tac "linear_combination R M n s f = linear_combination R M m t g")
  apply (thin_tac "t \<in> Nset m \<rightarrow> carrier R")
  apply (thin_tac "f \<in> Nset n \<rightarrow> H")
  apply (thin_tac "s \<in> Nset n \<rightarrow> carrier R")
  apply (thin_tac "linear_combination R M (Suc n) s f =
           e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n)))")
 apply (subst inj_on_def) apply (rule ballI)+ apply (rule impI)
 apply (case_tac "x \<in> Nset m")
  apply (case_tac "y \<in> Nset m")
  apply (simp add:Nset_def) apply (simp add:jointfun_def)
  apply (rule contrapos_pp, simp+) apply (fold Nset_def)
  apply (simp add:bij_to_def) apply (erule conjE)+
  apply (frule_tac f = g and A = "Nset m" and x = x and y = y in injective)
  apply (simp add:Nset_def) apply (simp add:Nset_def) apply assumption
  apply simp
  apply (subgoal_tac "x \<le> m") apply (subgoal_tac "y = Suc m")
  apply (simp add:jointfun_def)
 apply (subgoal_tac "Nset (Suc n) - {Suc n} = Nset n") apply simp
  apply (thin_tac "Nset (Suc n) - {Suc n} = Nset n")
  apply (simp add:bij_to_def) apply (erule conjE) apply (simp add:surj_to_def)
(* koko *)
  apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image,
                                  assumption+)
  apply simp
 apply (rule equalityI)
  apply (rule subsetI) apply (simp add:Nset_def)
  apply (rule subsetI) apply (simp add:Nset_def)
  apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (case_tac "y \<in> Nset m")
  apply (subgoal_tac "x = Suc m") apply (subgoal_tac "y \<le> m")
  apply (simp add:jointfun_def)
  apply (frule sym) apply (thin_tac "f (Suc n) = g y")
  apply (simp add:bij_to_def) apply (erule conjE)
 apply (subgoal_tac "Nset (Suc n) - {Suc n} = Nset n") apply simp
  apply (frule_tac f = g and A = "Nset m" and B = H and a = y in mem_in_image,
                                  assumption+)
  apply (simp add:surj_to_def)
 apply (rule equalityI)
  apply (rule subsetI) apply (simp add:Nset_def)
  apply (rule subsetI) apply (simp add:Nset_def)
  apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (subgoal_tac "x = Suc m") apply (subgoal_tac "y = Suc m")
  apply simp apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (rule univar_func_test) apply (rule ballI)
  apply (case_tac "x = Suc m") apply (simp add:jointfun_def)
  apply (simp add:funcset_mem)
  apply (subgoal_tac "x \<le> m") apply (simp add:jointfun_def)
  apply (subgoal_tac "x \<in> Nset m") apply (simp add:funcset_mem)
  apply (simp add:Nset_def) apply (simp add:Nset_def)
done

lemma unique_expression3_2:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; f\<in>Nset (Suc n) \<rightarrow> H; s \<in> Nset (Suc n) \<rightarrow> carrier R; l \<in> Nset (Suc n); (f l) \<notin> f ` (Nset (Suc n) - {l}); l \<noteq> Suc n\<rbrakk> \<Longrightarrow> \<exists>g m t. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) s f = linear_combination R M m t g \<and> t m = s l"
apply (frule module_is_ag [of "R" "M"], assumption+)
apply (subgoal_tac "(\<lambda>j.  s j \<star>\<^sub>M (f j)) \<in> Nset (Suc n) \<rightarrow> carrier M")
apply (frule_tac R = M and f = "(\<lambda>j.  s j \<star>\<^sub>M (f j))" and n = n and j = l in addition3, assumption+)
apply (subgoal_tac "e\<Sigma> M (cmp (\<lambda>j.  s j \<star>\<^sub>M (f j)) (transpos l (Suc n))) (Suc n)= e\<Sigma> M (\<lambda>j. (cmp s (transpos l (Suc n))) j \<star>\<^sub>M ((cmp f (transpos l (Suc n))) j)) (Suc n)") apply (simp del:eSum_Suc)
apply (subgoal_tac "linear_combination R M (Suc n) s f =
 linear_combination R M (Suc n) (cmp s (transpos l (Suc n))) (cmp f (transpos l (Suc n)))") apply (simp del:eSum_Suc)
 apply (subgoal_tac "(cmp f (transpos l (Suc n))) \<in> Nset (Suc n) \<rightarrow> H")
 apply (subgoal_tac "(cmp s (transpos l (Suc n))) \<in> Nset (Suc n) \<rightarrow> carrier R")
apply (frule_tac R = R and M = M and H = H and f = "cmp f (transpos l (Suc n))"
 and s = "cmp s (transpos l (Suc n))" and j = "Suc n" in unique_expression3_1, assumption+)
 apply (simp add:Nset_def)
apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) (Suc n) =
e\<Sigma> M (\<lambda>j. (cmp s (transpos l (Suc n))) j \<star>\<^sub>M ((cmp f (transpos l (Suc n))) j)) (Suc n)")
 apply (thin_tac "(cmp f (transpos l (Suc n))) \<in> Nset (Suc n) \<rightarrow> H")
 apply (thin_tac "cmp s (transpos l (Suc n)) \<in> Nset (Suc n) \<rightarrow> carrier R")
 apply (thin_tac " e\<Sigma> M (cmp (\<lambda>j. s j \<star>\<^sub>M (f j)) (transpos l (Suc n))) (Suc n) =
 e\<Sigma> M (\<lambda>j. (cmp s (transpos l (Suc n))) j \<star>\<^sub>M (cmp f (transpos l (Suc n)) j)) (Suc n)")
apply (rule contrapos_pp, simp+)
 apply (simp add:cmp_def) apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in transpos_ij_2,
                                 assumption+) apply simp
 apply (simp add:image_def)
apply (subgoal_tac "\<forall>x\<in>Nset (Suc n) - {Suc n}. f l = f (transpos l (Suc n) x)
 \<longrightarrow> False") apply blast apply (thin_tac " \<exists>x\<in>Nset (Suc n) - {Suc n}. f l = f (transpos l (Suc n) x)")
 apply (rule ballI) apply (rule impI)
 apply (case_tac "x = l") apply simp
 apply (simp add:transpos_ij_1)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n) - {l}")
 apply (subgoal_tac "f (Suc n) \<noteq> f (Suc n)") apply simp
 apply blast apply (simp add:Nset_def)
 apply (subgoal_tac "x \<noteq> Suc n")
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" and x = x in transpos_id_1, assumption+)
 apply simp apply assumption+ apply simp
 apply (subgoal_tac "x \<in> Nset (Suc n) - {l}")
 apply (subgoal_tac "f x \<noteq> f x") apply simp apply blast
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply simp
prefer 2
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (subst cmp_def)
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" and l = x in transpos_mem, assumption+)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
prefer 2
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (subst cmp_def)
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" and l = x in transpos_mem, assumption+)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
prefer 2
 apply (simp add:linear_combination_def)
prefer 3
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
prefer 2
apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subst cmp_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" and l = x in transpos_mem, assumption+)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subst cmp_def) apply (subst cmp_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" and l = x in transpos_mem, assumption+)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem) apply (simp add:funcset_mem subsetD)
 apply (simp add:Nset_def)
apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" and l = la in transpos_mem, assumption+)
 apply (subst cmp_def)+ apply simp apply (simp add:Nset_def)
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>g m. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> (\<exists>t. t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) (cmp s (transpos l (Suc n)))(cmp f (transpos l (Suc n))) = linear_combination R M m t g \<and> t m = cmp s (transpos l (Suc n)) (Suc n)) \<longrightarrow> False")
 apply (thin_tac "\<forall>g m. inj_on g (Nset m) \<longrightarrow> g \<in> Nset m \<rightarrow> H \<longrightarrow> (\<forall>t. linear_combination R M (Suc n) (cmp s (transpos l (Suc n))) (cmp f (transpos l (Suc n))) = linear_combination R M m t g \<longrightarrow> t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> t m \<noteq> s l)")
 apply blast
 apply (thin_tac "\<exists>g m. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> (\<exists>t. t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) (cmp s (transpos l (Suc n))) (cmp f (transpos l (Suc n))) = linear_combination R M m t g \<and> t m = cmp s (transpos l (Suc n)) (Suc n))")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "\<forall>t. linear_combination R M (Suc n) (cmp s (transpos l (Suc n))) (cmp f (transpos l (Suc n))) = linear_combination R M m t g \<longrightarrow> t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> t m \<noteq> s l")
 prefer 2 apply simp
 apply (subgoal_tac "\<forall>t. t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) (cmp s (transpos l (Suc n))) (cmp f (transpos l (Suc n))) = linear_combination R M m t g \<and> t m = cmp s (transpos l (Suc n)) (Suc n) \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>t. t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) (cmp s (transpos l (Suc n))) (cmp f (transpos l (Suc n))) = linear_combination R M m t g \<and> t m = cmp s (transpos l (Suc n)) (Suc n)")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
apply simp
 apply (subgoal_tac "(\<forall>ta. linear_combination R M m t g = linear_combination R M m ta g \<longrightarrow> ta \<in> Nset m \<rightarrow> carrier R \<longrightarrow> t m \<noteq> s l)")
 prefer 2 apply blast
 apply (subgoal_tac "t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> t m \<noteq> s l")
 prefer 2 apply blast
 apply (thin_tac "\<forall>ta. linear_combination R M m t g = linear_combination R M m ta g \<longrightarrow> ta \<in> Nset m \<rightarrow> carrier R \<longrightarrow> t m \<noteq> s l")
 apply simp
 apply (simp add:cmp_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:transpos_ij_2) apply (simp add:Nset_def)
done

lemma unique_expression3:"\<lbrakk>ring R; R module M; H \<subseteq> carrier M; f\<in>Nset (Suc n) \<rightarrow> H; s \<in> Nset (Suc n) \<rightarrow> carrier R; l \<in> Nset (Suc n); (f l) \<notin> f ` (Nset (Suc n) - {l})\<rbrakk> \<Longrightarrow> \<exists>g m t. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc n) s f = linear_combination R M m t g \<and> t m = s l"
apply (case_tac "l = Suc n")
 apply (rule_tac R = R and M = M and H = H and f = f and s = s and j = l and n= n in unique_expression3_1, assumption+)
 apply (rule_tac R = R and M = M and H = H and f = f and s = s and l = l and n= n in unique_expression3_2, assumption+)
done

lemma unique_expression4:"\<lbrakk> ring R; R module M; free_generator R M H\<rbrakk> \<Longrightarrow>
 f\<in>Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and> s \<in> Nset n \<rightarrow> carrier R \<and> linear_combination R M n s f \<noteq> 0\<^sub>M \<longrightarrow> (\<exists>m g t. (g \<in> Nset m \<rightarrow> H) \<and> inj_on g (Nset m) \<and> (g ` (Nset m) \<subseteq> f ` (Nset n)) \<and> (t \<in> Nset m \<rightarrow> carrier R) \<and> (\<forall>l\<in>Nset m. t l \<noteq> 0\<^sub>R) \<and> linear_combination R M n s f = linear_combination R M m t g)"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "\<not> zeroring R")
 prefer 2 apply (rule contrapos_pp, simp+)
 apply (simp add:zeroring_def)
 apply (frule ring_one[of "R"]) apply simp
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = s and n = 0 and m = f in linear_combination_mem, assumption+)
 apply (simp add:whole_ideal) apply (simp add:zero_ideal)
 apply (simp add:free_generator_def) apply (simp add:generator_def)
 apply simp apply assumption
 apply (subgoal_tac "1\<^sub>R \<star>\<^sub>M (linear_combination R M 0 s f) = linear_combination R M 0 s f")
 apply (subgoal_tac "1\<^sub>R \<star>\<^sub>M (linear_combination R M 0 s f) = 0\<^sub>R \<star>\<^sub>M (linear_combination R M 0 s f)") apply simp apply (simp add:sprod_0_m) apply simp
 apply (rule sprod_one, assumption+)
apply (simp add:linear_combination_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (subgoal_tac "f \<in> Nset 0 \<rightarrow> H \<and> inj_on f (Nset 0) \<and> f ` Nset 0 \<subseteq> f ` Nset 0 \<and> (\<exists>t. t \<in> Nset 0 \<rightarrow> carrier R \<and> (\<forall>l\<in>Nset 0. t l \<noteq> 0\<^sub>R) \<and>  s 0 \<star>\<^sub>M (f 0) = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (f j)) 0)") apply blast
 apply simp
 apply (subgoal_tac "s \<in> Nset 0 \<rightarrow> carrier R \<and> (\<forall>l\<in>Nset 0. s l \<noteq> 0\<^sub>R) \<and>  s 0 \<star>\<^sub>M (f 0) =  s 0 \<star>\<^sub>M (f 0)") apply blast apply simp
 apply (rule ballI) apply (simp add:Nset_def)
 apply (rule contrapos_pp, simp+)
 apply (frule_tac R = R and M = M and m = "f 0" in sprod_0_m, assumption+)
 apply (simp add:free_generator_def generator_def) apply (erule conjE)+
 apply (subgoal_tac "0 \<in> {0::nat}")
 apply (simp add:funcset_mem subsetD) apply simp apply simp
 apply (simp add:Nset_def)
apply (rule impI) apply (erule conjE)+
apply (case_tac "s (Suc n) = 0\<^sub>R")
 apply (subgoal_tac "linear_combination R M (Suc n) s f = linear_combination R M n s f") apply simp apply (thin_tac "linear_combination R M (Suc n) s f =
           linear_combination R M n s f")
 apply (frule_tac f = f and n = n and A = H in func_pre)
 apply (frule_tac f = s and n = n and A = "carrier R" in func_pre)
 apply (subgoal_tac "inj_on f (Nset n)") apply simp
prefer 2 apply (subgoal_tac "\<forall>z. z \<in> Nset n \<longrightarrow> z \<in> Nset (Suc n)")
 apply (simp add:inj_on_def) apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def)
prefer 2 apply (simp add:linear_combination_def)
 apply (subgoal_tac "0\<^sub>R \<star>\<^sub>M (f (Suc n)) = 0\<^sub>M") apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_r_zero, assumption+)
 apply (rule_tac R = M and f = "(\<lambda>j.  s j \<star>\<^sub>M (f j))" and n = "Suc n" and i = n in eSum_mem, assumption+)
 apply (rule univar_func_test)
 apply (rule ballI) apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem)
 apply (subgoal_tac "H \<subseteq> carrier M")
apply (simp add:funcset_mem subsetD) apply (simp add:free_generator_def generator_def) apply (simp add:Nset_def)
 apply (rule sprod_0_m, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
  apply (simp add:free_generator_def generator_def)
 apply auto
 apply (subgoal_tac "g ` Nset m \<subseteq> f ` Nset (Suc n)")
 apply blast
 apply (rule subsetI)
 apply (frule_tac A = "g ` Nset m" and B = "f ` Nset n" and c = x in subsetD,
        assumption+) apply (thin_tac "g ` Nset m \<subseteq> f ` Nset n")
 apply (thin_tac "x \<in> g ` Nset m") apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x. x \<in> Nset n \<longrightarrow> x \<in> Nset (Suc n)") apply blast
 apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
 apply (rule func_pre, assumption+)
 apply (subgoal_tac "\<forall>x. x \<in> Nset n \<longrightarrow> x \<in> Nset (Suc n)")
 apply (simp add:inj_on_def)  apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def)
 apply (rule func_pre, assumption+)
apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) \<noteq> 0\<^sub>M")
 apply (subgoal_tac "(\<lambda>x\<in>Nset 0. (s (Suc n))) \<in> (Nset 0) \<rightarrow> carrier R")
 prefer 2 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (subgoal_tac "(\<lambda>k\<in>Nset 0. (f (Suc n))) \<in> (Nset 0) \<rightarrow> H")
 prefer 2 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (subgoal_tac "(\<lambda>k\<in>Nset 0. (f (Suc n))) ` (Nset 0) \<subseteq> f ` Nset (Suc n)")
 apply (subgoal_tac "inj_on (\<lambda>k\<in>Nset 0. (f (Suc n))) (Nset 0)")
 apply (subgoal_tac "\<forall>t. t \<in> Nset 0 \<rightarrow> carrier R \<longrightarrow> (\<exists>l\<in>Nset 0. t l = 0\<^sub>R) \<or>
  linear_combination R M (Suc n) s f \<noteq> linear_combination R M 0 t (\<lambda>k\<in>Nset 0. (f (Suc n)))")  prefer 2 apply blast
 apply (thin_tac "\<forall>m g. g ` Nset m \<subseteq> f ` Nset (Suc n) \<longrightarrow> inj_on g (Nset m) \<longrightarrow> g \<in> Nset m \<rightarrow> H \<longrightarrow> (\<forall>t. t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> (\<exists>l\<in>Nset m. t l = 0\<^sub>R) \<or> linear_combination R M (Suc n) s f \<noteq> linear_combination R M m t g)")apply (simp add:Nset_def)apply (subgoal_tac "(\<lambda>x\<in>{0::nat}. s (Suc n)) 0 = 0\<^sub>R \<or> linear_combination R M (Suc n) s f \<noteq> linear_combination R M 0 (\<lambda>x\<in>{0}. s (Suc n)) (\<lambda>k\<in>{0}. f (Suc n))") prefer 2 apply blast
apply (thin_tac "\<forall>t. t \<in> {0::nat} \<rightarrow> carrier R \<longrightarrow> t 0 = 0\<^sub>R \<or> linear_combination R M (Suc n) s f \<noteq> linear_combination R M 0 t (\<lambda>k\<in>{0}. f (Suc n))")
 apply (fold Nset_def)
apply (case_tac "(\<lambda>x\<in>{0::nat}. s (Suc n)) 0 = 0\<^sub>R") apply simp
 apply simp
 apply (simp add:linear_combination_def)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = 0\<^sub>M")
 apply (subgoal_tac " 0\<^sub>M +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n))) =  s (Suc n) \<star>\<^sub>M (f (Suc n))") apply simp
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) \<in> carrier M")
 apply (simp add:ag_l_zero)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem)
 apply (simp add:free_generator_def generator_def) apply (erule conjE)+
apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
apply (thin_tac "\<forall>m g. g ` Nset m \<subseteq> f ` Nset (Suc n) \<longrightarrow> inj_on g (Nset m) \<longrightarrow>
g \<in> Nset m \<rightarrow> H \<longrightarrow> (\<forall>t. t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> (\<exists>l\<in>Nset m. t l = 0\<^sub>R) \<or>
linear_combination R M (Suc n) s f \<noteq> linear_combination R M m t g)")
apply (subst inj_on_def) apply (simp add:Nset_def)
 apply (thin_tac "\<forall>m g. g ` Nset m \<subseteq> f ` Nset (Suc n) \<longrightarrow> inj_on g (Nset m)    \<longrightarrow> g \<in> Nset m \<rightarrow> H \<longrightarrow> (\<forall>t. t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> (\<exists>l\<in>Nset m. t l =
 0\<^sub>R) \<or> linear_combination R M (Suc n) s f \<noteq> linear_combination R M m t g)")
 apply (rule subsetI) apply (simp add:image_def) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<le> Suc n") apply blast apply simp
 apply (thin_tac "\<forall>m g. g ` Nset m \<subseteq> f ` Nset (Suc n) \<longrightarrow> inj_on g (Nset m) \<longrightarrow> g \<in> Nset m \<rightarrow> H \<longrightarrow> (\<forall>t. t \<in> Nset m \<rightarrow> carrier R \<longrightarrow> (\<exists>l\<in>Nset m. t l = 0\<^sub>R) \<or> linear_combination R M (Suc n) s f \<noteq> linear_combination R M m t g)")
apply (simp add:linear_combination_def)
 apply (subgoal_tac " 0\<^sub>M +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n))) =  s (Suc n) \<star>\<^sub>M (f (Suc n))") apply simp
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) \<in> carrier M")
 apply (simp add:ag_l_zero)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem)
 apply (simp add:free_generator_def generator_def) apply (erule conjE)+
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
apply (subgoal_tac "jointfun m g 0 (\<lambda>x. (f (Suc n))) \<in> Nset (Suc m) \<rightarrow> H")
 apply (subgoal_tac "inj_on (jointfun m g 0 (\<lambda>x. (f (Suc n)))) (Nset (Suc m))")
 apply (subgoal_tac "(jointfun m g 0 (\<lambda>x. (f (Suc n)))) ` (Nset (Suc m)) \<subseteq>
                                      f ` (Nset (Suc n))")
 apply (subgoal_tac "(jointfun m t 0 (\<lambda>x. (s (Suc n)))) \<in> Nset (Suc m) \<rightarrow> carrier R")
 apply (subgoal_tac "\<forall>l\<in>Nset (Suc m). (jointfun m t 0 (\<lambda>x. (s (Suc n)))) l \<noteq> 0\<^sub>R")
 apply (subgoal_tac "linear_combination R M (Suc n) s f =  linear_combination R
 M (Suc m) (jointfun m t 0 (\<lambda>x. (s (Suc n)))) (jointfun m g 0 (\<lambda>x. (f (Suc n))))")
 apply blast
 apply (subst linear_combination_def)+ apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = e\<Sigma> M (\<lambda>j. jointfun m t 0 (\<lambda>x. s (Suc n)) j \<star>\<^sub>M (jointfun m g 0 (\<lambda>x. f (Suc n)) j)) m")
 apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) = (jointfun m t 0 (\<lambda>x. s (Suc n))) (Suc m) \<star>\<^sub>M (jointfun m g 0 (\<lambda>x. f (Suc n)) (Suc m))")
 apply simp
 apply (subst jointfun_def)+ apply simp
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "(\<lambda>j.  t j \<star>\<^sub>M (g j)) \<in> Nset m \<rightarrow> carrier M")
 apply (rule_tac R = M and f = "\<lambda>j.  t j \<star>\<^sub>M (g j)" and n = m and g = "\<lambda>j. jointfun m t 0 (\<lambda>x. s (Suc n)) j \<star>\<^sub>M (jointfun m g 0 (\<lambda>x. f (Suc n)) j)" in  eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<le> m")
 apply (subst jointfun_def)+ apply simp
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (subgoal_tac "H \<subseteq> carrier M")
 apply (simp add:funcset_mem subsetD)
 apply (simp add:free_generator_def generator_def) apply (simp add:Nset_def)
 apply (rule ballI) apply (subgoal_tac "l \<le> m")
 apply (subst jointfun_def)+ apply simp apply (simp add:Nset_def)
 apply (rule univar_func_test) apply (rule ballI) apply (subgoal_tac "x \<le> m")
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:funcset_mem subsetD)
 apply (simp add:free_generator_def generator_def) apply (simp add:Nset_def)
 apply (rule ballI) apply (case_tac "l = Suc m")
 apply (subst jointfun_def) apply simp
 apply (subgoal_tac "l \<in> Nset m") apply (subgoal_tac "l \<le> m")
 apply (subst jointfun_def) apply simp apply (simp add:Nset_def)
 apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "x = Suc m") apply (simp add:jointfun_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (subgoal_tac "x \<in> Nset m") apply (subgoal_tac "x \<le> m")
 apply (subst jointfun_def) apply simp apply (simp add:funcset_mem)
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (frule_tac f = g and n = m and A = H and g = "\<lambda>x. f (Suc n)" and m = 0 and B = H in im_jointfun)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (simp add:funcset_mem)
 apply (simp add:Nset_def)
 apply (simp del:Un_subset_iff)
 apply (subgoal_tac "Nset n \<subseteq> Nset (Suc n)")
 apply (frule_tac f = f and A = "Nset (Suc n)" and B = H and ?A1.0 = "Nset n"  and ?A2.0 = "Nset (Suc n)" in im_set_mono, assumption+) apply simp
 apply (subgoal_tac "(\<lambda>x. f (Suc n)) ` Nset 0 \<subseteq> f ` Nset (Suc n)")
 apply (rule subsetI) apply (case_tac "x \<in> g ` Nset m")
 apply (simp add:subsetD)+
 apply (simp add:Nset_def) apply (rule subsetI) apply (simp add:Nset_def)
apply (subst inj_on_def)
 apply (rule ballI)+ apply (rule impI)
 apply (thin_tac "linear_combination R M (Suc n) s f \<noteq> 0\<^sub>M")
 apply (thin_tac "\<forall>l\<in>Nset m. t l \<noteq> 0\<^sub>R")
 apply (case_tac "x \<in> Nset m")
 apply (case_tac "y \<in> Nset m")
  apply (thin_tac "inj_on f (Nset (Suc n))")
  apply (thin_tac "linear_combination R M n s f = linear_combination R M m t g")
  apply (subgoal_tac "x \<le> m") apply (subgoal_tac "y \<le> m")
  apply (simp add:jointfun_def) apply (simp add:inj_on_def)
  apply (simp add:Nset_def) apply (simp add:Nset_def)
  apply (subgoal_tac "y = Suc m") apply (subgoal_tac "x \<le> m")
  apply (simp add:jointfun_def)
  apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image,
  assumption+)
  apply (frule_tac A = "g ` Nset m" and B = "f ` Nset n" and c = "g x" in subsetD, assumption+) apply simp
  apply (thin_tac "f (Suc n) \<in> g ` Nset m")
  apply (thin_tac "g ` Nset m \<subseteq> f ` Nset n")
  apply (simp add:image_def) apply (subgoal_tac "\<forall>x\<in>Nset n. f (Suc n) = f x \<longrightarrow> False") apply blast apply (thin_tac "\<exists>x\<in>Nset n. f (Suc n) = f x")
  apply (rule ballI) apply (rule impI)
  apply (subgoal_tac "xa \<noteq> Suc n") prefer 2 apply (simp add:Nset_def)
  apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
  apply (subgoal_tac "xa \<in> Nset (Suc n)") apply (simp add:inj_on_def)
  apply (simp add:Nset_def) apply (simp add:Nset_def) apply (simp add:Nset_def)
  apply (simp add:Nset_def)
  apply (subgoal_tac "x = Suc m")
   apply (case_tac "y \<in> Nset m") apply (subgoal_tac "Suc m \<noteq> y")
   apply (subgoal_tac "y \<le> m") apply (simp add:jointfun_def)
  apply (frule_tac f = g and A = "Nset m" and B = H and a = y in mem_in_image,
  assumption+) apply (rotate_tac -6) apply (frule sym)
  apply (thin_tac "f (Suc n) = g y") apply simp
  apply (frule_tac A = "g ` Nset m" and B = "f ` Nset n" and c = "f (Suc n)" in subsetD, assumption+)
  apply (thin_tac "f (Suc n) \<in> g ` Nset m")
  apply (thin_tac "g ` Nset m \<subseteq> f ` Nset n")
  apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>Nset n. f (Suc n) = f x \<longrightarrow> False") apply blast
  apply (thin_tac "\<exists>x\<in>Nset n. f (Suc n) = f x") apply (rule ballI)
  apply (rule impI)
  apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
  apply (subgoal_tac "xa \<in> Nset (Suc n)")
 apply (subgoal_tac "Suc n = xa") prefer 2 apply (simp add:inj_on_def)
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply (simp add:Nset_def)
  (** here simp runs very well **)
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (subgoal_tac "y = Suc m") apply simp
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (frule_tac f = g and n = m and A = H and g = "\<lambda>x. f (Suc n)" and m = 0 and B = H in jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (simp add:funcset_mem)
 apply (simp add:Nset_def)
 apply simp
done

lemma unique_expression5:"\<lbrakk>ring R; R module M; free_generator R M H; f\<in>Nset n \<rightarrow> H; inj_on f (Nset n); s \<in> Nset n \<rightarrow> carrier R; g \<in> Nset m \<rightarrow> H; inj_on g (Nset m); t \<in> Nset m \<rightarrow> carrier R; linear_combination R M n s f = linear_combination R M m t g; \<forall>j\<in>Nset n. s j \<noteq> 0\<^sub>R; \<forall>k\<in>Nset m. t k \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow> f ` (Nset n) \<subseteq> g ` (Nset m)"
apply (rule contrapos_pp, simp+) apply (simp add:subset_def)
apply (subgoal_tac "\<forall>x\<in>Nset n. f x \<notin> g ` (Nset m) \<longrightarrow> False")
apply blast apply (thin_tac "\<exists>x\<in>Nset n. f x \<notin> g ` Nset m")
 apply (rule ballI) apply (rule impI)
 apply (frule whole_ideal [of "R"])
 apply (subgoal_tac "H \<subseteq> carrier M") prefer 2
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = s
 and n = n and m = f in linear_combination_mem, assumption+)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = t
 and n = m and m = g in linear_combination_mem, assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "(linear_combination R M n s f) +\<^sub>M (-\<^sub>M (linear_combination R M m t g)) = 0\<^sub>M") prefer 2 apply (simp add:ag_r_inv1)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and f = g and n = m and s = t in linear_span_iOp_closedTr2, assumption+)
 apply simp apply (thin_tac "-\<^sub>M (linear_combination R M m t g) =
           linear_combination R M m (\<lambda>x\<in>Nset m. -\<^sub>R (t x)) g")
 apply (frule sym) apply (thin_tac "linear_combination R M n s f = linear_combination R M m t g") apply simp
 apply (thin_tac "linear_combination R M m t g = linear_combination R M n s f")
 apply (simp add:linear_combination_def)
apply (subgoal_tac "(\<lambda>j. s j \<star>\<^sub>M (f j)) \<in> Nset n \<rightarrow> carrier M")
apply (frule_tac G = M and f = "\<lambda>j. s j \<star>\<^sub>M (f j)" and n = n and g = "(\<lambda>j. (if j \<in> Nset m then -\<^sub>R (t j) else arbitrary) \<star>\<^sub>M (g j))" and m = m in eSum_jointfun, assumption+)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (rule sprod_mem, assumption+)
 apply (frule ring_is_ag [of "R"])
 apply (rule ag_mOp_closed [of "R"], assumption+)
 apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
prefer 2
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD) apply (simp del:eSum_Suc)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n +\<^sub>M (e\<Sigma> M (\<lambda>j.  (if j \<in> Nset m then -\<^sub>R t j else arbitrary) \<star>\<^sub>M (g j)) m) = 0\<^sub>M")
apply (subgoal_tac "(jointfun n s m (\<lambda>l. (-\<^sub>R (t l)))) \<in> Nset (Suc (n + m)) \<rightarrow> (carrier R)")
 prefer 2
 apply (frule_tac f = s and n = n and A = "carrier R" and g = "\<lambda>l. -\<^sub>R (t l)"
 and m = m and B = "carrier R" in jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule ring_is_ag [of "R"]) apply (rule ag_mOp_closed, assumption+)
 apply (simp add:funcset_mem) apply simp
apply (subgoal_tac "(jointfun n f m g) \<in> Nset (Suc (n + m)) \<rightarrow> H")
 prefer 2
 apply (frule_tac f = f and n = n and A = H and g = g  and m = m and B = H in jointfun_hom0, assumption+)  apply simp
apply (subgoal_tac "e\<Sigma> M (jointfun n (\<lambda>j. s j \<star>\<^sub>M (f j)) m (\<lambda>j. (if j \<in> Nset m then -\<^sub>R (t j) else arbitrary) \<star>\<^sub>M (g j))) (Suc (n + m)) = e\<Sigma> M (\<lambda>j. (jointfun n s m (\<lambda>l. (-\<^sub>R (t l)))) j \<star>\<^sub>M ((jointfun n f m g) j)) (Suc (n + m))")
apply (simp del:eSum_Suc)
 prefer 2 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule eSum_eq, assumption+)
 apply (frule_tac f = "\<lambda>j.  s j \<star>\<^sub>M (f j)" and n = n and A = "carrier M" and
 g = "\<lambda>j.  (if j \<in> Nset m then -\<^sub>R (t j) else arbitrary) \<star>\<^sub>M (g j)" and m = m and B = "carrier M" in  jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (rule sprod_mem, assumption+)
 apply (frule ring_is_ag [of "R"])
 apply (rule ag_mOp_closed, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
 apply simp
 apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "xa \<in> Nset n") apply (subgoal_tac "xa \<le> n")
 apply (simp add:jointfun_def)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
 apply (subgoal_tac "\<not> xa \<le> n")
 apply (simp add:jointfun_def slide_def sliden_def)
 apply (subgoal_tac "(xa - Suc n) \<in> Nset m") apply (subgoal_tac "(xa - Suc n) \<in> Nset m")
 apply (rule sprod_mem, assumption+)
 apply (frule ring_is_ag [of "R"])
 apply (rule ag_mOp_closed, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD) apply assumption
 apply (simp add:Nset_def) apply (subgoal_tac "n < xa") prefer 2 apply simp
 apply (thin_tac "\<not> xa \<le> n") apply (subgoal_tac "Suc n \<le> xa")
 prefer 2 apply simp  apply (thin_tac "n < xa")
 apply (frule_tac m = xa and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
 apply simp apply (simp add:Nset_def)
apply (rule ballI)
 apply (case_tac "l \<le> n")
 apply (simp add:jointfun_def)
 apply (simp add:jointfun_def sliden_def slide_def)
 apply (simp add:le_def) apply (subgoal_tac "Suc n \<le> l") prefer 2 apply simp
 apply (simp add:Nset_def)
 apply (frule_tac m = l and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
 apply simp
 apply (frule_tac R = R and M = M and H = H and f = "jointfun n f m g" and n = "n + m" and s = "jointfun n s m (\<lambda>l. -\<^sub>R (t l))" and l = x in unique_expression3, assumption+)  apply (simp add:Nset_def)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. jointfun n s m (\<lambda>l. -\<^sub>R (t l)) j \<star>\<^sub>M (jointfun n f m g j)) (Suc (n + m)) = 0\<^sub>M")
 apply (thin_tac "e\<Sigma> M (jointfun n (\<lambda>j.  s j \<star>\<^sub>M (f j)) m (\<lambda>j. (if j \<in> Nset m then -\<^sub>R (t j) else arbitrary) \<star>\<^sub>M (g j))) (Suc (n + m)) =  0\<^sub>M")
 apply (subst image_def) apply simp apply (rule ballI)
 apply (case_tac "xa \<in> Nset n") apply (subgoal_tac "xa \<le> n")
 apply (subgoal_tac "x \<le> n")
 apply (simp add:jointfun_def) apply (erule conjE)
 apply (simp add:injective) apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (subgoal_tac "\<not> xa \<le> n") prefer 2 apply (simp add:Nset_def)
 apply (simp add:le_def) apply (subgoal_tac "Suc n \<le> xa") prefer 2 apply simp
 apply (erule conjE) apply (simp add:Nset_def) apply (fold Nset_def)
 apply (frule_tac m = xa and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
 apply simp
 apply (simp add:jointfun_def slide_def sliden_def)
 apply (frule_tac f = g and A = "Nset m" and B = H and a = "xa - Suc n" in mem_in_image) apply (simp add:Nset_def)
 apply (rule contrapos_pp, simp+)
apply (subgoal_tac "\<forall>ga ma. ga \<in> Nset ma \<rightarrow> H \<and> inj_on ga (Nset ma) \<and>
 (\<exists>ta. ta \<in> Nset ma \<rightarrow> carrier R \<and>  linear_combination R M (Suc (n + m))
 (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (jointfun n f m g) = linear_combination R M ma ta ga \<and> ta ma = jointfun n s m (\<lambda>l. -\<^sub>R (t l)) x) \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>ga ma. ga \<in> Nset ma \<rightarrow> H \<and> inj_on ga (Nset ma) \<and>
 (\<exists>ta. ta \<in> Nset ma \<rightarrow> carrier R \<and>  linear_combination R M (Suc (n + m))
 (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (jointfun n f m g) = linear_combination R M ma ta ga \<and> ta ma = jointfun n s m (\<lambda>l. -\<^sub>R (t l)) x)")
 apply (rule allI)+ apply (rule impI)
 apply (erule conjE)+
 apply (subgoal_tac "\<forall>ta. ta \<in> Nset ma \<rightarrow> carrier R \<and> linear_combination R M (Suc (n + m)) (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (jointfun n f m g) = linear_combination R M ma ta ga \<and> ta ma = jointfun n s m (\<lambda>l. -\<^sub>R (t l)) x \<longrightarrow> False")
 apply blast
 apply (thin_tac "\<exists>ta. ta \<in> Nset ma \<rightarrow> carrier R \<and> linear_combination R M (Suc (n + m)) (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (jointfun n f m g) = linear_combination R M ma ta ga \<and> ta ma = jointfun n s m (\<lambda>l. -\<^sub>R (t l)) x")
 apply (rule allI) apply (rule impI)
 apply (erule conjE)
 apply (subgoal_tac "linear_combination R M (Suc (n + m)) (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (jointfun n f m g) = 0\<^sub>M") prefer 2 apply (simp add:linear_combination_def) apply simp apply (thin_tac "linear_combination R M (Suc (n + m)) (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (jointfun n f m g) = linear_combination R M ma ta ga")
 apply (thin_tac "e\<Sigma> M jointfun n (\<lambda>j. s j \<star>\<^sub>M (f j)) m (\<lambda>j. (if j \<in> Nset m then -\<^sub>R (t j) else arbitrary) \<star>\<^sub>M (g j)) (n + m) +\<^sub>M (jointfun n (\<lambda>j. s j \<star>\<^sub>M (f j)) m (\<lambda>j. (if j \<in> Nset m then -\<^sub>R (t j) else arbitrary) \<star>\<^sub>M (g j))) (Suc (n + m)) = linear_combination R M ma ta ga")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. jointfun n s m (\<lambda>l. -\<^sub>R (t l)) j \<star>\<^sub>M
 (jointfun n f m g j)) (n + m) +\<^sub>M (jointfun n s m (\<lambda>l. -\<^sub>R (t l))) (Suc (n + m)) \<star>\<^sub>M (jointfun n f m g (Suc (n + m))) = linear_combination R M ma ta ga")
 apply (erule conjE)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n \<in> carrier M")
 apply (thin_tac "jointfun n s m (\<lambda>l. -\<^sub>R (t l)) \<in> Nset (Suc (n + m)) \<rightarrow> carrier R")
 apply (thin_tac "jointfun n f m g \<in> Nset (Suc (n + m)) \<rightarrow> H")
 apply (subgoal_tac "x \<le> n") apply (simp add:jointfun_def)
 prefer 2 apply (simp add:Nset_def)
 apply (subgoal_tac "s x \<noteq> 0\<^sub>R") prefer 2 apply simp
 apply (thin_tac "\<forall>j\<in>Nset n. s j \<noteq> 0\<^sub>R") apply (rotate_tac -3)
 apply (frule sym) apply (thin_tac "ta ma = s x") apply simp
 apply (thin_tac "s x = ta ma") apply (frule sym)
 apply (thin_tac "0\<^sub>M = linear_combination R M ma ta ga")
 apply (frule_tac R = R and M = M and H = H and s = ta and n = ma and m = ga in  unique_expression1, assumption+)
 apply (subgoal_tac "ma \<in> Nset ma") apply blast
 apply (simp add:Nset_def)
done

lemma unique_expression6:"\<lbrakk>ring R; R module M; free_generator R M H; f\<in>Nset n \<rightarrow> H; inj_on f (Nset n); s \<in> Nset n \<rightarrow> carrier R; g \<in> Nset m \<rightarrow> H; inj_on g (Nset m); t \<in> Nset m \<rightarrow> carrier R; linear_combination R M n s f = linear_combination R M m t g; \<forall>j\<in>Nset n. s j \<noteq> 0\<^sub>R; \<forall>k\<in>Nset m. t k \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow> f ` (Nset n) = g ` (Nset m)"
apply (rule equalityI)
apply (rule_tac R = R and M = M and H = H and f = f and n = n and s = s and g = g and m = m and t = t in unique_expression5, assumption+)
apply (rule_tac R = R and M = M and H = H and f = g and n = m and s = t and g = f and m = n and t = s in unique_expression5, assumption+)
apply (rule sym) apply assumption apply blast apply blast
done

lemma unique_expression7_1:"\<lbrakk>ring R; R module M; free_generator R M H; f\<in>Nset n \<rightarrow> H; inj_on f (Nset n); s \<in> Nset n \<rightarrow> carrier R; g \<in> Nset m \<rightarrow> H; inj_on g (Nset m); t \<in> Nset m \<rightarrow> carrier R; linear_combination R M n s f = linear_combination R M m t g; \<forall>j\<in>Nset n. s j \<noteq> 0\<^sub>R; \<forall>k\<in>Nset m. t k \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow> n = m"
apply (insert finite_Nset [of "n"])
apply (insert finite_Nset [of "m"])
apply (frule_tac A = "Nset n" and f = f in card_image)
apply (frule_tac A = "Nset m" and f = g in card_image)
apply (frule_tac R = R and M = M and H = H and f = f and n = n and s = s and g = g and t = t and m = m in unique_expression6, assumption+)
apply (rotate_tac -3) apply (frule sym) apply (thin_tac "card (f ` Nset n) = card (Nset n)")
apply simp
apply (simp add:card_Nset)
done

lemma unique_expression7_2Tr:"\<lbrakk>ring R; R module M; free_generator R M H\<rbrakk> \<Longrightarrow>  f\<in>Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and>  s \<in> Nset n \<rightarrow> carrier R \<and> t \<in> Nset n\<rightarrow> carrier R \<and> linear_combination R M n s f = linear_combination R M n t f \<longrightarrow> (\<forall>l\<in>Nset n. s l = t l)"
apply (induct_tac n)
 apply (rule impI)
 apply (erule conjE)+ apply (subgoal_tac "H \<subseteq> carrier M")
 apply (simp add:linear_combination_def)
 apply (simp add:Nset_def)
 apply (subgoal_tac "0 \<in> {0::nat}")
 apply (frule_tac f = s and A = "{0::nat}" and B = "carrier R" and x = 0 in funcset_mem, assumption+)
 apply (frule_tac f = t and A = "{0::nat}" and B = "carrier R" and x = 0 in funcset_mem, assumption+)
 apply (frule_tac f = f and A = "{0::nat}" and B = H and x = 0 in funcset_mem, assumption+)
 apply (frule_tac R = R and M = M and a = "s 0" and m = "f 0" in sprod_mem,
                assumption+) apply (simp add:funcset_mem subsetD)
 apply (frule_tac R = R and M = M and a = "t 0" and m = "f 0" in
               sprod_mem,  assumption+) apply (simp add:funcset_mem subsetD)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac G = M and x = "t 0 \<star>\<^sub>M (f 0)" in ag_r_inv1, assumption+)
 apply (frule_tac R = R and M = M and a = "t 0" and m = "f 0" in sprod_minus_am1, assumption+) apply (simp add:subsetD) apply simp
 apply (thin_tac "-\<^sub>M  (t 0 \<star>\<^sub>M (f 0)) =  (-\<^sub>R (t 0)) \<star>\<^sub>M (f 0)")
 apply (frule sym) apply (thin_tac " s 0 \<star>\<^sub>M (f 0) =  t 0 \<star>\<^sub>M (f 0)") apply simp
 apply (thin_tac "t 0 \<star>\<^sub>M (f 0) =  s 0 \<star>\<^sub>M (f 0)")
 apply (frule_tac R1 = R and M1 = M and a1 = "s 0" and b1 = "-\<^sub>R (t 0)" and m1 = "f 0" in sprod_distrib1 [THEN sym], assumption+)
 apply (frule ring_is_ag [of "R"]) apply (rule ag_mOp_closed, assumption+)
 apply (simp add:funcset_mem subsetD)
 apply simp apply (thin_tac "s 0 \<star>\<^sub>M (f 0) +\<^sub>M  (-\<^sub>R (t 0)) \<star>\<^sub>M (f 0) = 0\<^sub>M")
 apply (simp add:free_generator_def) apply (erule conjE)
 apply (subgoal_tac "(\<lambda>l. s 0 +\<^sub>R (-\<^sub>R (t 0))) \<in> Nset 0 \<rightarrow> carrier R")
 apply (subgoal_tac "(\<exists>f. f \<in> Nset 0 \<rightarrow> H \<and> inj_on f (Nset 0) \<and> linear_combination R M 0 (\<lambda>l.  s 0 +\<^sub>R (-\<^sub>R (t 0))) f = 0\<^sub>M) \<longrightarrow> (\<lambda>l.  s 0 +\<^sub>R (-\<^sub>R (t 0))) \<in> Nset 0 \<rightarrow> {0\<^sub>R}") prefer 2 apply simp
 apply (thin_tac "\<forall>n s. s \<in> Nset n \<rightarrow> carrier R \<and> (\<exists>f. f \<in> Nset n \<rightarrow> H \<and>
 inj_on f (Nset n) \<and> linear_combination R M n s f = 0\<^sub>M) \<longrightarrow> s \<in> Nset n \<rightarrow> {0\<^sub>R}")
 apply (simp add:Nset_def)
 apply (subgoal_tac "linear_combination R M 0 (\<lambda>l.  s 0 +\<^sub>R (-\<^sub>R (t 0))) f = 0\<^sub>M")apply (subgoal_tac "(\<lambda>l. s 0 +\<^sub>R (-\<^sub>R (t 0))) \<in> {0::nat} \<rightarrow> {0\<^sub>R}")
 apply (frule_tac f = "\<lambda>l.  s 0 +\<^sub>R (-\<^sub>R (t 0))" and A = "{0}" and B = "{0\<^sub>R}" and x = 0 in funcset_mem) apply simp apply simp
 apply (subgoal_tac "(s 0 +\<^sub>R (-\<^sub>R (t 0))) +\<^sub>R (t 0) = t 0") prefer 2 apply simp
 apply (frule ring_is_ag [of "R"])  apply (simp add:ag_l_zero)
apply (frule_tac ring_is_ag[of "R"])
apply (frule_tac G = R and x = "t 0" in ag_mOp_closed, assumption+)
 apply (frule_tac G = R and x = "s 0" and y = "-\<^sub>R (t 0)" and z = "t 0" in
 ag_pOp_assoc, assumption+) apply (simp add:ag_l_inv1)
 apply (simp add:ag_r_zero [THEN sym]) apply blast
 apply (simp add:linear_combination_def)
 apply (thin_tac "\<forall>n s. s \<in> Nset n \<rightarrow> carrier R \<and> (\<exists>f. f \<in> Nset n \<rightarrow> H \<and>
 inj_on f (Nset n) \<and> linear_combination R M n s f = 0\<^sub>M) \<longrightarrow> s \<in> Nset n \<rightarrow> {0\<^sub>R}")
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule ring_is_ag [of "R"]) apply (rule ag_pOp_closed, assumption+)
 apply (rule ag_mOp_closed, assumption+) apply simp
apply (simp add:free_generator_def generator_def)
apply (rule impI) apply (erule conjE)+
 apply (frule_tac f = f and n = n and A = H in func_pre)
 apply (subgoal_tac "s (Suc n) = t (Suc n)")
 apply (subgoal_tac "inj_on f (Nset n)")
 apply (frule_tac f = s and n = n and A = "carrier R" in func_pre)
 apply (frule_tac f = t and n = n and A = "carrier R" in func_pre)
 apply (subgoal_tac "linear_combination R M n s f = linear_combination R M n t f") apply simp
 apply (rule ballI)
 apply (case_tac "l \<in> Nset n") apply simp apply (simp add:Nset_def)
 apply (subgoal_tac "l = Suc n") apply simp apply simp
 apply (thin_tac "f \<in> Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and> s \<in> Nset n \<rightarrow> carrier R \<and>  t \<in> Nset n \<rightarrow> carrier R \<and> linear_combination R M n s f = linear_combination R M n t f \<longrightarrow> (\<forall>l\<in>Nset n. s l = t l)")
 apply (simp add:linear_combination_def)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = s and n = n and m = f in linear_combination_mem, assumption+)
 apply (simp add:whole_ideal) apply (simp add:free_generator_def generator_def)
 apply (rule func_pre, assumption+)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = t and n = n and m = f in linear_combination_mem, assumption+)
 apply (simp add:whole_ideal) apply (simp add:free_generator_def generator_def)
 apply (rule func_pre, assumption+) apply (simp add:linear_combination_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule_tac G = M and a = "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n" and b = "e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (f j)) n" and c = "t (Suc n) \<star>\<^sub>M (f (Suc n))" in pOp_cancel_r, assumption+)
 apply (rule sprod_mem, assumption+) apply (rule funcset_mem, assumption+)
 apply (simp add:Nset_def) apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:funcset_mem subsetD)
 apply (simp add:free_generator_def generator_def) apply (simp add:Nset_def)
 apply assumption
 apply (subgoal_tac "\<forall>z. z \<in> Nset n \<longrightarrow> z \<in> Nset (Suc n)")
 apply (simp add:inj_on_def) apply (rule allI) apply (rule impI)
 apply (thin_tac "f \<in> Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and> s \<in> Nset n \<rightarrow> carrier R \<and> t \<in> Nset n \<rightarrow> carrier R \<and> linear_combination R M n s f = linear_combination R M n t f \<longrightarrow> (\<forall>l\<in>Nset n. s l = t l)")
 apply (simp add:Nset_def)
 apply (thin_tac "f \<in> Nset n \<rightarrow> H \<and> inj_on f (Nset n) \<and> s \<in> Nset n \<rightarrow> carrier R \<and> t \<in> Nset n \<rightarrow> carrier R \<and> linear_combination R M n s f = linear_combination R M n t f \<longrightarrow> (\<forall>l\<in>Nset n. s l = t l)")
 apply (frule whole_ideal [of "R"])
 apply (subgoal_tac "H \<subseteq> carrier M") prefer 2 apply (simp add:free_generator_def generator_def)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = s
 and n = "Suc n" and m = f in linear_combination_mem, assumption+)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = t
 and n = "Suc n" and m = f in linear_combination_mem, assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac G = M and x = "linear_combination R M (Suc n) s f" in ag_r_inv1, assumption+) apply simp
 apply (frule_tac R = R and M = M and A = "carrier R" and H = H and f = f and s = t and n = "Suc n" in linear_span_iOp_closedTr2, assumption+) apply simp
 apply (thin_tac " -\<^sub>M (linear_combination R M (Suc n) t f) =
           linear_combination R M (Suc n) (\<lambda>x\<in>Nset (Suc n). -\<^sub>R (t x)) f")
 apply (frule sym) apply (thin_tac "linear_combination R M (Suc n) s f =
           linear_combination R M (Suc n) t f") apply simp
 apply (thin_tac "linear_combination R M (Suc n) t f = linear_combination R M (Suc n) s f")
apply (subgoal_tac "(\<lambda>j. s j \<star>\<^sub>M (f j)) \<in> Nset n \<rightarrow> carrier M")
prefer 2  apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = s and n = n and A = "carrier R" in func_pre)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
apply (subgoal_tac "linear_combination R M (Suc n) s f = linear_combination R M n s f +\<^sub>M (s (Suc n) \<star>\<^sub>M (f (Suc n)))") prefer 2 apply (simp add:linear_combination_def)
apply (subgoal_tac "linear_combination R M (Suc n) (\<lambda>x\<in>Nset (Suc n). -\<^sub>R (t x)) f = linear_combination R M n (\<lambda>x\<in>Nset (Suc n). -\<^sub>R (t x)) f +\<^sub>M ((-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f (Suc n)))") prefer 2 apply (simp add:linear_combination_def)
 apply (simp add:Nset_def)
apply simp
 apply (thin_tac "linear_combination R M (Suc n) s f = linear_combination R M n s f +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n)))")
 apply (thin_tac "linear_combination R M (Suc n) (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f = (linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f) +\<^sub>M ((-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f (Suc n)))")
 apply (frule_tac f = s and n = n and A = "carrier R" in func_pre)
 apply (frule_tac f = t and n = n and A = "carrier R" in func_pre)
 apply (frule_tac f = f and n = n and A = H in func_pre)
apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = s and m = f and n = n in linear_combination_mem, assumption+)
apply (frule_tac R = R and M = M and A = "carrier R" and H = H and s = "\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))" and m = f and n = n in linear_combination_mem, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<in> Nset (Suc n)") prefer 2 apply (simp add:Nset_def)
 apply simp apply (frule ring_is_ag [of "R"]) apply (rule ag_mOp_closed, assumption+) apply (simp add:funcset_mem) apply assumption
 apply (frule_tac R = R and M = M and a = "s (Suc n)" and m = "f (Suc n)" in
 sprod_mem, assumption+) apply (rule funcset_mem, assumption+)
 apply (simp add:Nset_def) apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
 apply (frule_tac R = R and M = M and a = "-\<^sub>R (t (Suc n))" and m = "f (Suc n)"
 in  sprod_mem, assumption+) apply (frule ring_is_ag [of "R"])
 apply (rule ag_mOp_closed, assumption+) apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
 apply (frule_tac G = M and a = "linear_combination R M n s f" and b = "s (Suc n) \<star>\<^sub>M (f (Suc n))" and c = "linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f" and d = "(-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f (Suc n))" in ag_add4_rel, assumption+)
 apply simp
 apply (thin_tac "linear_combination R M n s f +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n)))
 +\<^sub>M (linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f +\<^sub>M (-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f (Suc n))) = 0\<^sub>M")
 apply (subgoal_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) +\<^sub>M ((-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f (Suc n))) = (s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) \<star>\<^sub>M (f (Suc n))") apply simp
 apply (thin_tac "s (Suc n) \<star>\<^sub>M (f (Suc n)) +\<^sub>M  (-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f (Suc n)) = (s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) \<star>\<^sub>M (f (Suc n))")
prefer 2 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (rule sprod_distrib1 [THEN sym], assumption+)
 apply (simp add:funcset_mem)
 apply (frule ring_is_ag [of "R"]) apply (rule ag_mOp_closed, assumption+)
 apply (simp add:funcset_mem) apply (simp add:funcset_mem subsetD)
 apply (simp add:Nset_def)
apply (frule_tac R = R and M = M and A = "carrier R" and H = "f ` (Nset n)" and
 a = "linear_combination R M n s f" and b = "linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f" in linear_span_tOp_closed, assumption+)
 apply (frule_tac f = f and A = "Nset n" and B = H and ?A1.0 = "Nset n" in image_sub) apply simp
 apply (rule subset_trans, assumption+)
 apply (subst linear_span_def) apply (subgoal_tac "f ` Nset n \<noteq> {}") apply simp
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> f ` (Nset n)") apply blast
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:mem_in_image)
 apply (subgoal_tac "0 \<in> Nset n")
 apply (frule_tac f = f and A = "Nset n" and B = H in mem_in_image, assumption+)
 apply (simp add:nonempty) apply (simp add:Nset_def)
 apply (simplesubst linear_span_def) apply (subgoal_tac "f ` Nset n \<noteq> {}") apply simp
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> f ` (Nset n)")
 apply (subgoal_tac "(\<lambda>u. if u \<in> Nset (Suc n) then (-\<^sub>R (t u)) else arbitrary) \<in>
 Nset n \<rightarrow> carrier R") apply blast
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<in> Nset (Suc n)") apply simp
 apply (frule ring_is_ag[of "R"]) apply (rule ag_mOp_closed, assumption+)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (rule univar_func_test) apply (rule ballI)
apply (simp add:mem_in_image)
 apply (subgoal_tac "0 \<in> Nset n")
 apply (frule_tac f = f and A = "Nset n" and B = H in mem_in_image, assumption+)
 apply (simp add:nonempty) apply (simp add:Nset_def)
apply (simp add:linear_span_def)
 apply (subgoal_tac "Nset n \<noteq> {}") apply simp
 prefer 2 apply (subgoal_tac "0 \<in> Nset n") apply (simp add:nonempty)
 apply (simp add:Nset_def)
apply (subgoal_tac "\<forall>na. \<forall>fa\<in>Nset na \<rightarrow> f ` (Nset n). \<forall>sa\<in> Nset na \<rightarrow> carrier R.
linear_combination R M n s f +\<^sub>M (linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f) = linear_combination R M na sa fa \<longrightarrow> s (Suc n) = t (Suc n)")
 apply blast
 apply (thin_tac "\<exists>na. \<exists>fa\<in>Nset na \<rightarrow> f ` (Nset n). \<exists>sa\<in> Nset na \<rightarrow> carrier R.
linear_combination R M n s f +\<^sub>M (linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f) = linear_combination R M na sa fa ")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply simp
 apply (thin_tac "linear_combination R M n s f +\<^sub>M (linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f) = linear_combination R M na sa fa")
 apply (thin_tac "linear_combination R M n s f \<in> carrier M")
 apply (thin_tac "linear_combination R M n (\<lambda>x\<in>Nset (Suc n). (-\<^sub>R (t x))) f \<in> carrier M")
 apply (thin_tac "linear_combination R M n s f +\<^sub>M  (s (Suc n) \<star>\<^sub>M (f (Suc n))) \<in> carrier M")
 apply (subgoal_tac "jointfun na sa 0 (\<lambda>l. (s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) \<in> Nset (Suc na) \<rightarrow> carrier R")
 apply (subgoal_tac "jointfun na fa 0 (\<lambda>l. (f (Suc n))) \<in> Nset (Suc na) \<rightarrow> H")
 apply (subgoal_tac "linear_combination R M na sa fa +\<^sub>M ((s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) \<star>\<^sub>M (f (Suc n))) = eSum M (\<lambda>j. (jointfun na sa 0 (\<lambda>l. (s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) j )\<star>\<^sub>M ((jointfun na fa 0 (\<lambda>l. f (Suc n))) j)) (Suc na)")
 apply (simp del:eSum_Suc)
 apply (thin_tac "linear_combination R M na sa fa +\<^sub>M ((s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) \<star>\<^sub>M (f (Suc n))) = 0\<^sub>M")
 apply (frule_tac R = R and M = M and H = H and f = "jointfun na fa 0 (\<lambda>l. (f (Suc n)))" and s = "jointfun na sa 0 (\<lambda>l. (s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))))" and j = "Suc na" in unique_expression3_1, assumption+)
 apply (simp add:Nset_def)
 apply (simp (no_asm) add: jointfun_def)
 apply (subgoal_tac "(Nset (Suc na) - {Suc na}) \<inter> {x. x \<le> na} = {x. x \<le> na}")
 prefer 2  apply (rule equalityI) apply (rule subsetI)
 apply (simp add:Nset_def) apply (rule subsetI) apply (simp add:Nset_def)
 apply simp
 apply (subgoal_tac "((Nset (Suc na) - {Suc na}) \<inter> {x. \<not> x \<le> na}) = {}")
 apply simp prefer 2 apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Nset_def) apply (erule conjE)+
 apply (subgoal_tac "x < Suc na") prefer 2 apply simp
 apply (subgoal_tac "x \<le> na") apply simp apply (thin_tac "\<not> x \<le> na")
 apply simp apply simp apply (fold Nset_def)
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` Nset n" and ?A1.0 = "Nset na" in image_sub) apply simp
 apply (subgoal_tac "f (Suc n) \<notin> f ` (Nset n)") apply blast
 apply (rule contrapos_pp, simp+) apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>Nset n. f (Suc n) = f x \<longrightarrow> False")
 apply blast apply (rule ballI) apply (rule impI) apply (thin_tac "\<exists>x\<in>Nset n. f (Suc n) = f x")
 apply (subgoal_tac "x \<in> Nset (Suc n)")
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:inj_on_def)
 apply (subgoal_tac "Suc n = x") prefer 2 apply blast
 apply (thin_tac "\<forall>x\<in>Nset (Suc n). \<forall>y\<in>Nset (Suc n). f x = f y \<longrightarrow> x = y")
 apply (thin_tac "x \<in> Nset (Suc n)") apply (thin_tac "Suc n \<in> Nset (Suc n)")
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "Suc n = x")
apply (thin_tac "e\<Sigma> M (\<lambda>j. jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) j \<star>\<^sub>M (jointfun na fa 0 (\<lambda>l. f x) j)) na +\<^sub>M (jointfun na sa 0 (\<lambda>l.  s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) (Suc na) \<star>\<^sub>M (jointfun na fa 0 (\<lambda>l. f x) (Suc na))) = 0\<^sub>M")
 apply (thin_tac "s (Suc n) \<star>\<^sub>M (f x) \<in> carrier M")
 apply (thin_tac "(-\<^sub>R (t (Suc n))) \<star>\<^sub>M (f x) \<in> carrier M")
 apply (thin_tac "jointfun na fa 0 (\<lambda>l. f x) \<in> Nset (Suc na) \<rightarrow> H")
 apply (thin_tac "(Nset (Suc na) - {Suc na}) \<inter> {x. \<not> x \<le> na} = {}")
 apply (thin_tac "f (Suc n) = f x") apply (simp add:Nset_def)
apply (simp add:Nset_def) apply (simp add:Nset_def) apply simp
apply (subgoal_tac "\<forall>g m ta. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> ta \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc na) (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) (jointfun na fa 0 (\<lambda>l. f (Suc n))) = linear_combination R M m ta g \<and> ta m = jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) (Suc na) \<longrightarrow>s (Suc n) = t (Suc n)") apply blast
apply (thin_tac "\<exists>g m ta. g \<in> Nset m \<rightarrow> H \<and> inj_on g (Nset m) \<and> ta \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M (Suc na) (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) (jointfun na fa 0 (\<lambda>l. f (Suc n))) = linear_combination R M m ta g \<and> ta m = jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) (Suc na)")
apply (rule allI)+ apply (rule impI) apply (erule conjE)+
apply (subgoal_tac "e\<Sigma> M (\<lambda>j. (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) j \<star>\<^sub>M (jointfun na fa 0 (\<lambda>l. f (Suc n)) j)) (Suc na) = linear_combination R M (Suc na) (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) (jointfun na fa 0 (\<lambda>l. f (Suc n)))") apply simp
apply (thin_tac "e\<Sigma> M (\<lambda>j. jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) j \<star>\<^sub>M (jointfun na fa 0 (\<lambda>l. f (Suc n)) j)) na +\<^sub>M (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) (Suc na)) \<star>\<^sub>M (jointfun na fa 0 (\<lambda>l. f (Suc n)) (Suc na)) = linear_combination R M m ta g")
apply (frule_tac R = R and M = M and H = H and s = ta and n = m and m = g in unique_expression1, assumption+) apply (rule sym) apply assumption
apply (subgoal_tac "m \<in> Nset m")
 apply (subgoal_tac "ta m = 0\<^sub>R") prefer 2 apply simp
 apply (thin_tac "\<forall>j\<in>Nset m. ta j = 0\<^sub>R")
 apply (thin_tac "jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))
          \<in> Nset (Suc na) \<rightarrow> carrier R")
 apply (thin_tac "jointfun na fa 0 (\<lambda>l. f (Suc n)) \<in> Nset (Suc na) \<rightarrow> H")
 apply (thin_tac "linear_combination R M (Suc na) (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) (jointfun na fa 0 (\<lambda>l. f (Suc n))) = linear_combination R M m ta g")
 prefer 2 apply (simp add:Nset_def)
 apply (simp add:jointfun_def) apply (frule ring_is_ag[of "R"])
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") prefer 2 apply (simp add:Nset_def)
 apply (frule_tac f = t and A = "Nset (Suc n)" and B = "carrier R" and x = "Suc n"
 in funcset_mem, assumption+)
 apply (frule_tac G = R and x = "t (Suc n)" in ag_l_zero, assumption+)  apply simp
 apply (frule_tac f = s and A = "Nset (Suc n)" and B = "carrier R" and x = "Suc n"
 in funcset_mem, assumption+)
 apply (frule_tac G = R and x = "t (Suc n)" in ag_mOp_closed, assumption+)
 apply (simp add:ag_pOp_assoc[of "R"]) apply (thin_tac "0\<^sub>R =  s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))")
 apply (simp add:ag_l_inv1[of "R"])
 apply (simp add:ag_r_zero)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) j \<star>\<^sub>M (jointfun na fa 0 (\<lambda>l. f (Suc n)) j)) (Suc na) = 0\<^sub>M")
 apply (thin_tac " linear_combination R M (Suc na) (jointfun na sa 0 (\<lambda>l. s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n))))) (jointfun na fa 0 (\<lambda>l. f (Suc n))) = linear_combination R M m ta g")
apply (simp add:linear_combination_def)
apply (thin_tac "linear_combination R M na sa fa +\<^sub>M (s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) \<star>\<^sub>M (f (Suc n)) = 0\<^sub>M")
 apply simp apply (simp add:jointfun_def)
 apply (subgoal_tac "linear_combination R M na sa fa = e\<Sigma> M (\<lambda>j. (if j \<le> na then sa j else s (Suc n) +\<^sub>R (-\<^sub>R (t (Suc n)))) \<star>\<^sub>M (if j \<le> na then fa j else f (Suc n))) na") apply simp
 apply (simp add:linear_combination_def)
 apply (rule eSum_eq)
 apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (frule_tac f = f and A = "Nset n" and B = H and ?A1.0 = "Nset n" in image_sub) apply simp
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` (Nset n)" and ?A1.0 = "Nset na" in image_sub) apply simp
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` (Nset n)" and a = x in mem_in_image, assumption+) apply (frule_tac A = "fa ` (Nset na)" and B = "f ` (Nset n)" and c = "fa x" in subsetD, assumption+)
apply (frule_tac A = "f ` (Nset n)" and B = H and c = "fa x" in subsetD, assumption+)
 apply (simp add:subsetD)
 apply (rule univar_func_test) apply (rule ballI) apply simp apply (subgoal_tac "x \<le> na") apply simp
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (frule_tac f = f and A = "Nset n" and B = H and ?A1.0 = "Nset n" in image_sub) apply simp
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` (Nset n)" and ?A1.0 = "Nset na" in image_sub) apply simp
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` (Nset n)" and a = x in mem_in_image, assumption+) apply (frule_tac A = "fa ` (Nset na)" and B = "f ` (Nset n)" and c = "fa x" in subsetD, assumption+)
apply (frule_tac A = "f ` (Nset n)" and B = H and c = "fa x" in subsetD, assumption+)
 apply (simp add:subsetD) apply (simp add:Nset_def)
apply (rule ballI) apply (subgoal_tac "l \<le> na") apply simp
 apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI)
 apply (case_tac "x \<le> na")  apply (simp add:jointfun_def)
 apply (subgoal_tac "x \<in> Nset na")
 apply (frule_tac f = f and A = "Nset n" and B = H and ?A1.0 = "Nset n" in image_sub) apply simp
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` (Nset n)" and ?A1.0 = "Nset na" in image_sub) apply simp
 apply (frule_tac f = fa and A = "Nset na" and B = "f ` (Nset n)" and a = x in mem_in_image, assumption+) apply (frule_tac A = "fa ` (Nset na)" and B = "f ` (Nset n)" and c = "fa x" in subsetD, assumption+)
 apply (simp add:subsetD) apply (simp add:Nset_def)
 apply (subgoal_tac "x = Suc na") apply (simp add:jointfun_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:Nset_def) apply (simp add:Nset_def)
apply (rule univar_func_test) apply (rule ballI) apply (case_tac "x \<le> na")
 apply (subgoal_tac "x \<in> Nset na") apply (simp add:jointfun_def)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
 apply (subgoal_tac "x = Suc na")
 apply (simp add:jointfun_def)
 apply (frule ring_is_ag[of "R"])
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (rule ag_pOp_closed [of "R"], assumption+)
 apply (simp add:funcset_mem) apply (rule ag_mOp_closed, assumption+)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
apply (simp add:Nset_def)
done

end
