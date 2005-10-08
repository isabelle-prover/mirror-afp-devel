(**        Algebra7
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            hikoba@math.cst.nihon-u.ac.jp
                            May 3, 2004.

   chapter 5. Modules
      subsection 4-2. free generators (continued)
    section 5. existence of homomorphism
    section 6. Nakayama lemma
    section 7. direct sum and direct products of modules 1, general case
    section 8. exact sequence
    section 9. Tensor products
   **)

theory Algebra7
imports Algebra6
begin


lemma unique_expression7_2:"\<lbrakk>ring R; R module M; free_generator R M H; f\<in>Nset n \<rightarrow> H; inj_on f (Nset n); s \<in> Nset n \<rightarrow> carrier R; t \<in> Nset n\<rightarrow> carrier R; linear_combination R M n s f = linear_combination R M n t f\<rbrakk> \<Longrightarrow> (\<forall>l\<in>Nset n. s l = t l)"
apply (frule_tac R = R and M = M and H = H and f = f and n = n and s = s and t = t in unique_expression7_2Tr, assumption+) apply blast
done

lemma unique_expression7:"\<lbrakk>ring R; R module M; free_generator R M H; f\<in>Nset n \<rightarrow> H; inj_on f (Nset n); s \<in> Nset n \<rightarrow> carrier R; g \<in> Nset m \<rightarrow> H; inj_on g (Nset m); t \<in> Nset m \<rightarrow> carrier R; linear_combination R M n s f = linear_combination R M m t g; \<forall>j\<in>Nset n. s j \<noteq> 0\<^sub>R; \<forall>k\<in>Nset m. t k \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow> n = m \<and> (\<exists>h. h \<in> Nset n \<rightarrow> Nset n \<and> (\<forall>l\<in>Nset n. (cmp f h) l = g l \<and> (cmp s h) l = t l))"
apply (frule_tac R = R and M = M and H = H and f = f and n = n and s = s and g = g and m = m and t = t in unique_expression7_1, assumption+)
apply simp apply (thin_tac "n = m")
apply (frule_tac R = R and M = M and H = H and f = f and n = m and s = s and g = g and m = m and t = t in unique_expression6, assumption+)
apply (subgoal_tac "inj_on (cmp (invfun (Nset m) (g ` (Nset m)) f) g) (Nset m)")
apply (subgoal_tac "(cmp (invfun (Nset m) (g ` (Nset m)) f) g) \<in> Nset m \<rightarrow> Nset m")
apply (subgoal_tac "\<forall>l\<in>Nset m. (cmp f (cmp (invfun (Nset m) (g ` (Nset m)) f) g)) l = g l \<and> (cmp s (cmp (invfun (Nset m) (g ` (Nset m)) f) g)) l = t l")
apply blast
apply (rule ballI)
apply (subgoal_tac "cmp f (cmp (invfun (Nset m) (g ` Nset m) f) g) l = g l")
prefer 2 apply (simp add:cmp_def)
apply (rule invfun_r)
apply (rule univar_func_test) apply (rule ballI) apply (frule_tac f = f and A = "Nset m" and B = H and a = x in mem_in_image, assumption+) apply simp
 apply assumption apply (rotate_tac -4) apply (frule sym)
 apply (thin_tac "f ` Nset m = g ` Nset m") apply simp
 apply (thin_tac "g ` Nset m = f ` Nset m")
 apply (subst surj_to_def) apply simp
 apply (simp add:mem_in_image) apply simp
apply (subgoal_tac "linear_combination R M m s f = linear_combination R M m ( cmp s (cmp (invfun (Nset m) (g ` Nset m) f) g)) (cmp f (cmp (invfun (Nset m) (g ` Nset m) f) g))") apply simp
apply (subgoal_tac "linear_combination R M m (cmp s (cmp (invfun (Nset m) (g ` Nset m) f) g)) g =  linear_combination R M m t g")
apply (frule_tac R = R and M = M and H = H and f = g and n = m and s = "cmp s (cmp (invfun (Nset m) (g ` Nset m) f) g)" and t = t in unique_expression7_2, assumption+)
 apply (rule univar_func_test) apply (rule ballI) apply (subst cmp_def)
 apply (rule funcset_mem, assumption+)
 apply (subst cmp_def)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and x = x in funcset_mem, assumption+)
 apply (simp add:funcset_mem) apply (rotate_tac -9) apply (frule sym)
 apply (thin_tac "f ` Nset m = g ` Nset m") apply simp
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:image_def)
 apply blast apply assumption apply assumption apply simp
 apply (rotate_tac 9) apply (frule sym) apply (thin_tac "linear_combination R M m (cmp s (cmp (invfun (Nset m) (g ` Nset m) f) g)) (cmp f (cmp (invfun (Nset m) (g ` Nset m) f) g)) = linear_combination R M m t g") apply simp
 apply (thin_tac "linear_combination R M m t g = linear_combination R M m  (cmp s (cmp (invfun (Nset m) (g ` Nset m) f) g)) (cmp f (cmp (invfun (Nset m) (g ` Nset m) f) g))")
 apply (thin_tac "linear_combination R M m s f = linear_combination R M m (cmp s (cmp (invfun (Nset m) (g ` Nset m) f) g)) (cmp f (cmp (invfun (Nset m) (g ` Nset m) f) g))")
 apply (simp add:linear_combination_def)
 apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:cmp_def) apply (rule sprod_mem, assumption+)
 apply (rule funcset_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (subst image_def) apply simp apply blast
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:funcset_mem subsetD)
 apply (simp add:free_generator_def generator_def)
apply (rule univar_func_test) apply (rule ballI) apply (subst cmp_def)+
apply (rule sprod_mem, assumption+)
 apply (rule funcset_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (subst image_def) apply simp apply blast
 apply (subgoal_tac "f (invfun (Nset m) (g ` Nset m) f (g x)) \<in> H")
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (rule funcset_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (subst image_def) apply simp apply blast
 apply (rule ballI)
 apply (subst cmp_def)+
 apply (subgoal_tac "f (invfun (Nset m) (g ` Nset m) f (g la)) = g la")
 apply simp
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (subgoal_tac "g la \<in> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" and b = "g la" in invfun_r, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (subst image_def) apply simp apply blast apply assumption
 apply (subst image_def) apply simp apply blast
 apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m")
 apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (subst image_def) apply simp apply blast
apply (thin_tac "linear_combination R M m s f = linear_combination R M m t g")
 apply (thin_tac "\<forall>j\<in>Nset m. s j \<noteq> 0\<^sub>R")
 apply (thin_tac "\<forall>k\<in>Nset m. t k \<noteq> 0\<^sub>R")
 apply (thin_tac " cmp f (cmp (invfun (Nset m) (g ` Nset m) f) g) l = g l")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "(\<lambda>j. s j \<star>\<^sub>M (f j)) \<in> Nset m \<rightarrow> carrier M")
 apply (frule_tac R1 = M and f1 = "\<lambda>j. s j \<star>\<^sub>M (f j)" and n1 = m and h1 = " cmp (invfun (Nset m) (g ` Nset m) f) g" in addition21[THEN sym], assumption+)
 apply (subst linear_combination_def)+ apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) m =  e\<Sigma> M (cmp (\<lambda>j. s j \<star>\<^sub>M (f j))
                 (cmp (invfun (Nset m) (g ` Nset m) f) g)) m")
 apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subst cmp_def)+
 apply (rule sprod_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (subst image_def) apply simp apply blast
 apply (subgoal_tac "f (invfun (Nset m) (g ` Nset m) f (g x)) \<in> H")
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (rule funcset_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem) apply (rotate_tac -7) apply (frule sym)
 apply (thin_tac "f ` Nset m = g ` Nset m") apply simp
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mem_in_image)
apply (rule univar_func_test) apply (rule ballI) apply (subst cmp_def)+
 apply (rule sprod_mem, assumption+)
 apply (rule funcset_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> carrier M")
 apply (rule funcset_mem, assumption+)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -9) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image, assumption+)
 apply (simp add:funcset_mem)
 apply (rotate_tac -9) apply (frule sym) apply simp
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:image_def)
 apply blast apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:funcset_mem subsetD) apply (simp add:free_generator_def generator_def)
 apply (rule ballI)
 apply (subst cmp_def)+ apply simp
apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:funcset_mem subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -3) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = g and A = "Nset m" and B = H and a = x in mem_in_image,
                   assumption+)
 apply (subst cmp_def) apply (simp add:funcset_mem)
apply (rotate_tac -2) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mem_in_image)
 apply (subgoal_tac "g \<in> Nset m \<rightarrow> g ` (Nset m)")
 apply (thin_tac "g \<in> Nset m \<rightarrow> H")
 apply (subgoal_tac "f \<in> Nset m \<rightarrow> g ` (Nset m)")
apply (frule_tac f = f and A = "Nset m" and B = "g ` Nset m" in inv_func, assumption+)
 apply (rotate_tac -3) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (subst surj_to_def) apply simp
apply (rule_tac f = g and A = "Nset m" and B = "g ` (Nset m)" and g = "invfun (Nset m) (g ` Nset m) f"  in cmp_inj, assumption+)
 apply (rule invfun_inj, assumption+)
 apply (rotate_tac -4) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (simp add:surj_to_def)
 apply (rotate_tac -2) apply (frule sym) apply (thin_tac "f ` Nset m = g ` Nset m") apply simp apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:image_def) apply blast
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:image_def)
 apply blast
done

lemma gen_mHom_eq:"\<lbrakk>ring R; R module M; R module N; generator R M H; f \<in> mHom R M N; g \<in> mHom R M N; \<forall>h\<in>H. f h = g h \<rbrakk> \<Longrightarrow> f = g"
apply (simp add:generator_def) apply (erule conjE)+
apply (rule mHom_eq, assumption+) apply (rule ballI)
 apply (subgoal_tac "m \<in> linear_span R M (carrier R) H")
 apply (thin_tac "linear_span R M (carrier R) H = carrier M")
 apply (simp add:linear_span_def) apply (case_tac "H = {}")
 apply simp apply (simp add:mHom_0) apply simp prefer 2 apply simp
apply (subgoal_tac "\<forall>n. \<forall>h\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> carrier R. m = (linear_combination R M n s h) \<longrightarrow> f m = g m")
apply blast
apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H. \<exists>s\<in>Nset n \<rightarrow> carrier R. m = linear_combination R M n s f")
apply (rule allI) apply (rule ballI)+ apply (rule impI)
apply simp
 apply (frule_tac s = s and n = n and g = h in linmap_im_lincomb [of "R" "carrier R" "M" "N" "f" "H"])
 apply (simp add:whole_ideal) apply assumption+  apply simp
 apply (frule_tac s = s and n = n and g = h in linmap_im_lincomb [of "R" "carrier R" "M" "N" "g" "H"])
 apply (simp add:whole_ideal) apply assumption+  apply simp
 apply (rename_tac m n c s)
 apply (thin_tac "f (linear_combination R M n s c) = linear_combination R N n s (cmp f c)")
 apply (thin_tac "g (linear_combination R M n s c) = linear_combination R N n s (cmp g c)")
 apply (subgoal_tac "f ` H \<subseteq> carrier N")
apply (rule linear_comb_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:cmp_def)
 apply (simp add:image_def) apply (subgoal_tac "c x \<in> H")
 apply blast apply (simp add:funcset_mem)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:cmp_def)
 apply (simp add:image_def) apply (subgoal_tac "c x \<in> H")
 apply blast apply (simp add:funcset_mem)
 apply (rule ballI) apply (simp add:cmp_def) apply (subgoal_tac "c j \<in> H")
 apply simp apply (simp add:funcset_mem)
apply (rule subsetI) apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>H. x = g xa \<longrightarrow> x \<in> carrier N")
 apply blast apply (rule ballI) apply (rule impI) apply simp
 apply (subgoal_tac "xa \<in> carrier M") apply (simp add:mHom_mem)
 apply (simp add:subsetD)
done

section "5. existence of homomorphism"

constdefs
 fgs::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, 'a set]  \<Rightarrow> 'a set" (* free generator span, A is a subset of free generator *)
 "fgs R M A == linear_span R M (carrier R) A"
constdefs
 fsp::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, ('b, 'r, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'b, 'a set, 'a set, 'a \<Rightarrow> 'b] \<Rightarrow> bool"
 "fsp R M N f H A g == g \<in> mHom R (mdl M (fgs R M A)) N \<and> (\<forall>z\<in>A. f z = g z) \<and> A \<subseteq> H" (* f \<in> H \<rightarrow> N (not a module hom), free span pair condition *)

constdefs
fsps::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, ('b, 'r, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow>  (('a set) * ('a \<Rightarrow> 'b)) set"
 "fsps R M N f H == {Z. \<exists>A g. Z = (A, g) \<and> fsp R M N f H A g}"
        (* free span pairs *)
constdefs
 od_fm_fun::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, ('b, 'r, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> (('a set) * ('a \<Rightarrow> 'b)) OrderedSet"
 "od_fm_fun R M N f H == \<lparr>carrier = fsps R M N f H, ord_rel = {Y. Y \<in> (fsps R M N f H) \<times> (fsps R M N f H) \<and> (fst (fst Y)) \<subseteq> (fst (snd Y))}, ordering = \<lambda>u\<in>(fsps R M N f H). \<lambda>v\<in>(fsps R M N f H). (fst u \<subseteq> fst v) \<rparr>"  (* ordered set free module with function f *)

lemma fgs_submodule:"\<lbrakk>ring R; R module M; R module N; free_generator R M H;     f \<in> H \<rightarrow> carrier N; (a, b) \<in> fsps R M N f H \<rbrakk> \<Longrightarrow> submodule R M (fgs R M a)"
apply (subst fgs_def)
apply (rule linear_span_subModule, assumption+)
 apply (simp add:whole_ideal)
 apply (subgoal_tac "a \<subseteq> H") apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:fsps_def fsp_def)
done

lemma fst_chain_subset:"\<lbrakk>ring R; R module M; R module N; free_generator R M H;
 f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; (a, b) \<in> C\<rbrakk>  \<Longrightarrow> a \<subseteq> carrier M"
apply (subgoal_tac "a \<subseteq> H") apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD, assumption+) apply (simp add:fsps_def fsp_def)
done

lemma fsps_chain_boundTr1:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; \<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H; \<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}\<rbrakk> \<Longrightarrow>  fa \<in> Nset n \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C} \<longrightarrow> (\<exists>(c, d) \<in> C. fa ` (Nset n) \<subseteq> c)"
apply (induct_tac n)
 apply (rule impI) apply (simp add:Nset_def)
 apply (frule_tac f = fa and A = "{0}" and B = "\<Union>{a. \<exists>b. (a, b) \<in> C}" and ?A1.0 = "{0}" in image_sub) apply simp apply simp
 apply blast
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (frule_tac f = fa and A = "Nset (Suc n)" and B = "\<Union>{a. \<exists>b. (a, b) \<in> C}" and x = "Suc n" in funcset_mem, assumption+) apply simp
 apply (subgoal_tac "\<forall>x. (\<exists>b. (x, b) \<in> C) \<and> fa (Suc n) \<in> x \<longrightarrow> (\<exists>u\<in>C. (\<lambda>(c, d). fa ` Nset (Suc n) \<subseteq> c) u)")
 apply (thin_tac "\<exists>x\<in>C. (\<lambda>(c, d). fa ` Nset n \<subseteq> c) x")
 apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}")
 apply (thin_tac "\<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H")
 apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
apply blast
 apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> fa (Suc n) \<in> x")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "\<forall>b. (x, b) \<in> C  \<longrightarrow> (\<exists>u\<in>C. (\<lambda>(c, d). fa ` Nset (Suc n) \<subseteq> c) u)")
 apply (thin_tac "\<exists>x\<in>C. (\<lambda>(c, d). fa ` Nset n \<subseteq> c) x")
 apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}")
 apply (thin_tac "\<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H")
 apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
 apply blast apply (thin_tac "\<exists>b. (x, b) \<in> C")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "\<forall>x1\<in>C. (\<lambda>(c, d). fa ` Nset n \<subseteq> c) x1 \<longrightarrow> (\<exists>u\<in>C. (\<lambda>(c, d). fa ` Nset (Suc n) \<subseteq> c) u)")
 apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}")
 apply (thin_tac "\<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H")
 apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
 apply blast apply (thin_tac "\<exists>x\<in>C. (\<lambda>(c, d). fa ` Nset n \<subseteq> c) x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "fa ` Nset n \<subseteq> (fst x1)")
 apply (subgoal_tac "(fst x1, snd x1) \<in> C") apply (thin_tac "(\<lambda>(c, d). fa ` Nset n \<subseteq> c) x1") apply (thin_tac "x1 \<in> C")
 prefer 2 apply simp prefer 2 apply (subgoal_tac "x1 = (fst x1, snd x1)")
 apply blast apply simp
 apply (subgoal_tac "fst (x, b) \<subseteq> fst (fst x1, snd x1) \<or> fst (fst x1, snd x1) \<subseteq> fst (x, b)") prefer 2
 apply blast
 apply (subgoal_tac "x \<subseteq> fst x1 \<or> fst x1 \<subseteq> x") prefer 2 apply simp
 apply (thin_tac "fst (x, b) \<subseteq> fst (fst x1, snd x1) \<or> fst (fst x1, snd x1) \<subseteq> fst (x, b)")
apply (case_tac "x \<subseteq> fst x1")
 apply (subgoal_tac "fa ` (Nset (Suc n)) \<subseteq> fst x1") apply blast
 apply (subst Nset_Suc)
 apply (rule subsetI) apply (simp add:image_def)
 apply (case_tac "xa = fa (Suc n)") apply (simp add:subsetD) apply simp
 apply (subgoal_tac "\<forall>x\<in>Nset n. xa = fa x \<longrightarrow> xa \<in> fst x1")
 apply blast apply (thin_tac "\<exists>x\<in>Nset n. xa = fa x") apply (rule ballI)
 apply (rule impI) apply (subgoal_tac "xa \<in> {y. \<exists>x\<in>Nset n. y = fa x}")
 apply (rule subsetD, assumption+) apply simp apply blast
apply simp
 apply (subgoal_tac "fa ` (Nset (Suc n)) \<subseteq> x") apply blast
 apply (subst Nset_Suc)
 apply (rule subsetI) apply (simp add:image_def)
 apply (case_tac "xa = fa (Suc n)") apply (simp add:subsetD) apply simp
 apply (subgoal_tac "\<forall>y\<in>Nset n. xa = fa y \<longrightarrow> xa \<in> x")
 apply blast apply (thin_tac "\<exists>x\<in>Nset n. xa = fa x") apply (rule ballI)
 apply (rule impI) apply (subgoal_tac "xa \<in> {y. \<exists>x\<in>Nset n. y = fa x}")
 apply (rule subsetD, assumption+) apply simp apply blast
 apply simp apply blast
apply (simp add:Nset_def)
done

lemma fsps_chain_boundTr1_1:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; \<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H; \<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}; fa \<in> Nset n \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}\<rbrakk> \<Longrightarrow> \<exists>(c, d) \<in> C. fa ` (Nset n) \<subseteq> c"
apply (simp add:fsps_chain_boundTr1)
done

lemma fsps_chain_boundTr1_2:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; \<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H; \<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}; fa \<in> Nset n \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}\<rbrakk> \<Longrightarrow> \<exists>P \<in> C. fa ` (Nset n) \<subseteq> fst P"
apply (frule_tac R = R and M = M and N = N and f = f and C = C and fa = fa and n = n in fsps_chain_boundTr1_1, assumption+)
apply (simp add:split)
apply (subgoal_tac "\<forall>x\<in>C. (\<lambda>(c, d). fa ` Nset n \<subseteq> c) x \<longrightarrow> (\<exists>P\<in>C. fa ` Nset n \<subseteq> fst P
)") apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
 apply (thin_tac "\<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H")
 apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}")
 apply blast
 apply (thin_tac "\<exists>x\<in>C. (\<lambda>(c, d). fa ` Nset n \<subseteq> c) x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "fa ` Nset n \<subseteq> (fst x)")
 apply blast
 apply (subgoal_tac "(\<lambda>(c, d). fa ` Nset n \<subseteq> c) (fst x, snd x)")
 apply blast
 apply (simp add:split)
done

lemma eSum_in_SubmoduleTr:"\<lbrakk>ring R; R module M; R module N; H \<subseteq> carrier M;
A \<subseteq> H\<rbrakk> \<Longrightarrow>  f \<in> Nset n \<rightarrow> A \<and> s \<in> Nset n \<rightarrow> carrier R  \<longrightarrow>
linear_combination R (mdl M (fgs R M A)) n s f = linear_combination R M n s f"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+
 apply (simp add:linear_combination_def) apply (simp add:mdl_def)
apply (rule impI) apply (erule conjE)+
 apply (frule_tac f = f and n = n and A = A in func_pre)
 apply (frule_tac f = s and n = n and A = "carrier R" in func_pre)
 apply simp
apply (simp add:linear_combination_def) apply (simp add:mdl_def)
done

lemma eSum_in_Submodule:"\<lbrakk>ring R; R module M; R module N; H \<subseteq> carrier M;
A \<subseteq> H; f \<in> Nset n \<rightarrow> A; s \<in> Nset n \<rightarrow> carrier R\<rbrakk> \<Longrightarrow> linear_combination R (mdl M (fgs R M A)) n s f = linear_combination R M n s f"
apply (simp add:eSum_in_SubmoduleTr)
done

lemma fgs_mono:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; H1 \<subseteq> H2; H2 \<subseteq> H\<rbrakk> \<Longrightarrow> fgs R M H1 \<subseteq> fgs R M H2"
apply (case_tac "H1 = {}")
 apply (simp add:fgs_def linear_span_def)
 apply (case_tac "H2 = {}") apply simp apply simp
 apply (frule nonempty_ex [of "H2"])
 apply (subgoal_tac "\<forall>x. x \<in> H2 \<longrightarrow> (\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H2. \<exists>s\<in>Nset n \<rightarrow> carrier R. 0\<^sub>M = linear_combination R M n s f)") apply blast
 apply (thin_tac "\<exists>x. x \<in> H2") apply (rule allI) apply (rule impI)
 apply (subgoal_tac "(\<lambda>j. x) \<in> Nset 0 \<rightarrow> H2")
 apply (subgoal_tac "(\<lambda>j. 0\<^sub>R) \<in> Nset 0 \<rightarrow> carrier R")
 apply (subgoal_tac "0\<^sub>M = linear_combination R M 0 (\<lambda>j. 0\<^sub>R) (\<lambda>j. x)")
 apply blast
 apply (simp add:linear_combination_def)
 apply (subgoal_tac "H \<subseteq> carrier M") prefer 2 apply (simp add:free_generator_def generator_def)
 apply (frule_tac A = H2 and B = H and C = "carrier M" in subset_trans, assumption+)
 apply (frule_tac A = H2 and B = "carrier M" and c = x in subsetD, assumption+)
 apply (simp add:sprod_0_m)
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule ring_is_ag [of "R"]) apply (simp add:ag_inc_zero)
 apply (rule univar_func_test) apply (rule ballI) apply assumption
apply (subgoal_tac "H2 \<noteq> {}") prefer 2 apply (rule contrapos_pp, simp+)
 apply (rule subsetI)
 apply (simp add:fgs_def) apply (simp add:linear_span_def)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H1. \<forall>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H1. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (subgoal_tac "f \<in> Nset n \<rightarrow> H2") apply blast
 apply (thin_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H2. \<forall>s\<in>Nset n \<rightarrow> carrier R.
  x \<noteq> linear_combination R M n s f")
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = f and A = "Nset n" and B = H1 and x = xa in funcset_mem, assumption+)
 apply (simp add:subsetD)
done

lemma fsps_chain_boundTr2_1:" \<lbrakk>ring R; R module M; R module N; free_generator R M H;f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; (a, b) \<in> C; a \<noteq> {}; (aa, ba) \<in> C; aa \<noteq> {}; x \<in> fgs R M a; x \<in> fgs R M aa; a \<subseteq> aa\<rbrakk> \<Longrightarrow> b x = ba x"
 apply (simp add:fgs_def linear_span_def)
 apply (subgoal_tac "\<forall>n. \<forall>fa\<in>Nset n \<rightarrow> a. \<forall>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s fa \<longrightarrow> b x = ba x") apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> a. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (subgoal_tac "\<forall>m. \<forall>g\<in>Nset m \<rightarrow> aa. \<forall>t\<in>Nset m \<rightarrow> carrier R. x = linear_combination R M m t g \<longrightarrow> b x = ba x") apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> aa. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f") apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (subgoal_tac "linear_combination R M n s fa = linear_combination R M m t g") prefer 2 apply simp
 apply (thin_tac "x = linear_combination R M m t g")
 apply (subgoal_tac "linear_combination R M n s fa \<in> fgs R M a")
 prefer 2 apply (simp add:fgs_def linear_span_def) apply (rotate_tac -2)
 apply (frule sym)  apply (thin_tac "linear_combination R M n s fa = linear_combination R M m t g") apply simp
apply (thin_tac "f \<in> H \<rightarrow> carrier N")
 apply (thin_tac "C \<subseteq> fsps R M N f H")
 apply (thin_tac "linear_combination R M m t g = linear_combination R M n s fa")
 apply blast
 apply (subgoal_tac "linear_combination R M n s fa \<in> fgs R M aa")
 prefer 2
 apply (thin_tac "linear_combination R M n s fa \<in> fgs R M a")
 apply (simp add:fgs_def linear_span_def)
 apply (thin_tac "f \<in> H \<rightarrow> carrier N")
 apply (thin_tac "C \<subseteq> fsps R M N f H")
 apply (thin_tac "linear_combination R M n s fa = linear_combination R M m t g")
 apply (thin_tac "fa \<in> Nset n \<rightarrow> a") apply (thin_tac "s \<in> Nset n \<rightarrow> carrier R")
 apply blast
 apply simp
 apply (subgoal_tac "b \<in> mHom R (mdl M (fgs R M a)) N")
 apply (subgoal_tac "R module (mdl M (fgs R M a))") prefer 2
  apply (rule mdl_is_module, assumption+)
  apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD,
                                 assumption+)
  apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (frule whole_ideal [of "R"])
 apply (frule_tac R = R and A = "carrier R" and M = "mdl M (fgs R M a)" and N = N and f = b and H = a and s = s and n = n and g = fa in linmap_im_lincomb, assumption+)
 apply (subst mdl_def) apply simp (** make it a lemma **)
 apply (subst fgs_def)
 apply (rule elem_linear_span1, assumption+)
 apply (simp add:fst_chain_subset) apply assumption+
  apply (thin_tac "x = linear_combination R M m t g")
apply (frule_tac R = R and M = M and N = N and H = H and A = a and f = fa and n = n and s = s in eSum_in_Submodule, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD, assumption+)
 apply (simp add:fsps_def fsp_def) apply assumption+
 apply simp apply (thin_tac "linear_combination R (mdl M (fgs R M a)) n s fa =
          linear_combination R M m t g")  apply (rotate_tac -8)
 apply (frule sym) apply (thin_tac "linear_combination R M n s fa = linear_combination R M m t g") apply simp
 apply (subgoal_tac "ba \<in> mHom R (mdl M (fgs R M aa)) N")
 apply (subgoal_tac "R module (mdl M (fgs R M aa))") prefer 2
  apply (rule mdl_is_module, assumption+)
apply (rule_tac R = R and M = M and N = N and H = H and f = f and a = aa and b = ba in fgs_submodule, assumption+) apply (rule subsetD, assumption+)
 apply (frule whole_ideal[of "R"])
 apply (subgoal_tac "fa \<in> Nset n \<rightarrow> aa") prefer 2 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:funcset_mem subsetD)
 apply (frule_tac R = R and A = "carrier R" and M = "mdl M (fgs R M aa)" and N = N and f = ba and H = aa and s = s and n = n and g = fa in linmap_im_lincomb, assumption+)
 apply (subst mdl_def) apply simp apply (subst fgs_def)
 apply (rule elem_linear_span1, assumption+)
 apply (rule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = aa and b = ba in fst_chain_subset, assumption+)
  apply (frule_tac A = C and B = "fsps R M N f H" and c = "(aa, ba)" in subsetD, assumption+)
 apply (frule_tac R = R and M = M and N = N and H = H and A = aa and f = fa and n = n and s = s in eSum_in_Submodule, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(aa, ba)" in subsetD, assumption+)
 apply (simp add:fsps_def fsp_def) apply assumption+ apply simp
apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD, assumption+)
 apply (thin_tac "linear_combination R M n s fa \<in> fgs R M aa")
 apply (thin_tac "linear_combination R (mdl M (fgs R M aa)) n s fa =
          linear_combination R M n s fa")
 apply (thin_tac "b (linear_combination R M n s fa) =
          linear_combination R N n s (cmp b fa)")
 apply (thin_tac "linear_combination R M m t g = linear_combination R M n s fa")
 apply (thin_tac "ba (linear_combination R M n s fa) =
          linear_combination R N n s (cmp ba fa)")
 apply (subst linear_combination_def)+
 apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:cmp_def)
 apply (rule_tac R = R and M = "mdl M (fgs R M a)" and N = N and f = b and m = "fa x" in mHom_mem, assumption+)
 apply (frule_tac f = fa and A = "Nset n" and B = a and x = x in funcset_mem, assumption+)
 apply (subst mdl_def) apply simp apply (simp add:fgs_def)
 apply (frule_tac R = R and M = M and H = a in elem_linear_span1, assumption+)
 apply (rule_tac f = f and b = b in fst_chain_subset, assumption+)
 apply (rule subsetD, assumption+)
apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:cmp_def)
 apply (rule_tac R = R and M = "mdl M (fgs R M aa)" and N = N and f = ba and m = "fa x" in mHom_mem, assumption+)
 apply (frule_tac f = fa and A = "Nset n" and B = aa and x = x in funcset_mem, assumption+)
 apply (subst mdl_def) apply simp apply (simp add:fgs_def)
 apply (frule_tac R = R and M = M and H = aa in elem_linear_span1, assumption+)
 apply (rule_tac f = f and b = ba in fst_chain_subset, assumption+)
 apply (rule subsetD, assumption+)
apply (rule ballI) apply (subst cmp_def)+
 apply (frule_tac f = fa and A = "Nset n" and B = a and x = l in funcset_mem,
  assumption+)
 apply (thin_tac "g \<in> Nset m \<rightarrow> aa") apply (thin_tac "t \<in> Nset m \<rightarrow> carrier R")
 apply (thin_tac "C \<subseteq> fsps R M N f H")
 apply (simp add:fsps_def fsp_def)
 apply (erule conjE)+
 apply (subgoal_tac "f (fa l) = b (fa l)") prefer 2 apply simp
 apply (thin_tac "\<forall>z\<in>a. f z = b z") apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "f (fa l) = b (fa l)") apply simp
 apply (thin_tac "b (fa l) = f (fa l)")
 apply (frule_tac f = fa and A = "Nset n" and B = aa and x = l in funcset_mem,
  assumption+)
 apply (subgoal_tac "f (fa l) = ba (fa l)") prefer 2 apply simp
 apply (thin_tac "\<forall>z\<in>aa. f z = ba z") apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "f (fa l) = ba (fa l)") apply simp
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(aa, ba)" in subsetD,
              assumption+)
 apply (simp add:fsps_def fsp_def)
apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD,
              assumption+)
apply (simp add:fsps_def fsp_def)
done

lemma fsps_chain_boundTr2_2:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; C \<noteq> {}; (a, b) \<in> C; x \<in> fgs R M a; (a1, b1) \<in> C; x \<in> fgs R M a1\<rbrakk> \<Longrightarrow> b x = b1 x"
 apply (case_tac "a = {}") apply simp
 apply (case_tac "a1 = {}") apply simp
 apply (simp add:fgs_def linear_span_def)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "({}, b)" in subsetD, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "({}, b1)" in subsetD, assumption+)
apply (subgoal_tac "b \<in> mHom R (mdl M (fgs R M {})) N")
 apply (subgoal_tac "b1 \<in> mHom R (mdl M (fgs R M {})) N")
 apply (subgoal_tac "R module (mdl M (fgs R M {}))")
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = b in mHom_0, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = b1 in mHom_0, assumption+)
 apply (simp add:mdl_def)
 apply (rule mdl_is_module, assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (simp add:fsps_def fsp_def) apply (simp add:fsps_def fsp_def)
apply (simp add:fgs_def linear_span_def)
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> a1. \<exists>s\<in>Nset n \<rightarrow> carrier R. 0\<^sub>M = linear_combination R M n s f")
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "({}, b)" in subsetD, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a1, b1)" in subsetD, assumption+)
apply (subgoal_tac "b \<in> mHom R (mdl M (fgs R M {})) N")
 apply (subgoal_tac "b1 \<in> mHom R (mdl M (fgs R M a1)) N")
 apply (subgoal_tac "R module (mdl M (fgs R M {}))")
 apply (subgoal_tac "R module (mdl M (fgs R M a1))")
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = b in mHom_0, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M a1)" and N = N and f = b1 in mHom_0, assumption+)
 apply (simp add:mdl_def)
 apply (rule mdl_is_module, assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (rule mdl_is_module, assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (simp add:fsps_def fsp_def)
 apply (simp add:fsps_def fsp_def)
apply (case_tac "a1 = {}")
 apply (simp add:fgs_def linear_span_def)
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> a. \<exists>s\<in>Nset n \<rightarrow> carrier R. 0\<^sub>M = linear_combination R M n s f")
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "({}, b1)" in subsetD, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD, assumption+)
apply (subgoal_tac "b \<in> mHom R (mdl M (fgs R M a)) N")
 apply (subgoal_tac "b1 \<in> mHom R (mdl M (fgs R M {})) N")
 apply (subgoal_tac "R module (mdl M (fgs R M a))")
 apply (subgoal_tac "R module (mdl M (fgs R M {}))")
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = b1 in mHom_0, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M a)" and N = N and f = b in mHom_0, assumption+)
 apply (simp add:mdl_def)
 apply (rule mdl_is_module, assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (rule mdl_is_module, assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (simp add:fsps_def fsp_def) apply (simp add:fsps_def fsp_def)
apply (subgoal_tac "fst (a, b) \<subseteq> fst (a1, b1) \<or> fst (a1, b1) \<subseteq> fst (a, b)")
 prefer 2 apply blast
 apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
 apply simp
apply (case_tac "a \<subseteq> a1")
 apply (rule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a and b = b and aa = a1 and ba = b1 and x = x in fsps_chain_boundTr2_1, assumption+) apply simp
  apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a1 and b = b1 and aa = a and ba = b and x = x in fsps_chain_boundTr2_1, assumption+) apply (rule sym) apply assumption
done

lemma fsps_chain_boundTr2:"\<And>x. \<lbrakk>ring R; R module M; R module N; free_generator R M H;  f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H;  \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; x \<in> (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})); C \<noteq> {}\<rbrakk>  \<Longrightarrow> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) \<in> (carrier N) \<and> (\<exists>a1 b1. (a1, b1) \<in> C \<and> x \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) = b1 x)"
apply (subgoal_tac "\<exists>!y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> (fgs R M a) \<and> y = b x)")
apply (subgoal_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) = b x)")
prefer 2 apply (rule theI') apply simp
apply simp
apply (rule ex_ex1I)
 apply (subgoal_tac "x \<in> linear_span R M (carrier R) (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 prefer 2 apply (simp add:fgs_def)
 apply (subgoal_tac "x \<in> (if \<forall>x. (\<exists>b. (x, b) \<in> C) \<longrightarrow> x = {} then {0\<^sub>M} else {x. \<exists>n. \<exists>f\<in>Nset n \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f})")
 prefer 2 apply (simp add:linear_span_def)
 apply (thin_tac "x \<in> linear_span R M (carrier R) (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 apply (case_tac "\<forall>x. (\<exists>b. (x, b) \<in> C) \<longrightarrow> x = {}") apply simp
 apply (frule nonempty_ex[of "C"])
 apply (subgoal_tac "\<forall>x. x \<in> C \<longrightarrow> (\<exists>y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and>
                      0\<^sub>M \<in> fgs R M a \<and> y = b (0\<^sub>M)))")
 apply blast
 apply (thin_tac "\<exists>x. x \<in> C") apply (rule allI) apply (rule impI)
 apply (subgoal_tac "(fst xa, snd xa) \<in> C") prefer 2 apply (simp add:split)
 apply (thin_tac "xa \<in> C")
 apply (subgoal_tac "(fst xa, snd xa) \<in> fsps R M N f H")
 prefer 2 apply blast
 apply (subgoal_tac "fst xa = {}") prefer 2 apply blast
  apply (thin_tac "\<forall>x. (\<exists>b. (x, b) \<in> C) \<longrightarrow> x = {}")
  apply (subgoal_tac "0\<^sub>N \<in> carrier N \<and> (fst xa, snd xa) \<in> C \<and> 0\<^sub>M \<in> fgs R M (fst xa) \<and> 0\<^sub>N = (snd xa) (0\<^sub>M)")  apply blast
 apply (frule module_is_ag[of "R" "N"], assumption+)
 apply (simp add:ag_inc_zero[of "N"])
 apply (rule conjI) apply (simp add:fgs_def linear_span_def)
 apply (thin_tac "C \<subseteq> fsps R M N f H")
 apply (simp add:fsps_def fsp_def)
 apply (subgoal_tac "0\<^sub>M \<in> carrier (mdl M (fgs R M {}))")
 apply (subgoal_tac "R module (mdl M (fgs R M {}))")
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = "snd xa" in mHom_0, assumption+)
 apply (simp add:mdl_def)
 apply (subst fgs_def)
 apply (rule mdl_is_module, assumption+)
 apply (rule linear_span_subModule, assumption+)
 apply (simp add:whole_ideal) apply simp
 apply (simp add:mdl_def fgs_def linear_span_def)
apply simp
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}. \<forall>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f \<longrightarrow> (\<exists>y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and fa = fa and n = n in fsps_chain_boundTr1_2, assumption+)
 apply (rule allI)+ apply (rule impI) apply (rule subsetD, assumption+)
 apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}")
 apply (subgoal_tac "\<forall>P\<in>C. fa ` (Nset n) \<subseteq> fst P \<longrightarrow> (\<exists>y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))")
 apply blast apply (thin_tac "\<exists>P\<in>C. fa ` Nset n \<subseteq> fst P")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "fa \<in> Nset n \<rightarrow> fst P")
 prefer 2  apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "fa xa \<in> fa ` (Nset n)") apply (rule subsetD, assumption+)
 apply (simp add:image_def) apply blast
 apply (subgoal_tac "linear_combination R M n s fa \<in> fgs R M (fst P)")
 prefer 2
 apply (subgoal_tac "fst P \<noteq> {}")
 apply (simp add:fgs_def linear_span_def)
 apply blast
 apply (subgoal_tac "fa 0 \<in> fa ` (Nset n)") apply (frule_tac A = "fa ` (Nset n)" and B = "fst P" and c = "fa 0" in subsetD, assumption+)
 apply (rule nonempty, assumption+) apply (simp add:image_def)
 apply (subgoal_tac "0 \<in> Nset n") apply blast apply (simp add:Nset_def)
 apply (subgoal_tac "(snd P) (linear_combination R M n s fa) \<in> carrier N")
 apply (subgoal_tac "(fst P, snd P) \<in> C")
 apply blast apply simp
 apply (frule_tac A = C and B = "fsps R M N f H" and c = P in subsetD, assumption+)
 apply (subgoal_tac "fsp R M N f H (fst P) (snd P)") prefer 2
  apply (subgoal_tac "(fst P, snd P) \<in> fsps R M N f H")
 apply (unfold fsps_def) prefer 2 apply simp
  apply (thin_tac "P \<in> {(A, g) |A g. fsp R M N f H A g}")
  apply blast
 apply (fold fsps_def)
 apply (subgoal_tac "(snd P) \<in> mHom R (mdl M (fgs R M (fst P))) N")
 apply (subgoal_tac "R module (mdl M (fgs R M (fst P)))")
 apply (rule_tac R = R and M = "mdl M (fgs R M (fst P))" and N = N and f = "snd P" and m = "linear_combination R M n s fa" in mHom_mem, assumption+)
 apply (simp add:mdl_def)
 apply (rule mdl_is_module, assumption+)
 apply (subgoal_tac "(fst P, snd P) \<in> fsps R M N f H")
 apply (rule_tac f = f in fgs_submodule, assumption+) apply simp
 apply (simp add:fsp_def) apply (erule conjE)+
 apply (thin_tac "y \<in> carrier N") apply (thin_tac "ya \<in> carrier N")
apply (thin_tac "x \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 apply (subgoal_tac "\<forall>a b a1 b1. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x \<and>
                      (a1, b1) \<in> C \<and> x \<in> fgs R M a1 \<and> ya = b1 x \<longrightarrow> y = ya")
 apply blast
 apply (thin_tac "\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x")
 apply (thin_tac "\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> ya = b x")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+ apply simp
apply (rule_tac R = R and M = M and N = N and H = H and f = f and C = C and
x = x and a = a and b = b and ?a1.0 = a1 and ?b1.0 = b1 in fsps_chain_boundTr2_2, assumption+)
done

lemma fsps_chain_bound1:"\<lbrakk>ring R; R module M; R module N; free_generator R M H;  f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H;  \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; C \<noteq> {}\<rbrakk>  \<Longrightarrow> (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))) \<in> mHom R (mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) N"
apply (subgoal_tac "R module (mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})))")
prefer 2 apply (rule mdl_is_module, assumption+)
 apply (subst fgs_def)
 apply (rule linear_span_subModule, assumption+) apply (simp add:whole_ideal)
 apply (rule subsetI) apply simp
 apply (subgoal_tac "\<forall>xa. (\<exists>b. (xa, b) \<in> C) \<and> x \<in> xa \<longrightarrow> x \<in> carrier M")
 apply blast apply (thin_tac "\<exists>xa. (\<exists>b. (xa, b) \<in> C) \<and> x \<in> xa")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "\<forall>b. (xa, b) \<in> C \<longrightarrow> x \<in> carrier M") apply blast
 apply (thin_tac "\<exists>b. (xa, b) \<in> C") apply (rule allI) apply (rule impI)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(xa, b)" in subsetD,
                        assumption+)
 apply (subgoal_tac "xa \<subseteq> H") apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule subsetD, assumption+) apply (rule subsetD, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:fsps_def fsp_def)
apply (rule mHom_test, assumption+)
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (thin_tac "R module mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))")
 apply (simp add:mdl_def)
 apply (simp add:fsps_chain_boundTr2)
apply (rule conjI)
 apply (simp add:restrict_def extensional_def mdl_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule module_is_ag [of "R" "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))"], assumption+)
 apply (frule_tac G = "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))" and x = m and y = n in ag_pOp_closed, assumption+)
 apply (subgoal_tac "m +\<^sub>(mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) n = m +\<^sub>M n")
 prefer 2 apply (simp add:mdl_def)
 apply simp apply (thin_tac "m +\<^sub>(mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) n =  m +\<^sub>M n")
 apply (thin_tac "R module mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))")
 apply (thin_tac "agroup (mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})))")
 apply (simp add:mdl_def)
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = m in fsps_chain_boundTr2, assumption+) apply (erule conjE)
 apply (subgoal_tac "\<forall>a1 b1. (a1, b1) \<in> C \<and> m \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) =  b1 m  \<longrightarrow> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b ( m +\<^sub>M n))) = (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) +\<^sub>N (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> n \<in> fgs R M a \<and> y = b n))") apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> m \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m )) = b1 m ")
apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) \<in> carrier N")
apply (rule allI)+ apply (rule impI) apply (erule conjE)+
apply simp
apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) = b1 m")
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = n in fsps_chain_boundTr2, assumption+) apply (erule conjE)
apply (subgoal_tac "\<forall>a2 b2. (a2, b2) \<in> C \<and> n \<in> fgs R M a2 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> n \<in> fgs R M a \<and> y = b n )) =  b2 n \<longrightarrow> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and>  m +\<^sub>M n \<in> fgs R M a \<and> y = b ( m +\<^sub>M n))) = b1 m +\<^sub>N (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> n \<in> fgs R M a \<and> y = b n))") apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> n \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> n \<in> fgs R M a \<and> y = b n)) = b1  n")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+ apply simp
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> n \<in> fgs R M a \<and> y = b n)) = b2 n")
 apply (thin_tac "b2 n \<in> carrier N")
 apply (subgoal_tac "fst (a1, b1) \<subseteq> fst (a2, b2) \<or> fst (a2, b2) \<subseteq> fst (a1, b1)") prefer 2 apply blast apply simp
 apply (case_tac "a1 \<subseteq> a2")
 apply (frule_tac R = R and M = M and N = N and H = H and ?H1.0 = a1 and ?H2.0 = a2 in fgs_mono, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a2, b2)" in subsetD, assumption+) apply (simp add:fsps_def fsp_def)
 apply (frule_tac A = "fgs R M a1" and B = "fgs R M a2" and c = m in subsetD, assumption+)
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and a = a2 and b = b2 in fgs_submodule, assumption+) apply (rule subsetD, assumption+)
 apply (frule_tac R = R and M = M and H = "fgs R M a2" and h = m and k = n in submodule_pOp_closed, assumption+)
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = "m +\<^sub>M n" in fsps_chain_boundTr2, assumption+) apply (erule conjE)
apply (subgoal_tac "\<forall>a3 b3. (a3, b3) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a3 \<and> (THE y.
y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b ( m +\<^sub>M n))) = b3 ( m +\<^sub>M n) \<longrightarrow> ((THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b (m +\<^sub>M n))) = b1 m +\<^sub>N (b2 n))") apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b (m +\<^sub>M n))) =  b1 (m +\<^sub>M n)")
 apply (rule allI)+ apply (rule impI)  apply (erule conjE)+  apply simp
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b (m +\<^sub>M n))) = b3 (m +\<^sub>M n)")
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a3 and b = b3 and x = "m +\<^sub>M n" and ?a1.0 = a2 and ?b1.0 = b2 in fsps_chain_boundTr2_2, assumption+) apply simp
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a1 and b = b1 and x = m and ?a1.0 = a2 and ?b1.0 = b2 in fsps_chain_boundTr2_2, assumption+) apply simp
 apply (thin_tac "m +\<^sub>M n \<in> fgs R M a3") apply (thin_tac "b3 ( m +\<^sub>M n) = b2 ( m +\<^sub>M n)") apply (thin_tac "b2 (m +\<^sub>M n) \<in> carrier N")
 apply (thin_tac "(a3, b3) \<in> C") apply (thin_tac "b1 m = b2 m")
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a2, b2)" in subsetD,
                     assumption+)
 apply (subgoal_tac "b2 \<in> mHom R (mdl M (fgs R M a2)) N")
 apply (frule_tac R = R and M = M and H = "fgs R M a2" in mdl_is_module, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M a2)" and N = N and f = b2 and m = m and n = n in mHom_add, assumption+)
 apply (simp add:mdl_def) apply (simp add:mdl_def)
 apply (simp add:mdl_def) apply (simp add:fsps_def fsp_def)
apply simp apply (rename_tac m n a2 b2 a1 b1)
 apply (frule_tac R = R and M = M and N = N and H = H and ?H1.0 = a1 and ?H2.0 = a2 in fgs_mono, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a2, b2)" in subsetD, assumption+) apply (simp add:fsps_def fsp_def)
 apply (frule_tac A = "fgs R M a1" and B = "fgs R M a2" and c = n in subsetD, assumption+)
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and a = a2 and b = b2 in fgs_submodule, assumption+) apply (rule subsetD, assumption+)
 apply (frule_tac R = R and M = M and H = "fgs R M a2" and h = m and k = n in submodule_pOp_closed, assumption+)
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = "m +\<^sub>M n" in fsps_chain_boundTr2, assumption+) apply (erule conjE)
apply (subgoal_tac "\<forall>a3 b3. (a3, b3) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a3 \<and> (THE y.
y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b ( m +\<^sub>M n))) = b3 ( m +\<^sub>M n) \<longrightarrow> ((THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b (m +\<^sub>M n))) = b2 m +\<^sub>N (b1 n))") apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b (m +\<^sub>M n))) =  b1 (m +\<^sub>M n)")
 apply (rule allI)+ apply (rule impI)  apply (erule conjE)+  apply simp
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> (m +\<^sub>M n) \<in> fgs R M a \<and> y = b (m +\<^sub>M n))) = b3 (m +\<^sub>M n)")
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a3 and b = b3 and x = "m +\<^sub>M n" and ?a1.0 = a2 and ?b1.0 = b2 in fsps_chain_boundTr2_2, assumption+) apply simp
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a1 and b = b1 and x = n and ?a1.0 = a2 and ?b1.0 = b2 in fsps_chain_boundTr2_2, assumption+) apply simp
 apply (thin_tac "m +\<^sub>M n \<in> fgs R M a3") apply (thin_tac "b3 ( m +\<^sub>M n) = b2 ( m +\<^sub>M n)") apply (thin_tac "b2 (m +\<^sub>M n) \<in> carrier N")
 apply (thin_tac "(a3, b3) \<in> C") apply (thin_tac "b1 n = b2 n")
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a2, b2)" in subsetD,
                     assumption+)
 apply (subgoal_tac "b2 \<in> mHom R (mdl M (fgs R M a2)) N")
 apply (frule_tac R = R and M = M and H = "fgs R M a2" in mdl_is_module, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M a2)" and N = N and f = b2 and m = m and n = n in mHom_add, assumption+)
 apply (simp add:mdl_def) apply (simp add:mdl_def)
 apply (simp add:mdl_def) apply (simp add:fsps_def fsp_def)
apply (rule ballI)+ apply simp
 apply (subgoal_tac "m \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})") apply simp
 prefer 2 apply (simp add:mdl_def)
 apply (subgoal_tac "a \<star>\<^sub>(mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) m \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})") apply simp
 prefer 2
 apply (frule_tac R = R and M = "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))" and a = a and m = m in sprod_mem, assumption+) apply (simp add:mdl_def)
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = m in fsps_chain_boundTr2, assumption+) apply (erule conjE)
apply (subgoal_tac "\<forall>a1 b1. (a1, b1) \<in> C \<and> m \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) = b1 m \<longrightarrow> ((THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and> a \<star>\<^sub>(mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) m \<in> fgs R M aa \<and> y =  b (a \<star>\<^sub>(mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) m))) =a \<star>\<^sub>N (THE y. y \<in> carrier N \<and>  (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)))")
 apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> m \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) = b1 m")
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) \<in> carrier N")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+ apply simp
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) = b1 m")
 apply (subst mdl_def)+ apply simp
 apply (subgoal_tac "R module (mdl M (fgs R M a1))")
 apply (frule_tac R = R and M = "mdl M (fgs R M a1)" and a = a and m = m in sprod_mem, assumption+)
 apply (simp add:mdl_def)
 apply (subgoal_tac "a \<star>\<^sub>(mdl M (fgs R M a1)) m = a \<star>\<^sub>M m") apply simp
 apply (thin_tac "a \<star>\<^sub>(mdl M (fgs R M a1)) m = a \<star>\<^sub>M m")
 prefer 2  apply (simp add:mdl_def)
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = "a \<star>\<^sub>M m" in fsps_chain_boundTr2, assumption+)  apply (simp add:mdl_def)
 apply assumption apply (erule conjE)+
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "\<forall>a2 b2. (a2, b2) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M a2 \<and> (THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M aa \<and> y = b ( a \<star>\<^sub>M m))) = b2 (a \<star>\<^sub>M m) \<longrightarrow> False")
 apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
 apply (thin_tac "a \<star>\<^sub>(mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) m  \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and>  a \<star>\<^sub>M m \<in> fgs R M aa \<and> y = b ( a \<star>\<^sub>M m))) \<noteq> a \<star>\<^sub>N (b1 m)")
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M aa \<and> y = b (a \<star>\<^sub>M m))) \<in> carrier N")
 apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M a1 \<and> (THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M aa \<and> y = b (a \<star>\<^sub>M m))) = b1 ( a \<star>\<^sub>M m)")
 apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M aa \<and> y = b (a \<star>\<^sub>M m))) \<in> carrier N")
 apply (rule allI)+ apply (rule impI)
 apply (erule conjE)+ apply simp
apply (thin_tac "(THE y. y \<in> carrier N \<and> (\<exists>aa b. (aa, b) \<in> C \<and> (a \<star>\<^sub>M m) \<in> fgs R M aa \<and> y = b (a \<star>\<^sub>M m))) = b2 (a \<star>\<^sub>M m)")
prefer 2
 apply (rule mdl_is_module, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a1, b1)" in subsetD, assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (subgoal_tac "a \<star>\<^sub>M m \<in> fgs R M a1") prefer 2 apply (simp add:mdl_def)
 apply (subgoal_tac "b1 \<in> mHom R (mdl M (fgs R M a1)) N")
 apply (subgoal_tac "R module (mdl M (fgs R M a1))")
 apply (frule_tac R1 = R and M1 = "mdl M (fgs R M a1)" and N1 = N and m1 = m and f1 = b1 and a1 = a in mHom_lin [THEN sym], assumption+)
 apply (simp add:mdl_def) apply assumption+ apply simp
 apply (subgoal_tac "a \<star>\<^sub>(mdl M (fgs R M a1)) m = a \<star>\<^sub>M m") apply simp
 apply (thin_tac "a \<star>\<^sub>(mdl M (fgs R M a1)) m = a \<star>\<^sub>M m")
 apply (thin_tac "a \<star>\<^sub>N (b1 m) = b1 ( a \<star>\<^sub>M m)")
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = a2 and b = b2 and x = "a \<star>\<^sub>M m" and ?a1.0 = a1 and ?b1.0 = b1 in fsps_chain_boundTr2_2, assumption+)
 apply simp apply (simp add:mdl_def)
 apply (rule mdl_is_module, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a1, b1)" in subsetD,
                        assumption+)
 apply (rule_tac f = f in fgs_submodule, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a1, b1)" in subsetD,
                        assumption+) apply (simp add:fsps_def fsp_def)
done

lemma fsps_chain_bound2:"\<lbrakk>ring R; R module M; R module N; free_generator R M H;  f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H;  \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; C \<noteq> {}\<rbrakk>  \<Longrightarrow> \<forall>y\<in>(\<Union>{a. \<exists>b. (a, b) \<in> C}). (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))) y = f y"
apply (rule ballI)
 apply (subgoal_tac "y \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 prefer 2
 apply simp
 apply (subgoal_tac "\<forall>x. (\<exists>b. (x, b) \<in> C) \<and> y \<in> x \<longrightarrow> (y \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))") apply blast apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> y \<in> x")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "\<forall>b. (x, b) \<in> C \<longrightarrow> y \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 apply blast apply (thin_tac "\<exists>b. (x, b) \<in> C")
 apply (rule allI) apply (rule impI)
 apply (subst fgs_def)
 apply (simp add:linear_span_def)
 apply (subgoal_tac "x \<noteq> {}") prefer 2 apply (simp add:nonempty)
 apply (rule conjI) apply (subgoal_tac "\<not>  (\<forall>x. (\<exists>b. (x, b) \<in> C) \<longrightarrow> x = {})")
 apply blast apply simp apply blast
 apply (subgoal_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}")
 apply simp
 apply (subgoal_tac "(\<lambda>j\<in>Nset 0. 1\<^sub>R) \<in> Nset 0 \<rightarrow> carrier R")
 apply (subgoal_tac "(\<lambda>j\<in>Nset 0. y) \<in> Nset 0 \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}")
 apply (subgoal_tac "y = linear_combination R M 0 (\<lambda>j\<in>Nset 0. 1\<^sub>R) (\<lambda>j\<in>Nset 0. y)")
 apply blast
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:linear_combination_def)
 apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and a = x and b = b in fst_chain_subset, assumption+)
 apply (frule_tac A = x and B = "carrier M" and c = y in subsetD, assumption+)
 apply (simp add:sprod_one) apply (simp add:Nset_def)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply blast
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (simp add:ring_one) apply blast
apply simp
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C and x = y in fsps_chain_boundTr2, assumption+) apply (erule conjE)
apply (thin_tac "(THE ya. ya \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> y \<in> fgs R M a \<and> ya = b y)) \<in> carrier N")
 apply (subgoal_tac "\<forall>a1 b1. (a1, b1) \<in> C \<and> y \<in> fgs R M a1 \<and> (THE ya. ya \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> y \<in> fgs R M a \<and> ya = b y)) = b1 y \<longrightarrow> ((THE ya. ya \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> y \<in> fgs R M a \<and> ya = b y)) = f y)")
 apply blast
 apply (thin_tac "\<exists>a1 b1. (a1, b1) \<in> C \<and> y \<in> fgs R M a1 \<and> (THE ya. ya \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> y \<in> fgs R M a \<and> ya = b y)) = b1 y")
 apply (rule allI)+
 apply (rule impI) apply (erule conjE)+ apply simp
 apply (thin_tac "(THE ya. ya \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> y \<in> fgs R M a \<and> ya = b y)) = b1 y")
 apply (thin_tac "y \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 apply (subgoal_tac "\<forall>x.  (\<exists>b. (x, b) \<in> C) \<and> y \<in> x \<longrightarrow> b1 y = f y")
 apply blast apply (thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> y \<in> x")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "\<forall>b. (x, b) \<in> C \<longrightarrow> b1 y = f y")
 apply blast apply (thin_tac " \<exists>b. (x, b) \<in> C")
apply (rule allI) apply (rule impI)
apply (frule_tac A = C and B = "fsps R M N f H" and c = "(x, b)" in subsetD,
                                    assumption+)
apply (subgoal_tac "fsp R M N f H x b") prefer 2 apply (simp add:fsps_def fsp_def)
apply (simp add:fsp_def) apply (erule conjE)+
 apply (subgoal_tac "f y = b y") prefer 2 apply simp
 apply (subgoal_tac "y \<in> fgs R M x")
 apply (rule_tac a = a1 and b = b1 and ?a1.0 = x and ?b1.0 = b and x = y in  fsps_chain_boundTr2_2 [of "R" "M" "N" "H" "f" "C"], assumption+)
 apply (frule_tac x = y and A = x in nonempty)
 apply (simp add:fgs_def)
 apply (frule_tac R = R and M = M and H = x in elem_linear_span1, assumption+)
 apply (rule_tac R = R and M = M and N = N and H = H and f = f and C = C and a  = x and b = b in fst_chain_subset, assumption+)
 apply (simp add:subsetD)
done

lemma od_fm_fun_inductive:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N\<rbrakk> \<Longrightarrow> inductive_set (od_fm_fun R M N f H)"
apply (simp add:inductive_set_def)
apply (rule conjI)
 apply (subst ordered_set_def)
 apply (rule conjI)
 apply (simp add:od_fm_fun_def)
 apply (rule subsetI) apply simp
apply (rule conjI)
 apply (rule ballI) apply (simp add:od_fm_fun_def)
apply (rule conjI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:od_fm_fun_def)
 apply (simp add:fsps_def fsp_def) apply (erule conjE)+
 apply (subgoal_tac "fst a = fst b") prefer 2 apply (rule equalityI, assumption+)
apply simp
 apply (simp add:split_def)
 apply (subgoal_tac "snd a = snd b")
 apply (subgoal_tac "a = (fst a, snd a)")
 apply (subgoal_tac "b = (fst b, snd b)") apply simp
 apply (simp add:surjective_pairing ) apply (rule surjective_pairing)
 apply (thin_tac "fst a = fst b")
 apply (erule conjE)+
 apply (subgoal_tac "R module (mdl M (fgs R M (fst b)))")
 apply (rule_tac R = R and M = "mdl M (fgs R M (fst b))" and N = N and f = "snd a" and g = "snd b" in mHom_eq, assumption+)
 apply (rule ballI)
 apply (subgoal_tac "m \<in> (if fst b = {} then {0\<^sub>M} else {x. \<exists>n. \<exists>f\<in>Nset n \<rightarrow> fst b. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f})")
 prefer 2 apply (simp add:mdl_def fgs_def linear_span_def)
 apply (case_tac "fst b = {}") apply simp
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = "snd a" in mHom_0, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = "snd b" in mHom_0, assumption+) apply (simp add:mdl_def) apply simp
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> fst b. \<forall>s\<in>Nset n \<rightarrow> carrier R. m = linear_combination R M n s f \<longrightarrow> snd a m = snd b m") apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> fst b. \<exists>s\<in>Nset n \<rightarrow> carrier R. m = linear_combination R M n s f") apply (rule allI) apply (rule ballI)+
 apply (rule impI) apply simp
 apply (frule whole_ideal [of "R"])
 apply (frule_tac R = R and A = "carrier R" and M = "mdl M (fgs R M (fst b))" and N = N and f = "snd a" and H = "fst b" and n = n and s = s and g = fa in linmap_im_lincomb, assumption+)
 apply (subst mdl_def)  apply simp  apply (subst fgs_def)
 apply (subgoal_tac "fst b \<subseteq> carrier M") apply (simp add:elem_linear_span1)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def) apply assumption+
 apply (frule_tac R = R and M = M and H = H and A = "fst b" and f = fa and s = s in eSum_in_Submodule, assumption+) apply (simp add:free_generator_def generator_def) apply assumption apply simp apply assumption apply simp
 apply (thin_tac "linear_combination R (mdl M (fgs R M (fst b))) n s fa =
          linear_combination R M n s fa")
 apply (frule_tac R = R and A = "carrier R" and M = "mdl M (fgs R M (fst b))" and N = N and f = "snd b" and H = "fst b" and n = n and s = s and g = fa in linmap_im_lincomb, assumption+)
 apply (subst mdl_def)  apply simp  apply (subst fgs_def)
 apply (rule elem_linear_span1, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def) apply assumption+
 apply (frule_tac R = R and M = M and H = H and A = "fst b" and f = fa and s = s in eSum_in_Submodule, assumption+) apply (simp add:free_generator_def generator_def) apply assumption apply simp apply assumption apply simp
 apply (thin_tac "snd a (linear_combination R M n s fa) =
          linear_combination R N n s (cmp (snd a) fa)")
 apply (thin_tac "snd b (linear_combination R M n s fa) =
          linear_combination R N n s (cmp (snd b) fa)")
 apply (thin_tac "linear_combination R (mdl M (fgs R M (fst b))) n s fa =
          linear_combination R M n s fa")
 apply (thin_tac "m = linear_combination R M n s fa")
 apply (subst linear_combination_def)+
 apply (rule eSum_eq) apply (simp add:module_is_ag)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (subst cmp_def)
 apply (rule_tac R = R and M = "mdl M (fgs R M (fst b))" and N = N and f = "snd a" and m = "fa x" in mHom_mem, assumption+)
 apply (simp add:mdl_def)
 apply (frule_tac f = fa and A = "Nset n" and B = "fst b" in funcset_mem, assumption+)
 apply (subst fgs_def)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = "fst b" and a = "1\<^sub>R" and h = "fa x" in elem_linear_span, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:ring_one) apply assumption
apply (subgoal_tac "fa x \<in> carrier M")
 apply (simp add:sprod_one)
 apply (subgoal_tac "H \<subseteq> carrier M")
 apply (frule_tac A = "fst b" and B = H and c = "fa x" in subsetD, assumption+)
 apply (rule_tac A = H and B = "carrier M" and c = "fa x" in subsetD, assumption+) apply (simp add:free_generator_def generator_def)
apply (rule univar_func_test)
 apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (subst cmp_def)
 apply (rule_tac R = R and M = "mdl M (fgs R M (fst b))" and N = N and f = "snd b" and m = "fa x" in mHom_mem, assumption+)
 apply (simp add:mdl_def)
 apply (frule_tac f = fa and A = "Nset n" and B = "fst b" in funcset_mem, assumption+)
 apply (subst fgs_def)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = "fst b" and a = "1\<^sub>R" and h = "fa x" in elem_linear_span, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:ring_one) apply assumption
apply (subgoal_tac "fa x \<in> carrier M")
 apply (simp add:sprod_one)
 apply (subgoal_tac "H \<subseteq> carrier M")
 apply (frule_tac A = "fst b" and B = H and c = "fa x" in subsetD, assumption+)
 apply (rule_tac A = H and B = "carrier M" and c = "fa x" in subsetD, assumption+) apply (simp add:free_generator_def generator_def)
apply (rule ballI)
 apply (frule_tac f = fa and A = "Nset n" and B = "fst b" and x = l in funcset_mem, assumption)
 apply (simp add:cmp_def)
 apply (rule mdl_is_module, assumption+)
 apply (subst fgs_def)
 apply (frule whole_ideal [of "R"])
 apply (rule_tac R = R and M = M and A = "carrier R" and H = "fst b" in linear_span_subModule, assumption+)
 apply (rule subset_trans, assumption+) apply (simp add:free_generator_def generator_def)
apply (rule conjI)
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply (simp add:od_fm_fun_def)
 apply (rule ballI)+
 apply (simp add:od_fm_fun_def)
apply (rule allI) apply (rule impI)
apply (case_tac "C = {}")
apply (simp add:upper_bound_def)
 apply (subst od_fm_fun_def) apply simp apply (simp add:fsps_def fsp_def)
 apply (subgoal_tac "(\<lambda>x\<in>(fgs R M {}). 0\<^sub>N) \<in> mHom R (mdl M (fgs R M {})) N \<and>
          (\<forall>z\<in>{}. f z = b z) \<and> {} \<subseteq> H") apply blast
 apply (rule conjI)
 apply (subgoal_tac "R module (mdl M (fgs R M {}))")
 apply (rule_tac R = R and M = "mdl M (fgs R M {})" and N = N and f = "\<lambda>x\<in>fgs R M {}. 0\<^sub>N" in mHom_test, assumption+)
 apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:fgs_def linear_span_def)
 apply (simp add:mdl_def) apply (rule ag_inc_zero) apply (simp add:module_is_ag)
 apply (rule conjI)
 apply (simp add:restrict_def extensional_def mdl_def)
 apply (rule conjI) apply (rule ballI)+
 apply (simp add:fsp_def linear_span_def mdl_def)
 apply (simp add:fgs_def linear_span_def)
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (frule  ag_inc_zero[of "M"]) apply (frule ag_inc_zero [of "N"])
 apply (simp add:ag_l_zero)
 apply (rule ballI)+ apply (simp add:mdl_def fgs_def linear_span_def)
 apply (frule  module_is_ag[of "R" "M"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:sprod_a_0)
 apply (simp add:fgs_def linear_span_def)
 apply (rule mdl_is_module, assumption+)
 apply (simp add: submodule_0)
apply (rule conjI) apply simp apply simp
(** from here C \<noteq> {} **)
 apply (simp add:Chain_def)
 apply (simp add:tordered_set_def) apply (simp add:Iod_def)
 apply (erule conjE)+
apply (simp add:upper_bound_def)
 apply (simp add:od_fm_fun_def Iod_def)
 apply (subgoal_tac "\<forall>z. z \<in> C \<longrightarrow> z \<in> fsps R M N f H") apply simp
prefer 2 apply (rule allI) apply (rule impI) apply (rule subsetD, assumption+)
 apply (subgoal_tac "((\<Union>{a. \<exists>b. (a, b) \<in> C}),  (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)))) \<in> fsps R M N f H")
 apply (subgoal_tac "\<forall>s \<in> C. (((\<Union>{a. \<exists>b. (a, b) \<in> C}),  (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and>y = b x)))) \<in> fsps R M N f H \<longrightarrow> (s \<in> fsps R M N f H \<longrightarrow> fst s \<subseteq> (\<Union>{a. \<exists>b. (a, b) \<in> C})) \<and> (s \<notin> fsps R M N f H \<longrightarrow> arbitrary ((\<Union>{a. \<exists>b. (a, b) \<in> C}),  (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)))))) \<and> (((\<Union>{a. \<exists>b. (a, b) \<in> C}),  (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)))) \<notin> fsps R M N f H \<longrightarrow> (s \<in> fsps R M N f H \<longrightarrow> arbitrary) \<and>(s \<notin> fsps R M N f H \<longrightarrow> arbitrary ((\<Union>{a. \<exists>b. (a, b) \<in> C}),  (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))))))")
apply blast
apply (rule ballI) apply simp
apply (frule_tac A = C and B = "fsps R M N f H" and c = s in subsetD, assumption+) apply simp
apply (rule subsetI) apply simp
 apply (subgoal_tac "(fst s, snd s) \<in> C") apply blast apply simp
 apply (subgoal_tac "fsp R M N f H (\<Union>{a. \<exists>b. (a, b) \<in> C}) (\<lambda>x\<in>fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}). THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))") apply (subst fsps_def) apply blast
apply (subst fsp_def)
apply (rule conjI)
 apply (rule fsps_chain_bound1, assumption+)
apply (rule conjI)
apply (frule_tac R = R and M = M and N = N and H = H and f = f and C = C in fsps_chain_bound2, assumption+)
apply (rule ballI)
 apply (subgoal_tac "(\<lambda>x\<in>fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}). THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) z = f z")
apply (rule sym) apply assumption apply blast
apply (rule subsetI) apply simp
 apply (thin_tac "ordered_set \<lparr>carrier = C, ord_rel = {x. x \<in> fsps R M N f H \<times> fsps R M N f H \<and> fst (fst x) \<subseteq> fst (snd x) \<and> fst x \<in> C \<and> snd x \<in> C}, ordering = \<lambda>u\<in>fsps R M N f H. \<lambda>v\<in>fsps R M N f H. fst u \<subseteq> fst v\<rparr>")
 apply (thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a")
 apply (thin_tac "\<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H")
 apply auto
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(xa, b)" in subsetD, assumption+)
 apply (simp add:fsps_def fsp_def)
 apply (erule conjE)+
 apply (frule_tac A = xa and B = H and c = x in subsetD, assumption+)
apply simp
done

lemma sSum_eq:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; H1 \<subseteq> H; h \<in> H - H1\<rbrakk> \<Longrightarrow>  (fgs R M H1) \<plusminus>\<^sub>M (fgs R M {h}) = fgs R M (H1 \<union> {h})"
apply (rule equalityI)
apply (rule subsetI)
apply (simp add:sSum_def)
 apply (subgoal_tac "\<forall>h1\<in>fgs R M H1. \<forall>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<longrightarrow>
                                           x \<in> fgs R M (insert h H1)")
 apply blast
 apply (thin_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2")
 apply (rule ballI)+ apply (rule impI)
 apply (frule_tac R = R and M = M and N = N and H = H and ?H1.0 = H1 and ?H2.0 = "insert h H1" in fgs_mono, assumption+)
 apply (rule subsetI) apply simp
 apply (rule subsetI) apply simp apply (case_tac "xa = h") apply simp
 apply simp apply (simp add:subsetD)
 apply (frule_tac R = R and M = M and N = N and H = H and ?H1.0 = "{h}" and ?H2.0 = "insert h H1" in fgs_mono, assumption+)
 apply simp apply (rule subsetI) apply simp apply (case_tac "xa = h")
 apply simp apply (simp add:subsetD) apply simp
 apply (frule_tac A = "fgs R M H1" and B = "fgs R M (insert h H1)" and c = h1 in subsetD, assumption+)
 apply (frule_tac A = "fgs R M {h}" and B = "fgs R M (insert h H1)" and c = h2 in subsetD, assumption+)
 apply (subgoal_tac "submodule R M (fgs R M (insert h H1))")
 apply (simp add:submodule_pOp_closed)
apply (subst fgs_def) apply (rule linear_span_subModule, assumption+)
 apply (simp add:whole_ideal)
 apply (rule subsetI) apply simp apply (subgoal_tac "H \<subseteq> carrier M")
 apply (case_tac "xa = h") apply (simp add:subsetD) apply simp
 apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+) apply (simp add:subsetD) apply (simp add:free_generator_def generator_def)
apply (rule subsetI) apply (simp add:fgs_def)
apply (subgoal_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> insert h H1. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f") prefer 2 apply (simp add:linear_span_def)
apply (thin_tac "x \<in> linear_span R M (carrier R) (insert h H1)")
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> insert h H1. \<forall>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f \<longrightarrow> x \<in> linear_span R M (carrier R) H1 \<plusminus>\<^sub>M
                  (linear_span R M (carrier R) {h})")
apply blast
apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> insert h H1. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp add:linear_combination_def)
 apply (frule whole_ideal [of "R"])
 apply (frule_tac H = H1 in linear_span_subModule [of "R" "M" "carrier R"], assumption+) apply (subgoal_tac "H \<subseteq> carrier M") apply (rule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
apply (frule_tac H = "{h}" in linear_span_subModule [of "R" "M" "carrier R"], assumption+) apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac R = R and M = M and ?H1.0 = "linear_span R M (carrier R) H1" and ?H2.0 = "linear_span R M (carrier R) {h}" and g = "(\<lambda>j.  s j \<star>\<^sub>M (f j))" and n = n in Sum_of_SubmodulesTr, assumption+)
 apply (subgoal_tac "(\<lambda>j. s j \<star>\<^sub>M (f j)) \<in> Nset n \<rightarrow> linear_span R M (carrier R) H1 \<union> linear_span R M (carrier R) {h}") apply simp
apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = f and A = "Nset n" and B = "insert h H1" and x = xa in funcset_mem, assumption+) apply simp
 apply (thin_tac "(\<lambda>j. s j \<star>\<^sub>M (f j)) \<in> Nset n \<rightarrow> linear_span R M (carrier R) H1 \<union> linear_span R M (carrier R) {h} \<longrightarrow>  e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n \<in> linear_span R M (carrier R) H1 \<plusminus>\<^sub>M (linear_span R M (carrier R) {h})")
 apply (case_tac "f xa = h") apply simp
 apply (frule_tac f = s and A = "Nset n" and B = "carrier R" and x = xa in funcset_mem, assumption+)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = "{h}" and a = "s xa" and h = h in elem_linear_span, assumption+) apply simp
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def) apply (simp add:funcset_mem)
 apply simp apply simp apply simp
 apply (frule_tac R = R and M = M and A = "carrier R" and H = "H1" and a = "s xa" and h = "f xa" in elem_linear_span, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def) apply (simp add:funcset_mem)
 apply assumption+ apply simp
done

constdefs
 monofun::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, ('b, 'r, 'm2) ModuleType_scheme, 'a \<Rightarrow> 'b, 'a set, 'a] \<Rightarrow> ('a \<Rightarrow> 'b)"
 "monofun R M N f H h == (\<lambda>x\<in>fgs R M {h}. (THE y. (\<exists>r\<in>carrier R. x = r \<star>\<^sub>M h \<and>   y = r \<star>\<^sub>N (f h))))"

lemma fgs_single_span:"\<lbrakk>ring R; R module M; R module N; h \<in> carrier M; x \<in> (fgs R M {h})\<rbrakk> \<Longrightarrow> \<exists>a\<in>carrier R. x = a \<star>\<^sub>M h"
apply (simp add:fgs_def linear_span_def)
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> {h}. \<forall>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f \<longrightarrow> (\<exists>a\<in>carrier R. x =  a \<star>\<^sub>M h)")
apply blast
apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> {h}. \<exists>s\<in>Nset n \<rightarrow> carrier R. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (frule_tac R = R and M = M and A = "carrier R" and z = h and h = f and n = n and t = s in single_span, assumption+)
 apply (simp add:whole_ideal) apply assumption+
apply (subgoal_tac "\<forall>sa\<in>Nset 0 \<rightarrow> carrier R. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  sa 0 \<star>\<^sub>M h \<longrightarrow> (\<exists>a\<in>carrier R. x =  a \<star>\<^sub>M h)")
 apply blast
 apply (thin_tac "\<exists>sa\<in>Nset 0 \<rightarrow> carrier R. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  sa 0 \<star>\<^sub>M h")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "0 \<in> Nset 0") apply (frule_tac f = sa and A = "Nset 0" and
 B = "carrier R" and x = 0 in funcset_mem, assumption+)
 apply (simp add:linear_combination_def) apply blast
apply (simp add:Nset_def)
done

lemma monofun_mHomTr:"\<lbrakk>ring R; R module M; R module N; h \<in> H; free_generator R M H; f \<in> H \<rightarrow> carrier N; a \<in> carrier R; H \<subseteq> carrier M; r \<in> carrier R; a \<star>\<^sub>M h = r \<star>\<^sub>M h\<rbrakk> \<Longrightarrow> a = r"
apply (frule_tac R = R and M = M and a = a and m = h in sprod_mem, assumption+)
 apply (simp add:subsetD)
apply (frule_tac R = R and M = M and a = r and m = h in sprod_mem, assumption+)
 apply (simp add:subsetD)
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac G = M and x = "r \<star>\<^sub>M h" in ag_mOp_closed, assumption)
 apply (frule_tac G = M and a = "a \<star>\<^sub>M h" and b = "r \<star>\<^sub>M h" and c = "-\<^sub>M  (r \<star>\<^sub>M h)" in ag_pOp_add_r, assumption+)
 apply (thin_tac "a \<star>\<^sub>M h =  r \<star>\<^sub>M h")
 apply (simp add:ag_r_inv1)
 apply (frule_tac A = H and B = "carrier M" and c = h in subsetD, assumption+)
 apply (simp add:sprod_minus_am1)
 apply (frule ring_is_ag [of "R"])
apply (frule_tac G = R and x = r in ag_mOp_closed, assumption+)
 apply (simp add:sprod_distrib1[THEN sym])
apply (simp add:free_generator_def) apply (erule conjE)+
apply (subgoal_tac "(\<lambda>j. (a +\<^sub>R (-\<^sub>R r))) \<in> Nset 0 \<rightarrow> carrier R")
apply (subgoal_tac "(\<lambda>j. h) \<in> Nset 0 \<rightarrow> H \<and> inj_on (\<lambda>j. h) (Nset 0) \<and>
 linear_combination R M 0 (\<lambda>j. (a +\<^sub>R (-\<^sub>R r))) (\<lambda>j. h) = 0\<^sub>M")
apply (subgoal_tac "(\<lambda>j. (a +\<^sub>R (-\<^sub>R r))) \<in> Nset 0 \<rightarrow> {0\<^sub>R}")
 apply (subgoal_tac "0\<in>Nset 0")
 apply (frule_tac f = "\<lambda>j. a +\<^sub>R -\<^sub>R r" and A = "Nset 0" and B = "{0\<^sub>R}" and x = 0 in funcset_mem, assumption+) apply simp
 apply (subgoal_tac "a +\<^sub>R -\<^sub>R r \<in> carrier R")
 apply (frule_tac G = R and a = "a +\<^sub>R -\<^sub>R r" and b = "0\<^sub>R" and c = r in ag_pOp_add_r, assumption+)
 apply (simp add:ag_inc_zero) apply assumption+
 apply (thin_tac "a +\<^sub>R -\<^sub>R r = 0\<^sub>R")
 apply (simp add:ag_pOp_assoc) apply (simp add:ag_l_inv1)
 apply (simp add:ag_l_zero) apply (simp add:ag_r_zero) apply simp
 apply (simp add:ag_inc_zero) apply (simp add:Nset_def)
apply blast
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI) apply assumption
 apply (rule conjI)
 apply (subst inj_on_def) apply (simp add:Nset_def)
 apply (subst linear_combination_def) apply simp
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (rule ag_pOp_closed, assumption+)
done

lemma monofun_mhomTr1:"\<lbrakk>ring R; R module M; R module N; h \<in> H; free_generator R M H; f \<in> H \<rightarrow> carrier N; a \<in> carrier R\<rbrakk>  \<Longrightarrow>  monofun R M N f H h (a \<star>\<^sub>M h) = a \<star>\<^sub>N (f h)"
apply (subgoal_tac "H \<subseteq> carrier M")
 prefer 2 apply (simp add:free_generator_def generator_def)
apply (simp add:monofun_def)
apply (subgoal_tac "a \<star>\<^sub>M h \<in> fgs R M {h}") apply simp
 prefer 2 apply (simp add:fgs_def)
 apply (rule_tac linear_span_sprod_closed [of "R" "M" "carrier R" "{h}" "a" "h"], assumption+)
 apply (simp add:whole_ideal)
 apply (rule subsetI) apply (simp add:subsetD) apply assumption
 apply (frule_tac R = R and M = M and H = "{h}" in elem_linear_span1, assumption+) apply (rule subsetI) apply (simp add:subsetD) apply simp
apply (subgoal_tac "\<exists>!y. \<exists>r\<in>carrier R.  a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> y =  r \<star>\<^sub>N (f h)")
apply (subgoal_tac "\<exists>r\<in>carrier R. a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> (THE y. \<exists>s\<in>carrier R.  a \<star>\<^sub>M h =  s \<star>\<^sub>M h \<and> y =  s \<star>\<^sub>N (f h)) =  r \<star>\<^sub>N (f h)")
prefer 2 apply (rule theI')
apply simp
 apply (thin_tac "\<exists>!y. \<exists>r\<in>carrier R.  a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> y =  r \<star>\<^sub>N (f h)")
 apply (subgoal_tac "\<forall>r\<in>carrier R. a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> (THE y. \<exists>s\<in>carrier R.  a \<star>\<^sub>M h =  s \<star>\<^sub>M h \<and> y = s \<star>\<^sub>N (f h)) = r \<star>\<^sub>N (f h) \<longrightarrow> ((THE y. \<exists>r\<in>carrier R.  a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> y = r \<star>\<^sub>N (f h)) = a \<star>\<^sub>N (f h))")
 apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> (THE y. \<exists>s\<in>carrier R. a \<star>\<^sub>M h = s \<star>\<^sub>M h \<and> y = s \<star>\<^sub>N (f h)) =  r \<star>\<^sub>N (f h)")
 apply (rule ballI) apply (rule impI) apply (erule conjE)+ apply simp
 apply (thin_tac " (THE y. \<exists>s\<in>carrier R.  r \<star>\<^sub>M h =  s \<star>\<^sub>M h \<and> y =  s \<star>\<^sub>N (f h)) = r \<star>\<^sub>N (f h)")
 apply (subgoal_tac "a = r") apply blast
 apply (simp add:monofun_mHomTr)
apply (rule ex_ex1I)
 apply (subgoal_tac "a \<star>\<^sub>M h =  a \<star>\<^sub>M h \<and>  a \<star>\<^sub>N (f h) =  a \<star>\<^sub>N (f h)") apply blast
 apply simp
apply (subgoal_tac "\<forall>r\<in>carrier R. \<forall>s\<in>carrier R. a \<star>\<^sub>M h =  r \<star>\<^sub>M h \<and> y =  r \<star>\<^sub>N (f h) \<and> a \<star>\<^sub>M h =  s \<star>\<^sub>M h \<and> ya =  s \<star>\<^sub>N (f h) \<longrightarrow> y = ya")
apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. a \<star>\<^sub>M h = r \<star>\<^sub>M h \<and> y = r \<star>\<^sub>N (f h)")
 apply (thin_tac "\<exists>r\<in>carrier R. a \<star>\<^sub>M h = r \<star>\<^sub>M h \<and> ya = r \<star>\<^sub>N (f h)")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)+
 apply simp
 apply (frule_tac R = R and M = M and N = N and h = h and H = H and f = f and a = r and r = s in monofun_mHomTr, assumption+) apply (rule sym)
 apply assumption
apply blast
done

lemma monofun_mem:"\<lbrakk>ring R; R module M; R module N; h \<in> H; free_generator R M H; x \<in> fgs R M {h}; f \<in> H \<rightarrow> carrier N\<rbrakk>  \<Longrightarrow>  monofun R M N f H h x \<in> carrier N"

apply (subgoal_tac "H \<subseteq> carrier M")
 prefer 2 apply (simp add:free_generator_def generator_def)
apply (frule fgs_single_span [of "R" "M" "N" "h" "x"], assumption+)
 apply (simp add:subsetD) apply assumption
apply (subgoal_tac "\<forall>a\<in>carrier R. x =  a \<star>\<^sub>M h \<longrightarrow> monofun R M N f H h x \<in> carrier N") apply blast apply (thin_tac "\<exists>a\<in>carrier R. x =  a \<star>\<^sub>M h")
apply (rule ballI) apply (rule impI) apply simp
apply (frule_tac R = R and M = M and N = N and h = h and f = f and a = a in monofun_mhomTr1, assumption+) apply simp
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem)
done

lemma monofun_eq_f:"\<lbrakk>ring R; R module M; R module N; h \<in> H; free_generator R M H; f \<in> H \<rightarrow> carrier N\<rbrakk>  \<Longrightarrow>  monofun R M N f H h h = f h"
apply (frule_tac R = R and M = M and N = N and h = h and f = f and a = "1\<^sub>R" in
 monofun_mhomTr1, assumption+)
 apply (simp add:ring_one)
 apply (frule_tac f = f and A = H and B = "carrier N" and x = h in funcset_mem,
                           assumption+)
 apply (subgoal_tac "h \<in> carrier M")
 apply (simp add:sprod_one)
apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
done

lemma sSum_unique:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; H1 \<subseteq> H; h \<in> H - H1; h1 \<in>(fgs R M H1); h2 \<in> (fgs R M H1); k1 \<in> (fgs R M {h}); k2 \<in> (fgs R M {h}); h1 +\<^sub>M k1 = h2 +\<^sub>M k2\<rbrakk> \<Longrightarrow> h1 = h2 \<and> k1 = k2"
apply (frule whole_ideal [of "R"])
apply (subgoal_tac "H \<subseteq> carrier M") prefer 2 apply (simp add:free_generator_def generator_def)
 apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+)
 apply simp apply (erule conjE)
 apply (frule_tac A = H and B = "carrier M" and c = h in subsetD, assumption+)
 apply (frule_tac R = R and M = M and N = N and h = h and x = k1 in fgs_single_span, assumption+)
 apply (subgoal_tac "\<forall>a\<in>carrier R. k1 =  a \<star>\<^sub>M h \<longrightarrow> h1 = h2 \<and> k1 = k2")
 apply blast apply (thin_tac "\<exists>a\<in>carrier R. k1 =  a \<star>\<^sub>M h")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac R = R and M = M and a = a and m = h in sprod_mem, assumption+)
 apply (frule_tac R = R and M = M and N = N and h = h and x = k2 in fgs_single_span, assumption+)
 apply (subgoal_tac "\<forall>b\<in>carrier R. k2 =  b \<star>\<^sub>M h \<longrightarrow> h1 = h2 \<and> k1 = k2")
 apply blast apply (thin_tac "\<exists>a\<in>carrier R. k2 =  a \<star>\<^sub>M h")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac R = R and M = M and a = b and m = h in sprod_mem, assumption+)
apply (frule_tac R = R and A = "carrier R" and M = M and H = H1 in lin_span_sub_carrier, assumption+)
 apply (simp add:fgs_def)
 apply (frule_tac A = "linear_span R M (carrier R) H1" and B = "carrier M" and
 c = h1 in subsetD, assumption+)
 apply (frule_tac A = "linear_span R M (carrier R) H1" and B = "carrier M" and
 c = h2 in subsetD, assumption+)
 apply (subgoal_tac "-\<^sub>M h2 +\<^sub>M (h1 +\<^sub>M k1) = -\<^sub>M h2 +\<^sub>M (h2 +\<^sub>M k2)")
 prefer 2 apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac G = M and x = h2 in ag_mOp_closed, assumption+)
 apply (thin_tac "h1 +\<^sub>M  a \<star>\<^sub>M h =  h2 +\<^sub>M  b \<star>\<^sub>M h")
 apply (simp add:ag_pOp_assoc[THEN sym])
 apply (simp add:ag_l_inv1) apply (simp add:ag_l_zero)
 apply (frule_tac G = M and x = "-\<^sub>M h2" and y = h1 in ag_pOp_closed, assumption+)
 apply (frule_tac G = M and x = "-\<^sub>M h2 +\<^sub>M h1" and y = k1 in ag_pOp_closed, assumption+) apply simp
 apply (frule_tac a = "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M (a \<star>\<^sub>M h)" and b = "b \<star>\<^sub>M h" and c = "-\<^sub>M (b \<star>\<^sub>M h)" in ag_pOp_add_r) apply simp apply assumption
 apply (rule ag_mOp_closed, assumption+)
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  a \<star>\<^sub>M h =  b \<star>\<^sub>M h")
 apply (simp add:ag_r_inv1)
 apply (frule_tac x = "-\<^sub>M h2 +\<^sub>M h1" and y = "a \<star>\<^sub>M h" and z = "-\<^sub>M (b \<star>\<^sub>M h)" in ag_pOp_assoc, assumption+)
 apply (rule ag_mOp_closed, assumption+) apply simp
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  a \<star>\<^sub>M h +\<^sub>M (-\<^sub>M  (b \<star>\<^sub>M h)) = 0\<^sub>M")
 apply (frule_tac R = R and M = M and a = b and m = h in sprod_minus_am1,
             assumption+) apply simp
apply (frule ring_is_ag[of "R"]) apply (thin_tac "-\<^sub>M (b \<star>\<^sub>M h) =  (-\<^sub>R b) \<star>\<^sub>M h")
apply (frule_tac G = R and x = b in ag_mOp_closed, assumption+)
apply (simp add:sprod_distrib1 [THEN sym])
apply (frule_tac x = a and y = "-\<^sub>R b" in ag_pOp_closed [of "R"], assumption+)
apply (thin_tac "a \<star>\<^sub>M h \<in> linear_span R M (carrier R) {h}")
apply (thin_tac "b \<star>\<^sub>M h \<in> linear_span R M (carrier R) {h}")
apply (thin_tac "k1 =  a \<star>\<^sub>M h") apply (thin_tac "k2 =  b \<star>\<^sub>M h")
apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 \<in> carrier M")
apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  (a \<star>\<^sub>M h) \<in> carrier M")
apply (frule_tac R = R and M = M and A = "carrier R" and H = H1 and a = h2 in linear_span_iOp_closed, assumption+)
apply (frule_tac R = R and M = M and A = "carrier R" and H = H1 and a = "-\<^sub>M h2" and b = h1 in linear_span_tOp_closed, assumption+)
apply (thin_tac "h1 \<in> linear_span R M (carrier R) H1")
 apply (thin_tac "h2 \<in> linear_span R M (carrier R) H1")
 apply (thin_tac "linear_span R M (carrier R) H1 \<subseteq> carrier M")
 apply (thin_tac "-\<^sub>M h2 \<in> linear_span R M (carrier R) H1")
apply (simp add:linear_span_def [of _ _ _ "H1"])
apply (case_tac "H1 = {}") apply simp
 apply (frule_tac a = "-\<^sub>M h2 +\<^sub>M h1" and b = "0\<^sub>M" and c = h2 in ag_pOp_add_l) apply (rule ag_pOp_closed, assumption+) apply (simp add:ag_inc_zero)
 apply assumption+
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 = 0\<^sub>M")
 apply (simp add:ag_pOp_assoc[of "M", THEN sym])
 apply (simp add:ag_r_zero) apply (simp add:ag_r_inv1)
 apply (simp add:ag_l_zero)
 apply (simp add:sprod_distrib1)
apply (frule_tac R = R and M = M and a = "-\<^sub>R b" and m = h in sprod_mem, assumption+)
 apply (frule_tac x = "a \<star>\<^sub>M h" and y = "(-\<^sub>R b) \<star>\<^sub>M h" in ag_pOp_closed [of "M"], assumption+)
 apply (simp add:ag_l_zero)
 apply (simp add:sprod_minus_am1 [THEN sym])
 apply (frule_tac G = M and a = "a \<star>\<^sub>M h +\<^sub>M -\<^sub>M  (b \<star>\<^sub>M h)" and b = "0\<^sub>M" and c = "b \<star>\<^sub>M h" in ag_pOp_add_r)
 apply (rule ag_pOp_closed, assumption+)
 apply (thin_tac "a \<star>\<^sub>M h +\<^sub>M (-\<^sub>M (b \<star>\<^sub>M h)) = 0\<^sub>M")
 apply (simp add:ag_pOp_assoc)
 apply (simp add:ag_l_inv1) apply (simp add:ag_r_zero)
 apply (simp add:ag_l_zero)
apply simp
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H1. \<forall>s\<in>Nset n \<rightarrow> carrier R. -\<^sub>M h2 +\<^sub>M h1 = linear_combination R M n s f \<longrightarrow> (h1 = h2 \<and>  a \<star>\<^sub>M h =  b \<star>\<^sub>M h)")
apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H1. \<exists>s\<in>Nset n \<rightarrow> carrier R.  -\<^sub>M h2 +\<^sub>M h1 = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (frule_tac R = R and M = M and H = H1 and f = f and n = n and s = s in unique_expression2, assumption+)
 apply (subgoal_tac "\<forall>m g t. g \<in> Nset m \<rightarrow> H1 \<and> bij_to g (Nset m) (f ` Nset n) \<and> t \<in> Nset m \<rightarrow> carrier R \<and>  linear_combination R M n s f = linear_combination R M m t g \<longrightarrow> (h1 = h2 \<and>  a \<star>\<^sub>M h =  b \<star>\<^sub>M h)")
 apply (thin_tac "f \<in> Nset n \<rightarrow> H1")
 apply (thin_tac "s \<in> Nset n \<rightarrow> carrier R")
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 = linear_combination R M n s f")
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  ( a +\<^sub>R -\<^sub>R b) \<star>\<^sub>M h = 0\<^sub>M")
 apply blast
 apply (thin_tac "\<exists>m g t. g \<in> Nset m \<rightarrow> H1 \<and> bij_to g (Nset m) (f ` Nset n) \<and>  t \<in> Nset m \<rightarrow> carrier R \<and> linear_combination R M n s f = linear_combination R M m t g")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac " -\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  ( a +\<^sub>R -\<^sub>R b) \<star>\<^sub>M h = linear_combination R M (Suc m) (jointfun m t 0 (\<lambda>k\<in>Nset 0. (a +\<^sub>R (-\<^sub>R b)))) (jointfun m g 0 (\<lambda>k\<in>Nset 0. h))")
 apply (subgoal_tac "inj_on (jointfun m g 0 (\<lambda>k\<in>Nset 0. h)) (Nset (Suc m))")
 apply simp
 apply (frule_tac R = R and M = M and H = H and s = "jointfun m t 0 (\<lambda>k\<in>Nset 0.  a +\<^sub>R (-\<^sub>R b))" and n = "Suc m" and m = "jointfun m g 0 (\<lambda>k\<in>Nset 0. h)" in unique_expression1, assumption+)
 apply (subgoal_tac "(\<lambda>k\<in>Nset 0.  a +\<^sub>R -\<^sub>R b) \<in> Nset 0 \<rightarrow> carrier R") prefer 2 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:Nset_def)
 apply (frule_tac f = t and n = m and A = "carrier R" and g = "(\<lambda>k\<in>Nset 0.  a +\<^sub>R (-\<^sub>R b))" and B = "carrier R" in jointfun_hom, assumption+)
 apply simp
 apply (subgoal_tac "g \<in> Nset m \<rightarrow> H") prefer 2 apply (rule univar_func_test)
 apply (rule ballI)
 apply (frule_tac f = g and A = "Nset m" and B = H1 and x = x in funcset_mem, assumption+)
 apply (simp add:subsetD)
 apply (subgoal_tac "(\<lambda>k\<in>Nset 0. h) \<in> Nset 0 \<rightarrow> H")
 prefer 2 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Nset_def)
 apply (frule_tac f = g and n = m and A = H and g = "(\<lambda>k\<in>Nset 0. h)" and B = H in jointfun_hom, assumption+) apply simp
 apply assumption
 apply (rule sym) apply simp
 apply (subgoal_tac "Suc m \<in> Nset (Suc m)") prefer 2 apply (simp add:Nset_def)
 apply (subgoal_tac "jointfun m t 0 (\<lambda>k\<in>Nset 0.  a +\<^sub>R -\<^sub>R b) (Suc m) = 0\<^sub>R")
 prefer 2 apply simp
 apply (subgoal_tac "jointfun m t 0 (\<lambda>k\<in>Nset 0.  a +\<^sub>R -\<^sub>R b) (Suc m) = a +\<^sub>R -\<^sub>R b") prefer 2 apply (thin_tac "jointfun m t 0 (\<lambda>k\<in>Nset 0.  a +\<^sub>R -\<^sub>R b) (Suc m) = 0\<^sub>R")
 apply (simp add:jointfun_def sliden_def) apply (subgoal_tac "0 \<in> Nset 0")
 apply simp  apply (simp add:Nset_def) apply simp
 apply (frule ring_is_ag [of "R"])
 apply (subgoal_tac "a +\<^sub>R -\<^sub>R b \<in> carrier R")
 apply (frule_tac G = R and a = "a +\<^sub>R -\<^sub>R b" and b = "0\<^sub>R" and c = b in ag_pOp_add_r, assumption+)
 apply (thin_tac "a +\<^sub>R -\<^sub>R b = 0\<^sub>R")
 apply (simp add:ag_pOp_assoc [of "R"])
 apply (simp add:ag_l_inv1)
 apply (simp add:ag_r_zero) apply (simp add:ag_l_zero)
 apply (subgoal_tac "linear_combination R M m t g = 0\<^sub>M")
 apply (thin_tac "0\<^sub>M = linear_combination R M (Suc m) (jointfun m t 0 (\<lambda>k\<in>Nset 0. 0\<^sub>R)) (jointfun m g 0 (\<lambda>k\<in>Nset 0. h))") apply simp
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "-\<^sub>M h2 +\<^sub>M h1 \<in> carrier M")
 apply (frule_tac G = M and a = "-\<^sub>M h2 +\<^sub>M h1" and b = "0\<^sub>M" and c = h2 in ag_pOp_add_l, assumption+) apply (simp add:ag_inc_zero) apply assumption+
 apply (thin_tac " -\<^sub>M h2 +\<^sub>M h1 = 0\<^sub>M")
 apply (simp add:ag_r_zero)
 apply (simp add:ag_pOp_assoc [THEN sym])
 apply (simp add:ag_r_inv1) apply (simp add:ag_l_zero)
 apply (simp add:ag_pOp_closed) apply (simp add:ag_inc_zero)
apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+)
 apply (rule_tac R = R and M = M and H = H1 and s = t and m = g in linear_comb0_1, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<in> Nset (Suc m)")
 apply (subgoal_tac "jointfun m t 0 (\<lambda>k\<in>Nset 0. 0\<^sub>R) x = 0\<^sub>R")
 prefer 2 apply simp
 apply (thin_tac "\<forall>j\<in>Nset (Suc m). jointfun m t 0 (\<lambda>k\<in>Nset 0. 0\<^sub>R) j = 0\<^sub>R")
 apply (subgoal_tac "x \<le> m") prefer 2 apply (simp add:Nset_def)
 apply (simp add:jointfun_def) apply (simp add:Nset_def) apply assumption
 apply simp
apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  ( a +\<^sub>R -\<^sub>R b) \<star>\<^sub>M h = 0\<^sub>M")
 apply (thin_tac "f \<in> Nset n \<rightarrow> H1")
 apply (thin_tac "s \<in> Nset n \<rightarrow> carrier R")
 apply (thin_tac "linear_combination R M n s f = linear_combination R M m t g")
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M ( a +\<^sub>R -\<^sub>R b) \<star>\<^sub>M h = linear_combination R M (Suc m) (jointfun m t 0 (\<lambda>k\<in>Nset 0. a +\<^sub>R -\<^sub>R b)) (jointfun m g 0 (\<lambda>k\<in>Nset 0. h))")
 apply (thin_tac "t \<in> Nset m \<rightarrow> carrier R")
 apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 = linear_combination R M n s f")
 apply (simp add:bij_to_def) apply (erule conjE)
apply (simp add:inj_on_def)
 apply (rule ballI)+ apply (rule impI)
 apply (case_tac "x = Suc m")
 apply (case_tac "y = Suc m") apply simp
 apply (subgoal_tac "y \<le> m") apply (simp add:jointfun_def sliden_def)
 apply (subgoal_tac "0 \<in> Nset 0") apply simp
 apply (subgoal_tac "y \<in> Nset m")
 apply (frule_tac f = g and A = "Nset m" and B = H1 and x = y in funcset_mem,
                   assumption+) apply simp apply (simp add:Nset_def)
 apply (simp add:Nset_def) apply (simp add:Nset_def)
apply (case_tac "y = Suc m")
 apply (subgoal_tac "x \<le> m") apply (simp add:jointfun_def)
 apply (simp add:sliden_def) apply (subgoal_tac "0 \<in> Nset 0") apply simp
 apply (subgoal_tac "x \<in> Nset m")
 apply (frule_tac f = g and A = "Nset m" and B = "H1" and x = x in funcset_mem,
                      assumption+) apply simp apply (simp add:Nset_def)
 apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (subgoal_tac "x \<in> Nset m") apply (subgoal_tac "y \<in> Nset m")
 apply (thin_tac "y \<in> Nset (Suc m)") apply (thin_tac "x \<in> Nset (Suc m)")
 apply (subgoal_tac "x \<le> m") apply (subgoal_tac "y \<le> m")
 apply (simp add:jointfun_def)
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply (simp add:Nset_def)
 apply (simp add:Nset_def)
apply (thin_tac "-\<^sub>M h2 +\<^sub>M h1 +\<^sub>M  ( a +\<^sub>R -\<^sub>R b) \<star>\<^sub>M h = 0\<^sub>M")
 apply(simp add:linear_combination_def)
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (g j)) m = e\<Sigma> M (\<lambda>j. jointfun m t 0 (\<lambda>k\<in>Nset 0. a +\<^sub>R -\<^sub>R b)j \<star>\<^sub>M (jointfun m g 0 (\<lambda>k\<in>Nset 0. h) j)) m")
 apply (subgoal_tac "( a +\<^sub>R -\<^sub>R b) \<star>\<^sub>M h = jointfun m t 0 (\<lambda>k\<in>Nset 0.  a +\<^sub>R -\<^sub>R b) (Suc m) \<star>\<^sub>M (jointfun m g 0 (\<lambda>k\<in>Nset 0. h) (Suc m))")
 apply simp
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:jointfun_def sliden_def) apply (simp add:Nset_def)
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = e\<Sigma> M (\<lambda>j. t j \<star>\<^sub>M (g j)) m")
apply (rule eSum_eq, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x \<le> m") apply (simp add:jointfun_def)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem)
 apply (simp add:funcset_mem subsetD) apply (simp add:Nset_def)
apply (rule ballI) apply (subgoal_tac "l \<le> m")
 apply (simp add:jointfun_def) apply (simp add:Nset_def)
done

lemma ex_extensionTr:" \<lbrakk>ring R; R module M; R module N; free_generator R M H;  f \<in> H \<rightarrow> carrier N; H1 \<subseteq> H; h \<in> H; h \<notin> H1; g \<in> mHom R (mdl M (fgs R M H1)) N; fgs R M (insert h H1) = fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h}); x \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})\<rbrakk> \<Longrightarrow> \<exists>k1\<in> fgs R M H1. \<exists>k2\<in>fgs R M {h}. x = k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)"
apply (subgoal_tac "\<exists>!y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> y =  g h1 +\<^sub>N (monofun R M N f H h h2)")
apply (subgoal_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> (THE y.
\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g h1 +\<^sub>N (monofun R M N f H h h2)")
prefer 2 apply (rule theI') apply simp
 apply (thin_tac "\<exists>!y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)")
 apply blast
apply (rule ex_ex1I)
 apply (thin_tac "fgs R M (insert h H1) = fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (simp add:sSum_def)
 apply (subgoal_tac "\<forall>h1\<in>fgs R M H1. \<forall>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<longrightarrow> (\<exists>y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2))") apply blast
 apply (thin_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2")
 apply (rule ballI)+ apply (rule impI)
 apply (subgoal_tac "g h1 +\<^sub>N (monofun R M N f H h h2) = g h1 +\<^sub>N (monofun R M N f H h h2)") apply blast apply simp
apply (subgoal_tac "\<forall>h1\<in>fgs R M H1. \<forall>h2\<in>fgs R M {h}. \<forall>k1\<in>fgs R M H1. \<forall>k2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2) \<and> x = k1 +\<^sub>M k2 \<and> ya = g k1 +\<^sub>N (monofun R M N f H h k2) \<longrightarrow> y = ya")
apply blast
 apply (thin_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)")
 apply (thin_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 +\<^sub>M h2 \<and> ya = g h1 +\<^sub>N (monofun R M N f H h h2)")
apply (rule ballI)+ apply (rule impI)+ apply (erule conjE)+
 apply simp
 apply (frule_tac R = R and M = M and N = N and H = H and ?H1.0 = H1 and h = h and ?h1.0 = h1 and ?h2.0 = k1 and ?k1.0 = h2 and ?k2.0 = k2 in sSum_unique, assumption+) apply simp apply assumption+ apply (rule sym) apply assumption
 apply (erule conjE) apply blast
done

lemma monofun_add:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; h \<in> H; x \<in> fgs R M {h}; y \<in> fgs R M {h}\<rbrakk> \<Longrightarrow> monofun R M N f H h (x +\<^sub>M y) = monofun R M N f H h x +\<^sub>N (monofun R M N f H h y)"
apply (subgoal_tac "H \<subseteq> carrier M") prefer 2 apply (simp add:free_generator_def generator_def)
apply (frule_tac R = R and M = M and N = N and h = h and x = x in fgs_single_span, assumption+)
 apply (simp add:subsetD) apply assumption
apply (frule_tac R = R and M = M and N = N and h = h and x = y in fgs_single_span, assumption+)
 apply (simp add:subsetD) apply assumption
apply (subgoal_tac "\<forall>a\<in>carrier R. \<forall>b\<in>carrier R. x = a \<star>\<^sub>M h \<and> y =  b \<star>\<^sub>M h \<longrightarrow>(monofun R M N f H h ( x +\<^sub>M y) = monofun R M N f H h x +\<^sub>N (monofun R M N f H h y))")
apply blast apply (thin_tac "\<exists>a\<in>carrier R. x =  a \<star>\<^sub>M h")
 apply (thin_tac "\<exists>a\<in>carrier R. y =  a \<star>\<^sub>M h")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)
apply simp
apply (subgoal_tac "H \<subseteq> carrier M") prefer 2 apply (simp add:free_generator_def generator_def)
apply (frule_tac A = H and B = "carrier M" and c = h in subsetD, assumption+)
apply (simp add:sprod_distrib1 [THEN sym])
apply (frule ring_is_ag [of "R"])
 apply (frule_tac G = R and x = a and y = b in ag_pOp_closed, assumption+)
 apply (simp add:monofun_mhomTr1)
 apply (frule_tac f = f and A = H and B = "carrier N" and x = h in funcset_mem,
 assumption+)
 apply (simp add:sprod_distrib1)
done

lemma monofun_sprod:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; h \<in> H; x \<in> fgs R M {h}; a \<in> carrier R\<rbrakk> \<Longrightarrow> monofun R M N f H h ( a \<star>\<^sub>M x) = a \<star>\<^sub>N (monofun R M N f H h x)"
apply (subgoal_tac "H \<subseteq> carrier M") prefer 2 apply (simp add:free_generator_def generator_def)
apply (frule_tac R = R and M = M and N = N and h = h and x = x in fgs_single_span, assumption+)
 apply (simp add:subsetD) apply assumption
 apply (subgoal_tac "\<forall>b\<in>carrier R. x = b \<star>\<^sub>M h \<longrightarrow> (monofun R M N f H h ( a \<star>\<^sub>M x) =  a \<star>\<^sub>N (monofun R M N f H h x))")
 apply blast
 apply (thin_tac "\<exists>a\<in>carrier R. x =  a \<star>\<^sub>M h")
apply (rule ballI) apply (rule impI)
 apply simp
 apply (frule_tac R = R and M = M and a = b and m = h in sprod_mem, assumption+) apply (simp add:subsetD)
 apply (frule_tac R1 = R and M1 = M and a1 = a and b1 = b and m1 = h in sprod_assoc [THEN sym], assumption+) apply (simp add:subsetD)
 apply (simp add:sprod_assoc [THEN sym])
 apply (frule_tac R = R and x = a and y = b in ring_tOp_closed, assumption+)
 apply (simp add:monofun_mhomTr1)
 apply (frule_tac f = f and A = H and B = "carrier N" and x = h in funcset_mem,
 assumption+)
apply (simp add:sprod_assoc)
done

lemma ex_extension:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N; H1 \<subseteq> H; h \<in> H - H1; (H1, g) \<in> fsps R M N f H\<rbrakk> \<Longrightarrow> \<exists>k. ((H1 \<union> {h}), k) \<in> fsps R M N f H"
apply (simp add:fsps_def fsp_def)
 apply (erule conjE)+
 apply (frule_tac R1 = R and M1 = M and N1 = N and H1 = H and ?H1.1 = H1 and h1 = h in sSum_eq[THEN sym], assumption+)
 apply simp
 apply (subgoal_tac "(\<lambda>x \<in> (fgs R M (H1 \<union> {h})). (THE y. (\<exists>h1\<in>(fgs R M H1). \<exists>h2\<in>(fgs R M {h}). x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))) \<in> mHom R (mdl M (fgs R M (insert h H1))) N \<and> f h = (\<lambda>x \<in> (fgs R M (H1 \<union> {h})). (THE y. (\<exists>h1\<in>(fgs R M H1). \<exists>h2\<in>(fgs R M {h}). x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))) h \<and> (\<forall>z\<in>H1. g z = (\<lambda>x \<in> (fgs R M (H1 \<union> {h})). (THE y. (\<exists>h1\<in>(fgs R M H1). \<exists>h2\<in>(fgs R M {h}). x = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))) z)")
 apply blast
apply (rule conjI)
 apply (rule mHom_test, assumption+)
 apply (rule mdl_is_module, assumption+)
 apply (simp add:fgs_def) apply (frule sym)
 apply (thin_tac "linear_span R M (carrier R) (insert h H1) =
       linear_span R M (carrier R) H1 \<plusminus>\<^sub>M (linear_span R M (carrier R) {h})")
 apply simp
 apply (rule linear_span_subModule, assumption+)
 apply (simp add:whole_ideal)
 apply (rule subsetI) apply simp apply (case_tac "x = h") apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD) apply (simp add:free_generator_def generator_def)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def) apply assumption
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (subgoal_tac "x \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})") apply simp
apply (frule_tac x = x in ex_extensionTr[of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply (subgoal_tac "\<forall>h1\<in>fgs R M H1. \<forall>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g h1 +\<^sub>N (monofun R M N f H h h2) \<longrightarrow> ((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) \<in> carrier N)") apply blast
 apply (thin_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g h1 +\<^sub>N (monofun R M N f H h h2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (thin_tac "(THE y. \<exists>h1a\<in>fgs R M H1. \<exists>h2a\<in>fgs R M {h}. h1 +\<^sub>M h2 =  h1a +\<^sub>M h2a \<and> y =  g h1a +\<^sub>N (monofun R M N f H h h2a)) = g h1 +\<^sub>N (monofun R M N f H h h2)")
 apply (frule_tac R = R and M = "mdl M (fgs R M H1)" and N = N and f = g and m = h1 in  mHom_mem)
 apply (rule mdl_is_module, assumption+)
 apply (subst fgs_def)
 apply (rule linear_span_subModule, assumption+)
 apply (simp add:whole_ideal) apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule subset_trans, assumption+) apply (simp add:free_generator_def generator_def) apply assumption+ apply (simp add:mdl_def)
apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (rule ag_pOp_closed, assumption+)
 apply (rule monofun_mem, assumption+)
 apply (simp add:mdl_def)
apply (rule conjI)
 apply (simp add:mdl_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (subgoal_tac "m +\<^sub>(mdl M (fgs R M (insert h H1))) n = m +\<^sub>M n")
 prefer 2 apply (simp add:mdl_def) apply simp
 apply (subgoal_tac "m +\<^sub>M n \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})") apply (simp add:mdl_def) apply (fold mdl_def)
 apply (frule_tac x = m in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply (subgoal_tac "\<forall>m1\<in>fgs R M H1. \<forall>m2\<in>fgs R M {h}. m = m1 +\<^sub>M m2 \<and> (THE y. \<exists>h1\<in>fgs R M H1.  \<exists>h2\<in>fgs R M {h}. m = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g m1 +\<^sub>N (monofun R M N f H h m2) \<longrightarrow> ((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m +\<^sub>M n = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) +\<^sub>N (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. n = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))")
 apply blast
 apply (thin_tac "\<exists>k1\<in>fgs R M H1. \<exists>k2\<in>fgs R M {h}. m = k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE) apply simp
 apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m1 +\<^sub>M m2 =  h1 +\<^sub>M h2 \<and> y =  g h1 +\<^sub>N (monofun R M N f H h h2)) = g m1 +\<^sub>N (monofun R M N f H h m2)")
apply (frule_tac x = n in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply (subgoal_tac "\<forall>n1\<in>fgs R M H1. \<forall>n2\<in>fgs R M {h}. n = n1 +\<^sub>M n2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. n = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g n1 +\<^sub>N (monofun R M N f H h n2) \<longrightarrow> ((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m1 +\<^sub>M m2 +\<^sub>M n =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g m1 +\<^sub>N (monofun R M N f H h m2) +\<^sub>N (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. n = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))")
 apply blast
 apply (thin_tac " \<exists>k1\<in>fgs R M H1. \<exists>k2\<in>fgs R M {h}. n = k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1.  \<exists>h2\<in>fgs R M {h}. n =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE) apply simp
 apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. n1 +\<^sub>M n2 = h1 +\<^sub>M h2 \<and>  y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g n1 +\<^sub>N (monofun R M N f H h n2)")
apply (frule_tac x = "m +\<^sub>M n" in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply simp
 apply (subgoal_tac "\<forall>k1\<in>fgs R M H1. \<forall>k2\<in>fgs R M {h}. m +\<^sub>M n =  k1 +\<^sub>M k2 \<and>   (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m +\<^sub>M n =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2) \<longrightarrow> ((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m1 +\<^sub>M m2 +\<^sub>M ( n1 +\<^sub>M n2) =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g m1 +\<^sub>N (monofun R M N f H h m2) +\<^sub>N ( g n1 +\<^sub>N (monofun R M N f H h n2)))")
 apply blast
 apply (thin_tac "\<exists>k1\<in>fgs R M H1. \<exists>k2\<in>fgs R M {h}. m +\<^sub>M n =  k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m +\<^sub>M n =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE) apply simp
 apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. k1 +\<^sub>M k2 = h1 +\<^sub>M h2 \<and> y =  g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
apply (frule whole_ideal [of "R"])
apply (frule_tac R = R and A = "carrier R" and M = M and H = "{h}" in lin_span_sub_carrier, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply simp apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:fgs_def)
 apply (frule_tac A = "linear_span R M (carrier R) {h}" and B = "carrier M" and c = m2 in subsetD, assumption+)
 apply (frule_tac A = "linear_span R M (carrier R) {h}" and B = "carrier M" and c = n2 in subsetD, assumption+)
apply (frule_tac R = R and A = "carrier R" and M = M and H = H1 in lin_span_sub_carrier, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (subgoal_tac "m1 +\<^sub>M n1 \<in> linear_span R M (carrier R) H1")
 prefer 2 apply (rule_tac R = R and M = M and H = "linear_span R M (carrier R)  H1" and h = m1 and k = n1 in submodule_pOp_closed, assumption+)
 apply (rule linear_span_subModule, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def) apply assumption+
 apply (subgoal_tac "m2 +\<^sub>M n2 \<in> linear_span R M (carrier R) {h}")
 prefer 2 apply (rule_tac R = R and M = M and H = "linear_span R M (carrier R)  {h}" and h = m2 and k = n2 in submodule_pOp_closed, assumption+)
 apply (rule linear_span_subModule, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply simp apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def) apply assumption+
 apply (fold fgs_def)
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac A = "fgs R M H1" and B = "carrier M" and c = m1 in subsetD, assumption+)
 apply (frule_tac A = "fgs R M H1" and B = "carrier M" and c = n1 in subsetD, assumption+)
 apply (simp add:pOp_assocTr41 [THEN sym])
 apply (simp add:pOp_assocTr42)
 apply (frule_tac G = M and x = m2 and y = n1 in ag_pOp_commute, assumption+)
 apply simp
 apply (simp add:pOp_assocTr43 [THEN sym])
 apply (frule_tac ?h1.0 = "m1 +\<^sub>M n1" and ?h2.0 = k1  and ?k1.0 = "m2 +\<^sub>M n2" and ?k2.0 = k2 in sSum_unique[of "R" "M" "N" "H" "H1" "h"], assumption+)
 apply simp apply assumption+ apply (erule conjE)+
 apply (rotate_tac -2) apply (frule sym) apply (thin_tac "m1 +\<^sub>M n1 = k1")
 apply (frule sym) apply (thin_tac "m2 +\<^sub>M n2 = k2")
 apply (thin_tac "m2 +\<^sub>M n1 =  n1 +\<^sub>M m2")
 apply (thin_tac "m1 +\<^sub>M m2 \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
apply (subgoal_tac "g k1 = g (m1 +\<^sub>M n1)") prefer 2
 apply (thin_tac "n1 +\<^sub>M n2 \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (thin_tac "k1 +\<^sub>M k2 \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (thin_tac "k1 \<in> fgs R M H1")
 apply (thin_tac "k2 \<in> fgs R M {h}")
 apply (thin_tac "m1 +\<^sub>M n1 +\<^sub>M ( m2 +\<^sub>M n2) =  k1 +\<^sub>M k2")
 apply (thin_tac "\<forall>z\<in>H1. f z = g z")
apply simp
 apply (thin_tac "n1 +\<^sub>M n2 \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (thin_tac "k1 +\<^sub>M k2 \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (thin_tac "k1 =  m1 +\<^sub>M n1") apply simp
 apply (thin_tac "k2 = m2 +\<^sub>M n2") apply (thin_tac " g k1 = g ( m1 +\<^sub>M n1)")
 apply (subgoal_tac "R module (mdl M (fgs R M H1))")
 prefer 2 apply (rule mdl_is_module, assumption+)
 apply (simp add:fgs_def) apply (rule linear_span_subModule, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (subgoal_tac "m1 \<in> carrier (mdl M (fgs R M H1))")
 prefer 2 apply (simp add:mdl_def)
 apply (subgoal_tac "n1 \<in> carrier (mdl M (fgs R M H1))")
 prefer 2 apply (simp add:mdl_def)
 apply (frule_tac m = m1 and n = n1 in mHom_add [of "R" "mdl M (fgs R M H1)" "N" "g"], assumption+)
 apply (subgoal_tac "m1 +\<^sub>(mdl M (fgs R M H1)) n1 = m1 +\<^sub>M n1")
 prefer 2 apply (simp add:mdl_def) apply simp
 apply (simp add:monofun_add)
 apply (frule_tac R = R and M = M and N = N and h = h and H = H and x = m2 and f = f in monofun_mem, assumption+)
 apply (frule_tac R = R and M = M and N = N and h = h and H = H and x = n2 and f = f in monofun_mem, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M H1)" and N = N and f = g and m = m1 in mHom_mem, assumption+)
 apply (frule_tac R = R and M = "mdl M (fgs R M H1)" and N = N and f = g and m = n1 in mHom_mem, assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simplesubst pOp_assocTr41 [THEN sym], assumption+)
 apply (subst pOp_assocTr42, assumption+)
 apply (frule_tac G = N and x = "monofun R M N f H h m2" and y = "g n1" in ag_pOp_commute, assumption+) apply simp
 apply (subst pOp_assocTr43 [THEN sym], assumption+) apply simp
apply (frule sym) apply (thin_tac "fgs R M (insert h H1) = fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})") apply simp
apply (thin_tac "g \<in> mHom R (mdl M (fgs R M H1)) N")
 apply (thin_tac "m +\<^sub>(mdl M (fgs R M (insert h H1))) n = m +\<^sub>M n")
 apply (thin_tac "fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h}) = fgs R M (insert h H1)")
 apply (simp add:mdl_def)
 apply (simp add:fgs_def)
 apply (frule_tac R = R and M = M and A = "carrier R" and H = "insert h H1" and a = m and b = n in linear_span_tOp_closed, assumption+)
 apply (simp add:whole_ideal)
 apply (rule subsetI) apply simp apply (subgoal_tac "H \<subseteq> carrier M")
 apply (case_tac "x = h")
 apply (simp add:subsetD) apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+) apply (simp add:subsetD) apply (simp add:free_generator_def generator_def)
 apply assumption+
apply (rule ballI)+
 apply (subgoal_tac "a \<star>\<^sub>(mdl M (fgs R M (insert h H1))) m = a \<star>\<^sub>M m")
 prefer 2 apply (simp add:mdl_def)
 apply (frule sym) apply (thin_tac "fgs R M (H1 \<union> {h}) = fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply simp apply (thin_tac "a \<star>\<^sub>(mdl M (fgs R M (insert h H1))) m = a \<star>\<^sub>M m")
 apply (subgoal_tac "m \<in> fgs R M (insert h H1)")
 apply (subgoal_tac "a \<star>\<^sub>M m \<in> fgs R M (insert h H1)")
 apply simp
 apply (frule sym) apply (thin_tac "fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h}) = fgs R M (insert h H1)")
 apply simp
 apply (frule_tac x = m in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply (subgoal_tac "\<forall>m1\<in>fgs R M H1. \<forall>m2\<in>fgs R M {h}. m = m1 +\<^sub>M m2 \<and> (THE y.  \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g m1 +\<^sub>N (monofun R M N f H h m2) \<longrightarrow> ((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. a \<star>\<^sub>M m = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = a \<star>\<^sub>N ((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m =  h1 +\<^sub>M h2 \<and> y =  g h1 +\<^sub>N (monofun R M N f H h h2))))")
 apply blast
 apply (thin_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m = h1 +\<^sub>M h2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g h1 +\<^sub>N (monofun R M N f H h h2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE) apply simp
 apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. m1 +\<^sub>M m2 =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g m1 +\<^sub>N (monofun R M N f H h m2)")
apply (frule whole_ideal [of "R"])
apply (frule_tac R = R and A = "carrier R" and M = M and H = H1 in lin_span_sub_carrier, assumption+)
apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac x = "a \<star>\<^sub>M ( m1 +\<^sub>M m2)" in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply (subgoal_tac "\<forall>k1\<in>fgs R M H1. \<forall>k2\<in>fgs R M {h}. a \<star>\<^sub>M (m1 +\<^sub>M m2) = k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. a \<star>\<^sub>M (m1 +\<^sub>M m2) = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2) \<longrightarrow>((THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. a \<star>\<^sub>M (m1 +\<^sub>M m2) = h1 +\<^sub>M h2 \<and> y =  g h1 +\<^sub>N (monofun R M N f H h h2)) = a \<star>\<^sub>N (g m1 +\<^sub>N (monofun R M N f H h m2)))")
 apply blast
 apply (thin_tac "\<exists>k1\<in>fgs R M H1. \<exists>k2\<in>fgs R M {h}. a \<star>\<^sub>M (m1 +\<^sub>M m2) = k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. a \<star>\<^sub>M (m1 +\<^sub>M m2) = h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)+
 apply simp
 apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. k1 +\<^sub>M k2 =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (subgoal_tac "m1 \<in> carrier M") prefer 2 apply (simp add:fgs_def subsetD)
 apply (subgoal_tac "m2 \<in> carrier M") prefer 2
 apply (frule_tac R = R and A = "carrier R" and M = M and H = "{h}" in lin_span_sub_carrier, assumption+)
apply (subgoal_tac "H \<subseteq> carrier M") apply simp apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:fgs_def subsetD)
 apply (simp add:sprod_distrib2)
 apply (thin_tac "m1 +\<^sub>M m2 \<in> carrier (mdl M (fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})))")
 apply (subgoal_tac "a \<star>\<^sub>M m1 \<in> fgs R M H1")
 apply (subgoal_tac "a \<star>\<^sub>M m2 \<in> fgs R M {h}")
apply (frule_tac R = R and M = M and N = N and H = H and ?H1.0 = H1 and h = h and ?h1.0 = "a \<star>\<^sub>M m1" and ?h2.0 = k1 and ?k1.0 = "a \<star>\<^sub>M m2" and ?k2.0 = k2 in sSum_unique, assumption+)
 apply simp apply assumption+ apply (erule conjE)
 apply (rotate_tac -2) apply (frule sym) apply (thin_tac "a \<star>\<^sub>M m1 = k1")
 apply (frule sym) apply (thin_tac "a \<star>\<^sub>M m2 = k2")
 apply (thin_tac " m1 +\<^sub>M m2 \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (thin_tac "fgs R M (insert h H1) = fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (thin_tac "a \<star>\<^sub>M m1 +\<^sub>M  a \<star>\<^sub>M m2 =  k1 +\<^sub>M k2") apply simp
apply (subgoal_tac "R module (mdl M (fgs R M H1))")
 apply (subgoal_tac "m1 \<in> carrier (mdl M (fgs R M H1))")
 apply (frule_tac R = R and M = "mdl M (fgs R M H1)" and N = N and m = m1 and f = g and a = a in mHom_lin, assumption+)
 apply (subgoal_tac " a \<star>\<^sub>(mdl M (fgs R M H1)) m1 = a \<star>\<^sub>M m1") prefer 2 apply (simp add:mdl_def) apply simp
 apply (thin_tac "a \<star>\<^sub>(mdl M (fgs R M H1)) m1 =  a \<star>\<^sub>M m1")
 apply (thin_tac "g (a \<star>\<^sub>M m1) = a \<star>\<^sub>N (g m1)")
 apply (frule_tac R = R and M = "mdl M (fgs R M H1)" and N = N and f = g and m = m1 in mHom_mem, assumption+)
 apply (frule_tac R = R and M = M and N = N and h = h and H = H and x = "a \<star>\<^sub>M m2" in monofun_mem, assumption+)
 apply (simp add:monofun_sprod)
 apply (frule_tac R = R and M = M and N = N and h = h and H = H and x = m2 in monofun_mem, assumption+)
 apply (simp add:sprod_distrib2)
 apply (simp add:mdl_def)
 apply (rule mdl_is_module, assumption+) apply (simp add:fgs_def)
 apply (rule linear_span_subModule, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (simp add:fgs_def)
 apply (rule submodule_sprod_closed, assumption+)
 apply (rule linear_span_subModule, assumption+) apply (subgoal_tac "H \<subseteq> carrier M")
 apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+) apply (simp add:subsetD) apply (simp add:free_generator_def generator_def)
 apply assumption apply (simp add:fgs_def)
 apply (simp add:fgs_def) apply (rule linear_span_sprod_closed, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def) apply assumption
 apply assumption
 apply (thin_tac "fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h}) = fgs R M (insert h H1)")
 apply (frule whole_ideal [of "R"])
 apply (frule_tac r = a and x = m in linear_span_sprod_closed [of "R" "M" "carrier R" "insert h H1"], assumption+)
 apply (rule subsetI) apply (subgoal_tac "H \<subseteq> carrier M") apply simp
 apply (case_tac "x = h")
 apply (rule subsetD, assumption+) apply simp apply simp
 apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+) apply (simp add:subsetD) apply (simp add:free_generator_def generator_def) apply assumption apply (simp add:fgs_def) apply (simp add:fgs_def)
 apply (simp add:mdl_def)
 apply (subgoal_tac "h \<in> fgs R M (H1 \<union> {h})")
 prefer 2 apply (thin_tac "fgs R M (H1 \<union> {h}) = fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (simp add:fgs_def)
 apply (frule_tac elem_linear_span1 [of "R" "M" "insert h H1"], assumption+)
 apply (rule subsetI) apply simp apply (case_tac "x = h") apply simp
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def) apply simp
 apply (subgoal_tac "H \<subseteq> carrier M") apply (frule_tac A = H1 and B = H and C = "carrier M" in subset_trans, assumption+) apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply (subgoal_tac "h \<in> insert h H1") apply (simp add:subsetD)
 apply simp apply simp
apply (rule conjI)
apply (frule_tac x = h in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"],
                    assumption+)
 apply (subgoal_tac "\<forall>k1\<in>fgs R M H1. \<forall>k2\<in>fgs R M {h}. h =  k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. h =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2) \<longrightarrow> (f h = (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. h =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))")
 apply blast
 apply (thin_tac "\<exists>k1\<in>fgs R M H1. \<exists>k2\<in>fgs R M {h}. h =  k1 +\<^sub>M k2 \<and> (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. h =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M { k1 +\<^sub>M k2}.
 k1 +\<^sub>M k2 =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H (k1 +\<^sub>M k2) h2)) =     g k1 +\<^sub>N (monofun R M N f H (k1 +\<^sub>M k2) k2)")
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "h =  k1 +\<^sub>M k2")
 apply simp
 apply (subgoal_tac "h \<in> fgs R M {h}") apply (thin_tac "h \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
 apply (subgoal_tac "0\<^sub>M \<in> fgs R M H1")
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (frule_tac A = H and B = "carrier M" and c = h in subsetD, assumption+)
 apply (frule_tac x = h in ag_l_zero[of "M"], assumption+)
 apply (subgoal_tac "k1 +\<^sub>M k2 = 0\<^sub>M +\<^sub>M h") prefer 2 apply simp
 apply (thin_tac "k1 +\<^sub>M k2 = h") apply (thin_tac "0\<^sub>M +\<^sub>M h = h")
apply (frule_tac ?h1.0= k1 and ?h2.0 = "0\<^sub>M" and ?k1.0 = k2 and ?k2.0 = h in sSum_unique [of "R" "M" "N" "H" "H1" "h"], assumption+)
 apply simp apply assumption+ apply (thin_tac "k1 +\<^sub>M k2 =  0\<^sub>M +\<^sub>M h")
 apply (erule conjE)+ apply simp
 apply (subgoal_tac "R module (mdl M (fgs R M H1))")
 apply (frule_tac mHom_0 [of "R" "mdl M (fgs R M H1)" "N" "g"], assumption+)
 apply (simp add:mdl_def) apply (fold mdl_def)
 apply (frule_tac f = f and A = H and B = "carrier N" and x = h in funcset_mem,
          assumption+)
 apply (simp add:monofun_eq_f)
 apply (frule module_is_ag[of "R" "N"], assumption+)
 apply (simp add:ag_l_zero[THEN sym])
 apply (rule mdl_is_module, assumption+) apply (simp add:fgs_def)
 apply (rule linear_span_subModule, assumption+)
 apply (simp add:whole_ideal) apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule subset_trans, assumption+) apply (simp add:free_generator_def generator_def)
 apply (simp add:fgs_def)
 apply (rule linear_span_inc_0, assumption+) apply (simp add:whole_ideal)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
apply (simp add:fgs_def)
 apply (frule_tac R = R and M = M and H = "{h}" in elem_linear_span1, assumption+) apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def) apply simp
 apply (thin_tac "h \<in> fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})")
apply (rule ballI)
 apply (frule_tac R = R and M = M and H = H1 in elem_linear_span1, assumption+) apply (subgoal_tac "H \<subseteq> carrier M") apply (rule subset_trans, assumption+)
 apply (simp add:free_generator_def generator_def)
 apply (frule_tac A = H1 and B = "linear_span R M (carrier R) H1" and c = z in subsetD, assumption+)
 apply (frule whole_ideal [of "R"])
 apply (frule_tac linear_span_subModule[of "R" "M" "carrier R" "H1"], assumption+)
apply (subgoal_tac "H \<subseteq> carrier M")
 apply (rule subset_trans, assumption+) apply (simp add:free_generator_def generator_def)
 apply (frule_tac linear_span_subModule[of "R" "M" "carrier R" "{h}"], assumption+)
apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def) apply (fold fgs_def)
 apply (frule sSum_cont_H [of "R" "M" "fgs R M H1" "fgs R M {h}"], assumption+) apply (frule_tac A = "fgs R M H1" and B = "fgs R M H1 \<plusminus>\<^sub>M (fgs R M {h})" and c = z in subsetD, assumption+) apply simp
 apply (simp add:submodule_def [of _ _ "fgs R M H1"]) apply (frule conj_1)
 apply (fold submodule_def) apply (frule_tac A = "fgs R M H1" and B = "carrier M" and c = z in subsetD, assumption+)
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (frule_tac G1 = M and t = z in ag_r_zero [THEN sym], assumption+)
 apply (frule_tac x = z in ex_extensionTr [of "R" "M" "N" "H" "f" "H1" "h" "g"], assumption+)
 apply (subgoal_tac "\<forall>k1\<in>fgs R M H1. \<forall>k2\<in>fgs R M {h}. z = k1 +\<^sub>M k2 \<and> (THE y.  \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. z =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2) \<longrightarrow> (g z = (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. z =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)))")
 apply blast
 apply (thin_tac "\<exists>k1\<in>fgs R M H1. \<exists>k2\<in>fgs R M {h}. z = k1 +\<^sub>M k2 \<and> (THE y.  \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. z =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.  k1 +\<^sub>M k2 =  h1 +\<^sub>M h2 \<and> y = g h1 +\<^sub>N (monofun R M N f H h h2)) = g k1 +\<^sub>N (monofun R M N f H h k2)")
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "z =  k1 +\<^sub>M k2")
 apply simp
 apply (subgoal_tac "k1 +\<^sub>M k2 =  z +\<^sub>M 0\<^sub>M") prefer 2 apply simp
 apply (thin_tac " z =  z +\<^sub>M 0\<^sub>M") apply (thin_tac "k1 +\<^sub>M k2 = z")
 apply (frule_tac ?h1.0 = k1 and ?h2.0 = z and ?k1.0 = k2 and ?k2.0 = "0\<^sub>M" in sSum_unique[of "R" "M" "N" "H" "H1" "h"], assumption+)
 apply simp apply assumption+ apply (simp add:fgs_def)
 apply (rule linear_span_inc_0, assumption+)
 apply (subgoal_tac "H \<subseteq> carrier M") apply (simp add:subsetD)
 apply (simp add:free_generator_def generator_def)
 apply assumption apply (thin_tac "k1 +\<^sub>M k2 =  z +\<^sub>M 0\<^sub>M")
apply (erule conjE) apply simp
 apply (subgoal_tac "H \<subseteq> carrier M")
 apply (frule_tac A = H and B = "carrier M" and c = h in subsetD, assumption+)
 apply (frule_tac R1 = R and M1 = M and m1 = h in sprod_0_m [THEN sym],
                                                              assumption+)
 apply simp
 apply (frule monofun_sprod [of "R" "M" "N" "H" "f" "h" "h" "0\<^sub>R"], assumption+)
 apply (subst fgs_def)
 apply (frule elem_linear_span1 [of "R" "M" "{h}"], assumption+)
 apply (simp add:subsetD) apply simp
 apply (frule ring_is_ag[of "R"])
 apply (simp add:ag_inc_zero) apply simp
 apply (simp add:monofun_eq_f)
 apply (frule funcset_mem [of "f" "H" "carrier N" "h"], assumption+)
 apply (frule sprod_0_m[of "R" "N" "f h"], assumption+) apply simp
apply (frule module_is_ag[of "R" "N"], assumption+)
 apply (rule ag_r_zero [THEN sym], assumption+)
 apply (subgoal_tac "z \<in> carrier (mdl M (fgs R M H1))")
 apply (rule mHom_mem[of "R" "mdl M (fgs R M H1)" "N" "g"], assumption+)
 apply (rule mdl_is_module, assumption+)
 apply (simp add:mdl_def)
 apply (simp add:free_generator_def generator_def)
done

lemma exist_extension_mhom:"\<lbrakk>ring R; R module M; R module N; free_generator R M H; f \<in> H \<rightarrow> carrier N\<rbrakk> \<Longrightarrow> \<exists>g\<in>mHom R M N. \<forall>x\<in>H. g x = f x"
apply (frule_tac R = R and M = M and N = N and H = H and f = f in od_fm_fun_inductive, assumption+)
apply (frule_tac D = "od_fm_fun R M N f H" in g_Zorn_lemma3)
apply (subgoal_tac "\<forall>m\<in>carrier (od_fm_fun R M N f H). maximal\<^sub>(od_fm_fun R M N f H) m \<longrightarrow> (\<exists>g\<in>mHom R M N. \<forall>x\<in>H. g x = f x)")
apply blast apply (thin_tac "\<exists>m\<in>carrier (od_fm_fun R M N f H). maximal\<^sub>(od_fm_fun R M N f H) m")
apply (rule ballI) apply (rule impI)
 apply (thin_tac "inductive_set (od_fm_fun R M N f H)")
 apply (simp add:maximal_element_def)
 apply (simp add:od_fm_fun_def)
apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "fst m = H")
 apply (thin_tac "\<forall>b\<in>fsps R M N f H. fst m \<subseteq> fst b \<longrightarrow> m = b")
 apply (subgoal_tac "(fst m, snd m) \<in> fsps R M N f H") prefer 2
 apply (thin_tac "fst m = H")  apply simp
 apply (subgoal_tac "fsp R M N f H (fst m) (snd m)") prefer 2
 apply (unfold fsps_def) apply blast apply (fold fsps_def)
 apply (thin_tac "(fst m, snd m) \<in> fsps R M N f H")
 apply (subgoal_tac "generator R M H") prefer 2 apply (simp add:free_generator_def)
 apply (simp add:generator_def) apply (erule conjE)
 apply (case_tac "H = {}") apply simp
 apply (simp add:linear_span_def)
 apply (frule_tac R = R and M = M and N = N in mHom_ex_one, assumption+)
 apply (frule_tac x = "mzeromap M N" and A = "mHom R M N" in nonempty)
 apply simp
apply (simp add:fsp_def) apply (erule conjE)
apply (subgoal_tac "snd m \<in> mHom R M N") apply blast
 apply (thin_tac "\<forall>z\<in>H. f z = snd m z")
 apply (thin_tac "\<forall>g\<in>mHom R M N. \<exists>x\<in>H. g x \<noteq> snd m x")
 apply (rule mHom_test, assumption+)
 apply (simp add:mHom_def aHom_def) apply (erule conjE)+
 apply (subgoal_tac "carrier (mdl M (fgs R M H)) = carrier M") apply simp
 apply (simp add:mdl_def)
 apply (simp add:mdl_def fgs_def)
apply (thin_tac "\<forall>g\<in>mHom R M N. \<exists>x\<in>H. g x \<noteq> f x")
 apply (subgoal_tac "(fst m, snd m) \<in> fsps R M N f H") prefer 2
  apply simp
  apply (subgoal_tac "fsp R M N f H (fst m) (snd m)") prefer 2
  apply (unfold fsps_def) apply blast apply (fold fsps_def)
  apply (thin_tac "(fst m, snd m) \<in> fsps R M N f H")
 apply (subgoal_tac "(fst m) \<subseteq> H") prefer 2 apply (simp add:fsps_def fsp_def)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "\<exists>h\<in>H. h \<notin> (fst m)") prefer 2 apply blast
 apply (subgoal_tac "\<forall>h\<in>H. h \<notin> fst m \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>h\<in>H. h \<notin> fst m") apply (rule ballI) apply (rule impI)
apply (frule_tac ?H1.0 = "fst m" and h = h in sSum_eq [of "R" "M" "N" "H"],
                                assumption+) apply simp
apply (frule_tac ?H1.0 = "fst m" and h = h and g = "snd m" in ex_extension [of "R" "M" "N" "H" "f"], assumption+)
 apply simp apply (simp add:fsps_def)
 apply (subgoal_tac "\<forall>k. (fst m \<union> {h}, k) \<in> fsps R M N f H \<longrightarrow> False")
 apply blast apply (thin_tac "\<exists>k. (fst m \<union> {h}, k) \<in> fsps R M N f H")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "fst m \<subseteq> fst (fst m \<union> {h}, k) \<longrightarrow> m = (fst m \<union> {h}, k)")
 prefer 2 apply blast
 apply (thin_tac "\<forall>b\<in>fsps R M N f H. fst m \<subseteq> fst b \<longrightarrow> m = b")
 apply simp
apply (subgoal_tac "fst m \<subseteq> insert h (fst m)")
 apply simp apply (subgoal_tac "fst m \<noteq> insert h (fst m)")
 apply (subgoal_tac "(fst m, snd m) = (insert h (fst m), k)")
 prefer 2 apply simp apply (thin_tac "m = (insert h (fst m), k)")
 apply blast apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "h \<in> fst m") apply blast apply (thin_tac "h \<notin> fst m")
 apply (thin_tac "fsp R M N f H (fst m) (snd m)")
 apply (thin_tac "fst m \<subseteq> H") apply (thin_tac "fgs R M (fst m) \<plusminus>\<^sub>M (fgs R M {h}) = fgs R M (fst m)")
 apply (thin_tac "m = (fst m, k)") apply (frule sym)
 apply (thin_tac "fst m = insert h (fst m)")
 apply (rule_tac A = "insert h (fst m)" and B = "fst m" and a = h in eq_set_inc)
 apply (thin_tac "insert h (fst m) = fst m") apply simp apply assumption
apply (rule subsetI) apply simp
done

section "6. Nakayama lemma"

constdefs
 Gwn::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, nat]
                                                  \<Rightarrow> bool"
  "Gwn R M j == \<exists>H. finite_generator R M H \<and> j = card H"

lemma NAKTr1:"\<lbrakk>ring R; R module M; M fgover R\<rbrakk>
\<Longrightarrow> \<exists>H. finite_generator R M H \<and> (LEAST j. \<exists>L. finite_generator R M L \<and> j = card L) = card H"
apply (simp add:fGOver_def)
 apply (subgoal_tac "\<forall>H. finite_generator R M H \<longrightarrow> (\<exists>H. finite_generator R M H \<and> (LEAST j. \<exists>L. finite_generator R M L \<and> j = card L) = card H)")
 apply blast apply (thin_tac "\<exists>H. finite_generator R M H")
 apply (rule allI) apply (rule impI)
apply (rule LeastI)
apply (rule_tac x = H in exI) apply simp
done

lemma NAKTr2:"\<lbrakk>ring R; R module M; Gwn R M j; k < (LEAST j. Gwn R M j)\<rbrakk> \<Longrightarrow> \<not> Gwn R M k"
apply (rule not_less_Least, assumption+)
done

lemma NAKTr3:"\<lbrakk>ring R; R module M; M fgover R; H \<subseteq> carrier M; finite H;
card H < (LEAST j. \<exists>L. finite_generator R M L \<and> j = card L)\<rbrakk> \<Longrightarrow> \<not> finite_generator R M H"
apply (simp add: fGOver_def)
apply (subgoal_tac "\<forall>H1. finite_generator R M H1 \<longrightarrow> (\<not> finite_generator R M H)") apply blast apply (thin_tac "\<exists>H. finite_generator R M H")
apply (rule allI) apply (rule impI)
apply (frule_tac j = "card H1" and k = "card H" in NAKTr2 [of "R" "M"],
                                       assumption+)
 apply (simp add:Gwn_def) apply blast
 apply (simp add:Gwn_def)
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "Gwn R M (card H)") apply simp
 apply (thin_tac "\<not> Gwn R M (card H)")
apply (simp add:Gwn_def)
 apply (thin_tac "finite_generator R M H1")
 apply (rule_tac x = H in exI) apply simp
done

lemma finite_gen_over_ideal:"\<lbrakk>ring R; R module M; ideal R A; h \<in> Nset n \<rightarrow>
 carrier M; generator R M (h ` Nset n); A \<odot>\<^sub>R M = carrier M; m \<in> carrier M \<rbrakk>
 \<Longrightarrow>  \<exists>s\<in>Nset n \<rightarrow> A. m = linear_combination R M n s h"
apply (frule lin_span_closed3[of "R" "M" "A" "h ` Nset n"], assumption+)
apply (subgoal_tac "m \<in> linear_span R M A (h ` Nset n)")
 prefer 2 apply simp
 apply (thin_tac "linear_span R M A (h ` Nset n) = carrier M")
 apply (simp add:linear_span_def) apply (simp add:Nset_nonempty)
apply auto
apply (simp add:finite_lin_span)
done

lemma NAKTr4:" \<lbrakk>ring R; R module M; ideal R A; h \<in> Nset k \<rightarrow> carrier M; 0 < k;
 h ` Nset k \<subseteq> carrier M; s \<in> Nset k \<rightarrow> A; h k = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) +\<^sub>M (s k \<star>\<^sub>M (h k))\<rbrakk> \<Longrightarrow> (1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k) = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0)"
apply (frule module_is_ag, assumption+)
apply (subgoal_tac "h k \<in> carrier M")
apply (subgoal_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) \<in> carrier M")
apply (subgoal_tac "s k \<star>\<^sub>M (h k) \<in> carrier M")
apply (subgoal_tac "-\<^sub>M (s k \<star>\<^sub>M (h k)) \<in> carrier M")
apply (frule_tac a = "h k" and b = "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) +\<^sub>M (s k \<star>\<^sub>M (h k))" and c = "-\<^sub>M (s k \<star>\<^sub>M (h k))" in ag_pOp_add_r [of "M"], assumption+)
apply (rule ag_pOp_closed, assumption+)
apply (thin_tac "h k = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) +\<^sub>M (s k \<star>\<^sub>M (h k))")
apply (frule_tac x = "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0)" in ag_pOp_assoc [of "M"  _ "s k \<star>\<^sub>M (h k)" "-\<^sub>M (s k \<star>\<^sub>M (h k))"], assumption+)
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) +\<^sub>M  (s k \<star>\<^sub>M (h k)) +\<^sub>M
 (-\<^sub>M (s k \<star>\<^sub>M (h k))) = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) +\<^sub>M
 ((s k \<star>\<^sub>M (h k)) +\<^sub>M (-\<^sub>M (s k \<star>\<^sub>M (h k))))")
 apply (simp add:ag_r_inv1)
 apply (simp add:ag_r_zero)
apply (subgoal_tac "h k +\<^sub>M (-\<^sub>M (s k \<star>\<^sub>M (h k))) = (1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k)") apply simp
 apply (subst sprod_distrib1, assumption+) apply (simp add:ring_one)
 apply (frule ring_is_ag [of "R"])
 apply (rule ag_mOp_closed, assumption+)
apply (insert n_in_Nsetn [of "k"]) apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem)
 apply (subst  sprod_minus_am1, assumption+)
 apply (simp add:funcset_mem ideal_subset) apply (simp add:funcset_mem)
apply (simp add:sprod_one)
 apply (rule ag_mOp_closed, assumption+)
apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
  apply (simp add:funcset_mem)
apply (rule_tac R = M and f = "\<lambda>j. s j \<star>\<^sub>M (h j)" and n = k and
   i = "k - Suc 0" in eSum_mem, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+) apply (simp add:funcset_mem ideal_subset)
 apply (simp add:funcset_mem) apply (simp add:Nset_def)
apply (simp add:funcset_mem)
done

lemma NAKTr5:"\<lbrakk>ring R; \<not> zeroring R; R module M; ideal R A; A \<subseteq> J_rad R; A \<odot>\<^sub>R M = carrier M; finite_generator R M H; card H = Suc k; 0 < k\<rbrakk> \<Longrightarrow> \<exists>h \<in> Nset k \<rightarrow> carrier M. H = h ` (Nset k) \<and>  h k \<in> linear_span R M A (h ` Nset (k - Suc 0))"
apply (insert Nset2_finiteTr [of "k"])
 apply (subgoal_tac "\<exists>h. h \<in> Nset k \<rightarrow> H \<and> surj_to h (Nset k) H")
 prefer 2
 apply (subgoal_tac "finite H")
 apply blast apply (simp add:finite_generator_def)
 apply (thin_tac " \<forall>A. finite A \<and> card A = Suc k \<longrightarrow>
           (\<exists>f. f \<in> Nset k \<rightarrow> A \<and> surj_to f (Nset k) A)")
 apply (subgoal_tac "\<forall>h. h \<in> Nset k \<rightarrow> H \<and> surj_to h (Nset k) H \<longrightarrow>
 (\<exists>h\<in>Nset k \<rightarrow> carrier M.
          H = h ` Nset k \<and> h k \<in> linear_span R M A (h ` Nset (k - Suc 0)))")
 apply blast
 apply (thin_tac "\<exists>h. h \<in> Nset k \<rightarrow> H \<and> surj_to h (Nset k) H")
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (simp add:surj_to_def) apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "h ` Nset k = H")
apply (frule_tac f = h and A = "Nset k" and B = "H" and x = k in funcset_mem)
 apply (simp add:n_in_Nsetn)
 apply (simp add:finite_generator_def) apply (erule conjE)+
 apply (simp add:generator_def) apply (erule conjE)
 apply (frule_tac A = "h ` Nset k" and B = "carrier M" and c = "h k" in
   subsetD, assumption+)
 apply (frule_tac h = h and n = k and m = "h k" in finite_gen_over_ideal [of
 "R" "M" "A"], assumption+)
 apply (rule extend_fun, assumption+) apply (simp add:generator_def)
 apply assumption+
apply (subgoal_tac "\<forall>s\<in>Nset k \<rightarrow> A. h k = linear_combination R M k s h \<longrightarrow>
 (\<exists>ha\<in>Nset k \<rightarrow> carrier M. h ` Nset k = ha ` Nset k \<and>
              ha k \<in> linear_span R M A (ha ` Nset (k - Suc 0)))")
 apply (thin_tac " A \<odot>\<^sub>R M = carrier M")
 apply (thin_tac "card (h ` Nset k) = Suc k")
 apply (thin_tac "h \<in> Nset k \<rightarrow> h ` Nset k")
 apply (thin_tac "H = h ` Nset k")
 apply (thin_tac "h k \<in> h ` Nset k")
 apply (thin_tac "finite (h ` Nset k)")
 apply (thin_tac "h ` Nset k \<subseteq> carrier M")
 apply (thin_tac "linear_span R M (carrier R) (h ` Nset k) = carrier M")
 apply (thin_tac "h k \<in> carrier M")
 apply blast
 apply (thin_tac "\<exists>s\<in>Nset k \<rightarrow> A. h k = linear_combination R M k s h")
apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "h k = linear_combination R M (Suc (k - Suc 0)) s h")
 apply (thin_tac "h k = linear_combination R M k s h")
 apply (thin_tac "h k \<in> h ` Nset k")
 apply (thin_tac "h k \<in> carrier M")
prefer 2 apply simp
 apply (simp del:Suc_pred add:linear_combination_def) apply simp
 apply (frule_tac f = h and A = "Nset k" and B = "h ` Nset k" and
 ?B1.0 = "carrier M" in extend_fun, assumption+)
apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule NAKTr4, assumption+)
 apply (frule_tac x = "s k" in J_rad_unit, assumption+)
 apply (insert n_in_Nsetn [of "k"])
 apply (simp add:funcset_mem subsetD)
 apply (frule ring_one [of "R"])
apply (subgoal_tac "unit R (1\<^sub>R +\<^sub>R ((-\<^sub>R (s k)) \<cdot>\<^sub>R (1\<^sub>R)))")
 prefer 2 apply simp
 apply (thin_tac "\<forall>y. y \<in> carrier R \<longrightarrow> unit R (1\<^sub>R +\<^sub>R ((-\<^sub>R (s k)) \<cdot>\<^sub>R y))")
 apply (subgoal_tac "(-\<^sub>R (s k)) \<in> carrier R")
 apply (simp add:ring_r_one)
 apply (simp add:unit_def)
prefer 2
 apply (frule ring_is_ag)
 apply (rule ag_mOp_closed, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (thin_tac "h k = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) +\<^sub>M  (s k \<star>\<^sub>M (h k))")
 apply (subgoal_tac "\<forall>y\<in>carrier R. ( 1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<cdot>\<^sub>R y = 1\<^sub>R \<longrightarrow> (\<exists>ha\<in>Nset k \<rightarrow> carrier M.  h ` Nset k = ha ` Nset k \<and>  ha k \<in> linear_span R M A (ha ` Nset (k - Suc 0)))")
 apply (thin_tac "A \<subseteq> J_rad R")
 apply (thin_tac "A \<odot>\<^sub>R M = carrier M")
 apply (thin_tac "card (h ` Nset k) = Suc k")
 apply (thin_tac "h \<in> Nset k \<rightarrow> h ` Nset k")
 apply (thin_tac "H = h ` Nset k")
 apply (thin_tac "finite (h ` Nset k)")
 apply (thin_tac "h ` Nset k \<subseteq> carrier M")
 apply (thin_tac "linear_span R M (carrier R) (h ` Nset k) = carrier M")
 apply (thin_tac "s \<in> Nset k \<rightarrow> A")
 apply (thin_tac " h \<in> Nset k \<rightarrow> carrier M")
 apply (thin_tac "(1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k) = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0)")
 apply blast
 apply (thin_tac "\<exists>y\<in>carrier R. ( 1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<cdot>\<^sub>R y = 1\<^sub>R")
 apply (rule ballI) apply (rule impI)
apply (subgoal_tac "h k \<in> linear_span R M A (h ` Nset (k - Suc 0))")
 apply(thin_tac "A \<subseteq> J_rad R")
 apply(thin_tac "A \<odot>\<^sub>R M = carrier M")
 apply(thin_tac "card (h ` Nset k) = Suc k")
 apply(thin_tac "h \<in> Nset k \<rightarrow> h ` Nset k")
 apply(thin_tac "H = h ` Nset k")
 apply(thin_tac "finite (h ` Nset k)")
 apply(thin_tac "h ` Nset k \<subseteq> carrier M")
 apply(thin_tac "linear_span R M (carrier R) (h ` Nset k) = carrier M")
 apply(thin_tac "(1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k) = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0)")
 apply blast
apply (frule_tac H = "h ` Nset (k - Suc 0)" and s = s and n = "k - Suc 0" and f = h
       in lin_span_closed2 [of "R" "A" "M"], assumption+)
 apply (frule_tac f = h and A = "Nset k" and B = "carrier M" and ?A1.0 =
 "Nset (k - Suc 0)" in image_sub)
 apply (rule subsetI)
 apply (simp add:Nset_def)
 apply (frule_tac i = x and j = "k - Suc 0" and k = k in le_less_trans)
 apply simp apply (simp add:less_imp_le) apply assumption
 apply (subgoal_tac "s \<in> Nset (Suc (k - Suc 0)) \<rightarrow> A")
 apply (rule_tac f = s in func_pre) apply assumption
 apply simp
apply (subgoal_tac "h \<in> Nset (k - Suc 0) \<rightarrow> (h ` Nset (k - Suc 0))")
 apply (subgoal_tac "(h ` Nset (k - Suc 0)) \<subseteq> linear_span R M (carrier R) (h ` Nset (k - Suc 0))")
 apply (rule extend_fun, assumption+)
 apply (rule subsetI)
 apply (rule h_in_linear_span, assumption+)
 apply (rule subsetI) apply (simp add:image_def)
 apply (subgoal_tac "\<forall>l. l \<in> Nset (k - Suc 0) \<longrightarrow> l \<in> Nset k")
 apply (thin_tac " A \<odot>\<^sub>R M = carrier M")
 apply (thin_tac "card {y. \<exists>x\<in>Nset k. y = h x} = Suc k")
 apply (thin_tac "h \<in> Nset k \<rightarrow> {y. \<exists>x\<in>Nset k. y = h x}")
 apply (thin_tac "H = {y. \<exists>x\<in>Nset k. y = h x}")
 apply (thin_tac "finite {y. \<exists>x\<in>Nset k. y = h x}")
 apply (thin_tac "linear_span R M (carrier R) {y. \<exists>x\<in>Nset k. y = h x} = carrier M")
 apply (thin_tac "h \<in> Nset k \<rightarrow> carrier M")
 apply (thin_tac "(1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k) = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0)")
 apply blast
 apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
 apply (frule_tac i = l and j = "k - Suc 0" and k = k in le_less_trans)
 apply simp apply (simp add:less_imp_le) apply assumption
apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:image_def) apply blast
 apply (simp add:linear_combination_def) apply (rotate_tac -7)
 apply (frule sym)
 apply (thin_tac "(1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k) = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0)") apply simp
 apply (thin_tac "A \<odot>\<^sub>R M = carrier M")
 apply (thin_tac "linear_span R M (carrier R) (h ` Nset k) = carrier M")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (h j)) (k - Suc 0) = (1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k) ")
 apply (frule_tac x = "1\<^sub>R +\<^sub>R (-\<^sub>R (s k))" and y = y in  ring_tOp_commute)
 apply (frule ring_is_ag)
 apply (rule ag_pOp_closed [of "R"], assumption+) apply simp
 apply (frule_tac H = "h ` Nset (k - Suc 0)" and r = y and x = "(1\<^sub>R +\<^sub>R (-\<^sub>R (s k))) \<star>\<^sub>M (h k)" in linear_span_sprod_closed [of "R" "M" "A"], assumption+)
 apply (frule_tac f = h and A = "Nset k" and B = "carrier M" and ?A1.0 =
 "Nset (k - Suc 0)" in image_sub)
 apply (rule subsetI)
 apply (simp add:Nset_def)
 apply (frule_tac i = x and j = "k - Suc 0" and k = k in le_less_trans)
 apply simp apply (simp add:less_imp_le) apply assumption
 apply assumption+
apply (subgoal_tac "h k \<in> carrier M")
apply (subgoal_tac "1\<^sub>R +\<^sub>R (-\<^sub>R (s k)) \<in> carrier R")
apply (simp add:sprod_assoc[THEN sym])
apply (simp add:sprod_one)
apply (frule ring_is_ag)
 apply (rule ag_pOp_closed, assumption+)
 apply (simp add:Nset_def funcset_mem)
done

lemma NAK:"\<lbrakk>ring R; \<not> zeroring R; R module M; M fgover R; ideal R A; A \<subseteq> J_rad R;  A \<odot>\<^sub>R M = carrier M \<rbrakk> \<Longrightarrow> carrier M = {0\<^sub>M}"
apply (frule NAKTr1[of "R" "M"], assumption+)
apply (auto del:equalityI)
apply (simp add:finite_generator_def) apply (erule conjE)
apply (case_tac "Suc 0 < card H")
apply (frule_tac H = H and k = "card H - Suc 0" in NAKTr5 [of "R" "M" "A"],
                  assumption+)
 apply (simp add:finite_generator_def)
 apply simp apply simp
apply (subgoal_tac "\<forall>h\<in>Nset (card H - Suc 0) \<rightarrow> carrier M. H = h ` Nset (card H - Suc 0) \<and> h (card H - Suc 0) \<in> linear_span R M A (h ` Nset (card H - Suc 0 - Suc 0)) \<longrightarrow> carrier M = {0\<^sub>M}")
apply blast
 apply (thin_tac "\<exists>h\<in>Nset (card H - Suc 0) \<rightarrow> carrier M. H = h ` Nset (card H - Suc 0) \<and> h (card H - Suc 0) \<in> linear_span R M A (h ` Nset (card H - Suc 0 - Suc 0))")
 apply (rule ballI) apply (rule impI) apply (erule conjE)
apply (frule_tac i = "Suc 0" and n = "card H" in less_diff_pos)
 apply (frule_tac k = "card H - Suc 0" in Nset_pre_sub)
 apply (frule_tac f = h and A = "Nset (card H - Suc 0)" and B = "carrier M"
 and ?A1.0 = "Nset (card H - Suc 0 - Suc 0)" in image_sub, assumption+)
 apply (frule_tac H = H and ?H1.0 = "h ` Nset (card H - Suc 0 - Suc 0)"
 in generator_generator [of "R" "M"], assumption+)
 apply (frule_tac k = "card H - Suc 0" in  Nset_pre_un)
 apply simp
apply (rule subsetI)
 apply (subgoal_tac "x \<in> insert (h (card H - Suc 0)) (h ` Nset (card H - Suc (Suc 0)))") prefer 2 apply simp
 apply (thin_tac "x \<in> H")
 apply (thin_tac " Nset (card H - Suc 0) =
          insert (card H - Suc 0) (Nset (card H - Suc (Suc 0)))")
 apply (thin_tac "H = insert (h (card H - Suc 0)) (h ` Nset (card H - Suc (Suc 0)))")
apply simp
 apply (case_tac "x = h (card H - Suc 0)")
 apply simp
 apply (frule_tac H = "h ` Nset (card H - Suc (Suc 0))" in lin_span_lin_span [of "R" "A" "M"], assumption+)
 apply (simp add:subsetD) apply simp
 apply (rule h_in_linear_span, assumption+)
 apply (frule_tac H = "h ` Nset (card H - Suc 0 - Suc 0)" in NAKTr3 [of "R" "M"], assumption+)
 apply (rule finite_imageI) apply (rule finite_Nset)
 apply (frule_tac a = "(LEAST j. \<exists>L. finite L \<and> generator R M L \<and> j = card L)" and
 b = "card H" and c = "card (h ` Nset (card H - Suc 0 - Suc 0))" in less_convert)
 apply (subgoal_tac "finite (Nset (card H - Suc 0 - Suc 0))")
 apply (frule_tac A = "Nset (card H - Suc 0 - Suc 0)" and f = h in card_image_le)
 apply (thin_tac "(LEAST j. \<exists>L. finite L \<and> generator R M L \<and> j = card L) =
             card H")
 apply (thin_tac "h \<in> Nset (card H - Suc 0) \<rightarrow> carrier M")
 apply (thin_tac "h (card H - Suc 0)
             \<in> linear_span R M A (h ` Nset (card H - Suc 0 - Suc 0))")
 apply (thin_tac "Nset (card H - Suc 0 - Suc 0) \<subseteq> Nset (card H - Suc 0)")
 apply (thin_tac "h ` Nset (card H - Suc 0 - Suc 0) \<subseteq> carrier M")
 apply (thin_tac "generator R M (h ` Nset (card H - Suc 0 - Suc 0))")
 apply (thin_tac "finite (Nset (card H - Suc 0 - Suc 0))")
 apply (thin_tac "H = h ` Nset (card H - Suc 0)")
 apply (simp add:card_Nset)
 apply (rule_tac i = "card (h ` Nset (card H - Suc (Suc 0)))" and j = "Suc (card H - Suc (Suc 0))" and k = "card H" in le_less_trans, assumption+)
 apply (rule_tac a = "card H" in Suc_Suc_less, assumption+)
 apply (simp add:finite_Nset)
 apply (simp add:finite_generator_def)
 apply (simp add:finite_generator_def)
 apply (subgoal_tac "finite (h ` Nset (card H - Suc (Suc 0)))") apply simp
 apply (rule finite_imageI) apply (simp add:finite_Nset)
apply (case_tac "H = {}")
 apply (simp add:generator_def) apply (simp add:linear_span_def)
 apply (thin_tac "(LEAST j. \<exists>L. finite L \<and> generator R M L \<and> j = card L) = card H")
 apply (frule_tac A = H in nonempty_card_pos, assumption+)
 apply (frule_tac m = 0 and n = "card H" in Suc_leI)
 apply (subgoal_tac "card H = Suc 0") prefer 2
 apply (auto del:equalityI)
 apply (frule_tac A = H in nonempty_ex)
apply (subgoal_tac "\<forall>x. x \<in> H \<longrightarrow> carrier M = {0\<^sub>M}") apply blast
 apply (thin_tac "\<exists>x. x \<in> H")
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "{x} \<subseteq> H")
 apply (subgoal_tac "card {x} = 1") prefer 2 apply (simp add:card1)
 prefer 2 apply (rule subsetI) apply simp
apply (frule_tac B = H and A = "{x}" in card_seteq, assumption+)
 apply simp
 apply (thin_tac "H \<noteq> {}")
 apply (thin_tac "card H = Suc 0")
 apply (thin_tac "x \<in> H")
 apply (thin_tac "card {x} = 1")
 apply (thin_tac "{x} \<subseteq> H")
apply (simp add:generator_def) apply (erule conjE)
 apply (subgoal_tac "x \<in> carrier M") prefer 2
 apply (subgoal_tac "x \<in>{x}")  apply (simp add:subsetD)
 apply (thin_tac "{x} = H") apply simp
 apply (subgoal_tac "x \<in> A \<odot>\<^sub>R M") prefer 2 apply simp
 apply (thin_tac "A \<odot>\<^sub>R M = carrier M")
 apply (simp add:smodule_ideal_coeff_def)
 apply (simp add:linear_span_def [of "R" "M" "A"])
 apply (simp add:nonempty)
apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> carrier M. \<forall>s\<in>Nset n \<rightarrow> A.
 x = linear_combination R M n s f \<longrightarrow> carrier M = {0\<^sub>M}")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> carrier M.
                    \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (rotate_tac -5) apply (frule sym)
 apply (thin_tac "linear_span R M (carrier R) H = carrier M")
 apply simp
 apply (frule_tac H = H and s = s and n = n and f = f in lin_span_closed2 [of "R" "A" "M"], assumption+)
 apply simp apply assumption+
 apply (frule sym) apply (thin_tac "x = linear_combination R M n s f")
 apply simp apply (thin_tac "linear_combination R M n s f = x")
 apply (thin_tac "H \<subseteq> linear_span R M (carrier R) H")
 apply (thin_tac "f \<in> Nset n \<rightarrow> linear_span R M (carrier R) H")
apply (subgoal_tac "x \<in> carrier M")
 prefer 2 apply (subgoal_tac "x \<in> H")
 apply (rotate_tac -3) apply (frule sym)
 apply (thin_tac "carrier M = linear_span R M (carrier R) H")
 apply simp
 apply (subgoal_tac "x \<in> {x}") apply simp prefer 2
 apply (thin_tac "s \<in> Nset n \<rightarrow> A")
 apply (thin_tac "carrier M = linear_span R M (carrier R) H")
 apply (subgoal_tac "H \<noteq> {}") prefer 2 apply (rule contrapos_pp, simp+)
apply (simp add:linear_span_def[of "R" "M" "A"])
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> H. \<forall>s\<in>Nset n \<rightarrow> A.
  x = linear_combination R M n s f \<longrightarrow> linear_span R M (carrier R) H = {0\<^sub>M}")
 apply (thin_tac "x \<in> linear_span R M (carrier R) H")
 apply (thin_tac "{x} = H") apply (thin_tac "x \<in> carrier M")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> H.
                    \<exists>s\<in>Nset n \<rightarrow> A. x = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (frule sym) apply (thin_tac "{x} = H")
 apply (frule_tac z = x and h = f and t = s and n = n in single_span [of "R" "M" "A"],  assumption+)
 apply simp apply assumption
 apply (subgoal_tac "\<forall>sa\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  sa 0 \<star>\<^sub>M x
 \<longrightarrow> linear_span R M (carrier R) H = {0\<^sub>M}")
 apply (thin_tac "x \<in> linear_span R M (carrier R) H")
 apply (thin_tac "x \<in> carrier M")
 apply (thin_tac "f \<in> Nset n \<rightarrow> H")
 apply (thin_tac "s \<in> Nset n \<rightarrow> A")
 apply (thin_tac "x = linear_combination R M n s f")
 apply blast apply (thin_tac "\<exists>sa\<in>Nset 0 \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  sa 0 \<star>\<^sub>M x")
 apply (rule ballI) apply (rule impI)
 apply (thin_tac "x \<in> linear_span R M (carrier R) H")
 apply (subgoal_tac "x = 0\<^sub>M")
prefer 2
 apply (thin_tac "H = {x}")
 apply (unfold linear_combination_def)
 apply (subgoal_tac "x =  sa 0 \<star>\<^sub>M x") prefer 2 apply (thin_tac "x \<in> carrier M")
 apply simp
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n = sa 0 \<star>\<^sub>M x")
 apply (thin_tac "x = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n")
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (frule_tac f = sa and A = "Nset 0" and B = A and x = 0 in funcset_mem,
                assumption+)
 apply (thin_tac "sa \<in> Nset 0 \<rightarrow> A") apply (thin_tac "0 \<in> Nset 0")
 apply (frule_tac module_is_ag [of "R" "M"], assumption+)
 apply (subgoal_tac "sa 0 \<star>\<^sub>M x \<in> carrier M")
 apply (frule_tac a = x and b = "sa 0 \<star>\<^sub>M x" and c = "-\<^sub>M (sa 0 \<star>\<^sub>M x)" in  ag_pOp_add_r [of "M"], assumption+)
 apply (rule ag_mOp_closed, assumption+)
 apply (thin_tac "x =  sa 0 \<star>\<^sub>M x")
 apply (simp add:ag_r_inv1)
apply (subgoal_tac "x +\<^sub>M (-\<^sub>M (sa 0 \<star>\<^sub>M x)) = 1\<^sub>R \<star>\<^sub>M x +\<^sub>M (-\<^sub>M  (sa 0 \<star>\<^sub>M x))")
 apply simp
 apply (thin_tac "x +\<^sub>M (-\<^sub>M (sa 0 \<star>\<^sub>M x)) = 0\<^sub>M")
 apply (frule_tac a = "sa 0" and m = x in sprod_minus_am1 [of "R" "M"], assumption+)
 apply (simp add:ideal_subset) apply assumption apply simp
 apply (thin_tac "-\<^sub>M (sa 0 \<star>\<^sub>M x) =  (-\<^sub>R (sa 0)) \<star>\<^sub>M x")
 apply (frule_tac a1 = "1\<^sub>R" and b1 = "(-\<^sub>R (sa 0))" and m1 = x
 in sprod_distrib1 [THEN sym, of "R" "M"], assumption+)
 apply (simp add:ring_one)
 apply (frule ring_is_ag) apply (rule ag_mOp_closed, assumption+)
 apply (simp add:ideal_subset) apply assumption
 apply simp
 apply (thin_tac "1\<^sub>R \<star>\<^sub>M x +\<^sub>M  (-\<^sub>R (sa 0)) \<star>\<^sub>M x = 0\<^sub>M")
 apply (subgoal_tac "sa 0 \<in> J_rad R") prefer 2 apply (simp add:subsetD)
 apply (frule_tac x = "sa 0" in J_rad_unit [of "R"], assumption+)
 apply (frule ring_one [of "R"])
 apply (subgoal_tac "unit R ( 1\<^sub>R +\<^sub>R  (-\<^sub>R (sa 0)) \<cdot>\<^sub>R (1\<^sub>R))")
 prefer 2 apply simp
 apply (thin_tac "\<forall>y. y \<in> carrier R \<longrightarrow> unit R ( 1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0)) \<cdot>\<^sub>R y)") apply (simp add:unit_def)
 apply (subgoal_tac "-\<^sub>R (sa 0) \<in> carrier R")
 apply (simp add:ring_r_one)
 apply (subgoal_tac "\<forall>y\<in>carrier R. (1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0))) \<cdot>\<^sub>R y = 1\<^sub>R \<longrightarrow>
    x = 0\<^sub>M")
 apply (thin_tac " ( 1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0))) \<star>\<^sub>M x = 0\<^sub>M")
 apply (thin_tac "sa 0 \<star>\<^sub>M x \<in> carrier M")
 apply (thin_tac "-\<^sub>R (sa 0) \<in> carrier R")
 apply (thin_tac "sa 0 \<in> J_rad R")
 apply blast apply (thin_tac "\<exists>y\<in>carrier R. ( 1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0))) \<cdot>\<^sub>R y = 1\<^sub>R")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac x = "1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0))" and y = y in ring_tOp_commute [of "R"])
 apply (frule ring_is_ag) apply (rule ag_pOp_closed, assumption+)
 apply simp
 apply (thin_tac "(1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0))) \<cdot>\<^sub>R y = 1\<^sub>R")
 apply (frule_tac a = y and b = "1\<^sub>R +\<^sub>R (-\<^sub>R (sa 0))" and m = x in
  sprod_assoc [of "R" "M"], assumption+)
 apply (frule ring_is_ag)
 apply (rule ag_pOp_closed, assumption+) apply simp
 apply (simp add:sprod_one)
 apply (simp add:sprod_a_0)
apply (frule ring_is_ag)
 apply (rule ag_mOp_closed, assumption+)
 apply (simp add:ideal_subset)
 apply (simp add:sprod_one)
 apply (rule sprod_mem, assumption+)
 apply (simp add:ideal_subset) apply assumption apply (simp add:Nset_def)
apply (thin_tac "f \<in> Nset n \<rightarrow> H")
 apply (thin_tac "s \<in> Nset n \<rightarrow> A")
 apply (thin_tac "x = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n =  sa 0 \<star>\<^sub>M x")
 apply (thin_tac "sa \<in> Nset 0 \<rightarrow> A")
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:linear_span_def)
 apply (subgoal_tac "\<forall>n. \<forall>f\<in>Nset n \<rightarrow> {0\<^sub>M}. \<forall>s\<in>Nset n \<rightarrow> carrier R.
  xa = linear_combination R M n s f \<longrightarrow> xa = 0\<^sub>M")
 apply blast
 apply (thin_tac "\<exists>n. \<exists>f\<in>Nset n \<rightarrow> {0\<^sub>M}.
                 \<exists>s\<in>Nset n \<rightarrow> carrier R. xa = linear_combination R M n s f")
 apply (rule allI) apply (rule ballI)+ apply (rule impI)
 apply (simp only:linear_combination_def)
 apply (rule eSum_zero, assumption+)
 apply (rule univar_func_test) apply (rule ballI)
 apply (frule_tac f = f and A = "Nset n" and B = "{0\<^sub>M}" and x = xb in funcset_mem, assumption+) apply simp
 apply (rule sprod_a_0, assumption+)
 apply (simp add:funcset_mem)
apply (rule subsetI) apply simp
apply (rule linear_span_inc_0 [of "R" "M" "carrier R"], assumption+)
 apply (simp add:whole_ideal)
 apply (rule subsetI) apply simp
apply (thin_tac "{x} = H") apply simp
done

lemma fg_qmodule:"\<lbrakk>ring R; R module M; M fgover R; submodule R M N \<rbrakk> \<Longrightarrow>
                          (M /\<^sub>m N) fgover R"
apply (frule mpj_mHom[of "R" "M" "N"], assumption+)
apply (frule mpj_surjec [of "R" "M" "N"], assumption+)
apply (rule surjec_finitely_gen [of "R" "M" "M /\<^sub>m N" "mpj M N"], assumption+)
apply (simp add:qmodule_module)
apply assumption+
done

lemma NAK1:"\<lbrakk>ring R; \<not> zeroring R; R module M; M fgover R; submodule R M N; ideal R A; A \<subseteq> J_rad R;  carrier M = A \<odot>\<^sub>R M \<plusminus>\<^sub>M N \<rbrakk> \<Longrightarrow> carrier M = N"
apply (subgoal_tac "A \<odot>\<^sub>R (M /\<^sub>m N) = carrier (M /\<^sub>m N)")
apply (frule fg_qmodule [of "R" "M" "N"], assumption+)
apply (frule qmodule_module [of "R" "M" "N"], assumption+)
apply (frule NAK [of "R" "M /\<^sub>m N" "A"], assumption+)
 apply (thin_tac "R module M /\<^sub>m N")
 apply (thin_tac "M /\<^sub>m N fgover R")
 apply (thin_tac "A \<odot>\<^sub>R M /\<^sub>m N = carrier (M /\<^sub>m N)")
 apply (thin_tac "carrier M = A \<odot>\<^sub>R M \<plusminus>\<^sub>M N")
 apply (simp add:qmodule_def) apply (simp add:set_mr_cos_def)
apply (simp add:submodule_def) apply (erule conjE)+
apply (rule equalityI) prefer 2 apply assumption
 apply (thin_tac " N \<subseteq> carrier M")
 apply (thin_tac "\<forall>a\<in>carrier R. \<forall>m\<in>N.  a \<star>\<^sub>M m \<in> N")
 apply (rule subsetI)
 apply (subgoal_tac "x \<uplus>\<^sub>M N \<in> {X. \<exists>a\<in>carrier M. X = a \<uplus>\<^sub>M N}")
 prefer 2 apply (thin_tac "{X. \<exists>a\<in>carrier M. X = a \<uplus>\<^sub>M N} = {N}")
 apply simp apply blast
apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac a = x in ag_a_in_ar_cos [of "M" "N"], assumption+)
 apply simp
apply (simp add:smodule_ideal_coeff_def)
apply (frule qmodule_module [of "R" "M" "N"], assumption+)
 apply (frule lin_span_sub_carrier [of "R" "A" "M /\<^sub>m N" "carrier (M /\<^sub>m N)"],
                                  assumption+) apply simp
apply (rule equalityI, assumption+)
 apply (thin_tac "linear_span R (M /\<^sub>m N) A (carrier (M /\<^sub>m N)) \<subseteq> carrier (M /\<^sub>m N)")
 apply (rule subsetI)
 apply (subgoal_tac "x \<in> set_mr_cos M N") prefer 2 apply (simp add:qmodule_def)
 apply (thin_tac "x \<in> carrier (M /\<^sub>m N)") apply (simp add:set_mr_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier M. x = a \<uplus>\<^sub>M N \<longrightarrow>
   (x \<in> linear_span R (M /\<^sub>m N) A (carrier (M /\<^sub>m N)))") apply blast
 apply (thin_tac "\<exists>a\<in>carrier M. x = a \<uplus>\<^sub>M N") apply (rule ballI)
 apply (rule impI)
 apply (subgoal_tac "a \<in> linear_span R M A (carrier M)  \<plusminus>\<^sub>M N")
 apply (thin_tac "carrier M = linear_span R M A (carrier M) \<plusminus>\<^sub>M N")
 apply (thin_tac "a \<in> carrier M")
 apply (simp add:sSum_def)
apply (subgoal_tac "\<forall>h1\<in>linear_span R M A (carrier M). \<forall>h2\<in>N. a =  h1 +\<^sub>M h2
 \<longrightarrow> (a \<uplus>\<^sub>M N \<in> linear_span R (M /\<^sub>m N) A (carrier (M /\<^sub>m N)))")
 apply blast
 apply (thin_tac "\<exists>h1\<in>linear_span R M A (carrier M). \<exists>h2\<in>N. a =  h1 +\<^sub>M h2")
 apply (rule ballI)+ apply (rule impI)
 apply (subgoal_tac "a \<uplus>\<^sub>M N = mpj M N a") apply simp
 apply (thin_tac "x = mpj M N ( h1 +\<^sub>M h2)") apply (thin_tac "a =  h1 +\<^sub>M h2")
 apply (thin_tac "(h1 +\<^sub>M h2) \<uplus>\<^sub>M N = mpj M N ( h1 +\<^sub>M h2)")
 apply (frule mpj_mHom [of "R" "M" "N"], assumption+)
 apply (subgoal_tac "linear_span R M A (carrier M) \<subseteq> carrier M")
 prefer 2 apply (rule lin_span_sub_carrier[of "R" "A" "M" "carrier M"], assumption+) apply simp
 apply (subst mHom_add[of "R" "M" "M /\<^sub>m N" "mpj M N"], assumption+)
 apply (simp add:subsetD) apply (simp add:submodule_def) apply (erule conjE)+
 apply (simp add:subsetD)
 apply (subgoal_tac "mpj M N h2 = 0\<^sub>(M /\<^sub>m N)") apply simp
 apply (frule module_is_ag [of "R" "M /\<^sub>m N"], assumption+)
 apply (subst ag_r_zero, assumption+)
 apply (frule_tac A = "linear_span R M A (carrier M)" and B = "carrier M" and
 c = h1 in subsetD, assumption+)
 apply (rule mHom_mem [of "R" "M" "M /\<^sub>m N" "mpj M N"], assumption+)
 apply (frule linmap_im_linspan1 [of "R" "A" "M" "M /\<^sub>m N" "mpj M N" "carrier M"], assumption+) apply simp apply simp
 apply (subgoal_tac "mpj M N ` carrier M = carrier (M /\<^sub>m N)")
 apply simp
 apply (thin_tac "h1 \<in> linear_span R M A (carrier M)")
 apply (thin_tac "linear_span R M A (carrier M) \<subseteq> carrier M")
 apply (thin_tac "mpj M N h2 = 0\<^sub>M /\<^sub>m N")
 apply (thin_tac "mpj M N h1 \<in> linear_span R (M /\<^sub>m N) A (mpj M N ` carrier M)")
 apply (thin_tac "h2 \<in> N")
 apply (frule mpj_surjec [of "R" "M" "N"], assumption+)
 apply (simp add:surjec_def) apply (erule conjE)
 apply (simp add:surj_to_def)
 apply (simp add:mpj_0)
 apply (subgoal_tac "h1 +\<^sub>M h2 \<in> carrier M")
 apply (simp add:mpj_def) apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_pOp_closed, assumption+)
 apply (frule_tac lin_span_sub_carrier [of "R" "A" "M" "carrier M"], assumption+) apply simp apply (simp add:subsetD) apply (simp add:submodule_def)
 apply (erule conjE)+ apply (simp add:subsetD)
apply simp
done


section "7. direct sum and direct products of modules 1, general case"

constdefs
 prodM_sprod ::"[('r, 'm) RingType_scheme, 'i set,  'i \<Rightarrow> ('a, 'r, 'm1) ModuleType_scheme] \<Rightarrow>  'r \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow>  ('i \<Rightarrow> 'a)"
  "prodM_sprod R I A == \<lambda>a\<in>carrier R. \<lambda>g\<in>carr_prodag I A.
                                         (\<lambda>j\<in>I. a \<star>\<^sub>(A j) (g j))"
constdefs
 prodM::"[('r, 'm) RingType_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'm1) ModuleType_scheme] \<Rightarrow>  \<lparr> carrier:: ('i \<Rightarrow> 'a) set,
      pOp::['i \<Rightarrow> 'a, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a),
      mOp:: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a), zero::('i \<Rightarrow> 'a),
      sprod :: ['r, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a) \<rparr>"

 "prodM R I A == \<lparr>carrier = carr_prodag I A,
   pOp = prod_pOp I A, mOp = prod_mOp I A,
   zero = prod_zero I A, sprod = prodM_sprod R I A \<rparr>"

constdefs
  mProject::"[('r, 'm) RingType_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'more) ModuleType_scheme, 'i] \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a"
  "mProject R I A j == \<lambda>f\<in>carr_prodag I A. f j"

syntax
  "@PRODMODULES" :: "[('r, 'm) RingType_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'more)
 ModuleType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a ) set"  ("(3m\<Pi>\<^sub>_\<^sub>_/ _)" [72,72,73]72)

translations
  "m\<Pi>\<^sub>R\<^sub>I A" == "prodM R I A"

lemma prodM_carr:"\<lbrakk>ring R; \<forall>i\<in>I. (R module (M i))\<rbrakk> \<Longrightarrow>
                                carrier (prodM R I M) = carr_prodag I M"
apply (simp add:prodM_def)
done

lemma prodM_mem_eq:"\<lbrakk>ring R; \<forall>i\<in>I. (R module (M i)); m1 \<in> carrier (prodM R I M); m2 \<in> carrier (prodM R I M); \<forall>i\<in>I. m1 i = m2 i \<rbrakk> \<Longrightarrow> m1 = m2"
apply (frule prodM_carr [of "R" "I" "M"], assumption+) apply simp
apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
apply (rule carr_prodag_mem_eq [of "I" "M"], assumption+)
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+)
apply simp
done

lemma prodM_sprod_mem:"\<lbrakk>ring R; \<forall>i\<in>I. (R module (M i)); a \<in> carrier R;
 m \<in> carr_prodag I M\<rbrakk> \<Longrightarrow> prodM_sprod R I M a m \<in> carr_prodag I M"
apply (simp add:prodM_sprod_def carr_prodag_def)
apply (erule conjE)+
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Un_carrier_def)
 apply (subgoal_tac "m x \<in> carrier (M x)") prefer 2 apply simp
 apply (subgoal_tac "R module M x") prefer 2 apply simp
 apply (frule_tac M = "M x" and a = a and m = "m x" in sprod_mem [of "R"],
                                             assumption+)
 apply blast
apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply simp apply assumption+ apply simp
done

lemma prodM_sprod_val:"\<lbrakk>ring R; \<forall>i\<in>I. (R module (M i)); a \<in> carrier R;
 m \<in> carr_prodag I M; j \<in> I\<rbrakk> \<Longrightarrow> (prodM_sprod R I M a m) j = a \<star>\<^sub>(M j) (m j)"
apply (simp add:prodM_sprod_def)
done

lemma prodM_Module:"\<lbrakk>ring R; \<forall>i\<in>I. (R module (M i))\<rbrakk> \<Longrightarrow>
                                       R module (prodM R I M)"
apply (simp add:Module_def [of "R" "prodM R I M"])
apply (rule conjI)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (frule prodag_agroup[of "I" "M"])
 apply (simp add:agroup_def [of "prodM R I M"])
 apply (simp add:prodM_def)
 apply (simp add:agroup_def [of "a\<Pi>\<^sub>I M"])
 apply (simp add:prodag_def)
 apply (thin_tac " prod_pOp I M \<in> carr_prodag I M \<rightarrow> carr_prodag I M \<rightarrow> carr_prodag I M \<and>
       prod_mOp I M \<in> carr_prodag I M \<rightarrow> carr_prodag I M \<and>
       prod_zero I M \<in> carr_prodag I M \<and>
       (\<forall>x\<in>carr_prodag I M.
           \<forall>y\<in>carr_prodag I M.
              \<forall>z\<in>carr_prodag I M.
                 prod_pOp I M (prod_zero I M) x = x \<and>
                 prod_pOp I M (prod_mOp I M x) x = prod_zero I M \<and>
                 prod_pOp I M (prod_pOp I M x y) z =
                 prod_pOp I M x (prod_pOp I M y z) \<and>
                 prod_pOp I M x y = prod_pOp I M y x)")
 apply (rule impI) apply (rule ballI)
 apply (frule prod_zero_func[of "I" "M"])
 apply (subgoal_tac "x +\<^sub>(a\<Pi>\<^sub>I M) 0\<^sub>(a\<Pi>\<^sub>I M) = x")
 apply (simp add:prodag_def)
 apply (frule prodag_agroup[of "I" "M"])
 apply (rule ag_r_zero, assumption+) apply (simp add:prodag_def)
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+) apply simp
apply (rule conjI)
 apply (simp add:prodM_def)
 apply (rule bivar_func_test) apply (rule ballI)+
 apply (subst carr_prodag_def) apply (simp add:CollectI)
 apply (rule conjI)
 apply (simp add:prodM_sprod_def extensional_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rename_tac a f j)
 apply (simp add:Un_carrier_def prodM_sprod_def)
 apply (simp add:carr_prodag_def) apply (erule conjE)+
 apply (subgoal_tac "f j \<in> carrier (M j)") prefer 2 apply simp
 apply (subgoal_tac "R module (M j)") prefer 2 apply simp
 apply (frule_tac M = "M j" and a = a and m = "f j" in sprod_mem [of "R"],
                                                 assumption+)
 apply blast
apply (rule ballI)
 apply (simp add:prodM_sprod_def)
 apply (rule sprod_mem, assumption+)
 apply simp apply assumption apply (simp add:carr_prodag_def)
apply (rule ballI)+
 apply (simp add:prodM_def)
 apply (rule conjI)
 apply (frule_tac a = "a \<cdot>\<^sub>R b" and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (rule_tac x = a and y = b in ring_tOp_closed, assumption+)
 apply (frule_tac a = b and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (frule_tac a = a and m = "prodM_sprod R I M b m" in prodM_sprod_mem [of
 "R" "I" "M"], assumption+)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (rule carr_prodag_mem_eq [of "I" "M"], assumption+)
 apply (rule ballI)
 apply (subgoal_tac "m l \<in> carrier (M l)")
 apply (frule_tac x = a and y = b in ring_tOp_closed, assumption+)
 apply (subst prodM_sprod_val, assumption+)+
 apply (rule sprod_assoc, assumption+) apply simp apply assumption+
 apply (simp add:carr_prodag_def) apply (rule ballI)
 apply (rule module_is_ag [of "R" _], assumption+) apply simp
 apply (rule conjI)
 apply (frule ring_is_ag)
 apply (frule_tac x = a and y = b in ag_pOp_closed, assumption+)
 apply (frule_tac  a = "a +\<^sub>R b" and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (frule_tac a = b and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (frule_tac a = a and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (frule_tac X = "prodM_sprod R I M a m" and
 Y = "prodM_sprod R I M b m" in  prod_pOp_mem [of "I" "M"], assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "M"], assumption+)
 apply (rule ballI)
 apply (subgoal_tac "m l \<in> carrier (M l)")
 apply (simp add:prod_pOp_def)
 apply (subst prodM_sprod_val, assumption+)+
 apply (rule sprod_distrib1, assumption+) apply simp apply assumption+
 apply (simp add:carr_prodag_def) apply (rule ballI)
 apply (rule module_is_ag [of "R"], assumption+)  apply simp
apply (rule conjI)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (frule_tac X = m and Y = n in prod_pOp_mem [of "I" "M"], assumption+)
 apply (frule_tac a = a and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (frule_tac a = a and m = n in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (frule_tac X = "prodM_sprod R I M a m" and Y = "prodM_sprod R I M a n" in prod_pOp_mem [of "I" "M"], assumption+)
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (simp add:prodM_sprod_mem [of "R" "I" "M"])
 apply assumption+
 apply (rule ballI)
 apply (subgoal_tac "m l \<in> carrier (M l)")
 apply (subgoal_tac "n l \<in> carrier (M l)")
 apply (subst prodM_sprod_val, assumption+)
 apply (simp add:prod_pOp_def) apply (subst prodM_sprod_val, assumption+)+
 apply (rule sprod_distrib2, assumption+) apply simp apply assumption+
 apply (simp add:carr_prodag_def)
 apply (simp add:carr_prodag_def)
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+)
 apply simp
 apply (frule ring_one)
 apply (frule_tac a = "1\<^sub>R" and m = m in prodM_sprod_mem [of "R" "I" "M"],
                                           assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "M"])
 apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+)
 apply simp apply assumption+
 apply (rule ballI) apply (subgoal_tac "m l \<in> carrier (M l)")
 apply (subst prodM_sprod_val, assumption+)
 apply (rule sprod_one, assumption+) apply simp apply assumption
 apply (simp add:carr_prodag_def)
done

constdefs
 dsumM::"[('r, 'm) RingType_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'more) ModuleType_scheme] \<Rightarrow>  \<lparr> carrier:: ('i \<Rightarrow> 'a) set,
      pOp::['i \<Rightarrow> 'a, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a),
      mOp:: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a), zero::('i \<Rightarrow> 'a),
      sprod :: ['r, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a) \<rparr>"
  "dsumM R I A == \<lparr> carrier = carr_dsumag I A,
   pOp = prod_pOp I A, mOp = prod_mOp I A,
   zero = prod_zero I A, sprod = prodM_sprod R I A\<rparr>"

syntax
  "@DSUMMOD" :: "[('r, 'm) RingType_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'more)
  ModuleType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a ) set"  ("(3\<^sub>_\<Oplus>~\<^sub>_/ _)" [72,72,73]72)

translations
  "\<^sub>R\<Oplus>~\<^sub>I A" == "dsumM R I A"

lemma dsum_sprod_mem:"\<lbrakk>ring R; \<forall>i\<in>I. R module M i; a \<in> carrier R;
 b \<in> carr_dsumag I M\<rbrakk>  \<Longrightarrow> prodM_sprod R I M a b \<in> carr_dsumag I M"
apply (subgoal_tac "carr_dsumag I M \<subseteq> carr_prodag I M")
 prefer 2 apply (rule subsetI) apply (simp add:carr_dsumag_def finiteHom_def)
apply (frule subsetD [of "carr_dsumag I M" "carr_prodag I M" "b"], assumption+)
apply (frule prodM_sprod_mem [of "R" "I" "M" "a" "b"], assumption+)
apply (subst carr_dsumag_def) apply (simp add:finiteHom_def CollectI)
apply (simp add:carr_dsumag_def finiteHom_def)
apply (subgoal_tac "\<forall>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. b j = 0\<^sub>M j) \<longrightarrow>
 (\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. prodM_sprod R I M a b j = 0\<^sub>M j))")
apply blast apply (thin_tac "\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. b j = 0\<^sub>M j)")
apply (rule allI) apply (rule impI)
apply (subgoal_tac "\<forall>j\<in>I - H. prodM_sprod R I M a b j = 0\<^sub>(M j)")
apply blast
apply (rule ballI) apply (erule conjE)+
 apply (subgoal_tac "b j = 0\<^sub>(M j)") prefer 2 apply simp
 apply (thin_tac "\<forall>j\<in>I - H. b j = 0\<^sub>(M j)")
 apply (simp add:prodM_sprod_def)
 apply (rule sprod_a_0, assumption+) apply simp+
done

lemma carr_dsum_prod:"\<lbrakk>ring R; \<forall>i\<in>I. R module M i\<rbrakk> \<Longrightarrow>
                                  carr_dsumag I M \<subseteq> carr_prodag I M"
apply (rule subsetI) apply (simp add:carr_dsumag_def finiteHom_def)
done

lemma carr_dsum_prod1:"\<lbrakk>ring R; \<forall>i\<in>I. R module M i\<rbrakk> \<Longrightarrow>
                  \<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M"
apply (rule allI) apply (rule impI)
apply (frule carr_dsum_prod [of "R" "I" "M"], assumption+)
apply (simp add:subsetD)
done

lemma carr_dsumM_mem_eq:"\<lbrakk>ring R; \<forall>i\<in>I. R module M i; x \<in> carr_dsumag I M;
  y \<in> carr_dsumag I M; \<forall>j\<in>I. x j = y j\<rbrakk> \<Longrightarrow> x = y"
apply (frule carr_dsum_prod [of "R" "I" "M"], assumption+)
apply (frule subsetD [of "carr_dsumag I M" "carr_prodag I M" "x"], assumption+)
apply (frule subsetD [of "carr_dsumag I M" "carr_prodag I M" "y"], assumption+)
apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
apply (rule carr_prodag_mem_eq [of "I" "M"], assumption+)
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+)
apply simp
done

lemma dsumM_Module:"\<lbrakk>ring R; \<forall>i\<in>I. R module (M i) \<rbrakk> \<Longrightarrow> R module (\<^sub>R\<Oplus>~\<^sub>I M)"
apply (simp add:Module_def [of "R" "\<^sub>R\<Oplus>~\<^sub>I M"])
apply (rule conjI)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (frule dsumag_agroup[of "I" "M"])
 apply (simp add:agroup_def [of "\<^sub>R\<Oplus>~\<^sub>I M"])
 apply (simp add:dsumM_def)
 apply (simp add:agroup_def[of "a\<Oplus>~\<^sub>I M"])
 apply (simp add:dsumag_def)
 apply (thin_tac " prod_pOp I M \<in> carr_dsumag I M \<rightarrow> carr_dsumag I M \<rightarrow> carr_dsumag I M \<and> prod_mOp I M \<in> carr_dsumag I M \<rightarrow> carr_dsumag I M \<and>
 prod_zero I M \<in> carr_dsumag I M \<and> (\<forall>x\<in>carr_dsumag I M. \<forall>y\<in>carr_dsumag I M.
  \<forall>z\<in>carr_dsumag I M. prod_pOp I M (prod_zero I M) x = x \<and>
                 prod_pOp I M (prod_mOp I M x) x = prod_zero I M \<and>
                 prod_pOp I M (prod_pOp I M x y) z =
                 prod_pOp I M x (prod_pOp I M y z) \<and>
                 prod_pOp I M x y = prod_pOp I M y x)")
 apply (rule impI) apply (rule ballI)
 apply (frule dsumag_agroup[of "I" "M"])
 apply (subgoal_tac "x +\<^sub>(a\<Oplus>~\<^sub>I M) 0\<^sub>(a\<Oplus>~\<^sub>I M) = x")
 apply (simp add:dsumag_def)
 apply (rule ag_r_zero[of "a\<Oplus>~\<^sub>I M"], assumption+) apply (simp add:dsumag_def)
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+)
 apply simp
apply (simp add:dsumM_def)
 apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (rule dsum_sprod_mem, assumption+) apply (rule ballI)
 apply (rule module_is_ag [of "R"], assumption+) apply simp
apply (rule ballI)+
 apply (frule_tac a = "a \<cdot>\<^sub>R b" and b = m in dsum_sprod_mem [of "R" "I" "M"],
                                              assumption+)
 apply (simp add:ring_tOp_closed) apply assumption
 apply (frule_tac a = b and b = m in dsum_sprod_mem [of "R" "I" "M"],
                                              assumption+)
 apply (frule_tac a = a and b = "prodM_sprod R I M b m" in
                      dsum_sprod_mem [of "R" "I" "M"], assumption+)
 apply (frule_tac a = "a +\<^sub>R b" and b = m in dsum_sprod_mem [of "R" "I" "M"],
                                              assumption+)
 apply (frule ring_is_ag) apply (simp add:ag_pOp_closed)
 apply assumption
 apply (frule_tac a = a and b = m in dsum_sprod_mem [of "R" "I" "M"],
                                              assumption+)
 apply (subgoal_tac "\<forall>j\<in>I. agroup (M j)")
 apply (frule_tac X = "prodM_sprod R I M a m" and
  Y = "prodM_sprod R I M b m" in  dsum_pOp_mem [of "I" "M"], assumption+)
 apply (subgoal_tac "carr_dsumag I M \<subseteq> carr_prodag I M")
 apply (subgoal_tac "\<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M")
apply (rule conjI)
 apply (rule carr_dsumM_mem_eq [of "R" "I" "M"], assumption+)
 apply (rule ballI)
 apply (frule_tac x = a and y = b in ring_tOp_closed, assumption+)
 apply (subgoal_tac "m j \<in> carrier (M j)")
 apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+)
 apply (simp add:subsetD) apply assumption
 apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+)
 apply (simp add:subsetD) apply assumption
 apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+)
 apply (simp add:subsetD) apply assumption
 apply (rule sprod_assoc, assumption) apply simp apply assumption+
 apply (subgoal_tac "m \<in> carr_prodag I M") prefer 2 apply simp
 apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (rule carr_dsumM_mem_eq [of "R" "I" "M"], assumption+)
 apply (rule ballI)
 apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+)
 apply (frule ring_is_ag)
 apply (simp add:ag_pOp_closed) apply simp apply assumption
 apply (simp add:prod_pOp_def)
  apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+) apply simp
  apply assumption
  apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+) apply simp
  apply assumption
  apply (rule sprod_distrib1, assumption+) apply simp
  apply assumption+
  apply (subgoal_tac "m \<in> carr_prodag I M")  apply (simp add:carr_prodag_def)
  apply simp
 apply (frule_tac X = m and Y = n in  dsum_pOp_mem [of "I" "M"], assumption+)
 apply (frule_tac a = a and b = "prod_pOp I M m n" in
                 dsum_sprod_mem [of "R" "I" "M"],  assumption+)
 apply (frule_tac a = a and b = n in dsum_sprod_mem [of "R" "I" "M"],
                                                           assumption+)
 apply (rule conjI)
 apply (rule carr_dsumM_mem_eq [of "R" "I" "M"], assumption+)
 apply (rule  dsum_pOp_mem [of "I" "M"], assumption+)
 apply (rule ballI)
   apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+) apply simp
  apply assumption
  apply (simp add:prod_pOp_def)
  apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+) apply simp
  apply assumption
  apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+)
  apply (simp add:carr_prodag_def)
  apply assumption
 apply (rule sprod_distrib2, assumption+)
  apply simp apply assumption apply (subgoal_tac "m \<in> carr_prodag I M")
  apply (simp add:carr_prodag_def) apply simp
  apply (subgoal_tac "n \<in> carr_prodag I M") apply (simp add:carr_prodag_def)
  apply simp
apply (frule_tac a = "1\<^sub>R" and b = m in dsum_sprod_mem [of "R" "I" "M"],
                                                           assumption+)
 apply (simp add:ring_one) apply assumption
 apply (rule carr_dsumM_mem_eq [of "R" "I" "M"], assumption+)
 apply (rule ballI)
 apply (subst prodM_sprod_val [of "R" "I" "M"], assumption+)
 apply (simp add:ring_one) apply (simp add:subsetD) apply assumption
 apply (rule sprod_one, assumption+)
  apply simp
  apply (frule_tac c = m in subsetD [of "carr_dsumag I M" "carr_prodag I M"], assumption+)
  apply (simp add:carr_prodag_def)
apply (rule allI) apply (rule impI) apply (simp add:subsetD)
 apply (rule subsetI) apply (simp add:carr_dsumag_def finiteHom_def)
apply (rule ballI)
 apply (rule module_is_ag [of "R"], assumption+)
 apply simp
done

constdefs
 ringModule::"('r, 'b) RingType_scheme \<Rightarrow> ('r, 'r) ModuleType"
                ("(\<^sub>M_)" [998]999)
 "\<^sub>MR == \<lparr>carrier = carrier R, pOp = pOp R, mOp = mOp R,
    zero = zero R, sprod = tOp R\<rparr>"

lemma ringModule_Module:"ring R \<Longrightarrow> R module \<^sub>MR"
apply (simp add:Module_def)  apply (rule conjI)
 apply (simp add:agroup_def)  apply (simp add:ringModule_def)
 apply (frule ring_is_ag)  apply (simp add:agroup_def)
 apply (thin_tac "pOp R \<in> carrier R \<rightarrow> carrier R \<rightarrow> carrier R \<and>
       mOp R \<in> carrier R \<rightarrow> carrier R \<and> 0\<^sub>R \<in> carrier R \<and>
  (\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. \<forall>z\<in>carrier R. 0\<^sub>R +\<^sub>R x = x \<and>
   -\<^sub>R x +\<^sub>R x = 0\<^sub>R \<and> x +\<^sub>R y +\<^sub>R z =  x +\<^sub>R ( y +\<^sub>R z) \<and>  x +\<^sub>R y =  y +\<^sub>R x)")
 apply (rule impI) apply (rule ballI)  apply (frule ring_is_ag)
 apply (simp add:ag_r_zero) apply (rule conjI) apply (simp add:ringModule_def)
 apply (simp add:ring_def)
apply (rule ballI)+  apply (simp add:ringModule_def)
apply (simp add:ring_def)  apply (fold ring_def)
 apply (simp add:ring_distrib2)  apply (simp add:ring_r_one)
done

constdefs
 dsumMhom::"['i set, 'i \<Rightarrow> ('a, 'r, 'm) ModuleType_scheme, 'i \<Rightarrow> ('b, 'r, 'm1) ModuleType_scheme, 'i \<Rightarrow> ('a \<Rightarrow> 'b)] \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'b)"
 "dsumMhom I A B S == \<lambda>f\<in>carr_dsumag I A. (\<lambda>k\<in>I. (S k) (f k))"

lemma dsumMhom_mem:"\<lbrakk>ring R; \<forall>i\<in>I. R module M i; \<forall>i\<in>I. R module N i;
           \<forall>i\<in>I. S i \<in> mHom R (M i) (N i); x \<in> carr_dsumag I M\<rbrakk>
        \<Longrightarrow> dsumMhom I M N S x \<in> carr_dsumag I N"
apply (subst carr_dsumag_def) apply (simp add:CollectI)
apply (simp add:finiteHom_def)
apply (rule conjI)
apply (simp add:dsumMhom_def)
apply (subgoal_tac "x \<in> carr_prodag I M") prefer 2
 apply (simp add:carr_dsumag_def finiteHom_def)
 apply (simp add:carr_prodag_def)
 apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply (erule conjE)+
 apply simp
 apply (frule_tac x = xa in funcset_mem [of "x" "I" "Un_carrier I M"],
                                                       assumption+)
 apply (simp add:Un_carrier_def)
 apply (subgoal_tac "\<forall>X. (\<exists>i\<in>I. X = carrier (M i)) \<and> x xa \<in> X \<longrightarrow>
          (\<exists>xb. (\<exists>i\<in>I. xb = carrier (N i)) \<and> S xa (x xa) \<in> xb)")
 apply (thin_tac "\<forall>i\<in>I. x i \<in> carrier (M i)")
 apply (thin_tac "\<forall>i\<in>I. S i \<in> mHom R (M i) (N i)")
 apply blast
 apply (thin_tac "\<exists>xb. (\<exists>i\<in>I. xb = carrier (M i)) \<and> x xa \<in> xb")
 apply (rule allI) apply (rule impI)  apply (erule conjE)
 apply (thin_tac "\<exists>i\<in>I. X = carrier (M i)") apply (thin_tac "x xa \<in> X")
 apply (subgoal_tac "x xa \<in> carrier (M xa)") prefer 2 apply simp
 apply (subgoal_tac "S xa \<in> mHom R (M xa) (N xa)") prefer 2 apply simp
 apply (subgoal_tac "R module (M xa)") prefer 2 apply simp
 apply (subgoal_tac "R module (N xa)") prefer 2 apply simp
 apply (frule_tac M = "M xa" and N = "N xa" and f = "S xa" and
        m = "x xa" in mHom_mem [of "R"], assumption+)
 apply blast
apply (rule ballI)
 apply (subgoal_tac "x i \<in> carrier (M i)") prefer 2 apply simp
 apply (subgoal_tac "S i \<in> mHom R (M i) (N i)") prefer 2 apply simp
 apply (subgoal_tac "R module (M i)") prefer 2 apply simp
 apply (subgoal_tac "R module (N i)") prefer 2 apply simp
 apply (rule_tac M = "M i" and N = "N i" and f = "S i" and
        m = "x i" in mHom_mem [of "R"], assumption+)
apply (simp add:carr_dsumag_def finiteHom_def) apply (erule conjE)+
 apply (subgoal_tac "\<forall>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. x j = 0\<^sub>M j) \<longrightarrow>
 (\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. dsumMhom I M N S x j = 0\<^sub>N j))")
 apply (thin_tac "\<forall>i\<in>I. R module M i")
 apply (thin_tac "\<forall>i\<in>I. R module N i")
 apply (thin_tac "\<forall>i\<in>I. S i \<in> mHom R (M i) (N i)")
 apply blast
 apply (thin_tac "\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. x j = 0\<^sub>M j)")
apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "\<forall>j\<in>I - H. dsumMhom I M N S x j = 0\<^sub>(N j)")
 apply blast
apply (rule ballI)
 apply (subgoal_tac "x \<in> carr_dsumag I M")
 apply (simp add:dsumMhom_def)
 apply (rule mHom_0, assumption+)
 apply simp+
apply (simp add:carr_dsumag_def finiteHom_def) apply blast
done

lemma dsumMhom_mHom:"\<lbrakk>ring R; \<forall>i\<in>I. (R module (M i)); \<forall>i\<in>I. (R module (N i));
 \<forall>i\<in>I. ((S i) \<in> mHom R (M i) (N i)) \<rbrakk> \<Longrightarrow>
                dsumMhom I M N S \<in> mHom R (\<^sub>R\<Oplus>~\<^sub>I M) (\<^sub>R\<Oplus>~\<^sub>I N)"
apply (subst mHom_def) apply (simp add:CollectI)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:dsumM_def)
 apply (simp add:dsumMhom_mem)
apply (rule conjI)
 apply (simp add:dsumMhom_def extensional_def)
 apply (simp add:dsumM_def)
apply (rule ballI)+
 apply (simp add:dsumM_def)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (M i)")
 apply (frule_tac X = a and Y = b in dsum_pOp_mem [of "I" "M"], assumption+)
 apply (frule_tac x = "prod_pOp I M a b" in dsumMhom_mem [of "R" "I" "M" "N" "S"], assumption+)
 apply (frule_tac x = a in dsumMhom_mem [of "R" "I" "M" "N" "S"], assumption+)
 apply (frule_tac x = b in dsumMhom_mem [of "R" "I" "M" "N" "S"], assumption+)
 apply (subgoal_tac "\<forall>i\<in>I. agroup (N i)")
 apply (frule_tac X = "dsumMhom I M N S a" and Y = "dsumMhom I M N S b" in dsum_pOp_mem [of "I" "N"], assumption+)
 apply (rule carr_dsumM_mem_eq [of "R" "I" "N"], assumption+)
 apply (rule ballI)
 apply (frule carr_dsum_prod1 [of "R" "I" "M"], assumption+)
 apply (frule carr_dsum_prod1 [of "R" "I" "N"], assumption+)
 apply (simp add:prod_pOp_def)
 apply (simp add:dsumMhom_def)
 apply (rule mHom_add, assumption+)
  apply simp+
  apply (subgoal_tac "a \<in>  carr_prodag I M") prefer 2 apply simp
  apply (simp add:carr_prodag_def)
  apply (subgoal_tac "b \<in>  carr_prodag I M") prefer 2 apply simp
  apply (simp add:carr_prodag_def)
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+) apply simp
apply (rule ballI) apply (rule module_is_ag [of "R"], assumption+) apply simp
apply (rule ballI)+
 apply (simp add:dsumM_def)
 apply (frule_tac a = a and b = m in dsum_sprod_mem [of "R" "I" "M"],
                                                          assumption+)
 apply (frule_tac x = "prodM_sprod R I M a m" in
                  dsumMhom_mem [of "R" "I" "M" "N" "S"], assumption+)
 apply (frule_tac x = m in dsumMhom_mem [of "R" "I" "M" "N" "S"], assumption+)
 apply (frule_tac a = a and b = "dsumMhom I M N S m" in
                    dsum_sprod_mem [of "R" "I" "N"], assumption+)
 apply (rule carr_dsumM_mem_eq [of "R" "I" "N"], assumption+)
 apply (rule ballI)
 apply (frule carr_dsum_prod1 [of "R" "I" "M"], assumption+)
 apply (frule carr_dsum_prod1 [of "R" "I" "N"], assumption+)
 apply (simp add:dsumMhom_def prodM_sprod_def)
 apply (subgoal_tac "S j \<in> mHom R (M j) (N j)") prefer 2 apply simp
 apply (rule mHom_lin, assumption+)
  apply simp+
 apply (subgoal_tac "m \<in> carr_prodag I M") prefer 2 apply simp
 apply (simp add:carr_prodag_def) apply assumption+
done

section "8. exact sequence"

constdefs
 Zm :: "[('r, 'm) RingType_scheme, 'a] \<Rightarrow> ('a, 'r) ModuleType"
 "Zm R e == \<lparr> carrier = {e}, pOp = \<lambda>x\<in>{e}. \<lambda>y\<in>{e}. e, mOp =
 \<lambda>x\<in>{e}. e, zero = e, sprod = \<lambda>r\<in>carrier R. \<lambda>x\<in>{e}. e\<rparr>"

lemma Zm_Module:"ring R \<Longrightarrow> R module (Zm R e)"
apply (simp add:Module_def)
apply (rule conjI)
 apply (simp add:agroup_def)
 apply (simp add:Zm_def)
 apply (rule conjI)+
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply simp
 apply (rule univar_func_test)
 apply (rule ballI)
 apply simp
apply (rule conjI)
apply (simp add:Zm_def)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply simp
apply (rule ballI)+
 apply (simp add:Zm_def)
 apply (frule ring_is_ag)
 apply (simp add:ag_pOp_closed)
 apply (simp add:ring_one)
 apply (frule_tac R = R and x = a and y = b in ring_tOp_closed, assumption+)
 apply simp
done

lemma Zm_carrier:"carrier (Zm R e) = {e}"
apply (simp add:Zm_def)
done

lemma Z_to_M_0:"\<lbrakk> ring R; R module M; f \<in> mHom R (Zm R e) M\<rbrakk> \<Longrightarrow>
     f e = 0\<^sub>M"
apply (insert Zm_Module [of "R" "e"])  apply simp
 apply (frule mHom_add [of "R" "Zm R e" "M" "f" "e" "e"], assumption+)
 apply (simp add:Zm_def) apply (simp add:Zm_def)
apply (subgoal_tac "pOp (Zm R e) e e = e")
 prefer 2 apply (simp add:Zm_def)
 apply simp apply (thin_tac "e +\<^sub>(Zm R e) e = e")
 apply (frule mHom_mem [of "R" "Zm R e" "M" "f" "e"], assumption+)
 apply (simp add:Zm_def)
 apply (frule sym) apply (thin_tac "f e =  f e +\<^sub>M (f e)")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule ag_eq_sol2 [of "M" "f e" "f e" "f e"], assumption+)
apply (simp add:ag_r_inv1)
done

lemma Z_to_M:"\<lbrakk> ring R; R module M; f \<in> mHom R (Zm R e) M; g \<in> mHom R (Zm R e) M \<rbrakk>  \<Longrightarrow> f = g"
apply (rule mHom_eq [of "R" "Zm R e" "M"], assumption+)
 apply (simp add:Zm_Module)
 apply assumption+
 apply (rule ballI)
 apply (simp add:Zm_def)
 apply (fold Zm_def)
 apply (frule Z_to_M_0 [of "R" "M" "f" "e"], assumption+)
 apply (frule Z_to_M_0 [of "R" "M" "g" "e"], assumption+)
 apply simp
done

lemma mzeromap_mHom:"\<lbrakk>ring R; R module M; R module N\<rbrakk> \<Longrightarrow> mzeromap M N \<in> mHom R M N"
apply (simp add:mHom_def aHom_def)
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:mzeromap_def) apply (simp add:Module_def agroup_def)
apply (rule conjI)
 apply (simp add:mzeromap_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed [of "M"], assumption+)
 apply (simp add:mzeromap_def)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (rule ag_l_zero[THEN sym, of "N"], assumption+)
 apply (simp add:ag_inc_zero)
apply (rule ballI)+
 apply (frule_tac a = a and m = m in sprod_mem [of "R" "M"], assumption+)
 apply (simp add:mzeromap_def)
apply (rule sprod_a_0 [THEN sym], assumption+)
done

lemma HOM_carrier:"\<lbrakk>ring R; R module M; R module N\<rbrakk> \<Longrightarrow> carrier (HOM\<^sub>R M N) = mHom R M N"
apply (simp add:HOM_def)
done

lemma mHom_Z_M:"\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow> mHom R (Zm R e) M = {mzeromap (Zm R e) M}"
apply (rule equalityI)
 apply (rule subsetI)
 apply simp
 apply (insert Zm_Module [of "R" "e"]) apply simp
 apply (frule mzeromap_mHom [of "R" "Zm R e" "M"], assumption+)
 apply (simp add:Z_to_M)
apply (rule subsetI) apply simp
 apply (simp add:mzeromap_mHom)
done

lemma Zm_isom:"(Zm R (e::'a)) \<cong>\<^sub>R (Zm R (u::'b))"
apply (subgoal_tac "(\<lambda>x\<in>{e}. u) \<in> mHom R (Zm R (e::'a)) (Zm R (u::'b))")
apply (subgoal_tac "bijec\<^sub>(Zm R (e::'a))\<^sub>,\<^sub>(Zm R (u::'b)) (\<lambda>x\<in>{e}. u)")
apply (simp add:misomorphic_def)
 apply blast
prefer 2
 apply (simp add:mHom_def aHom_def)
 apply (simp add:Zm_def)
 apply (rule univar_func_test) apply (rule ballI) apply simp
apply (simp add:bijec_def)
apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (simp add:ker_def)
 apply (simp add:Zm_def)
 apply (simp add:surjec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (simp add:surj_to_def image_def Zm_def)
done

lemma HOM_Z_M_0:"\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow> HOM\<^sub>R (Zm R e) M \<cong>\<^sub>R (Zm R e)"
apply (simp add:HOM_def)
apply (frule mHom_Z_M [of "R" "M" "e"], assumption+)
apply (fold HOM_def)
apply (subgoal_tac "(\<lambda>x\<in>{mzeromap (Zm R e) M}. e) \<in> mHom R (HOM\<^sub>R (Zm R e) M) (Zm R e)")
apply (subgoal_tac "bijec\<^sub>(HOM\<^sub>R (Zm R e) M)\<^sub>,\<^sub>(Zm R e) (\<lambda>x\<in>{mzeromap (Zm R e) M}. e)")
apply (simp add:misomorphic_def)
 apply blast
apply (simp add:bijec_def)
apply (rule conjI)
 apply (simp add:injec_def) apply (simp add:aHom_def)
 apply (rule conjI)
 apply (frule Zm_Module [of "R" "e"])
 apply (simp add:HOM_carrier [of "R" "Zm R e" "M"])
 apply (simp add:Zm_def) apply (fold Zm_def)
 apply (rule univar_func_test) apply (rule ballI)
 apply simp
apply (rule conjI)
 apply (simp add:extensional_def mzeromap_def)
 apply (simp add:HOM_def)
apply (rule conjI)
 apply (rule ballI)
 apply (rule conjI)
 apply (rule impI) apply (rule ballI)
 apply (rule conjI) apply (rule impI)
 apply (rule conjI) apply (rule impI)
 apply (simp add:Zm_def)
 apply (simp add:Zm_def) apply (fold Zm_def)
 apply (rule impI)
 apply (subgoal_tac "mzeromap (Zm R e) M \<in> carrier (HOM\<^sub>R (Zm R e) M)")
 apply (frule mHom_l_one [of "R" "Zm R e" "M" "mzeromap (Zm R e) M"])
 apply (simp add:Zm_Module) apply assumption
 apply (simp add:HOM_carrier)
 apply (simp add:HOM_def)
 apply (simp add:HOM_carrier)
apply (rule impI)
 apply (subgoal_tac "b = mzeromap (Zm R e) M") apply simp
 apply (thin_tac "a \<in> carrier (HOM\<^sub>R (Zm R e) M)")
 apply (thin_tac "a = mzeromap (Zm R e) M")
 apply (thin_tac "b \<noteq> mzeromap (Zm R e) M")
 apply (simp add:HOM_def)
apply (rule impI)
 apply (rule ballI)
 apply (simp add:HOM_def)
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def) apply (simp add:HOM_def)
 apply (rule subsetI)
 apply (simp add:ker_def)
 apply (simp add:HOM_def) apply (simp add:Zm_def)
apply (simp add:surjec_def) apply (simp add:mHom_def) apply (fold mHom_def)
 apply (simp add:surj_to_def)
 apply (simp add:HOM_def Zm_def)
 apply (frule Zm_Module [of "R" "e"])
 apply (frule HOM_is_module [of "R" "Zm R e" "M"], assumption+)
 apply (frule mzeromap_mHom [of "R" "HOM\<^sub>R (Zm R e) M" "Zm R e"], assumption+)
apply (subgoal_tac "(\<lambda>x\<in>{mzeromap (Zm R e) M}. e) = mzeromap (HOM\<^sub>R (Zm R e) M) (Zm R e)") apply simp
 apply (subgoal_tac "mzeromap (HOM\<^sub>R (Zm R e) M) (Zm R e)
       \<in> extensional (carrier (HOM\<^sub>R (Zm R e) M))")
 prefer 2 apply (simp add:mHom_def aHom_def)
 apply (subgoal_tac "(\<lambda>x\<in>{mzeromap (Zm R e) M}. e) \<in> extensional (carrier (HOM\<^sub>R (Zm R e) M))")
apply (rule funcset_eq, assumption+)
 apply (rule ballI)
 apply (simp add:HOM_carrier)
 apply (subgoal_tac "mzeromap (Zm R e) M \<in> carrier (HOM\<^sub>R (Zm R e) M)")
apply (frule mHom_mem [of "R" "HOM\<^sub>R (Zm R e) M" "Zm R e" "mzeromap (HOM\<^sub>R (Zm R e) M) (Zm R e)" "mzeromap (Zm R e) M"], assumption+)
apply (simp add:Zm_def)
 apply (subst HOM_carrier, assumption+) apply simp
apply (subst HOM_carrier, assumption+) apply (simp add:extensional_def)
done

lemma M_to_Z:"\<lbrakk> ring R; R module M; f \<in> mHom R M (Zm R e); g \<in> mHom R M (Zm R e)\<rbrakk>  \<Longrightarrow> f = g"
apply (rule mHom_eq [of "R" "M" "Zm R e"], assumption+)
 apply (simp add:Zm_Module)
 apply assumption+
 apply (rule ballI)
 apply (frule_tac m = m in mHom_mem [of "R" "M" "Zm R e" "f"], assumption+)
 apply (simp add:Zm_Module)
 apply assumption+
 apply (frule_tac m = m in mHom_mem [of "R" "M" "Zm R e" "g"], assumption+)
 apply (simp add:Zm_Module)
 apply assumption+
apply (simp add:Zm_def)
done

lemma mHom_to_zero:"\<lbrakk>ring R; R module M\<rbrakk> \<Longrightarrow>  mHom R M (Zm R e) = {mzeromap M (Zm R e)}"
apply (frule mzeromap_mHom [of "R" "M" "Zm R e"], assumption+)
 apply (simp add:Zm_Module)
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac f = "mzeromap M (Zm R e)" and g = x in M_to_Z [of "R" "M"],
                                      assumption+)
 apply simp
 apply (rule subsetI)
 apply simp
done

lemma carrier_HOM_M_Z:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> carrier (HOM\<^sub>R M (Zm R e)) = {mzeromap M (Zm R e)}"
apply (subst HOM_carrier, assumption+)
apply (simp add:Zm_Module)
apply (simp add:mHom_to_zero)
done

lemma  HOM_M_Z_0:"\<lbrakk>ring R; R module M \<rbrakk> \<Longrightarrow> HOM\<^sub>R M (Zm R e) \<cong>\<^sub>R (Zm R e)"
apply (subgoal_tac "(\<lambda>x\<in>mHom R M (Zm R e). 0\<^sub>(Zm R e)) \<in> mHom R (HOM\<^sub>R M (Zm R e)) (Zm R e)")
apply (subgoal_tac "bijec\<^sub>(HOM\<^sub>R M (Zm R e))\<^sub>,\<^sub>(Zm R e) (\<lambda>x\<in>mHom R M (Zm R e). 0\<^sub>(Zm R e))")
apply (simp add:misomorphic_def)
 apply blast
 apply (simp add:bijec_def)
 apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (rule equalityI) apply (rule subsetI)
 apply (simp add:ker_def) apply (erule conjE)
 apply (simp add:HOM_def) apply (fold HOM_def)
apply (rule mHom_eq [of "R" "M" "Zm R e"], assumption+)
 apply (simp add:Zm_Module) apply assumption
 apply (rule mzeromap_mHom, assumption+) apply (simp add:Zm_Module)
 apply (rule ballI)
 apply (frule_tac f = x and m = m in mHom_mem [of "R" "M" "Zm R e"], assumption+) apply (simp add:Zm_Module) apply assumption+
 apply (simp add:mHom_to_zero [of "R" "M"])
apply (rule subsetI)
 apply (simp add:HOM_def) apply (fold HOM_def)
 apply (simp add:ker_def)
 apply (frule Zm_Module [of "R" "e"])
 apply (simp add:mzeromap_mHom [of "R" "M" "Zm R e"])
 apply (simp add:HOM_def) apply (fold HOM_def)
 apply (simp add:mzeromap_mHom)
apply (simp add:surjec_def) apply (simp add:mHom_def) apply (fold mHom_def)
 apply (subst HOM_carrier [of "R" "M" "Zm R e"], assumption+)
 apply (simp add:Zm_Module)
 apply (simplesubst mHom_to_zero, assumption+)
 apply (simp add:surj_to_def)
 apply (simp add:image_def)
 apply (simp add:Zm_def)
apply (simplesubst mHom_to_zero, assumption+)
 apply (rule HOM_is_module, assumption+)
 apply (simp add:Zm_Module) apply simp
 apply (frule Zm_Module [of "R" "e"])
 apply (simp add:mzeromap_def)
 apply (subst HOM_carrier [of "R" "M" "Zm R e"], assumption+)
 apply (rule funcset_eq[of _ "mHom R M (Zm R e)" ])
 apply (simp add:extensional_def)
 apply (simp add:restrict_def extensional_def)
 apply (rule ballI)
 apply (simp add:mHom_to_zero)
done

lemma M_to_Z_0:"\<lbrakk>ring R; R module M; f \<in> mHom R M (Zm R e)\<rbrakk> \<Longrightarrow> ker\<^sub>M\<^sub>,\<^sub>(Zm R e) f = carrier M"
apply (simp add:ker_def)
apply (simp add:Zm_def) apply (fold Zm_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (rule subsetI)
 apply (simp add:mHom_def) apply (frule conj_1)
 apply (simp add:aHom_def) apply (frule conj_1)
 apply (thin_tac "f \<in> carrier M \<rightarrow> carrier (Zm R e) \<and>
           f \<in> extensional (carrier M) \<and>
           (\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f ( a +\<^sub>M b) =  f a +\<^sub>(Zm R e) (f b)) \<and>
           (\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. f ( a \<star>\<^sub>M m) =  a \<star>\<^sub>(Zm R e) (f m))")
 apply (simp add:Zm_def)
 apply (frule funcset_mem, assumption+)
apply simp
done

constdefs
exact3 ::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,  ('b, 'r, 'm1) ModuleType_scheme, ('c, 'r, 'm1) ModuleType_scheme, 'a \<Rightarrow> 'b, 'b \<Rightarrow> 'c] \<Rightarrow> bool"
"exact3 R L0 L1 L2 h0 h1 == h0 ` (carrier L0) = ker\<^sub>(L1)\<^sub>,\<^sub>(L2) h1"

constdefs
exact4 ::"[('r, 'm) RingType_scheme, ('a0, 'r, 'm1) ModuleType_scheme,  ('a1, 'r, 'm1) ModuleType_scheme, ('a2, 'r, 'm1) ModuleType_scheme, ('a3, 'r, 'm1) ModuleType_scheme, 'a0 \<Rightarrow> 'a1, 'a1 \<Rightarrow> 'a2, 'a2 \<Rightarrow> 'a3] \<Rightarrow> bool"
"exact4 R L0 L1 L2 L3 h0 h1 h2 == h0 ` (carrier L0) = ker\<^sub>(L1)\<^sub>,\<^sub>(L2) h1 \<and> h1 ` (carrier L1) = ker\<^sub>(L2)\<^sub>,\<^sub>(L3) h2 "

constdefs
exact5 ::"[('r, 'm) RingType_scheme, ('a0, 'r, 'm1) ModuleType_scheme,  ('a1, 'r, 'm1) ModuleType_scheme, ('a2, 'r, 'm1) ModuleType_scheme, ('a3, 'r, 'm1) ModuleType_scheme, ('a4, 'r, 'm1) ModuleType_scheme, 'a0 \<Rightarrow> 'a1, 'a1 \<Rightarrow> 'a2, 'a2 \<Rightarrow> 'a3, 'a3 \<Rightarrow> 'a4] \<Rightarrow> bool"
"exact5 R L0 L1 L2 L3 L4 h0 h1 h2 h3 == h0 ` (carrier L0) = ker\<^sub>(L1)\<^sub>,\<^sub>(L2) h1 \<and> h1 ` (carrier L1) = ker\<^sub>(L2)\<^sub>,\<^sub>(L3) h2 \<and> h2 ` (carrier L2) = ker\<^sub>(L3)\<^sub>,\<^sub>(L4) h3 "

exact8 ::"[('r, 'm) RingType_scheme, ('a0, 'r, 'm1) ModuleType_scheme,  ('a1, 'r, 'm1) ModuleType_scheme, ('a2, 'r, 'm1) ModuleType_scheme, ('a3, 'r, 'm1) ModuleType_scheme, ('a4, 'r, 'm1) ModuleType_scheme, ('a5, 'r, 'm1) ModuleType_scheme, ('a6, 'r, 'm1) ModuleType_scheme, ('a7, 'r, 'm1) ModuleType_scheme, 'a0 \<Rightarrow> 'a1, 'a1 \<Rightarrow> 'a2, 'a2 \<Rightarrow> 'a3, 'a3 \<Rightarrow> 'a4, 'a4 \<Rightarrow> 'a5, 'a5 \<Rightarrow> 'a6, 'a6 \<Rightarrow> 'a7] \<Rightarrow> bool"
"exact8 R L0 L1 L2 L3 L4 L5 L6 L7 h0 h1 h2 h3 h4 h5 h6 == h0 ` (carrier L0) = ker\<^sub>(L1)\<^sub>,\<^sub>(L2) h1 \<and> h1 ` (carrier L1) = ker\<^sub>(L2)\<^sub>,\<^sub>(L3) h2 \<and> h2 ` (carrier L2) = ker\<^sub>(L3)\<^sub>,\<^sub>(L4) h3\<and> h3 ` (carrier L3) = ker\<^sub>(L4)\<^sub>,\<^sub>(L5) h4 \<and> h4 ` (carrier L4) = ker\<^sub>(L5)\<^sub>,\<^sub>(L6) h5 \<and> h5 ` (carrier L5) = ker\<^sub>(L6)\<^sub>,\<^sub>(L7) h6"

lemma exact3_comp_0:"\<lbrakk>ring R; R module L; R module M; R module N; f \<in> mHom R L M; g \<in> mHom R M N; exact3 R L M N f g\<rbrakk> \<Longrightarrow> compos L g f = mzeromap L N"
apply (frule mHom_compos [of "R" "L" "M" "N" "f" "g"], assumption+)
apply (frule mzeromap_mHom [of "R" "L" "N"], assumption+)
apply (rule mHom_eq [of "R" "L" "N"], assumption+)
apply (rule ballI)
 apply (subst compos_def) apply (subst compose_def) apply simp
 apply (simp add:exact3_def)
 apply (subgoal_tac "f \<in> (carrier L) \<rightarrow> (carrier M)")
 prefer 2 apply (simp add:mHom_def aHom_def)
 apply (frule_tac a = m in mem_in_image [of "f" "carrier L" "carrier M"], assumption+)
 apply simp
apply (simp add:ker_def mzeromap_def)
done

lemma exact_im_sub_kern:"\<lbrakk>ring R; R module L; R module M; R module N; f \<in> mHom R L M; g \<in> mHom R M N; exact3 R L M N f g\<rbrakk> \<Longrightarrow> f ` (carrier L) \<subseteq> ker\<^sub>M\<^sub>,\<^sub>N g"
apply (simp add:exact3_def)
done

lemma mzero_im_sub_ker:"\<lbrakk>ring R; R module L; R module M; R module N; f \<in> mHom R L M; g \<in> mHom R M N; compos L g f = mzeromap L N\<rbrakk> \<Longrightarrow> f ` (carrier L) \<subseteq> ker\<^sub>M\<^sub>,\<^sub>N g"
apply (rule subsetI)
 apply (simp add:image_def)
 apply auto
 apply (simp add:ker_def)
 apply (simp add:mHom_mem)
 apply (simp add:compos_def compose_def)
 apply (subgoal_tac "(\<lambda>x\<in>carrier L. g (f x)) xa = mzeromap L N xa")
 prefer 2 apply simp
 apply (thin_tac "(\<lambda>x\<in>carrier L. g (f x)) = mzeromap L N")
 apply simp
 apply (simp add:mzeromap_def)
done

lemma left_exact_injec:"\<lbrakk>ring R; R module M; R module N; z \<in> mHom R (Zm R e) M; f \<in> mHom R M N; exact3 R (Zm R e) M N z f \<rbrakk> \<Longrightarrow> injec\<^sub>M\<^sub>,\<^sub>N f"
apply (simp add:injec_def)
apply (rule conjI)
apply (simp add:mHom_def)
apply (simp add:exact3_def)
apply (simp add:Zm_def) apply (fold Zm_def)
apply (simp add: Z_to_M_0 [of "R" "M" "z" "e"])
done

lemma injec_left_exact:"\<lbrakk>ring R; R module M; R module N; z \<in> mHom R (Zm R e) M; f \<in> mHom R M N; injec\<^sub>M\<^sub>,\<^sub>N f\<rbrakk> \<Longrightarrow> exact3 R (Zm R e) M N z f "
apply (simp add:exact3_def)
apply (simp add:Zm_def) apply (fold Zm_def)
 apply (simp add:Z_to_M_0 [of "R" "M" "z" "e"])
 apply (simp add:injec_def)
done

lemma injec_mHom_image:"\<lbrakk>ring R; R module N; R module M1; R module M2; x \<in> mHom R N M2; f \<in> mHom R M1 M2; x ` (carrier N) \<subseteq> f ` (carrier M1); injec\<^sub>M1\<^sub>,\<^sub>M2 f\<rbrakk>\<Longrightarrow>  (\<lambda>n \<in>(carrier N). (SOME m. (m \<in> carrier M1 \<and> x n = f m))) \<in> mHom R N M1 \<and> compos N f (\<lambda>n \<in> (carrier N). (SOME m. m \<in> carrier M1 \<and> x n = f m)) = x"
apply (subgoal_tac " (\<lambda>n\<in>carrier N. SOME m. m \<in> carrier M1 \<and> x n = f m) \<in> mHom R N M1") apply simp
apply (rule mHom_eq, assumption+)
 apply (simp add:mHom_compos) apply assumption
 apply (rule ballI)
 apply (simp add:compos_def compose_def)
 apply (thin_tac "(\<lambda>n\<in>carrier N. SOME m. m \<in> carrier M1 \<and> x n = f m) \<in> mHom R N M1")
 apply (frule_tac m = m in mHom_mem [of "R" "N" "M2" "x"], assumption+)
 apply (subgoal_tac "x m \<in> x ` carrier N")
 apply (frule_tac c = "x m" in subsetD [of "x ` carrier N" "f ` carrier M1"], assumption+)
 apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (thin_tac "\<exists>xa\<in>carrier M1. x m = f xa") apply (erule conjE)
 apply (rotate_tac -1) apply (frule sym) apply simp
 apply (simp add:image_def) apply blast
apply (simp add:mHom_def[of "R" "N" "M1"] aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (subgoal_tac "x xa \<in> f ` carrier M1") apply (simp add:image_def)
 apply (rule someI2_ex) apply blast apply simp
 apply (simp add:image_def) apply blast
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_pOp_closed)
 apply (simp add:sprod_mem)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule_tac x = a and y = b in ag_pOp_closed [of "N"], assumption+)
 apply (subgoal_tac "x (a +\<^sub>N b) \<in> x ` carrier N")
 apply (frule_tac c = "x ( a +\<^sub>N b)" in subsetD [of "x ` carrier N" "f ` carrier M1"], assumption+)
 apply (subgoal_tac "x a \<in> x ` carrier N")
 apply (frule_tac c = "x a" in subsetD [of "x ` carrier N" "f ` carrier M1"], assumption+)
 apply (subgoal_tac "x b \<in> x ` carrier N")
 apply (frule_tac c = "x b" in subsetD [of "x ` carrier N" "f ` carrier M1"], assumption+)
 apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (rule someI2_ex) apply blast
 apply (rule someI2_ex) apply blast
 apply (thin_tac "\<exists>xa\<in>carrier N. x ( a +\<^sub>N b) = x xa")
 apply (thin_tac "\<exists>xa\<in>carrier M1. x ( a +\<^sub>N b) = f xa")
 apply (thin_tac "\<exists>xa\<in>carrier N. x a = x xa")
 apply (thin_tac "\<exists>xa\<in>carrier M1. x a = f xa")
 apply (thin_tac "\<exists>xa\<in>carrier N. x b = x xa")
 apply (thin_tac "\<exists>xa\<in>carrier M1. x b = f xa")
 apply (erule conjE)+
 apply (subgoal_tac "f (xaa +\<^sub>M1 xa +\<^sub>M1 (-\<^sub>M1 xb)) = 0\<^sub>M2")
 apply (subgoal_tac "xaa +\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xb = 0\<^sub>M1")
 prefer 2  apply (simp add:injec_def)
 apply (erule conjE) apply (simp add:ker_def)
 apply (subgoal_tac "xaa +\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xb \<in> {a. a \<in> carrier M1 \<and> f a = 0\<^sub>M2}")
 apply simp apply (thin_tac "{a. a \<in> carrier M1 \<and> f a = 0\<^sub>M2} = {0\<^sub>M1}")
 apply simp
 apply (frule module_is_ag [of "R" "M1"], assumption+)
 apply (rule ag_pOp_closed, assumption+)+
 apply (frule_tac x = xb in ag_mOp_closed [of M1], assumption+)
 apply (frule module_is_ag [of "R" "M1"], assumption+)
 apply (frule_tac x = xaa and y = xa in ag_pOp_closed [of M1], assumption+)
 apply (subgoal_tac "xaa +\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xb +\<^sub>M1 xb = 0\<^sub>M1 +\<^sub>M1 xb")
 prefer 2 apply simp
 apply (thin_tac "xaa +\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xb = 0\<^sub>M1")
 apply (simp add:ag_l_zero [of "M1"])
 apply (frule_tac x = xb in ag_mOp_closed [of M1], assumption+)
 apply (frule_tac x = "xaa +\<^sub>M1 xa" and y = "-\<^sub>M1 xb" and z = "xb" in ag_pOp_assoc [of "M1"], assumption+)
 apply simp apply (thin_tac "xaa +\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xb +\<^sub>M1 xb = xb")
 apply (simp add:ag_l_inv1) apply (simp add:ag_r_zero)
 apply (subst  mHom_add [of "R" "M1" "M2" "f"], assumption+)
 apply (frule module_is_ag [of "R" "M1"], assumption)
 apply (rule ag_pOp_closed, assumption+)
 apply (frule module_is_ag [of "R" "M1"], assumption)
 apply (rule ag_mOp_closed[of "M1"], assumption+)
 apply (subst mHom_add [of "R" "M1" "M2" "f"], assumption+)
 apply (subst mHom_inv [of "R" "M1" "M2" _ "f"], assumption+)
 apply (frule_tac m= a and n = b in mHom_add[of "R" "N" "M2" "x"], assumption+)
 apply simp
 apply (frule module_is_ag [of "R" "M2"], assumption+)
 apply (rule ag_r_inv1[of "M2"], assumption+)
 apply (simp add:mHom_mem)
 apply (simp add:image_def) apply blast
 apply (simp add:image_def) apply blast
 apply (simp add:image_def) apply blast
apply (rule ballI)+
 apply (frule_tac a = a and m = m in sprod_mem [of "R" "N"], assumption+)
 apply (subgoal_tac "x (a \<star>\<^sub>N m) \<in> x ` carrier N")
 apply (frule_tac c = "x (a \<star>\<^sub>N m)" in subsetD [of "x ` carrier N" "f ` carrier M1"], assumption+)
 apply (subgoal_tac "x m \<in> x ` carrier N")
 apply (frule_tac c = "x m" in subsetD [of "x ` carrier N" "f ` carrier M1"], assumption+)
 apply (thin_tac "x ( a \<star>\<^sub>N m) \<in> x ` carrier N")
 apply (thin_tac "x m \<in> x ` carrier N")
 apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (rule someI2_ex) apply blast
 apply (thin_tac "\<exists>xa\<in>carrier M1. x m = f xa")
 apply (thin_tac "\<exists>xa\<in>carrier M1. x ( a \<star>\<^sub>N m) = f xa")
 apply (erule conjE)+
 apply (frule_tac m = m and a = a in mHom_lin [of "R" "N" "M2" _ "x"],
                assumption+)
 apply (subgoal_tac "f xaa = f (a \<star>\<^sub>M1 xa)")
  apply (rotate_tac -1) apply (frule sym) apply (thin_tac "f xaa = f ( a \<star>\<^sub>M1 xa)")
 apply (subgoal_tac "a \<star>\<^sub>M1 xa +\<^sub>M1 (-\<^sub>M1 xaa) \<in> ker\<^sub>M1\<^sub>,\<^sub>M2 f")
 apply (simp add:ker_def) apply (erule conjE) apply (simp add:injec_def)
 apply (erule conjE) apply (simp add:ker_def)
 apply (subgoal_tac "a \<star>\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xaa \<in> {a. a \<in> carrier M1 \<and> f a = 0\<^sub>M2}")
 prefer 2  apply (thin_tac "{a. a \<in> carrier M1 \<and> f a = 0\<^sub>M2} = {0\<^sub>M1}")
 apply simp apply simp
 apply (thin_tac "{y. \<exists>xa\<in>carrier N. y = x xa} \<subseteq> {y. \<exists>x\<in>carrier M1. y = f x}")
 apply (thin_tac "{a. a \<in> carrier M1 \<and> f a = 0\<^sub>M2} = {0\<^sub>M1}")
 apply (frule_tac a = a and m = xa in sprod_mem [of "R" "M1"], assumption+)
 apply (frule module_is_ag[of "R" "M1"], assumption+)
 apply (frule_tac x = xaa in ag_mOp_closed [of "M1"], assumption+)
 apply (subgoal_tac " a \<star>\<^sub>M1 xa +\<^sub>M1 (-\<^sub>M1 xaa) +\<^sub>M1 xaa = 0\<^sub>M1 +\<^sub>M1 xaa")
 prefer 2 apply simp apply (thin_tac "a \<star>\<^sub>M1 xa +\<^sub>M1 -\<^sub>M1 xaa = 0\<^sub>M1")
 apply (simp add:ag_l_zero)
 apply (simp add:ag_pOp_assoc) apply (simp add:ag_l_inv1)
 apply (simp add:ag_r_zero)
 apply (simp add:ker_def)
 apply (rule conjI)
 apply (frule module_is_ag[of "R" "M1"], assumption+)
 apply (rule ag_pOp_closed, assumption+)
 apply (simp add:sprod_mem)
 apply (frule module_is_ag[of "R" "M1"], assumption+)
 apply (rule ag_mOp_closed[of "M1"], assumption+)
 apply (subst mHom_add[of "R" "M1" "M2" "f"] , assumption+)
 apply (simp add:sprod_mem)
 apply (frule module_is_ag[of "R" "M1"], assumption+)
 apply (rule ag_mOp_closed, assumption+)
 apply (simp add: mHom_inv [of "R" "M1" "M2"])
 apply (frule module_is_ag[of "R" "M2"], assumption+)
 apply (rule ag_r_inv1, assumption+)
 apply (simp add:mHom_mem)
 apply (simp add:mHom_lin)
 apply (simp add:image_def) apply blast
 apply (simp add:image_def) apply blast
done

lemma right_exact_surjec:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
 p \<in> mHom R N (Zm R e); exact3 R M N (Zm R e) f p\<rbrakk> \<Longrightarrow> surjec\<^sub>M\<^sub>,\<^sub>N f"
apply (simp add:surjec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (simp add:surj_to_def)
apply (simp add:exact3_def)
 apply (simp add:M_to_Z_0)
done

lemma surjec_right_exact:"\<lbrakk>ring R; R module M; R module N; f \<in> mHom R M N;
 p \<in> mHom R N (Zm R e); surjec\<^sub>M\<^sub>,\<^sub>N f\<rbrakk> \<Longrightarrow> exact3 R M N (Zm R e) f p"
apply (simp add:exact3_def)
apply (simp add:ker_def)
apply (simp add:mHom_def [of "R" "N" _])
 apply (simp add:aHom_def)
 apply (simp add:Zm_def)
 apply (frule conj_1)
 apply (thin_tac "p \<in> carrier N \<rightarrow> {e} \<and> p \<in> extensional (carrier N) \<and>
  (\<forall>a\<in>carrier N. \<forall>b\<in>carrier N. p ( a +\<^sub>N b) = (if p a = e then \<lambda>y\<in>{e}. e
  else arbitrary) (p b)) \<and> (\<forall>a\<in>carrier R.
           \<forall>m\<in>carrier N. p ( a \<star>\<^sub>N m) = (if p m = e then e else arbitrary))")
 apply (subgoal_tac "{a. a \<in> carrier N \<and> p a = e} = carrier N")
 apply simp apply (simp add:surjec_def surj_to_def)
 apply (rule equalityI)
  apply (rule subsetI)
  apply simp
  apply (rule subsetI)
  apply simp
  apply (frule_tac x = x in funcset_mem [of "p" "carrier N" "{e}"],
                                                         assumption+)
  apply simp
done

lemma exact4_exact3:"\<lbrakk>ring R; R module M; R module N; z\<in>mHom R (Zm R e) M ; f \<in> mHom R M N; z1 \<in> mHom R N (Zm R e); exact4 R (Zm R e) M N (Zm R e) z f z1\<rbrakk> \<Longrightarrow>
exact3 R (Zm R e) M N z f \<and> exact3 R M N (Zm R e) f z1"
apply (simp add:exact4_def exact3_def)
done


lemma exact4_bijec:"\<lbrakk>ring R; R module M; R module N; z\<in>mHom R (Zm R e) M ; f \<in> mHom R M N; z1 \<in> mHom R N (Zm R e); exact4 R (Zm R e) M N (Zm R e) z f z1\<rbrakk> \<Longrightarrow>
 bijec\<^sub>M\<^sub>,\<^sub>N f"
apply (frule exact4_exact3 [of "R" "M" "N" "z" "e" "f" "z1"], assumption+)
 apply (erule conjE)
 apply (simp add:bijec_def)
 apply (simp add:left_exact_injec)
 apply (simp add:right_exact_surjec)
done

lemma exact_im_sub_ker:"\<lbrakk>ring R; R module L; R module M; R module N; f \<in> mHom R L M; g \<in> mHom R M N; z1 \<in> mHom R N (Zm R e); R module Z; exact4 R L M N (Zm R e) f g z1; x \<in> mHom R M Z; compos L x f = mzeromap L Z \<rbrakk> \<Longrightarrow> (\<lambda>z\<in>(carrier N). x (SOME y. y \<in> carrier M \<and> g y = z)) \<in> mHom R N Z"
apply (simplesubst mHom_def) apply simp
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply simp
apply (subgoal_tac "exact3 R M N (Zm R e) g z1")
prefer 2 apply (simp add:exact4_def exact3_def)
apply (frule right_exact_surjec [of "R" "M" "N" "g" "z1"], assumption+)
 apply (simp add:surjec_def) apply (frule conj_2)
 apply (simp add:surj_to_def) apply (erule conjE)
 apply (subgoal_tac "xa \<in> g ` (carrier M)")
 apply (thin_tac "g ` carrier M = carrier N") apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (erule conjE) apply (simp add: mHom_mem)
 apply simp
 apply (simp add:extensional_def)
apply (rule ballI)+
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (frule_tac x = a and y = b in ag_pOp_closed [of "N"], assumption+)
apply (subgoal_tac "exact3 R M N (Zm R e) g z1")
prefer 2 apply (simp add:exact4_def exact3_def)
apply (frule right_exact_surjec [of "R" "M" "N" "g" "z1"], assumption+)
 apply (simp add:surjec_def) apply (frule conj_2)
 apply (simp add:surj_to_def) apply (erule conjE)
 apply (subgoal_tac "a +\<^sub>N b \<in> g ` (carrier M)")
 apply (subgoal_tac "a \<in> g ` (carrier M)")
 apply (subgoal_tac "b \<in> g ` (carrier M)")
 prefer 2 apply simp apply (thin_tac "g ` carrier M = carrier N")
 prefer 2 apply simp
 prefer 2 apply simp
 apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (rule someI2_ex) apply blast
 apply (rule someI2_ex)
 apply (thin_tac "\<exists>x\<in>carrier M. a = g x") apply (thin_tac "\<exists>x\<in>carrier M. b = g x")
 apply (thin_tac "xa \<in> carrier M \<and> g xa = b")
 apply (thin_tac "xaa \<in> carrier M \<and> g xaa = a")
 apply (subgoal_tac "\<forall>x\<in>carrier M. a +\<^sub>N b = g x \<longrightarrow> (\<exists>aa. aa \<in> carrier M \<and> g aa =  a +\<^sub>N b)") apply blast apply (thin_tac "\<exists>x\<in>carrier M.  a +\<^sub>N b = g x")
 apply (rule ballI) apply (rule impI)
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "a +\<^sub>N b = g xb")
 apply blast
 apply (erule conjE)+
 apply (thin_tac "\<exists>x\<in>carrier M.  a +\<^sub>N b = g x")
 apply (thin_tac "\<exists>x\<in>carrier M. a = g x")
 apply (thin_tac "\<exists>x\<in>carrier M. b = g x")
 apply (subgoal_tac "(xaa +\<^sub>M xa +\<^sub>M (-\<^sub>M xb)) \<in> ker\<^sub>M\<^sub>,\<^sub>N g")
 apply (frule mzero_im_sub_ker [of "R" "L" "M" "Z" "f" "x"], assumption+)
 apply (simp add:exact4_def)
 apply (erule conjE)
 apply (frule_tac c = "xaa +\<^sub>M xa +\<^sub>M -\<^sub>M xb" in subsetD [of "ker\<^sub>M\<^sub>,\<^sub>N g" "ker\<^sub>M\<^sub>,\<^sub>Z x"], assumption+)
 apply (subgoal_tac "x (xaa +\<^sub>M xa +\<^sub>M (-\<^sub>M xb)) = 0\<^sub>Z")
 prefer 2 apply (simp add:ker_def)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = xaa and y = xa in ag_pOp_closed [of "M"], assumption+)
 apply (frule_tac x = xb in ag_mOp_closed [of "M"], assumption+)
 apply (frule_tac m = "xaa +\<^sub>M xa" and n = "-\<^sub>M xb" in mHom_add [of "R" "M" "Z" "x"], assumption+)
 apply simp
 apply (subgoal_tac "x ( xaa +\<^sub>M xa) +\<^sub>Z (x (-\<^sub>M xb)) +\<^sub>Z (x xb) = 0\<^sub>Z +\<^sub>Z (x xb)")
 prefer 2 apply simp
 apply (thin_tac " x (xaa +\<^sub>M xa +\<^sub>M (-\<^sub>M xb)) = 0\<^sub>Z")
 apply (frule module_is_ag [of "R" "Z"], assumption+)
 apply (frule_tac m = xb and f = x in mHom_mem [of "R" "M" "Z"], assumption+)
 apply (thin_tac "x (xaa +\<^sub>M xa) +\<^sub>Z (x (-\<^sub>M xb)) = 0\<^sub>Z")
 apply (simp add:ag_l_zero)
 apply (frule_tac m = "xaa +\<^sub>M xa" and f = x in mHom_mem [of "R" "M" "Z"], assumption+)
  apply (frule_tac m = "-\<^sub>M xb" and f = x in mHom_mem [of "R" "M" "Z"], assumption+)
 apply (simp add:ag_pOp_assoc [of "Z"])
 apply (simp add:mHom_inv)
 apply (simp add:ag_l_inv1) apply (simp add:ag_r_zero)
 apply (simp add:mHom_add)
apply (simp add:ker_def)
 apply (rule conjI)
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (rule ag_pOp_closed [of "M"], assumption+)
 apply (frule_tac x = xaa and y = xa in ag_pOp_closed[of "M"], assumption+)
 apply (frule_tac x = xb in ag_mOp_closed [of "M"], assumption+)
apply (frule module_is_ag[of "R" "M"], assumption+)
apply (frule_tac x = xaa and y = xa in ag_pOp_closed[of "M"], assumption+)
apply (frule_tac x = xb in ag_mOp_closed [of "M"], assumption+)
 apply (simp add:mHom_add)
 apply (simp add:mHom_inv)
 apply (simp add:ag_r_inv1[of "N"])
apply (rule ballI)+
 apply (frule_tac a = a and m = m in sprod_mem [of "R" "N"], assumption+)
 apply simp
 apply (subgoal_tac "surjec\<^sub>M\<^sub>,\<^sub>N g")
 apply (simp add:surjec_def) apply (frule conj_2) apply (fold surjec_def)
 apply (simp add:surj_to_def)
 apply (subgoal_tac "a \<star>\<^sub>N m \<in> g ` (carrier M)")
 apply (subgoal_tac "m \<in>  g ` (carrier M)")
 prefer 2 apply simp apply (thin_tac "g ` carrier M = carrier N")
 prefer 2 apply simp
 apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (rule someI2_ex)
 apply (thin_tac " \<exists>x\<in>carrier M. m = g x")
 apply (thin_tac "xa \<in> carrier M \<and> g xa = m")
 apply (subgoal_tac "\<forall>x\<in>carrier M.  a \<star>\<^sub>N m = g x \<longrightarrow>(\<exists>aa. aa \<in> carrier M \<and> g aa =  a \<star>\<^sub>N m)")
 apply blast apply (rule ballI) apply (rule impI) apply (rotate_tac -1)
 apply (frule sym) apply (thin_tac "a \<star>\<^sub>N m = g xaa") apply blast
 apply (thin_tac "\<exists>x\<in>carrier M.  a \<star>\<^sub>N m = g x")
 apply (thin_tac "\<exists>x\<in>carrier M. m = g x") apply (erule conjE)+
 apply (subgoal_tac "a \<star>\<^sub>M xa +\<^sub>M (-\<^sub>M xaa) \<in> ker\<^sub>M\<^sub>,\<^sub>N g")
 apply (frule mzero_im_sub_ker [of "R" "L" "M" "Z" "f" "x"], assumption+)
 apply (simp add:exact4_def)
 apply (frule_tac c = "a \<star>\<^sub>M xa +\<^sub>M -\<^sub>M xaa" in subsetD[of "ker\<^sub>M\<^sub>,\<^sub>N g" "ker\<^sub>M\<^sub>,\<^sub>Z x"],
                  assumption+)
 apply (thin_tac "a \<star>\<^sub>M xa +\<^sub>M -\<^sub>M xaa \<in> ker\<^sub>M\<^sub>,\<^sub>N g")
 apply (thin_tac "ker\<^sub>M\<^sub>,\<^sub>N g \<subseteq> ker\<^sub>M\<^sub>,\<^sub>Z x")
 apply (thin_tac " f ` carrier L = ker\<^sub>M\<^sub>,\<^sub>N g \<and> g ` carrier M = ker\<^sub>N\<^sub>,\<^sub>(Zm R e) z1")
 apply (subgoal_tac "x (a \<star>\<^sub>M xa +\<^sub>M -\<^sub>M xaa) = 0\<^sub>Z")
 apply (frule_tac a = a and m = xa in sprod_mem [of "R" "M"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = xaa in ag_mOp_closed [of "M"], assumption+)
 apply (simp add:mHom_add)
 apply (frule_tac  m = "-\<^sub>M xaa" and f = x in mHom_mem [of "R" "M" "Z"], assumption+)
 apply (frule_tac  m = "a \<star>\<^sub>M xa" and f = x in mHom_mem [of "R" "M" "Z"], assumption+)
 apply (frule_tac m = "xaa" and f = x in mHom_mem [of "R" "M" "Z"], assumption+)
 apply (subgoal_tac "x ( a \<star>\<^sub>M xa) +\<^sub>Z (x (-\<^sub>M xaa)) +\<^sub>Z (x xaa) = 0\<^sub>Z +\<^sub>Z (x xaa)")
 apply (thin_tac "x ( a \<star>\<^sub>M xa) +\<^sub>Z (x (-\<^sub>M xaa)) = 0\<^sub>Z")
 apply (frule module_is_ag [of "R" "Z"], assumption+)
 apply (simp add:ag_l_zero[of "Z"])
 apply (simp add:ag_pOp_assoc [of "Z"])
 apply (simp add:mHom_inv) apply (simp add:ag_l_inv1)
 apply (simp add:ag_r_zero)
 apply (simp add:mHom_lin)
 apply simp
 apply (simp add:ker_def)
 apply (simp add:ker_def)
 apply (rule conjI)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (rule ag_pOp_closed [of "M"], assumption+)
 apply (simp add:sprod_mem) apply (simp add:ag_mOp_closed)
 apply (frule_tac a = a and m = xa in sprod_mem [of "R" "M"], assumption+)
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = xaa in ag_mOp_closed [of "M"], assumption+)
 apply (simp add:mHom_add)
 apply (simp add:mHom_lin) apply (simp add:mHom_inv)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (simp add:ag_r_inv1)
 apply (rule right_exact_surjec [of "R" "M" "N" "g" "z1" "e"], assumption+)
 apply (simp add:exact4_def exact3_def)
done

    (*     f    g    z1
         L \<rightarrow> M \<rightarrow> N \<rightarrow> 0      exact4 L M N (Zm R e) f g z1, x \<in> mHom R M Z
               x\  | \<exists>x'       im f \<subseteq> ker x, then exists x'
                   Z        *)

lemma exact_im_sub_ker1:"\<lbrakk>ring R; R module L; R module M; R module N; f \<in> mHom R L M; g \<in> mHom R M N; z1 \<in> mHom R N (Zm R e); R module Z; exact4 R L M N (Zm R e) f g z1; x \<in> mHom R M Z; compos L x f = mzeromap L Z \<rbrakk> \<Longrightarrow>
compos M (\<lambda>z\<in>(carrier N). x (SOME y. y \<in> carrier M \<and> g y = z)) g = x"
apply (frule exact_im_sub_ker [of "R" "L" "M" "N" "f" "g" "z1" "e" "Z" "x"],
               assumption+)
apply (frule_tac g = "(\<lambda>z\<in>carrier N. x (SOME y. y \<in> carrier M \<and> g y = z))" in mHom_compos [of "R" "M" "N" "Z" "g"], assumption+)
apply (rule mHom_eq [of "R" "M" "Z" _ "x"], assumption+)
apply (rule ballI)
apply (subst compos_def) apply (subst compose_def) apply simp
apply (simp add:mHom_mem)
 apply (thin_tac "compos M (\<lambda>z\<in>carrier N. x (SOME y. y \<in> carrier M \<and> g y = z)) g \<in> mHom R M Z")
 apply (thin_tac "(\<lambda>z\<in>carrier N. x (SOME y. y \<in> carrier M \<and> g y = z)) \<in> mHom R N Z")
 apply (subgoal_tac "surjec\<^sub>M\<^sub>,\<^sub>N g")
 prefer 2
 apply (rule right_exact_surjec [of "R" "M" "N" "g" "z1" "e"], assumption+)
 apply (simp add:exact4_def exact3_def)
 apply (simp add:surjec_def) apply (frule conj_2)
 apply (fold surjec_def)
 apply (simp add:surj_to_def)
 apply (frule_tac m = m in mHom_mem [of "R" "M" "N" "g"], assumption+)
 apply (subgoal_tac "g m \<in> g ` (carrier M)") prefer 2 apply simp
 apply (thin_tac "g ` carrier M = carrier N")
 apply (simp add:image_def)
 apply (rule someI2_ex) apply blast
 apply (thin_tac "\<exists>x\<in>carrier M. g m = g x") apply (erule conjE)
 apply (subgoal_tac "xa +\<^sub>M (-\<^sub>M m) \<in> ker\<^sub>M\<^sub>,\<^sub>N g")
 apply (frule mzero_im_sub_ker [of "R" "L" "M" "Z" "f" "x"], assumption+)
 apply (simp add:exact4_def)
 apply (frule_tac c = "xa +\<^sub>M (-\<^sub>M m)" in subsetD[of "ker\<^sub>M\<^sub>,\<^sub>N g" "ker\<^sub>M\<^sub>,\<^sub>Z x"],
                  assumption+)
 apply (thin_tac "xa +\<^sub>M (-\<^sub>M m) \<in> ker\<^sub>M\<^sub>,\<^sub>N g")
 apply (subgoal_tac "x (xa +\<^sub>M (-\<^sub>M m)) = 0\<^sub>Z")
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (frule_tac x = m in ag_mOp_closed [of "M"], assumption+)
 apply (simp add:mHom_add)
 apply (subgoal_tac "x xa +\<^sub>Z (x (-\<^sub>M m)) +\<^sub>Z (x m) = 0\<^sub>Z +\<^sub>Z (x m)")
 apply (thin_tac " x xa +\<^sub>Z (x (-\<^sub>M m)) = 0\<^sub>Z")
 apply (frule_tac m = m in mHom_mem [of "R" "M" "Z" "x"], assumption+)
 apply (frule_tac m = "-\<^sub>M m" in mHom_mem [of "R" "M" "Z" "x"], assumption+)
 apply (frule_tac m = "xa" in mHom_mem [of "R" "M" "Z" "x"], assumption+)
 apply (frule module_is_ag [of "R" "Z"], assumption+)
 apply (simp add:ag_l_zero[of "Z"])
 apply (simp add:ag_pOp_assoc [of "Z"])
 apply (simp add:mHom_inv) apply (simp add:ag_l_inv1)
 apply (simp add:ag_r_zero)
 apply simp
 apply (simp add:ker_def)
apply (simp add:ker_def)
 apply (frule module_is_ag[of "R" "M"], assumption+)
 apply (frule_tac x = m in ag_mOp_closed [of "M"], assumption+)
 apply (simp add:ag_pOp_closed)
 apply (simp add:mHom_add)
 apply (simp add:mHom_inv)
 apply (frule_tac m = m in mHom_mem [of "R" "M" "N" "g"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (rule ag_r_inv1, assumption+)
done

constdefs
 module_iota::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme] \<Rightarrow> 'a \<Rightarrow> 'a"  ("(m\<iota>\<^sub>_ _)" [92, 93]92)
 "m\<iota>\<^sub>R M == \<lambda>x\<in>carrier M. x"

lemma short_exact_sequence:"\<lbrakk>ring R; R module M; submodule R M N; z\<in>mHom R (Zm R e) (mdl M N); z1 \<in> mHom R (M /\<^sub>m N) (Zm R e)\<rbrakk> \<Longrightarrow>  exact5 R (Zm R e) (mdl M N) M (M /\<^sub>m N) (Zm R e) z (m\<iota>\<^sub>R (mdl M N)) (mpj M N) z1"
apply (simp add:exact5_def)
apply (rule conjI)
 apply (simp add:Zm_def) apply (fold Zm_def)
 apply (frule mdl_is_module [of "R" "M" "N"], assumption+)
 apply (simp add:ker_def) apply (simp add:module_iota_def)
 apply (simp add:Z_to_M_0 [of "R" "mdl M N" "z"])
 apply (simp add:mdl_def) apply (fold mdl_def)
 apply (rule equalityI)
 apply simp
 apply (simp add:submodule_inc_0)
 apply (rule subsetI)
 apply (simp add:CollectI)
apply (rule conjI)
 apply (simp add:module_iota_def)
 apply (simp add:mdl_def) apply (fold mdl_def)
 apply (simp add:mker_of_mpj[THEN sym])
 apply (frule qmodule_module [of "R" "M" "N"], assumption+)
apply (subst M_to_Z_0 [of "R" "M /\<^sub>m N" "z1" "e"], assumption+)
 apply (frule mpj_surjec [of "R" "M" "N"], assumption+)
 apply (simp add:surjec_def surj_to_def)
done

lemma rexact4_lexact4_HOM:"\<lbrakk>ring R; R module M1; R module M2; R module M3;
f \<in> mHom R M1 M2; g \<in> mHom R M2 M3; z1 \<in> mHom R M3 (Zm R e); exact4 R M1 M2 M3(Zm R e) f g z1\<rbrakk> \<Longrightarrow> \<forall>N. R module N \<longrightarrow> exact4 R (HOM\<^sub>R (Zm R e) N) (HOM\<^sub>R M3 N) (HOM\<^sub>R M2 N) (HOM\<^sub>R M1 N) (sup_sharp R M3 (Zm R e) N z1) (sup_sharp R M2 M3 N g) (sup_sharp R M1 M2 N f)"

 (*              f     g    z1
             M1 \<rightarrow> M2 \<rightarrow> M3 \<rightarrow> (Zm R e)
                         |
                         N                     *)
apply (rule allI) apply (rule impI)
apply (subst exact4_def)
apply (rule conjI)
 apply (frule Zm_Module [of "R" "e"])
 apply (subst HOM_carrier [of "R" "Zm R e" ], assumption+)
 apply (simp add:mHom_Z_M)
 apply (simp add:sup_sharp_def)
 apply (simp add:mzeromap_mHom)
 apply (simp add:ker_def)
 apply (simp add:HOM_def)
 apply (rule equalityI)
 apply (rule subsetI)
 apply simp
 apply (frule_tac N = N in mzeromap_mHom [of "R" "Zm R e"], assumption+)
 apply (frule_tac N = N and g = "mzeromap (Zm R e) N" in mHom_compos [of "R" "M3" "Zm R e" _ "z1" _ ], assumption+)
 apply simp
 apply (frule_tac N = N and g = "compos M3 (mzeromap (Zm R e) N) z1" in mHom_compos [of "R" "M2" "M3" _ "g" _], assumption+)
 apply (frule_tac N = N in mzeromap_mHom [of "R" "M2"], assumption+)
 apply (rule_tac N = N and f = "compos M2 (compos M3 (mzeromap (Zm R e) N) z1) g" and g = "mzeromap M2 N" in mHom_eq [of "R" "M2"], assumption+)
apply (rule ballI)
 apply (simp add:compos_def mzeromap_def compose_def)
 apply (simp add:mHom_mem)+
 apply (rule subsetI)
 apply simp apply (erule conjE) apply simp
 apply (frule_tac N = N in mzeromap_mHom [of "R" "Zm R e"], assumption+)
 apply (frule_tac N = N and g = "mzeromap (Zm R e) N" in mHom_compos [of "R" "M3" "Zm R e" _ "z1"], assumption+)
 apply (rule_tac  N = N and f = x and g = "compos M3 (mzeromap (Zm R e) N) z1" in mHom_eq[of "R" "M3"], assumption+)
 apply (rule ballI)
 apply (subst compos_def) apply (subst compose_def)
 apply (subst mzeromap_def) apply (simp add:mHom_mem)
 apply (simp add:exact4_def)
 apply (subgoal_tac "exact3 R M2 M3 (Zm R e) g z1")
 prefer 2 apply (simp add:exact3_def)
 apply (frule right_exact_surjec [of "R" "M2" "M3"  "g" "z1"], assumption+)
 apply (simp add:surjec_def)
 apply (thin_tac "f ` carrier M1 = ker\<^sub>M2\<^sub>,\<^sub>M3 g \<and> g ` carrier M2 = ker\<^sub>M3\<^sub>,\<^sub>(Zm R e) z1")
 apply (erule conjE) apply (simp add:surj_to_def)
 apply (simp add:image_def)
 apply (subgoal_tac "m \<in> {y. \<exists>x\<in>carrier M2. y = g x}")
 apply (thin_tac "{y. \<exists>x\<in>carrier M2. y = g x} = carrier M3")
 prefer 2 apply simp apply simp
 apply (subgoal_tac "\<forall>y\<in>carrier M2. m = g y \<longrightarrow> x m = 0\<^sub>N")
 apply blast
 apply (rule ballI) apply (rule impI) apply simp
 apply (thin_tac "compos M3 (mzeromap (Zm R e) N) z1 \<in> mHom R M3 N")
 apply (thin_tac "\<exists>x\<in>carrier M2. g y = g x") apply (thin_tac "m = g y")
 apply (simp add:compos_def compose_def)
 apply (subgoal_tac "(\<lambda>xa\<in>carrier M2. x (g xa)) y = x ( g y)")
 apply (simp add:mzeromap_def) apply (thin_tac "(\<lambda>xa\<in>carrier M2. x (g xa)) = mzeromap M2 N")
 apply simp
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def)
 apply (simp add:ker_def)
 apply (simp add:HOM_carrier)
 apply (subgoal_tac "\<forall>xa\<in>mHom R M3 N. x = sup_sharp R M2 M3 N g xa \<longrightarrow>
  x \<in> mHom R M2 N \<and> sup_sharp R M1 M2 N f x = 0\<^sub>(HOM\<^sub>R M1 N)")
 apply blast apply (thin_tac "\<exists>xa\<in>mHom R M3 N. x = sup_sharp R M2 M3 N g xa")
 apply (rule ballI) apply (rule impI)
 apply (frule_tac L = N and f = xa in sup_sharp_homTr [of "R" "M2" "M3" _ "g"],
               assumption+)
 apply simp
 apply (frule_tac L = N and f = "sup_sharp R M2 M3 N g xa" in sup_sharp_homTr [of "R" "M1" "M2" _ "f"],
               assumption+)
 apply (rule_tac N = N and f = "sup_sharp R M1 M2 N f (sup_sharp R M2 M3 N g xa)" and g = "0\<^sub>(HOM\<^sub>R M1 N)" in mHom_eq [of "R" "M1"], assumption+)
 apply (simp add:HOM_def) apply (simp add:mzeromap_mHom)
apply (rule ballI)
 apply (subst sup_sharp_def)
 apply simp
 apply (subst compos_def) apply (subst compose_def)
 apply (subst sup_sharp_def) apply simp
 apply (subst compos_def) apply (subst compose_def) apply simp
 apply (simp add:mHom_mem)
 apply (subgoal_tac "exact3 R M1 M2 M3 f g")
 prefer 2 apply (simp add:exact4_def exact3_def)
 apply (frule_tac exact3_comp_0 [of "R" "M1" "M2" "M3" "f" "g"], assumption+)
 apply (simp add:compos_def compose_def)
 apply (frule exact3_comp_0 [of "R" "M1" "M2" "M3" "f" "g"], assumption+)
 apply (simp add:compos_def compose_def)
 apply (subgoal_tac "(\<lambda>x\<in>carrier M1. g (f x)) m = mzeromap M1 M3 m")
 prefer 2 apply simp
 apply (thin_tac "(\<lambda>x\<in>carrier M1. g (f x)) = mzeromap M1 M3")
 apply simp
 apply (simp add:HOM_def)
 apply (simp add:mzeromap_def) apply (simp add:mHom_0)
apply (rule subsetI)
 apply (simp add:ker_def)
 apply (erule conjE)
 apply (simp add:HOM_carrier)
 apply (simp add:HOM_def)
 apply (simp add:sup_sharp_def)
 apply (subgoal_tac "\<exists>h \<in> mHom R M3 N. x = compos M2 h g")
 apply (simp add:image_def)
 apply (frule_tac Z = N and x = x in  exact_im_sub_ker1 [of "R" "M1" "M2" "M3" "f" "g" "z1" "e"], assumption+)
 apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "compos M2 (\<lambda>z\<in>carrier M3. x (SOME y. y \<in> carrier M2 \<and> g y = z)) g = x")
 apply (frule_tac Z = N and x = x in exact_im_sub_ker [of "R" "M1" "M2" "M3" "f" "g" "z1" "e"], assumption+)
 apply blast
done


lemma exact_HOM_exactTr:" \<lbrakk>f \<in> mHom (R:: ('r, 'm) RingType_scheme) M1 M2; g \<in> mHom R M2 M3; z1 \<in> mHom R M3 (Zm R e); R module (NV::('a, 'r) ModuleType); \<forall>(N::('a, 'r) ModuleType). R module N \<longrightarrow> exact4 R (HOM\<^sub>R (Zm R e) N) (HOM\<^sub>R M3 N) (HOM\<^sub>R M2 N) (HOM\<^sub>R M1 N) (sup_sharp R M3 (Zm R e) N z1) (sup_sharp R M2 M3 N g) (sup_sharp R M1 M2 N f); R module L\<rbrakk> \<Longrightarrow> exact4 R (HOM\<^sub>R (Zm R e) (L::('a, 'r) ModuleType)) (HOM\<^sub>R M3 L) (HOM\<^sub>R M2 L) (HOM\<^sub>R M1 L) (sup_sharp R M3 (Zm R e) L z1) (sup_sharp R M2 M3 L g) (sup_sharp R M1 M2 L f)"
apply simp
done
(*
lemma exact_HOM_exact:"\<lbrakk>ring (R:: ('r, 'm) RingType_scheme); R module M1; R module M2; R module M3; f \<in> mHom R M1 M2; g \<in> mHom R M2 M3; z1 \<in> mHom R M3 (Zm R e); R module (NV::('g, 'r) ModuleType); \<forall>(N::('g, 'r) ModuleType). R module N \<longrightarrow> exact4 R (HOM\<^sub>R (Zm R e) N) (HOM\<^sub>R M3 N) (HOM\<^sub>R M2 N) (HOM\<^sub>R M1 N) (sup_sharp R M3 (Zm R e) N z1) (sup_sharp R M2 M3 N g) (sup_sharp R M1 M2 N f) \<rbrakk> \<Longrightarrow> exact4 R M1 M2 M3 (Zm R e) f g z1"
apply (subst exact4_def)
apply (subgoal_tac "surjec\<^sub>M2\<^sub>,\<^sub>M3 g")
 apply (frule surjec_right_exact [of "R" "M2" "M3" "g" "z1" "e"], assumption+)
 apply (simp add:exact3_def)
prefer 2
apply (frule img_set_submodule [of "R" "M2" "M3" "g"], assumption+)
apply (frule qmodule_module [of "R" "M3" "g ` carrier M2"], assumption+)
apply (subgoal_tac "exact4 R (HOM\<^sub>R (Zm R e) (M3 /\<^sub>m (g ` carrier M2))) (HOM\<^sub>R M3 (M3 /\<^sub>m (g ` carrier M2))) (HOM\<^sub>R M2 (M3 /\<^sub>m (g ` carrier M2))) (HOM\<^sub>R M1 (M3 /\<^sub>m (g ` carrier M2))) (sup_sharp R M3 (Zm R e) (M3 /\<^sub>m (g ` carrier M2)) z1) (sup_sharp R M2 M3 (M3 /\<^sub>m (g ` carrier M2)) g) (sup_sharp R M1 M2 (M3 /\<^sub>m (g ` carrier M2)) f)")
prefer 2
 apply (thin_tac "submodule R M3 (g ` carrier M2)")
 apply (thin_tac "ring R") apply (thin_tac "R module M1")
 apply (thin_tac " R module M2") apply (thin_tac "R module M3")
apply blast ML "reset show_types"
apply (rule allI)
 apply (rule impI)
 apply simp     ????????????
*)

lemma lexact4_rexact4_HOM:"\<lbrakk>ring R; R module M1; R module M2; R module M3;
f \<in> mHom R M1 M2; g \<in> mHom R M2 M3; z \<in> mHom R (Zm R e) M1; exact4 R (Zm R e) M1 M2 M3 z f g \<rbrakk> \<Longrightarrow> \<forall>N. R module N \<longrightarrow> exact4 R (HOM\<^sub>R N (Zm R e)) (HOM\<^sub>R N M1) (HOM\<^sub>R N M2) (HOM\<^sub>R N M3) (sub_sharp R N (Zm R e) M1 z) (sub_sharp R N M1 M2 f) (sub_sharp R N M2 M3 g)"

 (*
                        N
                     z  |   f     g
            (Zm R e) \<rightarrow> M1 \<rightarrow> M2 \<rightarrow> M3  *)
apply (rule allI) apply (rule impI)
apply (subst exact4_def)
apply (rule conjI)
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def)
 apply (simp add:HOM_def) apply (fold HOM_def)
 apply (subgoal_tac "\<forall>xa\<in>mHom R N (Zm R e). x = sub_sharp R N (Zm R e) M1 z xa \<longrightarrow> x \<in> ker\<^sub>(HOM\<^sub>R N M1)\<^sub>,\<^sub>(HOM\<^sub>R N M2) (sub_sharp R N M1 M2 f)")
 apply blast
 apply (thin_tac "\<exists>xa\<in>mHom R N (Zm R e). x = sub_sharp R N (Zm R e) M1 z xa")
 apply (rule ballI) apply (rule impI)
 apply (simp add:ker_def) apply (simp add:HOM_def)
 apply (simp add:sub_sharp_def)
 apply (frule Zm_Module[of "R" "e"])
 apply (simp add:mHom_compos)
 apply (frule_tac L = N and f = xa in mHom_compos [of "R" _ "Zm R e" "M1" _ "z"], assumption+)
 apply (frule_tac L = N and f = "compos N z xa" in mHom_compos [of "R" _ "M1" "M2" _ "f"], assumption+)
 apply (frule_tac M = N in mzeromap_mHom [of "R" _ "M2"], assumption+)
 apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:mzeromap_def) apply (simp add:compos_def compose_def)
  apply (frule_tac M = N and f = xa and m = m in mHom_mem [of "R" _ "Zm R e"],
                            assumption+)
 apply (simp add:exact4_def)
 apply (frule conj_1) apply (thin_tac "z ` carrier (Zm R e) = ker\<^sub>M1\<^sub>,\<^sub>M2 f \<and> f ` carrier M1 = ker\<^sub>M2\<^sub>,\<^sub>M3 g")
 apply (simp add:image_def)
 apply (subgoal_tac "z (xa m) \<in> {y. \<exists>x\<in>carrier (Zm R e). y = z x}")
 prefer 2 apply (thin_tac "{y. \<exists>x\<in>carrier (Zm R e). y = z x} = ker\<^sub>M1\<^sub>,\<^sub>M2 f")
 apply simp apply blast apply simp apply (simp add:ker_def)
apply (rule subsetI)
 apply (simp add:ker_def) apply (simp add:HOM_def)
 apply (erule conjE)
 apply (frule_tac M = N in mHom_to_zero [of "R" _ "e"], assumption+)
 apply simp apply (simp add:sub_sharp_def)
 apply (simp add:exact4_def) apply (frule conj_1)
 apply (thin_tac "z ` carrier (Zm R e) = ker\<^sub>M1\<^sub>,\<^sub>M2 f \<and>
             f ` carrier M1 = ker\<^sub>M2\<^sub>,\<^sub>M3 g")
 apply (simp add:Zm_def) apply (fold Zm_def)
 apply (frule_tac L = N and f = x in mzero_im_sub_ker [of "R" _ "M1" "M2" _ "f"], assumption+) apply (rotate_tac -2) apply (frule sym)
 apply (thin_tac "{z e} = ker\<^sub>M1\<^sub>,\<^sub>M2 f") apply simp
 apply (subgoal_tac "mzeromap N (Zm R e) \<in> mHom R N (Zm R e)")
 prefer 2  apply simp
 apply (frule_tac L = N and f = "mzeromap N (Zm R e)" in mHom_compos [of "R" _ "Zm R e" "M1" _ "z" ], assumption+)
 apply (simp add:Zm_Module) apply assumption+
 apply (rule mHom_eq, assumption+) apply (rule ballI)
 apply (simp add:compos_def compose_def mzeromap_def)
 apply (simp add:Zm_def) apply (fold Zm_def)
 apply (subgoal_tac "x m \<in> x ` carrier N")
 apply (frule_tac c = "x m" and A = "x ` carrier N" and B = "{z e}" in
                      subsetD, assumption+)  apply simp
 apply (simp add:image_def) apply blast
apply (simp add:ker_def) apply (simp add:HOM_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>mHom R N M1. x = sub_sharp R N M1 M2 f xa \<longrightarrow>
 x \<in> mHom R N M2 \<and> sub_sharp R N M2 M3 g x = mzeromap N M3")
 apply blast apply (thin_tac "\<exists>xa\<in>mHom R N M1. x = sub_sharp R N M1 M2 f xa")
 apply (rule ballI) apply (rule impI)
 apply (simp add:sub_sharp_def)
 apply (frule_tac L = N and f = xa in mHom_compos [of "R" _ "M1" "M2" _ "f"],
                              assumption+) apply simp
 apply (frule_tac L = N and f = "compos N f xa" in mHom_compos [of "R" _ "M2"
 "M3" _ "g"], assumption+)
 apply (rule mHom_eq, assumption+)
 apply (simp add:mzeromap_mHom)
 apply (rule ballI)
 apply (simp add:compos_def compose_def mzeromap_def)
 apply (thin_tac " x = (\<lambda>x\<in>carrier N. f (xa x))")
 apply (thin_tac "(\<lambda>x\<in>carrier N. f (xa x)) \<in> mHom R N M2")
 apply (thin_tac "(\<lambda>x\<in>carrier N. g (if x \<in> carrier N then f (xa x) else arbitrary)) \<in> mHom R N M3")
 apply (frule_tac M = N and f = xa and m = m in mHom_mem [of "R" _ "M1"], assumption+)
 apply (simp add:exact4_def) apply (frule conj_2)
 apply (thin_tac "z ` carrier (Zm R e) = ker\<^sub>M1\<^sub>,\<^sub>M2 f \<and> f ` carrier M1 = ker\<^sub>M2\<^sub>,\<^sub>M3 g")
 apply (subgoal_tac "f (xa m) \<in> f ` carrier M1") apply simp
 apply (simp add:ker_def) apply (thin_tac "f ` carrier M1 = ker\<^sub>M2\<^sub>,\<^sub>M3 g")
 apply (simp add:image_def) apply blast
 apply (rule subsetI)
 apply simp apply (erule conjE)
 apply (simp add:image_def) apply (simp add:sub_sharp_def)
 apply (frule_tac L = N and f = x in  mzero_im_sub_ker [of "R" _ "M2" "M3" _ "g"], assumption+)
 apply (simp add:exact4_def)
 apply (frule conj_2) apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "f ` carrier M1 = ker\<^sub>M2\<^sub>,\<^sub>M3 g")
 apply simp apply (thin_tac "ker\<^sub>M2\<^sub>,\<^sub>M3 g = f ` carrier M1")
 apply (frule left_exact_injec [of "R" "M1" "M2" "z" "e" "f"], assumption+)
 apply (simp add:exact3_def exact4_def)
 apply (frule_tac N = N and x = x in injec_mHom_image [of "R" _ "M1" "M2" _ "f" ], assumption+)
 apply (erule conjE) apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "compos N f (\<lambda>n\<in>carrier N. SOME m. m \<in> carrier M1 \<and> x n = f m) = x")
 apply blast
done

(* Now, we cannot prove following because of type problem
lemma l_exact4_HOM_lexact4:"\<lbrakk>ring R; R module M1; R module M2; R module M3; f \<in> mHom R M1 M2;
   g \<in> mHom R M2 M3; z \<in> mHom R (Zm R e) M1;
   \<forall>N. R module N \<longrightarrow>
       exact4 R (HOM\<^sub>R N Zm R e) (HOM\<^sub>R N M1) (HOM\<^sub>R N M2) (HOM\<^sub>R N M3)
        (sub_sharp R N (Zm R e) M1 z) (sub_sharp R N M1 M2 f)
        (sub_sharp R N M2 M3 g)\<rbrakk>
\<Longrightarrow> exact4 R (Zm R e) M1 M2 M3 z f g" *)

(*
lemma exact_coker:"\<lbrakk>ring R; R module M1; R module M2; R module M3; z \<in> mHom R (Zm R e) M1; f \<in> mHom R M1 M2; g \<in> mHom R M2 M3; z1 \<in> mHom R M3 (Zm R ee);  R module N1; R module N2; R module N3; h \<in> mHom R N1 N2; i \<in> mHom R N2 N3; exact5 (Zm R e) M1 M2 M3 (Zm R ee) z f g z1: exact5 (Zm R u) N1 N2 N3 (Zm R uu) z h i z1: f1 \<in> mHom R M1 N1; f2 \<in> mHom R M2 N2; f3 \<in> mHom R M3 N3; compos m1 f2 f = compos M1 h f1; compos M2 f3 g = compos M2 i f2\<rbrakk> \<Longrightarrow> exact8 (Zm R e) (mdl M1 (ker\<^sub>M1\<^sub>,\<^sub>N1 f1)) (mdl M2 (ker\<^sub>M2\<^sub>,\<^sub>N2 f2)) (mdl M3 (ker\<^sub>M3\<^sub>,\<^sub>N3 f3)) (N1 /\<^sub>m (f1 ` (carrier M1))) (N2 /\<^sub>m (f2 ` (carrier M2))) (N3 /\<^sub>m (f3 ` (carrier M3))) z f g zz hh ii zz1 "


constdefs *)

section "9. Tensor product"

constdefs
 prod_carr::"[('a, 'r, 'm) ModuleType_scheme, ('b, 'r, 'm) ModuleType_scheme]
 \<Rightarrow> ('a * 'b) set" (infixl "\<times>\<^sub>c" 100)
 "M \<times>\<^sub>c N == (carrier M) \<times> (carrier N)"

constdefs
 bilinear_map::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme,  ('b, 'r, 'm1) ModuleType_scheme, ('c, 'r, 'm1) ModuleType_scheme, 'a * 'b \<Rightarrow> 'c] \<Rightarrow> bool"
 "bilinear_map R M1 M2 N f == f \<in> M1 \<times>\<^sub>c M2 \<rightarrow> carrier N \<and> f \<in> extensional (M1 \<times>\<^sub>c M2) \<and> (\<forall>x1 \<in> carrier M1. \<forall>x2 \<in> carrier M1. \<forall>y\<in>carrier M2.(f (x1 +\<^sub>M1 x2, y) = f (x1, y) +\<^sub>N (f (x2, y)))) \<and> (\<forall>x\<in>carrier M1. \<forall>y1\<in>carrier M2. \<forall>y2\<in>carrier M2. f (x, y1 +\<^sub>M2 y2) = f (x, y1) +\<^sub>N (f (x, y2))) \<and> (\<forall>x\<in>carrier M1. \<forall>y\<in>carrier M2. \<forall>r\<in>carrier R. f (r \<star>\<^sub>M1 x, y) = r \<star>\<^sub>N (f (x, y)) \<and> f (x, r \<star>\<^sub>M2 y) = r \<star>\<^sub>N (f (x, y)))"

lemma prod_carr_mem:"\<lbrakk>ring R; R module M; R module N; m\<in>carrier M; n\<in>carrier N\<rbrakk> \<Longrightarrow> (m, n) \<in> M \<times>\<^sub>c N"
apply (simp add:prod_carr_def)
done

lemma bilinear_mem:"\<lbrakk>ring R; R module M1; R module M2; R module N; m1 \<in> carrier M1; m2 \<in> carrier M2; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (m1, m2) \<in> carrier N"
apply (simp add:bilinear_map_def) apply (erule conjE)+
apply (rule funcset_mem [of "f" "M1 \<times>\<^sub>c M2" "carrier N"], assumption+)
apply (simp add:prod_carr_def)
done

lemma bilinear_l_add:"\<lbrakk>ring R; R module M1; R module M2; R module N; m11 \<in> carrier M1; m12 \<in> carrier M1; m2 \<in> carrier M2; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (m11 +\<^sub>M1 m12, m2) = f (m11, m2) +\<^sub>N (f (m12, m2))"
apply (simp add:bilinear_map_def)
done

lemma bilinear_r_add:"\<lbrakk>ring R; R module M1; R module M2; R module N; m \<in> carrier M1; m21 \<in> carrier M2; m22 \<in> carrier M2; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (m, m21 +\<^sub>M2 m22) = f (m, m21) +\<^sub>N (f (m, m22))"
apply (simp add:bilinear_map_def)
done

lemma bilinear_l_lin:"\<lbrakk>ring R; R module M1; R module M2; R module N; m1 \<in> carrier M1; m2 \<in> carrier M2; r \<in> carrier R; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (r \<star>\<^sub>M1 m1, m2) = r \<star>\<^sub>N (f (m1, m2))"
apply (simp add:bilinear_map_def)
done

lemma bilinear_r_lin:"\<lbrakk>ring R; R module M1; R module M2; R module N; m1 \<in> carrier M1; m2 \<in> carrier M2; r \<in> carrier R; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (m1, r \<star>\<^sub>M2 m2) = r \<star>\<^sub>N (f (m1, m2))"
apply (simp add:bilinear_map_def)
done

lemma bilinear_l_0:"\<lbrakk>ring R; R module M1; R module M2; R module N; m2 \<in> carrier M2; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (0\<^sub>M1, m2) = 0\<^sub>N"
apply (frule module_inc_zero [of "R" "M1"], assumption+)
apply (frule bilinear_l_add [of "R" "M1" "M2" "N" "0\<^sub>M1" "0\<^sub>M1" "m2" "f"],
  assumption+)
  apply (frule module_is_ag [of "R" "M1"], assumption+)
 apply (simp add:ag_l_zero)
 apply (frule bilinear_mem [of "R" "M1" "M2" "N" "0\<^sub>M1" "m2" "f"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (frule ag_eq_sol1 [of "N" "f (0\<^sub>M1, m2)" "f (0\<^sub>M1, m2)" "f (0\<^sub>M1, m2)"], assumption+)
 apply (rule sym, assumption+)
apply (simp add:ag_l_inv1)
done

lemma bilinear_r_0:"\<lbrakk>ring R; R module M1; R module M2; R module N; m1 \<in> carrier M1; bilinear_map R M1 M2 N f\<rbrakk> \<Longrightarrow> f (m1, 0\<^sub>M2) = 0\<^sub>N"
apply (frule module_inc_zero [of "R" "M2"], assumption+)
apply (frule bilinear_r_add [of "R" "M1" "M2" "N" "m1" "0\<^sub>M2" "0\<^sub>M2"  "f"],
  assumption+)
  apply (frule module_is_ag [of "R" "M2"], assumption+)
 apply (simp add:ag_l_zero)
 apply (frule bilinear_mem [of "R" "M1" "M2" "N" "m1" "0\<^sub>M2" "f"], assumption+)
 apply (frule module_is_ag [of "R" "N"], assumption+)
 apply (frule ag_eq_sol1 [of "N" "f (m1, 0\<^sub>M2)" "f (m1, 0\<^sub>M2)" "f (m1, 0\<^sub>M2)"], assumption+)
 apply (rule sym, assumption+)
apply (simp add:ag_l_inv1)
done

constdefs
 universal_property::"[('r, 'm) RingType_scheme, ('a, 'r, 'm1) ModuleType_scheme, ('b, 'r, 'm1) ModuleType_scheme, ('c, 'r, 'm1) ModuleType_scheme, 'a * 'b \<Rightarrow>'c] \<Rightarrow> bool"
 "universal_property (R::('r, 'm) RingType_scheme) (M:: ('a, 'r, 'm1) ModuleType_scheme) (N:: ('b, 'r, 'm1) ModuleType_scheme) (MN::('c, 'r, 'm1) ModuleType_scheme) (f:: 'a * 'b \<Rightarrow> 'c) == (bilinear_map R M N MN f) \<and> (\<forall>(Z :: ('c, 'r, 'm1) ModuleType_scheme). \<forall>(g :: 'a * 'b \<Rightarrow> 'c). (R module Z) \<and> (bilinear_map R M N Z g) \<longrightarrow>  ((\<exists>!h. (h \<in> mHom R MN Z) \<and> (compose (M \<times>\<^sub>c N) h f = g))))"

(* universal_property R MV M N MN f *)

lemma tensor_prod_uniqueTr:"\<lbrakk> ring (R:: ('r, 'm) RingType_scheme); R module (M :: ('a, 'r, 'm1) ModuleType_scheme); R module (N:: ('b, 'r, 'm1) ModuleType_scheme); R module (MN:: ('c, 'r, 'm1) ModuleType_scheme); R module (MN1::('c, 'r, 'm1) ModuleType_scheme); universal_property R M N MN f; universal_property R M N MN1 g\<rbrakk> \<Longrightarrow>\<exists>!k. k \<in> mHom R MN1 MN \<and>  compose (M \<times>\<^sub>c N) k g = f"
apply (simp add: universal_property_def [of  _ _ _ _ "f"])
 apply (frule conj_1) apply (fold universal_property_def)
 apply (simp add:universal_property_def [of _ _ _ _ "g"])
done

lemma tensor_prod_unique:"\<lbrakk> ring (R:: ('r, 'm) RingType_scheme); R module (M :: ('a, 'r, 'm1) ModuleType_scheme); R module (N:: ('b, 'r, 'm1) ModuleType_scheme); R module (MN:: ('c, 'r, 'm1) ModuleType_scheme); R module (MN1::('c, 'r, 'm1) ModuleType_scheme); universal_property R M N MN f; universal_property R M N MN1 g\<rbrakk> \<Longrightarrow> MN  \<cong>\<^sub>R MN1"
apply (frule tensor_prod_uniqueTr [of "R" "M" "N" "MN" "MN1" "f" "g"], assumption+)
apply (erule ex1E)
 apply (thin_tac "\<forall>y. y \<in> mHom R MN1 MN \<and> compose (M \<times>\<^sub>c N) y g = f \<longrightarrow> y = k")
apply (frule tensor_prod_uniqueTr [of "R" "M" "N" "MN1" "MN" "g" "f"], assumption+)
apply (erule ex1E)
apply (thin_tac "\<forall>y. y \<in> mHom R MN MN1 \<and> compose (M \<times>\<^sub>c N) y f = g \<longrightarrow> y = ka")
apply (erule conjE)+
apply (rename_tac k h)
 apply (subgoal_tac "k \<in> carrier MN1 \<rightarrow> carrier MN")
 prefer 2 apply (simp add:mHom_def aHom_def)
 apply (subgoal_tac "f \<in> (M \<times>\<^sub>c N) \<rightarrow> (carrier MN)")
 prefer 2 apply (simp add:universal_property_def bilinear_map_def)
 apply (subgoal_tac "h \<in> (carrier MN) \<rightarrow> (carrier MN1)")
 prefer 2 apply (simp add:mHom_def aHom_def)
 apply (frule_tac  g = h and h = k in compose_assoc [of "f" "M \<times>\<^sub>c N" "carrier MN" _ "carrier MN1" _ "carrier MN"], assumption+)
 apply simp
 apply (subgoal_tac "g \<in> (M \<times>\<^sub>c N) \<rightarrow> (carrier MN1)")
 prefer 2 apply (simp add:universal_property_def bilinear_map_def)
 apply (frule_tac g = k and h = h in compose_assoc [of "g" "M \<times>\<^sub>c N" "carrier MN1" _ "carrier MN" _ "carrier MN1"], assumption+)
 apply simp
 apply (subgoal_tac "compose (M \<times>\<^sub>c N) (mId\<^sub>MN) f = f")
 prefer 2
 apply (frule mId_mHom [of "R" "MN"], assumption+)
 apply (subgoal_tac "mId\<^sub>MN  \<in> carrier MN \<rightarrow> carrier MN")
 prefer 2 apply (simp add:mHom_def aHom_def)
apply (frule  composition [of "f" "M \<times>\<^sub>c N" "carrier MN" "mId\<^sub>MN" "carrier MN"], assumption+)
apply (rule funcset_eq [of _ "M \<times>\<^sub>c N"] )
 apply (simp add:compose_def restrict_def extensional_def)
 apply (simp add:universal_property_def bilinear_map_def)
apply (rule ballI)
 apply (simp add:compose_def mId_def)
 apply (simp add:funcset_mem) apply (rotate_tac -4)
 apply (frule sym) apply (thin_tac "f = compose (M \<times>\<^sub>c N) (compose (carrier MN) k h) f")
 apply (subgoal_tac "(compose (carrier MN) k h) = mId\<^sub>MN")
 apply (subgoal_tac "(compose (carrier MN1) h k) = (mId\<^sub>MN1)")
 apply (simp add:misomorphic_def)
 apply (frule_tac f = h and g = k in mHom_mId_bijec [of "R" "MN" "MN1"],
            assumption+)
 apply blast  (* compose (carrier MN1) h k = mId\<^sub>MN1 *)
 apply (subgoal_tac "compose (M \<times>\<^sub>c N) (mId\<^sub>MN1) g = g")
 prefer 2
 apply (frule mId_mHom [of "R" "MN1"], assumption+)
 apply (subgoal_tac "mId\<^sub>MN1  \<in> carrier MN1 \<rightarrow> carrier MN1")
 prefer 2 apply (simp add:mHom_def aHom_def)
apply (frule  composition [of "g" "M \<times>\<^sub>c N" "carrier MN1" "mId\<^sub>MN1" "carrier MN1"], assumption+)
apply (rule funcset_eq [of _ "M \<times>\<^sub>c N"] )
 apply (simp add:compose_def restrict_def extensional_def)
 apply (simp add:universal_property_def bilinear_map_def)
apply (rule ballI)
 apply (simp add:compose_def mId_def)
 apply (simp add:funcset_mem)
 apply (frule sym) apply (thin_tac "g = compose (M \<times>\<^sub>c N) (compose (carrier MN1) h k) g")
apply (frule tensor_prod_uniqueTr [of "R" "M" "N" "MN1" "MN1" "g" "g"], assumption+)
 apply (erule ex1E)
 apply (frule mId_mHom [of "R" "MN1"], assumption+)
 apply (subgoal_tac "mId\<^sub>MN1 = ka") prefer 2
  apply (thin_tac "compose (M \<times>\<^sub>c N) k g = f")
  apply (thin_tac "compose (M \<times>\<^sub>c N) h f = g")
  apply (thin_tac "compose (M \<times>\<^sub>c N) (compose (carrier MN) k h) f = f")
  apply (thin_tac "compose (carrier MN) k h = mId\<^sub>MN ")
  apply (thin_tac "ka \<in> mHom R MN1 MN1 \<and> compose (M \<times>\<^sub>c N) ka g = g")
  apply (thin_tac "compose (M \<times>\<^sub>c N) (compose (carrier MN1) h k) g = g")
 apply blast
 apply (subgoal_tac "compose (carrier MN1) h k = ka")
 apply (thin_tac "k \<in> mHom R MN1 MN")
 apply (thin_tac "compose (M \<times>\<^sub>c N) k g = f")
 apply (thin_tac "compose (M \<times>\<^sub>c N) h f = g")
 apply (thin_tac "k \<in> carrier MN1 \<rightarrow> carrier MN")
 apply (thin_tac "f \<in> M \<times>\<^sub>c N \<rightarrow> carrier MN")
 apply (thin_tac "h \<in> carrier MN \<rightarrow> carrier MN1")
 apply (thin_tac "compose (M \<times>\<^sub>c N) (compose (carrier MN) k h) f = f")
 apply (thin_tac "compose (carrier MN) k h = mId\<^sub>MN")
 apply (thin_tac "compose (M \<times>\<^sub>c N) (mId\<^sub>MN1 ) g = g")
 apply (thin_tac "compose (M \<times>\<^sub>c N) (compose (carrier MN1) h k) g = g")
 apply (thin_tac "ka \<in> mHom R MN1 MN1 \<and> compose (M \<times>\<^sub>c N) ka g = g")
 apply (thin_tac "\<forall>y. y \<in> mHom R MN1 MN1 \<and> compose (M \<times>\<^sub>c N) y g = g \<longrightarrow> y = ka")
 apply simp
 apply (thin_tac "mId\<^sub>MN1  \<in> mHom R MN1 MN1")
 apply (thin_tac "compose (M \<times>\<^sub>c N) (mId\<^sub>MN1 ) g = g")
 apply (thin_tac "ka \<in> mHom R MN1 MN1 \<and> compose (M \<times>\<^sub>c N) ka g = g")
 apply (thin_tac "mId\<^sub>MN1  = ka")
 apply (subgoal_tac "(compose (carrier MN1) h k) \<in> mHom R MN1 MN1")
 apply simp
apply (thin_tac "\<forall>y. y \<in> mHom R MN1 MN1 \<and> compose (M \<times>\<^sub>c N) y g = g \<longrightarrow> y = ka")

 apply (frule_tac f = k and g = h in  mHom_compos[of "R" "MN1" "MN" "MN1"],
                        assumption+)
 apply (simp add:compos_def)  (** compose (carrier MN1) h k = mId\<^sub>MN1 done **)
  (* compose (carrier MN) k h = mId\<^sub>MN *)
 apply (frule mId_mHom [of "R" "MN"], assumption+)
 apply (subgoal_tac "compose (M \<times>\<^sub>c N) (mId\<^sub>MN) f = f")
 prefer 2
 apply (subgoal_tac "mId\<^sub>MN  \<in> carrier MN \<rightarrow> carrier MN")
 prefer 2 apply (simp add:mHom_def aHom_def)
apply (frule  composition [of "f" "M \<times>\<^sub>c N" "carrier MN" "mId\<^sub>MN" "carrier MN"], assumption+)
apply (frule tensor_prod_uniqueTr [of "R" "M" "N" "MN" "MN" "f" "f"], assumption+)
 apply (erule ex1E)
 apply (subgoal_tac "mId\<^sub>MN = ka") prefer 2
  apply (thin_tac "compose (M \<times>\<^sub>c N) k g = f")
  apply (thin_tac "compose (M \<times>\<^sub>c N) h f = g")
  apply (thin_tac "compose (M \<times>\<^sub>c N) (compose (carrier MN) k h) f = f")
  apply (thin_tac "ka \<in> mHom R MN MN \<and> compose (M \<times>\<^sub>c N) ka f = f")
 apply blast
 apply (rotate_tac -1) apply (frule sym) apply (thin_tac "mId\<^sub>MN  = ka")
 apply simp
 apply (thin_tac "compose (M \<times>\<^sub>c N) k g = f")
 apply (thin_tac "compose (M \<times>\<^sub>c N) h f = g")
 apply (thin_tac "k \<in> carrier MN1 \<rightarrow> carrier MN")
 apply (thin_tac "f \<in> M \<times>\<^sub>c N \<rightarrow> carrier MN")
 apply (thin_tac "h \<in> carrier MN \<rightarrow> carrier MN1")
 apply (thin_tac "compose (M \<times>\<^sub>c N) (mId\<^sub>MN) f = f")
 apply (subgoal_tac "(compose (carrier MN) k h) \<in> mHom R MN MN")
 apply simp
 apply (frule_tac f = h and g = k in  mHom_compos[of "R" "MN" "MN1" "MN"],
                        assumption+)
 apply (simp add:compos_def)
done

end
