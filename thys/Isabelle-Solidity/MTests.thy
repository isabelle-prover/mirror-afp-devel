theory MTests
  imports Mcalc
begin

section \<open>Double Aliasing for Dynamic Arrays\<close>

abbreviation DA0 where "DA0 a \<equiv> \<forall>x<length a. \<exists>v. a!x = adata.Value (Uint v)"
abbreviation DA1 where "DA1 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> DA0 a'"
abbreviation DA2 where "DA2 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> DA1 a'"

lemma is_Array1:
  assumes "\<exists>ar. y = adata.Array ar \<and> DA2 ar"
      and "unat j < length (adata.ar y)"
    shows "adata.is_Array (the (alookup [Uint j] y))"
  using assms by (auto simp add: alookup.simps)

lemma is_Array2:
  assumes "\<exists>ar. y = adata.Array ar \<and> DA2 ar"
      and "unat j < length (adata.ar y)"
      and "unat k < length (adata.ar ((adata.ar y) ! (unat j)))"
    shows "adata.is_Array (the (alookup [Uint j,Uint k] y))"
  using assms by (auto simp add: alookup.simps elim!: allE)

lemma not_is_none_alookup_1:
  assumes "\<exists>ar. y = adata.Array ar \<and> DA2 ar"
      and "unat j < length (adata.ar y)"
    shows "\<not> Option.is_none (alookup [Uint j] y)"
  using assms
  by (auto simp add: alookup.simps)

lemma not_is_none_alookup_2:
  assumes "\<exists>ar. y = adata.Array ar \<and> DA2 ar"
      and "unat j < length (adata.ar y)"
      and "unat k < length (adata.ar ((adata.ar y) ! (unat j)))"
    shows "\<not> Option.is_none (alookup [Uint j,Uint k] y)"
  using assms by (auto simp add: alookup.simps)

lemma (in Contract) doublealiasingdynamicd3:
  assumes "\<exists>ar. x = adata.Array ar \<and> DA2 ar"
      and "\<exists>ar. y = adata.Array ar \<and> DA2 ar"
      and "\<exists>ar. z = adata.Array ar \<and> DA2 ar"
      and "unat i < length (adata.ar x)"
      and "unat j < length (adata.ar y)"
      and "unat k < length (adata.ar ((adata.ar y) ! (unat j)))"
      and "unat l < length (adata.ar z)"
      and "unat m < length (adata.ar ((adata.ar z) ! (unat l)))"
      and "unat n < length (adata.ar (adata.ar (adata.ar z ! unat l) ! unat m))"
    shows
     "wp (do {
        write x (STR ''x'');
        write y (STR ''y'');
        write z (STR ''z'');
        assign_stack_monad (STR ''x'') [sint_monad i] (stackLookup (STR ''y'') [sint_monad j]);
        assign_stack_monad (STR ''y'') [sint_monad j, sint_monad k] (stackLookup (STR ''z'') [sint_monad l, sint_monad m]);
        assign_stack_monad (STR ''z'') [sint_monad l, sint_monad m, sint_monad n] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i, Uint k, Uint n] cd = Some (adata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
                      apply auto
    apply (erule isValue_isArray_all, assumption, assumption)
     apply mc+
    apply (rule is_Array1[OF assms(2,5)])
   apply wp+
        apply (auto simp add: pred_memory_def)
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array1[OF assms(2,5)])
  apply wp+
                  apply (auto simp add: pred_memory_def)
   apply (erule isValue_isArray_all, assumption, assumption)
    apply (mc lookup: not_is_none_alookup_1[OF assms(2,5)] not_is_none_alookup_1[OF assms(1,4)] not_is_none_alookup_2[OF assms(3,7,8)] not_is_none_alookup_2[OF assms(2,5,6)])+
   apply (rule is_Array2[OF assms(3,7,8)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=la and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_1[OF assms(2,5)] not_is_none_alookup_1[OF assms(1,4)])+
  apply (drule_tac ?is3.0 = "[Uint l, Uint m]" and ?l1.0=laa and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_1[OF assms(2,5)] not_is_none_alookup_1[OF assms(1,4)] not_is_none_alookup_2[OF assms(3,7,8)] not_is_none_alookup_2[OF assms(2,5,6)] )+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_1[OF assms(2,5)] not_is_none_alookup_1[OF assms(1,4)] not_is_none_alookup_2[OF assms(3,7,8)] not_is_none_alookup_2[OF assms(2,5,6)])+
  apply simp
  using assms by (auto dest!:spec simp:alookup.simps) \<comment> \<open>Takes a bit longer\<close>

end
