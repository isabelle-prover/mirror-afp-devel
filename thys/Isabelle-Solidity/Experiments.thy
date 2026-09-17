theory Experiments
  imports Mcalc
begin

section \<open>Static Arrays\<close>

abbreviation SA0
  where "SA0 a d \<equiv> length a = d \<and> (\<forall>x<length a. \<exists>v. a!x = adata.Value (Uint v))"
abbreviation SA1
  where "SA1 a d1 d2 \<equiv> length a = d1 \<and> (\<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> SA0 a' d2)"
abbreviation SA2
  where "SA2 a d1 d2 d3 \<equiv> length a = d1 \<and> (\<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> SA1 a' d2 d3)"
abbreviation SA3
  where "SA3 a d1 d2 d3 d4 \<equiv> length a = d1 \<and> (\<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> SA2 a' d2 d3 d4)"

subsection \<open>Initialization\<close>

subsubsection \<open>One Dimensional Arrays\<close>

lemma alookup_not_is_none_1:
"\<not> Option.is_none (alookup [Uint 0] (adata.Array (array (Suc 0) (adata.Value (Bool False)))))"
  by (simp add:alookup.simps array_def)

lemma (in Contract) initializationd1n1:
  assumes "x = adata.Array [adata.Value (Bool False)]"
    shows
     "wp (do {
        write x (STR ''x'');
        mdecl (TArray 1 (TValue TBool)) (STR ''y'');
        assign_stack_monad (STR ''y'') [sint_monad 0] true_monad
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint 0] cd = Some (adata.Value (Bool False))))
      (K (K True))
      s"
  unfolding mdecl_def
  apply wp+
   apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc lookup:alookup_not_is_none_1)+
  using assms by (auto simp add: alookup.simps)

subsubsection \<open>Two Dimensional Arrays\<close>

lemma alookup_not_is_none_2:
  "\<not> Option.is_none
           (alookup [Uint 0, Uint 0]
             (adata.Array (array (Suc 0) (adata.Array (array (Suc 0) (adata.Value (Bool False)))))))"
  by (simp add:alookup.simps array_def)

lemma (in Contract) initializationd2n1:
  assumes "x = adata.Array [adata.Array [adata.Value (Bool False)]]"
    shows
     "wp (do {
        write x (STR ''x'');
        mdecl (TArray 1 (TArray 1 (TValue TBool))) (STR ''y'');
        assign_stack_monad (STR ''y'') [sint_monad 0,sint_monad 0] true_monad
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint 0,Uint 0] cd = Some (adata.Value (Bool False))))
      (K (K True))
      s"
  unfolding mdecl_def
  apply wp+
   apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc lookup:alookup_not_is_none_2)+
  using assms by (auto simp add: alookup.simps)

subsection \<open>Assignments\<close>

subsubsection \<open>One Dimensional Arrays\<close>

(*
  We can substitue z=5 and z=20 to get assignd1n5 and assignd1n20
*)
lemma (in Contract) assignd1:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA0 ar z"
      and "unat i < z"
    shows
     "wp (do {
        write x (STR ''x'');
        assign_stack_monad (STR ''x'') [sint_monad i] (sint_monad y)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i] cd = Some (adata.Value (Uint y))))
      (K (K True))
      s"
  apply wp+
   apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc)+
  using assms by (auto simp add: alookup.simps)

subsubsection \<open>Two Dimensional Arrays\<close>

(*
  We can substitue z1=z2=5 and z1=z2=20 to get assignd2n5 and assignd2n20
*)
lemma (in Contract) assignd2:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA1 ar z1 z2"
      and "unat i < z1"
      and "unat j < z2"
    shows
     "wp (do {
        write x (STR ''x'');
        assign_stack_monad (STR ''x'') [sint_monad i,sint_monad j] (sint_monad y)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i,Uint j] cd = Some (adata.Value (Uint y))))
      (K (K True))
      s"
  apply wp+
   apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc)+
  using assms by (auto simp add: alookup.simps)

subsubsection \<open>Three Dimensional Arrays\<close>

(*
  We can substitue z1=z2=5 and z1=z2=20 to get assignd3n5 and assignd3n20
*)
lemma (in Contract) assignd3:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA2 ar z1 z2 z3"
      and "unat i < z1"
      and "unat j < z2"
      and "unat k < z3"
    shows
     "wp (do {
        write x (STR ''x'');
        assign_stack_monad (STR ''x'') [sint_monad i,sint_monad j,sint_monad k] (sint_monad y)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i,Uint j,Uint k] cd = Some (adata.Value (Uint y))))
      (K (K True))
      s"
  apply wp+
     apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc)+
  using assms by (auto dest!:spec simp: alookup.simps)

subsubsection \<open>Four Dimensional Arrays\<close>

(*
  We can substitue z1=z2=5 and z1=z2=20 to get assignd4n5 and assignd4n20
*)
lemma (in Contract) assignd4:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA3 ar z1 z2 z3 z4"
      and "unat i < z1"
      and "unat j < z2"
      and "unat k < z3"
      and "unat l < z4"
    shows
     "wp (do {
        write x (STR ''x'');
        assign_stack_monad (STR ''x'') [sint_monad i,sint_monad j,sint_monad k,sint_monad l] (sint_monad y)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i,Uint j,Uint k,Uint l] cd = Some (adata.Value (Uint y))))
      (K (K True))
      s"
  apply wp+
      apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc)+
  using assms
  by (auto dest!:spec simp: alookup.simps)

subsection \<open>Single Aliasing\<close>

subsubsection \<open>Two Dimensional Arrays\<close>

lemma is_Array_SA1:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA1 ar d1 d2"
      and "unat j < d1"
    shows "adata.is_Array (the (alookup [Uint j] y))"
  using assms by (auto simp add: alookup.simps)

lemma not_is_none_alookup_SA1:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA1 ar d1 d2"
      and "unat j < d1"
    shows "\<not> Option.is_none (alookup [Uint j] y)"
  using assms
  by (auto simp add: alookup.simps)

lemma singlealiasingd2_adata:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA1 ar d1 d2"
      and "\<exists>ar. y = adata.Array ar \<and> SA1 ar d1 d2"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
    shows "alookup [Uint i, Uint k]
        (the (aupdate ([Uint i] @ [Uint k]) (adata.Value (Uint p))
               (the (alookup [Uint j] y \<bind> (\<lambda>cd. aupdate [Uint i] cd x))))) =
       Some (adata.Value (Uint p))"
proof -
  from assms obtain ar where "y = adata.Array ar"
    and "\<forall>x<length ar. \<exists>a'. ar!x = adata.Array a' \<and> SA0 a' d2" by auto
  moreover with assms obtain ar2
    where "ar!unat j = adata.Array ar2"
    and "length ar2 = d2" by auto
  ultimately show ?thesis using assms by (auto dest!:spec simp:alookup.simps)
qed

(*
  We can substitue d1=d2=d3=d4=5 and d1=d2=d3=d4=20 to get singlealiasingd2n5 and singlealiasingd2n20
*)
lemma (in Contract) singlealiasingd2:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA1 ar d1 d2"
      and "\<exists>ar. y = adata.Array ar \<and> SA1 ar d1 d2"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
    shows
     "wp (do {
        write x (STR ''x'');
        write y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad i] (stackLookup (STR ''y'') [sint_monad j]);
        assign_stack_monad (STR ''y'') [sint_monad j, sint_monad k] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i, Uint k] cd = Some (adata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
                apply auto
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array_SA1[OF assms(2,4)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=l and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA1[OF assms(2,4)] not_is_none_alookup_SA1[OF assms(1,3)])+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_SA1[OF assms(2,4)] not_is_none_alookup_SA1[OF assms(1,3)])+
  using singlealiasingd2_adata[OF assms] by simp

subsubsection \<open>Three Dimensional Arrays\<close>

lemma is_Array_SA2:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat j < d1"
    shows "adata.is_Array (the (alookup [Uint j] y))"
  using assms by (auto simp add: alookup.simps)

lemma not_is_none_alookup_SA2:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat j < d1"
    shows "\<not> Option.is_none (alookup [Uint j] y)"
  using assms
  by (auto simp add: alookup.simps)

lemma singlealiasingd3_adata:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d3"
    shows "alookup [Uint i, Uint k, Uint l]
        (the (aupdate ([Uint i] @ [Uint k, Uint l]) (adata.Value (Uint p))
               (the (alookup [Uint j] y \<bind> (\<lambda>cd. aupdate [Uint i] cd x))))) =
       Some (adata.Value (Uint p))"
proof -
  from assms obtain ar where "y = adata.Array ar"
    and "\<forall>x<length ar. \<exists>a'. ar!x = adata.Array a' \<and> SA1 a' d2 d3" by auto
  moreover with assms obtain ar2 where "ar!unat j = adata.Array ar2"
    and "length ar2 = d2"
    and "\<forall>x<length ar2. \<exists>a'. ar2!x = adata.Array a' \<and> SA0 a' d3" by auto
  ultimately show ?thesis using assms by (auto dest!:spec simp:alookup.simps)
qed

(*
  We can substitue d1=d2=d3=d4=5 and d1=d2=d3=d4=10 to get singlealiasingd3n5 and singlealiasingd3n10
*)
lemma (in Contract) singlealiasingd3:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d3"
    shows
     "wp (do {
        write x (STR ''x'');
        write y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad i] (stackLookup (STR ''y'') [sint_monad j]);
        assign_stack_monad (STR ''y'') [sint_monad j, sint_monad k, sint_monad l] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i, Uint k, Uint l] cd = Some (adata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
                apply auto
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array_SA2[OF assms(2,4)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=la and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA2[OF assms(2,4)] not_is_none_alookup_SA2[OF assms(1,3)])+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_SA2[OF assms(2,4)] not_is_none_alookup_SA2[OF assms(1,3)])+
  using singlealiasingd3_adata[OF assms] by simp

subsubsection \<open>Four Dimensional Arrays\<close>

lemma is_Array_SA3:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat j < d1"
    shows "adata.is_Array (the (alookup [Uint j] y))"
  using assms by (auto simp add: alookup.simps)

lemma not_is_none_alookup_SA3:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat j < d1"
    shows "\<not> Option.is_none (alookup [Uint j] y)"
  using assms
  by (auto simp add: alookup.simps)

lemma singlealiasingd4_adata:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d3"
      and "unat m < d4"
    shows "alookup [Uint i, Uint k, Uint l, Uint m]
        (the (aupdate ([Uint i] @ [Uint k, Uint l, Uint m]) (adata.Value (Uint p))
               (the (alookup [Uint j] y \<bind> (\<lambda>cd. aupdate [Uint i] cd x))))) =
       Some (adata.Value (Uint p))"
proof -
  from assms obtain ar where "y = adata.Array ar"
    and "\<forall>x<length ar. \<exists>a'. ar!x = adata.Array a' \<and> SA2 a' d2 d3 d4" by auto
  moreover with assms obtain ar2 where "ar!unat j = adata.Array ar2"
    and "length ar2 = d2"
    and "\<forall>x<length ar2. \<exists>a'. ar2!x = adata.Array a' \<and> SA1 a' d3 d4" by auto
  ultimately show ?thesis using assms by (auto dest!:spec simp:alookup.simps)
qed

(*
  We can substitue d1=d2=d3=d4=5 and d1=d2=d3=d4=10 to get singlealiasingd4n5 and singlealiasingd4n10
*)
lemma (in Contract) singlealiasingd4:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d3"
      and "unat m < d4"
    shows
     "wp (do {
        write x (STR ''x'');
        write y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad i] (stackLookup (STR ''y'') [sint_monad j]);
        assign_stack_monad (STR ''y'') [sint_monad j, sint_monad k, sint_monad l, sint_monad m] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i, Uint k, Uint l, Uint m] cd = Some (adata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
                apply auto
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array_SA3[OF assms(2,4)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=la and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA3[OF assms(2,4)] not_is_none_alookup_SA3[OF assms(1,3)])+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_SA3[OF assms(2,4)] not_is_none_alookup_SA3[OF assms(1,3)])+
  using singlealiasingd4_adata[OF assms] by simp

subsection \<open>Double Aliasing\<close>

subsubsection \<open>Three Dimensional Arrays\<close>

lemma is_Array_2_SA2:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat j < d1"
      and "unat k < d2"
    shows "adata.is_Array (the (alookup [Uint j,Uint k] y))"
  using assms by (auto simp add: alookup.simps elim!: allE)

lemma not_is_none_alookup_2_SA2:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat j < d1"
      and "unat k < d2"
    shows "\<not> Option.is_none (alookup [Uint j,Uint k] y)"
  using assms by (auto simp add: alookup.simps)

lemma doublealiasingd3_adata:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "\<exists>ar. z = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d1"
      and "unat m < d2"
      and "unat n < d3"
    shows "alookup [Uint i, Uint k, Uint n]
        (the (aupdate [Uint i, Uint k, Uint n] (adata.Value (Uint p))
               (the (alookup [Uint l, Uint m] z \<bind>
                     (\<lambda>cd. aupdate [Uint i, Uint k] cd
                            (the (alookup [Uint j] y \<bind> (\<lambda>cd. aupdate [Uint i] cd x)))))))) =
       Some (adata.Value (Uint p))"
proof -
  from assms obtain ar where "y = adata.Array ar"
    and "length ar = d1"
    and "\<forall>x<length ar. \<exists>a'. ar!x = adata.Array a' \<and> SA1 a' d2 d3" by auto
  moreover with assms obtain ar2 where "ar!unat j = adata.Array ar2" and "ar!unat j = adata.Array ar2"
    and "length ar2 = d2"
    and "\<forall>x<length ar2. \<exists>a'. ar2!x = adata.Array a' \<and> SA0 a' d3" by auto
  moreover from assms obtain ar' where "z = adata.Array ar'"
    and "length ar' = d1"
    and "\<forall>x<length ar'. \<exists>a'. ar'!x = adata.Array a' \<and> SA1 a' d2 d3" by auto
  moreover with assms obtain ar2' where "ar'!unat l = adata.Array ar2'" and "ar'!unat l = adata.Array ar2'"
    and "length ar2' = d2"
    and "\<forall>x<length ar2'. \<exists>a'. ar2'!x = adata.Array a' \<and> SA0 a' d3" by auto
  ultimately show ?thesis using assms by (auto simp:alookup.simps)
qed

(*
  We can substitue d1=d2=d3=d4=5 and d1=d2=d3=d4=10 to get doublealiasingd3n5 and doublealiasingd3n10
*)
lemma (in Contract) doublealiasingd3:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "\<exists>ar. y = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "\<exists>ar. z = adata.Array ar \<and> SA2 ar d1 d2 d3"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d1"
      and "unat m < d2"
      and "unat n < d3"
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
    apply (rule is_Array_SA2[OF assms(2,5)])
   apply wp+
        apply (auto simp add: pred_memory_def)
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array_SA2[OF assms(2,5)])
  apply wp+
                  apply (auto simp add: pred_memory_def)
   apply (erule isValue_isArray_all, assumption, assumption)
    apply (mc lookup: not_is_none_alookup_SA2[OF assms(2,5)] not_is_none_alookup_SA2[OF assms(1,4)] not_is_none_alookup_2_SA2[OF assms(3,7,8)] not_is_none_alookup_2_SA2[OF assms(2,5,6)])+
   apply (rule is_Array_2_SA2[OF assms(3,7,8)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=la and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA2[OF assms(2,5)] not_is_none_alookup_SA2[OF assms(1,4)])+
  apply (drule_tac ?is3.0 = "[Uint l, Uint m]" and ?l1.0=laa and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA2[OF assms(2,5)] not_is_none_alookup_SA2[OF assms(1,4)] not_is_none_alookup_2_SA2[OF assms(3,7,8)] not_is_none_alookup_2_SA2[OF assms(2,5,6)] )+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_SA2[OF assms(2,5)] not_is_none_alookup_SA2[OF assms(1,4)] not_is_none_alookup_2_SA2[OF assms(3,7,8)] not_is_none_alookup_2_SA2[OF assms(2,5,6)])+
  apply simp
  using doublealiasingd3_adata[OF assms] by simp

subsubsection \<open>Four Dimensional Arrays\<close>

lemma is_Array_2_SA3:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat j < d1"
      and "unat k < d2"
    shows "adata.is_Array (the (alookup [Uint j,Uint k] y))"
  using assms by (auto simp add: alookup.simps elim!: allE)

lemma not_is_none_alookup_2_SA3:
  assumes "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat j < d1"
      and "unat k < d2"
    shows "\<not> Option.is_none (alookup [Uint j,Uint k] y)"
  using assms by (auto simp add: alookup.simps)


lemma doublealiasingd4_adata:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "\<exists>ar. z = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d1"
      and "unat m < d2"
      and "unat n < d3"
      and "unat o' < d4"
    shows "alookup [Uint i, Uint k, Uint n, Uint o']
        (the (aupdate [Uint i, Uint k, Uint n, Uint o'] (adata.Value (Uint p))
               (the (alookup [Uint l, Uint m] z \<bind>
                     (\<lambda>cd. aupdate [Uint i, Uint k] cd
                            (the (alookup [Uint j] y \<bind> (\<lambda>cd. aupdate [Uint i] cd x)))))))) =
       Some (adata.Value (Uint p))"
proof -
  from assms obtain ar where "y = adata.Array ar"
    and "length ar = d1"
    and "\<forall>x<length ar. \<exists>a'. ar!x = adata.Array a' \<and> SA2 a' d2 d3 d4" by auto
  moreover with assms obtain ar2 where "ar!unat j = adata.Array ar2" and "ar!unat j = adata.Array ar2"
    and "length ar2 = d2"
    and "\<forall>x<length ar2. \<exists>a'. ar2!x = adata.Array a' \<and> SA1 a' d3 d4" by auto
  moreover from assms obtain ar' where "z = adata.Array ar'"
    and "length ar' = d1"
    and "\<forall>x<length ar'. \<exists>a'. ar'!x = adata.Array a' \<and> SA2 a' d2 d3 d4" by auto
  moreover with assms obtain ar2' where "ar'!unat l = adata.Array ar2'" and "ar'!unat l = adata.Array ar2'"
    and "length ar2' = d2"
    and "\<forall>x<length ar2'. \<exists>a'. ar2'!x = adata.Array a' \<and> SA1 a' d3 d4" by auto
  moreover with assms obtain ar3' where "ar2'!unat m = adata.Array ar3'"
    and "length ar3' = d3"
    and "\<forall>x<length ar3'. \<exists>a'. ar3'!x = adata.Array a' \<and> SA0 a' d4" by auto
  ultimately show ?thesis using assms by (auto simp:alookup.simps)
qed

(*
  We can substitue d1=d2=d3=d4=5 and d1=d2=d3=d4=10 to get doublealiasingd4n5 and doublealiasingd4n10
*)
lemma (in Contract) doublealiasingd4:
  assumes "\<exists>ar. x = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "\<exists>ar. y = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "\<exists>ar. z = adata.Array ar \<and> SA3 ar d1 d2 d3 d4"
      and "unat i < d1"
      and "unat j < d1"
      and "unat k < d2"
      and "unat l < d1"
      and "unat m < d2"
      and "unat n < d3"
      and "unat o' < d4"
    shows
     "wp (do {
        write x (STR ''x'');
        write y (STR ''y'');
        write z (STR ''z'');
        assign_stack_monad (STR ''x'') [sint_monad i] (stackLookup (STR ''y'') [sint_monad j]);
        assign_stack_monad (STR ''y'') [sint_monad j, sint_monad k] (stackLookup (STR ''z'') [sint_monad l, sint_monad m]);
        assign_stack_monad (STR ''z'') [sint_monad l, sint_monad m, sint_monad n, sint_monad o'] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i, Uint k, Uint n, Uint o'] cd = Some (adata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
                      apply auto
    apply (erule isValue_isArray_all, assumption, assumption)
     apply mc+
    apply (rule is_Array_SA3[OF assms(2,5)])
   apply wp+
        apply (auto simp add: pred_memory_def)
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array_SA3[OF assms(2,5)])
  apply wp+
                  apply (auto simp add: pred_memory_def)
   apply (erule isValue_isArray_all, assumption, assumption)
    apply (mc lookup: not_is_none_alookup_SA3[OF assms(2,5)] not_is_none_alookup_SA3[OF assms(1,4)] not_is_none_alookup_2_SA3[OF assms(3,7,8)] not_is_none_alookup_2_SA3[OF assms(2,5,6)])+
   apply (rule is_Array_2_SA3[OF assms(3,7,8)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=la and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA3[OF assms(2,5)] not_is_none_alookup_SA3[OF assms(1,4)])+
  apply (drule_tac ?is3.0 = "[Uint l, Uint m]" and ?l1.0=laa and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_SA3[OF assms(2,5)] not_is_none_alookup_SA3[OF assms(1,4)] not_is_none_alookup_2_SA3[OF assms(3,7,8)] not_is_none_alookup_2_SA3[OF assms(2,5,6)] )+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_SA3[OF assms(2,5)] not_is_none_alookup_SA3[OF assms(1,4)] not_is_none_alookup_2_SA3[OF assms(3,7,8)] not_is_none_alookup_2_SA3[OF assms(2,5,6)])+
  apply simp
  using doublealiasingd4_adata[OF assms] by simp

section \<open>Dynamic Arrays\<close>

abbreviation DA0 where "DA0 a \<equiv> \<forall>x<length a. \<exists>v. a!x = adata.Value (Uint v)"
abbreviation DA1 where "DA1 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> DA0 a'"
abbreviation DA2 where "DA2 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> DA1 a'"
abbreviation DA3 where "DA3 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = adata.Array a' \<and> DA2 a'"

subsection \<open>One Dimensional Arrays\<close>

lemma (in Contract) assigndynamicd1:
  assumes "\<exists>ar. x = adata.Array ar \<and> DA0 ar"
      and "unat i < length (adata.ar x)"
    shows
     "wp (do {
        write x (STR ''x'');
        assign_stack_monad (STR ''x'') [sint_monad i] (sint_monad y)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i] cd = Some (adata.Value (Uint y))))
      (K (K True))
      s"
  apply wp+
   apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc)+
  using assms by (auto simp:alookup.simps)

subsection \<open>Two Dimensional Arrays\<close>

lemma (in Contract) assigndynamicd2:
  assumes "\<exists>ar. x = adata.Array ar \<and> DA1 ar"
      and "unat i < length (adata.ar x)"
      and "unat j < length (adata.ar ((adata.ar x) ! (unat i)))"
    shows
     "wp (do {
        write x (STR ''x'');
        assign_stack_monad (STR ''x'') [sint_monad i,sint_monad j] (sint_monad y)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i,Uint j] cd = Some (adata.Value (Uint y))))
      (K (K True))
      s"
  apply wp+
   apply (auto simp add: pred_memory_def)
  apply (rule pred_some_read)
   apply (mc)+
  using assms by (auto simp add: alookup.simps)

subsection \<open>Single Aliasing\<close>

subsubsection \<open>Two Dimensional Arrays\<close>

lemma is_Array_DA1:
  assumes "\<exists>ar. y = adata.Array ar \<and> DA1 ar"
      and "unat j < length (adata.ar y)"
    shows "adata.is_Array (the (alookup [Uint j] y))"
  using assms by (auto simp add: alookup.simps)

lemma not_is_none_alookup_DA1:
  assumes "\<exists>ar. y = adata.Array ar \<and> DA1 ar"
      and "unat j < length (adata.ar y)"
    shows "\<not> Option.is_none (alookup [Uint j] y)"
  using assms
  by (auto simp add: alookup.simps)

lemma singlealiasingdynamicd2_adata:
  assumes "\<exists>ar. x = adata.Array ar \<and> DA1 ar"
      and "\<exists>ar. y = adata.Array ar \<and> DA1 ar"
      and "unat i < length (adata.ar x)"
      and "unat j < length (adata.ar y)"
      and "unat k < length (adata.ar ((adata.ar y) ! (unat j)))"
    shows "alookup [Uint i, Uint k]
        (the (aupdate ([Uint i] @ [Uint k]) (adata.Value (Uint p))
               (the (alookup [Uint j] y \<bind> (\<lambda>cd. aupdate [Uint i] cd x))))) =
       Some (adata.Value (Uint p))"
proof -
  from assms obtain ar where "y = adata.Array ar"
    and "\<forall>x<length ar. \<exists>a'. ar!x = adata.Array a' \<and> DA0 a'" by auto
  moreover with assms obtain ar2
    where "ar!unat j = adata.Array ar2" by auto
  ultimately show ?thesis using assms by (auto dest!:spec simp:alookup.simps)
qed

(*
  We can substitue d1=d2=d3=d4=5 and d1=d2=d3=d4=20 to get singlealiasingd2n5 and singlealiasingd2n20
*)
lemma (in Contract) singlealiasingdynamicd2:
  assumes "\<exists>ar. x = adata.Array ar \<and> DA1 ar"
      and "\<exists>ar. y = adata.Array ar \<and> DA1 ar"
      and "unat i < length (adata.ar x)"
      and "unat j < length (adata.ar y)"
      and "unat k < length (adata.ar ((adata.ar y) ! (unat j)))"
    shows
     "wp (do {
        write x (STR ''x'');
        write y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad i] (stackLookup (STR ''y'') [sint_monad j]);
        assign_stack_monad (STR ''y'') [sint_monad j, sint_monad k] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint i, Uint k] cd = Some (adata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
                apply auto
   apply (erule isValue_isArray_all, assumption, assumption)
    apply mc+
   apply (rule is_Array_DA1[OF assms(2,4)])
  apply wp+
       apply (auto simp add: pred_memory_def)
  apply (drule_tac ?is3.0 = "[Uint j]" and ?l1.0=l and ?l2.0=x1 in aliasing_1, simp, simp)
     apply (mc lookup: not_is_none_alookup_DA1[OF assms(2,4)] not_is_none_alookup_DA1[OF assms(1,3)])+
  apply (rule pred_some_read)
   apply (mc lookup: not_is_none_alookup_DA1[OF assms(2,4)] not_is_none_alookup_DA1[OF assms(1,3)])+
  using singlealiasingdynamicd2_adata[OF assms] by simp

end
