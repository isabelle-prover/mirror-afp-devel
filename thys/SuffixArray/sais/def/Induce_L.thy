theory Induce_L
  imports 
    "../../util/Repeat" 
     "../prop/Buckets"
begin 
section "Induce L Refinement"

fun induce_l_step_r0 ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_l_step_r0 (B, SA, i) (\<alpha>, T) =
  (if SA ! i < length T
   then
     (case SA ! i of
        Suc j \<Rightarrow>
          (case suffix_type T j of 
             L_type \<Rightarrow>
               (let k = \<alpha> (T ! j);
                    l = B ! k
                in (B[k := Suc l], SA[l := j], Suc i))
             | _ \<Rightarrow> (B, SA, Suc i))
        | _ \<Rightarrow> (B, SA, Suc i))
   else (B, SA, Suc i))"
(*
lemma abs_induce_l_step_to_r0:
  "i < length SA \<Longrightarrow> abs_induce_l_step (B, SA, i) (\<alpha>, T) = induce_l_step_r0 (B, SA, i) (\<alpha>, T)"
  by (clarsimp simp: Let_def split: prod.splits nat.splits SL_types.splits)
*)
fun induce_l_step ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<times> SL_types list\<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_l_step (B, SA, i) (\<alpha>, T, ST) =
  (if SA ! i < length T
   then
     (case SA ! i of
        Suc j \<Rightarrow>
          (case ST ! j of 
             L_type \<Rightarrow>
               (let k = \<alpha> (T ! j);
                    l = B ! k
                in (B[k := Suc (B ! k)], SA[l := j], Suc i))
             | _ \<Rightarrow> (B, SA, Suc i))
        | _ \<Rightarrow> (B, SA, Suc i))
   else (B, SA, Suc i))"

definition induce_l_base :: 
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   SL_types list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_l_base \<alpha> T ST B SA = repeat (length T) induce_l_step (B, SA, 0) (\<alpha>, T, ST)"

definition induce_l :: 
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   SL_types list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"induce_l \<alpha> T ST B SA = (let (B', SA', i) = induce_l_base \<alpha> T ST B SA in SA')"

end