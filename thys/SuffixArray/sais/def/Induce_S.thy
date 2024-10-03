theory Induce_S
  imports "../abs-proof/Abs_Induce_S_Verification"
begin

section "Induce S Refinement"

fun induce_s_step_r0 ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_s_step_r0 (B, SA, i) (\<alpha>, T) =
  (case i of 
    Suc n \<Rightarrow>
      (if Suc n < length SA \<and> SA ! Suc n < length T then
        (case SA ! Suc n of
          Suc j \<Rightarrow>
            (case suffix_type T j of
              S_type \<Rightarrow>
                (let b = \<alpha> (T ! j);
                     k = B ! b - Suc 0
                 in (B[b := k], SA[k := j], n)
                )
              | _ \<Rightarrow> (B, SA, n)
            )
          | _ \<Rightarrow> (B, SA, n)
        )
        else
          (B, SA, n)
       )
    | _   \<Rightarrow> (B, SA, 0)
  )"

fun induce_s_step_r1 ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<times> SL_types list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_s_step_r1 (B, SA, i) (\<alpha>, T, ST) =
  (case i of 
    Suc n \<Rightarrow>
      (if Suc n < length SA \<and> SA ! Suc n < length T then
        (case SA ! Suc n of
          Suc j \<Rightarrow>
            (case ST ! j of
              S_type \<Rightarrow>
                (let b = \<alpha> (T ! j);
                     k = B ! b - Suc 0
                 in (B[b := k], SA[k := j], n)
                )
              | _ \<Rightarrow> (B, SA, n)
            )
          | _ \<Rightarrow> (B, SA, n)
        )
        else
          (B, SA, n)
       )
    | _   \<Rightarrow> (B, SA, 0)
  )"

fun induce_s_step_r2 ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<times> SL_types list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_s_step_r2 (B, SA, i) (\<alpha>, T, ST) =
  (case i of 
    Suc n \<Rightarrow>
      (if Suc n < length SA  then
        (case SA ! Suc n of
          Suc j \<Rightarrow>
            (case ST ! j of
              S_type \<Rightarrow>
                (let b = \<alpha> (T ! j);
                     k = B ! b - Suc 0
                 in (B[b := k], SA[k := j], n)
                )
              | _ \<Rightarrow> (B, SA, n)
            )
          | _ \<Rightarrow> (B, SA, n)
        )
        else
          (B, SA, n)
       )
    | _   \<Rightarrow> (B, SA, 0)
  )"

fun induce_s_step ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<times> SL_types list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_s_step (B, SA, i) (\<alpha>, T, ST) =
  (case i of 
    Suc n \<Rightarrow>
    (case SA ! Suc n of
        Suc j \<Rightarrow>
          (case ST ! j of
            S_type \<Rightarrow>
              (let b = \<alpha> (T ! j);
                   k = B ! b - Suc 0
               in (B[b := k], SA[k := j], n)
              )
            | _ \<Rightarrow> (B, SA, n)
          )
        | _ \<Rightarrow> (B, SA, n)
      )
    | _   \<Rightarrow> (B, SA, 0)
  )"

definition induce_s_base :: 
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   SL_types list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"induce_s_base \<alpha> T ST B SA = repeat (length T - Suc 0) induce_s_step (B, SA, length T - Suc 0) (\<alpha>, T, ST)"

definition induce_s :: 
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   SL_types list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"induce_s \<alpha> T ST B SA = (let (B', SA', i) = induce_s_base \<alpha> T ST B SA in SA')"

end