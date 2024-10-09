theory Bucket_Insert
  imports 
    "../../util/Repeat"
begin
section "Bucket Insert"

fun bucket_insert_step ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<times> nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"bucket_insert_step (B, SA, i) (\<alpha>, T, LMS) =
  (let b = \<alpha> (T ! (LMS ! i));
       k = B ! b - Suc 0
   in (B[b := k], SA[k := LMS ! i], Suc i))"

definition bucket_insert_base ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"bucket_insert_base \<alpha> T B SA LMS = repeat (length LMS) bucket_insert_step (B, SA, 0) (\<alpha>, T, LMS)"

definition bucket_insert ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
   nat list"
  where
"bucket_insert \<alpha> T B SA LMS =
  (let (B', SA', i) = bucket_insert_base \<alpha> T B SA LMS
   in SA')"

end