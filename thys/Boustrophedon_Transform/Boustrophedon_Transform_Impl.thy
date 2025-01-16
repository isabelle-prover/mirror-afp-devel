theory Boustrophedon_Transform_Impl
  imports Boustrophedon_Transform Secant_Numbers Tangent_Numbers "HOL-Library.Stream"
begin

subsection \<open>Implementation\<close>

text \<open>
  In the following we will provide some simple functions based on infinite streams
  to compute the Seidel triangle and the Boustrophedon transform of a sequence efficiently.
\<close>

text \<open>
  The core functionality is the following auxiliary function, which produces the next row of the
  Seidel triangle from the current row and the corresponding entry in the input sequence.
\<close>
primrec seidel_triangle_rows_step :: "'a :: monoid_add \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "seidel_triangle_rows_step a [] = [a]"
| "seidel_triangle_rows_step a (x # xs) = a # seidel_triangle_rows_step (a + x) xs"

primrec seidel_triangle_rows_step_tailrec :: "'a :: monoid_add \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "seidel_triangle_rows_step_tailrec a [] acc = a # acc"
| "seidel_triangle_rows_step_tailrec a (x # xs) acc =
     seidel_triangle_rows_step_tailrec (a + x) xs (a # acc)"

lemma seidel_triangle_rows_step_tailrec_correct [simp]:
  "seidel_triangle_rows_step_tailrec a xs acc =
   rev (seidel_triangle_rows_step a xs) @ acc"
  by (induction xs arbitrary: a acc) simp_all

lemma length_seidel_triangle_rows_step [simp]:
  "length (seidel_triangle_rows_step a xs) = Suc (length xs)"
  by (induction xs arbitrary: a) auto

lemma nth_seidel_triangle_rows_step:
  "i \<le> length xs \<Longrightarrow> seidel_triangle_rows_step a xs ! i = a + sum_list (take i xs)"
  by (induction xs arbitrary: i a) (auto simp: nth_Cons add_ac split: nat.splits)

lemma seidel_triangle_rows_step_correct:
  fixes a :: "nat \<Rightarrow> 'a :: comm_monoid_add"
  shows "seidel_triangle_rows_step (a n) (map (seidel_triangle a (n-Suc 0)) (rev [0..<n])) =
           map (seidel_triangle a n) [0..<Suc n]"
proof (rule nth_equalityI, goal_cases)
  case i: (2 i)
  have "seidel_triangle_rows_step (a n) (map (seidel_triangle a (n-1)) (rev [0..<n])) ! i =
          a n + sum_list (take i (map (seidel_triangle a (n - Suc 0)) (rev [0..<n])))"
    using i by (subst nth_seidel_triangle_rows_step) auto
  also have "sum_list (take i (map (seidel_triangle a (n - Suc 0)) (rev [0..<n]))) =
               (\<Sum>j<i. seidel_triangle a (n - 1) (n - Suc j))"
    using i by (subst sum.list_conv_set_nth) (simp_all add: atLeast0LessThan rev_nth)
  also have "a n + \<dots> = seidel_triangle a n i"
    by (rule seidel_triangle_conv_rowsum [symmetric]) (use i in auto)
  also have "\<dots> = map (seidel_triangle a n) [0..<Suc n] ! i"
    using i by (subst nth_map) (auto simp del: upt_Suc)
  finally show ?case by simp
qed auto
  

text \<open>
  This auxiliary function produces an infinite stream of all the subsequent rows of the Seidel
  triangle, given the current row and a stream of the remaining elements of the input sequence.
\<close>
primcorec seidel_triangle_rows_aux :: "'a :: comm_monoid_add stream \<Rightarrow> 'a list \<Rightarrow> 'a list stream" where
  "seidel_triangle_rows_aux as xs =
     (let ys = seidel_triangle_rows_step_tailrec (shd as) xs []
      in  rev ys ## seidel_triangle_rows_aux (stl as) ys)"

lemma seidel_triangle_rows_aux_correct:
  "seidel_triangle_rows_aux (sdrop n as)
     (map (seidel_triangle (\<lambda>i. as !! i) (n-Suc 0)) (rev [0..<n])) !! m =
   map (seidel_triangle (\<lambda>i. as !! i) (n + m)) [0..<Suc (n+m)]"
proof (induction m arbitrary: n)
  case 0
  show ?case
    by (simp add: seidel_triangle_rows_step_correct del: upt_Suc)
next
  case (Suc m n)
  have "seidel_triangle_rows_aux (sdrop n as) 
          (map (seidel_triangle ((!!) as) (n - 1)) (rev [0..<n])) !! Suc m =
        seidel_triangle_rows_aux (sdrop (Suc n) as)
                    (map (seidel_triangle ((!!) as) n) (rev [0..<Suc n])) !! m"
    by (simp add: seidel_triangle_rows_step_correct rev_map del: upt_Suc)
  also have "\<dots> = map (seidel_triangle ((!!) as) (Suc (n + m))) [0..<n+m+2]"
    using Suc.IH[of "Suc n"] by (simp del: upt_Suc)
  finally show ?case
    by simp
qed

text \<open>
  This function produces an infinite stream of all the rows of the Seidel triangle of the
  sequence given by the input stream.

  Note that in the literature the triangle is often printed with every other row
  reversed, to emphasise the ``ox-plow'' nature of the recurrence. It is however
  mathematically more natural to not do this, so our version does not do this.
\<close>
definition seidel_triangle_rows :: "'a :: comm_monoid_add stream \<Rightarrow> 'a list stream" where
  "seidel_triangle_rows as = seidel_triangle_rows_aux as []"

lemma seidel_triangle_rows_correct:
  "seidel_triangle_rows as !! n = map (seidel_triangle (\<lambda>i. as !! i) n) [0..<Suc n]"
  using seidel_triangle_rows_aux_correct[of 0 as n]
  by (simp del: upt_Suc add: seidel_triangle_rows_def)



primcorec boustrophedon_stream_aux :: "'a :: comm_monoid_add stream \<Rightarrow> 'a list \<Rightarrow> 'a stream" where
  "boustrophedon_stream_aux as xs =
     (let ys = seidel_triangle_rows_step_tailrec (shd as) xs []
      in  hd ys ## boustrophedon_stream_aux (stl as) ys)"

lemma boustrophedon_stream_aux_conv_seidel_triangle_rows_aux:
  "boustrophedon_stream_aux as xs = smap last (seidel_triangle_rows_aux as xs)"
  by (coinduction arbitrary: as xs) (auto simp: hd_rev)  

lemma boustrophedon_stream_aux_correct:
  "boustrophedon_stream_aux (sdrop n as)
     (map (seidel_triangle (\<lambda>i. as !! i) (n - Suc 0)) (rev [0..<n])) !! m =
   boustrophedon (\<lambda>i. as !! i) (n + m)"
  by (subst boustrophedon_stream_aux_conv_seidel_triangle_rows_aux, subst snth_smap,
      subst seidel_triangle_rows_aux_correct)
     (simp add: boustrophedon_def)


text \<open>
  This function produces the Boustrophedon transform of a stream.
\<close>
definition boustrophedon_stream :: "'a :: comm_monoid_add stream \<Rightarrow> 'a stream" where
  "boustrophedon_stream as = boustrophedon_stream_aux as []"

lemma boustrophedon_stream_correct:
  "boustrophedon_stream as !! n = boustrophedon (\<lambda>i. as !! i) n"
  using boustrophedon_stream_aux_correct[of 0 as n]
  by (simp add: boustrophedon_stream_def)



text \<open>
  Lastly, we also provide a function to compute a single number in the transformed sequence
  to avoid code-generation problems related to streams.
\<close>
fun seidel_triangle_impl_aux :: "(nat \<Rightarrow> 'a :: comm_monoid_add) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "seidel_triangle_impl_aux a xs i n k =
     (let ys = seidel_triangle_rows_step_tailrec (a i) xs []
      in  if n = 0 then ys ! (i - k) else seidel_triangle_impl_aux a ys (i + 1) (n - 1) k)"

lemmas [simp del] = seidel_triangle_impl_aux.simps

lemma seidel_triangle_impl_aux_correct:
  assumes "k \<le> n + i" "length xs = i"
  shows   "seidel_triangle_impl_aux a xs i n k =
             seidel_triangle_rows_aux (smap a (fromN i)) xs !! n ! k"
  using assms
  by (induction n arbitrary: k i xs)
     (subst seidel_triangle_impl_aux.simps; simp add: Let_def rev_nth)+

lemma seidel_triangle_code [code]:
  "seidel_triangle a n k = (if k > n then 0 else seidel_triangle_impl_aux a [] 0 n k)"
  using seidel_triangle_impl_aux_correct[of k n 0 "[]" a]
        seidel_triangle_rows_aux_correct[of 0 "smap a nats" n]
  by (simp del: upt_Suc)

lemma entringer_number_code [code]:
  "entringer_number n k = seidel_triangle (\<lambda>n. if n = 0 then 1 else 0) n k"
  by (subst entringer_number_conv_seidel_triangle) auto

end