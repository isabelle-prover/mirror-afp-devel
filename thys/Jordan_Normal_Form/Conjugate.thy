(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
theory Conjugate
  imports Complex
begin

class conjugate =
  fixes conjugate :: "'a \<Rightarrow> 'a"
  assumes conjugate_id[simp]: "conjugate (conjugate a) = a"
      and conjugate_cancel_iff[simp]: "conjugate a = conjugate b \<longleftrightarrow> a = b"

class conjugatable_field = field + conjugate +
  assumes conjugate_dist_mul: "conjugate (a * b) = conjugate a * conjugate b"
      and conjugate_dist_add: "conjugate (a + b) = conjugate a + conjugate b"
      and conjugate_neg: "conjugate (-a) = - conjugate a"
      and conjugate_zero[simp]: "conjugate 0 = 0"
begin
  lemma conjugate_zero_iff[simp]: "conjugate a = 0 \<longleftrightarrow> a = 0"
    using conjugate_cancel_iff[of _ 0, unfolded conjugate_zero].
end

lemma setsum_conjugate:
  fixes f :: "'b \<Rightarrow> 'a :: conjugatable_field"
  assumes finX: "finite X"
  shows "conjugate (setsum f X) = setsum (\<lambda>x. conjugate (f x)) X"
  using finX by (induct set:finite, auto simp: conjugate_dist_add)

class conjugatable_ordered_field = conjugatable_field + ordered_comm_monoid_add +
  assumes conjugate_square_positive: "a * conjugate a \<ge> 0"
begin
  lemma conjugate_square_0: "a * conjugate a = 0 \<Longrightarrow> a = 0" by auto
end

subsection {* Instantiations *}

instantiation complex :: conjugatable_ordered_field
begin
  definition [simp]: "conjugate \<equiv> cnj"
  definition [simp]: "x < y \<equiv> Im x = Im y \<and> Re x < Re y"
  definition [simp]: "x \<le> y \<equiv> Im x = Im y \<and> Re x \<le> Re y"
  
  instance by (intro_classes, auto simp: complex.expand)
end

instantiation real :: conjugatable_ordered_field
begin
  definition [simp]: "conjugate (x::real) \<equiv> x"
  instance by (intro_classes, auto)
end

instantiation rat :: conjugatable_ordered_field
begin
  definition [simp]: "conjugate (x::rat) \<equiv> x"
  instance by (intro_classes, auto)
end

end