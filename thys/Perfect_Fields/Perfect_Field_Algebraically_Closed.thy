(*
  File:      Perfect_Fields/Perfect_Field_Algebraically_Closed.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  The connection between algebraically closed fields and perfect fields.
  Should probably be moved to the main file as soon as algebraically closed
  fields are available in the distribution.
*)
subsection \<open>Algebraically closed fields are perfect\<close>
theory Perfect_Field_Algebraically_Closed
  imports Perfect_Fields "Formal_Puiseux_Series.Formal_Puiseux_Series"
begin

(* TODO: the alg_closed_field type class should be moved from
   Formal_Puiseux_Series into the distribution.
*)

(* TODO: Move to wherever alg_closed_field is defined. *)
lemma (in alg_closed_field) nth_root_exists:
  assumes "n > 0"
  shows   "\<exists>y. y ^ n = (x :: 'a)"
proof -
  define f where "f = (\<lambda>i. if i = 0 then -x else if i = n then 1 else 0)"
  have "\<exists>x. (\<Sum>k\<le>n. f k * x ^ k) = 0"
    by (rule alg_closed) (use assms in \<open>auto simp: f_def\<close>)
  also have "(\<lambda>x. \<Sum>k\<le>n. f k * x ^ k) = (\<lambda>x. \<Sum>k\<in>{0,n}. f k * x ^ k)"
    by (intro ext sum.mono_neutral_right) (auto simp: f_def)
  finally show "\<exists>y. y ^ n = x"
    using assms by (simp add: f_def)
qed


context alg_closed_field
begin

lemma alg_closed_surj_frob:
  assumes "CHAR('a) > 0"
  shows   "surj (frob :: 'a \<Rightarrow> 'a)"
proof -
  show "surj (frob :: 'a \<Rightarrow> 'a)"
  proof safe
    fix x :: 'a
    obtain y where "y ^ CHAR('a) = x"
      using nth_root_exists CHAR_pos assms by blast
    hence "frob y = x"
      using CHAR_pos by (simp add: frob_def)
    thus "x \<in> range frob"
      by (metis rangeI)
  qed auto
qed

sublocale perfect_field
  by standard (use alg_closed_surj_frob in auto)

end


(* TODO move: some properties of formal Puiseux series *)
lemma fpxs_const_eq_0_iff [simp]: "fpxs_const x = 0 \<longleftrightarrow> x = 0"
  by (metis fpxs_const_0 fpxs_const_eq_iff)

lemma semiring_char_fpxs [simp]: "CHAR('a :: comm_semiring_1 fpxs) = CHAR('a)"
  by (rule CHAR_eqI; unfold of_nat_fpxs_eq) (auto simp: of_nat_eq_0_iff_char_dvd)

instance fpxs :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance fpxs :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance fpxs :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance fpxs :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard
instance fpxs :: ("field_prime_char") field_prime_char
  by standard auto

end