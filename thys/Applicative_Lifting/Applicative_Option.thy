(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Option\<close>

theory Applicative_Option imports
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
begin

fun ap_option :: "('a \<Rightarrow> 'b) option \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
    "ap_option (Some f) (Some x) = Some (f x)"
  | "ap_option _ _ = None"

abbreviation (input) pure_option :: "'a \<Rightarrow> 'a option"
where "pure_option \<equiv> Some"

adhoc_overloading Applicative.pure pure_option
adhoc_overloading Applicative.ap ap_option

lemma some_ap_option: "ap_option (Some f) x = map_option f x"
by (cases x) simp_all

lemma ap_some_option: "ap_option f (Some x) = map_option (\<lambda>g. g x) f"
by (cases f) simp_all

applicative option (C, W)
for
  pure: Some
  ap: ap_option
proof -
  interpret applicative_syntax .
  { fix x :: "'a option"
    show "pure (\<lambda>x. x) \<diamondop> x = x" by (cases x) simp_all
  next
    fix g :: "('c \<Rightarrow> 'b) option" and f :: "('a \<Rightarrow> 'c) option" and x
    show "pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
      by (cases g f x rule: option.exhaust[case_product option.exhaust, case_product option.exhaust]) simp_all
  next
    fix f :: "('c \<Rightarrow> 'b \<Rightarrow> 'a) option" and x y
    show "pure (\<lambda>f x y. f y x) \<diamondop> f \<diamondop> x \<diamondop> y = f \<diamondop> y \<diamondop> x"
      by (cases f x y rule: option.exhaust[case_product option.exhaust, case_product option.exhaust]) simp_all
  next
    fix f :: "('b \<Rightarrow> 'b \<Rightarrow> 'a) option" and x
    show "pure (\<lambda>f x. f x x) \<diamondop> f \<diamondop> x = f \<diamondop> x \<diamondop> x"
      by (cases f x rule: option.exhaust[case_product option.exhaust]) simp_all
  }
qed (simp_all add: some_ap_option ap_some_option)

no_adhoc_overloading Applicative.pure pure_option -- \<open>We do not want to print all occurrences of @{const "Some"} as @{const "pure"}\<close>

end