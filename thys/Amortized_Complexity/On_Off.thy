(* Author: Tobias Nipkow *)

section "Deterministic Online and Offline Algorithms"

theory On_Off
imports Complex_Main
begin

locale On_Off =
fixes step :: "'state \<Rightarrow> 'request \<Rightarrow> 'answer \<Rightarrow> 'state"
fixes t :: "'state \<Rightarrow> 'request \<Rightarrow> 'answer \<Rightarrow> nat"
begin

type_synonym ('s,'q,'a)alg_off = "'s \<Rightarrow> 'q list \<Rightarrow> 'a list"
type_synonym ('s,'q,'a)alg_on = "'s \<Rightarrow> 'q \<Rightarrow> 'a"

fun T :: "'state \<Rightarrow> 'request list \<Rightarrow> 'answer list \<Rightarrow> nat" where
"T s [] [] = 0" |
"T s (q#qs) (a#as) = t s q a + T (step s q a) qs as"

fun off :: "('state,'request,'answer) alg_on \<Rightarrow> ('state,'request,'answer) alg_off" where
"off A s [] = []" |
"off A s (q#qs) = A s q # off A (step s q (A s q)) qs"

abbreviation T_off :: "('state,'request,'answer) alg_off \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_off A init qs == T init qs (A init qs)"

abbreviation T_on :: "('state,'request,'answer) alg_on \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_on A == T_off (off A)"

definition T_opt :: "'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_opt s qs = Inf {T s qs as | as. size as = size qs}"

definition compet :: "('state,'request,'answer) alg_on \<Rightarrow> real \<Rightarrow> 'state set \<Rightarrow> bool" where
"compet A c S0 = (\<forall>s0\<in>S0. \<exists>b \<ge> 0. \<forall>qs. real(T_on A s0 qs) \<le> c * T_opt s0 qs + b)"

lemma length_off[simp]: "length(off A s qs) = length qs"
by (induction qs arbitrary: s) auto

lemma compet_mono: assumes "compet A c S0" and "c \<le> c'"
shows "compet A c' S0"
proof (unfold compet_def, auto)
  let ?compt = "\<lambda>s0 qs b (c::real). T_on A s0 qs \<le> c * T_opt s0 qs + b"
  fix s0 assume "s0 \<in> S0"
  with assms(1) obtain b where "b \<ge> 0" and 1: "\<forall>qs. ?compt s0 qs b c"
    by(auto simp: compet_def)
  have "\<forall>qs.  ?compt s0 qs b c'"
  proof
    fix qs
    from 1 have "?compt s0 qs b c" ..
    thus "?compt s0 qs b c'"
      using 1 mult_right_mono[OF assms(2) of_nat_0_le_iff[of "T_opt s0 qs"]]
      by arith
  qed
  thus "\<exists>b\<ge>0. \<forall>qs. ?compt s0 qs b c'" using `b\<ge>0` by(auto)
qed

lemma competE: fixes c :: real
assumes "compet A c S0" "c \<ge> 0" "\<forall>s0 qs. size(aoff s0 qs) = length qs" "s0\<in>S0"
shows "\<exists>b\<ge>0. \<forall>qs. T_on A s0 qs \<le> c * T_off aoff s0 qs + b"
proof -
  from assms(1,4) obtain b where "b\<ge>0" and
    1: "\<forall>qs. T_on A s0 qs \<le> c * T_opt s0 qs + b"
    by(auto simp add: compet_def)
  { fix qs
    have 2: "real(T_on A s0 qs) \<le> c * Inf {T s0 qs as | as. size as = size qs} + b"
      (is "_ \<le> _ * real(Inf ?T) + _")
      using 1 by(auto simp add: T_opt_def)
    have "Inf ?T \<le> T_off aoff s0 qs"
      using assms(3) by (intro cInf_lower) auto
    from mult_left_mono[OF of_nat_le_iff[THEN iffD2, OF this] assms(2)]
    have "T_on A s0 qs \<le> c * T_off aoff s0 qs + b" using 2 by arith
  }
  thus ?thesis using `b\<ge>0` by(auto simp: compet_def)
qed

end

end