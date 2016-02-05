(* Author: Tobias Nipkow *)

section "Deterministic Online and Offline Algorithms"

theory On_Off
imports Complex_Main
begin

type_synonym ('s,'r,'a) alg_off = "'s \<Rightarrow> 'r list \<Rightarrow> 'a list"
type_synonym ('s,'is,'r,'a) alg_on = "('s \<Rightarrow> 'is) * ('s * 'is \<Rightarrow> 'r \<Rightarrow> 'a * 'is)"

locale On_Off =
fixes step :: "'state \<Rightarrow> 'request \<Rightarrow> 'answer \<Rightarrow> 'state"
fixes t :: "'state \<Rightarrow> 'request \<Rightarrow> 'answer \<Rightarrow> nat"
begin

fun T :: "'state \<Rightarrow> 'request list \<Rightarrow> 'answer list \<Rightarrow> nat" where
"T s [] [] = 0" |
"T s (r#rs) (a#as) = t s r a + T (step s r a) rs as"

definition Step ::
  "('state * 'istate \<Rightarrow> 'request \<Rightarrow> 'answer * 'istate)
   \<Rightarrow> 'state * 'istate \<Rightarrow> 'request \<Rightarrow> 'state * 'istate"
where
"Step stp s r = (let (a,is') = stp s r in (step (fst s) r a, is'))"

fun off2 :: "('state * 'is \<Rightarrow> 'request \<Rightarrow> 'answer * 'is) \<Rightarrow> ('state * 'is,'request,'answer) alg_off" where
"off2 stp s [] = []" |
"off2 stp s (r#rs) = fst (stp s r) # off2 stp (Step stp s r) rs"

abbreviation off :: "('state,'is,'request,'answer) alg_on \<Rightarrow> ('state,'request,'answer) alg_off" where
"off A s0 \<equiv> off2 (snd A) (s0, fst A s0)"

abbreviation T_off :: "('state,'request,'answer) alg_off \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_off A s0 rs == T s0 rs (A s0 rs)"

abbreviation T_on :: "('state,'is,'request,'answer) alg_on \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_on A == T_off (off A)"

definition T_opt :: "'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_opt s rs = Inf {T s rs as | as. size as = size rs}"

definition compet :: "('state,'is,'request,'answer) alg_on \<Rightarrow> real \<Rightarrow> 'state set \<Rightarrow> bool" where
"compet A c S0 = (\<forall>s0\<in>S0. \<exists>b \<ge> 0. \<forall>rs. real(T_on A s0 rs) \<le> c * T_opt s0 rs + b)"

lemma length_off[simp]: "length(off2 A s rs) = length rs"
by (induction rs arbitrary: s) (auto split: prod.split)

lemma compet_mono: assumes "compet A c S0" and "c \<le> c'"
shows "compet A c' S0"
proof (unfold compet_def, auto)
  let ?compt = "\<lambda>s0 rs b (c::real). T_on A s0 rs \<le> c * T_opt s0 rs + b"
  fix s0 assume "s0 \<in> S0"
  with assms(1) obtain b where "b \<ge> 0" and 1: "\<forall>rs. ?compt s0 rs b c"
    by(auto simp: compet_def)
  have "\<forall>rs.  ?compt s0 rs b c'"
  proof
    fix rs
    from 1 have "?compt s0 rs b c" ..
    thus "?compt s0 rs b c'"
      using 1 mult_right_mono[OF assms(2) of_nat_0_le_iff[of "T_opt s0 rs"]]
      by arith
  qed
  thus "\<exists>b\<ge>0. \<forall>rs. ?compt s0 rs b c'" using `b\<ge>0` by(auto)
qed

lemma competE: fixes c :: real
assumes "compet A c S0" "c \<ge> 0" "\<forall>s0 rs. size(aoff s0 rs) = length rs" "s0\<in>S0"
shows "\<exists>b\<ge>0. \<forall>rs. T_on A s0 rs \<le> c * T_off aoff s0 rs + b"
proof -
  from assms(1,4) obtain b where "b\<ge>0" and
    1: "\<forall>rs. T_on A s0 rs \<le> c * T_opt s0 rs + b"
    by(auto simp add: compet_def)
  { fix rs
    have 2: "real(T_on A s0 rs) \<le> c * Inf {T s0 rs as | as. size as = size rs} + b"
      (is "_ \<le> _ * real(Inf ?T) + _")
      using 1 by(auto simp add: T_opt_def)
    have "Inf ?T \<le> T_off aoff s0 rs"
      using assms(3) by (intro cInf_lower) auto
    from mult_left_mono[OF of_nat_le_iff[THEN iffD2, OF this] assms(2)]
    have "T_on A s0 rs \<le> c * T_off aoff s0 rs + b" using 2 by arith
  }
  thus ?thesis using `b\<ge>0` by(auto simp: compet_def)
qed

end

end