(*  Title:       The Framework for competitive Analysis of randomized online algorithms
    Author:      Tobias Nipkow
                 Max Haslbeck
*)

theory Competitive_Analysis
imports
  Prob_Theory
  On_Off
begin
 

section "Competitive Analysis"

subsection "Probability Theory in Isabelle/HOL"

subsection "Competitive Analysis Formalized"
 
type_synonym ('s,'is,'r,'a)alg_on_step = "('s * 'is  \<Rightarrow> 'r \<Rightarrow> ('a * 'is) pmf)"
type_synonym ('s,'is)alg_on_init = "('s \<Rightarrow> 'is pmf)"
type_synonym ('s,'is,'q,'a)alg_on_rand = "('s,'is)alg_on_init * ('s,'is,'q,'a)alg_on_step"

section "classes of algorithms"


definition deterministic_init :: "('s,'is)alg_on_init \<Rightarrow> bool" where
  "deterministic_init I \<longleftrightarrow> (\<forall>init. card( set_pmf (I init)) = 1)"

definition deterministic_step :: "('s,'is,'q,'a)alg_on_step \<Rightarrow> bool" where
  "deterministic_step S \<longleftrightarrow> (\<forall>i is q. card( set_pmf (S (i, is) q)) = 1)"

definition random_step :: "('s,'is,'q,'a)alg_on_step \<Rightarrow> bool" where
  "random_step S \<longleftrightarrow> ~ deterministic_step S"

 
context On_Off
begin

  

fun steps where
  "steps s [] [] = s"
| "steps s (q#qs) (a#as) = steps (step s q a) qs as"


lemma T_append: "length qs = length as \<Longrightarrow> T s (qs@[q]) (as@[a]) = T s qs as + t (steps s qs as) q a"
apply(induct qs as arbitrary: s rule: list_induct2)
   by simp_all

abbreviation Step_rand :: "('state,'is,'request,'answer) alg_on_rand  \<Rightarrow> 'request \<Rightarrow> 'state * 'is \<Rightarrow> ('state * 'is) pmf" where
"Step_rand A r s \<equiv> bind_pmf ((snd A) s r) (\<lambda>(a,is'). return_pmf (step (fst s) r a, is'))"
 
fun config'_rand :: "('state,'is,'request,'answer) alg_on_rand  \<Rightarrow> ('state*'is) pmf \<Rightarrow> 'request list  
    \<Rightarrow> ('state * 'is) pmf" where
"config'_rand A s []  = s" |
"config'_rand A s (r#rs) = config'_rand A (s \<bind> Step_rand A r) rs"

lemma config'_rand_append: "config'_rand A s (rs@[r]) = config'_rand A s rs \<bind> Step_rand A r"
apply(induct rs arbitrary: s) by(simp_all)


abbreviation config_rand where
"config_rand A s0 rs == config'_rand A ((fst A s0) \<bind> (\<lambda>is. return_pmf (s0, is))) rs"

lemma config'_rand_induct: "(\<forall>x \<in> set_pmf init. P (fst x)) \<Longrightarrow> (\<And>s q a. P s \<Longrightarrow> P (step s q a))
     \<Longrightarrow> \<forall>x\<in>set_pmf (config'_rand A init qs). P (fst x)"
proof (induct qs arbitrary: init)
  case (Cons r rs)
  show ?case apply(simp)
    apply(rule Cons(1))
      apply(subst ball_simps(9)[where P=P, symmetric])
      apply(subst set_map_pmf[symmetric])   
      apply(simp only: map_bind_pmf)
      apply(simp add: bind_assoc_pmf bind_return_pmf split_def)
      using Cons(2,3) apply blast
      by fact
qed (simp)
 
lemma config_rand_induct: "P s0 \<Longrightarrow> (\<And>s q a. P s \<Longrightarrow> P (step s q a)) \<Longrightarrow> \<forall>x\<in>set_pmf (config_rand A s0 qs). P (fst x)"
using config'_rand_induct[of "((fst A s0) \<bind> (\<lambda>is. return_pmf (s0, is)))" P] by auto


fun T_on_rand' :: "('state,'is,'request,'answer) alg_on_rand \<Rightarrow> ('state*'is) pmf \<Rightarrow> 'request list \<Rightarrow>  real" where
"T_on_rand' A s [] = 0" |
"T_on_rand' A s (r#rs) = E ( s \<bind> (\<lambda>s. bind_pmf (snd A s r) (\<lambda>(a,is'). return_pmf (real (t (fst s) r a)))) )
                              + T_on_rand' A (s \<bind> Step_rand A r) rs"


lemma T_on_rand'_append: "T_on_rand' A s (xs@ys) = T_on_rand' A s xs + T_on_rand' A (config'_rand A s xs) ys"
apply(induct xs arbitrary: s) by simp_all   

abbreviation T_on_rand :: "('state,'is,'request,'answer) alg_on_rand \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> real" where
  "T_on_rand A s rs == T_on_rand' A (fst A s \<bind> (\<lambda>is. return_pmf (s,is))) rs" 

lemma T_on_rand_append: "T_on_rand A s (xs@ys) = T_on_rand A s xs + T_on_rand' A (config_rand A s xs) ys"
by(rule T_on_rand'_append)  

abbreviation "T_on_rand_n A s0 xs n == T_on_rand' A (config_rand A s0 (take n xs)) [xs!n]" 

lemma T_on_rand_as_sum: "T_on_rand A s0 rs = setsum (T_on_rand_n A s0 rs) {..<length rs} "
apply(induct rs rule: rev_induct)
  by(simp_all add: T_on_rand'_append  nth_append)


lemma T_on_rand'_nn: "T_on_rand' (I,S) s qs \<ge> 0"
apply(induct qs arbitrary: s) 
  apply(simp_all add: bind_return_pmf)
  apply(rule add_nonneg_nonneg)
  apply(rule E_nonneg) 
    by(simp_all add: split_def) 

lemma T_on_rand_nn: "T_on_rand (I,S) s0 qs \<ge> 0"
by (rule T_on_rand'_nn)
 
definition compet_rand :: "('state,'is,'request,'answer) alg_on_rand \<Rightarrow> real \<Rightarrow> 'state set \<Rightarrow> bool" where
"compet_rand A c S0 = (\<forall>s0\<in>S0. \<exists>b \<ge> 0. \<forall>qs. T_on_rand A s0 qs \<le> c * T_opt s0 qs + b)"


subsection "embedding of deterministic into randomized algorithms"

fun embedd :: "('state,'is,'request,'answer) alg_on \<Rightarrow> ('state,'is,'request,'answer) alg_on_rand" where
"embedd A = ( (\<lambda>s. return_pmf (fst A s))  ,
                  (\<lambda>s r. return_pmf (snd A s r)) )"

lemma T_deter_rand: "T_off (\<lambda>s0. (off2 A (s0, x))) s0 qs = T_on_rand' (embedd A) (return_pmf (s0,x)) qs"
apply(induct qs arbitrary: s0 x) 
  by(simp_all add: Step_def bind_return_pmf split: prod.split)

lemma T_on_embedd: "T_on A s0 qs = T_on_rand (embedd A) s0 qs"
using T_deter_rand[where x="fst A s0", of s0 qs A] by(auto simp: bind_return_pmf)
 
lemma compet_embedded: "compet A c S0 = compet_rand (embedd A) c S0"
unfolding compet_def compet_rand_def using T_on_embedd by metis

 
   
end 



end 
