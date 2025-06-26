theory Ad_Codegen_Example
  imports Hidden_Number_Problem

(* This theory file is to demonstrate the executable adversary. It is not meant to be imported. *)
begin

section "This theory demonstrates an example of the executable adversary."

text "@{const full_babai} does not need a global interpretation to be executed."
value "full_babai [vec_of_list [0, 1], vec_of_list [2, 3]] (vec_of_list [2.3, 6.4]) (4/3)"

text "Let's define our \<open>d\<close>, \<open>n\<close>, \<open>p\<close>, \<open>\<alpha>\<close>, and \<open>k\<close>."
abbreviation "d \<equiv> 72"
abbreviation "n \<equiv> 1279"
abbreviation "p \<equiv> (2::nat)^1279 - 1"
abbreviation "\<alpha> \<equiv> p div 3"
abbreviation "k \<equiv> 47"

value "p"
value "\<alpha>"

text "Since our adversary definition is inside a locale, we need a global interpretation."
global_interpretation ad_interp: hnp_adversary d p
  defines \<A> = ad_interp.\<A>
  and int_gen_basis = ad_interp.int_gen_basis
  and int_to_nat_residue = ad_interp.int_to_nat_residue
  and ts_from_pairs = ad_interp.ts_from_pairs
  and scaled_uvec_from_pairs = ad_interp.scaled_uvec_from_pairs
  and \<A>_vec = ad_interp.\<A>_vec
  by unfold_locales

text "For this example, we use our executable msb function."
abbreviation "\<O> \<equiv> \<lambda>t. msb k n ((\<alpha> * t) mod p)"

definition inc_amt :: "nat" where "inc_amt = p div 5"

fun gen_ts :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "gen_ts 0 t = []"
| "gen_ts (Suc i) t = t # (gen_ts i ((t + inc_amt) mod p))"

definition gen_pairs :: "(nat \<times> nat) list" where
  "gen_pairs = map (\<lambda>t. (t, \<O> t)) (gen_ts d 1)"

text "The @{const gen_pairs} function generates the data that the adversary receives.
We prove that the adversary is likely to be successful when the \<open>ts\<close> which define this data
are uniformly distributed.
Here, we use the @{const gen_ts} function to generate an explicit list of \<open>ts\<close>."

value "length gen_pairs"

value "gen_pairs"

value "ad_interp.\<A> gen_pairs"

value "\<alpha>"

end
