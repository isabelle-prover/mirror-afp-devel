(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Sumcheck Protocol\<close>

theory Sumcheck_Protocol
  imports 
    Public_Coin_Proofs
    Abstract_Multivariate_Polynomials
begin

subsection \<open>The sumcheck problem\<close>

text \<open>Type of sumcheck instances\<close>
type_synonym ('p, 'a, 'b) sc_inst = "'a set \<times> 'p \<times> 'b"

definition (in multi_variate_polynomial) 
  Sumcheck :: "('p, 'a, 'b) sc_inst set" where
  "Sumcheck = {(H, p, v) | H p v. v = (\<Sum>\<sigma>\<in>substs (vars p) H. eval p \<sigma>)}"


subsection \<open>The sumcheck protocol\<close>

text \<open>Type of the prover\<close> 
type_synonym ('p, 'a, 'b, 'v, 's) prover = "(('p, 'a, 'b) sc_inst, 'a, 'v, 'p, 's) prv"

text \<open>Here is how the expanded type lools like @{typ [display] "('p, 'a, 'b, 'v, 's) prover"}.\<close>


context multi_variate_polynomial begin

text \<open>Sumcheck function\<close>
fun sumcheck :: "('p, 'a, 'b, 'v, 's) prover \<Rightarrow> 's \<Rightarrow> ('p, 'a, 'b) sc_inst \<Rightarrow> 'a \<Rightarrow> ('v \<times> 'a) list \<Rightarrow> bool" where
  "sumcheck pr s (H, p, v) r_prev [] \<longleftrightarrow> v = eval p Map.empty"
| "sumcheck pr s (H, p, v) r_prev ((x, r) # rm) \<longleftrightarrow> 
     (let (q, s') = pr (H, p, v) x (map fst rm) r_prev s in
        vars q \<subseteq> {x} \<and> deg q \<le> deg p \<and>
        v = (\<Sum>y \<in> H. eval q [x \<mapsto> y]) \<and> 
        sumcheck pr s' (H, inst p [x \<mapsto> r], eval q [x \<mapsto> r]) r rm)"

text \<open>Honest prover definition\<close>
fun honest_prover :: "('p, 'a, 'b, 'v, unit) prover" where
  "honest_prover (H, p, _) x xs _ _ = (\<Sum>\<sigma> \<in> substs (set xs) H. inst p \<sigma>, ())"

declare honest_prover.simps [simp del]
lemmas honest_prover_def = honest_prover.simps 

text \<open>Lemmas on variables and degree of the honest prover.\<close>

lemma honest_prover_vars:
  assumes "vars p \<subseteq> insert x V" "finite V" "H \<noteq> {}" "finite H" 
  shows "vars (\<Sum>\<sigma>\<in>substs V H. inst p \<sigma>) \<subseteq> {x}" 
proof -
  have *: "\<And>\<sigma>. \<sigma> \<in> substs V H \<Longrightarrow> vars (inst p \<sigma>) \<subseteq> {x}" using assms
    by (metis (no_types, lifting) Diff_eq_empty_iff Diff_insert subset_iff substE vars_inst)

  have "vars (sum (inst p) (substs V H)) \<subseteq> (\<Union>\<sigma>\<in>substs V H. vars (inst p \<sigma>))" 
    using \<open>finite V\<close> \<open>finite H\<close>
    by (auto simp add: vars_sum substs_finite)
  also have "\<dots> \<subseteq> {x}" using \<open>H \<noteq> {}\<close> *
    by (auto simp add: substs_nonempty vars_finite substs_finite)
  finally show ?thesis .
qed

lemma honest_prover_deg:
  assumes "H \<noteq> {}" "finite V"
  shows "deg (\<Sum>\<sigma>\<in>substs V H. inst p \<sigma>) \<le> deg p"
proof - 
  have "deg (\<Sum>\<sigma>\<in>substs V H. inst p \<sigma>) \<le> Max {deg (inst p \<sigma>) |\<sigma>. \<sigma> \<in> substs V H}"
    by(auto simp add: substs_finite substs_nonempty deg_sum assms)
  also have "\<dots> \<le> deg p" 
    by(auto simp add: substs_finite substs_nonempty deg_inst assms)
  finally show ?thesis .
qed


subsection \<open>The sumcheck protocol as a public-coin proof instance\<close>

text \<open>Define verifier functions\<close>

fun sc_ver0 :: "('p, 'a, 'b) sc_inst \<Rightarrow> unit \<Rightarrow> bool" where
   "sc_ver0 (H, p, v) () \<longleftrightarrow> v = eval p Map.empty"

fun sc_ver1 :: 
  "('p, 'a, 'b) sc_inst \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> unit \<Rightarrow> bool \<times> ('p, 'a, 'b) sc_inst \<times> unit" 
where
   "sc_ver1 (H, p, v) q r x _ () = (
      vars q \<subseteq> {x} \<and> deg q \<le> deg p \<and> v = (\<Sum>y \<in> H. eval q [x \<mapsto> y]), 
      (H, inst p [x \<mapsto> r], eval q [x \<mapsto> r]), 
      ()
   )"

sublocale sc: public_coin_proof sc_ver0 sc_ver1 .


text \<open>Equivalence of @{term sumcheck} with public-coin proofs instance\<close>

lemma prove_sc_eq_sumcheck:
  \<open>sc.prove () pr ps (H, p, v) r rm = sumcheck pr ps (H, p, v) r rm\<close>
proof (induction "()" pr ps "(H, p, v)" r rm arbitrary: p v rule: sc.prove.induct)
  case (1 vs prv ps r)
  then show ?case by (simp)
next
  case (2 vs prv ps r r' rs x xs)
  then show ?case by (simp split:prod.split)
qed


end
end



