(* Author: Alexander Maletzky *)

section \<open>Code Equations and Useful Functions related to the Computation of Gr\"obner Bases\<close>

theory Algorithm_Schema_Impl
  imports Algorithm_Schema Polynomials.MPoly_Type_Class_OAlist
begin

lemma card_keys_MP_oalist [code]: "card_keys (MP_oalist xs) = length (fst (list_of_oalist_ntm xs))"
proof -
  let ?rel = "ko.lt (key_order_of_nat_term_order_inv (snd (list_of_oalist_ntm xs)))"
  have "irreflp ?rel" by (simp add: irreflp_def)
  moreover have "transp ?rel" by (simp add: lt_of_nat_term_order_alt)
  ultimately have *: "distinct (map fst (fst (list_of_oalist_ntm xs)))" using oa_ntm.list_of_oalist_sorted
    by (rule distinct_sorted_wrt_irrefl)
  have "card_keys (MP_oalist xs) = length (map fst (fst (list_of_oalist_ntm xs)))"
    by (simp only: card_keys_def keys_MP_oalist image_set o_def oa_ntm.sorted_domain_def[symmetric],
        rule distinct_card, fact *)
  also have "... = length (fst (list_of_oalist_ntm xs))" by simp
  finally show ?thesis .
qed

subsection \<open>Generating Cyclic Polynomials\<close>

definition cycl_pp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) pp"
  where "cycl_pp n d i = sparse\<^sub>0 (map (\<lambda>k. (modulo (k + i) n, 1)) [0..<d])"

definition cyclic :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::{zero,one,uminus}) list"
  where "cyclic to n =
            (let xs = [0..<n] in
              (map (\<lambda>d. distr\<^sub>0 to (map (\<lambda>i. (cycl_pp n d i, 1)) xs)) [1..<n]) @ [distr\<^sub>0 to [(cycl_pp n n 0, 1), (0, -1)]]
            )"

text \<open>\<open>cyclic n\<close> is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates, with maximum degree \<open>n\<close>.\<close>

subsection \<open>Generating Katsura Polynomials\<close>

definition Katsura_poly :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 rat)"
  where "Katsura_poly to n i =
            change_ord to ((\<Sum>j=-(int n)..<(int n) + 1 - i. V\<^sub>0 (nat (abs j)) * V\<^sub>0 (nat (abs j + i))) - V\<^sub>0 i)"

definition Katsura :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 rat) list"
  where "Katsura to n =
          (let xs = [0..<n] in
            (distr\<^sub>0 to ((sparse\<^sub>0 [(0, 1)], 1) # (map (\<lambda>i. (sparse\<^sub>0 [(Suc i, 1)], 2)) xs) @ [(0, -1)])) # (map (Katsura_poly to n) xs)
          )"

text \<open>\<open>Katsura n\<close> is a system of \<open>n + 1\<close> polynomials in \<open>n + 1\<close> indeterminates, with maximum degree \<open>2\<close>.\<close>

end (* theory *)
