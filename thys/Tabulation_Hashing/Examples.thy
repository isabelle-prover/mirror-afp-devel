theory Examples
imports
  Simple_Tabulation_Hashing
begin

section \<open>Examples\<close>

datatype alphabet = A | B | C

lemma UNIV_alphabet: "UNIV = {A,B,C}"
  by (smt (verit, del_insts) UNIV_eq_I alphabet.exhaust insertCI)

lemma finite_UNIV_alphabet: "finite (UNIV :: alphabet set)" unfolding UNIV_alphabet by simp

instantiation alphabet :: finite begin instance by (standard, fact finite_UNIV_alphabet) end

experiment begin

interpretation simple_tabulation_hashing "TYPE(2)" by standard auto

term "tb_S" (* :: "2 itself \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b ^ 'c) pmf" *)
term "tb_H" (* :: "'a ^ 2 \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b ^ 'c) \<Rightarrow> 'b ^ 'c" *)

(* we have to explicitly declare the signature of tb_S to instantiate the type variable 'n on each
   use. we can save some typing by using abbreviations *)
abbreviation "tb_S2 \<equiv> tb_S TYPE(2)"

lemma example1:
  shows "measure_pmf.prob tb_S2 {h.
    tb_H (vec_of_list [A,A]) h = (vec_of_list [True] :: (bool, 1) vec) \<and>
    tb_H (vec_of_list [B,B]) h = vec_of_list [False] \<and>
    tb_H (vec_of_list [B,A]) h = c}
    = 1 / 8"
  (* if you replace any one of the tb_H2 with tb_H, Isabelle can't apply the following lemma *)
  by (simp add: prob_tb_H_bin1_bin2_bin3 vec_of_list_inject card_UNIV_vec)

lemma example2:
  shows "measure_pmf.prob tb_S2 {h.
    tb_H (vec_of_list [A,A]) h = (a :: (bool, 3) vec) \<and>
    tb_H (vec_of_list [B,B]) h = b \<and>
    tb_H (vec_of_list [B,A]) h = c}
    = 1 / 512"
  by (simp add: prob_tb_H_bin1_bin2_bin3 vec_of_list_inject card_UNIV_vec)

lemma example3:
  fixes a b c :: "(bool, 3) vec"
  shows "measure_pmf.prob tb_S2 {h.
    tb_H (vec_of_list ''AA'') h = a \<and>
    tb_H (vec_of_list ''AB'') h = b \<and>
    tb_H (vec_of_list ''BA'') h = c}
    = 1 / 512"
  by (simp add: prob_tb_H_bin1_bin2_bin3 vec_of_list_inject card_UNIV_vec)

end (* experiment *)

experiment begin

(* using the ' version we can use types to fix 'result 'q and 'fragment *)
interpretation simple_tabulation_hashing'
  "TYPE(64)" \<comment> \<open>instantiate 'n\<close>
  "TYPE(bool)" "TYPE(3)" \<comment> \<open>instantiate 'result and 'q\<close>
  "TYPE(alphabet)" \<comment> \<open>instantiate 'fragment\<close>
  by unfold_locales simp_all

term "tb_S" (* :: "(nat \<Rightarrow> alphabet \<Rightarrow> bool ^ 3) pmf" *)
term "tb_H" (* :: "alphabet ^ 64 \<Rightarrow> (nat \<Rightarrow> alphabet  \<Rightarrow> bool ^ 3) \<Rightarrow> bool ^ 3" *)

lemma example4:
  assumes "card {x,y,z} = 3"
  shows "measure_pmf.prob (tb_S TYPE(64)) {h. \<forall> key\<in>{x,y,z}. tb_H key h = f key} = 1 / 512"
  using assms three_universal
  by (subst measure_pmf.k_universal_probD'[where R = R])
    (simp_all add: card_UNIV_vec power_one_over)
end (* experiment *)

end (* theory *)