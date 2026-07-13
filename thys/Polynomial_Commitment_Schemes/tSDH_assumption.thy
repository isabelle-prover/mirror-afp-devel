theory tSDH_assumption

imports "Sigma_Commit_Crypto.Commitment_Schemes" "Berlekamp_Zassenhaus.Finite_Field"

begin

section \<open>The t-Strong Diffie-Hellman Assumption\<close>

text\<open>The t-SDH game and advantage as in section 2.3 of the original KZG paper
``Constant-Size Commitments to Polynomials and Their Applications'' \<^cite>\<open>KZG10\<close>.\<close>

locale t_SDH = G : cyclic_group G
  for G:: "('a, 'b) cyclic_group_scheme" (structure) 
  and t::nat  
  and to_type :: "nat \<Rightarrow> ('c::prime_card) mod_ring"
  and exp :: "'a \<Rightarrow> 'c mod_ring \<Rightarrow> 'a"
begin

type_synonym ('grp,'mr) adversary = "'grp list \<Rightarrow> ('mr mod_ring *'grp) spmf"

text \<open>The t-SDH game states that given a t+1-long tuple in the form of $(g, g^\alpha, g^{\alpha^2}, \ldots, g^{\alpha^t})$
the Adversary has to return an element c and $g^{1/(c+\alpha)}$.\<close>
definition game :: "('a,'c) adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    return_spmf (exp \<^bold>g (1/((to_type \<alpha>)+c)) = g) 
  } ELSE return_spmf False"

text \<open>The advantage is that the Adversary wins the game. 
For the t-SDH assumption to hold this advantage should be negligible.\<close>
definition advantage :: " ('a,'c) adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True" 

text \<open>An alternative but equivalent game for the t-SDH-game. This alternative game capsulates the 
event that the Adversary wins in the assert\_spmf statement.
adapted proof from Sigma\_Commit\_Crypto.Commitment\_Schemes bind\_game\_alt\_def\<close>
lemma game_alt_def:
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    _::unit \<leftarrow> assert_spmf (exp \<^bold>g (1/((to_type \<alpha>)+c)) = g);
    return_spmf True 
  } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
   have "?lhs = TRY do {
      \<alpha> \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
          TRY return_spmf (exp \<^bold>g (1/((to_type \<alpha>)+c)) = g) 
          ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      \<alpha> \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (exp \<^bold>g (1/((to_type \<alpha>)+c)) = g);
            return_spmf True
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = ?rhs"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  finally show ?thesis .
qed

end

end