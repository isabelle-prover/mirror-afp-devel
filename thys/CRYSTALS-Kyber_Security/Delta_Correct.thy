theory Delta_Correct

imports "HOL-Probability.Probability"

begin 
section \<open>$\delta$-Correctness of PKEs\<close>
text \<open>The following locale defines the $\delta$-correctness of a public key encryption (PKE) scheme
given by the algorithms \<open>key_gen\<close> \<open>encrypt\<close> and \<open>decrypt\<close>.
\<open>Msgs\<close> is the set of all possible messages that can be encoded with the PKE.
Since some PKE have a small failure probability, the definition of correctness has to be 
adapted to cover the case of failures as well. 
The standard definition of such $\delta$-correctness is given in the function \<open>expect_correct\<close>.\<close>
locale pke_delta_correct =
fixes key_gen :: "('pk \<times> 'sk) pmf"
  and encrypt :: "'pk \<Rightarrow> 'plain \<Rightarrow> 'cipher pmf" 
  and decrypt :: "'sk \<Rightarrow> 'cipher \<Rightarrow> 'plain"
  and Msgs :: "'plain set"
begin

type_synonym ('pk', 'sk') cor_adversary = "('pk' \<Rightarrow> 'sk' \<Rightarrow> bool pmf)"

definition expect_correct where
"expect_correct = measure_pmf.expectation key_gen
  (\<lambda>(pk,sk). MAX m\<in>Msgs. pmf (bind_pmf (encrypt pk m)
  (\<lambda>c. return_pmf (decrypt sk c \<noteq> m))) True)"

definition delta_correct where
"delta_correct delta = (expect_correct \<le> delta)"

text \<open>\<open>game_correct\<close> is the game played to guarantee correctness. If an adversary \<open>Adv\<close> has a 
non-negligible advantage in the correctness game, he might have enough information to break 
the PKE.
However, the definition of this correctness game is somewhat questionable, since the adversary 
\<open>Adv\<close> is given the secret key as well, thus enabling him to break the encryption and the PKE.\<close>

definition game_correct where
"game_correct Adv = do{
      (pk,sk) \<leftarrow> key_gen;
      m \<leftarrow> Adv pk sk;
      c \<leftarrow> encrypt pk m;
      let m' = decrypt sk c;
      return_pmf (m' \<noteq> m)
    }"


end

text \<open>An auxiliary lemma to handle the maximum over a sum.\<close>

lemma max_sum:
fixes A B and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {ordered_comm_monoid_add, linorder}"
assumes "finite A " "A \<noteq> {}"
shows "(MAX x\<in>A. (\<Sum>y\<in>B. f x y)) \<le> (\<Sum>y\<in>B. (MAX x\<in>A. f x y))"
proof -
  obtain x where "x\<in>A" and "(\<Sum>y\<in>B. f x y) = (MAX x\<in>A. (\<Sum>y\<in>B. f x y))" using assms
  by (metis (no_types, lifting) Max_in finite_imageI imageE image_is_empty)
  moreover have "(\<Sum>y\<in>B. f x y) \<le> (\<Sum>y\<in>B. MAX x\<in>A. f x y)" 
    by (intro sum_mono) (simp add: assms(1) calculation(1))
  ultimately show ?thesis by metis
qed

end