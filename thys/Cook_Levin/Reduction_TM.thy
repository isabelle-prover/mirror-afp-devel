chapter \<open>Turing machines for reducing $\NP$ languages to \SAT{}\label{s:Red_TM}\<close>

theory Reduction_TM
  imports Sat_TM_CNF Oblivious_2_Tape
begin

text \<open>
At long last we are going to create a polynomial-time Turing machine that, for a
fixed language $L\in\NP$, computes for every string $x$ a CNF formula $\Phi$
such that $x\in L$ iff.\ $\Phi$ is satisfiable. This concludes the proof of the
Cook-Levin theorem.

The CNF formula $\Phi$ is a conjunction of formulas $\Phi_0, \dots, \Phi_9$, and
the previous chapter has provided us with Turing machines @{const tm_PHI0},
@{const tm_PHI1}, etc.\ that are supposed to generate these formulas. But only
for $\Phi_9$ has this been proven yet. So our first task is to transfer the
Turing machines @{const tm_PHI0}, $\dots$, @{const tm_PHI8} into the locale
@{locale reduction_sat_x} and show that they really do generate the CNF formulas
$\Phi_0, \dots, \Phi_8$.

The TMs require certain values on their tapes prior to starting. Therefore we
build a Turing machine that computes these values. Then, in a final effort, we
combine all these TMs to create this article's biggest Turing machine.
\<close>


section \<open>Turing machines for parts of $\Phi$ revisited\<close>

text \<open>
In this section we restate the semantic lemmas @{text "transforms_tm_PHI0"}
etc.\ of the Turing machines @{const tm_PHI0} etc.\ in the context of the locale
@{locale reduction_sat_x}. This means that the lemmas now have terms like @{term
"formula_n \<Phi>\<^sub>0"} in them instead of more complicated expressions. It also means
that we more clearly see which values the tapes need to contain initially
because they are now expressed in terms of values in the locale, such as $n$,
$p(n)$, or $m'$.

\null
\<close>

context reduction_sat_x
begin

lemma tm_PHI0 [transforms_intros]:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k :: nat
  assumes "length tps = k" and "1 < j" and "j + 8 < k"
  assumes
    "tps ! 1 = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! j = (\<lfloor>m'\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
    [j := (\<lfloor>Suc (Suc m')\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>nll_Psi (Suc (Suc m') * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape (formula_n \<Phi>\<^sub>0)]"
  assumes "ttt = 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2"
  shows "transforms (tm_PHI0 j) tps ttt tps'"
proof -
  have "nll_Psi (m' * H) H 1 = formula_n (\<Psi> (\<zeta>\<^sub>0 0) 1)"
    using nll_Psi zeta0_def m' by simp
  moreover have "nll_Psi (H + m' * H) H 1 = formula_n (\<Psi> (\<zeta>\<^sub>1 0) 1)"
    using nll_Psi zeta1_def m'
    by (smt (verit) ab_semigroup_add_class.add_ac(1) add.commute add_cancel_left_right mult_2 mult_zero_left)
  moreover have "nll_Psi (Suc (Suc m') * H) H 0 = formula_n (\<Psi> (\<zeta>\<^sub>2 0) 0)"
  proof -
    have "Suc (Suc m') * H = N + 2 * H"
      using m' by simp
    moreover have "Suc (Suc m') * H + H = N + (Suc 0) * Z"
      using m' Z_def by simp
    ultimately have "\<zeta>\<^sub>2 0 = [Suc (Suc m') * H..<Suc (Suc m') * H + H]"
      using zeta2_def by (metis Nat.add_0_right mult_zero_left)
    then show ?thesis
      using nll_Psi by simp
  qed
  ultimately have "nll_Psi (m' * H) H 1 @ nll_Psi (H + m' * H) H 1 @ nll_Psi (Suc (Suc m') * H) H 0 =
      formula_n \<Phi>\<^sub>0"
    using formula_n_def PHI0_def by simp
  then show ?thesis
    using transforms_tm_PHI0I[OF assms(1-3) H_ge_3 assms(4-13)] assms(14,15) by simp
qed

lemma tm_PHI1 [transforms_intros]:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 7 < k"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
    [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>nll_Psi 0 H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>1)]"
  assumes "ttt = 1875 * H ^ 4"
  shows "transforms (tm_PHI1 j) tps ttt tps'"
proof -
  have "nll_Psi 0 H 1 = formula_n (\<Psi> ([0..<H]) 1)"
    using nll_Psi by simp
  then have "nll_Psi 0 H 1 = formula_n (\<Psi> (\<gamma> 0) 1)"
    using gamma_def by simp
  then have "nll_Psi 0 H 1 = formula_n \<Phi>\<^sub>1"
    using PHI1_def by simp
  then show ?thesis
    using transforms_tm_PHI1I[OF assms(1-3) H_ge_3 assms(4-12)] assms(13,14) by simp
qed

lemma tm_PHI2 [transforms_intros]:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 8 < k"
  assumes "idx = n "
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2"
  assumes "tps' = tps
    [j := (\<lfloor>2 * idx + 2\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * idx)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>2)]"
  shows "transforms (tm_PHI2 j) tps ttt tps'"
proof -
  have "nll_Psi (H + 2 * idx * H) H 3 @ nll_Psi (2 * H + 2 * idx * H) H 3 = formula_n \<Phi>\<^sub>2"
  proof -
    have "\<gamma> (2 * n + 1) = [H + 2 * idx * H..<H + 2 * idx * H + H]"
      using assms(4) gamma_def by simp
    moreover have "\<gamma> (2 * n + 2) = [2 * H + 2 * idx * H..<2 * H + 2 * idx * H + H]"
      using assms(4) gamma_def by simp
    ultimately show "nll_Psi (H + 2 * idx * H) H 3 @ nll_Psi (2 * H + 2 * idx * H) H 3 = formula_n \<Phi>\<^sub>2"
      using nll_Psi PHI2_def formula_n_def by simp
  qed
  then show ?thesis
    using transforms_tm_PHI2I[OF assms(1-3) H_ge_3 assms(5-14)] assms(15,16) by simp
qed

lemma PHI3_correct: "concat (map (\<lambda>i. nll_Psi (H * (1 + 2 * i)) H 2) [0..<n]) = formula_n \<Phi>\<^sub>3"
proof -
  have "nll_Psi (H * (1 + 2 * i)) H 2 = formula_n (\<Psi> (\<gamma> (2*i+1)) 2)" for i
  proof -
    have "\<gamma> (2 * i + 1) = [H * (1 + 2 * i)..<H * (1 + 2 * i) + H]"
      using gamma_def by (simp add: mult.commute)
    then show ?thesis
      using nll_Psi by simp
  qed
  then have "concat (map (\<lambda>i. nll_Psi (H * (1 + 2 * i)) H 2) [0..<n]) =
      concat (map (\<lambda>i. formula_n (\<Psi> (\<gamma> (2*i+1)) 2)) [0..<n])"
    by simp
  also have "... = formula_n (concat (map (\<lambda>i. \<Psi> (\<gamma> (2*i+1)) 2) [0..<n]))"
    using concat_formula_n by simp
  also have "... = formula_n \<Phi>\<^sub>3"
    using PHI3_def by simp
  finally show ?thesis .
qed

lemma tm_PHI3:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 8 < k"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
  assumes "tps' = tps
    [j := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>3),
     j + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_PHI345 2 j) tps ttt tps'"
  using transforms_tm_PHI345I[OF assms(1,2,3) H_ge_3, of 2 2 nss 1 "n "] H_gr_2 assms PHI3_correct
  by fastforce

lemma PHI4_correct:
  assumes "idx = 2 * n + 2 + 1" and "kappa = 2" and "step = 2" and "numiter = p n"
  shows "concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<numiter]) = formula_n \<Phi>\<^sub>4"
proof -
  have "nll_Psi (H * (idx + step * i)) H kappa = formula_n (\<Psi> (\<gamma> (2 * n + 2 + 2 * i + 1)) 2)" for i
  proof -
    have "\<gamma> (2 * n + 2 + 2 * i + 1) = [H * (idx + step * i)..<H * (idx + step * i) + H]"
      using assms gamma_def by (simp add: add.commute mult.commute)
    then show ?thesis
      using nll_Psi assms by simp
  qed
  then have "concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<numiter]) =
      concat (map (\<lambda>i. formula_n (\<Psi> (\<gamma> (2 * n + 2 + 2 * i + 1)) 2)) [0..<numiter])"
    by simp
  also have "... = formula_n (concat (map (\<lambda>i. \<Psi> (\<gamma> (2 * n + 2 + 2 * i + 1)) 2) [0..<p n]))"
    using assms concat_formula_n by simp
  also have "... = formula_n \<Phi>\<^sub>4"
    using PHI4_def by simp
  finally show ?thesis .
qed

lemma tm_PHI4:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt step k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 8 < k" assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>2 * n + 2 + 1\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (2 * n + 2 + 1 + 2 * p n))\<^sup>2))"
  assumes "tps' = tps
    [j := (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>4),
     j + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_PHI345 2 j) tps ttt tps'"
  using transforms_tm_PHI345I[OF assms(1,2,3) H_ge_3, of 2 2 nss "2 * n + 2 + 1" "p n"] H_gr_2 assms PHI4_correct
  by fastforce

lemma PHI5_correct:
  assumes "idx = 2 * n + 2 * p n + 3" and "kappa = 0" and "step = 1" and "numiter = T' "
  shows "concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<numiter]) = formula_n \<Phi>\<^sub>5"
proof -
  have "nll_Psi (H * (idx + step * i)) H kappa = formula_n (\<Psi> (\<gamma> (2 * n + 2 * p n + 3 + i)) 0)" for i
  proof -
    have "\<gamma> (2 * n + 2 * p n + 3 + i) = [H * (idx + step * i)..<H * (idx + step * i) + H]"
      using assms gamma_def by (simp add: add.commute mult.commute)
    then show ?thesis
      using nll_Psi assms by simp
  qed
  then have "concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<numiter]) =
      concat (map (\<lambda>i. formula_n (\<Psi> (\<gamma> (2 * n + 2 * p n + 3 + i)) 0)) [0..<numiter])"
    by simp
  also have "... = formula_n (concat (map (\<lambda>i. \<Psi> (\<gamma> (2 * n + 2 * p n + 3 + i)) 0) [0..<T']))"
    using assms concat_formula_n by simp
  also have "... = formula_n \<Phi>\<^sub>5"
    using PHI5_def by simp
  finally show ?thesis .
qed

lemma tm_PHI5:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 8 < k"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>2 * n + 2 * p n + 3\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>2 * n + 2 * p n + 3 + T'\<rfloor>\<^sub>N, 1)"
  assumes "ttt = Suc T' * (9 + 1891 * (H ^ 4 * (nlength (2 * n + 2 * p n + 3 + T'))\<^sup>2))"
  assumes "tps' = tps
    [j := (\<lfloor>2 * n + 2 * p n + 3 + T'\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>5),
     j + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_PHI345 1 j) tps ttt tps'"
  using transforms_tm_PHI345I[OF assms(1,2,3) H_ge_3, of 0 1, OF _ _ assms(4-12)] H_gr_2 assms(13-) PHI5_correct
  by fastforce

lemma PHI6_correct:
  "concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (xs ! i)) [0..<length xs]) = formula_n \<Phi>\<^sub>6"
proof -
  have "nll_Psi (H * (2 + 2 * i)) H (xs ! i) = formula_n (\<Psi> (\<gamma> (2 * i + 2)) (if x ! i then 3 else 2))"
    if "i < length xs" for i
  proof -
    have "\<gamma> (2 * i + 2) = [H * (2 + 2 * i)..<H * (2 + 2* i) + H]"
      using gamma_def by (simp add: mult.commute)
    then have "nll_Psi (H * (2 + 2 * i)) H (xs ! i) = formula_n (\<Psi> (\<gamma> (2 * i + 2)) (xs ! i))"
      using nll_Psi by simp
    moreover have "xs ! i = (if x ! i then 3 else 2)"
      using that by simp
    ultimately show ?thesis
      by simp
  qed
  then have "map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (xs ! i)) [0..<length xs] =
      map (\<lambda>i. formula_n (\<Psi> (\<gamma> (2 * i + 2)) (if x ! i then 3 else 2))) [0..<length xs]"
    by simp
  then have "concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (xs ! i)) [0..<length xs]) =
      concat (map (\<lambda>i. formula_n (\<Psi> (\<gamma> (2 * i + 2)) (if x ! i then 3 else 2))) [0..<length xs])"
    by metis
  also have "... = formula_n (concat (map (\<lambda>i. \<Psi> (\<gamma> (2 * i + 2)) (if x ! i then 3 else 2)) [0..<length xs]))"
    using concat_formula_n by simp
  also have "... = formula_n (concat (map (\<lambda>i. \<Psi> (\<gamma> (2 * i + 2)) (if x ! i then 3 else 2)) [0..<n]))"
    by simp
  also have "... = formula_n \<Phi>\<^sub>6"
    using PHI6_def by simp
  finally show ?thesis .
qed

lemma tm_PHI6 [transforms_intros]:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 7 < k"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! 0 = (\<lfloor>xs\<rfloor>, 1)"
    "tps ! j = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
    [0 := (\<lfloor>xs\<rfloor>, Suc n),
     j := (\<lfloor>2 + 2 * n\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>6)]"
  assumes "ttt = 133650 * H ^ 6 * n ^ 3 + 1"
  shows "transforms (tm_PHI6 j) tps ttt tps'"
  using transforms_tm_PHI6I[OF assms(1,2,3) H_ge_3 bs_xs assms(4-13) _] assms(14,15) PHI6_correct
  by simp

lemma PHI7_correct:
  assumes "idx = 2 * n + 4" and "numiter = p n"
  shows "concat (map (\<lambda>i. nll_Upsilon (idx + 2 * i) H) [0..<numiter]) = formula_n \<Phi>\<^sub>7"
proof -
  have "nll_Upsilon (idx + 2 * i) H = formula_n (\<Upsilon> (\<gamma> (2*n + 4 + 2 * i)))" for i
  proof -
    have "nll_Upsilon (idx + 2 * i) H = formula_n (\<Upsilon> [(idx + 2 * i)*H..<(idx + 2 * i)*H+H])"
      using nll_Upsilon[OF H_ge_3] by simp
    also have "... = formula_n (\<Upsilon> (\<gamma> (2 * n + 4 + 2 * i)))"
      using gamma_def assms(1) by (simp add: add.commute)
    finally show ?thesis .
  qed
  then have "concat (map (\<lambda>i. nll_Upsilon (idx + 2 * i) H) [0..<numiter]) =
      concat (map (\<lambda>i. formula_n (\<Upsilon> (\<gamma> (2*n + 4 + 2 * i)))) [0..<numiter])"
    by simp
  also have "... = formula_n (concat (map (\<lambda>i. \<Upsilon> (\<gamma> (2*n + 4 + 2 * i))) [0..<numiter]))"
    using concat_formula_n by simp
  also have "... = formula_n (concat (map (\<lambda>i. \<Upsilon> (\<gamma> (2*n + 4 + 2 * i))) [0..<p n]))"
    using assms(2) by simp
  also have "... = formula_n \<Phi>\<^sub>7"
    using PHI7_def by simp
  finally show ?thesis .
qed

lemma tm_PHI7 [transforms_intros]:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt numiter k idx :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 6 < k"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>p n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 1"
  assumes "tps' = tps
    [j := (\<lfloor>2 * n + 4 + 2 * p n\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ formula_n \<Phi>\<^sub>7)]"
  shows "transforms (tm_PHI7 j) tps ttt tps'"
  using transforms_tm_PHI7I[OF assms(1,2,3) H_ge_3 assms(4-12)] assms(13) PHI7_correct
  by simp

lemma tm_PHI8 [transforms_intros]:
  fixes tps tps' :: "tape list" and j :: tapeidx and ttt k idx :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 7 < k"
  assumes "idx = 1 + 3 * T' + m' "
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
      [1 := nlltape (nss @ formula_n \<Phi>\<^sub>8),
       j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
       j + 6 := (\<lfloor>formula_n \<Phi>\<^sub>8\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
  assumes "ttt = 18 + 1861 * H ^ 4 * (nlength (Suc (1 + 3 * T' + m')))\<^sup>2"
  shows "transforms (tm_PHI8 j) tps ttt tps'"
proof -
  let ?idx = "1 + 3 * T' + m' "
  have "m' * H + T' * 3 * H + H = ?idx * H"
    using m' add_mult_distrib by simp
  then have "\<zeta>\<^sub>1 T' = [?idx * H..<?idx * H + H]"
    using zeta1_def Z_def m' by (metis ab_semigroup_add_class.add_ac(1) mult.assoc mult_2)
  then have "nll_Psi (?idx * H) H 3 = formula_n \<Phi>\<^sub>8"
    using PHI8_def nll_Psi by simp
  then show ?thesis
    using transforms_tm_PHI8I[OF assms(1-3) H_ge_3 assms(5-13) _ assms(15)] assms(14) by simp
qed

end  (* context reduction_sat_x *)


section \<open>A Turing machine for initialization\<close>

text \<open>
As we have seen in the previous section, the Turing machines @{const tm_PHI0}
etc.\ expect some tapes to contain certain values that depend on the verifier TM
$M$. In this section we construct the TM @{term tm_PHI_init} that computes
theses values.

The TM expects the string $x$ on the input tape. Then it determines the length
$n$ of $x$ and stores it on tape~11. Then it computes the value $p(n)$ and
stores it on tape~15. Then it computes $m = 2n + 2p(n) + 2$ and stores it on
tape~16. It then writes $\mathbf{0}^m$ to tape~9 and runs @{const
tm_list_headpos}, which writes the sequences of head positions for the input and
work/output tape of the verifier TM $M$ to tapes~4 and~7, respectively.  The
length of these lists determines $T'$, which is written to tape~17. From this
and $m$ the TM computes $m'$ and writes it to tape~18. It then writes $H$, which
is hard-coded, to tape~19 and finally $N = H\cdot m'$ to tape~20.

We assume that the TM starts in a configuration where the input tape head and
the heads on tapes with index greater than 10 are positioned on cell number~1,
whereas all other tapes are on cell number~0 as usual.
The TM has no tape parameters, as all tapes are fixed to work with the final TM
later.

As with other TMs before, we will define and analyze the TM on the theory level
and then transfer the semantics to the locale @{locale reduction_sat_x}.
\<close>

definition tm_PHI_init :: "nat \<Rightarrow> machine \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> machine" where
  "tm_PHI_init G M p \<equiv>
     tm_right 9 ;;
     tm_length_input 11 ;;
     tm_polynomial p 11 ;;
     tm_copyn 15 16 ;;
     tm_add 11 16 ;;
     tm_incr 16 ;;
     tm_times2 16 ;;
     tm_copyn 16 17 ;;
     tm_write_replicate 2 17 9 ;;
     tm_left 9 ;;
     tm_list_headpos G M 2 ;;
     tm_count 4 17 4 ;;
     tm_decr 17 ;;
     tm_copyn 16 18 ;;
     tm_incr 18 ;;
     tm_add 17 18 ;;
     tm_setn 19 (max G (length M)) ;;
     tm_mult 18 19 20"

lemma tm_PHI_init_tm:
  fixes H k
  assumes "turing_machine 2 G M" and "k > 20" and "H \<ge> Suc (length M)" and "H \<ge> G"
  assumes "H \<ge> 5"
  shows "turing_machine k H (tm_PHI_init G M p)"
  unfolding tm_PHI_init_def
  using assms turing_machine_sequential_turing_machine tm_right_tm tm_length_input_tm tm_polynomial_tm
    tm_copyn_tm tm_add_tm tm_incr_tm tm_times2_tm tm_write_replicate_tm tm_left_tm tm_list_headpos_tm
    tm_count_tm tm_decr_tm tm_setn_tm tm_mult_tm
  by simp

locale turing_machine_PHI_init =
  fixes G :: nat and M :: machine and p :: "nat \<Rightarrow> nat"
begin

definition "tm3 \<equiv> tm_right 9"
definition "tm4 \<equiv> tm3 ;; tm_length_input 11"
definition "tm5 \<equiv> tm4 ;; tm_polynomial p 11"
definition "tm6 \<equiv> tm5 ;; tm_copyn 15 16"
definition "tm7 \<equiv> tm6 ;; tm_add 11 16"
definition "tm8 \<equiv> tm7 ;; tm_incr 16"
definition "tm9 \<equiv> tm8 ;; tm_times2 16"
definition "tm10 \<equiv> tm9 ;; tm_copyn 16 17"
definition "tm11 \<equiv> tm10 ;; tm_write_replicate 2 17 9"
definition "tm12 \<equiv> tm11 ;; tm_left 9"
definition "tm13 \<equiv> tm12 ;; tm_list_headpos G M 2"
definition "tm14 \<equiv> tm13 ;; tm_count 4 17 4"
definition "tm15 \<equiv> tm14 ;; tm_decr 17"
definition "tm16 \<equiv> tm15 ;; tm_copyn 16 18"
definition "tm17 \<equiv> tm16 ;; tm_incr 18"
definition "tm18 \<equiv> tm17 ;; tm_add 17 18"
definition "tm19 \<equiv> tm18 ;; tm_setn 19 (max G (length M))"
definition "tm20 \<equiv> tm19 ;; tm_mult 18 19 20"

lemma tm20_eq_tm_PHI_init: "tm20 = tm_PHI_init G M p"
  unfolding tm20_def tm19_def tm18_def tm17_def tm16_def tm15_def tm14_def tm13_def tm12_def tm11_def
  unfolding tm10_def tm9_def tm8_def tm7_def tm6_def tm5_def tm4_def tm3_def tm_PHI_init_def
  by simp

context
  fixes k H thalt :: nat and tps0 :: "tape list" and xs zs :: "symbol list"
  assumes poly_p: "polynomial p"
    and M_tm: "turing_machine 2 G M"
    and k: "k = length tps0" "20 < k"
    and H: "H = max G (length M)"
    and xs: "bit_symbols xs"
    and zs: "zs = 2 # 2 # replicate (2 * length xs + 2 * p (length xs)) 2"
  assumes thalt:
    "\<forall>t<thalt. fst (execute M (start_config 2 zs) t) < length M"
    "fst (execute M (start_config 2 zs) thalt) = length M"
  assumes tps0:
    "tps0 ! 0 = (\<lfloor>xs\<rfloor>, 1)"
    "\<And>i. 0 < i \<Longrightarrow> i \<le> 10 \<Longrightarrow> tps0 ! i = (\<lfloor>[]\<rfloor>, 0)"
    "\<And>i. 10 < i \<Longrightarrow> i < k \<Longrightarrow> tps0 ! i = (\<lfloor>[]\<rfloor>, 1)"
begin

lemma G: "G \<ge> 4"
  using M_tm turing_machine_def by simp

lemma H: "H \<ge> length M" "H \<ge> G"
  using H by simp_all

definition "tps3 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm3 [transforms_intros]: "transforms tm3 tps0 1 tps3"
  unfolding tm3_def by (tform tps: tps3_def tps0 k)

abbreviation "n \<equiv> length xs"

definition "tps4 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 5 + 11 * (length xs)\<^sup>2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def tps4_def tps0 k time: assms)
  show "proper_symbols xs"
    using xs by auto
  show "tps3 ! 11 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using canrepr_0 tps3_def tps0 k by simp
qed

definition "tps5 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 5 + 11 * (length xs)\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength (length xs))\<^sup>2)"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform tps: canrepr_0 tps4_def tps5_def tps0 k poly_p time: assms)

definition "tps6 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>p n\<rfloor>\<^sub>N, 1)]"

lemma tm6 [transforms_intros]:
  assumes "ttt = 19 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) + 3 * nlength (p n)"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: tps5_def tps6_def tps0 k)
  show "tps5 ! 16 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using canrepr_0 k tps0 tps5_def by simp
  show "ttt = 5 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
      (14 + 3 * (nlength (p n) + nlength 0))"
    using assms by simp
qed

definition "tps7 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>n + p n\<rfloor>\<^sub>N, 1)]"

lemma tm7 [transforms_intros]:
  assumes "ttt = 29 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n))"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform tps: tps6_def tps7_def tps0 k assms)

definition "tps8 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>Suc (n + p n)\<rfloor>\<^sub>N, 1)]"

lemma tm8 [transforms_intros]:
  assumes "ttt = 34 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n)"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def by (tform tps: tps7_def tps8_def tps0 k assms)

definition "tps9 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1)]"

lemma tm9 [transforms_intros]:
  assumes "ttt = 39 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n))"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def by (tform tps: tps8_def tps9_def tps0 k assms)

definition "tps10 \<equiv> tps0
  [9 := (\<lfloor>[]\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1)]"

lemma tm10 [transforms_intros]:
  assumes "ttt = 53 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 3 * nlength (Suc (Suc (2 * n + 2 * p n)))"
  shows "transforms tm10 tps0 ttt tps10"
  unfolding tm10_def
proof (tform tps: tps9_def tps10_def tps0 k)
  show "tps9 ! 17 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps9_def canrepr_0 tps0 k by simp
  show "ttt = 39 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
      3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) +
      2 * nlength (n + p n) + 2 * nlength (Suc (n + p n)) +
      (14 + 3 * (nlength (Suc (Suc (2 * n + 2 * p n))) + nlength 0))"
    using assms by simp
qed

definition "tps11 \<equiv> tps0
  [9 := (\<lfloor>zs\<rfloor>, 1),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm11 [transforms_intros]:
  assumes "ttt = 57 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 3 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    Suc (Suc (2 * n + 2 * p n)) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n))))"
  shows "transforms tm11 tps0 ttt tps11"
  unfolding tm11_def
proof (tform tps: tps10_def tps11_def tps0 k time: assms)
  show "tps11 = tps10
    [17 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     9 := (\<lfloor>replicate (Suc (Suc (2 * n + 2 * p n))) 2\<rfloor>, 1)]"
    unfolding tps11_def tps10_def using zs by (simp add: list_update_swap[of _ 9])
qed

definition "tps12 \<equiv> tps0
  [9 := (\<lfloor>zs\<rfloor>, 0),
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm12 [transforms_intros]:
  assumes "ttt = 82 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n))))"
  shows "transforms tm12 tps0 ttt tps12"
  unfolding tm12_def
proof (tform tps: tps11_def tps12_def tps0 k time: assms)
  have "tps11 ! 9 |-| 1 = (\<lfloor>zs\<rfloor>, 0)"
    using tps11_def k by simp
  then show "tps12 = tps11[9 := tps11 ! 9 |-| 1]"
    unfolding tps12_def tps11_def by (simp add: list_update_swap[of _ 9])
qed

abbreviation exc :: "nat \<Rightarrow> config" where
  "exc t \<equiv> execute M (start_config 2 zs) t"

definition "tps13 \<equiv> tps0
  [9 := exc thalt <!> 0,
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   3 := (\<lfloor>exc thalt <#> 0\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   6 := (\<lfloor>exc thalt <#> 1\<rfloor>\<^sub>N, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   10 := exc thalt <!> 1]"

lemma tm13 [transforms_intros]:
  assumes "ttt = 82 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt)"
  shows "transforms tm13 tps0 ttt tps13"
  unfolding tm13_def
proof (tform)
  show "turing_machine 2 G M"
    using M_tm .
  show "2 + 9 \<le> length tps12"
    using tps12_def k by simp
  show "\<forall>t<thalt. fst (execute M (start_config 2 zs) t) < length M"
      "fst (execute M (start_config 2 zs) thalt) = length M"
    using thalt .
  show "symbols_lt G zs"
  proof -
    have "zs = replicate (2 * n + 2 * p n + 2) 2"
      using zs by simp
    then have "\<forall>i<length zs. zs ! i = 2"
      using nth_replicate by (metis length_replicate)
    then show ?thesis
      using G by simp
  qed
  show "tps13 = tps12
    [2 + 1 := (\<lfloor>snd (exc thalt) :#: 0\<rfloor>\<^sub>N, 1),
     2 + 2 := (\<lfloor>map (\<lambda>t. snd (exc t) :#: 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
     2 + 4 := (\<lfloor>snd (exc thalt) :#: 1\<rfloor>\<^sub>N, 1),
     2 + 5 := (\<lfloor>map (\<lambda>t. snd (exc t) :#: 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
     2 + 7 := exc thalt <!> 0, 2 + 8 := exc thalt <!> 1]"
    unfolding tps13_def tps12_def by (simp add: list_update_swap[of _ 9])
  show "tps12 ! 2 = \<lceil>\<triangleright>\<rceil>"
    using tps12_def tps0 onesie_1 by simp
  show "tps12 ! (2 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 0)"
    using tps12_def tps0 canrepr_0 by simp
  show "tps12 ! (2 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 0)"
    using tps12_def tps0 nlcontents_Nil by simp
  show "tps12 ! (2 + 3) = \<lceil>\<triangleright>\<rceil>"
    using tps12_def tps0 onesie_1 by simp
  show "tps12 ! (2 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 0)"
    using tps12_def tps0 canrepr_0 by simp
  show "tps12 ! (2 + 5) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 0)"
    using tps12_def tps0 nlcontents_Nil by simp
  show "tps12 ! (2 + 6) = \<lceil>\<triangleright>\<rceil>"
    using tps12_def tps0 onesie_1 by simp
  show "tps12 ! (2 + 7) = (\<lfloor>zs\<rfloor>, 0)"
    using tps12_def k tps0 by simp
  show "tps12 ! (2 + 8) = (\<lfloor>[]\<rfloor>, 0)"
    using tps12_def tps0 by simp
  show "ttt = 82 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
      3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
      2 * nlength (Suc (n + p n)) + 7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
      (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
      27 * Suc thalt * (9 + 2 * nlength thalt)"
    using assms by simp
qed

definition "tpsA \<equiv> tps0
  [9 := exc thalt <!> 0,
   3 := (\<lfloor>exc thalt <#> 0\<rfloor>\<^sub>N, 1),
   6 := (\<lfloor>exc thalt <#> 1\<rfloor>\<^sub>N, 1),
   10 := exc thalt <!> 1]"

definition "tps14 \<equiv> tps0
  [9 := exc thalt <!> 0,
   11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>Suc thalt\<rfloor>\<^sub>N, 1),
   3 := (\<lfloor>exc thalt <#> 0\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   6 := (\<lfloor>exc thalt <#> 1\<rfloor>\<^sub>N, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   10 := exc thalt <!> 1]"

lemma tm14:
  assumes "ttt = 87 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2"
  shows "transforms tm14 tps0 ttt tps14"
  unfolding tm14_def
proof (tform)
  show "4 < length tps13" "17 < length tps13"
    using tps13_def k by (simp_all only: length_list_update)
  show "tps13 ! 4 = (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps13_def k by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps13 ! 17 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps13_def k by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps14 = tps13
      [17 := (\<lfloor>length (map (\<lambda>t. snd (exc t) :#: 0) [0..<Suc thalt])\<rfloor>\<^sub>N, 1)]"
    unfolding tps14_def tps13_def by (simp add: list_update_swap[of 17])
  show "ttt = 82 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
      3 * nlength (p n) +
      3 * max (nlength n) (nlength (p n)) +
      2 * nlength (n + p n) +
      2 * nlength (Suc (n + p n)) +
      7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
      (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
      (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
      (14 * (nllength (map (\<lambda>t. snd (exc t) :#: 0) [0..<Suc thalt]))\<^sup>2 + 5)"
    using assms by simp
qed

definition "tps14' \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>Suc thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tps14': "tps14' = tps14"
  unfolding tps14'_def tps14_def tpsA_def by (simp add: list_update_swap)

lemma len_tpsA: "length tpsA = k"
  using tpsA_def k by simp

lemma tm14' [transforms_intros]:
  assumes "ttt = 87 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2"
  shows "transforms tm14 tps0 ttt tps14'"
  using tm14 tps14' assms by simp

definition "tps15 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm15 [transforms_intros]:
  assumes "ttt = 95 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt)"
  shows "transforms tm15 tps0 ttt tps15"
  unfolding tm15_def
proof (tform tps: tps14'_def len_tpsA k time: assms)
  show "tps15 = tps14'[17 := (\<lfloor>Suc thalt - 1\<rfloor>\<^sub>N, 1)]"
    unfolding tps15_def tps14'_def by (simp add: list_update_swap)
qed

definition "tps16 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1)]"

lemma tm16 [transforms_intros]:
  assumes "ttt = 109 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt)"
  shows "transforms tm16 tps0 ttt tps16"
  unfolding tm16_def
proof (tform tps: tps15_def tps16_def k len_tpsA)
  have "tps15 ! 18 = tpsA ! 18"
    using tps15_def by simp
  also have "... = tps0 ! 18"
    using tpsA_def by simp
  also have "... = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 canrepr_0 k by simp
  finally show "tps15 ! 18 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" .
  show "ttt = 95 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
      3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) +
      2 * nlength (n + p n) + 2 * nlength (Suc (n + p n)) +
      7 * nlength (Suc (Suc (2 * n + 2 * p n))) +
      (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) + (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
      14 * (nllength
        (map (\<lambda>t. snd (exc t) :#: 0) [0..<thalt] @ [snd (exc thalt) :#: 0]))\<^sup>2 +
      2 * nlength (Suc thalt) + (14 + 3 * (nlength (Suc (Suc (2 * n + 2 * p n))) + nlength 0))"
    using assms by simp
qed

definition "tps17 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1)]"

lemma tm17 [transforms_intros]:
  assumes "ttt = 114 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))"
  shows "transforms tm17 tps0 ttt tps17"
  unfolding tm17_def by (tform tps: tps16_def tps17_def k len_tpsA time: assms)

definition "tps18 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>thalt + Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1)]"

lemma tm18 [transforms_intros]:
  assumes "ttt = 124 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n)))))"
  shows "transforms tm18 tps0 ttt tps18"
  unfolding tm18_def by (tform tps: tps17_def tps18_def k len_tpsA time: assms)

definition "tps19 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>thalt + Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>max G (length M)\<rfloor>\<^sub>N, 1)]"

lemma tm19 [transforms_intros]:
  assumes "ttt = 134 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) +
    2 * nlength (max G (length M))"
  shows "transforms tm19 tps0 ttt tps19"
  unfolding tm19_def
proof (tform tps: assms nlength_0)
  have "tps18 ! 19 = tpsA ! 19"
    using tps18_def by simp
  also have "... = tps0 ! 19"
    using tpsA_def by simp
  also have "... = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 canrepr_0 k by simp
  finally show "tps18 ! 19 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" .
  show "19 < length tps18"
    using tps18_def len_tpsA k by simp
  show "tps19 = tps18[19 := (\<lfloor>max G (length M)\<rfloor>\<^sub>N, 1)]"
    using tps19_def tps18_def len_tpsA k by presburger
qed

definition "tps20 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>thalt + Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>max G (length M)\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>(thalt + Suc (2 * Suc (n + p n))) * max G (length M)\<rfloor>\<^sub>N, 1)]"

lemma tm20:
  assumes "ttt = 138 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) +
    2 * nlength (max G (length M)) +
    26 * (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M))) *
     (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M)))"
  shows "transforms tm20 tps0 ttt tps20"
  unfolding tm20_def
proof (tform time: assms)
  have "tps19 ! 20 = tpsA ! 20"
    using tps19_def by simp
  also have "... = tps0 ! 20"
    using tpsA_def by simp
  also have "... = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 canrepr_0 k by simp
  finally show "tps19 ! 20 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" .
  show "tps20 = tps19
      [20 := (\<lfloor>Suc (Suc (Suc (thalt + (2 * n + 2 * p n)))) * max G (length M)\<rfloor>\<^sub>N, 1)]"
    unfolding tps20_def tps19_def by (simp add: list_update_swap)
  show "18 < length tps19" "19 < length tps19" "20 < length tps19"
    using tps19_def k len_tpsA by (simp_all only: length_list_update)
  have "tps19 ! 18 = (\<lfloor>thalt + Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1)"
    using tps19_def tpsA_def len_tpsA k tps0 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps19 ! 18 = (\<lfloor>Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))\<rfloor>\<^sub>N, 1)"
    by simp
  show "tps19 ! 19 = (\<lfloor>max G (length M)\<rfloor>\<^sub>N, 1)"
    using tps19_def tpsA_def len_tpsA k tps0 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
qed

lemma tm20' [transforms_intros]:
  assumes "ttt = (2 * d_polynomial p + 826) * (max G (length M) + thalt + Suc (Suc (Suc (2 * n + 2 * p n)))) ^ 4"
  shows "transforms tm20 tps0 ttt tps20"
proof -
  let ?ttt = "138 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) +
    3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) +
    (27 + 27 * thalt) * (9 + 2 * nlength thalt) +
    14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 +
    2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) +
    2 * nlength (max G (length M)) +
    26 * (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M))) *
     (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M)))"
  let ?a = "3 * nlength (p n) + 3 * max (nlength n) (nlength (p n)) + 2 * nlength (n + p n) +
    2 * nlength (Suc (n + p n)) + 10 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) + (27 + 27 * thalt) * (9 + 2 * nlength thalt)"
  let ?b = "2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
    3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) +
    2 * nlength (max G (length M)) +
    26 * (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M))) *
     (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M)))"
  let ?m = "max G (length M) + thalt + Suc (Suc (Suc (2 * n + 2 * p n)))"
  define m where "m = max G (length M) + thalt + Suc (Suc (Suc (2 * n + 2 * p n)))"
  note m_def [simp]
  have **: "y \<le> y * m" for y
    by simp
  have *: "nlength y \<le> m" if "y \<le> m" for y
    using nlength_mono[OF that] nlength_mono by (meson dual_order.trans nlength_le_n)
  have 1: "nlength (p n) \<le> m"
    using * by simp
  have 2: "max (nlength n) (nlength (p n)) \<le> m"
    using * by simp
  have 3: "nlength (n + p n) \<le> m"
    using * by simp
  have 4: "nlength (Suc (n + p n)) \<le> m"
    using * by simp
  have 5: "nlength (Suc (Suc (2 * n + 2 * p n))) \<le> m"
    using * by simp
  have 6: "nlength n \<le> m"
    using * by simp
  have 7: "2 * n + 2 * p n \<le> m"
    by simp
  have 8: "thalt \<le> m" "nlength thalt \<le> m" "nlength (Suc thalt) \<le> m"
    using * by simp_all
  have 10: "max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) \<le> m"
    using * by simp
  have 11: "nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) \<le> m"
    using * by simp
  have 12: "nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M)) \<le> m"
    using * nlength_le_n by (smt (verit) ab_semigroup_add_class.add_ac(1) add.commute add_Suc_right add_le_mono m_def)
  have 13: "nlength (max G (length M)) \<le> m"
    using 12 by simp
  have 14: "Suc (nlength thalt) \<le> m"
  proof -
    have "nlength thalt \<le> nlength m"
      using nlength_mono by simp
    moreover have "m \<ge> 3"
      by simp
    ultimately have "nlength thalt < m"
      using nlength_less_n dual_order.strict_trans2 by blast
    then show ?thesis
      by simp
  qed
  have 15: "Suc thalt \<le> m"
    by simp

  have "?a \<le> 20 * m +
      (2 * n + 2 * p n) * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) + (27 + 27 * thalt) * (9 + 2 * nlength thalt)"
    using 1 2 3 4 5 by linarith
  also have "... \<le> 20 * m + m * (12 + 2 * nlength (Suc (Suc (2 * n + 2 * p n)))) + (27 + 27 * thalt) * (9 + 2 * nlength thalt)"
    using 7 by (metis add.commute add_mono_thms_linordered_semiring(2) mult_Suc_right mult_le_cancel2)
  also have "... \<le> 20 * m + m * (12 + 2 * m) + (27 + 27 * thalt) * (9 + 2 * nlength thalt)"
    using 5 by (meson add_left_mono add_mono_thms_linordered_semiring(3) mult_le_mono2)
  also have "... \<le> 20 * m + m * (12 + 2 * m) + (27 + 27 * m) * (9 + 2 * m)"
    using 8 add_le_mono le_refl mult_le_mono by presburger
  also have "... \<le> 20 * m + m * (12 * m + 2 * m) + (27 * m + 27 * m) * (9 + 2 * m)"
    using ** by (meson add_le_mono add_mono_thms_linordered_semiring(2) add_mono_thms_linordered_semiring(3) mult_le_mono1 mult_le_mono2)
  also have "... \<le> 20 * m + m * (12 * m + 2 * m) + (27 * m + 27 * m) * (9 * m + 2 * m)"
    using ** by simp
  also have "... = 20 * m + m * 14 * m + 54 * m * 11 * m"
    by algebra
  also have "... = 20 * m + 14 * m ^ 2 + 594 * m ^ 2"
    by algebra
  also have "... = 20 * m + 608 * m ^ 2"
    by simp
  also have "... \<le> 20 * m ^ 2 + 608 * m ^ 2"
    using linear_le_pow by (meson add_le_mono1 mult_le_mono2 zero_less_numeral)
  also have "... = 628 * m ^ 2"
    by simp
  finally have part1: "?a \<le> 628 * m ^ 2" .

  have "nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]) \<le> Suc (nlength thalt) * Suc thalt"
  proof -
    have "exc t <#> 0 \<le> thalt" if "t \<le> thalt" for t
      using that M_tm head_pos_le_halting_time thalt(2) zero_less_numeral by blast
    then have "y \<le> thalt" if "y \<in> set (map (\<lambda>t. exc t <#> 0) [0..<Suc thalt])" for y
      using that by force
    then have "nllength (map (\<lambda>t. exc t <#> 0) [0..<Suc thalt]) \<le> Suc (nlength thalt) * Suc thalt"
        (is "nllength ?ns \<le> _")
      using nllength_le_len_mult_max[of ?ns thalt] by simp
    then show ?thesis
      by simp
  qed
  then have part2: "nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]) \<le> m * m"
    using 14 15 by (meson le_trans mult_le_mono)

  have "?b = 2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
      3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) + 2 * nlength (max G (length M)) +
      26 * (nlength (Suc (Suc (Suc (thalt + (2 * n + 2 * p n))))) + nlength (max G (length M))) ^ 2"
    by algebra
  also have "... \<le> 2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
      3 * max (nlength thalt) (nlength (Suc (Suc (Suc (2 * n + 2 * p n))))) + 2 * nlength (max G (length M)) +
      26 * m ^ 2"
    using 12 by simp
  also have "... \<le> 2 * nlength (Suc thalt) + 2 * nlength (Suc (Suc (2 * n + 2 * p n))) +
      3 * m + 2 * nlength (max G (length M)) + 26 * m ^ 2"
    using 10 by linarith
  also have "... \<le> 2 * m + 2 * m + 3 * m + 2 * m + 26 * m ^ 2"
    using 13 8 5 by simp
  also have "... = 9 * m + 26 * m ^ 2"
    by simp
  also have "... \<le> 9 * m ^ 2 + 26 * m ^ 2"
    using linear_le_pow by (meson add_le_mono1 mult_le_mono2 zero_less_numeral)
  also have "... = 35 * m ^ 2"
    by simp
  finally have part3: "?b \<le> 35 * m ^ 2" .

  have "?ttt = 138 + 11 * n\<^sup>2 + (d_polynomial p + d_polynomial p * (nlength n)\<^sup>2) + ?a +
      14 * (nllength (map (\<lambda>t. exc t <#> 0) [0..<thalt] @ [exc thalt <#> 0]))\<^sup>2 + ?b"
    by simp
  also have "... \<le> 138 + 11 * n\<^sup>2 + d_polynomial p + d_polynomial p * (nlength n)\<^sup>2 + ?a + 14 * (m * m)\<^sup>2 + ?b"
    using part2 by simp
  also have "... \<le> 138 + 11 * n\<^sup>2 + d_polynomial p + d_polynomial p * (nlength n)\<^sup>2 + ?a + 14 * (m * m)\<^sup>2 + 35 * m ^ 2"
    using part3 by linarith
  also have "... \<le> 138 + 11 * n\<^sup>2 + d_polynomial p + d_polynomial p * (nlength n)\<^sup>2 + 628 * m ^ 2 + 14 * (m * m)\<^sup>2 + 35 * m ^ 2"
    using part1 by linarith
  also have "... = 138 + 11 * n\<^sup>2 + d_polynomial p + d_polynomial p * (nlength n)\<^sup>2 + 663 * m ^ 2 + 14 * m ^ 4"
    by algebra
  also have "... \<le> 138 + 11 * m ^ 2 + d_polynomial p + d_polynomial p * (nlength n)\<^sup>2 + 663 * m ^ 2 + 14 * m ^ 4"
    by simp
  also have "... \<le> 138 + 11 * m ^ 2 + d_polynomial p + d_polynomial p * m ^ 2 + 663 * m ^ 2 + 14 * m ^ 4"
    using 6 by simp
  also have "... = 138 + d_polynomial p + d_polynomial p * m ^ 2 + 674 * m ^ 2 + 14 * m ^ 4"
    by simp
  also have "... \<le> 138 + d_polynomial p + d_polynomial p * m ^ 4 + 674 * m ^ 2 + 14 * m ^ 4"
    using pow_mono'[of 2 4] by simp
  also have "... \<le> 138 + d_polynomial p + d_polynomial p * m ^ 4 + 674 * m ^ 4 + 14 * m ^ 4"
    using pow_mono'[of 2 4] by simp
  also have "... = 138 + d_polynomial p + d_polynomial p * m ^ 4 + 688 * m ^ 4"
    by simp
  also have "... \<le> 138 * m + d_polynomial p + d_polynomial p * m ^ 4 + 688 * m ^ 4"
    using ** by simp
  also have "... \<le> 138 * m ^ 4 + d_polynomial p + d_polynomial p * m ^ 4 + 688 * m ^ 4"
    using linear_le_pow[of 4 m] by simp
  also have "... = d_polynomial p + d_polynomial p * m ^ 4 + 826 * m ^ 4"
    by simp
  also have "... \<le> d_polynomial p * m + d_polynomial p * m ^ 4 + 826 * m ^ 4"
    using ** by simp
  also have "... \<le> d_polynomial p * m ^ 4 + d_polynomial p * m ^ 4 + 826 * m ^ 4"
    using linear_le_pow[of 4 m] by (simp del: m_def)
  also have "... = 2 * d_polynomial p * m ^ 4 + 826 * m ^ 4"
    by simp
  also have "... = (2 * d_polynomial p + 826) * m ^ 4"
    by algebra
  finally have "?ttt \<le> (2 * d_polynomial p + 826) * m ^ 4" .
  then have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm20 transforms_monotone by fast
qed

end  (* context tps0 *)

end  (* locale turing_machine_PHI_init *)

lemma transforms_tm_PHI_initI:
  fixes G :: nat and M :: machine and p :: "nat \<Rightarrow> nat"
  fixes k H thalt :: nat and tps tps' :: "tape list" and xs zs :: "symbol list"
  assumes poly_p: "polynomial p"
    and M_tm: "turing_machine 2 G M"
    and k: "k = length tps" "20 < k"
    and H: "H = max G (length M)"
    and xs: "bit_symbols xs"
    and zs: "zs = 2 # 2 # replicate (2 * length xs + 2 * p (length xs)) 2"
  assumes thalt:
    "\<forall>t<thalt. fst (execute M (start_config 2 zs) t) < length M"
    "fst (execute M (start_config 2 zs) thalt) = length M"
  assumes tps0:
    "tps ! 0 = (\<lfloor>xs\<rfloor>, 1)"
    "\<And>i. 0 < i \<Longrightarrow> i \<le> 10 \<Longrightarrow> tps ! i = (\<lfloor>[]\<rfloor>, 0)"
    "\<And>i. 10 < i \<Longrightarrow> i < k \<Longrightarrow> tps ! i = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = (2 * d_polynomial p + 826) * (max G (length M) + thalt + Suc (Suc (Suc (2 * (length xs) + 2 * p (length xs))))) ^ 4"
  assumes "tps' = tps
      [9 := execute M (start_config 2 zs) thalt <!> 0,
       3 := (\<lfloor>execute M (start_config 2 zs) thalt <#> 0\<rfloor>\<^sub>N, 1),
       6 := (\<lfloor>execute M (start_config 2 zs) thalt <#> 1\<rfloor>\<^sub>N, 1),
       10 := execute M (start_config 2 zs) thalt <!> 1,
       11 := (\<lfloor>length xs\<rfloor>\<^sub>N, 1),
       15 := (\<lfloor>p (length xs)\<rfloor>\<^sub>N, 1),
       16 := (\<lfloor>2 * Suc ((length xs) + p (length xs))\<rfloor>\<^sub>N, 1),
       17 := (\<lfloor>thalt\<rfloor>\<^sub>N, 1),
       4 := (\<lfloor>map (\<lambda>t. execute M (start_config 2 zs) t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
       7 := (\<lfloor>map (\<lambda>t. execute M (start_config 2 zs) t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
       18 := (\<lfloor>thalt + Suc (2 * Suc ((length xs) + p (length xs)))\<rfloor>\<^sub>N, 1),
       19 := (\<lfloor>max G (length M)\<rfloor>\<^sub>N, 1),
       20 := (\<lfloor>(thalt + Suc (2 * Suc ((length xs) + p (length xs)))) * max G (length M)\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_PHI_init G M p) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI_init G M p .
  note ctx = poly_p M_tm k H xs zs thalt tps0
  have "transforms loc.tm20 tps ttt (loc.tps20 thalt tps xs zs)"
    using assms loc.tm20'[OF ctx] loc.tps20_def[OF ctx] loc.tpsA_def[OF ctx]
    by blast
  then have "transforms (tm_PHI_init G M p) tps ttt (loc.tps20 thalt tps xs zs)"
    using loc.tm20_eq_tm_PHI_init by simp
  moreover have "loc.tps20 thalt tps xs zs = tps'"
    using assms loc.tps20_def[OF ctx] loc.tpsA_def[OF ctx] by presburger
  ultimately show ?thesis
    by simp
qed

text \<open>
Next we transfer the semantics of @{const tm_PHI_init} to the locale
@{locale reduction_sat_x}.
\<close>

lemma (in reduction_sat_x) tm_PHI_init [transforms_intros]:
  fixes k :: nat and tps tps' :: "tape list"
  assumes "k = length tps" and "20 < k"
  assumes
      "tps ! 0 = (\<lfloor>xs\<rfloor>, 1)"
      "\<And>i. 0 < i \<Longrightarrow> i \<le> 10 \<Longrightarrow> tps ! i = (\<lfloor>[]\<rfloor>, 0)"
      "\<And>i. 10 < i \<Longrightarrow> i < k \<Longrightarrow> tps ! i = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = (2 * d_polynomial p + 826) * (H + T' + Suc (Suc (Suc (2 * n + 2 * p n)))) ^ 4"
  assumes "tps' = tps
      [9 := exc (zeros m) T' <!> 0,
       3 := (\<lfloor>exc (zeros m) T' <#> 0\<rfloor>\<^sub>N, 1),
       6 := (\<lfloor>exc (zeros m) T' <#> 1\<rfloor>\<^sub>N, 1),
       10 := exc (zeros m) T' <!> 1,
       11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
       15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
       16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
       17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
       4 := (\<lfloor>map (\<lambda>t. exc (zeros m) t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
       7 := (\<lfloor>map (\<lambda>t. exc (zeros m) t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
       18 := (\<lfloor>T' + Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1),
       19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
       20 := (\<lfloor>(T' + Suc (2 * Suc (n + p n))) * H\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_PHI_init G M p) tps ttt tps'"
proof -
  have nx: "n = length xs"
    by simp
  then have zeros_zs: "zeros m = 2 # 2 # replicate (2 * length xs + 2 * p (length xs)) 2"
    using zeros m_def by simp
  then have thalt:
      "\<forall>t<T' . fst (exc (zeros m) t) < length M"
      "fst (exc (zeros m) T') = length M"
    using less_TT TT T'_def by metis+
  have H: "H = max G (length M)"
    using H_def by simp
  have ttt: "ttt = (2 * d_polynomial p + 826) *
      (max G (length M) + T' + Suc (Suc (Suc (2 * (length xs) + 2 * p (length xs))))) ^ 4"
    using H nx assms(6) by simp
  have tps': "tps' = tps
      [9 := exc (zeros m) T' <!> 0,
      3 := (\<lfloor>snd (exc (zeros m) T') :#: 0\<rfloor>\<^sub>N, 1),
      6 := (\<lfloor>snd (exc (zeros m) T') :#: 1\<rfloor>\<^sub>N, 1),
      10 := exc (zeros m) T' <!> 1, 11 := (\<lfloor>length xs\<rfloor>\<^sub>N, 1),
      15 := (\<lfloor>p (length xs)\<rfloor>\<^sub>N, 1),
      16 := (\<lfloor>2 * Suc (length xs + p (length xs))\<rfloor>\<^sub>N, 1),
      17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
      4 := (\<lfloor>map (\<lambda>t. snd (exc (zeros m) t) :#: 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
      7 := (\<lfloor>map (\<lambda>t. snd (exc (zeros m) t) :#: 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
      18 := (\<lfloor>T' + Suc (2 * Suc (length xs + p (length xs)))\<rfloor>\<^sub>N, 1),
      19 := (\<lfloor>max G (length M)\<rfloor>\<^sub>N, 1),
      20 := (\<lfloor>(T' + Suc (2 * Suc (length xs + p (length xs)))) * max G (length M)\<rfloor>\<^sub>N, 1)]"
    using H nx assms(7) by presburger
  show "transforms (tm_PHI_init G M p) tps ttt tps'"
    using transforms_tm_PHI_initI[OF p tm_M assms(1,2) H bs_xs zeros_zs thalt assms(3,4,5) ttt tps'] .
qed


section \<open>The actual Turing machine computing the reduction\<close>

text \<open>
In this section we put everything together to build a Turing machine that given
a string $x$ outputs the CNF formula $\Phi$ defined in Chapter~\ref{s:Reducing}.
In principle this is just a sequence of the TMs @{const tm_PHI_init}, @{const
tm_PHI0}, $\dots$, @{const tm_PHI9}, where @{const tm_PHI345} occurs once for
each of the formulas $\Phi_3$, $\Phi_4$, and $\Phi_5$. All these TMs are linked
by TMs that copy values prepared by @{const tm_PHI_init} to the tapes where the
following TM expects them. Also as the very first step the tape heads on tapes
$0$ and $11$ and beyond must be moved one cell to the right to meet @{const
tm_PHI_init}'s expectations.

The TM will have 110 tapes because we just allocate another batch of tapes for
every TM computing a $\Phi_i$, rather than cleaning up and reusing tapes.
\<close>

text \<open>
The Turing machine for computing $\Phi$ is to be defined in the locale @{locale
reduction_sat}. We save the space to write the TM in closed form.
\<close>

context reduction_sat
begin

definition "tm1 \<equiv> tm_right_many {i. i < 1 \<or> 10 < i}"
definition "tm2 \<equiv> tm1 ;; tm_PHI_init G M p"

definition "tm3 \<equiv> tm2 ;; tm_copyn 18 21"
definition "tm4 \<equiv> tm3 ;; tm_copyn 19 22"
definition "tm5 \<equiv> tm4 ;; tm_right 1"
definition "tm6 \<equiv> tm5 ;; tm_PHI0 21"

definition "tm7 \<equiv> tm6 ;; tm_setn 29 H"
definition "tm8 \<equiv> tm7 ;; tm_PHI1 28"

definition "tm9 \<equiv> tm8 ;; tm_copyn 11 35"
definition "tm10 \<equiv> tm9 ;; tm_setn 36 H"
definition "tm11 \<equiv> tm10 ;; tm_PHI2 35"

definition "tm12 \<equiv> tm11 ;; tm_setn 42 1"
definition "tm13 \<equiv> tm12 ;; tm_setn 43 H"
definition "tm14 \<equiv> tm13 ;; tm_setn 44 2"
definition "tm15 \<equiv> tm14 ;; tm_copyn 11 50"
definition "tm16 \<equiv> tm15 ;; tm_times2incr 50"
definition "tm17 \<equiv> tm16 ;; tm_PHI345 2 42"

definition "tm18 \<equiv> tm17 ;; tm_setn 52 H"
definition "tm19 \<equiv> tm18 ;; tm_setn 53 2"
definition "tm20 \<equiv> tm19 ;; tm_copyn 11 51"
definition "tm21 \<equiv> tm20 ;; tm_times2 51"
definition "tm22 \<equiv> tm21 ;; tm_plus_const 3 51"
definition "tm23 \<equiv> tm22 ;; tm_copyn 16 59"
definition "tm24 \<equiv> tm23 ;; tm_incr 59"
definition "tm25 \<equiv> tm24 ;; tm_PHI345 2 51"

definition "tm26 \<equiv> tm25 ;; tm_setn 61 H"
definition "tm27 \<equiv> tm26 ;; tm_copyn 16 60"
definition "tm28 \<equiv> tm27 ;; tm_incr 60"
definition "tm29 \<equiv> tm28 ;; tm_copyn 60 68"
definition "tm30 \<equiv> tm29 ;; tm_add 17 68"
definition "tm31 \<equiv> tm30 ;; tm_PHI345 1 60"

definition "tm32 \<equiv> tm31 ;; tm_setn 69 2"
definition "tm33 \<equiv> tm32 ;; tm_setn 70 H"
definition "tm34 \<equiv> tm33 ;; tm_PHI6 69"

definition "tm35 \<equiv> tm34 ;; tm_copyn 11 77"
definition "tm36 \<equiv> tm35 ;; tm_times2 77"
definition "tm37 \<equiv> tm36 ;; tm_plus_const 4 77"
definition "tm38 \<equiv> tm37 ;; tm_setn 78 H"
definition "tm39 \<equiv> tm38 ;; tm_copyn 15 83"
definition "tm40 \<equiv> tm39 ;; tm_PHI7 77"

definition "tm41 \<equiv> tm40 ;; tm_copyn 18 84"
definition "tm42 \<equiv> tm41 ;; tm_add 17 84"
definition "tm43 \<equiv> tm42 ;; tm_add 17 84"
definition "tm44 \<equiv> tm43 ;; tm_add 17 84"
definition "tm45 \<equiv> tm44 ;; tm_incr 84"
definition "tm46 \<equiv> tm45 ;; tm_setn 85 H"
definition "tm47 \<equiv> tm46 ;; tm_PHI8 84"

definition "tm48 \<equiv> tm47 ;; tm_copyn 20 91"
definition "tm49 \<equiv> tm48 ;; tm_setn 92 H"
definition "tm50 \<equiv> tm49 ;; tm_setn 93 Z"
definition "tm51 \<equiv> tm50 ;; tm_copyn 17 94"
definition "tm52 \<equiv> tm51 ;; tm_set 95 (numlistlist (formula_n \<psi>))"
definition "tm53 \<equiv> tm52 ;; tm_set 96 (numlistlist (formula_n \<psi>'))"
definition "tm54 \<equiv> tm53 ;; tm_setn 97 1"
definition "tm55 \<equiv> tm54 ;; tm_PHI9 4 7 91"

definition "tm56 \<equiv> tm55 ;; tm_cr 1"
definition "tm57 \<equiv> tm56 ;; tm_cp_until 1 109 {0}"
definition "tm58 \<equiv> tm57 ;; tm_erase_cr 1"
definition "tm59 \<equiv> tm58 ;; tm_cr 109"
definition "tm60 \<equiv> tm59 ;; tm_binencode 109 1"

definition H' :: nat where
  "H' \<equiv> Suc (Suc H)"

lemma H_gr_3: "H > 3"
  using H_def tm_M turing_machine_def by auto

lemma H': "H' \<ge> Suc (length M)" "H' \<ge> G" "H' \<ge> 6"
  using H'_def H_ge_length_M H_ge_G H_gr_3 by simp_all

lemma tm40_tm: "turing_machine 110 H' tm40"
  unfolding tm40_def tm39_def tm38_def tm37_def tm36_def tm35_def tm34_def tm33_def tm32_def tm31_def
  unfolding tm30_def tm29_def tm28_def tm27_def tm26_def tm25_def tm24_def tm23_def tm22_def tm21_def
  unfolding tm20_def tm19_def tm18_def tm17_def tm16_def tm15_def tm14_def tm13_def tm12_def tm11_def
  unfolding tm10_def tm9_def tm8_def tm7_def tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def
  using H'
    tm_copyn_tm tm_add_tm tm_incr_tm tm_times2_tm tm_setn_tm tm_times2incr_tm
    tm_plus_const_tm tm_right_tm tm_right_many_tm
    tm_PHI_init_tm[OF tm_M] tm_PHI0_tm tm_PHI1_tm tm_PHI2_tm tm_PHI345_tm tm_PHI6_tm tm_PHI7_tm
  by simp

lemma tm55_tm: "turing_machine 110 H' tm55"
  unfolding tm55_def tm54_def tm53_def tm52_def tm51_def
  unfolding tm50_def tm49_def tm48_def tm47_def tm46_def tm45_def tm44_def tm43_def tm42_def tm41_def
  using tm40_tm H'
    tm_copyn_tm tm_add_tm tm_incr_tm tm_setn_tm tm_set_tm[OF _ _ _ symbols_lt_numlistlist]
    tm_PHI8_tm tm_PHI9_tm
  by simp

lemma tm60_tm: "turing_machine 110 H' tm60"
  unfolding tm60_def tm59_def tm58_def tm57_def tm56_def
  using tm55_tm H' tm_erase_cr_tm tm_cr_tm tm_cp_until_tm tm_binencode_tm
  by simp

end  (* locale reduction_sat *)

text \<open>
Unlike before, we prove the semantics inside locale @{locale reduction_sat_x} since we
need not be concerned with ``polluting'' the namespace of the locale. After all there
will not be any more Turing machines.
\<close>

context reduction_sat_x
begin

context
  fixes tps0 :: "tape list"
  assumes k: "110 = length tps0"
  assumes tps0:
      "tps0 ! 0 = (\<lfloor>xs\<rfloor>, 0)"
      "\<And>i. 0 < i \<Longrightarrow> i < 110\<Longrightarrow> tps0 ! i = (\<lfloor>[]\<rfloor>, 0)"
begin

definition "tps1 \<equiv> map (\<lambda>j. if j < 1 \<or> 10 < j then tps0 ! j |+| 1 else tps0 ! j) [0..<110]"

lemma lentps1: "length tps1 = 110"
  using tps1_def by simp

lemma tps1:
  "0 < j \<Longrightarrow> j < 10 \<Longrightarrow> tps1 ! j = (\<lfloor>[]\<rfloor>, 0)"
  "10 < j \<Longrightarrow> j < 110 \<Longrightarrow> tps1 ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tps1_def k tps0 by simp_all

lemma tps1': "tps1 ! 0 = (\<lfloor>xs\<rfloor>, 1)"
proof -
  have "tps1 ! 0 = tps0 ! 0 |+| 1"
    using tps1_def k lentps1
    by (smt (verit, del_insts) add.right_neutral length_greater_0_conv length_map less_or_eq_imp_le list.size(3)
      not_numeral_le_zero nth_map nth_upt zero_less_one)
  then show ?thesis
    using tps0 by simp
qed

lemma tm1 [transforms_intros]: "transforms tm1 tps0 1 tps1"
  unfolding tm1_def by (tform tps: tps1_def tps0 k)

abbreviation "zs \<equiv> zeros m"

definition "tpsA \<equiv> tps1
  [9 := exc zs T' <!> 0,
   3 := (\<lfloor>exc zs T' <#> 0\<rfloor>\<^sub>N, 1),
   6 := (\<lfloor>exc zs T' <#> 1\<rfloor>\<^sub>N, 1),
   10 := exc zs T' <!> 1]"

lemma tpsA:
  "tpsA ! 0 = (\<lfloor>xs\<rfloor>, 1)"
  "tpsA ! 1 = (\<lfloor>[]\<rfloor>, 0)"
  "10 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsA ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsA_def tps1 tps1' by simp_all

lemma lentpsA: "length tpsA = 110"
  using tpsA_def tps1_def k by simp

definition "tps2 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1)]"

lemma lentps2: "length tps2 = 110"
  using tps2_def lentpsA by simp

lemma tm2 [transforms_intros]:
  assumes "ttt = 1 + (2 * d_polynomial p + 826) * (H + m') ^ 4"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps0 tps1_def k lentps1)
  have m': "m' = T' + Suc (2 * Suc (n + p n))"
    using m'_def by simp
  show "ttt = 1 + ((2 * d_polynomial p + 826) * (H + T' + Suc (Suc (Suc (2 * n + 2 * p n)))) ^ 4)"
    using assms m'
    by (metis ab_semigroup_add_class.add_ac(1) add_2_eq_Suc distrib_left_numeral mult_Suc_right)
  have m: "m = 2 * Suc (n + p n)"
    using m_def by simp
  show "tps2 = tps1
    [9 := exc zs T' <!> 0,
     3 := (\<lfloor>snd (exc zs T') :#: 0\<rfloor>\<^sub>N, 1),
     6 := (\<lfloor>snd (exc zs T') :#: 1\<rfloor>\<^sub>N, 1),
     10 := exc zs T' <!> 1, 11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
     15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
     16 := (\<lfloor>2 * Suc (n + p n)\<rfloor>\<^sub>N, 1),
     17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
     4 := (\<lfloor>map (\<lambda>t. snd (exc zs t) :#: 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
     7 := (\<lfloor>map (\<lambda>t. snd (exc zs t) :#: 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
     18 := (\<lfloor>T' + Suc (2 * Suc (n + p n))\<rfloor>\<^sub>N, 1),
     19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
     20 := (\<lfloor>(T' + Suc (2 * Suc (n + p n))) * H\<rfloor>\<^sub>N, 1)]"
    using tps2_def tpsA_def m m' by presburger
qed

definition "tps3 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   21 := (\<lfloor>m'\<rfloor>\<^sub>N, 1)]"

lemma lentps3: "length tps3 = 110"
  using tps3_def lentpsA by simp

lemma tm3 [transforms_intros]:
  assumes "ttt = 15 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m'"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: lentps2 k assms tps2_def)
  have "tps2 ! 21 = tpsA ! 21"
    using tps2_def by simp
  then show "tps2 ! 21 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsA canrepr_0 k lentps1 by simp
  show "tps3 = tps2[21 := (\<lfloor>m'\<rfloor>\<^sub>N, 1)]"
    unfolding tps3_def tps2_def by (simp only:)
  show "ttt = 1 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + (14 + 3 * (nlength m' + nlength 0))"
    using assms by simp
qed

definition "tps4 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   21 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   22 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma lentps4: "length tps4 = 110"
  using tps4_def lentpsA by (simp only: length_list_update)

lemma tm4 [transforms_intros]:
  assumes "ttt = 29 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 3 * nlength H"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform)
  show "19 < length tps3" "22 < length tps3"
   using lentps3 k by simp_all
  show "tps3 ! 19 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps3_def lentps3 k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps3 ! 22 = tpsA ! 22"
    unfolding tps3_def by simp
  then show "tps3 ! 22 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsA canrepr_0 k lentps1 by simp
  show "tps4 = tps3[22 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps4_def tps3_def by (simp only:)
  show "ttt = 15 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
      3 * nlength m' + (14 + 3 * (nlength H + nlength 0))"
    using assms by simp
qed

definition "tps5 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   21 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   22 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   1 := (\<lfloor>[]\<rfloor>, 1)]"

lemma lentps5: "length tps5 = 110"
  using tps5_def lentpsA by (simp only: length_list_update)

lemma tm5 [transforms_intros]:
  assumes "ttt = 30 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 3 * nlength H"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform)
  show "1 < length tps4"
    using lentps4 k by simp
  show "ttt = 29 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 3 * nlength H + Suc 0"
    using assms by simp
  have "tps4 ! 1 = tpsA ! 1"
    using tps4_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then have "tps4 ! 1 = (\<lfloor>[]\<rfloor>, 0)"
    using tpsA by simp
  then have "tps4 ! 1 |+| 1 = (\<lfloor>[]\<rfloor>, 1)"
    by simp
  then show "tps5 = tps4[1 := tps4 ! 1 |+| 1]"
    unfolding tps5_def tps4_def by (simp only: list_update_swap)
qed

definition "tps6 \<equiv> tpsA
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   21 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   22 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0),
   21 := (\<lfloor>Suc (Suc m')\<rfloor>\<^sub>N, 1),
   21 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   21 + 6 := (\<lfloor>nll_Psi (Suc (Suc m') * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma lentps6: "length tps6 = 110"
  using tps6_def lentpsA by (simp only: length_list_update)

lemma tm6 [transforms_intros]:
  assumes "ttt = 30 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 3 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform)
  show "21 + 8 < length tps5"
    using k lentps5 by simp
  show "tps5 ! 1 = (\<lfloor>[]\<rfloor>, 1)"
    using tps5_def lentps5 k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tps5 ! 21 = (\<lfloor>m'\<rfloor>\<^sub>N, 1)"
    using tps5_def lentps5 k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have *: "21 + 1 = 22"
    by simp
  show "tps5 ! (21 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps5_def lentps5 k by (simp only: * length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps5 ! 23 = tpsA ! 23"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 2) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  have "tps5 ! 24 = tpsA ! 24"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  have "tps5 ! 25 = tpsA ! 25"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  have "tps5 ! 26 = tpsA ! 26"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  have "tps5 ! 27 = tpsA ! 27"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  have "tps5 ! 28 = tpsA ! 28"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  have "tps5 ! 29 = tpsA ! 29"
    using tps5_def by (simp only: nth_list_update_eq nth_list_update_neq)
  then show "tps5 ! (21 + 8) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsA k by simp
  show "ttt = 30 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
      3 * nlength m' + 3 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2"
    using assms by simp
  show "tps6 = tps5
    [21 := (\<lfloor>Suc (Suc m')\<rfloor>\<^sub>N, 1),
     21 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     21 + 6 := (\<lfloor>nll_Psi (Suc (Suc m') * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape (formula_n \<Phi>\<^sub>0)]"
    unfolding tps6_def tps5_def by (simp only: list_update_swap[of 1] list_update_overwrite)
qed

definition "tpsB \<equiv> tpsA
  [21 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   22 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   21 := (\<lfloor>Suc (Suc m')\<rfloor>\<^sub>N, 1),
   21 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   21 + 6 := (\<lfloor>nll_Psi (Suc (Suc m') * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tpsB: "j > 27 \<Longrightarrow> j < 110 \<Longrightarrow> tpsB ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsB_def tpsA by simp

lemma lentpsB: "length tpsB = 110"
  using lentpsA tpsB_def by simp

lemma tps6: "tps6 = tpsB
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0)]"
  unfolding tps6_def tpsB_def by (simp only: list_update_swap)

lemma tps6': "j > 27 \<Longrightarrow> j < 110 \<Longrightarrow> tps6 ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tps6 tpsB by (simp only: nth_list_update_neq)

definition "tps7 \<equiv> tpsB
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0),
   29 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm7 [transforms_intros]:
  assumes "ttt = 40 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 3 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 2 * nlength H"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def
proof (tform)
  show "29 < length tps6"
    using lentpsB k tps6 by (simp only: length_list_update)
  show "tps6 ! 29 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps6' canrepr_0 k by simp
  show "tps7 = tps6[29 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps7_def using tps6 by (simp only: list_update_swap)
  show "ttt = 30 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
      3 * nlength m' + 3 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
      (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps8 \<equiv> tpsB
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1),
   29 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   28 + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   28 + 6 := (\<lfloor>nll_Psi 0 H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm8 [transforms_intros]:
  assumes "ttt = 40 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
    3 * nlength m' + 3 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
    2 * nlength H + 1875 * H ^ 4"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def
proof (tform)
  show "28 + 7 < length tps7"
    using lentpsB k tps7_def by (simp only: length_list_update)
  show "tps7 ! 1 = nlltape (formula_n \<Phi>\<^sub>0)"
    using tps7_def lentpsB k by (simp only: nth_list_update_eq nth_list_update_neq length_list_update)
  show "tps7 ! 28 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsB tps7_def canrepr_0 k by (simp only: nth_list_update_neq)
  have "tps7 ! 29 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps7_def lentpsB k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps7 ! 30 = tpsB ! 30"
    using tps7_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 2) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsB k by simp
  have "tps7 ! 31 = tpsB ! 31"
    using tps7_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsB k by simp
  have "tps7 ! 32 = tpsB ! 32"
    using tps7_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsB k by simp
  have "tps7 ! 33 = tpsB ! 33"
    using tps7_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsB k by simp
  have "tps7 ! 34 = tpsB ! 34"
    using tps7_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsB k by simp
  have "tps7 ! 35 = tpsB ! 35"
    using tps7_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps7 ! (28 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsB k by simp
  show "ttt = 40 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
      3 * nlength m' + 3 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
      2 * nlength H + 1875 * H ^ 4"
    using assms by simp
  show "tps8 = tps7
    [28 + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
     28 + 6 := (\<lfloor>nll_Psi 0 H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1)]"
    unfolding tps8_def tps7_def by (simp only: list_update_swap[of 1] list_update_overwrite)
qed

definition "tpsC \<equiv> tpsB
  [29 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   28 + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   28 + 6 := (\<lfloor>nll_Psi 0 H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tpsC: "j > 34 \<Longrightarrow> j < 110 \<Longrightarrow> tpsC ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsC_def tpsB by simp

lemma lentpsC: "length tpsC = 110"
  using lentpsB tpsC_def by simp

lemma tps8: "tps8 = tpsC
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1)]"
  unfolding tps8_def tpsC_def by (simp only: list_update_swap)

definition "tps9 \<equiv> tpsC
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1),
   35 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"

lemma tm9 [transforms_intros]:
  assumes "ttt = 54 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' +
    5 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    3 * nlength n"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def
proof (tform)
  show "11 < length tps8" "35 < length tps8"
    using lentpsC tps8 k by (simp_all only: length_list_update)
  show "tps8 ! 11 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps8 lentpsC k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps8 ! 35 = tpsC ! 35"
    using tps8 by (simp only: nth_list_update_neq)
  then show "tps8 ! 35 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsC k canrepr_0 by simp
  show "tps9 = tps8[35 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"
    unfolding tps9_def tps8 by (simp only:)
  show "ttt = 40 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
      3 * nlength m' + 3 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
      2 * nlength H + 1875 * H ^ 4 + (14 + 3 * (nlength n + nlength 0))"
    using assms by simp
qed

definition "tps10 \<equiv> tpsC
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1),
   35 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   36 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm10 [transforms_intros]:
  assumes "ttt = 64 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
    3 * nlength m' + 5 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
    1875 * H ^ 4 + 3 * nlength n + 2 * nlength H"
  shows "transforms tm10 tps0 ttt tps10"
  unfolding tm10_def
proof (tform)
  show "36 < length tps9"
    using lentpsC tps9_def k by (simp_all only: length_list_update)
  have "tps9 ! 36 = tpsC ! 36"
    using tps9_def by (simp only: nth_list_update_neq)
  then show "tps9 ! 36 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsC k canrepr_0 by simp
  show "tps10 = tps9[36 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps10_def tps9_def by (simp only: list_update_swap)
  show "ttt = 54 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
      3 * nlength m' + 5 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
      1875 * H ^ 4 + 3 * nlength n + (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps11 \<equiv> tpsC
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2),
   35 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   36 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   35 := (\<lfloor>2 * n + 2\<rfloor>\<^sub>N, 1),
   35 + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   35 + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * n)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm11 [transforms_intros]:
  assumes "ttt = 64 + (2 * d_polynomial p + 826) * (H + m') ^ 4 +
    3 * nlength m' + 7 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 +
    1875 * H ^ 4 + 3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
  shows "transforms tm11 tps0 ttt tps11"
  unfolding tm11_def
proof (tform)
  show "35 + 8 < length tps10"
    using lentpsC k tps10_def by (simp only: length_list_update)
  show "tps10 ! 1 = nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1)"
    using tps10_def lentpsC k by (simp only: nth_list_update_eq nth_list_update_neq length_list_update)
  show "tps10 ! 35 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps10_def lentpsC k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps10 ! 36 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps10_def lentpsC k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps10 ! 37 = tpsC ! 37"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 2) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  have "tps10 ! 38 = tpsC ! 38"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  have "tps10 ! 39 = tpsC ! 39"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  have "tps10 ! 40 = tpsC ! 40"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  have "tps10 ! 41 = tpsC ! 41"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  have "tps10 ! 42 = tpsC ! 42"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  have "tps10 ! 43 = tpsC ! 43"
    using tps10_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps10 ! (35 + 8) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsC k by simp
  show "tps11 = tps10
    [35 := (\<lfloor>2 * n + 2\<rfloor>\<^sub>N, 1),
     35 + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
     35 + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * n)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2)]"
    unfolding tps11_def tps10_def by (simp only: list_update_swap[of 1] list_update_overwrite)
  show "ttt = 64 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' +
      5 * nlength H + 5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      3 * nlength n + 2 * nlength H + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
    using assms by simp
qed

definition "tpsD \<equiv> tpsC
  [35 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   36 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   35 := (\<lfloor>2 * n + 2\<rfloor>\<^sub>N, 1),
   35 + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   35 + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * n)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tpsD: "41 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsD ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsD_def tpsC by simp

lemma lentpsD: "length tpsD = 110"
  using lentpsC tpsD_def by simp

lemma tps11: "tps11 = tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2)]"
  unfolding tps11_def tpsD_def by (simp only: list_update_swap)

definition "tps12 \<equiv> tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2),
   42 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm12 [transforms_intros]:
  assumes "ttt = 76 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 7 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
  shows "transforms tm12 tps0 ttt tps12"
  unfolding tm12_def
proof (tform)
  show "42 < length tps11"
    using lentpsD tps11 k by (simp_all only: length_list_update)
  have "tps11 ! 42 = tpsD ! 42"
    using tps11 by (simp only: nth_list_update_neq)
  then show "tps11 ! 42 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsD k canrepr_0 by simp
  show "tps12 = tps11[42 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    unfolding tps12_def tps11 by (simp only:)
  show "ttt = 64 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 7 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      (10 + 2 * nlength 0 + 2 * nlength 1)"
    using canrepr_1 assms by simp
qed

definition "tps13 \<equiv> tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2),
   42 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   43 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm13 [transforms_intros]:
  assumes "ttt = 86 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
  shows "transforms tm13 tps0 ttt tps13"
  unfolding tm13_def
proof (tform)
  show "43 < length tps12"
    using lentpsD tps12_def k by (simp_all only: length_list_update)
  have "tps12 ! 43 = tpsD ! 43"
    using tps12_def by (simp only: nth_list_update_neq)
  then show "tps12 ! 43 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsD k canrepr_0 by simp
  show "tps13 = tps12[43 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps13_def tps12_def by (simp only:)
  show "ttt = 76 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 7 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 + 3 * nlength n +
      3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps14 \<equiv> tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2),
   42 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   43 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   44 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"

lemma tm14 [transforms_intros]:
  assumes "ttt = 100 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
  shows "transforms tm14 tps0 ttt tps14"
  unfolding tm14_def
proof (tform)
  show "44 < length tps13"
    using lentpsD tps13_def k by (simp_all only: length_list_update)
  have "tps13 ! 44 = tpsD ! 44"
    using tps13_def by (simp only: nth_list_update_neq)
  then show "tps13 ! 44 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsD k canrepr_0 by simp
  show "tps14 = tps13[44 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"
    unfolding tps14_def tps13_def by (simp only:)
  show "ttt = 86 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      (10 + 2 * nlength 0 + 2 * nlength 2)"
    using nlength_2 assms by simp
qed

definition "tps15 \<equiv> tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2),
   42 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   43 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   44 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   50 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"

lemma tm15 [transforms_intros]:
  assumes "ttt = 114 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    6 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
  shows "transforms tm15 tps0 ttt tps15"
  unfolding tm15_def
proof (tform)
  show "11 < length tps14" "50 < length tps14"
    using lentpsD tps14_def k by (simp_all only: length_list_update)
  show "tps14 ! 11 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps14_def k lentpsD by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps14 ! 50 = tpsD ! 50"
    using tps14_def by (simp only: nth_list_update_neq)
  then show "tps14 ! 50 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsD k canrepr_0 by simp
  show "tps15 = tps14[50 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"
    unfolding tps15_def tps14_def by (simp only:)
  show "ttt = 100 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      3 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      (14 + 3 * (nlength n + nlength 0))"
    using assms by simp
qed

definition "tps16 \<equiv> tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2),
   42 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   43 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   44 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   50 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1)]"

lemma tm16 [transforms_intros]:
  assumes "ttt = 126 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2"
  shows "transforms tm16 tps0 ttt tps16"
  unfolding tm16_def
proof (tform)
  show "2 \<le> length tps15" "50 < length tps15"
    using lentpsD tps15_def k by (simp_all only: length_list_update)
  show "tps15 ! 50 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps15_def k lentpsD by (simp only: length_list_update nth_list_update_eq)
  have "tps16 = tps15[50 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1)]"
    unfolding tps16_def tps15_def by (simp only: list_update_swap[of 1] list_update_overwrite)
  then show "tps16 = tps15[50 := (\<lfloor>Suc (2 * n)\<rfloor>\<^sub>N, 1)]"
    by simp
  show "ttt = 114 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 + 6 * nlength n +
      3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 + (12 + 4 * nlength n)"
    using assms by simp
qed

definition "tps17 \<equiv> tpsD
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   42 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   43 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   44 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   50 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
   42 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
   42 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm17 [transforms_intros]:
  assumes "ttt = 126 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
  shows "transforms tm17 tps0 ttt tps17"
  unfolding tm17_def
proof (tform transforms_intros: tm_PHI3)
  show "42 + 8 < length tps16"
    using lentpsD k tps16_def by (simp only: length_list_update)
  show "tps16 ! 1 = nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2)"
    using tps16_def lentpsD k by (simp only: nth_list_update_eq nth_list_update_neq length_list_update)
  show "tps16 ! 42 = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
    using tps16_def lentpsD k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps16 ! 43 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps16_def lentpsD k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps16 ! 44 = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    using tps16_def lentpsD k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 2) = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps16 ! 45 = tpsD ! 45"
    using tps16_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsD k by simp
  have "tps16 ! 46 = tpsD ! 46"
    using tps16_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsD k by simp
  have "tps16 ! 47 = tpsD ! 47"
    using tps16_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsD k by simp
  have "tps16 ! 48 = tpsD ! 48"
    using tps16_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsD k by simp
  have "tps16 ! 49 = tpsD ! 49"
    using tps16_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsD k by simp
  have "tps16 ! 50 = (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1)"
    using tps16_def lentpsD k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps16 ! (42 + 8) = (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps17 = tps16
    [42 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
     1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
     42 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    unfolding tps17_def tps16_def by (simp only: list_update_swap[of 1] list_update_overwrite)
  then show "tps17 = tps16
    [42 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
     1 := nlltape (((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1) @ formula_n \<Phi>\<^sub>2) @ formula_n \<Phi>\<^sub>3),
     42 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    by simp
  show "ttt = 126 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
    using assms by simp
qed

definition "tpsE \<equiv> tpsD
  [42 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   43 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   44 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   50 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
   42 := (\<lfloor>1 + 2 * n\<rfloor>\<^sub>N, 1),
   42 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tpsE: "50 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsE ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsE_def tpsD by simp

lemma lentpsE: "length tpsE = 110"
  using lentpsD tpsE_def by simp

lemma tps17: "tps17 = tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3)]"
  unfolding tps17_def tpsE_def by (simp only: list_update_swap)

definition "tps18 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm18 [transforms_intros]:
  assumes "ttt = 136 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
  shows "transforms tm18 tps0 ttt tps18"
  unfolding tm18_def
proof (tform)
  show "52 < length tps17"
    using lentpsE tps17 k by (simp_all only: length_list_update)
  have "tps17 ! 52 = tpsE ! 52"
    using tps17 by (simp only: nth_list_update_neq)
  then show "tps17 ! 52 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsE k canrepr_0 by simp
  show "tps18 = tps17[52 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps18_def tps17 by (simp only:)
  show "ttt = 126 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 9 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) +
      (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps19 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"

lemma tm19 [transforms_intros]:
  assumes "ttt = 150 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
  shows "transforms tm19 tps0 ttt tps19"
  unfolding tm19_def
proof (tform)
  show "53 < length tps18"
    using lentpsE tps18_def k by (simp_all only: length_list_update)
  have "tps18 ! 53 = tpsE ! 53"
    using tps18_def by (simp only: nth_list_update_neq)
  then show "tps18 ! 53 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsE k canrepr_0 by simp
  show "tps19 = tps18[53 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"
    unfolding tps19_def tps18_def by (simp only:)
  show "ttt = 136 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) +
      (10 + 2 * nlength 0 + 2 * nlength 2)"
    using assms nlength_2 by simp
qed

definition "tps20 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"

lemma tm20 [transforms_intros]:
  assumes "ttt = 164 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      13 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
  shows "transforms tm20 tps0 ttt tps20"
  unfolding tm20_def
proof (tform)
  show "11 < length tps19" "51 < length tps19"
    using lentpsE tps19_def k by (simp_all only: length_list_update)
  show "tps19 ! 11 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps19_def k lentpsE by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps19 ! 51 = tpsE ! 51"
    using tps19_def by (simp only: nth_list_update_neq)
  then show "tps19 ! 51 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsE k canrepr_0 by simp
  show "tps20 = tps19[51 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"
    unfolding tps20_def tps19_def by (simp only:)
  show "ttt = 150 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      10 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) +
      (14 + 3 * (nlength n + nlength 0))"
    using assms by simp
qed

definition "tps21 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)]"

lemma tm21 [transforms_intros]:
  assumes "ttt = 169 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2))"
  shows "transforms tm21 tps0 ttt tps21"
  unfolding tm21_def
proof (tform time: assms)
  show "51 < length tps20"
    using lentpsE tps20_def k by (simp only: length_list_update)
  show "tps20 ! 51 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps20_def k lentpsE by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tps21 = tps20[51 := (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)]"
    unfolding tps21_def tps20_def by (simp only: list_update_overwrite)
qed

definition "tps22 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1)]"

lemma tm22 [transforms_intros]:
  assumes "ttt = 184 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3)"
  shows "transforms tm22 tps0 ttt tps22"
  unfolding tm22_def
proof (tform time: assms)
  show "51 < length tps21"
    using lentpsE tps21_def k by (simp only: length_list_update)
  show "tps21 ! 51 = (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)"
    using tps21_def k lentpsE by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tps22 = tps21[51 := (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1)]"
    unfolding tps22_def tps21_def by (simp only: list_update_overwrite)
qed

definition "tps23 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1),
   59 := (\<lfloor>m\<rfloor>\<^sub>N, 1)]"

lemma tm23 [transforms_intros]:
  assumes "ttt = 198 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    3 * nlength m"
  shows "transforms tm23 tps0 ttt tps23"
  unfolding tm23_def
proof (tform)
  show "16 < length tps22" "59 < length tps22"
    using lentpsE tps22_def k by (simp_all only: length_list_update)
  show "tps22 ! 16 = (\<lfloor>m\<rfloor>\<^sub>N, 1)"
    using tps22_def k lentpsE by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps22 ! 59 = tpsE ! 59"
    using tps22_def by (simp only: nth_list_update_neq)
  then show "tps22 ! 59 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsE k canrepr_0 by simp
  show "tps23 = tps22[59 := (\<lfloor>m\<rfloor>\<^sub>N, 1)]"
    unfolding tps23_def tps22_def by (simp only:)
  show "ttt = 184 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      (14 + 3 * (nlength m + nlength 0))"
    using assms by simp
qed

definition "tps24 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1),
   59 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)]"

lemma tm24 [transforms_intros]:
  assumes "ttt = 203 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    5 * nlength m"
  shows "transforms tm24 tps0 ttt tps24"
  unfolding tm24_def
proof (tform time: assms)
  show "59 < length tps23"
    using lentpsE tps23_def k by (simp only: length_list_update)
  have "tps23 ! 59 = (\<lfloor>m\<rfloor>\<^sub>N, 1)"
    using tps23_def k lentpsE by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps23 ! 59 = (\<lfloor>m\<rfloor>\<^sub>N, 1)"
    by simp
  show "tps24 = tps23[59 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)]"
    unfolding tps24_def tps23_def by (simp only: list_update_overwrite)
qed

definition "tps25 \<equiv> tpsE
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
   52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1),
   59 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1),
   51 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm25 [transforms_intros]:
  assumes "ttt = 203 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      5 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2))"
  shows "transforms tm25 tps0 ttt tps25"
  unfolding tm25_def
proof (tform transforms_intros: tm_PHI4)
  show "51 + 8 < length tps24"
    using lentpsE tps24_def k by (simp only: length_list_update)
  show "tps24 ! 1 = nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3)"
    using tps24_def lentpsE k by (simp only: nth_list_update_eq nth_list_update_neq length_list_update)
  have "tps24 ! 51 = (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1)"
    using tps24_def lentpsE k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! 51 = (\<lfloor>2 * n + 2 + 1\<rfloor>\<^sub>N, 1)"
    by (metis add.assoc nat_1_add_1 numeral_Bit1 numerals(1))
  have "tps24 ! 52 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps24_def lentpsE k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps24 ! 53 = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    using tps24_def lentpsE k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 2) = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps24 ! 54 = tpsE ! 54"
    using tps24_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsE k by simp
  have "tps24 ! 55 = tpsE ! 55"
    using tps24_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsE k by simp
  have "tps24 ! 56 = tpsE ! 56"
    using tps24_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsE k by simp
  have "tps24 ! 57 = tpsE ! 57"
    using tps24_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsE k by simp
  have "tps24 ! 58 = tpsE ! 58"
    using tps24_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps24 ! (51 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsE k by simp
  have "tps24 ! 59 = (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)"
    using tps24_def lentpsE k by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  moreover have *: "Suc m = 2 * n + 2 + 1 + 2 * p n"
    using m_def by simp
  ultimately show "tps24 ! (51 + 8) = (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps25 = tps24
    [51 := (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1),
     1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
     51 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    unfolding tps25_def tps24_def by (simp only: list_update_swap list_update_overwrite)
  then show "tps25 = tps24
    [51 := (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1),
     1 := nlltape ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3) @ formula_n \<Phi>\<^sub>4),
     51 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    by simp
  show "ttt = 203 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      5 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (2 * n + 2 + 1 + 2 * p n))\<^sup>2))"
    using assms * by simp
qed

definition "tpsF \<equiv> tpsE
  [52 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   53 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 3\<rfloor>\<^sub>N, 1),
   59 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1),
   51 := (\<lfloor>2 * n + 2 + 1 + 2 * p n\<rfloor>\<^sub>N, 1),
   51 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tpsF: "59 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsF ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsF_def tpsE by simp

lemma lentpsF: "length tpsF = 110"
  using lentpsE tpsF_def by simp

lemma tps25: "tps25 = tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4)]"
  unfolding tps25_def tpsF_def by (simp only: list_update_swap)

definition "tps26 \<equiv> tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
   61 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm26 [transforms_intros]:
  assumes "ttt = 213 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    5 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2))"
  shows "transforms tm26 tps0 ttt tps26"
  unfolding tm26_def
proof (tform)
  show "61 < length tps25"
    using lentpsF tps25 k by (simp_all only: length_list_update)
  have "tps25 ! 61 = tpsF ! 61"
    using tps25 by (simp only: nth_list_update_neq)
  then show "tps25 ! 61 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsF k canrepr_0 by simp
  show "tps26 = tps25[61 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps26_def tps25 by (simp only:)
  show "ttt = 203 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 11 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      5 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
      (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps27 \<equiv> tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
   61 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>m\<rfloor>\<^sub>N, 1)]"

lemma tm27 [transforms_intros]:
  assumes "ttt = 227 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    8 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2))"
  shows "transforms tm27 tps0 ttt tps27"
  unfolding tm27_def
proof (tform)
  show "16 < length tps26" "60 < length tps26"
    using lentpsF tps26_def k by (simp_all only: length_list_update)
  show "tps26 ! 16 = (\<lfloor>m\<rfloor>\<^sub>N, 1)"
    using tps26_def k lentpsF by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tps26 ! 60 = tpsF ! 60"
    using tps26_def by (simp only: nth_list_update_neq)
  then show "tps26 ! 60 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsF k canrepr_0 by simp
  show "tps27 = tps26[60 := (\<lfloor>m\<rfloor>\<^sub>N, 1)]"
    unfolding tps27_def tps26_def by (simp only:)
  show "ttt = 213 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      5 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
      (14 + 3 * (nlength m + nlength 0))"
    using assms by simp
qed

definition "tps28 \<equiv> tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
   61 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)]"

lemma tm28 [transforms_intros]:
  assumes "ttt = 232 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2))"
  shows "transforms tm28 tps0 ttt tps28"
  unfolding tm28_def
proof (tform)
  show "60 < length tps27"
    using lentpsF tps27_def k by (simp_all only: length_list_update)
  show "tps27 ! 60 = (\<lfloor>m\<rfloor>\<^sub>N, 1)"
    using tps27_def k lentpsF by (simp only: length_list_update nth_list_update_eq)
  show "tps28 = tps27[60 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)]"
    unfolding tps28_def tps27_def by (simp only: list_update_overwrite)
  show "ttt = 227 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      8 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
      (5 + 2 * nlength m)"
    using assms by simp
qed

definition "tps29 \<equiv> tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
   61 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1),
   68 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)]"

lemma tm29 [transforms_intros]:
  assumes "ttt = 246 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
    3 * nlength (Suc m)"
  shows "transforms tm29 tps0 ttt tps29"
  unfolding tm29_def
proof (tform)
  show "60 < length tps28" "68 < length tps28"
    using lentpsF tps28_def k by (simp_all only: length_list_update)
  show "tps28 ! 60 = (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)"
    using tps28_def k lentpsF by (simp only: length_list_update nth_list_update_eq)
  have "tps28 ! 68 = tpsF ! 68"
    using tps28_def by (simp only: nth_list_update_neq)
  then show "tps28 ! 68 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsF k canrepr_0 by simp
  show "tps29 = tps28[68 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)]"
    unfolding tps29_def tps28_def by (simp only: list_update_overwrite)
  show "ttt = 232 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
      (14 + 3 * (nlength (Suc m) + nlength 0))"
    using assms by simp
qed

definition "tps30 \<equiv> tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4),
   61 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1),
   68 := (\<lfloor>T' + Suc m\<rfloor>\<^sub>N, 1)]"

lemma tm30 [transforms_intros]:
  assumes "ttt = 256 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
    5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
    15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
    Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
    10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
    3 * nlength (Suc m) + 3 * max (nlength T') (nlength (Suc m))"
  shows "transforms tm30 tps0 ttt tps30"
  unfolding tm30_def
proof (tform)
  show "17 < length tps29" "68 < length tps29"
    using lentpsF tps29_def k by (simp_all only: length_list_update)
  show "tps29 ! 17 = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    using tps29_def k lentpsF by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps29 ! 68 = (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)"
    using tps29_def k lentpsF by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps30 = tps29[68 := (\<lfloor>T' + Suc m\<rfloor>\<^sub>N, 1)]"
    unfolding tps30_def tps29_def by (simp only: list_update_overwrite)
  show "ttt = 246 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
      3 * nlength (Suc m) + (3 * max (nlength T') (nlength (Suc m)) + 10)"
    using assms by simp
qed

definition "tps31 \<equiv> tpsF
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
         (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
          formula_n \<Phi>\<^sub>5),
   61 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1),
   68 := (\<lfloor>T' + Suc m\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m + T'\<rfloor>\<^sub>N, 1),
   60 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

definition "ttt31 \<equiv> 256 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
  5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
  15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
  Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
  10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
  3 * nlength (Suc m) + 3 * max (nlength T') (nlength (Suc m)) +
  Suc T' * (9 + 1891 * (H ^ 4 * (nlength (Suc m + T'))\<^sup>2))"

lemma le_N: "y \<le> 2 * n + 2 * p n + 3 + T' \<Longrightarrow> y \<le> N "
  using H_gr_2 m'_def N_eq
  by (metis Suc_1 Suc_leI add_2_eq_Suc' add_leE le_trans mult_le_mono1 nat_mult_1)

lemma n_le_N: "n \<le> N "
  using le_N by simp

lemma H_le_N: "H \<le> N "
  using N_eq by simp

lemma N_ge_1: "N \<ge> 1"
  using H_le_N H_ge_3 by simp

lemma pow2_sum_le:
  fixes a b :: nat
  shows "(a + b) ^ 2 \<le> a ^ 2 + (2 * a + 1) * b ^ 2"
proof -
  have "(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2"
    by algebra
  also have "... \<le> a ^ 2 + 2 * a * b ^ 2 + b ^ 2"
    by (simp add: power2_nat_le_imp_le)
  also have "... = a ^ 2 + (2 * a + 1) * b ^ 2"
    by simp
  finally show ?thesis .
qed

lemma ttt31: "ttt31 \<le> (32 * d_polynomial p + 222011) * H ^ 4 * N ^ 4"
proof -
  have a: "Suc T' * (9 + 1891 * (H ^ 4 * (nlength (Suc m + T'))\<^sup>2)) \<le> 1900 * H ^ 4 * N ^ 4"
  proof -
    have "Suc (2 * n + 2 * p n + 2) + T' \<le> 2 * n + 2 * p n + 3 + T' "
      by simp
    also have "... \<le> H * (2 * n + 2 * p n + 3 + T')"
      using H_gr_2 by simp
    finally have "Suc m + T' \<le> N "
      unfolding N_eq m_def by simp
    then have "nlength (Suc m + T') \<le> N "
      using nlength_le_n order.trans by auto
    then have "(nlength (Suc m + T')) ^ 2 \<le> N ^ 2"
      by simp
    then have "H ^ 4 * (nlength (Suc m + T')) ^ 2 \<le> H ^ 4 * N ^ 2"
      using mult_le_mono by simp
    then have "9 + 1891 * (H ^ 4 * (nlength (Suc m + T'))\<^sup>2) \<le> 9 + 1891 * H ^ 4 * N ^ 2"
      by simp
    then have "Suc T' * (9 + 1891 * (H ^ 4 * (nlength (Suc m + T'))\<^sup>2)) \<le> Suc T' * (9 + 1891 * H ^ 4 * N ^ 2)"
      using mult_le_mono2 by blast
    also have "... \<le> N * (9 + 1891 * H ^ 4 * N ^ 2)"
    proof -
      have "Suc T' \<le> N "
        using le_N by simp
      then show ?thesis
        using mult_le_mono1 by blast
    qed
    also have "... = 9 * N + 1891 * H ^ 4 * N ^ 3"
      by algebra
    also have "... \<le> 9 * N ^ 3 + 1891 * H ^ 4 * N ^ 3"
      using linear_le_pow by simp
    also have "... \<le> 9 * N ^ 3 + 1891 * H ^ 4 * N ^ 4"
      using pow_mono'[of 3 4] by simp
    also have "... \<le> 9 * N ^ 4 + 1891 * H ^ 4 * N ^ 4"
      using pow_mono'[of 3 4] by simp
    also have "... \<le> 9 * H ^ 4 * N ^ 4 + 1891 * H ^ 4 * N ^ 4"
      using H_ge_3 by simp
    also have "... = 1900 * H ^ 4 * N ^ 4"
      by simp
    finally show ?thesis .
  qed

  have b: "5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 \<le> 140675 * H ^ 4 * N ^ 4"
  proof -
    have "3 * H + m' * H \<le> 2 * N "
      using N_eq m'_def by simp
    then have "nlength (3 * H + m' * H) \<le> nlength (2 * N)"
      using nlength_mono by simp
    also have "... \<le> Suc (nlength N)"
      using le_trans nlength_times2 by blast
    also have "... \<le> Suc N"
      using nlength_le_n by simp
    finally have "nlength (3 * H + m' * H) \<le> Suc N" .
    then have "3 + nlength (3 * H + m' * H) \<le> 4 + N "
      by simp
    then have "(3 + nlength (3 * H + m' * H)) ^ 2 \<le> (4 + N) ^ 2"
      by simp
    also have "... \<le> 16 + 9 * N ^ 2"
      using pow2_sum_le[of 4 "N "] by simp
    finally have "(3 + nlength (3 * H + m' * H)) ^ 2 \<le> 16 + 9 * N ^ 2" .
    then have "5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 \<le> 5627 * H ^ 4 * (16 + 9 * N ^ 2)"
      by simp
    also have "... = 5627 * H ^ 4 * 16 + 5627 * H ^ 4 * 9 * N ^ 2"
      by algebra
    also have "... = 90032 * H ^ 4 + 50643 * H ^ 4 * N ^ 2"
      by simp
    also have "... \<le> 90032 * H ^ 4 * N ^ 2 + 50643 * H ^ 4 * N ^ 2"
      using pow_mono' N_ge_1 by simp
    also have "... = 140675 * H ^ 4 * N ^ 2"
      by simp
    also have "... \<le> 140675 * H ^ 4 * N ^ 4"
      using pow_mono' by simp
    finally show ?thesis .
  qed

  have c: "3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 \<le> 60224 * H ^ 4 * N ^ 4"
  proof -
    have "3 * H \<le> N " and "2 * n * H \<le> N "
      using N_eq by simp_all
    then have "3 * H + 2 * n * H \<le> 2 * N "
      by simp
    then have "nlength (3 * H + 2 * n * H) \<le> 3 * H + 2 * n * H"
      using nlength_le_n by simp
    then have "nlength (3 * H + 2 * n * H) \<le> H * (3 + 2 * n)"
      by (metis distrib_right mult.commute)
    also have "... \<le> N "
      using N_eq by simp
    finally have "nlength (3 * H + 2 * n * H) \<le> N " .
    then have "3 + nlength (3 * H + 2 * n * H) \<le> 3 + N "
      by simp
    then have "(3 + nlength (3 * H + 2 * n * H))\<^sup>2 \<le> (3 + N) ^ 2"
      by simp
    also have "... \<le> 9 + 7 * N ^ 2"
      using pow2_sum_le[of 3 "N "] by simp
    finally have "(3 + nlength (3 * H + 2 * n * H))\<^sup>2 \<le> 9 + 7 * N ^ 2" .
    then have "3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 \<le> 3764 * H ^ 4 * (9 + 7 * N ^ 2)"
      by simp
    also have "... = 3764 * H ^ 4 * 9 + 3764 * H ^ 4 * 7 * N ^ 2"
      by algebra
    also have "... = 33876 * H ^ 4 + 26348 * H ^ 4 * N ^ 2"
      by simp
    also have "... \<le> 33876 * H ^ 4 * N ^ 2 + 26348 * H ^ 4 * N ^ 2"
      using pow_mono' N_ge_1 by simp
    also have "... = 60224 * H ^ 4 * N ^ 2"
      by simp
    also have "... \<le> 60224 * H ^ 4 * N ^ 4"
      using pow_mono' by simp
    finally show ?thesis .
  qed

  have d: "Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) \<le> 1906 * H ^ 4 * N ^ 4"
  proof -
    have "Suc (p n) \<le> N "
      using le_N by simp
    then have "Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) \<le> N * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2))"
      using mult_le_mono1 by blast
    also have "... \<le> N * (9 + 1897 * (H ^ 4 * (nlength N)\<^sup>2))"
    proof -
      have "Suc m \<le> N "
        using m_def le_N by simp
      then show ?thesis
        using H4_nlength H_ge_3 add_le_mono less_or_eq_imp_le mult_le_mono by presburger
    qed
    also have "... \<le> N * (9 + 1897 * (H ^ 4 * N\<^sup>2))"
      using nlength_le_n by simp
    also have "... = N * 9 + N * 1897 * H ^ 4 * N ^ 2"
      by (simp add: add_mult_distrib2)
    also have "... \<le> N ^ 3 * 9 + N * 1897 * H ^ 4 * N ^ 2"
      using linear_le_pow by simp
    also have "... \<le> 9 * H ^ 4 * N ^ 3 + N * 1897 * H ^ 4 * N ^ 2"
      using H_ge_3 by simp
    also have "... = 9 * H ^ 4 * N ^ 3 + 1897 * H ^ 4 * N ^ 3"
      by algebra
    also have "... = 1906 * H ^ 4 * N ^ 3"
      by simp
    also have "... \<le> 1906 * H ^ 4 * N ^ 4"
      using pow_mono' by simp
    finally show ?thesis .
  qed

  have e: "Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) \<le> 1906 * H ^ 4 * N ^ 4"
  proof -
    have "nlength (1 + 2 * n) \<le> N "
      using le_N nlength_le_n[of "1 + 2 * n "] by simp
    then have "(nlength (1 + 2 * n)) ^ 2 \<le> N ^ 2"
      by simp
    then have "Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) \<le> Suc n * (9 + 1897 * (H ^ 4 * N\<^sup>2))"
      using add_le_mono less_or_eq_imp_le mult_le_mono2 by presburger
    also have "... = Suc n * (9 + 1897 * H ^ 4 * N\<^sup>2)"
      by simp
    also have "... \<le> N * (9 + 1897 * H ^ 4 * N ^ 2)"
      using mult_le_mono1[OF le_N[of "Suc n"]] by simp
    also have "... = N * 9 + 1897 * H ^ 4 * N ^ 3"
      by algebra
    also have "... \<le> 9 * N ^ 3 + 1897 * H ^ 4 * N ^ 3"
      using linear_le_pow by simp
    also have "... \<le> 9 * H ^ 4 * N ^ 3 + 1897 * H ^ 4 * N ^ 3"
      using H_ge_3 by simp
    also have "... = 1906 * H ^ 4 * N ^ 3"
      by simp
    also have "... \<le> 1906 * H ^ 4 * N ^ 4"
      using pow_mono' by simp
    finally show ?thesis .
  qed

  have nlength_le_GN: "y \<le> N \<Longrightarrow> nlength y \<le> H ^ 4 * N ^ 4" for y
  proof -
    assume "y \<le> N "
    then have "nlength y \<le> N ^ 4"
      using nlength_le_n linear_le_pow H_ge_3 by (meson dual_order.trans zero_less_numeral)
    also have "... \<le> H ^ 4 * N ^ 4"
      using H_gr_2 by simp
    finally show ?thesis .
  qed

  have f: "13 * nlength H \<le> 13 * H ^ 4 * N ^ 4"
    using nlength_le_GN[of H] N_eq by simp
  have g: "15 * nlength n \<le> 15 * H ^ 4 * N ^ 4"
    using nlength_le_GN[OF n_le_N] by simp
  have h: "6 * nlength (2 * n + 3) \<le> 6 * H ^ 4 * N ^ 4"
    using nlength_le_GN le_N by simp
  have i: "10 * nlength m \<le> 10 * H ^ 4 * N ^ 4"
    using m_def nlength_le_GN le_N by simp
  have j: "3 * nlength (Suc m) \<le> 3 * H ^ 4 * N ^ 4"
    using m_def nlength_le_GN le_N by simp
  have k: "3 * max (nlength T') (nlength (Suc m)) \<le> 3 * H ^ 4 * N ^ 4"
  proof -
    have "nlength T' \<le> H ^ 4 * N ^ 4"
      using nlength_le_GN le_N by simp
    moreover have "nlength (Suc m) \<le> H ^ 4 * N ^ 4"
      using m_def nlength_le_GN le_N by simp
    ultimately show ?thesis
      by simp
  qed
  have l: "1875 * H ^ 4 \<le> 1875 * H ^ 4 * N ^ 4"
    using N_ge_1 by simp
  have m: "3 * nlength m' \<le> 3 * H ^ 4 * N ^ 4"
    using m'_def le_N le_refl nat_mult_le_cancel_disj nlength_le_GN by simp

  have "ttt31 \<le> 256 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 1928 * H ^ 4 * N ^ 4 +
      140675 * H ^ 4 * N ^ 4 + 60224 * H ^ 4 * N ^ 4 + 1906 * H ^ 4 * N ^ 4 + 1906 * H ^ 4 * N ^ 4 + 1900 * H ^ 4 * N ^ 4"
    using ttt31_def a b c d e m l k f h i g j by linarith
  also have "... = 256 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 208539 * H ^ 4 * N ^ 4"
    by simp
  also have "... \<le> 256 + (2 * d_polynomial p + 826) * (N + N) ^ 4 + 208539 * H ^ 4 * N ^ 4"
  proof -
    have "H \<le> N "
      using N_eq by simp
    then show ?thesis
      using le_N[of "m'"] m'_def by simp
  qed
  also have "... = 256 + (2 * d_polynomial p + 826) * (2 * N) ^ 4 + 208539 * H ^ 4 * N ^ 4"
    by algebra
  also have "... = 256 + (2 * d_polynomial p + 826) * 16 * N ^ 4 + 208539 * H ^ 4 * N ^ 4"
    by simp
  also have "... \<le> 256 + (2 * d_polynomial p + 826) * 16 * H ^ 4 * N ^ 4 + 208539 * H ^ 4 * N ^ 4"
    using H_ge_3 by simp
  also have "... = 256 + (32 * d_polynomial p + 13216) * H ^ 4 * N ^ 4 + 208539 * H ^ 4 * N ^ 4"
    by simp
  also have "... = 256 + (32 * d_polynomial p + 221755) * H ^ 4 * N ^ 4"
    by algebra
  also have "... \<le> 256 * H ^ 4 + (32 * d_polynomial p + 221755) * H ^ 4 * N ^ 4"
    using H_gr_2 by simp
  also have "... \<le> 256 * H ^ 4 * N ^ 4 + (32 * d_polynomial p + 221755) * H ^ 4 * N ^ 4"
    using N_ge_1 by simp
  also have "... = (32 * d_polynomial p + 222011) * H ^ 4 * N ^ 4"
    by algebra
  finally show ?thesis .
qed

lemma tm31 [transforms_intros]: "transforms tm31 tps0 ttt31 tps31"
  unfolding tm31_def
proof (tform transforms_intros: tm_PHI5)
  show "60 + 8 < length tps30"
    using lentpsF tps30_def k by (simp_all only: length_list_update)
  show "tps30 ! 1 = nlltape (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4)"
    using tps30_def k lentpsF by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have *: "2 * n + 2 * p n + 3 = Suc m"
    using m_def One_nat_def Suc_1 add_Suc_right numeral_3_eq_3 by presburger
  have "tps30 ! 60 = (\<lfloor>Suc m\<rfloor>\<^sub>N, 1)"
    using tps30_def k lentpsF by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps30 ! 60 = (\<lfloor>2 * n + 2 * p n + 3\<rfloor>\<^sub>N, 1)"
    using * by presburger
  have "tps30 ! 61 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps30_def k lentpsF by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps30 ! (60 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps30 ! 62 = tpsF ! 62"
    using tps30_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps30 ! (60 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsF k canrepr_0 by simp
  have "tps30 ! 63 = tpsF ! 63"
    using tps30_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps30 ! (60 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsF k by simp
  have "tps30 ! 64 = tpsF ! 64"
    using tps30_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps30 ! (60 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsF k by simp
  have "tps30 ! 65 = tpsF ! 65"
    using tps30_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps30 ! (60 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsF k by simp
  have "tps30 ! 66 = tpsF ! 66"
    using tps30_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps30 ! (60 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsF k by simp
  have "tps30 ! 67 = tpsF ! 67"
    using tps30_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps30 ! (60 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsF k by simp
  have "tps30 ! 68 = (\<lfloor>T' + Suc m\<rfloor>\<^sub>N, 1)"
    using tps30_def k lentpsF by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then have "tps30 ! (60 + 8) = (\<lfloor>Suc m + 1 * T'\<rfloor>\<^sub>N, 1)"
    by (metis add.commute add_One_commute nat_mult_1 numeral_plus_numeral semiring_norm(2) semiring_norm(4) semiring_norm(6) semiring_norm(7))
  then show "tps30 ! (60 + 8) = (\<lfloor>2 * n + 2 * p n + 3 + T'\<rfloor>\<^sub>N, 1)"
    using * nat_mult_1 by presburger
  have "tps31 = tps30
    [60 := (\<lfloor>Suc m + T'\<rfloor>\<^sub>N, 1),
     1 := nlltape
           (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
            formula_n \<Phi>\<^sub>5),
     60 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    unfolding tps31_def tps30_def by (simp only: list_update_swap list_update_overwrite)
  then show "tps31 = tps30
    [60 := (\<lfloor>2 * n + 2 * p n + 3 + T'\<rfloor>\<^sub>N, 1),
     1 := nlltape
           ((formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4) @
            formula_n \<Phi>\<^sub>5),
     60 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    using * by (metis append_eq_appendI)
  show "ttt31 = 256 + (2 * d_polynomial p + 826) * (H + m') ^ 4 + 3 * nlength m' + 13 * nlength H +
      5627 * H ^ 4 * (3 + nlength (3 * H + m' * H))\<^sup>2 + 1875 * H ^ 4 +
      15 * nlength n + 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * n * H))\<^sup>2 +
      Suc n * (9 + 1897 * (H ^ 4 * (nlength (1 + 2 * n))\<^sup>2)) + 6 * nlength (2 * n + 3) +
      10 * nlength m + Suc (p n) * (9 + 1897 * (H ^ 4 * (nlength (Suc m))\<^sup>2)) +
      3 * nlength (Suc m) + 3 * max (nlength T') (nlength (Suc m)) +
      Suc T' * (9 + 1891 * (H ^ 4 * (nlength (2 * n + 2 * p n + 3 + T'))\<^sup>2))"
    using ttt31_def m_def One_nat_def Suc_1 add_Suc_right numeral_3_eq_3 by presburger
qed

definition "tpsG \<equiv> tpsF
  [61 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m\<rfloor>\<^sub>N, 1),
   68 := (\<lfloor>T' + Suc m\<rfloor>\<^sub>N, 1),
   60 := (\<lfloor>Suc m + T'\<rfloor>\<^sub>N, 1),
   60 + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tpsG: "68 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsG ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsG_def tpsF by simp

lemma lentpsG: "length tpsG = 110"
  using lentpsF tpsG_def by simp

lemma tps31: "tps31 = tpsG
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5)]"
  unfolding tps31_def tpsG_def by (simp only: list_update_swap)

definition "tps32 \<equiv> tpsG
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
         (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
          formula_n \<Phi>\<^sub>5),
   69 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"

lemma tm32 [transforms_intros]:
  assumes "ttt = ttt31 + 14"
  shows "transforms tm32 tps0 ttt tps32"
  unfolding tm32_def
proof (tform)
  show "69 < length tps31"
    using lentpsF tps31_def k by (simp_all only: length_list_update)
  have "tps31 ! 69 = tpsF ! 69"
    using tps31_def by (simp only: nth_list_update_neq)
  then show "tps31 ! 69 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsF k canrepr_0 by simp
  show "tps32 = tps31[69 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"
    unfolding tps32_def tps31 by (simp only:)
  show "ttt = ttt31 + (10 + 2 * nlength 0 + 2 * nlength 2)"
    using assms nlength_2 by simp
qed

definition "tps33 \<equiv> tpsG
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
         (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
          formula_n \<Phi>\<^sub>5),
   69 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   70 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm33 [transforms_intros]:
  assumes "ttt = ttt31 + 24 + 2 * nlength H"
  shows "transforms tm33 tps0 ttt tps33"
  unfolding tm33_def
proof (tform)
  show "70 < length tps32"
    using lentpsG tps32_def k by (simp_all only: length_list_update)
  have "tps32 ! 70 = tpsG ! 70"
    using tps32_def by (simp only: nth_list_update_neq)
  then show "tps32 ! 70 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsG k canrepr_0 by simp
  show "tps33 = tps32[70 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps33_def tps32_def by (simp only:)
  show "ttt = ttt31 + 14 + (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps34 \<equiv> tpsG
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
         (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
          formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6),
   69 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   70 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   0 := (\<lfloor>xs\<rfloor>, Suc n),
   69 := (\<lfloor>2 + 2 * n\<rfloor>\<^sub>N, 1)]"

lemma tm34 [transforms_intros]:
  assumes "ttt = ttt31 + 24 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1)"
  shows "transforms tm34 tps0 ttt tps34"
  unfolding tm34_def
proof (tform)
  show "69 + 7 < length tps33"
    using lentpsG tps33_def k by (simp_all only: length_list_update)
  let ?nss = "(formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @
   formula_n \<Phi>\<^sub>4 @ formula_n \<Phi>\<^sub>5)"
  show "tps33 ! 1 = nlltape ?nss"
    using tps33_def k lentpsG by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps33 ! 0 = tps1 ! 0"
    unfolding tps33_def tpsG_def tpsF_def tpsE_def tpsD_def tpsC_def tpsB_def tpsA_def
    by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps33 ! 0 = (\<lfloor>xs\<rfloor>, 1)"
    using tps1' by simp
  show "tps33 ! 69 = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    using tps33_def k lentpsG by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps33 ! 70 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps33_def k lentpsG by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps33 ! (69 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps33 ! 71 = tpsG ! 71"
    using tps33_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps33 ! (69 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsG k canrepr_0 by simp
  have "tps33 ! 72 = tpsG ! 72"
    using tps33_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps33 ! (69 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsG k by simp
  have "tps33 ! 73 = tpsG ! 73"
    using tps33_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps33 ! (69 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsG k by simp
  have "tps33 ! 74 = tpsG ! 74"
    using tps33_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps33 ! (69 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsG k by simp
  have "tps33 ! 75 = tpsG ! 75"
    using tps33_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps33 ! (69 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsG k by simp
  have "tps33 ! 76 = tpsG ! 76"
    using tps33_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps33 ! (69 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsG k by simp
  show "tps34 = tps33
    [0 := (\<lfloor>xs\<rfloor>, Suc n),
     69 := (\<lfloor>2 + 2 * n\<rfloor>\<^sub>N, 1),
     1 := nlltape (?nss @ formula_n \<Phi>\<^sub>6)]"
    unfolding tps34_def tps33_def by (simp only: list_update_swap list_update_overwrite append_assoc)
  show "ttt = ttt31 + 24 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1)"
    using assms by simp
qed

definition "tpsH \<equiv> tpsG
  [69 := (\<lfloor>2\<rfloor>\<^sub>N, 1),
   70 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   0 := (\<lfloor>xs\<rfloor>, Suc n),
   69 := (\<lfloor>2 + 2 * n\<rfloor>\<^sub>N, 1)]"

lemma tpsH: "76 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsH ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsH_def tpsG by simp

lemma lentpsH: "length tpsH = 110"
  using lentpsG tpsH_def by simp

lemma tps34: "tps34 = tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6)]"
  unfolding tps34_def tpsH_def by (simp only: list_update_swap)

definition "tps35 \<equiv> tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6),
   77 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"

lemma tm35 [transforms_intros]:
  assumes "ttt = ttt31 + 38 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 3 * nlength n"
  shows "transforms tm35 tps0 ttt tps35"
  unfolding tm35_def
proof (tform)
  show "11 < length tps34" "77 < length tps34"
    using lentpsH tps34 k by (simp_all only: length_list_update)
  show "tps34 ! 11 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps34 k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps34 ! 77 = tpsH ! 77"
    using tps34 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps34 ! 77 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsH k canrepr_0 by simp
  show "tps35 = tps34[77 := (\<lfloor>n\<rfloor>\<^sub>N, 1)]"
    unfolding tps35_def tps34 by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt31 + 24 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) +
      (14 + 3 * (nlength n + nlength 0))"
    using assms by simp
qed

definition "tps36 \<equiv> tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6),
   77 := (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)]"

lemma tm36 [transforms_intros]:
  assumes "ttt = ttt31 + 43 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n"
  shows "transforms tm36 tps0 ttt tps36"
  unfolding tm36_def
proof (tform time: assms)
  show "77 < length tps35"
    using lentpsH tps35_def k by (simp_all only: length_list_update)
  show "tps35 ! 77 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps35_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps36 = tps35[77 := (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)]"
    unfolding tps36_def tps35_def by (simp only: list_update_swap[of 77] list_update_overwrite)
qed

definition "tps37 \<equiv> tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6),
   77 := (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1)]"

lemma tm37 [transforms_intros]:
  assumes "ttt = ttt31 + 63 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4)"
  shows "transforms tm37 tps0 ttt tps37"
  unfolding tm37_def
proof (tform)
  show "77 < length tps36"
    using lentpsH tps36_def k by (simp_all only: length_list_update)
  show "tps36 ! 77 = (\<lfloor>2 * n\<rfloor>\<^sub>N, 1)"
    using tps36_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps37 = tps36[77 := (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1)]"
    unfolding tps37_def tps36_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt31 + 43 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) +
      5 * nlength n + 4 * (5 + 2 * nlength (2 * n + 4))"
    using assms by simp
qed

definition "tps38 \<equiv> tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6),
   77 := (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1),
   78 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm38 [transforms_intros]:
  assumes "ttt = ttt31 + 73 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) +
    5 * nlength n + 8 * nlength (2 * n + 4) + 2 * nlength H"
  shows "transforms tm38 tps0 ttt tps38"
  unfolding tm38_def
proof (tform)
  show "78 < length tps37"
    using lentpsH tps37_def k by (simp_all only: length_list_update)
  have "tps37 ! 78 = tpsH ! 78"
    using tps37_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps37 ! 78 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsH k canrepr_0 by simp
  show "tps38 = tps37[78 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps38_def tps37_def by (simp only: list_update_swap)
  show "ttt = ttt31 + 63 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) +
      5 * nlength n + 8 * nlength (2 * n + 4) + (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps39 \<equiv> tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6),
   77 := (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1),
   78 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   83 := (\<lfloor>p n\<rfloor>\<^sub>N, 1)]"

lemma tm39 [transforms_intros]:
  assumes "ttt = ttt31 + 87 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n)"
  shows "transforms tm39 tps0 ttt tps39"
  unfolding tm39_def
proof (tform)
  show "15 < length tps38" "83 < length tps38"
    using lentpsH tps38_def k by (simp_all only: length_list_update)
  show "tps38 ! 15 = (\<lfloor>p n\<rfloor>\<^sub>N, 1)"
    using tps38_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps38 ! 83 = tpsH ! 83"
    using tps38_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps38 ! 83 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsH k canrepr_0 by simp
  show "tps39 = tps38[83 := (\<lfloor>p n\<rfloor>\<^sub>N, 1)]"
    unfolding tps39_def tps38_def by (simp only: list_update_swap)
  show "ttt = ttt31 + 73 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + (14 + 3 * (nlength (p n) + nlength 0))"
    using assms by simp
qed

definition "tps40 \<equiv> tpsH
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   77 := (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1),
   78 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   83 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   77 := (\<lfloor>2 * n + 4 + 2 * p n\<rfloor>\<^sub>N, 1),
   77 + 6 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm40 [transforms_intros]:
  assumes "ttt = ttt31 + 88 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2"
  shows "transforms tm40 tps0 ttt tps40"
  unfolding tm40_def
proof (tform)
  show "77 + 6 < length tps39"
    using lentpsH tps39_def k by (simp_all only: length_list_update)
  let ?nss = "formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
      formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6"
  show "tps39 ! 1 = nlltape ?nss"
    using tps39_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps39 ! 77 = (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1)"
    using tps39_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps39 ! 78 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps39_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps39 ! (77 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps39 ! 79 = tpsH ! 79"
    using tps39_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps39 ! (77 + 2) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsH k by simp
  have "tps39 ! 80 = tpsH ! 80"
    using tps39_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps39 ! (77 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsH k by simp
  have "tps39 ! 81 = tpsH ! 81"
    using tps39_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps39 ! (77 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsH k by simp
  have "tps39 ! 82 = tpsH ! 82"
    using tps39_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps39 ! (77 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsH k by simp
  have "tps39 ! 83 = (\<lfloor>p n\<rfloor>\<^sub>N, 1)"
    using tps39_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps39 ! (77 + 6) = (\<lfloor>p n\<rfloor>\<^sub>N, 1)"
    by simp
  show "tps40 = tps39
    [77 := (\<lfloor>2 * n + 4 + 2 * p n\<rfloor>\<^sub>N, 1),
     77 + 6 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     1 := nlltape (?nss @ formula_n \<Phi>\<^sub>7)]"
    unfolding tps40_def tps39_def by (simp only: list_update_swap list_update_overwrite append_assoc)
  show "ttt = ttt31 + 87 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      (p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 1)"
    using assms by simp
qed

definition "tpsI \<equiv> tpsH
  [77 := (\<lfloor>2 * n + 4\<rfloor>\<^sub>N, 1),
   78 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   83 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   77 := (\<lfloor>2 * n + 4 + 2 * p n\<rfloor>\<^sub>N, 1),
   77 + 6 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tpsI: "83 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsI ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsI_def tpsH by simp

lemma lentpsI: "length tpsI = 110"
  using lentpsH tpsI_def by simp

lemma tps40: "tps40 = tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7)]"
  unfolding tps40_def tpsI_def by (simp only: list_update_swap)

definition "tps41 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   84 := (\<lfloor>m'\<rfloor>\<^sub>N, 1)]"

lemma tm41 [transforms_intros]:
  assumes "ttt = ttt31 + 102 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 +
    3 * nlength m'"
  shows "transforms tm41 tps0 ttt tps41"
  unfolding tm41_def
proof (tform)
  show "18 < length tps40" "84 < length tps40"
    using lentpsI tps40 k by (simp_all only: length_list_update)
  show "tps40 ! 18 = (\<lfloor>m'\<rfloor>\<^sub>N, 1)"
    using tps40_def k lentpsH by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps40 ! 84 = tpsI ! 84"
    using tps40 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps40 ! 84 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsI k canrepr_0 by simp
  show "tps41 = tps40[84 := (\<lfloor>m'\<rfloor>\<^sub>N, 1)]"
    unfolding tps41_def tps40 by (simp only: list_update_swap)
  show "ttt = ttt31 + 88 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 +
      (14 + 3 * (nlength m' + nlength 0))"
    using assms by simp
qed

definition "tps42 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   84 := (\<lfloor>T' + m'\<rfloor>\<^sub>N, 1)]"

lemma tm42 [transforms_intros]:
  assumes "ttt = ttt31 + 112 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
    3 * max (nlength T') (nlength m')"
  shows "transforms tm42 tps0 ttt tps42"
  unfolding tm42_def
proof (tform)
  show "17 < length tps41" "84 < length tps41"
    using lentpsI tps41_def k by (simp_all only: length_list_update)
  show "tps41 ! 17 = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    using tps41_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps41 ! 84 = (\<lfloor>m'\<rfloor>\<^sub>N, 1)"
    using tps41_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps42 = tps41[84 := (\<lfloor>T' + m'\<rfloor>\<^sub>N, 1)]"
    unfolding tps42_def tps41_def by (simp only: list_update_overwrite)
  show "ttt = ttt31 + 102 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 +
      3 * nlength m' + (3 * max (nlength T') (nlength m') + 10)"
    using assms by simp
qed

definition "tps43 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   84 := (\<lfloor>2 * T' + m'\<rfloor>\<^sub>N, 1)]"

lemma tm43 [transforms_intros]:
  assumes "ttt = ttt31 + 122 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
    3 * max (nlength T') (nlength m') +
    3 * max (nlength T') (nlength (T' + m'))"
  shows "transforms tm43 tps0 ttt tps43"
  unfolding tm43_def
proof (tform)
  show "17 < length tps42" "84 < length tps42"
    using lentpsI tps42_def k by (simp_all only: length_list_update)
  show "tps42 ! 17 = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    using tps42_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps42 ! 84 = (\<lfloor>T' + m'\<rfloor>\<^sub>N, 1)"
    using tps42_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps43 = tps42[84 := (\<lfloor>2 * T' + m'\<rfloor>\<^sub>N, 1)]"
    unfolding tps43_def tps42_def by (simp only: list_update_overwrite)
  then show "tps43 = tps42[84 := (\<lfloor>T' + (T' + m')\<rfloor>\<^sub>N, 1)]"
    by (simp add: left_add_twice)
  show "ttt = ttt31 + 112 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
      3 * max (nlength T') (nlength m') +
      (3 * max (nlength T') (nlength (T' + m')) + 10)"
    using assms by simp
qed

definition "tps44 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   84 := (\<lfloor>3 * T' + m'\<rfloor>\<^sub>N, 1)]"

lemma tm44 [transforms_intros]:
  assumes "ttt = ttt31 + 132 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
    3 * max (nlength T') (nlength m') +
    3 * max (nlength T') (nlength (T' + m')) +
    3 * max (nlength T') (nlength (2 * T' + m'))"
  shows "transforms tm44 tps0 ttt tps44"
  unfolding tm44_def
proof (tform)
  show "17 < length tps43" "84 < length tps43"
    using lentpsI tps43_def k by (simp_all only: length_list_update)
  show "tps43 ! 17 = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    using tps43_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps43 ! 84 = (\<lfloor>2 * T' + m'\<rfloor>\<^sub>N, 1)"
    using tps43_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps44 = tps43[84 := (\<lfloor>3 * T' + m'\<rfloor>\<^sub>N, 1)]"
    unfolding tps44_def tps43_def by (simp only: list_update_overwrite)
  then show "tps44 = tps43[84 := (\<lfloor>T' + (2 * T' + m')\<rfloor>\<^sub>N, 1)]"
    by (simp add: left_add_twice)
  show "ttt = ttt31 + 122 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
      3 * max (nlength T') (nlength m') +
      3 * max (nlength T') (nlength (T' + m')) +
      (3 * max (nlength T') (nlength (2 * T' + m')) + 10)"
    using assms by simp
qed

definition "tps45 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   84 := (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1)]"

lemma tm45 [transforms_intros]:
  assumes "ttt = ttt31 + 137 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
    3 * max (nlength T') (nlength m') +
    3 * max (nlength T') (nlength (T' + m')) +
    3 * max (nlength T') (nlength (2 * T' + m')) +
    2 * nlength (3 * T' + m')"
  shows "transforms tm45 tps0 ttt tps45"
  unfolding tm45_def
proof (tform)
  show "84 < length tps44"
    using lentpsI tps44_def k by (simp_all only: length_list_update)
  show "tps44 ! 84 = (\<lfloor>3 * T' + m'\<rfloor>\<^sub>N, 1)"
    using tps44_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps45 = tps44[84 := (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1)]"
    unfolding tps45_def tps44_def by (simp only: list_update_overwrite)
  then show "tps45 = tps44[84 := (\<lfloor>Suc (3 * T' + m')\<rfloor>\<^sub>N, 1)]"
    by simp
  show "ttt = ttt31 + 132 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
      3 * max (nlength T') (nlength m') +
      3 * max (nlength T') (nlength (T' + m')) +
      3 * max (nlength T') (nlength (2 * T' + m')) +
      (5 + 2 * nlength (3 * T' + m'))"
    using assms by simp
qed

definition "tps46 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7),
   84 := (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1),
   85 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm46 [transforms_intros]:
  assumes "ttt = ttt31 + 147 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
    8 * nlength (2 * n + 4) + 4 * nlength H + 3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
    3 * max (nlength T') (nlength m') +
    3 * max (nlength T') (nlength (T' + m')) +
    3 * max (nlength T') (nlength (2 * T' + m')) +
    2 * nlength (3 * T' + m')"
  shows "transforms tm46 tps0 ttt tps46"
  unfolding tm46_def
proof (tform)
  show "85 < length tps45"
    using lentpsI tps45_def k by (simp_all only: length_list_update)
  have "tps45 ! 85 = tpsI ! 85"
    using tps45_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps45 ! 85 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsI k canrepr_0 by simp
  show "tps46 = tps45[85 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps46_def tps45_def by (simp only:)
  show "ttt = ttt31 + 137 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 2 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
      3 * max (nlength T') (nlength m') +
      3 * max (nlength T') (nlength (T' + m')) +
      3 * max (nlength T') (nlength (2 * T' + m')) +
      2 * nlength (3 * T' + m') +
      (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps47 \<equiv> tpsI
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   84 := (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1),
   85 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   84 + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   84 + 6 := (\<lfloor>formula_n \<Phi>\<^sub>8\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

definition "ttt47 \<equiv> ttt31 + 166 +
    6 * nlength H +
    133650 * H ^ 6 * n ^ 3 +
    5 * nlength n +
    8 * nlength (2 * n + 4) +
    3 * nlength (p n) +
    p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 +
    3 * nlength m' +
    3 * max (nlength T') (nlength m') +
    3 * max (nlength T') (nlength (T' + m')) +
    3 * max (nlength T') (nlength (2 * T' + m')) +
    2 * nlength (3 * T' + m') +
    1861 * H ^ 4 * (nlength (Suc (1 + 3 * T' + m')))\<^sup>2"

lemma ttt47: "ttt47 \<le> (32 * d_polynomial p + 364343) * H ^ 6 * N ^ 4"
proof -
  have nlength_le_GN: "y \<le> N \<Longrightarrow> nlength y \<le> H ^ 6 * N ^ 3" for y
  proof -
    assume "y \<le> N "
    then have "nlength y \<le> N ^ 3"
      using nlength_le_n linear_le_pow H_ge_3 by (meson dual_order.trans zero_less_numeral)
    also have "... \<le> H ^ 6 * N ^ 3"
      using H_gr_2 by simp
    finally show ?thesis .
  qed

  have h: "6 * nlength H \<le> 6 * H ^ 6 * N ^ 3"
    using nlength_le_GN[OF H_le_N] by simp
  have i: "5 * nlength n \<le> 5 * H ^ 6 * N ^ 3"
    using nlength_le_GN[OF n_le_N] by simp
  have j: "8 * nlength (2 * n + 4) \<le> 8 * H ^ 6 * N ^ 3"
  proof -
    have "2 * n + 4 \<le> 2 * n + H * 3"
      using H_ge_3 by simp
    also have "... \<le> H * 2 * n + H * 3"
      using H_ge_3 by simp
    also have "... = H * (2 * n + 3)"
      by algebra
    also have "... \<le> N "
      using N_eq by simp
    finally have "2 * n + 4 \<le> N " .
    then have "8 * nlength (2 * n + 4) \<le> 8 * nlength N"
      using nlength_mono by simp
    also have "... \<le> 8 * N "
      using nlength_le_n by simp
    also have "... \<le> 8 * H ^ 6 * N "
      using H_ge_3 by simp
    also have "... \<le> 8 * H ^ 6 * N ^ 3"
      using linear_le_pow by simp
    finally show ?thesis .
  qed
  have k: "3 * nlength (p n) \<le> 3 * H ^ 6 * N ^ 3"
    using nlength_le_GN[OF le_N] by simp
  have l: "3 * nlength m' \<le> 3 * H ^ 6 * N ^ 3"
    using nlength_le_GN[OF le_N] m'_def by simp
  have g: "3 * max (nlength T') (nlength m') \<le> 3 * H ^ 6 * N ^ 3"
  proof -
    have "m' \<le> N "
      using le_N m'_def by simp
    moreover have "T' \<le> N "
      using le_N by simp
    ultimately have "max (nlength T') (nlength m') \<le> nlength N"
      using max_nlength nlength_mono by simp
    then have "3 * max (nlength T') (nlength m') \<le> 3 * N "
      using nlength_le_n by (meson le_trans mult_le_mono2)
    also have "... \<le> 3 * H ^ 6 * N "
      using H_ge_3 by simp
    also have "... \<le> 3 * H ^ 6 * N ^ 3"
      using linear_le_pow by simp
    finally show ?thesis .
  qed
  have f: "3 * max (nlength T') (nlength (T' + m')) \<le> 6 * H ^ 6 * N ^ 3"
  proof -
    have "T' + m' \<le> N + N "
      using N_eq m'_def H_gr_2 add_le_mono le_N less_or_eq_imp_le mult_le_mono trans_le_add2
      by presburger
    then have "T' + m' \<le> 2 * N "
      by simp
    moreover have "T' \<le> N "
      using le_N by simp
    ultimately have "max (nlength T') (nlength (T' + m')) \<le> nlength (2 * N)"
      using max_nlength nlength_mono by simp
    then have "3 * max (nlength T') (nlength (T' + m')) \<le> 3 * (2 * N)"
      using nlength_le_n by (meson le_trans mult_le_mono2)
    also have "... = 6 * N "
      by simp
    also have "... \<le> 6 * H ^ 6 * N "
      using H_ge_3 by simp
    also have "... \<le> 6 * H ^ 6 * N ^ 3"
      using linear_le_pow by simp
    finally show ?thesis .
  qed
  have e: "3 * max (nlength T') (nlength (2 * T' + m')) \<le> 6 * H ^ 6 * N ^ 3"
  proof -
    have "2 * T' + m' \<le> N + N "
      using N_eq m'_def H_gr_2 add_le_mono le_N less_or_eq_imp_le mult_le_mono trans_le_add2
      by presburger
    then have "2 * T' + m' \<le> 2 * N "
      by simp
    moreover have "T' \<le> N "
      using le_N by simp
    ultimately have "max (nlength T') (nlength (2 * T' + m')) \<le> nlength (2 * N)"
      using max_nlength nlength_mono by simp
    then have "3 * max (nlength T') (nlength (2 * T' + m')) \<le> 3 * (2 * N)"
      using nlength_le_n by (meson le_trans mult_le_mono2)
    also have "... = 6 * N "
      by simp
    also have "... \<le> 6 * H ^ 6 * N "
      using H_ge_3 by simp
    also have "... \<le> 6 * H ^ 6 * N ^ 3"
      using linear_le_pow by simp
    finally show ?thesis .
  qed
  have d: "2 * nlength (3 * T' + m') \<le> 4 * H ^ 6 * N ^ 3"
  proof -
    have "3 * T' + m' \<le> N + N "
      using N_eq H_ge_3 m'_def by (metis add_leE add_le_mono le_N le_refl mult_le_mono)
    then have "3 * T' + m' \<le> 2 * N "
      by simp
    then have "nlength (3 * T' + m') \<le> 2 * N "
      using nlength_le_n le_trans by blast
    then have "2 * nlength (3 * T' + m') \<le> 4 * N "
      by simp
    also have "... \<le> 4 * H ^ 6 * N "
      using H_ge_3 by simp
    also have "... \<le> 4 * H ^ 6 * N ^ 3"
      using linear_le_pow by simp
    finally show ?thesis .
  qed
  have c: "6 * nlength H \<le> 6 * H ^ 6 * N ^ 3"
  proof -
    have "6 * nlength H \<le> 6 * H"
      using nlength_le_n by simp
    also have "... \<le> 6 * H ^ 6"
      using linear_le_pow by simp
    also have "... \<le> 6 * H ^ 6 * N ^ 3"
      using N_ge_1 by simp
    finally show ?thesis .
  qed
  have a: "p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 \<le> 1028 * H ^ 6 * N ^ 3"
  proof -
    have "nlength (2 * n + 4 + 2 * p n) = nlength (2 * (n + 2 + p n))"
      by (metis distrib_left_numeral mult_2_right numeral_Bit0)
    also have "... \<le> Suc (nlength (n + 2 + p n))"
      using nlength_times2 by blast
    also have "... \<le> Suc (n + 2 + p n)"
      by (simp add: nlength_le_n)
    also have "... \<le> N "
      using le_N by simp
    finally have "nlength (2 * n + 4 + 2 * p n) \<le> N " .
    then have "(nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 \<le> (N + nlength H) ^ 2"
      by simp
    also have "... \<le> (N + N) ^ 2"
      using H_le_N nlength_le_n by (meson add_left_mono le_trans power2_nat_le_eq_le)
    also have "... = (2 * N) ^ 2"
      by algebra
    also have "... = 4 * N ^ 2"
      by simp
    finally have "(nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 \<le> 4 * N ^ 2" .
    then have "p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 \<le> p n * 257 * H * (4 * N ^ 2)"
      by simp
    also have "... \<le> N * 257 * H * (4 * N ^ 2)"
      using le_N by simp
    also have "... = 1028 * H * N ^ 3"
      by algebra
    also have "... \<le> 1028 * H ^ 6 * N ^ 3"
      using linear_le_pow by simp
    finally show ?thesis .
  qed
  have b: "1861 * H ^ 4 * (nlength (Suc (1 + 3 * T' + m')))\<^sup>2 \<le> 7444 * H ^ 6 * N ^ 3"
  proof -
    have "Suc (1 + 3 * T' + m') \<le> 3 * (2 * n + 2 * p n + 3 + T') + m' "
      by simp
    also have "... \<le> N + N "
      using N_eq H_ge_3 m'_def add_le_mono le_N le_refl mult_le_mono1 by presburger
    also have "... \<le> 2 * N "
      by simp
    finally have "Suc (1 + 3 * T' + m') \<le> 2 * N " .
    then have "nlength (Suc (1 + 3 * T' + m')) \<le> 2 * N "
      using nlength_le_n le_trans by blast
    then have "(nlength (Suc (1 + 3 * T' + m'))) ^ 2 \<le> (2 * N) ^ 2"
      using power2_nat_le_eq_le by presburger
    then have "(nlength (Suc (1 + 3 * T' + m'))) ^ 2 \<le> 4 * N ^ 2"
      by simp
    then have "1861 * H ^ 4 * (nlength (Suc (1 + 3 * T' + m')))\<^sup>2 \<le> 1861 * H ^ 4 * (4 * N ^ 2)"
      by simp
    also have "... = 7444 * H ^ 4 * N ^ 2"
      by simp
    also have "... \<le> 7444 * H ^ 6 * N ^ 2"
      using pow_mono' by simp
    also have "... \<le> 7444 * H ^ 6 * N ^ 3"
      using pow_mono' by simp
    finally show ?thesis .
  qed
  have m: "133650 * H ^ 6 * n ^ 3 \<le> 133650 * H ^ 6 * N ^ 3"
    using n_le_N by simp

  have "ttt47 \<le> ttt31 + 166 +
      6 * H ^ 6 * N ^ 3 + 133650 * H ^ 6 * N ^ 3 + 5 * H ^ 6 * N ^ 3 +
      8 * H ^ 6 * N ^ 3 + 3 * H ^ 6 * N ^ 3 + 1028 * H ^ 6 * N ^ 3 +
      3 * H ^ 6 * N ^ 3 + 3 * H ^ 6 * N ^ 3 + 6 * H ^ 6 * N ^ 3 +
      6 * H ^ 6 * N ^ 3 + 4 * H ^ 6 * N ^ 3 + 7444 * H ^ 6 * N ^ 3"
    using ttt47_def a b c d e f g h i j k l m by linarith
  also have "... = ttt31 + 166 + 142166 * H ^ 6 * N ^ 3"
    by simp
  also have "... \<le> ttt31 + 166 * H ^ 6 + 142166 * H ^ 6 * N ^ 3"
    using H_ge_3 by simp
  also have "... \<le> ttt31 + 166 * H ^ 6 * N ^ 3 + 142166 * H ^ 6 * N ^ 3"
    using N_ge_1 by simp
  also have "... = ttt31 + 142332 * H ^ 6 * N ^ 3"
    by simp
  also have "... \<le> ttt31 + 142332 * H ^ 6 * N ^ 4"
    using pow_mono' by simp
  also have "... \<le> (32 * d_polynomial p + 222011) * H ^ 4 * N ^ 4 + 142332 * H ^ 6 * N ^ 4"
    using ttt31 by simp
  also have "... \<le> (32 * d_polynomial p + 222011) * H ^ 6 * N ^ 4 + 142332 * H ^ 6 * N ^ 4"
    using pow_mono' by simp
  also have "... = (32 * d_polynomial p + 364343) * H ^ 6 * N ^ 4"
    by algebra
  finally show ?thesis .
qed

lemma tm47 [transforms_intros]: "transforms tm47 tps0 ttt47 tps47"
  unfolding tm47_def
proof (tform)
  show "84 + 7 < length tps46"
    using lentpsI tps46_def k by (simp_all only: length_list_update)
  let ?nss = "formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7"
  show "tps46 ! 1 = nlltape ?nss"
    using tps46_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps46 ! 84 = (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1)"
    using tps46_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps46 ! 85 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps46_def k lentpsI by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps46 ! (84 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps46 ! 86 = tpsI ! 86"
    using tps46_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps46 ! (84 + 2) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsI k by simp
  have "tps46 ! 87 = tpsI ! 87"
    using tps46_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps46 ! (84 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsI k by simp
  have "tps46 ! 88 = tpsI ! 88"
    using tps46_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps46 ! (84 + 4) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsI k by simp
  have "tps46 ! 89 = tpsI ! 89"
    using tps46_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps46 ! (84 + 5) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsI k by simp
  have "tps46 ! 90 = tpsI ! 90"
    using tps46_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps46 ! (84 + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsI k by simp
  have "tps46 ! 91 = tpsI ! 91"
    using tps46_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps46 ! (84 + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsI k by simp
  show "tps47 = tps46
      [1 := nlltape (?nss @ formula_n \<Phi>\<^sub>8),
       84 + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
       84 + 6 := (\<lfloor>formula_n \<Phi>\<^sub>8\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
    unfolding tps47_def tps46_def by (simp only: list_update_swap list_update_overwrite append_assoc)
  show "ttt47 = ttt31 + 147 + 2 * nlength H + (133650 * H ^ 6 * n ^ 3 + 1) + 5 * nlength n +
      8 * nlength (2 * n + 4) + 4 * nlength H + 3 * nlength (p n) +
      p n * 257 * H * (nlength (2 * n + 4 + 2 * p n) + nlength H)\<^sup>2 + 3 * nlength m' +
      3 * max (nlength T') (nlength m') +
      3 * max (nlength T') (nlength (T' + m')) +
      3 * max (nlength T') (nlength (2 * T' + m')) +
      2 * nlength (3 * T' + m') +
      (18 + 1861 * H ^ 4 * (nlength (Suc (1 + 3 * T' + m')))\<^sup>2)"
    using ttt47_def by simp
qed

definition "tpsJ \<equiv> tpsI
  [84 := (\<lfloor>1 + 3 * T' + m'\<rfloor>\<^sub>N, 1),
   85 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   84 + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   84 + 6 := (\<lfloor>formula_n \<Phi>\<^sub>8\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tpsJ: "90 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsJ ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsJ_def tpsI by simp

lemma lentpsJ: "length tpsJ = 110"
  using lentpsI tpsJ_def by simp

lemma tps47: "tps47 = tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8)]"
  unfolding tps47_def tpsJ_def by (simp only: list_update_swap)

definition "tps48 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1)]"

lemma tm48 [transforms_intros]:
  assumes "ttt = ttt47 + 14 + 3 * nlength N"
  shows "transforms tm48 tps0 ttt tps48"
  unfolding tm48_def
proof (tform)
  show "20 < length tps47" "91 < length tps47"
    using lentpsJ tps47 k by (simp_all only: length_list_update)
  have "tps47 ! 20 = (\<lfloor>m' * H\<rfloor>\<^sub>N, 1)"
    using tps47 k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps47 ! 20 = (\<lfloor>N\<rfloor>\<^sub>N, 1)"
    using m' by simp
  have "tps47 ! 91 = tpsJ ! 91"
    using tps47 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps47 ! 91 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsJ k canrepr_0 by simp
  show "tps48 = tps47[91 := (\<lfloor>N\<rfloor>\<^sub>N, 1)]"
    unfolding tps48_def tps47 by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt47 + (14 + 3 * (nlength N + nlength 0))"
    using assms by simp
qed

definition "tps49 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm49 [transforms_intros]:
  assumes "ttt = ttt47 + 24 + 3 * nlength N + 2 * nlength H"
  shows "transforms tm49 tps0 ttt tps49"
  unfolding tm49_def
proof (tform)
  show "92 < length tps48"
    using lentpsJ tps48_def k by (simp_all only: length_list_update)
  have "tps48 ! 92 = tpsJ ! 92"
    using tps48_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps48 ! 92 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsJ k canrepr_0 by simp
  show "tps49 = tps48[92 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"
    unfolding tps49_def tps48_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt47 + 14 + 3 * nlength N + (10 + 2 * nlength 0 + 2 * nlength H)"
    using assms by simp
qed

definition "tps50 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1)]"

lemma tm50 [transforms_intros]:
  assumes "ttt = ttt47 + 34 + 3 * nlength N + 2 * nlength H + 2 * nlength Z"
  shows "transforms tm50 tps0 ttt tps50"
  unfolding tm50_def
proof (tform)
  show "93 < length tps49"
    using lentpsJ tps49_def k by (simp_all only: length_list_update)
  have "tps49 ! 93 = tpsJ ! 93"
    using tps49_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps49 ! 93 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsJ k canrepr_0 by simp
  show "tps50 = tps49[93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1)]"
    unfolding tps50_def tps49_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt47 + 24 + 3 * nlength N + 2 * nlength H + (10 + 2 * nlength 0 + 2 * nlength Z)"
    using assms by simp
qed

definition "tps51 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1),
   94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1)]"

lemma tm51 [transforms_intros]:
  assumes "ttt = ttt47 + 48 + 3 * nlength N + 2 * nlength H + 2 * nlength Z + 3 * nlength T'"
  shows "transforms tm51 tps0 ttt tps51"
  unfolding tm51_def
proof (tform)
  show "17 < length tps50" "94 < length tps50"
    using lentpsJ tps50_def k by (simp_all only: length_list_update)
  show "tps50 ! 17 = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    using tps50_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps50 ! 94 = tpsJ ! 94"
    using tps50_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps50 ! 94 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsJ k canrepr_0 by simp
  show "tps51 = tps50[94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1)]"
    unfolding tps51_def tps50_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt47 + 34 + 3 * nlength N + 2 * nlength H + 2 * nlength Z +
      (14 + 3 * (nlength T' + nlength 0))"
    using assms by simp
qed

definition "tps52 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1),
   94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   95 := (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm52 [transforms_intros]:
  assumes "ttt = ttt47 + 58 + 3 * nlength N + 2 * nlength H + 2 * nlength Z +
    3 * nlength T' + 2 * nlllength (formula_n \<psi>)"
  shows "transforms tm52 tps0 ttt tps52"
  unfolding tm52_def
proof (tform)
  show "95 < length tps51"
    using lentpsJ tps51_def k by (simp_all only: length_list_update)
  have "tps51 ! 95 = tpsJ ! 95"
    using tps51_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then have *: "tps51 ! 95 = (\<lfloor>[]\<rfloor>, 1)"
    using tpsJ k by simp
  then show "tps51 ::: 95 = \<lfloor>[]\<rfloor>"
    by simp
  show "clean_tape (tps51 ! 95)"
    using * by simp
  show "proper_symbols []"
    by simp
  show "proper_symbols (numlistlist (formula_n \<psi>))"
    using proper_symbols_numlistlist by simp
  have "tps52 = tps51[95 := (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
    unfolding tps52_def tps51_def by (simp only: list_update_swap list_update_overwrite)
  then show "tps52 = tps51[95 := (\<lfloor>numlistlist (formula_n \<psi>)\<rfloor>, 1)]"
    using nllcontents_def by simp
  show "ttt = ttt47 + 48 + 3 * nlength N + 2 * nlength H + 2 * nlength Z +
      3 * nlength T' + (8 + tps51 :#: 95 + 2 * length [] +
      Suc (2 * length (numlistlist (formula_n \<psi>))))"
    using assms * nlllength_def by simp
qed

definition "tps53 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1),
   94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   95 := (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   96 := (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm53 [transforms_intros]:
  assumes "ttt = ttt47 + 68 + 3 * nlength N + 2 * nlength H + 2 * nlength Z + 3 * nlength T' +
    2 * nlllength (formula_n \<psi>) + 2 * length (numlistlist (formula_n \<psi>'))"
  shows "transforms tm53 tps0 ttt tps53"
  unfolding tm53_def
proof (tform)
  show "96 < length tps52"
    using lentpsJ tps52_def k by (simp_all only: length_list_update)
  have "tps52 ! 96 = tpsJ ! 96"
    using tps52_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then have *: "tps52 ! 96 = (\<lfloor>[]\<rfloor>, 1)"
    using tpsJ k by simp
  then show "tps52 ::: 96 = \<lfloor>[]\<rfloor>"
    by simp
  show "clean_tape (tps52 ! 96)"
    using * by simp
  show "proper_symbols []"
    by simp
  show "proper_symbols (numlistlist (formula_n \<psi>'))"
    using proper_symbols_numlistlist by simp
  have "tps53 = tps52[96 := (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
    unfolding tps53_def tps52_def by (simp only: list_update_swap list_update_overwrite)
  then show "tps53 = tps52[96 := (\<lfloor>numlistlist (formula_n \<psi>')\<rfloor>, 1)]"
    using nllcontents_def by simp
  show "ttt = ttt47 + 58 + 3 * nlength N + 2 * nlength H + 2 * nlength Z + 3 * nlength T' +
      2 * nlllength (formula_n \<psi>) +
      (8 + tps52 :#: 96 + 2 * length [] + Suc (2 * length (numlistlist (formula_n \<psi>'))))"
    using assms * nlllength_def by simp
qed

definition "tps54 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape
      (formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1),
   94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   95 := (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   96 := (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   97 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm54 [transforms_intros]:
  assumes "ttt = ttt47 + 80 + 3 * nlength N + 2 * nlength H + 2 * nlength Z + 3 * nlength T' +
    2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>')"
  shows "transforms tm54 tps0 ttt tps54"
  unfolding tm54_def
proof (tform)
  show "97 < length tps53"
    using lentpsJ tps53_def k by (simp_all only: length_list_update)
  have "tps53 ! 97 = tpsJ ! 97"
    using tps53_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then show "tps53 ! 97 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsJ k canrepr_0 by simp
  show "tps54 = tps53[97 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    unfolding tps54_def tps53_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt47 + 68 + 3 * nlength N + 2 * nlength H + 2 * nlength Z + 3 * nlength T' +
      2 * nlllength (formula_n \<psi>) + 2 * length (numlistlist (formula_n \<psi>')) +
      (10 + 2 * nlength 0 + 2 * nlength 1)"
    using assms canrepr_1 nlllength_def by simp
qed

definition "tps55 \<equiv> tpsJ
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n PHI),
   91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1),
   94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   95 := (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   96 := (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   97 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   91 + 6 := (\<lfloor>Suc T'\<rfloor>\<^sub>N, 1),
   91 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

definition "ttt55 \<equiv> ttt47 + 80 + 3 * nlength N + 2 * nlength H + 2 * nlength Z +
  3 * nlength T' + 2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') +
  16114767 * 2 ^ (16 * Z) * N ^ 7"

lemma ttt55: "ttt55 \<le> ttt47 + 2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') +
      16114857 * 2 ^ (16 * Z) * N ^ 7"
proof -
  have nlength_le_ZN: "y \<le> N \<Longrightarrow> nlength y \<le> 2 ^ (16*Z)* N ^ 7" for y
  proof -
    assume "y \<le> N "
    then have "nlength y \<le> N ^ 7"
      using nlength_le_n linear_le_pow H_ge_3 by (meson dual_order.trans zero_less_numeral)
    also have "... \<le> 2 ^ (16*Z) * N ^ 7"
      by simp
    finally show ?thesis .
  qed

  have "3 * nlength N \<le> 3 * 2 ^ (16*Z) * N ^ 7"
    using nlength_le_ZN by simp
  moreover have "2 * nlength H \<le> 2 * 2 ^ (16*Z) * N ^ 7"
    using nlength_le_ZN[OF H_le_N] by simp
  moreover have "2 * nlength Z \<le> 2 * 2 ^ (16*Z) * N ^ 7"
  proof -
    have "Z \<le> N "
      using N_eq Z_def by simp
    then show ?thesis
      using nlength_le_ZN by simp
  qed
  moreover have "3 * nlength T' \<le> 3 * 2 ^ (16*Z) * N ^ 7"
    using nlength_le_ZN[OF le_N] by simp
  moreover have "80 \<le> 80 * 2 ^ (16*Z) * N ^ 7"
    using N_ge_1 by simp
  ultimately have "ttt55 \<le> ttt47 + 80 * 2 ^ (16*Z) * N ^ 7 + 3 * 2 ^ (16*Z) * N ^ 7 +
      2 * 2 ^ (16*Z) * N ^ 7 + 2 * 2 ^ (16*Z) * N ^ 7 + 3 * 2 ^ (16*Z) * N ^ 7 +
      2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') +
      16114767 * 2 ^ (16 * Z) * N ^ 7"
    using ttt55_def by linarith
  also have "... = ttt47 + 2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') +
      16114857 * 2 ^ (16 * Z) * N ^ 7"
    by simp
  finally show ?thesis .
qed

lemma tm55 [transforms_intros]: "transforms tm55 tps0 ttt55 tps55"
  unfolding tm55_def
proof (tform)
  show "91 + 17 < length tps54"
    using lentpsJ tps54_def k by (simp_all only: length_list_update)
  let ?nss = "formula_n \<Phi>\<^sub>0 @ formula_n \<Phi>\<^sub>1 @ formula_n \<Phi>\<^sub>2 @ formula_n \<Phi>\<^sub>3 @ formula_n \<Phi>\<^sub>4 @
       formula_n \<Phi>\<^sub>5 @ formula_n \<Phi>\<^sub>6 @ formula_n \<Phi>\<^sub>7 @ formula_n \<Phi>\<^sub>8"
  show "tps54 ! 1 = nlltape ?nss"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps54 ! 4 = (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps54 ! 7 = (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps54 ! 91 = (\<lfloor>N\<rfloor>\<^sub>N, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  have "tps54 ! 92 = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps54 ! (91 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps54 ! 93 = (\<lfloor>Z\<rfloor>\<^sub>N, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps54 ! (91 + 2) = (\<lfloor>Z\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps54 ! 94 = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps54 ! (91 + 3) = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    by simp
  have "tps54 ! 95 = (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps54 ! (91 + 4) = (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    by simp
  have "tps54 ! 96 = (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps54 ! (91 + 5) = (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    by simp
  have "tps54 ! 97 = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
    using tps54_def k lentpsJ by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "tps54 ! (91 + 6) = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
    by simp
  show "tps54 ! (91 + i) = (\<lfloor>[]\<rfloor>, 1)" if "6 < i" "i < 17" for i
  proof -
    have "tps54 ! (91 + i) = tpsJ ! (91 + i)"
      using tps54_def that by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
    then show "tps54 ! (91 + i) = (\<lfloor>[]\<rfloor>, 1)"
      using tpsJ k that by simp
  qed
  have "tps55 = tps54
      [1 := nlltape (formula_n PHI),
       91 + 6 := (\<lfloor>Suc T'\<rfloor>\<^sub>N, 1),
       91 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    unfolding tps55_def tps54_def by (simp only: list_update_swap list_update_overwrite)
  then show "tps55 = tps54
      [1 := nlltape (?nss @ formula_n (PHI9)),
       91 + 6 := (\<lfloor>Suc T'\<rfloor>\<^sub>N, 1),
       91 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using PHI_def formula_n_def by simp
  show "ttt55 = ttt47 + 80 + 3 * nlength N + 2 * nlength H + 2 * nlength Z +
      3 * nlength T' + 2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') +
      16114767 * 2 ^ (16 * Z) * N ^ 7"
    using ttt55_def by simp
qed

lemma tps0_start_config: "(0, tps0) = start_config 110 xs"
proof
  show "fst (0, tps0) = fst (start_config 110 xs)"
    using start_config_def by simp
  let ?tps = "(\<lambda>i. if i = 0 then \<triangleright> else if i \<le> length xs then xs ! (i - 1) else \<box>, 0) #
        replicate (110 - 1) (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)"
  have "tps0 = ?tps"
  proof (rule nth_equalityI)
    show "length tps0 = length ?tps"
      using k by simp
    show "tps0 ! j = ?tps ! j" if "j < length tps0" for j
      using tps0 contents_def k that by (cases "j = 0") auto
  qed
  then show "snd (0, tps0) = snd (start_config 110 xs)"
    using start_config_def by auto
qed

lemma tm55': "snd (execute tm55 (start_config 110 xs) ttt55) = tps55"
  using tps0_start_config transforms_def transits_def tm55
  by (smt (verit, best) execute_after_halting_ge prod.sel(1) prod.sel(2))

definition "tpsK \<equiv> tpsJ
  [91 := (\<lfloor>N\<rfloor>\<^sub>N, 1),
   92 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   93 := (\<lfloor>Z\<rfloor>\<^sub>N, 1),
   94 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   95 := (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   96 := (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   97 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   91 + 6 := (\<lfloor>Suc T'\<rfloor>\<^sub>N, 1),
   91 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tpsK: "97 < j \<Longrightarrow> j < 110 \<Longrightarrow> tpsK ! j = (\<lfloor>[]\<rfloor>, 1)"
  using tpsK_def tpsJ by simp

lemma lentpsK: "length tpsK = 110"
  using lentpsJ tpsK_def by simp

lemma tps55: "tps55 = tpsK
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n PHI)]"
  unfolding tps55_def tpsK_def by (simp only: list_update_swap)

definition "tps56 \<equiv> tpsK
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm56 [transforms_intros]:
  assumes "ttt = ttt55 + tps55 :#: 1 + 2"
  shows "transforms tm56 tps0 ttt tps56"
  unfolding tm56_def
proof (tform)
  show "1 < length tps55"
    using lentpsJ tps55_def k by (simp_all only: length_list_update)
  have *: "tps55 ! 1 = nlltape (formula_n PHI)"
    using tps55 k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "clean_tape (tps55 ! 1)"
    using clean_tape_nllcontents by simp
  have "tps55 ! 1 |#=| 1 = (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using * by simp
  then show "tps56 = tps55[1 := tps55 ! 1 |#=| 1]"
    unfolding tps56_def tps55 by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt55 + (tps55 :#: 1 + 2)"
    using assms by simp
qed

definition "tps57 \<equiv> tpsK
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := nlltape (formula_n PHI),
   109 := nlltape (formula_n PHI)]"

lemma tm57 [transforms_intros]:
  assumes "ttt = ttt55 + tps55 :#: 1 + 2 + Suc (nlllength (formula_n PHI))"
  shows "transforms tm57 tps0 ttt tps57"
  unfolding tm57_def
proof (tform)
  show "1 < length tps56" "109 < length tps56"
    using lentpsK tps56_def k by (simp_all only: length_list_update)
  have *: "tps56 ! 1 = (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using tps56_def k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  let ?n = "nlllength (formula_n PHI)"
  show "rneigh (tps56 ! 1) {0} ?n"
  proof (rule rneighI)
    show "(tps56 ::: 1) (tps56 :#: 1 + nlllength (formula_n PHI)) \<in> {0}"
      using proper_symbols_numlistlist nllcontents_def * contents_outofbounds nlllength_def
      by simp
    have "\<And>n'. n' < ?n \<Longrightarrow> (tps56 ::: 1) (1 + n') > 0"
      using proper_symbols_numlistlist nllcontents_def * contents_inbounds nlllength_def
      by fastforce
    then show "\<And>n'. n' < ?n \<Longrightarrow> (tps56 ::: 1) (tps56 :#: 1 + n') \<notin> {0}"
      using * by simp
  qed
  have "tps56 ! 109 = tpsK ! 109"
    using tps56_def by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  then have **: "tps56 ! 109 = (\<lfloor>[]\<rfloor>, 1)"
    using tpsK k by simp
  have "implant (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1) (\<lfloor>[]\<rfloor>, 1) ?n =
    (\<lfloor>[] @
       take (nlllength (formula_n PHI))
        (drop (1 - 1) (numlistlist (formula_n PHI)))\<rfloor>,
     Suc (length []) + nlllength (formula_n PHI))"
    using implant_contents[of 1 ?n "numlistlist (formula_n PHI)" "[]"] nlllength_def nllcontents_def
    by simp
  then have "implant (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1) (\<lfloor>[]\<rfloor>, 1) ?n =
     (\<lfloor>take ?n (numlistlist (formula_n PHI))\<rfloor>, Suc ?n)"
    by simp
  also have "... = (\<lfloor>numlistlist (formula_n PHI)\<rfloor>, Suc ?n)"
    using nlllength_def by simp
  also have "... = (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc ?n)"
    using nllcontents_def by simp
  finally have "implant (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1) (\<lfloor>[]\<rfloor>, 1) ?n = (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc ?n)" .
  then have "implant (tps56 ! 1) (tps56 ! 109) ?n = (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc ?n)"
    using * ** by simp
  then have "implant (tps56 ! 1) (tps56 ! 109) ?n = nlltape (formula_n PHI)"
    by simp
  moreover have "tps56 ! 1 |+| nlllength (formula_n PHI) = nlltape (formula_n PHI)"
    using * by simp
  moreover have "tps57 = tps56
    [1 := nlltape (formula_n PHI),
     109 := nlltape (formula_n PHI)]"
    unfolding tps57_def tps56_def by (simp only: list_update_swap[of 1] list_update_overwrite)
  ultimately show "tps57 = tps56
    [1 := tps56 ! 1 |+| nlllength (formula_n PHI),
     109 := implant (tps56 ! 1) (tps56 ! 109) (nlllength (formula_n PHI))]"
    by simp
  show "ttt = ttt55 + tps55 :#: 1 + 2 + Suc (nlllength (formula_n PHI))"
    using assms by simp
qed

definition "tps58 \<equiv> tpsK
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := (\<lfloor>[]\<rfloor>, 1),
   109 := nlltape (formula_n PHI)]"

lemma tm58 [transforms_intros]:
  assumes "ttt = ttt55 + 9 + tps55 :#: 1 + 3 * nlllength (formula_n PHI) + tps57 :#: 1"
  shows "transforms tm58 tps0 ttt tps58"
  unfolding tm58_def
proof (tform)
  show "1 < length tps57"
    using lentpsK tps57_def k by (simp_all only: length_list_update)
  let ?zs = "numlistlist (formula_n PHI)"
  show "proper_symbols ?zs"
    using proper_symbols_numlistlist by simp
  have "tps57 ! 1 = nlltape (formula_n PHI)"
    using tps57_def k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then have "tps57 ! 1 = (\<lfloor>numlistlist (formula_n PHI)\<rfloor>, Suc (nlllength (formula_n PHI)))"
    using nlllength_def nllcontents_def by auto
  then show "tps57 ::: 1 = \<lfloor>numlistlist (formula_n PHI)\<rfloor>"
    by simp
  show "tps58 = tps57[1 := (\<lfloor>[]\<rfloor>, 1)]"
    unfolding tps58_def tps57_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt55 + tps55 :#: 1 + 2 + Suc (nlllength (formula_n PHI)) +
      (tps57 :#: 1 + 2 * length (numlistlist (formula_n PHI)) + 6)"
    using assms nlllength_def by simp
qed

definition "tps59 \<equiv> tpsK
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := (\<lfloor>[]\<rfloor>, 1),
   109 := (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm59 [transforms_intros]:
  assumes "ttt = ttt55 + 11 + tps55 :#: 1 + 3 * nlllength (formula_n PHI) + tps57 :#: 1 + tps58 :#: 109"
  shows "transforms tm59 tps0 ttt tps59"
  unfolding tm59_def
proof (tform)
  show "109 < length tps58"
    using lentpsK tps58_def k by (simp_all only: length_list_update)
  have *: "tps58 ! 109 = nlltape (formula_n PHI)"
    using tps58_def k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then show "clean_tape (tps58 ! 109)"
    by (simp add: clean_tape_nllcontents)
  have "tps58 ! 109 |#=| 1 = (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using * by simp
  then show "tps59 = tps58[109 := tps58 ! 109 |#=| 1]"
    unfolding tps59_def tps58_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt55 + 9 + tps55 :#: 1 + 3 * nlllength (formula_n PHI) + tps57 :#: 1 +
      (tps58 :#: 109 + 2)"
    using assms by simp
qed

definition "tps60 \<equiv> tpsK
  [11 := (\<lfloor>n\<rfloor>\<^sub>N, 1),
   15 := (\<lfloor>p n\<rfloor>\<^sub>N, 1),
   16 := (\<lfloor>m\<rfloor>\<^sub>N, 1),
   17 := (\<lfloor>T'\<rfloor>\<^sub>N, 1),
   4 := (\<lfloor>map (\<lambda>t. exc zs t <#> 0) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   7 := (\<lfloor>map (\<lambda>t. exc zs t <#> 1) [0..<Suc T']\<rfloor>\<^sub>N\<^sub>L, 1),
   18 := (\<lfloor>m'\<rfloor>\<^sub>N, 1),
   19 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   20 := (\<lfloor>m' * H\<rfloor>\<^sub>N, 1),
   1 := (\<lfloor>[]\<rfloor>, 1),
   109 := (\<lfloor>formula_n PHI\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   109 := (\<lfloor>numlistlist (formula_n PHI)\<rfloor>,
       Suc (length (numlistlist (formula_n PHI)))),
   1 := (\<lfloor>binencode (numlistlist (formula_n PHI))\<rfloor>,
       Suc (2 * length (numlistlist (formula_n PHI))))]"

lemma tm60:
  assumes "ttt = ttt55 + 12 + tps55 :#: 1 + 12 * nlllength (formula_n PHI) + tps57 :#: 1 + tps58 :#: 109"
  shows "transforms tm60 tps0 ttt tps60"
  unfolding tm60_def
proof (tform)
  show "109 < length tps59" "1 < length tps59"
    using lentpsK tps59_def k by (simp_all only: length_list_update)
  let ?zs = "numlistlist (formula_n PHI)"
  show "binencodable ?zs"
    using proper_symbols_numlistlist symbols_lt_numlistlist by fastforce
  show "tps59 ! 109 = (\<lfloor>numlistlist (formula_n PHI)\<rfloor>, 1)"
    using tps59_def k lentpsK nllcontents_def
    by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps59 ! 1 = (\<lfloor>[]\<rfloor>, 1)"
    using tps59_def k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  show "tps60 \<equiv> tps59
    [109 := (\<lfloor>numlistlist (formula_n PHI)\<rfloor>,
        Suc (length (numlistlist (formula_n PHI)))),
     1 := (\<lfloor>binencode (numlistlist (formula_n PHI))\<rfloor>,
           Suc (2 * length (numlistlist (formula_n PHI))))]"
    unfolding tps60_def tps59_def by (simp only: list_update_swap list_update_overwrite)
  show "ttt = ttt55 + 11 + tps55 :#: 1 + 3 * nlllength (formula_n PHI) + tps57 :#: 1 +
      tps58 :#: 109 + (9 * length (numlistlist (formula_n PHI)) + 1)"
    using assms nlllength_def by simp
qed

definition "ttt60 \<equiv> 16 * ttt55"

lemma tm60': "transforms tm60 tps0 ttt60 tps60"
proof -
  have tps55_head_1: "tps55 :#: 1 \<le> ttt55"
  proof -
    have *: "(1::nat) < 110"
      using k by simp
    show ?thesis
      using head_pos_le_time[OF tm55_tm *, of "xs " ttt55] tm55' k by simp
  qed

  let ?ttt = "ttt55 + 12 + tps55 :#: 1 + 12 * nlllength (formula_n PHI) + tps57 :#: 1 + tps58 :#: 109"
  have 55: "tps55 :#: 1 = Suc (nlllength (formula_n PHI))"
  proof -
    have "tps55 ! 1 = nlltape (formula_n PHI)"
      using tps55 k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
    then show ?thesis
      by simp
  qed
  moreover have "tps57 :#: 1 = Suc (nlllength (formula_n PHI))"
  proof -
    have "tps57 ! 1 = nlltape (formula_n PHI)"
      using tps57_def k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
    then show ?thesis
      by simp
  qed
  moreover have "tps58 :#: 109 = Suc (nlllength (formula_n PHI))"
  proof -
    have "tps58 ! 109 = nlltape (formula_n PHI)"
      using tps58_def k lentpsK by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
    then show ?thesis
      by simp
  qed
  ultimately have "?ttt = ttt55 + 12 + 3 * (Suc (nlllength (formula_n PHI))) + 12 * nlllength (formula_n PHI)"
    by simp
  also have "... = ttt55 + 15 + 15 * (nlllength (formula_n PHI))"
    by simp
  also have "... = ttt55 + 15 * (Suc (nlllength (formula_n PHI)))"
    by simp
  also have "... \<le> ttt55 + 15 * ttt55"
    using tps55_head_1 55 by simp
  also have "... = 16 * ttt55"
    by simp
  finally have "?ttt \<le> 16 * ttt55" .
  then show ?thesis
    using tm60 transforms_monotone ttt60_def by simp
qed

lemma tm60_start_config: "transforms tm60 (snd (start_config 110 (string_to_symbols x))) ttt60 tps60"
  using tm60' tps0_start_config by (metis prod.sel(2))

end  (* context tps *)

end  (* locale reduction_sat_x *)

text \<open>
The time bound @{term ttt60} formally depends on the string $x$. But we need a bound
depending only on the length.
\<close>

context reduction_sat
begin

definition T60 :: "nat \<Rightarrow> nat" where
  "T60 nn \<equiv> reduction_sat_x.ttt60 M G p (replicate nn True)"

lemma T60:
  fixes x :: string
  shows "T60 (length x) = reduction_sat_x.ttt60 M G p x"
proof -
  interpret x: reduction_sat_x L M G T p x
    by (simp add: reduction_sat_axioms reduction_sat_x.intro)

  define tpsx :: "tape list" where "tpsx = snd (start_config 110 (x.xs))"
  have x1: "110 = length tpsx"
    using start_config_def tpsx_def by auto
  have x2: "tpsx ! 0 = (\<lfloor>x.xs\<rfloor>, 0)"
    using start_config_def tpsx_def by auto
  have x3: "\<And>i. 0 < i \<Longrightarrow> i < 110 \<Longrightarrow> tpsx ! i = (\<lfloor>[]\<rfloor>, 0)"
    using start_config_def tpsx_def by auto

  let ?y = "replicate (length x) True"
  interpret y: reduction_sat_x L M G T p ?y
    by (simp add: reduction_sat_axioms reduction_sat_x.intro)
  define tpsy :: "tape list" where "tpsy = snd (start_config 110 (y.xs))"
  have y1: "110 = length tpsy"
    using start_config_def tpsy_def by auto
  have y2: "tpsy ! 0 = (\<lfloor>y.xs\<rfloor>, 0)"
    using start_config_def tpsy_def by auto
  have y3: "\<And>i. 0 < i \<Longrightarrow> i < 110 \<Longrightarrow> tpsy ! i = (\<lfloor>[]\<rfloor>, 0)"
    using start_config_def tpsy_def by auto

  have m: "x.m = y.m"
    using x.m_def y.m_def by simp
  have T': "x.T' = y.T'"
    using x.T'_def y.T'_def m by simp
  have m': "x.m' = y.m'"
    using x.m'_def y.m'_def T' by simp
  have N: "x.N = y.N"
    using x.N_eq y.N_eq T' by simp

  have "x.ttt31 = y.ttt31"
    using x.ttt31_def[OF x1 x2 x3] y.ttt31_def[OF y1 y2 y3] T' m m' by simp
  then have "x.ttt47 = y.ttt47"
    using x.ttt47_def[OF x1 x2 x3] y.ttt47_def[OF y1 y2 y3] T' m m' by simp
  then have "x.ttt55 = y.ttt55"
    using x.ttt55_def[OF x1 x2 x3] y.ttt55_def[OF y1 y2 y3] T' m m' N by simp
  then have "x.ttt60 = y.ttt60"
    using x.ttt60_def[OF x1 x2 x3] y.ttt60_def[OF y1 y2 y3] by simp
  then show "T60 (length x) = reduction_sat_x.ttt60 M G p x"
  unfolding T60_def by simp
qed

lemma poly_T60: "big_oh_poly T60"
proof -
  define fN :: "nat \<Rightarrow> nat" where
    "fN = (\<lambda>nn. H * (2 * nn + 2 * p nn + 3 + TT (2 * nn + 2 * p nn + 2)))"
  define f where
    "f = (\<lambda>nn. 16 * ((32 * d_polynomial p + 364343) * H ^ 6 * fN nn ^ 4 +
      2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN nn ^ 7))"
  have T60_upper: "T60 nn \<le> f nn" for nn
  proof -
    define y where "y = replicate nn True"
    then have leny: "length y = nn"
      by simp
    interpret y: reduction_sat_x _ _ _ _ _ y
      by (simp add: reduction_sat_axioms reduction_sat_x.intro)
    define tps0 :: "tape list" where "tps0 = snd (start_config 110 y.xs)"
    have 1: "110 = length tps0"
      using start_config_def tps0_def by auto
    have 2: "tps0 ! 0 = (\<lfloor>y.xs\<rfloor>, 0)"
      using start_config_def tps0_def by auto
    have 3: "\<And>i. 0 < i \<Longrightarrow> i < 110 \<Longrightarrow> tps0 ! i = (\<lfloor>[]\<rfloor>, 0)"
      using start_config_def tps0_def by auto

    have "T60 nn = y.ttt60"
      by (simp add: y_def T60_def)
    also have "... \<le> 16 * y.ttt55"
      using y.ttt60_def[OF 1 2 3] by simp
    also have "... \<le> 16 * (y.ttt47 + 2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * y.N ^ 7)"
      using y.ttt55[OF 1 2 3] by simp
    also have "... \<le> 16 * ((32 * d_polynomial p + 364343) * H ^ 6 * y.N ^ 4 +
        2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * y.N ^ 7)"
      using y.ttt47[OF 1 2 3] by simp
    also have "... = 16 * ((32 * d_polynomial p + 364343) * H ^ 6 * fN nn ^ 4 +
        2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN nn ^ 7)"
    proof -
      have "y.N = fN nn"
        using y.N_eq y.T'_def y.m_def y_def fN_def by simp
      then show ?thesis
        by simp
    qed
    finally have "T60 nn \<le> 16 * ((32 * d_polynomial p + 364343) * H ^ 6 * fN nn ^ 4 +
        2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN nn ^ 7)" .
    then show ?thesis
      using f_def by simp
  qed

  have *: "big_oh_poly fN"
  proof -
    have 5: "big_oh_poly p"
      using big_oh_poly_polynomial[OF p] by simp
    have 6: "big_oh_poly TT"
      using T big_oh_poly_le TT_le by simp
    have "big_oh_poly (\<lambda>nn. 2 * p nn + 2)"
      using 5 big_oh_poly_sum big_oh_poly_prod big_oh_poly_const
      by presburger
    moreover have "big_oh_poly (\<lambda>nn. 2 * nn)"
      using big_oh_poly_prod big_oh_poly_const big_oh_poly_id by simp
    ultimately have "big_oh_poly (\<lambda>nn. 2 * nn + 2 * p nn + 2)"
      using big_oh_poly_sum by fastforce
    then have "big_oh_poly (TT \<circ> (\<lambda>nn. 2 * nn + 2 * p nn + 2))"
      using big_oh_poly_composition[OF _ 6] by simp
    moreover have "TT \<circ> (\<lambda>nn. 2 * nn + 2 * p nn + 2) = (\<lambda>nn. TT (2 * nn + 2 * p nn + 2))"
      by auto
    ultimately have "big_oh_poly (\<lambda>nn. TT (2 * nn + 2 * p nn + 2))"
      by simp
    moreover have "big_oh_poly (\<lambda>nn. 2 * nn + 2 * p nn + 3)"
      using 5 big_oh_poly_prod big_oh_poly_const big_oh_poly_sum big_oh_poly_id by simp
    ultimately have "big_oh_poly (\<lambda>nn. 2 * nn + 2 * p nn + 3 + TT (2 * nn + 2 * p nn + 2))"
      using big_oh_poly_sum by simp
    then have "big_oh_poly (\<lambda>nn. H * (2 * nn + 2 * p nn + 3 + TT (2 * nn + 2 * p nn + 2)))"
      using big_oh_poly_prod big_oh_poly_const by simp
    then show ?thesis
      using fN_def by simp
  qed
  then have "big_oh_poly (\<lambda>n. fN n ^ 4)"
    using big_oh_poly_pow by simp
  moreover have "big_oh_poly (\<lambda>n. (32 * d_polynomial p + 364343) * H ^ 6)"
    using big_oh_poly_prod big_oh_poly_const big_oh_poly_sum by simp
  ultimately have "big_oh_poly (\<lambda>n. (32 * d_polynomial p + 364343) * H ^ 6 * fN n ^ 4)"
    using big_oh_poly_prod by simp
  moreover have "big_oh_poly (\<lambda>n. 2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN n ^ 7)"
    using big_oh_poly_pow * big_oh_poly_sum big_oh_poly_prod big_oh_poly_const
    by simp
  ultimately have "big_oh_poly (\<lambda>n. ((32 * d_polynomial p + 364343) * H ^ 6 * fN n ^ 4) +
      (2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN n ^ 7))"
    using big_oh_poly_sum by simp
  moreover have "(\<lambda>n. ((32 * d_polynomial p + 364343) * H ^ 6 * fN n ^ 4) +
      (2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN n ^ 7)) =
      (\<lambda>n. (32 * d_polynomial p + 364343) * H ^ 6 * fN n ^ 4 +
        2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN n ^ 7)"
    by auto
  ultimately have "big_oh_poly (\<lambda>n. (32 * d_polynomial p + 364343) * H ^ 6 * fN n ^ 4 +
      2 * nlllength (formula_n \<psi>) + 2 * nlllength (formula_n \<psi>') + 16114857 * 2 ^ (16 * Z) * fN n ^ 7)"
    by simp
  then have "big_oh_poly f"
    using f_def big_oh_poly_prod big_oh_poly_const by blast
  then show "big_oh_poly T60"
    using T60_upper big_oh_poly_le by simp
qed

text \<open>
This is the function, in terms of bit strings, that maps $x$ to $\Phi$.
\<close>

definition freduce :: "string \<Rightarrow> string" ("f\<^bsub>reduce\<^esub>") where
  "f\<^bsub>reduce\<^esub> x \<equiv> formula_to_string (reduction_sat_x.PHI M G p x)"

text \<open>
The function $f_{reduce}$ many-one reduces $L$ to \SAT{}.
\<close>

lemma x_in_L: "x \<in> L \<longleftrightarrow> f\<^bsub>reduce\<^esub> x \<in> SAT"
proof
  interpret x: reduction_sat_x
    by (simp add: reduction_sat_axioms reduction_sat_x.intro)
  show "x \<in> L \<Longrightarrow> f\<^bsub>reduce\<^esub> x \<in> SAT"
    using freduce_def SAT_def x.L_iff_satisfiable by auto
  show "f\<^bsub>reduce\<^esub> x \<in> SAT \<Longrightarrow> x \<in> L"
  proof -
    assume "f\<^bsub>reduce\<^esub> x \<in> SAT"
    then obtain phi where
      phi: "satisfiable phi" "f\<^bsub>reduce\<^esub> x = formula_to_string phi "
      using SAT_def freduce_def by auto

    have "formula_to_string (reduction_sat_x.PHI M G p x) = formula_to_string phi"
      using phi(2) freduce_def by simp
    then have "reduction_sat_x.PHI M G p x = phi"
      using formula_to_string_inj by simp
    then have "satisfiable (reduction_sat_x.PHI M G p x)"
      using phi(1) by simp
    then show "x \<in> L"
      using x.L_iff_satisfiable by simp
  qed
qed

text \<open>
The Turing machine @{const tm60} computes $f_{reduce}$ with time bound $T60$.
\<close>

lemma computes_in_time_tm60: "computes_in_time 110 tm60 f\<^bsub>reduce\<^esub> T60"
proof
  fix x :: string

  interpret x: reduction_sat_x _ _ _ _ _ x
    by (simp add: reduction_sat_axioms reduction_sat_x.intro)

  have "binencodable (numlistlist (formula_n x.PHI))"
    by (metis One_nat_def Suc_1 Suc_leI le_refl proper_symbols_numlistlist symbols_lt_numlistlist)
  then have *: "bit_symbols (binencode (numlistlist (formula_n x.PHI)))"
    using bit_symbols_binencode by simp

  define tps0 :: "tape list" where "tps0 = snd (start_config 110 x.xs)"
  have 1: "110 = length tps0"
    using start_config_def tps0_def by auto
  have 2: "tps0 ! 0 = (\<lfloor>x.xs\<rfloor>, 0)"
    using start_config_def tps0_def by auto
  have 3: "\<And>i. 0 < i \<Longrightarrow> i < 110 \<Longrightarrow> tps0 ! i = (\<lfloor>[]\<rfloor>, 0)"
    using start_config_def tps0_def by auto
  let ?tps = "x.tps60 tps0"
  have "length ?tps = 110"
    using x.tps60_def[OF 1 2 3] x.lentpsK[OF 1 2 3] by (simp_all only: length_list_update)
  then have "?tps ! 1 = (\<lfloor>binencode (numlistlist (formula_n (x.PHI)))\<rfloor>,
      Suc (2 * length (numlistlist (formula_n x.PHI))))"
    using x.tps60_def[OF 1 2 3] by (simp only: length_list_update nth_list_update_neq nth_list_update_eq)
  then have "?tps ::: 1 = \<lfloor>binencode (numlistlist (formula_n x.PHI))\<rfloor>"
    by simp
  also have "... = string_to_contents (symbols_to_string (binencode (numlistlist (formula_n x.PHI))))"
    using bit_symbols_to_contents[OF *] by simp
  also have "... = string_to_contents (f\<^bsub>reduce\<^esub> x)"
    using freduce_def by auto
  finally have **: "?tps ::: 1 = string_to_contents (f\<^bsub>reduce\<^esub> x)" .

  have "transforms tm60 tps0 x.ttt60 ?tps"
    using tps0_def x.tm60_start_config[OF 1 2 3] by simp
  then have "transforms tm60 (snd (start_config 110 x.xs)) (T60 (length x)) ?tps"
    using T60 tps0_def by simp

  then show "\<exists>tps.
      tps ::: 1 = string_to_contents (f\<^bsub>reduce\<^esub> x) \<and>
      transforms tm60 (snd (start_config 110 (string_to_symbols x))) (T60 (length x)) tps"
    using ** by auto
qed

text \<open>
Since $T60$ is bounded by a polynomial, the previous three lemmas imply that $L$
is polynomial-time many-one reducible to \SAT{}.
\<close>

lemma L_reducible_SAT: "L \<le>\<^sub>p SAT"
  using reducible_def tm60_tm poly_T60 computes_in_time_tm60 x_in_L by fastforce

end  (* locale reduction_sat *)

text \<open>
In the locale @{locale reduction_sat} the language $L$ was chosen arbitrarily
with properties that we have proven $\NP$ languages have. So we can now show
that \SAT{} is $\NP$-hard.

\null
\<close>

theorem NP_hard_SAT:
  assumes "L \<in> \<N>\<P>"
  shows "L \<le>\<^sub>p SAT"
proof -
  obtain M G T p where
    T: "big_oh_poly T" and
    p: "polynomial p" and
    tm_M: "turing_machine 2 G M" and
    oblivious_M: "oblivious M" and
    T_halt: "\<And>y. bit_symbols y \<Longrightarrow> fst (execute M (start_config 2 y) (T (length y))) = length M" and
    cert: "\<And>x. x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> execute M (start_config 2 \<langle>x; u\<rangle>) (T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>)"
    using NP_imp_oblivious_2tape[OF assms] by metis

  interpret red: reduction_sat L M G T p
    using T p tm_M oblivious_M T_halt cert reduction_sat.intro by simp

  show ?thesis
    using red.L_reducible_SAT by simp
qed


section \<open>\SAT{} is $\NP$-complete\label{s:complete}\<close>

text \<open>
The time has come to reap the fruits of our labor and show that \SAT{} is
$\NP$-complete.

\null
\<close>

theorem NP_complete_SAT: "NP_complete SAT"
  using NP_hard_SAT SAT_in_NP NP_complete_def by simp

end
