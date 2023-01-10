section \<open>Turing machines for the parts of $\Phi$\label{s:tmcnf}\<close>

theory Sat_TM_CNF
  imports Aux_TM_Reducing
begin

text \<open>
In this section we build Turing machines for all parts $\Phi_0,\dots,\Phi_9$ of
the CNF formula $\Phi$. Some of them ($\Phi_0$, $\Phi_1$, $\Phi_2$, and
$\Phi_8$) are just fixed-length sequences of $\Psi$ formulas constructible by
fixed-length sequences of @{const tm_Psigamma} machines.  Others ($\Phi_3$,
$\Phi_4$, $\Phi_5$, $\Phi_6$) are variable-length and require looping over a
@{const tm_Psigamma} machine. The TM for $\Phi_7$ is a loop over @{const
tm_Upsilongamma}. Lastly, the TM for $\Phi_9$ is a loop over a TM that generates
the formulas $\chi_t$.

Ideally we would want to prove the semantics of the TMs inside the locale
@{locale reduction_sat}, in which $\Phi$ was defined. However, we use locales to
prove the semantics of TMs, and locales cannot be nested. For this reason we
have to define the TMs on the theory level and prove their semantics there, too,
just as we have done with all TMs until now. In the next chapter the semantics
lemmas will be transferred to the locale @{locale reduction_sat}.

Unlike most TMs so far, the TMs in this section are not meant to be reusable
but serve a special purpose, namely to be combined into one large TM computing
$\Phi$. For this reason the TMs are somewhat peculiar. For example, they write
their output to the fixed tape~$1$ rather than having a parameter for the output
tape. They also often expect the tapes to be initialized in a very special way.
Moreover, the TMs often leave the work tapes in a ``dirty'' state with remnants
of intermediate calculations. The combined TM for all of $\Phi$ will simply
allocate a new batch of work tapes for every individual TM.
\<close>


subsection \<open>A Turing machine for $\Phi_0$\<close>

text \<open>
The next Turing machine expects a number $i$ on tape $j$ and a number $H$ on
tape $j + 1$ and outputs to tape $1$ the formula $\Psi([i\dots H, (i+1)\dots H),
1) \land \Psi([(i+1)\dots H, (i+2)\dots H), 1) \land \Psi([(i+2)\dots H,
(i+3)\dots H), 0)$, which is just $\Phi_0$ for suitable values of $i$ and $H$.
\<close>

definition tm_PHI0 :: "tapeidx \<Rightarrow> machine" where
  "tm_PHI0 j \<equiv>
    tm_setn (j + 2) 1 ;;
    tm_Psigamma j ;;
    tm_extendl_erase 1 (j + 6) ;;
    tm_incr j ;;
    tm_Psigamma j ;;
    tm_extendl_erase 1 (j + 6) ;;
    tm_incr j ;;
    tm_setn (j + 2) 0 ;;
    tm_Psigamma j ;;
    tm_extendl 1 (j + 6)"

lemma tm_PHI0_tm:
  assumes "0 < j" and "j + 8 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_PHI0 j)"
  unfolding tm_PHI0_def
  using assms tm_Psigamma_tm tm_extendl_tm tm_erase_cr_tm tm_times2_tm tm_incr_tm tm_setn_tm tm_cr_tm
    tm_extendl_erase_tm
  by simp

locale turing_machine_PHI0 =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_setn (j + 2) 1"
definition "tm2 \<equiv> tm1 ;; tm_Psigamma j"
definition "tm3 \<equiv> tm2 ;; tm_extendl_erase 1 (j + 6)"
definition "tm5 \<equiv> tm3 ;; tm_incr j"
definition "tm6 \<equiv> tm5 ;; tm_Psigamma j"
definition "tm7 \<equiv> tm6 ;; tm_extendl_erase 1 (j + 6)"
definition "tm9 \<equiv> tm7 ;; tm_incr j"
definition "tm10 \<equiv> tm9 ;; tm_setn (j + 2) 0"
definition "tm11 \<equiv> tm10 ;; tm_Psigamma j"
definition "tm12 \<equiv> tm11 ;; tm_extendl 1 (j + 6)"

lemma tm12_eq_tm_PHI0: "tm12 = tm_PHI0 j"
  using tm12_def tm11_def tm10_def tm9_def tm7_def tm6_def tm5_def
  using tm3_def tm2_def tm1_def tm_PHI0_def
  by simp

context
  fixes tps0 :: "tape list" and k idx H :: nat
  assumes jk: "length tps0 = k" "1 < j" "j + 8 < k"
    and H: "H \<ge> 3"
  assumes tps0:
    "tps0 ! 1 = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 8) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 12"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def jk)
  show "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 jk canrepr_0 by simp
  show "ttt = 10 + 2 * nlength 0 + 2 * nlength 1"
    using assms canrepr_1 by simp
qed

definition "tps2 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (idx * H) H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 12 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: assms tps0 H tps1_def tps2_def jk)

definition "tps3 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   1 := nlltape (nll_Psi (idx * H) H (Suc 0)),
   j + 6 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 23 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H (Suc 0))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps0 H tps2_def tps3_def jk time: assms)
  show "tps2 ! 1 = nlltape []"
    using tps2_def jk nllcontents_Nil tps0 by simp
  show "tps3 = tps2
      [1 := nlltape ([] @ nll_Psi (idx * H) H (Suc 0)),
       j + 6 := (\<lfloor>[]\<rfloor>, 1)]"
    unfolding tps3_def tps2_def using jk by (simp add: list_update_swap)
qed

definition "tps5 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   1 := nlltape (nll_Psi (idx * H) H (Suc 0)),
   j + 6 := (\<lfloor>[]\<rfloor>, 1),
   j := (\<lfloor>Suc idx\<rfloor>\<^sub>N, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 28 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) +
      2 * nlength idx"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform tps: tps0 H tps3_def tps5_def jk time: assms)

definition "tps6 \<equiv> tps0
  [j := (\<lfloor>Suc idx\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (Suc idx * H) H (Suc 0)\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   1 := nlltape (nll_Psi (idx * H) H 1)]"

lemma tm6 [transforms_intros]:
  assumes "ttt = 28 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: tps0 H tps5_def tps6_def jk time: assms)
  show "tps6 = tps5[j + 6 := (\<lfloor>nll_Psi (Suc idx * H) H (Suc 0)\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
    unfolding tps5_def tps6_def using jk
    by (simp add: list_update_swap[of j] list_update_swap[of _ "j + 6"])
qed

definition "tps7 \<equiv> tps0
  [j := (\<lfloor>Suc idx\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>[]\<rfloor>, 1),
   1 := nlltape (nll_Psi (idx * H) H 1 @ nll_Psi (H + idx * H) H 1)]"

lemma tm7 [transforms_intros]:
  assumes "ttt = 39 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
    4 * nlllength (nll_Psi (idx * H) H 1) +
    2 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 +
    4 * nlllength (nll_Psi (H + idx * H) H 1)"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform tps: assms tps6_def tps7_def jk)

definition "tps9 \<equiv> tps0
  [j := (\<lfloor>Suc (Suc idx)\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>[]\<rfloor>, 1),
   1 := nlltape (nll_Psi (idx * H) H 1 @ nll_Psi (H + idx * H) H 1)]"

lemma tm9 [transforms_intros]:
  assumes "ttt = 44 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx)"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def
proof (tform tps: tps0 H tps7_def tps9_def jk time: assms)
  show "tps9 = tps7[j := (\<lfloor>Suc (Suc idx)\<rfloor>\<^sub>N, 1)]"
    using tps9_def tps7_def jk by (simp add: list_update_swap)
qed

definition "tps10 \<equiv> tps0
  [j := (\<lfloor>Suc (Suc idx)\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>[]\<rfloor>, 1),
   1 := nlltape (nll_Psi (idx * H) H 1 @ nll_Psi (H + idx * H) H 1)]"

lemma tm10 [transforms_intros]:
  assumes "ttt = 56 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx)"
  shows "transforms tm10 tps0 ttt tps10"
  unfolding tm10_def
proof (tform tps: tps0 H tps9_def tps10_def jk)
  show "ttt = 44 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx) + (10 + 2 * nlength (Suc 0) + 2 * nlength 0) "
    using assms canrepr_1 by simp
qed

definition "tps11 \<equiv> tps0
  [j := (\<lfloor>Suc (Suc idx)\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (Suc (Suc idx) * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   1 := nlltape (nll_Psi (idx * H) H 1 @ nll_Psi (H + idx * H) H 1)]"

lemma tm11 [transforms_intros]:
  assumes "ttt = 56 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2"
  shows "transforms tm11 tps0 ttt tps11"
  unfolding tm11_def by (tform tps: tps0 H tps10_def tps11_def jk time: assms)

definition "tps12 \<equiv> tps0
  [j := (\<lfloor>Suc (Suc idx)\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (Suc (Suc idx) * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   1 := nlltape (nll_Psi (idx * H) H 1 @ nll_Psi (H + idx * H) H 1 @ nll_Psi (Suc (Suc idx) * H) H 0)]"

lemma tm12:
  assumes "ttt = 60 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      2 * nlllength (nll_Psi (H + (H + idx * H)) H 0)"
  shows "transforms tm12 tps0 ttt tps12"
  unfolding tm12_def by (tform tps: tps11_def tps12_def jk assms)

lemma tm12':
  assumes "ttt = 5627 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2"
  shows "transforms tm12 tps0 ttt tps12"
proof -
  let ?ttt = "60 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * nlllength (nll_Psi (idx * H) H 1) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      2 * nlllength (nll_Psi (H + (H + idx * H)) H 0)"
  have "?ttt \<le> 60 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * nlllength (nll_Psi (H + idx * H) H 1) +
      2 * nlength (Suc idx) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      2 * nlllength (nll_Psi (H + (H + idx * H)) H 0)"
    using nlllength_nll_Psi_le'[of "idx * H" "2 * H + idx * H" "H"] by simp
  also have "... \<le> 60 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * H * (3 + nlength (3 * H + idx * H)) +
      2 * nlength (Suc idx) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      2 * nlllength (nll_Psi (H + (H + idx * H)) H 0)"
    using nlllength_nll_Psi_le'[of "H + idx * H" "2 * H + idx * H" "H"] by simp
  also have "... \<le> 60 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      4 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 4 * H * (3 + nlength (3 * H + idx * H)) +
      2 * nlength (Suc idx) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      2 * H * (3 + nlength (3 * H + idx * H))"
    using nlllength_nll_Psi_le'[of "H + (H + idx * H)" "2 * H + idx * H" "H"] by simp
  also have "... = 60 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 + 2 * nlength (Suc idx) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2"
    by simp
  also have "... \<le> 60 + 1851 * H ^ 4 * (nlength (Suc (Suc idx)))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 + 2 * nlength (Suc idx) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2"
    using nlength_mono linear_le_pow by simp
  also have "... \<le> 60 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 + 2 * nlength (Suc idx) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2"
    using nlength_mono linear_le_pow by simp
  also have "... = 60 + 5553 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength idx + 2 * nlength (Suc idx)"
    by simp
  also have "... \<le> 60 + 5553 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 2 * nlength (Suc idx) + 2 * nlength (Suc idx)"
    using nlength_mono by simp
  also have "... = 60 + 5553 * H ^ 4 * (nlength (Suc (Suc (Suc idx))))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 4 * nlength (Suc idx)"
    by simp
  also have "... \<le> 60 + 5553 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2 +
      10 * H * (3 + nlength (3 * H + idx * H)) + 4 * nlength (Suc idx)"
  proof -
    have "Suc (Suc (Suc idx)) \<le> 3 * H + idx * H"
    proof (cases "idx = 0")
      case True
      then show ?thesis
        using H by simp
    next
      case False
      then show ?thesis
        using H
        by (metis One_nat_def Suc3_eq_add_3 comm_semiring_class.distrib le_Suc_eq less_eq_nat.simps(1) mult.commute
          mult_1 mult_le_mono1 nle_le not_numeral_le_zero)
    qed
    then have "nlength (Suc (Suc (Suc idx))) \<le> 3 + nlength (3 * H + idx * H)"
      using nlength_mono trans_le_add2 by presburger
    then have "nlength (Suc (Suc (Suc idx))) ^ 2 \<le> (3 + nlength (3 * H + idx * H)) ^ 2"
      by simp
    then show ?thesis
      by simp
  qed
  also have "... \<le> 60 + 5553 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2 +
      10 * H ^ 4 * (3 + nlength (3 * H + idx * H)) + 4 * nlength (Suc idx)"
    using linear_le_pow by simp
  also have "... \<le> 60 + 5553 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2 +
      10 * H ^ 4 * (3 + nlength (3 * H + idx * H)) ^ 2 + 4 * nlength (Suc idx)"
    using linear_le_pow by simp
  also have "... = 60 + 5563 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2 + 4 * nlength (Suc idx)"
    by simp
  also have "... \<le> 60 + 5563 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2 +
    4 * H^4 * (3 + nlength (3 * H + idx * H))^2"
  proof -
    have "idx \<le> idx * H"
      using H by simp
    then have "Suc idx \<le> 3 * H + idx * H"
      using H by linarith
    then have "nlength (Suc idx) \<le> 3 + nlength (3 * H + idx * H)"
      using nlength_mono trans_le_add2 by presburger
    also have "... \<le> (3 + nlength (3 * H + idx * H)) ^ 2"
      by (simp add: power2_eq_square)
    also have "... \<le> H * (3 + nlength (3 * H + idx * H)) ^ 2"
      using H by simp
    also have "... \<le> H^4 * (3 + nlength (3 * H + idx * H)) ^ 2"
      using linear_le_pow by simp
    finally have "nlength (Suc idx) \<le> H^4 * (3 + nlength (3 * H + idx * H)) ^ 2" .
    then show ?thesis
      by simp
  qed
  also have "... = 60 + 5567 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2"
    by simp
  also have "... \<le> 60 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2 + 5567 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2"
    using H linear_le_pow by simp
  also have "... = 5627 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2"
    by simp
  finally have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm12 transforms_monotone by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_PHI0 *)

lemma transforms_tm_PHI0I:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k idx H :: nat
  assumes "length tps = k" and "1 < j" and "j + 8 < k" and "H \<ge> 3"
  assumes
    "tps ! 1 = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
    [j := (\<lfloor>Suc (Suc idx)\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>nll_Psi (Suc (Suc idx) * H) H 0\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
     1 := nlltape (nll_Psi (idx * H) H 1 @ nll_Psi (H + idx * H) H 1 @ nll_Psi (Suc (Suc idx) * H) H 0)]"
  assumes "ttt = 5627 * H ^ 4 * (3 + nlength (3 * H + idx * H))\<^sup>2"
  shows "transforms (tm_PHI0 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI0 j .
  show ?thesis
    using loc.tps12_def loc.tm12' loc.tm12_eq_tm_PHI0 assms by metis
qed


subsection \<open>A Turing machine for $\Phi_1$\<close>

text \<open>
The next TM expects a number $H$ on tape $j + 1$ and appends to the formula on
tape $1$ the formula $\Psi([0, H), 1)$.
\<close>

definition tm_PHI1 :: "tapeidx \<Rightarrow> machine" where
  "tm_PHI1 j \<equiv>
    tm_setn (j + 2) 1 ;;
    tm_Psigamma j ;;
    tm_extendl 1 (j + 6)"

lemma tm_PHI1_tm:
  assumes "0 < j" and "j + 7 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_PHI1 j)"
  unfolding tm_PHI1_def using assms tm_Psigamma_tm tm_setn_tm tm_extendl_tm by simp

locale turing_machine_PHI1 =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_setn (j + 2) 1"
definition "tm2 \<equiv> tm1 ;; tm_Psigamma j"
definition "tm3 \<equiv> tm2 ;; tm_extendl 1 (j + 6)"

lemma tm3_eq_tm_PHI1: "tm3 = tm_PHI1 j"
  using tm3_def tm2_def tm1_def tm_PHI1_def by simp

context
  fixes tps0 :: "tape list" and k idx H :: nat and nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j" "j + 7 < k"
    and H: "H \<ge> 3"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 12"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def jk)
  show "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 jk canrepr_0 by simp
  show "ttt = 10 + 2 * nlength 0 + 2 * nlength 1"
    using assms canrepr_1 by simp
qed

definition "tps2 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi 0 H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 12 + 1851 * H ^ 4"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps0 H tps1_def tps2_def jk)
  show "ttt = 12 + 1851 * H ^ 4 * (nlength (Suc 0))\<^sup>2"
    using canrepr_1 assms by simp
qed

definition "tps3 \<equiv> tps0
  [j + 2 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi 0 H 1\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   1 := nlltape (nss @ nll_Psi 0 H 1)]"

lemma tm3:
  assumes "ttt = 16 + 1851 * H ^ 4 + 2 * nlllength (nll_Psi 0 H 1)"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def by (tform tps: tps0 H tps2_def tps3_def jk time: assms)

lemma tm3':
  assumes "ttt = 1875 * H ^ 4"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  let ?ttt = "16 + 1851 * H ^ 4 + 2 * nlllength (nll_Psi 0 H 1)"
  have "?ttt \<le> 16 + 1851 * H ^ 4 + 2 * H * (3 + nlength H)"
    using nlllength_nll_Psi_le
    by (metis (mono_tags, lifting) add_left_mono mult.assoc nat_mult_le_cancel1 plus_nat.add_0 rel_simps(51))
  also have "... = 16 + 1851 * H ^ 4 + 6 * H + 2 * H * nlength H"
    by algebra
  also have "... \<le> 16 + 1851 * H ^ 4 + 6 * H + 2 * H * H"
    using nlength_le_n by simp
  also have "... \<le> 16 + 1851 * H ^ 4 + 6 * H * H + 2 * H * H"
    by simp
  also have "... = 16 + 1851 * H ^ 4 + 8 * H^2"
    by algebra
  also have "... \<le> 16 + 1851 * H ^ 4 + 8 * H^4"
    using pow_mono'[of 2 4 H] by simp
  also have "... = 16 + 1859 * H ^ 4"
    by simp
  also have "... \<le> 16 * H^4 + 1859 * H ^ 4"
    using H by simp
  also have "... = 1875 * H ^ 4"
    by simp
  finally have "?ttt \<le> 1875 * H ^ 4" .
  then show ?thesis
    using assms tm3 transforms_monotone by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_PHI1 *)

lemma transforms_tm_PHI1I:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k H :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 7 < k" and "H \<ge> 3"
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
       1 := nlltape (nss @ nll_Psi 0 H 1)]"
  assumes "ttt = 1875 * H ^ 4"
  shows "transforms (tm_PHI1 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI1 j .
  show ?thesis
    using loc.tps3_def loc.tm3' loc.tm3_eq_tm_PHI1 assms by metis
qed


subsection \<open>A Turing machine for $\Phi_2$\<close>

text \<open>
The next TM expects a number $i$ on tape $j$ and a number $H$ on tape $j + 1$.
It appends to the formula on tape~$1$ the formula $\Psi([(2i+1)H, (2i+2)H), 3)
\land \Psi([(2i+2)H, (2i+3)H), 3)$.
\<close>

definition tm_PHI2 :: "tapeidx \<Rightarrow> machine" where
  "tm_PHI2 j \<equiv>
    tm_times2 j ;;
    tm_incr j ;;
    tm_setn (j + 2) 3 ;;
    tm_Psigamma j ;;
    tm_extendl_erase 1 (j + 6) ;;
    tm_incr j ;;
    tm_Psigamma j ;;
    tm_extendl 1 (j + 6)"

lemma tm_PHI2_tm:
  assumes "0 < j" and "j + 8 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_PHI2 j)"
  unfolding tm_PHI2_def
  using assms tm_Psigamma_tm tm_extendl_tm tm_erase_cr_tm tm_times2_tm tm_incr_tm tm_setn_tm tm_cr_tm tm_extendl_erase_tm
  by simp

locale turing_machine_PHI2 =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_times2 j"
definition "tm2 \<equiv> tm1 ;; tm_incr j"
definition "tm3 \<equiv> tm2 ;; tm_setn (j + 2) 3"
definition "tm4 \<equiv> tm3 ;; tm_Psigamma j"
definition "tm5 \<equiv> tm4 ;; tm_extendl_erase 1 (j + 6)"
definition "tm7 \<equiv> tm5 ;; tm_incr j"
definition "tm8 \<equiv> tm7 ;; tm_Psigamma j"
definition "tm9 \<equiv> tm8 ;; tm_extendl 1 (j + 6)"

lemma tm9_eq_tm_PHI2: "tm9 = tm_PHI2 j"
  using tm9_def tm8_def tm7_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_PHI2_def
  by simp

context
  fixes tps0 :: "tape list" and k idx H :: nat and nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j" "j + 7 < k"
    and H: "H \<ge> 3"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j := (\<lfloor>2 * idx\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 5 + 2 * nlength idx"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def by (tform tps: tps0 tps1_def jk assms)

definition "tps2 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 1\<rfloor>\<^sub>N, 1)]"

lemma tm2:
  assumes "ttt = 10 + 2 * nlength idx + 2 * nlength (2 * idx)"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: tps0 H tps1_def tps2_def jk assms)

lemma tm2' [transforms_intros]:
  assumes "ttt = 12 + 4 * nlength idx"
  shows "transforms tm2 tps0 ttt tps2"
proof -
  have "10 + 2 * nlength idx + 2 * nlength (2 * idx) \<le> 10 + 2 * nlength idx + 2 * (Suc (nlength idx))"
    using nlength_times2 by (meson add_left_mono mult_le_mono2)
  then have "10 + 2 * nlength idx + 2 * nlength (2 * idx) \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm2 transforms_monotone by simp
qed

definition "tps3 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 1\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 26 + 4 * nlength idx"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps0 H tps2_def tps3_def jk)
  show "tps2 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps2_def jk canrepr_0 tps0 by simp
  show "ttt = 12 + 4 * nlength idx + (10 + 2 * nlength 0 + 2 * nlength 3)"
    using nlength_3 assms by simp
qed

definition "tps4 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 1\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (Suc (2 * idx) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 26 + 4 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: tps0 H tps3_def tps4_def jk time: assms)

definition "tps5 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 1\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>[]\<rfloor>, 1),
   1 := nlltape (nss @ nll_Psi (H + 2 * idx * H) H 3)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 37 + 4 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3)"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform tps: tps0 H tps4_def tps5_def jk time: assms)

definition "tps7 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 2\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>[]\<rfloor>, 1),
   1 := nlltape (nss @ nll_Psi (H + 2 * idx * H) H 3)]"

lemma tm7:
  assumes "ttt = 42 + 4 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
    4 * nlllength (nll_Psi (H + 2 * idx * H) H 3) + 2 * nlength (Suc (2 * idx))"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def
proof (tform tps: tps0 H tps5_def tps7_def jk time: assms)
  show "tps7 = tps5[j := (\<lfloor>Suc (Suc (2 * idx))\<rfloor>\<^sub>N, 1)]"
    using tps5_def tps7_def jk by (simp add: list_update_swap)
qed

lemma tm7' [transforms_intros]:
  assumes "ttt = 44 + 6 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3)"
  shows "transforms tm7 tps0 ttt tps7"
proof -
  let ?ttt = "42 + 4 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3) +
      2 * nlength (Suc (2 * idx))"
  have "?ttt \<le> 42 + 4 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3) +
      2 * (Suc (nlength idx))"
    using nlength_times2plus1 by (metis add.commute add_left_mono mult_le_mono2 plus_1_eq_Suc)
  then have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm7 transforms_monotone by simp
qed

definition "tps8 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 2\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * idx)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   1 := nlltape (nss @ nll_Psi (H + 2 * idx * H) H 3)]"

lemma tm8 [transforms_intros]:
  assumes "ttt = 44 + 6 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def
proof (tform tps: tps0 H tps7_def tps8_def jk time: assms)
  show "tps8 = tps7
      [j + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * idx)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
    unfolding tps8_def tps7_def by (simp add: list_update_swap[of "j+6"])
qed

definition "tps9 \<equiv> tps0
  [j := (\<lfloor>2 * idx + 2\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (Suc (Suc (2 * idx)) * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1),
   1 := nlltape (nss @ nll_Psi (H + 2 * idx * H) H 3 @ nll_Psi (2 * H + 2 * idx * H) H 3)]"

lemma tm9:
  assumes "ttt = 48 + 6 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2 +
      2 * nlllength (nll_Psi (2 * H + 2 * idx * H) H 3)"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def by (tform tps: tps0 H tps9_def tps8_def jk time: assms)

lemma tm9':
  assumes "ttt = 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2"
  shows "transforms tm9 tps0 ttt tps9"
proof -
  let ?ttt = "48 + 6 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * nlllength (nll_Psi (H + 2 * idx * H) H 3) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2 +
      2 * nlllength (nll_Psi (2 * H + 2 * idx * H) H 3)"
  have "?ttt \<le> 48 + 6 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      4 * H * (3 + nlength (2 * H + 2 * idx * H + H)) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2 +
      2 * nlllength (nll_Psi (2 * H + 2 * idx * H) H 3)"
    using nlllength_nll_Psi_le'[of "H + 2 * idx * H" "2 * H + 2 * idx * H" H 3] by simp
  also have "... \<le> 48 + 6 * nlength idx + 1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      5 * H * (3 + nlength (2 * H + 2 * idx * H + H)) + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2 +
      3 * H * (3 + nlength (2 * H + 2 * idx * H + H))"
    using nlllength_nll_Psi_le'[of "2 * H + 2 * idx * H" "2 * H + 2 * idx * H" H 3] by simp
  also have "... = 48 + 6 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc (2 * idx))))\<^sup>2 +
      8 * H * (3 + nlength (2 * H + 2 * idx * H + H)) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2"
    by simp
  also have "... \<le> 48 + 6 * nlength idx +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2 +
      8 * H * (3 + nlength (2 * H + 2 * idx * H + H)) +
      1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2"
    using H4_nlength H by simp
  also have "... = 48 + 6 * nlength idx + 3702 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * idx)))))\<^sup>2 +
      8 * H * (3 + nlength (3 * H + 2 * idx * H))"
    by simp
  also have "... \<le> 48 + 6 * nlength idx + 3702 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2 +
      8 * H * (3 + nlength (3 * H + 2 * idx * H))"
  proof -
    have "Suc (Suc (Suc (2 * idx))) \<le> 3 * H + 2 * idx * H"
      using H
      by (metis One_nat_def Suc3_eq_add_3 Suc_eq_plus1_left add_leD1 comm_monoid_mult_class.mult_1
        distrib_right mult.commute mult_le_mono1)
    then have "nlength (Suc (Suc (Suc (2 * idx)))) \<le> 3 + nlength (3 * H + 2 * idx * H)"
      using nlength_mono trans_le_add2 by blast
    then show ?thesis
      by simp
  qed
  also have "... \<le> 48 + 6 * nlength idx + 3702 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2 +
      8 * H^4 * (3 + nlength (3 * H + 2 * idx * H))"
    using linear_le_pow by simp
  also have "... \<le> 48 + 6 * nlength idx + 3702 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2 +
      8 * H^4 * (3 + nlength (3 * H + 2 * idx * H))^2"
    using linear_le_pow by simp
  also have "... = 48 + 6 * nlength idx + 3710 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2"
    by simp
  also have "... \<le> 48 + 3716 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2"
  proof -
    have "nlength idx \<le> nlength (3 * H + 2 * idx * H)"
      using H by (intro nlength_mono) (simp add: trans_le_add2)
    also have "... \<le> 3 + nlength (3 * H + 2 * idx * H)"
      by simp
    also have "... \<le> (3 + nlength (3 * H + 2 * idx * H)) ^ 2"
      using linear_le_pow by simp
    also have "... \<le> H ^ 4 * (3 + nlength (3 * H + 2 * idx * H)) ^ 2"
      using H by simp
    finally have "nlength idx \<le> H ^ 4 * (3 + nlength (3 * H + 2 * idx * H)) ^ 2" .
    then show ?thesis
      by simp
  qed
  also have "... \<le> 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2"
  proof -
    have "1 \<le> nlength (3 * H + 2 * idx * H)"
      using H nlength_0
      by (metis One_nat_def Suc_leI add_eq_0_iff_both_eq_0 length_0_conv length_greater_0_conv mult_Suc
        not_numeral_le_zero numeral_3_eq_3)
    also have "... \<le> 3 + nlength (3 * H + 2 * idx * H)"
      by simp
    also have "... \<le> (3 + nlength (3 * H + 2 * idx * H)) ^ 2"
      using linear_le_pow by simp
    also have "... \<le> H ^ 4 * (3 + nlength (3 * H + 2 * idx * H)) ^ 2"
      using H by simp
    finally have "1 \<le> H ^ 4 * (3 + nlength (3 * H + 2 * idx * H)) ^ 2" .
    then show ?thesis
      by simp
  qed
  finally have "?ttt \<le> 3764 * H ^ 4 * (3 + nlength (3 * H + 2 * idx * H))\<^sup>2" .
  then show ?thesis
    using assms tm9 transforms_monotone by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_PHI2 *)

lemma transforms_tm_PHI2I:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k idx H :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 8 < k"
    and "H \<ge> 3"
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
     1 := nlltape (nss @ nll_Psi (H + 2 * idx * H) H 3 @ nll_Psi (2 * H + 2 * idx * H) H 3)]"
  shows "transforms (tm_PHI2 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI2 j .
  show ?thesis
    using loc.tm9' loc.tps9_def loc.tm9_eq_tm_PHI2 assms by simp
qed


subsection \<open>Turing machines for $\Phi_3$, $\Phi_4$, and $\Phi_5$\<close>

text \<open>
The CNF formulas $\Phi_3$, $\Phi_4$, and $\Phi_5$ have a similar structure and
can thus be handled by the same Turing machine. The following TM has a parameter
$step$ and the usual tape parameter $j$. It expects on tape $j$ a number $idx$,
on tape $j + 1$ a number $H$, on tape $j + 2$ a number $\kappa$, and on tape $j
+ 8$ the number $idx + step \cdot numiter$ for some number $numiter$. It appends
to the CNF formula on tape~$1$ the formula $\Psi(\gamma_{idx}, \kappa) \land
\Psi(\gamma_{idx + step\cdot (numiter - 1)}, \kappa)$, where $\gamma_i = [iH,
(i+1)H)$.

\null
\<close>

definition tm_PHI345 :: "nat \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_PHI345 step j \<equiv>
    WHILE tm_equalsn j (j + 8) (j + 3) ; \<lambda>rs. rs ! (j + 3) = \<box> DO
      tm_Psigamma j ;;
      tm_extendl_erase 1 (j + 6) ;;
      tm_plus_const step j
    DONE"

lemma tm_PHI345_tm:
  assumes "G \<ge> 6" and "0 < j" and "j + 8 < k"
  shows "turing_machine k G (tm_PHI345 step j)"
  unfolding tm_PHI345_def
  using assms tm_equalsn_tm tm_Psigamma_tm tm_extendl_erase_tm tm_plus_const_tm
    turing_machine_loop_turing_machine
  by simp

locale turing_machine_PHI345 =
  fixes step :: nat and j :: tapeidx
begin

definition "tmC \<equiv> tm_equalsn j (j + 8) (j + 3)"
definition "tm1 \<equiv> tm_Psigamma j"
definition "tm2 \<equiv> tm1 ;; tm_extendl_erase 1 (j + 6)"
definition "tm4 \<equiv> tm2 ;; tm_plus_const step j"
definition "tmL \<equiv> WHILE tmC ; \<lambda>rs. rs ! (j + 3) = \<box> DO tm4 DONE"

lemma tmL_eq_tm_PHI345: "tmL = tm_PHI345 step j"
  unfolding tmL_def tm4_def tm2_def tm1_def tm_PHI345_def tmC_def by simp

context
  fixes tps0 :: "tape list" and numiter H k idx kappa :: nat and nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j" "j + 8 < k"
    and H: "H \<ge> 3"
    and kappa: "kappa \<le> H"
    and step: "step > 0"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>kappa\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 8) = (\<lfloor>idx + step * numiter\<rfloor>\<^sub>N, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t]))]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
proof -
  have "\<lfloor>idx\<rfloor>\<^sub>N = \<lfloor>idx + step * 0\<rfloor>\<^sub>N"
    by simp
  moreover have "nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<0])) = nlltape nss"
    using nllcontents_Nil by simp
  ultimately show ?thesis
    using tpsL_def tps0 jk by (metis list_update_id)
qed

definition tpsC :: "nat \<Rightarrow> tape list" where
  "tpsC t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t])),
     j + 3 := (\<lfloor>t = numiter\<rfloor>\<^sub>B, 1)]"

lemma tmC:
  assumes "t \<le> numiter"
    and "ttt = 3 * nlength (idx + step * t) + 7"
  shows "transforms tmC (tpsL t) ttt (tpsC t)"
  unfolding tmC_def
proof (tform tps: tps0 tpsL_def jk)
  show "tpsL t ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using canrepr_0 jk tpsL_def tps0 by simp
  show "(0::nat) \<le> 1"
    by simp
  show "tpsC t = (tpsL t)
      [j + 3 := (\<lfloor>idx + step * t = idx + step * numiter\<rfloor>\<^sub>B, 1)]"
    using step tpsC_def jk tpsL_def tps0 by simp
  show "ttt = 3 * nlength (min (idx + step * t) (idx + step * numiter)) + 7"
    using assms by (simp add: min_def)
qed

lemma tmC' [transforms_intros]:
  assumes "t \<le> numiter"
    and "ttt = 3 * nlength (idx + step * numiter) + 7"
  shows "transforms tmC (tpsL t) ttt (tpsC t)"
proof -
  have "3 * nlength (idx + step * t) + 7 \<le> ttt"
    using assms nlength_mono by simp
  then show ?thesis
    using assms tmC transforms_monotone by blast
qed

definition tpsL0 :: "nat \<Rightarrow> tape list" where
  "tpsL0 t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t]))]"

lemma tpsL0_eq_tpsC:
  assumes "t < numiter"
  shows "tpsL0 t = tpsC t"
  unfolding tpsL0_def tpsC_def
  using assms jk ncontents_0 tps0 list_update_id[of tps0 "j + 3"]
  by (simp add: list_update_swap)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t])),
     j + 6 := (\<lfloor>nll_Psi ((idx+step*t) * H) H kappa\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm1 [transforms_intros]:
  assumes "t < numiter"
    and "ttt = 1851 * H ^ 4 * (nlength (Suc (idx+step*t)))\<^sup>2"
  shows "transforms tm1 (tpsL0 t) ttt (tpsL1 t)"
  unfolding tm1_def by (tform tps: H kappa tps0 tpsL0_def tpsL1_def jk time: assms(2))

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t])),
     j + 6 := (\<lfloor>[]\<rfloor>, 1),
     1 := nlltape ((nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t])) @ nll_Psi ((idx+step*t) * H) H kappa)]"

lemma tm2:
  assumes "t < numiter"
    and "ttt = 1851 * H ^ 4 * (nlength (Suc (idx + step * t)))\<^sup>2 +
      (11 + 4 * nlllength (nll_Psi ((idx + step * t) * H) H kappa))"
  shows "transforms tm2 (tpsL0 t) ttt (tpsL2 t)"
  unfolding tm2_def by (tform tps: assms H kappa tps0 tpsL1_def tpsL2_def jk)

definition tpsL2' :: "nat \<Rightarrow> tape list" where
  "tpsL2' t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>[]\<rfloor>, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t]) @ nll_Psi ((idx+step*t) * H) H kappa)]"

lemma tpsL2': "tpsL2 t = tpsL2' t"
  unfolding tpsL2_def tpsL2'_def by (simp only: list_update_swap list_update_overwrite) simp

lemma tm2':
  assumes "t < numiter"
    and "ttt = 1851 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 +
      (11 + 4 * nlllength (nll_Psi ((idx + step * t) * H) H kappa))"
  shows "transforms tm2 (tpsL0 t) ttt (tpsL2' t)"
proof -
  let ?ttt = "1851 * H ^ 4 * (nlength (Suc (idx + step * t)))\<^sup>2 +
      (11 + 4 * nlllength (nll_Psi ((idx + step * t) * H) H kappa))"
  have "?ttt \<le> 1851 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 +
      (11 + 4 * nlllength (nll_Psi ((idx + step * t) * H) H kappa))"
  proof -
    have "Suc (idx + step * t) \<le> Suc (idx + step * (numiter - 1))"
      using assms(1) step by simp
    also have "... = Suc (idx + step * numiter - step)"
      by (metis Nat.add_diff_assoc One_nat_def Suc_le_eq add_less_same_cancel1 assms(1) mult.right_neutral
       nat_mult_le_cancel_disj nat_neq_iff not_add_less1 right_diff_distrib')
    also have "... \<le> idx + step * numiter"
      using step Suc_le_eq assms(1) by simp
    finally have "Suc (idx + step * t) \<le> idx + step * numiter" .
    then have "nlength (Suc (idx + step * t)) \<le> nlength (idx + step * numiter)"
      using nlength_mono by simp
    then show ?thesis
      by simp
  qed
  then have "transforms tm2 (tpsL0 t) ttt (tpsL2 t)"
    using assms tm2 transforms_monotone by blast
  then show ?thesis
    using tpsL2' by simp
qed

definition tpsL2'' :: "nat \<Rightarrow> tape list" where
  "tpsL2'' t \<equiv> tps0
    [j := (\<lfloor>idx + step * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<Suc t])),
     j + 6 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tpsL2'': "tpsL2'' t = tpsL2' t"
proof -
  have "nll_Psi ((idx+step*t) * H) H kappa = nll_Psi (H * (idx+step*t)) H kappa"
    by (simp add: mult.commute)
  then have "concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<t]) @ nll_Psi ((idx+step*t) * H) H kappa =
      concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<Suc t])"
    by simp
  then show "tpsL2'' t = tpsL2' t"
    using tpsL2'_def tpsL2''_def by (simp add: list_update_swap)
qed

lemma nlllength_nll_Psi:
  assumes "t < numiter"
  shows "nlllength (nll_Psi ((idx + step * t) * H) H kappa) \<le> 5 * H ^ 4 * nlength (idx + step * numiter)^2"
proof -
  have "nlllength (nll_Psi ((idx + step * t) * H) H kappa) \<le> H * (3 + nlength ((idx + step * t) * H + H))"
    using nlllength_nll_Psi_le by simp
  also have "... \<le> H * (3 + nlength ((idx + step * numiter) * H))"
  proof -
    have "(idx + 1 + step * t) \<le> (idx + step * Suc t)"
      using step by simp
    then have "(idx + 1 + step * t) \<le> (idx + step * numiter)"
      using assms(1) Suc_le_eq by auto
    then have "(idx + 1 + step * t) * H \<le> (idx + step * numiter) * H"
      using mult_le_cancel2 by blast
    then show ?thesis
      using nlength_mono by simp
  qed
  also have "... = 3 * H + H * nlength ((idx + step * numiter) * H)"
    by algebra
  also have "... \<le> 3 * H + H * (nlength (idx + step * numiter) + nlength H)"
    using nlength_prod by simp
  also have "... \<le> 3 * H + H * (nlength (idx + step * numiter) + H)"
    using nlength_le_n by simp
  also have "... = 3 * H + H ^ 2 + H * nlength (idx + step * numiter)"
    by algebra
  also have "... \<le> 3 * H^4 + H ^ 2 + H * nlength (idx + step * numiter)"
    using linear_le_pow by simp
  also have "... \<le> 3 * H^4 + H ^ 4 + H * nlength (idx + step * numiter)"
    using pow_mono' by simp
  also have "... \<le> 4 * H^4 + H ^ 4 * nlength (idx + step * numiter)"
    using linear_le_pow by simp
  also have "... \<le> 4 * H^4 + H ^ 4 * nlength (idx + step * numiter)^2"
    using linear_le_pow by simp
  also have "... \<le> 5 * H ^ 4 * nlength (idx + step * numiter)^2"
  proof -
    have "idx + step * numiter > 0"
      using assms(1) step by simp
    then have "nlength (idx + step * numiter) > 0"
      using nlength_0 by simp
    then have "nlength (idx + step * numiter) ^ 2 > 0"
      by simp
    then have "H ^ 4 \<le> H ^ 4 * nlength (idx + step * numiter) ^ 2"
      by (metis One_nat_def Suc_leI mult_numeral_1_right nat_mult_le_cancel_disj numerals(1))
    then show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma tm2'' [transforms_intros]:
  assumes "t < numiter" and "ttt = 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11"
  shows "transforms tm2 (tpsL0 t) ttt (tpsL2'' t)"
proof -
  have "transforms tm2 (tpsL0 t) ttt (tpsL2' t)"
    using tm2'[OF assms(1)] nlllength_nll_Psi[OF assms(1)] transforms_monotone assms(2) by simp
  then show ?thesis
    using tpsL2' tpsL2'' by simp
qed

definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
    [j := (\<lfloor>idx + step * Suc t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<Suc t])),
     j + 6 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm4:
  assumes "t < numiter"
    and "ttt = 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * (5 + 2 * nlength (idx + step * t + step))"
  shows "transforms tm4 (tpsL0 t) ttt (tpsL4 t)"
  unfolding tm4_def
proof (tform tps: assms(1) H kappa tps0 tpsL2''_def tpsL4_def jk)
  have "idx + step * Suc t = idx + step * t + step"
    by simp
  then show "tpsL4 t = (tpsL2'' t)[j := (\<lfloor>idx + step * t + step\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL4_def tpsL2''_def using jk by (simp only: list_update_swap[of _ j] list_update_overwrite)
  show "ttt = 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * (5 + 2 * nlength (idx + step * t + step))"
    using assms(2) .
qed

lemma tm4':
  assumes "t < numiter"
    and "ttt = (6 * step + 1882) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2"
  shows "transforms tm4 (tpsC t) ttt (tpsL4 t)"
proof -
  let ?ttt = "1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * (5 + 2 * nlength (idx + step * t + step))"
  have "idx + step * t + step \<le> idx + step * numiter"
    using assms(1)
    by (metis Suc_le_eq add.assoc add.commute add_le_cancel_left add_mult_distrib2 mult_le_mono2 mult_numeral_1_right numerals(1) plus_1_eq_Suc)
  then have "?ttt \<le> 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * (5 + 2 * nlength (idx + step * numiter))"
    using nlength_mono by simp
  also have "... = 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * 5 + step * 2 * nlength (idx + step * numiter)"
    by algebra
  also have "... \<le> 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * 5 + step * 2 * nlength (idx + step * numiter)^2"
    by (simp add: linear_le_pow)
  also have "... \<le> 1871 * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + 11 +
      step * 5 + step * H^4 * nlength (idx + step * numiter)^2"
  proof -
    have "2 < H"
      using H by simp
    then have "2 < H ^ 4"
      using linear_le_pow by (meson le_trans not_less zero_less_numeral)
    then show ?thesis
      by simp
  qed
  also have "... = (step + 1871) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + (11 + step * 5)"
    by algebra
  also have "... \<le> (step + 1871) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2 + (11 + step * 5) * H ^ 4 * (nlength (idx + step * numiter))^2"
  proof -
    have "H ^ 4 * (nlength (idx + step * numiter))^2 > 0"
      using step assms(1) nlength_0 H by auto
    then show ?thesis
      by (smt (z3) One_nat_def Suc_leI add_mono_thms_linordered_semiring(2) mult.assoc mult_numeral_1_right nat_mult_le_cancel_disj numeral_code(1))
  qed
  also have "... = (6 * step + 1882) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2"
    by algebra
  finally have "?ttt \<le> (6 * step + 1882) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2" .
  then have "transforms tm4 (tpsL0 t) ttt (tpsL4 t)"
    using tm4 assms transforms_monotone by blast
  then show ?thesis
    using tpsL0_eq_tpsC assms(1) by simp
qed

lemma tm4'' [transforms_intros]:
  assumes "t < numiter"
    and "ttt = (6 * step + 1882) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2"
  shows "transforms tm4 (tpsC t) ttt (tpsL (Suc t))"
proof -
  have "tpsL4 t = tpsL (Suc t)"
    using tpsL4_def tpsL_def jk tps0 list_update_id[of tps0 "j + 6"]
    by (simp add: list_update_swap)
  then show ?thesis
    using tm4' assms by metis
qed

lemma tmL:
  assumes "ttt = Suc numiter * (9 + (6 * step + 1885) * (H ^ 4 * (nlength (idx + step * numiter))\<^sup>2))"
    and "nn = numiter"
  shows "transforms tmL (tpsL 0) ttt (tpsC nn)"
  unfolding tmL_def
proof (tform tps: assms(2))
  let ?ttt = "(6 * step + 1882) * H ^ 4 * (nlength (idx + step * numiter))\<^sup>2"
  show "\<And>t. t < nn \<Longrightarrow> read (tpsC t) ! (j + 3) = \<box>"
    using assms(2) tpsC_def jk read_ncontents_eq_0 by simp
  show "read (tpsC nn) ! (j + 3) \<noteq> \<box>"
    using assms(2) tpsC_def jk read_ncontents_eq_0 by simp
  show "nn * (3 * nlength (idx + step * numiter) + 7 + ?ttt + 2) + (3 * nlength (idx + step * numiter) + 7) + 1 \<le> ttt"
    (is "?lhs \<le> ttt")
  proof -
    let ?g = "H ^ 4 * (nlength (idx + step * numiter))\<^sup>2"
    have "nlength (idx + step * numiter) \<le> nlength (idx + step * numiter)^2"
      using linear_le_pow by simp
    moreover have "H ^ 4 > 0"
      using H by simp
    ultimately have *: "nlength (idx + step * numiter) \<le> ?g"
      by (metis ab_semigroup_mult_class.mult_ac(1) le_square mult.left_commute nat_mult_le_cancel_disj power2_eq_square)
    have "?lhs = numiter * (3 * nlength (idx + step * numiter) + 9 + ?ttt) + 3 * nlength (idx + step * numiter) + 8"
      using assms(2) by simp
    also have "... \<le> numiter * (3 * nlength (idx + step * numiter) + 9 + ?ttt) + 3 * ?g + 8"
      using * by simp
    also have "... \<le> numiter * (3 * ?g + 9 + (6 * step + 1882) * ?g) + 3 * ?g + 8"
      using * by simp
    also have "... = numiter * (9 + (6 * step + 1885) * ?g) + 3 * ?g + 8"
      by algebra
    also have "... \<le> numiter * (9 + (6 * step + 1885) * ?g) + (6 * step + 1885) * ?g + 8"
      by simp
    also have "... \<le> numiter * (9 + (6 * step + 1885) * ?g) + (9 + (6 * step + 1885) * ?g)"
      by simp
    also have "... = Suc numiter * (9 + (6 * step + 1885) * ?g)"
      by simp
    finally show ?thesis
      using assms(1) by simp
  qed
qed

lemma tmL':
  assumes "ttt = Suc numiter * (9 + (6 * step + 1885) * (H ^ 4 * (nlength (idx + step * numiter))\<^sup>2))"
  shows "transforms tmL tps0 ttt (tpsC numiter)"
  using assms tmL tpsL_eq_tps0 by simp

end  (* context tps0 *)

end  (* locale turing_machine_PHI345 *)

lemma transforms_tm_PHI345I:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt step numiter H k idx kappa :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 8 < k"
    and "H \<ge> 3"
    and "kappa \<le> H"
    and "step > 0"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>kappa\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 8) = (\<lfloor>idx + step * numiter\<rfloor>\<^sub>N, 1)"
  assumes "ttt = Suc numiter * (9 + (6 * step + 1885) * (H ^ 4 * (nlength (idx + step * numiter))\<^sup>2))"
  assumes "tps' = tps
    [j := (\<lfloor>idx + step * numiter\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (idx + step * i)) H kappa) [0..<numiter])),
     j + 3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_PHI345 step j) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI345 step j .
  show ?thesis
    using assms loc.tmL' loc.tpsC_def loc.tmL_eq_tm_PHI345 by simp
qed


subsection \<open>A Turing machine for $\Phi_6$\<close>

text \<open>
The next Turing machine expects a symbol sequence $zs$ on input tape~$0$, the
number~$2$ on tape $j$, and a number $H$ on tape $j + 1$. It appends to the CNF
formula on tape~$1$ the formula $\bigwedge_{i=0}^{|zs| - 1} \Psi(\gamma_{2+2i},
z_i)$, where $z_i$ is $2$ or $3$ if $zs_i$ is \textbf{0} or \textbf{1},
respectively.
\<close>

definition tm_PHI6 :: "tapeidx \<Rightarrow> machine" where
  "tm_PHI6 j \<equiv>
    WHILE [] ; \<lambda>rs. rs ! 0 \<noteq> \<box> DO
      IF \<lambda>rs. rs ! 0 = \<zero> THEN
        tm_setn (j + 2) 2
      ELSE
        tm_setn (j + 2) 3
      ENDIF ;;
      tm_Psigamma j ;;
      tm_extendl_erase 1 (j + 6) ;;
      tm_setn (j + 2) 0 ;;
      tm_right 0 ;;
      tm_plus_const 2 j
    DONE"

lemma tm_PHI6_tm:
  assumes "G \<ge> 6" and "0 < j" and "j + 7 < k"
  shows "turing_machine k G (tm_PHI6 j)"
  unfolding tm_PHI6_def
  using assms tm_Psigamma_tm tm_extendl_erase_tm tm_plus_const_tm
    turing_machine_loop_turing_machine turing_machine_branch_turing_machine
    tm_right_tm tm_setn_tm Nil_tm
  by simp

locale turing_machine_PHI6 =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> IF \<lambda>rs. rs ! 0 = \<zero> THEN tm_setn (j + 2) 2 ELSE tm_setn (j + 2) 3 ENDIF"
definition "tm2 \<equiv> tm1 ;; tm_Psigamma j"
definition "tm3 \<equiv> tm2 ;; tm_extendl_erase 1 (j + 6)"
definition "tm4 \<equiv> tm3 ;; tm_setn (j + 2) 0"
definition "tm5 \<equiv> tm4 ;; tm_right 0"
definition "tm6 \<equiv> tm5 ;; tm_plus_const 2 j"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! 0 \<noteq> \<box> DO tm6 DONE"

lemma tmL_eq_tm_PHI6: "tmL = tm_PHI6 j"
  using tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_PHI6_def tmL_def by simp

context
  fixes tps0 :: "tape list" and k H :: nat and zs :: "symbol list" and nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j" "j + 7 < k"
    and H: "H \<ge> 3"
    and zs: "bit_symbols zs"
  assumes tps0:
    "tps0 ! 0 = (\<lfloor>zs\<rfloor>, 1)"
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
begin

lemma H0: "H > 0"
  using H by simp

lemma H_mult: "x \<le> H * x" "x \<le> x * H"
  using H by simp_all

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc t),
     j := (\<lfloor>2 + 2 * t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (zs ! i)) [0..<t]))]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
proof -
  have "(\<lfloor>zs\<rfloor>, 1) = (\<lfloor>zs\<rfloor>, Suc 0)"
    by simp
  moreover have "nlltape (concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (zs ! i)) [0..<0])) = (\<lfloor>[]\<rfloor>, 1)"
    using nllcontents_Nil by simp
  moreover have "2 = Suc (Suc 0)"
    by simp
  ultimately show ?thesis
    using tpsL_def tps0 jk by simp (metis One_nat_def Suc_1 list_update_id)
qed

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc t),
     j := (\<lfloor>2 + 2 * t\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>zs ! t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (zs ! i)) [0..<t]))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 16" and "t < length zs"
  shows "transforms tm1 (tpsL t) ttt (tpsL1 t)"
  unfolding tm1_def
proof (tform tps: tpsL_def tps0 jk)
  have *: "read (tpsL t) ! 0 = zs ! t"
    using jk tpsL_def tapes_at_read'[of 0 "tpsL t"] assms(2) by simp
  show "read (tpsL t) ! 0 = \<zero> \<Longrightarrow> tpsL1 t = (tpsL t)[j + 2 := (\<lfloor>2\<rfloor>\<^sub>N, 1)]"
    using * tpsL_def tpsL1_def jk by (simp add: list_update_swap)
  show "tpsL1 t = (tpsL t)[j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1)]" if "read (tpsL t) ! \<box> \<noteq> \<zero>"
  proof -
    have "zs ! t = \<one>"
      using * that zs assms(2) by auto
    then show ?thesis
      using tpsL_def tpsL1_def jk by (simp add: list_update_swap)
  qed
  show "10 + 2 * nlength 0 + 2 * nlength 2 + 2 \<le> ttt"
    using nlength_0 nlength_2 assms(1) by simp
  show "10 + 2 * nlength 0 + 2 * nlength 3 + 1 \<le> ttt"
    using nlength_0 nlength_3 assms(1) by simp
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc t),
     j := (\<lfloor>2 + 2 * t\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>zs ! t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>nll_Psi (2 * H + 2 * t * H) H (zs ! t)\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc 0),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (zs ! i)) [0..<t]))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 16 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2"
    and "t < length zs"
  shows "transforms tm2 (tpsL t) ttt (tpsL2 t)"
  unfolding tm2_def
proof (tform tps: assms(2) tps0 H tpsL1_def tpsL2_def jk time: assms(1))
  show "zs ! t \<le> H"
    using assms(2) H zs by auto
qed

definition tpsL3 :: "nat \<Rightarrow> tape list" where
  "tpsL3 t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc t),
     j := (\<lfloor>2 + 2 * t\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>zs ! t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>[]\<rfloor>, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<Suc t]))]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 27 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t))"
    and "t < length zs"
  shows "transforms tm3 (tpsL t) ttt (tpsL3 t)"
  unfolding tm3_def
proof (tform tps: assms(2) tps0 H tpsL2_def tpsL3_def jk time: assms(1))
  have "nll_Psi (2 * H + H * (2 * t)) H = nll_Psi (2 * H + 2 * t * H) H"
    by (simp add: mult.commute)
  then have "(nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<t])) @
            nll_Psi (2 * H + 2 * t * H) H (zs ! t) =
        nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<Suc t])"
    using assms(2) by simp
  then show "tpsL3 t = (tpsL2 t)
      [1 := nlltape
            ((nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<t])) @
              nll_Psi (2 * H + 2 * t * H) H (zs ! t)),
       j + 6 := (\<lfloor>[]\<rfloor>, 1)]"
    unfolding tpsL3_def tpsL2_def jk by (simp add: list_update_swap)
qed

definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc t),
     j := (\<lfloor>2 + 2 * t\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>[]\<rfloor>, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<Suc t]))]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 41 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t))"
    and "t < length zs"
  shows "transforms tm4 (tpsL t) ttt (tpsL4 t)"
  unfolding tm4_def
proof (tform tps: assms(2) tpsL3_def tpsL4_def jk)
  have "zs ! t = 2 \<or> zs ! t = 3"
    using zs assms(2) by auto
  then show "ttt = 27 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t)) +
      (10 + 2 * nlength (zs ! t) + 2 * nlength 0)"
    using nlength_2 nlength_3 assms(1) by auto
qed

definition tpsL5 :: "nat \<Rightarrow> tape list" where
  "tpsL5 t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc (Suc t)),
     j := (\<lfloor>2 + 2 * t\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>[]\<rfloor>, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<Suc t]))]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 42 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t))"
    and "t < length zs"
  shows "transforms tm5 (tpsL t) ttt (tpsL5 t)"
  unfolding tm5_def
proof (tform tps: assms(2) tps0 H tpsL4_def tpsL5_def jk time: assms(1))
  have neq: "0 \<noteq> j"
    using jk by simp
  have "tpsL4 t ! 0 = (\<lfloor>zs\<rfloor>, Suc t)"
    using tpsL4_def jk by simp
  then show "tpsL5 t = (tpsL4 t)[0 := tpsL4 t ! 0 |+| 1]"
    unfolding tpsL5_def tpsL4_def jk by (simp add: list_update_swap[OF neq] list_update_swap[of _ 0])
qed

definition tpsL6 :: "nat \<Rightarrow> tape list" where
  "tpsL6 t \<equiv> tps0
    [0 := (\<lfloor>zs\<rfloor>, Suc (Suc t)),
     j := (\<lfloor>2 + 2 * (Suc t)\<rfloor>\<^sub>N, 1),
     j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>[]\<rfloor>, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (2 * H + H * (2 * i)) H (zs ! i)) [0..<Suc t]))]"

lemma tm6:
  assumes "ttt = 52 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t)) +
      4 * nlength (4 + 2 * t)"
    and "t < length zs"
  shows "transforms tm6 (tpsL t) ttt (tpsL6 t)"
  unfolding tm6_def
proof (tform tps: tps0 H tpsL5_def tpsL6_def jk assms(2))
  show "tpsL6 t = (tpsL5 t)[j := (\<lfloor>Suc (Suc (2 * t)) + 2\<rfloor>\<^sub>N, 1)]"
    using tpsL6_def tpsL5_def jk by (simp add: list_update_swap)
  have *: "4 + 2 * t = Suc (Suc (Suc (Suc (2 * t))))"
    by simp
  then show "ttt = 42 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t)) +
      2 * (5 + 2 * nlength (Suc (Suc (2 * t)) + 2))"
    using assms(1) * by simp
qed

lemma tpsL6_eq_tpsL: "tpsL6 t = tpsL (Suc t)"
proof -
  have "tpsL (Suc t) ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    using tpsL_def tps0 jk by simp
  then have "tpsL (Suc t) = (tpsL (Suc t))[j + 6 := (\<lfloor>[]\<rfloor>, 1)]"
    using list_update_id by metis
  moreover have "tpsL (Suc t) ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL_def tps0 jk canrepr_0 by simp
  ultimately have "tpsL (Suc t) = (tpsL (Suc t))[j + 6 := (\<lfloor>[]\<rfloor>, 1), j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using list_update_id by metis
  moreover have "tpsL6 t = (tpsL (Suc t))[j + 6 := (\<lfloor>[]\<rfloor>, 1), j + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL6_def tpsL_def by (simp add: list_update_swap)
  ultimately show ?thesis
    by simp
qed

lemma tm6':
  assumes "ttt = 133648 * H ^ 6 * length zs^2"
    and "t < length zs"
  shows "transforms tm6 (tpsL t) ttt (tpsL (Suc t))"
proof -
  have **: "Suc (2 * length zs)^2 \<le> 9 * length zs ^ 2"
  proof -
    have "Suc (2 * length zs)^2 = 1 + 2 * 2 * length zs + (2 * length zs)^2"
      by (metis add.commute add_Suc_shift mult.assoc nat_mult_1_right one_power2 plus_1_eq_Suc power2_sum)
    also have "... = 1 + 4 * length zs + 4 * length zs^2"
      by simp
    also have "... \<le> length zs + 4 * length zs + 4 * length zs^2"
      using assms(2) by simp
    also have "... = 5 * length zs + 4 * length zs^2"
      by simp
    also have "... \<le> 5 * length zs^2 + 4 * length zs^2"
      using linear_le_pow by simp
    also have "... = 9 * length zs^2"
      by simp
    finally show ?thesis
      by simp
  qed

  have *: "t \<le> length zs - 1"
    using assms(2) by simp

  let ?ttt = "52 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + 2 * t * H) H (zs ! t)) +
      4 * nlength (4 + 2 * t)"
  have "?ttt = 52 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + H * (2 * t)) H (zs ! t)) +
      4 * nlength (4 + 2 * t)"
    by (simp add: mult.commute)
  also have "... \<le> 52 + 1851 * H ^ 4 * (nlength (Suc (Suc (Suc (2 * t)))))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + H * (2 * t)) H (zs ! t)) +
      4 * nlength (2 + 2 * length zs)"
    using nlength_mono assms(2) by simp
  also have "... \<le> 52 + 1851 * H ^ 4 * (nlength (Suc (2 * length zs)))\<^sup>2 +
      4 * nlllength (nll_Psi (2 * H + H * (2 * t)) H (zs ! t)) +
      4 * nlength (2 + 2 * length zs)"
    using H4_nlength H assms(2) by simp
  also have "... \<le> 52 + 1851 * H ^ 4 * (nlength (Suc (2 * length zs)))\<^sup>2 +
      4 * H * (3 + nlength (3 * H + H * (2 * (length zs - 1)))) +
      4 * nlength (2 + 2 * length zs)"
    using nlllength_nll_Psi_le'[of "2 * H + H * (2 * t)" "2 * H + H * (2 * (length zs - 1))" H] *
    by simp
  also have "... = 52 + 1851 * H ^ 4 * (nlength (Suc (2 * length zs)))\<^sup>2 +
      4 * H * (3 + nlength (H * (1 + 2 * length zs))) + 4 * nlength (2 + 2 * length zs)"
  proof -
    have "3 * H + H * (2 * (length zs - 1)) = H * (3 + 2 * (length zs - 1))"
      by algebra
    also have "... = H * (3 + 2 * length zs - 2)"
      using assms(2)
      by (metis Nat.add_diff_assoc Suc_pred add_mono_thms_linordered_semiring(1) le_numeral_extra(4)
        length_greater_0_conv list.size(3) mult_2 nat_1_add_1 not_less_zero plus_1_eq_Suc
        right_diff_distrib' trans_le_add1)
    also have "... = H * (1 + 2 * length zs)"
      by simp
    finally have "3 * H + H * (2 * (length zs - 1)) = H * (1 + 2 * length zs)" .
    then show ?thesis
      by metis
  qed
  also have "... \<le> 52 + 1851 * H ^ 4 * (3 + nlength (Suc (2 * length zs)))\<^sup>2 +
      4 * H * (3 + nlength (H * (1 + 2 * length zs))) + 4 * nlength (2 + 2 * length zs)"
    by simp
  also have "... \<le> 52 + 1851 * H ^ 4 * (3 + nlength (H * Suc (2 * length zs)))\<^sup>2 +
      4 * H * (3 + nlength (H * Suc (2 * length zs))) + 4 * nlength (2 + 2 * length zs)"
  proof -
    have "Suc (2 * length zs) \<le> H * Suc (2 * length zs)"
      using H_mult by blast
    then have "nlength (Suc (2 * length zs))^2 \<le> nlength (H * Suc (2 * length zs))^2"
      using nlength_mono by simp
    then show ?thesis
      by simp
  qed
  also have "... \<le> 52 + 1851 * H ^ 4 * (3 + nlength (H * Suc (2 * length zs)))\<^sup>2 +
      4 * H * (3 + nlength (H * Suc (2 * length zs)))^2 + 4 * nlength (2 + 2 * length zs)"
    using linear_le_pow by simp
  also have "... \<le> 52 + 1851 * H ^ 4 * (3 + nlength (H * Suc (2 * length zs)))\<^sup>2 +
      4 * H^4 * (3 + nlength (H * Suc (2 * length zs)))^2 + 4 * nlength (2 + 2 * length zs)"
    using linear_le_pow by simp
  also have "... = 52 + 1855 * H ^ 4 * (3 + nlength (H * Suc (2 * length zs)))\<^sup>2 +
      4 * nlength (2 + 2 * length zs)"
    by simp
  also have "... \<le> 52 + 1855 * H ^ 4 * (3 + nlength (H * Suc (2 * length zs)))\<^sup>2 +
      4 * nlength (H * Suc (2 * length zs))"
  proof -
    have "2 + 2 * m \<le> H * Suc (2 * m)" if "m > 0" for m
      using H H_mult(2) by (metis Suc_leD add_mono eval_nat_numeral(3) mult.commute mult_Suc_right)
    then have "2 + 2 * length zs \<le> H * Suc (2 * length zs)"
      using assms(2) by (metis less_nat_zero_code not_gr_zero)
    then show ?thesis
      using nlength_mono by simp
  qed
  also have "... \<le> 52 + 1855 * H ^ 4 * (3 + H * Suc (2 * length zs))\<^sup>2 +
      4 * nlength (H * Suc (2 * length zs))"
    using nlength_le_n nlength_mono by simp
  also have "... \<le> 52 + 1855 * H ^ 4 * (3 + H * Suc (2 * length zs))\<^sup>2 +
      4 * (H * Suc (2 * length zs))"
    using nlength_le_n nlength_mono by (meson add_left_mono mult_le_cancel1)
  also have "... = 52 + 1855 * H ^ 4 * (3^2 + 2 * 3 * H * Suc (2 * length zs) + H^2 * Suc (2 * length zs)^2) +
      4 * (H * Suc (2 * length zs))"
    by algebra
  also have "... \<le> 52 + 1855 * H ^ 4 * (72 * H^2 * length zs^2) + 4 * (H * Suc (2 * length zs))"
  proof -
    have "3^2 + 2 * 3 * H * Suc (2 * length zs) + H^2 * Suc (2 * length zs)^2 =
        9 + 6 * H * Suc (2 * length zs) + H^2 * Suc (2 * length zs)^2"
      by simp
    also have "... \<le> 9 + 6 * H^2 * Suc (2 * length zs) + H^2 * Suc (2 * length zs)^2"
      using H linear_le_pow by (simp add: add_mono)
    also have "... \<le> 9 + 6 * H^2 * Suc (2 * length zs)^2 + H^2 * Suc (2 * length zs)^2"
      using linear_le_pow by (meson add_le_mono1 add_left_mono le_refl mult_le_mono zero_less_numeral)
    also have "... = 9 + 7 * H^2 * Suc (2 * length zs)^2"
      by simp
    also have "... \<le> 9 + 7 * H^2 * 9 * length zs^2"
      using ** by simp
    also have "... = 9 + 63 * H^2 * length zs^2"
      by simp
    also have "... \<le> 9 * H^2 * length zs^2 + 63 * H^2 * length zs^2"
      using assms(2) H by simp
    also have "... = 72 * H^2 * length zs^2"
      by simp
    finally have "3^2 + 2 * 3 * H * Suc (2 * length zs) + H^2 * Suc (2 * length zs)^2 \<le> 72 * H^2 * length zs^2" .
    then show ?thesis
      using add_le_mono le_refl mult_le_mono2 by presburger
  qed
  also have "... = 52 + 133560 * H ^ 6 * length zs^2 + 4 * (H * Suc (2 * length zs))"
    by simp
  also have "... \<le> 52 + 133560 * H ^ 6 * length zs^2 + 4 * (H * 9 * length zs ^ 2)"
    using ** by (smt (verit) add_left_mono mult.assoc mult_le_cancel1 power2_nat_le_imp_le)
  also have "... = 52 + 133560 * H ^ 6 * length zs^2 + 36 * H * length zs ^ 2"
    by simp
  also have "... \<le> 52 + 133560 * H ^ 6 * length zs^2 + 36 * H^6 * length zs ^ 2"
    using linear_le_pow by simp
  also have "... = 52 + 133596 * H ^ 6 * length zs^2"
    by simp
  also have "... \<le> 52 * H ^ 6 * length zs^2 + 133596 * H ^ 6 * length zs^2"
    using H assms(2) by simp
  also have "... = 133648 * H ^ 6 * length zs^2"
    by simp
  finally have "?ttt \<le> 133648 * H ^ 6 * length zs^2" .
  then have "transforms tm6 (tpsL t) ttt (tpsL6 t)"
    using tm6 assms transforms_monotone by blast
  then show ?thesis
    using tpsL6_eq_tpsL by simp
qed

lemma tmL:
  assumes "ttt = 133650 * H ^ 6 * length zs ^ 3 + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length zs))"
  unfolding tmL_def
proof (tform)
  let ?t = "133648 * H ^ 6 * length zs^2"
  show "\<And>i. i < length zs \<Longrightarrow> transforms tm6 (tpsL i) ?t (tpsL (Suc i))"
    using tm6' by simp
  have *: "read (tpsL t) ! 0 = \<lfloor>zs\<rfloor> (Suc t)" for t
    using jk tapes_at_read'[symmetric, of 0 "tpsL t"] by (simp add: tpsL_def)
  show "read (tpsL t) ! 0 \<noteq> \<box>" if "t < length zs" for t
  proof -
    have "read (tpsL t) ! 0 = zs ! t"
      using that * by simp
    then show ?thesis
      using that zs by auto
  qed
  show "\<not> read (tpsL (length zs)) ! 0 \<noteq> \<box>"
    using * by simp
  show "length zs * (?t + 2) + 1 \<le> ttt"
  proof (cases "length zs = 0")
    case True
    then show ?thesis
      using assms(1) by simp
  next
    case False
    then have "1 \<le> H^6 * length zs ^ 2"
      using H linear_le_pow by (simp add: Suc_leI)
    then have "?t + 2 \<le> 133650 * H ^ 6 * length zs^2"
      by simp
    then have "length zs * (?t + 2) \<le> length zs * 133650 * H ^ 6 * length zs^2"
      by simp
    then have "length zs * (?t + 2) \<le> 133650 * H ^ 6 * length zs^3"
      by (simp add: power2_eq_square power3_eq_cube)
    then show ?thesis
      using assms(1) by simp
  qed
qed

lemma tmL':
  assumes "ttt = 133650 * H ^ 6 * length zs ^ 3 + 1"
  shows "transforms tmL tps0 ttt (tpsL (length zs))"
  using assms tmL tpsL_eq_tps0 by simp

end

end  (* locale turing_machine_PHI6 *)

lemma transforms_tm_PHI6I:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k H :: nat and zs :: "symbol list" and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 7 < k"
    and "H \<ge> 3"
    and "bit_symbols zs"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! 0 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j = (\<lfloor>2\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
    [0 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
     j := (\<lfloor>2 + 2 * length zs\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>i. nll_Psi (H * (2 + 2 * i)) H (zs ! i)) [0..<length zs]))]"
  assumes "ttt = 133650 * H ^ 6 * length zs ^ 3 + 1"
  shows "transforms (tm_PHI6 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI6 j .
  show ?thesis
    using assms loc.tpsL_def loc.tmL' loc.tmL_eq_tm_PHI6 by simp
qed


subsection \<open>A Turing machine for $\Phi_7$\<close>

text \<open>
The next Turing machine expects a number $idx$ on tape $j$, a number $H$ on tape
$j + 1$, and a number $numiter$ on tape $j + 6$. It appends to the CNF formula
on tape~$1$ the formula $\bigwedge_{t=0}^{numiter} \Upsilon(\gamma_{idx + 2t})$
with $\gamma_i = [iH, (i+1)H)$. This equals $\Phi_7$ if $idx = 2n + 4$ and
$numiter = p(n)$.
\<close>

definition tm_PHI7 :: "tapeidx \<Rightarrow> machine" where
  "tm_PHI7 j \<equiv>
    WHILE [] ; \<lambda>rs. rs ! (j + 6) \<noteq> \<box> DO
      tm_Upsilongamma j ;;
      tm_extendl_erase 1 (j + 4) ;;
      tm_plus_const 2 j ;;
      tm_decr (j + 6)
    DONE"

lemma tm_PHI7_tm:
  assumes "0 < j" and "j + 6 < k" and "6 \<le> G" and "2 \<le> k"
  shows "turing_machine k G (tm_PHI7 j)"
  unfolding tm_PHI7_def
  using tm_Upsilongamma_tm tm_decr_tm Nil_tm tm_extendl_erase_tm tm_plus_const_tm assms turing_machine_loop_turing_machine
  by simp

locale turing_machine_tm_PHI7 =
  fixes step :: nat and j :: tapeidx
begin

definition "tmL1 \<equiv> tm_Upsilongamma j"
definition "tmL2 \<equiv> tmL1 ;; tm_extendl_erase 1 (j + 4)"
definition "tmL4 \<equiv> tmL2 ;; tm_plus_const 2 j"
definition "tmL5 \<equiv> tmL4 ;; tm_decr (j + 6)"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! (j + 6) \<noteq> \<box> DO tmL5 DONE"

lemma tmL_eq_tm_PHI7: "tmL = tm_PHI7 j"
  unfolding tmL_def tmL5_def tmL4_def tmL2_def tmL1_def tm_PHI7_def by simp

context
  fixes tps0 :: "tape list" and numiter H k idx :: nat and nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j" "j + 6 < k"
    and H: "H \<ge> 3"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>numiter\<rfloor>\<^sub>N, 1)"
begin

lemma nlength_H: "nlength H \<ge> 1"
  using nlength_0 H by (metis dual_order.trans nlength_1_simp nlength_mono one_le_numeral)

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j := (\<lfloor>idx + 2 * t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>numiter - t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<t]))]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
  using tpsL_def tps0 by auto (metis list_update_id)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j := (\<lfloor>idx + 2 * t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>numiter - t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<t])),
     j + 4 := (\<lfloor>nll_Upsilon (idx + 2 * t) H\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "t < numiter"
    and "ttt = 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def by (tform tps: H tps0 tpsL_def tpsL1_def jk time: assms(2))

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [j := (\<lfloor>idx + 2 * t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>numiter - t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<t]) @ (nll_Upsilon (idx + 2 * t) H)),
     j + 4 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmL2 [transforms_intros]:
  assumes "t < numiter"
    and "ttt = 11 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * nlllength (nll_Upsilon (idx + 2 * t) H)"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def by (tform tps: assms(1) H tps0 tpsL1_def tpsL2_def jk time: assms(2))

definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
    [j := (\<lfloor>idx + 2 * Suc t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>numiter - t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<t]) @ (nll_Upsilon (idx + 2 * t) H)),
     j + 4 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmL4 [transforms_intros]:
  assumes "t < numiter"
    and "ttt = 21 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * nlllength (nll_Upsilon (idx + 2 * t) H) + 4 * nlength (Suc (Suc (idx + 2 * t)))"
  shows "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
  unfolding tmL4_def
proof (tform tps: assms(1) H tps0 tpsL2_def tpsL4_def jk time: assms(2))
  show "tpsL4 t = (tpsL2 t)[j := (\<lfloor>idx + 2 * t + 2\<rfloor>\<^sub>N, 1)]"
    using tpsL4_def tpsL2_def jk by (simp add: list_update_swap[of j])
qed

definition tpsL5 :: "nat \<Rightarrow> tape list" where
  "tpsL5 t \<equiv> tps0
    [j := (\<lfloor>idx + 2 * Suc t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>numiter - Suc t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<t]) @ (nll_Upsilon (idx + 2 * t) H)),
     j + 4 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmL5:
  assumes "t < numiter"
    and "ttt = 29 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * nlllength (nll_Upsilon (idx + 2 * t) H) + 4 * nlength (Suc (Suc (idx + 2 * t))) +
      2 * nlength (numiter - t)"
  shows "transforms tmL5 (tpsL t) ttt (tpsL5 t)"
  unfolding tmL5_def
proof (tform tps: assms(1) H tps0 tpsL4_def tpsL5_def jk time: assms(2))
  show "tpsL5 t = (tpsL4 t)[j + 6 := (\<lfloor>numiter - t - 1\<rfloor>\<^sub>N, 1)]"
    using tpsL5_def tpsL4_def jk by (simp add: list_update_swap[of "j+6"])
qed

lemma tpsL5_eq_tpsL: "tpsL5 t = tpsL (Suc t)"
proof -
  define tps where "tps = tps0
    [j := (\<lfloor>idx + 2 * Suc t\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>numiter - Suc t\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<t]) @ (nll_Upsilon (idx + 2 * t) H))]"
  then have "tps = tpsL (Suc t)"
    using tpsL_def jk tps0 by simp
  moreover have "tps = tpsL5 t"
  proof -
    have "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
      using tps_def jk tps0 by simp
    then have "tps[j + 4 := (\<lfloor>[]\<rfloor>, 1)] = tps"
      using list_update_id[of _ "j+4"] by metis
    then show ?thesis
      unfolding tps_def using tpsL5_def by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma tmL5' [transforms_intros]:
  assumes "t < numiter"
    and "ttt = 256 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2"
  shows "transforms tmL5 (tpsL t) ttt (tpsL (Suc t))"
proof -
  let ?ttt = "29 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * nlllength (nll_Upsilon (idx + 2 * t) H) + 4 * nlength (Suc (Suc (idx + 2 * t))) +
      2 * nlength (numiter - t)"
  have "?ttt \<le> 29 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * nlllength (nll_Upsilon (idx + 2 * t) H) + 4 * nlength (Suc (Suc (idx + 2 * t))) +
      2 * nlength numiter"
    using nlength_mono by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * H * (4 + nlength (idx + 2 * t) + nlength H) + 4 * nlength (Suc (Suc (idx + 2 * t))) +
      2 * nlength numiter"
    using nlllength_nll_Upsilon_le H by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * H * (4 + nlength (idx + 2 * numiter) + nlength H) + 4 * nlength (Suc (Suc (idx + 2 * t))) +
      2 * nlength numiter"
    using nlength_mono assms(1) by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * t) + nlength H)\<^sup>2 +
      4 * H * (4 + nlength (idx + 2 * numiter) + nlength H) + 4 * nlength (idx + 2 * numiter) +
      2 * nlength numiter"
    using nlength_mono assms(1) by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      4 * H * (4 + nlength (idx + 2 * numiter) + nlength H) + 4 * nlength (idx + 2 * numiter) +
      2 * nlength numiter"
    using nlength_mono assms(1) by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      4 * H * (4 + nlength (idx + 2 * numiter) + nlength H) + 6 * nlength (idx + 2 * numiter)"
    using nlength_mono by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      4 * H * (4 + nlength (idx + 2 * numiter) + nlength H) + 6 * (nlength (idx + 2 * numiter) + nlength H)"
    using nlength_mono by simp
  also have "... = 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      16 * H + 4 * H * (nlength (idx + 2 * numiter) + nlength H) + 6 * (nlength (idx + 2 * numiter) + nlength H)"
    by algebra
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      16 * H + 4 * H * (nlength (idx + 2 * numiter) + nlength H) + 2 * H * (nlength (idx + 2 * numiter) + nlength H)"
  proof -
    have "6 \<le> 2 * H"
      using H by simp
    then show ?thesis
      using mult_le_mono1 nat_add_left_cancel_le by presburger
  qed
  also have "... = 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      16 * H + 6 * H * (nlength (idx + 2 * numiter) + nlength H)"
    by simp
  also have "... \<le> 29 + 205 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 +
      16 * H + 6 * H * (nlength (idx + 2 * numiter) + nlength H)^2"
    using linear_le_pow by simp
  also have "... = 29 + 211 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 + 16 * H"
    by simp
  also have "... \<le> 29 + 227 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2"
    using H nlength_0 by (simp add: Suc_leI)
  also have "... \<le> 256 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2"
    using H nlength_0 by (simp add: Suc_leI)
  finally have "?ttt \<le> ttt"
    using assms(2) by simp
  then have "transforms tmL5 (tpsL t) ttt (tpsL5 t)"
    using assms(1) tmL5 transforms_monotone by blast
  then show ?thesis
    using tpsL5_eq_tpsL by simp
qed

lemma tmL:
  assumes "ttt = numiter * (257 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL numiter)"
  unfolding tmL_def
proof (tform)
  show "\<And>i. i < numiter \<Longrightarrow> read (tpsL i) ! (j + 6) \<noteq> \<box>"
    using jk tpsL_def read_ncontents_eq_0 by simp
  show "\<not> read (tpsL numiter) ! (j + 6) \<noteq> \<box>"
    using jk tpsL_def read_ncontents_eq_0 by simp
  show "numiter * (256 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 + 2) + 1 \<le> ttt"
  proof -
    have "1 \<le> (nlength (idx + 2 * numiter) + nlength H)\<^sup>2"
      using nlength_H by simp
    then have "2 \<le> H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2"
      using H by (metis add_leE mult_2 mult_le_mono nat_1_add_1 numeral_Bit1 numerals(1))
    then show ?thesis
      using assms by simp
  qed
qed

lemma tmL':
  assumes "ttt = numiter * 257 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 + 1"
  shows "transforms tmL tps0 ttt (tpsL numiter)"
  using assms tmL tpsL_eq_tps0 by (simp add: Groups.mult_ac(1))

end  (* context tps0 *)

end  (* locale turing_machine_tm_PHI7 *)

lemma transforms_tm_PHI7I:
  fixes tps tps' :: "tape list" and ttt numiter H k idx :: nat and nss :: "nat list list" and j :: tapeidx
  assumes "length tps = k" and "1 < j" and "j + 6 < k"
    and "H \<ge> 3"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>numiter\<rfloor>\<^sub>N, 1)"
  assumes "ttt = numiter * 257 * H * (nlength (idx + 2 * numiter) + nlength H)\<^sup>2 + 1"
  assumes "tps' = tps
    [j := (\<lfloor>idx + 2 * numiter\<rfloor>\<^sub>N, 1),
     j + 6 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     1 := nlltape (nss @ concat (map (\<lambda>t. nll_Upsilon (idx + 2 * t) H) [0..<numiter]))]"
  shows "transforms (tm_PHI7 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_tm_PHI7 j .
  show ?thesis
    using assms loc.tmL' loc.tpsL_def loc.tmL_eq_tm_PHI7 by simp
qed


subsection \<open>A Turing machine for $\Phi_8$\<close>

text \<open>
The next TM expects a number $idx$ on tape $j$ and a number $H$ on tape $j + 1$.
It appends to the formula on tape~$1$ the formula $\Psi([idx\cdot H, (idx+1)H),
3)$.
\<close>

definition tm_PHI8 :: "tapeidx \<Rightarrow> machine" where
  "tm_PHI8 j \<equiv>
    tm_setn (j + 2) 3 ;;
    tm_Psigamma j ;;
    tm_extendl 1 (j + 6)"

lemma tm_PHI8_tm:
  assumes "0 < j" and "j + 7 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_PHI8 j)"
  unfolding tm_PHI8_def using assms tm_Psigamma_tm tm_setn_tm tm_extendl_tm by simp

locale turing_machine_PHI8 =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_setn (j + 2) 3"
definition "tm2 \<equiv> tm1 ;; tm_Psigamma j"
definition "tm3 \<equiv> tm2 ;; tm_extendl 1 (j + 6)"

lemma tm3_eq_tm_PHI8: "tm3 = tm_PHI8 j"
  using tm3_def tm2_def tm1_def tm_PHI8_def by simp

context
  fixes tps0 :: "tape list" and k idx H :: nat and nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j" "j + 7 < k"
    and H: "H \<ge> 3"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 14"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def jk)
  show "tps0 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 jk canrepr_0 by simp
  show "ttt = 10 + 2 * nlength 0 + 2 * nlength 3"
    using assms nlength_3 by simp
qed

definition "tps2 \<equiv> tps0
  [j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (idx * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 14 + 1851 * H ^ 4 * nlength (Suc idx) ^ 2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: tps0 H tps1_def tps2_def jk time: assms canrepr_1)

definition "tps3 \<equiv> tps0
  [1 := nlltape (nss @ nll_Psi (idx * H) H 3),
   j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
   j + 6 := (\<lfloor>nll_Psi (idx * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm3:
  assumes "ttt = 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 +
    2 * nlllength (nll_Psi (idx * H) H 3)"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def by (tform tps: tps0 H tps2_def tps3_def jk time: assms)

lemma tm3':
  assumes "ttt = 18 + 1861 * H ^ 4 * (nlength (Suc idx))\<^sup>2"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  have *: "(nlength (Suc idx))\<^sup>2 \<ge> 1"
    using nlength_0 by (simp add: Suc_leI)
  let ?ttt = "18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * nlllength (nll_Psi (idx * H) H 3)"
  have "?ttt \<le> 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H * (3 + nlength (idx * H + H))"
    using nlllength_nll_Psi_le by simp
  also have "... = 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H * (3 + nlength (Suc idx * H))"
    by (simp add: add.commute)
  also have "... \<le> 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H * (3 + nlength (Suc idx) + nlength H)"
    using nlength_prod by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1) add_left_mono mult_le_cancel1)
  also have "... = 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 6 * H + 2 * H * nlength (Suc idx) + 2 * H * nlength H"
    by algebra
  also have "... \<le> 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 6 * H + 2 * H * nlength (Suc idx) + 2 * H * H"
    using nlength_le_n by simp
  also have "... \<le> 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 6 * H ^ 4 + 2 * H * nlength (Suc idx) + 2 * H * H"
    using linear_le_pow[of 4 H] by simp
  also have "... \<le> 18 + 1851 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 6 * H ^ 4 + 2 * H ^ 4 * nlength (Suc idx) + 2 * H * H"
    using linear_le_pow[of 4 H] by simp
  also have "... \<le> 18 + 1857 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H ^ 4 * nlength (Suc idx) + 2 * H * H"
    using * by simp
  also have "... \<le> 18 + 1859 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H * H"
    using linear_le_pow[of 2 "nlength (Suc idx)"] by simp
  also have "... = 18 + 1859 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H ^ 2"
    by algebra
  also have "... \<le> 18 + 1859 * H ^ 4 * (nlength (Suc idx))\<^sup>2 + 2 * H ^ 4"
    using pow_mono'[of 2 4 H] by simp
  also have "... \<le> 18 + 1861 * H ^ 4 * (nlength (Suc idx))\<^sup>2"
    using * by simp
  finally have "?ttt \<le> 18 + 1861 * H ^ 4 * (nlength (Suc idx))\<^sup>2" .
  then show ?thesis
    using tm3 assms transforms_monotone by simp
qed

end

end  (* locale turing_machine_PHI8 *)

lemma transforms_tm_PHI8I:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k idx H :: nat and nss :: "nat list list"
  assumes "length tps = k" and "1 < j" and "j + 7 < k"
    and "H \<ge> 3"
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
  assumes "tps' = tps
      [1 := nlltape (nss @ nll_Psi (idx * H) H 3),
       j + 2 := (\<lfloor>3\<rfloor>\<^sub>N, 1),
       j + 6 := (\<lfloor>nll_Psi (idx * H) H 3\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
  assumes "ttt = 18 + 1861 * H ^ 4 * (nlength (Suc idx))\<^sup>2"
  shows "transforms (tm_PHI8 j) tps ttt tps'"
proof -
  interpret loc: turing_machine_PHI8 j .
  show ?thesis
    using loc.tps3_def loc.tm3' loc.tm3_eq_tm_PHI8 assms by metis
qed


subsection \<open>A Turing machine for $\Phi_9$\<close>

text \<open>
The CNF formula $\Phi_9 = \bigwedge_{t=1}^{T'}$ is the most complicated part of
$\Phi$. Clearly, the main task here is to generate the formulas $\chi_t$
\<close>


subsubsection \<open>A Turing machine for $\chi_t$\<close>

text \<open>
A lemma that will help with some time bounds:
\<close>

lemma pow2_le_2pow2: "z ^ 2 \<le> 2 ^ (2*z)" for z :: nat
proof (induction z)
  case 0
  then show ?case
    by simp
next
  case (Suc z)
  show ?case
  proof (cases "z = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    have "Suc z ^ 2 = z ^ 2 + 2 * z + 1"
      by (metis Suc_eq_plus1 ab_semigroup_add_class.add_ac(1) nat_mult_1_right one_power2 plus_1_eq_Suc power2_sum)
    also have "... \<le> z ^ 2 + 3 * z"
      using False by simp
    also have "... \<le> z ^ 2 + 3 * z ^ 2"
      by (simp add: linear_le_pow)
    also have "... = 2^2 * z ^ 2"
      by simp
    also have "... \<le> 2^2 * 2 ^ (2 * z)"
      using Suc by simp
    also have "... = 2 ^ (2 * Suc z)"
      by (simp add: power_add)
    finally show ?thesis .
  qed
qed

text \<open>
The next Turing machine can be used to generate $\chi_t$. It expects on tape~1 a
CNF formula, on tape~$j_1$ the list of positions of $M$'s input tape head, on
tape~$j_2$ the list of positions of $M$'s output tape head, on tapes~$j_3,
\dots, j_3+3$ the numbers $N$, $G$, $Z$, and $T$, on tape~$j_3+4$ the formula
$\psi$, on tape~$j_3+5$ the formula $\psi'$, and finally on tape~$j_3+6$ the
number $t$. The TM appends the formula $\chi_t$ to the formula on tape~1, which
should be thought of as an unfinished version of $\Phi$.

The TM first computes $\prev(t)$ using @{const tm_prev} and compares it with
$t$. Depending on the outcome of this comparison it generates either $\rho_t$ or
$\rho'_t$ by concatenating ranges of numbers generated using @{const tm_range}.
Then the TM uses @{const tm_relabel} to compute $\rho_t(\psi)$ or
$\rho'_t(\psi')$. The result equals $\chi_t$ and is appended to tape~1.  Finally
$t$ is incremented and $T$ is decremented. This is so the TM can be used inside
a while loop that initializes $T$ with $T'$ and $t$ with $1$.

\null
\<close>

definition tm_chi :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_chi j1 j2 j3 \<equiv>
    tm_prev j2 (j3 + 6) ;;
    tm_equalsn (j3 + 11) (j3 + 6) (j3 + 13) ;;
    tm_decr (j3 + 6) ;;
    tm_mult (j3 + 6) (j3 + 2) (j3 + 7) ;;
    tm_add j3 (j3 + 7) ;;
    tm_range (j3 + 7) (j3 + 2) (j3 + 8) ;;
    tm_extend_erase (j3 + 12) (j3 + 8) ;;
    tm_setn (j3 + 7) 0 ;;
    IF \<lambda>rs. rs ! (j3 + 13) = \<box> THEN
      tm_mult (j3 + 11) (j3 + 2) (j3 + 7) ;;
      tm_add j3 (j3 + 7) ;;
      tm_range (j3 + 7) (j3 + 2) (j3 + 8) ;;
      tm_extend_erase (j3 + 12) (j3 + 8) ;;
      tm_setn (j3 + 7) 0
    ELSE
      []
    ENDIF ;;
    tm_incr (j3 + 6) ;;
    tm_mult (j3 + 6) (j3 + 2) (j3 + 7) ;;
    tm_add j3 (j3 + 7) ;;
    tm_range (j3 + 7) (j3 + 2) (j3 + 8) ;;
    tm_extend_erase (j3 + 12) (j3 + 8) ;;
    tm_setn (j3 + 11) 0 ;;
    tm_nth j1 (j3 + 6) (j3 + 11) 4 ;;
    tm_setn (j3 + 7) 0 ;;
    tm_mult (j3 + 11) (j3 + 1) (j3 + 7) ;;
    tm_range (j3 + 7) (j3 + 1) (j3 + 8) ;;
    tm_extend_erase (j3 + 12) (j3 + 8) ;;
    tm_setn (j3 + 7) 0 ;;
    tm_erase_cr (j3 + 11) ;;
    tm_cr (j3 + 12) ;;
    IF \<lambda>rs. rs ! (j3 + 13) = \<box> THEN
      tm_relabel (j3 + 4) (j3 + 11)
    ELSE
      tm_erase_cr (j3 + 13) ;;
      tm_relabel (j3 + 5) (j3 + 11)
    ENDIF ;;
    tm_erase_cr (j3 + 12) ;;
    tm_extendl_erase 1 (j3 + 11) ;;
    tm_incr (j3 + 6) ;;
    tm_decr (j3 + 3)"

lemma tm_chi_tm:
  assumes "0 < j1" and "j1 < j2" and "j2 < j3" and "j3 + 17 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_chi j1 j2 j3)"
  unfolding tm_chi_def
  using tm_prev_tm tm_equalsn_tm tm_decr_tm tm_mult_tm tm_add_tm tm_range_tm tm_extend_erase_tm
    tm_setn_tm tm_incr_tm tm_nth_tm tm_erase_cr_tm tm_relabel_tm Nil_tm tm_cr_tm tm_extendl_erase_tm
    assms turing_machine_branch_turing_machine
  by simp

locale turing_machine_chi =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_prev j2 (j3 + 6)"
definition "tm2 \<equiv> tm1 ;; tm_equalsn (j3 + 11) (j3 + 6) (j3 + 13)"

definition "tm3 \<equiv> tm2 ;; tm_decr (j3 + 6)"
definition "tm4 \<equiv> tm3 ;; tm_mult (j3 + 6) (j3 + 2) (j3 + 7)"
definition "tm5 \<equiv> tm4 ;; tm_add j3 (j3 + 7)"
definition "tm6 \<equiv> tm5 ;; tm_range (j3 + 7) (j3 + 2) (j3 + 8)"
definition "tm7 \<equiv> tm6 ;; tm_extend_erase (j3 + 12) (j3 + 8)"
definition "tm8 \<equiv> tm7 ;; tm_setn (j3 + 7) 0"

definition "tmT1 \<equiv> tm_mult (j3 + 11) (j3 + 2) (j3 + 7)"
definition "tmT2 \<equiv> tmT1 ;; tm_add j3 (j3 + 7)"
definition "tmT3 \<equiv> tmT2 ;; tm_range (j3 + 7) (j3 + 2) (j3 + 8)"
definition "tmT4 \<equiv> tmT3 ;; tm_extend_erase (j3 + 12) (j3 + 8)"
definition "tmT5 \<equiv> tmT4 ;; tm_setn (j3 + 7) 0"

definition "tm89 \<equiv> IF \<lambda>rs. rs ! (j3 + 13) = \<box> THEN tmT5 ELSE [] ENDIF"
definition "tm10 \<equiv> tm8 ;; tm89"

definition "tm11 \<equiv> tm10 ;; tm_incr (j3 + 6)"
definition "tm13 \<equiv> tm11 ;; tm_mult (j3 + 6) (j3 + 2) (j3 + 7)"
definition "tm14 \<equiv> tm13 ;; tm_add j3 (j3 + 7)"
definition "tm15 \<equiv> tm14 ;; tm_range (j3 + 7) (j3 + 2) (j3 + 8)"
definition "tm16 \<equiv> tm15 ;; tm_extend_erase (j3 + 12) (j3 + 8)"
definition "tm17 \<equiv> tm16 ;; tm_setn (j3 + 11) 0"
definition "tm18 \<equiv> tm17 ;; tm_nth j1 (j3 + 6) (j3 + 11) 4"
definition "tm19 \<equiv> tm18 ;; tm_setn (j3 + 7) 0"
definition "tm20 \<equiv> tm19 ;; tm_mult (j3 + 11) (j3 + 1) (j3 + 7)"
definition "tm21 \<equiv> tm20 ;; tm_range (j3 + 7) (j3 + 1) (j3 + 8)"
definition "tm22 \<equiv> tm21 ;; tm_extend_erase (j3 + 12) (j3 + 8)"
definition "tm23 \<equiv> tm22 ;; tm_setn (j3 + 7) 0"
definition "tm24 \<equiv> tm23 ;; tm_erase_cr (j3 + 11)"
definition "tm25 \<equiv> tm24 ;; tm_cr (j3 + 12)"

definition "tmE1 \<equiv> tm_erase_cr (j3 + 13)"
definition "tmE2 \<equiv> tmE1 ;; tm_relabel (j3 + 5) (j3 + 11)"
definition "tmTT1 \<equiv> tm_relabel (j3 + 4) (j3 + 11)"

definition "tm2526 \<equiv> IF \<lambda>rs. rs ! (j3 + 13) = \<box> THEN tmTT1 ELSE tmE2 ENDIF"
definition "tm26 \<equiv> tm25 ;; tm2526"
definition "tm27 \<equiv> tm26 ;; tm_erase_cr (j3 + 12)"
definition "tm28 \<equiv> tm27 ;; tm_extendl_erase 1 (j3 + 11)"
definition "tm29 \<equiv> tm28 ;; tm_incr (j3 + 6)"
definition "tm30 \<equiv> tm29 ;; tm_decr (j3 + 3)"

lemma tm30_eq_tm_chi: "tm30 = tm_chi j1 j2 j3"
  unfolding tm30_def tm29_def tm28_def tm27_def tm26_def tm25_def tm24_def tm23_def tm22_def tm21_def tm20_def
    tm19_def tm18_def tm17_def tm16_def tm15_def tm14_def tm13_def tm11_def tm10_def
    tm8_def tm7_def tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def
    tm89_def tmE1_def tmE2_def tmTT1_def tm2526_def
    tmT5_def tmT4_def tmT3_def tmT2_def tmT1_def
    tm_chi_def
  by simp

context
  fixes tps0 :: "tape list" and k G N Z T' T t :: nat and hp0 hp1 :: "nat list" and \<psi> \<psi>' :: formula
  fixes nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j1" "j1 < j2" "j2 < j3" "j3 + 17 < k"
    and G: "G \<ge> 3"
    and Z: "Z = 3 * G"
    and N: "N \<ge> 1"
    and len_hp0: "length hp0 = Suc T'"
    and hp0: "\<forall>i<length hp0. hp0 ! i \<le> T'"
    and len_hp1: "length hp1 = Suc T'"
    and hp1: "\<forall>i<length hp1. hp1 ! i \<le> T'"
    and t: "0 < t" "t \<le> T'"
    and T: "0 < T" "T \<le> T'"
    and T': "T' < N"
    and psi: "variables \<psi> \<subseteq> {..<3*Z+G}" "fsize \<psi> \<le> (3*Z+G) * 2 ^ (3*Z+G)" "length \<psi> \<le> 2 ^ (3*Z+G)"
    and psi': "variables \<psi>' \<subseteq> {..<2*Z+G}" "fsize \<psi>' \<le> (2*Z+G) * 2 ^ (2*Z+G)" "length \<psi>' \<le> 2 ^ (2*Z+G)"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j1 = (\<lfloor>hp0\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! j2 = (\<lfloor>hp1\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! j3 = (\<lfloor>N\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 1) = (\<lfloor>G\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 2) = (\<lfloor>Z\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 3) = (\<lfloor>T\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 4) = (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! (j3 + 5) = (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! (j3 + 6) = (\<lfloor>t\<rfloor>\<^sub>N, 1)"
    "\<And>i. 6 < i \<Longrightarrow> i < 17 \<Longrightarrow> tps0 ! (j3 + i) = (\<lfloor>[]\<rfloor>, 1)"
begin

lemma Z_ge_1: "Z \<ge> 1"
  using G Z by simp

lemma Z_ge_9: "Z \<ge> 9"
  using G Z by simp

lemma T'_ge_1: "T' \<ge> 1"
  using t by simp

lemma tps0': "\<And>i. 1 \<le> i \<Longrightarrow> i < 11 \<Longrightarrow> tps0 ! (j3 + 6 + i) = (\<lfloor>[]\<rfloor>, 1)"
proof -
  fix i :: nat
  assume i: "1 \<le> i" "i < 11"
  then have "6 < 6 + i" "6 + i < 17"
    by simp_all
  then have "tps0 ! (j3 + (6 + i)) = (\<lfloor>[]\<rfloor>, 1)"
    using tps0(11) by simp
  then show "tps0 ! (j3 + 6 + i) = (\<lfloor>[]\<rfloor>, 1)"
    by (metis group_cancel.add1)
qed

text \<open>The simplifier turns $j3 + 6 + 3$ into $9 + j3$. The next lemma helps with that.\<close>

lemma tps0_sym: "\<And>i. 6 < i \<Longrightarrow> i < 17 \<Longrightarrow> tps0 ! (i + j3) = (\<lfloor>[]\<rfloor>, 1)"
  using tps0(11) by (simp add: add.commute)

lemma previous_hp1_le: "previous hp1 t \<le> t"
  using len_hp1 hp1 t(2) previous_le[of hp1 t] by simp

definition "tps1 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 71 + 153 * nllength hp1 ^ 3"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: canrepr_0 tps0_sym tps0 tps1_def jk t len_hp1 time: assms)
  show "tps1 = tps0[j3 + 6 + 5 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1)]"
    using tps1_def by (simp add: add.commute)
qed

definition "tps2 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 78 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t)"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps0 tps1_def tps2_def jk time: assms)
  show "tps1 ! (j3 + 13) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps1_def tps0(11) canrepr_0 by simp
  show "(0::nat) \<le> 1"
    by simp
qed

definition "tps3 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 86 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength t"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def by (tform tps: tps0 tps2_def tps3_def jk assms)

definition "tps4 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>(t - 1) * Z\<rfloor>\<^sub>N, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 90 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength t +
    26 * (nlength (t - 1) + nlength Z) ^ 2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps0 tps3_def tps4_def jk)
  show "tps3 ! (j3 + 7) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps3_def jk canrepr_0 tps0 by simp
  show "ttt = 86 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) +
    2 * nlength t + (4 + 26 * (nlength (t - Suc 0) + nlength Z) * (nlength (t - Suc 0) + nlength Z))"
  proof -
    have "(26 * nlength (t - Suc 0) + 26 * nlength Z) * (nlength (t - Suc 0) + nlength Z) =
        26 * (nlength (t - Suc 0) + nlength Z) ^ 2"
      by algebra
    then show ?thesis
      using assms by simp
  qed
qed

definition "tps5 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + (t - 1) * Z\<rfloor>\<^sub>N, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 100 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength t +
    26 * (nlength (t - 1) + nlength Z) ^ 2 + 3 * max (nlength N) (nlength ((t - 1) * Z))"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def by (tform tps: tps0 tps4_def tps5_def jk time: assms)

definition "tps6 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + (t - 1) * Z\<rfloor>\<^sub>N, 1),
   j3 + 8 := (\<lfloor>[N + (t - 1) * Z..<N + (t - 1) * Z + Z]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm6 [transforms_intros]:
  assumes "ttt = 100 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength t +
    26 * (nlength (t - 1) + nlength Z) ^ 2 + 3 * max (nlength N) (nlength ((t - 1) * Z)) +
    Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z))"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
  by (tform tps: nlcontents_Nil canrepr_0 tps0_sym tps0 tps5_def tps6_def jk time: assms)

definition "tps7 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + (t - 1) * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape [N + (t - 1) * Z..<N + (t - 1) * Z + Z]]"

lemma tm7 [transforms_intros]:
  assumes "ttt = 111 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength t +
    26 * (nlength (t - 1) + nlength Z) ^ 2 + 3 * max (nlength N) (nlength ((t - 1) * Z)) +
    Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) +
    4 * nllength [N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z]"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def
proof (tform tps: tps0 tps6_def tps7_def jk time: assms)
  show "tps6 ! (j3 + 12) = nltape []"
    using tps6_def jk nlcontents_Nil tps0 by force
  show "tps7 = tps6
      [j3 + 12 := nltape ([] @ [N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z]),
       j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"
    unfolding tps7_def tps6_def
    using tps0 jk list_update_id[of tps0 "j3 + 8"]
    by (simp add: list_update_swap)
qed

definition "tps8 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape [N + (t - 1) * Z..<N + (t - 1) * Z + Z]]"

lemma tm8:
  assumes "ttt = 121 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) +
    2 * nlength t + 26 * (nlength (t - 1) + nlength Z) ^ 2 + 3 * max (nlength N) (nlength ((t - 1) * Z)) +
    Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) + 4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z] +
    2 * nlength (N + (t - 1) * Z)"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def by (tform tps: tps0 tps7_def tps8_def jk time: assms)

text \<open>
For the next upper bound we have no scruples replacing $\log T'$, $\log N$, and
$\log Z$ by $T'$, $N$ and $Z$, respectively.  All values are polynomial in $n$
($Z$ is even a constant), so the overall polynomiality is not in jeopardy.
\<close>

lemma nllength_le:
  fixes nmax :: nat and ns :: "nat list"
  assumes "\<forall>n\<in>set ns. n \<le> nmax"
  shows "nllength ns \<le> Suc nmax * length ns"
proof -
  have "nllength ns \<le> Suc (nlength nmax) * length ns"
    using assms nllength_le_len_mult_max by simp
  then show ?thesis
    using nlength_le_n by (meson Suc_le_mono dual_order.trans mult_le_mono1)
qed

lemma nllength_upt_le:
  fixes a b :: nat
  shows "nllength [a..<b] \<le> Suc b * (b - a)"
proof -
  have "nllength [a..<b] \<le> Suc (nlength b) * (b - a)"
    using nllength_upt_le_len_mult_max by simp
  then show ?thesis
    using nlength_le_n by (meson Suc_le_mono dual_order.trans mult_le_mono1)
qed

lemma nllength_hp1: "nllength hp1 \<le> Suc T' * Suc T'"
proof -
  have "\<forall>n\<in>set hp1. n \<le> T'"
    using hp1 by (metis in_set_conv_nth)
  then have "nllength hp1 \<le> Suc T' * Suc T'"
    using nllength_le[of hp1 T'] len_hp1 by simp
  then show ?thesis
    by simp
qed

definition "ttt8 \<equiv> 168 + 153 * Suc T' ^ 6 + 5 * t + 26 * (t + Z) ^ 2 + 47 * Z + 15 * Z * (N + t * Z)"

lemma tm8' [transforms_intros]: "transforms tm8 tps0 ttt8 tps8"
proof -
  let ?s = "88 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength (N + (t - 1) * Z)"
  let ?ttt = "121 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) +
    2 * nlength t + 26 * (nlength (t - 1) + nlength Z) ^ 2 + 3 * max (nlength N) (nlength ((t - 1) * Z)) +
    Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) + 4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z] +
    2 * nlength (N + (t - 1) * Z)"
  have "?ttt = ?s + 33 + 2 * nlength t + 26 * (nlength (t - 1) + nlength Z) ^ 2 + 3 * max (nlength N) (nlength ((t - 1) * Z)) +
      Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) + 4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z]"
    by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * (nlength (t - 1) + nlength Z) ^ 2 +
      3 * max (nlength N) (nlength ((t - 1) * Z)) + Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) +
      4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z]"
    using nlength_le_n by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + nlength Z) ^ 2 +
      3 * max (nlength N) (nlength ((t - 1) * Z)) + Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) +
      4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z]"
    using nlength_le_n by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max (nlength N) (nlength ((t - 1) * Z)) + Suc Z * (43 + 9 * nlength (N + (t - 1) * Z + Z)) +
      4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z]"
    using nlength_le_n by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max (nlength N) (nlength ((t - 1) * Z)) + Suc Z * (43 + 9 * (N + (t - 1) * Z + Z)) +
      4 * nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z]"
    using nlength_le_n add_le_mono le_refl mult_le_mono by presburger
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max (nlength N) (nlength ((t - 1) * Z)) + Suc Z * (43 + 9 * (N + (t - 1) * Z + Z)) +
      4 * Suc (nlength (N + (t - 1) * Z + Z)) * Z"
  proof -
    have "nllength [N + (t - 1) * Z..<N + (t - 1) * Z + Z] \<le> Suc (nlength (N + (t - 1) * Z + Z)) * Z"
      using nllength_le_len_mult_max[of "[N + (t - 1) * Z..<N + (t - 1) * Z + Z]" "N + (t - 1) * Z + Z"]
      by simp
    then show ?thesis
      by linarith
  qed
  also have "... = ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * nlength (max N ((t - 1) * Z)) + Suc Z * (43 + 9 * (N + (t - 1) * Z + Z)) +
      4 * Suc (nlength (N + (t - 1) * Z + Z)) * Z"
    using max_nlength by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max N ((t - 1) * Z) + Suc Z * (43 + 9 * (N + (t - 1) * Z + Z)) +
      4 * Suc (nlength (N + (t - 1) * Z + Z)) * Z"
    using nlength_le_n by simp
  also have "... = ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max N ((t - 1) * Z) + Suc Z * (43 + 9 * (N + t * Z)) +
      4 * Suc (nlength (N + (t - 1) * Z + Z)) * Z"
    using t by (smt (verit) ab_semigroup_add_class.add_ac(1) add.commute diff_Suc_1 gr0_implies_Suc mult_Suc)
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max N ((t - 1) * Z) + Suc Z * (43 + 9 * (N + t * Z)) +
      4 * Suc (N + (t - 1) * Z + Z) * Z"
    using nlength_le_n Suc_le_mono add_le_mono le_refl mult_le_mono by presburger
  also have "... = ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * max N ((t - 1) * Z) + Suc Z * (43 + 9 * (N + t * Z)) +
      4 * Suc (N + t * Z) * Z"
    by (smt (verit, del_insts) Suc_eq_plus1 Suc_leI add.commute add.left_commute add_leD2 le_add_diff_inverse mult.commute mult_Suc_right t(1))
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * (N + ((t - 1) * Z)) + Suc Z * (43 + 9 * (N + t * Z)) + 4 * Suc (N + t * Z) * Z"
    by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * (N + t * Z) + Suc Z * (43 + 9 * (N + t * Z)) + 4 * Suc (N + t * Z) * Z"
    by simp
  also have "... = ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * (N + t * Z) + Suc Z * (43 + 9 * (N + t * Z)) + (4 + 4 * (N + t * Z)) * Z"
    by simp
  also have "... \<le> ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 +
      3 * (N + t * Z) + Suc Z * (43 + 9 * (N + t * Z)) + (4 + 4 * (N + t * Z)) * Suc Z"
    by simp
  also have "... = ?s + 33 + 2 * t + 26 * ((t - 1) + Z) ^ 2 + 3 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by algebra
  also have "... = 121 + 153 * nllength hp1 ^ 3 + 3 * nlength (min (previous hp1 t) t) + 2 * nlength (N + (t - 1) * Z) +
      2 * t + 26 * ((t - 1) + Z) ^ 2 + 3 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... \<le> 121 + 153 * nllength hp1 ^ 3 + 3 * nlength t + 2 * nlength (N + (t - 1) * Z) +
      2 * t + 26 * ((t - 1) + Z) ^ 2 + 3 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    using previous_hp1_le nlength_mono by simp
  also have "... \<le> 121 + 153 * nllength hp1 ^ 3 + 2 * nlength (N + (t - 1) * Z) +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 3 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    using nlength_le_n by simp
  also have "... \<le> 121 + 153 * nllength hp1 ^ 3 + 2 * (N + (t - 1) * Z) +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 3 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    using nlength_le_n add_le_mono1 mult_le_mono2 nat_add_left_cancel_le by presburger
  also have "... \<le> 121 + 153 * nllength hp1 ^ 3 + 2 * (N + t * Z) +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 3 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... = 121 + 153 * nllength hp1 ^ 3 +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 5 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... \<le> 121 + 153 * (Suc T' * Suc T') ^ 3 +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 5 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    using nllength_hp1 by simp
  also have "... = 121 + 153 * (Suc T' ^ 2)^3 +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 5 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by algebra
  also have "... = 121 + 153 * Suc T' ^ 6 +
      5 * t + 26 * ((t - 1) + Z) ^ 2 + 5 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... \<le> 121 + 153 * Suc T' ^ 6 +
      5 * t + 26 * (t + Z) ^ 2 + 5 * (N + t * Z) + Suc Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... = 121 + 153 * Suc T' ^ 6 +
      5 * t + 26 * (t + Z) ^ 2 + 5 * (N + t * Z) + 47 + 13 * (N + t * Z) + Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... = 168 + 153 * Suc T' ^ 6 +
      5 * t + 26 * (t + Z) ^ 2 + 18 * (N + t * Z) + Z * (47 + 13 * (N + t * Z))"
    by simp
  also have "... \<le> 168 + 153 * Suc T' ^ 6 +
      5 * t + 26 * (t + Z) ^ 2 + 2 * Z * (N + t * Z) + Z * (47 + 13 * (N + t * Z))"
    using Z_ge_9 by (metis add_le_mono add_le_mono1 mult_2 mult_le_mono1 nat_add_left_cancel_le numeral_Bit0)
  also have "... = 168 + 153 * Suc T' ^ 6 +
      5 * t + 26 * (t + Z) ^ 2 + 2 * Z * (N + t * Z) + 47 * Z + 13 * Z * (N + t * Z)"
    by algebra
  also have "... = 168 + 153 * Suc T' ^ 6 + 5 * t + 26 * (t + Z) ^ 2 + 47 * Z + 15 * Z * (N + t * Z)"
    by simp
  finally have "?ttt \<le> ttt8"
    using ttt8_def by simp
  then show ?thesis
    using tm8 transforms_monotone by simp
qed

definition "tpsT1 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>previous hp1 t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape [N + (t - 1) * Z..<N + (t - 1) * Z + Z]]"

lemma tmT1 [transforms_intros]:
  assumes "ttt = 4 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2"
  shows "transforms tmT1 tps8 ttt tpsT1"
  unfolding tmT1_def
proof (tform tps: tps0 tps8_def tpsT1_def jk)
  show "ttt = 4 + 26 * (nlength (previous hp1 t) + nlength Z) * (nlength (previous hp1 t) + nlength Z)"
    using assms by algebra
  show "tpsT1 = tps8[j3 + 7 := (\<lfloor>previous hp1 t * Z\<rfloor>\<^sub>N, 1)]"
    unfolding tpsT1_def tps8_def by (simp add: list_update_swap[of "j3+7"])
qed

definition "tpsT2 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + previous hp1 t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape [N + (t - 1) * Z..<N + (t - 1) * Z + Z]]"

lemma tmT2 [transforms_intros]:
  assumes "ttt = 14 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (previous hp1 t * Z))"
  shows "transforms tmT2 tps8 ttt tpsT2"
  unfolding tmT2_def by (tform tps: tps0 tpsT1_def tpsT2_def jk assms)

definition "tpsT3 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + previous hp1 t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape [N + (t - 1) * Z..<N + (t - 1) * Z + Z],
   j3 + 8 := (\<lfloor>[N + previous hp1 t * Z..<N + previous hp1 t * Z + Z]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tmT3 [transforms_intros]:
  assumes "ttt = 14 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (previous hp1 t * Z)) +
    Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z))"
  shows "transforms tmT3 tps8 ttt tpsT3"
  unfolding tmT3_def
  by (tform tps: nlcontents_Nil canrepr_0 tps0_sym tps0 tpsT2_def tpsT3_def jk time: assms)

definition "tpsT4 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + previous hp1 t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmT4 [transforms_intros]:
  assumes "ttt = 25 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (previous hp1 t * Z)) +
    Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
    4 * nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z]"
  shows "transforms tmT4 tps8 ttt tpsT4"
  unfolding tmT4_def by (tform tps: tps0 tpsT3_def tpsT4_def jk time: assms)

definition "tpsT5 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmT5 [transforms_intros]:
  assumes "ttt = 35 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (previous hp1 t * Z)) +
    Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
    4 * nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] +
    2 * nlength (N + previous hp1 t * Z)"
  shows "transforms tmT5 tps8 ttt tpsT5"
  unfolding tmT5_def by (tform tps: tps0 tpsT4_def tpsT5_def jk time: assms)

definition "tps9 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else [])),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm89 [transforms_intros]:
  assumes "ttt = 37 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (previous hp1 t * Z)) +
    Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
    4 * nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] +
    2 * nlength (N + previous hp1 t * Z)"
  shows "transforms tm89 tps8 ttt tps9"
  unfolding tm89_def
proof (tform time: assms)
  have "tps8 ! (j3 + 13) = (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1)"
    using tps8_def jk by simp
  then have *: "(previous hp1 t \<noteq> t) = (read tps8 ! (j3 + 13) = \<box>)"
    using jk tps8_def read_ncontents_eq_0 by force
  show "read tps8 ! (j3 + 13) = \<box> \<Longrightarrow> tps9 = tpsT5"
    using * tps9_def tpsT5_def by simp
  have "(\<lfloor>[]\<rfloor>, 1) = tps0 ! (j3 + 8)"
    using jk tps0 by simp
  then have "tps0[j3 + 8 := (\<lfloor>[]\<rfloor>, 1)] = tps0"
    using jk tps0 by (metis list_update_id)
  then have "tps8 = tps0
    [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
     j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
     j3 + 6 := (\<lfloor>t - 1\<rfloor>\<^sub>N, 1),
     j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 12 := nltape [N + (t - 1) * Z..<N + (t - 1) * Z + Z],
     j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"
    using tps8_def jk tps0 by (simp add: list_update_swap[of _ "j3 + 8"])
  then show "read tps8 ! (j3 + 13) \<noteq> \<box> \<Longrightarrow> tps9 = tps8"
    using * tps9_def by simp
qed

definition "ttt10 \<equiv> ttt8 + 37 + 26 * (nlength (previous hp1 t) + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (previous hp1 t * Z)) +
    Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
    4 * nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] +
    2 * nlength (N + previous hp1 t * Z)"

lemma tm10 [transforms_intros]: "transforms tm10 tps0 ttt10 tps9"
  unfolding tm10_def by (tform tps: ttt10_def)

definition "tps11 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else [])),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm11 [transforms_intros]:
  assumes "ttt = ttt10 + 5 + 2 * nlength (t - 1)"
  shows "transforms tm11 tps0 ttt tps11"
  unfolding tm11_def by (tform tps: t(1) tps0 tps9_def tps11_def jk time: assms)

definition "tps13 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else [])),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm13 [transforms_intros]:
  assumes "ttt = ttt10 + 9 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2"
  shows "transforms tm13 tps0 ttt tps13"
  unfolding tm13_def
proof (tform tps: tps0 tps11_def tps13_def jk)
  show "ttt = ttt10 + 5 + 2 * nlength (t - 1) + (4 + 26 * (nlength t + nlength Z) * (nlength t + nlength Z))"
    using assms by simp (metis Groups.mult_ac(1) distrib_left power2_eq_square)
  show "tps13 = tps11[j3 + 7 := (\<lfloor>t * Z\<rfloor>\<^sub>N, 1)]"
    unfolding tps13_def tps11_def by (simp add: list_update_swap[of "j3+7"])
qed

definition "tps14 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else [])),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm14 [transforms_intros]:
  assumes "ttt = ttt10 + 19 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z))"
  shows "transforms tm14 tps0 ttt tps14"
  unfolding tm14_def
proof (tform tps: tps0 tps13_def tps14_def jk time: assms)
  show "tps14 = tps13[j3 + 7 := (\<lfloor>N + t * Z\<rfloor>\<^sub>N, 1)]"
    unfolding tps14_def tps13_def by (simp add: list_update_swap[of "j3+7"])
qed

definition "tps15 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else [])),
   j3 + 8 := (\<lfloor>[N + t * Z..<N + t * Z + Z]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm15 [transforms_intros]:
  assumes "ttt = ttt10 + 19 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z))"
  shows "transforms tm15 tps0 ttt tps15"
  unfolding tm15_def
proof (tform tps: tps0 tps14_def tps15_def jk time: assms)
  show "tps14 ! (j3 + 8) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps14_def jk nlcontents_Nil tps0 by simp
  show "tps14 ! (j3 + 8 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps14_def jk canrepr_0 tps0_sym by simp
  show "tps14 ! (j3 + 8 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps14_def jk canrepr_0 tps0_sym by simp
qed

definition "tps16 \<equiv> tps0
  [j3 + 11 := (\<lfloor>previous hp1 t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
         [N + t * Z..<N + t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm16 [transforms_intros]:
  assumes "ttt = ttt10 + 30 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
    4 * nllength [N + t * Z..<N + t * Z + Z]"
  shows "transforms tm16 tps0 ttt tps16"
  unfolding tm16_def by (tform tps: tps0 tps15_def tps16_def jk time: assms)

definition "tps17 \<equiv> tps0
  [j3 + 11 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
         [N + t * Z..<N + t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm17 [transforms_intros]:
  assumes "ttt = ttt10 + 40 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
    4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t)"
  shows "transforms tm17 tps0 ttt tps17"
  unfolding tm17_def by (tform tps: tps0 tps16_def tps17_def jk time: jk assms)

definition "tps18 \<equiv> tps0
  [j3 + 11 := (\<lfloor>hp0 ! t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>N + t * Z\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
         [N + t * Z..<N + t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm18 [transforms_intros]:
  assumes "ttt = ttt10 + 66 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
    4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
    21 * (nllength hp0)\<^sup>2"
  shows "transforms tm18 tps0 ttt tps18"
  unfolding tm18_def
proof (tform tps: tps0 tps18_def tps17_def jk time: assms)
  show "t < length hp0"
    using len_hp0 t by simp
qed

definition "tps19 \<equiv> tps0
  [j3 + 11 := (\<lfloor>hp0 ! t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
         [N + t * Z..<N + t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm19 [transforms_intros]:
  assumes "ttt = ttt10 + 76 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
    4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
    21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z)"
  shows "transforms tm19 tps0 ttt tps19"
  unfolding tm19_def
  by (tform tps: tps0 tps18_def tps19_def jk time: assms)

definition "tps20 \<equiv> tps0
  [j3 + 11 := (\<lfloor>hp0 ! t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>hp0 ! t * G\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
         [N + t * Z..<N + t * Z + Z]),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

definition "ttt20 \<equiv> ttt10 + 80 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z) ^ 2 +
    3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
    4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
    21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z) + 26 * (nlength (hp0 ! t) + nlength G) ^ 2"

lemma tm20 [transforms_intros]: "transforms tm20 tps0 ttt20 tps20"
  unfolding tm20_def
proof (tform tps: tps0 tps19_def tps20_def jk)
  show "tps20 = tps19[j3 + 7 := (\<lfloor>hp0 ! t * G\<rfloor>\<^sub>N, 1)]"
    unfolding tps20_def tps19_def by (simp add: list_update_swap[of "j3 + 7"])
  show "ttt20 = ttt10 + 76 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z)\<^sup>2 +
      3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
      4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
      21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z) +
      (4 + 26 * (nlength (hp0 ! t) + nlength G) * (nlength (hp0 ! t) + nlength G))"
    using ttt20_def by simp (metis Groups.mult_ac(1) distrib_left power2_eq_square)
qed

definition "tps21 \<equiv> tps0
  [j3 + 11 := (\<lfloor>hp0 ! t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>hp0 ! t * G\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape
        ([N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
         (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
         [N + t * Z..<N + t * Z + Z]),
   j3 + 8 := (\<lfloor>[hp0 ! t * G..<hp0 ! t * G + G]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm21 [transforms_intros]:
  assumes "ttt = ttt20 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G))"
  shows "transforms tm21 tps0 ttt tps21"
  unfolding tm21_def
proof (tform tps: tps0 tps20_def tps21_def jk time: assms)
  show "tps20 ! (j3 + 8) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps20_def jk nlcontents_Nil tps0 by simp
  show "tps20 ! (j3 + 8 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps20_def jk canrepr_0 tps0_sym by simp
  show "tps20 ! (j3 + 8 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps20_def jk canrepr_0 tps0_sym by simp
qed

abbreviation "\<sigma> \<equiv>
  [N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
  (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
  [N + t * Z..<N + t * Z + Z] @
  [hp0 ! t * G..<hp0 ! t * G + G]"

definition "tps22 \<equiv> tps0
  [j3 + 11 := (\<lfloor>hp0 ! t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>hp0 ! t * G\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape \<sigma>,
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm22 [transforms_intros]:
  assumes "ttt = ttt20 + 11 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G]"
  shows "transforms tm22 tps0 ttt tps22"
  unfolding tm22_def by (tform tps: tps0 tps21_def tps22_def jk time: assms)

definition "tps23 \<equiv> tps0
  [j3 + 11 := (\<lfloor>hp0 ! t\<rfloor>\<^sub>N, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape \<sigma>,
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm23 [transforms_intros]:
  assumes "ttt = ttt20 + 21 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G)"
  shows "transforms tm23 tps0 ttt tps23"
  unfolding tm23_def by (tform tps: tps0 tps22_def tps23_def jk time: assms)

definition "tps24 \<equiv> tps0
  [j3 + 11 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := nltape \<sigma>,
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm24 [transforms_intros]:
  assumes "ttt = ttt20 + 28 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G) +
    2 * nlength (hp0 ! t)"
  shows "transforms tm24 tps0 ttt tps24"
  unfolding tm24_def
proof (tform tps: tps0 tps23_def tps24_def jk assms)
  show "proper_symbols (canrepr (hp0 ! t))"
    using proper_symbols_canrepr by simp
qed

definition "tps25 \<equiv> tps0
  [j3 + 11 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 13 := (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm25 [transforms_intros]:
  assumes "ttt = ttt20 + 31 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G) +
    2 * nlength (hp0 ! t) + nllength \<sigma>"
  shows "transforms tm25 tps0 ttt tps25"
  unfolding tm25_def
proof (tform tps: tps0 tps24_def tps25_def jk assms)
  have *: "tps24 ! (j3 + 12) = nltape \<sigma>"
    using tps24_def jk by simp
  then show "clean_tape (tps24 ! (j3 + 12))"
    using clean_tape_nlcontents by simp
  have "tps25 = tps24[j3 + 12 := nltape \<sigma> |#=| 1]"
    unfolding tps25_def tps24_def by (simp add: list_update_swap)
  then show "tps25 = tps24[j3 + 12 := tps24 ! (j3 + 12) |#=| 1]"
    using * by simp
qed

definition "tpsE1 \<equiv> tps0
  [j3 + 11 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 13 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmE1:
  assumes "ttt = 7 + 2 * nlength (if previous hp1 t = t then 1 else 0)"
  shows "transforms tmE1 tps25 ttt tpsE1"
  unfolding tmE1_def
proof (tform tps: tps0 tps25_def tpsE1_def jk assms)
  show "proper_symbols (canrepr (if previous hp1 t = t then 1 else 0))"
    using proper_symbols_canrepr by simp
qed

lemma tmE1' [transforms_intros]:
  assumes "ttt = 9"
  shows "transforms tmE1 tps25 ttt tpsE1"
  using tmE1 assms transforms_monotone by (simp add: nlength_le_n)

definition "tpsE2 \<equiv> tps0
  [j3 + 11 := nlltape' (formula_n (relabel \<sigma> \<psi>')) 0,
   j3 + 13 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmE2 [transforms_intros]:
  assumes "ttt = 16 + 108 * (nlllength (formula_n \<psi>'))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)"
    and "previous hp1 t = t"
  shows "transforms tmE2 tps25 ttt tpsE2"
  unfolding tmE2_def
proof (tform tps: tps0 tpsE1_def tpsE2_def jk assms time: assms(1))
  let ?sigma = "[N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
            [N + t * Z..<N + t * Z + Z] @ [hp0 ! t * G..<hp0 ! t * G + G]"
  show "variables \<psi>' \<subseteq> {..<length ?sigma}"
    using assms(2) psi'(1) by auto
  show "tpsE1 ! (j3 + 11) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using tpsE1_def jk nllcontents_Nil by simp
  show "tpsE1 ! (j3 + 11 + 1) = (\<lfloor>?sigma\<rfloor>\<^sub>N\<^sub>L, 1)"
    using assms(2) tpsE1_def jk by (simp add: add.commute[of j3 12])
  show "tpsE1 ! (j3 + 11 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tpsE1_def jk nlcontents_Nil by (simp add: add.commute[of j3 13])
  show "tpsE1 ! (j3 + 11 + 3) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tpsE1_def jk tps0_sym nlcontents_Nil by simp
  show "tpsE1 ! (j3 + 11 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsE1_def jk tps0_sym canrepr_0 by simp
  show "tpsE1 ! (j3 + 11 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsE1_def jk tps0_sym canrepr_0 by simp
  show "tpsE2 = tpsE1[j3 + 11 := nlltape' (formula_n (relabel ?sigma \<psi>')) 0]"
    unfolding tpsE2_def tpsE1_def using assms(2) by (simp add: list_update_swap[of "j3+11"])
qed

definition "tpsTT1 \<equiv> tps0
  [j3 + 11 := nlltape' (formula_n (relabel \<sigma> \<psi>)) 0,
   j3 + 13 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tmTT1 [transforms_intros]:
  assumes "ttt = 7 + 108 * (nlllength (formula_n \<psi>))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)"
    and "previous hp1 t \<noteq> t"
  shows "transforms tmTT1 tps25 ttt tpsTT1"
  unfolding tmTT1_def
proof (tform tps: tps0 tps25_def tpsTT1_def jk time: assms(1))
  let ?sigma = "[N + (t - Suc 0) * Z..<N + (t - Suc 0) * Z + Z] @
            (if previous hp1 t \<noteq> t
             then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z]
             else []) @
            [N + t * Z..<N + t * Z + Z] @ [hp0 ! t * G..<hp0 ! t * G + G]"
  show "variables \<psi> \<subseteq> {..<length ?sigma}"
    using assms(2) psi(1) by auto
  show "tps25 ! (j3 + 11) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using tps25_def jk nllcontents_Nil by simp
  show "tps25 ! (j3 + 11 + 1) = (\<lfloor>?sigma\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps25_def jk by (simp add: add.commute[of j3 12])
  show "tps25 ! (j3 + 11 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps25_def jk canrepr_0 nlcontents_Nil assms(2) by (simp add: add.commute[of j3 13])
  show "tps25 ! (j3 + 11 + 3) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps25_def jk tps0_sym nlcontents_Nil by simp
  show "tps25 ! (j3 + 11 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps25_def jk tps0_sym canrepr_0 by simp
  show "tps25 ! (j3 + 11 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps25_def jk tps0_sym canrepr_0 by simp
  show "tpsTT1 = tps25[j3 + 11 := nlltape' (formula_n (relabel ?sigma \<psi>)) 0]"
    using tpsTT1_def tps25_def assms(2) canrepr_0 by (simp add: list_update_swap[of "j3+11"])
qed

definition "tps26 \<equiv> tps0
  [j3 + 11 := nlltape' (formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))) 0,
   j3 + 13 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma nlllength_psi: "nlllength (formula_n \<psi>) \<le> 24 * Z ^ 2 * 2 ^ (4*Z)"
proof -
  let ?V = "3 * Z + G"
  have "\<And>v. v \<in> variables \<psi> \<Longrightarrow> v \<le> ?V"
    using psi(1) by auto
  then have "nlllength (formula_n \<psi>) \<le> fsize \<psi> * Suc (Suc (nlength ?V)) + length \<psi>"
    using nlllength_formula_n by simp
  also have "... \<le> fsize \<psi> * Suc (Suc (nlength ?V)) + 2 ^ ?V"
    using psi by simp
  also have "... \<le> ?V * 2 ^ ?V * Suc (Suc (nlength ?V)) + 2 ^ ?V"
    using psi(2) by (metis add_le_mono1 mult.commute mult_le_mono2)
  also have "... \<le> 4*Z * 2 ^ ?V * Suc (Suc (nlength ?V)) + 2 ^ ?V"
    using Z by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * Suc (Suc (nlength ?V)) + 2 ^ ?V"
  proof -
    have "?V \<le> 4 * Z"
      using Z by simp
    then have "(2::nat) ^ ?V \<le> 2 ^ (4*Z)"
      by simp
    then show ?thesis
      using add_le_mono le_refl mult_le_mono by presburger
  qed
  also have "... \<le> 4*Z * (2::nat) ^ (4*Z) * Suc (Suc (nlength (4*Z))) + 2 ^ ?V"
    using Z nlength_mono by simp
  also have "... \<le> 4*Z * (2::nat) ^ (4*Z) * Suc (Suc (4*Z)) + 2 ^ ?V"
    using nlength_le_n by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * Suc (Suc (4*Z)) + 2 ^ (4*Z)"
    using Z by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * (5*Z) + 2 ^ (4*Z)"
    using Z G by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * (6*Z)"
    using Z G by simp
  also have "... = 24 * Z ^ 2 * 2 ^ (4*Z)"
    by algebra
  finally show ?thesis .
qed

lemma nlllength_psi': "nlllength (formula_n \<psi>') \<le> 24 * Z ^ 2 * 2 ^ (4*Z)"
proof -
  let ?V = "2 * Z + G"
  have "\<And>v. v \<in> variables \<psi>' \<Longrightarrow> v \<le> ?V"
    using psi'(1) by auto
  then have "nlllength (formula_n \<psi>') \<le> fsize \<psi>' * Suc (Suc (nlength ?V)) + length \<psi>'"
    using nlllength_formula_n by simp
  also have "... \<le> fsize \<psi>' * Suc (Suc (nlength ?V)) + 2 ^ ?V"
    using psi' by simp
  also have "... \<le> ?V * 2 ^ ?V * Suc (Suc (nlength ?V)) + 2 ^ ?V"
    using psi'(2) by (metis add_le_mono1 mult.commute mult_le_mono2)
  also have "... \<le> 4*Z * 2 ^ ?V * Suc (Suc (nlength ?V)) + 2 ^ ?V"
    using Z by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * Suc (Suc (nlength ?V)) + 2 ^ ?V"
  proof -
    have "?V \<le> 4 * Z"
      using Z by simp
    then have "(2::nat) ^ ?V \<le> 2 ^ (4*Z)"
      by simp
    then show ?thesis
      using add_le_mono le_refl mult_le_mono by presburger
  qed
  also have "... \<le> 4*Z * (2::nat) ^ (4*Z) * Suc (Suc (nlength (4*Z))) + 2 ^ ?V"
    using Z nlength_mono by simp
  also have "... \<le> 4*Z * (2::nat) ^ (4*Z) * Suc (Suc (4*Z)) + 2 ^ ?V"
    using nlength_le_n by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * Suc (Suc (4*Z)) + 2 ^ (4*Z)"
    using Z by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * (5*Z) + 2 ^ (4*Z)"
    using Z G by simp
  also have "... \<le> 4*Z * 2 ^ (4*Z) * (6*Z)"
    using Z G by simp
  also have "... = 24 * Z ^ 2 * 2 ^ (4*Z)"
    by algebra
  finally show ?thesis .
qed

lemma tm2526:
  assumes "ttt = 17 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)"
  shows "transforms tm2526 tps25 ttt tps26"
  unfolding tm2526_def
proof (tform)
  have *: "tps25 ! (j3 + 13) = (\<lfloor>previous hp1 t = t\<rfloor>\<^sub>B, 1)"
    using tps25_def jk by simp
  then have **: "(previous hp1 t \<noteq> t) = (read tps25 ! (j3 + 13) = \<box>)"
    using jk tps25_def read_ncontents_eq_0 by force
  show "read tps25 ! (j3 + 13) = \<box> \<Longrightarrow> previous hp1 t \<noteq> t"
    using ** by simp
  show "read tps25 ! (j3 + 13) \<noteq> \<box> \<Longrightarrow> previous hp1 t = t"
    using ** by simp
  show "read tps25 ! (j3 + 13) = \<box> \<Longrightarrow> tps26 = tpsTT1"
    using tps26_def tpsTT1_def ** by presburger
  show "read tps25 ! (j3 + 13) \<noteq> \<box> \<Longrightarrow> tps26 = tpsE2"
    using tps26_def tpsE2_def ** by presburger

  let ?tT = "7 + 108 * (nlllength (formula_n \<psi>))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)"
  let ?tF = "16 + 108 * (nlllength (formula_n \<psi>'))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)"
  have "?tT + 2 \<le> 9 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)"
    using nlllength_psi linear_le_pow by simp
  also have "... \<le> ttt"
    using assms by simp
  finally show "?tT + 2 \<le> ttt" .
  show "?tF + 1 \<le> ttt"
    using nlllength_psi' assms linear_le_pow by simp
qed

lemma nllength_\<sigma>: "nllength \<sigma> \<le> 12 * T' * Z^2 + 4 * Z * N"
proof -
  have "n \<le> N + T' * Z + Z" if "n \<in> set \<sigma>" for n
  proof -
    consider
        "n \<in> set [N + (t - 1) * Z..<N + (t - 1) * Z + Z]"
      | "n \<in> set [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z]"
      | "n \<in> set [N + t * Z..<N + t * Z + Z]"
      | "n \<in> set [hp0 ! t * G..<hp0 ! t * G + G]"
      using `n \<in> set \<sigma>` by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "n \<le> N + (t - 1) * Z + Z"
        by simp
      also have "... \<le> N + T' * Z + Z"
        using t(2) by auto
      finally show ?thesis
        by simp
    next
      case 2
      then have "n \<le> N + (previous hp1 t) * Z + Z"
        by simp
      also have "... \<le> N + t * Z + Z"
        by (simp add: previous_hp1_le)
      also have "... \<le> N + T' * Z + Z"
        using t(2) by simp
      finally show ?thesis
        by simp
    next
      case 3
      then have "n \<le> N + t * Z + Z"
        by simp
      also have "... \<le> N + T' * Z + Z"
        using t(2) by auto
      finally show ?thesis
        by simp
    next
      case 4
      then have "n \<le> N + (hp0 ! t) * G + G"
        by simp
      also have "... \<le> N + T' * G + G"
        using t len_hp0 hp0 by simp
      also have "... \<le> N + T' * Z + Z"
        using Z by simp
      finally show ?thesis
        by simp
    qed
  qed
  then have "nllength \<sigma> \<le> Suc (N + T' * Z + Z) * (length \<sigma>)"
    using nllength_le[of \<sigma> "N + T' * Z + Z"] by simp
  also have "... \<le> Suc (N + T' * Z + Z) * (3 * Z + G)"
  proof -
    have "length \<sigma> \<le> 3 * Z + G"
      by simp
    then show ?thesis
      using mult_le_mono2 by presburger
  qed
  also have "... \<le> Suc (N + T' * Z + Z) * (3 * Z + Z)"
    using Z by simp
  also have "... = 4 * Z * Suc (N + T' * Z + Z)"
    by simp
  also have "... = 4 * Z + 4 * Z * (N + T' * Z + Z)"
    by simp
  also have "... = 4 * Z + 4 * Z * N + 4 * T' * Z^2 + 4 * Z^2"
    by algebra
  also have "... \<le> 4 * Z^2 + 4 * Z * N + 4 * T' * Z^2 + 4 * Z^2"
    using linear_le_pow by simp
  also have "... = 8 * Z^2 + 4 * Z * N + 4 * T' * Z^2"
    by simp
  also have "... \<le> 8 * T' * Z^2 + 4 * Z * N + 4 * T' * Z^2"
    using t by simp
  also have "... = 12 * T' * Z^2 + 4 * Z * N"
    by simp
  finally show ?thesis .
qed

lemma tm2526' [transforms_intros]:
  assumes "ttt = 17 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (12 * T' * Z^2 + 4 * Z * N)\<^sup>2)"
  shows "transforms tm2526 tps25 ttt tps26"
proof -
  have "17 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2) \<le> ttt"
    using assms nllength_\<sigma> by simp
  then show ?thesis
    using tm2526 transforms_monotone by simp
qed

lemma tm26 [transforms_intros]:
  assumes "ttt = ttt20 + 31 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G) +
    2 * nlength (hp0 ! t) + nllength \<sigma> +
    17 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (12 * T' * Z^2 + 4 * Z * N)\<^sup>2)"
  shows "transforms tm26 tps0 ttt tps26"
  unfolding tm26_def by (tform tps: assms)

definition "tps27 \<equiv> tps0
  [j3 + 11 := nlltape' (formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))) 0,
   j3 + 13 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
   j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j3 + 12 := (\<lfloor>[]\<rfloor>, 1),
   j3 + 8 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm27:
  assumes "ttt = ttt20 + 38 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G) +
    2 * nlength (hp0 ! t) + 3 * nllength \<sigma> +
    17 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (12 * T' * Z^2 + 4 * Z * N)\<^sup>2)"
  shows "transforms tm27 tps0 ttt tps27"
  unfolding tm27_def
proof (tform tps: tps0 tps26_def tps27_def jk)
  let ?zs = "numlist \<sigma>"
  show "tps26 ::: (j3 + 12) = \<lfloor>?zs\<rfloor>"
    using tps26_def jk nlcontents_def by simp
  show "proper_symbols ?zs"
    using proper_symbols_numlist by simp
  show "ttt = ttt20 + 31 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
      4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G) +
      2 * nlength (hp0 ! t) + nllength \<sigma> +
      17 + 108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 * (3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2) +
      (tps26 :#: (j3 + 12) + 2 * length (numlist \<sigma>) + 6)"
    using tps26_def jk nllength_def assms by simp
qed

definition "tps27' \<equiv> tps0
  [j3 + 11 := nlltape' (formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))) 0]"

lemma tps27': "tps27 = tps27'"
proof -
  have 1: "tps0[j3 + 13 := (\<lfloor>[]\<rfloor>, Suc 0)] = tps0"
    using list_update_id[of tps0 "j3+13"] jk tps0 by simp
  have 2: "tps0[j3 + 12 := (\<lfloor>[]\<rfloor>, Suc 0)] = tps0"
    using list_update_id[of tps0 "j3+12"] jk tps0 by simp
  have 3: "tps0[j3 + 8 := (\<lfloor>[]\<rfloor>, Suc 0)] = tps0"
    using list_update_id[of tps0 "j3+8"] jk tps0 by simp
  have 4: "tps0[j3 + 7 := (\<lfloor>0\<rfloor>\<^sub>N, Suc 0)] = tps0"
    using list_update_id[of tps0 "j3+7"] canrepr_0 jk tps0 by simp
  have 5: "tps0[j3 + 6 := (\<lfloor>t\<rfloor>\<^sub>N, Suc 0)] = tps0"
    using list_update_id[of tps0 "j3+6"] jk tps0 by simp
  show ?thesis
    unfolding tps27_def tps27'_def
    using tps0
    by (simp split del: if_split add:
      list_update_swap[of _ "j3 + 13"] 1
      list_update_swap[of _ "j3 + 12"] 2
      list_update_swap[of _ "j3 + 8"] 3
      list_update_swap[of _ "j3 + 7"] 4
      list_update_swap[of _ "j3 + 6"] 5)
qed

definition "ttt27 = ttt20 + 38 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
    4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] + 2 * nlength (hp0 ! t * G) +
    2 * nlength (hp0 ! t) + 3 * nllength \<sigma> +
    17 + 108 * (24 * Z ^ 2 * 2 ^ (4*Z))\<^sup>2 * (3 + (12 * T' * Z^2 + 4 * Z * N)\<^sup>2)"

lemma tm27' [transforms_intros]: "transforms tm27 tps0 ttt27 tps27'"
  using ttt27_def tm27 nllength_\<sigma> tps27' transforms_monotone by simp

definition "tps28 \<equiv> tps0
  [1 := nlltape (nss @ formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))),
   j3 + 11 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm28:
  assumes "ttt = ttt27 + (11 + 4 * nlllength (formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))))"
  shows "transforms tm28 tps0 ttt tps28"
  unfolding tm28_def by (tform tps: tps0(1) tps0 tps27'_def tps28_def jk time: ttt27_def assms)

lemma nlllength_relabel_chi_t:
  "nlllength (formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))) \<le>
     Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)"
  (is "nlllength (formula_n (relabel \<sigma> ?phi)) \<le> _")
proof -
  have "variables ?phi \<subseteq> {..<length \<sigma>}"
  proof (cases "previous hp1 t = t")
    case True
    then show ?thesis
      using psi'(1) by auto
  next
    case False
    then show ?thesis
      using psi(1) by auto
  qed
  then have "nlllength (formula_n (relabel \<sigma> ?phi)) \<le> Suc (nllength \<sigma>) * nlllength (formula_n ?phi)"
    using nlllength_relabel_variables by simp
  moreover have "nlllength (formula_n ?phi) \<le> 24 * Z ^ 2 * 2 ^ (4*Z)"
    using nlllength_psi nlllength_psi' by (cases "previous hp1 t = t") simp_all
  ultimately have "nlllength (formula_n (relabel \<sigma> ?phi)) \<le> Suc (nllength \<sigma>) * (24 * Z ^ 2 * 2 ^ (4*Z))"
    by (meson le_trans mult_le_mono2)
  then show ?thesis
    by linarith
qed

definition "tps28' \<equiv> tps0
    [1 := nlltape (nss @ formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>)))]"

lemma tps28': "tps28' = tps28"
  unfolding tps28'_def tps28_def using tps0 list_update_id[of tps0 "j3+11"]
  by (simp add: list_update_swap[of _ "j3 + 11"])

lemma tm28' [transforms_intros]:
  assumes "ttt = ttt27 + (11 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)))"
  shows "transforms tm28 tps0 ttt tps28'"
  using assms tm28 tps28' nlllength_relabel_chi_t transforms_monotone by simp

definition "tps29 \<equiv> tps0
    [1 := nlltape (nss @ formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))),
     j3 + 6 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1)]"

lemma tm29 [transforms_intros]:
  assumes "ttt = ttt27 + 16 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t"
  shows "transforms tm29 tps0 ttt tps29"
  unfolding tm29_def by (tform tps: assms tps0 tps28'_def tps29_def jk)

definition "tps30 \<equiv> tps0
    [1 := nlltape (nss @ formula_n (relabel \<sigma> (if previous hp1 t = t then \<psi>' else \<psi>))),
     j3 + 6 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1),
     j3 + 3 := (\<lfloor>T - 1\<rfloor>\<^sub>N, 1)]"

lemma tm30:
  assumes "ttt = ttt27 + 24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t + 2 * nlength T"
  shows "transforms tm30 tps0 ttt tps30"
  unfolding tm30_def by (tform tps: assms tps0 tps29_def tps30_def jk)

text \<open>
Some helpers for bounding the running time:
\<close>

lemma pow4_le_2pow4: "z ^ 4 \<le> 2 ^ (4*z)" for z :: nat
proof -
  have "z ^ 4 = (z ^ 2) ^ 2"
    by simp
  also have "... \<le> (2^(2*z)) ^ 2"
    using pow2_le_2pow2 power_mono by blast
  also have "... = 2^(4*z)"
    by (metis mult.commute mult_2_right numeral_Bit0 power_mult)
  finally show ?thesis .
qed

lemma pow8_le_2pow8: "z ^ 8 \<le> 2 ^ (8*z)" for z :: nat
proof -
  have "z ^ 8 = (z ^ 2) ^ 4"
    by simp
  also have "... \<le> (2^(2*z)) ^ 4"
    using pow2_le_2pow2 power_mono by blast
  also have "... = 2^(8*z)"
    by (metis mult.commute mult_2_right numeral_Bit0 power_mult)
  finally show ?thesis .
qed

lemma Z_sq_le: "Z^2 \<le> 2^(16*Z)"
proof -
  have "Z^2 \<le> 2^(2*Z)"
    using pow2_le_2pow2[of Z] by simp
  also have "... \<le> 2^(16*Z)"
    by simp
  finally show "Z^2 \<le> 2^(16*Z)" .
qed

lemma time_bound:
  "ttt27 + 24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t + 2 * nlength T \<le> 16114765 * 2^(16*Z) * N^6"
proof -
  have sum_sq: "(a + b) ^ 2 \<le> Suc (2 * b) * a ^ 2 + b ^ 2" for a b :: nat
  proof -
    have "(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2"
      by algebra
    also have "... \<le> a ^ 2 + 2 * a ^ 2 * b + b ^ 2"
      using linear_le_pow by simp
    also have "... = Suc (2 * b) * a ^ 2 + b ^ 2"
      by simp
    finally show ?thesis .
  qed
  have 1: "t < N"
    using t T' by simp
  then have 15: "t \<le> N"
    by simp
  have 2: "nlength t < N"
    using 1 nlength_le_n dual_order.strict_trans2 by blast
  have 25: "nlength T \<le> N"
    using T T' nlength_le_n by (meson le_trans order_less_imp_le)
  have 27: "nlength (t - 1) < N"
    using t(1) nlength_mono 2
    by (metis diff_less dual_order.strict_trans2 less_numeral_extra(1) linorder_not_less order.asym)
  have 3: "t * Z < N * Z"
    using 1 Z_ge_1 by simp
  then have 4: "N + t * Z < Suc Z * N"
    using 1 by simp
  have 41: "N + t * Z + Z \<le> Suc Z * N"
  proof -
    have "N + t * Z + Z \<le> N + (N - 1) * Z + Z"
      using 1 N by auto
    then show ?thesis
      using N
      by (metis One_nat_def Suc_n_not_le_n ab_semigroup_add_class.add_ac(1) add.commute mult.commute mult_eq_if times_nat.simps(2))
  qed
  have 42: "(t + Z)^2 \<le> (N + Z) ^ 2"
    using 1 by simp
  have 45: "(N + Z) ^ 2 \<le> 3*Z*N^2 + Z^2"
  proof -
    have "(N + Z) ^ 2 \<le> Suc (2 * Z) * N^2 + Z^2"
      using sum_sq by simp
    also have "... \<le> 3*Z * N^2 +Z^2"
      using Z_ge_1 by simp
    finally show ?thesis .
  qed
  have 5: "nlength (previous hp1 t) < N"
    using previous_hp1_le 1 by (meson dual_order.strict_trans2 nlength_le_n)
  then have 51: "nlength (previous hp1 t) \<le> N"
    by simp
  have 6: "nlength (N + t * Z) < Suc Z * N"
    using 4 nlength_le_n by (meson le_trans linorder_not_le)
  have "nllength \<sigma> \<le> 12 * N * Z^2 + 4 * Z * N"
  proof -
    have "nllength \<sigma> \<le> 12 * T' * Z^2 + 4 * Z * N"
      using nllength_\<sigma> by simp
    also have "... \<le> 12 * N * Z^2 + 4 * Z * N"
      using T' by simp
    finally show ?thesis .
  qed
  have 7: "previous hp1 t \<le> N"
    using previous_hp1_le 15 by simp
  have 65: "(nlength (previous hp1 t) + nlength Z)\<^sup>2 < (N + Z) ^ 2"
  proof -
    have "nlength (previous hp1 t) + nlength Z < N + Z"
      using 7 2 5 by (simp add: add_less_le_mono nlength_le_n)
    then show ?thesis
      by (simp add: power_strict_mono)
  qed
  have 66: "N + previous hp1 t * Z + Z \<le> Suc Z * N"
    using 41 previous_hp1_le by (meson add_le_mono le_trans less_or_eq_imp_le mult_le_mono)
  have 67: "(nlength t + nlength Z)\<^sup>2 \<le> 3 * Z * N^2 + Z^2"
  proof -
    have "nlength t + nlength Z < N + Z"
      using nlength_le_n 2 by (simp add: add_less_le_mono)
    then have "(nlength t + nlength Z)^2 < (N + Z) ^ 2"
      by (simp add: power_strict_mono)
    then show ?thesis
      using 45 by simp
  qed
  have "nlength (previous hp1 t * Z) \<le> N * Z"
    using nlength_le_n previous_hp1_le 1 by (meson le_trans less_or_eq_imp_le mult_le_mono)
  have 75: "max (nlength N) (nlength (t * Z)) \<le> Suc Z * N"
  proof -
    have "max (nlength N) (nlength (t * Z)) \<le> nlength (max N (t * Z))"
      using max_nlength by simp
    also have "... \<le> nlength (N + t * Z)"
      by (simp add: nlength_mono)
    finally show ?thesis
      using 6 by simp
  qed
  then have 78: "max (nlength N) (nlength (previous hp1 t * Z)) \<le> Suc Z * N"
    using previous_hp1_le nlength_mono by (smt (verit, best) Groups.mult_ac(2) le_trans max_def mult_le_mono2)
  have 79: "nlength (N + t * Z + Z) \<le> Suc Z * N + Z"
  proof -
    have "N + t * Z + Z \<le> Suc Z * N + Z"
      using previous_le 15 by simp
    then show ?thesis
      using nlength_le_n le_trans by blast
  qed
  have 8: "nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] \<le> 2 * Z^2 * N + 2 * Z^2"
  proof -
    have "nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] \<le>
        Suc (nlength (N + previous hp1 t * Z + Z)) * Z"
      using nllength_upt_le_len_mult_max by (metis diff_add_inverse)
    moreover have "nlength (N + previous hp1 t * Z + Z) \<le> Suc Z * N + Z"
    proof -
      have "N + previous hp1 t * Z + Z \<le> Suc Z * N + Z"
        using previous_le 15 7 by simp
      then show ?thesis
        using nlength_le_n le_trans by blast
    qed
    ultimately have "nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] \<le> Suc (Suc Z * N + Z) * Z"
      by (meson Suc_le_mono le_trans less_or_eq_imp_le mult_le_mono)
    also have "... = (Z^2 + Z) * Suc N"
      by (metis add.commute mult.commute mult.left_commute mult_Suc nat_arith.suc1 power2_eq_square)
    also have "... \<le> (Z^2 + Z^2) * Suc N"
      by (meson add_le_cancel_left linear_le_pow mult_le_mono1 rel_simps(51))
    also have "... = 2 * Z^2 * Suc N"
      by simp
    also have "... = 2 * Z^2 * N + 2 * Z^2"
      by simp
    finally show ?thesis .
  qed
  have 84: "Z * Suc Z \<le> 2 * Z^2"
    by (simp add: power2_eq_square)
  have 85: "nlength (N + previous hp1 t * Z) \<le> Suc Z * N"
  proof -
    have "nlength (N + previous hp1 t * Z) \<le> nlength (N + t * Z)"
      using previous_hp1_le nlength_mono by simp
    then show ?thesis
      using 6 by simp
  qed
  have 9: "Suc Z \<le> 2*Z"
    using Z_ge_1 by simp
  then have 91: "Suc Z ^ 2 \<le> 4 * Z^2"
    by (metis mult_2_right numeral_Bit0 power2_eq_square power2_nat_le_eq_le power_mult_distrib)
  have 99: "Z^2 \<ge> 81"
  proof -
    have "Z * Z \<ge> 9 * 9"
      using Z_ge_9 mult_le_mono by presburger
    moreover have "9 * 9 = (81::nat)"
      by simp
    ultimately show ?thesis
      by (simp add: power2_eq_square)
  qed

  have part1: "ttt8 \<le> 241 * Z^2 + 266 * Z^2 * N ^ 6"
  proof -
    have "ttt8 \<le> 168 + 153 * N ^ 6 + 5 * t + 26 * (t + Z)\<^sup>2 + 47 * Z + 15 * Z * (N + t * Z)"
      using ttt8_def T' by simp
    also have "... \<le> 168 + 153 * N ^ 6 + 5 * N + 26 * (t + Z)\<^sup>2 + 47 * Z + 15 * Z * (N + t * Z)"
      using 15 by simp
    also have "... \<le> 168 + 153 * N ^ 6 + 5 * N + 26 * (N + Z)\<^sup>2 + 47 * Z + 15 * Z * (N + t * Z)"
      using 42 by simp
    also have "... \<le> 168 + 153 * N ^ 6 + 5 * N + 26 * (3*Z*N^2 + Z^2) + 47 * Z + 15 * Z * (N + t * Z)"
      using 45 by simp
    also have "... \<le> 168 + 153 * N ^ 6 + 5 * N + 26 * (3*Z*N^2 + Z^2) + 47 * Z + 15 * Z * Suc Z * N"
      using 4 by (metis (mono_tags, lifting) add_left_mono less_or_eq_imp_le mult.assoc mult_le_mono2)
    also have "... \<le> 168 + 153 * N ^ 6 + 5 * N + 26 * (3*Z*N^2 + Z^2) + 47 * Z + 30 * Z^2 * N"
      using `Z * Suc Z \<le> 2 * Z^2` by simp
    also have "... = 168 + 153 * N ^ 6 + 5 * N + 78 * Z * N^2 + 26*Z^2 + 47 * Z + 30 * Z^2 * N"
      by simp
    also have "... \<le> 168 + 158 * N ^ 6 + 78 * Z * N^2 + 73 * Z^2 + 30 * Z^2 * N"
      using linear_le_pow[of 6 N] linear_le_pow[of 2 Z] by simp
    also have "... \<le> 168 + 158 * N ^ 6 + 78 * Z^2 * N^2 + 73 * Z^2 + 30 * Z^2 * N^2"
      using linear_le_pow
      by (metis add_le_mono add_le_mono1 le_square mult_le_mono1 mult_le_mono2 nat_add_left_cancel_le power2_eq_square)
    also have "... = 168 + 158 * N ^ 6 + 108 * Z^2 * N^2 + 73 * Z^2"
      by simp
    also have "... \<le> 168*Z^2 + 158 * N ^ 6 + 108 * Z^2 * N^2 + 73 * Z^2"
      using Z_ge_1 by simp
    also have "... \<le> 241 * Z^2 + 158 * N ^ 6 + 108 * Z^2 * N^6"
      using pow_mono'[of 2 6 N] by simp
    also have "... \<le> 241 * Z^2 + 158 * Z^2 * N ^ 6 + 108 * Z^2 * N^6"
      using Z_ge_1 by simp
    also have "... = 241 * Z^2 + 266 * Z^2 * N ^ 6"
      by simp
    finally show ?thesis .
  qed

  have part2: "ttt10 - ttt8 \<le> 63 * Z^2 + 226 * Z^2 * N^6"
  proof -
    have "ttt10 - ttt8 = 37 + 26 * (nlength (previous hp1 t) + nlength Z)\<^sup>2 +
        3 * max (nlength N) (nlength (previous hp1 t * Z)) +
        Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
        4 * nllength [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] +
        2 * nlength (N + previous hp1 t * Z)"
      using ttt10_def ttt8_def by simp
    also have "... \<le> 37 + 26 * (nlength (previous hp1 t) + nlength Z)\<^sup>2 +
        3 * max (nlength N) (nlength (previous hp1 t * Z)) +
        Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
        4 * (2 * Z^2 * N + 2 * Z^2) + 2 * nlength (N + previous hp1 t * Z)"
      using 8 by simp
    also have "... \<le> 37 + 26 * (N + Z)\<^sup>2 +
        3 * max (nlength N) (nlength (previous hp1 t * Z)) +
        Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
        4 * (2 * Z^2 * N + 2 * Z^2) + 2 * nlength (N + previous hp1 t * Z)"
      using 65 by linarith
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
        8 * Z^2 * N + 8 * Z^2 + 2 * nlength (N + previous hp1 t * Z)"
      using 78 45 by auto
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        Suc Z * (43 + 9 * nlength (N + previous hp1 t * Z + Z)) +
        8 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      using 85 by linarith
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        Suc Z * (43 + 9 * nlength (Suc Z * N)) +
        8 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      using 66 nlength_mono add_le_mono le_refl mult_le_mono by presburger
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        Suc Z * (43 + 9 * (Suc Z * N)) +
        8 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      using nlength_le_n add_le_mono le_refl mult_le_mono by presburger
    also have "... = 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        43 * Suc Z + Suc Z * 9 * Suc Z * N +
        8 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      by algebra
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        43 * 2 * Z + 2 * Z * 9 * Suc Z * N +
        8 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      using 9 by (simp add: add_le_mono)
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        86 * Z + 36 * Z * Z * N + 8 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      by simp
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        86 * Z + 44 * Z^2 * N + 8 * Z^2 + 2 * Suc Z * N"
      by (simp add: power2_eq_square)
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        86 * Z + 44 * Z^2 * N + 8 * Z^2 + 4 * Z * N"
      using 9 by simp
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * (Suc Z * N) +
        86 * Z + 48 * Z^2 * N + 8 * Z^2"
      using linear_le_pow by simp
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 3 * 2 * Z * N +
        86 * Z + 48 * Z^2 * N + 8 * Z^2"
      using 9 by simp
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 6 * Z * N +
        86 * Z^2 * N + 48 * Z^2 * N + 8 * Z^2"
      using linear_le_pow[of 2 Z] N by simp (metis N le_trans mult_le_mono1 nat_mult_1)
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 140 * Z^2 * N + 8 * Z^2"
      using linear_le_pow[of 2 Z] by simp
    also have "... \<le> 37 + 26 * (3*Z*N^2 + Z^2) + 148 * Z^2 * N"
      using N by simp
    also have "... = 37 + 78 * Z * N^2 + 26 * Z^2 + 148 * Z^2 * N"
      by simp
    also have "... \<le> 63 * Z^2 + 78 * Z * N^2 + 148 * Z^2 * N"
      using Z_ge_1 by simp
    also have "... \<le> 63 * Z^2 + 78 * Z^2 * N^2 + 148 * Z^2 * N"
      using linear_le_pow by simp
    also have "... \<le> 63 * Z^2 + 226 * Z^2 * N^2"
      using linear_le_pow by simp
    also have "... \<le> 63 * Z^2 + 226 * Z^2 * N^6"
      using pow_mono'[of 2 6 N] by simp
    finally show ?thesis .
  qed

  have 10: "nllength hp0 \<le> N ^ 2"
  proof -
    have "\<forall>n\<in>set hp0. n \<le> T'"
      using hp0 by (metis in_set_conv_nth)
    then have "nllength hp0 \<le> Suc T' * Suc T'"
      using nllength_le[of hp0 T'] len_hp0 by simp
    also have "... \<le> N * N"
      using T' Suc_leI mult_le_mono by presburger
    also have "... = N ^ 2"
      by algebra
    finally show ?thesis .
  qed
  have 11: "nllength [N + t * Z..<N + t * Z + Z] \<le> 2 * Z^2 * N + Z"
  proof -
    have "nllength [N + t * Z..<N + t * Z + Z] \<le> Suc (N + t * Z + Z) * Z"
      using nllength_upt_le[of "N + t * Z" "N + t * Z + Z"] by simp
    also have "... \<le> Suc (Suc Z * N) * Z"
      using 41 by simp
    also have "... = (Z*Z + Z)*N + Z"
      by (metis add.commute mult.commute mult.left_commute mult_Suc)
    also have "... \<le> 2 * Z^2 * N + Z"
      using linear_le_pow[of 2 Z] by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have 12: "nlength (hp0 ! t) + nlength G \<le> N + Z"
  proof -
    have "nlength (hp0 ! t) + nlength G \<le> hp0 ! t + G"
      using nlength_le_n by (simp add: add_mono)
    also have "... \<le> T' + Z"
      using Z by (simp add: add_le_mono hp0 le_imp_less_Suc len_hp0 t(2))
    also have "... \<le> N + Z"
      using T' by simp
    finally show ?thesis .
  qed

  have part3: "ttt20 - ttt10 \<le> 120 * Z^2 + 206 * Z^2 * N ^ 4"
  proof -
    have "ttt20 - ttt10 = 80 + 2 * nlength (t - 1) + 26 * (nlength t + nlength Z)\<^sup>2 +
        3 * max (nlength N) (nlength (t * Z)) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
        4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
        21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z) + 26 * (nlength (hp0 ! t) + nlength G)\<^sup>2"
      using ttt20_def ttt10_def by simp
    also have "... \<le> 80 + 2 * N + 26 * (3 * Z * N^2 + Z^2) +
        3 * (Suc Z * N) + Suc Z * (43 + 9 * nlength (N + t * Z + Z)) +
        4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
        21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z) + 26 * (nlength (hp0 ! t) + nlength G)\<^sup>2"
      using 27 67 75 by auto
    also have "... \<le> 80 + 2 * N + 26 * (3 * Z * N^2 + Z^2) +
        3 * (Suc Z * N) + Suc Z * (43 + 9 * (Suc Z * N + Z)) +
        4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * nlength (previous hp1 t) +
        21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z) + 26 * (nlength (hp0 ! t) + nlength G)\<^sup>2"
      using 79 add_le_mono le_refl mult_le_mono by presburger
    also have "... \<le> 80 + 2 * N + 26 * (3 * Z * N^2 + Z^2) +
        3 * (Suc Z * N) + Suc Z * (43 + 9 * (Suc Z * N + Z)) +
        4 * nllength [N + t * Z..<N + t * Z + Z] + 2 * N +
        21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z) + 26 * (N + Z)\<^sup>2"
      using 51 12
      by (metis add_le_cancel_right add_le_mono nat_add_left_cancel_le nat_mult_le_cancel_disj power2_nat_le_eq_le)
    also have "... \<le> 80 + 4 * N + 52 * (3 * Z * N^2 + Z^2) + 3 * (Suc Z * N) + Suc Z * (43 + 9 * (Suc Z * N + Z)) +
        4 * nllength [N + t * Z..<N + t * Z + Z] + 21 * (nllength hp0)\<^sup>2 + 2 * nlength (N + t * Z)"
      using 45 by simp
    also have "... \<le> 80 + 4 * N + 52 * (3 * Z * N^2 + Z^2) + 3 * (Suc Z * N) + Suc Z * (43 + 9 * (Suc Z * N + Z)) +
        4 * nllength [N + t * Z..<N + t * Z + Z] + 21 * (nllength hp0)\<^sup>2 + 2 * Suc Z * N"
      using 6 by linarith
    also have "... \<le> 80 + 4 * N + 52 * (3 * Z * N^2 + Z^2) + 3 * (Suc Z * N) + Suc Z * (43 + 9 * (Suc Z * N + Z)) +
        4 * (2 * Z^2 * N + Z) + 21 * (N^2)\<^sup>2 + 2 * Suc Z * N"
      using 11 10 add_le_mono le_refl mult_le_mono2 power2_nat_le_eq_le by presburger
    also have "... = 80 + 4 * N + 156 * Z * N^2 + 52 * Z^2 + 3 * (Suc Z * N) + Suc Z * (43 + 9 * (Suc Z * N + Z)) +
        8 * Z^2 * N + 4 * Z + 21 * N ^ 4 + 2 * Suc Z * N"
      by simp
    also have "... = 80 + 156 * Z * N^2 + 52 * Z^2 + Suc Z * 43 + Suc Z * 9 * Suc Z * N + Suc Z * 9 * Z +
        (4 + 5 * Suc Z + 8 * Z^2) * N + 4 * Z + 21 * N ^ 4"
      by algebra
    also have "... = 123 + 156 * Z * N^2 + 52 * Z^2 + 47 * Z + 9 * Suc Z * Suc Z * N + Suc Z * 9 * Z +
        (9 + 5 * Z + 8 * Z^2) * N + 21 * N ^ 4"
      by simp
    also have "... = 123 + 156 * Z * N^2 + 52 * Z^2 + 47 * Z + 9 * Z * Suc Z +
        (9 * Suc Z^2 + 9 + 5 * Z + 8 * Z^2) * N + 21 * N ^ 4"
      by algebra
    also have "... \<le> 123 + 156 * Z * N^2 + 52 * Z^2 + 47 * Z + 9 * Z * Suc Z +
        (44 * Z^2 + 9 + 5 * Z) * N + 21 * N ^ 4"
      using 91 by simp
    also have "... \<le> 123 + 156 * Z * N^2 + 70 * Z^2 + 47 * Z + (44 * Z^2 + 9 + 5 * Z) * N + 21 * N ^ 4"
      using 84 by simp
    also have "... \<le> 123 + 156 * Z * N^2 + 70 * Z^2 + 47 * Z^2 + (44 * Z^2 + 9 + 5 * Z^2) * N + 21 * N ^ 4"
      using linear_le_pow[of 2 Z] add_le_mono le_refl mult_le_mono power2_nat_le_imp_le
      by presburger
    also have "... \<le> 123 + 156 * Z * N^2 + 117 * Z^2 + (49 * Z^2 + 9) * N ^ 4 + 21 * N ^ 4"
      using linear_le_pow[of 4 N] by simp
    also have "... \<le> 123 + 156 * Z * N^4 + 117 * Z^2 + (49 * Z^2 + 9) * N ^ 4 + 21 * N ^ 4"
      using pow_mono'[of 2 4 N] by simp
    also have "... = 123 + 117 * Z^2 + (156 * Z + 49 * Z^2 + 30) * N ^ 4"
      by algebra
    also have "... \<le> 123 + 117 * Z^2 + (205 * Z^2 + 30) * N ^ 4"
      using linear_le_pow[of 2 Z] by simp
    also have "... \<le> 120 * Z^2 + (205 * Z^2 + 30) * N ^ 4"
      using 99 by simp
    also have "... \<le> 120 * Z^2 + 206 * Z^2 * N ^ 4"
      using 99 by simp
    finally show ?thesis .
  qed

  have 12: "hp0 ! t * G + G \<le> Z * N"
  proof -
    have "hp0 ! t * G + G \<le> T' * G + G"
      using hp0 t(2) len_hp0 by simp
    also have "... \<le> (N - 1) * G + G"
      using T' by auto
    also have "... = N * G"
      using T' by (metis Suc_diff_1 add.commute less_nat_zero_code mult_Suc not_gr_zero)
    also have "... \<le> Z * N"
      using Z by simp
    finally show ?thesis .
  qed
  have 13: "Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) \<le> 43 * Z + 9 * Z^2 * N"
  proof -
    have "Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) \<le> Suc G * (43 + 9 * (hp0 ! t * G + G))"
      using nlength_le_n add_le_mono le_refl mult_le_mono by presburger
    also have "... \<le> Suc G * (43 + 9 * (Z * N))"
      using 12 add_le_mono less_or_eq_imp_le mult_le_mono by presburger
    also have "... \<le> Z * (43 + 9 * (Z * N))"
      using G Z by simp
    also have "... = 43 * Z + 9 * N * Z * Z"
      by algebra
    also have "... = 43 * Z + 9 * Z^2 * N"
      by algebra
    finally show ?thesis .
  qed
  have 14: "nllength [hp0 ! t * G..<hp0 ! t * G + G] \<le> Z^2 * N"
  proof -
    have "nllength [hp0 ! t * G..<hp0 ! t * G + G] \<le> (hp0 ! t * G + G) * Suc G"
      using nllength_upt_le[of "hp0 ! t * G" "hp0 ! t * G + G"] by simp
    also have "... \<le> (hp0 ! t * G + G) * Z"
      using Z G by simp
    also have "... \<le> N * Z * Z"
      using 12 by (simp add: mult.commute)
    also have "... = Z^2 * N"
      by algebra
    finally show ?thesis .
  qed
  have 15: "nlength (hp0 ! t) \<le> N"
    using T' hp0 t(2) len_hp0 nlength_le_n by (metis le_imp_less_Suc le_trans less_or_eq_imp_le)
  have 16: "nlength (hp0 ! t * G) \<le> Z * N"
  proof -
    have "nlength (hp0 ! t * G) \<le> hp0 ! t * G"
      using nlength_le_n by simp
    also have "... \<le> T' * G"
      using Z T' hp0 t(2) len_hp0 by simp
    also have "... \<le> Z * N"
      using Z T' by simp
    finally show ?thesis .
  qed
  have 17: "(12 * T' * Z\<^sup>2 + 4 * Z * N) ^ 2 \<le> 256 * Z^4 * N^2"
  proof -
    have "(12 * T' * Z\<^sup>2 + 4 * Z * N) ^ 2 \<le> (12 * N * Z^2 + 4 * Z * N)^2"
      using T' by simp
    also have "... \<le> (12 * N * Z^2 + 4 * Z^2 * N)^2"
      using linear_le_pow[of 2 Z] add_le_mono le_refl mult_le_mono power2_nat_le_eq_le power2_nat_le_imp_le
      by presburger
    also have "... = 256 * Z^4 * N^2"
      by algebra
    finally show ?thesis .
  qed
  have 18: "108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 * (3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2) \<le> 16111872 * 2^(16*Z) * N^2"
  proof -
    have "108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 = 62208 * (Z^2 * 2 ^ (4*Z))^2"
      by algebra
    also have "... = 62208 * Z^(2*2) * 2 ^ (2*(4*Z))"
      by (metis (no_types, lifting) mult.assoc power_even_eq power_mult_distrib)
    also have "... = 62208 * Z^4 * 2 ^ (8*Z)"
      by simp
    finally have *: "108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 = 62208 * Z^4 * 2 ^ (8*Z)" .
    have "3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2 \<le> 3 + 256 * Z^4 * N^2"
      using 17 by simp
    moreover have "Z^4 * N^2 \<ge> 1"
      using Z_ge_1 N by simp
    ultimately have "3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2 \<le> 259 * Z^4 * N^2"
      by linarith
    then have "108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 * (3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2) \<le>
        16111872 * Z^4 * 2 ^ (8*Z) * Z^4 * N^2"
      using * by simp
    also have "... = 16111872 * Z^8 * 2 ^ (8*Z) * N^2"
      by simp
    also have "... \<le> 16111872 * 2^(8*Z) * 2 ^ (8*Z) * N^2"
      using pow8_le_2pow8 by simp
    also have "... = 16111872 * 2^(8*Z+8*Z) * N^2"
      by (metis (no_types, lifting) mult.assoc power_add)
    also have "... = 16111872 * 2^(16*Z) * N^2"
      by simp
    finally show ?thesis .
  qed
  have 19: "nllength \<sigma> \<le> 16 * Z^2 * N"
  proof -
    have "nllength \<sigma> \<le> 12 * T' * Z^2 + 4 * Z * N"
      using nllength_\<sigma> by simp
    also have "... \<le> 12 * N * Z^2 + 4 * Z * N"
      using T' by simp
    also have "... \<le> 12 * Z^2 * N + 4 * Z^2 * N"
      using linear_le_pow[of 2 Z] by simp
    also have "... \<le> 16 * Z^2 * N"
      by simp
    finally show ?thesis .
  qed

  have part4: "ttt27 - ttt20 \<le> 50 * Z + 16111936 * 2^(16*Z) * N^2"
  proof -
    have "ttt27 - ttt20 = 55 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
        4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] +
        2 * nlength (hp0 ! t * G) + 2 * nlength (hp0 ! t) + 3 * nllength \<sigma> +
        108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 * (3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2)"
      using ttt27_def ttt20_def by linarith
    also have "... \<le> 55 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
        4 * nllength [hp0 ! t * G..<hp0 ! t * G + G] +
        2 * nlength (hp0 ! t * G) + 2 * nlength (hp0 ! t) + 3 * (16 * Z^2 * N) +
        108 * (24 * Z\<^sup>2 * 2 ^ (4 * Z))\<^sup>2 * (3 + (12 * T' * Z\<^sup>2 + 4 * Z * N)\<^sup>2)"
      using 19 by (simp add: mult.commute)
    also have "... \<le> 55 + Suc G * (43 + 9 * nlength (hp0 ! t * G + G)) +
        2 * Z * N + 2 * N + 52 * Z^2 * N + 16111872 * 2^(16*Z) * N^2"
      using 14 15 16 18 by linarith
    also have "... \<le> 55 + 43 * Z + 9 * Z^2 * N + 2 * Z * N + 2 * N + 52 * Z^2 * N + 16111872 * 2^(16*Z) * N^2"
      using 13 by linarith
    also have "... = 55 + 43 * Z + 2 * Z * N + 2 * N + 61 * Z^2 * N + 16111872 * 2^(16*Z) * N^2"
      by simp
    also have "... \<le> 50 * Z + 2 * Z * N + 2 * N + 61 * Z^2 * N + 16111872 * 2^(16*Z) * N^2"
      using Z_ge_9 by simp
    also have "... \<le> 50 * Z + 3 * Z * N + 61 * Z^2 * N + 16111872 * 2^(16*Z) * N^2"
      using Z_ge_9 by simp
    also have "... \<le> 50 * Z + 64 * Z^2 * N + 16111872 * 2^(16*Z) * N^2"
      using linear_le_pow[of 2 Z] by simp
    also have "... \<le> 50 * Z + 64 * Z^2 * N^2 + 16111872 * 2^(16*Z) * N^2"
      using linear_le_pow[of 2 N] by simp
    also have "... \<le> 50 * Z + 64 * 2^(2*Z) * N^2 + 16111872 * 2^(16*Z) * N^2"
      using pow2_le_2pow2 by simp
    also have "... \<le> 50 * Z + 64 * 2^(16*Z) * N^2 + 16111872 * 2^(16*Z) * N^2"
      by simp
    also have "... = 50 * Z + 16111936 * 2^(16*Z) * N^2"
      by simp
    finally show ?thesis .
  qed

  have part5: "24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t + 2 * nlength T \<le>
    24 + 1633 * 2^(8*Z) * N"
  proof -
    have "24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t + 2 * nlength T \<le>
        24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 4 * N"
      using 25 2 by simp
    also have "... \<le> 24 + 4 * (Suc (16 * Z^2 * N) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 4 * N"
      using 19 by (simp add: mult.commute)
    also have "... \<le> 24 + 1632 * Z^2 * N * Z ^ 2 * 2 ^ (4*Z) + 4 * N"
      using Z N by simp
    also have "... = 24 + 1632 * Z^4 * 2 ^ (4*Z) * N + 4 * N"
      by simp
    also have "... \<le> 24 + 1632 * 2^(4*Z) * 2 ^ (4*Z) * N + 4 * N"
      using pow4_le_2pow4 by simp
    also have "... = 24 + 1632 * 2^(8*Z) * N + 4 * N"
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) add_mult_distrib numeral_Bit0 power_add)
    also have "... \<le> 24 + 1632 * 2^(8*Z) * N + 2^(8*Z) * N"
    proof -
      have "(4::nat) \<le> 2 ^ 8"
        by simp
      also have "... \<le> 2 ^ (8*Z)"
        using Z_ge_1 by (metis nat_mult_1_right nat_mult_le_cancel_disj one_le_numeral power_increasing)
      finally have "(4::nat) \<le> 2 ^ (8*Z)" .
      then show ?thesis
        by simp
    qed
    also have "... \<le> 24 + 1633 * 2^(8*Z) * N"
      by simp
    finally show ?thesis .
  qed

  show "ttt27 + 24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t + 2 * nlength T \<le>
    16114765 * 2^(16*Z) * N^6"
  proof -
    have "ttt27 \<le> ttt20 + 50 * Z + 16111936 * 2^(16*Z) * N^2"
      using part4 ttt27_def by simp
    also have "... \<le> ttt10 + 120 * Z^2 + 206 * Z^2 * N ^ 4 + 50 * Z + 16111936 * 2^(16*Z) * N^2"
      using part3 ttt20_def by simp
    also have "... \<le> ttt8 + 63 * Z^2 + 226 * Z^2 * N^6 + 120 * Z^2 + 206 * Z^2 * N ^ 4 + 50 * Z +
        16111936 * 2^(16*Z) * N^2"
      using part2 ttt10_def by simp
    also have "... \<le> 241 * Z^2 + 266 * Z^2 * N ^ 6 + 63 * Z^2 + 226 * Z^2 * N^6 + 120 * Z^2 +
        206 * Z^2 * N ^ 4 + 50 * Z + 16111936 * 2^(16*Z) * N^2"
      using part1 by simp
    also have "... = 424 * Z^2 + 492 * Z^2 * N ^ 6 + 206 * Z^2 * N ^ 4 + 50 * Z + 16111936 * 2^(16*Z) * N^2"
      by simp
    also have "... \<le> 474 * Z^2 + 492 * Z^2 * N ^ 6 + 206 * Z^2 * N ^ 4 + 16111936 * 2^(16*Z) * N^2"
      using linear_le_pow[of 2 Z] by simp
    also have "... \<le> 474 * Z^2 + 698 * Z^2 * N ^ 6 + 16111936 * 2^(16*Z) * N^2"
      using pow_mono'[of 4 6 N] by simp
    also have "... \<le> 474 * Z^2 + 698 * Z^2 * N ^ 6 + 16111936 * 2^(16*Z) * N^6"
      using pow_mono'[of 2 6 N] by simp
    also have "... \<le> 474 * Z^2 + 698 * 2^(16*Z) * N ^ 6 + 16111936 * 2^(16*Z) * N^6"
      using Z_sq_le by simp
    also have "... = 474 * Z^2 + 16112634 * 2^(16*Z) * N^6"
      by simp
    also have "... \<le> 474 * 2^(16*Z) + 16112634 * 2^(16*Z) * N^6"
      using Z_sq_le by simp
    also have "... \<le> 16113108 * 2^(16*Z) * N^6"
      using N by simp
    finally have "ttt27 \<le> 16113108 * 2^(16*Z) * N^6" .
    then have "ttt27 + 24 + 4 * (Suc (nllength \<sigma>) * 24 * Z ^ 2 * 2 ^ (4*Z)) + 2 * nlength t + 2 * nlength T \<le>
        16113108 * 2^(16*Z) * N^6 + 24 + 1633 * 2^(8*Z) * N"
      using part5 by simp
    also have "... \<le> 16113108 * 2^(16*Z) * N^6 + 24 + 1633 * 2^(16*Z) * N"
      by simp
    also have "... \<le> 16113108 * 2^(16*Z) * N^6 + 24 + 1633 * 2^(16*Z) * N^6"
      using linear_le_pow[of 6 N] by simp
    also have "... = 24 + 16114741 * 2^(16*Z) * N^6"
      by simp
    also have "... \<le> 24 * 2^(16*Z) + 16114741 * 2^(16*Z) * N^6"
      using Z_sq_le by simp
    also have "... \<le> 16114765 * 2^(16*Z) * N^6"
      using N by simp
    finally show ?thesis .
  qed
qed

lemma tm30':
  assumes "ttt = 16114765 * 2^(16*Z) * N^6"
  shows "transforms tm30 tps0 ttt tps30"
  using tm30 time_bound transforms_monotone assms by simp

end  (* context tps0 *)

end  (* locale turing_machine_chi *)

lemma transforms_tm_chi:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and k G N Z T' T t :: nat and hp0 hp1 :: "nat list" and \<psi> \<psi>' :: formula
  fixes nss :: "nat list list"
  assumes "length tps = k"
    and "1 < j1" "j1 < j2" "j2 < j3" "j3 + 17 < k"
    and "G \<ge> 3"
    and "Z = 3 * G"
    and "N \<ge> 1"
    and "length hp0 = Suc T'"
    and "\<forall>i<length hp0. hp0 ! i \<le> T'"
    and "length hp1 = Suc T'"
    and "\<forall>i<length hp1. hp1 ! i \<le> T'"
    and "0 < t" "t \<le> T'"
    and "0 < T" "T \<le> T'"
    and "T' < N"
    and "variables \<psi> \<subseteq> {..<3*Z+G}" "fsize \<psi> \<le> (3*Z+G) * 2 ^ (3*Z+G)" "length \<psi> \<le> 2 ^ (3*Z+G)"
    and "variables \<psi>' \<subseteq> {..<2*Z+G}" "fsize \<psi>' \<le> (2*Z+G) * 2 ^ (2*Z+G)" "length \<psi>' \<le> 2 ^ (2*Z+G)"
  assumes
    "tps ! 1 = nlltape nss"
    "tps ! j1 = (\<lfloor>hp0\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! j2 = (\<lfloor>hp1\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! j3 = (\<lfloor>N\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 1) = (\<lfloor>G\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 2) = (\<lfloor>Z\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 3) = (\<lfloor>T\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 4) = (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps ! (j3 + 5) = (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps ! (j3 + 6) = (\<lfloor>t\<rfloor>\<^sub>N, 1)"
    "\<And>i. 6 < i \<Longrightarrow> i < 17 \<Longrightarrow> tps ! (j3 + i) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps
        [1 := nlltape (nss @ formula_n (relabel
          ([N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
            (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
            [N + t * Z..<N + t * Z + Z] @
            [hp0 ! t * G..<hp0 ! t * G + G])
           (if previous hp1 t = t then \<psi>' else \<psi>))),
         j3 + 6 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1),
         j3 + 3 := (\<lfloor>T - 1\<rfloor>\<^sub>N, 1)]"
  assumes "ttt = 16114765 * 2 ^ (16*Z) * N^6"
  shows "transforms (tm_chi j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_chi j1 j2 j3 .
  show ?thesis
    using loc.tm30'[OF assms(1-34)] loc.tps30_def[OF assms(1-34)] assms(35,36) loc.tm30_eq_tm_chi
    by simp
qed


subsubsection \<open>A Turing machine for $\Phi_9$ proper\<close>

text \<open>
The formula $\Phi_9$ is a conjunction of formulas $\chi_t$. The TM @{const
tm_chi} decreases the number on tape $j_3 + 3$. If this tape is initialized with
$T'$, then a while loop with @{const tm_chi} as its body will generate $\Phi_9$.
The next TM is such a machine:
\<close>

definition tm_PHI9 :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_PHI9 j1 j2 j3 \<equiv> WHILE [] ; \<lambda>rs. rs ! (j3 + 3) \<noteq> \<box> DO tm_chi j1 j2 j3 DONE"

lemma tm_PHI9_tm:
  assumes "0 < j1" and "j1 < j2" and "j2 < j3" and "j3 + 17 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_PHI9 j1 j2 j3)"
  unfolding tm_PHI9_def
  using tm_chi_tm turing_machine_loop_turing_machine Nil_tm assms by simp

lemma map_nth:
  fixes zs ys f n i
  assumes "zs = map f [0..<n]" and "i < length zs"
  shows "zs ! i = f i"
  using assms by simp

lemma concat_formula_n:
  "concat (map (\<lambda>t. formula_n (\<phi> t)) [0..<n]) = formula_n (concat (map (\<lambda>t. \<phi> t) [0..<n]))"
  using formula_n_def by (induction n) simp_all

lemma upt_append_upt:
  assumes "a \<le> b" and "b \<le> c"
  shows "[a..<b] @ [b..<c] = [a..<c]"
proof (rule nth_equalityI)
  show "length ([a..<b] @ [b..<c]) = length [a..<c]"
    using assms by simp
  show "([a..<b] @ [b..<c]) ! i = [a..<c] ! i" if "i < length ([a..<b] @ [b..<c])" for i
    using assms that nth_append[of "[a..<b]" "[b..<c]" i] by (cases "i < b - a") simp_all
qed

text \<open>
The semantics of the TM @{const tm_PHI9} can be proved inside the locale
@{locale reduction_sat_x} because it is a fairly simple TM.
\<close>

context reduction_sat_x
begin

text \<open>
The TM @{const tm_chi} is the first TM whose semantics we transfer into the
locale @{locale reduction_sat_x}.
\<close>

lemma tm_chi:
  fixes tps0 :: "tape list" and k t' t :: nat and j1 j2 j3 :: tapeidx
  fixes nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j1" "j1 < j2" "j2 < j3" "j3 + 17 < k"
    and t: "0 < t" "t \<le> T'"
    and T: "0 < t'" "t' \<le> T'"
  assumes "hp0 = map (\<lambda>t. exc (zeros m) t <#> 0) [0..<Suc T']"
  assumes "hp1 = map (\<lambda>t. exc (zeros m) t <#> 1) [0..<Suc T']"
  assumes tps0:
     "tps0 ! 1 = nlltape nss"
     "tps0 ! j1 = (\<lfloor>hp0\<rfloor>\<^sub>N\<^sub>L, 1)"
     "tps0 ! j2 = (\<lfloor>hp1\<rfloor>\<^sub>N\<^sub>L, 1)"
     "tps0 ! j3 = (\<lfloor>N\<rfloor>\<^sub>N, 1)"
     "tps0 ! (j3 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
     "tps0 ! (j3 + 2) = (\<lfloor>Z\<rfloor>\<^sub>N, 1)"
     "tps0 ! (j3 + 3) = (\<lfloor>t'\<rfloor>\<^sub>N, 1)"
     "tps0 ! (j3 + 4) = (\<lfloor>formula_n \<psi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
     "tps0 ! (j3 + 5) = (\<lfloor>formula_n \<psi>'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
     "tps0 ! (j3 + 6) = (\<lfloor>t\<rfloor>\<^sub>N, 1)"
     "\<And>i. 6 < i \<Longrightarrow> i < 17 \<Longrightarrow> tps0 ! (j3 + i) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "tps' = tps0
      [1 := nlltape (nss @ formula_n (\<chi> t)),
       j3 + 6 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1),
       j3 + 3 := (\<lfloor>t' - 1\<rfloor>\<^sub>N, 1)]"
  assumes "ttt = 16114765 * 2^(16*Z) * N ^ 6"
  shows "transforms (tm_chi j1 j2 j3) tps0 ttt tps'"
proof -
  interpret loc: turing_machine_chi j1 j2 j3 .

  have G: "H \<ge> 3"
    using H_gr_2 by simp
  then have N: "N \<ge> 1"
    using N_eq by simp
  have Z: "Z = 3 * H"
    using Z_def by simp
  have len_hp0: "length hp0 = Suc T'"
    using assms by simp
  have len_hp1: "length hp1 = Suc T'"
    using assms by simp
  have hp0: "\<forall>i<length hp0. hp0 ! i \<le> T'"
  proof standard+
    fix i :: nat
    assume "i < length hp0"
    then have "hp0 ! i = exc (zeros m) i <#> 0"
      using map_nth assms(10) by blast
    then show "hp0 ! i \<le> T'"
      using inputpos_less inputpos_def by simp
  qed
  have hp1: "\<forall>i<length hp1. hp1 ! i \<le> T'"
  proof standard+
    fix i :: nat
    assume "i < length hp1"
    then have "hp1 ! i = exc (zeros m) i <#> 1"
      using map_nth assms(11) by blast
    then show "hp1 ! i \<le> T'"
      using headpos_1_less by simp
  qed
  have psi: "variables \<psi> \<subseteq> {..<3*Z+H}" "fsize \<psi> \<le> (3*Z+H) * 2 ^ (3*Z+H)" "length \<psi> \<le> 2 ^ (3*Z+H)"
    using psi by simp_all
  have psi': "variables \<psi>' \<subseteq> {..<2*Z+H}" "fsize \<psi>' \<le> (2*Z+H) * 2 ^ (2*Z+H)" "length \<psi>' \<le> 2 ^ (2*Z+H)"
    using psi' by simp_all

  let ?sigma = "[N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
    (if previous hp1 t \<noteq> t then [N + previous hp1 t * Z..<N + previous hp1 t * Z + Z] else []) @
    [N + t * Z..<N + t * Z + Z] @
    [hp0 ! t * H..<hp0 ! t * H + H]"

  have hp0_nth: "hp0 ! i = exc (zeros m) i <#> 0" if "i \<le> T' " for i
    using that assms map_nth len_hp0 by (metis (no_types, lifting) le_imp_less_Suc)
  then have hp0_eq_inputpos: "hp0 ! i = inputpos m i" if "i \<le> T' " for i
    using inputpos_def that by simp

  have hp1_nth: "hp1 ! i = exc (zeros m) i <#> 1" if "i \<le> T' " for i
    using that assms map_nth len_hp1 by (metis (no_types, lifting) le_imp_less_Suc)

  have previous_eq_prev: "previous hp1 idx = prev m idx" if "idx \<le> T' " for idx
  proof (cases "\<exists>i<idx. hp1 ! i = hp1 ! idx")
    case True
    then have 1: "\<exists>i<idx. exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1"
      using that hp1_nth by auto
    then have "prev m idx = (GREATEST i. i < idx \<and> exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1)"
      using prev_def by simp
    have "previous hp1 idx = (GREATEST i. i < idx \<and> hp1 ! i = hp1 ! idx)"
      using True previous_def by simp
    also have "... = (GREATEST i. i < idx \<and> exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1)"
      (is "Greatest ?P = Greatest ?Q")
    proof (rule Greatest_equality)
      have "\<exists>i. ?Q i"
        using 1 by simp
      moreover have 2: "\<forall>y. ?Q y \<longrightarrow> y \<le> idx"
        by simp
      ultimately have 3: "?Q (Greatest ?Q)"
        using GreatestI_ex_nat[of ?Q] by blast
      then have 4: "Greatest ?Q < idx"
        by simp
      then have "Greatest ?Q \<le> T' "
        using that by simp
      then have "hp1 ! (Greatest ?Q) = exc (zeros m) (Greatest ?Q) <#> 1"
        using hp1_nth by simp
      moreover have "hp1 ! idx = exc (zeros m) idx <#> 1"
        using that hp1_nth by simp
      ultimately have "hp1 ! (Greatest ?Q) = hp1 ! idx"
        using 3 by simp
      then show "?P (Greatest ?Q)"
        using 4 by simp
      show "i \<le> Greatest ?Q" if "?P i" for i
      proof -
        have "i < idx"
          using that by simp
        then have "hp1 ! i = exc (zeros m) i <#> 1"
          using `idx \<le> T' ` hp1_nth by simp
        moreover have "hp1 ! idx = exc (zeros m) idx <#> 1"
          using `idx \<le> T' ` hp1_nth by simp
        ultimately have "exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1"
          using that by simp
        then have "?Q i"
          using `i < idx` by simp
        then show ?thesis
          using Greatest_le_nat[of ?Q i] 2 by blast
      qed
    qed
    also have "... = prev m idx"
      using prev_def 1 by simp
    finally show ?thesis .
  next
    case False
    have "\<not> (\<exists>i<idx. exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1)"
    proof (rule ccontr)
      assume "\<not> (\<not> (\<exists>i<idx. exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1))"
      then obtain i where "i < idx" "exc (zeros m) i <#> 1 = exc (zeros m) idx <#> 1"
        by auto
      then have "hp1 ! i = hp1 ! idx"
        using hp1_nth that by simp
      then show False
        using False `i < idx` by simp
    qed
    then have "prev m idx = idx"
      using prev_def by auto
    moreover have "previous hp1 idx = idx"
      using False assms previous_def by auto
    ultimately show ?thesis
      by simp
  qed

  have "\<zeta>\<^sub>0 i @ \<zeta>\<^sub>1 i @ \<zeta>\<^sub>2 i = [N + i * Z..<N + (Suc i) * Z]" for i
    using zeta0_def zeta1_def zeta2_def upt_append_upt Z by simp
  then have zeta012: "\<zeta>\<^sub>0 i @ \<zeta>\<^sub>1 i @ \<zeta>\<^sub>2 i = [N + i * Z..<N + i * Z + Z]" for i
    by (simp add: ab_semigroup_add_class.add_ac(1) add.commute[of Z "i*Z"])
  have gamma: "\<gamma> (inputpos m i) = [inputpos m i * H..<inputpos m i * H + H]" for i
    using gamma_def by (simp add: add.commute)

  have rho: "\<rho> t = ?sigma" if "prev m t < t"
  proof -
    have "previous hp1 t \<noteq> t"
      using t that previous_eq_prev by simp
    then have "?sigma = [N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
        [N + prev m t * Z..<N + prev m t * Z + Z] @
        [N + t * Z..<N + t * Z + Z] @
        [inputpos m t * H..<inputpos m t * H + H]"
      using previous_eq_prev hp0_eq_inputpos t by simp
    also have "... = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1)) @
        (\<zeta>\<^sub>0 (prev m t) @ \<zeta>\<^sub>1 (prev m t) @ \<zeta>\<^sub>2 (prev m t)) @
        (\<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t) @
        \<gamma> (inputpos m t)"
      using zeta012 gamma by simp
    also have "... = \<rho> t"
      using rho_def by simp
    finally have "?sigma = \<rho> t" .
    then show ?thesis
      by simp
  qed

  have rho': "\<rho>' t = ?sigma" if "prev m t = t"
  proof -
    have "previous hp1 t = t"
      using t that previous_eq_prev by simp
    then have "?sigma = [N + (t - 1) * Z..<N + (t - 1) * Z + Z] @
        [N + t * Z..<N + t * Z + Z] @
        [inputpos m t * H..<inputpos m t * H + H]"
      using previous_eq_prev hp0_eq_inputpos t by simp
    also have "... = (\<zeta>\<^sub>0 (t - 1) @ \<zeta>\<^sub>1 (t - 1) @ \<zeta>\<^sub>2 (t - 1)) @
        (\<zeta>\<^sub>0 t @ \<zeta>\<^sub>1 t @ \<zeta>\<^sub>2 t) @
        \<gamma> (inputpos m t)"
      using zeta012 gamma by simp
    also have "... = \<rho>' t"
      using rho'_def by simp
    finally have "?sigma = \<rho>' t" .
    then show ?thesis
      by simp
  qed

  have "\<chi> t = relabel ?sigma (if previous hp1 t = t then \<psi>' else \<psi>)"
  proof (cases "prev m t < t")
    case True
    then have "\<chi> t = relabel (\<rho> t) \<psi>"
      using chi_def by simp
    moreover have "previous hp1 t < t"
      using t True previous_eq_prev by simp
    ultimately show ?thesis
      using rho True by simp
  next
    case False
    then have *: "prev m t = t"
      by (simp add: nat_less_le prev_le)
    then have "\<chi> t = relabel (\<rho>' t) \<psi>'"
      using chi_def by simp
    moreover have "previous hp1 t = t"
      using t * previous_eq_prev by simp
    ultimately show ?thesis
      using rho' * by simp
  qed

  then show "transforms (tm_chi j1 j2 j3) tps0 ttt tps'"
    using transforms_tm_chi[OF jk G Z N len_hp0 hp0 len_hp1 hp1 t T T'_less psi psi' tps0 _ assms(24)] assms(23)
    by simp
qed

lemma Z_sq_le: "Z^2 \<le> 2^(16*Z)"
proof -
  have "Z^2 \<le> 2^(2*Z)"
    using pow2_le_2pow2[of Z] by simp
  also have "... \<le> 2^(16*Z)"
    by simp
  finally show "Z^2 \<le> 2^(16*Z)" .
qed

lemma tm_PHI9 [transforms_intros]:
  fixes tps0 tps' :: "tape list" and k :: nat and j1 j2 j3 :: tapeidx
  fixes nss :: "nat list list"
  assumes jk: "length tps0 = k" "1 < j1" "j1 < j2" "j2 < j3" "j3 + 17 < k"
  assumes "hp0 = map (\<lambda>t. exc (zeros m) t <#> 0) [0..<Suc T']"
  assumes "hp1 = map (\<lambda>t. exc (zeros m) t <#> 1) [0..<Suc T']"
  assumes tps0:
    "tps0 ! 1 = nlltape nss"
    "tps0 ! j1 = (\<lfloor>hp0\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! j2 = (\<lfloor>hp1\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! j3 = (\<lfloor>N\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 2) = (\<lfloor>Z\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 3) = (\<lfloor>T'\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 4) = (\<lfloor>formula_n psi\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! (j3 + 5) = (\<lfloor>formula_n psi'\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! (j3 + 6) = (\<lfloor>1\<rfloor>\<^sub>N, 1)"
    "\<And>i. 6 < i \<Longrightarrow> i < 17 \<Longrightarrow> tps0 ! (j3 + i) = (\<lfloor>[]\<rfloor>, 1)"
  assumes tps': "tps' = tps0
        [1 := nlltape (nss @ formula_n \<Phi>\<^sub>9),
         j3 + 6 := (\<lfloor>Suc T'\<rfloor>\<^sub>N, 1),
         j3 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
  assumes "ttt = 16114767 * 2 ^ (16 * Z) * N ^ 7"
  shows "transforms (tm_PHI9 j1 j2 j3) tps0 ttt tps'"
proof -
  define tps where "tps = (\<lambda>t. tps0
        [1 := nlltape (nss @ concat (map (\<lambda>t. formula_n (\<chi> (Suc t))) [0..<t])),
         j3 + 6 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1),
         j3 + 3 := (\<lfloor>T' - t\<rfloor>\<^sub>N, 1)])"
  have "transforms (tm_PHI9 j1 j2 j3) (tps 0) ttt (tps T')"
    unfolding tm_PHI9_def
  proof (tform)
    let ?ttt = "16114765 * 2^(16*Z) * N ^ 6"
    show "transforms (tm_chi j1 j2 j3) (tps i) ?ttt (tps (Suc i))" if "i < T' " for i
    proof (rule tm_chi ; (use assms tps_def that in simp ; fail)?)
      show "tps (Suc i) = (tps i)
          [1 := nlltape
                ((nss @ concat (map (\<lambda>t. formula_n (\<chi> (Suc t))) [0..<i])) @
                  formula_n (\<chi> (Suc i))),
          j3 + 6 := (\<lfloor>Suc (Suc i)\<rfloor>\<^sub>N, 1),
          j3 + 3 := (\<lfloor>T' - i - 1\<rfloor>\<^sub>N, 1)]"
        using that tps_def by (simp add: list_update_swap)
    qed
    show "\<And>i. i < T' \<Longrightarrow> read (tps i) ! (j3 + 3) \<noteq> \<box>"
      using jk tps_def read_ncontents_eq_0 by simp
    show "\<not> read (tps T') ! (j3 + 3) \<noteq> \<box>"
      using jk tps_def read_ncontents_eq_0 by simp
    show "T' * (16114765 * 2 ^ (16 * Z) * N ^ 6 + 2) + 1 \<le> ttt"
    proof -
      have "T' * (16114765 * 2 ^ (16 * Z) * N ^ 6 + 2) + 1 \<le> T' * (16114767 * 2 ^ (16 * Z) * N ^ 6) + 1"
        using Z_sq_le H_gr_2 N_eq by auto
      also have "... \<le> T' * (16114767 * 2 ^ (16 * Z) * N ^ 6) + (16114767 * 2 ^ (16 * Z) * N ^ 6)"
        using H_gr_2 N_eq by auto
      also have "... = Suc T' * (16114767 * 2 ^ (16 * Z) * N ^ 6)"
        by simp
      also have "... \<le> N * (16114767 * 2 ^ (16 * Z) * N ^ 6)"
        using T'_less Suc_leI mult_le_mono1 by presburger
      also have "... = 16114767 * 2 ^ (16 * Z) * N ^ 7"
        by algebra
      also have "... = ttt"
        using assms(20) by simp
      finally show ?thesis .
    qed
  qed
  moreover have "tps 0 = tps0"
    using tps_def tps0 list_update_id[of tps0 "Suc 0"] list_update_id[of tps0 "j3 + 6"]
      list_update_id[of tps0 "j3 + 3"]
    by simp
  moreover have "tps T' = tps'"
  proof -
    have "concat (map (\<lambda>t. formula_n (\<chi> (Suc t))) [0..<T']) =
        formula_n (concat (map (\<lambda>t. \<chi> (Suc t)) [0..<T']))"
      using concat_formula_n by simp
    then show ?thesis
      using PHI9_def tps_def tps' list_update_id[of tps0 "Suc 0"] list_update_id[of tps0 "j3 + 6"]
        list_update_id[of tps0 "j3 + 3"]
      by simp
  qed
  ultimately show "transforms (tm_PHI9 j1 j2 j3) tps0 ttt tps'"
    by simp
qed

end  (* context reduction_sat_x *)

end
