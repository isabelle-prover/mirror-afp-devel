chapter \<open>Auxiliary Turing machines for reducing $\NP$ languages to \SAT{}\label{s:Aux_TM}\<close>

theory Aux_TM_Reducing
  imports Reducing
begin

text \<open>
In the previous chapter we have seen how to reduce a language $L\in\NP$ to
\SAT{} by constructing for every string $x$ a CNF formula $\Phi$ that is
satisfiable iff.\ $x\in L$. To complete the Cook-Levin theorem it remains to
show that there is a polynomial-time Turing machine that on input $x$ outputs
$\Phi$.  Constructing such a TM will be the subject of the rest of this article
and conclude in the next chapter. This chapter introduces several TMs used in
the construction.
\<close>


section \<open>Generating literals\<close>

text \<open>
Our representation of CNF formulas as lists of lists of numbers is based on a
representation of literals as numbers. Our function @{const literal_n} encodes
the positive literal $v_i$ as the number $2i + 1$ and the negative literal $\bar
v_i$ as $2i$. We already have the Turing machine @{const tm_times2} to cover the
second case. Now we build a TM for the first case, that is, for doubling and
incrementing.

\null
\<close>

definition tm_times2incr :: "tapeidx \<Rightarrow> machine" where
  "tm_times2incr j \<equiv> tm_times2 j ;; tm_incr j"

lemma tm_times2incr_tm:
  assumes "0 < j" and "j < k" and "G \<ge> 4"
  shows "turing_machine k G (tm_times2incr j)"
  unfolding tm_times2incr_def using tm_times2_tm tm_incr_tm assms by simp

lemma transforms_tm_times2incrI [transforms_intros]:
  fixes j :: tapeidx
  fixes k :: nat and tps tps' :: "tape list"
  assumes "k \<ge> 2" and "j > 0" and "j < k" and "length tps = k"
  assumes "tps ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
  assumes "t = 12 + 4 * nlength n"
  assumes "tps' = tps[j := (\<lfloor>Suc (2 * n)\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_times2incr j) tps t tps'"
proof -
  define tt where "tt = 10 + (2 * nlength n + 2 * nlength (2 * n))"
  have "transforms (tm_times2incr j) tps tt tps'"
    unfolding tm_times2incr_def by (tform tps: tt_def assms)
  moreover have "tt \<le> t"
  proof -
    have "tt = 10 + 2 * nlength n + 2 * nlength (2 * n)"
      using tt_def by simp
    also have "... \<le> 10 + 2 * nlength n + 2 * (Suc (nlength n))"
    proof -
      have "nlength (2 * n) \<le> Suc (nlength n)"
        by (metis eq_imp_le gr0I le_SucI nat_0_less_mult_iff nlength_even_le)
      then show ?thesis
        by simp
    qed
    also have "... = 12 + 4 * nlength n"
      by simp
    finally show ?thesis
      using assms(6) by simp
  qed
  ultimately show ?thesis
    using transforms_monotone by simp
qed

lemma literal_n_rename:
  assumes "v div 2 < length \<sigma>"
  shows "2 * \<sigma> ! (v div 2) + v mod 2 = (literal_n \<circ> rename \<sigma>) (n_literal v)"
proof (cases "even v")
  case True
  then show ?thesis
    using n_literal_def assms by simp
next
  case False
  then show ?thesis
    using n_literal_def assms by simp presburger
qed

text \<open>
Combining @{const tm_times2} and @{const tm_times2incr}, the next Turing machine
accepts a variable index $i$ on tape $j_1$ and a flag $b$ on tape $j_2$ and
outputs on tape $j_1$ the encoding of the positive literal $v_i$ or the negative
literal $\bar v_i$ if $b$ is positive or zero, respectively.
\<close>

definition tm_to_literal :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_to_literal j1 j2 \<equiv>
    IF \<lambda>rs. rs ! j2 = \<box> THEN
      tm_times2 j1
    ELSE
      tm_times2incr j1
    ENDIF"

lemma tm_to_literal_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j1" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_to_literal j1 j2)"
  unfolding tm_to_literal_def
  using assms tm_times2_tm tm_times2incr_tm turing_machine_branch_turing_machine
  by simp

lemma transforms_tm_to_literalI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k i b :: nat
  assumes "0 < j1" "j1 < k" "j2 < k" "2 \<le> k" "length tps = k"
  assumes
    "tps ! j1 = (\<lfloor>i\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>b\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 13 + 4 * nlength i"
  assumes "tps' = tps
    [j1 := (\<lfloor>2 * i + (if b = 0 then 0 else 1)\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_to_literal j1 j2) tps ttt tps'"
  unfolding tm_to_literal_def
proof (tform tps: assms read_ncontents_eq_0)
  show "5 + 2 * nlength i + 2 \<le> ttt" and "12 + 4 * nlength i + 1 \<le> ttt"
    using assms(8) by simp_all
qed


section \<open>A Turing machine for relabeling formulas\<close>

text \<open>
In order to construct $\Phi_9$, we must construct CNF formulas $\chi_t$, which
have the form $\rho(\psi)$ or $\rho'(\psi')$. So we need a Turing machine for
relabeling formulas. In this section we devise a Turing machine that gets a
substitution $\sigma$ and a CNF formula $\phi$ and outputs $\sigma(\phi)$. In
order to bound its running time we first prove some bounds on the length of
relabeled formulas.
\<close>


subsection \<open>The length of relabeled formulas\<close>

text \<open>
First we bound the length of the representation of a single relabeled clause.
In the following lemma the assumption ensures that the substitution $\sigma$ has
a value for every variable in the clause.
\<close>

lemma nllength_rename:
  assumes "\<forall>v\<in>set clause. v div 2 < length \<sigma>"
  shows "nllength (map (literal_n \<circ> rename \<sigma>) (n_clause clause)) \<le> length clause * Suc (nllength \<sigma>)"
proof (cases "\<sigma> = []")
  case True
  then show ?thesis
    using assms n_clause_def by simp
next
  case False
  let ?f = "literal_n \<circ> rename \<sigma> \<circ> n_literal"
  have *: "map (literal_n \<circ> rename \<sigma>) (n_clause clause) = map ?f clause"
    using n_clause_def by simp

  have "nlength (2 * n + 1) \<le> Suc (nlength n)" for n
    using nlength_times2plus1 by simp
  then have "nlength (2 * Max (set \<sigma>) + 1) \<le> Suc (nlength (Max (set \<sigma>)))"
    by simp
  moreover have "nlength (Max (set \<sigma>)) \<le> nllength \<sigma> - 1"
    using False member_le_nllength_1 by simp
  ultimately have "nlength (2 * Max (set \<sigma>) + 1) \<le> Suc (nllength \<sigma> - 1)"
    by simp
  then have **: "nlength (2 * Max (set \<sigma>) + 1) \<le> nllength \<sigma>"
    using nllength_gr_0 False by simp

  have "?f n \<le> 2 * (\<sigma> ! (n div 2)) + 1" if "n div 2 < length \<sigma>" for n
    using n_literal_def by (cases "even n") simp_all
  then have "?f v \<le> 2 * (\<sigma> ! (v div 2)) + 1" if "v \<in> set clause" for v
    using assms that by simp
  moreover have "\<sigma> ! (v div 2) \<le> Max (set \<sigma>)" if "v \<in> set clause" for v
    using that assms by simp
  ultimately have "?f v \<le> 2 * Max (set \<sigma>) + 1" if "v \<in> set clause" for v
    using that by fastforce
  then have "n \<le> 2 * Max (set \<sigma>) + 1" if "n \<in> set (map ?f clause)" for n
    using that by auto
  then have "nllength (map ?f clause) \<le> Suc (nlength (2 * Max (set \<sigma>) + 1)) * length (map ?f clause)"
    using nllength_le_len_mult_max by blast
  also have "... = Suc (nlength (2 * Max (set \<sigma>) + 1)) * length clause"
    by simp
  also have "... \<le> Suc (nllength \<sigma>) * length clause"
    using ** by simp
  finally have "nllength (map ?f clause) \<le> Suc (nllength \<sigma>) * length clause" .
  then show ?thesis
    using * by (metis mult.commute)
qed

text \<open>
Our upper bound for the length of the symbol representation of a relabeled
formula is fairly crude. It is basically the length of the string resulting from
replacing every symbol of the original formula by the entire substitution.
\<close>

lemma nlllength_relabel:
  assumes "\<forall>clause\<in>set \<phi>. \<forall>v\<in>set (clause_n clause). v div 2 < length \<sigma>"
  shows "nlllength (formula_n (relabel \<sigma> \<phi>)) \<le> Suc (nllength \<sigma>) * nlllength (formula_n \<phi>)"
  using assms
proof (induction \<phi>)
  case Nil
  then show ?case
    by (simp add: relabel_def)
next
  case (Cons clause \<phi>)
  let ?nclause = "clause_n clause"
  have "\<forall>v\<in>set ?nclause. v div 2 < length \<sigma>"
    using Cons.prems by simp
  then have "nllength (map (literal_n \<circ> rename \<sigma>) (n_clause ?nclause)) \<le> length ?nclause * Suc (nllength \<sigma>)"
    using nllength_rename by simp
  then have "nllength (map (literal_n \<circ> rename \<sigma>) clause) \<le> length clause * Suc (nllength \<sigma>)"
    using clause_n_def n_clause_n by simp
  moreover have "map (literal_n \<circ> rename \<sigma>) clause = clause_n (map (rename \<sigma>) clause)"
    using clause_n_def by simp
  ultimately have *: "nllength (clause_n (map (rename \<sigma>) clause)) \<le> length clause * Suc (nllength \<sigma>)"
    by simp

  have "formula_n (relabel \<sigma> (clause # \<phi>)) = clause_n (map (rename \<sigma>) clause) # formula_n (relabel \<sigma> \<phi>)"
    by (simp add: formula_n_def relabel_def)
  then have "nlllength (formula_n (relabel \<sigma> (clause # \<phi>))) =
      nllength (clause_n (map (rename \<sigma>) clause)) + 1 + nlllength (formula_n (relabel \<sigma> \<phi>))"
    using nlllength_Cons by simp
  also have "... \<le> length clause * Suc (nllength \<sigma>) + 1 + nlllength (formula_n (relabel \<sigma> \<phi>))"
    using * by simp
  also have "... \<le> length clause * Suc (nllength \<sigma>) + 1 + Suc (nllength \<sigma>) * nlllength (formula_n \<phi>)"
    using Cons by (metis add_mono_thms_linordered_semiring(2) insert_iff list.set(2))
  also have "... = 1 + Suc (nllength \<sigma>) * (length clause + nlllength (formula_n \<phi>))"
    by algebra
  also have "... \<le> Suc (nllength \<sigma>) * (1 + length clause + nlllength (formula_n \<phi>))"
    by simp
  also have "... \<le> Suc (nllength \<sigma>) * (1 + nllength (clause_n clause) + nlllength (formula_n \<phi>))"
    using length_le_nllength n_clause_def n_clause_n
    by (metis add_Suc_shift add_le_cancel_right length_map mult_le_mono2 plus_1_eq_Suc)
  also have "... = Suc (nllength \<sigma>) * (nlllength (formula_n (clause # \<phi>)))"
    using formula_n_def nlllength_Cons by simp
  finally show ?case .
qed

text \<open>
A simple sufficient condition for the assumption in the previous lemma.
\<close>

lemma variables_\<sigma>:
  assumes "variables \<phi> \<subseteq> {..<length \<sigma>}"
  shows "\<forall>clause\<in>set \<phi>.\<forall>v\<in>set (clause_n clause). v div 2 < length \<sigma>"
proof standard+
  fix clause :: clause and v :: nat
  assume clause: "clause \<in> set \<phi>" and v: "v \<in> set (clause_n clause)"

  obtain i where i: "i < length clause" "v = literal_n (clause ! i)"
    using v clause_n_def by (metis in_set_conv_nth length_map nth_map)
  then have clause_i: "clause ! i = n_literal v"
    using n_literal_n by simp

  show "v div 2 < length \<sigma>"
  proof (cases "even v")
    case True
    then have "clause ! i = Neg (v div 2)"
      using clause_i n_literal_def by simp
    then have "\<exists>c\<in>set \<phi>. Neg (v div 2) \<in> set c"
      using clause i(1) by (metis nth_mem)
    then have "v div 2 \<in> variables \<phi>"
      using variables_def by auto
    then show ?thesis
      using assms by auto
  next
    case False
    then have "clause ! i = Pos (v div 2)"
      using clause_i n_literal_def by simp
    then have "\<exists>c\<in>set \<phi>. Pos (v div 2) \<in> set c"
      using clause i(1) by (metis nth_mem)
    then have "v div 2 \<in> variables \<phi>"
      using variables_def by auto
    then show ?thesis
      using assms by auto
  qed
qed

text \<open>
Combining the previous two lemmas yields this upper bound:
\<close>

lemma nlllength_relabel_variables:
  assumes "variables \<phi> \<subseteq> {..<length \<sigma>}"
  shows "nlllength (formula_n (relabel \<sigma> \<phi>)) \<le> Suc (nllength \<sigma>) * nlllength (formula_n \<phi>)"
  using assms variables_\<sigma> nlllength_relabel by blast


subsection \<open>Relabeling clauses\<close>

text \<open>
Relabeling a CNF formula is accomplished by relabeling each of its clauses. In
this section we devise a Turing machine for relabeling clauses. The TM accepts
on tape $j$ a list of numbers representing a substitution $\sigma$ and on tape
$j + 1$ a clause represented as a list of numbers. It outputs on tape $j + 2$
the relabeled clause, consuming the original clause on tape $j + 1$ in the
process.
\<close>

definition tm_relabel_clause :: "tapeidx \<Rightarrow> machine" where
  "tm_relabel_clause j \<equiv>
    WHILE [] ; \<lambda>rs. rs ! (j + 1) \<noteq> \<box> DO
      tm_nextract \<bar> (j + 1) (j + 3) ;;
      tm_mod2 (j + 3) (j + 4) ;;
      tm_div2 (j + 3) ;;
      tm_nth_inplace j (j + 3) \<bar> ;;
      tm_to_literal (j + 3) (j + 4) ;;
      tm_append (j + 2) (j + 3) ;;
      tm_setn (j + 3) 0 ;;
      tm_setn (j + 4) 0
    DONE ;;
    tm_cr (j + 2) ;;
    tm_erase_cr (j + 1)"

lemma tm_relabel_clause_tm:
  assumes "G \<ge> 5" and "j + 4 < k" and "0 < j"
  shows "turing_machine k G (tm_relabel_clause j)"
  unfolding tm_relabel_clause_def
  using assms tm_nextract_tm tm_mod2_tm tm_div2_tm tm_nth_inplace_tm tm_to_literal_tm tm_append_tm tm_setn_tm
    tm_cr_tm tm_erase_cr_tm Nil_tm turing_machine_loop_turing_machine
  by simp

locale turing_machine_relabel_clause =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_nextract \<bar> (j + 1) (j + 3)"
definition "tm2 \<equiv> tm1 ;; tm_mod2 (j + 3) (j + 4)"
definition "tm3 \<equiv> tm2 ;; tm_div2 (j + 3)"
definition "tm4 \<equiv> tm3 ;; tm_nth_inplace j (j + 3) \<bar>"
definition "tm5 \<equiv> tm4 ;; tm_to_literal (j + 3) (j + 4)"
definition "tm6 \<equiv> tm5 ;; tm_append (j + 2) (j + 3)"
definition "tm7 = tm6 ;; tm_setn (j + 3) 0"
definition "tm8 \<equiv> tm7 ;; tm_setn (j + 4) 0"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! (j + 1) \<noteq> \<box> DO tm8 DONE"
definition "tm9 \<equiv> tmL ;; tm_cr (j + 2)"
definition "tm10 \<equiv> tm9 ;; tm_erase_cr (j + 1)"

lemma tm10_eq_tm_relabel_clause: "tm10 = tm_relabel_clause j"
  unfolding tm_relabel_clause_def tm3_def tmL_def tm5_def tm4_def tm1_def tm2_def tm6_def tm7_def tm8_def tm9_def tm10_def
  by simp

context
  fixes tps0 :: "tape list" and k :: nat and \<sigma> clause :: "nat list"
  assumes clause: "\<forall>v\<in>set clause. v div 2 < length \<sigma>"
  assumes jk: "0 < j" "j + 4 < k" "length tps0 = k"
  assumes tps0:
    "tps0 ! j = (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j + 1) = (\<lfloor>clause\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tpsL t \<equiv> tps0
  [j + 1 := nltape' clause t,
   j + 2 := nltape (take t (map literal_n (map (rename \<sigma>) (n_clause clause))))]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
  using tpsL_def tps0 jk nllength_Nil by (metis One_nat_def list_update_id take0)

definition "tps1 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take t (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 3 := (\<lfloor>clause ! t\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "t < length clause"
    and "ttt = 12 + 2 * nlength (clause ! t)"
  shows "transforms tm1 (tpsL t) ttt (tps1 t)"
  unfolding tm1_def
proof (tform tps: assms(1) tpsL_def tps1_def tps0 jk)
  show "ttt = 12 + 2 * nlength 0 + 2 * nlength (clause ! t)"
    using assms(2) by simp
qed

definition "tps2 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take t (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 3 := (\<lfloor>clause ! t\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>(clause ! t) mod 2\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "t < length clause"
    and "ttt = 13 + 2 * nlength (clause ! t)"
  shows "transforms tm2 (tpsL t) ttt (tps2 t)"
  unfolding tm2_def by (tform tps: assms tps1_def tps2_def tps0 jk)

definition "tps3 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take t (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 3 := (\<lfloor>clause ! t div 2\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>clause ! t mod 2\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "t < length clause"
    and "ttt = 16 + 4 * nlength (clause ! t)"
  shows "transforms tm3 (tpsL t) ttt (tps3 t)"
  unfolding tm3_def by (tform tps: assms(1) tps2_def tps3_def jk time: assms(2))

definition "tps4 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take t (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 3 := (\<lfloor>\<sigma> ! (clause ! t div 2)\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>clause ! t mod 2\<rfloor>\<^sub>N, 1)]"

lemma tm4 [transforms_intros]:
  assumes "t < length clause"
    and "ttt = 28 + 4 * nlength (clause ! t) + 18 * (nllength \<sigma>)\<^sup>2"
  shows "transforms tm4 (tpsL t) ttt (tps4 t)"
  unfolding tm4_def
proof (tform tps: assms(1) tps0 tps3_def tps4_def jk clause time: assms(2))
  show "tps4 t = (tps3 t)[j + 3 := (\<lfloor>\<sigma> ! (clause ! t div 2)\<rfloor>\<^sub>N, 1)]"
    unfolding tps4_def tps3_def by (simp add: list_update_swap[of "j + 3"])
qed

definition "tps5 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take t (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 3 := (\<lfloor>2 * (\<sigma> ! (clause ! t div 2)) + clause ! t mod 2\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>clause ! t mod 2\<rfloor>\<^sub>N, 1)]"

lemma tm5 [transforms_intros]:
  assumes "t < length clause"
   and "ttt = 41 + 4 * nlength (clause ! t) + 18 * (nllength \<sigma>)\<^sup>2 +
      4 * nlength (\<sigma> ! (clause ! t div 2))"
  shows "transforms tm5 (tpsL t) ttt (tps5 t)"
  unfolding tm5_def by (tform tps: assms(1) tps0 tps4_def tps5_def jk time: assms(2))

definition "tps6 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take (Suc t) (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 3 := (\<lfloor>2 * (\<sigma> ! (clause ! t div 2)) + clause ! t mod 2\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>clause ! t mod 2\<rfloor>\<^sub>N, 1)]"

lemma tm6:
  assumes "t < length clause"
   and "ttt = 47 + 4 * nlength (clause ! t) + 18 * (nllength \<sigma>)\<^sup>2 +
      4 * nlength (\<sigma> ! (clause ! t div 2)) +
      2 * nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2)"
  shows "transforms tm6 (tpsL t) ttt (tps6 t)"
  unfolding tm6_def
proof (tform tps: assms(1) tps0 tps5_def tps6_def jk)
  have "2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2 =
      (literal_n \<circ> rename \<sigma>) (n_literal (clause ! t))"
    using clause assms(1) literal_n_rename by simp
  then have "2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2 =
      (map (literal_n \<circ> rename \<sigma>) (n_clause clause)) ! t"
    using assms(1) by (simp add: n_clause_def)
  then have "take t (map (literal_n \<circ> rename \<sigma>) (n_clause clause)) @
        [2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2] =
      take (Suc t) (map (literal_n \<circ> rename \<sigma>) (n_clause clause))"
    by (simp add: assms(1) n_clause_def take_Suc_conv_app_nth)
  then show "tps6 t = (tps5 t)
      [j + 2 := nltape
        (take t (map (literal_n \<circ> rename \<sigma>) (n_clause clause)) @
         [2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2])]"
    unfolding tps5_def tps6_def
    by (simp only: list_update_overwrite list_update_swap_less[of "j + 2"]) simp
  show "ttt = 41 + 4 * nlength (clause ! t) + 18 * (nllength \<sigma>)\<^sup>2 +
      4 * nlength (\<sigma> ! (clause ! t div 2)) +
      (7 + nllength (take t (map (literal_n \<circ> rename \<sigma>) (n_clause clause))) -
       Suc (nllength (take t (map (literal_n \<circ> rename \<sigma>) (n_clause clause)))) +
       2 * nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2))"
    using assms(2) by simp
qed

lemma nlength_\<sigma>1:
  assumes "t < length clause"
  shows "nlength (clause ! t) \<le> nllength \<sigma>"
proof -
  have "clause ! t div 2 < length \<sigma>"
    using clause assms(1) by simp
  then have "nlength (clause ! t div 2) < length \<sigma>"
    using nlength_le_n by (meson leD le_less_linear order.trans)
  then have "nlength (clause ! t) \<le> length \<sigma>"
    using canrepr_div_2 by simp
  then show "nlength (clause ! t) \<le> nllength \<sigma>"
    using length_le_nllength by (meson dual_order.trans mult_le_mono2)
qed

lemma nlength_\<sigma>2:
  assumes "t < length clause"
  shows "nlength (\<sigma> ! (clause ! t div 2)) \<le> nllength \<sigma>"
  using assms clause member_le_nllength nth_mem by simp

lemma nlength_\<sigma>3:
  assumes "t < length clause"
  shows "nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2) \<le> Suc (nllength \<sigma>)"
proof -
  have "nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2) \<le> nlength (2 * \<sigma> ! (clause ! t div 2) + 1)"
    using nlength_mono by simp
  also have "... \<le> Suc (nlength (\<sigma> ! (clause ! t div 2)))"
    using nlength_times2plus1 by (meson dual_order.trans)
  finally show ?thesis
    using nlength_\<sigma>2 assms by fastforce
qed

lemma tm6' [transforms_intros]:
  assumes "t < length clause"
   and "ttt = 49 + 28 * nllength \<sigma> ^ 2"
  shows "transforms tm6 (tpsL t) ttt (tps6 t)"
proof -
  let ?ttt = "47 + 4 * nlength (clause ! t) + 18 * (nllength \<sigma>)\<^sup>2 +
      4 * nlength (\<sigma> ! (clause ! t div 2)) +
      2 * nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2)"

  have "?ttt \<le> 47 + 4 * nllength \<sigma> + 18 * (nllength \<sigma>)\<^sup>2 +
      4 * nllength \<sigma> + 2 * Suc (nllength \<sigma>)"
    using nlength_\<sigma>1 nlength_\<sigma>3 nlength_\<sigma>2 assms(1) by fastforce
  also have "... = 49 + 10 * nllength \<sigma> + 18 * (nllength \<sigma>)\<^sup>2"
    by simp
  also have "... \<le> 49 + 10 * nllength \<sigma> ^ 2 + 18 * (nllength \<sigma>)\<^sup>2"
    using linear_le_pow by simp
  also have "... = 49 + 28 * nllength \<sigma> ^ 2"
    by simp
  finally have "?ttt \<le> 49 + 28 * nllength \<sigma> ^ 2" .
  then show ?thesis
    using tm6 assms transforms_monotone by blast
qed

definition "tps7 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take (Suc t) (map literal_n (map (rename \<sigma>) (n_clause clause)))),
   j + 4 := (\<lfloor>clause ! t mod 2\<rfloor>\<^sub>N, 1)]"

lemma tm7:
  assumes "t < length clause"
   and "ttt = 59 + 28 * nllength \<sigma> ^ 2 +
      2 * nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2)"
  shows "transforms tm7 (tpsL t) ttt (tps7 t)"
  unfolding tm7_def
proof (tform tps: assms(1) tps0 tps6_def tps7_def jk time: assms(2))
  show "tps7 t = (tps6 t)[j + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using tps6_def tps7_def tps0 jk
    by (smt (z3) add_left_cancel list_update_id list_update_overwrite list_update_swap num.simps(8)
      numeral_eq_iff one_eq_numeral_iff semiring_norm(84))
qed

lemma tm7' [transforms_intros]:
  assumes "t < length clause"
   and "ttt = 61 + 30 * nllength \<sigma> ^ 2"
  shows "transforms tm7 (tpsL t) ttt (tps7 t)"
proof -
  let ?ttt = "59 + 28 * nllength \<sigma> ^ 2 +
      2 * nlength (2 * \<sigma> ! (clause ! t div 2) + clause ! t mod 2)"
  have "?ttt \<le> 59 + 28 * nllength \<sigma> ^ 2 + 2 * Suc (nllength \<sigma>)"
    using nlength_\<sigma>3 assms(1) by fastforce
  also have "... = 61 + 28 * nllength \<sigma> ^ 2 + 2 * nllength \<sigma>"
    by simp
  also have "... \<le> 61 + 30 * nllength \<sigma> ^ 2"
    using linear_le_pow by simp
  finally have "?ttt \<le> 61 + 30 * nllength \<sigma> ^ 2" .
  then show ?thesis
    using assms tm7 transforms_monotone by blast
qed

definition "tps8 t \<equiv> tps0
  [j + 1 := nltape' clause (Suc t),
   j + 2 := nltape (take (Suc t) (map literal_n (map (rename \<sigma>) (n_clause clause))))]"

lemma tm8:
  assumes "t < length clause"
    and "ttt = 61 + 30 * (nllength \<sigma>)\<^sup>2 + (10 + 2 * nlength (clause ! t mod 2))"
  shows "transforms tm8 (tpsL t) ttt (tps8 t)"
  unfolding tm8_def
proof (tform tps: assms(1) tps0 tps7_def tps8_def jk time: assms(2))
  show "tps8 t = (tps7 t)[j + 4 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using tps7_def tps8_def tps0 jk
    by (smt (z3) add_left_imp_eq list_update_id list_update_overwrite list_update_swap numeral_eq_iff
      numeral_eq_one_iff semiring_norm(85) semiring_norm(87))
qed

lemma tm8' [transforms_intros]:
  assumes "t < length clause"
    and "ttt = 71 + 32 * (nllength \<sigma>)\<^sup>2"
  shows "transforms tm8 (tpsL t) ttt (tpsL (Suc t))"
proof -
  have "nlength (clause ! t mod 2) \<le> nllength \<sigma>"
    using assms(1) nlength_\<sigma>1 by (meson mod_less_eq_dividend nlength_mono order.trans)
  then have "nlength (clause ! t mod 2) \<le> nllength \<sigma> ^ 2"
    using linear_le_pow by (metis nat_le_linear power2_nat_le_imp_le verit_la_disequality)
  then have "61 + 30 * (nllength \<sigma>)\<^sup>2 + (10 + 2 * nlength (clause ! t mod 2)) \<le> ttt"
    using assms(2) by simp
  then have "transforms tm8 (tpsL t) ttt (tps8 t)"
    using assms(1) tm8 transforms_monotone by blast
  moreover have "tps8 t = tpsL (Suc t)"
    using tps8_def tpsL_def by simp
  ultimately show ?thesis
    by simp
qed

lemma tmL [transforms_intros]:
  assumes "ttt = length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length clause))"
  unfolding tmL_def
proof (tform)
  let ?t = "71 + 32 * (nllength \<sigma>)\<^sup>2"
  show "read (tpsL t) ! (j + 1) \<noteq> \<box>" if "t < length clause" for t
  proof -
    have "tpsL t ! (j + 1) = nltape' clause t"
      using tpsL_def jk by simp
    then show ?thesis
      using nltape'_tape_read that tapes_at_read' tpsL_def jk
      by (smt (z3) Suc_eq_plus1 leD length_list_update less_add_same_cancel1 less_trans_Suc zero_less_numeral)
  qed
  show "\<not> read (tpsL (length clause)) ! (j + 1) \<noteq> \<box>"
  proof -
    have "tpsL (length clause) ! (j + 1) = nltape' clause (length clause)"
      using tpsL_def jk by simp
    then show ?thesis
      using nltape'_tape_read tapes_at_read' tpsL_def jk
      by (smt (z3) Suc_eq_plus1 length_list_update less_add_same_cancel1 less_or_eq_imp_le less_trans_Suc zero_less_numeral)
  qed
  show "length clause * (71 + 32 * (nllength \<sigma>)\<^sup>2 + 2) + 1 \<le> ttt"
    using assms(1) by simp
qed

lemma tpsL_length: "tpsL (length clause) = tps0
  [j + 1 := nltape' clause (length clause),
   j + 2 := nltape (map literal_n (map (rename \<sigma>) (n_clause clause)))]"
  using tpsL_def by (simp add: n_clause_def)

definition "tps9 \<equiv> tps0
  [j + 1 := nltape' clause (length clause),
   j + 2 := (\<lfloor>map literal_n (map (rename \<sigma>) (n_clause clause))\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm9:
  assumes "ttt = 4 + length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
      nllength (map (literal_n \<circ> rename \<sigma>) (n_clause clause))"
  shows "transforms tm9 (tpsL 0) ttt tps9"
  unfolding tm9_def
proof (tform tps: tps0 tps9_def tpsL_def jk tpsL_length)
  show "clean_tape (tpsL (length clause) ! (j + 2))"
    using tpsL_def jk clean_tape_nlcontents tps0(3) by simp
  show "ttt = length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) + 1 +
    (tpsL (length clause) :#: (j + 2) + 2)"
    using n_clause_def assms jk tpsL_length by fastforce
qed

lemma tm9' [transforms_intros]:
  assumes "ttt = 4 + 2 * length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2)"
  shows "transforms tm9 tps0 ttt tps9"
proof -
  let ?ttt = "4 + length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
    nllength (map (literal_n \<circ> rename \<sigma>) (n_clause clause))"
  have "?ttt \<le> 4 + length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
      length clause * Suc (nllength \<sigma>)"
    using clause nllength_rename by simp
  also have "... \<le> 4 + length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
      length clause * (Suc (nllength \<sigma> ^ 2))"
    by (simp add: linear_le_pow)
  also have "... \<le> 4 + length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
      length clause * (73 + nllength \<sigma> ^ 2)"
    by (metis One_nat_def Suc_eq_plus1 Suc_leI add.commute add_left_mono mult_le_mono2 zero_less_numeral)
  also have "... \<le> 4 + length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
      length clause * (73 + 32 * nllength \<sigma> ^ 2)"
    by simp
  also have "... = 4 + 2 * length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2)"
    by simp
  finally have "?ttt \<le> 4 + 2 * length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2)" .
  then show ?thesis
    using tm9 assms transforms_monotone tpsL_eq_tps0 by fastforce
qed

definition "tps10 \<equiv> tps0
  [j + 1 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
   j + 2 := (\<lfloor>map literal_n (map (rename \<sigma>) (n_clause clause))\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm10:
  assumes "ttt = 11 + 2 * length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) + 3 * nllength clause"
  shows "transforms tm10 tps0 ttt tps10"
  unfolding tm10_def
proof (tform tps: tps0 tps9_def jk)
  show "tps9 ::: (j + 1) = \<lfloor>numlist clause\<rfloor>"
    using tps9_def jk tps0(2) nlcontents_def by simp
  show "proper_symbols (numlist clause)"
    using proper_symbols_numlist by simp
  show "tps10 = tps9[j + 1 := (\<lfloor>[]\<rfloor>, 1)]"
    by (simp add: jk nlcontents_def tps0 tps10_def tps9_def list_update_swap numlist_Nil)
  show "ttt = 4 + 2 * length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) +
      (tps9 :#: (j + 1) + 2 * length (numlist clause) + 6)"
    using assms tps9_def jk nllength_def by simp
qed

lemma tm10':
  assumes "ttt = 11 + 64 * nllength clause * (3 + (nllength \<sigma>)\<^sup>2)"
  shows "transforms tm10 tps0 ttt tps10"
proof -
  let ?ttt = "11 + 2 * length clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) + 3 * nllength clause"
  have "?ttt \<le> 11 + 2 * nllength clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) + 3 * nllength clause"
    by (simp add: length_le_nllength)
  also have "... \<le> 11 + 2 * nllength clause * (73 + 32 * (nllength \<sigma>)\<^sup>2) + 2 * 2 * nllength clause"
    by simp
  also have "... = 11 + 2 * nllength clause * (75 + 32 * (nllength \<sigma>)\<^sup>2)"
    by algebra
  also have "... \<le> 11 + 2 * nllength clause * (96 + 32 * (nllength \<sigma>)\<^sup>2)"
    by simp
  also have "... = 11 + 2 * 32 * nllength clause * (3 + (nllength \<sigma>)\<^sup>2)"
    by simp
  also have "... = 11 + 64 * nllength clause * (3 + (nllength \<sigma>)\<^sup>2)"
    by simp
  finally have "?ttt \<le> 11 + 64 * nllength clause * (3 + (nllength \<sigma>)\<^sup>2)" .
  then show ?thesis
    using tm10 assms transforms_monotone by blast
qed

end

end  (* locale turing_machine_relabel-clause *)

lemma transforms_tm_relabel_clauseI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k :: nat and \<sigma> clause :: "nat list"
  assumes "0 < j" "j + 4 < k" "length tps = k"
    and "\<forall>v\<in>set clause. v div 2 < length \<sigma>"
  assumes
    "tps ! j = (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j + 1) = (\<lfloor>clause\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 11 + 64 * nllength clause * (3 + (nllength \<sigma>)\<^sup>2)"
  assumes "tps' = tps
    [j + 1 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
     j + 2 := (\<lfloor>clause_n (map (rename \<sigma>) (n_clause clause))\<rfloor>\<^sub>N\<^sub>L, 1)]"
  shows "transforms (tm_relabel_clause j) tps ttt tps'"
proof -
  interpret loc: turing_machine_relabel_clause j .
  show ?thesis
    using assms loc.tm10_eq_tm_relabel_clause loc.tps10_def loc.tm10' clause_n_def by simp
qed


subsection \<open>Relabeling CNF formulas\<close>

text \<open>
A Turing machine can relabel a CNF formula by relabeling each clause using the
TM @{const tm_relabel_clause}. The next TM accepts a CNF formula as a list of
lists of literals on tape $j_1$ and a substitution $\sigma$ as a list of numbers
on tape $j_2 + 1$. It outputs the relabeled formula on tape $j_2$, which
initially must be empty.
\<close>

definition tm_relabel :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_relabel j1 j2 \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      tm_nextract \<sharp> j1 (j2 + 2) ;;
      tm_relabel_clause (j2 + 1) ;;
      tm_appendl j2 (j2 + 3) ;;
      tm_erase_cr (j2 + 3)
    DONE ;;
    tm_cr j1 ;;
    tm_cr j2"

lemma tm_relabel_tm:
  assumes "G \<ge> 6" and "j2 + 5 < k" and "0 < j1" and "j1 < j2"
  shows "turing_machine k G (tm_relabel j1 j2)"
  unfolding tm_relabel_def
  using assms tm_cr_tm tm_nextract_tm tm_appendl_tm tm_relabel_clause_tm Nil_tm tm_erase_cr_tm turing_machine_loop_turing_machine
  by simp

locale turing_machine_relabel =
  fixes j1 j2 :: tapeidx
begin

definition "tmL1 \<equiv> tm_nextract \<sharp> j1 (j2 + 2)"
definition "tmL2 \<equiv> tmL1 ;; tm_relabel_clause (j2 + 1)"
definition "tmL3 \<equiv> tmL2 ;; tm_appendl j2 (j2 + 3)"
definition "tmL4 \<equiv> tmL3 ;; tm_erase_cr (j2 + 3)"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tmL4 DONE"
definition "tm2 \<equiv> tmL ;; tm_cr j1"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"

lemma tm3_eq_tm_relabel: "tm3 = tm_relabel j1 j2"
  unfolding tm_relabel_def tm2_def tmL_def tmL4_def tmL3_def tmL2_def tmL1_def tm3_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and \<sigma> :: "nat list" and \<phi> :: formula
  assumes variables: "variables \<phi> \<subseteq> {..<length \<sigma>}"
  assumes jk: "0 < j1" "j1 < j2" "j2 + 5 < k" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>formula_n \<phi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! (j2 + 1) = (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j2 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j2 + 3) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j2 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j2 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

abbreviation n\<phi> :: "nat list list" where
  "n\<phi> \<equiv> formula_n \<phi>"

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
     [j1 := nlltape' n\<phi> t,
      j2 := nlltape (formula_n (take t (relabel \<sigma> \<phi>)))]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
  using tps0 tpsL_def formula_n_def nlllength_def numlist_Nil numlist_def numlistlist_def
  by (metis One_nat_def list.map(1) list.size(3) list_update_id take0)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
     [j1 := nlltape' n\<phi> (Suc t),
      j2 := nlltape (formula_n (take t (relabel \<sigma> \<phi>))),
      j2 + 2 := (\<lfloor>n\<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "ttt = 12 + 2 * nllength (n\<phi> ! t)"
    and "t < length \<phi>"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def
proof (tform tps: tps0 tpsL_def tpsL1_def jk)
  show "t < length n\<phi>"
    using assms(2) formula_n_def by simp
  show "tpsL1 t = (tpsL t)
      [j1 := nlltape' n\<phi> (Suc t),
       j2 + 2 := (\<lfloor>n\<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1)]"
    using tpsL1_def tpsL_def by (simp add: jk list_update_swap_less)
  show "ttt = 12 + 2 * nllength [] + 2 * nllength (n\<phi> ! t)"
    using assms(1) by simp
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
     [j1 := nlltape' n\<phi> (Suc t),
      j2 := nlltape (formula_n (take t (relabel \<sigma> \<phi>))),
      j2 + 2 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
      j2 + 3 := (\<lfloor>clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tmL2 [transforms_intros]:
  assumes "ttt = 23 + 2 * nllength (n\<phi> ! t) + 64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2)"
    and "t < length \<phi>"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def
proof (tform tps: assms(2) tps0 tpsL1_def jk)
  show "\<forall>v\<in>set (n\<phi> ! t). v div 2 < length \<sigma>"
    using variables_\<sigma> variables assms(2) by (metis formula_n_def nth_map nth_mem)
  have "tpsL1 t ! (j2 + (1 + 2)) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tpsL1_def jk tps0 by (simp add: numeral_3_eq_3)
  then show "tpsL1 t ! (j2 + 1 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    by (metis add.assoc)
  have "tpsL1 t ! (j2 + (1 + 3)) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def jk tps0 by simp
  then show "tpsL1 t ! (j2 + 1 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by (metis add.assoc)
  have "tpsL1 t ! (j2 + (1 + 4)) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def jk tps0 by simp
  then show "tpsL1 t ! (j2 + 1 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by (metis add.assoc)
  have "tpsL2 t = (tpsL1 t)
    [j2 + (1 + 1) := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
     j2 + (1 + 2) := (\<lfloor>clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))\<rfloor>\<^sub>N\<^sub>L, 1)]"
    using jk tps0 tpsL1_def tpsL2_def by (simp add: numeral_3_eq_3)
  then show "tpsL2 t = (tpsL1 t)
    [j2 + 1 + 1 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
     j2 + 1 + 2 := (\<lfloor>clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))\<rfloor>\<^sub>N\<^sub>L, 1)]"
    by (metis add.assoc)
  show "ttt = 12 + 2 * nllength (n\<phi> ! t) +
      (11 + 64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2))"
    using assms(1) by simp
qed

definition tpsL3 :: "nat \<Rightarrow> tape list" where
  "tpsL3 t \<equiv> tps0
     [j1 := nlltape' n\<phi> (Suc t),
      j2 := nlltape
        (formula_n (take t (relabel \<sigma> \<phi>)) @ [clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))]),
      j2 + 2 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
      j2 + 3 := (\<lfloor>clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tmL3 [transforms_intros]:
  assumes "ttt = 29 + 2 * nllength (n\<phi> ! t) +
      64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2) +
      2 * nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t))))"
    and "t < length \<phi>"
  shows "transforms tmL3 (tpsL t) ttt (tpsL3 t)"
  unfolding tmL3_def
proof (tform tps: assms(2) tps0 tpsL2_def jk)
  show "tpsL3 t = (tpsL2 t)
      [j2 := nlltape (formula_n (take t (relabel \<sigma> \<phi>)) @ [clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))])]"
    unfolding tpsL3_def tpsL2_def by (simp add: list_update_swap_less[of j2])
  show "ttt = 23 + 2 * nllength (n\<phi> ! t) + 64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2) +
      (7 + nlllength (formula_n (take t (relabel \<sigma> \<phi>))) - Suc (nlllength (formula_n (take t (relabel \<sigma> \<phi>)))) +
       2 * nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))))"
    using assms(1) by simp
qed

definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
     [j1 := nlltape' n\<phi> (Suc t),
      j2 := nlltape
        (formula_n (take t (relabel \<sigma> \<phi>)) @ [clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))]),
      j2 + 2 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tmL4:
  assumes "ttt = 36 + 2 * nllength (n\<phi> ! t) +
      64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2) +
      4 * nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t))))"
    and "t < length \<phi>"
  shows "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
  unfolding tmL4_def
proof (tform tps: assms(2) tps0 tpsL3_def jk)
  let ?zs = "numlist (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t))))"
  show "tpsL3 t ::: (j2 + 3) = \<lfloor>?zs\<rfloor>"
    using tpsL3_def nlcontents_def jk by simp
  show "proper_symbols ?zs"
    using proper_symbols_numlist by simp
  have *: "j1 \<noteq> j2 + 3"
    using jk by simp
  have "\<lfloor>[]\<rfloor> = \<lfloor>[]\<rfloor>\<^sub>N\<^sub>L"
    using nlcontents_def numlist_Nil by simp
  then show "tpsL4 t = (tpsL3 t)[j2 + 3 := (\<lfloor>[]\<rfloor>, 1)]"
    using tpsL3_def tpsL4_def tps0 jk list_update_id[of tps0 "j2+3"]
    by (simp add: list_update_swap[OF *] list_update_swap[of _ "j2 + 3"])
  show "ttt = 29 + 2 * nllength (n\<phi> ! t) + 64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2) +
      2 * nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))) +
      (tpsL3 t :#: (j2 + 3) + 2 * length (numlist (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t))))) + 6)"
    using assms(1) tpsL3_def jk nllength_def by simp
qed

lemma nllength_1:
  assumes "t < length \<phi>"
  shows "nllength (n\<phi> ! t) \<le> nlllength n\<phi>"
  using assms formula_n_def nlllength_take by (metis le_less_linear length_map less_trans not_add_less2)

lemma nllength_2:
  assumes "t < length \<phi>"
  shows "nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))) \<le> nlllength (formula_n (relabel \<sigma> \<phi>))"
    (is "?l \<le> ?r")
proof -
  have "?l = nllength (clause_n (map (rename \<sigma>) (\<phi> ! t)))"
    using assms by (simp add: formula_n_def n_clause_n)
  moreover have "clause_n (map (rename \<sigma>) (\<phi> ! t)) \<in> set (formula_n (relabel \<sigma> \<phi>))"
    using assms formula_n_def relabel_def by simp
  ultimately show ?thesis
    using member_le_nlllength_1 by fastforce
qed

definition "tpsL4' t \<equiv> tps0
     [j1 := nlltape' n\<phi> (Suc t),
      j2 := nlltape (formula_n (take (Suc t) (relabel \<sigma> \<phi>)))]"

lemma tpsL4:
  assumes "t < length \<phi>"
  shows "tpsL4 t = tpsL4' t"
proof -
  have "formula_n (take t (relabel \<sigma> \<phi>)) @ [clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t)))] =
      formula_n (take (Suc t) (relabel \<sigma> \<phi>))"
    using assms formula_n_def relabel_def by (simp add: n_clause_n take_Suc_conv_app_nth)
  then show ?thesis
    using tpsL4_def tpsL4'_def jk tps0
    by (smt (verit, del_insts) Suc_1 add_Suc_right add_cancel_left_right less_SucI
      list_update_id list_update_swap not_less_eq numeral_1_eq_Suc_0 numeral_One)
qed

lemma tpsL4'_eq_tpsL: "tpsL4' t = tpsL (Suc t)"
  using tpsL_def tpsL4'_def by simp

lemma tmL4' [transforms_intros]:
  assumes "ttt = 36 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * nlllength (formula_n (relabel \<sigma> \<phi>))"
    and "t < length \<phi>"
  shows "transforms tmL4 (tpsL t) ttt (tpsL (Suc t))"
proof -
  let ?ttt = "36 + 2 * nllength (n\<phi> ! t) +
      64 * nllength (n\<phi> ! t) * (3 + (nllength \<sigma>)\<^sup>2) +
      4 * nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t))))"
  have "?ttt \<le> 36 + 2 * nlllength n\<phi> +
      64 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) +
      4 * nllength (clause_n (map (rename \<sigma>) (n_clause (n\<phi> ! t))))"
    using nllength_1 assms(2) add_le_mono add_le_mono1 mult_le_mono1 mult_le_mono2 nat_add_left_cancel_le
    by metis
  also have "... \<le> 36 + 2 * nlllength n\<phi> +
      64 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) +
      4 * nlllength (formula_n (relabel \<sigma> \<phi>))"
    using nllength_2 assms(2) by simp
  also have "... \<le> 36 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * nlllength (formula_n (relabel \<sigma> \<phi>))"
    by simp
  finally have "?ttt \<le> 36 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * nlllength (formula_n (relabel \<sigma> \<phi>))" .
  then have "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
    using assms tmL4 transforms_monotone by blast
  then show ?thesis
    using assms(2) tpsL4'_eq_tpsL tpsL4 by simp
qed

lemma tmL:
  assumes "ttt = length \<phi> * (38 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * nlllength (formula_n (relabel \<sigma> \<phi>))) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length \<phi>))"
  unfolding tmL_def
proof (tform)
  let ?t = "36 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * nlllength (formula_n (relabel \<sigma> \<phi>))"
  show "\<not> read (tpsL (length \<phi>)) ! j1 \<noteq> \<box>"
  proof -
    have "tpsL (length \<phi>) ! j1 = nlltape' n\<phi> (length n\<phi>)"
      using tpsL_def jk formula_n_def by simp
    then show ?thesis
      using nlltape'_tape_read[of n\<phi> "length n\<phi>"] tapes_at_read'[of j1 "tpsL (length \<phi>)"] tpsL_def jk
      by simp
  qed
  show "read (tpsL t) ! j1 \<noteq> \<box>" if "t < length \<phi>" for t
  proof -
    have "tpsL t ! j1 = nlltape' n\<phi> t"
      using tpsL_def jk by simp
    then show ?thesis
      using that formula_n_def nlltape'_tape_read[of n\<phi> t] tapes_at_read'[of j1 "tpsL t"] tpsL_def jk
      by simp
  qed
  show "length \<phi> * (?t + 2) + 1 \<le> ttt"
    using assms(1) by simp
qed

lemma tmL' [transforms_intros]:
  assumes "ttt = 107 * nlllength n\<phi> ^ 2 * (3 + nllength \<sigma> ^ 2) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length \<phi>))"
proof -
  let ?ttt = "length \<phi> * (38 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * nlllength (formula_n (relabel \<sigma> \<phi>))) + 1"
  have "?ttt \<le> length \<phi> * (38 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * (Suc (nllength \<sigma>) * nlllength n\<phi>)) + 1"
    using nlllength_relabel_variables variables by fastforce
  also have "... \<le> length \<phi> * (38 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * ((3 + nllength \<sigma>) * nlllength n\<phi>)) + 1"
  proof -
    have "Suc (nllength \<sigma>) \<le> 3 + nllength \<sigma>"
      by simp
    then show ?thesis
      using add_le_mono le_refl mult_le_mono by presburger
  qed
  also have "... \<le> length \<phi> * (38 + 65 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2) + 4 * ((3 + nllength \<sigma> ^ 2) * nlllength n\<phi>)) + 1"
    using linear_le_pow by simp
  also have "... = length \<phi> * (38 + 69 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2)) + 1"
    by simp
  also have "... \<le> nlllength n\<phi> * (38 + 69 * nlllength n\<phi> * (3 + (nllength \<sigma>)\<^sup>2)) + 1"
    using length_le_nlllength formula_n_def by (metis add_mono_thms_linordered_semiring(3) length_map mult_le_mono1)
  also have "... = 38 * nlllength n\<phi> + (69 * nlllength n\<phi> ^ 2 * (3 + (nllength \<sigma>)\<^sup>2)) + 1"
    by algebra
  also have "... \<le> 38 * nlllength n\<phi> ^ 2 * (3 + nllength \<sigma> ^ 2) + (69 * nlllength n\<phi> ^ 2 * (3 + (nllength \<sigma>)\<^sup>2)) + 1"
  proof -
    have "nlllength n\<phi> \<le> nlllength n\<phi> ^ 2 * (3 + nllength \<sigma> ^ 2)"
      using linear_le_pow by (metis One_nat_def Suc_leI add_gr_0 mult_le_mono nat_mult_1_right zero_less_numeral)
    then show ?thesis
      by simp
  qed
  also have "... = 107 * nlllength n\<phi> ^ 2 * (3 + nllength \<sigma> ^ 2) + 1"
    by simp
  finally have "?ttt \<le> 107 * nlllength n\<phi> ^ 2 * (3 + nllength \<sigma> ^ 2) + 1" .
  then show ?thesis
    using tmL assms transforms_monotone by blast
qed

definition tps1 :: "tape list" where
  "tps1 \<equiv> tps0
     [j1 := nlltape' n\<phi> (length \<phi>),
      j2 := nlltape (formula_n (relabel \<sigma> \<phi>))]"

lemma tps1_eq_tpsL: "tps1 = tpsL (length \<phi>)"
  using tps1_def tpsL_def jk tps0 relabel_def by simp

definition "tps2 \<equiv> tps0
    [j2 := nlltape (formula_n (relabel \<sigma> \<phi>))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = Suc (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      Suc (Suc (Suc (nlllength n\<phi>)))"
  shows "transforms tm2 (tpsL 0) ttt tps2"
  unfolding tm2_def
proof (tform tps: tps0 tpsL_def tps1_def jk)
  have *: "tpsL (length \<phi>) ! j1 = nlltape' n\<phi> (length \<phi>)"
    using tpsL_def jk by simp
  then show "clean_tape (tpsL (length \<phi>) ! j1)"
    using clean_tape_nllcontents by simp
  have "tpsL (length \<phi>) ! j1 |#=| 1 = nlltape' n\<phi> 0"
    using * by simp
  then show "tps2 = (tpsL (length \<phi>))[j1 := tpsL (length \<phi>) ! j1 |#=| 1]"
    using tps0 jk tps2_def tps1_eq_tpsL tps1_def
    by (metis (no_types, lifting) One_nat_def list_update_id list_update_overwrite list_update_swap_less nlllength_Nil take0)
  show "ttt = 107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2) + 1 +
      (tpsL (length \<phi>) :#: j1 + 2)"
    using assms tpsL_def jk formula_n_def by simp
qed

definition "tps3 \<equiv> tps0
    [j2 := nlltape' (formula_n (relabel \<sigma> \<phi>)) 0]"

lemma tm3:
  assumes "ttt = 7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      nlllength n\<phi> + nlllength (formula_n (relabel \<sigma> \<phi>))"
  shows "transforms tm3 (tpsL 0) ttt tps3"
  unfolding tm3_def
proof (tform tps: assms tps0 tps2_def tps3_def jk)
  show "clean_tape (tps2 ! j2)"
    using tps2_def jk clean_tape_nllcontents by simp
qed

lemma tm3' [transforms_intros]:
  assumes "ttt = 7 + (108 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2))"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  let ?ttt = "7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      nlllength n\<phi> + nlllength (formula_n (relabel \<sigma> \<phi>))"
  have "?ttt \<le> 7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      nlllength n\<phi> + Suc (nllength \<sigma>) * nlllength n\<phi>"
    using variables nlllength_relabel_variables by simp
  also have "... = 7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      (2 + nllength \<sigma>) * nlllength n\<phi>"
    by simp
  also have "... \<le> 7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      (2 + nllength \<sigma> ^ 2) * nlllength n\<phi>"
    using linear_le_pow by simp
  also have "... \<le> 7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) + (3 + nllength \<sigma> ^ 2) * nlllength n\<phi>"
    by (metis add_2_eq_Suc add_Suc_shift add_mono_thms_linordered_semiring(2) le_add2 mult.commute mult_le_mono2 numeral_3_eq_3)
  also have "... \<le> 7 + (107 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2)) +
      (3 + nllength \<sigma> ^ 2) * nlllength n\<phi> ^ 2"
    using linear_le_pow by simp
  also have "... = 7 + (108 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2))"
    by simp
  finally have "?ttt \<le> 7 + (108 * (nlllength n\<phi>)\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2))" .
  then show ?thesis
    using tm3 assms tpsL_eq_tps0 transforms_monotone by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_relabel *)

lemma transforms_tm_relabelI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k :: nat and \<sigma> :: "nat list" and \<phi> :: formula
  assumes "0 < j1" and "j1 < j2" and "j2 + 5 < k" and "length tps = k"
    and "variables \<phi> \<subseteq> {..<length \<sigma>}"
  assumes
    "tps ! j1 = (\<lfloor>formula_n \<phi>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps ! (j2 + 1) = (\<lfloor>\<sigma>\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j2 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j2 + 3) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j2 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j2 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps
    [j2 := nlltape' (formula_n (relabel \<sigma> \<phi>)) 0]"
  assumes "ttt = 7 + (108 * (nlllength (formula_n \<phi>))\<^sup>2 * (3 + (nllength \<sigma>)\<^sup>2))"
  shows "transforms (tm_relabel j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_relabel j1 j2 .
  show ?thesis
    using assms loc.tm3_eq_tm_relabel loc.tm3' loc.tps3_def by simp
qed


section \<open>Listing the head positions of a Turing machine\<close>

text \<open>
The formulas $\chi_t$ used for $\Phi_9$ require the functions $\inputpos$ and
$\prev$, or more precisely the substitutions $\rho_t$ and $\rho'_t$ do.

In this section we build a TM that simulates a two-tape TM $M$ on some input
until it halts. During the simulation it creates two lists: one with the
sequence of head positions on $M$'s input tape and one with the sequence of head
positions on $M$'s output tape. The first list directly provides $\inputpos$;
the second list allows the computation of $\prev$ using the TM @{const tm_prev}.
\<close>


subsection \<open>Simulating and logging head movements\<close>

text \<open>
At the core of the simulation is the following Turing command. It interprets the
tapes $j + 7$ and $j + 8$ as input tape and output tape of a two-tape Turing
machine $M$ and the symbol in the first cell of tape $j + 6$ as the state of
$M$. It then applies the actions of $M$ in this configuration to the tapes $j +
7$ and $j + 8$ and adapts the state on tape $j + 6$ accordingly. On top of that
it writes (``logs'') to tape $j$ the direction in which $M$'s input tape head
has moved and to tape $j + 3$ the direction in which $M$'s work tape head has
moved.

The head movement directions are encoded by the symbols $\Box$,
$\triangleright$, and \textbf{0} for Left, Stay, and Right, respectively.

The command is parameterized by the TM $M$ and its alphabet size $G$ (and as
usual the tape index $j$). The command does nothing if the state on tape $j + 6$
is the halting state or if the symbol read from the simulated tape $j + 7$ or $j
+ 8$ is outside the alphabet $G$.

\null
\<close>

definition direction_to_symbol :: "direction \<Rightarrow> symbol" where
  "direction_to_symbol d \<equiv> (case d of Left \<Rightarrow> \<box> | Stay \<Rightarrow> \<triangleright> | Right \<Rightarrow> \<zero>)"

lemma direction_to_symbol_less: "direction_to_symbol d < 3"
  using direction_to_symbol_def by (cases d) simp_all

definition cmd_simulog :: "nat \<Rightarrow> machine \<Rightarrow> tapeidx \<Rightarrow> command" where
  "cmd_simulog G M j rs \<equiv>
   (1,
    if rs ! (j + 6) \<ge> length M \<or> rs ! (j + 7) \<ge> G \<or> rs ! (j + 8) \<ge> G
    then map (\<lambda>z. (z, Stay)) rs
    else
      map (\<lambda>i. let sas = (M ! (rs ! (j + 6))) [rs ! (j + 7), rs ! (j + 8)] in
          if i = j then (direction_to_symbol (sas [~] 0), Stay)
          else if i = j + 3 then (direction_to_symbol (sas [~] 1), Stay)
          else if i = j + 6 then (fst sas, Stay)
          else if i = j + 7 then sas [!] 0
          else if i = j + 8 then sas [!] 1
          else (rs ! i, Stay))
        [0..<length rs])"

lemma turing_command_cmd_simulog:
  fixes G H :: nat
  assumes "turing_machine 2 G M" and "k \<ge> j + 9" and "j > 0" and "H \<ge> Suc (length M)" and "H \<ge> G"
  shows "turing_command k 1 H (cmd_simulog G M j)"
proof
  show "\<And>gs. length gs = k \<Longrightarrow> length ([!!] cmd_simulog G M j gs) = length gs"
    using cmd_simulog_def by simp
  have G: "H \<ge> 4"
    using assms(1,5) turing_machine_def by simp
  show "cmd_simulog G M j rs [.] i < H"
    if "length rs = k" and "(\<And>i. i < length rs \<Longrightarrow> rs ! i < H)" and "i < length rs"
    for rs i
  proof (cases "rs ! (j + 6) \<ge> length M \<or> rs ! (j + 7) \<ge> G \<or> rs ! (j + 8) \<ge> G")
    case True
    then show ?thesis
      using assms that cmd_simulog_def by simp
  next
    case False
    then have inbounds: "rs ! (j + 6) < length M"
      by simp
    let ?cmd = "M ! (rs ! (j + 6))"
    let ?gs = "[rs ! (j + 7), rs ! (j + 8)]"
    let ?sas = "?cmd ?gs"
    have lensas: "length (snd ?sas) = 2"
      using assms(1) inbounds turing_commandD(1)
      by (metis length_Cons list.size(3) numeral_2_eq_2 turing_machineD(3))
    consider
        "i = j"
      | "i = j + 3"
      | "i = j + 6"
      | "i = j + 7"
      | "i = j + 8"
      | "i \<noteq> j \<and> i \<noteq> j + 3 \<and> i \<noteq> j + 6 \<and> i \<noteq> j + 7 \<and> i \<noteq> j + 8"
      by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "cmd_simulog G M j rs [!] i = (direction_to_symbol (?sas [~] 0), Stay)"
        using cmd_simulog_def False that by simp
      then have "cmd_simulog G M j rs [.] i < 3"
        using direction_to_symbol_less by simp
      then show ?thesis
        using G by simp
    next
      case 2
      then have "cmd_simulog G M j rs [!] i = (direction_to_symbol (?sas [~] 1), Stay)"
        using cmd_simulog_def False that by simp
      then have "cmd_simulog G M j rs [.] i < 3"
        using direction_to_symbol_less by simp
      then show ?thesis
        using G by simp
    next
      case 3
      then have "cmd_simulog G M j rs [!] i = (fst ?sas, Stay)"
        using cmd_simulog_def False that by simp
      then have "cmd_simulog G M j rs [.] i \<le> length M"
        using assms inbounds turing_commandD(4) turing_machineD(3)
        by (metis One_nat_def Suc_1 fst_conv length_Cons list.size(3))
      then show ?thesis
        using assms(4) by simp
    next
      case 4
      then have "cmd_simulog G M j rs [!] i = ?sas [!] 0"
        using cmd_simulog_def False that by simp
      then show ?thesis
        using 4 assms inbounds turing_machine_def that lensas turing_commandD(3)
        by (metis One_nat_def Suc_1 length_Cons list.size(3) nth_Cons_0 nth_mem zero_less_numeral)
    next
      case 5
      then have *: "cmd_simulog G M j rs [!] i = ?sas [!] 1"
        using cmd_simulog_def False that by simp
      have "turing_command 2 (length M) G ?cmd"
        using assms(1) inbounds turing_machine_def by simp
      moreover have "symbols_lt G ?gs"
        using False less_2_cases_iff numeral_2_eq_2 by simp
      ultimately have "?sas [.] 1 < G"
        using turing_commandD(2) by simp
      then show ?thesis
        using assms * by simp
    next
      case 6
      then have "cmd_simulog G M j rs [!] i = (rs ! i, Stay)"
        using cmd_simulog_def False that(3) by simp
      then show ?thesis
        using that by simp
    qed
  qed
  show "cmd_simulog G M j rs [.] 0 = rs ! 0" if "length rs = k" and "0 < k" for rs
  proof (cases "rs ! (j + 6) \<ge> length M \<or> rs ! (j + 7) \<ge> G \<or> rs ! (j + 8) \<ge> G")
    case True
    then show ?thesis
      using assms that cmd_simulog_def by simp
  next
    case False
    then show ?thesis
      using assms that cmd_simulog_def by simp
  qed
  show "\<And>gs. length gs = k \<Longrightarrow> [*] (cmd_simulog G M j gs) \<le> 1"
    using cmd_simulog_def by simp
qed

text \<open>
The logging Turing machine consists only of the logging command.
\<close>

definition tm_simulog :: "nat \<Rightarrow> machine \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_simulog G M j \<equiv> [cmd_simulog G M j]"

lemma tm_simulog_tm:
  fixes H :: nat
  assumes "turing_machine 2 G M" and "k \<ge> j + 9" and "j > 0" and "H \<ge> Suc (length M)" and "H \<ge> G"
  shows "turing_machine k H (tm_simulog G M j)"
  using turing_command_cmd_simulog tm_simulog_def assms turing_machine_def by simp

lemma transforms_tm_simulogI [transforms_intros]:
  fixes G :: nat and M :: machine and j :: tapeidx
  fixes k :: nat and tps tps' :: "tape list" and xs :: "symbol list"
  assumes "turing_machine 2 G M" and "k \<ge> j + 9" and "j > 0"
    and "symbols_lt G xs"
    and "cfg = execute M (start_config 2 xs) t" and "fst cfg < length M"
    and "length tps = k"
  assumes
    "tps ! j = \<lceil>dummy1\<rceil>"
    "tps ! (j + 3) = \<lceil>dummy2\<rceil>"
    "tps ! (j + 6) = \<lceil>fst cfg\<rceil>"
    "tps ! (j + 7) = cfg <!> 0"
    "tps ! (j + 8) = cfg <!> 1"
  assumes "tps' = tps
     [j := \<lceil>direction_to_symbol ((M ! (fst cfg)) (config_read cfg) [~] 0)\<rceil>,
      j + 3 := \<lceil>direction_to_symbol ((M ! (fst cfg)) (config_read cfg) [~] 1)\<rceil>,
      j + 6 := \<lceil>fst (execute M (start_config 2 xs) (Suc t))\<rceil>,
      j + 7 := execute M (start_config 2 xs) (Suc t) <!> 0,
      j + 8 := execute M (start_config 2 xs) (Suc t) <!> 1]"
  shows "transforms (tm_simulog G M j) tps 1 tps'"
proof -
  have "sem (cmd_simulog G M j) (0, tps) = (1, tps')"
  proof (rule semI)
    define H where "H = max G (Suc (length M))"
    then have "H \<ge> Suc (length M)" "H \<ge> G"
      by simp_all
    then show "proper_command k (cmd_simulog G M j)"
      using assms cmd_simulog_def by simp
    show "length tps = k" and "length tps' = k"
      using assms by simp_all
    show "fst (cmd_simulog G M j (read tps)) = 1"
      using cmd_simulog_def sem' by simp

    define rs where "rs = read tps"
    then have lenrs: "length rs = k"
      by (simp add: assms rs_def read_length)
    have rs6: "rs ! (j + 6) = fst cfg"
      using rs_def tapes_at_read'[of "j + 6" tps] assms by simp
    then have inbounds: "rs ! (j + 6) < length M"
      using assms by simp
    have rs7: "rs ! (j + 7) = cfg <.> 0"
      using rs_def tapes_at_read'[of "j + 7" tps] assms by simp
    then have rs7_less: "rs ! (j + 7) < G"
      using assms tape_alphabet[OF assms(1,4)] by simp
    have rs8: "rs ! (j + 8) = cfg <.> 1"
      using rs_def tapes_at_read'[of "j + 8" tps] assms by simp
    then have rs8_less: "rs ! (j + 8) < G"
      using assms tape_alphabet[OF assms(1,4)] by simp
    let ?gs = "[rs ! (j + 7), rs ! (j + 8)]"
    have gs: "?gs = config_read cfg"
    proof (rule nth_equalityI)
      show "length [rs ! (j + 7), rs ! (j + 8)] = length (config_read cfg)"
        using assms execute_num_tapes start_config_length read_length by simp
      then show "[rs ! (j + 7), rs ! (j + 8)] ! i = config_read cfg ! i"
          if "i < length [rs ! (j + 7), rs ! (j + 8)]" for i
        using assms that rs7 rs8 read_length tapes_at_read'
        by (metis One_nat_def length_Cons less_2_cases_iff list.size(3) nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
    qed
    let ?cmd = "M ! (rs ! (j + 6))"
    let ?sas = "?cmd ?gs"
    have lensas: "length (snd ?sas) = 2"
      using assms(1) inbounds turing_commandD(1) turing_machine_def
      by (metis One_nat_def Suc_1 canrepr_1 list.size(4) nlength_1_simp nth_mem plus_1_eq_Suc)
    have sas: "?sas = (M ! (fst cfg)) (config_read cfg)"
      using rs6 gs by simp
    have "act (cmd_simulog G M j rs [!] i) (tps ! i) = tps' ! i" if "i < k" for i
    proof -
      have "cmd_simulog G M j rs =
      (1, map (\<lambda>i. let sas = (M ! (rs ! (j + 6))) [rs ! (j + 7), rs ! (j + 8)] in
              if i = j then (direction_to_symbol (sas [~] 0), Stay)
              else if i = j + 3 then (direction_to_symbol (sas [~] 1), Stay)
              else if i = j + 6 then (fst sas, Stay)
              else if i = j + 7 then sas [!] 0
              else if i = j + 8 then sas [!] 1
              else (rs ! i, Stay))
            [0..<length rs])"
        using inbounds rs7_less rs8_less assms cmd_simulog_def by simp
      then have *: "cmd_simulog G M j rs [!] i =
         (if i = j then (direction_to_symbol (?sas [~] 0), Stay)
          else if i = j + 3 then (direction_to_symbol (?sas [~] 1), Stay)
          else if i = j + 6 then (fst ?sas, Stay)
          else if i = j + 7 then ?sas [!] 0
          else if i = j + 8 then ?sas [!] 1
          else (rs ! i, Stay))"
        using that lenrs by simp
      consider
          "i = j"
        | "i = j + 3"
        | "i = j + 6"
        | "i = j + 7"
        | "i = j + 8"
        | "i \<noteq> j \<and> i \<noteq> j + 3 \<and> i \<noteq> j + 6 \<and> i \<noteq> j + 7 \<and> i \<noteq> j + 8"
        by linarith
      then show ?thesis
      proof (cases)
        case 1
        then have "cmd_simulog G M j rs [!] i = (direction_to_symbol (?sas [~] 0), Stay)"
          using * by simp
        moreover have "tps' ! i = \<lceil>direction_to_symbol (?sas [~] 0)\<rceil>"
          using 1 assms sas by simp
        ultimately show ?thesis
          using 1 act_onesie assms(8) by simp
      next
        case 2
        then have "cmd_simulog G M j rs [!] i = (direction_to_symbol (?sas [~] 1), Stay)"
          using * by simp
        moreover have "tps' ! i = \<lceil>direction_to_symbol (?sas [~] 1)\<rceil>"
          using 2 assms sas by simp
        ultimately show ?thesis
          using 2 act_onesie assms by simp
      next
        case 3
        then have "cmd_simulog G M j rs [!] i = (fst ?sas, Stay)"
          using * by simp
        moreover have "tps' ! i = \<lceil>fst (execute M (start_config 2 xs) (Suc t))\<rceil>"
          using 3 assms by simp
        ultimately show ?thesis
          using 3 act_onesie assms by (metis exe_lt_length execute.simps(2) sas sem_fst)
      next
        case 4
        then have "cmd_simulog G M j rs [!] i = ?sas [!] 0"
          using * by simp
        moreover have "tps' ! i = execute M (start_config 2 xs) (Suc t) <!> 0"
          using 4 assms by simp
        moreover have "proper_command 2 (M ! (rs ! (j + 6)))"
          using assms(1,6) rs6 turing_machine_def turing_commandD(1) turing_machineD by metis
        ultimately show ?thesis
          using 4 assms(1,11,5,6) exe_lt_length gs read_length rs6 sem_snd turing_machine_def
          by (metis execute.simps(2) length_Cons list.size(3) numeral_2_eq_2 zero_less_numeral)
      next
        case 5
        then have "cmd_simulog G M j rs [!] i = ?sas [!] 1"
          using * by simp
        moreover have "tps' ! i = execute M (start_config 2 xs) (Suc t) <!> 1"
          using 5 assms by simp
        moreover have "proper_command 2 (M ! (rs ! (j + 6)))"
          using assms(1,6) rs6 turing_machineD turing_commandD(1) by metis
        ultimately show ?thesis
          using 5 assms(1,12,5,6) exe_lt_length gs read_length rs6 sem_snd turing_machine_def
          by (metis One_nat_def execute.simps(2) length_Cons less_2_cases_iff list.size(3) numeral_2_eq_2)
      next
        case 6
        then have "cmd_simulog G M j rs [!] i = (rs ! i, Stay)"
          using * by simp
        moreover have "tps' ! i = tps ! i"
          using 6 assms(13) by simp
        ultimately show ?thesis
          using 6 assms act_Stay rs_def that by metis
      qed
    qed
    then show "act (cmd_simulog G M j (read tps) [!] i) (tps ! i) = tps' ! i" if "i < k" for i
      using that rs_def by simp
  qed
  moreover have "execute (tm_simulog G M j) (0, tps) 1 = sem (cmd_simulog G M j) (0, tps)"
    using tm_simulog_def by (simp add: exe_lt_length)
  ultimately have "execute (tm_simulog G M j) (0, tps) 1 = (1, tps')"
    by simp
  then show ?thesis
    using transforms_def transits_def tm_simulog_def by auto
qed


subsection \<open>Adjusting head position counters\<close>

text \<open>
The Turing machine @{const tm_simulog} logs the head movements, but what we need
is a list of all the head positions during the execution of $M$. The next TM
maintains a number for a head position and adjusts it based on a head movement
symbol as provided by @{const tm_simulog}.

More precisely, the next Turing machine accepts on tape $j$ a symbol encoding a
direction, on tape $j + 1$ a number representing a head position, and on tape $j
+ 2$ a list of numbers.  Depending on the symbol on tape $j$ it decreases,
increases or leaves unchanged the number on tape $j + 1$. Then it appends this
adjusted number to the list on tape $j + 2$.
\<close>

definition tm_adjust_headpos :: "nat \<Rightarrow> machine" where
  "tm_adjust_headpos j \<equiv>
    IF \<lambda>rs. rs ! j = \<box> THEN
      tm_decr (j + 1)
    ELSE
      IF \<lambda>rs. rs ! j = \<zero> THEN
        tm_incr (j + 1)
      ELSE
        []
      ENDIF
    ENDIF ;;
    tm_append (j + 2) (j + 1)"

lemma tm_adjust_headpos_tm:
  assumes "G \<ge> 5" and "j + 2 < k"
  shows "turing_machine k G (tm_adjust_headpos j)"
  unfolding tm_adjust_headpos_def
  using assms turing_machine_branch_turing_machine tm_decr_tm tm_incr_tm tm_append_tm Nil_tm turing_machine_sequential_turing_machine
  by simp

locale turing_machine_adjust_headpos =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> IF \<lambda>rs. rs ! j = \<zero> THEN tm_incr (j + 1) ELSE [] ENDIF"
definition "tm2 \<equiv> IF \<lambda>rs. rs ! j = \<box> THEN tm_decr (j + 1) ELSE tm1 ENDIF"
definition "tm3 \<equiv> tm2 ;; tm_append (j + 2) (j + 1)"

lemma tm3_eq_tm_adjust_headpos: "tm3 = tm_adjust_headpos j"
  unfolding tm1_def tm2_def tm3_def tm_adjust_headpos_def by simp

context
  fixes tps :: "tape list" and jj :: tapeidx and k t :: nat and xs :: "symbol list"
  fixes M :: machine
  fixes G cfg
  assumes jk: "length tps = k" "k \<ge> j + 3" "jj < 2"
  assumes M: "turing_machine 2 G M"
  assumes xs: "symbols_lt G xs"
  assumes cfg: "cfg = execute M (start_config 2 xs) t" "fst cfg < length M"
  assumes tps0:
    "tps ! j = \<lceil>direction_to_symbol ((M ! (fst cfg)) (config_read cfg) [~] jj)\<rceil>"
    "tps ! (j + 1) = (\<lfloor>cfg <#> jj\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = nltape (map (\<lambda>t. (execute M (start_config 2 xs) t <#> jj)) [0..<Suc t])"
begin

lemma k_ge_2: "2 \<le> k"
  using jk by simp

abbreviation exc :: "symbol list \<Rightarrow> nat \<Rightarrow> config" where
  "exc y tt \<equiv> execute M (start_config 2 y) tt"

lemma read_tps_j: "read tps ! j = direction_to_symbol ((M ! (fst cfg)) (config_read cfg) [~] jj)"
  using tps0 onesie_read jk tapes_at_read'
  by (metis less_add_same_cancel1 less_le_trans zero_less_numeral)

lemma write_symbol:
  "\<exists>v. execute M (start_config 2 xs) (Suc t) <!> jj = act (v, (M ! (fst cfg)) (config_read cfg) [~] jj) (cfg <!> jj)"
proof -
  let ?d = "(M ! (fst cfg)) (config_read cfg) [~] jj"
  obtain v where v: "(M ! (fst cfg)) (config_read cfg) [!] jj = (v, ?d)"
    by (simp add: prod_eq_iff)
  have "execute M (start_config 2 xs) (Suc t) <!> jj = exe M cfg <!> jj"
    using cfg(1) by simp
  also have "... = sem (M ! (fst cfg)) cfg <!> jj"
    by (simp add: cfg(2) exe_lt_length)
  also have "... = act ((M ! (fst cfg)) (config_read cfg) [!] jj) (cfg <!> jj)"
    using sem_snd_tm M cfg execute_num_tapes start_config_length jk
    by (metis (no_types, lifting) numeral_2_eq_2 prod.exhaust_sel zero_less_Suc)
  also have "... = act (v, ?d) (cfg <!> jj)"
    using v by simp
  finally have *: "execute M (start_config 2 xs) (Suc t) <!> jj = act (v, ?d) (cfg <!> jj)" .
  then show ?thesis
    by auto
qed

lemma tm1 [transforms_intros]:
  assumes "ttt = 7 + 2 * nlength (cfg <#> jj)"
    and "(M ! (fst cfg)) (config_read cfg) [~] jj \<noteq> Left"
    and "tps' = tps[j + 1 := (\<lfloor>execute M (start_config 2 xs) (Suc t) <#> jj\<rfloor>\<^sub>N, 1)]"
  shows "transforms tm1 tps ttt tps'"
  unfolding tm1_def
proof (tform)
  let ?d = "(M ! (fst cfg)) (config_read cfg) [~] jj"
  obtain v where v: "execute M (start_config 2 xs) (Suc t) <!> jj = act (v, ?d) (cfg <!> jj)"
    using write_symbol by auto

  { assume "read tps ! j = 2"
    then have "?d = Right"
      using read_tps_j assms(2) direction_to_symbol_def by (cases ?d) simp_all
    show "j + 1 < length tps"
      using jk by simp
    show "tps ! (j + 1) = (\<lfloor>cfg <#> jj\<rfloor>\<^sub>N, 1)"
      using tps0 by simp_all
    show "tps' = tps[j + 1 := (\<lfloor>Suc (cfg <#> jj)\<rfloor>\<^sub>N, 1)]"
    proof -
      have "execute M (start_config 2 xs) (Suc t) <!> jj = cfg <!> jj |:=| v |+| 1"
        using v `?d = Right` act_Right' by simp
      then have "execute M (start_config 2 xs) (Suc t) <#> jj = cfg <#> jj + 1"
        by simp
      then show ?thesis
        using assms(3) by simp
    qed
  }
  { assume "read tps ! j \<noteq> 2"
    then have "?d = Stay"
      using read_tps_j assms(2) direction_to_symbol_def by (cases ?d) simp_all
    then have "execute M (start_config 2 xs) (Suc t) <!> jj = cfg <!> jj |:=| v"
      using v act_Stay' by simp
    then have "execute M (start_config 2 xs) (Suc t) <#> jj = cfg <#> jj"
      by simp
    then show "tps' = tps"
      using assms(3) tps0 by (metis list_update_id)
  }
  show "(5 + 2 * nlength (cfg <#> jj)) + 2 \<le> ttt" "0 + 1 \<le> ttt"
    using assms(1) by simp_all
qed

lemma tm2 [transforms_intros]:
  assumes "ttt = 10 + 2 * nlength (cfg <#> jj)"
    and "tps' = tps[j + 1 := (\<lfloor>execute M (start_config 2 xs) (Suc t) <#> jj\<rfloor>\<^sub>N, 1)]"
  shows "transforms tm2 tps ttt tps'"
  unfolding tm2_def
proof (tform tps: k_ge_2 jk assms)
  let ?d = "(M ! (fst cfg)) (config_read cfg) [~] jj"
  show "8 + 2 * nlength (cfg <#> jj) + 2 \<le> ttt"
    using assms(1) by simp
  show "read tps ! j \<noteq> \<box> \<Longrightarrow> ?d \<noteq> Left"
    using read_tps_j direction_to_symbol_def by (cases ?d) simp_all
  { assume 0: "read tps ! j = \<box>"
    show "tps ! (j + 1) = (\<lfloor>cfg <#> jj\<rfloor>\<^sub>N, 1)"
      using tps0 by simp
    show "tps' = tps[j + 1 := (\<lfloor>cfg <#> jj - 1\<rfloor>\<^sub>N, 1)]"
    proof -
      let ?d = "(M ! (fst cfg)) (config_read cfg) [~] jj"
      obtain v where v: "execute M (start_config 2 xs) (Suc t) <!> jj = act (v, ?d) (cfg <!> jj)"
        using write_symbol by auto
      then have "?d = Left"
        using 0 read_tps_j assms(2) direction_to_symbol_def by (cases ?d) simp_all
      then have "execute M (start_config 2 xs) (Suc t) <!> jj = cfg <!> jj |:=| v |-| 1"
        using v act_Left' by simp
      then have "execute M (start_config 2 xs) (Suc t) <#> jj = cfg <#> jj - 1"
        by simp
      then show ?thesis
        using assms(2) by simp
    qed
  }
qed

lemma tm3:
  assumes "ttt = 16 + 2 * nlength (cfg <#> jj) + 2 * nlength (exc xs (Suc t) <#> jj)"
    and "tps' = tps
      [j + 1 := (\<lfloor>execute M (start_config 2 xs) (Suc t) <#> jj\<rfloor>\<^sub>N, 1),
       j + 2 := nltape (map (\<lambda>t. (execute M (start_config 2 xs) t <#> jj)) [0..<Suc (Suc t)])]"
  shows "transforms tm3 tps ttt tps'"
  unfolding tm3_def
proof (tform tps: jk assms)
  let ?ns = "(map (\<lambda>t. (execute M (start_config 2 xs) t <#> jj)) [0..<Suc t])"
  let ?i = "Suc (nllength (map (\<lambda>t. (execute M (start_config 2 xs) t <#> jj)) [0..<Suc t]))"
  let ?n = "exc xs (Suc t) <#> jj"
  let ?tps = "tps[j + 1 := (\<lfloor>exc xs (Suc t) <#> jj\<rfloor>\<^sub>N, 1)]"
  show "?tps ! (j + 2) = (\<lfloor>?ns\<rfloor>\<^sub>N\<^sub>L, ?i)"
    using tps0 by simp
  show "Suc (nllength ?ns) \<le> ?i"
    by simp
  show "tps' = tps
    [j + 1 := (\<lfloor>?n\<rfloor>\<^sub>N, 1),
     j + 2 := nltape (?ns @ [snd (exe M (exc xs t)) :#: jj])]"
    using assms(2) nlcontents_def nllength_def by simp
  show "ttt =
      10 + 2 * nlength (cfg <#> jj) +
      (7 + nllength (map (\<lambda>t. exc xs t <#> jj) [0..<Suc t]) -
       Suc (nllength (map (\<lambda>t. exc xs t <#> jj) [0..<Suc t])) +
       2 * nlength (snd (exe M (exc xs t)) :#: jj))"
    using assms(1) by simp
qed

end  (* context tps k *)

end  (* locale turing_machine_adjust_headpos *)

lemma transforms_tm_adjust_headposI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and k jj t :: nat and xs :: "symbol list"
    and M :: machine and G :: nat and cfg :: config
  assumes "turing_machine 2 G M"
    and "length tps = k" and "k \<ge> j + 3" and "jj < 2"
    and "symbols_lt G xs"
    and cfg: "cfg = execute M (start_config 2 xs) t" "fst cfg < length M"
  assumes
    "tps ! j = \<lceil>direction_to_symbol ((M ! (fst cfg)) (config_read cfg) [~] jj)\<rceil>"
    "tps ! (j + 1) = (\<lfloor>cfg <#> jj\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = nltape (map (\<lambda>t. (execute M (start_config 2 xs) t <#> jj)) [0..<Suc t])"
  assumes max_head_pos: "\<forall>t. execute M (start_config 2 xs) t <#> jj \<le> max_head_pos"
  assumes ttt: "ttt = 16 + 4 * nlength max_head_pos"
  assumes "tps' = tps
    [j + 1 := (\<lfloor>execute M (start_config 2 xs) (Suc t) <#> jj\<rfloor>\<^sub>N, 1),
     j + 2 := nltape (map (\<lambda>t. (execute M (start_config 2 xs) t <#> jj)) [0..<Suc (Suc t)])]"
  shows "transforms (tm_adjust_headpos j) tps ttt tps'"
proof -
  interpret loc: turing_machine_adjust_headpos j .
  let ?ttt = "16 + 2 * nlength (cfg <#> jj) + 2 * nlength (execute M (start_config 2 xs) (Suc t) <#> jj)"
  have "transforms (tm_adjust_headpos j) tps ?ttt tps'"
    using assms loc.tm3_eq_tm_adjust_headpos loc.tm3 by simp
  moreover have "?ttt \<le> ttt"
  proof -
    have "?ttt \<le> 16 + 2 * nlength (cfg <#> jj) + 2 * nlength max_head_pos"
      using max_head_pos nlength_mono by (meson add_le_mono le_refl mult_le_mono2)
    also have "... \<le> 16 + 2 * nlength max_head_pos + 2 * nlength max_head_pos"
      using max_head_pos cfg nlength_mono by simp
    also have "... = 16 + 4 * nlength max_head_pos"
      by simp
    finally show ?thesis
      using ttt by simp
  qed
  ultimately show ?thesis
    using transforms_monotone by simp
qed


subsection \<open>Listing the head positions\<close>

text \<open>
The next Turing machine is essentially a loop around the TM @{const tm_simulog}, which
outputs head movements, combined with two instances of the TM @{const
tm_adjust_headpos}, each of which maintains a head positions lists. The loop
ends when the simulated machine reaches the halting state.  If the simulated
machine does not halt, neither does the simulator, but we will not consider this
case when we analyze the semantics. The TM receives an input on tape $j + 7$.
During the simulation of $M$ this tape is a replica of the simulated machine's
input tape, and tape $j + 8$ is a replica of the work/output tape. The lists of
the head positions will be on tapes $j + 2$ and $j + 5$ for the input tape and
work/output tape, respectively.
\<close>

definition tm_list_headpos :: "nat \<Rightarrow> machine \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_list_headpos G M j \<equiv>
    tm_right_many {j + 1, j + 2, j + 4, j+ 5} ;;
    tm_write (j + 6) \<box> ;;
    tm_append (j + 2) (j + 1) ;;
    tm_append (j + 5) (j + 4) ;;
    WHILE [] ; \<lambda>rs. rs ! (j + 6) < length M DO
      tm_simulog G M j ;;
      tm_adjust_headpos j ;;
      tm_adjust_headpos (j + 3) ;;
      tm_write_many {j, j + 3} \<triangleright>
    DONE ;;
    tm_write (j + 6) \<triangleright> ;;
    tm_cr (j + 2) ;;
    tm_cr (j + 5)"

lemma tm_list_headpos_tm:
  fixes H :: nat
  assumes "turing_machine 2 G M" and "k \<ge> j + 9" and "j > 0" and "H \<ge> Suc (length M)" and "H \<ge> G"
  assumes "H \<ge> 5"
  shows "turing_machine k H (tm_list_headpos G M j)"
  unfolding tm_list_headpos_def
  using assms turing_machine_loop_turing_machine turing_machine_sequential_turing_machine Nil_tm
    tm_append_tm tm_simulog_tm tm_adjust_headpos_tm tm_right_many_tm tm_write_tm tm_write_many_tm tm_cr_tm
  by simp

locale turing_machine_list_headpos =
  fixes G :: nat and M :: machine and j :: tapeidx
begin

definition "tm1 \<equiv> tm_right_many {j + 1, j + 2, j + 4, j + 5}"
definition "tm2 \<equiv> tm1 ;; tm_write (j + 6) \<box>"
definition "tm3 \<equiv> tm2 ;; tm_append (j + 2) (j + 1)"
definition "tm4 \<equiv> tm3 ;; tm_append (j + 5) (j + 4)"
definition "tmL1 \<equiv> tm_simulog G M j"
definition "tmL2 \<equiv> tmL1 ;; tm_adjust_headpos j"
definition "tmL3 \<equiv> tmL2 ;; tm_adjust_headpos (j + 3)"
definition "tmL4 \<equiv> tmL3 ;; tm_write_many {j, j + 3} \<triangleright>"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! (j + 6) < length M DO tmL4 DONE"
definition "tm5 \<equiv> tm4 ;; tmL"
definition "tm6 \<equiv> tm5 ;; tm_write (j + 6) \<triangleright>"
definition "tm7 \<equiv> tm6 ;; tm_cr (j + 2)"
definition "tm8 \<equiv> tm7 ;; tm_cr (j + 5)"

lemma tm8_eq_tm_list_headpos: "tm8 = tm_list_headpos G M j"
  unfolding tm1_def tm2_def tm3_def tm4_def tmL1_def tmL2_def tmL3_def tmL4_def tmL_def tm5_def tm6_def tm7_def tm8_def
    tm_list_headpos_def
  by simp

context
  fixes tps0 :: "tape list"
  fixes thalt k :: nat and xs :: "symbol list"
  assumes M: "turing_machine 2 G M"
  assumes jk: "k \<ge> j + 9" "j > 0" "length tps0 = k"
  assumes thalt:
    "\<forall>t<thalt. fst (execute M (start_config 2 xs) t) < length M"
    "fst (execute M (start_config 2 xs) thalt) = length M"
  assumes xs: "symbols_lt G xs"
  assumes tps0:
    "tps0 ! j = \<lceil>\<triangleright>\<rceil>"
    "tps0 ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 0)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 0)"
    "tps0 ! (j + 3) = \<lceil>\<triangleright>\<rceil>"
    "tps0 ! (j + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 0)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 0)"
    "tps0 ! (j + 6) = \<lceil>\<triangleright>\<rceil>"
    "tps0 ! (j + 7) = (\<lfloor>xs\<rfloor>, 0)"
    "tps0 ! (j + 8) = (\<lfloor>[]\<rfloor>, 0)"
begin

abbreviation exec :: "nat \<Rightarrow> config" where
  "exec t \<equiv> execute M (start_config 2 xs) t"

lemma max_head_pos_0: "\<forall>t. exec t <#> 0 \<le> thalt"
  using thalt M head_pos_le_halting_time by simp

lemma max_head_pos_1: "\<forall>t. exec t <#> 1 \<le> thalt"
  using thalt M head_pos_le_halting_time by simp

definition "tps1 \<equiv> tps0
  [(j + 1) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 2) := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 4) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 5) := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 6) := \<lceil>\<triangleright>\<rceil>]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 1"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: assms tps0 jk tps1_def)
  show "tps1 = map (\<lambda>i. if i \<in> {j + 1, j + 2, j + 4, j + 5} then tps0 ! i |+| 1
                        else tps0 ! i) [0..<length tps0]"
     (is "tps1 = ?rhs")
  proof (rule nth_equalityI)
    show len: "length tps1 = length ?rhs"
      by (simp add: tps1_def)
    let ?J = "{j + 1, j + 2, j + 4, j + 5}"
    show "tps1 ! i = ?rhs ! i" if "i < length tps1" for i
    proof (cases "i \<in> ?J")
      case True
      have "tps1 ! (j + 1) = ?rhs ! (j + 1)"
        using tps1_def jk tps0 by fastforce
      moreover have "tps1 ! (j + 2) = ?rhs ! (j + 2)"
        using tps1_def jk tps0 by fastforce
      moreover have "tps1 ! (j + 4) = ?rhs ! (j + 4)"
        using tps1_def jk tps0 by fastforce
      moreover have "tps1 ! (j + 5) = ?rhs ! (j + 5)"
        using tps1_def jk tps0 by fastforce
      ultimately show ?thesis
        using True by fast
    next
      case notinJ: False
      then have *: "?rhs ! i = tps0 ! i"
        using that len by simp
      show ?thesis
      proof (cases "i = j + 6")
        case True
        then show ?thesis
          using * that tps0(7) tps1_def by simp
      next
        case False
        then have "tps1 ! i = tps0 ! i"
          using tps1_def notinJ that by simp
        then show ?thesis
          using * by simp
      qed
    qed
  qed
qed

definition "tps2 \<equiv> tps0
  [(j + 1) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 2) := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 4) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 5) := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 6) := \<lceil>\<box>\<rceil>]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: assms tps0 jk tps2_def tps1_def)
  show "tps2 = tps1[j + 6 := tps1 ! (j + 6) |:=| 0]"
    using tps2_def tps1_def jk onesie_write
    by (smt (z3) list_update_beyond list_update_overwrite nth_list_update_eq verit_comp_simplify1(3))
qed

definition "tps3 \<equiv> tps0
  [(j + 1) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 2) := nltape [0],
   (j + 4) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 5) := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 6) := \<lceil>\<box>\<rceil>]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 8"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps0 jk tps2_def tps3_def)
  show "tps3 = tps2[j + 2 := nltape ([] @ [0])]"
    using tps3_def jk tps2_def
    by (smt (verit, ccfv_SIG) Suc3_eq_add_3 add_2_eq_Suc add_less_cancel_left lessI list_update_overwrite
      list_update_swap not_add_less2 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 numeral_plus_numeral
      self_append_conv2 semiring_norm(4) semiring_norm(5))
  show "ttt = 2 + (7 + nllength [] - Suc 0 + 2 * nlength 0)"
    using assms by simp
qed

definition "tps4 \<equiv> tps0
  [(j + 1) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 2) := nltape [0],
   (j + 4) := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   (j + 5) := nltape [0],
   (j + 6) := \<lceil>\<box>\<rceil>]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 14"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def jk tps0 tps4_def)
  show "tps4 = tps3[j + 5 := nltape ([] @ [0])]"
    unfolding tps3_def tps4_def
    using jk tps0
    by (smt (z3) add_left_imp_eq list_update_overwrite list_update_swap num.simps(8) numeral_eq_iff self_append_conv2)
  show "ttt = 8 + (7 + nllength [] - Suc 0 + 2 * nlength 0)"
    using assms by simp
qed

text \<open>The tapes after $t$ iterations:\<close>

definition "tpsL t \<equiv> tps0
  [(j + 1) := (\<lfloor>exec t <#> 0\<rfloor>\<^sub>N, 1),
   (j + 2) := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc t]),
   (j + 4) := (\<lfloor>exec t <#> 1\<rfloor>\<^sub>N, 1),
   (j + 5) := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc t]),
   (j + 6) := \<lceil>fst (exec t)\<rceil>,
   (j + 7) := exec t <!> 0,
   (j + 8) := exec t <!> 1]"

lemma lentpsL: "length (tpsL t) = k"
  using jk tpsL_def by simp

lemma tpsL_0_eq_tps4: "tpsL 0 = tps4"
proof -
  have *: "exec 0 = (0, [(\<lfloor>xs\<rfloor>, 0), (\<lfloor>[]\<rfloor>, 0)])"
    using start_config_def contents_def by auto
  show ?thesis
    (is "tpsL 0 = ?rhs")
  proof (rule nth_equalityI)
    show "length (tpsL 0) = length ?rhs"
      by (simp add: tps4_def tpsL_def)
    show "tpsL 0 ! i = ?rhs ! i" if "i < length (tpsL 0)" for i
    proof -
      show ?thesis
      proof (cases "i = j \<or> i = j + 1 \<or> i = j + 2 \<or> i = j + 4 \<or> i = j + 5 \<or> i = j + 6 \<or> i = j + 7 \<or> i = j + 8")
        case True
        then show ?thesis
          unfolding tps4_def tpsL_def using * tps0 jk by auto
      next
        case False
        then show ?thesis
          unfolding tps4_def tpsL_def using * tps0 jk that by (smt (z3) nth_list_update_neq)
      qed
    qed
  qed
qed

definition "tpsL1 t \<equiv> tps0
  [j := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 0)\<rceil>,
   j + 1 := (\<lfloor>exec t <#> 0\<rfloor>\<^sub>N, 1),
   j + 2 := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc t]),
   j + 3 := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 1)\<rceil>,
   j + 4 := (\<lfloor>exec t <#> 1\<rfloor>\<^sub>N, 1),
   j + 5 := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc t]),
   j + 6 := \<lceil>fst (exec (Suc t))\<rceil>,
   j + 7 := exec (Suc t) <!> 0,
   j + 8 := exec (Suc t) <!> 1]"

lemma lentpsL1: "length (tpsL1 t) = k"
    using jk tpsL1_def by (simp only: length_list_update)

lemma tmL1 [transforms_intros]:
  assumes "fst (exec t) < length M"
  shows "transforms tmL1 (tpsL t) 1 (tpsL1 t)"
  unfolding tmL1_def
proof (tform tps: M xs jk assms)
  show "j + 9 \<le> length (tpsL t)"
    using tpsL_def jk by (simp only: length_list_update)
  show "tpsL t ! j = \<lceil>\<triangleright>\<rceil>"
    using tpsL_def tps0 by (simp only: nth_list_update_eq nth_list_update_neq)
  show "tpsL t ! (j + 3) = \<lceil>\<triangleright>\<rceil>"
    using tpsL_def tps0 by (simp only: nth_list_update_eq nth_list_update_neq)
  show "tpsL t ! (j + 6) = \<lceil>fst (exec t)\<rceil>"
    using tpsL_def tps0 jk by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tpsL t ! (j + 7) = exec t <!> 0"
    using tpsL_def tps0 jk by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show " tpsL t ! (j + 8) = exec t <!> 1"
    using tpsL_def tps0 jk by (simp only: length_list_update nth_list_update_eq nth_list_update_neq One_nat_def)
  show "tpsL1 t = (tpsL t)
    [j := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 0)\<rceil>,
     j + 3 := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 1)\<rceil>,
     j + 6 := \<lceil>fst (exec (Suc t))\<rceil>,
     j + 7 := exec (Suc t) <!> 0,
     j + 8 := exec (Suc t) <!> 1]"
    unfolding tpsL1_def tpsL_def
    by (simp only: list_update_overwrite list_update_swap_less[of "j+7"] list_update_swap_less[of "j+6"]
      list_update_swap_less[of "j+3"] list_update_swap_less[of "j"])
qed

definition "tpsL2 t \<equiv> tps0
  [j := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 0)\<rceil>,
   j + 1 := (\<lfloor>exec (Suc t) <#> 0\<rfloor>\<^sub>N, 1),
   j + 2 := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc (Suc t)]),
   j + 3 := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 1)\<rceil>,
   j + 4 := (\<lfloor>exec t <#> 1\<rfloor>\<^sub>N, 1),
   j + 5 := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc t]),
   j + 6 := \<lceil>fst (exec (Suc t))\<rceil>,
   j + 7 := exec (Suc t) <!> 0,
   j + 8 := exec (Suc t) <!> 1]"

lemma lentpsL2: "length (tpsL2 t) = k"
    using jk tpsL2_def by (simp only: length_list_update)

lemma tmL2 [transforms_intros]:
  assumes "fst (exec t) < length M"
    and "ttt = 17 + 4 * nlength thalt"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def
proof (tform tps: M xs jk assms(1))
  show "\<forall>t. exec t <#> 0 \<le> thalt"
    using max_head_pos_0 by simp
  show "j + 3 \<le> length (tpsL1 t)"
    using lentpsL1 jk by simp
  show "(0 :: nat) < 2"
    by simp
  show "tpsL1 t ! j = \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 0)\<rceil>"
    using tpsL1_def jk lentpsL1 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tpsL1 t ! (j + 1) = (\<lfloor>exec t <#> 0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def jk by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tpsL1 t ! (j + 2) = nltape (map (\<lambda>t. snd (exec t) :#: 0) [0..<Suc t])"
    using tpsL1_def jk lentpsL1 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  show "tpsL2 t = (tpsL1 t)
      [j + 1 := (\<lfloor>exec (Suc t) <#> 0\<rfloor>\<^sub>N, 1),
       j + 2 := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc (Suc t)])]"
    unfolding tpsL1_def tpsL2_def
    by (simp only: list_update_overwrite list_update_swap_less[of "j+1"] list_update_swap_less[of "j+2"])
  show "ttt = 1 + (16 + 4 * nlength thalt)"
    using assms(2) by simp
qed

definition "tpsL3 t \<equiv> tps0
  [j := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 0)\<rceil>,
   j + 1 := (\<lfloor>exec (Suc t) <#> 0\<rfloor>\<^sub>N, 1),
   j + 2 := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc (Suc t)]),
   j + 3 := \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 1)\<rceil>,
   j + 4 := (\<lfloor>exec (Suc t) <#> 1\<rfloor>\<^sub>N, 1),
   j + 5 := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc (Suc t)]),
   j + 6 := \<lceil>fst (exec (Suc t))\<rceil>,
   j + 7 := exec (Suc t) <!> 0,
   j + 8 := exec (Suc t) <!> 1]"

lemma lentpsL3: "length (tpsL3 t) = k"
  using jk tpsL3_def by (simp only: length_list_update)

lemma tmL3 [transforms_intros]:
  assumes "fst (exec t) < length M" and "ttt = 33 + 8 * nlength thalt"
  shows "transforms tmL3 (tpsL t) ttt (tpsL3 t)"
  unfolding tmL3_def
proof (tform tps: M jk assms(1))
  show "\<forall>t. exec t <#> 1 \<le> thalt"
    using max_head_pos_1 .
  show "j + 3 + 3 \<le> length (tpsL2 t)"
    using tpsL2_def jk by (simp only: length_list_update)
  show "symbols_lt G xs"
    using xs .
  show "(1 :: nat) < 2"
    by simp
  show "tpsL2 t ! (j + 3) = \<lceil>direction_to_symbol ((M ! fst (exec t)) (config_read (exec t)) [~] 1)\<rceil>"
    using tpsL2_def jk lentpsL2 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "j + 3 + 1 = j + 4"
    by simp
  then show "tpsL2 t ! (j + 3 + 1) = (\<lfloor>exec t <#> 1\<rfloor>\<^sub>N, 1)"
    using tpsL2_def jk by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "j + 3 + 2 = j + 5"
    by simp
  then show "tpsL2 t ! (j + 3 + 2) = nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc t])"
    using tpsL2_def jk lentpsL2 by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  have "tpsL3 t = (tpsL2 t)
      [j + 4 := (\<lfloor>snd (exec (Suc t)) :#: 1\<rfloor>\<^sub>N, 1),
       j + 5 := nltape (map (\<lambda>t. snd (exec t) :#: 1) [0..<Suc (Suc t)])]"
    unfolding tpsL2_def tpsL3_def
    by (simp only: list_update_overwrite list_update_swap_less[of "j+4"] list_update_swap_less[of "j+5"])
  moreover have "j + 3 + 1 = j + 4" "j + 3 + 2 = j + 5"
    by simp_all
  ultimately show "tpsL3 t = (tpsL2 t)
      [j + 3 + 1 := (\<lfloor>snd (exec (Suc t)) :#: 1\<rfloor>\<^sub>N, 1),
       j + 3 + 2 := nltape (map (\<lambda>t. snd (exec t) :#: 1) [0..<Suc (Suc t)])]"
    by metis
  show "ttt = 17 + 4 * nlength thalt + (16 + 4 * nlength thalt)"
    using assms(2) by simp
qed

definition "tpsL4 t \<equiv> tps0
  [j + 1 := (\<lfloor>exec (Suc t) <#> 0\<rfloor>\<^sub>N, 1),
   j + 2 := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc (Suc t)]),
   j + 4 := (\<lfloor>exec (Suc t) <#> 1\<rfloor>\<^sub>N, 1),
   j + 5 := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc (Suc t)]),
   j + 6 := \<lceil>fst (exec (Suc t))\<rceil>,
   j + 7 := exec (Suc t) <!> 0,
   j + 8 := exec (Suc t) <!> 1]"

lemma lentpsL4: "length (tpsL4 t) = k"
  using jk tpsL4_def by (simp only: length_list_update)

lemma tmL4:
  assumes "fst (exec t) < length M"
    and "ttt = 34 + 8 * nlength thalt"
  shows "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
  unfolding tmL4_def
proof (tform tps: jk assms(1) lentpsL3 lentpsL4 time: assms)
  have "tpsL4 t ! i = tpsL3 t ! i |:=| Suc 0" if "i = j \<or> i = j + 3 " for i
  proof (cases "i = j")
    case True
    then show ?thesis
      using tpsL3_def tpsL4_def jk lentpsL4 onesie_write tps0
      by (simp only: length_list_update nth_list_update_eq nth_list_update_neq One_nat_def)
  next
    case False
    then have "i = j + 3"
      using that by simp
    then show ?thesis
      using tpsL3_def tpsL4_def jk lentpsL4 onesie_write tps0
      by (simp only: length_list_update nth_list_update_eq nth_list_update_neq One_nat_def)
  qed
  then show "\<And>ja. ja \<in> {j, j + 3} \<Longrightarrow> tpsL4 t ! ja = tpsL3 t ! ja |:=| 1"
    by simp
  have "tpsL4 t ! i = tpsL3 t ! i" if "i < length (tpsL4 t)" and "i \<noteq> j \<and> i \<noteq> j + 3" for i
  proof -
    consider
        "i = j" | "i = j + 1" | "i = j + 2" | "i = j + 3" | "i = j + 4" | "i = j + 5" | "i = j + 6" | "i = j + 7" | "i = j + 8"
      | "i < j" | "i > j + 8"
      by linarith
    then show ?thesis
      using tpsL3_def tpsL4_def that
      by (cases) (auto simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  qed
  then show "\<And>ja. ja < length (tpsL4 t) \<Longrightarrow> ja \<notin> {j, j + 3} \<Longrightarrow> tpsL4 t ! ja = tpsL3 t ! ja"
    by simp
qed

lemma tpsL4_Suc: "tpsL4 t = tpsL (Suc t)" (is "?l = ?r")
proof (rule nth_equalityI)
  show "length ?l = length ?r"
    using lentpsL4 tpsL_def jk by simp
  show "?l ! i = ?r ! i" if "i < length ?l" for i
  proof -
    consider
        "i = j" | "i = j + 1" | "i = j + 2" | "i = j + 3" | "i = j + 4" | "i = j + 5" | "i = j + 6" | "i = j + 7" | "i = j + 8"
      | "i < j" | "i > j + 8"
      by linarith
    then show ?thesis
      using tpsL4_def tpsL_def
      by (cases) (simp_all only: length_list_update nth_list_update_eq nth_list_update_neq)
  qed
qed

lemma tmL4':
  assumes "fst (exec t) < length M"
    and "ttt = 34 + 8 * nlength thalt"
  shows "transforms tmL4 (tpsL t) ttt (tpsL (Suc t))"
  using tpsL4_Suc tmL4 assms by simp

lemma tmL:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL thalt)"
  unfolding tmL_def
proof (tform)
  have "tpsL t ! (j + 6) = \<lceil>fst (exec t)\<rceil>" for t
    using tpsL_def jk by (simp only: length_list_update nth_list_update_eq nth_list_update_neq)
  moreover have "j + 6 < length (tpsL t)"
    using jk tpsL_def by simp
  ultimately have *: "read (tpsL t) ! (j + 6) = fst (exec t)" for t
    using tapes_at_read'[of "j + 6" "tpsL t"] onesie_read[of "fst (exec t)"]
    by (simp add: lentpsL)
  show "\<And>t. t < thalt \<Longrightarrow> read (tpsL t) ! (j + 6) < length M"
    using * thalt by simp
  show "\<And>t. t < thalt \<Longrightarrow> transforms tmL4 (tpsL t) (34 + 8 * nlength thalt) (tpsL (Suc t))"
    using tmL4' * thalt(1) by simp
  show "\<not> read (tpsL thalt) ! (j + 6) < length M"
    using * thalt(2) by simp
  show "thalt * tosym (34 + 8 * nlength thalt) + 1 \<le> ttt"
    using assms by simp
qed

lemma tmL' [transforms_intros]:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 1"
  shows "transforms tmL tps4 ttt (tpsL thalt)"
  using assms tmL tpsL_0_eq_tps4 by simp

definition "tps5 \<equiv> tps0
  [(j + 1) := (\<lfloor>exec thalt <#> 0\<rfloor>\<^sub>N, 1),
   (j + 2) := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]),
   (j + 4) := (\<lfloor>exec thalt <#> 1\<rfloor>\<^sub>N, 1),
   (j + 5) := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]),
   (j + 6) := \<lceil>fst (exec thalt)\<rceil>,
   (j + 7) := exec thalt <!> 0,
   (j + 8) := exec thalt <!> 1]"

lemma tm5:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 15"
  shows "transforms tm5 tps0 ttt (tpsL thalt)"
  unfolding tm5_def by (tform tps: jk time: assms)

lemma tm5' [transforms_intros]:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 15"
  shows "transforms tm5 tps0 ttt tps5"
  using assms tm5 tps5_def tpsL_def by simp

definition "tps6 \<equiv> tps0
  [(j + 1) := (\<lfloor>exec thalt <#> 0\<rfloor>\<^sub>N, 1),
   (j + 2) := nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]),
   (j + 4) := (\<lfloor>exec thalt <#> 1\<rfloor>\<^sub>N, 1),
   (j + 5) := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]),
   (j + 7) := exec thalt <!> 0,
   (j + 8) := exec thalt <!> 1]"

lemma tm6 [transforms_intros]:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 16"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: jk time: assms)
  show "tps6 = tps5[j + 6 := tps5 ! (j + 6) |:=| 1]"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using tps5_def tps6_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      have i_less: "i < length ?r"
        using that len by simp
      consider
          "i = j" | "i = j + 1" | "i = j + 2" | "i = j + 3" | "i = j + 4" | "i = j + 5" | "i = j + 6" | "i = j + 7" | "i = j + 8"
        | "i < j" | "i > j + 8"
        by linarith
      then show ?thesis
        using i_less tps5_def tps6_def onesie_write tps0
        by (cases) (simp_all only: length_list_update nth_list_update_eq nth_list_update_neq)
    qed
  qed
qed

definition "tps7 \<equiv> tps0
  [(j + 1) := (\<lfloor>exec thalt <#> 0\<rfloor>\<^sub>N, 1),
   (j + 2) := (\<lfloor>map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 4) := (\<lfloor>exec thalt <#> 1\<rfloor>\<^sub>N, 1),
   (j + 5) := nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]),
   (j + 7) := exec thalt <!> 0,
   (j + 8) := exec thalt <!> 1]"

lemma tm7 [transforms_intros]:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 19 + nllength (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt])"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def
proof (tform tps: tps7_def tps6_def jk assms)
  show "clean_tape (tps6 ! (j + 2))"
    using jk tps6_def clean_tape_nlcontents by simp
  have "tps6 ! (j + 2) = nltape (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt])"
    using jk tps6_def by simp
  then have "tps6 ! (j + 2) |#=| 1 = (\<lfloor>map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1)" (is "_ = ?tp")
    by simp
  moreover have "tps7 = tps6[j + 2 := ?tp]"
    unfolding tps7_def tps6_def by (simp add: list_update_swap)
  ultimately show "tps7 = tps6[j + 2 := tps6 ! (j + 2) |#=| 1]"
    by simp
qed

definition "tps8 \<equiv> tps0
  [(j + 1) := (\<lfloor>exec thalt <#> 0\<rfloor>\<^sub>N, 1),
   (j + 2) := (\<lfloor>map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 4) := (\<lfloor>exec thalt <#> 1\<rfloor>\<^sub>N, 1),
   (j + 5) := (\<lfloor>map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
   (j + 7) := exec thalt <!> 0,
   (j + 8) := exec thalt <!> 1]"

lemma tm8:
  assumes "ttt = thalt * (36 + 8 * nlength thalt) + 22 + nllength (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]) +
    nllength (map (\<lambda>t. (exec t) <#> 1) [0..<Suc thalt])"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def
proof (tform tps: tps8_def tps7_def jk assms)
  show "clean_tape (tps7 ! (j + 5))"
    using jk tps7_def clean_tape_nlcontents by simp
  have "tps7 ! (j + 5) = nltape (map (\<lambda>t. exec t <#> 1) [0..<Suc thalt])"
    using jk tps7_def by simp
  then have "tps7 ! (j + 5) |#=| 1 = (\<lfloor>map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1)" (is "_ = ?tp")
    by simp
  moreover have "tps8 = tps7[j + 5 := ?tp]"
    unfolding tps8_def tps7_def by (simp add: list_update_swap)
  ultimately show "tps8 = tps7[j + 5 := tps7 ! (j + 5) |#=| 1]"
    by simp
qed

lemma tm8':
  assumes "ttt = 27 * Suc thalt * (9 + 2 * nlength thalt)"
  shows "transforms tm8 tps0 ttt tps8"
proof -
  have 0: "nllength (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]) \<le> Suc (nlength thalt) * Suc thalt"
    using nllength_le_len_mult_max[of "map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]" thalt] max_head_pos_0 by simp
  have 1: "nllength (map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]) \<le> Suc (nlength thalt) * Suc thalt"
    using nllength_le_len_mult_max[of "map (\<lambda>t. exec t <#> 1) [0..<Suc thalt]" thalt] max_head_pos_1 by simp

  let ?ttt = "thalt * (36 + 8 * nlength thalt) + 22 + nllength (map (\<lambda>t. exec t <#> 0) [0..<Suc thalt]) +
    nllength (map (\<lambda>t. (exec t) <#> 1) [0..<Suc thalt])"
  have "?ttt \<le> thalt * (36 + 8 * nlength thalt) + 22 + Suc (nlength thalt) * Suc thalt + Suc (nlength thalt) * Suc thalt"
    using 0 1 by linarith
  also have "... = thalt * (36 + 8 * nlength thalt) + 22 + 2 * Suc (nlength thalt) * Suc thalt"
    by simp
  also have "... \<le> Suc thalt * (36 + 8 * nlength thalt) + 22 + 2 * Suc (nlength thalt) * Suc thalt"
    by simp
  also have "... \<le> Suc thalt * (4 * (9 + 2 * nlength thalt)) + 22 + 2 * Suc (nlength thalt) * Suc thalt"
    by simp
  also have "... = 4 * Suc thalt * (9 + 2 * nlength thalt) + 22 + 2 * Suc (nlength thalt) * Suc thalt"
    by linarith
  also have "... = 4 * Suc thalt * (9 + 2 * nlength thalt) + 22 + Suc thalt * (2 + 2 * nlength thalt)"
    by simp
  also have "... \<le> 4 * Suc thalt * (9 + 2 * nlength thalt) + 22 + Suc thalt * (9 + 2 * nlength thalt)"
  proof -
    have "2 + 2 * nlength thalt \<le> 9 + 2 * nlength thalt"
      by simp
    then show ?thesis
      using Suc_mult_le_cancel1 add_le_cancel_left by blast
  qed
  also have "... = 5 * Suc thalt * (9 + 2 * nlength thalt) + 22"
    by linarith
  also have "... \<le> 5 * Suc thalt * (9 + 2 * nlength thalt) + 22 * Suc thalt * (9 + 2 * nlength thalt)"
  proof -
    have "1 \<le> Suc thalt * (9 + 2 * nlength thalt)"
      by simp
    then show ?thesis
      by linarith
  qed
  also have "... = 27 * Suc thalt * (9 + 2 * nlength thalt)"
    by linarith
  finally have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm8 transforms_monotone by simp
qed

end  (* context *)

end  (* locale turing_machine_list_headpos *)

lemma transforms_tm_list_headposI [transforms_intros]:
  fixes G :: nat and j :: tapeidx and M :: machine
  fixes tps tps' :: "tape list"
  fixes thalt k ttt :: nat and xs :: "symbol list"
  assumes "turing_machine 2 G M"
  assumes "length tps = k" and "k \<ge> j + 9" and "j > 0"
  assumes
    "\<forall>t<thalt. fst (execute M (start_config 2 xs) t) < length M"
    "fst (execute M (start_config 2 xs) thalt) = length M"
  assumes "symbols_lt G xs"
  assumes "tps ! j = \<lceil>\<triangleright>\<rceil>"
    "tps ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 0)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 0)"
    "tps ! (j + 3) = \<lceil>\<triangleright>\<rceil>"
    "tps ! (j + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 0)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 0)"
    "tps ! (j + 6) = \<lceil>\<triangleright>\<rceil>"
    "tps ! (j + 7) = (\<lfloor>xs\<rfloor>, 0)"
    "tps ! (j + 8) = (\<lfloor>[]\<rfloor>, 0)"
  assumes "ttt = 27 * Suc thalt * (9 + 2 * nlength thalt)"
  assumes "tps' = tps
    [(j + 1) := (\<lfloor>(execute M (start_config 2 xs) thalt) <#> 0\<rfloor>\<^sub>N, 1),
     (j + 2) := (\<lfloor>map (\<lambda>t. (execute M (start_config 2 xs) t) <#> 0) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
     (j + 4) := (\<lfloor>(execute M (start_config 2 xs) thalt) <#> 1\<rfloor>\<^sub>N, 1),
     (j + 5) := (\<lfloor>map (\<lambda>t. (execute M (start_config 2 xs) t) <#> 1) [0..<Suc thalt]\<rfloor>\<^sub>N\<^sub>L, 1),
     (j + 7) := (execute M (start_config 2 xs) thalt) <!> 0,
     (j + 8) := (execute M (start_config 2 xs) thalt) <!> 1]"
  shows "transforms (tm_list_headpos G M j) tps ttt tps'"
proof -
  interpret loc: turing_machine_list_headpos .
  show ?thesis
    using assms loc.tm8' loc.tm8_eq_tm_list_headpos loc.tps8_def by metis
qed


section \<open>A Turing machine for $\Psi$ formulas\<close>

text \<open>
CNF formulas from the $\Psi$ family of formulas feature prominently in $\Phi$. In
this section we first present a Turing machine for generating arbitrary members of this
family and later a specialized one for the $\Psi$ formulas that we need for
$\Phi$.
\<close>

subsection \<open>The general case\<close>

text \<open>
The next Turing machine generates a representation of the CNF formula $\Psi(vs,
k)$. It expects $vs$ as a list of numbers on tape $j$ and the number $k$ on tape
$j + 1$. A list of lists of numbers representing $\Psi(vs, k)$ is output to tape
$j + 2$.

The TM iterates over the elements of $vs$. In each iteration it generates a
singleton clause containing the current element of $vs$ either as positive or
negative literal, depending on whether $k$ is greater than zero or equal to
zero. Then it decrements the number $k$. Thus the first $k$ variable indices of
$vs$ will be turned into $k$ positive literals, the rest into negative ones
(provided $|vs| \geq k$).

\null
\<close>

definition tm_Psi :: "tapeidx \<Rightarrow> machine" where
  "tm_Psi j \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j \<noteq> \<box> DO
      tm_nextract \<bar> j (j + 3) ;;
      tm_times2 (j + 3) ;;
      IF \<lambda>rs. rs ! (j + 1) \<noteq> \<box> THEN
        tm_incr (j + 3)
      ELSE
        []
      ENDIF ;;
      tm_to_list (j + 3) ;;
      tm_appendl (j + 2) (j + 3) ;;
      tm_decr (j + 1) ;;
      tm_erase_cr (j + 3)
    DONE ;;
    tm_cr (j + 2) ;;
    tm_erase_cr j"

lemma tm_Psi_tm:
  assumes "0 < j" and "j + 3 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_Psi j)"
  unfolding tm_Psi_def
  using Nil_tm tm_nextract_tm tm_times2_tm tm_incr_tm tm_to_list_tm tm_appendl_tm tm_decr_tm
    tm_erase_cr_tm tm_cr_tm turing_machine_loop_turing_machine turing_machine_branch_turing_machine
    assms
  by simp

text \<open>
Two lemmas to help with the running time bound of @{const tm_Psi}:
\<close>

lemma sum_list_mono_nth:
  fixes xs :: "'a list" and f g :: "'a \<Rightarrow> nat"
  assumes "\<forall>i<length xs. f (xs ! i) \<le> g (xs ! i)"
  shows "sum_list (map f xs) \<le> sum_list (map g xs)"
  using assms by (metis in_set_conv_nth sum_list_mono)

lemma sum_list_plus_const:
  fixes xs :: "'a list" and f :: "'a \<Rightarrow> nat" and c :: nat
  shows "sum_list (map (\<lambda>x. c + f x) xs) = c * length xs + sum_list (map f xs)"
  by (induction xs) simp_all

locale turing_machine_Psi =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_nextract \<bar> j (j + 3)"
definition "tm2 \<equiv> tm1 ;; tm_times2 (j + 3)"
definition "tm23 \<equiv> IF \<lambda>rs. rs ! (j + 1) \<noteq> \<box> THEN tm_incr (j + 3) ELSE [] ENDIF"
definition "tm3 \<equiv> tm2 ;; tm23"
definition "tm4 \<equiv> tm3 ;; tm_to_list (j + 3)"
definition "tm5 \<equiv> tm4 ;; tm_appendl (j + 2) (j + 3)"
definition "tm6 \<equiv> tm5 ;; tm_decr (j + 1)"
definition "tm7 \<equiv> tm6 ;; tm_erase_cr (j + 3)"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j \<noteq> \<box> DO tm7 DONE"
definition "tm8 \<equiv> tmL ;; tm_cr (j + 2)"
definition "tm9 \<equiv> tm8 ;; tm_erase_cr j"

lemma tm9_eq_tm_Psi: "tm9 = tm_Psi j"
  unfolding tm9_def tm8_def tmL_def tm7_def tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_Psi_def tm23_def
  by simp

context
  fixes tps0 :: "tape list" and k kk :: nat and ns :: "nat list"
  assumes jk: "length tps0 = k" "0 < j" "j + 3 < k"
    and kk: "kk \<le> length ns"
  assumes tps0:
    "tps0 ! j = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j + 1) = (\<lfloor>kk\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
 "tpsL t \<equiv> tps0
    [j := nltape' ns t,
     j + 1 := (\<lfloor>kk - t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t])]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
proof -
  have "tpsL 0 ! (j + 2) = tps0 ! (j + 2)"
    using tpsL_def tps0 jk by simp
  moreover have "tpsL 0 ! (j + 1) = tps0 ! (j + 1)"
    using tpsL_def tps0 jk by simp
  moreover have "tpsL 0 ! (j + 3) = tps0 ! (j + 3)"
    using tpsL_def tps0 jk by simp
  ultimately show ?thesis
    using tpsL_def tps0 jk
    by (metis (no_types, lifting) One_nat_def diff_zero list_update_id list_update_overwrite nllength_Nil take0)
qed

definition tpsL1 :: "nat \<Rightarrow> tape list" where
 "tpsL1 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t]),
     j + 3 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "t < length ns"
    and "ttt = 12 + 2 * nlength (ns ! t)"
  shows "transforms tm1 (tpsL t) ttt (tpsL1 t)"
  unfolding tm1_def
proof (tform tps: assms(1) tpsL_def jk)
  show "tpsL t ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL_def jk tps0 canrepr_0 by simp
  show "ttt = 12 + 2 * nlength 0 + 2 * nlength (ns ! t)"
    using assms(2) by simp
  show "tpsL1 t = (tpsL t)
      [j := nltape' ns (Suc t),
       j + 3 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1)]"
    by (simp add: jk tps0 tpsL1_def tpsL_def list_update_swap numeral_3_eq_3)
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
 "tpsL2 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t]),
     j + 3 := (\<lfloor>2 * ns ! t\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "t < length ns"
    and "ttt = 17 + 4 * nlength (ns ! t)"
  shows "transforms tm2 (tpsL t) ttt (tpsL2 t)"
  unfolding tm2_def by (tform tps: assms(1) tpsL1_def tpsL2_def jk time: assms(2))

definition tpsL3 :: "nat \<Rightarrow> tape list" where
 "tpsL3 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t]),
     j + 3 := (\<lfloor>2 * ns ! t + (if t < kk then 1 else 0)\<rfloor>\<^sub>N, 1)]"

lemma tm23 [transforms_intros]:
  assumes "t < length ns"
    and "ttt = 7 + 2 * nlength (2 * ns ! t)"
  shows "transforms tm23 (tpsL2 t) ttt (tpsL3 t)"
  unfolding tm23_def
proof (tform tps: assms(1) tpsL2_def jk time: assms(2))
  show "read (tpsL2 t) ! (j + 1) \<noteq> \<box> \<Longrightarrow>
      tpsL3 t = (tpsL2 t)[j + 3 := (\<lfloor>Suc (2 * ns ! t)\<rfloor>\<^sub>N, 1)]"
    using tpsL2_def tpsL3_def jk read_ncontents_eq_0 by simp
  show "5 + 2 * nlength (2 * ns ! t) + 2 \<le> ttt"
    using assms by simp
  show "\<not> read (tpsL2 t) ! (j + 1) \<noteq> \<box> \<Longrightarrow> tpsL3 t = tpsL2 t"
    using tpsL2_def tpsL3_def jk read_ncontents_eq_0 by simp
qed

lemma tm3:
  assumes "t < length ns"
    and "ttt = 24 + 4 * nlength (ns ! t) + 2 * nlength (2 * ns ! t)"
  shows "transforms tm3 (tpsL t) ttt (tpsL3 t)"
  unfolding tm3_def by (tform tps: assms jk)

lemma tm3' [transforms_intros]:
  assumes "t < length ns" and "ttt = 26 + 6 * nlength (ns ! t)"
  shows "transforms tm3 (tpsL t) ttt (tpsL3 t)"
proof -
  let ?ttt = "24 + 4 * nlength (ns ! t) + 2 * nlength (2 * ns ! t)"
  have "nlength (2*x) \<le> Suc (nlength x)" for x
    by (metis eq_refl gr0I less_imp_le_nat nat_0_less_mult_iff nlength_0 nlength_even_le)
  then have "?ttt \<le> 24 + 4 * nlength (ns ! t) + 2 * Suc (nlength (ns ! t))"
    by (meson add_mono_thms_linordered_semiring(2) mult_le_mono2)
  then have "?ttt \<le> 26 + 6 * nlength (ns ! t)"
    by simp
  then show ?thesis
    using tm3 assms transforms_monotone by blast
qed

definition tpsL4 :: "nat \<Rightarrow> tape list" where
 "tpsL4 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t]),
     j + 3 := (\<lfloor>[2 * ns ! t + (if t < kk then 1 else 0)]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm4:
  assumes "t < length ns"
   and "ttt = 31 + 6 * nlength (ns ! t) + 2 * nlength (2 * ns ! t + (if t < kk then 1 else 0))"
  shows "transforms tm4 (tpsL t) ttt (tpsL4 t)"
  unfolding tm4_def
proof (tform tps: assms tpsL3_def jk tps0)
  show "tpsL4 t = (tpsL3 t)
      [j + 3 := (\<lfloor>[2 * ns ! t + (if t < kk then 1 else 0)]\<rfloor>\<^sub>N\<^sub>L, 1)]"
    using tpsL3_def tpsL4_def jk tps0 by simp
qed

lemma tm4' [transforms_intros]:
  assumes "t < length ns" and "ttt = 33 + 8 * nlength (ns ! t)"
  shows "transforms tm4 (tpsL t) ttt (tpsL4 t)"
proof -
  have "nlength (2 * ns ! t + (if t < kk then 1 else 0)) \<le> Suc (nlength (ns ! t))"
    using nlength_0_simp nlength_even_le nlength_le_n nlength_times2plus1
    by (smt (z3) add.right_neutral le_Suc_eq mult_0_right neq0_conv)
  then have "31 + 6 * nlength (ns ! t) +
      2 * nlength (2 * ns ! t + (if t < kk then 1 else 0)) \<le> ttt"
    using assms(2) by simp
  then show ?thesis
    using tm4 transforms_monotone assms(1) by blast
qed

definition tpsL5 :: "nat \<Rightarrow> tape list" where
 "tpsL5 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<Suc t]),
     j + 3 := (\<lfloor>[2 * ns ! t + (if t < kk then 1 else 0)]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm5 [transforms_intros]:
  assumes "t < length ns"
    and "ttt = 39 + 8 * nlength (ns ! t) + 2 * nllength [2 * ns ! t + (if t < kk then 1 else 0)]"
  shows "transforms tm5 (tpsL t) ttt (tpsL5 t)"
  unfolding tm5_def
proof (tform tps: assms(1) tpsL4_def jk)
  let ?tps = "(tpsL4 t)
    [j + 2 := nlltape
        (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t] @ [[2 * ns ! t + (if t < kk then 1 else 0)]])]"
  show "tpsL5 t = ?tps"
    unfolding tpsL5_def tpsL4_def
    by (simp only: list_update_overwrite list_update_swap_less[of "j+2"]) simp
  show "ttt = 33 + 8 * nlength (ns ! t) +
      (7 + nlllength (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t]) -
       Suc (nlllength (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<t])) +
      2 * nllength [2 * ns ! t + (if t < kk then 1 else 0)])"
    using assms by simp
qed

definition tpsL6 :: "nat \<Rightarrow> tape list" where
 "tpsL6 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - t - 1\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<Suc t]),
     j + 3 := (\<lfloor>[2 * ns ! t + (if t < kk then 1 else 0)]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm6:
  assumes "t < length ns"
    and "ttt = 39 + 8 * nlength (ns ! t) +
      2 * nllength [2 * ns ! t + (if t < kk then 1 else 0)] +
      (8 + 2 * nlength (kk - t))"
  shows "transforms tm6 (tpsL t) ttt (tpsL6 t)"
  unfolding tm6_def by (tform tps: assms(1) tpsL6_def tpsL5_def jk time: assms(2))

lemma nllength_elem: "nllength [2 * ns ! t + (if t < kk then 1 else 0)] \<le> 2 + nlength (ns ! t)"
proof -
  have "2 * ns ! t + (if t < kk then 1 else 0) \<le> 2 * ns ! t + 1"
    by simp
  then have "nlength (2 * ns ! t + (if t < kk then 1 else 0)) \<le> nlength (2 * ns ! t + 1)"
    using nlength_mono by simp
  then have "nlength (2 * ns ! t + (if t < kk then 1 else 0)) \<le> Suc (nlength (ns ! t))"
    using nlength_times2plus1 by fastforce
  then show ?thesis
    using nllength by simp
qed

lemma tm6' [transforms_intros]:
  assumes "t < length ns"
    and "ttt = 43 + 10 * nlength (ns ! t) + (8 + 2 * nlength (kk - t))"
  shows "transforms tm6 (tpsL t) ttt (tpsL6 t)"
proof -
  let ?ttt = "39 + 8 * nlength (ns ! t) +
      2 * nllength [2 * ns ! t + (if t < kk then 1 else 0)] +
      (8 + 2 * nlength (kk - t))"
  have "?ttt \<le> 39 + 8 * nlength (ns ! t) +
      2 * (2 + nlength (ns ! t)) + (8 + 2 * nlength (kk - t))"
    using nllength_elem
    by (meson add_mono_thms_linordered_semiring(2) add_mono_thms_linordered_semiring(3) nat_mult_le_cancel_disj)
  also have "... \<le> 43 + 10 * nlength (ns ! t) + (8 + 2 * nlength (kk - t))"
    by simp
  finally have "?ttt \<le> ttt"
    using assms(2) by simp
  then show ?thesis
    using assms(1) tm6 transforms_monotone by blast
qed

definition tpsL7 :: "nat \<Rightarrow> tape list" where
 "tpsL7 t \<equiv> tps0
    [j := nltape' ns (Suc t),
     j + 1 := (\<lfloor>kk - Suc t\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<Suc t]),
     j + 3 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm7:
  assumes "t < length ns"
    and "ttt = 51 + (10 * nlength (ns ! t) + 2 * nlength (kk - t)) +
      (7 + 2 * length (numlist [2 * ns ! t + (if t < kk then 1 else 0)]))"
  shows "transforms tm7 (tpsL t) ttt (tpsL7 t)"
  unfolding tm7_def
proof (tform tps: assms(1) tpsL6_def tpsL7_def jk time: tpsL6_def jk assms(2))
  let ?ns = "[2 * ns ! t + (if t < kk then 1 else 0)]"
  show "tpsL6 t ::: (j + 3) = \<lfloor>numlist ?ns\<rfloor>"
    using tpsL6_def nlcontents_def jk by simp
  show "proper_symbols (numlist ?ns)"
    using proper_symbols_numlist by simp
qed

lemma tm7':
  assumes "t < length ns" and "ttt = 62 + 14 * nllength ns"
  shows "transforms tm7 (tpsL t) ttt (tpsL7 t)"
proof -
  let ?ttt = "51 + (10 * nlength (ns ! t) + 2 * nlength (kk - t)) +
      (7 + 2 * length (numlist [2 * ns ! t + (if t < kk then 1 else 0)]))"
  have "?ttt = 58 + (10 * nlength (ns ! t) + 2 * nlength (kk - t)) +
      2 * length (numlist [2 * ns ! t + (if t < kk then 1 else 0)])"
    by simp
  also have "... \<le> 58 + (10 * nlength (ns ! t) + 2 * nlength (kk - t)) + 2 * (2 + nlength (ns ! t))"
    using nllength_elem nllength_def mult_le_mono2 nat_add_left_cancel_le by metis
  also have "... = 62 + 12 * nlength (ns ! t) + 2 * nlength (kk - t)"
    by simp
  also have "... \<le> 62 + 12 * nlength (ns ! t) + 2 * nlength (length ns)"
    using assms(1) kk nlength_mono by simp
  also have "... \<le> 62 + 12 * nllength ns + 2 * nlength (length ns)"
    using assms(1) member_le_nllength by simp
  also have "... \<le> 62 + 12 * nllength ns + 2 * nllength ns"
    using length_le_nllength nlength_le_n by (meson add_left_mono dual_order.trans mult_le_mono2)
  also have "... = 62 + 14 * nllength ns"
    by simp
  finally have "?ttt \<le> 62 + 14 * nllength ns" .
  then show ?thesis
    using assms tm7 transforms_monotone by blast
qed

lemma tpsL7_eq_tpsL: "tpsL7 t = tpsL (Suc t)"
  unfolding tpsL7_def tpsL_def
  using jk tps0
  by (smt (z3) Suc_eq_plus1 add_2_eq_Suc' add_cancel_left_right add_left_cancel list_update_id list_update_swap
   num.simps(8) numeral_eq_iff numeral_eq_one_iff semiring_norm(86) zero_neq_numeral)

lemma tm7'' [transforms_intros]:
  assumes "t < length ns" and "ttt = 62 + 14 * nllength ns"
  shows "transforms tm7 (tpsL t) ttt (tpsL (Suc t))"
  using assms tpsL7_eq_tpsL tm7' by simp

lemma tmL [transforms_intros]:
  assumes "ttt = length ns * (62 + 14 * nllength ns + 2) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length ns))"
  unfolding tmL_def
proof (tform)
  let ?t = "62 + 14 * nllength ns"
  show "read (tpsL t) ! j \<noteq> \<box>" if "t < length ns" for t
  proof -
    have "tpsL t ! j = nltape' ns t"
      using tpsL_def jk by simp
    then show ?thesis
      using nltape'_tape_read that tapes_at_read' tpsL_def jk
      by (metis (no_types, lifting) add_lessD1 leD length_list_update)
  qed
  have "tpsL t ! j = nltape' ns t" for t
    using tpsL_def jk nlcontents_def by simp
  then show "\<not> read (tpsL (length ns)) ! j \<noteq> \<box>"
    using nltape'_tape_read tpsL_def jk tapes_at_read'
    by (metis (no_types, lifting) add_lessD1 length_list_update order_refl)
  show "length ns * (62 + 14 * nllength ns + 2) + 1 \<le> ttt"
    using assms by simp
qed

definition tps8 :: "tape list" where
 "tps8 \<equiv> tps0
    [j := nltape' ns (length ns),
     j + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape' (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<length ns]) 0]"

lemma tm8:
  assumes "ttt = Suc (length ns * (64 + 14 * nllength ns)) +
    Suc (Suc (Suc (nlllength (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<length ns]))))"
  shows "transforms tm8 (tpsL 0) ttt tps8"
  unfolding tm8_def
proof (tform tps: tpsL_def tps8_def jk time: assms tpsL_def jk)
  show "clean_tape (tpsL (length ns) ! (j + 2))"
    using tpsL_def jk clean_tape_nllcontents by simp
  show "tps8 = (tpsL (length ns))[j + 2 := tpsL (length ns) ! (j + 2) |#=| 1]"
    unfolding tps8_def tpsL_def using jk kk by simp
qed

lemma tm8' [transforms_intros]:
  assumes "ttt = 4 + 81 * nllength ns ^ 2"
  shows "transforms tm8 tps0 ttt tps8"
proof -
  let ?nss = "map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<length ns]"
  let ?ttt = "Suc (length ns * (64 + 14 * nllength ns)) + Suc (Suc (Suc (nlllength ?nss)))"

  have "nlllength ?nss = (\<Sum>ns\<leftarrow>?nss. Suc (nllength ns))"
    using nlllength by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<length ns]. Suc (nllength [2 * ns ! i + (if i < kk then 1 else 0)]))"
  proof -
    have "map (\<lambda>ns. Suc (nllength ns)) ?nss = map (\<lambda>i. Suc (nllength (?nss ! i))) [0..<length ns]"
      by simp
    then have "map (\<lambda>ns. Suc (nllength ns)) ?nss = map (\<lambda>i. Suc (nllength [2 * ns ! i + (if i < kk then 1 else 0)])) [0..<length ns]"
      by simp
    then show ?thesis
      by metis
  qed
  also have "... = (\<Sum>i\<leftarrow>[0..<length ns]. Suc (Suc (nlength (2 * ns ! i + (if i < kk then 1 else 0)))))"
    using nllength by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[0..<length ns]. Suc (Suc (nlength (2 * ns ! i + 1))))"
    using sum_list_mono_nth[of "[0..<length ns]"] nlength_mono by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[0..<length ns]. Suc (Suc (Suc (nlength (ns ! i)))))"
    using sum_list_mono_nth[of "[0..<length ns]"] nlength_times2plus1 by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<length ns]. 2 + Suc (nlength (ns ! i)))"
    by simp
  also have "... = 2 * length ns + (\<Sum>i\<leftarrow>[0..<length ns]. Suc (nlength (ns ! i)))"
    using sum_list_plus_const[of 2 _ "[0..<length ns]"] by simp
  also have "... = 2 * length ns + nllength ns"
  proof -
    have "map (\<lambda>i. Suc (nlength (ns ! i))) [0..<length ns] = map (\<lambda>n. Suc (nlength n)) ns"
      by (rule nth_equalityI) simp_all
    then show ?thesis
      using nllength by simp
  qed
  finally have "nlllength ?nss \<le> 2 * length ns + nllength ns" .
  then have "?ttt \<le> Suc (length ns * (64 + 14 * nllength ns)) + Suc (Suc (Suc (2 * length ns + nllength ns)))"
    by simp
  also have "... = 4 + length ns * (64 + 14 * nllength ns) + 2 * length ns + nllength ns"
    by simp
  also have "... = 4 + length ns * (66 + 14 * nllength ns) + nllength ns"
    by algebra
  also have "... \<le> 4 + nllength ns * (66 + 14 * nllength ns) + nllength ns"
    using length_le_nllength by simp
  also have "... = 4 + 67 * nllength ns + 14 * nllength ns ^ 2"
    by algebra
  also have "... \<le> 4 + 67 * nllength ns ^ 2 + 14 * nllength ns ^ 2"
    using linear_le_pow by simp
  also have "... = 4 + 81 * nllength ns ^ 2"
    by simp
  finally have "?ttt \<le> 4 + 81 * nllength ns ^ 2" .
  then show ?thesis
    using tm8 assms transforms_monotone tpsL_eq_tps0 by simp
qed

definition tps9 :: "tape list" where
 "tps9 \<equiv> tps0
    [j := (\<lfloor>[]\<rfloor>, 1),
     j + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape' (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<length ns]) 0]"

lemma tm9:
  assumes "ttt = 11 + 81 * nllength ns ^ 2 + 3 * nllength ns"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def
proof (tform tps: tps8_def tps9_def jk)
  show "tps8 ::: j = \<lfloor>numlist ns\<rfloor>"
    using tps8_def jk nlcontents_def by simp
  show "proper_symbols (numlist ns)"
    using proper_symbols_numlist by simp
  show "ttt = 4 + 81 * (nllength ns)\<^sup>2 + (tps8 :#: j + 2 * length (numlist ns) + 6)"
    using tps8_def jk assms nllength_def by simp
qed

lemma tm9':
  assumes "ttt = 11 + 84 * nllength ns ^ 2"
  shows "transforms tm9 tps0 ttt tps9"
proof -
  have "11 + 81 * nllength ns ^ 2 + 3 * nllength ns \<le> 11 + 84 * nllength ns ^ 2"
    using linear_le_pow by simp
  then show ?thesis
    using tm9 assms transforms_monotone by simp
qed

end

end  (* locale turing_machine_Psi *)

lemma transforms_tm_PsiI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k kk :: nat and ns :: "nat list"
  assumes "length tps = k" "0 < j" "j + 3 < k"
    and "kk \<le> length ns"
  assumes
    "tps ! j = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j + 1) = (\<lfloor>kk\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 11 + 84 * nllength ns ^ 2"
  assumes "tps' = tps
    [j := (\<lfloor>[]\<rfloor>, 1),
     j + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape' (map (\<lambda>t. [2 * ns ! t + (if t < kk then 1 else 0)]) [0..<length ns]) 0]"
  shows "transforms (tm_Psi j) tps ttt tps'"
proof -
  interpret loc: turing_machine_Psi j .
  show ?thesis
    using loc.tm9_eq_tm_Psi loc.tps9_def loc.tm9' assms by simp
qed


subsection \<open>For intervals\<close>

text \<open>
To construct $\Phi$ we need only $\Psi$ formulas where the variable index list
is an interval $\gamma_i = [iH, (i+1)H)$. In this section we devise a Turing
machine that outputs $\Psi([start, start + len), \kappa)$ for arbitrary $start$,
$len$, and $\kappa$.
\<close>

definition nll_Psi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "nll_Psi start len \<kappa> \<equiv> map (\<lambda>i. [2 * (start + i) + (if i < \<kappa> then 1 else 0)]) [0..<len]"

lemma nll_Psi: "nll_Psi start len \<kappa> = formula_n (\<Psi> [start..<start+len] \<kappa>)"
    (is "?lhs = ?rhs")
proof (rule nth_equalityI)
  show len: "length ?lhs = length ?rhs"
    using nll_Psi_def Psi_def formula_n_def by simp
  let ?psi = "\<Psi> [start..<start+len] \<kappa>"
  show "?lhs ! i = ?rhs ! i" if "i < length ?lhs" for i
  proof -
    have "i < length ?psi"
      using that Psi_def nll_Psi_def by simp
    have "i < len"
      using that Psi_def nll_Psi_def by simp
    show ?thesis
    proof (cases "i < \<kappa>")
      case True
      then have "?psi ! i = [Pos (start + i)]"
        using Psi_def nth_append[of "map (\<lambda>s. [Pos s]) (take \<kappa> [start..<start+len])" _ i] `i < len`
        by simp
      moreover have "?rhs ! i = clause_n (?psi ! i)"
        using formula_n_def that `i < length ?psi` by simp
      ultimately have "?rhs ! i = [Suc (2 * (start + i))]"
        using clause_n_def by simp
      moreover have "?lhs ! i = [2 * (start + i) + 1]"
        using True nll_Psi_def that by simp
      ultimately show ?thesis
        by simp
    next
      case False
      then have "?psi ! i = [Neg (start + i)]"
        using Psi_def nth_append[of "map (\<lambda>s. [Pos s]) (take \<kappa> [start..<start+len])" _ i] `i < len`
        by auto
      moreover have "?rhs ! i = clause_n (?psi ! i)"
        using formula_n_def that `i < length ?psi` by simp
      ultimately have "?rhs ! i = [2 * (start + i)]"
        using clause_n_def by simp
      moreover have "?lhs ! i = [2 * (start + i)]"
        using False nll_Psi_def that by simp
      ultimately show ?thesis
        by simp
    qed
  qed
qed

lemma nlllength_nll_Psi_le: "nlllength (nll_Psi start len \<kappa>) \<le> len * (3 + nlength (start + len))"
proof -
  define f :: "nat \<Rightarrow> nat list" where
    "f = (\<lambda>i. [2 * (start + i) + (if i < \<kappa> then 1 else 0)])"
  let ?nss = "map f [0..<len]"
  have "nlllength (nll_Psi start len \<kappa>) = (\<Sum>ns\<leftarrow>?nss. Suc (nllength ns))"
    using nlllength f_def nll_Psi_def by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<len]. (\<lambda>ns. Suc (nllength ns)) (f i))"
    by (metis (no_types, lifting) map_eq_conv map_map o_apply)
  also have "... = (\<Sum>i\<leftarrow>[0..<len]. Suc (nllength ([2 * (start + i) + (if i < \<kappa> then 1 else 0)])))"
    using f_def by simp
  also have "... = (\<Sum>i\<leftarrow>[0..<len]. Suc (Suc (nlength (2 * (start + i) + (if i < \<kappa> then 1 else 0)))))"
    using nllength by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[0..<len]. Suc (Suc (nlength (2 * (start + i) + 1))))"
    using nlength_mono
      sum_list_mono[of "[0..<len]"
        "\<lambda>i. Suc (Suc (nlength (2 * (start + i) + (if i < \<kappa> then 1 else 0))))"
        "\<lambda>i. Suc (Suc (nlength (2 * (start + i) + 1)))"]
    by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[0..<len]. Suc (Suc (nlength (2 * (start + len)))))"
    using nlength_mono
      sum_list_mono[of "[0..<len]"
        "\<lambda>i. Suc (Suc (nlength (2 * (start + i) + 1)))"
        "\<lambda>i. Suc (Suc (nlength (2 * (start + len))))"]
    by simp
  also have "... = len * Suc (Suc (nlength (2 * (start + len))))"
    using sum_list_const[of _ "[0..<len]"] by simp
  also have "... \<le> len * Suc (Suc (Suc (nlength (start + len))))"
    using nlength_times2 by (metis add_gr_0 eq_refl mult_le_cancel1 nlength_even_le)
  also have "... = len * (3 + nlength (start + len))"
    by (simp add: Suc3_eq_add_3)
  finally show ?thesis .
qed

lemma nlllength_nll_Psi_le':
  assumes "start1 \<le> start2"
  shows "nlllength (nll_Psi start1 len \<kappa>) \<le> len * (3 + nlength (start2 + len))"
proof -
  have "nlllength (nll_Psi start1 len \<kappa>) \<le> len * (3 + nlength (start1 + len))"
    using nlllength_nll_Psi_le by simp
  moreover have "nlength (start1 + len) \<le> nlength (start2 + len)"
    using assms nlength_mono by simp
  ultimately show ?thesis
    by (meson add_mono_thms_linordered_semiring(2) mult_le_mono2 order_trans)
qed

lemma H4_nlength:
  fixes x y H :: nat
  assumes "x \<le> y" and "H \<ge> 3"
  shows "H ^ 4 * (nlength x)\<^sup>2 \<le> H ^ 4 * (nlength y)\<^sup>2"
  using assms by (simp add: nlength_mono)

text \<open>
The next Turing machine receives on tape $j$ a number $i$, on tape $j + 1$ a
number $H$, and on tape $j + 2$ a number $\kappa$. It outputs $\Psi([i \cdot
H, (i + 1) \cdot H), \kappa)$.
\<close>

definition tm_Psigamma :: "tapeidx \<Rightarrow> machine" where
  "tm_Psigamma j \<equiv>
    tm_mult j (j + 1) (j + 3) ;;
    tm_range (j + 3) (j + 1) (j + 4) ;;
    tm_copyn (j + 2) (j + 5) ;;
    tm_Psi (j + 4) ;;
    tm_erase_cr (j + 3)"

lemma tm_Psigamma_tm:
  assumes "G \<ge> 6" and "j + 7 < k"
  shows "turing_machine k G (tm_Psigamma j)"
  unfolding tm_Psigamma_def
  using assms tm_mult_tm tm_range_tm tm_copyn_tm tm_Psi_tm tm_erase_cr_tm
  by simp

locale turing_machine_Psigamma =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_mult j (j + 1) (j + 3)"
definition "tm2 \<equiv> tm1 ;; tm_range (j + 3) (j + 1) (j + 4)"
definition "tm3 \<equiv> tm2 ;; tm_copyn (j + 2) (j + 5)"
definition "tm4 \<equiv> tm3 ;; tm_Psi (j + 4)"
definition "tm5 \<equiv> tm4 ;; tm_erase_cr (j + 3)"

lemma tm5_eq_tm_Psigamma: "tm5 = tm_Psigamma j"
  using tm5_def tm4_def tm3_def tm2_def tm1_def tm_Psigamma_def by simp

context
  fixes tps0 :: "tape list" and H k idx \<kappa> :: nat
  assumes jk: "length tps0 = k" "0 < j" "j + 7 < k"
    and H: "H \<ge> 3"
    and \<kappa>: "\<kappa> \<le> H"
  assumes tps0:
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>\<kappa>\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j + 3 := (\<lfloor>idx * H\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 4 + 26 * (nlength idx + nlength H) ^ 2 "
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk tps0 tps1_def)
  show "tps0 ! (j + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps0 canrepr_0 by simp
  show "ttt = 4 + 26 * (nlength idx + nlength H) * (nlength idx + nlength H)"
    using assms by algebra
qed

definition "tps2 \<equiv> tps0
  [j + 3 := (\<lfloor>idx * H\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>[idx * H..<idx * H + H]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 4 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps0 tps1_def tps2_def jk time: assms)
  show "tps1 ! (j + 4) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps1_def tps0 jk nlcontents_Nil by simp
  have "j + 4 + 1 = j + 5"
    by simp
  then show "tps1 ! (j + 4 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps1_def tps0 jk canrepr_0
    by (metis add_left_imp_eq nth_list_update_neq numeral_eq_iff semiring_norm(83) semiring_norm(90))
  have "j + 4 + 2 = j + 6"
    by simp
  then show "tps1 ! (j + 4 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps1_def tps0 jk canrepr_0
    by (metis add_left_imp_eq nth_list_update_neq num.simps(8) numeral_eq_iff)
qed

definition "tps3 \<equiv> tps0
  [j + 3 := (\<lfloor>idx * H\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>[idx * H..<idx * H + H]\<rfloor>\<^sub>N\<^sub>L, 1),
   j + 5 := (\<lfloor>\<kappa>\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 18 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) + 3 * nlength \<kappa>"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps0 tps2_def tps3_def jk)
  show "tps2 ! (j + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps2_def jk tps0 canrepr_0 by simp
  show "ttt = 4 + 26 * (nlength idx + nlength H)\<^sup>2 +
      Suc H * (43 + 9 * nlength (idx * H + H)) +
      (14 + 3 * (nlength \<kappa> + nlength 0))"
    using assms by simp
qed

definition "tps4 \<equiv> tps0
  [j + 3 := (\<lfloor>idx * H\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>[]\<rfloor>, 1),
   j + 5 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 6 := nlltape'
        (map (\<lambda>t. [2 * [idx * H..<idx * H + H] ! t + (if t < \<kappa> then 1 else 0)])
          [0..<length [idx * H..<idx * H + H]]) 0]"

lemma tm4:
  assumes "ttt = 29 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) +
     3 * nlength \<kappa> + 84 * (nllength [idx * H..<idx * H + H])\<^sup>2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps0 tps3_def tps4_def jk \<kappa> time: assms)
  have *: "j + 4 + 1 = j + 5" "j + 4 + 2 = j + 6" "j + 4 + 3 = j + 7"
    using add.assoc by simp_all
  have "tps3 ! (j + 5) = (\<lfloor>\<kappa>\<rfloor>\<^sub>N, 1)"
    using tps3_def jk by simp
  then show "tps3 ! (j + 4 + 1) = (\<lfloor>\<kappa>\<rfloor>\<^sub>N, 1)"
    using * by metis
  have "tps3 ! (j + 6) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using tps3_def jk tps0 nllcontents_Nil by simp
  then show "tps3 ! (j + 4 + 2) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
    using * by metis
  have "tps3 ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
    using tps3_def jk tps0 by simp
  then show "tps3 ! (j + 4 + 3) = (\<lfloor>[]\<rfloor>, 1)"
    using * by metis
  have "tps4 = tps3
    [j + 4 := (\<lfloor>[]\<rfloor>, 1),
     j + 5 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 6 := nlltape'
        (map (\<lambda>t. [2 * [idx * H..<idx * H + H] ! t + (if t < \<kappa> then 1 else 0)])
          [0..<length [idx * H..<idx * H + H]]) 0]"
    unfolding tps4_def tps3_def
    by (simp only: list_update_overwrite list_update_swap_less)
  then show "tps4 = tps3
    [j + 4 := (\<lfloor>[]\<rfloor>, 1),
     j + 4 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j + 4 + 2 := nlltape'
        (map (\<lambda>t. [2 * [idx * H..<idx * H + H] ! t + (if t < \<kappa> then 1 else 0)])
          [0..<length [idx * H..<idx * H + H]]) 0]"
    using * by metis
qed

definition "tps4' \<equiv> tps0
  [j + 3 := (\<lfloor>idx * H\<rfloor>\<^sub>N, 1),
   j + 4 := (\<lfloor>[]\<rfloor>, 1),
   j + 5 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 6 := nlltape' (map (\<lambda>t. [2 * (idx * H + t) + (if t < \<kappa> then 1 else 0)]) [0..<H]) 0]"

lemma tps4'_eq_tps4: "tps4' = tps4"
proof -
  have "map (\<lambda>t. [2 * [idx * H..<idx * H + H] ! t + (if t < \<kappa> then 1 else 0)]) [0..<length [idx * H..<idx * H + H]] =
      map (\<lambda>t. [2 * (idx * H + t) + (if t < \<kappa> then 1 else 0)]) [0..<H]"
    by simp
  then show ?thesis
    using tps4'_def tps4_def by metis
qed

lemma tm4' [transforms_intros]:
  assumes "ttt = 29 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) +
     3 * nlength \<kappa> + 84 * (nllength [idx * H..<idx * H + H])\<^sup>2"
  shows "transforms tm4 tps0 ttt tps4'"
  using tm4 tps4'_eq_tps4 assms by simp

definition "tps5 \<equiv> tps0
  [j + 3 := (\<lfloor>[]\<rfloor>, 1),
   j + 4 := (\<lfloor>[]\<rfloor>, 1),
   j + 5 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 6 := nlltape' (map (\<lambda>t. [2 * (idx * H + t) + (if t < \<kappa> then 1 else 0)]) [0..<H]) 0]"

lemma tm5:
  assumes "ttt = 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) +
    3 * nlength \<kappa> + 84 * (nllength [idx * H..<idx * H + H])\<^sup>2 +
    2 * nlength (idx * H)"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: tps0 tps4'_def tps5_def jk \<kappa> time: assms tps4'_def jk)
  show "proper_symbols (canrepr (idx * H))"
    using proper_symbols_canrepr by simp
qed

definition "tps5' \<equiv> tps0
  [j + 6 := (\<lfloor>nll_Psi (idx * H) H \<kappa>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tps5'_eq_tps5: "tps5' = tps5"
  using tps5'_def tps5_def jk tps0 nll_Psi_def nlltape'_0 canrepr_0 by (metis list_update_id)

lemma tm5':
  assumes "ttt = 1851 * H^4 * (nlength (Suc idx))^2"
  shows "transforms tm5 tps0 ttt tps5'"
proof -
  let ?ttt = "36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) +
      3 * nlength \<kappa> + 84 * (nllength [idx * H..<idx * H + H])\<^sup>2 + 2 * nlength (idx * H)"
  have "?ttt \<le> 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) +
      3 * nlength \<kappa> + 84 * (Suc (nlength (Suc idx * H)) * H)\<^sup>2 + 2 * nlength (idx * H)"
    using nllength_le_len_mult_max[of "[idx * H..<idx * H + H]" "Suc idx * H"] by simp
  also have "... \<le> 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (idx * H + H)) +
      3 * nlength H + 84 * (Suc (nlength (Suc idx * H)) * H)\<^sup>2 + 2 * nlength (idx * H)"
    using \<kappa> nlength_mono by simp
  also have "... = 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * nlength (Suc idx * H)) +
      3 * nlength H + 84 * (Suc (nlength (Suc idx * H)) * H)\<^sup>2 + 2 * nlength (idx * H)"
    by (simp add: add.commute)
  also have "... \<le> 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      3 * nlength H + 84 * (Suc (nlength (Suc idx * H)) * H)\<^sup>2 + 2 * nlength (idx * H)"
  proof -
    have "Suc H * (43 + 9 * nlength (Suc idx * H)) \<le> Suc H * (43 + 9 * (nlength (Suc idx) + nlength H))"
      using nlength_prod by (meson add_mono_thms_linordered_semiring(2) mult_le_mono2)
    then show ?thesis
      by simp
  qed
  also have "... \<le> 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      3 * nlength H + 84 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + 2 * nlength (idx * H)"
    using nlength_prod Suc_le_mono add_le_mono le_refl mult_le_mono power2_nat_le_eq_le by presburger
  also have "... \<le> 36 + 26 * (nlength idx + nlength H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      3 * nlength H + 84 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + 2 * (nlength idx + nlength H)"
    using nlength_prod Suc_le_mono add_le_mono le_refl mult_le_mono power2_nat_le_eq_le by presburger
  also have "... \<le> 36 + 26 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      3 * nlength H + 84 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + 2 * (nlength idx + nlength H)"
  proof -
    have "nlength idx + nlength H \<le> Suc (nlength (Suc idx) + nlength H)"
      using nlength_mono by (metis add.commute nat_add_left_cancel_le nlength_Suc_le plus_1_eq_Suc trans_le_add2)
    moreover have "H > 0"
      using H by simp
    ultimately have "nlength idx + nlength H \<le> Suc (nlength (Suc idx) + nlength H) * H"
      by (metis (no_types, opaque_lifting) Suc_le_eq Suc_neq_Zero mult.assoc mult.commute mult_eq_1_iff mult_le_mono nat_mult_eq_cancel_disj)
    then show ?thesis
      by simp
  qed
  also have "... = 36 + 110 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      3 * nlength H + 2 * (nlength idx + nlength H)"
    by simp
  also have "... \<le> 36 + 110 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      3 * (Suc (nlength (Suc idx) + nlength H) * H)^2 + 2 * (nlength idx + nlength H)"
  proof -
    have "nlength H \<le> Suc (nlength (Suc idx) + nlength H) * H"
      using H by (simp add: nlength_le_n trans_le_add1)
    then have "nlength H \<le> (Suc (nlength (Suc idx) + nlength H) * H)^2"
      by (meson le_refl le_trans power2_nat_le_imp_le)
    then show ?thesis
      by simp
  qed
  also have "... = 36 + 113 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      2 * (nlength idx + nlength H)"
    by simp
  also have "... \<le> 36 + 113 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + Suc H * (43 + 9 * (nlength (Suc idx) + nlength H)) +
      2 * (Suc (nlength (Suc idx) + nlength H) * H) ^ 2"
  proof -
    have "nlength idx + nlength H \<le> Suc (nlength (Suc idx) + nlength H)"
      using nlength_mono by (simp add: le_SucI)
    also have "... \<le> Suc (nlength (Suc idx) + nlength H) * H"
      using H by (metis Suc_eq_plus1 le_add2 mult.commute mult_le_mono1 nat_mult_1 numeral_eq_Suc order_trans)
    also have "... \<le> (Suc (nlength (Suc idx) + nlength H) * H)^2"
      by (simp add: power2_eq_square)
    finally have "nlength idx + nlength H \<le> (Suc (nlength (Suc idx) + nlength H) * H)^2" .
    then show ?thesis
      by simp
  qed
  also have "... = 79 + 115 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 +
      9 * (nlength (Suc idx) + nlength H) + (43 + 9 * (nlength (Suc idx) + nlength H)) * H"
    by simp
  also have "... = 79 + 115 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 +
      9 * (nlength (Suc idx) + nlength H) + 43 * H + 9 * (nlength (Suc idx) + nlength H) * H"
    by algebra
  also have "... \<le> 79 + 115 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 +
      9 * (Suc (nlength (Suc idx) + nlength H) * H) ^ 2 + 43 * H + 9 * (nlength (Suc idx) + nlength H) * H"
  proof -
    have "nlength (Suc idx) + nlength H \<le> Suc (nlength (Suc idx) + nlength H)"
      by simp
    also have "... \<le> Suc (nlength (Suc idx) + nlength H) * H"
      using H
      by (metis One_nat_def add_leD1 le_refl mult_le_mono mult_numeral_1_right numeral_3_eq_3 numeral_nat(1) plus_1_eq_Suc)
    also have "... \<le> (Suc (nlength (Suc idx) + nlength H) * H) ^ 2"
      by (simp add: power2_eq_square)
    finally have "nlength (Suc idx) + nlength H \<le> (Suc (nlength (Suc idx) + nlength H) * H) ^ 2" .
    then show ?thesis
      by simp
  qed
  also have "... = 79 + 124 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + 43 * H + 9 * (nlength (Suc idx) + nlength H) * H"
    by simp
  also have "... \<le> 79 + 124 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 +
    43 * H + 9 * (Suc (nlength (Suc idx) + nlength H) * H) ^ 2"
  proof -
    have "(nlength (Suc idx) + nlength H) * H \<le> Suc (nlength (Suc idx) + nlength H) * H"
      by simp
    then have "(nlength (Suc idx) + nlength H) * H \<le> (Suc (nlength (Suc idx) + nlength H) * H) ^ 2"
      by (metis nat_le_linear power2_nat_le_imp_le verit_la_disequality)
    then show ?thesis
      by linarith
  qed
  also have "... = 79 + 133 * (Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 + 43 * H"
    by simp
  also have "... \<le> 79 + 133 * (9*H^3 * (nlength (Suc idx))^2 + 4*H^4) + 43 * H"
  proof -
    let ?m = "nlength (Suc idx)"
    let ?l = "Suc ?m"
    have "(Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 = ((?l + nlength H) * H)\<^sup>2"
      by simp
    also have "... = (?l*H + nlength H*H) ^ 2"
      by algebra
    also have "... \<le> (?l*H + H*H) ^ 2"
      using nlength_le_n by simp
    also have "... = (?l*H)^2 + 2*?l*H^3 + H^4"
      by algebra
    also have "... \<le> (?l*H)^2 + 2*?l^2*H^3 + H^4"
      by (metis Suc_n_not_le_n add_le_mono1 mult_le_mono1 mult_le_mono2 nat_add_left_cancel_le not_less_eq_eq power2_nat_le_imp_le)
    also have "... = ?l^2*(H^2 + 2*H^3) + H^4"
      by algebra
    also have "... \<le> ?l^2*(H^3 + 2*H^3) + H^4"
    proof -
      have "H^2 \<le> H^3"
        using pow_mono by (simp add: numeral_3_eq_3 numerals(2))
      then show ?thesis
        by simp
    qed
    also have "... = ?l^2*3*H^3 + H^4"
      by simp
    also have "... = (?m^2 + 2 * ?m + 1)*3*H^3 + H^4"
      by (smt (z3) add.commute add_Suc mult_2 nat_1_add_1 one_power2 plus_1_eq_Suc power2_sum)
    also have "... \<le> (?m^2 + 2 * ?m^2 + 1)*3*H^3 + H^4"
      using linear_le_pow by simp
    also have "... = (3*?m^2 + 1)*3*H^3 + H^4"
      by simp
    also have "... = 9*?m^2*H^3 + 3*H^3 + H^4"
      by algebra
    also have "... \<le> 9*?m^2*H^3 + 3*H^4 + H^4"
      using pow_mono' by simp
    also have "... = 9*H^3 * ?m^2 + 4*H^4"
      by simp
    finally have "(Suc (nlength (Suc idx) + nlength H) * H)\<^sup>2 \<le> 9*H^3 * ?m^2 + 4*H^4" .
    then show ?thesis
      by simp
  qed
  also have "... = 79 + 133 * 9*H^3 * (nlength (Suc idx))^2 + 133*4*H^4 + 43 * H"
    by simp
  also have "... \<le> 79 + 133 * 9*H^3 * (nlength (Suc idx))^2 + 133*4*H^4 + 43 * H^4"
    using linear_le_pow by simp
  also have "... \<le> 79*H^4 + 133 * 9*H^3 * (nlength (Suc idx))^2 + 133*4*H^4 + 43 * H^4"
    using H by simp
  also have "... = 654 * H^4 + 1197 * H^3 * (nlength (Suc idx))^2"
    by simp
  also have "... \<le> 654 * H^4 + 1197 * H^4 * (nlength (Suc idx))^2"
    using pow_mono' by simp
  also have "... \<le> 654 * H^4 * (nlength (Suc idx))^2 + 1197 * H^4 * (nlength (Suc idx))^2"
    using nlength_mono nlength_1_simp
    by (metis add_le_mono1 le_add1 mult_le_mono2 mult_numeral_1_right numerals(1) one_le_power plus_1_eq_Suc)
  also have "... = 1851 * H^4 * (nlength (Suc idx))^2"
    by simp
  finally have "?ttt \<le> 1851 * H^4 * (nlength (Suc idx))^2" .
  then show ?thesis
    using assms tm5 transforms_monotone tps5'_eq_tps5 by simp
qed

end  (* context *)

end  (* locale turing_machine_Psigamma *)

lemma transforms_tm_PsigammaI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt H k idx \<kappa> :: nat
  assumes "length tps = k" and "0 < j" and "j + 7 < k"
    and "H \<ge> 3"
    and "\<kappa> \<le> H"
  assumes
    "tps ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>\<kappa>\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 6) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 7) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 1851 * H^4 * (nlength (Suc idx))^2"
  assumes "tps' = tps
    [j + 6 := (\<lfloor>nll_Psi (idx * H) H \<kappa>\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
  shows "transforms (tm_Psigamma j) tps ttt tps'"
proof -
  interpret loc: turing_machine_Psigamma j .
  show ?thesis
    using loc.tm5' loc.tps5'_def loc.tm5_eq_tm_Psigamma assms by simp
qed


section \<open>A Turing machine for $\Upsilon$ formulas\<close>

text \<open>
The CNF formula $\Phi_7$ is made of CNF formulas $\Upsilon(\gamma_i)$ with
$\gamma_i = [i\cdot H, (i+1)\cdot H)$. In this section we build a Turing machine
that outputs such CNF formulas.
\<close>


subsection \<open>A Turing machine for singleton clauses\<close>

text \<open>
The $\Upsilon$ formulas, just like the $\Psi$ formulas, are conjunctions of
singleton clauses. The next Turing machine outputs singleton clauses. The Turing
machine has two parameters: a Boolean $incr$ and a tape index $j$. It receives a
variable index on tape $j$, a CNF formula as list of lists of numbers on tape $j
+ 2$ and a number $H$ on tape $j + 3$. The TM appends to the formula on tape $j
+ 2$ a singleton clause with a positive or negative (depending on $incr$)
literal derived from the variable index. It also decrements $H$ and increments
the variable index, which makes it more suitable for use in a loop constructing
an $\Upsilon$ formula.

Given our encoding of literals, what the TM actually does is doubling the number
on tape $j + 1$ and optionally (if $incr$ is true) incrementing it.
\<close>

definition tm_times2_appendl :: "bool \<Rightarrow> tapeidx \<Rightarrow> machine" where
 "tm_times2_appendl incr j \<equiv>
    tm_copyn j (j + 1) ;;
    tm_times2 (j + 1) ;;
    (if incr then tm_incr (j + 1) else []) ;;
    tm_to_list (j + 1) ;;
    tm_appendl (j + 2) (j + 1) ;;
    tm_erase_cr (j + 1) ;;
    tm_incr j ;;
    tm_decr (j + 3)"

lemma tm_times2_appendl_tm:
  assumes "0 < j" and "j + 3 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_times2_appendl incr j)"
  unfolding tm_times2_appendl_def
  using Nil_tm tm_incr_tm tm_to_list_tm tm_appendl_tm tm_decr_tm tm_erase_cr_tm tm_times2_tm assms tm_copyn_tm
  by simp

locale turing_machine_times2_appendl =
  fixes j :: tapeidx
begin

context
  fixes tps0 :: "tape list" and v H k :: nat and nss :: "nat list list" and incr :: bool
  assumes jk: "length tps0 = k" "0 < j" "j + 3 < k"
  assumes tps0:
    "tps0 ! j = (\<lfloor>v\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 2) = nlltape nss"
    "tps0 ! (j + 3) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
begin

definition "tm1 \<equiv> tm_copyn j (j + 1)"
definition "tm2 \<equiv> tm1 ;; tm_times2 (j + 1)"
definition "tm3 \<equiv> tm2 ;; (if incr then tm_incr (j + 1) else [])"
definition "tm4 \<equiv> tm3 ;; tm_to_list (j + 1)"
definition "tm5 \<equiv> tm4 ;; tm_appendl (j + 2) (j + 1)"
definition "tm6 \<equiv> tm5 ;; tm_erase_cr (j + 1)"
definition "tm7 \<equiv> tm6 ;; tm_incr j"
definition "tm8 \<equiv> tm7 ;; tm_decr (j + 3)"

lemma tm8_eq_tm_times2appendl: "tm8 \<equiv> tm_times2_appendl incr j"
  using tm8_def tm7_def tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_times2_appendl_def by simp

definition "tps1 \<equiv> tps0
  [j + 1 := (\<lfloor>v\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 14 + 3 * nlength v"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def tps0 jk)
  show "tps0 ! (j + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using jk tps0 canrepr_0 by simp
  show "ttt = 14 + 3 * (nlength v + nlength 0)"
    using assms by simp
qed

definition "tps2 \<equiv> tps0
  [j + 1 := (\<lfloor>2 * v\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 19 + 5 * nlength v"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: tps2_def tps1_def jk assms)

definition "tps3 \<equiv> tps0
  [j + 1 := (\<lfloor>2 * v + (if incr then 1 else 0)\<rfloor>\<^sub>N, 1)]"

lemma tm3_True:
  assumes "ttt = 24 + 5 * nlength v + 2 * nlength (2 * v)" and incr
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps3_def tps2_def jk)
  let ?t = "5 + 2 * nlength (2 * v)"
  have "transforms (tm_incr (j + 1)) tps2 ?t tps3"
    by (tform tps: tps3_def tps2_def jk assms(2))
  then show "transforms (if incr then tm_incr (j + 1) else []) tps2 ?t tps3"
    using assms(2) by simp
  show "ttt = 19 + 5 * nlength v + ?t"
    using assms by simp
qed

lemma tm3_False:
  assumes "ttt = 19 + 5 * nlength v" and "\<not> incr"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps3_def tps2_def jk assms)
  show "transforms (if incr then tm_incr (j + 1) else []) tps2 0 tps3"
    using transforms_Nil jk tps3_def tps2_def assms(2) by simp
qed

lemma tm3:
  assumes "ttt = 24 + 5 * nlength v + 2 * nlength (2 * v)"
  shows "transforms tm3 tps0 ttt tps3"
  using tm3_True tm3_False assms transforms_monotone by (cases incr) simp_all

lemma tm3' [transforms_intros]:
  assumes "ttt = 26 + 7 * nlength v"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  have "nlength (2 * v) \<le> Suc (nlength v)"
    using nlength_times2 by simp
  then show ?thesis
    using assms tm3 transforms_monotone by simp
qed

definition "tps4 \<equiv> tps0
  [j + 1 := (\<lfloor>[2 * v + (if incr then 1 else 0)]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm4:
  assumes "ttt = 31 + 7 * nlength v + 2 * nlength (2 * v + (if incr then 1 else 0))"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: tps4_def tps3_def jk assms)

lemma tm4' [transforms_intros]:
  assumes "ttt = 33 + 9 * nlength v"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  have "nlength (2 * v + (if incr then 1 else 0)) \<le> Suc (nlength v)"
    using nlength_times2 nlength_times2plus1 by simp
  then show ?thesis
    using assms tm4 transforms_monotone by simp
qed

definition "tps5 \<equiv> tps0
  [j + 1 := (\<lfloor>[2 * v + (if incr then 1 else 0)]\<rfloor>\<^sub>N\<^sub>L, 1),
   j + 2 := nlltape (nss @ [[2 * v + (if incr then 1 else 0)]])]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 39 + 9 * nlength v + 2 * nllength [2 * v + (if incr then 1 else 0)]"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: tps5_def tps4_def jk tps0)
  show "ttt = 33 + 9 * nlength v + (7 + nlllength nss - Suc (nlllength nss) +
      2 * nllength [2 * v + (if incr then 1 else 0)])"
    using assms by simp
qed

definition "tps6 \<equiv> tps0
  [j + 2 := nlltape (nss @ [[2 * v + (if incr then 1 else 0)]])]"

lemma tm6:
  assumes "ttt = 46 + 9 * nlength v + 4 * nllength [2 * v + (if incr then 1 else 0)]"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: tps6_def tps5_def jk)
  let ?zs = "numlist [2 * v + (if incr then 1 else 0)]"
  show "tps5 ::: (j + 1) = \<lfloor>?zs\<rfloor>"
    using jk tps5_def nlcontents_def by simp
  show "proper_symbols ?zs"
    using proper_symbols_numlist by simp
  show "tps6 = tps5[j + 1 := (\<lfloor>[]\<rfloor>, 1)]"
    using jk tps6_def tps5_def tps0
    by (metis (no_types, lifting) add_left_cancel list_update_id list_update_overwrite list_update_swap
      numeral_eq_one_iff semiring_norm(83))
  show "ttt = 39 + 9 * nlength v + 2 * nllength [2 * v + (if incr then 1 else 0)] +
      (tps5 :#: (j + 1) + 2 * length (numlist [2 * v + (if incr then 1 else 0)]) + 6)"
    using assms nllength_def tps5_def jk by simp
qed

lemma tm6' [transforms_intros]:
  assumes "ttt = 54 + 13 * nlength v"
  shows "transforms tm6 tps0 ttt tps6"
proof -
  have "nlength (2 * v + (if incr then 1 else 0)) \<le> Suc (nlength v)"
    using nlength_times2 nlength_times2plus1 by simp
  then show ?thesis
    using assms tm6 transforms_monotone nllength by simp
qed

definition "tps7 \<equiv> tps0
  [j := (\<lfloor>Suc v\<rfloor>\<^sub>N, 1),
   j + 2 := nlltape (nss @ [[2 * v + (if incr then 1 else 0)]])]"

lemma tm7 [transforms_intros]:
  assumes "ttt = 59 + 15 * nlength v"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform tps: tps7_def tps6_def tps0 jk assms)

definition "tps8 \<equiv> tps0
  [j := (\<lfloor>Suc v\<rfloor>\<^sub>N, 1),
   j + 2 := nlltape (nss @ [[2 * v + (if incr then 1 else 0)]]),
   j + 3 := (\<lfloor>H - 1\<rfloor>\<^sub>N, 1)]"

lemma tm8:
  assumes "ttt = 67 + 15 * nlength v + 2 * nlength H"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def by (tform tps: tps8_def tps0 tps7_def jk time: assms)

end

end  (* locale turing_machine_times2_appendl *)

lemma transforms_tm_times2_appendlI [transforms_intros]:
  fixes j :: tapeidx and incr :: bool
  fixes tps tps' :: "tape list" and ttt v H k :: nat and nss :: "nat list list"
  assumes "length tps = k" and "0 < j" and "j + 3 < k"
  assumes
    "tps ! j = (\<lfloor>v\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 2) = nlltape nss"
    "tps ! (j + 3) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 67 + 15 * nlength v + 2 * nlength H"
  assumes "tps' = tps
    [j := (\<lfloor>Suc v\<rfloor>\<^sub>N, 1),
     j + 2 := nlltape (nss @ [[2 * v + (if incr then 1 else 0)]]),
     j + 3 := (\<lfloor>H - 1\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_times2_appendl incr j) tps ttt tps'"
proof -
  interpret loc: turing_machine_times2_appendl j .
  show ?thesis
    using assms loc.tm8 loc.tps8_def loc.tm8_eq_tm_times2appendl by metis
qed


subsection \<open>A Turing machine for $\Upsilon(\gamma_i)$ formulas\<close>

text \<open>
We will not need the general $\Upsilon$ formulas, but only $\Upsilon(\gamma_i)$
for $\gamma_i = [i\cdot H, (i + 1)\cdot H)$. Represented as list of lists of
numbers they look like this (for $H \geq 3$):
\<close>

definition nll_Upsilon :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "nll_Upsilon idx len \<equiv> [[2 * (idx * len) + 1], [2 * (idx * len + 1) + 1]] @ map (\<lambda>i. [2 * (idx * len + i)]) [3..<len]"

lemma nll_Upsilon:
  assumes "len \<ge> 3"
  shows "nll_Upsilon idx len = formula_n (\<Upsilon> [idx*len..<idx*len+len])"
    (is "?lhs = ?rhs")
proof (rule nth_equalityI)
  show len: "length ?lhs = length ?rhs"
    using nll_Upsilon_def Upsilon_def formula_n_def assms by simp
  have "length ?lhs = len - 1"
    using nll_Upsilon_def assms by simp
  define nss where "nss = [[2 * (idx * len) + 1], [2 * (idx * len + 1) + 1]]"
  then have *: "?lhs = nss @ map (\<lambda>i. [2 * (idx * len + i)]) [3..<len]"
    using nll_Upsilon_def by simp
  have "length nss = 2"
    using nss_def by simp
  let ?ups = "\<Upsilon> [idx*len..<idx*len+len]"
  show "?lhs ! i = ?rhs ! i" if "i < length ?lhs" for i
  proof (cases "i < 2")
    case True
    then have "?lhs ! i = nss ! i"
      using * `length nss = 2` by (simp add: nth_append)
    then have lhs: "?lhs ! i = [2 * (idx * len + i) + 1]"
      using nss_def True by (cases "i = 0") auto

    have "?ups ! i = [Pos (idx*len+i)]"
      unfolding Upsilon_def using True assms by (cases "i = 0") auto
    moreover have "?rhs ! i = clause_n (?ups ! i)"
      using that len formula_n_def by simp
    ultimately have "?rhs ! i = clause_n [Pos (idx*len+i)]"
      by simp
    then have "?rhs ! i = [Suc (2*(idx*len+i))]"
      using clause_n_def by simp
    then show ?thesis
      using lhs by simp
  next
    case False
    then have "?lhs ! i = map (\<lambda>i. [2 * (idx * len + i)]) [3..<len] ! (i - 2)"
      using `length nss = 2` * by (simp add: nth_append)
    also have "... = (\<lambda>i. [2 * (idx * len + i)]) ([3..<len] ! (i - 2))"
      using False that `length nss = 2` * by simp
    also have "... = (\<lambda>i. [2 * (idx * len + i)]) (i + 1)"
      using False that `length nss = 2` * by simp
    also have "... = [2 * (idx * len + i + 1)]"
      by simp
    finally have lhs: "?lhs ! i = [2 * (idx * len + i + 1)]" .

    have "?ups ! i = map (\<lambda>s. [Neg s]) (drop 3 [idx*len..<idx*len+len]) ! (i - 2)"
      using Upsilon_def False that formula_n_def len by auto
    also have "... = (\<lambda>s. [Neg s]) (drop 3 [idx*len..<idx*len+len] ! (i - 2))"
      using Upsilon_def False that formula_n_def len by auto
    also have "... = (\<lambda>s. [Neg s]) (idx * len + i + 1)"
      using Upsilon_def False that formula_n_def len by auto
    finally have "?ups ! i = [Neg (idx * len + i + 1)]" .
    moreover have "?rhs ! i = clause_n (?ups ! i)"
      using Upsilon_def False that formula_n_def len by auto
    ultimately have "?rhs ! i = clause_n [Neg (idx * len + i + 1)]"
      by simp
    then show ?thesis
      using clause_n_def lhs by simp
  qed
qed

lemma nlllength_nll_Upsilon_le:
  assumes "len \<ge> 3"
  shows "nlllength (nll_Upsilon idx len) \<le> len * (4 + nlength idx + nlength len)"
proof -
  define f :: "nat \<Rightarrow> nat list" where "f = (\<lambda>i. [2 * (idx * len + i)])"
  let ?nss = "map f [3..<len]"
  have "nlllength ?nss = (\<Sum>ns\<leftarrow>?nss. Suc (nllength ns))"
    using nlllength f_def by simp
  also have "... = (\<Sum>i\<leftarrow>[3..<len]. (\<lambda>ns. Suc (nllength ns)) (f i))"
    by (metis (no_types, lifting) map_eq_conv map_map o_apply)
  also have "... = (\<Sum>i\<leftarrow>[3..<len]. Suc (nllength ([2 * (idx * len + i)])))"
    using f_def by simp
  also have "... = (\<Sum>i\<leftarrow>[3..<len]. Suc (Suc (nlength (2 * (idx * len + i)))))"
    using nllength by simp
  also have "... \<le> (\<Sum>i\<leftarrow>[3..<len]. Suc (Suc (nlength (2 * (Suc idx * len)))))"
    using nlength_mono
      sum_list_mono[of "[3..<len]"
        "\<lambda>i. Suc (Suc (nlength (2 * (idx * len + i))))"
        "\<lambda>i. Suc (Suc (nlength (2 * (Suc idx * len))))"]
    by simp
  also have "... = Suc (Suc (nlength (2 * (Suc idx * len)))) * (len - 3)"
    using assms sum_list_const[of _ "[3..<len]"] by simp
  also have "... \<le> Suc (Suc (Suc (nlength (Suc idx * len)))) * (len - 3)"
    using nlength_times2 Suc_le_mono mult_le_mono1 by presburger
  also have "... = (len - 3) * (3 + nlength (Suc idx * len))"
    by (simp add: Suc3_eq_add_3)
  finally have *: "nlllength ?nss \<le> (len - 3) * (3 + nlength (Suc idx * len))" .

  let ?nss2 = "[[2 * (idx * len) + 1], [2 * (idx * len + 1) + 1]]"
  have "nlllength ?nss2 = (\<Sum>ns\<leftarrow>?nss2. Suc (nllength ns))"
    using nlllength by simp
  also have "... = Suc (nllength [2 * (idx * len) + 1]) + Suc (nllength [2 * (idx * len + 1) + 1])"
    by simp
  also have "... = Suc (Suc (nlength (2 * (idx * len) + 1))) + Suc (Suc (nlength (2 * (idx * len + 1) + 1)))"
    using nllength by simp
  also have "... \<le> Suc (Suc (nlength (2 * (Suc idx * len)))) + Suc (Suc (nlength (2 * (idx * len + 1) + 1)))"
    using nlength_mono assms by simp
  also have "... \<le> Suc (Suc (nlength (2 * (Suc idx * len)))) + Suc (Suc (nlength (2 * (Suc idx * len))))"
    using nlength_mono assms by simp
  also have "... = 2 * Suc (Suc (nlength (2 * (Suc idx * len))))"
    by simp
  also have "... \<le> 2 * Suc (Suc (Suc (nlength (Suc idx * len))))"
    using nlength_times2 by (meson Suc_le_mono mult_le_mono nle_le)
  also have "... = 2 * (3 + nlength (Suc idx * len))"
    by simp
  finally have **: "nlllength ?nss2 \<le> 2 * (3 + nlength (Suc idx * len))" .

  have "nll_Upsilon idx len = ?nss2 @ ?nss"
    using nll_Upsilon_def f_def by simp
  then have "nlllength (nll_Upsilon idx len) = nlllength ?nss2 + nlllength ?nss"
    by (metis length_append nlllength_def numlistlist_append)
  then have "nlllength (nll_Upsilon idx len) \<le> 2 * (3 + nlength (Suc idx * len)) + (len - 3) * (3 + nlength (Suc idx * len))"
    using * ** by simp
  also have "... = (2 + (len - 3)) * (3 + nlength (Suc idx * len))"
    by simp
  also have "... = (len - 1) * (3 + nlength (Suc idx * len))"
    using assms Nat.le_imp_diff_is_add by fastforce
  also have "... \<le> len * (3 + nlength (Suc idx * len))"
    by simp
  also have "... \<le> len * (3 + nlength (Suc idx) + nlength len)"
    using nlength_prod by (metis ab_semigroup_add_class.add_ac(1) mult_le_mono2 nat_add_left_cancel_le)
  also have "... \<le> len * (4 + nlength idx + nlength len)"
    using nlength_Suc by simp
  finally show ?thesis .
qed

text \<open>
The next Turing machine outputs CNF formulas of the shape $\Upsilon(\gamma_i)$,
where $\gamma_i = [i\cdot H, (i+1)\cdot H)$. It expects a number $i$ on tape $j$
and a number $H$ on tape $j + 1$. It writes a representation of the formula to
tape $j + 4$.
\<close>

definition tm_Upsilongamma :: "tapeidx \<Rightarrow> machine" where
  "tm_Upsilongamma j \<equiv>
    tm_copyn (j + 1) (j + 5) ;;
    tm_mult j (j + 1) (j + 2) ;;
    tm_times2_appendl True (j + 2) ;;
    tm_times2_appendl True (j + 2) ;;
    tm_decr (j + 5) ;;
    tm_incr (j + 2) ;;
    WHILE [] ; \<lambda>rs. rs ! (j + 5) \<noteq> \<box> DO
      tm_times2_appendl False (j + 2)
    DONE ;;
    tm_erase_cr (j + 2) ;;
    tm_cr (j + 4)"

lemma tm_Upsilongamma_tm:
  assumes "0 < j" and "j + 5 < k" and "G \<ge> 6"
  shows "turing_machine k G (tm_Upsilongamma j)"
  unfolding tm_Upsilongamma_def
  using tm_copyn_tm Nil_tm tm_decr_tm tm_times2_appendl_tm tm_decr_tm tm_mult_tm tm_incr_tm
    assms turing_machine_loop_turing_machine tm_erase_cr_tm tm_cr_tm
  by simp

locale turing_machine_Upsilongamma =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_copyn (j + 1) (j + 5)"
definition "tm2 \<equiv> tm1 ;; tm_mult j (j + 1) (j + 2)"
definition "tm3 \<equiv> tm2 ;; tm_times2_appendl True (j + 2)"
definition "tm4 \<equiv> tm3 ;; tm_times2_appendl True (j + 2)"
definition "tm5 \<equiv> tm4 ;; tm_decr (j + 5)"
definition "tm6 \<equiv> tm5 ;; tm_incr (j + 2)"
definition "tmB \<equiv> tm_times2_appendl False (j + 2)"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! (j + 5) \<noteq> \<box> DO tmB DONE"
definition "tm7 \<equiv> tm6 ;; tmL"
definition "tm8 \<equiv> tm7 ;; tm_erase_cr (j + 2)"
definition "tm9 \<equiv> tm8 ;; tm_cr (j + 4)"

lemma tm9_eq_tm_Upsilongamma: "tm9 = tm_Upsilongamma j"
  using tm9_def tm8_def tm7_def tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tmB_def tmL_def tm_Upsilongamma_def
  by simp

context
  fixes tps0 :: "tape list" and idx H k :: nat
  assumes jk: "length tps0 = k" "0 < j" "j + 5 < k"
    and H: "H \<ge> 3"
  assumes tps0:
    "tps0 ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps0 ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j + 5 := (\<lfloor>H\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 14 + 3 * nlength H"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def tps0 jk)
  show "tps0 ! (j + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using jk tps0 canrepr_0 by simp
  show "ttt = 14 + 3 * (nlength H + nlength 0)"
    using assms by simp
qed

definition "tps2 \<equiv> tps0
  [j + 5 := (\<lfloor>H\<rfloor>\<^sub>N, 1),
   j + 2 := (\<lfloor>idx * H\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 18 + 3 * nlength H + 26 * (nlength idx + nlength H)^2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps2_def tps1_def jk tps0)
  show "tps1 ! (j + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps1_def jk canrepr_1 tps0
    by (metis add_left_imp_eq canrepr_0 nth_list_update_neq' numeral_eq_iff semiring_norm(89))
  show "ttt = 14 + 3 * nlength H + (4 + 26 * (nlength idx + nlength H) * (nlength idx + nlength H))"
    using assms by algebra
qed

definition "tps3 \<equiv> tps0
  [j + 5 := (\<lfloor>H - 1\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1]]),
   j + 2 := (\<lfloor>idx * H + 1\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 85 + 5 * nlength H + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H)"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps3_def tps2_def jk tps0)
  have *: "j + 2 + 1 = j + 3" "j + 2 + 2 = j + 4" "j + 2 + 3 = j + 5"
    by simp_all
  show "tps2 ! (j + 2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
    using jk tps2_def tps0 by (simp only: *) simp
  show "tps2 ! (j + 2 + 2) = nlltape []"
    using jk tps2_def tps0 nllcontents_Nil by (simp only: *) simp
  show "tps2 ! (j + 2 + 3) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    using jk tps2_def tps0 by (simp only: *) simp
  show "tps3 = tps2
    [j + 2 := (\<lfloor>Suc (idx * H)\<rfloor>\<^sub>N, 1),
     j + 2 + 2 := nlltape ([] @ [[2 * (idx * H) + (if True then 1 else 0)]]),
     j + 2 + 3 := (\<lfloor>H - 1\<rfloor>\<^sub>N, 1)]"
    unfolding tps3_def tps2_def
    by (simp only: *) (simp add: list_update_swap[of "Suc (Suc j)"] list_update_swap_less[of "j+4"])
  show "ttt = 18 + 3 * nlength H + 26 * (nlength idx + nlength H)\<^sup>2 +
      (67 + 15 * nlength (idx * H) + 2 * nlength H)"
    using assms by simp
qed

definition "tps4 \<equiv> tps0
  [j + 5 := (\<lfloor>H - 2\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]]),
   j + 2 := (\<lfloor>idx * H + 2\<rfloor>\<^sub>N, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 152 + 5 * nlength H + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps4_def tps3_def jk tps0)
  have *: "j + 2 + 1 = j + 3" "j + 2 + 2 = j + 4" "j + 2 + 3 = j + 5"
    by simp_all
  show "tps3 ! (j + 2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
    using jk tps3_def tps0 by (simp only: *) simp
  show "tps3 ! (j + 2 + 2) = nlltape [[2 * (idx * H) + 1]]"
    using jk tps3_def tps0 by (simp only: *) simp
  show "tps3 ! (j + 2 + 3) = (\<lfloor>H - 1\<rfloor>\<^sub>N, 1)"
    using jk tps3_def tps0 by (simp only: *) simp
  have 2: "2 = Suc (Suc 0)"
    by simp
  show "tps4 = tps3
    [j + 2 := (\<lfloor>Suc (Suc (idx * H))\<rfloor>\<^sub>N, 1),
     j + 2 + 2 := nlltape ([[2 * (idx * H) + 1]] @ [[2 * Suc (idx * H) + (if True then 1 else 0)]]),
     j + 2 + 3 := (\<lfloor>H - 1 - 1\<rfloor>\<^sub>N, 1)]"
    unfolding tps4_def tps3_def by (simp only: *) (simp add: 2 list_update_swap)
  show "ttt = 85 + 5 * nlength H + 26 * (nlength idx + nlength H)\<^sup>2 + 15 * nlength (idx * H) +
      (67 + 15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1))"
    using assms by simp
qed

definition "tps5 \<equiv> tps0
  [j + 5 := (\<lfloor>H - 3\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]]),
   j + 2 := (\<lfloor>idx * H + 2\<rfloor>\<^sub>N, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 160 + 5 * nlength H + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1) + 2 * nlength (H - 2)"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: tps5_def tps4_def jk tps0)
  show "ttt = 152 + 5 * nlength H + 26 * (nlength idx + nlength H)\<^sup>2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1) + (8 + 2 * nlength (H - 2)) "
    using assms by simp
qed

definition "tps6 \<equiv> tps0
  [j + 5 := (\<lfloor>H - 3\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]]),
   j + 2 := (\<lfloor>idx * H + 3\<rfloor>\<^sub>N, 1)]"

lemma tm6:
  assumes "ttt = 165 + 5 * nlength H + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1) + 2 * nlength (H - 2) +
      2 * nlength (Suc (Suc (idx * H)))"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: tps6_def tps5_def jk tps0)
  show "tps6 = tps5[j + 2 := (\<lfloor>Suc (Suc (Suc (idx * H)))\<rfloor>\<^sub>N, 1)]"
    unfolding tps5_def tps6_def
    by (simp only: One_nat_def Suc_1 add_2_eq_Suc' add_Suc_right numeral_3_eq_3) (simp add: list_update_swap)
  show "ttt = 160 + 5 * nlength H + 26 * (nlength idx + nlength H)\<^sup>2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1) + 2 * nlength (H - 2) +
      (5 + 2 * nlength (Suc (Suc (idx * H))))"
    using assms by simp
qed

lemma tm6' [transforms_intros]:
  assumes "ttt = 165 + 41 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2"
  shows "transforms tm6 tps0 ttt tps6"
proof -
  let ?ttt = "165 + 5 * nlength H + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1) + 2 * nlength (H - 2) +
      2 * nlength (Suc (Suc (idx * H)))"
  have "?ttt \<le> 165 + 5 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (H - 1) + 2 * nlength (H - 2) +
      2 * nlength (Suc (Suc (idx * H)))"
    using nlength_mono by simp
  also have "... \<le> 165 + 5 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (Suc idx * H) + 2 * nlength (H - 2) +
      2 * nlength (Suc (Suc (idx * H)))"
    using nlength_mono by simp
  also have "... \<le> 165 + 5 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2 + 15 * nlength (idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H) +
      2 * nlength (Suc (Suc (idx * H)))"
    using nlength_mono by simp
  also have "... \<le> 165 + 5 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2 + 15 * nlength (Suc idx * H) +
      15 * nlength (Suc (idx * H)) + 2 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H) +
      2 * nlength (Suc (Suc (idx * H)))"
    using nlength_mono by simp
  also have "... \<le> 165 + 5 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2 + 15 * nlength (Suc idx * H) +
      15 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H) +
      2 * nlength (Suc (Suc (idx * H)))"
    using nlength_mono H by simp
  also have "... \<le> 165 + 5 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2 + 15 * nlength (Suc idx * H) +
      15 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H) +
      2 * nlength (Suc idx * H)"
    using nlength_mono H by simp
  also have "... = 165 + 41 * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)^2"
    using nlength_mono by simp
  finally have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm6 transforms_monotone by simp
qed

definition "tpsL t \<equiv> tps0
  [j + 5 := (\<lfloor>H - 3 - t\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<3 + t]),
   j + 2 := (\<lfloor>idx * H + 3 + t\<rfloor>\<^sub>N, 1)]"

lemma tpsL_eq_tps6: "tpsL 0 = tps6"
  using tpsL_def tps6_def by simp

lemma map_Suc_append: "a \<le> b \<Longrightarrow> map f [a..<Suc b] = map f [a..<b] @ [f b]"
  by simp

lemma tmB:
  assumes "ttt = 67 + 15 * nlength (idx * H + 3 + t) + 2 * nlength (H - 3 - t)"
  shows "transforms tmB (tpsL t) ttt (tpsL (Suc t))"
  unfolding tmB_def
proof (tform tps: tpsL_def jk tps0)
  have *: "j + 2 + 1 = j + 3" "j + 2 + 2 = j + 4" "j + 2 + 3 = j + 5"
    by simp_all
  show "tpsL t ! (j + 2 + 1) = (\<lfloor>[]\<rfloor>, 1)"
    using jk tpsL_def tps0 by (simp only: *) simp
  let ?nss = "[[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<3 + t]"
  show "tpsL t ! (j + 2 + 2) = nlltape ?nss"
    using jk tpsL_def by (simp only: *) simp
  show "tpsL t ! (j + 2 + 3) = (\<lfloor>H - 3 - t\<rfloor>\<^sub>N, 1)"
    using jk tpsL_def by (simp only: *) simp
  have "map (\<lambda>i. [2 * (idx * H + i)]) [3..<3 + Suc t] =
      map (\<lambda>i. [2 * (idx * H + i)]) [3..<3 + t] @ [[2 * (idx * H + 3 + t) + (if False then 1 else 0)]]"
    using map_Suc_append[of "3" "3 + t" "\<lambda>i. [2 * (idx * H + i)]"] by simp
  then have "[[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<3 + Suc t] =
      ?nss @ [[2 * (idx * H + 3 + t) + (if False then 1 else 0)]]"
    by simp
  then show "tpsL (Suc t) = (tpsL t)
    [j + 2 := (\<lfloor>Suc (idx * H + 3 + t)\<rfloor>\<^sub>N, 1),
     j + 2 + 2 := nlltape (?nss @ [[2 * (idx * H + 3 + t) + (if False then 1 else 0)]]),
     j + 2 + 3 := (\<lfloor>H - 3 - t - 1\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL_def
    by (simp only: *) (simp add: list_update_swap[of "Suc (Suc j)"] list_update_swap_less[of "j + 4"])
  show "ttt = 67 + 15 * nlength (idx * H + 3 + t) + 2 * nlength (H - 3 - t)"
    using assms by simp
qed

lemma tmB' [transforms_intros]:
  assumes "ttt = 67 + 15 * nlength (Suc idx * H) + 2 * nlength H"
    and "t < H - 3"
  shows "transforms tmB (tpsL t) ttt (tpsL (Suc t))"
proof -
  let ?ttt = "67 + 15 * nlength (idx * H + 3 + t) + 2 * nlength (H - 3 - t)"
  have "?ttt \<le> 67 + 15 * nlength (idx * H + 3 + t) + 2 * nlength H"
    using nlength_mono by simp
  also have "... \<le> 67 + 15 * nlength (Suc idx * H) + 2 * nlength H"
    using assms(2) nlength_mono by simp
  finally have "?ttt \<le> ttt"
    using assms(1) by simp
  then show ?thesis
    using tmB transforms_monotone by blast
qed

lemma tmL:
  assumes "ttt = H * (70 + 17 * nlength (Suc idx * H))"
  shows "transforms tmL (tpsL 0) ttt (tpsL (H - 3))"
  unfolding tmL_def
proof (tform)
  have "read (tpsL t) ! (j + 5) = \<box> \<longleftrightarrow> H - 3 - t = 0" for t
    using jk tpsL_def read_ncontents_eq_0 by simp
  then show "\<And>t. t < H - 3 \<Longrightarrow> read (tpsL t) ! (j + 5) \<noteq> \<box>"
      and "\<not> read (tpsL (H - 3)) ! (j + 5) \<noteq> \<box>"
    by simp_all
  show "(H - 3) * (67 + 15 * nlength (Suc idx * H) + 2 * nlength H + 2) + 1 \<le> ttt"
    (is "?lhs \<le> ttt")
  proof -
    have "?lhs = (H - 3) * (69 + 15 * nlength (Suc idx * H) + 2 * nlength H) + 1"
      by simp
    also have "... \<le> (H - 3) * (69 + 15 * nlength (Suc idx * H) + 2 * nlength (Suc idx * H)) + 1"
      using nlength_mono by simp
    also have "... = (H - 3) * (69 + 17 * nlength (Suc idx * H)) + 1"
      by simp
    also have "... \<le> H * (69 + 17 * nlength (Suc idx * H)) + 1"
      by simp
    also have "... \<le> H * (69 + 17 * nlength (Suc idx * H)) + H"
      using H by simp
    also have "... = H * (70 + 17 * nlength (Suc idx * H))"
      by algebra
    finally show "?lhs \<le> ttt"
      using assms by simp
  qed
qed

definition "tps7 \<equiv> tps0
  [j + 5 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<H]),
   j + 2 := (\<lfloor>Suc idx * H\<rfloor>\<^sub>N, 1)]"

lemma tpsL_eq_tps7: "tpsL (H - 3) = tps7"
proof -
  let ?t = "H - 3"
  have "(\<lfloor>H - 3 - ?t\<rfloor>\<^sub>N, 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by simp
  moreover have "nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<3 + ?t]) =
      nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<H])"
    using H by simp
  moreover have "(\<lfloor>idx * H + 3 + ?t\<rfloor>\<^sub>N, 1) = (\<lfloor>Suc idx * H\<rfloor>\<^sub>N, 1)"
    using H by (simp add: add.commute)
  ultimately show ?thesis
    using tpsL_def tps7_def by simp
qed

lemma tmL' [transforms_intros]:
  assumes "ttt = H * (70 + 17 * nlength (Suc idx * H))"
  shows "transforms tmL tps6 ttt tps7"
  using tmL tpsL_eq_tps6 tpsL_eq_tps7 assms by simp

lemma tm7 [transforms_intros]:
  assumes "ttt = 165 + 41 * nlength (H + idx * H) + 26 * (nlength idx + nlength H)\<^sup>2 +
      H * (70 + 17 * nlength (H + idx * H))"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform tps: tps7_def tpsL_def jk tps0 time: assms)

definition "tps8 \<equiv> tps0
  [j + 5 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
   j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<H]),
   j + 2 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm8:
  assumes "ttt = 172 + 43 * nlength (H + idx * H) + 26 * (nlength idx + nlength H)\<^sup>2 +
      H * (70 + 17 * nlength (H + idx * H))"
  shows "transforms tm8 tps0 ttt tps8"
  unfolding tm8_def
proof (tform tps: tps8_def tps7_def jk tps0 assms)
  show "proper_symbols (canrepr (H + idx * H))"
    using proper_symbols_canrepr by simp
qed

definition "tps8' \<equiv> tps0[j + 4 := nlltape (nll_Upsilon idx H)]"

lemma tps8'_eq_tps8: "tps8' = tps8"
proof -
  define tps where "tps = tps0
    [j + 4 := nlltape ([[2 * (idx * H) + 1], [2 * (idx * H + 1) + 1]] @ map (\<lambda>i. [2 * (idx * H + i)]) [3..<H])]"
  then have "tps = tps8"
    using jk tps8_def canrepr_0 tps0
    by (smt (verit, best) add_left_imp_eq arith_simps(4) list_update_id list_update_swap num.simps(2) numeral_eq_iff semiring_norm(83))
  then show ?thesis
    using nll_Upsilon_def tps8'_def tps_def by simp
qed

lemma tm8' [transforms_intros]:
  assumes "ttt = 199 * H * (nlength idx + nlength H)^2"
  shows "transforms tm8 tps0 ttt tps8'"
proof -
  let ?ttt = "172 + 43 * nlength (H + idx * H) + 26 * (nlength idx + nlength H)\<^sup>2 +
      H * (70 + 17 * nlength (H + idx * H))"
  have "?ttt = 172 + 43 * nlength (H + idx * H) + 26 * (nlength idx + nlength H)\<^sup>2 +
      70 * H + 17 * H * nlength (H + idx * H)"
    by algebra
  also have "... = 172 + 70 * H + (17 * H + 43) * nlength (H + idx * H) + 26 * (nlength idx + nlength H)\<^sup>2"
    by algebra
  also have "... = 172 + 70 * H + (17 * H + 43) * nlength (Suc idx * H) + 26 * (nlength idx + nlength H)\<^sup>2"
    by simp
  also have "... \<le> 172 + 70 * H + (17 * H + 43) * (nlength (Suc idx) + nlength H) + 26 * (nlength idx + nlength H)\<^sup>2"
    using nlength_prod by (meson add_le_mono mult_le_mono order_refl)
  also have "... \<le> 172 + 70 * H + (17 * H + 43) * (Suc (nlength idx) + nlength H) + 26 * (nlength idx + nlength H)\<^sup>2"
    using nlength_Suc add_le_mono le_refl mult_le_mono by presburger
  also have "... = 172 + 70 * H + (17 * H + 43) + (17 * H + 43) * (nlength idx + nlength H) + 26 * (nlength idx + nlength H)\<^sup>2"
    by simp
  also have "... = 215 + 87 * H + (17 * H + 43) * (nlength idx + nlength H) + 26 * (nlength idx + nlength H)\<^sup>2"
    by simp
  also have "... \<le> 215 + 87 * H + (17 * H + 43) * (nlength idx + nlength H)^2 + 26 * (nlength idx + nlength H)\<^sup>2"
    using linear_le_pow by simp
  also have "... = 215 + 87 * H + (17 * H + 69) * (nlength idx + nlength H)^2"
    by algebra
  also have "... \<le> 159 * H + (17 * H + 69) * (nlength idx + nlength H)^2"
    using H by simp
  also have "... \<le> 159 * H + 40 * H * (nlength idx + nlength H)^2"
    using H by simp
  also have "... \<le> 199 * H * (nlength idx + nlength H)^2"
  proof -
    have "nlength H > 0"
      using H nlength_0 by simp
    then have "nlength idx + nlength H \<ge> 1"
      by linarith
    then show ?thesis
      by simp
  qed
  finally have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tps8'_eq_tps8 tm8 transforms_monotone by simp
qed

definition "tps9 \<equiv> tps0
  [j + 4 := (\<lfloor>nll_Upsilon idx H\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"

lemma tm9:
  assumes "ttt = 199 * H * (nlength idx + nlength H)^2 + Suc (Suc (Suc (nlllength (nll_Upsilon idx H))))"
  shows "transforms tm9 tps0 ttt tps9"
  unfolding tm9_def
proof (tform tps: tps8'_def tps9_def jk tps0 assms)
  show "clean_tape (tps8' ! (j + 4))"
    using tps8'_def jk tps0 clean_tape_nllcontents by simp
qed

lemma tm9' [transforms_intros]:
  assumes "ttt = 205 * H * (nlength idx + nlength H)^2"
  shows "transforms tm9 tps0 ttt tps9"
proof -
  let ?ttt = "199 * H * (nlength idx + nlength H)^2 + Suc (Suc (Suc (nlllength (nll_Upsilon idx H))))"
  have "?ttt \<le> 199 * H * (nlength idx + nlength H)^2 + Suc (Suc (Suc (H * (4 + nlength idx + nlength H))))"
    using nlllength_nll_Upsilon_le H by simp
  also have "... = 199 * H * (nlength idx + nlength H)^2 + 3 + H * (4 + nlength idx + nlength H)"
    by simp
  also have "... = 199 * H * (nlength idx + nlength H)^2 + 3 + 4 * H + H * (nlength idx + nlength H)"
    by algebra
  also have "... \<le> 199 * H * (nlength idx + nlength H)^2 + 5 * H + H * (nlength idx + nlength H)"
    using H by simp
  also have "... \<le> 199 * H * (nlength idx + nlength H)^2 + 5 * H + H * (nlength idx + nlength H)^2"
    using linear_le_pow by simp
  also have "... = 200 * H * (nlength idx + nlength H)^2 + 5 * H"
    by simp
  also have "... \<le> 205 * H * (nlength idx + nlength H)^2"
  proof -
    have "nlength H \<ge> 1"
      using H nlength_0 by (metis less_one not_less not_numeral_le_zero)
    then show ?thesis
      by simp
  qed
  finally have "?ttt \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm9 transforms_monotone by simp
qed

end  (* context *)

end  (* locale turing_machine_Upsilongamma *)

lemma transforms_tm_UpsilongammaI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt idx H k :: nat
  assumes "length tps = k" and "0 < j" and "j + 5 < k"
    and "H \<ge> 3"
  assumes
    "tps ! j = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 1) = (\<lfloor>H\<rfloor>\<^sub>N, 1)"
    "tps ! (j + 2) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 3) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 4) = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! (j + 5) = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 205 * H * (nlength idx + nlength H)^2"
  assumes "tps' = tps[j + 4 := (\<lfloor>nll_Upsilon idx H\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)]"
  shows "transforms (tm_Upsilongamma j) tps ttt tps'"
proof -
  interpret loc: turing_machine_Upsilongamma j .
  show ?thesis
    using assms loc.tm9_eq_tm_Upsilongamma loc.tm9' loc.tps9_def by simp
qed

end
