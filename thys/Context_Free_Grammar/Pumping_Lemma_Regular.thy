(*
Authors: Kaan Taskin
*)

section \<open>Pumping Lemma for Strongly Right-Linear Grammars\<close>

theory Pumping_Lemma_Regular
imports NDA_rlin2 "List_Power.List_Power"
begin

text \<open>The proof is on the level of strongly right-linear grammars.
Currently there is no proof on the automaton level but now it would be easy to obtain one.\<close>

lemma not_distinct:
  assumes "m = card P"
      and "m \<ge> 1"
      and "\<forall>i < length w. w ! i \<in> P"
      and "length w \<ge> Suc m"
    shows "\<exists>xs ys zs y. w = xs @ [y] @ ys @ [y] @ zs \<and> length (xs @ [y] @ ys @ [y]) \<le> Suc m"
using assms proof (induction w arbitrary: P m rule: length_induct)
  case (1 aw)
  from "1.prems"(4) obtain a w where aw_cons[simp]: "aw = a#w" and w_len: "m \<le> length w"
    using Suc_le_length_iff[of m aw] by blast
  show ?case proof (cases "a \<in> set w")
    case True
    hence "\<not> distinct aw" by simp
    then obtain xs ys zs y where aw_split: "aw = xs @ [y] @ ys @ [y] @ zs"
      using not_distinct_decomp by blast
    show ?thesis proof (cases "length (xs @ [y] @ ys @ [y]) \<le> Suc m")
      case True
      with aw_split show ?thesis by blast
    next
      case False
      let ?xsyys = "xs @ [y] @ ys"
      from False have a4: "length ?xsyys \<ge> Suc m" by simp
      from aw_split have a5: "length ?xsyys < length aw" by simp
      with "1.prems"(3) have "\<forall>i<length ?xsyys. aw ! i \<in> P" by simp
      with aw_split have a3: "\<forall>i < length ?xsyys. ?xsyys ! i \<in> P"
        by (metis append_assoc nth_append)
      from "1.prems"(2) "1.prems"(1) a3 a4 a5 have "\<exists>xs' ys' zs' y'. ?xsyys = xs' @ [y'] @ ys' @ [y'] @ zs' \<and> length (xs' @ [y'] @ ys' @ [y']) \<le> Suc m"
        using "1.IH" by simp
      then obtain xs' ys' zs' y' where xsyys_split: "?xsyys = xs' @ [y'] @ ys' @ [y'] @ zs'" and xsyys'_len: "length (xs' @ [y'] @ ys' @ [y']) \<le> Suc m" by blast
      let ?xs = xs' let ?y = y' let ?ys = ys' let ?zs = "zs' @ [y] @ zs" 
      from xsyys_split aw_split have *: "aw = ?xs @ [?y] @ ?ys @ [?y] @ ?zs" by simp
      from xsyys'_len have **: "length (?xs @ [?y] @ ?ys @ [?y]) \<le> Suc m" by simp
      from * ** show ?thesis by blast
    qed
  next
    case False
    let ?P' = "P - {a}"
    from "1.prems"(3) have a_in: "a \<in> P" by auto
    with "1.prems"(1) have a1: "m-1 = card ?P'" by simp
    from "1.prems"(2) w_len have "w \<noteq> []" by auto
    with "1.prems"(3) False have b_in: "\<exists>b\<noteq>a. b \<in> P" by force
    from a_in b_in "1.prems"(2) "1.prems"(1) have "m \<ge> 2"
      by (metis Suc_1 card_1_singletonE not_less_eq_eq singletonD verit_la_disequality)
    hence a2: "m-1 \<ge> 1" by simp
    from False "1.prems"(3) have a3: "\<forall>i<length w. w ! i \<in> ?P'"
      using DiffD2 by auto
    from "1.prems"(2) w_len have a4: "Suc (m-1) \<le> length w" by simp
    from a1 a2 a3 a4 have "\<exists>xs ys zs y. w = xs @ [y] @ ys @ [y] @ zs \<and> length (xs @ [y] @ ys @ [y]) \<le> Suc (m - 1)"
      using "1.IH" by simp
    then obtain xs ys zs y where w_split: "w = xs @ [y] @ ys @ [y] @ zs" and xsys_len: "length (xs @ [y] @ ys @ [y]) \<le> m" by auto
    from w_split have *: "a#w = (a#xs) @ [y] @ ys @ [y] @ zs" by simp
    from xsys_len have **: "length ((a#xs) @ [y] @ ys @ [y]) \<le> Suc m" by simp
    from * ** aw_cons show ?thesis by blast
  qed
qed

text
\<open>We define the function \<open>nxts_nts P a w\<close> that collects all paths traversing the word \<open>w\<close> starting from the non-terminal \<open>A\<close> in the 
 production set \<open>P\<close>. \<open>nxts_nts0\<close> appends the non-terminal \<open>A\<close> in front of every list produced by \<open>nxts_nts\<close>\<close>

fun nxts_nts :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> 'n list set" where
  "nxts_nts P A [] = {[]}"
| "nxts_nts P A (a#w) = (\<Union>B\<in>nxt_rlin2 P A a. (Cons B)`nxts_nts P B w)"

definition nxts_nts0 where
"nxts_nts0 P A w \<equiv> ((#) A) ` nxts_nts P A w"

subsection \<open>Properties of \<open>nxts_nts\<close> and \<open>nxts_nts0\<close>\<close>

lemma nxts_nts0_i0:
  "\<forall>e \<in> nxts_nts0 P A w. e!0 = A"
  unfolding nxts_nts0_def by auto

lemma nxts_nts0_shift:
  assumes "i < length w"
  shows "\<forall>e \<in> nxts_nts0 P A w. \<exists>e' \<in> nxts_nts P A w. e ! (Suc i) = e' ! i"
  unfolding nxts_nts0_def by auto

lemma nxts_nts_pick_nt:
  assumes "e \<in> nxts_nts P A (a#w)"
  shows "\<exists>C\<in>nxt_rlin2 P A a. \<exists>e' \<in> nxts_nts P C w. e = C#e'"
  using assms by auto

lemma nxts_nts0_len:
  "\<forall>e \<in> nxts_nts0 P A w. length e = Suc (length w)"
  unfolding nxts_nts0_def
  by (induction P A w rule: nxts_nts.induct) auto

lemma nxts_nts0_nxt: 
  assumes "i < length w"
  shows "\<forall>e \<in> nxts_nts0 P A w. e!(Suc i) \<in> nxt_rlin2 P (e!i) (w!i)"
  unfolding nxts_nts0_def using assms proof (induction P A w arbitrary: i rule: nxts_nts.induct)
  case (1 P A)
  thus ?case by simp
next
  case (2 P A a w)
  thus ?case
    using less_Suc_eq_0_disj by auto
qed

lemma nxts_nts0_path:
  assumes "i1 \<le> length w"
      and "i2 \<le> length w"
      and "i1 \<le> i2"
    shows "\<forall>e \<in> nxts_nts0 P A w. e!i2 \<in> nxts_rlin2_set P {e!i1} (drop i1 (take i2 w))"
proof
  fix e
  assume "e \<in> nxts_nts0 P A w"
  with assms show "e ! i2 \<in> nxts_rlin2_set P {e ! i1} (drop i1 (take i2 w))" proof (induction "i2-i1" arbitrary: i2)
    case 0
    thus ?case
      by (simp add: nxts_rlin2_set_def)
  next
    case (Suc x)
      let ?i2' = "i2 - 1"
      from Suc.hyps(2) have x_def: "x = ?i2' - i1" by simp
      from Suc.prems(2) have i2'_len: "?i2' \<le> length w" by simp
      from Suc.prems(3) Suc.hyps(2) have i1_i2': "i1 \<le> ?i2'" by simp
      have IH: "e ! ?i2' \<in> nxts_rlin2_set P {e ! i1} (drop i1 (take ?i2' w))"
        using Suc.hyps(1)[of ?i2', OF x_def Suc.prems(1) i2'_len i1_i2' Suc.prems(4)] .
      from Suc.hyps(2) Suc.prems(2) Suc.prems(4) have "e ! i2 \<in> nxt_rlin2 P (e!(i2-1)) (w!(i2-1))"
        using nxts_nts0_nxt[of ?i2' w P A] by simp
      hence e_i2: "e ! i2 \<in> nxts_rlin2_set P {e!(i2-1)} [w!(i2-1)]"
        unfolding nxts_rlin2_set_def nxt_rlin2_set_def by simp
      have "drop i1 (take (i2 - 1) w) @ [w ! (i2 - 1)] = drop i1 (take i2 w)"
        by (smt (verit) Cons_nth_drop_Suc Suc.hyps(2) Suc.prems(2) Suc.prems(3) add_Suc drop_drop drop_eq_Nil drop_take i1_i2' i2'_len le_add_diff_inverse2 le_less_Suc_eq nle_le nth_via_drop order.strict_iff_not take_Suc_conv_app_nth x_def)
      thus ?case 
        using nxts_trans2[of "e ! (i2 - 1)" P "e ! i1" "drop i1 (take (i2 - 1) w)" "e ! i2" "[w!(i2-1)]", OF IH e_i2] by argo
  qed
qed

lemma nxts_nts0_path_start:
  assumes "i \<le> length w"
  shows "\<forall>e \<in> nxts_nts0 P A w. e ! i \<in> nxts_rlin2_set P {A} (take i w)"
  using assms nxts_nts0_path[of 0 w i P A] by (simp add: nxts_nts0_def)

lemma nxts_nts_elem:
  assumes "i < length w"
  shows "\<forall>e \<in> nxts_nts P A w. e ! i \<in> Nts P"
proof
  fix e
  assume "e \<in> nxts_nts P A w"
  with assms show "e ! i \<in> Nts P" proof (induction P A w arbitrary: i e rule: nxts_nts.induct)
    case (1 P A)
    thus ?case by simp
  next
    case (2 P A a w)
    from 2(3) obtain C e' where C_def: "C \<in> nxt_rlin2 P A a" and e'_def: "e' \<in> nxts_nts P C w" and e_app: "e = C#e'"
      using nxts_nts_pick_nt[of e P A a w] by blast
    show ?case proof (cases "i = 0")
      case True
      with e_app C_def show ?thesis
        using nxt_rlin2_nts by simp
    next
      case False
      from False 2(2) have i_len: "i - 1 < length w" by simp
      have "e' ! (i - 1) \<in> Nts P" 
        using "2.IH"[of C "i-1" e', OF C_def i_len e'_def] .
      with e_app False have "e ! i \<in> Nts P" by simp
      thus ?thesis .
    qed
  qed
qed

lemma nxts_nts0_elem:
  assumes "A \<in> Nts P"
      and "i \<le> length w"
  shows "\<forall>e \<in> nxts_nts0 P A w. e ! i \<in> Nts P"
proof (cases "i = 0")
  case True
  thus ?thesis
    by (simp add: assms(1) nxts_nts0_i0)
next
  case False
  show ?thesis proof
    fix e
    assume e_def: "e \<in> nxts_nts0 P A w"
    from False e_def assms(2) have "\<exists>e' \<in> nxts_nts P A w. e ! i = e' ! (i-1)"
      using nxts_nts0_shift[of "i-1" w P A] by simp
    then obtain e' where e'_def: "e' \<in> nxts_nts P A w" and e_ind: "e ! i = e' ! (i-1)"
      by blast
    from False e'_def assms(2) have "e' ! (i-1) \<in> Nts P"
      using nxts_nts_elem[of "i-1" w P A] by simp
    with e_ind show "e ! i \<in> Nts P" by simp
  qed
qed

lemma nxts_nts0_pick:
  assumes "B \<in> nxts_rlin2_set P {A} w"
  shows "\<exists>e \<in> nxts_nts0 P A w. last e = B"
unfolding nxts_nts0_def using assms proof (induction P A w arbitrary: B rule: nxts_nts.induct)
  case (1 P A)
  thus ?case
    by (simp add: nxts_rlin2_set_def)
next
  case (2 P A a w)
  from 2(2) obtain C where C_def: "C \<in> nxt_rlin2 P A a" and C_path: "B \<in> nxts_rlin2_set P {C} w"
    using nxts_rlin2_set_first_step[of B P A a w] by blast
  have "\<exists>e \<in> nxts_nts0 P C w. last e = B"
    using "2.IH"[of C B, OF C_def C_path] by (simp add: nxts_nts0_def)
  then obtain e where e_def: "e \<in> nxts_nts0 P C w" and e_last: "last e = B" 
    by blast
  from e_def C_def have *: "A#e \<in> nxts_nts0 P A (a#w)"
    unfolding nxts_nts0_def by auto
  from e_last e_def have **: "last (A#e) = B"
    using nxts_nts0_len[of P C w] by auto
  from * ** show ?case
    unfolding nxts_nts0_def by blast
qed

subsection \<open>Pumping Lemma\<close>

text
\<open>The following lemma states that in the automata level there exists a cycle occurring in the first \<open>m\<close> symbols where \<open>m\<close> is the cardinality 
 of the non-terminals set, under the following assumptions\<close>

lemma nxts_split_cycle:
  assumes "finite P"
      and "A \<in> Nts P"
      and "m = card (Nts P)"
      and "B \<in> nxts_rlin2_set P {A} w"
      and "length w \<ge> m"
    shows "\<exists>x y z C. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> m \<and>
              C \<in> nxts_rlin2_set P {A} x \<and> C \<in> nxts_rlin2_set P {C} y \<and> B \<in> nxts_rlin2_set P {C} z"
proof -
  let ?nts = "nxts_nts0 P A w"
  obtain e where e_def: "e \<in> ?nts" and e_last: "last e = B"
    using nxts_nts0_pick[of B P A w, OF assms(4)] by auto
  from e_def have e_len: "length e = Suc (length w)"
    using nxts_nts0_len[of P A w] by simp
  from e_len e_def have e_elem: "\<forall>i < length e. e!i \<in> Nts P"
    using nxts_nts0_elem[OF assms(2)] by (auto simp: less_Suc_eq_le)
  have "finite (Nts P)"
    using finite_Nts[of P, OF assms(1)] .
  with assms(2) assms(3) have m_geq_1: "m \<ge> 1"
    using less_eq_Suc_le by fastforce
  from assms(5) e_len have "\<exists>xs ys zs y. e = xs @ [y] @ ys @ [y] @ zs \<and> length (xs @ [y] @ ys @ [y]) \<le> Suc m"
    using not_distinct[OF assms(3) m_geq_1 e_elem] by simp
  then obtain xs ys zs C where e_split: "e = xs @ [C] @ ys @ [C] @ zs" and xy_len: "length (xs @ [C] @ ys @ [C]) \<le> Suc m"
    by blast
  let ?e1 = "xs @ [C]" let ?e2 = "ys @ [C]" let ?e3 = zs
  let ?x = "take (length ?e1 - 1) w" let ?y = "drop (length ?e1 - 1) (take (length ?e1+length ?e2 - 1) w)"
  let ?z = "drop (length ?e1+length ?e2 - 1) w"
  have *: "w = ?x@?y@?z"
    by (metis Nat.add_diff_assoc2 append_assoc append_take_drop_id diff_add_inverse drop_take le_add1 length_append_singleton plus_1_eq_Suc take_add)
  from e_len e_split have **: "length ?y \<ge> 1" by simp
  from xy_len have ***: "length (?x@?y) \<le> m" by simp
  have x_fac: "?x = take (length xs) w" by simp
  from ** have x_fac2: "length xs \<le> length w"  by simp
  from e_split have x_fac3: "e ! length xs = C" by simp
  from e_def x_fac x_fac3 have ****: "C \<in> nxts_rlin2_set P {A} ?x"
    using nxts_nts0_path_start[of "length xs" w P A, OF x_fac2] by auto
  have y_fac: "?y = drop (length xs) (take (length xs + length ys + 1) w)" by simp
  from e_len e_split have y_fac2: "length xs + length ys + 1 \<le> length w" by simp
  have y_fac3: "length xs \<le> length xs + length ys + 1" by simp
  have y_fac4: "e ! (length xs + length ys + 1) = C"
    by (metis add.right_neutral add_Suc_right append.assoc append_Cons e_split length_Cons length_append list.size(3) nth_append_length plus_1_eq_Suc)
  from e_def y_fac x_fac3 y_fac4 have *****: "C \<in> nxts_rlin2_set P {C} ?y"
    using nxts_nts0_path[of "length xs" w "length xs + length ys + 1" P A, OF x_fac2 y_fac2 y_fac3] by auto
  have z_fac: "?z = drop (length xs + length ys + 1) (take (length w) w)" by simp
  from e_last e_len have z_fac2: "e ! (length w) = B"
    by (metis Zero_not_Suc diff_Suc_1 last_conv_nth list.size(3))
  from e_def z_fac y_fac2 y_fac4 z_fac2 have ******: "B \<in> nxts_rlin2_set P {C} ?z"
    using nxts_nts0_path[of "length xs + length ys + 1" w "length w" P A] by auto
  from * ** *** **** ***** ****** show ?thesis by blast
qed

text
\<open>We also show that a cycle can be pumped in the automata level\<close>

lemma pump_cycle:
  assumes "B \<in> nxts_rlin2_set P {A} x"
      and "B \<in> nxts_rlin2_set P {B} y"
    shows "B \<in> nxts_rlin2_set P {A} (x@(y^^i))"
using assms proof (induction i)
  case 0
  thus ?case by (simp add: assms(1))
next
  case (Suc i)
  have "B \<in> nxts_rlin2_set P {A} (x@(y^^i))"
    using Suc.IH[OF assms] .
  with assms(2) have "B \<in> nxts_rlin2_set P {A} (x@(y^^i)@y)"
    using nxts_trans2[of B P A "x@(y^^i)" B y] by simp
  thus ?case
    by (simp add: pow_list_comm)
qed

text
\<open>Combining the previous lemmas we can prove the pumping lemma where the starting non-terminal is in the production set. We simply extend the
 lemma for non-terminals that are not part of the production set, as these non-terminals will produce the empty language\<close>

lemma pumping_re_aux:
  assumes "finite P"
      and "A \<in> Nts P"
      and "m = card (Nts P)"
      and "accepted P A w"
      and "length w \<ge> m"
    shows "\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> m \<and> (\<forall>i. accepted P A (x@(y^^i)@z))"
proof -
  from assms(4) obtain Z where Z_in:"Z \<in> nxts_rlin2_set P {A} w" and Z_eps:"(Z,[])\<in>P"
    by (auto simp: accepted_def)
  obtain x y z C where *: "w = x@y@z" and **: "length y \<ge> 1" and ***: "length (x@y) \<le> m" and
              1: "C \<in> nxts_rlin2_set P {A} x" and 2: "C \<in> nxts_rlin2_set P {C} y" and 3: "Z \<in> nxts_rlin2_set P {C} z"
    using nxts_split_cycle[OF assms(1) assms(2) assms(3) Z_in assms(5)] by auto
  have "\<forall>i. C \<in> nxts_rlin2_set P {A} (x@(y^^i))"
    using pump_cycle[OF 1 2] by simp
  with 3 have "\<forall>i. Z \<in> nxts_rlin2_set P {A} (x@(y^^i)@z)"
    using nxts_trans2[of C P A] by fastforce
  with Z_eps have ****: "(\<forall>i. accepted P A (x@(y^^i)@z))"
    by (auto simp: accepted_def)
  from * ** *** **** show ?thesis by auto
qed

theorem pumping_lemma_re_nts:
  assumes "rlin2 P"
      and "finite P"
      and "A \<in> Nts P"
  shows "\<exists>n. \<forall>w \<in> Lang P A. length w \<ge> n \<longrightarrow>
          (\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<and> (\<forall>i. x@(y^^i)@z \<in> Lang P A))" 
  using assms pumping_re_aux[of P A "card (Nts P)"] Lang_iff_accepted_if_rlin2[OF assms(1)] by metis

theorem pumping_lemma_regular:
  assumes "rlin2 P" and "finite P"
  shows "\<exists>n. \<forall>w \<in> Lang P A. length w \<ge> n \<longrightarrow>
          (\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<and> (\<forall>i. x@(y^^i)@z \<in> Lang P A))" 
proof (cases "A \<in> Nts P")
  case True
  thus ?thesis
    using pumping_lemma_re_nts[OF assms True] by simp
next
  case False
  hence "Lang P A = {}"
    by (auto intro!: Lang_empty_if_notin_Lhss simp add: Lhss_def Nts_def)
  thus ?thesis by simp
qed

text \<open>Most of the time pumping lemma is used in the contrapositive form
to prove that no right-linear set of productions exists.\<close>

corollary pumping_lemma_regular_contr:
  assumes "finite P"
      and "\<forall>n. \<exists>w \<in> Lang P A. length w \<ge> n \<and> (\<forall>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<longrightarrow> (\<exists>i. x@(y^^i)@z \<notin> Lang P A))" 
    shows "\<not>rlin2 P"
using assms pumping_lemma_regular[of P A] by metis

end