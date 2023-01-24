section \<open>Elementary Turing machines\label{s:tm-elementary}\<close>

theory Elementary
  imports Combinations
begin

text \<open>
In this section we devise some simple yet useful Turing machines.  We have
already fully analyzed the empty TM, where start and halting state coincide, in
the lemmas~@{thm [source] computes_Nil_empty}, @{thm [source] Nil_tm}, and @{thm
[source] transforms_Nil}.  The next more complex TMs are those with exactly one
command. They represent TMs with two states: the halting state and the start
state where the action happens. This action might last for one step only, or the
TM may stay in this state for longer; for example, it can move a tape head
rightward to the next blank symbol.  We will also start using the @{text ";;"}
operator to combine some of the one-command TMs.
\<close>

text \<open>
Most Turing machines we are going to construct throughout this section and
indeed the entire article are really families of Turing machines that usually
are parameterized by tape indices.
\<close>

type_synonym tapeidx = nat

text \<open>
Throughout this article, names of commands are prefixed with @{text cmd_} and
names of Turing machines with @{text tm_}. Usually for a TM named @{term tm_foo}
there is a lemma @{text tm_foo_tm} stating that it really is a Turing machine and
a lemma @{text transforms_tm_fooI} describing its semantics and running time. The
lemma usually receives a @{text transforms_intros} attribute for use with our
proof method.

If @{term "tm_foo"} comprises more than two TMs we will typically analyze the
semantics and running time in a locale named @{text "turing_machine_foo"}. The
first example of this is @{term tm_equals} in
Section~\ref{s:tm-elementary-comparing}.

When it comes to running times, we will have almost no scruples simplifying
upper bounds to have the form $a + b\cdot n^c$ for some constants $a, b, c$,
even if this means, for example, bounding $n \log n$ by $n^2$.
\<close>


subsection \<open>Clean tapes\<close>

text \<open>
Most of our Turing machines will not change the start symbol in the first cell
of a tape nor will they write the start symbol anywhere else. The only
exceptions are machines that simulate arbitrary other machines. We call tapes
that have the start symbol only in the first cell \emph{clean tapes}.
\<close>

definition clean_tape :: "tape \<Rightarrow> bool" where
  "clean_tape tp \<equiv> \<forall>i. fst tp i = \<triangleright> \<longleftrightarrow> i = 0"

lemma clean_tapeI:
  assumes "\<And>i. fst tp i = \<triangleright> \<longleftrightarrow> i = 0"
  shows "clean_tape tp"
  unfolding clean_tape_def using assms by simp

lemma clean_tapeI':
  assumes "fst tp 0 = \<triangleright>" and "\<And>i. i > 0 \<Longrightarrow> fst tp i \<noteq> \<triangleright>"
  shows "clean_tape tp"
  unfolding clean_tape_def using assms by auto

text \<open>
A clean configuration is one with only clean tapes.
\<close>

definition clean_config :: "config \<Rightarrow> bool" where
  "clean_config cfg \<equiv> (\<forall>j<||cfg||. \<forall>i. (cfg <:> j) i = \<triangleright> \<longleftrightarrow> i = 0)"

lemma clean_config_tapes: "clean_config cfg = (\<forall>tp\<in>set (snd cfg). clean_tape tp)"
  using clean_config_def clean_tape_def by (metis in_set_conv_nth)

lemma clean_configI:
  assumes "\<And>j i. j < length tps \<Longrightarrow> fst (tps ! j) i = \<triangleright> \<longleftrightarrow> i = 0"
  shows "clean_config (q, tps)"
  unfolding clean_config_def using assms by simp

lemma clean_configI':
  assumes "\<And>tp i. tp \<in> set tps \<Longrightarrow> fst tp i = \<triangleright> \<longleftrightarrow> i = 0"
  shows "clean_config (q, tps)"
  using clean_configI assms by simp

lemma clean_configI'':
  assumes "\<And>tp. tp \<in> set tps \<Longrightarrow> (fst tp 0 = \<triangleright> \<and> (\<forall>i>0. fst tp i \<noteq> \<triangleright>))"
  shows "clean_config (q, tps)"
  using clean_configI' assms by blast

lemma clean_configE:
  assumes "clean_config (q, tps)"
  shows "\<And>j i. j < length tps \<Longrightarrow> fst (tps ! j) i = \<triangleright> \<longleftrightarrow> i = 0"
  using clean_config_def assms by simp

lemma clean_configE':
  assumes "clean_config (q, tps)"
  shows "\<And>tp i. tp \<in> set tps \<Longrightarrow> fst tp i = \<triangleright> \<longleftrightarrow> i = 0"
  using clean_configE assms by (metis in_set_conv_nth)

lemma clean_contents_proper [simp]: "proper_symbols zs \<Longrightarrow> clean_tape (\<lfloor>zs\<rfloor>, q)"
  using clean_tape_def contents_def proper_symbols_ne1 by simp

lemma contents_clean_tape': "proper_symbols zs \<Longrightarrow> fst tp = \<lfloor>zs\<rfloor> \<Longrightarrow> clean_tape tp"
  using contents_def clean_tape_def by (simp add: nat_neq_iff)

text \<open>
Some more lemmas about @{const contents}:
\<close>

lemma contents_append_blanks: "\<lfloor>ys @ replicate m \<box>\<rfloor> = \<lfloor>ys\<rfloor>"
proof
  fix i
  consider
      "i = 0"
    | "0 < i \<and> i \<le> length ys"
    | "length ys < i \<and> i \<le> length ys + m"
    | "length ys + m < i"
    by linarith
  then show "\<lfloor>ys @ replicate m \<box>\<rfloor> i = \<lfloor>ys\<rfloor> i"
  proof (cases)
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using contents_inbounds
      by (metis (no_types, opaque_lifting) Suc_diff_1 Suc_le_eq le_add1 le_trans length_append nth_append)
  next
    case 3
    then show ?thesis
      by (smt (z3) Suc_diff_Suc add_diff_inverse_nat contents_def diff_Suc_1 diff_commute leD less_one
        less_or_eq_imp_le nat_add_left_cancel_le not_less_eq nth_append nth_replicate)
  next
    case 4
    then show ?thesis
      by simp
  qed
qed

lemma contents_append_update:
  assumes "length ys = m"
  shows "\<lfloor>ys @ [v] @ zs\<rfloor>(Suc m := w) = \<lfloor>ys @ [w] @ zs\<rfloor>"
proof
  fix i
  consider
      "i = 0"
    | "0 < i \<and> i < Suc m"
    | "i = Suc m"
    | "i > Suc m \<and> i \<le> Suc m + length zs"
    | "i > Suc m + length zs"
    by linarith
  then show "(\<lfloor>ys @ [v] @ zs\<rfloor>(Suc m := w)) i = \<lfloor>ys @ [w] @ zs\<rfloor> i"
    (is "?l = ?r")
  proof (cases)
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then have "?l = (ys @ [v] @ zs) ! (i - 1)"
      using assms contents_inbounds by simp
    then have *: "?l = ys ! (i - 1)"
      using 2 assms by (metis Suc_diff_1 Suc_le_lessD less_Suc_eq_le nth_append)
    have "?r = (ys @ [w] @ zs) ! (i - 1)"
      using 2 assms contents_inbounds by simp
    then have "?r = ys ! (i - 1)"
      using 2 assms by (metis Suc_diff_1 Suc_le_lessD less_Suc_eq_le nth_append)
    then show ?thesis
      using * by simp
  next
    case 3
    then show ?thesis
      using assms by auto
  next
    case 4
    then have "?l = (ys @ [v] @ zs) ! (i - 1)"
      using assms contents_inbounds by simp
    then have "?l = ((ys @ [v]) @ zs) ! (i - 1)"
      by simp
    then have *: "?l = zs ! (i - 1 - Suc m)"
      using 4 assms by (metis diff_Suc_1 length_append_singleton less_imp_Suc_add not_add_less1 nth_append)
    then have "?r = (ys @ [w] @ zs) ! (i - 1)"
      using 4 assms contents_inbounds by simp
    then have "?r = ((ys @ [w]) @ zs) ! (i - 1)"
      by simp
    then have "?r = zs ! (i - 1 - Suc m)"
      using 4 assms by (metis diff_Suc_1 length_append_singleton less_imp_Suc_add not_add_less1 nth_append)
    then show ?thesis
      using * by simp
  next
    case 5
    then show ?thesis
      using assms by simp
  qed
qed

lemma contents_snoc: "\<lfloor>ys\<rfloor>(Suc (length ys) := w) = \<lfloor>ys @ [w]\<rfloor>"
proof
  fix i
  consider "i = 0" | "0 < i \<and> i \<le> length ys" | "i = Suc (length ys)" | "i > Suc (length ys)"
    by linarith
  then show "(\<lfloor>ys\<rfloor>(Suc (length ys) := w)) i = \<lfloor>ys @ [w]\<rfloor> i"
  proof (cases)
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      by (smt (verit, ccfv_SIG) contents_def diff_Suc_1 ex_least_nat_less fun_upd_apply leD le_Suc_eq
        length_append_singleton less_imp_Suc_add nth_append)
  next
    case 3
    then show ?thesis
      by simp
  next
    case 4
    then show ?thesis
      by simp
  qed
qed

definition config_update_pos :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> config" where
  "config_update_pos cfg j p \<equiv> (fst cfg, (snd cfg)[j:=(cfg <:> j, p)])"

lemma config_update_pos_0: "config_update_pos cfg j (cfg <#> j) = cfg"
  using config_update_pos_def by simp

definition config_update_fwd :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> config" where
  "config_update_fwd cfg j d \<equiv> (fst cfg, (snd cfg)[j:=(cfg <:> j, cfg <#> j + d)])"

lemma config_update_fwd_0: "config_update_fwd cfg j 0 = cfg"
  using config_update_fwd_def by simp

lemma config_update_fwd_additive:
  "config_update_fwd (config_update_fwd cfg j d1) j d2 = (config_update_fwd cfg j (d1 + d2))"
  using config_update_fwd_def
  by (smt add.commute add.left_commute fst_conv le_less_linear list_update_beyond list_update_overwrite nth_list_update_eq sndI)


subsection \<open>Moving tape heads\<close>

text \<open>
Among the most simple things a Turing machine can do is moving one of its tape
heads.
\<close>

subsubsection \<open>Moving left\<close>

text \<open>
The next command makes a TM move its head on tape $j$ one cell to the left
unless, of course, it is in the leftmost cell already.
\<close>

definition cmd_left :: "tapeidx \<Rightarrow> command" where
  "cmd_left j \<equiv> \<lambda>rs. (1, map (\<lambda>i. (rs ! i, if i = j then Left else Stay)) [0..<length rs])"

lemma turing_command_left: "turing_command k 1 G (cmd_left j)"
  by (auto simp add: cmd_left_def)

lemma cmd_left': "[*] (cmd_left j rs) = 1"
  using cmd_left_def by simp

lemma cmd_left'': "j < length rs \<Longrightarrow> (cmd_left j rs) [!] j = (rs ! j, Left)"
  using cmd_left_def by simp

lemma cmd_left''': "i < length rs \<Longrightarrow> i \<noteq> j \<Longrightarrow> (cmd_left j rs) [!] i = (rs ! i, Stay)"
  using cmd_left_def by simp

lemma tape_list_eq:
  assumes "length tps' = length tps"
    and "\<And>i. i < length tps \<Longrightarrow> i \<noteq> j \<Longrightarrow> tps' ! i = tps ! i"
    and "tps' ! j = x"
  shows "tps' = tps[j := x]"
  using assms by (smt length_list_update list_update_beyond not_le nth_equalityI nth_list_update)

lemma sem_cmd_left:
  assumes "j < length tps"
  shows "sem (cmd_left j) (0, tps) = (1, tps[j:=(fst (tps ! j), snd (tps ! j) - 1)])"
proof
  show "fst (sem (cmd_left j)  (0, tps)) = fst (1, tps[j := (fst (tps ! j), snd (tps ! j) - 1)])"
    using cmd_left' sem_fst by simp
  have "snd (sem (cmd_left j) (0, tps)) = tps[j := (fst (tps ! j), snd (tps ! j) - 1)]"
  proof (rule tape_list_eq)
    show "||sem (cmd_left j) (0, tps)|| = length tps"
      using turing_command_left sem_num_tapes2' by (metis snd_eqD)
    show "sem (cmd_left j) (0, tps) <!> i = tps ! i" if "i < length tps" and "i \<noteq> j" for i
    proof -
      let ?rs = "read tps"
      have "length ?rs = length tps"
        using read_length by simp
      moreover have "sem (cmd_left j) (0, tps) <!> i = act (cmd_left j ?rs [!] i) (tps ! i)"
        by (simp add: cmd_left_def sem_snd that(1))
      ultimately show ?thesis
        using that act_Stay cmd_left''' by simp
    qed
    show "sem (cmd_left j) (0, tps) <!> j = (fst (tps ! j), snd (tps ! j) - 1)"
      using assms act_Left cmd_left_def read_length sem_snd by simp
  qed
  then show "snd (sem (cmd_left j) (0, tps)) = snd (1, tps[j := (fst (tps ! j), snd (tps ! j) - 1)])"
    by simp
qed

definition tm_left :: "tapeidx \<Rightarrow> machine" where
  "tm_left j \<equiv> [cmd_left j]"

lemma tm_left_tm: "k \<ge> 2 \<Longrightarrow> G \<ge> 4 \<Longrightarrow> turing_machine k G (tm_left j)"
  unfolding tm_left_def using turing_command_left by auto

lemma exe_tm_left:
  assumes "j < length tps"
  shows "exe (tm_left j) (0, tps) = (1, tps[j := tps ! j |-| 1])"
  unfolding tm_left_def using sem_cmd_left assms by (simp add: exe_lt_length)

lemma execute_tm_left:
  assumes "j < length tps"
  shows "execute (tm_left j) (0, tps) (Suc 0) = (1, tps[j := tps ! j |-| 1])"
  using assms exe_tm_left by simp

lemma transits_tm_left:
  assumes "j < length tps"
  shows "transits (tm_left j) (0, tps) (Suc 0) (1, tps[j := tps ! j |-| 1])"
  using execute_tm_left assms transitsI by blast

lemma transforms_tm_left:
  assumes "j < length tps"
  shows "transforms (tm_left j) tps (Suc 0) (tps[j := tps ! j |-| 1])"
  using transits_tm_left assms by (simp add: tm_left_def transforms_def)

lemma transforms_tm_leftI [transforms_intros]:
  assumes "j < length tps"
    and "t = 1"
    and "tps' = tps[j := tps ! j |-| 1]"
  shows "transforms (tm_left j) tps t tps'"
  using transits_tm_left assms by (simp add: tm_left_def transforms_def)


subsubsection \<open>Moving right\<close>

text \<open>
The next command makes the head on tape $j$ move one cell to the right.
\<close>

definition cmd_right :: "tapeidx \<Rightarrow> command" where
  "cmd_right j \<equiv> \<lambda>rs. (1, map (\<lambda>i. (rs ! i, if i = j then Right else Stay)) [0..<length rs])"

lemma turing_command_right: "turing_command k 1 G (cmd_right j)"
  by (auto simp add: cmd_right_def)

lemma cmd_right': "[*] (cmd_right j rs) = 1"
  using cmd_right_def by simp

lemma cmd_right'': "j < length rs \<Longrightarrow> (cmd_right j rs) [!] j = (rs ! j, Right)"
  using cmd_right_def by simp

lemma cmd_right''': "i < length rs \<Longrightarrow> i \<noteq> j \<Longrightarrow> (cmd_right j rs) [!] i = (rs ! i, Stay)"
  using cmd_right_def by simp

lemma sem_cmd_right:
  assumes "j < length tps"
  shows "sem (cmd_right j) (0, tps) = (1, tps[j:=(fst (tps ! j), snd (tps ! j) + 1)])"
proof
  show "fst (sem (cmd_right j)  (0, tps)) = fst (1, tps[j := (fst (tps ! j), snd (tps ! j) + 1)])"
    using cmd_right' sem_fst by simp
  have "snd (sem (cmd_right j) (0, tps)) = tps[j := (fst (tps ! j), snd (tps ! j) + 1)]"
  proof (rule tape_list_eq)
    show "||sem (cmd_right j) (0, tps)|| = length tps"
      using sem_num_tapes3 turing_command_right by (metis snd_conv)
    show "sem (cmd_right j) (0, tps) <!> i = tps ! i" if "i < length tps" and "i \<noteq> j" for i
    proof -
      let ?rs = "read tps"
      have "length ?rs = length tps"
        using read_length by simp
      moreover have "sem (cmd_right j) (0, tps) <!> i = act (cmd_right j ?rs [!] i) (tps ! i)"
        by (simp add: cmd_right_def sem_snd that(1))
      ultimately show ?thesis
        using that act_Stay cmd_right''' by simp
    qed
    show "sem (cmd_right j) (0, tps) <!> j = (fst (tps ! j), snd (tps ! j) + 1)"
      using assms act_Right cmd_right_def read_length sem_snd by simp
  qed
  then show "snd (sem (cmd_right j) (0, tps)) = snd (1, tps[j := (fst (tps ! j), snd (tps ! j) + 1)])"
    by simp
qed

definition tm_right :: "tapeidx \<Rightarrow> machine" where
  "tm_right j \<equiv> [cmd_right j]"

lemma tm_right_tm: "k \<ge> 2 \<Longrightarrow> G \<ge> 4 \<Longrightarrow> turing_machine k G (tm_right j)"
  unfolding tm_right_def using turing_command_right cmd_right' by auto

lemma exe_tm_right:
  assumes "j < length tps"
  shows "exe (tm_right j) (0, tps) = (1, tps[j:=(fst (tps ! j), snd (tps ! j) + 1)])"
  unfolding tm_right_def using sem_cmd_right assms by (simp add: exe_lt_length)

lemma execute_tm_right:
  assumes "j < length tps"
  shows "execute (tm_right j) (0, tps) (Suc 0) = (1, tps[j:=(fst (tps ! j), snd (tps ! j) + 1)])"
  using assms exe_tm_right by simp

lemma transits_tm_right:
  assumes "j < length tps"
  shows "transits (tm_right j) (0, tps) (Suc 0) (1, tps[j:=(fst (tps ! j), snd (tps ! j) + 1)])"
  using execute_tm_right assms transitsI by blast

lemma transforms_tm_right:
  assumes "j < length tps"
  shows "transforms (tm_right j) tps (Suc 0) (tps[j := tps ! j |+| 1])"
  using transits_tm_right assms by (simp add: tm_right_def transforms_def)

lemma transforms_tm_rightI [transforms_intros]:
  assumes "j < length tps"
    and "t = Suc 0"
    and "tps' = tps[j := tps ! j |+| 1]"
  shows "transforms (tm_right j) tps t tps'"
  using transits_tm_right assms by (simp add: tm_right_def transforms_def)


subsubsection \<open>Moving right on several tapes\<close>

text \<open>
The next command makes the heads on all tapes from a set $J$ of tapes move one
cell to the right.
\<close>

definition cmd_right_many :: "tapeidx set \<Rightarrow> command" where
  "cmd_right_many J \<equiv> \<lambda>rs. (1, map (\<lambda>i. (rs ! i, if i \<in> J then Right else Stay)) [0..<length rs])"

lemma turing_command_right_many: "turing_command k 1 G (cmd_right_many J)"
  by (auto simp add: cmd_right_many_def)

lemma sem_cmd_right_many:
  "sem (cmd_right_many J) (0, tps) = (1, map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
proof
  show "fst (sem (cmd_right_many J)  (0, tps)) =
      fst (1, map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
    using cmd_right_many_def sem_fst by simp
  have "snd (sem (cmd_right_many J) (0, tps)) =
    map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps]"
    (is "?lhs = ?rhs")
  proof (rule nth_equalityI)
    show "length ?lhs = length ?rhs"
      using turing_command_right_many sem_num_tapes2'
      by (metis (no_types, lifting) diff_zero length_map length_upt snd_conv)
    then have len: "length ?lhs = length tps"
      by simp
    show "?lhs ! j = ?rhs ! j" if "j < length ?lhs" for j
    proof (cases "j \<in> J")
      case True
      let ?rs = "read tps"
      have "length ?rs = length tps"
        using read_length by simp
      moreover have "sem (cmd_right_many J) (0, tps) <!> j = act (cmd_right_many J ?rs [!] j) (tps ! j)"
        using cmd_right_many_def sem_snd that True len by auto
      moreover have "?rhs ! j = tps ! j |+| 1"
        using that len True by simp
      ultimately show ?thesis
        using that act_Right cmd_right_many_def True len by simp
    next
      case False
      let ?rs = "read tps"
      have "length ?rs = length tps"
        using read_length by simp
      moreover have "sem (cmd_right_many J) (0, tps) <!> j = act (cmd_right_many J ?rs [!] j) (tps ! j)"
        using cmd_right_many_def sem_snd that False len by auto
      moreover have "?rhs ! j = tps ! j"
        using that len False by simp
      ultimately show ?thesis
        using that act_Stay cmd_right_many_def False len by simp
    qed
  qed
  then show "snd (sem (cmd_right_many J) (0, tps)) =
      snd (1, map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
    by simp
qed

definition tm_right_many :: "tapeidx set \<Rightarrow> machine" where
  "tm_right_many J \<equiv> [cmd_right_many J]"

lemma tm_right_many_tm: "k \<ge> 2 \<Longrightarrow> G \<ge> 4 \<Longrightarrow> turing_machine k G (tm_right_many J)"
  unfolding tm_right_many_def using turing_command_right_many by auto

lemma transforms_tm_right_manyI [transforms_intros]:
  assumes "t = Suc 0"
    and "tps' = map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps]"
  shows "transforms (tm_right_many J) tps t tps'"
proof -
  have "exe (tm_right_many J) (0, tps) = (1, map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
    unfolding tm_right_many_def using sem_cmd_right_many by (simp add: exe_lt_length)
  then have "execute (tm_right_many J) (0, tps) (Suc 0) = (1, map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
    by simp
  then have "transits (tm_right_many J) (0, tps) (Suc 0) (1, map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
    using transitsI by blast
  then have "transforms (tm_right_many J) tps (Suc 0) (map (\<lambda>j. if j \<in> J then tps ! j |+| 1 else tps ! j) [0..<length tps])"
    by (simp add: tm_right_many_def transforms_def)
  then show ?thesis
    using assms by (simp add: tm_right_many_def transforms_def)
qed


subsection \<open>Copying and translating tape contents\<close>

text \<open>
The Turing machines in this section scan a tape $j_1$ and copy the symbols to
another tape $j_2$. Scanning can be performed in either direction, and ``copying''
may include mapping the symbols.
\<close>


subsubsection \<open>Copying and translating from one tape to another\<close>

text \<open>
The next predicate is true iff.\ on the given tape the next symbol from the set
$H$ of symbols is exactly $n$ cells to the right from the current head position.
Thus, a command that moves the tape head right until it finds a symbol from $H$
takes $n$ steps and moves the head $n$ cells right.
\<close>

definition rneigh :: "tape \<Rightarrow> symbol set \<Rightarrow> nat \<Rightarrow> bool" where
  "rneigh tp H n \<equiv> fst tp (snd tp + n) \<in> H \<and> (\<forall>n' < n. fst tp (snd tp + n') \<notin> H)"

lemma rneighI:
  assumes "fst tp (snd tp + n) \<in> H" and "\<And>n'. n' < n \<Longrightarrow> fst tp (snd tp + n') \<notin> H"
  shows "rneigh tp H n"
  using assms rneigh_def by simp

text \<open>
The analogous predicate for moving to the left:
\<close>

definition lneigh :: "tape \<Rightarrow> symbol set \<Rightarrow> nat \<Rightarrow> bool" where
  "lneigh tp H n \<equiv> fst tp (snd tp - n) \<in> H \<and> (\<forall>n' < n. fst tp (snd tp - n') \<notin> H)"

lemma lneighI:
  assumes "fst tp (snd tp - n) \<in> H" and "\<And>n'. n' < n \<Longrightarrow> fst tp (snd tp - n') \<notin> H"
  shows "lneigh tp H n"
  using assms lneigh_def by simp

text \<open>
The next command scans tape $j_1$ rightward until it reaches a symbol from the
set $H$. While doing so it copies the symbols, after applying a mapping $f$, to
tape $j_2$.
\<close>

definition cmd_trans_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> command" where
  "cmd_trans_until j1 j2 H f \<equiv> \<lambda>rs.
    if rs ! j1 \<in> H
    then (1, map (\<lambda>r. (r, Stay)) rs)
    else (0, map (\<lambda>i. (if i = j2 then f (rs ! j1) else rs ! i, if i = j1 \<or> i = j2 then Right else Stay)) [0..<length rs])"

text \<open>
The analogous command for moving to the left:
\<close>

definition cmd_ltrans_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> command" where
  "cmd_ltrans_until j1 j2 H f \<equiv> \<lambda>rs.
    if rs ! j1 \<in> H
    then (1, map (\<lambda>r. (r, Stay)) rs)
    else (0, map (\<lambda>i. (if i = j2 then f (rs ! j1) else rs ! i, if i = j1 \<or> i = j2 then Left else Stay)) [0..<length rs])"

lemma proper_cmd_trans_until: "proper_command k (cmd_trans_until j1 j2 H f)"
  using cmd_trans_until_def by simp

lemma proper_cmd_ltrans_until: "proper_command k (cmd_ltrans_until j1 j2 H f)"
  using cmd_ltrans_until_def by simp

lemma sem_cmd_trans_until_1:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<in> H"
  shows "sem (cmd_trans_until j1 j2 H f) (0, tps) = (1, tps)"
  using cmd_trans_until_def tapes_at_read read_length assms act_Stay
  by (intro semI[OF proper_cmd_trans_until]) auto

lemma sem_cmd_ltrans_until_1:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<in> H"
  shows "sem (cmd_ltrans_until j1 j2 H f) (0, tps) = (1, tps)"
  using cmd_ltrans_until_def tapes_at_read read_length assms act_Stay
  by (intro semI[OF proper_cmd_ltrans_until]) auto

lemma sem_cmd_trans_until_2:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<notin> H"
  shows "sem (cmd_trans_until j1 j2 H f) (0, tps) =
    (0, tps[j1 := tps ! j1 |+| 1, j2 := tps ! j2 |:=| (f (tps :.: j1)) |+| 1])"
  using cmd_trans_until_def tapes_at_read read_length assms act_Stay act_Right
  by (intro semI[OF proper_cmd_trans_until]) auto

lemma sem_cmd_ltrans_until_2:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<notin> H"
  shows "sem (cmd_ltrans_until j1 j2 H f) (0, tps) =
    (0, tps[j1 := tps ! j1 |-| 1, j2 := tps ! j2 |:=| (f (tps :.: j1)) |-| 1])"
  using cmd_ltrans_until_def tapes_at_read read_length assms act_Stay act_Left
  by (intro semI[OF proper_cmd_ltrans_until]) auto

definition tm_trans_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> machine" where
  "tm_trans_until j1 j2 H f \<equiv> [cmd_trans_until j1 j2 H f]"

definition tm_ltrans_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> machine" where
  "tm_ltrans_until j1 j2 H f \<equiv> [cmd_ltrans_until j1 j2 H f]"

lemma tm_trans_until_tm:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "\<forall>h<G. f h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_trans_until j1 j2 H f)"
  unfolding tm_trans_until_def cmd_trans_until_def using assms turing_machine_def by auto

lemma tm_ltrans_until_tm:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "\<forall>h<G. f h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_ltrans_until j1 j2 H f)"
  unfolding tm_ltrans_until_def cmd_ltrans_until_def using assms turing_machine_def by auto

lemma exe_tm_trans_until_1:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<in> H"
  shows "exe (tm_trans_until j1 j2 H f) (0, tps) = (1, tps)"
  unfolding tm_trans_until_def using sem_cmd_trans_until_1 assms exe_lt_length by simp

lemma exe_tm_ltrans_until_1:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<in> H"
  shows "exe (tm_ltrans_until j1 j2 H f) (0, tps) = (1, tps)"
  unfolding tm_ltrans_until_def using sem_cmd_ltrans_until_1 assms exe_lt_length by simp

lemma exe_tm_trans_until_2:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<notin> H"
  shows "exe (tm_trans_until j1 j2 H f) (0, tps) =
    (0, tps[j1 := tps ! j1 |+| 1, j2 := tps ! j2 |:=| (f (tps :.: j1)) |+| 1])"
  unfolding tm_trans_until_def using sem_cmd_trans_until_2 assms exe_lt_length by simp

lemma exe_tm_ltrans_until_2:
  assumes "j1 < k" and "length tps = k" and "(0, tps) <.> j1 \<notin> H"
  shows "exe (tm_ltrans_until j1 j2 H f) (0, tps) =
    (0, tps[j1 := tps ! j1 |-| 1, j2 := tps ! j2 |:=| (f (tps :.: j1)) |-| 1])"
  unfolding tm_ltrans_until_def using sem_cmd_ltrans_until_2 assms exe_lt_length by simp

text \<open>
Let $tp_1$ and $tp_2$ be two tapes with head positions $i_1$ and $i_2$,
respectively. The next function describes the result of overwriting the symbols
at positions $i_2, \dots, i_2 + n - 1$ on tape $tp_2$ by the symbols at
positions $i_1, \dots, i_1 + n - 1$ on tape $tp_1$ after applying a symbol map
$f$.
\<close>

definition transplant :: "tape \<Rightarrow> tape \<Rightarrow> (symbol \<Rightarrow> symbol)\<Rightarrow> nat \<Rightarrow> tape" where
  "transplant tp1 tp2 f n \<equiv>
     (\<lambda>i. if snd tp2 \<le> i \<and> i < snd tp2 + n then f (fst tp1 (snd tp1 + i - snd tp2)) else fst tp2 i,
      snd tp2 + n)"

text \<open>
The analogous function for moving to the left while copying:
\<close>

definition ltransplant :: "tape \<Rightarrow> tape \<Rightarrow> (symbol \<Rightarrow> symbol)\<Rightarrow> nat \<Rightarrow> tape" where
  "ltransplant tp1 tp2 f n \<equiv>
     (\<lambda>i. if snd tp2 - n < i \<and> i \<le> snd tp2 then f (fst tp1 (snd tp1 + i - snd tp2)) else fst tp2 i,
      snd tp2 - n)"

lemma transplant_0: "transplant tp1 tp2 f 0 = tp2"
  unfolding transplant_def by standard auto

lemma ltransplant_0: "ltransplant tp1 tp2 f 0 = tp2"
  unfolding ltransplant_def by standard auto

lemma transplant_upd: "transplant tp1 tp2 f n |:=| (f ( |.| (tp1 |+| n))) |+| 1 = transplant tp1 tp2 f (Suc n)"
  unfolding transplant_def by auto

lemma ltransplant_upd:
  assumes "n < snd tp2"
  shows "ltransplant tp1 tp2 f n |:=| (f ( |.| (tp1 |-| n))) |-| 1 = ltransplant tp1 tp2 f (Suc n)"
  unfolding ltransplant_def using assms by fastforce

lemma tapes_ltransplant_upd:
  assumes "t < tps :#: j2" and "t < tps :#: j1" and "j1 < k" and "j2 < k" and "length tps = k"
    and "tps' = tps[j1 := tps ! j1 |-| t, j2 := ltransplant (tps ! j1) (tps ! j2) f t]"
  shows "tps'[j1 := tps' ! j1 |-| 1, j2 := tps' ! j2 |:=| (f (tps' :.: j1)) |-| 1] =
    tps[j1 := tps ! j1 |-| Suc t, j2 := ltransplant (tps ! j1) (tps ! j2) f (Suc t)]"
    (is "?lhs = ?rhs")
proof (rule nth_equalityI)
  show 1: "length ?lhs = length ?rhs"
    using assms by simp
  have len: "length ?lhs = k"
    using assms by simp
  show "?lhs ! j = ?rhs ! j" if "j < length ?lhs" for j
  proof -
    have "j < k"
      using len that by simp
    show ?thesis
    proof (cases "j \<noteq> j1 \<and> j \<noteq> j2")
      case True
      then show ?thesis
        using assms by simp
    next
      case j1j2: False
      show ?thesis
      proof (cases "j1 = j2")
        case True
        then have j: "j = j1" "j = j2"
          using j1j2 by simp_all
        have "tps' ! j1 = ltransplant (tps ! j1) (tps ! j2) f t"
          using j assms that by simp
        then have *: "snd (tps' ! j1) = snd (tps ! j1) - t"
          using j ltransplant_def by simp
        then have "fst (tps' ! j1) =
          (\<lambda>i. if snd (tps ! j2) - t < i \<and> i \<le> snd (tps ! j2) then f (fst (tps ! j1) (snd (tps ! j1) + i - snd (tps ! j2))) else fst (tps ! j2) i)"
          using j ltransplant_def assms by auto
        then have "fst (tps' ! j1) =
          (\<lambda>i. if snd (tps ! j1) - t < i \<and> i \<le> snd (tps ! j1) then f (fst (tps ! j1) (snd (tps ! j1) + i - snd (tps ! j1))) else fst (tps ! j1) i)"
         using j by auto
        then have "fst (tps' ! j1) (snd (tps ! j1) - t) = fst (tps ! j1) (snd (tps ! j1) - t)"
          by simp
        then have "tps' :.: j1 = fst (tps ! j1) (snd (tps ! j1) - t)"
          using * by simp
        then have "?lhs ! j = (ltransplant (tps ! j1) (tps ! j2) f t) |:=| (f ( |.| (tps ! j1 |-| t))) |-| 1"
          using assms(6) j that by simp
        then have "?lhs ! j = (ltransplant (tps ! j1) (tps ! j2) f (Suc t))"
          using ltransplant_upd assms(1) by simp
        moreover have "?rhs ! j = ltransplant (tps ! j1) (tps ! j2) f (Suc t)"
          using assms(6) that j by simp
        ultimately show ?thesis
          by simp
      next
        case j1_neq_j2: False
        then show ?thesis
        proof (cases "j = j1")
          case True
          then have "?lhs ! j = tps' ! j1 |-| 1"
            using assms j1_neq_j2 by simp
          then have "?lhs ! j = (tps ! j1 |-| t) |-| 1"
            using assms j1_neq_j2 by simp
          moreover have "?rhs ! j = tps ! j1 |-| Suc t"
            using True assms j1_neq_j2 by simp
          ultimately show ?thesis
            by simp
        next
          case False
          then have j: "j = j2"
            using j1j2 by simp
          then have "?lhs ! j = tps' ! j2 |:=| (f (tps' :.: j1)) |-| 1"
            using assms by simp
          then have "?lhs ! j = (ltransplant (tps ! j1) (tps ! j2) f t) |:=| (f (tps' :.: j1)) |-| 1"
            using assms by simp
          then have "?lhs ! j = (ltransplant (tps ! j1) (tps ! j2) f (Suc t))"
            using ltransplant_def assms ltransplant_upd by (smt (z3) j1_neq_j2 nth_list_update_eq nth_list_update_neq)
          moreover have "?rhs ! j = ltransplant (tps ! j1) (tps ! j2) f (Suc t)"
            using assms(6) that j by simp
          ultimately show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed

lemma execute_tm_trans_until_less:
  assumes "j1 < k" and "j2 < k" and "length tps = k" and "rneigh (tps ! j1) H n" and "t \<le> n"
  shows "execute (tm_trans_until j1 j2 H f) (0, tps) t =
    (0, tps[j1 := tps ! j1 |+| t, j2 := transplant (tps ! j1) (tps ! j2) f t])"
  using assms(5)
proof (induction t)
  case 0
  then show ?case
    using transplant_0 by simp
next
  case (Suc t)
  then have "t < n" by simp
  let ?M = "tm_trans_until j1 j2 H f"
  have "execute ?M (0, tps) (Suc t) = exe ?M (execute ?M (0, tps) t)"
    by simp
  also have "... = exe ?M (0, tps[j1 := tps ! j1 |+| t, j2 := transplant (tps ! j1) (tps ! j2) f t])"
      (is "_ = exe ?M (0, ?tps)")
    using Suc by simp
  also have "... = (0, ?tps[j1 := ?tps ! j1 |+| 1, j2 := ?tps ! j2 |:=| (f (?tps :.: j1)) |+| 1])"
  proof (rule exe_tm_trans_until_2[where ?k=k])
    show "j1 < k"
      using assms(1) .
    show "length (tps[j1 := tps ! j1 |+| t, j2 := transplant (tps ! j1) (tps ! j2) f t]) = k"
      using assms by simp
    show "(0, tps[j1 := tps ! j1 |+| t, j2 := transplant (tps ! j1) (tps ! j2) f t]) <.> j1 \<notin> H"
      using assms transplant_def rneigh_def \<open>t < n\<close>
      by (smt fst_conv length_list_update less_not_refl2 nth_list_update_eq nth_list_update_neq snd_conv)
  qed
  finally show ?case
    using assms transplant_upd
    by auto
      (smt add.commute fst_conv transplant_def transplant_upd less_not_refl2 list_update_overwrite list_update_swap
       nth_list_update_eq nth_list_update_neq plus_1_eq_Suc snd_conv)
qed

lemma execute_tm_ltrans_until_less:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "t \<le> n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
  shows "execute (tm_ltrans_until j1 j2 H f) (0, tps) t =
    (0, tps[j1 := tps ! j1 |-| t, j2 := ltransplant (tps ! j1) (tps ! j2) f t])"
  using assms(5)
proof (induction t)
  case 0
  then show ?case
    using ltransplant_0 by simp
next
  case (Suc t)
  then have "t < n"
    by simp
  have 1: "t < tps :#: j2"
    using assms(7) Suc by simp
  have 2: "t < tps :#: j1"
    using assms(6) Suc by simp
  let ?M = "tm_ltrans_until j1 j2 H f"
  define tps' where "tps' = tps[j1 := tps ! j1 |-| t, j2 := ltransplant (tps ! j1) (tps ! j2) f t]"
  have "execute ?M (0, tps) (Suc t) = exe ?M (execute ?M (0, tps) t)"
    by simp
  also have "... = exe ?M (0, tps')"
    using Suc tps'_def by simp
  also have "... = (0, tps'[j1 := tps' ! j1 |-| 1, j2 := tps' ! j2 |:=| (f (tps' :.: j1)) |-| 1])"
  proof (rule exe_tm_ltrans_until_2[where ?k=k])
    show "j1 < k"
      using assms(1) .
    show "length tps' = k"
      using assms tps'_def by simp
    show "(0, tps') <.> j1 \<notin> H"
      using assms ltransplant_def tps'_def lneigh_def \<open>t < n\<close>
      by (smt fst_conv length_list_update less_not_refl2 nth_list_update_eq nth_list_update_neq snd_conv)
  qed
  finally show ?case
    using tapes_ltransplant_upd[OF 1 2 assms(1,2,3) tps'_def] by simp
qed

lemma execute_tm_trans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k" and "rneigh (tps ! j1) H n"
  shows "execute (tm_trans_until j1 j2 H f) (0, tps) (Suc n) =
    (1, tps[j1 := tps ! j1 |+| n, j2 := transplant (tps ! j1) (tps ! j2) f n])"
proof -
  let ?M = "tm_trans_until j1 j2 H f"
  have "execute ?M (0, tps) (Suc n) = exe ?M (execute ?M (0, tps) n)"
    by simp
  also have "... = exe ?M (0, tps[j1 := tps ! j1 |+| n, j2 := transplant (tps ! j1) (tps ! j2) f n])"
    using execute_tm_trans_until_less[where ?t=n] assms by simp
  also have "... = (1, tps[j1 := tps ! j1 |+| n, j2 := transplant (tps ! j1) (tps ! j2) f n])"
      (is "_ = (1, ?tps)")
  proof -
    have "length ?tps = k"
      using assms(3) by simp
    moreover have "(0, ?tps) <.> j1 \<in> H"
      using rneigh_def transplant_def assms
      by (smt fst_conv length_list_update less_not_refl2 nth_list_update_eq nth_list_update_neq snd_conv)
    ultimately show ?thesis
      using exe_tm_trans_until_1 assms by simp
  qed
  finally show ?thesis by simp
qed

lemma execute_tm_ltrans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
  shows "execute (tm_ltrans_until j1 j2 H f) (0, tps) (Suc n) =
    (1, tps[j1 := tps ! j1 |-| n, j2 := ltransplant (tps ! j1) (tps ! j2) f n])"
proof -
  let ?M = "tm_ltrans_until j1 j2 H f"
  have "execute ?M (0, tps) (Suc n) = exe ?M (execute ?M (0, tps) n)"
    by simp
  also have "... = exe ?M (0, tps[j1 := tps ! j1 |-| n, j2 := ltransplant (tps ! j1) (tps ! j2) f n])"
    using execute_tm_ltrans_until_less[where ?t=n] assms by simp
  also have "... = (1, tps[j1 := tps ! j1 |-| n, j2 := ltransplant (tps ! j1) (tps ! j2) f n])"
      (is "_ = (1, ?tps)")
  proof -
    have "length ?tps = k"
      using assms(3) by simp
    moreover have "(0, ?tps) <.> j1 \<in> H"
      using lneigh_def ltransplant_def assms
      by (smt (verit, ccfv_threshold) fst_conv length_list_update less_not_refl nth_list_update_eq nth_list_update_neq snd_conv)
    ultimately show ?thesis
      using exe_tm_ltrans_until_1 assms by simp
  qed
  finally show ?thesis by simp
qed

lemma transits_tm_trans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k" and "rneigh (tps ! j1) H n"
  shows "transits (tm_trans_until j1 j2 H f)
    (0, tps)
    (Suc n)
    (1, tps[j1 := tps ! j1 |+| n, j2 := transplant (tps ! j1) (tps ! j2) f n])"
  using execute_tm_trans_until[OF assms] transitsI[of _ _ "Suc n" _ "Suc n"] by blast

lemma transits_tm_ltrans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
  shows "transits (tm_ltrans_until j1 j2 H f)
    (0, tps)
    (Suc n)
    (1, tps[j1 := tps ! j1 |-| n, j2 := ltransplant (tps ! j1) (tps ! j2) f n])"
  using execute_tm_ltrans_until[OF assms] transitsI[of _ _ "Suc n" _ "Suc n"] by blast

lemma transforms_tm_trans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k" and "rneigh (tps ! j1) H n"
  shows "transforms (tm_trans_until j1 j2 H f)
    tps
    (Suc n)
    (tps[j1 := tps ! j1 |+| n, j2 := transplant (tps ! j1) (tps ! j2) f n])"
  using tm_trans_until_def transforms_def transits_tm_trans_until[OF assms] by simp

lemma transforms_tm_ltrans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
  shows "transforms (tm_ltrans_until j1 j2 H f)
    tps
    (Suc n)
    (tps[j1 := tps ! j1 |-| n, j2 := ltransplant (tps ! j1) (tps ! j2) f n])"
  using tm_ltrans_until_def transforms_def transits_tm_ltrans_until[OF assms] by simp

corollary transforms_tm_trans_untilI [transforms_intros]:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "rneigh (tps ! j1) H n"
    and "t = Suc n"
    and "tps' = tps[j1 := tps ! j1 |+| n, j2 := transplant (tps ! j1) (tps ! j2) f n]"
  shows "transforms (tm_trans_until j1 j2 H f) tps t tps'"
  using transforms_tm_trans_until[OF assms(1-4)] assms(5,6) by simp

corollary transforms_tm_ltrans_untilI [transforms_intros]:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
    and "t = Suc n"
    and "tps' = tps[j1 := tps ! j1 |-| n, j2 := ltransplant (tps ! j1) (tps ! j2) f n]"
  shows "transforms (tm_ltrans_until j1 j2 H f) tps t tps'"
  using transforms_tm_ltrans_until[OF assms(1-6)] assms(7,8) by simp


subsubsection \<open>Copying one tape to another\<close>

text \<open>
If we set the symbol map $f$ in @{const tm_trans_until} to the identity
function, we get a Turing machine that simply makes a copy.
\<close>

definition tm_cp_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> machine" where
  "tm_cp_until j1 j2 H \<equiv> tm_trans_until j1 j2 H id"

lemma id_symbol: "\<forall>h<G. (id :: symbol \<Rightarrow> symbol) h < G"
  by simp

lemma tm_cp_until_tm:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "G \<ge> 4"
  shows "turing_machine k G (tm_cp_until j1 j2 H)"
  unfolding tm_cp_until_def using tm_trans_until_tm id_symbol assms turing_machine_def by simp

abbreviation implant :: "tape \<Rightarrow> tape \<Rightarrow> nat \<Rightarrow> tape" where
  "implant tp1 tp2 n \<equiv> transplant tp1 tp2 id n"

lemma implant: "implant tp1 tp2 n =
     (\<lambda>i. if snd tp2 \<le> i \<and> i < snd tp2 + n then fst tp1 (snd tp1 + i - snd tp2) else fst tp2 i,
      snd tp2 + n)"
  using transplant_def by auto

lemma implantI:
  assumes "tp' =
     (\<lambda>i. if snd tp2 \<le> i \<and> i < snd tp2 + n then fst tp1 (snd tp1 + i - snd tp2) else fst tp2 i,
      snd tp2 + n)"
  shows "implant tp1 tp2 n = tp'"
  using implant assms by simp

lemma fst_snd_pair: "fst t = a \<Longrightarrow> snd t = b \<Longrightarrow> t = (a, b)"
  by auto

lemma implantI':
  assumes "fst tp' =
     (\<lambda>i. if snd tp2 \<le> i \<and> i < snd tp2 + n then fst tp1 (snd tp1 + i - snd tp2) else fst tp2 i)"
    and "snd tp' = snd tp2 + n"
  shows "implant tp1 tp2 n = tp'"
  using implantI fst_snd_pair[OF assms] by simp

lemma implantI'':
  assumes "\<And>i. snd tp2 \<le> i \<and> i < snd tp2 + n \<Longrightarrow> fst tp' i = fst tp1 (snd tp1 + i - snd tp2)"
    and "\<And>i. i < snd tp2 \<Longrightarrow> fst tp' i = fst tp2 i"
    and "\<And>i. snd tp2 + n \<le> i \<Longrightarrow> fst tp' i = fst tp2 i"
  assumes "snd tp' = snd tp2 + n"
  shows "implant tp1 tp2 n = tp'"
  using assms implantI' by (meson linorder_le_less_linear)

lemma implantI''':
  assumes "\<And>i. i2 \<le> i \<and> i < i2 + n \<Longrightarrow> ys i = ys1 (i1 + i - i2)"
    and "\<And>i. i < i2 \<Longrightarrow> ys i = ys2 i"
    and "\<And>i. i2 + n \<le> i \<Longrightarrow> ys i = ys2 i"
  assumes "i = i2 + n"
  shows "implant (ys1, i1) (ys2, i2) n = (ys, i)"
  using assms implantI'' by auto

lemma implant_self: "implant tp tp n = tp |+| n"
  unfolding transplant_def by auto

lemma transforms_tm_cp_untilI [transforms_intros]:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "rneigh (tps ! j1) H n"
    and "t = Suc n"
    and "tps' = tps[j1 := tps ! j1 |+| n, j2 := implant (tps ! j1) (tps ! j2) n]"
  shows "transforms (tm_cp_until j1 j2 H) tps t tps'"
  unfolding tm_cp_until_def using transforms_tm_trans_untilI[OF assms(1-6)] by simp

lemma implant_contents:
  assumes "i > 0" and "n + (i - 1) \<le> length xs"
  shows "implant (\<lfloor>xs\<rfloor>, i) (\<lfloor>ys\<rfloor>, Suc (length ys)) n =
     (\<lfloor>ys @ (take n (drop (i - 1) xs))\<rfloor>, Suc (length ys) + n)"
     (is "?lhs = ?rhs")
proof -
  have lhs: "?lhs =
   (\<lambda>j. if Suc (length ys) \<le> j \<and> j < Suc (length ys) + n then \<lfloor>xs\<rfloor> (i + j - Suc (length ys)) else \<lfloor>ys\<rfloor> j,
    Suc (length ys) + n)"
    using implant by auto
  let ?zs = "ys @ (take n (drop (i - 1) xs))"
  have lenzs: "length ?zs = length ys + n"
    using assms by simp
  have fst_rhs: "fst ?rhs = (\<lambda>j. if j = 0 then 1 else if j \<le> length ys + n then ?zs ! (j - 1) else 0)"
    using assms by auto

  have "(\<lambda>j. if Suc (length ys) \<le> j \<and> j < Suc (length ys) + n then \<lfloor>xs\<rfloor> (i + j - Suc (length ys)) else \<lfloor>ys\<rfloor> j) =
      (\<lambda>j. if j = 0 then 1 else if j \<le> length ys + n then ?zs ! (j - 1) else 0)"
    (is "?l = ?r")
  proof
    fix j
    consider
        "j = 0"
      | "j > 0 \<and> j \<le> length ys"
      | "j > length ys \<and> j \<le> length ys + n"
      | "j > length ys + n"
      by linarith
    then show "?l j = ?r j"
    proof (cases)
      case 1
      then show ?thesis
        by simp
    next
      case 2
      then show ?thesis
        using assms contents_def by (smt (z3) Suc_diff_1 less_trans_Suc not_add_less1 not_le not_less_eq_eq nth_append)
    next
      case 3
      then have "?r j = ?zs ! (j - 1)"
        by simp
      also have "... = take n (drop (i - 1) xs) ! (j - 1 - length ys)"
        using 3 lenzs
        by (metis add.right_neutral diff_is_0_eq le_add_diff_inverse not_add_less2 not_le not_less_eq nth_append plus_1_eq_Suc)
      also have "... = take n (drop (i - 1) xs) ! (j - Suc (length ys))"
        by simp
      also have "... = xs ! (i - 1 + j - Suc (length ys))"
        using 3 assms by auto
      also have "... = \<lfloor>xs\<rfloor> (i + j - Suc (length ys))"
        using assms contents_def 3 by auto
      also have "... = ?l j"
        using 3 by simp
      finally have "?r j = ?l j" .
      then show ?thesis
        by simp
    next
      case 4
      then show ?thesis
        by simp
    qed
  qed
  then show ?thesis
    using lhs fst_rhs by simp
qed


subsubsection \<open>Moving to the next specific symbol\<close>

text \<open>
Copying a tape to itself means just moving to the right.
\<close>

definition tm_right_until :: "tapeidx \<Rightarrow> symbol set \<Rightarrow> machine" where
  "tm_right_until j H \<equiv> tm_cp_until j j H"

text \<open>
Copying a tape to itself does not change the tape. So this is a Turing machine
even for the input tape $j = 0$, unlike @{const tm_cp_until} where
the target tape cannot, in general, be the input tape.
\<close>

lemma tm_right_until_tm:
  assumes "j < k" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_right_until j H)"
  unfolding tm_right_until_def tm_cp_until_def tm_trans_until_def cmd_trans_until_def
  using assms turing_machine_def
  by auto

lemma transforms_tm_right_untilI [transforms_intros]:
  assumes "j < length tps"
    and "rneigh (tps ! j) H n"
    and "t = Suc n"
    and "tps' = (tps[j := tps ! j |+| n])"
  shows "transforms (tm_right_until j H) tps t tps'"
  using transforms_tm_cp_untilI assms implant_self tm_right_until_def
  by (metis list_update_id nth_list_update_eq)


subsubsection \<open>Translating to a constant symbol\<close>

text \<open>
Another way to specialize @{const tm_trans_until} and @{const tm_ltrans_until}
is to have a constant function $f$.
\<close>

definition tm_const_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_const_until j1 j2 H h \<equiv> tm_trans_until j1 j2 H (\<lambda>_. h)"

lemma tm_const_until_tm:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_const_until j1 j2 H h)"
  unfolding tm_const_until_def using tm_trans_until_tm assms turing_machine_def by metis

text \<open>
Continuing with our fantasy names ending in \emph{-plant}, we name the operation
@{term constplant}.
\<close>

abbreviation constplant :: "tape \<Rightarrow> symbol \<Rightarrow> nat \<Rightarrow> tape" where
  "constplant tp2 h n \<equiv> transplant (\<lambda>_. 0, 0) tp2 (\<lambda>_. h) n"

lemma constplant_transplant: "constplant tp2 h n = transplant tp1 tp2 (\<lambda>_. h) n"
  using transplant_def by simp

lemma constplant: "constplant tp2 h n =
     (\<lambda>i. if snd tp2 \<le> i \<and> i < snd tp2 + n then h else fst tp2 i,
      snd tp2 + n)"
  using transplant_def by simp

lemma transforms_tm_const_untilI [transforms_intros]:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "rneigh (tps ! j1) H n"
    and "t = Suc n"
    and "tps' = tps[j1 := tps ! j1 |+| n, j2 := constplant (tps ! j2) h n]"
  shows "transforms (tm_const_until j1 j2 H h) tps t tps'"
  unfolding tm_const_until_def using transforms_tm_trans_untilI assms constplant_transplant by metis

definition tm_lconst_until :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol set \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_lconst_until j1 j2 H h \<equiv> tm_ltrans_until j1 j2 H (\<lambda>_. h)"

lemma tm_lconst_until_tm:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_lconst_until j1 j2 H h)"
  unfolding tm_lconst_until_def using tm_ltrans_until_tm assms turing_machine_def by metis

abbreviation lconstplant :: "tape \<Rightarrow> symbol \<Rightarrow> nat \<Rightarrow> tape" where
  "lconstplant tp2 h n \<equiv> ltransplant (\<lambda>_. 0, 0) tp2 (\<lambda>_. h) n"

lemma lconstplant_ltransplant: "lconstplant tp2 h n = ltransplant tp1 tp2 (\<lambda>_. h) n"
  using ltransplant_def by simp

lemma lconstplant: "lconstplant tp2 h n =
     (\<lambda>i. if snd tp2 - n < i \<and> i \<le> snd tp2 then h else fst tp2 i,
      snd tp2 - n)"
  using ltransplant_def by simp

lemma transforms_tm_lconst_untilI [transforms_intros]:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
    and "t = Suc n"
    and "tps' = tps[j1 := tps ! j1 |-| n, j2 := lconstplant (tps ! j2) h n]"
  shows "transforms (tm_lconst_until j1 j2 H h) tps t tps'"
  unfolding tm_lconst_until_def using transforms_tm_ltrans_untilI assms lconstplant_ltransplant by metis


subsection \<open>Writing single symbols\<close>

text \<open>
The next command writes a fixed symbol $h$ to tape $j$. It does not move a tape
head.
\<close>

definition cmd_write :: "tapeidx \<Rightarrow> symbol \<Rightarrow> command" where
  "cmd_write j h rs \<equiv> (1, map (\<lambda>i. (if i = j then h else rs ! i, Stay)) [0..<length rs])"

lemma sem_cmd_write: "sem (cmd_write j h) (0, tps) = (1, tps[j := tps ! j |:=| h])"
  using cmd_write_def read_length act_Stay by (intro semI) auto

definition tm_write :: "tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_write j h \<equiv> [cmd_write j h]"

lemma tm_write_tm:
  assumes "0 < j" and "j < k" and "h < G" and "G \<ge> 4"
  shows "turing_machine k G (tm_write j h)"
  unfolding tm_write_def cmd_write_def using assms turing_machine_def by auto

lemma transforms_tm_writeI [transforms_intros]:
  assumes "tps' = tps[j := tps ! j |:=| h]"
  shows "transforms (tm_write j h) tps 1 tps'"
  unfolding tm_write_def
  using sem_cmd_write exe_lt_length assms tm_write_def transits_def transforms_def
  by auto

text \<open>
The next command writes the symbol to tape $j_2$ that results from applying a
function $f$ to the symbol read from tape $j_1$. It does not move any tape heads.
\<close>

definition cmd_trans2 :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> command" where
  "cmd_trans2 j1 j2 f rs \<equiv> (1, map (\<lambda>i. (if i = j2 then f (rs ! j1) else rs ! i, Stay)) [0..<length rs])"

lemma sem_cmd_trans2:
  assumes "j1 < length tps"
  shows "sem (cmd_trans2 j1 j2 f) (0, tps) = (1, tps[j2 := tps ! j2 |:=| (f (tps :.: j1))])"
  using cmd_trans2_def tapes_at_read assms read_length act_Stay by (intro semI) auto

definition tm_trans2 :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> machine" where
  "tm_trans2 j1 j2 f \<equiv> [cmd_trans2 j1 j2 f]"

lemma tm_trans2_tm:
  assumes "j1 < k" and "0 < j2" and "j2 < k" and "\<forall>h < G. f h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_trans2 j1 j2 f)"
  unfolding tm_trans2_def cmd_trans2_def using assms turing_machine_def by auto

lemma exe_tm_trans2:
  assumes "j1 < length tps"
  shows "exe (tm_trans2 j1 j2 f) (0, tps) = (1, tps[j2 := tps ! j2 |:=| (f (tps :.: j1))])"
  unfolding tm_trans2_def using sem_cmd_trans2 assms exe_lt_length by simp

lemma execute_tm_trans2:
  assumes "j1 < length tps"
  shows "execute (tm_trans2 j1 j2 f) (0, tps) 1 = (1, tps[j2 := tps ! j2 |:=| (f (tps :.: j1))])"
  using assms exe_tm_trans2 by simp

lemma transits_tm_trans2:
  assumes "j1 < length tps"
  shows "transits (tm_trans2 j1 j2 f) (0, tps) 1 (1, tps[j2 := tps ! j2 |:=| (f (tps :.: j1))])"
  using assms execute_tm_trans2 transits_def by auto

lemma transforms_tm_trans2:
  assumes "j1 < length tps"
  shows "transforms (tm_trans2 j1 j2 f) tps 1 (tps[j2 := tps ! j2 |:=| (f (tps :.: j1))])"
  using tm_trans2_def assms transits_tm_trans2 transforms_def by simp

lemma transforms_tm_trans2I [transforms_intros]:
  assumes "j1 < length tps" and "tps' = tps[j2 := tps ! j2 |:=| (f (tps :.: j1))]"
  shows "transforms (tm_trans2 j1 j2 f) tps 1 tps'"
  using assms transforms_tm_trans2 by simp

text \<open>
Equating the two tapes in @{const tm_trans2}, we can map a symbol in-place.
\<close>

definition tm_trans :: "tapeidx \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> machine" where
  "tm_trans j f \<equiv> tm_trans2 j j f"

lemma tm_trans_tm:
  assumes "0 < j" and "j < k" and "\<forall>h < G. f h < G" and "G \<ge> 4"
  shows "turing_machine k G (tm_trans j f)"
  unfolding tm_trans_def using tm_trans2_tm assms by simp

lemma transforms_tm_transI [transforms_intros]:
  assumes "j < length tps" and "tps' = tps[j := tps ! j |:=| (f (tps :.: j))]"
  shows "transforms (tm_trans j f) tps 1 tps'"
  using assms transforms_tm_trans2 tm_trans_def by simp

text \<open>
The next command is like the previous one, except it also moves the tape head to
the right.
\<close>

definition cmd_rtrans :: "tapeidx \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> command" where
  "cmd_rtrans j f rs \<equiv> (1, map (\<lambda>i. (if i = j then f (rs ! i) else rs ! i, if i = j then Right else Stay)) [0..<length rs])"

lemma sem_cmd_rtrans:
  assumes "j < length tps"
  shows "sem (cmd_rtrans j f) (0, tps) = (1, tps[j := tps ! j |:=| (f (tps :.: j)) |+| 1])"
  using cmd_rtrans_def tapes_at_read read_length assms act_Stay act_Right
  by (intro semI) auto

definition tm_rtrans :: "tapeidx \<Rightarrow> (symbol \<Rightarrow> symbol) \<Rightarrow> machine" where
  "tm_rtrans j f \<equiv> [cmd_rtrans j f]"

lemma tm_rtrans_tm:
  assumes "0 < j" and "j < k" and "\<forall>h<G. f h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_rtrans j f)"
  unfolding tm_rtrans_def cmd_rtrans_def using assms turing_machine_def by auto

lemma exe_tm_rtrans:
  assumes "j < length tps"
  shows "exe (tm_rtrans j f) (0, tps) = (1, tps[j := tps ! j |:=| (f (tps :.: j)) |+| 1])"
  unfolding tm_rtrans_def using sem_cmd_rtrans assms exe_lt_length by simp

lemma execute_tm_rtrans:
  assumes "j < length tps"
  shows "execute (tm_rtrans j f) (0, tps) 1 = (1, tps[j := tps ! j |:=| (f (tps :.: j)) |+| 1])"
  using assms exe_tm_rtrans by simp

lemma transits_tm_rtrans:
  assumes "j < length tps"
  shows "transits (tm_rtrans j f) (0, tps) 1 (1, tps[j := tps ! j |:=| (f (tps :.: j)) |+| 1])"
  using assms execute_tm_rtrans transits_def by auto

lemma transforms_tm_rtrans:
  assumes "j < length tps"
  shows "transforms (tm_rtrans j f) tps 1 (tps[j := tps ! j |:=| (f (tps :.: j)) |+| 1])"
  using assms transits_tm_rtrans transforms_def by (metis One_nat_def length_Cons list.size(3) tm_rtrans_def)

lemma transforms_tm_rtransI [transforms_intros]:
  assumes "j < length tps" and "tps' = tps[j := tps ! j |:=| (f (tps :.: j)) |+| 1]"
  shows "transforms (tm_rtrans j f) tps 1 tps'"
  using assms transforms_tm_rtrans by simp

text \<open>
The next command writes a fixed symbol $h$ to all tapes in the set $J$.
\<close>

definition cmd_write_many :: "tapeidx set \<Rightarrow> symbol \<Rightarrow> command" where
  "cmd_write_many J h rs \<equiv> (1, map (\<lambda>i. (if i \<in> J then h else rs ! i, Stay)) [0..<length rs])"

lemma proper_cmd_write_many: "proper_command k (cmd_write_many J h)"
  unfolding cmd_write_many_def by auto

lemma sem_cmd_write_many:
  shows "sem (cmd_write_many J h) (0, tps) =
    (1, map (\<lambda>j. if j \<in> J then tps ! j |:=| h else tps ! j) [0..<length tps])"
  using cmd_write_many_def read_length act_Stay
  by (intro semI[OF proper_cmd_write_many]) auto

definition tm_write_many :: "tapeidx set \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_write_many J h \<equiv> [cmd_write_many J h]"

lemma tm_write_many_tm:
  assumes "0 \<notin> J" and "\<forall>j\<in>J. j < k" and "h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_write_many J h)"
  unfolding tm_write_many_def cmd_write_many_def using assms turing_machine_def by auto

lemma exe_tm_write_many: "exe (tm_write_many J h) (0, tps) =
    (1, map (\<lambda>j. if j \<in> J then tps ! j |:=| h else tps ! j) [0..<length tps])"
  unfolding tm_write_many_def using sem_cmd_write_many exe_lt_length by simp

lemma execute_tm_write_many: "execute (tm_write_many J h) (0, tps) 1 =
    (1, map (\<lambda>j. if j \<in> J then tps ! j |:=| h else tps ! j) [0..<length tps])"
  using exe_tm_write_many by simp

lemma transforms_tm_write_many:
  "transforms (tm_write_many J h) tps 1 (map (\<lambda>j. if j \<in> J then tps ! j |:=| h else tps ! j) [0..<length tps])"
  using execute_tm_write_many transits_def transforms_def tm_write_many_def by auto

lemma transforms_tm_write_manyI [transforms_intros]:
  assumes "\<forall>j\<in>J. j < k"
    and "length tps = k"
    and "length tps' = k"
    and "\<And>j. j \<in> J \<Longrightarrow> tps' ! j = tps ! j |:=| h"
    and "\<And>j. j < k \<Longrightarrow> j \<notin> J \<Longrightarrow> tps' ! j = tps ! j"
  shows "transforms (tm_write_many J h) tps 1 tps'"
proof -
  have "tps' = map (\<lambda>j. if j \<in> J then tps ! j |:=| h else tps ! j) [0..<length tps]"
    using assms by (intro nth_equalityI) simp_all
  then show ?thesis
    using assms transforms_tm_write_many by auto
qed


subsection \<open>Writing a symbol multiple times\<close>

text \<open>
In this section we devise a Turing machine that writes the symbol sequence
$h^m$ with a hard-coded symbol $h$ and number $m$ to a tape. The resulting
tape is defined by the next operation:
\<close>

definition overwrite :: "tape \<Rightarrow> symbol \<Rightarrow> nat \<Rightarrow> tape" where
  "overwrite tp h m \<equiv> (\<lambda>i. if snd tp \<le> i \<and> i < snd tp + m then h else fst tp i, snd tp + m)"

lemma overwrite_0: "overwrite tp h 0 = tp"
proof -
  have "snd (overwrite tp h 0) = snd tp"
    unfolding overwrite_def by simp
  moreover have "fst (overwrite tp h 0) = fst tp"
    unfolding overwrite_def by auto
  ultimately show ?thesis
    using prod_eqI by blast
qed

lemma overwrite_upd: "(overwrite tp h t) |:=| h |+| 1 = overwrite tp h (Suc t)"
  using overwrite_def by auto

lemma overwrite_upd':
  assumes "j < length tps" and "tps' = tps[j := overwrite (tps ! j) h t]"
  shows "(tps[j := overwrite (tps ! j) h t])[j := tps' ! j |:=| h |+| 1] =
    tps[j := overwrite (tps ! j) h (Suc t)]"
  using assms overwrite_upd by simp

text \<open>
The next command writes the symbol $h$ to the tape $j$ and moves the tape head
to the right.
\<close>

definition cmd_char :: "tapeidx \<Rightarrow> symbol \<Rightarrow> command" where
  "cmd_char j z = cmd_rtrans j (\<lambda>_. z)"

lemma turing_command_char:
  assumes "0 < j" and "j < k" and "h < G"
  shows "turing_command k 1 G (cmd_char j h)"
  unfolding cmd_char_def cmd_rtrans_def using assms by auto

definition tm_char :: "tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_char j z \<equiv> [cmd_char j z]"

lemma tm_char_tm:
  assumes "0 < j" and "j < k" and "G \<ge> 4" and "z < G"
  shows "turing_machine k G (tm_char j z)"
  using assms turing_command_char tm_char_def by auto

lemma transforms_tm_charI [transforms_intros]:
  assumes "j < length tps" and "tps' = tps[j := tps ! j |:=| z |+| 1]"
  shows "transforms (tm_char j z) tps 1 tps'"
  using assms transforms_tm_rtransI tm_char_def cmd_char_def tm_rtrans_def by metis

lemma sem_cmd_char:
  assumes "j < length tps"
  shows "sem (cmd_char j h) (0, tps) = (1, tps[j := tps ! j |:=| h |+| 1])"
  using cmd_char_def cmd_rtrans_def tapes_at_read read_length assms act_Right
  by (intro semI) auto

text \<open>
The next TM is a sequence of $m$ @{const cmd_char} commands properly relocated.
It writes a sequence of $m$ times the symbol $h$ to tape $j$.
\<close>

definition tm_write_repeat :: "tapeidx \<Rightarrow> symbol \<Rightarrow> nat \<Rightarrow> machine" where
  "tm_write_repeat j h m \<equiv> map (\<lambda>i. relocate_cmd i (cmd_char j h)) [0..<m]"

lemma tm_write_repeat_tm:
  assumes "0 < j" and "j < k" and "h < G" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_write_repeat j h m)"
proof
  let ?M = "tm_write_repeat j h m"
  show "2 \<le> k" and "4 \<le> G"
    using assms(4,5) .
  show "turing_command k (length ?M) G (?M ! i)" if "i < length ?M" for i
  proof -
    have "?M ! i = relocate_cmd i (cmd_char j h)"
      using that tm_write_repeat_def by simp
    then have "turing_command k (1 + i) G (?M ! i)"
      using assms turing_command_char turing_command_relocate_cmd by metis
    then show ?thesis
      using turing_command_mono that by simp
  qed
qed

lemma exe_tm_write_repeat:
  assumes "j < length tps" and "q < m"
  shows "exe (tm_write_repeat j h m) (q, tps) = (Suc q, tps[j := tps ! j |:=| h |+| 1])"
  using sem_cmd_char assms sem sem_relocate_cmd tm_write_repeat_def by (auto simp add: exe_lt_length)

lemma execute_tm_write_repeat:
  assumes "j < length tps" and "t \<le> m"
  shows "execute (tm_write_repeat j h m) (0, tps) t = (t, tps[j := overwrite (tps ! j) h t])"
  using assms(2)
proof (induction t)
  case 0
  then show ?case using overwrite_0 by simp
next
  case (Suc t)
  then have "t < m" by simp
  have "execute (tm_write_repeat j h m) (0, tps) (Suc t) = exe (tm_write_repeat j h m) (execute (tm_write_repeat j h m) (0, tps) t)"
    by simp
  also have "... = exe (tm_write_repeat j h m) (t, tps[j := overwrite (tps ! j) h t])"
    using Suc by simp
  also have "... = (Suc t, tps[j := overwrite (tps ! j) h (Suc t)])"
    using `t < m` exe_tm_write_repeat assms overwrite_upd' by simp
  finally show ?case .
qed

lemma transforms_tm_write_repeatI [transforms_intros]:
  assumes "j < length tps" and "tps' = tps[j := overwrite (tps ! j) h m]"
  shows "transforms (tm_write_repeat j h m) tps m tps'"
  using assms execute_tm_write_repeat transits_def transforms_def tm_write_repeat_def by auto


subsection \<open>Moving to the start of the tape\<close>

text \<open>
The next command moves the head on tape $j$ to the left until it reaches
a symbol from the set $H$:
\<close>

definition cmd_left_until :: "symbol set \<Rightarrow> tapeidx \<Rightarrow> command" where
  "cmd_left_until H j rs \<equiv>
    if rs ! j \<in> H
    then (1, map (\<lambda>r. (r, Stay)) rs)
    else (0, map (\<lambda>i. (rs ! i, if i = j then Left else Stay)) [0..<length rs])"

lemma sem_cmd_left_until_1:
  assumes "j < k" and "length tps = k" and "(0, tps) <.> j \<in> H"
  shows "sem (cmd_left_until H j) (0, tps) = (1, tps)"
  using cmd_left_until_def tapes_at_read read_length assms act_Stay
  by (intro semI) auto

lemma sem_cmd_left_until_2:
  assumes "j < k" and "length tps = k" and "(0, tps) <.> j \<notin> H"
  shows "sem (cmd_left_until H j) (0, tps) = (0, tps[j := tps ! j |-| 1])"
  using cmd_left_until_def tapes_at_read read_length assms act_Stay act_Left
  by (intro semI) auto

definition tm_left_until :: "symbol set \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_left_until H j \<equiv> [cmd_left_until H j]"

lemma tm_left_until_tm:
  assumes "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_left_until H j)"
  unfolding tm_left_until_def cmd_left_until_def using assms turing_machine_def by auto

text \<open>
A \emph{begin tape} for a set of symbols has one of these symbols only in cell
zero.  It generalizes the concept of clean tapes, where the set of symbols is
$\{\triangleright\}$.
\<close>

definition begin_tape :: "symbol set \<Rightarrow> tape \<Rightarrow> bool" where
  "begin_tape H tp \<equiv> \<forall>i. fst tp i \<in> H \<longleftrightarrow> i = 0"

lemma begin_tapeI:
  assumes "fst tp 0 \<in> H" and "\<And>i. i > 0 \<Longrightarrow> fst tp i \<notin> H"
  shows "begin_tape H tp"
  unfolding begin_tape_def using assms by auto

lemma exe_tm_left_until_1:
  assumes "j < length tps" and "(0, tps) <.> j \<in> H"
  shows "exe (tm_left_until H j) (0, tps) = (1, tps)"
  using tm_left_until_def assms exe_lt_length sem_cmd_left_until_1 by auto

lemma exe_tm_left_until_2:
  assumes "j < length tps" and "(0, tps) <.> j \<notin> H"
  shows "exe (tm_left_until H j) (0, tps) = (0, tps[j := tps ! j |-| 1])"
  using tm_left_until_def assms exe_lt_length sem_cmd_left_until_2 by auto

text \<open>
We do not show the semantics of @{const tm_left_until} for the general case, but
only for when applied to begin tapes.
\<close>

lemma execute_tm_left_until_less:
  assumes "j < length tps" and "begin_tape H (tps ! j)" and "t \<le> tps :#: j"
  shows "execute (tm_left_until H j) (0, tps) t = (0, tps[j := tps ! j |-| t])"
  using assms(3)
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  then have "fst (tps ! j) (snd (tps ! j) - t) \<notin> H"
    using assms begin_tape_def by simp
  then have neq_0: "fst (tps ! j |-| t) (snd (tps ! j |-| t)) \<notin> H"
    by simp
  have "execute (tm_left_until H j) (0, tps) (Suc t) = exe (tm_left_until H j) (execute (tm_left_until H j) (0, tps) t)"
    by simp
  also have "... = exe (tm_left_until H j) (0, tps[j := tps ! j |-| t])"
    using Suc by simp
  also have "... = (0, tps[j := tps ! j |-| (Suc t)])"
    using neq_0 exe_tm_left_until_2 assms by simp
  finally show ?case by simp
qed

lemma execute_tm_left_until:
  assumes "j < length tps" and "begin_tape H (tps ! j)"
  shows "execute (tm_left_until H j) (0, tps) (Suc (tps :#: j)) = (1, tps[j := tps ! j |#=| 0])"
  using assms begin_tape_def exe_tm_left_until_1 execute_tm_left_until_less by simp

lemma transits_tm_left_until:
  assumes "j < length tps" and "begin_tape H (tps ! j)"
  shows "transits (tm_left_until H j) (0, tps) (Suc (tps :#: j)) (1, tps[j := tps ! j |#=| 0])"
  using execute_imp_transits[OF execute_tm_left_until[OF assms]] by simp

lemma transforms_tm_left_until:
  assumes "j < length tps" and "begin_tape H (tps ! j)"
  shows "transforms (tm_left_until H j) tps (Suc (tps :#: j)) (tps[j := tps ! j |#=| 0])"
  using tm_left_until_def transforms_def transits_tm_left_until[OF assms] by simp

text \<open>
The most common case is $H = \{\triangleright\}$, which means the Turing machine
moves the tape head left to the closest start symbol. On clean tapes it moves
the tape head to the leftmost cell of the tape.
\<close>

definition tm_start :: "tapeidx \<Rightarrow> machine" where
  "tm_start \<equiv> tm_left_until {1}"

lemma tm_start_tm:
  assumes "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_start j)"
  unfolding tm_start_def using assms tm_left_until_tm by simp

lemma transforms_tm_start:
  assumes "j < length tps" and "clean_tape (tps ! j)"
  shows "transforms (tm_start j) tps (Suc (tps :#: j)) (tps[j := tps ! j |#=| 0])"
  using tm_start_def assms transforms_tm_left_until begin_tape_def clean_tape_def by (metis insertCI singletonD)

lemma transforms_tm_startI [transforms_intros]:
  assumes "j < length tps" and "clean_tape (tps ! j)"
    and "t = Suc (tps :#: j)"
    and "tps' = tps[j := tps ! j |#=| 0]"
  shows "transforms (tm_start j) tps t tps'"
  using transforms_tm_start assms by simp

text \<open>
The next Turing machine is the first instance in which we use the $;;$ operator
with concrete Turing machines. It is also the first time we use the proof method
@{method tform} for @{const transforms}. The TM performs a ``carriage return''
on a clean tape, that is, it moves to the first non-start symbol.
\<close>

definition tm_cr :: "tapeidx \<Rightarrow> machine" where
  "tm_cr j \<equiv> tm_start j ;; tm_right j"

lemma tm_cr_tm: "k \<ge> 2 \<Longrightarrow> G \<ge> 4 \<Longrightarrow> turing_machine k G (tm_cr j)"
  using turing_machine_sequential_turing_machine by (simp add: tm_cr_def tm_right_tm tm_start_tm)

lemma transforms_tm_crI [transforms_intros]:
  assumes "j < length tps"
    and "clean_tape (tps ! j)"
    and "t = tps :#: j + 2"
    and "tps' = tps[j := tps ! j |#=| 1]"
  shows "transforms (tm_cr j) tps t tps'"
  unfolding tm_cr_def by (tform tps: assms)


subsection \<open>Erasing a tape\<close>

text \<open>
The next Turing machine overwrites all but the start symbol with blanks. It
first performs a carriage return and then writes blanks until it reaches a
blank. This only works as intended if there are no gaps, that is, blanks between
non-blank symbols.
\<close>

definition tm_erase :: "tapeidx \<Rightarrow> machine" where
  "tm_erase j \<equiv> tm_cr j ;; tm_const_until j j {\<box>} \<box>"

lemma tm_erase_tm: "G \<ge> 4 \<Longrightarrow> 0 < j \<Longrightarrow> j < k \<Longrightarrow> turing_machine k G (tm_erase j)"
  unfolding tm_erase_def using tm_cr_tm tm_const_until_tm by simp

lemma transforms_tm_eraseI [transforms_intros]:
  assumes "j < length tps"
    and "proper_symbols zs"
    and "tps ::: j = \<lfloor>zs\<rfloor>"
    and "t = tps :#: j + length zs + 3"
    and "tps' = tps[j := (\<lfloor>[]\<rfloor>, Suc (length zs))]"
  shows "transforms (tm_erase j) tps t tps'"
  unfolding tm_erase_def
proof (tform tps: assms time: assms(4))
  show "clean_tape (tps ! j)"
    using assms contents_clean_tape' by simp
  show "rneigh (tps[j := tps ! j |#=| 1] ! j) {\<box>} (length zs)"
    using assms contents_clean_tape' by (intro rneighI) auto
  show "tps' = tps
    [j := tps ! j |#=| 1, j := tps[j := tps ! j |#=| 1] ! j |+| length zs,
     j := constplant (tps[j := tps ! j |#=| 1] ! j) \<box> (length zs)]"
  proof -
    have "(\<lfloor>[]\<rfloor>, Suc (length zs)) = constplant (\<lfloor>zs\<rfloor>, Suc 0) \<box> (length zs)"
      using transplant_def contents_def by auto
    then show ?thesis
      using assms by simp
  qed
qed

text \<open>
The next TM returns to the leftmost blank symbol after erasing the tape.
\<close>

definition tm_erase_cr :: "tapeidx \<Rightarrow> machine" where
  "tm_erase_cr j \<equiv> tm_erase j ;; tm_cr j"

lemma tm_erase_cr_tm:
  assumes "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_erase_cr j)"
  using tm_erase_cr_def tm_cr_tm tm_erase_tm assms by simp

lemma transforms_tm_erase_crI [transforms_intros]:
  assumes "j < length tps"
    and "proper_symbols zs"
    and "tps ::: j = \<lfloor>zs\<rfloor>"
    and "t = tps :#: j + 2 * length zs + 6"
    and "tps' = tps[j := (\<lfloor>[]\<rfloor>, 1)]"
  shows "transforms (tm_erase_cr j) tps t tps'"
  unfolding tm_erase_cr_def
  by (tform tps: assms time: assms(4))


subsection \<open>Writing a symbol sequence\<close>

text \<open>
The Turing machine in this section writes a hard-coded symbol sequence to a
tape. It is like @{const tm_write_repeat} except with an arbitrary symbol
sequence.
\<close>

fun tm_print :: "tapeidx \<Rightarrow> symbol list \<Rightarrow> machine" where
  "tm_print j [] = []" |
  "tm_print j (z # zs) = tm_char j z ;; tm_print j zs"

lemma tm_print_tm:
  assumes "0 < j" and "j < k" and "G \<ge> 4" and "\<forall>i<length zs. zs ! i < G"
  shows "turing_machine k G (tm_print j zs)"
  using assms(4)
proof (induction zs)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons z zs)
  then have "turing_machine k G (tm_char j z)"
    using assms tm_char_tm by auto
  then show ?case
    using assms Cons by fastforce
qed

text \<open>
The result of writing the symbols @{term zs} to a tape @{term tp}:
\<close>

definition inscribe :: "tape \<Rightarrow> symbol list \<Rightarrow> tape" where
  "inscribe tp zs \<equiv>
     (\<lambda>i. if snd tp \<le> i \<and> i < snd tp + length zs then zs ! (i - snd tp) else fst tp i,
      snd tp + length zs)"

lemma inscribe_Nil: "inscribe tp [] = tp"
proof -
  have "(\<lambda>i. if snd tp \<le> i \<and> i < snd tp then [] ! (i - snd tp) else fst tp i) = fst tp"
    by auto
  then show ?thesis
    unfolding inscribe_def by simp
qed

lemma inscribe_Cons: "inscribe ((fst tp)(snd tp := z), Suc (snd tp)) zs = inscribe tp (z # zs)"
  using inscribe_def by auto

lemma inscribe_contents: "inscribe (\<lfloor>ys\<rfloor>, Suc (length ys)) zs = (\<lfloor>ys @ zs\<rfloor>, Suc (length ys + length zs))"
  (is "?lhs = ?rhs")
proof
  show "snd ?lhs = snd ?rhs"
    using inscribe_def contents_def by simp
  show "fst ?lhs = fst ?rhs"
  proof
    fix i :: nat
    consider
        "i = 0"
      | "0 < i \<and> i < Suc (length ys)"
      | "Suc (length ys) \<le> i \<and> i < Suc (length ys + length zs)"
      | "Suc (length ys + length zs) \<le> i"
      by linarith
    then show "fst ?lhs i = fst ?rhs i"
    proof (cases)
      case 1
      then show ?thesis
        using inscribe_def contents_def by simp
    next
      case 2
      then have "fst ?lhs i = \<lfloor>ys\<rfloor> i"
        using inscribe_def by simp
      then have lhs: "fst ?lhs i = ys ! (i - 1)"
        using 2 contents_def by simp
      have "fst ?rhs i = (ys @ zs) ! (i - 1)"
        using 2 contents_def by simp
      then have "fst ?rhs i = ys ! (i - 1)"
        using 2 by (metis Suc_diff_1 not_less_eq nth_append)
      then show ?thesis
        using lhs by simp
    next
      case 3
      then show ?thesis
        using contents_def inscribe_def
        by (smt (verit, del_insts) One_nat_def add.commute diff_Suc_eq_diff_pred fst_conv length_append less_Suc0
         less_Suc_eq_le less_diff_conv2 nat.simps(3) not_less_eq nth_append plus_1_eq_Suc snd_conv)
    next
      case 4
      then show ?thesis
        using contents_def inscribe_def
        by simp
    qed
  qed
qed

lemma inscribe_contents_Nil: "inscribe (\<lfloor>[]\<rfloor>, Suc 0) zs = (\<lfloor>zs\<rfloor>, Suc (length zs))"
  using inscribe_def contents_def by auto

lemma transforms_tm_print:
  assumes "j < length tps"
  shows "transforms (tm_print j zs) tps (length zs) (tps[j := inscribe (tps ! j) zs])"
  using assms
proof (induction zs arbitrary: tps)
  case Nil
  then show ?case
    using inscribe_Nil transforms_Nil by simp
next
  case (Cons z zs)
  have "transforms (tm_char j z ;; tm_print j zs) tps (length (z # zs)) (tps[j := inscribe (tps ! j) (z # zs)])"
  proof (tform tps: Cons)
    let ?tps = "tps[j := tps ! j |:=| z |+| 1]"
    have "transforms (tm_print j zs) ?tps (length zs) (?tps[j := inscribe (?tps ! j) zs])"
      using Cons by (metis length_list_update)
    moreover have "(?tps[j := inscribe (?tps ! j) zs]) = (tps[j := inscribe (tps ! j) (z # zs)])"
      using inscribe_Cons Cons.prems by simp
    ultimately show "transforms (tm_print j zs) ?tps (length zs) (tps[j := inscribe (tps ! j) (z # zs)])"
      by simp
  qed
  then show "transforms (tm_print j (z # zs)) tps (length (z # zs)) (tps[j := inscribe (tps ! j) (z # zs)])"
    by simp
qed

lemma transforms_tm_printI [transforms_intros]:
  assumes "j < length tps" and "tps' = (tps[j := inscribe (tps ! j) zs])"
  shows "transforms (tm_print j zs) tps (length zs) tps'"
  using assms transforms_tm_print by simp


subsection \<open>Setting the tape contents to a symbol sequence\<close>

text \<open>
The following Turing machine erases the tape, then prints a hard-coded
symbol sequence, and then performs a carriage return. It thus sets
the tape contents to the symbol sequence.
\<close>

definition tm_set :: "tapeidx \<Rightarrow> symbol list \<Rightarrow> machine" where
  "tm_set j zs \<equiv> tm_erase_cr j ;; tm_print j zs ;; tm_cr j"

lemma tm_set_tm:
  assumes "0 < j" and "j < k" and "G \<ge> 4" and "\<forall>i<length zs. zs ! i < G"
  shows "turing_machine k G (tm_set j zs)"
  unfolding tm_set_def using assms tm_print_tm tm_erase_cr_tm tm_cr_tm by simp

lemma transforms_tm_setI [transforms_intros]:
  assumes "j < length tps"
    and "clean_tape (tps ! j)"
    and "proper_symbols ys"
    and "proper_symbols zs"
    and "tps ::: j = \<lfloor>ys\<rfloor>"
    and "t = 8 + tps :#: j + 2 * length ys + Suc (2 * length zs)"
    and "tps' = tps[j := (\<lfloor>zs\<rfloor>, 1)]"
  shows "transforms (tm_set j zs) tps t tps'"
  unfolding tm_set_def
proof (tform tps: assms(1-5))
  show "clean_tape
     (tps[j := (\<lfloor>[]\<rfloor>, 1),
          j := inscribe (tps[j := (\<lfloor>[]\<rfloor>, 1)] ! j) zs] ! j)"
    using assms inscribe_contents_Nil clean_contents_proper[OF assms(4)] by simp
  show "tps' = tps
      [j := (\<lfloor>[]\<rfloor>, 1), j := inscribe (tps[j := (\<lfloor>[]\<rfloor>, 1)] ! j) zs,
       j := tps[j := (\<lfloor>[]\<rfloor>, 1), j := inscribe (tps[j := (\<lfloor>[]\<rfloor>, 1)] ! j) zs] ! j |#=| 1]"
    using assms inscribe_def clean_tape_def assms contents_def inscribe_contents_Nil by simp
  show "t = tps :#: j + 2 * length ys + 6 + length zs +
      (tps[j := (\<lfloor>[]\<rfloor>, 1),
           j := inscribe (tps[j := (\<lfloor>[]\<rfloor>, 1)] ! j) zs] :#: j + 2)"
    using assms inscribe_def by simp
qed


subsection \<open>Comparing two tapes\label{s:tm-elementary-comparing}\<close>

text \<open>
The next Turing machine compares the contents of two tapes $j_1$ and $j_2$ and
writes to tape $j_3$ either a @{text \<one>} or a @{text \<box>} depending on whether the
tapes are equal or not. The next command does all the work. It scans both tapes
left to right and halts if it encounters a blank on both tapes, which means the
tapes are equal, or two different symbols, which means the tapes are unequal. It
only works for contents without blanks.
\<close>

definition cmd_cmp :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> command" where
  "cmd_cmp j1 j2 j3 rs \<equiv>
    if rs ! j1 \<noteq> rs ! j2
    then (1, map (\<lambda>i. (if i = j3 then \<box> else rs ! i, Stay)) [0..<length rs])
    else if rs ! j1 = \<box> \<or> rs ! j2 = \<box>
      then (1, map (\<lambda>i. (if i = j3 then \<one> else rs ! i, Stay)) [0..<length rs])
      else (0, map (\<lambda>i. (rs ! i, if i = j1 \<or> i = j2 then Right else Stay)) [0..<length rs])"

lemma sem_cmd_cmp1:
  assumes "length tps = k"
    and "j1 < k" and "j2 < k" and "j3 < k"
    and "tps :.: j1 \<noteq> tps :.: j2"
  shows "sem (cmd_cmp j1 j2 j3) (0, tps) = (1, tps[j3 := tps ! j3 |:=| \<box>])"
  unfolding cmd_cmp_def using assms tapes_at_read' act_Stay read_length by (intro semI) auto

lemma sem_cmd_cmp2:
  assumes "length tps = k"
    and "j1 < k" and "j2 < k" and "j3 < k"
    and "tps :.: j1 = tps :.: j2" and "tps :.: j1 = \<box> \<or> tps :.: j2 = \<box>"
  shows "sem (cmd_cmp j1 j2 j3) (0, tps) = (1, tps[j3 := tps ! j3 |:=| \<one>])"
  unfolding cmd_cmp_def using assms tapes_at_read' act_Stay read_length by (intro semI) auto

lemma sem_cmd_cmp3:
  assumes "length tps = k"
    and "j2 \<noteq> j3" and "j1 \<noteq> j3" and "j1 < k" and "j2 < k" and "j3 < k"
    and "tps :.: j1 = tps :.: j2" and "tps :.: j1 \<noteq> \<box> \<and> tps :.: j2 \<noteq> \<box>"
  shows "sem (cmd_cmp j1 j2 j3) (0, tps) = (0, tps[j1 := tps ! j1 |+| 1, j2 := tps ! j2 |+| 1])"
proof (rule semI)
  show "proper_command k (cmd_cmp j1 j2 j3)"
    using cmd_cmp_def by simp
  show "length tps = k"
    using assms(1) .
  show "length (tps[j1 := tps ! j1 |+| 1, j2 := tps ! j2 |+| 1]) = k"
    using assms(1) by simp
  show "fst ((cmd_cmp j1 j2 j3) (read tps)) = 0"
    unfolding cmd_cmp_def using assms tapes_at_read' by simp
  show "act (cmd_cmp j1 j2 j3 (read tps) [!] j) (tps ! j) = tps[j1 := tps ! j1 |+| 1, j2 := tps ! j2 |+| 1] ! j"
      if "j < k" for j
    unfolding cmd_cmp_def
    using assms tapes_at_read' that act_Stay act_Right read_length
    by (cases "j1 = j2") simp_all
qed

definition tm_cmp :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_cmp j1 j2 j3 \<equiv> [cmd_cmp j1 j2 j3]"

lemma tm_cmp_tm:
  assumes "k \<ge> 2" and "j3 > 0" and "G \<ge> 4"
  shows "turing_machine k G (tm_cmp j1 j2 j3)"
  unfolding tm_cmp_def cmd_cmp_def using assms turing_machine_def by auto

lemma exe_cmd_cmp1:
  assumes "length tps = k"
    and "j1 < k" and "j2 < k" and "j3 < k"
    and "tps :.: j1 \<noteq> tps :.: j2"
  shows "exe (tm_cmp j1 j2 j3) (0, tps) = (1, tps[j3 := tps ! j3 |:=| \<box>])"
  using tm_cmp_def assms exe_lt_length sem_cmd_cmp1 by simp

lemma exe_cmd_cmp2:
  assumes "length tps = k"
    and "j1 < k" and "j2 < k" and "j3 < k"
    and "tps :.: j1 = tps :.: j2" and "tps :.: j1 = \<box> \<or> tps :.: j2 = \<box>"
  shows "exe (tm_cmp j1 j2 j3) (0, tps) = (1, tps[j3 := tps ! j3 |:=| \<one>])"
  using tm_cmp_def assms exe_lt_length sem_cmd_cmp2 by simp

lemma exe_cmd_cmp3:
  assumes "length tps = k"
    and "j2 \<noteq> j3" and "j1 \<noteq> j3" and "j1 < k" and "j2 < k" and "j3 < k"
    and "tps :.: j1 = tps :.: j2" and "tps :.: j1 \<noteq> \<box> \<and> tps :.: j2 \<noteq> \<box>"
  shows "exe (tm_cmp j1 j2 j3) (0, tps) = (0, tps[j1 := tps ! j1 |+| 1, j2 := tps ! j2 |+| 1])"
  using tm_cmp_def assms exe_lt_length sem_cmd_cmp3 by simp

lemma execute_tm_cmp_eq:
  fixes tps :: "tape list"
  assumes "length tps = k"
    and "j2 \<noteq> j3" and "j1 \<noteq> j3" and "j1 < k" and "j2 < k" and "j3 < k"
    and "proper_symbols xs"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>xs\<rfloor>, 1)"
  shows "execute (tm_cmp j1 j2 j3) (0, tps) (Suc (length xs)) =
      (1, tps[j1 := tps ! j1 |+| length xs, j2 := tps ! j2 |+| length xs, j3 := tps ! j3 |:=| \<one>])"
proof -
  have "execute (tm_cmp j1 j2 j3) (0, tps) t = (0, tps[j1 := tps ! j1 |+| t, j2 := tps ! j2 |+| t])"
      if "t \<le> length xs" for t
    using that
  proof (induction t)
    case 0
    then show ?case
      by simp
  next
    case (Suc t)
    then have t_less: "t < length xs"
      by simp
    have "execute (tm_cmp j1 j2 j3) (0, tps) (Suc t) = exe (tm_cmp j1 j2 j3) (execute (tm_cmp j1 j2 j3) (0, tps) t)"
      by simp
    also have "... = exe (tm_cmp j1 j2 j3) (0, tps[j1 := tps ! j1 |+| t, j2 := tps ! j2 |+| t])"
        (is "_ = exe _ (0, ?tps)")
      using Suc by simp
    also have "... = (0, ?tps[j1 := ?tps ! j1 |+| 1, j2 := ?tps ! j2 |+| 1])"
    proof -
      have 1: "?tps :.: j1 = xs ! t"
        using assms(1,2,4,8) t_less Suc.prems contents_inbounds
        by (metis (no_types, lifting) diff_Suc_1 fst_conv length_list_update nth_list_update_eq
          nth_list_update_neq plus_1_eq_Suc snd_conv zero_less_Suc)
      moreover have 2: "?tps :.: j2 = xs ! t"
        using t_less assms(1,5,9) by simp
      ultimately have "?tps :.: j1 = ?tps :.: j2"
        by simp
      moreover have "?tps :.: j1 \<noteq> 0 \<and> ?tps :.: j2 \<noteq> 0"
        using 1 2 assms(7) t_less by auto
      moreover have "length ?tps = k"
        using assms(1) by simp
      ultimately show ?thesis
        using assms exe_cmd_cmp3 by blast
    qed
    also have "... = (0, tps[j1 := tps ! j1 |+| Suc t, j2 := tps ! j2 |+| Suc t])"
      using assms
      by (smt (z3) Suc_eq_plus1 add.commute fst_conv list_update_overwrite list_update_swap
        nth_list_update_eq nth_list_update_neq snd_conv)
    finally show ?case
      by simp
  qed
  then have "execute (tm_cmp j1 j2 j3) (0, tps) (length xs) =
      (0, tps[j1 := tps ! j1 |+| length xs, j2 := tps ! j2 |+| length xs])"
    by simp
  then have "execute (tm_cmp j1 j2 j3) (0, tps) (Suc (length xs)) =
      exe (tm_cmp j1 j2 j3) (0, tps[j1 := tps ! j1 |+| length xs, j2 := tps ! j2 |+| length xs])"
      (is "_ = exe _ (0, ?tps)")
    by simp
  also have "... = (1, ?tps[j3 := ?tps ! j3 |:=| \<one>])"
  proof -
    have 1: "?tps :.: j1 = 0"
      using assms(1,4,8) contents_outofbounds
      by (metis fst_conv length_list_update lessI nth_list_update_eq nth_list_update_neq plus_1_eq_Suc snd_conv)
    moreover have 2: "?tps :.: j2 = 0"
      using assms(1,5,9) by simp
    ultimately have "?tps :.: j1 = ?tps :.: j2" "?tps :.: j1 = \<box> \<or> ?tps :.: j2 = \<box>"
      by simp_all
    moreover have "length ?tps = k"
      using assms(1) by simp
    ultimately show ?thesis
      using assms exe_cmd_cmp2 by blast
  qed
  also have "... = (1, tps[j1 := tps ! j1 |+| length xs, j2 := tps ! j2 |+| length xs, j3 := tps ! j3 |:=| \<one>])"
    using assms by simp
  finally show ?thesis .
qed

lemma ex_contents_neq:
  assumes "proper_symbols xs" and "proper_symbols ys" and "xs \<noteq> ys"
  shows "\<exists>m. m \<le> Suc (min (length xs) (length ys)) \<and> \<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m"
proof -
  consider "length xs < length ys" | "length xs = length ys" | "length xs > length ys"
    by linarith
  then show ?thesis
  proof (cases)
    case 1
    let ?m = "length xs"
    have "\<lfloor>xs\<rfloor> (Suc ?m) = \<box>"
      by simp
    moreover have "\<lfloor>ys\<rfloor> (Suc ?m) \<noteq> \<box>"
      using 1 assms(2) by (simp add: proper_symbols_ne0)
    ultimately show ?thesis
      using 1 by auto
  next
    case 2
    then have "\<exists>i<length xs. xs ! i \<noteq> ys ! i"
      using assms by (meson list_eq_iff_nth_eq)
    then show ?thesis
      using contents_def 2 by auto
  next
    case 3
    let ?m = "length ys"
    have "\<lfloor>ys\<rfloor> (Suc ?m) = \<box>"
      by simp
    moreover have "\<lfloor>xs\<rfloor> (Suc ?m) \<noteq> \<box>"
      using 3 assms(1) by (simp add: proper_symbols_ne0)
    ultimately show ?thesis
      using 3 by auto
  qed
qed

lemma execute_tm_cmp_neq:
  fixes tps :: "tape list"
  assumes "length tps = k"
    and "j1 \<noteq> j2" and "j2 \<noteq> j3" and "j1 \<noteq> j3" and "j1 < k" and "j2 < k" and "j3 < k"
    and "proper_symbols xs"
    and "proper_symbols ys"
    and "xs \<noteq> ys"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "m = (LEAST m. m \<le> Suc (min (length xs) (length ys)) \<and> \<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m)"
  shows "execute (tm_cmp j1 j2 j3) (0, tps) m =
    (1, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1), j3 := tps ! j3 |:=| \<box>])"
proof -
  have neq: "\<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m"
    using ex_contents_neq[OF assms(8-10)] assms(13) by (metis (mono_tags, lifting) LeastI_ex)
  have eq: "\<lfloor>xs\<rfloor> i = \<lfloor>ys\<rfloor> i" if "i < m" for i
    using ex_contents_neq[OF assms(8-10)] assms(13) not_less_Least that by (smt (z3) Least_le le_trans less_imp_le_nat)
  have "m > 0"
    using neq contents_def gr0I by metis

  have "execute (tm_cmp j1 j2 j3) (0, tps) t = (0, tps[j1 := tps ! j1 |+| t, j2 := tps ! j2 |+| t])"
      if "t < m" for t
    using that
  proof (induction t)
    case 0
    then show ?case
      by simp
  next
    case (Suc t)
    have "execute (tm_cmp j1 j2 j3) (0, tps) (Suc t) = exe (tm_cmp j1 j2 j3) (execute (tm_cmp j1 j2 j3) (0, tps) t)"
      by simp
    also have "... = exe (tm_cmp j1 j2 j3) (0, tps[j1 := tps ! j1 |+| t, j2 := tps ! j2 |+| t])"
        (is "_ = exe _ (0, ?tps)")
      using Suc by simp
    also have "... = (0, ?tps[j1 := ?tps ! j1 |+| 1, j2 := ?tps ! j2 |+| 1])"
    proof -
      have 1: "?tps :.: j1 = \<lfloor>xs\<rfloor> (Suc t)"
        using assms(1,2,5,11) by simp
      moreover have 2: "?tps :.: j2 = \<lfloor>ys\<rfloor> (Suc t)"
        using assms(1,6,12) by simp
      ultimately have "?tps :.: j1 = ?tps :.: j2"
        using Suc eq by simp
      moreover from this have "?tps :.: j1 \<noteq> \<box> \<and> ?tps :.: j2 \<noteq> \<box>"
        using 1 2 assms neq Suc.prems contents_def
        by (smt (z3) Suc_leI Suc_le_lessD Suc_lessD diff_Suc_1 le_trans less_nat_zero_code zero_less_Suc)
      moreover have "length ?tps = k"
        using assms(1) by simp
      ultimately show ?thesis
        using assms exe_cmd_cmp3 by blast
    qed
    also have "... = (0, tps[j1 := tps ! j1 |+| Suc t, j2 := tps ! j2 |+| Suc t])"
      using assms
      by (smt (z3) Suc_eq_plus1 add.commute fst_conv list_update_overwrite list_update_swap
        nth_list_update_eq nth_list_update_neq snd_conv)
    finally show ?case
      by simp
  qed
  then have "execute (tm_cmp j1 j2 j3) (0, tps) (m - 1) =
      (0, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1)])"
    using `m > 0` by simp
  then have "execute (tm_cmp j1 j2 j3) (0, tps) m =
      exe (tm_cmp j1 j2 j3) (0, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1)])"
    using `m > 0` by (metis contents_at_0 diff_Suc_1 execute.elims neq)
  then show "execute (tm_cmp j1 j2 j3) (0, tps) m =
      (1, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1), j3 := tps ! j3 |:=| \<box>])"
    using exe_cmd_cmp1 assms \<open>0 < m\<close>
    by (smt (z3) One_nat_def Suc_diff_Suc diff_zero fst_conv length_list_update neq nth_list_update_eq
      nth_list_update_neq plus_1_eq_Suc snd_conv)
qed

lemma transforms_tm_cmpI [transforms_intros]:
  fixes tps :: "tape list"
  assumes "length tps = k"
    and "j1 \<noteq> j2" and "j2 \<noteq> j3" and "j1 \<noteq> j3" and "j1 < k" and "j2 < k" and "j3 < k"
    and "proper_symbols xs"
    and "proper_symbols ys"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "t = Suc (min (length xs) (length ys))"
    and "b = (if xs = ys then \<one> else \<box>)"
    and "m =
     (if xs = ys
      then Suc (length xs)
      else (LEAST m. m \<le> Suc (min (length xs) (length ys)) \<and> \<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m))"
    and "tps' = tps[j1 := (\<lfloor>xs\<rfloor>, m), j2 := (\<lfloor>ys\<rfloor>, m), j3 := tps ! j3 |:=| b]"
  shows "transforms (tm_cmp j1 j2 j3) tps t tps'"
proof (cases "xs = ys")
  case True
  then have m: "m = Suc (length xs)"
    using assms(14) by simp
  have "execute (tm_cmp j1 j2 j3) (0, tps) (Suc (length xs)) =
      (1, tps[j1 := tps ! j1 |+| length xs, j2 := tps ! j2 |+| length xs, j3 := tps ! j3 |:=| \<one>])"
    using execute_tm_cmp_eq assms True by blast
  then have "execute (tm_cmp j1 j2 j3) (0, tps) m =
      (1, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1), j3 := tps ! j3 |:=| b])"
    using m assms(13) True diff_Suc_1 by simp
  moreover have "m \<le> t"
    using True assms(12) m by simp
  ultimately show ?thesis
    using transitsI tm_cmp_def transforms_def assms True
    by (metis (no_types, lifting) One_nat_def add.commute diff_Suc_1 fst_conv list.size(3) list.size(4) plus_1_eq_Suc snd_conv)
next
  case False
  then have m: "m = (LEAST m. m \<le> Suc (min (length xs) (length ys)) \<and> \<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m)"
    using assms(14) by simp
  then have "execute (tm_cmp j1 j2 j3) (0, tps) m =
      (1, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1), j3 := tps ! j3 |:=| \<box>])"
    using False assms execute_tm_cmp_neq by blast
  then have "execute (tm_cmp j1 j2 j3) (0, tps) m =
      (1, tps[j1 := tps ! j1 |+| (m - 1), j2 := tps ! j2 |+| (m - 1), j3 := tps ! j3 |:=| b])"
    using False by (simp add: assms(13))
  moreover have "m \<le> t"
    using ex_contents_neq[OF assms(8,9)] False assms(12) m by (metis (mono_tags, lifting) LeastI)
  ultimately show ?thesis
    using transitsI tm_cmp_def transforms_def assms False
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_pred add.commute execute.simps(1)
      fst_eqD list.size(3) list.size(4) not_gr0 numeral_One snd_conv zero_neq_numeral)
qed

text \<open>
The next Turing machine extends @{const tm_cmp} by a carriage return on tapes
$j_1$ and $j_2$, ensuring that the next command finds the tape heads in a
well-specified position. This makes the TM easier to reuse.
\<close>

definition tm_equals :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_equals j1 j2 j3 \<equiv> tm_cmp j1 j2 j3 ;; tm_cr j1 ;; tm_cr j2"

lemma tm_equals_tm:
  assumes "k \<ge> 2" and "j3 > 0" and "G \<ge> 4"
  shows "turing_machine k G (tm_equals j1 j2 j3)"
  unfolding tm_equals_def using tm_cmp_tm tm_cr_tm assms by simp

text \<open>
We analyze the behavior of @{const tm_equals} inside a locale. This is how we
will typically proceed for Turing machines that are composed of more than two
TMs. The locale is parameterized by the TM's parameters, which in the present
case means the three tape indices $j_1$, $j_2$, and $j_3$.  Inside the locale
the TM is decomposed such that proofs of @{const transforms} only involve two
TMs combined by one of the three control structures (sequence, branch, loop).
In the current example we have three TMs named @{term tm1}, @{term tm2}, @{term
tm3}, where @{term tm3} is just @{const tm_equals}. Furthermore there will be
lemmas \emph{tm1}, \emph{tm2}, \emph{tm3} describing, in terms of @{const
transforms}, the behavior of the respective TMs. For this we define three tape
lists @{term tps1}, @{term tps2}, @{term tps3}.

This naming scheme creates many name clashes for things that only have a single
use. That is the reason for the encapsulation in a locale.

Afterwards this locale is interpreted, just once in lemma~@{text
transforms_tm_equalsI}, to prove the semantics and running time of @{const
tm_equals}.

\null
\<close>

locale turing_machine_equals =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_cmp j1 j2 j3"
definition "tm2 \<equiv> tm1 ;; tm_cr j1"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"

lemma tm3_eq_tm_equals: "tm3 = tm_equals j1 j2 j3"
  unfolding tm3_def tm2_def tm1_def tm_equals_def by simp

context
  fixes tps0 :: "tape list" and k t b :: nat and xs ys :: "symbol list"
  assumes jk [simp]: "length tps0 = k" "j1 \<noteq> j2" "j2 \<noteq> j3" "j1 \<noteq> j3" "j1 < k" "j2 < k" "j3 < k"
    and proper: "proper_symbols xs" "proper_symbols ys"
    and t: "t = Suc (min (length xs) (length ys))"
    and b: "b = (if xs = ys then 3 else 0)"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>ys\<rfloor>, 1)"
begin

definition "m \<equiv>
  (if xs = ys
   then Suc (length xs)
   else (LEAST m. m \<le> Suc (min (length xs) (length ys)) \<and> \<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m))"

lemma m_gr_0: "m > 0"
proof -
  have "\<lfloor>xs\<rfloor> m \<noteq> \<lfloor>ys\<rfloor> m" if "xs \<noteq> ys"
    using ex_contents_neq LeastI_ex m_def proper that by (metis (mono_tags, lifting))
  then show "m > 0"
    using m_def by (metis contents_at_0 gr0I less_Suc_eq_0_disj)
qed

lemma m_le_t: "m \<le> t"
proof (cases "xs = ys")
  case True
  then show ?thesis
    using t m_def by simp
next
  case False
  then have "m \<le> Suc (min (length xs) (length ys))"
    using ex_contents_neq False proper m_def by (metis (mono_tags, lifting) LeastI_ex)
  then show ?thesis
    using t by simp
qed

definition "tps1 \<equiv> tps0[j1 := (\<lfloor>xs\<rfloor>, m), j2 := (\<lfloor>ys\<rfloor>, m), j3 := tps0 ! j3 |:=| b]"

lemma tm1 [transforms_intros]: "transforms tm1 tps0 t tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def m_def b time: t)
  show "proper_symbols xs" "proper_symbols ys"
    using proper by simp_all
qed

definition "tps2 \<equiv> tps0[j1 := (\<lfloor>xs\<rfloor>, 1), j2 := (\<lfloor>ys\<rfloor>, m), j3 := tps0 ! j3 |:=| b]"

lemma tm2:
  assumes "ttt = t + m + 2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps1_def)
  show "clean_tape (tps1 ! j1)"
    using tps1_def clean_contents_proper jk proper(1)
    by (metis nth_list_update_eq nth_list_update_neq)
  show "ttt = t + (tps1 :#: j1 + 2)"
    using tps1_def tps0 jk assms
    by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) nth_list_update_eq nth_list_update_neq snd_conv)
  show "tps2 = tps1[j1 := tps1 ! j1 |#=| 1]"
    unfolding tps2_def tps1_def by (simp add: list_update_swap[of j1])
qed

lemma tm2' [transforms_intros]: "transforms tm2 tps0 (2 * t + 2) tps2"
  using m_le_t tm2 transforms_monotone by simp

definition "tps3 \<equiv> tps0[j1 := (\<lfloor>xs\<rfloor>, 1), j2 := (\<lfloor>ys\<rfloor>, 1), j3 := tps0 ! j3 |:=| b]"

lemma tm3:
  assumes "ttt = 2 * t + m + 4"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def tps3_def)
  have *: "tps2 ! j2 = (\<lfloor>ys\<rfloor>, m)"
    using tps2_def by (simp add: nth_list_update_neq')
  then show "clean_tape (tps2 ! j2)"
    using clean_contents_proper proper(2) by simp
  show "ttt = 2 * t + 2 + (tps2 :#: j2 + 2)"
    using assms * by simp
  show "tps3 = tps2[j2 := tps2 ! j2 |#=| 1]"
    unfolding tps3_def tps2_def by (simp add: list_update_swap[of j2])
qed

definition "tps3' \<equiv> tps0[j3 := tps0 ! j3 |:=| b]"

lemma tm3': "transforms tm3 tps0 (3 * min (length xs) (length ys) + 7) tps3'"
proof -
  have "tps3' = tps3"
    using tps3'_def tps3_def tps0 jk by (metis list_update_id)
  then show ?thesis
    using m_le_t tm3 transforms_monotone t by simp
qed

end  (* context tps0 k xs ys *)

end  (* locale turing_machine_equals *)

lemma transforms_tm_equalsI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and xs ys :: "symbol list" and b :: symbol
  assumes "length tps = k" "j1 \<noteq> j2" "j2 \<noteq> j3" "j1 \<noteq> j3" "j1 < k" "j2 < k" "j3 < k"
    and "proper_symbols xs" "proper_symbols ys"
    and "b = (if xs = ys then \<one> else \<box>)"
  assumes
    "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
  assumes "ttt = 3 * min (length xs) (length ys) + 7"
  assumes "tps' = tps
    [j3 := tps ! j3 |:=| b]"
  shows "transforms (tm_equals j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_equals j1 j2 j3 .
  show ?thesis
    using assms loc.tm3' loc.tm3_eq_tm_equals loc.tps3'_def by simp
qed


subsection \<open>Computing the identity function\<close>

text \<open>
In order to compute the identity function, a Turing machine can just copy the
input tape to the output tape:
\<close>

definition tm_id :: machine where
  "tm_id \<equiv> tm_cp_until 0 1 {\<box>}"

lemma tm_id_tm:
  assumes "1 < k" and "G \<ge> 4"
  shows "turing_machine k G tm_id"
  unfolding tm_id_def using assms tm_cp_until_tm by simp

lemma transforms_tm_idI:
  fixes zs :: "symbol list" and k :: nat and tps :: "tape list"
  assumes "1 < k"
    and "proper_symbols zs"
    and "tps = snd (start_config k zs)"
    and "tps' = tps[0 := (\<lfloor>zs\<rfloor>, (Suc (length zs))), 1 := (\<lfloor>zs\<rfloor>, (Suc (length zs)))]"
  shows "transforms tm_id tps (Suc (Suc (length zs))) tps'"
proof -
  let ?n = "Suc (length zs)"
  define tps2 where
    "tps2 = tps[0 := tps ! 0 |+| (Suc (length zs)), 1 := implant (tps ! 0) (tps ! 1) (Suc (length zs))]"
  have 1: "rneigh (tps ! 0) {\<box>} ?n"
  proof (rule rneighI)
    show "(tps ::: 0) (tps :#: 0 + Suc (length zs)) \<in> {\<box>}"
      using start_config2 start_config3 assms by (simp add: start_config_def)
    show "\<And>n'. n' < Suc (length zs) \<Longrightarrow> (tps ::: 0) (tps :#: 0 + n') \<notin> {\<box>}"
      using start_config2 start_config3 start_config_pos assms
      by (metis One_nat_def Suc_lessD add_cancel_right_left diff_Suc_1 less_Suc_eq_0_disj less_Suc_eq_le not_one_less_zero singletonD)
  qed
  have 2: "length tps = k"
    using assms(1,3) by (simp add: start_config_length)
  have **: "transforms tm_id tps (Suc ?n) tps2"
    unfolding tm_id_def using transforms_tm_cp_untilI[OF _ assms(1) 2 1 _ tps2_def] assms(1) by simp

  have 0: "tps ! 0 = (\<lfloor>zs\<rfloor>, 0)"
    using assms start_config_def contents_def by auto
  moreover have "tps ! 1 = (\<lfloor>[]\<rfloor>, 0)"
    using assms start_config_def contents_def by auto
  moreover have "implant (\<lfloor>zs\<rfloor>, 0) (\<lfloor>[]\<rfloor>, 0) ?n = (\<lfloor>zs\<rfloor>, ?n)"
    by (rule implantI''') simp_all
  ultimately have "implant (tps ! 0) (tps ! 1) ?n = (\<lfloor>zs\<rfloor>, ?n)"
    by simp
  then have "tps2 = tps[0 := tps ! 0 |+| ?n, 1 := (\<lfloor>zs\<rfloor>, ?n)]"
    using tps2_def by simp
  then have "tps2 = tps[0 := (\<lfloor>zs\<rfloor>, ?n), 1 := (\<lfloor>zs\<rfloor>, ?n)]"
    using 0 by simp
  then have "tps2 = tps'"
    using assms(4) by simp
  then show ?thesis
    using ** by simp
qed

text \<open>
The identity function is computable with a time bound of $n + 2$.
\<close>

lemma computes_id: "computes_in_time 2 tm_id id (\<lambda>n. Suc (Suc n))"
proof
  fix x :: string
  let ?zs = "string_to_symbols x"
  let ?start = "snd (start_config 2 ?zs)"
  let ?T = "\<lambda>n. Suc (Suc n)"
  let ?tps = "?start[0 := (\<lfloor>?zs\<rfloor>, (Suc (length ?zs))), 1 := (\<lfloor>?zs\<rfloor>, (Suc (length ?zs)))]"
  have "proper_symbols ?zs"
    by simp
  then have "transforms tm_id ?start (Suc (Suc (length ?zs))) ?tps"
    using transforms_tm_idI One_nat_def less_2_cases_iff by blast
  then have "transforms tm_id ?start (?T (length x)) ?tps"
    by simp
  moreover have "?tps ::: 1 = string_to_contents (id x)"
    by (auto simp add: start_config_length)
  ultimately show "\<exists>tps. tps ::: 1 = string_to_contents (id x) \<and> transforms tm_id ?start (?T (length x)) tps"
    by auto
qed

end
