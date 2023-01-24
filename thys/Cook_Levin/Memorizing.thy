section \<open>Memorizing in states\label{s:tm-memorizing}\<close>

theory Memorizing
  imports Elementary
begin

text \<open>
Some Turing machines are best described by allowing them to memorize values in
their states.  For example, a TM that adds two binary numbers could memorize the
carry bit in states. In the textbook definition of TMs, with arbitrary state
space, this can be represented by a state space of the form $Q \times \{0, 1\}$,
where 0 and 1 represent the memorized values. In our simplified definition of
TMs, where the state space is an interval of natural numbers, this does not
work. However, there is a workaround. Since we can have arbitrarily many
tapes, we can make the TM store this value on an additional tape. Such a
memorization tape could be used to write/read a symbol representing the
memorized value. The tape head would never move on such a tape. The behavior of
the TM can then depend on the memorized value.

By adding several such tapes we can even have more than one value stored
simultaneously as well. However, this method increases the number of tapes, and
one part of the proof of the Cook-Levin theorem is showing that every TM can be
simulated on a two-tape TM (see Chapter~\ref{s:oblivious-two-tape}).  How to
remove such memorization tapes again without changing the behavior of the TM is
the subject of this section.

The straightforward idea is to multiply the states by the number of possible
values. So if the original TM has $Q$ non-halting states and memorizes $G$
different values, the new TM has $Q\cdot G$ non-halting states. It would be
natural to map a pair $(q, g)$ of state and memorized value to $q \cdot G + g$
or to $g \cdot Q + q$. However, there is a small technical problem.

The memorization tape is initialized, like all tapes in a start configuration,
with the head on the leftmost cell, which contains the start symbol. Thus the
initially memorized value is the number~1 representing~$\triangleright$. The new
TM must start in the start state, which we have fixed at~0. Thus the state-value
pair $(0, 1)$ must be mapped to~0, which neither of the two natural mappings
does.  Our workaround is to use the mapping $(q, g) \mapsto ((g - 1) \bmod G)
\cdot Q + q$.

The following function maps a Turing machine $M$ that memorizes one value from
$\{0,\dots,G-1\}$ on its last tape to a TM that has one tape less, has $G$ times
the number of non-halting states, and behaves just like $M$. The name
``cartesian'' for this function is just a funny term I made up.
\<close>

definition cartesian :: "machine \<Rightarrow> nat \<Rightarrow> machine" where
  "cartesian M G \<equiv>
   concat
    (map (\<lambda>h. map (\<lambda>q rs.
                      let (q', as) = (M ! q) (rs @ [(h + 1) mod G])
                      in (if q' = length M then G * length M else (fst (last as) + G - 1) mod G * length M + q',
                          butlast as))
              [0..<length M])
     [0..<G])"

lemma length_concat_const:
  assumes "\<And>h. length (f h) = c"
  shows "length (concat (map f [0..<G])) = G * c"
  using assms by (induction G; simp)

lemma length_cartesian: "length (cartesian M G) = G * length M"
  using cartesian_def by (simp add: length_concat_const)

lemma concat_nth:
  assumes "\<And>h. length (f h) = c"
    and "xs = concat (map f [0..<G])"
    and "h < G"
    and "q < c"
  shows "xs ! (h * c + q) = f h ! q"
  using assms(2,3)
proof (induction G arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc G)
  then have 1: "xs = concat (map f [0..<G]) @ f G" (is "xs = ?ys @ f G")
    by simp
  show ?case
  proof (cases "h < G")
    case True
    then have "h * c \<le> (G - 1) * c"
      by auto
    then have "h * c \<le> G * c - c"
      using True by (simp add: diff_mult_distrib)
    then have "h * c + q \<le> G * c - c + q"
      using assms(4) by simp
    then have "h * c + q < G * c"
      using assms(4) True \<open>h * c \<le> (G - 1) * c\<close> mult_eq_if by force
    then have "h * c + q < length ?ys"
      using length_concat_const assms by metis
    then have "xs ! (h * c + q) = ?ys ! (h * c + q)"
      using 1 by (simp add: nth_append)
    then show ?thesis
      using Suc True by simp
  next
    case False
    then show ?thesis
      using "1" Suc.prems(2) assms(1)
      by (metis add_diff_cancel_left' length_concat_const less_SucE not_add_less1 nth_append)
  qed
qed

lemma cartesian_at:
  assumes "M' = cartesian M b" and "h < b" and "q < length M"
  shows "(M' ! (h * length M + q)) rs =
    (let (q', as) = (M ! q) (rs @ [(h + 1) mod b])
     in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
         butlast as))"
proof -
  define f where "f =
   (\<lambda>h. map (\<lambda>q. \<lambda>rs.
      let (q', as) = (M ! q) (rs @ [(h + 1) mod b])
      in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
          butlast as))
    [0..<length M])"
  then have "length (f h) = length M" for h
    by simp
  moreover have "M' = concat (map f [0..<b])"
    using assms(1) cartesian_def f_def by simp
  ultimately have "M' ! (h * length M + q) = f h ! q"
    using concat_nth assms(2,3) by blast
  then show ?thesis
    using f_def by (simp add: assms(3))
qed

lemma concat_nth_ex:
  assumes "\<And>h. length (f h) = c"
    and "xs = concat (map f [0..<G])"
    and "j < G * c"
  shows "\<exists>i h. i < c \<and> h < G \<and> xs ! j = f h ! i"
  using assms(2,3)
proof (induction G arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc G)
  then have *: "xs = concat (map f [0..<G]) @ f G" (is "xs = ?ys @ f G")
    by simp
  show ?case
  proof (cases "j < G * c")
  case True
    then have "\<exists>i h. i < c \<and> h < G \<and> ?ys ! j = f h ! i"
      using Suc by simp
    then have "\<exists>i h. i < c \<and> h < Suc G \<and> ?ys ! j = f h ! i"
      using less_SucI by blast
    then have "\<exists>i h. i < c \<and> h < Suc G \<and> xs ! j = f h ! i"
      using True * by (simp add: assms(1) length_concat_const nth_append)
    then show ?thesis .
  next
    case False
    then have "j \<ge> G * c"
      by simp
    define h where "h = G"
    then have h: "h < Suc G"
      by simp
    define i where "i = j - G * c"
    then have i: "i < c"
      using False Suc.prems(2) by auto
    have "xs ! j = f h ! i"
      using assms by (simp add: "*" False h_def i_def length_concat_const nth_append)
    then show ?thesis
      using h i by auto
  qed
qed

text \<open>
The cartesian TM has one tape less than the original TM.
\<close>

lemma cartesian_num_tapes:
  assumes "turing_machine (Suc k) G M"
    and "M' = cartesian M b"
    and "length rs = k"
    and "q' < length M'"
  shows "length (snd ((M' ! q') rs)) = k"
proof -
  define q where "q = q' mod length M"
  define h where "h = q' div length M"
  then have "h < b" "q' = h * length M + q"
    using q_def assms(2) assms(4) length_cartesian less_mult_imp_div_less by auto
  then have "q < length M"
    using q_def assms(2,4) length_cartesian
    by (metis add_lessD1 length_0_conv length_greater_0_conv mod_less_divisor mult_0_right)

  have "(M' ! q') rs =
    (let (q', as) = (M ! q) (rs @ [(h + 1) mod b])
     in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
         butlast as))"
    using cartesian_at[OF assms(2) `h < b` `q < length M`] `q' = h * length M + q` by simp
  then have "snd ((M' ! q') rs) = (let (q', as) = (M ! q) (rs @ [(h + 1) mod b]) in butlast as)"
    by (metis (no_types, lifting) case_prod_unfold snd_conv)
  then have *: "snd ((M' ! q') rs) = butlast (snd ((M ! q) (rs @ [(h + 1) mod b])))"
    by (simp add: case_prod_unfold)

  have "length (rs @ [(h + 1) mod b]) = Suc k"
    using assms(3) by simp
  then have "length (snd ((M ! q) (rs @ [(h + 1) mod b]))) = Suc k"
    using assms(1) \<open>q < length M\<close> turing_commandD(1) turing_machine_def nth_mem by metis
  then show ?thesis
    using * by simp
qed

text \<open>
The cartesian TM of a TM with alphabet $G$ also has the alphabet $G$ provided it
memorizes at most $G$ values.
\<close>

lemma cartesian_tm:
  assumes "turing_machine (Suc k) G M"
    and "M' = cartesian M b"
    and "k \<ge> 2"
    and "b \<le> G"
    and "b > 0"
  shows "turing_machine k G M'"
proof
  show "G \<ge> 4"
    using assms(1) turing_machine_def by simp
  show "2 \<le> k"
    using assms(3) .

  define f where "f =
   (\<lambda>h. map (\<lambda>i rs.
              let (q, as) = (M ! i) (rs @ [(h + 1) mod b])
              in (if q = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q,
                  butlast as))
      [0..<length M])"
  then have 1: "\<And>h. length (f h) = length M"
    by simp
  have 2: "M' = concat (map f [0..<b])"
    using f_def assms(2) cartesian_def by simp

  show "turing_command k (length M') G (M' ! j)" if "j < length M'" for j
  proof
    have 3: "j < b * length M"
      using that by (simp add: assms(2) length_cartesian)
    with 1 2 concat_nth_ex have "\<exists>i h. i < length M \<and> h < b \<and> M' ! j = f h ! i"
      by blast
    then obtain i h where
      i: "i < length M" and
      h: "h < b" and
      cmd: "M' ! j = (\<lambda>rs.
          let (q, as) = (M ! i) (rs @ [(h + 1) mod b])
          in (if q = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q,
              butlast as))"
      using f_def by auto
    have "(h + 1) mod b < b"
      using h by auto
    then have modb: "(h + 1) mod b < G"
      using assms(4) by linarith

    have tc: "turing_command (Suc k) (length M) G (M ! i)"
      using i assms(1) turing_machine_def by simp

    show goal1: "\<And>gs. length gs = k \<Longrightarrow> length ([!!] (M' ! j) gs) = length gs"
    proof -
      fix gs :: "symbol list"
      assume a: "length gs = k"
      let ?q = "fst ((M ! i) (gs @ [(h + 1) mod b]))"
      let ?as = "snd ((M ! i) (gs @ [(h + 1) mod b]))"
      have "(M' ! j) gs =
          (if ?q = length M then b * length M else (fst (last ?as) + b - 1) mod b * length M + ?q,
          butlast ?as)"
        using cmd by (metis (no_types, lifting) case_prod_unfold)
      then have "[!!] (M' ! j) gs = butlast ?as"
        by simp
      moreover have "length ?as = Suc k"
        using a turing_commandD(1)[OF tc] by simp
      ultimately show "length ([!!] (M' ! j) gs) = length gs"
        by (simp add: a)
    qed
    show "(M' ! j) gs [.] ja < G"
      if "length gs = k" and
        "(\<And>i. i < length gs \<Longrightarrow> gs ! i < G)" and
        "ja < length gs"
      for gs ja
    proof -
      let ?q = "fst ((M ! i) (gs @ [(h + 1) mod b]))"
      let ?as = "snd ((M ! i) (gs @ [(h + 1) mod b]))"
      have *: "(M' ! j) gs =
          (if ?q = length M then b * length M else (fst (last ?as) + b - 1) mod b * length M + ?q,
          butlast ?as)"
        using cmd by (metis (no_types, lifting) case_prod_unfold)
      have "length (gs @ [(h + 1) mod b]) = Suc k"
        using that by simp
      moreover have "(gs @ [(h + 1) mod b]) ! i < G" if "i < length (gs @ [(h + 1) mod b])" for i
        using that by (metis \<open>\<And>i. i < length gs \<Longrightarrow> gs ! i < G\<close> modb
          length_append_singleton less_Suc_eq nth_append nth_append_length)
      ultimately have "(\<forall>j<length (gs @ [(h + 1) mod b]). (M ! i) (gs @ [(h + 1) mod b]) [.] j < G)"
        using that turing_commandD(2)[OF tc] by simp
      moreover have "butlast ?as ! ja = ?as ! ja"
        by (metis * goal1 nth_butlast snd_conv that(1) that(3))
      ultimately show ?thesis
        using "*" that(3) by auto
    qed
    show "(M' ! j) gs [.] 0 = gs ! 0" if "length gs = k" and "0 < k" for gs
    proof -
      let ?q = "fst ((M ! i) (gs @ [(h + 1) mod b]))"
      let ?as = "snd ((M ! i) (gs @ [(h + 1) mod b]))"
      have *: "(M' ! j) gs =
          (if ?q = length M then b * length M else (fst (last ?as) + b - 1) mod b * length M + ?q,
            butlast ?as)"
        using cmd by (metis (no_types, lifting) case_prod_unfold)
      have "length (gs @ [(h + 1) mod b]) = Suc k"
        using that by simp
      then have "(M ! i) (gs @ [(h + 1) mod b]) [.] 0 = gs ! 0"
        using that turing_commandD(3)[OF tc] by (simp add: nth_append)
      then show ?thesis
        using that * by (metis goal1 nth_butlast snd_conv)
    qed
    show "[*] ((M' ! j) gs) \<le> length M'" if "length gs = k" for gs
    proof -
      let ?q = "[*] ((M ! i) (gs @ [(h + 1) mod b]))"
      let ?as = "snd ((M ! i) (gs @ [(h + 1) mod b]))"
      have *: "(M' ! j) gs =
        (if ?q = length M then b * length M else (fst (last ?as) + b - 1) mod b * length M + ?q,
          butlast ?as)"
        using cmd by (metis (no_types, lifting) case_prod_unfold)
      have "length (gs @ [h]) = Suc k"
        using that by simp
      then have "?q \<le> length M"
        using assms(1) i turing_commandD(4)[OF tc] by (metis length_append_singleton)
      show ?thesis
      proof (cases "?q = length M")
        case True
        then show ?thesis
          using * by (simp add: assms(2) length_cartesian)
      next
        case False
        then have "?q < length M"
          using `?q \<le> length M` by simp
        then have **: "[*] ((M' ! j) gs) = (fst (last ?as) + b - 1) mod b * length M + ?q"
          using * by simp
        have "(fst (last ?as) + b - 1) mod b \<le> b - 1"
          using h less_imp_Suc_add by fastforce
        have "(fst (last ?as) + b - 1) mod b * length M \<le> b * length M - length M"
          using h less_imp_Suc_add by fastforce
        then have "(fst (last ?as) + b - 1) mod b * length M + ?q \<le> b * length M - length M + ?q"
          by simp
        then have "(fst (last ?as) + b - 1) mod b * length M + ?q < b * length M"
          using `?q < length M` 3 assms(5) by auto
        then show ?thesis
          using length_cartesian ** assms(2) by simp
      qed
    qed
  qed
qed

text \<open>
A special case of the previous lemma is $b = G$:
\<close>

corollary cartesian_tm':
  assumes "turing_machine (Suc k) G M"
    and "M' = cartesian M G"
    and "k \<ge> 2"
  shows "turing_machine k G M'"
  using assms cartesian_tm by (metis gr0I not_numeral_le_zero order_refl turing_machine_def)

text \<open>
A cartesian TM assumes essentially the same configurations the original machine
does, except that it has one tape less and the states have a greater number. We
call these configurations ``squished'', another fancy made-up term alluding to
the removal of one tape.

\null
\<close>

definition squish :: "nat \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> config" where
  "squish G Q cfg \<equiv>
     let (q, tps) = cfg
     in (if q \<ge> Q then G * Q else ( |.| (last tps) + G - 1) mod G * Q + q, butlast tps)"

lemma squish:
  "squish G Q cfg =
    (if fst cfg \<ge> Q then G * Q else ( |.| (last (snd cfg)) + G - 1) mod G * Q + fst cfg, butlast (snd cfg))"
  using squish_def by (simp add: case_prod_beta)

lemma squish_head_pos:
  assumes "||cfg|| > 2"
  shows "squish G Q cfg <#> 0 = cfg <#> 0"
    and "squish G Q cfg <#> 1 = cfg <#> 1"
  using assms squish
    by (metis One_nat_def Suc_1 Suc_lessD length_butlast less_diff_conv nth_butlast plus_1_eq_Suc snd_conv,
        metis One_nat_def Suc_1 length_butlast less_diff_conv nth_butlast plus_1_eq_Suc snd_conv)

lemma mod_less:
  fixes q Q h G :: nat
  assumes "q < Q" and "0 < G"
  shows "h mod G * Q + q < G * Q"
proof -
  have "h mod G \<le> G - 1"
    using assms(2) less_Suc_eq_le by fastforce
  then have "h mod G * Q \<le> (G - 1) * Q"
    by simp
  then have "h mod G * Q \<le> G * Q - Q"
    by (simp add: left_diff_distrib')
  then have "h mod G * Q + q \<le> G * Q - Q + q"
    by simp
  then have "h mod G * Q + q \<le> G * Q - 1"
    using assms by simp
  then show ?thesis
    by (metis One_nat_def Suc_pred add.left_neutral add.right_neutral add_mono_thms_linordered_semiring(1)
      assms le_simps(2) linorder_not_less mult_pos_pos zero_le)
qed

lemma squish_halt_state:
  assumes "G > 0" and "fst cfg \<le> Q"
  shows "fst (squish G Q cfg) = G * Q \<longleftrightarrow> fst cfg = Q"
proof
  show "fst cfg = Q \<Longrightarrow> fst (squish G Q cfg) = G * Q"
    by (simp add: squish)
  show "fst (squish G Q cfg) = G * Q \<Longrightarrow> fst cfg = Q"
  proof (rule ccontr)
    assume a: "fst (squish G Q cfg) = G * Q"
    assume "fst cfg \<noteq> Q"
    then have "fst cfg < Q"
      using assms(2) by simp
    then have "fst (squish G Q cfg) = ( |.| (last (snd cfg)) + G - 1) mod G * Q + fst cfg"
      using squish by simp
    also have "... < G * Q"
      using mod_less[OF `fst cfg < Q` assms(1)] by simp
    finally have "fst (squish G Q cfg) < G * Q" .
    with a show False
      by simp
  qed
qed

lemma butlast_replicate: "butlast (replicate k x) = replicate (k - Suc 0) x"
  by (intro nth_equalityI) (simp_all add: nth_butlast)

lemma squish_start_config: "G \<ge> 4 \<Longrightarrow> k \<ge> 2 \<Longrightarrow> squish G Q (start_config (Suc k) zs) = start_config k zs"
  using squish_def start_config_def by (simp add: butlast_replicate)

text \<open>
The cartesian Turing machine only works properly if the original TM never moves
its head on the last tape. We call a tape of a TM $M$ \emph{immobile} if $M$
never moves the head on the tape.
\<close>

definition immobile :: "machine \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 "immobile M j k \<equiv> \<forall>q rs. q < length M \<longrightarrow> length rs = k \<longrightarrow> (M ! q) rs [~] j = Stay"

lemma immobileI [intro]:
  assumes "\<And>q rs. q < length M \<Longrightarrow> length rs = k \<Longrightarrow> (M ! q) rs [~] j = Stay"
  shows "immobile M j k"
  using immobile_def assms by simp

text \<open>
If the head never moves on tape $k$, the head will stay in position $0$.
\<close>

lemma immobile_head_pos_proper:
  assumes "proper_machine (Suc k) M"
    and "immobile M k (Suc k)"
    and "||cfg|| = Suc k"
  shows "execute M cfg t <#> k = cfg <#> k"
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  have "execute M cfg (Suc t) = exe M (execute M cfg t)"
    (is "_ = exe M ?cfg")
    by simp
  show ?case
  proof (cases "fst ?cfg \<ge> length M")
    case True
    then have "exe M ?cfg = ?cfg"
      using exe_ge_length by simp
    then show ?thesis
      by (simp add: Suc.IH)
  next
    case False
    let ?cmd = "M ! (fst ?cfg)"
    let ?rs = "config_read ?cfg"
    have "exe M ?cfg = sem ?cmd ?cfg"
      using False exe_def by simp
    moreover have "proper_command (Suc k) (M ! (fst ?cfg))"
      using assms(1) False by simp
    ultimately have "exe M ?cfg <!> k = act (snd (?cmd ?rs) ! k) (?cfg <!> k)"
      using assms execute_num_tapes_proper lessI sem_snd by presburger
    then show ?thesis
      using False Suc act assms execute_num_tapes_proper immobile_def read_length by simp
  qed
qed

lemma immobile_head_pos:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "||cfg|| = Suc k"
  shows "execute M cfg t <#> k = cfg <#> k"
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  have "execute M cfg (Suc t) = exe M (execute M cfg t)"
    (is "_ = exe M ?cfg")
    by simp
  show ?case
  proof (cases "fst ?cfg \<ge> length M")
    case True
    then have "exe M ?cfg = ?cfg"
      using exe_ge_length by simp
    then show ?thesis
      by (simp add: Suc.IH)
  next
    case False
    let ?cmd = "M ! (fst ?cfg)"
    let ?rs = "config_read ?cfg"
    have "exe M ?cfg = sem ?cmd ?cfg"
      using False exe_def by simp
    moreover have "proper_command (Suc k) (M ! (fst ?cfg))"
      using assms(1) False by (metis turing_commandD(1) linorder_not_le turing_machineD(3))
    ultimately have "exe M ?cfg <!> k = act (snd (?cmd ?rs) ! k) (?cfg <!> k)"
      using assms execute_num_tapes lessI sem_snd by presburger
    then show ?thesis
      using False Suc act assms execute_num_tapes immobile_def read_length by simp
  qed
qed

text \<open>
Sequentially combining two Turing machines with an immobile tape yields a Turing
machine with the same immobile tape.
\<close>

lemma immobile_sequential:
  assumes "turing_machine k G M1"
    and "turing_machine k G M2"
    and "immobile M1 j k"
    and "immobile M2 j k"
  shows "immobile (M1 ;; M2) j k"
proof
  let ?M = "M1 ;; M2"
  fix q :: nat and rs :: "symbol list"
  assume q: "q < length ?M" and rs: "length rs = k"
  show "(?M ! q) rs [~] j = Stay"
  proof (cases "q < length M1")
    case True
    then have "?M ! q = M1 ! q"
      by (simp add: nth_append turing_machine_sequential_def)
    then show ?thesis
      using assms(3) immobile_def by (simp add: True rs)
  next
    case False
    then have "?M ! q = relocate_cmd (length M1) (M2 ! (q - length M1))"
      using q turing_machine_sequential_nth' by simp
    then show ?thesis
      using relocate_cmd_head False assms(4) q rs length_turing_machine_sequential immobile_def
      by simp
  qed
qed

text \<open>
A loop also keeps a tape immobile.
\<close>

lemma immobile_loop:
  assumes "turing_machine k G M1"
    and "turing_machine k G M2"
    and "immobile M1 j k"
    and "immobile M2 j k"
    and "j < k"
  shows "immobile (WHILE M1 ; cond DO M2 DONE) j k"
proof
  let ?loop = "WHILE M1 ; cond DO M2 DONE"
  have "?loop =
      M1 @
      [cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)] @
      (relocate (length M1 + 1) M2) @
      [cmd_jump (\<lambda>_. True) 0 0]"
      (is "_ = M1 @ [?a] @ ?bs @ [?c]")
    using turing_machine_loop_def by simp
  then have loop: "?loop = (M1 @ [?a]) @ (?bs @ [?c])"
    by simp
  fix q :: nat
  assume q: "q < length ?loop"
  fix rs :: "symbol list"
  assume rs: "length rs = k"
  consider
      "q < length M1"
    | "q = length M1"
    | "length M1 < q \<and> q \<le> length M1 + length M2"
    | "length M1 + length M2 < q"
    by linarith
  then show "(?loop ! q) rs [~] j = Stay"
  proof (cases)
    case 1
    then have "?loop ! q = M1 ! q"
      by (simp add: nth_append turing_machine_loop_def)
    then show ?thesis
      using assms(3) 1 rs immobile_def by simp
  next
    case 2
    then have "?loop ! q = cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)"
      by (simp add: nth_append turing_machine_loop_def)
    then show ?thesis
      using rs cmd_jump_def assms(5) by simp
  next
    case 3
    then have "?loop ! q = (?bs @ [?c]) ! (q - (length M1 + 1))"
      using nth_append[of "M1 @ [?a]" "?bs @ [?c]"] loop by simp
    moreover have "q - (length M1 + 1) < length ?bs"
      using 3 length_relocate by auto
    ultimately have "?loop ! q = ?bs ! (q - (length M1 + 1))"
      by (simp add: nth_append)
    then show ?thesis
      using assms(4,5) relocate_cmd_head 3 relocate rs immobile_def by auto
  next
    case 4
    then have "q = length M1 + length M2 + 1"
      using q turing_machine_loop_len by simp
    then have "?loop ! q = ?c"
      using turing_machine_loop_def
      by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 append_assoc length_append list.size(3)
        list.size(4) nth_append_length plus_nat.simps(2) length_relocate)
    then show ?thesis
      using rs cmd_jump_def assms(5) by simp
  qed
qed

text \<open>
An immobile tape stays immobile when further tapes are appended. We only need
this for the special case of two-tape Turing machines.
\<close>

lemma immobile_append_tapes:
  assumes "j < k" and "j > 1" and "k \<ge> 2" and "turing_machine 2 G M"
  shows "immobile (append_tapes 2 k M) j k"
proof
  let ?M = "append_tapes 2 k M"
  fix q :: nat
  assume q: "q < length ?M"
  fix rs :: "symbol list"
  assume rs: "length rs = k"
  have "q < length M"
    using assms q by (metis length_append_tapes)
  show "(?M ! q) rs [~] j = Stay"
  proof -
    have "(?M ! q) rs =
         (fst ((M ! q) (take 2 rs)), snd ((M ! q) (take 2 rs)) @ (map (\<lambda>j. (rs ! j, Stay)) [2..<k]))"
      using append_tapes_nth by (simp add: append_tapes_nth \<open>q < length M\<close> rs)
    then have "(?M ! q) rs [~] j =
         snd ((snd ((M ! q) (take 2 rs)) @ (map (\<lambda>j. (rs ! j, Stay)) [2..<k])) ! j)"
      using assms by simp
    also have "... = snd ((map (\<lambda>j. (rs ! j, Stay)) [2..<k]) ! (j - 2))"
    proof -
      have "length (take 2 rs) = 2"
        using rs assms(3) by simp
      then have "length ([!!] (M ! q) (take 2 rs)) = 2"
        using assms rs by (metis turing_commandD(1) \<open>q < length M\<close> nth_mem turing_machine_def)
      then show ?thesis
        using nth_append[of "snd ((M ! q) (take 2 rs))" "map (\<lambda>j. (rs ! j, Stay)) [2..<k]" j] assms by simp
    qed
    finally show ?thesis
      using assms(1,2) by simp
  qed
qed

text \<open>
For the elementary Turing machines we introduced in
Section~\ref{s:tm-elementary} all tapes are immobile but the ones given as
parameters.
\<close>

lemma immobile_tm_trans_until:
  assumes "j \<noteq> j1" and "j \<noteq> j2" and "j < k"
  shows "immobile (tm_trans_until j1 j2 H f) j k"
  using assms tm_trans_until_def cmd_trans_until_def by auto

lemma immobile_tm_ltrans_until:
  assumes "j \<noteq> j1" and "j \<noteq> j2" and "j < k"
  shows "immobile (tm_ltrans_until j1 j2 H f) j k"
  using assms tm_ltrans_until_def cmd_ltrans_until_def by auto

lemma immobile_tm_left_until:
  assumes "j \<noteq> j'" and "j < k"
  shows "immobile (tm_left_until H j') j k"
  using assms tm_left_until_def cmd_left_until_def by auto

lemma immobile_tm_start:
  assumes "j \<noteq> j'" and "j < k"
  shows "immobile (tm_start j') j k"
  using tm_start_def immobile_tm_left_until[OF assms] by metis

lemma immobile_tm_write:
  assumes "j < k"
  shows "immobile (tm_write j' h) j k"
  using assms tm_write_def cmd_write_def by auto

lemma immobile_tm_write_many:
  assumes "j < k"
  shows "immobile (tm_write_many J h) j k"
  using assms tm_write_many_def cmd_write_many_def by auto

lemma immobile_tm_right:
  assumes "j \<noteq> j'" and "j < k"
  shows "immobile (tm_right j') j k"
  using assms tm_right_def cmd_right_def by auto

lemma immobile_tm_rtrans:
  assumes "j \<noteq> j'" and "j < k"
  shows "immobile (tm_rtrans j' f) j k"
  using assms tm_rtrans_def cmd_rtrans_def by auto

lemma immobile_tm_left:
  assumes "j \<noteq> j'" and "j < k"
  shows "immobile (tm_left j') j k"
  using assms tm_left_def cmd_left_def by auto

lemma mod_inc_dec: "(h::nat) < G \<Longrightarrow> ((h + G - 1) mod G + 1) mod G = h"
  using mod_Suc_eq by auto

lemma last_length: "length xs = Suc k \<Longrightarrow> last xs = xs ! k"
  by (metis diff_Suc_1 last_conv_nth length_0_conv nat.simps(3))

text \<open>
The tapes used for memorizing the values have blank symbols in every cell but
possibly for the leftmost cell. In keeping with funny names, we call such tapes
@{term onesie} tapes.
\<close>

definition onesie :: "symbol \<Rightarrow> tape" ("\<lceil>_\<rceil>") where
  "\<lceil>h\<rceil> \<equiv> (\<lambda>x. if x = 0 then h else \<box>, 0)"

lemma onesie_1: "\<lceil>\<triangleright>\<rceil> = (\<lfloor>[]\<rfloor>, 0)"
  unfolding onesie_def contents_def by auto

lemma onesie_read [simp]: "|.| \<lceil>h\<rceil> = h"
  using onesie_def by simp

lemma onesie_write: "\<lceil>x\<rceil> |:=| y = \<lceil>y\<rceil>"
  using onesie_def by auto

lemma act_onesie: "act (h, Stay) \<lceil>x\<rceil> = \<lceil>h\<rceil>"
  using onesie_def by auto

text \<open>
We now consider the semantics of cartesian Turing machines. Roughly speaking, a
cartesian TM assumes the squished configurations of the original TM.  A crucial
assumption here is that the original TM only ever memorizes a symbol from a
certain range of symbols, with one relaxation: when switching to the halting
state, any symbol may be written to the memorization tape. The reason is that
there is only one halting state even for the cartesian TM, and thus the halting
state is not subject to the mapping of states implemented by the @{const
cartesian} operation.

In the following lemma, @{text "\<lceil>\<triangleright>\<rceil>"} is the memorization tape. It has the
start symbol because in the start configuration all tapes have the start symbol
in the leftmost cell.
\<close>

lemma cartesian_execute:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "k \<ge> 2"
    and "b > 0"
    and "length tps = k"
    and "\<And>t. execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t <.> k < b \<or> fst (execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t) = length M"
  shows "execute (cartesian M b) (0, tps) t =
    squish b (length M) (execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t)"
proof (induction t)
  case 0
  then show ?case
    using squish by simp
next
  case (Suc t)
  let ?M' = "cartesian M b"
  have len: "length ?M' = b * length M"
    using length_cartesian by simp
  let ?cfg = "execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t"
  have 1: "?cfg <#> k = 0"
    using assms(1,2,5) immobile_head_pos onesie_def by auto
  have 3: "||?cfg|| = Suc k"
    using assms(1,5) execute_num_tapes by auto
  let ?Q = "length M"
  let ?squish = "squish b ?Q"
  let ?scfg = "?squish ?cfg"
  obtain q tps where qtps: "?cfg = (q, tps)"
    by fastforce
  have "length tps = Suc k"
    using 3 qtps by simp
  then have last: "last tps = tps ! k"
    using assms(4) by (metis diff_Suc_1 last_conv_nth length_greater_0_conv zero_less_Suc)

  have "exe ?M' ?scfg = ?squish (exe M ?cfg)"
  proof (cases "q \<ge> length M")
    case True
    then have t1: "exe M ?cfg = ?cfg"
      using exe_def qtps by auto
    have "?scfg = (b * length M, butlast tps)"
      using True squish qtps by simp
    then have "exe ?M' ?scfg = ?scfg"
      using exe_def len by simp
    with t1 show ?thesis
      by simp
  next
    case False
    then have scfg: "?scfg = (( |.| (last tps) + b - 1) mod b * length M + q, butlast tps)"
        (is "_ = (?q, _)")
      using squish qtps by simp
    moreover have q_less: "?q < length ?M'"
      using mod_less False length_cartesian assms(4) by simp
    ultimately have 9: "exe ?M' ?scfg = sem (?M' ! ?q) ?scfg"
      using exe_def by simp
    let ?cmd' = "?M' ! ?q"
    let ?h = "( |.| (last tps) + b - 1) mod b"
    have "q < length M"
      using False by simp
    then have 4: "|.| (last tps) < b"
      using assms last qtps False by (metis fst_conv less_not_refl3 snd_conv)
    have h_less: "?h < b"
      using 4 by simp
    then have "?cmd' \<equiv> \<lambda>rs.
        (let (q', as) = (M ! q) (rs @ [(?h + 1) mod b])
         in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
             butlast as))"
      using cartesian_at[OF _ h_less `q < length M`] by presburger
    then have cmd': "?cmd' \<equiv> \<lambda>rs.
        (let (q', as) = (M ! q) (rs @ [ |.| (last tps)])
         in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
             butlast as))"
      using mod_inc_dec[OF 4] by simp
    let ?rs' = "config_read ?scfg"
    have 10: "sem ?cmd' ?scfg =
        (let (newstate, as) = ?cmd' ?rs'
         in (newstate, map (\<lambda>(a, tp). act a tp) (zip as (butlast tps))))"
      using scfg by (simp add: sem_def)
    let ?newstate' = "fst (?cmd' ?rs')"
    let ?as' = "snd (?cmd' ?rs')"
    have 11: "sem ?cmd' ?scfg =
         (?newstate', map (\<lambda>(a, tp). act a tp) (zip ?as' (butlast tps)))"
      using 10 by (simp add: case_prod_beta)
    with 9 have lhs: "exe ?M' ?scfg =
         (?newstate', map (\<lambda>(a, tp). act a tp) (zip ?as' (butlast tps)))"
      by simp

    let ?cmd = "M ! q"
    let ?rs = "config_read ?cfg"
    let ?newstate = "fst (?cmd ?rs)"
    let ?as = "snd (?cmd ?rs)"
    have "?squish (exe M ?cfg) = ?squish (sem ?cmd ?cfg)"
      using qtps False exe_def by simp
    also have "... = ?squish (?newstate, map (\<lambda>(a, tp). act a tp) (zip ?as (snd ?cfg)))"
      by (metis sem)
    also have "... = ?squish (?newstate, map (\<lambda>(a, tp). act a tp) (zip ?as tps))"
        (is "_ = ?squish (_, ?tpsSuc)")
      using qtps by simp
    also have "... =
      (if ?newstate \<ge> ?Q then b * ?Q else ( |.| (last ?tpsSuc) + b - 1) mod b * ?Q + ?newstate,
       butlast ?tpsSuc)"
      using squish by simp
    finally have rhs: "?squish (exe M ?cfg) =
      (if ?newstate \<ge> ?Q then b * ?Q else ( |.| (last ?tpsSuc) + b - 1) mod b * ?Q + ?newstate,
       butlast ?tpsSuc)" .

    have "read (butlast tps) @ [ |.| (last tps)] = read tps"
      using `length tps = Suc k` read_def
      by (metis (no_types, lifting) last_map length_0_conv map_butlast map_is_Nil_conv old.nat.distinct(1) snoc_eq_iff_butlast)
    then have rs'_read: "?rs' @ [ |.| (last tps)] = read tps"
      using scfg by simp

    have fst: "fst (?cmd' ?rs') =
      (if ?newstate \<ge> ?Q then b * ?Q else ( |.| (last ?tpsSuc) + b - 1) mod b * ?Q + ?newstate)"
    proof -
      have "fst (?cmd' ?rs') \<equiv> fst (
        (let (q', as) = (M ! q) (?rs' @ [ |.| (last tps)])
         in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
             butlast as)))"
        using cmd' by simp
      then have "fst (?cmd' ?rs') =
         (if fst ((M ! q) (?rs' @ [ |.| (last tps)])) = length M
          then b * length M
          else (fst (last (snd ((M ! q) (?rs' @ [ |.| (last tps)])))) + b - 1) mod b * length M +
            fst ((M ! q) (?rs' @ [ |.| (last tps)])))"
        by (auto simp add: Let_def split_beta)
      then have lhs: "fst (?cmd' ?rs') =
         (if fst ((M ! q) (read tps)) = length M
          then b * ?Q
          else (fst (last (snd ((M ! q) (read tps)))) + b - 1) mod b * ?Q + fst ((M ! q) (read tps)))"
        using rs'_read by simp

      have *: "|.| (last (map (\<lambda>(a, tp). act a tp) (zip ?as tps))) = fst (last (snd ((M ! q) (read tps))))"
      proof -
        have "length ?as = Suc k"
          using "3" \<open>q < length M\<close> assms(1) read_length turing_machine_def
          by (metis turing_commandD(1) nth_mem)
        then have "length (map (\<lambda>(a, tp). act a tp) (zip ?as tps)) = Suc k"
          using `length tps = Suc k` by simp
        then have "last (map (\<lambda>(a, tp). act a tp) (zip ?as tps)) =
            (map (\<lambda>(a, tp). act a tp) (zip ?as tps)) ! k"
          using last_length by blast
        moreover have "proper_command (Suc k) ?cmd"
          using \<open>q < length M\<close> assms(1) turing_machine_def turing_commandD(1) nth_mem by blast
        ultimately have 1: "last (map (\<lambda>(a, tp). act a tp) (zip ?as tps)) = act (?as ! k) (tps ! k)"
          using "3" \<open>q < length M\<close> assms(1) qtps sem' sem_snd_tm by auto

        have "snd (?as ! k) = Stay"
          using assms(2) `length tps = Suc k` "3" \<open>q < length M\<close> read_length immobile_def
          by simp
        then have "act (?as ! k) (tps ! k) = (tps ! k) |:=| (fst (?as ! k))"
          by (metis act_Stay' prod.collapse)
        then have "|.| (act (?as ! k) (tps ! k)) = fst (?as ! k)"
          by simp
        with 1 have 2: "|.| (last (map (\<lambda>(a, tp). act a tp) (zip ?as tps))) = fst (?as ! k)"
          by simp

        have "fst (last (snd ((M ! q) (read tps)))) = fst (last ?as)"
          using qtps by simp
        then have "fst (last (snd ((M ! q) (read tps)))) = fst (?as ! k)"
          using `length ?as = Suc k` by (simp add: last_length)
        with 2 show ?thesis
          by simp
      qed

      have "(if fst ((M ! q) ?rs) \<ge> ?Q
         then b * ?Q
         else ( |.| (last ?tpsSuc) + b - 1) mod b * ?Q + fst ((M ! q) ?rs)) =
        (if fst ((M ! q) (read tps)) \<ge> ?Q
         then b * ?Q
         else ( |.| (last ?tpsSuc) + b - 1) mod b * ?Q + fst ((M ! q) (read tps)))"
        using qtps by simp
      also have "... =
        (if fst ((M ! q) (read tps)) = ?Q
         then b * ?Q
         else ( |.| (last ?tpsSuc) + b - 1) mod b * ?Q + fst ((M ! q) (read tps)))"
        using assms(1) turing_machine_def
        by (metis (mono_tags, lifting) "3" turing_commandD(4) \<open>q < length M\<close> le_antisym nth_mem prod.sel(2) qtps read_length)
      also have "... =
         (if fst ((M ! q) (read tps)) = length M
          then b * ?Q
          else (fst (last (snd ((M ! q) (read tps)))) + b - 1) mod b * ?Q + fst ((M ! q) (read tps)))"
        using * by simp
      finally show ?thesis
        using lhs by simp
    qed

    have snd: "map (\<lambda>(a, tp). act a tp) (zip ?as' (butlast tps)) =
        butlast (map (\<lambda>(a, tp). act a tp) (zip ?as tps))"
    proof (rule nth_equalityI)
      let ?lhs = "map (\<lambda>(a, tp). act a tp) (zip ?as' (butlast tps))"
      let ?rhs = "butlast (map (\<lambda>(a, tp). act a tp) (zip ?as tps))"
      have "||?scfg|| = k"
        using \<open>length tps = Suc k\<close> scfg by simp
      then have "length ?rs' = k"
        by (simp add: read_length)
      then have "length ?as' = k"
        using cartesian_num_tapes q_less assms(1,3) by simp
      moreover have "length (butlast tps) = k"
        using `length tps = Suc k` by simp
      ultimately have "length ?lhs = k"
        by simp

      have "length ?as = Suc k"
        using \<open>length tps = Suc k\<close> \<open>q < length M\<close> assms(1) qtps read_length turing_machine_def
        by (metis "3" turing_commandD(1) nth_mem)
      then have "length ?rhs = k"
        using `length tps = Suc k` by simp
      then show "length ?lhs = length ?rhs"
        using `length ?lhs = k` by simp

      show "?lhs ! j = ?rhs ! j" if "j < length ?lhs" for j
      proof -
        have "j < k"
          using that `length ?lhs = k` by auto

        have "length (butlast tps) = k"
          using \<open>length (butlast tps) = k\<close> by blast
        then have lhs: "?lhs ! j = act (?as' ! j) (tps ! j)"
          using `j < k` `length ?as' = k` by (simp add: nth_butlast)

        have rhs: "?rhs ! j = act (?as ! j) (tps ! j)"
          using `j < k` `length ?as = Suc k` `length tps = Suc k` by (simp add: nth_butlast)

        have "?as' ! j = snd (
            (let (q', as) = (M ! q) (?rs' @ [ |.| (last tps)])
             in (if q' = length M then b * length M else (fst (last as) + b - 1) mod b * length M + q',
                 butlast as))) ! j"
          using cmd' by simp
        also have "... = snd (
            ((if fst ((M ! q) (?rs' @ [ |.| (last tps)])) = length M
              then b * length M
              else (fst (last (snd ((M ! q) (?rs' @ [ |.| (last tps)])))) + b - 1) mod b * length M + fst ((M ! q) (?rs' @ [ |.| (last tps)])),
             butlast (snd ((M ! q) (?rs' @ [ |.| (last tps)])))))) ! j"
          by (metis (no_types, lifting) case_prod_unfold)
        also have "... = butlast (snd ((M ! q) (?rs' @ [ |.| (last tps)]))) ! j"
          by simp
        finally have "?as' ! j = butlast (snd ((M ! q) (?rs' @ [ |.| (last tps)]))) ! j" .
        then have as'_j: "?as' ! j = butlast (snd ((M ! q) (read tps))) ! j"
          using rs'_read by simp

        have "?as ! j = snd ((M ! q) (read tps)) ! j"
          using qtps by simp
        moreover have "?as ! j = (butlast ?as) ! j"
          using `length ?as = Suc k` `j < k` by (simp add: nth_butlast)
        ultimately have "?as ! j = butlast (snd ((M ! q) (read tps))) ! j"
          using qtps by simp
        then have "?as ! j = ?as' ! j"
          using as'_j by simp
        then show ?thesis
          using lhs rhs by simp
      qed
    qed
    then show ?thesis
      using fst lhs rhs by simp
  qed
  then show ?case
    by (simp add: Suc.IH)
qed

text \<open>
One assumption of the previous lemma is that the memorization tape can only
contain a symbol from a certain range (except in the halting state). One way to
achieve this is for the Turing machine to only ever write a symbol from that
range to the memorization tape (or switch to the halting state). Formally:
\<close>

definition bounded_write :: "machine \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bounded_write M k b \<equiv>
    \<forall>q rs. q < length M \<longrightarrow> length rs = Suc k \<longrightarrow> (M ! q) rs [.] k < b \<or> fst ((M ! q) rs) = length M"

text \<open>
The advantage of @{const bounded_write} is that it is a relatively easy to prove
property of a Turing machine. With @{const bounded_write} the previous lemma,
@{thm [source] cartesian_execute}, turns into the following one, where the
assumption $b > 0$ becomes $b > 1$ because initially the memorization tape has
the start symbol, represented by the number~1.

\null
\<close>

lemma cartesian_execute_onesie:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "k \<ge> 2"
    and "b > 1"
    and "length tps = k"
    and "bounded_write M k b"
  shows "execute (cartesian M b) (0, tps) t = squish b (length M) (execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t)"
proof -
  have "execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t <.> k < b \<or> fst (execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t) = length M"
    for t
  proof (induction t)
    case 0
    then show ?case
      using assms by auto
  next
    case (Suc t)
    let ?tps = "tps @ [\<lceil>\<triangleright>\<rceil>]"
    have *: "execute M (0, ?tps) (Suc t) = exe M (execute M (0, ?tps) t)"
        (is "_ = exe M ?cfg")
      by simp
    show ?case
    proof (cases "fst ?cfg \<ge> length M")
      case True
      then show ?thesis
        using * Suc exe_ge_length by presburger
    next
      case False
      let ?rs = "config_read ?cfg"
      let ?q = "fst ?cfg"
      let ?tps = "snd ?cfg"
      have len: "length ?tps = Suc k"
        using assms(1,5) execute_num_tapes by simp
      have pos: "?tps :#: k = 0"
        using assms immobile_head_pos onesie_def by auto
      have lenrs: "length ?rs = Suc k"
        using len read_length by simp
      have **: "exe M ?cfg = sem (M ! ?q) ?cfg"
        using False exe_lt_length by simp
      have ***: "sem (M ! ?q) ?cfg <!> k = act ((M ! ?q) ?rs [!] k) (?tps ! k)"
      proof -
        have "proper_command (Suc k) (M ! ?q)"
          by (metis False turing_commandD(1) assms(1) le_less_linear nth_mem turing_machine_def)
        then show ?thesis
          using len sem_snd by blast
      qed

      have "(M ! ?q) ?rs [~] k = Stay"
        using assms(2) lenrs False immobile_def by simp
      then have act: "act ((M ! ?q) ?rs [!] k) (?tps ! k) = (?tps ! k) |:=| ((M ! ?q) ?rs [.] k)"
        using act_Stay' by (metis prod.collapse)
       show ?thesis
      proof (cases "(M ! ?q) ?rs [.] k < b")
        case True
        then have "sem (M ! ?q) ?cfg <.> k < b"
          using pos *** act by simp
        then show ?thesis
          using * ** by simp
      next
        case halt: False
        then have "fst ((M ! ?q) ?rs) = length M"
          using assms(6) bounded_write_def lenrs False le_less_linear by blast
        then show ?thesis
          using * ** sem_fst by simp
      qed
    qed
  qed
  then show ?thesis
    using cartesian_execute[OF assms(1-3) _ assms(5)] assms(4) by simp
qed

text \<open>
In the following lemma, the term @{term "\<lceil>c\<rceil>"} reflects the fact that in
the halting state the memorized symbol can be anything.
\<close>

lemma cartesian_transforms_onesie:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "k \<ge> 2"
    and "b > 1"
    and "bounded_write M k b"
    and "length tps = k"
    and "transforms M (tps @ [\<lceil>\<triangleright>\<rceil>]) t (tps' @ [\<lceil>c\<rceil>])"
  shows "transforms (cartesian M b) tps t tps'"
proof -
  have "execute M (0, tps @ [\<lceil>\<triangleright>\<rceil>]) t = (length M, tps' @ [\<lceil>c\<rceil>])"
    using transforms_def transits_def by (metis (no_types, lifting) assms(7) execute_after_halting_ge fst_conv)
  then have "execute (cartesian M b) (0, tps) t = squish b (length M) (length M, tps' @ [\<lceil>c\<rceil>])"
    using assms cartesian_execute_onesie by simp
  moreover from this have "fst (execute (cartesian M b) (0, tps) t) = b * length M"
    using squish_halt_state[of b _ "length M"] One_nat_def assms(4) by simp
  ultimately have "execute (cartesian M b) (0, tps) t = (b * length M, tps')"
    using squish by simp
  then show ?thesis
    using transforms_def transits_def length_cartesian by auto
qed

text \<open>
A Turing machine with alphabet $G$, when started on a symbol sequence over $G$,
is guaranteed to only write symbols from $G$ to any of its tapes, including any
memorization tapes. Therefore the last assumption of
lemma~@{thm [source] cartesian_execute} is satisfied. So in the case of the start
configuration we do not need any extra assumptions such as @{const
bounded_write}. This is formalized in the next lemma. The downside is that it
can only be applied to ``finished'' TMs but not to reusable TMs, because these
do not usually start in the start state.
\<close>

lemma cartesian_execute_start_config:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "k \<ge> 2"
    and "\<forall>i<length zs. zs ! i < G"
  shows "execute (cartesian M G) (start_config k zs) t =
    squish G (length M) (execute M (start_config (Suc k) zs) t)"
proof -
  let ?tps = "snd (start_config k zs)"
  have "snd (start_config (Suc k) zs) =
    (\<lambda>i. if i = 0 then 1 else if i \<le> length zs then zs ! (i - 1) else 0, 0) #
        replicate k (\<lambda>i. if i = 0 then 1 else 0, 0)"
    using start_config_def by auto
  also have "... = (\<lambda>i. if i = 0 then 1 else if i \<le> length zs then zs ! (i - 1) else 0, 0) #
        replicate (k - 1) (\<lambda>i. if i = 0 then 1 else 0, 0) @ [(\<lambda>i. if i = 0 then 1 else 0, 0)]"
    using assms(3)
    by (metis (no_types, lifting) One_nat_def Suc_1 Suc_le_D Suc_pred less_Suc_eq_0_disj replicate_Suc replicate_append_same)
  also have "... = snd (start_config k zs) @ [(\<lambda>i. if i = 0 then 1 else 0, 0)]"
    using start_config_def by auto
  finally have "snd (start_config (Suc k) zs) = snd (start_config k zs) @ [\<lceil>\<triangleright>\<rceil>]"
    using onesie_def by auto
  then have *: "start_config (Suc k) zs = (0, ?tps @ [\<lceil>\<triangleright>\<rceil>])"
    using start_config_def by simp
  then have "execute M (0, ?tps @ [\<lceil>\<triangleright>\<rceil>]) t <.> k < G" for t
    using assms(1,4) by (metis lessI tape_alphabet)
  moreover have "G \<ge> 2"
    using assms(1) turing_machine_def by simp
  moreover have "length ?tps = k"
    using start_config_length assms(3) by simp
  ultimately have "execute (cartesian M G) (0, ?tps) t =
      squish G (length M) (execute M (0, ?tps @ [\<lceil>\<triangleright>\<rceil>]) t)"
    using cartesian_execute[OF assms(1-3)] by simp
  moreover have "start_config k zs = (0, ?tps)"
    using start_config_def by simp
  ultimately show ?thesis
    using * by simp
qed

text \<open>
So far we have only considered single memorization tapes. But of course we
can have more than one by iterating the @{const cartesian} function. Applying
this functions once removes the final memorization tape, but leaves others
intact, that is, it maintains immobile tapes:
\<close>

lemma cartesian_immobile:
  assumes "turing_machine (Suc k) G M"
    and "j < k"
    and "immobile M j (Suc k)"
    and "M' = cartesian M G"
  shows "immobile M' j k"
proof standard+
  fix q :: nat and rs :: "symbol list"
  assume q: "q < length M'" and rs: "length rs = k"
  have "q < G * length M"
    using assms(1,4) q length_cartesian by simp
  then have "G > 0"
    using gr0I by fastforce
  have "length M > 0"
    using \<open>q < G * length M\<close> by auto
  define h where "h = q div length M"
  moreover define i where "i = q mod length M"
  then have "i < length M"
    using \<open>0 < length M\<close> mod_less_divisor by simp
  have "h < G"
    using i_def h_def \<open>q < G * length M\<close> less_mult_imp_div_less by blast
  have "q = h * length M + i"
    using h_def i_def by simp
  then have "M' ! q = (\<lambda>rs.
      (let (q', as) = (M ! i) (rs @ [(h + 1) mod G])
       in (if q' = length M then G * length M else (fst (last as) + G - 1) mod G * length M + q',
           butlast as)))"
    using assms(1,4) `h < G` `i < length M` cartesian_at by auto
  then have "(M' ! q) rs =
      (let (q', as) = (M ! i) (rs @ [(h + 1) mod G])
       in (if q' = length M then G * length M else (fst (last as) + G - 1) mod G * length M + q',
           butlast as))" for rs
    by simp
  then have "(M' ! q) rs =
      (let qas = (M ! i) (rs @ [(h + 1) mod G])
       in (if fst qas = length M then G * length M else (fst (last (snd qas)) + G - 1) mod G * length M + fst qas,
           butlast (snd qas)))" for rs
    by (metis (no_types, lifting) old.prod.case prod.collapse)
  then have "(M' ! q) rs =
      (if (fst ((M ! i) (rs @ [(h + 1) mod G]))) = length M
       then G * length M
       else (fst (last (snd ((M ! i) (rs @ [(h + 1) mod G])))) + G - 1) mod G * length M + fst ((M ! i) (rs @ [(h + 1) mod G])),
       butlast (snd ((M ! i) (rs @ [(h + 1) mod G]))))" for rs
    by metis
  then have 1: "snd ((M' ! q) rs) = butlast (snd ((M ! i) (rs @ [(h + 1) mod G])))" for rs
    by simp

  have len: "length (rs @ [(h + 1) mod G]) = Suc k"
    by (simp add: rs)
  then have 2: "(M ! i) (rs @ [(h + 1) mod G]) [~] j = Stay"
    using immobile_def assms(3) len \<open>i < length M\<close> by blast
  have "length (snd ((M ! i) (rs @ [(h + 1) mod G]))) = Suc k"
    using len assms(1) turing_machine_def by (metis turing_commandD(1) \<open>i < length M\<close> turing_machineD(3))
  then have "butlast (snd ((M ! i) (rs @ [(h + 1) mod G]))) ! j =
      snd ((M ! i) (rs @ [(h + 1) mod G])) ! j"
    using assms(2) by (simp add: nth_butlast)
  then have "snd ((M' ! q) rs) ! j = snd ((M ! i) (rs @ [(h + 1) mod G])) ! j"
    using 1 by simp
  then show "(M' ! q) rs [~] j = Stay"
    using 2 by simp
qed

text \<open>
With the next function, @{term icartesian}, we can strip several memorization
tapes off.
\<close>

fun icartesian :: "nat \<Rightarrow> machine \<Rightarrow> nat \<Rightarrow> machine" where
  "icartesian 0 M G = M" |
  "icartesian (Suc k) M G = icartesian k (cartesian M G) G"

text \<open>
Applying @{const icartesian} maintains the property of being a Turing machine.
We show that only for the special case that all tapes but the input and output
tapes are memorization tapes. In this case, we end up with a two-tape machine.
\<close>

lemma icartesian_tm:
  assumes "turing_machine (k + 2) G M"
    and "\<And>j. j < k \<Longrightarrow> immobile M (j + 2) (k + 2)"
  shows "turing_machine 2 G (icartesian k M G)"
  using assms(1,2)
proof (induction k arbitrary: M)
  case 0
  then show ?case
    by (metis add.left_neutral icartesian.simps(1))
next
  case (Suc k)
  let ?M = "cartesian M G"
  have "turing_machine (Suc (k + 2)) G M"
    using Suc by simp
  moreover have "k + 2 \<ge> 2"
    by simp
  ultimately have "turing_machine (k + 2) G ?M"
    using \<open>turing_machine (Suc (k + 2)) G M\<close> cartesian_tm' by blast
  moreover have "\<And>j. j < k \<Longrightarrow> immobile ?M (j + 2) (k + 2)"
    using cartesian_immobile Suc by simp
  ultimately have "turing_machine 2 G (icartesian k ?M G)"
    using Suc by simp
  then show "turing_machine 2 G (icartesian (Suc k) M G)"
    by simp
qed

text \<open>
At this point we ought to prove something about the semantics of @{const
icartesian}. However, we will only need one specific result, which we can only
express at the end of Section~\ref{s:oblivious-tm} after we have introduced
oblivious Turing machines.
\<close>

end
