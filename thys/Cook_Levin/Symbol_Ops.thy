section \<open>Symbol sequence operations\<close>

theory Symbol_Ops
  imports Two_Four_Symbols
begin

text \<open>
While previous sections have focused on ``formatted'' symbol sequences for
numbers and lists, in this section we devise some Turing machines dealing with
``unstructured'' arbitrary symbol sequences. The only ``structure'' that is
often imposed is that of not containing a blank symbol because when reading a
symbol sequence, say from the input tape, a blank would signal the end of the
symbol sequence.
\<close>


subsection \<open>Checking for being over an alphabet\<close>

text \<open>
In this section we devise a Turing machine that checks if a proper symbol sequence
is over a given alphabet represented by an upper bound symbol $z$.
\<close>

abbreviation proper_symbols_lt :: "symbol \<Rightarrow> symbol list \<Rightarrow> bool" where
  "proper_symbols_lt z zs \<equiv> proper_symbols zs \<and> symbols_lt z zs"

text \<open>
The next Turing machine checks if the symbol sequence (up until the first blank)
on tape $j_1$ contains only symbols from $\{2, \dots, z - 1\}$, where $z$ is a
parameter of the TM, and writes to tape $j_2$ the number~1 or~0, representing
True or False, respectively. It assumes that $j_2$ initially contains at most
one symbol.
\<close>

definition tm_proper_symbols_lt :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_proper_symbols_lt j1 j2 z \<equiv>
    tm_write j2 \<one> ;;
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      IF \<lambda>rs. rs ! j1 < 2 \<or> rs ! j1 \<ge> z THEN
        tm_write j2 \<box>
      ELSE
        []
      ENDIF ;;
      tm_right j1
    DONE ;;
    tm_cr j1"

lemma tm_proper_symbols_lt_tm:
  assumes "0 < j2" "j1 < k" "j2 < k" and "G \<ge> 4"
  shows "turing_machine k G (tm_proper_symbols_lt j1 j2 z)"
  using assms tm_write_tm tm_right_tm tm_cr_tm Nil_tm tm_proper_symbols_lt_def
    turing_machine_loop_turing_machine turing_machine_branch_turing_machine
  by simp

locale turing_machine_proper_symbols_lt =
  fixes j1 j2 :: tapeidx and z :: symbol
begin

definition "tm1 \<equiv> tm_write j2 \<one>"
definition "tm2 \<equiv> IF \<lambda>rs. rs ! j1 < 2 \<or> rs ! j1 \<ge> z THEN tm_write j2 \<box> ELSE [] ENDIF"
definition "tm3 \<equiv> tm2 ;; tm_right j1"
definition "tm4 \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tm3 DONE"
definition "tm5 \<equiv> tm1 ;; tm4"
definition "tm6 \<equiv> tm5 ;; tm_cr j1"

lemma tm6_eq_tm_proper_symbols_lt: "tm6 = tm_proper_symbols_lt j1 j2 z"
  unfolding tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_proper_symbols_lt_def
  by simp

context
  fixes zs :: "symbol list" and tps0 :: "tape list" and k :: nat
  assumes jk: "k = length tps0" "j1 \<noteq> j2" "j1 < k" "j2 < k"
    and zs: "proper_symbols zs"
    and tps0:
      "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
      "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 t \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, Suc t),
   j2 := (if proper_symbols_lt z (take t zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)]"

lemma tm1 [transforms_intros]: "transforms tm1 tps0 1 (tps1 0)"
  unfolding tm1_def
proof (tform tps: jk tps0)
  have "(if proper_symbols_lt z (take 0 zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1) = (\<lfloor>[\<one>]\<rfloor>, 1)"
    by simp
  moreover have "tps0 ! j2 |:=| \<one> = (\<lfloor>[\<one>]\<rfloor>, 1)"
    using tps0(2) contents_def by auto
  moreover have "tps0[j1 := (\<lfloor>zs\<rfloor>, Suc 0)] = tps0"
    using tps0(1) by (metis One_nat_def list_update_id)
  ultimately show "tps1 0 = tps0[j2 := tps0 ! j2 |:=| \<one>]"
    unfolding tps1_def by auto
qed

definition "tps2 t \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, Suc t),
   j2 := (if proper_symbols_lt z (take (Suc t) zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)]"

lemma tm2 [transforms_intros]:
  assumes "t < length zs"
  shows "transforms tm2 (tps1 t) 3 (tps2 t)"
  unfolding tm2_def
proof (tform tps: jk tps1_def)
  have "tps1 t ! j1 = (\<lfloor>zs\<rfloor>, Suc t)"
    using tps1_def jk by simp
  moreover have "read (tps1 t) ! j1 = tps1 t :.: j1"
    using tapes_at_read' jk tps1_def by (metis (no_types, lifting) length_list_update)
  ultimately have *: "read (tps1 t) ! j1 = zs ! t"
    using contents_inbounds assms(1) by simp
  have j2: "tps1 t ! j2 = (if proper_symbols_lt z (take t zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)"
    using tps1_def jk by simp
  show "tps2 t = (tps1 t)[j2 := tps1 t ! j2 |:=| \<box>]" if "read (tps1 t) ! j1 < 2 \<or> z \<le> read (tps1 t) ! j1"
  proof -
    have c3: "(\<lfloor>[\<one>]\<rfloor>, 1) |:=| \<box> = (\<lfloor>[]\<rfloor>, 1)"
      using contents_def by auto
    have "(if proper_symbols_lt z (take t zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1) |:=| \<box> =
       (if proper_symbols_lt z (take (Suc t) zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)"
    proof (cases "proper_symbols_lt z (take t zs)")
      case True
      have "zs ! t < 2 \<or> z \<le> zs ! t"
        using that * by simp
      then have "\<not> proper_symbols_lt z (take (Suc t) zs)"
        using assms(1) by auto
      then show ?thesis
        using c3 by auto
    next
      case False
      then have "\<not> proper_symbols_lt z (take (Suc t) zs)"
        by auto
      then show ?thesis
        using c3 False by auto
    qed
    then have "tps1 t ! j2 |:=| \<box> = (if proper_symbols_lt z (take (Suc t) zs) then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)"
      using j2 by simp
    then show "tps2 t = (tps1 t)[j2 := tps1 t ! j2 |:=| \<box>]"
      unfolding tps2_def tps1_def using c3 jk(1,4) by simp
  qed
  show "tps2 t = tps1 t" if "\<not> (read (tps1 t) ! j1 < 2 \<or> z \<le> read (tps1 t) ! j1)"
  proof -
    have 1: "zs ! t \<ge> 2 \<and> z > zs ! t"
      using that * by simp
    show "tps2 t = tps1 t"
    proof (cases "proper_symbols_lt z (take t zs)")
      case True
      have "proper_symbols_lt z (take (Suc t) zs)"
        using True 1 assms(1) zs by (metis length_take less_antisym min_less_iff_conj nth_take)
      then show ?thesis
        using tps1_def tps2_def jk by simp
    next
      case False
      then have "\<not> proper_symbols_lt z (take (Suc t) zs)"
        by auto
      then show ?thesis
        using tps1_def tps2_def jk False by auto
    qed
  qed
qed

lemma tm3 [transforms_intros]:
  assumes "t < length zs"
  shows "transforms tm3 (tps1 t) 4 (tps1 (Suc t))"
  unfolding tm3_def
proof (tform tps: assms jk tps2_def)
  have "tps2 t ! j1 |+| 1 = (\<lfloor>zs\<rfloor>, Suc (Suc t))"
    using tps2_def jk by simp
  then show "tps1 (Suc t) = (tps2 t)[j1 := tps2 t ! j1 |+| 1]"
    unfolding tps1_def tps2_def
    by (metis (no_types, lifting) jk(2) list_update_overwrite list_update_swap)
qed

lemma tm4 [transforms_intros]:
  assumes "ttt = 1 + 6 * length zs"
  shows "transforms tm4 (tps1 0) ttt (tps1 (length zs))"
  unfolding tm4_def
proof (tform time: assms)
  show "read (tps1 t) ! j1 \<noteq> \<box>" if "t < length zs" for t
  proof -
    have "tps1 t ! j1 = (\<lfloor>zs\<rfloor>, Suc t)"
      using tps1_def jk by simp
    moreover have "read (tps1 t) ! j1 = tps1 t :.: j1"
      using tapes_at_read' jk tps1_def by (metis (no_types, lifting) length_list_update)
    ultimately have "read (tps1 t) ! j1 = zs ! t"
      using contents_inbounds that by simp
    then show ?thesis
      using zs that by auto
  qed
  show "\<not> read (tps1 (length zs)) ! j1 \<noteq> \<box>"
  proof -
    have "tps1 (length zs) ! j1 = (\<lfloor>zs\<rfloor>, Suc (length zs))"
      using tps1_def jk by simp
    moreover have "read (tps1 (length zs)) ! j1 = tps1 (length zs) :.: j1"
      using tapes_at_read' jk tps1_def by (metis (no_types, lifting) length_list_update)
    ultimately show ?thesis
      by simp
  qed
qed

lemma tm5 [transforms_intros]:
  assumes "ttt = 2 + 6 * length zs"
  shows "transforms tm5 tps0 ttt (tps1 (length zs))"
  unfolding tm5_def
  by (tform time: assms)

definition "tps5 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, 1),
   j2 := (if proper_symbols_lt z zs then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)]"

definition "tps5' \<equiv> tps0
  [j2 := (if proper_symbols_lt z zs then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[]\<rfloor>, 1)]"

lemma tm6:
  assumes "ttt = 5 + 7 * length zs"
  shows "transforms tm6 tps0 ttt tps5'"
  unfolding tm6_def
proof (tform time: assms tps1_def jk)
  have *: "tps1 (length zs) ! j1 = (\<lfloor>zs\<rfloor>, Suc (length zs))"
    using tps1_def jk by simp
  show "clean_tape (tps1 (length zs) ! j1)"
    using * zs by simp
  have "tps5 = (tps1 (length zs))[j1 :=  (\<lfloor>zs\<rfloor>, Suc (length zs)) |#=| 1]"
    unfolding tps5_def tps1_def by (simp add: list_update_swap[OF jk(2)])
  then have "tps5 = (tps1 (length zs))[j1 := tps1 (length zs) ! j1 |#=| 1]"
    using * by simp
  moreover have "tps5' = tps5"
    using tps5'_def tps5_def tps0 jk by (metis list_update_id)
  ultimately show "tps5' = (tps1 (length zs))[j1 := tps1 (length zs) ! j1 |#=| 1]"
    by simp
qed

definition "tps6 \<equiv> tps0
  [j2 := (\<lfloor>proper_symbols_lt z zs\<rfloor>\<^sub>B, 1)]"

lemma tm6':
  assumes "ttt = 5 + 7 * length zs"
  shows "transforms tm6 tps0 ttt tps6"
proof -
  have "tps6 = tps5'"
    using tps6_def tps5'_def canrepr_0 canrepr_1 by auto
  then show ?thesis
    using tm6 assms by simp
qed

end

end  (* locale *)

lemma transforms_tm_proper_symbols_ltI [transforms_intros]:
  fixes j1 j2 :: tapeidx and z :: symbol
  fixes zs :: "symbol list" and tps tps' :: "tape list" and k :: nat
  assumes "k = length tps" "j1 \<noteq> j2" "j1 < k" "j2 < k"
    and "proper_symbols zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 5 + 7 * length zs"
  assumes "tps' = tps
    [j2 := (\<lfloor>proper_symbols_lt z zs\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_proper_symbols_lt j1 j2 z) tps ttt tps'"
proof -
  interpret loc: turing_machine_proper_symbols_lt j1 j2 .
  show ?thesis
    using assms loc.tm6_eq_tm_proper_symbols_lt loc.tps6_def loc.tm6' by simp
qed


subsection \<open>The length of the input\<close>

text \<open>
The Turing machine in this section reads the input tape until the first blank
and increments a counter on tape $j$ for every symbol read. In the end
it performs a carriage return on the input tape, and tape $j$ contains the
length of the input as binary number. For this to work, tape $j$ must initially
be empty.
\<close>

lemma proper_tape_read:
  assumes "proper_symbols zs"
  shows "|.| (\<lfloor>zs\<rfloor>, i) = \<box> \<longleftrightarrow> i > length zs"
proof -
  have "|.| (\<lfloor>zs\<rfloor>, i) = \<box>" if "i > length zs" for i
    using that contents_outofbounds by simp
  moreover have "|.| (\<lfloor>zs\<rfloor>, i) \<noteq> \<box>" if "i \<le> length zs" for i
    using that contents_inbounds assms contents_def proper_symbols_ne0 by simp
  ultimately show ?thesis
    by (meson le_less_linear)
qed

definition tm_length_input :: "tapeidx \<Rightarrow> machine" where
  "tm_length_input j \<equiv>
    WHILE [] ; \<lambda>rs. rs ! 0 \<noteq> \<box> DO
      tm_incr j ;;
      tm_right 0
    DONE ;;
    tm_cr 0"

lemma tm_length_input_tm:
  assumes "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_length_input j)"
  using tm_length_input_def tm_incr_tm assms Nil_tm tm_right_tm tm_cr_tm
  by (simp add: turing_machine_loop_turing_machine)

locale turing_machine_length_input =
  fixes j :: tapeidx
begin

definition "tmL1 \<equiv> tm_incr j"
definition "tmL2 \<equiv> tmL1 ;; tm_right 0"
definition "tm1 \<equiv> WHILE [] ; \<lambda>rs. rs ! 0 \<noteq> \<box> DO tmL2 DONE"
definition "tm2 \<equiv> tm1 ;; tm_cr 0"

lemma tm2_eq_tm_length_input: "tm2 = tm_length_input j"
  unfolding tm2_def tm1_def tmL2_def tmL1_def tm_length_input_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and zs :: "symbol list"
  assumes jk: "0 < j" "j < k" "length tps0 = k"
    and zs: "proper_symbols zs"
    and tps0:
      "tps0 ! 0 = (\<lfloor>zs\<rfloor>, 1)"
      "tps0 ! j = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0[0 := (\<lfloor>zs\<rfloor>, 1 + t), j := (\<lfloor>t\<rfloor>\<^sub>N, 1)]"

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
  using tpsL_def tps0 jk by (metis One_nat_def list_update_id plus_1_eq_Suc)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0[0 := (\<lfloor>zs\<rfloor>, 1 + t), j := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1)]"

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0[0 := (\<lfloor>zs\<rfloor>, 1 + Suc t), j := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "t < length zs" and "ttt = 5 + 2 * nlength t"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def
  by (tform tps: assms(1) tpsL_def tpsL1_def tps0 jk time: assms(2))

lemma tmL2:
  assumes "t < length zs" and "ttt = 6 + 2 * nlength t"
  shows "transforms tmL2 (tpsL t) ttt (tpsL (Suc t))"
  unfolding tmL2_def
proof (tform tps: assms(1) tpsL_def tpsL1_def tps0 jk time: assms(2))
  have "tpsL1 t ! 0 = (\<lfloor>zs\<rfloor>, 1 + t)"
    using tpsL2_def tpsL1_def jk tps0 by simp
  then have "tpsL2 t = (tpsL1 t)[0 := tpsL1 t ! 0 |#=| Suc (tpsL1 t :#: 0)]"
    using tpsL2_def tpsL1_def jk tps0
    by (smt (z3) fstI list_update_overwrite list_update_swap nat_neq_iff plus_1_eq_Suc prod.sel(2))
  then show "tpsL (Suc t) = (tpsL1 t)[0 := tpsL1 t ! 0 |+| 1]"
    using tpsL2_def tpsL_def tpsL1_def jk tps0 by simp
qed

lemma tmL2':
  assumes "t < length zs" and "ttt = 6 + 2 * nlength (length zs)"
  shows "transforms tmL2 (tpsL t) ttt (tpsL (Suc t))"
proof -
  have "6 + 2 * nlength t \<le> 6 + 2 * nlength (length zs)"
    using assms(1) nlength_mono by simp
  then show ?thesis
    using assms tmL2 transforms_monotone by blast
qed

lemma tm1:
  assumes "ttt = length zs * (8 + 2 * nlength (length zs)) + 1"
  shows "transforms tm1 (tpsL 0) ttt (tpsL (length zs))"
  unfolding tm1_def
proof (tform)
  let ?t = "6 + 2 * nlength (length zs)"
  show "\<And>t. t < length zs \<Longrightarrow> transforms tmL2 (tpsL t) ?t (tpsL (Suc t))"
    using tmL2' by simp
  have *: "tpsL t ! 0 = (\<lfloor>zs\<rfloor>, Suc t)" for t
    using tpsL_def jk by simp
  then show "\<And>t. t < length zs \<Longrightarrow> read (tpsL t) ! 0 \<noteq> \<box>"
    using proper_tape_read[OF zs] tpsL_def jk tapes_at_read'
    by (metis length_list_update less_Suc_eq_0_disj not_less_eq)
  show "\<not> read (tpsL (length zs)) ! 0 \<noteq> \<box>"
    using proper_tape_read[OF zs] tpsL_def jk tapes_at_read' *
    by (metis length_list_update less_Suc_eq_0_disj less_imp_Suc_add nat_neq_iff not_less_less_Suc_eq)
  show "length zs * (6 + 2 * nlength (length zs) + 2) + 1 \<le> ttt"
    using assms by simp
qed

lemma tmL' [transforms_intros]:
  assumes "ttt = 10 * length zs ^ 2 + 1"
  shows "transforms tm1 (tpsL 0) ttt (tpsL (length zs))"
proof -
  let ?ttt = "length zs * (8 + 2 * nlength (length zs)) + 1"
  have "?ttt \<le> length zs * (8 + 2 * length zs) + 1"
    using nlength_le_n by simp
  also have "... \<le> 8 * length zs + 2 * length zs ^ 2 + 1"
    by (simp add: add_mult_distrib2 power2_eq_square)
  also have "... \<le> 10 * length zs ^ 2 + 1"
    using linear_le_pow by simp
  finally have "?ttt \<le> 10 * length zs ^ 2 + 1" .
  then show ?thesis
    using tm1 assms transforms_monotone by simp
qed

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps0[0 := (\<lfloor>zs\<rfloor>, 1), j := (\<lfloor>length zs\<rfloor>\<^sub>N, 1)]"

lemma tm2:
  assumes "ttt = 10 * length zs ^ 2 + length zs + 4"
  shows "transforms tm2 (tpsL 0) ttt tps2"
  unfolding tm2_def
proof (tform time: assms tpsL_def jk tps: tpsL_def tpsL1_def tps0 jk)
  show "clean_tape (tpsL (length zs) ! 0)"
   using tpsL_def jk clean_contents_proper[OF zs] by simp
  have "tpsL (length zs) ! 0 = (\<lfloor>zs\<rfloor>, Suc (length zs))"
    using tpsL_def jk by simp
  then show "tps2 = (tpsL (length zs))[0 := tpsL (length zs) ! 0 |#=| 1]"
    using tps2_def tpsL_def jk by (simp add: list_update_swap_less)
qed

definition tps2' :: "tape list" where
  "tps2' \<equiv> tps0[j := (\<lfloor>length zs\<rfloor>\<^sub>N, 1)]"

lemma tm2':
  assumes "ttt = 11 * length zs ^ 2 + 4"
  shows "transforms tm2 tps0 ttt tps2'"
proof -
  have "10 * length zs ^ 2 + length zs + 4 \<le> ttt"
    using assms linear_le_pow[of 2 "length zs"] by simp
  moreover have "tps2 = tps2'"
    using tps2_def tps2'_def jk tps0 by (metis list_update_id)
  ultimately show ?thesis
    using transforms_monotone tm2 tpsL_eq_tps0 by simp
qed

end

end

lemma transforms_tm_length_inputI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and zs :: "symbol list"
  assumes "0 < j" "j < k" "length tps = k"
    and "proper_symbols zs"
  assumes
    "tps ! 0 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 11 * length zs ^ 2 + 4"
  assumes "tps' = tps
    [j := (\<lfloor>length zs\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_length_input j) tps ttt tps'"
proof -
  interpret loc: turing_machine_length_input j .
  show ?thesis
    using loc.tm2' loc.tps2'_def loc.tm2_eq_tm_length_input assms by simp
qed


subsection \<open>Whether the length is even\<close>

text \<open>
The next Turing machines reads the symbols on tape $j_1$ until the first blank
and alternates between numbers~0 and~1 on tape $j_2$. Then tape $j_2$
contains the parity of the length of the symbol sequence on tape $j_1$. Finally, the TM
flips the output once more, so that tape $j_2$ contains a Boolean indicating
whether the length was even or not. We assume tape $j_2$ is initially empty,
that is, represents the number~0.
\<close>

definition tm_even_length :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_even_length j1 j2 \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      tm_not j2 ;;
      tm_right j1
    DONE ;;
    tm_not j2 ;;
    tm_cr j1"

lemma tm_even_length_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j1 < k" "0 < j2" "j2 < k"
  shows "turing_machine k G (tm_even_length j1 j2)"
  using tm_even_length_def tm_right_tm tm_not_tm Nil_tm assms tm_cr_tm turing_machine_loop_turing_machine
  by simp

locale turing_machine_even_length =
  fixes j1 j2 :: tapeidx
begin

definition "tmB \<equiv> tm_not j2 ;; tm_right j1"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tmB DONE"
definition "tm2 \<equiv> tmL ;; tm_not j2"
definition "tm3 \<equiv> tm2 ;; tm_cr j1"

lemma tm3_eq_tm_even_length: "tm3 = tm_even_length j1 j2"
  unfolding tm3_def tm2_def tmL_def tmB_def tm_even_length_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and zs :: "symbol list"
  assumes zs: "proper_symbols zs"
  assumes jk: "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, Suc t),
     j2 := (\<lfloor>odd t\<rfloor>\<^sub>B, 1)]"

lemma tpsL0: "tpsL 0 = tps0"
  unfolding tpsL_def using tps0 jk by (metis (mono_tags, opaque_lifting) One_nat_def even_zero list_update_id)

lemma tmL2 [transforms_intros]: "transforms tmB (tpsL t) 4 (tpsL (Suc t))"
  unfolding tmB_def
proof (tform tps: tpsL_def jk)
  have "(tpsL t)
    [j2 := (\<lfloor>(if odd t then 1 else 0 :: nat) \<noteq> 1\<rfloor>\<^sub>B, 1),
     j1 := (tpsL t)[j2 := (\<lfloor> (if odd t then 1 else 0 :: nat) \<noteq> 1 \<rfloor>\<^sub>B, 1)] ! j1 |+| 1] =
    (tpsL t)
    [j2 := (\<lfloor>odd (Suc t)\<rfloor>\<^sub>B, 1),
     j1 := (tpsL t) ! j1 |+| 1]"
    using jk by simp
  also have "... = (tpsL t)
    [j2 := (\<lfloor>odd (Suc t)\<rfloor>\<^sub>B, 1),
     j1 := (\<lfloor>zs\<rfloor>, Suc (Suc t))]"
    using tpsL_def jk by simp
  also have "... = (tpsL t)
    [j1 := (\<lfloor>zs\<rfloor>, Suc (Suc t)),
     j2 := (\<lfloor>odd (Suc t)\<rfloor>\<^sub>B, 1)]"
    using jk by (simp add: list_update_swap)
  also have "... = tps0
    [j1 := (\<lfloor>zs\<rfloor>, Suc (Suc t)),
     j2 := (\<lfloor>odd (Suc t)\<rfloor>\<^sub>B, 1)]"
    using jk tpsL_def by (simp add: list_update_swap)
  also have "... = tpsL (Suc t)"
    using tpsL_def by simp
  finally show "tpsL (Suc t) = (tpsL t)
    [j2 := (\<lfloor>(if odd t then 1 else 0 :: nat) \<noteq> 1\<rfloor>\<^sub>B, 1),
     j1 := (tpsL t)[j2 := (\<lfloor>(if odd t then 1 else 0 :: nat) \<noteq> 1\<rfloor>\<^sub>B, 1)] ! j1 |+| 1]"
    by simp
qed

lemma tmL:
  assumes "ttt = 6 * length zs + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length zs))"
  unfolding tmL_def
proof (tform time: assms)
  have "read (tpsL t) ! j1 = tpsL t :.: j1" for t
    using tpsL_def tapes_at_read' jk
    by (metis (no_types, lifting) length_list_update)
  then have "read (tpsL t) ! j1 = \<lfloor>zs\<rfloor> (Suc t)" for t
    using tpsL_def jk by simp
  then show "\<And>t. t < length zs \<Longrightarrow> read (tpsL t) ! j1 \<noteq> \<box>" and "\<not> read (tpsL (length zs)) ! j1 \<noteq> \<box>"
    using zs by auto
qed

lemma tmL' [transforms_intros]:
  assumes "ttt = 6 * length zs + 1"
  shows "transforms tmL tps0 ttt (tpsL (length zs))"
  using assms tmL tpsL0 by simp

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
     j2 := (\<lfloor>even (length zs) \<rfloor>\<^sub>B, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 6 * length zs + 4"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tpsL_def jk time: assms)
  show "tps2 = (tpsL (length zs))[j2 := (\<lfloor>(if odd (length zs) then 1 else 0 :: nat) \<noteq> 1\<rfloor>\<^sub>B, 1)]"
    unfolding tps2_def tpsL_def by (simp add: list_update_swap)
qed

definition tps3 :: "tape list" where
  "tps3 \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, 1),
     j2 := (\<lfloor>even (length zs)\<rfloor>\<^sub>B, 1)]"

lemma tm3:
  assumes "ttt = 7 * length zs + 7"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def jk time: assms)
  show "clean_tape (tps2 ! j1)"
    using tps2_def jk zs clean_contents_proper by simp
  have "tps2 ! j1 |#=| 1 = (\<lfloor>zs\<rfloor>, 1)"
    using tps2_def jk by simp
  then show "tps3 = tps2[j1 := tps2 ! j1 |#=| 1]"
    unfolding tps3_def tps2_def using jk by (simp add: list_update_swap)
  show "ttt = 6 * length zs + 4 + (tps2 :#: j1 + 2)"
    using assms tps2_def jk by simp
qed

definition tps3' :: "tape list" where
  "tps3' \<equiv> tps0
    [j2 := (\<lfloor>even (length zs)\<rfloor>\<^sub>B, 1)]"

lemma tps3': "tps3' = tps3"
  using tps3'_def tps3_def tps0 by (metis list_update_id)

lemma tm3':
  assumes "ttt = 7 * length zs + 7"
  shows "transforms tm3 tps0 ttt tps3'"
  using tps3' tm3 assms by simp

end  (* context *)

end  (* locale *)

lemma transforms_tm_even_lengthI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and zs :: "symbol list"
  assumes "j1 < k" "j2 < k" "j1 \<noteq> j2"
    and "proper_symbols zs"
    and "length tps = k"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps
    [j2 := (\<lfloor>even (length zs)\<rfloor>\<^sub>B, 1)]"
  assumes "ttt = 7 * length zs + 7"
  shows "transforms (tm_even_length j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_even_length j1 j2 .
  show ?thesis
    using assms loc.tps3'_def loc.tm3' loc.tm3_eq_tm_even_length by simp
qed


subsection \<open>Checking for ends-with or empty\<close>

text \<open>
The next Turing machine implements a slightly idiosyncratic operation that we
use in the next section for checking if a symbol sequence represents a list of
numbers. The operation consists in checking if the symbol sequence on tape $j_1$
either is empty or ends with the symbol $z$, which is another parameter of the
TM.  If the condition is met, the number~1 is written to tape $j_2$, otherwise
the number~0.
\<close>

definition tm_empty_or_endswith :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_empty_or_endswith j1 j2 z \<equiv>
      tm_right_until j1 {\<box>} ;;
      tm_left j1 ;;
      IF \<lambda>rs. rs ! j1 \<in> {\<triangleright>, z} THEN
        tm_setn j2 1
      ELSE
        []
      ENDIF ;;
      tm_cr j1"

lemma tm_empty_or_endswith_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j2" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_empty_or_endswith j1 j2 z)"
  using assms Nil_tm tm_right_until_tm tm_left_tm tm_setn_tm tm_cr_tm
    turing_machine_branch_turing_machine tm_empty_or_endswith_def
  by simp

locale turing_machine_empty_or_endswith =
  fixes j1 j2 :: tapeidx and z :: symbol
begin

definition "tm1 \<equiv> tm_right_until j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_left j1"
definition "tmI \<equiv> IF \<lambda>rs. rs ! j1 \<in> {\<triangleright>, z} THEN tm_setn j2 1 ELSE [] ENDIF"
definition "tm3 \<equiv> tm2 ;; tmI"
definition "tm4 \<equiv> tm3 ;; tm_cr j1"

lemma tm4_eq_tm_empty_or_endswith: "tm4 = tm_empty_or_endswith j1 j2 z"
  unfolding tm4_def tm3_def tmI_def tm2_def tm1_def tm_empty_or_endswith_def
  by simp

context
  fixes tps0 :: "tape list" and k :: nat and zs :: "symbol list"
  assumes jk: "j1 \<noteq> j2" "j1 < k" "j2 < k" "length tps0 = k"
    and zs: "proper_symbols zs"
    and tps0:
      "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
      "tps0 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition tps1 :: "tape list" where
  "tps1 \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (length zs)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform time: assms tps: tps0 tps1_def jk)
  show "rneigh (tps0 ! j1) {0} (length zs)"
  proof (rule rneighI)
    show "(tps0 ::: j1) (tps0 :#: j1 + length zs) \<in> {0}"
      using tps0 by simp
    show "\<And>n'. n' < length zs \<Longrightarrow> (tps0 ::: j1) (tps0 :#: j1 + n') \<notin> {0}"
      using zs tps0 by auto
  qed
qed

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, length zs)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 2 + length zs"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
  by (tform time: assms tps: tps1_def tps2_def jk)

definition tps3 :: "tape list" where
  "tps3 \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, length zs),
     j2 := (\<lfloor>zs = [] \<or> last zs = z\<rfloor>\<^sub>B, 1)]"

lemma tmI [transforms_intros]: "transforms tmI tps2 14 tps3"
  unfolding tmI_def
proof (tform tps: tps0 tps2_def jk)
  have *: "read tps2 ! j1 = \<lfloor>zs\<rfloor> (length zs)"
    using tps2_def jk tapes_at_read'[of j1 tps2] by simp

  show "tps3 = tps2[j2 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]" if "read tps2 ! j1 \<in> {\<triangleright>, z}"
  proof -
    have "zs = [] \<or> last zs = z"
      using that * contents_inbounds zs
      by (metis diff_less dual_order.refl insert_iff last_conv_nth length_greater_0_conv proper_symbols_ne1 singletonD zero_less_one)
    then have "(if zs = [] \<or> last zs = z then 1 else 0) = 1"
      by simp
    then show ?thesis
      using tps2_def tps3_def jk by (smt (verit, best))
  qed
  show "tps3 = tps2" if "read tps2 ! j1 \<notin> {\<triangleright>, z}"
  proof -
    have "\<not> (zs = [] \<or> last zs = z)"
      using that * contents_inbounds zs
      by (metis contents_at_0 dual_order.refl insertCI last_conv_nth length_greater_0_conv list.size(3))
    then have "(if zs = [] \<or> last zs = z then 1 else 0) = 0"
      by simp
    then show ?thesis
      using tps2_def tps3_def jk tps0 by (smt (verit, best) list_update_id nth_list_update_neq)
  qed
  show "10 + 2 * nlength 0 + 2 * nlength 1 + 2 \<le> 14"
    using nlength_1_simp by simp
qed

lemma tm3 [transforms_intros]:
  assumes "ttt = 16 + length zs"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def by (tform tps: assms)

definition tps4 :: "tape list" where
  "tps4 \<equiv> tps0
    [j2 := (\<lfloor>zs = [] \<or> last zs = z\<rfloor>\<^sub>B, 1)]"

lemma tm4:
  assumes "ttt = 18 + 2 * length zs"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform time: assms tps3_def jk tps: tps3_def jk zs)
  have "tps3 ! j1 |#=| 1 = (\<lfloor>zs\<rfloor>, 1)"
    using tps3_def jk zs by simp
  then show "tps4 = tps3[j1 := tps3 ! j1 |#=| 1]"
    using tps4_def tps3_def jk tps0(1) by (metis list_update_id list_update_overwrite list_update_swap)
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_empty_or_endswithI [transforms_intros]:
  fixes j1 j2 :: tapeidx and z :: symbol
  fixes tps tps' :: "tape list" and k :: nat and zs :: "symbol list"
  assumes "j1 \<noteq> j2" "j1 < k" "j2 < k"
    and "length tps = k"
    and "proper_symbols zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 18 + 2 * length zs"
  assumes "tps' = tps
    [j2 := (\<lfloor>zs = [] \<or> last zs = z\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_empty_or_endswith j1 j2 z) tps ttt tps'"
proof -
  interpret loc: turing_machine_empty_or_endswith j1 j2 z .
  show ?thesis
    using assms loc.tps4_def loc.tm4 loc.tm4_eq_tm_empty_or_endswith by simp
qed


subsection \<open>Stripping trailing symbols\<close>

text \<open>
Stripping the symbol $z$ from the end of a symbol sequence @{term zs} means:
\<close>

definition rstrip :: "symbol \<Rightarrow> symbol list \<Rightarrow> symbol list" where
  "rstrip z zs \<equiv> take (LEAST i. i \<le> length zs \<and> set (drop i zs) \<subseteq> {z}) zs"

lemma length_rstrip: "length (rstrip z zs) = (LEAST i. i \<le> length zs \<and> set (drop i zs) \<subseteq> {z})"
  using rstrip_def wellorder_Least_lemma[where ?P="\<lambda>i. i \<le> length zs \<and> set (drop i zs) \<subseteq> {z}"] by simp

lemma length_rstrip_le: "length (rstrip z zs) \<le> length zs"
  using rstrip_def by simp

lemma rstrip_stripped:
  assumes "i \<ge> length (rstrip z zs)" and "i < length zs"
  shows "zs ! i = z"
proof -
  let ?P = "\<lambda>i. i \<le> length zs \<and> set (drop i zs) \<subseteq> {z}"
  have "?P (length zs)"
    by simp
  then have "?P i"
    using assms length_rstrip LeastI[where ?P="?P"] Least_le[where ?P="?P"]
    by (metis (mono_tags, lifting) dual_order.trans order_less_imp_le set_drop_subset_set_drop)
  then have "set (drop i zs) \<subseteq> {z}"
    by simp
  then show ?thesis
    using assms(2) by (metis Cons_nth_drop_Suc drop_eq_Nil2 leD list.set(2) set_empty singleton_insert_inj_eq subset_singletonD)
qed

lemma rstrip_replicate: "rstrip z (replicate n z) = []"
  using rstrip_def
  by (metis (no_types, lifting) Least_eq_0 empty_replicate set_drop_subset set_replicate take_eq_Nil zero_le)

lemma rstrip_not_ex:
  assumes "\<not> (\<exists>i<length zs. zs ! i \<noteq> z)"
  shows "rstrip z zs = []"
  using assms rstrip_def by (metis in_set_conv_nth replicate_eqI rstrip_replicate)

lemma
  assumes "\<exists>i<length zs. zs ! i \<noteq> z"
  shows rstrip_ex_length: "length (rstrip z zs) > 0"
    and rstrip_ex_last: "last (rstrip z zs) \<noteq> z"
proof -
  let ?P = "\<lambda>i. i \<le> length zs \<and> set (drop i zs) \<subseteq> {z}"
  obtain i where i: "i < length zs" "zs ! i \<noteq> z"
    using assms by auto
  then have "\<not> set (drop i zs) \<subseteq> {z}"
    by (metis Cons_nth_drop_Suc drop_eq_Nil2 leD list.set(2) set_empty singleton_insert_inj_eq' subset_singletonD)
  then have "\<not> set (drop 0 zs) \<subseteq> {z}"
    by (metis drop.simps(1) drop_0 set_drop_subset set_empty subset_singletonD)
  then show len: "length (rstrip z zs) > 0"
    using length_rstrip by (metis (no_types, lifting) LeastI bot.extremum drop_all dual_order.refl gr0I list.set(1))
  let ?j = "length (rstrip z zs) - 1"
  have 3: "?j < length (rstrip z zs)"
    using len by simp
  then have 4: "?j < Least ?P"
    using length_rstrip by simp
  have 5: "?P (length (rstrip z zs))"
    using LeastI_ex[of "?P"] length_rstrip by fastforce
  show "last (rstrip z zs) \<noteq> z"
  proof (rule ccontr)
    assume "\<not> last (rstrip z zs) \<noteq> z"
    then have "last (rstrip z zs) = z"
      by simp
    then have "rstrip z zs ! ?j = z"
      using len by (simp add: last_conv_nth)
    then have 2: "zs ! ?j = z"
      using len length_rstrip rstrip_def by auto
    have "?P ?j"
    proof -
      have "?j \<le> length zs"
        using 3 length_rstrip_le by (meson le_eq_less_or_eq order_less_le_trans)
      moreover have "set (drop ?j zs) \<subseteq> {z}"
        using 5 3 2
        by (metis Cons_nth_drop_Suc One_nat_def Suc_pred insert_subset len list.simps(15) order_less_le_trans set_eq_subset)
      ultimately show ?thesis
        by simp
    qed
    then show False
      using 4 Least_le[of "?P"] by fastforce
  qed
qed

text \<open>
A Turing machine stripping the non-blank, non-start symbol $z$ from a proper
symbol sequence works in the obvious way.  First it moves to the end of the
symbol sequence, that is, to the first blank. Then it moves left to the first
non-$z$ symbol thereby overwriting every symbol with a blank. Finally it
performs a ``carriage return''.
\<close>

definition tm_rstrip :: "symbol \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_rstrip z j \<equiv>
     tm_right_until j {\<box>} ;;
     tm_left j ;;
     tm_lconst_until j j (UNIV - {z}) \<box> ;;
     tm_cr j"

lemma tm_rstrip_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_rstrip z j)"
  using assms tm_right_until_tm tm_left_tm tm_lconst_until_tm tm_cr_tm tm_rstrip_def
  by simp

locale turing_machine_rstrip =
  fixes z :: symbol and j :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_left j"
definition "tm3 \<equiv> tm2 ;; tm_lconst_until j j (UNIV - {z}) \<box>"
definition "tm4 \<equiv> tm3 ;; tm_cr j"

lemma tm4_eq_tm_rstrip: "tm4 = tm_rstrip z j"
  unfolding tm4_def tm3_def tm2_def tm1_def tm_rstrip_def by simp

context
  fixes tps0 :: "tape list" and zs :: "symbol list" and k :: nat
  assumes z: "z > 1"
  assumes zs: "proper_symbols zs"
  assumes jk: "0 < j" "j < k" "length tps0 = k"
  assumes tps0: "tps0 ! j = (\<lfloor>zs\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j := (\<lfloor>zs\<rfloor>, Suc (length zs))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (length zs)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def jk time: assms)
  have *: "tps0 ! j = (\<lfloor>zs\<rfloor>, 1)"
    using tps0 jk by simp
  show "rneigh (tps0 ! j) {\<box>} (length zs)"
    using * zs by (intro rneighI) auto
qed

definition "tps2 \<equiv> tps0
  [j := (\<lfloor>zs\<rfloor>, length zs)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = length zs + 2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
  by (tform tps: tps1_def tps2_def jk time: assms)

definition "tps3 \<equiv> tps0
  [j := (\<lfloor>rstrip z zs\<rfloor>, length (rstrip z zs))]"

lemma tm3 [transforms_intros]:
  assumes "ttt = length zs + 2 + Suc (length zs - length (rstrip z zs))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def tps3_def jk time: assms jk tps2_def)
  let ?n = "length zs - length (rstrip z zs)"
  have *: "tps2 ! j = (\<lfloor>zs\<rfloor>, length zs)"
    using tps2_def jk by simp
  show "lneigh (tps2 ! j) (UNIV - {z}) ?n"
  proof (cases "\<exists>i<length zs. zs ! i \<noteq> z")
    case True
    then have 1: "length (rstrip z zs) > 0"
      using rstrip_ex_length by simp
    show ?thesis
    proof (rule lneighI)
      show "(tps2 ::: j) (tps2 :#: j - ?n) \<in> UNIV - {z}"
        using * 1 contents_inbounds True length_rstrip length_rstrip_le rstrip_def rstrip_ex_last
        by (smt (verit, best) DiffI One_nat_def UNIV_I diff_diff_cancel diff_less fst_conv last_conv_nth
          le_eq_less_or_eq length_greater_0_conv less_Suc_eq_le nth_take singletonD snd_conv)
      have "\<And>n'. n' < ?n \<Longrightarrow> (tps2 ::: j) (tps2 :#: j - n') = z"
        using * rstrip_stripped by simp
      then show "\<And>n'. n' < ?n \<Longrightarrow> (tps2 ::: j) (tps2 :#: j - n') \<notin> UNIV - {z}"
        by simp
    qed
  next
    case False
    then have 1: "rstrip z zs = []"
      using rstrip_not_ex by simp
    show ?thesis
    proof (rule lneighI)
      show "(tps2 ::: j) (tps2 :#: j - ?n) \<in> UNIV - {z}"
        using * 1 z by simp
      show "\<And>n'. n' < ?n \<Longrightarrow> (tps2 ::: j) (tps2 :#: j - n') \<notin> UNIV - {z}"
        using * rstrip_stripped by simp
    qed
  qed

  have "lconstplant (\<lfloor>zs\<rfloor>, length zs) \<box> ?n = (\<lfloor>rstrip z zs\<rfloor>, length (rstrip z zs))"
    (is "?lhs = _")
  proof -
    have "?lhs = (\<lambda>i. if length zs - ?n < i \<and> i \<le> length zs then \<box> else \<lfloor>zs\<rfloor> i, length zs - ?n)"
      using lconstplant[of "(\<lfloor>zs\<rfloor>, length zs)" 0 "?n"] by auto
    moreover have "(\<lambda>i. if length zs - ?n < i \<and> i \<le> length zs then \<box> else \<lfloor>zs\<rfloor> i) = \<lfloor>rstrip z zs\<rfloor>"
    proof
      fix i
      consider "length zs - ?n < i \<and> i \<le> length zs" | "i > length zs" | "i \<le> length (rstrip z zs)"
        by linarith
      then show "(if length zs - ?n < i \<and> i \<le> length zs then \<box> else \<lfloor>zs\<rfloor> i) = \<lfloor>rstrip z zs\<rfloor> i"
      proof (cases)
        case 1
        then show ?thesis
          by auto
      next
        case 2
        then show ?thesis
          by (metis contents_outofbounds diff_diff_cancel length_rstrip_le less_imp_diff_less)
      next
        case 3
        then show ?thesis
          using contents_def length_rstrip length_rstrip_le rstrip_def by auto
      qed
    qed
    moreover have "length zs - ?n = length (rstrip z zs)"
      using diff_diff_cancel length_rstrip_le by simp
    ultimately show ?thesis
      by simp
  qed
  then have "lconstplant (tps2 ! j) \<box> ?n = (\<lfloor>rstrip z zs\<rfloor>, length (rstrip z zs))"
    using tps2_def jk by simp
  then show "tps3 = tps2
    [j := tps2 ! j |-| ?n,
     j := lconstplant (tps2 ! j) \<box> ?n]"
    unfolding tps3_def tps2_def by simp
qed

definition "tps4 \<equiv> tps0
  [j := (\<lfloor>rstrip z zs\<rfloor>, 1)]"

lemma tm4:
  assumes "ttt = length zs + 2 + Suc (length zs - length (rstrip z zs)) + length (rstrip z zs) + 2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def tps4_def jk time: assms tps3_def jk)
  show "clean_tape (tps3 ! j)"
    using tps3_def jk zs rstrip_def by simp
qed

lemma tm4':
  assumes "ttt = 3 * length zs + 5"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  let ?ttt = "length zs + 2 + Suc (length zs - length (rstrip z zs)) + length (rstrip z zs) + 2"
  have "?ttt = length zs + 5 + (length zs - length (rstrip z zs)) + length (rstrip z zs)"
    by simp
  also have "... \<le> length zs + 5 + length zs + length (rstrip z zs)"
    by simp
  also have "... \<le> length zs + 5 + length zs + length zs"
    using length_rstrip_le by simp
  also have "... = 3 * length zs + 5"
    by simp
  finally have "?ttt \<le> 3 * length zs + 5" .
  then show ?thesis
    using assms transforms_monotone tm4 by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_rstripI [transforms_intros]:
  fixes z :: symbol and j :: tapeidx
  fixes tps tps' :: "tape list" and zs :: "symbol list" and k :: nat
  assumes "z > 1" and "0 < j" "j < k"
    and "proper_symbols zs"
    and "length tps = k"
  assumes "tps ! j = (\<lfloor>zs\<rfloor>, 1)"
  assumes "ttt = 3 * length zs + 5"
  assumes "tps' = tps[j := (\<lfloor>rstrip z zs\<rfloor>, 1)]"
  shows "transforms (tm_rstrip z j) tps ttt tps'"
proof -
  interpret loc: turing_machine_rstrip z j .
  show ?thesis
    using assms loc.tm4' loc.tps4_def loc.tm4_eq_tm_rstrip by simp
qed


subsection \<open>Writing arbitrary length sequences of the same symbol\<close>

text \<open>
The next Turing machine accepts a number $n$ on tape $j_1$ and writes the symbol
sequence $z^n$ to tape $j_2$. The symbol $z$ is a parameter of the TM. The TM
decrements the number on tape $j_1$ until it reaches zero.
\<close>

definition tm_write_replicate :: "symbol \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_write_replicate z j1 j2 \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      tm_char j2 z ;;
      tm_decr j1
    DONE ;;
    tm_cr j2"

lemma tm_write_replicate_tm:
  assumes "0 < j1" and "0 < j2" and "j1 < k" and "j2 < k" and "j1 \<noteq> j2" and "G \<ge> 4" and "z < G"
  shows "turing_machine k G (tm_write_replicate z j1 j2)"
  unfolding tm_write_replicate_def
  using turing_machine_loop_turing_machine Nil_tm tm_char_tm tm_decr_tm tm_cr_tm assms
  by simp

locale turing_machine_write_replicate =
  fixes j1 j2 :: tapeidx and z :: symbol
begin

definition "tm1 \<equiv> tm_char j2 z"
definition "tm2 \<equiv> tm1 ;; tm_decr j1"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tm2 DONE"
definition "tm3 \<equiv> tmL ;; tm_cr j2"

lemma tm3_eq_tm_write_replicate: "tm3 = tm_write_replicate z j1 j2"
  using tm3_def tm2_def tm1_def tm_write_replicate_def tmL_def by simp

context
  fixes tps0 :: "tape list" and k n :: nat
  assumes jk: "length tps0 = k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "j1 < k" "j2 < k"
    and z: "1 < z"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j1 := (\<lfloor>n - t\<rfloor>\<^sub>N, 1),
     j2 := (\<lfloor>replicate t z\<rfloor>, Suc t)]"

lemma tpsL0: "tpsL 0 = tps0"
  using tpsL_def tps0 jk by (metis One_nat_def diff_zero list_update_id replicate_empty)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j1 := (\<lfloor>n - t\<rfloor>\<^sub>N, 1),
     j2 := (\<lfloor>replicate (Suc t) z\<rfloor>, Suc (Suc t))]"

lemma tmL1 [transforms_intros]: "transforms tm1 (tpsL t) 1 (tpsL1 t)"
  unfolding tm1_def
proof (tform tps: tpsL_def tpsL1_def tps0 jk)
  have "tpsL t :#: j2 = Suc t"
    using tpsL1_def jk by (metis length_list_update nth_list_update_eq snd_conv tpsL_def)
  moreover have "tpsL t ::: j2 = \<lfloor>replicate t z\<rfloor>"
    using tpsL1_def jk by (metis fst_conv length_list_update nth_list_update_eq tpsL_def)
  moreover have "\<lfloor>replicate t z\<rfloor>(Suc t := z) = \<lfloor>replicate (Suc t) z\<rfloor>"
    using contents_snoc by (metis length_replicate replicate_Suc replicate_append_same)
  ultimately show "tpsL1 t = (tpsL t)[j2 := tpsL t ! j2 |:=| z |+| 1]"
    unfolding tpsL1_def tpsL_def by simp
qed

lemma tmL2:
  assumes "ttt = 9 + 2 * nlength (n - t)"
  shows "transforms tm2 (tpsL t) ttt (tpsL (Suc t))"
  unfolding tm2_def
proof (tform tps: assms tpsL_def tpsL1_def tps0 jk)
  show "tpsL (Suc t) = (tpsL1 t)[j1 := (\<lfloor>n - t - 1\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL_def tpsL1_def using jk by (simp add: list_update_swap)
qed

lemma tmL2' [transforms_intros]:
  assumes "ttt = 9 + 2 * nlength n"
  shows "transforms tm2 (tpsL t) ttt (tpsL (Suc t))"
proof -
  have "9 + 2 * nlength (n - t) \<le> 9 + 2 * nlength n"
    using nlength_mono[of "n - t" n] by simp
  then show ?thesis
    using assms tmL2 transforms_monotone by blast
qed

lemma tmL [transforms_intros]:
  assumes "ttt = n * (11 + 2 * nlength n) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL n)"
  unfolding tmL_def
proof (tform)
  let ?t = "9 + 2 * nlength n"
  show "\<And>i. i < n \<Longrightarrow> read (tpsL i) ! j1 \<noteq> \<box>"
    using jk tpsL_def read_ncontents_eq_0 by simp
  show "\<not> read (tpsL n) ! j1 \<noteq> \<box>"
    using jk tpsL_def read_ncontents_eq_0 by simp
  show "n * (9 + 2 * nlength n + 2) + 1 \<le> ttt"
    using assms by simp
qed

definition tps3 :: "tape list" where
  "tps3 \<equiv> tps0
    [j1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j2 := (\<lfloor>replicate n z\<rfloor>, 1)]"

lemma tm3:
  assumes "ttt = n * (12 + 2 * nlength n) + 4"
  shows "transforms tm3 (tpsL 0) ttt tps3"
  unfolding tm3_def
proof (tform tps: z tpsL_def tps3_def tps0 jk)
  have "ttt = Suc (n * (11 + 2 * nlength n)) + Suc (Suc (Suc n))"
  proof -
    have "Suc (n * (11 + 2 * nlength n)) + Suc (Suc (Suc n)) = n * (11 + 2 * nlength n) + 4 + n"
      by simp
    also have "... = n * (12 + 2 * nlength n) + 4"
      by algebra
    finally have "Suc (n * (11 + 2 * nlength n)) + Suc (Suc (Suc n)) = ttt"
      using assms by simp
    then show ?thesis
      by simp
  qed
  then show "ttt = n * (11 + 2 * nlength n) + 1 + (tpsL n :#: j2 + 2)"
    using tpsL_def jk by simp
qed

lemma tm3':
  assumes "ttt = n * (12 + 2 * nlength n) + 4"
  shows "transforms tm3 tps0 ttt tps3"
  using tm3 tpsL0 assms by simp

end

end

lemma transforms_tm_write_replicateI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k n :: nat
  assumes "length tps = k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "j1 < k" "j2 < k" and "1 < z"
  assumes
    "tps ! j1 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = n * (12 + 2 * nlength n) + 4"
  assumes "tps' = tps
    [j1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j2 := (\<lfloor>replicate n z\<rfloor>, 1)]"
  shows "transforms (tm_write_replicate z j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_write_replicate j1 j2 .
  show ?thesis
    using assms loc.tm3' loc.tps3_def loc.tm3_eq_tm_write_replicate by simp
qed


subsection \<open>Extracting the elements of a pair\<close>

text \<open>
In Section~\ref{s:tm-basic-pair} we defined a pairing function for strings. For
example, $\langle \bbbI\bbbI, \bbbO\bbbO\rangle$ is first mapped to
$\bbbI\bbbI\#\bbbO\bbbO$ and ultimately represented as
$\bbbO\bbbI\bbbO\bbbI\bbbI\bbbI\bbbO\bbbO\bbbO\bbbO$. A Turing machine that is
to compute a function for the argument $\langle \bbbI\bbbI, \bbbO\bbbO\rangle$
would receive as input the symbols \textbf{0101110000}. Typically the TM would
then extract the two components \textbf{11} and \textbf{00}. In this section we
devise TMs to do just that.

As it happens, applying the quaternary alphabet decoding function @{const
bindecode} (see Section~\ref{s:tm-quaternary}) to such a symbol sequence gets us
halfway to extracting the elements of the pair. For example, decoding
\textbf{0101110000} yields @{text "\<one>\<one>\<sharp>\<zero>\<zero>"}, and now the TM only has to
locate the @{text \<sharp>}.

A Turing machine cannot rely on being given a well-formed pair. After decoding,
the symbol sequence might have more or fewer than one @{text \<sharp>} symbol or even
@{text "\<bar>"} symbols. The following functions @{term first} and @{term second}
are designed to extract the first and second element of a symbol sequence
representing a pair, and for other symbol sequences at least allow for an
efficient implementation. Implementations will come further down in this
section.
\<close>

definition first :: "symbol list \<Rightarrow> symbol list" where
  "first ys \<equiv> take (if \<exists>i<length ys. ys ! i \<in> {\<bar>, \<sharp>} then LEAST i. i < length ys \<and> ys ! i \<in> {\<bar>, \<sharp>} else length ys) ys"

definition second :: "symbol list \<Rightarrow> symbol list" where
  "second zs \<equiv> drop (Suc (length (first zs))) zs"

lemma firstD:
  assumes "\<exists>i<length ys. ys ! i \<in> {\<bar>, \<sharp>}" and "m = (LEAST i. i < length ys \<and> ys ! i \<in> {\<bar>, \<sharp>})"
  shows "m < length ys" and "ys ! m \<in> {\<bar>, \<sharp>}" and "\<forall>i<m. ys ! i \<notin> {\<bar>, \<sharp>}"
  using LeastI_ex[OF assms(1)] assms(2) by simp_all (use less_trans not_less_Least in blast)

lemma firstI:
  assumes "m < length ys" and "ys ! m \<in> {\<bar>, \<sharp>}" and "\<forall>i<m. ys ! i \<notin> {\<bar>, \<sharp>}"
  shows "(LEAST i. i < length ys \<and> ys ! i \<in> {\<bar>, \<sharp>}) = m"
  using assms by (metis (mono_tags, lifting) LeastI less_linear not_less_Least)

lemma length_first_ex:
  assumes "\<exists>i<length ys. ys ! i \<in> {\<bar>, \<sharp>}" and "m = (LEAST i. i < length ys \<and> ys ! i \<in> {\<bar>, \<sharp>})"
  shows "length (first ys) = m"
proof -
  have "m < length ys"
    using assms firstD(1) by presburger
  moreover have "first ys = take m ys"
    using assms first_def by simp
  ultimately show ?thesis
    by simp
qed

lemma first_notex:
  assumes "\<not> (\<exists>i<length ys. ys ! i \<in> {\<bar>, \<sharp>})"
  shows "first ys = ys"
  using assms first_def by auto

lemma length_first: "length (first ys) \<le> length ys"
  using length_first_ex first_notex first_def by simp

lemma length_second_first: "length (second zs) = length zs - Suc (length (first zs))"
  using second_def by simp

lemma length_second: "length (second zs) \<le> length zs"
  using second_def by simp

text \<open>
Our next goal is to show that @{const first} and @{const second} really extract
the first and second element of a pair.
\<close>

lemma bindecode_bitenc:
  fixes x :: string
  shows "bindecode (string_to_symbols (bitenc x)) = string_to_symbols x"
proof (induction x)
  case Nil
  then show ?case
    using less_2_cases_iff by force
next
  case (Cons a x)
  have "bitenc (a # x) = bitenc [a] @ bitenc x"
    by simp
  then have "string_to_symbols (bitenc (a # x)) = string_to_symbols (bitenc [a] @ bitenc x)"
    by simp
  then have "string_to_symbols (bitenc (a # x)) = string_to_symbols (bitenc [a]) @ string_to_symbols (bitenc x)"
    by simp
  then have "bindecode (string_to_symbols (bitenc (a # x))) =
      bindecode (string_to_symbols (bitenc [a]) @ string_to_symbols (bitenc x))"
    by simp
  also have "... = bindecode (string_to_symbols (bitenc [a])) @ bindecode (string_to_symbols (bitenc x))"
    using bindecode_append length_bitenc by (metis (no_types, lifting) dvd_triv_left length_map)
  also have "... = bindecode (string_to_symbols (bitenc [a])) @ string_to_symbols x"
    using Cons by simp
  also have "... = string_to_symbols [a] @ string_to_symbols x"
    using bindecode_def by simp
  also have "... = string_to_symbols ([a] @ x)"
    by simp
  also have "... = string_to_symbols (a # x)"
    by simp
  finally show ?case .
qed

lemma bindecode_string_pair:
  fixes x u :: string
  shows "bindecode \<langle>x; u\<rangle> = string_to_symbols x @ [\<sharp>] @ string_to_symbols u"
proof -
  have "bindecode \<langle>x; u\<rangle> = bindecode (string_to_symbols (bitenc x @ [True, True] @ bitenc u))"
    using string_pair_def by simp
  also have "... = bindecode
     (string_to_symbols (bitenc x) @
      string_to_symbols [\<bbbI>, \<bbbI>] @
      string_to_symbols (bitenc u))"
    by simp
  also have "... = bindecode (string_to_symbols (bitenc x)) @
      bindecode (string_to_symbols [\<bbbI>, \<bbbI>]) @
      bindecode (string_to_symbols (bitenc u))"
  proof -
    have "even (length (string_to_symbols [True, True]))"
      by simp
    moreover have "even (length (string_to_symbols (bitenc y)))" for y
      by (simp add: length_bitenc)
    ultimately show ?thesis
      using bindecode_append length_bindecode length_bitenc
      by (smt (z3) add_mult_distrib2 add_self_div_2 dvd_triv_left length_append length_map mult_2)
  qed
  also have "... = string_to_symbols x @ bindecode (string_to_symbols [\<bbbI>, \<bbbI>]) @ string_to_symbols u"
    using bindecode_bitenc by simp
  also have "... = string_to_symbols x @ [\<sharp>] @ string_to_symbols u"
    using bindecode_def by simp
  finally show ?thesis .
qed

lemma first_pair:
  fixes ys :: "symbol list" and x u :: string
  assumes "ys = bindecode \<langle>x; u\<rangle>"
  shows "first ys = string_to_symbols x"
proof -
  have ys: "ys = string_to_symbols x @ [\<sharp>] @ string_to_symbols u"
    using bindecode_string_pair assms by simp
  have bs: "bit_symbols (string_to_symbols x)"
    by simp
  have "ys ! (length (string_to_symbols x)) = \<sharp>"
    using ys by (metis append_Cons nth_append_length)
  then have ex: "ys ! (length (string_to_symbols x)) \<in> {\<bar>, \<sharp>}"
    by simp
  have "(LEAST i. i < length ys \<and> ys ! i \<in> {\<bar>, \<sharp>}) = length (string_to_symbols x)"
    using ex ys bs by (intro firstI) (simp_all add: nth_append)
  moreover have "length (string_to_symbols x) < length ys"
    using ys by simp
  ultimately have "first ys = take (length (string_to_symbols x)) ys"
    using ex first_def by auto
  then show "first ys = string_to_symbols x"
    using ys by simp
qed

lemma second_pair:
  fixes ys :: "symbol list" and x u :: string
  assumes "ys = bindecode \<langle>x; u\<rangle>"
  shows "second ys = string_to_symbols u"
proof -
  have ys: "ys = string_to_symbols x @ [\<sharp>] @ string_to_symbols u"
    using bindecode_string_pair assms by simp
  let ?m = "length (string_to_symbols x)"
  have "length (first ys) = ?m"
    using assms first_pair by presburger
  moreover have "drop (Suc ?m) ys = string_to_symbols u"
    using ys by simp
  ultimately have "drop (Suc (length (first ys))) ys = string_to_symbols u"
    by simp
  then show ?thesis
    using second_def by simp
qed


subsubsection \<open>A Turing machine for extracting the first element\<close>

text \<open>
Unlike most other Turing machines, the one in this section is not meant to be
reusable, but rather to compute a function, namely the function @{const first}.
For this reason there are no tape index parameters. Instead, the encoded pair is
expected on the input tape, and the output is written to the output tape.

\null
\<close>

lemma bit_symbols_first:
  assumes "ys = bindecode (string_to_symbols x)"
  shows "bit_symbols (first ys)"
proof (cases "\<exists>i<length ys. ys ! i \<in> {\<bar>, \<sharp>}")
  case True
  define m where "m = (LEAST i. i < length ys \<and> ys ! i \<in> {\<bar>, \<sharp>})"
  then have m: "m < length ys" "ys ! m \<in> {\<bar>, \<sharp>}" "\<forall>i<m. ys ! i \<notin> {\<bar>, \<sharp>}"
    using firstD[OF True] by blast+
  have len: "length (first ys) = m"
    using length_first_ex[OF True] m_def by simp
  have "bit_symbols (string_to_symbols x)"
    by simp
  then have "\<forall>i<length ys. ys ! i \<in> {2..<6}"
    using assms bindecode2345 by simp
  then have "\<forall>i<m. ys ! i \<in> {2..<6}"
    using m(1) by simp
  then have "\<forall>i<m. ys ! i \<in> {2..<4}"
    using m(3) by fastforce
  then show ?thesis
    using first_def len by auto
next
  case False
  then have 1: "\<forall>i<length ys. ys ! i \<notin> {\<bar>, \<sharp>}"
    by simp
  have "bit_symbols (string_to_symbols x)"
    by simp
  then have "\<forall>i<length ys. ys ! i \<in> {2..<6}"
    using assms bindecode2345 by simp
  then have "\<forall>i<length ys. ys ! i \<in> {2..<4}"
    using 1 by fastforce
  then show ?thesis
    using False first_notex by auto
qed

definition tm_first :: machine where
  "tm_first \<equiv>
    tm_right_many {0, 1, 2} ;;
    tm_bindecode 0 2 ;;
    tm_cp_until 2 1 {\<box>, \<bar>, \<sharp>}"

lemma tm_first_tm: "G \<ge> 6 \<Longrightarrow> k \<ge> 3 \<Longrightarrow> turing_machine k G tm_first"
  unfolding tm_first_def
  using tm_cp_until_tm tm_start_tm tm_bindecode_tm tm_right_many_tm
  by simp

locale turing_machine_fst_pair =
  fixes k :: nat
  assumes k: "k \<ge> 3"
begin

definition "tm1 \<equiv> tm_right_many {0, 1, 2}"
definition "tm2 \<equiv> tm1 ;; tm_bindecode 0 2"
definition "tm3 \<equiv> tm2 ;; tm_cp_until 2 1 {\<box>, \<bar>, \<sharp>}"

lemma tm3_eq_tm_first: "tm3 = tm_first"
  using tm1_def tm2_def tm3_def tm_first_def by simp

context
  fixes xs :: "symbol list"
  assumes bs: "bit_symbols xs"
begin

definition "tps0 \<equiv> snd (start_config k xs)"

lemma lentps [simp]: "length tps0 = k"
  using tps0_def start_config_length k by simp

lemma tps0_0: "tps0 ! 0 = (\<lfloor>xs\<rfloor>, 0)"
  using tps0_def start_config_def contents_def by auto

lemma tps0_gt_0: "j > 0 \<Longrightarrow> j < k \<Longrightarrow> tps0 ! j = (\<lfloor>[]\<rfloor>, 0)"
  using tps0_def start_config_def contents_def by auto

definition "tps1 \<equiv> tps0
  [0 := (\<lfloor>xs\<rfloor>, 1),
   1 := (\<lfloor>[]\<rfloor>, 1),
   2 := (\<lfloor>[]\<rfloor>, 1)]"

lemma tm1 [transforms_intros]: "transforms tm1 tps0 1 tps1"
  unfolding tm1_def
proof (tform)
  show "tps1 = map (\<lambda>j. if j \<in> {0, 1, 2} then tps0 ! j |+| 1 else tps0 ! j) [0..<length tps0]"
    (is "_ = ?rhs")
  proof (rule nth_equalityI)
    show "length tps1 = length ?rhs"
      using tps0_def tps1_def by simp
    show "tps1 ! j = ?rhs ! j" if "j < length tps1" for j
      using that tps0_0 tps0_gt_0 tps1_def by simp
  qed
qed

definition "tps2 \<equiv> tps0
  [0 := (\<lfloor>xs\<rfloor>, 1),
   1 := (\<lfloor>[]\<rfloor>, 1),
   2 := (\<lfloor>bindecode xs\<rfloor>, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 8 + 3 * length xs"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: bs k tps1_def assms tps2_def)

definition "tps3 \<equiv> tps0
  [0 := (\<lfloor>xs\<rfloor>, 1),
   1 := (\<lfloor>first (bindecode xs)\<rfloor>, Suc (length (first (bindecode xs)))),
   2 := (\<lfloor>bindecode xs\<rfloor>, Suc (length (first (bindecode xs))))]"

lemma tm3:
  assumes "ttt = 8 + 3 * length xs + Suc (length (first (bindecode xs)))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: k tps2_def time: assms)
  let ?ys = "bindecode xs"
  have tps2: "tps2 ! 2 = (\<lfloor>?ys\<rfloor>, 1)"
    using tps2_def k by simp
  show "rneigh (tps2 ! 2) {\<box>, \<bar>, \<sharp>} (length (first ?ys))"
  proof (cases "\<exists>i<length ?ys. ?ys ! i \<in> {\<bar>, \<sharp>}")
    case ex5: True
    define m where "m = (LEAST i. i < length ?ys \<and> ?ys ! i \<in> {\<bar>, \<sharp>})"
    then have m: "m = length (first ?ys)"
      using length_first_ex ex5 by simp
    show ?thesis
    proof (rule rneighI)
      have "?ys ! m \<in> {\<bar>, \<sharp>}"
        using firstD m_def ex5 by blast
      then show "(tps2 ::: 2) (tps2 :#: 2 + length (first ?ys)) \<in> {\<box>, \<bar>, \<sharp>}"
        using m tps2 contents_def by simp
      show "(tps2 ::: 2) (tps2 :#: 2 + i) \<notin> {\<box>, \<bar>, \<sharp>}" if "i < length (first ?ys)" for i
      proof -
        have "m < length ?ys"
          using ex5 firstD(1) length_first_ex m by blast
        then have "length (first ?ys) < length ?ys"
          using m by simp
        then have "i < length ?ys"
          using that by simp
        then have "?ys ! i \<noteq> 0"
          using proper_bindecode by fastforce
        moreover have "?ys ! i \<notin> {\<bar>, \<sharp>}"
          using ex5 firstD(3) length_first_ex that by blast
        ultimately show ?thesis
          using Suc_neq_Zero \<open>i < length (bindecode xs)\<close> tps2 by simp
      qed
    qed
  next
    case notex5: False
    then have ys: "?ys = first ?ys"
      using first_notex by simp
    show ?thesis
    proof (rule rneighI)
      show "(tps2 ::: 2) (tps2 :#: 2 + length (first ?ys)) \<in> {\<box>, \<bar>, \<sharp>}"
        using ys tps2 by simp
      show "(tps2 ::: 2) (tps2 :#: 2 + i) \<notin> {\<box>, \<bar>, \<sharp>}" if "i < length (first ?ys)" for i
        using notex5 that ys proper_bindecode contents_inbounds
        by (metis Suc_leI add_gr_0 diff_Suc_1 fst_conv gr_implies_not0 insert_iff
          plus_1_eq_Suc snd_conv tps2 zero_less_one)
    qed
  qed
  show "tps3 = tps2[2 := tps2 ! 2 |+| length (first ?ys), 1 := implant (tps2 ! 2) (tps2 ! 1) (length (first ?ys))]"
    (is "_ = ?tps")
  proof -
    have 0: "tps3 ! 0 = ?tps ! 0"
      using tps2_def tps3_def by simp
    have 1: "tps3 ! 2 = ?tps ! 2"
      using tps2_def tps3_def k by simp
    have lentps2: "length tps2 > 2"
      using k tps2_def by simp
    have "implant (tps2 ! 2) (tps2 ! 1) (length (first ?ys)) =
      (\<lfloor>first ?ys\<rfloor>, Suc (length (first ?ys)))"
    proof -
      have len: "length (first ?ys) \<le> length ?ys"
        using first_def by simp
      have "tps2 ! 1 = (\<lfloor>[]\<rfloor>, 1)"
        using tps2_def lentps2 by simp
      then have "implant (tps2 ! 2) (tps2 ! 1) (length (first ?ys)) =
          implant (\<lfloor>?ys\<rfloor>, 1) (\<lfloor>[]\<rfloor>, 1) (length (first ?ys))"
        using tps2 by simp
      also have "... = (\<lfloor>take (length (first ?ys)) ?ys\<rfloor>, Suc (length (first ?ys)))"
        using implant_contents[of 1 "length (first ?ys)" ?ys "[]"] len by simp
      also have "... = (\<lfloor>first ?ys\<rfloor>, Suc (length (first ?ys)))"
        using first_def using first_notex length_first_ex by presburger
      finally show ?thesis .
    qed
    moreover have "length tps2 > 2"
      using k tps2_def by simp
    ultimately show ?thesis
      using 0 1 tps2_def tps3_def tps0_def lentps k tps2
      by (smt (z3) length_list_update list_update_overwrite list_update_swap nth_list_update)
  qed
qed

lemma tm3':
  assumes "ttt = 9 + 4 * length xs"
  shows "transforms tm3 tps0 ttt tps3"
proof -
  let ?t = "8 + 3 * length xs + Suc (length (first (bindecode xs)))"
  have "?t \<le> 8 + 3 * length xs + Suc (length (bindecode xs))"
    using length_first by (meson Suc_le_mono add_le_mono order_refl)
  also have "... \<le> 8 + 3 * length xs + Suc (length xs)"
    using length_bindecode by simp
  also have "... = 9 + 3 * length xs + length xs"
    by simp
  also have "... = 9 + 4 * length xs"
    by simp
  finally have "?t \<le> ttt"
    using assms(1) by simp
  moreover have "transforms tm3 tps0 ?t tps3"
    using tm3 by simp
  ultimately show ?thesis
    using transforms_monotone by simp
qed

end  (* context tps *)

lemma tm3_computes:
  "computes_in_time k tm3 (\<lambda>x. symbols_to_string (first (bindecode (string_to_symbols x)))) (\<lambda>n. 9 + 4 * n)"
proof -
  define f where "f = (\<lambda>x. symbols_to_string (first (bindecode (string_to_symbols x))))"
  define T :: "nat \<Rightarrow> nat" where "T = (\<lambda>n. 9 + 4 * n)"
  have "computes_in_time k tm3 f T"
  proof
    fix x :: string
    let ?xs = "string_to_symbols x"
    have bs: "bit_symbols ?xs"
      by simp
    define tps where "tps = tps3 ?xs"
    have trans: "transforms tm3 (tps0 ?xs) (9 + 4 * length ?xs) tps"
      using bs tm3' tps_def by blast
    have "tps3 ?xs ::: 1 = \<lfloor>first (bindecode ?xs)\<rfloor>"
      using bs tps3_def k by simp
    moreover have "bit_symbols (first (bindecode ?xs))"
      using bit_symbols_first by simp
    ultimately have "tps3 ?xs ::: 1 = string_to_contents (symbols_to_string (first (bindecode ?xs)))"
      using bit_symbols_to_symbols contents_string_to_contents by simp
    then have *: "tps ::: 1 = string_to_contents (f x)"
      using tps_def f_def by auto
    then have "transforms tm3 (snd (start_config k (string_to_symbols x))) (T (length x)) tps"
      using trans T_def tps0_def by simp
    then show "\<exists>tps. tps ::: 1 = string_to_contents (f x) \<and>
        transforms tm3 (snd (start_config k (string_to_symbols x))) (T (length x)) tps"
      using * by auto
  qed
  then show ?thesis
    using f_def T_def by simp
qed

end  (* locale turing_machine_fst_pair *)

lemma tm_first_computes:
  assumes "k \<ge> 3"
  shows "computes_in_time
    k
    tm_first
    (\<lambda>x. symbols_to_string (first (bindecode (string_to_symbols x))))
    (\<lambda>n. 9 + 4 * n)"
proof -
  interpret loc: turing_machine_fst_pair k
    using turing_machine_fst_pair.intro assms by simp
  show ?thesis
    using loc.tm3_eq_tm_first loc.tm3_computes by simp
qed


subsubsection \<open>A Turing machine for splitting pairs\<close>

text \<open>
The next Turing machine expects a proper symbol sequence @{term zs} on tape
$j_1$ and outputs @{term "first zs"} and @{term "second zs"} on tapes $j_2$ and
$j_3$, respectively.
\<close>

definition tm_unpair :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_unpair j1 j2 j3 \<equiv>
    tm_cp_until j1 j2 {\<box>, \<bar>, \<sharp>} ;;
    tm_right j1 ;;
    tm_cp_until j1 j3 {\<box>} ;;
    tm_cr j1 ;;
    tm_cr j2 ;;
    tm_cr j3"

lemma tm_unpair_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j2" and "0 < j3" and "j1 < k" "j2 < k" "j3 < k"
  shows "turing_machine k G (tm_unpair j1 j2 j3)"
  using tm_cp_until_tm tm_right_tm tm_cr_tm assms tm_unpair_def by simp

locale turing_machine_unpair =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_cp_until j1 j2 {\<box>, \<bar>, \<sharp>}"
definition "tm2 \<equiv> tm1 ;; tm_right j1"
definition "tm3 \<equiv> tm2 ;; tm_cp_until j1 j3 {\<box>}"
definition "tm4 \<equiv> tm3 ;; tm_cr j1"
definition "tm5 \<equiv> tm4 ;; tm_cr j2"
definition "tm6 \<equiv> tm5 ;; tm_cr j3"

lemma tm6_eq_tm_unpair: "tm6 = tm_unpair j1 j2 j3"
  unfolding tm6_def tm5_def tm4_def tm3_def tm2_def tm1_def tm_unpair_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and zs :: "symbol list"
  assumes jk: "0 < j2" "0 < j3" "j1 \<noteq> j2" "j1 \<noteq> j3" "j2 \<noteq> j3" "j1 < k" "j2 < k" "j3 < k" "length tps0 = k"
    and zs: "proper_symbols zs"
    and tps0:
      "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
      "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
      "tps0 ! j3 = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, Suc (length (first zs))),
   j2 := (\<lfloor>first zs\<rfloor>, Suc (length (first zs)))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (length (first zs))"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: assms tps0 tps1_def jk)
  let ?n = "length (first zs)"
  have *: "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    using tps0 jk by simp
  show "rneigh (tps0 ! j1) {\<box>, \<bar>, \<sharp>} (length (first zs))"
  proof (cases "\<exists>i<length zs. zs ! i \<in> {\<bar>, \<sharp>}")
    case ex5: True
    define m where "m = (LEAST i. i < length zs \<and> zs ! i \<in> {\<bar>, \<sharp>})"
    then have m: "m = length (first zs)"
      using length_first_ex ex5 by simp
    show ?thesis
    proof (rule rneighI)
      have "zs ! m \<in> {\<bar>, \<sharp>}"
        using firstD m_def ex5 by blast
      then show "(tps0 ::: j1) (tps0 :#: j1 + length (first zs)) \<in> {\<box>, \<bar>, \<sharp>}"
        using m * contents_def by simp
      show "(tps0 ::: j1) (tps0 :#: j1 + i) \<notin> {\<box>, \<bar>, \<sharp>}" if "i < length (first zs)" for i
      proof -
        have "m < length zs"
          using ex5 firstD(1) length_first_ex m by blast
        then have "length (first zs) < length zs"
          using m by simp
        then have "i < length zs"
          using that by simp
        then have "zs ! i \<noteq> \<box>"
          using zs by fastforce
        moreover have "zs ! i \<notin> {\<bar>, \<sharp>}"
          using ex5 firstD(3) length_first_ex that by blast
        ultimately show ?thesis
          using Suc_neq_Zero `i < length zs` * by simp
      qed
    qed
  next
    case notex5: False
    then have ys: "zs = first zs"
      using first_notex by simp
    show ?thesis
    proof (rule rneighI)
      show "(tps0 ::: j1) (tps0 :#: j1 + length (first zs)) \<in> {\<box>, \<bar>, \<sharp>}"
        using ys * by simp
      show "(tps0 ::: j1) (tps0 :#: j1 + i) \<notin> {\<box>, \<bar>, \<sharp>}" if "i < length (first zs)" for i
        using notex5 that ys proper_bindecode contents_inbounds * zs by auto
    qed
  qed

  have 1: "implant (tps0 ! j1) (tps0 ! j2) ?n = (\<lfloor>first zs\<rfloor>, Suc ?n)"
  proof -
    have "implant (tps0 ! j1) (tps0 ! j2) ?n =
        (\<lfloor>[] @ take (length (first zs)) (drop (1 - 1) zs)\<rfloor>,
         Suc (length []) + length (first zs))"
      using implant_contents[of 1 "length (first zs)" zs "[]"] tps0(1,2)
      by (metis (mono_tags, lifting) add.right_neutral diff_Suc_1 le_eq_less_or_eq
        firstD(1) first_notex length_first_ex less_one list.size(3) plus_1_eq_Suc)
    then have "implant (tps0 ! j1) (tps0 ! j2) ?n = (\<lfloor>take ?n zs\<rfloor>, Suc ?n)"
      by simp
    then show "implant (tps0 ! j1) (tps0 ! j2) ?n = (\<lfloor>first zs\<rfloor>, Suc ?n)"
      using first_def length_first_ex by auto
  qed
  have 2: "tps0 ! j1 |+| ?n = (\<lfloor>zs\<rfloor>, Suc ?n)"
    using tps0 jk by simp
  show "tps1 = tps0
      [j1 := tps0 ! j1 |+| ?n,
       j2 := implant (tps0 ! j1) (tps0 ! j2) ?n]"
    unfolding tps1_def using jk 1 2 by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, length (first zs) + 2),
   j2 := (\<lfloor>first zs\<rfloor>, Suc (length (first zs)))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = length (first zs) + 2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps1_def jk tps2_def time: assms)
  have "tps1 ! j1 |+| 1 = (\<lfloor>zs\<rfloor>, length (first zs) + 2)"
    using tps1_def jk by simp
  then show "tps2 = tps1[j1 := tps1 ! j1 |+| 1]"
    unfolding tps2_def tps1_def using jk by (simp add: list_update_swap)
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, length (first zs) + 2 + (length zs - Suc (length (first zs)))),
   j2 := (\<lfloor>first zs\<rfloor>, Suc (length (first zs))),
   j3 := (\<lfloor>second zs\<rfloor>, Suc (length (second zs)))]"

lemma tm3 [transforms_intros]:
  assumes "ttt = length (first zs) + 2 + Suc (length zs - Suc (length (first zs)))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: assms tps2_def tps3_def jk)
  let ?ll = "length (first zs)"
  let ?n = "length zs - Suc ?ll"
  have at_j1: "tps2 ! j1 = (\<lfloor>zs\<rfloor>, length (first zs) + 2)"
    using tps2_def jk by simp
  show "rneigh (tps2 ! j1) {0} ?n"
  proof (rule rneighI)
    show "(tps2 ::: j1) (tps2 :#: j1 + (length zs - Suc ?ll)) \<in> {0}"
      using at_j1 by simp
    show "(tps2 ::: j1) (tps2 :#: j1 + m) \<notin> {0}" if "m < length zs - Suc ?ll" for m
    proof -
      have *: "(tps2 ::: j1) (tps2 :#: j1 + m) = \<lfloor>zs\<rfloor> (?ll + 2 + m)"
        using at_j1 by simp
      have "Suc ?ll < length zs"
        using that by simp
      then have "?ll + 2 + m \<le> Suc (length zs)"
        using that by simp
      then have "\<lfloor>zs\<rfloor> (?ll + 2 + m) = zs ! (?ll + 1 + m)"
        using that by simp
      then have "\<lfloor>zs\<rfloor> (?ll + 2 + m) > 0"
        using zs that by (metis add.commute gr0I less_diff_conv not_add_less2 plus_1_eq_Suc)
      then show ?thesis
        using * by simp
    qed
  qed

  have 1: "implant (tps2 ! j1) (tps2 ! j3) ?n = (\<lfloor>second zs\<rfloor>, Suc (length (second zs)))"
  proof (cases "Suc ?ll \<le> length zs")
    case True
    have "implant (tps2 ! j1) (tps2 ! j3) ?n = implant (\<lfloor>zs\<rfloor>, ?ll + 2) (\<lfloor>[]\<rfloor>, 1) ?n"
      using tps2_def jk by (metis at_j1 nth_list_update_neq' tps0(3))
    also have "... = (\<lfloor>take ?n (drop (Suc ?ll) zs)\<rfloor>, Suc ?n)"
      using True implant_contents
      by (metis (no_types, lifting) One_nat_def add.commute add_2_eq_Suc' append.simps(1) diff_Suc_1
        dual_order.refl le_add_diff_inverse2 list.size(3) plus_1_eq_Suc zero_less_Suc)
    also have "... = (\<lfloor>take (length (second zs)) (drop (Suc ?ll) zs)\<rfloor>, Suc (length (second zs)))"
      using length_second_first by simp
    also have "... = (\<lfloor>second zs\<rfloor>, Suc (length (second zs)))"
      using second_def by simp
    finally show ?thesis .
  next
    case False
    then have "?n = 0"
      by simp
    then have "implant (tps2 ! j1) (tps2 ! j3) ?n = implant (\<lfloor>zs\<rfloor>, ?ll + 2) (\<lfloor>[]\<rfloor>, 1) 0"
      using tps2_def jk by (metis at_j1 nth_list_update_neq' tps0(3))
    then have "implant (tps2 ! j1) (tps2 ! j3) ?n = (\<lfloor>[]\<rfloor>, 1)"
      using transplant_0 by simp
    moreover have "second zs = []"
      using False second_def by simp
    ultimately show ?thesis
      by simp
  qed

  show "tps3 = tps2
      [j1 := tps2 ! j1 |+| ?n,
       j3 := implant (tps2 ! j1) (tps2 ! j3) ?n]"
    using tps3_def tps2_def using 1 jk at_j1 by (simp add: list_update_swap[of j1])
qed

definition "tps4 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, 1),
   j2 := (\<lfloor>first zs\<rfloor>, Suc (length (first zs))),
   j3 := (\<lfloor>second zs\<rfloor>, Suc (length (second zs)))]"

lemma tm4:
  assumes "ttt = 2 * length (first zs) + 7 + 2 * (length zs - Suc (length (first zs)))"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: assms tps3_def tps4_def jk zs)
  have "tps3 ! j1 |#=| 1 = (\<lfloor>zs\<rfloor>, 1)"
    using tps3_def jk by simp
  then show "tps4 = tps3[j1 := tps3 ! j1 |#=| 1]"
    unfolding tps4_def tps3_def using jk by (simp add: list_update_swap)
qed

lemma tm4' [transforms_intros]:
  assumes "ttt = 4 * length zs + 7"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  have "2 * length (first zs) + 7 + 2 * (length zs - Suc (length (first zs))) \<le> 2 * length (first zs) + 7 + 2 * length zs"
    by simp
  also have "... \<le> 2 * length zs + 7 + 2 * length zs"
    using length_first by simp
  also have "... = ttt"
    using assms by simp
  finally have "2 * length (first zs) + 7 + 2 * (length zs - Suc (length (first zs))) \<le> ttt" .
  then show ?thesis
    using assms tm4 transforms_monotone by simp
qed

definition "tps5 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, 1),
   j2 := (\<lfloor>first zs\<rfloor>, 1),
   j3 := (\<lfloor>second zs\<rfloor>, Suc (length (second zs)))]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 4 * length zs + 9 + Suc (length (first zs))"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: assms tps4_def tps5_def jk)
  show "clean_tape (tps4 ! j2)"
    using zs first_def tps4_def jk by simp
  have "tps4 ! j2 |#=| 1 = (\<lfloor>first zs\<rfloor>, 1)"
    using tps4_def jk by simp
  then show "tps5 = tps4[j2 := tps4 ! j2 |#=| 1]"
    unfolding tps5_def tps4_def using jk by (simp add: list_update_swap)
qed

definition "tps6 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, 1),
   j2 := (\<lfloor>first zs\<rfloor>, 1),
   j3 := (\<lfloor>second zs\<rfloor>, 1)]"

lemma tm6:
  assumes "ttt = 4 * length zs + 11 + Suc (length (first zs)) + Suc (length (second zs))"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: assms tps5_def tps6_def jk)
  show "clean_tape (tps5 ! j3)"
    using zs second_def tps5_def jk by simp
qed

definition "tps6' \<equiv> tps0
  [j2 := (\<lfloor>first zs\<rfloor>, 1),
   j3 := (\<lfloor>second zs\<rfloor>, 1)]"

lemma tps6': "tps6' = tps6"
  using tps6_def tps6'_def list_update_id tps0(1) by metis

lemma tm6':
  assumes "ttt = 6 * length zs + 13"
  shows "transforms tm6 tps0 ttt tps6'"
proof -
  have "4 * length zs + 11 + Suc (length (first zs)) + Suc (length (second zs)) \<le>
      4 * length zs + 13 + length zs + length (second zs)"
    using length_first by simp
  also have "... \<le> 6 * length zs + 13"
    using length_second by simp
  finally have "4 * length zs + 11 + Suc (length (first zs)) + Suc (length (second zs)) \<le> ttt"
    using assms by simp
  then show ?thesis
    using tm6 tps6' transforms_monotone by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_unpairI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and zs :: "symbol list"
  assumes "0 < j2" "0 < j3" "j1 \<noteq> j2" "j1 \<noteq> j3" "j2 \<noteq> j3" "j1 < k" "j2 < k" "j3 < k"
    and "length tps = k"
    and "proper_symbols zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    "tps ! j3 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 6 * length zs + 13"
  assumes "tps' = tps
    [j2 := (\<lfloor>first zs\<rfloor>, 1),
     j3 := (\<lfloor>second zs\<rfloor>, 1)]"
  shows "transforms (tm_unpair j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_unpair j1 j2 j3 .
  show ?thesis
    using assms loc.tps6'_def loc.tm6' loc.tm6_eq_tm_unpair by metis
qed

end
