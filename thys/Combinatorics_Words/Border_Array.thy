(*  Title:      Border Array
    File:       Combinatorics_Words.Border_Array
    Author:     Štěpán Holub, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Border_Array

imports
 CoWBasic

begin

subsection \<open>Auxiliary lemmas on suffix and border extension\<close>

lemma border_ConsD: assumes "b#x \<le>b a#w"
  shows "a = b" and
        "x \<noteq> \<epsilon> \<Longrightarrow> x \<le>b w" and
        border_ConsD_neq: "x \<noteq> w" and
        border_ConsD_pref: "x \<le>p w" and
        border_ConsD_suf: "x \<le>s w"
proof-
  show "a = b"
    using borderD_pref[OF assms] by force
  show "x \<noteq> w" and "x \<le>p w" and "x \<le>s w"
    using borderD_neq[OF assms, unfolded \<open>a = b\<close>]
      borderD_pref[OF assms, unfolded Cons_prefix_Cons]
      suffix_ConsD2[OF borderD_suf[OF assms]] by force+
  thus "x \<noteq> \<epsilon> \<Longrightarrow> x \<le>b w"
    unfolding border_def  by blast
qed

lemma ext_suf_Cons:
  "Suc i + \<^bold>|u\<^bold>| = \<^bold>|w\<^bold>| \<Longrightarrow> u \<le>s w \<Longrightarrow> (w!i)#u \<le>s (w!i)#w"
proof-
  assume "Suc i + \<^bold>|u\<^bold>| = \<^bold>|w\<^bold>|" and "u \<le>s w"
  hence "u = drop (Suc i) w"
    unfolding suffix_def using \<open>Suc i + \<^bold>|u\<^bold>| = \<^bold>|w\<^bold>|\<close> by auto
  have "i < \<^bold>|w\<^bold>|"
    using \<open>Suc i + \<^bold>|u\<^bold>| = \<^bold>|w\<^bold>|\<close> by auto
  from id_take_nth_drop[OF this, folded \<open>u = drop (Suc i) w\<close>]
  show "w ! i # u \<le>s w ! i # w"
    using suffix_ConsI triv_suf by metis
qed


lemma ext_suf_Cons_take_drop: assumes "take k (drop (Suc i) w) \<le>s drop (Suc i) w" and "w ! i = w ! (\<^bold>|w\<^bold>| - Suc k)"
  shows "take (Suc k) (drop i w) \<le>s drop i w"
proof (cases "(Suc k) + i < \<^bold>|w\<^bold>|", simp_all)
  assume "Suc (k + i) < \<^bold>|w\<^bold>|"

  hence "i < \<^bold>|w\<^bold>|"
    by simp

  have "Suc (\<^bold>|w\<^bold>| - Suc i - Suc k) = \<^bold>|w\<^bold>| - Suc(i+k)"
    using Suc_diff_Suc \<open>Suc (k + i) < \<^bold>|w\<^bold>|\<close>
    by (simp add: Suc_diff_Suc)

  have "\<^bold>|take k (drop (Suc i) w)\<^bold>| = k"
    using \<open>Suc (k + i) < \<^bold>|w\<^bold>|\<close> by fastforce

  have "Suc (\<^bold>|w\<^bold>| - Suc i - Suc k) + \<^bold>|take k (drop (Suc i) w)\<^bold>| = \<^bold>|drop (Suc i) w\<^bold>|"
    unfolding \<open>\<^bold>|take k (drop (Suc i) w)\<^bold>| = k\<close> \<open>Suc (\<^bold>|w\<^bold>| - Suc i - Suc k) = \<^bold>|w\<^bold>| - Suc(i+k)\<close>
    using  \<open>Suc (k + i) < \<^bold>|w\<^bold>|\<close> by simp

  hence "\<^bold>|drop (Suc (\<^bold>|w\<^bold>| - Suc i - k)) (drop i w)\<^bold>| = k"
    using  \<open>i < \<^bold>|w\<^bold>|\<close> by fastforce
  have "\<^bold>|w\<^bold>| - Suc i - k < \<^bold>|drop i w\<^bold>|"
    by (metis Suc_diff_Suc \<open>i < \<^bold>|w\<^bold>|\<close> diff_less_Suc length_drop)

  have "(drop i w)!(\<^bold>|w\<^bold>| - Suc i - k) = w ! i"
    using \<open>Suc (k + i) < \<^bold>|w\<^bold>|\<close> \<open>w ! i = w ! (\<^bold>|w\<^bold>| - Suc k)\<close> by auto

  have "take (Suc k) (drop i w) = w!i#take k (drop (Suc i) w)"
    using Cons_nth_drop_Suc[OF \<open>i < \<^bold>|w\<^bold>|\<close>] take_Suc_Cons[of k "w!i" "drop (Suc i) w"] by argo

  have "drop (Suc (\<^bold>|w\<^bold>| - Suc i - k)) (drop i w) = drop (\<^bold>|w\<^bold>| - Suc i - k) (drop (Suc i) w)"
    by auto
  hence "drop (Suc (\<^bold>|w\<^bold>| - Suc i - k)) (drop i w) = take k (drop (Suc i) w)"
    using \<open>\<^bold>|take k (drop (Suc i) w)\<^bold>| = k\<close>
      \<open>take k (drop (Suc i) w) \<le>s drop (Suc i) w\<close> suf_drop_conv length_drop by metis

  with
    id_take_nth_drop[OF \<open>\<^bold>|w\<^bold>| - Suc i - k < \<^bold>|drop i w\<^bold>|\<close>]
  show ?thesis
    unfolding \<open>(drop i w)!(\<^bold>|w\<^bold>| - Suc i - k) = w ! i\<close>
      \<open>take (Suc k) (drop i w) = w!i#take k (drop (Suc i) w)\<close>
    unfolding suffix_def by auto
qed

lemma ext_border_Cons:
  "Suc i + \<^bold>|u\<^bold>| = \<^bold>|w\<^bold>| \<Longrightarrow> u \<le>b w \<Longrightarrow> (w!i)#u \<le>b (w!i)#w"
  unfolding border_def using ext_suf_Cons Cons_prefix_Cons list.discI list.inject by metis

lemma border_add_Cons_len: assumes "max_borderP u w" and "v \<le>b (a#w)" shows "\<^bold>|v\<^bold>| \<le> Suc \<^bold>|u\<^bold>|"
proof-
  have "v \<noteq> \<epsilon>"
    using \<open>v \<le>b (a#w)\<close> by simp
  then obtain v' where "v = a#v'"
    using  borderD_pref[OF \<open>v \<le>b (a#w)\<close>, unfolded prefix_Cons] by blast
  show "\<^bold>|v\<^bold>| \<le> Suc \<^bold>|u\<^bold>|"
  proof (cases "v' = \<epsilon>")
    assume "v' \<noteq> \<epsilon>"
    have "w \<noteq> \<epsilon>"
      using  borderedI[OF \<open>v \<le>b (a#w)\<close>] sing_not_bordered[of a] by blast
    have "v' \<le>b w"
      using border_ConsD(2)[OF \<open>v \<le>b (a#w)\<close>[unfolded \<open>v = a # v'\<close>] \<open>v' \<noteq> \<epsilon>\<close>].
    thus "\<^bold>|v\<^bold>| \<le> Suc \<^bold>|u\<^bold>|"
      unfolding \<open>v = a # v'\<close> length_Cons Suc_le_mono
      using \<open>max_borderP u w\<close>[unfolded max_borderP_def]
        prefix_length_le by blast
  qed (simp add: \<open>v = a#v'\<close>)
qed

section \<open>Computing the Border Array\<close>

text\<open>The computation is a special case of the Knuth-Morris-Pratt algorithm.\<close>

text\<open>
\<^item> KMP w arr bord pos
\<^item> w: processed word does not change; it is processed starting from the last letter
\<^item> pos: actually examined pos-th letter; that is, it is w!(pos-1)
\<^item> arr: already calculated suffix-border-array of w;
       that is, the length of array is (|w| - pos)
       and arr!(|w| - pos - bord) is the max border length of the suffix of w of length bord
\<^item> bord: length of the current max border length candidate
       to see whether it can be extended we compare: w!(pos-1) ?= w!(|w| - (Suc bord));
       (Suc bord) is the length of the max border if the comparison is succesful
\<^item>      if the comparison fails we move to the max border of the suffix of length bord;
       its max border length is stored in arr!(|w| - pos - bord)
\<^item>      if bord was 0 and the comparison failed, the word is unbordered
\<close>

fun   KMP_arr :: "'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where    "KMP_arr _ arr _ 0 = arr" |
    "KMP_arr w arr bord (Suc i) =
          (if w!i = w!(\<^bold>|w\<^bold>| - (Suc bord))
          then  (Suc bord) # arr
          else (if bord = 0
                then  0#arr
                else (if (arr!(\<^bold>|w\<^bold>| - (Suc i) - bord)) < bord \<comment> \<open>always True, for sake of termination\<close>
                      then arr
                      else  undefined#arr \<comment> \<open>else: dummy termination condition\<close>
                      )
                )
          )"

fun KMP_bord :: "'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where     "KMP_bord _ _ bord 0 = bord" |
    "KMP_bord w arr bord (Suc i) =
          (if w!i = w!(\<^bold>|w\<^bold>| - (Suc bord))
          then Suc bord
          else (if bord = 0
                 then  0
                 else (if (arr!(\<^bold>|w\<^bold>| - (Suc i) - bord)) < bord \<comment> \<open>always True, for sake of termination\<close>
                       then arr!(\<^bold>|w\<^bold>| - (Suc i) - bord)
                       else  0 \<comment> \<open>dummy termination condition\<close>
                      )
                 )
          )"

fun KMP_pos :: "'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "KMP_pos _ _ _ 0 = 0" |
    "KMP_pos w arr bord (Suc i) =
          (if w!i = w!(\<^bold>|w\<^bold>| - (Suc bord))
          then i
          else (if bord = 0
                 then  i
                 else (if (arr!(\<^bold>|w\<^bold>| - (Suc i) - bord)) < bord \<comment> \<open>always True, for sake of termination\<close>
                       then Suc i
                       else  i \<comment> \<open>else: dummy termination condition\<close>
                      )
                 )
          )"

thm prod_cases
    nat.exhaust
    prod.exhaust
    prod_cases3

function KMP :: "'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "KMP w arr bord 0 = arr"  |
  "KMP w arr bord (Suc i) = KMP w (KMP_arr w arr bord (Suc i)) (KMP_bord w arr bord (Suc i)) (KMP_pos w arr bord (Suc i))"
  using not0_implies_Suc by (force+)
termination
  by (relation "measures [\<lambda>(_, _ , compar, pos). pos,\<lambda>(_, _ , compar, pos). compar]", simp_all)

lemma KMP_len: "\<^bold>|KMP w arr bord pos\<^bold>| = \<^bold>|arr\<^bold>| + pos"
  by (induct w arr bord pos rule: KMP.induct, auto)

value[nbe] "KMP [a] [0] 0 0"

value "KMP [ 0::nat] [0] 0 0"
value "KMP [5,4,5,3,5,5::nat] [0] 0 5"
value "KMP [5,4::nat,5,3,5,5] [1,0] 1 4"
value "KMP [0,1,1,0::nat,0,0,1,1,1] [0] 0 8"
value "KMP [0::nat,1] [0] 0 1"

subsection \<open>Verification of the computation\<close>

definition KMP_valid :: "'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "KMP_valid w arr bord pos = (\<^bold>|arr\<^bold>| + pos = \<^bold>|w\<^bold>|  \<and>
                                    \<comment> \<open>bord is the length of a border of (drop pos w), or 0\<close>
                                    pos + bord < \<^bold>|w\<^bold>| \<and>
                                    take bord (drop pos w) \<le>p (drop pos w) \<and>
                                    take bord (drop pos w) \<le>s (drop pos w) \<and>
                                    \<comment> \<open>... and no longer border can be extended\<close>
                                    (\<forall> v. v \<le>b w!(pos - 1)#(drop pos w) \<longrightarrow> \<^bold>|v\<^bold>| \<le> Suc bord) \<and>
                                    \<comment> \<open>the array gives maximal border lengths of corresponding suffixes\<close>
                                    (\<forall> k < \<^bold>|arr\<^bold>|. max_borderP (take (arr!k) (drop (pos + k) w)) (drop (pos + k) w))
                                    )"

lemma " KMP_valid w arr bord pos  \<Longrightarrow> w \<noteq> \<epsilon>"
  unfolding KMP_valid_def
  using le_antisym less_imp_le_nat less_not_refl2 take_Nil take_all_iff by metis

lemma KMP_valid_base: assumes "w \<noteq> \<epsilon>" shows "KMP_valid w [0] 0 (\<^bold>|w\<^bold>|-1)"
proof (unfold KMP_valid_def, intro conjI)
  show "\<^bold>|[0]\<^bold>| + (\<^bold>|w\<^bold>| - 1) = \<^bold>|w\<^bold>|"
    by (simp add: assms)
  show "\<^bold>|w\<^bold>| - 1 + 0 < \<^bold>|w\<^bold>|"
    using \<open>w \<noteq> \<epsilon>\<close>  by simp
  show "take 0 (drop (\<^bold>|w\<^bold>| - 1) w) \<le>p drop (\<^bold>|w\<^bold>| - 1) w"
    by simp
  show "take 0 (drop (\<^bold>|w\<^bold>| - 1) w) \<le>s drop (\<^bold>|w\<^bold>| - 1) w"
    by simp
  show "\<forall>v. v \<le>b w ! (\<^bold>|w\<^bold>| - 1 - 1) # drop (\<^bold>|w\<^bold>| - 1) w \<longrightarrow> \<^bold>|v\<^bold>| \<le> Suc 0"
  proof (rule allI, rule impI)
     fix v assume b: "v \<le>b w ! (\<^bold>|w\<^bold>| - 1 - 1) # drop (\<^bold>|w\<^bold>| - 1) w"
    have "\<^bold>|w ! (\<^bold>|w\<^bold>| - 1 - 1) # drop (\<^bold>|w\<^bold>| - 1) w\<^bold>| = Suc (Suc 0)"
      using \<open>\<^bold>|[0]\<^bold>| + (\<^bold>|w\<^bold>| - 1) = \<^bold>|w\<^bold>|\<close> by auto
    from border_len(3)[OF b, unfolded this]
    show "\<^bold>|v\<^bold>| \<le> Suc 0"
      using border_len(3)[OF b] by simp
  qed
  have  "\<^bold>|w\<^bold>| - Suc 0 = \<^bold>|butlast w\<^bold>|"
    by simp
  have all: "\<forall>v. v \<le>b [last w] \<longrightarrow> v \<le>p \<epsilon>"
      by (meson borderedI sing_not_bordered)
  have "butlast w \<cdot> [last w] = w"
    by (simp add: assms)
  hence last:  "drop (\<^bold>|w\<^bold>| - Suc 0) w = [last w]"
    unfolding \<open>\<^bold>|w\<^bold>| - Suc 0 = \<^bold>|butlast w\<^bold>|\<close> using drop_pref by metis
  hence "max_borderP \<epsilon> (drop (\<^bold>|w\<^bold>| - Suc 0) w)"
    unfolding max_borderP_def using all by simp
  thus "\<forall>k<\<^bold>|[0]\<^bold>|. max_borderP (take ([0] ! k) (drop (\<^bold>|w\<^bold>| - 1 + k) w)) (drop (\<^bold>|w\<^bold>| - 1 + k) w)"
    by simp
qed

lemma KMP_valid_step: assumes "KMP_valid w arr bord (Suc i)"
  shows "KMP_valid  w (KMP_arr w arr bord (Suc i)) (KMP_bord w arr bord (Suc i)) (KMP_pos w arr bord (Suc i))"
proof-
  \<comment> \<open>Consequences of the assumption\<close>
  have all_k: "\<forall>k<\<^bold>|arr\<^bold>|. max_borderP (take (arr ! k) (drop (Suc i + k) w)) (drop (Suc i + k) w)"
    using assms[unfolded KMP_valid_def] by blast
  have "\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|" and
    "Suc i + bord < \<^bold>|w\<^bold>|" and
    bord_pref: "take bord (drop (Suc i) w) \<le>p drop (Suc i) w" and
    bord_suf: "take bord (drop (Suc i) w) \<le>s drop (Suc i) w" and
    up_bord: "\<And> v. v \<le>b w!i#(drop (Suc i) w) \<Longrightarrow> \<^bold>|v\<^bold>| \<le> Suc bord" and
    all_k_neq0: "\<And> k. k < \<^bold>|arr\<^bold>| \<Longrightarrow> take (arr ! k) (drop (Suc i + k) w) = drop (Suc i + k) w \<longrightarrow> drop (Suc i + k) w = \<epsilon>" and
    all_k_pref: "\<And> k. k < \<^bold>|arr\<^bold>| \<Longrightarrow> take (arr ! k) (drop (Suc i + k) w) \<le>p drop (Suc i + k) w" and
    all_k_suf: "\<And> k. k < \<^bold>|arr\<^bold>| \<Longrightarrow> take (arr ! k) (drop (Suc i + k) w) \<le>s drop (Suc i + k) w" and
    all_k_v: "\<And> k v. k < \<^bold>|arr\<^bold>| \<Longrightarrow> v \<le>b drop (Suc i + k) w \<Longrightarrow> v \<le>p take (arr ! k) (drop (Suc i + k) w)"
    using assms[unfolded KMP_valid_def max_borderP_def diff_Suc_1] by blast+
  have all_k_neq: "\<And> k. k < \<^bold>|arr\<^bold>| \<Longrightarrow> take (arr ! k) (drop (Suc i + k) w) \<noteq> drop (Suc i + k) w"
    using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> \<open>\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|\<close> all_k_neq0
    add.commute add_le_imp_le_left drop_all_iff le_antisym less_imp_le_nat less_not_refl2 by metis

  have "w \<noteq> \<epsilon>"
    using \<open>\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|\<close> by auto
  have "Suc i < \<^bold>|w\<^bold>|"
    using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close>  by simp
  have pop_i: "drop i w = (w!i)# (drop (Suc i) w)"
    by (simp add: Cons_nth_drop_Suc Suc_lessD \<open>Suc i < \<^bold>|w\<^bold>|\<close>)
  have "drop (Suc i) w \<noteq> \<epsilon>"
    using \<open>Suc i < \<^bold>|w\<^bold>|\<close> by fastforce
  have "Suc i + (\<^bold>|w\<^bold>| - Suc i - bord) = \<^bold>|w\<^bold>| - bord"
    unfolding diff_right_commute[of _ _ bord] using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close>  by linarith

  show "KMP_valid  w (KMP_arr w arr bord (Suc i)) (KMP_bord w arr bord (Suc i)) (KMP_pos w arr bord (Suc i))"
  proof (cases "w ! i = w ! (\<^bold>|w\<^bold>| - Suc bord)")
    assume match: "w ! i = w ! (\<^bold>|w\<^bold>| - Suc bord)" \<comment> \<open>The current candidate is extendable\<close>
    show ?thesis
    proof (unfold KMP_valid_def KMP_arr.simps KMP_bord.simps KMP_pos.simps if_P[OF match], intro conjI)
      show "\<^bold>|Suc bord # arr\<^bold>| + i = \<^bold>|w\<^bold>|"
        using \<open>\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|\<close> by auto
      show "i + Suc bord < \<^bold>|w\<^bold>|"
        using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> by auto
      show "take (Suc bord) (drop i w) \<le>p drop i w"
        using take_is_prefix by auto
      show "take (Suc bord) (drop i w) \<le>s drop i w"
        using \<open>take bord (drop (Suc i) w) \<le>s drop (Suc i) w\<close> ext_suf_Cons_take_drop match by blast
          \<comment> \<open>The new border array is correct\<close>
      show all_k_new: "\<forall>k<\<^bold>|Suc bord # arr\<^bold>|. max_borderP (take ((Suc bord # arr) ! k) (drop (i + k) w)) (drop (i + k) w)"
      proof (rule allI, rule impI)
        fix k assume "k < \<^bold>|Suc bord # arr\<^bold>|"
        show "max_borderP (take ((Suc bord # arr) ! k) (drop (i + k) w)) (drop (i + k) w)"
        proof (cases "0 < k")
          assume "0 < k" \<comment> \<open>old entries are valid:\<close>
          thus ?thesis using all_k
            by (metis Suc_less_eq \<open>k < \<^bold>|Suc bord # arr\<^bold>|\<close> add.right_neutral add_Suc_shift gr0_implies_Suc list.size(4) nth_Cons_Suc)
        next
          assume "\<not> 0 < k" hence "k = 0" by simp
          show ?thesis \<comment> \<open>the extended border is maximal:\<close>
            unfolding max_borderP_def \<open>k = 0\<close>
          proof (intro conjI)
            show "take ((Suc bord # arr) ! 0) (drop (i + 0) w) = drop (i + 0) w \<longrightarrow> drop (i + 0) w = \<epsilon>"
              using \<open>i + Suc bord < \<^bold>|w\<^bold>|\<close> by fastforce
            show "take ((Suc bord # arr) ! 0) (drop (i + 0) w) \<le>p drop (i + 0) w"
              using \<open>take (Suc bord) (drop i w) \<le>p drop i w\<close> by auto
            show "take ((Suc bord # arr) ! 0) (drop (i + 0) w) \<le>s drop (i + 0) w"
              by simp fact
            show "\<forall>v. v \<le>b drop (i + 0) w \<longrightarrow> v \<le>p take ((Suc bord # arr) ! 0) (drop (i + 0) w)"
            proof (rule allI, rule impI)
              fix v assume "v \<le>b drop (i + 0) w" hence "v \<le>b drop i w" by simp
              from borderD_pref[OF this] up_bord[OF this[unfolded pop_i]]
              show "v \<le>p take ((Suc bord # arr) ! 0) (drop (i + 0) w)"
                 unfolding prefix_def by force
            qed
          qed
        qed
      qed
        \<comment> \<open>the extended border is the longest candidate:\<close>
      have "max_borderP (take (Suc bord) (drop i w)) (drop i w)"
        using  all_k_new[rule_format, of 0, unfolded length_Cons nth_Cons_0 add_0_right, OF zero_less_Suc].
      from border_add_Cons_len[OF this] max_borderP_D_max[OF this] max_borderP_D_neq[OF _ this]
      show "\<forall>v. v \<le>b w ! (i - 1) # drop i w \<longrightarrow> \<^bold>|v\<^bold>| \<le> Suc (Suc bord)"
        using nat_le_linear take_all take_len list.discI pop_i by metis
    qed
  next
    assume mismatch: "w ! i \<noteq> w ! (\<^bold>|w\<^bold>| - Suc bord)" \<comment> \<open>The current candidate is not extendable\<close>
    show ?thesis
    proof (cases "bord = 0")
      assume  "bord \<noteq> 0" \<comment> \<open>Recursion: try the maximal border of the current candidate...\<close>
        let ?k  =  "\<^bold>|w\<^bold>| - Suc i - bord" and
            ?w' = "drop (Suc i) w"
        have "?k < \<^bold>|arr\<^bold>|"
        using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> \<open>\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|\<close> \<open>bord \<noteq> 0\<close> by linarith
      from all_k_neq[OF this]
      have "arr ! ?k < bord" \<comment> \<open>... which is stored in the array, and is shorter\<close>
        by (simp add: \<open>take (arr ! ?k) (drop (Suc i + ?k) w) \<noteq> drop (Suc i + ?k) w\<close> \<open>Suc i + ?k = \<^bold>|w\<^bold>| - bord\<close> \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> add_diff_inverse_nat diff_add_inverse2 gr0I less_diff_conv nat_diff_split_asm )
        let ?old_pref = "take bord ?w'" and
            ?old_suf =  "drop (\<^bold>|w\<^bold>| - bord) w" and
            ?new_pref = "take (arr ! ?k) ?w'"
      show ?thesis
      proof (unfold KMP_valid_def KMP_arr.simps KMP_bord.simps KMP_pos.simps if_not_P[OF mismatch] if_not_P[OF \<open>bord \<noteq> 0\<close>] if_P[OF \<open>arr ! ?k < bord\<close>] diff_Suc_1, intro conjI)
        show "\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|"
          using \<open>\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|\<close> by auto
        show "Suc i + arr ! ?k < \<^bold>|w\<^bold>|"
          using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> \<open>arr ! ?k < bord\<close> by linarith
        show "take (arr ! ?k) (drop (Suc i) w) \<le>p drop (Suc i) w"
          using take_is_prefix by blast

        \<comment> \<open>Next goal: the new border is a suffix\<close>

        have "?old_suf \<le>s ?w'"
          by (meson \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> le_suf_drop less_diff_conv nat_less_le)
        have "\<^bold>|?old_pref\<^bold>| = bord"
          using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> take_len len_after_drop nat_less_le by blast
        also have "... = \<^bold>|?old_suf\<^bold>|"
          using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close>  by simp
        ultimately have eq1: "?old_pref = ?old_suf" \<comment> \<open>bord defines a border\<close>
          using \<open>take bord (drop (Suc i) w) \<le>s drop (Suc i) w\<close> \<open>drop (\<^bold>|w\<^bold>| - bord) w \<le>s drop (Suc i) w\<close> suf_ruler_eq_len by metis


        have "\<^bold>|?new_pref\<^bold>| = arr!?k"
          using take_len \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close> \<open>arr ! ?k < bord\<close> diff_diff_left by force
        have "take (arr ! ?k) ?old_suf \<le>p ?old_pref"
          using take_is_prefix \<open>?old_pref = ?old_suf\<close> by metis
        from pref_take[OF pref_trans[OF this take_is_prefix], unfolded \<open>\<^bold>|?new_pref\<^bold>| = arr!?k\<close>, symmetric]
        have "take (arr ! ?k) ?old_suf = take (arr ! ?k) ?w'"
          using take_len \<open>arr ! ?k < bord\<close> \<open>bord = \<^bold>|drop (\<^bold>|w\<^bold>| - bord) w\<^bold>|\<close> less_imp_le_nat by metis
        from all_k_suf[OF \<open>?k < \<^bold>|arr\<^bold>|\<close>, unfolded \<open>Suc i + ?k = \<^bold>|w\<^bold>| - bord\<close>] this
        have "take (arr ! ?k) ?w' \<le>s ?old_suf" by simp \<comment> \<open>The new prefix is a suffix of the old suffix\<close>

        with \<open>?old_pref \<le>s ?w'\<close>[unfolded \<open>?old_pref = ?old_suf\<close>]
        show "take (arr ! ?k) ?w' \<le>s ?w'"
          using suf_trans by blast

        \<comment> \<open>Key facts about borders of the w'\<close>
            have "?old_pref \<noteq> \<epsilon>"
              using \<open>bord \<noteq> 0\<close> \<open>\<^bold>|?old_pref\<^bold>| = bord\<close> by force
            moreover have "?old_pref \<noteq> ?w'"
              using \<open>Suc i + bord < \<^bold>|w\<^bold>|\<close>
              by (intro lenarg_not, unfold length_drop \<open>\<^bold>|take bord ?w'\<^bold>| = bord\<close>, linarith)
            ultimately have "?old_pref \<le>b ?w'" \<comment> \<open>bord is the length of a border\<close>
              by (intro borderI[OF bord_pref bord_suf])

        \<comment> \<open>We want to prove that the new border is the longest candidate\<close>
           show "\<forall>v. v \<le>b w !i # ?w' \<longrightarrow> \<^bold>|v\<^bold>| \<le> Suc (arr ! ?k)"
             proof (rule allI,rule impI)
               have extendable: "w ! i # v' \<le>b w ! i # ?w' \<Longrightarrow> v' \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|v'\<^bold>| \<le> arr ! ?k" for v' \<comment> \<open>First consider a border of w', which is extendable\<close>
               proof-
                 assume "w!i # v' \<le>b w!i # ?w'" and "v' \<noteq> \<epsilon>"
                 from suf_trans[OF borderD_suf[OF \<open>w!i # v' \<le>b w ! i # ?w'\<close>, folded pop_i] suffix_drop]
                 have "w!i # v' \<le>s w".
                 from this[unfolded suf_drop_conv, THEN nth_via_drop] mismatch
                 have "\<^bold>|w!i # v'\<^bold>| \<noteq> Suc bord"
                   by force
                 with up_bord[OF \<open>w!i # v' \<le>b w ! i # ?w'\<close>]
                 have "\<^bold>|v'\<^bold>| < bord"  \<comment> \<open>It is shorter than the old candidate border\<close>
                   by simp
                 from border_ConsD(2)[OF \<open>w!i # v' \<le>b w ! i # ?w'\<close> \<open>v' \<noteq> \<epsilon>\<close>]
                 have "v' \<le>b ?w'".
                 from borders_compare[OF \<open>?old_pref \<le>b ?w'\<close> this, unfolded  \<open>\<^bold>|?old_pref\<^bold>| = bord\<close>, unfolded \<open>?old_pref = ?old_suf\<close>, OF \<open>\<^bold>|v'\<^bold>| < bord\<close>]
                 have "v' \<le>b ?old_suf". \<comment> \<open>... and therefore its border\<close>
                 from prefix_length_le[OF max_borderP_D_max[OF all_k[rule_format, OF \<open>?k < \<^bold>|arr\<^bold>|\<close>], unfolded \<open>Suc i + ?k = \<^bold>|w\<^bold>| - bord\<close>, OF this]]
                 show "\<^bold>|v'\<^bold>| \<le> arr!?k" \<comment> \<open>... and hence short\<close>
                   using len_take1[of "arr!?k", of w] by simp
               qed
            fix v assume "v \<le>b w!i # ?w'"  \<comment> \<open>Now consider a border of the extended word\<close>
            show "\<^bold>|v\<^bold>| \<le> Suc (arr ! ?k)"
            proof (cases "\<^bold>|v\<^bold>| \<le> Suc 0")
              assume "\<not> \<^bold>|v\<^bold>| \<le> Suc 0" hence "Suc 0 < \<^bold>|v\<^bold>|" by simp
              from hd_tl_longE[OF this]
              obtain a v' where "v = a#v'" and "v' \<noteq> \<epsilon>"
                by blast
              with borderD_pref[OF \<open>v \<le>b w!i # ?w'\<close>, unfolded prefix_Cons]
              have "v = w!i#v'"
                by simp
              from extendable[OF \<open>v \<le>b w!i # ?w'\<close>[unfolded \<open>v = w!i#v'\<close>] \<open>v' \<noteq> \<epsilon>\<close>]
              show ?thesis
                by (simp add: \<open>v = a # v'\<close>)
          qed simp
        qed
        show " \<forall>k<\<^bold>|arr\<^bold>|. max_borderP (take (arr ! k) (drop (Suc i + k) w)) (drop (Suc i + k) w)"
          using all_k by blast
      qed
    next
      assume "bord = 0" \<comment> \<open>End of recursion.\<close>
      show ?thesis
      proof (unfold KMP_valid_def KMP_arr.simps KMP_bord.simps KMP_pos.simps if_not_P[OF mismatch] if_P[OF \<open>bord = 0\<close>], intro conjI)
        show "\<^bold>|0 # arr\<^bold>| + i = \<^bold>|w\<^bold>|"
          using \<open>\<^bold>|arr\<^bold>| + Suc i = \<^bold>|w\<^bold>|\<close> by auto
        show "i + 0 < \<^bold>|w\<^bold>|"
          by (simp add: Suc_lessD \<open>Suc i < \<^bold>|w\<^bold>|\<close>)
        show "take 0 (drop i w) \<le>p drop i w"
          by simp
        show "take 0 (drop i w) \<le>s drop i w"
          using ext_suf_Cons_take_drop by simp
            \<comment> \<open>The extension is unbordered\<close>
        have "max_borderP \<epsilon> (drop i w)"
        proof(rule ccontr)
          assume "\<not> max_borderP \<epsilon> (drop i w)"
          then obtain a t where "max_borderP (a#t) (drop i w)"
            unfolding pop_i  using max_border_ex[of "w ! i # drop (Suc i) w"] neq_Nil_conv by metis
          from up_bord[OF max_borderP_border[OF this list.simps(3), unfolded pop_i], unfolded \<open>bord = 0\<close>]
          have "t = \<epsilon>" by simp
          from max_borderP_border[OF \<open>max_borderP (a#t) (drop i w)\<close>[unfolded this] list.simps(3)]
          have "[a] \<le>b drop i w".
          from borderD_pref[OF this]
          have "w!i = a"
            by (simp add: pop_i)
          moreover have "w!(\<^bold>|w\<^bold>| - 1) = a"
            using  borderD_suf[OF \<open>[a] \<le>b drop i w\<close>] nth_via_drop sing_len suf_drop_conv suf_share_take suffix_drop suffix_length_le by metis
          ultimately show False
            using mismatch[unfolded \<open>bord = 0\<close>] by simp
        qed
        thus "\<forall>v. v \<le>b w ! (i - 1) # drop i w \<longrightarrow> \<^bold>|v\<^bold>| \<le> Suc 0"
          by (metis border_add_Cons_len list.size(3))
            \<comment> \<open>The array is valid: old values from assumption, the first 0 since the extension is unbordered\<close>
        show "\<forall>k<\<^bold>|0 # arr\<^bold>|. max_borderP (take ((0 # arr) ! k) (drop (i + k) w)) (drop (i + k) w)"
        proof (rule allI, rule impI)
          fix k assume "k < \<^bold>|0 # arr\<^bold>|"
          show "max_borderP (take ((0 # arr) ! k) (drop (i + k) w)) (drop (i + k) w)"
          proof (cases "0 < k")
            assume "0 < k"
            thus ?thesis using all_k
              by (metis Suc_less_eq \<open>k < \<^bold>|0 # arr\<^bold>|\<close> add.right_neutral add_Suc_shift gr0_implies_Suc list.size(4) nth_Cons_Suc)
          next
            assume "\<not> 0 < k" hence "k = 0" by simp
            thus ?thesis
              using \<open>max_borderP \<epsilon> (drop i w)\<close> by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma KMP_valid_max: assumes  "KMP_valid w arr bord pos" "k < \<^bold>|w\<^bold>|"
  shows "max_borderP (take ((KMP w arr bord pos)!k) (drop k w)) (drop k w)"
  using assms
proof (induct w arr bord pos arbitrary: k rule: KMP.induct)
  case (2 w arr bord i)
  then show ?case
    unfolding KMP.simps using KMP_valid_step  by blast
qed (simp add: KMP_valid_def)

section \<open>Border array\<close>

fun border_array :: "'a list \<Rightarrow> nat list" where
  "border_array \<epsilon> = \<epsilon>"
| "border_array (a#w) = rev (KMP (rev (a#w)) [0] 0 (\<^bold>|a#w\<^bold>|-1))"

lemma border_array_len: "\<^bold>|border_array w\<^bold>| = \<^bold>|w\<^bold>|"
  by (induct w, simp_all add: KMP_len)

theorem bord_array: assumes "Suc k \<le> \<^bold>|w\<^bold>|" shows "(border_array w)!k = \<^bold>|max_border (take (Suc k) w)\<^bold>|"
proof-
  define m where "m = \<^bold>|w\<^bold>| - Suc k"
  hence "m < \<^bold>|rev w\<^bold>|"
    by (simp add: Suc_diff_Suc assms less_eq_Suc_le)
  have "rev w \<noteq> \<epsilon>" and "k < \<^bold>|rev w\<^bold>|"
    using \<open>Suc k \<le> \<^bold>|w\<^bold>|\<close> by auto
  hence "w = hd w#tl w"
    by simp
  from arg_cong[OF border_array.simps(2)[of "hd w" "tl w", folded this], of rev, unfolded rev_rev_ident]
  have "rev (border_array w) =  (KMP (rev w) [0] 0 (\<^bold>|w\<^bold>|-1))".
  hence "max_borderP (take (rev (border_array w)!m) (drop m (rev w))) (drop m (rev w))"
    using KMP_valid_max[rule_format, OF KMP_valid_base[OF \<open>rev w \<noteq> \<epsilon>\<close>] \<open>m < \<^bold>|rev w\<^bold>|\<close>] by simp
  hence  "max_border (drop m (rev w)) = take (rev (border_array w)!m) (drop m (rev w))"
    using max_borderP_max_border by blast
  hence  "\<^bold>|max_border (drop m (rev w))\<^bold>| =  rev (border_array w)!m"
    by (metis \<open>m < \<^bold>|rev w\<^bold>|\<close> drop_all_iff leD max_border_nemp_neq nat_le_linear take_all take_len)
  thus ?thesis
    using m_def
    by (metis Suc_diff_Suc \<open>k < \<^bold>|rev w\<^bold>|\<close> \<open>m < \<^bold>|rev w\<^bold>|\<close> border_array_len diff_diff_cancel drop_rev length_rev less_imp_le_nat max_border_len_rev rev_nth)
qed

lemma max_border_comp [code]: "max_border w = take ((border_array w)!(\<^bold>|w\<^bold>|-1)) w"
proof (cases "w = \<epsilon>")
  assume "w = \<epsilon>"
  thus "max_border w = take ((border_array w)!(\<^bold>|w\<^bold>|-1)) w"
    using max_bord_take take_Nil by metis
next
  assume "w \<noteq> \<epsilon>"
  hence "Suc (\<^bold>|w\<^bold>| - 1) \<le> \<^bold>|w\<^bold>|" by simp
  from bord_array[OF this]
  have "(border_array w)!(\<^bold>|w\<^bold>|-1) = \<^bold>|max_border w\<^bold>|"
    by (simp add: \<open>w \<noteq> \<epsilon>\<close>)
  thus "max_border w = take ((border_array w)!(\<^bold>|w\<^bold>|-1)) w"
    using max_bord_take by auto
qed

value[nbe] "primitive [a,b,a]"

value "primitive [0,1,0::nat]"

value "border_array [5,4,5,3,5,5,5,4,5::nat]"

value "primitive [5,4,5,3,5,5,5,4,5::nat]"

value "primitive [5,4,5,3,5,5,5,4,5::nat]"

value[nbe] "bordered []"

value "border_array [0,1,1,0,0,0,1,1,1,1,1,0,0,0,1,1,1,0,1,1,0,0,0,1,1,1,1,1,1,0,0,0,1,1,1,0,1,1,0,0,0,1,1,1,0,1,1,0,0,0,1,1,1,0,0,1,0::nat]"

value[nbe] "border_array \<epsilon>"

value "border_array [1,0,1,0,1,1,0,0::nat]"

value "max_border [1,0,1,0,1,1,0,0,1,0,1,1,0,1,0,1,1,0,0,1,0,1,1,0,1,0,1,1,0,0,1,0,1,0,0,1::nat]"

thm max_border_comp \<comment> \<open>code for @{term max_border}, based on @{term border_array}\<close>

value "bordered [1,0::nat,1,0,1,1,0,1]"

value "\<pi> [1::nat,0,1,0,1,1,0,1]"

thm  min_per_root_take \<comment> \<open>code for @{term \<pi>}, based on @{term max_border}\<close>

value "\<^bold>|\<pi> [1::nat,0,1,0,1,1,0,1]\<^bold>|"

value "\<rho> [1::nat,0,1,1,0,1,1,0,1]"

thm primroot_code  \<comment> \<open>code for @{term \<rho>}, based on @{term \<pi>}\<close>

value "\<rho> [1::nat,0,1,1,0,1,1,0]"


value[nbe] "\<pi> \<epsilon>"


end
