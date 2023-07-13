section \<open>Coin Flip Space\<close>

text \<open>In this section, we introduce the coin flip space, an infinite lazy stream of booleans and
introduce a probability measure and topology for the space.\<close>

theory Coin_Space
  imports
    "HOL-Probability.Probability"
    "HOL-Library.Code_Lazy"
begin

lemma stream_eq_iff:
  assumes "\<And>i. x !! i = y !! i"
  shows "x = y"
proof -
  have "x = smap id x" by (simp add: stream.map_id)
  also have "... = y" using assms unfolding smap_alt by auto
  finally show ?thesis by simp
qed

text \<open>Notation for the discrete $\sigma$-algebra:\<close>

abbreviation discrete_sigma_algebra
  where "discrete_sigma_algebra \<equiv> count_space UNIV"

bundle discrete_sigma_algebra_notation
begin
  notation discrete_sigma_algebra ("\<D>")
end

bundle no_discrete_sigma_algebra_notation
begin
  no_notation discrete_sigma_algebra ("\<D>")
end

unbundle discrete_sigma_algebra_notation

lemma map_prod_measurable[measurable]:
  assumes "f \<in> M \<rightarrow>\<^sub>M M'"
  assumes "g \<in> N \<rightarrow>\<^sub>M N'"
  shows "map_prod f g \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M M' \<Otimes>\<^sub>M N'"
  using assms by (subst measurable_pair_iff) simp

lemma measurable_sigma_sets_with_exception:
  fixes f :: "'a \<Rightarrow> 'b :: countable"
  assumes "\<And>x. x \<noteq> d \<Longrightarrow> f -` {x} \<inter> space M \<in> sets M"
  shows "f \<in> M \<rightarrow>\<^sub>M count_space UNIV"
proof -
  define A :: "'b set set" where "A = (\<lambda>x. {x}) ` UNIV"

  have 0: "sets (count_space UNIV) = sigma_sets (UNIV :: 'b set) A"
    unfolding A_def by (subst sigma_sets_singletons) auto

  have 1: "f -` {x} \<inter> space M \<in> sets M" for x
  proof (cases "x = d")
    case True
    have "f -` {d} \<inter> space M = space M - (\<Union>y \<in> UNIV - {d}. f -` {y} \<inter> space M)"
      by (auto simp add:set_eq_iff)
    also have "... \<in> sets M"
      using assms
      by (intro sets.compl_sets sets.countable_UN) auto
    finally show ?thesis
      using True by simp
  next
    case False
    then show ?thesis using assms by simp
  qed
  hence 1: "\<And>y. y \<in> A \<Longrightarrow> f -` y \<inter> space M \<in> sets M"
    unfolding A_def by auto

  thus ?thesis
    by (intro measurable_sigma_sets[OF 0]) simp_all
qed

lemma restr_empty_eq: "restrict_space M {} = restrict_space N {}"
  by (intro measure_eqI) (auto simp add:sets_restrict_space)

lemma (in prob_space) distr_stream_space_snth [simp]:
  assumes "sets M = sets N"
  shows   "distr (stream_space M) N (\<lambda>xs. snth xs n) = M"
proof -
  have "distr (stream_space M) N (\<lambda>xs. snth xs n) = distr (stream_space M) M (\<lambda>xs. snth xs n)"
    by (rule distr_cong) (use assms in auto)
  also have "\<dots> = distr (Pi\<^sub>M UNIV (\<lambda>i. M)) M (\<lambda>f. f n)"
    by (subst stream_space_eq_distr, subst distr_distr) (auto simp: to_stream_def o_def)
  also have "\<dots> = M"
    by (intro distr_PiM_component prob_space_axioms) auto
  finally show ?thesis .
qed

lemma (in prob_space) distr_stream_space_shd [simp]:
  assumes "sets M = sets N"
  shows   "distr (stream_space M) N shd = M"
  using distr_stream_space_snth[OF assms, of 0] by (simp del: distr_stream_space_snth)

lemma shift_measurable:
  assumes "set x \<subseteq> space M"
  shows "(\<lambda>bs. x @- bs) \<in> stream_space M \<rightarrow>\<^sub>M stream_space M"
proof -
  have "(\<lambda>bs. (x @- bs) !! n) \<in> (stream_space M) \<rightarrow>\<^sub>M M" for n
  proof (cases "n < length x")
    case True
    have "(\<lambda>bs. (x @- bs) !! n) = (\<lambda>bs. x ! n)"
      using True by simp
    also have "... \<in> stream_space M \<rightarrow>\<^sub>M M"
      using assms True by (intro measurable_const) auto
    finally show ?thesis by simp
  next
    case False
    have "(\<lambda>bs. (x @- bs) !! n) = (\<lambda>bs. bs !! (n - length x))"
      using False by simp
    also have "... \<in> (stream_space M) \<rightarrow>\<^sub>M M"
      by (intro measurable_snth)
    finally show ?thesis by simp
  qed
  thus ?thesis
    by (intro measurable_stream_space2) auto
qed

lemma (in sigma_finite_measure) restrict_space_pair_lift:
  assumes "A' \<in> sets A"
  shows "restrict_space A A' \<Otimes>\<^sub>M M = restrict_space (A \<Otimes>\<^sub>M M) (A' \<times> space M)" (is "?L = ?R")
proof -
  let ?X = "((\<inter>) (A' \<times> space M) ` {a \<times> b |a b. a \<in> sets A \<and> b \<in> sets M})"
  have 0: "A' \<subseteq> space A"
    using assms sets.sets_into_space by blast

  have "?X \<subseteq> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
  proof (rule image_subsetI)
    fix x assume "x \<in> {a \<times> b |a b. a \<in> sets A \<and> b \<in> sets M}"
    then obtain u v where uv_def: "x = u \<times> v" "u \<in> sets A" "v \<in> sets M"
      by auto
    have 1:"u \<inter> A' \<in> sets (restrict_space A A')"
      using uv_def(2) unfolding sets_restrict_space by auto
    have "v \<subseteq> space M"
      using uv_def(3) sets.sets_into_space by auto
    hence "A' \<times> space M \<inter> x = (u \<inter> A') \<times> v"
      unfolding uv_def(1) by auto
    also have "... \<in> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
      using 1 uv_def(3) by auto

    finally show "A' \<times> space M \<inter> x \<in> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
      by simp
  qed
  moreover have "{a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M} \<subseteq> ?X"
  proof (rule subsetI)
    fix x assume "x \<in> {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}"
    then obtain u v where uv_def: "x = u \<times> v" "u \<in> sets (restrict_space A A')" "v \<in> sets M"
      by auto

    have "x = (A' \<times> space M) \<inter> x"
      unfolding uv_def(1) using uv_def(2,3) sets.sets_into_space
      by (intro Int_absorb1[symmetric]) (auto simp add:sets_restrict_space)
    moreover have "u \<in> sets A" using uv_def(2) assms unfolding sets_restrict_space by blast
    hence "x \<in> {a \<times> b |a b. a \<in> sets A \<and> b \<in> sets M}"
      unfolding uv_def(1) using uv_def(3) by auto
    ultimately show "x \<in> ?X"
      by simp
  qed
  ultimately have 2: "?X = {a \<times> b |a b. a \<in> sets (restrict_space A A') \<and> b \<in> sets M}" by simp

  have "sets ?R = sigma_sets (A'\<times>space M) ((\<inter>) (A'\<times>space M) ` {a\<times>b |a b. a \<in> sets A\<and>b \<in> sets M})"
    unfolding sets_restrict_space sets_pair_measure using assms  sets.sets_into_space
    by (intro sigma_sets_Int sigma_sets.Basic) auto
  also have "... = sets (restrict_space A A' \<Otimes>\<^sub>M M)"
    unfolding sets_pair_measure space_restrict_space Int_absorb2[OF 0] sets_restrict_space 2
    by auto
  finally have 3:"sets (restrict_space (A \<Otimes>\<^sub>M M) (A' \<times> space M)) = sets (restrict_space A A' \<Otimes>\<^sub>M M)"
    by simp

  have 4: "emeasure (restrict_space A A'\<Otimes>\<^sub>MM) S = emeasure (restrict_space (A\<Otimes>\<^sub>MM) (A'\<times>space M)) S"
    (is "?L1 = ?R1") if 5:"S \<in> sets (restrict_space A A' \<Otimes>\<^sub>M M)" for S
  proof -
    have "Pair x -` S = {}" if "x \<notin> A'" "x \<in> space A" for x
      using that 5 by (auto simp add:3[symmetric] sets_restrict_space)
    hence 5: "emeasure M (Pair x -` S) = 0" if "x \<notin> A'" "x \<in> space A" for x
      using that by auto
    have "?L1 = (\<integral>\<^sup>+ x. emeasure M (Pair x -` S) \<partial>restrict_space A A')"
      by (intro emeasure_pair_measure_alt[OF that])
    also have "... = (\<integral>\<^sup>+x\<in>A'. emeasure M (Pair x -` S) \<partial>A)"
      using assms by (intro nn_integral_restrict_space) auto
    also have "... = (\<integral>\<^sup>+x. emeasure M (Pair x -` S) \<partial>A)"
      using 5 by (intro nn_integral_cong) force
    also have "... = emeasure (A \<Otimes>\<^sub>M M) S"
      using that assms by (intro emeasure_pair_measure_alt[symmetric])
        (auto simp add:3[symmetric] sets_restrict_space)
    also have "... = ?R1"
      using assms that by (intro emeasure_restrict_space[symmetric])
        (auto simp add:3[symmetric] sets_restrict_space)
    finally show ?thesis by simp
  qed

  show ?thesis using 3 4
    by (intro measure_eqI) auto
qed

lemma to_stream_comb_seq_eq:
  "to_stream (comb_seq n x y) = stake n (to_stream x) @- to_stream y"
  unfolding comb_seq_def to_stream_def
  by (intro stream_eq_iff) simp

lemma to_stream_snth: "to_stream ((!!) x) = x"
  by (intro ext stream_eq_iff) (simp add:to_stream_def)

lemma snth_to_stream: "snth (to_stream x) = x"
  by (intro ext) (simp add:to_stream_def)

lemma (in prob_space) branch_stream_space:
  "(\<lambda>(x, y). stake n x @- y) \<in> stream_space M \<Otimes>\<^sub>M stream_space M \<rightarrow>\<^sub>M stream_space M"
  "distr (stream_space M \<Otimes>\<^sub>M stream_space M) (stream_space M) (\<lambda>(x,y). stake n x@-y)
    = stream_space M" (is "?L = ?R")
proof -
  let ?T = "stream_space M"
  let ?S = "PiM UNIV (\<lambda>_. M)"

  interpret S: sequence_space "M"
    by standard

  show 0:"(\<lambda>(x, y). stake n x @- y) \<in> ?T \<Otimes>\<^sub>M ?T \<rightarrow>\<^sub>M ?T"
    by simp

  have "?L = distr (distr ?S ?T to_stream \<Otimes>\<^sub>M distr ?S ?T to_stream) ?T (\<lambda>(x,y). stake n x@-y)"
    by (subst (1 2) stream_space_eq_distr) simp
  also have "... = distr (distr (?S \<Otimes>\<^sub>M ?S) (?T \<Otimes>\<^sub>M ?T) (\<lambda>(x, y). (to_stream x, to_stream y)))
     ?T (\<lambda>(x, y). stake n x @- y)"
    using prob_space_imp_sigma_finite[OF prob_space_stream_space]
    by (intro arg_cong2[where f="(\<lambda>x y. distr x ?T y)"] pair_measure_distr)
      (simp_all flip:stream_space_eq_distr)
  also have "... = distr (?S\<Otimes>\<^sub>M?S) ?T ((\<lambda>(x, y). stake n x@-y)\<circ>(\<lambda>(x, y). (to_stream x,to_stream y)))"
    by (intro distr_distr 0) (simp add: measurable_pair_iff)
  also have "... = distr (?S\<Otimes>\<^sub>M?S) ?T ((\<lambda>(x, y). stake n (to_stream x) @- to_stream y))"
    by (simp add:comp_def case_prod_beta')
  also have "... = distr (?S\<Otimes>\<^sub>M?S) ?T (to_stream \<circ> (\<lambda>(x, y). comb_seq n x y))"
    using to_stream_comb_seq_eq[symmetric]
    by (intro arg_cong2[where f="(\<lambda>x y. distr x ?T y)"] ext) auto
  also have "... = distr (distr (?S\<Otimes>\<^sub>M?S) ?S  (\<lambda>(x, y). comb_seq n x y)) ?T to_stream"
    by (intro distr_distr[symmetric] measurable_comb_seq) simp
  also have "... = distr ?S ?T to_stream"
    by (subst S.PiM_comb_seq) simp
  also have "... = ?R"
    unfolding stream_space_eq_distr[symmetric] by simp
  finally show "?L = ?R"
    by simp
qed

text \<open>The type for the coin flip space is isomorphic to @{typ "bool stream"}. Nevertheless, we
introduce it as a separate type to be able to introduce a topology and mark it as a lazy type for
code-generation:\<close>

codatatype coin_stream = Coin (chd:bool) (ctl:coin_stream)

code_lazy_type coin_stream

primcorec from_coins :: "coin_stream \<Rightarrow> bool stream" where
  "from_coins coins = chd coins ## (from_coins (ctl coins))"

primcorec to_coins :: "bool stream \<Rightarrow> coin_stream" where
  "to_coins str = Coin (shd str) (to_coins (stl str))"

lemma to_from_coins: "to_coins (from_coins x) = x"
  by (rule coin_stream.coinduct[where R="(\<lambda>x y. x = to_coins (from_coins y))"]) simp_all

lemma from_to_coins: "from_coins (to_coins x) = x"
  by (rule stream.coinduct[where R="(\<lambda>x y. x = from_coins (to_coins y))"]) simp_all

lemma bij_to_coins: "bij to_coins"
  by (intro bij_betwI[where g="from_coins"] to_from_coins from_to_coins) auto

lemma bij_from_coins: "bij from_coins"
  by (intro bij_betwI[where g="to_coins"] to_from_coins from_to_coins) auto

definition cshift where "cshift x y = to_coins (x @- from_coins y)"
definition cnth where "cnth x n = from_coins x !! n"
definition ctake where "ctake n x = stake n (from_coins x)"
definition cdrop where "cdrop n x = to_coins (sdrop n (from_coins x))"
definition rel_coins where "rel_coins x y = (to_coins x = y)"
definition cprefix where "cprefix x y \<longleftrightarrow> ctake (length x) y = x"
definition cconst where "cconst x = to_coins (sconst x)"

context
  includes lifting_syntax
begin

lemma bi_unique_rel_coins [transfer_rule]: "bi_unique rel_coins"
  unfolding rel_coins_def using inj_onD[OF bij_is_inj[OF bij_to_coins]]
  by (intro bi_uniqueI left_uniqueI right_uniqueI) auto

lemma bi_total_rel_coins [transfer_rule]: "bi_total rel_coins"
  unfolding rel_coins_def using from_to_coins to_from_coins
  by (intro bi_totalI left_totalI right_totalI) auto

lemma cnth_transfer [transfer_rule]: "(rel_coins ===> (=) ===> (=)) snth cnth"
  unfolding rel_coins_def cnth_def rel_fun_def by (auto simp:from_to_coins)

lemma cshift_transfer [transfer_rule]: "((=) ===> rel_coins ===> rel_coins) shift cshift"
  unfolding rel_coins_def cshift_def rel_fun_def by (auto simp:from_to_coins)

lemma ctake_transfer [transfer_rule]: "((=) ===> rel_coins ===> (=)) stake ctake"
  unfolding rel_coins_def ctake_def rel_fun_def by (auto simp:from_to_coins)

lemma cdrop_transfer [transfer_rule]: "((=) ===> rel_coins ===> rel_coins) sdrop cdrop"
  unfolding rel_coins_def cdrop_def rel_fun_def by (auto simp:from_to_coins)

lemma chd_transfer [transfer_rule]: "(rel_coins ===> (=)) shd chd"
  unfolding rel_coins_def rel_fun_def by (auto simp:from_to_coins)

lemma ctl_transfer [transfer_rule]: "(rel_coins ===> rel_coins) stl ctl"
  unfolding rel_coins_def rel_fun_def by (auto simp:from_to_coins)

lemma cconst_transfer [transfer_rule]: "((=) ===> rel_coins) sconst cconst"
  unfolding rel_coins_def cconst_def rel_fun_def by (auto simp:from_to_coins)

end

lemma coins_eq_iff:
  assumes "\<And>i. cnth x i = cnth y i"
  shows "x = y"
proof -
  have "(\<forall>i. cnth x i = cnth y i) \<longrightarrow> x = y"
    by transfer (use stream_eq_iff in auto)
  thus ?thesis using assms by simp
qed

lemma length_ctake [simp]: "length (ctake n x) = n"
  by transfer (rule length_stake)

lemma ctake_nth[simp]: "m < n \<Longrightarrow> ctake n s ! m = cnth s m"
  by transfer (rule stake_nth)

lemma ctake_cdrop: "cshift (ctake n s) (cdrop n s) = s"
  by transfer (rule stake_sdrop)

lemma cshift_append[simp]: "cshift (p@q) s = cshift p (cshift q s)"
  by transfer (rule shift_append)

lemma cshift_empty[simp]: "cshift [] xs = xs"
  by transfer simp

lemma ctake_null[simp]: "ctake 0 xs = []"
  by transfer simp

lemma ctake_Suc[simp]: "ctake (Suc n) s = chd s # ctake n (ctl s)"
  by transfer simp

lemma cdrop_null[simp]: "cdrop 0 s = s"
  by transfer simp

lemma cdrop_Suc[simp]: "cdrop (Suc n) s = cdrop n (ctl s)"
  by transfer simp

lemma chd_shift[simp]: "chd (cshift xs s) = (if xs = [] then chd s else hd xs)"
  by transfer simp

lemma ctl_shift[simp]: "ctl (cshift xs s) = (if xs = [] then ctl s else cshift (tl xs) s)"
  by transfer simp

lemma shd_sconst[simp]: "chd (cconst x) = x"
  by transfer simp

lemma take_ctake: "take n (ctake m s) = ctake (min n m) s"
  by transfer (rule take_stake)

lemma ctake_add[simp]: "ctake m s @ ctake n (cdrop m s) = ctake (m + n) s"
  by transfer (rule stake_add)

lemma cdrop_add[simp]: "cdrop m (cdrop n s) = cdrop (n + m) s"
  by transfer (rule sdrop_add)

lemma cprefix_iff: "cprefix x y \<longleftrightarrow> (\<forall>i < length x. cnth y i = x ! i)" (is "?L \<longleftrightarrow> ?R")
proof -
  have "?L \<longleftrightarrow> ctake (length x) y = x"
    unfolding cprefix_def by simp
  also have "... \<longleftrightarrow> (\<forall>i < length x . (ctake (length x) y) ! i = x ! i)"
    by (simp add: list_eq_iff_nth_eq)
  also have "... \<longleftrightarrow> ?R"
    by (intro all_cong) simp
  finally show ?thesis by simp
qed

text \<open>A non-empty shift is not idempotent:\<close>

lemma empty_if_shift_idem:
  assumes "\<And>cs. cshift h cs = cs"
  shows "h = []"
proof (cases h)
  case Nil
  then show ?thesis by simp
next
  case (Cons hh ht)
  have "[hh] = ctake 1 (cshift (hh#ht) (cconst (\<not> hh)))"
    by simp
  also have "... = ctake 1 (cconst (\<not> hh))"
    using assms unfolding Cons by simp
  also have "... = [\<not> hh]" by simp
  finally show ?thesis by simp
qed

text \<open>Stream version of @{thm [source] prefix_length_prefix}:\<close>

lemma cprefix_length_prefix:
  assumes "length x \<le> length y"
  assumes "cprefix x bs" "cprefix y bs"
  shows "prefix x y"
proof -
  have "take (length x) y = take (length x) (ctake (length y) bs)"
    using assms(3) unfolding cprefix_def by simp
  also have "... = ctake (length x) bs"
    unfolding take_ctake using assms by simp
  also have "... = x"
    using assms(2) unfolding cprefix_def by simp
  finally have "take (length x) y = x"
    by simp
  thus ?thesis
    by (metis take_is_prefix)
qed

lemma same_prefix_not_parallel:
  assumes "cprefix x bs" "cprefix y bs"
  shows "\<not>(x \<parallel> y)"
  using assms cprefix_length_prefix
  by (cases "length x \<le> length y") auto

lemma ctake_shift:
  "ctake m (cshift xs ys) = (if m \<le> length xs then take m xs else xs @ ctake (m - length xs) ys)"
proof (induction m arbitrary: xs)
  case (Suc m xs)
  thus ?case
    by (cases xs) auto
qed auto

lemma ctake_shift_small [simp]: "m \<le> length xs \<Longrightarrow> ctake m (cshift xs ys) = take m xs"
  and ctake_shift_big [simp]:
    "m \<ge> length xs \<Longrightarrow> ctake m (cshift xs ys) = xs @ ctake (m - length xs) ys"
  by (subst ctake_shift; simp)+

lemma cdrop_shift:
  "cdrop m (cshift xs ys) = (if m \<le> length xs then cshift (drop m xs) ys else cdrop (m - length xs) ys)"
proof (induction m arbitrary: xs)
  case (Suc m xs)
  thus ?case
    by (cases xs) auto
qed auto

lemma cdrop_shift_small [simp]:
    "m \<le> length xs \<Longrightarrow> cdrop m (cshift xs ys) = cshift (drop m xs) ys"
  and cdrop_shift_big [simp]:
    "m \<ge> length xs \<Longrightarrow> cdrop m (cshift xs ys) = cdrop (m - length xs) ys"
  by (subst cdrop_shift; simp)+

text \<open>Infrastructure for building coin streams:\<close>

primcorec cmap_iterate ::" ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> coin_stream"
  where
    "cmap_iterate m f s = Coin (m s) (cmap_iterate m f (f s))"

lemma cmap_iterate: "cmap_iterate m f s = to_coins (smap m (siterate f s))"
proof (rule coin_stream.coinduct
    [where R="(\<lambda>xs ys. (\<exists>x. xs = cmap_iterate m f x \<and> ys= to_coins (smap m (siterate f x))))"])
  show "\<exists>x. cmap_iterate m f s = cmap_iterate m f x \<and>
        to_coins (smap m (siterate f s)) = to_coins (smap m (siterate f x))"
    by (intro exI[where x="s"] refl conjI)
next
  fix xs ys
  assume "\<exists>x. xs = cmap_iterate m f x \<and> ys = to_coins (smap m (siterate f x))"
  then obtain x where 0:"xs = cmap_iterate m f x" "ys = to_coins (smap m (siterate f x))"
    by auto

  have "chd xs = chd ys"
    unfolding 0 by (subst cmap_iterate.ctr, subst siterate.ctr) simp
  moreover have "ctl xs = cmap_iterate m f (f x)"
    unfolding 0 by (subst cmap_iterate.ctr) simp
  moreover have "ctl ys = to_coins(smap m(siterate f (f x)))"
    unfolding 0 by (subst siterate.ctr) simp
  ultimately show
    "chd xs = chd ys \<and> (\<exists>x. ctl xs=cmap_iterate m f x \<and> ctl ys = to_coins (smap m (siterate f x)))"
    by auto
qed

definition build_coin_gen ::  "('a \<Rightarrow> bool list) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> coin_stream"
  where
    "build_coin_gen m f s = cmap_iterate (hd \<circ> fst)
      (\<lambda>(r,s'). (if tl r = [] then (m s', f s') else (tl r, s'))) (m s, f s)"

lemma build_coin_gen_aux:
  fixes f :: "'a \<Rightarrow> 'b stream"
  assumes "\<And>x. (\<exists>n y. n \<noteq> [] \<and> f x = n@-f y \<and> g x = n@-g y)"
  shows "f x = g x"
proof (rule stream.coinduct[where R="(\<lambda>xs ys. (\<exists>x n. xs = n @- (f x) \<and> ys = n @- (g x)))"])
  show "\<exists>y n. f x = n @-(f y) \<and> g x = n @- (g y)"
    by (intro exI[where x="x"] exI[where x="[]"]) auto
next
  fix xs ys :: "'b stream"
  assume "\<exists>x n. xs = n @- (f x) \<and> ys = n @- (g x)"
  hence "\<exists>x n. n \<noteq> [] \<and> xs = n @- (f x) \<and> ys = n @- (g x)"
    using assms by (metis shift.simps(1))
  then obtain x n where 0:"xs = n @- (f x)" "ys = n @- (g x)" "n \<noteq> []"
    by auto

  have "shd xs = shd ys"
    using 0 by simp
  moreover have "stl xs = tl n@-(f x)" "stl ys = tl n@-(g x)"
    using 0 by auto
  ultimately show "shd xs = shd ys \<and> (\<exists>x n. stl xs =  n@- (f x) \<and> stl ys =  n@- (g x))"
    by auto
qed

lemma build_coin_gen:
  assumes "\<And>x. m x \<noteq> []"
  shows "build_coin_gen m f s = to_coins (flat (smap m (siterate f s)))"
proof -
  let ?g = "(\<lambda>(r, s'). if tl r = [] then (m s', f s') else (tl r, s'))"

  have liter: "smap (hd \<circ> fst) (siterate ?g (bs, x)) =
    bs @- (smap (hd \<circ> fst) (siterate ?g (m x, f x)))" if "bs \<noteq> []" for x bs
    using that
  proof (induction bs rule:list_nonempty_induct)
    case (single y)
    then show ?case by (subst siterate.ctr) simp
  next
    case (cons y ys)
    then show ?case by (subst siterate.ctr) (simp add:comp_def)
  qed
  have "smap(hd\<circ>fst) (siterate ?g (m x,f x)) = m x@- smap(hd\<circ>fst) (siterate ?g (m (f x), f (f x)))"
    for x by (subst liter[OF assms]) auto
  moreover have "flat (smap m (siterate f x)) = m x @- flat (smap m (siterate f (f x)))" for x
    by (subst siterate.ctr) (simp add:flat_Stream[OF assms])

  ultimately have "\<exists>n y. n \<noteq> [] \<and>
    smap (hd \<circ> fst) (siterate ?g (m x, f x)) = n @- smap (hd \<circ> fst) (siterate ?g (m y, f y)) \<and>
    flat (smap m (siterate f x)) = n @- flat (smap m (siterate f y))" for x
    by (intro exI[where x="m x"] exI[where x="f x"] conjI assms)

  hence "smap (hd \<circ> fst) (siterate ?g (m s', f s')) = flat (smap m (siterate f s'))" for s'
    by (rule build_coin_gen_aux[where f="(\<lambda>x. smap (hd \<circ> fst) (siterate ?g (m x, f x)))"])
  thus ?thesis
    unfolding build_coin_gen_def cmap_iterate by simp
qed

text \<open>Measure space for coin streams:\<close>

definition coin_space :: "coin_stream measure"
  where "coin_space = embed_measure (stream_space (measure_pmf (pmf_of_set UNIV))) to_coins"

bundle coin_space_notation
begin
  notation coin_space ("\<B>")
end

bundle no_coin_space_notation
begin
  no_notation coin_space ("\<B>")
end

unbundle coin_space_notation

lemma space_coin_space: "space \<B> = UNIV"
  using bij_is_surj[OF bij_to_coins]
  unfolding coin_space_def space_embed_measure space_stream_space by simp

lemma B_t_eq_distr: "\<B> = distr (stream_space (pmf_of_set UNIV)) \<B> to_coins"
  unfolding coin_space_def by (intro embed_measure_eq_distr bij_is_inj[OF bij_to_coins])

lemma from_coins_measurable: "from_coins \<in> \<B> \<rightarrow>\<^sub>M (stream_space (pmf_of_set UNIV))"
  unfolding coin_space_def by (intro measurable_embed_measure1) (simp add:from_to_coins)

lemma to_coins_measurable: "to_coins \<in> (stream_space (pmf_of_set UNIV)) \<rightarrow>\<^sub>M \<B>"
  unfolding coin_space_def
  by (intro measurable_embed_measure2 bij_is_inj[OF bij_to_coins])

lemma chd_measurable: "chd \<in> \<B> \<rightarrow>\<^sub>M \<D>"
proof -
  have 0:"chd (to_coins x) = shd x" for x
    using chd_transfer unfolding rel_fun_def by auto
  thus ?thesis
    unfolding coin_space_def by (intro measurable_embed_measure1) simp
qed

lemma cnth_measurable: "(\<lambda>xs. cnth xs i) \<in> \<B> \<rightarrow>\<^sub>M \<D>"
  unfolding coin_space_def cnth_def by (intro measurable_embed_measure1) (simp add:from_to_coins)

lemma B_eq_distr:
  "stream_space (pmf_of_set UNIV) = distr \<B> (stream_space (pmf_of_set UNIV)) from_coins"
  (is "?L = ?R")
proof -
  let ?S = "stream_space (pmf_of_set UNIV)"
  have "?R = distr (distr ?S \<B> to_coins) ?S from_coins"
    using B_t_eq_distr by simp
  also have "... = distr ?S ?S (from_coins \<circ> to_coins)"
    by (intro distr_distr to_coins_measurable from_coins_measurable)
  also have "... = distr ?S ?S id"
    unfolding id_def comp_def from_to_coins by simp
  also have "... = ?L"
    unfolding id_def by simp
  finally show ?thesis
    by simp
qed

lemma B_t_finite: "emeasure \<B> (space \<B>) = 1"
proof -
  let ?S = "stream_space (pmf_of_set (UNIV::bool set))"
  have "1 = emeasure ?S (space ?S)"
    by (intro prob_space.emeasure_space_1[symmetric] prob_space.prob_space_stream_space
        prob_space_measure_pmf)
  also have "... = emeasure \<B> (from_coins -` (space (stream_space (pmf_of_set UNIV))) \<inter> space \<B>)"
    by (subst B_eq_distr) (intro emeasure_distr from_coins_measurable sets.top)
  also have "... = emeasure \<B> (space \<B>)"
    unfolding space_coin_space space_stream_space vimage_def by simp
  finally show ?thesis by simp
qed

interpretation coin_space: prob_space coin_space
  using B_t_finite by standard

lemma distr_shd: "distr \<B> \<D> chd = pmf_of_set UNIV" (is "?L = ?R")
proof -
  have "?L = distr (stream_space (measure_pmf (pmf_of_set UNIV))) \<D> (chd \<circ> to_coins)"
    by (subst B_t_eq_distr) (intro distr_distr to_coins_measurable chd_measurable)
  also have "... = distr (stream_space (measure_pmf (pmf_of_set UNIV))) \<D> shd"
    using chd_transfer unfolding rel_fun_def rel_coins_def by (simp add:comp_def)
  also have "... = ?R"
    using coin_space.distr_stream_space_shd by auto
  finally show ?thesis by simp
qed

lemma cshift_measurable: "cshift x \<in> \<B> \<rightarrow>\<^sub>M \<B>"
proof -
  have "(to_coins \<circ> shift x \<circ> from_coins) \<in> \<B> \<rightarrow>\<^sub>M \<B>"
    by (intro measurable_comp[OF from_coins_measurable] measurable_comp[OF _ to_coins_measurable]
        shift_measurable) auto
  thus ?thesis
    unfolding cshift_def by (simp add:comp_def)
qed

lemma cdrop_measurable: "cdrop x \<in> \<B> \<rightarrow>\<^sub>M \<B>"
proof -
  have "(to_coins \<circ> sdrop x \<circ> from_coins) \<in> \<B> \<rightarrow>\<^sub>M \<B>"
    by (intro measurable_comp[OF from_coins_measurable] measurable_comp[OF _ to_coins_measurable]
        shift_measurable) auto
  thus ?thesis
    unfolding cdrop_def by (simp add:comp_def)
qed

lemma ctake_measurable: "ctake k \<in> \<B> \<rightarrow>\<^sub>M \<D>"
proof -
  have "stake k \<circ> from_coins \<in> \<B> \<rightarrow>\<^sub>M \<D>"
    by (intro measurable_comp[OF from_coins_measurable]) simp
  thus ?thesis
    unfolding ctake_def by (simp add:comp_def)
qed

lemma branch_coin_space:
  "(\<lambda>(x, y). cshift (ctake n x) y) \<in> \<B> \<Otimes>\<^sub>M \<B> \<rightarrow>\<^sub>M \<B>"
  "distr (\<B> \<Otimes>\<^sub>M \<B>) \<B> (\<lambda>(x,y). cshift (ctake n x) y) = \<B>" (is "?L = ?R")
proof -
  let ?M = "stream_space (measure_pmf (pmf_of_set UNIV))"
  let ?f = "(\<lambda>(x,y). stake n x @- y)"
  let ?g = "map_prod from_coins from_coins"

  have "(\<lambda>(x, y). cshift (ctake n x) y) = to_coins \<circ> (?f \<circ> ?g)"
    by (simp add:comp_def cshift_def ctake_def case_prod_beta')
  also have "... \<in> \<B> \<Otimes>\<^sub>M \<B> \<rightarrow>\<^sub>M \<B>"
    by (intro measurable_comp[OF _ to_coins_measurable] measurable_comp[where N="(?M \<Otimes>\<^sub>M ?M)"]
        map_prod_measurable from_coins_measurable prob_space.branch_stream_space(1)
        prob_space_measure_pmf)
  finally show "(\<lambda>(x, y). cshift (ctake n x) y) \<in> \<B> \<Otimes>\<^sub>M \<B> \<rightarrow>\<^sub>M \<B>"
    by simp

  have "distr (\<B> \<Otimes>\<^sub>M \<B>) (?M \<Otimes>\<^sub>M ?M) ?g = (distr \<B> ?M from_coins \<Otimes>\<^sub>M distr \<B> ?M from_coins)"
    unfolding map_prod_def using prob_space_measure_pmf
    by (intro pair_measure_distr[symmetric] from_coins_measurable) (auto intro!:
        prob_space_imp_sigma_finite prob_space.prob_space_stream_space simp:B_eq_distr[symmetric])
  also have "... = ?M \<Otimes>\<^sub>M ?M"
    unfolding B_eq_distr[symmetric] by simp
  finally have 0: "distr (\<B> \<Otimes>\<^sub>M \<B>) (?M \<Otimes>\<^sub>M ?M) ?g = (?M \<Otimes>\<^sub>M ?M)"
    by simp

  have "?L = distr (\<B> \<Otimes>\<^sub>M \<B>) \<B> (to_coins \<circ> ?f \<circ> ?g)"
    unfolding cshift_def ctake_def by (simp add:comp_def map_prod_def case_prod_beta')
  also have "... = distr (distr (\<B> \<Otimes>\<^sub>M \<B>) (?M \<Otimes>\<^sub>M ?M) ?g) \<B> (to_coins \<circ> ?f)"
    by (intro distr_distr[symmetric] map_prod_measurable from_coins_measurable
        measurable_comp[OF _ to_coins_measurable] prob_space_measure_pmf) simp
  also have "... = distr (?M \<Otimes>\<^sub>M ?M) \<B> (to_coins \<circ> ?f)"
    unfolding 0 by simp
  also have "... = distr (distr (?M \<Otimes>\<^sub>M ?M) ?M ?f) \<B> to_coins"
    by (intro distr_distr[symmetric] to_coins_measurable) simp
  also have "... = distr ?M \<B> to_coins"
    by (subst prob_space.branch_stream_space(2)) (auto intro:prob_space_measure_pmf)
  also have "... = ?R"
    using B_t_eq_distr by simp
  finally show "?L = ?R"
    by simp
qed

definition from_coins_t :: "coin_stream \<Rightarrow> (nat \<Rightarrow> bool discrete)"
  where "from_coins_t = snth \<circ> smap discrete \<circ> from_coins"

definition to_coins_t :: "(nat \<Rightarrow> bool discrete) \<Rightarrow> coin_stream"
  where "to_coins_t = to_coins \<circ> smap of_discrete \<circ> to_stream"

lemma from_to_coins_t:
  "from_coins_t (to_coins_t x) = x"
  unfolding to_coins_t_def from_coins_t_def
  by (intro ext) (simp add:snth_to_stream from_to_coins of_discrete_inverse)

lemma to_from_coins_t:
  "to_coins_t (from_coins_t x) = x"
  unfolding to_coins_t_def from_coins_t_def
  by (simp add:to_stream_snth to_from_coins comp_def discrete_inverse
      stream.map_comp stream.map_ident)

lemma bij_to_coins_t: "bij to_coins_t"
  by (intro bij_betwI[where g="from_coins_t"] to_from_coins_t from_to_coins_t) auto

lemma bij_from_coins_t: "bij from_coins_t"
  by (intro bij_betwI[where g="to_coins_t"] to_from_coins_t from_to_coins_t) auto

instantiation coin_stream :: topological_space
begin
definition open_coin_stream :: "coin_stream set \<Rightarrow> bool"
  where "open_coin_stream U = open (from_coins_t ` U)"

instance proof
  show "open (UNIV :: coin_stream set)"
    using bij_is_surj[OF bij_from_coins_t] unfolding open_coin_stream_def by simp
  show "open (S \<inter> T)" if "open S" "open T" for S T :: "coin_stream set"
    using that unfolding open_coin_stream_def image_Int[OF bij_is_inj[OF bij_from_coins_t]]
    by auto
  show "open (\<Union> K)" if "\<forall>S \<in> K. open S" for K :: "coin_stream set set"
    using that unfolding open_coin_stream_def image_Union
    by auto
qed
end

definition coin_stream_basis
  where "coin_stream_basis = (\<lambda>x. Collect (cprefix x)) ` UNIV"

lemma image_collect_eq: "f ` {x. A (f x)} = {x. A x} \<inter> range f"
  by auto

lemma coin_stream_basis: "topological_basis coin_stream_basis"
proof -
  have "bij_betw (\<lambda>x. (!!) (smap discrete x)) UNIV UNIV"
    by (intro bij_betwI[where g="smap of_discrete \<circ> to_stream"]) (simp_all add:to_stream_snth
        snth_to_stream stream.map_comp comp_def of_discrete_inverse discrete_inverse
        stream.map_ident)
  hence 3:"range (\<lambda>x. (!!) (smap discrete x)) = UNIV"
    using bij_is_surj by auto

  obtain K :: "(nat \<Rightarrow> bool discrete) set set" where
    K_countable: "countable K" and K_top_basis: "topological_basis K" and
    K_cylinder: "\<forall>k\<in>K. \<exists>X. (k = Pi\<^sub>E UNIV X) \<and> (\<forall>i. open (X i)) \<and> finite {i. X i \<noteq> UNIV}"
  using product_topology_countable_basis by auto

  have from_coins_cprefix: "from_coins_t ` {xs. cprefix p xs} =
    PiE UNIV (\<lambda>i. if i < length p then {discrete (p ! i)} else UNIV)" (is "?L = ?R") for p
  proof -
    have 2:"from_coins ` {xs. cprefix p xs} = {f. \<forall>i < length p. f !! i = p ! i}"
      unfolding cprefix_iff cnth_def using bij_is_surj[OF bij_from_coins]
      by (subst image_collect_eq) auto

    have "from_coins_t`{xs. cprefix p xs} = (snth\<circ>smap discrete)`(from_coins ` {xs. cprefix p xs})"
      unfolding from_coins_t_def image_image by simp
    also have "... = (snth \<circ> smap discrete) ` {f. \<forall>i < length p. f !! i = p ! i}"
      unfolding 2 by simp
    also have "... = (\<lambda>x. snth (smap discrete x)) `
      {f. \<forall>i < length p. (smap discrete f) !! i = discrete (p ! i)}"
      by (simp add:discrete_inject)
    also have "... = {x. \<forall>i<length p. x i = discrete (p ! i)} \<inter> range (\<lambda>x. (!!) (smap discrete x))"
      by (intro image_collect_eq)
    also have "... = {x. \<forall>i<length p. x i = discrete (p ! i)}"
      unfolding 3 by simp
    also have "... = PiE UNIV (\<lambda>i. if i < length p then {discrete (p ! i)} else UNIV)"
      unfolding PiE_def Pi_def by auto
    finally show ?thesis
      by simp
  qed

  have "open U" if 0:"U \<in> coin_stream_basis" for U
  proof -
    obtain p where U_eq:"U = {xs. cprefix p xs}" using 0 unfolding coin_stream_basis_def by auto
    show ?thesis
      unfolding open_coin_stream_def U_eq from_coins_cprefix
      by (intro open_PiE) (auto intro:open_discrete)
  qed
  moreover have "\<exists>B\<in>coin_stream_basis. x \<in> B \<and> B \<subseteq> U" if "open U" "x \<in> U" for U x
  proof -
    have "open (from_coins_t ` U)" "from_coins_t x \<in> from_coins_t ` U"
      using that unfolding open_coin_stream_def by auto
    then obtain B where B: "B \<in> K" "from_coins_t x \<in> B" "B \<subseteq> from_coins_t ` U"
      using topological_basisE[OF K_top_basis] by blast
    obtain X where X: "B = Pi\<^sub>E UNIV X" and fin_X: "finite {i. X i \<noteq> UNIV}"
      using K_cylinder B(1) by auto
    define Z where "Z i = (X i \<noteq> UNIV)" for i
    define n where "n = (if {i. X i \<noteq> UNIV} \<noteq> {} then Suc (Max {i. X i \<noteq> UNIV}) else 0)"
    have "i < n" if "Z i" for i
      using fin_X that less_Suc_eq_le unfolding n_def Z_def[symmetric] by (auto split:if_split_asm)
    hence X_univ: "X i = UNIV" if "i \<ge> n" for i
      using that leD unfolding Z_def by auto

    define R where "R = {xs. cprefix (ctake n x) xs}"
    have "{discrete (ctake n x ! i)} \<subseteq> X i" if "i < n" for i
    proof -
      have "{discrete (ctake n x ! i)} = {discrete (cnth x i)}" using that
        by simp
      also have "... = {from_coins_t x i}"
        unfolding from_coins_t_def cnth_def by simp
      also have "... \<subseteq> X i"
        using B(2) unfolding X PiE_def Pi_def by auto
      finally show ?thesis
        by simp
    qed
    hence "from_coins_t ` R \<subseteq> PiE UNIV X"
      using X_univ unfolding R_def from_coins_cprefix
      by (intro PiE_mono) auto
    moreover have "... \<subseteq> from_coins_t ` U"
      using B(3) X by simp
    ultimately have "from_coins_t ` R \<subseteq> from_coins_t ` U"
      by simp
    hence "R \<subseteq> U"
      using bij_is_inj[OF bij_from_coins_t]
      by (simp add: inj_image_eq_iff subset_image_iff)
    moreover have "R \<in> coin_stream_basis" "x \<in> R"
      unfolding R_def coin_stream_basis_def by (auto simp:cprefix_def)
    ultimately show ?thesis
      by auto
  qed
  ultimately show ?thesis
    by (intro topological_basisI) auto
qed

lemma coin_steam_open: "open {xs. cprefix x xs}"
  by (intro topological_basis_open[OF coin_stream_basis]) (simp add:coin_stream_basis_def)

instance coin_stream :: second_countable_topology
proof
  show "\<exists>(B :: coin_stream set set). countable B \<and> open = generate_topology B"
    by (intro exI[where x="coin_stream_basis"] topological_basis_imp_subbasis conjI
        coin_stream_basis) (simp add:coin_stream_basis_def)
qed

instantiation coin_stream :: uniformity_dist
begin
definition dist_coin_stream :: "coin_stream \<Rightarrow> coin_stream \<Rightarrow> real"
  where "dist_coin_stream x y = dist (from_coins_t x) (from_coins_t y)"

definition uniformity_coin_stream :: "(coin_stream \<times> coin_stream) filter"
  where "uniformity_coin_stream = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

instance proof
  show "uniformity = (INF e\<in>{0 <..}. principal {(x, y). dist (x::coin_stream) y < e})"
    unfolding uniformity_coin_stream_def by simp
qed
end

lemma in_from_coins_iff: "x \<in> from_coins_t ` U \<longleftrightarrow> (to_coins_t x \<in> U)"
  using to_from_coins_t from_to_coins_t by (simp add:image_iff) metis

instantiation coin_stream :: metric_space
begin
instance proof
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)" for U :: "coin_stream set"
  proof -
    have "open U \<longleftrightarrow> open (from_coins_t ` U)"
      unfolding open_coin_stream_def by simp
    also have "... \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist (from_coins_t x) y < e \<longrightarrow> y \<in> from_coins_t ` U)"
      unfolding fun_open_ball_aux by auto
    also have "... \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. \<forall>y \<in> to_coins_t ` UNIV. dist x y < e \<longrightarrow> y \<in> U)"
      unfolding dist_coin_stream_def by (intro ball_cong refl ex_cong)
       (simp add: from_to_coins_t in_from_coins_iff)
    also have "... \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> y \<in> U)"
      using bij_is_surj[OF bij_to_coins_t] by simp
    finally have "open U = (\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> y \<in> U)"
      by simp
    thus ?thesis
      unfolding eventually_uniformity_metric by simp
  qed
  show "(dist x y = 0) = (x = y)" for x y :: coin_stream
    unfolding dist_coin_stream_def by (metis dist_eq_0_iff to_from_coins_t)
  show "dist x y \<le> dist x z + dist y z" for x y z :: coin_stream
    unfolding dist_coin_stream_def by (intro dist_triangle2)
qed
end

lemma from_coins_t_u_continuous: "uniformly_continuous_on UNIV from_coins_t"
  unfolding uniformly_continuous_on_def dist_coin_stream_def by auto

lemma to_coins_t_u_continuous: "uniformly_continuous_on UNIV to_coins_t"
  unfolding uniformly_continuous_on_def dist_coin_stream_def from_to_coins_t by auto

lemma to_coins_t_continuous: "continuous_on UNIV to_coins_t"
  using to_coins_t_u_continuous uniformly_continuous_imp_continuous by auto

instance coin_stream :: complete_space
proof
  show "convergent X" if "Cauchy X" for X :: "nat \<Rightarrow> coin_stream"
  proof -
    have "Cauchy (from_coins_t \<circ> X)" 
      using uniformly_continuous_imp_Cauchy_continuous[unfolded Cauchy_continuous_on_def]
            from_coins_t_u_continuous that by auto
    hence "convergent (from_coins_t \<circ> X)"
      by (rule Cauchy_convergent)
    then obtain x where "(from_coins_t \<circ> X) \<longlonglongrightarrow> x"
      unfolding convergent_def by auto
    moreover have "isCont to_coins_t x"
      using to_coins_t_continuous continuous_on_eq_continuous_within by blast
    ultimately have "(to_coins_t \<circ> from_coins_t \<circ> X) \<longlonglongrightarrow> to_coins_t x"
      using isCont_tendsto_compose by (auto simp add:comp_def)
    thus "convergent X"
      unfolding convergent_def comp_def to_from_coins_t by auto
  qed
qed

lemma at_least_borelI:
  assumes "topological_basis K"
  assumes "countable K"
  assumes "K \<subseteq> sets M"
  assumes "open U"
  shows "U \<in> sets M"
proof -
  obtain K' where K'_range: "K' \<subseteq> K" and "\<Union>K' = U"
    using assms(1,4) unfolding topological_basis_def by blast
  hence "U = \<Union>K'" by simp
  also have "... \<in> sets M"
    using K'_range assms(2,3) countable_subset
    by (intro sets.countable_Union) auto
  finally show ?thesis by simp
qed

lemma measurable_sets_coin_space:
  assumes "f \<in> measurable \<B> A"
  assumes "Collect P \<in> sets A"
  shows "{xs. P (f xs)} \<in> sets \<B>"
proof -
  have "{xs. P (f xs)} = f -` Collect P \<inter> space \<B>"
    unfolding vimage_def space_coin_space by simp
  also have "... \<in> sets \<B>"
    by (intro measurable_sets[OF assms(1,2)])
  finally show ?thesis by simp
qed

lemma coin_space_is_borel_measure:
  assumes "open U"
  shows "U \<in> sets \<B>"
proof -
  have 0:"countable coin_stream_basis"
    unfolding coin_stream_basis_def by simp

  have cnth_sets: "{xs. cnth xs i = v} \<in> sets \<B>" for i v
    by (intro measurable_sets_coin_space[OF cnth_measurable]) auto

  have "{xs. cprefix x xs} \<in> sets \<B>" for x
  proof (cases "x \<noteq> []")
    case True
    have "{xs. cprefix x xs} = (\<Inter>i < length x. {xs. cnth xs i = x ! i})"
      unfolding cprefix_iff by auto
    also have "... \<in> sets \<B>"
      using cnth_sets True
      by (intro sets.countable_INT image_subsetI) auto
    finally show ?thesis by simp
  next
    case False
    hence "{xs. cprefix x xs} = space \<B>"
      unfolding cprefix_iff space_coin_space by simp
    also have "... \<in> sets \<B>"
      by simp
    finally show ?thesis by simp
  qed
  hence 1:"coin_stream_basis \<subseteq> sets \<B>"
    unfolding coin_stream_basis_def by auto
  show ?thesis
    using at_least_borelI[OF coin_stream_basis 0 1 assms] by simp
qed

text \<open>This is the upper topology on @{typ "'a option"} with the natural partial order on
@{typ "'a option"}.\<close>

definition option_ud :: "'a option topology"
  where "option_ud = topology (\<lambda>S. S=UNIV \<or> None \<notin> S)"

lemma option_ud_topology: "istopology (\<lambda>S. S=UNIV \<or> None \<notin> S)" (is "istopology ?T")
proof -
  have "?T (U \<inter> V)" if "?T U" "?T V" for U V using that by auto
  moreover have "?T (\<Union>K)" if "\<And>U. U \<in> K \<Longrightarrow> ?T U" for K using that by auto
  ultimately show ?thesis unfolding istopology_def by auto
qed

lemma openin_option_ud: "openin option_ud S \<longleftrightarrow> (S = UNIV \<or> None \<notin> S)"
  unfolding option_ud_def by (subst topology_inverse'[OF option_ud_topology]) auto

lemma topspace_option_ud: "topspace option_ud = UNIV"
proof -
  have "UNIV \<subseteq> topspace option_ud" by (intro openin_subset) (simp add:openin_option_ud)
  thus ?thesis by auto
qed

lemma contionuos_into_option_udI:
  assumes "\<And>x. openin X (f -` {Some x} \<inter> topspace X)"
  shows "continuous_map X option_ud f"
proof -
  have "openin X {x \<in> topspace X. f x \<in> U}" if "openin option_ud U" for U
  proof (cases "U = UNIV")
    case True
    then show ?thesis by simp
  next
    case False
    define V where "V = the ` U"
    have "None \<notin> U"
      using that False unfolding openin_option_ud by simp
    hence "Some ` V = id ` U"
      unfolding V_def image_image id_def
      by (intro image_cong refl) (metis option.exhaust_sel)
    hence "U = Some ` V" by simp
    hence "{x \<in> topspace X. f x \<in> U} = (\<Union>v \<in> V. f -` {Some v} \<inter> topspace X)" by auto
    moreover have "openin X (\<Union>v \<in> V. f -` {Some v} \<inter> topspace X)"
      using assms by (intro openin_Union) auto
    ultimately show ?thesis by auto
  qed
  thus ?thesis
    unfolding continuous_map topspace_option_ud by auto
qed

lemma map_option_continuous:
  "continuous_map option_ud option_ud (map_option f)"
  by (intro contionuos_into_option_udI) (simp add:topspace_option_ud vimage_def openin_option_ud)

end

