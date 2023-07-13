section \<open>Tracking Randomized Algorithms\label{sec:tracking_randomized_algorithm}\<close>

text \<open>This section introduces the @{term "track_random_bits"} monad morphism, which converts a
randomized algorithm to one that tracks the number of used coin-flips. The resulting algorithm
can still be executed. This morphism is useful for testing and debugging. For the verification
of coin-flip usage, the morphism @{term "tspmf_of_ra"} introduced in
Section~\ref{sec:tracking_spmfs} is more useful.\<close>

theory Tracking_Randomized_Algorithm
  imports Randomized_Algorithm
begin

definition track_random_bits :: "'a random_alg_int \<Rightarrow> ('a \<times> nat) random_alg_int"
  where "track_random_bits f bs =
    do {
      (r,bs') \<leftarrow> f bs;
      n \<leftarrow> consumed_bits f bs;
      Some ((r,n),bs')
    }"

lemma track_random_bits_Some_iff:
  assumes "track_random_bits f bs \<noteq> None"
  shows "f bs \<noteq> None"
  using assms unfolding track_random_bits_def by (cases "f bs", auto)

lemma track_random_bits_alt:
  assumes "wf_random f"
  shows "track_random_bits f bs =
    map_option (\<lambda>p. ((eval_rm f p, length p), cdrop (length p) bs)) (consumed_prefix f bs)"
proof (cases "consumed_prefix f bs")
  case None
  hence "f bs = None"
    by (subst wf_random_alt[OF assms(1)]) simp
  then show ?thesis
    unfolding track_random_bits_def None by simp
next
  case (Some a)
  hence "f bs = Some (eval_rm f a, cdrop (length a) bs)"
    by (subst wf_random_alt[OF assms(1)]) simp
  then show ?thesis
    unfolding track_random_bits_def Some consumed_bits_def by simp
qed

lemma track_rb_coin:
  "track_random_bits coin_rai = coin_rai \<bind> (\<lambda>b. return_rai (b,1))" (is "?L = ?R")
proof (rule ext)
  fix bs :: "coin_stream"
  have "wf_on_prefix coin_rai [chd bs] (chd bs)"
    unfolding wf_on_prefix_def coin_rai_def by simp
  moreover have "cprefix [chd bs] bs"
    unfolding cprefix_def by simp
  ultimately have "{p \<in> ptree_rm (coin_rai). cprefix p bs} = {[chd bs]}"
    by (intro prefixes_singleton) (auto simp:ptree_rm_def)
  hence "consumed_prefix (coin_rai) bs = Some [chd bs]"
    unfolding consumed_prefix_def by simp
  hence "consumed_bits (coin_rai) bs = Some 1"
    unfolding consumed_bits_def by simp
  thus "?L bs = ?R bs"
    unfolding track_random_bits_def bind_rai_def
    by (simp add:coin_rai_def return_rai_def)
qed

lemma track_rb_return: "track_random_bits (return_rai x) = return_rai (x,0)" (is "?L = ?R")
proof (rule ext)
  fix bs :: "coin_stream"
  have "wf_on_prefix (return_rai x) [] x"
    unfolding wf_on_prefix_def return_rai_def by simp
  moreover have "cprefix [] bs"
    unfolding cprefix_def by simp
  ultimately have "{p \<in> ptree_rm (return_rai x). cprefix p bs} = {[]}"
    by (intro prefixes_singleton) (auto simp:ptree_rm_def)
  hence "consumed_prefix (return_rai x) bs = Some []"
    unfolding consumed_prefix_def by simp
  hence "consumed_bits (return_rai x) bs = Some 0"
    unfolding consumed_bits_def by simp
  thus "?L bs = ?R bs"
    unfolding track_random_bits_def by (simp add:return_rai_def)
qed

lemma consumed_prefix_imp_wf:
  assumes "consumed_prefix m bs = Some p"
  shows "wf_on_prefix m p (eval_rm m p)"
proof -
  have "p \<in> ptree_rm m"
    using assms unfolding consumed_prefix_def the_elem_opt_Some_iff[OF prefixes_at_most_one] by blast
  then obtain r where "wf_on_prefix m p r"
    unfolding ptree_rm_def by auto
  thus ?thesis
    unfolding wf_on_prefix_def eval_rm_def by simp
qed

lemma consumed_prefix_imp_prefix:
  assumes "consumed_prefix m bs = Some p"
  shows "cprefix p bs"
  using assms unfolding consumed_prefix_def the_elem_opt_Some_iff[OF prefixes_at_most_one] by blast

lemma consumed_prefix_bindI:
  assumes "consumed_prefix m bs = Some p"
  assumes "consumed_prefix (f (eval_rm m p)) (cdrop (length p) bs) = Some q"
  shows "consumed_prefix (m \<bind> f) bs = Some (p@q)"
proof -
  define r where "r = eval_rm m p"

  have 0: "wf_on_prefix m p r"
    unfolding r_def using consumed_prefix_imp_wf[OF assms(1)] by simp

  have "consumed_prefix (f r) (cdrop (length p) bs) = Some q"
    using assms(2) unfolding r_def by simp
  hence 1: "wf_on_prefix (f r) q (eval_rm (f r) q)"
    using consumed_prefix_imp_wf by auto
  have "wf_on_prefix (m \<bind> f) (p@q) (eval_rm (f r) q)"
    by (intro wf_on_prefix_bindI[where r="r"] 0 1)
  hence "p@q \<in> ptree_rm (m \<bind> f)"
    unfolding ptree_rm_def by auto
  moreover have "cprefix p bs" "cprefix q (cdrop (length p) bs)"
    using consumed_prefix_imp_prefix assms by auto
  hence "cprefix (p@q) bs"
    unfolding cprefix_def by (metis length_append ctake_add)
  ultimately have "{p \<in> ptree_rm (m \<bind> f). cprefix p bs} = {p@q}"
    by (intro prefixes_singleton) auto
  thus ?thesis
    unfolding consumed_prefix_def by simp
qed

lemma track_rb_bind:
  assumes "wf_random m"
  assumes "\<And>x. x \<in> range_rm m \<Longrightarrow> wf_random (f x)"
  shows "track_random_bits (m \<bind> f) = track_random_bits m \<bind>
  (\<lambda>(r,n). track_random_bits (f r) \<bind> (\<lambda>(r',m). return_rai (r',n+m)))" (is "?L = ?R")
proof (rule ext)
  fix bs :: "coin_stream"
  have wf_bind: "wf_random (m \<bind> f)"
    by (intro wf_bind assms)

  consider (a) "m bs = None" | (b) "m bs \<noteq> None \<and> (m \<bind> f) bs = None" | (c) "(m \<bind> f) bs \<noteq> None"
    by blast
  then show "?L bs = ?R bs"
  proof (cases)
    case a
    thus ?thesis
      unfolding track_random_bits_def bind_rai_def a by simp
  next
    case b
    then obtain r bs' where 0:"m bs = Some (r,bs')" by auto
    have 1:"(f r) bs' = None" using b unfolding bind_rai_def 0 by simp
    then show ?thesis  unfolding track_random_bits_def bind_rai_def 0 by simp
  next
    case c
    have "(m \<bind> f) bs  = None" if "m bs = None"
      using that unfolding bind_rai_def by simp
    hence "m bs \<noteq> None" using c by blast
    then obtain p where 0:
      "m bs = Some (eval_rm m p, cdrop (length p) bs)" "consumed_prefix m bs = Some p"
      using wf_random_alt[OF assms(1)] by auto
    define bs' where "bs' = cdrop (length p) bs"
    define r where "r = eval_rm m p"
    have 1: "m bs = Some (r, bs')" unfolding 0 r_def bs'_def by simp
    hence "r \<in> range_rm m" using 1 in_range_rmI by metis
    hence wf: "wf_random (f r)" by (intro assms(2))
    have "f r bs' \<noteq> None" using c 1 unfolding bind_rai_def by force
    then obtain q where 2:
      "f r bs' = Some (eval_rm (f r) q, cdrop (length q) bs')" "consumed_prefix (f r) bs' = Some q"
      using wf_random_alt[OF wf] by auto

    hence 3:"consumed_prefix (m \<bind> f) bs = Some (p@q)"
      unfolding r_def bs'_def by (intro consumed_prefix_bindI 0) auto

    have "track_random_bits m bs = Some ((r, length p), bs')"
      unfolding track_random_bits_alt[OF assms(1)] bind_rai_def 0 bs'_def r_def by simp
    moreover have "track_random_bits (f r) bs' =
      Some ((eval_rm (f r) q, length q), cdrop (length q) bs')"
      unfolding track_random_bits_alt[OF wf] 2 by simp
    moreover have "wf_on_prefix m p r"
      unfolding r_def by (intro consumed_prefix_imp_wf[OF 0(2)])
    hence "eval_rm (f r) q = eval_rm (m \<bind> f) (p@q)"
      unfolding eval_rm_def bind_rai_def wf_on_prefix_def by simp
    ultimately have
      "?R bs = Some ((eval_rm (m \<bind> f) (p@q), length p+length q), cdrop (length p+length q) bs)"
      unfolding bind_rai_def return_rai_def bs'_def by simp
    also have "... = ?L bs"
      unfolding track_random_bits_alt[OF wf_bind] 3 by simp
    finally show ?thesis by simp
  qed
qed

lemma track_random_bits_mono:
  assumes "wf_random f" "wf_random g"
  assumes "ord_rai f g"
  shows "ord_rai (track_random_bits f) (track_random_bits g)"
proof -
  have "track_random_bits f bs = track_random_bits g bs"
    if "track_random_bits f bs \<noteq> None" for bs
  proof -
    have "f bs \<noteq> None" using that track_random_bits_Some_iff by simp
    then obtain r bs' where "f bs = Some (r,bs')" by auto
    then obtain p where 0:"wf_on_prefix f p r" and 2:"cprefix p bs"
      using assms(1) unfolding wf_random_def by (auto split:option.split_asm)

    have 1: "wf_on_prefix g p r"
      using wf_lub_helper[OF assms(3)] 0 by blast

    have "track_random_bits h bs = Some ((r, length p),cdrop (length p) bs)"
      if "wf_on_prefix h p r" "wf_random h" for h
    proof -
      have "p \<in> ptree_rm h"
        using that unfolding ptree_rm_def by auto
      hence "{p \<in> ptree_rm h. cprefix p bs} = {p}"
        using 2 by (intro prefixes_singleton) auto
      hence "consumed_prefix h bs = Some p"
        unfolding consumed_prefix_def by simp
      moreover have "eval_rm h p = r"
        using that(1) unfolding wf_on_prefix_def eval_rm_def by simp
      ultimately show  ?thesis
        unfolding track_random_bits_alt[OF that(2)] by simp
    qed

    thus ?thesis
      using 0 1 assms(1,2) by simp
  qed
  thus ?thesis
    unfolding ord_rai_def fun_ord_def flat_ord_def by blast
qed

lemma wf_track_random_bits:
  assumes "wf_random f"
  shows "wf_random (track_random_bits f)"
proof (rule wf_randomI)
  fix bs
  assume "track_random_bits f bs \<noteq> None"
  hence "f bs \<noteq> None" using track_random_bits_Some_iff by blast
  then obtain r bs' where "f bs = Some (r, bs')"
    by auto
  then obtain p where 0:"wf_on_prefix f p r" "cprefix p bs"
    using assms unfolding wf_random_def by (auto split:option.split_asm)
  hence "{q \<in> ptree_rm f. cprefix q (cshift p cs)} = {p}" for cs
    by (intro prefixes_singleton) (auto simp:cprefix_def ptree_rm_def)
  hence "consumed_prefix f (cshift p cs) = Some p" for cs
    unfolding consumed_prefix_def by simp
  hence "wf_on_prefix (track_random_bits f) p (r, length p)"
    using 0 unfolding track_random_bits_def wf_on_prefix_def consumed_bits_def by simp
  thus "\<exists>p r. cprefix p bs \<and> wf_on_prefix (track_random_bits f) p r"
    using 0 by auto
qed

lemma track_random_bits_lub_rai:
  assumes "Complete_Partial_Order.chain ord_rai A"
  assumes "\<And>r. r \<in> A \<Longrightarrow> wf_random r"
  shows "track_random_bits (lub_rai A) = lub_rai (track_random_bits ` A)" (is "?L = ?R")
proof -
  have 0:"Complete_Partial_Order.chain ord_rai (track_random_bits ` A)"
    by (intro chain_imageI[OF assms(1)] track_random_bits_mono assms(2))

  have "?L bs = ?R bs" if "?L bs \<noteq> None" for bs
  proof -
    have 1:"lub_rai A bs \<noteq> None" using that track_random_bits_Some_iff by simp
    have "lub_rai A bs = None" if "\<And>f. f \<in> A \<Longrightarrow> f bs = None"
      using that unfolding lub_rai_def fun_lub_def flat_lub_def by auto
    then obtain f where f_in_A: "f \<in> A" and "f bs \<noteq> None"
      using 1 by blast
    hence "consumed_prefix f bs \<noteq> None"
      using consumed_prefix_none_iff[OF assms(2)[OF f_in_A]] by simp
    hence 2:"track_random_bits f bs \<noteq> None"
      unfolding track_random_bits_alt[OF assms(2)[OF f_in_A]] by simp
    have "ord_rai (track_random_bits f) (track_random_bits (lub_rai A))"
      by (intro track_random_bits_mono wf_lub[OF assms(1)] assms(2)
          random_alg_int_pd.lub_upper[OF assms(1)] f_in_A)
    hence "track_random_bits (lub_rai A) bs = track_random_bits f bs"
      using 2 unfolding ord_rai_def fun_ord_def flat_ord_def by metis

    moreover have "ord_rai (track_random_bits f) (lub_rai (track_random_bits ` A))"
      using f_in_A by (intro random_alg_int_pd.lub_upper[OF 0]) auto
    hence "lub_rai (track_random_bits ` A) bs = track_random_bits f bs"
      using 2 unfolding ord_rai_def fun_ord_def flat_ord_def by metis
    ultimately show ?thesis by simp
  qed
  hence "flat_ord None (?L bs) (?R bs)" for bs
    unfolding flat_ord_def by blast
  hence "ord_rai ?L ?R"
    unfolding ord_rai_def fun_ord_def by simp
  moreover have "ord_rai (track_random_bits f) (track_random_bits (lub_rai A))" if "f \<in> A" for f
    using that assms(2) wf_lub[OF assms(1,2)]
    by (intro track_random_bits_mono random_alg_int_pd.lub_upper[OF assms(1)])
  hence "ord_rai ?R ?L"
    by (intro random_alg_int_pd.lub_least 0) auto
  ultimately show ?thesis
    using random_alg_int_pd.leq_antisym by auto
qed

lemma untrack_random_bits:
  assumes "wf_random f"
  shows "track_random_bits f \<bind> (\<lambda>x. return_rai (fst x)) = f" (is "?L = ?R")
proof -
  have "?L bs = ?R bs" for bs
    unfolding track_random_bits_alt[OF assms] bind_rai_def return_rai_def
    by (subst wf_random_alt[OF assms]) (cases "consumed_prefix f bs", auto)
  thus ?thesis
    by auto
qed

lift_definition track_coin_use :: "'a random_alg \<Rightarrow> ('a \<times> nat) random_alg"
  is track_random_bits
  by (rule wf_track_random_bits)

definition bind_tra ::
  "('a \<times> nat) random_alg \<Rightarrow> ('a \<Rightarrow> ('b \<times> nat) random_alg) \<Rightarrow> ('b \<times> nat) random_alg"
  where "bind_tra m f = do {
    (r,k) \<leftarrow> m;
    (s,l) \<leftarrow> (f r);
    return_ra (s, k+l)
  }"

definition coin_tra :: "(bool \<times> nat) random_alg"
  where "coin_tra = do {
    b \<leftarrow> coin_ra;
    return_ra (b,1)
  }"

definition return_tra :: "'a \<Rightarrow> ('a \<times> nat) random_alg"
  where "return_tra x = return_ra (x,0)"

adhoc_overloading Monad_Syntax.bind bind_tra

text \<open>Monad laws:\<close>

lemma return_bind_tra:
  "bind_tra (return_tra x) g = g x"
  unfolding bind_tra_def return_tra_def
  by (simp add:bind_return_ra return_bind_ra)

lemma bind_tra_assoc:
  "bind_tra (bind_tra f g) h = bind_tra f (\<lambda>x. bind_tra (g x) h)"
  unfolding bind_tra_def
  by (simp add:bind_return_ra return_bind_ra bind_ra_assoc case_prod_beta' algebra_simps)

lemma bind_return_tra:
  "bind_tra m return_tra = m"
  unfolding bind_tra_def return_tra_def
  by (simp add:bind_return_ra return_bind_ra)

lemma track_coin_use_bind:
  fixes m :: "'a random_alg"
  fixes f :: "'a \<Rightarrow> 'b random_alg"
  shows "track_coin_use (m \<bind> f) = track_coin_use m \<bind> (\<lambda>r. track_coin_use (f r))"
    (is "?L = ?R")
proof -
  have "Rep_random_alg ?L = Rep_random_alg ?R"
    unfolding track_coin_use.rep_eq bind_ra.rep_eq bind_tra_def
    by (subst track_rb_bind) (simp_all add:wf_rep_rand_alg comp_def case_prod_beta'
        track_coin_use.rep_eq bind_ra.rep_eq return_ra.rep_eq)
  thus ?thesis
    using Rep_random_alg_inject by auto
qed

lemma track_coin_use_coin: "track_coin_use coin_ra = coin_tra" (is "?L = ?R")
  unfolding coin_tra_def using track_rb_coin[transferred] by metis

lemma track_coin_use_return: "track_coin_use (return_ra x) = return_tra x"  (is "?L = ?R")
  unfolding return_tra_def using track_rb_return[transferred] by metis

lemma track_coin_use_lub:
  assumes "Complete_Partial_Order.chain ord_ra A"
  shows "track_coin_use (lub_ra A) = lub_ra (track_coin_use ` A)" (is "?L = ?R")
proof -
  have 0: "Complete_Partial_Order.chain ord_rai (Rep_random_alg ` A)"
    using assms unfolding ord_ra.rep_eq Complete_Partial_Order.chain_def by auto

  have 2: "(Rep_random_alg ` track_coin_use ` A) = track_random_bits ` Rep_random_alg ` A"
    using track_coin_use.rep_eq unfolding image_image by auto

  have 1: "Complete_Partial_Order.chain ord_rai (Rep_random_alg ` track_coin_use ` A)"
    using wf_rep_rand_alg unfolding 2 by (intro chain_imageI[OF 0] track_random_bits_mono) auto

  have "Rep_random_alg ?L = track_random_bits (lub_rai (Rep_random_alg ` A))"
    using 0 unfolding track_coin_use.rep_eq lub_ra.rep_eq by simp
  also have "... = lub_rai (track_random_bits ` Rep_random_alg ` A)"
    using wf_rep_rand_alg by (intro track_random_bits_lub_rai 0) auto
  also have "... = Rep_random_alg ?R"
    using 1 unfolding lub_ra.rep_eq 2 by simp
  finally have "Rep_random_alg ?L = Rep_random_alg ?R"
    by simp
  thus ?thesis
    using Rep_random_alg_inject by auto
qed

lemma track_coin_use_mono:
  assumes "ord_ra f g"
  shows "ord_ra (track_coin_use f) (track_coin_use g)"
  using assms by transfer (rule track_random_bits_mono)

lemma bind_mono_tra_aux:
  assumes "ord_ra f1 f2" "\<And>y. ord_ra (g1 y) (g2 y)"
  shows "ord_ra (bind_tra f1 g1) (bind_tra f2 g2)"
  using assms unfolding bind_tra_def ord_ra.rep_eq bind_ra.rep_eq
  by (auto intro!:bind_rai_mono random_alg_int_pd.leq_refl
      simp:comp_def bind_ra.rep_eq case_prod_beta' return_ra.rep_eq)

lemma bind_tra_mono [partial_function_mono]:
  assumes "mono_ra B" and "\<And>y. mono_ra (C y)"
  shows "mono_ra (\<lambda>f. bind_tra (B f) (\<lambda>y. C y f))"
  using assms by (intro monotoneI bind_mono_tra_aux) (auto simp:monotone_def)

lemma track_coin_use_empty:
  "track_coin_use (lub_ra {}) = (lub_ra {})" (is "?L = ?R")
proof -
  have "?L = lub_ra (track_coin_use ` {})"
    by (intro track_coin_use_lub) (simp add:Complete_Partial_Order.chain_def)
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

lemma untrack_coin_use:
  "map_ra fst (track_coin_use f) = f" (is "?L = ?R")
proof -
  have "Rep_random_alg ?L = Rep_random_alg ?R"
    unfolding map_ra_def bind_ra.rep_eq track_coin_use.rep_eq comp_def return_ra.rep_eq
    by (auto intro!:untrack_random_bits simp:wf_rep_rand_alg)
  thus ?thesis
    using Rep_random_alg_inject by auto
qed

definition rel_track_coin_use :: "('a \<times> nat) random_alg \<Rightarrow> 'a random_alg \<Rightarrow> bool" where
  "rel_track_coin_use q p \<longleftrightarrow> q = track_coin_use p"

lemma admissible_rel_track_coin_use:
  "ccpo.admissible (prod_lub lub_ra lub_ra) (rel_prod ord_ra ord_ra) (case_prod rel_track_coin_use)"
  (is "ccpo.admissible ?lub ?ord ?P")
proof (rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_track_coin_use p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_track_coin_use p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_ra) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain (ord_ra) (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto

  have "lub_ra (fst ` Y) = lub_ra (track_coin_use ` snd ` Y)"
    unfolding image_image using R
    by (intro arg_cong[of _ _ lub_ra] image_cong) (auto simp: rel_track_coin_use_def)
  also have "\<dots> = track_coin_use (lub_ra (snd ` Y))"
    by (intro track_coin_use_lub[symmetric] chain2)
  finally have "rel_track_coin_use (lub_ra (fst ` Y)) (lub_ra (snd ` Y))"
    unfolding rel_track_coin_use_def .
  then show "?P (?lub Y)"
    by (simp add: prod_lub_def)
qed

lemma admissible_rel_track_coin_use_cont [cont_intro]:
  fixes ord
  shows "\<lbrakk> mcont lub ord lub_ra ord_ra f; mcont lub ord lub_ra ord_ra g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_track_coin_use (f x) (g x))"
  by (rule admissible_subst[OF admissible_rel_track_coin_use, where f="\<lambda>x. (f x, g x)", simplified])
     (rule mcont_Pair)

lemma mcont_track_coin_use:
  "mcont lub_ra ord_ra lub_ra ord_ra track_coin_use"
  unfolding mcont_def monotone_def cont_def
  by (auto simp: track_coin_use_mono track_coin_use_lub)

lemmas mcont2mcont_track_coin_use = mcont_track_coin_use[THEN random_alg_pf.mcont2mcont]

context includes lifting_syntax
begin

lemma fixp_track_coin_use_parametric[transfer_rule]:
  assumes f: "\<And>x. mono_ra (\<lambda>f. F f x)"
  and g: "\<And>x. mono_ra (\<lambda>f. G f x)"
  and param: "((A ===> rel_track_coin_use) ===> A ===> rel_track_coin_use) F G"
  shows "(A ===> rel_track_coin_use) (random_alg_pf.fixp_fun F) (random_alg_pf.fixp_fun G)"
  using f g
proof(rule parallel_fixp_induct_1_1[OF
      random_alg_pfd random_alg_pfd _ _ reflexive reflexive,
        where P="(A ===> rel_track_coin_use)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_ra) (fun_lub lub_ra))
        (rel_prod (fun_ord ord_ra) (fun_ord ord_ra))
        (\<lambda>x. (A ===> rel_track_coin_use) (fst x) (snd x))"
    unfolding rel_fun_def
    by(rule admissible_all admissible_imp cont_intro)+
  have 0:"track_coin_use (lub_ra {}) = lub_ra {}"
    using track_coin_use_lub[where A="{}"]
    by (simp add:Complete_Partial_Order.chain_def)
  show "(A ===> rel_track_coin_use) (\<lambda>_. lub_ra {}) (\<lambda>_. lub_ra {})"
    by (auto simp: rel_fun_def rel_track_coin_use_def 0)
  show "(A ===> rel_track_coin_use) (F f) (G g)" if "(A ===> rel_track_coin_use) f g" for f g
    using that by(rule rel_funD[OF param])
qed

lemma return_ra_tranfer[transfer_rule]: "((=) ===> rel_track_coin_use) return_tra return_ra"
  unfolding rel_fun_def rel_track_coin_use_def track_coin_use_return by simp

lemma bind_ra_tranfer[transfer_rule]:
  "(rel_track_coin_use ===> ((=) ===> rel_track_coin_use) ===> rel_track_coin_use) bind_tra bind_ra"
  unfolding rel_fun_def rel_track_coin_use_def track_coin_use_bind by simp presburger

lemma coin_ra_tranfer[transfer_rule]:
  "rel_track_coin_use coin_tra coin_ra"
  unfolding rel_fun_def rel_track_coin_use_def track_coin_use_coin by simp

end

end