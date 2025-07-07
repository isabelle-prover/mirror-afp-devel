(*  Title:       Computational p-Adics: Compactness of Local Rings of p-Adic Integers
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)


theory More_pAdic_Product

imports Fin_Field_Product

begin


section \<open>Compactness of local ring of integers\<close>

subsection \<open>Preliminaries\<close>

lemma infinite_vimageE:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "infinite (UNIV :: 'a set)" and "range f \<subseteq> B" and "finite B"
  obtains b where "b \<in> B" and "infinite (f -` {b})"
proof-
  from assms(2) have "f -` B = UNIV" using subsetD rangeI by blast
  with assms(1,3) have "\<not> (\<forall>b\<in>B. finite (f -` {b}))"
    using finite_UN[of B "\<lambda>b. f -` {b}"] vimage_eq_UN[of f B] by argo
  from this obtain b where "b \<in> B" and "infinite (f -` {b})" by blast
  with that show ?thesis by fast
qed


\<comment> \<open>
  This is used to create a subsequence with outputs restricted to a specific image subset.
\<close>
primrec subset_subseq ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> nat"
  where
    "subset_subseq f A 0 = (LEAST k. f k \<in> A)" |
    "subset_subseq f A (Suc n) = (LEAST k. k > subset_subseq f A n \<and> f k \<in> A)"

lemma
  assumes "infinite (f -` A)"
  shows subset_subseq_strict_mono: "strict_mono (subset_subseq f A)"
    and subset_subseq_range      : "f (subset_subseq f A n) \<in> A"
proof-
  from assms have "f -` A \<noteq> {}" by auto
  hence "\<exists>k. f k \<in> A" by blast
  hence ex_first:
    "\<exists>!k. f k \<in> A \<and> (\<forall>j. f j \<in> A \<longrightarrow> k \<le> j)"
    using ex_ex1_least_nat_le by simp
  define P where "P \<equiv> \<lambda>N k. k > N \<and> f k \<in> A"
  have "\<And>N. (f -` A) \<inter> {N<..} \<noteq> {}"
  proof
    fix N assume "(f -` A) \<inter> {N<..} = {}"
    hence "(f -` A) \<subseteq> {..N}" by fastforce
    with assms show False using finite_subset by fast
  qed
  with P_def have "\<And>N. \<exists>k. P N k" by fast
  hence ex_next:
    "\<And>N. \<exists>!k. P N k \<and> (\<forall>j. P N j \<longrightarrow> k \<le> j)"
    using ex_ex1_least_nat_le by force

  from P_def show "f (subset_subseq f A n) \<in> A"
    using Least1I[OF ex_first] Least1I[OF ex_next] by (cases n) auto

  from P_def have step: "\<And>n. subset_subseq f A (Suc n) > subset_subseq f A n"
    using Least1I[OF ex_next] by auto

  show "strict_mono (subset_subseq f A)"
  proof
    fix m n show "m < n \<Longrightarrow> subset_subseq f A m < subset_subseq f A n"
    proof (induct n)
      case (Suc n) thus ?case using step[of n] by (cases "n = m") simp_all
    qed simp
  qed

qed


subsection \<open>Sequential compactness\<close>

subsubsection \<open>Creating a Cauchy subsequence\<close>

abbreviation
  "p_adic_prod_int_convergent_subseq_seq_step p X g n \<equiv>
    \<lambda>k. p_adic_prod_int_quot (p_adic_prod_shift_p_depth p (- int n) ((X (g k) - X (g 0))))"

primrec p_adic_prod_int_convergent_subseq_seq ::
  "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow>
    (nat \<Rightarrow> 'a p_adic_prod) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat)"
  where "p_adic_prod_int_convergent_subseq_seq p X 0 = id" |
  "p_adic_prod_int_convergent_subseq_seq p X (Suc n) =
    p_adic_prod_int_convergent_subseq_seq p X n \<circ>
      subset_subseq
        (
          p_adic_prod_int_convergent_subseq_seq_step p X (
            p_adic_prod_int_convergent_subseq_seq p X n
          ) n
        )
        {SOME z.
          infinite (
            p_adic_prod_int_convergent_subseq_seq_step p X (
              p_adic_prod_int_convergent_subseq_seq p X n
            ) n
            -` {z}
          )
        }"

abbreviation
  "p_adic_prod_int_convergent_subseq p X n \<equiv>
    p_adic_prod_int_convergent_subseq_seq p X n n"

lemma restricted_X_infinite_quot_vimage:
  "\<exists>z. infinite ((\<lambda>k. p_adic_prod_int_quot (X k)) -` {z})"
  if  fin_p_quot  : "finite (range (\<lambda>x::'a adelic_int_quot. x prestrict ((=) p)))"
  and range_X     : "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
  and restricted_X: "\<forall>n. X n = (X n) prestrict ((=) p)"
  for p :: "'a::nontrivial_factorial_idom prime" and X :: "nat \<Rightarrow> 'a p_adic_prod"
proof-
  define resp where "resp \<equiv> \<lambda>x::'a adelic_int_quot. x prestrict ((=) p)"
  define X_quot where "X_quot \<equiv> \<lambda>k. p_adic_prod_int_quot (X k)"
  have "range X_quot \<subseteq> range resp"
  proof safe
    fix k
    from range_X restricted_X X_quot_def resp_def have
      "X_quot k = resp (adelic_int_quot (Abs_adelic_int (X k)))"
      using p_restrict_adelic_int_abs_eq p_restrict_adelic_int_quot_abs_eq rangeI subsetD by metis
    thus "X_quot k \<in> range resp" by simp
  qed
  with fin_p_quot resp_def obtain b where "b \<in> range resp" and "infinite (X_quot -` {b})"
    using infinite_vimageE by blast
  with X_quot_def show ?thesis by fast
qed

context
  fixes p       :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
    and X       :: "nat \<Rightarrow> 'a p_adic_prod"
    and ss      :: "nat \<Rightarrow> (nat \<Rightarrow> nat)"
    and ss_step :: "nat \<Rightarrow> (nat \<Rightarrow> 'a adelic_int_quot)"
    and nth_im  :: "nat \<Rightarrow> 'a adelic_int_quot"
    and subss   :: "nat \<Rightarrow> (nat \<Rightarrow> nat)"
  defines
    "ss \<equiv> p_adic_prod_int_convergent_subseq_seq p X"
    and
    "ss_step \<equiv> \<lambda>n. p_adic_prod_int_convergent_subseq_seq_step p X (ss n) n"
    and "nth_im \<equiv> \<lambda>n. (SOME z. infinite (ss_step n -` {z}))"
    and "subss  \<equiv> \<lambda>n. subset_subseq (ss_step n) {nth_im n}"
  assumes fin_p_quot  : "finite (range (\<lambda>x::'a adelic_int_quot. x prestrict ((=) p)))"
    and   range_X     : "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
    and   restricted_X: "\<forall>n. X n = (X n) prestrict ((=) p)"
begin

lemma p_adic_prod_int_convergent_subseq_seq_step_infinite_quot_vimage:
    "\<exists>z. infinite (ss_step n -` {z})" (is ?A)
  and p_adic_prod_int_convergent_subseq_seq_step_depth:
    "\<forall>k. (X (ss n k)) \<not>\<simeq>\<^sub>p (X (ss n 0)) \<longrightarrow>
      ((X (ss n k) - X (ss n 0))\<degree>\<^sup>p) \<ge> int n"
    (is ?B)
proof-
  have "?A \<and> ?B"
  proof (induct n)
    case 0
    from range_X have "range (\<lambda>k. X k - X 0) \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
      using global_p_depth_p_adic_prod.global_depth_set_minus by fastforce
    moreover from restricted_X have
      "\<forall>k. X k - X 0 = (X k - X 0) prestrict (=) p"
      using global_p_depth_p_adic_prod.p_restrict_minus by metis
    ultimately
      have  A: "\<exists>z. infinite ((\<lambda>k. p_adic_prod_int_quot (X k - X 0)) -` {z})"
      using fin_p_quot restricted_X_infinite_quot_vimage
      by    blast
    from ss_def range_X have B:
      "\<forall>k. (X (ss 0 k)) \<not>\<simeq>\<^sub>p (X (ss 0 0)) \<longrightarrow>
        int 0 \<le> ((X (ss 0 k) - X (ss 0 0))\<degree>\<^sup>p)"
      using global_p_depth_p_adic_prod.global_depth_set_minus
            p_equality_p_adic_prod.conv_0 global_p_depth_p_adic_prod.global_depth_setD
      by    fastforce
    with ss_step_def ss_def show
      "(\<exists>z. infinite (ss_step 0 -` {z})) \<and>
        (\<forall>k. (X (ss 0 k)) \<not>\<simeq>\<^sub>p (X (ss 0 0)) \<longrightarrow>
          int 0 \<le> ((X (ss 0 k) - X (ss 0 0))\<degree>\<^sup>p))"
      using A B by simp
  next
    case (Suc n)
    hence inf  : "\<exists>z. infinite (ss_step n -` {z})"
      and depth:
        "\<And>k. (X (ss n k)) \<not>\<simeq>\<^sub>p (X (ss n 0)) \<Longrightarrow>
          int n \<le> ((X (ss n k) - X (ss n 0))\<degree>\<^sup>p)"
      by auto
    from nth_im_def have inf_nth_vimage: "infinite (ss_step n -` {nth_im n})"
      using someI_ex[OF inf] by blast
    from subss_def have ss_step_kth: "\<forall>k. ss_step n (subss n k) = nth_im n"
      using subset_subseq_range[OF inf_nth_vimage] by blast
    have
      "\<And>k.
        p_adic_prod_shift_p_depth p (- int n) ((X (ss n k) - X (ss n 0)) prestrict ((=) p))
          \<in> \<O>\<^sub>\<forall>\<^sub>p"
      using p_adic_prod_depth_embeds.shift_p_depth_p_restrict_global_depth_set_memI
            depth p_equality_p_adic_prod.conv_0
      by    fastforce
    with restricted_X have depth_set:
      "\<And>k.
        p_adic_prod_shift_p_depth p (- int n) (X (ss n k) - X (ss n 0))
          \<in> \<O>\<^sub>\<forall>\<^sub>p"
      using global_p_depth_p_adic_prod.p_restrict_minus by metis

    have B:
      "\<forall>k. (X (ss (Suc n) k)) \<not>\<simeq>\<^sub>p (X (ss (Suc n) 0)) \<longrightarrow>
        ((X (ss (Suc n) k) - X (ss (Suc n) 0))\<degree>\<^sup>p) \<ge> int (Suc n)"
    proof clarify
      fix k assume k: "(X (ss (Suc n) k)) \<not>\<simeq>\<^sub>p (X (ss (Suc n) 0))"
      from ss_def ss_step_def subss_def nth_im_def
        have  X_Suc_n_k: "X (ss (Suc n) k) = X (ss n (subss n k))"
        and   X_Suc_n_0: "X (ss (Suc n) 0) = X (ss n (subss n 0))"
        by    auto
      from ss_step_def have
        "p_adic_prod_shift_p_depth p (- int n) (X (ss (Suc n) 0) - X (ss (Suc n) k))
          \<in> \<P>\<^sub>\<forall>\<^sub>p"
        using depth_set X_Suc_n_k X_Suc_n_0 ss_step_kth p_adic_prod_int_quot_eq_iff
              p_adic_prod_depth_embeds.shift_p_depth_minus
        by    fastforce
      with k show "((X (ss (Suc n) k) - X (ss (Suc n) 0))\<degree>\<^sup>p) \<ge> int (Suc n)"
        using p_adic_prod_depth_embeds.shift_p_depth_mem_global_depth_set
              p_equality_p_adic_prod.sym[of p] global_p_depth_p_adic_prod.depth_diff[of p]
              p_equality_p_adic_prod.conv_0[of p "X (ss (Suc n) 0)"]
        by    fastforce
    qed
    from ss_step_def ss_def have ss_step_Suc_n:
      "ss_step (Suc n) = (\<lambda>k.
        p_adic_prod_int_quot (
          p_adic_prod_shift_p_depth p (- int (Suc n)) ((X (ss (Suc n) k) - X (ss (Suc n) 0)))
        )
      )"
      by presburger
    moreover have
      "\<exists>z. infinite (
        (\<lambda>k.
          p_adic_prod_int_quot (
            p_adic_prod_shift_p_depth p (-int (Suc n)) ((X (ss (Suc n) k) - X (ss (Suc n) 0)))
          )
        ) -` {z}
      )"
    proof (intro restricted_X_infinite_quot_vimage, rule fin_p_quot, safe)
      fix k
      have
        "p_adic_prod_shift_p_depth p (- int (Suc n)) (
            (X (ss (Suc n) k) - X (ss (Suc n) 0)) prestrict ((=) p)
        ) \<in> \<O>\<^sub>\<forall>\<^sub>p"
        using B p_adic_prod_depth_embeds.shift_p_depth_p_restrict_global_depth_set_memI
              p_equality_p_adic_prod.conv_0
        by    fastforce
      with restricted_X show
        "p_adic_prod_shift_p_depth p (- int (Suc n)) (X (ss (Suc n) k) - X (ss (Suc n) 0))
          \<in> \<O>\<^sub>\<forall>\<^sub>p"
        using global_p_depth_p_adic_prod.p_restrict_minus by metis
      from restricted_X show
          "p_adic_prod_shift_p_depth p (- int (Suc n)) (X (ss (Suc n) k) - X (ss (Suc n) 0)) =
            p_adic_prod_shift_p_depth p (- int (Suc n)) (
              X (ss (Suc n) k) - X (ss (Suc n) 0)
            ) prestrict (=) p"
          using p_adic_prod_depth_embeds.shift_p_depth_p_restrict
                global_p_depth_p_adic_prod.p_restrict_minus
          by    metis
    qed
    ultimately have A: "\<exists>z. infinite (ss_step (Suc n) -` {z})" by presburger
    show
      "(\<exists>z. infinite (ss_step (Suc n) -` {z})) \<and>
        (\<forall>k. (X (ss (Suc n) k)) \<not>\<simeq>\<^sub>p (X (ss (Suc n) 0)) \<longrightarrow>
             int (Suc n) \<le> ((X (ss (Suc n) k) - X (ss (Suc n) 0))\<degree>\<^sup>p))"
        using A B by blast
  qed
  thus ?A and ?B by auto
qed

lemma p_adic_prod_int_convergent_subset_subseq_strict_mono:
  "strict_mono (subset_subseq (ss_step n) {nth_im n})"
  using ss_step_def nth_im_def p_adic_prod_int_convergent_subseq_seq_step_infinite_quot_vimage
        subset_subseq_strict_mono someI_ex
  by    fast

lemma p_adic_prod_int_convergent_subseq_strict_mono': "strict_mono (ss n)"
proof (induct n)
  case (Suc n) from ss_def ss_step_def nth_im_def show "strict_mono (ss (Suc n))"
    using ss_def ss_step_def nth_im_def strict_monoD[OF Suc]
          strict_monoD[OF p_adic_prod_int_convergent_subset_subseq_strict_mono]
    by    (force intro: strict_mono_onI)
qed (simp add: ss_def strict_mono_id flip: id_def)

lemma p_adic_prod_int_convergent_subseq_strict_mono:
  "strict_mono (p_adic_prod_int_convergent_subseq p X)"
proof (rule iffD2, rule strict_mono_Suc_iff, clarify)
  fix n :: nat
  have "Suc n \<le> subset_subseq (ss_step n) {nth_im n} (Suc n)"
    using strict_mono_imp_increasing p_adic_prod_int_convergent_subset_subseq_strict_mono by fast
  hence "n < subset_subseq (ss_step n) {nth_im n} (Suc n)" by linarith
  with ss_def ss_step_def nth_im_def
    show  "p_adic_prod_int_convergent_subseq p X n < p_adic_prod_int_convergent_subseq p X (Suc n)"
    using ss_def strict_monoD p_adic_prod_int_convergent_subseq_strict_mono'
    by    auto
qed

lemma p_adic_prod_int_convergent_subseq_Cauchy:
  "p_adic_prod_p_cauchy p (X \<circ> p_adic_prod_int_convergent_subseq p X)"
proof (rule iffD2, rule global_p_depth_p_adic_prod.p_consec_cauchy, clarify)
  fix n
  define C where "C \<equiv> X \<circ> p_adic_prod_int_convergent_subseq p X"
  have
    "global_p_depth_p_adic_prod.p_consec_cauchy_condition p C n (nat (n + 1))"
    unfolding global_p_depth_p_adic_prod.p_consec_cauchy_condition_def
  proof clarify
    fix k :: nat
    assume k: "k \<ge> nat (n + 1)" "(C (Suc k)) \<not>\<simeq>\<^sub>p (C k)"
    define D0 D1 D2
      where "D0 \<equiv> C (Suc k) - C k"
      and   "D1 \<equiv> X (ss k (subss k (Suc k))) - X (ss k 0)"
      and   "D2 \<equiv> X (ss k k) - X (ss k 0)"
    with C_def ss_def ss_step_def subss_def nth_im_def have D0_eq: "D0 = D1 - D2"
      by (force simp add: algebra_simps)
    from k(2) D0_def have D0_nequiv0: "D0 \<not>\<simeq>\<^sub>p 0"
      using p_equality_p_adic_prod.conv_0 by fast
    consider  (D1) "D1 \<simeq>\<^sub>p 0" | (D2) "D2 \<simeq>\<^sub>p 0" |
              (neither) "D1 \<not>\<simeq>\<^sub>p 0" "D2 \<not>\<simeq>\<^sub>p 0"
      by blast
    thus "(D0\<degree>\<^sup>p) > n"
    proof cases
      case D1
      moreover from this have "D2 \<not>\<simeq>\<^sub>p 0"
        using D0_eq D0_nequiv0 p_equality_p_adic_prod.minus by fastforce
      ultimately show ?thesis
        using k(1) D2_def D0_eq global_p_depth_p_adic_prod.depth_diff_equiv0_left
              p_equality_p_adic_prod.conv_0 p_adic_prod_int_convergent_subseq_seq_step_depth
        by    fastforce
    next
      case D2
      moreover from this have "D1 \<not>\<simeq>\<^sub>p 0"
        using D0_eq D0_nequiv0 p_equality_p_adic_prod.minus by fastforce
      ultimately show ?thesis
        using k(1) D1_def D0_eq global_p_depth_p_adic_prod.depth_diff_equiv0_right
              p_equality_p_adic_prod.conv_0 p_adic_prod_int_convergent_subseq_seq_step_depth
        by    fastforce
    next
      case neither
      moreover from this D1_def D2_def
        have  "k \<le> min (D1\<degree>\<^sup>p) (D2\<degree>\<^sup>p)"
        using p_equality_p_adic_prod.conv_0 p_adic_prod_int_convergent_subseq_seq_step_depth
        by    fastforce
      ultimately show ?thesis
        using k(1) D0_eq D0_nequiv0 global_p_depth_p_adic_prod.depth_nonarch_diff by fastforce
    qed
  qed
  thus "\<exists>K. global_p_depth_p_adic_prod.p_consec_cauchy_condition p C n K" by blast
qed

lemma p_adic_prod_int_convergent_subseq_limseq:
  "x \<in> (\<lambda>z. z prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p"
  if "p_adic_prod_p_open_nbhds_limseq (X \<circ> g) x"
proof (intro image_eqI global_p_depth_p_adic_prod.global_imp_eq, standard)
  fix q :: "'a prime"
  show "x \<simeq>\<^sub>q x prestrict ((=) p)"
  proof (cases "q = p")
    case False
    moreover from that have "p_adic_prod_p_limseq q (X \<circ> g) x"
      using global_p_depth_p_adic_prod.globally_limseq_imp_locally_limseq by fast
    moreover from restricted_X have "\<forall>n. (X \<circ> g) n = (X \<circ> g) n prestrict (=) p"
      by force
    ultimately show "x \<simeq>\<^sub>q (x prestrict ((=) p))"
      using global_p_depth_p_adic_prod.p_restrict_equiv0
            global_p_depth_p_adic_prod.p_limseq_p_constant
            global_p_depth_p_adic_prod.p_limseq_unique p_equality_p_adic_prod.trans_left[of q x 0]
      by (metis (full_types))
  qed (simp add: global_p_depth_p_adic_prod.p_restrict_equiv[symmetric])
  from that range_X show "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using eventually_sequentially
          global_p_depth_p_adic_prod.global_depth_set_p_open_nbhds_LIMSEQ_closed
    by    force
qed

end (* context finite p-quotient *)

subsubsection \<open>Proving sequential compactness\<close>

context
  fixes p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  assumes fin_p_quot: "finite (range (\<lambda>x::'a adelic_int_quot. x prestrict ((=) p)))"
begin

lemma p_adic_prod_local_int_ring_seq_compact':
  "\<exists>g::nat\<Rightarrow>nat. strict_mono g \<and> p_adic_prod_p_cauchy p (X \<circ> g)"
  if range_X:
    "range X \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
  for X :: "nat \<Rightarrow> 'a p_adic_prod"
proof-
  define g where "g \<equiv> p_adic_prod_int_convergent_subseq p X"
  from range_X have "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
    using global_p_depth_p_adic_prod.global_depth_set_closed_under_p_restrict_image by force
  moreover from range_X have "\<forall>n. X n = X n prestrict ((=) p)"
    using subsetD
          global_p_depth_p_adic_prod.p_restrict_image_restrict[of
            "X _" "(=) p" "\<O>\<^sub>\<forall>\<^sub>p"
          ]
    by    force
  ultimately have "strict_mono g" and "p_adic_prod_p_cauchy p (X \<circ> g)"
    using g_def fin_p_quot p_adic_prod_int_convergent_subseq_Cauchy[of p X]
          p_adic_prod_int_convergent_subseq_strict_mono
    by    (blast, presburger)
  thus ?thesis by blast
qed

lemma p_adic_prod_local_int_ring_seq_compact:
  "\<exists>x\<in>(\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p).
    \<exists>g::nat\<Rightarrow>nat.
      strict_mono g \<and> p_adic_prod_p_open_nbhds_limseq (X \<circ> g) x"
  if range_X:
    "range X \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
  for X :: "nat \<Rightarrow> 'a p_adic_prod"
proof-
  from range_X have 1: "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
    using global_p_depth_p_adic_prod.global_depth_set_closed_under_p_restrict_image by force
  moreover from range_X have 2: "\<forall>n. X n = X n prestrict ((=) p)"
    using subsetD
          global_p_depth_p_adic_prod.p_restrict_image_restrict[of
            "X _" "(=) p" "\<O>\<^sub>\<forall>\<^sub>p"
          ]
    by    force
  from range_X obtain g where g: "strict_mono g" "p_adic_prod_p_cauchy p (X \<circ> g)"
    using p_adic_prod_local_int_ring_seq_compact' by blast
  from g(2) obtain x
    where "p_adic_prod_p_open_nbhds_limseq (\<lambda>n. (X \<circ> g) n prestrict (=) p) x "
    using p_complete_p_adic_prod.p_cauchyE
    by    blast
  moreover have "(\<lambda>n. (X \<circ> g) n prestrict (=) p) = X \<circ> g" using 2 by auto
  ultimately have "p_adic_prod_p_open_nbhds_limseq (X \<circ> g) x" by auto
  moreover from this fin_p_quot
    have  "x \<in> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
    using 1 2 p_adic_prod_int_convergent_subseq_limseq
    by    blast
  ultimately show ?thesis using g(1) by blast
qed

lemma adelic_int_local_int_ring_seq_abs:
  "range X \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
  if  range_X: "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
  and range_abs_X:
    "range (\<lambda>k. Abs_adelic_int (X k)) \<subseteq> range (\<lambda>x. x prestrict ((=) p))"
  for X :: "nat \<Rightarrow> 'a p_adic_prod"
proof (standard, clarify, rule image_eqI)
  fix n
  from range_X show *: "X n \<in> \<O>\<^sub>\<forall>\<^sub>p" by fast
  from range_abs_X obtain y where "Abs_adelic_int (X n) = y prestrict ((=) p)" by blast
  from this obtain x
    where "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
    and   "Abs_adelic_int (X n) = Abs_adelic_int (x prestrict ((=) p))"
    using Abs_adelic_int_cases p_restrict_adelic_int_abs_eq
    by    metis
  thus "X n = X n prestrict ((=) p)"
    using * global_p_depth_p_adic_prod.global_depth_set_p_restrict Abs_adelic_int_inject
          global_p_depth_p_adic_prod.p_restrict_restrict'
    by    force
qed

lemma adelic_int_local_int_ring_seq_compact':
  "\<exists>g::nat\<Rightarrow>nat. strict_mono g \<and> adelic_int_p_cauchy p (X \<circ> g)"
  if range_X:
    "range X \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
  for X :: "nat \<Rightarrow> 'a adelic_int"
proof (cases X rule : adelic_int_seq_cases)
  case (Abs_adelic_int F)
  with range_X
    have  "range F \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
    using adelic_int_local_int_ring_seq_abs
    by    fast
  with fin_p_quot obtain g where g: "strict_mono g" "p_adic_prod_p_cauchy p (F \<circ> g)"
    using p_adic_prod_local_int_ring_seq_compact' by blast
  moreover from Abs_adelic_int(1)
    have  "(\<lambda>n. Abs_adelic_int ((F \<circ> g) n)) = X \<circ> g"
    by    fastforce
  moreover from Abs_adelic_int(2)
    have "range (F \<circ> g) \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
    by    auto
  ultimately have "adelic_int_p_cauchy p (X \<circ> g)" using adelic_int_p_cauchy_abs_eq by metis
  with g(1) show ?thesis by blast
qed

lemma adelic_int_local_int_ring_seq_compact:
  "\<exists>x\<in>range (\<lambda>x. x prestrict ((=) p)).
    \<exists>g::nat\<Rightarrow>nat.
      strict_mono g \<and> adelic_int_p_open_nbhds_limseq (X \<circ> g) x"
  if range_X:
    "range X \<subseteq> range (\<lambda>x. x prestrict ((=) p))"
  for X :: "nat \<Rightarrow> 'a adelic_int"
proof (cases X rule : adelic_int_seq_cases)
  case (Abs_adelic_int F)
  with range_X
    have  "range F \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
    using adelic_int_local_int_ring_seq_abs
    by    fast
  with fin_p_quot obtain y g
    where y  : "y \<in> (\<lambda>x. x prestrict (=) p) ` \<O>\<^sub>\<forall>\<^sub>p"
      and g  : "strict_mono g"
      and g_y: "p_adic_prod_p_open_nbhds_limseq (F \<circ> g) y"
    using p_adic_prod_local_int_ring_seq_compact by blast
  from y have "y \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using global_p_depth_p_adic_prod.global_depth_set_closed_under_p_restrict_image by auto
  moreover from Abs_adelic_int(2)
    have  "range (F \<circ> g) \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
    by    force
  ultimately have
    "adelic_int_p_open_nbhds_limseq
      (\<lambda>k. Abs_adelic_int ((F \<circ> g) k)) (Abs_adelic_int y)"
    using g_y adelic_int_p_open_nbhds_limseq_abs_eq
    by    blast
  moreover from Abs_adelic_int(1)
    have  "(\<lambda>k. Abs_adelic_int ((F \<circ> g) k)) = X \<circ> g"
    by    fastforce
  ultimately have lim: "adelic_int_p_open_nbhds_limseq (X \<circ> g) (Abs_adelic_int y)" by force
  from y obtain z where z: "z \<in> \<O>\<^sub>\<forall>\<^sub>p" "y = z prestrict (=) p" by fast
  hence "Abs_adelic_int y = Abs_adelic_int z prestrict (=) p"
    using p_restrict_adelic_int_abs_eq by fastforce
  with g show ?thesis using lim by blast
qed

end (* context fin_p_quot *)

lemma int_adic_prod_local_int_ring_seq_compact:
  "\<exists>x\<in>(\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p).
    \<exists>g::nat\<Rightarrow>nat.
      strict_mono g \<and> p_adic_prod_p_open_nbhds_limseq (X \<circ> g) x"
  if "range X \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` (\<O>\<^sub>\<forall>\<^sub>p)"
  for p :: "int prime"
  and X :: "nat \<Rightarrow> int p_adic_prod"
  using that p_adic_prod_local_int_ring_seq_compact finite_range_prestrict_single_int_prime
  by    blast

lemma int_adelic_int_local_int_ring_seq_compact:
  "\<exists>x\<in>range (\<lambda>x. x prestrict ((=) p)).
    \<exists>g::nat\<Rightarrow>nat.
      strict_mono g \<and> adelic_int_p_open_nbhds_limseq (X \<circ> g) x"
  if "range X \<subseteq> range (\<lambda>x. x prestrict ((=) p))"
  for p :: "int prime"
  and X :: "nat \<Rightarrow> int adelic_int"
  using that adelic_int_local_int_ring_seq_compact finite_range_prestrict_single_int_prime
  by    blast


subsection \<open>Finite-open-cover compactness\<close>

function exclusion_sequence ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow>
    'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "exclusion_sequence A f a 0 = a" |
  "exclusion_sequence A f a (Suc n) =
      (SOME x. x \<in> A \<and> x \<notin> (\<Union>k\<le>n. f (exclusion_sequence A f a k)))"
  by pat_completeness auto
termination by (relation "measure(\<lambda>(A,f,a,n). n)") auto

lemma
  assumes "\<not> A \<subseteq> (\<Union>k\<le>n. f (exclusion_sequence A f a k))"
  shows exclusion_sequence_mem: "exclusion_sequence A f a (Suc n) \<in> A"
    and exclusion_sequence_excludes:
      "exclusion_sequence A f a (Suc n) \<notin> (\<Union>k\<le>n. f (exclusion_sequence A f a k))"
proof-
  from assms have *:
    "\<exists>x. x \<in> A \<and> x \<notin> (\<Union>k\<le>n. f (exclusion_sequence A f a k))"
    by    blast
  show  "exclusion_sequence A f a (Suc n) \<in> A"
    and
    "exclusion_sequence A f a (Suc n) \<notin> (\<Union>k\<le>n. f (exclusion_sequence A f a k))"
    using someI_ex[OF *] by auto
qed

context
  fixes p      :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  assumes fin_p_quot: "finite (range (\<lambda>x::'a adelic_int_quot. x prestrict ((=) p)))"
begin

lemma p_adic_prod_local_int_ring_finite_cover:
  "\<exists>C. finite C \<and>
    C \<subseteq> (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<and>
    (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<subseteq>
      (\<Union>c\<in>C. p_adic_prod_p_open_nbhd p n c)"
  for C :: "'a set"
proof-
  define p_ring :: "'a p_adic_prod set"
    where "p_ring \<equiv> (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p"
  have
    "\<not> (\<forall>C\<subseteq>p_ring.
      p_ring \<subseteq> (\<Union>c\<in>C. p_adic_prod_p_open_nbhd p n c) \<longrightarrow>
      infinite C
    )"
  proof (safe)
    assume n:
      "\<forall>C\<subseteq>p_ring.
        p_ring \<subseteq> \<Union> (p_adic_prod_p_open_nbhd p n ` C) \<longrightarrow> infinite C"
    define X where
      "X \<equiv>
        \<lambda>k. exclusion_sequence p_ring (p_adic_prod_p_open_nbhd p n) (0::'a p_adic_prod) k"
    have partial_dn_cover:
      "\<forall>k. X ` {..k} \<subseteq> p_ring \<longrightarrow>
        \<not> p_ring \<subseteq> (\<Union>j\<le>k. p_adic_prod_p_open_nbhd p n (X j))"
    proof clarify
      fix k
      assume  "X ` {..k} \<subseteq> p_ring"
        and   "p_ring \<subseteq> (\<Union>j\<le>k. p_adic_prod_p_open_nbhd p n (X j))"
      with n have "infinite (X ` {..k})" by auto
      thus False by blast
    qed
    moreover have partial_range_X: "\<forall>k. X ` {..k} \<subseteq> p_ring"
    proof
      fix k show "X ` {..k} \<subseteq> p_ring"
      proof (induct k)
        case 0 from X_def p_ring_def show ?case
          using global_p_depth_p_adic_prod.global_depth_set_0
                global_p_depth_p_adic_prod.p_restrict_zero
          by    fastforce
      next
        case (Suc k)
        hence "\<not> p_ring \<subseteq> (\<Union>j\<le>k. p_adic_prod_p_open_nbhd p n (X j))"
          using partial_dn_cover by blast
        with X_def have "X (Suc k) \<in> p_ring" using exclusion_sequence_mem by force
        moreover have "{..Suc k} = insert (Suc k) {..k}" by auto
        ultimately show ?case using Suc by auto
      qed
    qed
    ultimately
      have dn_cover:
        "\<forall>k. \<not> p_ring \<subseteq> (\<Union>j\<le>k. p_adic_prod_p_open_nbhd p n (X j))"
      and range_X: "range X \<subseteq> p_ring"
      by  (fastforce, fast)
    from p_ring_def fin_p_quot obtain g
      where g: "strict_mono g" "p_adic_prod_p_cauchy p (X \<circ> g)"
      using range_X p_adic_prod_local_int_ring_seq_compact'
      by    metis
    from this obtain K where K: "p_adic_prod_p_cauchy_condition p (X \<circ> g) n K" by fast
    have "X (g (Suc K)) \<notin> p_adic_prod_p_open_nbhd p n (X (g K))"
    proof
      assume "X (g (Suc K)) \<in> p_adic_prod_p_open_nbhd p n (X (g K))"
      moreover from g(1) have g_K: "g K < g (Suc K)" using strict_monoD by blast
      ultimately have
        "X (g (Suc K)) \<in> (\<Union>j\<le>g (Suc K) - 1. p_adic_prod_p_open_nbhd p n (X j))"
        by force
      with X_def show False
        using g_K dn_cover
              exclusion_sequence_excludes[of p_ring "p_adic_prod_p_open_nbhd p n" 0 "g (Suc K) - 1"]
        by    simp
    qed
    hence "(X (g (Suc K))) \<not>\<simeq>\<^sub>p (X (g K))"
      and "((X (g (Suc K)) - X (g K))\<degree>\<^sup>p) < n"
      using global_p_depth_p_adic_prod.p_open_nbhd_eq_circle
      by    (blast, fastforce)
    with K show False
      using global_p_depth_p_adic_prod.p_cauchy_conditionD[of p "X \<circ> g" n K "Suc K" K] by auto
  qed
  thus ?thesis using p_ring_def by fast
qed

lemma p_adic_prod_local_int_ring_lebesgue_number:
  "\<exists>d. \<forall>x\<in>(\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p.
    \<exists>A\<in>\<A>. p_adic_prod_p_open_nbhd p d x \<subseteq> A"
  if  cover:
    "(\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<subseteq> \<Union> \<A>"
  and by_opens:
    "\<forall>A\<in>\<A>. generate_topology (p_adic_prod_local_p_open_nbhds p) A"
proof-
  define p_ring :: "'a p_adic_prod set"
    where "p_ring \<equiv> (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p"
  have
    "\<not> (\<forall>d. \<exists>x\<in>p_ring. \<forall>A\<in>\<A>.
      \<not> p_adic_prod_p_open_nbhd p d x \<subseteq> A)"
  proof
    assume *:
      "\<forall>d. \<exists>x\<in>p_ring. \<forall>A\<in>\<A>.
        \<not> p_adic_prod_p_open_nbhd p d x \<subseteq> A"
    define X where
      "X \<equiv> \<lambda>n. SOME x.
        x \<in> p_ring \<and>
        (\<forall>A\<in>\<A>. \<not> p_adic_prod_p_open_nbhd p (int n) x \<subseteq> A)"
    have range_X: "range X \<subseteq> p_ring"
    proof safe
      fix n
      from * have ex_x:
        "\<exists>x. x \<in> p_ring \<and>
          (\<forall>A\<in>\<A>. \<not> p_adic_prod_p_open_nbhd p (int n) x \<subseteq> A)"
        by force
      from X_def show "X n \<in> p_ring" using someI_ex[OF ex_x] by fast
    qed
    with fin_p_quot obtain a g
      where     g: "strict_mono g"
      and       a: "p_adic_prod_p_open_nbhds_limseq (X \<circ> g) a"
      using     p_adic_prod_local_int_ring_seq_compact
      unfolding X_def p_ring_def
      by        blast
    from range_X p_ring_def have "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
      using global_p_depth_p_adic_prod.global_depth_set_closed_under_p_restrict_image by force
    moreover from range_X p_ring_def have "\<forall>n. X n = X n prestrict ((=) p)"
      using subsetD
            global_p_depth_p_adic_prod.p_restrict_image_restrict[of
              "X _" "(=) p" "\<O>\<^sub>\<forall>\<^sub>p"
            ]
      by    force
    ultimately have "a \<in> p_ring"
      using p_ring_def fin_p_quot a p_adic_prod_int_convergent_subseq_limseq by blast
    with cover p_ring_def obtain A where A: "A \<in> \<A>" "a \<in> A" by blast
    with by_opens obtain n where n: "p_adic_prod_p_open_nbhd p n a \<subseteq> A"
      using global_p_depth_p_adic_prod.p_open_nbhds_open_subopen by blast
    from a have "p_adic_prod_p_limseq p (X \<circ> g) a"
      using global_p_depth_p_adic_prod.globally_limseq_imp_locally_limseq by fast
    from this obtain K where K: "p_adic_prod_p_limseq_condition p (X \<circ> g) a n K" by presburger
    define k where "k \<equiv> max (nat n) K"
    from * have ex_x:
      "\<exists>x. x \<in> p_ring \<and>
        (\<forall>A\<in>\<A>. \<not> p_adic_prod_p_open_nbhd p (int (g k)) x \<subseteq> A)"
      by force
    from X_def A(1)
      have  X_g_m: "\<not> p_adic_prod_p_open_nbhd p (int (g k)) (X (g k)) \<subseteq> A"
      using someI_ex[OF ex_x]
      by    fast
    moreover from g k_def have n_g_k: "n \<le> int (g k)"
      using strict_mono_imp_increasing[of g k] by linarith
    ultimately have "X (g k) \<not>\<simeq>\<^sub>p a"
      using n X_g_m global_p_depth_p_adic_prod.p_open_nbhd_eq_circle
            global_p_depth_p_adic_prod.p_open_nbhd_circle_multicentre
            global_p_depth_p_adic_prod.p_open_nbhd_antimono
      by    blast
    with K k_def have "X (g k) \<in> p_adic_prod_p_open_nbhd p n a"
      using global_p_depth_p_adic_prod.p_limseq_conditionD[of p _ a n K k]
            global_p_depth_p_adic_prod.p_open_nbhd_eq_circle
      by    force
    with n show False
      using n_g_k X_g_m global_p_depth_p_adic_prod.p_open_nbhd_circle_multicentre
            global_p_depth_p_adic_prod.p_open_nbhd_antimono
      by    fast
  qed
  thus ?thesis using p_ring_def by force
qed

lemma p_adic_prod_local_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<subseteq> \<Union> \<B>"
  if cover:
    "(\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<subseteq> \<Union> \<A>"
  and by_opens:
    "\<forall>A\<in>\<A>. generate_topology (p_adic_prod_local_p_open_nbhds p) A"
proof-
  define p_ring :: "'a p_adic_prod set"
    where "p_ring \<equiv> (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p"
  with cover by_opens obtain d where d:
    "\<forall>x\<in>p_ring. \<exists>A\<in>\<A>. p_adic_prod_p_open_nbhd p d x \<subseteq> A"
    using p_adic_prod_local_int_ring_lebesgue_number by presburger
  from p_ring_def obtain C where C:
    "finite C" "C \<subseteq> p_ring"
    "p_ring \<subseteq> (\<Union>c\<in>C. p_adic_prod_p_open_nbhd p d c)"
    using p_adic_prod_local_int_ring_finite_cover by metis
  define f where
    "f \<equiv> \<lambda>c. SOME A. A \<in> \<A> \<and> p_adic_prod_p_open_nbhd p d c \<subseteq> A"
  define \<B> where "\<B> \<equiv> f ` C"
  have "\<B> \<subseteq> \<A>"
    unfolding \<B>_def
  proof safe
    fix c assume "c \<in> C"
    with d C(2)
      have  ex_A: "\<exists>A. A \<in> \<A> \<and> p_adic_prod_p_open_nbhd p d c \<subseteq> A"
      by    blast
    from f_def show "f c \<in> \<A>" using someI_ex[OF ex_A] by blast
  qed
  moreover from \<B>_def C(1) have "finite \<B>" by simp
  moreover have "p_ring \<subseteq> \<Union> \<B>"
  proof
    fix x assume "x \<in> p_ring"
    with C(3) obtain c where c: "c \<in> C" "x \<in> p_adic_prod_p_open_nbhd p d c" by auto
    from d C(2) c(1)
      have  ex_A: "\<exists>A. A \<in> \<A> \<and> p_adic_prod_p_open_nbhd p d c \<subseteq> A"
      by    blast
    from f_def have "p_adic_prod_p_open_nbhd p d c \<subseteq> f c" using someI_ex[OF ex_A] by auto
    with \<B>_def c show "x \<in> \<Union> \<B>" by auto
  qed
  ultimately show ?thesis using p_ring_def by blast
qed

lemma p_adic_prod_local_scaled_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    (\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<B>"
  if cover:
    "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<A>"
  and by_opens:
    "\<forall>A\<in>\<A>. generate_topology (p_adic_prod_local_p_open_nbhds p) A"
  for \<A> :: "'a p_adic_prod set set"
proof-
  define p_ring p_depth_ring :: "'a p_adic_prod set"
    where "p_ring \<equiv> (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p"
    and
    "p_depth_ring \<equiv>
      (\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
  from p_ring_def p_depth_ring_def
    have  drop: "p_adic_prod_shift_p_depth p   n  `    p_ring    = p_depth_ring"
    and   lift: "p_adic_prod_shift_p_depth p (-n) ` p_depth_ring = p_ring"
    by    (simp_all add: p_adic_prod_depth_embeds.shift_p_depth_p_restrict_global_depth_set_image)
  define \<A>' where "\<A>' \<equiv> (`) (p_adic_prod_shift_p_depth p (-n)) ` \<A>"
  from cover p_depth_ring_def \<A>'_def have "p_ring \<subseteq> \<Union> \<A>'" using lift by blast
  moreover from by_opens have by_opens':
    "\<forall>A'\<in>\<A>'. generate_topology (p_adic_prod_local_p_open_nbhds p) A'"
    using p_adic_prod_depth_embeds.shift_p_depth_p_open_set unfolding \<A>'_def by fast
  ultimately obtain \<B>'
    where \<B>': "\<B>' \<subseteq> \<A>'" "finite \<B>'" "p_ring \<subseteq> \<Union> \<B>'"
    using fin_p_quot p_ring_def p_adic_prod_local_int_ring_compact
    by    force
  define \<B> where "\<B> \<equiv> (`) (p_adic_prod_shift_p_depth p n) ` \<B>'"
  have "\<B> \<subseteq> \<A>"
    unfolding \<B>_def
  proof clarify
    fix B' assume "B' \<in> \<B>'"
    with \<B>'(1) \<A>'_def obtain A
      where "A \<in> \<A>" and "B' = p_adic_prod_shift_p_depth p (-n) ` A"
      by    blast
    thus "p_adic_prod_shift_p_depth p n ` B' \<in> \<A>"
      using p_adic_prod_depth_embeds.shift_shift_p_depth_image[of p n "-n"] by simp
  qed
  moreover from \<B>_def \<B>'(2) have "finite \<B>" by blast
  moreover from \<B>_def \<B>'(3) have "p_depth_ring \<subseteq> \<Union> \<B>" using drop by blast
  ultimately show ?thesis using p_depth_ring_def by blast
qed

lemma adelic_int_local_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    range (\<lambda>x. x prestrict ((=) p)) \<subseteq> \<Union> \<B>"
  if  fin_p_quot: "finite (range (\<lambda>x::'a adelic_int_quot. x prestrict ((=) p)))"
  and cover: "range (\<lambda>x. x prestrict ((=) p)) \<subseteq> \<Union> \<A>"
  and by_opens:
    "\<forall>A\<in>\<A>. generate_topology (adelic_int_local_p_open_nbhds p) A"
  for \<A> :: "'a adelic_int set set"
proof-
  define f f' :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
    where "f  \<equiv> \<lambda>x. x prestrict ((=) p)"
    and   "f' \<equiv> \<lambda>x. x prestrict ((\<noteq>) p)"
  define f_f' where "f_f' \<equiv> \<lambda>A. f ` Rep_adelic_int ` A + range f'"
  define p_ring :: "'a p_adic_prod set" where "p_ring \<equiv> f ` \<O>\<^sub>\<forall>\<^sub>p"
  define \<A>' where "\<A>' \<equiv> f_f' ` \<A>"
  from cover f_def f'_def f_f'_def p_ring_def \<A>'_def have "p_ring \<subseteq> \<Union> \<A>'"
    using adelic_int_local_depth_ring_lift_cover[of 0] by fast
  moreover from by_opens f_def f'_def f_f'_def \<A>'_def have
    "\<forall>A'\<in>\<A>'. generate_topology (p_adic_prod_local_p_open_nbhds p) A'"
    using adelic_int_lift_local_p_open by fast
  ultimately obtain \<B>'
    where \<B>': "\<B>' \<subseteq> \<A>'" "finite \<B>'" "p_ring \<subseteq> \<Union> \<B>'"
    using fin_p_quot f_def p_ring_def p_adic_prod_local_int_ring_compact
    by    force
  define g where "g \<equiv> \<lambda>B'. SOME B. B \<in> \<A> \<and> B' = f_f' B"
  define \<B> where "\<B> \<equiv> g ` \<B>'"
  from \<B>_def \<B>'(2) have "finite \<B>" by fast
  moreover have subcover: "\<B> \<subseteq> \<A>"
    unfolding \<B>_def
  proof clarify
    fix B' assume "B' \<in> \<B>'"
    with \<A>'_def \<B>'(1) have ex_B: "\<exists>B. B \<in> \<A> \<and> B' = f_f' B" by blast
    from g_def show "g B' \<in> \<A>" using someI_ex[OF ex_B] by fastforce
  qed
  moreover have "range (\<lambda>x. x prestrict ((=) p)) \<subseteq> \<Union> \<B>"
  proof clarify
    fix x show "x prestrict (=) p \<in> \<Union> \<B>"
    proof (cases x)
      case (Abs_adelic_int a)
      from p_ring_def Abs_adelic_int(2) \<B>'(3) have "f a \<in> \<Union> \<B>'" by auto
      from this obtain B' where B': "B' \<in> \<B>'" "f a \<in> B'" by fast
      from \<A>'_def \<B>'(1) B'(1) have ex_B: "\<exists>B. B \<in> \<A> \<and> B' = f_f' B" by auto
      from B'(1) \<B>_def have g_B': "g B' \<in> \<B>" by auto
      from g_def B'(2) have "f a \<in> f_f' (g B')" using someI_ex[OF ex_B] by simp
      with f_f'_def obtain b c where b: "b \<in> g B'" and bc: "f a = f (Rep_adelic_int b) + f' c"
        using set_plus_elim by blast
      have "f' c = 0"
      proof (intro global_p_depth_p_adic_prod.global_imp_eq, standard)
        fix q :: "'a prime" show "f' c \<simeq>\<^sub>q 0"
        proof (cases "p = q")
          case True with f'_def show ?thesis
            using global_p_depth_p_adic_prod.p_restrict_equiv0 by fast
        next
          case False
          moreover from f_def bc have "f' c = f (a - Rep_adelic_int b)"
            by (simp add: global_p_depth_p_adic_prod.p_restrict_minus)
          ultimately show ?thesis
            using f_def global_p_depth_p_adic_prod.p_restrict_equiv0 by auto
        qed
      qed
      with f_def Abs_adelic_int bc have
        "x prestrict (=) p = b prestrict ((=) p)"
        using p_restrict_adelic_int_abs_eq p_restrict_adelic_int_abs_eq
              Rep_adelic_int[of b] Rep_adelic_int_inverse[of b]
        by    fastforce
      moreover from by_opens b(1) have "b prestrict ((=) p) \<in> g B'"
        using subcover g_B' global_p_depth_adelic_int.p_restrict_p_open_set_mem_iff by blast
      ultimately show ?thesis using g_B' by auto
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma adelic_int_local_scaled_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    (\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<B>"
  if  fin_p_quot: "finite (range (\<lambda>x::'a adelic_int_quot. x prestrict ((=) p)))"
  and cover:
    "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<A>"
  and by_opens:
    "\<forall>A\<in>\<A>. generate_topology (adelic_int_local_p_open_nbhds p) A"
  for \<A> :: "'a adelic_int set set"
proof-
  show ?thesis
  proof (cases "n \<le> 0")
    case True
    hence
      "(\<lambda>x::'a adelic_int. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) =
        range (\<lambda>x. x prestrict ((=) p))"
      using nonpos_global_depth_set_adelic_int by auto
    with fin_p_quot cover by_opens show ?thesis
      using adelic_int_local_int_ring_compact by fastforce
  next
    case False
    define f f' :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
      where "f  \<equiv> \<lambda>x. x prestrict ((=) p)"
      and   "f' \<equiv> \<lambda>x. x prestrict ((\<noteq>) p)"
    define f_f' where "f_f' \<equiv> \<lambda>A. f ` Rep_adelic_int ` A + range f'"
    define p_ring p_depth_ring :: "'a p_adic_prod set"
      where "p_ring       \<equiv> f ` \<O>\<^sub>\<forall>\<^sub>p"
      and   "p_depth_ring \<equiv> f ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
    define \<A>' where "\<A>' \<equiv> f_f' ` \<A>"
    from False cover f_def f'_def f_f'_def p_depth_ring_def \<A>'_def
      have  "p_depth_ring \<subseteq> \<Union> \<A>'"
      using adelic_int_local_depth_ring_lift_cover[of n p \<A>]
      by    auto
    moreover from by_opens f_def f'_def f_f'_def \<A>'_def have
      "\<forall>A'\<in>\<A>'. generate_topology (p_adic_prod_local_p_open_nbhds p) A'"
      using adelic_int_lift_local_p_open by fast
    ultimately obtain \<B>' where \<B>':
      "\<B>' \<subseteq> \<A>'" "finite \<B>'" "p_depth_ring \<subseteq> \<Union> \<B>'"
      using fin_p_quot f_def p_depth_ring_def p_adic_prod_local_scaled_int_ring_compact[of n]
      by    force
    define g where "g \<equiv> \<lambda>B'. SOME B. B \<in> \<A> \<and> B' = f_f' B"
    define \<B> where "\<B> \<equiv> g ` \<B>'"
    from \<B>_def \<B>'(2) have "finite \<B>" by fast
    moreover have subcover: "\<B> \<subseteq> \<A>"
      unfolding \<B>_def
    proof clarify
      fix B' assume "B' \<in> \<B>'"
      with \<A>'_def \<B>'(1) have ex_B: "\<exists>B. B \<in> \<A> \<and> B' = f_f' B" by blast
      from g_def show "g B' \<in> \<A>" using someI_ex[OF ex_B] by fastforce
    qed
    moreover have
      "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) \<subseteq>
        \<Union> \<B>"
    proof clarify
      fix x :: "'a adelic_int" assume x: "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
      show "x prestrict (=) p \<in> \<Union> \<B>"
      proof (cases x)
        case (Abs_adelic_int a)
        hence "a = Rep_adelic_int x" using Abs_adelic_int_inverse by fastforce
        with False x have "a \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
          using lift_nonneg_global_depth_set_adelic_int[of n] by auto
        with p_depth_ring_def \<B>'(3) have "f a \<in> \<Union> \<B>'"
          using nonneg_global_depth_set_adelic_int_eq_projection[of n] by fast
        from this obtain B' where B': "B' \<in> \<B>'" "f a \<in> B'" by fast
        from \<A>'_def \<B>'(1) B'(1) have ex_B: "\<exists>B. B \<in> \<A> \<and> B' = f_f' B"
          by auto
        from B'(1) \<B>_def have g_B': "g B' \<in> \<B>" by auto
        from g_def B'(2) have "f a \<in> f_f' (g B')" using someI_ex[OF ex_B] by simp
        with f_f'_def obtain b c where b: "b \<in> g B'" and bc: "f a = f (Rep_adelic_int b) + f' c"
          using set_plus_elim by blast
        have "f' c = 0"
        proof (intro global_p_depth_p_adic_prod.global_imp_eq, standard)
          fix q :: "'a prime" show "f' c \<simeq>\<^sub>q 0"
          proof (cases "p = q")
            case True with f'_def show ?thesis
              using global_p_depth_p_adic_prod.p_restrict_equiv0 by fast
          next
            case False
            moreover from f_def bc have "f' c = f (a - Rep_adelic_int b)"
              by (simp add: global_p_depth_p_adic_prod.p_restrict_minus)
            ultimately show ?thesis
              using f_def global_p_depth_p_adic_prod.p_restrict_equiv0 by auto
          qed
        qed
        with f_def Abs_adelic_int bc have
          "x prestrict (=) p = b prestrict ((=) p)"
          using p_restrict_adelic_int_abs_eq p_restrict_adelic_int_abs_eq
                Rep_adelic_int[of b] Rep_adelic_int_inverse[of b]
          by    fastforce
        moreover from by_opens b(1) have "b prestrict ((=) p) \<in> g B'"
          using subcover g_B' global_p_depth_adelic_int.p_restrict_p_open_set_mem_iff by blast
        ultimately show ?thesis using g_B' by auto
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

end (* context fin_p_quot *)

lemma int_adic_prod_local_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    (\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<subseteq> \<Union> \<B>"
  if  "(\<lambda>x. x prestrict ((=) p)) ` \<O>\<^sub>\<forall>\<^sub>p \<subseteq> \<Union> \<A>"
  and "\<forall>A\<in>\<A>. generate_topology (p_adic_prod_local_p_open_nbhds p) A"
  for p :: "int prime"
  and \<A> :: "int p_adic_prod set set"
  using that p_adic_prod_local_int_ring_compact[of p \<A>] finite_range_prestrict_single_int_prime
  by    presburger

lemma int_adic_prod_local_scaled_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    (\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<B>"
  if
    "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<A>"
  and "\<forall>A\<in>\<A>. generate_topology (p_adic_prod_local_p_open_nbhds p) A"
  for p :: "int prime"
  and \<A> :: "int p_adic_prod set set"
  using that p_adic_prod_local_scaled_int_ring_compact[of p n \<A>]
        finite_range_prestrict_single_int_prime
  by    presburger

lemma int_adelic_int_local_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    range (\<lambda>x. x prestrict ((=) p)) \<subseteq> \<Union> \<B>"
  if  "range (\<lambda>x. x prestrict ((=) p)) \<subseteq> \<Union> \<A>"
  and "\<forall>A\<in>\<A>. generate_topology (adelic_int_local_p_open_nbhds p) A"
  for p :: "int prime"
  and \<A> :: "int adelic_int set set"
  using that adelic_int_local_int_ring_compact[of p \<A>] finite_range_prestrict_single_int_prime
  by    presburger

lemma int_adelic_int_local_scaled_int_ring_compact:
  "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and>
    (\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<B>"
  if
    "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      \<subseteq> \<Union> \<A>"
  and "\<forall>A\<in>\<A>. generate_topology (adelic_int_local_p_open_nbhds p) A"
  for p :: "int prime"
  and \<A> :: "int adelic_int set set"
  using that adelic_int_local_scaled_int_ring_compact[of p n \<A>]
        finite_range_prestrict_single_int_prime
  by    presburger

end (* theory *)
