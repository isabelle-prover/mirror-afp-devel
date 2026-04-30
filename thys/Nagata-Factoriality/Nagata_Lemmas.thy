theory Nagata_Lemmas
  imports Localization_Interface
begin

section \<open>Record-based Nagata descent lemmas\<close>

definition ring_avoids ::
  "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
where
  "ring_avoids R S p \<longleftrightarrow> (\<forall>s\<in>S. \<not> p divides\<^bsub>R\<^esub> s)"

definition ring_prime_generated ::
  "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "ring_prime_generated R S \<longleftrightarrow>
    (\<forall>s\<in>S. \<exists>fs.
      set fs \<subseteq> S \<and>
      (\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q) \<and>
      foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s)"

lemma ring_prime_generatedI:
  assumes "\<And>s. s \<in> S \<Longrightarrow> \<exists>fs.
    set fs \<subseteq> S \<and>
    (\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q) \<and>
    foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s"
  shows "ring_prime_generated R S"
  using assms unfolding ring_prime_generated_def by blast

lemma ring_prime_generatedE:
  assumes "ring_prime_generated R S" "s \<in> S"
  obtains fs where
    "set fs \<subseteq> S"
    "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
    "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s"
  using assms unfolding ring_prime_generated_def by blast

definition ring_powers_set ::
  "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> 'a set"
where
  "ring_powers_set R p = {x. \<exists>n::nat. x = p [^]\<^bsub>R\<^esub> n}"

inductive_set ring_mult_submonoid_closure ::
  "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for R and A
where
  one_closed: "\<one>\<^bsub>R\<^esub> \<in> ring_mult_submonoid_closure R A"
| generator: "a \<in> A \<Longrightarrow> a \<in> ring_mult_submonoid_closure R A"
| mult_closed:
    "a \<in> ring_mult_submonoid_closure R A \<Longrightarrow>
      b \<in> ring_mult_submonoid_closure R A \<Longrightarrow>
      a \<otimes>\<^bsub>R\<^esub> b \<in> ring_mult_submonoid_closure R A"

lemma ring_mult_submonoid_closure_subset:
  assumes ring_R: "ring R"
    and A_sub: "A \<subseteq> carrier R"
  shows "ring_mult_submonoid_closure R A \<subseteq> carrier R"
proof -
  interpret R: ring R
    by (rule ring_R)
  show ?thesis
  proof
    fix x
    assume x_in: "x \<in> ring_mult_submonoid_closure R A"
    then show "x \<in> carrier R"
      by induction (use A_sub in auto)
  qed
qed

lemma ring_mult_submonoid_closure_submonoid:
  assumes ring_R: "ring R"
    and A_sub: "A \<subseteq> carrier R"
  shows "submonoid R (ring_mult_submonoid_closure R A)"
proof -
  interpret R: ring R
    by (rule ring_R)
  show ?thesis
  proof 
    show "ring_mult_submonoid_closure R A \<subseteq> carrier R"
      by (rule ring_mult_submonoid_closure_subset[OF ring_R A_sub])
  qed (auto simp: ring_mult_submonoid_closure.one_closed ring_mult_submonoid_closure.mult_closed)
qed

lemma foldr_mult_right:
  assumes ring_R: "ring R"
    and xs_sub: "set xs \<subseteq> carrier R"
    and y_in: "y \<in> carrier R"
  shows "foldr (\<otimes>\<^bsub>R\<^esub>) xs y =
      foldr (\<otimes>\<^bsub>R\<^esub>) xs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> y"
proof -
  interpret R: ring R
    by (rule ring_R)
  show ?thesis
    using xs_sub y_in
  proof (induction xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    have x_in: "x \<in> carrier R"
      using Cons.prems(1) by simp
    have xs_sub': "set xs \<subseteq> carrier R"
      using Cons.prems(1) by simp
    have prod_in: "foldr (\<otimes>\<^bsub>R\<^esub>) xs \<one>\<^bsub>R\<^esub> \<in> carrier R"
      using xs_sub'
    proof (induction xs)
      case Nil
      then show ?case by simp
    next
      case (Cons z zs)
      then show ?case by simp
    qed
    show ?case
      using Cons.IH[OF xs_sub' Cons.prems(2)] x_in prod_in Cons.prems(2)
      by (simp add: R.m_assoc)
  qed
qed

lemma ring_powers_submonoid:
  assumes ring_R: "ring R"
    and p_in: "p \<in> carrier R"
  shows "submonoid R (ring_powers_set R p)"
proof -
  interpret R: ring R
    by (rule ring_R)
  show ?thesis
  proof (unfold_locales)
    show "ring_powers_set R p \<subseteq> carrier R"
      using p_in unfolding ring_powers_set_def by auto
    show "\<And>x y. x \<in> ring_powers_set R p \<Longrightarrow> y \<in> ring_powers_set R p \<Longrightarrow> x \<otimes>\<^bsub>R\<^esub> y \<in> ring_powers_set R p"
    proof -
      fix x y
      assume x_in: "x \<in> ring_powers_set R p" and y_in: "y \<in> ring_powers_set R p"
      then obtain m n :: nat where x_def: "x = p [^]\<^bsub>R\<^esub> m" and y_def: "y = p [^]\<^bsub>R\<^esub> n"
        unfolding ring_powers_set_def by blast
      show "x \<otimes>\<^bsub>R\<^esub> y \<in> ring_powers_set R p"
        using R.nat_pow_mult p_in ring_powers_set_def x_def y_def by fastforce
    qed
    show "\<one>\<^bsub>R\<^esub> \<in> ring_powers_set R p"
    proof -
      have "\<one>\<^bsub>R\<^esub> = p [^]\<^bsub>R\<^esub> (0::nat)"
        using p_in by simp
      then show ?thesis
        unfolding ring_powers_set_def by blast
    qed
  qed
qed

lemma ring_prime_generated_powers_set:
  assumes ring_R: "ring R"
    and p_in: "p \<in> carrier R"
    and hp: "ring_prime\<^bsub>R\<^esub> p"
  shows "ring_prime_generated R (ring_powers_set R p)"
proof (rule ring_prime_generatedI)
  interpret R: ring R
    by (rule ring_R)
  fix s
  assume s_in: "s \<in> ring_powers_set R p"
  then obtain n :: nat where s_def: "s = p [^]\<^bsub>R\<^esub> n"
    unfolding ring_powers_set_def by blast
  show "\<exists>fs.
      set fs \<subseteq> ring_powers_set R p \<and>
      (\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q) \<and>
      foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s"
  proof (intro exI conjI)
    show "set (replicate n p) \<subseteq> ring_powers_set R p"
    proof
      fix q
      assume q_in: "q \<in> set (replicate n p)"
      then have q_eq: "q = p"
        by simp
      show "q \<in> ring_powers_set R p"
        by (metis (mono_tags, lifting) R.nat_pow_eone mem_Collect_eq p_in q_eq
            ring_powers_set_def)
    qed
    show "(\<forall>q\<in>set (replicate n p). ring_prime\<^bsub>R\<^esub> q)"
      using hp by simp
    show "foldr (\<otimes>\<^bsub>R\<^esub>) (replicate n p) \<one>\<^bsub>R\<^esub> = s"
    proof -
      have "foldr (\<otimes>\<^bsub>R\<^esub>) (replicate n p) \<one>\<^bsub>R\<^esub> = p [^]\<^bsub>R\<^esub> n"
        using p_in
      proof (induction n)
        case 0
        then show ?case by simp
      next
        case (Suc n)
        have "foldr (\<otimes>\<^bsub>R\<^esub>) (replicate (Suc n) p) \<one>\<^bsub>R\<^esub> =
            p \<otimes>\<^bsub>R\<^esub> p [^]\<^bsub>R\<^esub> n"
          using Suc.IH p_in by simp
        also have "\<dots> = p [^]\<^bsub>R\<^esub> (Suc n)"
          by (rule sym[OF R.nat_pow_Suc2[OF p_in]])
        finally show ?case .
      qed
      then show ?thesis
        using s_def by simp
    qed
  qed
qed

lemma ring_prime_generated_mult_submonoid_closure:
  assumes ring_R: "ring R"
    and A_sub: "A \<subseteq> carrier R"
    and hprime: "\<And>q. q \<in> A \<Longrightarrow> ring_prime\<^bsub>R\<^esub> q"
  shows "ring_prime_generated R (ring_mult_submonoid_closure R A)"
proof (rule ring_prime_generatedI)
  interpret R: ring R
    by (rule ring_R)
  have closure_sub: "ring_mult_submonoid_closure R A \<subseteq> carrier R"
    by (rule ring_mult_submonoid_closure_subset[OF ring_R A_sub])
  fix s
  assume s_in: "s \<in> ring_mult_submonoid_closure R A"
  show "\<exists>fs.
      set fs \<subseteq> ring_mult_submonoid_closure R A \<and>
      (\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q) \<and>
      foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s"
    using s_in
  proof induction
    case one_closed
    show ?case
      by (intro exI[of _ "[]"]) auto
  next
    case (generator a)
    show ?case
    proof (intro exI[of _ "[a]"] conjI)
      have a_in_closure: "a \<in> ring_mult_submonoid_closure R A"
        by (rule ring_mult_submonoid_closure.generator[OF generator.hyps])
      show "set [a] \<subseteq> ring_mult_submonoid_closure R A"
        using a_in_closure by simp
      show "\<forall>q\<in>set [a]. ring_prime\<^bsub>R\<^esub> q"
        using hprime generator.hyps by simp
      have a_in: "a \<in> carrier R"
        using A_sub generator.hyps by blast
      show "foldr (\<otimes>\<^bsub>R\<^esub>) [a] \<one>\<^bsub>R\<^esub> = a"
        using a_in by simp
    qed
  next
    case (mult_closed a b)
    from mult_closed.IH(1) obtain fs where
        fs_sub: "set fs \<subseteq> ring_mult_submonoid_closure R A"
        and fs_prime: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
        and fs_prod: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = a"
      by blast
    from mult_closed.IH(2) obtain gs where
        gs_sub: "set gs \<subseteq> ring_mult_submonoid_closure R A"
        and gs_prime: "\<forall>q\<in>set gs. ring_prime\<^bsub>R\<^esub> q"
        and gs_prod: "foldr (\<otimes>\<^bsub>R\<^esub>) gs \<one>\<^bsub>R\<^esub> = b"
      by blast
    have fs_carr: "set fs \<subseteq> carrier R"
      using fs_sub closure_sub by blast
    have b_in: "b \<in> carrier R"
      using mult_closed.hyps(2) closure_sub by blast
    have prod_append:
        "foldr (\<otimes>\<^bsub>R\<^esub>) (fs @ gs) \<one>\<^bsub>R\<^esub> = a \<otimes>\<^bsub>R\<^esub> b"
    proof -
      have "foldr (\<otimes>\<^bsub>R\<^esub>) (fs @ gs) \<one>\<^bsub>R\<^esub> =
          foldr (\<otimes>\<^bsub>R\<^esub>) fs (foldr (\<otimes>\<^bsub>R\<^esub>) gs \<one>\<^bsub>R\<^esub>)"
        by simp
      also have "\<dots> = foldr (\<otimes>\<^bsub>R\<^esub>) fs b"
        by (simp add: gs_prod)
      also have "\<dots> = foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b"
        by (rule foldr_mult_right[OF ring_R fs_carr b_in])
      also have "\<dots> = a \<otimes>\<^bsub>R\<^esub> b"
        by (simp add: fs_prod)
      finally show ?thesis .
    qed
    show ?case
      by (intro exI[of _ "fs @ gs"])
        (use fs_sub fs_prime gs_sub gs_prime prod_append in auto)
  qed
qed

locale nagata_localization = eq_obj_rng_of_frac R S + domain R for R (structure) and S
begin

lemma no_zero_divisors:
  "\<forall>a \<in> carrier R. \<forall>b \<in> carrier R. a \<otimes>\<^bsub>R\<^esub> b = \<zero> \<longrightarrow> a = \<zero> \<or> b = \<zero>"
  using integral by blast

lemma multlist_closed:
  assumes xs_sub: "set xs \<subseteq> carrier R"
  shows "foldr (\<otimes>\<^bsub>R\<^esub>) xs \<one>\<^bsub>R\<^esub> \<in> carrier R"
  using xs_sub
  by (induction xs) auto

lemma multlist_mem_submonoid:
  assumes fs_sub: "set fs \<subseteq> S"
  shows "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> \<in> S"
  using fs_sub
proof (induction fs)
  case Nil
  show ?case
    by simp
next
  case (Cons q qs)
  have q_in: "q \<in> S"
    using Cons.prems by simp
  have qs_in: "set qs \<subseteq> S"
    using Cons.prems by simp
  show ?case
    using q_in Cons.IH[OF qs_in] by simp
qed

lemma multlist_nonzero_of_prime_factors:
  assumes fs_sub: "set fs \<subseteq> S"
    and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
  shows "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> \<noteq> \<zero>"
  using fs_sub hf
proof (induction fs)
  case Nil
  show ?case
    by simp
next
  case (Cons q qs)
  have q_in: "q \<in> S"
    using Cons.prems(1) by simp
  have q_carr: "q \<in> carrier R"
    using q_in subset rev_subsetD by blast
  have q_prime: "ring_prime\<^bsub>R\<^esub> q"
    using Cons.prems(2) by simp
  have q_nz: "q \<noteq> \<zero>"
    using ring_primeE(1)[OF q_carr q_prime] .
  have qs_sub: "set qs \<subseteq> S"
    using Cons.prems(1) by simp
  have qs_prime: "\<forall>r\<in>set qs. ring_prime\<^bsub>R\<^esub> r"
    using Cons.prems(2) by simp
  have qs_nz: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<noteq> \<zero>"
    using Cons.IH[OF qs_sub qs_prime] .
  have qs_carr: "set qs \<subseteq> carrier R"
    using qs_sub subset by blast
  have prod_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<in> carrier R"
    by (rule multlist_closed[OF qs_carr])
  show ?case
    by (simp add: integral_iff prod_carr q_carr q_nz qs_nz)
qed

lemma zero_notin_submonoid_of_prime_generated:
  assumes hS: "ring_prime_generated R S"
  shows "\<zero> \<notin> S"
proof
  assume zero_in: "\<zero> \<in> S"
  obtain fs where
      fs_sub: "set fs \<subseteq> S"
      and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
      and hprod: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = \<zero>"
    using ring_prime_generatedE[OF hS zero_in] by blast
  have "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> \<noteq> \<zero>"
    using multlist_nonzero_of_prime_factors[OF fs_sub hf] .
  with hprod show False
    by contradiction
qed

lemma zero_notin_submonoid_of_prime_or_unit:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
  shows "\<zero> \<notin> S"
proof
  assume zero_in: "\<zero> \<in> S"
  from hS[OF zero_in] show False
  proof
    assume "ring_prime\<^bsub>R\<^esub> \<zero>"
    then show False
      by (simp add: ring_prime_def)
  next
    assume zero_unit: "\<zero> \<in> Units R"
    have inv_zero_in: "inv \<zero> \<in> carrier R"
      using zero_unit by simp
    have "(\<zero> \<otimes>\<^bsub>R\<^esub> inv \<zero>) = \<zero>"
      using inv_zero_in by simp
    moreover have "(\<zero> \<otimes>\<^bsub>R\<^esub> inv \<zero>) = \<one>"
      using zero_unit by simp
    ultimately show False
      using one_not_zero by simp
  qed
qed

lemma ring_prime_imp_ring_irreducible:
  assumes p_in: "p \<in> carrier R"
    and hp: "ring_prime\<^bsub>R\<^esub> p"
  shows "ring_irreducible\<^bsub>R\<^esub> p"
proof -
  from ring_primeE[OF p_in hp] have p_nz: "p \<noteq> \<zero>"
    and p_prime_mult: "prime (mult_of R) p"
    by auto
  have "irreducible (mult_of R) p"
    using p_prime_mult by (rule mult_of.prime_irreducible)
  have p_nz_in: "p \<in> carrier R - {\<zero>}"
    using p_in p_nz by blast
  from p_nz_in and \<open>irreducible (mult_of R) p\<close> show ?thesis
    by (rule ring_irreducibleI')
qed

lemma prime_of_irreducible_of_dvd_mem:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and s_in: "s \<in> S"
    and p_dvd_s: "p divides\<^bsub>R\<^esub> s"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof -
  have p_not_unit: "p \<notin> Units R"
    using ring_irreducibleE(4)[OF p_in hp] .
  from hS[OF s_in] show ?thesis
  proof
    assume hs_prime: "ring_prime\<^bsub>R\<^esub> s"
    have s_in_carrier: "s \<in> carrier R"
      using s_in subset rev_subsetD by blast
    have s_irreducible: "ring_irreducible\<^bsub>R\<^esub> s"
      using s_in_carrier hs_prime by (rule ring_prime_imp_ring_irreducible)
    have p_assoc_s: "p \<sim>\<^bsub>R\<^esub> s"
      by (meson divides_irreducible_condition p_dvd_s p_in p_not_unit ring_irreducible_def
          s_irreducible)
    have s_prime: "prime R s"
      using ring_primeE(3)[OF s_in_carrier hs_prime] .
    have s_nz: "s \<noteq> \<zero>"
      using ring_primeE(1)[OF s_in_carrier hs_prime] .
    have p_nz: "p \<noteq> \<zero>"
      using ring_irreducibleE(1)[OF p_in hp] .
    have s_assoc_p_mult: "s \<sim>\<^bsub>mult_of R\<^esub> p"
      using assoc_iff_assoc_mult[OF s_in_carrier p_in] associated_sym[OF p_assoc_s] by blast
    have s_prime_mult: "prime (mult_of R) s"
      using prime_eq_prime_mult[OF s_in_carrier] s_prime by blast
    have "prime R p"
    proof -
      have "prime (mult_of R) p"
      proof (rule mult_of.prime_cong[OF s_prime_mult s_assoc_p_mult])
        show "s \<in> carrier (mult_of R)"
          using s_in_carrier s_nz by simp
        show "p \<in> carrier (mult_of R)"
          using p_in p_nz by simp
      qed
      then show ?thesis
        using prime_eq_prime_mult[OF p_in] by blast
    qed
    then have p_prime: "prime R p" .
    from p_nz p_prime show ?thesis
      by (rule ring_primeI)
  next
    assume hs_unit: "s \<in> Units R"
    have "p \<in> Units R"
      using divides_unit[OF p_dvd_s p_in hs_unit] .
    with p_not_unit show ?thesis
      by contradiction
  qed
qed

lemma prime_of_irreducible_of_dvd_prime_factors:
  assumes fs_sub: "set fs \<subseteq> S"
    and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and hdiv: "p divides\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub>"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof -
  have hmain:
      "\<And>gs. set gs \<subseteq> S \<Longrightarrow>
        (\<forall>q\<in>set gs. ring_prime\<^bsub>R\<^esub> q) \<Longrightarrow>
        p divides\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) gs \<one>\<^bsub>R\<^esub> \<Longrightarrow>
        ring_prime\<^bsub>R\<^esub> p"
  proof -
    fix gs
    show "set gs \<subseteq> S \<Longrightarrow>
        (\<forall>q\<in>set gs. ring_prime\<^bsub>R\<^esub> q) \<Longrightarrow>
        p divides\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) gs \<one>\<^bsub>R\<^esub> \<Longrightarrow>
        ring_prime\<^bsub>R\<^esub> p"
    proof (induction gs)
      case Nil
      have p_dvd_one: "p divides\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>"
        using Nil.prems(3) by simp
      have "p \<in> Units R"
        by (rule divides_unit[OF p_dvd_one p_in Units_one_closed])
      with ring_irreducibleE(4)[OF p_in hp] show ?case
        by contradiction
    next
      case (Cons q qs)
      have q_in: "q \<in> S"
        using Cons.prems(1) by simp
      have q_carr: "q \<in> carrier R"
        using q_in subset rev_subsetD by blast
      have q_ring_prime: "ring_prime\<^bsub>R\<^esub> q"
        using Cons.prems(2) by simp
      have q_prime: "prime R q"
        using ring_primeE(3)[OF q_carr q_ring_prime] .
      have q_nz: "q \<noteq> \<zero>"
        using ring_primeE(1)[OF q_carr q_ring_prime] .
      have q_ring_irred: "ring_irreducible\<^bsub>R\<^esub> q"
        using ring_prime_imp_ring_irreducible[OF q_carr q_ring_prime] .
      have q_not_unit: "q \<notin> Units R"
        using ring_irreducibleE(4)[OF q_carr q_ring_irred] .
      have qs_sub: "set qs \<subseteq> S"
        using Cons.prems(1) by simp
      have qs_prime: "\<forall>r\<in>set qs. ring_prime\<^bsub>R\<^esub> r"
        using Cons.prems(2) by simp
      have qs_carr: "set qs \<subseteq> carrier R"
        using qs_sub subset by blast
      have rest_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<in> carrier R"
        by (rule multlist_closed[OF qs_carr])
      obtain d where
          d_in: "d \<in> carrier R"
          and hd: "foldr (\<otimes>\<^bsub>R\<^esub>) (q # qs) \<one>\<^bsub>R\<^esub> = p \<otimes>\<^bsub>R\<^esub> d"
        using Cons.prems(3) unfolding factor_def by blast
      have q_dvd_pd: "q divides\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> d)"
      proof -
        have "q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> = p \<otimes>\<^bsub>R\<^esub> d"
          using hd by simp
        then show ?thesis
          using rest_carr by force
      qed
      have q_dvd_p_or_d: "q divides\<^bsub>R\<^esub> p \<or> q divides\<^bsub>R\<^esub> d"
        using primeE[OF q_prime] p_in d_in q_dvd_pd by blast
      from q_dvd_p_or_d show ?case
      proof
        assume q_dvd_p: "q divides\<^bsub>R\<^esub> p"
        have q_assoc_p: "q \<sim>\<^bsub>R\<^esub> p"
          by (meson divides_irreducible_condition hp q_carr q_dvd_p q_not_unit ring_irreducible_def)
        have q_assoc_p_mult: "q \<sim>\<^bsub>mult_of R\<^esub> p"
          using assoc_iff_assoc_mult[OF q_carr p_in] q_assoc_p by blast
        have q_prime_mult: "prime (mult_of R) q"
          using prime_eq_prime_mult[OF q_carr] q_prime by blast
        have "prime R p"
        proof -
          have "prime (mult_of R) p"
          proof (rule mult_of.prime_cong[OF q_prime_mult q_assoc_p_mult])
            show "q \<in> carrier (mult_of R)"
              using q_carr q_nz by simp
            show "p \<in> carrier (mult_of R)"
              using p_in ring_irreducibleE(1)[OF p_in hp] by simp
          qed
          then show ?thesis
            using prime_eq_prime_mult[OF p_in] by blast
        qed
        then have p_prime: "prime R p" .
        from ring_irreducibleE(1)[OF p_in hp] p_prime show ?thesis
          by (rule ring_primeI)
      next
        assume q_dvd_d: "q divides\<^bsub>R\<^esub> d"
        obtain e where e_in: "e \<in> carrier R" and he: "d = q \<otimes>\<^bsub>R\<^esub> e"
          using q_dvd_d unfolding factor_def by blast
        have pe_carr: "p \<otimes>\<^bsub>R\<^esub> e \<in> carrier R"
          using p_in e_in by auto
        have rest_eq: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> = p \<otimes>\<^bsub>R\<^esub> e"
        proof -
          have "q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> = q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> e)"
            using hd he q_carr rest_carr p_in e_in by (simp add: m_assoc m_comm m_lcomm)
          then show ?thesis
            using q_nz q_carr rest_carr pe_carr by (simp add: m_lcancel)
        qed
        have p_dvd_rest: "p divides\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>"
          unfolding factor_def using e_in rest_eq by blast
        show ?thesis
          by (rule Cons.IH[OF qs_sub qs_prime p_dvd_rest])
      qed
    qed
  qed
  show ?thesis
    by (rule hmain[OF fs_sub hf hdiv])
qed

lemma prime_of_irreducible_of_dvd_mem_prime_generated:
  assumes hS: "ring_prime_generated R S"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and s_in: "s \<in> S"
    and p_dvd_s: "p divides\<^bsub>R\<^esub> s"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof -
  obtain fs where
      fs_sub: "set fs \<subseteq> S"
      and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
      and hprod: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s"
    using ring_prime_generatedE[OF hS s_in] by blast
  have "p divides\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub>"
    using p_dvd_s by (simp add: hprod)
  then show ?thesis
    by (rule prime_of_irreducible_of_dvd_prime_factors[OF fs_sub hf p_in hp])
qed

lemma dvd_of_localization_dvd:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and p_in: "p \<in> carrier R"
    and a_in: "a \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
    and hdiv: "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a"
  shows "p divides\<^bsub>R\<^esub> a"
proof -
  have zero_notin: "\<zero> \<notin> S"
    using hS by (rule zero_notin_submonoid_of_prime_or_unit)
  have hdiv':
      "\<exists>s \<in> S. p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> a)"
    using dvd_map_iff[OF p_in a_in zero_notin no_zero_divisors] hdiv
    by blast
  then obtain s where s_in: "s \<in> S" and p_dvd_sa: "p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> a)"
    by blast
  have s_in_carrier: "s \<in> carrier R"
    using s_in subset rev_subsetD by blast
  then obtain c where c_in: "c \<in> carrier R" and hc: "s \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> c"
    using p_dvd_sa unfolding factor_def by blast
  from hS[OF s_in] show ?thesis
  proof
    assume hs_prime: "ring_prime\<^bsub>R\<^esub> s"
    have s_nz: "s \<noteq> \<zero>" and s_prime: "prime R s"
      using ring_primeE[OF s_in_carrier hs_prime] by auto
    have s_not_unit: "s \<notin> Units R"
      using primeE[OF s_prime] by blast
    have s_dvd_pc: "s divides\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> c)"
      using a_in hc by force
    have s_dvd_p_or_c: "s divides\<^bsub>R\<^esub> p \<or> s divides\<^bsub>R\<^esub> c"
      using primeE[OF s_prime] p_in c_in s_dvd_pc by blast
    from s_dvd_p_or_c show ?thesis
    proof
      assume s_dvd_p: "s divides\<^bsub>R\<^esub> p"
      have s_assoc_p: "s \<sim>\<^bsub>R\<^esub> p"
        by (meson divides_irreducible_condition hp ring_irreducible_def s_dvd_p s_in_carrier
            s_not_unit)
      have "p divides\<^bsub>R\<^esub> s"
        using associatedD[OF associated_sym[OF s_assoc_p]] .
      moreover have "\<not> p divides\<^bsub>R\<^esub> s"
        using havoid s_in unfolding ring_avoids_def by blast
      ultimately show ?thesis
        by contradiction
    next
      assume s_dvd_c: "s divides\<^bsub>R\<^esub> c"
      then obtain d where d_in: "d \<in> carrier R" and hd: "c = s \<otimes>\<^bsub>R\<^esub> d"
        unfolding factor_def by blast
      have pd_in: "p \<otimes>\<^bsub>R\<^esub> d \<in> carrier R"
        using p_in d_in by auto
      have "s \<otimes>\<^bsub>R\<^esub> a = s \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> d)"
        using hc hd s_in_carrier a_in p_in d_in by (simp add: m_assoc m_comm m_lcomm)
      then have "a = p \<otimes>\<^bsub>R\<^esub> d"
        using s_nz s_in_carrier a_in pd_in by (simp add: m_lcancel)
      then show ?thesis
        unfolding factor_def using d_in by blast
    qed
  next
    assume hs_unit: "s \<in> Units R"
    have sa_assoc_a: "(s \<otimes>\<^bsub>R\<^esub> a) \<sim>\<^bsub>R\<^esub> a"
      using hs_unit a_in s_in_carrier by (intro associatedI2') (simp add: m_comm)
    have "p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> a)"
      using p_dvd_sa .
    then show ?thesis
      using divides_cong_r[OF _ sa_assoc_a p_in] by blast
  qed
qed

lemma prime_of_localization_prime:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
    and hploc: "ring_prime\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof (rule ring_primeI)
  show "p \<noteq> \<zero>"
    using ring_irreducibleE(1)[OF p_in hp] .
next
  show "prime R p"
  proof (rule primeI)
    show "p \<notin> Units R"
      using ring_irreducibleE(4)[OF p_in hp] .
  next
    fix a b
    assume a_in: "a \<in> carrier R"
      and b_in: "b \<in> carrier R"
      and p_dvd_ab: "p divides\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
    obtain c where c_in: "c \<in> carrier R" and hc: "a \<otimes>\<^bsub>R\<^esub> b = p \<otimes>\<^bsub>R\<^esub> c"
      using p_dvd_ab unfolding factor_def by blast
    have a_frac_in: "rng_to_rng_of_frac a \<in> carrier rec_rng_of_frac"
      by (rule ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom a_in])
    have b_frac_in: "rng_to_rng_of_frac b \<in> carrier rec_rng_of_frac"
      by (rule ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom b_in])
    have c_frac_in: "rng_to_rng_of_frac c \<in> carrier rec_rng_of_frac"
      by (rule ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom c_in])
    have hloc_div:
        "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub>
          (rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b)"
    proof -
      have map_ab:
          "rng_to_rng_of_frac (a \<otimes>\<^bsub>R\<^esub> b) =
            rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b"
        using ring_hom_mult[OF rng_to_rng_of_frac_is_ring_hom a_in b_in] .
      have map_pc:
          "rng_to_rng_of_frac (p \<otimes>\<^bsub>R\<^esub> c) =
            rng_to_rng_of_frac p \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac c"
        using ring_hom_mult[OF rng_to_rng_of_frac_is_ring_hom p_in c_in] .
      have "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (a \<otimes>\<^bsub>R\<^esub> b)"
        unfolding factor_def using c_frac_in hc map_pc by auto
      then show ?thesis
        using map_ab by simp
    qed
    have hloc_prime: "prime rec_rng_of_frac (rng_to_rng_of_frac p)"
      using hploc unfolding ring_prime_def by simp
    have hloc_cases:
        "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a \<or>
          rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b"
      by (metis a_frac_in b_frac_in hloc_div hloc_prime primeE)
    then show "p divides\<^bsub>R\<^esub> a \<or> p divides\<^bsub>R\<^esub> b"
      using dvd_of_localization_dvd[OF hS p_in a_in hp havoid]
        dvd_of_localization_dvd[OF hS p_in b_in hp havoid]
      by blast
  qed
qed

lemma dvd_of_mul_eq_prime_factors:
  assumes fs_sub: "set fs \<subseteq> S"
    and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
    and p_in: "p \<in> carrier R"
    and a_in: "a \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and hnot: "\<forall>q\<in>set fs. \<not> p divides\<^bsub>R\<^esub> q"
    and c_in: "c \<in> carrier R"
    and hEq: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> c"
  shows "p divides\<^bsub>R\<^esub> a"
proof -
  have hmain:
      "\<And>gs d. set gs \<subseteq> S \<Longrightarrow>
        (\<forall>q\<in>set gs. ring_prime\<^bsub>R\<^esub> q) \<Longrightarrow>
        (\<forall>q\<in>set gs. \<not> p divides\<^bsub>R\<^esub> q) \<Longrightarrow>
        d \<in> carrier R \<Longrightarrow>
        foldr (\<otimes>\<^bsub>R\<^esub>) gs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> d \<Longrightarrow>
        p divides\<^bsub>R\<^esub> a"
  proof -
    fix gs d
    show "set gs \<subseteq> S \<Longrightarrow>
        (\<forall>q\<in>set gs. ring_prime\<^bsub>R\<^esub> q) \<Longrightarrow>
        (\<forall>q\<in>set gs. \<not> p divides\<^bsub>R\<^esub> q) \<Longrightarrow>
        d \<in> carrier R \<Longrightarrow>
        foldr (\<otimes>\<^bsub>R\<^esub>) gs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> d \<Longrightarrow>
        p divides\<^bsub>R\<^esub> a"
    proof (induction gs arbitrary: d)
      case Nil
      from Nil.prems have d_in: "d \<in> carrier R" and eq: "a = p \<otimes>\<^bsub>R\<^esub> d"
        using a_in by simp_all
      show ?case
        using d_in eq unfolding factor_def by blast
    next
      case (Cons q qs)
    have q_in: "q \<in> S"
      using Cons.prems(1) by simp
    have q_carr: "q \<in> carrier R"
      using q_in subset rev_subsetD by blast
    have q_ring_prime: "ring_prime\<^bsub>R\<^esub> q"
      using Cons.prems(2) by simp
    have q_prime: "prime R q"
      using ring_primeE(3)[OF q_carr q_ring_prime] .
    have q_nz: "q \<noteq> \<zero>"
      using ring_primeE(1)[OF q_carr q_ring_prime] .
    have q_ring_irred: "ring_irreducible\<^bsub>R\<^esub> q"
      using ring_prime_imp_ring_irreducible[OF q_carr q_ring_prime] .
    have q_not_unit: "q \<notin> Units R"
      using ring_irreducibleE(4)[OF q_carr q_ring_irred] .
    have qs_sub: "set qs \<subseteq> S"
      using Cons.prems(1) by simp
    have qs_prime: "\<forall>r\<in>set qs. ring_prime\<^bsub>R\<^esub> r"
      using Cons.prems(2) by simp
    have qs_not: "\<forall>r\<in>set qs. \<not> p divides\<^bsub>R\<^esub> r"
      using Cons.prems(3) by simp
    have qs_carr: "set qs \<subseteq> carrier R"
      using qs_sub subset by blast
    have rest_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<in> carrier R"
      by (rule multlist_closed[OF qs_carr])
    have resta_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a \<in> carrier R"
      using rest_carr a_in by auto
    have q_dvd_pd: "q divides\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> d)"
    proof -
      have hqd: "q \<otimes>\<^bsub>R\<^esub> (foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a) = p \<otimes>\<^bsub>R\<^esub> d"
        using Cons.prems(5) a_in m_comm m_lcomm q_carr rest_carr by force
      then show ?thesis
        by (metis dividesI resta_carr)
    qed
    have q_dvd_p_or_d: "q divides\<^bsub>R\<^esub> p \<or> q divides\<^bsub>R\<^esub> d"
      using primeE[OF q_prime] p_in Cons.prems(4) q_dvd_pd by blast
    from q_dvd_p_or_d show ?case
    proof
      assume q_dvd_p: "q divides\<^bsub>R\<^esub> p"
      have q_assoc_p: "q \<sim>\<^bsub>R\<^esub> p"
        by (metis divides_irreducible_condition hp q_carr q_dvd_p q_not_unit ring_irreducible_def)
      have "p divides\<^bsub>R\<^esub> q"
        using associatedD[OF associated_sym[OF q_assoc_p]] .
      with Cons.prems(3) show ?thesis
        by simp
    next
      assume q_dvd_d: "q divides\<^bsub>R\<^esub> d"
      obtain e where e_in: "e \<in> carrier R" and he: "d = q \<otimes>\<^bsub>R\<^esub> e"
        using q_dvd_d unfolding factor_def by blast
      have pe_carr: "p \<otimes>\<^bsub>R\<^esub> e \<in> carrier R"
        using p_in e_in by auto
      have rest_eq: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> e"
      proof -
        have "q \<otimes>\<^bsub>R\<^esub> (foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a) =
            q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> e)"
          using Cons.prems(5) he q_carr rest_carr a_in p_in e_in
          by (simp add: m_assoc m_comm m_lcomm)
        then show ?thesis
          using q_nz q_carr resta_carr pe_carr by (simp add: m_lcancel)
      qed
      show ?thesis
        by (rule Cons.IH[OF qs_sub qs_prime qs_not e_in rest_eq])
    qed
  qed
  qed
  show ?thesis
    by (rule hmain[OF fs_sub hf hnot c_in hEq])
qed

lemma dvd_of_localization_dvd_prime_generated:
  assumes hS: "ring_prime_generated R S"
    and p_in: "p \<in> carrier R"
    and a_in: "a \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
    and hdiv: "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a"
  shows "p divides\<^bsub>R\<^esub> a"
proof -
  have zero_notin: "\<zero> \<notin> S"
    using zero_notin_submonoid_of_prime_generated[OF hS] .
  have hdiv':
      "\<exists>s \<in> S. p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> a)"
    using dvd_map_iff[OF p_in a_in zero_notin no_zero_divisors] hdiv
    by blast
  then obtain s where s_in: "s \<in> S" and p_dvd_sa: "p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> a)"
    by blast
  obtain c where c_in: "c \<in> carrier R" and hc: "s \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> c"
    using p_dvd_sa unfolding factor_def by blast
  obtain fs where
      fs_sub: "set fs \<subseteq> S"
      and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
      and hprod: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s"
    using ring_prime_generatedE[OF hS s_in] by blast
  have hnot: "\<forall>q\<in>set fs. \<not> p divides\<^bsub>R\<^esub> q"
    using havoid fs_sub unfolding ring_avoids_def by blast
  have hEq: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a = p \<otimes>\<^bsub>R\<^esub> c"
    using hc by (simp add: hprod)
  show ?thesis
    using dvd_of_mul_eq_prime_factors[OF fs_sub hf p_in a_in hp hnot c_in hEq] .
qed

lemma map_irreducible_not_unit_of_zero_notin:
  assumes zero_notin: "\<zero> \<notin> S"
    and loc_dom: "domain rec_rng_of_frac"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
  shows "rng_to_rng_of_frac p \<notin> Units rec_rng_of_frac"
proof
  interpret L: domain rec_rng_of_frac
    by (rule loc_dom)
  assume map_p_unit: "rng_to_rng_of_frac p \<in> Units rec_rng_of_frac"
  have map_p_dvd_one:
      "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> \<one>\<^bsub>rec_rng_of_frac\<^esub>"
    using L.unit_divides[OF map_p_unit L.one_closed] .
  have map_p_dvd_map_one:
      "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac \<one>"
    using map_p_dvd_one ring_hom_one[OF rng_to_rng_of_frac_is_ring_hom]
    by simp
  have one_in: "\<one> \<in> carrier R"
    by simp
  have hdiv:
      "\<exists>s \<in> S. p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> \<one>)"
    using dvd_map_iff[OF p_in one_in zero_notin no_zero_divisors] map_p_dvd_map_one
    by blast
  then obtain s where s_in: "s \<in> S" and p_dvd_s: "p divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> \<one>)"
    by blast
  have s_carr: "s \<in> carrier R"
    using s_in subset rev_subsetD by blast
  have "p divides\<^bsub>R\<^esub> s"
    using p_dvd_s s_carr by simp
  moreover have "\<not> p divides\<^bsub>R\<^esub> s"
    using havoid s_in unfolding ring_avoids_def by blast
  ultimately show False
    by contradiction
qed

lemma map_irreducible_not_unit:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and loc_dom: "domain rec_rng_of_frac"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
  shows "rng_to_rng_of_frac p \<notin> Units rec_rng_of_frac"
proof -
  have zero_notin: "\<zero> \<notin> S"
    using hS by (rule zero_notin_submonoid_of_prime_or_unit)
  show ?thesis
    using map_irreducible_not_unit_of_zero_notin[OF zero_notin loc_dom p_in hp havoid] .
qed

lemma localization_irreducible_of_irreducible:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and loc_dom: "domain rec_rng_of_frac"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
  shows "ring_irreducible\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
proof -
  interpret L: domain rec_rng_of_frac
    by (rule loc_dom)
  have zero_notin: "\<zero> \<notin> S"
    using hS by (rule zero_notin_submonoid_of_prime_or_unit)
  have map_p_in: "rng_to_rng_of_frac p \<in> carrier rec_rng_of_frac"
    by (rule ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in])
  have map_p_nz: "rng_to_rng_of_frac p \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    using map_eq_zero_iff[OF p_in zero_notin no_zero_divisors]
      ring_irreducibleE(1)[OF p_in hp]
    by blast
  have map_p_not_unit: "rng_to_rng_of_frac p \<notin> Units rec_rng_of_frac"
    using map_irreducible_not_unit[OF hS loc_dom p_in hp havoid] .
  show ?thesis
  proof (rule L.ring_irreducibleI)
    show "rng_to_rng_of_frac p \<in> carrier rec_rng_of_frac - {\<zero>\<^bsub>rec_rng_of_frac\<^esub>}"
      using map_p_in map_p_nz by blast
  next
    show "rng_to_rng_of_frac p \<notin> Units rec_rng_of_frac"
      using map_p_not_unit .
  next
    fix x y
    assume x_in: "x \<in> carrier rec_rng_of_frac"
      and y_in: "y \<in> carrier rec_rng_of_frac"
      and xy: "rng_to_rng_of_frac p = x \<otimes>\<^bsub>rec_rng_of_frac\<^esub> y"
    from fraction_surj[OF x_in] obtain a where a_in: "a \<in> carrier R"
      and hs: "\<exists>s \<in> S. x = (a |\<^bsub>rel\<^esub> s)"
      by blast
    from hs obtain s where s_in: "s \<in> S" and x_def: "x = (a |\<^bsub>rel\<^esub> s)"
      by blast
    from fraction_surj[OF y_in] obtain b where b_in: "b \<in> carrier R"
      and ht: "\<exists>t \<in> S. y = (b |\<^bsub>rel\<^esub> t)"
      by blast
    from ht obtain t where t_in: "t \<in> S" and y_def: "y = (b |\<^bsub>rel\<^esub> t)"
      by blast
    have as_rel: "(a, s) \<in> carrier rel"
      using a_in s_in by (simp add: rel_def)
    have bt_rel: "(b, t) \<in> carrier rel"
      using b_in t_in by (simp add: rel_def)
    have st_in: "s \<otimes>\<^bsub>R\<^esub> t \<in> S"
      using s_in t_in by simp
    have st_carrier: "s \<otimes>\<^bsub>R\<^esub> t \<in> carrier R"
      using st_in subset rev_subsetD by blast
    have p_rel: "(p, \<one>) \<in> carrier rel"
      using p_in one_closed by (simp add: rel_def)
    have ab_in: "a \<otimes>\<^bsub>R\<^esub> b \<in> carrier R"
      using a_in b_in by auto
    have ab_rel: "(a \<otimes>\<^bsub>R\<^esub> b, s \<otimes>\<^bsub>R\<^esub> t) \<in> carrier rel"
      using a_in b_in st_in by (simp add: rel_def)
    have frac_prod:
        "x \<otimes>\<^bsub>rec_rng_of_frac\<^esub> y = (a \<otimes>\<^bsub>R\<^esub> b |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> t)"
      using fraction_mult_rep[OF as_rel bt_rel] x_def y_def by simp
    have eq_frac:
        "rng_to_rng_of_frac p = (a \<otimes>\<^bsub>R\<^esub> b |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> t)"
      using xy frac_prod by (simp add: rng_to_rng_of_frac_def)
    have p_eq_raw: "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p = \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
    proof -
      have eq_cross:
          "rng_to_rng_of_frac p = (a \<otimes>\<^bsub>R\<^esub> b |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> t) \<longleftrightarrow>
            (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p = \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
        using fraction_eq_iff_cross_multiply[OF p_rel ab_rel zero_notin no_zero_divisors]
        unfolding rng_to_rng_of_frac_def by simp
      from eq_cross eq_frac show ?thesis
        by blast
    qed
    have p_eq: "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p = a \<otimes>\<^bsub>R\<^esub> b"
      using p_eq_raw ab_in by simp
    from hS[OF st_in] show "x \<in> Units rec_rng_of_frac \<or> y \<in> Units rec_rng_of_frac"
    proof
      assume hst_prime: "ring_prime\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> t)"
      have st_prime: "prime R (s \<otimes>\<^bsub>R\<^esub> t)"
        and st_nz: "s \<otimes>\<^bsub>R\<^esub> t \<noteq> \<zero>"
        using ring_primeE[OF st_carrier hst_prime] by auto
      have st_dvd_ab: "(s \<otimes>\<^bsub>R\<^esub> t) divides\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
      proof -
        have ab_eq: "a \<otimes>\<^bsub>R\<^esub> b = (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p"
          using p_eq by simp
        show ?thesis
          by (rule dividesI[OF p_in ab_eq])
      qed
      have st_dvd_a_or_b:
          "(s \<otimes>\<^bsub>R\<^esub> t) divides\<^bsub>R\<^esub> a \<or> (s \<otimes>\<^bsub>R\<^esub> t) divides\<^bsub>R\<^esub> b"
        using primeE[OF st_prime] a_in b_in st_dvd_ab by blast
      from st_dvd_a_or_b show ?thesis
      proof
        assume st_dvd_a: "(s \<otimes>\<^bsub>R\<^esub> t) divides\<^bsub>R\<^esub> a"
        then obtain d where d_in: "d \<in> carrier R" and hd: "a = (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> d"
          unfolding factor_def by blast
        have db_in: "d \<otimes>\<^bsub>R\<^esub> b \<in> carrier R"
          using d_in b_in by auto
        have "p = d \<otimes>\<^bsub>R\<^esub> b"
        proof -
          have "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p = a \<otimes>\<^bsub>R\<^esub> b"
            by (rule p_eq)
          also have "\<dots> = ((s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> d) \<otimes>\<^bsub>R\<^esub> b"
            using hd by simp
          also have "\<dots> = (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> (d \<otimes>\<^bsub>R\<^esub> b)"
            using st_carrier d_in b_in by (simp add: m_assoc)
          finally have "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p =
              (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> (d \<otimes>\<^bsub>R\<^esub> b)" .
          then show ?thesis
            using st_nz st_carrier p_in db_in by (simp add: m_lcancel)
        qed
        then have d_or_b_unit: "d \<in> Units R \<or> b \<in> Units R"
          using ring_irreducibleE(5)[OF p_in hp d_in b_in] by blast
        then show ?thesis
        proof
          assume d_unit: "d \<in> Units R"
          have t_in_carrier: "t \<in> carrier R"
            using t_in subset rev_subsetD by blast
          have td_in: "t \<otimes>\<^bsub>R\<^esub> d \<in> carrier R"
            using t_in_carrier d_in by auto
          have td_rel: "(t \<otimes>\<^bsub>R\<^esub> d, \<one>) \<in> carrier rel"
            using td_in one_closed by (simp add: rel_def)
          have x_eq_map_td: "x = rng_to_rng_of_frac (t \<otimes>\<^bsub>R\<^esub> d)"
          proof -
            have s_in_carrier: "s \<in> carrier R"
              using s_in subset rev_subsetD by blast
            have "x = (a |\<^bsub>rel\<^esub> s)"
              using x_def by simp
            also have "\<dots> = ((s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> d |\<^bsub>rel\<^esub> s)"
              using hd by (simp add: m_assoc)
            also have "\<dots> = (s \<otimes>\<^bsub>R\<^esub> (t \<otimes>\<^bsub>R\<^esub> d) |\<^bsub>rel\<^esub> s)"
              using s_in_carrier t_in_carrier d_in by (simp add: m_assoc)
            also have "\<dots> = (s \<otimes>\<^bsub>R\<^esub> (t \<otimes>\<^bsub>R\<^esub> d) |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> \<one>)"
              using s_in_carrier by simp
            also have "\<dots> = (t \<otimes>\<^bsub>R\<^esub> d |\<^bsub>rel\<^esub> \<one>)"
              using fraction_rescale[OF td_rel s_in] by simp
            also have "\<dots> = rng_to_rng_of_frac (t \<otimes>\<^bsub>R\<^esub> d)"
              by (simp add: rng_to_rng_of_frac_def)
            finally show ?thesis .
          qed
          have t_unit_loc: "rng_to_rng_of_frac t \<in> Units rec_rng_of_frac"
            using map_submonoid_elem_is_unit[OF t_in] .
          have d_unit_loc: "rng_to_rng_of_frac d \<in> Units rec_rng_of_frac"
            using map_unit_is_unit[OF d_unit] .
          have "rng_to_rng_of_frac (t \<otimes>\<^bsub>R\<^esub> d) =
              rng_to_rng_of_frac t \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac d"
            using ring_hom_mult[OF rng_to_rng_of_frac_is_ring_hom t_in_carrier d_in] .
          then show ?thesis
            using x_eq_map_td t_unit_loc d_unit_loc by simp
        next
          assume b_unit: "b \<in> Units R"
          have "(b |\<^bsub>rel\<^esub> t) \<in> Units rec_rng_of_frac"
            by (rule fraction_unit_numerator_is_unit[OF b_unit t_in])
          then show ?thesis
            using y_def by blast
        qed
      next
        assume st_dvd_b: "(s \<otimes>\<^bsub>R\<^esub> t) divides\<^bsub>R\<^esub> b"
        then obtain d where d_in: "d \<in> carrier R" and hd: "b = (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> d"
          unfolding factor_def by blast
        have ad_in: "a \<otimes>\<^bsub>R\<^esub> d \<in> carrier R"
          using a_in d_in by auto
        have "p = a \<otimes>\<^bsub>R\<^esub> d"
        proof -
          have "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p = a \<otimes>\<^bsub>R\<^esub> b"
            by (rule p_eq)
          also have "\<dots> = a \<otimes>\<^bsub>R\<^esub> ((s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> d)"
            using hd by simp
          also have "\<dots> = (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> d)"
            using st_carrier a_in d_in by (simp add: m_assoc m_comm m_lcomm)
          finally have "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p =
              (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> d)" .
          then show ?thesis
            using st_nz st_carrier p_in ad_in by (simp add: m_lcancel)
        qed
        then have a_or_d_unit: "a \<in> Units R \<or> d \<in> Units R"
          using ring_irreducibleE(5)[OF p_in hp a_in d_in] by blast
        then show ?thesis
        proof
          assume a_unit: "a \<in> Units R"
          have "(a |\<^bsub>rel\<^esub> s) \<in> Units rec_rng_of_frac"
            by (rule fraction_unit_numerator_is_unit[OF a_unit s_in])
          then show ?thesis
            using x_def by blast
        next
          assume d_unit: "d \<in> Units R"
          have s_in_carrier: "s \<in> carrier R"
            using s_in subset rev_subsetD by blast
          have sd_in: "s \<otimes>\<^bsub>R\<^esub> d \<in> carrier R"
            using s_in_carrier d_in by auto
          have sd_rel: "(s \<otimes>\<^bsub>R\<^esub> d, \<one>) \<in> carrier rel"
            using sd_in one_closed by (simp add: rel_def)
          have y_eq_map_sd: "y = rng_to_rng_of_frac (s \<otimes>\<^bsub>R\<^esub> d)"
          proof -
            have t_in_carrier: "t \<in> carrier R"
              using t_in subset rev_subsetD by blast
            have "y = (b |\<^bsub>rel\<^esub> t)"
              using y_def by simp
            also have "\<dots> = ((s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> d |\<^bsub>rel\<^esub> t)"
              using hd by (simp add: m_assoc)
            also have "\<dots> = (t \<otimes>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> d) |\<^bsub>rel\<^esub> t)"
              using t_in_carrier s_in_carrier d_in by (simp add: m_assoc m_comm m_lcomm)
            also have "\<dots> = (t \<otimes>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> d) |\<^bsub>rel\<^esub> t \<otimes>\<^bsub>R\<^esub> \<one>)"
              using t_in_carrier by simp
            also have "\<dots> = (s \<otimes>\<^bsub>R\<^esub> d |\<^bsub>rel\<^esub> \<one>)"
              using fraction_rescale[OF sd_rel t_in] by simp
            also have "\<dots> = rng_to_rng_of_frac (s \<otimes>\<^bsub>R\<^esub> d)"
              by (simp add: rng_to_rng_of_frac_def)
            finally show ?thesis .
          qed
          have s_unit_loc: "rng_to_rng_of_frac s \<in> Units rec_rng_of_frac"
            using map_submonoid_elem_is_unit[OF s_in] .
          have d_unit_loc: "rng_to_rng_of_frac d \<in> Units rec_rng_of_frac"
            using map_unit_is_unit[OF d_unit] .
          have "rng_to_rng_of_frac (s \<otimes>\<^bsub>R\<^esub> d) =
              rng_to_rng_of_frac s \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac d"
            using ring_hom_mult[OF rng_to_rng_of_frac_is_ring_hom s_in_carrier d_in] .
          then show ?thesis
            using y_eq_map_sd s_unit_loc d_unit_loc by simp
        qed
      qed
    next
      assume hst_unit: "s \<otimes>\<^bsub>R\<^esub> t \<in> Units R"
      have ab_assoc_p: "(a \<otimes>\<^bsub>R\<^esub> b) \<sim>\<^bsub>R\<^esub> p"
      proof -
        have "a \<otimes>\<^bsub>R\<^esub> b = (s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p"
          using p_eq by simp
        also have "\<dots> = p \<otimes>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> t)"
          using p_in Units_closed[OF hst_unit] by (simp add: m_assoc m_comm m_lcomm)
        finally have "a \<otimes>\<^bsub>R\<^esub> b = p \<otimes>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> t)" .
        then show ?thesis
          using hst_unit p_in by (rule associatedI2')
      qed
      have p_mult_irreducible: "irreducible (mult_of R) p"
        using ring_irreducibleE(3)[OF p_in hp] .
      have p_assoc_ab_mult: "p \<sim>\<^bsub>mult_of R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
        using assoc_iff_assoc_mult[OF p_in ab_in] associated_sym[OF ab_assoc_p] by blast
      have st_carr: "s \<otimes>\<^bsub>R\<^esub> t \<in> carrier R"
        using Units_closed[OF hst_unit] .
      have st_nz: "s \<otimes>\<^bsub>R\<^esub> t \<noteq> \<zero>"
        using st_in zero_notin by auto
      have p_nz: "p \<noteq> \<zero>"
        using ring_irreducibleE(1)[OF p_in hp] .
      have ab_nz: "a \<otimes>\<^bsub>R\<^esub> b \<noteq> \<zero>"
        using ab_assoc_p divides_cong_r p_nz zero_divides by blast
      have a_nz: "a \<noteq> \<zero>"
        using ab_nz b_in by fastforce
      have b_nz: "b \<noteq> \<zero>"
        using a_in ab_nz by force
      have a_in_mult: "a \<in> carrier (mult_of R)"
        using a_in a_nz by simp
      have b_in_mult: "b \<in> carrier (mult_of R)"
        using b_in b_nz by simp
      have ab_mult_irreducible: "irreducible (mult_of R) (a \<otimes>\<^bsub>R\<^esub> b)"
      proof (rule mult_of.irreducible_cong[OF p_mult_irreducible p_assoc_ab_mult])
        show "p \<in> carrier (mult_of R)"
          using p_in p_nz by simp
        show "(a \<otimes>\<^bsub>R\<^esub> b) \<in> carrier (mult_of R)"
          using ab_in ab_nz by simp
      qed
      have xy_unit: "x \<in> Units rec_rng_of_frac \<or> y \<in> Units rec_rng_of_frac"
      proof (rule mult_of.irreducible_prodE[OF ab_mult_irreducible a_in_mult b_in_mult])
        assume a_irreducible: "irreducible (mult_of R) a" and b_unit_mult: "b \<in> Units (mult_of R)"
        have b_unit: "b \<in> Units R"
          using b_unit_mult by simp
        have y_unit: "y \<in> Units rec_rng_of_frac"
          unfolding y_def using fraction_unit_numerator_is_unit[OF b_unit t_in] by blast
        show "x \<in> Units rec_rng_of_frac \<or> y \<in> Units rec_rng_of_frac"
          using y_unit by auto
      next
        assume a_unit_mult: "a \<in> Units (mult_of R)" and b_irreducible: "irreducible (mult_of R) b"
        have a_unit: "a \<in> Units R"
          using a_unit_mult by simp
        have x_unit: "x \<in> Units rec_rng_of_frac"
          unfolding x_def using fraction_unit_numerator_is_unit[OF a_unit s_in] by blast
        show "x \<in> Units rec_rng_of_frac \<or> y \<in> Units rec_rng_of_frac"
          by (simp add: x_unit)
      qed
      then show ?thesis .
    qed
  qed
qed

lemma nagata_key_lemma:
  assumes hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and loc_fd: "factorial_domain rec_rng_of_frac"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof (cases "\<exists>s \<in> S. p divides\<^bsub>R\<^esub> s")
  case True
  then obtain s where s_in: "s \<in> S" and p_dvd_s: "p divides\<^bsub>R\<^esub> s"
    by blast
  show ?thesis
    using prime_of_irreducible_of_dvd_mem[OF hS p_in hp s_in p_dvd_s] .
next
  case False
  interpret Lfd: factorial_domain rec_rng_of_frac
    by (rule loc_fd)
  interpret L: domain rec_rng_of_frac
    by (rule Lfd.domain_axioms)
  have havoid: "ring_avoids R S p"
    using False unfolding ring_avoids_def by blast
  have loc_irreducible: "ring_irreducible\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
    using localization_irreducible_of_irreducible[OF hS Lfd.domain_axioms p_in hp havoid] .
  have loc_irred_mult: "irreducible (mult_of rec_rng_of_frac) (rng_to_rng_of_frac p)"
    using Lfd.ring_irreducibleE(3)[OF ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in] loc_irreducible] .
  have loc_in_nz: "rng_to_rng_of_frac p \<in> carrier rec_rng_of_frac - {\<zero>\<^bsub>rec_rng_of_frac\<^esub>}"
    using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in]
      Lfd.ring_irreducibleE(1)[OF ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in] loc_irreducible]
    by blast
  have loc_in_mult: "rng_to_rng_of_frac p \<in> carrier (mult_of rec_rng_of_frac)"
    using loc_in_nz by simp
  have loc_prime_mult: "prime (mult_of rec_rng_of_frac) (rng_to_rng_of_frac p)"
    by (rule factorial_monoid.irreducible_prime[OF Lfd.factorial_monoid_axioms loc_irred_mult loc_in_mult])
  have loc_ring_prime: "ring_prime\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
    using Lfd.ring_primeI'[OF loc_in_nz loc_prime_mult] .
  show ?thesis
    using prime_of_localization_prime[OF hS p_in hp havoid loc_ring_prime] .
qed

(* This prime-generated factor-splitting block is one of the slower proof steps
   in the session because it performs an explicit inductive redistribution of
   localized prime factors across both sides of the target factorization. *)
lemma split_prime_factors_of_mul_eq:
  assumes fs_sub: "set fs \<subseteq> S"
    and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
    and p_in: "p \<in> carrier R"
    and a_in: "a \<in> carrier R"
    and b_in: "b \<in> carrier R"
    and hEq: "p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = a \<otimes>\<^bsub>R\<^esub> b"
  shows "\<exists>fs1 fs2 a' b'.
      fs <~~> fs1 @ fs2 \<and>
      set fs1 \<subseteq> S \<and> (\<forall>q\<in>set fs1. ring_prime\<^bsub>R\<^esub> q) \<and>
      set fs2 \<subseteq> S \<and> (\<forall>q\<in>set fs2. ring_prime\<^bsub>R\<^esub> q) \<and>
      a' \<in> carrier R \<and> b' \<in> carrier R \<and>
      a = foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a' \<and>
      b = foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b' \<and>
      p = a' \<otimes>\<^bsub>R\<^esub> b'"
  using fs_sub hf p_in a_in b_in hEq
proof (induction fs arbitrary: a b)
  case Nil
  have hpab_eq: "p \<otimes>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub> = a \<otimes>\<^bsub>R\<^esub> b"
    using Nil.prems(6) by simp
  have hpab: "p = a \<otimes>\<^bsub>R\<^esub> b"
    using Nil.prems(3) hpab_eq by simp
  show ?case
  proof (intro exI conjI)
    show "[] <~~> [] @ []"
      by simp
    show "set [] \<subseteq> S"
      by simp
    show "\<forall>q\<in>set []. ring_prime\<^bsub>R\<^esub> q"
      by simp
    show "set [] \<subseteq> S"
      by simp
    show "\<forall>q\<in>set []. ring_prime\<^bsub>R\<^esub> q"
      by simp
    show "a \<in> carrier R"
      by (rule Nil.prems(4))
    show "b \<in> carrier R"
      by (rule Nil.prems(5))
    show "a = foldr (\<otimes>\<^bsub>R\<^esub>) [] \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a"
      using Nil.prems(4) by simp
    show "b = foldr (\<otimes>\<^bsub>R\<^esub>) [] \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b"
      using Nil.prems(5) by simp
    show "p = a \<otimes>\<^bsub>R\<^esub> b"
      by (rule hpab)
  qed
next
  case (Cons q qs)
  have q_in: "q \<in> S"
    using Cons.prems(1) by simp
  have q_carr: "q \<in> carrier R"
    using q_in subset rev_subsetD by blast
  have q_ring_prime: "ring_prime\<^bsub>R\<^esub> q"
    using Cons.prems(2) by simp
  have q_prime: "prime R q"
    using ring_primeE(3)[OF q_carr q_ring_prime] .
  have q_nz: "q \<noteq> \<zero>"
    using ring_primeE(1)[OF q_carr q_ring_prime] .
  have qs_sub: "set qs \<subseteq> S"
    using Cons.prems(1) by simp
  have qs_prime: "\<forall>r\<in>set qs. ring_prime\<^bsub>R\<^esub> r"
    using Cons.prems(2) by simp
  have qs_carr: "set qs \<subseteq> carrier R"
    using qs_sub subset by blast
  have rest_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<in> carrier R"
    by (rule multlist_closed[OF qs_carr])
  have prest_carr: "p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> \<in> carrier R"
    using Cons.prems(3) rest_carr by auto
  have q_dvd_ab: "q divides\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
  proof -
    have hEq_cons: "p \<otimes>\<^bsub>R\<^esub> (q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) = a \<otimes>\<^bsub>R\<^esub> b"
      using Cons.prems(6) by simp
    have "q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) =
        p \<otimes>\<^bsub>R\<^esub> (q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>)"
      using Cons.prems(3) q_carr rest_carr by (simp add: m_assoc m_comm m_lcomm)
    also have "\<dots> = a \<otimes>\<^bsub>R\<^esub> b"
      using hEq_cons .
    finally have "q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) = a \<otimes>\<^bsub>R\<^esub> b" .
    then have ab_eq: "a \<otimes>\<^bsub>R\<^esub> b =
        q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>)"
      by simp
    show ?thesis
      by (rule dividesI[OF prest_carr ab_eq])
  qed
  have q_dvd_a_or_b: "q divides\<^bsub>R\<^esub> a \<or> q divides\<^bsub>R\<^esub> b"
    using primeE[OF q_prime] Cons.prems(4) Cons.prems(5) q_dvd_ab by blast
  from q_dvd_a_or_b show ?case
  proof
    assume q_dvd_a: "q divides\<^bsub>R\<^esub> a"
    obtain a1 where a1_in: "a1 \<in> carrier R" and ha1: "a = q \<otimes>\<^bsub>R\<^esub> a1"
      using q_dvd_a unfolding factor_def by blast
    have a1b_carr: "a1 \<otimes>\<^bsub>R\<^esub> b \<in> carrier R"
      using a1_in Cons.prems(5) by auto
    have hEq': "p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> = a1 \<otimes>\<^bsub>R\<^esub> b"
    proof -
      have "q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) =
          p \<otimes>\<^bsub>R\<^esub> (q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>)"
        using Cons.prems(3) q_carr rest_carr by (simp add: m_assoc m_comm m_lcomm)
      also have "\<dots> = a \<otimes>\<^bsub>R\<^esub> b"
        using Cons.prems(6) by simp
      also have "\<dots> = (q \<otimes>\<^bsub>R\<^esub> a1) \<otimes>\<^bsub>R\<^esub> b"
        using ha1 by simp
      also have "\<dots> = q \<otimes>\<^bsub>R\<^esub> (a1 \<otimes>\<^bsub>R\<^esub> b)"
        using q_carr a1_in Cons.prems(5) by (simp add: m_assoc)
      finally have "q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) =
          q \<otimes>\<^bsub>R\<^esub> (a1 \<otimes>\<^bsub>R\<^esub> b)" .
      then show ?thesis
        using q_nz q_carr prest_carr a1b_carr by (simp add: m_lcancel)
    qed
    obtain fs1 fs2 a' b' where
        part: "qs <~~> fs1 @ fs2"
        and fs1_sub: "set fs1 \<subseteq> S"
        and fs1_prime: "\<forall>r\<in>set fs1. ring_prime\<^bsub>R\<^esub> r"
        and fs2_sub: "set fs2 \<subseteq> S"
        and fs2_prime: "\<forall>r\<in>set fs2. ring_prime\<^bsub>R\<^esub> r"
        and a'_in: "a' \<in> carrier R"
        and b'_in: "b' \<in> carrier R"
        and ha: "a1 = foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a'"
        and hb: "b = foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b'"
        and hp': "p = a' \<otimes>\<^bsub>R\<^esub> b'"
      using Cons.IH[OF qs_sub qs_prime Cons.prems(3) a1_in Cons.prems(5) hEq'] by blast
    show ?thesis
    proof (intro exI conjI)
      show "q # qs <~~> (q # fs1) @ fs2"
        using part by simp
      show "set (q # fs1) \<subseteq> S"
        using q_in fs1_sub by simp
      show "\<forall>r\<in>set (q # fs1). ring_prime\<^bsub>R\<^esub> r"
        using q_ring_prime fs1_prime by simp
      show "set fs2 \<subseteq> S"
        by (rule fs2_sub)
      show "\<forall>r\<in>set fs2. ring_prime\<^bsub>R\<^esub> r"
        by (rule fs2_prime)
      show "a' \<in> carrier R"
        by (rule a'_in)
      show "b' \<in> carrier R"
        by (rule b'_in)
      show "a = foldr (\<otimes>\<^bsub>R\<^esub>) (q # fs1) \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a'"
      proof -
        have fs1_carr: "set fs1 \<subseteq> carrier R"
          using fs1_sub subset by blast
        have fs1_prod_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<in> carrier R"
          by (rule multlist_closed[OF fs1_carr])
        have "a = q \<otimes>\<^bsub>R\<^esub> a1"
          by (rule ha1)
        also have "\<dots> = q \<otimes>\<^bsub>R\<^esub> (foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a')"
          using ha by simp
        also have "\<dots> = (q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>R\<^esub> a'"
          using q_carr fs1_prod_carr a'_in by (simp add: m_assoc)
        also have "\<dots> = foldr (\<otimes>\<^bsub>R\<^esub>) (q # fs1) \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a'"
          by simp
        finally show ?thesis .
      qed
      show "b = foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b'"
        by (rule hb)
      show "p = a' \<otimes>\<^bsub>R\<^esub> b'"
        by (rule hp')
    qed
  next
    assume q_dvd_b: "q divides\<^bsub>R\<^esub> b"
    obtain b1 where b1_in: "b1 \<in> carrier R" and hb1: "b = q \<otimes>\<^bsub>R\<^esub> b1"
      using q_dvd_b unfolding factor_def by blast
    have ab1_carr: "a \<otimes>\<^bsub>R\<^esub> b1 \<in> carrier R"
      using Cons.prems(4) b1_in by auto
    have hEq': "p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub> = a \<otimes>\<^bsub>R\<^esub> b1"
    proof -
      have "q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) =
          p \<otimes>\<^bsub>R\<^esub> (q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>)"
        using Cons.prems(3) q_carr rest_carr by (simp add: m_assoc m_comm m_lcomm)
      also have "\<dots> = a \<otimes>\<^bsub>R\<^esub> b"
        using Cons.prems(6) by simp
      also have "\<dots> = a \<otimes>\<^bsub>R\<^esub> (q \<otimes>\<^bsub>R\<^esub> b1)"
        using hb1 by simp
      also have "\<dots> = q \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b1)"
        using q_carr Cons.prems(4) b1_in by (simp add: m_assoc m_comm m_lcomm)
      finally have "q \<otimes>\<^bsub>R\<^esub> (p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) qs \<one>\<^bsub>R\<^esub>) =
          q \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b1)" .
      then show ?thesis
        using q_nz q_carr prest_carr ab1_carr by (simp add: m_lcancel)
    qed
    obtain fs1 fs2 a' b' where
        part: "qs <~~> fs1 @ fs2"
        and fs1_sub: "set fs1 \<subseteq> S"
        and fs1_prime: "\<forall>r\<in>set fs1. ring_prime\<^bsub>R\<^esub> r"
        and fs2_sub: "set fs2 \<subseteq> S"
        and fs2_prime: "\<forall>r\<in>set fs2. ring_prime\<^bsub>R\<^esub> r"
        and a'_in: "a' \<in> carrier R"
        and b'_in: "b' \<in> carrier R"
        and ha: "a = foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a'"
        and hb: "b1 = foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b'"
        and hp': "p = a' \<otimes>\<^bsub>R\<^esub> b'"
      using Cons.IH[OF qs_sub qs_prime Cons.prems(3) Cons.prems(4) b1_in hEq'] by blast
    show ?thesis
    proof (intro exI conjI)
      show "q # qs <~~> fs1 @ (q # fs2)"
        using part by simp
      show "set fs1 \<subseteq> S"
        by (rule fs1_sub)
      show "\<forall>r\<in>set fs1. ring_prime\<^bsub>R\<^esub> r"
        by (rule fs1_prime)
      show "set (q # fs2) \<subseteq> S"
        using q_in fs2_sub by simp
      show "\<forall>r\<in>set (q # fs2). ring_prime\<^bsub>R\<^esub> r"
        using q_ring_prime fs2_prime by simp
      show "a' \<in> carrier R"
        by (rule a'_in)
      show "b' \<in> carrier R"
        by (rule b'_in)
      show "a = foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a'"
        by (rule ha)
      show "b = foldr (\<otimes>\<^bsub>R\<^esub>) (q # fs2) \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b'"
      proof -
        have fs2_carr: "set fs2 \<subseteq> carrier R"
          using fs2_sub subset by blast
        have fs2_prod_carr: "foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<in> carrier R"
          by (rule multlist_closed[OF fs2_carr])
        have "b = q \<otimes>\<^bsub>R\<^esub> b1"
          by (rule hb1)
        also have "\<dots> = q \<otimes>\<^bsub>R\<^esub> (foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b')"
          using hb by simp
        also have "\<dots> = (q \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>R\<^esub> b'"
          using q_carr fs2_prod_carr b'_in by (simp add: m_assoc)
        also have "\<dots> = foldr (\<otimes>\<^bsub>R\<^esub>) (q # fs2) \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b'"
          by simp
        finally show ?thesis .
      qed
      show "p = a' \<otimes>\<^bsub>R\<^esub> b'"
        by (rule hp')
    qed
  qed
qed

lemma localization_irreducible_of_irreducible_prime_generated:
  assumes hS: "ring_prime_generated R S"
    and loc_dom: "domain rec_rng_of_frac"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
  shows "ring_irreducible\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
proof -
  interpret L: domain rec_rng_of_frac
    by (rule loc_dom)
  have zero_notin: "\<zero> \<notin> S"
    using zero_notin_submonoid_of_prime_generated[OF hS] .
  have map_p_in: "rng_to_rng_of_frac p \<in> carrier rec_rng_of_frac"
    by (rule ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in])
  have map_p_nz: "rng_to_rng_of_frac p \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    using map_eq_zero_iff[OF p_in zero_notin no_zero_divisors]
      ring_irreducibleE(1)[OF p_in hp]
    by blast
  have map_p_not_unit: "rng_to_rng_of_frac p \<notin> Units rec_rng_of_frac"
    using map_irreducible_not_unit_of_zero_notin[OF zero_notin loc_dom p_in hp havoid] by blast
  show ?thesis
  proof (rule L.ring_irreducibleI)
    show "rng_to_rng_of_frac p \<in> carrier rec_rng_of_frac - {\<zero>\<^bsub>rec_rng_of_frac\<^esub>}"
      using map_p_in map_p_nz by blast
    show "rng_to_rng_of_frac p \<notin> Units rec_rng_of_frac"
      by (rule map_p_not_unit)
    fix x y
    assume x_in: "x \<in> carrier rec_rng_of_frac"
      and y_in: "y \<in> carrier rec_rng_of_frac"
      and xy: "rng_to_rng_of_frac p = x \<otimes>\<^bsub>rec_rng_of_frac\<^esub> y"
    from fraction_surj[OF x_in] obtain a where
        a_in: "a \<in> carrier R"
        and hs: "\<exists>s \<in> S. x = (a |\<^bsub>rel\<^esub> s)"
      by blast
    from hs obtain s where
        s_in: "s \<in> S"
        and x_def: "x = (a |\<^bsub>rel\<^esub> s)"
      by blast
    from fraction_surj[OF y_in] obtain b where
        b_in: "b \<in> carrier R"
        and ht: "\<exists>t \<in> S. y = (b |\<^bsub>rel\<^esub> t)"
      by blast
    from ht obtain t where
        t_in: "t \<in> S"
        and y_def: "y = (b |\<^bsub>rel\<^esub> t)"
      by blast
    have s_carr: "s \<in> carrier R"
      using s_in subset rev_subsetD by blast
    have t_carr: "t \<in> carrier R"
      using t_in subset rev_subsetD by blast
    have st_in: "s \<otimes>\<^bsub>R\<^esub> t \<in> S"
      using s_in t_in by (simp add: m_closed)
    obtain fs where
        fs_sub: "set fs \<subseteq> S"
        and hf: "\<forall>q\<in>set fs. ring_prime\<^bsub>R\<^esub> q"
        and hprod: "foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = s \<otimes>\<^bsub>R\<^esub> t"
      using ring_prime_generatedE[OF hS st_in] by blast
    have p_rel: "(p, \<one>) \<in> carrier rel"
      using p_in one_closed by (simp add: rel_def)
    have as_rel: "(a, s) \<in> carrier rel"
      using a_in s_in by (simp add: rel_def)
    have bt_rel: "(b, t) \<in> carrier rel"
      using b_in t_in by (simp add: rel_def)
    have ab_rel: "(a \<otimes>\<^bsub>R\<^esub> b, s \<otimes>\<^bsub>R\<^esub> t) \<in> carrier rel"
      using a_in b_in s_in t_in by (simp add: rel_def)
    have frac_prod: "x \<otimes>\<^bsub>rec_rng_of_frac\<^esub> y = (a \<otimes>\<^bsub>R\<^esub> b |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> t)"
      using fraction_mult_rep[OF as_rel bt_rel] x_def y_def by simp
    have eq_frac: "rng_to_rng_of_frac p = (a \<otimes>\<^bsub>R\<^esub> b |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> t)"
      using xy frac_prod by (simp add: rng_to_rng_of_frac_def)
    have hEq_cross_raw: "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p =
        \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
      using fraction_eq_iff_cross_multiply[OF p_rel ab_rel zero_notin no_zero_divisors] eq_frac
      unfolding rng_to_rng_of_frac_def by simp
    have hEq_cross: "(s \<otimes>\<^bsub>R\<^esub> t) \<otimes>\<^bsub>R\<^esub> p = a \<otimes>\<^bsub>R\<^esub> b"
      using hEq_cross_raw a_in b_in by simp
    have hEq: "p \<otimes>\<^bsub>R\<^esub> foldr (\<otimes>\<^bsub>R\<^esub>) fs \<one>\<^bsub>R\<^esub> = a \<otimes>\<^bsub>R\<^esub> b"
      using hEq_cross hprod m_comm p_in s_carr t_carr by auto
    obtain fs1 fs2 a' b' where
        part: "fs <~~> fs1 @ fs2"
        and fs1_sub: "set fs1 \<subseteq> S"
        and fs1_prime: "\<forall>q\<in>set fs1. ring_prime\<^bsub>R\<^esub> q"
        and fs2_sub: "set fs2 \<subseteq> S"
        and fs2_prime: "\<forall>q\<in>set fs2. ring_prime\<^bsub>R\<^esub> q"
        and a'_in: "a' \<in> carrier R"
        and b'_in: "b' \<in> carrier R"
        and ha: "a = foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> a'"
        and hb: "b = foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> b'"
        and hpab: "p = a' \<otimes>\<^bsub>R\<^esub> b'"
      using split_prime_factors_of_mul_eq[OF fs_sub hf p_in a_in b_in hEq] by blast
    have fs1_carr: "set fs1 \<subseteq> carrier R"
      using fs1_sub subset by blast
    have fs2_carr: "set fs2 \<subseteq> carrier R"
      using fs2_sub subset by blast
    have prod1_in: "foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<in> carrier R"
      by (rule multlist_closed[OF fs1_carr])
    have prod2_in: "foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<in> carrier R"
      by (rule multlist_closed[OF fs2_carr])
    have prod1_mem: "foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub> \<in> S"
      using multlist_mem_submonoid[OF fs1_sub] .
    have prod2_mem: "foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub> \<in> S"
      using multlist_mem_submonoid[OF fs2_sub] .
    have a's_rel: "(a', s) \<in> carrier rel"
      using a'_in s_in by (simp add: rel_def)
    have b't_rel: "(b', t) \<in> carrier rel"
      using b'_in t_in by (simp add: rel_def)
    have x_eq:
        "x = rng_to_rng_of_frac (foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (a' |\<^bsub>rel\<^esub> s)"
      by (simp add: a's_rel ha map_mul_fraction prod1_in x_def)
    have y_eq:
        "y = rng_to_rng_of_frac (foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (b' |\<^bsub>rel\<^esub> t)"
      using b't_rel hb map_mul_fraction prod2_in y_def by presburger
    have a'_unit_or_b'_unit: "a' \<in> Units R \<or> b' \<in> Units R"
      using ring_irreducibleE(5)[OF p_in hp a'_in b'_in] hpab by blast
    then show "x \<in> Units rec_rng_of_frac \<or> y \<in> Units rec_rng_of_frac"
    proof
      assume a'_unit: "a' \<in> Units R"
      have prod1_unit: "rng_to_rng_of_frac (foldr (\<otimes>\<^bsub>R\<^esub>) fs1 \<one>\<^bsub>R\<^esub>) \<in> Units rec_rng_of_frac"
        using map_submonoid_elem_is_unit[OF prod1_mem] .
      have frac1_unit: "(a' |\<^bsub>rel\<^esub> s) \<in> Units rec_rng_of_frac"
        by (rule fraction_unit_numerator_is_unit[OF a'_unit s_in])
      show ?thesis
        using x_eq prod1_unit frac1_unit by simp
    next
      assume b'_unit: "b' \<in> Units R"
      have prod2_unit: "rng_to_rng_of_frac (foldr (\<otimes>\<^bsub>R\<^esub>) fs2 \<one>\<^bsub>R\<^esub>) \<in> Units rec_rng_of_frac"
        using map_submonoid_elem_is_unit[OF prod2_mem] .
      have frac2_unit: "(b' |\<^bsub>rel\<^esub> t) \<in> Units rec_rng_of_frac"
        by (rule fraction_unit_numerator_is_unit[OF b'_unit t_in])
      show ?thesis
        using y_eq prod2_unit frac2_unit by simp
    qed
  qed
qed

lemma prime_of_localization_prime_prime_generated:
  assumes hS: "ring_prime_generated R S"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
    and havoid: "ring_avoids R S p"
    and hploc: "ring_prime\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof -
  have p_nz: "p \<noteq> \<zero>"
    using ring_irreducibleE(1)[OF p_in hp] .
  have hloc_prime: "prime rec_rng_of_frac (rng_to_rng_of_frac p)"
    using hploc unfolding ring_prime_def by simp
  have p_prime: "prime R p"
  proof (rule primeI)
    show "p \<notin> Units R"
      using ring_irreducibleE(4)[OF p_in hp] .
    fix a b
    assume a_in: "a \<in> carrier R"
      and b_in: "b \<in> carrier R"
      and hdiv: "p divides\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b)"
    then obtain d where d_in: "d \<in> carrier R" and hfactor: "a \<otimes>\<^bsub>R\<^esub> b = p \<otimes>\<^bsub>R\<^esub> d"
      unfolding factor_def by blast
    then have map_p_dvd_ab:
        "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub>
          (rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b)"
      by (smt (verit, del_insts) a_in b_in dividesI p_in ring_hom_closed ring_hom_mult 
            rng_to_rng_of_frac_is_ring_hom)
    have map_a_in: "rng_to_rng_of_frac a \<in> carrier rec_rng_of_frac"
      using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom a_in] .
    have map_b_in: "rng_to_rng_of_frac b \<in> carrier rec_rng_of_frac"
      using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom b_in] .
    have map_p_dvd_a_or_b:
        "rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a \<or>
         rng_to_rng_of_frac p divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b"
      by (meson hloc_prime map_a_in map_b_in map_p_dvd_ab primeE)
    then show "p divides\<^bsub>R\<^esub> a \<or> p divides\<^bsub>R\<^esub> b"
      using dvd_of_localization_dvd_prime_generated[OF hS p_in a_in hp havoid]
        dvd_of_localization_dvd_prime_generated[OF hS p_in b_in hp havoid]
      by blast
  qed
  from p_nz p_prime show ?thesis
    by (rule ring_primeI)
qed

lemma nagata_key_lemma_prime_generated:
  assumes hS: "ring_prime_generated R S"
    and loc_fd: "factorial_domain rec_rng_of_frac"
    and p_in: "p \<in> carrier R"
    and hp: "ring_irreducible\<^bsub>R\<^esub> p"
  shows "ring_prime\<^bsub>R\<^esub> p"
proof (cases "\<exists>s \<in> S. p divides\<^bsub>R\<^esub> s")
  case True
  then obtain s where s_in: "s \<in> S" and p_dvd_s: "p divides\<^bsub>R\<^esub> s"
    by blast
  show ?thesis
    using prime_of_irreducible_of_dvd_mem_prime_generated[OF hS p_in hp s_in p_dvd_s] .
next
  case False
  interpret Lfd: factorial_domain rec_rng_of_frac
    by (rule loc_fd)
  interpret L: domain rec_rng_of_frac
    by (rule Lfd.domain_axioms)
  have havoid: "ring_avoids R S p"
    using False unfolding ring_avoids_def by blast
  have loc_irreducible: "ring_irreducible\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
    using localization_irreducible_of_irreducible_prime_generated[OF hS Lfd.domain_axioms p_in hp havoid] .
  have loc_irred_mult: "irreducible (mult_of rec_rng_of_frac) (rng_to_rng_of_frac p)"
    using Lfd.ring_irreducibleE(3)[OF ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in] loc_irreducible] .
  have loc_in_nz: "rng_to_rng_of_frac p \<in> carrier rec_rng_of_frac - {\<zero>\<^bsub>rec_rng_of_frac\<^esub>}"
    using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in]
      Lfd.ring_irreducibleE(1)[OF ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom p_in] loc_irreducible]
    by blast
  have loc_in_mult: "rng_to_rng_of_frac p \<in> carrier (mult_of rec_rng_of_frac)"
    using loc_in_nz by simp
  have loc_prime_mult: "prime (mult_of rec_rng_of_frac) (rng_to_rng_of_frac p)"
    by (rule factorial_monoid.irreducible_prime[OF Lfd.factorial_monoid_axioms loc_irred_mult loc_in_mult])
  have loc_ring_prime: "ring_prime\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac p)"
    using Lfd.ring_primeI'[OF loc_in_nz loc_prime_mult] .
  show ?thesis
    using prime_of_localization_prime_prime_generated[OF hS p_in hp havoid loc_ring_prime] .
qed

lemma nagata_theorem:
  assumes noeth: "noetherian_domain R"
    and hS: "ring_prime_generated R S"
    and loc_fd: "factorial_domain rec_rng_of_frac"
  shows "factorial_domain R"
proof -
  interpret N: noetherian_domain R
    by (rule noeth)
  interpret PC: primeness_condition_monoid "mult_of R"
  proof
    fix a
    assume a_in: "a \<in> carrier (mult_of R)"
      and a_irred: "irreducible (mult_of R) a"
    have a_in_R: "a \<in> carrier R - {\<zero>}"
      using a_in by simp
    have a_ring_irred: "ring_irreducible\<^bsub>R\<^esub> a"
      using ring_irreducibleI'[OF a_in_R a_irred] .
    have a_prime: "ring_prime\<^bsub>R\<^esub> a"
      using nagata_key_lemma_prime_generated[OF hS loc_fd DiffD1[OF a_in_R] a_ring_irred] .
    have a_prime_mult: "prime (mult_of R) a"
      using ring_primeE(2)[OF DiffD1[OF a_in_R] a_prime] .
    show "prime (mult_of R) a"
      by (rule a_prime_mult)
  qed
  have wfactors_exist_mult:
      "\<And>a. \<lbrakk>a \<in> carrier (mult_of R); a \<notin> Units (mult_of R)\<rbrakk> \<Longrightarrow>
        \<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs a"
  proof -
    fix a
    assume a_in: "a \<in> carrier (mult_of R)"
      and a_not_unit: "a \<notin> Units (mult_of R)"
    have a_in_R: "a \<in> carrier R - {\<zero>}"
      using a_in by simp
    have a_not_unit_R: "a \<notin> Units R"
      using a_not_unit by simp
    show "\<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs a"
      using N.factorization_property[OF a_in_R a_not_unit_R] .
  qed
  have factorial_mult: "factorial_monoid (mult_of R)"
    by (rule mult_of.factorial_monoidI[OF wfactors_exist_mult PC.wfactors_unique])
  show ?thesis
    unfolding factorial_domain_def using domain_axioms factorial_mult by simp
qed

lemma nagata_theorem_of_prime_or_unit:
  assumes noeth: "noetherian_domain R"
    and hS: "\<And>s. s \<in> S \<Longrightarrow> ring_prime\<^bsub>R\<^esub> s \<or> s \<in> Units R"
    and loc_fd: "factorial_domain rec_rng_of_frac"
  shows "factorial_domain R"
proof -
  interpret N: noetherian_domain R
    by (rule noeth)
  interpret PC: primeness_condition_monoid "mult_of R"
  proof
    fix a
    assume a_in: "a \<in> carrier (mult_of R)"
      and a_irred: "irreducible (mult_of R) a"
    have a_in_R: "a \<in> carrier R - {\<zero>}"
      using a_in by simp
    have a_ring_irred: "ring_irreducible\<^bsub>R\<^esub> a"
      using ring_irreducibleI'[OF a_in_R a_irred] .
    have a_ring_prime: "ring_prime\<^bsub>R\<^esub> a"
      using nagata_key_lemma[OF hS loc_fd DiffD1[OF a_in_R] a_ring_irred] .
    show "prime (mult_of R) a"
      using ring_primeE(2)[OF DiffD1[OF a_in_R] a_ring_prime] .
  qed
  have wfactors_exist_mult:
      "\<And>a. \<lbrakk>a \<in> carrier (mult_of R); a \<notin> Units (mult_of R)\<rbrakk> \<Longrightarrow>
        \<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs a"
  proof -
    fix a
    assume a_in: "a \<in> carrier (mult_of R)"
      and a_not_unit: "a \<notin> Units (mult_of R)"
    have a_in_R: "a \<in> carrier R - {\<zero>}"
      using a_in by simp
    have a_not_unit_R: "a \<notin> Units R"
      using a_not_unit by simp
    show "\<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs a"
      using N.factorization_property[OF a_in_R a_not_unit_R] .
  qed
  have factorial_mult: "factorial_monoid (mult_of R)"
    by (rule mult_of.factorial_monoidI[OF wfactors_exist_mult PC.wfactors_unique])
  show ?thesis
    unfolding factorial_domain_def using domain_axioms factorial_mult by simp
qed

lemma nagata_theorem_of_prime_generators:
  assumes noeth: "noetherian_domain R"
    and S_eq: "S = ring_mult_submonoid_closure R A"
    and A_sub: "A \<subseteq> carrier R"
    and hprime: "\<And>q. q \<in> A \<Longrightarrow> ring_prime\<^bsub>R\<^esub> q"
    and loc_fd: "factorial_domain rec_rng_of_frac"
  shows "factorial_domain R"
proof -
  have hS: "ring_prime_generated R S"
    unfolding S_eq
    by (rule ring_prime_generated_mult_submonoid_closure[OF ring_axioms A_sub hprime])
  show ?thesis
    by (rule nagata_theorem[OF noeth hS loc_fd])
qed

lemma nagata_theorem_of_finite_prime_generators:
  assumes noeth: "noetherian_domain R"
    and finA: "finite A"
    and S_eq: "S = ring_mult_submonoid_closure R A"
    and A_sub: "A \<subseteq> carrier R"
    and hprime: "\<And>q. q \<in> A \<Longrightarrow> ring_prime\<^bsub>R\<^esub> q"
    and loc_fd: "factorial_domain rec_rng_of_frac"
  shows "factorial_domain R"
  using finA nagata_theorem_of_prime_generators[OF noeth S_eq A_sub hprime loc_fd] by blast

end

end
