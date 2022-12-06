theory Birkhoff_Finite_Distributive_Lattices
  imports
    "HOL-Library.Finite_Lattice"
    "HOL.Transcendental"
begin

unbundle lattice_syntax

text \<open> The proof of Birkhoff's representation theorem for finite
       distributive lattices @{cite birkhoffRingsSets1937} presented
       here follows Davey and Priestley @{cite daveyChapterRepresentationFinite2002}. \<close>

section \<open> Atoms, Join Primes and Join Irreducibles \label{sec:join-irreducibles} \<close>

text \<open> Atomic elements are defined as follows. \<close>

definition (in bounded_lattice_bot) atomic :: "'a \<Rightarrow> bool" where
  "atomic x \<equiv> x \<noteq> \<bottom> \<and> (\<forall> y. y \<le> x \<longrightarrow> y = \<bottom> \<or> y = x)"

text \<open> Two related concepts are \<^emph>\<open>join-prime\<close> elements and \<^emph>\<open>join-irreducible\<close> 
       elements. \<close>

definition (in bounded_lattice_bot) join_prime :: "'a \<Rightarrow> bool" where
  "join_prime x \<equiv> x \<noteq> \<bottom> \<and> (\<forall> y z . x \<le> y \<squnion> z \<longrightarrow> x \<le> y \<or> x \<le> z)"

definition (in bounded_lattice_bot) join_irreducible :: "'a \<Rightarrow> bool" where
  "join_irreducible x \<equiv> x \<noteq> \<bottom> \<and> (\<forall> y z . y < x \<longrightarrow> z < x \<longrightarrow> y \<squnion> z < x)"

lemma (in bounded_lattice_bot) join_irreducible_def':
  "join_irreducible x = (x \<noteq> \<bottom> \<and> (\<forall> y z . x = y \<squnion> z \<longrightarrow> x = y \<or> x = z))"
  unfolding join_irreducible_def
  by (metis 
        nless_le
        sup.bounded_iff
        sup.cobounded1
        sup_ge2)

text \<open> Every join-prime is also join-irreducible. \<close>

lemma (in bounded_lattice_bot) join_prime_implies_join_irreducible:
  assumes "join_prime x"
  shows "join_irreducible x"
  using assms
  unfolding 
    join_irreducible_def' 
    join_prime_def
  by (simp add: dual_order.eq_iff)

text \<open> In the special case when the underlying lattice is
       distributive, the join-prime elements and join-irreducible
       elements coincide. \<close>

class bounded_distrib_lattice_bot = bounded_lattice_bot +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
begin

subclass distrib_lattice
  by (unfold_locales, metis (full_types) sup_inf_distrib1)

end

context complete_distrib_lattice
begin

subclass bounded_distrib_lattice_bot
  by (unfold_locales, 
      metis (full_types) 
        sup_inf_distrib1)

end

lemma (in bounded_distrib_lattice_bot) join_irreducible_is_join_prime:
  "join_irreducible x = join_prime x"
proof
  assume "join_prime x"
  thus "join_irreducible x"
    by (simp add: join_prime_implies_join_irreducible)
next
  assume "join_irreducible x"
  {
    fix y z
    assume "x \<le> y \<squnion> z"
    hence "x = x \<sqinter> (y \<squnion> z)"
      by (metis local.inf.orderE)
    hence "x = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
      using inf_sup_distrib1 by auto
    hence "(x = x \<sqinter> y) \<or> (x = x \<sqinter> z)"
      using \<open>join_irreducible x\<close>
      unfolding join_irreducible_def'
      by metis
    hence "(x \<le> y) \<or> (x \<le> z)"
      by (metis (full_types) local.inf.cobounded2)
  }
  thus "join_prime x"
    by (metis 
          \<open>join_irreducible x\<close> 
          join_irreducible_def' 
          join_prime_def)
qed

text \<open> Every atomic element is join-irreducible. \<close>

lemma (in bounded_lattice_bot) atomic_implies_join_prime:
  assumes "atomic x"
  shows "join_irreducible x"
  using assms
  unfolding 
    atomic_def 
    join_irreducible_def'
  by (metis (no_types, opaque_lifting) 
        sup.cobounded2 
        sup_bot.right_neutral)   

text \<open> In the case of Boolean algebras, atomic elements and
       join-prime elements are one-in-the-same. \<close>

lemma (in boolean_algebra) join_prime_is_atomic:
  "atomic x = join_prime x"
proof
  assume "atomic x"
  {
    fix y z
    assume "x \<le> y \<squnion> z"
    hence "x = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
      using inf.absorb1 inf_sup_distrib1 by fastforce
    moreover
    have "x \<le> y \<or> (x \<sqinter> y) = \<bottom>"
         "x \<le> z \<or> (x \<sqinter> z) = \<bottom>"
      using \<open>atomic x\<close> inf.cobounded1 inf.cobounded2
      unfolding atomic_def
      by fastforce+
    ultimately have "x \<le> y \<or> x \<le> z"
      using \<open>atomic x\<close> atomic_def by auto
  }
  thus "join_prime x"
    using \<open>atomic x\<close> join_prime_def atomic_def
    by auto
next
  assume "join_prime x"
  {
    fix y
    assume "y \<le> x" "y \<noteq> x"
    hence "x = x \<squnion> y"
      using sup.orderE by blast
    also have "\<dots> = (x \<squnion> y) \<sqinter> (y \<squnion> -y)"
      by simp
    finally have "x = (x \<sqinter> -y) \<squnion> y"
      by (simp add: sup_inf_distrib2)
    hence "x \<le> -y"
      using 
        \<open>join_prime x\<close>
        \<open>y \<noteq> x\<close> 
        \<open>y \<le> x\<close>
        antisym_conv
        inf_le2
        sup_neg_inf 
      unfolding join_prime_def
      by blast
    hence "y \<le> y \<sqinter> -y"
      by (metis
            \<open>x = x \<squnion> y\<close>
            inf.orderE
            inf_compl_bot_right
            inf_sup_absorb
            order_refl
            sup.commute)
    hence "y = \<bottom>"
      using sup_absorb2 by fastforce
  }
  thus "atomic x" 
    using \<open>join_prime x\<close>
    unfolding 
      atomic_def
      join_prime_def 
    by auto
qed

text \<open> All atomic elements are disjoint. \<close>

lemma (in bounded_lattice_bot) atomic_disjoint:
  assumes "atomic \<alpha>"
      and "atomic \<beta>"
    shows "(\<alpha> = \<beta>) \<longleftrightarrow> (\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>)"
proof
  assume "\<alpha> = \<beta>"
  hence "\<alpha> \<sqinter> \<beta> = \<alpha>"
    by simp
  thus "\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>"
    using \<open>atomic \<alpha>\<close>
    unfolding atomic_def
    by auto
next
  assume "\<alpha> \<sqinter> \<beta> \<noteq> \<bottom>"
  hence "\<beta> \<le> \<alpha> \<and> \<alpha> \<le> \<beta>"
    by (metis 
          assms 
          atomic_def 
          inf_absorb2 
          inf_le1 
          inf_le2)
  thus "\<alpha> = \<beta>" by auto
qed

definition (in bounded_lattice_bot) atomic_elements ("\<A>") where
  "\<A> \<equiv> {a . atomic a}"

definition (in bounded_lattice_bot) join_irreducible_elements ("\<J>") where
  "\<J> \<equiv> {a . join_irreducible a}"

section \<open> Birkhoff's Representation Theorem For Finite Distributive Lattices \label{section:birkhoffs-theorem} \<close>

text \<open> Birkhoff's representation theorem for finite distributive
       lattices follows from the fact that every non-\<open>\<bottom>\<close> element
       can be represented by the join-irreducible elements beneath it. \<close>

text \<open> In this section we merely demonstrate the representation aspect of
       Birkhoff's theorem. In \S\ref{section:isomorphism} we show this 
       representation is a lattice homomorphism. \<close>

text \<open> The fist step to representing elements is to show that there \<^emph>\<open>exist\<close>
       join-irreducible elements beneath them. This is done by showing if there is 
       no join-irreducible element, we can make a descending chain with more elements 
       than the finite Boolean algebra under consideration. \<close>

fun (in order) descending_chain_list :: "'a list \<Rightarrow> bool" where
  "descending_chain_list [] = True"
| "descending_chain_list [x] = True"
| "descending_chain_list (x # x' # xs)
     = (x < x' \<and> descending_chain_list (x' # xs))"

lemma (in order) descending_chain_list_tail:
  assumes "descending_chain_list (s # S)"
  shows "descending_chain_list S"
  using assms
  by (induct S, auto)

lemma (in order) descending_chain_list_drop_penultimate:
  assumes "descending_chain_list (s # s' # S)"
  shows "descending_chain_list (s # S)"
  using assms
  by (induct S, simp, auto)

lemma (in order) descending_chain_list_less_than_others:
  assumes "descending_chain_list (s # S)"
  shows   "\<forall>s' \<in> set S. s < s'"
  using assms
  by (induct S, 
        auto, 
        simp add: descending_chain_list_drop_penultimate)

lemma (in order) descending_chain_list_distinct:
  assumes "descending_chain_list S"
  shows "distinct S"
  using assms
  by (induct S,
      simp,
      meson
        descending_chain_list_less_than_others
        descending_chain_list_tail
        distinct.simps(2)
        less_irrefl)

lemma (in finite_distrib_lattice) join_irreducible_lower_bound_exists:
  assumes "\<not> (x \<le> y)"
  shows "\<exists> z \<in> \<J>. z \<le> x \<and> \<not> (z \<le> y)"
proof (rule ccontr)
  assume \<star>: "\<not> (\<exists> z \<in> \<J>. z \<le> x \<and> \<not> (z \<le> y))"
  {
    fix z :: 'a
    assume 
      "z \<le> x"
      "\<not> (z \<le> y)"
    with \<star> obtain p q where
        "p < z"
        "q < z"
        "p \<squnion> q = z"
      by (metis (full_types) 
            bot_least
            dual_order.not_eq_order_implies_strict
            join_irreducible_def'
            join_irreducible_elements_def
            sup_ge1
            sup_ge2 
            mem_Collect_eq)
    hence "\<not> (p \<le> y) \<or> \<not> (q \<le> y)"
      by (metis (full_types) \<open>\<not> z \<le> y\<close> sup_least)
    hence "\<exists> p < z. \<not> (p \<le> y)"
      by (metis \<open>p < z\<close> \<open>q < z\<close>)
  }
  note fresh = this
  {
    fix n :: nat
    have "\<exists> S . descending_chain_list S
                  \<and> length S = n
                  \<and> (\<forall>s \<in> set S. s \<le> x \<and> \<not> (s \<le> y))"
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      then show ?case proof (cases "n = 0")
        case True
        hence "descending_chain_list [x]
                 \<and> length [x] = Suc n
                 \<and> (\<forall>s \<in> set [x]. s \<le> x \<and> \<not> (s \<le> y))"
          by (metis 
                Suc 
                assms 
                length_0_conv 
                length_Suc_conv 
                descending_chain_list.simps(2)
                le_less set_ConsD)
        then show ?thesis
          by blast
      next
        case False
        from this obtain s S where
            "descending_chain_list (s # S)"
            "length (s # S) = n"
            "\<forall>s \<in> set (s # S). s \<le> x \<and> \<not> (s \<le> y)"
          using 
            Suc.hyps 
            length_0_conv 
            descending_chain_list.elims(2)
          by metis
        note A = this
        hence "s \<le> x" "\<not> (s \<le> y)" by auto
        obtain s' :: 'a where
          "s' < s"
          "\<not> (s' \<le> y)"
          using 
            fresh [OF \<open>s \<le> x\<close> \<open>\<not> (s \<le> y)\<close>]
          by auto
        note B = this
        let ?S' = "s' # s # S"
        from A and B have
          "descending_chain_list ?S'"
          "length ?S' = Suc n"
          "\<forall>s \<in> set ?S'. s \<le> x \<and> \<not> (s \<le> y)"
            by auto
        then show ?thesis by blast
      qed
    qed
  }
  from this obtain S :: "'a list" where
    "descending_chain_list S"
    "length S = 1 + (card (UNIV::'a set))"
    by auto
  hence "card (set S) = 1 + (card (UNIV::'a set))"
    using descending_chain_list_distinct
          distinct_card
    by fastforce
  hence "\<not> card (set S) \<le> card (UNIV::'a set)"
    by presburger
  thus "False"
    using card_mono finite_UNIV by blast
qed

definition (in bounded_lattice_bot)
  join_irreducibles_embedding :: "'a \<Rightarrow> 'a set" ("\<lbrace> _ \<rbrace>" [50]) where
  "\<lbrace> x \<rbrace> \<equiv> {a \<in> \<J>. a \<le> x}"

text \<open> We can now show every element is exactly the suprema of the 
       join-irreducible elements beneath them in any distributive lattice. \<close>

theorem (in finite_distrib_lattice) sup_join_prime_embedding_ident:
   "x = \<Squnion> \<lbrace> x \<rbrace>"
proof -
  have "\<forall> a \<in> \<lbrace> x \<rbrace>. a \<le> x"
    by (metis (no_types, lifting) 
          join_irreducibles_embedding_def 
          mem_Collect_eq)
  hence "\<Squnion> \<lbrace> x \<rbrace> \<le> x"
    by (simp add: Sup_least)
  moreover
  {
    fix y :: 'a
    assume "\<Squnion> \<lbrace> x \<rbrace> \<le> y"
    have "x \<le> y"
    proof (rule ccontr)
      assume "\<not> x \<le> y"
      from this obtain a where
          "a \<in> \<J>"
          "a \<le> x"
          "\<not> a \<le> y"
        using join_irreducible_lower_bound_exists [OF \<open>\<not> x \<le> y\<close>]
        by metis
      hence "a \<in> \<lbrace> x \<rbrace>"
        by (metis (no_types, lifting) 
              join_irreducibles_embedding_def 
              mem_Collect_eq)
      hence "a \<le> y"
        using \<open>\<Squnion>\<lbrace> x \<rbrace> \<le> y\<close>
              Sup_upper
              order.trans
        by blast
      thus "False"
        by (metis (full_types) \<open>\<not> a \<le> y\<close>)
    qed
  }
  ultimately show ?thesis
    using antisym_conv by blast
qed


text \<open> Just as \<open>x = \<Squnion> \<lbrace> x \<rbrace>\<close>, the reverse is also true; \<open>\<lambda> x. \<lbrace> x \<rbrace>\<close>
       and \<open>\<lambda> S. \<Squnion> S\<close> are inverses where \<open>S \<in> \<O>\<J>\<close>, the set of downsets
       in \<open>Pow \<J>\<close>. \<close>

definition (in bounded_lattice_bot) down_irreducibles ("\<O>\<J>") where
  "\<O>\<J> \<equiv> { S \<in> Pow \<J> . (\<exists> x . S = \<lbrace> x \<rbrace>) }"

lemma (in finite_distrib_lattice) join_irreducible_embedding_sup_ident:
  assumes "S \<in> \<O>\<J>"
  shows "S = \<lbrace> \<Squnion> S \<rbrace>"
proof -
  obtain x where
      "S = \<lbrace> x \<rbrace>"
    using 
      \<open>S \<in> \<O>\<J>\<close>
    unfolding 
      down_irreducibles_def
    by auto
  with \<open>S \<in> \<O>\<J>\<close> have "\<forall> s \<in> S. s \<in> \<J> \<and> s \<le> \<Squnion> S"
    unfolding 
      down_irreducibles_def
      Pow_def
    using Sup_upper
    by fastforce
  hence "S \<subseteq> \<lbrace> \<Squnion> S \<rbrace>"
    unfolding join_irreducibles_embedding_def
    by blast
  moreover
  {
    fix y
    assume
      "y \<in> \<J>"
      "y \<le> \<Squnion> S"
    have "finite S" by auto
    from \<open>finite S\<close> and \<open>y \<le> \<Squnion> S\<close> have "\<exists> s \<in> S. y \<le> s"
    proof (induct S rule: finite_induct)
      case empty
      hence "y \<le> \<bottom>"
        by (metis Sup_empty)
      then show ?case
        using
          \<open>y \<in> \<J>\<close>
        unfolding 
          join_irreducible_elements_def
          join_irreducible_def
        by (metis (mono_tags, lifting) 
              le_bot 
              mem_Collect_eq)
    next
      case (insert s S)
      hence "y \<le> s \<or> y \<le> \<Squnion> S"
        using
          \<open>y \<in> \<J>\<close>
        unfolding 
          join_irreducible_elements_def
          join_irreducible_is_join_prime
          join_prime_def
        by auto
      then show ?case
        by (metis (full_types) 
              insert.hyps(3) 
              insertCI)
    qed
    hence "y \<le> x"
      by (metis (no_types, lifting) 
            \<open>S = \<lbrace> x \<rbrace>\<close>
            join_irreducibles_embedding_def
            order_trans 
            mem_Collect_eq)
    hence "y \<in> S"
      by (metis (no_types, lifting) 
            \<open>S = \<lbrace> x \<rbrace>\<close> 
            \<open>y \<in> \<J>\<close> 
            join_irreducibles_embedding_def 
            mem_Collect_eq)
  }
  hence "\<lbrace> \<Squnion> S \<rbrace> \<subseteq> S"
    unfolding 
      join_irreducibles_embedding_def
    by blast
  ultimately show ?thesis by auto
qed

text \<open> Given that \<open>\<lambda> x. \<lbrace> x \<rbrace>\<close> has a left and right inverse, we can show
       it is a \<^emph>\<open>bijection\<close>. \<close>

text \<open> The bijection below is recognizable as a form of \<^emph>\<open>Birkhoff's Representation Theorem\<close> 
       for finite distributive lattices. \<close>

theorem (in finite_distrib_lattice) birkhoffs_theorem:
  "bij_betw (\<lambda> x. \<lbrace> x \<rbrace>) UNIV \<O>\<J>"
  unfolding bij_betw_def
proof
  {
    fix x y
    assume "\<lbrace> x \<rbrace> = \<lbrace> y \<rbrace>"
    hence "\<Squnion> \<lbrace> x \<rbrace> = \<Squnion> \<lbrace> y \<rbrace>"
      by simp
    hence "x = y"
      using sup_join_prime_embedding_ident
      by auto
  }
  thus "inj (\<lambda> x. \<lbrace> x \<rbrace>)"
    unfolding inj_def
    by auto
next
  show "range (\<lambda> x. \<lbrace> x \<rbrace>) = \<O>\<J>"
    unfolding 
      down_irreducibles_def
      join_irreducibles_embedding_def
    by auto
qed

section \<open> Finite Ditributive Lattice Isomorphism \label{section:isomorphism} \<close>

text \<open> The form of Birkhoff's theorem presented in \S\ref{section:birkhoffs-theorem}
       simply gave a bijection between a finite distributive lattice and the
       downsets of its join-irreducible elements. This relationship can be
       extended to a full-blown \<^emph>\<open>lattice homomorphism\<close>. In particular
       we have the following properties:

       \<^item> \<open>\<bottom>\<close> and \<open>\<top>\<close> are preserved; specifically \<open>\<lbrace> \<bottom> \<rbrace> = {}\<close> and
         \<open>\<lbrace> \<top> \<rbrace> = \<J>\<close>.

       \<^item> Order is preserved: \<open>x \<le> y = (\<lbrace> x \<rbrace> \<subseteq> \<lbrace> y \<rbrace>)\<close>.

       \<^item> \<open>\<lambda> x . \<lbrace> x \<rbrace>\<close> is a lower complete semi-lattice homomorphism, mapping
         \<open>\<lbrace> \<Squnion> X \<rbrace> = (\<Union> x \<in> X . \<lbrace> x \<rbrace>)\<close>.

       \<^item> In addition to preserving arbitrary joins, \<open>\<lambda> x . \<lbrace> x \<rbrace>\<close> is a
         lattice homomorphism, since it also preserves finitary meets with
         \<open> \<lbrace> x \<sqinter> y \<rbrace> = \<lbrace> x \<rbrace> \<inter> \<lbrace> y \<rbrace> \<close>. Arbitrary meets are also preserved, 
         but relative to a top element \<open>\<J>\<close>, or in other words 
         \<open> \<lbrace> \<Sqinter> X \<rbrace> = \<J> \<inter> (\<Inter> x \<in> X. \<lbrace> x \<rbrace>) \<close>.

       \<^item> In the case of a Boolean algebra, complementation corresponds to 
         relative set complementation via \<open>\<lbrace> - x \<rbrace> = \<J> - \<lbrace> x \<rbrace>\<close>.
\<close>

lemma (in finite_distrib_lattice) join_irreducibles_bot:
  "\<lbrace> \<bottom> \<rbrace> = {}"
  unfolding
    join_irreducibles_embedding_def
    join_irreducible_elements_def
    join_irreducible_is_join_prime
    join_prime_def
  by (simp add: bot_unique)

lemma (in finite_distrib_lattice) join_irreducibles_top:
  "\<lbrace> \<top> \<rbrace> = \<J>"
  unfolding
    join_irreducibles_embedding_def
    join_irreducible_elements_def
    join_irreducible_is_join_prime
    join_prime_def
  by auto

lemma (in finite_distrib_lattice) join_irreducibles_order_isomorphism:
  "x \<le> y = (\<lbrace> x \<rbrace> \<subseteq> \<lbrace> y \<rbrace>)"
  by (rule iffI, 
        metis (mono_tags, lifting) 
          join_irreducibles_embedding_def 
          order_trans 
          mem_Collect_eq 
          subsetI,
        metis (full_types) 
          Sup_subset_mono 
          sup_join_prime_embedding_ident)

lemma (in finite_distrib_lattice) join_irreducibles_join_homomorphism:
  "\<lbrace> x \<squnion> y \<rbrace> = \<lbrace> x \<rbrace> \<union> \<lbrace> y \<rbrace>"
proof
  show "\<lbrace> x \<squnion> y \<rbrace> \<subseteq> \<lbrace> x \<rbrace> \<union> \<lbrace> y \<rbrace>"
    unfolding
      join_irreducibles_embedding_def
      join_irreducible_elements_def
      join_irreducible_is_join_prime
      join_prime_def
    by blast
next
  show "\<lbrace> x \<rbrace> \<union> \<lbrace> y \<rbrace> \<subseteq> \<lbrace> x \<squnion> y \<rbrace>"
    unfolding
      join_irreducibles_embedding_def
      join_irreducible_elements_def
      join_irreducible_is_join_prime
      join_prime_def
    using
      le_supI1
      sup.absorb_iff1
      sup.assoc
    by force
qed

lemma (in finite_distrib_lattice) join_irreducibles_sup_homomorphism:
  "\<lbrace> \<Squnion> X \<rbrace> = (\<Union> x \<in> X . \<lbrace> x \<rbrace>)"
proof -
  have "finite X"
    by simp
  thus ?thesis
  proof (induct X rule: finite_induct)
    case empty
    then show ?case by (simp add: join_irreducibles_bot)
  next
    case (insert x X)
    then show ?case by (simp add: join_irreducibles_join_homomorphism)
  qed
qed


lemma (in finite_distrib_lattice) join_irreducibles_meet_homomorphism:
  "\<lbrace> x \<sqinter> y \<rbrace> = \<lbrace> x \<rbrace> \<inter> \<lbrace> y \<rbrace>"
  unfolding
    join_irreducibles_embedding_def
  by auto

text \<open> Arbitrary meets are also preserved, but relative to a top element \<open>\<J>\<close>. \<close>

lemma (in finite_distrib_lattice) join_irreducibles_inf_homomorphism:
  "\<lbrace> \<Sqinter> X \<rbrace> = \<J> \<inter> (\<Inter> x \<in> X. \<lbrace> x \<rbrace>)"
proof -
  have "finite X"
    by simp
  thus ?thesis
  proof (induct X rule: finite_induct)
    case empty
    then show ?case by (simp add: join_irreducibles_top)
  next
    case (insert x X)
    then show ?case by (simp add: join_irreducibles_meet_homomorphism, blast)
  qed
qed

text \<open> Finally, we show that complementation is preserved. \<close>

text \<open> To begin, we define the class of finite Boolean algebras.
       This class is simply an extension of @{class boolean_algebra},
       extended with \<^term>\<open>finite UNIV\<close> as per the axiom class @{class finite}. We also
       also extend the language of the class with \<^emph>\<open>infima\<close> and \<^emph>\<open>suprema\<close> 
       (i.e. \<open>\<Sqinter> A\<close> and \<open>\<Squnion> A\<close> respectively). \<close>

class finite_boolean_algebra = boolean_algebra + finite + Inf + Sup +
  assumes Inf_def: "\<Sqinter> A = Finite_Set.fold (\<sqinter>) \<top> A"
  assumes Sup_def: "\<Squnion> A = Finite_Set.fold (\<squnion>) \<bottom> A"
begin

text \<open> Finite Boolean algebras are trivially a subclass of finite
       distributive lattices, which are necessarily \<^emph>\<open>complete\<close>. \<close>

subclass finite_distrib_lattice_complete
  using
    Inf_fin.coboundedI
    Sup_fin.coboundedI
    finite_UNIV
    le_bot
    top_unique
    Inf_def
    Sup_def
  by (unfold_locales, blast, fastforce+)

subclass bounded_distrib_lattice_bot
  by (unfold_locales, metis sup_inf_distrib1)
end

lemma (in finite_boolean_algebra) join_irreducibles_complement_homomorphism:
  "\<lbrace> - x \<rbrace> = \<J> - \<lbrace> x \<rbrace>"
proof
  show "\<lbrace> - x \<rbrace> \<subseteq> \<J> - \<lbrace> x \<rbrace>"
  proof
    fix j
    assume "j \<in> \<lbrace> - x \<rbrace>"
    hence "j \<notin> \<lbrace> x \<rbrace>"
      unfolding
        join_irreducibles_embedding_def
        join_irreducible_elements_def
        join_irreducible_is_join_prime
        join_prime_def
      by (metis
            (mono_tags, lifting)
            CollectD
            bot_unique
            inf.boundedI
            inf_compl_bot)
    thus "j \<in> \<J> - \<lbrace> x \<rbrace>"
      using \<open>j \<in> \<lbrace> - x \<rbrace>\<close>
      unfolding
        join_irreducibles_embedding_def
      by blast
  qed
next
  show "\<J> - \<lbrace> x \<rbrace> \<subseteq> \<lbrace> - x \<rbrace>"
  proof
    fix j
    assume "j \<in> \<J> - \<lbrace> x \<rbrace>"
    hence "j \<in> \<J>" and "\<not> j \<le> x"
      unfolding join_irreducibles_embedding_def
      by blast+
    moreover have "j \<le> x \<squnion> -x"
      by auto
    ultimately have "j \<le> -x"
      unfolding
        join_irreducible_elements_def
        join_irreducible_is_join_prime
        join_prime_def
      by blast
    thus "j \<in> \<lbrace> - x \<rbrace>"
      unfolding join_irreducibles_embedding_def
      using \<open>j \<in> \<J>\<close>
      by auto
  qed
qed


section \<open> Cardinality \<close>

text \<open> Another consequence of Birkhoff's theorem from \S\ref{section:birkhoffs-theorem}
       is that every finite Boolean algebra has a cardinality which is 
       a power of two. This gives a bound on the number of 
       atoms/join-prime/irreducible elements, which must be logarithmic in 
       the size of the finite Boolean algebra they belong to. \<close>

text \<open> We first show that \<open>\<O>\<J>\<close>, the downsets of the join-irreducible elements 
       \<open>\<J>\<close>, are the same as the powerset of \<open>\<J>\<close> in any finite Boolean algebra. \<close>

lemma (in finite_boolean_algebra) \<O>\<J>_is_Pow_\<J>:
  "\<O>\<J> = Pow \<J>"
proof
  show "\<O>\<J> \<subseteq> Pow \<J>"
    unfolding down_irreducibles_def
    by auto
next
  show "Pow \<J> \<subseteq> \<O>\<J>"
  proof (rule ccontr)
    assume "\<not> Pow \<J> \<subseteq> \<O>\<J>"
    from this obtain S where
        "S \<subseteq> \<J>"
        "\<forall> x. S \<noteq> {a \<in> \<J>. a \<le> x}"
      unfolding 
        down_irreducibles_def
        join_irreducibles_embedding_def
      by auto
    hence "S \<noteq> {a \<in> \<J>. a \<le> \<Squnion> S}"
      by auto
    moreover 
    have "\<forall> s \<in> S . s \<in> \<J> \<and> s \<le> \<Squnion> S"
      by (metis (no_types, lifting) 
            \<open>S \<subseteq> \<J>\<close> 
            Sup_upper subsetD)
    hence "S \<subseteq> {a \<in> \<J>. a \<le> \<Squnion> S}"
      by (metis (mono_tags, lifting) Ball_Collect)
    ultimately have "\<exists> y \<in> \<J> . y \<le> \<Squnion> S \<and> y \<notin> S"
      by (metis (mono_tags, lifting) 
            mem_Collect_eq 
            subsetI 
            subset_antisym)
    moreover
    {
      fix y
      assume 
        "y \<in> \<J>"
        "y \<le> \<Squnion> S"
      from 
        finite [of S]
        \<open>y \<le> \<Squnion> S\<close>
        \<open>S \<subseteq> \<J>\<close>
      have "y \<in> S"
      proof (induct S rule: finite_induct)
        case empty
        hence "y \<le> \<bottom>"
          by (metis (full_types) local.Sup_empty)
        then show ?case
          using \<open>y \<in> \<J>\<close>
          unfolding 
            join_irreducible_elements_def
            join_irreducible_def
          by (metis (mono_tags, lifting) 
                le_bot 
                mem_Collect_eq)
      next
        case (insert s S)
        hence "y \<le> s \<or> y \<le> \<Squnion> S"
          using \<open>y \<in> \<J>\<close>
          unfolding 
            join_irreducible_elements_def
            join_irreducible_is_join_prime
            join_prime_def
          by simp
        moreover
        {
          assume "y \<le> s"
          have "atomic s"
            by (metis in_mono 
                  insert.prems(2) 
                  insertCI 
                  join_irreducible_elements_def 
                  join_irreducible_is_join_prime 
                  join_prime_is_atomic 
                  mem_Collect_eq)
          hence "y = s"
            by (metis (no_types, lifting) 
                  \<open>y \<in> \<J>\<close> 
                  \<open>y \<le> s\<close> 
                  atomic_def 
                  join_irreducible_def 
                  join_irreducible_elements_def 
                  mem_Collect_eq)
        }
        ultimately show ?case
          by (metis   
                insert.prems(2) 
                insert_iff 
                insert_subset 
                insert(3))
      qed
    }
    ultimately show False by auto
  qed
qed
  

lemma (in finite_boolean_algebra) UNIV_card:
  "card (UNIV::'a set) = card (Pow \<J>)"
  using 
    bij_betw_same_card [where f="\<lambda>x. \<lbrace> x \<rbrace>"]
    birkhoffs_theorem
  unfolding 
    \<O>\<J>_is_Pow_\<J>
  by blast

lemma finite_Pow_card:
  assumes "finite X"
  shows "card (Pow X) = 2 powr (card X)"
  using assms
proof (induct X rule: finite_induct)
  case empty
  then show ?case by fastforce
next
  case (insert x X)
  have "0 \<le> (2 :: real)" by auto
  hence two_powr_one: "(2 :: real) = 2 powr 1" by fastforce
  have "bij_betw (\<lambda> x. fst x \<union> snd x) ({{},{x}} \<times> Pow X) (Pow (insert x X))"
    unfolding bij_betw_def
  proof
    {
      fix y z
      assume 
        "y \<in> {{}, {x}} \<times> Pow X"
        "z \<in> {{}, {x}} \<times> Pow X"
        "fst y \<union> snd y = fst z \<union> snd z"
        (is "?Uy = ?Uz")
      hence 
          "x \<notin> snd y"
          "x \<notin> snd z"
          "fst y = {x} \<or> fst y = {}"
          "fst z = {x} \<or> fst z = {}"
        using insert.hyps(2) by auto
      hence 
          "x \<in> ?Uy \<longleftrightarrow> fst y = {x}"
          "x \<in> ?Uz \<longleftrightarrow> fst z = {x}"
          "x \<notin> ?Uy \<longleftrightarrow> fst y = {}"
          "x \<notin> ?Uz \<longleftrightarrow> fst z = {}"
          "snd y = ?Uy - {x}"
          "snd z = ?Uz - {x}"
        by auto
      hence 
          "x \<in> ?Uy \<longleftrightarrow> y = ({x}, ?Uy - {x})"
          "x \<in> ?Uz \<longleftrightarrow> z = ({x}, ?Uz - {x})"
          "x \<notin> ?Uy \<longleftrightarrow> y = ({}, ?Uy - {x})"
          "x \<notin> ?Uz \<longleftrightarrow> z = ({}, ?Uz - {x})"
        by (metis fst_conv prod.collapse)+
      hence "y = z"
        using \<open>?Uy = ?Uz\<close>
        by metis
    }
    thus "inj_on (\<lambda>x. fst x \<union> snd x) ({{}, {x}} \<times> Pow X)"
      unfolding inj_on_def
      by auto
  next
    show "(\<lambda>x. fst x \<union> snd x) ` ({{}, {x}} \<times> Pow X) = Pow (insert x X)"
    proof (intro equalityI subsetI)
      fix y
      assume "y \<in> (\<lambda>x. fst x \<union> snd x) ` ({{}, {x}} \<times> Pow X)"
      from this obtain z where
         "z \<in> ({{}, {x}} \<times> Pow X)"
         "y = fst z \<union> snd z"
        by auto
      hence 
          "snd z \<subseteq> X"
          "fst z \<subseteq> insert x X"
        using SigmaE by auto
      thus "y \<in> Pow (insert x X)"
        using \<open>y = fst z \<union> snd z\<close> by blast
    next
      fix y
      assume "y \<in> Pow (insert x X)"
      let ?z = "(if x \<in> y then {x} else {}, y - {x})"
      have "?z \<in> ({{}, {x}} \<times> Pow X)"
        using \<open>y \<in> Pow (insert x X)\<close> by auto
      moreover have "(\<lambda>x. fst x \<union> snd x) ?z = y"
        by auto
      ultimately show "y \<in> (\<lambda>x. fst x \<union> snd x) ` ({{}, {x}} \<times> Pow X)"
        by blast
    qed
  qed
  hence "card (Pow (insert x X)) = card ({{},{x}} \<times> Pow X)"
    using bij_betw_same_card by fastforce
  also have "\<dots> = 2 * card (Pow X)"
    by (simp add: insert.hyps(1))
  also have "\<dots> = 2 * (2 powr (card X))"
    by (simp add: insert.hyps(3))
  also have "\<dots> = (2 powr 1) * 2 powr (card X)"
    using two_powr_one
    by fastforce
  also have "\<dots> = 2 powr (1 + card X)"
    by (simp add: powr_add)
  also have "\<dots> = 2 powr (card (insert x X))"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case .
qed

lemma (in finite_boolean_algebra) UNIV_card_powr_2:
  "card (UNIV::'a set) = 2 powr (card \<J>)"
  using 
    finite [of \<J>]
    finite_Pow_card [of \<J>]
    UNIV_card
  by linarith

lemma (in finite_boolean_algebra) join_irreducibles_card_log_2:
  "card \<J> = log 2 (card (UNIV :: 'a set))"
proof (cases "card (UNIV :: 'a set) = 1")
  case True
  hence "\<exists> x :: 'a. UNIV = {x}"
    using card_1_singletonE by blast
  hence "\<forall> x y :: 'a. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> x = y"
    by (metis (mono_tags) singletonD)
  hence "\<forall> x y :: 'a. x = y"
    by blast
  hence "\<forall> x. x = \<bottom>"
    by blast
  hence "\<J> = {}"
    unfolding 
      join_irreducible_elements_def
      join_irreducible_is_join_prime
      join_prime_def
    by blast
  hence "card \<J> = (0 :: real)"
    by simp
  moreover
  have "log 2 (card (UNIV :: 'a set)) = 0"
    by (simp add: True)
  ultimately show ?thesis by auto
next
  case False
  hence "0 < 2 powr (card \<J>)" "2 powr (card \<J>) \<noteq> 1"
    using finite_UNIV_card_ge_0 finite UNIV_card_powr_2
    by (simp, linarith)
  hence "log 2 (2 powr (card \<J>)) = card \<J>"
    by simp
  then show ?thesis
    using UNIV_card_powr_2
    by simp
qed

end
