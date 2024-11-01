section \<open>Alternating permutations\<close>
theory Alternating_Permutations
  imports "HOL-Combinatorics.Combinatorics" Boustrophedon_Transform_Library
begin

text \<open>
  Given a strict linear order $<$ on some finite set $A = \{a_1, \ldots, a_n\}$ with
  $a_1 < \ldots < a_n$ we call a permutation $\pi$ \<^emph>\<open>alternating\<close> if
  $f(a_1) > f(a_2) < f(a_3) > f_(a_4) \ldots$.

  Since it is somewhat awkward to specify this for a function, we instead define what an
  alternating permutation is using the view that a permutation on $A$ is simple the tuple
  $(f_(a_1), \ldots, f(a_n))$.
\<close>

subsection \<open>Alternating lists\<close>

text \<open>
  Given a relation $R$, we say that a list $[x_1, \ldots, x_n]$ is \<^emph>\<open>$R$-alternating\<close> if
  we have $(x_i, x_{i+1}) \in R$ for any even $i$ and $(x_{i+1}, x_i)\in R$ for any odd $i$.

  In other words: if we view $R$ as an order then the list alternates between ``rises`` and
  ``falls``, starting with a ``fall''.
\<close>

fun alternating_list :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "alternating_list R [] \<longleftrightarrow> True"
| "alternating_list R [x] \<longleftrightarrow> True"
| "alternating_list R (x # y # xs) \<longleftrightarrow> (y,x) \<in> R \<and> alternating_list (R\<inverse>) (y # xs)"

lemma alternating_list_Cons_iff:
  "alternating_list R (x # xs) \<longleftrightarrow> xs = [] \<or> ((hd xs, x) \<in> R \<and> alternating_list (converse R) xs)"
  by (cases xs) auto

lemma alternating_list_append_iff:
  "alternating_list R (xs @ ys) \<longleftrightarrow> (let R' = if even (length xs) then R else converse R in
     alternating_list R xs \<and> alternating_list R' ys \<and> (xs = [] \<or> ys = [] \<or> (last xs, hd ys) \<in> R'))"
  by (induction R xs rule: alternating_list.induct)
     (auto simp: Let_def alternating_list_Cons_iff)


text \<open>
  A reverse-alternating list is the same as an alternating list except that it starts with a
  ``rise'' instead of a ``fall''. Equivalently, a reverse-alternating list is an alternating list
  with respect to the converse relation.
\<close>
abbreviation rev_alternating_list :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "rev_alternating_list R \<equiv> alternating_list (R\<inverse>)"

lemma alternating_list_rev:
  "alternating_list R (rev xs) \<longleftrightarrow> alternating_list (if odd (length xs) then R else converse R) xs"
  by (induction xs arbitrary: R)
     (auto simp: alternating_list_append_iff last_rev alternating_list_Cons_iff)

lemma alternating_list_map:
  assumes "alternating_list R xs"
  assumes "monotone_on (set xs) (\<lambda>x y. (x, y) \<in> R) (\<lambda>x y. (x, y) \<in> R') f"
  shows   "alternating_list R' (map f xs)"
proof -
  define A where "A = set xs"
  have "(f x, f y) \<in> R'" if "(x, y) \<in> R" "x \<in> A" "y \<in> A" for x y
    using assms(2) that by (auto simp: monotone_on_def A_def)
  moreover have "set xs \<subseteq> A"
    by (simp add: A_def)
  ultimately show ?thesis using assms(1)
    by (induction R xs arbitrary: R' rule: alternating_list.induct) auto
qed

lemma alternating_list_map_iff:
  assumes "monotone_on (set xs) (\<lambda>x y. (x, y) \<in> R) (\<lambda>x y. (x, y) \<in> R') f"
  assumes "strict_linear_order_on (set xs) R" "strict_linear_order_on (f ` set xs) R'"
  shows   "alternating_list R' (map f xs) \<longleftrightarrow> alternating_list R xs"
proof
  assume "alternating_list R xs"
  thus "alternating_list R' (map f xs)"
    by (intro alternating_list_map) (use assms in simp_all)
next
  assume "alternating_list R' (map f xs)"
  hence "alternating_list R (map (inv_into (set xs) f) (map f xs))"
  proof (rule alternating_list_map)
    have "monotone_on (f ` set xs) (\<lambda>x y. (x, y) \<in> R') (\<lambda>x y. (x, y) \<in> R) (inv_into (set xs) f)"
      by (rule monotone_on_inv_into) (use assms in simp_all)
    thus "monotone_on (set (map f xs)) (\<lambda>x y. (x, y) \<in> R') (\<lambda>x y. (x, y) \<in> R) (inv_into (set xs) f)"
      by simp
  qed
  also have "map (inv_into (set xs) f) (map f xs) = map (\<lambda>x. x) xs"
    unfolding map_map o_def
    by (intro map_cong inv_into_f_f monotone_on_imp_inj_on[OF assms(1)])
       (use assms in simp_all)
  finally show "alternating_list R xs"
    by simp
qed


subsection \<open>The set of alternating permutations on a set\<close>

definition alternating_permutations_of_set :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
  "alternating_permutations_of_set R A = {ys\<in>permutations_of_set A. alternating_list R ys}"

lemma finite_alternating_permutations_of_set [intro]: "finite (alternating_permutations_of_set R A)"
  unfolding alternating_permutations_of_set_def by simp

lemma alternating_permutations_of_set_code [code]:
  "alternating_permutations_of_set R A = Set.filter (alternating_list R) (permutations_of_set A)"
  by (simp add: alternating_permutations_of_set_def Set.filter_def)

abbreviation rev_alternating_permutations_of_set :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
  "rev_alternating_permutations_of_set R A \<equiv> alternating_permutations_of_set (converse R) A"

definition alt_permutes ("_ alt'_permutes\<^bsub>_\<^esub> _" [40,0,40] 41) where
  "f alt_permutes\<^bsub>R\<^esub> A \<longleftrightarrow> f permutes A \<and> alternating_list R (map f (sorted_list_of_set_wrt R A))"

abbreviation rev_alt_permutes ("_ rev'_alt'_permutes\<^bsub>_\<^esub> _" [40,0,40] 41) where
  "f rev_alt_permutes\<^bsub>R\<^esub> A \<equiv> f alt_permutes\<^bsub>converse R\<^esub> A"

abbreviation alt_permutes_less ("_ alt'_permutes _" [40,40] 41) where
  "f alt_permutes A \<equiv> f alt_permutes\<^bsub>{(x,y). x < y}\<^esub> A"

abbreviation rev_alt_permutes_less ("_ rev'_alt'_permutes _" [40,40] 41) where
  "f rev_alt_permutes A \<equiv> f rev_alt_permutes\<^bsub>{(x,y). x < y}\<^esub> A"



lemma alternating_permutations_of_set_empty [simp]:
  "alternating_permutations_of_set R {} = {[]}"
  by (auto simp: alternating_permutations_of_set_def)

lemma alternating_permutations_of_set_singleton [simp]:
  "alternating_permutations_of_set R {x} = {[x]}"
  by (auto simp: alternating_permutations_of_set_def)

lemma bij_betw_alternating_permutations_of_set:
  assumes "monotone_on A (\<lambda>x y. (x,y) \<in> R) (\<lambda>x y. (x,y) \<in> R') f"
  assumes "strict_linear_order_on A R" "strict_linear_order_on (f ` A) R'" "B = f  ` A"
  shows   "bij_betw (map f) (alternating_permutations_of_set R A) (alternating_permutations_of_set R' B)"
proof -
  have "inj_on f A"
    by (rule monotone_on_imp_inj_on[OF assms(1)]) (use assms(2,3) in simp_all)
  have inj: "inj_on (map f) (alternating_permutations_of_set R A)"
    by (rule inj_on_mapI[OF inj_on_subset[OF \<open>inj_on f A\<close>]])
       (auto simp: alternating_permutations_of_set_def permutations_of_set_def)

  have "map f ` alternating_permutations_of_set R A = alternating_permutations_of_set R' (f ` A)"
    (is "_ ` ?lhs = ?rhs")
  proof safe
    fix xs assume "xs \<in> ?lhs"
    thus "map f xs \<in> ?rhs" using assms
      by (auto simp: alternating_permutations_of_set_def permutations_of_set_def distinct_map alternating_list_map
                     inj_on_subset[OF \<open>inj_on f A\<close>])
  next
    fix xs assume xs: "xs \<in> ?rhs"
    hence set_xs: "set xs = f ` A"
      by (auto simp: alternating_permutations_of_set_def permutations_of_set_def)
    define ys where "ys = map (inv_into A f) xs"
    have mono: "monotone_on (f ` A) (\<lambda>x y. (x,y) \<in> R') (\<lambda>x y. (x,y) \<in> R) (inv_into A f)"
      by (intro monotone_on_inv_into) (use assms in simp_all)
    hence inj': "inj_on (inv_into A f) (f ` A)"
      by (rule monotone_on_imp_inj_on) (use assms \<open>inj_on f A\<close> in simp_all)
    have "ys \<in> ?lhs" using xs mono \<open>inj_on f A\<close> inj' assms(2,3)
      by (auto simp: ys_def alternating_permutations_of_set_def permutations_of_set_def distinct_map
               intro!: inj_on_subset[OF \<open>inj_on f A\<close>] alternating_list_map)
    moreover have "map f ys = map (\<lambda>x. x) xs"
      unfolding ys_def map_map o_def
      by (intro map_cong inv_into_f_f) (use \<open>inj_on f A\<close> set_xs in auto)
    ultimately show "xs \<in> map f ` ?lhs"
      by auto
  qed
  with inj show ?thesis using \<open>B = f ` A\<close>
    unfolding bij_betw_def by blast
qed
    
lemma alternating_permutations_of_set_glue:
  assumes A: "finite A" 
  assumes X: "X \<subseteq> A" and x: "x \<in> A - X" "\<And>y. y \<in> A-{x} \<Longrightarrow> (x,y) \<in> R"
  assumes xs: "xs \<in> alternating_permutations_of_set R X"
  assumes ys: "ys \<in> alternating_permutations_of_set R (A - X - {x})"
  defines "R' \<equiv> (if odd (card X) then R else R\<inverse>)"
  shows   "rev xs @ [x] @ ys \<in> alternating_permutations_of_set R' A"
proof -
  have "set (xs @ ys) \<subseteq> A - {x}"
    using xs ys X x unfolding alternating_permutations_of_set_def permutations_of_set_def
    by auto
  hence *: "y \<in> A - {x}" if "y \<in> set (xs @ ys)" for y
    using that by blast
  have length_xs: "length xs = card X"
    using xs distinct_card[of xs]
    unfolding alternating_permutations_of_set_def permutations_of_set_def by simp

  have "xs = [] \<or> (hd xs, x) \<in> R\<inverse>"
    using x(2)[OF *, of "hd xs"] by (cases "xs = []") auto
  moreover have "ys = [] \<or> (hd ys, x) \<in> R\<inverse>"
    using x(2)[OF *, of "hd ys"] by (cases "ys = []") auto
  ultimately have "alternating_list R' (rev xs @ [x] @ ys)"
    using xs ys unfolding alternating_list_append_iff R'_def alternating_permutations_of_set_def
    by (simp add: length_xs alternating_list_rev last_rev)
  moreover have "rev xs @ [x] @ ys \<in> permutations_of_set A"
    using xs ys X x unfolding alternating_permutations_of_set_def permutations_of_set_def
    by auto
  ultimately show ?thesis
    unfolding alternating_permutations_of_set_def by blast
qed

lemma alternating_permutations_of_set_split:
  assumes A: "finite A" 
  assumes z: "z \<in> A"
  assumes zs: "zs \<in> alternating_permutations_of_set R A"
  assumes k: "k < length zs" "zs ! k = z"
  defines "R' \<equiv> (if odd k then R else converse R)"
  obtains xs ys where
    "zs = rev xs @ [z] @ ys" "alternating_list R' xs" "alternating_list R' ys" 
    "distinct xs" "distinct ys" "length xs = k"
proof -
  have "set zs = A" "distinct zs"
    using zs unfolding alternating_permutations_of_set_def permutations_of_set_def by blast+
  with z(1) have "z \<in> set zs"
    by blast
  then obtain xs ys where zs_eq: "zs = xs @ z # ys"
    by (metis in_set_conv_decomp)

  have "zs ! length xs = z" "length xs < length zs"
    using k by (simp_all add: zs_eq)
  with \<open>distinct zs\<close> and k have k_eq: "k = length xs"
    using distinct_conv_nth by blast

  have "alternating_list R (xs @ z # ys)"
    using zs by (simp add: alternating_permutations_of_set_def zs_eq)
  hence "alternating_list R' (rev xs)" "alternating_list R' ys"
    by (auto simp: alternating_list_append_iff alternating_list_Cons_iff
                   Let_def k_eq R'_def alternating_list_rev)
  thus ?thesis
    using \<open>distinct zs\<close> k_eq by (intro that[of "rev xs" ys]) (simp_all add: zs_eq)
qed

lemma inj_on_glue_alternating_permutations_of_set:
  fixes A :: "'a set"
  assumes x: "x \<in> A" "\<And>y. y \<in> A - {x} \<Longrightarrow> (x, y) \<in> R"
  defines "P \<equiv> (\<lambda>X::'a set. alternating_permutations_of_set R X)"
  shows   "inj_on (\<lambda>(xs, ys). rev xs @ [x] @ ys) ((\<Union>X\<in>Pow (A-{x}). P X \<times> P (A - X - {x})))"
proof (rule inj_onI, clarify, goal_cases)
  case (1 xs1 ys1 xs2 ys2)
  from 1 have "rev xs1 @ x # ys1 = rev xs2 @ x # ys2"
    by simp
  moreover have "x \<notin> set xs1" "x \<notin> set xs2" "x \<notin> set ys1" "x \<notin> set ys2" 
    using 1 unfolding P_def alternating_permutations_of_set_def permutations_of_set_def
    by auto
  ultimately show "xs1 = xs2 \<and> ys1 = ys2"
    by (subst (asm) append_Cons_eq_iff) auto
qed


subsection \<open>Zigzag numbers\<close>

text \<open>
  The zigzag numbers $E_n$ count the number of alternating permutations on a linearly ordered set
  with $n$ elements. Note that varying conventions exist; e.g.\ these are also sometimes
  also called ``Euler numbers'' or ``Euler zigzag numbers''.~\oeiscite{A000111}

  In our formalisation, ``Euler numbers'' are something closely related but different,
  following the conventions of ProofWiki and Mathematica.

  It is easy to see that we can w.l.o.g.\ assume that the set in question is the integers
  from $1$ to $n$ and the order in question is the natural order $<$.
\<close>
definition zigzag_number :: "nat \<Rightarrow> nat" where
  "zigzag_number n = card (alternating_permutations_of_set {(x,y). x < y} {1..n})"

lemma zigzag_number_0 [simp]: "zigzag_number 0 = 1"
  and zigzag_number_1 [simp]: "zigzag_number (Suc 0) = 1"
  by (simp_all add: zigzag_number_def)

lemma card_alternating_permutations_of_set:
  assumes "strict_linear_order_on A R" "finite A"
  shows   "card (alternating_permutations_of_set R A) = zigzag_number (card A)"
proof -
  obtain f :: "nat \<Rightarrow> 'a" where f:
    "bij_betw f {1..card A} A" "monotone_on {1..card A} (<) (\<lambda>x y. (x,y) \<in> R) f"
    using strict_linear_orderE_bij_betw'[OF assms] .
  define P1 where "P1 = alternating_permutations_of_set {(x, y). x < y} {1..card A}"
  define P2 where "P2 = alternating_permutations_of_set R A"

  have "zigzag_number (card A) = card P1"
    by (simp add: zigzag_number_def P1_def)
  also have "bij_betw (map f) P1 P2"
    unfolding P1_def P2_def
  proof (rule bij_betw_alternating_permutations_of_set)
    show "strict_linear_order_on (f ` {1..card A}) R" and "A = f ` {1..card A}"
      using assms f(1) by (simp_all add: bij_betw_def)
  qed (use f(2) in auto)
  hence "card P1 = card P2"
    by (rule bij_betw_same_card)
  finally show ?thesis
    by (simp add: P2_def)
qed

text \<open>
  The zigzag numbers satisfy the Catalan-like recurrence
  \[ 2 E_{n+1} = \sum_{k=0}^n {n \choose k} E_k E_{n-k}\ . \]

  The idea behind the proof is to look at a linearly ordered set $A$ of size $n+1$ (with $n > 0$)
  and its largest element $x$. We now do the following:

    \<^enum> Pick a number $0\leq k\leq n$.

    \<^enum> Pick a subset $X\subseteq A\setminus\{x\}$ of elements to occur to the left of $A$
      in our permutation. We have ${n\choose k}$ choices for this.

    \<^enum> Pick an alternating permutation \<open>xs\<close> of $X$ and a reverse-alternating permutation of
      \<open>ys\<close> of $A\setminus(X\cup\{x\})$. We have $E_k$ and $E_{n-k}$ choices for this, respectively.

    \<^enum> Return the permutation \<open>rev xs @ [x] @ ys\<close>

  This process constructs exactly all alternating and reverse-alternating permutations on $A$.
  Moreover, the alternating and reverse-alternating permutations of $A$ are disjoint and have
  the same cardinality since $|A| \geq 2$.

  Thus if we sum the number of possibilities we counted above over all $k$,
  we obtain exactly $2 E_{n+1}$.
\<close>
theorem zigzag_number_Suc:
  assumes "n > 0"
  shows   "2 * zigzag_number (Suc n) =
             (\<Sum>k\<le>n. (n choose k) * (zigzag_number k * zigzag_number (n - k)))"
proof -
  define P where "P = (\<lambda>X::nat set. alternating_permutations_of_set {(x,y). x < y} X)"
  define P' where "P' = (\<lambda>X::nat set. alternating_permutations_of_set {(x,y). x > y} X)"
  define glue :: "nat list \<times> nat list \<Rightarrow> nat list" where "glue = (\<lambda>(xs, ys). rev xs @ [1] @ ys)"
  define A where "A = {1..n+1}"
  have [intro]: "finite (P X)" "finite (P' X)" for X
    unfolding P_def P'_def by auto
  let ?less = "{(x,y). x < (y::nat)}"
  let ?greater = "{(x,y). x > (y::nat)}"
  have [simp]: "converse ?less = ?greater" "converse ?greater = ?less"
    by (auto simp: converse_def)
  define R where "R = (\<lambda>k. if odd (k::nat) then ?less else ?greater)"

  have disjoint: "P A \<inter> P' A = {}"
  proof -
    have False if "zs \<in> P A" "zs \<in> P' A" for zs
    proof -
      have zs: "set zs = A" "distinct zs" "alternating_list ?less zs" "alternating_list ?greater zs"
        using that
        unfolding P_def P'_def alternating_permutations_of_set_def permutations_of_set_def
        by simp_all
      have "length zs \<ge> 2"
        using distinct_card[of zs] zs \<open>n > 0\<close> by (simp add: A_def)
      then obtain x y zs' where zs_eq: "zs = x # y # zs'"
        by (auto simp: Suc_le_length_iff numeral_2_eq_2)
      show False
        using zs by (simp add: zs_eq)
    qed
    thus ?thesis
      by blast
  qed

  have "card (glue ` (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1}))) = 
        card (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1}))"
    unfolding glue_def P_def
    by (rule card_image, rule inj_on_glue_alternating_permutations_of_set)
       (auto simp: A_def)

  also have "glue ` (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1})) = P A \<union> P' A"
  proof (rule antisym)
    have "glue (xs, ys) \<in> P A \<union> P' A" 
      if X: "X \<in> Pow (A - {1})" and xs: "xs \<in> P X" and ys: "ys \<in> P (A - X - {1})" for X xs ys
    proof -
      have "rev xs @ [1] @ ys \<in> alternating_permutations_of_set
              (if odd (card X) then ?less else ?less\<inverse>) A"
        by (rule alternating_permutations_of_set_glue[of A X 1 ?less xs ys])
           (use X xs ys in \<open>auto simp: A_def P_def\<close>)
      hence "glue (xs, ys) \<in> (if odd (card X) then P A else P' A)"
        by (auto simp: glue_def P_def P'_def)
      also have "\<dots> \<subseteq> P A \<union> P' A"
        by auto
      finally show "glue (xs, ys) \<in> P A \<union> P' A" .
    qed
    thus "glue ` (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1})) \<subseteq> P A \<union> P' A"
      by blast
  next
    have "zs \<in> glue ` (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1}))" if zs: "zs \<in> P A \<union> P' A" for zs
    proof -
      from zs have set_zs: "set zs = A" and "distinct zs"
        by (auto simp: P_def P'_def alternating_permutations_of_set_def permutations_of_set_def)
      have "length zs = Suc n"
        using set_zs \<open>distinct zs\<close> distinct_card[of zs] by (simp add: A_def)
      from set_zs have "1 \<in> set zs"
        by (auto simp: A_def)
      then obtain k where k: "k < length zs" "zs ! k = 1"
        by (meson in_set_conv_nth)
      define R' where "R' = (if zs \<in> P A then ?less else ?greater)"
      obtain xs ys where xs_ys:
        "zs = rev xs @ [1] @ ys" "alternating_list (if odd k then R' else R'\<inverse>) xs"
        "alternating_list (if odd k then R' else R'\<inverse>) ys" "distinct xs" "distinct ys" "length xs = k"
        by (rule alternating_permutations_of_set_split[of A 1 zs R' k])
           (use k zs in \<open>auto simp: A_def R'_def P_def P'_def\<close>)
      have set_xs: "set xs \<subseteq> A - {1}"
        using \<open>distinct zs\<close> unfolding set_zs [symmetric] xs_ys(1) by (auto simp: xs_ys(1))
      have set_ys: "set ys = A - set xs - {1}"
        using \<open>distinct zs\<close> unfolding set_zs [symmetric] xs_ys(1) by (auto simp: xs_ys(1))
      have "odd k \<longleftrightarrow> zs \<in> P A"
      proof -
        have 1: "xs \<noteq> [] \<or> ys \<noteq> []"
          using xs_ys(1) \<open>n > 0\<close> \<open>length zs = Suc n\<close> by (auto simp: A_def)
        have 2: "x \<in> A - {1}" if "x \<in> set (xs @ ys)" for x
        proof -
          have "x \<in> set (xs @ ys)"
            using that by simp
          also have "\<dots> \<subseteq> set zs - {1}"
            using \<open>distinct zs\<close> by (auto simp add: xs_ys(1))
          finally show ?thesis
            by (simp add: set_zs)
        qed
        have 3: "xs = [] \<or> 1 < hd xs" 
          using 2[of "hd xs"] by (cases "xs = []") (auto simp: hd_in_set A_def)
        have 4: "ys = [] \<or> 1 < hd ys" 
          using 2[of "hd ys"] by (cases "ys = []") (auto simp: hd_in_set A_def)
        have "alternating_list R' zs"
          using zs by (auto simp: R'_def P_def P'_def alternating_permutations_of_set_def)
        thus ?thesis
          using 1 3 4 xs_ys(2,3) \<open>length xs = k\<close> zs
          by (auto simp: xs_ys(1) alternating_list_append_iff alternating_list_Cons_iff
                         alternating_list_rev Let_def R'_def last_rev split: if_splits)
      qed
      hence "(if odd k then R' else R'\<inverse>) = ?less"
        by (auto simp: R'_def)
      with xs_ys and set_ys have "zs = glue (xs, ys)" "xs \<in> P (set xs)" "ys \<in> P (A - set xs - {1})"
        by (simp_all add: glue_def P_def alternating_permutations_of_set_def permutations_of_set_def)
      thus "zs \<in> glue ` (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1}))"
        using set_xs by blast
    qed
    thus "P A \<union> P' A \<subseteq> glue ` (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1}))"
      by blast
  qed

  also have "card (P A \<union> P' A) = card (P A) + card (P' A)"
    by (subst card_Un_disjoint) (use disjoint in auto)
  also have "card (P A) = zigzag_number (Suc n)"
    unfolding P_def by (subst card_alternating_permutations_of_set) (auto simp: A_def)
  also have "card (P' A) = zigzag_number (Suc n)"
    unfolding P'_def by (subst card_alternating_permutations_of_set) (auto simp: A_def)

  also have "card (\<Union>X\<in>Pow (A-{1}). P X \<times> P (A - X - {1})) = 
               (\<Sum>X\<in>Pow (A - {1}). card (P X \<times> P (A - X - {1})))"
  proof (intro card_UN_disjoint ballI impI)
    fix X Y assume "X \<in> Pow (A - {1})" "Y \<in> Pow (A - {1})" "X \<noteq> Y"
    show "P X \<times> P (A - X - {1}) \<inter> P Y \<times> P (A - Y - {1}) = {}"
      using \<open>X \<noteq> Y\<close> unfolding P_def alternating_permutations_of_set_def permutations_of_set_def
      by blast
  qed (auto simp: A_def)
  also have "\<dots> = (\<Sum>X\<in>Pow (A - {1}). zigzag_number (card X) * zigzag_number (n - card X))"
  proof (rule sum.cong)
    fix X assume X: "X \<in> Pow (A - {1})"
    have [simp]: "finite X"
      by (rule finite_subset[of _ A]) (use X in \<open>auto simp: A_def\<close>)
    have "card (P X \<times> P (A - X - {1})) = card (P X) * card (P (A - X - {1}))"
      by (rule card_cartesian_product)
    also have "card (P X) = zigzag_number (card X)"
      unfolding P_def by (rule card_alternating_permutations_of_set) (use X in auto)
    also have "card (P (A - X - {1})) = zigzag_number (card (A - X - {1}))"
      unfolding P_def by (rule card_alternating_permutations_of_set) (use X in \<open>auto simp: A_def\<close>)
    also have "card (A - X - {1}) = card (A - X) - 1"
      using X by (subst card_Diff_subset) (auto simp: A_def)
    also have "card (A - X) = card A - card X"
      using X finite_subset[of X A] by (subst card_Diff_subset) (auto simp: A_def)
    also have "card A = n + 1"
      by (simp add: A_def)
    finally show "card (P X \<times> P (A - X - {1})) = 
                    zigzag_number (card X) * zigzag_number (n - card X)"
      by simp
  qed auto

  also have "Pow (A - {1}) = (\<Union>k\<le>n. {X\<in>Pow (A-{1}). card X = k})"
    by (subst Pow_conv_subsets_of_size) (simp_all add: A_def)
  also have "(\<Sum>X\<in>\<dots>. zigzag_number (card X) * zigzag_number (n - card X)) =
               (\<Sum>k\<le>n. card {X. X \<subseteq> A-{1} \<and> card X = k} * (zigzag_number k * zigzag_number (n - k)))"
    by (subst sum.UNION_disjoint) (auto simp: A_def)
  also have "\<dots> = (\<Sum>k\<le>n. (n choose k) * (zigzag_number k * zigzag_number (n - k)))"
    using n_subsets[of "A - {1}"] by (simp add: A_def)
  finally show ?thesis
    by simp
qed

text \<open>
  The exponential generating function of the zigzag numbers is:
    \[f(x) = \sum_{n\geq 0} \frac{E_n}{n!} x^n = \sec x + \tan x\]
  This follows from the fact that by the above recurrence for $E_n$, both $f$ and $\sin + \tan$
  satisfy the ordinary differential equation $2 f'(x) = 1 + f(x)^2$
\<close>
corollary exponential_generating_function_zigzag_number:
  "Abs_fps (\<lambda>n. of_nat (zigzag_number n) / fact n :: 'a :: field_char_0) = fps_sec 1 + fps_tan 1"
proof -
  define F where "F \<equiv> Abs_fps (\<lambda>n. of_nat (zigzag_number n) / fact n :: 'a)"
  define G where "G \<equiv> (fps_sec 1 + fps_tan 1 :: 'a fps)"
  have [simp]: "fps_nth F 0 = 1" "fps_nth F (Suc 0) = 1"
    by (simp_all add: F_def)
  have F_Suc: "fps_nth F (Suc n) = (\<Sum>k\<le>n. fps_nth F k * fps_nth F (n - k)) / (2 * of_nat (n + 1))"
    if "n > 0" for n
  proof -
    have "2 * fps_nth F (Suc n) = of_nat (2 * zigzag_number (Suc n)) / fact (Suc n)"
      by (simp add: F_def)
    also have "\<dots> = (\<Sum>k\<le>n. fps_nth F k * fps_nth F (n - k)) / of_nat (n + 1)"
      by (subst zigzag_number_Suc) (use that in \<open>auto simp: F_def mult_ac binomial_fact sum_divide_distrib\<close>)
    finally show ?thesis
      unfolding of_nat_mult by (simp add: divide_simps mult_ac del: of_nat_Suc)
  qed
  have "2 * fps_deriv F = 1 + F ^ 2"
    by (rule fps_ext) (auto simp: fps_nth_power_0 F_Suc fps_square_nth divide_simps simp del: of_nat_Suc)
  have "2 * fps_deriv G = 1 + G ^ 2" 
    using fps_sec_square_conv_fps_tan_square[where ?'a = 'a]
    by (simp add: G_def fps_sec_deriv fps_tan_deriv' power2_eq_square algebra_simps)

  have "fps_nth F n = fps_nth G n" for n
  proof (induction rule: less_induct)
    case (less n)
    show ?case
    proof (cases "n = 0")
      case True
      thus ?thesis
        by (auto simp: F_def G_def)
    next
      case n: False
      have "2 * of_nat n * fps_nth F n = fps_nth (2 * fps_deriv F) (n - 1)"
        using n by simp
      also have "2 * fps_deriv F = 1 + F ^ 2"
        by fact
      also have "fps_nth (1 + F ^ 2) (n - 1) = fps_nth 1 (n - 1) + (\<Sum>k\<le>n-1. F $ k * F $ (n - Suc k))"
        using n by (simp add: fps_square_nth)
      also have "(\<Sum>k\<le>n-1. F $ k * F $ (n - Suc k)) = (\<Sum>k\<le>n-1. G $ k * G $ (n - Suc k))"
        by (intro sum.cong arg_cong2[of _ _ _ _ "(*)"] less.IH) (use n in auto)
      also have "fps_nth 1 (n - 1) + \<dots> = fps_nth (1 + G ^ 2) (n - 1)"
        using n by (simp add: fps_square_nth)
      also have "(1 + G ^ 2) = 2 * fps_deriv G"
        using \<open>2 * fps_deriv G = 1 + G ^ 2\<close> ..
      also have "fps_nth \<dots> (n - 1) = 2 * of_nat n * fps_nth G n"
        using n by simp
      finally show ?thesis
        using n by simp
    qed
  qed
  thus "F = G"
    by (rule fps_ext)
qed

text \<open>
  Lastly, we get the following explicit relationships between the zigzag numbers
  and the coefficients appearing in the Maclaurin series of $\sec$ and $\tan$.
\<close>
corollary zigzag_number_conv_fps_sec:
  assumes "even n"
  shows   "real (zigzag_number n) = fps_nth (fps_sec 1) n * fact n"
proof -
  have "real (zigzag_number n) / fact n = 
          fps_nth (Abs_fps (\<lambda>n. real (zigzag_number n) / fact n)) n"
    by simp
  also have "Abs_fps (\<lambda>n. real (zigzag_number n) / fact n) = fps_sec 1 + fps_tan 1"
    by (rule exponential_generating_function_zigzag_number)
  also have "fps_nth \<dots> n = fps_nth (fps_sec 1) n"
    using assms by (simp add: fps_nth_tan_even)
  finally show ?thesis
    by (simp add: field_simps)
qed

corollary zigzag_number_conv_fps_tan:
  assumes "odd n"
  shows   "real (zigzag_number n) = fps_nth (fps_tan 1) n * fact n"
proof -
  have "real (zigzag_number n) / fact n = 
          fps_nth (Abs_fps (\<lambda>n. real (zigzag_number n) / fact n)) n"
    by simp
  also have "Abs_fps (\<lambda>n. real (zigzag_number n) / fact n) = fps_sec 1 + fps_tan 1"
    by (rule exponential_generating_function_zigzag_number)
  also have "fps_nth \<dots> n = fps_nth (fps_tan 1) n"
    using assms by (simp add: fps_nth_sec_odd)
  finally show ?thesis
    by (simp add: field_simps)
qed



subsection \<open>Alternating permutations with a fixed first element\<close>

text \<open>
  In order to study the \<^emph>\<open>Entringer numbers\<close>, a generalisation of the zigzag numbers,
  we introduce the set of alternating permutations on a set that start with some fixed
  element \<open>x\<close>.
\<close>
definition alternating_permutations_of_set_with_hd :: 
  "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a list set" where
  "alternating_permutations_of_set_with_hd R A x =
     {xs\<in>alternating_permutations_of_set R A. xs \<noteq> [] \<and> hd xs = x}"

lemma alternating_permutations_of_set_with_hd_singleton:
  "alternating_permutations_of_set_with_hd R {y} x = (if x = y then {[x]} else {})"
  by (auto simp: alternating_permutations_of_set_with_hd_def alternating_permutations_of_set_def)

lemma alternating_permutations_of_set_with_hd_outside:
  assumes "x \<notin> A"
  shows   "alternating_permutations_of_set_with_hd R A x = {}"
proof -
  {
    fix xs assume "xs \<in> alternating_permutations_of_set_with_hd R A x"
    hence "set xs = A" "xs \<noteq> []" "hd xs = x"
      by (auto simp: alternating_permutations_of_set_with_hd_def 
                     alternating_permutations_of_set_def permutations_of_set_def)
    moreover from this have "hd xs \<in> set xs"
      by (intro hd_in_set)
    ultimately have "x \<in> A"
      by auto
    hence False
      using assms by simp
  }
  thus ?thesis
    by blast
qed

lemma alternating_permutations_of_set_with_hd_least:
  assumes "strict_linear_order_on A R"
  assumes "\<And>y. y \<in> A - {x} \<Longrightarrow> (x, y) \<in> R" "x \<in> A" "A \<noteq> {x}" "finite A"
  shows   "alternating_permutations_of_set_with_hd R A x = {}"
proof -
  from assms have "A - {x} \<noteq> {}"
    by auto
  hence "card (A - {x}) > 0"
    using \<open>finite A\<close> card_gt_0_iff by blast
  hence "card A \<ge> 2"
    by (subst (asm) card_Diff_subset) (use assms in auto)

  {
    fix xs assume "xs \<in> alternating_permutations_of_set_with_hd R A x"
    hence xs: "set xs = A" "xs \<noteq> []" "hd xs = x" "alternating_list R xs" "distinct xs"
      by (auto simp: alternating_permutations_of_set_with_hd_def 
                     alternating_permutations_of_set_def permutations_of_set_def)
    have "length xs \<ge> 2"
      using distinct_card[of xs] xs \<open>card A \<ge> 2\<close> by simp
    then obtain x' y xs' where xs_eq: "xs = x' # y # xs'"
      by (auto simp: Suc_le_length_iff numeral_2_eq_2)
    have [simp]: "x' = x"
      using \<open>hd xs = x\<close> by (simp add: xs_eq)
    from xs(4) have "(y, x) \<in> R"
      by (simp add: xs_eq)
    moreover from this and assms(1) have "y \<in> A - {x}"
      using \<open>set xs = A\<close>  by (auto simp: strict_linear_order_on_def irrefl_def xs_eq)
    with assms(2)[of y] and \<open>set xs = A\<close> have "(x, y) \<in> R"
      by (auto simp: xs_eq)
    ultimately have False
      using strict_linear_order_on_asym_on[OF assms(1)] \<open>x \<in> A\<close> \<open>y \<in> A - {x}\<close> 
      by (auto simp: asym_on_def)
  }
  thus ?thesis
    by blast
qed

lemma alternating_permutations_of_set_with_hd_greatest:
  assumes "strict_linear_order_on A R"
  assumes "\<And>y. y \<in> A - {x} \<Longrightarrow> (y, x) \<in> R" "x \<in> A"
  shows   "bij_betw (\<lambda>xs. x # xs)
             (rev_alternating_permutations_of_set R (A - {x}))
             (alternating_permutations_of_set_with_hd R A x)"
proof -
  have [simp]: "A \<noteq> {}"
    using \<open>x \<in> A\<close> by auto
  show ?thesis
  proof (rule bij_betwI)
    show "(#) x \<in> rev_alternating_permutations_of_set R (A - {x}) \<rightarrow>
                    alternating_permutations_of_set_with_hd R A x"
    proof (safe, goal_cases)
      case (1 xs)
      hence "set xs \<subseteq> A - {x}"
        by (auto simp: alternating_permutations_of_set_def permutations_of_set_def)
      moreover have "hd xs \<in> set xs \<or> xs = []"
        using hd_in_set by blast
      ultimately have "hd xs \<in> A - {x} \<or> xs = []"
        by blast
      hence "(hd xs, x) \<in> R \<or> xs = []"
        using assms(2) by blast
      thus ?case
        using \<open>x \<in> A\<close> assms(2) 1
        by (auto simp: alternating_permutations_of_set_with_hd_def alternating_permutations_of_set_def
                       permutations_of_set_nonempty alternating_list_Cons_iff)
    qed
  next
    show "tl \<in> alternating_permutations_of_set_with_hd R A x \<rightarrow>
                 rev_alternating_permutations_of_set R (A - {x})"
      by (auto simp: alternating_permutations_of_set_with_hd_def
                     alternating_permutations_of_set_def permutations_of_set_nonempty
                     alternating_list_Cons_iff)
  qed (auto simp: alternating_permutations_of_set_with_hd_def)  
qed

lemma UN_alternating_permutations_of_set_with_hd:
  assumes "A \<noteq> {}"
  shows   "(\<Union>x\<in>A. alternating_permutations_of_set_with_hd R A x) =
             alternating_permutations_of_set R A"
  using assms
  by (force simp: alternating_permutations_of_set_with_hd_def
                  alternating_permutations_of_set_def permutations_of_set_def intro!: hd_in_set)

lemma alternating_permutations_of_set_with_hd_split_first:
  assumes "strict_linear_order_on A R" "x \<in> A" "A \<noteq> {x}"
  shows   "bij_betw ((#) x)
            (\<Union>y\<in>{y\<in>A-{x}. (y,x)\<in>R}. alternating_permutations_of_set_with_hd (converse R) (A - {x}) y)
            (alternating_permutations_of_set_with_hd R A x)"
proof -
  have [simp]: "A \<noteq> {}"
    using assms by auto
  have "A - {x} \<noteq> {}"
    using assms by blast
 
  show ?thesis
  proof (rule bij_betwI)
    show "(#) x \<in> \<Union> (alternating_permutations_of_set_with_hd (R\<inverse>) (A - {x}) ` {y \<in> A - {x}. (y, x) \<in> R}) \<rightarrow>
                   alternating_permutations_of_set_with_hd R A x"
    proof (intro Pi_I; elim UN_E, goal_cases)
      case (1 xs y)
      have xs: "xs \<in> permutations_of_set (A - {x})" "alternating_list (converse R) xs" "hd xs = y"
        using 1 by (auto simp: alternating_permutations_of_set_with_hd_def 
                               alternating_permutations_of_set_def)
      have "x # xs \<in> permutations_of_set A"
        using xs \<open>x \<in> A\<close> by (auto simp: permutations_of_set_nonempty)
      moreover have "alternating_list R (x # xs)"
        using xs 1 by (auto simp: alternating_list_Cons_iff)
      ultimately show "x # xs \<in> alternating_permutations_of_set_with_hd R A x"
        unfolding alternating_permutations_of_set_with_hd_def
        by (auto simp: alternating_permutations_of_set_def)
    qed
  next
    show "tl \<in> alternating_permutations_of_set_with_hd R A x \<rightarrow>
                  \<Union> (alternating_permutations_of_set_with_hd (R\<inverse>) (A - {x}) ` {y \<in> A - {x}. (y, x) \<in> R})"
    proof (safe, goal_cases)
      case (1 xs)
      have xs: "xs \<in> permutations_of_set A" "alternating_list R xs" "hd xs = x"
        using 1 by (auto simp: alternating_permutations_of_set_with_hd_def 
                               alternating_permutations_of_set_def)
      have "xs \<noteq> []"
        using xs assms by (auto simp: permutations_of_set_def)
      then obtain ys where xs_eq: "xs = x # ys"
        using xs(3) by (cases xs) auto

      have ys: "ys \<in> permutations_of_set (A - {x})"
        using xs by (auto simp: permutations_of_set_nonempty xs_eq)
      hence "set ys = A - {x}"
        by (auto simp: permutations_of_set_def)
      hence "ys \<noteq> []"
        using \<open>A - {x} \<noteq> {}\<close> by (intro notI) auto

      have "hd ys \<in> A"
        using hd_in_set[of ys] \<open>set ys = A - {x}\<close> \<open>ys \<noteq> []\<close> by auto
      moreover have "rev_alternating_list R ys" "(hd ys, x) \<in> R"
        using xs \<open>ys \<noteq> []\<close> by (auto simp: xs_eq alternating_list_Cons_iff)
      moreover have "(hd ys, hd ys) \<notin> R"
        using assms(1) by (auto simp: strict_linear_order_on_def irrefl_def)
      ultimately show ?case
        using \<open>ys \<noteq> []\<close> ys
        by (auto simp: xs_eq alternating_permutations_of_set_with_hd_def
                       alternating_permutations_of_set_def)
    qed
  qed (auto simp: alternating_permutations_of_set_with_hd_def)
qed

lemma bij_betw_alternating_permutations_of_set_with_hd_flip:
  assumes "x \<le> n"
  shows   "bij_betw (map (\<lambda>k. n - k))
             (alternating_permutations_of_set_with_hd {(x::nat,y). x < y} {0..n} x)
             (alternating_permutations_of_set_with_hd {(x::nat,y). x > y} {0..n} (n - x))"
proof -
  have *: "bij_betw (\<lambda>k. n - k) {0..n} {0..n}"
    by (rule bij_betwI[of _ _ _ "\<lambda>k. n - k"]) auto
  have "bij_betw (map ((-) n))
          (alternating_permutations_of_set {(x, y). x < y} {0..n})
          (alternating_permutations_of_set {(x, y). y < x} {0..n})"
    by (rule bij_betw_alternating_permutations_of_set)
       (use * in \<open>auto simp: monotone_on_def image_def bij_betw_def\<close>)

  thus ?thesis
    unfolding alternating_permutations_of_set_with_hd_def
  proof (rule bij_betw_Collect, goal_cases)
    case (1 xs)
    hence "xs \<noteq> []" "set xs = {0..n}"
      by (auto simp: alternating_permutations_of_set_def permutations_of_set_def)
    with hd_in_set[of xs] have "hd xs \<le> n"
      by auto
    thus ?case using \<open>xs \<noteq> []\<close> assms
      by (auto simp: hd_map)
  qed
qed



subsection \<open>Entringer numbers\<close>

text \<open>
  The Entringer number $E_{n,k}$ now counts the number of alternating permutations
  on a set with $n+1$ elements that start with the (unique) element of rank $k$,
  i.e.\ the $k$-th largest element of the set.~\oeiscite{A008282}

  As we will see, it suffices to w.l.o.g.\ only consider sets of integers of the form
  $\{0, \ldots, n\}$.
\<close>

definition entringer_number :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "entringer_number n k = 
     card (alternating_permutations_of_set_with_hd {(x,y). x < y} {0..n} k)"

lemma entringer_number_0_0 [simp]: "entringer_number 0 0 = 1"
  and entring_number_0_left [simp]: "k \<noteq> 0 \<Longrightarrow> entringer_number 0 k = 0"
  by (simp_all add: entringer_number_def alternating_permutations_of_set_with_hd_singleton)

lemma entringer_number_0_right [simp]:
  assumes "n > 0"
  shows   "entringer_number n 0 = 0"
proof -
  have "alternating_permutations_of_set_with_hd {(x,y). x < y} {0..n} 0 = {}"
    by (rule alternating_permutations_of_set_with_hd_least) (use assms in auto)
  thus ?thesis
    using assms by (simp add: entringer_number_def)
qed

lemma entringer_number_greater_eq_0 [simp]:
  assumes "k > n"
  shows   "entringer_number n k = 0"
proof -
  have "alternating_permutations_of_set_with_hd {(x,y). x < y} {0..n} k = {}"
    by (rule alternating_permutations_of_set_with_hd_outside) (use assms in auto)
  thus ?thesis
    using assms by (simp add: entringer_number_def)
qed

theorem card_alternating_permutations_of_set_with_hd:
  assumes "strict_linear_order_on A R" "finite A" "x \<in> A"
  shows   "card (alternating_permutations_of_set_with_hd R A x) =
             entringer_number (card A - 1) (card {y\<in>A-{x}. (y,x) \<in> R})"
proof -
  define n where "n = card A - 1"
  have "A \<noteq> {}"
    using \<open>x \<in> A\<close> by auto
  with \<open>finite A\<close> have "card A > 0"
    using card_gt_0_iff by blast
  hence "card A = Suc n"
    by (auto simp: n_def)
  hence *: "{0..n} = {0..<card A}"
    by auto

  obtain f :: "nat \<Rightarrow> 'a" where f:
    "bij_betw f {0..n} A" "monotone_on {0..n} (<) (\<lambda>x y. (x,y) \<in> R) f"
    using strict_linear_orderE_bij_betw[OF assms(1,2)] unfolding * .
  obtain k where k: "k \<le> n" "f k = x"
    using f(1) \<open>x \<in> A\<close> by (auto simp: bij_betw_def)
  have R_f_iff: "(f x, f y) \<in> R \<longleftrightarrow> x < y" if "x \<le> n" "y \<le> n" for x y
    by (rule monotone_on_strict_linear_orderD[OF f(2)])
       (use assms that f(1) in \<open>auto simp: bij_betw_def\<close>)
  have f_eq_iff: "f x = f y \<longleftrightarrow> x = y" if "x \<le> n" "y \<le> n" for x y
    using f(1) that by (auto simp: bij_betw_def inj_on_def)

  have "bij_betw f {i\<in>{0..n}. i < k} {y\<in>A. (y, x) \<in> R}"
    using f(1) by (rule bij_betw_Collect) (use f(2) k in \<open>auto simp: monotone_on_def R_f_iff\<close>)
  hence "card {i\<in>{0..n}. i < k} = card {y\<in>A. (y, x) \<in> R}"
    by (rule bij_betw_same_card)
  also have "{i\<in>{0..n}. i < k} = {..<k}"
    using k by auto
  also have "{y\<in>A. (y, x) \<in> R} = {y\<in>A-{x}. (y, x) \<in> R}"
    using \<open>x \<in> A\<close> assms by (auto simp: strict_linear_order_on_def irrefl_def)
  finally have k_eq: "k = card {y\<in>A-{x}. (y, x) \<in> R}"
    by simp

  have "bij_betw (map f)
          (alternating_permutations_of_set_with_hd {(x,y). x < y} {0..n} k)
          (alternating_permutations_of_set_with_hd R A x)"
    unfolding alternating_permutations_of_set_with_hd_def
    using bij_betw_alternating_permutations_of_set
  proof (rule bij_betw_Collect)
    show "A = f ` {0..n}" "strict_linear_order_on (f ` {0..n}) R"
      using f(1) assms by (simp_all add: bij_betw_def)
  next
    fix xs assume "xs \<in> alternating_permutations_of_set {(x, y). x < y} {0..n}"
    hence xs: "set xs = {0..n}" "xs \<noteq> []"
      by (auto simp: alternating_permutations_of_set_def permutations_of_set_def)
    show "(map f xs \<noteq> [] \<and> hd (map f xs) = x) \<longleftrightarrow> (xs \<noteq> [] \<and> hd xs = k)"
      using k hd_in_set[of xs] xs by (auto simp: hd_map f_eq_iff)
  qed (use f assms in \<open>auto simp: hd_map\<close>)
  hence "card (alternating_permutations_of_set_with_hd {(x,y). x < y} {0..n} k) =
         card (alternating_permutations_of_set_with_hd R A x)"
    by (rule bij_betw_same_card)
  also have "card (alternating_permutations_of_set_with_hd {(x,y). x < y} {0..n} k) =
             entringer_number n k"
    unfolding entringer_number_def by simp
  finally show ?thesis
    by (simp add: n_def k_eq)
qed

text \<open>
  It is not difficult to show that $E_{n,n} = E_n$, i.e.\ the Entringer numbers really
  are a generalisation of the Euler numbers. The idea is that if we have an alternating
  permutation of $n$ elements $0, 1, \ldots, n$ that starts with largest one (i.e.\ $n$)
  then the list we obtain after dropping the initial element is a reverse-alternating
  permutation of $0, 1, \ldots, n-1$ with no further restrictions, and this map is one-to-one.
\<close>
lemma entringer_number_same [simp]:
  "entringer_number n n = zigzag_number n"
proof (cases "n = 0")
  case False
  have "bij_betw (\<lambda>xs. n # xs)
               (rev_alternating_permutations_of_set {(x, y). x < y} ({0..n}-{n}))
               (alternating_permutations_of_set_with_hd {(x, y). x < y} {0..n} n)"
    by (rule alternating_permutations_of_set_with_hd_greatest) auto
  hence "card (rev_alternating_permutations_of_set {(x, y). x < y} ({0..n}-{n})) =
         card (alternating_permutations_of_set_with_hd {(x, y). x < y} {0..n} n)"
    by (rule bij_betw_same_card)
  also have "\<dots> = entringer_number n n"
    using False by (simp add: entringer_number_def)
  also have "converse {(x, y). x < y} = {(x::nat, y). x > y}"
    by auto
  also have "card (alternating_permutations_of_set {(x, y). x > y} ({0..n}-{n})) = zigzag_number n"
    by (subst card_alternating_permutations_of_set) auto
  finally show ?thesis ..
qed auto

lemma card_rev_alternating_permutations_of_set_with_hd:
  assumes x: "x \<le> n"
  shows "card (alternating_permutations_of_set_with_hd {(x::nat,y). x > y} {0..n} x) =
           entringer_number n (n - x)"
proof -
  have "card (alternating_permutations_of_set_with_hd {(x::nat,y). x > y} {0..n} x) =
        entringer_number n (card {y \<in> {0..n} - {x}. x < y})"
    by (subst card_alternating_permutations_of_set_with_hd) (use assms in auto)
  also have "{y \<in> {0..n} - {x}. x < y} = {x<..n}"
    using x by auto
  finally show ?thesis
    by simp
qed

text \<open>
  The following summation identity can be visualised as follows: if we have an alternating
  permutation of the elements $0, \ldots, n$ that starts with $k$ then the next element
  after $k$ must be a reverse-alternating permutation starting with one of the elements
  $0, \ldots, k-1$, and this is again a bijection.
\<close>
theorem sum_entringer_numbers:
  assumes k: "k \<le> Suc n"
  shows   "(\<Sum>i<k. entringer_number n (n - i)) = entringer_number (Suc n) k"
proof -
  define A where "A = (\<lambda>X x. alternating_permutations_of_set_with_hd {(x::nat,y). x < y} X x)"
  define A' where "A' = (\<lambda>X x. alternating_permutations_of_set_with_hd {(x::nat,y). x > y} X x)"
  have converses: "converse {(x::nat,y). x < y} = {(x::nat,y). x > y}" 
                  "converse {(x::nat,y). x > y} = {(x::nat,y). x < y}"
    by auto

  have "bij_betw ((#) k)
         (\<Union> (alternating_permutations_of_set_with_hd ({(x, y). x < y}\<inverse>) ({0..Suc n} - {k}) ` {y \<in> {0..Suc n} - {k}. (y, k) \<in> {(x, y). x < y}}))
         (alternating_permutations_of_set_with_hd {(x, y). x < y} {0..Suc n} k)"
    by (intro alternating_permutations_of_set_with_hd_split_first) (use k in auto)
  also have "{y \<in> {0..Suc n} - {k}. (y, k) \<in> {(x, y). x < y}} = {0..<k}"
    using k by auto
  finally have "bij_betw ((#) k) (\<Union>i<k. A' ({0..Suc n} - {k}) i) (A {0..Suc n} k)"
    using converses by (simp add: A_def A'_def case_prod_unfold atLeast0LessThan)
  hence "card (\<Union>i<k. A' ({0..Suc n} - {k}) i) = card (A {0..Suc n} k)"
    by (rule bij_betw_same_card)
  also have "card (A {0..Suc n} k) = entringer_number (Suc n) k"
    by (simp add: entringer_number_def A_def)
  also have "card (\<Union>i<k. A' ({0..Suc n} - {k}) i) = (\<Sum>i<k. card (A' ({0..Suc n} - {k}) i))"
    by (subst card_UN_disjoint)
       (auto simp: A'_def alternating_permutations_of_set_with_hd_def alternating_permutations_of_set_def)
  also have "\<dots> = (\<Sum>i<k. entringer_number n (n - i))"
  proof (intro sum.cong)
    fix i assume i: "i \<in> {..<k}"
    have "card (A' ({0..Suc n} - {k}) i) =
          entringer_number n (card {j \<in> {0..Suc n} - {k} - {i}. i < j})"
      unfolding A'_def using i k
      by (subst card_alternating_permutations_of_set_with_hd) auto
    also have "{j \<in> {0..Suc n} - {k} - {i}. i < j} = {i<..Suc n} - {k}"
      using i k by auto
    also have "card \<dots> = n - i"
      using i k by (subst card_Diff_subset) auto
    finally show "card (A' ({0..Suc n} - {k}) i) = entringer_number n (n - i)" .
  qed auto
  finally show ?thesis .
qed

lemma sum_entringer_numbers':
  assumes k: "k \<le> n"
  shows   "(\<Sum>i\<le>k. entringer_number n (n - i)) = entringer_number (Suc n) (Suc k)"
proof -
  have "(\<Sum>i<Suc k. entringer_number n (n - i)) = entringer_number (Suc n) (Suc k)"
    by (rule sum_entringer_numbers) (use k in auto)
  also have "{..<Suc k} = {..k}"
    by auto
  finally show ?thesis .
qed

text \<open>
  A consequence of this summation identity is that the sum of all the values in the $n$-th row
  of the Entringer triangle is exactly the $n$-th zigzag number.
\<close>
corollary sum_entringer_numbers_row: "(\<Sum>k\<le>n. entringer_number n k) = zigzag_number (Suc n)"
proof -
  have "(\<Sum>k\<le>n. entringer_number n (n - k)) = zigzag_number (Suc n)"
    using sum_entringer_numbers'[OF order.refl, of n] by simp
  also have "(\<Sum>k\<le>n. entringer_number n (n - k)) = (\<Sum>k\<le>n. entringer_number n k)"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>k. n - k" "\<lambda>k. n - k"]) auto
  finally show ?thesis
    by simp
qed

text \<open>
  By telescoping the summation identity, we also obtain the following simple recurrence
  for the Entringer numbers:
\<close>
corollary entringer_number_rec:
  assumes "k \<le> n"
  shows   "entringer_number (Suc n) (Suc k) =
             entringer_number (Suc n) k + entringer_number n (n - k)"
proof -
  have "entringer_number (Suc n) (Suc k) = (\<Sum>i\<le>k. entringer_number n (n - i))"
    by (rule sum_entringer_numbers' [symmetric]) (use assms in auto)
  also have "{..k} = insert k {..<k}"
    by auto
  also have "(\<Sum>i\<in>\<dots>. entringer_number n (n - i)) =
             (\<Sum>i<k. entringer_number n (n - i)) + entringer_number n (n - k)"
    by (subst sum.insert) auto
  also have "(\<Sum>i<k. entringer_number n (n - i)) = entringer_number (Suc n) k"
    by (rule sum_entringer_numbers) (use assms in auto)
  finally show ?thesis .
qed

text \<open>
  This recurrence can be used to compute the Entringer numbers (although if one wants
  this to be efficient one has to be a bit smarter about avoiding double computations;
  either by memoisation or by finding a smarter way to traverse the triangle).
\<close>
lemma entringer_number_code [code]:
  "entringer_number n k =
     (if n = 0 then if k = 0 then 1 else 0
      else if k = 0 \<or> k > n then 0
      else entringer_number n (k - 1) + entringer_number (n - 1) (n - k))"
  using entringer_number_rec[of "k - 1" "n - 1"] by (cases n; cases k) auto

end
