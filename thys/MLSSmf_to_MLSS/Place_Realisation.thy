theory Place_Realisation
  imports Place_Framework MLSS_Decision_Proc.MLSS_Realisation Proper_Venn_Regions
begin

lemma u_exists:
  assumes "finite (S :: 'a set)"
    shows "\<exists>(u :: 'a \<Rightarrow> hf). (\<forall>x \<in> S. \<forall>y \<in> S. x \<noteq> y \<longrightarrow> u x \<noteq> u y) \<and> (\<forall>x \<in> S. hcard (u x) \<ge> n)"
proof -
  from \<open>finite S\<close> have "\<exists>f. inj_on f S \<and> f ` S = {0 ..< card S}"
  proof (induction S)
    case empty
    then show ?case by simp
  next
    case (insert x S)
    from insert.IH obtain f where "inj_on f S" "f ` S = {0 ..< card S}" by blast
    then have range_f_on_S: "y \<in> S \<Longrightarrow> f y < card S" for y
      by fastforce
    let ?f = "(\<lambda>x. if x \<in> S then f x else card S)"
    have "?f y \<noteq> ?f z" if "y \<in> insert x S" "z \<in> insert x S" "y \<noteq> z" for y z
    proof -
      from that consider "y \<in> S \<and> z \<in> S" | "y \<in> S \<and> z = x" | "y = x \<and> z \<in> S" | "y = x \<and> z = x"
        by fast
      then show ?thesis
      proof (cases)
        case 1
        then have "?f y = f y" "?f z = f z" by simp+
        moreover
        from \<open>inj_on f S\<close> \<open>y \<noteq> z\<close> 1 have "f y \<noteq> f z"
          by (simp add: inj_on_contraD)
        ultimately
        show ?thesis by presburger
      next
        case 2
        then have "?f y = f y" by simp
        with range_f_on_S have "?f y < card S"
          using 2 by presburger
        moreover
        from 2 \<open>x \<notin> S\<close> have "?f z = card S" by argo
        ultimately
        show ?thesis by force
      next
        case 3
        then have "?f z = f z" by simp
        with range_f_on_S have "?f z < card S"
          using 3 by presburger
        moreover
        from 3 \<open>x \<notin> S\<close> have "?f y = card S" by argo
        ultimately
        show ?thesis by force
      next
        case 4
        with \<open>y \<noteq> z\<close> have False by blast
        then show ?thesis by blast
      qed
    qed
    then have "inj_on ?f (insert x S)"
      using inj_on_def by blast
    moreover
    have "?f ` (insert x S) = {0 ..< card (insert x S)}"
    proof (standard; standard)
      fix c assume "c \<in> ?f ` (insert x S)"
      then obtain y where "y \<in> insert x S" "c = ?f y" by blast
      then have "c < Suc (card S)"
        apply (cases "y \<in> S")
        using range_f_on_S
         apply fastforce
        by auto
      also have "... = card (insert x S)"
        using \<open>x \<notin> S\<close> \<open>finite S\<close> by simp
      finally show "c \<in> {0 ..< card (insert x S)}" by simp
    next
      fix c assume "c \<in> {0 ..< card (insert x S)}"
      then have "c \<le> card S"
        using \<open>x \<notin> S\<close> \<open>finite S\<close> by auto

      have "\<exists>y \<in> S. ?f y = c" if "c < card S"
      proof -
        from that have "c \<in> {0 ..< card S}" by simp
        with \<open>f ` S = {0 ..< card S}\<close>
        obtain y where "y \<in> S" "f y = c"
          using image_iff[where ?z = c and ?f = f and ?A = S]
          by blast
        moreover
        from \<open>y \<in> S\<close> have "f y = ?f y" by auto
        ultimately
        show ?thesis by auto
      qed
      then have "c < card S \<Longrightarrow> \<exists>y \<in> insert x S. ?f y = c" by blast
      moreover
      from \<open>x \<notin> S\<close> have "?f x = card S" by argo
      then have "c = card S \<Longrightarrow> \<exists>y \<in> insert x S. ?f y = c" by blast
      ultimately
      show "c \<in> ?f ` (insert x S)"
        using \<open>c \<le> card S\<close> by fastforce
    qed
    ultimately
    show ?case by blast
  qed
  then obtain f' where "inj_on f' S" "f' ` S = {0 ..< card S}" by blast
  let ?f = "\<lambda>x. f' x + n"
  from \<open>inj_on f' S\<close> have f_inj: "?f x \<noteq> ?f y" if "x \<in> S" "y \<in> S" "x \<noteq> y" for x y
    by (simp add: inj_on_eq_iff that)
  from \<open>f' ` S = {0 ..< card S}\<close> have f_ge_n: "?f x \<notin> {0 ..< n}" if "x \<in> S" for x
    using that by auto

  let ?u = "\<lambda>x. HF (Abs_hf ` {0 ..< n}) \<triangleleft> Abs_hf (?f x)"
  have "?u x \<noteq> ?u y" if "x \<in> S" "y \<in> S" "x \<noteq> y" for x y
  proof -
    from f_inj that have "?f x \<noteq> ?f y" by blast
    then have "Abs_hf (?f x) \<noteq> Abs_hf (?f y)"
      by (simp add: Abs_hf_inject)
    moreover
    from f_ge_n \<open>x \<in> S\<close> have "Abs_hf (?f x) \<notin> Abs_hf ` {0 ..< n}"
      using Abs_hf_inject by fastforce
    then have "Abs_hf (?f x) \<^bold>\<notin> HF (Abs_hf ` {0 ..< n})" by simp
    moreover
    from f_ge_n \<open>y \<in> S\<close> have "Abs_hf (?f y) \<notin> Abs_hf ` {0 ..< n}"
      using Abs_hf_inject by fastforce
    then have "Abs_hf (?f y) \<^bold>\<notin> HF (Abs_hf ` {0 ..< n})" by simp
    ultimately
    show "?u x \<noteq> ?u y"
      by (metis hmem_hinsert)
  qed
  then have "\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> ?u x \<noteq> ?u y" by blast
  moreover
  have "hcard (?u x) \<ge> n" if "x \<in> S" for x
  proof -
    from f_ge_n \<open>x \<in> S\<close> have "Abs_hf (?f x) \<notin> Abs_hf ` {0 ..< n}"
      using Abs_hf_inject by fastforce
    then have "Abs_hf (?f x) \<^bold>\<notin> HF (Abs_hf ` {0 ..< n})" by simp
    then have "hcard (?u x) = Suc (hcard (HF (Abs_hf ` {0..<n})))"
      by (simp add: hcard_hinsert_if)
    also have "... = Suc (card (Abs_hf ` {0 ..< n}))"
      using hcard_def by auto
    also have "... = Suc (card {0 ..< n})"
      using Abs_hf_inject card_image injD inj_on_def by metis
    also have "... = Suc n" by auto
    finally show "hcard (?u x) \<ge> n" by auto
  qed
  ultimately
  show ?thesis by meson
qed

locale place_realization =
  adequate_place_framework \<C> PI at\<^sub>p for \<C> PI at\<^sub>p +
    fixes u :: "('a \<Rightarrow> bool) \<Rightarrow> hf"
  assumes u_distinct: "\<lbrakk>\<pi>\<^sub>1 \<in> PI - Range at\<^sub>p; \<pi>\<^sub>2 \<in> PI - Range at\<^sub>p; \<pi>\<^sub>1 \<noteq> \<pi>\<^sub>2\<rbrakk> \<Longrightarrow> u \<pi>\<^sub>1 \<noteq> u \<pi>\<^sub>2"
      and hcard_u_not_in_range_at\<^sub>p: "\<pi> \<in> PI - Range at\<^sub>p \<Longrightarrow> hcard (u \<pi>) \<ge> card PI"
begin

definition "G_PI \<equiv> place_mem_graph \<C> PI"
declare G_PI_def [simp]

definition "membership \<equiv> place_membership \<C> PI"
declare membership_def [simp]

lemma arcs_G_PI: "arcs G_PI = membership" by simp
lemma arcs_ends_G_PI: "arcs_ends G_PI = membership"
  unfolding arcs_ends_def arc_to_ends_def by auto
lemma verts_G_PI: "verts G_PI = PI" by simp

lemma u_distinct':
  "\<lbrakk>\<pi>\<^sub>1 \<in> PI - Range at\<^sub>p; \<pi>\<^sub>2 \<in> PI - Range at\<^sub>p; \<pi>\<^sub>1 \<noteq> \<pi>\<^sub>2\<rbrakk> \<Longrightarrow> u \<pi>\<^sub>1 \<noteq> u \<pi>\<^sub>2"
  using u_distinct by simp

interpretation realisation G_PI "PI - Range at\<^sub>p" "Range at\<^sub>p" u "{(\<pi>, \<pi>) |\<pi>. \<pi> \<in> PI}"
proof -
  have "(PI - Range at\<^sub>p) \<inter> Range at\<^sub>p = {}"
    by (simp add: inf_commute)
  moreover
  have "verts G_PI = (PI - Range at\<^sub>p) \<union> Range at\<^sub>p"
    using range_at\<^sub>p by auto 
  moreover
  have "\<not> t \<rightarrow>\<^bsub>G_PI\<^esub> p" if "p \<in> PI - Range at\<^sub>p" for p t
  proof -
    have "(t, p) \<notin> membership"
    proof (rule ccontr)
      assume "\<not> (t, p) \<notin> membership"
      then have "(t, p) \<in> membership" by blast
      then have t: "t \<in> PI" and p: "p \<in> PI" and "\<exists>x y. AT (Var x =\<^sub>s Single (Var y)) \<in> \<C> \<and> t y \<and> p x"
        by auto
      then obtain x y where xy: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>" "t y" "p x" by blast
      with C5_1 range_at\<^sub>p single_valued_at\<^sub>p obtain \<pi>
        where C5_1_1: "\<pi> \<in> PI" "(y, \<pi>) \<in> at\<^sub>p" "\<pi> x"
          and C5_1_2: "\<pi>' \<in> PI \<and> \<pi>' x \<Longrightarrow> \<pi>' = \<pi>" for \<pi>'
        by blast
      show False
      proof (cases "(y, p) \<in> at\<^sub>p")
        case True
        from xy have "y \<in> W" by fastforce
        with \<open>p \<in> PI - Range at\<^sub>p\<close> \<open>(y, p) \<in> at\<^sub>p\<close> show ?thesis by blast
      next
        case False
        with C5_1_2 xy p show ?thesis
          using C5_1 by fast
      qed
    qed
    moreover
    have "arcs_ends G_PI = membership"
      unfolding arcs_ends_def arc_to_ends_def by simp
    ultimately
    show ?thesis by blast
  qed
  moreover
  from C6 have "dag G_PI" by auto
  ultimately
  show "realisation G_PI (PI - Range at\<^sub>p) (Range at\<^sub>p)"
    unfolding realisation_def
    by (meson realisation_axioms.intro)
qed

function place_realise :: "('a \<Rightarrow> bool) \<Rightarrow> hf" where
  "\<pi> \<in> PI - Range at\<^sub>p \<Longrightarrow> place_realise \<pi> = HF {u \<pi>}"
| "\<pi> \<in> Range at\<^sub>p \<Longrightarrow> place_realise \<pi> = HF {\<Squnion>HF (place_realise ` parents G_PI \<pi>)}"
| "\<pi> \<notin> PI \<Longrightarrow> place_realise \<pi> = 0"
  using B_T_partition_verts range_at\<^sub>p by blast+
termination
  apply (relation "measure (\<lambda>t. card (ancestors G_PI t))")
   apply (simp_all add: card_ancestors_strict_mono del: G_PI_def)
  done

lemma place_realise_singleton:
  assumes "\<pi> \<in> PI"
    shows "hcard (place_realise \<pi>) = 1"
  using assms
proof (cases \<pi> rule: place_realise.cases)
  case (1 \<pi>)
  have "finite {u \<pi>}" by blast
  then have "hcard (HF {u \<pi>}) = 1"
    using hcard_def by auto
  with 1 show ?thesis by simp
next
  case (2 \<pi>)
  then have "hcard (HF {\<Squnion>HF (place_realise ` parents G_PI \<pi>)}) = 1"
    using hcard_def by auto
  with 2 show ?thesis by simp
next
  case (3 \<pi>)
  with assms show ?thesis by fast
qed

lemma place_realise_nonempty:
  assumes "\<pi> \<in> PI"
    shows "place_realise \<pi> \<noteq> 0"
  using assms place_realise_singleton hcard_1E by fastforce

lemma place_realise_elem_hcard_in_range_at\<^sub>p:
  assumes "\<pi> \<in> Range at\<^sub>p"
    shows "\<exists>a. place_realise \<pi> = HF {a} \<and> hcard a < card PI"
proof -
  from assms obtain a where a: "a = \<Squnion>HF (place_realise ` parents G_PI \<pi>)" "place_realise \<pi> = HF {a}"
    by simp

  from assms have "\<pi> \<in> PI"
    by (metis B_T_partition_verts(2) UnCI verts_G_PI) 
  moreover
  have "\<pi> \<notin> parents G_PI \<pi>"
    using membership_irreflexive by fastforce
  moreover
  have "parents G_PI \<pi> \<subseteq> PI" by auto
  ultimately
  have "parents G_PI \<pi> \<subset> PI"
    by blast
  then have "card (parents G_PI \<pi>) < card PI"
    using finite_PI by (simp add: psubset_card_mono)
  moreover
  from hcard_Hunion_singletons[where ?s = "parents G_PI \<pi>" and ?f = place_realise]
  have "hcard (\<Squnion>HF (place_realise ` parents G_PI \<pi>)) \<le> card (parents G_PI \<pi>)"
    using place_realise_singleton \<open>parents G_PI \<pi> \<subseteq> PI\<close> by blast
  ultimately
  have "hcard (\<Squnion>HF (place_realise ` parents G_PI \<pi>)) < card PI"
    by linarith
  with a show ?thesis by blast
qed

lemma place_realise_elem_hcard_not_in_range_at\<^sub>p:
  assumes "\<pi> \<in> PI - Range at\<^sub>p"
    shows "\<exists>a. place_realise \<pi> = HF {a} \<and> hcard a \<ge> card PI"
  using assms hcard_u_not_in_range_at\<^sub>p by auto

lemma place_in_range_at_eq_if_parents_eq:
  assumes "\<pi>\<^sub>1 \<in> Range at\<^sub>p"
      and "\<pi>\<^sub>2 \<in> Range at\<^sub>p"
      and parents_eq: "parents G_PI \<pi>\<^sub>1 = parents G_PI \<pi>\<^sub>2"
    shows "\<pi>\<^sub>1 = \<pi>\<^sub>2"
proof (cases "parents G_PI \<pi>\<^sub>1 = {}")
  case True
  then have "\<pi>\<^sub>1 \<notin> Range membership" using arcs_ends_G_PI by force
  with \<open>\<pi>\<^sub>1 \<in> Range at\<^sub>p\<close> have "\<pi>\<^sub>1 \<in> Range at\<^sub>p - Range (place_membership \<C> PI)"
    by fastforce
  moreover
  from True parents_eq have "parents G_PI \<pi>\<^sub>2 = {}" by argo
  then have "\<pi>\<^sub>2 \<notin> Range membership" using arcs_ends_G_PI by force
  with \<open>\<pi>\<^sub>2 \<in> Range at\<^sub>p\<close> have "\<pi>\<^sub>2 \<in> Range at\<^sub>p - Range (place_membership \<C> PI)"
    by fastforce
  ultimately
  show ?thesis using C7 by blast
next
  case False  
  from assms range_at\<^sub>p have "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" by blast+

  from \<open>\<pi>\<^sub>1 \<in> Range at\<^sub>p\<close> obtain y\<^sub>1 where "(y\<^sub>1, \<pi>\<^sub>1) \<in> at\<^sub>p" by blast
  then have "y\<^sub>1 \<in> W" using dom_at\<^sub>p by blast
  then obtain x\<^sub>1 where "AT (Var x\<^sub>1 =\<^sub>s Single (Var y\<^sub>1)) \<in> \<C>"
    using memW_E by blast
  with C5_1 \<open>(y\<^sub>1, \<pi>\<^sub>1) \<in> at\<^sub>p\<close> have "\<pi>\<^sub>1 x\<^sub>1"
    by (metis single_valuedD single_valued_at\<^sub>p)

  from \<open>\<pi>\<^sub>2 \<in> Range at\<^sub>p\<close> obtain y\<^sub>2 where "(y\<^sub>2, \<pi>\<^sub>2) \<in> at\<^sub>p" by blast
  then have "y\<^sub>2 \<in> W" using dom_at\<^sub>p by blast
  then obtain x\<^sub>2 where "AT (Var x\<^sub>2 =\<^sub>s Single (Var y\<^sub>2)) \<in> \<C>"
    using memW_E by blast
  with C5_1 \<open>(y\<^sub>2, \<pi>\<^sub>2) \<in> at\<^sub>p\<close> have "\<pi>\<^sub>2 x\<^sub>2"
    by (metis single_valuedD single_valued_at\<^sub>p)

  have "\<pi> y\<^sub>1 \<longleftrightarrow> \<pi> y\<^sub>2" if "\<pi> \<in> PI" for \<pi>
  proof
    assume "\<pi> y\<^sub>1"
    with \<open>AT (Var x\<^sub>1 =\<^sub>s Single (Var y\<^sub>1)) \<in> \<C>\<close> \<open>\<pi>\<^sub>1 x\<^sub>1\<close> \<open>\<pi> \<in> PI\<close> \<open>\<pi>\<^sub>1 \<in> PI\<close>
    have "(\<pi>, \<pi>\<^sub>1) \<in> membership" by auto
    with parents_eq have "(\<pi>, \<pi>\<^sub>2) \<in> membership"
      using arcs_ends_G_PI by blast
    then obtain x\<^sub>2' y\<^sub>2' where "AT (Var x\<^sub>2' =\<^sub>s Single (Var y\<^sub>2')) \<in> \<C>" "\<pi> y\<^sub>2'" "\<pi>\<^sub>2 x\<^sub>2'"
      by auto
    with C5_1 have "(y\<^sub>2', \<pi>\<^sub>2) \<in> at\<^sub>p"
      using \<open>\<pi>\<^sub>2 \<in> PI\<close> by fastforce
    from \<open>AT (Var x\<^sub>2' =\<^sub>s Single (Var y\<^sub>2')) \<in> \<C>\<close> have "y\<^sub>2' \<in> W" by force
    from C5_2 \<open>(y\<^sub>2, \<pi>\<^sub>2) \<in> at\<^sub>p\<close> \<open>(y\<^sub>2', \<pi>\<^sub>2) \<in> at\<^sub>p\<close>
    have "\<forall>\<pi> \<in> PI. \<pi> y\<^sub>2' = \<pi> y\<^sub>2"
      using \<open>y\<^sub>2 \<in> W\<close> \<open>y\<^sub>2' \<in> W\<close> by fast
    with \<open>\<pi> y\<^sub>2'\<close> show "\<pi> y\<^sub>2"
      using \<open>\<pi> \<in> PI\<close> by fast
  next
    assume "\<pi> y\<^sub>2"
    with \<open>AT (Var x\<^sub>2 =\<^sub>s Single (Var y\<^sub>2)) \<in> \<C>\<close> \<open>\<pi>\<^sub>2 x\<^sub>2\<close> \<open>\<pi> \<in> PI\<close> \<open>\<pi>\<^sub>2 \<in> PI\<close>
    have "(\<pi>, \<pi>\<^sub>2) \<in> membership" by auto
    with parents_eq have "(\<pi>, \<pi>\<^sub>1) \<in> membership"
      using arcs_ends_G_PI by blast
    then obtain x\<^sub>1' y\<^sub>1' where "AT (Var x\<^sub>1' =\<^sub>s Single (Var y\<^sub>1')) \<in> \<C>" "\<pi> y\<^sub>1'" "\<pi>\<^sub>1 x\<^sub>1'"
      by auto
    with C5_1 have "(y\<^sub>1', \<pi>\<^sub>1) \<in> at\<^sub>p"
      using \<open>\<pi>\<^sub>1 \<in> PI\<close> by fastforce
    from \<open>AT (Var x\<^sub>1' =\<^sub>s Single (Var y\<^sub>1')) \<in> \<C>\<close> have "y\<^sub>1' \<in> W" by force
    from C5_2 \<open>(y\<^sub>1, \<pi>\<^sub>1) \<in> at\<^sub>p\<close> \<open>(y\<^sub>1', \<pi>\<^sub>1) \<in> at\<^sub>p\<close>
    have "\<forall>\<pi> \<in> PI. \<pi> y\<^sub>1' = \<pi> y\<^sub>1"
      using \<open>y\<^sub>1 \<in> W\<close> \<open>y\<^sub>1' \<in> W\<close> by fast
    with \<open>\<pi> y\<^sub>1'\<close> show "\<pi> y\<^sub>1"
      using \<open>\<pi> \<in> PI\<close> by fast
  qed
  with C5_3 show ?thesis
    using \<open>y\<^sub>1 \<in> W\<close> \<open>y\<^sub>2 \<in> W\<close> \<open>(y\<^sub>1, \<pi>\<^sub>1) \<in> at\<^sub>p\<close> \<open>(y\<^sub>2, \<pi>\<^sub>2) \<in> at\<^sub>p\<close>
    by (metis single_valued_at\<^sub>p single_valued_def)
qed

lemma place_realise_pairwise_disjoint:
  assumes "\<pi>\<^sub>1 \<in> PI"
      and "\<pi>\<^sub>2 \<in> PI"
      and "\<pi>\<^sub>1 \<noteq> \<pi>\<^sub>2"
    shows "place_realise \<pi>\<^sub>1 \<sqinter> place_realise \<pi>\<^sub>2 = 0"
  using assms
proof (induction \<pi>\<^sub>1 arbitrary: \<pi>\<^sub>2 rule: place_realise.induct)
  case (1 \<pi>)
  then show ?case
  proof (cases "\<pi>\<^sub>2 \<in> Range at\<^sub>p")
    case True
      from \<open>\<pi>\<^sub>2 \<in> Range at\<^sub>p\<close> place_realise_elem_hcard_in_range_at\<^sub>p
      obtain a where \<pi>\<^sub>2_a: "place_realise \<pi>\<^sub>2 = HF {a}" and hcard_a: "hcard a < card PI"
        by blast      
      from \<open>\<pi> \<in> PI - Range at\<^sub>p\<close> hcard_u_not_in_range_at\<^sub>p
      obtain b where \<pi>_b: "place_realise \<pi> = HF {b}" and hcard_b: "card PI \<le> hcard b"
        by auto

      from hcard_a hcard_b have "hcard a \<noteq> hcard b" by linarith
      then have "HF {a} \<sqinter> HF {b} = 0" by fastforce
      with \<pi>\<^sub>2_a \<pi>_b show ?thesis by auto
  next
    case False
    with \<open>\<pi>\<^sub>2 \<in> PI\<close> have "\<pi>\<^sub>2 \<in> PI - Range at\<^sub>p" by blast
    with 1 u_distinct' \<open>\<pi> \<noteq> \<pi>\<^sub>2\<close> have "u \<pi> \<noteq> u \<pi>\<^sub>2" by presburger
    then have "HF {u \<pi>} \<sqinter> HF {u \<pi>\<^sub>2} = 0" by simp
    with \<open>\<pi> \<in> PI - Range at\<^sub>p\<close> \<open>\<pi>\<^sub>2 \<in> PI - Range at\<^sub>p\<close> show ?thesis
      by simp
  qed
next
  case (2 \<pi>)
  then show ?case
  proof (cases "\<pi>\<^sub>2 \<in> Range at\<^sub>p")
    case True
    have parents_not_empty: "parents G_PI \<pi>' \<noteq> {} \<Longrightarrow> \<Squnion>HF (place_realise ` parents G_PI \<pi>') \<noteq> 0" for \<pi>'
    proof -
      assume "parents G_PI \<pi>' \<noteq> {}"
      then obtain \<pi>'' where "\<pi>'' \<in> parents G_PI \<pi>'" by blast
      moreover
      have "finite (parents G_PI \<pi>')" by blast
      ultimately
      have "place_realise \<pi>'' \<le> \<Squnion>HF (place_realise ` parents G_PI \<pi>')" by force
      moreover
      have "place_realise \<pi>'' \<noteq> 0"
        using place_realise_singleton \<open>\<pi>'' \<in> parents G_PI \<pi>'\<close>
        by fastforce
      ultimately
      show "\<Squnion>HF (place_realise ` parents G_PI \<pi>') \<noteq> 0" by force
    qed

    {assume "place_realise \<pi> \<sqinter> place_realise \<pi>\<^sub>2 \<noteq> 0"
      moreover
      from \<open>\<pi> \<in> Range at\<^sub>p\<close> have "place_realise \<pi> = HF {\<Squnion>HF (place_realise ` parents G_PI \<pi>)}" by auto
      moreover
      from \<open>\<pi>\<^sub>2 \<in> Range at\<^sub>p\<close> have "place_realise \<pi>\<^sub>2 = HF {\<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>2)}" by auto
      ultimately
      have Hunion_place_realise_parents_eq: "\<Squnion>HF (place_realise ` parents G_PI \<pi>) = \<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>2)" by simp
      
      have "parents G_PI \<pi> = parents G_PI \<pi>\<^sub>2"
      proof(standard; standard)
        fix \<pi>' assume "\<pi>' \<in> parents G_PI \<pi>"
        then have "\<pi>' \<in> PI" by auto
        with place_realise_singleton obtain c where "c \<^bold>\<in> place_realise \<pi>'"
          by (metis hcard_0 hempty_iff zero_neq_one)
        have "finite (parents G_PI \<pi>)" by blast
        with \<open>\<pi>' \<in> parents G_PI \<pi>\<close> have "place_realise \<pi>' \<le> \<Squnion>HF (place_realise ` parents G_PI \<pi>)"
          by force
        with \<open>c \<^bold>\<in> place_realise \<pi>'\<close> have "c \<^bold>\<in> \<Squnion>HF (place_realise ` parents G_PI \<pi>)"
          by (simp add: less_eq_hf_def)
        with Hunion_place_realise_parents_eq have "c \<^bold>\<in> \<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>2)"
          by argo
        then obtain \<pi>'' where "\<pi>'' \<in> parents G_PI \<pi>\<^sub>2" "c \<^bold>\<in> place_realise \<pi>''" by auto
        with \<open>c \<^bold>\<in> place_realise \<pi>'\<close> have "place_realise \<pi>' \<sqinter> place_realise \<pi>'' \<noteq> 0" by blast
        with "2.IH" have "\<pi>' = \<pi>''"
          using \<open>\<pi>' \<in> parents G_PI \<pi>\<close> \<open>\<pi>'' \<in> parents G_PI \<pi>\<^sub>2\<close> \<open>\<pi>' \<in> PI\<close> by force
        with \<open>\<pi>'' \<in> parents G_PI \<pi>\<^sub>2\<close> show "\<pi>' \<in> parents G_PI \<pi>\<^sub>2" by blast
      next
        fix \<pi>'' assume "\<pi>'' \<in> parents G_PI \<pi>\<^sub>2"
        then have "\<pi>'' \<in> PI" by auto
        with place_realise_singleton obtain c where "c \<^bold>\<in> place_realise \<pi>''"
          by (metis hcard_0 hempty_iff zero_neq_one)
        have "finite (parents G_PI \<pi>\<^sub>2)" by blast
        with \<open>\<pi>'' \<in> parents G_PI \<pi>\<^sub>2\<close> have "place_realise \<pi>'' \<le> \<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>2)"
          by force
        with \<open>c \<^bold>\<in> place_realise \<pi>''\<close> have "c \<^bold>\<in> \<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>2)"
          by (simp add: less_eq_hf_def)
        with Hunion_place_realise_parents_eq have "c \<^bold>\<in> \<Squnion>HF (place_realise ` parents G_PI \<pi>)"
          by argo
        then obtain \<pi>' where "\<pi>' \<in> parents G_PI \<pi>" "c \<^bold>\<in> place_realise \<pi>'" by auto
        with \<open>c \<^bold>\<in> place_realise \<pi>''\<close> have "place_realise \<pi>' \<sqinter> place_realise \<pi>'' \<noteq> 0" by blast
        with "2.IH" have "\<pi>' = \<pi>''"
          using \<open>\<pi>' \<in> parents G_PI \<pi>\<close> \<open>\<pi>'' \<in> parents G_PI \<pi>\<^sub>2\<close> \<open>\<pi>'' \<in> PI\<close> \<open>c \<^bold>\<in> place_realise \<pi>'\<close>
          by (metis hmem_hempty place_realise.simps(3))
        with \<open>\<pi>' \<in> parents G_PI \<pi>\<close> show "\<pi>'' \<in> parents G_PI \<pi>" by blast
      qed
    }
    with place_in_range_at_eq_if_parents_eq show ?thesis
      using 2 True by blast
    next
    case False
    with \<open>\<pi>\<^sub>2 \<in> PI\<close> have "\<pi>\<^sub>2 \<in> PI - Range at\<^sub>p" by blast

    from \<open>\<pi> \<in> Range at\<^sub>p\<close> place_realise_elem_hcard_in_range_at\<^sub>p
    obtain a where \<pi>_a: "place_realise \<pi> = HF {a}" and hcard_a: "hcard a < card PI"
      by blast
    from \<open>\<pi>\<^sub>2 \<in> PI - Range at\<^sub>p\<close> hcard_u_not_in_range_at\<^sub>p
    obtain b where \<pi>\<^sub>2_b: "place_realise \<pi>\<^sub>2 = HF {b}" and hcard_b: "card PI \<le> hcard b"
      by auto

    from hcard_a hcard_b have "hcard a \<noteq> hcard b" by linarith
    then have "HF {a} \<sqinter> HF {b} = 0" by fastforce
    with \<pi>_a \<pi>\<^sub>2_b show ?thesis by argo
  qed
next
  case (3 \<pi>)
  then show ?case by blast
qed

\<comment>\<open>Canonical assignments\<close>
fun \<M> :: "'a \<Rightarrow> hf" where
  "\<M> x = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> x})"

lemma var_empty_if_no_place_included_in_PI:
  assumes "\<forall>\<pi> \<in> PI. \<not> \<pi> x"
    shows "\<M> x = 0"
  using assms by fastforce

lemma HUnion_place_realise_eq_iff_place_composition_same:
  assumes "S \<subseteq> PI"
      and "T \<subseteq> PI"
    shows "\<Squnion>HF (place_realise ` S) = \<Squnion>HF (place_realise ` T) \<longleftrightarrow> S = T"
proof
  assume HUnion_eq: "\<Squnion>HF (place_realise ` S) = \<Squnion>HF (place_realise ` T)"
  from assms finite_PI have "finite S" "finite T"
    by (simp add: finite_subset)+
  show "S = T"
  proof (standard; standard)
    fix \<pi> assume "\<pi> \<in> S"
    with place_realise_nonempty obtain c where "c \<^bold>\<in> place_realise \<pi>"
      using \<open>S \<subseteq> PI\<close> by blast
    with \<open>\<pi> \<in> S\<close> have "c \<^bold>\<in> \<Squnion>HF (place_realise ` S)"
      using \<open>finite S\<close> by auto
    with HUnion_eq have "c \<^bold>\<in> \<Squnion>HF (place_realise ` T)" by argo
    then obtain \<pi>' where "\<pi>' \<in> T" "c \<^bold>\<in> place_realise \<pi>'"
      by auto
    with \<open>c \<^bold>\<in> place_realise \<pi>\<close> place_realise_pairwise_disjoint place_realise_nonempty
    have "\<pi> = \<pi>'"
      using \<open>\<pi> \<in> S\<close> assms by blast
    with \<open>\<pi>' \<in> T\<close> show "\<pi> \<in> T"
      by argo
  next
    fix \<pi> assume "\<pi> \<in> T"
    with place_realise_nonempty obtain c where "c \<^bold>\<in> place_realise \<pi>"
      using \<open>T \<subseteq> PI\<close> by blast
    with \<open>\<pi> \<in> T\<close> have "c \<^bold>\<in> \<Squnion>HF (place_realise ` T)"
      using \<open>finite T\<close> by auto
    with HUnion_eq have "c \<^bold>\<in> \<Squnion>HF (place_realise ` S)" by argo
    then obtain \<pi>' where "\<pi>' \<in> S" "c \<^bold>\<in> place_realise \<pi>'"
      by auto
    with \<open>c \<^bold>\<in> place_realise \<pi>\<close> place_realise_pairwise_disjoint place_realise_nonempty
    have "\<pi> = \<pi>'"
      using \<open>\<pi> \<in> T\<close> assms by blast
    with \<open>\<pi>' \<in> S\<close> show "\<pi> \<in> S"
      by argo
  qed
next
  assume "S = T"
  then show "\<Squnion>HF (place_realise ` S) = \<Squnion>HF (place_realise ` T)" by auto
qed

text \<open>Lemma 29: canonical assignment is satisfying\<close>
theorem \<M>_sat_\<C>: "\<forall>lt \<in> \<C>. interp I\<^sub>s\<^sub>a \<M> lt"
proof
  fix lt assume "lt \<in> \<C>"
  with norm_\<C> have "normalized_MLSS_literal lt" by blast
  then show "interp I\<^sub>s\<^sub>a \<M> lt"
  proof (cases lt)
    case (eq_empty x n)
      with C1_1 have "{\<pi> \<in> PI. \<pi> x} = {}"
        using \<open>lt \<in> \<C>\<close> by auto
      with HUnion_place_realise_eq_iff_place_composition_same
      have "\<M> x = 0" by fastforce
      with \<open>lt = AT (Var x =\<^sub>s \<emptyset> n)\<close> show ?thesis by auto
    next
    case (eq x y)
    with C1_2 have "{\<pi> \<in> PI. \<pi> x} = {\<pi> \<in> PI. \<pi> y}"
      using \<open>lt \<in> \<C>\<close> by auto
    with HUnion_place_realise_eq_iff_place_composition_same
    have "\<M> x = \<M> y" by simp
    with \<open>lt = AT (Var x =\<^sub>s Var y)\<close> show ?thesis by auto
  next
    case (neq x y)
    with C4 have "{\<pi> \<in> PI. \<pi> x} \<noteq> {\<pi> \<in> PI. \<pi> y}"
      using \<open>lt \<in> \<C>\<close> by auto
    with HUnion_place_realise_eq_iff_place_composition_same
    have "\<M> x \<noteq> \<M> y" by simp
    with \<open>lt = AF (Var x =\<^sub>s Var y)\<close> show ?thesis by auto
  next
    case (union x y z)
    with C2 have "{\<pi> \<in> PI. \<pi> x} = {\<pi> \<in> PI. \<pi> y} \<union> {\<pi> \<in> PI. \<pi> z}"
      using \<open>lt \<in> \<C>\<close> by auto
    with HUnion_place_realise_eq_iff_place_composition_same
    have "\<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> x}) =
          \<Squnion>HF (place_realise ` ({\<pi> \<in> PI. \<pi> y} \<union> {\<pi> \<in> PI. \<pi> z}))"
      by argo
    also have "... = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> y}) \<squnion> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> z})"
      using finite_PI by (simp add: image_Un union_hunion)
    finally have "\<M> x = \<M> y \<squnion> \<M> z" by fastforce
    with \<open>lt = AT (Var x =\<^sub>s Var y \<squnion>\<^sub>s Var z)\<close> show ?thesis by auto
  next
    case (diff x y z)
    with C3 have "{\<pi> \<in> PI. \<pi> x} = {\<pi> \<in> PI. \<pi> y} - {\<pi> \<in> PI. \<pi> z}"
      using \<open>lt \<in> \<C>\<close> by fast
    with HUnion_place_realise_eq_iff_place_composition_same
    have "\<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> x}) =
          \<Squnion>HF (place_realise ` ({\<pi> \<in> PI. \<pi> y} - {\<pi> \<in> PI. \<pi> z}))"
      by argo
    also have "... = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> y}) - \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> z})"
      using HUnion_hdiff_if_image_pairwise_disjoint
      using finite_PI place_realise_pairwise_disjoint
      by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono)
    finally have "\<M> x = \<M> y - \<M> z" by fastforce
    with \<open>lt = AT (Var x =\<^sub>s Var y -\<^sub>s Var z)\<close> show ?thesis by auto
  next
    case (singleton x y)
    with C5_1 obtain \<pi>\<^sub>0 where "(y, \<pi>\<^sub>0) \<in> at\<^sub>p" "\<pi>\<^sub>0 x" "(\<forall>\<pi>'\<in>PI. \<pi>' \<noteq> \<pi>\<^sub>0 \<longrightarrow> \<not> \<pi>' x)" "\<pi>\<^sub>0 \<in> PI"
      using \<open>lt \<in> \<C>\<close> range_at\<^sub>p by blast
    then have "{\<pi> \<in> PI. \<pi> x} = {\<pi>\<^sub>0}" by blast
    then have "\<M> x = place_realise \<pi>\<^sub>0" by fastforce
    also have "... = HF {\<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>0)}"
      using \<open>(y, \<pi>\<^sub>0) \<in> at\<^sub>p\<close> by (simp add: Range.intros) 
    finally have "\<M> x = HF {\<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>0)}" .
    moreover
    have "HF {\<M> y} = HF {\<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> y})}" by simp
    moreover
    have "{\<pi> \<in> PI. \<pi> y} = parents G_PI \<pi>\<^sub>0"
    proof (standard; standard)
      fix \<pi> assume "\<pi> \<in> {\<pi> \<in> PI. \<pi> y}"
      then have "\<pi> \<in> PI" "\<pi> y" by blast+
      with singleton \<open>\<pi>\<^sub>0 x\<close> \<open>\<pi>\<^sub>0 \<in> PI\<close> \<open>lt \<in> \<C>\<close>
      have "(\<pi>, \<pi>\<^sub>0) \<in> membership" by auto
      then show "\<pi> \<in> parents G_PI \<pi>\<^sub>0"
        using arcs_ends_G_PI by blast
    next
      fix \<pi> assume "\<pi> \<in> parents G_PI \<pi>\<^sub>0"
      then have "\<pi> \<in> PI" by force
      from \<open>\<pi> \<in> parents G_PI \<pi>\<^sub>0\<close> have "(\<pi>, \<pi>\<^sub>0) \<in> membership"
        by fastforce
      then obtain x' y' where "AT (Var x' =\<^sub>s Single (Var y')) \<in> \<C>" "\<pi> y'" "\<pi>\<^sub>0 x'"
        by auto
      with C5_1 have "(y', \<pi>\<^sub>0) \<in> at\<^sub>p" using \<open>\<pi>\<^sub>0 \<in> PI\<close> by fast

      from singleton \<open>lt \<in> \<C>\<close> have "y \<in> W" by force
      from \<open>AT (Var x' =\<^sub>s Single (Var y')) \<in> \<C>\<close> have "y' \<in> W" by force
      from \<open>(y', \<pi>\<^sub>0) \<in> at\<^sub>p\<close> \<open>(y, \<pi>\<^sub>0) \<in> at\<^sub>p\<close> C5_2 have "\<forall>\<pi> \<in> PI. \<pi> y = \<pi> y'"
        using \<open>y \<in> W\<close> \<open>y' \<in> W\<close> by fast
      with \<open>\<pi> y'\<close> \<open>\<pi> \<in> PI\<close> have "\<pi> y" by fast
      moreover
      from \<open>\<pi> \<in> parents G_PI \<pi>\<^sub>0\<close> have "\<pi> \<in> PI" by fastforce
      ultimately
      show "\<pi> \<in> {\<pi> \<in> PI. \<pi> y}" by blast
    qed
    with HUnion_place_realise_eq_iff_place_composition_same
    have "\<Squnion>HF (place_realise ` parents G_PI \<pi>\<^sub>0) = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> y})"
      by argo
    ultimately
    have "\<M> x = HF {\<M> y}" by argo
    with \<open>lt = AT (Var x =\<^sub>s Single (Var y))\<close> show ?thesis by simp
  qed
qed

text \<open>Correspondence of proper Venn regions and realization of places, and singleton model property\<close>

interpretation proper_Venn_regions V \<M>
  using finite_\<C>
  apply unfold_locales
  by (simp add: finite_vars_fm proper_Venn_regions_def)

lemma proper_Venn_region_place_composition:
  assumes "\<alpha> \<in> P\<^sup>+ V"
    shows "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x. \<pi> x \<longleftrightarrow> x \<in> \<alpha>})"
proof -
  from finite_\<C> have "finite V" by (simp add: finite_vars_fm)
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> \<open>finite V\<close> have "finite \<alpha>" by blast
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "\<alpha> \<noteq> {}" by simp
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "\<alpha> \<subseteq> V" by simp

  from \<open>finite \<alpha>\<close> \<open>\<alpha> \<noteq> {}\<close>
  have "\<Sqinter>HF (\<M> ` \<alpha>) = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x})"
  proof (induction \<alpha>)
    case (insert x \<alpha>')
    then show ?case
    proof (cases "\<alpha>' = {}")
      case True
      then have "\<Sqinter>HF (\<M> ` insert x \<alpha>') = \<M> x"
        using HInter_singleton by fastforce
      with True show ?thesis by force
    next
      case False
      with insert.IH have IH': "\<Sqinter>HF (\<M> ` \<alpha>') = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x \<in> \<alpha>'. \<pi> x})"
        by blast
      from False have "\<M> ` \<alpha>' \<noteq> {}" by blast
      with \<open>finite \<alpha>'\<close> have "\<Sqinter>HF (\<M> ` insert x \<alpha>') = \<M> x \<sqinter> \<Sqinter>HF (\<M> ` \<alpha>')"
        using HInter_hinsert[where ?A = "HF (\<M> ` \<alpha>')" and ?a = "\<M> x"]
        using HF_nonempty[where ?S = "\<M> ` \<alpha>'"]
        using HF_insert_hinsert[where ?S = "\<M> ` \<alpha>'" and ?x = "\<M> x"]
        by auto
      also have "... = \<M> x \<sqinter> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. (\<forall>x\<in>\<alpha>'. \<pi> x)})"
        using IH' by argo
      also have "... = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> x}) \<sqinter> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x \<in> \<alpha>'. \<pi> x})"
        by auto
      also have "... = \<Squnion>HF (place_realise ` ({\<pi> \<in> PI. \<pi> x} \<inter> {\<pi> \<in> PI. \<forall>x \<in> \<alpha>'. \<pi> x}))"
        using hinter_HUnion_if_image_pairwise_disjoint
        using finite_PI place_realise_pairwise_disjoint by force
      also have "... = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x \<in> insert x \<alpha>'. \<pi> x})"
        by (smt (verit, del_insts) Collect_cong Collect_mem_eq IntI Int_iff insert_iff mem_Collect_eq)
      finally show ?thesis .
    qed
  qed blast
  moreover
  have "\<Squnion>HF (\<M> ` (V - \<alpha>)) = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y})"
  proof (standard; standard)
    from finite_PI have "finite {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}" by simp
    fix c assume "c \<^bold>\<in> \<Squnion>HF (\<M> ` (V - \<alpha>))"
    then obtain y where "y \<in> V - \<alpha>" "c \<^bold>\<in> \<M> y" by auto
    then have "c \<^bold>\<in> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<pi> y})" by simp
    then obtain \<pi> where "\<pi> \<in> PI" "\<pi> y" "c \<^bold>\<in> place_realise \<pi>" by auto
    with \<open>y \<in> V - \<alpha>\<close> have "\<pi> \<in> {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}" by blast
    then have "place_realise \<pi> \<le> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y})"
      using mem_hsubset_HUnion[where ?S = "place_realise ` {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}" and ?s = "place_realise \<pi>"]
      using \<open>finite {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}\<close>
      by blast
    with \<open>c \<^bold>\<in> place_realise \<pi>\<close> show "c \<^bold>\<in> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y})"
      by fast
  next
    fix c assume "c \<^bold>\<in> \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y})"
    then obtain \<pi> y where "\<pi> \<in> PI" "y \<in> V - \<alpha>" "\<pi> y" "c \<^bold>\<in> place_realise \<pi>"
      by auto
    then have "\<pi> \<in> {\<pi> \<in> PI. \<pi> y}" by blast
    moreover
    from finite_PI have "finite {\<pi> \<in> PI. \<pi> y}" by simp
    ultimately
    have "c \<^bold>\<in> \<M> y" using \<open>c \<^bold>\<in> place_realise \<pi>\<close>
      using mem_hsubset_HUnion[where ?S = "place_realise ` {\<pi> \<in> PI. \<pi> y}" and ?s = "place_realise \<pi>"]
      by auto
    with \<open>y \<in> V - \<alpha>\<close> show "c \<^bold>\<in> \<Squnion>HF (\<M> ` (V - \<alpha>))"
      using mem_hsubset_HUnion[where ?S = "\<M> ` (V - \<alpha>)" and ?s = "\<M> y"]
      using finite_V by blast
  qed
  ultimately
  have "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x\<in>\<alpha>. \<pi> x}) - \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<exists>y\<in>\<Union> (vars ` \<C>) - \<alpha>. \<pi> y})"
    by auto
  also have "... = \<Squnion>HF (place_realise ` ({\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x} - {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}))"
    using HUnion_hdiff_if_image_pairwise_disjoint[where ?f = place_realise and ?U = PI
          and ?S = "{\<pi> \<in> PI. \<forall>x\<in>\<alpha>. \<pi> x}" and ?T = "{\<pi> \<in> PI. \<exists>y\<in>\<Union> (vars ` \<C>) - \<alpha>. \<pi> y}"]
    using place_realise_pairwise_disjoint
    by (simp add: finite_PI subsetI)
  moreover
  have "{\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x} - {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y} = {\<pi> \<in> PI. (\<forall>x \<in> \<alpha>. \<pi> x) \<and> (\<forall>y \<in> V - \<alpha>. \<not> \<pi> y)}"
  proof (standard; standard)
    fix \<pi> assume "\<pi> \<in> {\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x} - {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}"
    then have "\<pi> \<in> {\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x}" "\<pi> \<notin> {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}"
      by blast+
    from \<open>\<pi> \<in> {\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x}\<close> have "\<pi> \<in> PI" "\<forall>x \<in> \<alpha>. \<pi> x" by blast+
    moreover
    from \<open>\<pi> \<notin> {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}\<close> \<open>\<pi> \<in> PI\<close> have "\<forall>y \<in> V - \<alpha>. \<not> \<pi> y" by blast
    ultimately
    show "\<pi> \<in> {\<pi> \<in> PI. (\<forall>x \<in> \<alpha>. \<pi> x) \<and> (\<forall>y \<in> V - \<alpha>. \<not> \<pi> y)}" by blast
  next
    fix \<pi> assume "\<pi> \<in> {\<pi> \<in> PI. (\<forall>x \<in> \<alpha>. \<pi> x) \<and> (\<forall>y \<in> V - \<alpha>. \<not> \<pi> y)}"
    then have "\<pi> \<in> {\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x}" "\<pi> \<in> {\<pi> \<in> PI. \<forall>y \<in> V - \<alpha>. \<not> \<pi> y}" by blast+
    then show "\<pi> \<in> {\<pi> \<in> PI. \<forall>x \<in> \<alpha>. \<pi> x} - {\<pi> \<in> PI. \<exists>y \<in> V - \<alpha>. \<pi> y}" by blast
  qed
  ultimately
  have 1: "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. (\<forall>x \<in> \<alpha>. \<pi> x) \<and> (\<forall>y \<in> V - \<alpha>. \<not> \<pi> y)})"
    by argo
  
  have "\<pi> x \<longleftrightarrow> x \<in> \<alpha>" if "\<forall>x \<in> \<alpha>. \<pi> x" "\<forall>y \<in> V - \<alpha>. \<not> \<pi> y" and "\<pi> \<in> PI" for \<pi> x
  proof
    assume "\<pi> x"
    with \<open>\<pi> \<in> PI\<close> PI_subset_places_V places_domain have "x \<in> V"
      by fastforce
    moreover
    from \<open>\<forall>y \<in> V - \<alpha>. \<not> \<pi> y\<close> \<open>\<pi> x\<close> have "x \<notin> V - \<alpha>" by blast
    ultimately
    show "x \<in> \<alpha>" by blast
  next
    assume "x \<in> \<alpha>"
    with \<open>\<forall>x \<in> \<alpha>. \<pi> x\<close> show "\<pi> x" by blast
  qed
  moreover
  have "\<forall>x \<in> \<alpha>. \<pi> x" "\<forall>y \<in> V - \<alpha>. \<not> \<pi> y" if "\<forall>x. \<pi> x \<longleftrightarrow> x \<in> \<alpha>" for \<pi>
    using that by blast+
  ultimately
  have 2: "{\<pi> \<in> PI. (\<forall>x \<in> \<alpha>. \<pi> x) \<and> (\<forall>y \<in> V - \<alpha>. \<not> \<pi> y)} = {\<pi> \<in> PI. \<forall>x. \<pi> x \<longleftrightarrow> x \<in> \<alpha>}"
    by blast

  from 1 2
  show "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x. \<pi> x \<longleftrightarrow> x \<in> \<alpha>})"
    by argo    
qed

lemma place_corresponds_to_proper_Venn_region:
  assumes "\<alpha> \<in> P\<^sup>+ V"
      and "(\<lambda>x. x \<in> \<alpha>) \<in> PI"
    shows "proper_Venn_region \<alpha> = place_realise (\<lambda>x. x \<in> \<alpha>)"
proof -
  from proper_Venn_region_place_composition \<open>\<alpha> \<in> P\<^sup>+ V\<close>
  have "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {\<pi> \<in> PI. \<forall>x. \<pi> x = (x \<in> \<alpha>)})"
    by blast
  moreover
  from \<open>(\<lambda>x. x \<in> \<alpha>) \<in> PI\<close> have "{\<pi> \<in> PI. \<forall>x. \<pi> x = (x \<in> \<alpha>)} = {\<lambda>x. x \<in> \<alpha>}" by blast
  ultimately
  have "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {\<lambda>x. x \<in> \<alpha>})"
    by argo
 then show ?thesis by auto
qed

lemma canonical_assignments_singleton:
  assumes "\<alpha> \<in> P\<^sup>+ V"
    shows "hcard (proper_Venn_region \<alpha>) \<le> 1"
proof (cases "(\<lambda>x. x \<in> \<alpha>) \<in> PI")
  case True
  with place_corresponds_to_proper_Venn_region \<open>\<alpha> \<in> P\<^sup>+ V\<close>
  have "proper_Venn_region \<alpha> = place_realise (\<lambda>x. x \<in> \<alpha>)" by blast
  with place_realise_singleton True show ?thesis by presburger
next
  case False
  have "\<not> (\<exists>\<pi> \<in> PI. (\<forall>x. \<pi> x = (x \<in> \<alpha>)))"
  proof (rule ccontr)
    assume "\<not> \<not> (\<exists>\<pi>\<in>PI. \<forall>x. \<pi> x = (x \<in> \<alpha>))"
    then obtain \<pi> where "\<pi> \<in> PI" "\<pi> = (\<lambda>x. x \<in> \<alpha>)" by blast
    with False show False by blast
  qed
  then have "{\<pi> \<in> PI. \<forall>x. \<pi> x = (x \<in> \<alpha>)} = {}" by blast
  with proper_Venn_region_place_composition \<open>\<alpha> \<in> P\<^sup>+ V\<close>
  have "proper_Venn_region \<alpha> = \<Squnion>HF (place_realise ` {})" by presburger
  also have "... = 0" by auto
  finally show ?thesis by auto
qed

end

end