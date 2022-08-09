section\<open>Relative, Choice-less Cardinal Numbers\<close>

theory Cardinal_Relative
  imports
    Lambda_Replacement
    Univ_Relative
begin

txt\<open>The following command avoids that a commonly used one-letter variable be
captured by the definition of the constructible universe \<^term>\<open>L\<close>.\<close>
hide_const (open) L

txt\<open>We also return to the old notation for \<^term>\<open>sum\<close> to preserve the old
Constructibility code.\<close>
no_notation oadd (infixl \<open>+\<close> 65)
notation sum (infixr \<open>+\<close> 65)

definition
  Finite_rel   :: "[i\<Rightarrow>o,i]=>o"  where
  "Finite_rel(M,A) \<equiv> \<exists>om[M]. \<exists>n[M]. omega(M,om) \<and> n\<in>om \<and> eqpoll_rel(M,A,n)"

definition
  banach_functor :: "[i,i,i,i,i] \<Rightarrow> i" where
  "banach_functor(X,Y,f,g,W) \<equiv> X - g``(Y - f``W)"

lemma banach_functor_subset: "banach_functor(X,Y,f,g,W) \<subseteq> X"
  unfolding banach_functor_def by auto

definition
  is_banach_functor :: "[i\<Rightarrow>o,i,i,i,i,i,i]\<Rightarrow>o"  where
  "is_banach_functor(M,X,Y,f,g,W,b) \<equiv>
      \<exists>fW[M]. \<exists>YfW[M]. \<exists>gYfW[M]. image(M,f,W,fW) \<and> setdiff(M,Y,fW,YfW) \<and>
                                 image(M,g,YfW,gYfW) \<and> setdiff(M,X,gYfW,b)"


lemma (in M_basic) banach_functor_abs :
  assumes "M(X)" "M(Y)" "M(f)" "M(g)"
  shows "relation1(M,is_banach_functor(M,X,Y,f,g),banach_functor(X,Y,f,g))"
  unfolding relation1_def is_banach_functor_def banach_functor_def
  using assms
  by simp

lemma (in M_basic) banach_functor_closed:
  assumes "M(X)" "M(Y)" "M(f)" "M(g)"
  shows "\<forall>W[M]. M(banach_functor(X,Y,f,g,W))"
  unfolding banach_functor_def using assms image_closed
  by simp

context M_trancl
begin

lemma iterates_banach_functor_closed:
  assumes "n\<in>\<omega>" "M(X)" "M(Y)" "M(f)" "M(g)"
  shows "M(banach_functor(X,Y,f,g)^n(0))"
  using assms banach_functor_closed
  by (induct) simp_all

lemma banach_repl_iter':
  assumes
    "\<And>A. M(A) \<Longrightarrow> separation(M, \<lambda>b. \<exists>x\<in>A. x \<in> \<omega> \<and> b = banach_functor(X, Y, f, g)^x (0))"
    "M(X)" "M(Y)" "M(f)" "M(g)"
  shows
    "strong_replacement(M, \<lambda>x y. x\<in>nat \<and> y = banach_functor(X, Y, f, g)^x (0))"
  unfolding strong_replacement_def
proof clarsimp
  fix A
  let ?Z="{b \<in> Pow\<^bsup>M\<^esup>(X) . (\<exists>x\<in>A. x \<in> \<omega> \<and> b = banach_functor(X, Y, f, g)^x (0))}"
  assume "M(A)"
  moreover
  note assms
  moreover from calculation
  have "M(?Z)" by simp
  moreover from assms(2-)
  have "b \<in> ?Z \<longleftrightarrow> (\<exists>x\<in>A. x \<in> \<omega> \<and> b = banach_functor(X, Y, f, g)^x (0))" for b
    by (auto, rename_tac x, induct_tac x, (auto simp:def_Pow_rel)[1],
        rule_tac def_Pow_rel[THEN iffD2, OF iterates_banach_functor_closed[of _ X Y f g]])
          (simp_all add:banach_functor_subset)
  ultimately
  show "\<exists>Z[M]. \<forall>b[M]. b \<in> Z \<longleftrightarrow> (\<exists>x\<in>A. x \<in> \<omega> \<and> b = banach_functor(X, Y, f, g)^x (0))"
    by (intro rexI[of _ ?Z]) simp
qed

end \<comment> \<open>\<^locale>\<open>M_trancl\<close>\<close>

context M_Perm
begin

lemma mem_Pow_rel: "M(r) \<Longrightarrow> a \<in> Pow_rel(M,r) \<Longrightarrow> a \<in> Pow(r) \<and> M(a)"
  using Pow_rel_char by simp

lemma mem_bij_abs: "\<lbrakk>M(f);M(A);M(B)\<rbrakk> \<Longrightarrow>  f \<in> bij\<^bsup>M\<^esup>(A,B) \<longleftrightarrow> f\<in>bij(A,B)"
  using bij_rel_char by simp

lemma mem_inj_abs: "\<lbrakk>M(f);M(A);M(B)\<rbrakk> \<Longrightarrow>  f \<in> inj\<^bsup>M\<^esup>(A,B) \<longleftrightarrow> f\<in>inj(A,B)"
  using inj_rel_char by simp

lemma mem_surj_abs: "\<lbrakk>M(f);M(A);M(B)\<rbrakk> \<Longrightarrow>  f \<in> surj\<^bsup>M\<^esup>(A,B) \<longleftrightarrow> f\<in>surj(A,B)"
  using surj_rel_char by simp

end \<comment> \<open>\<^locale>\<open>M_Perm\<close>\<close>

locale M_cardinals = M_ordertype + M_trancl + M_Perm + M_replacement +
  assumes
    radd_separation: "M(R) \<Longrightarrow> M(S) \<Longrightarrow>
    separation(M, \<lambda>z.
      (\<exists>x y. z = \<langle>Inl(x), Inr(y)\<rangle>) \<or>
         (\<exists>x' x. z = \<langle>Inl(x'), Inl(x)\<rangle> \<and> \<langle>x', x\<rangle> \<in> R) \<or>
         (\<exists>y' y. z = \<langle>Inr(y'), Inr(y)\<rangle> \<and> \<langle>y', y\<rangle> \<in> S))"
    and
    rmult_separation: "M(b) \<Longrightarrow> M(d) \<Longrightarrow> separation(M,
    \<lambda>z. \<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> b \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> d))"

begin

lemma rvimage_separation: "M(f) \<Longrightarrow> M(r) \<Longrightarrow>
    separation(M, \<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> \<langle>f ` x, f ` y\<rangle> \<in> r)"
  using separation_Pair separation_in lam_replacement_product
    lam_replacement_fst lam_replacement_snd lam_replacement_constant
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by simp

lemma radd_closed[intro,simp]: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> M(c) \<Longrightarrow> M(d) \<Longrightarrow> M(radd(a,b,c,d))"
  using radd_separation by (auto simp add: radd_def)

lemma rmult_closed[intro,simp]: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> M(c) \<Longrightarrow> M(d) \<Longrightarrow> M(rmult(a,b,c,d))"
  using rmult_separation by (auto simp add: rmult_def)

end \<comment> \<open>\<^locale>\<open>M_cardinals\<close>\<close>

lemma (in M_cardinals) is_cardinal_iff_Least:
  assumes "M(A)" "M(\<kappa>)"
  shows "is_cardinal(M,A,\<kappa>) \<longleftrightarrow> \<kappa> = (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A)"
  using is_cardinal_iff assms
  unfolding cardinal_rel_def by simp

subsection\<open>The Schroeder-Bernstein Theorem\<close>
text\<open>See Davey and Priestly, page 106\<close>

context M_cardinals
begin

subsection\<open>Banach's Decomposition Theorem\<close>

lemma bnd_mono_banach_functor: "bnd_mono(X, banach_functor(X,Y,f,g))"
  unfolding bnd_mono_def banach_functor_def
  by blast

lemma inj_Inter:
  assumes "g \<in> inj(Y,X)" "A\<noteq>0" "\<forall>a\<in>A. a \<subseteq> Y"
  shows "g``(\<Inter>A) = (\<Inter>a\<in>A. g``a)"
proof (intro equalityI subsetI)
  fix x
  from assms
  obtain a where "a\<in>A" by blast
  moreover
  assume "x \<in> (\<Inter>a\<in>A. g `` a)"
  ultimately
  have x_in_im: "x \<in> g``y" if "y\<in>A" for y
    using that by auto
  have exists: "\<exists>z \<in> y. x = g`z" if "y\<in>A" for y
  proof -
    note that
    moreover from this and x_in_im
    have "x \<in> g``y" by simp
    moreover from calculation
    have "x \<in> g``y" by simp
    moreover
    note assms
    ultimately
    show ?thesis
      using image_fun[OF inj_is_fun] by auto
  qed
  with \<open>a\<in>A\<close>
  obtain z where "z \<in> a" "x = g`z" by auto
  moreover
  have "z \<in> y" if "y\<in>A" for y
  proof -
    from that and exists
    obtain w where "w \<in> y" "x = g`w" by auto
    moreover from this \<open>x = g`z\<close> assms that \<open>a\<in>A\<close> \<open>z\<in>a\<close>
    have "z = w" unfolding inj_def by blast
    ultimately
    show ?thesis by simp
  qed
  moreover
  note assms
  moreover from calculation
  have "z \<in> \<Inter>A" by auto
  moreover from calculation
  have "z \<in> Y" by blast
  ultimately
  show "x \<in> g `` (\<Inter>A)"
    using inj_is_fun[THEN funcI, of g] by fast
qed auto

lemma contin_banach_functor:
  assumes "g \<in> inj(Y,X)"
  shows "contin(banach_functor(X,Y,f,g))"
  unfolding contin_def
proof (intro allI impI)
  fix A
  assume "directed(A)"
  then
  have "A \<noteq> 0"
    unfolding directed_def ..
  have "banach_functor(X, Y, f, g, \<Union>A) = X - g``(Y - f``(\<Union>A))"
    unfolding banach_functor_def ..
  also
  have " \<dots> = X - g``(Y - (\<Union>a\<in>A. f``a))"
    by auto
  also from \<open>A\<noteq>0\<close>
  have " \<dots> = X - g``(\<Inter>a\<in>A. Y-f``a)"
    by auto
  also from \<open>A\<noteq>0\<close> and assms
  have " \<dots> = X - (\<Inter>a\<in>A. g``(Y-f``a))"
    using inj_Inter[of g Y X "{Y-f``a. a\<in>A}" ] by fastforce
  also from \<open>A\<noteq>0\<close>
  have " \<dots> = (\<Union>a\<in>A. X - g``(Y-f``a))" by simp
  also
  have " \<dots> = (\<Union>a\<in>A. banach_functor(X, Y, f, g, a))"
    unfolding banach_functor_def ..
  finally
  show "banach_functor(X,Y,f,g,\<Union>A) = (\<Union>a\<in>A. banach_functor(X,Y,f,g,a))" .
qed

lemma lfp_banach_functor:
  assumes "g\<in>inj(Y,X)"
  shows "lfp(X, banach_functor(X,Y,f,g)) =
       (\<Union>n\<in>nat. banach_functor(X,Y,f,g)^n (0))"
  using assms lfp_eq_Union bnd_mono_banach_functor contin_banach_functor
  by simp

lemma lfp_banach_functor_closed:
  assumes "M(g)" "M(X)" "M(Y)" "M(f)" "g\<in>inj(Y,X)"
    and banach_repl_iter: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> M(f) \<Longrightarrow> M(g) \<Longrightarrow>
               strong_replacement(M, \<lambda>x y. x\<in>nat \<and> y = banach_functor(X, Y, f, g)^x (0))"
  shows "M(lfp(X, banach_functor(X,Y,f,g)))"
proof -
  from assms
  have "M(banach_functor(X,Y,f,g)^n (0))" if "n\<in>nat" for n
    by(rule_tac nat_induct[OF that],simp_all add:banach_functor_closed)
  with assms
  show ?thesis
    using family_union_closed'[OF banach_repl_iter M_nat] lfp_banach_functor
    by simp
qed

lemma banach_decomposition_rel:
  assumes
    banach_repl_iter: "M(f) \<Longrightarrow> M(g) \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow>
               strong_replacement(M, \<lambda>x y. x\<in>nat \<and> y = banach_functor(X, Y, f, g)^x (0))"
  shows
    "[| M(f); M(g); M(X); M(Y); f \<in> X->Y;  g \<in> inj(Y,X) |] ==>
      \<exists>XA[M]. \<exists>XB[M]. \<exists>YA[M]. \<exists>YB[M].
         (XA \<inter> XB = 0) & (XA \<union> XB = X) &
         (YA \<inter> YB = 0) & (YA \<union> YB = Y) &
         f``XA=YA & g``YB=XB"
  apply (intro rexI conjI)
           apply (rule_tac [6] Banach_last_equation)
           apply (rule_tac [5] refl)
          apply (assumption |
      rule inj_is_fun Diff_disjoint Diff_partition fun_is_rel
      image_subset lfp_subset)+
  using lfp_banach_functor_closed[of g X Y f] assms
  unfolding banach_functor_def by simp_all

lemma schroeder_bernstein_closed:
  assumes
    banach_repl_iter: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> M(f) \<Longrightarrow> M(g) \<Longrightarrow>
               strong_replacement(M, \<lambda>x y. x\<in>nat \<and> y = banach_functor(X, Y, f, g)^x (0))"
  shows
  "[| M(f); M(g); M(X); M(Y); f \<in> inj(X,Y);  g \<in> inj(Y,X) |] ==> \<exists>h[M]. h \<in> bij(X,Y)"
  apply (insert banach_decomposition_rel [of f g X Y, OF banach_repl_iter])
  apply (simp add: inj_is_fun)
  apply (auto)
  apply (rule_tac x="restrict(f,XA) \<union> converse(restrict(g,YB))" in rexI)
   apply (auto intro!: restrict_bij bij_disjoint_Un intro: bij_converse_bij)
  done

text\<open>The previous lemmas finish our original, direct relativization
of the material involving the iterative proof (as appearing in \<^theory>\<open>ZF.Cardinal\<close>)
of the Schröder-Bernstein theorem. Next, we formalize 
Zermelo's proof that replaces the recursive construction by a fixed point
represented as an intersection \cite[Exr. x4.27]{moschovakis1994notes}. This allows
to avoid at least one replacement assumption.\<close>

lemma dedekind_zermelo:
  assumes
    "A' \<subseteq> B" "B \<subseteq> A" "A \<approx>\<^bsup>M\<^esup> A'"
    and types: "M(A')" "M(B)" "M(A)"
  shows
    "A \<approx>\<^bsup>M\<^esup> B"
proof -
  from \<open>A \<approx>\<^bsup>M\<^esup> A'\<close> and types
  obtain f where "f \<in> bij\<^bsup>M\<^esup>(A,A')"
    unfolding eqpoll_rel_def by blast
  let ?Q="B - f``A"
  from \<open>f \<in> _\<close> \<open>A' \<subseteq> B\<close> types
  have "f``X \<subseteq> B" for X
    using mem_bij_rel[THEN bij_is_fun, THEN Image_sub_codomain, of f A A'] by auto
  moreover
  note \<open>B \<subseteq> A\<close>
  moreover from calculation
  have "f``X \<subseteq> A" for X by auto
  moreover
  define \<T> where "\<T>  \<equiv> { X \<in> Pow\<^bsup>M\<^esup>(A) . ?Q \<union> f `` X \<subseteq> X}"
  moreover from calculation
  have "A \<in> \<T>" using def_Pow_rel by (auto simp:types)
  ultimately
  have "\<T> \<noteq> 0" unfolding \<T>_def by auto
  let ?T="\<Inter>\<T>"
  have "?T \<subseteq> A"
  proof
    fix x
    assume "x \<in> ?T"
    with \<open>\<T> \<noteq> 0\<close>
    obtain X where "x \<in> X" "X \<in> \<T>"
      by blast
    moreover from this
    have "X \<in> Pow\<^bsup>M\<^esup>(A)"
      unfolding \<T>_def by simp
    moreover from calculation and \<open>M(A)\<close>
    have "M(x)" using Pow_rel_char by (auto dest:transM)
    ultimately
    show "x \<in> A" using Pow_rel_char by (auto simp:types)
  qed
  moreover from \<open>\<T> \<noteq> 0\<close>
  have "?Q \<union> f``?T \<subseteq> ?T"
    using image_mono unfolding \<T>_def by blast
  moreover from \<open>f \<in> _\<close>
  have "M(\<T>)"
    using zermelo_separation unfolding \<T>_def by (auto simp:types dest:transM)
  moreover from this
  have "M(?T)" by simp
  moreover
  note \<open>\<T> \<noteq> 0\<close>
  ultimately
  have "?T \<in> \<T>"
    unfolding \<T>_def using def_Pow_rel
    by (auto simp:types)
  have "?T \<subseteq> ?Q \<union> f``?T"
  proof (intro subsetI, rule ccontr)
    fix x
    from \<open>_ \<union> f ``?T \<subseteq> ?T\<close>
    have "f `` (?T - {x}) \<subseteq> ?T" "f `` (?T - {x}) \<subseteq> f`` ?T" by auto
    assume "x \<in> ?T" "x \<notin> ?Q \<union> f``?T"
    then
    have "?T - {x} \<in> \<T>"
    proof -
      note \<open>f `` (?T - {x}) \<subseteq> ?T\<close>
      moreover from this and \<open>x \<notin> _ \<union> f``?T\<close>
      have "x \<notin> f `` ?T" by simp
      ultimately
      have "f `` (?T - {x}) \<subseteq> ?T - {x}" by auto
      moreover from \<open>x \<notin> ?Q \<union> _\<close> \<open>?Q \<union> _ \<subseteq> ?T\<close>
      have "?Q \<subseteq> ?T - {x}" by auto
      moreover
      note \<open>?T \<in> _\<close> \<open>x \<in> ?T\<close> \<open>M(?T)\<close> \<open>?T \<subseteq> _\<close>
      ultimately
      show ?thesis
        using def_Pow_rel[of "?T - {x}" A] transM[of _ ?T]
        unfolding \<T>_def
        by (auto simp:types)
    qed
    moreover
    note \<open>f `` (?T - {x}) \<subseteq> f`` ?T\<close>
    ultimately
    have "?T \<subseteq> ?T - {x}" by auto
    with \<open>x \<in> ?T\<close>
    show False by auto
  qed
  with \<open>?Q \<union> f``?T \<subseteq> ?T\<close>
  have "?T = ?Q \<union> f``?T" by auto
  from \<open>\<And>X. f``X \<subseteq> B\<close>
  have "(?Q \<union> f``?T) \<union> (f``A - f``?T) \<subseteq> B" by auto
  with \<open>?T = _\<close>
  have "?T \<union> (f``A - f``?T) \<subseteq> B" by simp
  with \<open>\<T> \<noteq> 0\<close> \<open>?T = _\<close>
  have "B = ?T \<union> (f``A - f``?T)"
  proof (intro equalityI, intro subsetI)
    fix x
    assume "x \<in> B"
    with \<open>\<T> \<noteq> 0\<close> \<open>?T = _\<close>
    show "x \<in> ?T \<union> (f``A - f``?T)"
      by (subst \<open>?T = _\<close>, clarify)
  qed
  moreover from \<open>?T \<subseteq> A\<close>
  have "A = ?T \<union> (A - ?T)" by auto
  moreover from \<open>M(?T)\<close> \<open>f \<in> _\<close>
  have "M(id(?T) \<union> restrict(f,A-?T))"
    using bij_rel_closed[THEN [2] transM] id_closed by (auto simp:types)
  moreover from \<open>?T = _\<close> \<open>f \<in> _\<close>
  have "f``A - f``?T = f``(A - ?T)"
    using bij_rel_char bij_is_inj[THEN inj_range_Diff, of f A]
    by (auto simp:types)
  from \<open>f \<in> _\<close> types
  have "id(?T) \<union> restrict(f, A-?T) \<in> bij(?T \<union> (A - ?T),?T \<union> (f``A - f``?T))"
    using id_bij mem_bij_rel[of _ A A', THEN bij_is_inj]
    by (rule_tac bij_disjoint_Un; clarsimp)
      (subst \<open>f``A - f``?T =_ \<close>, auto intro:restrict_bij, subst \<open>?T = _\<close>, auto)
  moreover
  note types
  ultimately
  show ?thesis
    using bij_rel_char unfolding eqpoll_rel_def by fastforce
qed

lemma schroeder_bernstein_closed':
  assumes "f \<in> inj\<^bsup>M\<^esup>(A,C)" " g \<in> inj\<^bsup>M\<^esup>(C,A)"
    and types:"M(A)" "M(C)"
  shows "A \<approx>\<^bsup>M\<^esup> C"
proof -
  from assms
  have "f \<in> inj(A,C)" " g \<in> inj(C,A)" "M(f)" "M(g)"
    using inj_rel_char by auto
  moreover from this
  have "g \<in> bij(C,range(g))" "g O f \<in> bij(A,range(g O f))"
    using inj_bij_range comp_inj by auto blast
  moreover from calculation
  have "range(g O f) \<subseteq> range(g)" "range(g) \<subseteq> A"
    using inj_is_fun[THEN range_fun_subset_codomain] by auto
  moreover from calculation
  obtain h where "h \<in> bij\<^bsup>M\<^esup>(A, range(g))"
    using dedekind_zermelo[of "range(g O f)" "range(g)" A]
      bij_rel_char def_eqpoll_rel
    by (auto simp:types)
  ultimately
  show ?thesis
    using bij_rel_char def_eqpoll_rel comp_bij[of h A "range(g)" "converse(g)" C]
      bij_converse_bij[of g C "range(g)"] by (auto simp:types)
qed

text\<open>Relative equipollence is an equivalence relation\<close>

declare mem_bij_abs[simp] mem_inj_abs[simp]

lemma bij_imp_eqpoll_rel:
  assumes "f \<in> bij(A,B)" "M(f)" "M(A)" "M(B)"
  shows "A \<approx>\<^bsup>M\<^esup> B"
  using assms by (auto simp add:def_eqpoll_rel)

lemma eqpoll_rel_refl: "M(A) \<Longrightarrow> A \<approx>\<^bsup>M\<^esup> A"
  using bij_imp_eqpoll_rel[OF id_bij, OF id_closed] .

lemma eqpoll_rel_sym: "X \<approx>\<^bsup>M\<^esup> Y \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow>  Y \<approx>\<^bsup>M\<^esup> X"
  unfolding def_eqpoll_rel using converse_closed
  by (auto intro: bij_converse_bij)

lemma eqpoll_rel_trans [trans]:
  "[|X \<approx>\<^bsup>M\<^esup> Y;  Y \<approx>\<^bsup>M\<^esup> Z;  M(X); M(Y) ; M(Z) |] ==> X \<approx>\<^bsup>M\<^esup> Z"
  unfolding def_eqpoll_rel by (auto intro: comp_bij)

text\<open>Relative le-pollence is a preorder\<close>

lemma subset_imp_lepoll_rel: "X \<subseteq> Y \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<lesssim>\<^bsup>M\<^esup> Y"
  unfolding def_lepoll_rel using id_subset_inj id_closed
  by simp blast

lemmas lepoll_rel_refl = subset_refl [THEN subset_imp_lepoll_rel, simp]

lemmas le_imp_lepoll_rel = le_imp_subset [THEN subset_imp_lepoll_rel]

lemma eqpoll_rel_imp_lepoll_rel: "X \<approx>\<^bsup>M\<^esup> Y ==> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<lesssim>\<^bsup>M\<^esup> Y"
  unfolding def_eqpoll_rel bij_def def_lepoll_rel using bij_is_inj
  by (auto)

lemma lepoll_rel_trans [trans]:
  assumes
    "X \<lesssim>\<^bsup>M\<^esup> Y" "Y \<lesssim>\<^bsup>M\<^esup> Z" "M(X)" "M(Y)" "M(Z)"
  shows
    "X \<lesssim>\<^bsup>M\<^esup> Z"
  using assms def_lepoll_rel
  by (auto intro: comp_inj)

lemma eq_lepoll_rel_trans [trans]:
  assumes
    "X \<approx>\<^bsup>M\<^esup> Y"  "Y \<lesssim>\<^bsup>M\<^esup> Z" "M(X)" "M(Y)" "M(Z)"
  shows
    "X \<lesssim>\<^bsup>M\<^esup> Z"
  using assms
  by (blast intro: eqpoll_rel_imp_lepoll_rel lepoll_rel_trans)

lemma lepoll_rel_eq_trans [trans]:
  assumes "X \<lesssim>\<^bsup>M\<^esup> Y"  "Y \<approx>\<^bsup>M\<^esup> Z" "M(X)" "M(Y)" "M(Z)"
  shows "X \<lesssim>\<^bsup>M\<^esup> Z"
  using assms
    eqpoll_rel_imp_lepoll_rel[of Y Z] lepoll_rel_trans[of X Y Z]
  by simp

lemma eqpoll_relI: "\<lbrakk> X \<lesssim>\<^bsup>M\<^esup> Y; Y \<lesssim>\<^bsup>M\<^esup> X; M(X) ; M(Y) \<rbrakk> \<Longrightarrow> X \<approx>\<^bsup>M\<^esup> Y"
  unfolding def_lepoll_rel using schroeder_bernstein_closed'
  by (auto simp del:mem_inj_abs)

lemma eqpoll_relE:
  "[| X \<approx>\<^bsup>M\<^esup> Y; [| X \<lesssim>\<^bsup>M\<^esup> Y; Y \<lesssim>\<^bsup>M\<^esup> X |] ==> P ;  M(X) ; M(Y) |] ==> P"
  by (blast intro: eqpoll_rel_imp_lepoll_rel eqpoll_rel_sym)

lemma eqpoll_rel_iff: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>\<^bsup>M\<^esup> Y \<longleftrightarrow> X \<lesssim>\<^bsup>M\<^esup> Y & Y \<lesssim>\<^bsup>M\<^esup> X"
  by (blast intro: eqpoll_relI elim: eqpoll_relE)

lemma lepoll_rel_0_is_0: "A \<lesssim>\<^bsup>M\<^esup> 0 \<Longrightarrow> M(A) \<Longrightarrow> A = 0"
  using def_lepoll_rel
  by (cases "A=0") (auto simp add: inj_def)

\<comment> \<open>\<^term>\<open>M(Y) \<Longrightarrow> 0 \<lesssim>\<^bsup>M\<^esup> Y\<close>\<close>
lemmas empty_lepoll_relI = empty_subsetI [THEN subset_imp_lepoll_rel, OF nonempty]

lemma lepoll_rel_0_iff: "M(A) \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> 0 \<longleftrightarrow> A=0"
  by (blast intro: lepoll_rel_0_is_0 lepoll_rel_refl)

lemma Un_lepoll_rel_Un:
  "[| A \<lesssim>\<^bsup>M\<^esup> B; C \<lesssim>\<^bsup>M\<^esup> D; B \<inter> D = 0; M(A); M(B); M(C); M(D) |] ==> A \<union> C \<lesssim>\<^bsup>M\<^esup> B \<union> D"
  using def_lepoll_rel using inj_disjoint_Un[of _ A B _ C D] if_then_replacement
  apply (auto)
  apply (rule, assumption)
  apply (auto intro!:lam_closed elim:transM)+
  done

lemma eqpoll_rel_0_is_0: "A \<approx>\<^bsup>M\<^esup> 0 \<Longrightarrow> M(A) \<Longrightarrow> A = 0"
  using eqpoll_rel_imp_lepoll_rel lepoll_rel_0_is_0 nonempty
  by blast

lemma eqpoll_rel_0_iff: "M(A) \<Longrightarrow> A \<approx>\<^bsup>M\<^esup> 0 \<longleftrightarrow> A=0"
  by (blast intro: eqpoll_rel_0_is_0 eqpoll_rel_refl)

lemma eqpoll_rel_disjoint_Un:
  "[| A \<approx>\<^bsup>M\<^esup> B;  C \<approx>\<^bsup>M\<^esup> D;  A \<inter> C = 0;  B \<inter> D = 0; M(A); M(B); M(C) ; M(D) |]
     ==> A \<union> C \<approx>\<^bsup>M\<^esup> B \<union> D"
  by (auto intro: bij_disjoint_Un simp add:def_eqpoll_rel)

subsection\<open>lesspoll: contributions by Krzysztof Grabczewski\<close>

lemma lesspoll_rel_not_refl: "M(i) \<Longrightarrow> ~ (i \<prec>\<^bsup>M\<^esup> i)"
  by (simp add: lesspoll_rel_def eqpoll_rel_refl)

lemma lesspoll_rel_irrefl: "i \<prec>\<^bsup>M\<^esup> i ==> M(i) \<Longrightarrow> P"
  by (simp add: lesspoll_rel_def eqpoll_rel_refl)

lemma lesspoll_rel_imp_lepoll_rel: "\<lbrakk>A \<prec>\<^bsup>M\<^esup> B; M(A); M(B)\<rbrakk>\<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> B"
  by (unfold lesspoll_rel_def, blast)

lemma rvimage_closed [intro,simp]:
  assumes
    "M(A)" "M(f)" "M(r)"
  shows
    "M(rvimage(A,f,r))"
  unfolding rvimage_def using assms rvimage_separation by auto

lemma lepoll_rel_well_ord: "[| A \<lesssim>\<^bsup>M\<^esup> B; well_ord(B,r); M(A); M(B); M(r) |] ==> \<exists>s[M]. well_ord(A,s)"
  unfolding def_lepoll_rel by (auto intro:well_ord_rvimage)

lemma lepoll_rel_iff_leqpoll_rel: "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> B \<longleftrightarrow> A \<prec>\<^bsup>M\<^esup> B | A \<approx>\<^bsup>M\<^esup> B"
  apply (unfold lesspoll_rel_def)
  apply (blast intro: eqpoll_relI elim: eqpoll_relE)
  done

end \<comment> \<open>\<^locale>\<open>M_cardinals\<close>\<close>

context M_cardinals
begin

lemma inj_rel_is_fun_M: "f \<in> inj\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(f) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> A \<rightarrow>\<^bsup>M\<^esup> B"
  using inj_is_fun function_space_rel_char by simp

\<comment> \<open>In porting the following theorem, I tried to follow the Discipline
strictly, though finally only an approach maximizing the use of
absoluteness results (@{thm function_space_rel_char inj_rel_char}) was
 the one paying dividends.\<close>
lemma inj_rel_not_surj_rel_succ:
  notes mem_inj_abs[simp del]
  assumes fi: "f \<in> inj\<^bsup>M\<^esup>(A, succ(m))" and fns: "f \<notin> surj\<^bsup>M\<^esup>(A, succ(m))"
    and types: "M(f)" "M(A)" "M(m)"
  shows "\<exists>f[M]. f \<in> inj\<^bsup>M\<^esup>(A,m)"
proof -
  from fi [THEN inj_rel_is_fun_M] fns types
  obtain y where y: "y \<in> succ(m)" "\<And>x. x\<in>A \<Longrightarrow> f ` x \<noteq> y" "M(y)"
    by (auto simp add: def_surj_rel)
  show ?thesis
  proof
    from types and \<open>M(y)\<close>
    show "M(\<lambda>z\<in>A. if f ` z = m then y else f ` z)"
      using transM[OF _ \<open>M(A)\<close>] lam_if_then_apply_replacement2 lam_replacement_iff_lam_closed
      by (auto)
    with types y fi
    have "(\<lambda>z\<in>A. if f`z = m then y else f`z) \<in> A\<rightarrow>\<^bsup>M\<^esup> m"
      using function_space_rel_char inj_rel_char inj_is_fun[of f A "succ(m)"]
      by (auto intro!: if_type [THEN lam_type] dest: apply_funtype)
    with types y fi
    show "(\<lambda>z\<in>A. if f`z = m then y else f`z) \<in> inj\<^bsup>M\<^esup>(A, m)"
      by (simp add: def_inj_rel) blast
  qed
qed

\<comment> \<open>Variations on transitivity\<close>

lemma lesspoll_rel_trans [trans]:
  "[| X \<prec>\<^bsup>M\<^esup> Y; Y \<prec>\<^bsup>M\<^esup> Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>\<^bsup>M\<^esup> Z"
  apply (unfold lesspoll_rel_def)
  apply (blast elim: eqpoll_relE intro: eqpoll_relI lepoll_rel_trans)
  done

lemma lesspoll_rel_trans1 [trans]:
  "[| X \<lesssim>\<^bsup>M\<^esup> Y; Y \<prec>\<^bsup>M\<^esup> Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>\<^bsup>M\<^esup> Z"
  apply (unfold lesspoll_rel_def)
  apply (blast elim: eqpoll_relE intro: eqpoll_relI lepoll_rel_trans)
  done

lemma lesspoll_rel_trans2 [trans]:
  "[|  X \<prec>\<^bsup>M\<^esup> Y; Y \<lesssim>\<^bsup>M\<^esup> Z; M(X); M(Y) ; M(Z)|] ==> X \<prec>\<^bsup>M\<^esup> Z"
  apply (unfold lesspoll_rel_def)
  apply (blast elim: eqpoll_relE intro: eqpoll_relI lepoll_rel_trans)
  done

lemma eq_lesspoll_rel_trans [trans]:
  "[| X \<approx>\<^bsup>M\<^esup> Y; Y \<prec>\<^bsup>M\<^esup> Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>\<^bsup>M\<^esup> Z"
  by (blast intro: eqpoll_rel_imp_lepoll_rel lesspoll_rel_trans1)

lemma lesspoll_rel_eq_trans [trans]:
  "[| X \<prec>\<^bsup>M\<^esup> Y; Y \<approx>\<^bsup>M\<^esup> Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>\<^bsup>M\<^esup> Z"
  by (blast intro: eqpoll_rel_imp_lepoll_rel lesspoll_rel_trans2)

lemma is_cardinal_cong:
  assumes "X \<approx>\<^bsup>M\<^esup> Y" "M(X)" "M(Y)"
  shows "\<exists>\<kappa>[M]. is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)"
proof -
  from assms
  have "(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> X) = (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> Y)"
    by (intro Least_cong) (auto intro: comp_bij bij_converse_bij simp add:def_eqpoll_rel)
  moreover from assms
  have "M(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> X)"
    using Least_closed' by fastforce
  moreover
  note assms
  ultimately
  show ?thesis
    using is_cardinal_iff_Least
    by auto
qed

\<comment> \<open>ported from Cardinal\<close>
lemma cardinal_rel_cong: "X \<approx>\<^bsup>M\<^esup> Y \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> |X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup>"
  apply (simp add: def_eqpoll_rel cardinal_rel_def)
  apply (rule Least_cong)
  apply (auto intro: comp_bij bij_converse_bij)
  done

lemma well_ord_is_cardinal_eqpoll_rel:
  assumes "well_ord(A,r)" shows "is_cardinal(M,A,\<kappa>) \<Longrightarrow> M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> M(r) \<Longrightarrow> \<kappa> \<approx>\<^bsup>M\<^esup> A"
proof (subst is_cardinal_iff_Least[THEN iffD1, of A \<kappa>])
  assume "M(A)" "M(\<kappa>)" "M(r)" "is_cardinal(M,A,\<kappa>)"
  moreover from assms and calculation
  obtain f i where "M(f)" "Ord(i)" "M(i)" "f \<in> bij(A,i)"
    using ordertype_exists[of A r] ord_iso_is_bij by auto
  moreover
  have "M(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A)"
    using Least_closed' by fastforce
  ultimately
  show "(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A) \<approx>\<^bsup>M\<^esup> A"
    using assms[THEN well_ord_imp_relativized]
      LeastI[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A" i] Ord_ordertype[OF assms]
      bij_converse_bij[THEN bij_imp_eqpoll_rel, of f] by simp
qed

lemmas Ord_is_cardinal_eqpoll_rel = well_ord_Memrel[THEN well_ord_is_cardinal_eqpoll_rel]

section\<open>Porting from \<^theory>\<open>ZF.Cardinal\<close>\<close>

txt\<open>The following results were ported more or less directly from \<^theory>\<open>ZF.Cardinal\<close>\<close>

\<comment> \<open>This result relies on various closure properties and
   thus cannot be translated directly\<close>
lemma well_ord_cardinal_rel_eqpoll_rel:
  assumes r: "well_ord(A,r)" and "M(A)" "M(r)" shows "|A|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> A"
  using assms well_ord_is_cardinal_eqpoll_rel is_cardinal_iff
  by blast

lemmas Ord_cardinal_rel_eqpoll_rel = well_ord_Memrel[THEN well_ord_cardinal_rel_eqpoll_rel]

lemma Ord_cardinal_rel_idem: "Ord(A) \<Longrightarrow> M(A) \<Longrightarrow> ||A|\<^bsup>M\<^esup>|\<^bsup>M\<^esup> = |A|\<^bsup>M\<^esup>"
  by (rule_tac Ord_cardinal_rel_eqpoll_rel [THEN cardinal_rel_cong]) auto

lemma well_ord_cardinal_rel_eqE:
  assumes woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" and eq: "|X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup>"
    and types: "M(X)" "M(r)" "M(Y)" "M(s)"
  shows "X \<approx>\<^bsup>M\<^esup> Y"
proof -
  from types
  have "X \<approx>\<^bsup>M\<^esup> |X|\<^bsup>M\<^esup>" by (blast intro: well_ord_cardinal_rel_eqpoll_rel [OF woX] eqpoll_rel_sym)
  also
  have "... = |Y|\<^bsup>M\<^esup>" by (rule eq)
  also from types
  have "... \<approx>\<^bsup>M\<^esup> Y" by (rule_tac well_ord_cardinal_rel_eqpoll_rel [OF woY])
  finally show ?thesis  by (simp add:types)
qed

lemma well_ord_cardinal_rel_eqpoll_rel_iff:
  "[| well_ord(X,r);  well_ord(Y,s); M(X); M(r); M(Y); M(s) |] ==> |X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup> \<longleftrightarrow> X \<approx>\<^bsup>M\<^esup> Y"
  by (blast intro: cardinal_rel_cong well_ord_cardinal_rel_eqE)

lemma Ord_cardinal_rel_le: "Ord(i) \<Longrightarrow> M(i) ==> |i|\<^bsup>M\<^esup> \<le> i"
  unfolding cardinal_rel_def
  using eqpoll_rel_refl Least_le by simp

lemma Card_rel_cardinal_rel_eq: "Card\<^bsup>M\<^esup>(K) ==> M(K) \<Longrightarrow> |K|\<^bsup>M\<^esup> = K"
  apply (unfold Card_rel_def)
  apply (erule sym)
  done

lemma Card_relI: "[| Ord(i);  !!j. j<i \<Longrightarrow> M(j) ==> ~(j \<approx>\<^bsup>M\<^esup> i); M(i) |] ==> Card\<^bsup>M\<^esup>(i)"
  apply (unfold Card_rel_def cardinal_rel_def)
  apply (subst Least_equality)
     apply (blast intro: eqpoll_rel_refl)+
  done

lemma Card_rel_is_Ord: "Card\<^bsup>M\<^esup>(i) ==> M(i) \<Longrightarrow> Ord(i)"
  apply (unfold Card_rel_def cardinal_rel_def)
  apply (erule ssubst)
  apply (rule Ord_Least)
  done

lemma Card_rel_cardinal_rel_le: "Card\<^bsup>M\<^esup>(K) ==> M(K) \<Longrightarrow> K \<le> |K|\<^bsup>M\<^esup>"
  apply (simp (no_asm_simp) add: Card_rel_is_Ord Card_rel_cardinal_rel_eq)
  done

lemma Ord_cardinal_rel [simp,intro!]: "M(A) \<Longrightarrow> Ord(|A|\<^bsup>M\<^esup>)"
  apply (unfold cardinal_rel_def)
  apply (rule Ord_Least)
  done

lemma Card_rel_iff_initial: assumes types:"M(K)"
  shows "Card\<^bsup>M\<^esup>(K) \<longleftrightarrow> Ord(K) & (\<forall>j[M]. j<K \<longrightarrow> ~ (j \<approx>\<^bsup>M\<^esup> K))"
proof -
  { fix j
    assume K: "Card\<^bsup>M\<^esup>(K)" "M(j) \<and> j \<approx>\<^bsup>M\<^esup> K"
    assume "j < K"
    also have "... = (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> K)" using K
      by (simp add: Card_rel_def cardinal_rel_def types)
    finally have "j < (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> K)" .
    then have "False" using K
      by (best intro: less_LeastE[of "\<lambda>j. M(j) \<and> j \<approx>\<^bsup>M\<^esup> K"])
  }
  with types
  show ?thesis
    by (blast intro: Card_relI Card_rel_is_Ord)
qed

lemma lt_Card_rel_imp_lesspoll_rel: "[| Card\<^bsup>M\<^esup>(a); i<a; M(a); M(i) |] ==> i \<prec>\<^bsup>M\<^esup> a"
  apply (unfold lesspoll_rel_def)
  apply (frule Card_rel_iff_initial [THEN iffD1], assumption)
  apply (blast intro!: leI [THEN le_imp_lepoll_rel])
  done

lemma Card_rel_0: "Card\<^bsup>M\<^esup>(0)"
  apply (rule Ord_0 [THEN Card_relI])
   apply (auto elim!: ltE)
  done

lemma Card_rel_Un: "[| Card\<^bsup>M\<^esup>(K);  Card\<^bsup>M\<^esup>(L); M(K); M(L) |] ==> Card\<^bsup>M\<^esup>(K \<union> L)"
  apply (rule Ord_linear_le [of K L])
     apply (simp_all add: subset_Un_iff [THEN iffD1]  Card_rel_is_Ord le_imp_subset
      subset_Un_iff2 [THEN iffD1])
  done

lemma Card_rel_cardinal_rel [iff]: assumes types:"M(A)" shows "Card\<^bsup>M\<^esup>(|A|\<^bsup>M\<^esup>)"
  using assms
proof (unfold cardinal_rel_def)
  show "Card\<^bsup>M\<^esup>(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A)"
  proof (cases "\<exists>i[M]. Ord (i) \<and> i \<approx>\<^bsup>M\<^esup> A")
    case False thus ?thesis           \<comment> \<open>degenerate case\<close>
      using Least_0[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"] Card_rel_0
      by fastforce
  next
    case True                         \<comment> \<open>real case: \<^term>\<open>A\<close> is isomorphic to some ordinal\<close>
    then obtain i where i: "Ord(i)" "i \<approx>\<^bsup>M\<^esup> A" "M(i)" by blast
    show ?thesis
    proof (rule Card_relI [OF Ord_Least], rule notI)
      fix j
      assume j: "j < (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A)" and "M(j)"
      assume "j \<approx>\<^bsup>M\<^esup> (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A)"
      also have "... \<approx>\<^bsup>M\<^esup> A" using i LeastI[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"] by (auto)
      finally have "j \<approx>\<^bsup>M\<^esup> A"
        using Least_closed'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"] by (simp add: \<open>M(j)\<close> types)
      thus False
        using \<open>M(j)\<close> by (blast intro:less_LeastE [OF _ j])
    qed (auto intro:Least_closed)
  qed
qed

lemma cardinal_rel_eq_lemma:
  assumes i:"|i|\<^bsup>M\<^esup> \<le> j" and j: "j \<le> i" and types: "M(i)" "M(j)"
  shows "|j|\<^bsup>M\<^esup> = |i|\<^bsup>M\<^esup>"
proof (rule eqpoll_relI [THEN cardinal_rel_cong])
  show "j \<lesssim>\<^bsup>M\<^esup> i" by (rule le_imp_lepoll_rel [OF j]) (simp_all add:types)
next
  have Oi: "Ord(i)" using j by (rule le_Ord2)
  with types
  have "i \<approx>\<^bsup>M\<^esup> |i|\<^bsup>M\<^esup>"
    by (blast intro: Ord_cardinal_rel_eqpoll_rel eqpoll_rel_sym)
  also from types
  have "... \<lesssim>\<^bsup>M\<^esup> j"
    by (blast intro: le_imp_lepoll_rel i)
  finally show "i \<lesssim>\<^bsup>M\<^esup> j" by (simp_all add:types)
qed (simp_all add:types)

lemma cardinal_rel_mono:
  assumes ij: "i \<le> j" and types:"M(i)" "M(j)" shows "|i|\<^bsup>M\<^esup> \<le> |j|\<^bsup>M\<^esup>"
  using Ord_cardinal_rel [OF \<open>M(i)\<close>] Ord_cardinal_rel [OF \<open>M(j)\<close>]
proof (cases rule: Ord_linear_le)
  case le then show ?thesis .
next
  case ge
  have i: "Ord(i)" using ij
    by (simp add: lt_Ord)
  have ci: "|i|\<^bsup>M\<^esup> \<le> j"
    by (blast intro: Ord_cardinal_rel_le ij le_trans i types)
  have "|i|\<^bsup>M\<^esup> = ||i|\<^bsup>M\<^esup>|\<^bsup>M\<^esup>"
    by (auto simp add: Ord_cardinal_rel_idem i types)
  also have "... = |j|\<^bsup>M\<^esup>"
    by (rule cardinal_rel_eq_lemma [OF ge ci]) (simp_all add:types)
  finally have "|i|\<^bsup>M\<^esup> = |j|\<^bsup>M\<^esup>" .
  thus ?thesis by (simp add:types)
qed

lemma cardinal_rel_lt_imp_lt: "[| |i|\<^bsup>M\<^esup> < |j|\<^bsup>M\<^esup>;  Ord(i);  Ord(j); M(i); M(j) |] ==> i < j"
  apply (rule Ord_linear2 [of i j], assumption+)
  apply (erule lt_trans2 [THEN lt_irrefl])
  apply (erule cardinal_rel_mono, assumption+)
  done

lemma Card_rel_lt_imp_lt: "[| |i|\<^bsup>M\<^esup> < K;  Ord(i);  Card\<^bsup>M\<^esup>(K); M(i); M(K)|] ==> i < K"
  by (simp (no_asm_simp) add: cardinal_rel_lt_imp_lt Card_rel_is_Ord Card_rel_cardinal_rel_eq)

lemma Card_rel_lt_iff: "[| Ord(i);  Card\<^bsup>M\<^esup>(K); M(i); M(K) |] ==> (|i|\<^bsup>M\<^esup> < K) \<longleftrightarrow> (i < K)"
  by (blast intro: Card_rel_lt_imp_lt Ord_cardinal_rel_le [THEN lt_trans1])

lemma Card_rel_le_iff: "[| Ord(i);  Card\<^bsup>M\<^esup>(K); M(i); M(K) |] ==> (K \<le> |i|\<^bsup>M\<^esup>) \<longleftrightarrow> (K \<le> i)"
  by (simp add: Card_rel_lt_iff Card_rel_is_Ord not_lt_iff_le [THEN iff_sym])

lemma well_ord_lepoll_rel_imp_cardinal_rel_le:
  assumes wB: "well_ord(B,r)" and AB: "A \<lesssim>\<^bsup>M\<^esup> B"
    and
    types: "M(B)" "M(r)" "M(A)"
  shows "|A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
  using Ord_cardinal_rel [OF \<open>M(A)\<close>] Ord_cardinal_rel [OF \<open>M(B)\<close>]
proof (cases rule: Ord_linear_le)
  case le thus ?thesis .
next
  case ge
  from lepoll_rel_well_ord [OF AB wB]
  obtain s where s: "well_ord(A, s)" "M(s)" by (blast intro:types)
  have "B \<approx>\<^bsup>M\<^esup> |B|\<^bsup>M\<^esup>" by (blast intro: wB eqpoll_rel_sym well_ord_cardinal_rel_eqpoll_rel types)
  also have "... \<lesssim>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>" by (rule le_imp_lepoll_rel [OF ge]) (simp_all add:types)
  also have "... \<approx>\<^bsup>M\<^esup> A" by (rule well_ord_cardinal_rel_eqpoll_rel [OF s(1) _ s(2)]) (simp_all add:types)
  finally have "B \<lesssim>\<^bsup>M\<^esup> A" by (simp_all add:types)
  hence "A \<approx>\<^bsup>M\<^esup> B" by (blast intro: eqpoll_relI AB types)
  hence "|A|\<^bsup>M\<^esup> = |B|\<^bsup>M\<^esup>" by (rule cardinal_rel_cong) (simp_all add:types)
  thus ?thesis by (simp_all add:types)
qed

lemma lepoll_rel_cardinal_rel_le: "[| A \<lesssim>\<^bsup>M\<^esup> i; Ord(i); M(A); M(i) |] ==> |A|\<^bsup>M\<^esup> \<le> i"
  using Memrel_closed
  apply (rule_tac le_trans)
   apply (erule well_ord_Memrel [THEN well_ord_lepoll_rel_imp_cardinal_rel_le], assumption+)
  apply (erule Ord_cardinal_rel_le, assumption)
  done

lemma lepoll_rel_Ord_imp_eqpoll_rel: "[| A \<lesssim>\<^bsup>M\<^esup> i; Ord(i); M(A); M(i) |] ==> |A|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> A"
  by (blast intro: lepoll_rel_cardinal_rel_le well_ord_Memrel well_ord_cardinal_rel_eqpoll_rel dest!: lepoll_rel_well_ord)

lemma lesspoll_rel_imp_eqpoll_rel: "[| A \<prec>\<^bsup>M\<^esup> i; Ord(i); M(A); M(i) |] ==> |A|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> A"
  using lepoll_rel_Ord_imp_eqpoll_rel[OF lesspoll_rel_imp_lepoll_rel] .

lemma lesspoll_cardinal_lt_rel:
  shows "[| A \<prec>\<^bsup>M\<^esup> i; Ord(i); M(i); M(A) |] ==> |A|\<^bsup>M\<^esup> < i"
proof -
  assume assms:"A \<prec>\<^bsup>M\<^esup> i" \<open>Ord(i)\<close> \<open>M(i)\<close> \<open>M(A)\<close>
  then
  have A:"Ord(|A|\<^bsup>M\<^esup>)" "|A|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> A" "M(|A|\<^bsup>M\<^esup>)"
    using Ord_cardinal_rel lesspoll_rel_imp_eqpoll_rel
    by simp_all
  with assms
  have "|A|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> i"
    using eq_lesspoll_rel_trans by auto
  consider "|A|\<^bsup>M\<^esup>\<in>i" | "|A|\<^bsup>M\<^esup>=i" | "i\<in>|A|\<^bsup>M\<^esup>"
    using Ord_linear[OF \<open>Ord(i)\<close> \<open>Ord(|A|\<^bsup>M\<^esup>)\<close>] by auto
  then
  have "|A|\<^bsup>M\<^esup> < i"
  proof(cases)
    case 1
    then show ?thesis using ltI \<open>Ord(i)\<close> by simp
  next
    case 2
    with \<open>|A|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> i\<close> \<open>M(i)\<close>
    show ?thesis using lesspoll_rel_irrefl by simp
  next
    case 3
    with \<open>Ord(|A|\<^bsup>M\<^esup>)\<close>
    have "i<|A|\<^bsup>M\<^esup>" using ltI by simp
    with \<open>M(A)\<close> A \<open>M(i)\<close>
    have "i \<prec>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
      using lt_Card_rel_imp_lesspoll_rel Card_rel_cardinal_rel by simp
    with \<open>M(|A|\<^bsup>M\<^esup>)\<close> \<open>M(i)\<close>
    show ?thesis
      using lesspoll_rel_irrefl lesspoll_rel_trans[OF \<open>|A|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> i\<close> \<open>i \<prec>\<^bsup>M\<^esup> _ \<close>]
      by simp
  qed
  then show ?thesis by simp
qed

lemma cardinal_rel_subset_Ord: "[|A<=i; Ord(i); M(A); M(i)|] ==> |A|\<^bsup>M\<^esup> \<subseteq> i"
  apply (drule subset_imp_lepoll_rel [THEN lepoll_rel_cardinal_rel_le])
       apply (auto simp add: lt_def)
  apply (blast intro: Ord_trans)
  done

\<comment> \<open>The next lemma is the first with several porting issues\<close>
lemma cons_lepoll_rel_consD:
  "[| cons(u,A) \<lesssim>\<^bsup>M\<^esup> cons(v,B);  u\<notin>A;  v\<notin>B; M(u); M(A); M(v); M(B) |] ==> A \<lesssim>\<^bsup>M\<^esup> B"
  apply (simp add: def_lepoll_rel, unfold inj_def, safe)
  apply (rule_tac x = "\<lambda>x\<in>A. if f`x=v then f`u else f`x" in rexI)
   apply (rule CollectI)
    \<comment> \<open>Proving it's in the function space \<^term>\<open>A\<rightarrow>B\<close>\<close>
    apply (rule if_type [THEN lam_type])
     apply (blast dest: apply_funtype)
    apply (blast elim!: mem_irrefl dest: apply_funtype)
    \<comment> \<open>Proving it's injective\<close>
   apply (auto simp add:transM[of _ A])
  using lam_replacement_iff_lam_closed  lam_if_then_apply_replacement
  by simp

lemma cons_eqpoll_rel_consD: "[| cons(u,A) \<approx>\<^bsup>M\<^esup> cons(v,B);  u\<notin>A;  v\<notin>B; M(u); M(A); M(v); M(B) |] ==> A \<approx>\<^bsup>M\<^esup> B"
  apply (simp add: eqpoll_rel_iff)
  apply (blast intro: cons_lepoll_rel_consD)
  done

lemma succ_lepoll_rel_succD: "succ(m) \<lesssim>\<^bsup>M\<^esup> succ(n) \<Longrightarrow> M(m) \<Longrightarrow> M(n) ==> m \<lesssim>\<^bsup>M\<^esup> n"
  apply (unfold succ_def)
  apply (erule cons_lepoll_rel_consD)
       apply (rule mem_not_refl)+
     apply assumption+
  done

lemma nat_lepoll_rel_imp_le:
  "m \<in> nat ==> n \<in> nat \<Longrightarrow> m \<lesssim>\<^bsup>M\<^esup> n \<Longrightarrow> M(m) \<Longrightarrow> M(n) \<Longrightarrow> m \<le> n"
proof (induct m arbitrary: n rule: nat_induct)
  case 0 thus ?case by (blast intro!: nat_0_le)
next
  case (succ m)
  show ?case  using \<open>n \<in> nat\<close>
  proof (cases rule: natE)
    case 0 thus ?thesis using succ
      by (simp add: def_lepoll_rel inj_def)
  next
    case (succ n') thus ?thesis using succ.hyps \<open> succ(m) \<lesssim>\<^bsup>M\<^esup> n\<close>
      by (blast dest!: succ_lepoll_rel_succD)
  qed
qed

lemma nat_eqpoll_rel_iff: "[| m \<in> nat; n \<in> nat; M(m); M(n) |] ==> m \<approx>\<^bsup>M\<^esup> n \<longleftrightarrow> m = n"
  apply (rule iffI)
   apply (blast intro: nat_lepoll_rel_imp_le le_anti_sym elim!: eqpoll_relE)
  apply (simp add: eqpoll_rel_refl)
  done

lemma nat_into_Card_rel:
  assumes n: "n \<in> nat" and types: "M(n)" shows "Card\<^bsup>M\<^esup>(n)"
  using types
  apply (subst Card_rel_def)
proof (unfold cardinal_rel_def, rule sym)
  have "Ord(n)" using n  by auto
  moreover
  { fix i
    assume "i < n" "M(i)" "i \<approx>\<^bsup>M\<^esup> n"
    hence False using n
      by (auto simp add: lt_nat_in_nat [THEN nat_eqpoll_rel_iff] types)
  }
  ultimately show "(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> n) = n" by (auto intro!: Least_equality types eqpoll_rel_refl)
qed

lemmas cardinal_rel_0 = nat_0I [THEN nat_into_Card_rel, THEN Card_rel_cardinal_rel_eq, simplified, iff]
lemmas cardinal_rel_1 = nat_1I [THEN nat_into_Card_rel, THEN Card_rel_cardinal_rel_eq, simplified, iff]

lemma succ_lepoll_rel_natE: "[| succ(n) \<lesssim>\<^bsup>M\<^esup> n;  n \<in> nat |] ==> P"
  by (rule nat_lepoll_rel_imp_le [THEN lt_irrefl], auto)

lemma nat_lepoll_rel_imp_ex_eqpoll_rel_n:
  "[| n \<in> nat;  nat \<lesssim>\<^bsup>M\<^esup> X ; M(n); M(X)|] ==> \<exists>Y[M]. Y \<subseteq> X & n \<approx>\<^bsup>M\<^esup> Y"
  apply (simp add: def_lepoll_rel def_eqpoll_rel)
  apply (fast del: subsetI subsetCE
      intro!: subset_SIs
      dest!: Ord_nat [THEN [2] OrdmemD, THEN [2] restrict_inj]
      elim!: restrict_bij
      inj_is_fun [THEN fun_is_rel, THEN image_subset])
  done

lemma lepoll_rel_succ: "M(i) \<Longrightarrow> i \<lesssim>\<^bsup>M\<^esup> succ(i)"
  by (blast intro: subset_imp_lepoll_rel)

lemma lepoll_rel_imp_lesspoll_rel_succ:
  assumes A: "A \<lesssim>\<^bsup>M\<^esup> m" and m: "m \<in> nat"
    and types: "M(A)" "M(m)"
  shows "A \<prec>\<^bsup>M\<^esup> succ(m)"
proof -
  { assume "A \<approx>\<^bsup>M\<^esup> succ(m)"
    hence "succ(m) \<approx>\<^bsup>M\<^esup> A" by (rule eqpoll_rel_sym) (auto simp add:types)
    also have "... \<lesssim>\<^bsup>M\<^esup> m" by (rule A)
    finally have "succ(m) \<lesssim>\<^bsup>M\<^esup> m" by (auto simp add:types)
    hence False by (rule succ_lepoll_rel_natE) (rule m) }
  moreover have "A \<lesssim>\<^bsup>M\<^esup> succ(m)" by (blast intro: lepoll_rel_trans A lepoll_rel_succ types)
  ultimately show ?thesis by (auto simp add: types lesspoll_rel_def)
qed

lemma lesspoll_rel_succ_imp_lepoll_rel:
  "[| A \<prec>\<^bsup>M\<^esup> succ(m); m \<in> nat; M(A); M(m) |] ==> A \<lesssim>\<^bsup>M\<^esup> m"
proof -
  {
    assume "m \<in> nat" "M(A)" "M(m)" "A \<lesssim>\<^bsup>M\<^esup> succ(m)"
      "\<forall>f\<in>inj\<^bsup>M\<^esup>(A, succ(m)). f \<notin> surj\<^bsup>M\<^esup>(A, succ(m))"
    moreover from this
    obtain f where "M(f)" "f\<in>inj\<^bsup>M\<^esup>(A,succ(m))"
      using def_lepoll_rel by auto
    moreover from calculation
    have "f \<notin> surj\<^bsup>M\<^esup>(A, succ(m))" by simp
    ultimately
    have "\<exists>f[M]. f \<in> inj\<^bsup>M\<^esup>(A, m)"
      using inj_rel_not_surj_rel_succ by auto
  }
  from this
  show "\<lbrakk> A \<prec>\<^bsup>M\<^esup> succ(m); m \<in> nat; M(A); M(m) \<rbrakk> \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> m"
    unfolding lepoll_rel_def eqpoll_rel_def bij_rel_def lesspoll_rel_def
    by (simp del:mem_inj_abs)
qed

lemma lesspoll_rel_succ_iff: "m \<in> nat \<Longrightarrow> M(A) ==> A \<prec>\<^bsup>M\<^esup> succ(m) \<longleftrightarrow> A \<lesssim>\<^bsup>M\<^esup> m"
  by (blast intro!: lepoll_rel_imp_lesspoll_rel_succ lesspoll_rel_succ_imp_lepoll_rel)

lemma lepoll_rel_succ_disj: "[| A \<lesssim>\<^bsup>M\<^esup> succ(m);  m \<in> nat; M(A) ; M(m)|] ==> A \<lesssim>\<^bsup>M\<^esup> m | A \<approx>\<^bsup>M\<^esup> succ(m)"
  apply (rule disjCI)
  apply (rule lesspoll_rel_succ_imp_lepoll_rel)
     prefer 2 apply assumption
    apply (simp (no_asm_simp) add: lesspoll_rel_def, assumption+)
  done

lemma lesspoll_rel_cardinal_rel_lt: "[| A \<prec>\<^bsup>M\<^esup> i; Ord(i); M(A); M(i) |] ==> |A|\<^bsup>M\<^esup> < i"
  apply (unfold lesspoll_rel_def, clarify)
  apply (frule lepoll_rel_cardinal_rel_le, assumption+) \<comment> \<open>because of types\<close>
  apply (blast intro: well_ord_Memrel well_ord_cardinal_rel_eqpoll_rel [THEN eqpoll_rel_sym]
      dest: lepoll_rel_well_ord  elim!: leE)
  done

lemma lt_not_lepoll_rel:
  assumes n: "n<i" "n \<in> nat"
    and types:"M(n)" "M(i)" shows "~ i \<lesssim>\<^bsup>M\<^esup> n"
proof -
  { assume i: "i \<lesssim>\<^bsup>M\<^esup> n"
    have "succ(n) \<lesssim>\<^bsup>M\<^esup> i" using n
      by (elim ltE, blast intro: Ord_succ_subsetI [THEN subset_imp_lepoll_rel] types)
    also have "... \<lesssim>\<^bsup>M\<^esup> n" by (rule i)
    finally have "succ(n) \<lesssim>\<^bsup>M\<^esup> n" by (simp add:types)
    hence False  by (rule succ_lepoll_rel_natE) (rule n) }
  thus ?thesis by auto
qed

text\<open>A slightly weaker version of \<open>nat_eqpoll_rel_iff\<close>\<close>
lemma Ord_nat_eqpoll_rel_iff:
  assumes i: "Ord(i)" and n: "n \<in> nat"
    and types: "M(i)" "M(n)"
  shows "i \<approx>\<^bsup>M\<^esup> n \<longleftrightarrow> i=n"
  using i nat_into_Ord [OF n]
proof (cases rule: Ord_linear_lt)
  case lt
  hence  "i \<in> nat" by (rule lt_nat_in_nat) (rule n)
  thus ?thesis by (simp add: nat_eqpoll_rel_iff n types)
next
  case eq
  thus ?thesis by (simp add: eqpoll_rel_refl types)
next
  case gt
  hence  "~ i \<lesssim>\<^bsup>M\<^esup> n" using n  by (rule lt_not_lepoll_rel) (simp_all add: types)
  hence  "~ i \<approx>\<^bsup>M\<^esup> n" using n  by (blast intro: eqpoll_rel_imp_lepoll_rel types)
  moreover have "i \<noteq> n" using \<open>n<i\<close> by auto
  ultimately show ?thesis by blast
qed

lemma Card_rel_nat: "Card\<^bsup>M\<^esup>(nat)"
proof -
  { fix i
    assume i: "i < nat" "i \<approx>\<^bsup>M\<^esup> nat" "M(i)"
    hence "~ nat \<lesssim>\<^bsup>M\<^esup> i"
      by (simp add: lt_def lt_not_lepoll_rel)
    hence False using i
      by (simp add: eqpoll_rel_iff)
  }
  hence "(\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> nat) = nat" by (blast intro: Least_equality eqpoll_rel_refl)
  thus ?thesis
    by (auto simp add: Card_rel_def cardinal_rel_def)
qed

lemma nat_le_cardinal_rel: "nat \<le> i \<Longrightarrow> M(i) ==> nat \<le> |i|\<^bsup>M\<^esup>"
  apply (rule Card_rel_nat [THEN Card_rel_cardinal_rel_eq, THEN subst], simp_all)
  apply (erule cardinal_rel_mono, simp_all)
  done

lemma n_lesspoll_rel_nat: "n \<in> nat ==> n \<prec>\<^bsup>M\<^esup> nat"
  by (blast intro: Card_rel_nat ltI lt_Card_rel_imp_lesspoll_rel)

lemma cons_lepoll_rel_cong:
  "[| A \<lesssim>\<^bsup>M\<^esup> B;  b \<notin> B; M(A); M(B); M(b); M(a) |] ==> cons(a,A) \<lesssim>\<^bsup>M\<^esup> cons(b,B)"
  apply (subst (asm) def_lepoll_rel, simp_all, subst def_lepoll_rel, simp_all, safe)
  apply (rule_tac x = "\<lambda>y\<in>cons (a,A) . if y=a then b else f`y" in rexI)
   apply (rule_tac d = "%z. if z \<in> B then converse (f) `z else a" in lam_injective)
    apply (safe elim!: consE')
      apply simp_all
    apply (blast intro: inj_is_fun [THEN apply_type])+
  apply (auto intro:lam_closed lam_if_then_replacement simp add:transM[of _ A])
  done

lemma cons_eqpoll_rel_cong:
  "[| A \<approx>\<^bsup>M\<^esup> B;  a \<notin> A;  b \<notin> B;  M(A); M(B); M(a) ; M(b) |] ==> cons(a,A) \<approx>\<^bsup>M\<^esup> cons(b,B)"
  by (simp add: eqpoll_rel_iff cons_lepoll_rel_cong)

lemma cons_lepoll_rel_cons_iff:
  "[| a \<notin> A;  b \<notin> B; M(a); M(A); M(b); M(B) |] ==> cons(a,A) \<lesssim>\<^bsup>M\<^esup> cons(b,B)  \<longleftrightarrow>  A \<lesssim>\<^bsup>M\<^esup> B"
  by (blast intro: cons_lepoll_rel_cong cons_lepoll_rel_consD)

lemma cons_eqpoll_rel_cons_iff:
  "[| a \<notin> A;  b \<notin> B; M(a); M(A); M(b); M(B) |] ==> cons(a,A) \<approx>\<^bsup>M\<^esup> cons(b,B)  \<longleftrightarrow>  A \<approx>\<^bsup>M\<^esup> B"
  by (blast intro: cons_eqpoll_rel_cong cons_eqpoll_rel_consD)

lemma singleton_eqpoll_rel_1: "M(a) \<Longrightarrow> {a} \<approx>\<^bsup>M\<^esup> 1"
  apply (unfold succ_def)
  apply (blast intro!: eqpoll_rel_refl [THEN cons_eqpoll_rel_cong])
  done

lemma cardinal_rel_singleton: "M(a) \<Longrightarrow> |{a}|\<^bsup>M\<^esup> = 1"
  apply (rule singleton_eqpoll_rel_1 [THEN cardinal_rel_cong, THEN trans])
     apply (simp (no_asm) add: nat_into_Card_rel [THEN Card_rel_cardinal_rel_eq])
    apply auto
  done

lemma not_0_is_lepoll_rel_1: "A \<noteq> 0 ==> M(A) \<Longrightarrow> 1 \<lesssim>\<^bsup>M\<^esup> A"
  apply (erule not_emptyE)
  apply (rule_tac a = "cons (x, A-{x}) " in subst)
   apply (rule_tac [2] a = "cons(0,0)" and P= "%y. y \<lesssim>\<^bsup>M\<^esup> cons (x, A-{x})" in subst)
    apply auto
proof -
  fix x
  assume "M(A)"
  then
  show "x \<in> A \<Longrightarrow> {0} \<lesssim>\<^bsup>M\<^esup> cons(x, A - {x})"
    by (auto intro: cons_lepoll_rel_cong transM[OF _ \<open>M(A)\<close>] subset_imp_lepoll_rel)
qed

lemma succ_eqpoll_rel_cong: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) ==> succ(A) \<approx>\<^bsup>M\<^esup> succ(B)"
  apply (unfold succ_def)
  apply (simp add: cons_eqpoll_rel_cong mem_not_refl)
  done

text\<open>The next result was not straightforward to port, and even a
different statement was needed.\<close>

lemma sum_bij_rel:
  "[| f \<in> bij\<^bsup>M\<^esup>(A,C); g \<in> bij\<^bsup>M\<^esup>(B,D); M(f); M(A); M(C); M(g); M(B); M(D)|]
      ==> (\<lambda>z\<in>A+B. case(%x. Inl(f`x), %y. Inr(g`y), z)) \<in> bij\<^bsup>M\<^esup>(A+B, C+D)"
proof -
  assume asm:"f \<in> bij\<^bsup>M\<^esup>(A,C)" "g \<in> bij\<^bsup>M\<^esup>(B,D)" "M(f)" "M(A)" "M(C)" "M(g)" "M(B)" "M(D)"
  then
  have "M(\<lambda>z\<in>A+B. case(%x. Inl(f`x), %y. Inr(g`y), z))"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>]
    by (auto intro:case_replacement4[THEN lam_closed])
  with asm
  show ?thesis
    apply simp
    apply (rule_tac d = "case (%x. Inl (converse(f)`x), %y. Inr(converse(g)`y))"
        in lam_bijective)
       apply (typecheck add: bij_is_inj inj_is_fun)
     apply (auto simp add: left_inverse_bij right_inverse_bij)
    done
qed

lemma sum_bij_rel':
  assumes "f \<in> bij\<^bsup>M\<^esup>(A,C)" "g \<in> bij\<^bsup>M\<^esup>(B,D)" "M(f)"
    "M(A)" "M(C)" "M(g)" "M(B)" "M(D)"
  shows
    "(\<lambda>z\<in>A+B. case(\<lambda>x. Inl(f`x), \<lambda>y. Inr(g`y), z)) \<in> bij(A+B, C+D)"
    "M(\<lambda>z\<in>A+B. case(\<lambda>x. Inl(f`x), \<lambda>y. Inr(g`y), z))"
proof -
  from assms
  show "M(\<lambda>z\<in>A+B. case(\<lambda>x. Inl(f`x), \<lambda>y. Inr(g`y), z))"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>]
    by (auto intro:case_replacement4[THEN lam_closed])
  with assms
  show "(\<lambda>z\<in>A+B. case(\<lambda>x. Inl(f`x), \<lambda>y. Inr(g`y), z)) \<in> bij(A+B, C+D)"
    apply simp
    apply (rule_tac d = "case (%x. Inl (converse(f)`x), %y. Inr(converse(g)`y))"
        in lam_bijective)
       apply (typecheck add: bij_is_inj inj_is_fun)
     apply (auto simp add: left_inverse_bij right_inverse_bij)
    done
qed

lemma sum_eqpoll_rel_cong:
  assumes "A \<approx>\<^bsup>M\<^esup> C" "B \<approx>\<^bsup>M\<^esup> D" "M(A)" "M(C)" "M(B)" "M(D)"
  shows "A+B \<approx>\<^bsup>M\<^esup> C+D"
  using assms
proof (simp add: def_eqpoll_rel, safe, rename_tac g)
  fix f g
  assume  "M(f)" "f \<in> bij(A, C)" "M(g)" "g \<in> bij(B, D)"
  with assms
  obtain h where "h\<in>bij(A+B, C+D)" "M(h)"
    using sum_bij_rel'[of f A C g B D] by simp
  then
  show "\<exists>f[M]. f \<in> bij(A + B, C + D)"
    by auto
qed

lemma prod_bij_rel':
  assumes "f \<in> bij\<^bsup>M\<^esup>(A,C)" "g \<in> bij\<^bsup>M\<^esup>(B,D)" "M(f)"
    "M(A)" "M(C)" "M(g)" "M(B)" "M(D)"
  shows
    "(\<lambda><x,y>\<in>A*B. <f`x, g`y>) \<in> bij(A*B, C*D)"
    "M(\<lambda><x,y>\<in>A*B. <f`x, g`y>)"
proof -
  from assms
  show "M((\<lambda><x,y>\<in>A*B. <f`x, g`y>))"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>]
      transM[OF _ cartprod_closed, of _ A B]
    by (auto intro:prod_fun_replacement[THEN lam_closed, of f g "A\<times>B"])
  with assms
  show "(\<lambda><x,y>\<in>A*B. <f`x, g`y>) \<in> bij(A*B, C*D)"
    apply simp
    apply (rule_tac d = "%<x,y>. <converse (f) `x, converse (g) `y>"
        in lam_bijective)
       apply (typecheck add: bij_is_inj inj_is_fun)
     apply (auto simp add: left_inverse_bij right_inverse_bij)
    done
qed

lemma prod_eqpoll_rel_cong:
  assumes "A \<approx>\<^bsup>M\<^esup> C" "B \<approx>\<^bsup>M\<^esup> D" "M(A)" "M(C)" "M(B)" "M(D)"
  shows "A\<times>B \<approx>\<^bsup>M\<^esup> C\<times>D"
  using assms
proof (simp add: def_eqpoll_rel, safe, rename_tac g)
  fix f g
  assume  "M(f)" "f \<in> bij(A, C)" "M(g)" "g \<in> bij(B, D)"
  with assms
  obtain h where "h\<in>bij(A\<times>B, C\<times>D)" "M(h)"
    using prod_bij_rel'[of f A C g B D] by simp
  then
  show "\<exists>f[M]. f \<in> bij(A \<times> B, C \<times> D)"
    by auto
qed

lemma inj_rel_disjoint_eqpoll_rel:
  "[| f \<in> inj\<^bsup>M\<^esup>(A,B);  A \<inter> B = 0;M(f); M(A);M(B) |] ==> A \<union> (B - range(f)) \<approx>\<^bsup>M\<^esup> B"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule_tac c = "%x. if x \<in> A then f`x else x"
      and d = "%y. if y \<in> range (f) then converse (f) `y else y"
      in lam_bijective)
      apply (blast intro!: if_type inj_is_fun [THEN apply_type])
     apply (simp (no_asm_simp) add: inj_converse_fun [THEN apply_funtype])
    apply (safe elim!: UnE')
     apply (simp_all add: inj_is_fun [THEN apply_rangeI])
   apply (blast intro: inj_converse_fun [THEN apply_type])
proof -
  assume "f \<in> inj(A, B)" "A \<inter> B = 0" "M(f)" "M(A)" "M(B)"
  then
  show "M(\<lambda>x\<in>A \<union> (B - range(f)). if x \<in> A then f ` x else x)"
    using  transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>]
      lam_replacement_iff_lam_closed lam_if_then_replacement2
    by auto
qed

lemma Diff_sing_lepoll_rel:
  "[| a \<in> A;  A \<lesssim>\<^bsup>M\<^esup> succ(n); M(a); M(A); M(n) |] ==> A - {a} \<lesssim>\<^bsup>M\<^esup> n"
  apply (unfold succ_def)
  apply (rule cons_lepoll_rel_consD)
        apply (rule_tac [3] mem_not_refl)
       apply (erule cons_Diff [THEN ssubst], simp_all)
  done

lemma lepoll_rel_Diff_sing:
  assumes A: "succ(n) \<lesssim>\<^bsup>M\<^esup> A"
    and types: "M(n)" "M(A)" "M(a)"
  shows "n \<lesssim>\<^bsup>M\<^esup> A - {a}"
proof -
  have "cons(n,n) \<lesssim>\<^bsup>M\<^esup> A" using A
    by (unfold succ_def)
  also from types
  have "... \<lesssim>\<^bsup>M\<^esup> cons(a, A-{a})"
    by (blast intro: subset_imp_lepoll_rel)
  finally have "cons(n,n) \<lesssim>\<^bsup>M\<^esup> cons(a, A-{a})" by (simp_all add:types)
  with types
  show ?thesis
    by (blast intro: cons_lepoll_rel_consD mem_irrefl)
qed

lemma Diff_sing_eqpoll_rel: "[| a \<in> A; A \<approx>\<^bsup>M\<^esup> succ(n); M(a); M(A); M(n) |] ==> A - {a} \<approx>\<^bsup>M\<^esup> n"
  by (blast intro!: eqpoll_relI
      elim!: eqpoll_relE
      intro: Diff_sing_lepoll_rel lepoll_rel_Diff_sing)

lemma lepoll_rel_1_is_sing: "[| A \<lesssim>\<^bsup>M\<^esup> 1; a \<in> A ;M(a); M(A) |] ==> A = {a}"
  apply (frule Diff_sing_lepoll_rel, assumption+, simp)
  apply (drule lepoll_rel_0_is_0, simp)
  apply (blast elim: equalityE)
  done

lemma Un_lepoll_rel_sum: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<union> B \<lesssim>\<^bsup>M\<^esup> A+B"
  apply (simp add: def_lepoll_rel)
  apply (rule_tac x = "\<lambda>x\<in>A \<union> B. if x\<in>A then Inl (x) else Inr (x)" in rexI)
   apply (rule_tac d = "%z. snd (z)" in lam_injective)
    apply force
   apply (simp add: Inl_def Inr_def)
proof -
  assume "M(A)" "M(B)"
  then
  show "M(\<lambda>x\<in>A \<union> B. if x \<in> A then Inl(x) else Inr(x))"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>] if_then_Inj_replacement
    by (rule_tac lam_closed) auto
qed

lemma well_ord_Un_M:
  assumes "well_ord(X,R)" "well_ord(Y,S)"
    and types: "M(X)" "M(R)" "M(Y)" "M(S)"
  shows "\<exists>T[M]. well_ord(X \<union> Y, T)"
  using assms
  by (erule_tac well_ord_radd [THEN [3] Un_lepoll_rel_sum [THEN lepoll_rel_well_ord]])
    (auto simp add: types)

lemma disj_Un_eqpoll_rel_sum: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<inter> B = 0 \<Longrightarrow> A \<union> B \<approx>\<^bsup>M\<^esup> A + B"
  apply (simp add: def_eqpoll_rel)
  apply (rule_tac x = "\<lambda>a\<in>A \<union> B. if a \<in> A then Inl (a) else Inr (a)" in rexI)
   apply (rule_tac d = "%z. case (%x. x, %x. x, z)" in lam_bijective)
      apply auto
proof -
  assume "M(A)" "M(B)"
  then
  show "M(\<lambda>x\<in>A \<union> B. if x \<in> A then Inl(x) else Inr(x))"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>] if_then_Inj_replacement
    by (rule_tac lam_closed) auto
qed

lemma eqpoll_rel_imp_Finite_rel_iff: "A \<approx>\<^bsup>M\<^esup> B ==> M(A) \<Longrightarrow> M(B) \<Longrightarrow> Finite_rel(M,A) \<longleftrightarrow> Finite_rel(M,B)"
  apply (unfold Finite_rel_def)
  apply (blast intro: eqpoll_rel_trans eqpoll_rel_sym)
  done

\<comment> \<open>It seems reasonable to have the absoluteness of \<^term>\<open>Finite\<close> here,
and deduce the rest of the results from this.

Perhaps modularize that proof to have absoluteness of injections and
bijections of finite sets (cf. @{thm lesspoll_rel_succ_imp_lepoll_rel}.\<close>

lemma Finite_abs[simp]:
  assumes "M(A)"
  shows "Finite_rel(M,A) \<longleftrightarrow> Finite(A)"
  unfolding Finite_rel_def Finite_def
proof (simp, intro iffI)
  assume "\<exists>n\<in>nat. A \<approx>\<^bsup>M\<^esup> n"
  then
  obtain n where "A \<approx>\<^bsup>M\<^esup> n" "n\<in>nat" by blast
  with assms
  show "\<exists>n\<in>nat. A \<approx> n"
    unfolding eqpoll_def using nat_into_M by (auto simp add:def_eqpoll_rel)
next
  fix n
  assume "\<exists>n\<in>nat. A \<approx> n"
  then
  obtain n where "A \<approx> n" "n\<in>nat" by blast
  moreover from this
  obtain f where "f \<in> bij(A,n)" unfolding eqpoll_def by auto
  moreover
  note assms
  moreover from calculation
  have "converse(f) \<in> n\<rightarrow>A"  using bij_is_fun by simp
  moreover from calculation
  have "M(converse(f))" using transM[of _ "n\<rightarrow>A"] by simp
  moreover from calculation
  have "M(f)" using bij_is_fun
      fun_is_rel[of "f" A "\<lambda>_. n", THEN converse_converse]
      converse_closed[of "converse(f)"] by simp
  ultimately
  show "\<exists>n\<in>nat. A \<approx>\<^bsup>M\<^esup> n"
    by (force dest:nat_into_M simp add:def_eqpoll_rel)
qed

\<comment> \<open>From the next result, the relative versions of
@{thm Finite_Fin_lemma} and @{thm Fin_lemma} should follow\<close>

lemma lepoll_rel_nat_imp_Finite_rel:
  assumes A: "A \<lesssim>\<^bsup>M\<^esup> n" and n: "n \<in> nat"
    and types: "M(A)" "M(n)"
  shows "Finite_rel(M,A)"
proof -
  have "A \<lesssim>\<^bsup>M\<^esup> n \<Longrightarrow> Finite_rel(M,A)" using n
  proof (induct n)
    case 0
    hence "A = 0" by (rule lepoll_rel_0_is_0, simp_all add:types)
    thus ?case by simp
  next
    case (succ n)
    hence "A \<lesssim>\<^bsup>M\<^esup> n \<or> A \<approx>\<^bsup>M\<^esup> succ(n)" by (blast dest: lepoll_rel_succ_disj intro:types)
    thus ?case using succ by (auto simp add: Finite_rel_def types)
  qed
  thus ?thesis using A .
qed

lemma lesspoll_rel_nat_is_Finite_rel:
  "A \<prec>\<^bsup>M\<^esup> nat \<Longrightarrow> M(A) \<Longrightarrow> Finite_rel(M,A)"
  apply (unfold Finite_rel_def)
  apply (auto dest: ltD lesspoll_rel_cardinal_rel_lt
      lesspoll_rel_imp_eqpoll_rel [THEN eqpoll_rel_sym])
  done

lemma lepoll_rel_Finite_rel:
  assumes Y: "Y \<lesssim>\<^bsup>M\<^esup> X" and X: "Finite_rel(M,X)"
    and types:"M(Y)" "M(X)"
  shows "Finite_rel(M,Y)"
proof -
  obtain n where n: "n \<in> nat" "X \<approx>\<^bsup>M\<^esup> n" "M(n)" using X
    by (auto simp add: Finite_rel_def)
  have "Y \<lesssim>\<^bsup>M\<^esup> X"         by (rule Y)
  also have "... \<approx>\<^bsup>M\<^esup> n"  by (rule n)
  finally have "Y \<lesssim>\<^bsup>M\<^esup> n" by (simp_all add:types \<open>M(n)\<close>)
  thus ?thesis using n
    by (simp add: lepoll_rel_nat_imp_Finite_rel types \<open>M(n)\<close> del:Finite_abs)
qed

lemma succ_lepoll_rel_imp_not_empty: "succ(x) \<lesssim>\<^bsup>M\<^esup> y ==> M(x) \<Longrightarrow> M(y) \<Longrightarrow> y \<noteq> 0"
  by (fast dest!: lepoll_rel_0_is_0)

lemma eqpoll_rel_succ_imp_not_empty: "x \<approx>\<^bsup>M\<^esup> succ(n) ==> M(x) \<Longrightarrow> M(n) \<Longrightarrow> x \<noteq> 0"
  by (fast elim!: eqpoll_rel_sym [THEN eqpoll_rel_0_is_0, THEN succ_neq_0])

lemma Finite_subset_closed:
  assumes "Finite(B)" "B\<subseteq>A" "M(A)"
  shows "M(B)"
proof -
  from \<open>Finite(B)\<close> \<open>B\<subseteq>A\<close>
  show ?thesis
  proof(induct,simp)
    case (cons x D)
    with assms
    have "M(D)" "x\<in>A"
      unfolding cons_def by auto
    then
    show ?case using transM[OF _ \<open>M(A)\<close>] by simp
  qed
qed

lemma Finite_Pow_abs:
  assumes "Finite(A)" " M(A)"
  shows "Pow(A) = Pow_rel(M,A)"
  using Finite_subset_closed[OF subset_Finite] assms Pow_rel_char
  by auto

lemma Finite_Pow_rel:
  assumes "Finite(A)" "M(A)"
  shows "Finite(Pow_rel(M,A))"
  using Finite_Pow Finite_Pow_abs[symmetric] assms by simp

lemma Pow_rel_0 [simp]: "Pow_rel(M,0) = {0}"
  using Finite_Pow_abs[of 0] by simp

lemma eqpoll_rel_imp_Finite: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> Finite(A) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> Finite(B)"
proof -
  assume "A \<approx>\<^bsup>M\<^esup> B" "Finite(A)" "M(A)" "M(B)"
  then obtain f n g where "f\<in>bij(A,B)" "n\<in>nat" "g\<in>bij(A,n)"
    unfolding Finite_def eqpoll_def eqpoll_rel_def
    using bij_rel_char
    by auto
  then
  have "g O converse(f) \<in> bij(B,n)"
    using bij_converse_bij comp_bij by simp
  with \<open>n\<in>_\<close>
  show"Finite(B)"
    unfolding Finite_def eqpoll_def by auto
qed

lemma eqpoll_rel_imp_Finite_iff: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> Finite(A) \<longleftrightarrow> Finite(B)"
  using eqpoll_rel_imp_Finite eqpoll_rel_sym by force

end \<comment> \<open>\<^locale>\<open>M_cardinals\<close>\<close>

end