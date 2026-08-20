theory Mostowski_Collapse
  imports ZF
begin

section \<open>The Mostowski Collapse Theorem\<close>

text \<open>
  The Mostowski collapse theorem says that every set-sized well-founded
  extensional relation is isomorphic to membership on a transitive set.  The
  collapsing map is obtained by well-founded recursion:
  each object is sent to the set of the collapses of its predecessors.  We
  work with a set \<open>A\<close> and collapse the restriction of a relation \<open>r\<close> to
  \<open>A\<close>.  The assumptions are therefore \<open>wf[A](r)\<close> and extensionality on
  \<open>A\<close>; the final isomorphism is stated for \<open>r \<inter> A*A\<close>.
\<close>

definition extensional_on :: "[i, i] \<Rightarrow> o" where
  "extensional_on(A,r) \<equiv>
    \<forall>x\<in>A. \<forall>y\<in>A. (\<forall>z\<in>A. \<langle>z,x\<rangle> \<in> r \<longleftrightarrow> \<langle>z,y\<rangle> \<in> r) \<longrightarrow> x = y"

definition collapse :: "[i, i, i] \<Rightarrow> i" where
  "collapse(A,r,x) \<equiv>
    wfrec[A](r, x, \<lambda>y f. f `` ((r -`` {y}) \<inter> A))"

definition collapse_map :: "[i, i] \<Rightarrow> i" where
  "collapse_map(A,r) \<equiv> (\<lambda>x\<in>A. collapse(A,r,x))"

definition collapse_range :: "[i, i] \<Rightarrow> i" where
  "collapse_range(A,r) \<equiv> range(collapse_map(A,r))"

lemma collapse_unfold:
  assumes "wf[A](r)" "x \<in> A"
  shows "collapse(A,r,x) = {collapse(A,r,y). y \<in> (r -`` {x}) \<inter> A}"
  unfolding collapse_def
  using assms by (simp add: wfrec_on image_lam)

lemma collapse_memI:
  assumes "wf[A](r)" "x \<in> A" "y \<in> A" "\<langle>y,x\<rangle> \<in> r"
  shows "collapse(A,r,y) \<in> collapse(A,r,x)"
proof -
  have "y \<in> (r -`` {x}) \<inter> A"
    using assms by (simp add: vimage_singleton_iff)
  with collapse_unfold [OF assms(1,2)] show ?thesis
    by force
qed

lemma collapse_memE:
  assumes "wf[A](r)" "x \<in> A" "u \<in> collapse(A,r,x)"
  obtains y where "y \<in> A" "\<langle>y,x\<rangle> \<in> r" "u = collapse(A,r,y)"
  using assms by (auto simp: collapse_unfold vimage_singleton_iff)

lemma collapse_injective:
  assumes wf: "wf[A](r)" and ext: "extensional_on(A,r)"
    and xA: "x \<in> A" and yA: "y \<in> A"
    and eq: "collapse(A,r,x) = collapse(A,r,y)"
  shows "x = y"
proof -
  have "\<forall>y\<in>A. collapse(A,r,x) = collapse(A,r,y) \<longrightarrow> x = y"
    using wf xA
  proof (rule wf_on_induct_raw)
    fix x
    assume xA': "x \<in> A"
      and IH: "\<forall>z\<in>A. \<langle>z,x\<rangle> \<in> r \<longrightarrow>
        (\<forall>y\<in>A. collapse(A,r,z) = collapse(A,r,y) \<longrightarrow> z = y)"
    show "\<forall>y\<in>A. collapse(A,r,x) = collapse(A,r,y) \<longrightarrow> x = y"
    proof
      fix y
      assume yA': "y \<in> A"
      show "collapse(A,r,x) = collapse(A,r,y) \<longrightarrow> x = y"
      proof
        assume eqxy: "collapse(A,r,x) = collapse(A,r,y)"
        have pred_eq: "\<forall>z\<in>A. \<langle>z,x\<rangle> \<in> r \<longleftrightarrow> \<langle>z,y\<rangle> \<in> r"
        proof
          fix z
          assume zA: "z \<in> A"
          show "\<langle>z,x\<rangle> \<in> r \<longleftrightarrow> \<langle>z,y\<rangle> \<in> r"
          proof
            assume zx: "\<langle>z,x\<rangle> \<in> r"
            have "collapse(A,r,z) \<in> collapse(A,r,x)"
              using wf xA' zA zx by (rule collapse_memI)
            then have "collapse(A,r,z) \<in> collapse(A,r,y)"
              using eqxy by simp
            then obtain w where wA: "w \<in> A" and wy: "\<langle>w,y\<rangle> \<in> r"
              and zw: "collapse(A,r,z) = collapse(A,r,w)"
              by (rule collapse_memE [OF wf yA'])
            then show "\<langle>z,y\<rangle> \<in> r"
              using IH zA zx wA zw by force
          next
            assume zy: "\<langle>z,y\<rangle> \<in> r"
            have "collapse(A,r,z) \<in> collapse(A,r,y)"
              using wf yA' zA zy by (rule collapse_memI)
            then have "collapse(A,r,z) \<in> collapse(A,r,x)"
              using eqxy by simp
            then obtain w where wA: "w \<in> A" and wx: "\<langle>w,x\<rangle> \<in> r"
              and zw: "collapse(A,r,z) = collapse(A,r,w)"
              by (rule collapse_memE [OF wf xA'])
            then show "\<langle>z,x\<rangle> \<in> r"
              using IH zA wx wA zw by force
          qed
        qed
        then show "x = y"
          using ext xA' yA' by (auto simp: extensional_on_def)
      qed
    qed
  qed
  then show ?thesis
    using yA eq by simp
qed

lemma collapse_map_type:
  "collapse_map(A,r) \<in> A \<rightarrow> collapse_range(A,r)"
  unfolding collapse_map_def collapse_range_def 
  by (intro lam_type rangeI) (auto simp: lam_def)

lemma collapse_map_apply [simp]:
  "x \<in> A \<Longrightarrow> collapse_map(A,r) ` x = collapse(A,r,x)"
  by (simp add: collapse_map_def)

lemma collapse_map_inj:
  assumes "wf[A](r)" "extensional_on(A,r)"
  shows "collapse_map(A,r) \<in> inj(A, collapse_range(A,r))"
  unfolding inj_def
proof
  show "collapse_map(A,r) \<in> A \<rightarrow> collapse_range(A,r)"
    by (rule collapse_map_type)
next
  show "\<forall>w\<in>A. \<forall>x\<in>A. collapse_map(A,r)`w = collapse_map(A,r)`x \<longrightarrow> w = x"
  proof (intro strip)
    fix w x
    assume wA: "w \<in> A" and xA: "x \<in> A" and eq: "collapse_map(A,r)`w = collapse_map(A,r)`x"
    then have "collapse(A,r,w) = collapse(A,r,x)"
      by simp
    then show "w = x"
      by (rule collapse_injective [OF assms wA xA])
  qed
qed

lemma collapse_map_bij:
  assumes "wf[A](r)" "extensional_on(A,r)"
  shows "collapse_map(A,r) \<in> bij(A, collapse_range(A,r))"
  using collapse_map_inj [OF assms]
  unfolding collapse_range_def
  by (rule inj_bij_range)

lemma collapse_range_iff:
  "u \<in> collapse_range(A,r) \<longleftrightarrow> (\<exists>x \<in> A. u = collapse(A,r,x))"
  unfolding collapse_range_def collapse_map_def range_def lam_def
  by blast

lemma collapse_range_transitive:
  assumes wf: "wf[A](r)"
  shows "Transset(collapse_range(A,r))"
  unfolding Transset_def
  by (force simp: collapse_range_iff elim: collapse_memE [OF wf])

lemma collapse_mem_iff:
  assumes wf: "wf[A](r)" and ext: "extensional_on(A,r)"
    and xA: "x \<in> A" and yA: "y \<in> A"
  shows "collapse(A,r,x) \<in> collapse(A,r,y) \<longleftrightarrow> \<langle>x,y\<rangle> \<in> r"
proof
  assume "collapse(A,r,x) \<in> collapse(A,r,y)"
  then obtain z where zA: "z \<in> A" and zy: "\<langle>z,y\<rangle> \<in> r"
    and xz: "collapse(A,r,x) = collapse(A,r,z)"
    by (rule collapse_memE [OF wf yA])
  have "x = z"
    using collapse_injective [OF wf ext xA zA xz] .
  then show "\<langle>x,y\<rangle> \<in> r"
    using zy by simp
next
  assume "\<langle>x,y\<rangle> \<in> r"
  then show "collapse(A,r,x) \<in> collapse(A,r,y)"
    by (rule collapse_memI [OF wf yA xA])
qed

lemma collapse_ord_iso:
  assumes wf: "wf[A](r)" and ext: "extensional_on(A,r)"
  shows "collapse_map(A,r) \<in>
    ord_iso(A, r \<inter> A*A, collapse_range(A,r), Memrel(collapse_range(A,r)))"
proof (rule ord_isoI)
  show "collapse_map(A,r) \<in> bij(A, collapse_range(A,r))"
    using wf ext by (rule collapse_map_bij)
next
  fix x y
  assume xA: "x \<in> A" and yA: "y \<in> A"
  show "\<langle>x,y\<rangle> \<in> r \<inter> A*A \<longleftrightarrow>
      \<langle>collapse_map(A,r)`x, collapse_map(A,r)`y\<rangle> \<in> Memrel(collapse_range(A,r))"
    using xA yA collapse_mem_iff [OF wf ext xA yA]
    by (auto simp: collapse_range_iff)
qed

theorem mostowski_collapse:
  assumes "wf[A](r)" "extensional_on(A,r)"
  shows "Transset(collapse_range(A,r)) \<and>
    collapse_map(A,r) \<in>
      ord_iso(A, r \<inter> A*A, collapse_range(A,r), Memrel(collapse_range(A,r)))"
  using assms
  by (simp add: collapse_range_transitive collapse_ord_iso)

theorem mostowski_collapse_exists:
  assumes "wf[A](r)" "extensional_on(A,r)"
  shows "\<exists>M f. Transset(M) \<and> f \<in> ord_iso(A, r \<inter> A*A, M, Memrel(M))"
  using mostowski_collapse [OF assms] by blast

lemma collapse_unique:
  assumes wf: "wf[A](r)"
    and ftype: "f \<in> A \<rightarrow> B"
    and frec: "\<And>x. x \<in> A \<Longrightarrow> f`x = f `` ((r -`` {x}) \<inter> A)"
    and xA: "x \<in> A"
  shows "f`x = collapse(A,r,x)"
  using wf xA
proof (rule wf_on_induct_raw)
  fix x
  assume xA': "x \<in> A"
    and IH: "\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r \<longrightarrow> f ` y = collapse(A,r,y)"
  have "f`x = f `` ((r -`` {x}) \<inter> A)"
    using frec xA' by simp
  also have "... = {collapse(A,r,y). y \<in> (r -`` {x}) \<inter> A}"
  proof (rule equalityI)
    show "f `` ((r -`` {x}) \<inter> A) \<subseteq>
      {collapse(A,r,y). y \<in> (r -`` {x}) \<inter> A}"
    proof
      fix u
      assume "u \<in> f `` ((r -`` {x}) \<inter> A)"
      then obtain y where pair: "\<langle>y,u\<rangle> \<in> f"
        and ypred: "y \<in> (r -`` {x}) \<inter> A"
        by (rule imageE)
      have uy: "u = f`y"
        using pair ftype by (simp add: apply_equality)
      have "f`y = collapse(A,r,y)"
        using IH ypred by (simp add: vimage_singleton_iff)
      then have "u = collapse(A,r,y)"
        using uy by simp
      moreover have "y \<in> (r -`` {x}) \<inter> A"
        by (rule ypred)
      ultimately show "u \<in> {collapse(A,r,y). y \<in> (r -`` {x}) \<inter> A}"
        by (rule RepFun_eqI)
    qed
  next
    show "{collapse(A,r,y). y \<in> (r -`` {x}) \<inter> A} \<subseteq>
      f `` ((r -`` {x}) \<inter> A)"
    proof
      fix u
      assume "u \<in> {collapse(A,r,y). y \<in> (r -`` {x}) \<inter> A}"
      then obtain y where ypred: "y \<in> (r -`` {x}) \<inter> A"
        and uy: "u = collapse(A,r,y)"
        by (rule RepFunE)
      have "y \<in> A"
        using ypred by simp
      then have pair: "\<langle>y,f`y\<rangle> \<in> f"
        by (rule apply_Pair [OF ftype])
      have "f`y = collapse(A,r,y)"
        using IH ypred by (simp add: vimage_singleton_iff)
      then have "\<langle>y,u\<rangle> \<in> f"
        using uy pair by simp
      then show "u \<in> f `` ((r -`` {x}) \<inter> A)"
        using ypred by (rule imageI)
    qed
  qed
  also have "... = collapse(A,r,x)"
    using collapse_unfold [OF wf xA'] by simp
  finally show "f`x = collapse(A,r,x)" .
qed

lemma collapse_map_unique:
  assumes wf: "wf[A](r)"
    and ftype: "f \<in> A \<rightarrow> B"
    and frec: "\<And>x. x \<in> A \<Longrightarrow> f`x = f `` ((r -`` {x}) \<inter> A)"
  shows "f = collapse_map(A,r)"
  unfolding collapse_map_def
  using collapse_unique [OF wf ftype frec]
  by (force intro: fun_extension ftype lam_type)

lemma collapse_range_unique:
  assumes wf: "wf[A](r)"
    and ftype: "f \<in> A \<rightarrow> B"
    and frec: "\<And>x. x \<in> A \<Longrightarrow> f`x = f `` ((r -`` {x}) \<inter> A)"
    and M: "M = range(f)"
  shows "M = collapse_range(A,r)"
  using collapse_map_unique [OF wf ftype frec] M
  unfolding collapse_range_def by simp

end

