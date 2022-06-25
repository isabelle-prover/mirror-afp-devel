theory Ground_Closure
  imports Ground_Terms
begin

subsubsection \<open>Multihole context closure\<close>

text \<open>Computing the multihole context closure of a given relation\<close>
inductive_set gmctxt_cl :: "('f \<times> nat) set \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" for \<F> \<R> where
  base [intro]: "(s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> gmctxt_cl \<F> \<R>"
| step [intro]: "length ss = length ts \<Longrightarrow> (\<forall> i < length ts. (ss ! i, ts ! i) \<in> gmctxt_cl \<F> \<R>) \<Longrightarrow> (f, length ss) \<in> \<F> \<Longrightarrow>
    (GFun f ss, GFun f ts) \<in> gmctxt_cl \<F> \<R>"

lemma gmctxt_cl_idemp [simp]:
  "gmctxt_cl \<F> (gmctxt_cl \<F> \<R>) = gmctxt_cl \<F> \<R>"
proof -
  {fix s t assume "(s, t) \<in> gmctxt_cl \<F> (gmctxt_cl \<F> \<R>)"
    then have "(s, t) \<in> gmctxt_cl \<F> \<R>"
      by (induct) (auto intro: gmctxt_cl.step)}
  then show ?thesis by auto
qed

lemma gmctxt_cl_refl:
  "funas_gterm t \<subseteq> \<F> \<Longrightarrow> (t, t) \<in> gmctxt_cl \<F> \<R>"
  by (induct t) (auto simp: SUP_le_iff intro!: gmctxt_cl.step)

lemma gmctxt_cl_swap:
  "gmctxt_cl \<F> (prod.swap ` \<R>) = prod.swap ` gmctxt_cl \<F> \<R>" (is "?Ls = ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Ls" then have "(s, t) \<in> ?Rs"
      by induct auto}
  moreover
  {fix s t assume "(s, t) \<in> ?Rs"
    then have "(t, s) \<in> gmctxt_cl \<F> \<R>" by auto
    then have "(s, t) \<in> ?Ls" by induct auto}
  ultimately show ?thesis by auto
qed

lemma gmctxt_cl_mono_funas:
  assumes "\<F> \<subseteq> \<G>" shows "gmctxt_cl \<F> \<R> \<subseteq> gmctxt_cl \<G> \<R>"
proof -
  {fix s t assume "(s, t) \<in> gmctxt_cl \<F> \<R>" then have "(s, t) \<in> gmctxt_cl \<G> \<R>"
      by induct (auto simp: subsetD[OF assms])}
  then show ?thesis by auto
qed

lemma gmctxt_cl_mono_rel:
  assumes "\<P> \<subseteq> \<R>" shows "gmctxt_cl \<F> \<P> \<subseteq> gmctxt_cl \<F> \<R>"
proof -
  {fix s t assume "(s, t) \<in> gmctxt_cl \<F> \<P>" then have "(s, t) \<in> gmctxt_cl \<F> \<R>" using assms
      by induct auto}
  then show ?thesis by auto
qed

definition gcomp_rel :: "('f \<times> nat) set \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" where
  "gcomp_rel \<F> R S = (R O gmctxt_cl \<F> S) \<union> (gmctxt_cl \<F> R O S)"

definition gtrancl_rel :: "('f \<times> nat) set \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" where
  "gtrancl_rel \<F> \<R> = (gmctxt_cl \<F> \<R>)\<^sup>+ O \<R> O (gmctxt_cl \<F> \<R>)\<^sup>+"

lemma gcomp_rel:
  "gmctxt_cl \<F> (gcomp_rel \<F> \<R> \<S>) = gmctxt_cl \<F> \<R> O gmctxt_cl \<F> \<S>" (is "?Ls = ?Rs")
proof
  { fix s u assume "(s, u) \<in> gmctxt_cl \<F> (\<R> O gmctxt_cl \<F> \<S> \<union> gmctxt_cl \<F> \<R> O \<S>)"
     then have "\<exists>t. (s, t) \<in> gmctxt_cl \<F> \<R> \<and> (t, u) \<in> gmctxt_cl \<F> \<S>"
    proof (induct)
      case (step ss ts f)
      from Ex_list_of_length_P[of _ "\<lambda> u i. (ss ! i, u) \<in> gmctxt_cl \<F> \<R> \<and> (u, ts ! i) \<in> gmctxt_cl \<F> \<S>"]
      obtain us where l: "length us = length ts" and
        inv: "\<forall> i < length ts. (ss ! i, us ! i) \<in> gmctxt_cl \<F> \<R> \<and> (us ! i, ts ! i) \<in> gmctxt_cl \<F> \<S>"
        using step(2, 3) by blast
      then show ?case using step(1, 3)
        by (intro exI[of _ "GFun f us"]) auto
    qed auto}
  then show "?Ls \<subseteq> ?Rs" unfolding gcomp_rel_def
    by auto
next
  {fix s t u assume "(s, t) \<in> gmctxt_cl \<F> \<R>" "(t, u) \<in> gmctxt_cl \<F> \<S>"
    then have "(s, u) \<in> gmctxt_cl \<F> (\<R> O gmctxt_cl \<F> \<S> \<union> gmctxt_cl \<F> \<R> O \<S>)"
    proof (induct arbitrary: u rule: gmctxt_cl.induct)
      case (step ss ts f)
      then show ?case
      proof (cases "(GFun f ts, u) \<in> \<S>")
        case True
        then have "(GFun f ss, u) \<in> gmctxt_cl \<F> \<R> O \<S>" using gmctxt_cl.step[OF step(1) _ step(3)] step(2)
          by auto
        then show ?thesis by auto
      next
        case False
        then obtain us where u[simp]: "u = GFun f us" and l: "length ts = length us"
          using step(4) by (cases u) (auto elim: gmctxt_cl.cases)
        have "i < length us \<Longrightarrow>
         (ss ! i, us ! i) \<in> gmctxt_cl \<F> (\<R> O gmctxt_cl \<F> \<S> \<union> gmctxt_cl \<F> \<R> O \<S>)" for i
          using step(1, 2, 4) False by (auto elim: gmctxt_cl.cases)
        then show ?thesis using l step(1, 3)
          by auto
      qed
    qed auto}
  then show "?Rs \<subseteq> ?Ls"
    by (auto simp: gcomp_rel_def)
qed

subsubsection \<open>Signature closed property\<close>

definition all_ctxt_closed :: "('f \<times> nat) set \<Rightarrow> 'f gterm rel \<Rightarrow> bool" where
  "all_ctxt_closed F r \<longleftrightarrow> (\<forall> f ts ss. (f, length ss) \<in> F \<longrightarrow> length ss = length ts \<longrightarrow>
    (\<forall>i. i < length ts \<longrightarrow> (ss ! i, ts ! i) \<in> r) \<longrightarrow>
    (GFun f ss, GFun f ts) \<in> r)"

lemma all_ctxt_closedI:
  assumes "\<And> f ss ts. (f, length ss) \<in> \<F> \<Longrightarrow> length ss = length ts \<Longrightarrow>
     (\<forall> i < length ts. (ss ! i, ts ! i) \<in> r) \<Longrightarrow> (GFun f ss, GFun f ts) \<in> r"
  shows "all_ctxt_closed \<F> r" using assms
  unfolding all_ctxt_closed_def by auto

lemma all_ctxt_closedD:
  "all_ctxt_closed F r \<Longrightarrow> (f, length ss) \<in> F \<Longrightarrow> length ss = length ts \<Longrightarrow>
    (\<forall> i < length ts. (ss ! i, ts ! i) \<in> r) \<Longrightarrow> (GFun f ss, GFun f ts) \<in> r"
  by (auto simp: all_ctxt_closed_def)

lemma all_ctxt_closed_refl_on:
  assumes "all_ctxt_closed \<F> r" "s \<in> \<T>\<^sub>G \<F>"
  shows "(s, s) \<in> r" using assms(2)
  by (induct) (auto simp: all_ctxt_closedD[OF assms(1)])

lemma gmctxt_cl_is_all_ctxt_closed [simp]:
  "all_ctxt_closed \<F> (gmctxt_cl \<F> \<R>)"
  unfolding all_ctxt_closed_def
  by auto

lemma all_ctxt_closed_gmctxt_cl_idem [simp]:
  assumes "all_ctxt_closed \<F> \<R>"
  shows "gmctxt_cl \<F> \<R> = \<R>"
proof -
  {fix s t assume "(s, t) \<in> gmctxt_cl \<F> \<R>" then have "(s, t) \<in> \<R>"
    proof (induct)
      case (step ss ts f)
      show ?case using step(2) all_ctxt_closedD[OF assms step(3, 1)]
        by auto
    qed auto}
  then show ?thesis by auto
qed


subsubsection \<open>Transitive closure preserves @{const all_ctxt_closed}\<close>

text \<open>induction scheme for transitive closures of lists\<close>

inductive_set trancl_list for \<R> where
  base[intro, Pure.intro] : "length xs = length ys \<Longrightarrow>
      (\<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R>) \<Longrightarrow> (xs, ys) \<in> trancl_list \<R>"
| list_trancl [Pure.intro]: "(xs, ys) \<in> trancl_list \<R> \<Longrightarrow> i < length ys \<Longrightarrow> (ys ! i, z) \<in> \<R> \<Longrightarrow>
    (xs, ys[i := z]) \<in> trancl_list \<R>"

lemma trancl_list_appendI [simp, intro]:
  "(xs, ys) \<in> trancl_list \<R> \<Longrightarrow> (x, y) \<in> \<R> \<Longrightarrow> (x # xs, y # ys) \<in> trancl_list \<R>"
proof (induct rule: trancl_list.induct)
  case (base xs ys)
  then show ?case using less_Suc_eq_0_disj
    by (intro trancl_list.base) auto
next
  case (list_trancl xs ys i z)
  from list_trancl(3) have *: "y # ys[i := z] = (y # ys)[Suc i := z]" by auto
  show ?case using list_trancl unfolding *
    by (intro trancl_list.list_trancl) auto
qed

lemma trancl_list_append_tranclI [intro]:
  "(x, y) \<in> \<R>\<^sup>+ \<Longrightarrow> (xs, ys) \<in> trancl_list \<R> \<Longrightarrow> (x # xs, y # ys) \<in> trancl_list \<R>"
proof (induct rule: trancl.induct)
  case (trancl_into_trancl a b c)
  then have "(a # xs, b # ys) \<in> trancl_list \<R>" by auto
  from trancl_list.list_trancl[OF this, of 0 c]
  show ?case using trancl_into_trancl(3)
    by auto
qed auto

lemma trancl_list_conv:
  "(xs, ys) \<in> trancl_list \<R> \<longleftrightarrow> length xs = length ys \<and> (\<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R>\<^sup>+)" (is "?Ls \<longleftrightarrow> ?Rs")
proof
  assume "?Ls" then show ?Rs
  proof (induct)
    case (list_trancl xs ys i z)
    then show ?case
      by auto (metis nth_list_update trancl.trancl_into_trancl)
  qed auto
next
  assume ?Rs then show ?Ls
  proof (induct ys arbitrary: xs)
    case Nil
    then show ?case by (cases xs) auto
  next
    case (Cons y ys)
    from Cons(2) obtain x xs' where *: "xs = x # xs'" and
      inv: "(x, y) \<in> \<R>\<^sup>+"
      by (cases xs) auto
    show ?case using Cons(1)[of "tl xs"] Cons(2) unfolding *
      by (intro trancl_list_append_tranclI[OF inv]) force
  qed
qed

lemma trancl_list_induct [consumes 2, case_names base step]:
  assumes "length ss = length ts" "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>\<^sup>+"
    and "\<And>xs ys. length xs = length ys \<Longrightarrow> \<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R> \<Longrightarrow> P xs ys"
    and "\<And>xs ys i z. length xs = length ys \<Longrightarrow> \<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R>\<^sup>+ \<Longrightarrow> P xs ys
      \<Longrightarrow> i < length ys \<Longrightarrow> (ys ! i, z) \<in> \<R> \<Longrightarrow> P xs (ys[i := z])"
  shows "P ss ts" using assms
  by (intro trancl_list.induct[of ss ts \<R> P]) (auto simp: trancl_list_conv)

lemma trancl_list_all_step_induct [consumes 2, case_names base step]:
  assumes "length ss = length ts" "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>\<^sup>+"
    and base: "\<And>xs ys. length xs = length ys \<Longrightarrow> \<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R> \<Longrightarrow> P xs ys"
    and steps: "\<And>xs ys zs. length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow>
       \<forall> i < length zs. (xs ! i, ys ! i) \<in> \<R>\<^sup>+ \<Longrightarrow> \<forall> i < length zs. (ys ! i, zs ! i) \<in> \<R> \<or> ys ! i = zs ! i \<Longrightarrow>
       P xs ys \<Longrightarrow> P xs zs"
  shows "P ss ts" using assms(1, 2)
proof (induct rule: trancl_list_induct)
case (step xs ys i z)
  then show ?case
    by (intro steps[of xs ys "ys[i := z]"])
       (auto simp: nth_list_update)
qed (auto simp: base)

lemma all_ctxt_closed_trancl:
  assumes  "all_ctxt_closed \<F> \<R>" "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "all_ctxt_closed \<F> (\<R>\<^sup>+)"
proof -
  {fix f ss ts assume sig: "(f, length ss) \<in> \<F>" and
      steps: "length ss = length ts" "\<forall>i<length ts. (ss ! i, ts ! i) \<in> \<R>\<^sup>+"
    have "(GFun f ss, GFun f ts) \<in> \<R>\<^sup>+" using steps sig
    proof (induct rule: trancl_list_induct)
      case (base ss ts)
      then show ?case using all_ctxt_closedD[OF assms(1) base(3, 1, 2)]
        by auto
    next
      case (step ss ts i t')
      from step(2) have "j < length ts \<Longrightarrow> ts ! j \<in> \<T>\<^sub>G \<F>" for j using assms(2)
        by (metis (no_types, lifting) SigmaD2 subset_iff trancl.simps)
      from this[THEN all_ctxt_closed_refl_on[OF assms(1)]]
      have "(GFun f ts, GFun f (ts[i := t'])) \<in> \<R>" using step(1, 4-)
        by (intro all_ctxt_closedD[OF assms(1)]) (auto simp: nth_list_update)
      then show ?case using step(3, 6)
        by auto
    qed}
  then show ?thesis by (intro all_ctxt_closedI)
qed

end