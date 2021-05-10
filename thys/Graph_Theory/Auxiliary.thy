theory Auxiliary
imports
  "HOL-Library.FuncSet"
  "HOL-Combinatorics.Orbits"
begin

lemma funpow_invs:
  assumes "m \<le> n" and inv: "\<And>x. f (g x) = x"
  shows "(f ^^ m) ((g ^^ n) x) = (g ^^ (n - m)) x"
  using \<open>m \<le> n\<close>
proof (induction m)
  case (Suc m)
  moreover then have "n - m = Suc (n - Suc m)" by auto
  ultimately show ?case by (auto simp: inv)
qed simp


section \<open>Permutation Domains\<close>

definition has_dom :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "has_dom f S \<equiv> \<forall>s. s \<notin> S \<longrightarrow> f s = s"

lemma has_domD: "has_dom f S \<Longrightarrow> x \<notin> S \<Longrightarrow> f x = x"
  by (auto simp: has_dom_def)

lemma has_domI: "(\<And>x. x \<notin> S \<Longrightarrow> f x = x) \<Longrightarrow> has_dom f S"
  by (auto simp: has_dom_def)

lemma permutes_conv_has_dom:
  "f permutes S \<longleftrightarrow> bij f \<and> has_dom f S"
  by (auto simp: permutes_def has_dom_def bij_iff)


section \<open>Segments\<close>

inductive_set segment :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" for f a b where
  base: "f a \<noteq> b \<Longrightarrow> f a \<in> segment f a b" |
  step: "x \<in> segment f a b \<Longrightarrow> f x \<noteq> b \<Longrightarrow> f x \<in> segment f a b"

lemma segment_step_2D:
  assumes "x \<in> segment f a (f b)" shows "x \<in> segment f a b \<or> x = b"
  using assms by induct (auto intro: segment.intros)

lemma not_in_segment2D:
  assumes "x \<in> segment f a b" shows "x \<noteq> b"
  using assms by induct auto

lemma segment_altdef:
  assumes "b \<in> orbit f a"
  shows "segment f a b = (\<lambda>n. (f ^^ n) a) ` {1..<funpow_dist1 f a b}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix x assume "x \<in> ?L"
  have "f a \<noteq>b \<Longrightarrow> b \<in> orbit f (f a)"
    using assms  by (simp add: orbit_step)
  then have *: "f a \<noteq> b \<Longrightarrow> 0 < funpow_dist f (f a) b"
    using assms using gr0I funpow_dist_0_eq[OF \<open>_ \<Longrightarrow> b \<in> orbit f (f a)\<close>] by (simp add: orbit.intros)
  from \<open>x \<in> ?L\<close> show "x \<in> ?R"
  proof induct
    case base then show ?case by (intro image_eqI[where x=1]) (auto simp: *)
  next
    case step then show ?case using assms funpow_dist1_prop less_antisym
      by (fastforce intro!: image_eqI[where x="Suc n" for n])
  qed
next
  fix x assume "x \<in> ?R"
  then obtain n where "(f ^^ n ) a = x" "0 < n" "n < funpow_dist1 f a b" by auto
  then show "x \<in> ?L"
  proof (induct n arbitrary: x)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "(f ^^ Suc n) a \<noteq> b" using Suc by (meson funpow_dist1_least)
    with Suc show ?case by (cases "n = 0") (auto intro: segment.intros)
  qed
qed

(*XXX move up*)
lemma segmentD_orbit:
  assumes "x \<in> segment f y z" shows "x \<in> orbit f y"
  using assms by induct (auto intro: orbit.intros)

lemma segment1_empty: "segment f x (f x) = {}"
  by (auto simp: segment_altdef orbit.base funpow_dist_0)

lemma segment_subset:
  assumes "y \<in> segment f x z"
  assumes "w \<in> segment f x y"
  shows "w \<in> segment f x z"
  using assms by (induct arbitrary: w) (auto simp: segment1_empty intro: segment.intros dest: segment_step_2D elim: segment.cases)

(* XXX move up*)
lemma not_in_segment1:
  assumes "y \<in> orbit f x" shows "x \<notin> segment f x y"
proof
  assume "x \<in> segment f x y"
  then obtain n where n: "0 < n" "n < funpow_dist1 f x y" "(f ^^ n) x = x"
    using assms by (auto simp: segment_altdef Suc_le_eq)
  then have neq_y: "(f ^^ (funpow_dist1 f x y - n)) x \<noteq> y" by (simp add: funpow_dist1_least)

  have "(f ^^ (funpow_dist1 f x y - n)) x = (f ^^ (funpow_dist1 f x y - n)) ((f ^^ n) x)"
    using n by (simp add: funpow_add)
  also have "\<dots> = (f ^^ funpow_dist1 f x y) x"
    using \<open>n < _\<close> by (simp add: funpow_add)
      (metis assms funpow_0 funpow_neq_less_funpow_dist1 n(1) n(3) nat_neq_iff zero_less_Suc) 
  also have "\<dots> = y" using assms by (rule funpow_dist1_prop)
  finally show False using neq_y by contradiction
qed

lemma not_in_segment2: "y \<notin> segment f x y"
  using not_in_segment2D by metis

(*XXX move*)
lemma in_segmentE:
  assumes "y \<in> segment f x z" "z \<in> orbit f x"
  obtains "(f ^^ funpow_dist1 f x y) x = y" "funpow_dist1 f x y < funpow_dist1 f x z"
proof
  from assms show "(f ^^ funpow_dist1 f x y) x = y"
    by (intro segmentD_orbit funpow_dist1_prop)
  moreover
  obtain n where "(f ^^ n) x = y" "0 < n" "n < funpow_dist1 f x z"
    using assms by (auto simp: segment_altdef)
  moreover then have "funpow_dist1 f x y \<le> n" by (meson funpow_dist1_least not_less)
  ultimately show "funpow_dist1 f x y < funpow_dist1 f x z" by linarith
qed

(*XXX move*)
lemma cyclic_split_segment:
  assumes S: "cyclic_on f S" "a \<in> S" "b \<in> S" and "a \<noteq> b"
  shows "S = {a,b} \<union> segment f a b \<union> segment f b a" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix c assume "c \<in> ?L"
  with S have "c \<in> orbit f a" unfolding cyclic_on_alldef by auto
  then show "c \<in> ?R" by induct (auto intro: segment.intros)
next
  fix c assume "c \<in> ?R"
  moreover have "segment f a b \<subseteq> orbit f a" "segment f b a \<subseteq> orbit f b"
    by (auto dest: segmentD_orbit)
  ultimately show "c \<in> ?L" using S by (auto simp: cyclic_on_alldef)
qed

(*XXX move*)
lemma segment_split:
  assumes y_in_seg: "y \<in> segment f x z"
  shows "segment f x z = segment f x y \<union> {y} \<union> segment f y z" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix w assume "w \<in> ?L" then show "w \<in> ?R" by induct (auto intro: segment.intros)
next
  fix w assume "w \<in> ?R"
  moreover
  { assume "w \<in> segment f x y" then have "w \<in> segment f x z"
    using segment_subset[OF y_in_seg] by auto }
  moreover
  { assume "w \<in> segment f y z" then have "w \<in> segment f x z"
      using y_in_seg by induct (auto intro: segment.intros) }
  ultimately
  show "w \<in> ?L" using y_in_seg by (auto intro: segment.intros)
qed

lemma in_segmentD_inv:
  assumes "x \<in> segment f a b" "x \<noteq> f a"
  assumes "inj f"
  shows "inv f x \<in> segment f a b"
  using assms by (auto elim: segment.cases)

lemma in_orbit_invI:
  assumes "b \<in> orbit f a"
  assumes "inj f"
  shows "a \<in> orbit (inv f) b"
  using assms(1)
  apply induct
   apply (simp add: assms(2) orbit_eqI(1))
  by (metis assms(2) inv_f_f orbit.base orbit_trans)

lemma segment_step_2:
  assumes A: "x \<in> segment f a b" "b \<noteq> a" and "inj f"
  shows "x \<in> segment f a (f b)"
  using A by induct (auto intro: segment.intros dest: not_in_segment2D injD[OF \<open>inj f\<close>])

lemma inv_end_in_segment:
  assumes "b \<in> orbit f a" "f a \<noteq> b" "bij f"
  shows "inv f b \<in> segment f a b"
  using assms(1,2)
proof induct
  case base then show ?case by simp
next
  case (step x)
  moreover
  from \<open>bij f\<close> have "inj f" by (rule bij_is_inj)
  moreover
  then have "x \<noteq> f x \<Longrightarrow> f a = x \<Longrightarrow> x \<in> segment f a (f x)" by (meson segment.simps)
  moreover
  have "x \<noteq> f x"
    using step \<open>inj f\<close> by (metis in_orbit_invI inv_f_eq not_in_segment1 segment.base)
  then have "inv f x \<in> segment f a (f x) \<Longrightarrow> x \<in> segment f a (f x)"
    using \<open>bij f\<close> \<open>inj f\<close> by (auto dest: segment.step simp: surj_f_inv_f bij_is_surj)
  then have "inv f x \<in> segment f a x \<Longrightarrow> x \<in> segment f a (f x)"
    using \<open>f a \<noteq> f x\<close> \<open>inj f\<close> by (auto dest: segment_step_2 injD)
  ultimately show ?case by (cases "f a = x") simp_all
qed

lemma segment_overlapping:
  assumes "x \<in> orbit f a" "x \<in> orbit f b" "bij f"
  shows "segment f a x \<subseteq> segment f b x \<or> segment f b x \<subseteq> segment f a x"
  using assms(1,2)
proof induction
  case base then show ?case by (simp add: segment1_empty)
next
  case (step x)
  from \<open>bij f\<close> have "inj f" by (simp add: bij_is_inj)
  have *: "\<And>f x y. y \<in> segment f x (f x) \<Longrightarrow> False" by (simp add: segment1_empty)
  { fix y z
    assume A: "y \<in> segment f b (f x)" "y \<notin> segment f a (f x)" "z \<in> segment f a (f x)"
    from \<open>x \<in> orbit f a\<close> \<open>f x \<in> orbit f b\<close> \<open>y \<in> segment f b (f x)\<close>
    have "x \<in> orbit f b"
      by (metis * inv_end_in_segment[OF _ _ \<open>bij f\<close>] inv_f_eq[OF \<open>inj f\<close>] segmentD_orbit)
    moreover
    with \<open>x \<in> orbit f a\<close> step.IH
    have "segment f a (f x) \<subseteq> segment f b (f x) \<or> segment f b (f x) \<subseteq> segment f a (f x)"
      apply auto
       apply (metis * inv_end_in_segment[OF _ _ \<open>bij f\<close>] inv_f_eq[OF \<open>inj f\<close>] segment_step_2D segment_subset step.prems subsetCE)
      by (metis (no_types, lifting) \<open>inj f\<close> * inv_end_in_segment[OF _ _ \<open>bij f\<close>] inv_f_eq orbit_eqI(2) segment_step_2D segment_subset subsetCE)
    ultimately
    have "segment f a (f x) \<subseteq> segment f b (f x)" using A by auto
  } note C = this
  then show ?case by auto
qed

lemma segment_disj:
  assumes "a \<noteq> b" "bij f"
  shows "segment f a b \<inter> segment f b a = {}"
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain x where x: "x \<in> segment f a b" "x \<in> segment f b a" by blast
  then have "segment f a b = segment f a x \<union> {x} \<union> segment f x b"
      "segment f b a = segment f b x \<union> {x} \<union> segment f x a"
    by (auto dest: segment_split)
  then have o: "x \<in> orbit f a" "x \<in> orbit f b" by (auto dest: segmentD_orbit)

  note * = segment_overlapping[OF o \<open>bij f\<close>]
  have "inj f" using \<open>bij f\<close> by (simp add: bij_is_inj)

  have "segment f a x = segment f b x"
  proof (intro set_eqI iffI)
    fix y assume A: "y \<in> segment f b x"
    then have "y \<in> segment f a x \<or> f a \<in> segment f b a"
      using * x(2) by (auto intro: segment.base segment_subset)
    then show "y \<in> segment f a x"
      using \<open>inj f\<close> A by (metis (no_types) not_in_segment2 segment_step_2)
  next
    fix y assume A: "y \<in> segment f a x "
    then have "y \<in> segment f b x \<or> f b \<in> segment f a b"
      using * x(1) by (auto intro: segment.base segment_subset)
    then show "y \<in> segment f b x"
      using \<open>inj f\<close> A by (metis (no_types) not_in_segment2 segment_step_2)
  qed
  moreover
  have "segment f a x \<noteq> segment f b x"
    by (metis assms bij_is_inj not_in_segment2 segment.base segment_step_2 segment_subset x(1))
  ultimately show False by contradiction
qed

lemma segment_x_x_eq:
  assumes "permutation f"
  shows "segment f x x = orbit f x - {x}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix y assume "y \<in> ?L" then show "y \<in> ?R" by (auto dest: segmentD_orbit simp: not_in_segment2)
next
  fix y assume "y \<in> ?R"
  then have "y \<in> orbit f x" "y \<noteq> x" by auto
  then show "y \<in> ?L" by induct (auto intro: segment.intros)
qed



section \<open>Lists of Powers\<close>

definition iterate :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a ) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "iterate m n f x = map (\<lambda>n. (f^^n) x) [m..<n]"

lemma set_iterate:
  "set (iterate m n f x) = (\<lambda>k. (f ^^ k) x) ` {m..<n} "
  by (auto simp: iterate_def)

lemma iterate_empty[simp]: "iterate n m f x = [] \<longleftrightarrow> m \<le> n"
  by (auto simp: iterate_def)

lemma iterate_length[simp]:
  "length (iterate m n f x) = n - m"
  by (auto simp: iterate_def)

lemma iterate_nth[simp]:
  assumes "k < n - m" shows "iterate m n f x ! k = (f^^(m+k)) x"
  using assms
  by (induct k arbitrary: m) (auto simp: iterate_def)

lemma iterate_applied:
  "iterate n m f (f x) = iterate (Suc n) (Suc m) f x"
  by (induct m arbitrary: n) (auto simp: iterate_def funpow_swap1)

end
