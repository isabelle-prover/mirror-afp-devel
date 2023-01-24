section "Miscellaneous lemmas"

theory MiscLemmas imports "HOL-Library.Sublist" begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl[simp,intro]: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star_n :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl_n: "star_n r 0 x x"
| step_n: "r x y \<Longrightarrow> star_n r n y z \<Longrightarrow> star_n r (Suc n) x z"

declare star_n.intros[simp, intro]

lemma star_n_decompose:
  "star_n r n x y \<Longrightarrow> star_n r n' x z \<Longrightarrow> n' < n
    \<Longrightarrow> (\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> y = z)
    \<Longrightarrow> (\<And>n x y z. star_n r n x y \<Longrightarrow> star_n r n x z \<Longrightarrow> y = z)
    \<Longrightarrow> star_n r (n - n') z y"
  apply (induct arbitrary: n' z rule: star_n.induct, simp)
  apply clarsimp
  apply (rename_tac n z n' za)
  apply (subgoal_tac "Suc n - n' = Suc (n - n')")
   prefer 2
   apply simp
  apply simp
  apply (case_tac "n' < n", simp)
   apply (case_tac n')
    apply clarsimp
    apply (erule star_n.cases[of _ 0]; simp)
   apply (rename_tac z' m)
   apply simp
   apply (drule_tac x=m and y=z' in meta_spec2)
   apply (subgoal_tac "Suc (n - Suc m) = n - m")
    prefer 2
    apply arith
   apply simp
   apply (erule meta_mp)
   apply (erule_tac ?a1.0="Suc m" in star_n.cases; simp)
   apply clarsimp
   apply (rename_tac y n z x y' n' z')
   apply (drule_tac x=x and y=y in meta_spec2)
   apply (drule_tac x=y' in meta_spec)
   apply simp
  apply (subgoal_tac "n' = n")
   prefer 2
   apply arith
  apply simp
  apply (case_tac n; simp)
   apply clarsimp
   apply (erule star_n.cases; simp)
   apply (erule star_n.cases; simp)
  apply (rename_tac za m)
  apply (drule_tac x="n - (Suc 0)" and y=za in meta_spec2)
  apply simp
  apply (erule meta_mp)
  apply (drule_tac x=m and y=y in meta_spec2)
  apply (rotate_tac -1)
  apply (drule_tac x=z and y=za in meta_spec2)
  apply (erule star_n.cases; simp)
  apply (erule star_n.cases; simp)
  by fastforce

lemma star_n_add:
  "star_n r n x z \<longleftrightarrow> (\<exists>n1 n2 y. star_n r n1 x y \<and> star_n r n2 y z \<and> n = n1 + n2)"
proof (rule iffI)
  assume "star_n r n x z"
  from this show "\<exists>n1 n2 y. star_n r n1 x y \<and> star_n r n2 y z \<and> n = n1 + n2"
    by (induct rule: star_n.induct; fastforce)
next
  assume H0: "\<exists>n1 n2 y. star_n r n1 x y \<and> star_n r n2 y z \<and> n = n1 + n2"
  have H: "star_n r n1 x y \<Longrightarrow>
       star_n r n2 y z \<Longrightarrow> star_n r (n1 + n2) x z" for y n1 n2
    by (induct rule: star_n.induct; simp)
  show "star_n r n x z " using H0 H by blast
qed

lemma star_star_n:
  "star r x y \<Longrightarrow> \<exists>n. star_n r n x y"
  by (induct rule: star.induct; fastforce)

lemma star_n_star:
  "star_n r n x y \<Longrightarrow> star r x y"
  by (induct rule: star_n.induct; fastforce elim!: step)

lemma star_eq_star_n:
  "star r x y = (\<exists>n. star_n r n x y)"
  by (meson star_n_star star_star_n)

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  by (meson star_eq_star_n star_n_add)

lemma step_rev:
  "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  by (meson star.simps star_trans)

lemma star_n_trans:
  "star_n r n x y \<Longrightarrow> star_n r n' y z \<Longrightarrow> star_n r (n + n') x z"
  using star_n_add by force

lemma step_n_rev:
  "star_n r n x y \<Longrightarrow> r y z \<Longrightarrow> star_n r (Suc n) x z"
  by (induct rule: star_n.induct; clarsimp)

lemma star_n_lastE:
  "star_n r (Suc n) x z \<Longrightarrow>
   (\<And>n' x' y' z'. n = n' \<Longrightarrow> x = x' \<Longrightarrow> z = z'
     \<Longrightarrow> star_n r n' x' y' \<Longrightarrow> r y' z' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct n arbitrary: x z)
  case 0
  then show ?case
    by cases (erule star_n.cases; force)
next
  case (Suc n)
  then show ?case
    by cases (erule star_n.cases; force)+
qed

lemma
  star_n_conjunct1: "star_n (\<lambda>x y. P x y \<and> Q x y) n s t \<Longrightarrow> star_n P n s t" and
  star_n_conjunct2: "star_n (\<lambda>x y. P x y \<and> Q x y) n s t \<Longrightarrow> star_n Q n s t" and
  star_n_commute: "star_n (\<lambda>x y. P x y \<and> Q x y) n s t \<Longrightarrow> star_n (\<lambda>x y. Q x y \<and> P x y) n s t"
  by (induct rule: star_n.induct; clarsimp)+

lemma forall_swap4:
  "(\<forall>x y z w. P x y z w) \<longleftrightarrow> (\<forall>z w y x. P x y z w)" by auto

lemma prefix_drop_append:
  "prefix xs ys \<Longrightarrow> xs @ drop (length xs) ys = ys"
  by (metis append_eq_conv_conj prefix_def)

lemma min_prefix:
  "\<forall>i. prefix (f i) (f (Suc i)) \<Longrightarrow> (\<forall>i. prefix (f 0) (f i))"
  apply clarsimp
  using prefix_order.lift_Suc_mono_le by blast

definition wf_to_wfP where
  "wf_to_wfP r \<equiv> \<lambda>x y. (x, y) \<in> r"

end