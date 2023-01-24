theory Globular_Set
  
imports "HOL-Library.FuncSet"

begin

section \<open>Background material on extensional functions\<close>

lemma PiE_imp_Pi: "f \<in> A \<rightarrow>\<^sub>E B \<Longrightarrow> f \<in> A \<rightarrow> B" by fast

lemma PiE_iff': "f \<in> A \<rightarrow>\<^sub>E B = (f \<in> A \<rightarrow> B \<and> f \<in> extensional A)"
  by (simp add: PiE_iff Pi_iff)

abbreviation composing ("_ \<circ> _ \<down> _" [60,0,60]59)
  where "g \<circ> f \<down> D \<equiv> compose D g f"

lemma compose_PiE: "f \<in> A \<rightarrow> B \<Longrightarrow> g \<in> B \<rightarrow> C \<Longrightarrow> g \<circ> f \<down> A \<in> A \<rightarrow>\<^sub>E C"
  by (metis funcset_compose compose_extensional PiE_iff')

lemma compose_eq_iff: "(g \<circ> f \<down> A = k \<circ> h \<down> A) = (\<forall>x \<in> A. g (f x) = k (h x))"
proof (safe)
  fix x assume "g \<circ> f \<down> A = k \<circ> h \<down> A" "x \<in> A"
  then show "g (f x) = k (h x)" by (metis compose_eq)
next
  assume "\<forall>x \<in> A. g (f x) = k (h x)"
  hence "\<And>x. x \<in> A \<Longrightarrow> (g \<circ> f \<down> A) x = (k \<circ> h \<down> A) x" by (metis compose_eq)
  then show "g \<circ> f \<down> A = k \<circ> h \<down> A" by (metis extensionalityI compose_extensional)
qed

lemma compose_eq_if: "(\<And>x. x \<in> A \<Longrightarrow> g (f x) = k (h x)) \<Longrightarrow> g \<circ> f \<down> A = k \<circ> h \<down> A"
  using compose_eq_iff by blast

lemma compose_compose_eq_iff2: "(h \<circ> (g \<circ> f \<down> A) \<down> A = h' \<circ> (g' \<circ> f' \<down> A) \<down> A) =
  (\<forall>x \<in> A. h (g (f x)) = h' (g' (f' x)))"
  by (simp add: compose_eq compose_eq_iff)

lemma compose_compose_eq_iff1: assumes "f \<in> A \<rightarrow> B" "f' \<in> A \<rightarrow> B"
  shows "((h \<circ> g \<down> B) \<circ> f \<down> A = (h' \<circ> g' \<down> B) \<circ> f' \<down> A) = (\<forall>x \<in> A. h (g (f x)) = h' (g' (f' x)))"
proof -
  have "(h \<circ> g \<down> B) \<circ> f \<down> A = h \<circ> (g \<circ> f \<down> A) \<down> A" by (metis assms(1) compose_assoc)
  moreover have "(h' \<circ> g' \<down> B) \<circ> f' \<down> A = h' \<circ> (g' \<circ> f' \<down> A) \<down> A" by (metis assms(2) compose_assoc)
  ultimately have h: "((h \<circ> g \<down> B) \<circ> f \<down> A = (h' \<circ> g' \<down> B) \<circ> f' \<down> A) =
    (h \<circ> (g \<circ> f \<down> A) \<down> A = h' \<circ> (g' \<circ> f' \<down> A) \<down> A)" by presburger
  then show ?thesis by (simp only: h compose_compose_eq_iff2)
qed

lemma compose_compose_eq_if1: "\<lbrakk>f \<in> A \<rightarrow> B; f' \<in> A \<rightarrow> B; \<forall>x \<in> A. h (g (f x)) = h' (g' (f' x))\<rbrakk> \<Longrightarrow>
  (h \<circ> g \<down> B) \<circ> f \<down> A = (h' \<circ> g' \<down> B) \<circ> f' \<down> A"
  using compose_compose_eq_iff1 by blast

lemma compose_compose_eq_if2: "\<forall>x \<in> A. h (g (f x)) = h' (g' (f' x)) \<Longrightarrow>
  h \<circ> (g \<circ> f \<down> A) \<down> A = h' \<circ> (g' \<circ> f' \<down> A) \<down> A"
  using compose_compose_eq_iff2 by blast

lemma compose_restrict_eq1: "f \<in> A \<rightarrow> B \<Longrightarrow>  restrict g B \<circ> f \<down> A = g \<circ> f \<down> A"
  by (smt (verit) PiE compose_eq_iff restrict_apply')

lemma compose_restrict_eq2: "g \<circ> (restrict f A) \<down> A = g \<circ> f \<down> A"
  by (metis (mono_tags, lifting) compose_eq_if restrict_apply')

lemma compose_Id_eq_restrict: "g \<circ> (\<lambda>x \<in> A. x) \<down> A = restrict g A"
  by (smt (verit) compose_restrict_eq1 compose_def restrict_apply' restrict_ext)

section \<open>Globular sets\<close>

subsection \<open>Globular sets\<close>

text \<open>
  We define a locale \<open>globular_set\<close> that encodes the cell data of a strict $\omega$-category
  \cite[Def 1.4.5]{Leinster2004}. The elements of \<open>X n\<close> are the \<open>n\<close>-cells, and the maps \<open>s\<close>
  and \<open>t\<close> give the source and target of a cell, respectively.
\<close>

locale globular_set =
  fixes X :: "nat \<Rightarrow> 'a set" and s :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" and t :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes s_fun: "s n \<in> X (Suc n) \<rightarrow> X n"
    and   t_fun: "t n \<in> X (Suc n) \<rightarrow> X n"
    and  s_comp: "x \<in> X (Suc (Suc n)) \<Longrightarrow> s n (t (Suc n) x) = s n (s (Suc n) x)"
    and  t_comp: "x \<in> X (Suc (Suc n)) \<Longrightarrow> t n (s (Suc n) x) = t n (t (Suc n) x)"
begin

lemma s_comp': "s n \<circ> t (Suc n) \<down> X (Suc (Suc n)) = s n \<circ> s (Suc n) \<down> X (Suc (Suc n))"
  by (metis (full_types) compose_eq_if s_comp)

lemma t_comp': "t n \<circ> s (Suc n) \<down> X (Suc (Suc n)) = t n \<circ> t (Suc n) \<down> X (Suc (Suc n))"
  by (metis (full_types) compose_eq_if t_comp)

text \<open>These are the generalised source and target maps. The arguments are the dimension of the
input and output, respectively. They allow notation similar to \<open>s\<^sup>m\<^sup>-\<^sup>p\<close> in \cite{Leinster2004}.\<close>

fun s' :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"s' 0 0 = id" |
"s' 0 (Suc n) = undefined" |
"s' (Suc m) n = (if Suc m < n then undefined
  else if Suc m = n then id
  else s' m n \<circ> s m)"

fun t' :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"t' 0 0 = id" |
"t' 0 (Suc n) = undefined" |
"t' (Suc m) n = (if Suc m < n then undefined
  else if Suc m = n then id
  else t' m n \<circ> t m)"

lemma s'_n_n [simp]: "s' n n = id"
  by (cases n, simp_all)

lemma s'_Suc_n_n [simp]: "s' (Suc n) n = s n"
  by simp

lemma s'_Suc_Suc_n_n [simp]: "s' (Suc (Suc n)) n = s n \<circ> s (Suc n)"
  by simp

lemma s'_Suc [simp]: "n \<le> m \<Longrightarrow> s' (Suc m) n = s' m n \<circ> s m"
  by simp

lemma s'_Suc': "n < m \<Longrightarrow> s' m n = s n \<circ> s' m (Suc n)"
proof (induction m arbitrary: n)
  case 0
  then show ?case by blast
next
  case (Suc m)
  hence "n \<le> m" by fastforce 
  show ?case proof (cases "n = m", simp)
    assume "n \<noteq> m" 
    then show "s' (Suc m) n = s n \<circ> s' (Suc m) (Suc n)" using Suc by fastforce
  qed    
qed

lemma t'_n_n [simp]: "t' n n = id"
  by (cases n, simp_all)

lemma t'_Suc_n_n [simp]: "t' (Suc n) n = t n"
  by simp

lemma t'_Suc_Suc_n_n [simp]: "t' (Suc (Suc n)) n = t n \<circ> t (Suc n)"
  by simp

lemma t'_Suc [simp]: "n \<le> m \<Longrightarrow> t' (Suc m) n = t' m n \<circ> t m"
  by simp

lemma t'_Suc': "n < m \<Longrightarrow> t' m n = t n \<circ> t' m (Suc n)"
proof (induction m arbitrary: n)
  case 0
  then show ?case by blast
next
  case (Suc m)
  hence "n \<le> m" by fastforce 
  show ?case proof (cases "n = m", simp)
    assume "n \<noteq> m" 
    then show "t' (Suc m) n = t n \<circ> t' (Suc m) (Suc n)" using Suc by fastforce
  qed    
qed

lemma s'_fun: "n \<le> m \<Longrightarrow> s' m n \<in> X m \<rightarrow> X n"
proof (induction m arbitrary: n)
  case 0
  thus ?case by force
next
  case (Suc m)
  thus ?case proof (cases "n = Suc m")
    case True
    then show ?thesis by auto
  next
    case False
    hence "n \<le> m" using `n \<le> Suc m` by force
    thus ?thesis using Suc.IH s_fun s'_Suc by auto
  qed
qed

lemma t'_fun: "n \<le> m \<Longrightarrow> t' m n \<in> X m \<rightarrow> X n"
proof (induction m arbitrary: n)
  case 0
  thus ?case by force
next
  case (Suc m)
  thus ?case proof (cases "n = Suc m")
    case True
    then show ?thesis by auto
  next
    case False
    hence "n \<le> m" using `n \<le> Suc m` by force
    thus ?thesis using Suc.IH t_fun t'_Suc by auto
  qed
qed

lemma s'_comp: "\<lbrakk> n < m; x \<in> X m \<rbrakk> \<Longrightarrow> s n (t' m (Suc n) x) = s' m n x"
proof (induction "m - n" arbitrary: n)
  case 0
  then show ?case by force
next
  case IH: (Suc k)
  show ?case proof (cases k)
    case 0
    with IH(2) have "m = Suc n" by fastforce
    then show ?thesis using s'_Suc' by auto
  next
    case (Suc k')
    with \<open>Suc k = m - n\<close> have hle: "Suc (Suc n) \<le> m" by simp
    hence "Suc n < m" by force
    hence "Suc (Suc n) \<le> m" by fastforce
    have "s n (t' m (Suc n) x)
       = s n (t (Suc n) (t' m (Suc (Suc n)) x))" using t'_Suc' \<open>Suc n < m\<close> by simp
    also have "\<dots> = s n (s (Suc n) (t' m (Suc (Suc n)) x))"
      using t'_fun \<open>Suc (Suc n) \<le> m\<close> s_comp IH(4) by blast
    also have "\<dots> = s n (s' m (Suc n) x)"
      using IH Suc_diff_Suc Suc_inject \<open>Suc n < m\<close> by presburger
    finally show ?thesis using \<open>n < m\<close> s'_Suc' by simp
  qed
qed

lemma t'_comp: "\<lbrakk> n < m; x \<in> X m \<rbrakk> \<Longrightarrow> t n (s' m (Suc n) x) = t' m n x"
proof (induction "m - n" arbitrary: n)
  case 0
  then show ?case by force
next
  case IH: (Suc k)
  show ?case proof (cases k)
    case 0
    with IH(2) have "m = Suc n" by fastforce
    then show ?thesis using IH.prems(1) by auto
  next
    case (Suc k')
    with \<open>Suc k = m - n\<close> have hle: "Suc (Suc n) \<le> m" by simp
    hence "Suc n < m" by force
    hence "Suc (Suc n) \<le> m" by fastforce
    have "t n (s' m (Suc n) x)
       = t n (s (Suc n) (s' m (Suc (Suc n)) x))" using s'_Suc' \<open>Suc n < m\<close> by simp
    also have "\<dots> = t n (t (Suc n) (s' m (Suc (Suc n)) x))"
      using s'_fun \<open>Suc (Suc n) \<le> m\<close> t_comp IH(4) by blast
    also have "\<dots> = t n (t' m (Suc n) x)"
      using IH Suc_diff_Suc Suc_inject \<open>Suc n < m\<close> by presburger
    finally show ?thesis using \<open>n < m\<close> t'_Suc' by simp
  qed
qed

text \<open>The following predicates and sets are needed to define composition in an $\omega$-category.\<close>

definition is_parallel_pair :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_parallel_pair m n x y \<equiv> n \<le> m \<and> x \<in> X m \<and> y \<in> X m \<and> s' m n x = s' m n y \<and> t' m n x = t' m n y"

text \<open>\cite[p. 44]{Leinster2004}\<close>
definition is_composable_pair :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_composable_pair m n y x \<equiv> n < m \<and> y \<in> X m \<and> x \<in> X m \<and> t' m n x = s' m n y"

definition composable_pairs :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) set" where
"composable_pairs m n = {(y, x). is_composable_pair m n y x}"

lemma composable_pairs_empty: "m \<le> n \<Longrightarrow> composable_pairs m n = {}"
  using is_composable_pair_def composable_pairs_def by simp

end

subsection \<open>Maps between globular sets\<close>

text \<open>We define maps between globular sets to be natural transformations of the corresponding
functors \cite[Def 1.4.5]{Leinster2004}.\<close>

locale globular_map = source: globular_set X s\<^sub>X t\<^sub>X + target: globular_set Y s\<^sub>Y t\<^sub>Y
  for X s\<^sub>X t\<^sub>X Y s\<^sub>Y t\<^sub>Y +
  fixes \<phi> :: "nat \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes map_fun: "\<phi> m \<in> X m \<rightarrow> Y m"
    and   is_natural_wrt_s: "x \<in> X (Suc m) \<Longrightarrow> \<phi> m (s\<^sub>X m x) = s\<^sub>Y m (\<phi> (Suc m) x)"
    and   is_natural_wrt_t: "x \<in> X (Suc m) \<Longrightarrow> \<phi> m (t\<^sub>X m x) = t\<^sub>Y m (\<phi> (Suc m) x)"
begin

lemma is_natural_wrt_s': "\<lbrakk> n \<le> m; x \<in> X m \<rbrakk> \<Longrightarrow> \<phi> n (source.s' m n x) = target.s' m n (\<phi> m x)"
proof (induction "m - n" arbitrary: n)
  case 0
  hence "m = n" by simp
  then show ?case by fastforce
next
  case (Suc k)
  hence "n < m" by force
  hence "Suc n \<le> m" by auto
  have "\<phi> n (source.s' m n x) = \<phi> n (s\<^sub>X n (source.s' m (Suc n) x))"
    using source.s'_Suc' \<open>n < m\<close> by simp
  also have "\<dots> = s\<^sub>Y n (\<phi> (Suc n) (source.s' m (Suc n) x))"
    using source.s'_fun \<open>Suc n \<le> m\<close> Suc(1) Suc(4) is_natural_wrt_s by blast
  also have "\<dots> = s\<^sub>Y n (target.s' m (Suc n) (\<phi> m x))"
    using Suc \<open>Suc n \<le> m\<close> Suc_diff_Suc Suc_inject \<open>n < m\<close> by presburger
  finally show ?case using target.s'_Suc' \<open>n < m\<close> by simp
qed

lemma is_natural_wrt_t': "\<lbrakk> n \<le> m; x \<in> X m \<rbrakk> \<Longrightarrow> \<phi> n (source.t' m n x) = target.t' m n (\<phi> m x)"
proof (induction "m - n" arbitrary: n)
  case 0
  hence "m = n" by simp
  then show ?case by fastforce
next
  case (Suc k)
  hence "n < m" by force
  hence "Suc n \<le> m" by auto
  have "\<phi> n (source.t' m n x) = \<phi> n (t\<^sub>X n (source.t' m (Suc n) x))"
    using source.t'_Suc' \<open>n < m\<close> by simp
  also have "\<dots> = t\<^sub>Y n (\<phi> (Suc n) (source.t' m (Suc n) x))"
    using source.t'_fun \<open>Suc n \<le> m\<close> Suc(1) Suc(4) is_natural_wrt_t by blast
  also have "\<dots> = t\<^sub>Y n (target.t' m (Suc n) (\<phi> m x))"
    using Suc \<open>Suc n \<le> m\<close> Suc_diff_Suc Suc_inject \<open>n < m\<close> by presburger
  finally show ?case using target.t'_Suc' \<open>n < m\<close> by simp
qed

end

text \<open>The composition of two globular maps is itself a globular map. This intermediate
  locale gathers the data needed for such a statement.\<close>
locale two_globular_maps = fst: globular_map X s\<^sub>X t\<^sub>X Y s\<^sub>Y t\<^sub>Y \<phi> + snd: globular_map Y s\<^sub>Y t\<^sub>Y Z s\<^sub>Z t\<^sub>Z \<psi>
  for X s\<^sub>X t\<^sub>X Y s\<^sub>Y t\<^sub>Y Z s\<^sub>Z t\<^sub>Z \<phi> \<psi>

sublocale two_globular_maps \<subseteq> comp: globular_map X s\<^sub>X t\<^sub>X Z s\<^sub>Z t\<^sub>Z "\<lambda>m. \<psi> m \<circ> \<phi> m"
proof (unfold_locales)
  fix m
  show "\<psi> m \<circ> \<phi> m \<in> X m \<rightarrow> Z m" using fst.map_fun snd.map_fun by fastforce
next
  fix x m assume "x \<in> X (Suc m)"
  then show "(\<psi> m \<circ> \<phi> m) (s\<^sub>X m x) = s\<^sub>Z m ((\<psi> (Suc m) \<circ> \<phi> (Suc m)) x)"
    using fst.is_natural_wrt_s snd.is_natural_wrt_s comp_apply fst.map_fun by fastforce
next
  fix x m assume "x \<in> X (Suc m)"
  then show "(\<psi> m \<circ> \<phi> m) (t\<^sub>X m x) = t\<^sub>Z m ((\<psi> (Suc m) \<circ> \<phi> (Suc m)) x)"
    using fst.is_natural_wrt_t snd.is_natural_wrt_t comp_apply fst.map_fun by fastforce
qed

sublocale two_globular_maps \<subseteq> compose: globular_map X s\<^sub>X t\<^sub>X Z s\<^sub>Z t\<^sub>Z "\<lambda>m. \<psi> m \<circ> \<phi> m \<down> X m"
proof (unfold_locales)
  fix m
  show "\<psi> m \<circ> \<phi> m \<down> X m \<in> X m \<rightarrow> Z m" using funcset_compose fst.map_fun snd.map_fun by fast
next
  fix x m assume "x \<in> X (Suc m)"
  then show "(\<psi> m \<circ> \<phi> m \<down> X m) (s\<^sub>X m x) = s\<^sub>Z m ((\<psi> (Suc m) \<circ> \<phi> (Suc m) \<down> X (Suc m)) x)"
    by (metis PiE fst.is_natural_wrt_s snd.is_natural_wrt_s fst.map_fun compose_eq fst.source.s_fun)
next
  fix x m assume "x \<in> X (Suc m)"
  then show "(\<psi> m \<circ> \<phi> m \<down> X m) (t\<^sub>X m x) = t\<^sub>Z m ((\<psi> (Suc m) \<circ> \<phi> (Suc m) \<down> X (Suc m)) x)"
    by (metis PiE fst.is_natural_wrt_t snd.is_natural_wrt_t fst.map_fun compose_eq fst.source.t_fun)
qed

subsection \<open>The terminal globular set\<close>

text \<open>The terminal globular set, with a unique m-cell for each m \cite[p. 264]{Leinster2004}.\<close>

interpretation final_glob: globular_set "\<lambda>m. {()}" "\<lambda>m. id" "\<lambda>m. id"
  by (unfold_locales, auto)

context globular_set
begin

text \<open>\cite[p. 272]{Leinster2004}\<close>

interpretation map_to_final_glob: globular_map X s t
  "\<lambda>m. {()}" "\<lambda>m. id" "\<lambda>m. id"
  "\<lambda>m. (\<lambda>x. ())"
  by (unfold_locales, simp_all)

end

end