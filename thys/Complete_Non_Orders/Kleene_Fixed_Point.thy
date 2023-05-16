theory Kleene_Fixed_Point
  imports Complete_Relations Continuity
begin


section \<open>Iterative Fixed Point Theorem\<close>

text \<open>Kleene's fixed-point theorem states that,
for a pointed directed complete partial order $\tp{A,\SLE}$
and a Scott-continuous map $f: A \to A$,
the supremum of $\set{f^n(\bot) \mid n\in\Nat}$ exists in $A$ and is a least 
fixed point.
Mashburn \cite{mashburn83} generalized the result so that
$\tp{A,\SLE}$ is a $\omega$-complete partial order
and $f$ is $\omega$-continuous.

In this section we further generalize the result and show that
for $\omega$-complete relation $\tp{A,\SLE}$
and for every bottom element $\bot \in A$,
the set $\set{f^n(\bot) \mid n\in\Nat}$ has suprema (not necessarily unique, of 
course) and, 
they are quasi-fixed points.
Moreover, if $(\SLE)$ is attractive, then the suprema are precisely the least 
quasi-fixed points.\<close>

subsection \<open>Existence of Iterative Fixed Points\<close>

text \<open>The first part of Kleene's theorem demands to prove that the set 
$\set{f^n(\bot) \mid n \in \Nat}$ has a supremum and 
that all such are quasi-fixed points. We prove this claim without assuming 
anything on the relation $\SLE$ besides $\omega$-completeness and one bottom element.\<close>

notation compower ("_^_"[1000,1000]1000)

lemma monotone_on_funpow: assumes f: "f ` A \<subseteq> A" and mono: "monotone_on A r r f"
  shows "monotone_on A r r (f^n)"
proof (induct n)
  case 0
  show ?case using monotone_on_id by (auto simp: id_def)
next
  case (Suc n)
  with funpow_dom[OF f] show ?case
    by (auto intro!: monotone_onI monotone_onD[OF mono] elim!:monotone_onE)
qed

no_notation bot ("\<bottom>")

context
  fixes A and less_eq (infix "\<sqsubseteq>" 50) and bot ("\<bottom>") and f
  assumes bot: "\<bottom> \<in> A" "\<forall>q \<in> A. \<bottom> \<sqsubseteq> q"
  assumes cont: "omega_chain-continuous A (\<sqsubseteq>) A (\<sqsubseteq>) f"
begin

interpretation less_eq_symmetrize.

private lemma f: "f ` A \<subseteq> A" using cont by auto

private abbreviation(input) "Fn \<equiv> {f^n \<bottom> |. n :: nat}"

private lemma fn_ref: "f^n \<bottom> \<sqsubseteq> f^n \<bottom>" and fnA: "f^n \<bottom> \<in> A"
proof (atomize(full), induct n)
  case 0
  from bot show ?case by simp
next
  case (Suc n)
  then have fn: "f^n \<bottom> \<in> A" and fnfn: "f^n \<bottom> \<sqsubseteq> f^n \<bottom>" by auto
  from f fn omega_continuous_imp_mono_refl[OF cont fnfn fnfn fnfn]
  show ?case by auto
qed

private lemma FnA: "Fn \<subseteq> A" using fnA by auto

private lemma Fn_chain: "omega_chain Fn (\<sqsubseteq>)"
proof (intro omega_chainI)
  show fn_monotone: "monotone (\<le>) (\<sqsubseteq>) (\<lambda>n. f^n \<bottom>)"
  proof
    fix n m :: nat
    assume "n \<le> m"
    from le_Suc_ex[OF this] obtain k where m: "m = n + k" by auto
    from bot fn_ref fnA omega_continuous_imp_mono_refl[OF cont]
    show "f^n \<bottom> \<sqsubseteq> f^m \<bottom>" by (unfold m, induct n, auto)
  qed
qed auto

private lemma Fn: "Fn = range (\<lambda>n. f^n \<bottom>)" by auto

theorem kleene_qfp:
  assumes q: "extreme_bound A (\<sqsubseteq>) Fn q"
  shows "f q \<sim> q"
proof
  have fq: "extreme_bound A (\<sqsubseteq>) (f ` Fn) (f q)"
    apply (rule continuousD[OF cont _ _ FnA q])
    using Fn_chain by auto
  with bot have nq: "f^n \<bottom> \<sqsubseteq> f q" for n by (induct n, auto simp: extreme_bound_iff)
  then show "q \<sqsubseteq> f q" using f q by blast
  have "f (f^n \<bottom>) \<in> Fn" for n by (auto intro!: exI[of _ "Suc n"])
  then have "f ` Fn \<subseteq> Fn" by auto
  from extreme_bound_subset[OF this fq q]
  show "f q \<sqsubseteq> q".
qed

lemma ex_kleene_qfp:
  assumes comp: "omega_chain-complete A (\<sqsubseteq>)"
  shows "\<exists>p. extreme_bound A (\<sqsubseteq>) Fn p"
  apply (intro comp[THEN completeD, OF FnA])
  using Fn_chain
  by auto

subsection \<open>Iterative Fixed Points are Least.\<close>
text \<open>Kleene's theorem also states that the quasi-fixed point found this way is a least one.
Again, attractivity is needed to prove this statement.\<close>

lemma kleene_qfp_is_least:
  assumes attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes q: "extreme_bound A (\<sqsubseteq>) Fn q"
  shows "extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>) q"
proof(safe intro!: extremeI kleene_qfp[OF q])
  from q
  show "q \<in> A" by auto
  fix c assume c: "c \<in> A" and cqfp: "f c \<sim> c"
  {
    fix n::nat
    have "f^n \<bottom> \<sqsubseteq> c"
    proof(induct n)
      case 0
      show ?case using bot c by auto
    next
      case IH: (Suc n)
      have "c \<sqsubseteq> c" using attract cqfp c by auto
      with IH have "f^(Suc n) \<bottom> \<sqsubseteq> f c"
        using omega_continuous_imp_mono_refl[OF cont] fn_ref fnA c by auto
      then show ?case using attract cqfp c fnA by blast
    qed
  }
  then show "q \<sqsubseteq> c" using q c by auto
qed

lemma kleene_qfp_iff_least:
  assumes comp: "omega_chain-complete A (\<sqsubseteq>)"
  assumes attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes dual_attract: "\<forall>p \<in> A. \<forall>q \<in> A. \<forall>x \<in> A. p \<sim> q \<longrightarrow> q \<sqsubseteq> x \<longrightarrow> p \<sqsubseteq> x"
  shows "extreme_bound A (\<sqsubseteq>) Fn = extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>)"
proof (intro ext iffI kleene_qfp_is_least[OF attract])
  fix q
  assume q: "extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>) q"
  from q have qA: "q \<in> A" by auto
  from q have qq: "q \<sqsubseteq> q" by auto
  from q have fqq: "f q \<sim> q" by auto
  from ex_kleene_qfp[OF comp]
  obtain k where k: "extreme_bound A (\<sqsubseteq>) Fn k" by auto
  have qk: "q \<sim> k"
  proof
    from kleene_qfp[OF k] q k
    show "q \<sqsubseteq> k" by auto
    from kleene_qfp_is_least[OF _ k] q attract
    show "k \<sqsubseteq> q" by blast
  qed
  show "extreme_bound A (\<sqsubseteq>) Fn q"
  proof (intro extreme_boundI,safe)
    fix n
    show "f^n \<bottom> \<sqsubseteq> q"
    proof (induct n)
      case 0
      from bot q show ?case by auto 
    next
      case S:(Suc n)
      from fnA f have fsnbA: "f (f^n \<bottom>) \<in> A" by auto
      have fnfn: "f^n \<bottom> \<sqsubseteq> f^n \<bottom>" using fn_ref by auto
      have "f (f^n \<bottom>) \<sqsubseteq> f q"
        using omega_continuous_imp_mono_refl[OF cont] fnA qA S fnfn qq by auto
      then show ?case using fsnbA qA attract fqq by auto
    qed
  next
    fix x
    assume "bound Fn (\<sqsubseteq>) x" and x: "x \<in> A"
    with k have kx: "k \<sqsubseteq> x" by auto
    with dual_attract[rule_format, OF _ _ x qk] q k
    show "q \<sqsubseteq> x" by auto
  next
    from q show "q \<in> A" by auto
  qed
qed

end

context attractive begin

interpretation less_eq_dualize + less_eq_symmetrize.

theorem kleene_qfp_is_dual_extreme:
  assumes comp: "omega_chain-complete A (\<sqsubseteq>)"
    and cont: "omega_chain-continuous A (\<sqsubseteq>) A (\<sqsubseteq>) f" and bA: "b \<in> A" and bot: "\<forall>x \<in> A. b \<sqsubseteq> x"
  shows "extreme_bound A (\<sqsubseteq>) {f^n b |. n :: nat} = extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>)"
  apply (rule kleene_qfp_iff_least[OF bA bot cont comp])
  using continuous_carrierD[OF cont]
  by (auto dest: sym_order_trans order_sym_trans)

end

corollary(in antisymmetric) kleene_fp:
  assumes cont: "omega_chain-continuous A (\<sqsubseteq>) A (\<sqsubseteq>) f"
    and b: "b \<in> A" "\<forall>x \<in> A. b \<sqsubseteq> x"
    and p: "extreme_bound A (\<sqsubseteq>) {f^n b |. n :: nat} p"
  shows "f p = p"
  using kleene_qfp[OF b cont] p cont[THEN continuous_carrierD]
  by (auto 2 3 intro!:antisym)

no_notation compower ("_^_"[1000,1000]1000)

end