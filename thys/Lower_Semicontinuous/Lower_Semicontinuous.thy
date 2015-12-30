(*  Title:     thys/Lower_Semicontinuous/Lower_Semicontinuous.thy
    Author:    Bogdan Grechuk, University of Edinburgh
*)

section {* Lower semicontinuous functions *}

theory Lower_Semicontinuous
imports Multivariate_Analysis
begin

subsection{* Relative interior in one dimension *}

lemma rel_interior_ereal_semiline:
  fixes a :: ereal
  shows "rel_interior {y. a \<le> ereal y} = {y. a < ereal y}"
proof (cases a)
  case (real r) then show ?thesis
    using rel_interior_real_semiline[of r]
    by (simp add: atLeast_def greaterThan_def)
next case PInf thus ?thesis using rel_interior_empty by auto
next case MInf thus ?thesis using rel_interior_univ2 by auto
qed

lemma closed_ereal_semiline:
  fixes a :: ereal
  shows "closed {y. a \<le> ereal y}"
proof (cases a)
  case (real r) then show ?thesis
    using closed_real_atLeast unfolding atLeast_def by simp
qed auto

lemma ereal_semiline_unique:
  fixes a b :: ereal
  shows "{y. a \<le> ereal y} = {y. b \<le> ereal y} \<longleftrightarrow> a = b"
by (metis mem_Collect_eq ereal_le_real order_antisym)

subsection {* Lower and upper semicontinuity *}

definition
  lsc_at :: "'a \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::order_topology) \<Rightarrow> bool" where
  "lsc_at x0 f \<longleftrightarrow> (\<forall>X l. X \<longlonglongrightarrow> x0 \<and> (f \<circ> X) \<longlonglongrightarrow> l \<longrightarrow> f x0 \<le> l)"

definition
  usc_at :: "'a \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::order_topology) \<Rightarrow> bool" where
  "usc_at x0 f \<longleftrightarrow> (\<forall>X l. X \<longlonglongrightarrow> x0 \<and> (f \<circ> X) \<longlonglongrightarrow> l \<longrightarrow> l \<le> f x0)"

lemma lsc_at_mem:
assumes "lsc_at x0 f"
assumes "x \<longlonglongrightarrow> x0"
assumes "(f o x) \<longlonglongrightarrow> A"
shows "f x0 <= A"
using assms lsc_at_def[of x0 f] by blast


lemma usc_at_mem:
assumes "usc_at x0 f"
assumes "x \<longlonglongrightarrow> x0"
assumes "(f o x) \<longlonglongrightarrow> A"
shows "f x0 >= A"
using assms usc_at_def[of x0 f] by blast

lemma lsc_at_open:
  fixes f :: "'a::first_countable_topology \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  shows "lsc_at x0 f \<longleftrightarrow>
    (\<forall>S. open S \<and> f x0 \<in> S \<longrightarrow> (\<exists>T. open T \<and> x0 \<in> T \<and> (\<forall>x'\<in>T. f x' \<le> f x0 \<longrightarrow> f x' \<in> S)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "~?rhs"
  from this obtain S where S_def:
     "open S & f x0 : S & (ALL T. (open T & x0 : T) --> (EX x':T. f x' <= f x0 & f x' ~: S))" by metis
  def X == "{x'. f x' <= f x0 & f x' ~: S}" hence "x0 islimpt X" unfolding islimpt_def using S_def by auto
  from this obtain x where x_def: "(ALL n. x n : X) & x \<longlonglongrightarrow> x0"
     using islimpt_sequential[of x0 X] by auto
  hence not: "~(f o x) \<longlonglongrightarrow> (f x0)" unfolding tendsto_explicit using X_def S_def by auto
  from compact_complete_linorder[of "f o x"] obtain l r where r_def: "subseq r & ((f o x) o r) \<longlonglongrightarrow> l" by auto
  { assume "l : S" hence "EX N. ALL n>=N. f(x(r n)) : S"
       using r_def tendsto_explicit[of "f o x o r" l] S_def by auto
    hence False using x_def X_def by auto
  } hence l_prop: "l ~: S & l<=f x0"
    using r_def x_def X_def Lim_bounded_ereal[of "f \<circ> x \<circ> r"]
    by auto
  { assume "f x0 <= l" hence "f x0 = l" using l_prop by auto
    hence False using l_prop S_def by auto
  }
  hence "EX x l. x \<longlonglongrightarrow> x0 & (f o x) \<longlonglongrightarrow> l & ~(f x0 <= l)"
     apply(rule_tac x="x o r" in exI) apply(rule_tac x=l in exI)
     using r_def x_def by (auto simp add: o_assoc lim_subseq)
  hence "~?lhs" unfolding lsc_at_def by blast
}
moreover
{ assume "?rhs"
 { fix x A assume x_def: "x \<longlonglongrightarrow> x0" "(f o x) \<longlonglongrightarrow> A"
   { assume "A ~= f x0"
     from this obtain S V where SV_def: "open S & open V & f x0 : S & A : V & S Int V = {}"
        using hausdorff[of "f x0" A] by auto
     from this obtain T where T_def: "open T & x0 : T & (ALL x':T. (f x' <= f x0 --> f x' : S))"
       using `?rhs` by metis
     from this obtain N1 where "ALL n>=N1. x n : T" using x_def tendsto_explicit[of x x0] by auto
     hence *: "ALL n>=N1. (f (x n) <= f x0 --> f(x n) : S)" using T_def by auto
     from SV_def obtain N2 where "ALL n>=N2. f(x n) : V"
        using tendsto_explicit[of "f o x" A] x_def by auto
     hence "ALL n>=(max N1 N2). ~(f(x n) <= f x0)" using SV_def * by auto
     hence "ALL n>=(max N1 N2). f(x n) >= f x0" by auto
     hence "f x0 <= A" using Lim_bounded2_ereal[of "f o x" A "max N1 N2" "f x0"] x_def by auto
   } hence "f x0 <= A" by auto
 } hence "?lhs" unfolding lsc_at_def by blast
} ultimately show ?thesis by blast
qed


lemma lsc_at_open_mem:
  fixes f :: "'a::first_countable_topology \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
assumes "lsc_at x0 f"
assumes "open S & f x0 : S"
obtains T where "open T & x0 : T & (ALL x':T. (f x' <= f x0 --> f x' : S))"
using assms lsc_at_open[of x0 f] by blast


lemma lsc_at_MInfty:
  fixes f :: "'a::topological_space => ereal"
  assumes "f x0 = -\<infinity>"
  shows "lsc_at x0 f"
unfolding lsc_at_def using assms by auto


lemma lsc_at_PInfty:
fixes f :: "'a::metric_space => ereal"
assumes "f x0 = \<infinity>"
shows "lsc_at x0 f \<longleftrightarrow> continuous (at x0) f"
unfolding lsc_at_open continuous_at_open using assms by auto


lemma lsc_at_real:
fixes f :: "'a::metric_space => ereal"
assumes "\<bar>f x0\<bar> \<noteq> \<infinity>"
shows "lsc_at x0 f \<longleftrightarrow> (!e. e>0 --> (EX T. open T & x0 : T & (!y : T. f y > f x0 - e)))"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
obtain m where m_def: "f x0 = ereal m" using assms by (cases "f x0") auto
{ assume lsc: "lsc_at x0 f"
  { fix e assume e_def: "(e :: ereal)>0"
    hence *: "f x0 : {f x0 - e <..< f x0 + e}" using assms ereal_between by auto
    from this obtain T where T_def: "open T & x0 : T & (ALL x':T. f x' <= f x0 --> f x' : {f x0 - e <..< f x0 + e})"
       apply (subst lsc_at_open_mem[of x0 f "{f x0 - e <..< f x0 + e}"]) using lsc e_def by auto
    { fix y assume "y:T"
      { assume "f y <= f x0" hence "f y >  f x0 - e" using T_def `y:T` by auto }
      moreover
      { assume "f y > f x0" hence "...>f x0 - e" using * by auto }
      ultimately have "f y >  f x0 - e" using not_le by blast
    } hence "EX T. open T & x0 : T & (!y : T. f y > f x0 - e)" using T_def by auto
  } hence "?rhs" by auto
}
moreover
{ assume "?rhs"
  { fix S assume S_def: "open S & f x0 : S"
    from this obtain e where e_def: "e>0 & {f x0 - e<..<f x0 + e} <= S"
      apply (subst ereal_open_cont_interval[of S "f x0"]) using assms by auto
    from this obtain T where T_def: "open T & x0 : T & (!y : T. f y > f x0 - e)"
        using `?rhs`[rule_format, of e] by auto
    { fix y assume "y:T" "f y <= f x0" hence "f y < f x0 + e"
         using assms e_def ereal_between[of "f x0" e] by auto
      hence "f y : S" using e_def T_def `y:T` by auto
    } hence "EX T. open T & x0 : T & (ALL y:T. (f y <= f x0 --> f y : S))" using T_def by auto
  } hence "lsc_at x0 f" using lsc_at_open by auto
} ultimately show ?thesis by auto
qed


lemma lsc_at_ereal:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 f \<longleftrightarrow> (ALL C<f(x0). EX T. open T & x0 : T & (!y : T. f y > C))"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "f x0 = -\<infinity>" hence ?thesis using lsc_at_MInfty by auto }
moreover
{ assume pinf: "f x0 = \<infinity>"
  { assume lsc: "lsc_at x0 f"
    { fix C assume "C<f x0"
      hence "open {C<..} & f x0 : {C<..}" by auto
      from this obtain T where T_def: "open T & x0 : T & (ALL y:T. f y : {C<..})"
         using pinf lsc lsc_at_PInfty[of f x0] unfolding continuous_at_open by metis
      hence "EX T. open T & x0 : T & (ALL y:T. C < f y)" by auto
    } hence "?rhs" by auto
  }
  moreover
  { assume "?rhs"
    { fix S assume S_def: "open S & f x0 : S"
      then obtain C where C_def: "ereal C < f x0 & {ereal C<..} <= S" using pinf open_PInfty by auto
      then obtain T where T_def: "open T & x0 : T & (!y : T. f y : S)"
        using `?rhs`[rule_format, of "ereal C"] by auto
      hence "EX T. open T & x0 : T & (ALL y:T. (f y <= f x0 --> f y : S))" using T_def by auto
    } hence "lsc_at x0 f" using lsc_at_open by auto
  } ultimately have ?thesis by blast
}
moreover
{ assume fin: "f x0 ~= -\<infinity>" "f x0 ~= \<infinity>"
  { assume lsc: "lsc_at x0 f"
    { fix C assume "C<f x0"
      hence "f x0-C>0" using fin ereal_less_minus_iff by auto
      from this obtain T where T_def: "open T & x0 : T & (ALL y:T. f x0 - (f x0-C) < f y)"
         using lsc_at_real[of f x0] lsc fin by auto
      moreover have "f x0 - (f x0-C) = C" using fin apply (cases "f x0", cases C) by auto
      ultimately have "EX T. open T & x0 : T & (ALL y:T. C < f y)" by auto
    } hence "?rhs" by auto
  }
  moreover
  { assume "?rhs"
    { fix e :: ereal assume "e>0"
      hence "f x0 - e < f x0" using fin apply (cases "f x0", cases e) by auto
      hence "EX T. open T & x0 : T & (ALL y:T. f x0 - e < f y)" using fin `?rhs` by auto
    } hence "lsc_at x0 f" using lsc_at_real[of f x0] fin by auto
  } ultimately have ?thesis by blast
} ultimately show ?thesis by blast
qed


lemma lst_at_ball:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 f \<longleftrightarrow> (ALL C<f(x0). EX d>0. ALL y : (ball x0 d). C<f(y))"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume lsc: "lsc_at x0 f"
  { fix C :: ereal assume "C<f x0"
    from this obtain T where "open T & x0 : T & (!y : T. C < f y)"
      using lsc lsc_at_ereal[of x0 f] by auto
    hence "EX d. d>0 & (!y : (ball x0 d). C < f y)"
      by (force simp add: open_contains_ball)
  }
}
moreover
{ assume "?rhs"
  { fix C :: ereal assume "C<f x0"
    from this obtain d where "d>0 & (!y : (ball x0 d). C < f y)" using `?rhs` by auto
    hence "EX T. open T & x0 : T & (!y : T. C < f y)" apply (rule_tac x="ball x0 d" in exI)
      apply (simp add: centre_in_ball) done
  } hence "lsc_at x0 f" using assms lsc_at_ereal[of x0 f] by auto
}
ultimately show ?thesis by auto
qed


lemma lst_at_delta:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 f \<longleftrightarrow> (ALL C<f(x0). EX d>0. !y. dist x0 y < d --> C < f y)"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have "?rhs \<longleftrightarrow> (ALL C<f(x0). EX d>0. ALL y : (ball x0 d). C < f y)" unfolding ball_def by auto
  thus ?thesis using lst_at_ball[of x0 f] by auto
qed


lemma lsc_liminf_at:
  fixes f :: "'a::metric_space => ereal"
  shows "lsc_at x0 f \<longleftrightarrow> f x0 \<le> Liminf (at x0) f"
  unfolding lst_at_ball le_Liminf_iff eventually_at
  by (intro arg_cong[where f=All] imp_cong refl ext ex_cong)
     (auto simp: dist_commute zero_less_dist_iff)


lemma lsc_liminf_at_eq:
  fixes f :: "'a::metric_space => ereal"
  shows "lsc_at x0 f \<longleftrightarrow> (f x0 = min (f x0) (Liminf (at x0) f))"
by (metis inf_ereal_def le_iff_inf lsc_liminf_at)


lemma lsc_imp_liminf:
fixes f :: "'a::metric_space => ereal"
assumes "lsc_at x0 f"
assumes "x \<longlonglongrightarrow> x0"
shows "f x0 <= liminf (f o x)"
proof (cases "f x0")
  case PInf then show ?thesis using assms lsc_at_PInfty[of f x0] lim_imp_Liminf[of _ "f \<circ> x"]
    continuous_at_sequentially[of x0 f] by auto
next
  case (real r)
  { fix e assume e_def: "(e :: ereal)>0"
    from this obtain T where T_def: "open T & x0 : T & (!y : T. f y > f x0 - e)"
       using lsc_at_real[of f x0] real assms by auto
    from this obtain N where N_def: "ALL n>=N. x n : T"
       apply (subst tendsto_obtains_N[of x x0 T]) using assms by auto
    hence "ALL n>=N. f x0 - e < (f o x) n" using T_def by auto
    hence "liminf (f o x) >= f x0 - e" by (intro Liminf_bounded) (auto simp: eventually_sequentially intro!: exI[of _ N])
    hence "f x0 <= liminf (f o x) + e" apply (cases e) unfolding ereal_minus_le_iff by auto
  }
  then show ?thesis by (intro ereal_le_epsilon) auto
qed auto

lemma lsc_liminf:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 f \<longleftrightarrow> (!x. x \<longlonglongrightarrow> x0 --> f x0 <= liminf (f o x))"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "?rhs"
  { fix x A assume x_def: "x \<longlonglongrightarrow> x0" "(f o x) \<longlonglongrightarrow> A"
    hence "f x0 <= A" using `?rhs` lim_imp_Liminf[of sequentially] by auto
  } hence "?lhs" unfolding lsc_at_def by blast
} from this show ?thesis using lsc_imp_liminf by auto
qed


lemma lsc_sequentially:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 f \<longleftrightarrow> (ALL x c. x \<longlonglongrightarrow> x0 & (ALL n. f(x n)<=c) --> f(x0)<=c)"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "?rhs"
  { fix x l assume "x \<longlonglongrightarrow> x0" "(f o x) \<longlonglongrightarrow> l"
    { assume "l = \<infinity>" hence "f x0 <= l" by auto }
    moreover
    { assume "l = -\<infinity>"
      { fix B :: real obtain N where N_def: "ALL n>=N. f(x n) <= ereal B"
           using Lim_MInfty[of "f o x"] `(f o x) \<longlonglongrightarrow> l` `l = -\<infinity>` by auto
        def g == "(%n. if n>=N then x n else x N)"
        hence "g \<longlonglongrightarrow> x0"
          by (intro filterlim_cong[THEN iffD1, OF refl refl _ `x \<longlonglongrightarrow> x0`])
             (auto simp: eventually_sequentially)
        moreover have "ALL n. f(g n) <= ereal B" using g_def N_def by auto
        ultimately have "f x0 <= ereal B" using `?rhs` by auto
      } hence "f x0 = -\<infinity>" using ereal_bot by auto
      hence "f x0 <= l" by auto }
    moreover
    { assume fin: "\<bar>l\<bar> \<noteq> \<infinity>"
      { fix e assume e_def: "(e :: ereal)>0"
        from this obtain N where N_def: "ALL n>=N. f(x n) : {l - e <..< l + e}"
           apply (subst tendsto_obtains_N[of "f o x" l "{l - e <..< l + e}"])
           using fin e_def ereal_between `(f o x) \<longlonglongrightarrow> l` by auto
        def g == "(%n. if n>=N then x n else x N)"
        hence "g \<longlonglongrightarrow> x0"
          by (intro filterlim_cong[THEN iffD1, OF refl refl _ `x \<longlonglongrightarrow> x0`])
             (auto simp: eventually_sequentially)
        moreover have "ALL n. f(g n) <= l + e" using g_def N_def by auto
        ultimately have "f x0 <= l + e" using `?rhs` by auto
      } hence "f x0 <= l" using ereal_le_epsilon by auto
    } ultimately have "f x0 <= l" by blast
  } hence "lsc_at x0 f" unfolding lsc_at_def by auto
}
moreover
{ assume lsc: "lsc_at x0 f"
  { fix x c assume xc_def: "x \<longlonglongrightarrow> x0 & (ALL n. f(x n)<=c)"
    hence "liminf (f o x) <= c" using Limsup_bounded[of sequentially "f o x" c] Liminf_le_Limsup[of sequentially "f o x"] by auto
    hence "f x0 <= c" using lsc xc_def lsc_imp_liminf[of x0 f x] by auto
  } hence "?rhs" by auto
} ultimately show ?thesis by blast
qed


lemma lsc_sequentially_gen:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 f \<longleftrightarrow> (ALL x c c0. x \<longlonglongrightarrow> x0 & c \<longlonglongrightarrow> c0 & (ALL n. f(x n)<=c n) --> f(x0)<=c0)"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "?rhs"
  { fix x c0 assume a: "x \<longlonglongrightarrow> x0 & (ALL n. f (x n) <= c0)"
    def c == "(%n::nat. c0)" hence "c \<longlonglongrightarrow> c0" by auto
    hence "f(x0)<=c0" using `?rhs`[rule_format, of x c c0] using a c_def by auto
  } hence "?lhs" using lsc_sequentially[of x0 f] by auto
}
moreover
{ assume lsc: "lsc_at x0 f"
  { fix x c c0 assume xc_def: "x \<longlonglongrightarrow> x0 & c \<longlonglongrightarrow> c0 & (ALL n. f(x n)<=c n)"
    hence "liminf (f o x) <= c0" using Liminf_mono[of "f o x" c sequentially] lim_imp_Liminf[of sequentially] by auto
    hence "f x0 <= c0" using lsc xc_def lsc_imp_liminf[of x0 f x] by auto
  } hence "?rhs" by auto
} ultimately show ?thesis by blast
qed


lemma lsc_sequentially_mem:
fixes f :: "'a::metric_space => ereal"
assumes "lsc_at x0 f"
assumes "x \<longlonglongrightarrow> x0" "c \<longlonglongrightarrow> c0"
assumes "ALL n. f(x n)<=c n"
shows "f(x0)<=c0"
using lsc_sequentially_gen[of x0 f] assms by auto


lemma lsc_uminus:
fixes f :: "'a::metric_space => ereal"
shows "lsc_at x0 (%x. -f x) \<longleftrightarrow> usc_at x0 f"
proof-
{ assume lsc: "lsc_at x0 (%x. -f x)"
  { fix x A assume x_def: "x \<longlonglongrightarrow> x0" "(f o x) \<longlonglongrightarrow> A"
    hence "(%i. - f (x i)) \<longlonglongrightarrow> -A" using tendsto_uminus_ereal[of "f o x" A] by auto
    hence "((%x. - f x) o x) \<longlonglongrightarrow> -A" unfolding o_def by auto
    hence " - f x0 <= - A" apply (subst lsc_at_mem[of x0 "(%x. -f x)" x]) using lsc x_def by auto
    hence "f x0 >= A" by auto
  } hence "usc_at x0 f" unfolding usc_at_def by auto
}
moreover
{ assume usc: "usc_at x0 f"
  { fix x A assume x_def: "x \<longlonglongrightarrow> x0" "((%x. - f x) o x) \<longlonglongrightarrow> A"
    hence "(%i. - f (x i)) \<longlonglongrightarrow> A" unfolding o_def by auto
    hence "(%i. f (x i)) \<longlonglongrightarrow> - A" using tendsto_uminus_ereal[of "(%i. - f (x i))" A] by auto
    hence "(f o x) \<longlonglongrightarrow> -A" unfolding o_def by auto
    hence "f x0 >= - A" apply (subst usc_at_mem[of x0 "f" x]) using usc x_def by auto
    hence "-f x0 <= A" unfolding ereal_uminus_le_reorder by auto
  } hence "lsc_at x0 (%x. -f x)" unfolding lsc_at_def by auto
} ultimately show ?thesis by blast
qed


lemma usc_limsup:
fixes f :: "'a::metric_space => ereal"
shows "usc_at x0 f \<longleftrightarrow> (!x. x \<longlonglongrightarrow> x0 --> f x0 >= limsup (f o x))"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
have "usc_at x0 f \<longleftrightarrow> (ALL x. x \<longlonglongrightarrow> x0 --> - f x0 <= liminf ((%x. - f x) o x))"
  using lsc_uminus[of x0 f] lsc_liminf[of x0 "(%x. - f x)"] by auto
moreover
{ fix x assume "x \<longlonglongrightarrow> x0"
  have "(-f x0 <= -limsup (f o x)) \<longleftrightarrow> (-f x0 <= liminf ((%x. - f x) o x))"
     using ereal_Liminf_uminus[of _ "f o x"] unfolding o_def by auto
  hence "(f x0 >= limsup (f o x)) \<longleftrightarrow> (-f x0 <= liminf ((%x. - f x) o x))"
     by auto
} ultimately show ?thesis by auto
qed


lemma usc_imp_limsup:
  fixes f :: "'a::metric_space => ereal"
  assumes "usc_at x0 f"
  assumes "x \<longlonglongrightarrow> x0"
  shows "f x0 >= limsup (f o x)"
using assms usc_limsup[of x0 f] by auto


lemma usc_limsup_at:
  fixes f :: "'a::metric_space => ereal"
  shows "usc_at x0 f \<longleftrightarrow> f x0 >= Limsup (at x0) f"
proof-
  have "usc_at x0 f \<longleftrightarrow> lsc_at x0 (%x. -(f x))" by (metis lsc_uminus)
  also have "... \<longleftrightarrow> -(f x0) <= Liminf (at x0) (%x. -(f x))" by (metis lsc_liminf_at)
  also have "... \<longleftrightarrow> -(f x0) <= -(Limsup (at x0) f)" by (metis ereal_Liminf_uminus)
  finally show ?thesis by auto
qed


lemma continuous_iff_lsc_usc:
fixes f :: "'a::metric_space => ereal"
shows "continuous (at x0) f \<longleftrightarrow> (lsc_at x0 f) & (usc_at x0 f)"
proof-
{ assume a: "continuous (at x0) f"
  { fix x assume "x \<longlonglongrightarrow> x0"
    hence "(f o x) \<longlonglongrightarrow> f x0" using a continuous_imp_tendsto[of x0 f x] by auto
    hence "liminf (f o x) = f x0 & limsup (f o x) = f x0"
       using lim_imp_Liminf[of sequentially] lim_imp_Limsup[of sequentially] by auto
  } hence "lsc_at x0 f & usc_at x0 f" unfolding lsc_liminf usc_limsup by auto
}
moreover
{ assume a: "(lsc_at x0 f) & (usc_at x0 f)"
  { fix x assume "x \<longlonglongrightarrow> x0"
    hence "limsup (f o x) <= f x0" using a unfolding usc_limsup by auto
    moreover have "... <= liminf (f o x)" using a `x \<longlonglongrightarrow> x0` unfolding lsc_liminf by auto
    ultimately have "limsup (f o x) = f x0 & liminf (f o x) = f x0"
       using Liminf_le_Limsup[of sequentially "f o x"] by auto
    hence "(f o x) \<longlonglongrightarrow> f x0" using Liminf_eq_Limsup[of sequentially] by auto
  } hence "continuous (at x0) f"
    using continuous_at_sequentially[of x0 f] by auto
} ultimately show ?thesis by blast
qed


lemma continuous_lsc_compose:
  assumes "lsc_at (g x0) f" "continuous (at x0) g"
  shows "lsc_at x0 (f o g)"
proof-
{ fix x L assume "x \<longlonglongrightarrow> x0" "(f o g o x) \<longlonglongrightarrow> L"
  hence "f(g x0) <= L" apply (subst lsc_at_mem[of "g x0" f "g o x" L])
     using assms continuous_imp_tendsto[of x0 g x] unfolding o_def by auto
} from this show ?thesis unfolding lsc_at_def by auto
qed


lemma continuous_isCont:
  "continuous (at x0) f \<longleftrightarrow> isCont f x0"
by (metis continuous_at isCont_def)


lemma isCont_iff_lsc_usc:
  fixes f :: "'a::metric_space => ereal"
  shows "isCont f x0 \<longleftrightarrow> (lsc_at x0 f) & (usc_at x0 f)"
by (metis continuous_iff_lsc_usc continuous_isCont)


definition
  lsc :: "('a::topological_space => 'b::order_topology) => bool" where
  "lsc f \<longleftrightarrow> (!x. lsc_at x f)"

definition
  usc :: "('a::topological_space => 'b::order_topology) => bool" where
  "usc f \<longleftrightarrow> (!x. usc_at x f)"


lemma continuous_UNIV_iff_lsc_usc:
  fixes f :: "'a::metric_space => ereal"
  shows "(ALL x. continuous (at x) f) \<longleftrightarrow> (lsc f) & (usc f)"
by (metis continuous_iff_lsc_usc lsc_def usc_def)


subsection {* Epigraphs *}


definition "Epigraph S (f::_ => ereal) = {xy. fst xy : S & f (fst xy) <= ereal(snd xy)}"


lemma mem_Epigraph: "(x, y) : Epigraph S f \<longleftrightarrow> x : S & f x <= ereal y" unfolding Epigraph_def by auto


lemma ereal_closed_levels:
fixes f :: "'a::metric_space => ereal"
shows "(ALL y. closed {x. f(x)<=y}) \<longleftrightarrow> (ALL r. closed {x. f(x)<=ereal r})"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "?rhs"
  { fix y :: ereal
    { assume "y ~= \<infinity> & y ~= -\<infinity>" hence "closed {x. f(x)<=y}" using `?rhs` by (cases y) auto }
    moreover
    { assume "y=\<infinity>" hence  "closed {x. f(x)<=y}" by auto }
    moreover
    { assume "y=-\<infinity>"
      hence "{x. f(x)<=y} = Inter {{x. f(x)<=ereal r} |r. r : UNIV}" using ereal_bot by auto
      hence "closed {x. f(x)<=y}" using closed_Inter `?rhs` by auto
    } ultimately have "closed {x. f(x)<=y}" by blast
  } hence "?lhs" by auto
} from this show ?thesis by auto
qed


lemma lsc_iff:
fixes f :: "'a::metric_space => ereal"
shows "(lsc f \<longleftrightarrow> (ALL y. closed {x. f(x)<=y})) & (lsc f \<longleftrightarrow> closed (Epigraph UNIV f))"
proof-
{ assume "lsc f"
  { fix z z0 assume a: "ALL n. z n : (Epigraph UNIV f) & z \<longlonglongrightarrow> z0"
    { fix n have "z n : (Epigraph UNIV f)" using a by auto
      hence "f (fst (z n)) <= ereal(snd (z n))" using a unfolding Epigraph_def by auto
      hence "EX xn cn. z n = (xn, cn) & f(xn)<=ereal cn"
         apply (rule_tac x="fst (z n)" in exI) apply (rule_tac x="snd (z n)" in exI) by auto
    } from this obtain x c where xc_def: "ALL n. z n = (x n, c n) & f(x n)<=ereal (c n)" by metis
    from this a have "EX x0 c0. z0 = (x0, c0) & x \<longlonglongrightarrow> x0 & c \<longlonglongrightarrow> c0"
       apply (rule_tac x="fst z0" in exI) apply (rule_tac x="snd z0" in exI)
       using tendsto_fst[of z z0] tendsto_snd[of z z0] by auto
    from this obtain x0 c0 where xc0_def: "z0 = (x0, c0) & x \<longlonglongrightarrow> x0 & c \<longlonglongrightarrow> c0" by auto
    hence "f(x0)<=ereal c0" apply (subst lsc_sequentially_mem[of x0 f x "ereal o c" "ereal c0"])
       using `lsc f` xc_def unfolding lsc_def unfolding o_def by auto
    hence "z0 : (Epigraph UNIV f)" unfolding Epigraph_def using xc0_def by auto
  } hence "closed (Epigraph UNIV f)" by (simp add: closed_sequential_limits)
}
moreover
{ assume "closed (Epigraph UNIV f)"
     hence *: "ALL x l. (ALL n. f (fst (x n)) <= ereal(snd (x n))) & x \<longlonglongrightarrow> l -->
     f (fst l) <= ereal(snd l)" unfolding Epigraph_def closed_sequential_limits by auto
  { fix r :: real
    { fix z z0 assume a: "ALL n. f(z n)<=ereal r & z \<longlonglongrightarrow> z0"
      hence "f(z0)<=ereal r" using *[rule_format, of "(%n. (z n,r))" "(z0,r)"]
         tendsto_Pair[of z z0] by auto
    } hence "closed {x. f(x)<=ereal r}" by (simp add: closed_sequential_limits)
  } hence "ALL y. closed {x. f(x)<=y}" using ereal_closed_levels by auto
}
moreover
{ assume a: "ALL y. closed {x. f(x)<= y}"
  { fix x0
    { fix x l assume "x \<longlonglongrightarrow> x0" "(f o x) \<longlonglongrightarrow> l"
      { assume "l = \<infinity>" hence "f x0 <= l" by auto }
      moreover
      { assume mi: "l = -\<infinity>"
        { fix B :: real
          obtain N where N_def: "ALL n>=N. f(x n)<=ereal B"
             using mi `(f o x) \<longlonglongrightarrow> l` Lim_MInfty[of "f o x"] by auto
          { fix d assume "(d::real)>0"
            from this obtain N1 where N1_def: "ALL n>=N1. dist (x n) x0 < d"
               using `x \<longlonglongrightarrow> x0` unfolding lim_sequentially by auto
            hence "EX y. dist y x0 < d & y : {x. f(x)<=ereal B}"
              apply (rule_tac x="x (max N N1)" in exI) using N_def by auto
          }
          hence "x0 : closure {x. f(x)<=ereal B}" apply (subst closure_approachable) by auto
          hence "f x0 <= ereal B" using a by auto
        } hence "f x0 <= l" using ereal_bot[of "f x0"] by auto
      }
      moreover
      { assume fin: "\<bar>l\<bar> \<noteq> \<infinity>"
        { fix e assume e_def: "(e :: ereal)>0"
          from this obtain N where N_def: "ALL n>=N. f(x n) : {l - e <..< l + e}"
             apply (subst tendsto_obtains_N[of "f o x" l "{l - e <..< l + e}"])
             using fin e_def ereal_between `(f o x) \<longlonglongrightarrow> l` by auto
          hence *: "ALL n>=N. x n : {x. f(x)<=l+e}" using N_def by auto
          { fix d assume "(d::real)>0"
            from this obtain N1 where N1_def: "ALL n>=N1. dist (x n) x0 < d"
               using `x \<longlonglongrightarrow> x0` unfolding lim_sequentially by auto
            hence "EX y. dist y x0 < d & y : {x. f(x)<=l+e}"
              apply (rule_tac x="x (max N N1)" in exI) using * by auto
          }
          hence "x0 : closure {x. f(x)<=l+e}" apply (subst closure_approachable) by auto
          hence "f x0 <= l+e" using a by auto
        } hence "f x0 <= l" using ereal_le_epsilon by auto
      } ultimately have "f x0 <= l" by blast
    } hence "lsc_at x0 f" unfolding lsc_at_def by auto
  } hence "lsc f" unfolding lsc_def by auto
}
ultimately show ?thesis by auto
qed


definition lsc_hull :: "('a::metric_space => ereal) => ('a::metric_space => ereal)" where
  "lsc_hull f = (SOME g. Epigraph UNIV g = closure(Epigraph UNIV f))"


lemma epigraph_mono:
  fixes f :: "'a::metric_space => ereal"
  shows "(x,y):Epigraph UNIV f & y<=z --> (x,z):Epigraph UNIV f"
unfolding Epigraph_def apply auto
using ereal_less_eq(3)[of y z] order_trans_rules(23) by blast



lemma closed_epigraph_lines:
fixes S :: "('a::metric_space * 'b::metric_space) set"
assumes "closed S"
shows "closed {z. (x, z) : S}"
proof-
{ fix z assume z_def: "z : closure {z. (x, z) : S}"
  { fix e :: real assume "e>0"
    from this obtain y where y_def: "(x,y) : S & dist y z < e"
       using closure_approachable[of z "{z. (x, z) : S}"] z_def by auto
    moreover have "dist (x,y) (x,z) = dist y z" unfolding dist_prod_def by auto
    ultimately have "EX s. s : S & dist s (x,z) < e" apply(rule_tac x="(x,y)" in exI) by auto
  } hence "(x,z):S" using closed_approachable[of S "(x,z)"] assms by auto
} hence "closure {z. (x, z) : S} <= {z. (x, z) : S}" by blast
from this show ?thesis using closure_subset_eq by auto
qed


lemma mono_epigraph:
  fixes S :: "('a::metric_space * real) set"
  assumes mono: "ALL x y z. (x,y):S & y<=z --> (x,z):S"
  assumes "closed S"
  shows "EX g. ((Epigraph UNIV g) = S)"
proof-
{ fix x
  have "closed {z. (x, z) : S}" using `closed S` closed_epigraph_lines by auto
  hence "EX a. {z. (x, z) : S} = {z. a <= ereal z}" apply (subst mono_closed_ereal) using mono by auto
} from this obtain g where g_def: "ALL x. {z. (x, z) : S} = {z. g x <= ereal z}" by metis
{ fix s
  have "s:S \<longleftrightarrow> (fst s, snd s) : S" by auto
  also have "... \<longleftrightarrow> g(fst s) <= ereal (snd s)" using g_def[rule_format, of "fst s"] by blast
  finally have "s:S \<longleftrightarrow> g(fst s) <= ereal (snd s)" by auto
}
hence "(Epigraph UNIV g) = S" unfolding Epigraph_def by auto
from this show ?thesis by auto
qed


lemma lsc_hull_exists:
  fixes f :: "'a::metric_space => ereal"
  shows "EX g. Epigraph UNIV g = closure (Epigraph UNIV f)"
proof-
{ fix x y z assume xy: "(x,y):closure (Epigraph UNIV f) & y<=z"
  { fix e :: real assume "e>0"
    hence "EX ya:Epigraph UNIV f. dist ya (x, y) < e"
      using xy closure_approachable[of "(x,y)" "Epigraph UNIV f"] by auto
    from this obtain a b where ab: "(a,b):Epigraph UNIV f & dist (a,b) (x,y) < e" by auto
    moreover have "dist (a,b) (x,y) = dist (a,b+(z-y)) (x,z)"
      unfolding dist_prod_def dist_norm by (simp add: algebra_simps)
    moreover have "(a,b+(z-y)):Epigraph UNIV f" apply (subst epigraph_mono[of _ b]) using ab xy by auto
    ultimately have "EX w:Epigraph UNIV f. dist w (x, z) < e" by auto
  } hence "(x,z):closure (Epigraph UNIV f)" using closure_approachable by auto
}
hence "ALL x y z. (x,y): closure (Epigraph UNIV f) & y<=z --> (x,z): closure (Epigraph UNIV f)" by auto
from this show ?thesis using mono_epigraph[of "closure (Epigraph UNIV f)"] by auto
qed


lemma epigraph_invertible:
  assumes "Epigraph UNIV f = Epigraph UNIV g"
  shows "f=g"
proof-
{ fix x
  { fix C have "f x <= ereal C \<longleftrightarrow> (x,C) : Epigraph UNIV f" unfolding Epigraph_def by auto
    also have "... \<longleftrightarrow> (x,C) : Epigraph UNIV g" using assms by auto
    also have "... \<longleftrightarrow> g x <= ereal C" unfolding Epigraph_def by auto
    finally have "f x <= ereal C \<longleftrightarrow> g x <= ereal C" by auto
  } hence "g x = f x" using ereal_le_real[of "g x" "f x"] ereal_le_real[of "f x" "g x"] by auto
} from this show ?thesis by (simp add: ext)
qed


lemma lsc_hull_ex_unique:
  fixes f :: "'a::metric_space => ereal"
  shows "EX! g. Epigraph UNIV g = closure (Epigraph UNIV f)"
using lsc_hull_exists epigraph_invertible by metis


lemma epigraph_lsc_hull:
  fixes f :: "'a::metric_space => ereal"
  shows "Epigraph UNIV (lsc_hull f) = closure(Epigraph UNIV f)"
proof-
have "EX g. Epigraph UNIV g = closure (Epigraph UNIV f)" using lsc_hull_exists by auto
thus ?thesis unfolding lsc_hull_def
   using some_eq_ex[of "(%g. Epigraph UNIV g = closure(Epigraph UNIV f))"] by auto
qed


lemma lsc_hull_expl:
  "(g = lsc_hull f) \<longleftrightarrow> (Epigraph UNIV g = closure(Epigraph UNIV f))"
proof-
{ assume "Epigraph UNIV g = closure(Epigraph UNIV f)"
  hence "lsc_hull f = g" unfolding lsc_hull_def apply (subst some1_equality[of _ g])
    using lsc_hull_ex_unique by metis+
}
from this show ?thesis using epigraph_lsc_hull by auto
qed


lemma lsc_lsc_hull: "lsc (lsc_hull f)"
   using epigraph_lsc_hull[of f] lsc_iff[of "lsc_hull f"] by auto


lemma epigraph_subset_iff:
  fixes f g :: "'a::metric_space => ereal"
  shows "Epigraph UNIV f <= Epigraph UNIV g \<longleftrightarrow> (ALL x. g x <= f x)"
proof-
{ assume epi: "Epigraph UNIV f <= Epigraph UNIV g"
  { fix x
    { fix z assume "f x <= ereal z"
      hence "(x,z):Epigraph UNIV f" unfolding Epigraph_def by auto
      hence "(x,z):Epigraph UNIV g" using epi by auto
      hence "g x <= ereal z" unfolding Epigraph_def by auto
    } hence "g x <= f x" apply (subst ereal_le_real) by auto
  }
}
moreover
{ assume le: "ALL x. g x <= f x"
  { fix x y assume "(x,y):Epigraph UNIV f"
    hence "f x <= ereal y" unfolding Epigraph_def by auto
    moreover have "g x <= f x" using le by auto
    ultimately have "g x <= ereal y" by auto
    hence "(x,y):Epigraph UNIV g" unfolding Epigraph_def by auto
  }
}
ultimately show ?thesis by auto
qed


lemma lsc_hull_le: "(lsc_hull f) x <= f x"
  using epigraph_lsc_hull[of f] closure_subset epigraph_subset_iff[of f "lsc_hull f"] by auto


lemma lsc_hull_greatest:
fixes f g :: "'a::metric_space => ereal"
assumes "lsc g" "ALL x. g x <= f x"
shows "ALL x. g x <= (lsc_hull f) x"
proof-
have "closure(Epigraph UNIV f) <= Epigraph UNIV g"
   using lsc_iff epigraph_subset_iff assms by (metis closure_minimal)
from this show ?thesis using epigraph_subset_iff lsc_hull_expl by metis
qed


lemma lsc_hull_iff_greatest:
fixes f g :: "'a::metric_space => ereal"
shows "(g = lsc_hull f) \<longleftrightarrow>
  lsc g & (ALL x. g x <= f x) & (ALL h. lsc h & (ALL x. h x <= f x) --> (ALL x. h x <= g x))"
(is "?lhs \<longleftrightarrow> ?rhs")
proof-
{ assume "?lhs" hence "?rhs" using lsc_lsc_hull lsc_hull_le lsc_hull_greatest by metis }
moreover
{ assume "?rhs"
  { fix x have "(lsc_hull f) x <= g x" using `?rhs` lsc_lsc_hull lsc_hull_le by metis
    moreover have "(lsc_hull f) x >= g x" using `?rhs` lsc_hull_greatest by metis
    ultimately have "(lsc_hull f) x = g x" by auto
  } hence "?lhs" by (simp add: ext)
} ultimately show ?thesis by blast
qed


lemma lsc_hull_mono:
fixes f g :: "'a::metric_space => ereal"
assumes "ALL x. g x <= f x"
shows "ALL x. (lsc_hull g) x <= (lsc_hull f) x"
proof-
{ fix x have "(lsc_hull g) x <= g x" using lsc_hull_le[of g x] by auto
  also have "... <= f x" using assms by auto
  finally have "(lsc_hull g) x <= f x" by auto
} note * = this
show ?thesis apply (subst lsc_hull_greatest) using lsc_lsc_hull[of g] * by auto
qed


lemma lsc_hull_lsc:
  "lsc f \<longleftrightarrow> (f = lsc_hull f)"
using lsc_hull_iff_greatest[of f f] by auto


lemma lsc_hull_liminf_at:
  fixes f :: "'a::metric_space => ereal"
  shows "ALL x. (lsc_hull f) x= min (f x) (Liminf (at x) f)"
proof-
{ fix x z assume "(x,z):Epigraph UNIV (%x. min (f x) (Liminf (at x) f))"
  hence xz_def: "ereal z >= (SUP e:{0<..}. INF y:ball x e. f y)"
    unfolding Epigraph_def min_Liminf_at by auto
  { fix e::real assume "e>0"
    hence "e/sqrt 2>0" using `e>0` by simp
    from this obtain e1 where e1_def: "e1<e/sqrt 2 & e1>0" using dense by auto
    hence "(SUP e:{0<..}. INF y:ball x e. f y) >= (INF y:ball x e1. f y)"
      by (auto intro: SUP_upper)
    hence "ereal z >= (INF y:ball x e1. f y)" using xz_def by auto
    hence *: "ALL y>ereal z. EX t. t : ball x e1 & f t <= y"
      by (simp add: Bex_def Inf_le_iff_less)
    obtain t where t_def: "t : ball x e1 & f t <= ereal(z+e1)"
      using e1_def *[rule_format, of "ereal(z+e1)"] by auto
    hence epi: "(t,z+e1):Epigraph UNIV f" unfolding Epigraph_def by auto
    have "dist x t < e1" using t_def unfolding ball_def dist_norm by auto
    hence "sqrt (e1 ^ 2 + dist x t ^ 2) < e"
      using e1_def apply (subst real_sqrt_sum_squares_less) by auto
    moreover have "dist (x,z) (t,z+e1) = sqrt (e1 ^ 2 + dist x t ^ 2)"
      unfolding dist_prod_def dist_norm by (simp add: algebra_simps)
    ultimately have "dist (x,z) (t,z+e1) < e" by auto
    hence "EX y:Epigraph UNIV f. dist y (x, z) < e"
      apply (rule_tac x="(t,z+e1)" in bexI) apply (simp add: dist_commute) using epi by auto
  } hence "(x,z) : closure (Epigraph UNIV f)"
      using closure_approachable[of "(x,z)" "Epigraph UNIV f"] by auto
}
moreover
{ fix x z assume xz_def: "(x,z):closure (Epigraph UNIV f)"
  { fix e::real assume "e>0"
    from this obtain y where y_def: "y:(Epigraph UNIV f) & dist y (x,z) < e"
      using closure_approachable[of "(x,z)" "Epigraph UNIV f"] xz_def by metis
    have "dist (fst y) x <= sqrt ((dist (fst y) x) ^ 2 + (dist (snd y) z) ^ 2)"
      by (auto intro: real_sqrt_sum_squares_ge1)
    also have "...<e" using y_def unfolding dist_prod_def by (simp add: algebra_simps)
    finally have "dist (fst y) x < e" by auto
    hence h1: "fst y:ball x e" unfolding ball_def by (simp add: dist_commute)
    have "dist (snd y) z <= sqrt ((dist (fst y) x) ^ 2 + (dist (snd y) z) ^ 2)"
      by (auto intro: real_sqrt_sum_squares_ge2)
    also have "...<e" using y_def unfolding dist_prod_def by (simp add: algebra_simps)
    finally have h2: "dist (snd y) z < e" by auto
    have "(INF y:ball x e. f y) <= f(fst y)" using h1 by (simp add: INF_lower)
    also have "...<=ereal(snd y)" using y_def unfolding Epigraph_def by auto
    also have "... < ereal(z+e)" using h2 unfolding dist_norm by auto
    finally have "(INF y:ball x e. f y) < ereal(z+e)" by auto
  } hence *: "ALL e>0. (INF y:ball x e. f y) < ereal(z+e)" by auto

  { fix e assume "(e::real)>0"
    { fix d assume "(d::real)>0"
      { assume "d<e"
        have "(INF y:ball x d. f y) < ereal(z+d)" using * `d>0` by auto
        also have "...< ereal(z+e)" using `d<e` by auto
        finally have "(INF y:ball x d. f y) < ereal(z+e)" by auto
      }
      moreover
      { assume "~(d<e)"
        hence "ball x e <= ball x d" by auto
        hence "(INF y:ball x d. f y) <= (INF y:ball x e. f y)" apply (subst INF_mono) by auto
        also have "...< ereal(z+e)" using * `e>0` by auto
        finally have "(INF y:ball x d. f y) < ereal(z+e)" by auto
      } ultimately have "(INF y:ball x d. f y) < ereal(z+e)" by blast
      hence "(INF y:ball x d. f y) <= ereal(z+e)" by auto
    } hence "min (f x) (Liminf (at x) f) <= ereal (z+e)" unfolding min_Liminf_at by (auto intro: SUP_least)
  } hence "min (f x) (Liminf (at x) f) <= ereal z" using ereal_le_epsilon2 by auto
  hence "(x,z):Epigraph UNIV (%x. min (f x) (Liminf (at x) f))" unfolding Epigraph_def by auto
}
ultimately have "Epigraph UNIV (%x. min (f x) (Liminf (at x) f))= closure (Epigraph UNIV f)" by auto
hence "(%x. min (f x) (Liminf (at x) f)) = lsc_hull f"
   using epigraph_invertible epigraph_lsc_hull[of f] by blast
from this show ?thesis by metis
qed


lemma lsc_hull_same_inf:
  fixes f :: "'a::metric_space => ereal"
  shows "(INF x. lsc_hull f x) = (INF x. f x)"
proof-
{ fix x
  have "(INF x. f x) <= (INF y:ball x 1. f y)" apply (subst INF_mono) by auto
  also have "... <= min (f x) (Liminf (at x) f)" unfolding min_Liminf_at by (auto intro: SUP_upper)
  also have "...=(lsc_hull f) x" using lsc_hull_liminf_at[of f] by auto
  finally have "(INF x. f x) <= (lsc_hull f) x" by auto
} hence "(INF x. f x) <= (INF x. lsc_hull f x)" apply (subst INF_greatest) by auto
moreover have "(INF x. lsc_hull f x) <= (INF x. f x)"
   apply (subst INF_mono) using lsc_hull_le by auto
ultimately show ?thesis by auto
qed


subsection {* Convex Functions *}


definition
  convex_on :: "'a::real_vector set => ('a => ereal) => bool" where
  "convex_on s f \<longleftrightarrow>
  (ALL x:s. ALL y:s. ALL u>=0. ALL v>=0. u + v = 1
  --> f (u *\<^sub>R x + v *\<^sub>R y) <= ereal u * f x + ereal v * f y)"


lemma convex_on_ereal_mem:
  assumes "convex_on s f"
  assumes "x:s" "y:s"
  assumes "u>=0" "v>=0" "u+v=1"
  shows "f (u *\<^sub>R x + v *\<^sub>R y) <= ereal u * f x + ereal v * f y"
using assms unfolding convex_on_def by auto


lemma convex_on_ereal_subset: "convex_on t f ==> s <= t ==> convex_on s f"
  unfolding convex_on_def by auto


lemma convex_on_ereal_univ: "convex_on UNIV f \<longleftrightarrow> (ALL S. convex_on S f)"
  using convex_on_ereal_subset by auto

lemma ereal_pos_setsum_right_distrib:
  fixes f :: "'a => ereal"
  assumes "r>=0" "r ~= \<infinity>"
  shows "r * setsum f A = setsum (%n. r * f n) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case using assms by (simp add: ereal_pos_distrib)
  qed
next
  case False thus ?thesis by simp
qed


lemma convex_ereal_add:
  fixes f g :: "'a::real_vector => ereal"
  assumes "convex_on s f" "convex_on s g"
  shows "convex_on s (%x. f x + g x)"
proof-
  { fix x y assume "x:s" "y:s" moreover
    fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
    ultimately have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y)
      <= (ereal u * f x + ereal v * f y) + (ereal u * g x + ereal v * g y)"
      using assms unfolding convex_on_def by (auto simp add:ereal_add_mono)
    also have "...=(ereal u * f x + ereal u * g x) + (ereal v * f y + ereal v * g y)"
      by (simp add: algebra_simps)
    also have "...= ereal u * (f x + g x) + ereal v * (f y + g y)"
      using uv by (simp add: ereal_pos_distrib)
    finally have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y)
      <= ereal u * (f x + g x) + ereal v * (f y + g y)" by auto }
  thus ?thesis unfolding convex_on_def by auto
qed

lemma convex_ereal_cmul:
  assumes "0 <= (c::ereal)" "convex_on s f"
  shows "convex_on s (%x. c * f x)"
proof-
{ fix x y assume "x:s" "y:s" moreover
  fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
  ultimately have "f (u *\<^sub>R x + v *\<^sub>R y) <= (ereal u * f x + ereal v * f y)"
     using assms unfolding convex_on_def by auto
  hence "c * f (u *\<^sub>R x + v *\<^sub>R y) <= c * (ereal u * f x + ereal v * f y)"
     using assms by (intro ereal_mult_left_mono) auto
  also have "... <=  c * (ereal u * f x) + c * (ereal v * f y)"
     using assms by (simp add: ereal_le_distrib)
  also have "... = ereal u *(c* f x) + ereal v *(c* f y)" by (simp add: algebra_simps)
  finally have "c * f (u *\<^sub>R x + v *\<^sub>R y)
      <= ereal u * (c * f x) + ereal v * (c * f y)" by auto }
  thus ?thesis unfolding convex_on_def by auto
qed



lemma convex_ereal_max:
  fixes f g :: "'a::real_vector => ereal"
  assumes "convex_on s f" "convex_on s g"
  shows "convex_on s (%x. max (f x) (g x))"
proof-
  { fix x y assume "x:s" "y:s" moreover
    fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
    ultimately have "max (f (u *\<^sub>R x + v *\<^sub>R y)) (g (u *\<^sub>R x + v *\<^sub>R y))
      <= max (ereal u * f x + ereal v * f y) (ereal u * g x + ereal v * g y)"
      apply (subst ereal_max_mono) using assms unfolding convex_on_def by auto
    also have "...<=ereal u * max (f x) (g x) + ereal v * max (f y) (g y)"
      apply (subst ereal_max_least)
      apply (subst ereal_add_mono) prefer 4 apply (subst ereal_add_mono)
      by (subst ereal_mult_left_mono, auto simp add: uv)+
    finally have "max (f (u *\<^sub>R x + v *\<^sub>R y)) (g (u *\<^sub>R x + v *\<^sub>R y))
      <= ereal u * max (f x) (g x) + ereal v * max (f y) (g y)" by auto }
  thus ?thesis unfolding convex_on_def by auto
qed


lemma convex_on_ereal_alt:
  fixes C :: "'a::real_vector set"
  assumes "convex C"
  shows "convex_on C f =
  (ALL x : C. ALL y : C. ALL m :: real. m >= 0 & m <= 1
      --> f (m *\<^sub>R x + (1 - m) *\<^sub>R y) <= (ereal m) * f x + (1 - (ereal m)) * f y)"
proof safe
  fix x y fix m :: real
  have[simp]: "ereal (1 - m) = (1 - ereal m)"
    using ereal_minus(1)[of 1 m] by (auto simp: one_ereal_def)
  assume asms: "convex_on C f" "x : C" "y : C" "0 <= m" "m <= 1"
  from this[unfolded convex_on_def, rule_format]
  have "ALL u v. ((0 <= u & 0 <= v & u + v = 1) -->
       f (u *\<^sub>R x + v *\<^sub>R y) <= (ereal u) * f x + (ereal v) * f y)" by auto
  from this[rule_format, of "m" "1 - m", simplified] asms
  show "f (m *\<^sub>R x + (1 - m) *\<^sub>R y)
          <= (ereal m) * f x + (1 - ereal m) * f y" by auto
next
  assume asm: "ALL x:C. ALL y:C. ALL m. 0 <= m & m <= 1
      --> f (m *\<^sub>R x + (1 - m) *\<^sub>R y) <= (ereal m) * f x + (1 - ereal m) * f y"
  { fix x y fix u v :: real
    assume lasm: "x : C" "y : C" "u >= 0" "v >= 0" "u + v = 1"
    hence[simp]: "1-u=v" "1 - ereal u = ereal v"
    using ereal_minus(1)[of 1 m] by (auto simp: one_ereal_def)
    from asm[rule_format, of x y u]
    have "f (u *\<^sub>R x + v *\<^sub>R y) <= (ereal u) * f x + (ereal v) * f y"
      using lasm by auto }
  thus "convex_on C f" unfolding convex_on_def by auto
qed


lemma convex_on_ereal_alt_mem:
  fixes C :: "'a::real_vector set"
  assumes "convex C"
  assumes "convex_on C f"
  assumes "x : C" "y : C"
  assumes "(m::real) >= 0" "m <= 1"
  shows "f (m *\<^sub>R x + (1 - m) *\<^sub>R y) <= (ereal m) * f x + (1 - (ereal m)) * f y"
by (metis assms convex_on_ereal_alt)


lemma ereal_add_right_mono: "(a::ereal) <= b ==> a + c <= b + c"
by (metis ereal_add_mono order_refl)

lemma convex_on_ereal_setsum_aux:
  assumes "1-a>0"
  shows "(1 - ereal a) * (ereal (c / (1 - a)) * b) = (ereal c) * b"
  by (metis mult.assoc mult.commute eq_divide_eq ereal_minus(1) assms
            one_ereal_def less_le times_ereal.simps(1))


lemma convex_on_ereal_setsum:
  fixes a :: "'a => real"
  fixes y :: "'a => 'b::real_vector"
  fixes f :: "'b => ereal"
  assumes "finite s" "s ~= {}"
  assumes "convex_on C f"
  assumes "convex C"
  assumes "(SUM i : s. a i) = 1"
  assumes "ALL i. i : s --> a i >= 0"
  assumes "ALL i. i : s --> y i : C"
  shows "f (SUM i : s. a i *\<^sub>R y i) <= (SUM i : s. ereal (a i) * f (y i))"
using assms(1,2,5-)
proof (induct s arbitrary:a rule:finite_ne_induct)
  case (singleton i)
  hence ai: "a i = 1" by auto
  thus ?case by (auto simp: one_ereal_def[symmetric])
next
  case (insert i s)
  from `convex_on C f`
  have conv: "ALL x y m. ((x : C & y : C & 0 <= m & m <= 1)
      --> f (m *\<^sub>R x + (1 - m) *\<^sub>R y) <= (ereal m) * f x + (1 - ereal m) * f y)"
      using convex_on_ereal_alt[of C f] `convex C` by auto
  { assume "a i = 1"
    hence "(SUM j : s. a j) = 0"
      using insert by auto
    hence "ALL j. (j : s --> a j = 0)"
      using setsum_nonneg_0[where 'b=real] insert by fastforce
    hence ?case using insert.hyps(1-3) `a i = 1`
      by (simp add: zero_ereal_def[symmetric] one_ereal_def[symmetric]) }
  moreover
  { assume asm: "a i ~= 1"
    from insert have yai: "y i : C" "a i >= 0" by auto
    have fis: "finite (insert i s)" using insert by auto
    hence ai1: "a i <= 1" using setsum_nonneg_leq_bound[of "insert i s" a] insert by simp
    hence "a i < 1" using asm by auto
    hence i0: "1 - a i > 0" by auto
    hence i1: "1 - ereal (a i) > 0" using ereal_minus(1)[of 1 "a i"]
      by (simp add: zero_ereal_def[symmetric] one_ereal_def[symmetric])
    have i2: "1 - ereal (a i) ~= \<infinity>" using ereal_minus(1)[of 1]
      by (simp add: zero_ereal_def[symmetric] one_ereal_def[symmetric])
    let "?a j" = "a j / (1 - a i)"
    have a_nonneg: "\<And>j. j \<in> s \<Longrightarrow> 0 \<le> a j / (1 - a i)"
      using i0 insert
      by (metis insert_iff divide_nonneg_pos)
    have "(SUM j : insert i s. a j) = 1" using insert by auto
    hence "(SUM j : s. a j) = 1 - a i" using setsum.insert insert by fastforce
    hence "(SUM j : s. a j) / (1 - a i) = 1" using i0 by auto
    hence a1: "(SUM j : s. ?a j) = 1" unfolding setsum_divide_distrib by simp
    have asum: "(SUM j : s. ?a j *\<^sub>R y j) : C"
      using insert convex_setsum[OF `finite s`
        `convex C` a1 a_nonneg] by auto
    have asum_le: "f (SUM j : s. ?a j *\<^sub>R y j) <= (SUM j : s. ereal (?a j) * f (y j))"
      using a_nonneg a1 insert by blast
    have "f (SUM j : insert i s. a j *\<^sub>R y j) = f ((SUM j : s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using setsum.insert[of s i "% j. a j *\<^sub>R y j", OF `finite s` `i ~: s`]
      by (auto simp only:add.commute)
    also have "... = f (((1 - a i) * inverse (1 - a i)) *\<^sub>R (SUM j : s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using i0 by auto
    also have "... = f ((1 - a i) *\<^sub>R (SUM j : s. (a j * inverse (1 - a i)) *\<^sub>R y j) + a i *\<^sub>R y i)"
      using scaleR_right.setsum[of "inverse (1 - a i)" "% j. a j *\<^sub>R y j" s, symmetric] by (auto simp:algebra_simps)
    also have "... = f ((1 - a i) *\<^sub>R (SUM j : s. ?a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      by (auto simp: divide_inverse)
    also have "... <= (1 - ereal (a i)) * f ((SUM j : s. ?a j *\<^sub>R y j)) + (ereal (a i)) * f (y i)"
      using conv[rule_format, of "y i" "(SUM j : s. ?a j *\<^sub>R y j)" "a i"]
      using yai(1) asum yai(2) ai1 by (auto simp add:add.commute)
    also have "... <= (1 - ereal (a i)) * (SUM j : s. ereal (?a j) * f (y j)) + (ereal (a i)) * f (y i)"
      using ereal_add_right_mono[OF ereal_mult_left_mono[of _ _ "1 - ereal (a i)",
        OF asum_le less_imp_le[OF i1]], of "(ereal (a i)) * f (y i)"] by simp
    also have "... = (SUM j : s. (1 - ereal (a i)) * (ereal (?a j) * f (y j))) + (ereal (a i)) * f (y i)"
      unfolding ereal_pos_setsum_right_distrib[of "1 - ereal (a i)" "% j. (ereal (?a j)) * f (y j)", OF less_imp_le[OF i1] i2] by auto
    also have "... = (SUM j : s. (ereal (a j)) * f (y j)) + (ereal (a i)) * f (y i)" using i0 convex_on_ereal_setsum_aux by auto
    also have "... = (ereal (a i)) * f (y i) + (SUM j : s. (ereal (a j)) * f (y j))" by (simp add: add.commute)
    also have "... = (SUM j : insert i s. (ereal (a j)) * f (y j))" using insert by auto
    finally have "f (SUM j : insert i s. a j *\<^sub>R y j) <= (SUM j : insert i s. (ereal (a j)) * f (y j))" by simp }
  ultimately show ?case by auto
qed


lemma setsum_2: "setsum u {1::nat..2} = (u 1)+(u 2)"
proof-
  have "{1::nat..2} = {1::nat,2}" by auto
  thus ?thesis by auto
qed


lemma convex_on_ereal_iff:
  assumes "convex s"
  shows "convex_on s f \<longleftrightarrow> (ALL k u x. (ALL i:{1..k::nat}. 0 <= u i & x i : s) & setsum u {1..k} = 1 -->
   f (setsum (%i. u i *\<^sub>R x i) {1..k} ) <= setsum (%i. (ereal (u i)) * f(x i)) {1..k} )"
  (is "?rhs \<longleftrightarrow> ?lhs")
proof-
{ assume "?rhs"
  { fix k u x
    have zero: "~(setsum u {1..0::nat} = (1::real))" by auto
    assume "(ALL i:{1..k::nat}. (0::real) <= u i & x i : s)"
    moreover assume "setsum u {1..k} = 1"
    moreover hence "k ~= 0" using zero by metis
    ultimately have "f (setsum (%i. u i *\<^sub>R x i) {1..k} )
      <= setsum (%i. (ereal (u i)) * f(x i)) {1..k}"
      using convex_on_ereal_setsum[of "{1..k}" s f u x] using assms `?rhs` by auto
  } hence "?lhs" by auto
}
moreover
{ assume "?lhs"
  { fix x y u v
    assume xys: "x:s" "y:s"
    assume uv1: "u>=0" "v>=0" "u + v = (1::real)"
    def xy == "(%i::nat. if i=1 then x else y)"
    def uv == "(%i::nat. if i=1 then u else v)"
    have "ALL i:{1..2::nat}. (0 <= uv i) & (xy i : s)" unfolding xy_def uv_def using xys uv1 by auto
    moreover have "setsum uv {1..2} = 1" using setsum_2[of uv] unfolding uv_def using uv1 by auto
    moreover have "(SUM i = 1..2. uv i *\<^sub>R xy i) = u *\<^sub>R x + v *\<^sub>R y"
        using setsum_2[of "(%i. uv i *\<^sub>R xy i)"] unfolding xy_def uv_def using xys uv1 by auto
    moreover have "(SUM i = 1..2. ereal (uv i) * f (xy i)) = ereal u * f x + ereal v * f y"
        using setsum_2[of "(%i. ereal (uv i) * f (xy i))"] unfolding xy_def uv_def using xys uv1 by auto
    ultimately have "f (u *\<^sub>R x + v *\<^sub>R y) <= ereal u * f x + ereal v * f y"
      using `?lhs`[rule_format, of "2" uv xy] by auto
  } hence "?rhs" unfolding convex_on_def by auto
} ultimately show ?thesis by blast
qed


lemma convex_Epigraph:
  assumes "convex S"
  shows "convex(Epigraph S f) \<longleftrightarrow> convex_on S f"
proof-
{ assume rhs: "convex(Epigraph S f)"
  { fix x y assume xy: "x:S" "y:S"
    fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
    have "f (u *\<^sub>R x + v *\<^sub>R y) <= ereal u * f x + ereal v * f y"
    proof-
      { assume "u=0 | v=0" hence ?thesis using uv by (auto simp: zero_ereal_def[symmetric] one_ereal_def[symmetric]) }
      moreover
      { assume "f x = \<infinity> | f y = \<infinity>" hence ?thesis using uv by (auto simp: zero_ereal_def[symmetric] one_ereal_def[symmetric]) }
      moreover
      { assume a: "f x = -\<infinity> & (f y ~= \<infinity>) & ~(u=0)"
        from this obtain z where "f y <= ereal z" apply (cases "f y") by auto
        hence yz: "(y,z) : Epigraph S f" unfolding Epigraph_def using xy by auto
        { fix C::real
          have "(x, (1/u)*(C - v * z)) : Epigraph S f" unfolding Epigraph_def using a xy by auto
          hence "(u *\<^sub>R x + v *\<^sub>R y, C) : Epigraph S f"
            using rhs convexD[of "Epigraph S f" "(x, (1/u)*(C - v * z))" "(y,z)" u v] uv yz a by auto
          hence "(f (u *\<^sub>R x + v *\<^sub>R y) <= ereal C)" unfolding Epigraph_def by auto
        } hence "f (u *\<^sub>R x + v *\<^sub>R y) = -\<infinity>" using ereal_bot by auto
        hence ?thesis by auto }
      moreover
      { assume a: "(f x ~= \<infinity>) & f y = -\<infinity> & ~(v=0)"
        from this obtain z where "f x <= ereal z" apply (cases "f x") by auto
        hence xz: "(x,z) : Epigraph S f" unfolding Epigraph_def using xy by auto
        { fix C::real
          have "(y, (1/v)*(C - u * z)) : Epigraph S f" unfolding Epigraph_def using a xy by auto
          hence "(u *\<^sub>R x + v *\<^sub>R y, C) : Epigraph S f"
            using rhs convexD[of "Epigraph S f" "(x,z)" "(y, (1/v)*(C - u * z))" u v] uv xz a by auto
          hence "(f (u *\<^sub>R x + v *\<^sub>R y) <= ereal C)" unfolding Epigraph_def by auto
        } hence "f (u *\<^sub>R x + v *\<^sub>R y) = -\<infinity>" using ereal_bot by auto
        hence ?thesis by auto }
      moreover
      { assume a: "f x ~= \<infinity> & f x ~= -\<infinity> & f y ~= \<infinity> & f y ~= -\<infinity>"
        from this obtain fx fy where fxy: "f x = ereal fx & f y = ereal fy"
           apply (cases "f x", cases "f y") by auto
        hence "(x, fx) : Epigraph S f & (y, fy) : Epigraph S f" unfolding Epigraph_def using xy by auto
        hence "(u *\<^sub>R x + v *\<^sub>R y, u * fx + v * fy) : Epigraph S f"
           using rhs convexD[of "Epigraph S f" "(x,fx)" "(y,fy)" u v] uv by auto
        hence ?thesis unfolding Epigraph_def using fxy by auto
      } ultimately show ?thesis by blast
    qed
  } hence "convex_on S f" unfolding convex_on_def by auto
}
moreover
{ assume lhs: "convex_on S f"
  { fix x y fx fy assume xy: "(x,fx):Epigraph S f" "(y,fy):Epigraph S f"
    fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
    hence le: "f x <= ereal fx & f y <= ereal fy" using xy unfolding Epigraph_def by auto
    have "x:S & y:S" using xy unfolding Epigraph_def by auto
    moreover hence inS: "u *\<^sub>R x + v *\<^sub>R y : S" using assms uv convexD[of S] by auto
    ultimately have "f(u *\<^sub>R x + v *\<^sub>R y) <= (ereal u) * f x + (ereal v) * f y"
      using lhs convex_on_ereal_mem[of S f x y u v] uv by auto
    also have "... <= (ereal u) * (ereal fx) + (ereal v) * (ereal fy)"
      apply (subst ereal_add_mono) apply (subst ereal_mult_left_mono)
      prefer 4 apply (subst ereal_mult_left_mono) using le uv by auto
    also have "... = ereal (u * fx + v * fy)" by auto
    finally have "(u *\<^sub>R x + v *\<^sub>R y, u * fx + v * fy) : Epigraph S f"
      unfolding Epigraph_def using inS by auto
  } hence "convex(Epigraph S f)" unfolding convex_def by auto
}
ultimately show ?thesis by auto
qed


lemma convex_EpigraphI:
  "convex_on s f ==> convex s ==> convex(Epigraph s f)"
unfolding convex_Epigraph by auto


definition
  concave_on :: "'a::real_vector set => ('a => ereal) => bool" where
  "concave_on S f \<longleftrightarrow> convex_on S (%x. - f x)"

definition
  finite_on :: "'a::real_vector set => ('a => ereal) => bool" where
  "finite_on S f \<longleftrightarrow> (ALL x:S. (f x ~= \<infinity> & f x ~= -\<infinity>))"

definition
  affine_on :: "'a::real_vector set => ('a => ereal) => bool" where
  "affine_on S f \<longleftrightarrow> (convex_on S f & concave_on S f & finite_on S f)"

definition
  "domain (f::_ => ereal) = {x. f x < \<infinity>}"


lemma domain_Epigraph_aux:
  assumes "x ~= \<infinity>"
  shows "EX r. x<=ereal r"
using assms by (cases x) auto


lemma domain_Epigraph:
  "domain f = {x. EX y. (x,y):Epigraph UNIV f}"
  unfolding domain_def Epigraph_def using domain_Epigraph_aux by auto


lemma domain_Epigraph_fst:
  "domain f = fst ` (Epigraph UNIV f)"
proof-
{ fix x assume "x:domain f"
  from this obtain y where "(x,y):Epigraph UNIV f"  using domain_Epigraph[of f] by auto
  moreover have "x = fst (x,y)" by auto
  ultimately have "x:fst ` (Epigraph UNIV f)" unfolding image_def by blast
} from this show ?thesis using domain_Epigraph[of f] by auto
qed


lemma convex_on_domain:
  "convex_on (domain f) f \<longleftrightarrow> convex_on UNIV f"
proof-
{ assume lhs: "convex_on (domain f) f"
  { fix x y
    fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
    have "f (u *\<^sub>R x + v *\<^sub>R y) <= ereal u * f x + ereal v * f y"
    proof-
      { assume "f x = \<infinity> | f y = \<infinity>" hence ?thesis using uv by (auto simp: zero_ereal_def[symmetric] one_ereal_def[symmetric]) }
      moreover
      { assume "~ (f x = \<infinity> | f y = \<infinity>)"
        hence "x : domain f & y : domain f" unfolding domain_def by auto
        hence ?thesis using lhs unfolding convex_on_def using uv by auto
      } ultimately show ?thesis by blast
    qed }
  hence "convex_on UNIV f" unfolding convex_on_def by auto
} from this show ?thesis using convex_on_ereal_subset by auto
qed


lemma convex_on_domain2:
  "convex_on (domain f) f \<longleftrightarrow> (ALL S. convex_on S f)"
by (metis convex_on_domain convex_on_ereal_univ)


lemma convex_domain:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "convex (domain f)"
proof-
have "convex (Epigraph UNIV f)" using assms convex_Epigraph by auto
thus ?thesis unfolding domain_Epigraph_fst
  apply (subst convex_linear_image) using fst_linear linear_conv_bounded_linear by auto
qed


lemma infinite_convex_domain_iff:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "ALL x. (f x = \<infinity> | f x = -\<infinity>)"
  shows "convex_on UNIV f \<longleftrightarrow> convex (domain f)"
proof-
{ assume dom: "convex (domain f)"
  { fix x y assume "x:domain f" "y:domain f" moreover
    fix u v ::real assume uv: "0 <= u" "0 <= v" "u + v = 1"
    ultimately have "u *\<^sub>R x + v *\<^sub>R y : domain f"
      using dom unfolding convex_def by auto
    hence "f(u *\<^sub>R x + v *\<^sub>R y) = -\<infinity>"
      using assms unfolding domain_def by auto
  } hence "convex_on (domain f) f" unfolding convex_on_def by auto
  hence "convex_on UNIV f" by (metis convex_on_domain2)
} thus ?thesis by (metis convex_domain)
qed


lemma convex_PInfty_outside:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f" "convex S"
  shows "convex_on UNIV (%x. if x:S then (f x) else \<infinity>)"
proof-
  def g == "(%x. if x:S then -\<infinity> else \<infinity>::ereal)"
  hence "convex_on UNIV g" apply (subst infinite_convex_domain_iff)
    using assms unfolding domain_def by auto
  moreover have "(%x. if x:S then (f x) else \<infinity>) = (%x. max (f x) (g x))"
    apply (subst fun_eq_iff) unfolding g_def apply auto
    apply (metis ereal_less_eq(2) max.absorb1)
    by (metis ereal_less_eq(1) max.absorb2)
  ultimately show ?thesis using convex_ereal_max assms by auto
qed



definition
  proper_on :: "'a::real_vector set => ('a => ereal) => bool" where
  "proper_on S f \<longleftrightarrow> ((ALL x:S. f x ~= -\<infinity>) & (EX x:S. f x ~= \<infinity>))"

definition
  proper :: "('a::real_vector => ereal) => bool" where
  "proper f \<longleftrightarrow> proper_on UNIV f"


lemma proper_iff:
  "proper f \<longleftrightarrow> ((ALL x. f x ~= -\<infinity>) & (EX x. f x ~= \<infinity>))"
unfolding proper_def proper_on_def by auto


lemma improper_iff:
  "~(proper f) \<longleftrightarrow> ((EX x. f x = -\<infinity>) | (ALL x. f x = \<infinity>))"
using proper_iff by auto

lemma ereal_MInf_plus[simp]: "-\<infinity> + x = (if x = \<infinity> then \<infinity> else -\<infinity>::ereal)"
  by (cases x) auto

lemma convex_improper:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "~(proper f)"
  shows "ALL x:rel_interior(domain f). f x = -\<infinity>"
proof-
{ assume "domain f = {}" hence ?thesis using rel_interior_empty by auto }
moreover
{ assume nemp: "domain f ~= {}"
  then obtain u where u_def: "f u = -\<infinity>" using assms improper_iff[of f] unfolding domain_def by auto
  hence udom: "u:domain f" unfolding domain_def by auto
  { fix x assume "x:rel_interior(domain f)"
    then obtain m where m_def: "m>1 & (1 - m) *\<^sub>R u + m *\<^sub>R x : domain f"
       using convex_rel_interior_iff[of "domain f" x] nemp convex_domain[of f] assms udom by auto
    def v == "1/m" hence v01: "0<v & v<1" using m_def by auto
    def y == "(1 - m) *\<^sub>R u + m *\<^sub>R x"
    hence "x = (1-v) *\<^sub>R u+v *\<^sub>R y" unfolding v_def using m_def by (simp add: algebra_simps)
    hence "f x <= (1-ereal v) * f u+ereal v * f y"
      using convex_on_ereal_alt_mem[of "UNIV" f y u v] assms convex_UNIV v01
      by (simp add: convex_UNIV add.commute)
    moreover have "f y < \<infinity>" using m_def y_def unfolding domain_def by auto
    moreover have *: "0 < 1 - ereal v" using v01
      by (metis diff_gt_0_iff_gt ereal_less(2) ereal_minus(1) one_ereal_def)
    moreover hence "(1-ereal v) * f u = -\<infinity>" using u_def by auto
    ultimately have "f x = -\<infinity>" using v01 by simp
  } hence ?thesis by auto
} ultimately show ?thesis by blast
qed


lemma convex_improper2:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "~(proper f)"
  shows "f x = \<infinity> | f x = -\<infinity> | x : rel_frontier (domain f)"
proof-
{ assume a: "~(f x = \<infinity> | f x = -\<infinity>)"
  hence "x: domain f" unfolding domain_def by auto
  hence "x : closure (domain f)" using closure_subset by auto
  moreover have "x ~: rel_interior (domain f)" using assms convex_improper a by auto
  ultimately have "x : rel_frontier (domain f)" unfolding rel_frontier_def by auto
} thus ?thesis by auto
qed


lemma convex_lsc_improper:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "~(proper f)"
  assumes "lsc f"
  shows "f x = \<infinity> | f x = -\<infinity>"
proof-
{ fix x assume "f x ~= \<infinity>"
  hence "lsc_at x f" using assms unfolding lsc_def by auto
  have "x: domain f" unfolding domain_def using `f x ~= \<infinity>` by auto
  hence "x : closure (domain f)" using closure_subset by auto
  hence x_def: "x : closure (rel_interior (domain f))"
    by (metis assms(1) convex_closure_rel_interior convex_domain)
  { fix C assume "C<f x"
    from this obtain d where d_def: "d>0 & (ALL y. dist x y < d --> C < f y)"
       using lst_at_delta[of x f] `lsc_at x f` by auto
    from this obtain y where y_def: "y:rel_interior (domain f) & dist y x < d"
       using x_def closure_approachable[of x "rel_interior (domain f)"] by auto
    hence "f y = -\<infinity>" by (metis assms(1) assms(2) convex_improper)
    moreover have "C < f y" using y_def d_def by (simp add: dist_commute)
    ultimately have False by auto
  } hence "f x = -\<infinity>" by auto
} from this show ?thesis by auto
qed


lemma convex_lsc_hull:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "convex_on UNIV (lsc_hull f)"
proof-
  have "convex(Epigraph UNIV f)" by (metis assms convex_EpigraphI convex_UNIV)
  hence "convex (Epigraph UNIV (lsc_hull f))" by (metis convex_closure epigraph_lsc_hull)
  thus ?thesis by (metis convex_Epigraph convex_UNIV)
qed


lemma improper_lsc_hull:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "~(proper f)"
  shows "~(proper (lsc_hull f))"
proof-
  {
    assume *: "ALL x. f x = \<infinity>"
    then have "lsc f"
      by (metis (full_types) UNIV_I lsc_at_open lsc_def open_UNIV)
    with * have "ALL x. (lsc_hull f) x = \<infinity>" by (metis lsc_hull_lsc)
  }
  hence "(ALL x. f x = \<infinity>) \<longleftrightarrow> (ALL x. (lsc_hull f) x = \<infinity>)"
    by (metis ereal_infty_less_eq(1) lsc_hull_le)
  moreover have "(EX x. f x = -\<infinity>) --> (EX x. (lsc_hull f) x = -\<infinity>)"
    by (metis ereal_infty_less_eq2(2) lsc_hull_le)
  ultimately show ?thesis using assms unfolding improper_iff by auto
qed


lemma lsc_hull_convex_improper:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "~(proper f)"
  shows "ALL x:rel_interior(domain f). (lsc_hull f) x = f x"
by (metis assms convex_improper ereal_infty_less_eq(2) lsc_hull_le)


lemma convex_with_rel_open_domain:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "rel_open (domain f)"
  shows "(ALL x. f x > -\<infinity>) | (ALL x. (f x = \<infinity> | f x = -\<infinity>))"
proof-
{ assume "~(ALL x. f x > -\<infinity>)"
  hence "~(proper f)" using proper_iff by auto
  hence "ALL x:rel_interior(domain f). f x = -\<infinity>" by (metis assms(1) convex_improper)
  hence "ALL x:domain f. f x = -\<infinity>" by (metis assms(2) rel_open_def)
  hence "ALL x. (f x = \<infinity> | f x = -\<infinity>)" unfolding domain_def by auto
} thus ?thesis by auto
qed


lemma convex_with_UNIV_domain:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "domain f = UNIV"
  shows "(ALL x. f x > -\<infinity>) | (ALL x. f x = -\<infinity>)"
by (metis assms convex_improper ereal_MInfty_lessI proper_iff rel_interior_univ2 UNIV_I)


lemma rel_interior_Epigraph:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "(x,z) : rel_interior (Epigraph UNIV f) \<longleftrightarrow>
    (x : rel_interior (domain f) & f x < ereal z)"
apply (subst rel_interior_projection[of _ "(%y. {z. (y, z) : Epigraph UNIV f})"])
apply (metis assms convex_EpigraphI convex_UNIV convex_on_ereal_univ)
unfolding domain_Epigraph Epigraph_def using rel_interior_ereal_semiline by auto


lemma rel_interior_EpigraphI:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "rel_interior (Epigraph UNIV f) =
    {(x,z) |x z. x : rel_interior (domain f) & f x < ereal z}"
proof-
{ fix x z
  have "(x,z):rel_interior (Epigraph UNIV f) \<longleftrightarrow> (x : rel_interior (domain f) & f x < ereal z)"
     using rel_interior_Epigraph[of f x z] assms by auto
} thus ?thesis by auto
qed



lemma convex_less_ri_domain:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "EX x. f x < a"
  shows "EX x:rel_interior (domain f). f x < a"
proof-
  def A == "{(x::'a::euclidean_space,m)|x m. ereal m<a}"
  obtain x where "f x < a" using assms by auto
  then obtain z where z_def: "f x < ereal z & ereal z < a" using ereal_dense2 by auto
  hence "(x,z):A & (x,z):Epigraph UNIV f" unfolding A_def Epigraph_def by auto
  hence "A Int (Epigraph UNIV f) ~= {}" unfolding A_def Epigraph_def using assms by auto
  moreover have "open A" proof(cases a)
    case real hence "A = {y. inner (0::'a, 1) y < real_of_ereal a}" using A_def by auto
      thus ?thesis using open_halfspace_lt by auto
    next case PInf thus ?thesis using A_def by auto
    next case MInf thus ?thesis using A_def by auto
  qed
  ultimately have "A Int rel_interior(Epigraph UNIV f) ~= {}"
    by (metis assms(1) convex_Epigraph convex_UNIV
       open_inter_closure_eq_empty open_inter_closure_rel_interior)
  then obtain x0 z0 where "(x0,z0):A & x0 : rel_interior (domain f) & f x0 < ereal z0"
    using rel_interior_Epigraph[of f] assms by auto
  thus ?thesis apply(rule_tac x="x0" in bexI) using A_def by auto
qed


lemma rel_interior_eq_between:
  fixes S T :: "('m::euclidean_space) set"
  assumes "convex S" "convex T"
  shows "(rel_interior S = rel_interior T) \<longleftrightarrow> (rel_interior S <= T & T <= closure S)"
by (metis assms closure_eq_between convex_closure_rel_interior convex_rel_interior_closure)



lemma convex_less_in_riS:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "convex S" "rel_interior S <= domain f"
  assumes "EX x:closure S. f x < a"
  shows "EX x:rel_interior S. f x < a"
proof-
  def g == "(%x. if x:closure S then (f x) else \<infinity>)"
  hence "EX x. g x < a" using assms by auto
  have convg: "convex_on UNIV g" unfolding g_def apply (subst convex_PInfty_outside)
    using assms convex_closure by auto
  hence *: "EX x:rel_interior (domain g). g x < a" apply (subst convex_less_ri_domain)
    using assms g_def by auto
  have "convex (domain g)" by (metis convg convex_domain)
  moreover have "rel_interior S <= domain g & domain g <= closure S"
    using g_def assms rel_interior_subset_closure unfolding domain_def by auto
  ultimately have "rel_interior (domain g) = rel_interior S"
    by (metis assms(2) rel_interior_eq_between)
  thus ?thesis
    by (metis "*" g_def less_ereal.simps(2))
qed


lemma convex_less_inS:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "convex S" "S <= domain f"
  assumes "EX x:closure S. f x < a"
  shows "EX x:S. f x < a"
using convex_less_in_riS[of f S a] rel_interior_subset[of S] assms by auto


lemma convex_finite_geq_on_closure:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "convex S" "finite_on S f"
  assumes "ALL x:S. f x >= a"
  shows "ALL x:closure S. f x >= a"
proof-
have "S <= domain f" using assms unfolding finite_on_def domain_def by auto
{ assume "~(ALL x:closure S. f x >= a)"
  hence "EX x:closure S. f x < a" by (simp add: not_le)
  hence False using convex_less_inS[of f S a] assms `S <= domain f` by auto
} thus ?thesis by auto
qed


lemma lsc_hull_of_convex_determined:
  fixes f g :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f" "convex_on UNIV g"
  assumes "rel_interior (domain f) = rel_interior (domain g)"
  assumes "ALL x:rel_interior (domain f). f x = g x"
  shows "lsc_hull f = lsc_hull g"
proof-
  have "rel_interior (Epigraph UNIV f) = rel_interior (Epigraph UNIV g)"
    apply (subst rel_interior_EpigraphI, metis assms)+ using assms by auto
  hence "closure (Epigraph UNIV f) = closure (Epigraph UNIV g)"
    by (metis assms convex_EpigraphI convex_UNIV convex_closure_rel_interior)
  thus ?thesis by (metis lsc_hull_expl)
qed


lemma domain_lsc_hull_between:
  fixes f :: "'a::euclidean_space => ereal"
  shows "domain f <= domain (lsc_hull f)
       & domain (lsc_hull f) <= closure (domain f)"
proof-
{ fix x assume "x:domain f"
  hence "x:domain (lsc_hull f)" unfolding domain_def using lsc_hull_le[of f x] by auto
} moreover
{ fix x assume "x:domain (lsc_hull f)"
  hence "min (f x) (Liminf (at x) f) < \<infinity>" unfolding domain_def using lsc_hull_liminf_at[of f] by auto
  then obtain z where z_def: "min (f x) (Liminf (at x) f) < z & z < \<infinity>" by (metis dense)
  { fix e::real assume "e>0"
    hence "INFIMUM (ball x e) f <= min (f x) (Liminf (at x) f)"
      unfolding min_Liminf_at apply (subst SUP_upper) by auto
    hence "EX y. y : ball x e & f y <= z"
      using Inf_le_iff_less[of "ball x e" f "min (f x) (Liminf (at x) f)"] z_def by (auto simp: Bex_def)
    hence "EX y. dist x y < e & y : domain f" unfolding domain_def ball_def using z_def by auto
  } hence "x:closure(domain f)" unfolding closure_approachable by (auto simp add: dist_commute)
} ultimately show ?thesis by auto
qed


lemma domain_vs_domain_lsc_hull:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "rel_interior(domain (lsc_hull f)) = rel_interior(domain f)
         & closure(domain (lsc_hull f)) = closure(domain f)
         & aff_dim(domain (lsc_hull f)) = aff_dim(domain f)"
proof-
  have "convex (domain f)" by (metis assms convex_domain)
  moreover have "convex (domain (lsc_hull f))" by (metis assms convex_domain convex_lsc_hull)
  moreover have "rel_interior (domain f) <= domain (lsc_hull f)
                 & domain (lsc_hull f) <= closure (domain f)"
                 by (metis domain_lsc_hull_between rel_interior_subset subset_trans)
  ultimately show ?thesis by (metis closure_eq_between rel_interior_aff_dim rel_interior_eq_between)
qed


lemma vertical_line_affine:
  fixes x :: "'a::euclidean_space"
  shows "affine {(x,m::real)|m. m:UNIV}"
unfolding affine_def by (auto simp add: pth_8)


lemma lsc_hull_of_convex_agrees_onRI:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "ALL x:rel_interior (domain f). (f x = (lsc_hull f) x)"
proof-
have cEpi: "convex (Epigraph UNIV f)" by (metis assms convex_EpigraphI convex_UNIV)
{ fix x assume x_def: "x : rel_interior (domain f)"
  hence "f x < \<infinity>" unfolding domain_def using rel_interior_subset by auto
  then obtain r where r_def: "(x,r):rel_interior (Epigraph UNIV f)"
    using assms x_def rel_interior_Epigraph[of f x]  by (metis ereal_dense2)
  def M == "{(x,m::real)|m. m:UNIV}"
  hence "affine M" using vertical_line_affine by auto
  moreover have "rel_interior (Epigraph UNIV f) Int M ~= {}" using r_def M_def by auto
  ultimately have *: "closure (Epigraph UNIV f) Int M = closure (Epigraph UNIV f Int M)"
    using convex_affine_closure_inter[of "Epigraph UNIV f" M] cEpi by auto
  have "Epigraph UNIV f Int M = {x} \<times> {m. f x <= ereal m}"
    unfolding Epigraph_def M_def by auto
  moreover have "closed({x} \<times> {m. f x<= ereal m})" apply (subst closed_Times)
    using closed_ereal_semiline by auto
  ultimately have "{x} \<times> {m. f x <= ereal m} = closure (Epigraph UNIV f) Int M"
    by (metis "*" Int_commute closure_closed)
  also have "...=Epigraph UNIV (lsc_hull f) Int M" by (metis Int_commute epigraph_lsc_hull)
  also have "...={x} \<times> {m. ((lsc_hull f) x) <= ereal m}"
    unfolding Epigraph_def M_def by auto
  finally have "{m. f x <= ereal m} = {m. lsc_hull f x <= ereal m}" by auto
  hence "f x = (lsc_hull f) x" using ereal_semiline_unique by auto
} thus ?thesis by auto
qed


lemma lsc_hull_of_convex_agrees_outside:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "ALL x. x ~: closure (domain f) --> (f x = (lsc_hull f) x)"
proof-
{ fix x assume "x ~: closure (domain f)"
  hence "x ~: domain (lsc_hull f)" using domain_lsc_hull_between by auto
  hence "(lsc_hull f) x = \<infinity>" unfolding domain_def by auto
  hence "f x = (lsc_hull f) x" using lsc_hull_le[of f x] by auto
} thus ?thesis by auto
qed


lemma lsc_hull_of_convex_agrees:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  shows "ALL x. (f x = (lsc_hull f) x) | x : rel_frontier (domain f)"
by (metis DiffI assms lsc_hull_of_convex_agrees_onRI lsc_hull_of_convex_agrees_outside rel_frontier_def)


lemma lsc_hull_of_proper_convex_proper:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f" "proper f"
  shows "proper (lsc_hull f)"
proof-
  obtain x where x_def: "x:rel_interior (domain f) & f x < \<infinity>"
     by (metis assms convex_less_ri_domain ereal_less_PInfty proper_iff)
  hence "f x = (lsc_hull f) x" using lsc_hull_of_convex_agrees[of f] assms
     unfolding rel_frontier_def by auto
  moreover have "f x > -\<infinity>" using assms proper_iff by auto
  ultimately have "(lsc_hull f) x < \<infinity> & (lsc_hull f) x > -\<infinity>" using x_def by auto
  thus ?thesis using convex_lsc_improper[of "lsc_hull f" x]
    lsc_lsc_hull[of f] assms convex_lsc_hull[of f] by auto
qed


lemma lsc_hull_of_proper_convex:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f" "proper f"
  shows "lsc (lsc_hull f) & proper (lsc_hull f) & convex_on UNIV (lsc_hull f) &
     (ALL x. (f x = (lsc_hull f) x) | x : rel_frontier (domain f))"
by (metis assms convex_lsc_hull lsc_hull_of_convex_agrees lsc_hull_of_proper_convex_proper lsc_lsc_hull)


lemma affine_no_rel_frontier:
  fixes S :: "('n::euclidean_space) set"
  assumes "affine S"
  shows "rel_frontier S = {}"
  unfolding rel_frontier_def using assms affine_closed[of S]
  closure_closed[of S] affine_rel_open[of S] rel_open_def[of S] by auto


lemma convex_with_affine_domain_is_lsc:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "affine (domain f)"
  shows "lsc f"
by (metis assms affine_no_rel_frontier emptyE lsc_def lsc_hull_liminf_at
          lsc_hull_of_convex_agrees lsc_liminf_at_eq)


lemma convex_finite_is_lsc:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "finite_on UNIV f"
  shows "lsc f"
proof-
  have "affine (domain f)"
    using assms affine_UNIV unfolding finite_on_def domain_def by auto
  thus ?thesis by (metis assms(1) convex_with_affine_domain_is_lsc)
qed


lemma always_eventually_within:
  "(ALL x:S. P x) \<Longrightarrow> eventually P (at x within S)"
  unfolding eventually_at_filter by auto


lemma ereal_divide_pos:
  assumes "(a::ereal)>0" "b>0"
  shows "a/(ereal b)>0"
  by (metis PInfty_eq_infinity assms ereal.simps(2) ereal_less(2) ereal_less_divide_pos ereal_mult_zero)


lemma real_interval_limpt:
  assumes "a<b"
  shows "(b::real) islimpt {a..<b}"
proof-
{ fix T assume "b:T" "open T"
  then obtain e where e_def: "e>0 & cball b e <= T" using open_contains_cball[of T] by auto
  hence "(b-e):cball b e" unfolding cball_def dist_norm by auto
  moreover
  { assume "a>=b-e" hence "a:cball b e" unfolding cball_def dist_norm using `a<b` by auto }
  ultimately have "max a (b-e):cball b e"
    by (metis max.absorb1 max.absorb2 linear)
  hence "max a (b-e):T" using e_def by auto
  moreover have "max a (b-e):{a..<b}" using e_def `a<b` by auto
  ultimately have "EX y:{a..<b}. y : T & y ~= b" by auto
} thus ?thesis unfolding islimpt_def by auto
qed


lemma lsc_hull_of_convex_aux:
  "Limsup (at 1 within {0..<1}) (%m. ereal ((1-m)*a+m*b)) <= ereal b"
proof-
  have nontr: "~trivial_limit (at 1 within {0..< 1::real})"
    apply (subst trivial_limit_within) using real_interval_limpt by auto
  have "((%m. ereal ((1-m)*a+m*b)) \<longlongrightarrow> (1 - 1) * a + 1 * b) (at 1 within {0..<1})"
    unfolding lim_ereal by (intro tendsto_intros)
  from lim_imp_Limsup[OF nontr this] show ?thesis by simp
qed


lemma lsc_hull_of_convex:
  fixes f :: "'a::euclidean_space => ereal"
  assumes "convex_on UNIV f"
  assumes "x : rel_interior (domain f)"
  shows "((%m. f((1-m)*\<^sub>R x + m *\<^sub>R y)) \<longlongrightarrow> (lsc_hull f) y) (at 1 within {0..<1})"
proof-
let "?g m" = "f((1-m)*\<^sub>R x + m *\<^sub>R y)"
{ assume "y=x" hence "?g = (%m. f y)" by (simp add: algebra_simps)
  hence "(?g \<longlongrightarrow> f y) (at 1 within {0..<1})" by (simp add: tendsto_const)
  moreover have "(lsc_hull f) y = f y" by (metis `y=x` assms lsc_hull_of_convex_agrees_onRI)
  ultimately have ?thesis by auto
}
moreover
{ assume "y~=x"
  have aux: "ALL m. y - ((1 - m) *\<^sub>R x + m *\<^sub>R y) = (1-m)*\<^sub>R (y-x)" by (simp add: algebra_simps)
  have "(lsc_hull f) y = min (f y) (Liminf (at y) f)" by (metis lsc_hull_liminf_at)
  also have "... <= Liminf (at 1 within {0..<1}) ?g" unfolding min_Liminf_at unfolding Liminf_within
     apply (subst SUP_mono) apply (rule_tac x="n/norm(y-x)" in bexI)
     apply (subst INF_mono) apply (rule_tac x="(1 - m) *\<^sub>R x + m *\<^sub>R y" in bexI) prefer 2
     unfolding ball_def dist_norm by (auto simp add: aux `y~=x` less_divide_eq)
  finally have *: "(lsc_hull f) y <= Liminf (at 1 within {0..<1}) ?g" by auto
  { fix b assume "ereal b>=(lsc_hull f) y"
    hence yb: "(y,b):closure(Epigraph UNIV f)" by (metis epigraph_lsc_hull mem_Epigraph UNIV_I)
    have "x : domain f" by (metis assms(2) rel_interior_subset set_rev_mp)
    hence "f x<\<infinity>" unfolding domain_def by auto
    then obtain a where"ereal a>f x" by (metis ereal_dense2)
      hence xa: "(x,a):rel_interior(Epigraph UNIV f)" by (metis assms rel_interior_Epigraph)
      { fix m :: real assume "0 <= m & m < 1"
        hence "(y, b) - (1-m) *\<^sub>R ((y, b) - (x, a)) : rel_interior (Epigraph UNIV f)"
          apply (subst rel_interior_closure_convex_shrink)
          apply (metis assms(1) convex_Epigraph convex_UNIV convex_on_ereal_univ)
          using yb xa by auto
        hence "f (y - (1-m) *\<^sub>R (y-x) ) < ereal (b-(1-m)*(b-a))"
          using assms(1) rel_interior_Epigraph by auto
        hence "?g m <= ereal ((1-m)*a+m*b)" by (simp add: algebra_simps)
      }
      hence "eventually (%m. ?g m <= ereal ((1-m)*a+m*b))
         (at 1 within {0..<1})" apply (subst always_eventually_within) by auto
      hence "Limsup (at 1 within {0..<1}) ?g <= Limsup (at 1 within {0..<1}) (%m. ereal ((1-m)*a+m*b))"
         apply (subst Limsup_mono) by auto
      also have "... <= ereal b" using lsc_hull_of_convex_aux by auto
      finally have "Limsup (at 1 within {0..<1}) ?g <=ereal b" by auto
    }
    hence "Limsup (at 1 within {0..<1}) ?g <= (lsc_hull f) y"
      using ereal_le_real[of "(lsc_hull f) y"] by auto
    moreover have nontr: "~trivial_limit (at (1::real) within {0..<1})"
       apply (subst trivial_limit_within) using real_interval_limpt by auto
    moreover hence "Liminf (at 1 within {0..<1}) ?g <= Limsup (at 1 within {0..<1}) ?g"
      apply (subst Liminf_le_Limsup) by auto
    ultimately have "Limsup (at 1 within {0..<1}) ?g = (lsc_hull f) y
                   & Liminf (at 1 within {0..<1}) ?g = (lsc_hull f) y"
      using * by auto
  hence ?thesis apply (subst Liminf_eq_Limsup) using nontr by auto
} ultimately show ?thesis by auto
qed

end
