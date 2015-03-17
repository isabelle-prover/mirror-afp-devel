theory "Mono-Nat-Fun"
imports "~~/src/HOL/Library/Infinite_Set"
begin

text {*
The following lemma proves that a monotonous function from and to the natural numbers is either eventually
constant or unbounded.
*}

lemma nat_mono_characterization:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "mono f"
  obtains n where "\<And>m . n \<le> m \<Longrightarrow> f n = f m" | "\<And> m . \<exists> n . m \<le> f n"
proof (cases "finite (range f)")
  case True
  from Max_in[OF True]
  obtain n where Max: "f n = Max (range f)" by auto
  show thesis
  proof(rule that(1))
    fix m
    assume "n \<le> m"
    hence "f n \<le> f m" using `mono f` by (metis monoD)
    also
    have "f m \<le> f n" unfolding Max by (rule Max_ge[OF True rangeI])
    finally
    show "f n = f m".
  qed
next
  case False
  thus thesis by (fastforce intro: that(2) simp add: infinite_nat_iff_unbounded_le)
qed

end
