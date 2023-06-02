(*
  Quadratics.thy
  author: Mike Stannett
  Date: 4 Jan 2023
*)

section \<open> Quadratics \<close>

text \<open> This theory shows how to find the roots of a quadratic,
assuming that roots exist (AxEField). \<close>


theory "Quadratics"
  imports Functions AxEField
begin

class Quadratics = Functions + AxEField
begin

abbreviation quadratic :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a)"
  where "quadratic a b c \<equiv> \<lambda> x . a*(sqr x) + b*x + c"

abbreviation qroot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qroot a b c r \<equiv> (quadratic a b c) r = 0"

abbreviation qroots :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "qroots a b c \<equiv> { r . qroot a b c r }"

abbreviation discriminant :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "discriminant a b c \<equiv> (sqr b) - 4*a*c"

abbreviation qcase1  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qcase1 a b c \<equiv> (a = 0 \<and> b = 0 \<and> c = 0)"
abbreviation qcase2  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qcase2 a b c \<equiv> (a = 0 \<and> b = 0 \<and> c \<noteq> 0)"
abbreviation qcase3  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qcase3 a b c \<equiv> (a = 0 \<and> b \<noteq> 0 \<and> (c = 0 \<or> c \<noteq>0))"
abbreviation qcase4  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qcase4 a b c \<equiv> (a \<noteq> 0 \<and> discriminant a b c < 0)"
abbreviation qcase5  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qcase5 a b c \<equiv> (a \<noteq> 0 \<and> discriminant a b c = 0)"
abbreviation qcase6  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "qcase6 a b c \<equiv> (a \<noteq> 0 \<and> discriminant a b c > 0)"



lemma lemQuadRootCondition: 
  assumes "a \<noteq> 0"
  shows "(sqr (2*a*r + b) = discriminant a b c) \<longleftrightarrow> qroot a b c r"
proof -
  have "sqr (2*a*r) = (4*a) * (a * sqr r)" 
    using lemSqrMult local.numeral_sqr mult_assoc sqr.simps(1) sqr.simps(2)
    by metis
  moreover have "2*(2*a*r)*b = (4*a) * (b*r)"
    by (metis dbl_def dbl_simps(5) mult.left_commute mult_2 mult_2_right mult_assoc)
  ultimately have s: "sqr (2*a*r) + 2*(2*a*r)*b = (4*a) * ((a * sqr r) + b *r)"
    by (simp add: local.distrib_left)

  have "sqr(2*a*r + b) = sqr (2*a*r) + 2*(2*a*r)*b + sqr b"
    using lemSqrSum by auto
  moreover have "\<dots> = (4*a) * ((a * sqr r) + b *r) + sqr b" using s by auto
  moreover have "\<dots> = (4*a) * ((a * sqr r) + b *r + c) - (4*a)*c + sqr b" 
    by (simp add: distrib_left)
  ultimately have eqn1: "sqr(2*a*r + b) = (4*a)*(quadratic a b c r) + (discriminant a b c)"
    by (simp add: add_diff_eq diff_add_eq)

  { assume "qroot a b c r"
    hence "sqr (2*a*r + b) = discriminant a b c" using eqn1 by simp
  }
  hence l2r: "qroot a b c r \<longrightarrow> sqr (2*a*r + b) = discriminant a b c" by auto

  { assume "sqr (2*a*r + b) = discriminant a b c"
    hence "0 = (4*a)*(quadratic a b c r)" using eqn1 by auto
    hence "qroot a b c r" by (metis assms divisors_zero zero_neq_numeral)
  }
  hence "(sqr (2*a*r + b) = discriminant a b c) \<longrightarrow> qroot a b c r" by blast

  thus ?thesis using l2r by blast
qed


lemma lemQuadraticCasesComplete:
  shows  "qcase1 a b c \<or> qcase2 a b c \<or> qcase3 a b c \<or> qcase4 a b c \<or>
             qcase5 a b c \<or> qcase6 a b c"
  using not_less_iff_gr_or_eq by blast


lemma lemQCase1:
  assumes "qcase1 a b c"
  shows "\<forall> r . qroot a b c r"
  using assms by simp


lemma lemQCase2:
  assumes "qcase2 a b c"
  shows "\<not> (\<exists> r . qroot a b c r)"
  by (simp add: assms)


lemma lemQCase3:
  assumes "qcase3 a b c"
  shows "qroot a b c r \<longleftrightarrow> r = -c/b"
proof -
  have "qroot a b c r \<longrightarrow> r = -c/b" 
  proof -
    { assume hyp: "qroot a b c r"
      hence "b*r + c = 0" using assms by auto
      hence "b*r = -c" by (simp add: local.eq_neg_iff_add_eq_0)
      hence "r = -c/b" by (metis assms local.nonzero_mult_div_cancel_left)
    }
    thus ?thesis by auto
  qed
  moreover have "r = -c/b \<longrightarrow> qroot a b c r" by (simp add: assms)
  ultimately show ?thesis by blast
qed




lemma lemQCase4:
  assumes "qcase4 a b c"
  shows "\<not> (\<exists> r . qroot a b c r)"
proof -
  have props: "(a \<noteq> 0 \<and> discriminant a b c < 0)" using assms by auto
  { assume hyp: "\<exists> r . qroot a b c r"
    then obtain r where r: "qroot a b c r" by auto
    hence "sqr (2 * a * r + b) = discriminant a b c" 
      using props lemQuadRootCondition[of "a" "r" "b" "c"] by auto
    hence "sqr (2*a*r + b) < 0" using props by auto
    hence "False" using lemSquaresPositive by auto
  }
  thus ?thesis by auto
qed



lemma lemQCase5:
  assumes "qcase5 a b c"
  shows "qroot a b c r \<longleftrightarrow> r = -b/(2*a)"
proof -
  have "qroot a b c r \<longrightarrow> r = -b/(2*a)"
  proof -
    { assume hyp: "qroot a b c r"
      hence "sqr (2 * a * r + b) = 0" 
        using assms lemQuadRootCondition[of "a" "r" "b" "c"] by auto
      hence "2*a*r + b = 0" by simp
      hence "2*a*r = -b" using local.eq_neg_iff_add_eq_0 by auto
      moreover have "2*a \<noteq> 0" using assms by auto
      ultimately have "r = ((-b)/(2*a))" by (metis local.nonzero_mult_div_cancel_left)
    }
    thus ?thesis by auto
  qed
  moreover have "r = -b/(2*a) \<longrightarrow> qroot a b c r"
  proof -
    { assume hyp: "r = -b/(2*a)"
      hence "(2*a)*r + b = discriminant a b c" by (simp add: assms)
      hence "qroot a b c r" using lemQuadRootCondition[of "a" "r" "b" "c"] assms by auto
    }
    thus ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed



lemma lemQCase6:
  assumes "qcase6 a b c"
and "rd = sqrt (discriminant a b c)"
and "rp = ((-b) + rd) / (2*a)"
and "rm = ((-b) - rd) / (2*a)"
  shows "(rp \<noteq> rm) \<and> qroots a b c = { rp, rm }"
proof -
  define d  where  d: "d = discriminant a b c"

  (* need to show rd exists and is non-zero *)
  have dpos: "d > 0" using assms d by auto
  hence rootd: "hasUniqueRoot d" using AxEField lemSqrt[of "d"] by auto
  hence rdprops: "0 \<le> rd \<and> d = sqr rd"
    using assms(2) d theI'[of "isNonNegRoot d"] by auto
  hence rdnot0: "rd \<noteq> 0" using assms dpos mult_nonneg_nonpos by auto
  hence rdpos:  "rd > 0" using rdprops by auto

  define pp where pp: "pp = (-b) + rd"
  define mm where mm: "mm = (-b) - rd"
  have "rd \<noteq> -rd" using rdnot0 by simp
  hence "pp \<noteq> mm" using pp mm add_left_imp_eq[of "-b" "rd" "-rd"] by auto
  moreover have aa: "2*a \<noteq> 0" using assms by auto
  ultimately have "pp/(2*a) \<noteq> mm/(2*a)" by auto
  hence conj1: "rp \<noteq> rm" using assms pp mm by simp

  have conj2: "qroots a b c = {rp, rm}" 
  proof -
    { fix r assume "r \<in> qroots a b c"
      hence "sqr (2*a*r + b) = d" 
        using assms lemQuadRootCondition d by auto
      hence "sqrt d = abs (2*a*r + b)" using lemSqrtOfSquare by blast
      moreover have "sqrt d = rd" using d assms by auto
      ultimately have rdprops: "rd = abs (2*a*r + b)" by auto

      define v :: "'a" where v: "v = 2*a*r + b"
      hence vnot0: "v \<noteq> 0" using rdprops rdnot0 by simp
      hence cases: "(v < 0) \<or> (v > 0)" by auto

      { assume "v < 0"
        hence "2*a*r + b = -rd" using v rdprops
          by (metis local.abs_if local.minus_minus)
        hence "2*a*r = (-b) - rd"
          by (metis local.add_diff_cancel_right' local.minus_diff_commute)
        hence "r = rm" using aa assms(4)
          by (metis local.nonzero_mult_div_cancel_left)
      }
      hence case1: "v < 0 \<longrightarrow> r = rm" by auto
        
      { assume "v > 0"
        hence "2*a*r + b = rd" using v rdprops by simp
        hence "2*a*r = (-b) + rd" by auto
        hence "r = rp" using aa assms(3)
          by (metis local.nonzero_mult_div_cancel_left)
      }
      hence "v > 0 \<longrightarrow> r = rp" by auto

      hence "r = rm \<or> r = rp" using case1 cases by blast
      hence "r \<in> { rm, rp }" by blast
    }
    hence "\<forall> r . r \<in> qroots a b c \<longrightarrow> r \<in> { rm, rp }" by blast
    hence l2r: "qroots a b c \<subseteq> {rm, rp}" by auto

    have rootm: "qroot a b c rm"
    proof -
      have "rm = ((-b) - rd) / (2*a)" using assms by auto
      hence "(2*a)*rm = (-b) - rd" using aa by simp
      hence "(2*a)*rm + b = - rd" by (simp add: local.diff_add_eq)
      hence "sqr( (2*a)*rm + b ) = sqr rd" by simp
      moreover have "\<dots> = discriminant a b c" 
        using assms(2) rootd d lemSquareOfSqrt[of "discriminant a b c" "rd"] by auto
      ultimately show ?thesis 
        using assms lemQuadRootCondition[of "a" "rm" "b" "c"] by auto
    qed

    have rootp: "qroot a b c rp"
    proof -
      have "rp = ((-b) + rd) / (2*a)" using assms by auto
      hence "(2*a)*rp = (-b) + rd" using aa by simp
      hence "(2*a)*rp + b = rd" by (simp add: local.diff_add_eq)
      hence "sqr( (2*a)*rp + b ) = sqr rd" by simp
      moreover have "\<dots> = discriminant a b c" 
        using assms(2) rootd d lemSquareOfSqrt[of "discriminant a b c" "rd"] by auto
      ultimately show ?thesis 
        using assms lemQuadRootCondition[of "a" "rp" "b" "c"] by auto
    qed

    hence "{rm, rp} \<subseteq> qroots a b c" using rootm rootp by auto
    thus ?thesis using l2r by blast
  qed

  thus ?thesis using conj1 by blast
qed


lemma lemQuadraticRootCount:
  assumes "\<not>(qcase1 a b c)"
  shows "finite (qroots a b c) \<and> card (qroots a b c) \<le> 2"
proof -
  define d  where  d: "d = discriminant a b c"

  have case1: "qcase1 a b c \<longrightarrow> ?thesis" using assms by auto
  moreover have case2: "qcase2 a b c \<longrightarrow> ?thesis" using lemQCase2 by auto
  moreover have case3: "qcase3 a b c \<longrightarrow> ?thesis" using lemQCase3 by auto
  moreover have case4: "qcase4 a b c \<longrightarrow> ?thesis" using lemQCase4 by auto
  moreover have case5: "qcase5 a b c \<longrightarrow> ?thesis" using lemQCase5 by auto
  moreover have case6: "qcase6 a b c \<longrightarrow> ?thesis" using lemQCase6 card_2_iff by auto
  ultimately show ?thesis using lemQuadraticCasesComplete by blast
qed


end (* of class Quadratics *)

end (* of theory Quadratics *)

