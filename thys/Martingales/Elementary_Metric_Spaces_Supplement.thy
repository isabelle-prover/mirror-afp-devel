theory Elementary_Metric_Spaces_Supplement
  imports "HOL-Analysis.Elementary_Metric_Spaces"
begin

section \<open>Supplementary Lemmas for Elementary Metric Spaces\<close>

subsection \<open>Diameter Lemma\<close>

lemma diameter_comp_strict_mono:
  fixes s :: "nat \<Rightarrow> 'a :: metric_space"
  assumes "strict_mono r" "bounded {s i |i. r n \<le> i}"
  shows "diameter {s (r i) | i. n \<le> i} \<le> diameter {s i | i. r n \<le> i}"
proof (rule diameter_subset)
  show "{s (r i) | i. n \<le> i} \<subseteq> {s i | i. r n \<le> i}" using assms(1) monotoneD strict_mono_mono by fastforce
qed (intro assms(2))

lemma diameter_bounded_bound':
  fixes S :: "'a :: metric_space set"
  assumes S: "bdd_above (case_prod dist ` (S\<times>S))" "x \<in> S" "y \<in> S"
  shows "dist x y \<le> diameter S"
proof -
  have "(x,y) \<in> S\<times>S" using S by auto
  then have "dist x y \<le> (SUP (x,y)\<in>S\<times>S. dist x y)" by (rule cSUP_upper2[OF assms(1)]) simp
  with \<open>x \<in> S\<close> show ?thesis by (auto simp: diameter_def)
qed

lemma bounded_imp_dist_bounded:
  assumes "bounded (range s)"
  shows "bounded ((\<lambda>(i, j). dist (s i) (s j)) ` ({n..} \<times> {n..}))"
  using bounded_dist_comp[OF bounded_fst bounded_snd, OF bounded_Times(1,1)[OF assms(1,1)]] by (rule bounded_subset, force) 

text \<open>A sequence is Cauchy, if and only if it is bounded and it's diameter tends to zero. The diameter is well-defined only if the sequence is bounded.\<close>
lemma cauchy_iff_diameter_tends_to_zero_and_bounded:
  fixes s :: "nat \<Rightarrow> 'a :: metric_space"
  shows "Cauchy s \<longleftrightarrow> ((\<lambda>n. diameter {s i | i. i \<ge> n}) \<longlonglongrightarrow> 0 \<and> bounded (range s))"
proof -
  have "{s i |i. N \<le> i} \<noteq> {}" for N by blast
  hence diameter_SUP: "diameter {s i |i. N \<le> i} = (SUP (i, j) \<in> {N..} \<times> {N..}. dist (s i) (s j))" for N unfolding diameter_def by (auto intro!: arg_cong[of _ _ Sup])
  show ?thesis 
  proof (intro iffI)
    assume asm: "Cauchy s"
    have "\<exists>N. \<forall>n\<ge>N. norm (diameter {s i |i. n \<le> i}) < e" if e_pos: "e > 0" for e
    proof -
      obtain N where dist_less: "dist (s n) (s m) < (1/2) * e" if "n \<ge> N" "m \<ge> N" for n m using asm e_pos by (metis Cauchy_def mult_pos_pos zero_less_divide_iff zero_less_numeral zero_less_one)
      {
        fix r assume "r \<ge> N"
        hence "dist (s n) (s m) < (1/2) * e" if "n \<ge> r" "m \<ge> r" for n m using dist_less that by simp
        hence "(SUP (i, j) \<in> {r..} \<times> {r..}. dist (s i) (s j)) \<le> (1/2) * e" by (intro cSup_least) fastforce+
        also have "... < e" using e_pos by simp
        finally have "diameter {s i |i. r \<le> i} < e" using diameter_SUP by presburger
      }
      moreover have "diameter {s i |i. r \<le> i} \<ge> 0" for r unfolding diameter_SUP using bounded_imp_dist_bounded[OF cauchy_imp_bounded, THEN bounded_imp_bdd_above, OF asm] by (intro cSup_upper2, auto)
      ultimately show ?thesis by auto
    qed                 
    thus "(\<lambda>n. diameter {s i |i. n \<le> i}) \<longlonglongrightarrow> 0 \<and> bounded (range s)" using cauchy_imp_bounded[OF asm] by (simp add: LIMSEQ_iff)
  next
    assume asm: "(\<lambda>n. diameter {s i |i. n \<le> i}) \<longlonglongrightarrow> 0 \<and> bounded (range s)"
    have "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (s n) (s m) < e" if e_pos: "e > 0" for e
    proof -
      obtain N where diam_less: "diameter {s i |i. r \<le> i} < e" if "r \<ge> N" for r using LIMSEQ_D asm(1) e_pos by fastforce
      {
        fix n m assume "n \<ge> N" "m \<ge> N"
        hence "dist (s n) (s m) < e" using cSUP_lessD[OF bounded_imp_dist_bounded[THEN bounded_imp_bdd_above], OF _ diam_less[unfolded diameter_SUP]] asm by auto
      }
      thus ?thesis by blast
    qed
    then show "Cauchy s" by (simp add: Cauchy_def)
  qed            
qed
  
end