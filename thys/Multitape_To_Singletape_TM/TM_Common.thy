section \<open>Preparations\<close>

theory TM_Common
  imports 
    "HOL-Library.FuncSet"
begin

text \<open>A direction of a TM: go right, go left, or neutral (stay)\<close>
datatype dir = R | L | N

fun go_dir :: "dir \<Rightarrow> nat \<Rightarrow> nat" where
  "go_dir R n = Suc n" 
| "go_dir L n = n - 1" 
| "go_dir N n = n" 

lemma finite_UNIV_dir[simp, intro]: "finite (UNIV :: dir set)" 
proof -
  have id: "UNIV = {L,R,N}"
    using dir.exhaust by auto
  show ?thesis unfolding id by auto
qed

hide_const (open) L R N

lemma fin_funcsetI[intro]: "finite A \<Longrightarrow> finite ((UNIV :: 'a :: finite set) \<rightarrow> A)" 
  by (metis PiE_UNIV_domain finite_PiE finite_code)

lemma finite_UNIV_fun_dir[simp,intro]: "finite (UNIV :: ('k :: finite \<Rightarrow> dir) set)" 
  using fin_funcsetI[OF finite_UNIV_dir] by auto

lemma relpow_transI: "(x,y) \<in> R^^n \<Longrightarrow> (y,z) \<in> R^^m \<Longrightarrow> (x,z) \<in> R^^(n+m)"
  by (simp add: relcomp.intros relpow_add)

lemma relpow_mono: fixes R :: "'a rel" shows "R \<subseteq> S \<Longrightarrow> R^^n \<subseteq> S^^n"
  by (induct n, auto)

lemma finite_infinite_inj_on: assumes A: "finite (A :: 'a set)" and inf: "infinite (UNIV :: 'b set)" 
  shows "\<exists> f :: 'a \<Rightarrow> 'b. inj_on f A"
proof -
  from inf obtain B :: "'b set" where B: "finite B" "card B = card A"
    by (meson infinite_arbitrarily_large)
  from A B obtain f :: "'a \<Rightarrow> 'b" where "bij_betw f A B"
    by (metis bij_betw_iff_card)
  thus ?thesis by (intro exI[of _ f], auto simp: bij_betw_def)
qed

lemma gauss_sum_nat2: "(\<Sum>i< (n :: nat). i) = (n - 1) * n div 2"
proof (cases n)
  case (Suc m)
  hence id: "{..<n} = {0..m}" by auto
  show ?thesis unfolding id unfolding gauss_sum_nat unfolding Suc by auto
qed auto

lemma aux_sum_formula: "(\<Sum>i<n. 10 + 5 * i) \<le> 3 * n^2 + 7 * (n :: nat)" 
proof -
  have "(\<Sum>i<n. 10 + 5 * i) = 10 * n + 5 * (\<Sum>i<n. i)" 
    by (subst sum.distrib, auto simp: sum_distrib_left)
  also have "\<dots> \<le> 10 * n + 3 * ((n - 1) * n)" 
    by (unfold gauss_sum_nat2, rule add_left_mono, cases n, auto)
  also have "\<dots> = 3 * n^2 + 7 * n" 
    unfolding power2_eq_square by (cases n, auto)
  finally show ?thesis .
qed

end
