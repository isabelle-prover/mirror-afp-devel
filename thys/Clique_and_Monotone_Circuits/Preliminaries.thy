section \<open>Preliminaries\<close>
theory Preliminaries
  imports 
    Main
    HOL.Real
    "HOL-Library.FuncSet"
begin

lemma exists_subset_between: 
  assumes 
    "card A \<le> n" 
    "n \<le> card C"
    "A \<subseteq> C"
    "finite C"
  shows "\<exists>B. A \<subseteq> B \<and> B \<subseteq> C \<and> card B = n" 
  using assms 
proof (induct n arbitrary: A C)
  case 0
  thus ?case using finite_subset[of A C] by (intro exI[of _ "{}"], auto)
next
  case (Suc n A C)
  show ?case
  proof (cases "A = {}")
    case True
    from obtain_subset_with_card_n[OF Suc(3)]
    obtain B where "B \<subseteq> C" "card B = Suc n" by metis
    thus ?thesis unfolding True by blast
  next
    case False
    then obtain a where a: "a \<in> A" by auto
    let ?A = "A - {a}" 
    let ?C = "C - {a}" 
    have 1: "card ?A \<le> n" using Suc(2-) a 
      using finite_subset by fastforce 
    have 2: "card ?C \<ge> n" using Suc(2-) a by auto
    from Suc(1)[OF 1 2 _ finite_subset[OF _ Suc(5)]] Suc(2-)
    obtain B where "?A \<subseteq> B" "B \<subseteq> ?C" "card B = n" by blast
    thus ?thesis using a Suc(2-) 
      by (intro exI[of _ "insert a B"], auto intro!: card_insert_disjoint finite_subset[of B C])
  qed
qed

lemma fact_approx_add: "fact (l + n) \<le> fact l * (real l + real n) ^ n" 
proof (induct n arbitrary: l)
  case (Suc n l)
  have "fact (l + Suc n) = (real l + Suc n) * fact (l + n)" by simp
  also have "\<dots> \<le> (real l + Suc n) * (fact l * (real l + real n) ^ n)" 
    by (intro mult_left_mono[OF Suc], auto)
  also have "\<dots> = fact l * ((real l + Suc n) * (real l + real n) ^ n)" by simp
  also have "\<dots> \<le> fact l * ((real l + Suc n) * (real l + real (Suc n)) ^ n)" 
    by (rule mult_left_mono, rule mult_left_mono, rule power_mono, auto)
  finally show ?case by simp
qed simp

lemma fact_approx_minus: assumes "k \<ge> n"
  shows "fact k \<le> fact (k - n) * (real k ^ n)"
proof -
  define l where "l = k - n" 
  from assms have k: "k = l + n" unfolding l_def by auto
  show ?thesis unfolding k using fact_approx_add[of l n] by simp
qed

lemma fact_approx_upper_add: assumes al: "a \<le> Suc l" shows "fact l * real a ^ n \<le> fact (l + n)" 
proof (induct n)
  case (Suc n)
  have "fact l * real a ^ (Suc n) = (fact l * real a ^ n) * real a" by simp
  also have "\<dots> \<le> fact (l + n) * real a" 
    by (rule mult_right_mono[OF Suc], auto)
  also have "\<dots> \<le> fact (l + n) * real (Suc (l + n))" 
    by (intro mult_left_mono, insert al, auto)
  also have "\<dots> = fact (Suc (l + n))" by simp
  finally show ?case by simp
qed simp

lemma fact_approx_upper_minus: assumes "n \<le> k" and "n + a \<le> Suc k" 
  shows "fact (k - n) * real a ^ n \<le> fact k" 
proof -
  define l where "l = k - n" 
  from assms have k: "k = l + n" unfolding l_def by auto
  show ?thesis using assms unfolding k 
    apply simp
    apply (rule fact_approx_upper_add, insert assms, auto simp: l_def)
    done
qed

lemma choose_mono: "n \<le> m \<Longrightarrow> n choose k \<le> m choose k" 
  unfolding binomial_def
  by (rule card_mono, auto)

lemma div_mult_le: "(a div b) * c \<le> (a * c) div (b :: nat)"
  by (metis div_mult2_eq div_mult_mult2 mult.commute mult_0_right times_div_less_eq_dividend)

lemma div_mult_pow_le: "(a div b)^n \<le> a^n div (b :: nat)^n"  
proof (cases "b = 0")
  case True
  thus ?thesis by (cases n, auto)
next
  case b: False  
  then obtain c d where a: "a = b * c + d" and id: "c = a div b" "d = a mod b" by auto
  have "(a div b)^n = c^n" unfolding id by simp
  also have "\<dots> = (b * c)^n div b^n" using b
    by (metis div_power dvd_triv_left nonzero_mult_div_cancel_left)
  also have "\<dots> \<le> (b * c + d)^n div b^n" 
    by (rule div_le_mono, rule power_mono, auto)
  also have "\<dots> = a^n div b^n " unfolding a by simp
  finally show ?thesis .
qed

lemma choose_inj_right:
  assumes id: "(n choose l) = (k choose l)" 
    and n0: "n choose l \<noteq> 0" 
    and l0:  "l \<noteq> 0" 
  shows "n = k"
proof (rule ccontr)
  assume nk: "n \<noteq> k" 
  define m where "m = min n k" 
  define M where "M = max n k" 
  from nk have mM: "m < M" unfolding m_def M_def by auto
  let ?new = "insert (M - 1) {0..< l - 1}" 
  let ?m = "{K \<in> Pow {0..<m}. card K = l}" 
  let ?M = "{K \<in> Pow {0..<M}. card K = l}" 
  from id n0 have lM :"l \<le> M" unfolding m_def M_def by auto
  from id have id: "(m choose l) = (M choose l)" 
    unfolding m_def M_def by auto
  from this[unfolded binomial_def]
  have "card ?M < Suc (card ?m)" 
    by auto
  also have "\<dots> = card (insert ?new ?m)" 
    by (rule sym, rule card_insert_disjoint, force, insert mM, auto)
  also have "\<dots> \<le> card (insert ?new ?M)" 
    by (rule card_mono, insert mM, auto)
  also have "insert ?new ?M = ?M" 
    by (insert mM lM l0, auto)
  finally show False by simp
qed

lemma card_funcsetE: "finite A \<Longrightarrow> card (A \<rightarrow>\<^sub>E B) = card B ^ card A" 
  by (subst card_PiE, auto)

lemma card_inj_on_subset_funcset: assumes finB: "finite B"
  and finC: "finite C" 
  and AB: "A \<subseteq> B" 
shows "card { f. f \<in> B \<rightarrow>\<^sub>E C \<and> inj_on f A} = 
  card C^(card B - card A) * prod ((-) (card C)) {0 ..< card A}"
proof -
  define D where "D = B - A" 
  from AB have B: "B = A \<union> D" and disj: "A \<inter> D = {}" unfolding D_def by auto
  have sub: "card B - card A = card D" unfolding D_def using finB AB
    by (metis card_Diff_subset finite_subset)
  have "finite A" "finite D" using finB unfolding B by auto
  thus ?thesis unfolding sub unfolding B using disj
  proof (induct A rule: finite_induct)
    case empty
    from card_funcsetE[OF this(1), of C] show ?case by auto
  next
    case (insert a A)
    have "{f. f \<in> insert a A \<union> D \<rightarrow>\<^sub>E C \<and> inj_on f (insert a A)}
      = {f(a := c) | f c. f \<in> A \<union> D \<rightarrow>\<^sub>E C \<and> inj_on f A \<and> c \<in> C - f ` A}" 
      (is "?l = ?r")
    proof
      show "?r \<subseteq> ?l" 
        by (auto intro: inj_on_fun_updI split: if_splits) 
      {
        fix f
        assume f: "f \<in> ?l" 
        let ?g = "f(a := undefined)" 
        let ?h = "?g(a := f a)" 
        have mem: "f a \<in> C - ?g ` A" using insert(1,2,4,5) f by auto
        from f have f: "f \<in> insert a A \<union> D \<rightarrow>\<^sub>E C" "inj_on f (insert a A)" by auto
        hence "?g \<in> A \<union> D \<rightarrow>\<^sub>E C" "inj_on ?g A" using \<open>a \<notin> A\<close> \<open>insert a A \<inter> D = {}\<close>
          by (auto split: if_splits simp: inj_on_def)
        with mem have "?h \<in> ?r" by blast
        also have "?h = f" by auto
        finally have "f \<in> ?r" .
      }
      thus "?l \<subseteq> ?r" by auto
    qed
    also have "\<dots> = (\<lambda> (f, c). f (a := c)) ` 
         (Sigma {f . f \<in> A \<union> D \<rightarrow>\<^sub>E C \<and> inj_on f A} (\<lambda> f. C - f ` A))"
      by auto
    also have "card (...) = card (Sigma {f . f \<in> A \<union> D \<rightarrow>\<^sub>E C \<and> inj_on f A} (\<lambda> f. C - f ` A))" 
    proof (rule card_image, intro inj_onI, clarsimp, goal_cases) 
      case (1 f c g d)
      let ?f = "f(a := c, a := undefined)" 
      let ?g = "g(a := d, a := undefined)" 
      from 1 have id: "f(a := c) = g(a := d)" by auto
      from fun_upd_eqD[OF id] 
      have cd: "c = d" by auto
      from id have "?f = ?g" by auto
      also have "?f = f" using `f \<in> A \<union> D \<rightarrow>\<^sub>E C` insert(1,2,4,5) 
        by (intro ext, auto)
      also have "?g = g" using `g \<in> A \<union> D \<rightarrow>\<^sub>E C` insert(1,2,4,5) 
        by (intro ext, auto)
      finally show "f = g \<and> c = d" using cd by auto
    qed
    also have "\<dots> = (\<Sum>f\<in>{f \<in> A \<union> D \<rightarrow>\<^sub>E C. inj_on f A}. card (C - f ` A))" 
      by (rule card_SigmaI, rule finite_subset[of _ "A \<union> D \<rightarrow>\<^sub>E C"],
          insert \<open>finite C\<close> \<open>finite D\<close> \<open>finite A\<close>, auto intro!: finite_PiE)
    also have "\<dots> = (\<Sum>f\<in>{f \<in> A \<union> D \<rightarrow>\<^sub>E C. inj_on f A}. card C - card A)"
      by (rule sum.cong[OF refl], subst card_Diff_subset, insert \<open>finite A\<close>, auto simp: card_image)
    also have "\<dots> = (card C - card A) * card {f \<in> A \<union> D \<rightarrow>\<^sub>E C. inj_on f A}" 
      by simp
    also have "\<dots> = card C ^ card D * ((card C - card A) * prod ((-) (card C)) {0..<card A})" 
      using insert by (auto simp: ac_simps)
    also have "(card C - card A) * prod ((-) (card C)) {0..<card A} =
      prod ((-) (card C)) {0..<Suc (card A)}" by simp
    also have "Suc (card A) = card (insert a A)" using insert by auto
    finally show ?case .
  qed
qed


end