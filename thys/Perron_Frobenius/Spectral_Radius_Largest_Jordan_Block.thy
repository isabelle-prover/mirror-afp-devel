(* Author: Thiemann *)

section \<open>The Jordan Blocks of the Spectral Radius are Largest\<close>

text \<open>Consider a non-negative real matrix, and consider any Jordan-block
  of any eigenvalues whose norm is the spectral radius. We prove that there is
  a Jordan block of the spectral radius which has the same size or is larger.\<close>

theory Spectral_Radius_Largest_Jordan_Block
imports 
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
  Perron_Frobenius_General
  "HOL-Real_Asymp.Real_Asymp"
begin

lemma poly_asymp_equiv: "(\<lambda>x. poly p (real x)) \<sim>[at_top] (\<lambda>x. lead_coeff p * real x ^ (degree p))" 
proof (cases "degree p = 0")
  case False
  hence lc: "lead_coeff p \<noteq> 0" by auto
  have 1: "1 = (\<Sum>n\<le>degree p. if n = degree p then (1 :: real) else 0)" by simp
  from False show ?thesis
  proof (intro asymp_equivI', unfold poly_altdef sum_divide_distrib, 
      subst 1, intro tendsto_sum, goal_cases)
    case (1 n)
    hence "n = degree p \<or> n < degree p" by auto
    thus ?case 
    proof
      assume "n = degree p" 
      thus ?thesis using False lc
        by (simp, intro LIMSEQ_I exI[of _ "Suc 0"], auto)
    qed (insert False lc, real_asymp)
  qed
next
  case True
  then obtain c where p: "p = [:c:]" by (metis degree_eq_zeroE)
  show ?thesis unfolding p by simp
qed

lemma sum_root_unity: fixes x :: "'a :: {comm_ring,division_ring}" 
  assumes "x^n = 1" 
  shows "sum (\<lambda> i. x^i) {..< n} = (if x = 1 then of_nat n else 0)" 
proof (cases "x = 1 \<or> n = 0")
  case x: False
  from x obtain m where n: "n = Suc m" by (cases n, auto)
  have id: "{..< n} = {0..m}" unfolding n by auto
  show ?thesis using assms x n unfolding id sum_gp by (auto simp: divide_inverse)
qed auto

lemma sum_root_unity_power_pos_implies_1:  
  assumes sumpos: "\<And> k. Re (sum (\<lambda> i. b i * x i ^ k) I) > 0" 
  and root_unity: "\<And> i. i \<in> I \<Longrightarrow> \<exists> d. d \<noteq> 0 \<and> x i ^ d = 1" 
shows "1 \<in> x ` I" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  hence x: "i \<in> I \<Longrightarrow> x i \<noteq> 1" for i by auto
  from sumpos[of 0] have I: "finite I" "I \<noteq> {}" 
    using sum.infinite by fastforce+
  have "\<forall> i. \<exists> d. i \<in> I \<longrightarrow> d \<noteq> 0 \<and> x i ^ d = 1" using root_unity by auto
  from choice[OF this] obtain d where d: "\<And> i. i \<in> I \<Longrightarrow> d i \<noteq> 0 \<and> x i ^ (d i) = 1" by auto
  define D where "D = prod d I" 
  have D0: "0 < D" unfolding D_def
    by (rule prod_pos, insert d, auto)
  have "0 < sum (\<lambda> k. Re (sum (\<lambda> i. b i * x i ^ k) I)) {..< D}" 
    by (rule sum_pos[OF _ _ sumpos], insert D0, auto)
  also have "\<dots> = Re (sum (\<lambda> k. sum (\<lambda> i. b i * x i ^ k) I) {..< D})" by auto
  also have "sum (\<lambda> k. sum (\<lambda> i. b i * x i ^ k) I) {..< D}
    = sum (\<lambda> i. sum (\<lambda> k. b i * x i ^ k) {..< D}) I" by (rule sum.swap)
  also have "\<dots> = sum (\<lambda> i. b i * sum (\<lambda> k. x i ^ k) {..< D}) I"
    by (rule sum.cong, auto simp: sum_distrib_left)
  also have "\<dots> = 0" 
  proof (rule sum.neutral, intro ballI)
    fix i
    assume i: "i \<in> I" 
    from d[OF this] x[OF this] have d: "d i \<noteq> 0" and rt_unity: "x i ^ d i = 1" 
      and x: "x i \<noteq> 1" by auto
    have "\<exists> C. D = d i * C" unfolding D_def
      by (subst prod.remove[of _ i], insert i I, auto)
    then obtain C where D: "D = d i * C" by auto
    have image: "(\<And> x. f x = x) \<Longrightarrow> {..< D} = f ` {..< D}" for f by auto
    let ?g = "(\<lambda> (a,c). a + d i * c)" 
    have "{..< D} = ?g ` (\<lambda> j. (j mod d i, j div d i)) ` {..< d i * C}" 
      unfolding image_image split D[symmetric] by (rule image, insert d mod_mult_div_eq, blast)
    also have "(\<lambda> j. (j mod d i, j div d i)) ` {..< d i * C} = {..< d i} \<times> {..< C}" (is "?f ` ?A = ?B")
    proof -
      {
        fix x
        assume "x \<in> ?B" then obtain a c where x: "x = (a,c)" and a: "a < d i" and c: "c < C" by auto 
        hence "a + c * d i < d i * (1 + c)" by simp
        also have "\<dots> \<le> d i * C" by (rule mult_le_mono2, insert c, auto)
        finally have "a + c * d i \<in> ?A" by auto
        hence "?f (a + c * d i) \<in> ?f ` ?A" by blast
        also have "?f (a + c * d i) = x" unfolding x using a by auto
        finally have "x \<in> ?f ` ?A" .
      }
      thus ?thesis using d by (auto simp: div_lt_nat)
    qed
    finally have D: "{..< D} = (\<lambda> (a,c). a + d i * c) ` ?B" by auto
    have inj: "inj_on ?g ?B"
    proof -
      {
        fix a1 a2 c1 c2
        assume id: "?g (a1,c1) = ?g (a2,c2)" and *: "(a1,c1) \<in> ?B" "(a2,c2) \<in> ?B" 
        from arg_cong[OF id, of "\<lambda> x. x div d i"] * have c: "c1 = c2" by auto
        from arg_cong[OF id, of "\<lambda> x. x mod d i"] * have a: "a1 = a2" by auto
        note a c
      }
      thus ?thesis by (smt SigmaE inj_onI)
    qed
    have "sum (\<lambda> k. x i ^ k) {..< D} = sum (\<lambda> (a,c). x i ^ (a + d i * c)) ?B" 
      unfolding D by (subst sum.reindex, rule inj, auto intro!: sum.cong) 
    also have "\<dots> = sum (\<lambda> (a,c). x i ^ a) ?B" 
      by (rule sum.cong, auto simp: power_add power_mult rt_unity)
    also have "\<dots> = 0" unfolding sum.cartesian_product[symmetric]  sum.swap[of _ "{..<C}"]
      by (rule sum.neutral, intro ballI, subst sum_root_unity[OF rt_unity], insert x, auto)
    finally 
    show "b i * sum (\<lambda> k. x i ^ k) {..< D} = 0" by simp
  qed
  finally show False by simp
qed

fun j_to_jb_index :: "(nat \<times> 'a)list \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "j_to_jb_index ((n,a) # n_as) i = (if i < n then (0,i) else 
     let rec = j_to_jb_index n_as (i - n) in (Suc (fst rec), snd rec))" 

fun jb_to_j_index :: "(nat \<times> 'a)list \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "jb_to_j_index n_as (0,j) = j" 
| "jb_to_j_index ((n,_) # n_as) (Suc i, j) = n + jb_to_j_index n_as (i,j)" 

lemma j_to_jb_index: assumes "i < sum_list (map fst n_as)" 
  and "j < sum_list (map fst n_as)" 
  and "j_to_jb_index n_as i = (bi, li)" 
  and "j_to_jb_index n_as j = (bj, lj)" 
  and "n_as ! bj = (n, a)" 
shows "((jordan_matrix n_as) ^\<^sub>m r) $$ (i,j) = (if bi = bj then ((jordan_block n a) ^\<^sub>m r) $$ (li, lj) else 0)
  \<and> (bi = bj \<longrightarrow> li < n \<and> lj < n \<and> bj < length n_as \<and> (n,a) \<in> set n_as)"
  unfolding jordan_matrix_pow using assms
proof (induct n_as arbitrary: i j bi bj)
  case (Cons mb n_as i j bi bj)
  obtain m b where mb: "mb = (m,b)" by force
  note Cons = Cons[unfolded mb]
  have [simp]: "dim_col (case x of (n, a) \<Rightarrow> 1\<^sub>m n) = fst x" for x by (cases x, auto)
  have [simp]: "dim_row (case x of (n, a) \<Rightarrow> 1\<^sub>m n) = fst x" for x by (cases x, auto)
  have [simp]: "dim_col (case x of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) = fst x" for x by (cases x, auto)
  have [simp]: "dim_row (case x of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) = fst x" for x by (cases x, auto)
  consider (UL) "i < m" "j < m" | (UR) "i < m" "j \<ge> m" | (LL) "i \<ge> m" "j < m" 
    | (LR) "i \<ge> m" "j \<ge> m" by linarith
  thus ?case
  proof cases
    case UL
    with Cons(2-) show ?thesis unfolding mb by (auto simp: Let_def)
  next
    case UR
    with Cons(2-) show ?thesis unfolding mb by (auto simp: Let_def dim_diag_block_mat o_def)
  next
    case LL
    with Cons(2-) show ?thesis unfolding mb by (auto simp: Let_def dim_diag_block_mat o_def)
  next
    case LR
    let ?i = "i - m" 
    let ?j = "j - m" 
    from LR Cons(2-) have bi: "j_to_jb_index n_as ?i = (bi - 1, li)" "bi \<noteq> 0" by (auto simp: Let_def)
    from LR Cons(2-) have bj: "j_to_jb_index n_as ?j = (bj - 1, lj)" "bj \<noteq> 0" by (auto simp: Let_def)
    from LR Cons(2-) have i: "?i < sum_list (map fst n_as)" by auto
    from LR Cons(2-) have j: "?j < sum_list (map fst n_as)" by auto
    from LR Cons(2-) bj(2) have nas: "n_as ! (bj - 1) = (n, a)" by (cases bj, auto)
    from bi(2) bj(2) have id: "(bi - 1 = bj - 1) = (bi = bj)" by auto
    note IH = Cons(1)[OF i j bi(1) bj(1) nas, unfolded id]
    have id: "diag_block_mat (map (\<lambda>a. case a of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) (mb # n_as)) $$ (i, j)
      = diag_block_mat (map (\<lambda>a. case a of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) n_as) $$ (?i, ?j)" 
      using i j LR unfolding mb by (auto simp: Let_def dim_diag_block_mat o_def)
    show ?thesis using IH unfolding id by auto
  qed     
qed auto

lemma j_to_jb_index_rev: assumes j: "j_to_jb_index n_as i = (bi, li)" 
  and i: "i < sum_list (map fst n_as)" 
  and k: "k \<le> li" 
shows "li \<le> i \<and> j_to_jb_index n_as (i - k) = (bi, li - k) \<and> (
  j_to_jb_index n_as j = (bi,li - k) \<longrightarrow> j < sum_list (map fst n_as) \<longrightarrow> j = i - k)"
  using j i
proof (induct n_as arbitrary: i bi j)
  case (Cons mb n_as i bi j)
  obtain m b where mb: "mb = (m,b)" by force
  note Cons = Cons[unfolded mb]
  show ?case
  proof (cases "i < m")
    case True
    thus ?thesis unfolding mb using Cons(2-) by (auto simp: Let_def)
  next
    case i_large: False
    let ?i = "i - m" 
    have i: "?i < sum_list (map fst n_as)" using Cons(2-) i_large by auto
    from Cons(2-) i_large have j: "j_to_jb_index n_as ?i = (bi - 1, li)" 
      and bi: "bi \<noteq> 0" by (auto simp: Let_def)
    note IH = Cons(1)[OF j i]
    from IH have IH1: "j_to_jb_index n_as (i - m - k) = (bi - 1, li - k)" and
       li: "li \<le> i - m" by auto
    from li have aim1: "li \<le> i" by auto
    from li k i_large have "i - k \<ge> m" by auto
    hence aim2: "j_to_jb_index (mb # n_as) (i - k) = (bi, li - k)" 
      using IH1 bi by (auto simp: mb Let_def add.commute)
    {
      assume *: "j_to_jb_index (mb # n_as) j = (bi, li - k)"
        "j < sum_list (map fst (mb # n_as))" 
      from * bi have j: "j \<ge> m" unfolding mb by (auto simp: Let_def split: if_splits)
      let ?j = "j - m" 
      from j * have jj: "?j < sum_list (map fst n_as)" unfolding mb by auto
      from j * have **: "j_to_jb_index n_as (j - m) = (bi - 1, li - k)" using bi mb 
        by (cases "j_to_jb_index n_as (j - m)", auto simp: Let_def)
      from IH[of ?j] jj ** have "j - m = i - m - k" by auto
      with j i_large k have "j = i - k" using \<open>m \<le> i - k\<close> by linarith
    } note aim3 = this
    show ?thesis using aim1 aim2 aim3 by blast
  qed
qed auto  
  

locale spectral_radius_1_jnf_max = 
  fixes A :: "real mat" and n m :: nat and lam :: complex and n_as
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and jnf: "jordan_nf (map_mat complex_of_real A) n_as" 
  and mem: "(m, lam) \<in> set n_as" 
  and lam1: "cmod lam = 1"  
  and sr1: "\<And>x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  and max_block: "\<And> k la. (k,la) \<in> set n_as \<Longrightarrow> cmod la \<le> 1 \<and> (cmod la = 1 \<longrightarrow> k \<le> m)" 
begin

lemma n_as0: "0 \<notin> fst ` set n_as" 
  using jnf[unfolded jordan_nf_def] ..

lemma m0: "m \<noteq> 0" using mem n_as0 by force

abbreviation cA where "cA \<equiv> map_mat complex_of_real A" 
abbreviation J where "J \<equiv> jordan_matrix n_as" 

lemma sim_A_J: "similar_mat cA J" 
  using jnf[unfolded jordan_nf_def] ..

lemma sumlist_nf: "sum_list (map fst n_as) = n" 
proof -
  have "sum_list (map fst n_as) = dim_row (jordan_matrix n_as)" by simp
  also have "\<dots> = dim_row cA" using similar_matD[OF sim_A_J] by auto
  finally show ?thesis using A by auto
qed

definition p :: "nat \<Rightarrow> real poly" where
  "p s = (\<Prod>i = 0..<s. [: - of_nat i / of_nat (s - i), 1 / of_nat (s - i) :])" 

lemma p_binom: assumes sk: "s \<le> k" 
  shows "of_nat (k choose s) = poly (p s) (of_nat k)" 
  unfolding binomial_altdef_of_nat[OF assms] p_def poly_prod
  by (rule prod.cong[OF refl], insert sk, auto simp: field_simps)

lemma p_binom_complex: assumes sk: "s \<le> k" 
  shows "of_nat (k choose s) = complex_of_real (poly (p s) (of_nat k))" 
  unfolding p_binom[OF sk, symmetric] by simp

lemma deg_p: "degree (p s) = s" unfolding p_def
  by (subst degree_prod_eq_sum_degree, auto)

lemma lead_coeff_p: "lead_coeff (p s) = (\<Prod>i = 0..<s. 1 / (of_nat s - of_nat i))" 
  unfolding p_def lead_coeff_prod
  by (rule prod.cong[OF refl], auto)

lemma lead_coeff_p_gt_0: "lead_coeff (p s) > 0" unfolding lead_coeff_p
  by (rule prod_pos, auto)

definition "c = lead_coeff (p (m - 1))" 

lemma c_gt_0: "c > 0" unfolding c_def by (rule lead_coeff_p_gt_0)
lemma c0: "c \<noteq> 0" using c_gt_0 by auto

definition PP where "PP = (SOME PP. similar_mat_wit cA J (fst PP) (snd PP))" 
definition P where "P = fst PP" 
definition iP where "iP = snd PP" 

lemma JNF: "P \<in> carrier_mat n n" "iP \<in> carrier_mat n n" "J \<in> carrier_mat n n"
  "P * iP = 1\<^sub>m n" "iP * P = 1\<^sub>m n" "cA = P * J * iP" 
proof (atomize (full), goal_cases)
  case 1
  have n: "n = dim_row cA" using A by auto
  from sim_A_J[unfolded similar_mat_def] obtain Q iQ
    where "similar_mat_wit cA J Q iQ" by auto
  hence "similar_mat_wit cA J (fst (Q,iQ)) (snd (Q,iQ))" by auto
  hence "similar_mat_wit cA J P iP" unfolding PP_def iP_def P_def
    by (rule someI)
  from similar_mat_witD[OF n this]
  show ?case by auto
qed

definition C :: "nat set" where
  "C = {j | j bj lj nn la. j < n \<and> j_to_jb_index n_as j = (bj, lj) 
    \<and> n_as ! bj = (nn,la) \<and> cmod la = 1 \<and> nn = m \<and> lj = nn - 1}"

lemma C_nonempty: "C \<noteq> {}" 
proof -
  from split_list[OF mem] obtain as bs where n_as: "n_as = as @ (m,lam) # bs" by auto
  let ?i = "sum_list (map fst as) + (m - 1)"
  have "j_to_jb_index n_as ?i = (length as, m - 1)" 
    unfolding n_as by (induct as, insert m0, auto simp: Let_def)
  with lam1 have "?i \<in> C" unfolding C_def unfolding sumlist_nf[symmetric] n_as using m0 by auto
  thus ?thesis by blast
qed

lemma C_n: "C \<subseteq> {..<n}" unfolding C_def by auto

lemma root_unity_cmod_1: assumes la: "la \<in> snd ` set n_as" and 1: "cmod la = 1" 
  shows "\<exists> d. d \<noteq> 0 \<and> la ^ d = 1" 
proof -
  from la obtain k where kla: "(k,la) \<in> set n_as" by force
  from n_as0 kla have k0: "k \<noteq> 0" by force
  from split_list[OF kla] obtain as bs where nas: "n_as = as @ (k,la) # bs" by auto
  have rt: "poly (char_poly cA) la = 0" using k0
    unfolding jordan_nf_char_poly[OF jnf] nas poly_prod_list prod_list_zero_iff by auto
  obtain ks f where decomp: "decompose_prod_root_unity (char_poly A) = (ks, f)" by force
  from sumlist_nf[unfolded nas] k0 have n0: "n \<noteq> 0" by auto
  note pf = perron_frobenius_for_complexity_jnf(1,7)[OF A n0 nonneg sr1 decomp, simplified]
  from pf(1) pf(2)[OF 1 rt] show "\<exists> d. d \<noteq> 0 \<and> la ^ d = 1" by metis 
qed

definition d where "d = (SOME d. \<forall> la. la \<in> snd ` set n_as \<longrightarrow> cmod la = 1 \<longrightarrow> 
  d la \<noteq> 0 \<and> la ^ (d la) = 1)" 

lemma d: assumes "(k,la) \<in> set n_as" "cmod la = 1" 
  shows "la ^ (d la) = 1 \<and> d la \<noteq> 0" 
proof -
  let ?P = "\<lambda> d. \<forall> la. la \<in> snd ` set n_as \<longrightarrow> cmod la = 1 \<longrightarrow> 
    d la \<noteq> 0 \<and> la ^ (d la) = 1" 
  from root_unity_cmod_1 have "\<forall> la. \<exists> d. la \<in> snd ` set n_as \<longrightarrow> cmod la = 1 \<longrightarrow> 
    d \<noteq> 0 \<and> la ^ d = 1" by blast
  from choice[OF this] have "\<exists> d. ?P d" .
  from someI_ex[OF this] have "?P d" unfolding d_def .
  from this[rule_format, of la, OF _ assms(2)] assms(1) show ?thesis by force
qed

definition D where "D = prod_list (map (\<lambda> na. if cmod (snd na) = 1 then d (snd na) else 1) n_as)" 

lemma D0: "D \<noteq> 0" unfolding D_def
  by (unfold prod_list_zero_iff, insert d, force)

definition f where "f off k = D * k + (m-1) + off"

lemma mono_f: "strict_mono (f off)" unfolding strict_mono_def f_def
  using D0 by auto

definition inv_op where "inv_op off k = inverse (c * real (f off k) ^ (m - 1))"

lemma limit_jordan_block: assumes kla: "(k, la) \<in> set n_as"
  and ij: "i < k" "j < k" 
shows "(\<lambda>N. (jordan_block k la ^\<^sub>m (f off N)) $$ (i, j) * inv_op off N)
  \<longlonglongrightarrow> (if i = 0 \<and> j = k - 1 \<and> cmod la = 1 \<and> k = m then la^off else 0)" 
proof -
  let ?c = "of_nat :: nat \<Rightarrow> complex" 
  let ?r = "of_nat :: nat \<Rightarrow> real" 
  let ?cr = complex_of_real 
  from ij have k0: "k \<noteq> 0" by auto
  from jordan_nf_char_poly[OF jnf] have cA: "char_poly cA = (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" .
  from degree_monic_char_poly[OF A] have "degree (char_poly A) = n" by auto
  have deg: "degree (char_poly cA) = n" using A by (simp add: degree_monic_char_poly)
  from this[unfolded cA] have "n = degree (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" by auto
  also have "\<dots> =  sum_list (map degree (map (\<lambda>(n, a). [:- a, 1:] ^ n) n_as))"
    by (subst degree_prod_list_eq, auto)
  also have "\<dots> = sum_list (map fst n_as)" 
    by (rule arg_cong[of _ _ sum_list], auto simp: degree_linear_power)
  finally have sum: "sum_list (map fst n_as) = n" by auto
  with split_list[OF kla] k0 have n0: "n \<noteq> 0" by auto
  obtain ks small where decomp: "decompose_prod_root_unity (char_poly A) = (ks, small)" by force
  note pf = perron_frobenius_for_complexity_jnf[OF A n0 nonneg sr1 decomp]
  define ji where "ji = j - i" 
  have ji: "j - i = ji" unfolding ji_def by auto
  let ?f = "\<lambda> N. c * (?r N)^(m-1)" 
  let ?jb = "\<lambda> N. (jordan_block k la ^\<^sub>m N) $$ (i,j)" 
  let ?jbc = "\<lambda> N. (jordan_block k la ^\<^sub>m N) $$ (i,j) / ?f N" 
  define e where "e = (if i = 0 \<and> j = k - 1 \<and> cmod la = 1 \<and> k = m then la^off else 0)"  
  let ?e1 = "\<lambda> N :: nat. ?cr (poly (p (j - i)) (?r N)) * la ^ (N + i - j)" 
  let ?e2 = "\<lambda> N. ?cr (poly (p ji) (?r N) / ?f N) * la ^ (N + i - j)" 
  define e2 where "e2 = ?e2" 
  let ?e3 = "\<lambda> N. poly (p ji) (?r N) / (c * ?r N ^ (m - 1)) * cmod la ^ (N + i - j)" 
  define e3 where "e3 = ?e3" 
  define e3' where "e3' = (\<lambda> N. (lead_coeff (p ji) * (?r N) ^ ji) / (c * ?r N ^ (m - 1)) * cmod la ^ (N + i - j))" 
  {
    assume ij': "i \<le> j" and la0: "la \<noteq> 0" 
    {
      fix N
      assume "N \<ge> k" 
      with ij ij' have ji: "j - i \<le> N" and id: "N + i - j = N - ji" unfolding ji_def by auto
      have "?jb N = (?c (N choose (j - i)) * la ^ (N + i - j))" 
        unfolding jordan_block_pow using ij ij' by auto
      also have "\<dots> = ?e1 N" by (subst p_binom_complex[OF ji], auto)
      finally have id: "?jb N = ?e1 N" .
      have "?jbc N = e2 N" 
        unfolding id e2_def ji_def using c_gt_0 by (simp add: norm_mult norm_divide norm_power) 
    } note jbc = this
    have cmod_e2_e3: "(\<lambda> n. cmod (e2 n)) \<sim>[at_top] e3" 
    proof (intro asymp_equivI LIMSEQ_I exI[of _ ji] allI impI)
      fix n r
      assume n: "n \<ge> ji" 
      have "cmod (e2 n) = \<bar>poly (p ji) (?r n) / (c * ?r n ^ (m - 1))\<bar> * cmod la ^ (n + i - j)"
        unfolding e2_def norm_mult norm_power norm_of_real by simp
      also have "\<bar>poly (p ji) (?r n) / (c * ?r n ^ (m - 1))\<bar> = poly (p ji) (?r n) / (c * real n ^ (m - 1))" 
        by (intro abs_of_nonneg divide_nonneg_nonneg mult_nonneg_nonneg, insert c_gt_0, auto simp: p_binom[OF n, symmetric])
      finally have "cmod (e2 n) = e3 n" unfolding e3_def by auto
      thus "r > 0 \<Longrightarrow> norm ((if cmod (e2 n) = 0 \<and> e3 n = 0 then 1 else cmod (e2 n) / e3 n) - 1) < r" by simp
    qed
    have e3': "e3 \<sim>[at_top] e3'" unfolding e3_def e3'_def
      by (intro asymp_equiv_intros, insert poly_asymp_equiv[of "p ji"], unfold deg_p)    
    {
      assume "e3' \<longlonglongrightarrow> 0" 
      hence e3: "e3 \<longlonglongrightarrow> 0" using e3' by (meson tendsto_asymp_equiv_cong)
      have "e2 \<longlonglongrightarrow> 0" 
        by (subst tendsto_norm_zero_iff[symmetric], subst tendsto_asymp_equiv_cong[OF cmod_e2_e3], rule e3) 
    } note e2_via_e3 = this

    have "(e2 o f off) \<longlonglongrightarrow> e" 
    proof (cases "cmod la = 1 \<and> k = m \<and> i = 0 \<and> j = k - 1")
      case False
      then consider (0) "la = 0" | (small) "la \<noteq> 0" "cmod la < 1" | 
        (medium) "cmod la = 1" "k < m \<or> i \<noteq> 0 \<or> j \<noteq> k - 1" 
        using max_block[OF kla] by linarith
      hence main: "e2 \<longlonglongrightarrow> e" 
      proof cases
        case 0
        hence e0: "e = 0" unfolding e_def by auto
        show ?thesis unfolding e0 0 LIMSEQ_iff e2_def ji
        proof (intro exI[of _ "Suc j"] impI allI, goal_cases)
          case (1 r n) thus ?case by (cases "n + i - j", auto)
        qed
      next
        case small
        define d where "d = cmod la" 
        from small have d: "0 < d" "d < 1" unfolding d_def by auto
        have e0: "e = 0" using small unfolding e_def by auto
        show ?thesis unfolding e0
          by (intro e2_via_e3, unfold e3'_def d_def[symmetric], insert d c0, real_asymp)
      next
        case medium
        with max_block[OF kla] have "k \<le> m" by auto
        with ij medium have ji: "ji < m - 1" unfolding ji_def by linarith
        have e0: "e = 0" using medium unfolding e_def by auto
        show ?thesis unfolding e0
          by (intro e2_via_e3, unfold e3'_def medium power_one mult_1_right, insert ji c0, real_asymp)
      qed
      show "(e2 o f off) \<longlonglongrightarrow> e"
        by (rule LIMSEQ_subseq_LIMSEQ[OF main mono_f])
    next
      case True
      hence large: "cmod la = 1" "k = m" "i = 0" "j = k - 1" by auto
      hence e: "e = la^off" and ji: "ji = m - 1" unfolding e_def ji_def by auto
      from large k0 have m0: "m \<ge> 1" by auto
      define m1 where "m1 = m - 1" 
      have id: "(real (m - 1) - real ia) = ?r m - 1 - ?r ia" for ia using m0 unfolding m1_def by auto
      define q where "q = p m1 - monom c m1" 
      hence pji: "p ji = q + monom c m1" unfolding q_def ji m1_def by simp
      let ?e4a = "\<lambda> x. (complex_of_real (poly q (real x) / (c * real x ^ m1))) * la ^ (x + i - j)" 
      let ?e4b = "\<lambda> x. la ^ (x + i - j)" 
      {
        fix x :: nat
        assume x: "x \<noteq> 0" 
        have "e2 x = ?e4a x + ?e4b x" 
          unfolding e2_def pji poly_add poly_monom m1_def[symmetric] using c0 x by (simp add: field_simps)
      } note e2_e4 = this
      have e2_e4: "\<forall>\<^sub>F x in sequentially. (e2 o f off) x = (?e4a o f off) x + (?e4b o f off) x"  unfolding o_def
        by (intro eventually_sequentiallyI[of "Suc 0"], rule e2_e4, insert D0, auto simp: f_def)
      have "(e2 o f off) \<longlonglongrightarrow> 0 + e" 
        unfolding tendsto_cong[OF e2_e4]
      proof (rule tendsto_add, rule LIMSEQ_subseq_LIMSEQ[OF _ mono_f])
        show "?e4a \<longlonglongrightarrow> 0" 
        proof (subst tendsto_norm_zero_iff[symmetric],
            unfold norm_mult norm_power large power_one mult_1_right norm_divide norm_of_real
            tendsto_rabs_zero_iff)
          have deg_q: "degree q \<le> m1" unfolding q_def using deg_p[of m1] 
            by (intro degree_diff_le degree_monom_le, auto)
          have coeff_q_m1: "coeff q m1 = 0" unfolding q_def c_def m1_def[symmetric] using deg_p[of m1] by simp
          from deg_q coeff_q_m1 have deg: "degree q < m1 \<or> q = 0" by fastforce
          have eq: "(\<lambda>n. poly q (real n) / (c * real n ^ m1)) \<sim>[at_top] 
                    (\<lambda>n. lead_coeff q * real n ^ degree q / (c * real n ^ m1))"
            by (intro asymp_equiv_intros poly_asymp_equiv)
          show "(\<lambda>n. poly q (?r n) / (c * ?r n ^ m1)) \<longlonglongrightarrow> 0" 
            unfolding tendsto_asymp_equiv_cong[OF eq] using deg
            by (standard, insert c0, real_asymp, simp)
        qed
      next  
        have id: "D * x + (m - 1) + off + i - j = D * x + off" for x
          unfolding ji[symmetric] ji_def using ij' by auto
        from d[OF kla large(1)] have 1: "la ^ d la = 1" by auto
        from split_list[OF kla] obtain as bs where n_as: "n_as = as @ (k,la) # bs" by auto
        obtain C where D: "D = d la * C" unfolding D_def unfolding n_as using large by auto
        show "(?e4b o f off) \<longlonglongrightarrow> e" 
          unfolding e f_def o_def id
          unfolding power_add power_mult D 1 by auto
      qed
      thus ?thesis by simp
    qed
    also have "((e2 o f off) \<longlonglongrightarrow> e) = ((?jbc o f off)  \<longlonglongrightarrow> e)"
    proof (rule tendsto_cong, unfold eventually_at_top_linorder, rule exI[of _ k], 
        intro allI impI, goal_cases)
      case (1 n)
      from mono_f[of off] 1 have "f off n \<ge> k" using le_trans seq_suble by blast
      from jbc[OF this] show ?case by (simp add: o_def)
    qed
    finally have "(?jbc o f off) \<longlonglongrightarrow> e" .
  } note part1 = this  
  {
    assume "i > j \<or> la = 0" 
    hence e: "e = 0" and jbn: "N \<ge> k \<Longrightarrow> ?jbc N = 0" for N 
      unfolding jordan_block_pow e_def using ij by auto
    have "?jbc \<longlonglongrightarrow> e" unfolding e LIMSEQ_iff by (intro exI[of _ k] allI impI, subst jbn, auto)
    from LIMSEQ_subseq_LIMSEQ[OF this mono_f]
    have "(?jbc o f off) \<longlonglongrightarrow> e" .
  } note part2 = this
  from part1 part2 have "(?jbc o f off) \<longlonglongrightarrow> e" by linarith
  thus ?thesis unfolding e_def o_def inv_op_def by (simp add: field_simps)
qed

definition lambda where "lambda i = snd (n_as ! fst (j_to_jb_index n_as i))" 

lemma cmod_lambda: "i \<in> C \<Longrightarrow> cmod (lambda i) = 1" 
  unfolding C_def lambda_def by auto  

lemma R_lambda: assumes i: "i \<in> C" 
  shows "(m, lambda i) \<in> set n_as" 
proof -
  from i[unfolded C_def]
  obtain bi li la where i: "i < n" and jb: "j_to_jb_index n_as i = (bi, li)" 
    and nth: "n_as ! bi = (m, la)" and "cmod la = 1 \<and> li = m - 1" by auto
  hence lam: "lambda i = la" unfolding lambda_def by auto  
  from j_to_jb_index[of _ n_as, unfolded sumlist_nf, OF i i jb jb nth] lam
  show ?thesis by auto
qed

lemma limit_jordan_matrix: assumes ij: "i < n" "j < n" 
shows "(\<lambda>N. (J ^\<^sub>m (f off N)) $$ (i, j) * inv_op off N)
  \<longlonglongrightarrow> (if j \<in> C \<and> i = j - (m - 1) then (lambda j)^off else 0)" 
proof -
  obtain bi li where bi: "j_to_jb_index n_as i = (bi, li)" by force
  obtain bj lj where bj: "j_to_jb_index n_as j = (bj, lj)" by force
  define la where "la = snd (n_as ! fst (j_to_jb_index n_as j))" 
  obtain nn where nbj: "n_as ! bj = (nn,la)" unfolding la_def bj fst_conv by (metis prod.collapse)
  from j_to_jb_index[OF ij[folded sumlist_nf] bi bj nbj]
  have eq: "bi = bj \<Longrightarrow> li < nn \<and> lj < nn \<and> bj < length n_as \<and> (nn, la) \<in> set n_as" and 
    index: "(J ^\<^sub>m r) $$ (i, j) =
    (if bi = bj then (jordan_block nn la ^\<^sub>m r) $$ (li, lj) else 0)" for r
    by auto
  note index_rev = j_to_jb_index_rev[OF bj, unfolded sumlist_nf, OF ij(2) le_refl]
  show ?thesis
  proof (cases "bi = bj")
    case False
    hence id: "(bi = bj) = False" by auto
    {
      assume "j \<in> C" "i = j - (m - 1)" 
      from this[unfolded C_def] bj nbj have "i = j - lj" by auto
      from index_rev[folded this] bi False have False by auto
    }
    thus ?thesis unfolding index id if_False by auto
  next
    case True
    hence id: "(bi = bj) = True" by auto
    from eq[OF True] have eq: "li < nn" "lj < nn" "(nn,la) \<in> set n_as" "bj < length n_as" by auto
    have "(\<lambda>N. (J ^\<^sub>m (f off N)) $$ (i, j) * inv_op off N)
      \<longlonglongrightarrow> (if li = 0 \<and> lj = nn - 1 \<and> cmod la = 1 \<and> nn = m then la^off else 0)" 
      unfolding index id if_True using limit_jordan_block[OF eq(3,1,2)] .
    also have "(li = 0 \<and> lj = nn - 1 \<and> cmod la = 1 \<and> nn = m) = (j \<in> C \<and> i = j - (m - 1))" (is "?l = ?r")
    proof
      assume ?r
      hence "j \<in> C" ..
      from this[unfolded C_def] bj nbj 
      have *: "nn = m" "cmod la = 1" "lj = nn - 1" by auto
      from \<open>?r\<close> * have "i = j - lj" by auto
      with * have "li = 0" using index_rev bi by auto
      with * show ?l by auto
    next
      assume ?l
      hence jI: "j \<in> C" using bj nbj ij by (auto simp: C_def)
      from \<open>?l\<close> have "li = 0" by auto
      with index_rev[of i] bi ij(1) \<open>?l\<close> True
      have "i = j - (m - 1)" by auto
      with jI show ?r by auto
    qed
    finally show ?thesis unfolding la_def lambda_def .
  qed
qed

declare sumlist_nf[simp]

lemma A_power_P: "cA ^\<^sub>m k * P = P * J ^\<^sub>m k" 
proof (induct k)
  case 0
  show ?case using A JNF by simp
next
  case (Suc k) 
  have "cA ^\<^sub>m Suc k * P = cA ^\<^sub>m k * cA * P" by simp
  also have "\<dots> = cA ^\<^sub>m k * (P * J * iP) * P" using JNF by simp
  also have "\<dots> = (cA ^\<^sub>m k * P) * (J * (iP * P))" 
    using A JNF(1-3) by (simp add: assoc_mult_mat[of _ n n _ n _ n])
  also have "J * (iP * P) = J" unfolding JNF using JNF by auto
  finally show ?case unfolding Suc 
    using A JNF(1-3) by (simp add: assoc_mult_mat[of _ n n _ n _ n])
qed

lemma inv_op_nonneg: "inv_op off k \<ge> 0" unfolding inv_op_def using c_gt_0 by auto

lemma P_nonzero_entry: assumes j: "j < n"
  shows "\<exists> i < n. P $$ (i,j) \<noteq> 0" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  hence 0: "\<And> i. i < n \<Longrightarrow> P $$ (i,j) = 0" by auto
  have "1 = (iP * P) $$ (j,j)" using j unfolding JNF by auto
  also have "\<dots> = (\<Sum>i = 0..<n. iP $$ (j, i) * P $$ (i, j))" 
    using j JNF(1-2) by (auto simp: scalar_prod_def)
  also have "\<dots> = 0" by (rule sum.neutral, insert 0, auto)
  finally show False by auto
qed

definition j where "j = (SOME j. j \<in> C)" 

lemma j: "j \<in> C" unfolding j_def using C_nonempty some_in_eq by blast

lemma j_n: "j < n" using j unfolding C_def by auto 

definition "i = (SOME i. i < n \<and> P $$ (i, j - (m - 1)) \<noteq> 0)" 

lemma i: "i < n" and P_ij0: "P $$ (i, j - (m - 1)) \<noteq> 0"
proof -
  from j_n have lt: "j - (m - 1) < n" by auto
  show "i < n" "P $$ (i, j - (m - 1)) \<noteq> 0"
    unfolding i_def using someI_ex[OF P_nonzero_entry[OF lt]] by auto
qed

definition "w = P *\<^sub>v unit_vec n j" 

lemma w: "w \<in> carrier_vec n" using JNF unfolding w_def by auto

definition "v = map_vec cmod w"

lemma v: "v \<in> carrier_vec n" unfolding v_def using w by auto

definition u where "u = iP *\<^sub>v map_vec of_real v" 

lemma u: "u \<in> carrier_vec n" unfolding u_def using JNF(2) v by auto

definition a where "a j = P $$ (i, j - (m - 1)) * u $v j" for j

lemma main_step: "0 < Re (\<Sum>j\<in>C. a j * lambda j ^ l)" 
proof -
  let ?c = "complex_of_real" 
  let ?cv = "map_vec ?c" 
  let ?cm = "map_mat ?c" 
  let ?v = "?cv v" 
  define cc where 
    "cc = (\<lambda> jj. ((\<Sum>k = 0..<n. (if k = jj - (m - 1) then P $$ (i, k) else 0)) * u $v jj))" 
  {
    fix off
    define G where "G = (\<lambda> k. (A ^\<^sub>m f off k *\<^sub>v v) $v i * inv_op off k)" 
    define F where "F = (\<Sum>j\<in>C. a j * lambda j ^ off)" 
    {
      fix kk
      define k where "k = f off kk" 
      have "((A ^\<^sub>m k) *\<^sub>v v) $ i * inv_op off kk = Re (?c (((A ^\<^sub>m k) *\<^sub>v v) $ i * inv_op off kk))" by simp
      also have "?c (((A ^\<^sub>m k) *\<^sub>v v) $ i * inv_op off kk) = ?cv ((A ^\<^sub>m k) *\<^sub>v v) $ i * ?c (inv_op off kk)" 
        using i A by simp
      also have "?cv ((A ^\<^sub>m k) *\<^sub>v v) = (?cm (A ^\<^sub>m k) *\<^sub>v ?v)" using A
        by (subst of_real_hom.mult_mat_vec_hom[OF _ v], auto)
      also have "\<dots> = (cA ^\<^sub>m k *\<^sub>v ?v)" 
        by (simp add: of_real_hom.mat_hom_pow[OF A])
      also have "\<dots> = (cA ^\<^sub>m k *\<^sub>v ((P * iP) *\<^sub>v ?v))" unfolding JNF using v by auto
      also have "\<dots> = (cA ^\<^sub>m k *\<^sub>v (P *\<^sub>v u))" unfolding u_def
        by (subst assoc_mult_mat_vec, insert JNF v, auto)
      also have "\<dots> = (P * J ^\<^sub>m k *\<^sub>v u)" unfolding A_power_P[symmetric]
        by (subst assoc_mult_mat_vec, insert u JNF(1) A, auto)
      also have "\<dots> = (P *\<^sub>v (J ^\<^sub>m k *\<^sub>v u))"
        by (rule assoc_mult_mat_vec, insert u JNF(1) A, auto)
      finally have "(A ^\<^sub>m k *\<^sub>v v) $v i * inv_op off kk = Re ((P *\<^sub>v (J ^\<^sub>m k *\<^sub>v u)) $ i * inv_op off kk)" by simp
      also have "\<dots> = Re (\<Sum>jj = 0..<n.
           P $$ (i, jj) * (\<Sum>ia = 0..< n. (J ^\<^sub>m k) $$ (jj, ia) * u $v ia * inv_op off kk))"
        by (subst index_mult_mat_vec, insert JNF(1) i u, auto simp: scalar_prod_def sum_distrib_right[symmetric]
           mult.assoc[symmetric])  
      finally have "(A ^\<^sub>m k *\<^sub>v v) $v i * inv_op off kk =
        Re (\<Sum>jj = 0..<n. P $$ (i, jj) * (\<Sum>ia = 0..<n. (J ^\<^sub>m k) $$ (jj, ia) * inv_op off kk * u $v ia))" 
        unfolding k_def
        by (simp only: ac_simps)
    } note A_to_u = this
    have "G \<longlonglongrightarrow> 
       Re (\<Sum>jj = 0..<n. P $$ (i, jj) *
           (\<Sum>ia = 0..<n. (if ia \<in> C \<and> jj = ia - (m - 1) then (lambda ia)^off else 0) * u $v ia))" 
      unfolding A_to_u G_def
      by (intro tendsto_intros limit_jordan_matrix, auto)
    also have "(\<Sum>jj = 0..<n. P $$ (i, jj) *
           (\<Sum>ia = 0..<n. (if ia \<in> C \<and> jj = ia - (m - 1) then (lambda ia)^off else 0) * u $v ia))
      = (\<Sum>jj = 0..<n. (\<Sum>ia \<in> C. (if ia \<in> C \<and> jj = ia - (m - 1) then P $$ (i, jj) else 0) * ((lambda ia)^off * u $v ia)))" 
      by (rule sum.cong[OF refl], unfold sum_distrib_left, subst (2) sum.mono_neutral_left[of "{0..<n}"],
        insert C_n, auto intro!: sum.cong)
    also have "\<dots> = (\<Sum>ia \<in> C. (\<Sum>jj = 0..<n. (if jj = ia - (m - 1) then P $$ (i, jj) else 0)) * ((lambda ia)^off * u $v ia))"
      unfolding sum.swap[of _ C] sum_distrib_right
      by (rule sum.cong[OF refl], auto)
    also have "\<dots> = (\<Sum>ia \<in> C. cc ia * (lambda ia)^off)" unfolding cc_def
      by (rule sum.cong[OF refl], simp)
    also have "\<dots> = F" unfolding cc_def a_def F_def
      by (rule sum.cong[OF refl], insert C_n, auto)
    finally have tend3: "G \<longlonglongrightarrow> Re F" . 
    (* so far we did not use the definition of i or v, except that v is a real vector.
       Hence, the result holds independently of i and v (if one would drop the Re) *)

    from j j_n have jR: "j \<in> C" and j: "j < n" by auto
    let ?exp = "\<lambda> k. sum (\<lambda> ii. P $$ (i, ii) * (J ^\<^sub>m k) $$ (ii,j)) {..<n}" 
    define M where "M = (\<lambda> k. cmod (?exp (f off k) * inv_op off k))" 
    {
      fix kk
      define k where "k = f off kk" 
      define cAk where "cAk = cA ^\<^sub>m k" 
      have cAk: "cAk \<in> carrier_mat n n" unfolding cAk_def using A by auto
      have "((A ^\<^sub>m k) *\<^sub>v v) $ i = ((map_mat cmod cAk) *\<^sub>v map_vec cmod w) $ i" 
        unfolding v_def[symmetric] cAk_def
        by (rule arg_cong[of _ _ "\<lambda> x. (x *\<^sub>v v) $ i"],
          unfold of_real_hom.mat_hom_pow[OF A, symmetric],
        insert nonneg_mat_power[OF A nonneg, of k], insert i j, 
        auto simp: nonneg_mat_def elements_mat_def)
      also have "\<dots> \<ge> cmod ((cAk *\<^sub>v w) $ i)" 
        by (subst (1 2) index_mult_mat_vec, insert i cAk w, auto simp: scalar_prod_def
        intro!: sum_norm_le norm_mult_ineq) 
      also have "cAk *\<^sub>v w = (cAk * P) *\<^sub>v unit_vec n j" 
        unfolding w_def using JNF cAk by simp
      also have "\<dots> = P *\<^sub>v (J ^\<^sub>m k *\<^sub>v unit_vec n j)" unfolding cAk_def A_power_P
        using JNF by (subst assoc_mult_mat_vec[of _ n n _ n], auto)
      also have "J ^\<^sub>m k *\<^sub>v unit_vec n j = col (J ^\<^sub>m k) j"
        by (rule eq_vecI, insert j, auto)
      also have "(P *\<^sub>v (col (J ^\<^sub>m k) j)) $ i = Matrix.row P i \<bullet> col (J ^\<^sub>m k) j" 
        by (subst index_mult_mat_vec, insert i JNF, auto)
      also have "\<dots> = sum (\<lambda> ii. P $$ (i, ii) * (J ^\<^sub>m k) $$ (ii,j)) {..<n}" 
        unfolding scalar_prod_def by (rule sum.cong, insert i j JNF(1), auto)    
      finally have "(A ^\<^sub>m k *\<^sub>v v) $v i \<ge> cmod (?exp k)" .
      from mult_right_mono[OF this inv_op_nonneg]
      have "(A ^\<^sub>m k *\<^sub>v v) $v i * inv_op off kk \<ge> cmod (?exp k * inv_op off kk)" unfolding norm_mult
        using inv_op_nonneg by auto      
    }
    hence ge: "(A ^\<^sub>m f off k *\<^sub>v v) $v i * inv_op off k \<ge> M k" for k unfolding M_def by auto 
    from j have mem: "j - (m - 1) \<in> {..<n}" by auto
    have "(\<lambda> k. ?exp (f off k) * inv_op off k) \<longlonglongrightarrow> 
      (\<Sum>ii<n. P $$ (i, ii) * (if j \<in> C \<and> ii = j - (m - 1) then lambda j ^ off else 0))"
      (is "_ \<longlonglongrightarrow> ?sum")
      unfolding sum_distrib_right mult.assoc 
      by (rule tendsto_sum, rule tendsto_mult, force, rule limit_jordan_matrix[OF _ j], auto)
    also have "?sum = P $$ (i, j - (m - 1)) * lambda j ^ off" 
      by (subst sum.remove[OF _ mem], force, subst sum.neutral, insert jR, auto)
    finally have tend1: "(\<lambda> k. ?exp (f off k) * inv_op off k) \<longlonglongrightarrow> P $$ (i, j - (m - 1)) * lambda j ^ off" .
    have tend2: "M \<longlonglongrightarrow> cmod (P $$ (i, j - (m - 1)) * lambda j ^ off)" unfolding M_def
      by (rule tendsto_norm, rule tend1)
    define B where "B = cmod (P $$ (i, j - (m - 1))) / 2"
    have B: "0 < B" unfolding B_def using P_ij0 by auto
    {
      from P_ij0 have 0: "P $$ (i, j - (m - 1)) \<noteq> 0" by auto
      define E where "E = cmod (P $$ (i, j - (m - 1)) * lambda j ^ off)" 
      from cmod_lambda[OF jR] 0 have E: "E / 2 > 0" unfolding E_def by auto
      from tend2[folded E_def] have tend2: "M \<longlonglongrightarrow> E" .
      from ge have ge: "G k \<ge> M k" for k unfolding G_def .
      from tend2[unfolded LIMSEQ_iff, rule_format, OF E]
      obtain k' where diff: "\<And> k. k \<ge> k' \<Longrightarrow> norm (M k - E) < E / 2" by auto
      {
        fix k
        assume "k \<ge> k'"
        from diff[OF this] have norm: "norm (M k - E) < E / 2" .
        have "M k \<ge> 0" unfolding M_def by auto
        with E norm have "M k \<ge> E / 2"
          by (smt real_norm_def field_sum_of_halves)
        with ge[of k] E have "G k \<ge> E / 2" by auto
        also have "E / 2 = B" unfolding E_def B_def j norm_mult norm_power 
          cmod_lambda[OF jR] by auto
        finally have "G k \<ge> B" .
      }
      hence "\<exists> k'. \<forall> k. k \<ge> k' \<longrightarrow> G k \<ge> B" by auto
    }    
    hence Bound: "\<exists>k'. \<forall>k\<ge>k'. B \<le> G k" by auto
    from tend3[unfolded LIMSEQ_iff, rule_format, of "B / 2"] B
    obtain kk where kk: "\<And> k. k \<ge> kk \<Longrightarrow> norm (G k - Re F) < B / 2" by auto
    from Bound obtain kk' where kk': "\<And> k. k \<ge> kk' \<Longrightarrow> B \<le> G k" by auto
    define k where "k = max kk kk'" 
    with kk kk' have 1: "norm (G k - Re F) < B / 2" "B \<le> G k" by auto
    with B have "Re F > 0" by (smt real_norm_def field_sum_of_halves)
  }
  thus ?thesis by blast
qed


lemma main_theorem: "(m, 1) \<in> set n_as"
proof -
  from main_step have pos: "0 < Re (\<Sum>i\<in>C. a i * lambda i ^ l)" for l by auto 
  have "1 \<in> lambda ` C" 
  proof (rule sum_root_unity_power_pos_implies_1[of a lambda C, OF pos])
    fix i
    assume "i \<in> C" 
    from d[OF R_lambda[OF this] cmod_lambda[OF this]]
    show "\<exists>d. d \<noteq> 0 \<and> lambda i ^ d = 1" by auto
  qed
  then obtain i where i: "i \<in> C" and "lambda i = 1" by auto
  with R_lambda[OF i] show ?thesis by auto
qed
end

lemma nonneg_sr_1_largest_jb:
  assumes nonneg: "nonneg_mat A" 
  and jnf: "jordan_nf (map_mat complex_of_real A) n_as" 
  and mem: "(m, lam) \<in> set n_as" 
  and lam1: "cmod lam = 1"
  and sr1: "\<And>x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  shows "\<exists> M. M \<ge> m \<and> (M,1) \<in> set n_as" 
proof -
  note jnf' = jnf[unfolded jordan_nf_def]
  from jnf' similar_matD[OF jnf'[THEN conjunct2]] obtain n 
    where A: "A \<in> carrier_mat n n" and n_as0: "0 \<notin> fst ` set n_as" by auto
  let ?M = "{ m. \<exists> lam. (m,lam) \<in> set n_as \<and> cmod lam = 1}" 
  have m: "m \<in> ?M" using mem lam1 by auto
  have fin: "finite ?M" 
    by (rule finite_subset[OF _ finite_set[of "map fst n_as"]], force)
  define M where "M = Max ?M"
  have "M \<in> ?M" using fin m unfolding M_def using Max_in by blast
  then obtain lambda where M: "(M,lambda) \<in> set n_as" "cmod lambda = 1" by auto
  from m fin have mM: "m \<le> M" unfolding M_def by simp
  interpret spectral_radius_1_jnf_max A n M lambda 
  proof (unfold_locales, rule A, rule nonneg, rule jnf, rule M, rule M, rule sr1)
    fix k la
    assume kla: "(k, la) \<in> set n_as" 
    with fin have 1: "cmod la = 1 \<longrightarrow> k \<le> M" unfolding M_def using Max_ge by blast
    obtain ks f where decomp: "decompose_prod_root_unity (char_poly A) = (ks, f)" by force
    from n_as0 kla have k0: "k \<noteq> 0" by force
    let ?cA = "map_mat complex_of_real A" 
    from split_list[OF kla] obtain as bs where nas: "n_as = as @ (k,la) # bs" by auto
    have rt: "poly (char_poly ?cA) la = 0" using k0
      unfolding jordan_nf_char_poly[OF jnf] nas poly_prod_list prod_list_zero_iff by auto
    have sumlist_nf: "sum_list (map fst n_as) = n" 
    proof -
      have "sum_list (map fst n_as) = dim_row (jordan_matrix n_as)" by simp
      also have "\<dots> = dim_row ?cA" using similar_matD[OF jnf'[THEN conjunct2]] by auto
      finally show ?thesis using A by auto
    qed
    from this[unfolded nas] k0 have n0: "n \<noteq> 0" by auto
    from perron_frobenius_for_complexity_jnf(4)[OF A n0 nonneg sr1 decomp rt]
    have "cmod la \<le> 1" .
    with 1 show "cmod la \<le> 1 \<and> (cmod la = 1 \<longrightarrow> k \<le> M)" by auto
  qed
  from main_theorem
  show ?thesis using mM by auto
qed
hide_const(open) spectral_radius

lemma (in ring_hom) hom_smult_mat: "mat\<^sub>h (a \<cdot>\<^sub>m A) = hom a \<cdot>\<^sub>m mat\<^sub>h A"
  by (rule eq_matI, auto simp: hom_mult)

lemma root_char_poly_smult: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and k: "k \<noteq> 0" 
shows "(poly (char_poly (k \<cdot>\<^sub>m A)) x = 0) = (poly (char_poly A) (x / k) = 0)" 
  using order_char_poly_smult[OF A k, of x] 
  by (metis A degree_0 degree_monic_char_poly monic_degree_0 order_root smult_carrier_mat)

theorem real_nonneg_mat_spectral_radius_largest_jordan_block: 
  assumes "real_nonneg_mat A" 
  and "jordan_nf A n_as"
  and "(m, lam) \<in> set n_as" 
  and "cmod lam = spectral_radius A" 
shows "\<exists> M \<ge> m. (M, of_real (spectral_radius A)) \<in> set n_as" 
proof -
  from similar_matD[OF assms(2)[unfolded jordan_nf_def, THEN conjunct2]] obtain n where
    A: "A \<in> carrier_mat n n" by auto
  let ?c = complex_of_real
  define B where "B = map_mat Re A" 
  have B: "B \<in> carrier_mat n n" unfolding B_def using A by auto
  have AB: "A = map_mat ?c B" unfolding B_def using assms(1) 
    by (auto simp: real_nonneg_mat_def elements_mat_def)
  have nonneg: "nonneg_mat B" using assms(1) unfolding AB 
    by (auto simp: real_nonneg_mat_def elements_mat_def nonneg_mat_def)
  let ?sr = "spectral_radius A" 
  show ?thesis
  proof (cases "?sr = 0")
    case False
    define isr where "isr = inverse ?sr" 
    let ?nas = "map (\<lambda>(n, a). (n, ?c isr * a)) n_as" 
    from False have isr0: "isr \<noteq> 0" unfolding isr_def by auto
    hence cisr0: "?c isr \<noteq> 0" by auto
    from False assms(4) have isr_pos: "isr > 0" unfolding isr_def
      by (smt norm_ge_zero positive_imp_inverse_positive)    
    define C where "C = isr \<cdot>\<^sub>m B"
    have C: "C \<in> carrier_mat n n" using B unfolding C_def by auto
    have BC: "B = ?sr \<cdot>\<^sub>m C" using isr0 unfolding C_def isr_def by auto
    have nonneg: "nonneg_mat C" unfolding C_def using isr_pos nonneg
      unfolding nonneg_mat_def elements_mat_def by auto
    from jordan_nf_smult[OF assms(2)[unfolded AB] cisr0]
    have jnf: "jordan_nf (map_mat ?c C) ?nas" unfolding C_def by (auto simp: of_real_hom.hom_smult_mat)
    from assms(3) have mem: "(m, ?c isr * lam) \<in> set ?nas" by auto
    have 1: "cmod (?c isr * lam) = 1" using False isr_pos unfolding isr_def norm_mult assms(4)
      by (smt mult.commute norm_of_real right_inverse)        
    {
      fix x
      have B': "map_mat ?c B \<in> carrier_mat n n" using B by auto
      assume "poly (char_poly C) x = 0" 
      hence "poly (char_poly (map_mat ?c C)) (?c x) = 0" unfolding of_real_hom.char_poly_hom[OF C] by auto
      hence "poly (char_poly A) (?c x / ?c isr) = 0" unfolding C_def of_real_hom.hom_smult_mat AB
        unfolding root_char_poly_smult[OF B' cisr0] .
      hence "eigenvalue A (?c x / ?c isr)" unfolding eigenvalue_root_char_poly[OF A] .
      hence mem: "cmod (?c x / ?c isr) \<in> cmod ` spectrum A" unfolding spectrum_def by auto
      from Max_ge[OF finite_imageI this]
      have "cmod (?c x / ?c isr) \<le> ?sr" unfolding Spectral_Radius.spectral_radius_def
        using A card_finite_spectrum(1) by blast
      hence "cmod (?c x) \<le> 1" using isr0 isr_pos unfolding isr_def 
        by (auto simp: field_simps norm_divide norm_mult)
      hence "x \<le> 1" by auto
    } note sr = this 
    from nonneg_sr_1_largest_jb[OF nonneg jnf mem 1 sr] obtain M where
      M: "M \<ge> m" "(M,1) \<in> set ?nas" by blast
    from M(2) obtain a where mem: "(M,a) \<in> set n_as" and "1 = ?c isr * a" by auto
    from this(2) have a: "a = ?c ?sr" using isr0 unfolding isr_def by (auto simp: field_simps)
    show ?thesis
      by (intro exI[of _ M], insert mem a M(1), auto)
  next
    case True
    from jordan_nf_root_char_poly[OF assms(2,3)]
    have "eigenvalue A lam" unfolding eigenvalue_root_char_poly[OF A] .
    hence "cmod lam \<in> cmod ` spectrum A" unfolding spectrum_def by auto
    from Max_ge[OF finite_imageI this]
    have "cmod lam \<le> ?sr" unfolding Spectral_Radius.spectral_radius_def
      using A card_finite_spectrum(1) by blast
    from this[unfolded True] have lam0: "lam = 0" by auto
    show ?thesis unfolding True using assms(3)[unfolded lam0] by auto
  qed
qed
  
end