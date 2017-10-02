subsection \<open>The Perron Frobenius Theorem for Irreducible Matrices\<close>

theory Perron_Frobenius_2
imports
  Perron_Frobenius
  Perron_Frobenius_Aux_2
  Rank_Nullity_Theorem.Miscellaneous (* for scalar-matrix-multiplication, 
    this import is incompatible with field_simps, ac_simps *)
begin 

context includes lifting_syntax
begin
lemma HMA_M_smult[transfer_rule]: "(op = ===> HMA_M ===> HMA_M) (op \<cdot>\<^sub>m) (op *k)" 
  unfolding smult_mat_def 
  unfolding rel_fun_def HMA_M_def from_hma\<^sub>m_def
  by (auto simp: matrix_scalar_mult_def)
end

lemma order_charpoly_smult: fixes A :: "complex ^ 'n ^ 'n" 
  assumes k: "k \<noteq> 0" 
  shows "order x (charpoly (k *k A)) = order (x / k) (charpoly A)" 
  by (transfer fixing: k, rule order_char_poly_smult[OF _ k])

(* use field, since the *k-lemmas have been stated for fields *)
lemma smult_eigen_vector: fixes a :: "'a :: field"  
  assumes "eigen_vector A v x" 
  shows "eigen_vector (a *k A) v (a * x)" 
proof -
  from assms[unfolded eigen_vector_def] have v: "v \<noteq> 0" and id: "A *v v = x *s v" by auto
  from arg_cong[OF id, of "op *s a"] have id: "(a *k A) *v v = (a * x) *s v" 
    unfolding scalar_matrix_vector_assoc by simp
  thus "eigen_vector (a *k A) v (a * x)" using v unfolding eigen_vector_def by auto
qed

lemma smult_eigen_value: fixes a :: "'a :: field"  
  assumes "eigen_value A x" 
  shows "eigen_value (a *k A) (a * x)" 
  using assms smult_eigen_vector[of A _ x a] unfolding eigen_value_def by blast

locale fixed_mat = fixes A :: "'a :: zero ^ 'n ^ 'n"
begin
 
definition G :: "('n,'n \<times> 'n) pre_digraph" where
  "G = 
     \<lparr> pre_digraph.verts = UNIV, arcs = { (i,j). A $ i $ j \<noteq> 0}, tail = snd, head = fst \<rparr>" 

lemma G_simps[simp]: "arcs G = { (i,j). A $ i $ j \<noteq> 0}" "tail G = snd" "head G = fst" 
  unfolding G_def by auto

sublocale fin_digraph G by (unfold_locales, unfold G_def, auto)

definition irreducible :: bool where
  "irreducible = (\<forall> i j. reachable1 G i j)" 
end

lemma arcs_ends_transpose: 
  "arcs_ends (fixed_mat.G (transpose A)) = (arcs_ends (fixed_mat.G A))^-1"
  unfolding fixed_mat.G_def arcs_ends_def arc_to_ends_def
  by (force simp: transpose_def)

lemma reachable1_transpose: 
  "reachable1 (fixed_mat.G (transpose A)) i j = reachable1 (fixed_mat.G A) j i"
  unfolding arcs_ends_transpose trancl_converse by auto 

locale nonneg_mat = fixed_mat A for 
  A :: "'a :: linordered_idom ^ 'n ^ 'n" + 
  assumes nonneg: "A $ i $ j \<ge> 0" 
begin 
lemma nonneg_matpow: "matpow A n $ i $ j \<ge> 0" 
  by (induct n arbitrary: i j, insert nonneg, 
    auto intro!: sum_nonneg simp: matrix_matrix_mult_def mat_def)

lemma awalk_pos_matpow_exact: "awalk i xs j \<Longrightarrow> matpow A (length xs) $ j $ i > 0" 
proof (induct xs arbitrary: i)
  case (Nil i)
  thus ?case by (auto simp: mat_def)
next
  case (Cons arc xs i)
  from Cons(2)[unfolded awalk_Cons_iff] obtain k where
    ik: "A $ k $ i \<noteq> 0" and xs: "awalk k xs j" by (cases arc, auto)
  from ik nonneg[of k i] have ik: "A $ k $ i > 0" by auto
  from Cons(1)[OF xs] have IH: "matpow A (length xs) $h j $h k > 0" .
  thus ?case using ik by (auto simp: nonneg_matpow nonneg matrix_matrix_mult_def 
    intro!: sum_pos2[of _ k] mult_nonneg_nonneg)
qed

lemma matpow_mono: assumes B: "\<And> i j. B $ i $ j \<ge> A $ i $ j"
  shows "matpow B n $ i $ j \<ge> matpow A n $ i $ j" 
proof (induct n arbitrary: i j)
  case (Suc n i j)
  thus ?case using B nonneg_matpow[of n] nonneg 
    by (auto simp: matrix_matrix_mult_def intro!: sum_mono mult_mono')
qed simp

lemma matpow_sum_one_mono: "matpow (A + mat 1) (n + k) $ i $ j \<ge> matpow (A + mat 1) n $ i $ j" 
proof (induct k)
  case (Suc k)
  have "(matpow (A + mat 1) (n + k) ** A) $h i $h j \<ge> 0" unfolding matrix_matrix_mult_def
    using order.trans[OF nonneg_matpow matpow_mono[of "A + mat 1" "n + k"]]
    by (auto intro!: sum_nonneg mult_nonneg_nonneg nonneg simp: mat_def)
  thus ?case using Suc by (simp add: matrix_add_ldistrib matrix_mul_rid)
qed simp

lemma awalk_pos_matpow_over: 
  assumes "awalk i xs j" "n \<ge> length xs"
  shows "matpow (A + mat 1) n $ j $ i > 0" 
proof -
  from assms(2) obtain k where n: "n = length xs + k" using le_Suc_ex by blast  
  have "0 < matpow A (length xs) $ j $ i" by (rule awalk_pos_matpow_exact[OF assms(1)])
  also have "\<dots> \<le> matpow (A + mat 1) (length xs) $ j $ i" 
    by (rule matpow_mono, auto simp: mat_def)
  also have "\<dots> \<le> matpow (A + mat 1) n $ j $ i" unfolding n using matpow_sum_one_mono .
  finally show ?thesis .
qed

lemma irreducible_matpow_pos: assumes irreducible 
  shows "matpow (A + mat 1) (CARD('n) - 1) $ i $ j > 0"
proof -
  from assms[unfolded irreducible_def] have "reachable G j i" by auto
  then obtain p where p: "apath j p i" unfolding reachable_apath by auto
  from p have "awalk j p i" by (rule awalkI_apath)
  show ?thesis
  proof (rule awalk_pos_matpow_over[OF \<open>awalk j p i\<close>])
    from length_apath_less[OF p] have "length p < card (verts G)" by auto
    also have "card (verts G) \<le> CARD('n)"
      by (rule card_mono, auto)
    finally show "length p \<le> CARD('n) - 1" by auto
  qed
qed
end

locale perron_frobenius = nonneg_mat A 
  for A :: "real ^ 'n ^ 'n" +
  assumes irr: irreducible
begin

lemma pf_transpose: "perron_frobenius (transpose A)" 
proof
  show "fixed_mat.irreducible (transpose A)" 
    unfolding fixed_mat.irreducible_def reachable1_transpose using irr[unfolded irreducible_def] 
    by auto
  fix i j
qed (insert nonneg, auto simp: transpose_def)

abbreviation le_vec :: "real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> bool" where
  "le_vec x y \<equiv> (\<forall> i. x $ i \<le> y $ i)" 

abbreviation lt_vec :: "real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> bool" where
  "lt_vec x y \<equiv> (\<forall> i. x $ i < y $ i)" 

definition "A1n = matpow (A + mat 1) (CARD('n) - 1)" 

lemmas A1n_pos = irreducible_matpow_pos[OF irr, folded A1n_def]

definition r :: "real ^ 'n \<Rightarrow> real" where
  "r x = Min { (A *v x) $ j / x $ j | j. x $ j \<noteq> 0 }" 

definition X :: "(real ^ 'n )set" where
  "X = { x . le_vec 0 x \<and> x \<noteq> 0 }" 

lemma nonneg_Ax: "x \<in> X \<Longrightarrow> le_vec 0 (A *v x)" 
  unfolding X_def using nonneg
  by (auto simp: matrix_vector_mult_def intro!: sum_nonneg)

lemma A_nonzero_fixed_j: "\<exists> i. A $ i $ j \<noteq> 0" 
proof -
  from irr[unfolded irreducible_def, rule_format, of j j] have "reachable1 G j j" .
  from this[unfolded reachable1_awalk] obtain p where walk: "awalk j p j" and p: "p \<noteq> []" by auto
  from p obtain a q where "p = a # q" by (cases p, auto)
  with walk have "awalk j (a # q) j" by auto
  from this[unfolded awalk_Cons_iff] obtain i where "j = tail G a" "i = head G a" "a \<in> arcs G" by auto
  hence Aij: "A $ i $ j \<noteq> 0" unfolding G_def by auto
  thus ?thesis ..
qed

lemma A_nonzero_fixed_i: "\<exists> j. A $ i $ j \<noteq> 0" 
proof -
  from irr[unfolded irreducible_def, rule_format, of i i] have "reachable1 G i i" .
  from this[unfolded reachable1_awalk] obtain p where walk: "awalk i p i" and p: "p \<noteq> []" by auto
  from p have "p = butlast p @ [last p]" by simp
  with walk have "awalk i (butlast p @ [last p]) i" by simp
  from this[unfolded awalk_append_iff] obtain j a where "awalk j [a] i" by blast
  from this[unfolded awalk_Cons_iff awalk_Nil_iff]
  have "j = tail G a" "i = head G a" "a \<in> arcs G" by auto
  hence Aij: "A $ i $ j \<noteq> 0" unfolding G_def by auto
  thus ?thesis ..
qed

lemma Ax_pos: assumes x: "lt_vec 0 x" 
  shows "lt_vec 0 (A *v x)" 
proof 
  fix i
  from A_nonzero_fixed_i[of i] obtain j where "A $ i $ j \<noteq> 0" by auto
  with nonneg[of i j] have A: "A $ i $ j > 0" by simp
  from x have "x $ j \<ge> 0" for j by (auto simp: order.strict_iff_order)
  note nonneg = mult_nonneg_nonneg[OF nonneg[of i] this]
  have "(A *v x) $ i = (\<Sum>j\<in>UNIV. A $ i $ j * x $ j)" 
    unfolding matrix_vector_mult_def by simp
  also have "\<dots> = A $ i $ j * x $ j + (\<Sum>j\<in>UNIV - {j}. A $ i $ j * x $ j)" 
    by (subst sum.remove, auto)
  also have "\<dots> > 0 + 0" 
    by (rule add_less_le_mono, insert A x[rule_format] nonneg,
    auto intro!: sum_nonneg mult_pos_pos)
  finally show "0 $ i < (A *v x) $ i" by simp
qed
  

lemma nonzero_Ax: assumes x: "x \<in> X"
  shows "A *v x \<noteq> 0" 
proof 
  assume 0: "A *v x = 0" 
  from x[unfolded X_def] have x: "le_vec 0 x" "x \<noteq> 0" by auto
  from x(2) obtain j where xj: "x $ j \<noteq> 0"
    by (metis vec_eq_iff zero_index)
  from A_nonzero_fixed_j[of j]  obtain i where Aij: "A $ i $ j \<noteq> 0" by auto
  from arg_cong[OF 0, of "\<lambda> v. v $ i", unfolded matrix_vector_mult_def]
  have "0 = (\<Sum> k \<in> UNIV. A $h i $h k * x $h k)" by auto
  also have "\<dots> = A $h i $h j * x $h j + (\<Sum> k \<in> UNIV - {j}. A $h i $h k * x $h k)" 
    by (subst sum.remove[of _ j], auto)
  also have "\<dots> > 0 + 0" 
    by (rule add_less_le_mono, insert nonneg[of i] Aij x(1) xj, 
    auto intro!: sum_nonneg mult_pos_pos simp: dual_order.not_eq_order_implies_strict) 
  finally show False by simp
qed

lemma r_witness: assumes x: "x \<in> X" 
  shows "\<exists> j. x $ j > 0 \<and> r x = (A *v x) $ j / x $ j"
proof -
  from x[unfolded X_def] have x: "le_vec 0 x" "x \<noteq> 0" by auto
  let ?A = "{ (A *v x) $ j / x $ j | j. x $ j \<noteq> 0 }" 
  from x(2) obtain j where "x $ j \<noteq> 0"
    by (metis vec_eq_iff zero_index)
  hence empty: "?A \<noteq> {}" by auto
  from Min_in[OF _ this, folded r_def]
  obtain j where "x $ j \<noteq> 0" and rx: "r x = (A *v x) $ j / x $ j" by auto
  with x have "x $ j > 0" by (auto simp: dual_order.not_eq_order_implies_strict)
  with rx show ?thesis by auto
qed

lemma rx_nonneg: assumes x: "x \<in> X"
  shows "r x \<ge> 0"
proof -
  from x[unfolded X_def] have x: "le_vec 0 x" "x \<noteq> 0" by auto
  let ?A = "{ (A *v x) $ j / x $ j | j. x $ j \<noteq> 0 }" 
  from r_witness[OF \<open>x \<in> X\<close>]
  have empty: "?A \<noteq> {}" by force
  show ?thesis unfolding r_def X_def
  proof (subst Min_ge_iff, force, use empty in force, intro ballI) 
    fix y
    assume "y \<in> ?A" 
    then obtain j where "y = (A *v x) $ j / x $ j" and "x $ j \<noteq> 0" by auto
    from nonneg_Ax[OF \<open>x \<in> X\<close>] this x
    show "0 \<le> y" by simp
  qed
qed

lemma rx_pos: assumes x: "lt_vec 0 x"
  shows "r x > 0"
proof -
  from Ax_pos[OF x] have lt: "lt_vec 0 (A *v x)" .
  from x have x': "x \<in> X" unfolding X_def order.strict_iff_order by auto
  let ?A = "{ (A *v x) $ j / x $ j | j. x $ j \<noteq> 0 }" 
  from r_witness[OF \<open>x \<in> X\<close>]
  have empty: "?A \<noteq> {}" by force
  show ?thesis unfolding r_def X_def
  proof (subst Min_gr_iff, force, use empty in force, intro ballI) 
    fix y
    assume "y \<in> ?A" 
    then obtain j where "y = (A *v x) $ j / x $ j" and "x $ j \<noteq> 0" by auto
    from lt this x show "0 < y" by simp
  qed
qed

lemma rx_le_Ax: assumes x: "x \<in> X" 
  shows "le_vec (r x *s x) (A *v x)" 
proof (intro allI)
  fix i
  show "(r x *s x) $h i \<le> (A *v x) $h i" 
  proof (cases "x $ i = 0")
    case True
    with nonneg_Ax[OF x] show ?thesis by auto
  next
    case False
    with x[unfolded X_def] have pos: "x $ i > 0" 
      by (auto simp: dual_order.not_eq_order_implies_strict)
    from False have "(A *v x) $h i / x $ i \<in> { (A *v x) $ j / x $ j | j. x $ j \<noteq> 0 }" by auto
    hence "(A *v x) $h i / x $ i \<ge> r x" unfolding r_def by simp
    hence "x $ i * r x \<le> x $ i * ((A *v x) $h i / x $ i)" unfolding mult_le_cancel_left_pos[OF pos] .
    also have "\<dots> = (A *v x) $h i" using pos by simp
    finally show ?thesis by (simp add: ac_simps)
  qed
qed

lemma rho_le_x_Ax_imp_rho_le_rx: assumes x: "x \<in> X"
  and \<rho>: "le_vec (\<rho> *s x) (A *v x)"
shows "\<rho> \<le> r x" 
proof -
  from r_witness[OF x] obtain j where 
    rx: "r x = (A *v x) $ j / x $ j" and xj: "x $ j > 0" "x $ j \<ge> 0" by auto
  from divide_right_mono[OF \<rho>[rule_format, of j] xj(2)]
  show ?thesis unfolding rx using xj by simp 
qed

lemma rx_Max: assumes x: "x \<in> X"
  shows "r x = Sup { \<rho> . le_vec (\<rho> *s x) (A *v x) }" (is "_ = Sup ?S")
proof -
  have "r x \<in> ?S" using rx_le_Ax[OF x] by auto
  moreover {
    fix y
    assume "y \<in> ?S"
    hence y: "le_vec (y *s x) (A *v x)" by auto
    from rho_le_x_Ax_imp_rho_le_rx[OF x this]
    have "y \<le> r x" . 
  }
  ultimately show ?thesis by (metis (mono_tags, lifting) cSup_eq_maximum)
qed

lemma r_smult: assumes x: "x \<in> X" 
  and a: "a > 0" 
shows "r (a *s x) = r x" 
  unfolding r_def
  by (rule arg_cong[of _ _ Min], unfold vector_smult_distrib, insert a, simp)

definition "X1 = (X \<inter> {x. norm x = 1})" 

lemma bounded_X1: "bounded X1" unfolding bounded_iff X1_def by auto

lemma closed_X1: "closed X1"
proof -
  have X1: "X1 = {x. le_vec 0 x \<and> norm x = 1}" 
    unfolding X1_def X_def by auto
  show ?thesis unfolding X1
    by (intro closed_Collect_conj closed_Collect_all  closed_Collect_le closed_Collect_eq,
      auto intro: continuous_intros)
qed

lemma compact_X1: "compact X1" using bounded_X1 closed_X1
  by (simp add: compact_eq_bounded_closed)

definition "pow_A_1 x = A1n *v x" 



lemma continuous_pow_A_1: "continuous_on R pow_A_1"
  unfolding pow_A_1_def continuous_on
  by (auto intro: tendsto_intros)

definition "Y = pow_A_1 ` X1" 

lemma compact_Y: "compact Y" 
  unfolding Y_def using compact_X1 continuous_pow_A_1[of X1] 
  by (metis compact_continuous_image)

lemma Y_pos_main: assumes y: "y \<in> pow_A_1 ` X" 
  shows "y $ i > 0" 
proof -
  from y obtain x where x: "x \<in> X" and y: "y = pow_A_1 x" unfolding Y_def X1_def by auto
  from r_witness[OF x] obtain j where xj: "x $ j > 0" by auto
  from x[unfolded X_def] have xi: "x $ i \<ge> 0" for i by auto
  have nonneg: "0 \<le> A1n $ i $ k * x $ k" for k using A1n_pos[of i k] xi[of k] by auto 
  have "y $ i = (\<Sum>j\<in>UNIV. A1n $ i $ j * x $ j)" 
    unfolding y pow_A_1_def matrix_vector_mult_def by simp
  also have "\<dots> = A1n $ i $ j * x $ j + (\<Sum>j\<in>UNIV - {j}. A1n $ i $ j * x $ j)" 
    by (subst sum.remove, auto)
  also have "\<dots> > 0 + 0" 
    by (rule add_less_le_mono, insert xj A1n_pos nonneg, 
    auto intro!: sum_nonneg mult_pos_pos simp: dual_order.not_eq_order_implies_strict)
  finally show ?thesis by simp
qed

lemma Y_pos: assumes y: "y \<in> Y" 
  shows "y $ i > 0" 
  using Y_pos_main[of y i] y unfolding Y_def X1_def by auto

lemma Y_nonzero: assumes y: "y \<in> Y" 
  shows "y $ i \<noteq> 0" 
  using Y_pos[OF y, of i] by auto

definition r' :: "real ^ 'n \<Rightarrow> real" where
  "r' x = Min (range (\<lambda> j. (A *v x) $ j / x $ j))" 

lemma r'_r: assumes x: "x \<in> Y" shows "r' x = r x" 
  unfolding r'_def r_def
proof (rule arg_cong[of _ _ Min])
  have "range (\<lambda>j. (A *v x) $ j / x $ j) \<subseteq> {(A *v x) $ j / x $ j |j. x $ j \<noteq> 0}" (is "?L \<subseteq> ?R")
  proof 
    fix y
    assume "y \<in> ?L" 
    then obtain j where "y = (A *v x) $ j / x $ j" by auto
    with Y_pos[OF x, of j] show "y \<in> ?R" by auto
  qed
  moreover have "?L \<supseteq> ?R" by auto
  ultimately show "?L = ?R" by blast
qed  

lemma continuous_Y_r: "continuous_on Y r"
proof -
  have *: "(\<forall> y \<in> Y. P y (r y)) = (\<forall> y \<in> Y. P y (r' y))" for P using r'_r by auto
  have "continuous_on Y r = continuous_on Y r'" 
    by (rule continuous_on_cong[OF refl r'_r[symmetric]])
  also have \<dots>
    unfolding continuous_on r'_def using Y_nonzero
    by (auto intro!: tendsto_Min tendsto_intros)
  finally show ?thesis .
qed
 
lemma X1_nonempty: "X1 \<noteq> {}" 
proof -
  define x where "x = ((\<chi> i. if i = undefined then 1 else 0) :: real ^ 'n)" 
  {
    assume "x = 0" 
    from arg_cong[OF this, of "\<lambda> x. x $ undefined"] have False unfolding x_def by auto
  }
  hence x: "x \<noteq> 0" by auto
  moreover have "le_vec 0 x" unfolding x_def by auto
  moreover have "norm x = 1" unfolding norm_vec_def setL2_def
    by (auto, subst sum.remove[of _ undefined], auto simp: x_def)
  ultimately show ?thesis unfolding X1_def X_def by auto
qed

lemma Y_nonempty: "Y \<noteq> {}" 
  unfolding Y_def using X1_nonempty by auto

definition z where "z = (SOME z. z \<in> Y \<and> (\<forall> y \<in> Y. r y \<le> r z))" 

abbreviation "sr \<equiv> r z"

lemma z: "z \<in> Y" and sr_max_Y: "\<And> y. y \<in> Y \<Longrightarrow> r y \<le> sr" 
proof -
  let ?P = "\<lambda> z. z \<in> Y \<and> (\<forall> y \<in> Y. r y \<le> r z)" 
  from continuous_attains_sup[OF compact_Y Y_nonempty continuous_Y_r]
  obtain y where "?P y" by blast
  from someI[of ?P, OF this, folded z_def]
  show "z \<in> Y" "\<And> y. y \<in> Y \<Longrightarrow> r y \<le> r z" by blast+
qed

lemma Y_subset_X: "Y \<subseteq> X" 
proof
  fix y
  assume "y \<in> Y" 
  from Y_pos[OF this] show "y \<in> X" unfolding X_def 
    by (auto simp: order.strict_iff_order) 
qed

lemma zX: "z \<in> X" 
  using z(1) Y_subset_X by auto

lemma le_vec_mono_left: assumes B: "\<And> i j. B $ i $ j \<ge> 0" 
  and "le_vec x y" 
shows "le_vec (B *v x) (B *v y)" 
proof (intro allI)
  fix i
  show "(B *v x) $ i \<le> (B *v y) $ i" unfolding matrix_vector_mult_def using B[of i] assms(2)
    by (auto intro!: sum_mono mult_left_mono)
qed  


lemma matpow_1_commute: "matpow (A + mat 1) n ** A = A ** matpow (A + mat 1) n" 
  by (induct n, auto simp: matrix_add_rdistrib matrix_add_ldistrib matrix_mul_rid matrix_mul_lid
  matrix_mul_assoc[symmetric])

lemma A1n_commute: "A1n ** A = A ** A1n" 
  unfolding A1n_def by (rule matpow_1_commute)

lemma le_vec_pow_A_1: assumes le: "le_vec (rho *s x) (A *v x)" 
  shows "le_vec (rho *s pow_A_1 x) (A *v pow_A_1 x)" 
proof -
  have "A1n $ i $ j \<ge> 0" for i j using A1n_pos[of i j] by auto
  from le_vec_mono_left[OF this le]
  have "le_vec (A1n *v (rho *s x)) (A1n *v (A *v x))" .
  also have "A1n *v (A *v x) = (A1n ** A) *v x" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = A *v (A1n *v x)" unfolding A1n_commute by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = A *v (pow_A_1 x)" unfolding pow_A_1_def ..
  also have "A1n *v (rho *s x) = rho *s (A1n *v x)" unfolding vector_smult_distrib ..
  also have "\<dots> = rho *s pow_A_1 x" unfolding pow_A_1_def ..
  finally show "le_vec (rho *s pow_A_1 x) (A *v pow_A_1 x)" .
qed

lemma r_pow_A_1: assumes x: "x \<in> X"
  shows "r x \<le> r (pow_A_1 x)" 
proof -
  let ?y = "pow_A_1 x" 
  have "?y \<in> pow_A_1 ` X" using x by auto
  from Y_pos_main[OF this] 
  have y: "?y \<in> X" unfolding X_def by (auto simp: order.strict_iff_order) 
  let ?A = "{\<rho>. le_vec (\<rho> *s x) (A *v x)}" 
  let ?B = "{\<rho>. le_vec (\<rho> *s pow_A_1 x) (A *v pow_A_1 x)}" 
  show ?thesis unfolding rx_Max[OF x] rx_Max[OF y]
  proof (rule cSup_mono)
    show "bdd_above ?B" using rho_le_x_Ax_imp_rho_le_rx[OF y] by fast
    show "?A \<noteq> {}" using rx_le_Ax[OF x] by auto 
    fix rho
    assume "rho \<in> ?A"
    hence "le_vec (rho *s x) (A *v x)" by auto
    from le_vec_pow_A_1[OF this] have "rho \<in> ?B" by auto
    thus "\<exists> rho' \<in> ?B. rho \<le> rho'" by auto
  qed
qed

lemma sr_max: assumes x: "x \<in> X" 
  shows "r x \<le> sr" 
proof -
  let ?n = "norm x" 
  define x' where "x' = inverse ?n *s x" 
  from x[unfolded X_def] have x0: "x \<noteq> 0" by auto
  hence n: "?n > 0" by auto
  have x': "x' \<in> X1" "x' \<in> X" using x n unfolding X1_def X_def x'_def by (auto simp: norm_smult)
  have id: "r x = r x'" unfolding x'_def 
    by (rule sym, rule r_smult[OF x], insert n, auto)
  define y where "y = pow_A_1 x'" 
  from x' have y: "y \<in> Y" unfolding Y_def y_def by auto
  note id
  also have "r x' \<le> r y" using r_pow_A_1[OF x'(2)] unfolding y_def .
  also have "\<dots> \<le> r z" using sr_max_Y[OF y] .
  finally show "r x \<le> r z" .
qed

lemma z_pos: "z $ i > 0" 
  using Y_pos[OF z(1)] by auto

lemma sr_pos: "sr > 0"
  by (rule rx_pos, insert z_pos, auto)

context fixes u
  assumes u: "u \<in> X" and ru: "r u = sr" 
begin

lemma sr_imp_eigen_vector_main: "sr *s u = A *v u" 
proof (rule ccontr)
  assume *: "sr *s u \<noteq> A *v u" 
  let ?x = "A *v u - sr *s u" 
  from * have 0: "?x \<noteq> 0" by auto
  let ?y = "pow_A_1 u" 
  have "le_vec (sr *s u) (A *v u)" using rx_le_Ax[OF u] unfolding ru .
  hence le: "le_vec 0 ?x" by auto
  from 0 le have x: "?x \<in> X" unfolding X_def by auto
  have y_pos: "lt_vec 0 ?y" using Y_pos_main[of ?y] u by auto
  hence y: "?y \<in> X" unfolding X_def by (auto simp: order.strict_iff_order)  
  from Y_pos_main[of "pow_A_1 ?x"] x 
  have "lt_vec 0 (pow_A_1 ?x)" by auto
  hence lt: "lt_vec (sr *s ?y) (A *v ?y)" unfolding pow_A_1_def matrix_vector_right_distrib_diff
    matrix_vector_mul_assoc A1n_commute vector_smult_distrib by simp
  let ?f = "(\<lambda> i. (A *v ?y - sr *s ?y) $ i / ?y $ i)" 
  let ?U = "UNIV :: 'n set"
  define eps where "eps = Min (?f ` ?U)" 
  have U: "finite (?f ` ?U)" "?f ` ?U \<noteq> {}" by auto
  have eps: "eps > 0" unfolding eps_def Min_gr_iff[OF U]
    using lt sr_pos y_pos by auto
  have le: "le_vec ((sr + eps) *s ?y) (A *v ?y)"
  proof 
    fix i
    have "((sr + eps) *s ?y) $ i = sr * ?y $ i + eps * ?y $ i" by simp
    also have "\<dots> \<le> sr * ?y $ i + ?f i * ?y $ i" 
    proof (rule add_left_mono[OF mult_right_mono])
      show "0 \<le> ?y $ i" using y_pos[rule_format, of i] by auto
      show "eps \<le> ?f i" unfolding eps_def by (rule Min_le, auto) 
    qed
    also have "\<dots> = (A *v ?y) $ i" using sr_pos y_pos[rule_format, of i] 
      by simp
    finally  
    show "((sr + eps) *s ?y) $ i \<le> (A *v ?y) $ i" .
  qed
  from rho_le_x_Ax_imp_rho_le_rx[OF y le]
  have "r ?y \<ge> sr + eps" .
  with sr_max[OF y] eps show False by auto
qed

lemma sr_imp_eigen_vector: "eigen_vector A u sr" 
  unfolding eigen_vector_def sr_imp_eigen_vector_main using u unfolding X_def by auto

lemma sr_u_pos: "lt_vec 0 u" 
proof -
  let ?y = "pow_A_1 u" 
  define n where "n = (CARD('n) - 1)" 
  define c where "c = (sr + 1)^n" 
  have c: "c > 0" using sr_pos unfolding c_def by auto
  have "lt_vec 0 ?y" using Y_pos_main[of ?y] u by auto
  also have "?y = A1n *v u" unfolding pow_A_1_def ..
  also have "\<dots> = c *s u" unfolding c_def A1n_def n_def[symmetric]
  proof (induct n)
    case (Suc n)
    show ?case by (simp add: matrix_add_ldistrib matrix_mul_rid 
      matrix_add_vect_distrib Suc matpow_1_commute matrix_vector_mul_assoc[symmetric] 
      vector_smult_distrib sr_imp_eigen_vector_main[symmetric] field_simps)
  qed (auto simp: matrix_vector_mul_lid)
  finally have lt: "lt_vec 0 (c *s u)" .
  have "0 < u $ i" for i using lt[rule_format, of i] c by simp (metis zero_less_mult_pos)
  thus "lt_vec 0 u" by simp
qed
end

lemma eigen_vector_z_sr: "eigen_vector A z sr" 
  using sr_imp_eigen_vector[OF zX refl] by auto

abbreviation "c \<equiv> complex_of_real" 
abbreviation "cA \<equiv> map_matrix c A" 
abbreviation "norm_v \<equiv> map_vector (norm :: complex \<Rightarrow> real)" 

lemma norm_v_ge_0: "le_vec 0 (norm_v v)" by (auto simp: map_vector_def)
lemma norm_v_eq_0: "norm_v v = 0 \<longleftrightarrow> v = 0" by (auto simp: map_vector_def vec_eq_iff)

lemma cA_index: "cA $ i $ j = c (A $ i $ j)" 
  unfolding map_matrix_def map_vector_def by simp

lemma norm_cA[simp]: "norm (cA $ i $ j) = A $ i $ j" 
  using nonneg[of i j] by (simp add: cA_index)

context fixes \<alpha> v
  assumes ev: "eigen_vector cA v \<alpha>" 
begin

lemma evD: "\<alpha> *s v = cA *v v" "v \<noteq> 0" 
  using ev[unfolded eigen_vector_def] by auto

lemma ev_alpha_norm_v: "norm_v (\<alpha> *s v) = (norm \<alpha> *s norm_v v)" 
  by (auto simp: map_vector_def norm_mult vec_eq_iff)

lemma ev_A_norm_v: "norm_v (cA *v v) $ j \<le> (A *v norm_v v) $ j" 
proof -
  have "norm_v (cA *v v) $ j = norm (\<Sum>i\<in>UNIV. cA $ j $ i * v $ i)" 
    unfolding map_vector_def by (simp add: matrix_vector_mult_def)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. norm (cA $ j $ i * v $ i))" by (rule norm_sum)
  also have "\<dots> = (\<Sum>i\<in>UNIV. A $ j $ i * norm_v v $ i)" 
    by (rule sum.cong[OF refl], auto simp: norm_mult map_vector_def)
  also have "\<dots> = (A *v norm_v v) $ j" by (simp add: matrix_vector_mult_def)
  finally show ?thesis .
qed

lemma ev_le_vec: "le_vec (norm \<alpha> *s norm_v v) (A *v norm_v v)" 
  using arg_cong[OF evD(1), of norm_v, unfolded ev_alpha_norm_v] ev_A_norm_v by auto

lemma norm_v_X: "norm_v v \<in> X" 
  using norm_v_ge_0[of v] evD(2) norm_v_eq_0[of v] unfolding X_def by auto

lemma ev_inequalities: "norm \<alpha> \<le> r (norm_v v)" "r (norm_v v) \<le> sr"
proof -
  have v: "norm_v v \<in> X" by (rule norm_v_X)
  from rho_le_x_Ax_imp_rho_le_rx[OF v ev_le_vec] 
  show "norm \<alpha> \<le> r (norm_v v)" .
  from sr_max[OF v]
  show "r (norm_v v) \<le> sr" .
qed

lemma norm_sr: "norm \<alpha> \<le> sr" using ev_inequalities by auto
end

lemma le_vec_trans: "le_vec x y \<Longrightarrow> le_vec y u \<Longrightarrow> le_vec x u" 
  using order.trans[of "x $ i" "y $ i" "u $ i" for i] by auto

lemma eigen_vector_z_sr_c: "eigen_vector cA (map_vector c z) (c sr)" 
  unfolding of_real_hom.eigen_vector_hom by (rule eigen_vector_z_sr)

definition "w = perron_frobenius.z (transpose A)" 

lemma w: "transpose A *v w = sr *s w" "lt_vec 0 w" "perron_frobenius.sr (transpose A) = sr"
proof -
  interpret t: perron_frobenius "transpose A" 
    by (rule pf_transpose)
  from eigen_vector_z_sr_c t.eigen_vector_z_sr_c 
  have ev: "eigen_value cA (c sr)" "eigen_value t.cA (c t.sr)" 
    unfolding eigen_value_def by auto
  {
    fix x
    have "eigen_value (t.cA) x = eigen_value (transpose cA) x" 
      unfolding map_matrix_def map_vector_def transpose_def 
      by (auto simp: vec_eq_iff)
    also have "\<dots> = eigen_value cA x" by (rule eigen_value_transpose)
    finally have "eigen_value (t.cA) x = eigen_value cA x" .
  } note ev_id = this
  with ev have ev: "eigen_value t.cA (c sr)" "eigen_value cA (c t.sr)" by auto
  then obtain v1 v2 where ev: "eigen_vector t.cA v1 (c sr)" "eigen_vector cA v2 (c t.sr)"
    unfolding eigen_value_def by auto
  from norm_sr[OF ev(2)] t.norm_sr[OF ev(1)] 
  show id: "t.sr = sr" by auto
  from t.eigen_vector_z_sr[unfolded id, folded w_def] show "transpose A *v w = sr *s w" 
    unfolding eigen_vector_def by auto
  from t.z_pos[folded w_def] show "lt_vec 0 w" by auto
qed

lemma c_cmod_id: "a \<in> \<real> \<Longrightarrow> Re a \<ge> 0 \<Longrightarrow> c (cmod a) = a" by (auto simp: Reals_def)

lemma pos_rowvector_mult_0: assumes lt: "lt_vec 0 x" 
  and 0: "(rowvector x :: real ^ 'n ^ 'n) *v y = 0" (is "?x *v _ = 0") and le: "le_vec 0 y" 
shows "y = 0" 
proof -
  {
    fix i
    assume "y $ i \<noteq> 0" 
    with le have yi: "y $ i > 0" by (auto simp: order.strict_iff_order)
    have "0 = (?x *v y) $ i" unfolding 0 by simp
    also have "\<dots> = (\<Sum>j\<in>UNIV. x $ j * y $ j)" 
      unfolding rowvector_def matrix_vector_mult_def by simp
    also have "\<dots> > 0" 
      by (rule sum_pos2[of _ i], insert yi lt le, auto intro!: mult_nonneg_nonneg 
        simp: order.strict_iff_order)
    finally have False by simp
  }
  thus ?thesis by (auto simp: vec_eq_iff)
qed

lemma pos_matrix_mult_0: assumes le: "\<And> i j. B $ i $ j \<ge> 0" 
  and lt: "lt_vec 0 x" 
  and 0: "B *v x = 0" 
shows "B = 0" 
proof -
  {
    fix i j
    assume "B $ i $ j \<noteq> 0" 
    with le have gt: "B $ i $ j > 0" by (auto simp: order.strict_iff_order)
    have "0 = (B *v x) $ i" unfolding 0 by simp
    also have "\<dots> = (\<Sum>j\<in>UNIV. B $ i $ j * x $ j)" 
      unfolding matrix_vector_mult_def by simp
    also have "\<dots> > 0" 
      by (rule sum_pos2[of _ j], insert gt lt le, auto intro!: mult_nonneg_nonneg 
        simp: order.strict_iff_order)
    finally have False by simp
  }
  thus "B = 0" unfolding vec_eq_iff by auto
qed

lemma eigen_value_smaller_matrix: assumes B: "\<And> i j. 0 \<le> B $ i $ j \<and> B $ i $ j \<le> A $ i $ j"
  and AB: "A \<noteq> B" 
  and ev: "eigen_value (map_matrix c B) sigma"
shows "cmod sigma < sr" 
proof -  
  let ?B = "map_matrix c B" 
  let ?sr = "spectral_radius ?B" 
  define \<sigma> where "\<sigma> = ?sr" 
  have "real_non_neg_mat ?B" unfolding real_non_neg_mat_def elements_mat_h_def
    by (auto simp: map_matrix_def map_vector_def B)
  from perron_frobenius[OF this, folded \<sigma>_def] obtain x where ev_sr: "eigen_vector ?B x (c \<sigma>)" 
    and rnn: "real_non_neg_vec x" by auto  
  define y where "y = norm_v x" 
  from rnn have xy: "x = map_vector c y" 
    unfolding real_non_neg_vec_def vec_elements_h_def y_def
    by (auto simp: map_vector_def vec_eq_iff c_cmod_id)
  from spectral_radius_max[OF ev, folded \<sigma>_def] have sigma_sigma: "cmod sigma \<le> \<sigma>" .
  from ev_sr[unfolded xy of_real_hom.eigen_vector_hom] 
  have ev_B: "eigen_vector B y \<sigma>" .
  from ev_B[unfolded eigen_vector_def] have ev_B': "B *v y = \<sigma> *s y" by auto
  have ypos: "y $ i \<ge> 0" for i unfolding y_def by (auto simp: map_vector_def)
  from ev_B this have y: "y \<in> X" unfolding eigen_vector_def X_def by auto
  
  have BA: "(B *v y) $ i \<le> (A *v y) $ i" for i
    unfolding matrix_vector_mult_def vec_lambda_beta
    by (rule sum_mono, rule mult_right_mono, insert B ypos, auto)  
  hence le_vec: "le_vec (\<sigma> *s y) (A *v y)" unfolding ev_B' by auto
  from rho_le_x_Ax_imp_rho_le_rx[OF y le_vec] 
  have "\<sigma> \<le> r y" by auto
  also have "\<dots> \<le> sr" using y by (rule sr_max)
  finally have sig_le_sr: "\<sigma> \<le> sr" .
  {
    assume "\<sigma> = sr" 
    hence r_sr: "r y = sr" and sr_sig: "sr = \<sigma>" using `\<sigma> \<le> r y` `r y \<le> sr` by auto
    from sr_u_pos[OF y r_sr] have pos: "lt_vec 0 y" .
    from sr_imp_eigen_vector[OF y r_sr] have ev': "eigen_vector A y sr" .
    have "(A - B) *v y = A *v y - B *v y" unfolding matrix_vector_mult_def
      by (auto simp: vec_eq_iff field_simps sum_subtractf) 
    also have "A *v y = sr *s y" using ev'[unfolded eigen_vector_def] by auto
    also have "B *v y = sr *s y" unfolding ev_B' sr_sig ..
    finally have id: "(A - B) *v y = 0" by simp
    from pos_matrix_mult_0[OF _ pos id] assms(1-2) have False by auto
  }
  with sig_le_sr sigma_sigma show ?thesis by argo
qed

lemma charpoly_erase_mat_sr: "0 < poly (charpoly (erase_mat A i i)) sr" 
proof -
  let ?A = "erase_mat A i i" 
  let ?pos = "poly (charpoly ?A) sr" 
  {
    from A_nonzero_fixed_j[of i] obtain k where "A $ k $ i \<noteq> 0" by auto
    assume "A = ?A" 
    hence "A $ k $ i = ?A $ k $ i" by simp
    also have "?A $ k $ i = 0" by (auto simp: erase_mat_def)
    also have "A $ k $ i \<noteq> 0" by fact
    finally have False by simp
  }
  hence AA: "A \<noteq> ?A" by auto
  have le: "0 \<le> ?A $ i $ j \<and> ?A $ i $ j \<le> A $ i $ j" for i j
    by (auto simp: erase_mat_def nonneg)
  note ev_small = eigen_value_smaller_matrix[OF le AA]  
  {
    fix rho :: real
    assume "eigen_value ?A rho" 
    hence ev: "eigen_value (map_matrix c ?A) (c rho)" 
      unfolding eigen_value_def using of_real_hom.eigen_vector_hom[of ?A _ rho] by auto
    from ev_small[OF this] have "abs rho < sr" by auto
  } note ev_small_real = this
  have pos0: "?pos \<noteq> 0" 
    using ev_small_real[of sr] by (auto simp: eigen_value_root_charpoly)
  {
    define p where "p = charpoly ?A"
    assume pos: "?pos < 0" 
    hence neg: "poly p sr < 0" unfolding p_def by auto
    from degree_monic_charpoly[of ?A] have mon: "monic p" and deg: "degree p \<noteq> 0" unfolding p_def by auto
    let ?f = "poly p" 
    have cont: "continuous_on {a..b} ?f" for a b by (auto intro: continuous_intros)
    from pos have le: "?f sr \<le> 0" by (auto simp: p_def)
    from mon have lc: "lead_coeff p > 0" by auto
    from poly_pinfty_ge[OF this deg, of 0] obtain z where lez: "\<And> x. z \<le> x \<Longrightarrow> 0 \<le> ?f x" by auto
    define y where "y = max z sr" 
    have yr: "y \<ge> sr" and "y \<ge> z" unfolding y_def by auto
    from lez[OF this(2)] have y0: "?f y \<ge> 0" .
    from IVT'[of ?f, OF le y0 yr cont] obtain x where ge: "x \<ge> sr" and rt: "?f x = 0" 
      unfolding p_def by auto
    hence "eigen_value ?A x" unfolding p_def by (simp add: eigen_value_root_charpoly)
    from ev_small_real[OF this] ge have False by auto
  }
  with pos0 show ?thesis by argo
qed

lemma multiplicity_sr_1: "order sr (charpoly A) = 1" 
proof -
  {
    assume "poly (pderiv (charpoly A)) sr = 0" 
    hence "0 = poly (monom 1 1 * pderiv (charpoly A)) sr" by simp
    also have "\<dots> = sum (\<lambda> i. poly (charpoly (erase_mat A i i)) sr) UNIV" 
      unfolding pderiv_char_poly_erase_mat poly_sum ..
    also have "\<dots> > 0" 
      by (rule sum_pos, (force simp: charpoly_erase_mat_sr)+)
    finally have False by simp
  } 
  hence nZ: "poly (pderiv (charpoly A)) sr \<noteq> 0" and nZ': "pderiv (charpoly A) \<noteq> 0" by auto
  from eigen_vector_z_sr have "eigen_value A sr" unfolding eigen_value_def ..
  from this[unfolded eigen_value_root_charpoly]
  have "poly (charpoly A) sr = 0" .
  hence "order sr (charpoly A) \<noteq> 0" unfolding order_root using nZ' by auto
  from order_pderiv[OF nZ' this] order_0I[OF nZ]
  show ?thesis by simp
qed

lemma sr_spectral_radius: "sr = spectral_radius cA" 
proof -
  from eigen_vector_z_sr_c have "eigen_value cA (c sr)" 
    unfolding eigen_value_def by auto
  from spectral_radius_max[OF this] 
  have sr: "sr \<le> spectral_radius cA" by auto
  with spectral_radius_ev[of cA] norm_sr
  show ?thesis by force
qed

lemma le_vec_A_mu: assumes y: "y \<in> X" and le: "le_vec (A *v y) (mu *s y)" 
  shows "sr \<le> mu" "lt_vec 0 y" 
  "mu = sr \<or> A *v y = mu *s y \<Longrightarrow> mu = sr \<and> A *v y = mu *s y" 
proof -
  let ?w = "rowvector w" 
  let ?w' = "columnvector w" 
  have "?w ** A = transpose (transpose (?w ** A))" 
    unfolding transpose_transpose by simp
  also have "transpose (?w ** A) = transpose A ** transpose ?w" 
    by (rule matrix_transpose_mul)
  also have "transpose ?w = columnvector w" by (rule transpose_rowvector)
  also have "transpose A ** \<dots> = columnvector (transpose A *v w)" 
    unfolding dot_rowvector_columnvector[symmetric] ..
  also have "transpose A *v w = sr *s w" unfolding w by simp
  also have "transpose (columnvector \<dots>) = rowvector (sr *s w)"
    unfolding transpose_def columnvector_def rowvector_def vector_scalar_mult_def by auto
  finally have 1: "?w ** A = rowvector (sr *s w)" .
  have "sr *s (?w *v y) = ?w ** A *v y" unfolding 1
    by (auto simp: rowvector_def vector_scalar_mult_def matrix_vector_mult_def vec_eq_iff
       sum_distrib_left)
  also have "\<dots> = ?w *v (A *v y)" by (simp add: matrix_vector_mul_assoc)
  finally have eq1: "sr *s (rowvector w *v y) = rowvector w *v (A *v y)" .
  have "le_vec (rowvector w *v (A *v y)) (?w *v (mu *s y))" 
    by (rule le_vec_mono_left[OF _ le], insert w(2), auto simp: rowvector_def order.strict_iff_order)
  also have "?w *v (mu *s y) = mu *s (?w *v y)" by (simp add: vector_smult_distrib)
  finally have le1: "le_vec (rowvector w *v (A *v y)) (mu *s (?w *v y))" .
  from le1[unfolded eq1[symmetric]] 
  have 2: "le_vec (sr *s (?w *v y)) (mu *s (?w *v y))" .
  {
    from y obtain i where yi: "y $ i > 0" and y: "\<And> j. y $ j \<ge> 0" unfolding X_def
      by (auto simp: order.strict_iff_order vec_eq_iff)
    from w(2) have wi: "w $ i > 0" and w: "\<And> j. w $ j \<ge> 0"
      by (auto simp: order.strict_iff_order)
    have "(?w *v y) $ i > 0" using yi y wi w
      by (auto simp: matrix_vector_mult_def rowvector_def 
        intro!: sum_pos2[of _ i] mult_nonneg_nonneg)
    moreover from 2[rule_format, of i] have "sr * (?w *v y) $ i \<le> mu * (?w *v y) $ i" by simp
    ultimately have "sr \<le> mu" by simp
  } 
  thus *: "sr \<le> mu" .
  define cc where "cc = (mu + 1)^(CARD('n) - 1)" 
  define n where "n = (CARD('n) - 1)" 
  from * sr_pos have mu: "mu \<ge> 0" "mu > 0" by auto
  hence cc: "cc > 0" unfolding cc_def by simp  
  from y have "pow_A_1 y \<in> pow_A_1 ` X" by auto
  from Y_pos_main[OF this] have lt: "0 < (A1n *v y) $ i" for i by (simp add: pow_A_1_def)
  have le: "le_vec (A1n *v y) (cc *s y)" unfolding cc_def A1n_def n_def[symmetric]
  proof (induct n)
    case (Suc n)
    let ?An = "matpow (A + mat 1) n" 
    let ?mu = "(mu + 1)" 
    have id': "matpow (A + mat 1) (Suc n) *v y = A *v (?An *v y) + ?An *v y" (is "?a = ?b + ?c")
      by (simp add: matrix_add_ldistrib matrix_mul_rid matrix_add_vect_distrib matpow_1_commute
       matrix_vector_mul_assoc[symmetric])
    have "le_vec ?b (?mu^n *s (A *v y))" 
      using le_vec_mono_left[OF nonneg Suc] by (simp add: vector_smult_distrib)    
    moreover have "le_vec (?mu^n *s (A *v y)) (?mu^n *s (mu *s y))" 
      using le mu by auto
    moreover have id: "?mu^n *s (mu *s y) = (?mu^n * mu) *s y" by simp
    from le_vec_trans[OF calculation[unfolded id]] 
    have le1: "le_vec ?b ((?mu^n * mu) *s y)" . 
    from Suc have le2: "le_vec ?c ((mu + 1) ^ n *s y)" .
    have le: "le_vec ?a ((?mu^n * mu) *s y + ?mu^n *s y)" 
      unfolding id' using add_mono[OF le1[rule_format] le2[rule_format]] by auto    
    have id'': "(?mu^n * mu) *s y + ?mu^n *s y = ?mu^Suc n *s y" by (simp add: field_simps)
    show ?case using le unfolding id'' .
  qed (simp add: matrix_vector_mul_lid)
  have lt: "0 < cc * y $ i" for i using lt[of i] le[rule_format, of i] by auto
  have "y $ i > 0" for i using lt[of i] cc by (rule zero_less_mult_pos)
  thus "lt_vec 0 y" by auto
  assume **: "mu = sr \<or> A *v y = mu *s y" 
  {
    assume "A *v y = mu *s y" 
    with y have "eigen_vector A y mu" unfolding X_def eigen_vector_def by auto
    hence "eigen_vector cA (map_vector c y) (c mu)" unfolding of_real_hom.eigen_vector_hom .
    from norm_sr[OF this] * have "mu = sr" by auto
  }
  with ** have mu_sr: "mu = sr" by auto
  from eq1[folded vector_smult_distrib]
  have 0: "?w *v (sr *s y - A *v y) = 0"
    unfolding matrix_vector_right_distrib_diff by simp
  have le0: "le_vec 0 (sr *s y - A *v y)" using assms(2)[unfolded mu_sr] by auto
  have "sr *s y - A *v y = 0" using pos_rowvector_mult_0[OF w(2) 0 le0] .
  hence ev_y: "A *v y = sr *s y" by auto
  show "mu = sr \<and> A *v y = mu *s y" using ev_y mu_sr by auto
qed

lemma nonnegative_eigenvector_has_ev_sr: assumes "eigen_vector A v mu" and le: "le_vec 0 v" 
  shows "mu = sr" 
proof -
  from assms(1)[unfolded eigen_vector_def] have v: "v \<noteq> 0" and ev: "A *v v = mu *s v" by auto
  from le v have v: "v \<in> X" unfolding X_def by auto
  from ev have "le_vec (A *v v) (mu *s v)" by auto
  from le_vec_A_mu[OF v this] ev show ?thesis by auto
qed

lemma similar_matrix_rotation: assumes ev: "eigen_value cA \<alpha>" and \<alpha>: "cmod \<alpha> = sr"
  shows "similar_matrix (cis (arg \<alpha>) *k cA) cA" 
proof -
  from ev obtain y where ev: "eigen_vector cA y \<alpha>" unfolding eigen_value_def by auto
  let ?y = "norm_v y"
  note maps = map_vector_def map_matrix_def
  define yp where "yp = norm_v y" 
  let ?yp = "map_vector c yp" 
  have yp: "yp \<in> X" unfolding yp_def by (rule norm_v_X[OF ev])
  from ev[unfolded eigen_vector_def] have ev_y: "cA *v y = \<alpha> *s y" by auto
  from ev_le_vec[OF ev, unfolded \<alpha>, folded yp_def]
  have 1: "le_vec (sr *s yp) (A *v yp)" by simp
  from rho_le_x_Ax_imp_rho_le_rx[OF yp 1] have "sr \<le> r yp" by auto
  with ev_inequalities[OF ev, folded yp_def]
  have 2: "r yp = sr" by auto
  have ev_yp: "A *v yp = sr *s yp" 
    and pos_yp: "lt_vec 0 yp" 
    using sr_imp_eigen_vector_main[OF yp 2] sr_u_pos[OF yp 2] by auto
  define D where "D = diagvector (\<lambda> j. cis (arg (y $ j)))" 
  define inv_D where "inv_D = diagvector (\<lambda> j. cis (- arg (y $ j)))" 
  have DD: "inv_D ** D = mat 1" "D ** inv_D = mat 1" unfolding D_def inv_D_def 
    by (auto simp add: diagvector_eq_mat cis_mult)
  {
    fix i
    have "(D *v ?yp) $ i = cis (arg (y $ i)) * c (cmod (y $ i))" 
      unfolding D_def yp_def by (simp add: maps) 
    also have "\<dots> = y $ i" by (simp add: cis_mult_cmod_id)
    also note calculation
  }
  hence y_D_yp: "y = D *v ?yp" by (auto simp: vec_eq_iff)
  define \<phi> where "\<phi> = arg \<alpha>" 
  let ?\<phi> = "cis (- \<phi>)" 
  have [simp]: "cis (- \<phi>) * rcis sr \<phi> = sr" unfolding cis_rcis_eq rcis_mult by simp
  have \<alpha>: "\<alpha> = rcis sr \<phi>" unfolding \<phi>_def \<alpha>[symmetric] rcis_cmod_arg ..
  define F where "F = ?\<phi> *k (inv_D ** cA ** D)" 
  have "cA *v (D *v ?yp) = \<alpha> *s y" unfolding y_D_yp[symmetric] ev_y by simp
  also have "inv_D *v \<dots> = \<alpha> *s ?yp" 
    unfolding vector_smult_distrib y_D_yp matrix_vector_mul_assoc DD matrix_vector_mul_lid ..
  also have "?\<phi> *s \<dots> = sr *s ?yp" unfolding \<alpha> by simp
  also have "\<dots> = map_vector c (sr *s yp)" unfolding vec_eq_iff by (auto simp: maps)
  also have "\<dots> = cA *v ?yp" unfolding ev_yp[symmetric] by (auto simp: maps matrix_vector_mult_def)
  finally have F: "F *v ?yp = cA *v ?yp" unfolding F_def matrix_scalar_vector_ac[symmetric]
    unfolding matrix_vector_mul_assoc[symmetric] vector_smult_distrib .
  have prod: "inv_D ** cA ** D = (\<chi> i j. cis (- arg (y $ i)) * cA $ i $ j * cis (arg (y $ j)))" 
    unfolding inv_D_def D_def diagvector_mult_right diagvector_mult_left by simp
  {
    fix i j
    have "cmod (F $ i $ j) = cmod (?\<phi> * cA $h i $h j * (cis (- arg (y $h i)) * cis (arg (y $h j))))" 
      unfolding F_def prod vec_lambda_beta matrix_scalar_mult_def
      by (simp, simp only: ac_simps)
    also have "\<dots> = A $ i $ j" unfolding cis_mult unfolding norm_mult by simp
    also note calculation
  }
  hence FA: "map_matrix norm F = A" unfolding maps by auto
  let ?F = "map_matrix c (map_matrix norm F)" 
  let ?G = "?F - F" 
  let ?Re = "map_matrix Re" 
  from F[folded FA] have 0: "?G *v ?yp = 0" unfolding matrix_diff_vect_distrib by simp
  have "?Re ?G *v yp = map_vector Re (?G *v ?yp)" 
    unfolding maps matrix_vector_mult_def vec_lambda_beta Re_sum by auto
  also have "\<dots> = 0" unfolding 0 by (simp add: vec_eq_iff maps)
  finally have 0: "?Re ?G *v yp = 0" .
  have "?Re ?G = 0" 
    by (rule pos_matrix_mult_0[OF _ pos_yp 0], auto simp: maps complex_Re_le_cmod)
  hence "?F = F" by (auto simp: maps vec_eq_iff cmod_eq_Re)
  with FA have AF: "cA = F" by simp
  from arg_cong[OF this, of "\<lambda> A. cis \<phi> *k A"]
  have sim: "cis \<phi> *k cA = inv_D ** cA ** D" unfolding F_def matrix.scale_scale cis_mult
    by simp
  have "similar_matrix (cis \<phi> *k cA) cA" unfolding similar_matrix_def similar_matrix_wit_def
     sim
    by (rule exI[of _ inv_D], rule exI[of _ D], auto simp: DD)
  thus ?thesis unfolding \<phi>_def .
qed

lemma maximal_eigen_value_order_1: assumes ev: "eigen_value cA \<alpha>" and \<alpha>: "cmod \<alpha> = sr"
  shows "order \<alpha> (charpoly cA) = 1" 
proof -
  let ?a = "cis (arg \<alpha>)" 
  let ?p = "charpoly cA" 
  from similar_matrix_rotation[OF ev \<alpha>]
  have "similar_matrix (?a *k cA) cA" .
  from similar_matrix_charpoly[OF this] 
  have id: "charpoly (?a *k cA) = ?p" .
  have p: "?p = map_poly c (charpoly A)" 
    by (transfer_hma rule: of_real_hom.char_poly_hom)
  have a: "?a \<noteq> 0" by simp
  from order_charpoly_smult[OF this, of _ cA, unfolded id]
  have "order x ?p = order (x / ?a) ?p" for x .
  note this[of \<alpha>]
  also have "\<alpha> / ?a = sr" unfolding \<alpha>[symmetric]
    by (metis a cis_mult_cmod_id nonzero_mult_div_cancel_left)
  also have "order \<dots> ?p = 1" unfolding multiplicity_sr_1[symmetric] p
    by (rule map_poly_inj_idom_divide_hom.order_hom, unfold_locales)
  finally show ?thesis .
qed
  
lemmas pf_main =
  eigen_vector_z_sr (* sr is eigenvalue *)
  norm_sr  (* it is maximal among all complex eigenvalues *)
  sr_spectral_radius (* so it is the spectral radius *)
  z_pos    (* it's eigenvector is positive *)
  multiplicity_sr_1 (* the algebr. multiplicity is 1 *)
  nonnegative_eigenvector_has_ev_sr (* every non-negative eigenvector has sr as eigenvalue *)
  similar_matrix_rotation (* maximal eigenvectors are rotated *)
  maximal_eigen_value_order_1 (* all maximal eigenvalues have order 1 *)
 
end
end