theory Run_Pure_B

imports Definition_Pure_O2H 

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax


context pure_o2h
begin
section \<open>Defining and Representing the Adversary $B$\<close>
text \<open>For the proof of the O2H, the final adversary $B$ is restricted to information on the set $S$.
That means, $B$ takes note in a separate register of type \<open>'l\<close> weather a value in $S$ was 
queried and in which step with a unitary \<open>U_S\<close>.
\<close>



text \<open>Given the initial state \<open>init \<otimes>\<^sub>s ket 0 :: 'mem \<times> 'l\<close>, we run the adversary with counting 
by performing consecutive bit-flips. 
\<open>run_B_upto n\<close> is the function that allows the adversary \<open>n\<close> calls to the query oracle.
\<open>run_B\<close> allows exactly \<open>d\<close> query calls.
The final state $\Psi_{right}$ as in the paper is then \<open>run_B\<close>.\<close>
  (* representation of adversarial run: 
  init \<Rightarrow> UA \<Rightarrow> Uquery H \<Rightarrow> US \<Rightarrow> UA \<Rightarrow> Uquery H \<Rightarrow> US \<Rightarrow> \<dots> \<Rightarrow> Uquery H \<Rightarrow> UA *)

definition \<open>run_B_upto n = run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (US S) init_B X_for_B Y_for_B H\<close>

definition \<open>run_B = run_pure_adv d (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (US S) init_B X_for_B Y_for_B H\<close>

lemma run_B_altdef: "run_B = run_B_upto d"
  unfolding run_B_def run_B_upto_def by auto

lemma run_B_upto_I:
  "run_B_upto (Suc n) = (UA (Suc n) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (X_for_B;Y_for_B) (Uquery H) *\<^sub>V
    US S n *\<^sub>V run_B_upto n"
  unfolding run_B_upto_def by auto

(* Notation: \<Psi>_left == run_A and  \<Psi>_right == run_B *)

text \<open>This version of the O2H is only for pure states. 
Therefore, the norm of states is always $1$.\<close>


lemma norm_run_B_upto:
  assumes "n<d+1"
  shows "norm (run_B_upto n) \<le> 1"
  using assms proof (induct n)
  case 0
  then show ?case unfolding run_B_upto_def init_B_def using norm_UA_0_init 
    by (auto simp add: tensor_op_ell2 norm_tensor_ell2 norm_init)
next
  case (Suc n)
  have "norm (run_B_upto (Suc n)) \<le> norm ((UA (Suc n) \<otimes>\<^sub>o (id_cblinfun::'l update))) * 
    norm ((X_for_B;Y_for_B) (Uquery H) *\<^sub>V US S n *\<^sub>V
    run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (US S) init_B X_for_B Y_for_B H)"
    unfolding run_B_upto_def run_pure_adv.simps using norm_cblinfun by blast
  also have "\<dots> \<le> norm ((UA (Suc n) \<otimes>\<^sub>o (id_cblinfun::'l update))) * 
    norm (run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (US S) init_B X_for_B Y_for_B H)" 
    by (simp add: iso_H_B isometry_US isometry_preserves_norm norm_isometry)
  also have "\<dots> \<le> 1" using norm_UA Suc by (simp add: mult_le_one run_B_upto_def tensor_op_norm)
  finally show ?case by linarith
qed

lemma norm_run_B:
  "norm run_B \<le> 1"
  unfolding run_B_altdef using norm_run_B_upto by auto

subsection \<open>Representing the run of Adversary $B$ as a finite sum\<close>

text \<open>How the state after the $n$-th query behaves with respect to projections.\<close>

lemma run_B_upto_proj_not_valid:
  assumes "n\<le>d"
  shows "Proj_ket_set (- Collect blog) *\<^sub>V run_B_upto n = 0"
  using le0[of n] proof (induct rule: dec_induct)
  case base
  have "proj_classical_set (- Collect blog) *\<^sub>V ket empty = 0" 
    by (intro proj_classical_set_not_elem)(auto simp add: blog_empty)
  then show ?case unfolding run_B_upto_def init_B_def Proj_ket_set_def
    by (auto simp add: tensor_op_ell2)
next
  case (step m)
  have 1: "Proj_ket_set (- Collect blog) *\<^sub>V run_B_upto (Suc m) = 
    (UA (Suc m) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (X_for_B;Y_for_B) (Uquery H) *\<^sub>V
    Proj_ket_set (- Collect blog) *\<^sub>V
    US S m *\<^sub>V run_B_upto m" unfolding Proj_ket_set_def
    by (metis UqueryH_tensor_id_cblinfunB run_B_upto_I tensor_op_padding tensor_op_padding')
  have "m<d" using step assms by auto
  have "(S_embed S \<otimes>\<^sub>o (proj_classical_set (- Collect blog) o\<^sub>C\<^sub>L Ub m)) *\<^sub>V run_B_upto m = 0"
    using step(3) unfolding Proj_ket_set_def by (subst tensor_op_padding, 
        subst proj_classical_set_not_blog_Ub[OF \<open>m<d\<close>])
      (metis (no_types, lifting) cblinfun.zero_right cblinfun_apply_cblinfun_compose 
        cblinfun_compose_id_left comp_tensor_op)
  moreover have "(not_S_embed S \<otimes>\<^sub>o proj_classical_set (- Collect blog)) *\<^sub>V run_B_upto m = 0"
    using step(3) unfolding Proj_ket_set_def by (subst tensor_op_padding) auto
  ultimately have 2: "Proj_ket_set (- Collect blog) *\<^sub>V US S m *\<^sub>V run_B_upto m =
    (S_embed S \<otimes>\<^sub>o Ub m) *\<^sub>V Proj_ket_set (- Collect blog) *\<^sub>V run_B_upto m + 
    (not_S_embed S \<otimes>\<^sub>o id_cblinfun) *\<^sub>V Proj_ket_set (- Collect blog) *\<^sub>V run_B_upto m" 
    using proj_classical_set_not_blog_Ub[symmetric] step assms unfolding US_def Proj_ket_set_def
    by (auto simp add: cblinfun.add_left cblinfun.add_right comp_tensor_op
        cblinfun_apply_cblinfun_compose[symmetric] simp del: cblinfun_apply_cblinfun_compose)
  show ?case by (subst 1, subst 2) (auto simp add: step(3))
qed


lemma orth_run_B_upto:
  fixes C :: "'mem update"
  assumes y: "y \<in> has_bits {Suc m..<d}" and m: "m<d"
  shows "is_orthogonal ((C \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto m) (x \<otimes>\<^sub>s ket (list_to_l y))" 
  using le0 y proof (induction m arbitrary: C y rule: Nat.dec_induct)
  case base
  have "empty \<noteq> list_to_l y" using base.prems has_bits_def has_bits_not_empty by fastforce
  then show ?case unfolding run_B_upto_def init_B_def by (auto simp add: tensor_op_ell2)
next
  case (step n)
  define A where "A = C o\<^sub>C\<^sub>L UA (Suc n) o\<^sub>C\<^sub>L (X;Y) (Uquery H) o\<^sub>C\<^sub>L S_embed S"
  define B where "B = C o\<^sub>C\<^sub>L UA (Suc n) o\<^sub>C\<^sub>L (X;Y) (Uquery H) o\<^sub>C\<^sub>L not_S_embed S"
  then have Suc: "(C \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto (Suc n) = 
    (id_cblinfun \<otimes>\<^sub>o Ub n) *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n + 
    (B \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n" 
    apply (subst tensor_op_padding'[symmetric])
    unfolding run_B_upto_I UqueryH_tensor_id_cblinfunB US_def A_def B_def
    unfolding cblinfun.add_left cblinfun.add_right
    by (metis (mono_tags, lifting) cblinfun_apply_cblinfun_compose 
        cblinfun_compose_id_left comp_tensor_op)
  have iso: "isometry (id_cblinfun \<otimes>\<^sub>o Ub n)" by (simp add: isometry_Ub)
  have len_y: "length y = d" using step unfolding has_bits_def len_d_lists_def by auto
  have blog_y: "blog (list_to_l y)" by (simp add: blog_list_to_l len_y)
  have y_has_bits: "y \<in> has_bits {Suc n..<d}"
    by (metis Set.basic_monos(7) Suc_n_not_le_n has_bits_incl ivl_subset step(4) nat_le_linear) 
  have range: "y[d-n-1:=\<not>y!(d-n-1)] \<in> has_bits {Suc n..<d}"
    by (intro has_bits_not_elem) (use step y_has_bits m len_y len_d_lists_def in \<open>auto\<close>)
  have no_flip: "((id_cblinfun \<otimes>\<^sub>o Ub n) *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n) \<bullet>\<^sub>C
    (x \<otimes>\<^sub>s ket (list_to_l y)) = 0" (is "?left = 0")
  proof -
    have "n<d" using assms(2) step(2) by force
    have "?left = ((id_cblinfun \<otimes>\<^sub>o Ub n) *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n) \<bullet>\<^sub>C
      ((id_cblinfun \<otimes>\<^sub>o Ub n) *\<^sub>V (id_cblinfun \<otimes>\<^sub>o Ub n) *\<^sub>V (x \<otimes>\<^sub>s ket (list_to_l y)))"
      by (simp add: Ub_ket flip_flip[OF \<open>n<d\<close> blog_y] tensor_op_ell2)
    also have "\<dots> = ((A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n) \<bullet>\<^sub>C 
      ((id_cblinfun \<otimes>\<^sub>o Ub n) *\<^sub>V (x \<otimes>\<^sub>s ket (list_to_l y)))"
      using isometry_cinner_both_sides[OF iso] by auto
    also have "\<dots> = ((A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n) \<bullet>\<^sub>C 
      (x \<otimes>\<^sub>s ket (flip n (list_to_l y)))" by (simp add: Ub_ket tensor_op_ell2)
    also have "\<dots> = ((A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto n) \<bullet>\<^sub>C 
      (x \<otimes>\<^sub>s ket (list_to_l (y[d-n-1:=\<not>y!(d-n-1)])))" 
      using \<open>n < d\<close> flip_list_to_l le_eq_less_or_eq len_y by presburger
    also have "\<dots> = 0" by (intro step(3)) (rule range)
    finally show ?thesis by auto
  qed
  show ?case using y_has_bits unfolding Suc cinner_add_left 
    by (subst no_flip, subst step(3))(use step in \<open>auto\<close>)
qed

lemma orth_run_B_upto_ket:
  assumes y: "y \<in> has_bits {Suc m..<d}" and Sucm: "Suc m<d"
  shows "is_orthogonal (run_B_upto m) (x \<otimes>\<^sub>s ket (list_to_l y))"
proof -
  have m: "m<d" using assms(2) by auto
  have id: "run_B_upto m = (id_cblinfun \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto m" by auto
  then show ?thesis
    by (subst id, intro orth_run_B_upto[OF _ m]) (use assms in \<open>auto\<close>)
qed

lemma orth_run_B_upto_flip:
  assumes y: "y \<in> has_bits {Suc m..<d}" and Sucm: "Suc m<d"
  shows "is_orthogonal (run_B_upto m) (x \<otimes>\<^sub>s ket (flip m (list_to_l y)))"
proof -
  have len_d: "y \<in> len_d_lists" using y unfolding has_bits_def by auto
  then have m: "m < length y" by (simp add: Suc_lessD Sucm len_d_lists_def) 
  have yd: "length y \<le> d" using y has_bits_def len_d_lists_def by auto
  have id: "run_B_upto m = (id_cblinfun \<otimes>\<^sub>o id_cblinfun) *\<^sub>V run_B_upto m" by auto
  have range: "y[d - m - 1 := \<not> y ! (d - m - 1)] \<in> has_bits {Suc m..<d}"
    by (intro has_bits_not_elem) (use y Sucm len_d in \<open>auto\<close>)
  then show ?thesis
    by (subst flip_list_to_l[OF m yd], subst id, intro orth_run_B_upto) 
      (use len_d len_d_lists_def Sucm in \<open>auto\<close>)
qed


lemma run_B_upto_proj_over:
  assumes "n\<le>d"
  shows "Proj_ket_set (list_to_l ` has_bits {n..<d}) *\<^sub>V run_B_upto n = 0"
proof (cases "n=d")
  case True then show ?thesis unfolding \<open>n=d\<close> Proj_ket_set_def proj_classical_set_def by auto
next
  case False 
  then have "n<d" using assms by auto
  show ?thesis
    using le0[of n] proof (induct rule: dec_induct)
    case base
    have "empty \<notin> list_to_l ` has_bits {0..<d}" using has_bits_def has_bits_not_empty by fastforce
    then have "proj_classical_set (list_to_l ` has_bits {0..<d}) *\<^sub>V ket (empty) = 0" 
      by (intro proj_classical_set_not_elem) auto
    then show ?case unfolding run_B_upto_def init_B_def Proj_ket_set_def
      by (auto simp add: tensor_op_ell2)
  next
    case (step m)
    then have "m<d" using assms by auto
    then have "Suc m\<le>d" by auto
    have "Suc m < d" using \<open>n < d\<close> step(2) by linarith
    have 1: "Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto (Suc m) = 
      (UA (Suc m) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (X_for_B;Y_for_B) (Uquery H) *\<^sub>V
      Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V
      US S m *\<^sub>V run_B_upto m" unfolding Proj_ket_set_def
      by (smt (verit, del_insts) UqueryH_tensor_id_cblinfunB cblinfun_apply_cblinfun_compose 
          cblinfun_compose_id_left cblinfun_compose_id_right comp_tensor_op run_B_upto_def 
          run_pure_adv.simps(2))
    have 2: "Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V US S m *\<^sub>V run_B_upto m =
      (S_embed S \<otimes>\<^sub>o Ub m) *\<^sub>V Proj_ket_set (flip m ` list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto m + 
      (not_S_embed S \<otimes>\<^sub>o id_cblinfun) *\<^sub>V Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto m" 
      using proj_classical_set_over_Ub[OF \<open>Suc m\<le>d\<close>, symmetric] step assms
      unfolding US_def Proj_ket_set_def 
      by (auto simp add: cblinfun.add_left cblinfun.add_right comp_tensor_op
          cblinfun_apply_cblinfun_compose[symmetric] simp del: cblinfun_apply_cblinfun_compose)
    have "Proj_ket_set (flip m ` list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto m = 0"
    proof -
      have "Proj_ket_set (flip m ` list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto m = 
        Proj (\<top> \<otimes>\<^sub>S ccspan (ket ` flip m ` list_to_l ` has_bits {Suc m..<d})) *\<^sub>V run_B_upto m"
        by (simp add: Proj_on_own_range is_Proj_tensor_op proj_classical_set_def 
            tensor_ccsubspace_via_Proj Proj_ket_set_def)
      also have "\<dots> = 0" by (intro Proj_0_compl, unfold ccspan_UNIV[symmetric],
            subst tensor_ccsubspace_ccspan,intro mem_ortho_ccspanI)
          (auto intro!: orth_run_B_upto_flip simp add: \<open>Suc m<d\<close>)
      finally show ?thesis by auto
    qed
    then have 3: "(S_embed S \<otimes>\<^sub>o Ub m) *\<^sub>V Proj_ket_set (flip m ` list_to_l ` has_bits {Suc m..<d})
       *\<^sub>V run_B_upto m = 0"
      by (metis (no_types, lifting) cblinfun.real.zero_right cblinfun_apply_cblinfun_compose)
    have "Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto m = 0"
    proof -
      have "Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V run_B_upto m = 
        Proj (\<top> \<otimes>\<^sub>S ccspan (ket ` list_to_l ` has_bits {Suc m..<d})) *\<^sub>V run_B_upto m"
        by (simp add: Proj_on_own_range is_Proj_tensor_op proj_classical_set_def 
            tensor_ccsubspace_via_Proj Proj_ket_set_def)
      also have "\<dots> = 0" by (intro Proj_0_compl, unfold ccspan_UNIV[symmetric],
            subst tensor_ccsubspace_ccspan,intro mem_ortho_ccspanI)
          (auto intro!: orth_run_B_upto_ket simp add: \<open>Suc m<d\<close>)
      finally show ?thesis by auto
    qed
    then have 4: "(not_S_embed S \<otimes>\<^sub>o id_cblinfun) *\<^sub>V Proj_ket_set (list_to_l ` has_bits {Suc m..<d}) *\<^sub>V
       run_B_upto m = 0" by (subst tensor_op_padding) auto
    show ?case by (subst 1, subst 2, subst 3, subst 4) auto
  qed
qed


text \<open>How \<open>\<Psi>s\<close> relate to \<open>run_B\<close>. We can write \<open>run_B\<close> as a sum counting over all valid
ket states in the counting register.\<close>

lemma not_empty_list_nth:
  assumes "x\<in>len_d_lists"
  shows "x \<noteq> empty_list \<longleftrightarrow> (\<exists>i<d. x!i)"
  using assms unfolding len_d_lists_def empty_list_def by (simp add: list_eq_iff_nth_eq)

text \<open>First we show the mere existence of such a form.\<close>
lemma run_B_upto_sum:
  assumes "n<d"
  shows "\<exists>v. run_B_upto n = (\<Sum>i\<in>has_bits_upto n. v i \<otimes>\<^sub>s ket (list_to_l i))"
  using le0[of n] assms proof (induct n rule: Nat.dec_induct)
  case base
  have "\<exists>xa\<in>{0..<d}. x ! (d - Suc xa)" 
    if "x \<noteq> empty_list" "x \<in> len_d_lists" for x :: "bool list"
    using not_empty_list_nth[OF that(2)] that(1) by (metis Suc_pred atLeast0LessThan 
        diff_diff_cancel diff_less_Suc lessThan_iff less_or_eq_imp_le not_less_eq zero_less_diff)
  then have rew: "has_bits_upto 0 = {empty_list}"
    unfolding has_bits_upto_def has_bits_def len_d_lists_def empty_list_def by auto
  show ?case by (subst rew, unfold run_B_upto_def init_B_def)
      (auto simp add: empty_list_to_l tensor_op_ell2)
next
  case (step n)
  let ?upto_n = "has_bits_upto n"
  let ?upto_Suc_n = "has_bits_upto (Suc n)"
  let ?only_n = "has_bits {n} - has_bits{Suc n..<d}"
  have [simp]: "n<d" by(rule Suc_lessD[OF step(4)])
  from step obtain v where v: "run_B_upto n = 
    (\<Sum>i\<in>?upto_n. v i \<otimes>\<^sub>s ket (list_to_l i))"
    using Suc_lessD by presburger
  define v1 where "v1 i = not_S_embed S *\<^sub>V (v i)" for i
  define v2 where "v2 i = S_embed S *\<^sub>V (v i)" for i
  have US_ket: "US S n *\<^sub>V (v i) \<otimes>\<^sub>s ket (list_to_l i) = 
    v1 i \<otimes>\<^sub>s ket (list_to_l i) + v2 i \<otimes>\<^sub>s ket (flip n (list_to_l i))" 
    if "i\<in>?upto_n" for i unfolding US_ket_only01 
    by (auto simp add: that v1_def v2_def)
  define v' where "v' i = (if i \<in> ?upto_n 
    then ((UA (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v1 i) 
    else ((UA (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v2 (i[d-n-1:= \<not>i!(d-n-1)])))" for i
  have "(\<Sum>i\<in>?upto_n. 
    ((UA (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v1 i) \<otimes>\<^sub>s ket (list_to_l i) +
    ((UA (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v2 i) \<otimes>\<^sub>s ket (flip n (list_to_l i))) =
    (\<Sum>i\<in>?upto_Suc_n. v' i \<otimes>\<^sub>s ket (list_to_l i))" (is "?l = ?r")
  proof -
    have left: "?l = (\<Sum>i\<in>?upto_n. ((UA (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v1 i) \<otimes>\<^sub>s ket (list_to_l i)) +
      (\<Sum>i\<in>?upto_n. (UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v2 i) \<otimes>\<^sub>s ket (flip n (list_to_l i)))"
      (is "?l = ?fst + ?snd" )
      by (subst sum.distrib)(auto intro!: sum.cong)
    have fst: "?fst = (\<Sum>i\<in>?upto_n. v' i \<otimes>\<^sub>s ket (list_to_l i))" unfolding v'_def by auto

    let ?reindex = "(\<lambda>k. k[d-n-1:= \<not>k!(d-n-1)])"
    have reindex_idem: "?reindex (?reindex l) = l" if "l\<in>len_d_lists" for l
      by (smt (verit, best) list_update_id list_update_overwrite)
    have snd': "?snd = (\<Sum>i\<in>?reindex` ?upto_n. 
      ((UA (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V v2 (?reindex i)) \<otimes>\<^sub>s 
      ket (list_to_l i))"
    proof (subst sum.reindex, goal_cases)
      case 1
      then show ?case unfolding has_bits_upto_def  
        by (metis (no_types, lifting) inj_on_def inj_on_diff reindex_idem)
    next
      case 2
      then show ?case 
      proof (intro sum.cong, goal_cases)
        case (2 x)
        have one: "n < length x" using \<open>n<d\<close> 2 has_bits_upto_def len_d_lists_def by auto
        have two: "length x \<le> d" using 2 len_d_lists_def has_bits_upto_def by auto
        have three: "x \<in> len_d_lists" using 2 has_bits_upto_def by auto
        show ?case by (subst flip_list_to_l[OF one two]) 
            (use reindex_idem[OF three] three in \<open>auto simp add:  len_d_lists_def\<close>)
      qed simp
    qed
    have set_rew: "?reindex ` ?upto_n = ?only_n"
    proof -
      have "x\<in>?only_n" if "x\<in>?reindex ` ?upto_n" for x
      proof -
        have len_d_x: "x \<in> len_d_lists" using that unfolding len_d_lists_def has_bits_upto_def by auto
        obtain x' where x':"x = ?reindex x' " "x'\<in>?upto_n" using \<open>x \<in> ?reindex ` ?upto_n\<close> by blast
        then have len_x': "length x' = d" unfolding len_d_lists_def has_bits_upto_def by auto
        have "\<not> x'!(d-n-1)" by (intro has_bits_upto_elem [OF x'(2)])  auto
        then have "x!(d-n-1)" unfolding x' by (subst nth_list_update_eq)(auto simp add: d_gr_0 len_x')
        then have a: "x\<in>has_bits {n}" unfolding has_bits_def using len_d_x by auto
        have "x' \<in> has_bits_upto (Suc n)" using has_bits_split_Suc has_bits_upto_def x'(2) by force
        then have "\<not> x'!(d-i-1)" if "i\<in>{Suc n..<d}" for i 
          by (intro has_bits_elem[of x' "{Suc n..<d}"], unfold has_bits_upto_def[symmetric]) 
            (use that in \<open>auto\<close>)
        then have "\<forall>i\<in>{Suc n..<d}. \<not> x!(d-i-1)" using x'(1) by fastforce
        then have b: "x\<notin>has_bits {Suc n..<d}" by (simp add: has_bits_def)
        show ?thesis using a b by auto
      qed
      moreover have"x\<in>?reindex ` ?upto_n" if "x\<in>?only_n" for x 
      proof -
        have len_d_x: "x \<in> len_d_lists" using that unfolding has_bits_def len_d_lists_def by auto
        define x' where x':"x' = ?reindex x " 
        then have "x'\<in>?reindex ` ?only_n" using \<open>x \<in> ?only_n\<close> reindex_idem by auto
        then have len_d_x': "x' \<in> len_d_lists" using that 
          unfolding has_bits_def len_d_lists_def by auto
        have "\<not>x'!(d-i-1)" if "i\<in>{n..<d}" for i 
        proof (cases "i = n")
          case True
          have ineq: "d - n - 1 < length x" using len_d_x len_d_lists_def by (simp add: d_gr_0)
          have "x\<in>has_bits {n}" using \<open>x \<in> ?only_n\<close> by blast
          then have "x ! (d-n-1)" unfolding has_bits_def by auto 
          then show ?thesis unfolding True x' by (subst nth_list_update_eq) (use ineq in \<open>auto\<close>)
        next
          case False
          have set: "i\<in>{Suc n..<d}" using False \<open>i\<in>{n..<d}\<close> by auto
          have "x\<notin>has_bits {Suc n..<d}" using \<open>x \<in> ?only_n\<close> by auto
          then have "\<not>x!(d-i-1)" using has_bits_def set using len_d_x by blast
          moreover have "x!(d-i-1) = x'!(d-i-1)" using False \<open>i\<in>{n..<d}\<close> using x' by force
          ultimately show ?thesis by auto
        qed
        then have "x'\<notin> has_bits {n..<d}" by (simp add: has_bits_def)
        then have "x'\<in>?upto_n" using len_d_x' has_bits_upto_def by auto
        then show ?thesis using x'
          by (metis (no_types, lifting) image_iff len_d_x reindex_idem)
      qed
      ultimately show ?thesis by auto
    qed
    have snd: "?snd = (\<Sum>i\<in>?only_n. v' i \<otimes>\<^sub>s ket (list_to_l i))" 
      unfolding v'_def snd' using set_rew 
      by (auto intro!: sum.cong simp add: has_bits_upto_def has_bits_split_Suc)
    have incl: "?only_n \<subseteq> has_bits {n..<d}" 
      using has_bits_incl[of "{n}" "{n..<d}"] by (auto)
    have union: "?upto_n \<union> ?only_n = ?upto_Suc_n"
      unfolding has_bits_split_Suc[OF \<open>n<d\<close>] has_bits_upto_def 
      using has_bits_in_len_d_lists[of "{n}"] by blast
    show ?thesis unfolding left fst snd
      by (subst sum.union_disjoint[symmetric])(use incl union has_bits_upto_def in \<open>auto\<close>)
  qed
  then show ?case unfolding run_B_upto_def unfolding run_pure_adv.simps 
    by (fold run_B_upto_def, subst v)
      (auto simp add: cblinfun.sum_right tensor_op_ell2 US_ket_only01 
        UqueryH_tensor_id_cblinfunB cblinfun.add_right US_ket nth_append v1_def v2_def)
qed


text \<open>As a shorthand, we define \<open>Proj_ket_upto\<close>.\<close>


lemma run_B_projection:
  assumes "n<d"
  shows "Proj_ket_upto (has_bits_upto n) *\<^sub>V run_B_upto n = run_B_upto n"
proof -
  obtain v where v: "run_B_upto n = (\<Sum>i\<in>has_bits_upto n. v i \<otimes>\<^sub>s ket (list_to_l i))"
    using run_B_upto_sum assms by auto 
  show ?thesis unfolding v by (subst cblinfun.sum_right, intro sum.cong, simp, 
        intro Proj_ket_upto_vec) fastforce
qed



text \<open>How \<open>\<Psi>s\<close> relate to \<open>run_B\<close>.\<close>

lemma run_B_upto_split:
  assumes "n\<le>d"
  shows "run_B_upto n = (\<Sum>i\<in>has_bits_upto n. \<Psi>s (list_to_l i) (run_B_upto n) \<otimes>\<^sub>s ket (list_to_l i))"
proof -
  have neg_set: "- list_to_l ` (has_bits_upto n) = 
    list_to_l ` has_bits {n..<d} \<union> - Collect blog" unfolding has_bits_upto_def
    by (smt (verit, del_insts) Compl_Diff_eq Diff_subset Un_commute inj_list_to_l 
        inj_on_image_set_diff has_bits_in_len_d_lists surj_list_to_l)
  have "run_B_upto n = id_cblinfun *\<^sub>V run_B_upto n" by auto
  also have "\<dots> = (\<Sum>i\<in>list_to_l ` has_bits_upto n. 
    (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)) *\<^sub>V run_B_upto n + 
    Proj_ket_set (- list_to_l ` has_bits_upto n) *\<^sub>V run_B_upto n" 
    by (subst id_cblinfun_tensor_split_finite[of "list_to_l ` has_bits_upto n"])
      (auto simp add: cblinfun.add_left) 
  also have "\<dots> = (\<Sum>i\<in>list_to_l ` has_bits_upto n. 
    (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)) *\<^sub>V run_B_upto n + 
    Proj_ket_set (list_to_l ` has_bits {n..<d}) *\<^sub>V run_B_upto n" 
  proof -
    have orth: "is_orthogonal x y" 
      if ass: "x \<in> ket ` list_to_l ` has_bits {n..<d}" "y \<in> ket ` (- Collect blog)" for x y
    proof -
      obtain j where j: "j\<in>has_bits {n..<d}" and x: "x = ket (list_to_l j)" using ass(1) by auto
      then have valid: "blog (list_to_l j)" 
        by (metis Set.basic_monos(7) has_bits_in_len_d_lists imageI mem_Collect_eq surj_list_to_l)
      obtain k where k: "\<not> blog k" and y: "y = ket k" using ass(2) by auto
      show "is_orthogonal x y" unfolding x y by (subst orthogonal_ket)(use k valid in \<open>blast\<close>)
    qed
    then show ?thesis using run_B_upto_proj_not_valid unfolding neg_set Proj_ket_set_def 
      by (subst proj_classical_set_union[OF orth]) 
        (auto simp add: tensor_op_right_add cblinfun.add_left assms ) 
  qed
  also have "\<dots> = (\<Sum>i\<in>has_bits_upto n. (tensor_ell2_right (ket (list_to_l i))) o\<^sub>C\<^sub>L 
    (tensor_ell2_right (ket (list_to_l i))*)) *\<^sub>V run_B_upto n" 
    unfolding run_B_upto_proj_over[OF \<open>n\<le>d\<close>] proof (subst sum.reindex, goal_cases) 
    case 1 show ?case using bij_betw_imp_inj_on[OF bij_betw_list_to_l]
      by (simp add: has_bits_upto_def inj_on_diff)
  qed (auto simp add: Proj_ket_set_def)
  finally have *: "run_B_upto n = 
    (\<Sum>i\<in>has_bits_upto n. (tensor_ell2_right (ket (list_to_l i))* *\<^sub>V run_B_upto n) \<otimes>\<^sub>s ket (list_to_l i))"
    by (smt (verit, ccfv_SIG) cblinfun.sum_left cblinfun_apply_cblinfun_compose sum.cong 
        tensor_ell2_right.rep_eq)
  show ?thesis unfolding \<Psi>s_def by (subst *)(use lessThan_Suc_atMost in \<open>auto\<close>)
qed



lemma run_B_split:
  "run_B = (\<Sum>i\<in>len_d_lists. \<Psi>s (list_to_l i) run_B \<otimes>\<^sub>s (ket (list_to_l i)))"
  unfolding run_B_altdef has_bits_upto_d[symmetric] by (subst run_B_upto_split[symmetric]) auto

end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end