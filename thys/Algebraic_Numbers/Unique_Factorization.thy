theory Unique_Factorization
  imports
    "../Polynomial_Interpolation/Ring_Hom_Poly"
    "../Polynomial_Factorization/Polynomial_Divisibility"
    "~~/src/HOL/Library/Permutations" 
    "~~/src/HOL/Computational_Algebra/Euclidean_Algorithm"
    "~~/src/HOL/Algebra/Divisibility"
    "../Containers/Containers_Auxiliary" (* only for a lemma *)
begin
hide_const(open) prime
hide_fact(open) Divisibility.irreducibleI
hide_fact(open) Divisibility.irreducibleD
hide_fact(open) Divisibility.irreducibleE

(* TODO: move or...? *)
lemma dvd_rewrites: "dvd.dvd (op *) = op dvd" by (unfold dvd.dvd_def dvd_def, rule)

(* put in the class context so that it can be used inside the context. *)
lemma (in comm_monoid_mult) prod_mset_prod_list: "prod_mset (mset xs) = prod_list xs"
  by (induct xs) auto


subsection {* Interfacing UFD properties *}
hide_const (open) Divisibility.irreducible

context comm_semiring_1
begin
lemma irreducibleE[elim]:
  assumes "irreducible p"
      and "p \<noteq> 0 \<Longrightarrow> \<not> p dvd 1 \<Longrightarrow> (\<And>a b. p = a * b \<Longrightarrow> a dvd 1 \<or> b dvd 1) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: irreducible_def)

lemma not_irreducibleE:
  assumes "\<not> irreducible x"
      and "x = 0 \<Longrightarrow> thesis"
      and "x dvd 1 \<Longrightarrow> thesis"
      and "\<And>a b. x = a * b \<Longrightarrow> \<not> a dvd 1 \<Longrightarrow> \<not> b dvd 1 \<Longrightarrow> thesis"
  shows thesis using assms unfolding irreducible_def by auto

lemma prime_elem_dvd_prod_list:
  assumes p: "prime_elem p" and pA: "p dvd prod_list A" shows "\<exists>a \<in> set A. p dvd a"
proof(insert pA, induct A)
  case Nil
  with p show ?case by (simp add: prime_elem_not_unit)
next
  case (Cons a A)
  then show ?case by (auto simp: prime_elem_dvd_mult_iff[OF p])
qed

lemma prime_elem_dvd_prod_mset:
  assumes p: "prime_elem p" and pA: "p dvd prod_mset A" shows "\<exists>a \<in># A. p dvd a"
proof(insert pA, induct A)
  case empty
  with p show ?case by (simp add: prime_elem_not_unit)
next
  case (add a A)
  then show ?case by (auto simp: prime_elem_dvd_mult_iff[OF p])
qed

lemma mult_unit_dvd_iff[simp]:
  assumes "b dvd 1"
  shows "a * b dvd c \<longleftrightarrow> a dvd c"
proof
  assume "a * b dvd c"
  with assms show "a dvd c" using dvd_mult_left[of a b c] by simp
next
  assume "a dvd c"
  with assms mult_dvd_mono show "a * b dvd c" by fastforce
qed

lemma mult_unit_dvd_iff'[simp]: "a dvd 1 \<Longrightarrow> (a * b) dvd c \<longleftrightarrow> b dvd c"
  using mult_unit_dvd_iff [of a b c] by (simp add: ac_simps)

lemma irreducibleD':
  assumes "irreducible a" "b dvd a"
  shows   "a dvd b \<or> b dvd 1"
proof -
  from assms obtain c where c: "a = b * c" by (elim dvdE)
  from irreducibleD[OF assms(1) this] have "b dvd 1 \<or> c dvd 1" .
  thus ?thesis by (auto simp: c)
qed

lemma unit_prod [intro]:
  shows "a dvd 1 \<Longrightarrow> b dvd 1 \<Longrightarrow> (a * b) dvd 1"
  by (subst mult_1_left [of 1, symmetric]) (rule mult_dvd_mono)

lemma is_unit_mult_iff[simp]:
  shows "(a * b) dvd 1 \<longleftrightarrow> a dvd 1 \<and> b dvd 1"
  by (auto dest: dvd_mult_left dvd_mult_right)
end

(* coprime shouldn't need "gcd"... *)
hide_const(open) coprime

context comm_monoid_mult begin

  definition coprime where "coprime p q \<equiv> \<forall>r. r dvd p \<longrightarrow> r dvd q \<longrightarrow> r dvd 1"

  lemma coprimeI:
    assumes "\<And>r. r dvd p \<Longrightarrow> r dvd q \<Longrightarrow> r dvd 1"
    shows "coprime p q" using assms by (auto simp: coprime_def)

  lemma coprimeE:
    assumes "coprime p q"
        and "(\<And>r. r dvd p \<Longrightarrow> r dvd q \<Longrightarrow> r dvd 1) \<Longrightarrow> thesis"
    shows thesis using assms by (auto simp: coprime_def)

  lemma coprime_commute[ac_simps]: "coprime p q \<longleftrightarrow> coprime q p" unfolding coprime_def by auto

  lemma not_coprime_iff_common_factor:
    "\<not> coprime p q \<longleftrightarrow> (\<exists>r. r dvd p \<and> r dvd q \<and> \<not> r dvd 1)"
    unfolding coprime_def by auto

end

context comm_semiring_isom begin
  lemma coprime_hom[simp]: "coprime (hom x) y' \<longleftrightarrow> coprime x (Hilbert_Choice.inv hom y')"
  proof-
    show ?thesis by (unfold coprime_def, fold ball_UNIV, subst surj[symmetric], simp)
  qed
  lemma coprime_inv_hom[simp]: "coprime (Hilbert_Choice.inv hom x') y \<longleftrightarrow> coprime x' (hom y)"
  proof-
    interpret inv: comm_semiring_isom "Hilbert_Choice.inv hom"..
    show ?thesis by simp
  qed
end

lemma(in semiring_gcd) coprime_iff_gcd_one[simp,code]:
  "coprime = (\<lambda>x y. gcd x y = 1)" using coprime by (intro ext, auto simp: coprime_def)

lemma(in comm_semiring_1) coprime_0[simp]: "coprime p 0 \<longleftrightarrow> p dvd 1" "coprime 0 p \<longleftrightarrow> p dvd 1"
  by (auto intro: coprimeI elim: coprimeE dest: dvd_trans)

lemma (in semidom) prod_list_zero_iff[simp]: "prod_list xs = 0 \<longleftrightarrow> 0 \<in> set xs" by (induction xs, auto)

context idom
begin

  text \<open>
    Following lemmas are adapted and generalized so that they don't use "algebraic" classes.
  \<close>

  lemma dvd_times_left_cancel_iff [simp]:
    assumes "a \<noteq> 0"
    shows "a * b dvd a * c \<longleftrightarrow> b dvd c"
      (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then obtain d where "a * c = a * b * d" ..
    with assms have "c = b * d" by (auto simp add: ac_simps)
    then show ?rhs ..
  next
    assume ?rhs
    then obtain d where "c = b * d" ..
    then have "a * c = a * b * d" by (simp add: ac_simps)
    then show ?lhs ..
  qed

  lemma dvd_times_right_cancel_iff [simp]:
    assumes "a \<noteq> 0"
    shows "b * a dvd c * a \<longleftrightarrow> b dvd c"
    using dvd_times_left_cancel_iff [of a b c] assms by (simp add: ac_simps)


  lemma irreducibleI':
    assumes "a \<noteq> 0" "\<not> a dvd 1" "\<And>b. b dvd a \<Longrightarrow> a dvd b \<or> b dvd 1"
    shows   "irreducible a"
  proof (rule irreducibleI)
    fix b c assume a_eq: "a = b * c"
    hence "a dvd b \<or> b dvd 1" by (intro assms) simp_all
    thus "b dvd 1 \<or> c dvd 1"
    proof
      assume "a dvd b"
      hence "b * c dvd b * 1" by (simp add: a_eq)
      moreover from \<open>a \<noteq> 0\<close> a_eq have "b \<noteq> 0" by auto
      ultimately show ?thesis using dvd_times_left_cancel_iff by fastforce
    qed blast
  qed (simp_all add: assms(1,2))

  lemma irreducible_altdef:
    shows "irreducible x \<longleftrightarrow> x \<noteq> 0 \<and> \<not> x dvd 1 \<and> (\<forall>b. b dvd x \<longrightarrow> x dvd b \<or> b dvd 1)"
    using irreducibleI'[of x] irreducibleD'[of x] irreducible_not_unit[of x] by auto

  lemma dvd_mult_unit_iff:
    assumes b: "b dvd 1"
    shows "a dvd c * b \<longleftrightarrow> a dvd c"
  proof-
    from b obtain b' where 1: "b * b' = 1" by (elim dvdE, auto)
    then have b0: "b \<noteq> 0" by auto
    from 1 have "a = (a * b') * b" by (simp add: ac_simps)
    also have "\<dots> dvd c * b \<longleftrightarrow> a * b' dvd c" using b0 by auto
    finally show ?thesis by (auto intro: dvd_mult_left)
  qed

  lemma dvd_mult_unit_iff': "b dvd 1 \<Longrightarrow> a dvd b * c \<longleftrightarrow> a dvd c"
    using dvd_mult_unit_iff [of b a c] by (simp add: ac_simps)

  lemma irreducible_mult_unit_left:
    shows "a dvd 1 \<Longrightarrow> irreducible (a * p) \<longleftrightarrow> irreducible p"
    by (auto simp: irreducible_altdef mult.commute[of a] dvd_mult_unit_iff)

  lemma irreducible_mult_unit_right:
    shows "a dvd 1 \<Longrightarrow> irreducible (p * a) \<longleftrightarrow> irreducible p"
    by (auto simp: irreducible_altdef mult.commute[of a] dvd_mult_unit_iff)

  lemma prime_elem_imp_irreducible:
    assumes "prime_elem p"
    shows   "irreducible p"
  proof (rule irreducibleI)
    fix a b
    assume p_eq: "p = a * b"
    with assms have nz: "a \<noteq> 0" "b \<noteq> 0" by auto
    from p_eq have "p dvd a * b" by simp
    with \<open>prime_elem p\<close> have "p dvd a \<or> p dvd b" by (rule prime_elem_dvd_multD)
    with \<open>p = a * b\<close> have "a * b dvd 1 * b \<or> a * b dvd a * 1" by auto
    thus "a dvd 1 \<or> b dvd 1"
      by (simp only: dvd_times_left_cancel_iff[OF nz(1)] dvd_times_right_cancel_iff[OF nz(2)])
  qed (insert assms, simp_all add: prime_elem_def)

  lemma unit_imp_dvd [dest]: "b dvd 1 \<Longrightarrow> b dvd a"
    by (rule dvd_trans [of _ 1]) simp_all

  lemma unit_mult_left_cancel: "a dvd 1 \<Longrightarrow> a * b = a * c \<longleftrightarrow> b = c"
    using mult_cancel_left [of a b c] by auto

  lemma unit_mult_right_cancel: "a dvd 1 \<Longrightarrow> b * a = c * a \<longleftrightarrow> b = c"
    using unit_mult_left_cancel [of a b c] by (auto simp add: ac_simps)

end

subsubsection {* Original part *}

lemma dvd_dvd_imp_smult:
  fixes p q :: "'a :: idom poly"
  assumes pq: "p dvd q" and qp: "q dvd p" shows "\<exists>c. p = smult c q"
proof (cases "p = 0")
  case True then show ?thesis by auto
next
  case False
  from qp obtain r where r: "p = q * r" by (elim dvdE, auto)
  with False qp have r0: "r \<noteq> 0" and q0: "q \<noteq> 0" by auto
  with divides_degree[OF pq] divides_degree[OF qp] False
  have "degree p = degree q" by auto
  with r degree_mult_eq[OF q0 r0] have "degree r = 0" by auto
  from degree_0_id[OF this] obtain c where "r = [:c:]" by metis
  from r[unfolded this] show ?thesis by auto
qed

lemma dvd_const:
  assumes pq: "(p::'a::semidom poly) dvd q" and q0: "q \<noteq> 0" and degq: "degree q = 0"
  shows "degree p = 0"
proof-
  from dvdE[OF pq] obtain r where *: "q = p * r".
  with q0 have "p \<noteq> 0" "r \<noteq> 0" by auto
  from degree_mult_eq[OF this] degq * show "degree p = 0" by auto
qed

context Rings.dvd begin
  abbreviation ddvd (infix "ddvd" 40) where "x ddvd y \<equiv> x dvd y \<and> y dvd x"
  lemma ddvd_sym[sym]: "x ddvd y \<Longrightarrow> y ddvd x" by auto
end

context comm_monoid_mult begin
  lemma ddvd_trans[trans]: "x ddvd y \<Longrightarrow> y ddvd z \<Longrightarrow> x ddvd z" using dvd_trans by auto
  lemma ddvd_transp: "transp (op ddvd)" by (intro transpI, fact ddvd_trans)
end

context comm_semiring_1 begin

definition mset_factors where "mset_factors F p \<equiv>
  F \<noteq> {#} \<and> (\<forall>f. f \<in># F \<longrightarrow> irreducible f) \<and> p = prod_mset F"

lemma mset_factorsI[intro!]:
  assumes "\<And>f. f \<in># F \<Longrightarrow> irreducible f" and "F \<noteq> {#}" and "prod_mset F = p"
  shows "mset_factors F p"
  unfolding mset_factors_def using assms by auto

lemma mset_factorsD:
  assumes "mset_factors F p"
  shows "f \<in># F \<Longrightarrow> irreducible f" and "F \<noteq> {#}" and "prod_mset F = p"
  using assms[unfolded mset_factors_def] by auto

lemma mset_factorsE[elim]:
  assumes "mset_factors F p"
      and "(\<And>f. f \<in># F \<Longrightarrow> irreducible f) \<Longrightarrow> F \<noteq> {#} \<Longrightarrow> prod_mset F = p \<Longrightarrow> thesis"
  shows thesis
  using assms[unfolded mset_factors_def] by auto

lemma mset_factors_imp_not_is_unit:
  assumes "mset_factors F p"
  shows "\<not> p dvd 1"
proof(cases F)
  case empty with assms show ?thesis by auto
next
  case (add f F)
  with assms have "\<not> f dvd 1" "p = f * prod_mset F" by (auto intro!: irreducible_not_unit)
  then show ?thesis by auto
qed

definition primitive_poly where "primitive_poly f \<equiv> \<forall>d. (\<forall>i. d dvd coeff f i) \<longrightarrow> d dvd 1"

end

lemma(in semidom) mset_factors_imp_nonzero:
  assumes "mset_factors F p"
  shows "p \<noteq> 0"
proof
  assume "p = 0"
  moreover from assms have "prod_mset F = p" by auto
  ultimately obtain f where "f \<in># F" "f = 0" by auto
  with assms show False by auto
qed

class ufd = idom +
  assumes mset_factors_exist: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<not> x dvd 1 \<Longrightarrow> \<exists>F. mset_factors F x"
    and mset_factors_unique: "\<And>x F G. x \<noteq> 0 \<Longrightarrow> mset_factors F x \<Longrightarrow> mset_factors G x \<Longrightarrow> rel_mset (op ddvd) F G"

subsubsection {* Connecting to HOL/Divisibility *}

context comm_semiring_1 begin

  abbreviation "mk_monoid \<equiv> \<lparr>carrier = UNIV - {0}, mult = op *, one = 1\<rparr>"

  lemma carrier_0[simp]: "x \<in> carrier mk_monoid \<longleftrightarrow> x \<noteq> 0" by auto

  lemmas mk_monoid_simps = carrier_0 monoid.simps

  abbreviation irred where "irred \<equiv> Divisibility.irreducible mk_monoid"
  abbreviation factor where "factor \<equiv> Divisibility.factor mk_monoid"
  abbreviation factors where "factors \<equiv> Divisibility.factors mk_monoid"
  abbreviation properfactor where "properfactor \<equiv> Divisibility.properfactor mk_monoid"

  lemma factors: "factors fs y \<longleftrightarrow> prod_list fs = y \<and> Ball (set fs) irred"
  proof -
    have "prod_list fs = foldr op * fs 1" by (induct fs, auto)
    thus ?thesis unfolding factors_def by auto
  qed

  lemma factor: "factor x y \<longleftrightarrow> (\<exists>z. z \<noteq> 0 \<and> x * z = y)" unfolding factor_def by auto

  lemma properfactor_nz:
    shows "(y :: 'a) \<noteq> 0 \<Longrightarrow> properfactor x y \<longleftrightarrow> x dvd y \<and> \<not> y dvd x"
    by (auto simp: properfactor_def factor_def dvd_def)

  lemma mem_Units[simp]: "y \<in> Units mk_monoid \<longleftrightarrow> y dvd 1"
    unfolding dvd_def Units_def by (auto simp: ac_simps)

end

(* a variant for "right" *)
lemma ex_mset_zip_right:
  assumes "length xs = length ys" "mset ys' = mset ys"
  shows "\<exists>xs'. length ys' = length xs' \<and> mset (zip xs' ys') = mset (zip xs ys)"
using assms
proof (induct xs ys arbitrary: ys' rule: list_induct2)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs y ys ys')
  obtain j where j_len: "j < length ys'" and nth_j: "ys' ! j = y"
    by (metis Cons.prems in_set_conv_nth list.set_intros(1) mset_eq_setD)

  define ysa where "ysa = take j ys' @ drop (Suc j) ys'"
  have "mset ys' = {#y#} + mset ysa"
    unfolding ysa_def using j_len nth_j
    by (metis Cons_nth_drop_Suc union_mset_add_mset_right add_mset_remove_trivial add_diff_cancel_left'
        append_take_drop_id mset.simps(2) mset_append)
  hence ms_y: "mset ysa = mset ys"
    by (simp add: Cons.prems)
  then obtain xsa where
    len_a: "length ysa = length xsa" and ms_a: "mset (zip xsa ysa) = mset (zip xs ys)"
    using Cons.hyps(2) by blast

  define xs' where "xs' = take j xsa @ x # drop j xsa"
  have ys': "ys' = take j ysa @ y # drop j ysa"
    using ms_y j_len nth_j Cons.prems ysa_def
    by (metis append_eq_append_conv append_take_drop_id diff_Suc_Suc Cons_nth_drop_Suc length_Cons
      length_drop size_mset)
  have j_len': "j \<le> length ysa"
    using j_len ys' ysa_def
    by (metis add_Suc_right append_take_drop_id length_Cons length_append less_eq_Suc_le not_less)
  have "length ys' = length xs'"
    unfolding xs'_def using Cons.prems len_a ms_y
    by (metis add_Suc_right append_take_drop_id length_Cons length_append mset_eq_length)
  moreover have "mset (zip xs' ys') = mset (zip (x # xs) (y # ys))"
    unfolding ys' xs'_def
    apply (rule HOL.trans[OF mset_zip_take_Cons_drop_twice])
    using j_len' by (auto simp: len_a ms_a)
  ultimately show ?case
    by blast
qed

lemma list_all2_reorder_right_invariance:
  assumes rel: "list_all2 R xs ys" and ms_y: "mset ys' = mset ys"
  shows "\<exists>xs'. list_all2 R xs' ys' \<and> mset xs' = mset xs"
proof -
  have len: "length xs = length ys"
    using rel list_all2_conv_all_nth by auto
  obtain xs' where
    len': "length xs' = length ys'" and ms_xy: "mset (zip xs' ys') = mset (zip xs ys)"
    using len ms_y by (metis ex_mset_zip_right)
  have "list_all2 R xs' ys'"
    using assms(1) len' ms_xy unfolding list_all2_iff by (blast dest: mset_eq_setD)
  moreover have "mset xs' = mset xs"
    using len len' ms_xy map_fst_zip mset_map by metis
  ultimately show ?thesis
    by blast
qed

lemma rel_mset_via_perm: "rel_mset rel (mset xs) (mset ys) \<longleftrightarrow> (\<exists>zs. perm xs zs \<and> list_all2 rel zs ys)"
proof (unfold rel_mset_def, intro iffI, goal_cases)
  case 1
  then obtain zs ws where zs: "mset zs = mset xs" and ws: "mset ws = mset ys" and zsws: "list_all2 rel zs ws" by auto
  note list_all2_reorder_right_invariance[OF zsws ws[symmetric], unfolded zs mset_eq_perm]
  then show ?case using perm_sym by auto
next
  case 2
  from this[folded mset_eq_perm] show ?case by force
qed

context idom begin
  lemma irred_0[simp]: "irred (0::'a)" by (unfold Divisibility.irreducible_def, auto simp: factor properfactor_def)
  lemma factor_idom[simp]: "factor (x::'a) y \<longleftrightarrow> (if y = 0 then x = 0 else x dvd y)"
    by (cases "y = 0"; auto intro: exI[of _ 1] elim: dvdE simp: factor)

  lemma associated_connect[simp]: "op \<sim>\<^bsub>mk_monoid\<^esub> = op ddvd" by (intro ext, unfold associated_def, auto)

  lemma essentially_equal_connect[simp]:
    "essentially_equal mk_monoid fs gs \<longleftrightarrow> rel_mset (op ddvd) (mset fs) (mset gs)"
    by (auto simp: essentially_equal_def rel_mset_via_perm)

  lemma irred_idom_nz:
    assumes x0: "(x::'a) \<noteq> 0"
    shows "irred x \<longleftrightarrow> \<not> x dvd 1 \<and> (\<forall> b. b dvd x \<longrightarrow> \<not> x dvd b \<longrightarrow> b dvd 1)"
    using x0 by (auto simp: Divisibility.irreducible_def properfactor_nz)

  lemma dvd_dvd_imp_unit_mult:
    assumes xy: "x dvd y" and yx: "y dvd x"
    shows "\<exists>z. z dvd 1 \<and> y = x * z"
  proof(cases "x = 0")
    case True with xy show ?thesis by (auto intro: exI[of _ 1])
  next
    case x0: False
    from xy obtain z where z: "y = x * z" by (elim dvdE, auto)
    from yx obtain w where w: "x = y * w" by (elim dvdE, auto)
    from z w have "x * (z * w) = x" by (auto simp: ac_simps)
    then have "z * w = 1" using x0 by auto
    with z show ?thesis by (auto intro: exI[of _ z])
  qed

  lemma irred_inner_nz:
    assumes x0: "x \<noteq> 0"
    shows "(\<forall>b. b dvd x \<longrightarrow> \<not> x dvd b \<longrightarrow> b dvd 1) \<longleftrightarrow> (\<forall>a b. x = a * b \<longrightarrow> a dvd 1 \<or> b dvd 1)" (is "?l \<longleftrightarrow> ?r")
  proof (intro iffI allI impI)
    assume l: ?l
    fix a b
    assume xab: "x = a * b"
    then have ax: "a dvd x" and bx: "b dvd x" by auto
    { assume a1: "\<not> a dvd 1"
      with l ax have xa: "x dvd a" by auto
      from dvd_dvd_imp_unit_mult[OF ax xa] obtain z where z1: "z dvd 1" and xaz: "x = a * z" by auto
      from xab x0 have "a \<noteq> 0" by auto
      with xab xaz have "b = z" by auto
      with z1 have "b dvd 1" by auto
    }
    then show "a dvd 1 \<or> b dvd 1" by auto
  next
    assume r: ?r
    fix b assume bx: "b dvd x" and xb: "\<not> x dvd b"
    then obtain a where xab: "x = a * b" by (elim dvdE, auto simp: ac_simps)
    with r consider "a dvd 1" | "b dvd 1" by auto
    then show "b dvd 1"
    proof(cases)
      case 2 then show ?thesis by auto
    next
      case 1
      then obtain c where ac1: "a * c = 1" by (elim dvdE, auto)
      from xab have "x * c = b * (a * c)" by (auto simp: ac_simps)
      with ac1 have "x * c = b" by auto
      then have "x dvd b" by auto
      with xb show ?thesis by auto
    qed
  qed

  lemma irred_idom[simp]: "irred x \<longleftrightarrow> x = 0 \<or> irreducible x"
  by (cases "x = 0"; simp add: irred_idom_nz irred_inner_nz irreducible_def)

  lemma assumes "x \<noteq> 0" and "factors fs x" and "f \<in> set fs" shows "f \<noteq> 0"
    using assms by (auto simp: factors)

  lemma factors_as_mset_factors:
    assumes x0: "x \<noteq> 0" and x1: "x \<noteq> 1"
    shows "factors fs x \<longleftrightarrow> mset_factors (mset fs) x" using assms
    by (auto simp: factors prod_mset_prod_list)


end

context ufd begin
  interpretation comm_monoid_cancel: comm_monoid_cancel "mk_monoid::'a monoid"
    apply (unfold_locales)
    apply simp_all
    using mult_left_cancel
    apply (auto simp: ac_simps)
    done
  lemma factors_exist:
    assumes "a \<noteq> 0"
    and "\<not> a dvd 1"
    shows "\<exists>fs. set fs \<subseteq> UNIV - {0} \<and> factors fs a"
  proof-
    from mset_factors_exist[OF assms]
    obtain F where "mset_factors F a" by auto
    also from ex_mset obtain fs where "F = mset fs" by metis
    finally have fs: "mset_factors (mset fs) a".
    then have "factors fs a" using assms by (subst factors_as_mset_factors, auto)
    moreover have "set fs \<subseteq> UNIV - {0}" using fs by (auto elim!: mset_factorsE)
    ultimately show ?thesis by auto
  qed

  lemma factors_unique:
    assumes fs: "factors fs a"
       and gs: "factors gs a"
       and a0: "a \<noteq> 0"
       and a1: "\<not> a dvd 1"
    shows "rel_mset op ddvd (mset fs) (mset gs)"
  proof-
    from a1 have "a \<noteq> 1" by auto
    with a0 fs gs have "mset_factors (mset fs) a" "mset_factors (mset gs) a" by (unfold factors_as_mset_factors)
    from mset_factors_unique[OF a0 this] show ?thesis.
  qed

  lemma factorial_monoid: "factorial_monoid (mk_monoid :: 'a monoid)"
    by (unfold_locales; auto simp add: factors_exist factors_unique)

end

lemma (in idom) factorial_monoid_imp_ufd:
  assumes "factorial_monoid (mk_monoid :: 'a monoid)"
  shows "class.ufd (op * :: 'a \<Rightarrow> _) 1 (op +) 0 (op -) uminus"
proof (unfold_locales)
  interpret factorial_monoid "mk_monoid :: 'a monoid" by (fact assms)
  {
    fix x assume x: "x \<noteq> 0" "\<not> x dvd 1"
    note * = factors_exist[simplified, OF this]
    with x show "\<exists>F. mset_factors F x" by (subst(asm) factors_as_mset_factors, auto)
  }
  fix x F G assume x0: "x \<noteq> 0" and FG: "mset_factors F x" "mset_factors G x"
  with mset_factors_imp_not_is_unit have x1: "\<not> x dvd 1" by auto
  obtain fs gs where fsgs: "F = mset fs" "G = mset gs" using ex_mset by metis
  note FG = FG[unfolded this]
  then have 0: "0 \<notin> set fs" "0 \<notin> set gs" by (auto elim!: mset_factorsE)
  from x1 have "x \<noteq> 1" by auto
  note FG[folded factors_as_mset_factors[OF x0 this]]
  from factors_unique[OF this, simplified, OF x0 x1, folded fsgs] 0
  show "rel_mset op ddvd F G" by auto
qed




subsection {* Preservation of Irreducibility *}


locale comm_semiring_1_hom = comm_monoid_mult_hom hom + zero_hom hom
  for hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"

locale irreducibility_hom = comm_semiring_1_hom +
  assumes irreducible_imp_irreducible_hom: "irreducible a \<Longrightarrow> irreducible (hom a)"
begin
  lemma hom_mset_factors:
    assumes F: "mset_factors F p"
    shows "mset_factors (image_mset hom F) (hom p)"
  proof (unfold mset_factors_def, intro conjI allI impI)
    note * = F[unfolded mset_factors_def]
    then show "hom p = prod_mset (image_mset hom F)" "image_mset hom F \<noteq> {#}" by auto 
    fix f' assume "f' \<in># image_mset hom F"
    then obtain f where f: "f \<in># F" and f'f: "f' = hom f" by auto
    with * irreducible_imp_irreducible_hom show "irreducible f'" unfolding f'f by auto
  qed
end

locale unit_preserving_hom = comm_semiring_1_hom +
  assumes is_unit_hom_if: "\<And>x. hom x dvd 1 \<Longrightarrow> x dvd 1"
begin
  lemma is_unit_hom_iff[simp]: "hom x dvd 1 \<longleftrightarrow> x dvd 1" using is_unit_hom_if hom_dvd by force

  lemma irreducible_hom_imp_irreducible:
    assumes irr: "irreducible (hom a)" shows "irreducible a"
  proof (intro irreducibleI)
    from irr show "a \<noteq> 0" by auto
    from irr show "\<not> a dvd 1" by (auto dest: irreducible_not_unit)
    fix b c assume "a = b * c"
    then have "hom a = hom b * hom c" by simp
    with irr have "hom b dvd 1 \<or> hom c dvd 1" by (auto dest: irreducibleD)
    then show "b dvd 1 \<or> c dvd 1" by simp
  qed
end

locale factor_preserving_hom = unit_preserving_hom + irreducibility_hom
begin
  lemma irreducible_hom[simp]: "irreducible (hom a) \<longleftrightarrow> irreducible a"
    using irreducible_hom_imp_irreducible irreducible_imp_irreducible_hom by metis
end

lemma factor_preserving_hom_comp:
  assumes f: "factor_preserving_hom f" and g: "factor_preserving_hom g"
  shows "factor_preserving_hom (f o g)"
proof-
  interpret f: factor_preserving_hom f by (rule f)
  interpret g: factor_preserving_hom g by (rule g)
  show ?thesis by (unfold_locales, auto)
qed

context comm_semiring_isom begin
  sublocale unit_preserving_hom by (unfold_locales, auto)
  sublocale factor_preserving_hom
  proof (standard)
    fix a :: 'a
    assume "irreducible a"
    note a = this[unfolded irreducible_def]
    show "irreducible (hom a)"
    proof (rule ccontr)
      assume "\<not> irreducible (hom a)"
      from this[unfolded Factorial_Ring.irreducible_def,simplified] a
      obtain hb hc where eq: "hom a = hb * hc" and nu: "\<not> hb dvd 1" "\<not> hc dvd 1" by auto
      from bij obtain b where hb: "hb = hom b" by (elim bij_pointE)
      from bij obtain c where hc: "hc = hom c" by (elim bij_pointE)
      from eq[unfolded hb hc, folded hom_mult] have "a = b * c" by auto
      with nu hb hc have "a = b * c" "\<not> b dvd 1" "\<not> c dvd 1" by auto
      with a show False by auto
    qed
  qed
end

subsubsection {* Missing muiltiset *}

lemma id_imp_bij:
  assumes id: "\<And>x. f (f x) = x" shows "bij f"
proof (intro bijI injI surjI[of f, OF id])
  fix x y assume "f x = f y"
  then have "f (f x) = f (f y)" by auto
  with id show "x = y" by auto
qed

definition "is_mset_set X \<equiv> \<forall>x \<in># X. count X x = 1"

lemma is_mset_setD[dest]: "is_mset_set X \<Longrightarrow> x \<in># X \<Longrightarrow> count X x = 1"
  unfolding is_mset_set_def by auto

lemma is_mset_setI[intro]:
  assumes "\<And>x. x \<in># X \<Longrightarrow> count X x = 1"
  shows "is_mset_set X"
  using assms unfolding is_mset_set_def by auto

lemma is_mset_set[simp]: "is_mset_set (mset_set X)"
  unfolding is_mset_set_def
  by (meson count_mset_set(1) count_mset_set(2) count_mset_set(3) not_in_iff)

lemma is_mset_set_add[simp]:
  "is_mset_set (X + {#x#}) \<longleftrightarrow> is_mset_set X \<and> x \<notin># X" (is "?L \<longleftrightarrow> ?R")
proof(intro iffI conjI)
  assume L: ?L
  with count_eq_zero_iff count_single show "is_mset_set X"
    unfolding is_mset_set_def
    by (metis (no_types, hide_lams) add_mset_add_single count_add_mset nat.inject set_mset_add_mset_insert union_single_eq_member)
  show "x \<notin># X"
  proof
    assume "x \<in># X"
    then have "count (X + {#x#}) x > 1" by auto
    with L show False by (auto simp: is_mset_set_def)
  qed
next
  assume R: ?R show ?L
  proof
    fix x' assume x': "x' \<in># X + {#x#}"
    show "count (X + {#x#}) x' = 1"
    proof(cases "x' \<in># X")
      case True with R have "count X x' = 1" by auto
        moreover from True R have "count {#x#} x' = 0" by auto
        ultimately show ?thesis by auto
    next
      case False then have "count X x' = 0" by (simp add: not_in_iff)
        with R x' show ?thesis by auto
    qed
  qed
qed


lemma mset_set_id[simp]:
  assumes "is_mset_set X"
  shows "mset_set (set_mset X) = X"
  using assms unfolding is_mset_set_def
  by (metis count_eq_zero_iff count_mset_set(1) count_mset_set(3) finite_set_mset multiset_eqI)

lemma count_image_mset:
  shows "count (image_mset f X) y = (\<Sum>x | x \<in># X \<and> y = f x. count X x)"
proof(induct X)
  case empty show ?case by auto
next
  case (add x X)
    define X' where "X' \<equiv> X + {#x#}"
    have "(\<Sum>z | z \<in># X' \<and> y = f z. count (X + {#x#}) z) =
          (\<Sum>z | z \<in># X' \<and> y = f z. count X z) + (\<Sum>z | z \<in># X' \<and> y = f z. count {#x#} z)"
      unfolding plus_multiset.rep_eq sum.distrib..
    also have split:
      "{z. z \<in># X' \<and> y = f z} =
       {z. z \<in># X' \<and> y = f z \<and> z \<noteq> x} \<union> {z. z \<in># X' \<and> y = f z \<and> z = x}" by blast
    then have "(\<Sum>z | z \<in># X' \<and> y = f z. count {#x#} z) =
      (\<Sum>z | z \<in># X' \<and> y = f z \<and> z = x. count {#x#} z)"
      unfolding split by (subst sum.union_disjoint, auto)
    also have "... = (if y = f x then 1 else 0)" using card_eq_Suc_0_ex1 by (auto simp: X'_def)
    also have "(\<Sum>z | z \<in># X' \<and> y = f z. count X z) = (\<Sum>z | z \<in># X \<and> y = f z. count X z)"
    proof(cases "x \<in># X")
      case True then have "z \<in># X' \<longleftrightarrow> z \<in># X" for z by (auto simp: X'_def)
      then show ?thesis by auto 
    next
      case False
        have split: "{z. z \<in># X' \<and> y = f z} = {z. z \<in># X \<and> y = f z} \<union> {z. z = x \<and> y = f z}"
          by (auto simp: X'_def)
        also have "sum (count X) ... = (\<Sum>z | z \<in># X \<and> y = f z. count X z) + (\<Sum>z | z = x \<and> y = f z. count X z)"
          by (subst sum.union_disjoint, auto simp: False)
        also with False have "\<And>z. z = x \<and> y = f z \<Longrightarrow> count X z = 0" by (meson count_inI)
        with sum.neutral_const have "(\<Sum>z | z = x \<and> y = f z. count X z) = 0" by auto
        finally show ?thesis by auto
    qed
    also have "... = count (image_mset f X) y" using add by auto
    finally show ?case by (simp add: X'_def)  
qed

lemma is_mset_set_image:
  assumes "inj_on f (set_mset X)" and "is_mset_set X"
  shows "is_mset_set (image_mset f X)"
proof (cases X)
  case empty then show ?thesis by auto
next
  case (add x X)
    define X' where "X' \<equiv> add_mset x X"
    with assms add have inj:"inj_on f (set_mset X')"
          and X': "is_mset_set X'" by auto
  show ?thesis
  proof(unfold add, intro is_mset_setI, fold X'_def)
    fix y assume "y \<in># image_mset f X'"
    then have "y \<in> f ` set_mset X'" by auto 
    with inj have "\<exists>!x'. x' \<in># X' \<and> y = f x'" by (meson imageE inj_onD)
    then obtain x' where x': "{x'. x' \<in># X' \<and> y = f x'} = {x'}" by auto
    then have "count (image_mset f X') y = count X' x'"
      unfolding count_image_mset by auto
    also from X' x' have "... = 1" by auto
    finally show "count (image_mset f X') y = 1".
  qed
qed

lemma rel_mset_free:
  assumes rel: "rel_mset rel X Y" and xs: "mset xs = X"
  shows "\<exists>ys. mset ys = Y \<and> list_all2 rel xs ys"
proof-
  from rel[unfolded rel_mset_def] obtain xs' ys'
    where xs': "mset xs' = X" and ys': "mset ys' = Y" and xsys': "list_all2 rel xs' ys'" by auto
  from xs' xs have "mset xs = mset xs'" by auto
  from mset_eq_permutation[OF this]
  obtain f where perm: "f permutes {..<length xs'}" and xs': "permute_list f xs' = xs".
  then have [simp]: "length xs' = length xs" by auto
  from permute_list_nth[OF perm, unfolded xs'] have *: "\<And>i. i < length xs \<Longrightarrow> xs ! i = xs' ! f i" by auto
  note [simp] = list_all2_lengthD[OF xsys',symmetric]
  note [simp] = atLeast0LessThan[symmetric]
  note bij =  permutes_bij[OF perm]
  define ys where "ys \<equiv> map (nth ys' \<circ> f) [0..<length ys']"
  then have [simp]: "length ys = length ys'" by auto 
  have "mset ys = mset (map (nth ys') (map f [0..<length ys']))"
   unfolding ys_def by auto
  also have "... = image_mset (nth ys') (image_mset f (mset [0..<length ys']))"
    by (simp add: multiset.map_comp)
  also have "(mset [0..<length ys']) = mset_set {0..<length ys'}"
    by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set sorted_list_of_set_range) 
  also have "image_mset f (...) = mset_set (f ` {..<length ys'})"
    using subset_inj_on[OF bij_is_inj[OF bij]] by (subst image_mset_mset_set, auto)
  also have "... = mset [0..<length ys']" using perm by (simp add: permutes_image)
  also have "image_mset (nth ys') ... = mset ys'" by(fold mset_map, unfold map_nth, auto)
  finally have "mset ys = Y" using ys' by auto
  moreover have "list_all2 rel xs ys"
  proof(rule list_all2_all_nthI)
    fix i assume i: "i < length xs"
    with * have "xs ! i = xs' ! f i" by auto
    also from i permutes_in_image[OF perm]
    have "rel (xs' ! f i) (ys' ! f i)" by (intro list_all2_nthD[OF xsys'], auto)
    finally show "rel (xs ! i) (ys ! i)" unfolding ys_def using i by simp
  qed simp
  ultimately show ?thesis by auto
qed

lemma rel_mset_split:
  assumes rel: "rel_mset rel (X1+X2) Y"
  shows "\<exists>Y1 Y2. Y = Y1 + Y2 \<and> rel_mset rel X1 Y1 \<and> rel_mset rel X2 Y2"
proof-
  obtain xs1 where xs1: "mset xs1 = X1" using ex_mset by auto
  obtain xs2 where xs2: "mset xs2 = X2" using ex_mset by auto
  from xs1 xs2 have "mset (xs1 @ xs2) = X1 + X2" by auto
  from rel_mset_free[OF rel this] obtain ys
    where ys: "mset ys = Y" "list_all2 rel (xs1 @ xs2) ys" by auto
  then obtain ys1 ys2
    where ys12: "ys = ys1 @ ys2"
      and xs1ys1: "list_all2 rel xs1 ys1"
      and xs2ys2: "list_all2 rel xs2 ys2"
    using list_all2_append1 by blast
  from ys12 ys have "Y = mset ys1 + mset ys2" by auto
  moreover from xs1 xs1ys1 have "rel_mset rel X1 (mset ys1)" unfolding rel_mset_def by auto
  moreover from xs2 xs2ys2 have "rel_mset rel X2 (mset ys2)" unfolding rel_mset_def by auto
  ultimately show ?thesis by (subst exI[of _ "mset ys1"], subst exI[of _ "mset ys2"],auto)
qed

subsubsection{* Back to divisibility *}

lemma(in comm_semiring_1) mset_factors_mult:
  assumes F: "mset_factors F a"
      and G: "mset_factors G b"
  shows "mset_factors (F+G) (a*b)"
proof(intro mset_factorsI)
  fix f assume "f \<in># F + G"
  then consider "f \<in># F" | "f \<in># G" by auto
  then show "irreducible f" by(cases, insert F G, auto)
qed (insert F G, auto)

lemma(in ufd) dvd_imp_subset_factors:
  assumes ab: "a dvd b"
      and F: "mset_factors F a"
      and G: "mset_factors G b"
  shows "\<exists>G'. G' \<subseteq># G \<and> rel_mset (op ddvd) F G'"
proof-
  from F G have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by (simp_all add: mset_factors_imp_nonzero)
  from ab obtain c where c: "b = a * c" by (elim dvdE, auto)
  with b0 have c0: "c \<noteq> 0" by auto
  show ?thesis
  proof(cases "c dvd 1")
    case True
    show ?thesis
      proof(cases F)
        case empty with F show ?thesis by auto
      next
        case (add f F')
          with F
          have a: "f * prod_mset F' = a"
           and F': "\<And>f. f \<in># F' \<Longrightarrow> irreducible f"
           and irrf: "irreducible f" by auto
          from irrf have f0: "f \<noteq> 0" and f1: "\<not>f dvd 1" by (auto dest: irreducible_not_unit)
          from a c have "(f * c) * prod_mset F' = b" by (auto simp: ac_simps)
          moreover {
            have "irreducible (f * c)" using True irrf by (subst irreducible_mult_unit_right)
            with F' irrf have "\<And>f'. f' \<in># F' + {#f * c#} \<Longrightarrow> irreducible f'" by auto
          }
          ultimately have "mset_factors (F' + {#f * c#}) b" by (intro mset_factorsI, auto)
          from mset_factors_unique[OF b0 this G]
          have F'G: "rel_mset op ddvd (F' + {#f * c#}) G".
          from True add have FF': "rel_mset op ddvd F (F' + {#f * c#})"
            by (auto simp add: multiset.rel_refl intro!: rel_mset_Plus)
          have "rel_mset op ddvd F G"
            apply(rule transpD[OF multiset.rel_transp[OF transpI] FF' F'G])
            using ddvd_trans.
          then show ?thesis by auto
      qed
  next
    case False
      from mset_factors_exist[OF c0 this] obtain H where H: "mset_factors H c" by auto
      from c mset_factors_mult[OF F H] have "mset_factors (F + H) b" by auto
      note mset_factors_unique[OF b0 this G]
      from rel_mset_split[OF this] obtain G1 G2
        where "G = G1 + G2" "rel_mset (op ddvd) F G1" "rel_mset (op ddvd) H G2" by auto
      then show ?thesis by (intro exI[of _ "G1"], auto)
  qed
qed

lemma(in idom) irreducible_factor_singleton:
  assumes a: "irreducible a"
  shows "mset_factors F a \<longleftrightarrow> F = {#a#}"
proof(cases F)
  case empty with mset_factorsD show ?thesis by auto
next
  case (add f F')
  show ?thesis
  proof
    assume F: "mset_factors F a"
    from add mset_factorsD[OF F] have *: "a = f * prod_mset F'" by auto
    then have fa: "f dvd a" by auto
    from * a have f0: "f \<noteq> 0" by auto
    from add have "f \<in># F" by auto
    with F have f: "irreducible f" by auto
    from add have "F' \<subseteq># F" by auto
    then have unitemp: "prod_mset F' dvd 1 \<Longrightarrow> F' = {#}"
    proof(induct F')
      case empty then show ?case by auto
    next
      case (add f F')
        from add have "f \<in># F" by (simp add: mset_subset_eq_insertD)
        with F irreducible_not_unit have "\<not> f dvd 1" by auto
        then have "\<not> (prod_mset F' * f) dvd 1" by simp
        with add show ?case by auto
    qed
    show "F = {#a#}"
    proof(cases "a dvd f")
      case True
        then obtain r where "f = a * r" by (elim dvdE, auto)
        with * have "f = (r * prod_mset F') * f" by (auto simp: ac_simps)
        with f0 have "r * prod_mset F' = 1" by auto
        then have "prod_mset F' dvd 1" by (metis dvd_triv_right)
        with unitemp * add show ?thesis by auto
    next
      case False with fa a f show ?thesis by (auto simp: irreducible_altdef)
    qed
  qed (insert a, auto)
qed


lemma(in ufd) irreducible_dvd_imp_factor:
  assumes ab: "a dvd b"
      and a: "irreducible a"
      and G: "mset_factors G b"
  shows "\<exists>g \<in># G. a ddvd g"
proof-
  from a have "mset_factors {#a#} a" by auto
  from dvd_imp_subset_factors[OF ab this G]
  obtain G' where G'G: "G' \<subseteq># G" and rel: "rel_mset (op ddvd) {#a#} G'" by auto
  with rel_mset_size size_1_singleton_mset size_single
  obtain g where gG': "G' = {#g#}" by fastforce
  from rel[unfolded this rel_mset_def]
  have "a ddvd g" by auto
  with gG' G'G show ?thesis by auto
qed

lemma(in idom) prod_mset_remove_units:
  "prod_mset F ddvd prod_mset {# f \<in># F. \<not>f dvd 1 #}"
proof(induct F)
  case (add f F) then show ?case by (cases "f = 0", auto)
qed auto

lemma(in comm_semiring_1) mset_factors_imp_dvd:
  assumes "mset_factors F x" and "f \<in># F" shows "f dvd x"
  using assms by (simp add: dvd_prod_mset mset_factors_def)

lemma(in ufd) prime_elem_iff_irreducible[iff]:
  "prime_elem x \<longleftrightarrow> irreducible x"
proof (intro iffI, fact prime_elem_imp_irreducible, rule prime_elemI)
  assume r: "irreducible x"
  then show x0: "x \<noteq> 0" and x1: "\<not> x dvd 1" by (auto dest: irreducible_not_unit)
  from irreducible_factor_singleton[OF r]
  have *: "mset_factors {#x#} x" by auto
  fix a b
  assume "x dvd a * b"
  then obtain c where abxc: "a * b = x * c" by (elim dvdE, auto)
  show "x dvd a \<or> x dvd b"
  proof(cases "c = 0 \<or> a = 0 \<or> b = 0")
    case True with abxc show ?thesis by auto
  next
    case False
    then have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" and c0: "c \<noteq> 0" by auto
    from x0 c0 have xc0: "x * c \<noteq> 0" by auto
    from x1 have xc1: "\<not> x * c dvd 1" by auto
    show ?thesis
    proof (cases "a dvd 1 \<or> b dvd 1")
      case False
      then have a1: "\<not> a dvd 1" and b1: "\<not> b dvd 1" by auto
      from mset_factors_exist[OF a0 a1]
      obtain F where Fa: "mset_factors F a" by auto
      then have F0: "F \<noteq> {#}" by auto
      from mset_factors_exist[OF b0 b1]
      obtain G where Gb: "mset_factors G b" by auto
      then have G0: "G \<noteq> {#}" by auto
      from mset_factors_mult[OF Fa Gb]
      have FGxc: "mset_factors (F + G) (x * c)" by (simp add: abxc)
      show ?thesis
      proof (cases "c dvd 1")
        case True
        from r irreducible_mult_unit_right[OF this] have "irreducible (x*c)" by simp
        note irreducible_factor_singleton[OF this] FGxc
        with F0 G0 have False by (cases F; cases G; auto)
        then show ?thesis by auto
      next
        case False
        from mset_factors_exist[OF c0 this] obtain H where "mset_factors H c" by auto
        with * have xHxc: "mset_factors (add_mset x H) (x * c)" by force
        note rel = mset_factors_unique[OF xc0 this FGxc]
        obtain hs where "mset hs = H" using ex_mset by auto
        then have "mset (x#hs) = add_mset x H" by auto
        from rel_mset_free[OF rel this]
        obtain jjs where jjsGH: "mset jjs = F + G" and rel: "list_all2 op ddvd (x # hs) jjs" by auto
        then obtain j js where jjs: "jjs = j # js" by (cases jjs, auto)
        with rel have xj: "x ddvd j" by auto
        from jjs jjsGH have j: "j \<in> set_mset (F + G)" by (intro union_single_eq_member, auto)
        from j consider "j \<in># F" | "j \<in># G" by auto
        then show ?thesis
        proof(cases)
          case 1
          with Fa have "j dvd a" by (auto intro: mset_factors_imp_dvd)
          with xj dvd_trans have "x dvd a" by auto
          then show ?thesis by auto
        next
          case 2
          with Gb have "j dvd b" by (auto intro: mset_factors_imp_dvd)
          with xj dvd_trans have "x dvd b" by auto
          then show ?thesis by auto
        qed
      qed
    next
      case True
      then consider "a dvd 1" | "b dvd 1" by auto
      then show ?thesis
      proof(cases)
        case 1
        then obtain d where ad: "a * d = 1" by (elim dvdE, auto)
        from abxc have "x * (c * d) = a * b * d" by (auto simp: ac_simps)
        also have "... = a * d * b" by (auto simp: ac_simps)
        finally have "x dvd b" by (intro dvdI, auto simp: ad)
        then show ?thesis by auto
      next
        case 2
        then obtain d where bd: "b * d = 1" by (elim dvdE, auto)
        from abxc have "x * (c * d) = a * b * d" by (auto simp: ac_simps)
        also have "... = (b * d) * a" by (auto simp: ac_simps)
        finally have "x dvd a" by (intro dvdI, auto simp:bd)
        then show ?thesis by auto
      qed
    qed
  qed
qed

subsection\<open>Results for GCDs etc.\<close>

lemma prod_list_remove1: "(x :: 'b :: comm_monoid_mult) \<in> set xs \<Longrightarrow> prod_list (remove1 x xs) * x = prod_list xs"
  by (induct xs, auto simp: ac_simps)

(* Isabelle 2015-style and generalized gcd-class without normalization and factors *)
class comm_monoid_gcd = gcd + comm_semiring_1 +
  assumes gcd_dvd1[iff]: "gcd a b dvd a"
      and gcd_dvd2[iff]: "gcd a b dvd b"
      and gcd_greatest: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b"
begin

  lemma gcd_0_0[simp]: "gcd 0 0 = 0"
    using gcd_greatest[OF dvd_0_right dvd_0_right, of 0] by auto

  lemma gcd_zero_iff[simp]: "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  proof
    assume "gcd a b = 0"
    from gcd_dvd1[of a b, unfolded this] gcd_dvd2[of a b, unfolded this]
    show "a = 0 \<and> b = 0" by auto
  qed auto

  lemma gcd_zero_iff'[simp]: "0 = gcd a b \<longleftrightarrow> a = 0 \<and> b = 0"
    using gcd_zero_iff by metis

  lemma dvd_gcd_0_iff[simp]:
    shows "x dvd gcd 0 a \<longleftrightarrow> x dvd a" (is ?g1)
      and "x dvd gcd a 0 \<longleftrightarrow> x dvd a" (is ?g2)
  proof-
    have "a dvd gcd a 0" "a dvd gcd 0 a" by (auto intro: gcd_greatest)
    with dvd_refl show ?g1 ?g2 by (auto dest: dvd_trans)
  qed

  lemma gcd_dvd_1[simp]: "gcd a b dvd 1 \<longleftrightarrow> coprime a b"
    using dvd_trans[OF gcd_greatest[of _ a b], of _ 1]
    by (cases "a = 0 \<and> b = 0") (auto intro!: coprimeI elim: coprimeE)

  lemma dvd_imp_gcd_dvd_gcd: "b dvd c \<Longrightarrow> gcd a b dvd gcd a c"
    by (meson gcd_dvd1 gcd_dvd2 gcd_greatest dvd_trans)

  definition listgcd :: "'a list \<Rightarrow> 'a" where
    "listgcd xs = foldr gcd xs 0"

  lemma listgcd_simps[simp]: "listgcd [] = 0" "listgcd (x # xs) = gcd x (listgcd xs)"
    by (auto simp: listgcd_def)

  lemma listgcd: "x \<in> set xs \<Longrightarrow> listgcd xs dvd x" 
  proof (induct xs)
    case (Cons y ys)
    show ?case
    proof (cases "x = y")
      case False
      with Cons have dvd: "listgcd ys dvd x" by auto
      thus ?thesis unfolding listgcd_simps using dvd_trans by blast
    next
      case True
      thus ?thesis unfolding listgcd_simps using dvd_trans by blast
    qed
  qed simp

  lemma listgcd_greatest: "(\<And> x. x \<in> set xs \<Longrightarrow> y dvd x) \<Longrightarrow> y dvd listgcd xs"
    by (induct xs arbitrary:y, auto intro: gcd_greatest)

end


context Rings.dvd begin

  definition "is_gcd x a b \<equiv> x dvd a \<and> x dvd b \<and> (\<forall>y. y dvd a \<longrightarrow> y dvd b \<longrightarrow> y dvd x)"

  definition "some_gcd a b \<equiv> SOME x. is_gcd x a b"

  lemma is_gcdI[intro!]:
    assumes "x dvd a" "x dvd b" "\<And>y. y dvd a \<Longrightarrow> y dvd b \<Longrightarrow> y dvd x"
    shows "is_gcd x a b" by (insert assms, auto simp: is_gcd_def)

  lemma is_gcdE[elim!]:
    assumes "is_gcd x a b"
        and "x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> (\<And>y. y dvd a \<Longrightarrow> y dvd b \<Longrightarrow> y dvd x) \<Longrightarrow> thesis"
    shows thesis by (insert assms, auto simp: is_gcd_def)

  lemma is_gcd_some_gcdI:
    assumes "\<exists>x. is_gcd x a b" shows "is_gcd (some_gcd a b) a b"
    by (unfold some_gcd_def, rule someI_ex[OF assms])

end

context comm_semiring_1 begin

  lemma some_gcd_0[intro!]: "is_gcd (some_gcd a 0) a 0" "is_gcd (some_gcd 0 b) 0 b"
    by (auto intro!: is_gcd_some_gcdI intro: exI[of _ a] exI[of _ b])

  lemma some_gcd_0_dvd[intro!]:
    "some_gcd a 0 dvd a" "some_gcd 0 b dvd b" using some_gcd_0 by auto

  lemma dvd_some_gcd_0[intro!]:
    "a dvd some_gcd a 0" "b dvd some_gcd 0 b" using some_gcd_0[of a] some_gcd_0[of b] by auto

end

context idom begin

  lemma is_gcd_connect:
    assumes "a \<noteq> 0" "b \<noteq> 0" shows "isgcd mk_monoid x a b \<longleftrightarrow> is_gcd x a b"
    using assms by (auto simp: isgcd_def)

  lemma some_gcd_connect:
    assumes "a \<noteq> 0" and "b \<noteq> 0" shows "somegcd mk_monoid a b = some_gcd a b"
    using assms by (auto intro!: arg_cong[of _ _ Eps] simp: is_gcd_connect some_gcd_def somegcd_def)
end

context comm_monoid_gcd
begin
  lemma is_gcd_gcd: "is_gcd (gcd a b) a b" using gcd_greatest by auto
  lemma is_gcd_some_gcd: "is_gcd (some_gcd a b) a b" by (insert is_gcd_gcd, auto intro!: is_gcd_some_gcdI)
  lemma gcd_dvd_some_gcd: "gcd a b dvd some_gcd a b" using is_gcd_some_gcd by auto
  lemma some_gcd_dvd_gcd: "some_gcd a b dvd gcd a b" using is_gcd_some_gcd by (auto intro: gcd_greatest)
  lemma some_gcd_ddvd_gcd: "some_gcd a b ddvd gcd a b" by (auto intro: gcd_dvd_some_gcd some_gcd_dvd_gcd)
  lemma some_gcd_dvd: "some_gcd a b dvd d \<longleftrightarrow> gcd a b dvd d" "d dvd some_gcd a b \<longleftrightarrow> d dvd gcd a b"
    using some_gcd_ddvd_gcd[of a b] by (auto dest:dvd_trans)

end

class idom_gcd = comm_monoid_gcd + idom
begin

  interpretation raw: comm_monoid_cancel "mk_monoid :: 'a monoid"
    by (unfold_locales, auto intro: mult_commute mult_assoc)

  interpretation raw: gcd_condition_monoid "mk_monoid :: 'a monoid"
    by (unfold_locales, auto simp: is_gcd_connect intro!: exI[of _ "gcd _ _"] dest: gcd_greatest)

  lemma gcd_mult_ddvd:
    "d * gcd a b ddvd gcd (d * a) (d * b)"
  proof (cases "d = 0")
    case True then show ?thesis by auto
  next
    case d0: False
    show ?thesis
    proof (cases "a = 0 \<or> b = 0")
      case False
      note some_gcd_ddvd_gcd[of a b]
      with d0 have "d * gcd a b ddvd d * some_gcd a b" by auto
      also have "d * some_gcd a b ddvd some_gcd (d * a) (d * b)"
        using False d0 raw.gcd_mult by (simp add: some_gcd_connect)
      also note some_gcd_ddvd_gcd
      finally show ?thesis.
    next
      case True
      with d0 show ?thesis
        apply (elim disjE)
         apply (rule ddvd_trans[of _ "d * b"]; force)
         apply (rule ddvd_trans[of _ "d * a"]; force)
        done
    qed
  qed

  lemma gcd_greatest_mult: assumes cad: "c dvd a * d" and cbd: "c dvd b * d"
    shows "c dvd gcd a b * d"
  proof-
    from gcd_greatest[OF assms] have c: "c dvd gcd (d * a) (d * b)" by (auto simp: ac_simps)
    note gcd_mult_ddvd[of d a b]
    then have "gcd (d * a) (d * b) dvd gcd a b * d" by (auto simp: ac_simps)
    from dvd_trans[OF c this] show ?thesis .
  qed

  lemma listgcd_greatest_mult: "(\<And> x :: 'a. x \<in> set xs \<Longrightarrow> y dvd x * z) \<Longrightarrow> y dvd listgcd xs * z"
  proof (induct xs)
    case (Cons x xs)
    from Cons have "y dvd x * z" "y dvd listgcd xs * z" by auto
    thus ?case unfolding listgcd_simps by (rule gcd_greatest_mult)
  qed (simp)

  lemma dvd_factor_mult_gcd:
    assumes dvd: "k dvd p * q" "k dvd p * r"
      and q0: "q \<noteq> 0" and r0: "r \<noteq> 0"
    shows "k dvd p * gcd q r" 
  proof -
    from dvd gcd_greatest[of k "p * q" "p * r"]
    have "k dvd gcd (p * q) (p * r)" by simp
    also from gcd_mult_ddvd[of p q r]
    have "... dvd (p * gcd q r)" by auto
    finally show ?thesis .
  qed

  lemma coprime_mult_cross_dvd:
    assumes coprime: "coprime p q" and eq: "p' * p = q' * q"
    shows "p dvd q'" (is ?g1) and "q dvd p'" (is ?g2)
  proof (atomize(full), cases "p = 0 \<or> q = 0")
    case True
    then show "?g1 \<and> ?g2"
    proof
      assume p0: "p = 0" with coprime have "q dvd 1" by auto
      with eq p0 show ?thesis by auto
    next
      assume q0: "q = 0" with coprime have "p dvd 1" by auto
      with eq q0 show ?thesis by auto
    qed
  next
    case False
    {
      fix p q r p' q' :: 'a
      assume cop: "coprime p q" and eq: "p' * p = q' * q" and p: "p \<noteq> 0" and q: "q \<noteq> 0"
         and r: "r dvd p" "r dvd q"
      let ?gcd = "gcd q p"
      from eq have "p' * p dvd q' * q" by auto
      hence d1: "p dvd q' * q" by (rule dvd_mult_right)
      have d2: "p dvd q' * p" by auto
      from dvd_factor_mult_gcd[OF d1 d2 q p] have 1: "p dvd q' * ?gcd" .
      from q p have 2: "?gcd dvd q" by simp
      from q p have 3: "?gcd dvd p" by simp
      from cop[unfolded coprime_def, rule_format, OF 3 2] have "?gcd dvd 1" .
      from 1 dvd_mult_unit_iff[OF this] have "p dvd q'" by auto
    } note main = this
    from main[OF coprime eq,of 1] False coprime coprime_commute main[OF _ eq[symmetric], of 1]
    show "?g1 \<and> ?g2" by auto
  qed

end

subclass (in ring_gcd) idom_gcd by (unfold_locales, auto)

lemma coprime_rewrites: "comm_monoid_mult.coprime (op *) 1 = coprime"
  apply (intro ext)
  apply (subst comm_monoid_mult.coprime_def)
  apply (unfold_locales)
  apply (unfold dvd_rewrites)
  apply (fold coprime_def) ..

(* TODO: incorporate into the default class hierarchy *)
locale gcd_condition =
  fixes ty :: "'a :: idom itself"
  assumes gcd_exists: "\<And>a b :: 'a. \<exists>x. is_gcd x a b"
begin
  sublocale idom_gcd "op *" "1 :: 'a" "op +" 0 "op -" uminus some_gcd 
    rewrites "dvd.dvd (op *) = op dvd"
        and "comm_monoid_mult.coprime (op * ) 1 = Unique_Factorization.coprime"
  proof-
    have "is_gcd (some_gcd a b) a b" for a b :: 'a by (intro is_gcd_some_gcdI gcd_exists)
    from this[unfolded is_gcd_def]
    show "class.idom_gcd op * (1 :: 'a) op + 0 op - uminus some_gcd" by (unfold_locales, auto simp: dvd_rewrites)
  qed (simp_all add: dvd_rewrites coprime_rewrites)
end

instance semiring_gcd \<subseteq> comm_monoid_gcd by (intro_classes, auto)

lemma listgcd_connect: "listgcd = gcd_list"
proof (intro ext)
  fix xs :: "'a list"
  show "listgcd xs = gcd_list xs" by(induct xs, auto)
qed

interpretation some_gcd: gcd_condition "TYPE('a::ufd)"
proof(unfold_locales, intro exI)
  interpret factorial_monoid "mk_monoid :: 'a monoid" by (fact factorial_monoid)
  note d = dvd.dvd_def some_gcd_def carrier_0
  fix a b :: 'a
  show "is_gcd (some_gcd a b) a b"
  proof (cases "a = 0 \<or> b = 0")
    case True
    thus ?thesis using some_gcd_0 by auto
  next
    case False
    with gcdof_exists[of a b]
    show ?thesis by (auto intro!: is_gcd_some_gcdI simp add: is_gcd_connect some_gcd_connect)
  qed
qed

lemma some_gcd_listgcd_dvd_listgcd: "some_gcd.listgcd xs dvd listgcd xs"
  by (induct xs, auto simp:some_gcd_dvd intro:dvd_imp_gcd_dvd_gcd)

lemma listgcd_dvd_some_gcd_listgcd: "listgcd xs dvd some_gcd.listgcd xs"
  by (induct xs, auto simp:some_gcd_dvd intro:dvd_imp_gcd_dvd_gcd)

context factorial_ring_gcd begin

text {* Do not declare the following as subclass, to avoid conflict in
  @{text "field \<subseteq> gcd_condition"} vs. @{text "factorial_ring_gcd \<subseteq> gcd_condition"}.
 *}
sublocale as_ufd: ufd
proof(unfold_locales, goal_cases)
  case (1 x)
  from prime_factorization_exists[OF `x \<noteq> 0`]
  obtain F where f: "\<And>f. f \<in># F \<Longrightarrow> prime_elem f" and Fx: "prod_mset F = normalize x" by auto
  from Fx have x: "x = unit_factor x * prod_mset F" by auto
  from `\<not> is_unit x` Fx have "F \<noteq> {#}" by auto
  then obtain g G where F: "F = add_mset g G" by (cases F, auto)
  then have "g \<in># F" by auto
  with f[OF this]prime_elem_iff_irreducible
    irreducible_mult_unit_left[OF unit_factor_is_unit[OF `x \<noteq> 0`]]
  have g: "irreducible (unit_factor x * g)" by auto
  show ?case
  proof (intro exI conjI mset_factorsI)
    from x show "prod_mset (add_mset (unit_factor x * g) G) = x" by (simp add: F ac_simps)
    fix f assume "f \<in># add_mset (unit_factor x * g) G"
    with f[unfolded F] g prime_elem_iff_irreducible
    show "irreducible f" by auto
  qed auto
next
  case (2 x F G)
  note transpD[OF multiset.rel_transp[OF ddvd_transp],trans]
  obtain fs where F: "F = mset fs" by (metis ex_mset)
  have "list_all2 (op ddvd) fs (map normalize fs)" by (intro list_all2_all_nthI, auto)
  then have FH: "rel_mset (op ddvd) F (image_mset normalize F)" by (unfold rel_mset_def F, force)
  also
    have FG: "image_mset normalize F = image_mset normalize G"
    proof (intro prime_factorization_unique')
      from 2 have xF: "x = prod_mset F" and xG: "x = prod_mset G" by auto
      from xF have "normalize x = prod_mset (image_mset normalize F)" by (simp add: local.normalize_prod_mset)
      with xG have nFG: "\<dots> = prod_mset (image_mset normalize G)" by (simp_all add: local.normalize_prod_mset)
      then show "(\<Prod>i\<in>#image_mset normalize F. i) = (\<Prod>i\<in>#image_mset normalize G. i)" by auto
      from 2 prime_elem_iff_irreducible have "f \<in># F \<Longrightarrow> prime_elem f" "g \<in># G \<Longrightarrow> prime_elem g" for f g
       by (auto intro: prime_elemI)
      then show " Multiset.Ball (image_mset normalize F) prime"
        "Multiset.Ball (image_mset normalize G) prime" by auto
    qed
  also
    obtain gs where G: "G = mset gs" by (metis ex_mset)
    have "list_all2 (op ddvd\<inverse>\<inverse>) gs (map normalize gs)" by (intro list_all2_all_nthI, auto)
    then have "rel_mset (op ddvd) (image_mset normalize G) G"
      by (subst multiset.rel_flip[symmetric], unfold rel_mset_def G, force)
  finally show ?case.
qed

end

instance int :: ufd by (intro class.ufd.of_class.intro as_ufd.ufd_axioms)
instance int :: idom_gcd by (intro_classes, auto)

lemma irreducible_field[simp]:
  "irreducible (x::'a::field) \<longleftrightarrow> False" by (auto simp: dvd_field_iff irreducible_def)

instance field \<subseteq> ufd by (intro_classes, auto simp: dvd_field_iff)

end
