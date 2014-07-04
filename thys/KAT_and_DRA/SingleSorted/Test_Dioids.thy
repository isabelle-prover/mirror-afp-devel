(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

header {* Test Dioids *}

theory Test_Dioids
  imports "../../Kleene_Algebra/Dioid"
begin

text {*
  Tests are embedded in a weak dioid, a dioid without the right annihilation and left distributivity axioms, using an 
  operator $t$ defined by a complementation operator. This allows us to use tests in weak settings, such as Probabilistic Kleene Algebra and Demonic Refinement Algebra.
*}

class near_dioid_tests_zerol = ab_near_semiring_one_zerol + plus_ord +
  fixes   comp_op :: "'a \<Rightarrow> 'a" ("n_" [90] 91)
  assumes test_one:         "n n 1 = 1"
  and     test_mult:        "n n (n n x \<cdot> n n y) = n n y \<cdot> n n x" 
  and     test_mult_comp:   "n x \<cdot> n n x = 0"
  and     test_de_morgan:   "n x + n y = n (n n x \<cdot> n n y)"

begin

lemma add_idem' [simp]: "x + x = x"
  by (metis annil distrib_right' mult_1_left test_de_morgan test_mult_comp test_one)

subclass near_dioid_one_zerol
  by (unfold_locales, simp) 

lemma "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  (* nitpick *) oops

lemma "n n x \<cdot> (y + z) = n n x \<cdot> y + n n x \<cdot> z"
  (* nitpick *) oops

text {*
  A test operator $t$ can then be defined as an abbreviation of applying $n$ twice.
  The elements of the image, $t(K)$, form a Boolean algebra, but we do not express this in Isabelle.
  Instead, we prove all the obvious laws of Boolean algebra.
*}

abbreviation test_operator :: "'a \<Rightarrow> 'a" ("t_" [100] 101) where
  "t x \<equiv> n (n x)"

lemma test_zero[simp]: "t 0 = 0"
  by (metis mult_1_left test_mult_comp test_one)

lemma test_distrib_left: "t x \<cdot> (t y + t z) = (t x \<cdot> t y) + (t x \<cdot> t z)"
  by (metis add.commute distrib_right' test_de_morgan test_mult)

lemma test_distrib_right: "(t x + t y) \<cdot> t z = (t x \<cdot> t z) + (t y \<cdot> t z)"
  by (metis distrib_right')

lemma test_mult_idem[simp]:   "t x \<cdot> t x = t x"
  by (metis add_0_right test_distrib_left mult_1_right test_de_morgan test_mult_comp test_one)

lemma test_idem[simp]: "t t x = t x"
  by (metis add_idem' test_de_morgan test_mult_idem)

lemma test_add_closed[simp]: "t (t x + t y) = t x + t y"
  by (metis add.commute test_de_morgan test_mult)

lemma test_mult_comm: "t x \<cdot> t y = t y \<cdot> t x"
  by (metis test_mult test_idem)

lemma test_add_comm: "t x + t y = t y + t x"
  by (metis add_comm)

lemma test_mult_assoc: "t x \<cdot> (t y \<cdot> t z) = (t x \<cdot> t y) \<cdot> t z"
  by (metis mult.assoc)

lemma test_add_assoc: "t x + (t y + t z) = (t x + t y) + t z" 
  by (metis add.assoc)

lemma test_add_comp: "n x + t x = 1"
  by (metis test_de_morgan test_mult_comp test_one mult_1_left)

lemma "n x \<cdot> t x = 0"
  by (metis test_mult_comp)

lemma test_mult_lb1: "t x \<cdot> t y \<le> t x"
  by (metis add.commute add_ub1 mult_1_left mult_isor test_add_comp test_de_morgan test_mult)

lemma test_mult_lb2: "t x \<cdot> t y \<le> t y"
  by (metis test_mult_comm test_mult_lb1)

lemma test_add_lb: "t x \<cdot> (t x + t y) = t x"
  by (metis add.commute less_eq_def test_distrib_left test_mult_idem test_mult_lb1)

lemma test_leq_mult_def: "(t x \<le> t y) = (t x \<cdot> t y = t x)"
  by (metis less_eq_def test_add_lb test_mult_comm test_mult_lb1)

lemma test_mult_glbI: "\<lbrakk>t z \<le>  t x;  t z \<le>  t y\<rbrakk> \<Longrightarrow> t z \<le>  t x \<cdot> t y"
  by (metis mult_isor test_leq_mult_def)

lemma test_mult_glb: "t z \<le>  t x \<and>  t z \<le>  t y \<longleftrightarrow> t z \<le>  t x \<cdot> t y"
  by (metis (full_types) order_trans test_mult_glbI test_mult_lb1 test_mult_lb2)

lemma test_add_distl: "(t x \<cdot> t y) + t z = (t x + t z) \<cdot> (t y + t z)"
proof (rule antisym)
  have "t x \<cdot> t y \<le> (t x + t z) \<cdot> (t y + t z)"
    by (metis add_lub mult_isor order_prop test_distrib_left)
  thus "t x \<cdot> t y + t z \<le> (t x + t z) \<cdot> (t y + t z)"
    by (metis add_lub_var add_ub2 distrib_right' test_add_comm test_add_lb)
next
  show "(t x + t z) \<cdot> (t y + t z) \<le> t x \<cdot> t y + t z"
    by (metis add.commute test_add_lb test_de_morgan test_distrib_left test_mult test_mult_lb2)
qed

lemma test_add_distr: "t x + (t y \<cdot> t z) = (t x + t y) \<cdot> (t x + t z)"
  by (metis add_comm test_add_distl)

lemma test_add_zerol: "0 + t x = t x"
  by (metis add_zerol)

lemma test_add_zeror: "t x + 0 = t x"
  by (metis add_zeror)

lemma test_mult_onel: "1 \<cdot> t x = t x"
  by (metis mult_onel)

lemma test_mult_oner: "t x \<cdot> 1 = t x"
  by (metis mult_oner)

lemma test_lb: "t x \<ge> 0"
  by (metis zero_least)

lemma test_ub: "t x \<le> 1"
  by (metis add_ub1 test_add_comp)

text {*
  A test is an element $p$ where $t\ p = p$.
*}  

definition test :: "'a \<Rightarrow> bool" where
  "test p \<equiv> t p = p"

notation comp_op ("!_" [101] 100)

lemma test_add_closed_var: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> test (p + q)"
  by (metis test_add_closed test_def)

lemma test_mult_closed: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> test (p \<cdot> q)"
  by (metis test_def test_mult test_mult_comm)

lemma test_comp_closed: "test p \<Longrightarrow> test (!p)"
  by (metis test_def)

lemma test_ub_var: "test p \<Longrightarrow> p \<le> 1"
  by (metis test_def test_ub)

lemma test_lb_var: "test p \<Longrightarrow> p \<ge> 0"
  by (metis zero_least)

lemma test_zero_var: "test 0"
  by (metis test_def test_zero)

lemma test_one_var: "test 1"
  by (metis test_def test_one)

lemma test_not_one: "!1 = 0"
  by (metis mult_oner test_mult_comp test_one)

lemma test_add_idem: "test p \<Longrightarrow> p + p = p"
  by (metis add_idem')

lemma test_mult_idem_var [simp]: "test p \<Longrightarrow> p \<cdot> p = p"
  by (metis test_def test_mult_idem)

lemma test_add_comm_var: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p + q = q + p"
  by (metis add.commute)

lemma test_mult_comm_var: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p \<cdot> q = q \<cdot> p"
  by (metis test_def test_mult_comm)

lemma test_distrib_left_var: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> p\<cdot>(q + r) = p\<cdot>q + p\<cdot>r"
  by (metis distrib_right' test_add_closed_var test_mult_comm_var)

lemma test_distrib_right_var: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> (p + q)\<cdot>r = p\<cdot>r + q\<cdot>r"
  by (metis distrib_right')

lemma test_add_distl_var: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> p\<cdot>q + r = (p + r)\<cdot>(q + r)"
  using test_add_distl[of p q r] by (simp add: test_def)

lemma test_add_distr_var: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> p + q\<cdot>r = (p + q)\<cdot>(p + r)"
  by (metis add_comm test_add_distl_var)

lemma test_absorb1: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p + p \<cdot> q = p"
  by (metis test_add_distr_var test_add_idem test_add_lb test_def)

lemma test_absorb2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p \<cdot> (p + q) = p"
  by (metis test_distrib_left_var test_mult_idem_var test_absorb1)

lemma test_absorb3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow>  (p + q) \<cdot> q = q"
  by (metis add.commute test_absorb2 test_add_closed_var test_mult_comm_var)

lemma test_leq_mult_def_var: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p \<le> q) = (p \<cdot> q = p)"
  by (metis add.commute less_eq_def test_absorb1 test_absorb2 test_mult_comm_var)

lemma test_double_comp_var: "test p \<Longrightarrow> p = !(!p)"
  by (metis test_def)

lemma test_comp: "test p \<Longrightarrow> \<exists>q. test q \<and> p + q = 1 \<and> p \<cdot> q = 0"
  by (metis test_add_comp test_def test_mult_comp)

lemma test_dist_var: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (test r \<and> r \<cdot> p = r \<cdot> q \<and> r + p = r + q \<longrightarrow> p = q)"
  by (metis add.commute test_absorb1 test_add_distr_var test_mult_comm_var)

lemma test_comp_uniq: "test p \<Longrightarrow> \<exists>!q. test q \<and> p + q = 1 \<and> p \<cdot> q = 0"
  by (safe, metis test_comp, metis test_dist_var)

lemma test_comp_mult [simp]: "test p \<Longrightarrow> p \<cdot> !p = 0"
  by (metis test_double_comp_var test_mult_comp)

lemma test_comp_mult2 [simp]: "test p \<Longrightarrow> !p \<cdot> p = 0"
  by (metis test_double_comp_var test_mult_comp)

lemma test_comp_add [simp]: "test p \<Longrightarrow> p + !p = 1"
  by (metis test_double_comp_var test_add_comp)

lemma test_comp_closed_var: "test p \<Longrightarrow> test (!p)"
  by (metis test_def)

lemma de_morgan1: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !p + !q = !(p \<cdot> q)"
  by (metis test_de_morgan test_def)

lemma de_morgan2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !p \<cdot> !q = !(p + q)"
  by (metis add.commute add_idem' opp_mult_def test_de_morgan test_double_comp_var test_mult)

lemma de_morgan3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !(!p + !q) = p \<cdot> q"
  by (metis de_morgan1 test_double_comp_var test_mult_closed)

lemma de_morgan4: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !(!p \<cdot> !q) = p + q"
  by (metis de_morgan2 test_add_closed_var test_def)

lemma test_comp_anti: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p \<le> q) = (!q \<le> !p)"
  by (metis add.commute de_morgan1 test_double_comp_var test_mult_closed less_eq_def test_leq_mult_def)

lemma ba_1: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> p + q + !q = r + !r"
  by (metis add.assoc mult_onel test_absorb1 test_add_comp test_def test_one_var)

lemma ba2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p + p = p + !(q + !q)"
  by (metis add_idem add_zeror ba_1 test_not_one test_one_var)

lemma ba3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p = (p \<cdot> q) + (p \<cdot> !q)"
  by (metis test_distrib_left_var mult_oner test_add_comp test_def)

lemma ba4: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p = (p + !q) \<cdot> (p + q)"
  by (metis add.commute add_zerol test_add_distr_var test_comp_mult test_def)

lemma ba5: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p + q) \<cdot> !p = q \<cdot> !p"
  by (metis distrib_right'  test_comp_mult add_zerol)

lemma ba6: "test p \<Longrightarrow> !p \<cdot> p = 0"
  by (metis test_def test_mult_comp)

lemma ba7: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !p = !(p + q) + !(p + !q)"
  by (metis ba3 de_morgan2 test_comp_closed_var test_double_comp_var)

lemma test_restrictl: "test p \<Longrightarrow> p \<cdot> x \<le> x"
  by (metis distrib_right' mult_onel order_prop test_comp_uniq)

text {* Nitpick refutes the next lemma. *}

lemma test_restrictr: "test p \<Longrightarrow> x \<cdot> p \<le> x"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> p\<cdot>q \<le> r \<longleftrightarrow> p \<le> !q + r"
proof auto
  assume assms: "test p" "test q" "test r" "p\<cdot>q \<le> r"
  hence "p \<le> r + p \<cdot>!q"
    by (metis add_iso ba3 distrib_left distrib_left)
  thus "p \<le> r + !q"
    by (metis add_iso_var assms(1) dual_order.trans order_refl test_restrictl)
next
  assume "test p" "test q" "test r" "p \<le> r + !q"
  thus "p \<cdot> q \<le> r" 
    by (metis add.commute mult_isor distrib_right' add_zeror test_comp_mult2 order_trans test_mult_comm_var test_restrictl)
qed
  
text {*
  Next, we prove lemmas mixing the embedded tests and any element of the carrier set.
*}

lemma test_eq1: "test p \<Longrightarrow> y \<le> x \<longleftrightarrow> p\<cdot>y \<le> x \<and> !p\<cdot>y \<le> x"
  apply (default, metis order_trans test_comp_closed_var test_restrictl)
  by (metis add_iso_var add_idem' distrib_right' mult_onel test_comp_add)

text {* Nitpick refutes the next four lemmas. *}

lemma test_eq2: "test p \<Longrightarrow> z \<le> p\<cdot>x + !p\<cdot>y \<longleftrightarrow> p\<cdot>z \<le> p\<cdot>x \<and> !p\<cdot>z \<le> !p\<cdot>y"
  (* nitpick *) oops

lemma test_eq3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
  (* nitpick *) oops

lemma test1: "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma test_eq4: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> x\<cdot>!q = !p\<cdot>x\<cdot>!q \<longleftrightarrow> p\<cdot>x\<cdot>!q = 0"
  apply default
  apply (metis annil mult.assoc test_comp_mult)
  by (metis add_zerol distrib_right' mult_onel test_comp_add)

lemma test2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>q\<cdot>p = p\<cdot>q"
  by (metis mult.assoc test_mult_comm_var test_mult_idem_var)

lemma test3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>q\<cdot>!p = 0"
  by (metis ba5 test_absorb1 test_comp_mult test_mult_closed)

lemma test4: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !p\<cdot>q\<cdot>p = 0"
  by (metis annil ba6 mult.assoc test_mult_comm_var)

text {* Nitpick refutes the next two lemmas. *}

lemma comm_add: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>(x + y) = (x + y)\<cdot>p"
  (* nitpick *) oops

lemma comm_add_var: "\<lbrakk>test p; test q; test r; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>(q\<cdot>x + r\<cdot>y) = (q\<cdot>x + r\<cdot>y)\<cdot>p"
  (*(* nitpick *)*) oops

lemma comm_mult: "\<lbrakk>test p; test q; q\<cdot>x = x\<cdot>q\<rbrakk> \<Longrightarrow> p\<cdot>q\<cdot>x = q\<cdot>p\<cdot>x"
  by (metis mult.assoc test_mult_comm_var)

lemma de_morgan_var1: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> (!p + q)\<cdot>(p + r) = p\<cdot>q + !p\<cdot>r"
proof -
  assume tests: "test p" "test q" "test r"
  hence "(!p + q)\<cdot>(p + r) = !p\<cdot>p + !p\<cdot>r + q\<cdot>p + r\<cdot>q"
    by (metis add_assoc' distrib_right' test_comp_closed_var test_distrib_left_var test_mult_comm_var)
  also have "... = !p\<cdot>r + q\<cdot>p + (p + !p)\<cdot>r\<cdot>q"
    by (metis add_zerol mult_onel test_comp_add test_comp_mult2 tests(1))
  also have "... = !p\<cdot>r + q\<cdot>p + p\<cdot>r\<cdot>q + !p\<cdot>r\<cdot>q"
    by (metis add_assoc' test_comp_closed_var test_distrib_right_var test_mult_closed tests)
  also have "... = !p\<cdot>r + p\<cdot>q + p\<cdot>q\<cdot>r + !p\<cdot>r\<cdot>q"
    by (metis mult.assoc test_mult_comm_var tests)
  also have "... = !p\<cdot>r\<cdot>1 + !p\<cdot>r\<cdot>q + p\<cdot>q\<cdot>1 + p\<cdot>q\<cdot>r"
    by (metis add.commute add.left_commute mult_oner)
  also have "... = !p\<cdot>r\<cdot>(1 + q) + p\<cdot>q\<cdot>(1 + r)"
    by (metis add_assoc' test_comp_closed_var test_distrib_left_var test_mult_closed test_one_var tests)
  finally show ?thesis
    by (metis add.commute less_eq_def mult_oner test_ub_var tests(2-3))
qed

lemma de_morgan_var2: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> !(p\<cdot>q + !p\<cdot>r) = (p\<cdot>!q + !p\<cdot>!r)"
  by (metis de_morgan1 de_morgan2 de_morgan_var1 test_def)

text {* Nitpick refutes the next two lemmas. *}

lemma "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> p \<and> !p \<cdot> x = !p \<cdot> x \<cdot> !p "
  (* nitpick *) oops

lemma test_distrib: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p + q)\<cdot>(q\<cdot>y + !q\<cdot>x) = q\<cdot>y + !q\<cdot>p\<cdot>x"
  (* nitpick *) oops

end

text {*
  We now make the assumption that tests distribute over finite sums of arbitrary elements from the left.
  This can be justified in models such as multirelations and probabilistic predicate transformers.
*}

class near_dioid_test_zerol_dist = near_dioid_tests_zerol +
  assumes weak_distrib_left: "t x \<cdot> (y + z) = t x \<cdot> y + t x \<cdot> z"
begin

lemma weak_distrib_left_var: "test p \<Longrightarrow> p \<cdot> (x + y) = p \<cdot> x + p \<cdot> y"
  by (metis weak_distrib_left test_double_comp_var)

lemma weak_subdistl: "test p \<Longrightarrow> p \<cdot> x \<le> p \<cdot> (x + y)"
  by (metis order_prop weak_distrib_left_var)

lemma weak_subdistl_var: "test p \<Longrightarrow> p \<cdot> x + p \<cdot> y \<le> p \<cdot> (x + y)"
  by (metis add.commute add_lub weak_subdistl)

lemma weak_mult_isol: "test p \<Longrightarrow> x \<le> y \<longrightarrow> p \<cdot> x \<le> p \<cdot> y"
  by (metis less_eq_def weak_subdistl)

lemma weak_mult_isol_var: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p \<le> x \<and> q \<le> y \<longrightarrow> p \<cdot> q \<le> x \<cdot> y"
  by (metis weak_mult_isol mult_isor order_trans)

lemma weak_mult_double_iso: "test p \<Longrightarrow> x \<le> y \<longrightarrow> p \<cdot> x \<cdot> z \<le> p \<cdot> y \<cdot> z"
  by (metis weak_mult_isol mult_isor)

text {* Nitpick refutes the next lemma. *}

lemma test_restrictr: "test p \<Longrightarrow> x \<cdot> p \<le> x"
  (* nitpick *) oops

lemma test_eq2: "test p \<Longrightarrow> z \<le> p\<cdot>x + !p\<cdot>y \<longleftrightarrow> p\<cdot>z \<le> p\<cdot>x \<and> !p\<cdot>z \<le> !p\<cdot>y"
proof auto
  assume assms: "test p" "z \<le> p\<cdot>x + !p\<cdot>y"
  hence "p\<cdot>(p\<cdot>x + !p\<cdot>y) \<le> p\<cdot>x"
    by (metis add_zeror annil mult.assoc weak_distrib_left_var test_comp_mult test_restrictl)
  thus "p\<cdot>z \<le> p\<cdot>x"
    by (metis assms weak_mult_isol order_trans)
next
  assume assms: "test p" "z \<le> p\<cdot>x + !p\<cdot>y"
  hence "!p\<cdot>(p\<cdot>x + !p\<cdot>y) \<le> !p\<cdot>y"
    by (metis mult.assoc test_comp_closed_var weak_distrib_left_var add_zerol annil assms(1) ba4 test_zero_var order_refl test_eq1)
  thus "!p\<cdot>z \<le> !p\<cdot>y"
    by (metis assms test_comp_closed weak_mult_isol order_trans)
next
  assume assms: "test p" "p\<cdot>z \<le> p\<cdot>x" "!p\<cdot>z \<le> !p\<cdot>y"
  thus "z \<le> p \<cdot> x + !p \<cdot> y"
    by (metis assms(2,3) add_iso_var distrib_right' mult_onel test_comp_add)
qed

text {* Nitpick refutes the next three lemmas. *}

lemma test_eq3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
  (* nitpick *) oops

lemma test1: "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

text {* Next, we study tests with commutativity conditions. *}

lemma comm_add: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>(x + y) = (x + y)\<cdot>p"
  by (metis distrib_right' weak_distrib_left_var)

lemma comm_add_var: "\<lbrakk>test p; test q; test r; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>(q\<cdot>x + r\<cdot>y) = (q\<cdot>x + r\<cdot>y)\<cdot>p"
  by (metis comm_add comm_mult mult.assoc)

lemma test_distrib: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p + q)\<cdot>(q\<cdot>y + !q\<cdot>x) = q\<cdot>y + !q\<cdot>p\<cdot>x"
proof -
  assume tests: "test p" "test q"
  hence "(p + q)\<cdot>(q\<cdot>y + !q\<cdot>x) = p\<cdot>q\<cdot>y + p\<cdot>!q\<cdot>x + q\<cdot>q\<cdot>y + q\<cdot>!q\<cdot>x"
    by (metis add_assoc' distrib_right' mult.assoc weak_distrib_left_var)
  also have "... = p\<cdot>q\<cdot>y + p\<cdot>!q\<cdot>x + q\<cdot>y"
    by (metis add.commute add_zerol annil test_comp_mult test_mult_idem_var tests(2))
  also have "... = (p + 1)\<cdot>q\<cdot>y + p\<cdot>!q\<cdot>x"
    by (metis add.commute add.left_commute distrib_right' mult_oner test_mult_comm_var test_one_var tests(2))
  finally show ?thesis
    by (metis mult_oner test_absorb3 test_comp_closed_var test_mult_comm_var test_one_var tests(1) tests(2))
qed

end

text {*
  The following class is relevant for probabilistic Kleene algebras.
*}

class pre_dioid_test_zerol = near_dioid_test_zerol_dist + pre_dioid
begin

subclass pre_dioid_one_zerol
  by (unfold_locales)

lemma test_restrictr: "test p \<Longrightarrow> x \<cdot> p \<le> x"
  by (metis mult_oner subdistl test_comp_uniq)

lemma test_eq3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
  apply default
  apply (metis mult.assoc test_restrictl)
  by (metis eq_iff mult.assoc mult_isol test_mult_idem_var test_restrictr)

lemma test1: "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> x \<cdot> (p + q) \<le> x \<cdot> p + x \<cdot> q"
  (* nitpick *) oops

end

text {*
  The following class is relevant for Demonic Refinement Algebras.
*}

class dioid_tests_zerol = dioid_one_zerol + pre_dioid_test_zerol

begin

lemma test1: "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  by (metis add_0_left add.commute distrib_left mult_oner test_comp_add)

text {* Nitpick refutes the following five lemmas. *}

lemma "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> !p\<cdot>x\<cdot>q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> x\<cdot>!q = !p\<cdot>x\<cdot>!q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> !p\<cdot>x\<cdot>q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> !p\<cdot>x\<cdot>q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  by (metis annil mult.assoc test1 test_comp_mult)

text {* Nitpick refutes the following four lemmas. *}

lemma "\<lbrakk>test p; test q; !p\<cdot>x\<cdot>q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; !p\<cdot>x\<cdot>q = 0\<rbrakk> \<Longrightarrow> x\<cdot>!q = !p\<cdot>x\<cdot>!q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; !p\<cdot>x\<cdot>q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0"
  (* nitpick *) oops

lemma "test p \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> p \<and> !p \<cdot> x = !p \<cdot> x \<cdot> !p \<Longrightarrow> p \<cdot> x = x \<cdot> p"
  (* nitpick *) oops

lemma assumes "test p" and "p\<cdot>x = x\<cdot>p"
  shows "p\<cdot>x = p\<cdot>x\<cdot>p \<and> !p\<cdot>x = !p\<cdot>x\<cdot>!p "
proof
  show "p\<cdot>x = p\<cdot>x\<cdot>p"
    by (metis assms eq_refl test_eq3)
next
  have "!p\<cdot>x = !p\<cdot>x\<cdot>(p + !p)"
    by (metis assms(1) mult_oner test_comp_add)
  thus "!p\<cdot>x = !p\<cdot>x\<cdot>!p" 
    by (metis assms distrib_left mult.assoc add_zerol annil test_comp_mult2)
qed
  
end

text {*
  The following class is relevant for Kleene Algebra with Tests.
*}

class dioid_tests = dioid_tests_zerol + dioid_one_zero
begin

lemma kat_eq1: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x\<cdot>!q = 0) = (p\<cdot>x = p\<cdot>x\<cdot>q)"
  by (metis annir mult.assoc test1 test_comp_mult)

lemma kat_eq2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x\<cdot>!q = 0) = (p\<cdot>x \<le> x\<cdot>q)"
  by (metis kat_eq1 test_eq3)

lemma kat_eq3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x = p\<cdot>x\<cdot>q) = (x\<cdot>!q = !p\<cdot>x\<cdot>!q)"
  by (metis kat_eq1 test_eq4)

text {* Nitpick refutes the next lemma. *}

lemma "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x\<cdot>!q = 0) \<Longrightarrow> (!p\<cdot>x\<cdot>q = 0)"
  (* nitpick *) oops

lemma comm_eq1: "test b \<Longrightarrow> (p\<cdot>b = b\<cdot>p) = (b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0)"
  apply default
  apply (metis add_0_left annil annir test_double_comp_var test_mult_comp mult.assoc)
  by (metis add_0_left ba6 de_morgan1 distrib_right' test_double_comp_var kat_eq1 test_one mult.assoc mult_onel no_trivial_inverse test_comp_closed_var test_not_one)

lemma comm_eq2: "test b \<Longrightarrow> (p\<cdot>!b = !b\<cdot>p) = (b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0)"
  by (metis add_comm comm_eq1 test_comp_closed_var test_double_comp_var)

lemma comm_eq3: "test b \<Longrightarrow> (p\<cdot>b = b\<cdot>p) = (p\<cdot>!b = !b\<cdot>p)"
  by (metis comm_eq1 comm_eq2)

lemma comm_pres: "test p \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>p \<and> !p\<cdot>x = !p\<cdot>x\<cdot>!p \<longleftrightarrow> p\<cdot>x = x\<cdot>p"
  apply (default, metis comm_eq3 kat_eq3)
  by (metis annil ba6 comm_eq3 mult.assoc test_eq4 test_mult_idem_var)

end

end
