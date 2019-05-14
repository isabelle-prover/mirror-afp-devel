(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
(* with contributions from Alexander Bentkamp, Universität des Saarlandes *)

section \<open>Matrices as Vector Spaces\<close>

text \<open>This theory connects the Matrix theory with the VectorSpace theory of
  Holden Lee. As a consequence notions like span, basis, linear dependence, etc. 
  are available for vectors and matrices of the Matrix-theory.\<close>

theory VS_Connect
imports 
  Matrix
  Missing_VectorSpace
  Determinant
begin

hide_const (open) Multiset.mult
hide_const (open) Polynomial.smult
hide_const (open) Modules.module
hide_const (open) subspace
hide_fact (open) subspace_def

named_theorems class_ring_simps

abbreviation class_ring :: "'a :: {times,plus,one,zero} ring" where
  "class_ring \<equiv> \<lparr> carrier = UNIV, mult = (*), one = 1, zero = 0, add = (+) \<rparr>"

interpretation class_semiring: semiring "class_ring :: 'a :: semiring_1 ring"
  rewrites [class_ring_simps]: "carrier class_ring = UNIV"
    and [class_ring_simps]: "mult class_ring = (*)"
    and [class_ring_simps]: "add class_ring = (+)"
    and [class_ring_simps]: "one class_ring = 1"
    and [class_ring_simps]: "zero class_ring = 0"
    and [class_ring_simps]: "pow (class_ring :: 'a ring) = (^)"
    and [class_ring_simps]: "finsum (class_ring :: 'a ring) = sum"
proof -
  let ?r = "class_ring :: 'a ring"
  show "semiring ?r"
    by (unfold_locales, auto simp: field_simps)
  then interpret semiring ?r .
  {
    fix x y
    have "x [^]\<^bsub>?r\<^esub> y = x ^ y"
      by (induct y, auto simp: power_commutes)
  }
  thus "([^]\<^bsub>?r\<^esub>) = (^)" by (intro ext)
  {
    fix f and A :: "'b set"
    have "finsum ?r f A = sum f A"
      by (induct A rule: infinite_finite_induct, auto)
  }
  thus "finsum ?r = sum" by (intro ext)
qed auto 

interpretation class_ring: ring "class_ring :: 'a :: ring_1 ring"
  rewrites "carrier class_ring = UNIV"
    and "mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and [class_ring_simps]: "a_inv (class_ring :: 'a ring) = uminus"
    and [class_ring_simps]: "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum"
proof -
  let ?r = "class_ring :: 'a ring"
  interpret semiring ?r ..
  show "finsum ?r = sum" "pow ?r = (^)" by (simp_all add: class_ring_simps)
  {
    fix x :: 'a
    have "\<exists>y. x + y = 0" by (rule exI[of _ "-x"], auto)
  } note [simp] = this
  show "ring ?r"
    by (unfold_locales, auto simp: field_simps Units_def)
  then interpret ring ?r .
  {
    fix x :: 'a
    have "\<ominus>\<^bsub>?r\<^esub> x = - x" unfolding a_inv_def m_inv_def
      by (rule the1_equality, rule ex1I[of _ "- x"], auto simp: minus_unique)
  } note ainv = this
  thus inv: "a_inv ?r = uminus" by (intro ext)
  {
    fix x y :: 'a
    have "x \<ominus>\<^bsub>?r\<^esub> y = x - y"
      apply (subst a_minus_def)
      using inv by auto
  }
  thus "(\<lambda>x y. x \<ominus>\<^bsub>?r\<^esub> y) = minus" by (intro ext)
qed (auto simp: class_ring_simps)

interpretation class_cring: cring "class_ring :: 'a :: comm_ring_1 ring"
  rewrites "carrier class_ring = UNIV"
    and "mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum"
    and [class_ring_simps]: "finprod class_ring = prod"
proof -
  let ?r = "class_ring :: 'a ring"
  interpret ring ?r ..
  show "cring ?r"
    by (unfold_locales, auto)
  then interpret cring ?r .
  show "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum" by (simp_all add: class_ring_simps)
  {
    fix f and A :: "'b set"
    have "finprod ?r f A = prod f A"
      by (induct A rule: infinite_finite_induct, auto)
  }
  thus "finprod ?r = prod" by (intro ext)
qed (auto simp: class_ring_simps)

definition div0 :: "'a :: {one,plus,times,zero}" where
  "div0 \<equiv> m_inv (class_ring :: 'a ring) 0"

lemma class_field: "field (class_ring :: 'a :: field ring)" (is "field ?r")
proof -
  interpret cring ?r ..
  {
    fix x :: 'a
    have "x \<noteq> 0 \<Longrightarrow> \<exists>xa. xa * x = 1 \<and> x * xa = 1"
      by (intro exI[of _ "inverse x"], auto)
  } note [simp] = this
  show "field ?r" 
    by (unfold_locales, auto simp: Units_def)
qed

interpretation class_field: field "class_ring :: 'a :: field ring"
  rewrites "carrier class_ring = UNIV"
    and "mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv class_ring = uminus"
    and "a_minus class_ring = minus"
    and "pow class_ring = (^)"
    and "finsum class_ring = sum"
    and "finprod class_ring = prod"
    and [class_ring_simps]: "m_inv (class_ring :: 'a ring) x = 
      (if x = 0 then div0 else inverse x)" 
    (* problem that m_inv ?r 0 = inverse 0 is not guaranteed  *)
proof -
  let ?r = "class_ring :: 'a ring"
  show "field ?r" using class_field.
  then interpret field ?r.
  show "a_inv ?r = uminus"
    and "a_minus ?r = minus"
    and "pow ?r = (^)"
    and "finsum ?r = sum"
    and "finprod ?r = prod" by (fact class_ring_simps)+
  show "inv\<^bsub>?r\<^esub> x = (if x = 0 then div0 else inverse x)"
  proof (cases "x = 0")
    case True
    thus ?thesis unfolding div0_def by simp
  next
    case False
    thus ?thesis unfolding m_inv_def
      by (intro the1_equality ex1I[of _ "inverse x"], auto simp: inverse_unique)
  qed
qed (auto simp: class_ring_simps)

lemmas matrix_vs_simps = module_mat_simps class_ring_simps

definition class_field :: "'a :: field ring"
  where [class_ring_simps]: "class_field \<equiv> class_ring"




locale matrix_ring = 
  fixes n :: nat
    and field_type :: "'a :: field itself"
begin
abbreviation R where "R \<equiv> ring_mat TYPE('a) n n"
sublocale ring R
  rewrites "carrier R = carrier_mat n n"
    and "add R = (+)"
    and "mult R = (*)"
    and "one R = 1\<^sub>m n"
    and "zero R = 0\<^sub>m n n"
  using ring_mat by (auto simp: ring_mat_simps)

end

lemma matrix_vs: "vectorspace (class_ring :: 'a :: field ring) (module_mat TYPE('a) nr nc)"
proof -
  interpret abelian_group "module_mat TYPE('a) nr nc"
    by (rule abelian_group_mat)
  show ?thesis unfolding class_field_def
    by (unfold_locales, unfold matrix_vs_simps, 
      auto simp: add_smult_distrib_left_mat add_smult_distrib_right_mat)
qed


locale vec_module =
  fixes f_ty::"'a::comm_ring_1 itself"
  and n::"nat"
begin

abbreviation V where "V \<equiv> module_vec TYPE('a) n"

sublocale Module.module "class_ring :: 'a ring" V
  rewrites "carrier V = carrier_vec n"
    and "add V = (+)"
    and "zero V = 0\<^sub>v n"
    and "module.smult V = (\<cdot>\<^sub>v)"
    and "carrier class_ring = UNIV"
    and "monoid.mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = (-)"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "\<And>X. X \<subseteq> UNIV = True" (* These rewrite rules will clean lemmas *)
    and "\<And>x. x \<in> UNIV = True"
    and "\<And>a A. a \<in> A \<rightarrow> UNIV \<equiv> True"
    and "\<And>P. P \<and> True \<equiv> P"
    and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  apply unfold_locales
  apply (auto simp: module_vec_simps class_ring_simps Units_def add_smult_distrib_vec 
      smult_add_distrib_vec intro!:bexI[of _ "- _"])
  done

end

locale matrix_vs = 
  fixes nr :: nat
    and nc :: nat
    and field_type :: "'a :: field itself"
begin

abbreviation V where "V \<equiv> module_mat TYPE('a) nr nc"
sublocale  
  vectorspace class_ring V
  rewrites "carrier V = carrier_mat nr nc"
    and "add V = (+)"
    and "mult V = (*)"
    and "one V = 1\<^sub>m nr"
    and "zero V = 0\<^sub>m nr nc"
    and "smult V = (\<cdot>\<^sub>m)"
    and "carrier class_ring = UNIV"
    and "mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "m_inv (class_ring :: 'a ring) x = 
      (if x = 0 then div0 else inverse x)"
  by (rule matrix_vs, auto simp: matrix_vs_simps class_field_def)
end

lemma vec_module: "module (class_ring :: 'a :: field ring) (module_vec TYPE('a) n)"
proof -
  interpret abelian_group "module_vec TYPE('a) n"
    apply (unfold_locales)
    unfolding module_vec_def Units_def
    using add_inv_exists_vec by auto
  show ?thesis
    unfolding class_field_def
    apply (unfold_locales)
    unfolding class_ring_simps
    unfolding module_vec_simps
    using add_smult_distrib_vec
    by (auto simp: smult_add_distrib_vec)
qed

lemma vec_vs: "vectorspace (class_ring :: 'a :: field ring) (module_vec TYPE('a) n)"
  unfolding vectorspace_def
  using vec_module class_field 
  by (auto simp: class_field_def)

locale vec_space =
  fixes f_ty::"'a::field itself"
  and n::"nat"
begin

  sublocale vec_module f_ty n.

  sublocale vectorspace class_ring V 
  rewrites cV[simp]: "carrier V = carrier_vec n"
    and [simp]: "add V = (+)"
    and [simp]: "zero V = 0\<^sub>v n"
    and [simp]: "smult V = (\<cdot>\<^sub>v)"
    and "carrier class_ring = UNIV"
    and "mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "m_inv (class_ring :: 'a ring) x = (if x = 0 then div0 else inverse x)"
  using vec_vs
  unfolding class_field_def
  by (auto simp: module_vec_simps class_ring_simps)

lemma finsum_vec[simp]: "finsum_vec TYPE('a) n = finsum V"
  by (force simp: finsum_vec_def monoid_vec_def finsum_def finprod_def)

lemma finsum_scalar_prod_sum:
  assumes f: "f : U \<rightarrow> carrier_vec n"
      and w: "w: carrier_vec n"
  shows "finsum V f U \<bullet> w = sum (\<lambda>u. f u \<bullet> w) U"
  using w f
proof (induct U rule: infinite_finite_induct)
  case (insert u U)
    hence f: "f : U \<rightarrow> carrier_vec n" "f u : carrier_vec n"  by auto
    show ?case
      unfolding finsum_insert[OF insert(1) insert(2) f]
      apply (subst add_scalar_prod_distrib) using insert by auto
qed auto

lemma vec_neg[simp]: assumes "x : carrier_vec n" shows "\<ominus>\<^bsub>V\<^esub> x = - x"
  unfolding a_inv_def m_inv_def apply simp 
  apply (rule the_equality, intro conjI)
  using assms apply auto
  using M.minus_unique uminus_carrier_vec uminus_r_inv_vec by blast

lemma finsum_dim:
  "finite A \<Longrightarrow> f \<in> A \<rightarrow> carrier_vec n \<Longrightarrow> dim_vec (finsum V f A) = n"
proof(induct set:finite)
  case (insert a A)
    hence dfa: "dim_vec (f a) = n" by auto
    have f: "f \<in> A \<rightarrow> carrier_vec n" using insert by auto
    hence fa: "f a \<in> carrier_vec n" using insert by auto
    show ?case
      unfolding finsum_insert[OF insert(1) insert(2) f fa]
      using insert by auto
qed simp

lemma lincomb_dim:
  assumes fin: "finite X"
    and X: "X \<subseteq> carrier_vec n"
  shows "dim_vec (lincomb a X) = n"
proof -
  let ?f = "\<lambda>v. a v \<cdot>\<^sub>v v"
  have f: "?f \<in> X \<rightarrow> carrier_vec n" apply rule using X by auto
  show ?thesis
    unfolding lincomb_def
    using finsum_dim[OF fin f].
qed


lemma finsum_index:
  assumes i: "i < n"
    and f: "f \<in> X \<rightarrow> carrier_vec n"
    and X: "X \<subseteq> carrier_vec n"
  shows "finsum V f X $ i = sum (\<lambda>x. f x $ i) X"
  using X f
proof (induct X rule: infinite_finite_induct)
  case empty
    then show ?case using i by simp next
  case (insert x X)
    then have Xf: "finite X"
      and xX: "x \<notin> X"
      and x: "x \<in> carrier_vec n"
      and X: "X \<subseteq> carrier_vec n"
      and fx: "f x \<in> carrier_vec n"
      and f: "f \<in> X \<rightarrow> carrier_vec n" by auto
    have i2: "i < dim_vec (finsum V f X)"
      using i finsum_closed[OF f] by auto
    have ix: "i < dim_vec x" using x i by auto
    show ?case
      unfolding finsum_insert[OF Xf xX f fx]
      unfolding sum.insert[OF Xf xX]
      unfolding index_add_vec(1)[OF i2]
      using insert lincomb_def
      by auto
qed (insert i, auto)

lemma lincomb_index:
  assumes i: "i < n"
    and X: "X \<subseteq> carrier_vec n"
  shows "lincomb a X $ i = sum (\<lambda>x. a x * x $ i) X"
proof -
  let ?f = "\<lambda>x. a x \<cdot>\<^sub>v x"
  have f: "?f : X \<rightarrow> carrier_vec n" using X by auto
  have point: "\<And>v. v \<in> X \<Longrightarrow> (a v \<cdot>\<^sub>v v) $ i = a v * v $ i" using i X by auto
  show ?thesis
    unfolding lincomb_def
    unfolding finsum_index[OF i f X]
    using point X by simp
qed

lemma append_insert: "set (xs @ [x]) = insert x (set xs)" by simp

lemma lincomb_units:
  assumes i: "i < n" 
  shows "lincomb a (set (unit_vecs n)) $ i = a (unit_vec n i)"
  unfolding lincomb_index[OF i unit_vecs_carrier]
  unfolding unit_vecs_first
proof -
  let ?f = "\<lambda>m i. \<Sum>x\<in>set (unit_vecs_first n m). a x * x $ i"
  have zero:"\<And>m j. m \<le> j \<Longrightarrow> j < n \<Longrightarrow> ?f m j = 0"
  proof -
    fix m
    show "\<And>j. m \<le> j \<Longrightarrow> j < n \<Longrightarrow> ?f m j = 0"
    proof (induction m)
      case (Suc m)
        hence mj:"m\<le>j" and mj':"m\<noteq>j" and jn:"j<n" and mn:"m<n" by auto
        hence mem: "unit_vec n m \<notin> set (unit_vecs_first n m)"
          apply(subst unit_vecs_first_distinct) by auto
        show ?case
          unfolding unit_vecs_first.simps
          unfolding append_insert
          unfolding sum.insert[OF finite_set mem]
          unfolding index_unit_vec(1)[OF mn jn]
          unfolding Suc(1)[OF mj jn] using mj' by simp
    qed simp
  qed
  { fix m
    have "i < m \<Longrightarrow> m \<le> n \<Longrightarrow> ?f m i = a (unit_vec n i)"
    proof (induction m arbitrary: i)
      case (Suc m)
        hence iSm: "i < Suc m" and i:"i<n" and mn: "m<n" by auto
        hence mem: "unit_vec n m \<notin> set (unit_vecs_first n m)"
          apply(subst unit_vecs_first_distinct) by auto
        show ?case
          unfolding unit_vecs_first.simps
          unfolding append_insert
          unfolding sum.insert[OF finite_set mem]
          unfolding index_unit_vec(1)[OF mn i]
          using zero Suc by (cases "i = m",auto)
    qed auto
  }
  thus "?f n i = a (unit_vec n i)" using assms by auto
qed

lemma lincomb_coordinates:
  assumes v: "v : carrier_vec n"
  defines "a \<equiv> (\<lambda>u. v $ (THE i. u = unit_vec n i))"
  shows "lincomb a (set (unit_vecs n)) = v"
proof -
  have a: "a \<in> set (unit_vecs n) \<rightarrow> UNIV" by auto
  have fvu: "\<And>i. i < n \<Longrightarrow> v $ i = a (unit_vec n i)"
    unfolding a_def using unit_vec_eq by auto
  show ?thesis
    apply rule
    unfolding lincomb_dim[OF finite_set unit_vecs_carrier]
    using v lincomb_units fvu
    by auto
qed

lemma span_unit_vecs_is_carrier: "span (set (unit_vecs n)) = carrier_vec n" (is "?L = ?R")
proof (rule;rule)
  fix v assume vsU: "v \<in> ?L" show "v \<in> ?R"
  proof -
    obtain a
      where v: "v = lincomb a (set (unit_vecs n))"
      using vsU
      unfolding finite_span[OF finite_set unit_vecs_carrier] by auto
    thus ?thesis using lincomb_closed[OF unit_vecs_carrier] by auto
  qed
  next fix v::"'a vec" assume v: "v \<in> ?R" show "v \<in> ?L"
    unfolding span_def
    using lincomb_coordinates[OF v,symmetric] by auto
qed

lemma fin_dim[simp]: "fin_dim"
  unfolding fin_dim_def
  apply (intro eqTrueI exI conjI) using span_unit_vecs_is_carrier unit_vecs_carrier by auto

lemma unit_vecs_basis: "basis (set (unit_vecs n))" unfolding basis_def span_unit_vecs_is_carrier
proof (intro conjI)
  show "\<not> lin_dep (set (unit_vecs n))" 
  proof
    assume "lin_dep (set (unit_vecs n))"
    from this[unfolded lin_dep_def] obtain A a v where
      fin: "finite A" and A: "A \<subseteq> set (unit_vecs n)"  
      and lc: "lincomb a A = 0\<^sub>v n" and v: "v \<in> A" and av: "a v \<noteq> 0"      
      by auto
    from v A obtain i where i: "i < n" and vu: "v = unit_vec n i" unfolding unit_vecs_def by auto
    define b where "b = (\<lambda> x. if x \<in> A then a x else 0)"
    have id: "A \<union> (set (unit_vecs n) - A) = set (unit_vecs n)" using A by auto
    from lincomb_index[OF i unit_vecs_carrier]
    have "lincomb b (set (unit_vecs n)) $ i = (\<Sum>x\<in> (A \<union> (set (unit_vecs n) - A)). b x * x $ i)" 
      unfolding id .
    also have "\<dots> = (\<Sum>x\<in> A. b x * x $ i) + (\<Sum>x\<in> set (unit_vecs n) - A. b x * x $ i)"
      by (rule sum.union_disjoint, insert fin, auto)
    also have "(\<Sum>x\<in> A. b x * x $ i) = (\<Sum>x\<in> A. a x * x $ i)"
      by (rule sum.cong, auto simp: b_def)
    also have "\<dots> = lincomb a A $ i" 
      by (subst lincomb_index[OF i], insert A unit_vecs_carrier, auto)
    also have "\<dots> = 0" unfolding lc using i by simp
    also have "(\<Sum>x\<in> set (unit_vecs n) - A. b x * x $ i) = 0"
      by (rule sum.neutral, auto simp: b_def)
    finally have "lincomb b (set (unit_vecs n)) $ i = 0" by simp
    from lincomb_units[OF i, of b, unfolded this]
    have "b v = 0" unfolding vu by simp
    with v av show False unfolding b_def by simp
  qed
qed (insert unit_vecs_carrier, auto)

lemma unit_vecs_length[simp]: "length (unit_vecs n) = n"
  unfolding unit_vecs_def by auto

lemma unit_vecs_distinct: "distinct (unit_vecs n)"
  unfolding distinct_conv_nth unit_vecs_length
proof (intro allI impI)
  fix i j
  assume *: "i < n" "j < n" "i \<noteq> j"
  show "unit_vecs n ! i \<noteq> unit_vecs n ! j"
  proof
    assume "unit_vecs n ! i = unit_vecs n ! j"
    from arg_cong[OF this, of "\<lambda> v. v $ i"] 
    show False using * unfolding unit_vecs_def by auto
  qed
qed

lemma dim_is_n: "dim = n"
  unfolding dim_basis[OF finite_set unit_vecs_basis]
  unfolding distinct_card[OF unit_vecs_distinct]
  by simp

end

locale mat_space =
  vec_space f_ty nc for f_ty::"'a::field itself" and nc::"nat" +
  fixes nr :: "nat"
begin
  abbreviation M where "M \<equiv> ring_mat TYPE('a) nc nr"
end

context vec_space
begin
lemma fin_dim_span:
assumes "finite A" "A \<subseteq> carrier V"
shows "vectorspace.fin_dim class_ring (vs (span A))"
proof -
  have "vectorspace class_ring (span_vs A)"
   using assms span_is_subspace subspace_def subspace_is_vs by simp
  have "A \<subseteq> span A" using assms in_own_span by simp
  have "submodule class_ring (span A) V" using assms span_is_submodule by simp
  have "LinearCombinations.module.span class_ring (vs (span A)) A = carrier (vs (span A))"
    using  span_li_not_depend(1)[OF \<open>A \<subseteq> span A\<close> \<open>submodule class_ring (span A) V\<close>] by auto
  then show ?thesis unfolding vectorspace.fin_dim_def[OF \<open>vectorspace class_ring (span_vs A)\<close>]
    using List.finite_set \<open>A \<subseteq> span A\<close> \<open>vectorspace class_ring (vs (span A))\<close>
    vec_vs vectorspace.carrier_vs_is_self[OF \<open>vectorspace class_ring (span_vs A)\<close>] using assms(1) by auto
qed

lemma fin_dim_span_cols:
assumes "A \<in> carrier_mat n nc"
shows "vectorspace.fin_dim class_ring (vs (span (set (cols A))))"
  using fin_dim_span cols_dim List.finite_set assms carrier_matD(1) module_vec_simps(3) by force
end

context vec_module
begin

lemma lincomb_list_as_mat_mult:
  assumes "\<forall>w \<in> set ws. dim_vec w = n"
  shows "lincomb_list c ws = mat_of_cols n ws *\<^sub>v vec (length ws) c" (is "?l ws c = ?r ws c")
proof (insert assms, induct ws arbitrary: c)
  case Nil
  then show ?case by (auto simp: mult_mat_vec_def scalar_prod_def)
next
  case (Cons w ws)
  { fix i assume i: "i < n"
    have "?l (w#ws) c = c 0 \<cdot>\<^sub>v w + mat_of_cols n ws *\<^sub>v vec (length ws) (c \<circ> Suc)"
      by (simp add: Cons o_def)
    also have "\<dots> $ i = ?r (w#ws) c $ i"
      using Cons i index_smult_vec
      by (simp add: mat_of_cols_Cons_index_0 mat_of_cols_Cons_index_Suc o_def vec_Suc mult_mat_vec_def row_def length_Cons)
    finally have "?l (w#ws) c $ i = \<dots>".
  }
  with Cons show ?case by (intro eq_vecI, auto)
qed

lemma lincomb_vec_diff_add:
    assumes A: "A \<subseteq> carrier_vec n"
    and BA: "B \<subseteq> A" and fin_A: "finite A" 
    and f: "f \<in> A \<rightarrow> UNIV" shows "lincomb f A = lincomb f (A-B) + lincomb f B"
proof -
  have "A - B \<union> B = A" using BA by auto
  hence "lincomb f A = lincomb f (A - B \<union> B)"  by simp
  also have "... = lincomb f (A-B) + lincomb f B"
    by (rule lincomb_union, insert assms, auto intro: finite_subset)
  finally show ?thesis .
qed

lemma dim_sumlist:
  assumes "\<forall>x\<in>set xs. dim_vec x = n"
  shows "dim_vec (M.sumlist xs) = n" using assms by (induct xs, auto)

lemma sumlist_nth:
  assumes "\<forall>x\<in>set xs. dim_vec x = n" and "i<n"
  shows "(M.sumlist xs) $ i= sum (\<lambda>j. (xs ! j) $ i) {0..<length xs}"
  using assms
proof (induct xs rule: rev_induct)
  case (snoc a xs) 
  have [simp]: "x \<in> carrier_vec n" if x: "x\<in>set xs" for x 
    using snoc.prems x unfolding carrier_vec_def by auto
  have [simp]: "a \<in> carrier_vec n" 
    using snoc.prems unfolding carrier_vec_def by auto
  have hyp: "M.sumlist xs $ i = (\<Sum>j = 0..<length xs. xs ! j $ i)" 
    by (rule snoc.hyps, auto simp add: snoc.prems)  
  have "M.sumlist (xs @ [a]) = M.sumlist xs + M.sumlist [a]" 
    by (rule M.sumlist_append, auto simp add: snoc.prems)
  also have "... = M.sumlist xs + a" by auto
  also have "... $ i = (M.sumlist xs $ i) + (a $ i)" 
    by (rule index_add_vec(1), auto simp add: snoc.prems)
  also have "... =  (\<Sum>j = 0..<length xs. xs ! j $ i) + (a $ i)" unfolding hyp by simp
  also have "... = (\<Sum>j = 0..<length (xs @ [a]). (xs @ [a]) ! j $ i)"
    by (auto, rule sum.cong, auto simp add: nth_append)     
  finally show ?case .
qed auto

lemma lincomb_as_lincomb_list_distinct:
  assumes s: "set ws \<subseteq> carrier_vec n" and d: "distinct ws"
  shows "lincomb f (set ws) = lincomb_list (\<lambda>i. f (ws ! i)) ws"
proof (insert assms, induct ws)
  case Nil
  then show ?case by auto
next
  case (Cons a ws)
  have [simp]: "\<And>v. v \<in> set ws \<Longrightarrow> v \<in> carrier_vec n" using Cons.prems(1) by auto
  then have ws: "set ws \<subseteq> carrier_vec n" by auto
  have hyp: "lincomb f (set (ws)) = lincomb_list (\<lambda>i. f (ws ! i)) ws"
  proof (intro Cons.hyps ws)
    show "distinct ws" using Cons.prems(2) by auto
  qed  
  have "(map (\<lambda>i. f (ws ! i) \<cdot>\<^sub>v ws ! i) [0..<length ws]) = (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)"
    by (intro nth_equalityI, auto)
  with ws have sumlist_rw: "sumlist (map (\<lambda>i. f (ws ! i) \<cdot>\<^sub>v ws ! i) [0..<length ws])
    = sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)"
    by (subst (1 2) sumlist_as_summset, auto)
  have "lincomb f (set (a # ws)) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set (a # ws). f v \<cdot>\<^sub>v v)" unfolding lincomb_def ..
  also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in> insert a (set ws). f v \<cdot>\<^sub>v v)" by simp
  also have "... = (f a \<cdot>\<^sub>v a) + (\<Oplus>\<^bsub>V\<^esub>v\<in> (set ws). f v \<cdot>\<^sub>v v)"
    by (rule finsum_insert, insert Cons.prems, auto)
  also have "... = f a \<cdot>\<^sub>v a + lincomb_list (\<lambda>i. f (ws ! i)) ws" using hyp lincomb_def by auto
  also have "... = f a \<cdot>\<^sub>v a + sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)" 
    unfolding lincomb_list_def sumlist_rw by auto
  also have "... = sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) (a # ws))"
  proof -
    let ?a = "(map (\<lambda>v. f v \<cdot>\<^sub>v v) [a])"
    have a: "a \<in> carrier_vec n" using Cons.prems(1) by auto
    have "f a \<cdot>\<^sub>v a = sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) [a])" using Cons.prems(1) by auto
    hence "f a \<cdot>\<^sub>v a + sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws) 
      = sumlist ?a + sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)" by simp
    also have "... = sumlist (?a @ (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws))"
      by (rule sumlist_append[symmetric], auto simp add: a)
    finally show ?thesis by auto
  qed
  also have "... = sumlist (map (\<lambda>i. f ((a # ws) ! i) \<cdot>\<^sub>v (a # ws) ! i) [0..<length (a # ws)])"
  proof -
    have u: "(map (\<lambda>i. f ((a # ws) ! i) \<cdot>\<^sub>v (a # ws) ! i) [0..<length (a # ws)]) 
        = (map (\<lambda>v. f v \<cdot>\<^sub>v v) (a # ws))"
    proof (intro nth_equalityI, goal_cases)
      case (2 i) thus ?case by (smt length_map map_nth nth_map)
    qed auto
    show ?thesis unfolding u ..
  qed
  also have "... = lincomb_list (\<lambda>i. f ((a # ws) ! i)) (a # ws)"
    unfolding lincomb_list_def ..
  finally show ?case .
qed

end

locale idom_vec = vec_module f_ty for f_ty :: "'a :: idom itself"
begin

lemma lin_dep_cols_imp_det_0':
  fixes ws
  defines "A \<equiv> mat_of_cols n ws"
  assumes dimv_ws: "\<forall>w\<in>set ws. dim_vec w = n"
  assumes A: "A \<in> carrier_mat n n" and ld_cols: "lin_dep (set (cols A))"
  shows  "det A = 0"
proof (cases "distinct ws")
  case False
  obtain i j where ij: "i\<noteq>j" and c: "col A i = col A j" and i: "i<n" and j: "j<n" 
    using False A unfolding A_def
    by (metis dimv_ws distinct_conv_nth carrier_matD(2) 
        col_mat_of_cols mat_of_cols_carrier(3) nth_mem carrier_vecI)
  show ?thesis by (rule det_identical_columns[OF A ij i j c])  
next
  case True
  have d1[simp]: "\<And>x. x \<in> set ws \<Longrightarrow> x \<in> carrier_vec n" using dimv_ws by auto 
  obtain A' f' v where f'_in: "f' \<in> A' \<rightarrow> UNIV" 
    and lc_f': "lincomb f' A' = 0\<^sub>v n" and f'_v: "f' v \<noteq> 0"
    and v_A': "v \<in> A'" and A'_in_rows: "A' \<subseteq> set (cols A)" 
    using ld_cols unfolding lin_dep_def by auto
  define f where "f \<equiv> \<lambda>x. if x \<notin> A' then 0 else f' x"
  have f_in: "f \<in> (set (cols A)) \<rightarrow> UNIV" using f'_in by auto
  have A'_in_carrier: "A' \<subseteq> carrier_vec n"
    by (metis (no_types) A'_in_rows A_def cols_dim carrier_matD(1) mat_of_cols_carrier(1) subset_trans)
  have lc_f: "lincomb f (set (cols A)) = 0\<^sub>v n"   
  proof -
    have l1: "lincomb f (set (cols A) - A') = 0\<^sub>v n"
      by (rule lincomb_zero, auto simp add: f_def, insert A cols_dim, blast)
    have l2: "lincomb f A' = 0\<^sub>v n " using lc_f' unfolding f_def using A'_in_carrier by auto
    have "lincomb f (set (cols A)) = lincomb f (set (cols A) - A') + lincomb f A'"
    proof (rule lincomb_vec_diff_add)
      show "set (cols A) \<subseteq> carrier_vec n"
        using A cols_dim by blast
      show "A' \<subseteq> set (cols A)"
        using A'_in_rows by blast
    qed auto
    also have "... =  0\<^sub>v n" using l1 l2 by auto
    finally show ?thesis .
  qed
  have v_in: "v \<in> (set (cols A))" using v_A' A'_in_rows by auto 
  have fv: "f v \<noteq> 0" using f'_v v_A' unfolding f_def by auto
  let ?c = "(\<lambda>i. f (ws ! i))"
  have "lincomb f (set ws) = lincomb_list ?c ws"
    by (rule lincomb_as_lincomb_list_distinct[OF _ True], auto)
  have "\<exists>v.  v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> A *\<^sub>v v = 0\<^sub>v n"
  proof (rule exI[of _ " vec (length ws) ?c"], rule conjI)
    show "vec (length ws) ?c \<in> carrier_vec n" using A A_def by auto
    have vec_not0: "vec (length ws) ?c \<noteq> 0\<^sub>v n"
    proof -
      obtain i where ws_i: "(ws ! i) = v" and i: "i<length ws" using v_in unfolding A_def        
        by (metis d1 cols_mat_of_cols in_set_conv_nth subset_eq)
      have "vec (length ws) ?c $ i = ?c i" by (rule index_vec[OF i])
      also have "... = f v" using ws_i by simp
      also have "... \<noteq> 0" using fv by simp
      finally show ?thesis
        using A A_def i by fastforce
    qed
    have "A *\<^sub>v vec (length ws) ?c = mat_of_cols n ws *\<^sub>v vec (length ws) ?c" unfolding A_def ..
    also have "... = lincomb_list ?c ws" by (rule lincomb_list_as_mat_mult[symmetric, OF dimv_ws])
    also have "... = lincomb f (set ws)" 
      by (rule lincomb_as_lincomb_list_distinct[symmetric, OF _ True], auto)
    also have "... =  0\<^sub>v n" 
      using lc_f unfolding A_def using A by (simp add: subset_code(1))
    finally show "vec (length ws) (\<lambda>i. f (ws ! i)) \<noteq> 0\<^sub>v n \<and> A *\<^sub>v vec (length ws) (\<lambda>i. f (ws ! i)) = 0\<^sub>v n"
      using vec_not0 by fast
  qed 
  thus ?thesis unfolding det_0_iff_vec_prod_zero[OF A] .
qed

lemma lin_dep_cols_imp_det_0:
  assumes A: "A \<in> carrier_mat n n" and ld: "lin_dep (set (cols A))"
  shows "det A = 0" 
proof -
  have col_rw: "(cols (mat_of_cols n (cols A))) = cols A"
    using A by auto
  have m: "mat_of_cols n (cols A) = A" using A by auto
  show ?thesis
  by (rule A lin_dep_cols_imp_det_0'[of "cols A", unfolded col_rw, unfolded m, OF _ A ld])
     (metis A cols_dim carrier_matD(1) subsetCE carrier_vecD)
qed

corollary lin_dep_rows_imp_det_0:
  assumes A: "A \<in> carrier_mat n n" and ld: "lin_dep (set (rows A))"
  shows "det A = 0" 
  by (subst det_transpose[OF A, symmetric], rule lin_dep_cols_imp_det_0, auto simp add: ld A)

lemma det_not_0_imp_lin_indpt_rows:
  assumes A: "A \<in> carrier_mat n n" and det: "det A \<noteq> 0"  
  shows "lin_indpt (set (rows A))"
    using lin_dep_rows_imp_det_0[OF A] det by auto

lemma upper_triangular_imp_lin_indpt_rows:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "lin_indpt (set (rows A))"
  using det_not_0_imp_lin_indpt_rows upper_triangular_imp_det_eq_0_iff assms
  by auto

(* Connection from set-based to list-based *)

lemma lincomb_as_lincomb_list:
  fixes ws f
  assumes s: "set ws \<subseteq> carrier_vec n"
  shows "lincomb f (set ws) = lincomb_list (\<lambda>i. if \<exists>j<i. ws!i = ws!j then 0 else f (ws ! i)) ws"
  using assms
proof (induct ws rule: rev_induct)
  case (snoc a ws)
  let ?f = "\<lambda>i. if \<exists>j<i. ws ! i = ws ! j then 0 else f (ws ! i)"
  let ?g = "\<lambda>i. (if \<exists>j<i. (ws @ [a]) ! i = (ws @ [a]) ! j then 0 else f ((ws @ [a]) ! i)) \<cdot>\<^sub>v (ws @ [a]) ! i"
  let ?g2= "(\<lambda>i. (if \<exists>j<i. ws ! i = ws ! j then 0 else f (ws ! i)) \<cdot>\<^sub>v ws ! i)"
  have [simp]: "\<And>v. v \<in> set ws \<Longrightarrow> v \<in> carrier_vec n" using snoc.prems(1) by auto
  then have ws: "set ws \<subseteq> carrier_vec n" by auto
  have hyp: "lincomb f (set ws) = lincomb_list ?f ws"
    by (intro snoc.hyps ws)  
  show ?case
  proof (cases "a\<in>set ws")
    case True    
    have g_length: "?g (length ws) = 0\<^sub>v n" using True
      by (auto, metis in_set_conv_nth nth_append)
    have "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [?g (length ws)]"
       by auto
    also have "... = (map ?g [0..<length ws]) @ [0\<^sub>v n]" using g_length by simp
    finally have map_rw: "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [0\<^sub>v n]" .
    have "M.sumlist (map ?g2 [0..<length ws]) = M.sumlist (map ?g [0..<length ws])"
      by (rule arg_cong[of _ _ "M.sumlist"], intro nth_equalityI, auto simp add: nth_append)
    also have "... =  M.sumlist (map ?g [0..<length ws]) + 0\<^sub>v n "
      by (metis M.r_zero calculation hyp lincomb_closed lincomb_list_def ws)
    also have "... = M.sumlist (map ?g [0..<length ws] @ [0\<^sub>v n])" 
      by (rule M.sumlist_snoc[symmetric], auto simp add: nth_append)
    finally have summlist_rw: "M.sumlist (map ?g2 [0..<length ws]) 
      = M.sumlist (map ?g [0..<length ws] @ [0\<^sub>v n])" .
    have "lincomb f (set (ws @ [a])) = lincomb f (set ws)" using True unfolding lincomb_def
      by (simp add: insert_absorb)
    thus ?thesis 
      unfolding hyp lincomb_list_def map_rw summlist_rw
      by auto
  next
    case False    
    have g_length: "?g (length ws) = f a \<cdot>\<^sub>v a" using False by (auto simp add: nth_append)
    have "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [?g (length ws)]"
       by auto
    also have "... = (map ?g [0..<length ws]) @ [(f a \<cdot>\<^sub>v a)]" using g_length by simp
    finally have map_rw: "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [(f a \<cdot>\<^sub>v a)]" .
    have summlist_rw: "M.sumlist (map ?g2 [0..<length ws]) = M.sumlist (map ?g [0..<length ws])"
      by (rule arg_cong[of _ _ "M.sumlist"], intro nth_equalityI, auto simp add: nth_append)
    have "lincomb f (set (ws @ [a])) = lincomb f (set (a # ws))" by auto
    also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in>set (a # ws). f v \<cdot>\<^sub>v v)" unfolding lincomb_def ..
    also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in> insert a (set ws). f v \<cdot>\<^sub>v v)" by simp    
    also have "... = (f a \<cdot>\<^sub>v a) + (\<Oplus>\<^bsub>V\<^esub>v\<in> (set ws). f v \<cdot>\<^sub>v v)"
    proof (rule finsum_insert)
      show "finite (set ws)" by auto
      show "a \<notin> set ws" using False by auto
      show "(\<lambda>v. f v \<cdot>\<^sub>v v) \<in> set ws \<rightarrow> carrier_vec n"
        using snoc.prems(1) by auto
      show "f a \<cdot>\<^sub>v a \<in> carrier_vec n" using snoc.prems by auto
    qed
    also have "... = (f a \<cdot>\<^sub>v a) + lincomb f (set ws)" unfolding lincomb_def ..
    also have "... = (f a \<cdot>\<^sub>v a) + lincomb_list ?f ws" using hyp by auto
    also have "... =  lincomb_list ?f ws  + (f a \<cdot>\<^sub>v a)"
      using M.add.m_comm lincomb_list_carrier snoc.prems by auto
    also have "... = lincomb_list (\<lambda>i. if \<exists>j<i. (ws @ [a]) ! i 
      = (ws @ [a]) ! j then 0 else f ((ws @ [a]) ! i)) (ws @ [a])" 
    proof (unfold lincomb_list_def map_rw summlist_rw, rule M.sumlist_snoc[symmetric])
      show "set (map ?g [0..<length ws]) \<subseteq> carrier_vec n" using snoc.prems
        by (auto simp add: nth_append)
      show "f a \<cdot>\<^sub>v a \<in> carrier_vec n"
        using snoc.prems by auto
    qed
    finally show ?thesis .
  qed
qed auto

lemma span_list_as_span:
  assumes "set vs \<subseteq> carrier_vec n"
  shows "span_list vs = span (set vs)"
  using assms
proof (auto simp: span_list_def span_def)
  fix f show "\<exists>a A. lincomb_list f vs = lincomb a A \<and> finite A \<and> A \<subseteq> set vs" 
    using assms lincomb_list_as_lincomb by auto
next
  fix f::"'a vec \<Rightarrow>'a" and A assume fA: "finite A" and A: "A \<subseteq> set vs" 
  have [simp]: "x \<in> carrier_vec n" if x: "x \<in> A" for x using A x assms by auto
  have [simp]:  "v \<in> carrier_vec n" if v: "v \<in> set vs" for v using assms v by auto
  have set_vs_Un: "((set vs) - A) \<union> A = set vs" using A by auto
  let ?f = "(\<lambda>x. if x\<in>(set vs) - A then 0 else f x)"
  have f0: "(\<Oplus>\<^bsub>V\<^esub>v\<in>(set vs) - A. ?f v \<cdot>\<^sub>v v) = 0\<^sub>v n" by (rule M.finsum_all0, auto)  
  have "lincomb f A = lincomb ?f A"
    by (auto simp add: lincomb_def intro!: finsum_cong2)
  also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in>(set vs) - A. ?f v \<cdot>\<^sub>v v) + (\<Oplus>\<^bsub>V\<^esub>v\<in>A. ?f v \<cdot>\<^sub>v v)" 
    unfolding f0 lincomb_def by auto
  also have "... = lincomb ?f (((set vs) - A) \<union> A)" 
    unfolding lincomb_def 
    by (rule M.finsum_Un_disjoint[symmetric], auto simp add: fA)
  also have "... = lincomb ?f (set vs)" using set_vs_Un by auto
  finally have "lincomb f A = lincomb ?f (set vs)" .    
  with lincomb_as_lincomb_list[OF assms] 
  show "\<exists>c. lincomb f A = lincomb_list c vs" by auto    
qed

lemma in_spanI[intro]:
  assumes "v = lincomb a A" "finite A" "A \<subseteq> W"
  shows "v \<in> span W"
unfolding span_def using assms by auto
lemma in_spanE:
  assumes "v \<in> span W"
  shows "\<exists> a A. v = lincomb a A \<and> finite A \<and> A \<subseteq> W"
using assms unfolding span_def by auto

declare in_own_span[intro]

lemma smult_in_span:
  assumes "W \<subseteq> carrier_vec n" and insp: "x \<in> span W"
  shows "c \<cdot>\<^sub>v x \<in> span W"
proof -
  from in_spanE[OF insp] obtain a A where a: "x = lincomb a A" "finite A" "A \<subseteq> W" by blast
  have "c \<cdot>\<^sub>v x = lincomb (\<lambda> x. c * a x) A" using a(1) unfolding lincomb_def a
    apply(subst finsum_smult) using assms a by (auto simp:smult_smult_assoc)
  thus "c \<cdot>\<^sub>v x \<in> span W" using a(2,3) by auto
qed

lemma span_subsetI: assumes ws: "ws \<subseteq> carrier_vec n" 
  "us \<subseteq> span ws" 
shows "span us \<subseteq> span ws" 
  by (simp add: assms(1) span_is_submodule span_is_subset subsetI ws)

end

context vec_space begin
sublocale idom_vec.

lemma sumlist_in_span: assumes W: "W \<subseteq> carrier_vec n"  
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> span W) \<Longrightarrow> sumlist xs \<in> span W" 
proof (induct xs)
  case Nil
  thus ?case using W by force
next
  case (Cons x xs)
  from span_is_subset2[OF W] Cons(2) have xs: "x \<in> carrier_vec n" "set xs \<subseteq> carrier_vec n" by auto
  from span_add1[OF W Cons(2)[of x] Cons(1)[OF Cons(2)]]
  have "x + sumlist xs \<in> span W" by auto
  also have "x + sumlist xs = sumlist ([x] @ xs)" 
    by (subst sumlist_append, insert xs, auto)
  finally show ?case by simp
qed

lemma span_span[simp]:
  assumes "W \<subseteq> carrier_vec n"
  shows "span (span W) = span W"
proof(standard,standard,goal_cases)
  case (1 x) with in_spanE obtain a A where a: "x = lincomb a A" "finite A" "A \<subseteq> span W" by blast
  from a(3) assms have AC:"A \<subseteq> carrier_vec n" by auto
  show ?case unfolding a(1)[unfolded lincomb_def]
  proof(insert a(3),atomize (full),rule finite_induct[OF a(2)],goal_cases)
    case 1
    then show ?case using span_zero by auto
  next
    case (2 x F)
    { assume F:"insert x F \<subseteq> span W"
      hence "a x \<cdot>\<^sub>v x \<in> span W" by (intro smult_in_span[OF assms],auto)
      hence "a x \<cdot>\<^sub>v x + (\<Oplus>\<^bsub>V\<^esub>v\<in>F. a v \<cdot>\<^sub>v v) \<in> span W"
        using span_add1 F 2 assms by auto
      hence "(\<Oplus>\<^bsub>V\<^esub>v\<in>insert x F. a v \<cdot>\<^sub>v v) \<in> span W"
        apply(subst M.finsum_insert[OF 2(1,2)]) using F assms by auto
    }
    then show ?case by auto
  qed
next
  case 2
  show ?case using assms by(intro in_own_span, auto)
qed


lemma upper_triangular_imp_basis:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "basis (set (rows A))"
  using upper_triangular_imp_distinct[OF assms]
  using upper_triangular_imp_lin_indpt_rows[OF assms] A
  by (auto intro: dim_li_is_basis simp: distinct_card dim_is_n set_rows_carrier)
end


end
