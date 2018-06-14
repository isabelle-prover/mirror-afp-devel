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
  VectorSpace.VectorSpace
begin

hide_const (open) Modules.module

named_theorems class_ring_simps

abbreviation class_ring :: "'a :: {times,plus,one,zero} ring" where
  "class_ring \<equiv> \<lparr> carrier = UNIV, mult = ( * ), one = 1, zero = 0, add = (+) \<rparr>"

interpretation class_semiring: semiring "class_ring :: 'a :: semiring_1 ring"
  rewrites [class_ring_simps]: "carrier class_ring = UNIV"
    and [class_ring_simps]: "mult class_ring = ( * )"
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
    and "mult class_ring = ( * )"
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
    and "mult class_ring = ( * )"
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
    and "mult class_ring = ( * )"
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
    and "mult R = ( * )"
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
    and "monoid.mult class_ring = ( * )"
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
    and "mult V = ( * )"
    and "one V = 1\<^sub>m nr"
    and "zero V = 0\<^sub>m nr nc"
    and "smult V = (\<cdot>\<^sub>m)"
    and "carrier class_ring = UNIV"
    and "mult class_ring = ( * )"
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
    and "mult class_ring = ( * )"
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

lemma (in vec_space) fin_dim_span:
assumes "finite A" "A \<subseteq> carrier V"
shows "vectorspace.fin_dim class_ring (vs (span A))"
proof -
  have "vectorspace class_ring (span_vs A)"
   using assms span_is_subspace subspace_def subspace_is_vs by simp
  have "A \<subseteq> span A" using assms in_own_span by simp
  have "submodule class_ring (span A) V" using assms span_is_submodule by simp
  have "LinearCombinations.module.span class_ring (vs (span A)) A = carrier (vs (span A))"
    using  span_li_not_depend(1)[OF `A \<subseteq> span A` `submodule class_ring (span A) V`] by auto
  then show ?thesis unfolding vectorspace.fin_dim_def[OF `vectorspace class_ring (span_vs A)`]
    using List.finite_set \<open>A \<subseteq> span A\<close> \<open>vectorspace class_ring (vs (span A))\<close>
    vec_vs vectorspace.carrier_vs_is_self[OF `vectorspace class_ring (span_vs A)`] using assms(1) by auto
qed

lemma (in vec_space) fin_dim_span_cols:
assumes "A \<in> carrier_mat n nc"
shows "vectorspace.fin_dim class_ring (vs (span (set (cols A))))"
using fin_dim_span cols_dim List.finite_set assms carrier_matD(1) module_vec_simps(3) by force


  
end
