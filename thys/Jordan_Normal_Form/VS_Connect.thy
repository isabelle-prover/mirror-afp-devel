(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Matrices as Vector Spaces\<close>

text \<open>This theory connects the Matrix theory with the VectorSpace theory of
  Holden Lee. As a consequence notions like span, basis, linear dependence, etc. 
  are available for vectors and matrices of the Matrix-theory.\<close>

theory VS_Connect
imports 
  Matrix
  "../VectorSpace/VectorSpace"
begin

named_theorems class_ring_simps

abbreviation class_ring :: "'a :: {times,plus,one,zero} ring" where
  "class_ring \<equiv> \<lparr> carrier = UNIV, mult = op *, one = 1, zero = 0, add = op + \<rparr>"

interpretation class_semiring: semiring "class_ring :: 'a :: semiring_1 ring"
  rewrites [class_ring_simps]: "carrier class_ring = UNIV"
    and [class_ring_simps]: "mult class_ring = op *"
    and [class_ring_simps]: "add class_ring = op +"
    and [class_ring_simps]: "one class_ring = 1"
    and [class_ring_simps]: "zero class_ring = 0"
    and [class_ring_simps]: "pow (class_ring :: 'a ring) = op ^"
    and [class_ring_simps]: "finsum (class_ring :: 'a ring) = sum"
proof -
  let ?r = "class_ring :: 'a ring"
  show "semiring ?r"
    by (unfold_locales, auto simp: field_simps)
  then interpret semiring ?r .
  {
    fix x y
    have "x (^)\<^bsub>?r\<^esub> y = x ^ y"
      by (induct y, auto simp: power_commutes)
  }
  thus "op (^)\<^bsub>?r\<^esub> = op ^" by (intro ext)
  {
    fix f and A :: "'b set"
    have "finsum ?r f A = sum f A"
      by (induct A rule: infinite_finite_induct, auto)
  }
  thus "finsum ?r = sum" by (intro ext)
qed auto 

interpretation class_ring: ring "class_ring :: 'a :: ring_1 ring"
  rewrites "carrier class_ring = UNIV"
    and "mult class_ring = op *"
    and "add class_ring = op +"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and [class_ring_simps]: "a_inv (class_ring :: 'a ring) = uminus"
    and [class_ring_simps]: "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = op ^"
    and "finsum (class_ring :: 'a ring) = sum"
proof -
  let ?r = "class_ring :: 'a ring"
  interpret semiring ?r ..
  show "finsum ?r = sum" "pow ?r = op ^" by (simp_all add: class_ring_simps)
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
  thus "a_inv ?r = uminus" by (intro ext)
  {
    fix x y :: 'a
    have "x \<ominus>\<^bsub>?r\<^esub> y = x - y" 
      by (subst a_minus_def[of x ?r y], (auto)[2], subst ainv, auto)
  }
  thus "op \<ominus>\<^bsub>?r\<^esub> = minus" by (intro ext)
qed (auto simp: class_ring_simps)

interpretation class_cring: cring "class_ring :: 'a :: comm_ring_1 ring"
  rewrites "carrier class_ring = UNIV"
    and "mult class_ring = op *"
    and "add class_ring = op +"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = op ^"
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
    and "pow (class_ring :: 'a ring) = op ^"
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
    and "mult class_ring = op *"
    and "add class_ring = op +"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv class_ring = uminus"
    and "a_minus class_ring = minus"
    and "pow class_ring = op ^"
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
    and "pow ?r = op ^"
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

lemmas matrix_vs_simps = mat_module_simps class_ring_simps

definition class_field :: "'a :: field ring"
  where [class_ring_simps]: "class_field \<equiv> class_ring"




locale matrix_ring = 
  fixes n :: nat
    and field_type :: "'a :: field itself"
begin
abbreviation R where "R \<equiv> ring\<^sub>m TYPE('a) n n"
sublocale ring R
  rewrites "carrier R = carrier\<^sub>m n n"
    and "add R = op \<oplus>\<^sub>m"
    and "mult R = op \<otimes>\<^sub>m"
    and "one R = \<one>\<^sub>m n"
    and "zero R = \<zero>\<^sub>m n n"
  using mat_ring by (auto simp: mat_ring_simps)

end

lemma matrix_vs: "vectorspace (class_ring :: 'a :: field ring) (module\<^sub>m TYPE('a) nr nc)"
proof -
  interpret abelian_group "module\<^sub>m TYPE('a) nr nc"
    by (rule mat_module_abelian_group)
  show ?thesis unfolding class_field_def
    by (unfold_locales, unfold matrix_vs_simps, 
      auto simp: mat_add_scalar_distrib_left mat_add_scalar_distrib_right)
qed


locale vec_module =
  fixes f_ty::"'a::comm_ring_1 itself"
  and n::"nat"
begin

abbreviation V where "V \<equiv> module\<^sub>v TYPE('a) n"

sublocale module "class_ring :: 'a ring" V
  rewrites "carrier V = carrier\<^sub>v n"
    and "add V = op \<oplus>\<^sub>v"
    and "zero V = \<zero>\<^sub>v n"
    and "module.smult V = op \<odot>\<^sub>v"
    and "carrier class_ring = UNIV"
    and "monoid.mult class_ring = op *"
    and "add class_ring = op +"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = op -"
    and "pow (class_ring :: 'a ring) = op ^"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "\<And>X. X \<subseteq> UNIV = True" (* These rewrite rules will clean lemmas *)
    and "\<And>x. x \<in> UNIV = True"
    and "\<And>a A. a \<in> A \<rightarrow> UNIV \<equiv> True"
    and "\<And>P. P \<and> True \<equiv> P"
    and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  apply unfold_locales
  apply (auto simp: vec_module_simps class_ring_simps Units_def vec_smult_l_distr vec_smult_r_distr intro!:bexI[of _ "\<ominus>\<^sub>v _"])
  done

end

locale matrix_vs = 
  fixes nr :: nat
    and nc :: nat
    and field_type :: "'a :: field itself"
begin

abbreviation V where "V \<equiv> module\<^sub>m TYPE('a) nr nc"
sublocale  
  vectorspace class_ring V
  rewrites "carrier V = carrier\<^sub>m nr nc"
    and "add V = op \<oplus>\<^sub>m"
    and "mult V = op \<otimes>\<^sub>m"
    and "one V = \<one>\<^sub>m nr"
    and "zero V = \<zero>\<^sub>m nr nc"
    and "smult V = op \<odot>\<^sub>m"
    and "carrier class_ring = UNIV"
    and "mult class_ring = op *"
    and "add class_ring = op +"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = op ^"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "m_inv (class_ring :: 'a ring) x = 
      (if x = 0 then div0 else inverse x)"
  by (rule matrix_vs, auto simp: matrix_vs_simps class_field_def)
end

lemma vec_module: "module (class_ring :: 'a :: field ring) (module\<^sub>v TYPE('a) n)"
proof -
  interpret abelian_group "module\<^sub>v TYPE('a) n"
    apply (unfold_locales)
    unfolding vec_module_def Units_def
    using vec_add_inv_exists by auto
  show ?thesis
    unfolding class_field_def
    apply (unfold_locales)
    unfolding class_ring_simps
    unfolding vec_module_simps
    using vec_smult_l_distr
    by (auto simp:  vec_smult_r_distr)
qed

lemma vec_vs: "vectorspace (class_ring :: 'a :: field ring) (module\<^sub>v TYPE('a) n)"
  unfolding vectorspace_def
  using vec_module class_field 
  by (auto simp: class_field_def)

locale vec_space =
  fixes f_ty::"'a::field itself"
  and n::"nat"
begin

  sublocale vec_module f_ty n.

  sublocale vectorspace class_ring V 
  rewrites cV[simp]: "carrier V = carrier\<^sub>v n"
    and [simp]: "add V = op \<oplus>\<^sub>v"
    and [simp]: "zero V = \<zero>\<^sub>v n"
    and [simp]: "smult V = op \<odot>\<^sub>v"
    and "carrier class_ring = UNIV"
    and "mult class_ring = op *"
    and "add class_ring = op +"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = op ^"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "m_inv (class_ring :: 'a ring) x = (if x = 0 then div0 else inverse x)"
  using vec_vs
  unfolding class_field_def
  by (auto simp: vec_module_simps class_ring_simps)

lemma finsum_vec[simp]: "finsum_vec TYPE('a) n = finsum V"
  unfolding finsum_vec_def vec_monoid_def
  unfolding finsum_def by simp

lemma finsum_scalar_prod_sum:
  assumes f: "f : U \<rightarrow> carrier\<^sub>v n"
      and w: "w: carrier\<^sub>v n"
  shows "finsum V f U \<bullet> w = sum (\<lambda>u. f u \<bullet> w) U"
  using w f
proof (induct U rule: infinite_finite_induct)
  case (insert u U)
    hence f: "f : U \<rightarrow> carrier\<^sub>v n" "f u : carrier\<^sub>v n"  by auto
    show ?case
      unfolding finsum_insert[OF insert(1) insert(2) f]
      apply (subst scalar_prod_left_distrib) using insert by auto
qed auto

lemma vec_neg[simp]: assumes "x : carrier\<^sub>v n" shows "\<ominus>\<^bsub>V\<^esub> x = \<ominus>\<^sub>v x"
  unfolding a_inv_def m_inv_def apply simp 
  apply (rule the_equality, intro conjI)
  using assms apply auto
  using M.minus_unique vec_uminus_closed vec_uminus_r_inv by blast

lemma finsum_dim:
  "finite A \<Longrightarrow> f \<in> A \<rightarrow> carrier\<^sub>v n \<Longrightarrow> dim\<^sub>v (finsum V f A) = n"
proof(induct set:finite)
  case (insert a A)
    hence dfa: "dim\<^sub>v (f a) = n" by auto
    have f: "f \<in> A \<rightarrow> carrier\<^sub>v n" using insert by auto
    hence fa: "f a \<in> carrier\<^sub>v n" using insert by auto
    show ?case
      unfolding finsum_insert[OF insert(1) insert(2) f fa]
      using insert by auto
qed simp

lemma lincomb_dim:
  assumes fin: "finite X"
    and X: "X \<subseteq> carrier\<^sub>v n"
  shows "dim\<^sub>v (lincomb a X) = n"
proof -
  let ?f = "\<lambda>v. a v \<odot>\<^sub>v v"
  have f: "?f \<in> X \<rightarrow> carrier\<^sub>v n" apply rule using X by auto
  show ?thesis
    unfolding lincomb_def
    using finsum_dim[OF fin f].
qed


lemma finsum_index:
  assumes i: "i < n"
    and f: "f \<in> X \<rightarrow> carrier\<^sub>v n"
    and X: "X \<subseteq> carrier\<^sub>v n"
  shows "finsum V f X $ i = sum (\<lambda>x. f x $ i) X"
  using X f
proof (induct X rule: infinite_finite_induct)
  case empty
    then show ?case using i by simp next
  case (insert x X)
    then have Xf: "finite X"
      and xX: "x \<notin> X"
      and x: "x \<in> carrier\<^sub>v n"
      and X: "X \<subseteq> carrier\<^sub>v n"
      and fx: "f x \<in> carrier\<^sub>v n"
      and f: "f \<in> X \<rightarrow> carrier\<^sub>v n" by auto
    have i2: "i < dim\<^sub>v (finsum V f X)"
      using i finsum_closed[OF f] by auto
    have ix: "i < dim\<^sub>v x" using x i by auto
    show ?case
      unfolding finsum_insert[OF Xf xX f fx]
      unfolding sum.insert[OF Xf xX]
      unfolding vec_index_add(1)[OF i2]
      using insert lincomb_def
      by auto
qed (insert i, auto)

lemma lincomb_index:
  assumes i: "i < n"
    and X: "X \<subseteq> carrier\<^sub>v n"
  shows "lincomb a X $ i = sum (\<lambda>x. a x * x $ i) X"
proof -
  let ?f = "\<lambda>x. a x \<odot>\<^sub>v x"
  have f: "?f : X \<rightarrow> carrier\<^sub>v n" using X by auto
  have point: "\<And>v. v \<in> X \<Longrightarrow> (a v \<odot>\<^sub>v v) $ i = a v * v $ i" using i X by auto
  show ?thesis
    unfolding lincomb_def
    unfolding finsum_index[OF i f X]
    using point X by simp
qed

lemma append_insert: "set (xs @ [x]) = insert x (set xs)" by simp

lemma lincomb_units:
  assumes i: "i < n" 
  shows "lincomb a (set (vec_units n)) $ i = a (vec_unit n i)"
  unfolding lincomb_index[OF i vec_units_carrier]
  unfolding vec_units_first
proof -
  let ?f = "\<lambda>m i. \<Sum>x\<in>set (vec_units_first n m). a x * x $ i"
  have zero:"\<And>m j. m \<le> j \<Longrightarrow> j < n \<Longrightarrow> ?f m j = 0"
  proof -
    fix m
    show "\<And>j. m \<le> j \<Longrightarrow> j < n \<Longrightarrow> ?f m j = 0"
    proof (induction m)
      case (Suc m)
        hence mj:"m\<le>j" and mj':"m\<noteq>j" and jn:"j<n" and mn:"m<n" by auto
        hence mem: "unit\<^sub>v n m \<notin> set (vec_units_first n m)"
          apply(subst vec_units_first_distinct) by auto
        show ?case
          unfolding vec_units_first.simps
          unfolding append_insert
          unfolding sum.insert[OF finite_set mem]
          unfolding vec_unit_index(1)[OF mn jn]
          unfolding Suc(1)[OF mj jn] using mj' by simp
    qed simp
  qed
  { fix m
    have "i < m \<Longrightarrow> m \<le> n \<Longrightarrow> ?f m i = a (unit\<^sub>v n i)"
    proof (induction m arbitrary: i)
      case (Suc m)
        hence iSm: "i < Suc m" and i:"i<n" and mn: "m<n" by auto
        hence mem: "unit\<^sub>v n m \<notin> set (vec_units_first n m)"
          apply(subst vec_units_first_distinct) by auto
        show ?case
          unfolding vec_units_first.simps
          unfolding append_insert
          unfolding sum.insert[OF finite_set mem]
          unfolding vec_unit_index(1)[OF mn i]
          using zero Suc by (cases "i = m",auto)
    qed auto
  }
  thus "?f n i = a (unit\<^sub>v n i)" using assms by auto
qed

lemma lincomb_coordinates:
  assumes v: "v : carrier\<^sub>v n"
  defines "a \<equiv> (\<lambda>u. v $ (THE i. u = vec_unit n i))"
  shows "lincomb a (set (vec_units n)) = v"
proof -
  have a: "a \<in> set (vec_units n) \<rightarrow> UNIV" by auto
  have fvu: "\<And>i. i < n \<Longrightarrow> v $ i = a (vec_unit n i)"
    unfolding a_def using vec_unit_eq by auto
  show ?thesis
    apply rule
    unfolding lincomb_dim[OF finite_set vec_units_carrier]
    using v lincomb_units fvu
    by auto
qed

lemma span_vec_units_is_carrier: "span (set (vec_units n)) = carrier\<^sub>v n" (is "?L = ?R")
proof (rule;rule)
  fix v assume vsU: "v \<in> ?L" show "v \<in> ?R"
  proof -
    obtain a
      where v: "v = lincomb a (set (vec_units n))"
      using vsU
      unfolding finite_span[OF finite_set vec_units_carrier] by auto
    thus ?thesis using lincomb_closed[OF vec_units_carrier] by auto
  qed
  next fix v::"'a vec" assume v: "v \<in> ?R" show "v \<in> ?L"
    unfolding span_def
    using lincomb_coordinates[OF v,symmetric] by auto
qed

lemma fin_dim[simp]: "fin_dim"
  unfolding fin_dim_def
  apply (intro eqTrueI exI conjI) using span_vec_units_is_carrier vec_units_carrier by auto

lemma vec_units_basis: "basis (set (vec_units n))" unfolding basis_def span_vec_units_is_carrier
proof (intro conjI)
  show "\<not> lin_dep (set (vec_units n))" 
  proof
    assume "lin_dep (set (vec_units n))"
    from this[unfolded lin_dep_def] obtain A a v where
      fin: "finite A" and A: "A \<subseteq> set (vec_units n)"  
      and lc: "lincomb a A = \<zero>\<^sub>v n" and v: "v \<in> A" and av: "a v \<noteq> 0"      
      by auto
    from v A obtain i where i: "i < n" and vu: "v = unit\<^sub>v n i" unfolding vec_units_def by auto
    define b where "b = (\<lambda> x. if x \<in> A then a x else 0)"
    have id: "A \<union> (set (vec_units n) - A) = set (vec_units n)" using A by auto
    from lincomb_index[OF i vec_units_carrier]
    have "lincomb b (set (vec_units n)) $ i = (\<Sum>x\<in> (A \<union> (set (vec_units n) - A)). b x * x $ i)" 
      unfolding id .
    also have "\<dots> = (\<Sum>x\<in> A. b x * x $ i) + (\<Sum>x\<in> set (vec_units n) - A. b x * x $ i)"
      by (rule sum.union_disjoint, insert fin, auto)
    also have "(\<Sum>x\<in> A. b x * x $ i) = (\<Sum>x\<in> A. a x * x $ i)"
      by (rule sum.cong, auto simp: b_def)
    also have "\<dots> = lincomb a A $ i" 
      by (subst lincomb_index[OF i], insert A vec_units_carrier, auto)
    also have "\<dots> = 0" unfolding lc using i by simp
    also have "(\<Sum>x\<in> set (vec_units n) - A. b x * x $ i) = 0"
      by (rule sum.neutral, auto simp: b_def)
    finally have "lincomb b (set (vec_units n)) $ i = 0" by simp
    from lincomb_units[OF i, of b, unfolded this]
    have "b v = 0" unfolding vu by simp
    with v av show False unfolding b_def by simp
  qed
qed (insert vec_units_carrier, auto)

lemma vec_units_length[simp]: "length (vec_units n) = n"
  unfolding vec_units_def by auto

lemma vec_units_distinct: "distinct (vec_units n)"
  unfolding distinct_conv_nth vec_units_length
proof (intro allI impI)
  fix i j
  assume *: "i < n" "j < n" "i \<noteq> j"
  show "vec_units n ! i \<noteq> vec_units n ! j"
  proof
    assume "vec_units n ! i = vec_units n ! j"
    from arg_cong[OF this, of "\<lambda> v. v $ i"] 
    show False using * unfolding vec_units_def by auto
  qed
qed

lemma dim_is_n: "dim = n"
  unfolding dim_basis[OF finite_set vec_units_basis]
  unfolding distinct_card[OF vec_units_distinct]
  by simp

end

locale mat_space =
  vec_space f_ty nc for f_ty::"'a::field itself" and nc::"nat" +
  fixes nr :: "nat"
begin
  abbreviation M where "M \<equiv> ring\<^sub>m TYPE('a) nc nr"
end

  
end
