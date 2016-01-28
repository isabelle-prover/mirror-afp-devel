(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section\<open>Vectors and Matrices\<close>

text \<open>We define vectors as pairs of dimension and a characteristic function from natural numbers
to elements.
Similarly, matrices are defined as triples of two dimensions and one
characteristic function from pairs of natural numbers to elements. 
Via a subtype we ensure that the characteristic function always behaves the same 
on indices outside the intended one. Hence, every matrix has a unique representation.

In this part we define basic operations like matrix-addition, -multiplication, scalar-product,
etc. We connect these operations to HOL-Algebra with its explicit carrier sets.\<close>

theory Matrix
imports
  Missing_Ring
  "~~/src/HOL/Algebra/Module"
  "../Polynomial_Interpolation/Ring_Hom"
begin

subsection\<open>Vectors\<close>

text \<open>Here we specify which value should be returned in case 
  an index is out of bounds. The current solution has the advantage
  that in the implementation later on, no index comparison has to be performed.\<close>

definition undef_vec :: "nat \<Rightarrow> 'a" where
  "undef_vec i \<equiv> [] ! i"

definition mk_vec :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mk_vec n f \<equiv> \<lambda> i. if i < n then f i else undef_vec (i - n)"

typedef 'a vec = "{(n, mk_vec n f) | n f :: nat \<Rightarrow> 'a. True}"
  by auto

setup_lifting type_definition_vec

lift_definition vec_dim :: "'a vec \<Rightarrow> nat" ( "dim\<^sub>v") is fst .
lift_definition vec_index :: "'a vec \<Rightarrow> (nat \<Rightarrow> 'a)" (infixl "$" 100) is snd .
lift_definition vec :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vec" 
  is "\<lambda> n f. (n, mk_vec n f)" by auto

lift_definition vec_of_list :: "'a list \<Rightarrow> 'a vec" is
  "\<lambda> v. (length v, mk_vec (length v) (nth v))" by auto

lift_definition list_of_vec :: "'a vec \<Rightarrow> 'a list" is
  "\<lambda> (n,v). map v [0 ..< n]" .

definition
  vec_carrier :: "nat \<Rightarrow> 'a vec set" ("carrier\<^sub>v")
  where "vec_carrier n = { v . dim\<^sub>v v = n}" 

lemma vec_dim_vec[simp]: "dim\<^sub>v (vec n f) = n" by transfer simp
lemma vec_dim[simp]: "vec n f \<in> carrier\<^sub>v n" unfolding vec_carrier_def by auto
lemma vec_index_vec[simp]: "i < n \<Longrightarrow> vec n f $ i = f i" by transfer (simp add: mk_vec_def)
lemma vec_eqI[intro]: "(\<And> i. i < dim\<^sub>v w \<Longrightarrow> v $ i = w $ i) \<Longrightarrow> dim\<^sub>v v = dim\<^sub>v w 
  \<Longrightarrow> v = w"
  by (transfer, auto simp: mk_vec_def)

lemma vec_elems: "v \<in> vec_carrier n \<longleftrightarrow> dim\<^sub>v v = n"
  unfolding vec_carrier_def by auto

lemma vec_elemsD[simp]: "v \<in> vec_carrier n \<Longrightarrow> dim\<^sub>v v = n" using vec_elems by auto

lemma vec_elemsI: "dim\<^sub>v v = n \<Longrightarrow> v \<in> vec_carrier n" using vec_elems by auto

definition
  vec_add :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: plus vec" (infixl "\<oplus>\<^sub>v" 65)
  where "v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2 \<equiv> vec (dim\<^sub>v v\<^sub>2) (\<lambda> i. v\<^sub>1 $ i + v\<^sub>2 $ i)"

definition
  vec_zero :: "nat \<Rightarrow> 'a :: zero vec" ("\<zero>\<^sub>v")
  where "\<zero>\<^sub>v n \<equiv> vec n (\<lambda> i. 0)" 

lemma vec_zero_carrier[simp]: "\<zero>\<^sub>v n \<in> carrier\<^sub>v n"
  unfolding vec_zero_def vec_carrier_def by auto

lemma vec_zero_index[simp]: "i < n \<Longrightarrow> \<zero>\<^sub>v n $ i = 0" "dim\<^sub>v (\<zero>\<^sub>v n) = n"
  unfolding vec_zero_def by auto

lemma vec_of_dim_0[simp]: "dim\<^sub>v v = 0 \<longleftrightarrow> v = \<zero>\<^sub>v 0" by auto

definition
  vec_unit :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: zero_neq_one) vec" ("unit\<^sub>v")
  where "unit\<^sub>v n i = vec n (\<lambda> j. if j = i then 1 else 0)" 

lemma vec_unit_index[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> unit\<^sub>v n i $ j = (if j = i then 1 else 0)"
  "i < n \<Longrightarrow> unit\<^sub>v n i $ i = 1"
  "dim\<^sub>v (unit\<^sub>v n i) = n"
  unfolding vec_unit_def by auto

lemma vec_unit_eq[simp]:
  assumes i: "i < n"
  shows "(unit\<^sub>v n i = unit\<^sub>v n j) = (i = j)"
proof -
  have "i \<noteq> j \<Longrightarrow> unit\<^sub>v n i $ i \<noteq> unit\<^sub>v n j $ i"
    unfolding vec_unit_def using i by simp
  then show ?thesis by metis
qed

lemma vec_unit_nonzero[simp]:
  assumes i_n: "i < n" shows "vec_unit n i \<noteq> vec_zero n" (is "?l \<noteq> ?r")
proof -
  have "?l $ i = 1" "?r $ i = 0" using i_n by auto
  thus "?l \<noteq> ?r" by auto
qed

lemma vec_unit_carrier[simp]: "unit\<^sub>v n i \<in> carrier\<^sub>v n"
  unfolding vec_unit_def vec_carrier_def by auto

definition vec_units:: "nat \<Rightarrow> 'a :: zero_neq_one vec list"
  where "vec_units n = map (vec_unit n) [0..<n]"

text "List of first i units"

fun vec_units_first:: "nat \<Rightarrow> nat \<Rightarrow> 'a::zero_neq_one vec list"
  where "vec_units_first n 0 = []"
    |   "vec_units_first n (Suc i) = vec_units_first n i @ [unit\<^sub>v n i]"

lemma vec_units_first: "vec_units n = vec_units_first n n"
  unfolding vec_units_def set_map set_upt
proof -
  {fix m
    have "m \<le> n \<Longrightarrow> map (unit\<^sub>v n) [0..<m] = vec_units_first n m"
    proof (induct m)
      case (Suc m) then have mn:"m\<le>n" by auto
        show ?case unfolding upt_Suc using Suc(1)[OF mn] by auto
    qed auto
  }
  thus "map (unit\<^sub>v n) [0..<n] = vec_units_first n n" by auto
qed

text "list of last i units"

fun vec_units_last:: "nat \<Rightarrow> nat \<Rightarrow> 'a :: zero_neq_one vec list"
  where "vec_units_last n 0 = []"
    |   "vec_units_last n (Suc i) = unit\<^sub>v n (n - Suc i) # vec_units_last n i"

lemma vec_units_last_carrier: "set (vec_units_last n i) \<subseteq> carrier\<^sub>v n"
  by (induct i;auto)

lemma vec_units_last[code]: "vec_units n = vec_units_last n n"
proof -
  { fix m assume "m = n"
    have "m \<le> n \<Longrightarrow> map (vec_unit n) [n-m..<n] = vec_units_last n m"
      proof (induction m)
      case (Suc m)
        then have nm:"n - Suc m < n" by auto
        have ins: "[n - Suc m ..< n] = (n - Suc m) # [n - m ..< n]"
          unfolding upt_conv_Cons[OF nm]
          by (auto simp: Suc.prems Suc_diff_Suc Suc_le_lessD)
        show ?case
          unfolding ins
          unfolding vec_units_last.simps
          unfolding list.map
          using Suc
          unfolding Suc by auto
      qed simp
  }
  thus "vec_units n = vec_units_last n n"
    unfolding vec_units_def by auto
qed

lemma vec_units_carrier: "set (vec_units n) \<subseteq> carrier\<^sub>v n"
proof
  fix u :: "'a vec"  assume u: "u \<in> set (vec_units n)"
  then obtain i where "u = vec_unit n i" unfolding vec_units_def by auto
  then show "u \<in> carrier\<^sub>v n"
    using vec_unit_carrier by auto
qed

lemma vec_units_last_distinct:
  "j \<le> n \<Longrightarrow> i < n - j \<Longrightarrow> unit\<^sub>v n i \<notin> set (vec_units_last n j)"
  by (induction j arbitrary:i, auto)

lemma vec_units_first_distinct:
  "i \<le> j \<Longrightarrow> j < n \<Longrightarrow> unit\<^sub>v n j \<notin> set (vec_units_first n i)"
  by (induction i arbitrary:j, auto)

definition map_vec ("map\<^sub>v") where "map_vec f v \<equiv> vec (dim\<^sub>v v) (\<lambda>i. f (v $ i))"

definition vec_uminus :: "'a :: uminus vec \<Rightarrow> 'a vec" ("\<ominus>\<^sub>v _" [81] 80) where
  "\<ominus>\<^sub>v v \<equiv> vec (dim\<^sub>v v) (\<lambda> i. - (v $ i))"

definition vec_scalar_mult :: "'a :: times \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl "\<odot>\<^sub>v" 70)
  where "a \<odot>\<^sub>v v \<equiv> vec (dim\<^sub>v v) (\<lambda> i. a * v $ i)"

definition scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: semiring_0" (infix "\<bullet>" 70)
  where "v \<bullet> w \<equiv> \<Sum> i \<in> {0 ..< dim\<^sub>v w}. v $ i * w $ i"

definition vec_monoid :: "'a itself \<Rightarrow> nat \<Rightarrow> ('a :: monoid_add vec) monoid" 
  ("monoid\<^sub>v") where
  "monoid\<^sub>v ty n \<equiv> \<lparr> 
    carrier = carrier\<^sub>v n, 
    mult = op \<oplus>\<^sub>v, 
    one = \<zero>\<^sub>v n\<rparr>"

definition vec_module ::
  "'a :: semiring_1 itself \<Rightarrow> nat \<Rightarrow> ('a,'a vec) module" ("module\<^sub>v") where
  "module\<^sub>v ty n \<equiv> \<lparr>
    carrier = carrier\<^sub>v n,
    mult = undefined,
    one = undefined,
    zero = \<zero>\<^sub>v n,
    add = op \<oplus>\<^sub>v,
    smult = op \<odot>\<^sub>v\<rparr>"

lemma vec_monoid_simps: 
  "mult (monoid\<^sub>v ty n) = op \<oplus>\<^sub>v" 
  "carrier (monoid\<^sub>v ty n) = carrier\<^sub>v n"
  "one (monoid\<^sub>v ty n) = \<zero>\<^sub>v n"
  unfolding vec_monoid_def by auto

lemma vec_module_simps:
  "add (module\<^sub>v ty n) = op \<oplus>\<^sub>v" 
  "zero (module\<^sub>v ty n) = \<zero>\<^sub>v n" 
  "carrier (module\<^sub>v ty n) = carrier\<^sub>v n" 
  "smult (module\<^sub>v ty n) = op \<odot>\<^sub>v"
  unfolding vec_module_def by auto

definition finsum_vec :: "'a :: monoid_add itself \<Rightarrow> nat \<Rightarrow> ('c \<Rightarrow> 'a vec) \<Rightarrow> 'c set \<Rightarrow> 'a vec" where
  "finsum_vec ty n = finprod (vec_monoid ty n)"

lemma vec_index_add[simp]: 
  "i < dim\<^sub>v v\<^sub>2 \<Longrightarrow> (v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2) $ i = v\<^sub>1 $ i + v\<^sub>2 $ i" "dim\<^sub>v (v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2) = dim\<^sub>v v\<^sub>2"
  unfolding vec_add_def by auto

lemma vec_index_map[simp]:
  "i < dim\<^sub>v v \<Longrightarrow> map\<^sub>v f v $ i = f (v $ i)"
  "dim\<^sub>v (map\<^sub>v f v) = dim\<^sub>v v"
  unfolding map_vec_def by auto

lemma map_vec_carrier[simp]: "map\<^sub>v h v \<in> carrier\<^sub>v n = (v \<in> carrier\<^sub>v n)" 
  unfolding map_vec_def vec_carrier_def by auto

lemma vec_index_uminus[simp]: 
  "i < dim\<^sub>v v \<Longrightarrow> (\<ominus>\<^sub>v v) $ i = - (v $ i)" 
  "dim\<^sub>v (\<ominus>\<^sub>v v) = dim\<^sub>v v" 
  unfolding vec_uminus_def by auto

lemma vec_index_scalar_mult[simp]: 
  "i < dim\<^sub>v v \<Longrightarrow> (a \<odot>\<^sub>v v) $ i = a * v $ i" "dim\<^sub>v (a \<odot>\<^sub>v v) = dim\<^sub>v v"
  unfolding vec_scalar_mult_def by auto

lemma vec_add_closed[simp]: 
  "v\<^sub>1 \<in> carrier\<^sub>v n \<Longrightarrow> v\<^sub>2 \<in> carrier\<^sub>v n \<Longrightarrow> v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2 \<in> carrier\<^sub>v n"
  unfolding vec_carrier_def by auto

lemma vec_add_comm[ac_simps]: 
  "(v\<^sub>1 :: 'a :: ab_semigroup_add vec) \<in> carrier\<^sub>v n \<Longrightarrow> v\<^sub>2 \<in> carrier\<^sub>v n \<Longrightarrow> v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2 = v\<^sub>2 \<oplus>\<^sub>v v\<^sub>1"
  by (intro vec_eqI, auto simp: ac_simps)

lemma vec_add_assoc[simp]: 
  "(v\<^sub>1 :: 'a :: semigroup_add vec) \<in> carrier\<^sub>v n \<Longrightarrow> v\<^sub>2 \<in> carrier\<^sub>v n \<Longrightarrow> v\<^sub>3 \<in> carrier\<^sub>v n 
  \<Longrightarrow> (v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2) \<oplus>\<^sub>v v\<^sub>3 = v\<^sub>1 \<oplus>\<^sub>v (v\<^sub>2 \<oplus>\<^sub>v v\<^sub>3)"
  by (intro vec_eqI, auto simp: ac_simps)

lemma vec_monoid: "comm_monoid (monoid\<^sub>v TYPE ('a :: comm_monoid_add) n)"
  by (unfold_locales, auto simp: vec_monoid_def ac_simps)

lemma vec_left_zero[simp]: 
  "(v :: 'a :: monoid_add vec) \<in> carrier\<^sub>v n  \<Longrightarrow> \<zero>\<^sub>v n \<oplus>\<^sub>v v = v"
  by (intro vec_eqI, auto)

lemma vec_uminus_closed[simp]: 
  "(\<ominus>\<^sub>v v \<in> carrier\<^sub>v n) = (v \<in> carrier\<^sub>v n)"
  unfolding vec_carrier_def by auto

lemma vec_uminus_r_inv[simp]: 
  "(v :: 'a :: group_add vec) \<in> carrier\<^sub>v n \<Longrightarrow> (v \<oplus>\<^sub>v \<ominus>\<^sub>v v) = \<zero>\<^sub>v n"
  by (intro vec_eqI, auto)

lemma vec_uminus_l_inv[simp]: 
  "(v :: 'a :: group_add vec) \<in> carrier\<^sub>v n \<Longrightarrow> (\<ominus>\<^sub>v v \<oplus>\<^sub>v v) = \<zero>\<^sub>v n"
  by (intro vec_eqI, auto)

lemma vec_add_inv_exists: 
  "(v :: 'a :: group_add vec) \<in> carrier\<^sub>v n \<Longrightarrow> \<exists> w \<in> carrier\<^sub>v n. w \<oplus>\<^sub>v v = \<zero>\<^sub>v n \<and> v \<oplus>\<^sub>v w = \<zero>\<^sub>v n"
  by (intro bexI[of _ "\<ominus>\<^sub>v v"], auto)

lemma vec_group: "comm_group (monoid\<^sub>v TYPE ('a :: ab_group_add) n)"
  by (unfold_locales, insert vec_add_inv_exists, auto simp: vec_monoid_def ac_simps Units_def)

lemmas finsum_vec_insert = 
  comm_monoid.finprod_insert[OF vec_monoid, folded finsum_vec_def, unfolded vec_monoid_simps]

lemmas finsum_vec_closed = 
  comm_monoid.finprod_closed[OF vec_monoid, folded finsum_vec_def, unfolded vec_monoid_simps]

lemmas finsum_vec_empty = 
  comm_monoid.finprod_empty[OF vec_monoid, folded finsum_vec_def, unfolded vec_monoid_simps]

lemma vec_scalar_mult_closed[simp]: "(a \<odot>\<^sub>v v \<in> carrier\<^sub>v n) = (v \<in> carrier\<^sub>v n)"
  unfolding vec_carrier_def by auto
 
lemma scalar_prod_left_zero[simp]: "v \<in> carrier\<^sub>v n \<Longrightarrow> \<zero>\<^sub>v n \<bullet> v = 0"
  unfolding scalar_prod_def
  by (rule setsum.neutral, auto)

lemma scalar_prod_right_zero[simp]: "v \<in> carrier\<^sub>v n \<Longrightarrow> v \<bullet> \<zero>\<^sub>v n = 0"
  unfolding scalar_prod_def
  by (rule setsum.neutral, auto)

lemma scalar_prod_left_unit[simp]: assumes v: "(v :: 'a :: semiring_1 vec) \<in> carrier\<^sub>v n" and i: "i < n"
  shows "unit\<^sub>v n i \<bullet> v = v $ i"
proof -
  let ?f = "\<lambda> k. unit\<^sub>v n i $ k * v $ k"
  have id: "(\<Sum>k\<in>{0..<n}. ?f k) = unit\<^sub>v n i $ i * v $ i + (\<Sum>k\<in>{0..<n} - {i}. ?f k)"
    by (rule setsum.remove, insert i, auto)
  also have "(\<Sum> k\<in>{0..<n} - {i}. ?f k) = 0"
    by (rule setsum.neutral, insert i, auto)
  finally
  show ?thesis unfolding scalar_prod_def using i v by simp
qed

lemma scalar_prod_right_unit[simp]: assumes i: "i < n"
  shows "(v :: 'a :: semiring_1 vec) \<bullet> unit\<^sub>v n i = v $ i"
proof -
  let ?f = "\<lambda> k. v $ k * unit\<^sub>v n i $ k"
  have id: "(\<Sum>k\<in>{0..<n}. ?f k) = v $ i * unit\<^sub>v n i $ i + (\<Sum>k\<in>{0..<n} - {i}. ?f k)"
    by (rule setsum.remove, insert i, auto)
  also have "(\<Sum>k\<in>{0..<n} - {i}. ?f k) = 0"
    by (rule setsum.neutral, insert i, auto)
  finally
  show ?thesis unfolding scalar_prod_def using i by simp
qed

lemma scalar_prod_left_distrib: assumes v: "v\<^sub>1 \<in> carrier\<^sub>v n" "v\<^sub>2 \<in> carrier\<^sub>v n" "v\<^sub>3 \<in> carrier\<^sub>v n"
  shows "(v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2) \<bullet> v\<^sub>3 = v\<^sub>1 \<bullet> v\<^sub>3 + v\<^sub>2 \<bullet> v\<^sub>3"
proof -
  have "(\<Sum>i\<in>{0..<dim\<^sub>v v\<^sub>3}. (v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2) $ i * v\<^sub>3 $ i) = (\<Sum>i\<in>{0..<dim\<^sub>v v\<^sub>3}. v\<^sub>1 $ i * v\<^sub>3 $ i + v\<^sub>2 $ i * v\<^sub>3 $ i)"
    by (rule setsum.cong, insert v, auto simp: algebra_simps)
  thus ?thesis unfolding scalar_prod_def using v by (auto simp: setsum.distrib)
qed

lemma scalar_prod_right_distrib: assumes v: "v\<^sub>1 \<in> carrier\<^sub>v n" "v\<^sub>2 \<in> carrier\<^sub>v n" "v\<^sub>3 \<in> carrier\<^sub>v n"
  shows "v\<^sub>1 \<bullet> (v\<^sub>2 \<oplus>\<^sub>v v\<^sub>3) = v\<^sub>1 \<bullet> v\<^sub>2 + v\<^sub>1 \<bullet> v\<^sub>3"
proof -
  have "(\<Sum>i\<in>{0..<dim\<^sub>v v\<^sub>3}. v\<^sub>1 $ i * (v\<^sub>2 \<oplus>\<^sub>v v\<^sub>3) $ i) = (\<Sum>i\<in>{0..<dim\<^sub>v v\<^sub>3}. v\<^sub>1 $ i * v\<^sub>2 $ i + v\<^sub>1 $ i * v\<^sub>3 $ i)"
    by (rule setsum.cong, insert v, auto simp: algebra_simps)
  thus ?thesis unfolding scalar_prod_def using v by (auto intro: setsum.distrib)
qed

lemma scalar_scalar_prod_assoc[simp]: assumes v: "v\<^sub>1 \<in> carrier\<^sub>v n" "v\<^sub>2 \<in> carrier\<^sub>v n" 
  shows "(a \<odot>\<^sub>v v\<^sub>1) \<bullet> v\<^sub>2 = a * (v\<^sub>1 \<bullet> v\<^sub>2)"
  unfolding scalar_prod_def setsum_right_distrib
  by (rule setsum.cong, insert v, auto simp: ac_simps)

lemma scalar_prod_scalar_assoc[simp]: assumes v: "v\<^sub>1 \<in> carrier\<^sub>v n" "v\<^sub>2 \<in> carrier\<^sub>v n" 
  shows "v\<^sub>1 \<bullet> (a \<odot>\<^sub>v v\<^sub>2) = (a :: 'a :: comm_ring) * (v\<^sub>1 \<bullet> v\<^sub>2)"
  unfolding scalar_prod_def setsum_right_distrib
  by (rule setsum.cong, insert v, auto simp: ac_simps)

lemma scalar_prod_comm: assumes "(v\<^sub>1 :: 'a :: comm_semiring_0 vec) \<in> carrier\<^sub>v n" "v\<^sub>2 \<in> carrier\<^sub>v n" 
  shows "v\<^sub>1 \<bullet> v\<^sub>2 = v\<^sub>2 \<bullet> v\<^sub>1"
  unfolding scalar_prod_def
  by (rule setsum.cong, insert assms, auto simp: ac_simps)

lemma vec_smult_l_distr:
  "((a::'a::ring) + b) \<odot>\<^sub>v v = a \<odot>\<^sub>v v \<oplus>\<^sub>v b \<odot>\<^sub>v v"
  unfolding vec_scalar_mult_def vec_add_def
  by (rule vec_eqI, auto simp: distrib_right)

lemma vec_smult_r_distr:
  assumes "v \<in> carrier\<^sub>v n" "w \<in> carrier\<^sub>v n"
  shows "(a::'a::ring) \<odot>\<^sub>v (v \<oplus>\<^sub>v w) = a \<odot>\<^sub>v v \<oplus>\<^sub>v a \<odot>\<^sub>v w"
  apply (rule vec_eqI)
  unfolding vec_scalar_mult_def vec_add_def
  using assms distrib_left by auto

lemma vec_smult_assoc1:
  "(a * b::'a::ring) \<odot>\<^sub>v v = a \<odot>\<^sub>v (b \<odot>\<^sub>v v)"
  apply (rule vec_eqI)
  unfolding vec_scalar_mult_def vec_add_def using mult.assoc by auto

lemma vec_smult_one [simp]:
  "(1::'a::ring_1) \<odot>\<^sub>v v = v" unfolding vec_scalar_mult_def
  by (rule vec_eqI,auto)

lemma finsum_vec_index: assumes "finite F" and i: "i < n"
  and vs: "vs \<in> F \<rightarrow> carrier\<^sub>v n"
  shows "finsum_vec TYPE('a :: comm_monoid_add) n vs F $ i = setsum (\<lambda> f. vs f $ i) F"
  using `finite F` vs
proof (induct F)
  case (insert f F)
  hence IH: "finsum_vec TYPE('a) n vs F $ i = (\<Sum>f\<in>F. vs f $ i)" 
    and vs: "vs \<in> F \<rightarrow> carrier\<^sub>v n" "vs f \<in> carrier\<^sub>v n" by auto
  show ?case unfolding finsum_vec_insert[OF insert(1-2) vs]
    unfolding setsum.insert[OF insert(1-2)]
    unfolding IH[symmetric]
    by (rule vec_index_add, insert i, insert finsum_vec_closed[OF vs(1)], auto)
qed (insert i, auto simp: finsum_vec_empty)


subsection\<open>Matrices\<close>

text \<open>Similarly as for vectors, we specify which value should be returned in case 
  an index is out of bounds. It is defined in a way that only few
  index comparisons have to be performed in the implementation.\<close>

definition undef_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> nat \<times> nat \<Rightarrow> 'a" where
  "undef_mat nr nc f \<equiv> \<lambda> (i,j). [[f (i,j). j <- [0 ..< nc]] . i <- [0 ..< nr]] ! i ! j"

lemma undef_mat_cong: assumes "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> f (i,j) = f' (i,j)"
  shows "undef_mat nr nc f x = undef_mat nr nc f' x"
proof (cases x)
  case (Pair i j)
  have nth_map_ge: "\<And> i xs. \<not> i < length xs \<Longrightarrow> xs ! i = [] ! (i - length xs)"
    by (metis append_Nil2 nth_append)
  note [simp] = Pair undef_mat_def nth_map_ge[of i] nth_map_ge[of j]
  show ?thesis 
    by (cases "i < nr", simp, cases "j < nc", insert assms, auto)
qed  

definition mk_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a)" where
  "mk_mat nr nc f \<equiv> \<lambda> (i,j). if i < nr \<and> j < nc then f (i,j) else undef_mat nr nc f (i,j)"

lemma mk_mat_cong: assumes "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> f (i,j) = f' (i,j)"
  shows "mk_mat nr nc f = mk_mat nr nc f'"
  using undef_mat_cong[of nr nc f f', OF assms]
  using assms unfolding mk_mat_def
  by auto

typedef 'a mat = "{(nr, nc, mk_mat nr nc f) | nr nc f :: nat \<times> nat \<Rightarrow> 'a. True}"
  by auto

setup_lifting type_definition_mat

lift_definition mat_dim_row :: "'a mat \<Rightarrow> nat" ( "dim\<^sub>r") is fst .
lift_definition mat_dim_col :: "'a mat \<Rightarrow> nat" ( "dim\<^sub>c") is "fst o snd" .
lift_definition mat_index :: "'a mat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a)" (infixl "$$" 100) is "snd o snd" .
lift_definition mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> 'a mat" 
  is "\<lambda> nr nc f. (nr, nc, mk_mat nr nc f)" by auto
lift_definition mat_of_row_fun :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a vec) \<Rightarrow> 'a mat" ("mat\<^sub>r")
  is "\<lambda> nr nc f. (nr, nc, mk_mat nr nc (\<lambda> (i,j). f i $ j))" by auto

definition mat_to_list :: "'a mat \<Rightarrow> 'a list list" where
  "mat_to_list A = [ [A $$ (i,j) . j <- [0 ..< dim\<^sub>c A]] . i <- [0 ..< dim\<^sub>r A]]"

fun square_mat :: "'a mat \<Rightarrow> bool" where "square_mat A = (dim\<^sub>c A = dim\<^sub>r A)"

definition upper_triangular :: "'a::zero mat \<Rightarrow> bool"
  where "upper_triangular A \<equiv>
    \<forall>i < dim\<^sub>r A. \<forall> j < i. A $$ (i,j) = 0"

lemma upper_triangularD[elim] :
  "upper_triangular A \<Longrightarrow> j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0"
unfolding upper_triangular_def by auto

lemma upper_triangularI[intro] :
  "(\<And>i j. j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> upper_triangular A"
unfolding upper_triangular_def by auto

lemma mat_dim_row_mat[simp]: "dim\<^sub>r (mat nr nc f) = nr" "dim\<^sub>r (mat\<^sub>r nr nc g) = nr" 
  by (transfer, simp)+

lemma mat_dim_col_mat[simp]: "dim\<^sub>c (mat nr nc f) = nc" "dim\<^sub>c (mat\<^sub>r nr nc g) = nc" 
  by (transfer, simp)+

definition mat_carrier :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat set" ("carrier\<^sub>m")
  where "mat_carrier nr nc = { m . dim\<^sub>r m = nr \<and> dim\<^sub>c m = nc}" 

lemma mat_carrier_triv[simp]: "m \<in> mat_carrier (dim\<^sub>r m) (dim\<^sub>c m)"
  "mat nr nc f \<in> mat_carrier nr nc"
  unfolding mat_carrier_def by auto

definition mat_elements :: "'a mat \<Rightarrow> 'a set"
  where "mat_elements A = set [A $$ (i,j). i <- [0 ..< dim\<^sub>r A], j <- [0 ..< dim\<^sub>c A]]"

lemma mat_elementsD [dest]:
  "a \<in> mat_elements A \<Longrightarrow> \<exists>i j. i < dim\<^sub>r A \<and> j < dim\<^sub>c A \<and> a = A $$ (i,j)"
  unfolding mat_elements_def by force

lemma mat_elementsI [intro]:
  "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> i < nr \<Longrightarrow> j < nc \<Longrightarrow> a = A $$ (i,j) \<Longrightarrow> a \<in> mat_elements A"
  unfolding mat_elements_def mat_carrier_def by force

lemma mat_index_mat[simp]:  "i < nr \<Longrightarrow> j < nc \<Longrightarrow> mat nr nc f $$ (i,j) = f (i,j)"
  "i < nr \<Longrightarrow> j < nc \<Longrightarrow> mat\<^sub>r nr nc g $$ (i,j) = g i $ j" 
  by (transfer', simp add: mk_mat_def)+

lemma mat_eqI[intro]: "(\<And> i j . i < dim\<^sub>r B \<Longrightarrow> j < dim\<^sub>c B \<Longrightarrow> A $$ (i,j) = B $$ (i,j)) 
  \<Longrightarrow> dim\<^sub>r A = dim\<^sub>r B 
  \<Longrightarrow> dim\<^sub>c A = dim\<^sub>c B 
  \<Longrightarrow> A = B"
  by (transfer, auto intro!: mk_mat_cong, auto simp: mk_mat_def) 

lemma mat_carrierI[intro]:
  assumes "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" shows  "A \<in> mat_carrier nr nc"
  using assms unfolding mat_carrier_def by auto

lemma mat_carrierD[dest,simp]: assumes "A \<in> mat_carrier nr nc"
  shows "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" using assms
  unfolding mat_carrier_def by auto

definition row :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec" where 
  "row A i = vec (dim\<^sub>c A) (\<lambda> j. A $$ (i,j))"

definition rows :: "'a mat \<Rightarrow> 'a vec list" where
  "rows A = map (row A) [0..<dim\<^sub>r A]"

lemma row_dim[simp]: "row A i \<in> carrier\<^sub>v (dim\<^sub>c A)" unfolding row_def by auto

lemma rows_dim[simp]: "set (rows A) \<subseteq> carrier\<^sub>v (dim\<^sub>c A)" unfolding rows_def by auto

lemma rows_length[simp]: "length (rows A) = dim\<^sub>r A" unfolding rows_def by auto

lemma rows_nth[simp]: "i < dim\<^sub>r A \<Longrightarrow> rows A ! i = row A i"
  unfolding rows_def by auto

lemma mat_row_row[simp]: "i < nr \<Longrightarrow> dim\<^sub>v (f i) = nc \<Longrightarrow> row (mat\<^sub>r nr nc f) i = f i"
  by (rule vec_eqI, auto simp: row_def)  

definition "mat_of a \<equiv> mat 1 1 (\<lambda>_. a)"

lemma dim_mat_of[simp]:
  "dim\<^sub>r (mat_of a) = 1" "dim\<^sub>c (mat_of a) = 1" unfolding mat_of_def by auto

lemma mat_of_index[simp]: "mat_of a $$ (0,0) = a" unfolding mat_of_def by simp

definition mat_of_row :: "'a vec \<Rightarrow> 'a mat"
  where "mat_of_row v = mat (dim\<^sub>v v) 1 (\<lambda>(i,j). v $ i)"

definition mat_of_rows :: "nat \<Rightarrow> 'a vec list \<Rightarrow> 'a mat"
  where "mat_of_rows n rs = mat (length rs) n (\<lambda>(i,j). rs ! i $ j)"

definition mat_of_rows_list :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a mat" where
  "mat_of_rows_list nc rs = mat (length rs) nc (\<lambda> (i,j). rs ! i ! j)"

lemma mat_of_rows_dim[simp]:
  "mat_of_rows n vs \<in> carrier\<^sub>m (length vs) n"
  "dim\<^sub>r (mat_of_rows n vs) = length vs"
  "dim\<^sub>c (mat_of_rows n vs) = n"
  unfolding mat_of_rows_def by auto

lemma mat_of_rows_row[simp]:
  assumes i:"i < length vs" and n: "vs ! i \<in> carrier\<^sub>v n"
  shows "row (mat_of_rows n vs) i = vs ! i"
  unfolding mat_of_rows_def row_def using n i by auto

lemma rows_mat_of_rows[simp]:
  assumes "set vs \<subseteq> carrier\<^sub>v n" shows "rows (mat_of_rows n vs) = vs"
  unfolding rows_def apply (rule nth_equalityI)
  using assms unfolding subset_code(1) by auto

lemma mat_of_rows_rows[simp]:
  "mat_of_rows (dim\<^sub>c A) (rows A) = A"
  unfolding mat_of_rows_def by (rule, auto simp: row_def)


definition col :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec" where 
  "col A j = vec (dim\<^sub>r A) (\<lambda> i. A $$ (i,j))"

definition cols :: "'a mat \<Rightarrow> 'a vec list" where
  "cols A = map (col A) [0..<dim\<^sub>c A]"

definition mat_of_cols :: "nat \<Rightarrow> 'a vec list \<Rightarrow> 'a mat"
  where "mat_of_cols n cs = mat n (length cs) (\<lambda>(i,j). cs ! j $ i)"

definition mat_of_cols_list :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a mat" where
  "mat_of_cols_list nr cs = mat nr (length cs) (\<lambda> (i,j). cs ! j ! j)"

lemma col_dim[simp]: "col A i \<in> carrier\<^sub>v (dim\<^sub>r A)" unfolding col_def by auto

lemma dim_col[simp]: "dim\<^sub>v (col A i) = dim\<^sub>r A" by auto

lemma cols_dim[simp]: "set (cols A) \<subseteq> carrier\<^sub>v (dim\<^sub>r A)" unfolding cols_def by auto

lemma cols_length[simp]: "length (cols A) = dim\<^sub>c A" unfolding cols_def by auto

lemma cols_nth[simp]: "i < dim\<^sub>c A \<Longrightarrow> cols A ! i = col A i"
  unfolding cols_def by auto

lemma mat_of_cols_dim[simp]:
  "mat_of_cols n vs \<in> carrier\<^sub>m n (length vs)"
  "dim\<^sub>r (mat_of_cols n vs) = n"
  "dim\<^sub>c (mat_of_cols n vs) = length vs"
  unfolding mat_of_cols_def by auto

lemma mat_of_cols_col[simp]:
  assumes j:"j < length vs" and n: "vs ! j \<in> carrier\<^sub>v n"
  shows "col (mat_of_cols n vs) j = vs ! j"
  unfolding mat_of_cols_def col_def using j n by auto

lemma cols_mat_of_cols[simp]:
  assumes "set vs \<subseteq> carrier\<^sub>v n" shows "cols (mat_of_cols n vs) = vs"
  unfolding cols_def apply(rule nth_equalityI)
  using assms unfolding subset_code(1) by auto

lemma mat_of_cols_cols[simp]:
  "mat_of_cols (dim\<^sub>r A) (cols A) = A"
  unfolding mat_of_cols_def by (rule, auto simp: col_def)

definition
  mat_add :: "('a :: plus) mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixl "\<oplus>\<^sub>m" 65) where
  "A \<oplus>\<^sub>m B \<equiv> mat (dim\<^sub>r B) (dim\<^sub>c B) (\<lambda> ij. A $$ ij + B $$ ij)"

definition mat_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mat \<Rightarrow> 'b mat" ("map\<^sub>m") where
  "mat_map f A \<equiv> mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda> ij. f (A $$ ij))"

definition mat_scalar_mult :: "'a :: times \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixl "\<odot>\<^sub>m" 70)
  where "a \<odot>\<^sub>m A \<equiv> map\<^sub>m (\<lambda> b. a * b) A"

definition mat_zero :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: zero mat" ("\<zero>\<^sub>m") where 
  "\<zero>\<^sub>m nr nc \<equiv> mat nr nc (\<lambda> ij. 0)" 

lemma mat_elements_0 [simp]: "mat_elements (\<zero>\<^sub>m nr nc) \<subseteq> {0}"
  unfolding mat_elements_def mat_zero_def by auto

definition mat_transpose :: "'a mat \<Rightarrow> 'a mat" ("transpose\<^sub>m") where
  "transpose\<^sub>m A \<equiv> mat (dim\<^sub>c A) (dim\<^sub>r A) (\<lambda> (i,j). A $$ (j,i))"

definition mat_one :: "nat \<Rightarrow> 'a :: {zero,one} mat" ("\<one>\<^sub>m") where
  "\<one>\<^sub>m n \<equiv> mat n n (\<lambda> (i,j). if i = j then 1 else 0)" 

definition mat_uminus :: "'a :: uminus mat \<Rightarrow> 'a mat" ("\<ominus>\<^sub>m _" [81] 80) where
  "\<ominus>\<^sub>m A \<equiv> mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda> ij. - (A $$ ij))"

abbreviation mat_minus :: "'a :: {plus,uminus} mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixl "\<ominus>\<^sub>m" 65) where
  "A \<ominus>\<^sub>m B \<equiv> A \<oplus>\<^sub>m \<ominus>\<^sub>m B"

definition mat_mult_vec :: "'a :: semiring_0 mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl "\<otimes>\<^sub>m\<^sub>v" 70)
  where "A \<otimes>\<^sub>m\<^sub>v v \<equiv> vec (dim\<^sub>r A) (\<lambda> i. row A i \<bullet> v)"

definition mat_mult_mat :: "'a :: semiring_0 mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixl "\<otimes>\<^sub>m" 70)
  where "A \<otimes>\<^sub>m B \<equiv> mat (dim\<^sub>r A) (dim\<^sub>c B) (\<lambda> (i,j). row A i \<bullet> col B j)"

definition mat_inverts :: "'a :: semiring_1 mat \<Rightarrow> 'a mat \<Rightarrow> bool" (infix "inverts\<^sub>m" 60)
  where "A inverts\<^sub>m B \<equiv> A \<otimes>\<^sub>m B = \<one>\<^sub>m (dim\<^sub>r A)"

definition mat_invertible :: "'a :: semiring_1 mat \<Rightarrow> bool"
  where "mat_invertible A \<equiv> square_mat A \<and> (\<exists>B. A inverts\<^sub>m B \<and> B inverts\<^sub>m A)"

definition mat_monoid :: "'a :: monoid_add itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat monoid" 
  ("monoid\<^sub>m") where
  "monoid\<^sub>m ty nr nc \<equiv> \<lparr> 
    carrier = carrier\<^sub>m nr nc, 
    mult = op \<oplus>\<^sub>m, 
    one = \<zero>\<^sub>m nr nc\<rparr>"

definition mat_ring :: "'a :: semiring_1 itself \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> ('a mat,'b) ring_scheme" 
  ("ring\<^sub>m") where
  "ring\<^sub>m ty n b \<equiv> \<lparr> 
    carrier = carrier\<^sub>m n n, 
    mult = op \<otimes>\<^sub>m, 
    one = \<one>\<^sub>m n, 
    zero = \<zero>\<^sub>m n n,
    add = op \<oplus>\<^sub>m,
    \<dots> = b\<rparr>"

definition mat_module :: "'a :: semiring_1 itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a,'a mat)module" 
  ("module\<^sub>m") where
  "module\<^sub>m ty nr nc \<equiv> \<lparr>
    carrier = carrier\<^sub>m nr nc, 
    mult = op \<otimes>\<^sub>m, 
    one = \<one>\<^sub>m nr, 
    zero = \<zero>\<^sub>m nr nc,
    add = op \<oplus>\<^sub>m,
    smult = op \<odot>\<^sub>m\<rparr>"

lemma mat_ring_simps: 
  "mult (ring\<^sub>m ty n b) = op \<otimes>\<^sub>m" 
  "add (ring\<^sub>m ty n b) = op \<oplus>\<^sub>m" 
  "one (ring\<^sub>m ty n b) = \<one>\<^sub>m n" 
  "zero (ring\<^sub>m ty n b) = \<zero>\<^sub>m n n" 
  "carrier (ring\<^sub>m ty n b) = carrier\<^sub>m n n" 
  unfolding mat_ring_def by auto

lemma mat_module_simps: 
  "mult (module\<^sub>m ty nr nc) = op \<otimes>\<^sub>m" 
  "add (module\<^sub>m ty nr nc) = op \<oplus>\<^sub>m" 
  "one (module\<^sub>m ty nr nc) = \<one>\<^sub>m nr" 
  "zero (module\<^sub>m ty nr nc) = \<zero>\<^sub>m nr nc" 
  "carrier (module\<^sub>m ty nr nc) = carrier\<^sub>m nr nc" 
  "smult (module\<^sub>m ty nr nc) = op \<odot>\<^sub>m"
  unfolding mat_module_def by auto
    
lemma mat_index_zero[simp]: "i < nr \<Longrightarrow> j < nc \<Longrightarrow> \<zero>\<^sub>m nr nc $$ (i,j) = 0" 
  "dim\<^sub>r (\<zero>\<^sub>m nr nc) = nr" "dim\<^sub>c (\<zero>\<^sub>m nr nc) = nc"
  unfolding mat_zero_def by auto

lemma mat_index_one[simp]: "i < n \<Longrightarrow> j < n \<Longrightarrow> \<one>\<^sub>m n $$ (i,j) = (if i = j then 1 else 0)" 
  "dim\<^sub>r (\<one>\<^sub>m n) = n" "dim\<^sub>c (\<one>\<^sub>m n) = n"
  unfolding mat_one_def by auto

lemma mat_index_add[simp]: 
  "i < dim\<^sub>r B \<Longrightarrow> j < dim\<^sub>c B \<Longrightarrow> (A \<oplus>\<^sub>m B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)" 
  "dim\<^sub>r (A \<oplus>\<^sub>m B) = dim\<^sub>r B" "dim\<^sub>c (A \<oplus>\<^sub>m B) = dim\<^sub>c B"
  unfolding mat_add_def by auto

lemma mat_index_map[simp]:
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> map\<^sub>m f A $$ (i,j) = f (A $$ (i,j))" 
  "dim\<^sub>r (map\<^sub>m f A) = dim\<^sub>r A" "dim\<^sub>c (map\<^sub>m f A) = dim\<^sub>c A"
  unfolding mat_map_def by auto

lemma mat_index_scalar_mult[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> (a \<odot>\<^sub>m A) $$ (i,j) = a * A $$ (i,j)" 
  "dim\<^sub>r (a \<odot>\<^sub>m A) = dim\<^sub>r A" "dim\<^sub>c (a \<odot>\<^sub>m A) = dim\<^sub>c A"
  unfolding mat_scalar_mult_def by auto

lemma mat_index_uminus[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> (\<ominus>\<^sub>m A) $$ (i,j) = - (A $$ (i,j))" 
  "dim\<^sub>r (\<ominus>\<^sub>m A) = dim\<^sub>r A" "dim\<^sub>c (\<ominus>\<^sub>m A) = dim\<^sub>c A"
  unfolding mat_uminus_def by auto

lemma mat_index_transpose[simp]:
  "i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>r A \<Longrightarrow> transpose\<^sub>m A $$ (i,j) = A $$ (j,i)"
  "dim\<^sub>r (transpose\<^sub>m A) = dim\<^sub>c A" "dim\<^sub>c (transpose\<^sub>m A) = dim\<^sub>r A"
  unfolding mat_transpose_def by auto

lemma mat_index_mat_mult_mat[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c B \<Longrightarrow> (A \<otimes>\<^sub>m B) $$ (i,j) = row A i \<bullet> col B j"
  "dim\<^sub>r (A \<otimes>\<^sub>m B) = dim\<^sub>r A" "dim\<^sub>c (A \<otimes>\<^sub>m B) = dim\<^sub>c B"
  by (auto simp: mat_mult_mat_def)

lemma dim_mat_mult_vec[simp]: "dim\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v) = dim\<^sub>r A"
  by (auto simp: mat_mult_vec_def)

lemma index_mat_mult_vec[simp]: "i < dim\<^sub>r A \<Longrightarrow> (A \<otimes>\<^sub>m\<^sub>v v) $ i = row A i \<bullet> v"
  by (auto simp: mat_mult_vec_def)

lemma row_index[simp]:
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> row A i $ j = A $$ (i,j)"
  "dim\<^sub>v (row A i) = dim\<^sub>c A"
  by (auto simp: row_def)

lemma col_index[simp]: "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> col A j $ i = A $$ (i,j)"
  by (auto simp: col_def)

lemma upper_triangular_one[simp]: "upper_triangular (\<one>\<^sub>m n)"
  by (rule, auto)

lemma upper_triangular_zero[simp]: "upper_triangular (\<zero>\<^sub>m n n)"
  by (rule, auto)

lemma mat_row_carrierI[intro,simp]: "mat\<^sub>r nr nc r \<in> carrier\<^sub>m nr nc"
  by (unfold mat_carrier_def vec_carrier_def, auto)
  
lemma mat_row_eqI: assumes rows: "\<And> i. i < dim\<^sub>r B \<Longrightarrow> row A i = row B i"
  and dims: "dim\<^sub>r A = dim\<^sub>r B" "dim\<^sub>c A = dim\<^sub>c B"
  shows "A = B"
proof (rule mat_eqI[OF _ dims])
  fix i j
  assume i: "i < dim\<^sub>r B" and j: "j < dim\<^sub>c B"
  from rows[OF i] have id: "row A i $ j = row B i $ j" by simp
  show "A $$ (i, j) = B $$ (i, j)"
    using row_index(1)[OF i j, folded id] row_index(1)[of i A j] i j dims
    by auto
qed

lemma row_mat[simp]: "i < nr \<Longrightarrow> row (mat nr nc f) i = vec nc (\<lambda> j. f (i,j))"
  by auto

lemma col_mat[simp]: "j < nc \<Longrightarrow> col (mat nr nc f) j = vec nr (\<lambda> i. f (i,j))"
  by auto

lemma mat_zero_closed[simp]: "\<zero>\<^sub>m nr nc \<in> carrier\<^sub>m nr nc"
  unfolding mat_carrier_def by auto

lemma mat_scalar_prod_closed[simp]: 
  "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> k \<odot>\<^sub>m A \<in> carrier\<^sub>m nr nc"
  unfolding mat_carrier_def by auto

lemma mat_add_closed[simp]: 
  "B \<in> carrier\<^sub>m nr nc \<Longrightarrow> A \<oplus>\<^sub>m B \<in> carrier\<^sub>m nr nc"
  unfolding mat_carrier_def by force

lemma mat_one_closed[simp]: "\<one>\<^sub>m n \<in> carrier\<^sub>m n n"
  unfolding mat_carrier_def by auto

lemma mat_uminus_closed: 
  "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> (\<ominus>\<^sub>m A \<in> carrier\<^sub>m nr nc)"
  unfolding mat_carrier_def by auto

lemma mat_uminus_carrier_iff[simp]: 
  "(\<ominus>\<^sub>m A \<in> carrier\<^sub>m nr nc) = (A \<in> carrier\<^sub>m nr nc)"
  unfolding mat_carrier_def by auto

lemma mat_minus_closed: 
  "B \<in> carrier\<^sub>m nr nc \<Longrightarrow> (A \<ominus>\<^sub>m B \<in> carrier\<^sub>m nr nc)"
  unfolding mat_carrier_def by auto

lemma mat_transpose_closed[simp]: "(transpose\<^sub>m A \<in> carrier\<^sub>m nc nr) = (A \<in> carrier\<^sub>m nr nc)"
  unfolding mat_carrier_def by auto

lemma row_closed[simp]: "i < nr \<Longrightarrow> A \<in> carrier\<^sub>m nr nc \<Longrightarrow> row A i \<in> carrier\<^sub>v nc"
  unfolding vec_carrier_def by auto

lemma col_closed[simp]: "j < nc \<Longrightarrow> A \<in> carrier\<^sub>m nr nc \<Longrightarrow> col A j \<in> carrier\<^sub>v nr"
  unfolding vec_carrier_def by auto

lemma mat_mult_mat_closed[simp]: 
  "A \<in> carrier\<^sub>m nr n \<Longrightarrow> B \<in> carrier\<^sub>m n nc \<Longrightarrow> A \<otimes>\<^sub>m B \<in> carrier\<^sub>m nr nc"
  unfolding mat_carrier_def by auto

lemma mat_mult_vec_closed[simp]: 
  "A \<in> carrier\<^sub>m nr n \<Longrightarrow> v \<in> carrier\<^sub>v n \<Longrightarrow> A \<otimes>\<^sub>m\<^sub>v v \<in> carrier\<^sub>v nr"
  unfolding mat_carrier_def vec_carrier_def by auto


lemma mat_add_comm[ac_simps]: 
  "(A :: 'a :: comm_monoid_add mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> B \<in> carrier\<^sub>m nr nc \<Longrightarrow> A \<oplus>\<^sub>m B = B \<oplus>\<^sub>m A"
  by (intro mat_eqI, auto simp: ac_simps)


lemma mat_minus_r_inv[simp]: 
  "(A :: 'a :: group_add mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> (A \<ominus>\<^sub>m A) = \<zero>\<^sub>m nr nc"
  by (intro mat_eqI, auto)

lemma mat_uminus_l_inv[simp]: 
  "(A :: 'a :: group_add mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> (\<ominus>\<^sub>m A \<oplus>\<^sub>m A) = \<zero>\<^sub>m nr nc"
  by (intro mat_eqI, auto)

lemma mat_add_inv_exists: 
  "(A :: 'a :: group_add mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> \<exists> B \<in> carrier\<^sub>m nr nc. B \<oplus>\<^sub>m A = \<zero>\<^sub>m nr nc \<and> A \<oplus>\<^sub>m B = \<zero>\<^sub>m nr nc"
  by (intro bexI[of _ "\<ominus>\<^sub>m A"], auto)

lemma mat_add_assoc[simp]: 
  "(A :: 'a :: monoid_add mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> B \<in> carrier\<^sub>m nr nc \<Longrightarrow> C \<in> carrier\<^sub>m nr nc 
  \<Longrightarrow> (A \<oplus>\<^sub>m B) \<oplus>\<^sub>m C = A \<oplus>\<^sub>m (B \<oplus>\<^sub>m C)"
  by (intro mat_eqI, auto simp: ac_simps)

lemma mat_uminus_mat_add: fixes A :: "'a :: group_add mat" 
  assumes "A \<in> carrier\<^sub>m nr nc"
  and "B \<in> carrier\<^sub>m nr nc"
  shows "\<ominus>\<^sub>m (A \<oplus>\<^sub>m B) = \<ominus>\<^sub>m B \<oplus>\<^sub>m \<ominus>\<^sub>m A"
  by (intro mat_eqI, insert assms, auto simp: minus_add)

lemma transpose_transpose[simp]: 
  "transpose\<^sub>m (transpose\<^sub>m A) = A"
  by (intro mat_eqI, auto)

lemma row_transpose[simp]: 
  "j < dim\<^sub>c A \<Longrightarrow> row (transpose\<^sub>m A) j = col A j"
  unfolding row_def col_def
  by (intro vec_eqI, auto)

lemma col_transpose[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> col (transpose\<^sub>m A) i = row A i"
  unfolding row_def col_def
  by (intro vec_eqI, auto)

lemma row_zero[simp]: 
  "i < nr \<Longrightarrow> row (\<zero>\<^sub>m nr nc) i = \<zero>\<^sub>v nc"
   by (intro vec_eqI, auto)

lemma col_zero[simp]: 
  "j < nc \<Longrightarrow> col (\<zero>\<^sub>m nr nc) j = \<zero>\<^sub>v nr"
   by (intro vec_eqI, auto)

lemma row_one[simp]: 
  "i < n \<Longrightarrow> row (\<one>\<^sub>m n) i = unit\<^sub>v n i"
  by (intro vec_eqI, auto)

lemma col_one[simp]: 
  "j < n \<Longrightarrow> col (\<one>\<^sub>m n) j = unit\<^sub>v n j"
  by (intro vec_eqI, auto)

lemma transpose_add: "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> B \<in> carrier\<^sub>m nr nc 
  \<Longrightarrow> transpose\<^sub>m (A \<oplus>\<^sub>m B) = transpose\<^sub>m A \<oplus>\<^sub>m transpose\<^sub>m B"
  by (intro mat_eqI, auto)

lemma transpose_uminus: "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> transpose\<^sub>m (\<ominus>\<^sub>m A) = \<ominus>\<^sub>m (transpose\<^sub>m A)"
  by (intro mat_eqI, auto)

lemma row_mat_add[simp]: 
  "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> B \<in> carrier\<^sub>m nr nc \<Longrightarrow> i < nr
  \<Longrightarrow> row (A \<oplus>\<^sub>m B) i = row A i \<oplus>\<^sub>v row B i"
  "i < dim\<^sub>r A \<Longrightarrow> dim\<^sub>r B = dim\<^sub>r A \<Longrightarrow> dim\<^sub>c B = dim\<^sub>c A \<Longrightarrow> row (A \<oplus>\<^sub>m B) i = row A i \<oplus>\<^sub>v row B i"
  by (rule vec_eqI, auto)

lemma col_mat_add[simp]: 
  "A \<in> carrier\<^sub>m nr nc \<Longrightarrow> B \<in> carrier\<^sub>m nr nc \<Longrightarrow> j < nc
  \<Longrightarrow> col (A \<oplus>\<^sub>m B) j = col A j \<oplus>\<^sub>v col B j"
  by (rule vec_eqI, auto)

lemma row_mat_mult[simp]: assumes m: "A \<in> carrier\<^sub>m nr n" "B \<in> carrier\<^sub>m n nc"
  and i: "i < nr"
  shows "row (A \<otimes>\<^sub>m B) i = vec nc (\<lambda> j. row A i \<bullet> col B j)"
  by (rule vec_eqI, insert m i, auto)

lemma col_mat_mult[simp]: assumes m: "A \<in> carrier\<^sub>m nr n" "B \<in> carrier\<^sub>m n nc"
  and j: "j < nc"
  shows "col (A \<otimes>\<^sub>m B) j = vec nr (\<lambda> i. row A i \<bullet> col B j)"
  by (rule vec_eqI, insert m j, auto)

lemma transpose_mat_mult:
  "(A :: 'a :: comm_semiring_0 mat) \<in> carrier\<^sub>m nr n \<Longrightarrow> B \<in> carrier\<^sub>m n nc 
  \<Longrightarrow> transpose\<^sub>m (A \<otimes>\<^sub>m B) = transpose\<^sub>m B \<otimes>\<^sub>m transpose\<^sub>m A"
  by (intro mat_eqI, auto simp: scalar_prod_comm[of _ n])

lemma mat_left_add_zero[simp]: 
  "(A :: 'a :: monoid_add mat) \<in> carrier\<^sub>m nr nc  \<Longrightarrow> \<zero>\<^sub>m nr nc \<oplus>\<^sub>m A = A"
  by (intro mat_eqI, auto)

lemma mat_left_mult_zero: 
  "A \<in> carrier\<^sub>m n nc \<Longrightarrow> \<zero>\<^sub>m nr n \<otimes>\<^sub>m A = \<zero>\<^sub>m nr nc"
  by (intro mat_eqI, auto)

lemma [simp]: "dim\<^sub>r A = n \<Longrightarrow> \<zero>\<^sub>m nr n \<otimes>\<^sub>m A = \<zero>\<^sub>m nr (dim\<^sub>c A)"
  by (rule mat_left_mult_zero, unfold mat_carrier_def, simp)

lemma mat_right_mult_zero: 
  "A \<in> carrier\<^sub>m nr n \<Longrightarrow> A \<otimes>\<^sub>m \<zero>\<^sub>m n nc = \<zero>\<^sub>m nr nc"
  by (intro mat_eqI, auto)

lemma [simp]: "dim\<^sub>c A = n \<Longrightarrow> A \<otimes>\<^sub>m \<zero>\<^sub>m n nc = \<zero>\<^sub>m (dim\<^sub>r A) nc"
  by (rule mat_right_mult_zero, unfold mat_carrier_def, simp)

lemma mat_left_mult_one: 
  "(A :: 'a :: semiring_1 mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> \<one>\<^sub>m nr \<otimes>\<^sub>m A = A"
  by (intro mat_eqI, auto)

lemma [simp]: "dim\<^sub>r (A :: 'a :: semiring_1 mat) = n \<Longrightarrow> \<one>\<^sub>m n \<otimes>\<^sub>m A = A"
  by (rule mat_left_mult_one, unfold mat_carrier_def, simp)

lemma mat_right_mult_one: 
  "(A :: 'a :: semiring_1 mat) \<in> carrier\<^sub>m nr nc \<Longrightarrow> A \<otimes>\<^sub>m \<one>\<^sub>m nc = A"
  by (intro mat_eqI, auto)

lemma [simp]: "dim\<^sub>c (A :: 'a :: semiring_1 mat) = n \<Longrightarrow> A \<otimes>\<^sub>m \<one>\<^sub>m n = A"
  by (rule mat_right_mult_one, unfold mat_carrier_def, simp)

lemma mat_vec_mult_one[simp]: 
  "(v :: 'a :: semiring_1 vec) \<in> carrier\<^sub>v n \<Longrightarrow> \<one>\<^sub>m n \<otimes>\<^sub>m\<^sub>v v = v"
  by (intro vec_eqI, auto)

lemma mat_mult_left_distrib[algebra_simps]: assumes m: "A \<in> carrier\<^sub>m nr n"
  "B \<in> carrier\<^sub>m nr n" "C \<in> carrier\<^sub>m n nc"
  shows "(A \<oplus>\<^sub>m B) \<otimes>\<^sub>m C = A \<otimes>\<^sub>m C \<oplus>\<^sub>m B \<otimes>\<^sub>m C"
  using m by (intro mat_eqI, auto simp: scalar_prod_left_distrib[of _ n])

lemma mat_mult_right_distrib[algebra_simps]: assumes m: "A \<in> carrier\<^sub>m nr n"
  "B \<in> carrier\<^sub>m n nc" "C \<in> carrier\<^sub>m n nc"
  shows "A \<otimes>\<^sub>m (B \<oplus>\<^sub>m C) = A \<otimes>\<^sub>m B \<oplus>\<^sub>m A \<otimes>\<^sub>m C"
  using m by (intro mat_eqI, auto simp: scalar_prod_right_distrib[of _ n])

lemma mat_mult_vec_left_distrib[algebra_simps]: assumes m: "A \<in> carrier\<^sub>m nr nc"
  "B \<in> carrier\<^sub>m nr nc" "v \<in> carrier\<^sub>v nc"
  shows "(A \<oplus>\<^sub>m B) \<otimes>\<^sub>m\<^sub>v v = A \<otimes>\<^sub>m\<^sub>v v \<oplus>\<^sub>v B \<otimes>\<^sub>m\<^sub>v v"
  using m by (intro vec_eqI, auto intro!: scalar_prod_left_distrib)

lemma mat_mult_vec_right_distrib[algebra_simps]: assumes m: "A \<in> carrier\<^sub>m nr nc"
  "v\<^sub>1 \<in> carrier\<^sub>v nc" "v\<^sub>2 \<in> carrier\<^sub>v nc"
  shows "A \<otimes>\<^sub>m\<^sub>v (v\<^sub>1 \<oplus>\<^sub>v v\<^sub>2) = A \<otimes>\<^sub>m\<^sub>v v\<^sub>1 \<oplus>\<^sub>v A \<otimes>\<^sub>m\<^sub>v v\<^sub>2"
  using m by (intro vec_eqI, auto simp: scalar_prod_right_distrib[of _ nc])


lemma mat_mult_vec:
  assumes m: "(A::'a::field mat) \<in> carrier\<^sub>m nr nc" and v: "v \<in> carrier\<^sub>v nc"
  shows "A \<otimes>\<^sub>m\<^sub>v (k \<odot>\<^sub>v v) = k \<odot>\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" (is "?l = ?r")
proof
  have nr: "dim\<^sub>v ?l = nr" using m v by auto
  also have "... = dim\<^sub>v ?r" using m v by auto
  finally show "dim\<^sub>v ?l = dim\<^sub>v ?r".

  show "\<And>i. i < dim\<^sub>v ?r \<Longrightarrow> ?l $ i = ?r $ i"
  proof -
    fix i assume "i < dim\<^sub>v ?r"
    hence i: "i < dim\<^sub>r A" using nr m by auto
    hence i2: "i < dim\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" using m by auto
    show "?l $ i = ?r $ i"
    apply (subst (1) mat_mult_vec_def)
    apply (subst (2) vec_scalar_mult_def)
    unfolding vec_index_vec[OF i] vec_index_vec[OF i2]
    unfolding mat_mult_vec_def vec_scalar_mult_def
    unfolding scalar_prod_def vec_index_vec[OF i]
    by (simp add: mult.left_commute setsum_right_distrib)
  qed
qed

lemma scalar_prod_assoc: assumes *: "v\<^sub>1 \<in> carrier\<^sub>v nr" "A \<in> carrier\<^sub>m nr nc" "v\<^sub>2 \<in> carrier\<^sub>v nc"
  shows "vec nc (\<lambda>j. v\<^sub>1 \<bullet> col A j) \<bullet> v\<^sub>2 = v\<^sub>1 \<bullet> vec nr (\<lambda>i. row A i \<bullet> v\<^sub>2)"
proof -
  have "vec nc (\<lambda>j. v\<^sub>1 \<bullet> col A j) \<bullet> v\<^sub>2 = (\<Sum>i\<in>{0..<nc}. vec nc (\<lambda>j. \<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * col A j $ k) $ i * v\<^sub>2 $ i)"
    unfolding scalar_prod_def using * by auto
  also have "\<dots> = (\<Sum>i\<in>{0..<nc}. (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * col A i $ k) * v\<^sub>2 $ i)"
    by (rule setsum.cong, auto)
  also have "\<dots> = (\<Sum>i\<in>{0..<nc}. (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * col A i $ k * v\<^sub>2 $ i))"
    unfolding setsum_left_distrib ..
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. (\<Sum>i\<in>{0..<nc}. v\<^sub>1 $ k * col A i $ k * v\<^sub>2 $ i))"
    by (rule setsum.commute)
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. (\<Sum>i\<in>{0..<nc}. v\<^sub>1 $ k * (col A i $ k * v\<^sub>2 $ i)))"
    by (simp add: ac_simps)
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * (\<Sum>i\<in>{0..<nc}. col A i $ k * v\<^sub>2 $ i))"
    unfolding setsum_right_distrib ..
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * vec nr (\<lambda>k. \<Sum>i\<in>{0..<nc}. row A k $ i * v\<^sub>2 $ i) $ k)"
    using * by auto
  also have "\<dots> = v\<^sub>1 \<bullet> vec nr (\<lambda>i. row A i \<bullet> v\<^sub>2)" unfolding scalar_prod_def using * by simp
  finally show ?thesis .
qed

lemma mat_mult_assoc[simp]: 
  "A \<in> carrier\<^sub>m n\<^sub>1 n\<^sub>2 \<Longrightarrow> B \<in> carrier\<^sub>m n\<^sub>2 n\<^sub>3 \<Longrightarrow> C \<in> carrier\<^sub>m n\<^sub>3 n\<^sub>4
  \<Longrightarrow> (A \<otimes>\<^sub>m B) \<otimes>\<^sub>m C = A \<otimes>\<^sub>m (B \<otimes>\<^sub>m C)"
  by (intro mat_eqI, auto simp: scalar_prod_assoc)

lemma mat_vec_mult_assoc[simp]: 
  "A \<in> carrier\<^sub>m n\<^sub>1 n\<^sub>2 \<Longrightarrow> B \<in> carrier\<^sub>m n\<^sub>2 n\<^sub>3 \<Longrightarrow> v \<in> carrier\<^sub>v n\<^sub>3 
  \<Longrightarrow> (A \<otimes>\<^sub>m B) \<otimes>\<^sub>m\<^sub>v v = A \<otimes>\<^sub>m\<^sub>v (B \<otimes>\<^sub>m\<^sub>v v)"
  by (intro vec_eqI, auto simp add: mat_mult_vec_def scalar_prod_assoc)

lemma mat_monoid: "comm_monoid (monoid\<^sub>m TYPE('a :: comm_monoid_add) nr nc)"
  by (unfold_locales, auto simp: mat_monoid_def ac_simps)

lemma mat_group: "comm_group (monoid\<^sub>m TYPE('a :: ab_group_add) nr nc)"
  by (unfold_locales, insert mat_add_inv_exists, auto simp: mat_monoid_def ac_simps Units_def)

lemma mat_semiring: "semiring (ring\<^sub>m TYPE('a :: semiring_1) n b)"
  by (unfold_locales, auto simp: mat_ring_def algebra_simps)

lemma mat_ring: "ring (ring\<^sub>m TYPE('a :: comm_ring_1) n b)"
  by (unfold_locales, insert mat_add_inv_exists, auto simp: mat_ring_def algebra_simps Units_def)

lemma mat_module_abelian_group: "abelian_group (module\<^sub>m TYPE('a :: comm_ring_1) nr nc)"
  by (unfold_locales, insert mat_add_inv_exists, auto simp: mat_module_def Units_def)

lemma row_scalar_mult[simp]: assumes i: "i < dim\<^sub>r A"
  shows "row (k \<odot>\<^sub>m A) i = k \<odot>\<^sub>v (row A i)" 
  by (rule vec_eqI, insert i, auto)

lemma col_scalar_mult[simp]: assumes i: "i < dim\<^sub>c A"
  shows "col (k \<odot>\<^sub>m A) i = k \<odot>\<^sub>v (col A i)" 
  by (rule vec_eqI, insert i, auto)

lemma row_uminus[simp]: assumes i: "i < dim\<^sub>r A"
  shows "row (\<ominus>\<^sub>m A) i = \<ominus>\<^sub>v (row A i)" 
  by (rule vec_eqI, insert i, auto)

lemma scalar_prod_uminus_left[simp]: assumes dim: "dim\<^sub>v v = dim\<^sub>v (w :: 'a :: ring vec)"
  shows "\<ominus>\<^sub>v v \<bullet> w = - (v \<bullet> w)"
  unfolding scalar_prod_def dim[symmetric]
  by (subst setsum_negf[symmetric], rule setsum.cong, auto)

lemma col_uminus[simp]: assumes i: "i < dim\<^sub>c A"
  shows "col (\<ominus>\<^sub>m A) i = \<ominus>\<^sub>v (col A i)" 
  by (rule vec_eqI, insert i, auto)

lemma scalar_prod_uminus_right[simp]: assumes dim: "dim\<^sub>v v = dim\<^sub>v (w :: 'a :: ring vec)"
  shows "v \<bullet> \<ominus>\<^sub>v w = - (v \<bullet> w)"
  unfolding scalar_prod_def dim
  by (subst setsum_negf[symmetric], rule setsum.cong, auto)

context fixes A B :: "'a :: ring mat" 
  assumes dim: "dim\<^sub>c A = dim\<^sub>r B"
begin
lemma mat_uminus_mult_left[simp]: "(\<ominus>\<^sub>m A \<otimes>\<^sub>m B) = \<ominus>\<^sub>m (A \<otimes>\<^sub>m B)"
  by (intro mat_eqI, insert dim, auto)

lemma mat_uminus_mult_right[simp]: "(A \<otimes>\<^sub>m \<ominus>\<^sub>m B) = \<ominus>\<^sub>m (A \<otimes>\<^sub>m B)"
  by (intro mat_eqI, insert dim, auto)
end

lemma negate_mat_vec_mult[simp]: assumes v: "dim\<^sub>v v = dim\<^sub>c (A :: 'a :: ring mat)"
  shows "\<ominus>\<^sub>m A \<otimes>\<^sub>m\<^sub>v v = \<ominus>\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" 
  using v by (intro vec_eqI, auto)

lemma uminus_vec_zero_eq: assumes v: "(v :: 'a :: group_add vec) \<in> carrier\<^sub>v n"
  shows "(\<ominus>\<^sub>v v = \<zero>\<^sub>v n) = (v = \<zero>\<^sub>v n)"
proof
  assume z: "\<ominus>\<^sub>v v = \<zero>\<^sub>v n"
  {
    fix i
    assume i: "i < n"
    have "v $ i = - (- (v $ i))" by simp
    also have "- (v $ i) = 0" using arg_cong[OF z, of "\<lambda> v. v $ i"] i v by auto
    also have "- 0 = (0 :: 'a)" by simp
    finally have "v $ i = 0" .
  }
  thus "v = \<zero>\<^sub>v n" using v
    by (intro vec_eqI, auto)
qed auto

lemma mat_map_closed[simp]: 
  "(map\<^sub>m f A \<in> carrier\<^sub>m nr nc) = (A \<in> carrier\<^sub>m nr nc)"
  unfolding mat_carrier_def by auto

lemma col_mat_map[simp]:
  assumes "j < dim\<^sub>c A" shows "col (map\<^sub>m f A) j = map\<^sub>v f (col A j)"
  unfolding mat_map_def map_vec_def using assms by auto

lemma scalar_vec_one[simp]: "1 \<odot>\<^sub>v (v :: 'a :: semiring_1 vec) = v"
  by (rule vec_eqI, auto)

lemma scalar_prod_scalar_right[simp]: 
  "dim\<^sub>v w = dim\<^sub>v v \<Longrightarrow> w \<bullet> (k \<odot>\<^sub>v v) = (k :: 'a :: comm_semiring_0) * (w \<bullet> v)"
  unfolding scalar_prod_def setsum_right_distrib
  by (auto intro: setsum.cong simp: ac_simps)

lemma scalar_prod_scalar_left[simp]: 
  "dim\<^sub>v w = dim\<^sub>v v \<Longrightarrow> (k \<odot>\<^sub>v w) \<bullet> v = (k :: 'a :: comm_semiring_0) * (w \<bullet> v)"
  unfolding scalar_prod_def setsum_right_distrib
  by (auto intro: setsum.cong simp: ac_simps)

lemma mat_mult_scalar_comm: assumes A: "A \<in> carrier\<^sub>m nr n" and B: "B \<in> carrier\<^sub>m n nc"
  shows "A \<otimes>\<^sub>m (k \<odot>\<^sub>m B) = (k :: 'a :: comm_semiring_0) \<odot>\<^sub>m (A \<otimes>\<^sub>m B)"
  by (rule mat_eqI, insert A B, auto)

lemma mat_add_scalar_distrib_left: assumes "A \<in> carrier\<^sub>m nr nc" "B \<in> carrier\<^sub>m nr nc"
  shows "k \<odot>\<^sub>m (A \<oplus>\<^sub>m B) = (k :: 'a :: semiring) \<odot>\<^sub>m A \<oplus>\<^sub>m k \<odot>\<^sub>m B"
  by (rule mat_eqI, insert assms, auto simp: field_simps)

lemma mat_add_scalar_distrib_right: assumes "A \<in> carrier\<^sub>m nr nc"
  shows "(k + l) \<odot>\<^sub>m A = (k :: 'a :: semiring) \<odot>\<^sub>m A \<oplus>\<^sub>m l \<odot>\<^sub>m A"
  by (rule mat_eqI, insert assms, auto simp: field_simps)

lemma mat_mult_scalar_assoc: assumes A: "A \<in> carrier\<^sub>m nr n" and B: "B \<in> carrier\<^sub>m n nc"
  shows "(k \<odot>\<^sub>m A) \<otimes>\<^sub>m B = (k :: 'a :: comm_semiring_0) \<odot>\<^sub>m (A \<otimes>\<^sub>m B)"
  by (rule mat_eqI, insert A B, auto) 

definition mat_similar_wit :: "'a :: semiring_1 mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "mat_similar_wit A B P Q = (let n = dim\<^sub>r A in {A,B,P,Q} \<subseteq> carrier\<^sub>m n n \<and> P \<otimes>\<^sub>m Q = \<one>\<^sub>m n \<and> Q \<otimes>\<^sub>m P = \<one>\<^sub>m n \<and>
    A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q)"

definition mat_similar :: "'a :: semiring_1 mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "mat_similar A B = (\<exists> P Q. mat_similar_wit A B P Q)"

lemma mat_similarD: assumes "mat_similar A B"
  shows "\<exists> n P Q. {A,B,P,Q} \<subseteq> carrier\<^sub>m n n \<and> P \<otimes>\<^sub>m Q = \<one>\<^sub>m n \<and> Q \<otimes>\<^sub>m P = \<one>\<^sub>m n \<and> A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q"
  using assms unfolding mat_similar_def mat_similar_wit_def[abs_def] Let_def by blast

lemma mat_similarI: assumes "{A,B,P,Q} \<subseteq> carrier\<^sub>m n n" "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q"
  shows "mat_similar A B" unfolding mat_similar_def 
  by (rule exI[of _ P], rule exI[of _ Q], unfold mat_similar_wit_def Let_def, insert assms, auto)

fun mat_pow :: "'a :: semiring_1 mat \<Rightarrow> nat \<Rightarrow> 'a mat" (infixr "^\<^sub>m" 75) where
  "A ^\<^sub>m 0 = \<one>\<^sub>m (dim\<^sub>r A)"
| "A ^\<^sub>m (Suc k) = A ^\<^sub>m k \<otimes>\<^sub>m A"

lemma mat_pow_dim[simp]:
  "dim\<^sub>r (A ^\<^sub>m k) = dim\<^sub>r A"
  "dim\<^sub>c (A ^\<^sub>m k) = (if k = 0 then dim\<^sub>r A else dim\<^sub>c A)"
  by (induct k, auto)

lemma mat_pow_dim_square[simp]:
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> dim\<^sub>r (A ^\<^sub>m k) = n"
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> dim\<^sub>c (A ^\<^sub>m k) = n"
  by auto

lemma mat_pow_closed[simp]: "A \<in> carrier\<^sub>m n n \<Longrightarrow> A ^\<^sub>m k \<in> carrier\<^sub>m n n" 
  unfolding mat_carrier_def by auto

definition mat_diag :: "'a mat \<Rightarrow> 'a list" where
  "mat_diag A = map (\<lambda> i. A $$ (i,i)) [0 ..< dim\<^sub>r A]"

lemma listprod_diag_setprod: "listprod (mat_diag A) = (\<Prod> i = 0 ..< dim\<^sub>r A. A $$ (i,i))"
  unfolding mat_diag_def 
  by (subst setprod.distinct_set_conv_list[symmetric], auto)

lemma mat_diag_transpose[simp]: "dim\<^sub>r A = dim\<^sub>c A \<Longrightarrow>
  mat_diag (transpose\<^sub>m A) = mat_diag A" unfolding mat_diag_def by auto

lemma mat_diag_zero[simp]: "mat_diag (\<zero>\<^sub>m n n) = replicate n 0"
  unfolding mat_diag_def 
  by (rule nth_equalityI, auto)

lemma mat_diag_one[simp]: "mat_diag (\<one>\<^sub>m n) = replicate n 1"
  unfolding mat_diag_def 
  by (rule nth_equalityI, auto)

lemma mat_pow_ring_pow: assumes A: "(A :: ('a :: semiring_1)mat) \<in> carrier\<^sub>m n n" 
  shows "A ^\<^sub>m k = A (^)\<^bsub>mat_ring TYPE('a) n b\<^esub> k" 
  (is "_ = A (^)\<^bsub>?C\<^esub> k")
proof -
  interpret semiring ?C by (rule mat_semiring)
  show ?thesis
    by (induct k, insert A, auto simp: mat_ring_def nat_pow_def)
qed

definition diagonal_mat :: "'a::zero mat \<Rightarrow> bool" where
  "diagonal_mat A \<equiv> \<forall>i<dim\<^sub>r A. \<forall>j<dim\<^sub>c A. i \<noteq> j \<longrightarrow> A $$ (i,j) = 0"

definition (in comm_monoid_add) mat_sum :: "'a mat \<Rightarrow> 'a" where 
  "mat_sum A = setsum (\<lambda> ij. A $$ ij) ({0 ..< dim\<^sub>r A} \<times> {0 ..< dim\<^sub>c A})"

lemma mat_sum_0[simp]: "mat_sum (\<zero>\<^sub>m nr nc) = (0 :: 'a :: comm_monoid_add)"
  unfolding mat_sum_def
  by (rule setsum.neutral, auto)

lemma mat_sum_add: assumes A: "(A :: 'a :: comm_monoid_add mat) \<in> carrier\<^sub>m nr nc" and B: "B \<in> carrier\<^sub>m nr nc" 
  shows "mat_sum (A \<oplus>\<^sub>m B) = mat_sum A + mat_sum B"
proof -
  from A B have id: "dim\<^sub>r A = nr" "dim\<^sub>r B = nr" "dim\<^sub>c A = nc" "dim\<^sub>c B = nc" 
    by auto
  show ?thesis unfolding mat_sum_def id
    by (subst setsum.distrib[symmetric], rule setsum.cong, insert A B, auto)
qed

subsection \<open>Update Operators\<close>

definition vec_update :: "'a vec \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a vec" ("_ |\<^sub>v _ \<mapsto> _" [60,61,62] 60)
  where "v |\<^sub>v i \<mapsto> a = vec (dim\<^sub>v v) (\<lambda>i'. if i' = i then a else v $ i')"

definition mat_update :: "'a mat \<Rightarrow> nat \<times> nat \<Rightarrow> 'a \<Rightarrow> 'a mat" ("_ |\<^sub>m _ \<mapsto> _" [60,61,62] 60)
  where "A |\<^sub>m ij \<mapsto> a = mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda>ij'. if ij' = ij then a else A $$ ij')"

term "\<zero>\<^sub>v 6 |\<^sub>v 1 \<mapsto> 2 |\<^sub>v 2 \<mapsto> 3"

term "\<zero>\<^sub>m 6 4 |\<^sub>m (1,3) \<mapsto> 2 |\<^sub>m (2,1) \<mapsto> 3"

lemma vec_dim_update[simp]:
  "dim\<^sub>v (v |\<^sub>v i \<mapsto> a) = dim\<^sub>v v" unfolding vec_update_def by simp

lemma vec_index_updated[simp]:
  assumes "i < dim\<^sub>v v" shows "(v |\<^sub>v i \<mapsto> a) $ i = a"
  unfolding vec_update_def using assms by simp

lemma vec_index_update_others[simp]:
  assumes "i' \<noteq> i" shows "(v |\<^sub>v i \<mapsto> a) $ i' = v $ i'"
  unfolding vec_update_def
  using assms apply transfer unfolding mk_vec_def by auto

lemma mat_dim_update[simp]:
  "dim\<^sub>r (A |\<^sub>m ij \<mapsto> a) = dim\<^sub>r A"
  "dim\<^sub>c (A |\<^sub>m ij \<mapsto> a) = dim\<^sub>c A" unfolding mat_update_def by simp+

lemma mat_index_updated[simp]:
  assumes "i < dim\<^sub>r A" "j < dim\<^sub>c A" shows "(A |\<^sub>m (i,j) \<mapsto> a) $$ (i,j) = a"
  unfolding mat_update_def using assms by simp

lemma mat_index_update_others[simp]:
  assumes i': "i' < dim\<^sub>r A" and j': "j' < dim\<^sub>c A" and neq: "(i',j') \<noteq> ij"
  shows "(A |\<^sub>m ij \<mapsto> a) $$ (i',j') = A $$ (i',j')"
  unfolding mat_update_def using assms by auto

subsection \<open>Block Vectors and Matrices\<close>

definition vec_append :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixr "@\<^sub>v" 65) where
  "v @\<^sub>v w \<equiv> let n = dim\<^sub>v v; m = dim\<^sub>v w in 
    vec (n + m) (\<lambda> i. if i < n then v $ i else w $ (i - n))"

lemma vec_append_index[simp]: "i < dim\<^sub>v v + dim\<^sub>v w
  \<Longrightarrow> (v @\<^sub>v w) $ i = (if i < dim\<^sub>v v then v $ i else w $ (i - dim\<^sub>v v))"
  "dim\<^sub>v (v @\<^sub>v w) = dim\<^sub>v v + dim\<^sub>v w"
  unfolding vec_append_def Let_def by auto

lemma vec_append_carrier[simp]: 
  "v \<in> carrier\<^sub>v n1 \<Longrightarrow> w \<in> carrier\<^sub>v n2 \<Longrightarrow> v @\<^sub>v w \<in> carrier\<^sub>v (n1 + n2)"
  unfolding vec_carrier_def by auto

lemma scalar_prod_append: assumes "v1 \<in> carrier\<^sub>v n1" "v2 \<in> carrier\<^sub>v n2"
  "w1 \<in> carrier\<^sub>v n1" "w2 \<in> carrier\<^sub>v n2"
  shows "(v1 @\<^sub>v v2) \<bullet> (w1 @\<^sub>v w2) = v1 \<bullet> w1 + v2 \<bullet> w2"
proof -
  from assms have dim: "dim\<^sub>v v1 = n1" "dim\<^sub>v v2 = n2" "dim\<^sub>v w1 = n1" "dim\<^sub>v w2 = n2" by auto
  have id: "{0 ..< n1 + n2} = {0 ..< n1} \<union> {n1 ..< n1 + n2}" by auto
  have id2: "{n1 ..< n1 + n2} = (\<lambda> x. x + n1) ` {0 ..< n2}" 
    by (simp add: add.commute image_add_atLeastLessThan)
  have "(v1 @\<^sub>v v2) \<bullet> (w1 @\<^sub>v w2) = (\<Sum>i = 0..<n1. v1 $ i * w1 $ i) +
    (\<Sum>i = n1..<n1 + n2. v2 $ (i - n1) * w2 $ (i - n1))"
  unfolding scalar_prod_def
    by (auto simp: dim id, subst setsum.union_disjoint, insert assms, force+)
  also have "(\<Sum>i = n1..<n1 + n2. v2 $ (i - n1) * w2 $ (i - n1))
    = (\<Sum>i = 0..< n2. v2 $ i * w2 $ i)"
    by (rule setsum.reindex_cong[OF _ id2], auto)
  finally show ?thesis by (simp, insert assms, auto simp: scalar_prod_def)
qed

definition "vec_first v n \<equiv> vec n (\<lambda>i. v $ i)"
definition "vec_last v n \<equiv> vec n (\<lambda>i. v $ (dim\<^sub>v v - n + i))"

lemma dim_vec_first[simp]: "dim\<^sub>v (vec_first v n) = n" unfolding vec_first_def by auto
lemma dim_vec_last[simp]: "dim\<^sub>v (vec_last v n) = n" unfolding vec_last_def by auto

lemma vec_first_carrier[simp]: "vec_first v n \<in> carrier\<^sub>v n" by (rule vec_elemsI, auto)
lemma vec_last_carrier[simp]: "vec_last v n \<in> carrier\<^sub>v n" by (rule vec_elemsI, auto)

lemma vec_first_last_append[simp]:
  assumes "v \<in> carrier\<^sub>v (n+m)" shows "vec_first v n @\<^sub>v vec_last v m = v"
  apply(rule) unfolding vec_first_def vec_last_def using assms by auto

(* A B
   C D *)
definition four_block_mat :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "four_block_mat A B C D = 
    (let nra = dim\<^sub>r A; nrd = dim\<^sub>r D; 
         nca = dim\<^sub>c A; ncd = dim\<^sub>c D
       in
    mat (nra + nrd) (nca + ncd) (\<lambda> (i,j). if i < nra then 
      if j < nca then A $$ (i,j) else B $$ (i,j - nca)
      else if j < nca then C $$ (i - nra, j) else D $$ (i - nra, j - nca)))"

lemma four_block_mat_index[simp]: 
  "i < dim\<^sub>r A + dim\<^sub>r D \<Longrightarrow> j < dim\<^sub>c A + dim\<^sub>c D \<Longrightarrow> four_block_mat A B C D $$ (i,j) 
  = (if i < dim\<^sub>r A then 
      if j < dim\<^sub>c A then A $$ (i,j) else B $$ (i,j - dim\<^sub>c A)
      else if j < dim\<^sub>c A then C $$ (i - dim\<^sub>r A, j) else D $$ (i - dim\<^sub>r A, j - dim\<^sub>c A))"
  "dim\<^sub>r (four_block_mat A B C D) = dim\<^sub>r A + dim\<^sub>r D"
  "dim\<^sub>c (four_block_mat A B C D) = dim\<^sub>c A + dim\<^sub>c D"
  unfolding four_block_mat_def Let_def by auto

lemma four_block_mat_carrier[simp]: 
  "A \<in> carrier\<^sub>m nr1 nc1 \<Longrightarrow> D \<in> carrier\<^sub>m nr2 nc2 \<Longrightarrow>
  four_block_mat A B C D \<in> carrier\<^sub>m (nr1 + nr2) (nc1 + nc2)"
  unfolding mat_carrier_def by auto

lemma four_block_mat_cong: "A1 = B1 \<Longrightarrow> A2 = B2 \<Longrightarrow> A3 = B3 \<Longrightarrow> A4 = B4 \<Longrightarrow>
  four_block_mat A1 A2 A3 A4 = four_block_mat B1 B2 B3 B4" by auto

lemma four_block_one_mat[simp]: 
  "four_block_mat (\<one>\<^sub>m n1) (\<zero>\<^sub>m n1 n2) (\<zero>\<^sub>m n2 n1) (\<one>\<^sub>m n2) = \<one>\<^sub>m (n1 + n2)"
  by (rule mat_eqI, auto)

lemma four_block_zero_mat[simp]: 
  "four_block_mat (\<zero>\<^sub>m nr1 nc1) (\<zero>\<^sub>m nr1 nc2) (\<zero>\<^sub>m nr2 nc1) (\<zero>\<^sub>m nr2 nc2) = \<zero>\<^sub>m (nr1 + nr2) (nc1 + nc2)"
  by (rule mat_eqI, auto)

lemma row_four_block_mat:
  assumes c: "A \<in> carrier\<^sub>m nr1 nc1" "B \<in> carrier\<^sub>m nr1 nc2"
  "C \<in> carrier\<^sub>m nr2 nc1" "D \<in> carrier\<^sub>m nr2 nc2"
  shows 
  "i < nr1 \<Longrightarrow> row (four_block_mat A B C D) i = row A i @\<^sub>v row B i" (is "_ \<Longrightarrow> ?AB")
  "\<not> i < nr1 \<Longrightarrow> i < nr1 + nr2 \<Longrightarrow> row (four_block_mat A B C D) i = row C (i - nr1) @\<^sub>v row D (i - nr1)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?CD")
proof -
  assume i: "i < nr1"
  show ?AB by (rule vec_eqI, insert i c, auto)
next
  assume i: "\<not> i < nr1" "i < nr1 + nr2"
  show ?CD by (rule vec_eqI, insert i c, auto)
qed  

lemma col_four_block_mat:
  assumes c: "A \<in> carrier\<^sub>m nr1 nc1" "B \<in> carrier\<^sub>m nr1 nc2"
  "C \<in> carrier\<^sub>m nr2 nc1" "D \<in> carrier\<^sub>m nr2 nc2"
  shows 
  "j < nc1 \<Longrightarrow> col (four_block_mat A B C D) j = col A j @\<^sub>v col C j" (is "_ \<Longrightarrow> ?AC")
  "\<not> j < nc1 \<Longrightarrow> j < nc1 + nc2 \<Longrightarrow> col (four_block_mat A B C D) j = col B (j - nc1) @\<^sub>v col D (j - nc1)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?BD")
proof -
  assume j: "j < nc1"
  show ?AC by (rule vec_eqI, insert j c, auto)
next
  assume j: "\<not> j < nc1" "j < nc1 + nc2"
  show ?BD by (rule vec_eqI, insert j c, auto)
qed  
 
lemma four_block_mat_mult: assumes 
  c1: "A1 \<in> carrier\<^sub>m nr1 n1" "B1 \<in> carrier\<^sub>m nr1 n2" "C1 \<in> carrier\<^sub>m nr2 n1" "D1 \<in> carrier\<^sub>m nr2 n2" and
  c2: "A2 \<in> carrier\<^sub>m n1 nc1" "B2 \<in> carrier\<^sub>m n1 nc2" "C2 \<in> carrier\<^sub>m n2 nc1" "D2 \<in> carrier\<^sub>m n2 nc2"
  shows "four_block_mat A1 B1 C1 D1 \<otimes>\<^sub>m four_block_mat A2 B2 C2 D2
  = four_block_mat (A1 \<otimes>\<^sub>m A2 \<oplus>\<^sub>m B1 \<otimes>\<^sub>m C2) (A1 \<otimes>\<^sub>m B2 \<oplus>\<^sub>m B1 \<otimes>\<^sub>m D2) 
    (C1 \<otimes>\<^sub>m A2 \<oplus>\<^sub>m D1 \<otimes>\<^sub>m C2) (C1 \<otimes>\<^sub>m B2 \<oplus>\<^sub>m D1 \<otimes>\<^sub>m D2)" (is "?M1 \<otimes>\<^sub>m ?M2 = _")
proof -
  note row = row_four_block_mat[OF c1]
  note col = col_four_block_mat[OF c2]
  {
    fix i j
    assume i: "i < nr1" and j: "j < nc1"
    have "row ?M1 i \<bullet> col ?M2 j = row A1 i \<bullet> col A2 j + row B1 i \<bullet> col C2 j"
      unfolding row(1)[OF i] col(1)[OF j] 
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i j, auto)
  }
  moreover
  {
    fix i j
    assume i: "\<not> i < nr1" "i < nr1 + nr2" and j: "j < nc1"
    hence i': "i - nr1 < nr2" by auto
    have "row ?M1 i \<bullet> col ?M2 j = row C1 (i - nr1) \<bullet> col A2 j + row D1 (i - nr1) \<bullet> col C2 j" 
      unfolding row(2)[OF i] col(1)[OF j]
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i i' j, auto)
  }
  moreover
  {
    fix i j
    assume i: "i < nr1" and j: "\<not> j < nc1" "j < nc1 + nc2"
    hence j': "j - nc1 < nc2" by auto
    have "row ?M1 i \<bullet> col ?M2 j = row A1 i \<bullet> col B2 (j - nc1) + row B1 i \<bullet> col D2 (j - nc1)" 
      unfolding row(1)[OF i] col(2)[OF j] 
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i j' j, auto)
  }
  moreover
  {
    fix i j
    assume i: "\<not> i < nr1" "i < nr1 + nr2" and j: "\<not> j < nc1" "j < nc1 + nc2"
    hence i': "i - nr1 < nr2" and j': "j - nc1 < nc2" by auto
    have "row ?M1 i \<bullet> col ?M2 j = row C1 (i - nr1) \<bullet> col B2 (j - nc1) + row D1 (i - nr1) \<bullet> col D2 (j - nc1)" 
      unfolding row(2)[OF i] col(2)[OF j]
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i i' j' j, auto)
  }
  ultimately show ?thesis
    by (intro mat_eqI, insert c1 c2, auto)
qed

lemma four_block_mat_elements:
  assumes c: "A \<in> carrier\<^sub>m nr1 nc1" "B \<in> carrier\<^sub>m nr1 nc2"
  "C \<in> carrier\<^sub>m nr2 nc1" "D \<in> carrier\<^sub>m nr2 nc2"
  shows
  "mat_elements (four_block_mat A B C D) \<subseteq>
   mat_elements A \<union> mat_elements B \<union> mat_elements C \<union> mat_elements D"
   (is "mat_elements ?four \<subseteq> _")
proof rule
  fix a assume "a \<in> mat_elements ?four"
  then obtain i j
    where i4: "i < dim\<^sub>r ?four" and j4: "j < dim\<^sub>c ?four" and a: "a = ?four $$ (i, j)"
    by auto
  show "a \<in> mat_elements A \<union> mat_elements B \<union> mat_elements C \<union> mat_elements D"
  proof (cases "i < nr1")
    case True note i1 = this
      show ?thesis
      proof (cases "j < nc1")
        case True
          then have "a = A $$ (i,j)" using c i1 a by simp
          thus ?thesis using c i1 True by auto next
        case False
          then have "a = B $$ (i,j-nc1)" using c i1 a j4 by simp
          moreover have "j - nc1 < nc2" using c j4 False by auto
          ultimately show ?thesis using c i1 by auto
      qed next
    case False note i1 = this
      have i2: "i - nr1 < nr2" using c i1 i4 by auto
      show ?thesis
      proof (cases "j < nc1")
        case True
          then have "a = C $$ (i-nr1,j)" using c i2 a i1 by simp
          thus ?thesis using c i2 True by auto next
        case False
          then have "a = D $$ (i-nr1,j-nc1)" using c i2 a i1 j4 by simp
          moreover have "j - nc1 < nc2" using c j4 False by auto
          ultimately show ?thesis using c i2 by auto
      qed
  qed
qed

lemma four_block_mat_assoc: fixes FB :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a :: zero mat"
  defines FB: "FB \<equiv> \<lambda> Bb Cc. four_block_mat Bb (\<zero>\<^sub>m (dim\<^sub>r Bb) (dim\<^sub>c Cc)) (\<zero>\<^sub>m (dim\<^sub>r Cc) (dim\<^sub>c Bb)) Cc"
  shows "FB A (FB B C) = FB (FB A B) C" (is "?L = ?R")
proof -
  let ?ar = "dim\<^sub>r A" let ?ac = "dim\<^sub>c A"
  let ?br = "dim\<^sub>r B" let ?bc = "dim\<^sub>c B"
  let ?cr = "dim\<^sub>r C" let ?cc = "dim\<^sub>c C"
  let ?r = "?ar + ?br + ?cr" let ?c = "?ac + ?bc + ?cc"
  let ?BC = "FB B C" let ?AB = "FB A B"
  have dL: "dim\<^sub>r ?L = ?r" "dim\<^sub>c ?L = ?c" unfolding FB by auto
  have dR: "dim\<^sub>r ?R = ?ar + ?br + ?cr" "dim\<^sub>c ?R = ?ac + ?bc + ?cc" unfolding FB by auto
  have dBC: "dim\<^sub>r ?BC = ?br + ?cr" "dim\<^sub>c ?BC = ?bc + ?cc" unfolding FB by auto
  have dAB: "dim\<^sub>r ?AB = ?ar + ?br" "dim\<^sub>c ?AB = ?ac + ?bc" unfolding FB by auto
  show ?thesis 
  proof (intro mat_eqI[of ?R ?L, unfolded dL dR, OF _ refl refl])
    fix i j
    assume i: "i < ?r" and j: "j < ?c"
    show "?L $$ (i,j) = ?R $$ (i,j)"
    proof (cases "i < ?ar")
      case True note i = this
      thus ?thesis using j
        by (cases "j < ?ac", auto simp: FB)
    next
      case False note ii = this
      show ?thesis
      proof (cases "j < ?ac")
        case True
        with i ii show ?thesis unfolding FB by auto
      next
        case False note jj = this
        from j jj i ii have L: "?L $$ (i,j) = ?BC $$ (i - ?ar, j - ?ac)" unfolding FB by auto
        have R: "?R $$ (i,j) = ?BC $$ (i - ?ar, j - ?ac)" using ii jj i j
          by (cases "i < ?ar + ?br"; cases "j < ?ac + ?bc", auto simp: FB)
        show ?thesis unfolding L R ..
      qed
    qed
  qed
qed

definition split_block :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat \<times> 'a mat)"
  where "split_block A sr sc = (let 
    nr = dim\<^sub>r A; nc = dim\<^sub>c A;
    nr2 = nr - sr; nc2 = nc - sc;
    A1 = mat sr sc (\<lambda> ij. A $$ ij);
    A2 = mat sr nc2 (\<lambda> (i,j). A $$ (i,j+sc));
    A3 = mat nr2 sc (\<lambda> (i,j). A $$ (i+sr,j));
    A4 = mat nr2 nc2 (\<lambda> (i,j). A $$ (i+sr,j+sc))
  in (A1,A2,A3,A4))"

lemma split_block: assumes res: "split_block A sr1 sc1 = (A1,A2,A3,A4)"
  and dims: "dim\<^sub>r A = sr1 + sr2" "dim\<^sub>c A = sc1 + sc2"
  shows "A1 \<in> carrier\<^sub>m sr1 sc1" "A2 \<in> carrier\<^sub>m sr1 sc2"
    "A3 \<in> carrier\<^sub>m sr2 sc1" "A4 \<in> carrier\<^sub>m sr2 sc2"
    "A = four_block_mat A1 A2 A3 A4"
  using res unfolding split_block_def Let_def 
  by (auto simp: dims)

text \<open>Using @{const four_block_mat} we define block-diagonal matrices.\<close>

fun diag_block_mat :: "'a :: zero mat list \<Rightarrow> 'a mat" where
  "diag_block_mat [] = \<zero>\<^sub>m 0 0"
| "diag_block_mat (A # As) = (let 
     B = diag_block_mat As
     in four_block_mat A (\<zero>\<^sub>m (dim\<^sub>r A) (dim\<^sub>c B)) (\<zero>\<^sub>m (dim\<^sub>r B) (dim\<^sub>c A)) B)"

lemma diag_block_mat_dim:
  "dim\<^sub>r (diag_block_mat As) = listsum (map dim\<^sub>r As)" (is "?row")
  "dim\<^sub>c (diag_block_mat As) = listsum (map dim\<^sub>c As)" (is "?col")
proof -
  from assms have "?row \<and> ?col"
    by (induct As, auto simp: Let_def)
  thus ?row and ?col by auto
qed

lemma diag_block_mat_singleton[simp]: "diag_block_mat [A] = A"
  by auto

lemma diag_block_mat_append: "diag_block_mat (As @ Bs) = 
  (let A = diag_block_mat As; B = diag_block_mat Bs
  in four_block_mat A (\<zero>\<^sub>m (dim\<^sub>r A) (dim\<^sub>c B)) (\<zero>\<^sub>m (dim\<^sub>r B) (dim\<^sub>c A)) B)" 
  unfolding Let_def
proof (induct As)
  case (Cons A As)
  show ?case
    unfolding append.simps
    unfolding diag_block_mat.simps Let_def
    unfolding Cons 
    by (rule four_block_mat_assoc)
qed auto
  
lemma diag_block_mat_last: "diag_block_mat (As @ [B]) = 
  (let A = diag_block_mat As
  in four_block_mat A (\<zero>\<^sub>m (dim\<^sub>r A) (dim\<^sub>c B)) (\<zero>\<^sub>m (dim\<^sub>r B) (dim\<^sub>c A)) B)"
  unfolding diag_block_mat_append diag_block_mat_singleton by auto  


lemma diag_block_mat_square:
  "Ball (set As) square_mat \<Longrightarrow> square_mat (diag_block_mat As)"
by (induct As, auto simp:Let_def)

lemma diag_block_mat_one[simp]: 
  "diag_block_mat (map (\<lambda>A. \<one>\<^sub>m (dim\<^sub>r A)) As) = (\<one>\<^sub>m (listsum (map dim\<^sub>r As)))"
  by (induct As, auto simp: Let_def)

lemma diag_block_mat_elements:
  "mat_elements (diag_block_mat As) \<subseteq> {0} \<union> \<Union> set (map mat_elements As)"
proof (induct As)
  case Nil then show ?case using diag_block_mat_dim[of Nil] by auto next
  case (Cons A As)
    let ?D = "diag_block_mat As"
    let ?B = "\<zero>\<^sub>m (dim\<^sub>r A) (dim\<^sub>c ?D)"
    let ?C = "\<zero>\<^sub>m (dim\<^sub>r ?D) (dim\<^sub>c A)"
    have A: "A \<in> carrier\<^sub>m (dim\<^sub>r A) (dim\<^sub>c A)" by auto
    have B: "?B \<in> carrier\<^sub>m (dim\<^sub>r A) (dim\<^sub>c ?D)" by auto
    have C: "?C \<in> carrier\<^sub>m (dim\<^sub>r ?D) (dim\<^sub>c A)" by auto
    have D: "?D \<in> carrier\<^sub>m (dim\<^sub>r ?D) (dim\<^sub>c ?D)" by auto
    have
      "mat_elements (diag_block_mat (A#As)) \<subseteq>
       mat_elements A \<union> mat_elements ?B \<union> mat_elements ?C \<union> mat_elements ?D"
      unfolding diag_block_mat.simps Let_def
      using four_block_mat_elements[OF A B C D] mat_elements_0
      by auto
    also have "... \<subseteq> {0} \<union> mat_elements A \<union> mat_elements ?D"
      using mat_elements_0 by auto
    finally show ?case using Cons by auto
qed

lemma diag_block_mat_pow: assumes sq: "Ball (set As) square_mat"
  shows "diag_block_mat As ^\<^sub>m n = diag_block_mat (map (\<lambda> A. A ^\<^sub>m n) As)" (is "?As ^\<^sub>m _ = _")
proof (induct n)
  case 0
  have "?As ^\<^sub>m 0 = \<one>\<^sub>m (dim\<^sub>r ?As)" by simp
  also have "dim\<^sub>r ?As = listsum (map dim\<^sub>r As)"
    using diag_block_mat_square[OF sq] unfolding diag_block_mat_dim by auto
  also have "\<one>\<^sub>m \<dots> = diag_block_mat (map (\<lambda>A. \<one>\<^sub>m (dim\<^sub>r A)) As)" by simp
  also have "\<dots> = diag_block_mat (map (\<lambda> A. A ^\<^sub>m 0) As)" by simp
  finally show ?case .
next
  case (Suc n)
  let ?An = "\<lambda> As. diag_block_mat (map (\<lambda>A. A ^\<^sub>m n) As)"
  let ?Asn = "\<lambda> As. diag_block_mat (map (\<lambda>A. A ^\<^sub>m n \<otimes>\<^sub>m A) As)"
  from Suc have "?case = (?An As \<otimes>\<^sub>m diag_block_mat As = ?Asn As)" by simp
  also have "\<dots>" using sq
  proof (induct As)
    case (Cons A As)
    hence IH: "?An As \<otimes>\<^sub>m diag_block_mat As = ?Asn As" 
      and sq: "Ball (set As) square_mat" and A: "dim\<^sub>c A = dim\<^sub>r A" by auto
    have sq2: "Ball (set (List.map (\<lambda>A. A ^\<^sub>m n) As)) square_mat"
      and sq3: "Ball (set (List.map (\<lambda>A. A ^\<^sub>m n \<otimes>\<^sub>m A) As)) square_mat"
      using sq by auto
    def n1 \<equiv> "dim\<^sub>r A"
    def n2 \<equiv> "listsum (map dim\<^sub>r As)"
    from A have A: "A \<in> carrier\<^sub>m n1 n1" unfolding n1_def mat_carrier_def by simp
    have [simp]: "dim\<^sub>c (?An As) = n2" "dim\<^sub>r (?An As) = n2"
      unfolding n2_def
      using diag_block_mat_square[OF sq2,unfolded square_mat.simps]
      unfolding diag_block_mat_dim map_map by (auto simp:o_def)
    have [simp]: "dim\<^sub>c (?Asn As) = n2" "dim\<^sub>r (?Asn As) = n2"
      unfolding n2_def
      using diag_block_mat_square[OF sq3,unfolded square_mat.simps]
      unfolding diag_block_mat_dim map_map by (auto simp:o_def)
    have [simp]:
      "dim\<^sub>r (diag_block_mat As) = n2"
      "dim\<^sub>c (diag_block_mat As) = n2"
      unfolding n2_def
      using diag_block_mat_square[OF sq,unfolded square_mat.simps]
      unfolding diag_block_mat_dim by auto
            
    have [simp]: "diag_block_mat As \<in> carrier\<^sub>m n2 n2" unfolding mat_carrier_def by simp
    have [simp]: "?An As \<in> carrier\<^sub>m n2 n2" unfolding mat_carrier_def by simp
    show ?case unfolding diag_block_mat.simps Let_def list.simps
      by (subst four_block_mat_mult[of _ n1 n1 _ n2 _ n2 _ _ n1 _ n2],
      insert A, auto simp: IH)
  qed auto
  finally show ?case by simp
qed

lemma diag_block_upper_triangular: assumes 
    "\<And> A i j. A \<in> set As \<Longrightarrow> j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0"
  and "Ball (set As) square_mat"
  and "j < i" "i < dim\<^sub>r (diag_block_mat As)"
  shows "diag_block_mat As $$ (i,j) = 0"
  using assms
proof (induct As arbitrary: i j)
  case (Cons A As i j)
  let ?n1 = "dim\<^sub>r A"
  let ?n2 = "listsum (map dim\<^sub>r As)"
  from Cons have [simp]: "dim\<^sub>c A = ?n1" by simp
  from Cons have "Ball (set As) square_mat" by auto
  note [simp] = diag_block_mat_square[OF this,unfolded square_mat.simps]
  note [simp] = diag_block_mat_dim(1)
  from Cons(5) have i: "i < ?n1 + ?n2" by simp
  show ?case 
  proof (cases "i < ?n1")
    case True
    with Cons(4) have j: "j < ?n1" by auto
    with True Cons(2)[of A, OF _ Cons(4)] show ?thesis
      by (simp add: Let_def)
  next
    case False note iAs = this
    show ?thesis
    proof (cases "j < ?n1")
      case True
      with i iAs show ?thesis by (simp add: Let_def)
    next
      case False note jAs = this
      from Cons(4) i have j: "j < ?n1 + ?n2" by auto
      show ?thesis using iAs jAs i j
        by (simp add: Let_def, subst Cons(1), insert Cons(2-4), auto)
    qed
  qed
qed simp

lemma four_block_scalar: assumes c: "A \<in> carrier\<^sub>m nr1 nc1" "B \<in> carrier\<^sub>m nr1 nc2"
  "C \<in> carrier\<^sub>m nr2 nc1" "D \<in> carrier\<^sub>m nr2 nc2"
  shows "a \<odot>\<^sub>m four_block_mat A B C D = four_block_mat (a \<odot>\<^sub>m A) (a \<odot>\<^sub>m B) (a \<odot>\<^sub>m C) (a \<odot>\<^sub>m D)"
  by (rule mat_eqI, insert c, auto)

lemma four_block_map: assumes c: "A \<in> carrier\<^sub>m nr1 nc1" "B \<in> carrier\<^sub>m nr1 nc2"
  "C \<in> carrier\<^sub>m nr2 nc1" "D \<in> carrier\<^sub>m nr2 nc2"
  shows "map\<^sub>m f (four_block_mat A B C D) = four_block_mat (map\<^sub>m f A) (map\<^sub>m f B) (map\<^sub>m f C) (map\<^sub>m f D)"
  by (rule mat_eqI, insert c, auto)

lemma four_block_mat_add: assumes 
  c1: "A1 \<in> carrier\<^sub>m nr1 nc1" "B1 \<in> carrier\<^sub>m nr1 nc2" "C1 \<in> carrier\<^sub>m nr2 nc1" "D1 \<in> carrier\<^sub>m nr2 nc2" and
  c2: "A2 \<in> carrier\<^sub>m nr1 nc1" "B2 \<in> carrier\<^sub>m nr1 nc2" "C2 \<in> carrier\<^sub>m nr2 nc1" "D2 \<in> carrier\<^sub>m nr2 nc2"
  shows "four_block_mat A1 B1 C1 D1 \<oplus>\<^sub>m four_block_mat A2 B2 C2 D2
  = four_block_mat (A1 \<oplus>\<^sub>m A2) (B1 \<oplus>\<^sub>m B2) (C1 \<oplus>\<^sub>m C2) (D1 \<oplus>\<^sub>m D2)"
  by (rule mat_eqI, insert assms, auto)


lemma four_block_diag: assumes c: "A \<in> carrier\<^sub>m n1 n1" 
   "D \<in> carrier\<^sub>m n2 n2"
  shows "mat_diag (four_block_mat A B C D) = mat_diag A @ mat_diag D"
  by (rule nth_equalityI, insert c, auto simp: mat_diag_def nth_append)

definition mk_diagonal :: "'a::zero list \<Rightarrow> 'a mat"
  where "mk_diagonal as = diag_block_mat (map (\<lambda>a. mat (Suc 0) (Suc 0) (\<lambda>_. a)) as)"

lemma mk_diagonal_dim:
  "dim\<^sub>r (mk_diagonal as) = length as" "dim\<^sub>c (mk_diagonal as) = length as"
  unfolding mk_diagonal_def by(induct as, auto simp: Let_def)

lemma mk_diagonal_diagonal: "diagonal_mat (mk_diagonal as)"
  unfolding mk_diagonal_def
proof (induct as)
  case Nil show ?case unfolding mk_diagonal_def diagonal_mat_def by simp next
  case (Cons a as)
    let ?n = "length (a#as)"
    let ?A = "mat (Suc 0) (Suc 0) (\<lambda>_. a)"
    let ?f = "map (\<lambda>a. mat (Suc 0) (Suc 0) (\<lambda>_. a))"
    let ?AS = "diag_block_mat (?f as)"
    let ?AAS = "diag_block_mat (?f (a#as))"
    show ?case
      unfolding diagonal_mat_def
    proof(intro allI impI)
      fix i j assume ir: "i < dim\<^sub>r ?AAS" and jc: "j < dim\<^sub>c ?AAS" and ij: "i \<noteq> j"
      hence ir2: "i < 1 + dim\<^sub>r ?AS" and jc2: "j < 1 + dim\<^sub>c ?AS"
        unfolding mat_dim_row_mat list.map diag_block_mat.simps Let_def
        by auto
      show "?AAS $$ (i,j) = 0"
      proof (cases "i = 0")
        case True
          then show ?thesis using jc ij by (auto simp: Let_def) next
        case False note i0 = this
          show ?thesis
          proof (cases "j = 0")
            case True
              then show ?thesis using ir ij by (auto simp: Let_def) next
            case False
              have ir3: "i-1 < dim\<^sub>r ?AS" and jc3: "j-1 < dim\<^sub>c ?AS"
                using ir2 jc2 i0 False by auto
              have IH: "\<And>i j. i < dim\<^sub>r ?AS \<Longrightarrow> j < dim\<^sub>c ?AS \<Longrightarrow> i \<noteq> j \<Longrightarrow>
                ?AS $$ (i,j) = 0"
                using Cons unfolding diagonal_mat_def by auto
              have "?AS $$ (i-1,j-1) = 0"
                using IH[OF ir3 jc3] i0 False ij by auto
              thus ?thesis using ir jc ij by (simp add: Let_def)
          qed
      qed
    qed
qed

definition orthogonal_mat :: "'a::semiring_0 mat \<Rightarrow> bool"
  where "orthogonal_mat A \<equiv>
    let B = mat_transpose A \<otimes>\<^sub>m A in
    diagonal_mat B \<and> (\<forall>i<dim\<^sub>c A. B $$ (i,i) \<noteq> 0)"

lemma orthogonal_matD[elim]:
  "orthogonal_mat A \<Longrightarrow>
   i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> (col A i \<bullet> col A j = 0) = (i \<noteq> j)"
  unfolding orthogonal_mat_def diagonal_mat_def by auto

lemma orthogonal_matI[intro]:
  "(\<And>i j. i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> (col A i \<bullet> col A j = 0) = (i \<noteq> j)) \<Longrightarrow>
   orthogonal_mat A"
  unfolding orthogonal_mat_def diagonal_mat_def by auto

definition orthogonal :: "'a::semiring_0 vec list \<Rightarrow> bool"
  where "orthogonal vs \<equiv>
    \<forall>i j. i < length vs \<longrightarrow> j < length vs \<longrightarrow>
      (vs ! i \<bullet> vs ! j = 0) = (i \<noteq> j)"

lemma orthogonalD[elim]:
  "orthogonal vs \<Longrightarrow> i < length vs \<Longrightarrow> j < length vs \<Longrightarrow>
  (nth vs i \<bullet> nth vs j = 0) = (i \<noteq> j)"
  unfolding orthogonal_def by auto

lemma orthogonalI[intro]:
  "(\<And>i j. i < length vs \<Longrightarrow> j < length vs \<Longrightarrow> (nth vs i \<bullet> nth vs j = 0) = (i \<noteq> j)) \<Longrightarrow>
   orthogonal vs"
  unfolding orthogonal_def by auto


(* THIS LINE SEPARATES AFP-ENTRY FROM NEWER DEVELOPMENTS *)

lemma four_block_mat_transpose: assumes *: "A \<in> carrier\<^sub>m nr1 nc1" "B \<in> carrier\<^sub>m nr1 nc2"
  "C \<in> carrier\<^sub>m nr2 nc1" "D \<in> carrier\<^sub>m nr2 nc2"
  shows "mat_transpose (four_block_mat A B C D) = 
    four_block_mat (mat_transpose A) (mat_transpose C) (mat_transpose B) (mat_transpose D)"
  by (rule mat_eqI, insert *, auto)

lemma zero_mat_transpose[simp]: "mat_transpose (\<zero>\<^sub>m n m) = (\<zero>\<^sub>m m n)"
  by (rule mat_eqI, auto)

lemma col_mat_mult2[simp]:
  assumes A: "A : carrier\<^sub>m nr n"
      and B: "B : carrier\<^sub>m n nc"
      and j: "j < nc"
  shows "col (A \<otimes>\<^sub>m B) j = A \<otimes>\<^sub>m\<^sub>v col B j"
proof
  have AB: "A \<otimes>\<^sub>m B : carrier\<^sub>m nr nc" using A B by auto
  fix i assume i: "i < dim\<^sub>v (A \<otimes>\<^sub>m\<^sub>v col B j)"
  show "col (A \<otimes>\<^sub>m B) j $ i = (A \<otimes>\<^sub>m\<^sub>v col B j) $ i"
    using A B AB j i by simp
qed auto

lemma upper_triangular_four_block: assumes AD: "A \<in> carrier\<^sub>m n n" "D \<in> carrier\<^sub>m m m"
  and ut: "upper_triangular A" "upper_triangular D"
  shows "upper_triangular (four_block_mat A B (\<zero>\<^sub>m m n) D)"
proof -
  let ?C = "four_block_mat A B (\<zero>\<^sub>m m n) D"
  from AD have dim: "dim\<^sub>r ?C = n + m" "dim\<^sub>c ?C = n + m" "dim\<^sub>r A = n" by auto
  show ?thesis
  proof (rule upper_triangularI, unfold dim)
    fix i j
    assume *: "j < i" "i < n + m"
    show "?C $$ (i,j) = 0"
    proof (cases "i < n")
      case True
      with upper_triangularD[OF ut(1) *(1)] * AD show ?thesis by auto
    next
      case False note i = this
      show ?thesis by (cases "j < n", insert upper_triangularD[OF ut(2)] * i AD, auto)
    qed
  qed
qed

lemma four_block_mat_pow: assumes A: "A \<in> carrier\<^sub>m n n"
  and B: "B \<in> carrier\<^sub>m m m"
  shows "(four_block_mat A (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) B) ^\<^sub>m k = 
    four_block_mat (A ^\<^sub>m k) (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) (B ^\<^sub>m k)"
proof (induct k)
  case (Suc k)
  let ?FB = "\<lambda> A B. four_block_mat A (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) B"
  let ?A = "?FB A B"
  let ?B = "?FB (A ^\<^sub>m k) (B ^\<^sub>m k)" 
  from A B have Ak: "A ^\<^sub>m k \<in> carrier\<^sub>m n n" and Bk: "B ^\<^sub>m k \<in> carrier\<^sub>m m m" by auto
  have "?A ^\<^sub>m Suc k = ?A ^\<^sub>m k \<otimes>\<^sub>m ?A" by simp
  also have "?A ^\<^sub>m k = ?B " by (rule Suc)
  also have "?B \<otimes>\<^sub>m ?A = ?FB (A ^\<^sub>m Suc k) (B ^\<^sub>m Suc k)"
    by (subst four_block_mat_mult[OF Ak _ _ Bk A _ _ B], insert A B, auto)
  finally show ?case .
qed (insert A B, auto)

lemma vec_uminus_sprod:
  assumes [simp]: "v : carrier\<^sub>v n" "w : carrier\<^sub>v n"
  shows "- ((v::'a::field vec) \<bullet> w) = (\<ominus>\<^sub>v v) \<bullet> w"
  unfolding scalar_prod_def vec_uminus_def
  apply (subst setsum_negf[symmetric])
proof (rule setsum.cong[OF refl])
  fix i assume i: "i : {0 ..<dim\<^sub>v w}"
  have [simp]: "dim\<^sub>v v = n" "dim\<^sub>v w = n" by auto
  show "- (v $ i * w $ i) = vec (dim\<^sub>v v) (\<lambda>i. - v $ i) $ i * w $ i"
    unfolding minus_mult_left using i by auto
qed


lemma vec_append_eq:
  assumes [simp]: "v : carrier\<^sub>v n" "v' : carrier\<^sub>v n"
  shows [simp]: "v @\<^sub>v w = v' @\<^sub>v w' \<longleftrightarrow> v = v' \<and> w = w'" (is "?L \<longleftrightarrow> ?R")
proof
  have [simp]: "dim\<^sub>v v = n" "dim\<^sub>v v' = n" by auto
  { assume L: ?L
    have vv': "v = v'"
    proof
      fix i assume i: "i < dim\<^sub>v v'"
      have "(v @\<^sub>v w) $ i = (v' @\<^sub>v w') $ i" using L by auto
      thus "v $ i = v' $ i" using i by auto
    qed auto 
    moreover have "w = w'"
    proof
      show "dim\<^sub>v w = dim\<^sub>v w'" using vv' L
        by (metis add_diff_cancel_left' vec_append_index(2))
      moreover fix i assume i: "i < dim\<^sub>v w'"
      have "(v @\<^sub>v w) $ (n + i) = (v' @\<^sub>v w') $ (n + i)" using L by auto
      ultimately show "w $ i = w' $ i" using i by simp
    qed
    ultimately show ?R by simp
  }
qed auto

lemma vec_append_add:
  assumes [simp]: "v : carrier\<^sub>v n" "v' : carrier\<^sub>v n"
      and [simp]: "w : carrier\<^sub>v m" "w' : carrier\<^sub>v m"
  shows "(v @\<^sub>v w) \<oplus>\<^sub>v (v' @\<^sub>v w') = (v \<oplus>\<^sub>v v') @\<^sub>v (w \<oplus>\<^sub>v w')" (is "?L = ?R")
proof
  have [simp]: "dim\<^sub>v v = n" "dim\<^sub>v v' = n" by auto
  have [simp]: "dim\<^sub>v w = m" "dim\<^sub>v w' = m" by auto
  fix i assume i: "i < dim\<^sub>v ?R"
  thus "?L $ i = ?R $ i" by (cases "i < n",auto)
qed auto


lemma mat_mult_vec_split:
  assumes A: "A : carrier\<^sub>m n n"
      and D: "D : carrier\<^sub>m m m"
      and a: "a : carrier\<^sub>v n"
      and d: "d : carrier\<^sub>v m"
  shows "four_block_mat A (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) D \<otimes>\<^sub>m\<^sub>v (a @\<^sub>v d) = A \<otimes>\<^sub>m\<^sub>v a @\<^sub>v D \<otimes>\<^sub>m\<^sub>v d"
    (is "?A00D \<otimes>\<^sub>m\<^sub>v _ = ?r")
proof
  have A00D: "?A00D : carrier\<^sub>m (n+m) (n+m)" using four_block_mat_carrier[OF A D].
  fix i assume i: "i < dim\<^sub>v ?r"
  show "(?A00D \<otimes>\<^sub>m\<^sub>v (a @\<^sub>v d)) $ i = ?r $ i" (is "?li = _")
  proof (cases "i < n")
    case True
      have "?li = (row A i @\<^sub>v \<zero>\<^sub>v m) \<bullet> (a @\<^sub>v d)"
        using A row_four_block_mat[OF A _ _ D] True by simp
      also have "... = row A i \<bullet> a + \<zero>\<^sub>v m \<bullet> d"
        apply (rule scalar_prod_append) using A D a d True by auto
      also have "... = row A i \<bullet> a" using d by simp
      finally show ?thesis using A True by auto
    next case False
      let ?i = "i - n"
      have "?li = (\<zero>\<^sub>v n @\<^sub>v row D ?i) \<bullet> (a @\<^sub>v d)"
        using i row_four_block_mat[OF A _ _ D] False A D by simp
      also have "... = \<zero>\<^sub>v n \<bullet> a + row D ?i \<bullet> d"
        apply (rule scalar_prod_append) using A D a d False by auto
      also have "... = row D ?i \<bullet> d" using a by simp
      finally show ?thesis using A D False i by auto
  qed
qed auto

lemma mat_similar_witI: assumes "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" 
  "A \<in> carrier\<^sub>m n n" "B \<in> carrier\<^sub>m n n" "P \<in> carrier\<^sub>m n n" "Q \<in> carrier\<^sub>m n n" 
  shows "mat_similar_wit A B P Q" using assms unfolding mat_similar_wit_def Let_def by auto

lemma mat_similar_witD: assumes "n = dim\<^sub>r A" "mat_similar_wit A B P Q"
  shows "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" 
  "A \<in> carrier\<^sub>m n n" "B \<in> carrier\<^sub>m n n" "P \<in> carrier\<^sub>m n n" "Q \<in> carrier\<^sub>m n n" 
  using assms(2) unfolding mat_similar_wit_def Let_def assms(1)[symmetric] by auto

lemma mat_similar_witD2: assumes "A \<in> carrier\<^sub>m n m" "mat_similar_wit A B P Q"
  shows "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" 
  "A \<in> carrier\<^sub>m n n" "B \<in> carrier\<^sub>m n n" "P \<in> carrier\<^sub>m n n" "Q \<in> carrier\<^sub>m n n" 
  using mat_similar_witD[OF _ assms(2), of n] assms(1)[unfolded mat_carrier_def] by auto

lemma mat_similar_wit_sym: assumes sim: "mat_similar_wit A B P Q"
  shows "mat_similar_wit B A Q P"
proof -
  from mat_similar_witD[OF refl sim] obtain n where 
    AB: "{A, B, P, Q} \<subseteq> carrier\<^sub>m n n" "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" and A: "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" by blast
  hence *: "{B, A, Q, P} \<subseteq> carrier\<^sub>m n n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" by auto
  let ?c = "\<lambda> A. A \<in> carrier\<^sub>m n n"
  from * have Carr: "?c B" "?c P" "?c Q" by auto
  note [simp] = mat_mult_assoc[of _ n n _ n _ n]
  show ?thesis
  proof (rule mat_similar_witI[of _ _ n])
    have "Q \<otimes>\<^sub>m A \<otimes>\<^sub>m P = (Q \<otimes>\<^sub>m P) \<otimes>\<^sub>m B \<otimes>\<^sub>m (Q \<otimes>\<^sub>m P)"
      using Carr unfolding A by simp
    also have "\<dots> = B" using Carr unfolding AB by simp
    finally show "B = Q \<otimes>\<^sub>m A \<otimes>\<^sub>m P" by simp
  qed (insert * AB, auto)
qed

lemma mat_similar_wit_refl: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "mat_similar_wit A A (\<one>\<^sub>m n) (\<one>\<^sub>m n)"
  by (rule mat_similar_witI[OF _ _ _ A], insert A, auto)

lemma mat_similar_wit_trans: assumes AB: "mat_similar_wit A B P Q"
  and BC: "mat_similar_wit B C P' Q'"
  shows "mat_similar_wit A C (P \<otimes>\<^sub>m P') (Q' \<otimes>\<^sub>m Q)"
proof -
  from mat_similar_witD[OF refl AB] obtain n where
    AB: "{A, B, P, Q} \<subseteq> carrier\<^sub>m n n" "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" by blast
  hence B: "B \<in> carrier\<^sub>m n n" by auto
  from mat_similar_witD2[OF B BC] have
    BC: "{C, P', Q'} \<subseteq> carrier\<^sub>m n n" "P' \<otimes>\<^sub>m Q' = \<one>\<^sub>m n" "Q' \<otimes>\<^sub>m P' = \<one>\<^sub>m n" "B = P' \<otimes>\<^sub>m C \<otimes>\<^sub>m Q'" by auto
  let ?c = "\<lambda> A. A \<in> carrier\<^sub>m n n"
  let ?P = "P \<otimes>\<^sub>m P'"
  let ?Q = "Q' \<otimes>\<^sub>m Q"
  from AB BC have carr: "?c A" "?c B" "?c C" "?c P" "?c P'" "?c Q" "?c Q'" 
    and Carr: "{A, C, ?P, ?Q} \<subseteq> carrier\<^sub>m n n" by auto
  note [simp] = mat_mult_assoc[of _ n n _ n _ n]
  have id: "A = ?P \<otimes>\<^sub>m C \<otimes>\<^sub>m ?Q" unfolding AB(4)[unfolded BC(4)] using carr 
    by simp
  have "?P \<otimes>\<^sub>m ?Q = P \<otimes>\<^sub>m (P' \<otimes>\<^sub>m Q') \<otimes>\<^sub>m Q" using carr by simp
  also have "\<dots> = \<one>\<^sub>m n" unfolding BC using carr AB by simp
  finally have PQ: "?P \<otimes>\<^sub>m ?Q = \<one>\<^sub>m n" .
  have "?Q \<otimes>\<^sub>m ?P = Q' \<otimes>\<^sub>m (Q \<otimes>\<^sub>m P) \<otimes>\<^sub>m P'" using carr by simp
  also have "\<dots> = \<one>\<^sub>m n" unfolding AB using carr BC by simp
  finally have QP: "?Q \<otimes>\<^sub>m ?P = \<one>\<^sub>m n" .
  show ?thesis
    by (rule mat_similar_witI[OF PQ QP id], insert Carr, auto)
qed

lemma mat_similar_refl: "A \<in> carrier\<^sub>m n n \<Longrightarrow> mat_similar A A"
  using mat_similar_wit_refl unfolding mat_similar_def by blast

lemma mat_similar_trans: "mat_similar A B \<Longrightarrow> mat_similar B C \<Longrightarrow> mat_similar A C"
  using mat_similar_wit_trans unfolding mat_similar_def by blast

lemma mat_similar_sym: "mat_similar A B \<Longrightarrow> mat_similar B A"
  using mat_similar_wit_sym unfolding mat_similar_def by blast

lemma mat_similar_wit_four_block: assumes 
      1: "mat_similar_wit A1 B1 P1 Q1"
  and 2: "mat_similar_wit A2 B2 P2 Q2"
  and URA: "URA = (P1 \<otimes>\<^sub>m UR \<otimes>\<^sub>m Q2)"
  and LLA: "LLA = (P2 \<otimes>\<^sub>m LL \<otimes>\<^sub>m Q1)"
  and A1: "A1 \<in> carrier\<^sub>m n n"
  and A2: "A2 \<in> carrier\<^sub>m m m"
  and LL: "LL \<in> carrier\<^sub>m m n"
  and UR: "UR \<in> carrier\<^sub>m n m"
  shows "mat_similar_wit (four_block_mat A1 URA LLA A2) (four_block_mat B1 UR LL B2)
    (four_block_mat P1 (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) P2) (four_block_mat Q1 (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) Q2)"
  (is "mat_similar_wit ?A ?B ?P ?Q")
proof -
  let ?n = "n + m"
  let ?O1 = "\<one>\<^sub>m n"   let ?O2 = "\<one>\<^sub>m m"   let ?O = "\<one>\<^sub>m ?n"
  from mat_similar_witD2[OF A1 1] have 11: "P1 \<otimes>\<^sub>m Q1 = ?O1" "Q1 \<otimes>\<^sub>m P1 = ?O1" 
    and P1: "P1 \<in> carrier\<^sub>m n n" and Q1: "Q1 \<in> carrier\<^sub>m n n" 
    and B1: "B1 \<in> carrier\<^sub>m n n" and 1: "A1 = P1 \<otimes>\<^sub>m B1 \<otimes>\<^sub>m Q1" by auto
  from mat_similar_witD2[OF A2 2] have 21: "P2 \<otimes>\<^sub>m Q2 = ?O2" "Q2 \<otimes>\<^sub>m P2 = ?O2" 
    and P2: "P2 \<in> carrier\<^sub>m m m" and Q2: "Q2 \<in> carrier\<^sub>m m m" 
    and B2: "B2 \<in> carrier\<^sub>m m m" and 2: "A2 = P2 \<otimes>\<^sub>m B2 \<otimes>\<^sub>m Q2" by auto
  have PQ1: "?P \<otimes>\<^sub>m ?Q = ?O"
    by (subst four_block_mat_mult[OF P1 _ _ P2 Q1 _ _ Q2], unfold 11 21, insert P1 P2 Q1 Q2,
      auto intro!: mat_eqI)
  have QP1: "?Q \<otimes>\<^sub>m ?P = ?O"
    by (subst four_block_mat_mult[OF Q1 _ _ Q2 P1 _ _ P2], unfold 11 21, insert P1 P2 Q1 Q2,
      auto intro!: mat_eqI)
  let ?PB = "?P \<otimes>\<^sub>m ?B"
  have P: "?P \<in> carrier\<^sub>m ?n ?n" using P1 P2 by auto
  have Q: "?Q \<in> carrier\<^sub>m ?n ?n" using Q1 Q2 by auto
  have B: "?B \<in> carrier\<^sub>m ?n ?n" using B1 UR LL B2 by auto
  have PB: "?PB \<in> carrier\<^sub>m ?n ?n" using P B by auto
  have PB1: "P1 \<otimes>\<^sub>m B1 \<in> carrier\<^sub>m n n" using P1 B1 by auto
  have PB2: "P2 \<otimes>\<^sub>m B2 \<in> carrier\<^sub>m m m" using P2 B2 by auto
  have P1UR: "P1 \<otimes>\<^sub>m UR \<in> carrier\<^sub>m n m" using P1 UR by auto
  have P2LL: "P2 \<otimes>\<^sub>m LL \<in> carrier\<^sub>m m n" using P2 LL by auto
  have id: "?PB = four_block_mat (P1 \<otimes>\<^sub>m B1) (P1 \<otimes>\<^sub>m UR) (P2 \<otimes>\<^sub>m LL) (P2 \<otimes>\<^sub>m B2)"
    by (subst four_block_mat_mult[OF P1 _ _ P2 B1 UR LL B2], insert P1 P2 B1 B2 LL UR, auto)
  have id: "?PB \<otimes>\<^sub>m ?Q = four_block_mat (P1 \<otimes>\<^sub>m B1 \<otimes>\<^sub>m Q1) (P1 \<otimes>\<^sub>m UR \<otimes>\<^sub>m Q2) 
    (P2 \<otimes>\<^sub>m LL \<otimes>\<^sub>m Q1) (P2 \<otimes>\<^sub>m B2 \<otimes>\<^sub>m Q2)" unfolding id
    by (subst four_block_mat_mult[OF PB1 P1UR P2LL PB2 Q1 _ _ Q2], 
    insert P1 P2 B1 B2 Q1 Q2 UR LL, auto)
  have id: "?A = ?P \<otimes>\<^sub>m ?B \<otimes>\<^sub>m ?Q" unfolding id 1 2 URA LLA ..
  show ?thesis
    by (rule mat_similar_witI[OF PQ1 QP1 id], insert A1 A2 B1 B2 Q1 Q2 P1 P2, auto)
qed


lemma mat_similar_four_block_0_ex: assumes 
      1: "mat_similar A1 B1"
  and 2: "mat_similar A2 B2"
  and A0: "A0 \<in> carrier\<^sub>m n m"
  and A1: "A1 \<in> carrier\<^sub>m n n"
  and A2: "A2 \<in> carrier\<^sub>m m m"
  shows "\<exists> B0. B0 \<in> carrier\<^sub>m n m \<and> mat_similar (four_block_mat A1 A0 (\<zero>\<^sub>m m n) A2) 
    (four_block_mat B1 B0 (\<zero>\<^sub>m m n) B2)"
proof -
  from 1[unfolded mat_similar_def] obtain P1 Q1 where 1: "mat_similar_wit A1 B1 P1 Q1" by auto
  note w1 = mat_similar_witD2[OF A1 1]
  from 2[unfolded mat_similar_def] obtain P2 Q2 where 2: "mat_similar_wit A2 B2 P2 Q2" by auto
  note w2 = mat_similar_witD2[OF A2 2]
  from w1 w2 have C: "B1 \<in> carrier\<^sub>m n n" "B2 \<in> carrier\<^sub>m m m" by auto
  from w1 w2 have id: "\<zero>\<^sub>m m n = Q2 \<otimes>\<^sub>m \<zero>\<^sub>m m n \<otimes>\<^sub>m P1" by simp
  let ?wit = "Q1 \<otimes>\<^sub>m A0 \<otimes>\<^sub>m P2"
  from w1 w2 A0 have wit: "?wit \<in> carrier\<^sub>m n m" by auto
  from mat_similar_wit_sym[OF mat_similar_wit_four_block[OF mat_similar_wit_sym[OF 1] mat_similar_wit_sym[OF 2] 
    refl id C mat_zero_closed A0]]
  have "mat_similar (four_block_mat A1 A0 (\<zero>\<^sub>m m n) A2) (four_block_mat B1 (Q1 \<otimes>\<^sub>m A0 \<otimes>\<^sub>m P2) (\<zero>\<^sub>m m n) B2)"
    unfolding mat_similar_def by auto
  thus ?thesis using wit by auto
qed

lemma mat_similar_four_block_0_0: assumes 
      1: "mat_similar A1 B1"
  and 2: "mat_similar A2 B2"
  and A1: "A1 \<in> carrier\<^sub>m n n"
  and A2: "A2 \<in> carrier\<^sub>m m m"
  shows "mat_similar (four_block_mat A1 (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) A2) 
    (four_block_mat B1 (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) B2)"
proof -
  from 1[unfolded mat_similar_def] obtain P1 Q1 where 1: "mat_similar_wit A1 B1 P1 Q1" by auto
  note w1 = mat_similar_witD2[OF A1 1]
  from 2[unfolded mat_similar_def] obtain P2 Q2 where 2: "mat_similar_wit A2 B2 P2 Q2" by auto
  note w2 = mat_similar_witD2[OF A2 2]
  from w1 w2 have C: "B1 \<in> carrier\<^sub>m n n" "B2 \<in> carrier\<^sub>m m m" by auto
  from w1 w2 have id: "\<zero>\<^sub>m m n = Q2 \<otimes>\<^sub>m \<zero>\<^sub>m m n \<otimes>\<^sub>m P1" by simp
  from w1 w2 have id2: "\<zero>\<^sub>m n m = Q1 \<otimes>\<^sub>m \<zero>\<^sub>m n m \<otimes>\<^sub>m P2" by simp
  from mat_similar_wit_sym[OF mat_similar_wit_four_block[OF mat_similar_wit_sym[OF 1] mat_similar_wit_sym[OF 2] 
    id2 id C mat_zero_closed mat_zero_closed]]
  show ?thesis unfolding mat_similar_def by blast
qed

lemma mat_similar_diag_block_mat: assumes "\<And> A B. (A,B) \<in> set Ms \<Longrightarrow> mat_similar A B"
  shows "mat_similar (diag_block_mat (map fst Ms)) (diag_block_mat (map snd Ms))"
  using assms
proof (induct Ms)
  case Nil
  show ?case by (auto intro!: mat_similar_refl[of _ 0])
next
  case (Cons AB Ms)
  obtain A B where AB: "AB = (A,B)" by force
  from Cons(2)[of A B] have simAB: "mat_similar A B" unfolding AB by auto
  from mat_similarD[OF this] obtain n where A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n n" by auto
  hence [simp]: "dim\<^sub>r A = n" "dim\<^sub>c A = n" "dim\<^sub>r B = n" "dim\<^sub>c B = n" by auto
  let ?C = "diag_block_mat (map fst Ms)" let ?D = "diag_block_mat (map snd Ms)"
  from Cons(1)[OF Cons(2)] have simRec: "mat_similar ?C ?D" by auto
  from mat_similarD[OF this] obtain m where C: "?C \<in> carrier\<^sub>m m m" and D: "?D \<in> carrier\<^sub>m m m" by auto
  hence [simp]: "dim\<^sub>r ?C = m" "dim\<^sub>c ?C = m" "dim\<^sub>r ?D = m" "dim\<^sub>c ?D = m" by auto
  have "mat_similar (diag_block_mat (map fst (AB # Ms))) (diag_block_mat (map snd (AB # Ms)))
    = mat_similar (four_block_mat A (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) ?C) (four_block_mat B (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) ?D)" 
    unfolding AB by (simp add: Let_def)
  also have "\<dots>"
    by (rule mat_similar_four_block_0_0[OF simAB simRec A C])
  finally show ?case .
qed

lemma mat_similar_wit_pow: assumes wit: "mat_similar_wit A B P Q"
  shows "mat_similar_wit (A ^\<^sub>m k) (B ^\<^sub>m k) P Q"
proof -
  def n \<equiv> "dim\<^sub>r A"
  let ?C = "carrier\<^sub>m n n"
  from mat_similar_witD[OF refl wit, folded n_def] have
    A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C"
    and PQ: "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" and QP: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n"
    and AB: "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q"
    by auto
  from A B have *: "(A ^\<^sub>m k) \<in> carrier\<^sub>m n n" "B ^\<^sub>m k \<in> carrier\<^sub>m n n" by auto
  note carr = A B P Q
  have id: "A ^\<^sub>m k = P \<otimes>\<^sub>m B ^\<^sub>m k \<otimes>\<^sub>m Q" unfolding AB
  proof (induct k)
    case 0
    thus ?case using carr by (simp add: PQ)
  next
    case (Suc k)
    def Bk \<equiv> "B ^\<^sub>m k"
    have Bk: "Bk \<in> carrier\<^sub>m n n" unfolding Bk_def using carr by simp
    have "(P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q) ^\<^sub>m Suc k = (P \<otimes>\<^sub>m Bk \<otimes>\<^sub>m Q) \<otimes>\<^sub>m (P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q)" by (simp add: Suc Bk_def)
    also have "\<dots> = P \<otimes>\<^sub>m (Bk \<otimes>\<^sub>m (Q \<otimes>\<^sub>m P) \<otimes>\<^sub>m B) \<otimes>\<^sub>m Q"
      using carr Bk by (simp add: mat_mult_assoc[of _ n n _ n _ n])
    also have "Bk \<otimes>\<^sub>m (Q \<otimes>\<^sub>m P) = Bk" unfolding QP using Bk by simp
    finally show ?case unfolding Bk_def by simp
  qed
  show ?thesis
    by (rule mat_similar_witI[OF PQ QP id * P Q])
qed  

lemma mat_similar_wit_pow_id: "mat_similar_wit A B P Q \<Longrightarrow> A ^\<^sub>m k = P \<otimes>\<^sub>m B ^\<^sub>m k \<otimes>\<^sub>m Q"
  using mat_similar_wit_pow[of A B P Q k] unfolding mat_similar_wit_def Let_def by blast

subsection\<open>Homomorphism properties\<close>

context semiring_hom
begin
abbreviation mat_hom :: "'a mat \<Rightarrow> 'b mat" ("mat\<^sub>h")
  where "mat\<^sub>h \<equiv> map\<^sub>m hom"

abbreviation vec_hom :: "'a vec \<Rightarrow> 'b vec" ("vec\<^sub>h")
  where "vec\<^sub>h \<equiv> map\<^sub>v hom"

lemma vec_hom_zero: "vec\<^sub>h (\<zero>\<^sub>v n) = \<zero>\<^sub>v n"
  by (rule vec_eqI, auto)

lemma mat_hom_one: "mat\<^sub>h (\<one>\<^sub>m n) = \<one>\<^sub>m n"
  by (rule mat_eqI, auto)

lemma mat_hom_mult: assumes A: "A \<in> carrier\<^sub>m nr n" and B: "B \<in> carrier\<^sub>m n nc"
  shows "mat\<^sub>h (A \<otimes>\<^sub>m B) = mat\<^sub>h A \<otimes>\<^sub>m mat\<^sub>h B"
proof -
  let ?L = "mat\<^sub>h (A \<otimes>\<^sub>m B)"
  let ?R = "mat\<^sub>h A \<otimes>\<^sub>m mat\<^sub>h B"
  let ?A = "mat\<^sub>h A" 
  let ?B = "mat\<^sub>h B" 
  from A B have id: 
    "dim\<^sub>r ?L = nr" "dim\<^sub>r ?R = nr" 
    "dim\<^sub>c ?L = nc" "dim\<^sub>c ?R = nc"  by auto
  show ?thesis
  proof (rule mat_eqI, unfold id)
    fix i j
    assume *: "i < nr" "j < nc"
    def I \<equiv> "{0 ..< n}"
    have id: "{0 ..< dim\<^sub>v (col ?B j)} = I" "{0 ..< dim\<^sub>v (col B j)} = I" 
      unfolding I_def using * B by auto
    have finite: "finite I" unfolding I_def by auto
    have I: "I \<subseteq> {0 ..< n}" unfolding I_def by auto
    have "?L $$ (i,j) = hom (row A i \<bullet> col B j)" using A B * by auto
    also have "\<dots> = row ?A i \<bullet> col ?B j" unfolding scalar_prod_def id using finite I
    proof (induct I)
      case (insert k I)
      show ?case unfolding setsum.insert[OF insert(1-2)] hom_add hom_mult
        using insert(3-) * A B by auto
    qed simp
    also have "\<dots> = ?R $$ (i,j)" using A B * by auto
    finally
    show "?L $$ (i, j) = ?R $$ (i, j)" .
  qed auto
qed

lemma mat_vec_mult_hom: assumes A: "A \<in> carrier\<^sub>m nr n" and v: "v \<in> carrier\<^sub>v n"
  shows "vec\<^sub>h (A \<otimes>\<^sub>m\<^sub>v v) = mat\<^sub>h A \<otimes>\<^sub>m\<^sub>v vec\<^sub>h v"
proof -
  let ?L = "vec\<^sub>h (A \<otimes>\<^sub>m\<^sub>v v)"
  let ?R = "mat\<^sub>h A \<otimes>\<^sub>m\<^sub>v vec\<^sub>h v"
  let ?A = "mat\<^sub>h A" 
  let ?v = "vec\<^sub>h v" 
  from A v have id: 
    "dim\<^sub>v ?L = nr" "dim\<^sub>v ?R = nr" 
    by auto
  show ?thesis
  proof (rule vec_eqI, unfold id)
    fix i 
    assume *: "i < nr" 
    def I \<equiv> "{0 ..< n}"
    have id: "{0 ..< dim\<^sub>v v} = I" "{0 ..< dim\<^sub>v (vec\<^sub>h v)} = I" 
      unfolding I_def using * v  by auto
    have finite: "finite I" unfolding I_def by auto
    have I: "I \<subseteq> {0 ..< n}" unfolding I_def by auto
    have "?L $ i = hom (row A i \<bullet> v)" using A v * by auto
    also have "\<dots> = row ?A i \<bullet> ?v" unfolding scalar_prod_def id using finite I
    proof (induct I)
      case (insert k I)
      show ?case unfolding setsum.insert[OF insert(1-2)] hom_add hom_mult
        using insert(3-) * A v by auto
    qed simp
    also have "\<dots> = ?R $ i" using A v * by auto
    finally
    show "?L $ i = ?R $ i" .
  qed auto
qed
end

lemma vec_eq_iff: "(x = y) = (dim\<^sub>v x = dim\<^sub>v y \<and> (\<forall> i < dim\<^sub>v y. x $ i = y $ i))" (is "?l = ?r")
proof
  assume ?r
  show ?l
    by (rule vec_eqI, insert `?r`, auto)
qed simp

lemma mat_eq_iff: "(x = y) = (dim\<^sub>r x = dim\<^sub>r y \<and> dim\<^sub>c x = dim\<^sub>c y \<and> 
  (\<forall> i j. i < dim\<^sub>r y \<longrightarrow> j < dim\<^sub>c y \<longrightarrow> x $$ (i,j) = y $$ (i,j)))" (is "?l = ?r")
proof
  assume ?r
  show ?l
    by (rule mat_eqI, insert `?r`, auto)
qed simp

lemma (in inj_semiring_hom) vec_hom_zero_iff[simp]: "(vec\<^sub>h x = \<zero>\<^sub>v n) = (x = \<zero>\<^sub>v n)"
proof -
  {
    fix i
    assume i: "i < n" "dim\<^sub>v x = n"
    hence "vec\<^sub>h x $ i = 0 \<longleftrightarrow> x $ i = 0"
      using vec_index_map(1)[of i x] by simp
  } note main = this
  show ?thesis unfolding vec_eq_iff by (simp, insert main, auto)
qed  

lemma (in inj_semiring_hom) mat_hom_inj: "mat\<^sub>h A = mat\<^sub>h B \<Longrightarrow> A = B"
  unfolding mat_eq_iff by (auto simp: hom_inj)

lemma (in inj_semiring_hom) vec_hom_inj: "vec\<^sub>h v = vec\<^sub>h w \<Longrightarrow> v = w"
  unfolding vec_eq_iff by (auto simp: hom_inj)

lemma (in semiring_hom) mat_hom_pow: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "mat\<^sub>h (A ^\<^sub>m k) = (mat\<^sub>h A) ^\<^sub>m k"
proof (induct k)
  case (Suc k)
  thus ?case using mat_hom_mult[OF mat_pow_closed[OF A, of k] A] by simp
qed (simp add: mat_hom_one)

lemma (in semiring_hom) hom_mat_sum: "hom (mat_sum A) = mat_sum (mat\<^sub>h A)"
proof -
  obtain B where id: "?thesis = (hom (setsum (op $$ A) B) = setsum (op $$ (mat\<^sub>h A)) B)"
    and B: "B \<subseteq> {0..<dim\<^sub>r A} \<times> {0..<dim\<^sub>c A}"
  unfolding mat_sum_def by auto
  from B have "finite B" 
    using finite_subset by blast
  thus ?thesis unfolding id using B
  proof (induct B)
    case (insert x F)
    show ?case unfolding setsum.insert[OF insert(1-2)] hom_add 
      using insert(3-) by auto
  qed simp
qed


end
