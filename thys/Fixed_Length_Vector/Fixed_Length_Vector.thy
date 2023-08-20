theory Fixed_Length_Vector
  imports "HOL-Library.Numeral_Type" "HOL-Library.Code_Cardinality"
begin

lemma zip_map_same: \<open>zip (map f xs) (map g xs) = map (\<lambda>x. (f x, g x)) xs\<close>
  by (induction xs) auto

section \<open>Type class for indexing\<close>

text \<open>
  The \<open>index\<close> class is used to define an isomorphism between some index types with fixed cardinality
  and a subset of the natural numbers. Crucially, infinite types can be made instance of this class
  too, since Isabelle defines infinite cardinality to be equal to zero.

  The \<open>index1\<close> class then adds more properties, such as injectivity, which can only be satisfied for
  finite index types.

  This class is roughly similar to the \<^class>\<open>enum\<close> class defined in the Isabelle library, which is
  proved at a later point. However, \<^class>\<open>enum\<close> does not admit infinite types.
\<close>

class index =
  fixes from_index :: \<open>'a \<Rightarrow> nat\<close>
    and to_index :: \<open>nat \<Rightarrow> 'a\<close>
  assumes to_from_index: \<open>n < CARD('a) \<Longrightarrow> from_index (to_index n) = n\<close>
  assumes from_index_surj: \<open>n < CARD('a) \<Longrightarrow> \<exists>a. from_index a = n\<close>
begin

text \<open>A list of all possible indexes.\<close>

definition indexes :: \<open>'a list\<close> where
\<open>indexes = map to_index [0..<CARD('a)]\<close>

text \<open>There are as many indexes as the cardinality of type \<^typ>\<open>'a\<close>.\<close>

lemma indexes_length[simp]: \<open>length indexes = CARD('a)\<close>
  unfolding indexes_def by auto

lemma list_cong_index:
  assumes \<open>length xs = CARD('a)\<close> \<open>length ys = CARD('a)\<close>
  assumes \<open>\<And>i. xs ! from_index i = ys ! from_index i\<close>
  shows \<open>xs = ys\<close>
  apply (rule nth_equalityI)
  using assms from_index_surj by auto

lemma from_indexE:
  assumes \<open>n < CARD('a)\<close>
  obtains a where \<open>from_index a = n\<close>
  using assms by (metis from_index_surj)

end

text \<open>Restrict \<^class>\<open>index\<close> to only admit finite types.\<close>

class index1 = index +
  assumes from_index_bound[simp]: \<open>from_index a < CARD('a)\<close>
  assumes from_index_inj: \<open>inj from_index\<close>
begin

text \<open>Finiteness follows from the class assumptions.\<close>

lemma card_nonzero[simp]: \<open>0 < CARD('a)\<close>
  by (metis less_nat_zero_code from_index_bound neq0_conv)

lemma finite_type[simp]: \<open>finite (UNIV :: 'a set)\<close>
  by (metis card_nonzero  card.infinite less_irrefl)

sublocale finite
  by standard simp

text \<open>\<^const>\<open>to_index\<close> and \<^const>\<open>from_index\<close> form a bijection.\<close>

lemma from_to_index[simp]: \<open>to_index (from_index i) = i\<close>
  by (meson injD from_index_bound from_index_inj to_from_index)

lemma indexes_from_index[simp]: \<open>indexes ! from_index i = i\<close>
  unfolding indexes_def by auto

lemma to_index_inj_on: \<open>inj_on to_index {0..<CARD('a)}\<close>
  by (rule inj_onI) (force elim: from_indexE)


end

text \<open>Finally, we instantiate the class for the pre-defined numeral types.\<close>

instantiation num0 :: index
begin

definition from_index_num0 :: \<open>num0 \<Rightarrow> nat\<close> where \<open>from_index_num0 _ = undefined\<close>
definition to_index_num0 :: \<open>nat \<Rightarrow> num0\<close> where \<open>to_index_num0 _ = undefined\<close>

instance
  by standard auto

end


lemma indexes_zero[simp]: \<open>indexes = ([] :: 0 list)\<close>
  by (auto simp: indexes_def)

instantiation num1 :: index1
begin

definition from_index_num1 :: \<open>num1 \<Rightarrow> nat\<close> where [simp]: \<open>from_index_num1 _ = 0\<close>
definition to_index_num1 :: \<open>nat \<Rightarrow> num1\<close> where [simp]: \<open>to_index_num1 _ = 1\<close>

instance
  by standard (auto simp: inj_on_def)

end


lemma indexes_one[simp]: \<open>indexes = [1 :: 1]\<close>
  by (auto simp: indexes_def)

instantiation bit0 :: (finite) index1
begin

definition from_index_bit0 :: \<open>'a bit0 \<Rightarrow> nat\<close> where \<open>from_index_bit0 x = nat (Rep_bit0 x)\<close>

definition to_index_bit0 :: \<open>nat \<Rightarrow> 'a bit0\<close> where \<open>to_index_bit0 \<equiv> of_nat\<close>

instance
  apply standard
  subgoal
    by (simp add: to_index_bit0_def from_index_bit0_def bit0.of_nat_eq Abs_bit0_inverse)
  subgoal for n
    unfolding from_index_bit0_def by (auto simp: Abs_bit0_inverse intro!: exI[where x = \<open>Abs_bit0 (int n)\<close>])
  subgoal for n
    using Rep_bit0[of n]
    by (simp add: from_index_bit0_def nat_less_iff)
  subgoal
    unfolding from_index_bit0_def inj_on_def
    by (metis Rep_bit0 Rep_bit0_inverse atLeastLessThan_iff int_nat_eq)
  done

end

instantiation bit1 :: (finite) index1
begin

definition from_index_bit1 :: \<open>'a bit1 \<Rightarrow> nat\<close> where \<open>from_index_bit1 x = nat (Rep_bit1 x)\<close>

definition to_index_bit1 :: \<open>nat \<Rightarrow> 'a bit1\<close> where \<open>to_index_bit1 \<equiv> of_nat\<close>

instance
  apply standard
  subgoal
    by (simp add: to_index_bit1_def from_index_bit1_def bit1.of_nat_eq Abs_bit1_inverse)
  subgoal for n
    unfolding from_index_bit1_def by (auto simp: Abs_bit1_inverse intro!: exI[where x = \<open>Abs_bit1 (int n)\<close>])
  subgoal for n
    using Rep_bit1[of n]
    by (simp add: from_index_bit1_def nat_less_iff)
  subgoal
    unfolding from_index_bit1_def inj_on_def
    by (metis Rep_bit1 Rep_bit1_inverse atLeastLessThan_iff eq_nat_nat_iff)
  done

end

lemma indexes_bit_simps:
  \<open>(indexes :: 'a :: finite bit0 list) = map of_nat [0..<2 * CARD('a)]\<close>
  \<open>(indexes :: 'b :: finite bit1 list) = map of_nat [0..<2 * CARD('b) + 1]\<close>
  unfolding indexes_def to_index_bit0_def to_index_bit1_def
  by simp+

text \<open>The following class and instance definitions connect \<^const>\<open>indexes\<close> to \<^const>\<open>enum_class.enum\<close>.\<close>

class index_enum = index1 + enum +
  assumes indexes_eq_enum: \<open>indexes = enum_class.enum\<close>

instance num1 :: index_enum
  by standard (auto simp: indexes_def enum_num1_def)

instance bit0 :: (finite) index_enum
  by standard (auto simp: indexes_def to_index_bit0_def enum_bit0_def Abs_bit0'_def bit0.of_nat_eq)


instance bit1 :: (finite) index_enum
  by standard (auto simp: indexes_def to_index_bit1_def enum_bit1_def Abs_bit1'_def bit1.of_nat_eq)

section \<open>Type definition and BNF setup\<close>

text \<open>
  A vector is a list with a fixed length, where the length is given by the cardinality of the second
  type parameter. To obtain the unit vector, we can choose an infinite type. There is no reason to
  restrict the index type to a particular sort constraint at this point, even though later on,
  \<^class>\<open>index\<close> is frequently used.
\<close>

typedef ('a, 'b) vec = "{xs. length xs = CARD('b)} :: 'a list set"
  morphisms list_of_vec vec_of_list
  by (rule exI[where x = \<open>replicate CARD('b) undefined\<close>]) simp

declare vec.list_of_vec_inverse[simp]

type_notation vec (infixl "^" 15)

setup_lifting type_definition_vec

lift_definition map_vec :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a ^ 'c \<Rightarrow> 'b ^ 'c\<close> is map by auto

lift_definition set_vec :: \<open>'a ^ 'b \<Rightarrow> 'a set\<close> is set .

lift_definition rel_vec :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a ^ 'c \<Rightarrow> 'b ^ 'c \<Rightarrow> bool\<close> is list_all2 .

lift_definition pred_vec :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a ^ 'b \<Rightarrow> bool\<close> is list_all .

lift_definition zip_vec :: \<open>'a ^ 'c \<Rightarrow> 'b ^ 'c \<Rightarrow> ('a \<times> 'b) ^ 'c\<close> is zip by auto

lift_definition replicate_vec :: \<open>'a \<Rightarrow> 'a ^ 'b\<close> is \<open>replicate CARD('b)\<close> by auto

bnf \<open>('a, 'b) vec\<close>
  map: map_vec
  sets: set_vec
  bd: natLeq
  wits: replicate_vec
  rel: rel_vec
  pred: pred_vec
  subgoal
    apply (rule ext)
    by transfer' auto
  subgoal
    apply (rule ext)
    by transfer' auto
  subgoal
    by transfer' auto
  subgoal
    apply (rule ext)
    by transfer' auto
  subgoal by (fact natLeq_card_order)
  subgoal by (fact natLeq_cinfinite)
  subgoal by (fact regularCard_natLeq)
  subgoal
    apply transfer'
    apply (simp flip: finite_iff_ordLess_natLeq)
    done
  subgoal
    apply (rule predicate2I)
    apply transfer'
    by (smt (verit) list_all2_trans relcompp.relcompI)
  subgoal
    apply (rule ext)+
    apply transfer
    by (auto simp: list.in_rel)
  subgoal
    apply (rule ext)
    apply transfer'
    by (auto simp: list_all_iff)
  subgoal
    by transfer' auto
  done

section \<open>Indexing\<close>

lift_definition nth_vec' :: \<open>'a ^ 'b \<Rightarrow> nat \<Rightarrow> 'a\<close> is nth .

lift_definition nth_vec :: \<open>'a ^ 'b \<Rightarrow> 'b :: index1 \<Rightarrow> 'a\<close> (infixl "$" 90)
  \<comment> \<open>We fix this to \<^class>\<open>index1\<close> because indexing a unit vector makes no sense.\<close>
  is \<open>\<lambda>xs. nth xs \<circ> from_index\<close> .

lemma nth_vec_alt_def: \<open>nth_vec v = nth_vec' v \<circ> from_index\<close>
  by transfer' auto

text \<open>
  We additionally define a notion of converting a function into a vector, by mapping over all
  \<^const>\<open>indexes\<close>.
\<close>

lift_definition vec_lambda :: \<open>('b :: index \<Rightarrow> 'a) \<Rightarrow> 'a ^ 'b\<close> (binder "\<chi>" 10)
  is \<open>\<lambda>f. map f indexes\<close> by simp

lemma vec_lambda_nth[simp]: \<open>vec_lambda f $ i = f i\<close>
  by transfer auto

section \<open>Unit vector\<close>

text \<open>
  The \<^emph>\<open>unit vector\<close> is the unique vector of length zero. We use \<^typ>\<open>0\<close> as index type, but
  \<^typ>\<open>nat\<close> or any other infinite type would work just as well.
\<close>

lift_definition unit_vec :: \<open>'a ^ 0\<close> is \<open>[]\<close> by simp

lemma unit_vec_unique: \<open>v = unit_vec\<close>
  by transfer auto

lemma unit_vec_unique_simp[simp]: \<open>NO_MATCH v unit_vec \<Longrightarrow> v = unit_vec\<close>
  by (rule unit_vec_unique)

lemma set_unit_vec[simp]: \<open>set_vec (v :: 'a ^ 0) = {}\<close>
  by transfer auto

lemma map_unit_vec[simp]: \<open>map_vec f v = unit_vec\<close>
  by simp

lemma zip_unit_vec[simp]: \<open>zip_vec u v = unit_vec\<close>
  by simp

lemma rel_unit_vec[simp]: \<open>rel_vec R (u :: 'a ^ 0) v \<longleftrightarrow> True\<close>
  by transfer auto

lemma pred_unit_vec[simp]: \<open>pred_vec P (v :: 'a ^ 0)\<close>
  by (simp add: vec.pred_set)


section \<open>General lemmas\<close>

lemmas vec_simps[simp] =
  map_vec.rep_eq
  zip_vec.rep_eq
  replicate_vec.rep_eq

lemmas map_vec_cong[fundef_cong] = map_cong[Transfer.transferred]

lemmas rel_vec_cong = list.rel_cong[Transfer.transferred]

lemmas pred_vec_cong = list.pred_cong[Transfer.transferred]

lemma vec_eq_if: "list_of_vec f = list_of_vec g \<Longrightarrow> f = g"
  by (metis list_of_vec_inverse)

lemma vec_cong: "(\<And>i. f $ i = g $ i) \<Longrightarrow> f = g"
  by transfer (simp add: list_cong_index)

lemma finite_set_vec[intro, simp]: \<open>finite (set_vec v)\<close>
  by transfer' auto

lemma set_vec_in[intro, simp]: \<open>v $ i \<in> set_vec v\<close>
  by transfer auto

lemma set_vecE[elim]:
  assumes \<open>x \<in> set_vec v\<close>
  obtains i where \<open>x = v $ i\<close>
  using assms
  by transfer (auto simp: in_set_conv_nth elim: from_indexE)

lemma map_nth_vec[simp]: \<open>map_vec f v $ i = f (v $ i)\<close>
  by transfer auto

lemma replicate_nth_vec[simp]: \<open>replicate_vec a $ i = a\<close>
  by transfer auto

lemma replicate_set_vec[simp]: \<open>set_vec (replicate_vec a :: 'a ^ 'b :: index1) = {a}\<close>
  by transfer simp

lemma vec_explode: \<open>v = (\<chi> i. v $ i)\<close>
  by (rule vec_cong) auto

lemma vec_explode1:
  fixes v :: \<open>'a ^ 1\<close>
  obtains a where \<open>v = (\<chi> _. a)\<close>
  apply (rule that[of \<open>v $ 1\<close>])
  apply (subst vec_explode[of v])
  apply (rule arg_cong[where f = vec_lambda])
  apply (rule ext)
  apply (subst num1_eq1)
  by (rule refl)

lemma zip_nth_vec[simp]: \<open>zip_vec u v $ i = (u $ i, v $ i)\<close>
  by transfer auto

lemma zip_vec_fst[simp]: \<open>map_vec fst (zip_vec u v) = u\<close>
  by transfer auto

lemma zip_vec_snd[simp]: \<open>map_vec snd (zip_vec u v) = v\<close>
  by transfer auto

lemma zip_lambda_vec[simp]: \<open>zip_vec (vec_lambda f) (vec_lambda g) = (\<chi> i. (f i, g i))\<close>
  by transfer' (simp add: zip_map_same)

lemma zip_map_vec: \<open>zip_vec (map_vec f u) (map_vec g v) = map_vec (\<lambda>(x, y). (f x, g y)) (zip_vec u v)\<close>
  by transfer' (auto simp: zip_map1 zip_map2)

lemma list_of_vec_length[simp]: \<open>length (list_of_vec (v :: 'a ^ 'b)) = CARD('b)\<close>
  using list_of_vec by blast

lemma list_vec_list: \<open>length xs = CARD('n) \<Longrightarrow> list_of_vec (vec_of_list xs :: 'a ^ 'n) = xs\<close>
  by (subst vec.vec_of_list_inverse) auto

lemma map_vec_list: \<open>length xs = CARD('n) \<Longrightarrow> map_vec f (vec_of_list xs :: 'a ^ 'n) = vec_of_list (map f xs)\<close>
  by (rule map_vec.abs_eq) (auto simp: eq_onp_def)

lemma set_vec_list: \<open>length xs = CARD('n) \<Longrightarrow> set_vec (vec_of_list xs :: 'a ^ 'n) = set xs\<close>
  by (rule set_vec.abs_eq) (auto simp: eq_onp_def)

lemma list_all_zip: \<open>length xs = length ys \<Longrightarrow> list_all P (zip xs ys) \<longleftrightarrow> list_all2 (\<lambda>x y. P (x, y)) xs ys\<close>
  by (erule list_induct2) auto

lemma pred_vec_zip: \<open>pred_vec P (zip_vec xs ys) \<longleftrightarrow> rel_vec (\<lambda>x y. P (x, y)) xs ys\<close>
  by transfer (simp add: list_all_zip)

lemma list_all2_left: \<open>length xs = length ys \<Longrightarrow> list_all2 (\<lambda>x y. P x) xs ys \<longleftrightarrow> list_all P xs\<close>
  by (erule list_induct2) auto

lemma list_all2_right: \<open>length xs = length ys \<Longrightarrow> list_all2 (\<lambda>_. P) xs ys \<longleftrightarrow> list_all P ys\<close>
  by (erule list_induct2) auto

lemma rel_vec_left: \<open>rel_vec (\<lambda>x y. P x) xs ys \<longleftrightarrow> pred_vec P xs\<close>
  by transfer (simp add: list_all2_left)

lemma rel_vec_right: \<open>rel_vec (\<lambda>_. P) xs ys \<longleftrightarrow> pred_vec P ys\<close>
  by transfer (simp add: list_all2_right)


section \<open>Instances\<close>

definition bounded_lists :: \<open>nat \<Rightarrow> 'a set \<Rightarrow> 'a list set\<close> where
\<open>bounded_lists n A = {xs. length xs = n \<and> list_all (\<lambda>x. x \<in> A) xs}\<close>

lemma bounded_lists_finite:
  assumes \<open>finite A\<close>
  shows \<open>finite (bounded_lists n A)\<close>
proof (induction n)
  case (Suc n)
  moreover have \<open>bounded_lists (Suc n) A \<subseteq> (\<lambda>(x, xs). x # xs) ` (A \<times> bounded_lists n A)\<close>
    unfolding bounded_lists_def
    by (force simp: length_Suc_conv split_beta)
  ultimately show ?case
    using assms by (meson finite_SigmaI finite_imageI finite_subset)
qed (simp add: bounded_lists_def)

lemma bounded_lists_bij: \<open>bij_betw list_of_vec (UNIV :: ('a ^ 'b) set) (bounded_lists CARD('b) UNIV)\<close>
  unfolding bij_betw_def bounded_lists_def
  by (metis (no_types, lifting) Ball_set Collect_cong UNIV_I inj_def type_definition.Rep_range type_definition_vec vec_eq_if)


text \<open>If the base type is \<^class>\<open>finite\<close>, so is the vector type.\<close>

instance vec :: (finite, type) finite
  apply standard
  apply (subst bij_betw_finite[OF bounded_lists_bij])
  apply (rule bounded_lists_finite)
  by simp

text \<open>The \<^const>\<open>size\<close> of the vector is the \<^const>\<open>length\<close> of the underlying list.\<close>

instantiation vec :: (type, type) size
begin

lift_definition size_vec :: \<open>'a ^ 'b \<Rightarrow> nat\<close> is length .

instance ..

end

lemma size_vec_alt_def[simp]: \<open>size (v :: 'a ^ 'b) = CARD('b)\<close>
  by transfer simp

text \<open>Vectors can be compared for equality.\<close>

instantiation vec :: (equal, type) equal
begin

lift_definition equal_vec :: \<open>'a ^ 'b \<Rightarrow> 'a ^ 'b \<Rightarrow> bool\<close> is \<open>equal_class.equal\<close> .

instance
  apply standard
  apply transfer'
  by (simp add: equal_list_def)

end

section \<open>Further operations\<close>

subsection \<open>Distinctness\<close>

lift_definition distinct_vec :: \<open>'a ^ 'n \<Rightarrow> bool\<close> is \<open>distinct\<close> .

lemma distinct_vec_alt_def: \<open>distinct_vec v \<longleftrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> v $ i \<noteq> v $ j)\<close>
  apply transfer
  unfolding distinct_conv_nth comp_apply
  by (metis from_index_bound from_to_index to_from_index)

lemma distinct_vecI:
  assumes \<open>\<And>i j. i \<noteq> j \<Longrightarrow> v $ i \<noteq> v $ j\<close>
  shows \<open>distinct_vec v\<close>
  using assms unfolding distinct_vec_alt_def by simp

lemma distinct_vec_mapI: \<open>distinct_vec xs \<Longrightarrow> inj_on f (set_vec xs) \<Longrightarrow> distinct_vec (map_vec f xs)\<close>
  by transfer' (metis distinct_map)

lemma distinct_vec_zip_fst: \<open>distinct_vec u \<Longrightarrow> distinct_vec (zip_vec u v)\<close>
  by transfer' (metis distinct_zipI1)

lemma distinct_vec_zip_snd: \<open>distinct_vec v \<Longrightarrow> distinct_vec (zip_vec u v)\<close>
  by transfer' (metis distinct_zipI2)

lemma inj_set_of_vec: \<open>distinct_vec (map_vec f v) \<Longrightarrow> inj_on f (set_vec v)\<close>
  by transfer' (metis distinct_map)

lemma distinct_vec_list: \<open>length xs = CARD('n) \<Longrightarrow> distinct_vec (vec_of_list xs :: 'a ^ 'n) \<longleftrightarrow> distinct xs\<close>
  by (subst distinct_vec.rep_eq) (simp add: list_vec_list)

subsection \<open>Summing\<close>

lift_definition sum_vec :: \<open>'b::comm_monoid_add ^ 'a \<Rightarrow> 'b\<close> is sum_list .

lemma sum_vec_lambda: \<open>sum_vec (vec_lambda v) = sum_list (map v indexes)\<close>
  by transfer simp

lemma elem_le_sum_vec:
  fixes f :: \<open>'a :: canonically_ordered_monoid_add ^ 'b :: index1\<close>
  shows "f $ i \<le> sum_vec f"
  by transfer (simp add: elem_le_sum_list)


section \<open>Code setup\<close>

text \<open>
  Since \<^const>\<open>vec_of_list\<close> cannot be directly used in code generation, we defined a convenience
  wrapper that checks the length and aborts if necessary.
\<close>

definition replicate' where \<open>replicate' n = replicate n undefined\<close>

declare [[code abort: replicate']]

lift_definition vec_of_list' :: \<open>'a list \<Rightarrow> 'a ^ 'n\<close>
  is \<open>\<lambda>xs. if length xs \<noteq> CARD('n) then replicate' CARD('n) else xs\<close>
  by (auto simp: replicate'_def)


experiment begin

proposition
  \<open>sum_vec (\<chi> (i::2). (3::nat)) = 6\<close>
  \<open>distinct_vec (vec_of_list' [1::nat, 2] :: nat ^ 2)\<close>
  \<open>\<not> distinct_vec (vec_of_list' [1::nat, 1] :: nat ^ 2)\<close>
  by eval+

end

export_code
  sum_vec
  map_vec
  rel_vec
  pred_vec
  set_vec
  zip_vec
  distinct_vec
  list_of_vec
  vec_of_list'
  checking SML

lifting_update vec.lifting
lifting_forget vec.lifting

bundle vec_syntax begin
type_notation
  vec (infixl "^" 15)
notation
  nth_vec (infixl "$" 90) and
  vec_lambda (binder "\<chi>" 10)
end

bundle no_vec_syntax begin
no_type_notation
  vec (infixl "^" 15)
no_notation
  nth_vec (infixl "$" 90) and
  vec_lambda (binder "\<chi>" 10)
end

unbundle no_vec_syntax

end