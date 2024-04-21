(*<*)
theory Ix
imports
  Main
begin

(*>*)
subsection\<open> A Haskell-like \<^emph>\<open>Ix\<close> class\label{sec:Ix} \<close>

text\<open>

We allow arbitrary indexing schemes for user-facing arrays via the
\<open>Ix\<close> class, which essentially represents a bijection
between a subset of an arbitrary type and an initial segment of the
naturals.

Source materials:
 \<^item> Haskell 2010 report: \<^url>\<open>https://www.haskell.org/onlinereport/haskell2010/haskellch19.html\<close>
 \<^item> GHC implementation: \<^url>\<open>https://hackage.haskell.org/package/base-4.16.0.0/docs/src/GHC.Ix.html\<close>
 \<^item> Haskell pure arrays (just for colour): \<^url>\<open>https://www.haskell.org/onlinereport/haskell2010/haskellch14.html\<close>
 \<^item> SML 2D arrays: \<^url>\<open>https://smlfamily.github.io/Basis/array2.html\<close>

Observations:
 \<^item> follow Haskell convention here: include the bounds
 \<^item> could alternatively use an array of one-dimensional arrays but those are not necessarily rectangular
 \<^item> we can't use \<^class>\<open>enum\<close> as that requires the whole type to be enumerable

Limitations:
 \<^item> the basic design assumes laziness; we don't ever want to build the list of indices
  \<^item> can be improved either by tweaking the code generator setup or changing the constants here
 \<^item> array indices typically have partial predecessor and successor operations and are totally ordered on their domain
 \<^item> no guarantee the \<open>interval\<close> is correct (does not prevent off-by-one errors in instances)

\<close>

class Ix =
  fixes interval :: "'a \<times> 'a \<Rightarrow> 'a list"
  fixes index :: "'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> nat"
  assumes index: "i \<in> set (interval b) \<Longrightarrow> interval b ! index b i = i"
  assumes interval: "map (index b) (interval b) = [0..<length (interval b)]"

lemma index_length:
  assumes "i \<in> set (interval b)"
  shows "index b i < length (interval b)"
proof -
  from assms[unfolded in_set_conv_nth]
  obtain j where "j < length (interval b)" and "interval b ! j = i"
    by blast
  with arg_cong[where f="\<lambda>x. List.nth x j", OF interval[of b]] show ?thesis
    by simp
qed

lemma distinct_interval:
  shows "distinct (interval b)"
by (metis distinct_map distinct_upt interval)

lemma inj_on_index:
  shows "inj_on (index b) (set (interval b))"
by (metis distinct_map distinct_upt interval)

lemma index_eq_conv:
  assumes "i \<in> set (interval b)"
  assumes "j \<in> set (interval b)"
  shows "index b i = index b j \<longleftrightarrow> i = j"
by (metis assms index)

lemma index_inv_into:
  assumes "i < length (interval b)"
  shows "inv_into (set (interval b)) (index b) i \<in> set (interval b)"
by (metis assms add.left_neutral inv_into_into length_map list.set_map interval nth_mem nth_upt)

lemma linear_order_on:
  shows "linear_order_on (set (interval b)) {(i, j). {i, j} \<subseteq> set (interval b) \<and> index b i \<le> index b j}"
by (force simp: linear_order_on_def partial_order_on_def preorder_on_def refl_on_def total_on_def
         intro: transI antisymI
          dest: index)

lemma interval_map:
  shows "map (\<lambda>i. f (interval b ! i)) [0..<length (interval b)] = map f (interval b)"
by (simp add: map_equality_iff)

lemma index_forE:
  assumes "i < length (interval b)"
  obtains j where "j \<in> set (interval b)" and "index b j = i"
using assms index index_length nth_eq_iff_index_eq[OF distinct_interval] nth_mem[OF assms] by blast

instantiation unit :: Ix
begin

definition "interval_unit = (\<lambda>(x::unit, y::unit). [()])"
definition "index_unit = (\<lambda>(x::unit, y::unit) _::unit. 0::nat)"

instance by standard (auto simp: interval_unit_def index_unit_def)

end

instantiation nat :: Ix
begin

definition "interval_nat = (\<lambda>(l, u::nat). [l..<Suc u])" \<comment>\<open> bounds are inclusive \<close>
definition "index_nat = (\<lambda>(l, u::nat) i::nat. i - l)"

lemma upt_minus:
  shows "map (\<lambda>i. i - l) [l..<u] = [0..<u - l]"
by (induct u) (auto simp: Suc_diff_le)

instance by standard (auto simp: interval_nat_def index_nat_def upt_minus nth_append)

end

instantiation int :: Ix
begin

definition "interval_int = (\<lambda>(l, u::int). [l..u])" \<comment>\<open> bounds are inclusive \<close>
definition "index_int = (\<lambda>(l, u::int) i::int. nat (i - l))"

lemma upto_minus:
  shows "map (\<lambda>i. nat (i - l)) [l..u] = [0..<nat (u - l + 1)]"
proof(induct "nat(u - l + 1)" arbitrary: u)
  case (Suc i)
  from Suc.hyps(1)[of "u - 1"] Suc.hyps(2) show ?case
    by (simp add: upto_rec2 ac_simps Suc_nat_eq_nat_zadd1 flip: upt_Suc_append)
qed simp

instance by standard (auto simp: interval_int_def index_int_def upto_minus)

end

type_synonym ('i, 'j) two_dim = "('i \<times> 'j) \<times> ('i \<times> 'j)"

instantiation prod :: (Ix, Ix) Ix
begin

definition "interval_prod = (\<lambda>((l, l'), (u, u')). List.product (interval (l, u)) (interval (l', u')))"
definition "index_prod = (\<lambda>((l, l'), (u, u')) (i, i'). index (l, u) i * length (interval (l', u')) + index (l', u') i')"

abbreviation (input) fst_bounds :: "('a \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'a)" where
  "fst_bounds b \<equiv> (fst (fst b), fst (snd b))"

abbreviation (input) snd_bounds :: "('a \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> ('b \<times> 'b)" where
  "snd_bounds b \<equiv> (snd (fst b), snd (snd b))"

lemma inj_on_index_prod:
  shows "inj_on (index ((l, l'), (u, u'))) (set (interval ((l, l'), (u, u'))))"
by (clarsimp simp: inj_on_def interval_prod_def index_prod_def)
   (metis index index_length length_pos_if_in_set add_diff_cancel_right'
          div_mult_self_is_m mod_less mod_mult_self3)

instance
proof
  show "interval b ! index b i = i" if "i \<in> set (interval b)" for b and i :: "'a \<times> 'b"
  proof -
    have *: "i * n + j < m * n" if "i < m"  and "j < n"
     for i j m n :: nat
      using that by (metis bot_nat_0.extremum_strict div_less div_less_iff_less_mult div_mult_self3 nat_arith.rule0 not_gr_zero)
    from that
    have "index (fst_bounds b) (fst i) * length (interval (snd_bounds b))
            + index (snd_bounds b) (snd i)
        < length (interval (fst_bounds b)) * length (interval (snd_bounds b))"
      by (clarsimp simp: interval_prod_def index_prod_def * dest!: index_length)
    then show ?thesis
      using that length_pos_if_in_set
      by (fastforce simp: interval_prod_def index_prod_def List.product_nth index index_length)
  qed
  show "map (index b) (interval b) = [0..<length (interval b)]" for b :: "('a \<times> 'b) \<times> ('a \<times> 'b)"
    by (rule iffD2[OF list_eq_iff_nth_eq])
       (clarsimp simp: interval_prod_def index_prod_def split_def product_nth ac_simps;
        metis (no_types, lifting) distinct_interval index index_length length_pos_if_in_set nth_mem
              less_mult_imp_div_less mod_div_mult_eq mod_less_divisor mult.commute nth_eq_iff_index_eq)
qed

end

setup \<open>Sign.mandatory_path "Ix"\<close>

setup \<open>Sign.mandatory_path "prod"\<close>

lemma interval_conv:
  shows "(x, y) \<in> set (interval b) \<longleftrightarrow> x \<in> set (interval (fst_bounds b)) \<and> y \<in> set (interval (snd_bounds b))"
by (force simp: interval_prod_def)

setup \<open>Sign.parent_path\<close>

type_synonym 'i square = "('i, 'i) two_dim"

definition square :: "'i::Ix Ix.square \<Rightarrow> bool" where
  "square = (\<lambda>((l, l'), (u, u')). Ix.interval (l, u) = Ix.interval (l', u'))"

setup \<open>Sign.mandatory_path "square"\<close>

lemma conv:
  assumes "Ix.square b"
  shows "i \<in> set (Ix.interval (fst_bounds b)) \<longleftrightarrow> i \<in> set (Ix.interval (snd_bounds b))"
using assms by (clarsimp simp: Ix.square_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

hide_const (open) interval index
(*<*)

end
(*>*)
