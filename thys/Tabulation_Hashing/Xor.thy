theory Xor
imports
  Main
begin

text \<open>This theory abstractly defines
\begin{itemize}
\item the binary operator \<open>xor\<close> (aliases \<open>(XOR)\<close> \<open>(\<oplus>)\<close>)
\item the n-ary version \<open>xor_fold\<close>
\item and the Big version \<open>xor_sum\<close> (alias \<open>\<Oplus>i\<in>J. f i\<close>).
\end{itemize}

An implementation of xor should abide by the following laws:
\begin{itemize}
\item identity element
\item commutative
\item associative
\item left/right neutrality
\item self-inverse
\end{itemize}

which constitutes an abelian group.

Instantiations of abel\_group\_xor have been provided for bool, nat and int.

Other theories relating to xor:
\begin{itemize}
\item @{const Boolean_Algebras.abstract_boolean_algebra_sym_diff}
\item @{const Bit_Operations.semiring_bit_operations_class.xor}
\item (AFP) \verb|Approximate_Model_Counting.RandomXOR| \cite{Approximate_Model_Counting-AFP}
\end{itemize}
\<close>

section \<open>Preliminaries\<close>
subsection \<open>The XOR operator\<close>

lemma (in monoid_list) list_conv_take_drop:
  shows "F xs = F (take i xs) \<^bold>* F (drop i xs)"
  by (metis append append_take_drop_id)

lemma (in monoid_list) list_conv_take_nth_drop:
  assumes "i < length xs"
  shows "F xs = F (take i xs) \<^bold>* xs ! i \<^bold>* F (drop (Suc i) xs)"
  by (metis Cons_nth_drop_Suc append append_take_drop_id assms assoc local.Cons)

lemma (in comm_monoid_list) absorb_right:
  assumes "i < length xs"
  shows "F xs \<^bold>* v = F (xs[i := xs ! i \<^bold>* v])"
  by (smt (verit, del_insts) append assms assoc commute list_conv_take_nth_drop local.Cons
    upd_conv_take_nth_drop)

lemma (in semiring_bit_operations) eq_iff:
  shows "semiring_bit_operations_class.xor a b = 0 \<longleftrightarrow> a = b"
  by (metis local.xor.assoc local.xor.left_neutral local.xor_self_eq)

subsubsection \<open>Definition of XOR\<close>

class xor =
  fixes xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>XOR\<close> 59) \<comment> \<open>Definition of 2-ary xor\<close>

class abel_group_xor = zero + xor +
  assumes xor_commute: "a XOR b = b XOR a"
  assumes xor_assoc: "(a XOR b) XOR c = a XOR b XOR c"
  assumes xor_right_neutral: "a XOR 0 = a"
  assumes eq_iff [iff]: "a XOR b = 0 \<longleftrightarrow> a = b"
begin

lemma self_inv [simp]:
  shows "a XOR a = 0"
  by simp

text \<open>The above properties show that XOR forms an abelian group\<close>
sublocale group xor 0 id
  using xor_commute xor_assoc by unfold_locales (simp_all add: xor_right_neutral)

sublocale abel_semigroup xor by unfold_locales (simp add: xor_commute)

sublocale comm_monoid xor 0 by unfold_locales simp

sublocale xor_sum: comm_monoid_set xor 0
  defines xor_sum = xor_sum.F ..

abbreviation "Xor_Sum \<equiv> xor_sum (\<lambda>x. x)"

sublocale xor_list: monoid_list xor 0
  defines xor_fold = xor_list.F .. \<comment> \<open>Definition of n-ary xor\<close>

sublocale xor_comm_list: comm_monoid_list xor 0
  rewrites "monoid_list.F xor 0 = xor_fold"
proof -
  show "comm_monoid_list xor 0" ..
  then interpret comm_monoid_list xor 0 .
  from xor_fold_def show "monoid_list.F xor 0 = xor_fold" by simp
qed

sublocale xor_list: comm_monoid_list_set xor 0
  rewrites "monoid_list.F xor 0 = xor_fold" and "comm_monoid_set.F xor 0 = xor_sum"
proof -
  show "comm_monoid_list_set xor 0" ..
  then interpret xor_sum: comm_monoid_list_set xor 0 .
  from xor_fold_def show "monoid_list.F xor 0 = xor_fold" by simp
  from xor_sum_def show "comm_monoid_set.F xor 0 = xor_sum" by (auto intro: sym)
qed

lemma xor_cong:
  assumes "a XOR b = 0"
  shows "a = b"
  using assms eq_iff by blast

lemma inj_on_UNIV:
  shows "inj_on xor UNIV"
  by (rule inj_onI) (metis right_neutral)

lemma map_indices_conv_list_update_conv:
  shows "map (\<lambda>j. if j = i then g j else xs ! j) [0..<length xs] = xs[i := g i]"
  by (fastforce intro: nth_equalityI)

lemma \<^marker>\<open>tag important\<close> fold_absorb:
  assumes "i < length xs"
  shows "xor_fold xs XOR v =
    xor_fold (map (\<lambda>j. if j = i then xs ! j XOR v else xs ! j) [0..<length xs])"
  unfolding map_indices_conv_list_update_conv
  using xor_comm_list.absorb_right[OF assms] .
end (*class xor*)

hide_fact xor_commute xor_assoc xor_right_neutral

subsubsection \<open>Standard Instantiations\<close>

instantiation bool :: abel_group_xor begin
definition (*tag:review*) "zero_bool \<equiv> False" (* since \<open>of_bool False = 0\<close> this should be okay *)
definition xor_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "xor_bool a b \<equiv> (a \<noteq> b)"
instance by standard (auto simp add: xor_bool_def zero_bool_def)
end (*instance bool::abel_group_xor*)

instantiation nat and int :: abel_group_xor begin
(* note: any type that implements semiring_bit_operations can be implemented this way, i.e. 'a word *)
definition xor_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "xor_nat \<equiv> semiring_bit_operations_class.xor"
definition xor_int :: "int \<Rightarrow> int \<Rightarrow> int" where "xor_int \<equiv> semiring_bit_operations_class.xor"
instance by standard (simp_all add: xor_nat_def xor_int_def ac_simps semiring_bit_operations_class.eq_iff)
end (*instance nat int :: abel_group_xor*)

subsubsection \<open>Syntactic sugar\<close>

open_bundle xor_syntax begin

notation xor (infixr \<open>\<oplus>\<close> 59)
notation Xor_Sum (\<open>\<Oplus>\<close>)

(* directly lifted from Groups_Big.thy *)
text \<open>Now: lots of fancy syntax. First, \<^term>\<open>xor_sum (\<lambda>x. e) A\<close> is written \<open>\<Oplus>x\<in>A. e\<close>.\<close>

syntax (ASCII)
  "_xor_sum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::abel_group_xor"  (\<open>(\<open>indent=3 notation=\<open>binder XORSUM\<close>\<close>XORSUM (_/:_)./ _)\<close> [0, 51, 10] 10)
syntax
  "_xor_sum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::abel_group_xor"  (\<open>(\<open>indent=2 notation=\<open>binder \<Oplus>\<close>\<close>\<Oplus>(_/\<in>_)./ _)\<close> [0, 51, 10] 10)

syntax_consts
  "_xor_sum" \<rightleftharpoons> xor_sum

translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Oplus>i\<in>A. b" \<rightleftharpoons> "CONST xor_sum (\<lambda>i. b) A"
end

unbundle no xor_syntax
end (* theory *)