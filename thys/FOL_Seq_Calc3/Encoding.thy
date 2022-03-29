section \<open>Encoding\<close>

theory Encoding imports "HOL-Library.Nat_Bijection" Syntax begin

abbreviation infix_sum_encode (infixr \<open>$\<close> 100) where
  \<open>c $ x \<equiv> sum_encode (c x)\<close>

lemma lt_sum_encode_Inr: \<open>n < Inr $ n\<close>
  unfolding sum_encode_def by simp

lemma sum_prod_decode_lt [simp]: \<open>sum_decode n = Inr b \<Longrightarrow> (x, y) = prod_decode b \<Longrightarrow> y < Suc n\<close>
  by (metis le_prod_encode_2 less_Suc_eq lt_sum_encode_Inr order_le_less_trans
      prod_decode_inverse sum_decode_inverse)

lemma sum_prod_decode_lt_Suc [simp]:
  \<open>sum_decode n = Inr b \<Longrightarrow> (Suc x, y) = prod_decode b \<Longrightarrow> x < Suc n\<close>
  by (metis dual_order.strict_trans le_prod_encode_1 lessI linorder_not_less lt_sum_encode_Inr
      not_less_eq prod_decode_inverse sum_decode_inverse)

lemma lt_list_encode: \<open>n [\<in>] ns \<Longrightarrow> n < list_encode ns\<close>
proof (induct ns)
  case (Cons m ns)
  then show ?case
    using le_prod_encode_1 le_prod_encode_2
    by (metis dual_order.strict_trans1 le_imp_less_Suc less_SucI list_encode.simps(2) set_ConsD)
qed simp

lemma prod_Suc_list_decode_lt [simp]:
  \<open>(x, Suc y) = prod_decode n \<Longrightarrow> y' [\<in>] (list_decode y) \<Longrightarrow> y' < n\<close>
  by (metis Suc_le_lessD lt_list_encode le_prod_encode_2 list_decode_inverse order_less_trans
      prod_decode_inverse)

subsection \<open>Terms\<close>

primrec nat_of_tm :: \<open>tm \<Rightarrow> nat\<close> where
  \<open>nat_of_tm (\<^bold>#n) = prod_encode (n, 0)\<close>
| \<open>nat_of_tm (\<^bold>\<dagger>f ts) = prod_encode (f, Suc (list_encode (map nat_of_tm ts)))\<close>

function tm_of_nat :: \<open>nat \<Rightarrow> tm\<close> where
  \<open>tm_of_nat n = (case prod_decode n of
    (n, 0) \<Rightarrow> \<^bold>#n
  | (f, Suc ts) \<Rightarrow> \<^bold>\<dagger>f (map tm_of_nat (list_decode ts)))\<close>
  by pat_completeness auto
termination by (relation \<open>measure id\<close>) simp_all

lemma tm_nat: \<open>tm_of_nat (nat_of_tm t) = t\<close>
  by (induct t) (simp_all add: map_idI)

lemma surj_tm_of_nat: \<open>surj tm_of_nat\<close>
  unfolding surj_def using tm_nat by metis

subsection \<open>Formulas\<close>

primrec nat_of_fm :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>nat_of_fm \<^bold>\<bottom> = 0\<close>
| \<open>nat_of_fm (\<^bold>\<ddagger>P ts) = Suc (Inl $ prod_encode (P, list_encode (map nat_of_tm ts)))\<close>
| \<open>nat_of_fm (p \<^bold>\<longrightarrow> q) = Suc (Inr $ prod_encode (Suc (nat_of_fm p), nat_of_fm q))\<close>
| \<open>nat_of_fm (\<^bold>\<forall>p) = Suc (Inr $ prod_encode (0, nat_of_fm p))\<close>

function fm_of_nat :: \<open>nat \<Rightarrow> fm\<close> where
  \<open>fm_of_nat 0 = \<^bold>\<bottom>\<close>
| \<open>fm_of_nat (Suc n) = (case sum_decode n of
    Inl n \<Rightarrow> let (P, ts) = prod_decode n in \<^bold>\<ddagger>P (map tm_of_nat (list_decode ts))
  | Inr n \<Rightarrow> (case prod_decode n of
      (Suc p, q) \<Rightarrow> fm_of_nat p \<^bold>\<longrightarrow> fm_of_nat q
    | (0, p) \<Rightarrow> \<^bold>\<forall>(fm_of_nat p)))\<close>
  by pat_completeness auto
termination by (relation \<open>measure id\<close>) simp_all

lemma fm_nat: \<open>fm_of_nat (nat_of_fm p) = p\<close>
  using tm_nat by (induct p) (simp_all add: map_idI)

lemma surj_fm_of_nat: \<open>surj fm_of_nat\<close>
  unfolding surj_def using fm_nat by metis

subsection \<open>Rules\<close>

text \<open>Pick a large number to help encode the Idle rule, so that we never hit it in practice.\<close>

definition idle_nat :: nat where
  \<open>idle_nat \<equiv> 4294967295\<close>

primrec nat_of_rule :: \<open>rule \<Rightarrow> nat\<close> where
  \<open>nat_of_rule Idle = Inl $ prod_encode (0, idle_nat)\<close>
| \<open>nat_of_rule (Axiom n ts) = Inl $ prod_encode (Suc n, Suc (list_encode (map nat_of_tm ts)))\<close>
| \<open>nat_of_rule FlsL = Inl $ prod_encode (0, 0)\<close>
| \<open>nat_of_rule FlsR = Inl $ prod_encode (0, Suc 0)\<close>
| \<open>nat_of_rule (ImpL p q) = Inr $ prod_encode (Inl $ nat_of_fm p, Inl $ nat_of_fm q)\<close>
| \<open>nat_of_rule (ImpR p q) = Inr $ prod_encode (Inr $ nat_of_fm p, nat_of_fm q)\<close>
| \<open>nat_of_rule (UniL t p) = Inr $ prod_encode (Inl $ nat_of_tm t, Inr $ nat_of_fm p)\<close>
| \<open>nat_of_rule (UniR p) = Inl $ prod_encode (Suc (nat_of_fm p), 0)\<close>

fun rule_of_nat :: \<open>nat \<Rightarrow> rule\<close> where
  \<open>rule_of_nat n = (case sum_decode n of
    Inl n \<Rightarrow> (case prod_decode n of
      (0, 0) \<Rightarrow> FlsL
    | (0, Suc 0) \<Rightarrow> FlsR
    | (0, n2) \<Rightarrow> if n2 = idle_nat then Idle else
      let (p, q) = prod_decode n2 in ImpR (fm_of_nat p) (fm_of_nat q)
    | (Suc n, Suc ts) \<Rightarrow> Axiom n (map tm_of_nat (list_decode ts))
    | (Suc p, 0) \<Rightarrow> UniR (fm_of_nat p))
  | Inr n \<Rightarrow> (let (n1, n2) = prod_decode n in
    case sum_decode n1 of
      Inl n1 \<Rightarrow> (case sum_decode n2 of
        Inl q \<Rightarrow> ImpL (fm_of_nat n1) (fm_of_nat q)
      | Inr p \<Rightarrow> UniL (tm_of_nat n1) (fm_of_nat p))
    | Inr p \<Rightarrow> ImpR (fm_of_nat p) (fm_of_nat n2)))\<close>

lemma rule_nat: \<open>rule_of_nat (nat_of_rule r) = r\<close>
  using tm_nat fm_nat by (cases r) (simp_all add: map_idI idle_nat_def)

lemma surj_rule_of_nat: \<open>surj rule_of_nat\<close>
  unfolding surj_def using rule_nat by metis

end
