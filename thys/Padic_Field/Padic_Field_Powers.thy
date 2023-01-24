theory Padic_Field_Powers
  imports Ring_Powers Padic_Field_Polynomials Generated_Boolean_Algebra
          Padic_Field_Topology


begin

text\<open>This theory is intended to develop the necessary background on subsets of powers of a $p$-adic
field to prove Macintyre's quantifier elimination theorem. In particular, we define semi-algebraic
subsets of $\mathbb{Q}_p^n$, semi-algebraic functions $\mathbb{Q}_p^n \to \mathbb{Q}_p$, and semi-
algebraic mappings $\mathbb{Q}_p^n \to \mathbb{Q}_p^m$  for arbitrary $n, m \in \mathbb{N}$. In
addition we prove that many common sets and functions are semi-algebraic. We are closely following
the paper \<^cite>\<open>"denef1986"\<close> by Denef, where an algebraic proof of Mactinyre's theorem is developed.\<close>

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Cartesian Powers of $p$-adic Fields\<close>
(**************************************************************************************************)
(**************************************************************************************************)
lemma list_tl:
"tl (t#x) = x"
  using List.list.sel(3) by auto

lemma list_hd:
"hd (t#x) = t"
  unfolding List.list.sel(1) by auto


sublocale padic_fields <  cring_coord_rings Q\<^sub>p "UP Q\<^sub>p"
  unfolding  cring_coord_rings_axioms_def cring_coord_rings_def
  using Qp.zero_not_one UPQ.R_cring
  apply (simp add: UPQ.is_UP_cring)
  by auto

sublocale padic_fields < Qp: domain_coord_rings Q\<^sub>p "UP Q\<^sub>p"
  unfolding domain_coord_rings_def cring_coord_rings_axioms_def cring_coord_rings_def
  using Qp.domain_axioms Qp.zero_not_one UPQ.R_cring
  apply (simp add: UPQ.UP_cring_axioms)
  by auto

context padic_fields
begin
no_notation Zp.to_fun (infixl\<open>\<bullet>\<close> 70)
no_notation ideal_prod (infixl "\<cdot>\<index>" 80)

notation
evimage (infixr "\<inverse>\<index>" 90) and
euminus_set ("_ \<^sup>c\<index>" 70)


type_synonym padic_tuple = "padic_number list"
type_synonym padic_function = "padic_number \<Rightarrow> padic_number"
type_synonym padic_nary_function = "padic_tuple \<Rightarrow> padic_number"
type_synonym padic_function_tuple = "padic_nary_function list"
type_synonym padic_nary_function_poly = "nat \<Rightarrow> padic_nary_function"


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Polynomials over $\mathbb{Q}_p$ and Polynomial Maps\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma last_closed':
  assumes "x@[t] \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "t \<in> carrier  Q\<^sub>p"
  using assms last_closed[of n "x@[t]" Q\<^sub>p]
  by (metis (full_types) cartesian_power_car_memE gr0I last_snoc
      length_append_singleton less_not_refl zero_less_Suc)

lemma segment_in_car':
  assumes "x@[t] \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  shows "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
proof-
  have 0: "length x = n"
    by (metis Suc_inject assms cartesian_power_car_memE length_append_singleton)
  have  "set x \<subseteq> set (x@[t])"
    by (metis rotate1.simps(2) set_rotate1 set_subset_Cons)
  then have 1: "set x \<subseteq> carrier Q\<^sub>p"
    using assms cartesian_power_car_memE''[of "x@[t]" Q\<^sub>p "Suc n"]
    by blast
  show ?thesis
    using 0 1 assms cartesian_power_car_memI[of x n Q\<^sub>p]
    by blast
qed

lemma Qp_zero:
"Q\<^sub>p\<^bsup>0\<^esup> = nil_ring"
  unfolding cartesian_power_def
  by simp

lemma Qp_zero_carrier:
"carrier (Q\<^sub>p\<^bsup>0\<^esup>) = {[]}"
  by (simp add: Qp_zero)

text\<open>Abbreviation for constant polynomials\<close>

abbreviation(input) Qp_to_IP where
"Qp_to_IP k \<equiv> Qp.indexed_const k"

lemma Qp_to_IP_car:
  assumes "k \<in> carrier Q\<^sub>p"
  shows "Qp_to_IP k \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  using assms
  unfolding coord_ring_def
  using Qp.indexed_const_closed by blast

lemma(in cring_coord_rings) smult_closed:
  assumes "a \<in> carrier R"
  assumes "q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "a \<odot>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  using assms unfolding coord_ring_def
  using Pring_smult_closed
  by (simp add: R.Pring_smult_closed)


lemma Qp_poly_smult_cfs:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "(a \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> P) m = a \<otimes> (P m)"
  using assms unfolding coord_ring_def
  using Qp.Pring_smult_cfs by blast

lemma Qp_smult_r_distr:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "a \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (P \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> q) = (a \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> P)  \<oplus>\<^bsub> Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (a \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> q)"
  using assms unfolding coord_ring_def
  using Qp.Pring_smult_r_distr by blast

lemma Qp_smult_l_distr:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "(a \<oplus> b) \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> P = (a \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> P)  \<oplus>\<^bsub> Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (b \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> P)"
  using assms unfolding coord_ring_def
  using Qp.Pring_smult_l_distr by blast

abbreviation(input) Qp_funs  where
"Qp_funs n \<equiv> Fun\<^bsub>n\<^esub> Q\<^sub>p"


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Evaluation of Polynomials in $\mathbb{Q}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)


abbreviation(input) Qp_ev where
"Qp_ev P q \<equiv> (eval_at_point Q\<^sub>p q P)"

lemma Qp_ev_one:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_ev \<one>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> a = \<one>" unfolding coord_ring_def
  by (metis Qp.Pring_one eval_at_point_const Qp.one_closed assms)

lemma Qp_ev_zero:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_ev \<zero>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> a = \<zero>"unfolding coord_ring_def
  by (metis Qp.Pring_zero eval_at_point_const Qp.zero_closed assms)

lemma Qp_eval_pvar_pow:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "k < n"
  assumes "(m::nat) \<noteq> 0"
  shows "Qp_ev ((pvar Q\<^sub>p k)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> m) a = ((a!k)[^]m)"
  by (metis eval_at_point_nat_pow eval_pvar assms(1) assms(2) pvar_closed)

text\<open>composition of polynomials over $\mathbb{Q}_p$\<close>

definition Qp_poly_comp where
"Qp_poly_comp m fs = poly_compose (length fs) m fs"

text\<open>lemmas about polynomial maps\<close>

lemma Qp_is_poly_tupleI:
  assumes "\<And>i. i < length fs\<Longrightarrow> fs!i \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  shows "is_poly_tuple m fs"
  unfolding is_poly_tuple_def using assms
  using cartesian_power_car_memE'' cartesian_power_car_memI' by blast

lemma Qp_is_poly_tuple_append:
  assumes "is_poly_tuple m fs"
  assumes "is_poly_tuple m gs"
  shows "is_poly_tuple m (fs@gs)"
proof(rule Qp_is_poly_tupleI)
  show "\<And>i. i < length (fs @ gs) \<Longrightarrow> (fs @ gs) ! i \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  proof- fix i assume A: "i < length (fs @ gs)"
  show "(fs @ gs) ! i \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
    apply(cases "i < length fs")
    using assms is_poly_tupleE[of m fs i] nth_append[of fs gs i]
     apply presburger
  proof-
    assume B: "\<not> i < length fs"
    then have C: "length fs \<le> i \<and> i < length (fs @ gs)"
      using A  not_le
      by blast
    then have "i - length fs < length gs"
      using length_append[of fs gs]
      by linarith
    then show ?thesis
      using A assms is_poly_tupleE[of m gs "i - length fs"] nth_append[of fs gs i] B
      by presburger
  qed
  qed
qed

lemma Qp_poly_mapE:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "j < m"
  shows "(poly_map n fs as)!j \<in> carrier Q\<^sub>p"
  using assms  poly_map_closed cartesian_power_car_memE' by blast

lemma Qp_poly_mapE':
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "length (poly_map n fs as) = length fs"
  unfolding poly_map_def
  using Qp.cring_axioms poly_tuple_evalE'
  by (metis assms restrict_def)

lemma Qp_poly_mapE'':
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "n \<noteq> 0"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "j < m"
  shows "(poly_map n fs as)!j = (Qp_ev (fs!j) as)"
  using assms
  unfolding poly_map_def poly_tuple_eval_def
  by (metis (no_types, lifting) nth_map restrict_apply')

lemma poly_map_apply:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "poly_map n fs as = poly_tuple_eval fs as"
  unfolding poly_map_def restrict_def
  by (simp add: assms)

lemma poly_map_pullbackI:
  assumes "is_poly_tuple n fs"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "poly_map n fs as \<in> S"
  shows "as \<in> poly_map n fs \<inverse>\<^bsub>n\<^esub> S"
  using assms poly_map_apply
  by blast

lemma poly_map_pullbackI':
  assumes "is_poly_tuple n fs"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "poly_map n fs as \<in> S"
  shows "as \<in> ((poly_map n fs) -` S)"
  by (simp add: assms(3))

text\<open>lemmas about polynomial composition\<close>
lemma  poly_compose_ring_hom:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  shows  "(ring_hom_ring (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) (Q\<^sub>p[\<X>\<^bsub>m\<^esub>]) (Qp_poly_comp m fs))"
  unfolding Qp_poly_comp_def
  by (simp add: assms(1) assms(2)  poly_compose_ring_hom)

lemma poly_compose_closed:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "(Qp_poly_comp m fs f) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  using Qp.cring_axioms assms
  unfolding Qp_poly_comp_def
  using poly_compose_closed by blast


lemma poly_compose_add:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_poly_comp m fs (f \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> g) = (Qp_poly_comp m fs f) \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>m\<^esub>]\<^esub>  (Qp_poly_comp m fs g)"
  using Qp.cring_axioms assms poly_compose_add
  unfolding is_poly_tuple_def Qp_poly_comp_def
  by blast

lemma poly_compose_mult:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "Qp_poly_comp m fs (f \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> g) = (Qp_poly_comp m fs f) \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>m\<^esub>]\<^esub>  (Qp_poly_comp m fs g)"
  using Qp.cring_axioms assms poly_compose_mult
  unfolding is_poly_tuple_def Qp_poly_comp_def
  by blast

lemma poly_compose_const:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "Qp_poly_comp m fs (Qp_to_IP a) = Qp_to_IP a"
  using Qp.cring_axioms assms poly_compose_const
  unfolding is_poly_tuple_def Qp_poly_comp_def
  by metis

lemma Qp_poly_comp_eval:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "Qp_ev (Qp_poly_comp m fs f) as = Qp_ev f (poly_map m fs as)"
proof-
  have "(restrict (poly_tuple_eval fs) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) as) = poly_tuple_eval fs as"
    unfolding restrict_def
    by (simp add: assms)
  thus ?thesis
  using assms Qp.cring_axioms poly_compose_eval
  unfolding Qp_poly_comp_def poly_map_def
  by presburger
qed



(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Mapping Univariate Polynomials to Multivariable Polynomials in One Variable\<close>
(**************************************************************************************************)
(**************************************************************************************************)


abbreviation(input) to_Qp_x where
"to_Qp_x \<equiv> (IP_to_UP (0::nat) :: (nat multiset \<Rightarrow> padic_number) \<Rightarrow> nat \<Rightarrow> padic_number)"

abbreviation(input) from_Qp_x where
"from_Qp_x \<equiv> UP_to_IP Q\<^sub>p (0::nat)"

lemma from_Qp_x_closed:
  assumes "q \<in> carrier Q\<^sub>p_x"
  shows "from_Qp_x q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>])"
  using assms UP_to_IP_closed unfolding coord_ring_def
  by (metis One_nat_def lessThan_0 lessThan_Suc)

lemma to_Qp_x_closed:
  assumes "q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>])"
  shows "to_Qp_x q \<in> carrier Q\<^sub>p_x"
  using assms Qp.IP_to_UP_closed[of q "0::nat"] Qp.cring_axioms
  unfolding coord_ring_def
  by (metis One_nat_def lessThan_0 lessThan_Suc)

lemma to_Qp_x_from_Qp_x:
  assumes "q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>])"
  shows "from_Qp_x (to_Qp_x q) = q"
  using assms UP_to_IP_inv[of q "0::nat"] Qp.Pring_car
  unfolding coord_ring_def
    by (metis One_nat_def lessThan_0 lessThan_Suc)

lemma from_Qp_x_to_Qp_x:
  assumes "q \<in> carrier Q\<^sub>p_x"
  shows "to_Qp_x (from_Qp_x q) = q"
  by (meson UPQ.IP_to_UP_inv assms)

text\<open>ring hom properties of these maps\<close>

lemma to_Qp_x_ring_hom:
"to_Qp_x \<in> ring_hom (Q\<^sub>p[\<X>\<^bsub>1\<^esub>]) Q\<^sub>p_x"
  using IP_to_UP_ring_hom[of "0::nat"] ring_hom_ring.homh
  unfolding coord_ring_def
    by (metis One_nat_def lessThan_0 lessThan_Suc)

lemma from_Qp_x_ring_hom:
"from_Qp_x \<in> ring_hom Q\<^sub>p_x (Q\<^sub>p[\<X>\<^bsub>1\<^esub>])"
  using  UP_to_IP_ring_hom ring_hom_ring.homh
  unfolding coord_ring_def
    by (metis One_nat_def lessThan_0 lessThan_Suc)


lemma from_Qp_x_add:
  assumes "a \<in> carrier Q\<^sub>p_x"
  assumes "b \<in> carrier Q\<^sub>p_x"
  shows "from_Qp_x (a \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> b) = from_Qp_x a \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>1\<^esub>]\<^esub> from_Qp_x b"
  by (metis (mono_tags, lifting) assms(1) assms(2) from_Qp_x_ring_hom ring_hom_add)

lemma from_Qp_x_mult:
  assumes "a \<in> carrier Q\<^sub>p_x"
  assumes "b \<in> carrier Q\<^sub>p_x"
  shows "from_Qp_x (a \<otimes>\<^bsub>Q\<^sub>p_x\<^esub> b) = from_Qp_x a \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>1\<^esub>]\<^esub> from_Qp_x b"
  by (metis assms(1) assms(2) from_Qp_x_ring_hom ring_hom_mult)

text\<open>equivalence of evaluation maps\<close>

lemma Qp_poly_Qp_x_eval:
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>])"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
  shows "Qp_ev P a = (to_Qp_x P)\<bullet>(Qp.to_R a)"
proof-
  have 0: "(IP_to_UP 0 P) \<bullet> (a ! 0) = ((IP_to_UP 0 P) \<bullet> (if 0 < length a then a ! 0 else \<zero>))"
    using assms
    by (metis (mono_tags, lifting) cartesian_power_car_memE gr0I zero_neq_one)
  have 1: "closed_fun Q\<^sub>p (\<lambda>n. if n < length a then a ! n else \<zero>)"
  proof
    fix n
    show "(if n < length a then a ! n else \<zero>) \<in> carrier Q\<^sub>p"
      apply(cases "n < length a")
      using assms
      apply (metis cartesian_power_car_memE cartesian_power_car_memE')
      by (meson Qp.cring_axioms cring.cring_simprules(2))
  qed
  have 2: " P \<in> Pring_set Q\<^sub>p {0::nat}"
    using assms unfolding coord_ring_def
   by (metis Qp.Pring_car UPQ.UP_to_IP_closed assms(1) to_Qp_x_closed to_Qp_x_from_Qp_x)
  have 3: "total_eval Q\<^sub>p (\<lambda>i. if i < length a then a ! i else \<zero>) P = IP_to_UP 0 P \<bullet> (if 0 < length a then a ! 0 else \<zero>)"
    using 1 2 assms IP_to_UP_poly_eval[of P "0::nat" "(\<lambda>i. if i < length a then a ! i else \<zero>)" ]
          UPQ.to_fun_def by presburger
  then show ?thesis
    using 0
    unfolding eval_at_point_def
    by blast
qed

lemma Qp_x_Qp_poly_eval:
  assumes "P \<in> carrier Q\<^sub>p_x"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "P \<bullet> a = Qp_ev (from_Qp_x P) (to_R1 a)"
proof-
  have "Qp_ev (from_Qp_x P) (to_R1 a) = (to_Qp_x (from_Qp_x P))\<bullet>(Qp.to_R (Qp.to_R1 a))"
    using Qp_poly_Qp_x_eval assms(1) assms(2) from_Qp_x_closed Qp.to_R1_closed by blast
  then show ?thesis using assms
    by (metis UPQ.IP_to_UP_inv Qp.to_R_to_R1)
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>$n^{th}$-Power Sets over $\mathbb{Q}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition P_set where
"P_set (n::nat) = {a \<in> nonzero Q\<^sub>p.  (\<exists>y \<in> carrier Q\<^sub>p . (y[^] n) = a)}"

lemma P_set_carrier:
"P_set n \<subseteq> carrier Q\<^sub>p"
  unfolding P_set_def nonzero_def
  by blast

lemma P_set_memI:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "b[^](n::nat) = a"
  shows "a \<in> P_set n"
  unfolding P_set_def
  using assms
  by (metis (mono_tags, lifting) mem_Collect_eq not_nonzero_Qp)

lemma P_set_nonzero:
"P_set n \<subseteq> nonzero Q\<^sub>p"
  unfolding P_set_def by blast


lemma P_set_nonzero':
  assumes "a \<in> P_set n"
  shows "a \<in> nonzero Q\<^sub>p"
        "a \<in> carrier  Q\<^sub>p"
  using assms P_set_nonzero P_set_carrier
   apply blast using assms P_set_carrier  by blast

lemma P_set_one:
  assumes "n \<noteq> 0"
  shows "\<one> \<in> P_set (n::nat)"
proof-
  have 0: "\<one>[^]n = \<one>"
    using Qp.nat_pow_one by blast
  have 1: "\<one> \<in> carrier Q\<^sub>p"
    by blast
  then show ?thesis
    using one_nonzero unfolding P_set_def
    using 0 by blast
qed

lemma zeroth_P_set:
"P_set 0 = {\<one>}"
proof
  show "P_set 0 \<subseteq> {\<one>}"
  unfolding P_set_def
  proof
    fix x
    assume "x \<in> {a \<in> nonzero Q\<^sub>p. \<exists>y\<in>carrier Q\<^sub>p. (y[^](0::nat)) = a}"
    then have "\<exists>y\<in>carrier Q\<^sub>p. (y[^](0::nat)) = x"
      by blast
    then obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> (a[^](0::nat)) = x"
      by blast
    then show "x \<in> {\<one>}"
      using Qp.nat_pow_0 by blast
  qed
  show "{\<one>} \<subseteq> P_set 0"
    using P_set_memI[of \<one> \<one> 0] Qp.nat_pow_one Qp.one_closed local.one_neq_zero
    by blast
qed

lemma P_set_mult_closed:
  assumes "n \<noteq> 0"
  assumes "a \<in> P_set n"
  assumes "b \<in> P_set n"
  shows "a \<otimes> b \<in> P_set n"
proof-
  obtain a0 where a0_def: "a0 \<in> carrier Q\<^sub>p \<and> (a0 [^] n = a)"
    using assms(2)
    unfolding P_set_def
    by blast
  obtain b0 where b0_def: "b0 \<in> carrier Q\<^sub>p \<and> (b0 [^] n = b)"
    using assms(3)
    unfolding P_set_def
    by blast
  have "(a0 \<otimes> b0) [^] n = a0 [^] n \<otimes> b0 [^] n"
    using a0_def b0_def Qp.nat_pow_distrib by blast
  then have 0: "a \<otimes> b  = (a0 \<otimes> b0) [^] n"
    using a0_def b0_def by blast
  have 1: "a0 \<otimes> b0 \<in> carrier Q\<^sub>p"
    by (meson Qp.cring_axioms a0_def b0_def cring.cring_simprules(5))
  have 2: "a \<otimes> b \<in> nonzero Q\<^sub>p"
    using assms nonzero_is_submonoid  unfolding P_set_def
    by (metis (no_types, lifting) "0" "1" Qp.integral Qp_nat_pow_nonzero a0_def b0_def mem_Collect_eq not_nonzero_Qp)
  then show ?thesis
    using 0 1 assms
    unfolding P_set_def by blast
qed

lemma P_set_inv_closed:
  assumes "a \<in> P_set n"
  shows "inv a \<in> P_set n"
proof(cases "n = 0")
  case True
  then show ?thesis
    using assms zeroth_P_set
    by (metis Qp.inv_one singletonD)
next
  case False
  then show ?thesis proof-
    obtain a0 where a0_def: "a0 \<in> carrier Q\<^sub>p \<and> a0[^]n = a"
      using assms P_set_def[of n] by blast
  have "a0 \<in> nonzero Q\<^sub>p"
    apply(rule ccontr)
  proof-
    assume "a0 \<notin> nonzero Q\<^sub>p "
    then have "a0 = \<zero>"
      using a0_def
      by (meson not_nonzero_Qp)
    then show False using a0_def assms
      by (metis (mono_tags, lifting) False P_set_def Qp.cring_axioms \<open>a0 \<notin> nonzero Q\<^sub>p\<close>
          cring_def mem_Collect_eq neq0_conv ring.pow_zero)
  qed
  then have "(inv a0)[^]n = inv a"
    using a0_def  \<open>a0 \<in> carrier Q\<^sub>p \<and> (a0[^]n) = a\<close> \<open>a0 \<in> nonzero Q\<^sub>p\<close> Units_nonzero
          monoid.nat_pow_of_inv[of Q\<^sub>p a n] Qp.nat_pow_of_inv Units_eq_nonzero by presburger
  then show ?thesis
    by (metis P_set_memI Qp.nat_pow_closed Qp.nonzero_memE(2) Qp.nonzero_pow_nonzero \<open>a0 \<in> nonzero Q\<^sub>p\<close> a0_def inv_in_frac(1) inv_in_frac(2))
  qed
qed

lemma P_set_val:
  assumes "a \<in> P_set (n::nat)"
  shows  "(ord a) mod n = 0"
proof(cases "n = 0")
  case True
  then show ?thesis
    using assms zeroth_P_set
    by (metis mod_by_0 of_nat_0 ord_one singletonD)
next
  case False
  then show ?thesis
  proof-
    obtain b where b_def: "b \<in> carrier Q\<^sub>p \<and> (b[^] n) = a"
      using assms P_set_def  by blast
    have an: "a \<in> nonzero Q\<^sub>p"
      using P_set_def assms by blast
    have bn: "b \<in> nonzero Q\<^sub>p"
    proof(rule ccontr)
      assume "b \<notin> nonzero Q\<^sub>p"
      then have "b = \<zero>\<^bsub> Q\<^sub>p\<^esub>"
        using b_def not_nonzero_Qp
        by metis
      then have "(b[^] n) = \<zero>"
        using False Qp.cring_axioms cring_def ring.pow_zero
        by blast
      then show False
        using b_def an  Qp.not_nonzero_memI by blast
    qed
    then have "ord a = n * (ord b)"
      using b_def an nonzero_nat_pow_ord
      by blast
    then show ?thesis
      by (metis mod_mult_self1_is_0)
  qed
qed


lemma P_set_pow:
  assumes "n > 0"
  assumes "s \<in> P_set n"
  shows "s[^]k \<in> P_set (n*k)"
proof-
  obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> y[^]n = s"
    using assms unfolding P_set_def by blast
  then have 0: "y \<in> nonzero Q\<^sub>p"
    using assms P_set_nonzero'(1) Qp_nonzero_nat_pow by blast
  have 1: "y[^](n*k) = s[^] k"
    using 0 y_def assms Qp.nat_pow_pow by blast
  hence 2: "s[^]k \<in> nonzero Q\<^sub>p"
    using 0 by (metis Qp_nat_pow_nonzero)
  thus ?thesis unfolding P_set_def using 1 y_def by blast
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Semialgebraic Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  In this section we introduce the notion of a $p$-adic semialgebraic set. Intuitively, these are
  the subsets of $\mathbb{Q}_p^n$ which are definable by first order quantifier-free formulas in
  the standard first-order language of rings, with an additional relation symbol included for the
  relation $\text{ val}(x) \leq \text{ val}(y)$, interpreted according to the definiton of the
  $p$-adic valuation on $\mathbb{Q}_p$. In fact, by Macintyre's quantifier elimination theorem
  for the first-order theory of $\mathbb{Q}_p$ in this language, one can equivalently remove the
  ``quantifier-free" clause from the latter definition. The definition we give here is also
  equivalent, and due to Denef in \<^cite>\<open>"denef1986"\<close>. The given definition here is desirable mainly
  for its utility in producing a proof of Macintyre's theorem, which is our overarching goal.
\<close>
      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Defining Semialgebraic Sets\<close>
      (********************************************************************************************)
      (********************************************************************************************)

definition basic_semialg_set where
"basic_semialg_set (m::nat) (n::nat) P = {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists>y \<in> carrier Q\<^sub>p. Qp_ev P q = (y[^]n)}"

lemma basic_semialg_set_zero_set:
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  assumes "q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "Qp_ev P q = \<zero>"
  assumes "n \<noteq>  0"
  shows "q \<in> basic_semialg_set (m::nat) (n::nat) P"
proof-
  have "\<zero> = (\<zero>[^]n)"
    using assms(4) Qp.nat_pow_zero by blast
  then show ?thesis
    unfolding basic_semialg_set_def
    using assms Qp.cring_axioms cring.cring_simprules(2)
    by blast
qed

lemma basic_semialg_set_def':
  assumes "n \<noteq> 0"
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  shows "basic_semialg_set (m::nat) (n::nat) P = {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> (P_set n)}"
proof
  show "basic_semialg_set m n P \<subseteq> {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> P_set n}"
  proof
    fix x
    assume A: "x \<in> basic_semialg_set m n P"
     show "x \<in> {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> P_set n}"
      apply(cases "Qp_ev P x = \<zero>")
      using A basic_semialg_set_def apply blast
      unfolding basic_semialg_set_def P_set_def
    proof
      assume A0: "Qp_ev P x \<noteq> \<zero>"
      have A1: " \<exists>y\<in>carrier Q\<^sub>p. Qp_ev P x = (y[^]n)"
        using A basic_semialg_set_def
        by blast
      have A2: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A basic_semialg_set_def
        by blast
      show " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> (Qp_ev P x = \<zero> \<or> Qp_ev P x \<in> {a \<in> nonzero Q\<^sub>p. \<exists>y\<in>carrier Q\<^sub>p. (y[^]n) = a})"
        by (metis (mono_tags, lifting) A1 A2 Qp.nonzero_memI assms(2) eval_at_point_closed mem_Collect_eq)
    qed
  qed
  show "{q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> P_set n} \<subseteq> basic_semialg_set m n P"
  proof
    fix x
    assume A: " x \<in> {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> P_set n}"
    then have A':"x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      by blast
    show "x \<in>  basic_semialg_set m n P"
      using A A'
      apply(cases "Qp_ev P x = \<zero>")
      using assms basic_semialg_set_zero_set[of P m x n]
       apply blast
    proof-
      assume B: "x \<in> {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> P_set n} "
      assume B': "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      assume B'': "Qp_ev P x \<noteq> \<zero> "
      show "x \<in> basic_semialg_set m n P"
        unfolding basic_semialg_set_def  P_set_def
      proof
        have "\<exists>y\<in>carrier Q\<^sub>p. Qp_ev P x = (y[^]n) "
          using A nonzero_def [of Q\<^sub>p] unfolding P_set_def
        proof -
          assume "x \<in> {q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). Qp_ev P q = \<zero> \<or> Qp_ev P q \<in> {a \<in> nonzero Q\<^sub>p. \<exists>y\<in>carrier Q\<^sub>p. (y[^]n) = a}}"
          then have "Qp_ev P x \<in> nonzero Q\<^sub>p \<and> (\<exists>r. r \<in> carrier Q\<^sub>p \<and> (r[^]n) = Qp_ev P x)"
            using B'' by blast
          then show ?thesis
            by blast
        qed
        then show "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> (\<exists>y\<in>carrier Q\<^sub>p. Qp_ev P x = (y[^]n))"
          using B'
          by blast
      qed
    qed
  qed
qed

lemma basic_semialg_set_memI:
  assumes "q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "Qp_ev P q = (y[^]n)"
  shows "q \<in> basic_semialg_set m n P"
  using assms(1) assms(2) assms(3) basic_semialg_set_def
  by blast

lemma basic_semialg_set_memE:
  assumes  "q \<in> basic_semialg_set m n P"
  shows "q \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        "\<exists>y \<in> carrier Q\<^sub>p. Qp_ev P q = (y[^]n)"
  using assms basic_semialg_set_def apply blast
  using assms basic_semialg_set_def by blast

definition is_basic_semialg :: "nat \<Rightarrow> ((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list set \<Rightarrow> bool" where
"is_basic_semialg m S \<equiv> (\<exists> (n::nat) \<noteq> 0. (\<exists> P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>]). S = basic_semialg_set m n P))"

abbreviation(input) basic_semialgs where
"basic_semialgs m \<equiv> {S. (is_basic_semialg m S)}"

definition semialg_sets where
"semialg_sets n = gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n)"

lemma carrier_is_semialg:
"(carrier (Q\<^sub>p\<^bsup>n\<^esup>)) \<in> semialg_sets n "
  unfolding semialg_sets_def
  using gen_boolean_algebra.universe by blast

lemma empty_set_is_semialg:
" {} \<in> semialg_sets n"
  using carrier_is_semialg[of n]
  unfolding semialg_sets_def using gen_boolean_algebra.complement
  by (metis Diff_cancel)

lemma semialg_intersect:
  assumes "A \<in> semialg_sets n"
  assumes "B \<in> semialg_sets n"
  shows "(A \<inter> B) \<in> semialg_sets n "
  using assms(1) assms(2) gen_boolean_algebra_intersect semialg_sets_def
  by blast

lemma semialg_union:
  assumes "A \<in> semialg_sets n"
  assumes "B \<in> semialg_sets n"
  shows "(A \<union> B) \<in> semialg_sets n "
  using assms gen_boolean_algebra.union semialg_sets_def
  by blast

lemma semialg_complement:
  assumes "A \<in> semialg_sets n"
  shows "(carrier (Q\<^sub>p\<^bsup>n\<^esup>) - A) \<in> semialg_sets n "
  using assms gen_boolean_algebra.complement semialg_sets_def
  by blast

lemma semialg_zero:
  assumes "A \<in> semialg_sets 0"
  shows "A = {[]} \<or> A = {}"
  using assms
  unfolding semialg_sets_def cartesian_power_def
proof-
  assume A0:  " A \<in> gen_boolean_algebra (carrier (RDirProd_list (R_list 0 Q\<^sub>p))) (basic_semialgs 0)"
  show " A = {[]} \<or> A = {}"
  proof-
    have "A \<noteq> {[]} \<longrightarrow> A = {}"
    proof
      assume A1: "A \<noteq> {[]}"
      show "A = {}"
      proof-
        have "(R_list 0 Q\<^sub>p) = []"
          by simp
        then have "(carrier (RDirProd_list (R_list 0 Q\<^sub>p))) = {[]}"
          using RDirProd_list_nil
          by simp
        then show ?thesis
          using A0 A1
          by (metis gen_boolean_algebra_subset subset_singletonD)
      qed
    qed
    then show ?thesis
      by linarith
  qed
qed

lemma basic_semialg_is_semialg:
  assumes "is_basic_semialg n A"
  shows "A \<in> semialg_sets n"
  by (metis (no_types, lifting) assms gen_boolean_algebra.simps inf_absorb1
      is_basic_semialg_def mem_Collect_eq basic_semialg_set_def
      semialg_sets_def subsetI)

lemma basic_semialg_is_semialg':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "m \<noteq>0"
  assumes "A = basic_semialg_set n m f"
  shows "A \<in> semialg_sets n"
  using assms basic_semialg_is_semialg is_basic_semialg_def
  by blast

definition is_semialgebraic where
"is_semialgebraic n S = (S \<in> semialg_sets n)"

lemma is_semialgebraicE:
  assumes "is_semialgebraic n S"
  shows "S \<in> semialg_sets n"
  using assms is_semialgebraic_def by blast

lemma is_semialgebraic_closed:
  assumes "is_semialgebraic n S"
  shows "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  using is_semialgebraicE[of n S] unfolding semialg_sets_def
  using assms gen_boolean_algebra_subset is_semialgebraicE semialg_sets_def
  by blast

lemma is_semialgebraicI:
  assumes "S \<in> semialg_sets n"
  shows "is_semialgebraic n S"
  by (simp add: assms is_semialgebraic_def)

lemma basic_semialg_is_semialgebraic:
  assumes "is_basic_semialg n A"
  shows "is_semialgebraic n A"
  using assms basic_semialg_is_semialg is_semialgebraicI by blast

lemma basic_semialg_is_semialgebraic':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "m \<noteq>0"
  assumes "A = basic_semialg_set n m f"
  shows "is_semialgebraic n A"
  using assms(1) assms(2) assms(3) basic_semialg_is_semialg' is_semialgebraicI by blast


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Algebraic Sets over $p$-adic Fields\<close>
      (********************************************************************************************)
      (********************************************************************************************)

lemma p_times_square_not_square:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "\<pp> \<otimes> (a [^] (2::nat)) \<notin> P_set (2::nat)"
proof
  assume A: "\<pp> \<otimes> (a[^](2::nat)) \<in> P_set (2::nat)"
  then have "\<pp> \<otimes> (a[^](2::nat)) \<in> nonzero Q\<^sub>p"
    unfolding P_set_def
    by blast
  then obtain b where b_def: "b \<in> carrier Q\<^sub>p \<and> b[^](2::nat) = \<pp> \<otimes> (a[^](2::nat))"
    using A P_set_def by blast
   have "b \<in> nonzero Q\<^sub>p"
     apply(rule ccontr) using b_def assms
     by (metis A P_set_nonzero'(1) Qp.nat_pow_zero not_nonzero_Qp zero_neq_numeral)
   then have LHS: "ord (b[^](2::nat)) = 2* (ord b)"
     using nonzero_nat_pow_ord
     by presburger
   have "ord( \<pp> \<otimes> (a[^](2::nat))) = 1 + 2* ord a"
     using assms nonzero_nat_pow_ord Qp_nat_pow_nonzero ord_mult ord_p p_nonzero
     by presburger
   then show False
     using b_def LHS
     by presburger
qed

lemma p_times_square_not_square':
  assumes "a \<in> carrier Q\<^sub>p"
  shows "\<pp> \<otimes> (a [^] (2::nat)) = \<zero> \<Longrightarrow> a = \<zero>"
  by (metis Qp.integral Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_memE(2) Qp.nonzero_pow_nonzero assms p_nonzero)

lemma zero_set_semialg_set:
  assumes "q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "Qp_ev q a = \<zero> \<longleftrightarrow>( \<exists>y \<in> carrier Q\<^sub>p. \<pp> \<otimes> ((Qp_ev q a) [^] (2::nat)) = y[^](2::nat)) "
proof
  show "Qp_ev q a = \<zero> \<Longrightarrow> \<exists>y\<in>carrier Q\<^sub>p. \<pp> \<otimes> (Qp_ev q a[^] (2::nat)) = (y[^] (2::nat))"
  proof-
    assume "Qp_ev q a = \<zero>"
    then have "\<pp> \<otimes> (Qp_ev q a[^](2::nat)) = (\<zero>[^](2::nat))"
      by (metis Qp.int_inc_closed Qp.nat_pow_zero Qp.r_null zero_neq_numeral)
    then have "\<zero> \<in> carrier Q\<^sub>p \<and> \<pp> \<otimes> (Qp_ev q a[^](2::nat)) = (\<zero>[^](2::nat))"
      using Qp.cring_axioms cring.cring_simprules(2)
      by blast
    then show "\<exists>y\<in>carrier Q\<^sub>p. \<pp> \<otimes> (Qp_ev q a[^] (2::nat)) = (y[^] (2::nat))"
      by blast
  qed
  show " \<exists>y\<in>carrier Q\<^sub>p. \<pp> \<otimes> (Qp_ev q a[^](2::nat)) = (y[^](2::nat)) \<Longrightarrow> Qp_ev q a = \<zero>"
  proof-
    assume A: " \<exists>y\<in>carrier Q\<^sub>p. \<pp> \<otimes> (Qp_ev q a[^](2::nat)) = (y[^](2::nat))"
    then obtain b where b_def: "b\<in>carrier Q\<^sub>p \<and> \<pp> \<otimes> (Qp_ev q a[^](2::nat)) = (b[^](2::nat))"
      by blast
    show "Qp_ev q a = \<zero>"
    proof(rule ccontr)
      assume " Qp_ev q a \<noteq> \<zero>"
      then have " Qp_ev q a \<in> nonzero Q\<^sub>p" using assms eval_at_point_closed[of a n q]  nonzero_def
      proof -
        have "Qp_ev q a \<in> carrier Q\<^sub>p"
          using \<open>\<lbrakk>a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>); q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])\<rbrakk> \<Longrightarrow>
                  Qp_ev q a \<in> carrier Q\<^sub>p\<close> \<open>a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)\<close> \<open>q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])\<close>
          by fastforce
        then have "Qp_ev q a \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>}"
          using \<open>Qp_ev q a \<noteq> \<zero>\<close> by force
        then show ?thesis
          by (metis nonzero_def )
      qed
      then have "\<pp> \<otimes> (Qp_ev q a[^](2::nat)) \<in> nonzero Q\<^sub>p"
        by (metis Qp.nonzero_closed Qp.nonzero_mult_closed Qp_nat_pow_nonzero not_nonzero_Qp p_nonzero p_times_square_not_square')
      then have "\<pp> \<otimes> (Qp_ev q a[^](2::nat)) \<in> P_set (2::nat)"
        using b_def
        unfolding P_set_def
        by blast
      then show False
        using \<open>Qp_ev q a \<in> nonzero Q\<^sub>p\<close> p_times_square_not_square
        by blast
    qed
  qed
qed

lemma alg_as_semialg:
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "q = \<pp> \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (P[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (2::nat))"
  shows "zero_set Q\<^sub>p n P = basic_semialg_set n (2::nat) q"
proof
  have 00: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> Qp_ev q x = \<pp> \<otimes> (Qp_ev P x) [^] (2::nat)"
    using assms eval_at_point_smult MP.nat_pow_closed Qp.int_inc_closed eval_at_point_nat_pow
    by presburger
  show "V\<^bsub>Q\<^sub>p\<^esub> n P \<subseteq> basic_semialg_set n 2 q"
  proof
    fix x
    assume A: "x \<in> V\<^bsub>Q\<^sub>p\<^esub> n P "
    show "x \<in> basic_semialg_set n (2::nat) q "
    proof-
      have P: "Qp_ev P x = \<zero>"
        using A zero_setE(2)
        by blast
      have "Qp_ev q x = \<zero>"
      proof-
        have "Qp_ev q x = \<pp> \<otimes> (Qp_ev (P[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (2::nat)) x)"
          using assms eval_at_point_smult[of x n "(P[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (2::nat))" \<pp>] basic_semialg_set_def
          by (meson A MP.nat_pow_closed Qp.int_inc_closed zero_setE(1))
        then show ?thesis
          by (metis A P Qp.int_inc_closed Qp.integral_iff Qp.nat_pow_zero Qp.zero_closed assms(1)
              eval_at_point_nat_pow neq0_conv zero_less_numeral zero_setE(1))
      qed
      then have 0: "Qp_ev q x = \<zero> \<or> Qp_ev q x \<in> P_set (2::nat)"
        by blast
      have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        using A zero_setE(1)
        by blast
      then show ?thesis using 0 basic_semialg_set_def'
        by (metis (no_types, opaque_lifting) Qp.nat_pow_zero Qp.zero_closed
            \<open>eval_at_point Q\<^sub>p x q = \<zero>\<close> basic_semialg_set_memI zero_neq_numeral)
    qed
  qed
  show "basic_semialg_set n 2 q \<subseteq> V\<^bsub>Q\<^sub>p\<^esub> n P"
  proof
    fix x
    assume A: "x \<in> basic_semialg_set n 2 q"
    have 0: "\<not> Qp_ev q x \<in> P_set 2"
    proof
      assume "Qp_ev q x \<in> P_set 2"
      then have 0: "Qp_ev q x \<in> nonzero Q\<^sub>p \<and>  (\<exists>y \<in> carrier Q\<^sub>p . (y[^] (2::nat)) = Qp_ev q x)"
        using P_set_def by blast
      have "( \<exists>y \<in> carrier Q\<^sub>p. \<pp> \<otimes> ((Qp_ev P x) [^] (2::nat)) = y[^](2::nat))"
      proof-
        obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> (y[^] (2::nat)) = Qp_ev q x"
          using 0 by blast
        have "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
          using A basic_semialg_set_memE(1) by blast
        then have "Qp_ev q x = \<pp> \<otimes> ((Qp_ev P x) [^] (2::nat))"
          using assms eval_at_point_scalar_mult 00 by blast
        then have "(y[^] (2::nat)) = \<pp> \<otimes> ((Qp_ev P x) [^] (2::nat))"
          using y_def by blast
        then show ?thesis using y_def by blast
      qed
      then have "Qp_ev P x = \<zero>"
        by (metis (no_types, lifting) A assms(1) basic_semialg_set_def mem_Collect_eq zero_set_semialg_set)
      then have "Qp_ev q x = \<zero>"
        using assms eval_at_point_smult
        by (metis "00" A Qp.int_inc_closed Qp.nat_pow_zero Qp.r_null basic_semialg_set_memE(1) zero_neq_numeral)
      then show False
        using 0 Qp.not_nonzero_memI by blast
    qed
    show " x \<in> V\<^bsub>Q\<^sub>p\<^esub> n P"
      apply(rule zero_setI)
      using A basic_semialg_set_memE(1) apply blast
      using A 0 00[of x]
      by (metis assms(1) basic_semialg_set_memE(1) basic_semialg_set_memE(2) zero_set_semialg_set)
  qed
qed

lemma is_zero_set_imp_basic_semialg:
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "S = zero_set Q\<^sub>p n P"
  shows "is_basic_semialg n S"
  unfolding is_basic_semialg_def
proof-
  obtain q where q_def: "q = \<pp> \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (P[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (2::nat))"
    by blast
  have 0: "zero_set Q\<^sub>p n P = basic_semialg_set n (2::nat) q"
    using alg_as_semialg[of P n q]  q_def assms(1) by linarith
  have "(P [^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (2::nat)) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
    using assms(1)
    by blast
  then have "\<pp> \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub>(P [^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (2::nat)) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
    using assms q_def Qp.int_inc_closed local.smult_closed by blast
  then have 1: "q \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
    by (metis q_def )
  then show "\<exists>m. m \<noteq> 0 \<and> (\<exists>P\<in>carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]). S = basic_semialg_set n m P)"
    using 0 assms
    by (metis zero_neq_numeral)
qed

lemma is_zero_set_imp_semialg:
  assumes "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "S = zero_set Q\<^sub>p n P"
  shows "is_semialgebraic n S"
  using assms(1) assms(2) basic_semialg_is_semialg is_semialgebraicI is_zero_set_imp_basic_semialg
  by blast

text\<open>Algebraic sets are semialgebraic\<close>

lemma is_algebraic_imp_is_semialg:
  assumes "is_algebraic Q\<^sub>p n S"
  shows "is_semialgebraic n S"
  proof(rule is_semialgebraicI)
    obtain ps where ps_def: "finite ps \<and> ps \<subseteq> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> S =  affine_alg_set Q\<^sub>p n ps"
      using is_algebraicE
      by (metis  assms)
    have "ps \<subseteq> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<longrightarrow> affine_alg_set Q\<^sub>p n ps \<in> semialg_sets n"
      apply(rule finite.induct[of ps])
        apply (simp add: ps_def)
      using affine_alg_set_empty[of n]
       apply (simp add: carrier_is_semialg)
    proof
      fix A a
      assume IH: "A \<subseteq> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<longrightarrow> affine_alg_set Q\<^sub>p n A \<in> semialg_sets n"
      assume P: "insert a A \<subseteq> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
      have "A \<subseteq> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
        using P by blast
      then
      show "affine_alg_set Q\<^sub>p n (insert a A) \<in> semialg_sets n"
        using IH P semialg_intersect[of "affine_alg_set Q\<^sub>p n A" n "affine_alg_set Q\<^sub>p n {a}" ]
               is_zero_set_imp_semialg affine_alg_set_insert[of n a A]
        by (metis Int_commute affine_alg_set_singleton insert_subset is_semialgebraicE)
    qed
    then show "S \<in> semialg_sets n"
      using ps_def by blast
  qed


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Basic Lemmas about the Semialgebraic Predicate\<close>
      (********************************************************************************************)
      (********************************************************************************************)


text\<open>Finite and cofinite sets are semialgebraic\<close>

lemma finite_is_semialg:
  assumes "F \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "finite F"
  shows "is_semialgebraic n F"
  using Qp.finite_sets_are_algebraic is_algebraic_imp_is_semialg[of n F]
           assms(1) assms(2)
  by blast

definition is_cofinite where
"is_cofinite n F = finite (ring_pow_comp Q\<^sub>p n F)"

lemma is_cofiniteE:
  assumes "F \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "is_cofinite n F"
  shows "finite (carrier (Q\<^sub>p\<^bsup>n\<^esup>) - F)"
  using assms(2) is_cofinite_def
  by (simp add: ring_pow_comp_def)

lemma complement_is_semialg:
  assumes "is_semialgebraic n F"
  shows "is_semialgebraic n ((carrier (Q\<^sub>p\<^bsup>n\<^esup>)) - F)"
  using assms is_semialgebraic_def semialg_complement by blast

lemma cofinite_is_semialgebraic:
  assumes "F \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "is_cofinite n F"
  shows "is_semialgebraic n F"
  using assms ring_pow_comp_inv[of F Q\<^sub>p n] complement_is_semialg[of n "(carrier (Q\<^sub>p\<^bsup>n\<^esup>) - F)"]
        finite_is_semialg[of "(carrier (Q\<^sub>p\<^bsup>n\<^esup>) - F)"]  is_cofiniteE[of F]
  by (simp add: ring_pow_comp_def)

lemma diff_is_semialgebraic:
  assumes "is_semialgebraic n A"
  assumes "is_semialgebraic n B"
  shows "is_semialgebraic n (A - B)"
  apply(rule is_semialgebraicI)
  using assms unfolding semialg_sets_def
  using gen_boolean_algebra_diff is_semialgebraicE semialg_sets_def
  by blast

lemma intersection_is_semialg:
  assumes "is_semialgebraic n A"
  assumes "is_semialgebraic n B"
  shows "is_semialgebraic n (A \<inter> B)"
  using assms(1) assms(2) is_semialgebraicE is_semialgebraicI semialg_intersect
  by blast

lemma union_is_semialgebraic:
  assumes "is_semialgebraic n A"
  assumes "is_semialgebraic n B"
  shows "is_semialgebraic n (A \<union> B)"
  using assms(1) assms(2) is_semialgebraicE is_semialgebraicI semialg_union by blast

lemma carrier_is_semialgebraic:
"is_semialgebraic n (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
using carrier_is_semialg
  by (simp add: carrier_is_semialg is_semialgebraic_def)

lemma empty_is_semialgebraic:
"is_semialgebraic n {}"
  by (simp add: empty_set_is_semialg is_semialgebraic_def)


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>One-Dimensional Semialgebraic Sets\<close>
      (********************************************************************************************)
      (********************************************************************************************)

definition one_var_semialg where
"one_var_semialg S =  ((to_R1 ` S) \<in> (semialg_sets 1))"

definition univ_basic_semialg_set where
"univ_basic_semialg_set (m::nat) P = {a \<in> carrier Q\<^sub>p. (\<exists>y \<in> carrier Q\<^sub>p. (P \<bullet> a = (y[^]m)))}"

text\<open>Equivalence of univ\_basic\_semialg\_sets and semialgebraic subsets of $\mathbb{Q}^1$ \<close>

lemma univ_basic_semialg_set_to_semialg_set:
  assumes "P \<in> carrier Q\<^sub>p_x"
  assumes "m \<noteq> 0"
  shows "to_R1 ` (univ_basic_semialg_set m P) = basic_semialg_set 1 m (from_Qp_x P)"
proof
  show "(\<lambda>a. [a]) ` univ_basic_semialg_set m P \<subseteq> basic_semialg_set 1 m (from_Qp_x P)"
  proof fix x
    assume A: "x \<in> (\<lambda>a. [a]) ` univ_basic_semialg_set m P"
    then obtain b y where by_def:"b \<in> carrier Q\<^sub>p \<and> y \<in> carrier Q\<^sub>p \<and> (P \<bullet> b) = (y[^]m) \<and> x = [b]"
      unfolding univ_basic_semialg_set_def
      by blast
    then have "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
      using A Qp.to_R1_closed[of b]
      unfolding univ_basic_semialg_set_def
      by blast
    then show "x \<in> basic_semialg_set 1 m (from_Qp_x P)"
      using by_def Qp_x_Qp_poly_eval assms
      unfolding basic_semialg_set_def
      by blast
  qed
  show "basic_semialg_set 1 m (from_Qp_x P) \<subseteq> (\<lambda>a. [a]) ` univ_basic_semialg_set m P"
  proof
    fix x
    assume A: "x \<in> basic_semialg_set 1 m (from_Qp_x P)"
    then obtain b where b_def:  "b \<in> carrier Q\<^sub>p \<and> x = [b]"
      unfolding basic_semialg_set_def
      by (metis (mono_tags, lifting) mem_Collect_eq Qp.to_R1_to_R Qp.to_R_pow_closed)
    obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> (Qp_ev (from_Qp_x P) [b]  = (y[^]m))"
      using A b_def
      unfolding basic_semialg_set_def
      by blast
    have " P \<bullet> b = (y[^]m)"
      using assms y_def b_def Qp_x_Qp_poly_eval by blast
    then show " x \<in> (\<lambda>a. [a]) ` univ_basic_semialg_set m P"
      using y_def b_def
      unfolding basic_semialg_set_def univ_basic_semialg_set_def
      by blast
  qed
qed

definition is_univ_semialgebraic where
"is_univ_semialgebraic S = (S \<subseteq> carrier Q\<^sub>p \<and> is_semialgebraic 1 (to_R1 ` S))"

lemma is_univ_semialgebraicE:
  assumes "is_univ_semialgebraic S"
  shows "is_semialgebraic 1 (to_R1 ` S)"
  using assms is_univ_semialgebraic_def by blast

lemma is_univ_semialgebraicI:
  assumes "is_semialgebraic 1 (to_R1 ` S)"
  shows "is_univ_semialgebraic S"
proof-
  have "S \<subseteq> carrier Q\<^sub>p"
  proof fix x assume "x \<in> S"
    then have "(to_R1 x) \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
      using assms
      by (smt Collect_mono_iff gen_boolean_algebra_subset image_def is_semialgebraicE mem_Collect_eq semialg_sets_def Qp.to_R1_carrier)
    then show "x \<in> carrier Q\<^sub>p"
      using assms
      by (metis nth_Cons_0 Qp.to_R_pow_closed)
  qed
  then show ?thesis
    using assms
    unfolding is_univ_semialgebraic_def
    by blast
qed

lemma univ_basic_semialg_set_is_univ_semialgebraic:
  assumes "P \<in> carrier Q\<^sub>p_x"
  assumes "m \<noteq> 0"
  shows "is_univ_semialgebraic (univ_basic_semialg_set m P)"
  using assms
  by (metis (mono_tags, lifting) basic_semialg_is_semialgebraic'
      from_Qp_x_closed is_univ_semialgebraic_def mem_Collect_eq subsetI
      univ_basic_semialg_set_def univ_basic_semialg_set_to_semialg_set)

lemma intersection_is_univ_semialgebraic:
  assumes "is_univ_semialgebraic A"
  assumes "is_univ_semialgebraic B"
  shows "is_univ_semialgebraic (A \<inter> B)"
  using assms intersection_is_semialg[of 1 "((\<lambda>a. [a]) ` A)" "((\<lambda>a. [a]) ` B)"]
  unfolding is_univ_semialgebraic_def
  by (metis le_infI1 Qp.to_R1_intersection)

lemma union_is_univ_semialgebraic:
  assumes "is_univ_semialgebraic A"
  assumes "is_univ_semialgebraic B"
  shows "is_univ_semialgebraic (A \<union> B)"
  using assms union_is_semialgebraic[of 1 "((\<lambda>a. [a]) ` A)" "((\<lambda>a. [a]) ` B)"]
  unfolding is_univ_semialgebraic_def
  by (metis Un_subset_iff image_Un)

lemma diff_is_univ_semialgebraic:
  assumes "is_univ_semialgebraic A"
  assumes "is_univ_semialgebraic B"
  shows "is_univ_semialgebraic (A - B)"
  using assms diff_is_semialgebraic[of 1 "((\<lambda>a. [a]) ` A)" "((\<lambda>a. [a]) ` B)"]
  unfolding is_univ_semialgebraic_def
  by (smt Diff_subset subset_trans Qp.to_R1_diff)

lemma finite_is_univ_semialgebraic:
  assumes "A \<subseteq> carrier Q\<^sub>p"
  assumes "finite A"
  shows "is_univ_semialgebraic A"
  using assms finite_is_semialg[of "((\<lambda>a. [a]) ` A)" ]  to_R1_finite[of A]
  unfolding is_univ_semialgebraic_def
  by (metis Qp.to_R1_carrier Qp.to_R1_subset)


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Defining the $p$-adic Valuation Semialgebraically\<close>
      (********************************************************************************************)
      (********************************************************************************************)


lemma Qp_square_root_criterion0:
  assumes "p \<noteq> 2"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "val a \<le> val b"
  assumes "a \<noteq> \<zero>"
  assumes "b \<noteq> \<zero>"
  assumes "val a \<ge> 0"
  shows "\<exists>y \<in> carrier Q\<^sub>p. a[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp>\<otimes>b[^](2::nat) = (y [^] (2::nat))"
proof-
  have 0: "(to_Zp a) \<in> carrier Z\<^sub>p"
    using assms(2) to_Zp_closed
    by blast
  have 1: "(to_Zp b) \<in> carrier Z\<^sub>p"
    using assms(3) to_Zp_closed
    by blast
  have 2: "a \<in> \<O>\<^sub>p"
    using val_ring_val_criterion assms(2) assms(5) assms(7) by blast
  have 3: "b \<in> \<O>\<^sub>p"
    using assms val_ring_val_criterion[of b] dual_order.trans by blast
  have 4: "val_Zp (to_Zp b) = val b"
    using 3 Zp_def \<iota>_def padic_fields.to_Zp_val padic_fields_axioms by blast
  have 5:  "val_Zp (to_Zp a) = val a"
    using Q\<^sub>p_def Zp_def assms(2) assms(7) padic_fields.Qp_val_ringI padic_fields.to_Zp_val padic_fields_axioms
    by blast
  have "\<exists>y \<in> carrier Z\<^sub>p. (to_Zp a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat) \<oplus>\<^bsub>Z\<^sub>p\<^esub> \<p> \<otimes>\<^bsub>Z\<^sub>p\<^esub>(to_Zp b)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat) = (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat))"
    using 0 1 2 4 5 assms Zp_square_root_criterion[of "(to_Zp a)" "(to_Zp b)"]
    by (metis "3" to_Zp_inc to_Zp_zero zero_in_val_ring)
  then obtain y where y_def: "y \<in> carrier Z\<^sub>p \<and> (to_Zp a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat) \<oplus>\<^bsub>Z\<^sub>p\<^esub> \<p> \<otimes>\<^bsub>Z\<^sub>p\<^esub>(to_Zp b)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat) = (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat))"
    by blast
  have 6: "a[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes>b[^](2::nat) = ((\<iota> y) [^] (2::nat))"
  proof-
    have 0: "\<iota> (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat)) = ((\<iota> y) [^] (2::nat))"
      using Qp_nonzero_nat_pow nat_pow_closed inc_pow nat_inc_zero inc_is_hom \<iota>_def y_def ring_hom_nat_pow[of Z\<^sub>p Q\<^sub>p \<iota> y 2]
            Q\<^sub>p_def Qp.ring_axioms Zp.ring_axioms
      by blast
    have 1: "\<iota> (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat)) = \<iota> ((to_Zp a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat) \<oplus>\<^bsub>Z\<^sub>p\<^esub> \<p> \<otimes>\<^bsub>Z\<^sub>p\<^esub>(to_Zp b)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat))"
      using y_def by presburger
    have 2: "\<iota> (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat)) = \<iota> ((to_Zp a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<iota> ( \<p> \<otimes>\<^bsub>Z\<^sub>p\<^esub>(to_Zp b)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat))"
      using "1" Zp.m_closed Zp_int_inc_closed assms(2) assms(3) inc_of_sum pow_closed to_Zp_closed by presburger
    hence 3: "\<iota> (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat)) = (\<iota> (to_Zp a))[^](2::nat) \<oplus> (\<iota>  \<p>) \<otimes> \<iota> ((to_Zp b)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat))"
      using Qp_nonzero_nat_pow nat_pow_closed inc_pow nat_inc_zero inc_is_hom \<iota>_def y_def ring_hom_nat_pow[of Z\<^sub>p Q\<^sub>p \<iota> _ 2]
            Q\<^sub>p_def Qp.ring_axioms Zp.ring_axioms Zp_int_inc_closed assms(2) assms(3) inc_of_prod pow_closed to_Zp_closed
      by metis
    then show ?thesis
      using "0" "4" val_ring_ord_criterion assms(2) assms(3) assms(4) assms(5)
          assms(6) assms(7) inc_pow not_nonzero_Zp ord_of_nonzero(1) p_inc to_Zp_closed to_Zp_inc
      by (metis to_Zp_zero val_pos val_ringI zero_in_val_ring)
  qed
  have "(\<iota> y) \<in> carrier Q\<^sub>p"
    using frac_closed local.inc_def y_def inc_closed by blast
  then show ?thesis
    using 6
    by blast
qed

lemma eint_minus_ineq':
  assumes "(a::eint) \<ge> b"
  shows "a -b \<ge> 0"
  by (metis assms eint_minus_ineq eint_ord_simps(3) idiff_infinity idiff_self order_trans top.extremum_unique top_eint_def)

lemma Qp_square_root_criterion:
  assumes "p \<noteq> 2"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "ord b \<ge> ord a"
  assumes "a \<noteq> \<zero>"
  assumes "b \<noteq> \<zero>"
  shows "\<exists>y \<in> carrier Q\<^sub>p. a[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp>\<otimes>b[^](2::nat) = (y [^] (2::nat))"
proof-
  have "\<exists>k::int. k \<le> min (ord a) (ord b) \<and> k mod 2 = 0"
  proof-
      let ?k = "if (min (ord a) (ord b)) mod 2 = 0 then min (ord a) (ord b)  else (min (ord a) (ord b)) - 1"
      have "?k \<le> min (ord a) (ord b) \<and> ?k mod 2 = 0"
        apply(cases "(min (ord a) (ord b)) mod 2 = 0 ")
       apply presburger
        by presburger
      then show ?thesis
        by meson
  qed
  then obtain k where k_def: "k \<le> min (ord a) (ord b) \<and> k mod 2 = 0"
    by meson
  obtain a0 where a0_def: "a0 = (\<pp>[^](-k)) \<otimes> a"
    by blast
  obtain b0 where b0_def: "b0 = (\<pp>[^](-k)) \<otimes> b"
    by blast
  have 0: "a0 \<in> nonzero Q\<^sub>p"
    using Qp.cring_axioms Qp.field_axioms Ring.integral a0_def assms(2) assms(5) cring_simprules(5)
          not_nonzero_Qp p_intpow_closed(1) p_nonzero
    by (metis Qp_int_pow_nonzero cring.cring_simprules(5))
  have 1: "val a0 =  val a - k"
    using a0_def assms(2) assms(5) val_mult p_nonzero  p_intpow_closed(1)
    by (metis Qp.m_comm Qp_int_pow_nonzero p_intpow_inv'' val_fract val_p_int_pow)
  have 11: "val b0 =  val b - k"
    using assms(3) assms(6) b0_def val_mult p_nonzero p_intpow_closed(1)
    by (metis Qp.m_lcomm Qp.one_closed Qp.r_one Qp_int_pow_nonzero p_intpow_inv'' val_fract val_p_int_pow)
  have A: "val a \<ge> k"
    using k_def val_ord assms by (smt eint_ord_simps(1) not_nonzero_Qp)
  have B: "val b \<ge> k"
    using  k_def val_ord assms by (smt eint_ord_simps(1) not_nonzero_Qp)
  then have 2: "val a0 \<ge> 0"
    using A 1 assms k_def eint_minus_ineq eint_ord_code(5) local.eint_minus_ineq' by presburger
  have 3: "val a0 \<le> val b0"
    using 1 11 assms
    by (metis eint.distinct(2) eint_minus_ineq eint_ord_simps(1) val_def)
  have 4: "a0 \<noteq> \<zero>"
    using a0_def "0" Qp.nonzero_memE(2) by blast
  have 5: "b0 \<noteq> \<zero>"
    using b0_def
    by (metis "4" Qp.integral_iff a0_def assms(2) assms(3) assms(6) p_intpow_closed(1))
  have "\<exists>y \<in> carrier Q\<^sub>p. a0[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp>\<otimes>b0[^](2::nat) = (y [^] (2::nat))"
    using Qp_square_root_criterion0[of a0 b0] assms 2 3 4 5 b0_def a0_def Qp.m_closed p_intpow_closed(1)
    by metis
  then obtain y where y_def: " y \<in> carrier Q\<^sub>p \<and> a0[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp>\<otimes>b0[^](2::nat) = (y [^] (2::nat))"
    by blast
  then have 6: " (\<pp>[^] (2 * k)) \<otimes>  (a0[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp>\<otimes>b0[^](2::nat)) =  (\<pp>[^] (2 * k))  \<otimes> (y [^] (2::nat))"
    by presburger
  then have 8: "((\<pp>[^] (2 * k)) \<otimes>  (a0[^](2::nat))) \<oplus>\<^bsub>Q\<^sub>p\<^esub>((\<pp>[^] (2 * k)) \<otimes> (\<pp>\<otimes>b0[^](2::nat))) =  (\<pp>[^] (2 * k))  \<otimes> (y [^] (2::nat))"
    using 6 Qp.r_distr[of "(a0[^](2::nat))" " (\<pp>\<otimes>b0[^](2::nat))" "(\<pp>[^] (2 * k))"]
    by (metis Qp.add.int_pow_closed Qp.m_closed Qp.nat_pow_closed Qp.one_closed a0_def assms(2) assms(3) b0_def p_inc p_intpow_closed(1) y_def)
  have 9: "(\<pp>[^](int 2*k)) = (\<pp>[^]k)[^](2::nat)"
    using Qp_int_nat_pow_pow[of \<pp> k 2]
    by (metis mult_of_nat_commute p_nonzero)
  then have "((\<pp>[^]k)[^](2::nat) \<otimes>  (a0[^](2::nat))) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^]k)[^](2::nat) \<otimes> (\<pp>\<otimes>b0[^](2::nat)) =  (\<pp>[^]k)[^](2::nat) \<otimes> (y [^] (2::nat))"
    by (metis "8" int_eq_iff_numeral)
  then have "((\<pp>[^]k) \<otimes> a0)[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>((\<pp>[^]k)[^](2::nat)) \<otimes> (\<pp>\<otimes>b0[^](2::nat)) = ((\<pp>[^]k)[^](2::nat))  \<otimes> (y [^] (2::nat))"
    by (metis Qp.cring_axioms a0_def assms(2) comm_monoid.nat_pow_distrib cring.cring_simprules(5) cring_def p_intpow_closed(1))
  then have 10:  "((\<pp>[^]k) \<otimes> a0)[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>((\<pp>[^]k)[^](2::nat)) \<otimes> (\<pp>\<otimes>b0[^](2::nat)) =  ((\<pp>[^]k)  \<otimes> y) [^] (2::nat)"
    using comm_monoid.nat_pow_distrib y_def
    by (metis Qp.comm_monoid_axioms p_intpow_closed(1))
  then have "((\<pp>[^]k) \<otimes> a0)[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>((((\<pp>[^]k)[^](2::nat)) \<otimes> \<pp>)\<otimes>b0[^](2::nat)) =  ((\<pp>[^]k)  \<otimes> y) [^] (2::nat)"
    using 10 monoid.m_assoc[of Q\<^sub>p "((\<pp>[^]k)[^](2::nat))" \<pp> " b0[^](2::nat)"]
    by (metis Qp.int_inc_closed Qp.m_assoc Qp.m_closed Qp.nat_pow_closed assms(3) b0_def p_intpow_closed(1))
  then have "((\<pp>[^]k) \<otimes> a0)[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>((\<pp> \<otimes> ((\<pp>[^]k)[^](2::nat)) )\<otimes>b0[^](2::nat)) =  ((\<pp>[^]k)  \<otimes> y) [^] (2::nat)"
    by (metis Qp.group_commutes_pow Qp.int_inc_closed Qp.m_comm p_intpow_closed(1))
  then have "((\<pp>[^]k) \<otimes> a0)[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>\<pp> \<otimes> (((\<pp>[^]k)[^](2::nat)) \<otimes>b0[^](2::nat)) =  ((\<pp>[^]k)  \<otimes> y) [^] (2::nat)"
    by (metis "10" Qp.int_inc_closed Qp.m_closed Qp.m_lcomm Qp.nat_pow_closed assms(3) b0_def p_intpow_closed(1))
  then have "((\<pp>[^]k) \<otimes> a0)[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>\<pp> \<otimes> ((\<pp>[^]k) \<otimes>b0)[^](2::nat) =  ((\<pp>[^]k)  \<otimes> y) [^] (2::nat)"
    by (metis Qp.m_closed Qp.nat_pow_distrib assms(3) b0_def p_intpow_closed(1))
  then have "a[^](2::nat) \<oplus>\<^bsub>Q\<^sub>p\<^esub>\<pp> \<otimes> b[^](2::nat) =  ((\<pp>[^]k)  \<otimes> y) [^] (2::nat)"
    by (metis Qp.l_one Qp.m_assoc a0_def assms(2) assms(3) b0_def p_intpow_closed(1) p_intpow_inv)
  then show ?thesis
    by (meson Qp.cring_axioms cring.cring_simprules(5) p_intpow_closed(1) y_def)
qed

lemma Qp_val_ring_alt_def0:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "ord a \<ge> 0"
  shows "\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
proof-
  have "\<exists>y \<in> carrier Z\<^sub>p. \<one>\<^bsub>Z\<^sub>p\<^esub> \<oplus>\<^bsub>Z\<^sub>p\<^esub> (\<p> [^]\<^bsub>Z\<^sub>p\<^esub> (3::nat))\<otimes>\<^bsub>Z\<^sub>p\<^esub> ((to_Zp a) [^]\<^bsub>Z\<^sub>p\<^esub> (4::nat)) = (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat))"
    using padic_integers.Zp_semialg_eq[of p "to_Zp a"] prime assms to_Zp_def
    by (metis (no_types, lifting) Qp.nonzero_closed Qp.not_nonzero_memI Zp_def val_ring_ord_criterion not_nonzero_Zp padic_integers_axioms to_Zp_closed to_Zp_inc to_Zp_zero zero_in_val_ring)
  then obtain y where y_def: "y \<in> carrier Z\<^sub>p \<and> \<one>\<^bsub>Z\<^sub>p\<^esub> \<oplus>\<^bsub>Z\<^sub>p\<^esub> (\<p> [^]\<^bsub>Z\<^sub>p\<^esub> (3::nat))\<otimes>\<^bsub>Z\<^sub>p\<^esub> ((to_Zp a) [^]\<^bsub>Z\<^sub>p\<^esub> (4::nat)) = (y [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat))"
    by blast
  then have "\<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = ((\<iota> y)[^](2::nat))"
    using  Group.nat_pow_0 Group.nat_pow_Suc nonzero_def
        val_ring_ord_criterion  assms inc_of_nonzero inc_of_prod inc_of_sum inc_pow
        m_closed nat_inc_closed nat_pow_closed  not_nonzero_Zp
        numeral_2_eq_2 p_natpow_inc to_Zp_closed to_Zp_inc
    by (smt Qp.nonzero_closed Qp.nonzero_memE(2) Zp.monom_term_car p_pow_nonzero(1) pow_closed to_Zp_zero zero_in_val_ring)
  then have "(\<iota> y) \<in> carrier Q\<^sub>p \<and> \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = ((\<iota> y)[^](2::nat))"
    using y_def inc_closed by blast
  then show ?thesis
    by blast
qed

text\<open>Defining the valuation semialgebraically for odd primes\<close>

lemma P_set_ord_semialg_odd_p:
  assumes "p \<noteq> 2"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows  "val a \<le> val b \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp> \<otimes> (b[^](2::nat))) = (y[^](2::nat)))"
proof(cases "a = \<zero>")
  case True
  show "val a \<le> val b \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp> \<otimes> (b[^](2::nat))) = (y[^](2::nat)))"
  proof
    show "val b \<ge> val a \<Longrightarrow> \<exists>y\<in>carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
    proof-
      assume A: "val b \<ge> val a"
      then have "val b \<ge> \<infinity>"
        by (metis True local.val_zero)
      then have "b = \<zero>"
        using assms(3) local.val_zero val_ineq by presburger
      then have "(a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (\<zero>[^](2::nat))"
        using True
        by (metis Qp.int_inc_zero Qp.int_nat_pow_rep Qp.nonzero_closed Qp.r_null Qp.r_zero assms(3) p_nonzero zero_power2)
      then show ?thesis
        using \<open>b = \<zero>\<close> assms(3) by blast
    qed
    show "\<exists>y\<in>carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat)) \<Longrightarrow> val b \<ge> val a"
    proof-
      assume "\<exists>y\<in>carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
      then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and>(a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
        by blast
      then have 0: "\<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
        by (metis (no_types, lifting) Qp.add.r_cancel_one' Qp.int_inc_closed Qp.nat_pow_closed
            Qp.not_nonzero_memI Qp_nonzero_nat_pow True assms(2) assms(3) local.monom_term_car not_nonzero_Qp zero_less_numeral)
      have "b = \<zero>"
        apply(rule ccontr)
        using 0 assms y_def p_times_square_not_square[of b]
        unfolding P_set_def
        by (metis (no_types, opaque_lifting) P_set_memI Qp.nat_pow_closed True
            \<open>b \<in> nonzero Q\<^sub>p \<Longrightarrow> \<pp> \<otimes> b [^] 2 \<notin> P_set 2\<close> not_nonzero_Qp p_times_square_not_square')
      then show ?thesis
        using eint_ord_code(3) local.val_zero by presburger
    qed
  qed
next
  case False
  then show ?thesis
  proof(cases "b = \<zero>")
    case True
    then have "(a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp> \<otimes> (b[^](2::nat))) =  (a[^](2::nat))"
      by (metis Qp.add.l_cancel_one' Qp.int_inc_zero Qp.int_nat_pow_rep Qp.nat_pow_closed Qp.nonzero_closed Qp.r_null assms(2) assms(3) p_nonzero zero_power2)
    then have 0: "(\<exists>y \<in> carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp> \<otimes> (b[^](2::nat))) = (y[^](2::nat)))"
      using assms(2)
      by blast
    have 1: "val a \<le> val b"
      using True assms local.val_zero  eint_ord_code(3) by presburger
    show "val a \<le> val b \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp> \<otimes> (b[^](2::nat))) = (y[^](2::nat)))"
      using 0 1
      by blast
  next
    case F: False
    show "val a \<le> val b \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp> \<otimes> (b[^](2::nat))) = (y[^](2::nat)))"
    proof
      show "val b \<ge> val a \<Longrightarrow> \<exists>y\<in>carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
      proof-
        assume  "val b \<ge> val a "
        then have "ord b \<ge> ord a"
          using F False
          by (metis eint_ord_simps(1) val_def)
        then show "\<exists>y\<in>carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
          using assms Qp_square_root_criterion[of a b] False F
          by blast
      qed
      show "\<exists>y\<in>carrier Q\<^sub>p.(a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat)) \<Longrightarrow> val b \<ge> val a"
      proof-
        assume "\<exists>y\<in>carrier Q\<^sub>p. (a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
        then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and>(a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat)) = (y[^](2::nat))"
          by blast
        have 0: "ord (a[^](2::nat)) =  2* ord a"
          by (metis (mono_tags, opaque_lifting) False Suc_1 assms(2) int_eq_iff_numeral nat_numeral
              nonzero_nat_pow_ord not_nonzero_Qp)
        have 1: "ord (\<pp> \<otimes> (b[^](2::nat))) = 1 + 2* ord b"
        proof-
          have 0: "ord (\<pp> \<otimes> (b[^](2::nat))) = ord \<pp> + ord  (b[^](2::nat))"
            using F Qp_nat_pow_nonzero assms(3) not_nonzero_Qp ord_mult p_nonzero
            by metis
          have 1: "ord  (b[^](2::nat)) = 2* ord b"
            using F assms
            by (metis (mono_tags, opaque_lifting)  Suc_1  int_eq_iff_numeral nat_numeral
              nonzero_nat_pow_ord not_nonzero_Qp)
          then show ?thesis
            using "0" ord_p
            by linarith
        qed
        show "val b \<ge> val a"
        proof(rule ccontr)
          assume "\<not> val b \<ge> val a"
          then have "val b \<noteq> val a \<and> val a \<ge> val b"
            by (metis linear)
          then have "ord a > ord b"
            using F False assms
            by (metis \<open>\<not> val a \<le> val b\<close> eint_ord_simps(1) le_less not_less_iff_gr_or_eq val_def)
          then have "ord (a[^](2::nat)) > ord (\<pp> \<otimes> (b[^](2::nat)))"
            using 0 1
            by linarith
          then have "ord ((a[^](2::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^](2::nat))) = ord (\<pp> \<otimes> (b[^](2::nat)))"
            by (meson F False Qp.int_inc_closed Qp_nat_pow_nonzero assms(2) assms(3)
                local.monom_term_car not_nonzero_Qp ord_ultrametric_noteq p_times_square_not_square')
          then have A0: "ord (y[^](2::nat)) = 1 + 2* ord b"
            by (metis "1" \<open>y \<in> carrier Q\<^sub>p \<and> (a[^]2) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<pp> \<otimes> (b[^]2) = (y[^]2)\<close>)
          have A1: "(y[^](2::nat)) \<in> nonzero Q\<^sub>p"
            using y_def 0 1
            by (smt F False Qp.nonzero_closed Qp_nat_pow_nonzero assms(2) assms(3) diff_ord_nonzero
                local.monom_term_car not_nonzero_Qp p_nonzero p_times_square_not_square')
          have A2: "y \<in> nonzero Q\<^sub>p"
            using A1 Qp_nonzero_nat_pow pos2 y_def by blast
          have A3: "ord (y[^](2::nat)) = 2* ord y"
            using  A2  nonzero_nat_pow_ord
            by presburger
          then show False using A0
            by presburger
        qed
      qed
    qed
  qed
qed

text\<open>Defining the valuation ring semialgebraically for all primes\<close>

lemma Qp_val_ring_alt_def:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "a \<in> \<O>\<^sub>p \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)))"
proof(cases "a = \<zero>")
  case True
  then have "\<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = \<one>"
    by (metis Qp.add.l_cancel_one' Qp.integral_iff Qp.nat_pow_closed Qp.not_nonzero_memI
        Qp.one_closed Qp_nonzero_nat_pow assms not_nonzero_Qp p_natpow_closed(1) zero_less_numeral)
  then have "\<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (\<one>[^](2::nat))"
    using Qp.nat_pow_one by blast
  then show ?thesis
    using True zero_in_val_ring by blast
next
  case False
  show "a \<in> \<O>\<^sub>p \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)))"
  proof
    show "a \<in> \<O>\<^sub>p \<Longrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)))"
      using assms Qp_val_ring_alt_def0[of a] False
      by (meson not_nonzero_Qp ord_nonneg)
    show "(\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))) \<Longrightarrow> a \<in> \<O>\<^sub>p"
    proof-
      assume "(\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)))"
      then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and>\<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
        by blast
      then have "(\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>"
        using Qp.ring_simprules
        by (smt Qp.nat_pow_closed assms p_natpow_closed(1))
      then have "ord ((\<pp>[^](3::nat))\<otimes> (a[^](4::nat))) = ord ((y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>)"
        by presburger
      then have "3 + ord (a[^](4::nat)) = ord ((y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>)"
        by (metis False Qp_nat_pow_nonzero assms not_nonzero_Qp of_nat_numeral ord_mult ord_p_pow_nat p_nonzero)
      then have 0: "3 + 4* ord a = ord ((y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>)"
        using assms False nonzero_nat_pow_ord[of a "(4::nat)"]
        by (metis nonzero_nat_pow_ord not_nonzero_Qp of_nat_numeral)
      have "ord a \<ge> 0"
      proof(rule ccontr)
        assume "\<not> 0 \<le> ord a"
        then have 00: "ord ((y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>) < 0"
          using 0
          by linarith
        have yn: "y \<in> nonzero Q\<^sub>p"
          apply(rule ccontr)
          using y_def 0
          by (metis "00" Qp.not_eq_diff_nonzero Qp.one_closed Qp.one_nonzero Qp.pow_zero
              \<open>\<pp> [^] 3 \<otimes> a [^] 4 = y [^] 2 \<ominus> \<one>\<close> diff_ord_nonzero less_numeral_extra(3)
              local.one_neq_zero not_nonzero_Qp ord_one zero_less_numeral)
        then have "ord ((y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>) = ord (y[^](2::nat))"
          using y_def ord_ultrametric_noteq''[of  "(y[^](2::nat))" "\<one>" ]
          by (metis "00" False Qp.integral Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_pow_nonzero
              Qp.not_eq_diff_nonzero Qp.one_nonzero Qp.r_right_minus_eq \<open>\<pp> [^] 3 \<otimes> a [^] 4 = y [^] 2 \<ominus> \<one>\<close>
              assms ord_one ord_ultrametric_noteq p_nonzero)
        then have "ord ((y[^](2::nat)) \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<one>) = 2* ord y"
          using y_def Qp_nat_pow_nonzero Qp_nonzero_nat_pow nonzero_nat_pow_ord[of y "(2::nat)"]  yn
          by linarith
        then have "3 + (4* ord a) = 2* ord y"
          using "00" "0"
          by linarith
        then show False
          by presburger
      qed
      then show "a \<in> \<O>\<^sub>p"
        using False val_ring_ord_criterion assms by blast
    qed
  qed
qed

lemma Qp_val_alt_def:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "val b \<le> val a \<longleftrightarrow> (\<exists>y \<in> carrier Q\<^sub>p. (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)))"
proof
  show "val a \<ge> val b \<Longrightarrow> \<exists>y\<in>carrier Q\<^sub>p. (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
  proof-
    assume A: "val a \<ge> val b"
    show "\<exists>y\<in>carrier Q\<^sub>p. (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
    proof(cases "b = \<zero>")
      case True
      then have "a = \<zero>"
        using A assms(1) val_ineq
        by blast
      then have "(b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (\<zero>[^](2::nat))"
        by (metis Qp.nat_pow_zero Qp.r_null Qp.r_zero True assms(2) p_natpow_closed(1) zero_neq_numeral)
      then show ?thesis
        using True A assms(2)
        by blast
    next
      case False
      assume B: "b \<noteq> \<zero>"
      show "\<exists>y\<in>carrier Q\<^sub>p. (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat)) \<otimes> (a[^](4::nat)) = (y[^](2::nat))"
      proof(cases "a = \<zero>")
        case True
        then have "(b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (b[^](4::nat))"
          using Qp.cring_axioms Qp.nat_pow_closed assms(2) cring_def p_natpow_closed(1) ring.pow_zero zero_less_numeral
          by (metis Qp.add.l_cancel_one' Qp.integral_iff assms(1))
        then have "(b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = ((b[^](2::nat))[^] (2::nat))"
          by (metis Qp_nat_pow_pow assms(2) mult_2_right numeral_Bit0)
        then have "(b[^](2::nat)) \<in> carrier Q\<^sub>p \<and> (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = ((b[^](2::nat))[^] (2::nat))"
          using Qp.nat_pow_closed assms(2)
          by blast
        then show ?thesis
          by blast
      next
        case False
        have F0:  "b \<in> nonzero Q\<^sub>p"
          using B assms(2) not_nonzero_Qp
          by metis
        have F1: "a \<in> nonzero Q\<^sub>p"
          using False assms(1) not_nonzero_Qp
          by metis
        then have "(a \<div> b) \<in> nonzero Q\<^sub>p"
          using B
          by (meson Localization.submonoid.m_closed Qp.nonzero_is_submonoid assms(2) inv_in_frac(3))
        then have "val a \<ge> val b"
          using F0 F1 A by blast
        then have "val (a \<div> b) \<ge> 0"
          using F0 F1 val_fract assms(1) local.eint_minus_ineq' by presburger
        obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat)) = (y[^](2::nat))"
          using Qp_val_ring_alt_def0
          by (meson B False Qp.integral Qp.nonzero_closed \<open>(a \<div> b) \<in> nonzero Q\<^sub>p\<close> \<open>0 \<le> val (a \<div> b)\<close>
              assms(1) assms(2) inv_in_frac(1) inv_in_frac(2) ord_nonneg val_ringI)
        then have "(b[^](4::nat)) \<otimes> (\<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat))) =
               (b[^](4::nat)) \<otimes> (y[^](2::nat))"
          by presburger
        then have  F2: "(b[^](4::nat)) \<otimes> (\<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat))) =
               ((b[^](2::nat)) [^] (2::nat)) \<otimes> (y[^](2::nat))"
          by (metis Qp.nat_pow_pow assms(2) mult_2_right numeral_Bit0)
        have  F3: "((b[^](4::nat)) \<otimes> \<one>) \<oplus>\<^bsub>Q\<^sub>p\<^esub> ((b[^](4::nat)) \<otimes>((\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat)))) =
               ((b[^](2::nat))[^] (2::nat)) \<otimes> (y[^](2::nat))"
        proof-
          have 0: "(\<pp>[^](3::nat)) \<otimes> (a \<div> b[^](4::nat)) \<in> carrier Q\<^sub>p "
          proof-
            have "(a \<div> b[^](4::nat)) \<in> carrier Q\<^sub>p"
              using F0 Qp.nat_pow_closed assms(1) fract_closed Qp_nat_pow_nonzero by presburger
            then show ?thesis
              by (meson Qp.cring_axioms cring.cring_simprules(5) p_natpow_closed(1))
          qed
          have 1: "(b[^](4::nat)) \<in> carrier Q\<^sub>p"
            using Qp.nat_pow_closed assms(2)
            by blast
          then show ?thesis
            using 0 F2  ring.ring_simprules(23)[of Q\<^sub>p "\<one>" "(\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat))" "(b[^](4::nat))"]
                  Qp.cring_axioms Qp.nonzero_mult_closed Qp.ring_axioms Qp_nat_pow_nonzero \<open>(a \<div> b) \<in> nonzero Q\<^sub>p\<close> p_nonzero
            by blast
        qed
        have F4: "(b[^](4::nat)) \<in> carrier Q\<^sub>p"
          using Qp.nat_pow_closed assms(2)
          by blast
        then have "((b[^](4::nat)) \<otimes> \<one>) = (b[^](4::nat))"
          using Qp.r_one by blast
        then have F5:  "(b[^](4::nat))\<oplus>\<^bsub>Q\<^sub>p\<^esub> ((b[^](4::nat)) \<otimes>((\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat)))) =
               ((b[^](2::nat)) [^] (2::nat)) \<otimes> (y[^](2::nat))"
          using F3
          by presburger
        have "((b[^](4::nat)) \<otimes>((\<pp>[^](3::nat))\<otimes> ((a \<div> b)[^](4::nat)))) = (\<pp>[^](3::nat))\<otimes>((b[^](4::nat)) \<otimes> ((a \<div> b)[^](4::nat)))"
        proof-
          have 0: "(b[^](4::nat)) \<in> carrier Q\<^sub>p"
            using F4 by blast
          have 1: "(\<pp>[^](3::nat)) \<in> carrier Q\<^sub>p"
            by blast
          have  2: "((a \<div> b)[^](4::nat)) \<in> carrier Q\<^sub>p"
            using F0 Qp.nat_pow_closed assms(1) fract_closed
            by blast
          show ?thesis using 0 1 2  monoid.m_assoc[of Q\<^sub>p] comm_monoid.m_comm[of Q\<^sub>p]
            using Qp.m_lcomm by presburger
        qed
        then have  "(b[^](4::nat))\<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes>((b[^](4::nat)) \<otimes> ((a \<div> b)[^](4::nat))) =
               ((b[^](2::nat)) [^] (2::nat)) \<otimes> (y[^](2::nat))"
          using F5  by presburger
        then have  "(b[^](4::nat))\<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes>((b \<otimes>(a \<div> b))[^](4::nat)) =
               ((b[^](2::nat)) [^] (2::nat)) \<otimes> (y[^](2::nat))"
          using F0 Qp.nat_pow_distrib assms(1) assms(2) fract_closed by presburger
        then have  "(b[^](4::nat))\<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes>(a[^](4::nat)) =
               ((b[^](2::nat)) [^] (2::nat)) \<otimes> (y[^](2::nat))"
          by (metis F0 assms(1) local.fract_cancel_right)
        then have  "(b[^](4::nat))\<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes>(a[^](4::nat)) =
               (((b[^](2::nat))\<otimes> y)[^](2::nat))"
          using Qp.nat_pow_closed Qp.nat_pow_distrib assms(2) y_def by blast
        then have  "((b[^](2::nat))\<otimes> y) \<in> carrier Q\<^sub>p \<and> (b[^](4::nat))\<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes>(a[^](4::nat)) =
               (((b[^](2::nat))\<otimes> y)[^](2::nat))"
          by (meson Qp.cring_axioms Qp.nat_pow_closed assms(2) cring.cring_simprules(5) y_def)
        then show ?thesis
          by blast
      qed
    qed
  qed
  show "\<exists>y \<in> carrier Q\<^sub>p. (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat)) \<Longrightarrow> val a \<ge> val b"
  proof-
    assume A: "\<exists>y \<in> carrier Q\<^sub>p. (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
    show "val a \<ge> val b"
    proof(cases "a = \<zero>")
      case True
      then show ?thesis
        using eint_ord_code(3) local.val_zero by presburger
    next
      case False
      have  "b \<noteq> \<zero>"
      proof(rule ccontr)
        assume  "\<not> b \<noteq> \<zero>"
        then have "\<exists>y \<in> carrier Q\<^sub>p.  (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
          using A
          by (metis (no_types, lifting) Qp.add.r_cancel_one' Qp.nat_pow_closed Qp.nonzero_memE(2)
              Qp_nonzero_nat_pow assms(1) assms(2) local.monom_term_car not_nonzero_Qp
              p_natpow_closed(1) zero_less_numeral)
        then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
          by blast
        have 0: "ord ((\<pp>[^](3::nat))\<otimes> (a[^](4::nat))) = 3 +  4* ord a"
        proof-
          have 00: "(\<pp>[^](3::nat)) \<in> nonzero Q\<^sub>p"
            using Qp_nat_pow_nonzero p_nonzero by blast
          have 01: "(a[^](4::nat)) \<in> nonzero Q\<^sub>p"
            using False Qp_nat_pow_nonzero assms(1) not_nonzero_Qp Qp.nonzero_memI by presburger
          then show ?thesis using ord_mult[of "\<pp>[^](3::nat)" "a[^](4::nat)"]
            by (metis (no_types, lifting) "00" False assms(1) nonzero_nat_pow_ord
                not_nonzero_Qp of_nat_numeral ord_p_pow_nat)
        qed
        have 1: "ord ((\<pp>[^](3::nat))\<otimes> (a[^](4::nat))) = 2* (ord y)"
        proof-
          have "y \<noteq> \<zero>"
          proof(rule ccontr)
            assume " \<not> y \<noteq> \<zero>"
            then have "(\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = \<zero>"
              using y_def  Qp.cring_axioms cring_def pos2 ring.pow_zero by blast
            then show False
              by (metis False Qp.integral Qp.nat_pow_closed Qp.nonzero_pow_nonzero
                  Qp.not_nonzero_memI Qp_nat_pow_nonzero assms(1) p_natpow_closed(1) p_nonzero)
          qed
          then show ?thesis
            using y_def
            by (metis nonzero_nat_pow_ord not_nonzero_Qp of_nat_numeral)
        qed
        then show False
          using 0
          by presburger
      qed
      then have F0: "b \<in> nonzero Q\<^sub>p"
        using assms(2) not_nonzero_Qp  by metis

      have F1: "a \<in> nonzero Q\<^sub>p"
        using False assms(1) not_nonzero_Qp by metis
      obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat)) = (y[^](2::nat))"
        using A by blast
      show ?thesis
      proof(rule ccontr)
        assume " \<not> val a \<ge> val b "
        then have F2: "ord a < ord b"
          using F0 F1 assms
          by (metis False \<open>b \<noteq> \<zero>\<close> eint_ord_simps(1) leI val_def)
        have 0: "ord ((\<pp>[^](3::nat))\<otimes> (a[^](4::nat))) = 3 + 4* ord a"
          using F0 ord_mult F1 Qp_nat_pow_nonzero nonzero_nat_pow_ord ord_p_pow_nat p_natpow_closed(2)
          by presburger
        have 1: " ord (b[^](4::nat)) = 4* ord b"
          using F0 nonzero_nat_pow_ord
          by presburger
        have 2: "(4 * (ord b)) > 4 * (ord a)"
          using F2 by linarith
        have 3: "(4 * (ord b)) \<le> 3 + 4* ord a"
        proof(rule ccontr)
          assume "\<not> (4 * (ord b)) \<le> 3 + 4* ord a"
          then have "(4 * (ord b)) > 3 + 4* ord a"
            by linarith
          then have 30: "ord ((b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat))) = 3 + 4* ord a"
            using "0" "1" F0 F1  Qp_nat_pow_nonzero Qp.nat_pow_closed assms(1) monom_term_car not_nonzero_Qp ord_ultrametric_noteq
                p_natpow_closed(1) p_nonzero
            by (metis Qp.integral)
          have "y \<in> nonzero Q\<^sub>p"
          proof(rule ccontr)
            assume A: "y \<notin> nonzero Q\<^sub>p"
            then have "y = \<zero>"
              using y_def  Qp.nonzero_memI by blast
            then have "b [^] 4 \<oplus> \<pp> [^] 3 \<otimes> a [^] 4 = \<zero>"
              by (smt "0" "1" A F0 False Qp.integral Qp.nat_pow_closed Qp.nonzero_closed
                Qp.nonzero_mult_closed Qp.nonzero_pow_nonzero Qp.pow_zero assms(1) diff_ord_nonzero not_nonzero_Qp p_nonzero pos2 y_def)
            then show False
              by (smt "0" "1" A F0 F1 Qp.integral Qp.nat_pow_closed Qp.nonzero_mult_closed
                Qp_nat_pow_nonzero assms(1) diff_ord_nonzero not_nonzero_Qp p_natpow_closed(1) p_nonzero y_def)
          qed
          then have 31: "ord ((b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat))) = 2* ord y"
            using nonzero_nat_pow_ord y_def
            by presburger
          then show False using 30 by presburger
        qed
        show False
          using 2 3
          by presburger
      qed
    qed
  qed
qed

text\<open>The polynomial in two variables which semialgebraically defines the valuation relation\<close>

definition Qp_val_poly where
"Qp_val_poly = (pvar Q\<^sub>p 1)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat) \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> (\<pp>[^](3::nat) \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> ((pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat)))"

lemma Qp_val_poly_closed:
"Qp_val_poly \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"
proof-
  have "(pvar Q\<^sub>p 1) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"
    using local.pvar_closed one_less_numeral_iff semiring_norm(76) by blast
  then have 0: "(pvar Q\<^sub>p 1)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"

    using  ring.Pring_is_ring[of Q\<^sub>p "{0::nat..2-1}"]
          monoid.nat_pow_closed[of "coord_ring Q\<^sub>p 2"] Qp.cring_axioms cring.axioms(1) ring.Pring_is_monoid
    by blast
  have 1: "(pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"
    using local.pvar_closed pos2 by blast
  have 2: "\<pp>[^](3::nat) \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"
    using 1 local.smult_closed p_natpow_closed(1) by blast
  then show ?thesis
    unfolding Qp_val_poly_def
    using 0 by blast
qed

lemma Qp_val_poly_eval:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "Qp_ev Qp_val_poly [a, b] =  (b[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (a[^](4::nat))"
proof-
  have 0: "[a,b] \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
  proof(rule cartesian_power_car_memI)
    show "length [a, b] = 2"
      by simp
    have "set [a,b] = {a,b}"
      by auto
    then show "set [a, b] \<subseteq> carrier Q\<^sub>p"
      using assms
      by (simp add: \<open>a \<in> carrier Q\<^sub>p\<close> \<open>b \<in> carrier Q\<^sub>p\<close>)
  qed
  obtain f where f_def: "f = ((pvar Q\<^sub>p 1)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat))"
    by blast
  obtain g where g_def: "g = (\<pp>[^](3::nat) \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> ((pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat)))"
    by blast
  have 1: "Qp_val_poly = f \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> g"
    unfolding Qp_val_poly_def
    using f_def g_def by blast
  have 1: "Qp_ev (pvar Q\<^sub>p (0::nat)) [a,b] = a"
    using eval_pvar
    by (metis \<open>[a, b] \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)\<close> nth_Cons_0 pos2)
  have 2: "Qp_ev (pvar Q\<^sub>p (1::nat)) [a,b] = b"
    using eval_pvar
    by (metis (no_types, lifting) "0" One_nat_def add_diff_cancel_right' assms(2)
        cartesian_power_car_memE gr_zeroI less_numeral_extra(1) less_numeral_extra(4)
        list.size(4) nth_Cons_pos Qp.to_R1_closed Qp.to_R_to_R1 zero_less_diff)
  have 3: "Qp_ev ((pvar Q\<^sub>p 1)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat)) [a,b] = (b[^](4::nat))"
    by (metis "0" "2" eval_at_point_nat_pow local.pvar_closed one_less_numeral_iff semiring_norm(76))
  have 4: "Qp_ev ((pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat)) [a,b] = (a[^](4::nat))"
    using "0" "1" eval_at_point_nat_pow local.pvar_closed pos2 by presburger
  then have 5: "Qp_ev (poly_scalar_mult Q\<^sub>p (\<pp>[^](3::nat)) ((pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat))) [a,b] = (\<pp>[^](3::nat))\<otimes> (a[^](4::nat))"
    using eval_at_point_smult[of "[a,b]" 2 "(pvar Q\<^sub>p 0)[^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>(4::nat)" "\<pp>[^](3::nat)" ] 2
    by (metis "0" MP.nat_pow_closed eval_at_point_scalar_mult local.pvar_closed p_natpow_closed(1) zero_less_numeral)
  then show ?thesis
  proof-
    have 00: "[a, b] \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
      by (simp add: "0")
    have 01: " pvar Q\<^sub>p 1 [^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> (4::nat) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"
      by (meson MP.nat_pow_closed local.pvar_closed one_less_numeral_iff semiring_norm(76))
    have 02: "\<pp>[^](3::nat) \<odot>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub>  (pvar Q\<^sub>p 0 [^]\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> (4::nat)) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>2\<^esub>])"
      by (meson MP.nat_pow_closed local.pvar_closed local.smult_closed p_natpow_closed(1) zero_less_numeral)
    then show ?thesis
      unfolding Qp_val_poly_def
      using 00 01 02
      by (metis (no_types, lifting) "3" "4" MP.nat_pow_closed eval_at_point_add eval_at_point_smult
          local.pvar_closed p_natpow_closed(1) zero_less_numeral)
  qed
qed

lemma Qp_2I:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "[a,b] \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
  apply(rule cartesian_power_car_memI)
  using assms
  apply (simp add: assms(1) assms(2))
  using assms
  by (simp add: assms(1) assms(2))

lemma pair_id:
  assumes "length as = 2"
  shows "as = [as!0, as!1]"
  using assms
  by (smt One_nat_def diff_Suc_1 length_Cons less_Suc0 less_SucE list.size(3)
      nth_Cons' nth_equalityI numeral_2_eq_2)

lemma Qp_val_semialg:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "val b \<le> val a \<longleftrightarrow> [a,b] \<in> basic_semialg_set 2 (2::nat) Qp_val_poly"
proof
  show "val a \<ge> val b \<Longrightarrow> [a, b] \<in> basic_semialg_set 2 2 Qp_val_poly"
    using Qp_val_alt_def[of a b] Qp_2I[of a b]  Qp_val_poly_eval[of a b]
    unfolding basic_semialg_set_def
    by (metis (mono_tags, lifting) assms(1) assms(2) mem_Collect_eq)
  show "[a, b] \<in> basic_semialg_set 2 2 Qp_val_poly \<Longrightarrow> val a \<ge> val b"
    using Qp_val_alt_def[of a b] Qp_2I[of a b]  Qp_val_poly_eval[of a b]
    unfolding basic_semialg_set_def
    using assms(1) assms(2)
    by blast
qed

definition val_relation_set where
"val_relation_set = {as \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (as!1) \<le> val (as!0)}"

lemma val_relation_setE:
  assumes "as \<in> val_relation_set"
  shows "as!0 \<in> carrier Q\<^sub>p \<and> as!1 \<in> carrier Q\<^sub>p \<and> as = [as!0,as!1] \<and> val (as!1) \<le> val (as!0)"
  using assms  unfolding val_relation_set_def
  by (smt cartesian_power_car_memE cartesian_power_car_memE' mem_Collect_eq one_less_numeral_iff pair_id pos2 semiring_norm(76))

lemma val_relation_setI:
  assumes "as!0 \<in> carrier Q\<^sub>p"
  assumes "as!1 \<in> carrier Q\<^sub>p"
  assumes "length as = 2"
  assumes "val (as!1) \<le> val(as!0)"
  shows "as \<in> val_relation_set"
  unfolding val_relation_set_def using assms Qp_2I[of "as!0" "as!1"]
  by (metis (no_types, lifting) mem_Collect_eq pair_id)

lemma val_relation_semialg:
"val_relation_set  = basic_semialg_set 2 (2::nat) Qp_val_poly"
proof
  show "val_relation_set \<subseteq>  basic_semialg_set 2 (2::nat) Qp_val_poly"
  proof fix as
    assume A: "as \<in> val_relation_set"
    have 0: "length as = 2"
      unfolding val_relation_set_def
      by (metis (no_types, lifting) A cartesian_power_car_memE mem_Collect_eq val_relation_set_def)
    have 1: "as = [as ! 0, as ! 1]"
      by (metis (no_types, lifting) A cartesian_power_car_memE mem_Collect_eq pair_id val_relation_set_def)
    show "as \<in>   basic_semialg_set 2 (2::nat) Qp_val_poly"
      using A 1 val_relation_setE[of as]  Qp_val_semialg[of  "as!0" "as!1"]
      by presburger
  qed
  show "basic_semialg_set 2 (2::nat) Qp_val_poly \<subseteq> val_relation_set"
  proof
    fix as
    assume "as \<in> basic_semialg_set 2 (2::nat) Qp_val_poly"
    then show "as \<in> val_relation_set"
      using val_relation_setI[of as]
      by (smt cartesian_power_car_memE cartesian_power_car_memE' mem_Collect_eq
          one_less_numeral_iff Qp_val_semialg basic_semialg_set_def
          val_relation_set_def padic_fields_axioms pair_id pos2 semiring_norm(76))
  qed
qed

lemma val_relation_is_semialgebraic:
"is_semialgebraic 2 val_relation_set"
proof -
have "{rs \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (rs ! 0) \<ge> val (rs ! 1)} = basic_semialg_set (Suc 1) (Suc 1) Qp_val_poly"
using Suc_1 val_relation_semialg val_relation_set_def by presburger
  then show ?thesis
    by (metis (no_types) Qp_val_poly_closed Suc_1 basic_semialg_is_semialgebraic' val_relation_set_def zero_neq_numeral)
qed

lemma Qp_val_ring_is_semialg:
  obtains P where "P \<in> carrier Q\<^sub>p_x \<and> \<O>\<^sub>p = univ_basic_semialg_set 2 P"
proof-
  obtain P where P_def: "P = (\<pp>[^](3::nat)) \<odot>\<^bsub>Q\<^sub>p_x \<^esub>(X_poly Q\<^sub>p) [^]\<^bsub>Q\<^sub>p_x\<^esub> (4::nat) \<oplus>\<^bsub>Q\<^sub>p_x\<^esub> \<one>\<^bsub>Q\<^sub>p_x\<^esub>"
    by blast
  have 0: "P \<in> carrier Q\<^sub>p_x"
  proof-
    have 0: "(X_poly Q\<^sub>p) \<in> carrier Q\<^sub>p_x"
      using UPQ.X_closed by blast
    then show ?thesis
      using P_def UPQ.P.nat_pow_closed p_natpow_closed(1) by blast
  qed
  have 1: "\<O>\<^sub>p = univ_basic_semialg_set 2 P"
  proof
    show "\<O>\<^sub>p \<subseteq> univ_basic_semialg_set 2 P"
    proof
      fix x
      assume A: "x \<in> \<O>\<^sub>p"
      show "x \<in> univ_basic_semialg_set 2 P"
      proof-
        have x_car: "x \<in> carrier Q\<^sub>p"
          using A val_ring_memE by blast
        then have "(\<exists>y \<in> carrier Q\<^sub>p. \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (x[^](4::nat)) = (y[^](2::nat)))"
          using A Qp_val_ring_alt_def[of x]
          by blast
        then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (x[^](4::nat)) = (y[^](2::nat))"
          by blast
        have "y \<in> carrier Q\<^sub>p \<and> P \<bullet> x = (y[^](2::nat))"
        proof-
          have "P \<bullet> x = \<one> \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<pp>[^](3::nat))\<otimes> (x[^](4::nat))"
          proof-
            have "((\<pp>[^](3::nat)) \<odot>\<^bsub>Q\<^sub>p_x\<^esub> (X_poly Q\<^sub>p) [^]\<^bsub>Q\<^sub>p_x\<^esub>  (4::nat)) \<in> carrier Q\<^sub>p_x"
              using UPQ.monom_closed p_natpow_closed(1) by blast
            then have "P \<bullet> x = (((\<pp>[^](3::nat)) \<odot>\<^bsub>Q\<^sub>p_x\<^esub> (X_poly Q\<^sub>p) [^]\<^bsub>Q\<^sub>p_x\<^esub>  (4::nat))\<bullet> x) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<one>\<^bsub>Q\<^sub>p_x\<^esub> \<bullet> x)"
              using P_def x_car UPQ.to_fun_plus by blast
            then have 0: "P \<bullet> x = (\<pp>[^](3::nat)) \<otimes>(( (X_poly Q\<^sub>p) [^]\<^bsub>Q\<^sub>p_x\<^esub>  (4::nat))\<bullet> x) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (\<one>\<^bsub>Q\<^sub>p_x\<^esub> \<bullet> x)"
              using UPQ.P.nat_pow_closed UPQ.X_closed UPQ.to_fun_smult p_natpow_closed(1) x_car by presburger
            have "(( (X_poly Q\<^sub>p) [^]\<^bsub>Q\<^sub>p_x\<^esub>  (4::nat))\<bullet> x) = (x[^](4::nat))"
              using UPQ.to_fun_X_pow x_car by blast
            then have "P \<bullet> x = (\<pp>[^](3::nat)) \<otimes>(x[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<one>"
              using "0" UPQ.to_fun_one x_car by presburger
            then show ?thesis
              using y_def Qp.add.m_comm Qp.one_closed local.monom_term_car p_natpow_closed(1) x_car
              by presburger
          qed
          then show ?thesis
            using y_def
            by blast
        qed
        then show ?thesis
          unfolding  univ_basic_semialg_set_def
          using x_car
          by blast
      qed
    qed
    show "univ_basic_semialg_set 2 P \<subseteq> \<O>\<^sub>p"
    proof fix x
      assume A: "x \<in> univ_basic_semialg_set (2::nat) P"
      then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> (P \<bullet> x) = (y[^](2::nat))"
        unfolding univ_basic_semialg_set_def
        by blast
      have x_car: "x \<in> carrier Q\<^sub>p"
        using A
        by (metis (no_types, lifting) mem_Collect_eq univ_basic_semialg_set_def)
      have 0: "(P \<bullet> x) = (\<pp>[^](3::nat)) \<otimes> (x[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<one>"
        using P_def x_car UPQ.UP_one_closed UPQ.monom_closed UPQ.monom_rep_X_pow UPQ.to_fun_monom
          UPQ.to_fun_one UPQ.to_fun_plus p_natpow_closed(1) by presburger
      have 1: "y \<in> carrier Q\<^sub>p \<and> (\<pp>[^](3::nat)) \<otimes> (x[^](4::nat)) \<oplus>\<^bsub>Q\<^sub>p\<^esub> \<one> = (y[^](2::nat))"
        using "0" y_def
        by blast
      then show "x \<in> \<O>\<^sub>p"
        using x_car Qp_val_ring_alt_def[of x] y_def
        by (metis Qp.add.m_comm Qp.one_closed local.monom_term_car p_natpow_closed(1))
    qed
  qed
  show ?thesis
    using 0 1 that
    by blast
qed

lemma Qp_val_ring_is_univ_semialgebraic:
"is_univ_semialgebraic \<O>\<^sub>p"
proof-
  obtain P where "P \<in> carrier Q\<^sub>p_x \<and> \<O>\<^sub>p = univ_basic_semialg_set 2 P"
    using Qp_val_ring_is_semialg by blast
  then show ?thesis
    by (metis univ_basic_semialg_set_is_univ_semialgebraic zero_neq_numeral)
qed

lemma Qp_val_ring_is_semialgebraic:
"is_semialgebraic 1 (to_R1` \<O>\<^sub>p)"
  using Qp_val_ring_is_univ_semialgebraic is_univ_semialgebraic_def by blast

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Inverse Images of Semialgebraic Sets by Polynomial Maps\<close>
      (********************************************************************************************)
      (********************************************************************************************)

lemma basic_semialg_pullback:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>k\<^esub>])"
  assumes "is_poly_tuple n fs"
  assumes "length fs = k"
  assumes "S = basic_semialg_set k m f"
  assumes "m  \<noteq>0"
  shows "poly_map n fs  \<inverse>\<^bsub>n\<^esub> S = basic_semialg_set n m (Qp_poly_comp n fs f)"
proof
  show "poly_map n fs  \<inverse>\<^bsub>n\<^esub> S \<subseteq> basic_semialg_set n m (Qp_poly_comp n fs f)"
  proof
    fix x
    assume A: "x \<in> poly_map n fs  \<inverse>\<^bsub>n\<^esub> S"
    then have 0: "poly_map n fs x \<in> S"
    proof -
      have "\<exists>n f. {rs. rs \<in> S} \<subseteq> {rs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>). \<exists>r. r \<in> carrier Q\<^sub>p \<and> Qp_ev f rs = (r[^](n::nat))}"
        by (metis (no_types) Collect_mem_eq \<open>S = basic_semialg_set k m f\<close> basic_semialg_set_def eq_iff)
      then show ?thesis
        using A by blast
    qed
    have 1: "x \<in> carrier  (Q\<^sub>p\<^bsup>n\<^esup>)"
      using A assms
      by (meson evimage_eq)
    have "\<exists>y \<in> (carrier Q\<^sub>p). Qp_ev f (poly_map n fs x) = (y[^]m)"
      using A 0 assms basic_semialg_set_def
      by blast
    then have "\<exists>y \<in> (carrier Q\<^sub>p). Qp_ev (Qp_poly_comp n fs f) x = (y[^]m)"
      using 1 assms Qp_poly_comp_eval
      by blast
    then show "x \<in> basic_semialg_set n m (Qp_poly_comp n fs f)"
      using "1" basic_semialg_set_def
      by blast
  qed
  show "basic_semialg_set n m (Qp_poly_comp n fs f) \<subseteq> poly_map n fs  \<inverse>\<^bsub>n\<^esub> S"
  proof fix x
    assume A: "x \<in> basic_semialg_set n m (Qp_poly_comp n fs f)"
    have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using A basic_semialg_set_def
      by blast
    have 1: "(poly_map n fs x) \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
      using "0" poly_map_closed assms(2) assms(3)  by blast
    show "x \<in> poly_map n fs  \<inverse>\<^bsub>n\<^esub> S"
    proof-
      have "\<exists>y \<in> carrier Q\<^sub>p. Qp_ev (Qp_poly_comp n fs f) x = (y[^]m)"
        using A basic_semialg_set_def
        by blast
      then have 2: "\<exists>y \<in> carrier Q\<^sub>p. Qp_ev f (poly_map n fs x) = (y[^]m)"
        using assms Qp_poly_comp_eval
        by (metis (no_types, lifting) A basic_semialg_set_def mem_Collect_eq)
      have 3: "poly_map n fs x \<in> S"
        using assms 0 1 basic_semialg_set_def[of k m f] "2"
        by blast
      show ?thesis
        using "0" "3" by blast
    qed
  qed
qed

lemma basic_semialg_pullback':
  assumes "is_poly_tuple n fs"
  assumes "length fs = k"
  assumes "A \<in> basic_semialgs k"
  shows "poly_map n fs  \<inverse>\<^bsub>n\<^esub> A \<in> (basic_semialgs n)"
proof-
  obtain f m where fm_def: "m \<noteq>0 \<and>f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>k\<^esub>]) \<and> A = basic_semialg_set k m f"
    using assms
    by (metis is_basic_semialg_def mem_Collect_eq)
  then have "poly_map n fs  \<inverse>\<^bsub>n\<^esub> A  = basic_semialg_set n m (Qp_poly_comp n fs f)"
    using assms basic_semialg_pullback[of f k n fs A m]
    by linarith
  then show ?thesis unfolding is_basic_semialg_def
    by (metis (mono_tags, lifting) assms(1) assms(2) fm_def mem_Collect_eq poly_compose_closed)
qed

lemma semialg_pullback:
  assumes "is_poly_tuple n fs"
  assumes "length fs = k"
  assumes "S \<in> semialg_sets k"
  shows "poly_map n fs  \<inverse>\<^bsub>n\<^esub> S \<in> semialg_sets n"
  unfolding semialg_sets_def
  apply(rule gen_boolean_algebra.induct[of S "(carrier (Q\<^sub>p\<^bsup>k\<^esup>))" "basic_semialgs k"])
  using assms semialg_sets_def apply blast
  apply (metis assms(1) assms(2) carrier_is_semialgebraic evimageI2 extensional_vimage_closed is_semialgebraicE poly_map_closed semialg_sets_def subsetI subset_antisym)
  apply (metis Int_absorb2 assms(1) assms(2) basic_semialg_is_semialg basic_semialg_is_semialgebraic basic_semialg_pullback' is_semialgebraic_closed mem_Collect_eq semialg_sets_def)
  apply (metis evimage_Un semialg_sets_def semialg_union)
  by (metis assms(1) assms(2) carrier_is_semialgebraic diff_is_semialgebraic evimage_Diff extensional_vimage_closed is_semialgebraicE is_semialgebraicI poly_map_closed poly_map_pullbackI semialg_sets_def subsetI subset_antisym)

lemma pullback_is_semialg:
  assumes "is_poly_tuple n fs"
  assumes "length fs = k"
  assumes "S \<in> semialg_sets k"
  shows "is_semialgebraic n (poly_map n fs  \<inverse>\<^bsub>n\<^esub> S)"
  using assms(1) assms(2) assms(3)  is_semialgebraicI padic_fields_axioms semialg_pullback
  by blast

text\<open>Equality and inequality sets for a pair of polynomials\<close>

definition val_ineq_set where
"val_ineq_set n f g = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)}"

lemma poly_map_length :
  assumes "length fs = m"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "length (poly_map n fs as) = m"
  using assms unfolding poly_map_def poly_tuple_eval_def
  by (metis (no_types, lifting) length_map restrict_apply')

lemma val_ineq_set_pullback:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "val_ineq_set n f g = poly_map n [g,f] \<inverse>\<^bsub>n\<^esub> val_relation_set "
proof
  show "val_ineq_set n f g \<subseteq> poly_map n [g,f]  \<inverse>\<^bsub>n\<^esub> val_relation_set"
  proof
    fix x
    assume "x \<in> val_ineq_set n f g"
    then have 0: "x \<in>  carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> val (Qp_ev f x) \<le> val (Qp_ev g x)"
      by (metis (mono_tags, lifting) mem_Collect_eq val_ineq_set_def)
    have 1: "poly_map n [g,f] x = [Qp_ev g x, Qp_ev f x]"
      unfolding  poly_map_def poly_tuple_eval_def  using 0
      by (metis (no_types, lifting) Cons_eq_map_conv list.simps(8) restrict_apply')
    have 2: "poly_map n [g,f] x \<in> val_relation_set"
      apply(rule val_relation_setI)
      using 1 0 assms  apply (metis eval_at_point_closed nth_Cons_0)
      using 1 0 assms  apply (metis One_nat_def eval_at_point_closed diff_Suc_1 less_numeral_extra(1) nth_Cons_pos Qp.to_R_to_R1)
      using poly_map_length assms 0  apply (metis "1" Qp_2I cartesian_power_car_memE eval_at_point_closed)
      by (metis "0" "1" One_nat_def nth_Cons_0 nth_Cons_Suc)
    have 3: "is_poly_tuple n [g, f]"
      using assms
      by (smt One_nat_def diff_Suc_1 Qp_is_poly_tupleI length_Suc_conv less_SucE less_one list.size(3) nth_Cons')
    then show "x \<in> poly_map n [g,f]  \<inverse>\<^bsub>n\<^esub> val_relation_set"
      using 0 1 2
      by blast
  qed
  show "poly_map n [g,f] \<inverse>\<^bsub>n\<^esub> val_relation_set \<subseteq> val_ineq_set n f g"
  proof fix x
    have 0: "is_poly_tuple n [g, f]"
      using Qp_is_poly_tupleI assms
      by (metis (no_types, lifting) diff_Suc_1 length_Cons less_Suc0 less_SucE list.size(3) nth_Cons')
    assume A: "x \<in> poly_map n [g,f] \<inverse>\<^bsub>n\<^esub> val_relation_set"
    then have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> poly_map n [g,f] x \<in> val_relation_set"
      using 0
      by (meson evimageD extensional_vimage_closed subsetD)
    have 2: "poly_map n [g,f] x = [Qp_ev g x, Qp_ev f x]"
      by (metis "1" Qp_poly_mapE' length_0_conv poly_map_cons)
    show "x \<in> val_ineq_set n f g"
       using 0 1 2 unfolding val_ineq_set_def  val_relation_set_def
       by (metis (no_types, lifting) "1" list.inject mem_Collect_eq nth_Cons_0 poly_map_apply val_relation_setE)
   qed
qed

lemma val_ineq_set_is_semialg:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "val_ineq_set n f g \<in> semialg_sets n"
proof-
  have 0: "val_relation_set \<in> semialg_sets 2"
    using val_relation_semialg basic_semialg_is_semialg'
    by (metis Qp_val_poly_closed zero_neq_numeral)
  show ?thesis using val_ineq_set_pullback semialg_pullback[of n "[g,f]" 2 "val_relation_set" ]
    by (metis (no_types, lifting) "0" assms(1) assms(2) diff_Suc_1 Qp_is_poly_tupleI
        length_Cons less_Suc0 less_SucE list.size(3) nth_Cons_0 nth_Cons_pos numeral_2_eq_2
        zero_neq_numeral)
qed

lemma val_ineq_set_is_semialgebraic:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n (val_ineq_set n f g)"
  using assms(1) assms(2) is_semialgebraicI val_ineq_set_is_semialg by blast

lemma val_ineq_setI:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "x \<in> (val_ineq_set n f g)"
  shows "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        "val (Qp_ev f x) \<le> val (Qp_ev g x)"
  using assms unfolding val_ineq_set_def  apply blast
  using assms unfolding val_ineq_set_def by blast

lemma val_ineq_setE:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes      "val (Qp_ev f x) \<le> val (Qp_ev g x)"
  shows "x \<in> (val_ineq_set n f g)"
  using assms unfolding val_ineq_set_def
  by blast

lemma val_ineq_set_is_semialgebraic':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)}"
  using assms val_ineq_set_is_semialgebraic unfolding val_ineq_set_def by blast

lemma val_eq_set_is_semialgebraic:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = val (Qp_ev g x)}"
proof-
  have 0: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)}"
    using assms val_ineq_set_is_semialgebraic unfolding val_ineq_set_def
    by blast
  have 1: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) \<le> val (Qp_ev f x)}"
    using assms val_ineq_set_is_semialgebraic unfolding val_ineq_set_def
    by blast
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = val (Qp_ev g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)} \<inter>
                                                   {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) \<le>  val (Qp_ev f x)}"
    apply(rule equalityI, rule  subsetI , rule IntI) unfolding mem_Collect_eq
    using le_less apply blast apply (metis order_refl)
    apply(rule  subsetI, erule IntE) unfolding mem_Collect_eq
    by (meson less_le_trans not_less_iff_gr_or_eq)
  show ?thesis unfolding 2 apply(rule intersection_is_semialg)
    using 0 apply blast using 1 by blast
qed

lemma equalityI'':
  assumes "\<And>x. A x \<Longrightarrow> B x"
  assumes "\<And>x. B x \<Longrightarrow> A x"
  shows "{x. A x} = {x. B x}"
  using assms by blast

lemma val_strict_ineq_set_is_semialgebraic:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) < val (Qp_ev g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) < val (Qp_ev g x)} =
             {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)} - {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = val (Qp_ev g x)}"
    apply(rule equalityI', rule DiffI) unfolding le_less mem_Collect_eq  apply blast
    unfolding mem_Collect_eq using neq_iff apply blast
    apply(erule DiffE) unfolding mem_Collect_eq by blast
  show ?thesis unfolding 0
    apply(rule diff_is_semialgebraic)
    using assms val_ineq_set_is_semialgebraic[of f n g] unfolding val_ineq_set_def apply blast
    using assms val_eq_set_is_semialgebraic[of f n g] unfolding val_ineq_set_def by blast
qed

lemma constant_poly_val_exists:
  shows "\<exists>g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]). (\<forall> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) = c)"
proof-
  obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> val a = c"
    by (meson Qp.minus_closed Qp.nonzero_closed dist_nonempty' p_nonzero)
  obtain g where g_def: "g = coord_const a"
    by blast
  show ?thesis using a_def g_def Qp_to_IP_car
    by (metis (no_types, opaque_lifting) Qp_to_IP_car a_def eval_at_point_const g_def le_less subset_iff)
qed

lemma val_ineq_set_is_semialgebraic'':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> c}"
proof-
  obtain g where g_def: "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> (\<forall> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) = c)"
    using constant_poly_val_exists by blast
  have 0: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)}"
    apply(rule val_ineq_set_is_semialgebraic')
    using assms apply blast using  g_def by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> val (Qp_ev g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) \<le> c}"
    apply(rule equalityI'') using g_def apply fastforce using g_def by fastforce
  show ?thesis using 0 unfolding 1 by blast
qed

lemma val_ineq_set_is_semialgebraic''':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). c \<le> val (Qp_ev f x)}"
proof-
  obtain g where g_def: "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> (\<forall> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) = c)"
    using constant_poly_val_exists by blast
  have 0: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) \<le> val (Qp_ev f x)}"
    apply(rule val_ineq_set_is_semialgebraic')
     using  g_def apply blast using assms by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) \<le> val (Qp_ev f x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>).  c \<le> val (Qp_ev f x)}"
    apply(rule equalityI'') using g_def apply fastforce using g_def by fastforce
  show ?thesis using 0 unfolding 1 by blast
qed

lemma val_eq_set_is_semialgebraic':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = c}"
proof-
  obtain g where g_def: "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> (\<forall> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) = c)"
    using constant_poly_val_exists by blast
  have 0: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = val (Qp_ev g x)}"
    apply(rule val_eq_set_is_semialgebraic)
    using assms apply blast using  g_def by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = val (Qp_ev g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) = c}"
    apply(rule equalityI'') using g_def apply fastforce using g_def by metis
  show ?thesis using 0 unfolding 1 by blast
qed

lemma val_strict_ineq_set_is_semialgebraic':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) < c}"
proof-
  obtain g where g_def: "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> (\<forall> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) = c)"
    using constant_poly_val_exists by blast
  have 0: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) < val (Qp_ev g x)}"
    apply(rule val_strict_ineq_set_is_semialgebraic)
    using assms apply blast using  g_def by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) < val (Qp_ev g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev f x) < c}"
    apply(rule equalityI'') using g_def apply fastforce using g_def
    by fastforce
  show ?thesis using 0 g_def unfolding 1
    by blast
qed

lemma val_strict_ineq_set_is_semialgebraic'':
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). c < val (Qp_ev f x)}"
proof-
  obtain g where g_def: "g \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> (\<forall> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) = c)"
    using constant_poly_val_exists by blast
  have 0: "is_semialgebraic n {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>).  val (Qp_ev g x) < val (Qp_ev f x)}"
    apply(rule val_strict_ineq_set_is_semialgebraic)
    using   g_def apply blast using assms  by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). val (Qp_ev g x) < val (Qp_ev f x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). c < val (Qp_ev f x)}"
    apply(rule equalityI'') using assms g_def apply fastforce using assms g_def by fastforce
  show ?thesis using 0 g_def unfolding 1
    by blast
qed

lemma(in cring) R1_memE:
  assumes "x \<in> carrier (R\<^bsup>1\<^esup>)"
  shows "x = [(hd x)]"
  using assms cartesian_power_car_memE
  by (metis diff_is_0_eq' hd_conv_nth le_eq_less_or_eq length_0_conv length_tl list.exhaust list.sel(3) normalize.cases nth_Cons_0 zero_neq_one)

lemma(in cring) R1_memE':
 assumes "x \<in> carrier (R\<^bsup>1\<^esup>)"
 shows "hd x \<in> carrier R"
  using R1_memE assms cartesian_power_car_memE[of x R 1] cartesian_power_car_memE'[of x R 1 0]
  by (metis hd_conv_nth less_numeral_extra(1) list.size(3) zero_neq_one)

lemma univ_val_ineq_set_is_univ_semialgebraic:
"is_univ_semialgebraic {x \<in> carrier Q\<^sub>p. val x \<le> c}"
proof-
  have 0: "is_semialgebraic 1 {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (Qp_ev (pvar Q\<^sub>p 0) x) \<le> c}"
    apply(rule val_ineq_set_is_semialgebraic'')
    using pvar_closed by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (Qp_ev (pvar Q\<^sub>p 0) x) \<le> c} = to_R1 ` {x \<in> carrier Q\<^sub>p. val x \<le> c}"
  proof(rule equalityI')
    show " \<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) \<le> c} \<Longrightarrow> x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x \<le> c}"
    proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) \<le> c}"
      then have 0: "x = [(hd x)] \<and> hd x \<in> carrier Q\<^sub>p"
        using Qp.R1_memE Qp.R1_memE' by blast
      have 1: "eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0) = hd x"
        using A 0
        by (metis (no_types, lifting) One_nat_def eval_pvar lessI nth_Cons_0 Qp.to_R1_closed)
      then show "x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x \<le> c}"
        using A 0 unfolding mem_Collect_eq
        by (metis (no_types, lifting) image_iff mem_Collect_eq)
    qed
    show "\<And>x. x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x \<le> c} \<Longrightarrow> x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) \<le> c}"
    proof fix x assume A: "x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x \<le> c} "
      then obtain a where a_def: "x = [a] \<and> a \<in> carrier Q\<^sub>p \<and> val a \<le> c"
        by blast
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using cartesian_power_car_memI Qp.to_R1_closed by presburger
      then have 1: "(eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = a"
        using a_def  by (metis eval_pvar less_one Qp.to_R_to_R1)
      show "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>) \<and> val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) \<le> c"
        unfolding 1 using a_def 0 by blast
    qed
  qed
  show ?thesis using 0 unfolding 1
    using is_univ_semialgebraicI by blast
qed

lemma univ_val_strict_ineq_set_is_univ_semialgebraic:
"is_univ_semialgebraic {x \<in> carrier Q\<^sub>p. val x < c}"
proof-
  have 0: "is_semialgebraic 1 {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (Qp_ev (pvar Q\<^sub>p 0) x) <c}"
    apply(rule val_strict_ineq_set_is_semialgebraic')
    using pvar_closed by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (Qp_ev (pvar Q\<^sub>p 0) x) < c} = to_R1 ` {x \<in> carrier Q\<^sub>p. val x < c}"
  proof(rule equalityI')
    show " \<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) < c} \<Longrightarrow> x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x < c}"
    proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) < c}"
      then have 0: "x = [(hd x)] \<and> hd x \<in> carrier Q\<^sub>p"
        using Qp.R1_memE Qp.R1_memE' by blast
      have 1: "eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0) = hd x"
        using A 0
        by (metis (no_types, lifting) One_nat_def eval_pvar lessI nth_Cons_0 Qp.to_R1_closed)
      then show "x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x < c}"
        using A 0 unfolding mem_Collect_eq
        by (metis (no_types, lifting) image_iff mem_Collect_eq)
    qed
    show "\<And>x. x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x < c} \<Longrightarrow> x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) < c}"
    proof fix x assume A: "x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x < c} "
      then obtain a where a_def: "x = [a] \<and> a \<in> carrier Q\<^sub>p \<and> val a < c"
        by blast
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using cartesian_power_car_memI Qp.to_R1_closed by presburger
      then have 1: "(eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = a"
        using a_def  by (metis eval_pvar less_one Qp.to_R_to_R1)
      show "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>) \<and> val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) < c"
        unfolding 1 using a_def 0 by blast
    qed
  qed
  show ?thesis using 0 unfolding 1
    using is_univ_semialgebraicI by blast
qed

lemma univ_val_eq_set_is_univ_semialgebraic:
"is_univ_semialgebraic {x \<in> carrier Q\<^sub>p. val x = c}"
proof-
  have 0: "is_semialgebraic 1 {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (Qp_ev (pvar Q\<^sub>p 0) x) = c}"
    apply(rule val_eq_set_is_semialgebraic')
    using pvar_closed by blast
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (Qp_ev (pvar Q\<^sub>p 0) x) = c} = to_R1 ` {x \<in> carrier Q\<^sub>p. val x = c}"
  proof(rule equalityI')
    show " \<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = c} \<Longrightarrow> x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x = c}"
    proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = c}"
      then have 0: "x = [(hd x)] \<and> hd x \<in> carrier Q\<^sub>p"
        using Qp.R1_memE Qp.R1_memE' by blast
      have 1: "eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0) = hd x"
        using A 0
        by (metis (no_types, lifting) One_nat_def eval_pvar lessI nth_Cons_0 Qp.to_R1_closed)
      show "x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x = c}"
        using A 0 unfolding mem_Collect_eq 1 by blast
    qed
    show "\<And>x. x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x = c} \<Longrightarrow> x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>). val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = c}"
    proof fix x assume A: "x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. val x = c} "
      then obtain a where a_def: "x = [a] \<and> a \<in> carrier Q\<^sub>p \<and> val a = c"
        by blast
      then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using cartesian_power_car_memI Qp.to_R1_closed by presburger
      then have 1: "(eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = a"
        using a_def  by (metis eval_pvar less_one Qp.to_R_to_R1)
      show "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>) \<and> val (eval_at_point Q\<^sub>p x (pvar Q\<^sub>p 0)) = c"
        unfolding 1 using a_def 0 by blast
    qed
  qed
  show ?thesis using 0 unfolding 1
    using is_univ_semialgebraicI by blast
qed


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>One Dimensional $p$-adic Balls are Semialgebraic\<close>
      (********************************************************************************************)
      (********************************************************************************************)

lemma coord_ring_one_def:
"Pring Q\<^sub>p {(0::nat)} = (Q\<^sub>p[\<X>\<^bsub>1\<^esub>])"
proof-
  have "{(0::nat)} = {..<1}"
    by auto
  thus ?thesis
  unfolding coord_ring_def
  by auto
qed

lemma times_p_pow_val:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b = \<pp>[^]n \<otimes> a"
  shows "val b = val a + n"
  using  val_mult[of "\<pp>[^]n" a] assms unfolding assms(2) val_p_int_pow
  by (metis add.commute p_intpow_closed(1))

lemma times_p_pow_neg_val:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b = \<pp>[^]-n \<otimes> a"
  shows "val b = val a - n"
  by (metis Qp.m_comm Qp_int_pow_nonzero assms(1) assms(2) p_intpow_closed(1) p_intpow_inv'' p_nonzero val_fract val_p_int_pow)

lemma eint_minus_int_pos:
  assumes "a - eint n \<ge> 0"
  shows "a \<ge> n"
  using assms apply(induction a)
  apply (metis diff_ge_0_iff_ge eint_ord_simps(1) idiff_eint_eint zero_eint_def)
  by simp

text\<open>\<open>p\<close>-adic balls as pullbacks of polynomial maps\<close>

lemma balls_as_pullbacks:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "\<exists>P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>]). to_R1` B\<^bsub>n\<^esub>[c] = poly_map 1 [P]  \<inverse>\<^bsub>1\<^esub> (to_R1 ` \<O>\<^sub>p)"
proof-
  obtain P0 where P0_def: "P0 = (to_poly (\<pp>[^](-n))) \<otimes>\<^bsub>Q\<^sub>p_x\<^esub>((X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c)"
    by blast
  have 0: "P0 \<in> carrier Q\<^sub>p_x"
  proof-
    have P0: "(X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c \<in> carrier Q\<^sub>p_x"
      using UPQ.X_closed UPQ.to_poly_closed assms by blast
    have P1: "(to_poly (\<pp>[^](-n))) \<in> carrier Q\<^sub>p_x"
      using UPQ.to_poly_closed p_intpow_closed(1) by blast
    then show ?thesis
      using P0_def P0 P1
      by blast
  qed
  have 1: "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> P0 \<bullet> x = (\<pp>[^](-n)) \<otimes>  (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
  proof- fix x assume A: "x \<in> carrier Q\<^sub>p"
    have P0: "(to_poly (\<pp>[^](-n))) \<bullet> x = (\<pp>[^](-n))"
      using A UPQ.to_fun_to_poly p_intpow_closed(1) by blast
    have P1: "((X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c) \<bullet> x =  (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
      by (metis A UPQ.to_fun_X_minus X_poly_minus_def assms)
    have P2: "to_poly (\<pp>[^](-n)) \<in> carrier Q\<^sub>p_x"
      using UPQ.to_poly_closed p_intpow_closed(1) by blast
    have P3: "((X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c) \<in> carrier Q\<^sub>p_x"
      using UPQ.X_closed UPQ.to_poly_closed assms by blast
    have "to_poly (\<pp>[^]- n) \<otimes>\<^bsub>Q\<^sub>p_x\<^esub> ((X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c) \<bullet> x = to_poly (\<pp>[^]- n) \<bullet> x \<otimes> (((X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c) \<bullet> x)"
      using A P0_def P0 P1 P2 P3 to_fun_mult[of "to_poly (\<pp>[^](-n))" "(X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c" x] UPQ.to_fun_mult
      by blast
    then have "to_poly (\<pp>[^]- n) \<otimes>\<^bsub>Q\<^sub>p_x\<^esub> ((X_poly Q\<^sub>p) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> to_poly c) \<bullet> x = (\<pp>[^](-n)) \<otimes>  (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) "
      by (metis P0 P1)
    then show "P0 \<bullet> x = (\<pp>[^](-n)) \<otimes>  (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
      using P0_def by metis
  qed
  have 2: " (\<lambda>a. [a]) ` B\<^bsub>n\<^esub>[c] = poly_map 1  [from_Qp_x P0]  \<inverse>\<^bsub>1\<^esub>  ((\<lambda>a. [a]) ` \<O>\<^sub>p)"
  proof
    show "(\<lambda>a. [a]) ` B\<^bsub>n\<^esub>[c] \<subseteq> poly_map 1  [from_Qp_x P0]  \<inverse>\<^bsub>1\<^esub>  ((\<lambda>a. [a]) ` \<O>\<^sub>p)"
    proof
      fix x
      assume A: "x \<in> (\<lambda>a. [a]) ` B\<^bsub>n\<^esub>[c]"
      then obtain a where a_def: "x = [a] \<and> a \<in> B\<^bsub>n\<^esub>[c]"
        by blast
      have P0: "P0 \<bullet> a \<in> \<O>\<^sub>p"
      proof-
        have "B\<^bsub>n\<^esub>[c] \<subseteq> carrier Q\<^sub>p"
          using c_ball_in_Qp by blast
        hence a_closed: "a \<in> carrier Q\<^sub>p"
          using a_def by blast
        have P0: "P0 \<bullet> a = (\<pp>[^](-n)) \<otimes>  (a \<ominus> c)"
          using 1 a_def c_ballE(1)
          by blast
        then have P1: "val (P0 \<bullet> a) = val (\<pp>[^](-n)) + val (a \<ominus> c)"
          using val_mult[of "\<pp>[^]-n" "a \<ominus> c"] a_closed assms Qp.minus_closed p_intpow_closed(1)
          by presburger
         then have P2: "val (P0 \<bullet> a) = val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) - n"
           by (metis P0 Qp.m_comm Qp.minus_closed Qp_int_pow_nonzero assms local.a_closed
               p_intpow_closed(1) p_intpow_inv'' p_nonzero val_fract val_p_int_pow)
         have P3: "val (a \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<ge> n"
           using a_def c_ballE(2)
           by blast
         then have "val (P0 \<bullet> a) \<ge> -n + n"
           using P2 by (metis add.commute diff_conv_add_uminus diff_self local.eint_minus_ineq' zero_eint_def)
         then have P4: "val (P0 \<bullet> a) \<ge> 0"
           by (metis add.commute add.right_inverse zero_eint_def)
         have P5: "P0 \<bullet> a \<in> carrier Q\<^sub>p"
           using "0" UPQ.to_fun_closed local.a_closed by blast
         then show ?thesis using P4
           using val_ring_val_criterion
           by blast
      qed
      have "poly_map 1 [from_Qp_x P0] x = [Qp_ev (from_Qp_x P0) [a]] "
        using a_def poly_map_def[of 1 "[from_Qp_x P0]"] poly_tuple_eval_def[of ]
        by (metis Qp_poly_mapE' c_ballE(1) length_0_conv poly_map_cons Qp.to_R1_closed)
      then have "poly_map 1 [from_Qp_x P0] x = [P0 \<bullet> a] "
        using Qp_x_Qp_poly_eval[of P0 a]
        by (metis "0" a_def c_ballE(1))
      then have P1: "poly_map 1 [from_Qp_x P0] x \<in> ((\<lambda>a. [a]) ` \<O>\<^sub>p)"
        using P0
        by blast
      have P2: "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using A c_ballE(1) Qp.to_R1_closed
        by blast
      have P3: "is_poly_tuple 1 [from_Qp_x P0]"
        apply(rule Qp_is_poly_tupleI)
        by (metis "0" Qp_is_poly_tupleI from_Qp_x_closed gr_implies_not0 is_poly_tupleE is_poly_tuple_Cons list.size(3) zero_neq_one)
      show "x \<in> poly_map 1 [UP_to_IP Q\<^sub>p 0 P0] \<inverse>\<^bsub>1\<^esub> (\<lambda>a. [a]) ` \<O>\<^sub>p"
        using P3 P2 P1 unfolding evimage_def poly_map_def
        by blast
    qed
    have 20: "is_poly_tuple 1 [from_Qp_x P0]"
      using 0 UP_to_IP_closed[of P0 "0::nat"]
      unfolding is_poly_tuple_def
      by (metis (no_types, lifting) empty_set from_Qp_x_closed list.simps(15) singletonD subset_code(1))
    show "poly_map 1 [UP_to_IP Q\<^sub>p 0 P0] \<inverse>\<^bsub>1\<^esub> (\<lambda>a. [a]) ` \<O>\<^sub>p \<subseteq> (\<lambda>a. [a]) ` B\<^bsub>n\<^esub>[c]"
    proof fix x assume A: "x \<in> poly_map 1 [UP_to_IP Q\<^sub>p 0 P0] \<inverse>\<^bsub>1\<^esub> ((\<lambda>a. [a]) ` \<O>\<^sub>p)"
      have A0: "(\<lambda>a. [a]) ` \<O>\<^sub>p \<subseteq> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using Qp_val_ring_is_univ_semialgebraic is_univ_semialgebraic_def Qp.to_R1_car_subset
              Qp_val_ring_is_semialgebraic is_semialgebraic_closed by presburger
      have "poly_map 1 [from_Qp_x P0] x \<in>  ((\<lambda>a. [a]) ` \<O>\<^sub>p)"
        using A0 A 20  by blast
      then obtain a where a_def:  "a \<in> \<O>\<^sub>p \<and> (poly_map 1 [from_Qp_x P0] x) = [a]"
        by blast
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using A
        by (meson evimage_eq)
      then obtain y where y_def: "x = [y] \<and> y \<in> carrier Q\<^sub>p"
        using A
        by (metis Qp.to_R1_to_R Qp.to_R_pow_closed)
      have "(poly_map 1 [from_Qp_x P0] x) = [(Qp_ev (from_Qp_x P0) [y])]"
        unfolding poly_map_def poly_tuple_eval_def using x_closed
        by (smt "20" One_nat_def length_Suc_conv list.size(3) nth_Cons_0 nth_map
            poly_tuple_eval_closed poly_tuple_eval_def restrict_apply' Qp.to_R1_to_R y_def zero_less_Suc)
      then have "(poly_map 1 [from_Qp_x P0] x) = [P0 \<bullet> y]"
        by (metis "0" Qp_x_Qp_poly_eval y_def)
      then have "[a] = [P0 \<bullet> y]"
        using a_def
        by presburger
      then have A1: "a =  (\<pp>[^](-n)) \<otimes>  (y \<ominus>\<^bsub>Q\<^sub>p\<^esub> c)"
        using 1[of y] y_def
        by blast
      have "y \<in> B\<^bsub>n\<^esub>[c]"
      proof-
        have B0: "val a =  val (y \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) - n"
          using A1 y_def Qp.minus_closed assms times_p_pow_neg_val by blast
        have B1: "val a \<ge> 0"
          using a_def val_ring_memE by blast
        then have  "val (y \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) - n \<ge> 0"
          using B0
          by metis
        then have  "val (y \<ominus>\<^bsub>Q\<^sub>p\<^esub> c) \<ge> n"
          using eint_minus_int_pos by blast
        then show "y \<in> B\<^bsub>n\<^esub>[c]"
          using c_ballI y_def by blast
      qed
      then show "x \<in> (\<lambda>a. [a]) ` B\<^bsub>n\<^esub>[c]"
        using y_def by blast
    qed
  qed
  then show ?thesis
    by (meson "0" from_Qp_x_closed)
qed

lemma ball_is_semialgebraic:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_semialgebraic 1 (to_R1` B\<^bsub>n\<^esub>[c])"
proof-
  obtain P where P_def: "P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1\<^esub>]) \<and> to_R1` B\<^bsub>n\<^esub>[c] = poly_map 1 [P]  \<inverse>\<^bsub>1\<^esub> (to_R1 ` \<O>\<^sub>p) "
    using assms balls_as_pullbacks[of c n] by meson
  have "is_poly_tuple 1 [P]"
    using P_def unfolding is_poly_tuple_def
    by (metis (no_types, opaque_lifting) list.inject list.set_cases neq_Nil_conv subset_code(1))
  then show ?thesis
    using assms P_def pullback_is_semialg[of 1 "[P]" 1 "((\<lambda>a. [a]) ` \<O>\<^sub>p) "]
    by (metis (mono_tags, lifting) One_nat_def
        Qp_val_ring_is_semialgebraic is_semialgebraic_def length_Suc_conv
        list.distinct(1) list.size(3))
qed

lemma ball_is_univ_semialgebraic:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "is_univ_semialgebraic (B\<^bsub>n\<^esub>[c])"
  using assms ball_is_semialgebraic c_ball_in_Qp is_univ_semialgebraic_def
  by presburger

abbreviation Qp_to_R1_set  where
"Qp_to_R1_set S \<equiv> to_R1 ` S"


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Finite Unions and Intersections of Semialgebraic Sets\<close>
      (********************************************************************************************)
      (********************************************************************************************)


definition are_semialgebraic where
"are_semialgebraic n Xs = (\<forall> x. x \<in> Xs \<longrightarrow> is_semialgebraic n x)"

lemma are_semialgebraicI:
  assumes "\<And>x. x \<in> Xs \<Longrightarrow> is_semialgebraic n x "
  shows "are_semialgebraic n Xs"
  using are_semialgebraic_def assms by blast

lemma are_semialgebraicE:
  assumes "are_semialgebraic n Xs"
  assumes "x \<in> Xs"
  shows "is_semialgebraic n x"
  using are_semialgebraic_def assms(1) assms(2) by blast

definition are_univ_semialgebraic where
"are_univ_semialgebraic Xs = (\<forall> x. x \<in> Xs \<longrightarrow> is_univ_semialgebraic x)"

lemma are_univ_semialgebraicI:
  assumes "\<And>x. x \<in> Xs \<Longrightarrow> is_univ_semialgebraic x "
  shows "are_univ_semialgebraic Xs"
  using are_univ_semialgebraic_def assms by blast

lemma are_univ_semialgebraicE:
  assumes "are_univ_semialgebraic Xs"
  assumes "x \<in> Xs"
  shows "is_univ_semialgebraic x"
  using are_univ_semialgebraic_def assms(1) assms(2) by blast

lemma are_univ_semialgebraic_semialgebraic:
  assumes "are_univ_semialgebraic Xs"
  shows "are_semialgebraic 1 (Qp_to_R1_set ` Xs)"
  apply(rule  are_semialgebraicI)
  using  are_univ_semialgebraicE assms image_iff is_univ_semialgebraicE
  by (metis (no_types, lifting))

lemma to_R1_set_union:
"to_R1 ` (\<Union> Xs) = \<Union> (Qp_to_R1_set ` Xs)"
  using image_iff by blast

lemma to_R1_inter:
  assumes "Xs \<noteq> {}"
  shows "to_R1 ` (\<Inter> Xs) = \<Inter> (Qp_to_R1_set ` Xs)"
proof
  show "to_R1 ` (\<Inter> Xs)  \<subseteq> \<Inter> (Qp_to_R1_set ` Xs)"
    by blast
  show "\<Inter> (Qp_to_R1_set ` Xs) \<subseteq> to_R1 ` (\<Inter> Xs)"
  proof fix x
    assume  A: "x \<in> \<Inter> (Qp_to_R1_set ` Xs)"
    then have 0: "\<And>S. S \<in> Xs \<Longrightarrow> x \<in> (Qp_to_R1_set S)"
      by blast
    obtain S where "S \<in> Xs \<and> x \<in> (Qp_to_R1_set S)"
      using assms 0
      by blast
    then obtain b where b_def: "b \<in> S \<and> x = [b]"
      by blast
    have "b \<in> (\<Inter> Xs)"
      using "0" b_def by blast
    then show "x \<in> to_R1 ` (\<Inter> Xs)"
      using b_def by blast
  qed
qed

lemma finite_union_is_semialgebraic:
  assumes "finite Xs"
  shows "Xs \<subseteq> semialg_sets n \<longrightarrow> is_semialgebraic n (\<Union> Xs)"
  apply(rule finite.induct[of Xs])
    apply (simp add: assms)
  apply (simp add: empty_is_semialgebraic)
  by (metis Sup_insert insert_subset is_semialgebraicI union_is_semialgebraic)

lemma finite_union_is_semialgebraic':
  assumes "finite Xs"
  assumes "Xs \<subseteq> semialg_sets n "
  shows "is_semialgebraic n (\<Union> Xs)"
  using assms(1) assms(2) finite_union_is_semialgebraic by blast

lemma(in padic_fields) finite_union_is_semialgebraic'':
  assumes "finite S"
  assumes  "\<And>x. x \<in> S \<Longrightarrow> is_semialgebraic m (F x)"
  shows "is_semialgebraic m (\<Union> x \<in> S. F x)"
  using assms  finite_union_is_semialgebraic[of "F`S" m] unfolding is_semialgebraic_def
  by blast

lemma finite_union_is_univ_semialgebraic':
  assumes "finite Xs"
  assumes "are_univ_semialgebraic Xs"
  shows "is_univ_semialgebraic (\<Union> Xs)"
proof-
  have "is_semialgebraic 1 (Qp_to_R1_set (\<Union> Xs))"
    using assms finite_union_is_semialgebraic'[of "((`) (\<lambda>a. [a]) ` Xs)"] to_R1_set_union[of Xs]
    by (metis (no_types, lifting) are_semialgebraicE are_univ_semialgebraic_semialgebraic
        finite_imageI is_semialgebraicE subsetI)
  then show ?thesis
    using is_univ_semialgebraicI by blast
qed

lemma finite_intersection_is_semialgebraic:
  assumes "finite Xs"
  shows "Xs \<subseteq> semialg_sets n \<and> Xs \<noteq>{} \<longrightarrow> is_semialgebraic n (\<Inter> Xs)"
  apply(rule finite.induct[of Xs])
  apply (simp add: assms)
  apply auto[1]
proof fix A::"((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list set set" fix a
  assume 0: "finite A"
  assume 1: "A \<subseteq> semialg_sets n \<and> A \<noteq> {} \<longrightarrow> is_semialgebraic n (\<Inter> A) "
  assume 2: "insert a A \<subseteq> semialg_sets n \<and> insert a A \<noteq> {}"
  show "is_semialgebraic n (\<Inter> (insert a A))"
  proof(cases "A = {}")
    case True
    then have "insert a A = {a}"
      by simp
    then show ?thesis
      by (metis "2" cInf_singleton insert_subset is_semialgebraicI)
  next
    case False
    then have "A \<subseteq> semialg_sets n \<and> A \<noteq> {}"
      using "2" by blast
    then have "is_semialgebraic n (\<Inter> A) "
      using "1" by linarith
    then show ?thesis
      using 0 1 2 intersection_is_semialg
      by (metis Inf_insert insert_subset is_semialgebraicI)
  qed
qed

lemma finite_intersection_is_semialgebraic':
  assumes "finite Xs"
  assumes "Xs \<subseteq> semialg_sets n \<and> Xs \<noteq>{}"
  shows  " is_semialgebraic n (\<Inter> Xs)"
  by (simp add: assms(1) assms(2) finite_intersection_is_semialgebraic)

lemma finite_intersection_is_semialgebraic'':
  assumes "finite Xs"
  assumes "are_semialgebraic n Xs \<and> Xs \<noteq>{}"
  shows  " is_semialgebraic n (\<Inter> Xs)"
  by (meson are_semialgebraicE assms(1) assms(2)
      finite_intersection_is_semialgebraic' is_semialgebraicE subsetI)

lemma finite_intersection_is_univ_semialgebraic:
  assumes "finite Xs"
  assumes "are_univ_semialgebraic Xs"
  assumes "Xs \<noteq> {}"
  shows  "is_univ_semialgebraic (\<Inter> Xs)"
proof-
  have "are_semialgebraic 1 (Qp_to_R1_set ` Xs)"
    using are_univ_semialgebraic_semialgebraic assms(2) by blast
  then have  "is_semialgebraic 1 (\<Inter> (Qp_to_R1_set ` Xs))"
    using assms finite_intersection_is_semialgebraic''[of "Qp_to_R1_set ` Xs" 1]
    by blast
  then  have "is_semialgebraic 1 (Qp_to_R1_set (\<Inter> Xs))"
    using assms  to_R1_inter[of Xs]
    by presburger
  then show ?thesis
    using is_univ_semialgebraicI by blast
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Cartesian Products of Semialgebraic Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma Qp_times_basic_semialg_right:
  assumes "a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) = basic_semialg_set (n+ m) k a"
proof
  show "cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<subseteq> basic_semialg_set (n + m) k a"
  proof fix x
    assume "x \<in> cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
    then obtain as bs where as_bs_def: "as \<in> (basic_semialg_set n k a) \<and> bs \<in> (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<and> x = as@bs"
      using cartesian_product_memE[of x "basic_semialg_set n k a" "carrier (Q\<^sub>p\<^bsup>m\<^esup>)" Q\<^sub>p n]
            basic_semialg_set_def
      by (metis (no_types, lifting) append_take_drop_id basic_semialg_set_memE(1) subsetI)
    have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n+m\<^esup>)"
      using as_bs_def basic_semialg_set_memE(1) cartesian_product_closed'
      by blast
    have 1: "(Qp_ev a x = Qp_ev a as)"
      using as_bs_def  poly_eval_cartesian_prod[of as n bs m a] assms basic_semialg_set_memE(1) by blast
    obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> (Qp_ev a as = (y[^]k))"
      using as_bs_def using basic_semialg_set_memE(2)[of as n k a] by blast
    show "x \<in> basic_semialg_set (n + m) k a"
      apply(rule basic_semialg_set_memI[of _ _ y])
        apply (simp add: "0")
       apply (simp add: y_def)
      using "1" y_def by blast
  qed
  show "basic_semialg_set (n + m) k a \<subseteq> cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
  proof fix x
    assume A: "x \<in> basic_semialg_set (n + m) k a"
    have A0: "x \<in> carrier (Q\<^sub>p\<^bsup>n+m\<^esup>)"
      using A basic_semialg_set_memE(1) by blast
    have A1: "set x \<subseteq> carrier Q\<^sub>p"
      using A0
      by (metis (no_types, lifting) cartesian_power_car_memE cartesian_power_car_memE' in_set_conv_nth subsetI)
    have A2: "length x = n + m"
      using A0 cartesian_power_car_memE
      by blast
    obtain as where as_def: "as = take n x"
      by blast
    obtain bs where bs_def: "bs = drop n x"
      by blast
    have 0:  "x = as@bs"
      using A as_def bs_def
        by (metis append_take_drop_id)
      have 1: "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        apply(rule cartesian_power_car_memI)
        using as_def A2
        apply (simp add: A2 min.absorb2)
        by (metis (no_types, lifting) A1 as_def dual_order.trans set_take_subset)
      have 2:  "bs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        apply(rule cartesian_power_car_memI)
        using bs_def A2
        apply (simp add: A2)
        by (metis A1 bs_def order.trans set_drop_subset)
      obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and>  Qp_ev a x = (y[^]k)"
        using basic_semialg_set_memE A by meson
      have 3: "as \<in> basic_semialg_set n k a"
        apply(rule basic_semialg_set_memI[of _ _ y])
          apply (simp add: "1")
        using \<open>y \<in> carrier Q\<^sub>p \<and> Qp_ev a x = (y[^]k)\<close> apply blast
        using y_def A 1 0 2 assms(1) poly_eval_cartesian_prod by blast
      show " x \<in> cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
        using 3 2 "0"
        by (metis (mono_tags, lifting) as_def basic_semialg_set_memE(1) bs_def cartesian_product_memI subsetI)
    qed
qed

lemma Qp_times_basic_semialg_right_is_semialgebraic:
  assumes "k > 0"
  assumes "a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic (n + m) (cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)))"
proof-
  have 0: "cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) = basic_semialg_set (n+ m) k a"
    using Qp_times_basic_semialg_right assms
    by presburger
  have 1: " a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n+m\<^esub>])"
    using assms poly_ring_car_mono'(2) by blast
  have 2: "is_semialgebraic (n + m) (basic_semialg_set (n + m) k a)"
    using  assms basic_semialg_is_semialgebraic'[of a "n+m" k "basic_semialg_set (n + m) k a"]
          "1" by blast
  show ?thesis
    using 0 2
    by metis
qed

lemma Qp_times_basic_semialg_right_is_semialgebraic':
  assumes "A \<in> basic_semialgs n"
  shows "is_semialgebraic (n + m) (cartesian_product A (carrier (Q\<^sub>p\<^bsup>m\<^esup>)))"
proof-
  obtain k P where "k \<noteq> 0 \<and> P\<in>carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])\<and> A = basic_semialg_set n k P"
    using assms  is_basic_semialg_def
    by (metis mem_Collect_eq)
  then show ?thesis using
      Qp_times_basic_semialg_right_is_semialgebraic[of  k P]
    using assms(1) by blast
qed

lemma cartesian_product_memE':
  assumes "x \<in> cartesian_product A B"
  obtains a b where "a \<in> A \<and> b \<in> B \<and> x = a@b"
  using assms unfolding cartesian_product_def by blast

lemma Qp_times_basic_semialg_left:
  assumes "a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialg_set n k a)  = basic_semialg_set (n+m) k (shift_vars n m a)"
proof
  show "cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialg_set n k a) \<subseteq> basic_semialg_set (n + m) k (shift_vars n m a)"
  proof fix x
    assume A: "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialg_set n k a)"
    then obtain as bs where as_bs_def: "as \<in> (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<and> bs \<in> (basic_semialg_set n k a) \<and> x = as@bs "
     using cartesian_product_memE' by blast
    have 0: "Qp_ev (shift_vars n m a) x = Qp_ev a bs"
      using A as_bs_def assms shift_vars_eval[of a n as m bs ]
      by (metis (no_types, lifting) basic_semialg_set_memE(1))
    obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> Qp_ev a bs = (y[^]k)"
      using as_bs_def basic_semialg_set_memE(2)
      by blast
    have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n+m\<^esup>)"
      using A as_bs_def
      by (metis (no_types, lifting) add.commute basic_semialg_set_memE(1) cartesian_product_closed')
    show "x \<in> basic_semialg_set (n + m) k (shift_vars n m a)"
      apply(rule basic_semialg_set_memI[of _ _ y])
        apply (simp add: "1")
          using y_def apply blast
           using "0" y_def by blast
  qed
  show "basic_semialg_set (n + m) k (shift_vars n m a) \<subseteq> cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialg_set n k a) "
  proof fix x
    assume A: "x \<in> basic_semialg_set (n + m) k (shift_vars n m a)"
    then obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> Qp_ev (shift_vars n m a) x = (y[^]k)"
      using assms basic_semialg_set_memE[of x "n + m" k "shift_vars n m a"]
            shift_vars_closed[of a m] Qp.cring_axioms
      by blast
    have "x \<in> carrier (Q\<^sub>p\<^bsup>m+n\<^esup>)"
      using A basic_semialg_set_memE(1)
      by (metis add.commute)
    then have "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
      using cartesian_product_carrier by blast
    then obtain as bs where as_bs_def: "x = as@bs \<and> as \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> bs \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      by (meson cartesian_product_memE')
    have "bs \<in> (basic_semialg_set n k a)"
    apply(rule basic_semialg_set_memI[of _ _ y])
      using as_bs_def apply blast
       apply (simp add: y_def)
        using y_def shift_vars_eval[of a n as m bs ] as_bs_def assms(1)
        by metis
    then show "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialg_set n k a)"
      using as_bs_def unfolding cartesian_product_def
      by blast
  qed
qed

lemma Qp_times_basic_semialg_left_is_semialgebraic:
  assumes "k > 0"
  assumes "a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialg_set n k a))"
  using basic_semialg_is_semialgebraic'[of a "n+m" k] Qp_times_basic_semialg_left
  by (metis assms(1) assms(2) basic_semialg_is_semialgebraic is_basic_semialg_def neq0_conv shift_vars_closed)

lemma Qp_times_basic_semialg_left_is_semialgebraic':
  assumes "A \<in> basic_semialgs n"
  shows "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) A)"
proof-
  obtain k P where "k \<noteq> 0 \<and> P\<in>carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])\<and> A = basic_semialg_set n k P"
    using assms  is_basic_semialg_def
    by (metis mem_Collect_eq)
  then show ?thesis using
      Qp_times_basic_semialg_left_is_semialgebraic[of k P]
    using assms(1)  by blast
qed

lemma product_of_basic_semialgs_is_semialg:
  assumes "k > 0"
  assumes "l > 0"
  assumes "a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "b \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
  shows "is_semialgebraic (n + m) (cartesian_product (basic_semialg_set n k a) (basic_semialg_set m l b))"
proof-
  have 0:  "cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) =  basic_semialg_set (n+ m) k a"
    using Qp_times_basic_semialg_right assms  by presburger
  have 1:  "cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialg_set m l b)  = basic_semialg_set (m + n) l (shift_vars m n b)"
    using Qp_times_basic_semialg_left assms by blast
  have 2: "(cartesian_product (basic_semialg_set n k a) (basic_semialg_set m l b)) =
                cartesian_product (basic_semialg_set n k a) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<inter>
                 cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialg_set m l b)"
  proof-
    have 0: "basic_semialg_set n k a \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using basic_semialg_set_memE(1) by blast
    have 1: "carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      by simp
    have 2: "carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      by simp
    have 3: "basic_semialg_set m l b \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using basic_semialg_set_memE(1) by blast
    show ?thesis
      using 0 1 2 3 cartesian_product_intersection[of "(basic_semialg_set n k a)" Q\<^sub>p n
                                              "(carrier (Q\<^sub>p\<^bsup>m\<^esup>))" m
                                              "(carrier (Q\<^sub>p\<^bsup>n\<^esup>))" "(basic_semialg_set m l b)"]
      by (smt Collect_cong inf.absorb_iff1 inf.absorb_iff2)
  qed
  then show ?thesis
    using Qp_times_basic_semialg_left_is_semialgebraic
          Qp_times_basic_semialg_right_is_semialgebraic  assms
    by (metis (no_types, lifting) add.commute intersection_is_semialg)
qed

lemma product_of_basic_semialgs_is_semialg':
  assumes "A \<in> (basic_semialgs n)"
  assumes "B \<in> (basic_semialgs m)"
  shows "is_semialgebraic (n + m) (cartesian_product A B)"
proof-
  obtain k a where ka_def: "k > 0 \<and> a \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>]) \<and> A = (basic_semialg_set n k a)"
    using assms
    by (metis is_basic_semialg_def mem_Collect_eq neq0_conv)
  obtain l b where lb_def: "l > 0 \<and> b \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>]) \<and> B = (basic_semialg_set m l b)"
    by (metis assms(2) gr_zeroI is_basic_semialg_def mem_Collect_eq)
  show ?thesis using ka_def lb_def assms product_of_basic_semialgs_is_semialg
  by blast
qed

lemma car_times_semialg_is_semialg:
  assumes "is_semialgebraic m B"
  shows "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) B)"
  apply(rule gen_boolean_algebra.induct[of B "carrier (Q\<^sub>p\<^bsup>m\<^esup>)""basic_semialgs m"])
  using assms is_semialgebraic_def semialg_sets_def apply blast
  apply (simp add: carrier_is_semialgebraic cartesian_product_carrier)
proof-
  show "\<And>A. A \<in> basic_semialgs m \<Longrightarrow> is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (A \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>)))"
  proof-
    fix A assume A: "A \<in> basic_semialgs m "
    then have " (A \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>)) = A"
      by (metis basic_semialg_set_memE(1) inf_absorb1 is_basic_semialg_def mem_Collect_eq subsetI)
    then show "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (A \<inter> carrier (Q\<^sub>p\<^bsup>m\<^esup>)))"
      using add.commute[of n m] assms A
            Qp_times_basic_semialg_left_is_semialgebraic'
      by (simp add: \<open>n + m = m + n\<close>)
  qed
  show "\<And>A C. A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m) \<Longrightarrow>
           is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) A) \<Longrightarrow>
           C \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m) \<Longrightarrow>
           is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) C) \<Longrightarrow>
           is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (A \<union> C))"
  proof- fix A C assume A: " A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m)"
           "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) A)"
           "C \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m)"
          " is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) C)"
    then have B: "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) A \<union> cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) C)"
      using union_is_semialgebraic by blast
    show "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (A \<union> C))"
    proof-
      have 0: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A(1) gen_boolean_algebra_subset
        by blast
      have  1: " C \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A(3) gen_boolean_algebra_subset
        by blast
      then show ?thesis using 0 A B
        using cartesian_product_binary_union_right[of A Q\<^sub>p m C "(carrier (Q\<^sub>p\<^bsup>n\<^esup>))"]
        unfolding is_semialgebraic_def semialg_sets_def
        by presburger
    qed
  qed
  show "\<And>A. A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m) \<Longrightarrow>
         is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) A) \<Longrightarrow>
         is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (carrier (Q\<^sub>p\<^bsup>m\<^esup>) - A))"
  proof- fix A assume A: "A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m)"
                      "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) A)"
    then have "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using gen_boolean_algebra_subset
      by blast
    then show "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (carrier (Q\<^sub>p\<^bsup>m\<^esup>) - A))"
      using A cartesian_product_car_complement_right[of A Q\<^sub>p m n]
      unfolding is_semialgebraic_def semialg_sets_def
      by (metis (mono_tags, lifting) semialg_complement semialg_sets_def)
  qed
qed

lemma basic_semialg_times_semialg_is_semialg:
  assumes "A \<in> basic_semialgs n"
  assumes "is_semialgebraic m B"
  shows " is_semialgebraic (n + m) (cartesian_product A B)"
  apply(rule gen_boolean_algebra.induct[of B "carrier (Q\<^sub>p\<^bsup>m\<^esup>)""basic_semialgs m"])
  using assms(2) is_semialgebraic_def semialg_sets_def apply blast
  using Qp_times_basic_semialg_right_is_semialgebraic' assms(1) apply blast
  apply (metis assms(1) basic_semialg_is_semialgebraic inf.absorb1 is_semialgebraic_closed mem_Collect_eq product_of_basic_semialgs_is_semialg')
    apply (metis (no_types, lifting) cartesian_product_binary_union_right is_semialgebraicI is_semialgebraic_closed semialg_sets_def union_is_semialgebraic)
proof-
  show "\<And>Aa. Aa \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m) \<Longrightarrow>
          is_semialgebraic (n + m) (cartesian_product A Aa) \<Longrightarrow> is_semialgebraic (n + m) (cartesian_product A (carrier (Q\<^sub>p\<^bsup>m\<^esup>) - Aa))"
   proof- fix B assume A:  "B \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (basic_semialgs m)"
                         "is_semialgebraic (n + m) (cartesian_product A B)"
    show "is_semialgebraic (n + m) (cartesian_product A (carrier (Q\<^sub>p\<^bsup>m\<^esup>) - B))"
    using A assms cartesian_product_complement_right[of B Q\<^sub>p m A n] add.commute[of n m]
  proof -
   have f1: "\<forall>n B. \<not> is_semialgebraic n B \<or> B \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
     by (meson is_semialgebraic_closed)
   have "is_basic_semialg n A"
     using \<open>A \<in> {S. is_basic_semialg n S}\<close> by blast
   then have f2: "is_semialgebraic n A"
     using padic_fields.basic_semialg_is_semialgebraic padic_fields_axioms by blast
   have "B \<in> semialg_sets m"
     using \<open>B \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) {S. is_basic_semialg m S}\<close> semialg_sets_def by blast
   then have "is_semialgebraic m B"
     by (meson padic_fields.is_semialgebraicI padic_fields_axioms)
   then show ?thesis
     using f2 f1 by (metis (no_types) Qp_times_basic_semialg_right_is_semialgebraic' \<open>A \<in> {S. is_basic_semialg n S}\<close> \<open>\<lbrakk>B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>); A \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)\<rbrakk> \<Longrightarrow> cartesian_product A (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) - cartesian_product A B = cartesian_product A (carrier (Q\<^sub>p\<^bsup>m\<^esup>) - B)\<close> \<open>is_semialgebraic (n + m) (cartesian_product A B)\<close> diff_is_semialgebraic)
  qed
  qed
qed

text\<open>Semialgebraic sets are closed under cartesian products\<close>

lemma cartesian_product_is_semialgebraic:
  assumes "is_semialgebraic n A"
  assumes "is_semialgebraic m B"
  shows "is_semialgebraic (n + m) (cartesian_product A B)"
  apply(rule gen_boolean_algebra.induct[of A "carrier (Q\<^sub>p\<^bsup>n\<^esup>)""basic_semialgs n"])
  using assms is_semialgebraicE semialg_sets_def apply blast
  using assms car_times_semialg_is_semialg  apply blast
  using assms basic_semialg_times_semialg_is_semialg
  apply (simp add: Int_absorb2 basic_semialg_is_semialgebraic is_semialgebraic_closed)
proof-
  show "\<And>A C. A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n) \<Longrightarrow>
           is_semialgebraic (n + m) (cartesian_product A B) \<Longrightarrow>
           C \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n) \<Longrightarrow>
           is_semialgebraic (n + m) (cartesian_product C B) \<Longrightarrow> is_semialgebraic (n + m) (cartesian_product (A \<union> C) B)"
  proof- fix A C assume A: "A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n)"
                           "is_semialgebraic (n + m) (cartesian_product A B)"
                           "C \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n)"
                           "is_semialgebraic (n + m) (cartesian_product C B)"
    show "is_semialgebraic (n + m) (cartesian_product (A \<union> C) B)"
      using A cartesian_product_binary_union_left[of A Q\<^sub>p n C B]
      by (metis (no_types, lifting) gen_boolean_algebra_subset union_is_semialgebraic)
  qed
  show "\<And>A. A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n) \<Longrightarrow>
         is_semialgebraic (n + m) (cartesian_product A B) \<Longrightarrow> is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>) - A) B)"
  proof- fix A assume A: "A \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) (basic_semialgs n)"
                        "is_semialgebraic (n + m) (cartesian_product A B)"
    show "is_semialgebraic (n + m) (cartesian_product (carrier (Q\<^sub>p\<^bsup>n\<^esup>) - A) B)"
      using assms  A cartesian_product_complement_left[of A Q\<^sub>p n B m]
      unfolding is_semialgebraic_def semialg_sets_def
      by (metis car_times_semialg_is_semialg diff_is_semialgebraic is_semialgebraicE is_semialgebraicI
          is_semialgebraic_closed semialg_sets_def)
  qed
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>$N^{th}$ Power Residues\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition nth_root_poly where
"nth_root_poly (n::nat) a = ((X_poly Q\<^sub>p) [^]\<^bsub>Q\<^sub>p_x\<^esub>  n) \<ominus>\<^bsub>Q\<^sub>p_x\<^esub> (to_poly a)"

lemma nth_root_poly_closed:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "nth_root_poly n a \<in> carrier Q\<^sub>p_x"
  using assms unfolding nth_root_poly_def
  by (meson UPQ.P.minus_closed UPQ.P.nat_pow_closed UPQ.X_closed UPQ.to_poly_closed)

lemma nth_root_poly_eval:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "(nth_root_poly n a) \<bullet> b = (b[^]n) \<ominus>\<^bsub>Q\<^sub>p\<^esub> a"
  using assms unfolding nth_root_poly_def
  using UPQ.P.nat_pow_closed UPQ.X_closed UPQ.to_fun_X_pow UPQ.to_fun_diff UPQ.to_fun_to_poly UPQ.to_poly_closed by presburger

text\<open>Hensel's lemma gives us this criterion for the existence of \<open>n\<close>-th roots\<close>

lemma nth_root_poly_root:
  assumes "(n::nat) > 1"
  assumes "a \<in> \<O>\<^sub>p"
  assumes "a \<noteq> \<one>"
  assumes "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> a) > 2* val ([n]\<cdot>\<one>)"
  shows "(\<exists> b \<in> \<O>\<^sub>p. ((b[^]n) = a))"
proof-
  obtain \<alpha> where alpha_def: "\<alpha> \<in> carrier Z\<^sub>p \<and> \<iota> \<alpha> = a"
    using assms(2) by blast
  have 0: "\<alpha> \<in> carrier Z\<^sub>p"
    by (simp add: alpha_def)
  have 1: "\<alpha> \<noteq> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using assms alpha_def inc_of_one
    by blast
  obtain N where N_def: "N = [n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by blast
  have N_closed: "N \<in> carrier Z\<^sub>p"
    using N_def Zp_nat_mult_closed
    by blast
  have 2: "\<iota> ([n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = ([n]\<cdot> \<one>)"
  proof(induction n)
    case 0
    have 00: "[(0::nat)] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
      using Zp_nat_inc_zero by blast
    have 01: "[(0::nat)] \<cdot>\<^bsub>Q\<^sub>p\<^esub> \<one> = \<zero>"
      using Qp.nat_inc_zero by blast
    then show ?case
      using 00 inc_of_nat by blast
  next
    case (Suc n)
    then show ?case
      using inc_of_nat by blast
  qed
  have 3: "val_Zp (\<one>\<^bsub>Z\<^sub>p\<^esub> \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>) = val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> a)"
    using alpha_def Zp.one_closed ring_hom_one[of \<iota> Z\<^sub>p Q\<^sub>p]  inc_is_hom Zp.ring_hom_minus[of Q\<^sub>p \<iota> "\<one>\<^bsub>Z\<^sub>p\<^esub>" \<alpha> ]
    Qp.ring_axioms
    unfolding \<iota>_def
    by (metis Q\<^sub>p_def Zp.minus_closed Zp_def padic_fields.val_of_inc padic_fields_axioms)
  have 4: "([n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) \<in> nonzero Z\<^sub>p"
  proof-
    have 40: "int n \<ge> 0"
      using of_nat_0_le_iff by blast
    have "nat (int n) = n"
      using nat_int by blast
    hence "[n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> = [int n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
      using 40  unfolding add_pow_def int_pow_def nat_pow_def
      proof -
        have "(if int n < 0 then inv\<^bsub>add_monoid Z\<^sub>p\<^esub> rec_nat \<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> (\<lambda>n f. f \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) 0 else rec_nat \<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> (\<lambda>n f. f \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) n) = rec_nat \<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> (\<lambda>n f. f \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) n"
          by (meson of_nat_less_0_iff)
        then show "rec_nat \<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> (\<lambda>n f. f \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) n = (let f = rec_nat \<one>\<^bsub>add_monoid Z\<^sub>p\<^esub> (\<lambda>n f. f \<otimes>\<^bsub>add_monoid Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) in if int n < 0 then inv\<^bsub>add_monoid Z\<^sub>p\<^esub> f (nat (- int n)) else f (nat (int n)))"
          using \<open>nat (int n) = n\<close> by presburger
      qed
      thus ?thesis
        using Zp_char_0[of n] Zp.not_nonzero_memE Zp_char_0' assms(1) gr_implies_not_zero by blast
    qed
  then have 5: "val_Zp ([n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = val ([n]\<cdot>\<^bsub>Q\<^sub>p\<^esub> (\<one>))"
    using 2 ord_of_inc
    by (metis N_closed N_def val_of_inc)
  then have 6: "(val_Zp (\<one>\<^bsub>Z\<^sub>p\<^esub> \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<alpha>)) > 2*(val_Zp ([n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>))"
    using assms 3  by presburger
  have "\<exists> b \<in> carrier Z\<^sub>p. (b[^]\<^bsub>Z\<^sub>p\<^esub>n= \<alpha>)"
    using Zp_nth_root_lemma[of \<alpha> n] assms "0" "1" "6" by blast
  then obtain b where b_def: "b \<in> carrier Z\<^sub>p \<and>    (b[^]\<^bsub>Z\<^sub>p\<^esub>n= \<alpha>)"
    by blast
  then have "\<iota> (b [^]\<^bsub>Z\<^sub>p\<^esub>n) = a"
    using alpha_def by blast
  then have "(\<iota> b) [^] n = a"
    by (metis Qp.nat_inc_zero Q\<^sub>p_def Qp.nat_pow_zero Zp.nat_pow_0 Zp.nat_pow_zero
        Zp_nat_inc_zero \<iota>_def alpha_def assms(3) b_def frac_inc_of_nat inc_of_one inc_pow not_nonzero_Qp)
  then show ?thesis
    using b_def by blast
qed

text\<open>All points sufficiently close to 1 have nth roots\<close>

lemma eint_nat_times_2:
"2*(n::nat) = 2*eint n"
  using times_eint_simps(1)
  by (metis mult.commute mult_2_right of_nat_add)

lemma P_set_of_one:
"P_set 1 = nonzero Q\<^sub>p"
  apply(rule equalityI) apply(rule subsetI)
  unfolding P_set_def nonzero_def mem_Collect_eq  apply blast
  apply(rule subsetI)  unfolding P_set_def nonzero_def mem_Collect_eq
  using Qp.nat_pow_eone by blast

lemma nth_power_fact:
  assumes "(n::nat) \<ge> 1"
  shows "\<exists> (m::nat) > 0. \<forall> u \<in> carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
proof(cases "n = 1")
  case True
  have "\<forall> u \<in> carrier Q\<^sub>p. ac 1 u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
    unfolding True P_set_of_one
    by (metis iless_Suc_eq padic_fields.val_ring_memE padic_fields.zero_in_val_ring padic_fields_axioms val_nonzero zero_eint_def)
  then show ?thesis  by blast
next
  case F: False
  obtain m where m_def: "m = 1 + nat ( 2*(ord ([n]\<cdot>\<^bsub>Q\<^sub>p\<^esub> (\<one>))))"
    by blast
  then have m_pos: "m > 0"
    by linarith
  have "\<forall> u \<in> carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  proof
    fix u
    assume A: "u \<in> carrier Q\<^sub>p"
    show " ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
    proof
      assume B: "ac m u = 1 \<and> val u = 0"
      then have 0: "val u = val \<one>"
        by (smt A ac_def not_nonzero_Qp val_one val_ord zero_eint_def)
      have 1: "ac m u = ac m \<one>"
        by (metis B Qp.one_nonzero ac_p ac_p_int_pow_factor angular_component_factors_x angular_component_p inc_of_one m_pos p_nonzero)
      have 2: "u \<in> nonzero Q\<^sub>p"
      proof-
        have "ac m \<zero> = 0"
          by (meson ac_def)
        then have "u \<noteq> \<zero>"
          by (metis B zero_neq_one)
        then show ?thesis
          using A not_nonzero_Qp Qp.nonzero_memI by presburger
      qed
      then have 3: "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> u) \<ge> m" using m_pos 0 1 ac_ord_prop[of "\<one>" u "0::int" m]
        by (metis B Qp.one_nonzero add.right_neutral eint.inject val_ord zero_eint_def)
      show "u \<in> P_set n"
      proof(cases "u = \<one>")
        case True
        then show ?thesis
          by (metis P_set_one insert_iff zeroth_P_set)
      next
        case False
        have F0: "u \<in> \<O>\<^sub>p"
          apply(rule val_ring_memI, rule A)
          unfolding 0 val_one by auto
        have F1: "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> u) \<ge> m"
          using False 3 by blast
        have "ord (\<one> \<ominus> u) \<ge> m"
          by (metis A F1 False Qp.not_eq_diff_nonzero Qp.one_closed eint_ord_simps(1) val_ord)
        hence F2: "ord (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> u) > 2*(ord ([n]\<cdot> \<one>))"
          using m_def F1 A False Qp.not_eq_diff_nonzero Qp.one_closed eint_ord_simps(1)
            int_nat_eq of_nat_1 of_nat_add val_ord[of "\<one> \<ominus> u"] eint_nat_times_2
          by linarith
        have "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> u) > 2*(val ([n]\<cdot> \<one>))"
        proof-
          have 0: "val (\<one> \<ominus>\<^bsub>Q\<^sub>p\<^esub> u) > 2*(ord ([n]\<cdot> \<one>))"
            using F2 val_ord[of "\<one> \<ominus> u"] A False Qp.not_eq_diff_nonzero Qp.one_closed eint_ord_simps(2) by presburger
          have "n > 0"
            using assms  by linarith
          hence "eint (ord ([n] \<cdot> \<one>)) = val ([n] \<cdot> \<one>)"
            using val_ord_nat_inc[of n]
            by blast
          hence "2*ord ([n]\<cdot> \<one>) = 2*val ([n]\<cdot> \<one>)"
            by (metis inc_of_nat times_eint_simps(1))
          thus ?thesis
            using 0 val_ord[of "\<one> \<ominus> u"] assms
            by presburger
        qed
        then have "(\<exists> b \<in> \<O>\<^sub>p. ((b[^]n) = u))"
          using m_def False nth_root_poly_root[of n u] F0 assms  F by linarith
        then have "(\<exists> b \<in> carrier Q\<^sub>p. ((b[^]n) = u))"
          using val_ring_memE by blast
        then show "u \<in> P_set n"
          using P_set_def[of n] 2
          by blast
      qed
    qed
  qed
  then show ?thesis using m_pos by blast
qed

definition pow_res where
"pow_res (n::nat) x = {a. a \<in> carrier Q\<^sub>p \<and>  (\<exists>y \<in> nonzero Q\<^sub>p. (a = x \<otimes> (y[^]n)))}"

lemma nonzero_pow_res:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "pow_res (n::nat) x \<subseteq> nonzero Q\<^sub>p"
proof
  fix a
  assume "a \<in> pow_res n x"
  then obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and> (a = x \<otimes> (y[^]n))"
    using pow_res_def by blast
  then show "a \<in> nonzero Q\<^sub>p"
    using assms Qp.Units_m_closed Qp_nat_pow_nonzero Units_eq_nonzero by blast
qed

lemma pow_res_of_zero:
  shows "pow_res n \<zero> = {\<zero>}"
  unfolding pow_res_def  apply(rule equalityI)
  apply(rule subsetI)
  unfolding mem_Collect_eq
  apply (metis Qp.integral_iff Qp.nat_pow_closed Qp.nonzero_closed Qp.zero_closed insertCI)
  apply(rule subsetI) unfolding mem_Collect_eq
  by (metis Qp.nat_pow_one Qp.one_nonzero Qp.r_one Qp.zero_closed equals0D insertE)

lemma equal_pow_resI:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> pow_res n x"
  shows "pow_res n x = pow_res n y"
proof
  have y_closed: "y \<in> carrier Q\<^sub>p"
    using assms unfolding pow_res_def by blast
  obtain c where c_def: "c \<in> nonzero Q\<^sub>p \<and> y = x \<otimes> (c[^]n)"
    using assms pow_res_def by blast
  have "((inv c)[^]n) = inv (c[^]n)"
    using c_def Qp.field_axioms Qp.nat_pow_of_inv Units_eq_nonzero by blast
  then have "y \<otimes> ((inv c)[^]n) = x"
    using y_closed c_def assms Qp.inv_cancelL(2) Qp.nonzero_closed Qp_nat_pow_nonzero Units_eq_nonzero
    by presburger
  then have P0: "(inv c) \<in> nonzero Q\<^sub>p \<and> x =y \<otimes> ((inv c)[^]n) "
    using c_def  nonzero_inverse_Qp by blast
  show "pow_res n x \<subseteq> pow_res n y"
  proof
    fix a
    assume A: "a \<in> pow_res n x"
    then have "a \<in> carrier Q\<^sub>p"
      by (metis (no_types, lifting) mem_Collect_eq pow_res_def)
    obtain b  where b_def: "b \<in> nonzero Q\<^sub>p \<and> a = x \<otimes> (b[^]n)"
      using A pow_res_def by blast
    then have 0: "b \<in> nonzero Q\<^sub>p \<and> a = y \<otimes> ((inv c)[^]n) \<otimes> (b[^]n)"
      using \<open>y \<otimes> inv c [^] n = x\<close> by blast
    have "b \<in> nonzero Q\<^sub>p \<and> a = y \<otimes> (((inv c)  \<otimes> b)[^]n)"
    proof-
      have "(inv c)[^]n \<otimes> (b[^]n) = ((inv c)  \<otimes> b)[^]n"
        using c_def b_def assms P0 Qp.nat_pow_distrib Qp.nonzero_closed by presburger
      then have " y \<otimes> (((inv c)[^]n) \<otimes> (b[^]n)) = y \<otimes> (((inv c)  \<otimes> b)[^]n)"
        by presburger
      then show ?thesis
        using y_closed 0 P0 Qp.m_assoc Qp.nat_pow_closed Qp.nonzero_closed assms(1) by presburger
    qed
    then have "((inv c)  \<otimes> b) \<in> nonzero Q\<^sub>p \<and> a = y \<otimes> (((inv c)  \<otimes> b)[^]n)"
      by (metis P0 Qp.integral_iff Qp.nonzero_closed Qp.nonzero_mult_closed not_nonzero_Qp)
    then show "a \<in> pow_res n y" using pow_res_def \<open>a \<in> carrier Q\<^sub>p\<close> by blast
  qed
  show "pow_res n y \<subseteq> pow_res n x"
  proof
    fix a
    assume A: "a \<in> pow_res n y"
    then have 0: "a \<in> carrier Q\<^sub>p"
      by (metis (no_types, lifting) mem_Collect_eq pow_res_def)
    obtain b  where b_def: "b \<in> nonzero Q\<^sub>p \<and> a = y \<otimes> (b[^]n)"
      using A pow_res_def by blast
    then have "a = (x \<otimes> (c[^]n)) \<otimes> (b[^]n)"
      using c_def by blast
    then have "a = x \<otimes> ((c[^]n) \<otimes> (b[^]n))"
      by (meson Qp.m_assoc Qp.nat_pow_closed Qp.nonzero_closed assms(1) b_def c_def)
    then have "a = x \<otimes> ((c \<otimes> b)[^]n)"
      using Qp.nat_pow_distrib Qp.nonzero_closed b_def c_def by presburger
    then have "(c \<otimes> b) \<in> nonzero Q\<^sub>p \<and>   a = x \<otimes> ((c \<otimes> b)[^]n)"
      by (metis Qp.integral_iff Qp.nonzero_closed Qp.nonzero_mult_closed b_def c_def not_nonzero_Qp)
    then show "a \<in> pow_res n x"
      using pow_res_def 0  by blast
  qed
qed

lemma zeroth_pow_res:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "pow_res 0 x = {x}"
  apply(rule equalityI)
  apply(rule subsetI)
  unfolding pow_res_def mem_Collect_eq
  using assms apply (metis Qp.nat_pow_0 Qp.r_one singletonI)
  apply(rule subsetI)
  unfolding pow_res_def mem_Collect_eq
  using assms by (metis Qp.nat_pow_0 Qp.one_nonzero Qp.r_one equals0D insertE)

lemma Zp_car_zero_res: assumes "x \<in> carrier Z\<^sub>p"
  shows "x 0 = 0"
  using assms unfolding Zp_def
  using Zp_def Zp_defs(3) padic_set_zero_res prime by blast

lemma zeroth_ac:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "ac 0 x = 0"
  apply(cases "x = \<zero> ")
  unfolding ac_def apply presburger
  using assms angular_component_closed[of x] Zp_car_zero_res unfolding nonzero_def mem_Collect_eq
  by presburger

lemma nonzero_ac_imp_nonzero:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "ac m x \<noteq> 0"
  shows "x \<in> nonzero Q\<^sub>p"
  using assms unfolding ac_def nonzero_def mem_Collect_eq
  by presburger

lemma nonzero_ac_val_ord:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "ac m x \<noteq> 0"
  shows "val x = ord x"
  using nonzero_ac_imp_nonzero assms val_ord by blast

lemma pow_res_equal_ord:
  assumes "n > 0"
  shows  "\<exists>m > 0. \<forall>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<longrightarrow> pow_res n x = pow_res n y"
proof-
  obtain m where m_def_0: "m > 0 \<and> ( \<forall> u \<in> carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using assms nth_power_fact[of n]
    by (metis less_imp_le_nat less_one linorder_neqE_nat nat_le_linear zero_less_iff_neq_zero)
  then have  m_def: "m > 0 \<and> ( \<forall> u \<in> carrier Q\<^sub>p. ac m u = 1 \<and> ord u = 0 \<longrightarrow> u \<in> P_set n)"
    by (smt nonzero_ac_val_ord zero_eint_def)
  have  "\<forall>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<longrightarrow> pow_res n x = pow_res n y"
  proof
    fix x
    show "\<forall>y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<longrightarrow> pow_res n x = pow_res n y"
    proof fix y
      show "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<longrightarrow> pow_res n x = pow_res n y"
      proof
        assume A: "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y "
        then have 0: "ac m (x \<div> y) = 1"
          using ac_inv[of y m] ac_mult
          by (metis ac_inv'''(1) ac_mult'  m_def nonzero_inverse_Qp)
        have 1: "ord (x \<div> y) = 0"
          using A  ord_fract by presburger
        have 2: "(x \<div> y) \<in> nonzero Q\<^sub>p"
          using A
          by (metis Qp.nonzero_closed Qp.nonzero_mult_closed local.fract_cancel_right nonzero_inverse_Qp not_nonzero_Qp zero_fract)
        have 3: "(x \<div> y) \<in> P_set n"
          using m_def 0 1 2 nonzero_def
          by (smt Qp.nonzero_closed)
        then obtain b where b_def: "b \<in> carrier Q\<^sub>p \<and> (b[^]n) = (x \<div> y)"
          using P_set_def
          by blast
        then have "(x \<div> y) \<otimes> y = (b[^]n) \<otimes> y"
          by presburger
        then have "x = (b[^]n) \<otimes> y"
          using A b_def
          by (metis Qp.nonzero_closed local.fract_cancel_left)
        then have "x = y \<otimes>(b[^]n)"
          using A b_def
          by (metis Qp.nonzero_closed local.fract_cancel_right)
        then have "x \<in> pow_res n y"
          unfolding pow_res_def using A b_def
          by (metis (mono_tags, lifting) "2" Qp.nat_pow_0 Qp.nonzero_closed Qp_nonzero_nat_pow mem_Collect_eq not_gr_zero)
        then show "pow_res n x = pow_res n y"
          using  A equal_pow_resI[of x y n] unfolding nonzero_def
          by (metis (mono_tags, lifting) A Qp.nonzero_closed equal_pow_resI)
      qed
    qed
  qed
  then show ?thesis using m_def by blast
qed

lemma pow_res_equal:
  assumes "n > 0"
  shows  "\<exists>m> 0. \<forall>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = (ord y mod n) \<longrightarrow> pow_res n x = pow_res n y"
proof-
  obtain m where m_def: "m > 0 \<and> (\<forall>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<longrightarrow> pow_res n x = pow_res n y)"
    using assms pow_res_equal_ord
    by meson
  have "\<forall>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y mod int n \<longrightarrow> pow_res n x = pow_res n y"
  proof fix x
    show  "\<forall>y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y mod int n \<longrightarrow> pow_res n x = pow_res n y"
    proof fix y
      show "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y mod int n \<longrightarrow> pow_res n x = pow_res n y"
      proof
        assume A: "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y mod int n"
        show "pow_res n x = pow_res n y"
        proof-
          have A0: "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p"
            using A by blast
          have A1: "ac m x = ac m y"
            using A by blast
          have A2: "ord x = ord y mod int n"
            using A by blast
          obtain k where k_def: "k = ord x"
            by blast
          obtain l where l_def: "ord y = ord x + (l:: int)*(int n)"
            using assms A2
            by (metis A k_def mod_eqE mod_mod_trivial mult_of_nat_commute)
          have m_def': "\<And>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<Longrightarrow>  pow_res n x = pow_res n y"
            using m_def
            by blast
          have 0: "ord (y \<otimes> (\<pp>[^](- l*n))) = ord x"
          proof-
            have 0: "ord (y \<otimes> (\<pp>[^](- l*n))) = ord y + (ord  (\<pp>[^](- l*n)))"
              using ord_mult p_nonzero  A0 Qp_int_pow_nonzero
              by blast
            have 1: "ord (\<pp>[^](- l*n)) = - l*n"
              using ord_p_pow_int[of "-l*n"]
              by blast
            then have "ord (y \<otimes> (\<pp>[^](- l*n))) = ord y - l*n"
              using 0
              by linarith
            then show ?thesis
              using k_def l_def by linarith
          qed
          have 1: "ac m (y \<otimes> (\<pp>[^](- l*n))) = ac m y"
            using assms ac_p_int_pow_factor_right[of ] m_def A Qp.nonzero_closed by presburger
          have 2: "y \<otimes> (\<pp>[^](- l*n)) \<in> nonzero Q\<^sub>p"
            using A0 Qp_int_pow_nonzero[of \<pp> "- l*n"] Qp.cring_axioms nonzero_def cring.cring_simprules(5)
              fract_cancel_left not_nonzero_Qp p_intpow_inv'' p_nonzero zero_fract Qp.integral_iff
              Qp.nonzero_closed Qp.nonzero_memE(2) Qp.nonzero_memI Qp.nonzero_mult_closed
              minus_mult_commute mult_minus_right p_intpow_closed(1) p_intpow_closed(2)
            by presburger
          then have 3: "pow_res n (y \<otimes> (\<pp>[^](- l*n))) = pow_res n x"
            using 2 A0 m_def'[of "y \<otimes> (\<pp>[^](- l*n))" x] "0" "1" A1
            by linarith
          have 4: "(y \<otimes> (\<pp>[^](- l*n))) = (y \<otimes> ((\<pp>[^]- l)[^]n))"
            using Qp_int_nat_pow_pow[of \<pp> "-l" n] p_nonzero
            by presburger
          have "y \<otimes> (\<pp>[^](- l*n))\<in> pow_res n y "
            using "2" "4" Qp_int_pow_nonzero nonzero_def p_nonzero
            unfolding pow_res_def nonzero_def
          proof -
            assume a1: "\<And>x n. x \<in> {a \<in> carrier Q\<^sub>p. a \<noteq> \<zero>} \<Longrightarrow> x [^] (n::int) \<in> {a \<in> carrier Q\<^sub>p. a \<noteq> \<zero>}"
            assume a2: "\<pp> \<in> {a \<in> carrier Q\<^sub>p. a \<noteq> \<zero>}"
            assume a3: "y \<otimes> \<pp> [^] (- l * int n) \<in> {a \<in> carrier Q\<^sub>p. a \<noteq> \<zero>}"
            have f4: "\<pp> [^] (- 1 * l) \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>}"
              using a2 a1 by presburger
            have f5: "- l = - 1 * l"
              by linarith
            then have f6: "y \<otimes> \<pp> [^] (- 1 * l * int n) = y \<otimes> (\<pp> [^] (- 1 * l)) [^] n"
              using \<open>y \<otimes> \<pp> [^] (- l * int n) = y \<otimes> (\<pp> [^] - l) [^] n\<close> by presburger
            then have "y \<otimes> (\<pp> [^] (- 1 * l)) [^] n \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>}"
              using f5 a3 by presburger
            then have "y \<otimes> (\<pp> [^] (- 1 * l)) [^] n \<in> {r \<in> carrier Q\<^sub>p. \<exists>ra. ra \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>} \<and> r = y \<otimes> ra [^] n}"
              using f4 by blast
            then have "y \<otimes> \<pp> [^] (- l * int n) \<in> {r \<in> carrier Q\<^sub>p. \<exists>ra. ra \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>} \<and> r = y \<otimes> ra [^] n}"
              using f6 f5 by presburger
            then show "y \<otimes> \<pp> [^] (- l * int n) \<in> {r \<in> carrier Q\<^sub>p. \<exists>ra\<in>{r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>}. r = y \<otimes> ra [^] n}"
              by meson
          qed
          then have "pow_res n (y \<otimes> (\<pp>[^](- l*n))) = pow_res n y"
            using equal_pow_resI[of "(y \<otimes> (\<pp>[^](- l*n)))" y n] "2" A0 assms
                  Qp.nonzero_mult_closed p_intpow_closed(2)
            by (metis (mono_tags, opaque_lifting) "3" A Qp.nonzero_closed equal_pow_resI)
          then show ?thesis using 3 by blast
        qed
      qed
    qed
  qed
  then show ?thesis
    using m_def
    by blast
qed

definition pow_res_classes where
"pow_res_classes n = {S. \<exists>x \<in> nonzero Q\<^sub>p. S = pow_res n x }"

lemma pow_res_semialg_def:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n \<ge> 1"
  shows "\<exists>P \<in> carrier Q\<^sub>p_x. pow_res n x = (univ_basic_semialg_set n P) - {\<zero>}"
proof-
  have 0: "pow_res n x = {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. (inv x) \<otimes> a = (y[^]n)}"
  proof
    show "pow_res n x \<subseteq> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n)}"
    proof
      fix a
      assume A: "a \<in> pow_res n x"
      then have "a \<in> carrier Q\<^sub>p \<and>  (\<exists>y\<in>nonzero Q\<^sub>p. a = x \<otimes> (y[^]n))"
        unfolding pow_res_def
        by blast
      then obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and>a = x \<otimes> (y[^]n)"
        by blast
      then have "y \<in> nonzero Q\<^sub>p \<and> inv x \<otimes> a = (y[^]n)"
      proof -
        show ?thesis
          by (metis (no_types, opaque_lifting) Qp.m_assoc Qp.m_comm Qp.nat_pow_closed Qp.nonzero_closed
              \<open>a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. a = x \<otimes> y [^] n)\<close> assms(1) local.fract_cancel_right nonzero_inverse_Qp y_def)
      qed
      then show "a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n)}"
        using assms \<open>a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. a = x \<otimes> (y[^]n))\<close>
        by blast
    qed

    show "{a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n)} \<subseteq> pow_res n x"
    proof
      fix a
      assume A: "a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n)}"
      show "a \<in> pow_res n x"
      proof-
        have "a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n))"
          using A by blast
        then obtain y where y_def: "y\<in>nonzero Q\<^sub>p \<and> inv x \<otimes> a = (y[^]n)"
          by blast
        then have "y\<in>nonzero Q\<^sub>p \<and>  a = x \<otimes>(y[^]n)"
          by (metis Qp.l_one Qp.m_assoc Qp.nonzero_closed Qp.not_nonzero_memI
              \<open>a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = y [^] n)\<close> assms(1) field_inv(2) inv_in_frac(1))
        then show ?thesis
          by (metis (mono_tags, lifting) \<open>a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n))\<close> mem_Collect_eq pow_res_def)
      qed
    qed
  qed
  obtain P where P_def: "P = up_ring.monom Q\<^sub>p_x (inv x) 1"
    by blast
  have P_closed: "P \<in> carrier Q\<^sub>p_x"
    using P_def Qp.nonzero_closed Qp.nonzero_memE(2) UPQ.is_UP_monomE(1) UPQ.is_UP_monomI assms(1) inv_in_frac(1) by presburger
  have P_eval: "\<And>a. a \<in> carrier Q\<^sub>p \<Longrightarrow> (P \<bullet> a) = (inv x) \<otimes> a"
    using P_def to_fun_monom[of ]
    by (metis Qp.nat_pow_eone Qp.nonzero_closed Qp.not_nonzero_memI assms(1) inv_in_frac(1))
  have 0: "pow_res n x = {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. (P \<bullet> a) = (y[^]n)}"
  proof
    show "pow_res n x \<subseteq> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}"
    proof fix a
      assume "a \<in> pow_res n x"
      then have "a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n))"
        using 0
        by blast
      then show "a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}"
        using P_eval
        by (metis (mono_tags, lifting) mem_Collect_eq)
     qed
    show "{a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)} \<subseteq> pow_res n x"
    proof fix a
      assume "a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}"
      then obtain y where y_def: "y\<in>nonzero Q\<^sub>p \<and> P \<bullet> a = (y[^]n)"
        by blast
      then have "y\<in>nonzero Q\<^sub>p \<and> inv x \<otimes> a = (y[^]n)"
        using P_eval \<open>a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}\<close>
        by blast
      then have "a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>nonzero Q\<^sub>p. inv x \<otimes> a = (y[^]n))"
         using \<open>a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}\<close> by blast
      then show "a \<in> pow_res n x"
      using 0
      by blast
    qed
  qed
  have 1: "univ_basic_semialg_set n P - {\<zero>} = {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. (P \<bullet> a) = (y[^]n)}"
  proof
    show "univ_basic_semialg_set n P - {\<zero>} \<subseteq> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}"
    proof
      fix a
      assume A: "a \<in> univ_basic_semialg_set n P - {\<zero>}"
      then have A0: "a \<in> carrier Q\<^sub>p \<and> (\<exists>y\<in>carrier Q\<^sub>p. P \<bullet> a = (y[^]n))"
        unfolding univ_basic_semialg_set_def by blast
      then have A0': "a \<in> nonzero Q\<^sub>p \<and> (\<exists>y\<in>carrier Q\<^sub>p. P \<bullet> a = (y[^]n))"
        using A
        by (metis DiffD2 not_nonzero_Qp singletonI)
      then obtain y where y_def: "y\<in>carrier Q\<^sub>p \<and> P \<bullet> a = (y[^]n)"
        by blast
      have A1: "(P \<bullet> a) \<noteq> \<zero>"
        using P_eval A0' Qp.integral_iff Qp.nonzero_closed Qp.nonzero_memE(2) assms(1) inv_in_frac(1) inv_in_frac(2) by presburger
      have A2: "y \<in> nonzero Q\<^sub>p"
      proof-
        have A20: "(y[^]n) \<noteq>\<zero>"
          using A1 y_def
          by blast
        have "y \<noteq> \<zero>"
          apply(rule ccontr) using A20 assms
          by (metis Qp.nat_pow_eone Qp.semiring_axioms Qp.zero_closed le_zero_eq semiring.nat_pow_zero)
        then show ?thesis
          using y_def A1 not_nonzero_Qp Qp.not_nonzero_memE by blast
      qed
      then have "y \<in> nonzero  Q\<^sub>p \<and> P \<bullet> a = (y[^]n)" using y_def
        by blast
      then show "a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}"
        using A0 nonzero_def
        by blast
    qed
    show "{a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)} \<subseteq> univ_basic_semialg_set n P - {\<zero>}"
    proof
      fix a
      assume A: "a \<in> {a \<in> carrier Q\<^sub>p. \<exists>y\<in>nonzero Q\<^sub>p. P \<bullet> a = (y[^]n)}"
      then obtain y where y_def: "y\<in>nonzero Q\<^sub>p \<and> P \<bullet> a = (y[^]n)"
        by blast
      then have "y \<noteq>\<zero> \<and> y\<in> carrier Q\<^sub>p \<and> P \<bullet> a = (y[^]n)"
        by (metis (mono_tags, opaque_lifting) Qp.nonzero_closed Qp.not_nonzero_memI)
      then have "a \<noteq>\<zero>"
        using  P_eval
        by (metis Qp.m_comm Qp.nonzero_closed Qp.nonzero_memE(2) Qp.nonzero_pow_nonzero Qp.zero_closed assms(1) inv_in_frac(1) zero_fract)
      then show "a \<in> univ_basic_semialg_set n P - {\<zero>}"
        unfolding univ_basic_semialg_set_def
        using A \<open>y \<noteq> \<zero> \<and> y \<in> carrier Q\<^sub>p \<and> P \<bullet> a = (y[^]n)\<close>
        by blast
    qed
  qed
  show ?thesis using 0 1
    by (metis (no_types, lifting) P_closed)
qed

lemma pow_res_is_univ_semialgebraic:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "is_univ_semialgebraic (pow_res n x)"
proof(cases "n = 0")
  case True
  have T0: "pow_res n x = {x}"
    unfolding True using assms
    by (simp add: assms zeroth_pow_res)
  have "[x] \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
    using assms Qp.to_R1_closed by blast
  hence "is_semialgebraic 1 {[x]}"
    using is_algebraic_imp_is_semialg singleton_is_algebraic by blast
  thus ?thesis unfolding T0 using assms
    by (simp add: \<open>x \<in> carrier Q\<^sub>p\<close> finite_is_univ_semialgebraic)
next
  case False
  show ?thesis
  proof(cases "x = \<zero>")
    case True
    then show ?thesis using finite_is_univ_semialgebraic False pow_res_of_zero
      by (metis Qp.zero_closed empty_subsetI finite.emptyI finite.insertI insert_subset)
  next
    case F: False
    then show ?thesis
      using False pow_res_semialg_def[of x n] diff_is_univ_semialgebraic[of _ "{\<zero>}"]  finite_is_univ_semialgebraic[of "{\<zero>}"]
      by (metis Qp.zero_closed assms empty_subsetI finite.emptyI finite.insertI insert_subset less_one less_or_eq_imp_le linorder_neqE_nat not_nonzero_Qp univ_basic_semialg_set_is_univ_semialgebraic)
  qed
qed

lemma pow_res_is_semialg:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "is_semialgebraic 1 (to_R1 ` (pow_res n x))"
  using assms pow_res_is_univ_semialgebraic is_univ_semialgebraicE
  by blast

lemma pow_res_refl:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "x \<in> pow_res n x"
proof-
  have "x = x \<otimes> (\<one> [^]n)"
    using assms Qp.nat_pow_one Qp.r_one by presburger
  thus ?thesis
    using assms unfolding pow_res_def mem_Collect_eq
    using Qp.one_nonzero by blast
qed

lemma equal_pow_resE:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "n > 0"
  assumes "pow_res n a = pow_res n b"
  shows "\<exists> s \<in> P_set n. a = b \<otimes> s"
proof-
  have "a \<in> pow_res n b"
    using assms pow_res_refl by blast
  then obtain y where y_def: " y \<in> nonzero Q\<^sub>p \<and> a = b \<otimes> y[^]n"
    unfolding pow_res_def by blast
  thus ?thesis  unfolding P_set_def
    using Qp.nonzero_closed Qp_nat_pow_nonzero by blast
qed

lemma pow_res_one:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "pow_res 1 x = nonzero Q\<^sub>p"
proof show "pow_res 1 x \<subseteq> nonzero Q\<^sub>p"
      using  assms nonzero_pow_res[of x 1] by blast
    show "nonzero Q\<^sub>p \<subseteq> pow_res 1 x"
    proof fix y assume A: "y \<in> nonzero Q\<^sub>p"
      then have 0: "\<one> \<in> nonzero Q\<^sub>p \<and> y = x \<otimes> ((inv x)\<otimes> y)[^](1::nat)"
        using assms  Qp.m_comm Qp.nat_pow_eone Qp.nonzero_closed Qp.nonzero_mult_closed
          Qp.one_nonzero local.fract_cancel_right nonzero_inverse_Qp by presburger
      have 1: "(inv x)\<otimes> y \<in> nonzero Q\<^sub>p"
        using A assms by (metis Qp.Units_m_closed Units_eq_nonzero nonzero_inverse_Qp)
      then show "y \<in> pow_res 1 x"
        unfolding pow_res_def using 0 1 A Qp.nonzero_closed by blast
    qed
qed


lemma pow_res_zero:
  assumes "n > 0"
  shows "pow_res n \<zero> = {\<zero>}"
proof
  show "pow_res n \<zero> \<subseteq> {\<zero>}"
  unfolding pow_res_def
  using Qp.l_null Qp.nat_pow_closed Qp.nonzero_closed by blast
  show "{\<zero>} \<subseteq> pow_res n \<zero>"
    using assms unfolding pow_res_def
    using Qp.l_null Qp.one_closed Qp.one_nonzero empty_subsetI insert_subset by blast
qed


lemma equal_pow_resI':
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> P_set n"
  assumes "a = b \<otimes> c"
  assumes "n > 0"
  shows "pow_res n a = pow_res n b"
proof-
  obtain y where y_def: "c = y[^]n \<and> y \<in> carrier Q\<^sub>p"
    using assms unfolding P_set_def by blast
  have c_nonzero: "c \<in> nonzero Q\<^sub>p"
    using P_set_nonzero'(1) assms(3) by blast
  have y_nonzero: "y \<in> nonzero Q\<^sub>p"
    using y_def c_nonzero  Qp_nonzero_nat_pow assms(5) by blast
  have 0: "a \<in> pow_res n b"
    using assms y_nonzero y_def unfolding pow_res_def
    by blast
  show ?thesis
    apply(cases "b = \<zero>")
    using pow_res_zero Qp.l_null Qp.nonzero_closed assms(4) c_nonzero apply presburger
    by (metis "0" assms(1) assms(2) assms(5) not_nonzero_Qp equal_pow_resI)
qed

lemma equal_pow_resI'':
  assumes "n > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "a \<otimes> inv b \<in> P_set n"
  shows "pow_res n a = pow_res n b"
  using assms equal_pow_resI'[of a b "a \<otimes> inv b" n] Qp.nonzero_closed local.fract_cancel_right
  by blast

lemma equal_pow_resI''':
  assumes "n > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "c \<in> nonzero Q\<^sub>p"
  assumes "pow_res n (c \<otimes> a) = pow_res n (c \<otimes> b)"
  shows "pow_res n a = pow_res n b"
proof-
  have 0: "c \<otimes>a \<in> nonzero Q\<^sub>p"
    by (meson Localization.submonoid.m_closed Qp.nonzero_is_submonoid assms(2) assms(4))
  have 1: "c \<otimes>b \<in> nonzero Q\<^sub>p"
    by (meson Localization.submonoid.m_closed Qp.nonzero_is_submonoid assms(3) assms(4))
  have "c\<otimes>a \<in> pow_res n (c\<otimes>b)"
  proof(cases "n = 1")
    case True
    then show ?thesis
      using assms 0 1 pow_res_one[of "c\<otimes>b"] by blast
  next
    case False
    then have "n \<ge> 2"
      using assms(1) by linarith
    then show ?thesis
      using assms 0 1 pow_res_refl[of "c\<otimes>a" n] unfolding nonzero_def
      by blast
  qed
  then obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and> (c \<otimes> a) = (c \<otimes> b)\<otimes>y[^]n"
    using assms unfolding pow_res_def by blast
  then have "a = b\<otimes>y[^]n"
    using assms
    by (metis Qp.m_assoc Qp.m_lcancel Qp.nonzero_closed Qp.nonzero_mult_closed Qp.not_nonzero_memI Qp_nat_pow_nonzero)
  then show ?thesis
    by (metis P_set_memI Qp.nonzero_closed Qp.nonzero_mult_closed Qp.not_nonzero_memI Qp_nat_pow_nonzero assms(1) assms(3) equal_pow_resI' y_def)
qed

lemma equal_pow_resI'''':
  assumes "n > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "a = b \<otimes> u"
  assumes "u \<in> P_set n"
  shows "pow_res n a = pow_res n b"
proof(cases "a = \<zero>")
  case True
  then have "b = \<zero>"
    using assms unfolding P_set_def
    by (metis (no_types, lifting) Qp.integral Qp.nonzero_closed Qp.not_nonzero_memI mem_Collect_eq)
  then show ?thesis using pow_res_zero
    using True by blast
next
  case False
  then have 0: "a \<in> nonzero Q\<^sub>p"
    using Qp.not_nonzero_memE assms(2) by blast
  have 1: "b \<in> nonzero Q\<^sub>p"
    using 0 assms unfolding P_set_def
    by (metis (no_types, lifting) Qp.integral_iff Qp.nonzero_closed mem_Collect_eq not_nonzero_Qp)
  have 2: "a \<otimes> (inv b)\<in> P_set n"
    using assms 0 1
    by (metis P_set_nonzero'(2) Qp.inv_cancelR(1) Qp.m_comm Qp.nonzero_memE(2) Units_eq_nonzero inv_in_frac(1))
  then show ?thesis using equal_pow_resI''
    by (meson "0" "1" assms(1) equal_pow_resI)
qed


lemma Zp_Units_ord_zero:
  assumes "a \<in> Units Z\<^sub>p"
  shows "ord_Zp a = 0"
proof-
  have "inv\<^bsub>Z\<^sub>p\<^esub> a \<in> nonzero Z\<^sub>p"
    apply(rule Zp.nonzero_memI, rule Zp.Units_inv_closed, rule assms)
    using assms Zp.Units_inverse in_Units_imp_not_zero by blast
  then have "ord_Zp (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv \<^bsub>Z\<^sub>p\<^esub> a) = ord_Zp a + ord_Zp (inv \<^bsub>Z\<^sub>p\<^esub> a)"
    using assms ord_Zp_mult Zp.Units_nonzero zero_not_one
    by (metis Zp.zero_not_one)
  then show ?thesis
    by (smt Zp.Units_closed Zp.Units_r_inv Zp.integral_iff Zp.nonzero_closed \<open>inv\<^bsub>Z\<^sub>p\<^esub> a \<in> nonzero Z\<^sub>p\<close> assms ord_Zp_one ord_pos)
qed

lemma pow_res_nth_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "pow_res n (a[^]n) = pow_res n \<one>"
proof
  show "pow_res n (a [^] n) \<subseteq> pow_res n \<one>"
  proof fix x assume A: "x \<in> pow_res n (a [^] n)"
    then show "x \<in> pow_res n \<one>"
      by (metis P_set_memI Qp.l_one Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_memE(2)
          Qp.nonzero_pow_nonzero Qp.one_closed assms(1) assms(2) equal_pow_resI')
  qed
  show "pow_res n \<one> \<subseteq> pow_res n (a [^] n)"
  proof fix x assume A: "x \<in> pow_res n \<one>"
    then obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and> x = \<one>\<otimes>y[^]n"
      unfolding pow_res_def by blast
    then have 0: "x = y[^]n"
      using Qp.l_one Qp.nonzero_closed by blast
    have "y[^]n = a[^]n \<otimes> (inv a \<otimes> y)[^]n"
    proof-
      have "a[^]n \<otimes> (inv a \<otimes> y)[^]n = a[^]n \<otimes> (inv a)[^]n \<otimes> y[^]n"
        using Qp.Units_inv_closed Qp.m_assoc Qp.nat_pow_closed Qp.nat_pow_distrib Qp.nonzero_closed Units_eq_nonzero assms(1) y_def by presburger
      then show ?thesis
        by (metis Qp.Units_inv_inv Qp.inv_cancelR(1) Qp.nat_pow_distrib Qp.nonzero_closed Qp.nonzero_mult_closed Units_eq_nonzero assms(1) nonzero_inverse_Qp y_def)
    qed
    then show "x \<in> pow_res n (a [^] n)"
      using y_def  A assms unfolding pow_res_def mem_Collect_eq
      by (metis "0" Qp.integral Qp.m_closed Qp.nonzero_closed Qp.not_nonzero_memI inv_in_frac(1) inv_in_frac(2) not_nonzero_Qp)
  qed
qed

lemma pow_res_of_p_pow:
  assumes "n > 0"
  shows "pow_res n (\<pp>[^]((l::int)*n)) = pow_res n \<one>"
proof-
  have 0: "\<pp>[^]((l::int)*n) = (\<pp>[^]l)[^]n"
    using Qp_p_int_nat_pow_pow by blast
  have "\<pp>[^]((l::int)*n) \<in> P_set n"
    using  P_set_memI[of _ "\<pp>[^]l"]
    by (metis "0" Qp.not_nonzero_memI Qp_int_pow_nonzero p_intpow_closed(1) p_nonzero)
  thus ?thesis
    using "0" assms p_intpow_closed(2) pow_res_nth_pow by presburger
qed

lemma pow_res_nonzero:
  assumes "n > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "pow_res n a = pow_res n b"
  shows "b \<in> nonzero Q\<^sub>p"
  using assms nonzero_pow_res[of a n] pow_res_zero[of n]
  by (metis insert_subset not_nonzero_Qp)

lemma pow_res_mult:
  assumes "n > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  assumes "pow_res n a = pow_res n c"
  assumes "pow_res n b = pow_res n d"
  shows "pow_res n (a \<otimes> b) = pow_res n (c \<otimes> d)"
proof(cases "a \<in> nonzero Q\<^sub>p")
  case True
  then have "c \<in> nonzero Q\<^sub>p"
    using assms pow_res_nonzero by blast
  then obtain \<alpha> where alpha_def: "\<alpha> \<in> nonzero Q\<^sub>p \<and> a = c \<otimes> \<alpha>[^]n"
    using  assms True pow_res_refl[of a n] unfolding assms unfolding pow_res_def
     by blast
  show ?thesis
  proof(cases "b \<in> nonzero Q\<^sub>p")
    case T: True
    then have "d \<in> nonzero Q\<^sub>p"
      using assms pow_res_nonzero by blast
    then obtain \<beta> where beta_def: "\<beta> \<in> nonzero Q\<^sub>p \<and> b = d \<otimes> \<beta>[^]n"
      using  T pow_res_refl[of b n] unfolding assms unfolding pow_res_def
      using assms by blast
    then have "a \<otimes> b = (c \<otimes> d) \<otimes> (\<alpha>[^]n \<otimes> \<beta>[^] n)"
      using Qp.m_assoc Qp.m_lcomm Qp.nonzero_closed Qp.nonzero_mult_closed Qp_nat_pow_nonzero alpha_def assms(3) assms(4) assms(5) by presburger
    then have 0: "a \<otimes> b = (c \<otimes> d) \<otimes> ((\<alpha> \<otimes> \<beta>)[^] n)"
        by (metis Qp.nat_pow_distrib Qp.nonzero_closed alpha_def beta_def)
      show ?thesis
        apply(intro equal_pow_resI'[of _ _  "(\<alpha> \<otimes> \<beta>)[^] n"] Qp.ring_simprules assms
                    P_set_memI[of _ "\<alpha> \<otimes> \<beta>"] Qp.nat_pow_closed nonzero_memE 0 Qp_nat_pow_nonzero
                    )
        using alpha_def beta_def apply auto
        apply(intro nonzero_memI Qp.nonzero_mult_closed)
        using alpha_def beta_def nonzero_memE  apply auto
        by (meson Qp.integral_iff)
  next
    case False
    then have "b = \<zero>"
      by (meson assms not_nonzero_Qp)
    then have "d = \<zero>"
      using assms by (metis False not_nonzero_Qp pow_res_nonzero)
    then show ?thesis
      using Qp.r_null \<open>b = \<zero>\<close> assms  by presburger
  qed
next
  case False
  then have "a = \<zero>"
      by (meson assms  not_nonzero_Qp)
    then have "c = \<zero>"
      using assms by (metis False not_nonzero_Qp pow_res_nonzero)
    then show ?thesis
      using Qp.r_null \<open>a = \<zero>\<close> assms Qp.l_null by presburger
  qed

lemma pow_res_p_pow_factor:
  assumes "n > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "pow_res n a = pow_res n (\<pp>[^]((l::int)*n) \<otimes> a)"
proof(cases "a  = \<zero>")
  case True
  then show ?thesis
    using Qp.r_null p_intpow_closed(1) by presburger
next
  case False
  then show ?thesis using assms pow_res_of_p_pow
    using Qp.m_comm Qp.one_closed Qp.r_one p_intpow_closed(1) pow_res_mult by presburger
qed

lemma pow_res_classes_finite:
  assumes "n \<ge> 1"
  shows "finite (pow_res_classes n)"
proof(cases "n = 1")
  case True
  have "pow_res_classes n = {(nonzero Q\<^sub>p)}"
    using True pow_res_one unfolding pow_res_classes_def
    using Qp.one_nonzero by blast
  then show ?thesis by auto
next
  case False
  then have n_bound: "n \<ge> 2"
    using assms by linarith
  obtain m where m_def: "m > 0 \<and> (\<forall>x y. x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p \<and> ac m x = ac m y \<and> ord x = ord y \<longrightarrow> pow_res n x = pow_res n y)"
    using assms  False pow_res_equal_ord n_bound
    by (metis gr_zeroI le_numeral_extra(2))
  obtain f where f_def: "f  = (\<lambda> \<eta> \<nu>. (SOME y. y \<in> (pow_res_classes n) \<and> (\<exists> x \<in> y. ac m x = \<eta> \<and> ord x = \<nu>)))"
    by blast
  have 0: "\<And>x. x \<in> nonzero Q\<^sub>p \<Longrightarrow> pow_res n x = f (ac m x) (ord x)"
  proof- fix x assume A: "x \<in> nonzero Q\<^sub>p"
    obtain \<eta> where eta_def: "\<eta> = ac m x"
      by blast
    obtain \<nu> where nu_def: "\<nu> = ord x"
      by blast
    have "\<exists>y \<in>pow_res n x. ac m y = ac m x \<and> ord y = ord x"
      using pow_res_refl A assms neq0_conv Qp.nonzero_closed by blast
    hence "pow_res n x \<in> (pow_res_classes n) \<and> (\<exists> y \<in> (pow_res n x). ac m y = \<eta> \<and> ord y = \<nu>)"
      unfolding nu_def eta_def using assms unfolding pow_res_classes_def
      using A by blast
    then have 0: "(\<exists> y. y \<in> (pow_res_classes n) \<and> (\<exists> x \<in> y. ac m x = \<eta> \<and> ord x = \<nu>))"
      by blast
    have  "f \<eta> \<nu> = (SOME y. y \<in> (pow_res_classes n) \<and> (\<exists> x \<in> y. ac m x = \<eta> \<and> ord x = \<nu>))"
      using f_def by blast
    then have 1: "f \<eta> \<nu> \<in> (pow_res_classes n) \<and> ((\<exists> y \<in> (f \<eta> \<nu>).  ac m y = \<eta> \<and> ord y = \<nu>))"
      using  0  someI_ex[of "\<lambda> y. y \<in> (pow_res_classes n) \<and> (\<exists> x \<in> y. ac m x = \<eta> \<and> ord x = \<nu>)"]
      unfolding f_def by blast
    then obtain y where y_def: "y \<in> (f \<eta> \<nu>) \<and> ac m y = ac m x \<and> ord y =  ord x"
      unfolding nu_def eta_def by blast
    obtain a where a_def: "a \<in> nonzero Q\<^sub>p \<and> (f \<eta> \<nu>) = pow_res n a"
      using 1 unfolding pow_res_classes_def by blast
    then have 2: "y \<in> pow_res n a"
      using y_def by blast
    have 3: "y \<in> nonzero Q\<^sub>p"
      using y_def nonzero_pow_res[of a n] a_def by blast
    then have 4: "pow_res n y = pow_res n a"
      using 3 y_def a_def equal_pow_resI[of y a n]  n_bound Qp.nonzero_closed
      by (metis equal_pow_resI)
    have 5: "pow_res n y = f \<eta> \<nu>"
      using 4 a_def by blast
    then show "pow_res n x = f (ac m x) (ord x)"
      unfolding eta_def nu_def
      using "3" A m_def y_def by blast
  qed
  obtain N where N_def: "N > 0 \<and> (\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using n_bound nth_power_fact assms by blast
  have 1: "\<And>x. x \<in> nonzero Q\<^sub>p \<Longrightarrow> (\<exists>y \<in> nonzero Q\<^sub>p. ord y \<ge> 0 \<and> ord y < n \<and> pow_res n x = pow_res n y)"
  proof- fix x assume x_def: "x \<in> nonzero Q\<^sub>p"
    then obtain k where k_def: "k = ord x mod n"
      by blast
    then obtain l where l_def: "ord x = (int n)*l + k"
      using cancel_div_mod_rules(2)[of n "ord x"0] unfolding k_def
      by (metis group_add_class.add.right_cancel)
    have "x = (\<pp>[^](ord x)) \<otimes> \<iota> (angular_component x)"
      using x_def angular_component_factors_x by blast
    then have "x = (\<pp>[^](n*l + k)) \<otimes> \<iota> (angular_component x)"
      unfolding l_def by blast
    hence "x = \<pp>[^](int n*l) \<otimes> (\<pp>[^] k) \<otimes> \<iota> (angular_component x)"
      by (metis p_intpow_add)
    hence 0: "x = (\<pp>[^]l)[^]n \<otimes> (\<pp>[^] k) \<otimes> \<iota> (angular_component x)"
      using p_pow_factor[of n l k] \<open>x = \<pp> [^] (int n * l + k) \<otimes> \<iota> (angular_component x)\<close> by presburger
    have 1: "\<iota> (angular_component x) \<in> carrier Q\<^sub>p"
      using x_def angular_component_closed inc_closed by blast
    hence 2: "x = (\<pp>[^]l)[^]n \<otimes> ((\<pp>[^] k) \<otimes> \<iota> (angular_component x))"
      using 0 by (metis Qp.m_assoc Qp.nat_pow_closed p_intpow_closed(1))
    obtain a where a_def: "a = (\<pp>[^] k) \<otimes> \<iota> (angular_component x)"
      by blast
    have 30: "angular_component x \<in> Units Z\<^sub>p"
      using angular_component_unit x_def by blast
    then have 3: "\<iota> (angular_component x) \<in> Units Q\<^sub>p"
      by (metis Units_eq_nonzero Zp.Units_closed in_Units_imp_not_zero inc_of_nonzero not_nonzero_Qp)
    have 4: "\<iota> (angular_component x) \<in> nonzero Q\<^sub>p"
      using 3 Units_nonzero_Qp by blast
    have a_nonzero: "a \<in> nonzero Q\<^sub>p"
      unfolding a_def  4
      by (meson "3" Qp.UnitsI(1) Qp.Units_m_closed Units_nonzero_Qp p_intpow_closed(1) p_intpow_inv)
    have 5: "x = a \<otimes>(\<pp>[^]l)[^]n"
      using 2 a_nonzero unfolding a_def
      using Qp.m_comm Qp.nat_pow_closed Qp.nonzero_closed p_intpow_closed(1) by presburger
    hence "x \<in> pow_res n a"
      unfolding pow_res_def
      using Qp.nonzero_closed Qp_int_pow_nonzero p_nonzero x_def by blast
    hence 6:"pow_res n a = pow_res n x"
      using x_def a_def equal_pow_resI[of x  a n]  a_nonzero n_bound Qp.nonzero_closed equal_pow_resI
      by blast
    have 7: "ord (\<iota> (angular_component x)) = 0"
    proof-
      have "ord_Zp (angular_component x) = 0" using 30 Zp_Units_ord_zero by blast
      then have "val_Zp (angular_component x) = 0"
        using "30" unit_imp_val_Zp0 by blast
      then have "val (\<iota> (angular_component x)) = 0"
        by (metis angular_component_closed val_of_inc x_def)
      then show ?thesis using angular_component_closed x_def
        by (metis "30" Zp.Units_closed \<open>ord_Zp (angular_component x) = 0\<close> in_Units_imp_not_zero not_nonzero_Qp ord_of_inc)
    qed
    have 8: "ord a = k"
      unfolding a_def using 3 4 7 ord_mult[of "\<pp> [^] k" "\<iota> (angular_component x)"] ord_p_pow_int[of k]
                p_pow_nonzero
      using Qp_int_pow_nonzero p_nonzero by presburger
    have 9: "k < n"
      unfolding k_def
      using assms by auto
    from 6 8 9 assms have \<open>0 \<le> ord a\<close> \<open>ord a < int n\<close> \<open>pow_res n x = pow_res n a\<close>
      by (auto simp add: k_def)
    with a_nonzero show "\<exists>y\<in>nonzero Q\<^sub>p. 0 \<le> ord y \<and> ord y < int n \<and> pow_res n x = pow_res n y"
      by auto
  qed
  have 2: "\<And>x. x \<in> (pow_res_classes n) \<Longrightarrow> \<exists> \<eta> \<nu>. \<eta> \<in> Units (Zp_res_ring m) \<and> \<nu> \<in> {0..<int n} \<and> x = f \<eta> \<nu>"
  proof- fix a assume A: "a \<in> (pow_res_classes n)"
    then obtain x where x_def: "x \<in> nonzero Q\<^sub>p \<and> a = pow_res n x"
      unfolding pow_res_classes_def by blast
    then obtain x' where x'_def: "x' \<in> nonzero Q\<^sub>p \<and> ord x' \<ge> 0 \<and> ord x' < n \<and> pow_res n x' = a"
      using 1[of x] unfolding x_def by blast
    hence 20: "f (ac m x') (ord x') = a"
      using 0 by blast
    have 21: "ac m x' \<in> Units (Zp_res_ring m)"
      using x'_def ac_units m_def by presburger
    then have 22: "ac m x' \<in> Units (Zp_res_ring m) \<and> (ord x') \<in> ({0..<n}::int set ) \<and> a = f (ac m x') (ord x')"
      using x'_def 20 atLeastLessThan_iff by blast
    then show "\<exists> \<eta> \<nu>. \<eta> \<in> Units (Zp_res_ring m) \<and> \<nu> \<in> {0..<int n} \<and> a = f \<eta> \<nu>" by blast
  qed
  obtain F where F_def: "F = (\<lambda>ps. f (fst ps) (snd ps))"
    by blast
  have 3: "\<And>x. x \<in> (pow_res_classes n) \<Longrightarrow> \<exists> ps \<in> Units (Zp_res_ring m) \<times> {0..<int n}.  x = f (fst ps) (snd ps)"
  proof- fix x assume A: "x \<in> pow_res_classes n"
    obtain \<eta> \<nu> where eta_nu_def: " \<eta> \<in> Units (Zp_res_ring m) \<and> \<nu> \<in> {0..<int n} \<and> x = f \<eta> \<nu>"
      using 2 A by blast
    then have "F (\<eta>, \<nu>) = x"
      unfolding F_def by (metis fst_conv snd_conv)
    then show " \<exists> ps \<in> Units (Zp_res_ring m) \<times> {0..<int n}.  x = f (fst ps) (snd ps)"
      using eta_nu_def local.F_def by blast
  qed
  have 4: "pow_res_classes n \<subseteq> F ` (Units (Zp_res_ring m) \<times> {0..<int n})"
    unfolding F_def using 3
    by blast
  have "finite (Units (Zp_res_ring m))"
    using m_def residues.finite_Units unfolding residues_def
    by (metis Qp.one_nonzero ac_in_res_ring ac_one' p_res_ring_one p_residue_ring_car_memE(1))
  hence "finite (Units (Zp_res_ring m) \<times> {0..<int n})"
    by blast
  then show "finite (pow_res_classes n)"
    using 4 by (meson finite_surj)
qed

lemma pow_res_classes_univ_semialg:
  assumes "S \<in> pow_res_classes n"
  shows "is_univ_semialgebraic S"
proof-
  obtain x where x_def: "x\<in>nonzero Q\<^sub>p \<and> S = pow_res n x"
  using assms unfolding pow_res_classes_def by blast
  then show ?thesis using pow_res_is_univ_semialgebraic
    using Qp.nonzero_closed by blast
qed

lemma pow_res_classes_semialg:
  assumes "S \<in> pow_res_classes n"
  shows "is_semialgebraic 1 (to_R1` S)"
  using pow_res_classes_univ_semialg
    assms(1)  is_univ_semialgebraicE by blast

definition nth_pow_wits where
"nth_pow_wits n = (\<lambda> S. (SOME x. x \<in> (S \<inter> \<O>\<^sub>p)))` (pow_res_classes n)"

lemma nth_pow_wits_finite:
  assumes "n > 0"
  shows "finite (nth_pow_wits n)"
proof-
  have "n \<ge> 1"
    by (simp add: assms leI)
  thus ?thesis
    unfolding nth_pow_wits_def using assms pow_res_classes_finite[of n] by blast
qed

lemma nth_pow_wits_covers:
  assumes "n > 0"
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "\<exists>y \<in> (nth_pow_wits n). y \<in> nonzero Q\<^sub>p \<and> y \<in> \<O>\<^sub>p \<and> x \<in> pow_res n y"
proof-
  have PP: "(pow_res n x) \<in> pow_res_classes n"
    unfolding pow_res_classes_def using assms by blast
  obtain k where k_def: "val x = eint k"
    using assms val_ord by blast
  obtain N::int where N_def: "N = (if  k < 0 then -k else k)" by blast
  then have N_nonneg: "N \<ge> 0"
    unfolding N_def
    by presburger
  have 0: "int n \<ge> 1"
    using assms by linarith
  have "N*(int n) + k \<ge> 0"
  proof(cases "k<0")
    case True then have "N = -k" unfolding N_def
      by presburger
    then have "N*n + k = k*(1- int n)"
      using distrib_left[of k 1 "-int n"] mult_cancel_left2 mult_minus_left
      by (metis add.inverse_inverse diff_minus_eq_add minus_mult_minus neg_equal_iff_equal uminus_add_conv_diff)
    then show ?thesis using 0 True  zero_less_mult_iff[of k "1 - int n"]
   proof -
     have "0 \<le> N * (int n - 1)"
       by (meson "0" N_nonneg diff_ge_0_iff_ge zero_le_mult_iff)
     then show ?thesis
       by (metis (no_types) \<open>N = - k\<close> add.commute distrib_left minus_add_cancel mult_minus1_right uminus_add_conv_diff)
   qed
  next
    case False
    then have "N = k" unfolding N_def
      by presburger
    then show ?thesis using 0 False
      by (metis N_nonneg add_increasing2 mult_nonneg_nonneg of_nat_0_le_iff)
  qed
  then have 1: "ord (\<pp>[^](N*n)\<otimes>x) \<ge> 0"
    using ord_mult k_def val_ord assms
    by (metis Qp_int_pow_nonzero eint.inject ord_p_pow_int p_nonzero)
  have 2: "\<pp>[^](N*n)\<otimes>x \<in> pow_res n x"
  proof-
    have "\<pp>[^](N*n) = (\<pp>[^]N)[^]n"
      using Qp_p_int_nat_pow_pow by blast
    then have "\<pp>[^]N \<in> nonzero Q\<^sub>p  \<and> \<pp>[^](N*n)\<otimes>x = x \<otimes> (\<pp>[^]N)[^]n"
      by (metis Qp.m_comm Qp.nonzero_closed Qp_int_pow_nonzero assms(2) p_nonzero)
    then show ?thesis unfolding pow_res_def
      by (metis (mono_tags, lifting) Qp.m_closed Qp.nonzero_closed assms(2) mem_Collect_eq p_intpow_closed(1))
  qed
  have 3: "\<pp>[^](N*n)\<otimes>x \<in> \<O>\<^sub>p"
    using 1 assms
    by (metis Q\<^sub>p_def Qp.nonzero_mult_closed Qp_int_pow_nonzero Z\<^sub>p_def val_ring_ord_criterion \<iota>_def p_nonzero padic_fields.zero_in_val_ring padic_fields_axioms)
  have 4: "x \<in> pow_res n (\<pp>[^](N*n)\<otimes>x)"
    using 2 equal_pow_resI[of x "\<pp>[^](N*n)\<otimes>x" n] pow_res_refl[of "\<pp>[^](N*n)\<otimes>x" n] assms
         Qp.nonzero_mult_closed p_intpow_closed(2) pow_res_refl Qp.nonzero_closed by metis
  have 5: "\<pp>[^](N*n)\<otimes>x \<in> (pow_res n x \<inter> \<O>\<^sub>p)"
    using 2 3 by blast
  have 6: "(SOME z. z \<in> (pow_res n x) \<inter> \<O>\<^sub>p) \<in> pow_res n x \<inter> \<O>\<^sub>p" using 5
    by (meson someI)
  obtain y where y_def: "y = (SOME z. z \<in> (pow_res n x) \<inter> \<O>\<^sub>p)"
    by blast
  then have A: "y \<in> pow_res n x"
    using "6" by blast
  then have "pow_res n x = pow_res n y"
    using equal_pow_resI[of x y n] assms y_def Qp.nonzero_closed nonzero_pow_res by blast
  then have 7: "x \<in> pow_res n y"
    using pow_res_refl[of x n] assms unfolding nonzero_def by blast
  have 8: "y \<in> nonzero Q\<^sub>p  "
    using y_def PP 6 A nonzero_pow_res[of x n] assms
    by blast
  have 9: "y \<in> \<O>\<^sub>p"
    using y_def "6" by blast
  have "y\<in>(\<lambda>S. SOME x. x \<in> S \<inter> \<O>\<^sub>p) ` pow_res_classes n \<and> y \<in> nonzero Q\<^sub>p \<and> y \<in> \<O>\<^sub>p \<and> x \<in> pow_res n y"
        using y_def PP 6 7 8 9 A nonzero_pow_res[of x n] assms
        by blast
  then show ?thesis unfolding nth_pow_wits_def by blast
qed

lemma nth_pow_wits_closed:
  assumes "n > 0"
  assumes "x \<in> nth_pow_wits n"
  shows "x \<in> carrier Q\<^sub>p" "x \<in> \<O>\<^sub>p" "x \<in> nonzero Q\<^sub>p" "\<exists> y \<in> pow_res_classes n. y = pow_res n x"
proof-
  obtain c where c_def: "c \<in> pow_res_classes n \<and> x =   (SOME x. x \<in> (c \<inter> \<O>\<^sub>p))"
    by (metis (no_types, lifting) assms(2) image_iff nth_pow_wits_def)
  then obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and> c = pow_res n y"
    unfolding pow_res_classes_def by blast
  then obtain a where a_def: "a \<in> (nth_pow_wits n) \<and> a \<in> nonzero Q\<^sub>p \<and> a \<in> \<O>\<^sub>p \<and> y \<in> pow_res n a"
    using nth_pow_wits_covers[of n y] assms(1) by blast
  have 00: "pow_res n a = c"
    using equal_pow_resI[of a y n] y_def assms a_def unfolding nonzero_def by blast
  then have P :"a \<in> c \<inter> \<O>\<^sub>p"
    using pow_res_refl[of a n] assms a_def unfolding 00 nonzero_def by blast
  then show 0: "x \<in> \<O>\<^sub>p" using c_def
    by (metis Collect_mem_eq Int_Collect tfl_some)
  then show "x \<in> carrier Q\<^sub>p"
    using val_ring_memE by blast
  have 1: "c \<subseteq> nonzero Q\<^sub>p"
    using c_def nonzero_pow_res[of y n] unfolding pow_res_classes_def
    using assms(1) y_def by blast
  have "(SOME x. x \<in> (c \<inter> \<O>\<^sub>p)) \<in> (c \<inter> \<O>\<^sub>p)"
    using P tfl_some
    by (smt Int_def someI_ex)
  then have 2: "x \<in> c"
    using c_def by blast
  thus "x \<in> nonzero Q\<^sub>p"
    using 1  by blast
  show "\<exists> y \<in> pow_res_classes n. y = pow_res n x"
    using 00 2 c_def P a_def equal_pow_resI[of a x n] 0 val_ring_memE assms(1) by blast
qed

lemma finite_extensional_funcset:
  assumes "finite A"
  assumes "finite (B::'b set)"
  shows "finite (A \<rightarrow>\<^sub>E B)"
  using finite_PiE[of A "\<lambda>_. B"] assms by blast

lemma nth_pow_wits_exists:
  assumes  "m > 0"
  assumes "c \<in> pow_res_classes m"
  shows "\<exists>x. x \<in> c \<inter> \<O>\<^sub>p"
proof-
  obtain x where x_def: "x \<in> nonzero Q\<^sub>p \<and> pow_res m x = c"
    using assms unfolding pow_res_classes_def by blast
  obtain y where y_def: "y \<in> (nth_pow_wits m) \<and> y \<in> nonzero Q\<^sub>p \<and> y \<in> \<O>\<^sub>p \<and> x \<in> pow_res m y"
    using nth_pow_wits_covers assms x_def
    by blast
  have 0: "pow_res m x = pow_res m y"
    using x_def y_def equal_pow_resI Qp.nonzero_closed assms(1) by blast
  then have 1: "y \<in> pow_res m  x"
    using pow_res_refl[of y m ] y_def assms unfolding nonzero_def  by blast
  thus ?thesis using x_def y_def assms
    by blast
qed

lemma pow_res_classes_mem_eq:
  assumes "m > 0"
  assumes "a \<in> pow_res_classes m"
  assumes "x \<in> a"
  shows  "a = pow_res m x"
proof-
  obtain y where y_def: "y \<in> nonzero Q\<^sub>p \<and> a = pow_res m y"
    using assms unfolding pow_res_classes_def by blast
  then show ?thesis using assms equal_pow_resI[of y x m]
    by (meson Qp.nonzero_closed nonzero_pow_res equal_pow_resI subsetD)
qed

lemma nth_pow_wits_neq_pow_res:
  assumes  "m > 0"
  assumes "x \<in> nth_pow_wits m"
  assumes "y \<in> nth_pow_wits m"
  assumes "x \<noteq> y"
  shows "pow_res m x \<noteq> pow_res m y"
proof-
  obtain a where a_def: "a \<in> pow_res_classes m \<and> x = (\<lambda> S. (SOME x. x \<in> (S \<inter> \<O>\<^sub>p))) a"
    using assms unfolding nth_pow_wits_def by blast
  obtain b where b_def: "b \<in> pow_res_classes m \<and> y = (\<lambda> S. (SOME x. x \<in> (S \<inter> \<O>\<^sub>p))) b"
    using assms unfolding nth_pow_wits_def by blast
  have a_neq_b: "a \<noteq> b"
    using assms a_def b_def by blast
  have 0: "x \<in> a \<inter> \<O>\<^sub>p"
    using a_def nth_pow_wits_exists[of m a] assms
    by (meson someI_ex)
  have 1: "y \<in> b \<inter> \<O>\<^sub>p"
    using b_def nth_pow_wits_exists[of m b] assms
    by (meson someI_ex)
  have 2: "pow_res m x = a"
    using a_def  pow_res_classes_mem_eq[of m a x] assms 0
    by blast
  have 3: "pow_res m y = b"
    using b_def  pow_res_classes_mem_eq[of m b y] assms 1
    by blast
  show ?thesis
    by (simp add: "2" "3" a_neq_b)
qed

lemma nth_pow_wits_disjoint_pow_res:
  assumes  "m > 0"
  assumes "x \<in> nth_pow_wits m"
  assumes "y \<in> nth_pow_wits m"
  assumes "x \<noteq> y"
  shows "pow_res m x \<inter> pow_res m y =  {}"
  using assms nth_pow_wits_neq_pow_res disjoint_iff_not_equal
  by (metis (no_types, opaque_lifting) nth_pow_wits_closed(4) pow_res_classes_mem_eq)

lemma nth_power_fact':
  assumes "0 < (n::nat)"
  shows "\<exists>m>0. \<forall>u\<in>carrier Q\<^sub>p. ac m u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  using nth_power_fact[of n] assms
  by (metis less_one less_or_eq_imp_le linorder_neqE_nat neq0_conv)

lemma equal_pow_res_criterion:
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "a = b \<otimes> (\<one> \<oplus> c)"
  assumes "val c \<ge> N"
  shows "pow_res n a = pow_res n b"
proof(cases "b = \<zero>")
  case True
  then have "a = \<zero>"
    using assms Qp.add.m_closed Qp.l_null Qp.one_closed by presburger
  then show ?thesis using True
    by blast
next
  case False
  then have F0: "a \<div> b = \<one> \<oplus> c"
    by (metis Qp.Units_one_closed Qp.add.m_closed Qp.inv_cancelR(2) Qp.one_closed Qp.unit_factor assms(4) assms(5) assms(6) assms(7) field_inv(2) inv_in_frac(1))
  have "0 < eint N"
    using assms by (metis eint_ord_simps(2) of_nat_0_less_iff zero_eint_def)
  hence F1: "val \<one> < val c"
    using assms less_le_trans[of 0 N "val c"] unfolding val_one
    by blast
  hence F2: " val \<one> = val (\<one> \<oplus> c)"
    using assms val_one one_nonzero Qp.add.m_comm Qp.one_closed val_ultrametric_noteq by metis
  have "val \<one> + eint (int N) \<le> val (\<one> \<ominus> (\<one> \<oplus> c))"
  proof-
    have "val (\<one> \<ominus> (\<one> \<oplus> c)) = val c"
      using Qp.add.inv_closed Qp.minus_eq Qp.minus_sum Qp.one_closed Qp.r_neg2 assms(6) val_minus by presburger
    thus ?thesis
    unfolding val_one using assms F1 by (metis add.left_neutral)
  qed
  hence F3: "ac N \<one> = ac N (\<one> \<oplus> c)"
    using F2  F1 assms ac_val[of \<one> "\<one> \<oplus> c" N]
    by (metis Qp.add.m_closed Qp.one_closed val_nonzero)
  have F4: "\<one> \<oplus> c \<in> P_set n"
    using assms F1 F2 F3 val_one ac_one
    by (metis Qp.add.m_closed Qp.one_closed Qp.one_nonzero ac_inv'' ac_inv'''(1) ac_one')
  then show ?thesis
    using assms(2) assms(4) assms(5) assms(7) equal_pow_resI' by blast
qed



lemma pow_res_nat_pow:
  assumes "n > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "pow_res n a = pow_res n b"
  shows "pow_res n (a[^](k::nat)) = pow_res n (b[^]k)"
  apply(induction k)
  using assms apply (metis Group.nat_pow_0)
  using assms pow_res_mult by (smt Qp.nat_pow_Suc2 Qp.nat_pow_closed)

lemma pow_res_mult':
  assumes "n > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  assumes "e \<in> carrier Q\<^sub>p"
  assumes "f \<in> carrier Q\<^sub>p"
  assumes "pow_res n a = pow_res n d"
  assumes "pow_res n b = pow_res n e"
  assumes "pow_res n c = pow_res n f"
  shows "pow_res n (a \<otimes> b \<otimes> c) = pow_res n (d \<otimes> e \<otimes> f)"
proof-
  have "pow_res n (a \<otimes> b) = pow_res n (d \<otimes> e)"
    using pow_res_mult assms  by meson
  then show ?thesis using pow_res_mult assms
    by (meson Qp.m_closed)
qed

lemma pow_res_disjoint:
  assumes "n > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "a \<notin> pow_res n \<one>"
  shows "\<not> (\<exists>y \<in> nonzero Q\<^sub>p. a = y[^]n)"
  using assms unfolding pow_res_def
  using Qp.l_one Qp.nonzero_closed by blast

lemma pow_res_disjoint':
  assumes "n > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "pow_res n a \<noteq> pow_res n \<one>"
  shows "\<not> (\<exists>y \<in> nonzero Q\<^sub>p. a = y[^]n)"
using assms pow_res_disjoint pow_res_refl
  by (metis pow_res_nth_pow)

lemma pow_res_one_imp_nth_pow:
  assumes "n > 0"
  assumes "a \<in> pow_res n \<one>"
  shows "\<exists>y \<in> nonzero Q\<^sub>p. a = y[^]n"
  using assms unfolding pow_res_def
  using Qp.l_one Qp.nat_pow_closed Qp.nonzero_closed by blast

lemma pow_res_eq:
  assumes "n > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> pow_res n a"
  shows "pow_res n b = pow_res n a"
proof(cases "a = \<zero>")
  case True
  then show ?thesis using assms by (metis pow_res_zero singletonD)
next
  case False
  then have a_nonzero: "a \<in> nonzero Q\<^sub>p" using Qp.not_nonzero_memE assms(2) by blast
  show ?thesis
  proof(cases "n = 1")
    case True
    then show ?thesis using a_nonzero assms
      using pow_res_one Q\<^sub>p_def Zp_def padic_fields_axioms by blast
  next
    case False
    then have "n \<ge> 2"
      using assms(1) by linarith
    then show ?thesis using False a_nonzero assms Qp.nonzero_closed nonzero_pow_res equal_pow_resI
      by blast
  qed
qed

lemma pow_res_classes_n_eq_one:
"pow_res_classes 1 = {nonzero Q\<^sub>p}"
  unfolding pow_res_classes_def using pow_res_one Qp.one_nonzero by blast

lemma nth_pow_wits_closed':
  assumes "n > 0"
  assumes "x \<in> nth_pow_wits n"
  shows "x \<in> \<O>\<^sub>p \<and> x \<in> nonzero Q\<^sub>p" using nth_pow_wits_closed
  assms  by blast


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Semialgebraic Sets Defined by Congruences\<close>
(**************************************************************************************************)
(**************************************************************************************************)

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>$p$-adic ord Congruence Sets\<close>
      (********************************************************************************************)
      (********************************************************************************************)

lemma carrier_is_univ_semialgebraic:
"is_univ_semialgebraic (carrier Q\<^sub>p)"
  apply(rule is_univ_semialgebraicI)
  using Qp.to_R1_carrier carrier_is_semialgebraic
  by presburger

lemma nonzero_is_univ_semialgebraic:
"is_univ_semialgebraic (nonzero Q\<^sub>p)"
proof-
  have "nonzero Q\<^sub>p = carrier Q\<^sub>p - {\<zero>}"
    unfolding nonzero_def by blast
  then show ?thesis using  diff_is_univ_semialgebraic[of "carrier Q\<^sub>p" "{\<zero>}"]
    by (metis Diff_empty Diff_insert0 carrier_is_univ_semialgebraic empty_subsetI
        finite.emptyI finite.insertI finite_is_univ_semialgebraic insert_subset)
qed

definition ord_congruence_set where
"ord_congruence_set n a = {x \<in> nonzero Q\<^sub>p. ord x mod n = a}"

lemma ord_congruence_set_nonzero:
"ord_congruence_set n a \<subseteq> nonzero Q\<^sub>p"
  by (metis (no_types, lifting) mem_Collect_eq ord_congruence_set_def subsetI)

lemma ord_congruence_set_closed:
"ord_congruence_set n a \<subseteq> carrier Q\<^sub>p"
  using nonzero_def ord_congruence_set_nonzero
  unfolding nonzero_def
  by (meson Qp.nonzero_closed ord_congruence_set_nonzero subset_iff)

lemma ord_congruence_set_memE:
  assumes "x \<in> ord_congruence_set n a"
  shows "x \<in> nonzero Q\<^sub>p"
        "ord x mod n = a"
  using assms ord_congruence_set_nonzero apply blast
  by (metis (mono_tags, lifting) assms mem_Collect_eq ord_congruence_set_def)

lemma ord_congruence_set_memI:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "ord x mod n = a"
  shows "x \<in> ord_congruence_set n a"
  using assms
  by (metis (mono_tags, lifting) mem_Collect_eq ord_congruence_set_def)

text\<open>
  We want to prove that ord\_congruence\_set is a finite union of semialgebraic sets,
  hence is also semialgebraic.
\<close>

lemma pow_res_ord_cong:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "x \<in> ord_congruence_set n a"
  shows "pow_res n x \<subseteq> ord_congruence_set n a"
proof fix y
  assume A: "y  \<in> pow_res n x"
  show "y \<in> ord_congruence_set (int n) a"
  proof-
    obtain a where a_def: "a \<in> nonzero Q\<^sub>p \<and> y = x \<otimes> (a[^]n)"
      using A pow_res_def[of n x] by blast
    have 0: "x \<in> nonzero Q\<^sub>p"
      using assms(2) ord_congruence_set_memE(1)
      by blast
    have 1: "y \<in> nonzero Q\<^sub>p"
      using A
      by (metis "0" Qp.integral Qp.nonzero_closed Qp.nonzero_mult_closed Qp_nat_pow_nonzero a_def not_nonzero_Qp)
    have 2: "ord y = ord x + n* ord  a"
      using a_def 0 1 Qp_nat_pow_nonzero nonzero_nat_pow_ord ord_mult
      by presburger
    show ?thesis
      apply(rule ord_congruence_set_memI)
      using assms ord_congruence_set_memE 2 1
       apply blast
      using "2" assms(2) ord_congruence_set_memE(2)
      by presburger
  qed
qed

lemma pow_res_classes_are_univ_semialgebraic:
  shows "are_univ_semialgebraic (pow_res_classes n)"
  apply(rule are_univ_semialgebraicI)
  using pow_res_classes_univ_semialg by blast

lemma ord_congruence_set_univ_semialg:
  assumes "n \<ge> 0"
  shows "is_univ_semialgebraic (ord_congruence_set n a)"
proof(cases "n = 0")
  case True
  have T0: "ord_congruence_set n a = {x \<in> nonzero Q\<^sub>p. ord x = a}"
    unfolding ord_congruence_set_def True by presburger
  have T1: "{x \<in> nonzero Q\<^sub>p. ord x = a} = {x \<in> nonzero Q\<^sub>p. val x = a}"
    apply(rule equalityI'')
    using val_ord apply blast
    using val_ord
    by (metis eint.inject)
  have T2: "{x \<in> nonzero Q\<^sub>p. val x = a} = {x \<in> carrier Q\<^sub>p. val x = a}"
    apply(rule equalityI'')
    using Qp.nonzero_closed apply blast
    by (metis iless_Suc_eq val_nonzero val_val_ring_prod zero_in_val_ring)
  show ?thesis unfolding T0 T1 T2 using univ_val_eq_set_is_univ_semialgebraic by blast
next
  case False
  obtain F where F_def: "F = {S \<in> (pow_res_classes (nat n)). S \<subseteq>(ord_congruence_set n a) }"
    by blast
  have 0: "F \<subseteq> pow_res_classes (nat n)"
    using F_def by blast
  have 1: "finite F"
    using 0 False nat_mono[of 1 n] nat_numeral[] pow_res_classes_finite[of "nat n"] rev_finite_subset
    by (smt assms nat_one_as_int)
  have 2: "are_univ_semialgebraic F"
    apply(rule are_univ_semialgebraicI) using 0 pow_res_classes_are_univ_semialgebraic
    by (metis (mono_tags) are_univ_semialgebraicE are_univ_semialgebraic_def assms  nat_mono nat_numeral subset_iff)
  have 3: "\<Union> F = (ord_congruence_set n a)"
  proof
    show "\<Union> F \<subseteq> ord_congruence_set n a"
      using F_def
      by blast
    show "ord_congruence_set n a \<subseteq> \<Union> F"
    proof fix x
      assume A: "x \<in> ord_congruence_set n a"
      have x_nonzero: "x \<in> nonzero Q\<^sub>p"
        using A ord_congruence_set_memE(1) by blast
      have 0: "pow_res (nat n) x \<in> F"
        using A pow_res_classes_def F_def
        by (smt nonzero_def assms mem_Collect_eq nat_0_le ord_congruence_set_memE(1) pow_res_ord_cong)
      have 1: "x \<in> pow_res (nat n) x" using False x_nonzero assms pow_res_refl[of x "nat n"]
        using Qp.nonzero_closed by blast
      show "x \<in> \<Union> F"
        using 0 1
        by blast
    qed
  qed
  then show ?thesis
    using "1" "2" finite_union_is_univ_semialgebraic'
    by fastforce
qed

lemma ord_congruence_set_is_semialg:
  assumes "n \<ge> 0"
  shows "is_semialgebraic 1 (Qp_to_R1_set (ord_congruence_set n a))"
  using assms is_univ_semialgebraicE ord_congruence_set_univ_semialg
  by blast

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Congruence Sets for the order of the Evaluation of a Polynomial\<close>
      (********************************************************************************************)
      (********************************************************************************************)


lemma poly_map_singleton:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "poly_map n [f] x = [(Qp_ev f x)]"
  unfolding poly_map_def poly_tuple_eval_def
  using assms
  by (metis (no_types, lifting) Cons_eq_map_conv list.simps(8) restrict_apply')

definition poly_cong_set where
"poly_cong_set n f m a = {x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>). (Qp_ev f x) \<noteq> \<zero>  \<and> (ord (Qp_ev f x) mod m = a)}"

lemma poly_cong_set_as_pullback:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "poly_cong_set n f m a = poly_map n [f]  \<inverse>\<^bsub>n\<^esub>(Qp_to_R1_set (ord_congruence_set m a))"
proof
  show "poly_cong_set n f m a \<subseteq> poly_map n [f]  \<inverse>\<^bsub>n\<^esub> ((\<lambda>a. [a]) ` ord_congruence_set m a)"
  proof fix x
    assume A: "x \<in> poly_cong_set n f m a"
    then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      by (metis (no_types, lifting) mem_Collect_eq poly_cong_set_def)
    have 1: "(Qp_ev f x) \<noteq> \<zero> "
      by (metis (mono_tags, lifting) A mem_Collect_eq poly_cong_set_def)
    have 2: "(ord (Qp_ev f x) mod m = a)"
      by (metis (mono_tags, lifting) A mem_Collect_eq poly_cong_set_def)
    have 3: "(Qp_ev f x) \<in> (ord_congruence_set m a)"
      using "0" "1" "2" eval_at_point_closed assms not_nonzero_Qp ord_congruence_set_memI
      by metis
    show "x \<in> poly_map n [f]  \<inverse>\<^bsub>n\<^esub> ((\<lambda>a. [a]) ` ord_congruence_set m a)"
    proof-
      have 00: "poly_map n [f] x = [(Qp_ev f x)]"
        using "0" assms poly_map_singleton by blast
      have 01: "[eval_at_point Q\<^sub>p x f] \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        using "0" assms eval_at_point_closed Qp.to_R1_closed by blast
      hence 02: "poly_map n [f] x \<in> (\<lambda>a. [a]) ` ord_congruence_set m a"
        using 3 "00" by blast
      then show "x \<in> poly_map n [f]  \<inverse>\<^bsub>n\<^esub> ((\<lambda>a. [a]) ` ord_congruence_set m a)"
        using 0 unfolding evimage_def
        by blast
    qed
  qed
  show "poly_map n [f] \<inverse>\<^bsub>n\<^esub> (\<lambda>a. [a]) ` ord_congruence_set m a
              \<subseteq> poly_cong_set n f m a"
  proof fix x
    assume A: "x \<in> poly_map n [f] \<inverse>\<^bsub>n\<^esub> ((\<lambda>a. [a]) ` (ord_congruence_set m a))"
    have 0: "((\<lambda>a. [a]) ` ord_congruence_set m a) \<subseteq> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
      using ord_congruence_set_closed Qp.to_R1_carrier by blast
    have "is_poly_tuple n [f]"
      using assms unfolding is_poly_tuple_def
      by (simp add: assms)
    then have 1:"poly_map n [f] \<inverse>\<^bsub>n\<^esub>((\<lambda>a. [a]) ` ord_congruence_set m a) \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using 0 A assms One_nat_def
      by (metis extensional_vimage_closed)
   then have 2: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
     using A unfolding evimage_def by blast
    then have 3: "poly_map n [f] x \<in> ((\<lambda>a. [a]) ` ord_congruence_set m a)"
      using A assms 0 One_nat_def
      by blast
    have "poly_map n [f] x = [(Qp_ev f x)]"
      using "2" assms poly_map_singleton by blast
    then have "Qp_ev f x \<in> ord_congruence_set m a"
      using 3
      by (metis (mono_tags, lifting) image_iff list.inject)
    then show "x \<in> poly_cong_set n f m a"
      unfolding poly_cong_set_def
      by (metis (mono_tags, lifting) "2" Qp.nonzero_memE(2)
          mem_Collect_eq ord_congruence_set_memE(1) ord_congruence_set_memE(2))
  qed
qed

lemma singleton_poly_tuple:
"is_poly_tuple n [f] \<longleftrightarrow> f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  unfolding is_poly_tuple_def
  by (metis (no_types, lifting) list.distinct(1) list.set_cases list.set_intros(1) set_ConsD subset_code(1))

lemma poly_cong_set_is_semialgebraic:
  assumes "m \<ge> 0"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialgebraic n (poly_cong_set n f m a)"
proof-
  have 0: "(\<lambda>a. [a]) ` ord_congruence_set m a \<in> semialg_sets 1"
  using assms
        ord_congruence_set_is_semialg[of m a]
  unfolding is_semialgebraic_def
  by blast
  have 1: "length [f] = 1"
  by simp
  hence " poly_map n [f] \<inverse>\<^bsub>n\<^esub> (\<lambda>a. [a]) ` ord_congruence_set m a \<in> semialg_sets n"
    using 0 singleton_poly_tuple[of n f] zero_neq_one assms
    pullback_is_semialg[of n "[f]" 1 "(\<lambda>a. [a]) ` ord_congruence_set m a"]
  unfolding is_semialgebraic_def
  by blast
  thus ?thesis using assms poly_cong_set_as_pullback[of f n m a]
  unfolding is_semialgebraic_def
  by presburger
qed

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Congruence Sets for Angular Components\<close>
      (********************************************************************************************)
      (********************************************************************************************)


text\<open>If a set is a union of \<open>n\<close>-th power residues, then it is semialgebraic.\<close>

lemma pow_res_union_imp_semialg:
  assumes "n \<ge> 1"
  assumes "S \<subseteq> nonzero Q\<^sub>p"
  assumes "\<And>x. x \<in> S \<Longrightarrow> pow_res n x \<subseteq> S"
  shows "is_univ_semialgebraic S"
proof-
  obtain F where F_def: "F = {T. T \<in> pow_res_classes n \<and> T \<subseteq> S}"
    by blast
  have 0: "F \<subseteq> pow_res_classes n"
    using F_def by blast
  have 1: "finite F"
    using 0 pow_res_classes_finite[of n] assms(1) finite_subset
    by auto
  have 2: "are_univ_semialgebraic F"
    using 0
    by (meson are_univ_semialgebraicE are_univ_semialgebraicI assms(1)
        pow_res_classes_are_univ_semialgebraic padic_fields_axioms subsetD)
  have 3: "S = \<Union> F"
  proof
    show "S \<subseteq> \<Union> F"
    proof fix x
      assume A: "x \<in> S"
      then have "pow_res n x \<subseteq> S"
        using assms(3) by blast
      then have "pow_res n x \<in> F"
        using A assms(2) F_def pow_res_classes_def
        by (smt mem_Collect_eq subsetD)
      then have "pow_res n x \<subseteq> \<Union> F"
        by blast
      then show "x \<in> \<Union> F"
        using A assms(1) assms(2) pow_res_refl[of x n] unfolding nonzero_def by blast
    qed
    show "\<Union> F \<subseteq> S"
      using F_def
      by blast
  qed
  show ?thesis
    using 1 2 3 finite_union_is_univ_semialgebraic'
    by blast
qed

definition ac_cong_set1 where
"ac_cong_set1 n y = {x \<in> carrier Q\<^sub>p. x \<noteq> \<zero> \<and> ac n x = ac n y}"

lemma ac_cong_set1_is_univ_semialg:
  assumes "n > 0"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "is_univ_semialgebraic (ac_cong_set1 n b)"
proof(cases "n = 1 \<and> p = 2")
  case True
  have "(ac_cong_set1 n b) = nonzero Q\<^sub>p"
  proof
    have 0: "Units (Zp_res_ring n) = {1}"
    proof show "Units (Zp_res_ring n) \<subseteq> {1}"
      proof fix x assume A: "x \<in> Units (Zp_res_ring n)"
        have 0: "carrier (Zp_res_ring n) = {0..(int 2) - 1}"
          using True
          by (metis assms(1) int_ops(3) p_residues power_one_right residues.res_carrier_eq)
        have 1: "carrier (Zp_res_ring n) = {0..(1::int)}"
        proof- have "int 2 - 1 = (1::int)"
                    by linarith
                  then show ?thesis
                    using 0
                    by presburger
        qed
        have 15: "{0..(1::int)} = {0, (1::int)}"
          using atLeastAtMostPlus1_int_conv [of 0 "0::int"]
          by (smt atLeastAtMost_singleton insert_commute)
        have 2: "carrier (Zp_res_ring n) = {0,(1::int)}"
          using "1" "15"
          by blast
        have 3: "0 \<notin> Units (Zp_res_ring n)"
          using True zero_not_in_residue_units by blast
        have "x \<in> carrier (Zp_res_ring n)"
          using A unfolding Units_def by blast
        then have "x = 1" using A  2 3
          by (metis "1" atLeastAtMost_iff atLeastatMost_empty
              atLeastatMost_empty_iff2 linorder_neqE_linordered_idom mod_by_1 mod_pos_pos_trivial )
        then show "x \<in> {1}"
          by simp
      qed
      show "{1} \<subseteq> Units (Zp_res_ring n)"
        by (meson assms(1) empty_subsetI insert_subset residue_1_unit(1))
    qed
    show "ac_cong_set1 n b \<subseteq> nonzero Q\<^sub>p"
      by (metis (mono_tags, lifting) ac_cong_set1_def mem_Collect_eq not_nonzero_Qp subsetI)
    show "nonzero Q\<^sub>p \<subseteq> ac_cong_set1 n b"
    proof fix x
      assume A: "x \<in> nonzero Q\<^sub>p"
      then have P0: "ac n x = 1"
        using 0 ac_units assms(1) by blast
      have P1: "ac n b = 1"
        using assms 0 ac_units assms(1) by blast
      then have "ac n x = ac n b"
        using P0 by metis
      then show " x \<in> ac_cong_set1 n b"
        unfolding ac_cong_set1_def using A
      proof -
        have "x \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero>}"
          by (metis (no_types) \<open>x \<in> nonzero Q\<^sub>p\<close> nonzero_def )
        then show "x \<in> {r \<in> carrier Q\<^sub>p. r \<noteq> \<zero> \<and> ac n r = ac n b}"
          using \<open>ac n x = ac n b\<close> by force
      qed
    qed
  qed
  then show "is_univ_semialgebraic (ac_cong_set1 n b)"
    by (simp add: nonzero_is_univ_semialgebraic)
next
  case F: False
  have F0: "2 \<le> card (Units (Zp_res_ring n))"
  proof(cases "n = 1")
    case True
    then have "field (Zp_res_ring n)"
       using p_res_ring_1_field by blast
    then have F00: "Units (Zp_res_ring n) = carrier (Zp_res_ring n) - {\<zero>\<^bsub>Zp_res_ring n\<^esub>}"
      using field.field_Units by blast
    have F01: "\<zero>\<^bsub>Zp_res_ring n\<^esub> \<in> carrier (Zp_res_ring n)"
      using assms(1) cring.cring_simprules(2) padic_integers.R_cring padic_integers_axioms by blast
    have F02: "card (carrier (Zp_res_ring n)) = p \<and> finite (carrier (Zp_res_ring n))"
      by (smt F01 True nat_eq_iff2 p_res_ring_zero p_residue_ring_car_memE(1) power_one_right residue_ring_card)
    have F03: "\<zero>\<^bsub>residue_ring (p ^ n)\<^esub> \<in> carrier (residue_ring (p ^ n)) "
      using F01 by blast
    have F04: "int (card (carrier (residue_ring (p ^ n)))) \<ge> int (card {\<zero>\<^bsub>residue_ring (p ^ n)\<^esub>}) "
      by (smt F02 F03 nat_int of_nat_0_le_iff of_nat_1 of_nat_power p_res_ring_0 p_res_ring_zero
          p_residue_ring_car_memE(1) power_increasing power_one_right residue_ring_card)
    have "card (carrier (residue_ring (p ^ n))) - 1 = p - 1"
      using F02 prime
      by (metis Totient.of_nat_eq_1_iff True less_imp_le_nat less_one nat_int nat_less_eq_zless
          of_nat_1 of_nat_diff of_nat_zero_less_power_iff p_residues pos_int_cases
          power_0 power_one_right residue_ring_card residues.m_gt_one zero_le_one)
    hence F05: "card (carrier (residue_ring (p ^ n)) - {\<zero>\<^bsub>residue_ring (p ^ n)\<^esub>}) = p - 1"
      using F02 F03 F04 card_Diff_singleton_if[of "(carrier (Zp_res_ring n))" "\<zero>\<^bsub>residue_ring (p^n)\<^esub>"]
           True int_ops(6)[of "card (carrier (residue_ring (p ^ n)))" "card {\<zero>\<^bsub>residue_ring (p ^ n)\<^esub>}"]
           p_res_ring_zero p_residue_ring_car_memE(1)
      by (metis)
  hence F06: "card (Units (Zp_res_ring n)) = p -1"
      using True F02 F01 F00
      by (metis p_res_ring_zero)
    have F04: "p - 1 \<ge>2 "
      using F prime
      by (meson True linorder_cases not_less prime_ge_2_int zle_diff1_eq)
    then show ?thesis
      using F03 F06
      by linarith
  next
    case False
    then show ?thesis
      by (metis assms(1) less_imp_le_nat mod2_gr_0 mod_less nat_le_linear nat_neq_iff residue_units_card_geq_2)
  qed
  show ?thesis
  apply(rule pow_res_union_imp_semialg[of "card (Units (Zp_res_ring n))"])
  using F0 assms apply linarith
  apply (metis (mono_tags, lifting) ac_cong_set1_def mem_Collect_eq not_nonzero_Qp subsetI)
proof-
  fix x
  assume AA: "x \<in> ac_cong_set1 n b"
  show "pow_res (card (Units (Zp_res_ring n))) x \<subseteq> ac_cong_set1 n b"
  proof
    fix y
    assume A: "y \<in> pow_res (card (Units (Zp_res_ring n))) x"
    show "y \<in> ac_cong_set1 n b"
    proof-
      obtain k where k_def: "k = card (Units (Zp_res_ring n))"
        by blast
      have "k \<ge>2"
        using assms k_def  F F0 by blast
      then obtain a where a_def: "a \<in> nonzero Q\<^sub>p \<and> y = x \<otimes> (a[^]k)"
        using  k_def A pow_res_def[of k x]
        by blast
      have 0: "x \<in> nonzero Q\<^sub>p"
        using AA ac_cong_set1_def
        by (metis (mono_tags, lifting) mem_Collect_eq not_nonzero_Qp)
      have 1: "y \<in> nonzero Q\<^sub>p"
        by (metis "0" Qp.Units_m_closed Qp_nat_pow_nonzero Units_eq_nonzero \<open>\<And>thesis. (\<And>a. a \<in> nonzero Q\<^sub>p \<and> y = x \<otimes> a [^] k \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
      have "ac n y = ac n x \<otimes>\<^bsub>Zp_res_ring n\<^esub> ac n (a[^]k)"
        using a_def 0 1 Qp_nat_pow_nonzero ac_mult'
        by blast
      then have 2: "ac n y = ac n x \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n a)[^]\<^bsub>Zp_res_ring n\<^esub> k"
      proof-
        have "ac n (a[^]k) = ac n a [^]\<^bsub>Zp_res_ring n\<^esub> k"
          using a_def assms(1) ac_nat_pow'[of a n k]
          by linarith
        then show ?thesis
          using \<open>ac n y = ac n x \<otimes>\<^bsub>Zp_res_ring n\<^esub> ac n (a[^]k)\<close>
          by presburger
      qed
      then have "ac n y = ac n x"
      proof-
        have "(ac n a) \<in> Units (Zp_res_ring n)"
          by (metis (mono_tags, opaque_lifting) a_def ac_units assms(1) )
        then have "(ac n a)^k mod (p^n) = 1"
          using k_def a_def ac_nat_pow ac_nat_pow' assms(1) residue_units_nilpotent
          using neq0_conv by presburger
        then have 00: "(ac n a)[^]\<^bsub>Zp_res_ring n\<^esub> k = 1"
          by (metis a_def ac_nat_pow ac_nat_pow' mod_by_1 power_0
              zero_neq_one)
        have "ac n x \<otimes>\<^bsub>residue_ring (p ^ n)\<^esub> ac n a [^]\<^bsub>residue_ring (p ^ n)\<^esub> k = ac n x \<otimes>\<^bsub>Zp_res_ring n\<^esub> \<one>\<^bsub>Zp_res_ring n\<^esub>"
          using 00  assms(1) p_res_ring_one by presburger
        hence "ac n x \<otimes>\<^bsub>residue_ring (p ^ n)\<^esub> ac n a [^]\<^bsub>residue_ring (p ^ n)\<^esub> k = ac n x"
          by (metis "0" Qp.nonzero_closed Qp.one_nonzero Qp.r_one ac_mult' ac_one' assms(1))
        then show ?thesis
          using 2 "0" 00
          by linarith
      qed
      then show ?thesis
        using  "1" AA nonzero_def
            ac_cong_set1_def[of n b] mem_Collect_eq
        by smt
    qed
  qed
qed
qed

definition ac_cong_set where
"ac_cong_set n k = {x \<in> carrier Q\<^sub>p. x \<noteq> \<zero> \<and> ac n x = k}"

lemma ac_cong_set_is_univ_semialg:
  assumes "n >0 "
  assumes "k \<in> Units (Zp_res_ring n)"
  shows "is_univ_semialgebraic (ac_cong_set n k)"
proof-
  have "k \<in> carrier (Zp_res_ring n)"
    using assms(2) Units_def[of "Zp_res_ring n"]
    by blast
  then have k_n: "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) n = k"
    using assms
    by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
  obtain b where b_def: "b = \<iota> ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    by blast
  have 0: "k mod p \<noteq> 0"
    using assms residue_UnitsE[of n k]
    by (metis le_eq_less_or_eq le_refl less_one nat_le_linear p_residues power_0
        power_one_right residues.mod_in_res_units residues_def zero_less_one
        zero_neq_one zero_not_in_residue_units zero_power)
  then have "val_Zp ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = 0"
    using val_Zp_p_int_unit by blast
  then have 1: "val b = 0"
    by (metis Zp_int_inc_closed b_def val_of_inc)
  have 2: "b \<in> \<O>\<^sub>p"
    using b_def Zp_int_mult_closed
    by blast
  have "ord_Zp ([k] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = 0"
    using 0 ord_Zp_p_int_unit by blast
  have "ac_Zp ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using "0" Zp_int_inc_closed ac_Zp_of_Unit ord_Zp_p_int_unit \<open>val_Zp ([k] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = 0\<close>
    by blast
  then have "(angular_component b) = ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using b_def 1 2 angular_component_ord_zero[of b]
    by (metis Qp.int_inc_zero Qp.one_closed val_ring_memE Zp.int_inc_zero Zp.one_closed
        Zp.one_nonzero Zp_int_inc_closed angular_component_of_inclusion inc_closed inc_of_int
        inc_of_one inc_to_Zp local.val_zero not_nonzero_Qp val_ineq val_one zero_in_val_ring)
  then have "ac n b = k"
    using ac_def[of n b] k_n
    by (metis Qp_char_0_int Zp_defs(1) ac_def b_def inc_of_int inc_of_one)
  then have 3: "(ac_cong_set n k) = (ac_cong_set1 n b)"
    unfolding ac_cong_set_def ac_cong_set1_def
    by meson
  have 4: "b \<in> nonzero Q\<^sub>p"
    using 1 2 val_nonzero
    by (metis Qp.one_closed val_ring_memE Zp_def \<iota>_def local.one_neq_zero
        not_nonzero_Qp padic_fields.val_ring_memE padic_fields_axioms val_ineq val_one)
  then show ?thesis
    using 1 2 3 assms ac_cong_set1_is_univ_semialg[of n b] val_nonzero[of b 1]
    by presburger
qed

definition val_ring_constant_ac_set where
"val_ring_constant_ac_set n k = {a \<in> \<O>\<^sub>p. val a = 0 \<and> ac n a = k}"

lemma val_nonzero':
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a = eint k"
  shows "a \<in> nonzero Q\<^sub>p"
  using val_nonzero[of a "k + 1"]
  by (metis Suc_ile_eq assms(1) assms(2) eint_ord_code(3) val_nonzero)

lemma val_ord':
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq>\<zero>"
  shows "val a = ord a"
  by (meson assms(1) assms(2) not_nonzero_Qp val_ord)

lemma val_ring_constant_ac_set_is_univ_semialgebraic:
  assumes "n > 0"
  assumes "k \<noteq> 0"
  shows "is_univ_semialgebraic (val_ring_constant_ac_set n k)"
proof(cases "val_ring_constant_ac_set n k = {}")
  case True
  then show ?thesis
    by (metis equals0D order_refl pow_res_union_imp_semialg subsetI)
next
  case False
  then obtain b where b_def: "b \<in> val_ring_constant_ac_set n k"
    by blast
  have 0: "val_ring_constant_ac_set n k = q_ball n k 0 \<zero>"
  proof
    show "val_ring_constant_ac_set n k \<subseteq> q_ball n k 0 \<zero>"
    proof fix x assume A: "x \<in> val_ring_constant_ac_set n k" then
      show "x \<in> q_ball n k 0 \<zero>"
      proof-
        have 0: "x \<in> \<O>\<^sub>p \<and> val x = 0 \<and> ac n x = k"
          using A
          unfolding val_ring_constant_ac_set_def
          by blast
        then have x_car: "x \<in> carrier Q\<^sub>p"
          using val_ring_memE
          by blast
        then have 00: "x = x \<ominus> \<zero>"
          using Qp.ring_simprules by metis
        then have 1: "ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<zero>) = k"
          using 0
          by presburger
        have 2: "val (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<zero>) = 0"
          using 0 00
          by metis
        have 3: "x \<in> nonzero Q\<^sub>p"
        proof(rule ccontr)
          assume " x \<notin> nonzero Q\<^sub>p "
          then have "x = \<zero>"
            using Qp.nonzero_memI x_car by blast
          then show False
            using 0 val_zero
            by (metis ac_def assms(2))
        qed
        have 4: "ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<zero>) = 0"
        proof(rule ccontr)
          assume "ord (x \<ominus> \<zero>) \<noteq> 0"
          then have "val (x \<ominus> \<zero>) \<noteq> 0"
            by (metis "00" "3" Qp.one_closed equal_val_imp_equal_ord(1) ord_one val_one)
          then show False
            using "2"
            by blast
        qed
        show ?thesis
          using 0 1 4
          unfolding  q_ball_def
          using x_car by blast
      qed
    qed
    show "q_ball n k 0 \<zero> \<subseteq> val_ring_constant_ac_set n k"
    proof fix x
      assume A: "x \<in> q_ball n k 0 \<zero>"
      then have 0: "ac n (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<zero>) = k"
        using q_ballE'(1) by blast
      have 1: "ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> \<zero>) = 0"
        using q_ball_def A
        by blast
      have 2: "x \<in> carrier Q\<^sub>p"
        using A q_ball_def by blast
      have 3: "ord x = 0"
        using 2 1 ring.ring_simprules[of Q\<^sub>p]
        by (metis Qp.ring_axioms)
      have 4: "ac n x = k"
        using 0 2 1  cring.axioms(1)[of Q\<^sub>p] ring.ring_simprules[of Q\<^sub>p]
         by (metis Qp.ring_axioms)
       have 5: "x \<in> \<O>\<^sub>p"
         using Qp_val_ringI[of x] 2 3 val_ord val_nonzero'
         by (metis Qp.integral_iff val_ring_memE Zp.nonzero_closed angular_component_closed
             angular_component_ord_zero image_eqI local.numer_denom_facts(1) local.numer_denom_facts(2)
             local.numer_denom_facts(4) not_nonzero_Qp)
       have 6: "x \<noteq> \<zero>"
         using 4 assms ac_def[of n x]
         by meson
       have 7: "val x = 0"
         using 6 3 2 assms val_ord' zero_eint_def by presburger
       show " x \<in> val_ring_constant_ac_set n k"
         unfolding val_ring_constant_ac_set_def
         using 7 6 5 4
         by blast
    qed
  qed
  obtain b where b_def: "b \<in> q_ball n k (0::int) \<zero>"
    using "0" b_def by blast
  have 1: "b \<in> carrier Q\<^sub>p \<and> ac n b = k"
    using b_def unfolding q_ball_def
    by (metis (mono_tags, lifting) "0" b_def mem_Collect_eq val_ring_constant_ac_set_def)
  then have 2: "b \<in> nonzero Q\<^sub>p"
    using 1 assms
    by (metis ac_def not_nonzero_Qp)
  have "q_ball n k 0 \<zero> = B\<^bsub>0 + int n\<^esub>[b]"
    using  1 b_def nonzero_def [of Q\<^sub>p] assms 0 2 c_ball_q_ball[of b n k "\<zero>" b 0]
    by (meson Qp.cring_axioms cring.cring_simprules(2))
  then have "is_univ_semialgebraic (q_ball n k (0::int) \<zero>) "
    using 1 ball_is_univ_semialgebraic[of b "0 + int n"]
    by  metis
  then show ?thesis
    using 0 by presburger
qed

definition val_ring_constant_ac_sets where
"val_ring_constant_ac_sets n = val_ring_constant_ac_set n ` (Units (Zp_res_ring n))"

lemma val_ring_constant_ac_sets_are_univ_semialgebraic:
  assumes "n > 0"
  shows "are_univ_semialgebraic (val_ring_constant_ac_sets n)"
proof(rule are_univ_semialgebraicI)
  have 0: "\<not> coprime 0 p"
    using coprime_0_right_iff[of p] coprime_commute[of p 0] coprime_int_iff[of "nat p" 0]
        nat_dvd_1_iff_1 prime_gt_1_nat zdvd1_eq
    by (metis not_prime_unit prime)
  have "(0::int) \<notin>(Units (Zp_res_ring n))"
    apply(rule ccontr)
    using 0 assms residues.cring[of "p ^ n"] unfolding residues_def
      by (smt less_one not_gr_zero power_le_imp_le_exp power_less_imp_less_exp residue_UnitsE)
  fix x
  assume A: "x \<in> val_ring_constant_ac_sets n"
  then obtain k where k_def: "x = val_ring_constant_ac_set n k \<and> k \<in> Units (Zp_res_ring n)"
    by (metis image_iff val_ring_constant_ac_sets_def)
  then show "is_univ_semialgebraic x"
    using assms
    by (metis \<open>0 \<notin> Units (Zp_res_ring n)\<close> val_ring_constant_ac_set_is_univ_semialgebraic)
qed

definition ac_cong_set3 where
"ac_cong_set3 n  = {as. \<exists> a b. a \<in> nonzero Q\<^sub>p \<and> b \<in> \<O>\<^sub>p \<and> val b = 0 \<and> (ac n a = ac n b) \<and> as = [a, b] }"

definition ac_cong_set2 where
"ac_cong_set2 n k = {as. \<exists> a b. a \<in> nonzero Q\<^sub>p \<and> b \<in> \<O>\<^sub>p \<and> val b = 0 \<and> (ac n a = k) \<and> (ac n b) = k \<and> as = [a, b] }"

lemma ac_cong_set2_cartesian_product:
  assumes "k \<in> Units (Zp_res_ring n)"
  assumes "n > 0"
  shows "ac_cong_set2 n k = cartesian_product (to_R1` (ac_cong_set n k)) (to_R1` (val_ring_constant_ac_set n k))"
proof
  show "ac_cong_set2 n k \<subseteq> cartesian_product ((\<lambda>a. [a]) ` ac_cong_set n k) ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k)"
  proof fix x
    assume A: "x \<in> ac_cong_set2 n k"
    show "x \<in> (cartesian_product ((\<lambda>a. [a]) ` ac_cong_set n k) ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k))"
      unfolding ac_cong_set_def val_ring_constant_ac_set_def ac_cong_set2_def
      apply(rule cartesian_product_memI[of _ Q\<^sub>p 1 _ 1])
       apply (metis (mono_tags, lifting) mem_Collect_eq subsetI Qp.to_R1_car_subset)
        apply (metis (no_types, lifting) val_ring_memE mem_Collect_eq subsetI Qp.to_R1_car_subset)
     proof-
       obtain a b where ab_def: "x = [a,b] \<and> a \<in> nonzero Q\<^sub>p \<and> b \<in> \<O>\<^sub>p \<and> val b = 0 \<and> (ac n a = k) \<and> (ac n b) = k"
         using A
         unfolding ac_cong_set_def val_ring_constant_ac_set_def ac_cong_set2_def
         by blast
       have 0: "take 1 x = [a]"
         by (simp add: ab_def)
       have 1: "drop 1 x = [b]"
         by (simp add: ab_def)
       have 2: "a \<in> {x \<in> carrier Q\<^sub>p. x \<noteq> \<zero> \<and> ac n x = k}"
         using ab_def nonzero_def
         by (smt mem_Collect_eq)
       have 3: "b \<in>  {a \<in> \<O>\<^sub>p. val a = 0 \<and> ac n a = k}"
         using ab_def
         by blast
       show "take 1 x \<in> (\<lambda>a. [a]) ` {x \<in> carrier Q\<^sub>p. x \<noteq> \<zero> \<and> ac n x = k}"
         using  0 2 by blast
       show "drop 1 x \<in> (\<lambda>a. [a]) ` {a \<in> \<O>\<^sub>p. val a = 0 \<and> ac n a = k}"
         using 1 3 by blast
     qed
  qed
  show "cartesian_product ((\<lambda>a. [a]) ` ac_cong_set n k) ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k) \<subseteq> ac_cong_set2 n k"
  proof fix x
    have 0: "(\<lambda>a. [a]) ` ac_cong_set n k \<subseteq> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
      using assms
      by (metis (no_types, lifting) ac_cong_set_def mem_Collect_eq subsetI Qp.to_R1_car_subset)
    have 1: "((\<lambda>a. [a]) ` val_ring_constant_ac_set n k) \<subseteq> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
      by (smt val_ring_memE mem_Collect_eq subsetI Qp.to_R1_carrier Qp.to_R1_subset val_ring_constant_ac_set_def)
    assume A: "x \<in> cartesian_product ((\<lambda>a. [a]) ` ac_cong_set n k) ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k)"
    then have "length x = 2"
      using 0 1 A cartesian_product_closed[of "((\<lambda>a. [a]) ` ac_cong_set n k)" Q\<^sub>p 1 "((\<lambda>a. [a]) ` val_ring_constant_ac_set n k)" 1]
      by (metis (no_types, lifting) cartesian_power_car_memE one_add_one subset_iff)
    then obtain a b where ab_def: "take 1 x = [a] \<and> drop 1 x = [b]"
      by (metis One_nat_def add_diff_cancel_left' drop0 drop_Cons_numeral numerals(1) pair_id plus_1_eq_Suc take0 take_Cons_numeral)
    have 2: " a \<in> (ac_cong_set n k) \<and> b \<in> (val_ring_constant_ac_set n k)"
    proof-
      have P0: "take 1 x \<in> (\<lambda>a. [a]) ` ac_cong_set n k"
        using 0 A cartesian_product_memE[of x "((\<lambda>a. [a]) ` ac_cong_set n k) " " ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k)" Q\<^sub>p 1]
        by blast
      have P1: "drop 1 x \<in> (\<lambda>a. [a]) ` val_ring_constant_ac_set n k"
        using 0 A cartesian_product_memE[of x "((\<lambda>a. [a]) ` ac_cong_set n k) " " ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k)" Q\<^sub>p 1]
        by blast
      have P2: "[a] \<in> (\<lambda>a. [a]) ` ac_cong_set n k"
        using P0 ab_def
        by metis
      have P3: "[b] \<in> (\<lambda>a. [a]) ` val_ring_constant_ac_set n k"
        using P1 ab_def by metis
      show ?thesis
        using P2 P3
        by blast
    qed
    have 3: "a \<in> nonzero Q\<^sub>p"
      using 2 assms nonzero_def [of Q\<^sub>p]  ac_cong_set_def[of n k]
      by blast
    have 4: "x = [a,b]"
      by (metis (no_types, lifting) \<open>length x = 2\<close> ab_def less_numeral_extra(1) nth_Cons_0 nth_take nth_via_drop pair_id)
    then have "\<exists>a b. a \<in> nonzero Q\<^sub>p \<and> b \<in> \<O>\<^sub>p \<and> val b = 0 \<and> ac n a = k \<and> ac n b = k \<and> x = [a, b]"
      using 2 3 ab_def  unfolding val_ring_constant_ac_set_def ac_cong_set_def
      by blast
    then show "x \<in> ac_cong_set2 n k"
      unfolding ac_cong_set2_def val_ring_constant_ac_set_def ac_cong_set_def
      by blast
  qed
qed

lemma ac_cong_set2_is_semialg:
  assumes "k \<in> Units (Zp_res_ring n)"
  assumes "n > 0"
  shows "is_semialgebraic 2 (ac_cong_set2 n k)"
  using  ac_cong_set_is_univ_semialg ac_cong_set2_cartesian_product[of k n]
      cartesian_product_is_semialgebraic[of 1 "((\<lambda>a. [a]) ` ac_cong_set n k)" 1 " ((\<lambda>a. [a]) ` val_ring_constant_ac_set n k)"]
  by (metis assms(1) assms(2) is_univ_semialgebraicE less_one less_or_eq_imp_le nat_neq_iff
      one_add_one val_ring_constant_ac_set_is_univ_semialgebraic zero_not_in_residue_units)

lemma ac_cong_set3_as_union:
  assumes "n > 0"
  shows "ac_cong_set3 n = \<Union> (ac_cong_set2 n ` (Units (Zp_res_ring n)) )"
proof
  show "ac_cong_set3 n \<subseteq> \<Union> (ac_cong_set2 n ` Units (Zp_res_ring n))"
  proof fix x assume A: "x \<in> ac_cong_set3 n"
    then have 0: "x \<in> (ac_cong_set2 n (ac n (x!0)))"
      unfolding ac_cong_set2_def ac_cong_set3_def
      by (smt mem_Collect_eq nth_Cons_0)
    have 1: "(ac n (x!0)) \<in> Units (Zp_res_ring n)"
      using A unfolding ac_cong_set3_def
      by (smt ac_units assms mem_Collect_eq nth_Cons_0)
    then show "x \<in> \<Union> (ac_cong_set2 n ` Units (Zp_res_ring n))"
      using 0
      by blast
  qed
  show "\<Union> (ac_cong_set2 n ` Units (Zp_res_ring n)) \<subseteq> ac_cong_set3 n"
  proof fix x assume A: "x \<in> \<Union> (ac_cong_set2 n ` Units (Zp_res_ring n))"
    obtain k where k_def: "x \<in> (ac_cong_set2 n k) \<and> k \<in> (Units (Zp_res_ring n))"
      using A by blast
    have 0: "k mod p \<noteq> 0"
      using k_def One_nat_def  Suc_le_eq assms less_numeral_extra(1)
          power_one_right residues.m_gt_one residues.mod_in_res_units
      by (metis p_residues residue_UnitsE zero_not_in_residue_units)
    obtain b where b_def: "b = ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
      by blast
    have "k \<noteq>0"
      using 0 mod_0
      by blast
    then have 1: "b \<in> nonzero Z\<^sub>p"
      using 0 b_def int_unit
      by (metis Zp.Units_nonzero Zp.zero_not_one)
    have 10: "ord_Zp b = 0" using 0 1
      using b_def ord_Zp_p_int_unit by blast
    have 2: "\<iota> b \<in> nonzero Q\<^sub>p" using k_def
      using "1" inc_of_nonzero by blast
    have 3: "angular_component (\<iota> b) = ac_Zp b"
      using "1" angular_component_of_inclusion
      by blast
    have 4: "ac_Zp b = b"
      using 1 10
      by (metis "3" Zp.r_one ac_Zp_factors' angular_component_closed inc_of_nonzero int_pow_0 mult_comm ord_Zp_def)
    have 5: "ac_Zp b n = k"
    proof-
      have "k \<in> carrier (Zp_res_ring n)"
        using k_def unfolding Units_def by blast
      then show ?thesis
        using b_def k_def 4 Zp_int_inc_res  mod_pos_pos_trivial
        by (metis p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
    qed
    then have "ac n (\<iota> b) = k"
      using 10 1 2 3 4 unfolding ac_def
      using Qp.not_nonzero_memI by metis
    then show "x \<in> ac_cong_set3 n"
      unfolding ac_cong_set3_def
      using k_def unfolding ac_cong_set2_def
      by (smt mem_Collect_eq)
  qed
qed

lemma ac_cong_set3_is_semialgebraic:
  assumes "n > 0"
  shows "is_semialgebraic 2 (ac_cong_set3 n)"
proof-
  have 0: "finite (ac_cong_set2 n ` (Units (Zp_res_ring n)) )"
    using assms residues.finite_Units[of "p^n"] unfolding residues_def
    using p_residues residues.finite_Units by blast
  have 1: "are_semialgebraic 2 (ac_cong_set2 n ` (Units (Zp_res_ring n)) )"
    apply(rule are_semialgebraicI)
    using ac_cong_set2_is_semialg assms by blast
  show ?thesis
    using 0 1 ac_cong_set3_as_union
    by (metis (no_types, lifting) are_semialgebraicE assms finite_union_is_semialgebraic' is_semialgebraicE subsetI)
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Permutations of indices of semialgebraic sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)


lemma fun_inv_permute:
  assumes "\<sigma> permutes {..<n}"
  shows "fun_inv \<sigma> permutes {..<n}"
        "\<sigma> \<circ> (fun_inv \<sigma>) = id"
        "(fun_inv \<sigma>) \<circ> \<sigma> = id"
  using assms unfolding fun_inv_def
  using permutes_inv apply blast
  using assms permutes_inv_o(1) apply blast
  using assms permutes_inv_o(2) by blast

lemma poly_tuple_pullback_eq_poly_map_vimage:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "S \<subseteq> carrir (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "poly_map n fs  \<inverse>\<^bsub>n\<^esub> S = poly_tuple_pullback n S fs"
  unfolding poly_map_def poly_tuple_pullback_def evimage_def restrict_def
  using assms
  by (smt vimage_inter_cong)

lemma permutation_is_semialgebraic:
  assumes "is_semialgebraic n S"
  assumes "\<sigma> permutes {..<n}"
  shows "is_semialgebraic n (permute_list \<sigma> ` S)"
proof-
  have "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms gen_boolean_algebra_subset is_semialgebraic_def semialg_sets_def
    by blast
  then have "(permute_list \<sigma> ` S) = poly_tuple_pullback n S (permute_list (fun_inv \<sigma>) (pvar_list Q\<^sub>p n))"
    using Qp.cring_axioms assms pullback_by_permutation_of_poly_list'[of  \<sigma> n S] unfolding poly_map_def
    by blast
  then have 0: "(permute_list \<sigma> ` S) = poly_tuple_pullback n S (permute_list (fun_inv \<sigma>) (pvar_list Q\<^sub>p n))"
    using poly_tuple_pullback_def
    by blast
  have 1: "(fun_inv \<sigma>) permutes {..<n}"
    using assms  unfolding fun_inv_def
    using permutes_inv by blast
  then show ?thesis using 1 pullback_is_semialg[of n "(permute_list (fun_inv \<sigma>) (pvar_list Q\<^sub>p n))"]
                         permutation_of_poly_list_is_poly_list[of  n "(pvar_list Q\<^sub>p n)" "fun_inv \<sigma>"]
                         pvar_list_is_poly_tuple[of n] assms poly_tuple_pullback_eq_poly_map_vimage
  by (metis "0" \<open>S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)\<close> is_semialgebraic_def length_permute_list pvar_list_length)
qed

lemma permute_list_closed:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "\<sigma> permutes {..<n}"
  shows "permute_list \<sigma> a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  apply(rule cartesian_power_car_memI)
  using assms cartesian_power_car_memE length_permute_list apply blast
  using assms cartesian_power_car_memE'' permute_list_set by blast

lemma permute_list_closed':
  assumes "\<sigma> permutes {..<n}"
  assumes "permute_list \<sigma> a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  apply(rule cartesian_power_car_memI)
  apply (metis assms(2) cartesian_power_car_memE length_permute_list)
  using assms cartesian_power_car_memE'[of "permute_list \<sigma> a" Q\<^sub>p n]
  by (metis cartesian_power_car_memE in_set_conv_nth length_permute_list set_permute_list subsetI)

lemma permute_list_compose_inv:
  assumes "\<sigma> permutes {..<n}"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "permute_list \<sigma> (permute_list (fun_inv \<sigma>) a) = a"
        "permute_list (fun_inv \<sigma>) (permute_list \<sigma> a) = a"
  using assms apply (metis cartesian_power_car_memE fun_inv_permute(3) permute_list_compose permute_list_id)
  using assms by (metis cartesian_power_car_memE fun_inv_permute(2) fun_inv_permute(1) permute_list_compose permute_list_id)

lemma permutation_is_semialgebraic_imp_is_semialgebraic:
  assumes "is_semialgebraic n (permute_list \<sigma> ` S)"
  assumes "\<sigma> permutes {..<n}"
  shows "is_semialgebraic n S"
proof-
  have "permute_list (fun_inv \<sigma>) ` (permute_list \<sigma> ` S) = S"
  proof-
    have 0: "(permute_list \<sigma> ` S) \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      using assms unfolding is_semialgebraic_def semialg_sets_def
      using gen_boolean_algebra_subset by blast
    have 1: "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    proof fix x assume "x \<in> S" then show "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
        using 0 assms
        by (meson image_subset_iff permute_list_closed')
    qed
    show ?thesis
    proof show "permute_list (fun_inv \<sigma>) ` permute_list \<sigma> ` S \<subseteq> S"
        using 0 assms permute_list_compose_inv[of \<sigma>]  "1" image_iff image_subset_iff subsetD
        by smt
        show "S \<subseteq> permute_list (fun_inv \<sigma>) ` permute_list \<sigma> ` S"
        using 0 assms permute_list_compose_inv[of \<sigma>]
        by (smt "1" image_iff subset_eq)
    qed
  qed
  then show ?thesis using permutation_is_semialgebraic
    by (metis assms(1) assms(2)  fun_inv_permute(1))
qed

lemma split_cartesian_product_is_semialgebraic:
  assumes "i \<le> n"
  assumes "is_semialgebraic n A"
  assumes "is_semialgebraic m B"
  shows "is_semialgebraic (n + m) (split_cartesian_product n m i A B)"
  using assms cartesian_product_is_semialgebraic scp_permutes[of i n m]
        permutation_is_semialgebraic[of "n + m" "cartesian_product A B" "(scp_permutation n m i)"]
  unfolding split_cartesian_product_def
  by blast

definition reverse_val_relation_set where
"reverse_val_relation_set = {as \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (as ! 0) \<le> val (as ! 1)}"

lemma  Qp_2_car_memE:
  assumes  "x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
  shows "x = [x!0, x!1]"
proof-
  have "length x = 2"
    using assms cartesian_power_car_memE by blast
  then show ?thesis
    using pair_id by blast
qed

definition flip where
"flip =  (\<lambda>i::nat. (if i = 0 then 1 else (if i = 1 then 0 else i)))"

lemma flip_permutes:
"flip permutes {0,1}"
 unfolding permutes_def flip_def
 by (smt mem_simps(1))

lemma flip_eval:
"flip 0 = 1"
"flip 1 = 0"
  unfolding flip_def
  by auto

lemma flip_x:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
  shows "permute_list flip x = [x!1, x!0]"
proof-
  have 0: "x = [x!0, x!1]"
    using assms Qp_2_car_memE by blast
  have 1: "length (permute_list flip x) = length [x!1, x!0]"
    using 0 unfolding permute_list_def
    by (metis length_Cons length_map map_nth)
  have 2: "\<And>i. i < 2 \<Longrightarrow> permute_list flip x ! i = [x!1, x!0] ! i"
  proof- fix i::nat assume A: "i < 2"
    show "permute_list flip x ! i = [x!1, x!0] ! i"
      using 0 unfolding permute_list_def
      by (smt flip_eval(1) flip_eval(2) length_Cons length_greater_0_conv list.simps(8) map_upt_Suc numeral_nat(7) upt_rec)
  qed
  have "\<And>i. i < length x \<Longrightarrow> permute_list flip x ! i = [x!1, x!0] ! i"
  proof-
  have 0:  "length x = 2"
      using assms cartesian_power_car_memE by blast
      show  "\<And>i. i < length x \<Longrightarrow> permute_list flip x ! i = [x!1, x!0] ! i" using 2 unfolding 0
        by blast
  qed
  thus ?thesis using 1
    by (metis length_permute_list nth_equalityI)
qed

lemma permute_with_flip_closed:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>2::nat\<^esup>)"
  shows  "permute_list  flip x \<in> carrier (Q\<^sub>p\<^bsup>2::nat\<^esup>)"
  apply(rule permute_list_closed)
  using assms apply blast
proof-
  have "{0::nat, 1} = {..<2::nat}"
    by auto
  thus "flip permutes {..<2}"
  using flip_permutes
  by auto
qed

lemma reverse_val_relation_set_semialg:
"is_semialgebraic 2 reverse_val_relation_set"
proof-
  have 1: "reverse_val_relation_set = permute_list flip `  val_relation_set"
    apply(rule equalityI')
  proof-
    show " \<And>x. x \<in> reverse_val_relation_set \<Longrightarrow> x \<in> permute_list flip ` val_relation_set"
      proof- fix x assume A: "x \<in> reverse_val_relation_set"
    have 0: "permute_list flip x = [x ! 1, x ! 0]"
      using flip_x[of x] A unfolding reverse_val_relation_set_def
      by blast
    have 1: "permute_list flip x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
      apply(rule permute_with_flip_closed) using A unfolding reverse_val_relation_set_def by blast
    have 2: "permute_list flip x \<in> val_relation_set"
      using 1 A unfolding 0 reverse_val_relation_set_def val_relation_set_def mem_Collect_eq
      by (metis Qp_2_car_memE list_hd list_tl)
    show "x \<in> permute_list flip ` val_relation_set"
      using flip_x[of x] A unfolding reverse_val_relation_set_def val_relation_set_def mem_Collect_eq
      by (metis (no_types, lifting) "1" "2" Qp_2_car_memE flip_x image_eqI list_tl nth_Cons_0 val_relation_set_def)
    qed
    show "\<And>x. x \<in> permute_list flip ` val_relation_set \<Longrightarrow> x \<in> reverse_val_relation_set"
    proof- fix x assume a: " x \<in> permute_list flip ` val_relation_set"
      then obtain y where y_def: "y \<in> val_relation_set \<and>x = permute_list flip y"
        by blast
      have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
        using y_def basic_semialg_set_memE(1) val_relation_semialg by blast
      have y_length: " length y = 2"
        using y_def basic_semialg_set_memE  val_relation_semialg
        by (metis cartesian_power_car_memE)
      obtain a b where ab_def: "y = [a,b]"
        using y_length pair_id by blast
      have 0: "a = y!0"
        using ab_def
        by (metis nth_Cons_0)
      have 1: "b = y!1"
        using ab_def
        by (metis cancel_comm_monoid_add_class.diff_cancel eq_numeral_extra(2) nth_Cons')
      have a_closed: "a \<in> carrier Q\<^sub>p"
        using 0 y_closed unfolding 0
        by (meson cartesian_power_car_memE' rel_simps(75) zero_order(5))
      have b_closed: "b \<in> carrier Q\<^sub>p"
      proof-
        have "1 < (2::nat)" by linarith
        thus ?thesis
        using y_closed unfolding 1
        by (meson cartesian_power_car_memE')
      qed
      have 2: "x = [b, a]" using flip_x[of y] y_def y_closed unfolding  ab_def unfolding 0 1
        using \<open>y \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>) \<Longrightarrow> permute_list flip y = [y ! 1, y ! 0]\<close> y_closed y_def by presburger
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
        using  y_def unfolding val_relation_set_def using permute_with_flip_closed[of y]
        by blast
      show " x \<in> reverse_val_relation_set"
        using x_closed  y_def
        unfolding val_relation_set_def reverse_val_relation_set_def  mem_Collect_eq 2 0 1
        by (metis Qp_2_car_memE list_hd list_tl)
    qed
  qed
  show ?thesis unfolding 1
    apply(rule permutation_is_semialgebraic)
    using val_relation_is_semialgebraic apply blast
    using flip_permutes
    by (metis Suc_1 insert_commute lessThan_0 lessThan_Suc numeral_nat(7))
qed

definition strict_val_relation_set where
"strict_val_relation_set = {as \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (as ! 0) < val (as ! 1)}"

definition val_diag where
"val_diag = {as \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (as ! 0) = val (as ! 1)}"

lemma val_diag_semialg:
"is_semialgebraic 2 val_diag"
proof-
  have "val_diag = val_relation_set \<inter>reverse_val_relation_set"
    apply(rule equalityI')
    apply(rule IntI)
    unfolding val_diag_def val_relation_set_def reverse_val_relation_set_def mem_Collect_eq
  apply simp
  apply simp
      apply(erule IntE) unfolding mem_Collect_eq
    using basic_trans_rules(24) by blast
  then show ?thesis using intersection_is_semialg
    by (simp add: reverse_val_relation_set_semialg val_relation_is_semialgebraic)
qed

lemma strict_val_relation_set_is_semialg:
"is_semialgebraic 2 strict_val_relation_set"
proof-
  have 0: "strict_val_relation_set = reverse_val_relation_set - val_diag"
    apply(rule equalityI')
    apply(rule DiffI)
    unfolding strict_val_relation_set_def val_diag_def val_relation_set_def reverse_val_relation_set_def mem_Collect_eq
    using order_le_less apply blast
  proof
    show "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>) \<and> val (x ! 0) < val (x ! 1) \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>) \<and> val (x ! 0) = val (x ! 1) \<Longrightarrow> False"
      using order_less_le by blast
    show " \<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (as ! 0) \<le> val (as ! 1)} - {as \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>). val (as ! 0) = val (as ! 1)} \<Longrightarrow>
         x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>) \<and> val (x ! 0) < val (x ! 1)"
      apply(erule DiffE) unfolding mem_Collect_eq using order_le_less by blast
  qed
  show ?thesis unfolding 0
    apply(rule diff_is_semialgebraic )
    using reverse_val_relation_set_semialg apply blast
        using val_diag_semialg by blast
qed

lemma singleton_length:
  "length [a] = 1"
  by auto

lemma take_closed':
  assumes "m > 0"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  shows "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  apply(rule take_closed[of m "m+l"])
  apply simp using assms by blast

lemma triple_val_ineq_set_semialg:
  shows "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1) \<and> val (as!1) \<le> val (as!2)}"
proof-
  have 0: "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1)}"
  proof-
    have 0: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1)} = cartesian_product (reverse_val_relation_set) (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
    proof(rule equalityI')
      show " \<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 0) \<le> val (as ! 1)} \<Longrightarrow> x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
      proof- fix x assume A: " x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 0) \<le> val (as ! 1)}"
        then have 0: "length x = 3" unfolding mem_Collect_eq
          using cartesian_power_car_memE by blast
        obtain a where a_def: "a = [x!0, x!1]"
          by blast
        have a_length: "length a = 2"
        proof-
          have "a = x!0 #[x!1]"
            unfolding a_def
            by blast
          thus ?thesis using  length_Cons[of "x!0" "[x!1]"] unfolding singleton_length[of "x!1"]
            by presburger
        qed
        obtain b where b_def: "b = [x!2]"
          by blast
        have b_length: "length b = 1"
          unfolding b_def singleton_length by auto
        have a_closed: "a \<in> reverse_val_relation_set"
        proof-
          have 0: "a = take 2 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_take[of 2 x]
             apply linarith
          proof- fix i::nat assume  a: "i < 2" show "a ! i = take 2 x ! i "
              apply(cases "i = 0")
               apply (metis a_def nth_Cons_0 nth_take zero_less_numeral)
              by (smt "0" \<open>length (take 2 x) = min (length x) 2\<close> a_def linorder_neqE_nat min.commute min.strict_order_iff nth_take numeral_eq_iff one_less_numeral_iff pair_id pos2 rel_simps(22) rel_simps(48) rel_simps(9) semiring_norm(81))
          qed
          have 1: "a \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
            apply(rule cartesian_power_car_memI')
             apply (simp add: a_length)
            unfolding 0 using A unfolding mem_Collect_eq
            using cartesian_power_car_memE' by fastforce
          show ?thesis using 1 A unfolding a_def reverse_val_relation_set_def A mem_Collect_eq
             by (metis Qp_2_car_memE list_tl nth_Cons_0)
        qed
        have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
          apply(rule cartesian_power_car_memI)
          unfolding b_length apply blast
          apply(rule subsetI)
          unfolding b_def using A unfolding mem_Collect_eq using cartesian_power_car_memE'[of x Q\<^sub>p "3::nat"  "2::nat"]
          by simp
        have 2: "x = a@b"
          apply(rule nth_equalityI)
          using 0 unfolding a_length b_length  length_append[of a b] apply presburger
        proof- fix i assume A: "i < length x"
          then have A1: "i < 3"
            unfolding 0 by blast
          show "x ! i = (a @ b) ! i"
            apply(cases "i = 0")
             apply (metis a_def append.simps(2) nth_Cons_0)
            apply(cases "(i:: nat) = 1")
             apply (simp add: a_def)

          proof- assume a: "i \<noteq>0" "i \<noteq> 1"
            then have "i = 2"
              using A1 by presburger
            thus ?thesis
              by (metis a_length b_def nth_append_length)
          qed
        qed
        have 3: "a = take 2 x"
          apply(rule nth_equalityI)
          unfolding a_length  0 length_take[of 2 x]
           apply linarith
          proof- fix i::nat assume  a: "i < 2" show "a ! i = take 2 x ! i "
              apply(cases "i = 0")
               apply (metis a_def nth_Cons_0 nth_take zero_less_numeral)
              by (smt "0" \<open>length (take 2 x) = min (length x) 2\<close> a_def linorder_neqE_nat min.commute min.strict_order_iff nth_take numeral_eq_iff one_less_numeral_iff pair_id pos2 rel_simps(22) rel_simps(48) rel_simps(9) semiring_norm(81))
          qed
        show " x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
          apply(rule cartesian_product_memI[of _ Q\<^sub>p 2 _ 1])
             apply (simp add: is_semialgebraic_closed reverse_val_relation_set_semialg)
            apply blast
          using 3  a_closed apply blast
        proof-
          have "drop 2 x = b"
            unfolding 2 unfolding 3 using 0
            by simp
          then show "drop 2 x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
            using b_closed by blast
        qed
      qed
      show "\<And>x. x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) \<Longrightarrow> x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 0) \<le> val (as ! 1)}"
      proof fix x assume A: "x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
        then obtain a b where ab_def: "a \<in> reverse_val_relation_set" "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)" "x = a@b"
          using cartesian_product_memE'[of x reverse_val_relation_set "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
          by metis
        have a_length: "length a = 2"
          using ab_def unfolding reverse_val_relation_set_def
          using cartesian_power_car_memE by blast
        have "(0::nat)< 2" by presburger
        hence  0: "x!0 = a!0"
          unfolding ab_def using a_length
          by (metis append.simps(2) nth_Cons_0 pair_id)
        have "(1::nat)< 2" by presburger
        hence 1: "x!1 = a!1"
          unfolding ab_def using  a_length
          by (metis append.simps(2) less_2_cases nth_Cons_0 nth_Cons_Suc pair_id)
        obtain b' where b'_def: "b = [b']"
          using ab_def cartesian_power_car_memE
          by (metis (no_types, opaque_lifting) append_Cons append_Nil append_eq_append_conv min_list.cases singleton_length)
        have b'_closed: "b' \<in> carrier Q\<^sub>p"
          using b'_def ab_def cartesian_power_car_memE
          by (metis Qp.R1_memE' list_hd)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>)"
          using  ab_def cartesian_power_append[of a Q\<^sub>p 2 b'] b'_def b'_closed
          unfolding b'_def ab_def(3) reverse_val_relation_set_def mem_Collect_eq
          by simp
        show "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>) \<and> val (x ! 0) \<le> val (x ! 1)"
          using x_closed ab_def unfolding reverse_val_relation_set_def mem_Collect_eq  0 1 by blast
      qed
    qed
    show ?thesis unfolding 0
      using cartesian_product_is_semialgebraic[of 2 reverse_val_relation_set 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
      by (simp add: carrier_is_semialgebraic reverse_val_relation_set_semialg)
  qed
  have 1: "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) \<le> val (as!2)}"
  proof-
    have 0: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) \<le> val (as!2)} = cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) (reverse_val_relation_set)"
    proof(rule equalityI')
      show "\<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) \<le> val (as ! 2)} \<Longrightarrow> x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set"
      proof-
       fix x assume A: " x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) \<le> val (as ! 2)}"
        then have 0: "length x = 3" unfolding mem_Collect_eq
          using cartesian_power_car_memE by blast
        obtain a where a_def: "a = [x!1, x!2]"
          by blast
        have a_length: "length a = 2"
        proof-
          have "a = x!1 #[x!2]"
            unfolding a_def
            by blast
          thus ?thesis using  length_Cons[of "x!1" "[x!2]"] unfolding singleton_length[of "x!2"]
            by presburger
        qed
        obtain b where b_def: "b = [x!0]"
          by blast
        have b_length: "length b = 1"
          unfolding b_def singleton_length by auto
        have a_closed: "a \<in> reverse_val_relation_set"
        proof-
          have 0: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
          proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
          qed
           have 1: "a \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
             using a_def  A drop_closed[of 1 3 x Q\<^sub>p] unfolding 0 mem_Collect_eq
              by (metis One_nat_def Suc_1 diff_Suc_1 numeral_3_eq_3 rel_simps(49) semiring_norm(77))
           show ?thesis using 1 A unfolding a_def reverse_val_relation_set_def A mem_Collect_eq
             by (metis Qp_2_car_memE list_tl nth_Cons_0)
        qed
        have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
          apply(rule cartesian_power_car_memI)
          unfolding b_length apply blast
          apply(rule subsetI)
          unfolding b_def using A unfolding mem_Collect_eq using cartesian_power_car_memE'[of x Q\<^sub>p "3::nat"  "0::nat"]
          by (metis b_def b_length in_set_conv_nth less_one Qp.to_R_to_R1 zero_less_numeral)
        have 2: "x = b@a"
          apply(rule nth_equalityI)
          using 0 unfolding a_length b_length  length_append[of b a] apply presburger
        proof- fix i assume A: "i < length x"
          then have A1: "i < 3"
            unfolding 0 by blast
          show "x ! i = (b @ a) ! i"
            apply(cases "i = 0")
             apply (metis append.simps(2) b_def nth_Cons_0)
            apply(cases "(i:: nat) = (1::nat)")
            using  append.simps a_def nth_Cons
             apply (metis b_length nth_append_length)
            apply(cases "(i:: nat) = (2::nat)")
            using A unfolding 0
            apply (metis a_def a_length arith_special(3) b_length list.inject nth_append_length_plus pair_id)
          proof-  assume A0: "i \<noteq>0" "i \<noteq> 1" "i \<noteq>2"
            then have "i \<ge> 3" by presburger
            then show "x ! i = (b @ a) ! i"
              using A unfolding 0 by presburger
          qed
        qed
        have 3: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
        proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
        qed
        show "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set"
          apply(rule cartesian_product_memI[of _ Q\<^sub>p 1 _ 2])
             apply (simp add: is_semialgebraic_closed reverse_val_relation_set_semialg)
          using reverse_val_relation_set_def apply blast
          using take_closed[of 1 3 x] A unfolding mem_Collect_eq apply auto[1]
          using a_closed unfolding 3 by blast
      qed
      show "\<And>x. x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set \<Longrightarrow> x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) \<le> val (as ! 2)}"
      proof fix x assume A: "x \<in>  cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set "
        then obtain a b where ab_def: "a \<in> reverse_val_relation_set" "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)" "x = b@a"
          using cartesian_product_memE'[of x  "carrier (Q\<^sub>p\<^bsup>1\<^esup>)" reverse_val_relation_set]
          by metis
        have a_length: "length a = 2"
          using ab_def unfolding reverse_val_relation_set_def
          using cartesian_power_car_memE by blast
        obtain b' where b'_def: "b = [b']"
          using ab_def cartesian_power_car_memE
          by (metis (no_types, opaque_lifting) append_Cons append_Nil append_eq_append_conv min_list.cases singleton_length)
        have b'_closed: "b' \<in> carrier Q\<^sub>p"
          using b'_def ab_def cartesian_power_car_memE
          by (metis Qp.R1_memE' list_hd)
        have b_length: "length b = 1"
          by (simp add: b'_def)
        have x_id: "x = b'#a"
          unfolding ab_def b'_def by auto
        have "(1::nat)< 2" by presburger
        hence  0: "x!1 = a!0"
          unfolding ab_def b'_def using a_length
          by (metis b'_def b_length nth_append_length pair_id)
        have 00: "2 = Suc 1"
          by auto
        have 1: "x!2 = a!1"
          using a_length nth_Cons[of b' a "2::nat"]
          unfolding x_id 00
          by (meson nth_Cons_Suc)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>)"
          unfolding x_id b'_def using b'_closed cartesian_power_cons[of a Q\<^sub>p 2 b'] ab_def
          unfolding reverse_val_relation_set_def mem_Collect_eq
          by simp

        show "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>) \<and> val (x ! 1) \<le> val (x ! 2)"
          using x_closed ab_def unfolding reverse_val_relation_set_def mem_Collect_eq  0 1 by blast
      qed
    qed
    show ?thesis unfolding 0
      using cartesian_product_is_semialgebraic[of 2 reverse_val_relation_set 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
      by (metis add_num_simps(2) car_times_semialg_is_semialg one_plus_numeral reverse_val_relation_set_semialg)
  qed
  have 2: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1) \<and> val (as!1) \<le> val (as!2)}=
          {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1)} \<inter> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) \<le> val (as!2)}"
    by blast
  show ?thesis using intersection_is_semialg 0 1 unfolding 2 by blast
qed

lemma triple_val_ineq_set_semialg':
  shows "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1) \<and> val (as!1) < val (as!2)}"
proof-
  have 0: "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1)}"
  proof-
    have 0: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1)} = cartesian_product (reverse_val_relation_set) (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
    proof(rule equalityI')
      show " \<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 0) \<le> val (as ! 1)} \<Longrightarrow> x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
      proof- fix x assume A: " x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 0) \<le> val (as ! 1)}"
        then have 0: "length x = 3" unfolding mem_Collect_eq
          using cartesian_power_car_memE by blast
        obtain a where a_def: "a = [x!0, x!1]"
          by blast
        have a_length: "length a = 2"
        proof-
          have "a = x!0 #[x!1]"
            unfolding a_def
            by blast
          thus ?thesis using  length_Cons[of "x!0" "[x!1]"] unfolding singleton_length[of "x!1"]
            by presburger
        qed
        obtain b where b_def: "b = [x!2]"
          by blast
        have b_length: "length b = 1"
          unfolding b_def singleton_length by auto
        have a_closed: "a \<in> reverse_val_relation_set"
        proof-
          have 0: "a = take 2 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_take[of 2 x]
             apply linarith
          proof- fix i::nat assume  a: "i < 2" show "a ! i = take 2 x ! i "
              apply(cases "i = 0")
               apply (metis a_def nth_Cons_0 nth_take zero_less_numeral)
              by (smt "0" \<open>length (take 2 x) = min (length x) 2\<close> a_def linorder_neqE_nat min.commute min.strict_order_iff nth_take numeral_eq_iff one_less_numeral_iff pair_id pos2 rel_simps(22) rel_simps(48) rel_simps(9) semiring_norm(81))
          qed
           have 1: "a \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
             using a_def 0  A unfolding mem_Collect_eq
             by (meson Qp_2I cartesian_power_car_memE' rel_simps(49) rel_simps(51) semiring_norm(77))
           show ?thesis using 1 A unfolding a_def reverse_val_relation_set_def A mem_Collect_eq
             by (metis Qp_2_car_memE list_tl nth_Cons_0)
        qed
        have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
          apply(rule cartesian_power_car_memI)
          unfolding b_length apply blast
          apply(rule subsetI)
          unfolding b_def using A unfolding mem_Collect_eq using cartesian_power_car_memE'[of x Q\<^sub>p "3::nat"  "2::nat"]
          by simp
        have 2: "x = a@b"
          apply(rule nth_equalityI)
          using 0 unfolding a_length b_length  length_append[of a b] apply presburger
        proof- fix i assume A: "i < length x"
          then have A1: "i < 3"
            unfolding 0 by blast
          show "x ! i = (a @ b) ! i"
            apply(cases "i = 0")
             apply (metis a_def append.simps(2) nth_Cons_0)
            apply(cases "(i:: nat) = 1")
             apply (simp add: a_def)
          proof- assume a: "i \<noteq>0" "i \<noteq> 1"
            then have "i = 2"
              using A1 by presburger
            thus ?thesis
              by (metis a_length b_def nth_append_length)
          qed
        qed
        have 3: "a = take 2 x"
          apply(rule nth_equalityI)
          unfolding a_length  0 length_take[of 2 x]
           apply linarith
          proof- fix i::nat assume  a: "i < 2" show "a ! i = take 2 x ! i "
              apply(cases "i = 0")
               apply (metis a_def nth_Cons_0 nth_take zero_less_numeral)
              by (smt "0" \<open>length (take 2 x) = min (length x) 2\<close> a_def linorder_neqE_nat min.commute min.strict_order_iff nth_take numeral_eq_iff one_less_numeral_iff pair_id pos2 rel_simps(22) rel_simps(48) rel_simps(9) semiring_norm(81))
          qed
        show " x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
          apply(rule cartesian_product_memI[of _ Q\<^sub>p 2 _ 1])
             apply (simp add: is_semialgebraic_closed reverse_val_relation_set_semialg)
            apply blast
          using 3  a_closed apply blast
        proof-
          have "drop 2 x = b"
            unfolding 2 unfolding 3 using 0
            by simp
          then show "drop 2 x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
            using b_closed by blast
        qed
      qed
      show "\<And>x. x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) \<Longrightarrow> x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 0) \<le> val (as ! 1)}"
      proof fix x assume A: "x \<in> cartesian_product reverse_val_relation_set (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
        then obtain a b where ab_def: "a \<in> reverse_val_relation_set" "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)" "x = a@b"
          using cartesian_product_memE'[of x reverse_val_relation_set "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
          by metis
        have a_length: "length a = 2"
          using ab_def unfolding reverse_val_relation_set_def
          using cartesian_power_car_memE by blast
        have "(0::nat)< 2" by presburger
        hence  0: "x!0 = a!0"
          unfolding ab_def using a_length
          by (metis append.simps(2) nth_Cons_0 pair_id)
        have "(1::nat)< 2" by presburger
        hence 1: "x!1 = a!1"
          unfolding ab_def using  a_length
          by (metis append.simps(2) less_2_cases nth_Cons_0 nth_Cons_Suc pair_id)
        obtain b' where b'_def: "b = [b']"
          using ab_def cartesian_power_car_memE
          by (metis (no_types, opaque_lifting) append_Cons append_Nil append_eq_append_conv min_list.cases singleton_length)
        have b'_closed: "b' \<in> carrier Q\<^sub>p"
          using b'_def ab_def cartesian_power_car_memE
          by (metis Qp.R1_memE' list_hd)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>)"
          using  ab_def cartesian_power_append[of a Q\<^sub>p 2 b'] b'_def b'_closed
          unfolding b'_def ab_def(3) reverse_val_relation_set_def mem_Collect_eq
          by simp
        show "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>) \<and> val (x ! 0) \<le> val (x ! 1)"
          using x_closed ab_def unfolding reverse_val_relation_set_def mem_Collect_eq  0 1 by blast
      qed
    qed
    show ?thesis unfolding 0
      using cartesian_product_is_semialgebraic[of 2 reverse_val_relation_set 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
      by (simp add: carrier_is_semialgebraic reverse_val_relation_set_semialg)
  qed
  have 1: "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) < val (as!2)}"
  proof-
    have 0: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) < val (as!2)} = cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) (strict_val_relation_set)"
    proof(rule equalityI')
      show "\<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) < val (as ! 2)} \<Longrightarrow> x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set"
      proof- fix x assume A: " x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) < val (as ! 2)}"
        then have 0: "length x = 3" unfolding mem_Collect_eq
          using cartesian_power_car_memE by blast
        obtain a where a_def: "a = [x!1, x!2]"
          by blast
        have a_length: "length a = 2"
        proof-
          have "a = x!1 #[x!2]"
            unfolding a_def
            by blast
          thus ?thesis using  length_Cons[of "x!1" "[x!2]"] unfolding singleton_length[of "x!2"]
            by presburger
        qed
        obtain b where b_def: "b = [x!0]"
          by blast
        have b_length: "length b = 1"
          unfolding b_def singleton_length by auto
        have a_closed: "a \<in> strict_val_relation_set"
        proof-
          have 0: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
          proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
          qed
           have 1: "a \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
             using a_def  A drop_closed[of 1 3 x Q\<^sub>p] unfolding 0 mem_Collect_eq
              by (metis One_nat_def Suc_1 diff_Suc_1 numeral_3_eq_3 rel_simps(49) semiring_norm(77))
           show ?thesis using 1 A unfolding a_def strict_val_relation_set_def A mem_Collect_eq
             by (metis Qp_2_car_memE list_tl nth_Cons_0)
        qed
        have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
          apply(rule cartesian_power_car_memI)
          unfolding b_length apply blast
          apply(rule subsetI)
          unfolding b_def using A unfolding mem_Collect_eq using cartesian_power_car_memE'[of x Q\<^sub>p "3::nat"  "0::nat"]
          by (metis b_def b_length in_set_conv_nth less_one Qp.to_R_to_R1 zero_less_numeral)
        have 2: "x = b@a"
          apply(rule nth_equalityI)
          using 0 unfolding a_length b_length  length_append[of b a] apply presburger
        proof- fix i assume A: "i < length x"
          then have A1: "i < 3"
            unfolding 0 by blast
          show "x ! i = (b @ a) ! i"
            apply(cases "i = 0")
             apply (metis append.simps(2) b_def nth_Cons_0)
            apply(cases "(i:: nat) = (1::nat)")
            using  append.simps a_def nth_Cons
             apply (metis b_length nth_append_length)
            apply(cases "(i:: nat) = (2::nat)")
            using A unfolding 0
            apply (metis a_def a_length arith_special(3) b_length list.inject nth_append_length_plus pair_id)
          proof-  assume A0: "i \<noteq>0" "i \<noteq> 1" "i \<noteq>2"
            then have "i \<ge> 3" by presburger
            then show "x ! i = (b @ a) ! i"
              using A unfolding 0 by presburger
          qed
        qed
        have 3: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
        proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
        qed
        show "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set"
          apply(rule cartesian_product_memI[of _ Q\<^sub>p 1 _ 2])
             apply (simp add: is_semialgebraic_closed strict_val_relation_set_is_semialg)
          using strict_val_relation_set_def apply blast
          using take_closed[of 1 3 x Q\<^sub>p] A unfolding mem_Collect_eq apply auto[1]
          using a_closed unfolding 3 by blast
      qed
      show "\<And>x. x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set \<Longrightarrow> x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) < val (as ! 2)}"
      proof fix x assume A: "x \<in>  cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set "
        then obtain a b where ab_def: "a \<in> strict_val_relation_set" "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)" "x = b@a"
          using cartesian_product_memE'[of x  "carrier (Q\<^sub>p\<^bsup>1\<^esup>)" strict_val_relation_set]
          by metis
        have a_length: "length a = 2"
          using ab_def unfolding strict_val_relation_set_def
          using cartesian_power_car_memE by blast
        obtain b' where b'_def: "b = [b']"
          using ab_def cartesian_power_car_memE
          by (metis (no_types, opaque_lifting) append_Cons append_Nil append_eq_append_conv min_list.cases singleton_length)
        have b'_closed: "b' \<in> carrier Q\<^sub>p"
          using b'_def ab_def
          by (metis Qp.R1_memE' list_hd)
        have b_length: "length b = 1"
          by (simp add: b'_def)
        have x_id: "x = b'#a"
          unfolding ab_def b'_def by auto
        have "(1::nat)< 2" by presburger
        hence  0: "x!1 = a!0"
          unfolding ab_def b'_def using a_length
          by (metis b'_def b_length nth_append_length pair_id)
        have 00: "2 = Suc 1"
          by auto
        have 1: "x!2 = a!1"
          using a_length nth_Cons[of b' a "2::nat"]
          unfolding x_id 00
          by (meson nth_Cons_Suc)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>)"
          unfolding x_id b'_def using b'_closed cartesian_power_cons[of a Q\<^sub>p 2 b'] ab_def
          unfolding strict_val_relation_set_def mem_Collect_eq
          by simp
        show "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>) \<and> val (x ! 1) < val (x ! 2)"
          using x_closed ab_def unfolding strict_val_relation_set_def mem_Collect_eq  0 1 by blast
      qed
    qed
    show ?thesis unfolding 0
      using cartesian_product_is_semialgebraic[of 2 reverse_val_relation_set 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
      by (metis add_num_simps(2) car_times_semialg_is_semialg one_plus_numeral strict_val_relation_set_is_semialg)
  qed
  have 2: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1) \<and> val (as!1) < val (as!2)}=
          {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!0) \<le> val (as!1)} \<inter> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) < val (as!2)}"
    by blast
  show ?thesis using intersection_is_semialg 0 1 unfolding 2 by blast
qed

lemma triple_val_ineq_set_semialg'':
  shows "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) < val (as!2)}"
proof-
    have 0: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) < val (as!2)} = cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) (strict_val_relation_set)"
    proof(rule equalityI')
      show "\<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) < val (as ! 2)} \<Longrightarrow> x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set"
      proof- fix x assume A: " x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) < val (as ! 2)}"
        then have 0: "length x = 3" unfolding mem_Collect_eq
          using cartesian_power_car_memE by blast
        obtain a where a_def: "a = [x!1, x!2]"
          by blast
        have a_length: "length a = 2"
        proof-
          have "a = x!1 #[x!2]"
            unfolding a_def
            by blast
          thus ?thesis using  length_Cons[of "x!1" "[x!2]"] unfolding singleton_length[of "x!2"]
            by presburger
        qed
        obtain b where b_def: "b = [x!0]"
          by blast
        have b_length: "length b = 1"
          unfolding b_def singleton_length by auto
        have a_closed: "a \<in> strict_val_relation_set"
        proof-
          have 0: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
          proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
          qed
           have 1: "a \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
             using a_def  A drop_closed[of 1 3 x Q\<^sub>p] unfolding 0 mem_Collect_eq
              by (metis One_nat_def Suc_1 diff_Suc_1 numeral_3_eq_3 rel_simps(49) semiring_norm(77))
           show ?thesis using 1 A unfolding a_def strict_val_relation_set_def A mem_Collect_eq
             by (metis Qp_2_car_memE list_tl nth_Cons_0)
        qed
        have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
          apply(rule cartesian_power_car_memI)
          unfolding b_length apply blast
          apply(rule subsetI)
          unfolding b_def using A unfolding mem_Collect_eq using cartesian_power_car_memE'[of x Q\<^sub>p "3::nat"  "0::nat"]
          by (metis b_def b_length in_set_conv_nth less_one Qp.to_R_to_R1 zero_less_numeral)
        have 2: "x = b@a"
          apply(rule nth_equalityI)
          using 0 unfolding a_length b_length  length_append[of b a] apply presburger
        proof- fix i assume A: "i < length x"
          then have A1: "i < 3"
            unfolding 0 by blast
          show "x ! i = (b @ a) ! i"
            apply(cases "i = 0")
             apply (metis append.simps(2) b_def nth_Cons_0)
            apply(cases "(i:: nat) = (1::nat)")
            using  append.simps a_def nth_Cons
             apply (metis b_length nth_append_length)
            apply(cases "(i:: nat) = (2::nat)")
            using A unfolding 0
            apply (metis a_def a_length arith_special(3) b_length list.inject nth_append_length_plus pair_id)
          proof-  assume A0: "i \<noteq>0" "i \<noteq> 1" "i \<noteq>2"
            then have "i \<ge> 3" by presburger
            then show "x ! i = (b @ a) ! i"
              using A unfolding 0 by presburger
          qed
        qed
        have 3: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
        proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
        qed
        show "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set"
          apply(rule cartesian_product_memI[of _ Q\<^sub>p 1 _ 2])
             apply (simp add: is_semialgebraic_closed strict_val_relation_set_is_semialg)
          using strict_val_relation_set_def apply blast
          using take_closed[of 1 3 x] A unfolding mem_Collect_eq
          using one_le_numeral apply blast
          using a_closed unfolding 3 by blast
      qed
      show "\<And>x. x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set \<Longrightarrow> x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) < val (as ! 2)}"
      proof fix x assume A: "x \<in>  cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) strict_val_relation_set "
        then obtain a b where ab_def: "a \<in> strict_val_relation_set" "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)" "x = b@a"
          using cartesian_product_memE'[of x  "carrier (Q\<^sub>p\<^bsup>1\<^esup>)" strict_val_relation_set]
          by metis
        have a_length: "length a = 2"
          using ab_def unfolding strict_val_relation_set_def
          using cartesian_power_car_memE by blast
        obtain b' where b'_def: "b = [b']"
          using ab_def cartesian_power_car_memE
          by (metis (no_types, opaque_lifting) append_Cons append_Nil append_eq_append_conv min_list.cases singleton_length)
        have b'_closed: "b' \<in> carrier Q\<^sub>p"
          using b'_def ab_def cartesian_power_car_memE
          by (metis Qp.R1_memE' list_hd)
        have b_length: "length b = 1"
          by (simp add: b'_def)
        have x_id: "x = b'#a"
          unfolding ab_def b'_def by auto
        have "(1::nat)< 2" by presburger
        hence  0: "x!1 = a!0"
          unfolding ab_def b'_def using a_length
          by (metis b'_def b_length nth_append_length pair_id)
        have 00: "2 = Suc 1"
          by auto
        have 1: "x!2 = a!1"
          using a_length nth_Cons[of b' a "2::nat"]
          unfolding x_id 00
          by (meson nth_Cons_Suc)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>)"
          unfolding x_id b'_def using b'_closed cartesian_power_cons[of a Q\<^sub>p 2 b'] ab_def
          unfolding strict_val_relation_set_def mem_Collect_eq
          by simp

        show "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>) \<and> val (x ! 1) < val (x ! 2)"
          using x_closed ab_def unfolding strict_val_relation_set_def mem_Collect_eq  0 1 by blast
      qed
    qed
    show ?thesis unfolding 0
      using cartesian_product_is_semialgebraic[of 2 reverse_val_relation_set 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
      by (metis add_num_simps(2) car_times_semialg_is_semialg one_plus_numeral strict_val_relation_set_is_semialg)
qed

lemma triple_val_ineq_set_semialg''':
  shows "is_semialgebraic 3 {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) \<le> val (as!2)}"
proof-
    have 0: "{as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as!1) \<le> val (as!2)} = cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) (reverse_val_relation_set)"
    proof(rule equalityI')
      show "\<And>x. x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) \<le> val (as ! 2)} \<Longrightarrow> x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set"
      proof- fix x assume A: " x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) \<le> val (as ! 2)}"
        then have 0: "length x = 3" unfolding mem_Collect_eq
          using cartesian_power_car_memE by blast
        obtain a where a_def: "a = [x!1, x!2]"
          by blast
        have a_length: "length a = 2"
        proof-
          have "a = x!1 #[x!2]"
            unfolding a_def
            by blast
          thus ?thesis using  length_Cons[of "x!1" "[x!2]"] unfolding singleton_length[of "x!2"]
            by presburger
        qed
        obtain b where b_def: "b = [x!0]"
          by blast
        have b_length: "length b = 1"
          unfolding b_def singleton_length by auto
        have a_closed: "a \<in> reverse_val_relation_set"
        proof-
          have 0: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
          proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
          qed
           have 1: "a \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
             using a_def  A drop_closed[of 1 3 x Q\<^sub>p] unfolding 0 mem_Collect_eq
              by (metis One_nat_def Suc_1 diff_Suc_1 numeral_3_eq_3 rel_simps(49) semiring_norm(77))
           show ?thesis using 1 A unfolding a_def reverse_val_relation_set_def A mem_Collect_eq
             by (metis Qp_2_car_memE list_tl nth_Cons_0)
        qed
        have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
          apply(rule cartesian_power_car_memI)
          unfolding b_length apply blast
          apply(rule subsetI)
          unfolding b_def using A unfolding mem_Collect_eq using cartesian_power_car_memE'[of x Q\<^sub>p "3::nat"  "0::nat"]
          by (metis b_def b_length in_set_conv_nth less_one Qp.to_R_to_R1 zero_less_numeral)
        have 2: "x = b@a"
          apply(rule nth_equalityI)
          using 0 unfolding a_length b_length  length_append[of b a] apply presburger
        proof- fix i assume A: "i < length x"
          then have A1: "i < 3"
            unfolding 0 by blast
          show "x ! i = (b @ a) ! i"
            apply(cases "i = 0")
             apply (metis append.simps(2) b_def nth_Cons_0)
            apply(cases "(i:: nat) = (1::nat)")
            using  append.simps a_def nth_Cons
            apply (metis b_length nth_append_length)
            apply(cases "(i:: nat) = (2::nat)")
            using A unfolding 0
            apply (metis a_def a_length arith_special(3) b_length list.inject nth_append_length_plus pair_id)
          proof-  assume A0: "i \<noteq>0" "i \<noteq> 1" "i \<noteq>2"
            then have "i \<ge> 3" by presburger
            then show "x ! i = (b @ a) ! i"
              using A unfolding 0 by presburger
          qed
        qed
        have 3: "a = drop 1 x"
            apply(rule nth_equalityI)
            unfolding a_length  0 length_drop[of 1 x]
             apply linarith
        proof- fix i::nat assume  a: "i < 2" show " a ! i = drop 1 x ! i"
              apply(cases "i = 0")
              unfolding a_def using nth_drop[of 1 x i]
              apply (metis (no_types, opaque_lifting) "0" a_def arith_extra_simps(6) diff_is_0_eq' eq_imp_le eq_numeral_extra(1) flip_def flip_eval(1) less_numeral_extra(1) less_one less_or_eq_imp_le nat_add_left_cancel_le nat_le_linear nat_less_le nth_Cons_0 nth_drop numeral_neq_zero trans_less_add2 zero_less_diff)
              apply(cases "i = 1")
              using nth_drop[of 1 x i] unfolding 0
              apply (metis "0" a_def a_length list.simps(1) nat_1_add_1 nth_drop one_le_numeral pair_id semiring_norm(3))
              using a by presburger
        qed
        show "x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set"
          apply(rule cartesian_product_memI[of _ Q\<^sub>p 1 _ 2])
             apply (simp add: is_semialgebraic_closed reverse_val_relation_set_semialg)
          using reverse_val_relation_set_def apply blast
          using take_closed[of 1 3 x] A unfolding mem_Collect_eq  apply auto[1]
          using a_closed unfolding 3 by blast
      qed
      show "\<And>x. x \<in> cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set \<Longrightarrow> x \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>). val (as ! 1) \<le> val (as ! 2)}"
      proof fix x assume A: "x \<in>  cartesian_product (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) reverse_val_relation_set "
        then obtain a b where ab_def: "a \<in> reverse_val_relation_set" "b \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)" "x = b@a"
          using cartesian_product_memE'[of x  "carrier (Q\<^sub>p\<^bsup>1\<^esup>)" reverse_val_relation_set]
          by metis
        have a_length: "length a = 2"
          using ab_def unfolding reverse_val_relation_set_def
          using cartesian_power_car_memE by blast
        obtain b' where b'_def: "b = [b']"
          using ab_def cartesian_power_car_memE
          by (metis (no_types, opaque_lifting) append_Cons append_Nil append_eq_append_conv min_list.cases singleton_length)
        have b'_closed: "b' \<in> carrier Q\<^sub>p"
          using b'_def ab_def cartesian_power_car_memE
          by (metis Qp.R1_memE' list_hd)
        have b_length: "length b = 1"
          by (simp add: b'_def)
        have x_id: "x = b'#a"
          unfolding ab_def b'_def by auto
        have "(1::nat)< 2" by presburger
        hence  0: "x!1 = a!0"
          unfolding ab_def b'_def using a_length
          by (metis b'_def b_length nth_append_length pair_id)
        have 00: "2 = Suc 1"
          by auto
        have 1: "x!2 = a!1"
          using a_length nth_Cons[of b' a "2::nat"]
          unfolding x_id 00
          by (meson nth_Cons_Suc)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>)"
          unfolding x_id b'_def using b'_closed cartesian_power_cons[of a Q\<^sub>p 2 b'] ab_def
          unfolding reverse_val_relation_set_def mem_Collect_eq
          by simp

        show "x \<in> carrier (Q\<^sub>p\<^bsup>3\<^esup>) \<and> val (x ! 1) \<le> val (x ! 2)"
          using x_closed ab_def unfolding reverse_val_relation_set_def mem_Collect_eq  0 1 by blast
      qed
    qed
    show ?thesis unfolding 0
      using cartesian_product_is_semialgebraic[of 2 reverse_val_relation_set 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]
      by (metis add_num_simps(2) car_times_semialg_is_semialg one_plus_numeral reverse_val_relation_set_semialg)
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Semialgebraic Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  The most natural way to define a semialgebraic function $f: \mathbb{Q}_p^n \to \mathbb{Q}_p$ is a
  function whose graph is a semialgebraic subset of $\mathbb{Q}_p^{n+1}$. However, the definition
  given here is slightly different, and devised by Denef in \<^cite>\<open>"denef1986"\<close> in order to prove
  Macintyre's theorem. As Denef notes, we can use Macintyre's theorem to deduce that the given
  definition perfectly aligns with the intuitive one.
\<close>

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Defining Semialgebraic Functions\<close>
      (********************************************************************************************)
      (********************************************************************************************)


text\<open>Apply a function f to the tuple consisting of the first n indices, leaving the remaining indices
unchanged\<close>

definition partial_image where
"partial_image m f xs = (f (take m xs))#(drop m xs)"

definition partial_pullback where
"partial_pullback m f l S = (partial_image m f)  \<inverse>\<^bsub>m+l\<^esub> S "

lemma partial_pullback_memE:
  assumes "as \<in> partial_pullback m f l S"
  shows "as \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)" "partial_image m f as \<in> S"
  using assms apply (metis evimage_eq partial_pullback_def)
  using assms unfolding partial_pullback_def
  by blast

lemma partial_pullback_closed:
"partial_pullback m f l S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  using partial_pullback_memE(1) by blast

lemma partial_pullback_memI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
  assumes "(f (take m as))#(drop m as) \<in> S"
  shows "as \<in> partial_pullback m f k S"
  using assms unfolding partial_pullback_def partial_image_def evimage_def
  by blast

lemma partial_image_eq:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  assumes "x = as @ bs"
  shows "partial_image n f x = (f as)#bs"
proof-
  have 0: "(take n x) = as"
    by (metis append_eq_conv_conj assms(1) assms(3) cartesian_power_car_memE)
  have 1: "drop n x = bs"
    by (metis "0" append_take_drop_id assms(3) same_append_eq)
  show ?thesis using 0 1 unfolding partial_image_def
    by blast
qed

lemma partial_pullback_memE':
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  assumes "x = as @ bs"
  assumes "x \<in> partial_pullback n f k S"
  shows "(f as)#bs \<in> S"
  using partial_pullback_memE[of x n f k S] partial_image_def[of n f x]
  by (metis assms(1) assms(2) assms(3) assms(4) partial_image_eq)

text\<open>Partial pullbacks have the same algebraic properties as pullbacks\<close>

lemma partial_pullback_intersect:
"partial_pullback m f l (S1 \<inter> S2) = (partial_pullback m f l S1) \<inter> (partial_pullback m f l S2)"
  unfolding partial_pullback_def
  by simp

lemma partial_pullback_union:
"partial_pullback m f l (S1 \<union> S2) = (partial_pullback m f l S1) \<union> (partial_pullback m f l S2)"
  unfolding partial_pullback_def
  by simp

lemma cartesian_power_drop:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
  shows "drop n x \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
  apply(rule cartesian_power_car_memI)
  using assms cartesian_power_car_memE
   apply (metis add_diff_cancel_left' length_drop)
  using assms cartesian_power_car_memE''
  by (metis order.trans set_drop_subset)

lemma partial_pullback_complement:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>) - S) = carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) - (partial_pullback m f l S) "
  apply(rule equalityI)
  using partial_pullback_def[of m f l "(carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>) - S)"]
        partial_pullback_def[of m f l S]
   apply (smt Diff_iff evimage_Diff partial_pullback_memE(1) subsetI)
proof fix x assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) - partial_pullback m f l S"
  show " x \<in> partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>) - S) "
    apply(rule partial_pullback_memI)
    using A
     apply blast
  proof
    have 00: "Suc l = l + 1"
      by auto
    have 0: "drop m x \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
      by (meson A DiffD1 cartesian_power_drop)
    have 1: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A by (meson DiffD1 le_add1 take_closed)
    have "f (take m x) # drop m x \<in> carrier (Q\<^sub>p\<^bsup>l+1\<^esup>) "
      using assms 0 1 00 cartesian_power_cons[of "drop m x" Q\<^sub>p l "f (take m x)"]
      by blast
    thus "f (take m x) # drop m x \<in> carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>) "
      using 00 by metis
    show "f (take m x) # drop m x \<notin> S"
      using A unfolding partial_pullback_def partial_image_def
      by blast
  qed
qed

lemma partial_pullback_carrier:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>)) = carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  apply(rule equalityI)
  using partial_pullback_memE(1) apply blast
proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  show "x \<in> partial_pullback m f l (carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>))"
    apply(rule partial_pullback_memI)
  using A cartesian_power_drop[of x m l] assms
   apply blast
proof-
  have "f (take m x) \<in> carrier Q\<^sub>p"
    using A  assms take_closed[of m "m+l" x Q\<^sub>p]
    by (meson Pi_mem le_add1)
  then show "f (take m x) # drop m x \<in> carrier (Q\<^sub>p\<^bsup>Suc l\<^esup>)"
    using cartesian_power_drop[of x m l]
    by (metis A add.commute cartesian_power_cons plus_1_eq_Suc)
qed
qed

text\<open>Definition 1.4 from Denef\<close>

definition is_semialg_function where
"is_semialg_function m f = ((f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p)  \<and>
                          (\<forall>l \<ge> 0. \<forall>S \<in> semialg_sets (1 + l). is_semialgebraic (m + l) (partial_pullback m f l S)))"

lemma is_semialg_function_closed:
  assumes "is_semialg_function m f"
  shows "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  using is_semialg_function_def assms by blast

lemma is_semialg_functionE:
  assumes "is_semialg_function m f"
  assumes "is_semialgebraic (1 + k) S"
  shows " is_semialgebraic (m + k) (partial_pullback m f k S)"
  using is_semialg_function_def assms
  by (meson is_semialgebraicE le0)

lemma is_semialg_functionI:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "\<And>k  S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m f k S)"
  shows "is_semialg_function m f"
  using assms unfolding is_semialg_function_def
  by blast

text\<open>Semialgebraicity for functions can be verified on basic semialgebraic sets \<close>

lemma is_semialg_functionI':
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "\<And>k  S. S \<in> basic_semialgs (1 + k) \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m f k S)"
  shows "is_semialg_function m f"
  apply(rule is_semialg_functionI)
  using assms(1) apply blast
proof-
  show "\<And>k S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m f k S)"
  proof- fix k S assume A: "S \<in> semialg_sets (1 + k)"
    show "is_semialgebraic (m + k) (partial_pullback m f k S)"
      apply(rule gen_boolean_algebra.induct[of S "carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)" "basic_semialgs (1 + k)"])
        using A unfolding semialg_sets_def
          apply blast
        using partial_pullback_carrier assms carrier_is_semialgebraic plus_1_eq_Suc apply presburger
        apply (metis assms(1) assms(2) carrier_is_semialgebraic intersection_is_semialg partial_pullback_carrier partial_pullback_intersect plus_1_eq_Suc)
        using partial_pullback_union union_is_semialgebraic apply presburger
        using assms(1) complement_is_semialg partial_pullback_complement plus_1_eq_Suc by presburger
  qed
qed

text\<open>Graphs of semialgebraic functions are semialgebraic\<close>
abbreviation graph where
"graph \<equiv> fun_graph Q\<^sub>p"

lemma graph_memE:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "x \<in> graph m f"
  shows "f (take m x) = x!m"
        "x = (take m x)@[f (take m x)]"
        "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
proof-
  obtain a where a_def:  "a\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> x = a @ [f a]"
    using assms
    unfolding fun_graph_def
    by blast
  then have 0: "a = take m x"
    by (metis append_eq_conv_conj cartesian_power_car_memE)
  then show "f (take m x) = x!m"
    by (metis a_def cartesian_power_car_memE nth_append_length)
  show "x = (take m x)@[f (take m x)]"
    using "0" a_def
    by blast
  show "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using "0" a_def by blast
qed

lemma graph_memI:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "f (take m x) = x!m"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m+1\<^esup>)"
  shows "x \<in> graph m f"
proof-
  have 0: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    apply(rule take_closed[of _ "m + 1"])
     apply simp
       using assms(3) by blast
  have "x = (take m x)@[x!m]"
  by (metis \<open>take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)\<close> add.commute
      assms(3) cartesian_power_car_memE length_append_singleton lessI
      nth_equalityI nth_take plus_1_eq_Suc take_Suc_conv_app_nth)
  then have "x = (take m x)@[f (take m x)]"
    using assms(2)
    by presburger
  then show ?thesis
    using assms 0
    unfolding fun_graph_def
    by blast
qed

lemma graph_mem_closed:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "x \<in> graph m f"
  shows "x \<in> carrier (Q\<^sub>p\<^bsup>m+1\<^esup>)"
proof(rule cartesian_power_car_memI')
  show "length x = m + 1"
    using assms graph_memE[of f m x]
    by (smt Groups.add_ac(2) cartesian_power_car_memE fun_graph_def length_append_singleton mem_Collect_eq plus_1_eq_Suc)
  show "\<And>i. i < m + 1 \<Longrightarrow> x ! i \<in> carrier Q\<^sub>p"
  proof- fix i assume A: "i < m + 1"
    then show "x ! i \<in> carrier Q\<^sub>p"
    proof(cases "i = m")
      case True
      then show ?thesis using graph_memE[of f m x]
        by (metis PiE assms(1) assms(2))
    next
      case False
      then show ?thesis using graph_memE[of f m x]
        by (metis \<open>i < m + 1\<close> add.commute assms(1) assms(2) cartesian_power_car_memE' less_SucE nth_take plus_1_eq_Suc)
    qed
  qed
qed

lemma graph_closed:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "graph m f \<subseteq> carrier (Q\<^sub>p\<^bsup>m+1\<^esup>)"
  using assms graph_mem_closed
  by blast

text\<open>The \<open>m\<close>-dimensional diagonal set is semialgebraic\<close>

notation diagonal ("\<Delta> ")

lemma diag_is_algebraic:
  shows "is_algebraic Q\<^sub>p (n + n) (\<Delta> n)"
  using Qp.cring_axioms diagonal_is_algebraic
  by blast

lemma diag_is_semialgebraic:
  shows "is_semialgebraic (n + n) (\<Delta> n)"
  using diag_is_algebraic is_algebraic_imp_is_semialg
  by blast

text\<open>Transposition permutations\<close>

definition transpose where
"transpose i j = (Fun.swap i j id)"

lemma transpose_permutes:
  assumes "i< n"
  assumes "j < n"
  shows "transpose i j permutes {..<n}"
  unfolding permutes_def transpose_def
proof
  show "\<forall>x. x \<notin> {..<n} \<longrightarrow> Fun.swap i j id x = x"
    using assms by (auto simp: Transposition.transpose_def)
  show "\<forall>y. \<exists>!x. Fun.swap i j id x = y"
  proof  fix y show "\<exists>!x. Fun.swap i j id x = y"
      using swap_id_eq[of i j y]
  by (metis eq_id_iff swap_apply(1) swap_apply(2) swap_id_eq swap_self)
qed
qed

lemma transpose_alt_def:
"transpose a b x = (if x = a then b else if x = b then a else x)"
  using swap_id_eq
  by (simp add: transpose_def)

definition last_to_first where
"last_to_first n = (\<lambda>i. if i = (n-1) then 0 else if i < n-1 then i + 1 else i)"

definition first_to_last where
"first_to_last n = fun_inv (last_to_first n)"

lemma last_to_first_permutes:
  assumes "(n::nat) > 0"
  shows "last_to_first n permutes {..<n}"
  unfolding permutes_def
proof
  show "\<forall>x. x \<notin> {..<n} \<longrightarrow> last_to_first n x = x"
  proof fix x show " x \<notin> {..<n} \<longrightarrow> last_to_first n x = x"
    proof assume A: "x \<notin> {..<n}" then have "\<not> x < n"
        by blast then have "x \<ge> n" by linarith
      then show  "last_to_first n x = x"
        unfolding last_to_first_def using assms
        by auto
    qed
  qed
  show "\<forall>y. \<exists>!x. last_to_first n x = y"
  proof fix y
    show "\<exists>!x. last_to_first n x = y"
    proof(cases "y = 0")
      case True
      then have 0: "last_to_first n (n-1) = y"
        using last_to_first_def
        by (simp add: last_to_first_def)
      have 1: "\<And>x. last_to_first n x = y \<Longrightarrow> x = n-1"
        unfolding last_to_first_def using True
        by (metis add_gr_0 less_numeral_extra(1) not_gr_zero)
      show ?thesis
        using 0 1
        by blast
    next
      case False
      then show ?thesis
      proof(cases "y < n")
        case True
        then have 0: "last_to_first n (y-1) = y"
          using False True
          unfolding last_to_first_def
          using add.commute by auto
        have 1: "\<And>x. last_to_first n x = y \<Longrightarrow> x =(y-1)"
          unfolding last_to_first_def
          using True False
          by auto
        show ?thesis using 0 1 by blast
      next
        case F: False
        then have 0: "y \<ge> n"
          using not_less by blast
        then have 1: "last_to_first n y = y"
          by (simp add: \<open>\<forall>x. x \<notin> {..<n} \<longrightarrow> last_to_first n x = x\<close>)
        have 2: "\<And>x. last_to_first n x = y \<Longrightarrow> x =y"
          using 0 unfolding last_to_first_def
          using False by presburger
        then show ?thesis using 1 2 by blast
      qed
    qed
  qed
qed

definition graph_swap where
"graph_swap n f = permute_list ((first_to_last (n+1))) ` (graph n f)"

lemma last_to_first_eq:
  assumes "length as = n"
  shows "permute_list (last_to_first (n+1)) (a#as)  = (as@[a])"
proof-
  have 0: "\<And>i. i < (n+1) \<Longrightarrow> permute_list (last_to_first (n + 1)) (a # as) ! i = (as@[a]) ! i"
  proof-
    fix i assume A: "i < n+1"
    show "permute_list (last_to_first (n + 1)) (a # as) ! i = (as @ [a]) ! i"
    proof(cases "i = n")
      case True
      have 0: "(as @ [a]) ! i = a"
        by (metis True assms nth_append_length)
      have 1: "length (a#as) = n + 1"
        by (simp add: assms)
      have 2: "i < length (a # as)"
        using "1" A by linarith
      have 3: "last_to_first (n + 1) permutes {..<length (a # as)}"
        by (metis "1" add_gr_0 last_to_first_permutes less_numeral_extra(1))
      have 4: "permute_list (last_to_first (n + 1)) (a # as) ! i = (a # as) ! last_to_first (n + 1) i"
        using  2 3  permute_list_nth[of "last_to_first (n + 1)" "a#as" i]
        by blast
      have 5: "permute_list (last_to_first (n + 1)) (a # as) ! i = (a # as) ! 0"
        using 4 unfolding last_to_first_def
        by (simp add: True)
      have 6: "permute_list (last_to_first (n + 1)) (a # as) ! i = a"
        using 5
        by simp
      then show ?thesis using 0   by auto
    next
      case False
      then show ?thesis
        by (smt A add.commute add.right_neutral add_diff_cancel_right' add_gr_0
            add_less_cancel_left append.simps(1) append.simps(2) assms last_to_first_def
            last_to_first_permutes less_SucE less_numeral_extra(1) list.size(3) list.size(4)
            nth_append permute_list_nth plus_1_eq_Suc)
    qed
  qed
  have 1: "length (a#as) = n + 1"
    by (simp add: assms)
  have 2: "length (permute_list (last_to_first (n+1)) (a#as)) = n + 1"
    by (metis "1" length_permute_list)
  have 3: "length (as@[a]) = n + 1"
    by (simp add: assms)
  then show ?thesis using 0 2
    by (metis nth_equalityI)
qed

lemma first_to_last_eq:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "permute_list (first_to_last (n+1)) (as@[a])  = (a#as)"
proof-
  have "length as = n"
    using assms(1) cartesian_power_car_memE by blast
  then show ?thesis
  using last_to_first_eq last_to_first_permutes[of n]
        permute_list_compose_inv(2)[of  "(last_to_first (n + 1))" n "a # as"]
  unfolding first_to_last_def
  by (metis add_gr_0 assms(1) assms(2) cartesian_power_append last_to_first_permutes
      less_one permute_list_closed' permute_list_compose_inv(2))
qed

lemma graph_swapI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "(f as)#as \<in> graph_swap n f"
proof-
  have 0: "as@[f as] \<in> graph n f"
    using assms using graph_memI[of f n] fun_graph_def
    by blast
  have 1: "f as \<in> carrier Q\<^sub>p"
    using assms
    by blast
  then show ?thesis
  using assms 0 first_to_last_eq[of as "n" "f as"]
  unfolding graph_swap_def
  by (metis image_eqI)
qed

lemma graph_swapE:
  assumes "x \<in> graph_swap n f"
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "hd x = f (tl x)"
proof-
  obtain y where y_def: "y \<in> graph n f \<and> x = permute_list (first_to_last (n+1)) y"
    using assms graph_swap_def
    by (smt image_def mem_Collect_eq)
  then have "take n y \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms(2) graph_memE(3)
    by blast
  then show "hd x = f (tl x)"
    by (metis (no_types, lifting) add.commute assms(2) cartesian_power_car_memE'
        first_to_last_eq graph_memE(1) graph_memE(2) graph_mem_closed lessI list.sel(1)
        list.sel(3) plus_1_eq_Suc y_def)
qed

text\<open>Semialgebraic functions have semialgebraic graphs\<close>

lemma graph_as_partial_pullback:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "partial_pullback n f 1 (\<Delta> 1) = graph n f"
proof
  show "partial_pullback n f 1 (\<Delta> 1) \<subseteq> graph n f"
  proof fix x assume A: "x \<in> partial_pullback n f 1 (\<Delta> 1)"
    then have 0: "f (take n x) # drop n x \<in> \<Delta>  1"
      by (metis local.partial_image_def partial_pullback_memE(2))
    then have 1: "length (f (take n x) # drop n x)  = 2"
      using diagonal_def
      by (metis (no_types, lifting) cartesian_power_car_memE mem_Collect_eq one_add_one)
    then obtain b where b_def: "[b] = drop n x"
      by (metis list.inject pair_id)
    then have "[f (take n x), b] \<in> \<Delta>  1"
      using "0"
      by presburger
    then have "b = f (take n x)"
      using 0
      by (smt One_nat_def Qp.cring_axioms diagonal_def drop0 drop_Suc_Cons list.inject mem_Collect_eq take_Suc_Cons)
    then have "x = (take n x)@[f (take n x)]"
      by (metis append_take_drop_id b_def)
    then show "x \<in> graph n f" using graph_memI[of f n x]
      by (metis (no_types, lifting) A \<open>b = f (take n x)\<close>
          assms b_def nth_via_drop partial_pullback_memE(1))
  qed
  show "graph n f \<subseteq> partial_pullback n f 1 (\<Delta>  1)"
  proof fix x
    assume A: "x \<in> graph n f "
    then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n+1\<^esup>)"
      using assms graph_mem_closed by blast
    have "x = (take n x) @ [f (take n x)]"
      using A graph_memE(2)[of f n x] assms
      by blast
    then have "partial_image n f x =  [f (take n x), f (take n x)]"
      by (metis append_take_drop_id local.partial_image_def same_append_eq)
    then have "partial_image n f x \<in> \<Delta> 1"
      using assms 0 diagonal_def[of 1] Qp.cring_axioms diagonalI[of  "partial_image n f x"]
       by (metis (no_types, lifting) A append_Cons append_eq_conv_conj
           cartesian_power_car_memE cartesian_power_car_memE' graph_memE(1)
           less_add_one self_append_conv2 Qp.to_R1_closed)
    then show "x \<in> partial_pullback n f 1 (\<Delta>  1)"
      unfolding partial_pullback_def using 0
      by blast
  qed
qed

lemma semialg_graph:
  assumes "is_semialg_function n f"
  shows "is_semialgebraic (n + 1) (graph n f)"
  using assms graph_as_partial_pullback[of f n] unfolding is_semialg_function_def
  by (metis diag_is_semialgebraic is_semialgebraicE less_imp_le_nat less_numeral_extra(1))

text\<open>Functions induced by polynomials are semialgebraic\<close>

definition var_list_segment where
"var_list_segment i j = map (\<lambda>i. pvar Q\<^sub>p i) [i..< j]"

lemma var_list_segment_length:
  assumes "i \<le> j"
  shows "length (var_list_segment i j) = j - i"
  using assms var_list_segment_def
  by fastforce

lemma var_list_segment_entry:
  assumes "k < j - i"
  assumes "i \<le> j"
  shows "var_list_segment i j ! k = pvar Q\<^sub>p (i + k)"
  using assms var_list_segment_length
  unfolding var_list_segment_def
  using nth_map_upt by blast

lemma var_list_segment_is_poly_tuple:
  assumes "i \<le>j"
  assumes "j \<le> n"
  shows "is_poly_tuple n (var_list_segment i j)"
  apply(rule Qp_is_poly_tupleI)
  using assms var_list_segment_entry var_list_segment_length  Qp.cring_axioms pvar_closed[of  _ n]
  by (metis (no_types, opaque_lifting)  add.commute add_lessD1 diff_add_inverse le_Suc_ex
      less_diff_conv)

lemma map_by_var_list_segment:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "j \<le> n"
  assumes "i \<le> j"
  shows "poly_map n (var_list_segment i j) as = list_segment i j as"
  apply(rule nth_equalityI )
  unfolding poly_map_def var_list_segment_def  list_segment_def restrict_def poly_tuple_eval_def
  apply (metis (full_types) assms(1) length_map)
  using assms  eval_pvar[of  _ n as] Qp.cring_axioms length_map add.commute
        length_upt less_diff_conv less_imp_add_positive nth_map nth_upt
        trans_less_add2
  by (smt le_add_diff_inverse2)

lemma map_by_var_list_segment_to_length:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "i \<le> n"
  shows "poly_map n (var_list_segment i n) as = drop i as"
  apply(rule nth_equalityI )
  apply (metis Qp_poly_mapE' assms(1) assms(2) cartesian_power_car_memE length_drop var_list_segment_length)
  using assms map_by_var_list_segment[of as n n i] list_segment_drop[of i as]  cartesian_power_car_memE[of as Q\<^sub>p n]
        map_nth[of ] nth_drop nth_map[of _ "[i..<n]" "(pvar Q\<^sub>p)" ] nth_map[of _ "map (pvar Q\<^sub>p) [i..<n]" "eval_at_point Q\<^sub>p as"]
  unfolding poly_map_def poly_tuple_eval_def var_list_segment_def restrict_def list_segment_def
  by (smt add.commute add_eq_self_zero drop_map drop_upt le_Suc_ex le_refl)

lemma map_tail_by_var_list_segment:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "i < n"
  shows "poly_map (n+1) (var_list_segment 1 (n+1)) (a#as) = as"
proof-
  have 0: "(a#as) \<in> carrier (Q\<^sub>p\<^bsup>n+1\<^esup>)"
    using assms
    by (meson cartesian_power_cons)
  have 1: "length as = n"
    using assms cartesian_power_car_memE
    by blast
  have 2: "drop 1 (a # as) = as"
    using 0 1 using list_segment_drop[of 1 "a#as"]
    by (metis One_nat_def drop0 drop_Suc_Cons )
  have "1 \<le>n + 1" by auto
  then show ?thesis
    using 0 2  map_by_var_list_segment_to_length[of "a#as" "n+1" 1]
  by presburger
qed

lemma Qp_poly_tuple_Cons:
  assumes "is_poly_tuple n fs"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>k\<^esub>])"
  assumes "k \<le>n"
  shows "is_poly_tuple n (f#fs)"
  using is_poly_tuple_Cons[of n fs f] poly_ring_car_mono[of  k n] assms
  by blast

lemma poly_map_Cons:
  assumes "is_poly_tuple n fs"
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "poly_map n (f#fs) a = (Qp_ev f a)#poly_map n fs a"
  using assms poly_map_cons by blast

lemma poly_map_append':
  assumes "is_poly_tuple n fs"
  assumes "is_poly_tuple n gs"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "poly_map n (fs@gs) a = poly_map n fs a @ poly_map n gs a"
  using assms(3) poly_map_append by blast

lemma partial_pullback_by_poly:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
  shows "partial_pullback n (Qp_ev f) k S = poly_tuple_pullback (n+k) S (f# (var_list_segment n (n+k)))"
proof
  show "partial_pullback n (Qp_ev f) k S \<subseteq> poly_tuple_pullback (n+k) S (f # var_list_segment n (n + k))"
  proof fix x assume A: " x \<in> partial_pullback n (Qp_ev f) k S"
    then obtain as bs where as_bs_def: "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<and> bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> x = as @ bs"
      using  partial_pullback_memE(1)[of x n "(Qp_ev f)" k S] cartesian_power_decomp
      by metis
    then have 0: "(Qp_ev f as#bs) \<in> S"
      using A partial_pullback_memE'
      by blast
    have 1: "Qp_ev f as = Qp_ev f (as@bs)"
      using assms as_bs_def poly_eval_cartesian_prod[of as n bs k f]
        Qp.cring_axioms [of ]
      by metis
    then have 2: "((Qp_ev f x) #bs) \<in> S"
      using "0" as_bs_def
      by presburger
    have 3: "bs = list_segment n (n+k) x"
      using as_bs_def list_segment_drop[of n x]
      by (metis (no_types, lifting) add_cancel_right_right add_diff_cancel_left'
          append_eq_append_conv append_take_drop_id cartesian_power_car_memE
          length_0_conv length_append length_map length_upt linorder_neqE_nat
          list_segment_def not_add_less1)
    have 4: "is_poly_tuple (n+k) (f # var_list_segment n (n + k))"
      using Qp_poly_tuple_Cons
        var_list_segment_is_poly_tuple
      by (metis add.commute assms(1) dual_order.refl le_add2)
    have 5: "f \<in> carrier (Q\<^sub>p [\<X>\<^bsub>n + k\<^esub>])"
      using poly_ring_car_mono[of n "n + k"] assms le_add1 by blast
    have 6: "is_poly_tuple (n + k) (var_list_segment n (n + k))"
      by (simp add: var_list_segment_is_poly_tuple)
    have 7: "x \<in> carrier (Q\<^sub>p\<^bsup>n + k\<^esup>)"
      using as_bs_def cartesian_power_concat(1) by blast
    hence 8: "poly_map (n+k) (f # var_list_segment n (n + k)) x = (Qp_ev f x)#poly_map (n+k) (var_list_segment n (n + k)) x"
      using 5 6 7 A poly_map_Cons[of "n + k" "var_list_segment n (n + k)" f x] 4
      unfolding partial_pullback_def evimage_def
      by blast
    hence 6: "poly_map (n+k) (f # var_list_segment n (n + k)) x = (Qp_ev f x)#bs"
      using 3 "7" le_add1 le_refl map_by_var_list_segment by presburger
    show " x \<in> poly_tuple_pullback (n+k) S (f # var_list_segment n (n + k))"
      unfolding poly_tuple_pullback_def using 6
      by (metis "2" "7" IntI poly_map_apply vimage_eq)
  qed
  show "poly_tuple_pullback (n + k) S (f # var_list_segment n (n + k)) \<subseteq> partial_pullback n (Qp_ev f) k S"
  proof fix x
    assume A: "x \<in> poly_tuple_pullback (n + k) S (f # var_list_segment n (n + k))"
    have 0: "is_poly_tuple (n+k) (f # var_list_segment n (n + k))"
      using Qp_poly_tuple_Cons assms(1) le_add1 var_list_segment_is_poly_tuple
      by blast
    have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
      using A unfolding poly_tuple_pullback_def
      by blast
    have 2: "poly_map (n+k) (f # var_list_segment n (n + k)) x \<in> S"
      using 1 assms A unfolding poly_map_def poly_tuple_pullback_def restrict_def
      by (metis (no_types, opaque_lifting) Int_commute add.commute evimage_def evimage_eq)
    have 3: "poly_map (n+k) (f # var_list_segment n (n + k)) x = (Qp_ev f x)#(drop n x)"
      using poly_map_Cons[of "n + k" "var_list_segment n (n + k)" f x] 1 assms(1) map_by_var_list_segment_to_length
            le_add1 poly_map_cons by presburger
    have 4: "poly_map (n+k) (f # var_list_segment n (n + k)) x = (Qp_ev f (take n x))#(drop n x)"
      using assms 1 3 eval_at_points_higher_pow[of  f n "n + k" "x"] le_add1
      by (metis  nat_le_iff_add)
    show "x \<in> partial_pullback n (Qp_ev f) k S"
      apply(rule partial_pullback_memI)
      using 1 apply blast
      using 2 3 4 by metis
  qed
qed

lemma poly_is_semialg:
  assumes "f \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
  shows "is_semialg_function n (Qp_ev f)"
proof(rule is_semialg_functionI)
  show "Qp_ev f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using assms
    by (meson Pi_I eval_at_point_closed)
  show "\<And>k S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (n + k) (partial_pullback n (Qp_ev f) k S)"
  proof- fix k::nat fix S
    assume A: "S \<in> semialg_sets (1 + k)"
    have 0: "is_poly_tuple (n + k) (f # var_list_segment n (n + k))"
      by (metis add.commute assms  le_add2 order_refl Qp_poly_tuple_Cons
          var_list_segment_is_poly_tuple)
    have 1: "length (f # var_list_segment n (n + k)) = k + 1"
      by (metis add.commute add_diff_cancel_left' le_add1 length_Cons
          plus_1_eq_Suc var_list_segment_length)
    have 2: "partial_pullback n (Qp_ev f) k S = poly_tuple_pullback (n + k) S (f # var_list_segment n (n + k))"
      using A assms partial_pullback_by_poly[of f n S k]
      unfolding semialg_sets_def
      using gen_boolean_algebra_subset
      by blast
    then show "is_semialgebraic (n + k) (partial_pullback n (Qp_ev f) k S)"
      using  add.commute[of 1 k] 0 1 assms(1)
            pullback_is_semialg[of "n+k" "(f # var_list_segment n (n + k))" "k+1" S]
      by (metis A is_semialgebraicI is_semialgebraic_closed poly_tuple_pullback_eq_poly_map_vimage)
  qed
qed

text\<open>Families of polynomials defined by semialgebraic coefficient functions\<close>

lemma semialg_function_on_carrier:
  assumes "is_semialg_function n f"
  assumes "restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict g (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  shows "is_semialg_function n g"
proof(rule is_semialg_functionI)
  have 0: "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using assms(1) is_semialg_function_closed
    by blast
  show "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)" then show " g x \<in> carrier Q\<^sub>p"
      using assms(2) 0
      by (metis (no_types, lifting) PiE restrict_Pi_cancel)
  qed
  show "\<And>k S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (n + k) (partial_pullback n g k S)"
  proof- fix k S
    assume A: "S \<in> semialg_sets (1 + k)"
    have 1: "is_semialgebraic (n + k) (partial_pullback n f k S)"
      using A assms(1) is_semialg_functionE is_semialgebraicI
      by blast
    have 2: "(partial_pullback n f k S) = (partial_pullback n g k S)"
      unfolding partial_pullback_def partial_image_def evimage_def
    proof
      show "(\<lambda>xs. f (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>) \<subseteq> (\<lambda>xs. g (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
      proof fix x assume "x \<in> (\<lambda>xs. f (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>) "
        have "(take n x) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
          using assms
          by (meson \<open>x \<in> (\<lambda>xs. f (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)\<close>
              inf_le2 le_add1 subset_iff take_closed)
        then have "f (take n x) = g (take n x)"
          using assms unfolding  restrict_def
          by meson
        then show " x \<in> (\<lambda>xs. g (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
          using assms \<open>x \<in> (\<lambda>xs. f (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)\<close>
          by blast
      qed
      show "(\<lambda>xs. g (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>) \<subseteq> (\<lambda>xs. f (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
      proof fix x assume A: "x \<in> (\<lambda>xs. g (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
        have "(take n x) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
          using assms
          by (meson A  inf_le2 le_add1 subset_iff take_closed)
        then have "f (take n x) = g (take n x)"
          using assms unfolding  restrict_def
          by meson
        then show "x \<in> (\<lambda>xs. f (take n xs) # drop n xs) -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+k\<^esup>)"
          using A by blast
      qed
    qed
    then show "is_semialgebraic (n + k) (partial_pullback n g k S)"
      using 1 by auto
  qed
qed

lemma semialg_function_on_carrier':
  assumes "is_semialg_function n f"
  assumes "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> f a = g a"
  shows "is_semialg_function n g"
  using assms semialg_function_on_carrier unfolding restrict_def
  by (meson restrict_ext semialg_function_on_carrier)

lemma constant_function_is_semialg:
  assumes "n > 0"
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "\<And> a. a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> f a = x"
  shows "is_semialg_function n f"
proof(rule semialg_function_on_carrier[of _ "Qp_ev (Qp_to_IP x)"])
  show "is_semialg_function n (Qp_ev (Qp_to_IP x))"
    using assms poly_is_semialg[of "(Qp_to_IP x)"] Qp_to_IP_car
    by blast
  have 0: "\<And> a. a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> f a = Qp_ev (Qp_to_IP x) a"
    using eval_at_point_const assms
    by blast
  then show "restrict (Qp_ev (Qp_to_IP x)) (carrier (Q\<^sub>p\<^bsup>n\<^esup>)) = restrict f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
    by (metis (no_types, lifting) restrict_ext)
qed

lemma cartesian_product_singleton_factor_projection_is_semialg:
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "b \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "is_semialgebraic (m+n) (cartesian_product A {b})"
  shows "is_semialgebraic m A"
proof-
  obtain f where f_def: "f = map (pvar Q\<^sub>p) [0..<m]"
    by blast
  have 0: "is_poly_tuple m f"
    using assms var_list_segment_is_poly_tuple[of 0 m m]
    unfolding var_list_segment_def f_def by blast
  have 4: "length f = m"
    unfolding f_def using length_map[of "pvar Q\<^sub>p" "[0..<m]"] by auto
  obtain g where g_def: "(g::(nat multiset \<Rightarrow> ((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set) list) = map (\<lambda>i::nat. Qp.indexed_const (b ! i)) [(0::nat)..<n]"
    by blast
  have 1: "is_poly_tuple m g"
  proof-
    have 0: "set [0::nat..< n] = {..<n}"
      using atLeast_upt by blast
    then have "\<And>i. i \<in> set [0::nat..< n] \<Longrightarrow> b!i \<in> carrier Q\<^sub>p"
      using assms(2) cartesian_power_car_memE'[of b Q\<^sub>p n]  by blast
    hence 1: "\<And>i. i \<in> set [0::nat..< n] \<Longrightarrow> Qp.indexed_const (b ! i) \<in> carrier (Q\<^sub>p[\<X>\<^bsub>m\<^esub>])"
      using assms Qp_to_IP_car by blast
    show ?thesis
      unfolding is_poly_tuple_def g_def
      apply(rule subsetI)
       using set_map[of "\<lambda>i. Qp.indexed_const (b ! i)" "[0..<n]"]  1 unfolding 0
       by (smt image_iff)
  qed
  have 2: "is_poly_tuple m (f@g)"
    using 0 1 Qp_is_poly_tuple_append assms(3) by blast
  have 3: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> poly_tuple_eval (f@g) x = x@b"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    have 30: "poly_tuple_eval f x = x"
    proof-
      have 300: "length (poly_tuple_eval f x) = length x"
        unfolding poly_tuple_eval_def using cartesian_power_car_memE
        by (metis "4" A length_map)
      have "\<And>i. i < length x \<Longrightarrow> poly_tuple_eval f x ! i = x ! i"
        unfolding f_def poly_tuple_eval_def using nth_map
        by (metis "4" A add_cancel_right_left cartesian_power_car_memE eval_pvar f_def length_map nth_upt)
      thus ?thesis using 300
        by (metis nth_equalityI)
    qed
    have 31: "poly_tuple_eval g x = b"
    proof-
      have 310: "length (poly_tuple_eval g x) = length b"
        unfolding poly_tuple_eval_def g_def  using cartesian_power_car_memE
        by (metis assms(2) length_map map_nth)
      have 311: "length b = n" using assms cartesian_power_car_memE by blast
      hence "\<And>i. i < n \<Longrightarrow> poly_tuple_eval g x ! i = b ! i" proof- fix i assume "i < n"
        thus "poly_tuple_eval g x ! i = b ! i"
          unfolding g_def poly_tuple_eval_def  using eval_at_point_const[of "b!i" x m] 310 nth_map
          by (metis "311" A assms(2) cartesian_power_car_memE' length_map map_nth)
      qed
      thus ?thesis using 311 310 nth_equalityI
        by (metis list_eq_iff_nth_eq)
    qed
    have 32: "poly_tuple_eval (f @ g) x = poly_map  m (f@g) x"
      unfolding poly_map_def restrict_def using A
      by (simp add: A)
    have 33: "poly_tuple_eval f x = poly_map  m f x"
      unfolding poly_map_def restrict_def using A
      by (simp add: A)
    have 34: "poly_tuple_eval g x = poly_map  m g x"
      unfolding poly_map_def restrict_def using A
      by (simp add: A)
    show "poly_tuple_eval (f @ g) x = x @ b"
      using assms 1 2 30 31  poly_map_append[of x m f g] A unfolding 32 33 34
      by (simp add: A \<open>b \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)\<close>)
  qed
  have 4: "A = (poly_tuple_eval (f@g)  \<inverse>\<^bsub>m\<^esub> (cartesian_product A {b}))"
  proof
    show "A \<subseteq> poly_tuple_eval (f @ g) \<inverse>\<^bsub>m\<^esub> cartesian_product A {b}"
    proof(rule subsetI) fix x assume A: "x \<in> A"
      then have 0: "poly_tuple_eval (f@g) x = x@b"
        using 3 assms by blast
      then show " x \<in> poly_tuple_eval (f @ g) \<inverse>\<^bsub>m\<^esub> cartesian_product A {b}"
        using A cartesian_product_memE
        by (smt Un_upper1 assms(1) assms(2) cartesian_product_memI' evimageI2 in_mono insert_is_Un mk_disjoint_insert singletonI)
    qed
    show "poly_tuple_eval (f @ g) \<inverse>\<^bsub>m\<^esub> cartesian_product A {b} \<subseteq> A"
    proof(rule subsetI) fix x assume A: "x \<in> (poly_tuple_eval (f @ g) \<inverse>\<^bsub>m\<^esub> cartesian_product A {b})"
      then have "poly_tuple_eval (f @ g) x \<in> cartesian_product A {b}"
        by blast
      then have "x@b \<in> cartesian_product A {b}"
        using A 3 by (metis evimage_eq)
      then show "x \<in> A"
        using A
        by (metis append_same_eq cartesian_product_memE' singletonD)
    qed
  qed
  have 5: "A = poly_map m (f@g)  \<inverse>\<^bsub>m\<^esub> (cartesian_product A {b})"
  proof
    show "A \<subseteq> poly_map m (f @ g) \<inverse>\<^bsub>m\<^esub> cartesian_product A {b}"
      unfolding poly_map_def evimage_def restrict_def using 4
      by (smt IntI assms(1) evimageD in_mono subsetI vimageI)
    show "poly_map m (f @ g) \<inverse>\<^bsub>m\<^esub> cartesian_product A {b} \<subseteq> A"
      unfolding poly_map_def evimage_def restrict_def using 4
      by (smt Int_iff evimageI2 subsetI vimage_eq)
  qed
  have 6: "length (f @ g) = m + n"
    unfolding f_def g_def by (metis index_list_length length_append length_map map_nth)
  show ?thesis using 2 5 6 assms pullback_is_semialg[of m "f@g" "m+n" "cartesian_product A {b}"]
    by (metis is_semialgebraicE zero_eq_add_iff_both_eq_0)
qed

lemma cartesian_product_factor_projection_is_semialg:
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "B \<noteq> {}"
  assumes "is_semialgebraic (m+n) (cartesian_product A B)"
  shows "is_semialgebraic m A"
proof-
  obtain b where b_def: "b \<in> B"
    using assms by blast
  have "is_semialgebraic n {b}"
    using assms b_def is_algebraic_imp_is_semialg singleton_is_algebraic by blast
  hence 0: "is_semialgebraic (m+n) (cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) {b})"
    using car_times_semialg_is_semialg assms(4)  by blast
  have "(cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) {b}) \<inter> (cartesian_product A B)
          = (cartesian_product A {b})"
    using assms b_def cartesian_product_intersection[of "carrier (Q\<^sub>p\<^bsup>m\<^esup>)" Q\<^sub>p m "{b}" n A B]
    by (metis (no_types, lifting) Int_absorb1 Int_empty_left Int_insert_left_if1 \<open>is_semialgebraic n {b}\<close> is_semialgebraic_closed set_eq_subset)
  hence "is_semialgebraic (m+n) (cartesian_product A {b})"
    using assms 0  intersection_is_semialg by metis
  thus ?thesis using assms cartesian_product_singleton_factor_projection_is_semialg
    by (meson \<open>is_semialgebraic n {b}\<close> insert_subset is_semialgebraic_closed)
qed

lemma partial_pullback_cartesian_product:
  assumes "\<xi> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
  shows "cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) = partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))) "
proof
  show "cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) \<subseteq> partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
  proof fix x assume A: "x \<in> cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
    then obtain y t where yt_def: "x = y@[t] \<and> y \<in> partial_pullback m \<xi> 0 S \<and> t \<in> carrier Q\<^sub>p"
      by (metis cartesian_product_memE' Qp.to_R1_to_R Qp.to_R_pow_closed)
    then have "[\<xi> y] \<in> S"
      using partial_pullback_memE unfolding partial_image_def
      by (metis (no_types, lifting) add.right_neutral append.right_neutral cartesian_power_drop le_zero_eq take_closed partial_pullback_memE' take_eq_Nil)
    then have 0: "[\<xi> y]@[t] \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
      using cartesian_product_memI' yt_def
      by (metis assms(2) carrier_is_semialgebraic is_semialgebraic_closed Qp.to_R1_closed)
    have 1: " x \<in> carrier (Q\<^sub>p\<^bsup>m + 1\<^esup>)"
      using A yt_def
      by (metis add.right_neutral cartesian_power_append partial_pullback_memE(1))
    show "x \<in> partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
      apply(rule partial_pullback_memI)
      using "1" apply blast
      using yt_def 0
      by (smt Cons_eq_appendI add.right_neutral local.partial_image_def partial_image_eq partial_pullback_memE(1) self_append_conv2 Qp.to_R1_closed)
  qed
  show "partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))) \<subseteq> cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
  proof(rule subsetI) fix x assume A: "x \<in> partial_pullback m \<xi> 1 (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
    then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>m + 1\<^esup>)"
      using assms partial_pullback_memE[of x m \<xi> 1 "cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"]
      by blast
    have 1: "\<xi> (take m x) # drop m x \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
      using A assms partial_pullback_memE[of x m \<xi> 1 "cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"]
      unfolding partial_image_def
      by blast
    have 2: "\<xi> (take m (take m x)) # drop m (take m x)  = [\<xi> (take m x)]"
      using 0 1
      by (metis add.commute add.right_neutral append.right_neutral append_take_drop_id take0 take_drop)
    show "x \<in> cartesian_product (partial_pullback m \<xi> 0 S) (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
      apply(rule cartesian_product_memI[of _  Q\<^sub>p m _ 1])
         apply (metis add_cancel_right_right partial_pullback_closed)
        apply blast
        apply(rule partial_pullback_memI[of _ m 0 \<xi> S]) using 0
       apply (metis Nat.add_0_right le_iff_add take_closed)
      using 2 apply (metis (no_types, lifting) "1" add.commute add.right_neutral assms(2) cartesian_product_memE(1) list.inject plus_1_eq_Suc take_Suc_Cons take_drop)
    using 0  cartesian_power_drop by blast
  qed
qed

lemma cartesian_product_swap:
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "is_semialgebraic (m+n) (cartesian_product A B)"
  shows "is_semialgebraic (m+n) (cartesian_product B A)"
proof-
  obtain f where f_def: "f = (\<lambda>i. (if i < m then n + i else (if i < m+n then i - m else i)))"
    by blast
  have 0: "\<And>i. i \<in> {..<m} \<longrightarrow> f i \<in> {n..<m+n}"
    unfolding f_def by simp
  have 1: "\<And>i. i \<in> {m..<m+n} \<longrightarrow> f i \<in> {..<n}"
    unfolding f_def by (simp add: less_diff_conv2)
  have 2: "\<And>i. i \<notin> {..<m + n} \<longrightarrow> f i \<notin> {..<m + n}"
    unfolding f_def by simp
  have f_permutes: "f permutes {..<m+n}"
    unfolding permutes_def
  proof
    show "\<forall>x. x \<notin> {..<m + n} \<longrightarrow> f x = x"
      unfolding f_def by simp
    show "\<forall>y. \<exists>!x. f x = y"
    proof fix y
      show "\<exists>!x. f x = y"
      proof(cases "y < n")
        case True
        have T0: "f (y+m) = y"
          unfolding f_def using True
          by simp
        have "\<And>i. f i = y \<Longrightarrow> i \<in> {m..<m+n}"
          using 0 1 2 True f_def nat_neq_iff by fastforce
        hence "\<And>i. f i = y \<Longrightarrow> i = y+m"
          using T0 unfolding f_def by auto
        thus ?thesis using T0 by blast
      next
        case False
        show ?thesis
        proof(cases  "y \<in> {n..<m+n}")
          case True
          have T0: "f (y-n) = y"
            using True unfolding f_def by auto
          have "\<And>i. f i = y \<Longrightarrow> i \<in> {..<m}"
            using 0 1 2 True f_def
            by (metis False atLeastLessThan_iff diff_add_inverse2 diff_diff_cancel diff_le_self
                lessThan_iff less_imp_diff_less linordered_semidom_class.add_diff_inverse nat_neq_iff not_add_less1)
          hence "\<And>i. f i = y \<Longrightarrow> i = y- n"
            using f_def by force
          then show ?thesis using T0 by blast
        next
          case F: False
          then show ?thesis using 0 1 2 unfolding f_def
            using False add_diff_inverse_nat lessThan_iff by auto
        qed
      qed
    qed
  qed
  have "permute_list f ` (cartesian_product A B) = (cartesian_product B A)"
  proof
    show "permute_list f ` cartesian_product A B \<subseteq> cartesian_product B A"
    proof fix x assume A: " x \<in> permute_list f ` cartesian_product A B"
      then obtain a b where ab_def: "a \<in> A \<and>b \<in> B \<and> x = permute_list f (a@b)"
        by (metis (mono_tags, lifting) cartesian_product_memE' image_iff)
      have 0: "x = permute_list f (a@b)"
        using ab_def by blast
      have 1: "length a = n"
        using ab_def assms cartesian_power_car_memE[of a Q\<^sub>p n] by blast
      have 2: "length b = m"
        using ab_def assms cartesian_power_car_memE[of b Q\<^sub>p m] by blast
      have 3: "length x = m + n"
        using 1 2 0 f_permutes by simp
      have 4: "\<And>i. i < m \<Longrightarrow> x ! i = (a@b) ! (f i)"
        unfolding 0 using permute_list_nth
        by (metis "0" "3" f_permutes length_permute_list trans_less_add1)
      hence 5: "\<And>i. i < m \<Longrightarrow> x ! i = b!i"
        unfolding f_def using 1 2
        by (metis "4" f_def nth_append_length_plus)
      have 6: "\<And>i. i \<in> {m..<m+n} \<Longrightarrow> x ! i = (a@b) ! (i - m)"
        unfolding 0 using f_def permute_list_nth  f_permutes
        by (metis (no_types, lifting) "0" "3" atLeastLessThan_iff length_permute_list not_add_less2
            ordered_cancel_comm_monoid_diff_class.diff_add)
      have 7: "x = b@a"
      proof(rule nth_equalityI)
        show "length x = length (b @ a)"
          using 1 2 3 by simp
        show "\<And>i. i < length x \<Longrightarrow> x ! i = (b @ a) ! i"
          unfolding 3 using 1 2 4 5
          by (smt "0" add.commute add_diff_inverse_nat f_def f_permutes length_append nat_add_left_cancel_less nth_append permute_list_nth)
      qed
      show "x \<in> cartesian_product B A" unfolding 7 using ab_def unfolding cartesian_product_def by blast
    qed
    show "cartesian_product B A \<subseteq> permute_list f ` cartesian_product A B"
    proof fix y assume A: "y \<in> cartesian_product B A"
      then obtain b a where ab_def: "b \<in> B \<and> a \<in> A \<and> y = b@a"
        using cartesian_product_memE' by blast
      obtain x where 0: "x = permute_list f (a@b)"
        by blast
      have 1: "length a = n"
        using ab_def assms cartesian_power_car_memE[of a Q\<^sub>p n] by blast
      have 2: "length b = m"
        using ab_def assms cartesian_power_car_memE[of b Q\<^sub>p m] by blast
      have 3: "length x = m + n"
        using 1 2 0 f_permutes by simp
      have 4: "\<And>i. i < m \<Longrightarrow> x ! i = (a@b) ! (f i)"
        unfolding 0 using permute_list_nth
        by (metis "0" "3" f_permutes length_permute_list trans_less_add1)
      hence 5: "\<And>i. i < m \<Longrightarrow> x ! i = b!i"
        unfolding f_def using 1 2
        by (metis "4" f_def nth_append_length_plus)
      have 6: "\<And>i. i \<in> {m..<m+n} \<Longrightarrow> x ! i = (a@b) ! (i - m)"
        unfolding 0 using f_def permute_list_nth  f_permutes
        by (metis (no_types, lifting) "0" "3" atLeastLessThan_iff length_permute_list not_add_less2
            ordered_cancel_comm_monoid_diff_class.diff_add)
      have 7: "x = b@a"
      proof(rule nth_equalityI)
        show "length x = length (b @ a)"
          using 1 2 3 by simp
        show "\<And>i. i < length x \<Longrightarrow> x ! i = (b @ a) ! i"
          unfolding 3 using 1 2 4 5
          by (smt "0" add.commute add_diff_inverse_nat f_def f_permutes length_append nat_add_left_cancel_less nth_append permute_list_nth)
      qed
      show "y \<in> permute_list f ` cartesian_product A B"
        using ab_def 7 cartesian_product_memI'[of _ Q\<^sub>p] unfolding 0
        by (metis assms(1) assms(2) image_eqI)
    qed
  qed
  thus ?thesis using assms f_permutes permutation_is_semialgebraic
    by metis
qed

lemma Qp_zero_subset_is_semialg:
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>0\<^esup>)"
  shows "is_semialgebraic 0 S"
proof(cases "S = {}")
  case True
  then show ?thesis
    by (simp add: empty_is_semialgebraic)
next
  case False
  then have "S = carrier (Q\<^sub>p\<^bsup>0\<^esup>)"
    using assms unfolding Qp_zero_carrier  by blast
  then show ?thesis
    by (simp add: carrier_is_semialgebraic)
qed

lemma cartesian_product_empty_list:
"cartesian_product A {[]} = A"
"cartesian_product {[]} A = A"
proof
  show "cartesian_product A {[]} \<subseteq> A"
    apply(rule subsetI)
    unfolding cartesian_product_def
    by (smt append_Nil2 empty_iff insert_iff mem_Collect_eq)
  show "A \<subseteq> cartesian_product A {[]}"
    apply(rule subsetI)
    unfolding cartesian_product_def
    by (smt append_Nil2 empty_iff insert_iff mem_Collect_eq)
  show "cartesian_product {[]} A = A"
  proof
    show "cartesian_product {[]} A \<subseteq> A"
    apply(rule subsetI)
    unfolding cartesian_product_def
    by (smt append_self_conv2 bex_empty insert_compr mem_Collect_eq)
  show "A \<subseteq> cartesian_product {[]} A"
    apply(rule subsetI)
    unfolding cartesian_product_def
    by blast
  qed
qed

lemma cartesian_product_singleton_factor_projection_is_semialg':
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "b \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "is_semialgebraic (m+n) (cartesian_product A {b})"
  shows "is_semialgebraic m A"
proof(cases "n > 0")
  case True
  show ?thesis
  proof(cases "m > 0")
    case T: True
    then show ?thesis
      using assms True cartesian_product_singleton_factor_projection_is_semialg by blast
  next
    case False
    then show ?thesis using Qp_zero_subset_is_semialg assms by blast
  qed
next
  case False
  then have F0: "b = []"
    using assms Qp_zero_carrier by blast
  have "cartesian_product A {b} = A"
    unfolding F0
    by (simp add: cartesian_product_empty_list(1))
  then show ?thesis using assms False
    by (metis add.right_neutral gr0I)
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>More on graphs of functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


text\<open>This section lays the groundwork for showing that semialgebraic functions are closed under
     various algebraic operations\<close>

text\<open>The take and drop functions on lists are polynomial maps\<close>

lemma function_restriction:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> S"
  assumes "n \<le> k"
  shows "(g \<circ> (take n)) \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<rightarrow> S"
proof fix x
  assume "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  then have "take n x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms(2) take_closed
    by blast
  then show "(g \<circ> take n) x \<in> S"
    using assms comp_apply
    by (metis Pi_iff comp_def)
qed

lemma partial_pullback_restriction:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "n < k"
  shows "partial_pullback k (g \<circ> take n) m S =
         split_cartesian_product  (n + m) (k - n) n (partial_pullback n g m S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>))"
proof(rule equalityI)
  show "partial_pullback k (g \<circ> take n) m S \<subseteq> split_cartesian_product (n + m) (k - n) n (partial_pullback n g m S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>))"
  proof fix x assume A: "x \<in> partial_pullback k (g \<circ> take n) m S"
    obtain as bs where asbs_def: "x = as@bs \<and> as \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<and> bs \<in> carrier  (Q\<^sub>p\<^bsup>m\<^esup>)"
      using partial_pullback_memE[of x k "g \<circ> take n" m S] A cartesian_power_decomp[of x Q\<^sub>p k m]
      by metis
    have 0: "((g \<circ> (take n)) as)#bs \<in> S"
      using asbs_def partial_pullback_memE'[of as k bs m x] A
      by blast
    have 1: "(g (take n as))#bs \<in> S"
      using 0
      by (metis comp_apply)
    have 2: "take n as @ bs \<in> carrier (Q\<^sub>p\<^bsup>n+m\<^esup>)"
      by (meson asbs_def assms(2) cartesian_power_concat(1) less_imp_le_nat take_closed)
    have 3: "(take n as)@bs \<in> (partial_pullback n g m S)"
      using 1 2 partial_pullback_memI[of "(take n as)@bs" n m g S]
      by (metis (mono_tags, opaque_lifting) asbs_def assms(2) local.partial_image_def nat_less_le
          partial_image_eq subsetD  subset_refl take_closed)
    have 4: "drop n as \<in> (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>))"
      using asbs_def assms(2) drop_closed
      by blast
    show " x \<in> split_cartesian_product (n + m) (k - n) n (partial_pullback n g m S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>))"
      using split_cartesian_product_memI[of "take n as" bs
                                        "partial_pullback n g m S" "drop n as"
                                         "carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)" Q\<^sub>p "n + m" "k - n" n ]  4
      by (metis (no_types, lifting) "3" append.assoc append_take_drop_id
          asbs_def assms(2) cartesian_power_car_memE less_imp_le_nat partial_pullback_memE(1)
          subsetI take_closed)
  qed
  show "split_cartesian_product (n + m) (k - n) n (partial_pullback n g m S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)) \<subseteq> partial_pullback k (g \<circ> take n) m S"
  proof fix x assume A: "x \<in> split_cartesian_product (n + m) (k - n) n (partial_pullback n g m S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>))"
    show "x \<in> partial_pullback k (g \<circ> take n) m S"
    proof(rule partial_pullback_memI)
      have 0: "(partial_pullback n g m S) \<subseteq> carrier (Q\<^sub>p\<^bsup>n+m\<^esup>)"
        using partial_pullback_closed by blast
      then  have "split_cartesian_product (n + m) (k - n) n (partial_pullback n g m S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)) \<subseteq> carrier (Q\<^sub>p\<^bsup>n + m + (k - n)\<^esup>)"
        using assms A  split_cartesian_product_closed[of "partial_pullback n g m S" Q\<^sub>p "n + m"
                                                "carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)" "k - n" n]
        using le_add1 by blast
      then show P: "x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>)"
        by (smt A Nat.add_diff_assoc2 add.commute add_diff_cancel_left' assms(2) le_add1 less_imp_le_nat subsetD)
      have "take n x @ drop (n + (k - n)) x \<in> partial_pullback n g m S"
        using 0 A split_cartesian_product_memE[of x "n + m" "k - n" n "partial_pullback n g m S" "carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)" Q\<^sub>p]
             le_add1 by blast
      have 1: "g (take n x) # drop k x \<in> S"
        using  partial_pullback_memE
        by (metis (no_types, lifting) \<open>take n x @ drop (n + (k - n)) x \<in> partial_pullback n g m S\<close>
              \<open>x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>)\<close> add.assoc assms(2) cartesian_power_drop le_add1
              le_add_diff_inverse less_imp_le_nat partial_pullback_memE' take_closed)
      have 2: "g (take n x) = (g \<circ> take n) (take k x)"
        using assms P comp_apply[of g "take n" "take k x"]
        by (metis add.commute append_same_eq append_take_drop_id less_imp_add_positive take_add take_drop)
      then show "(g \<circ> take n) (take k x) # drop k x \<in> S"
        using "1" by presburger
    qed
  qed
qed

lemma comp_take_is_semialg:
  assumes "is_semialg_function n g"
  assumes "n < k"
  assumes "0 < n"
  shows "is_semialg_function k (g \<circ> (take n))"
proof(rule is_semialg_functionI)
  show "g \<circ> take n \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using assms function_restriction[of g n "carrier Q\<^sub>p" k]  dual_order.strict_implies_order
        is_semialg_function_closed
    by blast
  show "\<And>ka S. S \<in> semialg_sets (1 + ka) \<Longrightarrow> is_semialgebraic (k + ka) (partial_pullback k (g \<circ> take n) ka S)"
  proof- fix l S assume A: "S \<in> semialg_sets (1 + l)"
    have 0: "is_semialgebraic (n + l) (partial_pullback n g l S) "
      using assms A is_semialg_functionE is_semialgebraicI
      by blast
    have "is_semialgebraic (n + l + (k - n)) (split_cartesian_product (n + l) (k - n) n (partial_pullback n g l S) (carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)))"
      using A 0 split_cartesian_product_is_semialgebraic[of _ _
                                                  "partial_pullback n g l S" _ "carrier (Q\<^sub>p\<^bsup>k - n\<^esup>)"]
            add_gr_0 assms(2) assms(3) carrier_is_semialgebraic le_add1 zero_less_diff
      by presburger
    then  show "is_semialgebraic (k + l) (partial_pullback k (g \<circ> take n) l S)"
      using partial_pullback_restriction[of g n k l S]
  by (metis (no_types, lifting) add.assoc add.commute assms(1) assms(2) is_semialg_function_closed le_add_diff_inverse less_imp_le_nat)
  qed
qed

text\<open>Restriction of a graph to a semialgebraic domain\<close>

lemma graph_formula:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "graph n g = {as \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>). g (take n as) = as!n}"
  using assms graph_memI fun_graph_def[of Q\<^sub>p n g]
  by (smt Collect_cong Suc_eq_plus1 graph_memE(1) graph_mem_closed mem_Collect_eq)

definition restricted_graph where
"restricted_graph n g S = {as \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>). take n as \<in> S \<and> g (take n as) = as!n }"

lemma restricted_graph_closed:
 "restricted_graph n g S \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  by (metis (no_types, lifting) mem_Collect_eq restricted_graph_def subsetI)

lemma restricted_graph_memE:
  assumes "a \<in> restricted_graph n g S"
  shows "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)" "take n a \<in> S" "g (take n a) = a!n"
  using assms
  using restricted_graph_closed apply blast
  apply (metis (no_types, lifting) assms mem_Collect_eq restricted_graph_def)
  using assms unfolding restricted_graph_def
  by blast

lemma restricted_graph_mem_formula:
  assumes "a \<in> restricted_graph n g S"
  shows "a = (take n a)@[g (take n a)]"
proof-
  have "length a = Suc n"
    using assms
    by (metis (no_types, lifting) cartesian_power_car_memE mem_Collect_eq restricted_graph_def)
  then have "a = (take n a)@[a!n]"
    by (metis append_eq_append_conv_if hd_drop_conv_nth lessI take_hd_drop)
  then show ?thesis
    by (metis assms restricted_graph_memE(3))
qed

lemma restricted_graph_memI:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "take n a \<in> S"
  assumes "g (take n a) = a!n"
  shows "a \<in> restricted_graph n g S"
  using assms restricted_graph_def
  by blast

lemma restricted_graph_memI':
  assumes "a \<in> S"
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "(a@[g a]) \<in> restricted_graph n g S"
proof-
  have "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms(1) assms(3) by blast
  then have "g a \<in> carrier Q\<^sub>p"
    using assms by blast
  then have 0: "a @ [g a] \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    using assms
    by (metis (no_types, lifting) add.commute cartesian_power_append plus_1_eq_Suc subsetD)
  have 1: "take n (a @ [g a]) \<in> S"
    using assms
    by (metis (no_types, lifting) append_eq_conv_conj cartesian_power_car_memE subsetD)
  show ?thesis
    using assms restricted_graph_memI[of "a@[g a]" n S g]
    by (metis "0" \<open>a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)\<close> append_eq_conv_conj cartesian_power_car_memE nth_append_length)
qed

lemma restricted_graph_subset:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "restricted_graph n g S \<subseteq> graph n g"
proof fix x  assume A: "x \<in> restricted_graph n g S"
  show "x \<in> graph n g"
    apply(rule graph_memI)
  using assms(1) apply blast
  using A restricted_graph_memE(3) apply blast
  by (metis A add.commute plus_1_eq_Suc restricted_graph_memE(1))
qed

lemma restricted_graph_subset':
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "restricted_graph n g S \<subseteq> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
proof fix a assume A: "a \<in> restricted_graph n g S"
  then have "a = (take n a)@[g (take n a)]"
    using restricted_graph_mem_formula by blast
  then show "a \<in> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
    using cartesian_product_memI' A unfolding restricted_graph_def
    by (metis (mono_tags, lifting) assms(2) last_closed' mem_Collect_eq subsetI Qp.to_R1_closed)
qed

lemma restricted_graph_intersection:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "restricted_graph n g S = graph n g \<inter> (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
proof
  show "restricted_graph n g S \<subseteq> graph n g \<inter> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
    using assms restricted_graph_subset restricted_graph_subset'
    by (meson Int_subset_iff)
  show "graph n g \<inter> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)) \<subseteq> restricted_graph n g S"
  proof fix x assume A: " x \<in> graph n g \<inter> cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"
    show "x \<in> restricted_graph n g S"
      apply(rule restricted_graph_memI)
      using A graph_memE[of g n x]
      apply (metis (no_types, lifting) Int_iff add.commute assms(1) graph_mem_closed plus_1_eq_Suc)
          using A graph_memE[of g n x] cartesian_product_memE[of x S "carrier (Q\<^sub>p\<^bsup>1\<^esup>)" Q\<^sub>p n]
          using assms(2) apply blast
          using A graph_memE[of g n x] cartesian_product_memE[of x S "carrier (Q\<^sub>p\<^bsup>1\<^esup>)" Q\<^sub>p n]
          using assms(1) by blast
   qed
 qed

lemma restricted_graph_is_semialgebraic:
  assumes "is_semialg_function n g"
  assumes "is_semialgebraic n S"
  shows "is_semialgebraic (n+1) (restricted_graph n g S)"
proof-
  have 0: "restricted_graph n g S = graph n g \<inter> (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
    using assms is_semialg_function_closed is_semialgebraic_closed
      restricted_graph_intersection by presburger
  have 1: "is_semialgebraic (n + 1) (graph n g)"
    using assms semialg_graph
    by blast
  have 2: "is_semialgebraic (n + 1) (cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>)))"
    using cartesian_product_is_semialgebraic[of n S 1 "carrier (Q\<^sub>p\<^bsup>1\<^esup>)"]  assms
      carrier_is_semialgebraic less_one
    by presburger
  then show ?thesis
    using 0 1 2 intersection_is_semialg[of "n+1" "graph n g" "cartesian_product S (carrier (Q\<^sub>p\<^bsup>1\<^esup>))"]
    by presburger
qed

lemma take_closed:
  assumes "n \<le> k"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  shows "take n x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  using assms take_closed
  by blast

lemma take_compose_closed:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "n < k"
  shows "g \<circ> take n \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>) \<rightarrow> carrier Q\<^sub>p"
proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  then have "(take n x) \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using assms  less_imp_le_nat take_closed
    by blast
  then have "g (take n x) \<in> carrier Q\<^sub>p"
    using assms(1) by blast
  then show "(g \<circ> take n) x \<in> carrier Q\<^sub>p"
    using comp_apply[of g "take n" x]
    by presburger
qed

lemma take_graph_formula:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "n < k"
  assumes "0 < n"
  shows "graph k (g \<circ> (take n)) = {as \<in> carrier (Q\<^sub>p\<^bsup>k+1\<^esup>). g (take n as) = as!k}"
proof-
  have "\<And>as. as \<in> carrier (Q\<^sub>p\<^bsup>k+1\<^esup>) \<Longrightarrow> (g \<circ> take n) (take k as) = g (take n as) "
    using assms comp_apply take_take[of n k]
  proof -
    fix as :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list"
    show "(g \<circ> take n) (take k as) = g (take n as)"
      by (metis (no_types) \<open>n < k\<close> comp_eq_dest_lhs min.strict_order_iff take_take)
  qed
  then show ?thesis
    using take_compose_closed[of g n k] assms comp_apply[of g "take n"] graph_formula[of "g \<circ> (take n)" k]
   by (smt Collect_cong Suc_eq_plus1)
qed

lemma graph_memI':
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "take n a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "g (take n a) = a!n"
  shows "a \<in> graph n g"
  using assms fun_graph_def[of Q\<^sub>p n g]
  by (smt cartesian_power_car_memE eq_imp_le lessI mem_Collect_eq take_Suc_conv_app_nth take_all)

lemma graph_memI'':
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "(a@[g a]) \<in> graph n g "
  using assms fun_graph_def
  by blast

lemma graph_as_restricted_graph:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows  "graph n f = restricted_graph n f (carrier (Q\<^sub>p\<^bsup>n\<^esup>))"
  apply(rule equalityI)
  apply (metis Suc_eq_plus1 assms graph_memE(1) graph_memE(3) graph_mem_closed restricted_graph_memI subsetI)
  by (simp add: assms restricted_graph_subset)

definition double_graph where
"double_graph n f g = {as \<in> carrier (Q\<^sub>p\<^bsup>n+2\<^esup>). f (take n as) = as!n \<and> g (take n as) = as!(n + 1)}"

lemma double_graph_rep:
  assumes "g \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  shows "double_graph n f g = restricted_graph (n + 1) (g \<circ> take n) (graph n f)"
proof
  show "double_graph n f g \<subseteq> restricted_graph (n + 1) (g \<circ> take n) (graph n f)"
  proof fix x assume A: "x \<in> double_graph n f g"
    then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>n+2\<^esup>) \<and> f (take n x) = x!n \<and> g (take n x) = x!(n + 1)"
      using double_graph_def by blast
     have 1: "take (n+1) x \<in> graph n f"
      apply(rule graph_memI)
       using assms(2) apply blast
        apply (metis "0" append_eq_conv_conj cartesian_power_car_memE le_add1 length_take
      less_add_same_cancel1 less_numeral_extra(1) min.absorb2 nth_take take_add)
       by (metis (no_types, opaque_lifting) "0" Suc_eq_plus1 Suc_n_not_le_n add_cancel_right_right
           dual_order.antisym le_iff_add not_less_eq_eq one_add_one plus_1_eq_Suc take_closed)
     show " x \<in> restricted_graph (n + 1) (g \<circ> take n) (graph n f)"
       apply(rule restricted_graph_memI)
         apply (metis "0" One_nat_def add_Suc_right numeral_2_eq_2)
       using "1" apply blast
       using 0 take_take[of n "n + 1" x] comp_apply
       by (metis le_add1 min.absorb1)
  qed
  show "restricted_graph (n + 1) (g \<circ> take n) (graph n f) \<subseteq> double_graph n f g"
  proof fix x
    assume A: "x \<in> restricted_graph (n + 1) (g \<circ> take n) (graph n f)"
    then have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc (n + 1)\<^esup>) \<and> take (n + 1) x \<in> graph n f \<and> (g \<circ> take n) (take (n + 1) x) = x ! (n + 1)"
      using restricted_graph_memE[of x "n+1" "(g \<circ> take n)" "graph n f" ]
      by blast
    then have 1: "x \<in> carrier (Q\<^sub>p\<^bsup>n+2\<^esup>)"
      using 0
      by (metis Suc_1 add_Suc_right)
    have 2: " f (take n x) = x ! n"
      using 0 take_take[of n "n + 1" x] graph_memE[of f n "take (n + 1) x"]
      by (metis assms(2) le_add1 less_add_same_cancel1 less_numeral_extra(1) min.absorb1 nth_take)
    have 3: "g (take n x) = x ! (n + 1)"
      using 0 comp_apply take_take[of n "n + 1" x]
      by (metis le_add1 min.absorb1)
    then show "x \<in> double_graph n f g"
      unfolding double_graph_def using 1 2 3
      by blast
  qed
qed

lemma double_graph_is_semialg:
  assumes "n > 0"
  assumes "is_semialg_function n f"
  assumes "is_semialg_function n g"
  shows "is_semialgebraic (n+2) (double_graph n f g)"
  using double_graph_rep[of g n f] assms restricted_graph_is_semialgebraic[of n "g \<circ> take n" "graph n f"]
  by (metis (no_types, lifting) Suc_eq_plus1 add_Suc_right is_semialg_function_closed
      less_add_same_cancel1 less_numeral_extra(1) one_add_one restricted_graph_is_semialgebraic
      comp_take_is_semialg semialg_graph)

definition add_vars :: "nat \<Rightarrow> nat  \<Rightarrow>  padic_tuple \<Rightarrow> padic_number" where
"add_vars i j as = as!i \<oplus>\<^bsub>Q\<^sub>p\<^esub> as!j"

lemma add_vars_rep:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "i < n"
  assumes "j < n"
  shows "add_vars i j as = Qp_ev ((pvar Q\<^sub>p i) \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar Q\<^sub>p j)) as"
  unfolding add_vars_def
  using assms eval_at_point_add[of as n "pvar Q\<^sub>p i" "pvar Q\<^sub>p j"]
        eval_pvar  by (metis  pvar_closed)

lemma add_vars_is_semialg:
  assumes "i < n"
  assumes "j < n"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "is_semialg_function n (add_vars i j)"
proof-
  have "pvar Q\<^sub>p i \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p j \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
    using  assms pvar_closed[of ]
    by blast
  then have "is_semialg_function n (Qp_ev (pvar Q\<^sub>p i \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p j))"
    using assms poly_is_semialg[of "(pvar Q\<^sub>p i) \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar Q\<^sub>p j)"]
    by blast
  then show ?thesis
    using assms add_vars_rep
      semialg_function_on_carrier[of n  "Qp_ev ((pvar Q\<^sub>p i) \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar Q\<^sub>p j))" "add_vars i j"  ]
  by (metis (no_types, lifting) restrict_ext)
qed

definition mult_vars :: "nat \<Rightarrow> nat  \<Rightarrow>  padic_tuple \<Rightarrow> padic_number" where
"mult_vars i j as = as!i \<otimes> as!j"

lemma mult_vars_rep:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "i < n"
  assumes "j < n"
  shows "mult_vars i j as = Qp_ev ((pvar Q\<^sub>p i) \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar Q\<^sub>p j)) as"
  unfolding mult_vars_def
  using assms eval_at_point_mult[of as n "pvar Q\<^sub>p i" "pvar Q\<^sub>p j"]
        eval_pvar[of i n as] eval_pvar[of j n as ]
  by (metis pvar_closed)

lemma mult_vars_is_semialg:
  assumes "i < n"
  assumes "j < n"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "is_semialg_function n (mult_vars i j)"
proof-
  have "pvar Q\<^sub>p i \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p j \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
    using  assms pvar_closed[of ]
    by blast
  then have "is_semialg_function n (Qp_ev (pvar Q\<^sub>p i \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> pvar Q\<^sub>p j))"
    using assms poly_is_semialg[of "(pvar Q\<^sub>p i) \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar Q\<^sub>p j)"]
    by blast
  then show ?thesis
    using assms mult_vars_rep
      semialg_function_on_carrier[of n  "Qp_ev ((pvar Q\<^sub>p i) \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar Q\<^sub>p j))" "mult_vars i j"  ]
    by (metis (no_types, lifting) restrict_ext)
qed

definition minus_vars :: "nat  \<Rightarrow>  padic_tuple \<Rightarrow> padic_number" where
"minus_vars i as =  \<ominus>\<^bsub>Q\<^sub>p\<^esub> as!i"

lemma minus_vars_rep:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "i < n"
  shows "minus_vars i as = Qp_ev (\<ominus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub>(pvar Q\<^sub>p i)) as"
  unfolding minus_vars_def
  using assms eval_pvar[of i n as] eval_at_point_a_inv[of as n "pvar Q\<^sub>p i"]
  by (metis pvar_closed)

lemma minus_vars_is_semialg:
  assumes "i < n"
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "is_semialg_function n (minus_vars i)"
proof-
  have 0: "pvar Q\<^sub>p i  \<in> carrier (Q\<^sub>p[\<X>\<^bsub>n\<^esub>])"
    using  assms pvar_closed[of ] Qp.cring_axioms by presburger
  have "is_semialg_function n  (Qp_ev (\<ominus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>n\<^esub>]\<^esub>(pvar Q\<^sub>p i)))"
    apply(rule poly_is_semialg )
    using "0" by blast
  then show ?thesis
    using assms minus_vars_rep[of a i n]
      semialg_function_on_carrier[of n  _ "minus_vars i"  ]
    by (metis (no_types, lifting) minus_vars_rep restrict_ext)
qed

definition extended_graph where
"extended_graph n f g h = {as \<in> carrier (Q\<^sub>p\<^bsup>n+3\<^esup>).
                      f (take n as) = as!n \<and> g (take n as) = as! (n + 1) \<and> h [(f (take n as)),(g (take n as))] = as! (n + 2) }"

lemma extended_graph_rep:
"extended_graph n f g h = restricted_graph (n + 2) (h \<circ> (drop n)) (double_graph n f g)"
proof
  show "extended_graph n f g h \<subseteq> restricted_graph (n + 2) (h \<circ> drop n) (double_graph n f g)"
  proof fix x
    assume "x \<in> extended_graph n f g h"
    then have A: "x \<in> carrier (Q\<^sub>p\<^bsup>n+3\<^esup>) \<and>f (take n x) = x!n \<and> g (take n x) = x! (n + 1) \<and>
                 h [(f (take n x)),(g (take n x))] = x! (n + 2)"
      unfolding extended_graph_def by blast
    then have 0: "take (n + 2) x  \<in> carrier (Q\<^sub>p\<^bsup>n+2\<^esup>)"
    proof -
      have "Suc (Suc n) \<le> n + numeral (num.One + num.Bit0 num.One)"
        by simp
      then show ?thesis
        by (metis (no_types) \<open>x \<in> carrier (Q\<^sub>p\<^bsup>n+3\<^esup>) \<and> f (take n x) = x ! n \<and> g (take n x) = x ! (n + 1) \<and> h [f (take n x), g (take n x)] = x ! (n + 2)\<close> add_2_eq_Suc' add_One_commute semiring_norm(5) take_closed)
    qed
    have 1: "f (take n (take (n + 2) x)) = (take (n + 2) x) ! n"
      using A
      by (metis Suc_1 add.commute append_same_eq append_take_drop_id
          less_add_same_cancel1 nth_take take_add take_drop zero_less_Suc)
    have 2: " g (take n (take (n + 2) x)) = (take (n + 2) x) ! (n + 1)"
      using A
      by (smt add.assoc add.commute append_same_eq append_take_drop_id less_add_same_cancel1
          less_numeral_extra(1) nth_take one_add_one take_add take_drop)
    then have 3: "take (n + 2) x \<in> double_graph n f g"
      unfolding double_graph_def
      using 0 1 2
      by blast
    have 4: "drop n (take (n + 2) x) = [(f (take n x)),(g (take n x))]"
    proof-
      have 40: "take (n + 2) x ! (n + 1) = x! (n + 1)"
        by (metis add.commute add_2_eq_Suc' lessI nth_take plus_1_eq_Suc)
      have 41: "take (n + 2) x ! n = x! n"
        by (metis Suc_1 less_SucI less_add_same_cancel1 less_numeral_extra(1) nth_take)
      have 42: "take (n + 2) x ! (n + 1) = g (take n x)"
        using 40 A
        by blast
      have 43: "take (n + 2) x ! n = f (take n x)"
        using 41 A
        by blast
      show ?thesis using A 42 43
        by (metis "0" add_cancel_right_right cartesian_power_car_memE cartesian_power_drop
            le_add_same_cancel1 nth_drop pair_id zero_le_numeral)
    qed
    then have 5: "(h \<circ> drop n) (take (n + 2) x) = x ! (n + 2)"
      using 3 A
      by (metis add_2_eq_Suc' comp_eq_dest_lhs)
    show "x \<in> restricted_graph (n + 2) (h \<circ> drop n) (double_graph n f g)"
      using restricted_graph_def A 3 5
      by (metis (no_types, lifting) One_nat_def Suc_1
          add_Suc_right numeral_3_eq_3 restricted_graph_memI)
  qed
  show "restricted_graph (n + 2) (h \<circ> drop n) (double_graph n f g) \<subseteq> extended_graph n f g h"
  proof fix x assume A: "x \<in> restricted_graph (n + 2) (h \<circ> drop n) (double_graph n f g)"
    then have 0: "take (n+2) x \<in> double_graph n f g"
      using restricted_graph_memE(2) by blast
    have 1: "(h \<circ> drop n) (take (n+2) x) = x! (n+2) "
      by (meson A restricted_graph_memE(3) padic_fields_axioms)
    have 2: "x \<in> carrier (Q\<^sub>p\<^bsup>n+3\<^esup>)"
      using A
      by (metis (no_types, opaque_lifting) Suc3_eq_add_3 add.commute add_2_eq_Suc'
          restricted_graph_closed subsetD)
    have 3: "length x = n + 3"
      using "2" cartesian_power_car_memE by blast
    have 4: "drop n (take (n+2) x) = [x!n, x!(n+1)]"
    proof-
      have "length (take (n+2) x) = n+2"
        by (simp add: "3")
      then have 40:"length (drop n (take (n+2) x)) = 2"
        by (metis add_2_eq_Suc' add_diff_cancel_left' length_drop)
      have 41: "(drop n (take (n+2) x))!0 = x!n"
        using 3
        by (metis Nat.add_0_right \<open>length (take (n + 2) x) = n + 2\<close> add_gr_0 le_add1 less_add_same_cancel1 less_numeral_extra(1) nth_drop nth_take one_add_one)
      have 42: "(drop n (take (n+2) x))!1 = x!(n+1)"
        using 3 nth_take nth_drop A
        by (metis add.commute le_add1 less_add_same_cancel1 less_numeral_extra(1) one_add_one take_drop)
      show ?thesis
        using 40 41 42
        by (metis pair_id)
    qed
    have "(take n x) = take n (take (n+2) x)"
      using take_take 3
      by (metis le_add1 min.absorb1)
    then have 5: "f (take n x) = x ! n"
      using 0 double_graph_def[of n f g] 3
      by (smt Suc_1 less_add_same_cancel1 mem_Collect_eq nth_take zero_less_Suc)
    have 6: "g (take n x) = x ! (n + 1) "
      using 0 double_graph_def[of n f g] 3 take_take[of n "n+2" x]
      by (smt Suc_1 \<open>take n x = take n (take (n + 2) x)\<close> add_Suc_right lessI mem_Collect_eq nth_take)
    have 7: " h [f (take n x), g (take n x)] = x ! (n + 2)"
      using 4 A comp_apply
      by (metis "1" "5" "6")
    show " x \<in> extended_graph n f g h"
      unfolding extended_graph_def
      using 2  5 6 7 A
      by blast
  qed
qed

lemma function_tuple_eval_closed:
  assumes "is_function_tuple Q\<^sub>p n fs"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "function_tuple_eval Q\<^sub>p n fs x \<in> carrier (Q\<^sub>p\<^bsup>length fs\<^esup>)"
  using function_tuple_eval_closed[of Q\<^sub>p n fs x] assms by blast

definition k_graph where
"k_graph n fs = {x \<in> carrier (Q\<^sub>p\<^bsup>n + length fs\<^esup>). x = (take n x)@ (function_tuple_eval Q\<^sub>p n fs (take n x)) }"

lemma k_graph_memI:
  assumes "is_function_tuple Q\<^sub>p n fs"
  assumes "x = as@function_tuple_eval Q\<^sub>p n fs as"
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "x \<in> k_graph n fs"
proof-
  have "take n x = as"
    using assms
    by (metis append_eq_conv_conj cartesian_power_car_memE)
  then show ?thesis unfolding k_graph_def using assms
    by (smt append_eq_conv_conj cartesian_power_car_memE cartesian_power_car_memI'' length_append local.function_tuple_eval_closed mem_Collect_eq)
qed

text\<open>composing a function with a function tuple\<close>

lemma Qp_function_tuple_comp_closed:
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "length fs = n"
  assumes "is_function_tuple Q\<^sub>p m fs"
  shows "function_tuple_comp Q\<^sub>p fs f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  using assms function_tuple_comp_closed
  by blast

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Tuples of Semialgebraic Functions\<close>
      (********************************************************************************************)
      (********************************************************************************************)

text\<open>Predicate for a tuple of semialgebraic functions\<close>

definition is_semialg_function_tuple where
"is_semialg_function_tuple n fs = (\<forall> f \<in> set fs. is_semialg_function n f)"

lemma is_semialg_function_tupleI:
  assumes "\<And> f. f \<in> set fs \<Longrightarrow> is_semialg_function n f"
  shows "is_semialg_function_tuple n fs"
  using assms is_semialg_function_tuple_def
  by blast

lemma is_semialg_function_tupleE:
  assumes "is_semialg_function_tuple n fs"
  assumes "i < length fs"
  shows "is_semialg_function n (fs ! i)"
  by (meson assms(1) assms(2) in_set_conv_nth is_semialg_function_tuple_def padic_fields_axioms)

lemma is_semialg_function_tupleE':
  assumes "is_semialg_function_tuple n fs"
  assumes "f \<in> set fs"
  shows "is_semialg_function n f"
  using assms(1) assms(2) is_semialg_function_tuple_def
  by blast

lemma semialg_function_tuple_is_function_tuple:
  assumes "is_semialg_function_tuple n fs"
  shows "is_function_tuple Q\<^sub>p n fs"
  apply(rule is_function_tupleI)
  using assms is_semialg_function_closed is_semialg_function_tupleE' by blast

lemma const_poly_function_tuple_comp_is_semialg:
  assumes "n > 0"
  assumes "is_semialg_function_tuple n fs"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "is_semialg_function n (poly_function_tuple_comp Q\<^sub>p n fs (Qp_to_IP a))"
  apply(rule semialg_function_on_carrier[of n "Qp_ev (Qp_to_IP a)"])
  using poly_is_semialg[of  "(Qp_to_IP a)"]
  using assms(1) assms(3) Qp_to_IP_car apply blast
  using poly_function_tuple_comp_eq[of n fs "(Qp_to_IP a)"]  assms unfolding restrict_def
  by (metis (no_types, opaque_lifting) eval_at_point_const poly_function_tuple_comp_constant semialg_function_tuple_is_function_tuple)

lemma pvar_poly_function_tuple_comp_is_semialg:
  assumes "n > 0"
  assumes "is_semialg_function_tuple n fs"
  assumes "i < length fs"
  shows "is_semialg_function n (poly_function_tuple_comp Q\<^sub>p n fs (pvar Q\<^sub>p i))"
  apply(rule semialg_function_on_carrier[of n "fs!i"])
  using assms(2) assms(3) is_semialg_function_tupleE apply blast
  by (metis assms(2) assms(3) poly_function_tuple_comp_pvar
      restrict_ext semialg_function_tuple_is_function_tuple)

text\<open>Polynomial functions with semialgebraic coefficients\<close>

definition point_to_univ_poly :: "nat \<Rightarrow> padic_tuple \<Rightarrow> padic_univ_poly" where
"point_to_univ_poly n a = ring_cfs_to_univ_poly n a"

definition tuple_partial_image where
"tuple_partial_image m fs x = (function_tuple_eval Q\<^sub>p m fs (take m x))@(drop m x)"

lemma tuple_partial_image_closed:
  assumes "length fs > 0"
  assumes "is_function_tuple Q\<^sub>p n fs"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
  shows "tuple_partial_image n fs x \<in> carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>)"
  using assms unfolding tuple_partial_image_def
  by (meson cartesian_power_concat(1) cartesian_power_drop
      function_tuple_eval_closed le_add1 take_closed)

lemma tuple_partial_image_indices:
  assumes "length fs > 0"
  assumes "is_function_tuple Q\<^sub>p n fs"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
  assumes "i < length fs"
  shows "(tuple_partial_image n fs x) ! i = (fs!i) (take n x)"
proof-
  have 0: "(function_tuple_eval Q\<^sub>p n fs (take n x)) ! i = (fs!i) (take n x)"
    using assms unfolding function_tuple_eval_def
    by (meson nth_map)
  have 1: "length (function_tuple_eval Q\<^sub>p n fs (take n x)) > i"
    by (metis assms(4) function_tuple_eval_def length_map)
  show ?thesis
    using 0 1 assms unfolding tuple_partial_image_def
    by (metis nth_append)
qed

lemma tuple_partial_image_indices':
  assumes "length fs > 0"
  assumes "is_function_tuple Q\<^sub>p n fs"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
  assumes "i < l"
  shows "(tuple_partial_image n fs x) ! (length fs + i) = x!(n + i)"
  using assms unfolding tuple_partial_image_def
  by (metis (no_types, lifting) cartesian_power_car_memE function_tuple_eval_closed le_add1
      nth_append_length_plus nth_drop take_closed)

definition tuple_partial_pullback where
"tuple_partial_pullback n fs l S = ((tuple_partial_image n fs)-`S)  \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"

lemma tuple_partial_pullback_memE:
  assumes "as \<in> tuple_partial_pullback m fs l S"
  shows "as \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)" "tuple_partial_image m fs as \<in> S"
  using assms
  apply (metis (no_types, opaque_lifting) Int_iff add.commute tuple_partial_pullback_def)
  using assms unfolding tuple_partial_pullback_def
  by blast

lemma tuple_partial_pullback_closed:
"tuple_partial_pullback m fs l S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  using tuple_partial_pullback_memE by blast

lemma tuple_partial_pullback_memI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
  assumes "is_function_tuple Q\<^sub>p m fs"
  assumes "((function_tuple_eval Q\<^sub>p m fs) (take m as))@(drop m as) \<in> S"
  shows "as \<in> tuple_partial_pullback m fs k S"
  using assms unfolding tuple_partial_pullback_def tuple_partial_image_def
  by blast

lemma tuple_partial_image_eq:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  assumes "x = as @ bs"
  shows "tuple_partial_image n fs x = ((function_tuple_eval Q\<^sub>p n fs) as)@bs"
proof-
  have 0: "(take n x) = as"
    by (metis append_eq_conv_conj assms(1) assms(3) cartesian_power_car_memE)
  have 1: "drop n x = bs"
    by (metis "0" append_take_drop_id assms(3) same_append_eq)
  show ?thesis using assms 0 1 unfolding tuple_partial_image_def
    by presburger
qed

lemma tuple_partial_pullback_memE':
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
  assumes "x = as @ bs"
  assumes "x \<in> tuple_partial_pullback n fs k S"
  shows "(function_tuple_eval Q\<^sub>p n fs as)@bs \<in> S"
  using tuple_partial_pullback_memE[of x n fs k S] tuple_partial_image_def[of n fs x]
  by (metis assms(1) assms(2) assms(3) assms(4) tuple_partial_image_eq)

text\<open>tuple partial pullbacks have the same algebraic properties as pullbacks\<close>

lemma tuple_partial_pullback_intersect:
"tuple_partial_pullback m f l (S1 \<inter> S2) = (tuple_partial_pullback m f l S1) \<inter> (tuple_partial_pullback m f l S2)"
  unfolding tuple_partial_pullback_def
  by blast

lemma tuple_partial_pullback_union:
"tuple_partial_pullback m f l (S1 \<union> S2) = (tuple_partial_pullback m f l S1) \<union> (tuple_partial_pullback m f l S2)"
  unfolding tuple_partial_pullback_def
  by blast

lemma tuple_partial_pullback_complement:
  assumes "is_function_tuple Q\<^sub>p m fs"
  shows "tuple_partial_pullback m fs l ((carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>)) - S) = carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) - (tuple_partial_pullback m fs l S) "
  apply(rule equalityI)
  using tuple_partial_pullback_def[of m fs l "((carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>)) - S)"]
        tuple_partial_pullback_def[of m fs l S]
   apply blast
proof fix x assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) - tuple_partial_pullback m fs l S"
  show " x \<in> tuple_partial_pullback m fs l (carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>) - S) "
    apply(rule tuple_partial_pullback_memI)
    using A
      apply blast
    using assms
    apply blast
  proof
    have 0: "drop m x \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
      by (meson A DiffD1 cartesian_power_drop)
    have 1: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A
      by (meson DiffD1 le_add1 take_closed)
    show "function_tuple_eval Q\<^sub>p m fs (take m x) @ drop m x
    \<in> carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>)"
      using 0 1 assms
      using cartesian_power_concat(1) function_tuple_eval_closed by blast
    show "function_tuple_eval Q\<^sub>p m fs (take m x) @ drop m x \<notin> S"
      using A unfolding tuple_partial_pullback_def tuple_partial_image_def
      by blast
  qed
qed

lemma tuple_partial_pullback_carrier:
  assumes "is_function_tuple Q\<^sub>p m fs"
  shows "tuple_partial_pullback m fs l (carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>)) = carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  apply(rule equalityI)
  using tuple_partial_pullback_memE(1) apply blast
proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  show "x \<in> tuple_partial_pullback m fs l (carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>))"
    apply(rule tuple_partial_pullback_memI)
  using A cartesian_power_drop[of x m l] take_closed assms
    apply blast
  using assms apply blast
  proof-
    have "function_tuple_eval Q\<^sub>p m fs (take m x) \<in> carrier (Q\<^sub>p\<^bsup>length fs\<^esup>)"
      using A take_closed assms
          function_tuple_eval_closed le_add1
      by blast
    then show "function_tuple_eval Q\<^sub>p m fs (take m x) @ drop m x
    \<in> carrier (Q\<^sub>p\<^bsup>length fs + l\<^esup>)"
    using cartesian_power_drop[of x m l] A cartesian_power_concat(1)
    by blast
  qed
qed

definition is_semialg_map_tuple where
"is_semialg_map_tuple m fs = (is_function_tuple Q\<^sub>p m fs \<and>
                          (\<forall>l \<ge> 0. \<forall>S \<in> semialg_sets ((length fs) + l). is_semialgebraic (m + l) (tuple_partial_pullback m fs l S)))"

lemma is_semialg_map_tuple_closed:
  assumes "is_semialg_map_tuple m fs"
  shows "is_function_tuple Q\<^sub>p m fs"
  using is_semialg_map_tuple_def assms by blast

lemma is_semialg_map_tupleE:
  assumes "is_semialg_map_tuple m fs"
  assumes "is_semialgebraic ((length fs) + l) S"
  shows " is_semialgebraic (m + l) (tuple_partial_pullback m fs l S)"
  using is_semialg_map_tuple_def[of m fs] assms is_semialgebraicE[of "((length fs) + l)" S]
  by blast

lemma is_semialg_map_tupleI:
  assumes "is_function_tuple Q\<^sub>p m fs"
  assumes "\<And>k  S. S \<in> semialg_sets ((length fs) + k) \<Longrightarrow> is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
  shows "is_semialg_map_tuple m fs"
  using assms unfolding is_semialg_map_tuple_def
  by blast

text\<open>Semialgebraicity for maps can be verified on basic semialgebraic sets\<close>

lemma is_semialg_map_tupleI':
  assumes "is_function_tuple Q\<^sub>p m fs"
  assumes "\<And>k  S. S \<in> basic_semialgs ((length fs) + k) \<Longrightarrow> is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
  shows "is_semialg_map_tuple m fs"
  apply(rule is_semialg_map_tupleI)
  using assms(1) apply blast
proof-
  show "\<And>k S. S \<in> semialg_sets ((length fs) + k) \<Longrightarrow> is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
  proof- fix k S assume A: "S \<in> semialg_sets ((length fs) + k)"
    show "is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
      apply(rule gen_boolean_algebra.induct[of S "carrier (Q\<^sub>p\<^bsup>length fs + k\<^esup>)" "basic_semialgs ((length fs) + k)"])
        using A unfolding semialg_sets_def
            apply blast
        using tuple_partial_pullback_carrier assms carrier_is_semialgebraic plus_1_eq_Suc apply presburger
        using assms(1) assms(2) carrier_is_semialgebraic intersection_is_semialg tuple_partial_pullback_carrier tuple_partial_pullback_intersect apply presburger
                using tuple_partial_pullback_union union_is_semialgebraic apply presburger
        using assms(1) complement_is_semialg tuple_partial_pullback_complement plus_1_eq_Suc by presburger
  qed
qed

text\<open>
  The goal of this section is to show that tuples of semialgebraic functions are semialgebraic maps.
\<close>

text\<open>The function $(x_0, x, y) \mapsto (x_0, f(x), y)$\<close>

definition twisted_partial_image where
"twisted_partial_image n m f xs = (take n xs)@ partial_image m f (drop n xs)"

text\<open>The set ${(x_0, x, y) \mid (x_0, f(x), y) \in S}$\<close>

text\<open>Convention: a function which produces a subset of (Qp (i + j +k)) will receive the 3 arity
parameters in sequence, at the very beginning of the function\<close>

definition twisted_partial_pullback where
"twisted_partial_pullback n m l f S = ((twisted_partial_image n m f)-`S)  \<inter> carrier (Q\<^sub>p\<^bsup>n+m+l\<^esup>)"

lemma twisted_partial_pullback_memE:
  assumes "as \<in> twisted_partial_pullback n m l f S"
  shows "as \<in> carrier (Q\<^sub>p\<^bsup>n+m+l\<^esup>)" "twisted_partial_image n m f as \<in> S"
  using assms
  apply (metis (no_types, opaque_lifting) Int_iff add.commute twisted_partial_pullback_def subset_iff)
  using assms unfolding twisted_partial_pullback_def
  by blast

lemma twisted_partial_pullback_closed:
"twisted_partial_pullback n m l f S \<subseteq> carrier (Q\<^sub>p\<^bsup>n+m+l\<^esup>)"
  using twisted_partial_pullback_memE(1) by blast

lemma twisted_partial_pullback_memI:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n+m+l\<^esup>)"
  assumes "(take n as)@((f (take m (drop n as)))#(drop (n + m) as)) \<in> S"
  shows "as \<in> twisted_partial_pullback n m l f S"
  using assms unfolding twisted_partial_pullback_def twisted_partial_image_def
  by (metis (no_types, lifting) IntI add.commute drop_drop local.partial_image_def vimageI)

lemma twisted_partial_image_eq:
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "cs \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
  assumes "x = as @ bs @ cs"
  shows "twisted_partial_image n m f x = as@((f bs)#cs)"
proof-
  have 0: "(take n x) = as"
    by (metis append_eq_conv_conj assms(1) assms(4)
        cartesian_power_car_memE)
  have 1: "twisted_partial_image n m f x = as@(partial_image m f (bs@cs))"
    using 0 assms twisted_partial_image_def
    by (metis append_eq_conv_conj cartesian_power_car_memE)
  have 2: "(partial_image m f (bs@cs)) = (f bs)#cs"
    using partial_image_eq[of bs m cs l "bs@cs" f] assms
    by blast
  show ?thesis using assms 0 1 2
    by (metis )
qed

lemma twisted_partial_pullback_memE':
  assumes "as \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  assumes "bs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "cs \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
  assumes "x = as @ bs @ cs"
  assumes "x \<in> twisted_partial_pullback n m l f S"
  shows "as@((f bs)#cs) \<in> S"
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) assms(5)
      twisted_partial_image_eq twisted_partial_pullback_memE(2))

text\<open>partial pullbacks have the same algebraic properties as pullbacks\<close>

text\<open>permutation which moves the entry at index \<open>i\<close> to 0\<close>

definition twisting_permutation where
"twisting_permutation (i::nat) = (\<lambda>j. if j < i then j + 1 else
                                 (if j = i then 0 else j))"

lemma twisting_permutation_permutes:
  assumes "i < n"
  shows "twisting_permutation i permutes {..<n}"
proof-
  have 0: "\<And>x. x > i \<Longrightarrow> twisting_permutation i x = x"
    unfolding twisting_permutation_def
    by auto
  have 1: "(\<forall>x. x \<notin> {..<n} \<longrightarrow> twisting_permutation i x = x)"
    using 0 assms
    by auto
  have 2: "(\<forall>y. \<exists>!x. twisting_permutation i x = y)"
  proof fix y
    show " \<exists>!x. twisting_permutation i x = y"
    proof(cases "y = 0")
      case True
      show "\<exists>!x. twisting_permutation i x = y"
        by (metis  Suc_eq_plus1 True  add_eq_0_iff_both_eq_0 less_nat_zero_code
            nat_neq_iff twisting_permutation_def zero_neq_one)
    next
      case False
      show ?thesis
      proof(cases "y \<le>i")
        case True
        show ?thesis
        proof
          show "twisting_permutation i (y - 1) = y"
            using True
            by (metis False add.commute add_diff_inverse_nat diff_less gr_zeroI le_eq_less_or_eq
                  less_imp_diff_less less_one twisting_permutation_def)
          show "\<And>x. twisting_permutation i x = y \<Longrightarrow> x = y - 1"
            using True False twisting_permutation_def by force
        qed
      next
        case F: False
        then show ?thesis using False
          unfolding twisting_permutation_def
          by (metis  add_leD1 add_leD2 add_le_same_cancel2 discrete le_numeral_extra(3)
              less_imp_not_less )
      qed
    qed
  qed
  show ?thesis
    using 1 2
    by (simp add: permutes_def)
qed

lemma twisting_permutation_action:
  assumes "length as = i"
  shows "permute_list (twisting_permutation i) (b#(as@bs)) =  as@(b#bs)"
proof-
  have 0: "length (permute_list (twisting_permutation i) (b#(as@bs))) = length  (as@(b#bs))"
    by (metis add.assoc length_append length_permute_list list.size(4))
  have "\<And>j. j < length (as@(b#bs))
          \<Longrightarrow> (permute_list (twisting_permutation i) (b#(as@bs))) ! j =  (as@(b#bs)) ! j"
  proof-
    fix j assume A: "j < length (as@(b#bs))"
    show "(permute_list (twisting_permutation i) (b#(as@bs))) ! j =  (as@(b#bs)) ! j"
    proof(cases "j < i")
      case True
      then have T0: "twisting_permutation i j = j + 1"
        using twisting_permutation_def by auto
      then have T1: "(b # as @ bs) ! twisting_permutation i j = as!j"
        using assms
        by (simp add: assms True nth_append)
      have T2: "(permute_list (twisting_permutation i) (b # as @ bs)) ! j = as!j"
      proof-
        have "twisting_permutation i permutes {..<length (b # as @ bs)}"
          by (metis (full_types) assms length_Cons length_append
              not_add_less1 not_less_eq twisting_permutation_permutes)
        then show ?thesis
          using True permute_list_nth[of "twisting_permutation i" "b#(as@bs)" j ]
              twisting_permutation_permutes[of i "length (b#(as@bs))"] assms
          by (metis T0 T1 add_cancel_right_right lessThan_iff
              permutes_not_in zero_neq_one)
      qed
      have T3: "(as @ b # bs) ! j = as!j"
        using assms True
        by (simp add: assms nth_append)
      show "(permute_list (twisting_permutation i) (b #( as @ bs))) ! j = (as @ b # bs) ! j"
        using T3 T2
        by simp
    next
      case False
      show ?thesis
      proof(cases "j = i")
        case True
      then have T0: "twisting_permutation i j = 0"
        using twisting_permutation_def by auto
      then have T1: "(b # as @ bs) ! twisting_permutation i j = b"
        using assms
        by (simp add: assms True nth_append)
      have T2: "(permute_list (twisting_permutation i) (b # as @ bs)) ! j = b"
      proof-
        have "twisting_permutation i permutes {..<length (b # as @ bs)}"
          by (metis (full_types) assms length_Cons length_append
              not_add_less1 not_less_eq twisting_permutation_permutes)
        then show ?thesis
          using True permute_list_nth[of "twisting_permutation i" "b#(as@bs)" j ]
              twisting_permutation_permutes[of i "length (b#(as@bs))"] assms
          by (metis "0" A T1 length_permute_list)
      qed
      have T3: "(as @ b # bs) ! j = b"
        by (metis True assms nth_append_length)
      show ?thesis
        by (simp add: T2 T3)
      next
        case F: False
        then have F0: "twisting_permutation i j = j"
          by (simp add: False twisting_permutation_def)
        then have F1: "(b # as @ bs) ! twisting_permutation i j = bs! (j - i - 1)"
          using assms
          by (metis (mono_tags, lifting) F False Suc_diff_1
              cancel_ab_semigroup_add_class.diff_right_commute linorder_neqE_nat not_gr_zero
              not_less_eq nth_Cons' nth_append)
        have F2: "(permute_list (twisting_permutation i) (b # as @ bs)) ! j = bs ! (j - i - 1)"
          using F1 assms permute_list_nth
          by (metis A add_cancel_right_right append.assoc last_to_first_eq le_add1
              le_eq_less_or_eq length_0_conv length_append length_permute_list list.distinct(1)
              twisting_permutation_permutes)
        have F3: "(as @ b # bs) ! j = bs!(j - i - 1)"
          by (metis F False assms linorder_neqE_nat nth_Cons_pos nth_append zero_less_diff)
        then show ?thesis
          using F2 F3
          by presburger
      qed
    qed
  qed
  then show ?thesis
    using 0
    by (metis nth_equalityI)
qed

lemma twisting_permutation_action':
  assumes "length as = i"
  shows "permute_list (fun_inv (twisting_permutation i)) (as@(b#bs)) = (b#(as@bs)) "
proof-
  obtain TI where TI_def: "TI = twisting_permutation i"
    by blast
  have 0: "TI permutes {..<length (as@(b#bs))}"
    using assms TI_def twisting_permutation_permutes[of i "length (as@(b#bs))"]
    by (metis add_diff_cancel_left' gr0I length_0_conv length_append list.distinct(1) zero_less_diff)
  have 1: "(fun_inv TI) permutes {..<length (as@(b#bs))}"
    by (metis "0" Nil_is_append_conv fun_inv_permute(1) length_greater_0_conv list.distinct(1))
  have "permute_list (fun_inv (twisting_permutation i)) (as@(b#bs)) =
        permute_list (fun_inv (twisting_permutation i)) (permute_list (twisting_permutation i) (b#(as@bs)))"
    using twisting_permutation_action[of as i b bs] assms
    by (simp add: \<open>length as = i\<close>)
  then have "permute_list (fun_inv TI) (as@(b#bs)) =
  permute_list ((fun_inv TI) \<circ> TI) (b#(as@bs))"
    using 0 1
    by (metis TI_def fun_inv_permute(2) fun_inv_permute(3) length_greater_0_conv
        length_permute_list permute_list_compose)
  then show ?thesis
    by (metis "0" Nil_is_append_conv TI_def fun_inv_permute(3)
        length_greater_0_conv list.distinct(1) permute_list_id)
qed

lemma twisting_semialg:
  assumes "is_semialgebraic n S"
  assumes "n > i"
  shows "is_semialgebraic n ((permute_list ((twisting_permutation i)) ` S))"
proof-
  obtain TI where TI_def: "TI = twisting_permutation i"
    by blast
  have 0: "TI permutes {..<(n::nat)}"
    using assms TI_def twisting_permutation_permutes[of i n]
    by blast
  have "(TI) permutes {..<n}"
    using TI_def  "0"
    by auto
  then show ?thesis
    using assms permutation_is_semialgebraic[of n S "TI"] TI_def
    by blast
qed

lemma twisting_semialg':
  assumes "is_semialgebraic n S"
  assumes "n > i"
  shows "is_semialgebraic n ((permute_list (fun_inv (twisting_permutation i)) ` S))"
proof-
  obtain TI where TI_def: "TI = twisting_permutation i"
    by blast
  have 0: "TI permutes {..<(n::nat)}"
    using assms TI_def twisting_permutation_permutes[of i n]
    by blast
  have "(fun_inv TI) permutes {..<n}" using 0 permutes_inv[of TI "{..<n}"]
    unfolding fun_inv_def
    by blast
  then show ?thesis
    using assms permutation_is_semialgebraic[of n S "fun_inv TI"] TI_def
    by blast
qed

text\<open>Defining a permutation that does: $(x0, x1, y) \mapsto (x_1, x0, y)$\<close>

definition tp_1 where
"tp_1 i j = (\<lambda> n. (if n<i then j + n else
                  (if i \<le> n \<and> n < i + j then n - i else
                   n)))"
lemma permutes_I:
  assumes "\<And>x. x \<notin> S \<Longrightarrow> f x = x"
  assumes "\<And>y. y \<in> S \<Longrightarrow> \<exists>!x \<in> S. f x = y"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<in> S"
  shows "f permutes S"
proof-
  have 0 : "(\<forall>x. x \<notin> S \<longrightarrow> f x = x) "
    using assms(1) by blast
  have 1: "(\<forall>y. \<exists>!x. f x = y)"
  proof fix y
    show "\<exists>!x. f x = y"
      apply(cases "y \<in> S")
       apply (metis "0" assms(2))
    proof-
      assume "y \<notin> S"
      then show "\<exists>!x. f x = y"
        by (metis assms(1) assms(3))
    qed
  qed
  show ?thesis
    using assms 1
    unfolding permutes_def
    by blast
qed

lemma tp_1_permutes:
"(tp_1 (i::nat) j) permutes {..< i + j}"
proof(rule permutes_I)
  show "\<And>x. x \<notin> {..<i + j} \<Longrightarrow> tp_1 i j x = x"
  proof- fix x assume A: "x \<notin> {..<i + j}"
    then show "tp_1 i j x = x"
      unfolding tp_1_def
      by auto
  qed
  show "\<And>y. y \<in> {..<i + j} \<Longrightarrow> \<exists>!x. x \<in> {..<i + j} \<and> tp_1 i j x = y"
  proof- fix y assume A: "y \<in> {..<i + j}"
    show "\<exists>!x. x \<in> {..<i + j} \<and> tp_1 i j x = y"
    proof(cases "y < j")
      case True
      then have 0:"tp_1 i j (y + i) = y"
        by (simp add: tp_1_def)
      have 1: "\<And>x. x \<noteq> y + i \<Longrightarrow> tp_1 i j x \<noteq> y"
      proof- fix x assume A: " x \<noteq> y + i"
        show "tp_1 i j x \<noteq> y"
          apply(cases "x < j")
           apply (metis A True add.commute le_add_diff_inverse le_eq_less_or_eq nat_neq_iff not_add_less1 tp_1_def trans_less_add2)
          by (metis A True add.commute le_add_diff_inverse less_not_refl tp_1_def trans_less_add1)
      qed
      show ?thesis using 0 1
        by (metis A \<open>\<And>x. x \<notin> {..<i + j} \<Longrightarrow> tp_1 i j x = x\<close>)
    next
      case False
      then have "y - j < i"
        using A by auto
      then have "tp_1 i j (y - j) = y"
        using False tp_1_def
        by (simp add: tp_1_def)
      then show ?thesis
        by (smt A False \<open>\<And>x. x \<notin> {..<i + j} \<Longrightarrow> tp_1 i j x = x\<close>
            add.commute add_diff_inverse_nat add_left_imp_eq
            less_diff_conv2 not_less tp_1_def
            padic_fields_axioms)
    qed
  qed
  show "\<And>x. x \<in> {..<i + j} \<Longrightarrow> tp_1 i j x \<in> {..<i + j}"
  proof fix x assume A: "x \<in> {..<i + j}"
    show "tp_1 i j x < i + j"
      unfolding tp_1_def using A
      by (simp add: trans_less_add2)
  qed
qed

lemma tp_1_permutes':
"(tp_1 (i::nat) j) permutes {..< i + j + k}"
  using tp_1_permutes
  by (simp add: permutes_def)

lemma tp_1_permutation_action:
  assumes "a \<in> carrier (Q\<^sub>p\<^bsup>i\<^esup>)"
  assumes "b \<in> carrier (Q\<^sub>p\<^bsup>j\<^esup>)"
  assumes "c \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
  shows "permute_list (tp_1 i j) (b@a@c)= a@b@c"
proof-
  have 0:"length (permute_list (tp_1 i j) (b@a@c))= length (a@b@c)"
    by (metis add.commute append.assoc length_append length_permute_list)
  have "\<And>x. x < length (a@b@c) \<Longrightarrow> (permute_list (tp_1 i j) (b@a@c)) ! x= (a@b@c) ! x"
  proof- fix x assume A: "x < length (a@b@c)"
    have B: "length (a @ b @ c) = i + j + length c"
      using add.assoc assms(1) assms(2) cartesian_power_car_memE length_append
      by metis
    have C: "tp_1 i j permutes {..<length (a @ b @ c)}"
      using B assms tp_1_permutes'[of i j "length b"] tp_1_permutes'
      by presburger
    have D: "length a = i"
      using assms(1) cartesian_power_car_memE by blast
    have E: "length b = j"
      using assms(2) cartesian_power_car_memE by blast
    show "(permute_list (tp_1 i j) (b@a@c)) ! x= (a@b@c) ! x"
    proof(cases "x < i")
      case True
      have T0: "(tp_1 i j x) = j + x"
        using tp_1_def[of i j ] True
        by auto
      then have "(b@ a @ c) ! (tp_1 i j x) = a!x"
        using D E assms(1) assms(2) assms(3) True nth_append
        by (metis nth_append_length_plus)
      then show ?thesis
        using A B C assms permute_list_nth[of "tp_1 i j" "a@b@c"]
        by (metis D True \<open>length (permute_list (tp_1 i j) (b @ a @ c)) =
             length (a @ b @ c)\<close> length_permute_list nth_append permute_list_nth)
    next
      case False
      show ?thesis
      proof(cases "x < i + j")
        case True
        then have T0: "(tp_1 i j x) = x - i"
          by (meson False not_less tp_1_def)
        have "x - i < length b"
          using E False True by linarith
        then have T1: "permute_list (tp_1 i j) (b@ a @ c) ! x = b!(x-i)"
          using nth_append
          by (metis A C T0 \<open>length (permute_list (tp_1 i j) (b @ a @ c)) = length (a @ b @ c)\<close>
              length_permute_list permute_list_nth)
        then show ?thesis
          by (metis D False \<open>x - i < length b\<close> nth_append)
      next
        case False
        then have "(tp_1 i j x) = x"
          by (meson tp_1_def trans_less_add1)
        then show ?thesis
          by (smt A C D E False add.commute add_diff_inverse_nat append.assoc
              length_append nth_append_length_plus permute_list_nth)
      qed
    qed
qed
  then show ?thesis
    using 0
    by (metis list_eq_iff_nth_eq)
qed

definition tw where
"tw i j = permute_list (tp_1 j i)"

lemma tw_is_semialg:
  assumes "n > 0"
  assumes "is_semialgebraic n S"
  assumes "n \<ge> i + j"
  shows "is_semialgebraic n ((tw i j)`S)"
  unfolding tw_def
  using assms tp_1_permutes'[of j i "n - (j + i)"]
        permutation_is_semialgebraic[of n S]
  by (metis add.commute le_add_diff_inverse)

lemma twisted_partial_pullback_factored:
  assumes "f \<in> (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<rightarrow> carrier Q\<^sub>p"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>n+1+ l\<^esup>)"
  assumes "Y = partial_pullback m f (n + l) (permute_list (fun_inv (twisting_permutation n)) ` S)"
  shows "twisted_partial_pullback n m l f S = (tw m n) ` Y"
proof
  show "twisted_partial_pullback n m l f S \<subseteq> tw m n ` Y"
  proof fix x
    assume A: "x \<in> twisted_partial_pullback n m l f S"
    then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n+m+l\<^esup>)"
      using twisted_partial_pullback_memE(1) by blast
    obtain a where a_def: "a = take n x"
      by blast
    obtain b where b_def: "b = take m (drop n x)"
      by blast
    obtain c where c_def: "c = (drop (n + m) x)"
      by blast
    have x_eq:"x = a@(b@c)"
      by (metis a_def append.assoc append_take_drop_id b_def c_def take_add)
    have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      by (metis (no_types, lifting) a_def dual_order.trans le_add1 take_closed x_closed)
    have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    proof-
      have "drop n x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
        by (metis (no_types, lifting) add.assoc cartesian_power_drop x_closed)
      then show ?thesis
        using b_def le_add1 take_closed by blast
    qed
    have c_closed: "c \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
      using c_def cartesian_power_drop x_closed by blast
    have B: "a@((f b)#c) \<in> S"
      using A twisted_partial_pullback_memE'
      by (smt a_closed a_def add.commute append_take_drop_id b_closed
          b_def c_closed c_def drop_drop)
    have  "permute_list (fun_inv (twisting_permutation n)) (a@((f b)#c)) = (f b)#(a@c)"
       using assms twisting_permutation_action'[of a n "f b" c]
               a_closed cartesian_power_car_memE
       by blast
    then have  C: "(f b)#(a@c) \<in> (permute_list (fun_inv (twisting_permutation n)) ` S)"
       by (metis B image_eqI)
    have C: "b@(a@c) \<in>  partial_pullback m f (n + l) (permute_list (fun_inv (twisting_permutation n)) ` S)"
    proof(rule partial_pullback_memI)
      show "b @ a @ c \<in> carrier (Q\<^sub>p\<^bsup>m + (n + l)\<^esup>)"
        using a_closed b_closed c_closed cartesian_power_concat(1)
        by blast
      have 0: "(take m (b @ a @ c)) = b"
        by (metis append.right_neutral b_closed  cartesian_power_car_memE
            diff_is_0_eq diff_self_eq_0 take0 take_all take_append)
      have 1: "drop m (b @ a @ c) = a@c"
        by (metis "0" append_take_drop_id same_append_eq)
      show "f (take m (b @ a @ c)) # drop m (b @ a @ c) \<in> permute_list (fun_inv (twisting_permutation n)) ` S"
        using 0 1 C
        by presburger
    qed
    have D: "tw m n (b@(a@c)) = a@(b@c)"
      using assms tw_def a_closed b_closed c_closed
      by (metis tp_1_permutation_action x_eq)
    then show "x \<in> tw m n ` Y"
      using x_eq C assms
      by (metis image_eqI)
  qed
  show "tw m n ` Y \<subseteq> twisted_partial_pullback n m l f S"
  proof fix x
    assume A: "x \<in> tw m n ` Y"
    then obtain y where y_def: "x = tw m n y \<and> y \<in> Y"
      by blast
    obtain as where as_def: "as \<in> (permute_list (fun_inv (twisting_permutation n)) ` S) \<and>
                            as = partial_image m f y"
      using partial_pullback_memE
      by (metis assms(3) y_def)
    obtain s where s_def: "s \<in> S \<and> permute_list (fun_inv (twisting_permutation n)) s = as"
      using as_def by blast
    obtain b where b_def: "b = take m y"
      by blast
    obtain a where a_def: "a = take n (drop m y)"
      by blast
    obtain c where c_def: "c = drop (n + m) y"
      by blast
    have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m  + n + l\<^esup>)"
      by (metis add.assoc assms(3) partial_pullback_memE(1) y_def)
    then have y_eq: "y = b@a@c"
      using a_def b_def c_def
      by (metis append_take_drop_id drop_drop)
    have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
      by (metis a_def add.commute cartesian_power_drop le_add1 take_closed take_drop y_closed)
    have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using add_leD2 b_def le_add1 take_closed y_closed
      by (meson trans_le_add1)
    have c_closed: "c \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
      using c_def cartesian_power_drop y_closed
      by (metis add.commute)
    have ac_closed: "a@c \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
      using a_closed c_closed cartesian_power_concat(1) by blast
    then have C: " local.partial_image m f y = f b # a @ c"
      using b_closed y_eq partial_image_eq[of b m "a@c" "n + l" y f]
      by blast
    then have as_eq: "as = (f b)#(a@c)"
      using  as_def
      by force
    have B: "(tw m n) y = a@b@c" using y_eq tw_def[of n m] tp_1_permutation_action
      by (smt a_closed b_closed c_closed tw_def)
    then have "x = a@(b@c)"
      by (simp add: y_def)
    then have "twisted_partial_image n m f x =  a@((f b)# c)"
      using a_closed b_closed c_closed twisted_partial_image_eq
      by blast
    then have D: "permute_list (twisting_permutation n) as = twisted_partial_image n m f x"
      using as_eq twisting_permutation_action[of a n "f b" c ]
      by (metis a_closed cartesian_power_car_memE)
    have "permute_list (twisting_permutation n) as \<in> S"
    proof-
      have S: "length s > n"
        using s_def assms cartesian_power_car_memE le_add1 le_neq_implies_less
            le_trans less_add_same_cancel1 less_one not_add_less1
        by (metis (no_types, lifting) subset_iff)
      have "permute_list (twisting_permutation n) as = permute_list (twisting_permutation n) (permute_list (fun_inv (twisting_permutation n)) s)"
        using fun_inv_def  s_def by blast
      then have "permute_list (twisting_permutation n) as =
          permute_list ((twisting_permutation n) \<circ> (fun_inv (twisting_permutation n))) s"
        using fun_inv_permute(2) fun_inv_permute(3) length_greater_0_conv
              length_permute_list twisting_permutation_permutes[of n "length s"]
              permute_list_compose[of "fun_inv (twisting_permutation n)" s "twisting_permutation n"]
        by (metis S permute_list_compose)
      then have "permute_list (twisting_permutation n) as =
          permute_list (id) s"
        by (metis S \<open>permute_list (twisting_permutation n) as = permute_list
            (twisting_permutation n) (permute_list (fun_inv (twisting_permutation n)) s)\<close>
            fun_inv_permute(3) length_greater_0_conv length_permute_list permute_list_compose
            twisting_permutation_permutes)
      then have "permute_list (twisting_permutation n) as = s"
        by simp
      then show ?thesis
        using s_def
        by (simp add: \<open>s \<in> S \<and> permute_list (fun_inv (twisting_permutation n)) s = as\<close>)
    qed
    then show "x \<in> twisted_partial_pullback n m l f S"
      unfolding twisted_partial_pullback_def using D
      by (smt \<open>x = a @ b @ c\<close> a_closed append.assoc append_eq_conv_conj b_closed
          c_closed cartesian_power_car_memE cartesian_power_concat(1) length_append
          list.inject local.partial_image_def twisted_partial_image_def
          twisted_partial_pullback_def twisted_partial_pullback_memI)
  qed
qed

lemma twisted_partial_pullback_is_semialgebraic:
  assumes "is_semialg_function m f"
  assumes "is_semialgebraic (n + 1 + l) S"
  shows "is_semialgebraic (n + m + l)(twisted_partial_pullback n m l f S)"
proof-
  have "(fun_inv (twisting_permutation n)) permutes {..<n + 1 + l}"
    by (simp add: fun_inv_permute(1) twisting_permutation_permutes)
  then have "is_semialgebraic (1 + n + l) (permute_list (fun_inv (twisting_permutation n)) ` S)"
    using add_gr_0 assms(2) permutation_is_semialgebraic
    by (metis add.commute)
  then have "is_semialgebraic (n + m + l)
              (partial_pullback m f (n + l) (permute_list (fun_inv (twisting_permutation n)) ` S))"
    using assms is_semialg_functionE[of m f "n + l" "(permute_list (fun_inv (twisting_permutation n)) ` S)"]
    by (metis (no_types, lifting) add.assoc add.commute)
  then have "is_semialgebraic (n + m + l)
              ((tw m n) `(partial_pullback m f (n + l) (permute_list (fun_inv (twisting_permutation n)) ` S)))"
    unfolding tw_def
    using  tp_1_permutes'[of n m l] assms permutation_is_semialgebraic[of "n + m + l"
          "partial_pullback m f (n + l) (permute_list (fun_inv (twisting_permutation n)) ` S)"
          "tp_1 n m" ]
    by blast
  then show ?thesis
    using twisted_partial_pullback_factored assms(1) assms(2)
      is_semialg_function_closed is_semialgebraic_closed
    by presburger
qed

definition augment where
"augment n x = take n x @ take n x @ drop n x"

lemma augment_closed:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
  shows "augment n x \<in> carrier (Q\<^sub>p\<^bsup>n+n+ l\<^esup>)"
  apply(rule cartesian_power_car_memI)
  apply (smt ab_semigroup_add_class.add_ac(1) add.commute append_take_drop_id
    assms augment_def cartesian_power_car_memE cartesian_power_drop length_append)
  using assms cartesian_power_car_memE'' unfolding augment_def
  by (metis (no_types, opaque_lifting) append_take_drop_id cartesian_power_concat(2) nat_le_iff_add take_closed)

lemma tuple_partial_image_factor:
  assumes "is_function_tuple Q\<^sub>p m fs"
  assumes "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  assumes "length fs = n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
  shows "tuple_partial_image m (fs@[f]) x = twisted_partial_image n m f (tuple_partial_image m fs (augment m x))"
proof-
  obtain a where a_def: "a = take m x"
    by blast
  obtain b where b_def: "b = drop m x"
    by blast
  have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using a_def assms(4) le_add1 take_closed
    by (meson dual_order.trans)
  have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
    using assms(4) b_def cartesian_power_drop
    by (metis (no_types, lifting))
  have A: "(augment m x) = a @ (a @ b)"
    using a_def augment_def b_def
    by blast
  have 0: "tuple_partial_image m fs (augment m x) = ((function_tuple_eval Q\<^sub>p m fs) a) @ a @ b"
    using A a_closed b_closed tuple_partial_image_eq[of a m "a@b" "m + l" "augment m x" fs]
      cartesian_power_concat(1)
    by blast
  have 1: "tuple_partial_image m (fs@[f]) x = ((function_tuple_eval Q\<^sub>p m fs a) @ [f a])@b"
    using 0 tuple_partial_image_eq[of a m b l x "fs@[f]"] unfolding function_tuple_eval_def
    by (metis (no_types, lifting) a_closed a_def append_take_drop_id b_closed b_def
        list.simps(8) list.simps(9) map_append)
  have 2: "tuple_partial_image m (fs@[f]) x = (function_tuple_eval Q\<^sub>p m fs a) @ ((f a)#b)"
    using 1
    by (metis (no_types, lifting) append_Cons append_Nil2 append_eq_append_conv2 same_append_eq)
  have 3: "tuple_partial_image m fs x = (function_tuple_eval Q\<^sub>p m fs a) @ b"
    using a_def b_def 2 tuple_partial_image_eq[of a m b l x fs ] assms  tuple_partial_image_def
    by blast
  have 4: "twisted_partial_image n m f (tuple_partial_image m fs (augment m x)) =
                  (function_tuple_eval Q\<^sub>p m fs a) @ ((f a)#b)"
    using twisted_partial_image_eq[of _ n _ m _ l] 0  assms(1) assms(3) b_closed
      local.a_closed local.function_tuple_eval_closed by blast
  show ?thesis using 2 4
    by presburger
qed

definition diagonalize where
"diagonalize n m S = S \<inter> cartesian_product (\<Delta> n) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"

lemma diagaonlize_is_semiaglebraic:
  assumes "is_semialgebraic (n + n + m) S"
  shows "is_semialgebraic (n + n + m) (diagonalize n m S)"
proof(cases "m = 0")
  case True
  then have 0: "carrier (Q\<^sub>p\<^bsup>m\<^esup>) = {[]}"
    unfolding  cartesian_power_def
    by simp
  have 1: "\<Delta> n \<subseteq> carrier (Q\<^sub>p\<^bsup>n+n\<^esup>)"
    using Qp.cring_axioms assms diagonalE(2)
    by blast
  then have "cartesian_product (\<Delta> n) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) = \<Delta> n"
    using 0 cartesian_product_empty_right[of "\<Delta> n" Q\<^sub>p "n + n"  "carrier (Q\<^sub>p\<^bsup>m\<^esup>)"]
    by linarith
  then have "diagonalize n m S = S \<inter> (\<Delta> n)"
    using diagonalize_def
    by presburger
  then show ?thesis
    using intersection_is_semialg True assms diag_is_semialgebraic
    by auto
next
  case False
  have "is_semialgebraic (n + n + m) (cartesian_product (\<Delta> n) (carrier (Q\<^sub>p\<^bsup>m\<^esup>)))"
    using carrier_is_semialgebraic[of m]
          cartesian_product_is_semialgebraic[of "n + n" "\<Delta> n" m "carrier (Q\<^sub>p\<^bsup>m\<^esup>)"]
          diag_is_semialgebraic[of n]  False
    by blast
  then show ?thesis
    using intersection_is_semialg assms(1) diagonalize_def
    by presburger
qed

lemma list_segment_take:
  assumes "length a \<ge>n"
  shows "list_segment 0 n a = take n a"
proof-
  have 0: "length (list_segment 0 n a) = length (take n a)"
    using assms unfolding list_segment_def
    by (metis (no_types, lifting) Groups.add_ac(2) add_diff_cancel_left'
        append_take_drop_id le_Suc_ex length_append length_drop length_map map_nth)
  have "\<And>i. i < n \<Longrightarrow> list_segment 0 n a !i = take n a ! i"
    unfolding list_segment_def using assms
    by (metis add.left_neutral diff_zero nth_map_upt nth_take)
  then show ?thesis using 0
    by (metis assms diff_zero le0 list_segment_length nth_equalityI)
qed

lemma augment_inverse_is_semialgebraic:
  assumes "is_semialgebraic (n+n+l) S"
  shows "is_semialgebraic (n+l) ((augment n -` S) \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>))"
proof-
  obtain Ps where Ps_def: "Ps = (var_list_segment 0 n)"
    by blast
  obtain Qs where Qs_def: "Qs = (var_list_segment n (n+l))"
    by blast
  obtain Fs where Fs_def: "Fs = Ps@Ps@Qs"
    by blast
  have 0: "is_poly_tuple (n+l) Ps"
    by (simp add: Ps_def var_list_segment_is_poly_tuple)
  have 1: "is_poly_tuple (n+l) Qs"
    by (simp add: Qs_def var_list_segment_is_poly_tuple)
  have 2: "is_poly_tuple (n+l) (Ps@Qs)"
    using Qp_is_poly_tuple_append[of "n+l" Ps Qs]
    by (metis (no_types, opaque_lifting) "0" "1" add.commute)
  have "is_poly_tuple (n+l) Fs"
    using 0 2 Qp_is_poly_tuple_append[of "n + l" Ps "Ps@Qs"] Fs_def assms
    by blast
  have 3: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) \<Longrightarrow> augment n x = poly_map (n + l) Fs x"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
    have 30: "poly_map (n+l) Ps x = take n x"
      using Ps_def  map_by_var_list_segment[of x "n + l" n 0]
            list_segment_take[of n x] cartesian_power_car_memE[of x Q\<^sub>p "n+l"]
      by (simp add: A)
    have 31: "poly_map (n + l) Qs x = drop n x"
      using Qs_def map_by_var_list_segment_to_length[of x "n + l" n] A le_add1
      by blast
    have 32: "poly_map (n + l) (Ps@Qs) x = take n x @ drop n x"
      using poly_map_append[of x "n+l" Ps Qs ]
      by (metis "30" "31" A append_take_drop_id)
    show "augment n x = poly_map (n + l) Fs x"
      using 30 32 poly_map_append
      by (metis A Fs_def poly_map_append augment_def)
  qed
  have 4: "(augment n -` S) \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) = poly_tuple_pullback (n + l) S Fs"
  proof
    show "augment n -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>) \<subseteq> poly_tuple_pullback (n + l) S Fs"
    proof fix x assume A: "x \<in> augment n -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
      then have 40: "augment n x \<in> S"
        by blast
      have 41: "augment n x \<in> carrier (Q\<^sub>p\<^bsup>n+n+ l\<^esup>)"
        using 40 assms unfolding augment_def
        using is_semialgebraic_closed
        by blast
      have "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
      proof-
        have "take n x @ x \<in> carrier (Q\<^sub>p\<^bsup>n+n+ l\<^esup>)"
          using augment_def A
          by (metis "41" append_take_drop_id)
        then have 0: "drop n (take n x @ x) \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
          by (metis (no_types, lifting) add.assoc cartesian_power_drop)
        have "drop n (take n x @ x) = x"
        proof-
          have "length x \<ge> n"
            using A
            by (metis IntD2 cartesian_power_car_memE le_add1)
          then have "length (take n x) = n"
            by (metis add_right_cancel append_take_drop_id
                le_add_diff_inverse length_append length_drop)
          then show ?thesis
            by (metis append_eq_conv_conj)
        qed
        then show ?thesis
          using 0
          by presburger
      qed
      then show "x \<in> poly_tuple_pullback (n + l) S Fs"
        using  41 3 unfolding poly_tuple_pullback_def
        by (metis (no_types, opaque_lifting) "40" add.commute cartesian_power_car_memE evimageI evimage_def poly_map_apply)
    qed
    show "poly_tuple_pullback (n + l) S Fs \<subseteq> augment n -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
    proof fix x assume A: "x \<in> poly_tuple_pullback (n + l) S Fs"
      have "x \<in> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
        using A unfolding poly_tuple_pullback_def by blast
      then show "x \<in> augment n -` S \<inter> carrier (Q\<^sub>p\<^bsup>n+l\<^esup>)"
        using 3
        by (metis (no_types, lifting) A poly_map_apply poly_tuple_pullback_def vimage_inter_cong)
    qed
  qed
  then show ?thesis using assms pullback_is_semialg[of "n + l" Fs]
    using poly_tuple_pullback_eq_poly_map_vimage
    unfolding restrict_def evimage_def Fs_def
    by (smt "4" Ex_list_of_length Fs_def Ps_def Qs_def \<open>is_poly_tuple (n + l) Fs\<close> add.commute
        add_diff_cancel_left' append_assoc diff_zero is_semialgebraic_closed le_add2 length_append
        not_add_less1 not_gr_zero padic_fields.is_semialgebraicE padic_fields_axioms var_list_segment_length zero_le)
qed

lemma tuple_partial_pullback_is_semialg_map_tuple_induct:
  assumes "is_semialg_map_tuple m fs"
  assumes "is_semialg_function m f"
  assumes "length fs = n"
  shows "is_semialg_map_tuple m (fs@[f])"
proof(rule is_semialg_map_tupleI)
  have 0: "is_function_tuple Q\<^sub>p m fs"
    using assms is_semialg_map_tuple_def
    by blast
  show "is_function_tuple Q\<^sub>p m (fs @ [f])"
  proof(rule is_function_tupleI)
    have A0: "set (fs @ [f]) = insert f (set fs)"
      by simp
    have A1: "set fs \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
      using 0 is_function_tuple_def
      by blast
    then show "set (fs @ [f]) \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
      using assms 0
      by (metis (no_types, lifting) A0 is_semialg_function_closed list.simps(15) set_ConsD subset_code(1))
  qed
  show "\<And>k S. S \<in> semialg_sets (length (fs @ [f]) + k) \<Longrightarrow>
                 is_semialgebraic (m + k) (tuple_partial_pullback m (fs @ [f]) k S)"
  proof- fix l S
    assume A: "S \<in> semialg_sets (length (fs @ [f]) + l)"
    then have B: "S \<in> semialg_sets (n + l + 1)"
      using assms
      by (metis (no_types, lifting) add.commute add_Suc_right add_diff_cancel_left'
          append_Nil2 diff_Suc_1 length_Suc_conv length_append)
    show "is_semialgebraic (m + l) (tuple_partial_pullback m (fs @ [f]) l S)"
    proof-
      obtain S0 where S0_def: "S0 = tuple_partial_pullback m fs (l+1) S"
        by blast
      have 0: "is_semialgebraic (m + l + 1) S0"
        using B assms is_semialg_map_tupleE[of m fs "l + 1" S]
        by (metis S0_def add.assoc is_semialgebraicI)
      obtain S1 where S1_def: "S1 = twisted_partial_pullback m m l f S0"
        by blast
      then have "is_semialgebraic (m + m + l) S1"
        using S1_def assms(1) 0 twisted_partial_pullback_is_semialgebraic[of m f m l S0]
        by (simp add: assms(2))
      then have L: "is_semialgebraic (m + m + l) (diagonalize m l S1)"
        using assms  diagaonlize_is_semiaglebraic
        by blast
      have 1: "(tuple_partial_pullback m (fs @ [f]) l S)
                = (augment m -` (diagonalize m l S1)) \<inter> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
      proof
        show "tuple_partial_pullback m (fs @ [f]) l S \<subseteq>
                      augment m -` diagonalize m l S1 \<inter> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"

        proof fix x assume P0: "x \<in> tuple_partial_pullback m (fs @ [f]) l S "
          show "x \<in> augment m -` diagonalize m l S1 \<inter> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
          proof
            show "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
              using tuple_partial_pullback_closed P0
              by blast
            show "x \<in> augment m -` diagonalize m l S1"
            proof-
              obtain a where a_def: "a = take m x"
                by blast
              then have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using \<open>x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)\<close> le_add1 take_closed
                by blast
              obtain b where b_def: "b = drop m x"
                by blast
              then have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
                using \<open>x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)\<close> cartesian_power_drop
                by blast
              have x_eq: "x = a@b"
                using a_def b_def
                by (metis append_take_drop_id)
              have X0: "a @ a @ b = augment m x"
                by (metis a_def augment_def b_def)
              have "a @ a @ b \<in>  diagonalize m l S1"
              proof-
                have "length (a@a) = m + m"
                  using a_closed cartesian_power_car_memE length_append
                  by blast
                then have "take (m + m) (a @ a @ b) = a@a"
                  by (metis append.assoc append_eq_conv_conj)
                then have X00: "take (m + m) (a @ a @ b) \<in> \<Delta>  m"
                  using diagonalI[of  "a@a"] a_def a_closed
                  by (metis append_eq_conv_conj cartesian_power_car_memE)
                then have X01: "a @ a @ b \<in> cartesian_product (\<Delta> m) (carrier (Q\<^sub>p\<^bsup>l\<^esup>))"
                  using a_closed b_closed cartesian_product_memI[of "\<Delta> m" Q\<^sub>p "m+m" "carrier (Q\<^sub>p\<^bsup>l\<^esup>)" l "a @ a @ b"]
                  unfolding diagonal_def
                  by (metis (no_types, lifting) X0 \<open>x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)\<close> augment_closed cartesian_power_drop mem_Collect_eq subsetI)
                have X02: "twisted_partial_image m m f (a @ a @ b) = a @ ((f a)# b)"
                  using twisted_partial_image_eq[of a m a m b l _ f] a_closed b_closed
                  by blast
                have "a @ a @ b \<in> S1"
                proof-
                  have "twisted_partial_image m m f (a @ a @ b) \<in> S0"
                  proof-
                    have X020:"tuple_partial_image m fs (a @ ((f a)# b))
                              = (function_tuple_eval Q\<^sub>p m fs a)@[f a]@b"
                      using tuple_partial_image_eq[of a m "(f a)# b" "l + 1" _ fs]
                      by (metis (no_types, lifting) a_closed append_Cons append_eq_conv_conj
                          cartesian_power_car_memE self_append_conv2 tuple_partial_image_def)
                    have X021: "(function_tuple_eval Q\<^sub>p m fs a)@[f a]@b \<in> S"
                    proof-
                      have X0210: "(function_tuple_eval Q\<^sub>p m fs a)@[f a]@b =
                                (function_tuple_eval Q\<^sub>p m (fs@[f]) a)@b"
                        unfolding function_tuple_eval_def
                        by (metis (mono_tags, lifting) append.assoc list.simps(8) list.simps(9) map_append)
                      have X0211: "(function_tuple_eval Q\<^sub>p m (fs@[f]) a)@b =
                                tuple_partial_image m (fs @ [f]) x"
                        using x_eq tuple_partial_image_eq[of a m b l x "fs@[f]"]
                        by (simp add: a_closed b_closed)
                      have "tuple_partial_image m (fs @ [f]) x \<in> S"
                        using P0 tuple_partial_pullback_memE(2)
                        by blast
                      then show ?thesis using X0211 X0210 by presburger
                    qed
                    have X022: "tuple_partial_image m fs (twisted_partial_image m m f (a @ a @ b))
                                 = (function_tuple_eval Q\<^sub>p m fs a)@[f a]@b"
                    proof-
                      have X0220: "tuple_partial_image m fs (twisted_partial_image m m f (a @ a @ b)) =
                                    tuple_partial_image m fs (a @ ((f a)# b))"
                        using X02 by presburger
                      have X0221: "tuple_partial_image m fs (twisted_partial_image m m f (a @ a @ b)) =
                                    (function_tuple_eval Q\<^sub>p m fs a) @ ((f a)# b)"
                        using tuple_partial_image_eq
                        by (metis X02 X020 append_Cons self_append_conv2)
                      then show ?thesis
                        unfolding function_tuple_eval_def
                        by (metis X02 X020 X0221 append_same_eq)
                    qed
                    have X023: "tuple_partial_image m fs (twisted_partial_image m m f (a @ a @ b)) \<in> S"
                      using X02 X020 X021 by presburger
                    have "twisted_partial_image m m f (a @ a @ b) \<in> carrier (Q\<^sub>p\<^bsup>m + (l+1)\<^esup>)"
                    proof-
                      have "a @ ((f a)# b) \<in> carrier (Q\<^sub>p\<^bsup>m + (l+1)\<^esup>)"
                        apply(rule cartesian_power_car_memI)
                         apply (metis a_closed add.commute b_closed cartesian_power_car_memE
                            length_Cons length_append plus_1_eq_Suc)
                      proof-
                        have "f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
                          using assms(2) is_semialg_function_closed by blast
                        then have "f a \<in> carrier Q\<^sub>p"
                          using a_closed assms
                          by blast
                        then show "set (a @ f a # b) \<subseteq> carrier Q\<^sub>p"
                          using  assms a_closed b_closed
                          by (meson cartesian_power_car_memE'' cartesian_power_concat(1) cartesian_power_cons)
                      qed
                      then show ?thesis
                        using X02
                        by presburger
                    qed
                    then show ?thesis
                      using S0_def X023 tuple_partial_pullback_def[of m fs "l+1" S ]
                      by blast
                  qed
                  then show ?thesis using X02 S1_def twisted_partial_pullback_def
                    by (metis (no_types, lifting) X0 \<open>x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)\<close> augment_closed
                        drop_drop local.partial_image_def twisted_partial_image_def
                        twisted_partial_pullback_memI)
                qed
                then show ?thesis using X01 diagonalize_def[of m l S1]
                  by blast
              qed
              then show ?thesis
                by (metis X0 vimageI)
            qed
          qed
        qed
        show "augment m -` diagonalize m l S1 \<inter> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<subseteq> tuple_partial_pullback m (fs @ [f]) l S"
        proof
          fix x
          assume A: "x \<in> augment m -` diagonalize m l S1 \<inter> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
          then have X0: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
            by blast
          obtain a where a_def: "a = take m x"
            by blast
          then have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using X0 le_add1 take_closed by blast
          obtain b where b_def: "b = drop m x"
            by blast
          then have a_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>l\<^esup>)"
            using X0 cartesian_power_drop
            by blast
          have X1: "augment m x = a@a@b"
            using a_def augment_def b_def
            by blast
          have X2: "a@a@b \<in> diagonalize m l S1"
            using A X1
            by (metis Int_iff vimage_eq)
          have X3: "a@a@b \<in>  S1"
            using X2 diagonalize_def
            by blast
          have X4: "twisted_partial_image m m f (a@a@b) \<in> S0"
            using X3 S1_def twisted_partial_pullback_memE(2)
            by blast
          have X5: "a@((f a)#b) \<in> S0"
            using X4 twisted_partial_image_eq[of a m a m b l _ f]
            by (metis X0 a_closed a_def le_add1 take_closed)
          have X6: "tuple_partial_image m fs (a@((f a)#b)) \<in> S"
            using S0_def X5 tuple_partial_pullback_memE(2)
            by blast
          have X7: "((function_tuple_eval Q\<^sub>p m fs a)@((f a)#b)) \<in> S"
            using X6 using tuple_partial_image_eq
            by (metis X0 a_def append_eq_conv_conj cartesian_power_car_memE
                le_add1 take_closed tuple_partial_image_def)
          have X8: "((function_tuple_eval Q\<^sub>p m fs a)@((f a)#b)) =
                        tuple_partial_image m (fs @ [f]) x"
          proof-
            have X80: "tuple_partial_image m (fs @ [f]) x = (function_tuple_eval Q\<^sub>p m (fs@[f]) a)@b"
              using tuple_partial_image_def a_def b_def
              by blast
            then show ?thesis unfolding function_tuple_eval_def
              by (metis (no_types, lifting) append_Cons append_eq_append_conv2 list.simps(9) map_append self_append_conv2)
          qed
          show "x \<in> tuple_partial_pullback m (fs @ [f]) l S"
            using X8 X7 tuple_partial_pullback_def
            by (metis X0 \<open>is_function_tuple Q\<^sub>p m (fs @ [f])\<close>
                tuple_partial_image_def tuple_partial_pullback_memI)
        qed
      qed
      then show ?thesis
        using augment_inverse_is_semialgebraic
        by (simp add: L)
    qed
  qed
qed

lemma singleton_tuple_partial_pullback_is_semialg_map_tuple:
  assumes "is_semialg_function_tuple m fs"
  assumes "length fs = 1"
  shows "is_semialg_map_tuple m fs"
proof(rule is_semialg_map_tupleI)
  show "is_function_tuple Q\<^sub>p m fs"
    by (simp add: assms(1) semialg_function_tuple_is_function_tuple)
  show "\<And>k S. S \<in> semialg_sets (length fs + k) \<Longrightarrow> is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
  proof- fix k S assume A: "S \<in> semialg_sets (length fs + k)"
    show "is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
    proof-
      obtain f where f_def: "fs = [f]"
        using assms
        by (metis One_nat_def length_0_conv length_Suc_conv)
      have 0: "is_semialg_function m f"
        using f_def assms is_semialg_function_tupleE'[of m fs f]
        by simp
      have 1: "\<And>x. tuple_partial_image m fs x = partial_image m f x"
        unfolding function_tuple_eval_def tuple_partial_image_def partial_image_def
        by (metis (no_types, lifting) append_Cons append_Nil2 append_eq_append_conv_if
            f_def list.simps(8) list.simps(9))
      have 2: "tuple_partial_pullback m fs k S = partial_pullback m f k S"
      proof
        show "tuple_partial_pullback m fs k S \<subseteq> partial_pullback m f k S"
            using 1 unfolding tuple_partial_pullback_def  partial_pullback_def evimage_def
            by (metis (no_types, lifting) set_eq_subset vimage_inter_cong)
        show "partial_pullback m f k S \<subseteq> tuple_partial_pullback m fs k S"
          using 1 unfolding tuple_partial_pullback_def  partial_pullback_def evimage_def
            by blast
      qed
      then show ?thesis
        by (metis "0" A assms(2) is_semialg_functionE is_semialgebraicI)
    qed
  qed
qed

lemma empty_tuple_partial_pullback_is_semialg_map_tuple:
  assumes "is_semialg_function_tuple m fs"
  assumes "length fs = 0"
  shows "is_semialg_map_tuple m fs"
  apply(rule is_semialg_map_tupleI)
  using assms(1) semialg_function_tuple_is_function_tuple apply blast
proof-
  fix k S assume A: "S \<in> semialg_sets (length fs + k)"
  then have 0: "is_semialgebraic k S"
    by (metis add.left_neutral assms(2) is_semialgebraicI)
  have 1: "tuple_partial_pullback m fs k S = cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) S"
  proof
    have 1: "\<And>x. function_tuple_eval Q\<^sub>p m fs (take m x) = []"
      using assms unfolding function_tuple_eval_def
      by blast
    show "tuple_partial_pullback m fs k S \<subseteq> cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) S"
      apply(rule subsetI) apply(rule cartesian_product_memI[of "carrier (Q\<^sub>p\<^bsup>m\<^esup>)" Q\<^sub>p m S k])
      apply blast using 0 is_semialgebraic_closed apply blast
      using  0 assms unfolding 1 tuple_partial_pullback_def tuple_partial_image_def
      apply (meson IntD2 le_add1 take_closed)
     by (metis append_Nil evimageD evimage_def)
   have 2: "cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
     using is_semialgebraic_closed[of k S] 0 assms cartesian_product_closed[of "carrier (Q\<^sub>p\<^bsup>m\<^esup>)" Q\<^sub>p m S k]  by blast
   show "cartesian_product (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) S \<subseteq> tuple_partial_pullback m fs k S"
     apply(rule subsetI)  apply(rule tuple_partial_pullback_memI)
     using 2 apply blast
     using assms semialg_function_tuple_is_function_tuple apply blast
     unfolding 1
     by (metis carrier_is_semialgebraic cartesian_product_memE(2) is_semialgebraic_closed self_append_conv2)
  qed
  show "is_semialgebraic (m + k) (tuple_partial_pullback m fs k S)"
    unfolding 1
    using "0" car_times_semialg_is_semialg by blast
qed

lemma tuple_partial_pullback_is_semialg_map_tuple:
  assumes "is_semialg_function_tuple m fs"
  shows "is_semialg_map_tuple m fs"
proof-
  have "\<And>n fs. is_semialg_function_tuple m fs \<and> length fs = n \<Longrightarrow> is_semialg_map_tuple m fs"
  proof- fix n
    show " \<And> fs. is_semialg_function_tuple m fs \<and> length fs = n \<Longrightarrow> is_semialg_map_tuple m fs"
      apply(induction n)
      using singleton_tuple_partial_pullback_is_semialg_map_tuple empty_tuple_partial_pullback_is_semialg_map_tuple apply blast
    proof-
      fix n fs
      assume IH: "(\<And>fs. is_semialg_function_tuple m fs \<and> length fs = n \<Longrightarrow> is_semialg_map_tuple m fs)"
      assume A: "is_semialg_function_tuple m fs \<and> length fs = Suc n"
      then obtain gs f where gs_f_def: "fs = gs@[f]"
        by (metis length_Suc_conv list.discI rev_exhaust)
      have gs_length: "length gs = n"
        using gs_f_def
        by (metis A length_append_singleton nat.inject)
      have 0: "set gs \<subseteq> set fs"
        by (simp add: gs_f_def subsetI)
      have 1: "is_semialg_function_tuple m gs"
        apply(rule is_semialg_function_tupleI)
        using 0 A gs_f_def is_semialg_function_tupleE'[of m fs]
        by blast
      then have 2: "is_semialg_map_tuple m gs"
        using IH gs_length
        by blast
      have 3: "is_semialg_function m f"
        using gs_f_def A
        by (metis gs_length is_semialg_function_tupleE lessI nth_append_length)
      then show "is_semialg_map_tuple m fs"
        using assms 2 gs_f_def tuple_partial_pullback_is_semialg_map_tuple_induct
        by blast
    qed
  qed
  then show ?thesis
    using assms by blast
qed


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Semialgebraic Functions are Closed under Composition with Semialgebraic Tuples\<close>
      (********************************************************************************************)
      (********************************************************************************************)

lemma function_tuple_comp_partial_pullback:
  assumes "is_semialg_function_tuple m fs"
  assumes "length fs = n"
  assumes "is_semialg_function n f"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
  shows "partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S =
             tuple_partial_pullback m fs k (partial_pullback n f k S)"
proof-
  have 0: "\<And>x. partial_image m (function_tuple_comp Q\<^sub>p fs f) x =
        partial_image n f (tuple_partial_image m fs x)"
    unfolding partial_image_def function_tuple_comp_def tuple_partial_image_def
    using comp_apply[of f "function_tuple_eval Q\<^sub>p 0 fs"]
    unfolding function_tuple_eval_def
  proof -
    fix x :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list"
    assume a1: "\<And>x. (f \<circ> (\<lambda>x. map (\<lambda>f. f x) fs)) x = f (map (\<lambda>f. f x) fs)"
    have f2: "\<forall>f rs. drop n (map f fs @ (rs::((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list)) = rs"
      by (simp add: assms(2))
    have "\<forall>f rs. take n (map f fs @ (rs::((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list)) = map f fs"
      by (simp add: assms(2))
    then show "(f \<circ> (\<lambda>rs. map (\<lambda>f. f rs) fs)) (take m x) # drop m x =
              f (take n (map (\<lambda>f. f (take m x)) fs @ drop m x)) # drop n (map (\<lambda>f. f (take m x)) fs @ drop m x)"
      using f2 a1 by presburger
  qed
  show "partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S =
              tuple_partial_pullback m fs k (partial_pullback n f k S)"
  proof
    show "partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S \<subseteq> tuple_partial_pullback m fs k (partial_pullback n f k S)"
    proof fix x assume A: "x \<in> partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S"
      then have 1: "partial_image m (function_tuple_comp Q\<^sub>p fs f) x \<in> S"
        using partial_pullback_memE(2) by blast
      have 2: "  partial_image n f (tuple_partial_image m fs x) \<in> S"
        using 0 1
        by presburger
      have 3: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
        using A assms
        by (metis partial_pullback_memE(1))
      have 4: "tuple_partial_image m fs x \<in> partial_pullback n f k S"
        apply(rule partial_pullback_memI)
         apply (metis "0" "3" add_cancel_left_left assms(1) assms(2) cartesian_power_drop drop0
            list.inject local.partial_image_def not_gr_zero semialg_function_tuple_is_function_tuple
            tuple_partial_image_closed)
        by (metis "2" local.partial_image_def)
      show " x \<in> tuple_partial_pullback m fs k (partial_pullback n f k S)"
        apply(rule tuple_partial_pullback_memI)
        apply (simp add: "3")
        using assms(1) semialg_function_tuple_is_function_tuple apply blast
        by (metis "4" tuple_partial_image_def)
    qed
    show " tuple_partial_pullback m fs k (partial_pullback n f k S) \<subseteq> partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S"
    proof fix x assume A: "x \<in> tuple_partial_pullback m fs k (partial_pullback n f k S)"
      show "x \<in> partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S "
      proof-
        have "partial_image n f (tuple_partial_image m fs x) \<in> S"
          using A partial_pullback_memE(2) tuple_partial_pullback_memE(2)
          by blast
        show ?thesis
          apply(rule partial_pullback_memI)
           apply (meson A subset_eq tuple_partial_pullback_closed)
          by (metis "0" \<open>local.partial_image n f (tuple_partial_image m fs x) \<in> S\<close>
              local.partial_image_def)
      qed
    qed
  qed
qed

lemma semialg_function_tuple_comp:
  assumes "is_semialg_function_tuple m fs"
  assumes "length fs = n"
  assumes "is_semialg_function n f"
  shows "is_semialg_function m (function_tuple_comp Q\<^sub>p fs f)"
proof(rule is_semialg_functionI)
  show "function_tuple_comp Q\<^sub>p fs f \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using function_tuple_comp_closed[of f Q\<^sub>p n fs] assms(1) assms(2)
      assms(3) is_semialg_function_closed semialg_function_tuple_is_function_tuple
    by blast
  show "\<And>k S. S \<in> semialg_sets (1 + k) \<Longrightarrow> is_semialgebraic (m + k) (partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S)"
  proof- fix k S
    assume A0: "S \<in> semialg_sets (1 + k)"
    show "is_semialgebraic (m + k) (partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S)"
    proof-
      have 0: "partial_pullback m (function_tuple_comp Q\<^sub>p fs f) k S =
             tuple_partial_pullback m fs k (partial_pullback n f k S)"
        using  function_tuple_comp_partial_pullback[of m fs n f S k] assms
            \<open>S \<in> semialg_sets (1 + k)\<close> is_semialgebraicI is_semialgebraic_closed
        by blast
      have 1: "is_semialgebraic (n + k) (partial_pullback n f k S)"
        using assms A0 is_semialg_functionE is_semialgebraicI
        by blast
      have 2: "is_semialgebraic (m + k) (tuple_partial_pullback m fs k (partial_pullback n f k S))"
        using 1 0 assms tuple_partial_pullback_is_semialg_map_tuple[of m fs]
          is_semialg_map_tupleE[of m fs k "partial_pullback n f k S"]
        by blast
      then show ?thesis
        using 0
        by simp
    qed
  qed
qed


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Algebraic Operations on Semialgebraic Functions\<close>
      (********************************************************************************************)
      (********************************************************************************************)


text\<open>Defining the set of extensional semialgebraic functions\<close>

definition Qp_add_fun where
"Qp_add_fun xs = xs!0 \<oplus>\<^bsub>Q\<^sub>p\<^esub> xs!1"

definition Qp_mult_fun where
"Qp_mult_fun xs = xs!0 \<otimes> xs!1"

text\<open>Inversion function on first coordinates of Qp tuples. Arbitrarily redefined at 0 to map to 0\<close>

definition Qp_invert where
"Qp_invert xs = (if ((xs!0) = \<zero>) then \<zero> else (inv (xs!0)))"

text\<open>Addition is semialgebraic\<close>

lemma addition_is_semialg:
"is_semialg_function 2 Qp_add_fun"
proof-
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>) \<Longrightarrow> Qp_add_fun x = Qp_ev (pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1) x"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
    have "Qp_ev (pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1) x = (Qp_ev (pvar Q\<^sub>p 0) x) \<oplus>\<^bsub>Q\<^sub>p\<^esub> (Qp_ev (pvar Q\<^sub>p 1) x)"
      by (metis A One_nat_def eval_at_point_add  pvar_closed less_Suc_eq numeral_2_eq_2)
    then show " Qp_add_fun x = Qp_ev (pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1) x"
      by (metis A Qp_add_fun_def add_vars_def add_vars_rep one_less_numeral_iff
          pos2 semiring_norm(76))
  qed
  then have 1: "restrict Qp_add_fun (carrier (Q\<^sub>p\<^bsup>2\<^esup>)) =
      restrict (Qp_ev (pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1)) (carrier (Q\<^sub>p\<^bsup>2\<^esup>))"
    by (meson restrict_ext)
  have "is_semialg_function 2 (Qp_ev (pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1))"
    using poly_is_semialg[of "pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1"]
    by (meson MP.add.m_closed local.pvar_closed one_less_numeral_iff pos2 semiring_norm(76))
  then show ?thesis
    using 1 semialg_function_on_carrier[of 2 "Qp_add_fun" "Qp_ev (pvar Q\<^sub>p 0 \<oplus>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1)"]
          semialg_function_on_carrier
    by presburger
qed

text\<open>Multiplication is semialgebraic:\<close>

lemma multiplication_is_semialg:
"is_semialg_function 2 Qp_mult_fun"
proof-
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>) \<Longrightarrow> Qp_mult_fun x = Qp_ev (pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1) x"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>2\<^esup>)"
    have "Qp_ev (pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1) x =
                (Qp_ev (pvar Q\<^sub>p 0) x) \<otimes> (Qp_ev (pvar Q\<^sub>p 1) x)"
      by (metis A One_nat_def eval_at_point_mult pvar_closed less_Suc_eq numeral_2_eq_2)
    then show " Qp_mult_fun x = Qp_ev (pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1) x"
      by (metis A Qp_mult_fun_def mult_vars_def mult_vars_rep
          one_less_numeral_iff pos2 semiring_norm(76))
  qed
  then have 1: "restrict Qp_mult_fun (carrier (Q\<^sub>p\<^bsup>2\<^esup>)) =
      restrict (Qp_ev (pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1)) (carrier (Q\<^sub>p\<^bsup>2\<^esup>))"
    by (meson restrict_ext)
  have "is_semialg_function 2 (Qp_ev (pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1))"
    using poly_is_semialg[of "pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1"]
    by (meson MP.m_closed local.pvar_closed one_less_numeral_iff pos2 semiring_norm(76))
  thus ?thesis
    using 1 semialg_function_on_carrier[of 2 "Qp_mult_fun" "Qp_ev (pvar Q\<^sub>p 0 \<otimes>\<^bsub>Q\<^sub>p[\<X>\<^bsub>2\<^esub>]\<^esub> pvar Q\<^sub>p 1)"]
          semialg_function_on_carrier
    by presburger
qed

text\<open>Inversion is semialgebraic:\<close>

lemma(in field) field_nat_pow_inv:
  assumes "a \<in> carrier R"
  assumes "a \<noteq> \<zero>"
  shows "inv (a [^] (n::nat)) = (inv a) [^] (n :: nat)"
  apply(induction n)
  using inv_one local.nat_pow_0 apply presburger
  using assms nat_pow_of_inv
  by (metis Units_one_closed field_inv(2) field_inv(3) unit_factor)

lemma Qp_invert_basic_semialg:
  assumes "is_basic_semialg (1 + k)  S"
  shows "is_semialgebraic (1 + k) (partial_pullback 1 Qp_invert k S)"
proof-
  obtain P n where P_n_def: "(n::nat) \<noteq> 0 \<and> P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1+k\<^esub>]) \<and> S = basic_semialg_set (1+k) n P \<and> P \<in> carrier (Q\<^sub>p[\<X>\<^bsub>1+k\<^esub>])"
    using assms is_basic_semialg_def
    by meson
  obtain d::nat where d_def: "d =  deg (coord_ring Q\<^sub>p k) (to_univ_poly (Suc k) 0 P)"
    by auto
  obtain l where l_def: "l =  ((- d) mod n)"
    by blast
  have 10: "n > 0"
    using P_n_def
    by blast
  have 11: "l \<ge> 0"
    using 10 by (simp add: l_def)
  have 1: "(l + d) mod n = 0"
    by (metis add_eq_0_iff equation_minus_iff l_def mod_0 mod_add_cong mod_minus_eq zmod_int)
  then obtain m::int where m_def: "(l + int d) = m * int n"
    using d_def l_def
    by (metis mult_of_nat_commute zmod_eq_0D)
  with 10 have \<open>m = (l + d) div n\<close>
    by simp
  with 10 11 have 2: "m \<ge> 0"
    by (simp add: div_int_pos_iff)
  obtain N where N_def: "N = m*n"
    by blast
  from 11 have 3: "N \<ge> d"
    by (simp add: N_def flip: m_def)
  have 4: "deg (coord_ring Q\<^sub>p k) (to_univ_poly (Suc k) 0 P) \<le> nat N"
    using d_def N_def 3
    by linarith
  have 5: " P \<in> carrier (coord_ring Q\<^sub>p (Suc k))"
    by (metis P_n_def  plus_1_eq_Suc)
  have 6: " \<exists>q\<in>carrier (coord_ring Q\<^sub>p (Suc k)).
       \<forall>x\<in>carrier Q\<^sub>p - {\<zero>}. \<forall>a\<in>carrier (Q\<^sub>p\<^bsup>k\<^esup>). Qp_ev q (insert_at_index a x 0) = (x[^]nat N) \<otimes> Qp_ev P (insert_at_index a (inv x) 0)"
    using 3 4 d_def to_univ_poly_one_over_poly''[of 0 k P "nat N"] "5"  Qp.field_axioms
    by blast
  obtain q where q_def: "q \<in> carrier (coord_ring Q\<^sub>p (Suc k)) \<and> ( \<forall> x \<in> carrier Q\<^sub>p - {\<zero>}. ( \<forall> a \<in>  carrier (Q\<^sub>p\<^bsup>k\<^esup>).
        eval_at_point Q\<^sub>p (insert_at_index a x 0) q =  (x[^] (nat N)) \<otimes> (eval_at_point Q\<^sub>p (insert_at_index a (inv x) 0) P)))"
    using 6
    by blast
  obtain T where T_def: "T = basic_semialg_set (1+k) n q"
    by auto
  have "is_basic_semialg (1 + k) T"
  proof-
    have "q \<in> carrier ( Q\<^sub>p[\<X>\<^bsub>Suc k\<^esub>])"
      using q_def
      by presburger
    then show ?thesis
      using T_def is_basic_semialg_def
      by (metis P_n_def plus_1_eq_Suc)
  qed
  then have T_semialg: "is_semialgebraic (1+k) T"
    using T_def basic_semialg_is_semialg[of "1+k" T] is_semialgebraicI
    by blast
  obtain Nz where Nz_def: "Nz = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs!0 \<noteq> \<zero>}"
    by blast
  have Nz_semialg: "is_semialgebraic (1+k) Nz"
  proof-
    obtain Nzc where Nzc_def: "Nzc = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs!0 = \<zero>}"
      by blast
    have 0: "Nzc = zero_set Q\<^sub>p (Suc k) (pvar Q\<^sub>p 0)"
      unfolding zero_set_def
      using Nzc_def
      by (metis (no_types, lifting) Collect_cong eval_pvar zero_less_Suc)
    have 1: "is_algebraic Q\<^sub>p (1+k)  Nzc"
      using 0 pvar_closed[of ]
      by (metis is_algebraicI' plus_1_eq_Suc zero_less_Suc)
    then have 2: "is_semialgebraic  (1+k) Nzc"
      using is_algebraic_imp_is_semialg by blast
    have 3: "Nz = carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>) - Nzc"
      using Nz_def Nzc_def
      by blast
    then show ?thesis
      using 2
      by (simp add: complement_is_semialg)
  qed
  have 7: "(partial_pullback 1 Qp_invert k S) \<inter> Nz = T \<inter> Nz"
  proof
    show "partial_pullback 1 Qp_invert k S \<inter> Nz \<subseteq> T \<inter> Nz"
    proof fix c assume A: "c \<in> partial_pullback 1 Qp_invert k S \<inter> Nz"
      show "c  \<in> T \<inter> Nz"
      proof-
        have c_closed: "c \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
          using A partial_pullback_closed[of 1  Qp_invert  k S]
          by blast
        obtain x a where xa_def: "c = (x#a)"
          using c_closed
          by (metis Suc_eq_plus1 add.commute cartesian_power_car_memE length_Suc_conv)
        have x_closed: "x \<in> carrier Q\<^sub>p"
          using xa_def  c_closed
          by (metis (no_types, lifting) append_Cons cartesian_power_decomp
              list.inject Qp.to_R1_to_R Qp.to_R_pow_closed)
        have a_closed: "a \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
          using  xa_def c_closed
          by (metis One_nat_def cartesian_power_drop drop0 drop_Suc_Cons)
        have 0: "c \<in> Nz"
          using A by blast
        then have "x \<noteq> \<zero>"
          using Nz_def xa_def
          by (metis (mono_tags, lifting) mem_Collect_eq nth_Cons_0)
        have 1: "Qp_invert [x] = inv x"
          unfolding Qp_invert_def
          by (metis \<open>x \<noteq> \<zero>\<close> nth_Cons_0)
        have 2: "partial_image 1 Qp_invert c \<in> S"
          using A partial_pullback_memE[of c 1 "Qp_invert" k S]
          by blast
        have 3: "inv x # a  \<in> S"
        proof-
          have 30: "[x] = take 1 c"
            by (simp add: xa_def)
          have 31: "a = drop 1 c"
            by (simp add: xa_def)
          show ?thesis
            using 1 30 31 partial_image_def[of 1 "Qp_invert" c] xa_def  "2"
            by metis
        qed
        obtain y where y_def: "y \<in> carrier Q\<^sub>p \<and> eval_at_point Q\<^sub>p (inv x # a) P = y [^] n"
          using 3 P_n_def basic_semialg_set_memE(2)
          by blast
        then have 4: "x [^] (nat N) \<otimes> eval_at_point Q\<^sub>p (inv x # a) P
                      = x [^] (nat N) \<otimes> y [^] n"
          by presburger
        have 5: "x [^] (nat N) \<otimes> y [^] n = ((x[^]m)\<otimes>y)[^]n"
        proof-
          have 50: "x [^] (N) \<otimes> y [^] n = x [^] (m*n) \<otimes> y [^] n"
            using N_def by blast
          have 51: "x [^] (m*n) = (x[^]m)[^]n"
            using Qp_int_nat_pow_pow \<open>x \<noteq> \<zero>\<close> not_nonzero_Qp x_closed
            by metis
          have 52: "x [^] (m*n)\<otimes> y [^] n = ((x[^]m) \<otimes> y) [^] n"
          proof-
            have 0: "x [^] (m*n)\<otimes> y [^] n= (x[^]m)[^]n \<otimes> (y[^] n)"
              using "51" by presburger
            have 1: "(x[^]m)[^]n \<otimes> (y[^] n) = ((x[^]m) \<otimes> y) [^] n"
              apply(induction n)
              using Qp.nat_pow_0 Qp.one_closed Qp.r_one apply presburger
              using x_closed y_def
              by (metis Qp.nat_pow_distrib Qp.nonzero_closed Qp_int_pow_nonzero \<open>x \<noteq> \<zero>\<close> not_nonzero_Qp)
            then show ?thesis
              using "0" by blast
          qed
          have 53: "x [^] N = x [^] (nat N)"
          proof-
            from 11 m_def N_def [symmetric] have "N \<ge> 0"
              by simp
            then show ?thesis
               by (metis pow_nat)
          qed
          then show ?thesis
            using 50 52
            by presburger
        qed
        have 6: "x [^] (nat N) \<otimes> eval_at_point Q\<^sub>p (inv x # a) P = ((x[^]m)\<otimes>y)[^]n"
          using "4" "5"
          by blast
        have 7: "eval_at_point Q\<^sub>p c q = ((x[^]m)\<otimes>y)[^]n"
        proof-
          have 70: "(insert_at_index a (inv x) 0) = inv x # a"
            using insert_at_index.simps
            by (metis (no_types, lifting) append_eq_append_conv2 append_same_eq append_take_drop_id drop0 same_append_eq)
          have 71: "(insert_at_index a x) 0 =  x # a"
            by simp
          then show ?thesis using 6 q_def
            by (metis "70" DiffI \<open>x \<noteq> \<zero>\<close> a_closed empty_iff insert_iff x_closed xa_def)
        qed
        have 8: "(x[^]m)\<otimes>y \<in> carrier Q\<^sub>p"
        proof-
          have 80: "x[^]m \<in> carrier Q\<^sub>p"
            using  \<open>x \<noteq> \<zero>\<close> x_closed Qp_int_pow_nonzero[of x m] unfolding nonzero_def
            by blast
          then show ?thesis
            using y_def by blast
        qed
        then have "c \<in> T"
          using T_def basic_semialg_set_def "7" c_closed by blast
        then show ?thesis
          by (simp add: \<open>c \<in> T\<close> "0")
      qed
    qed
    show "T \<inter> Nz \<subseteq> partial_pullback 1 Qp_invert k S \<inter> Nz"
    proof fix x assume A: "x \<in> T \<inter> Nz"
      show " x \<in> partial_pullback 1 Qp_invert k S \<inter> Nz "
      proof-
        have " x \<in> partial_pullback 1 Qp_invert k S"
        proof(rule partial_pullback_memI)
          show x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
            using T_def A
            by (meson IntD1 basic_semialg_set_memE(1))
          show "Qp_invert (take 1 x) # drop 1 x \<in> S"
          proof-
            have 00: "x!0  \<noteq> \<zero>"
              using A Nz_def
              by blast
            then have 0: "Qp_invert (take 1 x) # drop 1 x = inv (x!0) # drop 1 x"
              unfolding Qp_invert_def
              by (smt One_nat_def lessI nth_take)
            have "drop 1 x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
              using \<open>x \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)\<close> cartesian_power_drop by blast
            obtain a where a_def: "a = (x!0)"
              by blast
            have a_closed: "a \<in> carrier Q\<^sub>p"
              using 00 a_def A Nz_def cartesian_power_car_memE'[of x Q\<^sub>p "Suc k" 0] inv_in_frac(1)
              by blast
            have a_nz: "a \<noteq> \<zero>"
              using a_def Nz_def  A
              by blast
            obtain b where b_def: "b = drop 1 x"
              by blast
            have b_closed: "b \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
              using b_def A Nz_def  \<open>drop 1 x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)\<close>
              by blast
            have abx: "x = a#b"
              using a_def b_def x_closed
              by (metis (no_types, lifting) One_nat_def append_Cons append_Nil
                  append_eq_conv_conj cartesian_power_car_memE cartesian_power_decomp
                  lessI nth_take Qp.to_R1_to_R)
            have 1: "Qp_invert (take 1 x) # drop 1 x = (inv a)#b"
              using "0" a_def b_def
              by blast
            have 22: "eval_at_point Q\<^sub>p (insert_at_index b a 0) q =
                (a[^] (nat N)) \<otimes> (eval_at_point Q\<^sub>p (insert_at_index b (inv a) 0) P)"
              using q_def a_closed a_nz b_closed
              by blast
            obtain c where c_def: "c \<in> carrier Q\<^sub>p \<and> Qp_ev q x = (c[^]n)"
              using  A T_def unfolding basic_semialg_set_def
              by blast
            obtain c' where c'_def: "c' = (inv a)[^]m  \<otimes>  c"
              by blast
            have c'_closed: "c' \<in> carrier Q\<^sub>p"
              using c_def a_def a_closed a_nz Qp_int_pow_nonzero nonzero_def
                 c'_def inv_in_frac(3) Qp.m_closed Qp.nonzero_closed by presburger
            have 3: "(eval_at_point Q\<^sub>p ((inv a) # b) P) = (c'[^]n)"
            proof-
              have 30: "x = insert_at_index b a 0"
                using abx
                by simp
              have 31: "(c[^]n) =
                (a[^] (nat N)) \<otimes> (eval_at_point Q\<^sub>p (insert_at_index b (inv a) 0) P)"
                using 22 30 c_def
                by blast
              have 32: "insert_at_index b (inv a) 0 = (inv a) # b"
                using insert_at_index.simps
                by (metis drop0 self_append_conv2 take0)
              have 33: "(c[^]n) =
                (a[^] (nat N)) \<otimes> (eval_at_point Q\<^sub>p ((inv a) # b) P)"
               using "31" "32" by presburger
              have 34: "(inv a) # b \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
                apply(rule cartesian_power_car_memI'')
                 apply (metis b_closed cartesian_power_car_memE length_Suc_conv plus_1_eq_Suc)
                using a_closed a_nz b_closed
                apply (metis One_nat_def inv_in_frac(1) take0 take_Suc_Cons Qp.to_R1_closed)
                by (metis abx b_closed b_def drop_Cons' not_Cons_self2)
              have 35: "(eval_at_point Q\<^sub>p ((inv a) # b) P) \<in> carrier Q\<^sub>p"
                using 34 P_n_def  eval_at_point_closed
                by blast
              have  "inv(a[^] (nat N)) \<otimes> (c[^]n) =
               inv(a[^] (nat N)) \<otimes> ((a[^] (nat N)) \<otimes> (eval_at_point Q\<^sub>p ((inv a) # b) P))"
                using 31 "33"  by presburger
              then have 6: "inv(a[^] (nat N)) \<otimes> (c[^]n) =
               inv(a[^] (nat N)) \<otimes> (a[^] (nat N)) \<otimes> (eval_at_point Q\<^sub>p ((inv a) # b) P)"
                using 35 monoid.m_assoc[of Q\<^sub>p] Qp.monoid_axioms Qp.nat_pow_closed
                  Qp.nonzero_pow_nonzero a_nz inv_in_frac(1) local.a_closed by presburger
              have 37:"inv(a[^] (nat N)) \<otimes> (c[^]n) = (eval_at_point Q\<^sub>p ((inv a) # b) P)"
              proof-
                have "inv(a[^] (nat N)) \<otimes> (a[^] (nat N)) = \<one> "
                  using  a_closed  a_nz Qp.nat_pow_closed Qp.nonzero_pow_nonzero field_inv(1)
                  by blast
                then have "inv(a[^] (nat N)) \<otimes> (c[^]n) =
                        \<one> \<otimes> (eval_at_point Q\<^sub>p ((inv a) # b) P)"
                  using 6 by presburger
                then show ?thesis using 35 Qp.l_one by blast
              qed
              have 38:"(inv a)[^] (nat N) \<otimes> (c[^]n) = (eval_at_point Q\<^sub>p ((inv a) # b) P)"
                using 37 group.nat_pow_inv[of Q\<^sub>p a "nat N"] a_closed Qp.field_axioms field.field_nat_pow_inv[of Q\<^sub>p]
                by (metis a_nz)
              have 39:"((inv a)[^]m) [^] \<^bsub>Q\<^sub>p\<^esub> n \<otimes> (c[^]n) = (eval_at_point Q\<^sub>p ((inv a) # b) P)"
                using 2  38 monoid.nat_pow_pow[of Q\<^sub>p "inv a" ] N_def
                by (smt "3" Qp_int_nat_pow_pow a_closed a_nz inv_in_frac(3) of_nat_0_le_iff pow_nat)
              have 310:"((((inv a)[^]m) \<otimes> c)[^]n) = (eval_at_point Q\<^sub>p ((inv a) # b) P)"
              proof-
                have AA: "(inv a)[^]m \<in> carrier Q\<^sub>p"
                  using Qp_int_pow_nonzero nonzero_def a_closed a_nz inv_in_frac(3) Qp.nonzero_closed
                  by presburger
                have "((inv a)[^]m) [^] \<^bsub>Q\<^sub>p\<^esub> n \<otimes> (c[^]n) = ((((inv a)[^]m) \<otimes> c)[^]n)"
                  using Qp.nat_pow_distrib[of  "(inv a)[^]m" c n]  a_closed a_def c_def AA by blast
                then show ?thesis
                  using "39" by blast
              qed
              then show ?thesis using c'_def
                by blast
            qed
            have 4: "inv a # b \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
              by (metis a_closed a_nz add.commute b_closed cartesian_power_cons inv_in_frac(1))
            then have 5: "((inv a) # b) \<in> S"
              using 3 P_n_def c'_closed  basic_semialg_set_memI[of "(inv a) # b" "1 + k" c' P n]
              by blast
            have 6: "Qp_invert (take 1 x) # drop 1 x = inv a # b"
              using a_def b_def unfolding Qp_invert_def using "1" Qp_invert_def
              by blast
            show ?thesis using 5 6
              by presburger
          qed
        qed
        then show ?thesis
          using A by blast
      qed
    qed
  qed
  have 8: "is_semialgebraic (1+k) ((partial_pullback 1 Qp_invert k S) \<inter> Nz)"
    using "7" Nz_semialg T_semialg intersection_is_semialg
    by auto
  have 9: "(partial_pullback 1 Qp_invert k S) - Nz = {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs!0 = \<zero>} \<inter>S"
  proof
    show "partial_pullback 1 Qp_invert k S - Nz \<subseteq> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs ! 0 = \<zero>} \<inter>  S"
    proof fix x assume A: " x \<in> partial_pullback 1 Qp_invert k S - Nz"
      have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>)"
        using A
        by (metis DiffD1 partial_pullback_memE(1) plus_1_eq_Suc)
      have 1: "take 1 x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
        by (metis "0" le_add1 plus_1_eq_Suc take_closed)
      have 2: "drop 1 x \<in> carrier (Q\<^sub>p\<^bsup>k\<^esup>)"
        using "0" cartesian_power_drop plus_1_eq_Suc
        by presburger
      have 3: " x = take 1 x @ drop 1 x "
        using 0
        by (metis append_take_drop_id)
      have 4: "Qp_invert (take 1 x) # drop 1 x \<in> S"
        using A partial_pullback_memE'[of "take 1 x" 1 "drop 1 x" k x Qp_invert S] 1 2 3
        by blast
      have 5: "x!0 = \<zero>"
        using A 0 Nz_def by blast
      have 6: "Qp_invert (take 1 x) # drop 1 x = x"
      proof-
        have "(take 1 x) =[x!0]"
          using 0
          by (metis "1" "3" append_Cons nth_Cons_0 Qp.to_R1_to_R)
        then have "Qp_invert (take 1 x) = \<zero>"
          unfolding Qp_invert_def using 5
          by (metis less_one nth_take)
        then show ?thesis using 0 5
          by (metis "3" Cons_eq_append_conv \<open>take 1 x = [x ! 0]\<close> self_append_conv2)
      qed
      have "x \<in> S"
        using 6 4
        by presburger
      then show "x \<in> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs ! 0 = \<zero>} \<inter>  S"
        using Nz_def A 0
        by blast
    qed
    show "{xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs ! 0 = \<zero>} \<inter> S \<subseteq> partial_pullback 1 Qp_invert k S - Nz"
    proof fix x assume A: "x \<in> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs ! 0 = \<zero>} \<inter> S"
      have A0: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>)"
        using A by blast
      have A1: "x!0  = \<zero>"
        using A by blast
      have A2: "x \<in> S"
        using A by blast
      show " x \<in> partial_pullback 1 Qp_invert k S - Nz"
      proof
        show "x \<notin> Nz"
          using Nz_def A1 by blast
        show " x \<in> partial_pullback 1 Qp_invert k S"
        proof(rule partial_pullback_memI)
          show "x \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)"
            using A0
            by (simp add: A0)
          show "Qp_invert (take 1 x) # drop 1 x \<in> S"
          proof-
            have "Qp_invert (take 1 x) = \<zero>"
              unfolding Qp_invert_def  using A0 A1
              by (metis less_numeral_extra(1) nth_take)
            then have "Qp_invert (take 1 x) # drop 1 x = x"
              using A0 A1 A2
              by (metis (no_types, lifting) Cons_eq_append_conv Qp_invert_def \<open>x \<in> carrier (Q\<^sub>p\<^bsup>1+k\<^esup>)\<close>
                  append_take_drop_id inv_in_frac(2) le_add_same_cancel1 self_append_conv2
                  take_closed Qp.to_R1_to_R Qp.to_R_pow_closed zero_le)
            then show ?thesis
              using A2 by presburger
          qed
        qed
      qed
    qed
  qed
  have 10: "is_semialgebraic (1+k) {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs!0 = \<zero>}"
  proof-
    have "{xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs!0 = \<zero>} = V\<^bsub>Q\<^sub>p\<^esub> (Suc k) (pvar Q\<^sub>p 0)"
      unfolding zero_set_def using eval_pvar[of  0 "Suc k"] Qp.cring_axioms
      by blast
    then show ?thesis using
        is_zero_set_imp_basic_semialg pvar_closed[of  0 "Suc k"] Qp.cring_axioms
        is_zero_set_imp_semialg plus_1_eq_Suc zero_less_Suc
      by presburger
  qed
  have 11: "is_semialgebraic (1+k) ({xs \<in> carrier (Q\<^sub>p\<^bsup>Suc k\<^esup>). xs!0 = \<zero>} \<inter>S)"
    using 10 assms basic_semialg_is_semialgebraic intersection_is_semialg
    by blast
  have 12: "(partial_pullback 1 Qp_invert k S) = ((partial_pullback 1 Qp_invert k S) \<inter> Nz) \<union>
                                                  ((partial_pullback 1 Qp_invert k S) - Nz)"
    by blast
  have 13: "is_semialgebraic (1+k) ((partial_pullback 1 Qp_invert k S) - Nz)"
    using 11  9 by metis
  show ?thesis
    using 8  12 13
    by (metis "7" Int_Diff_Un Int_commute plus_1_eq_Suc union_is_semialgebraic)
qed

lemma Qp_invert_is_semialg:
"is_semialg_function 1 Qp_invert"
proof(rule is_semialg_functionI')
  show 0: "Qp_invert \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  proof fix x
    assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>1\<^esup>)"
    then obtain a where a_def: "x = [a]"
      by (metis Qp.to_R1_to_R)
    have a_closed: "a \<in> carrier Q\<^sub>p"
      using a_def A cartesian_power_concat(1) last_closed'
      by blast
    show " Qp_invert x \<in> carrier Q\<^sub>p"
    apply(cases "a = \<zero>")
    unfolding Qp_invert_def using a_def a_closed
    apply (meson Qp.to_R_to_R1)
    by (metis a_closed a_def inv_in_frac(1) Qp.to_R_to_R1)
  qed
  show "\<And>k S. S \<in> basic_semialgs (1 + k) \<Longrightarrow> is_semialgebraic (1 + k) (partial_pullback 1 Qp_invert k S)"
    using Qp_invert_basic_semialg
    by blast
qed

lemma Taylor_deg_1_expansion'':
  assumes "f \<in> carrier Q\<^sub>p_x"
  assumes "\<And>n. f n \<in> \<O>\<^sub>p"
  assumes "a \<in> \<O>\<^sub>p "
  assumes "b \<in> \<O>\<^sub>p"
  shows "\<exists>c c' c''. c = to_fun f a \<and> c' = deriv f a \<and> c \<in> \<O>\<^sub>p \<and> c' \<in> \<O>\<^sub>p \<and>c'' \<in> \<O>\<^sub>p \<and>
                  to_fun f (b) = c \<oplus> c' \<otimes> (b \<ominus> a) \<oplus> (c'' \<otimes> (b \<ominus> a)[^](2::nat))"
proof-
  obtain S where S_def: "S = (Q\<^sub>p  \<lparr> carrier := \<O>\<^sub>p \<rparr>)"
    by blast
  have 1: "f \<in> carrier (UP S)"
    unfolding S_def using val_ring_subring UPQ.poly_cfs_subring[of \<O>\<^sub>p f] assms
    by blast
  have 2: " f \<in> carrier (UP (Q\<^sub>p\<lparr>carrier := \<O>\<^sub>p\<rparr>))"
    using val_ring_subring 1 assms poly_cfs_subring[of \<O>\<^sub>p]
    by blast
  have 3: "\<exists>c\<in>\<O>\<^sub>p. f \<bullet> b = f \<bullet> a \<oplus> UPQ.deriv f a \<otimes> (b \<ominus> a) \<oplus> c \<otimes> (b \<ominus> a) [^] (2::nat)"
    using UP_subring_taylor_appr'[of \<O>\<^sub>p f b a] UP_subring_taylor_appr[of \<O>\<^sub>p f b a] val_ring_subring 1 2 assms
    by blast
  then show ?thesis
    using UP_subring_taylor_appr[of \<O>\<^sub>p f b a] assms UP_subring_deriv_closed[of \<O>\<^sub>p f a]
      UP_subring_eval_closed[of \<O>\<^sub>p f a] 2 val_ring_subring by blast
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Sets Defined by Residues of Valuation Ring Elements\<close>
(**************************************************************************************************)
(**************************************************************************************************)

sublocale padic_fields < Res: cring "Zp_res_ring (Suc n)"
  using p_residues residues.cring
  by blast

context padic_fields
begin

definition Qp_res where
"Qp_res x n =  to_Zp x n "

lemma Qp_res_closed:
  assumes "x \<in> \<O>\<^sub>p"
  shows "Qp_res  x n \<in> carrier (Zp_res_ring n)"
  unfolding Qp_res_def using assms val_ring_memE residue_closed to_Zp_closed by blast

lemma Qp_res_add:
  assumes "x \<in> \<O>\<^sub>p"
  assumes "y \<in> \<O>\<^sub>p"
  shows "Qp_res (x \<oplus> y) n = Qp_res x n \<oplus>\<^bsub>Zp_res_ring n\<^esub> Qp_res y n"
  unfolding Qp_res_def
  using assms residue_of_sum to_Zp_add by presburger

lemma Qp_res_mult:
  assumes "x \<in> \<O>\<^sub>p"
  assumes "y \<in> \<O>\<^sub>p"
  shows "Qp_res (x \<otimes> y) n = Qp_res x n \<otimes>\<^bsub>Zp_res_ring n\<^esub> Qp_res y n"
  unfolding Qp_res_def
  using assms residue_of_prod to_Zp_mult by presburger

lemma Qp_res_diff:
  assumes "x \<in> \<O>\<^sub>p"
  assumes "y \<in> \<O>\<^sub>p"
  shows "Qp_res (x \<ominus> y) n = Qp_res x n \<ominus>\<^bsub>Zp_res_ring n\<^esub> Qp_res y n"
  unfolding Qp_res_def
  using assms residue_of_diff to_Zp_minus
  by (meson val_ring_res)

lemma Qp_res_zero:
  shows  "Qp_res \<zero> n = 0"
  unfolding Qp_res_def to_Zp_zero
  using residue_of_zero(2) by blast

lemma Qp_res_one:
  assumes "n > 0"
  shows  "Qp_res \<one> n = (1::int)"
  using assms
  unfolding Qp_res_def to_Zp_one
  using residue_of_one(2) by blast

lemma Qp_res_nat_inc:
  shows  "Qp_res ([(n::nat)]\<cdot>\<one>) n = n mod p^n"
  unfolding Qp_res_def unfolding to_Zp_nat_inc
  using Zp_nat_inc_res by blast

lemma Qp_res_int_inc:
  shows  "Qp_res ([(k::int)]\<cdot>\<one>) n = k mod p^n"
  unfolding Qp_res_def unfolding to_Zp_int_inc
  using Zp_int_inc_res by blast

lemma Qp_poly_res_monom:
assumes "a \<in> \<O>\<^sub>p"
assumes "x \<in> \<O>\<^sub>p"
assumes "Qp_res a n = 0"
assumes "k > 0"
shows "Qp_res (up_ring.monom (UP Q\<^sub>p) a k \<bullet> x) n = 0"
proof-
  have 0: "up_ring.monom (UP Q\<^sub>p) a k \<bullet> x = a \<otimes> x [^] k"
    apply(rule UPQ.to_fun_monom[of a x k])
    using assms val_ring_memE apply blast
    using assms val_ring_memE by blast
  have 1: "x[^]k \<in> \<O>\<^sub>p"
    using assms val_ring_nat_pow_closed by blast
  show ?thesis unfolding 0
    using Qp_res_mult[of a "x[^]k" n] assms
    using "1" residue_times_zero_r by presburger
qed

lemma Qp_poly_res_zero:
  assumes "q \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>i. q i \<in> \<O>\<^sub>p"
  assumes "\<And>i. Qp_res (q i) n = 0"
  assumes "x \<in> \<O>\<^sub>p"
  shows "Qp_res (q \<bullet> x) n = 0"
proof-
  have "(\<forall>i. q i \<in> \<O>\<^sub>p \<and> Qp_res (q i) n = 0) \<longrightarrow> Qp_res (q \<bullet> x) n = 0"
  proof(rule UPQ.poly_induct[of q], rule assms, rule )
    fix p assume A: "p \<in> carrier (UP Q\<^sub>p)" " deg Q\<^sub>p p = 0" " \<forall>i. p i \<in> \<O>\<^sub>p \<and> Qp_res (p i) n = 0"
    have 0: "p \<bullet> x = p 0"
      using assms
      by (metis A(1) A(2) val_ring_memE UPQ.ltrm_deg_0 UPQ.to_fun_ctrm)
    show "Qp_res (p \<bullet> x) n = 0"
      unfolding 0 using A by blast
  next
    fix p
    assume A0: "(\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p q < deg Q\<^sub>p p \<Longrightarrow> (\<forall>i. q i \<in> \<O>\<^sub>p \<and> Qp_res (q i) n = 0) \<longrightarrow> Qp_res (q \<bullet> x) n = 0)"
      "p \<in> carrier (UP Q\<^sub>p)" "0 < deg Q\<^sub>p p"
    show "(\<forall>i. p i \<in> \<O>\<^sub>p \<and> Qp_res (p i) n = 0) \<longrightarrow> Qp_res (p \<bullet> x) n = 0"
    proof assume A1: " \<forall>i. p i \<in> \<O>\<^sub>p \<and> Qp_res (p i) n = 0"
      obtain k where k_def: "k = deg Q\<^sub>p p"
        by blast
      obtain q where q_def: "q = UPQ.trunc p"
        by blast
      have q_closed: "q \<in> carrier (UP Q\<^sub>p)"
        unfolding q_def
        using A0(2) UPQ.trunc_closed by blast
      have q_deg: "deg Q\<^sub>p q < deg Q\<^sub>p p"
        unfolding q_def
        using A0(2) A0(3) UPQ.trunc_degree by blast
      have 9: "\<And>i. i < deg Q\<^sub>p p \<Longrightarrow> q i = p i"
        unfolding q_def
        using A0(2) UPQ.trunc_cfs by blast
      have 90:  "\<And>i. \<not> i < deg Q\<^sub>p p \<Longrightarrow> q i = \<zero>"
        unfolding q_def
      proof -
        fix i :: nat
        assume "\<not> i < deg Q\<^sub>p p"
        then have "deg Q\<^sub>p q < i"
          using q_deg by linarith
        then show "Cring_Poly.truncate Q\<^sub>p p i = \<zero>"
          using UPQ.deg_gtE q_closed q_def by blast
      qed
      have 10: "(\<forall>i. q i \<in> \<O>\<^sub>p \<and> Qp_res (q i) n = 0)"
      proof fix i
        show "q i \<in> \<O>\<^sub>p \<and> Qp_res (q i) n = 0"
          apply(cases "i < deg Q\<^sub>p p")
           using A1  9[of i] apply presburger
           unfolding q_def using Qp_res_zero  90
           by (metis q_def zero_in_val_ring)
      qed
      have 11: "Qp_res (q \<bullet> x) n = 0"
        using 10 A1 A0 q_closed q_deg by blast
      have 12: "p = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) (p k) k"
        unfolding k_def q_def
        using A0(2) UPQ.trunc_simps(1) by blast
      have 13: "p \<bullet> x = q \<bullet> x \<oplus> (up_ring.monom (UP Q\<^sub>p) (p k) k) \<bullet> x"
      proof-
        have 0: " (q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) (p k) k) \<bullet> x = q \<bullet> x \<oplus> up_ring.monom (UP Q\<^sub>p) (p k) k \<bullet> x"
          apply(rule UPQ.to_fun_plus)
          using A0(2) UPQ.ltrm_closed k_def apply blast
          unfolding q_def apply(rule UPQ.trunc_closed, rule A0)
          using assms val_ring_memE by blast
        show ?thesis
          using 0 12 by metis
      qed
      have 14: "(up_ring.monom (UP Q\<^sub>p) (p k) k) \<bullet> x \<in> \<O>\<^sub>p"
        apply(rule val_ring_poly_eval)
          using A0(2) UPQ.ltrm_closed k_def apply blast
          using UPQ.cfs_monom[of "p k" k ] A1 zero_in_val_ring
          using A0(2) UPQ.ltrm_cfs k_def apply presburger
          using assms(4) by blast
      have 15: "Qp_res ((up_ring.monom (UP Q\<^sub>p) (p k) k) \<bullet> x) n = 0"
        apply(rule Qp_poly_res_monom)
        using A1 apply blast using assms apply blast
        using A1 apply blast unfolding k_def using A0 by blast
      have 16: "Qp_res (q \<bullet> x) n = 0"
        using A0 10 11 by blast
      have 17: "q \<bullet> x \<in> \<O>\<^sub>p"
        apply(rule val_ring_poly_eval, rule q_closed)
        using 10 apply blast by(rule assms)
      have 18: "Qp_res (q \<bullet> x \<oplus> (up_ring.monom (UP Q\<^sub>p) (p k) k) \<bullet> x) n = 0"
        using Qp_res_add[of "q \<bullet> x" "up_ring.monom (UP Q\<^sub>p) (p k) k \<bullet> x" n] 14  17
        unfolding 15 16
        by (metis "10" Qp_res_add UPQ.cfs_add UPQ.coeff_of_sum_diff_degree0 q_closed q_deg)
      show "Qp_res (p \<bullet> x) n = 0"
        using 13 18 by metis
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma Qp_poly_res_eval_0:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "x \<in> \<O>\<^sub>p"
  assumes "\<And>i. f i \<in> \<O>\<^sub>p"
  assumes "\<And>i. g i \<in> \<O>\<^sub>p"
  assumes "\<And>i. Qp_res (f i) n = Qp_res (g i) n"
  shows "Qp_res (f \<bullet> x) n = Qp_res (g \<bullet> x) n"
proof-
    obtain F where F_def: "F = f \<ominus>\<^bsub>UP Q\<^sub>p\<^esub>g"
      by blast
    have F_closed: "F \<in> carrier (UP Q\<^sub>p)"
      unfolding F_def
      using assms by blast
    have F_cfs: "\<And>i. F i = (f i) \<ominus> (g i)"
      unfolding F_def
      using assms UPQ.cfs_minus by blast
    have F_cfs_res: "\<And>i. Qp_res (F i) n = Qp_res (f i) n \<ominus>\<^bsub>Zp_res_ring n\<^esub> Qp_res (g i) n"
      unfolding F_cfs apply(rule Qp_res_diff)
      using assms apply blast using assms by blast
    have 0: "\<And>i. Qp_res (f i) n = Qp_res (g i) n"
      using assms by blast
    have F_cfs_res': "\<And>i. Qp_res (F i) n = 0"
      unfolding F_cfs_res 0
      by (metis diff_self mod_0 residue_minus)
    have 1: "\<And>i. F i \<in> \<O>\<^sub>p"
      unfolding F_cfs using assms
      using val_ring_minus_closed by blast
    have 2: "Qp_res (F \<bullet> x) n = 0"
      by(rule Qp_poly_res_zero, rule F_closed, rule 1, rule F_cfs_res', rule assms)
    have 3: "F \<bullet> x = f \<bullet> x \<ominus> g \<bullet> x"
      unfolding F_def using assms
      by (meson assms UPQ.to_fun_diff val_ring_memE)
    have 4: "Qp_res (F \<bullet> x) n = Qp_res (f \<bullet> x) n \<ominus>\<^bsub>Zp_res_ring n\<^esub> Qp_res (g \<bullet> x) n"
      unfolding 3 apply(rule Qp_res_diff, rule val_ring_poly_eval, rule assms)
      using assms apply blast using assms apply blast
      apply(rule val_ring_poly_eval, rule assms)
      using assms apply blast by(rule assms)
    have 5: "f \<bullet> x \<in> \<O>\<^sub>p"
      apply(rule val_ring_poly_eval, rule assms)
      using assms apply blast using assms by blast
    have 6: "g \<bullet> x \<in> \<O>\<^sub>p"
      apply(rule val_ring_poly_eval, rule assms)
      using assms apply blast by(rule assms)
    show "Qp_res (f \<bullet> x) n = Qp_res (g \<bullet> x) n"
      using 5 6 2 Qp_res_closed[of "f \<bullet> x" n] Qp_res_closed[of "g \<bullet> x" n]
      unfolding 4
    proof -
      assume "Qp_res (f \<bullet> x) n \<ominus>\<^bsub>Zp_res_ring n\<^esub> Qp_res (g \<bullet> x) n = 0"
      then show ?thesis
        by (metis (no_types) Qp_res_def 5 6 res_diff_zero_fact(1) residue_of_diff to_Zp_closed val_ring_memE)
    qed
qed

lemma Qp_poly_res_eval_1:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "x \<in> \<O>\<^sub>p"
  assumes "y \<in> \<O>\<^sub>p"
  assumes "\<And>i. f i \<in> \<O>\<^sub>p"
  assumes "Qp_res x n = Qp_res y n"
  shows "Qp_res (f \<bullet> x) n = Qp_res (f \<bullet> y) n"
proof-
  have "(\<forall>i. f i \<in> \<O>\<^sub>p) \<longrightarrow> Qp_res (f \<bullet> x) n = Qp_res (f \<bullet> y) n"
    apply(rule UPQ.poly_induct[of f], rule assms)
  proof fix f assume A: "f \<in> carrier (UP Q\<^sub>p)" "deg Q\<^sub>p f = 0" "\<forall>i. f i \<in> \<O>\<^sub>p"
    show "Qp_res (f \<bullet> x) n = Qp_res (f \<bullet> y) n"
    proof-
      obtain a where a_def: "a \<in> carrier Q\<^sub>p \<and> f = to_polynomial Q\<^sub>p a"
        using assms
        by (metis A(1) A(2) UPQ.lcf_closed UPQ.to_poly_inverse)
      have a_eq: "f = to_polynomial Q\<^sub>p a"
        using a_def  by blast
      have 0: "f \<bullet> x = a"
        using a_def assms unfolding a_eq
        by (meson UPQ.to_fun_to_poly val_ring_memE)
      have 1: "f \<bullet> y = a"
        using a_def assms unfolding a_eq
        by (meson UPQ.to_fun_to_poly val_ring_memE)
      show " Qp_res (f \<bullet> x) n = Qp_res (f \<bullet> y) n"
        unfolding 0 1 by blast
    qed
  next
    fix f
    assume A: " (\<And>q. q \<in> carrier (UP Q\<^sub>p) \<Longrightarrow> deg Q\<^sub>p q < deg Q\<^sub>p f \<Longrightarrow> (\<forall>i. q i \<in> \<O>\<^sub>p) \<longrightarrow> Qp_res (q \<bullet> x) n = Qp_res (q \<bullet> y) n)"
        "f \<in> carrier (UP Q\<^sub>p)" " 0 < deg Q\<^sub>p f"
    show "(\<forall>i. f i \<in> \<O>\<^sub>p) \<longrightarrow> Qp_res (f \<bullet> x) n = Qp_res (f \<bullet> y) n"
    proof assume A1: "\<forall>i. f i \<in> \<O>\<^sub>p"
      obtain q where q_def: "q = UPQ.trunc f"
        by blast
      have q_closed: "q \<in> carrier (UP Q\<^sub>p)"
        using q_def A UPQ.trunc_closed by presburger
      have q_deg: "deg Q\<^sub>p q < deg Q\<^sub>p f"
        using q_def A UPQ.trunc_degree by blast
      have q_cfs: "\<forall>i. q i \<in> \<O>\<^sub>p"
      proof fix i show "q i \<in> \<O>\<^sub>p"
        apply(cases "i < deg Q\<^sub>p f")
        unfolding q_def using A A1 UPQ.trunc_cfs
         apply presburger
        using q_deg q_closed
        proof -
        assume "\<not> i < deg Q\<^sub>p f"
        then have "deg Q\<^sub>p f \<le> i"
          by (meson diff_is_0_eq neq0_conv zero_less_diff)
        then show "Cring_Poly.truncate Q\<^sub>p f i \<in> \<O>\<^sub>p"
          by (metis (no_types) UPQ.deg_eqI diff_is_0_eq' le_trans nat_le_linear neq0_conv q_closed q_def q_deg zero_in_val_ring zero_less_diff)
        qed
      qed
      hence 0: "Qp_res (q \<bullet> x) n = Qp_res (q \<bullet> y) n"
        using A q_closed q_deg by blast
      have 1: "Qp_res (UPQ.ltrm f \<bullet> x) n = Qp_res (UPQ.ltrm f \<bullet> y) n"
      proof-
        have 10: "UPQ.ltrm f \<bullet> x =  (f (deg Q\<^sub>p f)) \<otimes> x[^](deg Q\<^sub>p f)"
          using A assms  A1 UPQ.to_fun_monom val_ring_memE by presburger
        have 11: "UPQ.ltrm f \<bullet> y =  (f (deg Q\<^sub>p f)) \<otimes> y[^](deg Q\<^sub>p f)"
          using A assms  A1 UPQ.to_fun_monom val_ring_memE by presburger
        obtain d where d_def: "d = deg Q\<^sub>p f"
          by blast
        have 12: "Qp_res (x[^]d) n = Qp_res (y[^]d) n"
          apply(induction d)
          using Qp.nat_pow_0 apply presburger
          using Qp_res_mult assms Qp.nat_pow_Suc val_ring_nat_pow_closed by presburger
        hence 13: "Qp_res (x [^] deg Q\<^sub>p f) n = Qp_res (y [^] deg Q\<^sub>p f) n"
          unfolding d_def by blast
        have 14: "x [^] deg Q\<^sub>p f \<in> \<O>\<^sub>p"
          using assms val_ring_nat_pow_closed by blast
        have 15: "y [^] deg Q\<^sub>p f \<in> \<O>\<^sub>p"
          using assms val_ring_nat_pow_closed by blast
        have 16: "Qp_res (f (deg Q\<^sub>p f) \<otimes> x [^] deg Q\<^sub>p f) n = Qp_res (f (deg Q\<^sub>p f)) n \<otimes>\<^bsub>residue_ring (p ^ n)\<^esub> Qp_res (x [^] deg Q\<^sub>p f) n"
          apply(rule Qp_res_mult[of "f (deg Q\<^sub>p f)" " x[^](deg Q\<^sub>p f)" n])
          using A1 apply blast by(rule 14)
        have 17: "Qp_res (f (deg Q\<^sub>p f) \<otimes> y [^] deg Q\<^sub>p f) n = Qp_res (f (deg Q\<^sub>p f)) n \<otimes>\<^bsub>residue_ring (p ^ n)\<^esub> Qp_res (y [^] deg Q\<^sub>p f) n"
          apply(rule Qp_res_mult[of "f (deg Q\<^sub>p f)" " y[^](deg Q\<^sub>p f)" n])
          using A1 apply blast by(rule 15)
        show ?thesis
          unfolding 10 11 16 17 13 by blast
      qed
      have f_decomp: "f = q \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> UPQ.ltrm f"
        using A unfolding q_def
        using UPQ.trunc_simps(1) by blast
      have 2: "f \<bullet> x = q \<bullet> x \<oplus> (UPQ.ltrm f \<bullet> x)"
        using A f_decomp q_closed q_cfs
        by (metis val_ring_memE UPQ.ltrm_closed UPQ.to_fun_plus assms(2))
      have 3: "f \<bullet> y = q \<bullet> y \<oplus> (UPQ.ltrm f \<bullet> y)"
        using A f_decomp q_closed q_cfs
        by (metis val_ring_memE UPQ.ltrm_closed UPQ.to_fun_plus assms(3))
      show 4: " Qp_res (f \<bullet> x) n = Qp_res (f \<bullet> y) n "
        unfolding 2 3 using assms q_cfs Qp_res_add 0 1
        by (metis (no_types, opaque_lifting) "2" "3" A(2) A1 Qp_res_def poly_eval_cong)
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma Qp_poly_res_eval_2:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "x \<in> \<O>\<^sub>p"
  assumes "y \<in> \<O>\<^sub>p"
  assumes "\<And>i. f i \<in> \<O>\<^sub>p"
  assumes "\<And>i. g i \<in> \<O>\<^sub>p"
  assumes "\<And>i. Qp_res (f i) n = Qp_res (g i) n"
  assumes "Qp_res x n = Qp_res y n"
  shows "Qp_res (f \<bullet> x) n = Qp_res (g \<bullet> y) n"
proof-
  have 0: "Qp_res (f \<bullet> x) n = Qp_res (g \<bullet> x) n"
    using Qp_poly_res_eval_0 assms by blast
  have 1: "Qp_res (g \<bullet> x) n = Qp_res (g \<bullet> y) n"
    using Qp_poly_res_eval_1 assms by blast
  show ?thesis unfolding 0 1 by blast
qed

definition poly_res_class where
"poly_res_class n d f = {q \<in> carrier (UP Q\<^sub>p). deg Q\<^sub>p q \<le> d \<and> (\<forall>i. q i \<in> \<O>\<^sub>p \<and> Qp_res (f i) n = Qp_res (q i) n) }"

lemma poly_res_class_closed:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "g \<in> carrier (UP Q\<^sub>p)"
  assumes "deg Q\<^sub>p f \<le> d"
  assumes "deg Q\<^sub>p g \<le> d"
  assumes "g \<in> poly_res_class n d f"
  shows "poly_res_class n d f = poly_res_class n d g"
  unfolding poly_res_class_def
  apply(rule equalityI)
apply(rule subsetI)
  unfolding mem_Collect_eq apply(rule conjI, blast, rule conjI, blast)
  using assms unfolding poly_res_class_def mem_Collect_eq
   apply presburger
apply(rule subsetI) unfolding mem_Collect_eq
  apply(rule conjI, blast, rule conjI, blast)
  using assms unfolding poly_res_class_def mem_Collect_eq
  by presburger

lemma poly_res_class_memE:
  assumes "f \<in> poly_res_class n d g"
  shows "f \<in> carrier (UP Q\<^sub>p)"
        "deg Q\<^sub>p f \<le> d"
        "f i \<in> \<O>\<^sub>p"
        "Qp_res (g i) n = Qp_res (f i) n"
  using assms unfolding poly_res_class_def mem_Collect_eq apply blast
  using assms unfolding poly_res_class_def mem_Collect_eq apply blast
  using assms unfolding poly_res_class_def mem_Collect_eq apply blast
  using assms unfolding poly_res_class_def mem_Collect_eq by blast

definition val_ring_polys where
"val_ring_polys = {f \<in> carrier (UP Q\<^sub>p). (\<forall>i. f i \<in> \<O>\<^sub>p)} "

lemma val_ring_polys_closed:
"val_ring_polys \<subseteq> carrier (UP Q\<^sub>p)"
  unfolding val_ring_polys_def by blast

lemma val_ring_polys_memI:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>i. f i \<in> \<O>\<^sub>p"
  shows "f \<in> val_ring_polys"
  using assms   unfolding val_ring_polys_def by blast

lemma val_ring_polys_memE:
  assumes "f \<in> val_ring_polys"
  shows "f \<in> carrier (UP Q\<^sub>p)"
        "f i \<in> \<O>\<^sub>p"
  using assms unfolding val_ring_polys_def apply blast
  using assms unfolding val_ring_polys_def by blast

definition val_ring_polys_grad where
"val_ring_polys_grad d = {f \<in> val_ring_polys. deg Q\<^sub>p f \<le> d}"

lemma val_ring_polys_grad_closed:
"val_ring_polys_grad d \<subseteq> val_ring_polys"
  unfolding val_ring_polys_grad_def by blast

lemma val_ring_polys_grad_closed':
"val_ring_polys_grad d \<subseteq> carrier (UP Q\<^sub>p)"
  unfolding val_ring_polys_grad_def val_ring_polys_def by blast

lemma val_ring_polys_grad_memI:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "\<And>i. f i \<in> \<O>\<^sub>p"
  assumes "deg Q\<^sub>p f \<le> d"
  shows "f \<in> val_ring_polys_grad d"
  using assms unfolding val_ring_polys_grad_def val_ring_polys_def by blast

lemma val_ring_polys_grad_memE:
  assumes "f \<in> val_ring_polys_grad d"
  shows "f \<in> carrier (UP Q\<^sub>p)"
        "deg Q\<^sub>p f \<le> d"
        "f i \<in> \<O>\<^sub>p"
  using assms unfolding val_ring_polys_grad_def val_ring_polys_def apply blast
  using assms unfolding val_ring_polys_grad_def val_ring_polys_def apply blast
  using assms unfolding val_ring_polys_grad_def val_ring_polys_def by blast

lemma poly_res_classes_in_val_ring_polys_grad:
  assumes "f \<in> val_ring_polys_grad d"
  shows "poly_res_class n d f \<subseteq> val_ring_polys_grad d"
  apply(rule subsetI, rule val_ring_polys_grad_memI)
    apply(rule poly_res_class_memE[of _ n d f], blast)
   apply(rule poly_res_class_memE[of _ n d f], blast)
  by(rule poly_res_class_memE[of _ n d f], blast)

lemma poly_res_class_disjoint:
  assumes "f \<in> val_ring_polys_grad d"
  assumes "f \<notin> poly_res_class n d g"
  shows "poly_res_class n d f \<inter> poly_res_class n d g = {}"
  apply(rule equalityI)
  apply(rule subsetI)
  using assms
  unfolding poly_res_class_def mem_Collect_eq Int_iff
  apply (metis val_ring_polys_grad_memE(1) val_ring_polys_grad_memE(2) val_ring_polys_grad_memE(3))
  by blast

lemma poly_res_class_refl:
  assumes "f \<in> val_ring_polys_grad d"
  shows "f \<in> poly_res_class n d f"
  unfolding poly_res_class_def mem_Collect_eq
  using assms val_ring_polys_grad_memE(1) val_ring_polys_grad_memE(2) val_ring_polys_grad_memE(3) by blast

lemma poly_res_class_memI:
  assumes "f \<in> carrier (UP Q\<^sub>p)"
  assumes "deg Q\<^sub>p f \<le> d"
  assumes "\<And>i. f i \<in> \<O>\<^sub>p"
  assumes "\<And>i. Qp_res (f i) n = Qp_res (g i) n"
  shows "f \<in> poly_res_class n d g"
  unfolding poly_res_class_def mem_Collect_eq using assms
  by metis

definition poly_res_classes where
"poly_res_classes n d = poly_res_class n d ` val_ring_polys_grad d"

lemma poly_res_classes_disjoint:
  assumes "A \<in> poly_res_classes n d"
  assumes "B \<in> poly_res_classes n d"
  assumes "g \<in> A - B"
  shows "A \<inter> B = {}"
proof-
  obtain a where a_def: "a \<in> val_ring_polys_grad d \<and> A = poly_res_class n d a"
    using assms unfolding poly_res_classes_def by blast
  obtain b where b_def: "b \<in> val_ring_polys_grad d \<and> B = poly_res_class n d b"
    using assms unfolding poly_res_classes_def by blast
  have 0: "\<And>f. f \<in> A \<inter> B \<Longrightarrow> False"
  proof-
    fix f assume A: "f \<in> A \<inter> B"
    have 1: "\<exists>i. Qp_res (g i) n \<noteq> Qp_res (f i) n"
    proof(rule ccontr)
      assume B: "\<nexists>i. Qp_res (g i) n \<noteq> Qp_res (f i) n"
      then have 2: "\<And>i.  Qp_res (g i) n = Qp_res (f i) n"
        by blast
      have 3: "g \<in> poly_res_class n d a"
        using a_def assms by blast
      have 4: "\<And>i. Qp_res (b i) n = Qp_res (f i) n"
        apply(rule poly_res_class_memE[of _ n d])
        using assms A b_def by blast
      have 5: "\<And>i. Qp_res (a i) n = Qp_res (g i) n"
        apply(rule poly_res_class_memE[of _ n d])
        using assms A a_def by blast
      have 6: "g \<in> poly_res_class n d b"
        apply(rule poly_res_class_memI, rule poly_res_class_memE[of _ n d a], rule 3,
            rule poly_res_class_memE[of _ n d a], rule 3,  rule poly_res_class_memE[of _ n d a], rule 3)
        unfolding 2 4 by blast
      show False using 6 b_def assms by blast
    qed
    then obtain i where i_def: "Qp_res (g i) n \<noteq> Qp_res (f i) n"
      by blast
    have 2: "\<And>i. Qp_res (a i) n = Qp_res (f i) n"
      apply(rule poly_res_class_memE[of _ n d])
      using A a_def by blast
    have 3: "\<And>i. Qp_res (b i) n = Qp_res (f i) n"
      apply(rule poly_res_class_memE[of _ n d])
      using A b_def by blast
    have 4: "\<And>i. Qp_res (a i) n = Qp_res (g i) n"
      apply(rule poly_res_class_memE[of _ n d])
      using assms a_def by blast
    show False using i_def 2 unfolding 4 2 by blast
  qed
  show ?thesis using 0 by blast
qed

definition int_fun_to_poly where
"int_fun_to_poly (f::nat \<Rightarrow> int) i = [(f i)]\<cdot>\<one>"

lemma int_fun_to_poly_closed:
  assumes "\<And>i. i > d \<Longrightarrow> f i = 0"
  shows "int_fun_to_poly f \<in> carrier (UP Q\<^sub>p)"
  apply(rule UPQ.UP_car_memI[of d])
  using assms unfolding int_fun_to_poly_def
  using Qp.int_inc_zero apply presburger
  by(rule Qp.int_inc_closed)

lemma int_fun_to_poly_deg:
  assumes "\<And>i. i > d \<Longrightarrow> f i = 0"
  shows "deg Q\<^sub>p (int_fun_to_poly f) \<le> d"
  apply(rule UPQ.deg_leqI, rule int_fun_to_poly_closed, rule assms, blast)
  unfolding int_fun_to_poly_def using assms
  using Qp.int_inc_zero by presburger

lemma Qp_res_mod_triv:
  assumes "a \<in> \<O>\<^sub>p"
  shows "Qp_res a n mod p ^ n = Qp_res a n"
  using assms Qp_res_closed[of a n]
  by (meson mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))

lemma int_fun_to_poly_is_class_wit:
  assumes "f \<in> poly_res_class n d g"
  shows "(int_fun_to_poly (\<lambda>i::nat. Qp_res (f i) n)) \<in> poly_res_class n d g"
proof(rule poly_res_class_memI[of   ], rule int_fun_to_poly_closed[of d])
  show 0: "\<And>i. d < i \<Longrightarrow> Qp_res (f i) n = 0"
  proof- fix i assume A: "d < i"
    hence 0: "deg Q\<^sub>p f < i"
      using A  assms poly_res_class_memE(2)[of f n d g]
      by linarith
    have 1: "f i = \<zero>"
      using 0 assms poly_res_class_memE[of f n d g]
      using UPQ.UP_car_memE(2) by blast
    show "Qp_res (f i) n = 0"
      unfolding 1 Qp_res_zero by blast
  qed
  show "deg Q\<^sub>p (int_fun_to_poly (\<lambda>i. Qp_res (f i) n)) \<le> d"
    by(rule int_fun_to_poly_deg, rule 0, blast)
  show "\<And>i. int_fun_to_poly (\<lambda>i. Qp_res (f i) n) i \<in> \<O>\<^sub>p"
    unfolding int_fun_to_poly_def
    using Qp.int_mult_closed Qp_val_ringI val_of_int_inc by blast
  show "\<And>i. Qp_res (int_fun_to_poly (\<lambda>i. Qp_res (f i) n) i) n = Qp_res (g i) n"
    unfolding int_fun_to_poly_def Qp_res_int_inc
    using Qp_res_mod_triv assms poly_res_class_memE(4) Qp_res_closed UPQ.cfs_closed
    by (metis poly_res_class_memE(3))
qed

lemma finite_support_funs_finite:
"finite (({..d} \<rightarrow> carrier (Zp_res_ring n)) \<inter> {(f::nat \<Rightarrow> int). \<forall>i > d. f i = 0})"
proof-
  have 0: "finite (\<Pi>\<^sub>E i \<in> {..d}.carrier (Zp_res_ring n))"
    apply(rule finite_PiE, blast)
    using residue_ring_card[of n] by blast
  obtain g where g_def: "g = (\<lambda>f. (\<lambda>i::nat. if i \<in> {..d} then f i else (0::int)))"
    by blast
  have 1: "g `  (\<Pi>\<^sub>E i \<in> {..d}.carrier (Zp_res_ring n)) = (({..d} \<rightarrow> carrier (Zp_res_ring n)) \<inter> {(f::nat \<Rightarrow> int). \<forall>i > d. f i = 0})"
  proof(rule equalityI, rule subsetI)
    fix x assume A: "x \<in> g ` ({..d} \<rightarrow>\<^sub>E carrier (residue_ring (p ^ n)))"
    obtain f where f_def: "f \<in> (\<Pi>\<^sub>E i \<in> {..d}.carrier (Zp_res_ring n)) \<and> x = g f"
      using A by blast
    have x_eq: "x = g f"
      using f_def by blast
    show "x \<in> ({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0}"
    proof(rule, rule)
      fix i assume A: "i \<in> {..d}"
      show "x i \<in> carrier (Zp_res_ring n)"
      proof(cases "i \<in> {..d}")
        case True
        then have T0: "f i \<in> carrier (Zp_res_ring n)"
          using f_def by blast
        have "x i = f i"
          unfolding x_eq g_def
          using True by metis
        thus ?thesis using T0 by metis
      next
        case False
        then have F0: "x i = 0"
          unfolding x_eq g_def by metis
        show ?thesis
          unfolding F0
          by (metis residue_mult_closed residue_times_zero_r)
      qed
    next
      show "x \<in> {f. \<forall>i>d. f i = 0}"
      proof(rule, rule, rule)
        fix i assume A: "d < i"
        then have 0: "i \<notin> {..d}"
          by simp
        thus "x i = 0"
          unfolding x_eq g_def
          by metis
      qed
    qed
  next
    show "({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0}
    \<subseteq> g ` ({..d} \<rightarrow>\<^sub>E carrier (residue_ring (p ^ n)))"
    proof(rule subsetI)
    fix x
    assume A: " x \<in> ({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0}"
    show " x \<in> g ` ({..d} \<rightarrow>\<^sub>E carrier (residue_ring (p ^ n)))"
    proof-
      obtain h where h_def: "h = restrict x {..d}"
        by blast
      have 0: "\<And>i. i \<in> {..d} \<Longrightarrow> h i = x i"
        unfolding h_def restrict_apply by metis
      have 1: "\<And>i. i \<notin> {..d} \<Longrightarrow> h i = undefined"
        unfolding h_def restrict_apply by metis
      have 2: "\<And>i. i \<in> {..d} \<Longrightarrow> h i \<in> carrier (Zp_res_ring n)"
        using A 0 unfolding 0 by blast
      have 3: "h \<in> {..d} \<rightarrow>\<^sub>E carrier (residue_ring (p ^ n))"
        by(rule, rule 2, blast, rule 1, blast)
      have 4: "\<And>i. i \<notin> {..d} \<Longrightarrow> x i = 0"
        using A unfolding Int_iff mem_Collect_eq
        by (metis atMost_iff eq_imp_le le_simps(1) linorder_neqE_nat)
      have 5: "x = g h"
      proof fix i
        show "x i = g h i"
          unfolding g_def
          apply(cases "i \<in> {..d}")
          using 0 apply metis unfolding 4
          by metis
      qed
      show ?thesis unfolding 5 using 3 by blast
     qed
   qed
  qed
  have 2: "finite (g `  (\<Pi>\<^sub>E i \<in> {..d}.carrier (Zp_res_ring n)))"
    using 0 by blast
  show ?thesis using 2 unfolding 1 by blast
qed

lemma poly_res_classes_finite:
"finite (poly_res_classes n d)"
proof-
  have 0: "poly_res_class n d ` int_fun_to_poly ` (({..d} \<rightarrow> carrier (Zp_res_ring n)) \<inter> {(f::nat \<Rightarrow> int). \<forall>i > d. f i = 0}) = poly_res_classes n d"
  proof(rule equalityI, rule subsetI)
    fix x assume A: " x \<in> poly_res_class n d ` int_fun_to_poly ` (({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0})"
    then obtain f where f_def: "f \<in> ({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0} \<and>
                                x = poly_res_class n d (int_fun_to_poly f)"
      by blast
    have x_eq: "x = poly_res_class n d (int_fun_to_poly f)"
      using f_def by blast
    show "x \<in> poly_res_classes n d"
    proof-
      have 0: "int_fun_to_poly f \<in> val_ring_polys_grad d"
        apply(rule val_ring_polys_grad_memI, rule int_fun_to_poly_closed[of d])
        using f_def apply blast
        using int_fun_to_poly_def
         apply (metis Qp.int_inc_closed padic_fields.int_fun_to_poly_def padic_fields.val_of_int_inc padic_fields_axioms val_ring_memI)
        apply(rule int_fun_to_poly_deg)
        using f_def by blast
      show ?thesis unfolding poly_res_classes_def x_eq
        using 0 by blast
    qed
  next
    show "poly_res_classes n d
    \<subseteq> poly_res_class n d `
       int_fun_to_poly `
       (({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter>
        {f. \<forall>i>d. f i = 0})"
    proof(rule subsetI)
    fix x assume A: " x \<in> poly_res_classes n d"
    show "x \<in> poly_res_class n d ` int_fun_to_poly ` (({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0})"
    proof-
      obtain f where f_def: "f \<in> val_ring_polys_grad d \<and> x = poly_res_class n d f"
        using A unfolding poly_res_classes_def by blast
      have x_eq: "x = poly_res_class n d f"
        using f_def by blast
      obtain h where h_def: "h = (\<lambda>i::nat. Qp_res (f i) n)"
        by blast
      have 0: "\<And>i. i > d \<Longrightarrow> f i = \<zero>"
      proof- fix i assume A: "i > d"
         have "i > deg Q\<^sub>p f"
           apply(rule le_less_trans[of _ d])
           using f_def unfolding val_ring_polys_grad_def val_ring_polys_def mem_Collect_eq
            apply blast
           by(rule A)
        then show "f i = \<zero>"
          using f_def unfolding val_ring_polys_grad_def val_ring_polys_def mem_Collect_eq
          using UPQ.deg_leE by blast
      qed
      have 1: "\<And>i. i > d \<Longrightarrow> h i = 0"
        unfolding h_def 0 Qp_res_zero by blast
      have 2: "x = poly_res_class n d (int_fun_to_poly h)"
        unfolding x_eq
        apply(rule poly_res_class_closed)
        using f_def unfolding val_ring_polys_grad_def val_ring_polys_def mem_Collect_eq apply blast
           apply(rule int_fun_to_poly_closed[of d], rule 1, blast)
        using f_def unfolding val_ring_polys_grad_def val_ring_polys_def mem_Collect_eq apply blast
         apply(rule int_fun_to_poly_deg, rule 1, blast)
        unfolding h_def
        apply(rule int_fun_to_poly_is_class_wit, rule poly_res_class_refl)
        using f_def by blast
      have 3: "h \<in> ({..d} \<rightarrow> carrier (residue_ring (p ^ n))) \<inter> {f. \<forall>i>d. f i = 0}"
        apply(rule , rule )
        unfolding h_def apply(rule Qp_res_closed, rule val_ring_polys_grad_memE[of _ d])
        using f_def apply blast
        unfolding mem_Collect_eq apply(rule, rule)
        unfolding 0 Qp_res_zero by blast
      show ?thesis
        unfolding 2 using 3 by blast
      qed
    qed
  qed
  have 1: "finite (poly_res_class n d ` int_fun_to_poly ` (({..d} \<rightarrow> carrier (Zp_res_ring n)) \<inter> {(f::nat \<Rightarrow> int). \<forall>i > d. f i = 0}))"
    using finite_support_funs_finite by blast
  show ?thesis using 1 unfolding 0 by blast
qed

lemma Qp_res_eq_zeroI:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "val a \<ge> n"
  shows "Qp_res a n = 0"
proof-
  have 0: "val_Zp (to_Zp a) \<ge> n"
    using assms to_Zp_val by presburger
  have 1: "to_Zp a n = 0"
    apply(rule zero_below_val_Zp, rule to_Zp_closed)
    using val_ring_closed assms apply blast
    by(rule 0)
  thus ?thesis unfolding Qp_res_def by blast
qed

lemma Qp_res_eqI:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "Qp_res (a \<ominus> b) n = 0"
  shows "Qp_res a n = Qp_res b n"
  using assms by (metis Qp_res_def val_ring_memE res_diff_zero_fact(1) to_Zp_closed to_Zp_minus)

lemma Qp_res_eqI':
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "val (a \<ominus> b) \<ge> n"
  shows "Qp_res a n = Qp_res b n"
  apply(rule Qp_res_eqI, rule assms, rule assms, rule Qp_res_eq_zeroI)
  using assms Q\<^sub>p_def Zp_def \<iota>_def padic_fields.val_ring_minus_closed padic_fields_axioms apply blast
  by(rule assms)

lemma Qp_res_eqE:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "Qp_res a n = Qp_res b n"
  shows "val (a \<ominus> b) \<ge> n"
proof-
  have 0: "val (a \<ominus> b) = val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b)"
    using assms
    by (metis to_Zp_minus to_Zp_val val_ring_minus_closed)
  have 1: "(to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b) n = 0"
    using assms unfolding Qp_res_def
    by (meson val_ring_memE res_diff_zero_fact'' to_Zp_closed)
  have 2: "val_Zp (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b) \<ge> n"
    apply(cases "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
  proof -
    assume a1: "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
    have "\<forall>n. eint (int n) \<le> val_Zp \<zero>\<^bsub>Z\<^sub>p\<^esub>"
      by (metis (no_types) Zp.r_right_minus_eq Zp.zero_closed val_Zp_dist_def val_Zp_dist_res_eq2)
       then show ?thesis
      using a1 by presburger
  next
    assume a1: "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
    have 00: "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b \<in> carrier Z\<^sub>p"
      using assms
      by (meson val_ring_memE Zp.cring_simprules(4) to_Zp_closed)
    show ?thesis
      using 1 a1 ord_Zp_geq[of "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b" n] 00
            val_ord_Zp[of "to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b"] eint_ord_code by metis
  qed
  thus ?thesis unfolding 0 by blast
qed

lemma notin_closed:
"(\<not> ((c::eint) \<le> x \<and> x \<le> d)) = (x < c \<or> d < x)"
  by auto

lemma Qp_res_neqI:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "val (a \<ominus> b) < n"
  shows "Qp_res a n \<noteq> Qp_res b n"
  apply(rule ccontr)
  using Qp_res_eqE[of a b n] assms
  using notin_closed by blast

lemma Qp_res_equal:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "l = Qp_res a n"
  shows "Qp_res a n = Qp_res ([l]\<cdot>\<one>) n "
  unfolding Qp_res_int_inc assms using assms Qp_res_mod_triv by presburger

definition Qp_res_class where
"Qp_res_class n b = {a \<in> \<O>\<^sub>p. Qp_res a n = Qp_res b n}"

definition Qp_res_classes where
"Qp_res_classes n = Qp_res_class n ` \<O>\<^sub>p"

lemma val_ring_int_inc_closed:
"[(k::int)]\<cdot>\<one> \<in> \<O>\<^sub>p"
proof-
  have 0: "[(k::int)]\<cdot>\<one> = \<iota> ([(k::int)]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using inc_of_int by blast
  thus ?thesis
    by blast
qed

lemma val_ring_nat_inc_closed:
"[(k::nat)]\<cdot>\<one> \<in> \<O>\<^sub>p"
proof-
 have 0: "[k]\<cdot>\<one> = \<iota> ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
   using inc_of_nat by blast
  thus ?thesis
    by blast
qed

lemma Qp_res_classes_wits:
"Qp_res_classes n  =  (\<lambda>l::int. Qp_res_class n ([l]\<cdot>\<one>)) ` (carrier (Zp_res_ring n))"
proof-
 obtain F where F_def: "F = (\<lambda>l::int. Qp_res_class n ([l]\<cdot>\<one>))"
    by blast
  have 0: "Qp_res_classes n  = F ` (carrier (Zp_res_ring n))"
  proof(rule equalityI, rule subsetI)
    fix x assume A: "x \<in> Qp_res_classes n"
    then obtain a where a_def: "a \<in> \<O>\<^sub>p \<and> x = Qp_res_class n a"
      unfolding Qp_res_classes_def by blast
    have 1: "Qp_res a n = Qp_res ([(Qp_res a n)]\<cdot>\<one>) n "
      apply(rule Qp_res_equal)
      using a_def apply blast by blast
    have 2: "Qp_res_class n a = Qp_res_class n ([(Qp_res a n)]\<cdot>\<one>)"
      unfolding Qp_res_class_def using 1 by metis
    have 3: "x =  Qp_res_class n ([(Qp_res a n)]\<cdot>\<one>)"
      using a_def unfolding 2 by blast
    have 4: "a \<in> \<O>\<^sub>p"
      using a_def by blast
    show " x \<in> F ` carrier (Zp_res_ring n)"
      unfolding F_def  3
      using Qp_res_closed[of a n] 4 by blast
  next
    show "F ` carrier (residue_ring (p ^ n)) \<subseteq> Qp_res_classes n"
    proof(rule subsetI)
    fix x assume A: "x \<in> F ` (carrier (Zp_res_ring n))"
    then obtain l where l_def: "l \<in> carrier (Zp_res_ring n) \<and> x = F l"
      using A by blast
    have 0: "x = F l"
      using l_def by blast
    show "x \<in> Qp_res_classes n"
      unfolding 0 F_def Qp_res_classes_def using val_ring_int_inc_closed by blast
    qed
  qed
  then show ?thesis unfolding F_def by blast
qed

lemma Qp_res_classes_finite:
"finite (Qp_res_classes n)"
by (metis Qp_res_classes_wits finite_atLeastLessThan_int finite_imageI p_res_ring_car)

definition Qp_cong_set where
"Qp_cong_set \<alpha> a =  {x \<in> \<O>\<^sub>p. to_Zp x \<alpha> = a \<alpha>}"

lemma Qp_cong_set_as_ball:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "a \<alpha> = 0"
  shows "Qp_cong_set \<alpha> a = B\<^bsub>\<alpha>\<^esub>[\<zero>]"
proof-
  have 0: "\<iota> a \<in> carrier Q\<^sub>p"
    using assms inc_closed[of a] by blast
  show ?thesis
  proof
    show "Qp_cong_set \<alpha> a \<subseteq> B\<^bsub>\<alpha>\<^esub>[\<zero>]"
    proof fix x assume A: "x \<in> Qp_cong_set \<alpha> a"
      show "x \<in> B\<^bsub>\<alpha> \<^esub>[\<zero>]"
      proof(rule c_ballI)
        show t0: "x \<in> carrier Q\<^sub>p"
          using A unfolding Qp_cong_set_def
          using val_ring_memE by blast
        show "eint (int \<alpha>) \<le> val (x \<ominus> \<zero>)"
        proof-
          have t1: "to_Zp x \<alpha> = 0"
            using A unfolding Qp_cong_set_def
            by (metis (mono_tags, lifting) assms(2) mem_Collect_eq)
          have t2: "val_Zp (to_Zp x) \<ge> \<alpha>"
            apply(cases "to_Zp x = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
             apply (metis Zp.r_right_minus_eq Zp.zero_closed val_Zp_dist_def val_Zp_dist_res_eq2)
              using ord_Zp_geq[of "to_Zp x" \<alpha>] A unfolding Qp_cong_set_def
              by (metis (no_types, lifting) val_ring_memE eint_ord_simps(1) t1 to_Zp_closed to_Zp_def val_ord_Zp)
          then show ?thesis using A unfolding Qp_cong_set_def mem_Collect_eq
            using val_ring_memE
             by (metis Qp_res_eqE Qp_res_eq_zeroI Qp_res_zero to_Zp_val zero_in_val_ring)
         qed
      qed
    qed
    show "B\<^bsub>int \<alpha>\<^esub>[\<zero>] \<subseteq> Qp_cong_set \<alpha> a"
    proof fix x assume A: "x \<in> B\<^bsub>int \<alpha>\<^esub>[\<zero>]"
      then have 0: "val x \<ge> \<alpha>"
        using assms c_ballE[of x \<alpha> \<zero>]
        by (smt Qp.minus_closed Qp.r_right_minus_eq Qp_diff_diff)
      have 1: "to_Zp x \<in> carrier Z\<^sub>p"
        using A 0 assms c_ballE(1) to_Zp_closed by blast
      have 2: "x \<in> \<O>\<^sub>p"
        using 0 A val_ringI c_ballE
        by (smt Q\<^sub>p_def Zp_def \<iota>_def eint_ord_simps(1) of_nat_0 of_nat_le_0_iff val_ring_ord_criterion padic_fields_axioms val_ord' zero_in_val_ring)
      then have "val_Zp (to_Zp  x) \<ge> \<alpha>"
        using 0 1 A assms c_ballE[of x \<alpha> \<zero>] to_Zp_val by presburger
      then have "to_Zp x \<alpha> = 0"
        using 1 zero_below_val_Zp by blast
      then show " x \<in> Qp_cong_set \<alpha> a"
        unfolding Qp_cong_set_def using assms(2) 2
        by (metis (mono_tags, lifting) mem_Collect_eq)
    qed
  qed
qed

lemma Qp_cong_set_as_ball':
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "val_Zp a < eint (int \<alpha>)"
  shows "Qp_cong_set \<alpha> a = B\<^bsub>\<alpha>\<^esub>[(\<iota> a)]"
proof
  show "Qp_cong_set \<alpha> a \<subseteq> B\<^bsub>\<alpha>\<^esub>[\<iota> a]"
  proof fix x
    assume A:  "x \<in> Qp_cong_set \<alpha> a"
    then have 0: "to_Zp x \<alpha> = a \<alpha>"
      unfolding Qp_cong_set_def  by blast
    have 1:  "x \<in> \<O>\<^sub>p"
      using A unfolding Qp_cong_set_def by blast
    have 2: "to_Zp x \<in> carrier Z\<^sub>p"
      using 1 val_ring_memE to_Zp_closed by blast
    have 3: "val_Zp (to_Zp x \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) \<ge> \<alpha>"
      using 0 assms 2 val_Zp_dist_def val_Zp_dist_res_eq2 by presburger
    have 4: "val_Zp (to_Zp x \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) > val_Zp a"
      using 3 assms(2) less_le_trans[of "val_Zp a" "eint (int \<alpha>)" "val_Zp (to_Zp x \<ominus>\<^bsub>Z\<^sub>p\<^esub> a)" ]
      by blast
    then have 5: "val_Zp (to_Zp x) = val_Zp a"
      using assms 2 equal_val_Zp by blast
    have 7: "val (x \<ominus> (\<iota> a)) \<ge> \<alpha>"
      using 3 5 1 by (metis "2" Zp.minus_closed assms(1) inc_of_diff to_Zp_inc val_of_inc)
    then show "x \<in> B\<^bsub>int \<alpha>\<^esub>[\<iota> a]"
      using c_ballI[of x \<alpha> "\<iota> a"]  1 assms val_ring_memE by blast
  qed
  show "B\<^bsub>int \<alpha>\<^esub>[\<iota> a] \<subseteq> Qp_cong_set \<alpha> a"
  proof fix x
    assume A: "x \<in> B\<^bsub>int \<alpha>\<^esub>[\<iota> a]"
    then have 0: "val (x \<ominus> \<iota> a) \<ge> \<alpha>"
      using c_ballE by blast
    have 1: "val (\<iota> a) = val_Zp a"
      using assms  Zp_def \<iota>_def padic_fields.val_of_inc padic_fields_axioms
      by metis
    then have 2: "val (x \<ominus> \<iota> a) > val (\<iota> a)"
      using 0 assms less_le_trans[of "val (\<iota> a)" "eint (int \<alpha>)" "val (x \<ominus> \<iota> a)"]
      by metis
    have "\<iota> a \<in> carrier Q\<^sub>p"
      using assms(1) inc_closed by blast
    then have B: "val x = val (\<iota> a)"
      using 2  A assms c_ballE(1)[of x \<alpha> "\<iota> a"]
      by (metis ultrametric_equal_eq)
    have 3: "val_Zp (to_Zp x) = val_Zp a"
      by (metis "1" A \<open>val x = val (\<iota> a)\<close> assms(1) c_ballE(1) to_Zp_val val_pos val_ringI)
    have 4: "val_Zp (to_Zp x \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) \<ge> \<alpha>"
      using 0 A 3
      by (metis B Zp.minus_closed assms(1) c_ballE(1) inc_of_diff to_Zp_closed to_Zp_inc val_of_inc val_pos val_ring_val_criterion)
    then have 5: "to_Zp x \<alpha> = a \<alpha>"
      by (meson A Zp.minus_closed assms(1) c_ballE(1) res_diff_zero_fact(1) to_Zp_closed zero_below_val_Zp)
    have 6: "x \<in> \<O>\<^sub>p"
    proof-
      have "val x \<ge> 0"
        using B assms 1 val_pos by presburger
      then show ?thesis
        using A c_ballE(1) val_ringI by blast
    qed
    then show "x \<in> Qp_cong_set \<alpha> a" unfolding Qp_cong_set_def
      using "5" by blast
  qed
qed

lemma Qp_cong_set_is_univ_semialgebraic:
  assumes "a \<in> carrier Z\<^sub>p"
  shows "is_univ_semialgebraic (Qp_cong_set \<alpha> a)"
proof(cases "a \<alpha> = 0")
  case True
  then show ?thesis
    using ball_is_univ_semialgebraic[of \<zero> \<alpha>] Qp.zero_closed  Qp_cong_set_as_ball assms
    by metis
next
  case False
  then have "\<alpha> \<noteq> 0"
    using assms residues_closed[of a 0]
    by (meson p_res_ring_0')
  then obtain n where n_def: "Suc n = \<alpha>"
    by (metis lessI less_Suc_eq_0_disj)
  then have "val_Zp a < eint (int \<alpha>)"
    using below_val_Zp_zero[of a n]
    by (smt False assms eint_ile eint_ord_simps(1) eint_ord_simps(2) zero_below_val_Zp)
  then show ?thesis
    using ball_is_univ_semialgebraic[of "\<iota> a" \<alpha>] Qp.zero_closed  Qp_cong_set_as_ball'[of a \<alpha>] assms
         inc_closed by presburger
qed

lemma constant_res_set_semialg:
  assumes "l \<in> carrier (Zp_res_ring n)"
  shows "is_univ_semialgebraic {x \<in> \<O>\<^sub>p. Qp_res x n = l}"
proof-
  have 0: "{x \<in> \<O>\<^sub>p. Qp_res x n = l} = Qp_cong_set n ([l]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    apply(rule equalityI')
    unfolding mem_Collect_eq Qp_cong_set_def Qp_res_def
    apply (metis val_ring_memE Zp_int_inc_rep nat_le_linear p_residue_padic_int to_Zp_closed)
    using assms
    by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
  show ?thesis unfolding 0
    apply(rule Qp_cong_set_is_univ_semialgebraic)
    by(rule Zp.int_inc_closed)
qed

end

end
